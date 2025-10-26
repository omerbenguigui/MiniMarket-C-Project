#define _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <ctype.h>
#include <math.h>

/* ---------- Constants / Macros ---------- */
#define MAX_PRODUCTS 128
#define NAME_LEN     64
#define LOG_PATH     "sim_all.csv"
#define STATE_PATH   "sim_state.bin"  

#define PERISHABLE  (0x01)
#define ON_SALE     (0x02)
#define TAX_EXEMPT  (0x04)

#define MIN(a,b) ((a)<(b)?(a):(b))
#define MAX(a,b) ((a)>(b)?(a):(b))

/* ---------- Types ---------- */
typedef struct {
    int    id;
    char   name[NAME_LEN];
    double baseCost;
    double price;
    int    stock;
    unsigned int flags;

    long long requested, served, stockouts, wasteUnits;
    double revenue, cogs, ordersCost;
} Product;

typedef struct {
    int daysDefault;
    int reorder_point;      // s
    int order_quantity;     // Q
    int leadMin, leadMax;   // inclusive
    double orderCostFixed;  // per PO
    double taxRate;
} Config;

typedef struct PO {
    int poId;
    int productIndex;
    int qty;
    int dueDay;
    int leadTime;
    struct PO* next;
} PO;

typedef struct {
    double revenue, cogs, ordersCost, profit;
    long long requested, served, stockouts;
} DayTotals;

typedef struct { int index; double profit; } ProfitRow;

/* ---------- Globals ---------- */
static Config  G_cfg;
static Product G_products[MAX_PRODUCTS];
static int     G_n = 0;
static PO* G_openPOs = NULL;
static int     G_day = 0;
static int     G_nextPO = 1;

static FILE* G_fAll = NULL;

/* ---------- Prototypes ---------- */
static void clear_line(void);
static int  rand_int(int a, int b);
static int  sample_poisson(double lambda);

static PO* po_create(int productIndex, int qty, int dueDay, int lead);
static void po_push_sorted(PO** head, PO* node);
static PO* po_pop_due_today(PO** head, int today);
static void po_free_list(PO* head);
static int  po_on_order_qty(PO* head, int productIndex);

static void load_defaults(void);
static void load_config_txt(const char* path);
static void demo_inventory(void);
static void load_inventory_csv(const char* path);

static void open_single_log_append(void);
static void reset_single_log_and_state(void);
static void close_single_log(void);

static double demand_lambda_for(const Product* p);
static int    waste_units_for_day(const Product* p);
static void   log_sale_row(int day, const Product* p, int req, int srv, int shortage, int waste);
static void   log_order_row(int dayPlaced, int poId, const Product* p, int qty, int dueDay, int leadTime, double orderCost);
static void   log_daily(int day, const DayTotals* D);

static void simulate_day(void);
static int  cmp_profit_desc(const void* a, const void* b);
static void report_top_products_by_profit(void);
static void report_service_and_stockouts(void);
static void report_summary_cumulative(void);
static void show_open_pos(void);
static void print_menu(void);

/* Welcome screen */
static void clear_screen(void);
static void wait_enter(void);
static void show_welcome(void);

/* NEW: persistence */
static int  save_state(const char* path);
static int  load_state(const char* path);

/* ---------- Utils ---------- */
static void clear_line(void) { int c; while ((c = getchar()) != '\n' && c != EOF) {} }
static int rand_int(int a, int b) { if (b < a) { int t = a; a = b; b = t; } return a + (rand() % (b - a + 1)); }
static int sample_poisson(double lambda) {
    if (lambda <= 0.0) return 0;
    double L = exp(-lambda), p = 1.0; int k = 0;
    do { k++; p *= ((double)rand() / RAND_MAX); } while (p > L);
    return k - 1;
}

/* ---------- Linked list (POs) ---------- */
static PO* po_create(int productIndex, int qty, int dueDay, int lead) {
    PO* n = (PO*)malloc(sizeof(PO)); if (!n) return NULL;
    n->poId = G_nextPO++; n->productIndex = productIndex; n->qty = qty; n->dueDay = dueDay; n->leadTime = lead; n->next = NULL;
    return n;
}
static void po_push_sorted(PO** head, PO* node) {
    if (!node) return;
    if (!*head || node->dueDay < (*head)->dueDay) { node->next = *head; *head = node; return; }
    PO* cur = *head; while (cur->next && cur->next->dueDay <= node->dueDay) cur = cur->next;
    node->next = cur->next; cur->next = node;
}
static PO* po_pop_due_today(PO** head, int today) {
    PO* outHead = NULL, * outTail = NULL;
    while (*head && (*head)->dueDay == today) {
        PO* n = *head; *head = (*head)->next; n->next = NULL;
        if (!outHead) outHead = outTail = n; else { outTail->next = n; outTail = n; }
    }
    return outHead;
}
static void po_free_list(PO* head) { while (head) { PO* n = head->next; free(head); head = n; } }
static int  po_on_order_qty(PO* head, int productIndex) { int s = 0; for (PO* n = head; n; n = n->next) if (n->productIndex == productIndex) s += n->qty; return s; }

/* ---------- Loading ---------- */
static void load_defaults(void) {
    G_cfg.daysDefault = 30; G_cfg.reorder_point = 15; G_cfg.order_quantity = 40;
    G_cfg.leadMin = 2; G_cfg.leadMax = 4; G_cfg.orderCostFixed = 15.0; G_cfg.taxRate = 0.17;
}
static void load_config_txt(const char* path) {
    FILE* f = NULL; if (fopen_s(&f, path, "r") != 0 || !f) { return; } /* silent if not found */
    char line[512], key[64], val[256];
    while (fgets(line, sizeof(line), f)) {
        if (line[0] == '#' || (line[0] == '/' && line[1] == '/')) continue;
        if (sscanf_s(line, " %63[^=]=%255[^\n]", key, (unsigned)sizeof(key), val, (unsigned)sizeof(val)) == 2) {
            for (int i = (int)strlen(key) - 1; i >= 0 && isspace((unsigned char)key[i]); --i) key[i] = '\0';
            for (int i = 0; val[i]; ++i) if (val[i] == '\r' || val[i] == '\n') val[i] = '\0';
            for (int i = 0; key[i]; ++i) key[i] = (char)tolower((unsigned char)key[i]);
            if (!strcmp(key, "days"))               G_cfg.daysDefault = atoi(val);
            else if (!strcmp(key, "s") || !strcmp(key, "reorder_point")) G_cfg.reorder_point = atoi(val);
            else if (!strcmp(key, "q") || !strcmp(key, "order_quantity")) G_cfg.order_quantity = atoi(val);
            else if (!strcmp(key, "leadtimemin"))   G_cfg.leadMin = atoi(val);
            else if (!strcmp(key, "leadtimemax"))   G_cfg.leadMax = atoi(val);
            else if (!strcmp(key, "ordercostfixed")) G_cfg.orderCostFixed = atof(val);
            else if (!strcmp(key, "taxrate"))        G_cfg.taxRate = atof(val);
        }
    }
    fclose(f);
}
static void demo_inventory(void) {
    G_n = 0; Product p;
    p.id = 101; strcpy_s(p.name, sizeof(p.name), "Milk 1L");      p.baseCost = 6.0;  p.price = 8.0;  p.stock = 50; p.flags = PERISHABLE;
    p.requested = p.served = p.stockouts = p.wasteUnits = 0; p.revenue = p.cogs = p.ordersCost = 0; G_products[G_n++] = p;
    p.id = 102; strcpy_s(p.name, sizeof(p.name), "Bread");        p.baseCost = 5.0;  p.price = 7.5;  p.stock = 40; p.flags = 0;
    p.requested = p.served = p.stockouts = p.wasteUnits = 0; p.revenue = p.cogs = p.ordersCost = 0; G_products[G_n++] = p;
    p.id = 204; strcpy_s(p.name, sizeof(p.name), "Strawberries"); p.baseCost = 20.0; p.price = 28.0; p.stock = 20; p.flags = PERISHABLE;
    p.requested = p.served = p.stockouts = p.wasteUnits = 0; p.revenue = p.cogs = p.ordersCost = 0; G_products[G_n++] = p;
    p.id = 305; strcpy_s(p.name, sizeof(p.name), "Olive Oil");    p.baseCost = 23.0; p.price = 35.0; p.stock = 15; p.flags = 0;
    p.requested = p.served = p.stockouts = p.wasteUnits = 0; p.revenue = p.cogs = p.ordersCost = 0; G_products[G_n++] = p;
}
static unsigned int parse_flags_token(const char* tok) {
    char buf[128]; strncpy_s(buf, sizeof(buf), tok, _TRUNCATE);
    for (int i = 0; buf[i]; ++i) if (buf[i] == ' ' || buf[i] == '\t' || buf[i] == '\r' || buf[i] == '\n') buf[i] = '\0';
    char* end = NULL; long v = strtol(buf, &end, 10); if (end && *end == '\0' && buf[0]) return (unsigned)v;
    unsigned int flags = 0; const char* p = buf;
    while (*p) {
        char t[64] = { 0 }; int ti = 0; while (*p && *p != '|' && ti < 63) { t[ti++] = *p++; } if (*p == '|') p++;
        for (int i = 0; t[i]; ++i) t[i] = (char)toupper((unsigned char)t[i]);
        if (!strcmp(t, "PERISHABLE")) flags |= PERISHABLE; else if (!strcmp(t, "ON_SALE")) flags |= ON_SALE; else if (!strcmp(t, "TAX_EXEMPT")) flags |= TAX_EXEMPT;
    }
    return flags;
}
static void load_inventory_csv(const char* path) {
    FILE* f = NULL; if (fopen_s(&f, path, "r") != 0 || !f) { demo_inventory(); return; } /* silent fallback */
    char line[1024]; if (!fgets(line, sizeof(line), f)) { fclose(f); demo_inventory(); return; }
    G_n = 0;
    while (fgets(line, sizeof(line), f)) {
        if (G_n >= MAX_PRODUCTS) break;
        char name[NAME_LEN]; int id, stock; double bc, pr; char flagsTok[128] = "0";
        int n = sscanf_s(line, " %d , %63[^,] , %lf , %lf , %d , %127[^\n]",
            &id, name, (unsigned)sizeof(name), &bc, &pr, &stock, flagsTok, (unsigned)sizeof(flagsTok));
        if (n >= 5) {
            Product p; memset(&p, 0, sizeof(p));
            p.id = id; strncpy_s(p.name, sizeof(p.name), name, _TRUNCATE);
            p.baseCost = bc; p.price = pr; p.stock = stock;
            p.flags = (n == 6 ? parse_flags_token(flagsTok) : 0);
            G_products[G_n++] = p;
        }
    }
    fclose(f);
}

/* ---------- Single CSV log (append / reset) ---------- */
static void open_single_log_append(void) {
    if (G_fAll) return;
    fopen_s(&G_fAll, LOG_PATH, "a+");
    if (!G_fAll) { fprintf(stderr, "ERR: cannot open %s\n", LOG_PATH); return; }
    fseek(G_fAll, 0, SEEK_END); long sz = ftell(G_fAll);
    if (sz <= 0) {
        fprintf(G_fAll,
            "type,day,poId,dayPlaced,productId,productName,orderQty,dueDay,leadTime,orderCost,"
            "requested,served,unitPrice,revenue,shortage,waste,"
            "revenue_d,cogs_d,orders_d,profit_d,fill_rate,stockouts\n");
        fflush(G_fAll);
    }
}
static void reset_single_log_and_state(void) {
    if (G_fAll) { fclose(G_fAll); G_fAll = NULL; }
    fopen_s(&G_fAll, LOG_PATH, "w");
    if (G_fAll) {
        fprintf(G_fAll,
            "type,day,poId,dayPlaced,productId,productName,orderQty,dueDay,leadTime,orderCost,"
            "requested,served,unitPrice,revenue,shortage,waste,"
            "revenue_d,cogs_d,orders_d,profit_d,fill_rate,stockouts\n");
        fflush(G_fAll);
    }
    po_free_list(G_openPOs); G_openPOs = NULL;
    for (int i = 0; i < G_n; i++) {
        G_products[i].requested = G_products[i].served = G_products[i].stockouts = G_products[i].wasteUnits = 0;
        G_products[i].revenue = G_products[i].cogs = G_products[i].ordersCost = 0.0;
    }
    G_day = 0; G_nextPO = 1;

    /* NEW: also clear saved state so next run starts fresh */
    remove(STATE_PATH);
}
static void close_single_log(void) { if (G_fAll) { fclose(G_fAll); G_fAll = NULL; } }

/* ---------- Demand / Waste ---------- */
static double demand_lambda_for(const Product* p) {
    double base = (p->flags & PERISHABLE) ? 6.0 : 3.5;
    double priceFactor = (p->price > 0 ? (12.0 / (p->price + 4.0)) : 2.0);
    double promo = (p->flags & ON_SALE) ? 1.25 : 1.0;
    double lam = base * priceFactor * promo; if (lam < 0.2) lam = 0.2; if (lam > 18.0) lam = 18.0; return lam;
}
static int waste_units_for_day(const Product* p) {
    if (!(p->flags & PERISHABLE)) return 0; int s = p->stock; if (s <= 0) return 0;
    double rate = (rand_int(1, 3)) / 100.0; int w = (int)floor(rate * s + 0.5); return (w > 0 ? w : 0);
}

/* ---------- Log writers ---------- */
static void log_sale_row(int day, const Product* p, int req, int srv, int shortage, int waste) {
    if (!G_fAll) return; double rev = srv * p->price;
    fprintf(G_fAll, "sale,%d,,,,%d,%s,,,,%d,%d,%.2f,%.2f,%d,%d,,,,,,\n",
        day, p->id, p->name, req, srv, p->price, rev, shortage, waste);
    fflush(G_fAll);
}
static void log_order_row(int dayPlaced, int poId, const Product* p, int qty, int dueDay, int leadTime, double orderCost) {
    if (!G_fAll) return;
    fprintf(G_fAll, "order,,%d,%d,%d,%s,%d,%d,%d,%.2f,,,,,,,,,,,\n",
        poId, dayPlaced, p->id, p->name, qty, dueDay, leadTime, orderCost);
    fflush(G_fAll);
}
static void log_daily(int day, const DayTotals* D) {
    if (!G_fAll) return; double fill = (D->requested > 0 ? ((double)D->served / (double)D->requested) : 1.0);
    fprintf(G_fAll, "daily,%d,,,,,,,,,,,,,,,%.2f,%.2f,%.2f,%.2f,%.4f,%lld\n",
        day, D->revenue, D->cogs, D->ordersCost, D->profit, fill, D->stockouts);
    fflush(G_fAll);
}

/* ---------- PERSISTENCE (save/load state) ---------- */
typedef struct { int poId, productIndex, qty, dueDay, leadTime; } SavePO;

static int save_state(const char* path) {
    FILE* f = NULL; if (fopen_s(&f, path, "wb") != 0 || !f) return 0;
    unsigned int magic = 0x53494D31; /* 'SIM1' */
    fwrite(&magic, sizeof(magic), 1, f);

    fwrite(&G_cfg, sizeof(G_cfg), 1, f);
    fwrite(&G_day, sizeof(G_day), 1, f);
    fwrite(&G_nextPO, sizeof(G_nextPO), 1, f);
    fwrite(&G_n, sizeof(G_n), 1, f);

    if (G_n > 0) fwrite(G_products, sizeof(Product), G_n, f);

    int count = 0; for (PO* n = G_openPOs; n; n = n->next) count++;
    fwrite(&count, sizeof(count), 1, f);
    for (PO* n = G_openPOs; n; n = n->next) {
        SavePO s = { n->poId, n->productIndex, n->qty, n->dueDay, n->leadTime };
        fwrite(&s, sizeof(s), 1, f);
    }
    fclose(f);
    return 1;
}

static int load_state(const char* path) {
    FILE* f = NULL; if (fopen_s(&f, path, "rb") != 0 || !f) return 0;
    unsigned int magic = 0; if (fread(&magic, sizeof(magic), 1, f) != 1 || magic != 0x53494D31) { fclose(f); return 0; }

    if (fread(&G_cfg, sizeof(G_cfg), 1, f) != 1) { fclose(f); return 0; }
    if (fread(&G_day, sizeof(G_day), 1, f) != 1) { fclose(f); return 0; }
    if (fread(&G_nextPO, sizeof(G_nextPO), 1, f) != 1) { fclose(f); return 0; }
    if (fread(&G_n, sizeof(G_n), 1, f) != 1) { fclose(f); return 0; }
    if (G_n<0 || G_n>MAX_PRODUCTS) { fclose(f); return 0; }

    if (G_n > 0 && fread(G_products, sizeof(Product), G_n, f) != (size_t)G_n) { fclose(f); return 0; }

    po_free_list(G_openPOs); G_openPOs = NULL;
    int count = 0; if (fread(&count, sizeof(count), 1, f) != 1) { fclose(f); return 0; }
    for (int i = 0; i < count; i++) {
        SavePO s; if (fread(&s, sizeof(s), 1, f) != 1) { fclose(f); return 0; }
        PO* node = po_create(s.productIndex, s.qty, s.dueDay, s.leadTime);
        if (node) { node->poId = s.poId; po_push_sorted(&G_openPOs, node); }
        if (G_nextPO <= s.poId) G_nextPO = s.poId + 1;
    }
    fclose(f);
    return 1;
}

/* ---------- One day ---------- */
static void simulate_day(void) {
    G_day += 1;
    DayTotals D; memset(&D, 0, sizeof(D));

    /* Arrivals */
    PO* arrivals = po_pop_due_today(&G_openPOs, G_day);
    if (arrivals) {
        printf("Arrivals: "); int first = 1;
        for (PO* n = arrivals; n; n = n->next) {
            Product* p = &G_products[n->productIndex]; p->stock += n->qty;
            if (!first) printf(", "); printf("%s +%d (PO#%d)", p->name, n->qty, n->poId); first = 0;
        }
        puts(""); po_free_list(arrivals);
    }

    /* Demand & sales */
    int* reqArr = (int*)calloc(G_n, sizeof(int)), * srvArr = (int*)calloc(G_n, sizeof(int));
    int* shortArr = (int*)calloc(G_n, sizeof(int)), * wstArr = (int*)calloc(G_n, sizeof(int));
    if (!reqArr || !srvArr || !shortArr || !wstArr) { puts("OOM"); free(reqArr); free(srvArr); free(shortArr); free(wstArr); return; }

    printf("Demand: ");
    for (int i = 0; i < G_n; i++) {
        Product* p = &G_products[i];
        int req = sample_poisson(demand_lambda_for(p));
        int srv = MIN(req, p->stock);
        int shortage = req - srv;
        p->stock -= srv;

        reqArr[i] = req; srvArr[i] = srv; shortArr[i] = shortage;

        p->requested += req; p->served += srv; p->stockouts += (shortage > 0 ? shortage : 0);
        D.requested += req; D.served += srv; D.stockouts += (shortage > 0 ? shortage : 0);
        double rev = srv * p->price, cg = srv * p->baseCost;
        p->revenue += rev; p->cogs += cg; D.revenue += rev; D.cogs += cg;

        if (i) printf(", "); printf("%s=%d", p->name, req);
    }
    puts("");

    printf("Sales:  ");
    for (int i = 0; i < G_n && i < 4; i++) { if (i) printf(", "); printf("%s=%d", G_products[i].name, srvArr[i]); }
    if (G_n > 4) printf(", ..."); printf(" (0 backorders)\n");

    /* Waste + log per product */
    int anyWaste = 0, anySto = 0;
    for (int i = 0; i < G_n; i++) {
        Product* p = &G_products[i];
        int waste = waste_units_for_day(p); if (waste > p->stock) waste = p->stock;
        if (waste > 0) { p->stock -= waste; p->wasteUnits += waste; anyWaste = 1; }
        wstArr[i] = waste; if (shortArr[i] > 0) anySto = 1;
        log_sale_row(G_day, p, reqArr[i], srvArr[i], shortArr[i], wstArr[i]);
    }

    if (anySto) {
        printf("Stockout Alerts: "); int first = 1;
        for (int i = 0; i < G_n; i++) if (shortArr[i] > 0) { if (!first) printf(", "); printf("%s short by %d units", G_products[i].name, shortArr[i]); first = 0; }
        puts("");
    }
    else puts("Stockout Alerts: none");

    if (anyWaste) {
        printf("Waste (Perishables): "); int first = 1;
        for (int i = 0; i < G_n; i++) if (wstArr[i] > 0) { if (!first) printf(", "); printf("%s -%d units", G_products[i].name, wstArr[i]); first = 0; }
        puts("");
    }

    /* Reorders (s,Q) */
    typedef struct { int idx, qty, due; } NewPO; NewPO* today = (NewPO*)malloc(sizeof(NewPO) * G_n); int nToday = 0;
    for (int i = 0; i < G_n; i++) {
        Product* p = &G_products[i];
        int invPos = p->stock + po_on_order_qty(G_openPOs, i);
        if (invPos <= G_cfg.reorder_point) {
            int lt = rand_int(G_cfg.leadMin, G_cfg.leadMax), due = G_day + lt;
            PO* node = po_create(i, G_cfg.order_quantity, due, lt);
            if (node) {
                po_push_sorted(&G_openPOs, node);
                p->ordersCost += G_cfg.orderCostFixed; D.ordersCost += G_cfg.orderCostFixed;
                log_order_row(G_day, node->poId, p, node->qty, node->dueDay, node->leadTime, G_cfg.orderCostFixed);
                today[nToday].idx = i; today[nToday].qty = node->qty; today[nToday].due = due; nToday++;
            }
        }
    }
    if (nToday > 0) {
        printf("Reorders: ");
        for (int k = 0; k < nToday; k++) { if (k) printf(", "); printf("%s - Order quantity: %d, ETA: Day %d", G_products[today[k].idx].name, today[k].qty, today[k].due); }
        puts("");
    }
    else puts("Reorders: none");
    free(today);

    D.profit = D.revenue - D.cogs - D.ordersCost;
    printf("KPI: Revenue=%.0f ILS | COGS=%.0f ILS | Orders=%.0f ILS | Profit=%.0f ILS\n", D.revenue, D.cogs, D.ordersCost, D.profit);
    log_daily(G_day, &D);

    /* NEW: auto-save state at end of day */
    save_state(STATE_PATH);

    free(reqArr); free(srvArr); free(shortArr); free(wstArr);
}

/* ---------- Reports ---------- */
static int cmp_profit_desc(const void* a, const void* b) {
    const ProfitRow* x = (const ProfitRow*)a, * y = (const ProfitRow*)b;
    if (y->profit > x->profit) return 1; if (y->profit < x->profit) return -1; return 0;
}
static void report_top_products_by_profit(void) {
    int K = 5; printf("How many products to show (Top-K)? [default 5]: ");
    int tmp; if (scanf_s("%d", &tmp) == 1 && tmp > 0) K = tmp;
    ProfitRow* rows = (ProfitRow*)malloc(sizeof(ProfitRow) * G_n); if (!rows) { puts("OOM"); return; }
    for (int i = 0; i < G_n; i++) { rows[i].index = i; rows[i].profit = G_products[i].revenue - G_products[i].cogs - G_products[i].ordersCost; }
    qsort(rows, G_n, sizeof(ProfitRow), cmp_profit_desc); if (K > G_n) K = G_n;
    puts("\n=== Top products by profit ===");
    printf("%-3s %-6s %-18s %-6s %-8s %-8s %-8s %-8s\n", "#", "ID", "Name", "Sold", "Revenue", "COGS", "Orders", "Profit");
    for (int j = 0; j < K; j++) {
        int i = rows[j].index; double pr = rows[j].profit; long long sold = G_products[i].served;
        printf("%-3d %-6d %-18s %-6lld %-8.0f %-8.0f %-8.0f %-8.0f\n", j + 1, G_products[i].id, G_products[i].name, sold,
            G_products[i].revenue, G_products[i].cogs, G_products[i].ordersCost, pr);
    }
    free(rows);
}
static void report_service_and_stockouts(void) {
    long long req = 0, srv = 0, sto = 0; for (int i = 0; i < G_n; i++) { req += G_products[i].requested; srv += G_products[i].served; sto += G_products[i].stockouts; }
    double fill = (req > 0 ? ((double)srv / (double)req) : 1.0) * 100.0;
    int topIdx[3] = { -1,-1,-1 }; long long topVals[3] = { 0,0,0 };
    for (int i = 0; i < G_n; i++) {
        long long v = G_products[i].stockouts;
        for (int k = 0; k < 3; k++) { if (v > topVals[k]) { for (int m = 2; m > k; m--) { topVals[m] = topVals[m - 1]; topIdx[m] = topIdx[m - 1]; } topVals[k] = v; topIdx[k] = i; break; } }
    }
    puts("\n=== Service level & stockouts ===");
    printf("Fill rate: %.2f%%\n", fill); printf("Stockouts (units): %lld\n", sto); printf("Top stockout products: ");
    int printed = 0; for (int k = 0; k < 3; k++) { if (topIdx[k] >= 0 && topVals[k] > 0) { if (printed) printf(", "); printf("%s %lld", G_products[topIdx[k]].name, topVals[k]); printed = 1; } }
    if (!printed) printf("none"); puts("");
}
static void report_summary_cumulative(void) {
    double revenue = 0, cogs = 0, orders = 0; long long req = 0, srv = 0, sto = 0;
    for (int i = 0; i < G_n; i++) { revenue += G_products[i].revenue; cogs += G_products[i].cogs; orders += G_products[i].ordersCost; req += G_products[i].requested; srv += G_products[i].served; sto += G_products[i].stockouts; }
    double profit = revenue - cogs - orders; double fill = (req > 0 ? ((double)srv / (double)req) : 1.0) * 100.0;
    printf("\n=== Summary (cumulative) - Days 1..%d ===\n", G_day);
    printf("Revenue: %.0f ILS\nCOGS:    %.0f ILS\nOrders:  %.0f ILS\nPROFIT:  %.0f ILS\n\n", revenue, cogs, orders, profit);
    printf("Fill rate: %.2f%%\nStockouts (units): %lld\n", fill, sto);
    int topIdx[3] = { -1,-1,-1 }; long long topVals[3] = { 0,0,0 };
    for (int i = 0; i < G_n; i++) {
        long long v = G_products[i].stockouts;
        for (int k = 0; k < 3; k++) { if (v > topVals[k]) { for (int m = 2; m > k; m--) { topVals[m] = topVals[m - 1]; topIdx[m] = topIdx[m - 1]; } topVals[k] = v; topIdx[k] = i; break; } }
    }
    printf("Top stockout products: "); int printed = 0;
    for (int k = 0; k < 3; k++) { if (topIdx[k] >= 0 && topVals[k] > 0) { if (printed) printf(", "); printf("%s %lld", G_products[topIdx[k]].name, topVals[k]); printed = 1; } }
    if (!printed) printf("none"); puts("");
    printf("\nSaved to: %s\n", LOG_PATH);
}
static void show_open_pos(void) {
    puts("\nOpen Purchase Orders (ETAs)\n---------------------------");
    if (!G_openPOs) { puts("(none)"); return; }
    for (PO* n = G_openPOs; n; n = n->next) {
        Product* p = &G_products[n->productIndex]; int daysLeft = n->dueDay - G_day; if (daysLeft < 0) daysLeft = 0;
        printf("PO#%d | %-16s | Order quantity: %d | ETA: Day %d | Days left: %d\n",
            n->poId, p->name, n->qty, n->dueDay, daysLeft);
    }
}

/* ---------- Welcome screen ---------- */
static void clear_screen(void) {
#ifdef _WIN32
    system("cls");
#else
    system("clear");
#endif
}
static void wait_enter(void) {
    puts("\nPress ENTER to continue...");
    int c;
    while ((c = getchar()) != '\n' && c != EOF) {}
}
static void show_welcome(void) {
    clear_screen();
    puts("+----------------------------------------------------+");
    puts("|                                                    |");
    puts("|           W E L C O M E   T O   T H E              |");
    puts("|                                                    |");
    puts("|                M I N I M A R K E T                 |"); /* NOTE: regular ASCII only */
    puts("|                                                    |");
    puts("+----------------------------------------------------+");
    wait_enter();
    clear_screen();
}

/* ---------- Menu ---------- */
static void print_menu(void) {
    puts("\n================= INVENTORY SIM ((s,Q)) =================");
    printf("Day: %d\n", G_day);
    puts("---------------------------------------------------------");
    puts("1) Run multiple days (you'll enter how many)");
    puts("2) Step 1 day");
    puts("3) Reports");
    puts("   3.1) Top products by profit (choose how many)");
    puts("   3.2) Service level & stockouts");
    puts("   3.3) Summary (cumulative totals)");
    puts("4) Show open purchase orders (ETAs)");
    puts("5) rest");
    puts("6) Exit");
    puts("---------------------------------------------------------");
    printf("Select: ");
}

/* ---------- Main ---------- */
int main(void) {
    srand((unsigned)time(NULL));

    /* Show welcome first */
    show_welcome();

    /* Auto-load on start: config/inventory, open single log in append mode */
    load_defaults();
    load_config_txt("config.txt");       /* if missing -> keep defaults */
    load_inventory_csv("inventory.csv"); /* if missing -> demo inventory */
    open_single_log_append();

    /* NEW: try to resume from saved state */
    if (load_state(STATE_PATH)) {
        printf("Loaded saved state from %s. Continuing at Day %d.\n", STATE_PATH, G_day);
    }
    else {
        printf("Starting new simulation. Day=%d.\n", G_day);
    }

    int running = 1;
    while (running) {
        print_menu();
        int choice = -1; if (scanf_s("%d", &choice) != 1) { clear_line(); continue; }

        if (choice == 1) {
            int N = 0; printf("How many days to run? ");
            if (scanf_s("%d", &N) != 1 || N <= 0) { puts("Invalid days."); clear_line(); continue; }
            for (int i = 0; i < N; i++) { printf("\nDay %d\n------\n", G_day + 1); simulate_day(); }
        }
        else if (choice == 2) {
            printf("\nDay %d\n------\n", G_day + 1); simulate_day();
        }
        else if (choice == 3) {
            printf("\nReports: choose 1/2/3: "); int r = 0;
            if (scanf_s("%d", &r) != 1) { clear_line(); continue; }
            if (r == 1) report_top_products_by_profit();
            else if (r == 2) report_service_and_stockouts();
            else if (r == 3) report_summary_cumulative();
            else puts("Unknown report.");
        }
        else if (choice == 4) {
            show_open_pos();
        }
        else if (choice == 5) {
            puts("\nAre you sure? This will CLEAR sim_all.csv and reset the simulation. (y/n)");
            char ch = 0; scanf_s(" %c", &ch, 1);
            if (ch == 'y' || ch == 'Y') { reset_single_log_and_state(); puts("Reset complete. Day=0."); }
            else puts("Reset cancelled.");
        }
        else if (choice == 6) {
            /* NEW: save state on exit */
            save_state(STATE_PATH);
            running = 0;
        }
        else {
            puts("Unknown option.");
        }
    }
    close_single_log(); po_free_list(G_openPOs);
    return 0;
}
