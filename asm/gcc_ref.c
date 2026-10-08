/* gcc reference build of the final C search, for comparison with asm/cube.s.
 * search(), rank_state() and cubie_coord() are copied unchanged from ida.c;
 * only the Ripes entry point, parsing without validation, and ecall output
 * are new. Tables come from tables.s (appended at assembly time). */
#include <stdint.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

extern const uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
extern const uint8_t orient_dist[ORIENTATIONS];
extern const uint8_t cubie_move[3][28];
extern const uint8_t pattern_dist[PERMUTATIONS * 9];

static const char input[] = "21345671111111";

static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

static uint8_t cubie_coord(const state_t *s, int cubie)
{
    int pos = 0;
    while (s->p[pos] != cubie)
        pos++;
    return (uint8_t) (pos * 4 + s->o[pos]);
}

static int8_t path[12];      // 記錄目前走了哪些轉法
static uint32_t nodes;        // 記錄總共檢查了幾個節點

/* IDA* 搜尋（不用遞迴，自己用筆記本記每一層）
 * bound: 這一輪的步數上限
 * 回傳 1 代表找到解（路線在 path），0 代表這一輪找不到 */
static uint16_t sp[12], so[12];   // 筆記本：每一層的位置、方向
static uint8_t s0[12], s1[12];    // 筆記本：每一層的角 0、角 1

static const uint16_t *const perm_row[3] = {permutation[0], permutation[1], permutation[2]};
static const uint16_t *const orient_row[3] = {orientation[0], orientation[1], orientation[2]};
static const uint8_t *const cubie_row[3] = {cubie_move[0], cubie_move[1], cubie_move[2]};

static int search(int bound)
{
    int g = 0, h, m, face, ori0, ori1;
    const uint16_t *pr, *orr;
    const uint8_t *cr;

enter:                                  /* 走進第 g 層的房間 */
    nodes++;
    ori0 = s0[g] & 3;                   /* ① 角 0 的方向 */
    ori1 = s1[g] & 3;                   /* ① 角 1 的方向 */
    h = pattern_dist[(sp[g] << 3) + sp[g] + (ori0 << 1) + ori0 + ori1];   /* ② */
    if (orient_dist[so[g]] > h)
        h = orient_dist[so[g]];
    if (g + h > bound)
        goto back;
    if (h == 0)
        return 1;
    path[g] = -1;

next:                                   /* 試第 g 層的下一扇門 */
    m = path[g] + 1;
    if ((m & 3) == 3)                /* 碰到空著的那一格 */
        m++;
    if (m == 12)                      /* 三個面都試完了 */
        goto back;
    face = m >> 2;                    /* 空格 3：算出是哪個面 */
    if (g > 0 && face == (path[g - 1] >> 2)) {
        path[g] = (int8_t) ((face << 2) + 2);   /* 同一面：跳到這面最後一扇門 */
        goto next;
    }
    if ((m & 3) == 0) {                 /* 這個面的第一扇門 */
        sp[g + 1] = sp[g];
        so[g + 1] = so[g];
        s0[g + 1] = s0[g];
        s1[g + 1] = s1[g];
    }
    pr = perm_row[face];                /* ④ 這個面的表起點 */
    orr = orient_row[face];
    cr = cubie_row[face];
    sp[g + 1] = pr[sp[g + 1]];
    so[g + 1] = orr[so[g + 1]];
    s0[g + 1] = cr[s0[g + 1]];
    s1[g + 1] = cr[s1[g + 1]];
    path[g] = (int8_t) m;
    g++;
    goto enter;

back:                                   /* 這間走不通，退回上一層 */
    if (g == 0)
        return 0;
    g--;
    goto next;
}

static void putc_ecall(int c)
{
    register int a0 asm("a0") = c;
    register int a7 asm("a7") = 11;
    asm volatile("ecall" : : "r"(a0), "r"(a7));
}

static void exit_ecall(int code)
{
    register int a0 asm("a0") = code;
    register int a7 asm("a7") = 93;
    asm volatile("ecall" : : "r"(a0), "r"(a7));
    for (;;)
        ;
}

void _start(void)
{
    static const char face_ch[3] = {'R', 'B', 'D'};
    static const char turn_ch[3] = {0, '2', '\''};
    state_t s;
    for (int i = 0; i < 14; ++i)
        (i < 7 ? s.p : s.o)[i % 7] = (uint8_t) (input[i] - '1');
    uint32_t r = rank_state(&s);
    sp[0] = (uint16_t) (r / ORIENTATIONS);
    so[0] = (uint16_t) (r % ORIENTATIONS);
    s0[0] = cubie_coord(&s, 0);
    s1[0] = cubie_coord(&s, 1);
    int bound = 0;
    while (!search(bound))
        bound++;
    for (int i = 0; i < bound; ++i) {
        if (i)
            putc_ecall(' ');
        putc_ecall(face_ch[path[i] >> 2]);
        if (turn_ch[path[i] & 3])
            putc_ecall(turn_ch[path[i] & 3]);
    }
    putc_ecall('\n');
    exit_ecall(0);
}
