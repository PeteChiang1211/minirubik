#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
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

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}
static uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];

static void build_transitions(void)
{
    state_t state;
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
}
static uint8_t perm_dist[PERMUTATIONS];

static void build_perm_dist(void)
{
    uint16_t queue[PERMUTATIONS];
    uint16_t head = 0, tail = 1;

    memset(perm_dist, UINT8_MAX, PERMUTATIONS);   // 全部標成「還沒算過」
    queue[0] = 0;                              // 從已解好開始
    perm_dist[0] = 0 ;                          // 已解好是幾步？

    while (head < tail) {
        uint16_t here = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = permutation[face][next];   // 再轉 90 度
                if (perm_dist[next] == UINT8_MAX) {
                    perm_dist[next] =perm_dist[here] + 1;       // 新狀態是幾步？
                    queue[tail++] = next;
                }
            }
        }
    }
}

static uint8_t orient_dist[ORIENTATIONS];

static void build_orient_dist(void)
{
    uint16_t queue[ORIENTATIONS];
    uint16_t head = 0, tail = 1;

    memset(orient_dist, UINT8_MAX, ORIENTATIONS);   // 全部標成「還沒算過」
    queue[0] = 0;                              // 從已解好開始
    orient_dist[0] = 0 ;                          // 已解好是幾步？

    while (head < tail) {
        uint16_t here = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = orientation[face][next];   // 再轉 90 度
                if (orient_dist[next] == UINT8_MAX) {
                    orient_dist[next] =orient_dist[here] + 1;       // 新狀態是幾步？
                    queue[tail++] = next;
                }
            }
        }
    }
}

static uint8_t cubie_move[3][28];   // 跟著一個角：轉一下之後，新的編號
static uint8_t pattern_dist[PERMUTATIONS * 9];   // 新小抄：位置 + 角 0、角 1 的方向

static void build_cubie_move(void)
{
    for (int face = 0; face < 3; face++)
        for (int pos = 0; pos < CUBIES; pos++)
            for (int ori = 0; ori < 3; ori++) {
                int to = 0;
                while (source[face][to] != pos)
                    to++;
                int nori = (ori + twist[face][to]) % 3;
                cubie_move[face][pos * 4 + ori] = (uint8_t) (to * 4 + nori);
            }
}

/* 從一個完整的 state 找出某個角的編號（位置 × 3 + 方向） */
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

static int solve(uint32_t r)
{
    state_t s;
    unrank_state(r, &s);
    sp[0] = (uint16_t) (r / ORIENTATIONS);   /* 筆記本第 0 行：起點 */
    so[0] = (uint16_t) (r % ORIENTATIONS);
    s0[0] = cubie_coord(&s, 0);
    s1[0] = cubie_coord(&s, 1);
    int bound = 0;
    while (!search(bound))
        bound++;
    return bound;
}

static uint8_t *exact;   // 標準答案：每個狀態真正的最短步數

static void build_exact_dist(void)
{
    exact = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint32_t head = 0, tail = 1;

    memset(exact, UINT8_MAX, STATES);
    queue[0] = 0;
    exact[0] = 0;

    while (head < tail) {
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (int face = 0; face < 3; face++) {
            uint16_t np = p, no = o;
            for (int turn = 0; turn < 3; turn++) {
                np = permutation[face][np];
                no = orientation[face][no];
                uint32_t there = (uint32_t) np * ORIENTATIONS + no;
                if (exact[there] == UINT8_MAX) {
                    exact[there] = exact[here] + 1;
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
}

static void build_pattern_dist(void)
{
    memset(pattern_dist, UINT8_MAX, sizeof pattern_dist);   // 先全部填 255（還沒填）
    for (uint32_t r = 0; r < STATES; r++) {
        state_t s;
        unrank_state(r, &s);                        // 把編號 r 變回完整的方塊
        uint16_t p = (uint16_t) (r / ORIENTATIONS);
        int ori0 = cubie_coord(&s, 0) & 3;        // 角 0 的方向
        int ori1 = cubie_coord(&s, 1) & 3;         // 角 1 的方向
        uint32_t cell = p * 9 + ori0 * 3 + ori1;    // 這個狀態屬於哪一格
        if (exact[r] < pattern_dist[cell])
            pattern_dist[cell] = exact[r];
    }
}

/* 在電腦上準備所有表 */
static void prepare(void)
{
    build_transitions();
    build_perm_dist();
    build_orient_dist();
    build_cubie_move();
    build_exact_dist();
    build_pattern_dist();
}

static int verify(void)
{
    uint32_t h1_bad = 0, h3_bad = 0;

    for (uint32_t r = 0; r < STATES; r++) {
        if (r % 500000 == 0)
            fprintf(stderr, "checked %u states...\n", r);

        state_t s;
        unrank_state(r, &s);
        uint16_t p = (uint16_t) (r / ORIENTATIONS);
        uint16_t o = (uint16_t) (r % ORIENTATIONS);
        uint8_t c0 = cubie_coord(&s, 0);
        uint8_t c1 = cubie_coord(&s, 1);

        /* H1：新的指南針不能估太多 */
        int h = pattern_dist[p * 9 + (c0 & 3) * 3 + (c1 & 3)];
        if (orient_dist[o] > h)
            h = orient_dist[o];
        if (h > exact[r])
            h1_bad++;

        /* H3：用 IDA* 解，再照著 path 走一遍 */
        int len = solve(r);
        uint16_t cp = p, co = o;
        for (int i = 0; i < len; i++) {
            int face = path[i] >> 2;
            int turns = (path[i] & 3) + 1;
            for (int t = 0; t < turns; t++) {
                cp = permutation[face][cp];
                co = orientation[face][co];
            }
        }
        if (len != exact[r] || cp != 0 || co != 0)
            h3_bad++;
    }

    printf("H1 violations: %u\n", h1_bad);
    printf("H3 failures:   %u\n", h3_bad);
    return h1_bad || h3_bad;
}

static void measure(void)
{
    uint32_t count = 0, worst = 0, worst_r = 0, over = 0;
    uint64_t total = 0;

    for (uint32_t r = 0; r < STATES; r++) {
        if (exact[r] != 11)
            continue;
        nodes = 0;
        solve(r);
        count++;
        total += nodes;
        if (nodes > worst) {
            worst = nodes;
            worst_r = r;
        }
        if (nodes > 250000)
            over++;
    }

    printf("distance-11 states: %u\n", count);
    printf("average nodes:      %llu\n", (unsigned long long) (total / count));
    printf("worst nodes:        %u (rank %u)\n", worst, worst_r);
    printf("over 250,000:       %u\n", over);
}

static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
    uint32_t head = 0, tail = 1, level_end = 1;
    state_t state;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    uint8_t move = (uint8_t) (face * 3U + turn);
                    toward_solved[there] = inverse_move[move];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

/* 把一張表寫成組語的 .half 或 .byte，每行 16 個數字 */
static void emit(FILE *f, const char *label, const char *directive,
                 const void *data, int count, int size)
{
    fprintf(f, "%s:\n", label);
    for (int i = 0; i < count; i++) {
        unsigned v = size == 2 ? ((const uint16_t *) data)[i]
                               : ((const uint8_t *) data)[i];
        if (i % 16 == 0)
            fprintf(f, "    %s ", directive);
        fprintf(f, "%u%s", v, (i % 16 == 15 || i == count - 1) ? "\n" : ", ");
    }
}

/* 把 Ripes 要用的 5 張表輸出成 tables.s */
static int export_tables(const char *name)
{
    FILE *f = fopen(name, "w");
    if (!f)
        return 1;
    fprintf(f, "# Generated by ./ida --export. Do not edit.\n");
    fprintf(f, ".data\n");
    emit(f, "permutation", ".half", permutation, 3 * PERMUTATIONS, 2);
    emit(f, "orientation", ".half", orientation, 3 * ORIENTATIONS, 2);
    emit(f, "pattern_dist", ".byte", pattern_dist, PERMUTATIONS * 9, 1);
    emit(f, "orient_dist", ".byte", orient_dist, ORIENTATIONS, 1);
    emit(f, "cubie_move", ".byte", cubie_move, 3 * 28, 1);
    return fclose(f) != 0;
}

int main(int argc, char **argv)
{
    state_t state;
    if (argc == 2 && strcmp(argv[1], "--export") == 0) {
    prepare();
    return export_tables("tables.s");
    }
    if (argc == 2 && strcmp(argv[1], "--verify") == 0) {
        prepare();
        return verify();
    }
    if (argc == 2 && strcmp(argv[1], "--dist") == 0) {
        prepare();
        /* exact[] is the full BFS distance table; 255 would mean unreached */
        uint32_t count[256] = {0}, total = 0;
        for (uint32_t r = 0; r < STATES; r++)
            count[exact[r]]++;
        for (int d = 0; d < 256; d++) {
            if (count[d] == 0)
                continue;
            total += count[d];
            printf("%3d %9u\n", d, count[d]);
        }
        printf("total %u of %u\n", total, (uint32_t) STATES);
        return 0;
    }
    if (argc == 2 && strcmp(argv[1], "--nodes") == 0) {
        prepare();
        measure();
        return 0;
    }
    if (argc != 2 || !parse_state(argv[1], &state)) {
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO | --verify | --nodes\n", argv[0]);
        return 2;
    }

    prepare();
    nodes = 0;
    int len = solve(rank_state(&state));
    for (int i = 0; i < len; i++)
    printf("%s%s", i ? " " : "", move_names[(path[i] >> 2) * 3 + (path[i] & 3)]);
    printf("\n");
    fprintf(stderr, "nodes: %u\n", nodes);
    return 0;
}

