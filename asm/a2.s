 # A-2: parse the state string into p, o, c0, c1
.data
weight:  .half 720, 120, 24, 6, 2, 1, 1   # 每個位置的權重
digits:  .zero 14                          # 轉換後的 14 個數字
input:   .string "25314672313211"          # 15 bytes（含結尾的 0）
         .byte 0                           # 補成 16 bytes，保持偶數

.text
main:
    # ---- 1. digits[i] = input[i] - '1' ----
    la   s0, input
    la   s1, digits
    li   t0, 0                    # i = 0
    li   t1, 14
parse_loop:
    add  t2, s0, t0
    lbu  t3, 0(t2)                # 讀第 i 個字元
    addi t3, t3, -49              # 減掉 '1'（ASCII 49）
    add  t2, s1, t0
    sb   t3, 0(t2)                # 存到 digits[i]
    addi t0, t0, 1
    blt  t0, t1, parse_loop

    # ---- 2. p = sum of smaller[i] * weight[i] ----
    li   s2, 0                    # p = 0
    li   t0, 0                    # i = 0
lehmer_i:
    add  t2, s1, t0
    lbu  t3, 0(t2)                # v = digits[i]
    li   t4, 0                    # smaller = 0
    addi t5, t0, 1                # j = i + 1
lehmer_j:
    li   t6, 7
    bge  t5, t6, lehmer_add       # j 到 7 就停
    add  t2, s1, t5
    lbu  a0, 0(t2)                # digits[j]
    bge  a0, t3, lehmer_skip      # digits[j] >= v 就不算
    addi t4, t4, 1                # smaller++
lehmer_skip:
    addi t5, t5, 1
    j    lehmer_j
lehmer_add:
    la   t2, weight
    slli a0, t0, 1                # i × 2（每格 2 bytes）
    add  t2, t2, a0
    lhu  a1, 0(t2)                # weight[i]
mul_loop:                         # p += smaller * weight[i]，用重複加法
    beqz t4, mul_done
    add  s2, s2, a1
    addi t4, t4, -1
    j    mul_loop
mul_done:
    addi t0, t0, 1
    li   t6, 7
    blt  t0, t6, lehmer_i

    # ---- 3. o = first six twists in base 3 ----
    li   s3, 0                    # o = 0
    li   t0, 7                    # 方向從 digits[7] 開始
orient_loop:
    add  t2, s1, t0
    lbu  t3, 0(t2)
    slli t4, s3, 1                # t4 = o × 2
    add  s3, s3, t4               # o = o × 3
    add  s3, s3, t3               # + 這一位的方向
    addi t0, t0, 1
    li   t6, 13                   # 只算前 6 個（digits[7]～[12]）
    blt  t0, t6, orient_loop

    # ---- 4. c0, c1 = position * 4 + twist ----
    li   a2, 0
    jal  ra, find_cubie           # 找角 0
    mv   s4, a0
    li   a2, 1
    jal  ra, find_cubie           # 找角 1
    mv   s5, a0

    # ---- print p o c0 c1 ----
    mv   a0, s2
    jal  ra, print_int_space
    mv   a0, s3
    jal  ra, print_int_space
    mv   a0, s4
    jal  ra, print_int_space
    mv   a0, s5
    jal  ra, print_int_space
    li   a7, 10
    ecall

# 輸入 a2 = 要找的角，回傳 a0 = 位置 * 4 + 方向
find_cubie:
    li   t0, 0                    # 位置 = 0
find_loop:
    add  t2, s1, t0
    lbu  t3, 0(t2)
    beq  t3, a2, find_done        # 找到了
    addi t0, t0, 1
    j    find_loop
find_done:
    lbu  t3, 7(t2)                # 這個位置的方向在 digits[位置 + 7]
    slli a0, t0, 2                # 位置 × 4
    add  a0, a0, t3
    ret

print_int_space:
    li   a7, 1
    ecall
    li   a0, 32                   # 空白
    li   a7, 11
    ecall
    ret