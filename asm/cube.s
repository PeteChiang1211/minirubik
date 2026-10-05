# minirubik solver in RV32I
.data
rows:    .zero 36                          # 9 個表起點：perm[3]、orient[3]、cubie[3]（word，放最前面對齊）
weight:  .half 720, 120, 24, 6, 2, 1, 1
levels:  .zero 84                          # 筆記本：sp so（half）、s0 s1 path（byte）
digits:  .zero 14
input:   .string "21345671111111"
         .byte 0
face_ch: .byte 82, 66, 68, 0               # 'R' 'B' 'D'
turn_ch: .byte 0, 50, 39, 0                # 不印、'2'、'\''

.text
main:
    # ==== A-2：讀入字串，算出 p o c0 c1（跟 a2.s 一樣） ====
    la   s0, input
    la   s1, digits
    li   t0, 0
    li   t1, 14
parse_loop:
    add  t2, s0, t0
    lbu  t3, 0(t2)
    addi t3, t3, -49
    add  t2, s1, t0
    sb   t3, 0(t2)
    addi t0, t0, 1
    blt  t0, t1, parse_loop

    li   s2, 0
    li   t0, 0
lehmer_i:
    add  t2, s1, t0
    lbu  t3, 0(t2)
    li   t4, 0
    addi t5, t0, 1
lehmer_j:
    li   t6, 7
    bge  t5, t6, lehmer_add
    add  t2, s1, t5
    lbu  a0, 0(t2)
    bge  a0, t3, lehmer_skip
    addi t4, t4, 1
lehmer_skip:
    addi t5, t5, 1
    j    lehmer_j
lehmer_add:
    la   t2, weight
    slli a0, t0, 1
    add  t2, t2, a0
    lhu  a1, 0(t2)
mul_loop:
    beqz t4, mul_done
    add  s2, s2, a1
    addi t4, t4, -1
    j    mul_loop
mul_done:
    addi t0, t0, 1
    li   t6, 7
    blt  t0, t6, lehmer_i

    li   s3, 0
    li   t0, 7
orient_loop:
    add  t2, s1, t0
    lbu  t3, 0(t2)
    slli t4, s3, 1
    add  s3, s3, t4
    add  s3, s3, t3
    addi t0, t0, 1
    li   t6, 13
    blt  t0, t6, orient_loop

    li   a2, 0
    jal  ra, find_cubie
    mv   s4, a0
    li   a2, 1
    jal  ra, find_cubie
    mv   s5, a0

    # ==== 把起點寫進筆記本第 0 層 ====
    la   t0, levels
    sh   s2, 0(t0)                 # sp[0] = p
    sh   s3, 24(t0)                # so[0] = o
    sb   s4, 48(t0)                # s0[0] = c0
    sb   s5, 60(t0)                # s1[0] = c1

    # ==== 算好 9 個表起點（C 的 perm_row 等） ====
    la   s7, rows
    la   t0, permutation
    li   t1, 10080                 # 5040 × 2 bytes
    sw   t0, 0(s7)                 # R
    add  t0, t0, t1
    sw   t0, 4(s7)                 # B
    add  t0, t0, t1
    sw   t0, 8(s7)                 # D
    la   t0, orientation
    li   t1, 1458                  # 729 × 2 bytes
    sw   t0, 12(s7)
    add  t0, t0, t1
    sw   t0, 16(s7)
    add  t0, t0, t1
    sw   t0, 20(s7)
    la   t0, cubie_move
    sw   t0, 24(s7)
    addi t0, t0, 28                # 28 × 1 byte
    sw   t0, 28(s7)
    addi t0, t0, 28
    sw   t0, 32(s7)

    # ==== IDA*：bound = 0, 1, 2, ... ====
    la   s1, levels
    la   s5, pattern_dist
    la   s6, orient_dist
    li   s4, 0                     # nodes = 0
    li   s3, 0                     # bound = 0
ida_loop:
    jal  ra, search
    bnez a0, print_path            # 找到了
    addi s3, s3, 1                 # bound++
    j    ida_loop

    # ==== 印出 path[0]～path[bound-1] ====
print_path:
    la   s8, face_ch
    la   s9, turn_ch
    li   s10, 0                    # i = 0
print_loop:
    beq  s10, s3, print_end
    beqz s10, no_space             # 第一步前面不印空白
    li   a0, 32
    li   a7, 11
    ecall
no_space:
    add  t0, s1, s10
    lbu  t1, 72(t0)                # m = path[i]
    srli t2, t1, 2                 # 面
    add  t2, s8, t2
    lbu  a0, 0(t2)                 # 'R' / 'B' / 'D'
    li   a7, 11
    ecall
    andi t2, t1, 3                 # 轉
    add  t2, s9, t2
    lbu  a0, 0(t2)                 # 不印 / '2' / '\''
    beqz a0, no_suffix
    li   a7, 11
    ecall
no_suffix:
    addi s10, s10, 1
    j    print_loop
print_end:
    li   a0, 10                    # 換行
    li   a7, 11
    ecall
        # ==== T5：照著 path 從起點轉一遍，檢查有沒有回到已解好 ====
    lhu  t3, 0(s1)                 # p = sp[0]（起點的位置編號）
    lhu  t4, 24(s1)                # o = so[0]（起點的方向編號）
    li   s10, 0                    # i = 0
check_loop:
    beq  s10, s3, check_end        # 走完 bound 步就結束
    add  t0, s1, s10
    lbu  t1, 72(t0)                # m = path[i]
    srli t2, t1, 2                 # face
    slli t2, t2, 2
    add  t2, s7, t2                # &rows[face]
    lw   a3, 0(t2)                 # perm 這一面的起點
    lw   a4, 12(t2)                # orient 這一面的起點
    andi t5, t1, 3                 # turn
    addi t5, t5, 1                 # 轉 turn + 1 次 90 度
turn_loop:
    slli a6, t3, 1
    add  a6, a3, a6
    lhu  t3, 0(a6)                 # p 轉一下
    slli a6, t4, 1
    add  a6, a4, a6
    lhu  t4, 0(a6)                 # o 轉一下
    addi t5, t5, -1
    bnez t5, turn_loop
    addi s10, s10, 1
    j    check_loop
check_end:
    or   a0, t3, t4                # p 和 o 都是 0，結果才會是 0
    snez a0, a0                    # 不是 0 就變成 1
    li   a7, 93
    ecall                          # 用代碼 a0 結束

# ==== search：C 的 search(bound)，找到回傳 a0 = 1 ====
search:
    li   s2, 0                     # g = 0
enter:                             # ---- 走進第 g 層的房間 ----
    addi s4, s4, 1                 # nodes++
    slli t0, s2, 1
    add  t0, s1, t0                # t0 = 第 g 層（2 bytes 的陣列）
    add  t1, s1, s2                # t1 = 第 g 層（1 byte 的陣列）
    lbu  a0, 48(t1)
    andi a0, a0, 3                 # ori0 = s0[g] & 3
    lbu  a1, 60(t1)
    andi a1, a1, 3                 # ori1 = s1[g] & 3
    lhu  a2, 0(t0)                 # sp[g]
    slli a3, a2, 3
    add  a3, a3, a2                # sp × 9
    slli a4, a0, 1
    add  a4, a4, a0                # ori0 × 3
    add  a3, a3, a4
    add  a3, a3, a1                # cell
    add  a3, s5, a3
    lbu  a5, 0(a3)                 # h = pattern_dist[cell]
    lhu  a2, 24(t0)                # so[g]
    add  a2, s6, a2
    lbu  a2, 0(a2)                 # orient_dist[so[g]]
    bge  a5, a2, h_ok
    mv   a5, a2                    # h 取比較大的
h_ok:
    add  a2, s2, a5                # g + h
    bgt  a2, s3, back              # g + h > bound 就退回
    beqz a5, found                 # h == 0：解好了
    li   a2, -1
    sb   a2, 72(t1)                # path[g] = -1

next:                              # ---- 試第 g 層的下一扇門 ----
    add  t1, s1, s2
    lb   a0, 72(t1)                # m = path[g]（可能是 -1，所以用 lb）
    addi a0, a0, 1                 # m = path[g] + 1
    andi a1, a0, 3
    li   a2, 3
    bne  a1, a2, no_gap
    addi a0, a0, 1                 # 碰到空格就跳過
no_gap:
    li   a2, 12
    beq  a0, a2, back              # 三個面都試完了
    srli a1, a0, 2                 # face = m >> 2
    beqz s2, no_prev
    lbu  a2, 71(t1)                # path[g-1]
    srli a2, a2, 2
    bne  a1, a2, no_prev
    slli a2, a1, 2
    addi a2, a2, 2
    sb   a2, 72(t1)                # 同一面：跳到這面最後一扇門
    j    next
no_prev:
    slli t0, s2, 1
    add  t0, s1, t0
    andi a2, a0, 3
    bnez a2, no_copy               # 不是這面的第一扇門就不複製
    lhu  a3, 0(t0)
    sh   a3, 2(t0)                 # sp[g+1] = sp[g]
    lhu  a3, 24(t0)
    sh   a3, 26(t0)                # so[g+1] = so[g]
    lbu  a3, 48(t1)
    sb   a3, 49(t1)                # s0[g+1] = s0[g]
    lbu  a3, 60(t1)
    sb   a3, 61(t1)                # s1[g+1] = s1[g]
no_copy:
    slli a2, a1, 2
    add  a2, s7, a2                # &rows[face]
    lw   a3, 0(a2)                 # perm 這一面的起點
    lw   a4, 12(a2)                # orient 這一面的起點
    lw   a5, 24(a2)                # cubie 這一面的起點
    lhu  a6, 2(t0)
    slli a6, a6, 1
    add  a6, a3, a6
    lhu  a6, 0(a6)
    sh   a6, 2(t0)                 # sp[g+1] = 轉一下
    lhu  a6, 26(t0)
    slli a6, a6, 1
    add  a6, a4, a6
    lhu  a6, 0(a6)
    sh   a6, 26(t0)                # so[g+1] = 轉一下
    lbu  a6, 49(t1)
    add  a6, a5, a6
    lbu  a6, 0(a6)
    sb   a6, 49(t1)                # s0[g+1] = 轉一下
    lbu  a6, 61(t1)
    add  a6, a5, a6
    lbu  a6, 0(a6)
    sb   a6, 61(t1)                # s1[g+1] = 轉一下
    sb   a0, 72(t1)                # path[g] = m
    addi s2, s2, 1                 # g++
    j    enter

back:                              # ---- 退回上一層 ----
    beqz s2, fail                  # 第 0 層：這一輪失敗
    addi s2, s2, -1                # g--
    j    next
found:
    li   a0, 1
    ret
fail:
    li   a0, 0
    ret

# 輸入 a2 = 要找的角，回傳 a0 = 位置 * 4 + 方向
find_cubie:
    li   t0, 0
find_loop:
    add  t2, s1, t0
    lbu  t3, 0(t2)
    beq  t3, a2, find_done
    addi t0, t0, 1
    j    find_loop
find_done:
    lbu  t3, 7(t2)
    slli a0, t0, 2
    add  a0, a0, t3
    ret