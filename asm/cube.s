# minirubik solver in RV32I
.data
rows:    .zero 36                          # 9 row addresses: perm[3], orient[3], cubie[3]
#@RENDER_BEGIN
# ---- LED data (removed in the CLI build) ----
cubie_col: .word 0xFFFFFF, 0x00C000, 0xFF0000, 0xFFFF00, 0xFF0000, 0x00C000, 0xFFFF00, 0x00C000, 0xFF8000, 0xFFFFFF, 0xFF0000, 0x0000FF
           .word 0xFFFF00, 0x0000FF, 0xFF0000, 0xFFFF00, 0xFF8000, 0x0000FF, 0xFFFFFF, 0x0000FF, 0xFF8000, 0xFFFFFF, 0xFF8000, 0x00C000
fl_off:    .half 752, 1312, 1332, 2292, 1752, 1732, 2276, 1716, 1696, 332, 1348, 1368
           .half 2712, 1788, 1768, 2696, 1680, 1804, 316, 1384, 1260, 736, 1276, 1296
cube_p:    .byte 0, 1, 2, 3, 4, 5, 6, 7    # which cubie sits at each corner
cube_o:    .byte 0, 0, 0, 0, 0, 0, 0, 0    # its twist (0..2)
tmp_p:     .zero 8                         # scratch for quarter_turn
tmp_o:     .zero 8
src_tab:   .byte 1, 4, 2, 0, 3, 5, 6, 7    # R
           .byte 0, 1, 2, 4, 5, 6, 3, 7    # B
           .byte 0, 2, 5, 3, 1, 4, 6, 7    # D
tw_tab:    .byte 1, 2, 0, 2, 1, 0, 0, 0    # R
           .byte 0, 0, 0, 1, 2, 1, 2, 0    # B
           .byte 0, 0, 0, 0, 0, 0, 0, 0    # D
#@RENDER_END
weight:  .half 720, 120, 24, 6, 2, 1, 1
levels:  .zero 84                          # sp[12] so[12] (half), s0[12] s1[12] path[12] (byte)
digits:  .zero 14
input:   .string "21345671111111"
         .byte 0
face_ch: .byte 82, 66, 68, 0               # 'R' 'B' 'D'
turn_ch: .byte 0, 50, 39, 0                # none, '2', '\''

.text
main:
    # ---- 1. digits[i] = input[i] - '1' ----
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

    # ---- 2. p = sum of smaller[i] * weight[i] ----
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

    # ---- 3. o = first six twists in base 3 ----
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

    # ---- 4. c0, c1 = position * 4 + twist ----
    li   a2, 0
    jal  ra, find_cubie
    mv   s4, a0
    li   a2, 1
    jal  ra, find_cubie
    mv   s5, a0

    # ---- save start state into level 0 ----
    la   t0, levels
    sh   s2, 0(t0)
    sh   s3, 24(t0)
    sb   s4, 48(t0)
    sb   s5, 60(t0)

    # ---- row addresses ----
    la   s7, rows
    la   t0, permutation
    li   t1, 10080
    sw   t0, 0(s7)
    add  t0, t0, t1
    sw   t0, 4(s7)
    add  t0, t0, t1
    sw   t0, 8(s7)
    la   t0, orientation
    li   t1, 1458
    sw   t0, 12(s7)
    add  t0, t0, t1
    sw   t0, 16(s7)
    add  t0, t0, t1
    sw   t0, 20(s7)
    la   t0, cubie_move
    sw   t0, 24(s7)
    addi t0, t0, 28
    sw   t0, 28(s7)
    addi t0, t0, 28
    sw   t0, 32(s7)

    # ---- IDA*: bound = 0, 1, 2, ... ----
    la   s1, levels
    la   s5, pattern_dist
    la   s6, orient_dist
    li   s4, 0
    li   s3, 0
ida_loop:
    jal  ra, search
    bnez a0, print_path
    addi s3, s3, 1
    j    ida_loop

    # ---- print the moves in path[0..bound-1] ----
print_path:
    la   s8, face_ch
    la   s9, turn_ch
    li   s10, 0
print_loop:
    beq  s10, s3, print_end
    beqz s10, no_space
    li   a0, 32
    li   a7, 11
    ecall
no_space:
    add  t0, s1, s10
    lbu  t1, 72(t0)
    srli t2, t1, 2
    add  t2, s8, t2
    lbu  a0, 0(t2)
    li   a7, 11
    ecall
    andi t2, t1, 3
    add  t2, s9, t2
    lbu  a0, 0(t2)
    beqz a0, no_suffix
    li   a7, 11
    ecall
no_suffix:
    addi s10, s10, 1
    j    print_loop
print_end:
    li   a0, 10
    li   a7, 11
    ecall

#@RENDER_BEGIN
    # ==== LED: draw the start, then redraw after every move ====
    la   t0, digits
    la   t1, cube_p
    li   t2, 0
init_loop:
    lbu  t3, 0(t0)
    sb   t3, 0(t1)
    lbu  t3, 7(t0)
    sb   t3, 8(t1)
    addi t0, t0, 1
    addi t1, t1, 1
    addi t2, t2, 1
    li   t4, 7
    blt  t2, t4, init_loop
    jal  ra, draw
    li   s10, 0                  # s10 = move index
anim_loop:
    beq  s10, s3, anim_done
    add  t0, s1, s10
    lbu  t1, 72(t0)              # move code = face*4 + turn
    srli s11, t1, 2              # face
    andi s8, t1, 3
    addi s8, s8, 1               # quarter turns: 1, 2 or 3
anim_turn:
    mv   a0, s11
    jal  ra, quarter_turn
    addi s8, s8, -1
    bnez s8, anim_turn
    jal  ra, draw
    addi s10, s10, 1
    j    anim_loop
anim_done:
#@RENDER_END

    # ==== T5: replay path from the start, check it reaches solved ====
    lhu  t3, 0(s1)
    lhu  t4, 24(s1)
    li   s10, 0
check_loop:
    beq  s10, s3, check_end
    add  t0, s1, s10
    lbu  t1, 72(t0)
    srli t2, t1, 2
    slli t2, t2, 2
    add  t2, s7, t2
    lw   a3, 0(t2)
    lw   a4, 12(t2)
    andi t5, t1, 3
    addi t5, t5, 1
turn_loop:
    slli a6, t3, 1
    add  a6, a3, a6
    lhu  t3, 0(a6)
    slli a6, t4, 1
    add  a6, a4, a6
    lhu  t4, 0(a6)
    addi t5, t5, -1
    bnez t5, turn_loop
    addi s10, s10, 1
    j    check_loop
check_end:
    or   a0, t3, t4
    snez a0, a0
    li   a7, 93
    ecall

# ---- search(bound = s3): a0 = 1 if solved within bound ----
search:
    li   s2, 0
enter:
    addi s4, s4, 1
    slli t0, s2, 1
    add  t0, s1, t0
    add  t1, s1, s2
    lbu  a0, 48(t1)
    andi a0, a0, 3
    lbu  a1, 60(t1)
    andi a1, a1, 3
    lhu  a2, 0(t0)
    slli a3, a2, 3
    add  a3, a3, a2
    slli a4, a0, 1
    add  a4, a4, a0
    add  a3, a3, a4
    add  a3, a3, a1
    add  a3, s5, a3
    lbu  a5, 0(a3)
    lhu  a2, 24(t0)
    add  a2, s6, a2
    lbu  a2, 0(a2)
    bge  a5, a2, h_ok
    mv   a5, a2
h_ok:
    add  a2, s2, a5
    bgt  a2, s3, back
    beqz a5, found
    li   a2, -1
    sb   a2, 72(t1)
next:
    add  t1, s1, s2
    lb   a0, 72(t1)
    addi a0, a0, 1
    andi a1, a0, 3
    li   a2, 3
    bne  a1, a2, no_gap
    addi a0, a0, 1
no_gap:
    li   a2, 12
    beq  a0, a2, back
    srli a1, a0, 2
    beqz s2, no_prev
    lbu  a2, 71(t1)
    srli a2, a2, 2
    bne  a1, a2, no_prev
    slli a2, a1, 2
    addi a2, a2, 2
    sb   a2, 72(t1)
    j    next
no_prev:
    slli t0, s2, 1
    add  t0, s1, t0
    andi a2, a0, 3
    bnez a2, no_copy
    lhu  a3, 0(t0)
    sh   a3, 2(t0)
    lhu  a3, 24(t0)
    sh   a3, 26(t0)
    lbu  a3, 48(t1)
    sb   a3, 49(t1)
    lbu  a3, 60(t1)
    sb   a3, 61(t1)
no_copy:
    slli a2, a1, 2
    add  a2, s7, a2
    lw   a3, 0(a2)
    lw   a4, 12(a2)
    lw   a5, 24(a2)
    lhu  a6, 2(t0)
    slli a6, a6, 1
    add  a6, a3, a6
    lhu  a6, 0(a6)
    sh   a6, 2(t0)
    lhu  a6, 26(t0)
    slli a6, a6, 1
    add  a6, a4, a6
    lhu  a6, 0(a6)
    sh   a6, 26(t0)
    lbu  a6, 49(t1)
    add  a6, a5, a6
    lbu  a6, 0(a6)
    sb   a6, 49(t1)
    lbu  a6, 61(t1)
    add  a6, a5, a6
    lbu  a6, 0(a6)
    sb   a6, 61(t1)
    sb   a0, 72(t1)
    addi s2, s2, 1
    j    enter
back:
    beqz s2, fail
    addi s2, s2, -1
    j    next
found:
    li   a0, 1
    ret
fail:
    li   a0, 0
    ret

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

#@RENDER_BEGIN
# ---- quarter_turn: a0 = face (0=R, 1=B, 2=D), one clockwise quarter turn on cube_p/cube_o ----
quarter_turn:
    slli t1, a0, 3               # face * 8 = row offset in src_tab / tw_tab
    la   t2, tw_tab
    add  t2, t2, t1
    la   t0, src_tab
    add  t1, t0, t1
    la   t0, cube_p
    li   t3, 0
qt_loop:
    add  t4, t1, t3
    lbu  t4, 0(t4)
    add  t4, t0, t4
    lbu  a0, 0(t4)
    lbu  a1, 8(t4)
    add  t5, t2, t3
    lbu  t5, 0(t5)
    add  a1, a1, t5
    li   t6, 3
    blt  a1, t6, qt_ok
    addi a1, a1, -3
qt_ok:
    add  t5, t0, t3
    sb   a0, 16(t5)              # tmp_p[i]
    sb   a1, 24(t5)              # tmp_o[i]
    addi t3, t3, 1
    li   t6, 8
    blt  t3, t6, qt_loop
    li   t3, 0
qt_copy:                         # copy tmp back to cube
    add  t5, t0, t3
    lbu  a0, 16(t5)
    sb   a0, 0(t5)
    lbu  a0, 24(t5)
    sb   a0, 8(t5)
    addi t3, t3, 1
    li   t6, 8
    blt  t3, t6, qt_copy
    ret

# ---- draw: paint all 24 facelets from cube_p/cube_o (no s registers: s1 and s3 are still live) ----
draw:
    la   t2, fl_off
    la   t3, cube_p
    la   t6, cubie_col
    li   t5, LED_MATRIX_0_BASE
    li   t4, 8
pos_loop:
    lbu  a4, 0(t3)
    slli a5, a4, 1
    add  a5, a5, a4
    slli a5, a5, 2
    add  a5, a5, t6
    lbu  a7, 8(t3)
    li   a6, 0
slot_loop:
    sub  a2, a6, a7
    bgez a2, slot_ok
    addi a2, a2, 3
slot_ok:
    slli a2, a2, 2
    add  a2, a2, a5
    lw   a1, 0(a2)
    lhu  a0, 0(t2)
    add  a0, a0, t5
    sw   a1, 0(a0)               # 4x3 block, unrolled
    sw   a1, 4(a0)
    sw   a1, 8(a0)
    sw   a1, 12(a0)
    sw   a1, 140(a0)
    sw   a1, 144(a0)
    sw   a1, 148(a0)
    sw   a1, 152(a0)
    sw   a1, 280(a0)
    sw   a1, 284(a0)
    sw   a1, 288(a0)
    sw   a1, 292(a0)
    addi t2, t2, 2
    addi a6, a6, 1
    li   a3, 3
    blt  a6, a3, slot_loop
    addi t3, t3, 1
    addi t4, t4, -1
    bnez t4, pos_loop
    ret
#@RENDER_END
