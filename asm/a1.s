# A-1: read three table entries and print them
.text
main:
    # cubie_move[0][4]: expect 1
    la   t0, cubie_move          # t0 = 表的起點位址
    lbu  a0, 4(t0)               # 讀 1 byte
    li   a7, 1
    ecall                        # 印整數
    li   a0, 10
    li   a7, 11
    ecall                        # 印換行

    # permutation[0][0]: expect 1104
    la   t0, permutation
    lhu  a0, 0(t0)               # 讀 2 bytes
    li   a7, 1
    ecall
    li   a0, 10
    li   a7, 11
    ecall

    # permutation[1][0]: expect 9
    la   t0, permutation
    li   t1, 10080               # 第 5040 格 = 起點 + 5040 × 2 bytes
    add  t0, t0, t1
    lhu  a0, 0(t0)
    li   a7, 1
    ecall
    li   a0, 10
    li   a7, 11
    ecall

    li   a7, 10
    ecall                        # 結束