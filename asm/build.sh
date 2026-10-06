#!/bin/sh
# Build both Ripes inputs from asm/cube.s and tables.s
#   asm/cube_full.s : LED rendering on
#   asm/cube_cli.s  : RENDER blocks removed, used for instruction counts
awk 1 asm/cube.s tables.s > asm/cube_full.s
sed '/#@RENDER_BEGIN/,/#@RENDER_END/d' asm/cube.s | awk 1 - tables.s > asm/cube_cli.s
