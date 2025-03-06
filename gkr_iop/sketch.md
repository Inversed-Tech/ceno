

check_state_equiv(reprA, reprB) {
    checks that reprA and reprB refer to the same bitstring
}

input -> STATE = 25 x [2 x <32>]
witness -> STATE' = 25 x [8 x <8>]

check_state_equiv(STATE, STATE')

witness -> C = 5 x [8 x <8>]
witness -> C_aux = 5 x 5 [8 x <8>]

for i in 0..5:
    C_aux[i][0] == STATE'[i * 5]
    for j in 1..4:
        C_aux[i][j] == C_aux[i][j - 1] xor STATE'[i * 5 + j]
    C[i] == C_aux[i][4]

witness -> C_temp = 5 x [<1>, <31>, <32>]
check_state_equiv(C, C_temp)

witness -> C_rot_temp = 5 x [<31>, <32>, <1>]
for i in 0..5:
    C_rot_temp[i][0] == C_temp[i][1]
    C_rot_temp[i][1] == C_temp[i][2]
    C_rot_temp[i][2] == C_temp[i][0]

witness -> C_rot = 5 x [8 x <8>]
check_state_equiv(C_rot_temp, C_rot)

witness -> D = 5 x [8 x <8>]

for i in 0..5:
    D[i] == C[(i - 1) mod 5] xor C_rot[(i + 1) mod 5]

witness -> OUTPUT = 5 x 5 x [8 x <8>]

for i in 0..5:
    for j in 0..5:
        OUTPUT[i][j] == D[i] xor STATE'[i][j]
