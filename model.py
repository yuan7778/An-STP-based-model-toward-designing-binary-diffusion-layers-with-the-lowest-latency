import itertools

n = 8
xor = 16
bd = 5
depth = 3


def generate_hamming_weight_vectors(n, i):
    all_vectors = itertools.product('01', repeat=n)
    hamming_i_vectors = set()
    for vector in all_vectors:
        if vector.count('1') == i:
            hamming_i_vectors.add(''.join(vector))
    vectors = sorted(list(hamming_i_vectors))
    return vectors


def compute_hamming_weight(s):
    count = 0
    for char in s:
        if char == '1':
            count += 1
    return count


def write_input_vector(n):
    for i in range(n):
        file.write(f"x{i}")
        if i != n - 1:
            file.write(",")
        if i == n - 1:
            file.write(f":BITVECTOR({n});\n")

    vec_str = '0' * n
    vec_str = '1' + vec_str[1:]
    for i in range(n):
        file.write(f"ASSERT(x{i}=0bin{vec_str});\n")
        index = vec_str.find('1')
        if index != -1 and index < len(vec_str) - 1:
            vec_str = vec_str[:index] + '0' + '1' + vec_str[index + 2:]
    file.write("\n\n")


def write_all_depth(n, xor):
    for i in range(n + xor):
        file.write(f"depth{i}")
        if i != n + xor - 1:
            file.write(",")
        else:
            file.write(":BITVECTOR(4);\n\n")
    for i in range(n):
        file.write(f"ASSERT(depth{i}=0b0001);\n")


def write_each_xor(n, i):
    for j in range(n + i):
        file.write(f"a{i}_{j}")
        if j != n + i - 1:
            file.write(",")
        else:
            file.write(f",c{i}:BITVECTOR(1);\n")

    file.write(f"ASSERT(BVPLUS(9,")
    for j in range(n + i):
        file.write(f"0bin00000000@a{i}_{j}")
        if j != n + i - 1:
            file.write(",")
        else:
            file.write(f")=0bin000000010);\n")

    file.write(f"ASSERT(x{n + i}=")
    for j in range(n + i - 1):
        file.write(f"BVXOR(")
    for j in range(n + i):
        file.write(f"BVMULT({n},0bin{'0' * (n - 1)}@a{i}_{j},x{j})")
        if j == 0:
            file.write(f",")
        if j != 0 and j != n + i - 1:
            file.write(f"),")
        if j == n + i - 1:
            file.write(f"));\n\n")

    for j in range(n + i):
        count = 0
        file.write(f"ASSERT(")
        for k in range(n + i):
            if k != j:
                file.write(f"BVGE(BVMULT(4,0b000@a{i}_{j},depth{j}),BVMULT(4,0b000@a{i}_{k},depth{k}))")
                count += 1
                if count < n + i - 1:
                    file.write(f" AND ")
                else:
                    file.write(f" => depth{n + i}=BVPLUS(4,depth{j},0b0001));\n")
    file.write("\n")

    for j in range(n + i):
        file.write(f"ASSERT(IF a{i}_{j}=0bin1 THEN (BVGE(BVPLUS(5")
        for k in range(n):
            file.write(f",0bin0000@x{n + i}[{k}:{k}]")
        file.write(f"),BVPLUS(5")
        for k in range(n):
            file.write(f",0bin0000@x{j}[{k}:{k}]")
        file.write(f"))) ELSE c{i}=0b0 ENDIF);\n")
    file.write("\n")


def write_invertibility():
    valid_vectors = []
    all_vectors = itertools.product('01', repeat=n)
    for vector in all_vectors:
        weight = vector.count('1')
        if 2 <= weight <= n:
            valid_vectors.append(''.join(vector))

    vectors = sorted(list(valid_vectors))

    for j in range(n):
        file.write(f"ASSERT(x{n + xor - 1 - j}/=0b{'0' * n});\n")
    for i in range(len(vectors)):
        hm = compute_hamming_weight(vectors[i])
        midhm = hm
        file.write(f"ASSERT(")
        for e in range(hm - 1):
            file.write(f"BVXOR(")
        for k in range(n):
            if vectors[i][k] == '1':
                midhm -= 1
                file.write(f"x{n + xor - 1 - k}")
                if midhm == hm - 1:
                    file.write(f",")
                if midhm != 0 and midhm != hm - 1:
                    file.write(f"),")
                if midhm == 0:
                    file.write(f")/=0b{'0' * n});\n")


def write_branch_number():
    for i in range(bd - 1):
        hm = i + 1
        vectors = generate_hamming_weight_vectors(n, hm)
        for j in range(len(vectors)):
            midhm = compute_hamming_weight(vectors[j])
            file.write(f"ASSERT(BVGE(BVPLUS(6,")
            for k in range(n):
                file.write(f"0b00000@")
                weight = midhm
                for e in range(hm - 1):
                    file.write(f"BVXOR(")
                for g in range(n):
                    if vectors[j][g] == "1":
                        file.write(f"x{n + xor - 1 - k}[{g}:{g}]")
                        if hm == 1 and k != n - 1:
                            file.write(f",")
                        if hm == 1 and k == n - 1:
                            file.write(f"),")
                        if hm != 1 and k != n - 1 and weight == midhm:
                            file.write(f",")
                        if hm != 1 and k != n - 1 and weight != midhm:
                            file.write(f"),")
                        if hm != 1 and k == n - 1 and weight == midhm:
                            file.write(f",")
                        if hm != 1 and k == n - 1 and weight != midhm and weight != 1:
                            file.write(f"),")
                        if hm != 1 and k == n - 1 and weight == 1:
                            file.write(f")),")
                        weight -= 1
            file.write(f"0b{bin(bd - midhm)[2:].zfill(6)}));\n\n")

    for i in range(bd - 1):
        hm = i + 1
        vectors2 = generate_hamming_weight_vectors(n, hm)
        for j in range(len(vectors2)):
            midhm = compute_hamming_weight(vectors2[j])
            file.write(f"ASSERT(BVGE(BVPLUS(6,")
            for k in range(n):
                file.write(f"0b00000@")
                weight = midhm
                for e in range(hm - 1):
                    file.write(f"BVXOR(")
                for g in range(n):
                    if vectors2[j][g] == "1":
                        file.write(f"x{n + xor - 1 - g}[{k}:{k}]")
                        if hm == 1 and k != n - 1:
                            file.write(f",")
                        if hm == 1 and k == n - 1:
                            file.write(f"),")
                        if hm != 1 and k != n - 1 and weight == midhm:
                            file.write(f",")
                        if hm != 1 and k != n - 1 and weight != midhm:
                            file.write(f"),")
                        if hm != 1 and k == n - 1 and weight == midhm:
                            file.write(f",")
                        if hm != 1 and k == n - 1 and weight != 1 and weight != midhm:
                            file.write(f"),")
                        if hm != 1 and k == n - 1 and weight == 1:
                            file.write(f")),")
                        weight -= 1
            file.write(f"0b{bin(bd - midhm)[2:].zfill(6)}));\n\n")


with open('model_output.cvc', 'w') as file:
    write_input_vector(n)

    for i in range(xor):
        file.write(f"x{n + i}")
        if i != xor - 1:
            file.write(",")
        if i == xor - 1:
            file.write(f":BITVECTOR({n});\n")
    file.write("\n\n")

    write_all_depth(n, xor)

    for i in range(xor):
        write_each_xor(n, i)

    for i in range(xor):
        file.write(f"ASSERT(BVLE(depth{i + n},0bin{bin(depth)[2:].zfill(4)}));\n")

    for b in range(n):
        file.write(f"ASSERT(BVGE(BVPLUS(5")
        for k in range(n):
            file.write(f",0bin0000@x{n + xor - 1 - b}[{k}:{k}]")
        file.write(f"),0bin{bin(bd - 1)[2:].zfill(5)}));\n")

    for l in range(n):
        for o in range(xor + l + 1, n + xor):
            file.write(f"ASSERT(x{xor + l}/=x{o});\n")
    file.write("\n\n")

    for c in range(n):
        file.write(f"ASSERT(BVGE(BVPLUS(5")
        for b in range(n):
            file.write(f",0bin0000@x{n + xor - 1 - b}[{c}:{c}]")
        file.write(f"),0bin{bin(bd - 1)[2:].zfill(5)}));\n")
    file.write("\n\n")

    for l1 in range(n):
        for o1 in range(l1 + 1, n):
            file.write(f"ASSERT(")
            for z in range(n):
                if z != n - 1:
                    file.write(f"x{n + xor - 1 - z}[{l1}:{l1}]@")
                if z == n - 1:
                    file.write(f"x{n + xor - 1 - z}[{l1}:{l1}]/=")
            for z2 in range(n):
                if z2 != n - 1:
                    file.write(f"x{n + xor - 1 - z2}[{o1}:{o1}]@")
                if z2 == n - 1:
                    file.write(f"x{n + xor - 1 - z2}[{o1}:{o1}]);\n")

    file.write("\n\n")

    write_invertibility()
    write_branch_number()

    file.write("QUERY(FALSE);\nCOUNTEREXAMPLE;")
