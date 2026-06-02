import itertools
import sys
def ygen(n):
    for i in range(n):
        file.write(f"y{i}")
        if i!=n-1:
            file.write(",")
        else:
            file.write(f":BITVECTOR({n});\n")

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


def rowgt(n,t):
    file.write(f"ASSERT((BVPLUS(12,")
    for j in range(n):
        file.write(f"0b00000000000@y0[{j}:{j}]")
        if j != n - 1:
            file.write(",")
    file.write(f")=0b{bin(t)[2:].zfill(12)}));\n")


def write_invertibility(n,bd):  
    valid_vectors = []
    all_vectors = itertools.product('01', repeat=n)
    for vector in all_vectors:
        weight = vector.count('1')
        if 2 <= weight <= n:
            valid_vectors.append(''.join(vector))

    vectors = sorted(list(valid_vectors))

    for j in range(n):
        file.write(f"ASSERT(y{j}/=0b{'0' * n});\n")
    for i in range(len(vectors)):
        hm = compute_hamming_weight(vectors[i])
        midhm = hm
        file.write(f"ASSERT(")
        for e in range(hm - 1):
            file.write(f"BVXOR(")
        for k in range(n):
            if vectors[i][k] == '1':
                midhm -= 1
                file.write(f"y{n-1-k}")
                if midhm == hm - 1:
                    file.write(f",")
                if midhm != 0 and midhm != hm - 1:
                    file.write(f"),")
                if midhm == 0:
                    file.write(f")/=0b{'0' * n});\n")


def write_branch_number(n,bd):
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
                        file.write(f"y{n-1-k}[{g}:{g}]")
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
                        file.write(f"y{n-1-g}[{k}:{k}]")
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
nomorepara = int(sys.argv[1])
with open(f'12_{nomorepara}.cvc', 'w') as file:
    dimenson=12
    branch=8
    ygen(dimenson)
    rowgt(dimenson,nomorepara)
    write_invertibility(dimenson,branch)
    write_branch_number(dimenson,branch)
    file.write("QUERY(FALSE);\nCOUNTEREXAMPLE;")