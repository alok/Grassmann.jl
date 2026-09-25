"""Reference re-implementation of Grassmann.jl parity.jl sign rules (bit-for-bit spec check).

Every function mirrors pseudocode in notes/grassmann-parity.md. Blades are UInt bitmasks,
bit k (0-based) <-> basis index k+1 (1-based, Julia convention).
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional

Coef = float


def popcount(x: int) -> int:
    return bin(x).count("1")


def indices(b: int) -> list[int]:
    """1-based positions of set bits, ascending (Leibniz.indices)."""
    out, k = [], 1
    while b:
        if b & 1:
            out.append(k)
        b >>= 1
        k += 1
    return out


def lowmask(n: int) -> int:
    return (1 << n) - 1 if n > 0 else 0


@dataclass
class Space:
    N: int                       # mdims
    kind: str                    # 'sig' | 'diag' | 'int'
    S: int = 0                   # Signature metric bits (bit set => square -1)
    diag: Optional[list] = None  # DiagonalForm values
    inf: bool = False            # option bit 1  (hasinf)
    orig: bool = False           # option bit 2  (hasorigin)
    dyad: int = 0                # dyadmode: -1 dyadic (V+V'), 0, +1 dual
    D: int = 0                   # diffvars
    mu: int = 0                  # diffmode

    # ---- derived -------------------------------------------------------
    @property
    def conformal(self) -> bool:
        return self.inf and self.orig

    @property
    def isdiag(self) -> bool:
        return True if self.kind in ("diag", "int") else not self.conformal

    @property
    def grade(self) -> int:
        return self.N - (2 if self.dyad < 0 else 1) * self.D

    @property
    def dmask(self) -> int:
        d, N = self.D, self.N
        if self.dyad < 0:
            v = ((1 << d) - 1) << (N - 2 * d)
            w = ((1 << d) - 1) << (N - d)
            return v | w
        return ((1 << d) - 1) << (N - d)

    def sigbits(self) -> int:
        """metric bits of Signature(V) as used by `parity` (Grassmann Signature(::Submanifold))."""
        if self.kind == "int":
            return 0
        if self.kind == "diag":
            return sum(1 << i for i, x in enumerate(self.diag) if x < 0)
        return 0 if self.conformal else self.S

    def g(self, i: int):
        """V[i] for the *parent* bundle (1-based): Signature -> +-1 from S, diag -> value."""
        if self.kind == "int":
            return 1
        if self.kind == "diag":
            return self.diag[i - 1]
        return -1 if (self.S >> (i - 1)) & 1 else 1


# ---------------------------------------------------------------- parities
def inv_count(a: int, b: int) -> int:
    """#{(i in a, j in b): i > j} == sum over bits k of a of popcount(b below k)."""
    s, k = 0, 0
    while a >> k:
        if (a >> k) & 1:
            s += popcount(b & lowmask(k))
        k += 1
    return s


def parityjoin(S: int, a: int, b: int) -> bool:
    return ((inv_count(a, b) + popcount(a & b & S)) & 1) == 1


def parity(V: Space, a: int, b: int) -> bool:
    Dm = ~V.dmask
    return parityjoin(V.sigbits(), a & Dm, b & Dm)


def parity_euclid(a: int, b: int) -> bool:          # parity(grade(V)::Int, a, b)
    return parityjoin(0, a, b)


def parityreverse(G: int) -> bool:
    return ((G - 1) * G // 2) % 2 == 1


def parityinvolute(G: int) -> bool:
    return G % 2 == 1


def parityclifford(G: int) -> bool:
    return parityreverse(G) ^ parityinvolute(G)


def parityright_raw(sumidx: int, G: int) -> bool:   # Leibniz parityright(V::Int,B::Int,G,N)
    return (sumidx + (G + 1) * G // 2) % 2 == 1


def parityleft_raw(sumidx: int, G: int, N: int) -> bool:
    return ((G % 2 == 1) and (N % 2 == 0)) ^ parityright_raw(sumidx, G)


def symmetricmask(V: Space, a: int, b: int):
    D = V.dmask
    aD, bD = a & D, b & D
    return a & ~D, b & ~D, aD | bD, aD & bD


def hasorigin_bits(V: Space, B: int) -> bool:        # Leibniz hasorigin(V,B::UInt)
    return (B & 2) == 2 if V.inf else (B & 1) == 1


def diffcheck(V: Space, A: int, B: int) -> bool:
    v = V.dmask
    conf = V.conformal
    hasinfAB = conf and ((A & 1) or (B & 1))
    hasorigAB = conf and (hasorigin_bits(V, A) or hasorigin_bits(V, B))
    hi = conf and (A & 1) and (B & 1) and not hasorigAB
    ho = conf and hasorigin_bits(V, A) and hasorigin_bits(V, B) and not hasinfAB
    return bool(hi or ho or (V.D != 0 and popcount(A & v) + popcount(B & v) > V.mu))


def complement(N: int, B: int, D: int = 0, P: int = 0) -> int:
    UP = (1 << (0 if P == 1 else P)) - 1
    ND = N - D
    C = ((~B) & (UP ^ lowmask(ND))) | (B & (UP ^ (lowmask(D) << ND)))
    C &= (1 << 64) - 1
    return C ^ UP if popcount(C & UP) != 1 else C


# ------------------------------------------------------------ regressive
def parityregressive(V: Space, a: int, b: int, skew: bool = False):
    """_parityregressive on Signature(V): returns (neg::bool, C, t, Z)."""
    N, D, G = V.N, V.D, V.grade
    A, B, Q, Z = symmetricmask(V, a, b)
    al, be = complement(N, A, D), complement(N, B, D)
    if popcount(al & be) == 0 and not diffcheck(V, al, be):
        C, L = al ^ be, popcount(A) + popcount(B)
        bas = complement(N, C, D) if (skew or A + B != 0) else 0
        par = (parityright_raw(sum(indices(A)), popcount(A))
               ^ parityright_raw(sum(indices(B)), popcount(B))
               ^ parityright_raw(sum(indices(C)), popcount(C)))
        neg = ((L * (L - G)) % 2 == 1) ^ par ^ parityjoin(V.sigbits(), al, be)
        return neg, bas | Q, True, Z
    return False, 0, False, Z


def regressive(V: Space, a: int, b: int):
    neg, C, t, Z = parityregressive(V, a, b)
    return (-1 if neg else 1), C, t, Z


# ------------------------------------------------------------ metric (non-diag)
def metric_matrix(V: Space) -> list[list[float]]:
    """metricdyad: conformal => hard-coded null pair + all +1 (ignores S bits beyond 2!)."""
    N = V.N
    M = [[0.0] * N for _ in range(N)]
    if V.conformal:
        M[0][1] = M[1][0] = -1.0
        for i in range(2, N):
            M[i][i] = 1.0
    else:
        for i in range(N):
            M[i][i] = float(V.g(i + 1))
    return M


def det(m: list[list[float]]) -> float:
    n = len(m)
    if n == 0:
        return 1.0
    if n == 1:
        return m[0][0]
    s = 0.0
    for j in range(n):
        if m[0][j] != 0:
            minor = [row[:j] + row[j + 1:] for row in m[1:]]
            s += (-1) ** j * m[0][j] * det(minor)
    return s


def combos(n: int, g: int) -> list[int]:
    """indexbasis(n,g): grade-g blades in lexicographic order of their sorted index lists."""
    from itertools import combinations
    return [sum(1 << (i - 1) for i in c) for c in combinations(range(1, n + 1), g)]


def compound_row(V: Space, B: int) -> list[tuple[int, float]]:
    M = metric_matrix(V)
    G = popcount(B)
    rows = [i - 1 for i in indices(B)]
    out = []
    for K in combos(V.grade, G):
        cols = [i - 1 for i in indices(K)]
        d = det([[M[r][c] for c in cols] for r in rows])
        out.append((K, d))
    return out


# ------------------------------------------------------------ interior (contraction)
def parityinterior(V: Space, a: int, b: int, lim: bool):
    """contraction(e_a, e_b) = e_a v *e_b  (Grassmann `interior`)."""
    A, B, Q, Z = symmetricmask(V, a, b)
    N = V.N
    if diffcheck(V, A, B):
        return ([], Z) if lim else (1, 0, False, Z)
    G = popcount(B)
    if V.isdiag:
        bas = [B]
        g = 1
        for i in indices(B):
            g *= V.g(i)
        gs = [g]
    else:
        row = compound_row(V, B)
        bas = [k for k, _ in row]
        gs = [x for _, x in row]
    gout, tout, acc = 0, False, {}
    order: list[int] = []
    for K, gk in zip(bas, gs):
        if gk != 0:  # (diffcheck2 is vacuous here: K has no diff bits)
            neg, C, t, _ = parityregressive(V, A, complement(N, K, V.D), True)
            CQ = C | Q
            tout |= t
            if t:
                ggg = -gk if (neg ^ parityright_raw(sum(indices(K)), G)) else gk
                if CQ not in acc:
                    acc[CQ] = 0
                    order.append(CQ)
                acc[CQ] += ggg
                gout += ggg
    if lim:
        return [(c, acc[c]) for c in order], Z
    if len(order) > 1:
        raise RuntimeError("limited interior")
    return gout, (order[0] if order else 0), tout, Z


def interior(V: Space, a: int, b: int):
    return parityinterior(V, a, b, False)


def parityinner(V: Space, a: int, b: int) -> float:
    """only the diag / conformal branch is live."""
    A, B, _, _ = symmetricmask(V, a, b)
    C = A & B
    g = 1
    for i in indices(C):
        g *= V.g(i)
    g = abs(g)
    return -g if parity(V, A, B) else g


# ------------------------------------------------------------ geometric product
def splitbasis(V: Space, B: int) -> list[int]:
    if B == 0:
        return []
    ind = indices(B)
    if V.isdiag:
        return [1 << (i - 1) for i in ind]
    M = metric_matrix(V)
    sub = [[M[i - 1][j - 1] for j in ind] for i in ind]
    f = [[j + 1 for j in range(len(ind)) if sub[i][j] != 0] for i in range(len(ind))]
    for i in range(len(f)):
        if (i + 1) not in f[i]:
            f[i].append(i + 1)
    j = 2
    while j <= len(f):
        t = False
        for k in range(1, j):
            for q in f[j - 1]:
                if q in f[k - 1]:
                    t = True
                    for p in f[j - 1]:
                        if p not in f[k - 1]:
                            f[k - 1].append(p)
                    f.pop(j - 1)
                    break
            if t:
                break
        if not t:
            j += 1
    return [sum(1 << (ind[p - 1] - 1) for p in grp) for grp in f]


def parityseq(V: Space, bs: list[int]) -> int:
    if V.isdiag or len(bs) == 1:
        return 1
    out = False
    for i in range(1, len(bs)):
        out ^= parity_euclid(bs[i - 1], bs[i])
    return -1 if out else 1


State = tuple  # ((Ae, Aeg), (Ai, Aig))


def pg_right(V: Space, st: State, B: int) -> list[State]:
    (Ae, Aeg), (Ai, Aig) = st
    G = popcount(B)
    flip = parityclifford(G) ^ ((G * popcount(Ai)) % 2 == 1)
    if V.isdiag or V.conformal:
        g, C, t, _ = interior(V, Ai, B)
        Aigg = Aig * g
        Cg = -Aigg if flip else Aigg
        CCg = [((Ae, Aeg), (C, Cg))] if t else []
    else:
        Cgs, _ = parityinterior(V, Ai, B, True)
        AigAeg = Aig * Aeg
        gg = -AigAeg if flip else AigAeg
        CCg = [((Ae, gg), cg) for cg in Cgs]
    if Ai & B == 0:
        p = -Aeg if parity_euclid(Ai ^ Ae, B) else Aeg
        return [((Ae ^ B, p * Aig), (Ai, 1))] + CCg
    return CCg


def pg_left(V: Space, A: int, st: State) -> list[State]:
    (Be, Beg), (Bi, Big) = st
    G = popcount(A)
    if V.isdiag or V.conformal:
        g, C, t, _ = interior(V, Bi, A)
        Bigg = Big * g
        Cg = -Bigg if parityreverse(G) else Bigg
        CCg = [((Be, Beg), (C, Cg))] if t else []
    else:
        Cgs, _ = parityinterior(V, Bi, A, True)
        BigBeg = Big * Beg
        gg = -BigBeg if parityreverse(G) else BigBeg
        CCg = [((Be, gg), cg) for cg in Cgs]
    if A & Bi == 0:
        p = -Beg if parity_euclid(A, Be ^ Bi) else Beg
        return [((A ^ Be, p * Big), (Bi, 1))] + CCg
    return CCg


def combinebasis(vals: list[State]) -> list[tuple[int, float]]:
    out = []
    for (E, Eg), (I, Ig) in vals:
        if E & I == 0:
            out.append((E ^ I, Eg * Ig))
    return out


def paritygeometric(V: Space, A: int, B: int) -> list[tuple[int, float]]:
    a, b = splitbasis(V, A), splitbasis(V, B)
    ga = max((popcount(x) for x in a), default=0)
    gb = max((popcount(x) for x in b), default=0)
    split_b = (popcount(A) >= popcount(B)) if (ga <= 1 and gb <= 1) else (ga >= gb)
    if split_b:
        if not b:
            vals = [((0, 1), (A, 1))]
        else:
            vals = pg_right(V, ((0, parityseq(V, b)), (A, 1)), b[0])
            for grp in b[1:]:
                vals = [s2 for s in vals for s2 in pg_right(V, s, grp)]
    else:
        if not a:
            vals = [((0, 1), (B, 1))]
        else:
            vals = pg_left(V, a[-1], ((0, parityseq(V, a)), (B, 1)))
            for grp in reversed(a[:-1]):
                vals = [s2 for s in vals for s2 in pg_left(V, grp, s)]
    return combinebasis(vals)


def mul(V: Space, a: int, b: int):
    """returns (terms: dict bits->coef, zcoef: Z bits or 0). Mirrors algebra.jl `mul`."""
    if V.isdiag:
        if V.D != 0 and diffcheck(V, a, b):
            return {}, 0
        A, B, Q, Z = symmetricmask(V, a, b)
        d = (A ^ B) | Q
        if A & B == 0:
            c = -1 if parity(V, a, b) else 1
        else:
            c = parityinner(V, A, B)
        return {d: c}, Z
    out: dict[int, float] = {}
    for k, c in paritygeometric(V, a, b):
        out[k] = out.get(k, 0) + c
    return out, 0


def wedge(V: Space, a: int, b: int):
    A, B, Q, Z = symmetricmask(V, a, b)
    if (A & B) or diffcheck(V, a, b):
        return {}, 0
    return {(A ^ B) | Q: (-1 if parity(V, a, b) else 1)}, Z


def vee(V: Space, a: int, b: int):
    p, C, t, Z = regressive(V, a, b)
    return ({C: p} if t else {}), Z


def contraction(V: Space, a: int, b: int):
    if V.isdiag or V.conformal:
        g, C, t, Z = interior(V, a, b)
        return ({C: g} if t else {}), Z
    Cg, Z = parityinterior(V, a, b, True)
    return {c: g for c, g in Cg}, Z


# ------------------------------------------------------------ unary
def gradeB(V: Space, B: int) -> int:
    return popcount(B & lowmask(V.grade))


def reverse(V, B):
    return {B: -1 if parityreverse(gradeB(V, B)) else 1}


def involute(V, B):
    return {B: -1 if parityinvolute(gradeB(V, B)) else 1}


def clifford(V, B):
    return {B: -1 if parityclifford(gradeB(V, B)) else 1}


def antireverse(V, B):
    return {B: -1 if parityreverse(V.grade - gradeB(V, B)) else 1}


def _null(V: Space, B: int, v):
    if V.conformal and popcount(B & 3) == 1:
        return 2 * v if B & 1 else v / 2
    return v


def complementright(V: Space, B: int):
    ND = V.N - V.D
    ind = indices(B & lowmask(ND))
    s = -1 if parityright_raw(sum(ind), popcount(B)) else 1
    return {complement(V.N, B, V.D, 0): s * _null(V, B, 1)}


def complementleft(V: Space, B: int):
    ND = V.N - V.D
    ind = indices(B & lowmask(ND))
    s = -1 if parityleft_raw(sum(ind), popcount(B), ND) else 1
    return {complement(V.N, B, V.D, 0): s * _null(V, B, 1)}


def _hodge_g(V: Space, B: int):
    ND = V.N - V.D
    ind = indices(B & lowmask(ND))
    g = 1
    for i in ind:
        g *= V.g(i)
    c = V.conformal and (B & 3) == 2
    return ind, g, c, ND


def complementrighthodge(V: Space, B: int):
    ind, g, c, ND = _hodge_g(V, B)
    s = parityright_raw(sum(ind), popcount(B)) ^ c
    return {complement(V.N, B, V.D, int(V.inf) + int(V.orig)): -g if s else g}


def complementlefthodge(V: Space, B: int):
    ind, g, c, ND = _hodge_g(V, B)
    s = parityleft_raw(sum(ind), popcount(B), ND) ^ c
    return {complement(V.N, B, V.D, int(V.inf) + int(V.orig)): -g if s else g}


def cross(V: Space, a: int, b: int):
    w, Z = wedge(V, a, b)
    if not w:
        return {}, Z
    (k, c), = w.items()
    return {kk: c * vv for kk, vv in complementrighthodge(V, k).items()}, Z
