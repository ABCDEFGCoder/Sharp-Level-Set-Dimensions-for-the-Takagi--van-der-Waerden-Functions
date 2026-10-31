#!/usr/bin/env python3
"""Takagi level-set dimensions: exact finite cross-checks.

Companion to Zixuan Ye, "Sharp Level-Set Dimensions for the
Takagi--van der Waerden Functions" (October 2026).

Run with Python 3, without optimization: python3 takagi_level_set_checks.py
Only the Python standard library is required. Every proof-related decision
uses integers or fractions.Fraction; no floating-point sampling is used.

The manuscript proves the universal statements analytically. These finite
checks are diagnostics, not a formal proof of the manuscript, independent
peer review, or an exhaustive check over all bases, slopes and depths.

Correspondence with the manuscript:
  profile/local_check: integer refinement and residue-exclusion lemmas;
  polygon_counts/verify_recursion: coupled count and explicit-bound propositions;
  exact_range/children/advance: exact tilted ranges and state expansion;
  check_ternary_tail_cover: endpoint-sensitive actual-level covering lemma;
  check_residue_rigidity/check_critical_counts: odd-base rigidity and counts;
  check_sparse_equality_blocks: four-step ternary return table;
  check_scalar_counterexample: the scalar-recursion obstruction example.

AI assistance in developing arguments, code and exposition is disclosed
in the manuscript. This script was generated and executed in that workflow.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q


def profile(r, j):
    """r*(psi(j/(2*r))+psi(j/2)/r), an integer."""
    a = j % (2*r)
    numerator = min(a, 2*r-a) + (a % 2)
    assert numerator % 2 == 0
    return numerator // 2


def local_check(r, s, phase):
    q, v = r//2, (r+1)//2
    values = [s*d + profile(r, phase*r+d) for d in range(r*r+1)]
    increments = [b-a for a,b in zip(values, values[1:])]
    assert all(s-1 <= a <= s+1 for a in increments)
    flats = Counter()
    cross = Counter()
    for a,b in zip(values, values[1:]):
        if a == b:
            flats[a] += 1
        else:
            for K in range(min(a,b), max(a,b)):
                cross[K] += 1
    if s == 0:
        assert flats == Counter({k:r for k in range(1,q+1)})
        assert cross == Counter({k:r for k in range(v)})
        return

    # A nonflat parent stays monotone, and contributes at most one
    # nonhorizontal child to each open fine strip.
    assert all(a >= 0 for a in increments) if s>0 else all(a <= 0 for a in increments)
    assert all(a <= 1 for a in cross.values())
    assert all(a <= 1 for a in flats.values())
    if abs(s) >= 2:
        assert not flats
    for K in flats:
        # Sources of new flat cells have disjoint height residues from
        # descendants of a flat parent.
        assert K % r not in range(1,q+1)
        h, ell = divmod(K,r*r)
        assert ell == 0 or ell >= q+1
        selected = h-1 if ell == 0 else h
        assert min(0,s) <= selected < max(0,s)
    for K in cross:
        h, _ = divmod(K,r*r)
        old = lambda k: min(0,s) <= k < max(0,s)
        if r%2:
            assert old(h-1) or old(h)
        else:
            assert old(h)


def check_local_profiles():
    checked = 0
    for r in range(2,42):
        phases = (0,1) if r%2 else (0,)
        for phase in phases:
            for s in range(-6,7):
                local_check(r,s,phase)
                checked += 1
    print('PASS: local profiles,', checked, 'exact parameter cases')


def polygon_counts(r,m):
    """P_(2m) at all endpoints of I_(2m,j), in units r**(1-2m)."""
    n = 2*m
    cells = 2*r**(n-1)
    periods = [2*r**d for d in range(n)]
    values = []
    for j in range(cells+1):
        H = sum(min(j%p,p-j%p) for p in periods)
        assert H%2 == 0
        values.append(H//2)
    flats = Counter()
    events = defaultdict(int)
    for a,b in zip(values, values[1:]):
        if a == b:
            flats[a] += 1
        else:
            a,b = min(a,b),max(a,b)
            events[a] += 1
            events[b] -= 1
    cross = Counter()
    active = 0
    for h in range(min(values), max(values)+1):
        active += events[h]
        if active:
            cross[h] = active
    assert active == 0
    return flats,cross


def verify_recursion(r,m,old,new):
    A,B = old
    AA,BB = new
    q,v = r//2,(r+1)//2
    for K,count in AA.items():
        h,ell = divmod(K,r*r)
        if 1 <= K%r <= q:
            expected = r*A[h] if 1 <= ell <= q else 0
            assert count == expected, (r,m,K,count,expected)
        else:
            selected = h-1 if ell == 0 else h
            assert count <= B[selected], (r,m,K,count,B[selected])
    for h,count in A.items():
        for k in range(1,q+1):
            assert AA[r*r*h+k] == r*count
    for K,count in BB.items():
        h,ell = divmod(K,r*r)
        limit = (r*A[h] if ell < v else 0) + B[h]
        if r%2:
            limit += B[h-1]
        assert count <= limit, (r,m,K,count,limit)
    a,b = max(A.values()),max(B.values())
    aa,bb = max(AA.values()),max(BB.values())
    gamma = 2 if r%2 else 1
    assert aa <= max(r*a,b)
    assert bb <= r*a+gamma*b


def check_global_polygons():
    for r,last in ((2,6),(3,5),(4,4),(5,4),(6,3),(7,3),(8,3),(9,3)):
        old = polygon_counts(r,1)
        assert max(old[0].values()) == max(old[1].values()) == 2
        for m in range(1,last+1):
            if m>1:
                new = polygon_counts(r,m)
                verify_recursion(r,m-1,old,new)
                old = new
            a,b = max(old[0].values()),max(old[1].values())
            gamma = 2 if r%2 else 1
            assert a == 2*r**(m-1)
            assert b <= 2*(r**m-gamma**m)//(r-gamma)
            print('PASS: r=',r,'m=',m,'flat maximum=',a,
                  'crossing maximum=',b,flush=True)


def exact_range(r,t):
    """Exact range of f_t for the odd-base half-graph (r >= 3 odd)."""
    assert r >= 3 and r % 2 == 1
    # Exact tilted-range identity proved in the manuscript.
    A = Q(r,r-1)
    if t>=0:
        return Q(0),A+t
    return A+t-A/r**(-t),A/r**(-t)


def halfgraph_cells(r,n):
    states = [(0,0)]
    for _ in range(n):
        following = []
        for t,B in states:
            a = t+1
            for j in range(r):
                following.append(((-1 if j%2 else 1)*a,
                                  r*B+a*(j+j%2)))
        states = following
    intervals = []
    for t,B in states:
        lo,hi = exact_range(r,t)
        # A level y of T corresponds to level 2*y of its half-graph.
        intervals.append(((B+lo)/(2*r**n),(B+hi)/(2*r**n)))
    return intervals


def check_ternary_tail_cover():
    """Verify the endpoint-sensitive cover inequality at EVERY real height
    for four complete finite levels, using independent exact image intervals.
    """
    r = 3
    for m in range(1,5):
        A,B = polygon_counts(r,m)
        delta = Q(1,r**(2*m-1))
        events = defaultdict(lambda:[0,0])
        for lo,hi in halfgraph_cells(r,2*m-1):
            # Two reflected halves of [0,1].
            events[lo][0] += 2
            events[hi][1] += 2
        top = max(events)
        for h in range(int(top/delta)+2):
            events[h*delta]  # Include every jump in the proposed upper bound.
        coordinates = sorted(events)
        active = 0
        for i,y in enumerate(coordinates):
            start,end = events[y]
            at = active+start
            h = y//delta
            assert at <= A[h]+B[h-1]+B[h], (m,y,at)
            active = at-end
            if i+1<len(coordinates):
                middle = (y+coordinates[i+1])/2
                h = middle//delta
                assert active <= A[h]+B[h-1]+B[h], (m,middle,active)
        assert active == 0
        print('PASS: ternary exact tail-cover inequality, all heights, m=',m)


def check_sparse_equality_blocks():
    expected = {5:3,6:3,10:9,14:3,15:3}
    periods = [2*3**d for d in range(4)]
    def height(j):
        H = sum(min(j%p,p-j%p) for p in periods)
        assert H%2 == 0
        return H//2  # 27*P_4(j/54).
    for phase in (0,1):
        groups = defaultdict(list)
        for d in range(81):
            a,b = height(27*phase+d),height(27*phase+d+1)
            if a == b:
                groups[a].append(d)
        assert {k:len(v) for k,v in groups.items()} == expected
        for k in (5,10):
            assert all(b-a>=2 for a,b in zip(groups[k],groups[k][1:]))
        print('PASS: sparse equality blocks, phase=',phase,
              {k:groups[k] for k in (5,10)})
    # Check the exact all-fast height and the elementary digit-separation bound.
    assert Q(1,3)+Q(10,3)*Q(1,80) == Q(3,8)
    assert Q(1,80)<1



def children(r, t, z):
    a = t + 1
    answer = []
    for j in range(r):
        s = (-1 if j % 2 else 1) * a
        w = r * z - a * (j + j % 2)
        lo, hi = exact_range(r, s)
        if lo <= w <= hi:
            answer.append((j, s, w))
    return answer


def advance(r, states):
    answer = Counter()
    for (t, z), multiplicity in states.items():
        for _, s, w in children(r, t, z):
            answer[s, w] += multiplicity
    return answer


def check_residue_rigidity():
    checked = 0
    for r in (3, 5, 7, 9, 11, 13, 15):
        D = r * r - 1
        for k in range(1, (r + 1) // 2):
            d = Q(2 * k, D)
            for t in range(-20, 21):
                lo, hi = exact_range(r, t)
                for residue in (d, r * d):
                    for h in range(-12, 13):
                        z = residue + 2 * h
                        if not lo <= z <= hi:
                            continue
                        got = children(r, t, z)
                        if (t, z) == (0, r * d):
                            assert len(got) == 3
                            assert {j for j, _, _ in got} == {
                                2 * k - 2, 2 * k - 1, 2 * k}
                        elif (t, z) == (-1, d):
                            assert len(got) == r
                            assert all((s, w) == (0, r * d)
                                       for _, s, w in got)
                        else:
                            assert len(got) == 1, (r, k, t, z, got)
                            assert all((s, w) not in ((0, r * d), (-1, d))
                                       for _, s, w in got)
                        checked += 1
    print('Finite residue cross-check:', checked, 'valid states: PASS')


def check_critical_counts():
    for r in (3, 5, 7, 9, 11):
        for k in range(1, (r + 1) // 2):
            z = Q(2 * k * r, r * r - 1)
            states = Counter({(0, z): 1})
            for n in range(25):
                m = n // 2
                numerator = ((r + 1) if n % 2 == 0 else (3 * r - 1))
                expected = Q(numerator * r**m - 2, r - 1)
                assert expected.denominator == 1
                assert sum(states.values()) == expected
                states = advance(r, states)
    # A direct four-state verification of the singleton used in the explicit
    # ternary condensation set: f(u)+u=1/4 has the unique solution u=1/18.
    orbit = [(1, Q(1, 4)), (2, Q(3, 4)),
             (3, Q(9, 4)), (-4, Q(-5, 4))]
    for i, (t, z) in enumerate(orbit):
        got = children(3, t, z)
        assert len(got) == 1
        target = orbit[i + 1] if i < 3 else orbit[2]
        assert got[0][1:] == target
    assert Q(1, 2) / 3 / 3 == Q(1, 18)
    print('Critical counts through depth 24 and ternary singleton: PASS')


def check_scalar_counterexample():
    y = Q(6425, 17496)
    states = Counter({(0, 2*y): 1})
    counts = {}
    expected = {
        7: Counter({(-1,Q(1,4)):5, (1,Q(1,4)):5,
                    (5,Q(25,4)):3, (7,Q(33,4)):2}),
        9: Counter({(-1,Q(1,4)):15, (1,Q(1,4)):15,
                    (1,Q(9,4)):15, (3,Q(9,4)):5,
                    (7,Q(25,4)):3, (9,Q(33,4)):2})}
    for n in range(10):
        if n in expected:
            assert states == expected[n], (n,states)
            counts[n] = sum(states.values())
        states = advance(3,states)
    assert counts == {7:15,9:55}
    N8,N10 = 2*counts[7],2*counts[9]
    assert N10 > 3*N8+4
    print('PASS: scalar recurrence counterexample, y=',y,
          'N_3,8=',N8,'N_3,10=',N10)


def main():
    check_local_profiles()
    check_global_polygons()
    check_ternary_tail_cover()
    check_residue_rigidity()
    check_critical_counts()
    check_sparse_equality_blocks()
    check_scalar_counterexample()
    print('PASS: all manuscript cross-checks completed with exact arithmetic')


if __name__ == '__main__':
    main()
