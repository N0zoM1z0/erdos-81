"""Exact perturbation construction for clique edge partitions.

No floating-point arithmetic or optimization backend is used.
The finite local lemma does not require chordality.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations
from typing import Iterable

Edge = tuple[int, int]
Part = tuple[int, ...]

def edge(u: int, v: int) -> Edge:
    if u == v:
        raise ValueError('Loops are not allowed')
    return (u,v) if u < v else (v,u)

def factor_complete(p: int) -> list[list[Edge]]:
    """Round-robin factorization of K_p; at most p matching classes."""
    if p < 0:
        raise ValueError('Negative order')
    if p < 2:
        return []
    n = p + (p % 2)
    a = list(range(n))
    factors = []
    for _ in range(n-1):
        pairs = [edge(a[i],a[n-1-i]) for i in range(n//2)
                 if a[i] < p and a[n-1-i] < p]
        factors.append(pairs)
        a = [a[0],a[-1]] + a[1:-1]
    assert set(e for f in factors for e in f) == set(combinations(range(p),2))
    assert sum(map(len,factors)) == p*(p-1)//2
    return factors

def graph_edges(p: int, q: int, missing: Iterable[Edge], outside: Iterable[Edge]) -> set[Edge]:
    miss = {edge(*e) for e in missing}
    out = {edge(*e) for e in outside}
    if p < 1 or q < 0:
        raise ValueError('Need p>=1 and q>=0')
    if any(not (0 <= x < p <= y < p+q) for x,y in miss):
        raise ValueError('Missing pairs must be root-outside pairs')
    if any(not (p <= x < y < p+q) for x,y in out):
        raise ValueError('Outside edges must have two outside endpoints')
    return set(combinations(range(p),2)) | ({(x,y) for x in range(p) for y in range(p,p+q)} - miss) | out

def verify_partition(
    edges: set[Edge], parts: Iterable[Part], max_size: int | None = None
) -> int:
    """Verify an exact clique partition, optionally with a block-size cap."""
    if max_size is not None and max_size < 2:
        raise ValueError('max_size must be at least 2')
    count = Counter()
    number = 0
    for Q in parts:
        if len(Q) < 2 or len(set(Q)) != len(Q):
            raise AssertionError(('Malformed part',Q))
        if max_size is not None and len(Q) > max_size:
            raise AssertionError(('Part exceeds the declared maximum size',Q,max_size))
        qe = {edge(x,y) for x,y in combinations(Q,2)}
        if not qe <= edges:
            raise AssertionError(('Nonclique part',Q,qe-edges))
        count.update(qe)
        number += 1
    if set(count) != edges or any(v != 1 for v in count.values()):
        raise AssertionError('Not an exact edge partition')
    return number

def construct(p: int, q: int, missing: Iterable[Edge] = (), outside: Iterable[Edge] = (), max_size: int = 4) -> dict:
    """Return an attaining integral partition and a source-bound dual.

    Sufficient condition: a+2m <= min(p,q-p), where a is the number
    of missing spokes and m the number of outside edges.
    max_size=4 gives the unrestricted optimum; max_size=3 gives the
    exact triangle-and-edge optimum.
    """
    if max_size not in (3,4):
        raise ValueError('max_size must be 3 or 4')
    miss = {edge(*e) for e in missing}
    out = {edge(*e) for e in outside}
    edges = graph_edges(p,q,miss,out)
    a,m = len(miss),len(out)
    t = a+2*m
    if t > min(p,q-p):
        raise ValueError('The sufficient defect-capacity condition fails')
    bad = {y for x,y in miss} | {x for e in out for x in e}
    clean = [v for v in range(p,p+q) if v not in bad]
    assert len(clean) >= p
    used_roots: set[int] = set()
    reserved_pairs: set[Edge] = set()
    parts: list[Part] = []
    for u,v in sorted(out):
        available = [x for x in range(p) if x not in used_roots and (x,u) not in miss and (x,v) not in miss]
        need = 2 if max_size == 4 else 1
        assert len(available) >= need
        roots = available[:need]
        used_roots.update(roots)
        parts.append(tuple(roots+[u,v]))
        if need == 2:
            reserved_pairs.add(edge(*roots))
    for host,matching in zip(clean,factor_complete(p)):
        for x,y in matching:
            if (x,y) not in reserved_pairs:
                parts.append((x,y,host))
    covered: set[Edge] = set()
    for Q in parts:
        qe = {edge(x,y) for x,y in combinations(Q,2)}
        assert not (covered & qe)
        covered |= qe
    parts.extend(sorted(edges-covered))
    number = verify_partition(edges,parts,max_size=max_size)
    expected = p*q-p*(p-1)//2-a-(2 if max_size==4 else 1)*m
    assert number == expected
    # For max_size 4 this dual is feasible on EVERY clique, of any size.
    # For max_size 3 it is feasible on all K2 and K3.
    y_weight = -2 if max_size==4 else -1
    weights = {e: (-1 if e[1]<p else y_weight if e[0]>=p else 1) for e in edges}
    assert sum(weights.values()) == number
    return {'p':p,'q':q,'missing':sorted(miss),'outside':sorted(out),
            'edges':sorted(edges),'parts':parts,'value':number,
            'max_size':max_size,'clean_hosts':clean,'dual_weights':weights}

def json_certificate(result: dict) -> dict:
    r = {k:v for k,v in result.items() if k != 'dual_weights'}
    r['dual_weights'] = [[*e,w] for e,w in sorted(result['dual_weights'].items())]
    return r

def jacobian_partition(result: dict) -> dict:
    label = lambda v: f'v{v:03d}'
    return {'graph': {'vertices':[label(v) for v in range(result['p']+result['q'])],
                      'edges':[[label(x),label(y)] for x,y in result['edges']]},
            'parts':[[label(v) for v in Q] for Q in result['parts']]}

def jacobian_dual(result: dict) -> dict:
    label = lambda v: f'v{v:03d}'
    return {'graph': {'vertices':[label(v) for v in range(result['p']+result['q'])],
                     'edges':[{'endpoints':[label(x),label(y)],'weight':{'num':str(w),'den':'1'}}
                              for (x,y),w in sorted(result['dual_weights'].items())]}}

def certify_near_extremizer(n: int, edges_input: Iterable[Edge], s: int) -> dict | None:
    """Recognize and construct the canonical finite-defect certificate.

    Every successful return is valid at the supplied finite order, without
    asymptotic assumptions. A rejection is not a bound on cp in general.
    The accompanying theorem makes this a complete decision test when G is
    chordal, n is beyond the closure threshold, and 0<=s<=n/100.
    """
    if n < 1 or s < 0:
        raise ValueError('Need positive order and nonnegative s')
    edges = {edge(*e) for e in edges_input}
    if any(not(0 <= x < y < n) for x,y in edges):
        raise ValueError('An edge endpoint is out of range')
    deg=[0]*n
    for x,y in edges:
        deg[x]+=1; deg[y]+=1
    root=[v for v in range(n) if 2*deg[v]>n]
    if not root or any(edge(x,y) not in edges for x,y in combinations(root,2)):
        return None
    root_set=set(root); out=[v for v in range(n) if v not in root_set]
    order=root+out; pos={v:i for i,v in enumerate(order)}
    p,q=len(root),len(out)
    missing=[(pos[x],pos[y]) for x in root for y in out if edge(x,y) not in edges]
    outside=[edge(pos[x],pos[y]) for x,y in edges if x not in root_set and y not in root_set]
    cost=p*q-p*(p-1)//2-len(missing)-2*len(outside)
    defect=n*(n+1)//6-cost
    if defect > s or len(missing)+2*len(outside)>min(p,q-p):
        return None
    ans=construct(p,q,missing,outside,4)
    actual_parts=[tuple(order[x] for x in part) for part in ans['parts']]
    assert verify_partition(edges,actual_parts,max_size=4)==cost
    return {'root':root, 'outside_vertices':out, 'missing_count':len(missing),
            'outside_edge_count':len(outside), 'deficit':defect,
            'cp':cost, 'parts':actual_parts}
