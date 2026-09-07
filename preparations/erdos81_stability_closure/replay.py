#!/usr/bin/env python3
"""Dependency-free exact replay of saved LP and copy-path certificates."""
from pathlib import Path
from itertools import combinations
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parent

def normkey(k): return (k[0],tuple(tuple(e) for e in k[1]))
def nbrs(n,edges):
    A=[set() for _ in range(n)]
    for u,v in edges:A[u].add(v);A[v].add(u)
    return A

def chordal(n,edges):
    A=nbrs(n,edges);R=set(range(n))
    while R:
        v=next((v for v in R if all(y in A[x] for x,y in combinations(A[v]&R,2))),None)
        if v is None:return False
        R.remove(v)
    return True

def main():
    vals={};primal_count=0;dual_count=0
    for row in json.loads((ROOT/'mixed_lp_certificates.json').read_text()):
        n=row['n'];es={tuple(e) for e in row['edges']};A=nbrs(n,es)
        packing=[(Q,F(x)) for Q,x in row['packing']]
        dual={tuple(e):F(x) for e,x in row['dual']}
        assert all(x>=0 for x in dual.values())
        assert set(dual)<=es
        loads={e:F(0) for e in es};gain=F(0)
        for Q,x in packing:
            assert x>=0 and len(Q) in (3,4) and len(set(Q))==len(Q)
            qe=[tuple(sorted(e)) for e in combinations(Q,2)]
            assert all(e in es for e in qe)
            gain+=(len(qe)-1)*x
            for e in qe:loads[e]+=x
            primal_count+=1
        assert all(x<=1 for x in loads.values())
        for s in (3,4):
            for Q in combinations(range(n),s):
                qe=list(combinations(Q,2))
                if all(e in es for e in qe):
                    assert sum(dual.get(e,F(0)) for e in qe)>=len(qe)-1
                    dual_count+=1
        assert gain==sum(dual.values())
        assert F(row['phi'])==len(es)-gain
        vals[(n,tuple(sorted(es)))]=F(row['phi'])
    step_count=0
    for path in json.loads((ROOT/'paths.json').read_text()):
        ks=[normkey(k) for k in path]
        for k in ks:assert chordal(*k)
        for before,after in zip(ks,ks[1:]):
            n,ee=before;ff=set(after[1]);ee=set(ee)
            assert vals[after]>=vals[before]
            dif=ee^ff;assert len(dif)<=n-2
            changed=set.intersection(*(set(e) for e in dif)) if dif else set(range(n))
            aa=nbrs(n,ee);bb=nbrs(n,ff)
            assert any(any(v!=u and v not in aa[u] and bb[u]==aa[v]
                           for v in range(n)) for u in changed)
            step_count+=1
        n,ee=ks[-1];aa=nbrs(n,ee)
        core={v for v in range(n) if len(aa[v])==n-1}
        assert not any(u not in core and v not in core for u,v in ee)
    result={'LP_certificates_replayed':len(vals),'positive_packing_entries':primal_count,
            'all_triangle_K4_dual_constraints':dual_count,'copy_steps_replayed':step_count,
            'verdict':'PASS'}
    (ROOT/'replay_report.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
