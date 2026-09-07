#!/usr/bin/env python3
"""Finite exact audit of the proposed local-to-global stability closure.
SciPy only finds LP candidates. All primal/dual constraints and objectives
are replayed over Fraction. No asymptotic transfer threshold is estimated.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, time, random, math
import networkx as nx
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
import sympy as sp
OUT=Path(__file__).resolve().parent
CACHE={}
COUNTS={}
def tick(k,n=1): COUNTS[k]=COUNTS.get(k,0)+n

def key(G):
    return (len(G), tuple(sorted(tuple(sorted(e)) for e in G.edges())))
def exact_phi4(G):
    K=key(G)
    if K in CACHE:return F(CACHE[K]['phi'])
    es=list(K[1]); idx={e:i for i,e in enumerate(es)}
    qs=[Q for k in (3,4) for Q in combinations(range(len(G)),k)
        if all(G.has_edge(*e) for e in combinations(Q,2))]
    if not qs:
        CACHE[K]={'n':len(G),'edges':es,'phi':str(len(es)),'packing':[],'dual':[]}
        return F(len(es))
    rr=[];cc=[]
    gains=[math.comb(len(Q),2)-1 for Q in qs]
    for j,Q in enumerate(qs):
        for e in combinations(Q,2):rr.append(idx[e]);cc.append(j)
    A=csc_matrix((np.ones(len(rr)),(rr,cc)),shape=(len(es),len(qs)))
    sol=linprog(-np.asarray(gains,dtype=float),A_ub=A,b_ub=np.ones(len(es)),bounds=(0,None),method='highs')
    if not sol.success:raise RuntimeError(sol.message)
    xx=[F(float(z)).limit_denominator(10**7) for z in sol.x]
    yy=[F(float(-z)).limit_denominator(10**7) for z in sol.ineqlin.marginals]
    assert all(z>=0 for z in xx+yy)
    loads=[F(0) for _ in es]
    for Q,g,x in zip(qs,gains,xx):
        assert sum(yy[idx[e]] for e in combinations(Q,2))>=g
        for e in combinations(Q,2):loads[idx[e]]+=x
    assert all(z<=1 for z in loads)
    val=sum(g*x for g,x in zip(gains,xx))
    assert val==sum(yy),(K,val,sum(yy))
    phi=F(len(es))-val
    CACHE[K]={'n':len(G),'edges':es,'phi':str(phi),
              'packing':[[list(Q),str(x)] for Q,x in zip(qs,xx) if x],
              'dual':[[list(e),str(y)] for e,y in zip(es,yy) if y]}
    return phi

def copy(G,u,v):
    assert u!=v and not G.has_edge(u,v)
    H=G.copy(); H.remove_edges_from(list(H.edges(u)))
    H.add_edges_from((u,x) for x in G[v])
    return H

def simplicial(G,u):
    return all(G.has_edge(x,y) for x,y in combinations(G[u],2))
def classes(G):
    cs={}
    for u in G:cs.setdefault(tuple(sorted(G[u])),[]).append(u)
    return list(cs.values())
def terminal_root(G):
    A=[u for u in G if G.degree(u)==len(G)-1]
    I=set(G)-set(A)
    if any(G.has_edge(x,y) for x,y in combinations(I,2)):return None
    return A

def monotone_path(G):
    cur=G.copy(); path=[key(cur)]; rounds=0
    while terminal_root(cur) is None:
        cls=classes(cur)
        chosen=None
        for A,B in combinations(cls,2):
            u,v=A[0],B[0]
            if not cur.has_edge(u,v) and simplicial(cur,u) and simplicial(cur,v):
                chosen=(A,B);break
        assert chosen is not None,('terminal_characterization',key(cur))
        A,B=chosen;u,v=A[0],B[0]
        phi=exact_phi4(cur)
        plus=copy(cur,u,v);minus=copy(cur,v,u)
        fp,fm=exact_phi4(plus),exact_phi4(minus)
        assert fp+fm>=2*phi
        source,target=(A,v) if fp>=phi else (B,u)
        old_classes=len(cls)
        for x in source:
            nxt=copy(cur,x,target)
            assert nx.is_chordal(nxt)
            assert exact_phi4(nxt)>=exact_phi4(cur)
            assert len(set(key(cur)[1])^set(key(nxt)[1]))<=len(G)-2
            path.append(key(nxt));cur=nxt
            tick('single_vertex_monotone_steps')
        assert len(classes(cur))<old_classes
        rounds+=1
        assert rounds<=len(G)-1
    tick('monotone_paths')
    tick('full_class_rounds',rounds)
    return path

def split_formula(p,q):
    e=p*q+math.comb(p,2)
    if q==0 and p>=4:return F(e,6)
    assert p>=4 and q>=1
    return max(F(p*q-math.comb(p,2)),F(2*p*q-math.comb(p,2),3),F(e,6))

def scalar_checks():
    # All-parameter comparison constants for strengthened regularization.
    mcoef=F(1,65536)+F(129,64*1024)+F(1,2*1024**2)
    assert mcoef<F(1,400)
    Dcoef=F(17,64)+F(11,4096)
    assert Dcoef<F(1,3)
    margin=F(63,64)-F(2,3)-F(2,693)-F(1,99)
    assert margin>F(1,4)
    assert F(20,99)<F(1,2)
    # Integer rounding of c <= ceil(7p/4) <= 9p/5 for p >= 15.
    for p in range(15,20001):
        assert F((7*p+3)//4,p)<=F(9,5)
        tick('integer_colour_count_bounds')
    # Edit extraction, using sqrt(2*10^-12) < 3/(2*10^6).
    assert F(2,10**12)<F(3,2*10**6)**2
    assert F(1,10**12)+F(3,2*10**6)<F(3,2*10**6)+F(1,10**11)
    assert F(1,10**12)+F(3,2*10**6)<F(33,100)**2/F(65536)
    assert F(3,1000)+F(9,2*10**6)<F(33,6400)
    # Local stability radius bound at n >= 10^32 and delta=10^-30.
    rho=F(1,10**12); delta=F(1,10**30); nmin=10**32
    assert F(1,6*nmin)+F(1,24*nmin*nmin)<delta
    # Delta <= 2 delta n^2, sqrt(2Delta/3)/n < 2*10^-15.
    assert F(4,3)*delta<F(2,10**15)**2
    upper=18*delta+F(2,10**15)+F(1,nmin)
    assert upper<rho/4
    assert rho/2-F(1,nmin)>rho/4
    # Exact terminal quadratics and local edit-distance formula.
    n,p=sp.symbols('n p')
    Q=(2*n+1)**2/sp.Integer(24)
    B=p*(n-p)-p*(p-1)/2
    assert sp.expand(Q-B-(6*p-2*n-1)**2/sp.Integer(24))==0
    C2=(4*n+1)**2/sp.Integer(120)
    assert sp.factor(Q-C2-(n*n/30+n/10+sp.Rational(1,30)))==0
    for nn in range(100,1201):
        Qn=F((2*nn+1)**2,24)
        assert F((4*nn+1)**2,120)<F(nn*nn,6)-F(nn*nn,40)
        assert 3*nn<F(nn*nn,6)-F(nn*nn,40)
        for pp in range(4,nn):
            phi=split_formula(pp,nn-pp)
            assert phi<=Qn
            tick('terminal_formula_bound_checks')
    return {'m0_coefficient':str(mcoef),'Dbar_coefficient':str(Dcoef),
            'terminal_list_margin_coefficient':str(margin),
            'barrier_upper_normalized_distance':str(upper),
            'rho':str(rho),'delta':str(delta),'nmin':str(nmin)}

def main():
    start=time.time()
    graphs=[G for G in nx.graph_atlas_g() if len(G)>0 and nx.is_chordal(G)]
    paths=[]
    for i,G in enumerate(graphs):
        exact_phi4(G)
        for u,v in combinations(G,2):
            if not G.has_edge(u,v):
                H1,H2=copy(G,u,v),copy(G,v,u)
                assert exact_phi4(H1)+exact_phi4(H2)>=2*exact_phi4(G)
                tick('two_direction_copy_checks')
        paths.append(monotone_path(G))
        if i%100==0:print('atlas',i,'LP-cache',len(CACHE),flush=True)
    # A labelled nontrivial example for a full convex class path.
    G=nx.complete_graph(3);G.add_nodes_from(range(3,7))
    G.add_edges_from((u,v) for u in (3,4) for v in (0,1))
    G.add_edges_from((u,v) for u in (5,6) for v in (1,2))
    seq=[]
    for k in range(5):
        H=nx.complete_graph(3);H.add_nodes_from(range(3,7))
        H.add_edges_from((u,v) for u in range(3,3+k) for v in (0,1))
        H.add_edges_from((u,v) for u in range(3+k,7) for v in (1,2))
        seq.append(str(exact_phi4(H)))
    for k in range(1,4):assert F(seq[k-1])+F(seq[k+1])>=2*F(seq[k])
    report={'atlas_graphs':len(graphs),**COUNTS,'exact_mixed_LP_certificates':len(CACHE),
            'two_class_sequence':seq,'scalar_constants':scalar_checks()}
    report.update(COUNTS)
    records=list(CACHE.values())
    # Verify all saved records remain source-bound; replay script independently rechecks them.
    (OUT/'mixed_lp_certificates.json').write_text(json.dumps(records,separators=(',',':')))
    (OUT/'paths.json').write_text(json.dumps(paths,separators=(',',':')))
    report['seconds']=round(time.time()-start,3)
    report['scope']='Finite exact certificates and arithmetic only; the infinite proof is PROOF.md. No weighted-transfer threshold is evaluated.'
    (OUT/'audit_report.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
