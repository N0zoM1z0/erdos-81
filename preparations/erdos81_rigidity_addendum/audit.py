from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, random
import networkx as nx
from construct import construct, json_certificate, jacobian_partition, jacobian_dual

OUT=Path(__file__).resolve().parent
rng=random.Random(810907)
counts=Counter()
saved=[]

def audit_one(p,q,missing,outside,save=False,all_cliques=True):
    g4=construct(p,q,missing,outside,4)
    g3=construct(p,q,missing,outside,3)
    counts['graph_instances']+=1
    counts['partition_certificates']+=2
    counts['edge_incidences_replayed']+=2*len(g4['edges'])
    G=nx.Graph(); G.add_nodes_from(range(p+q)); G.add_edges_from(g4['edges'])
    counts['chordal_instances' if nx.is_chordal(G) else 'nonchordal_instances']+=1
    m=len(set(map(tuple,outside)))
    assert g3['value']-g4['value']==m
    deficit=(p+q)*(p+q+1)//6-g4['value']
    if 0 <= deficit <= 3:
        if m == 0:
            K=set(range(p))
        else:
            assert m==1 and len(g4['missing'])<=1
            u,v=next(iter(g4['outside']))
            host=next(y for y in (u,v) if all(G.has_edge(x,y) for x in range(p)))
            K=set(range(p))|{host}
        assert all(G.has_edge(x,y) for x,y in combinations(K,2))
        assert not any(G.has_edge(x,y) for x,y in combinations(set(G)-K,2))
        counts['deficit_at_most_three_split_certificates']+=1
    if all_cliques:
        for Q in nx.enumerate_all_cliques(G):
            if len(Q)<2: continue
            w4=sum(g4['dual_weights'][tuple(sorted(e))] for e in combinations(Q,2))
            assert w4 <= 1
            if w4==1:
                x=sum(v<p for v in Q); y=len(Q)-x
                assert (x,y) in {(1,1),(2,1),(2,2),(3,2)}
            if len(Q)<=3:
                assert sum(g3['dual_weights'][tuple(sorted(e))] for e in combinations(Q,2))<=1
            if len(Q) in (3,4):
                assert sum(1-g4['dual_weights'][tuple(sorted(e))] for e in combinations(Q,2))>=len(Q)*(len(Q)-1)//2-1
            counts['all_clique_dual_checks']+=1
    if save:
        saved.append(json_certificate(g4)); saved.append(json_certificate(g3))
    return g4,g3

# Exhaustive perturbations within the stated defect cap at p=2,3.
for p,q in [(2,4),(3,6)]:
    cross=[(x,y) for x in range(p) for y in range(p,p+q)]
    possible_out=list(combinations(range(p,p+q),2))
    budget=min(p,q-p)
    for m in range(budget//2+1):
        for out in combinations(possible_out,m):
            for a in range(budget-2*m+1):
                for missing in combinations(cross,a):
                    audit_one(p,q,missing,out)

# Random general perturbations, including nonchordal ones.
for i in range(300):
    p=rng.randrange(4,33); q=rng.randrange(p,3*p+1)
    budget=rng.randrange(min(p,q-p)+1)
    m=rng.randrange(budget//2+1); a=budget-2*m
    out=rng.sample(list(combinations(range(p,p+q),2)),m)
    missing=rng.sample([(x,y) for x in range(p) for y in range(p,p+q)],a)
    audit_one(p,q,missing,out,save=(i<20),all_cliques=(p<=6 and p+q<=22))

# Seed: one outside edge, one missing spoke, chordal.
seed4,seed3=audit_one(4,8,[(3,5)],[(4,5)],save=True)
assert seed4['value']==23 and seed3['value']==24
(OUT/'jacobian_partition_input.json').write_text(json.dumps(jacobian_partition(seed4),indent=2))
(OUT/'jacobian_dual_input.json').write_text(json.dumps(jacobian_dual(seed4),indent=2))
(OUT/'seed.json').write_text(json.dumps(json_certificate(seed4),indent=2))
# Explicit nonchordal seed: incomparable root neighborhoods at adjacent outsiders.
audit_one(4,8,[(2,4),(3,5)],[(4,5)],save=True)

# First nonsplit layer: two independent outside edges, all spokes present.
ns4,ns3=audit_one(4,8,[],[(4,5),(6,7)],save=True)
assert ns4['value']==22 and (12*13)//6-ns4['value']==4
assert nx.is_chordal(nx.Graph(ns4['edges']))
assert set(e for e in ns4['edges'] if e[0]>=4 and e[1]<8)=={(4,5),(6,7)}

# Clique-type inequalities and equality classification, using integers only.
for x in range(101):
    for y in range(101):
        if x+y<2: continue
        weight=x*y-x*(x-1)//2-y*(y-1)
        assert weight<=1
        assert (weight==1)==((x,y) in {(1,1),(2,1),(2,2),(3,2)})
        counts['clique_type_checks']+=1

# Finite scalar admission for every s<=n/100 in the range checked.
# These are exact checks, not a replacement for the all-n proof.
for n in range(100,3001):
    M=n*(n+1)//6
    for s in range(n//100+1):
        k=n//3
        for p in range(max(1,k-10),min(n,k+11)):
            B=p*(n-p)-p*(p-1)//2
            ell=M-B
            if 0<=ell<=s:
                assert F(n,4)<=p<=F(3*n,8)
                assert 18*s<=min(p,n-2*p)
                assert n-1-2*s>F(n,2)
                assert p+9*s<F(n,2)
                # finite deficit decomposition, all old strict feasible (m,a)
                # extrema are enough for linear T = a+2m: <=18(s-ell).
                assert 18*(s-ell)<=min(p,n-2*p)
                counts['near_window_scalar_cases']+=1

# Residue formula and extremal roots, independently of approximate square roots.
for n in range(3,5001):
    k,r=divmod(n,3); M=n*(n+1)//6
    roots=[]
    for j in range(-10,11):
        p=k+j
        if not (0<=p<=n): continue
        ell=M-(p*(n-p)-p*(p-1)//2)
        target=[j*(3*j-1)//2,3*j*(j-1)//2,(j-1)*(3*j-2)//2][r]
        assert ell==target
        if ell==0: roots.append(p)
        counts['root_displacement_checks']+=1
    assert roots==([k] if r==0 else [k,k+1] if r==1 else [k+1])

# Sharp edit examples and outside-edge-price examples.
for p in [10,20,40,64]:
    q=2*p
    for a in [0,1,min(5,p)]:
        missing=[(0,p+i) for i in range(a)]
        g4,g3=audit_one(p,q,missing,[],save=True,all_cliques=False)
        assert (p+q)*(p+q+1)//6-g4['value']==a
    for m in [1,2,min(5,p//2)]:
        outside=[(p+2*i,p+2*i+1) for i in range(m)]
        g4,g3=audit_one(p,q,[],outside,save=True,all_cliques=False)
        assert (p+q)*(p+q+1)//6-g4['value']==2*m

(OUT/'partition_certificates.json').write_text(json.dumps(saved,separators=(',',':')))
counts['saved_partition_certificates']=len(saved)
report={'verdict':'PASS','counts':dict(counts),
        'seed':{'vertices':12,'edges':len(seed4['edges']),'cp':seed4['value'],'cp_at_most_3':seed3['value'],
                'parts_by_size':dict(Counter(map(len,seed4['parts'])))} ,
        'limits':['The asymptotic closure theorem is a supplied session proof, not inferred from these finite checks.',
                  'Large clique-type inequalities are checked algebraically; exhaustive clique enumeration is only performed on the stated small instances.',
                  'The root-window scalar checks run only through n=3000; the proof handles all n.']}
(OUT/'audit_report.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
