from batches import *
from fractions import Fraction
from itertools import combinations
import json,random,time
from pathlib import Path
ROOT=Path(__file__).parent
rng=random.Random(810909)
report={'scope':'Current-run checks only; no asymptotic extrapolation.'}
counts={'chordal_graphs':0,'subtree_checks':0,'prefix_subset_hostings':0,'exact_incident_optima':0,'ideal_union_checks':0,'rich_layer_hostings':0,'prefix_scores':0,'conditional_mean_selections':0}
start=time.time()
for G in nx.graph_atlas_g():
    if not G or not nx.is_chordal(G):continue
    counts['chordal_graphs']+=1
    order=peo_by_simplicial_deletion(G);pos=validate_peo(G,order)
    data,limit,eligible=subtree_scan(G,order,Fraction(0))
    parent,children,a,b,size,cost=data
    subs={v:descendants(children,v) for v in G}
    for v,X in subs.items():
        counts['subtree_checks']+=1
        assert nx.is_connected(G.subgraph(X))
        assert size[v]==len(X)
        assert G.subgraph(X).number_of_edges()==sum(b[u] for u in X)
        assert cost[v]==incident_target(G,X)
        boundary=set.union(*(set(G[u])-X for u in X)) if X else set()
        assert boundary=={u for u in G[v] if pos[u]>pos[v]}
        if len(X)<=limit:
            L=actual_lists(G,X)
            assert all(len(z)>=len(X) for z in L.values()) or not L
    # All descendant-closed ideals; components are full subtrees.
    if len(G)<=7:
        for mask in range(1<<len(G)):
            X={i for i in G if mask>>i&1}
            if not all(subs[v]<=X for v in X):continue
            roots=[v for v in X if parent[v] not in X]
            assert set().union(*(subs[v] for v in roots))==X
            if all(len(subs[v])<=limit for v in roots):
                counts['ideal_union_checks']+=1
                unionmargin=budget_margin(G,X)
                summed=sum((budget_margin(G,subs[v]) for v in roots),Fraction(0))
                correction=sum(len(subs[u])*len(subs[v]) for u,v in combinations(roots,2))
                assert unionmargin==summed-Fraction(correction,3)
                if X and unionmargin>=0:
                    assert any(budget_margin(G,subs[v])>=0 for v in roots)
    # Every subset of a short PEO prefix is hostable from its untouched suffix.
    m=limit;W=order[:m];Y=set(G)-set(W)
    for mask in range(1,1<<len(W)):
        X={W[i] for i in range(len(W)) if mask>>i&1}
        L=actual_lists(G,X,Y)
        assert all(len(z)>=m for z in L.values()) or not L
        col=exact_list_edge_colouring(L);assert col is not None
        parts=incident_partition(G,X,col);counts['prefix_subset_hostings']+=1
        if len(G)<=6:
            opt=cp_exact(incident_graph(G,X))
            assert opt==len(parts);counts['exact_incident_optima']+=1
    # Forward-degree-rich layers.
    for s in range(2,min(4,len(G))+1):
        layer=[v for v in order if a[v]>=2*s-1]
        if len(layer)>=s:
            initial,selected=conditional_mean_batch(G,layer,s,Fraction(1,6))
            exact_average=sum((budget_margin(G,Y,Fraction(1,6)) for Y in combinations(layer,s)),Fraction(0))/__import__('math').comb(len(layer),s)
            assert initial==exact_average
            assert budget_margin(G,selected,Fraction(1,6))>=initial
            counts['conditional_mean_selections']+=1
        for Xtuple in list(combinations(layer,s))[:8]:
            X=set(Xtuple);L=actual_lists(G,X)
            assert all(len(z)>=s for z in L.values())
            col=exact_list_edge_colouring(L);assert col is not None
            incident_partition(G,X,col);counts['rich_layer_hostings']+=1
    for s in range(1,len(order)+1):
        X=set(order[:s]);internal=G.subgraph(X).number_of_edges()
        target=sum(a[x] for x in X)-2*internal
        assert target==incident_target(G,X);counts['prefix_scores']+=1
report['atlas']=counts
# A 144-vertex user-regression instance. Exact scalar optimization on a 12-vertex window.
G,order,P,V=path_power_join(48,6)
X=set(V[:12]);C=Fraction(0)
assert validate_peo(G,order)
margin,best=exact_best_domain_batch(G,V[:12],C)
assert margin==6 and set(best)==X
payload,bonus=jacobian_weighted_encoding(G,V[:12],C)
(ROOT/'jacobian_margin_request.json').write_text(json.dumps(payload,indent=2))
max_clique_margin=None;clique_params=None
w=48+6+1
for aa in range(w//2+1):
 for bb in range(8):
  s=aa+bb
  if not(1<=s<=w//2):continue
  degree_sum=aa*(144-1)+bb*(48+6)+bb*(bb-1)//2
  c=degree_sum-3*s*(s-1)//2
  val=Fraction(s*(288-s),6)-c
  if max_clique_margin is None or val>max_clique_margin:
   max_clique_margin=val;clique_params=[aa,bb]
assert max_clique_margin==Fraction(-37,6)
# Explicit incident partition: greedy colours use the retained universal clique.
L=actual_lists(G,X,P); col=exact_list_edge_colouring(L); parts=incident_partition(G,X,col)
assert len(parts)==546
whole=parts+[P]
# This is not a whole partition: retained outside edges are not covered. Record incident only.
seed={'graph':{'vertices':list(G),'edges':[sorted(e) for e in incident_graph(G,X).edges]},'parts':parts}
(ROOT/'large_incident_witness.json').write_text(json.dumps(seed))
report['window_regression']={'n':144,'d':48,'k':6,'window':12,'best_margin':str(margin),'incident_parts':len(parts),'allowance':str(Fraction(12*(288-12),6)),'best_small_clique_margin':str(max_clique_margin),'best_clique_counts':clique_params,'forced_anchor_bonus':str(bonus),'expected_jacobian_max':str(bonus+36)}
# Small nonuniform list seed with no common palette for the connected 3-vertex batch.
P=[f'r{i}' for i in range(8)];X=['a','b','c'];G=nx.Graph();G.add_nodes_from(X+P)
G.add_edges_from(combinations(P,2));G.add_edges_from([('a','b'),('b','c')])
G.add_edges_from(('a',x) for x in P[:4]);G.add_edges_from(('c',x) for x in P[4:]);G.add_edges_from(('b',x) for x in P)
order=['a','c','b']+P;validate_peo(G,order)
assert min(dict(G.degree()).values())==5
assert not(set(G['a'])&set(G['b'])&set(G['c'])&set(P))
L=actual_lists(G,X,P);col=exact_list_edge_colouring(L);parts=incident_partition(G,X,col)
assert len(parts)==14
request={'graph':{'vertices':list(G),'edges':[sorted(e) for e in incident_graph(G,X).edges]},'parts':parts}
(ROOT/'jacobian_partition_request.json').write_text(json.dumps(request,indent=2))
report['nonuniform_seed']={'vertices':len(G),'minimum_degree':5,'batch_order':3,'common_palette':0,'internal_edges':2,'incident_edges':18,'incident_parts':14,'C':2,'budget_margin':str(budget_margin(G,X,2))}
# Exact robust-prefix inequalities over a broad integer grid.
numerical_checks=0
for k in range(1,101):
 for C in (Fraction(0),Fraction(1,6),Fraction(1),Fraction(3)):
  for s in range(k+1,6*k+1):
   for defect in (0,k,k*k//8):
    e= k*s-k*(k+1)//2-defect
    c=s*(1000+k)-2*e
    marg=Fraction(s*(6000-s),6)+C*s-c
    formula=(k+C)*s-Fraction(s*s,6)-k*(k+1)-2*defect
    assert marg==formula;numerical_checks+=1
report['robust_prefix_identity_checks']=numerical_checks
# Edge-edit stability of an already hosted incident certificate.
H0=incident_graph(G,X)
base_parts=parts
possible=[(u,v) for u,v in combinations(list(G),2) if u in X or v in X]
for trial in range(1000):
    H1=H0.copy()
    for u,v in rng.sample(possible,rng.randrange(1,min(12,len(possible))+1)):
        if H1.has_edge(u,v):H1.remove_edge(u,v)
        else:H1.add_edge(u,v)
    repaired=repair_triangle_edge_partition(H0,base_parts,H1)
report['edge_edit_repairs']=1000
report['runtime_seconds']=round(time.time()-start,3)
(ROOT/'audit_report.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
