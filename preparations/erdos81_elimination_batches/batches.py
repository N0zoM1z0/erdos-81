"""Exact, induced, host-colourable batch certificates for chordal graphs.

Dependencies: networkx. Arithmetic in objective calculations is exact.
The linear-time subtree scan assumes a supplied valid PEO; it does not
claim to optimize over every PEO or all vertex subsets.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
import networkx as nx


def peo_by_simplicial_deletion(G: nx.Graph):
    """Small-instance reference PEO finder; raises for nonchordal input."""
    live = set(G.nodes)
    order = []
    while live:
        options=[]
        for v in live:
            S = set(G[v]) & live
            if all(G.has_edge(x,y) for x,y in combinations(S,2)):
                options.append(v)
        if not options:
            raise ValueError('No simplicial vertex: the input is not chordal')
        v=min(options, key=lambda v:(len(set(G[v]) & live),str(v)))
        live.remove(v); order.append(v)
    return order


def validate_peo(G, order):
    if len(order)!=len(G) or set(order)!=set(G):
        raise ValueError('PEO is not a vertex permutation')
    pos={v:i for i,v in enumerate(order)}
    for v in order:
        later=[u for u in G[v] if pos[u]>pos[v]]
        if not all(G.has_edge(x,y) for x,y in combinations(later,2)):
            raise ValueError('Invalid PEO')
    return pos


def incident_graph(G,X):
    X=set(X)
    H=nx.Graph(); H.add_nodes_from(G)
    H.add_edges_from((u,v) for u,v in G.edges if u in X or v in X)
    return H


def incident_target(G,X):
    X=set(X)
    internal=G.subgraph(X).number_of_edges()
    cross=sum(v not in X for u in X for v in G[u])
    return cross-internal


def budget_margin(G,X,C=0):
    C=Fraction(C); s=len(X); n=len(G)
    return Fraction(s*(2*n-s),6)+C*s-incident_target(G,X)


def actual_lists(G,X,host_pool=None):
    X=set(X)
    pool=(set(G)-X) if host_pool is None else set(host_pool)
    if X & pool: raise ValueError('Hosts must be retained')
    return {tuple(sorted((u,v),key=str)): set(G[u]) & set(G[v]) & pool
            for u,v in G.subgraph(X).edges}


def exact_list_edge_colouring(lists):
    """Small-instance exhaustive MRV search, not a polynomial-time claim."""
    edges=list(lists)
    palettes={e:tuple(sorted(lists[e],key=str)) for e in edges}
    used={v:set() for e in edges for v in e}; colour={}
    def rec():
        if len(colour)==len(edges): return True
        best=None; opts=None
        for e in edges:
            if e in colour: continue
            z=[c for c in palettes[e] if c not in used[e[0]] and c not in used[e[1]]]
            if not z: return False
            if opts is None or len(z)<len(opts): best=e;opts=z
        u,v=best
        for c in opts:
            colour[best]=c;used[u].add(c);used[v].add(c)
            if rec():return True
            used[u].remove(c);used[v].remove(c);del colour[best]
        return False
    return dict(colour) if rec() else None


def incident_partition(G,X,colour):
    X=set(X); H=incident_graph(G,X)
    unused={frozenset(e) for e in H.edges}; parts=[]
    for (u,v),h in colour.items():
        if u not in X or v not in X or h in X:raise ValueError('Wrong edge/host role')
        Q=[u,v,h]; pairs=[frozenset(e) for e in combinations(Q,2)]
        if not all(e in unused for e in pairs):raise ValueError('Repeated or invalid triangle')
        parts.append(Q)
        for e in pairs: unused.remove(e)
    if set(map(frozenset,colour)) != {frozenset(e) for e in G.subgraph(X).edges}:
        raise ValueError('Not every internal edge is hosted')
    parts.extend([sorted(e,key=str) for e in sorted(unused,key=lambda e:tuple(sorted(map(str,e))))])
    check_partition(H,parts)
    if len(parts)!=incident_target(G,X):raise AssertionError('Cost identity failed')
    return parts


def check_partition(G,parts):
    edges={frozenset(e) for e in G.edges}; seen=set()
    for part in parts:
        if len(part)<2 or len(set(part))!=len(part):raise AssertionError('Invalid part')
        for e in combinations(part,2):
            e=frozenset(e)
            if e not in edges or e in seen:raise AssertionError('Invalid edge coverage')
            seen.add(e)
    if seen!=edges:raise AssertionError('Uncovered edges')
    return True


def cp_exact(G):
    """Exact full-clique recursion for small test graphs (all clique sizes)."""
    edges=list(G.edges); index={frozenset(e):i for i,e in enumerate(edges)}
    choices=[[] for _ in edges]
    for Q in nx.enumerate_all_cliques(G):
        if len(Q)<2:continue
        mask=sum(1<<index[frozenset(e)] for e in combinations(Q,2))
        for e in combinations(Q,2):choices[index[frozenset(e)]].append(mask)
    for row in choices: row.sort(key=int.bit_count,reverse=True)
    @lru_cache(None)
    def solve(mask):
        if mask==0:return 0
        bit=(mask&-mask).bit_length()-1
        return 1+min(solve(mask^c) for c in choices[bit] if c&mask==c)
    return solve((1<<len(edges))-1)


def elimination_data(G,order,validate=True):
    pos=validate_peo(G,order) if validate else {v:i for i,v in enumerate(order)}
    parent={};children={v:[] for v in G};forward={};backward={}
    for v in order:
        later=[u for u in G[v] if pos[u]>pos[v]]
        forward[v]=len(later);backward[v]=G.degree(v)-len(later)
        parent[v]=min(later,key=lambda u:pos[u]) if later else None
        if parent[v] is not None:children[parent[v]].append(v)
    size={v:1 for v in G};cost={v:forward[v]-2*backward[v] for v in G}
    for v in order:
        par=parent[v]
        if par is not None:
            size[par]+=size[v];cost[par]+=cost[v]
    return parent,children,forward,backward,size,cost


def descendants(children,v):
    ans=set();stack=[v]
    while stack:
        u=stack.pop();ans.add(u);stack.extend(children[u])
    return ans


def subtree_scan(G,order,C=0,validate=True):
    """O(n+m) after a valid PEO is supplied (excluding optional validation)."""
    data=elimination_data(G,order,validate)
    parent,children,forward,backward,size,cost=data
    delta=min(dict(G.degree()).values(),default=0)
    limit=max(1,(delta+1)//2)
    n=len(G);C=Fraction(C)
    eligible=[]
    for v in order:
        s=size[v]
        if s<=limit:
            margin=Fraction(s*(2*n-s),6)+C*s-cost[v]
            eligible.append({'root':v,'size':s,'cost':cost[v],'margin':margin})
    return data,limit,eligible


def score_encoding(G,domain,C=0):
    """Integer/rational QUBO: score = 6*budget_margin.
    This includes -2 interactions for nonedges; it is not a min-cut claim.
    """
    domain=list(domain); C=Fraction(C);n=len(G)
    linear={x:2*n+6*C-1-6*G.degree(x) for x in domain}
    pair={(x,y):(16 if G.has_edge(x,y) else -2) for x,y in combinations(domain,2)}
    return linear,pair


def exact_best_domain_batch(G,domain,C=0):
    """Exact exhaustive selector for a bounded domain; empty batch permitted."""
    domain=list(domain);linear,pairs=score_encoding(G,domain,C)
    best=Fraction(0);bestX=[]
    for mask in range(1<<len(domain)):
        X=[domain[i] for i in range(len(domain)) if mask>>i&1]
        score=sum((linear[x] for x in X),Fraction(0))
        score+=sum(pairs[(domain[i],domain[j])] for i in range(len(domain))
                   for j in range(i+1,len(domain)) if mask>>i&1 and mask>>j&1)
        if score!=6*budget_margin(G,X,C):raise AssertionError('QUBO mismatch')
        if score>best:best,bestX=score,X
    return best/6,bestX


def jacobian_weighted_encoding(G,domain,C=0):
    domain=list(domain);linear,pairs=score_encoding(G,domain,C)
    names={x:f'x{i:02}' for i,x in enumerate(domain)}
    # Force both anchors into every maximum by a positive dominating bonus.
    bonus=1+16*len(domain)*(len(domain)-1)//2+sum(abs(x) for x in linear.values())
    def rat(v):v=Fraction(v);return {'num':str(v.numerator),'den':str(v.denominator)}
    E=[{'endpoints':['anchor0','anchor1'],'weight':rat(bonus)}]
    E.extend({'endpoints':['anchor0',names[x]],'weight':rat(v)} for x,v in linear.items() if v)
    E.extend({'endpoints':[names[x],names[y]],'weight':rat(v)} for (x,y),v in pairs.items())
    return {'graph':{'vertices':['anchor0','anchor1']+[names[x] for x in domain],'edges':E}},bonus


def path_power_join(d,k):
    P=[f'p{i:03}' for i in range(d)];V=[f'v{i:03}' for i in range(2*d)]
    G=nx.Graph();G.add_nodes_from(P+V);G.add_edges_from(combinations(P,2))
    G.add_edges_from((x,v) for x in P for v in V)
    G.add_edges_from((V[i],V[j]) for i in range(2*d) for j in range(i+1,min(2*d,i+k+1)))
    return G,V+P,P,V


def repair_triangle_edge_partition(H0,parts,H1):
    """Restrict a triangle/K2 partition after edge edits; add new edges as K2s.

    The vertex set is fixed. No chordality of either incident graph is needed.
    Returns a partition with at most len(parts)+|E(H0) triangle E(H1)| parts.
    """
    if set(H0)!=set(H1):raise ValueError('Vertex set must be fixed')
    check_partition(H0,parts)
    if any(len(Q)>3 for Q in parts):raise ValueError('Bound requires K2/K3 base parts')
    E0={frozenset(e) for e in H0.edges};E1={frozenset(e) for e in H1.edges}
    answer=[]
    for Q in parts:
        surviving=[list(e) for e in combinations(Q,2) if frozenset(e) in E1]
        if len(Q)==3 and len(surviving)==3:answer.append(list(Q))
        else:answer.extend(surviving)
    answer.extend([sorted(e,key=str) for e in E1-E0])
    check_partition(H1,answer)
    assert len(answer)<=len(parts)+len(E0^E1)
    return answer


def conditional_mean_margin(G,chosen,undecided,remaining,total_size,C=0):
    chosen=set(chosen); undecided=set(undecided)
    t=len(undecided);k=remaining;C=Fraction(C)
    if not 0<=k<=t:raise ValueError('Invalid cardinality state')
    E=Fraction(G.subgraph(chosen).number_of_edges())
    D=Fraction(sum(G.degree(v) for v in chosen))
    if t:
        cross=sum(v in undecided for u in chosen for v in G[u])
        E+=Fraction(k*cross,t)
        D+=Fraction(k*sum(G.degree(v) for v in undecided),t)
    if t>=2:
        E+=Fraction(k*(k-1)*G.subgraph(undecided).number_of_edges(),t*(t-1))
    s=total_size;n=len(G)
    return Fraction(s*(2*n-s),6)+C*s-D+3*E


def conditional_mean_batch(G,domain,s,C=0):
    """Cardinality-preserving deterministic averaging, not exact maximization."""
    undecided=set(domain);chosen=set();k=s
    initial=conditional_mean_margin(G,chosen,undecided,k,s,C)
    while undecided:
        v=min(undecided,key=str);others=undecided-{v}
        vals=[]
        if k:
            vals.append((conditional_mean_margin(G,chosen|{v},others,k-1,s,C),True))
        if k<=len(others):
            vals.append((conditional_mean_margin(G,chosen,others,k,s,C),False))
        _,take=max(vals,key=lambda a:(a[0],a[1]))
        if take:chosen.add(v);k-=1
        undecided=others
    assert len(chosen)==s
    assert budget_margin(G,chosen,C)>=initial
    return initial,chosen
