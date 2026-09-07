# A local-to-global stability proof for chordal clique partitions

## Status and theorem

This is a new proof assembled in this research session. It has not received independent mathematical peer review or formal verification. The accompanying finite computations check the discrete copy mechanism, exact mixed-packing LP certificates, and the rational constants; they do not verify an infinite theorem by enumeration.

Subject to the three standard external results stated below, the argument proves the following.

**Theorem.** There is an integer N such that, for every chordal graph G of order n >= N,

    cp_{<=4}(G) <= floor(n(n+1)/6).

In particular, with the single absolute constant C=N, every finite chordal graph satisfies

    cp(G) <= n^2/6 + C n.

The constant is specified independently of the desired chordal assertion. Put

    rho = 10^(-12),   delta = 10^(-30).

Let T(epsilon) be the least positive integer for which the fixed weighted-packing transfer theorem below holds for every graph on at least T(epsilon) vertices. Set

    N = max{10^32, T(delta/2)},    C=N.

The external theorem proves this is a finite absolute integer. No numerical evaluation of T(delta/2) is claimed.

In fact, the upper bound for n >= N is attained by a suitable complete-split graph, so the eventual maximum is exactly floor(n(n+1)/6).

## External inputs

1. Vizing: every finite simple graph of maximum degree Delta has a proper edge-colouring with at most Delta+1 colours. A primary modern source restating this theorem is Assadi et al., *Vizing's Theorem in Near-Linear Time*, arXiv:2410.05240 (abstract).
2. Haggkvist--Janssen: the list-chromatic index of K_p is at most p. Source: *New Bounds on the List-Chromatic Index of the Complete Graph and Other Simple Graphs*, Combinatorics, Probability and Computing 6 (1997), 295--313, DOI 10.1017/S0963548397002927.
3. Weighted finite-family packing transfer: with gains 2 for triangles and 5 for K4s, let W4*(G) and W4(G) be the maximum fractional and integral edge-disjoint packing gains. For every epsilon>0 there is T(epsilon) such that

       0 <= W4*(G)-W4(G) <= epsilon |V(G)|^2

   whenever |V(G)| >= T(epsilon), uniformly over all graphs. Source: Rohatgi--Urschel--Wellens, *Regarding two conjectures on clique and biclique partitions*, arXiv:2005.02529, Theorem 3.4 with r=4. The uniform quantifier is also made explicit in its application in the proof of Theorem 3.6.

We also use standard elementary characterizations of chordal graphs: induced subgraphs are chordal, chordal graphs admit PEOs and clique trees, adding a simplicial vertex preserves chordality, and a noncomplete chordal graph has two nonadjacent simplicial vertices. The copy and terminal arguments needed here are proved below; no unproved stability statement is assumed.

No Delcourt--Postle decomposition theorem, unrestricted O(n) fractional clique-partition rounding, or generic symmetrization-stability theorem is used.

## 1. Notation and the mixed functional

All graphs are finite and simple. Clique partitions partition the edge set, and K2 parts are permitted. cp_{<=r} denotes the minimum number of parts of orders at most r.

Define

    Phi(G) = e(G)-W4*(G),
    Q(n) = (2n+1)^2/24,
    M(n) = floor(Q(n)) = floor(n(n+1)/6).

The identity for the two floors follows because n(n+1)/6 has fractional part either 0 or 1/3.

The dual for W4* is the minimum of sum_e y_e over nonnegative edge weights satisfying

    sum_{e in T} y_e >= 2   for every triangle T,
    sum_{e in K} y_e >= 5   for every K4 K.

The primal/dual optimum is attained. For instance, a dual value above 5 can be reduced to 5, so the minimization may be performed in a compact box.

Starting with all edges as K2s shows exactly

    cp_{<=4}(G) = e(G)-W4(G)
                 = Phi(G) + W4*(G)-W4(G).

For every G, Phi(G) <= cp_{<=3}(G): an integral triangle packing is also an admissible mixed fractional packing.

For a clique P in a chordal graph G, write

    p=|P|, H=G-P, q=|H|,
    m=e(H), w=omega(H),
    M=pq-e(P,H),
    D=max_{x in P} |V(H)\N_G(x)|.

A PEO can be chosen to end with any specified clique P. Repeatedly remove a simplicial vertex outside P: in a noncomplete chordal graph the two nonadjacent simplicial vertices cannot both be in P; in a complete graph any outside vertex may be removed.

## 2. An integral terminal construction retaining quantitative defect savings

**Lemma 2.1.** Let c=max{p,Delta(H)+1}, t=ceil(m/c). If

    q-2D-4t >= p,

then

    cp_{<=3}(G)
      <= pq-binom(p,2)
         + (1-2p/c)m - (1-2(w-1)/p)M.                (2.1)

This lemma does not require P to be maximum.

**Proof.** Properly edge-colour H with c colours by Vizing. Among all such colourings minimize the sum of the squares of class sizes. If two classes differ by at least two, their union contains an alternating path with one more edge of the larger class; swapping that path decreases the sum of squares. Thus all classes have at most ceil(m/c)=t edges.

Retain the p largest classes. They contain at least pm/c edges. Assign them bijectively to P and retain each edge whose assigned root vertex is a common neighbour of its endpoints.

Choose a PEO ending in P. For an outside edge uv with u earlier, all later neighbours of u form a clique, so

    N(u) intersect P subset N(v) intersect P.

If a_u=p-|N(u) intersect P|, the exact number of root hosts invalid for this edge is a_u. Each u has at most w-1 later neighbours in H. Hence the total invalid-host count on all outside edges, and therefore on the selected edges, is at most (w-1)M.

A uniform bijection of selected classes to P consequently has expected invalid count at most (w-1)M/p. Some bijection retains f edges with

    f >= pm/c - (w-1)M/p.

Use these f outside-edge triangles. Each root vertex has at most 2t used outside spokes. A root edge has at least q-2D-4t unused common outside hosts, by taking the union of the two missing-host sets and the two used-spoke sets. This is at least p. Haggkvist--Janssen properly list-edge-colours K_p from these actual lists, yielding edge-disjoint root triangles disjoint from the outside triangles.

Use K2s for all remaining outside and crossing edges. The exact count is

    pq-binom(p,2)+m-M-2f.

Substitution proves (2.1). All root edges have been explicitly completed. There is no induction on a damaged separator. QED.

A useful consequence is that if additionally

    c <= 9p/5,      2(w-1)/p <= 1/2,

then

    cp_{<=3}(G) <= pq-binom(p,2)-m/9-M/2.            (2.2)

## 3. Strict root regularization

**Lemma 3.1 (nonadjacency).** If u is outside P and misses x in P, then

    d_H(u) <= D+w-2.

Indeed, common neighbours of nonadjacent vertices in a chordal graph form a clique: two nonadjacent common neighbours would form an induced C4. Thus N_H(u) intersect N_H(x), together with u, is a clique in H, giving at most w-1 common neighbours. Other neighbours of u belong to H\N(x), which has at most D vertices and contains u itself. There are at most D-1 such neighbours. QED.

**Lemma 3.2 (strict regularization).** Suppose G contains a clique P satisfying

    p>=128,
    |q-2p| <= p/64,
    m+M <= p^2/65536.                               (3.1)

Then G has a clique P' (not necessarily maximum), with outside data p',q',m',M', such that

    cp_{<=3}(G) <= p'q'-binom(p',2)-m'/9-M'/2.       (3.2)

**Proof.** Move to the outside every root vertex whose original missing column exceeds p/64. Let r be the number moved, and let P0 be the retained root. This is only a change of the root designation; the graph is not edited and no parts are committed.

    r <= 64M/p <= p/1024,
    p0=p-r >= 99p/100,
    q0=q+r,
    D0<=p/64.

The newly outside edge count is exactly

    m0 = m + e(R,H) + binom(r,2).

In particular,

    m0 <= [1/65536 + 129/(64*1024) + 1/(2*1024^2)]p^2
        = (4161/2097152)p^2 < p^2/400.               (3.3)

Thus w0-1 <= sqrt(2m0)<p/10.

Define

    Dbar = max{D0, q0-7p0/4}.

Then

    Dbar <= max{p/64, (17/64+11/4096)p}
         = (1099/4096)p < p/3.                      (3.4)

While the current outside graph has a vertex of degree at least 7/4 times the current root order, add it to the root.

Every such addition is legal. By Lemma 3.1, a vertex not complete to the current root has outside degree at most Dbar+w0-2 < 13p/30, far below 7p0/4. The current root therefore remains a clique.

If u is promoted from a current outside graph of order q_i with root order p_i, its new missing-column size is

    q_i-1-d_{H_i}(u) <= q_i-7p_i/4-1
                     <= q0-7p0/4 <= Dbar.

Old root-column deficits and outside clique number cannot increase. Hence Dbar remains valid.

Each promotion removes at least 7p0/4 current outside edges, and these edges are counted only once. If h vertices are promoted,

    h <= 4m0/(7p0) <= p/693.                        (3.5)

At termination Delta(H') < 7p'/4, so

    c'=max{p',Delta(H')+1} <= ceil(7p'/4) <= 9p'/5.

The last inequality holds for every integer p'>=15, and p'>=p0>=127. Also

    2(w'-1)/p' < 20/99 < 1/2.

Put t'=ceil(m'/c'). Since c'>=p0,

    t' <= ceil(m0/p0) <= p/396+1.

Finally,

    q'-p'-2D'-4t'
      >= [63/64-2/693-2/3-1/99]p-4
       = (4505/14784)p-4
       > p/4-4 >= 0.                               (3.6)

Apply (2.2). QED.

The change from promotion threshold 2p to 7p/4 is essential. The former permits a zero coefficient on m in (2.1); the latter retains a fixed negative coefficient. Every displaced root edge has been included in m0.

## 4. Local stability in actual edit distance

Let a=floor(n/3). For A subset V(G) with |A|=a, let S_A be the complete-split graph whose clique side is A and whose independent side is V(G)\A. Define

    d_split(G) = min_{|A|=a} |E(G) symmetric_difference E(S_A)|.

One single-vertex copying operation changes at most n-2 unordered pairs. Therefore d_split changes by at most n-2 under that operation.

Fix rho=10^-12.

**Lemma 4.1 (entry to strict regularization).** If G is chordal, n>=1000, and

    d_split(G) <= rho n^2,

then G has a clique P satisfying (3.1).

**Proof.** Choose the corresponding template clique A, with edit count E<=rho n^2. Let P be a maximum clique of the induced chordal graph G[A], and write u=|A|-p.

A chordal graph on a vertices and clique number p has at most

    (p-1)a-binom(p,2)

edges, by summing min{p-1,a-i} along a PEO. It therefore has at least binom(u+1,2) missing pairs. Thus u<=sqrt(2E).

For n>=1000,

    p >= n/3-1-sqrt(2rho)n >= 33n/100 >=128,
    p <= n/3,
    0 <= q-2p=n-3p <=3+3sqrt(2rho)n <=p/64.

The old independent-side edges and the old cross nonedges contribute at most E defects altogether. All newly relevant pairs involving A\P contribute at most un. Consequently,

    m+M <= E+un <= (rho+sqrt(2rho))n^2
         <= (10^-12+3/(2*10^6))n^2
         < (33/100)^2 n^2/65536 <=p^2/65536.

QED.

**Lemma 4.2 (quantitative local stability).** Under the hypotheses of Lemma 4.1, let

    Delta = Q(n)-Phi(G).

Then Delta>=0 and

    d_split(G) <= 9Delta+n sqrt(2Delta/3)+n.          (4.1)

Moreover, cp_{<=3}(G)<=M(n).

**Proof.** Use P' from Lemma 3.2. Since Phi(G)<=cp_{<=3}(G),

    Delta >= Q(n)-[p'q'-binom(p',2)]+m'/9+M'/2.

The exact square identity is

    Q(n)-[p'(n-p')-binom(p',2)]
      = (6p'-2n-1)^2/24.

Hence

    m'+M' <= 9Delta,
    |p'-(2n+1)/6| <= sqrt(2Delta/3).

G differs from the complete-split graph with clique P' on exactly m'+M' pairs. Change its clique side to order floor(n/3), adding or removing |p'-floor(n/3)| vertices. This changes at most n|p'-floor(n/3)| edges. Since |(2n+1)/6-floor(n/3)|<1, (4.1) follows.

Finally (3.2) gives cp_{<=3}(G)<=Q(n); the left side is integral, so it is at most M(n). QED.

This is an actual local stability inequality, not merely the observation that near-template graphs have small clique partition number. It quantitatively excludes near-extremal graphs at the boundary of a fixed template neighborhood.

## 5. A monotone path of single-vertex copies

For nonadjacent vertices u,v, let G_{u->v} be obtained by replacing N(u) by N(v), leaving u and v nonadjacent.

**Lemma 5.1 (copy inequality).** For every graph G and every nonadjacent pair,

    Phi(G_{u->v})+Phi(G_{v->u}) >=2Phi(G).           (5.1)

**Proof.** Choose an optimal mixed edge-cover y for G. In G_{u->v}, leave unaffected edge weights fixed and give new ux the old weight on vx. A triangle or K4 containing u maps to one containing v in G. No clique contains both u and v. Hence every dual constraint is preserved.

If t_u and t_v are the sums of y-weights incident with u and v, the copied cover has total W4*(G)-t_u+t_v. The opposite copied cover has total W4*(G)-t_v+t_u. Their totals sum to 2W4*(G). The two copied edge counts also sum to 2e(G). Subtracting proves (5.1). QED.

Call vertices with the same open neighbourhood false twins. Their classes are independent. Select two distinct, mutually nonadjacent false-twin classes A,B consisting of simplicial vertices. Their neighbourhoods lie outside A union B and are cliques.

Keep the graph outside A union B fixed, and let H_j have j of these vertices with neighbourhood N(A) and the rest with neighbourhood N(B). All H_j are chordal, since the two fixed neighbourhoods are cliques. By (5.1),

    Phi(H_{j-1})+Phi(H_{j+1}) >=2Phi(H_j).

Thus j -> Phi(H_j) is discretely convex. At the current interior index, at least one adjacent value is no smaller. Choose that direction. Successive differences in that direction stay nonnegative, so continue monotonically all the way to its endpoint. This performs a full-class merge through single-vertex copies, with Phi never decreasing at any intermediate graph.

No old false-twin class outside A union B splits: all its vertices have the same adjacency to the target representative, hence acquire the same adjacency to each copied vertex. The remaining source vertices stay twins, and target vertices remain twins with the added copies. At the endpoint the number of false-twin classes strictly decreases.

**Lemma 5.2 (terminal characterization).** If every pair of nonadjacent simplicial vertices in a chordal graph has the same open neighbourhood, then the graph is complete-split.

**Proof.** If the graph is disconnected and has an edge, choose a nonisolated simplicial vertex in a nontrivial component and a simplicial vertex in a different component. Their neighbourhoods are disjoint and at least one is nonempty, contradicting the hypothesis. Thus a disconnected terminal graph is edgeless. Complete graphs are already complete-split.

In the remaining connected, noncomplete case, use a clique tree with at least two maximal-clique bags. A vertex private to a leaf bag is simplicial and belongs only to that bag. Private vertices at distinct leaves are nonadjacent. They all have the same open neighbourhood K by hypothesis.

Each leaf has exactly one private vertex. Otherwise another private vertex in the same leaf belongs to the first one's neighbourhood but not to the neighbourhood of a private vertex at a different leaf. Every leaf bag is consequently K plus one private vertex.

Every member of K occurs in every leaf bag, and the running-intersection property implies it occurs in every bag, since every tree node lies on a path between leaves. Thus K is universal to the rest of the graph. Every leaf-private vertex is isolated in G-K. If G-K had a nontrivial component, choose a nonisolated simplicial vertex of that chordal component. It is also simplicial in G and nonadjacent to a leaf-private vertex, but its neighbourhood is strictly larger than K, a contradiction. Hence G-K is independent. QED.

**Proposition 5.3 (fine monotone symmetrization).** Every chordal graph G admits a sequence

    G=G_0,G_1,...,G_L=S_{k,n-k}

of chordal graphs such that Phi is nondecreasing and consecutive graphs differ on at most n-2 edges. One may take L<=n(n-1).

Proof: execute the full-class monotone runs above until no pair is available. There are at most n-1 runs, each at most n moves. Lemma 5.2 identifies the terminal graph. QED.

The point of this proposition is NOT merely monotonicity at full-class endpoints. Every intermediate one-vertex move is monotone. This permits a fixed edit-distance boundary argument.

## 6. Complete-split terminals: the competing branches are separated

For S_{k,l}, k>=4 and l>=1, average its mixed-cover dual over automorphisms. If x is the root-edge weight and y the spoke weight, the constraints are

    x>=5/6, y>=0, x+2y>=2, x+y>=5/3.

The relevant vertices are (2,0), (4/3,1/3), (5/6,5/6). Thus, with n=k+l,

    Phi(S_{k,l}) = max{
      kl-binom(k,2),
      (2kl-binom(k,2))/3,
      [kl+binom(k,2)]/6
    }.                                             (6.1)

The three global upper bounds are respectively

    Q(n),        (4n+1)^2/120,       n(n-1)/12.

For l=0 and k>=4, the value is e(K_n)/6, witnessed by uniformly packing K4s and the constant dual 5/6. For k<=3, Phi<=e<=3n. These cover the degenerate cases needed below.

For n>=100, every branch other than the first in (6.1), including these degeneracies, is strictly less than

    n^2/6 - n^2/40.

For the second branch this is equivalent to n^2>8n+1; for 3n it follows from 17n>360. The complete-graph branch is smaller still.

It follows in particular from Proposition 5.3 that Phi(G)<=Q(n) for all chordal G of order at least 100.

More importantly, if a terminal S satisfies

    Phi(S) >= n^2/6-delta n^2,       delta=10^-30,

then its first branch is its value. Setting Delta=Q(n)-Phi(S), the same square identity gives

    d_split(S) <= n sqrt(2Delta/3)+n.                (6.2)

Here the template root is allowed to have a different order; changing at most |k-floor(n/3)| vertex roles costs at most n per role. No assertion about preservation of the original graph's clique number is made.

## 7. Global stability by the first-entry argument

**Theorem 7.1 (fixed-neighborhood stability).** For n>=10^32 and chordal G,

    Phi(G) >= n^2/6-10^-30 n^2

implies

    d_split(G) < (10^-12/2)n^2.                     (7.1)

**Proof.** Let rho=10^-12 and delta=10^-30. Take the fine monotone path from Proposition 5.3. Every graph on it has Phi at least the starting value. Hence for each path graph H,

    Q(n)-Phi(H) <= delta n^2+n/6+1/24 <=2delta n^2,

where n>=10^32.

The terminal graph is within rho n^2/4 of the balanced complete-split family by (6.2).

Suppose the starting graph has distance at least rho n^2/2. Choose the first path index i whose distance is below rho n^2/2. The preceding graph has distance at least rho n^2/2, and the move changes at most n-2 pairs. Thus

    rho n^2/2-n <= d_split(G_i) < rho n^2/2.

In particular G_i lies inside the local rho n^2 neighborhood, so Lemma 4.2 applies. It gives

    d_split(G_i)/n^2
       <=18delta+sqrt(4delta/3)+1/n
       <18*10^-30+2*10^-15+10^-32
       <rho/4.

But rho/2-1/n>rho/4, a contradiction. Therefore (7.1) holds. QED.

This is the missing structural implication. It uses local stability quantitatively and uses single-vertex monotonicity to ensure a path cannot enter the local ball from its boundary while remaining near-extremal. It does not infer global stability merely from uniqueness of the terminal maximizer.

## 8. Complete the clique-partition proof

Let

    N=max{10^32,T(10^-30/2)}.

Take any chordal G on n>=N vertices.

If Phi(G)>=n^2/6-10^-30 n^2, Theorem 7.1 places it inside the fixed local neighborhood. Lemma 4.2 gives

    cp_{<=3}(G)<=M(n).

Otherwise, the weighted finite-family transfer gives

    cp_{<=4}(G)
      =Phi(G)+W4*(G)-W4(G)
      <n^2/6-10^-30 n^2+(10^-30/2)n^2
      <n^2/6<=M(n).

Thus in either case

    cp(G)<=cp_{<=4}(G)<=M(n).

For 0<n<N, use K2s:

    cp(G)<=binom(n,2)<=n^2/6+Nn.

For n=0 the assertion is 0<=0. Since M(n)<=n^2/6+n/6 and N>=1, the same constant C=N handles the large orders too. This proves the theorem for every n.

## 9. Eventual sharpness

For a complete-split graph with core size k and outside size n-k, provided n-k>=chi'(K_k), factorizing the core and assigning factors to distinct outside vertices gives

    cp(S_{k,n-k})=k(n-k)-binom(k,2).

The lower bound uses weights -1 on core edges and +1 on spokes: every clique has weight at most one. Choose k nearest to (2n+1)/6. The maximum equals M(n), by checking n modulo 3, and the host condition holds for every sufficiently large n (indeed for the elementary small choices too).

Therefore max_{G chordal, |V|=n} cp(G)=M(n) for every n>=N.

## 10. Dependency and limitation ledger

* The proof does not assume that copying preserves clique number. It works with labelled edit distance, not the original clique size.
* All numerical root changes are included in m0. No rp or r^2 error is silently discarded.
* The strict penalty in Lemma 3.2 is essential. A non-strict local upper bound would not support the boundary argument.
* There is no universal O(n) bound on cp-cp_f, nor on W4*-W4. The weighted transfer is used only outside a fixed neighborhood, where a fixed quadratic gap pays for it.
* Inside that neighborhood there is an actual triangle/K2 partition, not a qualitative edit repair priced at the number of edits.
* No costs are summed over overlapping clique-tree bags. The clique tree is used only to identify terminal graphs.
* Larger root parts are not needed in this proof. Far from the template, the weighted transfer supplies triangles and K4s; near it, triangles and edges suffice.
* The exact value of the enormous absolute threshold T(10^-30/2) is not computed. It is provided by an independently stated uniform theorem, not defined in terms of the conjecture being proved.

## 11. Computational audit

`audit.py` checks 531 nonempty chordal atlas graphs through order seven. It verifies 5,394 two-direction mixed-cover copy inequalities and constructs 531 monotone single-copy paths, comprising 1,224 full-class rounds and 1,889 single-vertex moves. Every intermediate path graph is checked chordal, and every endpoint is checked complete-split.

Across these tests there are 7,964 source-bound mixed-packing LP certificates. SciPy finds candidates; all packing loads, all triangle and K4 dual constraints, and all primal/dual objective equalities are then replayed with exact Fractions.

The separate dependency-free `replay.py` checks all 7,964 certificates and all 1,889 path steps. It checks 36,743 dual constraints and 14,134 positive packing entries. Its output is `PASS`.

The audit also checks the rational all-parameter inequalities used in root regularization and the first-entry argument, 19,986 integer colour-count bounds, and 711,246 complete-split terminal comparisons.

One nontrivial two-class sequence has Phi values

    9, 7, 7, 7, 9.

This illustrates why an arbitrary direction may decrease the functional, and why choosing a nondecreasing adjacent direction before moving to the endpoint is necessary.

Jacobian independently returned an exact mixed-cover optimum of 380 for S_{20,40}: root weight 2, spoke weight 0; objective coefficients 190 and 800; triangle/K4 dual constraints verified. Thus Phi(S_{20,40})=990-380=610=M(60).

A 12-vertex terminal construction is supplied as a separate partition input and independently checked by the local edge-counter. The attempted Jacobian partition checker calls returned network errors in this run, so no successful Jacobian verification is claimed for that partition.

The finite audits are regression and arithmetic checks. They do not constitute independent peer review of the general proof, and do not evaluate the asymptotic transfer threshold.

## References

* Haggkvist, R.; Janssen, J. (1997). New Bounds on the List-Chromatic Index of the Complete Graph and Other Simple Graphs. DOI: 10.1017/S0963548397002927.
* Rohatgi, D.; Urschel, J. C.; Wellens, J. Regarding two conjectures on clique and biclique partitions. arXiv:2005.02529, Theorem 3.4 and the uniform application in Theorem 3.6.
* Assadi, S.; Behnezhad, S.; Bhattacharya, S.; Costa, M.; Solomon, S.; Zhang, T. Vizing's Theorem in Near-Linear Time. arXiv:2410.05240. Used only for the classical Delta+1 theorem restated in the abstract.
* The preceding session's root-regularization proof and the complete-split symmetrization programme motivated the argument. All additional copying, strict-penalty, terminal, and boundary steps needed here have been restated and proved in this document.
