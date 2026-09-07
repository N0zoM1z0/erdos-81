# PEO-hostable batches and exact elimination-tree selection

## Status

These are finite induced-reduction theorems, not a proof of the universal
chordal n^2/6+Cn conjecture. In particular, no universal existence claim for
an affordable batch is made. The only external graph-colouring theorem used
is Haggkvist--Janssen, *New Bounds on the List-Chromatic Index of the Complete
Graph and Other Simple Graphs*, Combinatorics, Probability and Computing 6
(1997), 295--313, DOI 10.1017/S0963548397002927: chi'_ell(K_s) <= s.
It implies the same s-list upper bound for every subgraph of K_s by extending
lists on missing edges and then restricting a colouring.

Write B_C(n)=n^2/6+Cn. I_X contains exactly the edges of G incident with X,
so retained vertices are independent in I_X. Define

  c_G(X)=e_G(X,V\X)-e(G[X]),
  margin_C(X)=|X|(2n-|X|)/6+C|X|-c_G(X).

### Exact incident price

If every internal edge can be properly coloured by a retained common
neighbour, its triangle and all leftover incident K2s give c_G(X) parts.
This is optimal among all clique partitions of I_X: weights -1 on internal
edges and +1 on crossing edges are at most 1 on every clique. A clique with
one retained vertex and k selected vertices has weight k-C(k,2)<=1; pure
selected cliques have nonpositive weight. No size restriction on competing
clique parts is used.

### Automatic PEO domains

Fix a PEO v_1,...,v_n, and let delta be the original minimum degree.
If W={v_1,...,v_m} and 2m<=delta+1, every X subset W is host-colourable using
only V\W. For an internal edge v_i v_j with i<j<=m, every neighbour of v_i
in the suffix is also adjacent to v_j. There are at least delta-(m-1)>=m
such neighbours. Give each internal edge its suffix-host list and apply
the s-list theorem with s=|X|<=m. A common palette across all vertices is
not required.

There is a second automatic domain. Put a(v)=|N^+(v)| and
A_s={v:a(v)>=2s-1}. Every subset X of A_s of order at most s is host-colourable.
For an internal edge whose earlier endpoint is u, at least
2s-1-(|X|-1)>=s retained later neighbours are available as common hosts.

More generally an initial PEO set X has, on any edge uv, the later-host
list of its earlier endpoint. This list has size at least
 delta-Delta(G[X]).
Thus delta>=3 Delta(G[X])-1 is an elementary greedy sufficient condition,
with the edgeless case automatic. The small-order condition
2|X|<=delta+1 is a different, often useful sufficient condition.

### Connected witnesses

If X has components X_1,...,X_t, then cp(I_X)=sum_i cp(I_{X_i}): no clique
of I_X can use selected vertices in two components. If each is fully hosted,
its exact local price is c_G(X_i), and
 margin_C(X)=sum_i margin_C(X_i)-(1/3)sum_{i<j}|X_i||X_j|.
Thus an affordable nonempty union contains an affordable connected component.
The original graph and original budget n are used in this identity.
For general disjoint sets X,Y the union margin identity has correction
3e(X,Y)-|X||Y|/3; it is valid as a scalar identity, and its price is usable
only when the corresponding host-colouring conditions hold.

### Elimination-tree oracle

For a vertex with later neighbours set parent(v) equal to its earliest later
neighbour. This yields a rooted forest, with edges directed toward later
vertices. Every graph edge connects an ancestor and descendant: if w is a
later neighbour of v other than parent(v), it is a later neighbour of
parent(v), so iterate.

Every earlier neighbour of a vertex belongs to its descendant subtree.
For T_v the full descendant subtree, with b(u)=|N^-(u)|,
 e(G[T_v])=sum_{u in T_v} b(u),
 c_G(T_v)=sum_{u in T_v}(a(u)-2b(u)).
Moreover G[T_v] is connected and N(T_v)=N^+(v), a clique.

Every linear extension that eliminates descendants before ancestors is a
PEO: the remaining neighbours of each eliminated vertex are a subset of
its original later neighbours. Every initial set of such an extension is
a disjoint union of full subtrees at incomparable nodes, and those subtrees
are anticomplete.

Put L=max(1,floor((delta+1)/2)); singletons are trivially host-colourable.
All connected T_v of size at most L are automatically host-colourable.
Among all downward-closed initial sets whose components have size at most L,
an affordable nonempty set exists iff one of those T_v is affordable.
The proof is the connected-witness identity above. This statement decides
existence, not maximum margin or maximum deletion size over disconnected
unions. It is relative to the fixed elimination forest.

All subtree sizes and costs are obtained by accumulating 1 and a(v)-2b(v)
from children to parents, in O(n+e(G)) arithmetic operations after a valid
PEO has been supplied. This does not assert that constructing the subsequent
list-edge colouring takes linear time. Optional PEO validation in the
reference code is also separate from that complexity claim.

### A deterministic averaging test on an automatic domain

Let Y subset A_s have m>=s vertices, and let X be a uniform s-subset of Y.
Then
 E margin_C(X) = s(n/3+C-(1/m)sum_{v in Y}d_G(v))
                -s^2/6+3e(G[Y])s(s-1)/(m(m-1)).
For s=1 interpret the last term as zero. If this is nonnegative, an affordable
batch exists and can be found by conditional expectations while keeping its
cardinality s. All outcomes in this domain are host-colourable, so no
post-selection list constraint is lost. This is a sufficient averaging
criterion, not an exact global optimum algorithm.

### Robust dense-prefix criterion

Let X be an automatically hostable prefix of size s>=k+1. Suppose every
forward degree in X is at most n/3+k and
 e(G[X])>=ks-C(k+1,2)-beta, beta>=0.
The exact prefix price is sum_{v in X}a(v)-2e(G[X]), hence
 margin_C(X)>=(k+C)s-s^2/6-k(k+1)-2beta.
At s=2k the right side is k^2/3+(2C-1)k-2beta.
At s=3k it is k^2/2+(3C-1)k-2beta.
In particular, when 6k<=delta+1, k>=8, C>=0, beta<=k^2/8, the 3k-prefix
is affordable with margin at least k^2/4-k>0. This tolerates a quadratic
internal-edge deficit; it assumes this dense prefix exists.

For G=K_d join P_{2d}^k, d>=8k, the natural PEO has first s path vertices,
forward degree d+k, e(G[X])=ks-C(k+1,2), and delta=d+k. Therefore
 c_G(X)=ds-ks+k(k+1),
 margin_C(X)=(k+C)s-s^2/6-k(k+1)
for k<=s<=2d-k. The case s=3k is the user-supplied calculation.
The case d=48,k=6,s=12,C=0 has price 546, allowance 552 and margin 6.

In that graph every clique X with 1<=|X|<=floor(55/2) fails the test.
For a universal vertices and b path vertices, b<=7, the minimum degree sum
is a(144-1)+b(48+6)+C(b,2), attained by b consecutive vertices at a path end.
The maximum resulting clique-deletion margin over all such a,b is -37/6.
This finite comparison was checked with exact fractions.

### Exact bounded-domain score

For binary z_v indicating X,
 6 margin_C(X)=sum_v(2n+6C-1-6d_G(v))z_v
               +sum_{u<v}(18*1_{uv in E}-2)z_uz_v.
The pair coefficients are 16 on edges and -2 on nonedges. The objective is
not, as written, a nonnegative-pair minimum-cut problem. The audit uses
exhaustive exact optimization, and Jacobian independently checked the
14-vertex anchored encoding for the 12-vertex path window.
The anchor bonus is 1807; its maximum is 1843, so the exact batch margin
maximum is (1843-1807)/6=6. Both anchors are forced into a maximizing set
by a bonus strictly larger than the maximum value achievable without them.

### Edge-edit stability of the induced reduction

Suppose I_X(G_0) has the triangle/K2 partition from full hosting and G_1 has
the same vertex set. Let epsilon count incident edges added or removed.
Restrict every old triangle to its surviving edges, retaining a full triangle
or using K2s for a proper restriction. Add all new incident edges as K2s.
Removing one or more edges from a triangle raises its part count by at most
the number of removed edges. Therefore
 cp(I_X(G_1))<=c_{G_0}(X)+epsilon.
If margin_C^{G_0}(X)>=epsilon and G_1 is chordal, the same vertex batch is an
affordable induced reduction in G_1. A new full host colouring is not needed.
Only triangle/K2 base parts are used in this robustness claim; it does not
assert the analogous one-per-edge bound for arbitrarily large clique parts.

### Composition and the missing implication

Each constructed local partition consumes only edges incident with the
removed batch. Reusing retained vertices as hosts in later rounds is safe.
The budget differences telescope exactly through current induced graphs.
No sum of separator sizes occurs.

None of the results proves that an affordable batch must exist in every
remaining chordal graph. The subtree oracle is exact only for its fixed
forest and its admitted components; the window and forward-layer tests
cover further sets, not all possible sets. Combining those searches with a
universal terminal theorem remains an unproved obligation. No absolute C
for all chordal graphs or counterexample to that assertion is claimed here.
