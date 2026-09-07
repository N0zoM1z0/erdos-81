# Exact defect accounting and rigidity near the chordal clique-partition maximum

## Status and dependencies

This is an addendum to the supplied session proof `A local-to-global stability proof for chordal clique partitions`. The new finite perturbation lemma below is elementary and independent of that proof. The global classification uses the supplied proof's fixed-neighborhood stability and strict root-regularization lemmas. Neither document has received independent mathematical peer review or formal verification. Finite audits are exact regression certificates, not an enumeration proof of the asymptotic theorem.

Write

    M(n) = floor(n(n+1)/6),
    Q(n) = (2n+1)^2/24,
    B_n(p) = p(n-p)-binom(p,2),
    ell_n(p) = M(n)-B_n(p).

The supplied closure uses delta=10^(-30), rho=10^(-12), and

    N = max{10^32, T(delta/2)},

where T(epsilon) is the uniform threshold for the fractional-to-integral packing transfer with triangle gain 2 and K4 gain 5. In particular, `cp_{<=4}(G)<=M(n)` for chordal G of order n>=N. The external transfer is Theorem 3.4 of Rohatgi--Urschel--Wellens, arXiv:2005.02529; its uniform application is stated explicitly in their proof of Theorem 3.6.

We retain the same N, not a new threshold depending on the deficit.

## 1. An elementary exact local repair lemma

Let G be any finite simple graph with a specified clique P of order p>=2. Let J=G-P have order q. Put

    a = pq-e(P,J),     m=e(J),     T=a+2m.

Assume

    T <= min{p,q-p}.                                      (1.1)

Then

    cp(G) = cp_{<=4}(G) = cp_f(G) = B_n(p)-a-2m,            (1.2)
    cp_{<=3}(G) = B_n(p)-a-m,                              (1.3)
    nu_3(G) = nu_3^*(G) = binom(p,2)+m,                    (1.4)
    W_4(G) = W_4^*(G) = 2binom(p,2)+3m.                    (1.5)

Here cp_f is the fractional edge-clique partition LP with equality constraints and all nontrivial clique sizes. No chordality is needed.

### 1.1 Choose clean outside hosts

Call a vertex of J clean if it has no neighbor in J and is adjacent to all of P. At most a outside vertices are incident with missing spokes, and at most 2m are incident with outside edges. Thus at least

    q-a-2m >= p

clean hosts exist. They form an independent set.

### 1.2 Use one K4 per outside edge

Process uv in E(J). Assign it two previously unused vertices of P adjacent to both u and v. At most a root vertices are forbidden by missing incidences, and after j assignments at most 2j root vertices have been used. At stage j<m there are at least

    p-a-2j >= 2m-2j >= 2

available vertices. The resulting K4s are edge-disjoint even when the outside edges meet, because their root pairs are vertex-disjoint.

These K4s cover all m outside edges and m root edges. Factor K_p into at most p matching classes by the round-robin construction. Delete the reserved m root pairs from their classes and assign the classes injectively to clean hosts. Every remaining root edge becomes a triangle. The clean hosts are not endpoints of outside edges, so their spokes cannot conflict with the K4s.

Use K2s for all remaining edges. The partition has

    m K4s,
    binom(p,2)-m root-hosted triangles,
    pq-a-2binom(p,2)-2m remaining K2s.

Its total is B_n(p)-a-2m.

### 1.3 A lower certificate for every clique size

Give weight -1 to root edges, +1 to crossing edges, and -2 to outside edges. A clique with x root vertices and y outside vertices has weight

    w(x,y)=xy-binom(x,2)-2binom(y,2).

The exact identity

    2w(x,y)=y(3-y)+(x-y)(1-x+y) <= 2

holds for all nonnegative integers x,y. Therefore every clique has weight at most one. The total edge weight is B_n(p)-a-2m, proving (1.2), including cp_f.

For mixed packing, the nonnegative weights 1-w_e give triangle sums at least two and K4 sums at least five. Their total is 2binom(p,2)+3m. The constructed packet attains this value, proving (1.5).

### 1.4 The triangle-only optimum is also exact

For each outside edge choose a distinct common root neighbor. The preceding capacity condition easily supplies these m different roots. Use the resulting outside triangles, and host every root edge on the clean vertices via its factorization. This produces exactly binom(p,2)+m edge-disjoint triangles.

The root edges together with E(J) meet every triangle of G. Giving them cover weight one is a fractional triangle-cover certificate of size binom(p,2)+m. This proves (1.4) and hence (1.3).

### 1.5 Structure of every unrestricted optimal partition

Equality w(x,y)=1 is possible only for

    (x,y)=(1,1),(2,1),(2,2),(3,2).

Indeed,

    2(1-w)=(x-y)(x-y-1)+(y-1)(y-2),

and both terms are nonnegative integers. Since the total lower certificate equals the attained optimum, every part in every optimal partition has weight exactly one.

Thus every optimum consists of crossing K2s, root-hosted triangles, two-root/two-outside K4s, and three-root/two-outside K5s. Exactly m parts meet J in two vertices, one for each outside edge. An optimal partition with no K5s is supplied above.

## 2. A canonical exact classification throughout a linear deficit window

**Theorem.** Let G be chordal on n>=N vertices and let s be an integer with

    0 <= s <= floor(n/100).

If cp(G)>=M(n)-s, then the set

    P = {v : d_G(v)>n/2}                                  (2.1)

is a clique. With p=|P|, J=G-P, a=p(n-p)-e(P,J), and m=e(J),

    M(n)-cp(G) = ell_n(p)+a+2m <= s.                       (2.2)

All identities (1.2)--(1.5) hold. Conversely, in this range of n and s, a chordal G has cp(G)>=M(n)-s exactly when it admits a clique P for which

    ell_n(p)+a+2m <= s.                                   (2.3)

Any such P is necessarily (2.1).

### Proof: enter the local neighborhood

Let Phi=e-W_4^*. The weighted transfer bound gives

    Phi(G) >= cp(G)-(delta/2)n^2
           >= n^2/6-s-(delta/2)n^2
           >= n^2/6-delta n^2.

The final inequality holds since n>=10^32 and s<=n/100. The supplied fixed-neighborhood stability theorem therefore puts G inside the strict regularization neighborhood.

Its strict terminal estimate supplies an actual clique P such that

    cp(G) <= B_n(p)-m/9-a/2.

Consequently

    ell_n(p)+m/9+a/2 <= s.                                (2.4)

In particular

    a+2m <= 18s.                                         (2.5)

Also ell_n(p)>=0 for every integer p. Since Q(n)-M(n)<=3/8,

    (3/2)(p-(2n+1)/6)^2
        =Q(n)-B_n(p) <= s+3/8.                           (2.6)

For n>=100, s<=n/100, this implies

    n/4 <= p <= 3n/8.                                    (2.7)

One exact arithmetic check is

    (n/24-1/6)^2-(n/150+1/4)
       =(25n^2-296n-3200)/14400 >=0  (n>=100).

Thus min{p,n-2p}>=n/4, while a+2m<=18s<=9n/50<n/4. The finite lemma applies, and its exact value gives (2.2).

### Canonical root

Now a+2m<=s. Every root vertex has degree at least n-1-a>=n-1-s>n/2. Every outside vertex has degree at most p+m<=3n/8+s/2<n/2. This proves (2.1).

### Converse

If (2.3) holds for any clique P, then ell_n(p)<=s gives (2.7), while a+2m<=s. These inequalities imply (1.1). The finite lemma yields cp=B_n(p)-a-2m, and (2.3) gives the desired lower bound. The degree argument again makes the root canonical. QED.

The inverse implication uses no asymptotic rounding after the graph has entered the neighborhood. The only use of transfer is to locate an integral near-extremizer inside that neighborhood.

## 3. Edit distance, uniqueness, and finite templates

For the canonical P, let S_P be the complete-split graph with clique side P. Exactly a crossing pairs must be added, and exactly m outside edges must be removed, to turn G into S_P. Thus

    distance(G,S_P)=a+m <= s-ell_n(p)-m <= s.              (3.1)

In fact S_P is the unique complete-split graph at distance at most s from G, on the given labelled vertex set. To see this, suppose S_K is that close. A vertex of J cannot lie in K: its degree in G is at most 3n/8+s/2, whereas a core vertex of S_K has degree n-1, a difference greater than s. Hence K is a subset of P. A vertex of P cannot be left outside K: its degree in G is at least n-1-s, whereas its degree in S_K would be |K|<=p<=3n/8, again differing by more than s. Thus K=P.

Therefore the exact distance to the family of all complete-split graphs is a+m, not merely bounded above by it.

All exceptional pairs are incident with at most a vertices in P and at most a+2m vertices in J. Their union has at most 2a+2m<=2s vertices. Every other root vertex is universal, and every other outside vertex is adjacent exactly to P and has no outside neighbor. For fixed s and fixed n modulo three, the near-extremizers therefore come from finitely many defect templates, with variable multiplicities of universal core vertices and clean independent vertices.

This does not say that a near-extremizer is s edits from an exact extremizer. Changing the root order has a separate price, ell_n(p). For example, at n=3k, S_{k+1,2k-1} has deficit one and no edge defects, but turning it into the exact extremal S_{k,2k} requires 2k-1 pair edits.

## 4. Exact rigidity and the displacement costs

Write n=3k+r, 0<=r<=2, and p=k+j. Then

    r=0: ell_n(p)=j(3j-1)/2,
    r=1: ell_n(p)=3j(j-1)/2,
    r=2: ell_n(p)=(j-1)(3j-2)/2.                          (4.1)

These identities are independent of k.

At s=0, (2.2) forces a=m=ell_n(p)=0. Thus every extremizer is complete-split, with root orders

    n=3k:   p=k;
    n=3k+1: p=k or k+1;
    n=3k+2: p=k+1.                                      (4.2)

These are exactly the integers nearest to (2n+1)/6. Conversely the complete-split graphs in (4.2) attain M(n) by the finite lemma with a=m=0.

The coefficient one in the edit bound is sharp. Delete exactly s spokes from a complete-split extremizer. It remains split and chordal, and (1.1) holds in the stated window. Its cp is M(n)-s, and its distance to the complete-split family is exactly s by uniqueness above.

## 5. All packing benchmarks are exact in this window

Let d_G=M(n)-cp(G). The identities from Section 1 give

    cp_{<=3}(G)-cp(G)=m,
    cp_f(G)=cp(G),
    nu_3^*(G)-nu_3(G)=0,
    W_4^*(G)-W_4(G)=0.                                  (5.1)

With the earlier notation

    S=M(n)-(e(G)-2nu_3^*(G)),
    g_4=W_4^*(G)-2nu_3^*(G),
    kappa_4=W_4^*(G)-W_4(G),

we obtain the exact decomposition

    S=ell_n(p)+a+m,
    g_4=m,
    kappa_4=0,
    d_G=S+g_4=ell_n(p)+a+2m.                              (5.2)

These zero-gap assertions apply only to the stated near-extremal window. They do not contradict the earlier counterexamples to universal O(n) full-clique fractional rounding.

## 6. A new exact non-split extremal value

**Corollary.** For every n>=N,

    max{cp(G): G chordal, nonsplit, |V(G)|=n}=M(n)-4.       (6.1)

**Upper bound.** If cp(G)>=M(n)-3, apply the theorem with s=3. Then ell+a+2m<=3, so m<=1. If m=0, P is a clique and J is independent, hence G is split. If m=1, then a<=1. At least one endpoint of the unique outside edge is complete to P; add that endpoint to P. The remaining outside set is independent, again showing G is split. Thus a nonsplit chordal graph has cp<=M(n)-4.

**Attainment.** Choose an extremal root order p from (4.2), and form

    K_p join (2K2 disjoint-union an independent set of order q-4).

It is chordal: the outside graph is a disjoint union of cliques and the root is universal. It is not split because the two outside edges induce 2K2. Here a=0 and m=2; condition (1.1) holds for n>=N. The finite lemma gives cp=B_n(p)-4=M(n)-4. QED.

## 7. Certificate-producing recognition

For a chordal input in the theorem's large-order and deficit window, the following is a complete recognition test for cp(G)>=M(n)-s:

1. Let P be the vertices of degree greater than n/2.
2. Check that P is a clique; compute a,m,ell_n(p).
3. Accept exactly when ell_n(p)+a+2m<=s.

On acceptance, the finite construction produces an optimal K2/K3/K4 partition and a signed all-clique dual with the same value. This is not a claim of polynomial-time exact optimization on arbitrary chordal graphs: the promised window is essential. At arbitrary finite orders, any accepted certificate can still be checked directly under (1.1), while rejection has no general cp implication.

All construction and checks can be performed in O(n^2) time with an adjacency matrix, including writing the O(n^2)-size partition. In particular, no list-edge-colouring existence algorithm is used in the local construction: the clean hosts allow an ordinary round-robin factorization.

## 8. Verification ledger

The supplied closure archive was extracted separately and its dependency-free replay rerun. It returned PASS for 7,964 rational mixed-packing LP certificates, 36,743 triangle/K4 dual constraints, and 1,889 single-copy steps. This is a replay of supplied evidence, not newly generated evidence or formal verification of the full proof.

The new audit checked 1,643 finite rooted perturbations, including six nonchordal examples of the local lemma. It replayed 3,286 attaining partitions and 815,824 graph-edge incidences, checked 60,594 actual clique inequalities on the enumerated small instances, and checked the all-integer clique-type inequality in 10,198 cases. It also checked 226,457 linear-window scalar cases and 104,775 root-displacement identities. A separate dependency-free script replays all 94 saved partition certificates and their source-bound duals.

Jacobian independently returned VALID for the 12-vertex, 38-edge, 23-part seed. It maximized its signed weight over all nontrivial cliques and returned value 1, attained by a K5. The total weight is 23, so the seed's cp is exactly 23. Its triangle-only optimum is 24, attained by the separate supplied triangle partition and certified by the root-plus-outside triangle cover.

The large-order threshold N is not evaluated by these finite tests. The global theorem remains a session-derived mathematical proof, not a published or formally verified resolution.

## References

* Supplied session proof, `A local-to-global stability proof for chordal clique partitions`, unchanged copy included as `closure_PROOF.md`.
* Rohatgi, Urschel, Wellens, *Regarding Two Conjectures on Clique and Biclique Partitions*, Electronic Journal of Combinatorics 28(4), P4.53 (2021), DOI 10.37236/9564; arXiv:2005.02529, Theorems 3.4 and 3.6.
* Haggkvist and Janssen, *New Bounds on the List-Chromatic Index of the Complete Graph and Other Simple Graphs*, CPC 6 (1997), 295--313, DOI 10.1017/S0963548397002927. Used by the supplied closure, not by the new finite repair lemma.
