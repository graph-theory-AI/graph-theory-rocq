```json
{
  "verdict": "proved",
  "confidence": "medium",
  "one_line": "The conjecture holds with the explicit crude bound c(m)=32(m+1)^3, by combining Carathéodory reduction with proportional-necklace interpolation between two matchings.",
  "would_publish": true,
  "caveats": "The proposed bound m/2 remains open; the proof uses the standard proportional interval-splitting theorem, and novelty has not been independently checked."
}
```

# Theorem

For every \(m\ge 1\), the conclusion of Conjecture 1.15 holds with
\[
c(m)=32(m+1)^3.
\]

Thus, if \(G\) is a finite bipartite graph, \(D=\Delta(G)\ge1\), and
\(E_1,\dots,E_m\subseteq E(G)\), then \(G\) has a matching \(S\) such that
\[
|S|\ge \frac{|E(G)|}{D}-32(m+1)^3
\]
and
\[
|S\cap E_i|\le \left\lceil\frac{|E_i|}{D}\right\rceil
\qquad (1\le i\le m).
\]

The constant is deliberately not optimized.

## 1. Proportional interval splitting

We use the following standard form of the proportional continuous necklace-splitting theorem.

### Lemma 1
Let \(\nu_1,\dots,\nu_r\) be nonatomic finite nonnegative measures on a compact interval \(I\), and let \(0\le\theta\le1\). There is a set \(X\subseteq I\), which is a union of at most \(2r\) intervals, such that
\[
\nu_j(X)=\theta \nu_j(I)
\qquad (1\le j\le r).
\]

This is also often formulated as the prescribed-share version of the generalized Hobby–Rice theorem. The usual stronger statement gives at most \(r\) intervals; the weaker \(2r\) bound is sufficient here. We only apply it to measures having piecewise-constant densities.

## 2. Interpolating two matchings

The main ingredient is that a convex combination of the statistics of two matchings can be approximately realized by one matching, with error depending only on the number of statistics.

### Lemma 2
Let \(H\) be a bipartite graph, let \(A,B\) be matchings in \(H\), and assign every edge a label
\[
w(e)=(w_0(e),\dots,w_{d-1}(e))\in\{0,1\}^d.
\]
Write
\[
w_j(M)=\sum_{e\in M}w_j(e).
\]
For every \(0\le\theta\le1\), there is a matching \(C\) such that
\[
w_0(C)\ge \theta w_0(A)+(1-\theta)w_0(B)-32d
\]
and, for \(1\le j<d\),
\[
w_j(C)\le \theta w_j(A)+(1-\theta)w_j(B)+32d.
\]

### Proof

Let the bipartition of \(H\) be \(L\cup R\). Add dummy vertices and dummy edges so that both \(A\) and \(B\) extend to perfect matchings \(A^*,B^*\) of the same balanced bipartite supergraph. All dummy edges are given label \(0\).

One explicit construction is as follows. If \(|L|=p\) and \(|R|=q\), add \(q\) dummy left vertices and \(p\) dummy right vertices. Any matching \(M\) extends to a perfect matching by:

1. matching each unmatched original left vertex to a distinct dummy right vertex;
2. matching each unmatched original right vertex to a distinct dummy left vertex;
3. matching the remaining dummy vertices bijectively.

The nontrivial components of \(A^*\triangle B^*\) are even alternating cycles. On each such cycle, write the edges cyclically as
\[
a_1,b_1,a_2,b_2,\dots,a_s,b_s,
\]
where \(a_j\in A^*\) and \(b_j\in B^*\). Regard the pair \((a_j,b_j)\) as one cell. Concatenate the cell lists of all nontrivial cycles into one interval, assigning one unit subinterval to each cell.

For every coordinate \(\ell\), define two nonatomic measures:
\[
\nu^A_\ell(\text{cell }j)=w_\ell(a_j),
\qquad
\nu^B_\ell(\text{cell }j)=w_\ell(b_j),
\]
distributing this mass uniformly over the cell. There are \(2d\) measures. By Lemma 1, there is a set \(X\), which is a union of at most \(4d\) intervals, satisfying
\[
\nu^A_\ell(X)=\theta \nu^A_\ell(I),
\qquad
\nu^B_\ell(X)=\theta \nu^B_\ell(I)
\]
for every \(\ell\).

Let \(J\) be the set of cells whose midpoints lie in \(X\). Since \(X\) has at most \(8d\) boundary points, at most \(8d\) cells are cut by its boundary. Consequently,
\[
\left|\sum_{j\in J}w_\ell(a_j)
      -\theta\sum_jw_\ell(a_j)\right|\le8d
\]
and similarly
\[
\left|\sum_{j\in J}w_\ell(b_j)
      -\theta\sum_jw_\ell(b_j)\right|\le8d.
\]

On each cycle, select \(a_j\) when \(j\in J\), and select \(b_j\) otherwise. Together with the common edges \(A^*\cap B^*\), call the resulting set \(T\). Before repairing conflicts,
\[
\left|w_\ell(T)-
 \bigl(\theta w_\ell(A^*)+(1-\theta)w_\ell(B^*)\bigr)\right|
 \le16d. \tag{1}
\]

The set \(T\) need not be a matching. Its only possible conflict on a cycle occurs when
\[
j-1\notin J,\qquad j\in J,
\]
because then \(b_{j-1}\) and \(a_j\) meet. Delete \(a_j\) at every such transition.

The sampled indicator of \(J\) changes at most \(8d\) times in the concatenated linear ordering. Closing each cyclic component can contribute one additional change, but only for a cycle already containing an internal change. Hence there are at most \(16d\) relevant cyclic transitions. We therefore delete at most \(16d\) edges.

The remaining augmented edge set is a matching. Discarding all dummy edges gives a matching \(C\) in \(H\). Deletion can only decrease every label coordinate. Thus, from (1),
\[
w_j(C)\le \theta w_j(A)+(1-\theta)w_j(B)+16d
\]
for all side coordinates \(j\ge1\), while for coordinate \(0\) we may lose another \(16d\):
\[
w_0(C)\ge \theta w_0(A)+(1-\theta)w_0(B)-32d.
\]
This proves the lemma. \(\square\)

## 3. Reduction to at most \(m+2\) matchings

Set
\[
d=m+1
\]
and, for a matching \(M\), define its statistic vector
\[
z(M)=\bigl(|M|,\ |M\cap E_1|,\dots,|M\cap E_m|\bigr)\in\mathbb R^d.
\]

By König’s line-coloring theorem, the edges of \(G\) can be partitioned into \(D=\Delta(G)\) matchings
\[
M_1',\dots,M_D'.
\]
Therefore
\[
p:=\left(\frac{|E(G)|}{D},
         \frac{|E_1|}{D},\dots,\frac{|E_m|}{D}\right)
   =\frac1D\sum_{j=1}^D z(M_j').
\]
Thus \(p\) belongs to the convex hull of the vectors \(z(M_j')\).

By Carathéodory’s theorem in \(\mathbb R^d\), there are matchings
\[
M_1,\dots,M_k,\qquad k\le d+1=m+2,
\]
and positive coefficients \(\lambda_1,\dots,\lambda_k\), with
\(\sum_j\lambda_j=1\), such that
\[
p=\sum_{j=1}^k\lambda_j z(M_j). \tag{2}
\]

## 4. Iterated interpolation

We combine these \(k\) matchings successively using Lemma 2. Label an edge \(e\) by
\[
w_0(e)=1,\qquad
w_i(e)=\mathbf 1_{\{e\in E_i\}}\quad(1\le i\le m).
\]

Let
\[
\Lambda_j=\sum_{\ell=1}^j\lambda_\ell,\qquad
p_j=\frac1{\Lambda_j}\sum_{\ell=1}^j\lambda_\ell z(M_\ell).
\]
Start with \(C_1=M_1\). Given \(C_{j-1}\), apply Lemma 2 to
\(C_{j-1}\) and \(M_j\), with
\[
\theta=\frac{\Lambda_{j-1}}{\Lambda_j},
\]
to obtain \(C_j\).

An induction gives
\[
|C_j|\ge (p_j)_0-(j-1)32d
\]
and
\[
|C_j\cap E_i|\le (p_j)_i+(j-1)32d
\qquad(1\le i\le m).
\]
Indeed, the old error is multiplied by \(\theta\le1\), and Lemma 2 adds at most \(32d\).

Since \(k-1\le d\), the final matching \(C=C_k\) satisfies
\[
|C|\ge \frac{|E(G)|}{D}-32d^2 \tag{3}
\]
and
\[
|C\cap E_i|\le \frac{|E_i|}{D}+32d^2
\qquad(1\le i\le m). \tag{4}
\]

## 5. Enforcing the exact ceilings

Put
\[
q_i=\left\lceil\frac{|E_i|}{D}\right\rceil,
\qquad
B=32d^2.
\]
By (4),
\[
|C\cap E_i|-q_i\le B.
\]

Process \(i=1,\dots,m\). Whenever the current matching contains more than \(q_i\) edges of \(E_i\), delete arbitrary edges of \(E_i\) until equality holds. Previous upper bounds remain valid because only deletions are made. At most \(B\) edges are deleted for each \(i\), hence at most \(mB\) in total.

The resulting matching \(S\) satisfies
\[
|S\cap E_i|\le q_i
 =\left\lceil\frac{|E_i|}{D}\right\rceil
\]
for every \(i\), and by (3),
\[
\begin{aligned}
|S|
&\ge \frac{|E(G)|}{D}-B-mB\\
&=\frac{|E(G)|}{D}-32(m+1)^3.
\end{aligned}
\]

This proves the conjecture with
\[
\boxed{c(m)=32(m+1)^3}.
\]

## Remarks and remaining questions

1. The argument is valid for bipartite multigraphs as well, using König’s line-coloring theorem for bipartite multigraphs.
2. The constant \(32(m+1)^3\) is very crude. The suggested bound \(c(m)=m/2\) is not approached here.
3. The only non-elementary input beyond standard matching theory and Carathéodory’s theorem is the established proportional interval-splitting theorem.
4. I have not independently verified whether this interpolation argument already appears in subsequent literature; the supplied catalog review reports no known resolution.