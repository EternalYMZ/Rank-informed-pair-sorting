# How many insertion shifts can a layer of pairs save?

Direct insertion on [3,2,1,0] takes six shifts. Comparing the ends and exchanging them leaves [0,2,1,3], which takes one. Counting the initial exchange as one movement gives a net saving of four.

Exchanging inverted endpoints $A>B$ removes their mutual inversion. Each intervening $X$ with $B<X<A$ removes two more. The initial exchange pays for the mutual inversion; the intervening keys account for the saving. Sum over the actual sequence of states, including for overlapping pairs. With ties, an interior key equal to either endpoint contributes one unit on a successful exchange.

For uniform distinct keys and predetermined disjoint pairs $(i_t,j_t)$ let $M$ count successful pair exchanges plus final insertion shifts. Then
$$\mathbb E M=n(n-1)/4-\tfrac13\sum_t(j_t-i_t-1).$$
An untouched interior key has the saving order in one of six relative orders. If it has already participated in another pair it holds the smaller or larger of two original keys. In either case four of 24 relative orders qualify. Each interior slot therefore saves $2/6=1/3$ in expectation. Linearity allows the savings to be dependent.

For fixed pair count $k$, any matching of the leftmost $k$ slots to the rightmost $k$ maximizes the sum of interior spans at $k(n-k-1)$. Input-dependent pairing changes the order law. The Lean development connects local order counts to uniform permutations, identifies the source of interior keys under disjoint gates, and sums the actual movements across the layer.

[PairLayerInsertion.lean](https://github.com/EternalYMZ/Rank-informed-pair-sorting/blob/4e033ec5d8a09d311e3a52c44e2d919436073443/Shellsort/PairLayerInsertion.lean) · [PairLayerRelativeOrder.lean](https://github.com/EternalYMZ/Rank-informed-pair-sorting/blob/4e033ec5d8a09d311e3a52c44e2d919436073443/Shellsort/PairLayerRelativeOrder.lean)
