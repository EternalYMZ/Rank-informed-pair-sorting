# Project S · P07 · Rank-informed pair sorting

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For every input and prescribed sequence of slot pairs, the actual successful exchanges, final ordinary insertion shifts and intervening-key corrections sum to the original insertion shifts. For disjoint pairs fixed in advance on a uniform permutation of distinct keys, Lean proves that the expected sum of successful exchanges and final shifts is n(n−1)/4 − (1/3)Σ(j−i−1). For fixed pair count it also identifies the maximum total interior span and an attaining matching. Rank-informed pairing is a separate problem.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). DisjointLayerMean and DisjointLayerEndpoints account for the uniform mean insertion movement of prescribed disjoint pairs. Count and Exchange give the arithmetic comparisons for pair counts and exchanges.
