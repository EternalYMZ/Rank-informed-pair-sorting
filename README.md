# Project S · P07 · Rank-informed pair sorting

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For every input in a linear order and every prescribed sequence of slot pairs, the successful compare-exchanges, the final ordinary insertion shifts, and the intervening-key corrections sum to the original insertion shifts. Overlapping gates and repeated keys are allowed. For predetermined disjoint pairs on distinct keys, additional roots check finite three- and four-key order counts, the maximum sum of interior spans, and the optimizing pair counts for that span expression. The uniform-input expected cost of the executed layer still needs a formal bridge between these results. Rank-informed pairing remains a separate problem.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). DisjointLayerMean and DisjointLayerEndpoints account for the uniform mean insertion movement of prescribed disjoint pairs. Count and Exchange give the arithmetic comparisons for pair counts and exchanges.
