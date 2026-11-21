# Project S · P07 · Rank-informed pair sorting

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For every input list in a linear order and every prescribed sequence of slot pairs, Lean proves an exact identity. The number of successful compare-exchanges, the subsequent ordinary insertion shifts, and the intervening-key corrections sum to the number of insertion shifts on the original list. Each correction uses the array just before its gate. Repeated keys and overlapping gates are allowed. Optimal pair selection and its expected cost require further results.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
