import Shellsort.FirstPassCostBounds
import Shellsort.PairLayerInsertion
import Mathlib.Data.List.FinRange

namespace Shellsort.PairLayerCostFormula

open PairLayerInsertion
noncomputable section

theorem physical_raw_mean (n : ℕ) :
    uniformAverage (fun p : RankPlacement n =>
      ((insertionExecution ((List.finRange n).map p.symm)).2 : ℝ)) =
    (n:ℝ)*((n:ℝ)-1)/4 := by
  have bridge (p : RankPlacement n) :
      (insertionExecution ((List.finRange n).map p.symm)).2 =
        gapInsertionCost p 1 (by decide) := by
    rw [← List.ofFn_eq_map, insertionExecution_ofFn_count, gapInsertionCost_eq_gapInversions,
      gapInversions_nat_pair_sum]
    simp [Nat.mod_one]
  simp_rw [bridge]
  simpa [Nat.mod_one] using uniform_firstPassCost_quotient_remainder n 1 (by decide)

/-- A certified expected saving for an executed layer is converted to the exact
mean of its successful exchanges plus the ordinary final insertion shifts. -/
theorem layer_cost_of_saving (n : ℕ) (gates : List SlotPair) (s : ℝ)
    (hs : uniformAverage (fun p : RankPlacement n =>
      ((runLayer gates ((List.finRange n).map p.symm)).saving : ℝ)) = s) :
    uniformAverage (fun p : RankPlacement n =>
      let out := runLayer gates ((List.finRange n).map p.symm)
      ((out.exchanges + (insertionExecution out.output).2 : ℕ) : ℝ)) =
      (n:ℝ)*((n:ℝ)-1)/4 - s := by
  apply eq_sub_iff_add_eq.mpr
  rw [← hs, ← uniformAverage_add, ← physical_raw_mean]
  congr 1
  funext p
  rw [← Nat.cast_add]
  exact congrArg (Nat.cast : ℕ → ℝ) (layer_then_insertion _ _)

#print axioms physical_raw_mean
#print axioms layer_cost_of_saving

end
end Shellsort.PairLayerCostFormula
