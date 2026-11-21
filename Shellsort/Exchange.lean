import Mathlib.Tactic

namespace PairExchange
-- x previously seen slots; 1,2 are the new slots exposed by S,L.
noncomputable def recordLoss (x : ℝ) := 1/(x+1)+2/(x+3)-(2/(x+2)+1/(x+3))

theorem recordLoss_exact (x : ℝ) (hx : 0 ≤ x) :
    recordLoss x = 2/((x+1)*(x+2)*(x+3)) := by
  unfold recordLoss
  field_simp [show x+1 ≠ 0 by linarith, show x+2 ≠ 0 by linarith,
    show x+3 ≠ 0 by linarith]; ring

theorem SL_improvement (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1/3-recordLoss x ∧ (1/3-recordLoss x = 0 ↔ x=0) := by
  rw [recordLoss_exact x hx]
  have h : 0 < (x+1)*(x+2)*(x+3) := by positivity
  have hp : 6 ≤ (x+1)*(x+2)*(x+3) := by nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ h).mpr
    linarith
  constructor
  · intro he
    have eq : 2 / ((x+1)*(x+2)*(x+3)) = 1/3 := by linarith
    have hh := (div_eq_iff h.ne').mp eq
    nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  · rintro rfl
    norm_num

theorem zero_increment (x b : ℝ) :
    0/x + b/(x+b) = b/(x+b) + 0/(x+b) := by simp

end PairExchange
#print axioms PairExchange.SL_improvement

namespace PairExchange
/-- Variable part of mean comparisons: omit terms fixed by length and pair count. -/
noncomputable def wordCost (x : ℝ) : List ℕ → ℝ
  | [] => 0
  | a :: tail => -(x+a)/3 - a/(x+a) + wordCost (x+a) tail

theorem SL_in_word (x : ℝ) (tail : List ℕ) :
    wordCost x (1::2::tail) - wordCost x (2::1::tail) = 1/3-recordLoss x := by
  simp only [wordCost,Nat.cast_one,Nat.cast_ofNat, recordLoss]
  rw [show x+1+2=x+3 by ring, show x+2+1=x+3 by ring]
  ring

theorem R_in_word (x : ℝ) (b : ℕ) (tail : List ℕ) :
    wordCost x (0::b::tail) - wordCost x (b::0::tail) = b/3 := by
  simp only [wordCost, Nat.cast_zero, add_zero, zero_div, sub_zero]
  ring
end PairExchange
