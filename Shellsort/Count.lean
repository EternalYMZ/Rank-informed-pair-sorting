import Mathlib.Tactic

namespace Shellsort.PairCount

noncomputable def harmonic : ℕ → ℝ
  | 0 => 0
  | k+1 => harmonic k + 1 / (k+1:ℝ)

noncomputable def cost (n k : ℕ) : ℝ :=
  (n:ℝ)*(n-1)/4+n-(k:ℝ)*(n-k-1)/3+k/2-harmonic k-harmonic n+harmonic (2*k)

theorem step (n k : ℕ) :
    cost n (k+1) - cost n k = (2*(k:ℝ)+2-n)/3 + 1/2 +
      1/((2*(k:ℝ)+1)*(2*(k:ℝ)+2)) := by
  unfold cost
  rw [show 2*(k+1)=2*k+1+1 by omega]
  simp only [harmonic, Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  field_simp; ring

theorem before {n k : ℕ} (hn : 6 ≤ n) (hk : k < n/2-1) :
    cost n (k+1) < cost n k := by
  have e := step n k
  by_cases h : k=0
  · subst k
    norm_num at e
    have : (6:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · have a : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have b : 2*(k:ℝ)+4 ≤ n := by exact_mod_cast (show 2*k+4 ≤ n by omega)
    have pos : 0 < (2*(k:ℝ)+1)*(2*k+2) := by positivity
    have q : 1/((2*(k:ℝ)+1)*(2*k+2)) < 1/6 := by
      apply (div_lt_iff₀ pos).mpr
      nlinarith [sq_nonneg (k:ℝ)]
    linarith

theorem after {n k : ℕ} (hk : n/2-1 ≤ k) : cost n k < cost n (k+1) := by
  have b : (n:ℝ) ≤ 2*k+3 := by exact_mod_cast (show n ≤ 2*k+3 by omega)
  have p : 0 < 1/((2*(k:ℝ)+1)*(2*k+2)) := by positivity
  linarith [step n k]

theorem unique {n : ℕ} (hn : 6 ≤ n) (k : ℕ) (hne : k ≠ n/2-1) :
    cost n (n/2-1) < cost n k := by
  rcases lt_or_gt_of_ne hne with h | h
  · have aux (j : ℕ) (hj : j ≤ n/2-1) (hkj : k < j) : cost n j < cost n k := by
      induction j with
      | zero => omega
      | succ j ih =>
        have t := before hn (show j < n/2-1 by omega)
        by_cases q : k=j
        · simpa [q] using t
        · exact t.trans (ih (by omega) (by omega))
    exact aux _ le_rfl h
  · induction k with
    | zero => omega
    | succ k ih =>
      have t := after (n:=n) (k:=k) (by omega)
      by_cases q : k=n/2-1
      · simpa [q] using t
      · exact (ih q (by omega)).trans t
end Shellsort.PairCount

