import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-! Finite relative-order calculations for a preselected layer of disjoint slot
pairs. The three roles are left endpoint, right endpoint and an interior key.
For a previously gated interior slot, roles three and four are its two raw keys.
The algebraic last step optimizes the proposed span profit over the pair count. -/
namespace Shellsort.PairLayerRelativeOrder

def rawHit {α : Type*} [LinearOrder α] : List α → ℕ
  | [a,b,x] => if b < x ∧ x < a then 1 else 0
  | _ => 0

def previousHit {α : Type*} [LinearOrder α] (smaller : Bool) : List α → ℕ
  | [a,b,u,v] =>
    let x := if smaller then min u v else max u v
    if b < x ∧ x < a then 1 else 0
  | _ => 0

def three : List (Fin 3) := [0,1,2]
def four : List (Fin 4) := [0,1,2,3]

/-- One favorable unpaired relative order out of six. -/
theorem raw_order_count :
    three.permutations'.length = 6 ∧ (three.permutations'.map rawHit).sum = 1 := by decide

/-- Four favorable relative orders out of twenty-four, for each side of
the earlier comparator separately. -/
theorem previous_order_count (smaller : Bool) :
    four.permutations'.length = 24 ∧
    (four.permutations'.map (previousHit smaller)).sum = 4 := by
  cases smaller <;> decide

private theorem raw_emb {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ↪o β) (l : List α) : rawHit (l.map e) = rawHit l := by
  rcases l with _ | ⟨a, t⟩; · rfl
  rcases t with _ | ⟨b, t⟩; · rfl
  rcases t with _ | ⟨x, t⟩; · rfl
  cases t <;> simp [rawHit]

private theorem previous_emb {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ↪o β) (s : Bool) (l : List α) :
    previousHit s (l.map e) = previousHit s l := by
  rcases l with _ | ⟨a, t⟩; · rfl
  rcases t with _ | ⟨b, t⟩; · rfl
  rcases t with _ | ⟨u, t⟩; · rfl
  rcases t with _ | ⟨v, t⟩; · rfl
  rcases le_total u v with h | h
  · cases t <;> cases s <;> simp [previousHit, min_eq_left h, max_eq_right h,
      min_eq_left (e.monotone h), max_eq_right (e.monotone h)]
  · cases t <;> cases s <;> simp [previousHit, min_eq_right h, max_eq_left h,
      min_eq_right (e.monotone h), max_eq_left (e.monotone h)]

/-- The same counts hold on all assignments of any three fixed distinct
ordered values to the three roles. -/
theorem raw_order_count_of_keys {α : Type*} [LinearOrder α] (e : Fin 3 ↪o α) :
    ((three.map e).permutations'.map rawHit).sum = 1 := by
  rw [← List.map_permutations', List.map_map]
  simpa only [Function.comp_def, raw_emb] using raw_order_count.2

/-- The min and max versions each have four successes for any four distinct
fixed keys, even if those keys are far apart in the ambient order. -/
theorem previous_order_count_of_keys {α : Type*} [LinearOrder α] (e : Fin 4 ↪o α)
    (s : Bool) :
    ((four.map e).permutations'.map (previousHit s)).sum = 4 := by
  rw [← List.map_permutations', List.map_map]
  simpa only [Function.comp_def, previous_emb] using (previous_order_count s).2

/-- The interior-length sum for the optimal placement of k disjoint pairs. -/
def spanProfit (n k : ℤ) := k * (n-k-1)

private theorem nth_slot_lower {n k : ℕ} (f : Fin k → Fin n) (hf : StrictMono f)
    (i : Fin k) : i.val ≤ (f i).val := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hprev : i < k := by omega
    have inc : (f ⟨i,hprev⟩).val < (f ⟨i+1,hi⟩).val :=
      hf (show (⟨i,hprev⟩ : Fin k) < ⟨i+1,hi⟩ from Nat.lt_succ_self i)
    have prev : i ≤ (f ⟨i,hprev⟩).val := ih hprev
    change i+1 ≤ (f ⟨i+1,hi⟩).val
    omega

private theorem nth_slot_upper {n k : ℕ} (f : Fin k → Fin n) (hf : StrictMono f)
    (i : Fin k) : (f i).val + k ≤ n + i.val := by
  let g := fun x : Fin k => (f x.rev).rev
  have hg : StrictMono g := fun _ _ h => Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr h))
  have h := nth_slot_lower g hg i.rev
  simp only [g, Fin.rev_rev, Fin.val_rev] at h
  have hi := i.isLt
  have hf' := (f i).isLt
  omega

/-- With the two sets of endpoints listed in increasing order, the permutation
records which right endpoint belongs to each left endpoint. For a legal layer
the displayed signed sum counts all strictly intervening slots. -/
def spanSum {n k : ℕ} (l r : Fin k → Fin n) (pairing : Equiv.Perm (Fin k)) : ℤ :=
  ∑ i, (((r (pairing i)).val : ℤ) - (l i).val - 1)

theorem spanSum_le {n k : ℕ} (l r : Fin k → Fin n) (hl : StrictMono l)
    (hr : StrictMono r) (pairing : Equiv.Perm (Fin k)) :
    spanSum l r pairing ≤ spanProfit n k := by
  have ren := Equiv.sum_comp pairing (fun i => ((r i).val : ℤ))
  have cancel : spanSum l r pairing = spanSum l r (Equiv.refl _) := by
    simp only [spanSum, Finset.sum_sub_distrib, ren, Equiv.refl_apply]
  rw [cancel]
  calc
    _ ≤ ∑ _ : Fin k, ((n : ℤ)-k-1) := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ := nth_slot_lower l hl i
      have h₂ := nth_slot_upper r hr i
      change ((r i).val : ℤ) - (l i).val - 1 ≤ _
      omega
    _ = spanProfit n k := by simp [spanProfit]; ring

/-- Take the first k slots as left endpoints and the last k as right
endpoints. The two sets are disjoint, all pairs are forward, and they attain
the upper bound for every assignment of the two sets to each other. -/
theorem extremal_spans {n k : ℕ} (h : 2*k ≤ n) :
    ∃ l r : Fin k → Fin n, StrictMono l ∧ StrictMono r ∧
      (∀ i j, l i < r j) ∧
      ∀ pairing : Equiv.Perm (Fin k), spanSum l r pairing = spanProfit n k := by
  let l : Fin k → Fin n := fun i => ⟨i.val, by have := i.isLt; omega⟩
  let r : Fin k → Fin n := fun i => ⟨n-k+i.val, by have := i.isLt; omega⟩
  refine ⟨l,r,fun _ _ h => h, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_left hij (n-k)
  · intro i j
    change i.val < n-k+j.val
    have hi := i.isLt
    omega
  · intro pairing
    have ren := Equiv.sum_comp pairing (fun i => ((r i).val : ℤ))
    have cancel : spanSum l r pairing = spanSum l r (Equiv.refl _) := by
      simp only [spanSum, Finset.sum_sub_distrib, ren, Equiv.refl_apply]
    have val (i : Fin k) : ((r i).val : ℤ) - (l i).val - 1 = (n:ℤ)-k-1 := by
      change ((n-k+i.val : ℕ) : ℤ) - i.val - 1 = _
      omega
    rw [cancel]
    simp [spanSum, Equiv.refl_apply, val, spanProfit]
    ring

/-- At even size, the largest two feasible counts tie when m is positive.
The hypotheses also cover the empty layer at size zero. -/
theorem even_pair_counts {m k : ℤ} (_hk : 0 ≤ k) (hm : k ≤ m) :
    spanProfit (2*m) k ≤ spanProfit (2*m) m ∧
    (spanProfit (2*m) k = spanProfit (2*m) m ↔ k = m ∨ k = m-1) := by
  have diff : spanProfit (2*m) m - spanProfit (2*m) k = (m-k)*(m-k-1) := by
    unfold spanProfit
    ring
  have pos : 0 ≤ (m-k)*(m-k-1) := by
    by_cases eq : k = m
    · simp [eq]
    · exact mul_nonneg (by omega) (by omega)
  constructor
  · omega
  · constructor
    · intro eq
      have hz : (m-k)*(m-k-1) = 0 := by omega
      rcases mul_eq_zero.mp hz with h | h <;> omega
    · rintro (rfl | rfl) <;> unfold spanProfit <;> ring

/-- At odd size the unique best count is the largest feasible count. -/
theorem odd_pair_counts {m k : ℤ} (_hk : 0 ≤ k) (_hm : k ≤ m) :
    spanProfit (2*m+1) k ≤ spanProfit (2*m+1) m ∧
    (spanProfit (2*m+1) k = spanProfit (2*m+1) m ↔ k = m) := by
  have diff : spanProfit (2*m+1) m - spanProfit (2*m+1) k = (m-k)*(m-k) := by
    unfold spanProfit
    ring
  have pos := mul_self_nonneg (m-k)
  constructor
  · omega
  · constructor
    · intro eq
      have hz : (m-k)*(m-k) = 0 := by omega
      rcases mul_eq_zero.mp hz with h | h <;> omega
    · rintro rfl
      rfl

end Shellsort.PairLayerRelativeOrder

#print axioms Shellsort.PairLayerRelativeOrder.raw_order_count
#print axioms Shellsort.PairLayerRelativeOrder.previous_order_count
#print axioms Shellsort.PairLayerRelativeOrder.raw_order_count_of_keys
#print axioms Shellsort.PairLayerRelativeOrder.previous_order_count_of_keys
#print axioms Shellsort.PairLayerRelativeOrder.spanSum_le
#print axioms Shellsort.PairLayerRelativeOrder.extremal_spans
#print axioms Shellsort.PairLayerRelativeOrder.even_pair_counts
#print axioms Shellsort.PairLayerRelativeOrder.odd_pair_counts
