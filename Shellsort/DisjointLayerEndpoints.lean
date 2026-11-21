import Shellsort.DisjointLayerMean
import Shellsort.PairLayerRelativeOrder
import Mathlib.Data.List.OfFn

namespace Shellsort.DisjointLayerMean
open PairLayerInsertion PairLayerRelativeOrder
noncomputable section

private theorem split_slot {α : Type*} (xs : List α) (i : ℕ) (h : i < xs.length) :
    xs = (xs.take i) ++ xs[i] :: xs.drop (i+1) := by
  calc xs = xs.take i ++ xs.drop i := (List.take_append_drop ..).symm
       _ = _ := by rw [List.drop_eq_getElem_cons h]

/-- Turn ordinary, zero-based array indices into a certified executable gate. -/
def ofEndpoints {n : ℕ} (l r : Fin n) (h : l < r) : Gate (List.finRange n) := by
  let xs := List.finRange n
  let rest := xs.drop (l.val+1)
  let w := r.val-(l.val+1)
  have lr : l.val < r.val := h
  have il : l.val < xs.length := by simp [xs]
  have ir : w < rest.length := by simp [w,rest,xs]; omega
  have left : xs[l.val] = l := by simp [xs]
  have right : rest[w] = r := by
    apply Fin.ext
    simp [rest,xs,w,List.getElem_drop]
    omega
  refine ⟨l,r,xs.take l.val,rest.take w,rest.drop (w+1),?_⟩
  have a := split_slot xs l.val il
  have b := split_slot rest w ir
  rw [left] at a
  rw [right] at b
  change xs = xs.take l.val ++ l :: rest at a
  rw [b] at a
  simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using a

theorem ofEndpoints_width {n : ℕ} (l r : Fin n) (h : l < r) :
    (ofEndpoints l r h).mid.length = r.val-(l.val+1) := by
  change ((List.finRange n).drop (l.val+1) |>.take _).length = _
  simp only [List.length_take,List.length_drop,List.length_finRange]
  exact Nat.min_eq_left (Nat.sub_le_sub_right r.isLt.le _)

/-- A fixed layer specified by its left endpoints, right endpoints and a bijection.
Endpoint lists need not be monotone in execution order. -/
def indexedGates {n k : ℕ} (l r : Fin k → Fin n) (π : Equiv.Perm (Fin k))
    (forward : ∀ i, l i < r (π i)) : List (Gate (List.finRange n)) :=
  List.ofFn fun i => ofEndpoints (l i) (r (π i)) (forward i)

theorem indexed_layer_mean {n k : ℕ} (l r : Fin k → Fin n) (π : Equiv.Perm (Fin k))
    (forward : ∀ i, l i < r (π i)) (li : Function.Injective l) (ri : Function.Injective r)
    (sep : ∀ i j, l i ≠ r j) :
    uniformAverage (fun p : RankPlacement n =>
      let out := runLayer ((indexedGates l r π forward).map Gate.physical) ((List.finRange n).map p.symm)
      ((out.exchanges + (insertionExecution out.output).2 : ℕ) : ℝ)) =
      (n:ℝ)*((n:ℝ)-1)/4 - (spanSum l r π : ℝ)/3 := by
  have ds : DisjointGates (indexedGates l r π forward) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact ⟨fun e => hij.ne' (li e),sep _ _,(sep _ _).symm,fun e => hij.ne' (π.injective (ri e))⟩
  rw [disjoint_layer_mean n _ ds]
  congr 2
  simp only [indexedGates,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ofEndpoints_width,
    spanSum,Int.cast_sum,Int.cast_sub,Int.cast_natCast,Int.cast_one]
  apply Finset.sum_congr rfl
  intro i _
  have h : (l i).val < (r (π i)).val := forward i
  rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  ring

private theorem sorted_reindex {n k : ℕ} (f : Fin k → Fin n) (injective : Function.Injective f) :
    ∃ inc : Fin k ↪o Fin n, ∃ perm : Equiv.Perm (Fin k), ∀ i, inc (perm i) = f i := by
  let e : Fin k ↪ Fin n := ⟨f,injective⟩
  let s := Finset.univ.map e
  have card : s.card = k := by simp [s]
  let all : Fin k ≃ (Finset.univ : Finset (Fin k)) :=
    {toFun := fun i => ⟨i,Finset.mem_univ i⟩, invFun := Subtype.val,
     left_inv := fun _ => rfl, right_inv := fun _ => rfl}
  let order := s.orderIsoOfFin card
  let perm := all.trans ((Finset.univ.equivMap e).trans order.symm.toEquiv)
  refine ⟨s.orderEmbOfFin card,perm,?_⟩
  intro i
  change (order (order.symm ((Finset.univ.equivMap e) (all i)))).val = _
  rw [order.apply_symm_apply]
  rfl

theorem span_le_in_execution_order {n k : ℕ} (l r : Fin k → Fin n)
    (π : Equiv.Perm (Fin k)) (li : Function.Injective l) (ri : Function.Injective r) :
    spanSum l r π ≤ spanProfit n k := by
  obtain ⟨left,σ,hl⟩ := sorted_reindex l li
  obtain ⟨right,τ,hr⟩ := sorted_reindex (fun i => r (π i)) (ri.comp π.injective)
  have sL := Equiv.sum_comp σ (fun i => ((left i).val : ℤ))
  have sR := Equiv.sum_comp τ (fun i => ((right i).val : ℤ))
  simp_rw [hl] at sL
  simp_rw [hr] at sR
  have upper := spanSum_le (fun i => left i) (fun i => right i) left.strictMono right.strictMono (Equiv.refl _)
  simpa only [spanSum,Finset.sum_sub_distrib,Equiv.refl_apply,sL,sR] using upper

/-- The least mean among all predetermined layers of exactly k disjoint pairs
is attained. The competitor quantifier allows every pairing and execution order. -/
theorem optimum_at_fixed_count (n k : ℕ) (feasible : 2*k ≤ n) :
    let best := (n:ℝ)*((n:ℝ)-1)/4 - (spanProfit n k : ℝ)/3
    let cost := fun (l r : Fin k → Fin n) (π : Equiv.Perm (Fin k)) (hf : ∀ i, l i < r (π i)) =>
      uniformAverage (fun p : RankPlacement n =>
        let out := runLayer ((indexedGates l r π hf).map Gate.physical) ((List.finRange n).map p.symm)
        ((out.exchanges + (insertionExecution out.output).2 : ℕ) : ℝ))
    (∀ (l r : Fin k → Fin n) (π : Equiv.Perm (Fin k)) (hf : ∀ i, l i < r (π i)),
      Function.Injective l → Function.Injective r → (∀ i j, l i ≠ r j) → best ≤ cost l r π hf) ∧
    ∃ l r : Fin k → Fin n, Function.Injective l ∧ Function.Injective r ∧
      (∀ i j, l i ≠ r j) ∧ ∃ forward : ∀ i j, l i < r j,
      ∀ π : Equiv.Perm (Fin k), cost l r π (fun i => forward i (π i)) = best := by
  dsimp only
  constructor
  · intro l r π hf li ri disj
    rw [indexed_layer_mean _ _ _ _ li ri disj]
    have h : ((spanSum l r π : ℤ) : ℝ) ≤ (spanProfit n k : ℝ) :=
      by exact_mod_cast span_le_in_execution_order l r π li ri
    linarith
  · obtain ⟨l,r,ls,rs,forward,attain⟩ := extremal_spans feasible
    have sep (i j) := (forward i j).ne
    refine ⟨l,r,ls.injective,rs.injective,sep,forward,?_⟩
    intro π
    rw [indexed_layer_mean _ _ _ _ ls.injective rs.injective sep,attain]

#print axioms optimum_at_fixed_count

end
end Shellsort.DisjointLayerMean
