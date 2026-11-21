import Shellsort.GapInversions
import Shellsort.PairLayerInsertion
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.ViaEmbedding

namespace Shellsort.PairSlotUniformMean
noncomputable section
open Finset

private def reindex {n : ℕ} (u : Equiv.Perm (Fin n)) : RankPlacement n ≃ RankPlacement n where
  toFun p := p.trans u.symm
  invFun p := p.trans u
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- A uniform full permutation has the same mean on an ordered list of k
distinct, predetermined slots as a uniform permutation of k abstract ranks,
for any statistic unchanged by embedding its ranks in increasing order. -/
theorem sample_mean {k n : ℕ} (slots : Fin k ↪ Fin n)
    (F : ∀ {m : ℕ}, (Fin k → Fin m) → ℕ)
    (natural : ∀ {m l : ℕ} (inc : Fin m ↪o Fin l) (v : Fin k → Fin m),
      F (fun i => inc (v i)) = F v) :
    uniformAverage (fun p : RankPlacement n => (F (fun i => p.symm (slots i)) : ℝ)) =
    (∑ d : Equiv.Perm (Fin k), (F d : ℝ)) / (k.factorial : ℝ) := by
  classical
  let obs := fun (p : RankPlacement n) (d : Equiv.Perm (Fin k)) =>
    (F (fun i => p.symm (slots (d i))) : ℝ)
  let total := ∑ d : Equiv.Perm (Fin k), (F d : ℝ)
  have row (p : RankPlacement n) : (∑ d, obs p d) = total := by
    let x := slots.trans p.symm.toEmbedding
    let s := Finset.univ.map x
    have card : s.card = k := by simp [s]
    let order := s.orderIsoOfFin card
    let inc := s.orderEmbOfFin card
    let all : Fin k ≃ (Finset.univ : Finset (Fin k)) :=
      {toFun := fun i => ⟨i,Finset.mem_univ i⟩, invFun := Subtype.val,
       left_inv := fun _ => rfl, right_inv := fun _ => rfl}
    let rank : Equiv.Perm (Fin k) :=
      all.trans ((Finset.univ.equivMap x).trans order.symm.toEquiv)
    have sorted (i : Fin k) : inc (rank i) = p.symm (slots i) := by
      change ((order (order.symm ((Finset.univ.equivMap x) (all i)))).val) = _
      rw [order.apply_symm_apply]; rfl
    let shift : Equiv.Perm (Fin k) ≃ Equiv.Perm (Fin k) :=
      { toFun := fun d => d.trans rank, invFun := fun d => d.trans rank.symm,
        left_inv := by intro d; ext; simp, right_inv := by intro d; ext; simp }
    calc ∑ d, obs p d = ∑ d, (F (shift d) : ℝ) := by
          apply sum_congr rfl; intro d _
          change (F (fun i => p.symm (slots (d i))) : ℝ) = F (d.trans rank)
          simpa only [Equiv.trans_apply,sorted] using congrArg Nat.cast
            (natural inc (d.trans rank))
         _ = total := shift.sum_comp (fun d => (F d : ℝ))
  have col (d : Equiv.Perm (Fin k)) : uniformAverage (fun p => obs p d) =
      uniformAverage (fun p : RankPlacement n => (F (fun i => p.symm (slots i)) : ℝ)) := by
    have eq := uniformAverage_reindex (reindex (d.viaEmbedding slots))
      (fun p : RankPlacement n => (F (fun i => p.symm (slots i)) : ℝ))
    simpa [obs,reindex,Equiv.Perm.viaEmbedding_apply] using eq
  have comm : uniformAverage (fun p => ∑ d, obs p d) =
      ∑ d, uniformAverage (fun p => obs p d) := by
    unfold uniformAverage
    rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [row] at comm
  simp only [col,uniformAverage_const,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at comm
  exact (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).2
    (by simpa only [mul_comm,total] using comm.symm)

def raw {m : ℕ} (v : Fin 3 → Fin m) : ℕ := if v 1 < v 2 ∧ v 2 < v 0 then 1 else 0

def paired {m : ℕ} (low : Bool) (v : Fin 4 → Fin m) : ℕ :=
  let x := if low then min (v 2) (v 3) else max (v 2) (v 3)
  if v 1 < x ∧ x < v 0 then 1 else 0

private theorem raw_count : (∑ d : Equiv.Perm (Fin 3), raw d) = 1 := by decide
private theorem paired_count (low : Bool) : (∑ d : Equiv.Perm (Fin 4), paired low d) = 4 := by
  cases low <;> decide

theorem raw_mean {n : ℕ} (s : Fin 3 ↪ Fin n) :
    uniformAverage (fun p : RankPlacement n => (raw (fun i => p.symm (s i)) : ℝ)) = 1/6 := by
  rw [sample_mean s (@raw) (by intros; simp [raw])]
  rw [← Nat.cast_sum,raw_count]; norm_num [Nat.factorial]

theorem paired_mean {n : ℕ} (s : Fin 4 ↪ Fin n) (low : Bool) :
    uniformAverage (fun p : RankPlacement n => (paired low (fun i => p.symm (s i)) : ℝ)) = 1/6 := by
  rw [sample_mean s (fun {m} => @paired m low) (by
    intro m l f v
    rcases le_total (v 2) (v 3) with h|h
    · cases low <;> simp [paired,min_eq_left h,max_eq_right h,min_eq_left (f.monotone h),max_eq_right (f.monotone h)]
    · cases low <;> simp [paired,min_eq_right h,max_eq_left h,min_eq_right (f.monotone h),max_eq_left (f.monotone h)])]
  rw [← Nat.cast_sum,paired_count]; norm_num [Nat.factorial]

open PairLayerInsertion

/-- Origins of the middle key for a gate with untouched endpoints left/right.
Different middle slots may depend on the same earlier comparator. -/
inductive Source {n : ℕ} (left right : Fin n) where
  | rawSlot (s : Fin 3 ↪ Fin n) (a : s 0 = left) (b : s 1 = right)
  | pairedSlot (s : Fin 4 ↪ Fin n) (a : s 0 = left) (b : s 1 = right) (low : Bool)

def key {n : ℕ} {l r : Fin n} (p : RankPlacement n) : Source l r → Fin n
  | .rawSlot s _ _ => p.symm (s 2)
  | .pairedSlot s _ _ low => if low then min (p.symm (s 2)) (p.symm (s 3))
                                   else max (p.symm (s 2)) (p.symm (s 3))

private theorem distinct {n : ℕ} {l r : Fin n} (p : RankPlacement n) (x : Source l r) :
    key p x ≠ p.symm l ∧ key p x ≠ p.symm r := by
  cases x with
  | rawSlot s a b =>
    subst l; subst r
    simp [key,p.symm.injective.eq_iff,s.injective.eq_iff]
  | pairedSlot s a b lo =>
    subst l; subst r
    rcases le_total (p.symm (s 2)) (p.symm (s 3)) with h|h <;>
      cases lo <;> simp [key,min_eq_left h,max_eq_right h,min_eq_right h,max_eq_left h,
        p.symm.injective.eq_iff,s.injective.eq_iff]

def event {n : ℕ} {l r : Fin n} (x : Source l r) (p : RankPlacement n) : ℕ :=
  if p.symm r < key p x ∧ key p x < p.symm l then 1 else 0

theorem event_mean {n : ℕ} {l r : Fin n} (x : Source l r) :
    uniformAverage (fun p : RankPlacement n => (event x p : ℝ)) = 1/6 := by
  cases x with
  | rawSlot s a b => subst l; subst r; exact raw_mean s
  | pairedSlot s a b lo => subst l; subst r; exact paired_mean s lo

private theorem point_saving {n : ℕ} {l r : Fin n} (xs : List (Source l r))
    (pre post : List (Fin n)) (p : RankPlacement n) :
    (comparePair pre (xs.map (key p)) post (p.symm l) (p.symm r)).saving =
      (xs.map (fun x => 2*event x p)).sum := by
  by_cases h : p.symm r < p.symm l
  · simp only [comparePair,h,ite_true,interiorSaving,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    have hx := distinct p x
    by_cases ev : p.symm r < key p x ∧ key p x < p.symm l <;>
      simp [interiorWeight,event,ev,hx.1,hx.2]
  · simp only [comparePair,h,ite_false]
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have miss : ¬ (p.symm r < key p x ∧ key p x < p.symm l) := fun z => h (lt_trans z.1 z.2)
      simpa [event,miss] using ih

theorem mean_saving {n : ℕ} {l r : Fin n} (xs : List (Source l r))
    (pre post : RankPlacement n → List (Fin n)) :
    uniformAverage (fun p => ((comparePair (pre p) (xs.map (key p)) (post p)
      (p.symm l) (p.symm r)).saving : ℝ)) = xs.length / 3 := by
  simp_rw [point_saving]
  induction xs with
  | nil => simp [uniformAverage_const]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      List.length_cons,Nat.cast_succ]
    rw [uniformAverage_add]
    have h : uniformAverage (fun p : RankPlacement n => 2*(event x p : ℝ)) =
        2*uniformAverage (fun p => (event x p : ℝ)) := by
      unfold uniformAverage; rw [←Finset.mul_sum]; ring
    rw [h,event_mean,ih]
    ring

theorem executed_mean {n : ℕ} {l r : Fin n} (xs : List (Source l r))
    (pre post : RankPlacement n → List (Fin n)) :
    uniformAverage (fun p : RankPlacement n =>
      let step := comparePair (pre p) (xs.map (key p)) (post p) (p.symm l) (p.symm r)
      ((step.exchanges + (insertionExecution step.output).2 : ℕ) : ℝ)) + xs.length / 3 =
    uniformAverage (fun p : RankPlacement n =>
      ((insertionExecution (pre p ++ (p.symm l :: (xs.map (key p) ++ [p.symm r])) ++ post p)).2 : ℝ)) := by
  rw [← mean_saving xs pre post, ← uniformAverage_add]
  congr 1; funext p
  dsimp only
  rw [← Nat.cast_add]
  exact congrArg (Nat.cast : ℕ → ℝ)
    (comparePair_then_insertion (pre p) (xs.map (key p)) (post p) (p.symm l) (p.symm r))

theorem run_at_pair {α : Type*} [LinearOrder α] (pre mid post : List α) (a b : α) :
    runGate ⟨pre.length,mid.length⟩ (pre ++ (a :: (mid ++ [b])) ++ post) =
    comparePair pre mid post a b := by
  simp [runGate,List.append_assoc]

private def three_slots {n : ℕ} (l r i : Fin n) (lr : l ≠ r) (il : i ≠ l)
    (ir : i ≠ r) : Fin 3 ↪ Fin n :=
  ⟨![l,r,i],by
    intro a b eq
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm lr, Ne.symm il,Ne.symm ir]⟩

private def asRaw {n : ℕ} (l r : Fin n) (lr : l ≠ r) (mid : List (Fin n))
    (hl : l ∉ mid) (hr : r ∉ mid) (z : {i // i ∈ mid}) : Source l r :=
  .rawSlot (three_slots l r z.val lr (by rintro h; exact hl (h ▸ z.property))
                                   (by rintro h; exact hr (h ▸ z.property))) rfl rfl

/-- A prescribed physical gate on a raw permutation saves width/3 moves
on average. Prefix, endpoints, middle and suffix specify the slot layout;
take them in natural physical order to recover a gate at any two indices. -/
theorem single_gate_on_raw {n : ℕ} (l r : Fin n) (lr : l ≠ r)
    (pre mid post : List (Fin n)) (hl : l ∉ mid) (hr : r ∉ mid) :
    let initial := fun p : RankPlacement n =>
      (pre ++ (l :: (mid ++ [r])) ++ post).map p.symm
    uniformAverage (fun p : RankPlacement n =>
      let step := runGate ⟨pre.length,mid.length⟩ (initial p)
      ((step.exchanges + (insertionExecution step.output).2 : ℕ) : ℝ)) + mid.length / 3 =
      uniformAverage (fun p : RankPlacement n => ((insertionExecution (initial p)).2 : ℝ)) := by
  let middle := mid.attach.map (asRaw l r lr mid hl hr)
  have key_eq (p : RankPlacement n) : middle.map (key p) = mid.map p.symm := by
    simp only [middle,List.map_map]
    exact List.attach_map_val
  have len : middle.length = mid.length := by simp [middle]
  have h := executed_mean middle (fun p => pre.map p.symm) (fun p => post.map p.symm)
  dsimp only at h ⊢
  simp_rw [key_eq] at h
  rw [len] at h
  simp only [List.map_append,List.map_cons,List.map_nil]
  have at_gate (p : RankPlacement n) :
      runGate ⟨pre.length,mid.length⟩ ((pre.map p.symm) ++ (p.symm l :: (mid.map p.symm ++ [p.symm r])) ++ post.map p.symm) =
      comparePair (pre.map p.symm) (mid.map p.symm) (post.map p.symm) (p.symm l) (p.symm r) := by
    simpa only [List.length_map] using run_at_pair (pre.map p.symm) (mid.map p.symm) (post.map p.symm) (p.symm l) (p.symm r)
  simpa only [at_gate] using h

#print axioms sample_mean
#print axioms event_mean
#print axioms executed_mean
#print axioms single_gate_on_raw

end
end Shellsort.PairSlotUniformMean
