import Shellsort.InsertionOperations

/-! Exact movement accounting for compare-exchange gates followed by ordinary
linear insertion. A successful gate exchange counts as one operation. -/
namespace Shellsort.PairLayerInsertion
variable {α : Type*} [LinearOrder α]

/-- In a successful exchange of high and low, an intervening key accounts for
two additional inversions if strictly between the endpoint values. An equal
endpoint accounts for one, so the formula also handles repeated keys. -/
def interiorWeight (low high x : α) : ℕ :=
  if low < x ∧ x < high then 2 else if x = low ∨ x = high then 1 else 0

def interiorSaving (low high : α) (middle : List α) : ℕ :=
  (middle.map (interiorWeight low high)).sum

private theorem point_identity (low high x : α) (h : low < high) :
    (if x < high then 1 else 0) + (if low < x then 1 else 0) =
    ((if x < low then 1 else 0) + (if high < x then 1 else 0)) +
      interiorWeight low high x := by
  unfold interiorWeight
  split_ifs <;> grind

private theorem middle_counts (low high : α) (h : low < high) (m : List α) :
    smallerCount high m + largerCount low m =
    smallerCount low m + largerCount high m + interiorSaving low high m := by
  induction m with
  | nil => simp [smallerCount, largerCount, interiorSaving]
  | cons x xs ih =>
    have counts (a : α) :
        smallerCount a (x :: xs) = (if x < a then 1 else 0) + smallerCount a xs ∧
        largerCount a (x :: xs) = (if a < x then 1 else 0) + largerCount a xs := by
      by_cases h₁ : x < a <;> by_cases h₂ : a < x <;>
        simp [smallerCount, largerCount, h₁, h₂, Nat.add_comm]
    simp only [(counts high).1, (counts low).1, (counts high).2, (counts low).2]
    change _ = _ + (interiorWeight low high x + interiorSaving low high xs)
    have point := point_identity low high x h
    omega

omit [LinearOrder α] in
private theorem core_perm (a b : α) (m : List α) :
    (a :: (m ++ [b])).Perm (b :: (m ++ [a])) := by
  have ha : (m ++ [a]).Perm (a :: m) := by simp
  have hb : (m ++ [b]).Perm (b :: m) := by simp
  exact (hb.cons a).trans ((List.Perm.swap b a m).trans (ha.symm.cons b))

private theorem retain_outside {u v : List α} (p : u.Perm v) {s : ℕ}
    (h : listInversions u = listInversions v + s) (pre post : List α) :
    listInversions (pre ++ u ++ post) = listInversions (pre ++ v ++ post) + s := by
  have prepend_eq (xs : List α) : listInversions (xs ++ u) = listInversions (xs ++ v) + s := by
    induction xs with
    | nil => simpa using h
    | cons x xs ih =>
      have hc : smallerCount x (xs ++ u) = smallerCount x (xs ++ v) :=
        ((p.append_left xs).filter (fun b => b < x)).length_eq
      simp only [List.cons_append, listInversions, hc, ih]
      omega
  induction post using List.reverseRecOn with
  | nil => simpa using prepend_eq pre
  | append_singleton t x ih =>
    have hc := largerCount_perm x ((p.append_left pre).append_right t)
    simp only [← List.append_assoc, listInversions_append_singleton, hc, ih]
    omega

/-- On the given physical slots the swap itself removes one inversion. The
remaining saving is charged to the intervening slot values. -/
theorem crossed_pair_inversions (pre m post : List α) (a b : α) (h : b < a) :
    listInversions (pre ++ (a :: (m ++ [b])) ++ post) =
      listInversions (pre ++ (b :: (m ++ [a])) ++ post) + (1 + interiorSaving b a m) := by
  apply retain_outside (core_perm a b m)
  have hab : ¬a < b := not_lt_of_gt h
  have ha : smallerCount a (m ++ [b]) = smallerCount a m + 1 := by
    simp [smallerCount, List.filter_append, h]
  have hb : smallerCount b (m ++ [a]) = smallerCount b m := by
    simp [smallerCount, List.filter_append, hab]
  simp only [listInversions, listInversions_append_singleton, ha, hb]
  have counts := middle_counts b a h m
  omega

structure GateResult (α : Type*) where
  output : List α
  exchanges : ℕ
  saving : ℕ

/-- Compare slots containing a and b in physical order. The output is the
updated list. Only a true reversed pair increments the exchange counter. -/
def comparePair (pre m post : List α) (a b : α) : GateResult α :=
  if b < a then ⟨pre ++ (b :: (m ++ [a])) ++ post, 1, interiorSaving b a m⟩
  else ⟨pre ++ (a :: (m ++ [b])) ++ post, 0, 0⟩

theorem comparePair_then_insertion (pre m post : List α) (a b : α) :
    let step := comparePair pre m post a b
    step.exchanges + (insertionExecution step.output).2 + step.saving =
      (insertionExecution (pre ++ (a :: (m ++ [b])) ++ post)).2 := by
  by_cases h : b < a
  · simp only [comparePair, h, ite_true, insertionExecution_count]
    have fact := crossed_pair_inversions pre m post a b h
    omega
  · simp [comparePair, h, insertionExecution_count]

/-- Number of slots before the left endpoint, and strictly between endpoints.
Thus the right endpoint is at left + 1 + between. -/
structure SlotPair where
  left : ℕ
  between : ℕ
  deriving DecidableEq

/-- A pair outside the array leaves it untouched. In-range gates use the
current physical keys, even if a previous gate has already moved an endpoint. -/
def runGate (g : SlotPair) (xs : List α) : GateResult α :=
  match xs.drop g.left with
  | [] => ⟨xs, 0, 0⟩
  | a :: rest =>
    match rest.drop g.between with
    | [] => ⟨xs, 0, 0⟩
    | b :: post => comparePair (xs.take g.left) (rest.take g.between) post a b

theorem runGate_then_insertion (g : SlotPair) (xs : List α) :
    let step := runGate g xs
    step.exchanges + (insertionExecution step.output).2 + step.saving =
      (insertionExecution xs).2 := by
  cases h₁ : xs.drop g.left with
  | nil => simp [runGate, h₁]
  | cons a rest =>
    cases h₂ : rest.drop g.between with
    | nil => simp [runGate, h₁, h₂]
    | cons b post =>
      have tail_eq := List.take_append_drop g.between rest
      rw [h₂] at tail_eq
      have input_eq := List.take_append_drop g.left xs
      rw [h₁, ← tail_eq] at input_eq
      have cert := comparePair_then_insertion (xs.take g.left) (rest.take g.between) post a b
      simp only [runGate, h₁, h₂]
      convert cert using 1
      simp_all [List.append_assoc]

/-- Execute pairs in the listed order, accumulating the real successful
exchanges and the interior saving from the state just before each gate. -/
def runLayer : List SlotPair → List α → GateResult α
  | [], xs => ⟨xs, 0, 0⟩
  | g :: gs, xs =>
    let first := runGate g xs
    let rest := runLayer gs first.output
    ⟨rest.output, first.exchanges + rest.exchanges, first.saving + rest.saving⟩

/-- For every list of position pairs, including every disjoint layer, its
exchange count plus the following insertion shifts saves exactly the sum of
the intervening-key corrections compared with inserting the original array. -/
theorem layer_then_insertion (gates : List SlotPair) (xs : List α) :
    let r := runLayer gates xs
    r.exchanges + (insertionExecution r.output).2 + r.saving =
      (insertionExecution xs).2 := by
  induction gates generalizing xs with
  | nil => simp [runLayer]
  | cons g gs ih =>
    have rest := ih (runGate g xs).output
    have first := runGate_then_insertion g xs
    dsimp only at rest first
    dsimp only [runLayer]
    omega

/-- With distinct endpoint and intervening keys the saving is twice the
number of interior slots whose key lies strictly between the endpoint keys. -/
theorem interiorSaving_distinct (low high : α) (m : List α)
    (hl : low ∉ m) (hh : high ∉ m) :
    interiorSaving low high m =
      2 * (m.filter (fun x => low < x ∧ x < high)).length := by
  induction m with
  | nil => simp [interiorSaving]
  | cons x m ih =>
    have hxl : x ≠ low := fun h => hl (by simp [h])
    have hxh : x ≠ high := fun h => hh (by simp [h])
    have tail := ih (fun hm => hl (List.mem_cons_of_mem _ hm))
                    (fun hm => hh (List.mem_cons_of_mem _ hm))
    by_cases hx : low < x ∧ x < high
    · simpa [interiorSaving, interiorWeight, hx, hxl, hxh, Nat.mul_add,
          Nat.add_comm] using tail
    · simpa [interiorSaving, interiorWeight, hx, hxl, hxh] using tail

end Shellsort.PairLayerInsertion
