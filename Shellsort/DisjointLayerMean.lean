import Shellsort.PairSlotUniformMean
import Shellsort.PairLayerCostFormula

namespace Shellsort.DisjointLayerMean
open PairLayerInsertion PairSlotUniformMean
noncomputable section

/-- A physical gate identified by splitting a fixed list of distinct slots. -/
structure Gate {n : ℕ} (layout : List (Fin n)) where
  l : Fin n
  r : Fin n
  pre : List (Fin n)
  mid : List (Fin n)
  post : List (Fin n)
  split : layout = pre ++ (l :: (mid ++ [r])) ++ post

def Gate.physical {n : ℕ} {layout : List (Fin n)} (g : Gate layout) : SlotPair :=
  ⟨g.pre.length,g.mid.length⟩

private theorem gate_separation {n : ℕ} {layout : List (Fin n)} (nd : layout.Nodup)
    (g : Gate layout) :
    g.l ≠ g.r ∧
    ∀ i ∈ g.pre ++ g.mid ++ g.post, i ≠ g.l ∧ i ≠ g.r := by
  rw [g.split] at nd
  simp only [List.nodup_append', List.nodup_cons, List.mem_append,
    not_or, List.disjoint_iff_ne, List.mem_cons] at nd
  constructor
  · grind
  · intro i hi
    simp only [List.mem_append] at hi
    grind

/-- For every used slot record the partner and whether it holds the smaller key. -/
abbrev State (n : ℕ) := Fin n → Option (Fin n × Bool)

def value {n : ℕ} (s : State n) (p : RankPlacement n) (i : Fin n) : Fin n :=
  match s i with
  | none => p.symm i
  | some (j,b) => if b then min (p.symm i) (p.symm j) else max (p.symm i) (p.symm j)

def Sound {n : ℕ} (s : State n) : Prop :=
  ∀ i j b, s i = some (j,b) → i ≠ j ∧ s j ≠ none

def afterGate {n : ℕ} (s : State n) (l r : Fin n) (i : Fin n) : Option (Fin n × Bool) :=
  if i=l then some (r,true) else if i=r then some (l,false) else s i

private theorem after_sound {n : ℕ} {s : State n} (ok : Sound s) {l r : Fin n}
    (lr : l ≠ r) : Sound (afterGate s l r) := by
  intro i j b hi
  by_cases hl : i=l
  · subst i
    simp [afterGate] at hi
    obtain ⟨rfl,rfl⟩ := hi
    simp [afterGate,lr,lr.symm]
  by_cases hr : i=r
  · subst i
    simp [afterGate,hl] at hi
    obtain ⟨rfl,rfl⟩ := hi
    simp [afterGate,lr.symm]
  have res := ok i j b (by simpa [afterGate,hl,hr] using hi)
  exact ⟨res.1,by by_cases jl : j=l <;> by_cases jr : j=r <;> simp_all [afterGate]⟩

private def three {n : ℕ} (a b c : Fin n) (ab : a≠b) (ca : c≠a) (cb : c≠b) :
    Fin 3 ↪ Fin n :=
  ⟨![a,b,c],by intro i j e; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm ab, Ne.symm ca, Ne.symm cb]⟩

private def four {n : ℕ} (a b c d : Fin n) (ab : a≠b) (ca : c≠a) (cb : c≠b)
    (da : d≠a) (db : d≠b) (cd : c≠d) : Fin 4 ↪ Fin n :=
  ⟨![a,b,c,d],by
    intro i j e; fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm ab, Ne.symm ca, Ne.symm cb, Ne.symm da, Ne.symm db, Ne.symm cd]⟩

private theorem exists_source {n : ℕ} {s : State n} (ok : Sound s) {l r i : Fin n}
    (lr : l≠r) (il : i≠l) (ir : i≠r) (hl : s l=none) (hr : s r=none) :
    ∃ z : Source l r, ∀ p, key p z = value s p i := by
  cases hh : s i with
  | none => exact ⟨.rawSlot (three l r i lr il ir) rfl rfl,fun p => by simp only [key,value,hh]; rfl⟩
  | some v =>
    obtain ⟨j,b⟩ := v
    have safe := ok _ _ _ hh
    have jl : j≠l := by rintro rfl; exact safe.2 hl
    have jr : j≠r := by rintro rfl; exact safe.2 hr
    exact ⟨.pairedSlot (four l r i j lr il ir jl jr safe.1) rfl rfl b,fun p => by
      simp only [key,value,hh]; rfl⟩

private theorem gate_output {n : ℕ} {layout : List (Fin n)} (nd : layout.Nodup)
    (g : Gate layout) (s : State n) (hl : s g.l=none) (hr : s g.r=none)
    (p : RankPlacement n) :
    (runGate g.physical (layout.map (value s p))).output =
      layout.map (value (afterGate s g.l g.r) p) := by
  obtain ⟨lr,sep⟩ := gate_separation nd g
  have unchanged (xs : List (Fin n)) (inside : ∀ i ∈ xs, i ∈ g.pre ++ g.mid ++ g.post) :
      xs.map (value (afterGate s g.l g.r) p) = xs.map (value s p) := by
    apply List.map_congr_left
    intro i hi
    have h := sep i (inside i hi)
    simp [value,afterGate,h.1,h.2]
  have pr := unchanged g.pre (by intro i hi; simp [hi])
  have mi := unchanged g.mid (by intro i hi; simp [hi])
  have po := unchanged g.post (by intro i hi; simp [hi])
  rw [congrArg (List.map (value s p)) g.split,congrArg (List.map (value (afterGate s g.l g.r) p)) g.split]
  simp only [List.map_append,List.map_cons,List.map_nil,pr,mi,po]
  have gate := run_at_pair (g.pre.map (value s p)) (g.mid.map (value s p)) (g.post.map (value s p))
    (value s p g.l) (value s p g.r)
  simp only [List.length_map] at gate
  unfold Gate.physical
  rw [gate]
  by_cases h : p.symm g.r < p.symm g.l
  · simp [comparePair,value,afterGate,lr.symm,hl,hr,h,min_eq_right h.le,max_eq_right h.le]
  · simp [comparePair,value,afterGate,lr.symm,hl,hr,h,min_eq_left (le_of_not_gt h),
      max_eq_left (le_of_not_gt h)]

private theorem gate_saving {n : ℕ} {layout : List (Fin n)} (nd : layout.Nodup)
    (g : Gate layout) (s : State n) (ok : Sound s)
    (hl : s g.l=none) (hr : s g.r=none) :
    uniformAverage (fun p : RankPlacement n =>
      ((runGate g.physical (layout.map (value s p))).saving : ℝ)) = g.mid.length/3 := by
  obtain ⟨lr,sep⟩ := gate_separation nd g
  have supply (x : {i // i ∈ g.mid}) := exists_source ok lr
    (sep x.val (by simp [x.property])).1 (sep x.val (by simp [x.property])).2 hl hr
  let zs := g.mid.attach.map fun i => Classical.choose (supply i)
  have eq (p : RankPlacement n) : zs.map (key p) = g.mid.map (value s p) := by
    simp only [zs,List.map_map]
    rw [← List.attach_map_val (l := g.mid) (f := value s p)]
    apply List.map_congr_left
    intro i _
    exact Classical.choose_spec (supply i) p
  have cost := mean_saving zs (fun p => g.pre.map (value s p)) (fun p => g.post.map (value s p))
  simp only [eq] at cost
  have width : zs.length = g.mid.length := by simp [zs]
  rw [width] at cost
  convert cost using 2
  funext p
  rw [congrArg (List.map (value s p)) g.split]
  simp only [List.map_append,List.map_cons,List.map_nil]
  have at_pair := run_at_pair (g.pre.map (value s p)) (g.mid.map (value s p)) (g.post.map (value s p))
    (value s p g.l) (value s p g.r)
  simp only [List.length_map] at at_pair
  unfold Gate.physical
  rw [at_pair]
  simp only [value,hl,hr]

/-- No physical slot is an endpoint of two distinct gates in the sequence. -/
def DisjointGates {n : ℕ} {layout : List (Fin n)} (gs : List (Gate layout)) : Prop :=
  gs.Pairwise fun first later =>
    later.l ≠ first.l ∧ later.l ≠ first.r ∧ later.r ≠ first.l ∧ later.r ≠ first.r

private theorem layer_saving_general {n : ℕ} {layout : List (Fin n)} (nd : layout.Nodup)
    (gs : List (Gate layout)) (s : State n) (ok : Sound s) (ds : DisjointGates gs)
    (free : ∀ g ∈ gs, s g.l=none ∧ s g.r=none) :
    uniformAverage (fun p : RankPlacement n =>
      ((runLayer (gs.map Gate.physical) (layout.map (value s p))).saving : ℝ)) =
      ((gs.map fun g => g.mid.length).sum:ℝ)/3 := by
  induction gs generalizing s with
  | nil => simp [runLayer,uniformAverage_const]
  | cons g gs ih =>
    obtain ⟨never,dt⟩ := List.pairwise_cons.mp ds
    obtain ⟨hl,hr⟩ := free g (by simp)
    have updated := after_sound ok (gate_separation nd g).1
    have later (k : Gate layout) (hk : k ∈ gs) :
        afterGate s g.l g.r k.l = none ∧ afterGate s g.l g.r k.r = none := by
      obtain ⟨a,b,c,d⟩ := never k hk
      simpa [afterGate,a,b,c,d] using free k (List.mem_cons_of_mem _ hk)
    have rest := ih _ updated dt later
    simp only [List.map_cons,runLayer,List.sum_cons,Nat.cast_add,gate_output nd g s hl hr]
    rw [uniformAverage_add,gate_saving nd g s ok hl hr,rest]
    ring

theorem layer_saving {n : ℕ} {layout : List (Fin n)} (nd : layout.Nodup)
    (gs : List (Gate layout)) (ds : DisjointGates gs) :
    uniformAverage (fun p : RankPlacement n =>
      ((runLayer (gs.map Gate.physical) (layout.map p.symm)).saving : ℝ)) =
      ((gs.map fun g => g.mid.length).sum:ℝ)/3 :=
  layer_saving_general nd gs (fun _ => none) (by intro i j b; simp) ds (by simp)

/-- End-to-end expected number of successful gate exchanges plus executed
final insertion shifts on the natural array of a uniform random permutation. -/
theorem disjoint_layer_mean (n : ℕ) (gs : List (Gate (List.finRange n)))
    (ds : DisjointGates gs) :
    uniformAverage (fun p : RankPlacement n =>
      let out := runLayer (gs.map Gate.physical) ((List.finRange n).map p.symm)
      ((out.exchanges + (insertionExecution out.output).2 : ℕ) : ℝ)) =
    (n:ℝ)*((n:ℝ)-1)/4 - ((gs.map fun g => g.mid.length).sum:ℝ)/3 :=
  PairLayerCostFormula.layer_cost_of_saving n _ _ (layer_saving (List.nodup_finRange n) gs ds)

#print axioms disjoint_layer_mean
end
end Shellsort.DisjointLayerMean
