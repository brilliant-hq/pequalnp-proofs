import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_819

open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (l : List α) (b d : α) (j : ℕ) :
    (l ++ [b]).getD j d = if j < l.length then l.getD j d else if j = l.length then b else d := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, ← List.getD_eq_getElem?_getD]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem sum_fold (f : ℕ → ℕ × ℕ) (l : List ℕ) : ∀ v : ℕ × ℕ,
    l.foldl (fun (v : ℕ × ℕ) i => (v.1 + (f i).1, v.2 + (f i).2)) v =
      (v.1 + (l.map fun i => (f i).1).sum, v.2 + (l.map fun i => (f i).2).sum) := by
  induction l with
  | nil => intro v; simp
  | cons a l ih =>
    intro v
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    ext <;> simp <;> omega

def Inv (X Y : List Bool) (P : List (ℕ × ℕ)) : Prop :=
  ∀ j : ℕ, (X.getD j false = false → Y.getD j false = true → 0 < (P.getD j (0,0)).1) ∧
    (X.getD j false = true → Y.getD j false = false → 0 < (P.getD j (0,0)).2)

theorem le_sum {l : List ℕ} {f : ℕ → ℕ} {i : ℕ} (hi : i ∈ l) : f i ≤ (l.map f).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hi)

theorem main (inst : DecidableEq GateOp) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (X Y : List Bool) (P : List (ℕ × ℕ)), X.length = P.length → Y.length = P.length →
      Inv X Y P →
      Inv (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) X)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) Y)
        (gs.foldl (fun (a : List (ℕ × ℕ)) g =>
          let s := g.inputs.foldl (fun (v : ℕ × ℕ) i =>
            let t := a.getD i (0,0)
            (v.1+t.1,v.2+t.2)) (0,0)
          let h := (g.inputs.head?.map (fun i => a.getD i (0,0))).getD (0,0)
          a ++ [if g.op = GateOp.not then (h.2,h.1) else s]) P) := by
  induction gs with
  | nil => intro X Y P _ _ h; exact h
  | cons g gs ih =>
    intro X Y P hX hY hI
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hX]
    · simp [hY]
    have hs := sum_fold (fun i => P.getD i (0,0)) g.inputs (0,0)
    intro j
    rw [getD_snoc, getD_snoc, getD_snoc, hX, hY]
    by_cases h1 : j < P.length
    · rw [if_pos h1, if_pos h1, if_pos h1]; exact hI j
    rw [if_neg h1, if_neg h1, if_neg h1]
    by_cases h2 : j = P.length
    swap
    · rw [if_neg h2, if_neg h2, if_neg h2]; simp
    rw [if_pos h2, if_pos h2, if_pos h2]
    rw [hs]
    simp only [zero_add]
    rcases hg g (List.mem_cons_self) with ho | ho | ho
    · rw [if_neg (by rw [ho]; intro h; cases h), ho]
      simp only [GateOp.eval]
      constructor
      · intro hx hy
        rw [List.all_eq_false] at hx
        obtain ⟨a, ha, hax⟩ := hx
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        rw [List.all_eq_true] at hy
        have hyi := hy _ (List.mem_map_of_mem hi)
        simp only [id] at hax hyi
        have := (hI i).1 (by simpa using hax) hyi
        exact lt_of_lt_of_le this (le_sum (f := fun i => (P.getD i (0,0)).1) hi)
      · intro hx hy
        rw [List.all_eq_false] at hy
        obtain ⟨a, ha, hay⟩ := hy
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        rw [List.all_eq_true] at hx
        have hxi := hx _ (List.mem_map_of_mem hi)
        simp only [id] at hay hxi
        have := (hI i).2 hxi (by simpa using hay)
        exact lt_of_lt_of_le this (le_sum (f := fun i => (P.getD i (0,0)).2) hi)
    · rw [if_neg (by rw [ho]; intro h; cases h), ho]
      simp only [GateOp.eval]
      constructor
      · intro hx hy
        rw [List.any_eq_true] at hy
        obtain ⟨a, ha, hay⟩ := hy
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        rw [List.any_eq_false] at hx
        have hxi := hx _ (List.mem_map_of_mem hi)
        simp only [id] at hay hxi
        have := (hI i).1 (by simpa using hxi) hay
        exact lt_of_lt_of_le this (le_sum (f := fun i => (P.getD i (0,0)).1) hi)
      · intro hx hy
        rw [List.any_eq_true] at hx
        obtain ⟨a, ha, hax⟩ := hx
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        rw [List.any_eq_false] at hy
        have hyi := hy _ (List.mem_map_of_mem hi)
        simp only [id] at hax hyi
        have := (hI i).2 hax (by simpa using hyi)
        exact lt_of_lt_of_le this (le_sum (f := fun i => (P.getD i (0,0)).2) hi)
    · rw [if_pos ho, ho]
      simp only [GateOp.eval]
      cases hin : g.inputs with
      | nil => simp
      | cons i rest =>
        simp only [List.map_cons, List.headD_cons, List.head?_cons, Option.map_some,
          Option.getD_some]
        constructor
        · intro hx hy
          exact (hI i).2 (by simpa using hx) (by simpa using hy)
        · intro hx hy
          exact (hI i).1 (by simpa using hx) (by simpa using hy)

end PEqualNP.Outside.L_lib_819

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_819 in
theorem PEqualNP.Outside.L_lib_819 : ∀ (N : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N → Bool),
  PEqualNP.MetaComplexity.FanInTwo C →
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let seed := List.ofFn (fun i : Fin N =>
    (((if x i = false ∧ y i = true then 1 else 0),
     (if x i = true ∧ y i = false then 1 else 0)) : Nat × Nat))
  let paths := C.gates.foldl (fun (a : List (Nat × Nat)) g =>
    let s := g.inputs.foldl (fun (v : Nat × Nat) i =>
      let t := a.getD i (0,0)
      (v.1+t.1,v.2+t.2)) (0,0)
    let h := (g.inputs.head?.map (fun i => a.getD i (0,0))).getD (0,0)
    a ++ [if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else s]) seed
  let X := C.wires (List.ofFn x)
  let Y := C.wires (List.ofFn y)
  ∀ j : Nat, (X.getD j false = false → Y.getD j false = true → 0 < (paths.getD j (0,0)).1) ∧
    (X.getD j false = true → Y.getD j false = false → 0 < (paths.getD j (0,0)).2) := by
  intro N C x y hC seed paths X Y
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have hbase : Inv (List.ofFn x) (List.ofFn y) seed := by
    intro j
    by_cases hj : j < N
    · have e1 : (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
        simp [List.getD_eq_getElem?_getD, hj]
      have e2 : (List.ofFn y).getD j false = y ⟨j, hj⟩ := by
        simp [List.getD_eq_getElem?_getD, hj]
      have e3 : seed.getD j (0,0) = ((if x ⟨j, hj⟩ = false ∧ y ⟨j, hj⟩ = true then 1 else 0),
          (if x ⟨j, hj⟩ = true ∧ y ⟨j, hj⟩ = false then 1 else 0)) := by
        simp [seed, List.getD_eq_getElem?_getD, hj]
      rw [e1, e2, e3]
      constructor
      · intro h1 h2; simp [h1, h2]
      · intro h1 h2; simp [h1, h2]
    · have e1 : (List.ofFn x).getD j false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
      have e2 : (List.ofFn y).getD j false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
      rw [e1, e2]
      simp
  exact main PEqualNP.MetaComplexity.NestedCover.gateOpDecEq C.gates hg (List.ofFn x) (List.ofFn y) seed (by simp [seed])
    (by simp [seed]) hbase
