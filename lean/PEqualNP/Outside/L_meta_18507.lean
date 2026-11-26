import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18507

open PEqualNP.CircuitLowerBounds

def WF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl WF x := rfl

def shift (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (· + k)⟩

theorem getD_shift (P V : List Bool) (i : ℕ) : (P ++ V).getD (i + P.length) false = V.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  congr 2; omega

theorem fold_shift (P : List Bool) (gs : List Gate) :
    ∀ V : List Bool, (gs.map (shift P.length)).foldl WF (P ++ V) = P ++ gs.foldl WF V := by
  induction gs with
  | nil => intro V; rfl
  | cons g gs ih =>
    intro V
    simp only [List.map_cons, List.foldl_cons]
    have : WF (P ++ V) (shift P.length g) = P ++ WF V g := by
      simp only [WF, shift, List.map_map, Function.comp_def, getD_shift, List.append_assoc]
    rw [this, ih]

theorem getD_pre (L A : List Bool) (i : ℕ) (h : i < L.length) : (L ++ A).getD i false = L.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem fold_front (L : List Bool) (gs : List Gate) (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < L.length) :
    ∀ A : List Bool, gs.foldl WF (L ++ A) =
      L ++ A ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => L.getD i false)) := by
  induction gs with
  | nil => intro A; simp
  | cons g gs ih =>
    intro A
    simp only [List.foldl_cons, List.map_cons]
    have e : WF (L ++ A) g = L ++ (A ++ [g.op.eval (g.inputs.map fun i => L.getD i false)]) := by
      simp only [WF, List.append_assoc]
      congr 4
      apply List.map_congr_left
      intro i hi
      exact getD_pre L A i (h g (by simp) i hi)
    rw [e, ih (fun g hg => h g (by simp [hg]))]
    simp

end PEqualNP.Outside.L_meta_18507

open PEqualNP.Outside.L_meta_18507 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18507 : ∀ (n s : ℕ) (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)), (∀ a b, H a b = H b a) → (∀ a, H a a = false) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ (∀ a : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = a)) = false) ∧ (∀ a b : Fin n, a ≠ b → C.eval (List.ofFn fun i : Fin n => decide (i = a ∨ i = b)) = H a b)) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => H u (π.symm v)) (n + s) := by
  intro n s H π hsym hloop ⟨C, hm, hs, h1, h2⟩
  let Z : List Gate := (List.finRange n).map (fun i => ⟨GateOp.or, [i.val, n + (π i).val]⟩)
  let D : Circuit := ⟨Z ++ C.gates.map (shift (2 * n)), C.output + 2 * n⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      simp
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hm g' hg').1, by simpa [shift] using (hm g' hg').2⟩
  · simp only [D, Z, Circuit.size, List.length_append, List.length_map, List.length_finRange]
    simp only [Circuit.size] at hs
    omega
  · intro u v
    let L : List Bool := PEqualNP.Represents.oneEach u v
    have hL : L.length = 2 * n := by simp [L, PEqualNP.Represents.oneEach]; omega
    have hx : ∀ i : Fin n, L.getD i.val false = decide (i = u) := by
      intro i
      simp only [L, PEqualNP.Represents.oneEach]
      rw [getD_pre _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hy : ∀ j : Fin n, L.getD (n + j.val) false = decide (j = v) := by
      intro j
      simp only [L, PEqualNP.Represents.oneEach]
      have := getD_shift (List.ofFn fun i : Fin n => decide (i = u)) (List.ofFn fun j : Fin n => decide (j = v)) j.val
      rw [List.length_ofFn] at this
      rw [Nat.add_comm, this]
      simp [List.getD_eq_getElem?_getD]
    have hfront := fold_front L Z (by
      intro g hg i hi
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
      simp at hi
      rcases hi with rfl | rfl <;> omega) []
    simp only [List.append_nil] at hfront
    let zv : List Bool := Z.map (fun g => g.op.eval (g.inputs.map fun i => L.getD i false))
    have hzv : zv = List.ofFn fun i : Fin n => decide (i = u ∨ i = π.symm v) := by
      simp only [zv, Z, List.map_map, Function.comp_def]
      rw [List.ofFn_eq_map]
      apply List.map_congr_left
      intro i _
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
      rw [hx i, hy (π i)]
      have : (π i = v) ↔ (i = π.symm v) := Equiv.apply_eq_iff_eq_symm_apply π
      by_cases h3 : i = u <;> by_cases h4 : i = π.symm v <;> simp_all
    have hw : D.wires L = L ++ C.wires zv := by
      rw [wires_eq, wires_eq]
      simp only [D, List.foldl_append]
      rw [hfront]
      rw [show 2 * n = L.length from hL.symm]
      exact fold_shift L C.gates zv
    show (D.wires L).getD (C.output + 2 * n) false = H u (π.symm v)
    rw [hw, show 2 * n = L.length from hL.symm, getD_shift]
    change C.eval zv = H u (π.symm v)
    rw [hzv]
    by_cases huv : u = π.symm v
    · rw [← huv, hloop u]
      have := h1 u
      simpa using this
    · exact h2 u (π.symm v) huv
