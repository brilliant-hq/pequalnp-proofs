import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

namespace PEqualNP.Outside.L_meta_32049_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_getD (gates : List Gate) : ∀ (w : List Bool) (j : ℕ), j < w.length →
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false
      = w.getD j false := by
  induction gates with
  | nil => intro w j _; rfl
  | cons g gs ih =>
    intro w j hj
    rw [List.foldl_cons, ih _ j (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem wires_input (C : Circuit) (x : Fin 7 → Bool) (j : Fin 7) :
    (C.wires (List.ofFn x)).getD j.val false = x j := by
  unfold Circuit.wires
  rw [foldl_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]
  fin_cases j <;> rfl

end PEqualNP.Outside.L_meta_32049_aux

theorem PEqualNP.Outside.L_meta_32049 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
  (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD h false = true) →
  7 ≤ h) := by
  intro C i k h hf hs he h0 hu hor hand hik hk hh hne hlt hx
  by_contra hcon
  have h7 : h < 7 := by omega
  obtain ⟨x, hx0, hx1, hx6, hw⟩ := hx
  have hcases : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · have := PEqualNP.Outside.L_meta_32049_aux.wires_input C x 1
    simp only [Fin.val_one] at this
    rw [this, hx1] at hw
    exact Bool.false_ne_true hw
  · exact PEqualNP.Outside.L_meta_32045 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32046 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32047 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32048 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · have := PEqualNP.Outside.L_meta_32049_aux.wires_input C x 6
    have e : ((6 : Fin 7) : ℕ) = 6 := rfl
    rw [e] at this
    rw [this, hx6] at hw
    exact Bool.false_ne_true hw
