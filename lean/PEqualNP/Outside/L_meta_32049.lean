import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

namespace PEqualNP.Outside.L_meta_32049_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false
      = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hj

theorem wire_input (C : Circuit) (x : Fin 7 → Bool) (j : Fin 7) :
    (C.wires (List.ofFn x)).getD j.val false = x j := by
  unfold Circuit.wires
  rw [foldl_getD_lt _ _ _ (by simp)]
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
  intro C i k h hfan hsize heval h0 huniq hor hand hik hk hh hne hlt hex
  by_contra hcon
  have h7 : h < 7 := Nat.lt_of_not_le hcon
  obtain ⟨x, x0, x1, x6, hw⟩ := hex
  interval_cases h
  · exact hne rfl
  · have e1 : (C.wires (List.ofFn x)).getD 1 false = x 1 :=
      PEqualNP.Outside.L_meta_32049_aux.wire_input C x 1
    rw [e1, x1] at hw
    exact Bool.noConfusion hw
  · exact PEqualNP.Outside.L_meta_32045 C i k hfan hsize heval h0 huniq hor hand hik hk hh
      ⟨x, x0, x1, x6, hw⟩
  · exact PEqualNP.Outside.L_meta_32046 C i k hfan hsize heval h0 huniq hor hand hik hk hh
      ⟨x, x0, x1, x6, hw⟩
  · exact PEqualNP.Outside.L_meta_32047 C i k hfan hsize heval h0 huniq hor hand hik hk hh
      ⟨x, x0, x1, x6, hw⟩
  · exact PEqualNP.Outside.L_meta_32048 C i k hfan hsize heval h0 huniq hor hand hik hk hh
      ⟨x, x0, x1, x6, hw⟩
  · have e6 : (C.wires (List.ofFn x)).getD 6 false = x 6 :=
      PEqualNP.Outside.L_meta_32049_aux.wire_input C x 6
    rw [e6, x6] at hw
    exact Bool.noConfusion hw
