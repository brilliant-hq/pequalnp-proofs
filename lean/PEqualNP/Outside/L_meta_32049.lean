import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

namespace PEqualNP.Outside.L_meta_32049_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_prefix (gs : List Gate) : ∀ (x : List Bool), ∃ s : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = x ++ s := by
  induction gs with
  | nil => intro x; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro x
    obtain ⟨s, hs⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: s, ?_⟩
    rw [List.foldl_cons, hs]
    simp

theorem wires_input (C : Circuit) (x : Fin 7 → Bool) (j : ℕ) (hj : j < 7) :
    (C.wires (List.ofFn x)).getD j false = x ⟨j, hj⟩ := by
  obtain ⟨s, hs⟩ := foldl_prefix C.gates (List.ofFn x)
  unfold Circuit.wires
  rw [hs]
  have hl : j < (List.ofFn x).length := by simp [hj]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, List.getElem?_ofFn]
  simp [hj]

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
  by_contra hlt7
  push Not at hlt7
  obtain ⟨x, hx0, hx1, hx6, hw⟩ := hx
  interval_cases h
  · exact hne rfl
  · rw [PEqualNP.Outside.L_meta_32049_aux.wires_input C x 1 (by decide)] at hw
    exact absurd hw (by simpa using hx1)
  · exact PEqualNP.Outside.L_meta_32045 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32046 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32047 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32048 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · rw [PEqualNP.Outside.L_meta_32049_aux.wires_input C x 6 (by decide)] at hw
    exact absurd hw (by simpa using hx6)
