import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

theorem PEqualNP.Outside.L_meta_32049 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
  (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD h false = true) →
  7 ≤ h := by
  intro C i k h hf hs he h0 hu hor hand hik hk hh hne hlt hx
  by_contra hc
  have h7 : h < 7 := by omega
  have hinp : ∀ (x : Fin 7 → Bool) (n : ℕ) (hn : n < 7),
      (C.wires (List.ofFn x)).getD n false = x ⟨n, hn⟩ := by
    intro x n hn
    rw [PEqualNP.Outside.L_meta_32045.wires_eq,
      PEqualNP.Outside.L_meta_32045.fold_prefix _ _ n (by simpa using hn)]
    exact PEqualNP.Outside.L_meta_32045.getD_ofFn x n hn
  obtain ⟨x, hx0, hx1, hx6, hw⟩ := hx
  have hcases : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hinp x 1 (by omega)] at hw
    have : x ⟨1, by omega⟩ = x 1 := rfl
    simp [this, hx1] at hw
  · exact PEqualNP.Outside.L_meta_32045 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32046 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32047 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_32048 C i k hf hs he h0 hu hor hand hik hk hh ⟨x, hx0, hx1, hx6, hw⟩
  · rw [hinp x 6 (by omega)] at hw
    have : x ⟨6, by omega⟩ = x 6 := rfl
    simp [this, hx6] at hw
