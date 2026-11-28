import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L27130
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

namespace PEqualNP.Outside.L_meta_32049

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32045

theorem wire_lt (C : Circuit) (x : Fin 7 → Bool) (n : ℕ) (hn : n < 7) :
    (C.wires (List.ofFn x)).getD n false = x ⟨n, hn⟩ := by
  have hlen : (List.ofFn x).length = 7 := List.length_ofFn
  rw [wires_eq, fold_prefix C.gates (List.ofFn x) n (by rw [hlen]; exact hn),
    getD_ofFn x n hn]

theorem wire_input_ne (C : Circuit) (x : Fin 7 → Bool) (n : ℕ) (hn : n < 7)
    (hx : x ⟨n, hn⟩ = false) (hw : (C.wires (List.ofFn x)).getD n false = true) : False := by
  rw [wire_lt C x n hn, hx] at hw
  simp at hw

end PEqualNP.Outside.L_meta_32049

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
  intro C i k h hf hsize hcorrect h0i honly hior hkand hik hk7i hhi hne0 hlt hex
  obtain ⟨x, hx0, hx1, hx6, hxw⟩ := hex
  by_contra hcon
  have hc : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : 1 < 7 := by omega
    have hx1' : x ⟨1, hn⟩ = false := hx1
    exact PEqualNP.Outside.L_meta_32049.wire_input_ne C x 1 hn hx1' hxw
  · exact PEqualNP.Outside.L_meta_32045 C i k hf hsize hcorrect h0i honly hior hkand hik hk7i hhi
      ⟨x, hx0, hx1, hx6, hxw⟩
  · exact PEqualNP.Outside.L_meta_32046 C i k hf hsize hcorrect h0i honly hior hkand hik hk7i hhi
      ⟨x, hx0, hx1, hx6, hxw⟩
  · exact PEqualNP.Outside.L_meta_32047 C i k hf hsize hcorrect h0i honly hior hkand hik hk7i hhi
      ⟨x, hx0, hx1, hx6, hxw⟩
  · exact PEqualNP.Outside.L_meta_32048 C i k hf hsize hcorrect h0i honly hior hkand hik hk7i hhi
      ⟨x, hx0, hx1, hx6, hxw⟩
  · have hn : 6 < 7 := by omega
    have hx6' : x ⟨6, hn⟩ = false := hx6
    exact PEqualNP.Outside.L_meta_32049.wire_input_ne C x 6 hn hx6' hxw
