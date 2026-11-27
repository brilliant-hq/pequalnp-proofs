import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFnN (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 4000000 in
theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b5) || (b6 && b7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1207

theorem PEqualNP.Outside.L_meta_1207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1207.C0, PEqualNP.Outside.L_meta_1207.ok0, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1207.ofFnN]; exact PEqualNP.Outside.L_meta_1207.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
