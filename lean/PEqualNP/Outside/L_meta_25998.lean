import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25998_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  { gates := [ ⟨GateOp.and, [3, 4]⟩
             , ⟨GateOp.not, [6]⟩
             , ⟨GateOp.and, [1, 9]⟩
             , ⟨GateOp.or,  [5, 6]⟩
             , ⟨GateOp.and, [2, 11]⟩
             , ⟨GateOp.or,  [10, 12]⟩
             , ⟨GateOp.or,  [8, 13]⟩
             , ⟨GateOp.or,  [0, 14]⟩
             ]
  , output := 15 }

end PEqualNP.Outside.L_meta_25998_aux

theorem PEqualNP.Outside.L_meta_25998 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 11, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_25998_aux.circuit, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    simp only [PEqualNP.Outside.L_meta_25998_aux.circuit, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or]
  ·
    decide
  ·
    decide
  ·
    decide
