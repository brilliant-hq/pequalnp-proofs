import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19513

private def theGates : List Gate :=
  [ ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [0, 15]⟩,
    ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [17, 14]⟩, ⟨GateOp.or, [18, 16]⟩ ]

private def theCircuit : Circuit := ⟨theGates, 19⟩

private theorem main :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      Represents (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨theCircuit, ?_, ?_, ?_⟩
  · show ∀ g ∈ theGates, _
    intro g hg
    simp only [theGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp⟩
  · show theGates.length ≤ 10
    decide
  · decide

end PEqualNP.Outside.L_meta_19513

theorem PEqualNP.Outside.L_meta_19513 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents
        (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19513.main
