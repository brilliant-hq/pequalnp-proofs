import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_50174

def D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 1]⟩], 0⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo D := by
  intro g hg
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_50174

theorem PEqualNP.Outside.L_meta_50174 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (20 : Nat).testBit t.val ∧
    w.getD q.val false = (24 : Nat).testBit t.val ∧
    w.getD r.val false = (30 : Nat).testBit t.val := by
  refine ⟨PEqualNP.Outside.L_meta_50174.D, ⟨8, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩, PEqualNP.Outside.L_meta_50174.fan, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
