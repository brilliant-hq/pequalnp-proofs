import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_49950 :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
      ∀ t : Fin 5,
        let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (8 : Nat).testBit t.val ∧
        w.getD q.val false = (12 : Nat).testBit t.val ∧
        w.getD r.val false = (22 : Nat).testBit t.val := by
  refine ⟨⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [1, 6]⟩,
      ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [0, 9]⟩], 10⟩,
    ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj i hi
    simp only [List.length_cons, List.length_nil] at hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    interval_cases j <;> simp_all <;> omega
  · decide
  · decide
  · decide
