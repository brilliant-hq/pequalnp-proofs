import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22822

open PEqualNP.CircuitLowerBounds

/-- Five fan-in-two AND/OR gates computing the six-point two-lit-points function of mask 233023.
    Inputs x0..x5 are wires 0..5; gate j writes wire 6+j. -/
def c : Circuit :=
  { gates := [ ⟨GateOp.or, [3, 4]⟩,    -- wire 6: x3 || x4
               ⟨GateOp.or, [5, 6]⟩,    -- wire 7: x5 || x6 = x3 || x4 || x5
               ⟨GateOp.or, [1, 2]⟩,    -- wire 8: x1 || x2
               ⟨GateOp.and, [8, 7]⟩,   -- wire 9: (x1||x2) && (x3||x4||x5)
               ⟨GateOp.or, [0, 9]⟩ ],  -- wire 10: x0 || ((x1||x2)&&(x3||x4||x5))
    output := 10 }

end PEqualNP.Outside.L_meta_22822

theorem PEqualNP.Outside.L_meta_22822 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧
    ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (233023 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  have fanTwo : PEqualNP.MetaComplexity.FanInTwo PEqualNP.Outside.L_meta_22822.c := by
    intro g hg
    simp only [PEqualNP.Outside.L_meta_22822.c, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [PEqualNP.MetaComplexity.FanInTwo]
  refine ⟨PEqualNP.Outside.L_meta_22822.c, fanTwo, ?_, ?_⟩
  · decide
  · decide
