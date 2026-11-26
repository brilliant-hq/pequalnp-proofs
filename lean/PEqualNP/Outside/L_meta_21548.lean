import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21548

def witness : Circuit := ⟨[
  ⟨.or, [3, 4]⟩,
  ⟨.not, [5]⟩,
  ⟨.or, [0, 6]⟩
  ], 7⟩

end PEqualNP.Outside.L_meta_21548

theorem PEqualNP.Outside.L_meta_21548 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4319 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21548.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    have all : PEqualNP.Outside.L_meta_21548.witness.gates.all (fun h => decide (h.op = .and ∨ h.op = .or ∨ h.op = .not) &&
        decide (h.inputs.length ≤ 2)) = true := by decide +kernel
    have fits := List.all_eq_true.mp all g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fits.1, fits.2⟩
  · change ∀ i j : Fin 5, PEqualNP.Outside.L_meta_21548.witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
      (4319 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)
    decide +kernel
