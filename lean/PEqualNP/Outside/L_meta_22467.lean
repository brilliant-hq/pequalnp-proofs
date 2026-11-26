import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22467

def witness : Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.and, [0, 7]⟩,
  ⟨.and, [1, 2]⟩,
  ⟨.or, [5, 9]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [3, 11]⟩,
  ⟨.or, [0, 12]⟩,
  ⟨.not, [13]⟩,
  ⟨.or, [8, 14]⟩
  ], 15⟩

end PEqualNP.Outside.L_meta_22467

theorem PEqualNP.Outside.L_meta_22467 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 16 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16568 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22467.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    have all : PEqualNP.Outside.L_meta_22467.witness.gates.all (fun h => decide (h.op = .and ∨ h.op = .or ∨ h.op = .not) &&
        decide (h.inputs.length ≤ 2)) = true := by decide +kernel
    have fits := List.all_eq_true.mp all g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fits.1, fits.2⟩
  · change ∀ i j : Fin 6, PEqualNP.Outside.L_meta_22467.witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (16568 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)
    decide +kernel
