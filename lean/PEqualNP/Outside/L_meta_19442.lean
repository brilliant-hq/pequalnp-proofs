import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19442

private def meta19442Circuit : PEqualNP.CircuitLowerBounds.Circuit where
  gates := [
    ⟨.or, [3, 4]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [15, 18]⟩]
  output := 19

end PEqualNP.Outside.L_meta_19442

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_19442 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19442.meta19442Circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19442.meta19442Circuit]
  · decide
  · decide
