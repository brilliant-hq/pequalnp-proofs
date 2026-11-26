import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19771

/-- The assignment desk's 33-gate construction, in evaluation order. -/
def witness : Circuit := ⟨[
  ⟨.or, [8, 15]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.or, [10, 12]⟩,
  ⟨.or, [13, 18]⟩,
  ⟨.or, [13, 16]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.or, [14, 19]⟩,
  ⟨.or, [15, 22]⟩,
  ⟨.and, [0, 23]⟩,
  ⟨.or, [17, 20]⟩,
  ⟨.and, [1, 25]⟩,
  ⟨.or, [14, 17]⟩,
  ⟨.or, [27, 18]⟩,
  ⟨.and, [2, 28]⟩,
  ⟨.or, [8, 22]⟩,
  ⟨.and, [3, 30]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [32, 20]⟩,
  ⟨.and, [4, 33]⟩,
  ⟨.or, [17, 21]⟩,
  ⟨.and, [5, 35]⟩,
  ⟨.or, [17, 19]⟩,
  ⟨.and, [6, 37]⟩,
  ⟨.or, [9, 12]⟩,
  ⟨.or, [39, 21]⟩,
  ⟨.and, [7, 40]⟩,
  ⟨.or, [24, 26]⟩,
  ⟨.or, [42, 29]⟩,
  ⟨.or, [43, 31]⟩,
  ⟨.or, [44, 34]⟩,
  ⟨.or, [45, 36]⟩,
  ⟨.or, [46, 38]⟩,
  ⟨.or, [47, 41]⟩], 48⟩

end PEqualNP.Outside.L_meta_19771

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19771 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15221827736417774580 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let C := PEqualNP.Outside.L_meta_19771.witness
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp [C, PEqualNP.Outside.L_meta_19771.witness] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> decide
  · decide +kernel
