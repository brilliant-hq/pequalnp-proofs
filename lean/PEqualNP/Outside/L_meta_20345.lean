import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_20345

def witness : Circuit := ⟨[
  ⟨.or, [11, 9]⟩,
  ⟨.or, [15, 1]⟩,
  ⟨.or, [3, 12]⟩,
  ⟨.or, [5, 13]⟩,
  ⟨.or, [7, 17]⟩,
  ⟨.or, [20, 4]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.and, [16, 21]⟩,
  ⟨.or, [18, 2]⟩,
  ⟨.or, [19, 4]⟩,
  ⟨.or, [9, 20]⟩,
  ⟨.or, [18, 6]⟩,
  ⟨.or, [25, 11]⟩,
  ⟨.or, [17, 24]⟩,
  ⟨.or, [28, 7]⟩,
  ⟨.and, [26, 24]⟩,
  ⟨.or, [30, 27]⟩,
  ⟨.or, [28, 29]⟩,
  ⟨.or, [30, 0]⟩,
  ⟨.and, [32, 14]⟩,
  ⟨.or, [34, 2]⟩,
  ⟨.and, [29, 19]⟩,
  ⟨.or, [37, 10]⟩,
  ⟨.or, [22, 38]⟩,
  ⟨.and, [39, 33]⟩,
  ⟨.and, [8, 36]⟩,
  ⟨.or, [23, 40]⟩,
  ⟨.or, [42, 41]⟩,
  ⟨.or, [43, 31]⟩,
  ⟨.or, [44, 35]⟩], 45⟩

end PEqualNP.Outside.L_meta_20345

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20345 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let C := PEqualNP.Outside.L_meta_20345.witness
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp [C, PEqualNP.Outside.L_meta_20345.witness] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> decide
  · decide +kernel
