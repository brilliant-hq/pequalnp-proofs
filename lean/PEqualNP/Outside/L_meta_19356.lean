import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19356
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[3,5]⟩,⟨.or,[0,9]⟩,⟨.or,[2,11]⟩,⟨.or,[6,10]⟩,⟨.or,[4,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,14]⟩,⟨.not,[15]⟩,⟨.and,[16,17]⟩],18⟩
end PEqualNP.Outside.L_meta_19356
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19356 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237180 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19356.circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19356.circuit], by decide +kernel, by decide +kernel⟩
