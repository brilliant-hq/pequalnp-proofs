import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19312
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[0,8]⟩,⟨.or,[9,10]⟩,⟨.or,[4,5]⟩,⟨.or,[10,12]⟩,⟨.and,[11,12]⟩,⟨.not,[14]⟩,⟨.and,[0,8]⟩,⟨.not,[16]⟩,⟨.and,[15,17]⟩,⟨.and,[13,18]⟩],19⟩
end PEqualNP.Outside.L_meta_19312
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19312 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644470 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19312.circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19312.circuit], by decide +kernel, by decide +kernel⟩
