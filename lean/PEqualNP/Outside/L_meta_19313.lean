import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19313
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[2,3]⟩,⟨.or,[5,8]⟩,⟨.and,[10,11]⟩,⟨.and,[4,5]⟩,⟨.and,[4,9]⟩,⟨.or,[10,11]⟩,⟨.or,[14,15]⟩,⟨.not,[16]⟩,⟨.or,[12,13]⟩,⟨.or,[17,18]⟩],19⟩
end PEqualNP.Outside.L_meta_19313
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19313 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644886 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19313.circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19313.circuit], by decide +kernel, by decide +kernel⟩
