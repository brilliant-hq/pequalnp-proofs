import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19355
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[3,4]⟩,⟨.or,[5,10]⟩,⟨.or,[8,9]⟩,⟨.or,[0,12]⟩,⟨.or,[2,13]⟩,⟨.or,[11,13]⟩,⟨.and,[11,14]⟩,⟨.not,[16]⟩,⟨.and,[15,17]⟩],18⟩
end PEqualNP.Outside.L_meta_19355
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19355 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594814 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19355.circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19355.circuit], by decide +kernel, by decide +kernel⟩
