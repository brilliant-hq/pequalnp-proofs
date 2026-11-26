import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19416
def chainC : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.or,[2,3]⟩,⟨.and,[12,7]⟩,⟨.or,[10,11]⟩,⟨.or,[14,13]⟩],15⟩
end PEqualNP.Outside.L_meta_19416
open PEqualNP.Outside.L_meta_19416 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19416 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 3, 3, 2] u)) 6 := by
  refine ⟨chainC, by simp [PEqualNP.MetaComplexity.Monotone2,chainC], by decide +kernel, by decide +kernel⟩

