import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_772

open Matrix

theorem mulVecLin_eq (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F)
    (B : Matrix (Fin c) (Fin d) F) :
    (Matrix.fromBlocks A (0 : Matrix (Fin a) (Fin d) F) (0 : Matrix (Fin c) (Fin b) F) B).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin c) F F).symm.toLinearMap ∘ₗ
        (LinearMap.prodMap A.mulVecLin B.mulVecLin) ∘ₗ
          (LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin d) F F).toLinearMap := by
  refine LinearMap.ext fun x => funext fun i => ?_
  rcases i with i | i <;>
    simp [fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow]

end PEqualNP.Outside.L_lib_772

open PEqualNP.Outside.L_lib_772 in
theorem PEqualNP.Outside.L_lib_772 : ∀ (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin c) (Fin d) F),
  (Matrix.fromBlocks A (0 : Matrix (Fin a) (Fin d) F) (0 : Matrix (Fin c) (Fin b) F) B).rank =
    A.rank + B.rank := by
  intro F _ a b c d A B
  rw [Matrix.rank, mulVecLin_eq, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range _), LinearEquiv.finrank_map_eq, LinearMap.range_prodMap,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  rfl

