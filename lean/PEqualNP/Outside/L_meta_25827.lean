import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25780
import PEqualNP.Outside.L_meta_6337

theorem PEqualNP.Outside.L_meta_25827 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C)) := by
  rintro ⟨C, hf, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6337.2 (PEqualNP.Outside.L_meta_25780 6 _ C hf hs hr)
