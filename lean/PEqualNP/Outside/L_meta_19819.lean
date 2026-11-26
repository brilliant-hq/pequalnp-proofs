import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseCol

theorem PEqualNP.Outside.L_meta_19819 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10543322878649664930 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [9, 12]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [18, 15]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [21, 15]⟩,
    ⟨.and, [1, 22]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.and, [3, 26]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [28, 14]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [33, 14]⟩,
    ⟨.and, [6, 34]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [7, 36]⟩,
    ⟨.or, [20, 23]⟩,
    ⟨.or, [38, 25]⟩,
    ⟨.or, [39, 27]⟩,
    ⟨.or, [40, 30]⟩,
    ⟨.or, [41, 32]⟩,
    ⟨.or, [42, 35]⟩,
    ⟨.or, [43, 37]⟩
  ], 44⟩
  refine ⟨C, by simp [C, PEqualNP.MetaComplexity.Monotone2], by decide, ?_⟩
  have h := PEqualNP.Library.Helpers.PromiseCol.represents_of_pcols (n := 8) (m := 8) (N := 6) (by decide) C [162, 133, 41, 22, 76, 104, 81, 146] (by decide) (by decide +kernel) (by decide +kernel)
  intro u v
  have h3 : (([162, 133, 41, 22, 76, 104, 81, 146] : List ℕ).getD u.val 0).testBit v.val = (10543322878649664930 : ℕ).testBit (8 * u.val + v.val) := by
    revert u v; decide +kernel
  exact (h u v).trans h3
