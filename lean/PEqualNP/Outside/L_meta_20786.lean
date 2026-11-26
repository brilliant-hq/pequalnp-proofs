import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20786 :
    PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 16 := by
  let c : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.and, [5, 7]⟩,
      ⟨.or, [8, 2]⟩, ⟨.and, [8, 2]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩,
      ⟨.or, [12, 3]⟩, ⟨.and, [12, 3]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩,
      ⟨.or, [16, 4]⟩, ⟨.and, [16, 4]⟩, ⟨.not, [18]⟩, ⟨.and, [17, 19]⟩], 20⟩
  refine ⟨c, ?_, by decide +revert, ?_⟩
  · intro g hg
    simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · dsimp only [c]
    decide +kernel
