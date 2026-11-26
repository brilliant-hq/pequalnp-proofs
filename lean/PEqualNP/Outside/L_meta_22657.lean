import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22657

def upperA : Fin 4 → Fin 6 → Bool :=
  fun (u : Fin 4) (v : Fin 6) => (841145 : ℕ).testBit (6 * u.val + v.val)

def upperC : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [3, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [9, 17]⟩, ⟨.and, [0, 18]⟩, ⟨.and, [12, 16]⟩, ⟨.and, [14, 10]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 21]⟩], 23⟩

theorem upper_mono : PEqualNP.MetaComplexity.Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents upperA upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22657

theorem PEqualNP.Outside.L_meta_22657 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841145 : ℕ).testBit (6 * u.val + v.val)) 14) :=
  ⟨PEqualNP.Outside.L_meta_22657.upperC, PEqualNP.Outside.L_meta_22657.upper_mono, by decide, PEqualNP.Outside.L_meta_22657.upper_rep⟩
