import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20709_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩

end PEqualNP.Outside.L_meta_20709_aux

theorem PEqualNP.Outside.L_meta_20709 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31917056 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_20709_aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20709_aux.witness, Set.mem_insert_iff, Set.mem_singleton_iff]
