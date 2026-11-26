import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20848_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 5) : Bool := (21366817 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 16]⟩], 19⟩

theorem upper : RepSizeAtMost graph 10 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [Monotone2, witness, Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_20848_aux

theorem PEqualNP.Outside.L_meta_20848 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (21366817 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact PEqualNP.Outside.L_meta_20848_aux.upper
