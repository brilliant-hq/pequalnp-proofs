import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20877

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩

theorem allowed : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20877

theorem PEqualNP.Outside.L_meta_20877 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_20877.witness, PEqualNP.Outside.L_meta_20877.allowed, by decide, by decide +kernel⟩
