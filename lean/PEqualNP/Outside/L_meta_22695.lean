import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22695
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[
  ⟨.or,[6,8]⟩,
  ⟨.or,[9,10]⟩,
  ⟨.or,[1,2]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[4,6]⟩,
  ⟨.or,[7,15]⟩,
  ⟨.and,[13,14]⟩,
  ⟨.and,[12,16]⟩,
  ⟨.and,[0,11]⟩,
  ⟨.and,[1,10]⟩,
  ⟨.or,[17,18]⟩,
  ⟨.or,[19,21]⟩,
  ⟨.or,[20,22]⟩],23⟩

theorem legal : Monotone2 circuit := by
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

end PEqualNP.Outside.L_meta_22695

theorem PEqualNP.Outside.L_meta_22695 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849780 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22695.circuit,PEqualNP.Outside.L_meta_22695.legal,by decide,by decide +kernel⟩
