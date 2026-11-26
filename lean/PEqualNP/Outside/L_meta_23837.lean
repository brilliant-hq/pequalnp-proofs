import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23837_aux
open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [6, 9]⟩], 10⟩

private theorem fanIn : PEqualNP.MetaComplexity.FanInTwo witnessCircuit := by
  intro g hg
  simp only [witnessCircuit, List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23837_aux

open PEqualNP.Outside.L_meta_23837_aux in
theorem PEqualNP.Outside.L_meta_23837 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4298 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witnessCircuit,fanIn,by decide,?_⟩
  decide +kernel
