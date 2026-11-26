import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24967 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408103 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[0,5]⟩,⟨.or,[1,2]⟩,⟨.or,[7,3]⟩,⟨.or,[3,4]⟩,⟨.not,[9]⟩,⟨.and,[0,10]⟩,⟨.not,[6]⟩,⟨.and,[8,12]⟩,⟨.or,[11,13]⟩],14⟩
  refine ⟨circuit,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
