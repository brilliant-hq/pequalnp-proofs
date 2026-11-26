import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24048 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4956 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[3,4]⟩,⟨.or,[0,6]⟩,⟨.or,[2,6]⟩,⟨.and,[5,8]⟩,⟨.and,[9,7]⟩,⟨.or,[9,7]⟩,⟨.not,[11]⟩,⟨.or,[10,12]⟩],13⟩
  refine ⟨circuit,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
