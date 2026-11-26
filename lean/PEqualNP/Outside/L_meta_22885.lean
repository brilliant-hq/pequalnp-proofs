import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22885 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634582207 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or,[2,3]⟩, ⟨.or,[4,6]⟩, ⟨.or,[1,5]⟩,
    ⟨.and,[7,8]⟩, ⟨.not,[9]⟩],10⟩
  refine ⟨circuit,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl <;> simp
