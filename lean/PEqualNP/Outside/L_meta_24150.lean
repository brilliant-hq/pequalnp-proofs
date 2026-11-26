import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24150_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 12]⟩], 13⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4440 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, witness_fan, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_24150_aux

theorem PEqualNP.Outside.L_meta_24150 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4440 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24150_aux.solve
