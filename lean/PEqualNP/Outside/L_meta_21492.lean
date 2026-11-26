import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21492_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 6]⟩], 8⟩

theorem wit_fan : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21492_aux

theorem PEqualNP.Outside.L_meta_21492 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25567 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21492_aux.wit, PEqualNP.Outside.L_meta_21492_aux.wit_fan, by decide, by decide +kernel⟩
