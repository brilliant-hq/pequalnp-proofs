import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own circuit formula
-- for AND/OR/NOT gates (notes/data/lrat-link), stated on the inputs with two points on (or one). The file checks
-- the gate kinds, the gate count and the value on each of those inputs.
namespace PEqualNP.Outside.L_meta_24737

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24737

theorem PEqualNP.Outside.L_meta_24737 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100014 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24737.wit, by simp [PEqualNP.Outside.L_meta_24737.wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide⟩
