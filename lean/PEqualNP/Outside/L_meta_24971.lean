import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24971_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.not, [5]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [8, 13]⟩], 14⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

theorem ev0 : ∀ i j : Fin 6,
    C0.eval [decide ((0 : Fin 6) = i ∨ 0 = j), decide ((1 : Fin 6) = i ∨ 1 = j), decide ((2 : Fin 6) = i ∨ 2 = j), decide ((3 : Fin 6) = i ∨ 3 = j), decide ((4 : Fin 6) = i ∨ 4 = j), decide ((5 : Fin 6) = i ∨ 5 = j)] = (6409150 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24971_aux

theorem PEqualNP.Outside.L_meta_24971 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409150 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24971_aux.C0, PEqualNP.Outside.L_meta_24971_aux.ok0, by decide, fun i j => by
    rw [PEqualNP.Outside.L_meta_24971_aux.ofFn6]
    exact PEqualNP.Outside.L_meta_24971_aux.ev0 i j⟩
