import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22056

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [14, 13]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33726 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22056

theorem PEqualNP.Outside.L_meta_22056 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33726 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22056.ckt, PEqualNP.Outside.L_meta_22056.fan, by decide, PEqualNP.Outside.L_meta_22056.ev⟩
