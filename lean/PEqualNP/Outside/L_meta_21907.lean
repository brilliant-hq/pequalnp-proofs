import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21907

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.and, [1, 4]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.or, [9, 10]⟩
    ],
    output := 11 }

theorem fan : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33826 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21907

theorem PEqualNP.Outside.L_meta_21907 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33826 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21907.ckt, PEqualNP.Outside.L_meta_21907.fan, by decide, PEqualNP.Outside.L_meta_21907.ev⟩
