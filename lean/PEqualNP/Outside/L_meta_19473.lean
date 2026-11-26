import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19473

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [8, 3]⟩,
    ⟨.or, [10, 0]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.and, [7, 4]⟩,
    ⟨.or, [15, 14]⟩,
    ⟨.not, [16]⟩,
    ⟨.or, [17, 13]⟩], 18⟩

theorem witness_fanIn : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro gate member
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19473

open PEqualNP.Outside.L_meta_19473 in
theorem PEqualNP.Outside.L_meta_19473 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨witness, witness_fanIn, by decide, by decide +kernel⟩
