import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19441 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7580827 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    ⟨[⟨.or, [0, 7]⟩,
      ⟨.or, [1, 9]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [11, 12]⟩,
      ⟨.and, [10, 13]⟩,
      ⟨.and, [8, 12]⟩,
      ⟨.or, [11, 15]⟩,
      ⟨.or, [7, 16]⟩,
      ⟨.not, [17]⟩,
      ⟨.or, [14, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro gate member
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor
    all_goals first | simp | decide
  · decide +kernel
