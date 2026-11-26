import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23720 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (469 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩,
      ⟨.and, [6, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩], 10⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
