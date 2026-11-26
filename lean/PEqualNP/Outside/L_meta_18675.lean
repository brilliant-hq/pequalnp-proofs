import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18675 : ∀ (x1 : ℕ) (x2 : List PEqualNP.CircuitLowerBounds.Gate),   (∀ (x3 : Fin x2.length),       have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.getD ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };       (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x4.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < x1 + ↑x3 ∧ x6 < x1 + ↑x3) →     PEqualNP.TopForm.IsAO2 x1 { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ x4 ∈ x2, x4.inputs.Nodup := by
  intro n gates h
  have member (g : Gate) (hg : g ∈ gates) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b := by
    obtain ⟨j, hj, eq⟩ := List.getElem_of_mem hg
    have data := h ⟨j, hj⟩
    dsimp only at data
    rw [List.getD_eq_getElem _ _ hj, eq] at data
    obtain ⟨ops, a, b, inputs, ne, _, _⟩ := data
    exact ⟨ops, a, b, inputs, ne⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    exact (member g hg).1
  · intro j hj i hi
    have data := h ⟨j, hj⟩
    rcases data.2 with ⟨a, b, inputs, _, ha, hb⟩
    change i ∈ (gates.getD j ⟨.or, []⟩).inputs at hi
    rw [inputs] at hi
    rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi : i = a ∨ i = b) with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨a, b, e, _⟩ := (member g hg).2
    simp [e]
  · intro g hg
    obtain ⟨a, b, e, ne⟩ := (member g hg).2
    simp [e, ne]

