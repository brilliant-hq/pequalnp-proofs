import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_498 : (∀ (n p q : ℕ) (A : Fin p → Finset (Fin n × Bool))
    (B : Fin q → Finset (Fin n × Bool)) (x : Fin n → Bool),
  let holds := fun C : Finset (Fin n × Bool) => ∃ l ∈ C, x l.1 = l.2
  (∃ t : Bool, (∀ i, holds (A i) ∨ t = true) ∧ (∀ j, holds (B j) ∨ t = false)) ↔
    ∀ i j, holds (A i ∪ B j)) := by
  intro n p q A B x
  dsimp only
  constructor
  · rintro ⟨t, hA, hB⟩ i j
    cases t
    · rcases hA i with ⟨l, hl, hxl⟩ | ht
      · exact ⟨l, Finset.mem_union_left _ hl, hxl⟩
      · cases ht
    · rcases hB j with ⟨l, hl, hxl⟩ | ht
      · exact ⟨l, Finset.mem_union_right _ hl, hxl⟩
      · cases ht
  · intro hAB
    by_cases hA : ∀ i, ∃ l ∈ A i, x l.1 = l.2
    · exact ⟨false, fun i => Or.inl (hA i), fun _ => Or.inr rfl⟩
    · refine ⟨true, fun _ => Or.inr rfl, fun j => Or.inl ?_⟩
      have hne : ∃ i, ¬ ∃ l ∈ A i, x l.1 = l.2 := Classical.not_forall.mp hA
      rcases hne with ⟨i, hi⟩
      rcases hAB i j with ⟨l, hl, hxl⟩
      rcases Finset.mem_union.mp hl with hlA | hlB
      · exact False.elim (hi ⟨l, hlA, hxl⟩)
      · exact ⟨l, hlB, hxl⟩
