import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_476 : (∀ (n m : ℕ) (C : Fin m → Finset (Fin n × Bool)) (A B : Finset (Fin n × Bool)),
  (∃ x : Fin n → Bool,
    (∀ i, ∃ l ∈ C i, x l.1 = l.2) ∧ ∃ l ∈ A ∪ B, x l.1 = l.2) ↔
  ∃ y : Option (Fin n) → Bool,
    (∀ i, ∃ l ∈ C i, y (some l.1) = l.2) ∧
    ((∃ l ∈ A, y (some l.1) = l.2) ∨ y none = true) ∧
    ((∃ l ∈ B, y (some l.1) = l.2) ∨ y none = false)) := by
  intro n m C A B
  constructor
  · rintro ⟨x, hC, l, hl, hx⟩
    by_cases hA : ∃ l ∈ A, x l.1 = l.2
    · refine ⟨fun o => o.elim false x, hC, Or.inl hA, Or.inr rfl⟩
    · have hB : l ∈ B := (Finset.mem_union.mp hl).resolve_left fun h => hA ⟨l, h, hx⟩
      refine ⟨fun o => o.elim true x, hC, Or.inr rfl, Or.inl ⟨l, hB, hx⟩⟩
  · rintro ⟨y, hC, hA, hB⟩
    refine ⟨fun v => y (some v), hC, ?_⟩
    cases h : y none
    · obtain ⟨l, hl, hy⟩ := hA.resolve_right (by simp [h])
      exact ⟨l, Finset.mem_union_left _ hl, hy⟩
    · obtain ⟨l, hl, hy⟩ := hB.resolve_right (by simp [h])
      exact ⟨l, Finset.mem_union_right _ hl, hy⟩
