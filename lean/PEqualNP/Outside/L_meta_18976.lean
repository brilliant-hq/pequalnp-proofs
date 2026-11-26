import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18976

private def masks : List ℕ :=
  [67100672, 25018369, 7962627, 24444933, 7405575, 6815755, 23330829, 5799955, 22282261, 21757977, 19988517, 19415081, 6619269, 2179233]

-- Each row gives a mask index, multiplier, and translation for {0, b, c}.
private def certificate : Array (ℕ × Fin 13 × Fin 13) := #[
  (1, 1, 0), (2, 1, 0), (3, 1, 0), (2, 9, 0), (2, 3, 1), (3, 3, 0), (3, 9, 0), (3, 9, 2), (3, 3, 2), (2, 3, 0), (2, 9, 1), (3, 1, 2), (2, 1, 1),
  (2, 1, 0), (2, 1, 0), (4, 1, 0), (5, 1, 0), (7, 1, 0), (6, 3, 0), (11, 3, 0), (8, 9, 4), (10, 3, 2), (5, 3, 0), (9, 1, 3), (6, 1, 2), (4, 1, 1),
  (3, 1, 0), (4, 1, 0), (3, 1, 0), (6, 1, 0), (8, 1, 0), (10, 1, 0), (10, 9, 0), (12, 1, 0), (13, 1, 5), (11, 9, 0), (11, 1, 3), (8, 1, 2), (5, 1, 1),
  (2, 9, 0), (5, 1, 0), (6, 1, 0), (2, 9, 0), (9, 1, 0), (11, 1, 0), (4, 9, 0), (6, 9, 2), (8, 3, 4), (5, 9, 0), (4, 9, 1), (10, 1, 2), (7, 1, 1),
  (2, 3, 1), (7, 1, 0), (8, 1, 0), (9, 1, 0), (2, 3, 1), (5, 3, 1), (11, 9, 3), (5, 9, 3), (4, 3, 2), (4, 3, 1), (6, 9, 3), (10, 9, 5), (6, 3, 3),
  (3, 3, 0), (6, 3, 0), (10, 1, 0), (11, 1, 0), (5, 3, 1), (3, 3, 0), (10, 3, 0), (13, 1, 0), (8, 3, 2), (4, 3, 0), (8, 3, 0), (12, 1, 2), (11, 3, 3),
  (3, 9, 0), (11, 3, 0), (10, 9, 0), (4, 9, 0), (11, 9, 3), (10, 3, 0), (3, 9, 0), (8, 9, 2), (12, 1, 7), (6, 9, 0), (5, 9, 1), (13, 1, 7), (8, 9, 0),
  (3, 9, 2), (8, 9, 4), (12, 1, 0), (6, 9, 2), (5, 9, 3), (13, 1, 0), (8, 9, 2), (3, 9, 2), (11, 3, 5), (10, 9, 2), (4, 9, 2), (11, 9, 5), (10, 3, 5),
  (3, 3, 2), (10, 3, 2), (13, 1, 5), (8, 3, 4), (4, 3, 2), (8, 3, 2), (12, 1, 7), (11, 3, 5), (3, 3, 2), (6, 3, 2), (10, 1, 5), (11, 1, 5), (5, 3, 3),
  (2, 3, 0), (5, 3, 0), (11, 9, 0), (5, 9, 0), (4, 3, 1), (4, 3, 0), (6, 9, 0), (10, 9, 2), (6, 3, 2), (2, 3, 0), (7, 1, 4), (8, 1, 4), (9, 1, 4),
  (2, 9, 1), (9, 1, 3), (11, 1, 3), (4, 9, 1), (6, 9, 3), (8, 3, 0), (5, 9, 1), (4, 9, 2), (10, 1, 5), (7, 1, 4), (2, 9, 1), (5, 1, 3), (6, 1, 3),
  (3, 1, 2), (6, 1, 2), (8, 1, 2), (10, 1, 2), (10, 9, 5), (12, 1, 2), (13, 1, 7), (11, 9, 5), (11, 1, 5), (8, 1, 4), (5, 1, 3), (3, 1, 2), (4, 1, 2),
  (2, 1, 1), (4, 1, 1), (5, 1, 1), (7, 1, 1), (6, 3, 3), (11, 3, 3), (8, 9, 0), (10, 3, 5), (5, 3, 3), (9, 1, 4), (6, 1, 3), (4, 1, 2), (2, 1, 1)
]

private def witness (b c : Fin 13) : ℕ × Fin 13 × Fin 13 :=
  let (i, q, d) := certificate[b.val * 13 + c.val]!
  (masks[i]!, q, d)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 50000000 in
private theorem certificate_ok (b : Fin 13) : ∀ c : Fin 13,
    let (m, q, d) := witness b c
    m ∈ masks ∧ q ∈ ([1, 3, 9] : List (Fin 13)) ∧
      ∀ x : Fin 13, decide (x ∈ ({0, b, c} : Finset (Fin 13))) = m.testBit (q * x + d).val := by
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 50000000 in
private theorem triple (a b c : Fin 13) :
    ∃ m ∈ masks, ∃ q ∈ ([1, 3, 9] : List (Fin 13)), ∃ d : Fin 13,
      ∀ x : Fin 13, decide (x ∈ ({a, b, c} : Finset (Fin 13))) = m.testBit (q * x + d).val := by
  rcases hw : witness (b - a) (c - a) with ⟨m, q, d⟩
  have hc := certificate_ok (b - a) (c - a)
  rw [hw] at hc
  dsimp only at hc
  obtain ⟨hm, hq, hp⟩ := hc
  refine ⟨m, hm, q, hq, d - q * a, ?_⟩
  intro x
  have hmem : x - a ∈ ({0, b - a, c - a} : Finset (Fin 13)) ↔
      x ∈ ({a, b, c} : Finset (Fin 13)) := by
    simp [Finset.mem_insert, Finset.mem_singleton, sub_eq_zero]
  have hd : q * (x - a) + d = q * x + (d - q * a) := by
    rw [mul_sub, sub_add_eq_add_sub, add_sub_assoc]
  simpa only [hmem, hd] using hp (x - a)

private theorem result (s : Finset (Fin 13)) (hs : s.card ≤ 3) :
    ∃ m ∈ masks, ∃ q ∈ ([1, 3, 9] : List (Fin 13)), ∃ d : Fin 13,
      ∀ x : Fin 13, decide (x ∈ s) = m.testBit (q * x + d).val := by
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with h | h | h | h
  · rw [Finset.card_eq_zero.mp h]
    exact ⟨67100672, by decide, 1, by decide, 0, by decide⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    simpa using triple a a a
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    simpa using triple a b b
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    exact triple a b c

end PEqualNP.Outside.L_meta_18976

theorem PEqualNP.Outside.L_meta_18976 : ∀ (x1 : Finset (Fin (13 : ℕ))), x1.card ≤ (3 : ℕ) → ∃ x3 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)], ∃ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), Decidable.decide (x6 ∈ x1) = x3.testBit ↑(x4 * x6 + x5) := by
  exact PEqualNP.Outside.L_meta_18976.result
