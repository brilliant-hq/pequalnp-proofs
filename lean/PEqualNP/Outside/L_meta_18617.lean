import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_18617 : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := by
  refine ⟨⟨[⟨GateOp.or, [18, 24]⟩,
    ⟨GateOp.or, [13, 27]⟩,
    ⟨GateOp.and, [1, 28]⟩,
    ⟨GateOp.or, [19, 25]⟩,
    ⟨GateOp.or, [15, 30]⟩,
    ⟨GateOp.and, [2, 31]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [16, 33]⟩,
    ⟨GateOp.and, [4, 34]⟩,
    ⟨GateOp.or, [22, 23]⟩,
    ⟨GateOp.or, [20, 36]⟩,
    ⟨GateOp.and, [10, 37]⟩,
    ⟨GateOp.or, [35, 38]⟩,
    ⟨GateOp.or, [32, 39]⟩,
    ⟨GateOp.or, [29, 40]⟩], 41⟩, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro x
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hin : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by rfl
  rw [hin]
  change (List.foldl step _ _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false)), (x 20 || ((x 22 || (x 23 || false)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false)), (x 20 || ((x 22 || (x 23 || false)) || false)), (x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false)), (x 20 || ((x 22 || (x 23 || false)) || false)), (x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)), ((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false)), (x 20 || ((x 22 || (x 23 || false)) || false)), (x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)), ((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)), ((x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)) || (((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)) || false))] _).getD 41 false = true ↔ _
  rw [List.foldl_cons]
  change (List.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, (x 1 || x 2), (x 18 || (x 24 || false)), (x 13 || ((x 18 || (x 24 || false)) || false)), (x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)), (x 19 || (x 25 || false)), (x 15 || ((x 19 || (x 25 || false)) || false)), (x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)), (x 17 || (x 21 || false)), (x 16 || ((x 17 || (x 21 || false)) || false)), (x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)), (x 22 || (x 23 || false)), (x 20 || ((x 22 || (x 23 || false)) || false)), (x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)), ((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)), ((x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)) || (((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)) || false)), ((x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)) || (((x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)) || (((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)) || false)) || false))] _).getD 41 false = true ↔ _
  change ((x 1 && ((x 13 || ((x 18 || (x 24 || false)) || false)) && true)) || (((x 2 && ((x 15 || ((x 19 || (x 25 || false)) || false)) && true)) || (((x 4 && ((x 16 || ((x 17 || (x 21 || false)) || false)) && true)) || ((x 10 && ((x 20 || ((x 22 || (x 23 || false)) || false)) && true)) || false)) || false)) || false)) = true ↔ _
  simp only [Bool.or_false, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩
    · exact ⟨1, 0, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨1, 5, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨1, 11, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨2, 2, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨2, 6, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨2, 12, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨4, 3, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨4, 4, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨4, 8, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨10, 7, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨10, 9, by decide, by decide, by decide, hp, hl⟩
    · exact ⟨10, 10, by decide, by decide, by decide, hp, hl⟩
  · rintro ⟨p, l, hp, hl, he, xp, xl⟩
    have table : ∀ p l : Fin 13,
        (decide (p ∈ ([1,2,4,10] : List (Fin 13))) && decide (l ≠ 1) &&
        decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) &&
        !decide ((p,l) ∈ ([(1,0), (1,5), (1,11), (2,2), (2,6), (2,12), (4,3), (4,4), (4,8), (10,7), (10,9), (10,10)] : List (Fin 13 × Fin 13)))) = false := by decide
    have hit : (p,l) ∈ ([(1,0), (1,5), (1,11), (2,2), (2,6), (2,12), (4,3), (4,4), (4,8), (10,7), (10,9), (10,10)] : List (Fin 13 × Fin 13)) := by
      by_contra hn
      have bad := table p l
      simp only [hp, he, hn, decide_true, decide_false] at bad
      rw [decide_eq_true hl] at bad
      cases bad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      change x _ = true at xp xl
      first
      | change x 1 = true at xp; change x 13 = true at xl; simp [xp,xl]
      | change x 1 = true at xp; change x 18 = true at xl; simp [xp,xl]
      | change x 1 = true at xp; change x 24 = true at xl; simp [xp,xl]
      | change x 2 = true at xp; change x 15 = true at xl; simp [xp,xl]
      | change x 2 = true at xp; change x 19 = true at xl; simp [xp,xl]
      | change x 2 = true at xp; change x 25 = true at xl; simp [xp,xl]
      | change x 4 = true at xp; change x 16 = true at xl; simp [xp,xl]
      | change x 4 = true at xp; change x 17 = true at xl; simp [xp,xl]
      | change x 4 = true at xp; change x 21 = true at xl; simp [xp,xl]
      | change x 10 = true at xp; change x 20 = true at xl; simp [xp,xl]
      | change x 10 = true at xp; change x 22 = true at xl; simp [xp,xl]
      | change x 10 = true at xp; change x 23 = true at xl; simp [xp,xl]
