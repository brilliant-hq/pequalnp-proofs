import PEqualNP.Defs

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_19152 :
  let rows : List ℕ → Finset (Finset (Fin 10)) := fun ms =>
    (ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
      ((List.finRange 10).filter fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset
  let H : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
  ∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ H.Adj a c) →
    (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, H.Adj a w) →
    I ∈ rows [50,116] ∧ ∀ w : Fin 10, w ∉ I →
      ∃ P ∈ rows [51,54,101,108], P ⊆ insert w I := by
  dsimp only
  simp only [SimpleGraph.fromRel_adj]
  decide +kernel
