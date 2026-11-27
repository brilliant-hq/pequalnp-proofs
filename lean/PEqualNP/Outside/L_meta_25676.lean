import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25676 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (18 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 0 ≤ t := by
  intro u t G
  constructor
  · intro _
    exact Nat.zero_le t
  · intro _
    refine ⟨1, Finset.univ, ∅, Finset.empty_subset _, Nat.zero_le u, ?_, ?_⟩
    · rw [Finset.card_univ, Fintype.card_fin]
      exact Nat.le_add_right 4 t
    · decide
