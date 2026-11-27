import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25676

theorem main_aux : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (18 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 0 ≤ t := by
  intro u t
  dsimp only
  constructor
  · intro _; exact Nat.zero_le _
  · intro _
    exact ⟨1, Finset.univ, ∅, Finset.empty_subset _, by simp, by rw [Finset.card_univ, Fintype.card_fin]; omega, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25676

theorem PEqualNP.Outside.L_meta_25676 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (18 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 0 ≤ t :=
  PEqualNP.Outside.L_meta_25676.main_aux
