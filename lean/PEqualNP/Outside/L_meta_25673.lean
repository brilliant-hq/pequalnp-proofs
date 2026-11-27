import Mathlib

namespace PEqualNP.Outside.L_meta_25673_aux

theorem main : ∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
    L ⊆ K ∧ L.card ≤ 0 ∧ 5 ≤ K.card + 0 ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor ((25298977 : ℕ).testBit (5 * i.val + (π i).val)) ((25298977 : ℕ).testBit (5 * j.val + (π j).val)))
        (Bool.xor ((25298977 : ℕ).testBit (5 * i.val + (π j).val)) ((25298977 : ℕ).testBit (5 * j.val + (π i).val))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  refine ⟨Fin.revPerm, Finset.univ, ∅, by simp, by simp, by simp, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_25673_aux

theorem PEqualNP.Outside.L_meta_25673 : let G := fun (i j : Fin 5) => (25298977 : ℕ).testBit (5 * i.val + j.val)
let u : ℕ := 0
let t : ℕ := 0
(∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
    L ⊆ K ∧ L.card ≤ u ∧ 5 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) := by
  intro G u t
  exact PEqualNP.Outside.L_meta_25673_aux.main
