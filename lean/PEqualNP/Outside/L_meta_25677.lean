import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25677

theorem key : ∀ π : Equiv.Perm (Fin 4), ¬ ∀ i j : Fin 4,
      Bool.xor (Bool.xor (((19 : ℕ).testBit (4 * i.val + (π i).val))) ((19 : ℕ).testBit (4 * j.val + (π j).val)))
        (Bool.xor ((19 : ℕ).testBit (4 * i.val + (π j).val)) ((19 : ℕ).testBit (4 * j.val + (π i).val))) =
      Bool.xor (decide (i ∈ (∅ : Finset (Fin 4)))) (decide (j ∈ (∅ : Finset (Fin 4)))) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25677

theorem PEqualNP.Outside.L_meta_25677 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (19 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ (if u = 0 then 1 else 0) ≤ t := by
  intro u t G
  constructor
  · rintro ⟨π, K, L, hLK, hLu, hK, h⟩
    by_cases hu : u = 0
    · subst hu
      simp only [↓reduceIte]
      by_contra ht
      have ht0 : t = 0 := by omega
      subst ht0
      have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hL
      have hKu : K = Finset.univ :=
        Finset.eq_univ_of_card K (le_antisymm (Finset.card_le_univ K) (by simpa using hK))
      subst hKu
      exact PEqualNP.Outside.L_meta_25677.key π (fun i j => h i (Finset.mem_univ _) j (Finset.mem_univ _))
    · simp only [hu, ↓reduceIte]
      exact Nat.zero_le t
  · intro ht
    by_cases hu : u = 0
    · simp only [hu, ↓reduceIte] at ht
      refine ⟨1, {1, 2, 3}, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
      · have hc : ({1, 2, 3} : Finset (Fin 4)).card = 3 := by decide
        omega
      · decide
    · refine ⟨1, Finset.univ, {0}, Finset.subset_univ _, ?_, by simp, ?_⟩
      · rw [Finset.card_singleton]
        omega
      · decide
