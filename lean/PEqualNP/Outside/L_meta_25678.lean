import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25678

theorem key : ∀ π : Equiv.Perm (Fin 4), ∀ L : Finset (Fin 4), ¬ ∀ i j : Fin 4,
      Bool.xor (Bool.xor (((53 : ℕ).testBit (4 * i.val + (π i).val))) ((53 : ℕ).testBit (4 * j.val + (π j).val)))
        (Bool.xor ((53 : ℕ).testBit (4 * i.val + (π j).val)) ((53 : ℕ).testBit (4 * j.val + (π i).val))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25678

theorem PEqualNP.Outside.L_meta_25678 : ∀ u t : ℕ,
let G := fun (i j : Fin 4) => (53 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ 1 ≤ t := by
  intro u t G
  constructor
  · rintro ⟨π, K, L, hLK, hLu, hK, h⟩
    by_contra ht
    have ht0 : t = 0 := by omega
    subst ht0
    have hKu : K = Finset.univ :=
      Finset.eq_univ_of_card K (le_antisymm (Finset.card_le_univ K) (by simpa using hK))
    subst hKu
    exact PEqualNP.Outside.L_meta_25678.key π L (fun i j => h i (Finset.mem_univ _) j (Finset.mem_univ _))
  · intro ht
    refine ⟨Equiv.swap 1 3, {0, 1, 2}, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
    · have hc : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
      omega
    · decide
