import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25673

def p : Fin 5 → Fin 5 := ![3, 4, 2, 1, 0]
def q : Fin 5 → Fin 5 := ![4, 3, 2, 0, 1]

def perm : Equiv.Perm (Fin 5) := ⟨p, q, by decide, by decide⟩

end PEqualNP.Outside.L_meta_25673

open PEqualNP.Outside.L_meta_25673 in
theorem PEqualNP.Outside.L_meta_25673 : let G := fun (i j : Fin 5) => (25298977 : ℕ).testBit (5 * i.val + j.val)
let u : ℕ := 0
let t : ℕ := 0
(∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
    L ⊆ K ∧ L.card ≤ u ∧ 5 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) := by
  refine ⟨perm, Finset.univ, ∅, by simp, by simp, by decide, ?_⟩
  decide
