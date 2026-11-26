import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18528_aux

def P (x1 : Fin (10 : ℕ) → Bool) : Bool := (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))))

set_option maxRecDepth 100000 in
theorem h : ∀ (v : Fin (10 : ℕ)), ∃ (s : Equiv.Perm (Fin (10 : ℕ))), s v = (9 : Fin (10 : ℕ)) ∧ ∀ (x : Fin (10 : ℕ) → Bool), P (x ∘ ⇑s) = P x := by
  intro v
  fin_cases v
  · exact ⟨⟨![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![4, 0, 1, 6, 9, 3, 5, 2, 8, 7], ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], by decide, by decide⟩, by decide, by decide +kernel⟩
  · exact ⟨⟨![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], by decide, by decide⟩, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_18528_aux

theorem PEqualNP.Outside.L_meta_18528 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : Fin (10 : ℕ)), ∃ (x3 : Equiv.Perm (Fin (10 : ℕ))), x3 x2 = (9 : Fin (10 : ℕ)) ∧ ∀ (x4 : Fin (10 : ℕ) → Bool), x1 (x4 ∘ ⇑x3) = x1 x4 := PEqualNP.Outside.L_meta_18528_aux.h
