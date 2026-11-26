import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18528_aux

def graph (x : Fin 10 → Bool) := (List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))

def p0 : Equiv.Perm (Fin 10) := ⟨![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0], by decide, by decide⟩
theorem h0 (x : Fin 10 → Bool) : graph (x ∘ p0) = graph x := by
  change (((x 9 && x 6 || x 9 && x 4 || x 4 && x 3)) || (((x 6 && x 8 || x 6 && x 1 || x 1 && x 0)) || (((x 8 && x 5 || x 8 && x 3 || x 3 && x 2)) || (((x 5 && x 7 || x 5 && x 0 || x 0 && x 4)) || (((x 7 && x 9 || x 7 && x 2 || x 2 && x 1)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p1 : Equiv.Perm (Fin 10) := ⟨![7, 9, 6, 8, 5, 2, 4, 1, 3, 0], ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1], by decide, by decide⟩
theorem h1 (x : Fin 10 → Bool) : graph (x ∘ p1) = graph x := by
  change (((x 7 && x 9 || x 7 && x 2 || x 2 && x 1)) || (((x 9 && x 6 || x 9 && x 4 || x 4 && x 3)) || (((x 6 && x 8 || x 6 && x 1 || x 1 && x 0)) || (((x 8 && x 5 || x 8 && x 3 || x 3 && x 2)) || (((x 5 && x 7 || x 5 && x 0 || x 0 && x 4)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p2 : Equiv.Perm (Fin 10) := ⟨![5, 7, 9, 6, 8, 0, 2, 4, 1, 3], ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2], by decide, by decide⟩
theorem h2 (x : Fin 10 → Bool) : graph (x ∘ p2) = graph x := by
  change (((x 5 && x 7 || x 5 && x 0 || x 0 && x 4)) || (((x 7 && x 9 || x 7 && x 2 || x 2 && x 1)) || (((x 9 && x 6 || x 9 && x 4 || x 4 && x 3)) || (((x 6 && x 8 || x 6 && x 1 || x 1 && x 0)) || (((x 8 && x 5 || x 8 && x 3 || x 3 && x 2)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p3 : Equiv.Perm (Fin 10) := ⟨![8, 5, 7, 9, 6, 3, 0, 2, 4, 1], ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3], by decide, by decide⟩
theorem h3 (x : Fin 10 → Bool) : graph (x ∘ p3) = graph x := by
  change (((x 8 && x 5 || x 8 && x 3 || x 3 && x 2)) || (((x 5 && x 7 || x 5 && x 0 || x 0 && x 4)) || (((x 7 && x 9 || x 7 && x 2 || x 2 && x 1)) || (((x 9 && x 6 || x 9 && x 4 || x 4 && x 3)) || (((x 6 && x 8 || x 6 && x 1 || x 1 && x 0)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p4 : Equiv.Perm (Fin 10) := ⟨![6, 8, 5, 7, 9, 1, 3, 0, 2, 4], ![7, 5, 8, 6, 9, 2, 0, 3, 1, 4], by decide, by decide⟩
theorem h4 (x : Fin 10 → Bool) : graph (x ∘ p4) = graph x := by
  change (((x 6 && x 8 || x 6 && x 1 || x 1 && x 0)) || (((x 8 && x 5 || x 8 && x 3 || x 3 && x 2)) || (((x 5 && x 7 || x 5 && x 0 || x 0 && x 4)) || (((x 7 && x 9 || x 7 && x 2 || x 2 && x 1)) || (((x 9 && x 6 || x 9 && x 4 || x 4 && x 3)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p5 : Equiv.Perm (Fin 10) := ⟨![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], by decide, by decide⟩
theorem h5 (x : Fin 10 → Bool) : graph (x ∘ p5) = graph x := by
  change (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p6 : Equiv.Perm (Fin 10) := ⟨![3, 4, 0, 1, 2, 8, 9, 5, 6, 7], ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], by decide, by decide⟩
theorem h6 (x : Fin 10 → Bool) : graph (x ∘ p6) = graph x := by
  change (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p7 : Equiv.Perm (Fin 10) := ⟨![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7], by decide, by decide⟩
theorem h7 (x : Fin 10 → Bool) : graph (x ∘ p7) = graph x := by
  change (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p8 : Equiv.Perm (Fin 10) := ⟨![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], by decide, by decide⟩
theorem h8 (x : Fin 10 → Bool) : graph (x ∘ p8) = graph x := by
  change (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

def p9 : Equiv.Perm (Fin 10) := ⟨![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], by decide, by decide⟩
theorem h9 (x : Fin 10 → Bool) : graph (x ∘ p9) = graph x := by
  change (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false)))))) = (((x 0 && x 1 || x 0 && x 5 || x 5 && x 7)) || (((x 1 && x 2 || x 1 && x 6 || x 6 && x 8)) || (((x 2 && x 3 || x 2 && x 7 || x 7 && x 9)) || (((x 3 && x 4 || x 3 && x 8 || x 8 && x 5)) || (((x 4 && x 0 || x 4 && x 9 || x 9 && x 6)) || (false))))))
  ac_rfl

end PEqualNP.Outside.L_meta_18528_aux

open PEqualNP.Outside.L_meta_18528_aux in
theorem PEqualNP.Outside.L_meta_18528 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : Fin (10 : ℕ)), ∃ (x3 : Equiv.Perm (Fin (10 : ℕ))), x3 x2 = (9 : Fin (10 : ℕ)) ∧ ∀ (x4 : Fin (10 : ℕ) → Bool), x1 (x4 ∘ ⇑x3) = x1 x4 := by
  intro F i
  fin_cases i
  · exact ⟨p0, rfl, h0⟩
  · exact ⟨p1, rfl, h1⟩
  · exact ⟨p2, rfl, h2⟩
  · exact ⟨p3, rfl, h3⟩
  · exact ⟨p4, rfl, h4⟩
  · exact ⟨p5, rfl, h5⟩
  · exact ⟨p6, rfl, h6⟩
  · exact ⟨p7, rfl, h7⟩
  · exact ⟨p8, rfl, h8⟩
  · exact ⟨p9, rfl, h9⟩
