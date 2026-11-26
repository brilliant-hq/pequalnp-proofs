import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18556

def Adj (p l : Fin 7) := p = l ∨ p = l + 1 ∨ p = l + 3
instance (p l : Fin 7) : Decidable (Adj p l) := by unfold Adj; infer_instance
def tab : List Nat := have x5 : List ℕ :=               have x5 : List ℕ :=                 have x5 : List ℕ := [(595 : ℕ), (480 : ℕ), (361 : ℕ), (244 : ℕ), (127 : ℕ)];                 (2626 : ℕ) :: (2244 : ℕ) :: (2376 : ℕ) :: (2126 : ℕ) :: (720 : ℕ) :: x5;               have x6 : List ℕ := (8488 : ℕ) :: (8368 : ℕ) :: (8250 : ℕ) :: (3008 : ℕ) :: (833 : ℕ) :: x5;               (1313 : ℕ) :: (9250 : ℕ) :: (1188 : ℕ) :: (1063 : ℕ) :: x6;             have x6 : List ℕ :=               have x6 : List ℕ := (8722 : ℕ) :: (4244 : ℕ) :: (12312 : ℕ) :: (4125 : ℕ) :: (9632 : ℕ) :: x5;               (10250 : ℕ) :: (6156 : ℕ) :: (12944 : ℕ) :: (4625 : ℕ) :: x6;             have x7 : List ℕ := (7300 : ℕ) :: (5125 : ℕ) :: (3078 : ℕ) :: (14600 : ℕ) :: (4361 : ℕ) :: x6;             (16256 : ℕ) :: (5889 : ℕ) :: (11778 : ℕ) :: (1539 : ℕ) :: x7
def bits (w : Nat) (i : Fin 14) := w.testBit i.val
def pos (p l : Fin 7) (i : Fin 14) := decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
def hasEdge (x : Fin 14 → Bool) := ∃ p l : Fin 7, Adj p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma cover (a : Fin 7 → Bool) : ∃ w ∈ tab,
    (∀ p : Fin 7, a p = true → bits w (Fin.castAdd 7 p) = true) ∧
    (∀ l : Fin 7, (∀ p : Fin 7, a p = true → ¬ Adj p l) → bits w (Fin.natAdd 7 l) = true) := by
  revert a
  decide +kernel

end PEqualNP.Outside.L_meta_18556

open PEqualNP.Outside.L_meta_18556

theorem PEqualNP.Outside.L_meta_18556 : (∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool),   (∀ (x2 x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (14 : ℕ)), x2 x4 = Bool.true → x3 x4 = Bool.true) → x1 x2 = Bool.true → x1 x3 = Bool.true) →     (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → (x1 fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) →       (∀           x4 ∈             have x5 : List ℕ :=               have x5 : List ℕ :=                 have x5 : List ℕ := [(595 : ℕ), (480 : ℕ), (361 : ℕ), (244 : ℕ), (127 : ℕ)];                 (2626 : ℕ) :: (2244 : ℕ) :: (2376 : ℕ) :: (2126 : ℕ) :: (720 : ℕ) :: x5;               have x6 : List ℕ := (8488 : ℕ) :: (8368 : ℕ) :: (8250 : ℕ) :: (3008 : ℕ) :: (833 : ℕ) :: x5;               (1313 : ℕ) :: (9250 : ℕ) :: (1188 : ℕ) :: (1063 : ℕ) :: x6;             have x6 : List ℕ :=               have x6 : List ℕ := (8722 : ℕ) :: (4244 : ℕ) :: (12312 : ℕ) :: (4125 : ℕ) :: (9632 : ℕ) :: x5;               (10250 : ℕ) :: (6156 : ℕ) :: (12944 : ℕ) :: (4625 : ℕ) :: x6;             have x7 : List ℕ := (7300 : ℕ) :: (5125 : ℕ) :: (3078 : ℕ) :: (14600 : ℕ) :: (4361 : ℕ) :: x6;             (16256 : ℕ) :: (5889 : ℕ) :: (11778 : ℕ) :: (1539 : ℕ) :: x7,           (x1 fun (x6 : Fin (14 : ℕ)) => x4.testBit ↑x6) = Bool.false) →         ∀ (x5 : Fin (14 : ℕ) → Bool), x1 x5 = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) := by
  intro f mono yes no x
  change f x = true ↔ hasEdge x
  change ∀ p l, Adj p l → f (pos p l) = true at yes
  change ∀ w ∈ tab, f (bits w) = false at no
  constructor
  · intro hf
    by_contra ne
    obtain ⟨w, hw, left, right⟩ := cover (fun p => x (Fin.castAdd 7 p))
    have bound (i : Fin 14) : x i = true → bits w i = true := by
      refine Fin.addCases (m := 7) (n := 7) (fun p => left p) (fun l hl => right l ?_) i
      intro p hp hadj
      exact ne ⟨p, l, hadj, hp, hl⟩
    exact Bool.false_ne_true ((no w hw).symm.trans (mono _ _ bound hf))
  · rintro ⟨p,l, edge, hp, hl⟩
    apply mono (pos p l) x _ (yes p l edge)
    intro i hi
    rcases of_decide_eq_true hi with h | h
    · exact h ▸ hp
    · exact h ▸ hl
