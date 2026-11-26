import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18556

abbrev Input := Fin 14 → Bool
abbrev Half := Fin 7 → Bool

def left (p : Fin 7) : Fin 14 := Fin.castAdd 7 p
def right (q : Fin 7) : Fin 14 := Fin.natAdd 7 q
def adj (p q : Fin 7) : Prop := p = q ∨ p = q + 1 ∨ p = q + 3

instance (p q : Fin 7) : Decidable (adj p q) := by
  unfold adj
  infer_instance

def good (x : Input) : Prop :=
  ¬∃ p q : Fin 7, adj p q ∧ x (left p) = true ∧ x (right q) = true

def leftBits (x : Input) : Half := fun p => x (left p)
def clear (t : Half) (q : Fin 7) : Bool := decide (∀ p : Fin 7, t p = true → ¬adj p q)
def frame (t : Half) : Input := Fin.append t (clear t)
def saturated (t : Half) : Prop :=
  ∀ p : Fin 7, t p = false → ∃ q : Fin 7, clear t q = true ∧ adj p q

instance (t : Half) : Decidable (saturated t) := by
  unfold saturated
  infer_instance

def patterns : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 45000000 in
theorem framesCovered : ∀ t : Half, saturated t →
    patterns.any (fun m => decide (∀ i : Fin 14, frame t i = m.testBit i.val)) = true := by
  decide +kernel

theorem leftInj : Function.Injective left := by
  intro p q e
  exact Fin.ext (congrArg (fun i : Fin 14 => i.val) e)

theorem rightInj : Function.Injective right := by
  intro p q e
  have h := congrArg Fin.val e
  change 7 + p.val = 7 + q.val at h
  exact Fin.ext (by omega)

theorem across (p q : Fin 7) : left p ≠ right q := by
  intro eq
  have h := congrArg Fin.val eq
  change p.val = 7 + q.val at h
  have bound := p.isLt
  omega

theorem added {x : Input} (h : Maximal good x) (i : Fin 14)
    (safe : good (Function.update x i true)) : x i = true := by
  have below : x ≤ Function.update x i true := by
    intro j
    by_cases eq : j = i
    · subst j
      simp
    · simp [Function.update_of_ne eq]
  have value := h.2 safe below i
  simp only [Function.update_self] at value
  cases e : x i
  · exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by simpa [e] using value))
  · rfl

theorem rightExact {x : Input} (h : Maximal good x) (q : Fin 7) :
    x (right q) = clear (leftBits x) q := by
  by_cases no : ∀ p : Fin 7, x (left p) = true → ¬adj p q
  · have safe : good (Function.update x (right q) true) := by
      rintro ⟨p, r, edge, pl, qr⟩
      have pTrue : x (left p) = true := by
        simpa only [Function.update_of_ne (across p q)] using pl
      by_cases eq : r = q
      · subst r
        exact no p pTrue edge
      · have different : right r ≠ right q := fun e => eq (rightInj e)
        have rTrue : x (right r) = true := by
          simpa only [Function.update_of_ne different] using qr
        exact h.1 ⟨p, r, edge, pTrue, rTrue⟩
    have yes := added h (right q) safe
    rw [yes]
    exact (decide_eq_true no).symm
  · have noRight : x (right q) = false := by
      cases e : x (right q)
      · rfl
      · exact False.elim (no fun p yes edge => h.1 ⟨p, q, edge, yes, e⟩)
    rw [noRight]
    exact (decide_eq_false no).symm

theorem leftClosed {x : Input} (h : Maximal good x) : saturated (leftBits x) := by
  intro p absent
  by_contra missing
  have safe : good (Function.update x (left p) true) := by
    rintro ⟨r, q, edge, pl, qr⟩
    have qTrue : x (right q) = true := by
      simpa only [Function.update_of_ne (Ne.symm (across p q))] using qr
    by_cases eq : r = p
    · subst r
      exact missing ⟨q, (rightExact h q).symm.trans qTrue, edge⟩
    · have different : left r ≠ left p := fun e => eq (leftInj e)
      have rTrue : x (left r) = true := by
        simpa only [Function.update_of_ne different] using pl
      exact h.1 ⟨r, q, edge, rTrue, qTrue⟩
  exact Bool.noConfusion (absent.symm.trans (added h (left p) safe))

theorem reconstruct {x : Input} (h : Maximal good x) : x = frame (leftBits x) := by
  funext i
  refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
  · intro p
    simp [frame, leftBits, left]
  · intro q
    simpa only [frame, right, Fin.append_right] using rightExact h q

def stated : List ℕ := [16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127]

theorem coverage : patterns.all (fun m => decide (m ∈ stated)) = true := by decide +kernel

theorem identification {x : Input} (h : Maximal good x) :
    ∃ m ∈ stated, x = fun i : Fin 14 => m.testBit i.val := by
  obtain ⟨m, hm, ok⟩ := List.any_eq_true.mp (framesCovered (leftBits x) (leftClosed h))
  have occurs : m ∈ stated := of_decide_eq_true (List.all_eq_true.mp coverage m hm)
  exact ⟨m, occurs, (reconstruct h).trans (funext (of_decide_eq_true ok))⟩

theorem supportOrder {x y : Input} (h : x ≤ y) :
    ∀ i, x i = true → y i = true := by
  intro i yes
  have le := h i
  rw [yes] at le
  cases out : y i
  · exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by simpa [out] using le))
  · rfl

end PEqualNP.Outside.L_meta_18556

open PEqualNP.Outside.L_meta_18556 in
theorem PEqualNP.Outside.L_meta_18556 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool),   (∀ (x2 x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (14 : ℕ)), x2 x4 = Bool.true → x3 x4 = Bool.true) → x1 x2 = Bool.true → x1 x3 = Bool.true) →     (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → (x1 fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) →       (∀           x4 ∈             have x5 : List ℕ :=               have x5 : List ℕ :=                 have x5 : List ℕ := [(595 : ℕ), (480 : ℕ), (361 : ℕ), (244 : ℕ), (127 : ℕ)];                 (2626 : ℕ) :: (2244 : ℕ) :: (2376 : ℕ) :: (2126 : ℕ) :: (720 : ℕ) :: x5;               have x6 : List ℕ := (8488 : ℕ) :: (8368 : ℕ) :: (8250 : ℕ) :: (3008 : ℕ) :: (833 : ℕ) :: x5;               (1313 : ℕ) :: (9250 : ℕ) :: (1188 : ℕ) :: (1063 : ℕ) :: x6;             have x6 : List ℕ :=               have x6 : List ℕ := (8722 : ℕ) :: (4244 : ℕ) :: (12312 : ℕ) :: (4125 : ℕ) :: (9632 : ℕ) :: x5;               (10250 : ℕ) :: (6156 : ℕ) :: (12944 : ℕ) :: (4625 : ℕ) :: x6;             have x7 : List ℕ := (7300 : ℕ) :: (5125 : ℕ) :: (3078 : ℕ) :: (14600 : ℕ) :: (4361 : ℕ) :: x6;             (16256 : ℕ) :: (5889 : ℕ) :: (11778 : ℕ) :: (1539 : ℕ) :: x7,           (x1 fun (x6 : Fin (14 : ℕ)) => x4.testBit ↑x6) = Bool.false) →         ∀ (x5 : Fin (14 : ℕ) → Bool), x1 x5 = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true := by
  intro f mono positive negative x
  change (∀ m ∈ stated, f (fun i : Fin 14 => m.testBit i.val) = false) at negative
  change f x = true ↔ ∃ p q : Fin 7, adj p q ∧ x (left p) = true ∧ x (right q) = true
  constructor
  · intro hit
    classical
    by_contra independent
    have goodX : good x := independent
    obtain ⟨y, order, maximal⟩ := Finite.exists_le_maximal goodX
    obtain ⟨m, hm, rfl⟩ := identification maximal
    have yes := mono x (fun i : Fin 14 => m.testBit i.val) (supportOrder order) hit
    cases (negative m hm).symm.trans yes
  · rintro ⟨p, q, hr, hp, hq⟩
    let y : Input := fun i => decide (i = left p ∨ i = right q)
    have pairGood : f y = true := positive p q hr
    apply mono y x ?_ pairGood
    intro i hi
    have endpoint : i = left p ∨ i = right q := of_decide_eq_true hi
    rcases endpoint with rfl | rfl
    · exact hp
    · exact hq
