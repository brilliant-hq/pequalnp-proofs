import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18522_aux

def Pb (x : Fin 14 → Bool) : Bool :=
  !(List.finRange 7).any (fun p => (List.finRange 7).any (fun l =>
    (decide (p = l) || decide (p = l + 1) || decide (p = l + 3)) && x (Fin.castAdd 7 p) && x (Fin.natAdd 7 l)))

def xs (n : ℕ) : Fin 14 → Bool := fun i => n.testBit i

def chk (n : ℕ) : Bool :=
  Pb (xs n) && (List.finRange 14).all (fun i => xs n i || !Pb (Function.update (xs n) i true))

def LL : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626,
  3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632,
  10250, 11778, 12312, 12944, 14600, 16256]

theorem c0 : ∀ a < 64, ∀ b < 64, (!chk (0 + 64 * a + b) || LL.contains (0 + 64 * a + b)) = true := by decide +kernel

theorem c1 : ∀ a < 64, ∀ b < 64, (!chk (4096 + 64 * a + b) || LL.contains (4096 + 64 * a + b)) = true := by decide +kernel

theorem c2 : ∀ a < 64, ∀ b < 64, (!chk (8192 + 64 * a + b) || LL.contains (8192 + 64 * a + b)) = true := by decide +kernel

theorem c3 : ∀ a < 64, ∀ b < 64, (!chk (12288 + 64 * a + b) || LL.contains (12288 + 64 * a + b)) = true := by decide +kernel

theorem allc : ∀ n < 16384, chk n = true → n ∈ LL := by
  intro n hn h
  have e : n = 4096 * (n / 4096) + 64 * (n % 4096 / 64) + n % 64 := by omega
  have ha : n % 4096 / 64 < 64 := by omega
  have hb : n % 64 < 64 := by omega
  have hq : n / 4096 < 4 := by omega
  generalize n % 4096 / 64 = a at e ha
  generalize n % 64 = b at e hb
  generalize hk : n / 4096 = k at e hq
  subst e
  interval_cases k
  · have := c0 a ha b hb; simp_all
  · have := c1 a ha b hb; simp_all
  · have := c2 a ha b hb; simp_all
  · have := c3 a ha b hb; simp_all

theorem enc : ∀ k : ℕ, ∀ f : ℕ → Bool, ∃ n < 2 ^ k, ∀ i < k, f i = n.testBit i := by
  intro k
  induction k with
  | zero => intro f; exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    intro f
    obtain ⟨m, hm, hf⟩ := ih f
    refine ⟨m + (if f k then 2 ^ k else 0), ?_, ?_⟩
    · split <;> rw [pow_succ] <;> omega
    · intro i hi
      have hmk : m.testBit k = false := Nat.testBit_eq_false_of_lt hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · split
        · rw [add_comm, Nat.testBit_two_pow_add_gt h]; exact hf i h
        · simpa using hf i h
      · subst h
        split
        · rename_i hh; rw [add_comm, Nat.testBit_two_pow_add_eq, hmk, hh]; rfl
        · rename_i hh; simpa [hmk] using hh

theorem Pb_iff (x : Fin 14 → Bool) : Pb x = true ↔ ¬∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) x4) = Bool.true := by
  simp [Pb, List.any_eq_true]
  constructor
  · intro h a
    exact ⟨fun h1 => h a a (Or.inl (Or.inl rfl)) h1, fun b hb => h a b (by tauto)⟩
  · intro h a b hab
    rcases hab with (rfl | hab) | hab
    · exact (h a).1
    · exact (h a).2 b (Or.inl hab)
    · exact (h a).2 b (Or.inr hab)

end PEqualNP.Outside.L_meta_18522_aux

open PEqualNP.Outside.L_meta_18522_aux in
theorem PEqualNP.Outside.L_meta_18522 : ∀ (x1 : Fin (14 : ℕ) → Bool),   Maximal (fun (x2 : Fin (14 : ℕ) → Bool) => ¬∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) x1 →     ∃       x3 ∈         have x4 : List ℕ :=           have x4 : List ℕ :=             have x4 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x4;           have x5 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x4;           (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x5;         have x5 : List ℕ :=           have x5 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x4;           (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x5;         have x6 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x5;         (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x6,       ∀ (x4 : Fin (14 : ℕ)), x1 x4 = x3.testBit ↑x4 := by
  intro x hmax
  obtain ⟨n, hn, hx⟩ := enc 14 (fun i => if h : i < 14 then x ⟨i, h⟩ else false)
  have hxe : x = xs n := by
    funext i
    have := hx i i.isLt
    simpa [xs] using this
  subst hxe
  have hc : chk n = true := by
    have h1 := hmax.1
    have h2 := hmax.2
    simp only [chk, Bool.and_eq_true, List.all_eq_true]
    refine ⟨(Pb_iff _).2 h1, ?_⟩
    intro i _
    by_cases hi : xs n i = true
    · simp [hi]
    · have hp : Pb (Function.update (xs n) i true) = false := by
        by_contra hne
        have hP := (Pb_iff _).1 (by simpa using hne)
        have hle : xs n ≤ Function.update (xs n) i true := by
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        have := h2 hP hle i
        simp at this
        exact hi (by revert this; cases xs n i <;> simp)
      simp [hp]
  have hm := allc n (by simpa using hn) hc
  refine ⟨n, ?_, fun i => rfl⟩
  simp only [LL, List.mem_cons, List.not_mem_nil, or_false] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega
