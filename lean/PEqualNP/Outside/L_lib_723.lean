import PEqualNP.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Field

namespace PEqualNP.Outside.L_lib_723_aux

open Classical

private lemma testBit_eq_decide_div_mod (x len : ℕ) :
    x.testBit len = decide ((x / 2 ^ len) % 2 = 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ len) with h | h <;> simp [h]

private lemma mod_two_pow_succ (x len : ℕ) :
    x % 2 ^ (len + 1) = x % 2 ^ len + if x.testBit len then 2 ^ len else 0 := by
  rw [testBit_eq_decide_div_mod]
  have hdiv : x = 2 ^ len * (x / 2 ^ len) + x % 2 ^ len := (Nat.div_add_mod x (2 ^ len)).symm
  have hdiv2 : x / 2 ^ len = 2 * ((x / 2 ^ len) / 2) + (x / 2 ^ len) % 2 :=
    (Nat.div_add_mod (x / 2 ^ len) 2).symm
  have hlt1 : x % 2 ^ len < 2 ^ len := Nat.mod_lt x (Nat.two_pow_pos len)
  have hsplit : x = 2 ^ (len + 1) * ((x / 2 ^ len) / 2) +
      (x % 2 ^ len + 2 ^ len * ((x / 2 ^ len) % 2)) := by
    calc
      x = 2 ^ len * (2 * ((x / 2 ^ len) / 2) + (x / 2 ^ len) % 2) + x % 2 ^ len := by
        conv_lhs => rw [hdiv, hdiv2]
      _ = 2 ^ (len + 1) * ((x / 2 ^ len) / 2) +
            (x % 2 ^ len + 2 ^ len * ((x / 2 ^ len) % 2)) := by
        rw [pow_succ]
        ring
  have hrem_lt : x % 2 ^ len + 2 ^ len * ((x / 2 ^ len) % 2) < 2 ^ (len + 1) := by
    rw [pow_succ]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ len) with h | h <;> rw [h] <;> omega
  have hmod : x % 2 ^ (len + 1) = x % 2 ^ len + 2 ^ len * ((x / 2 ^ len) % 2) := by
    conv_lhs => rw [hsplit]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
  rw [hmod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ len) with h | h <;> simp [h]

structure LinSys (s : ℕ) where
  E : ℕ
  R : ℕ
  PL : Fin E → Fin s → ℕ
  PR : Fin E → Fin s → ℕ
  Q : Fin E → Fin R → ℕ
  cL : Fin E → ℕ
  cR : Fin E → ℕ

def Solves {s : ℕ} (sys : LinSys s) (d : Fin s → ℕ) : Prop :=
  ∃ y : Fin sys.R → ℕ, ∀ i : Fin sys.E,
    (∑ j : Fin s, sys.PL i j * d j) + sys.cL i =
    (∑ j : Fin s, sys.PR i j * d j) + (∑ r : Fin sys.R, sys.Q i r * y r) + sys.cR i

def carryBound {s : ℕ} (sys : LinSys s) (i : Fin sys.E) : ℕ :=
  sys.cL i + sys.cR i + (∑ j : Fin s, sys.PL i j) + (∑ j : Fin s, sys.PR i j) +
    (∑ r : Fin sys.R, sys.Q i r)

abbrev CarryVec {s : ℕ} (sys : LinSys s) := ∀ i : Fin sys.E, Fin (2 * carryBound sys i + 1)

def decCarry {s : ℕ} (sys : LinSys s) (i : Fin sys.E)
    (u : Fin (2 * carryBound sys i + 1)) : ℤ :=
  (u.val : ℤ) - (carryBound sys i : ℤ)

private lemma exists_carry_of_bounds {s : ℕ} (sys : LinSys s) (i : Fin sys.E) (z : ℤ)
    (hlo : -(carryBound sys i : ℤ) ≤ z) (hhi : z ≤ (carryBound sys i : ℤ)) :
    ∃ u : Fin (2 * carryBound sys i + 1), decCarry sys i u = z := by
  refine ⟨⟨(z + (carryBound sys i : ℤ)).toNat, by omega⟩, ?_⟩
  simp only [decCarry]
  omega

abbrev SubState {s : ℕ} (sys : LinSys s) := CarryVec sys → Bool

noncomputable def startSub {s : ℕ} (sys : LinSys s) : SubState sys :=
  fun γ => decide (∀ i : Fin sys.E,
    decCarry sys i (γ i) = (sys.cL i : ℤ) - (sys.cR i : ℤ))

noncomputable def stepSub {s : ℕ} (sys : LinSys s)
    (S : SubState sys) (inp : Fin s → Bool) : SubState sys :=
  fun γ' => decide (∃ γ : CarryVec sys, S γ = true ∧ ∃ η : Fin sys.R → Bool,
    ∀ i : Fin sys.E,
      2 * decCarry sys i (γ' i) =
        decCarry sys i (γ i)
        + (∑ j : Fin s, if inp j then (sys.PL i j : ℤ) else 0)
        - (∑ j : Fin s, if inp j then (sys.PR i j : ℤ) else 0)
        - (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0))

noncomputable def accSub {s : ℕ} (sys : LinSys s) (S : SubState sys) : Bool :=
  decide (∃ γ : CarryVec sys, S γ = true ∧ ∃ yHi : Fin sys.R → ℕ,
    ∀ i : Fin sys.E,
      decCarry sys i (γ i) = ∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yHi r : ℤ))

private lemma sum_mul_le_mul_pow {α : Type*} [Fintype α] (w u : α → ℕ) (len : ℕ)
    (hu : ∀ a, u a < 2 ^ len) :
    (∑ a : α, (w a : ℤ) * (u a : ℤ)) ≤ (∑ a : α, (w a : ℤ)) * (2 : ℤ) ^ len := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 : (0 : ℤ) ≤ (w a : ℤ) := Int.natCast_nonneg _
  have h2 : (u a : ℤ) ≤ (2 : ℤ) ^ len := by exact_mod_cast le_of_lt (hu a)
  exact mul_le_mul_of_nonneg_left h2 h1

private lemma sum_mul_nonneg {α : Type*} [Fintype α] (w u : α → ℕ) :
    (0 : ℤ) ≤ ∑ a : α, (w a : ℤ) * (u a : ℤ) := by
  exact Finset.sum_nonneg fun a _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

private lemma carry_rhs_bounds {s : ℕ} (sys : LinSys s) (i : Fin sys.E) (len : ℕ)
    (u : Fin s → ℕ) (v : Fin sys.R → ℕ)
    (hu : ∀ j, u j < 2 ^ len) (hv : ∀ r, v r < 2 ^ len) :
    -(carryBound sys i : ℤ) * (2 : ℤ) ^ len ≤
      ((sys.cL i : ℤ) - (sys.cR i : ℤ))
      + (∑ j : Fin s, (sys.PL i j : ℤ) * (u j : ℤ))
      - (∑ j : Fin s, (sys.PR i j : ℤ) * (u j : ℤ))
      - (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (v r : ℤ)) ∧
    ((sys.cL i : ℤ) - (sys.cR i : ℤ))
      + (∑ j : Fin s, (sys.PL i j : ℤ) * (u j : ℤ))
      - (∑ j : Fin s, (sys.PR i j : ℤ) * (u j : ℤ))
      - (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (v r : ℤ)) ≤
      (carryBound sys i : ℤ) * (2 : ℤ) ^ len := by
  have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ len := by
    exact_mod_cast Nat.one_le_two_pow
  have hPL0 : (0 : ℤ) ≤ ∑ j : Fin s, (sys.PL i j : ℤ) * (u j : ℤ) := sum_mul_nonneg _ _
  have hPR0 : (0 : ℤ) ≤ ∑ j : Fin s, (sys.PR i j : ℤ) * (u j : ℤ) := sum_mul_nonneg _ _
  have hQ0 : (0 : ℤ) ≤ ∑ r : Fin sys.R, (sys.Q i r : ℤ) * (v r : ℤ) := sum_mul_nonneg _ _
  have hPL1 := sum_mul_le_mul_pow (sys.PL i) u len hu
  have hPR1 := sum_mul_le_mul_pow (sys.PR i) u len hu
  have hQ1 := sum_mul_le_mul_pow (sys.Q i) v len hv
  have hcL0 : (0 : ℤ) ≤ (sys.cL i : ℤ) := Int.natCast_nonneg _
  have hcR0 : (0 : ℤ) ≤ (sys.cR i : ℤ) := Int.natCast_nonneg _
  have hcL1 : (sys.cL i : ℤ) ≤ (sys.cL i : ℤ) * (2 : ℤ) ^ len := by nlinarith
  have hcR1 : (sys.cR i : ℤ) ≤ (sys.cR i : ℤ) * (2 : ℤ) ^ len := by nlinarith
  have hsumPL0 : (0 : ℤ) ≤ ∑ j : Fin s, (sys.PL i j : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hsumPR0 : (0 : ℤ) ≤ ∑ j : Fin s, (sys.PR i j : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hsumQ0 : (0 : ℤ) ≤ ∑ r : Fin sys.R, (sys.Q i r : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hB : (carryBound sys i : ℤ) =
      (sys.cL i : ℤ) + (sys.cR i : ℤ) + (∑ j : Fin s, (sys.PL i j : ℤ)) +
      (∑ j : Fin s, (sys.PR i j : ℤ)) + (∑ r : Fin sys.R, (sys.Q i r : ℤ)) := by
    simp [carryBound]
  constructor <;> nlinarith

private lemma sum_if_mul_pow {α : Type*} [Fintype α] (w : α → ℕ) (b : α → Bool) (len : ℕ) :
    (2 : ℤ) ^ len * (∑ a : α, if b a then (w a : ℤ) else 0) =
      ∑ a : α, (w a : ℤ) * ((if b a then 2 ^ len else 0 : ℕ) : ℤ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases b a <;> simp [mul_comm]

private lemma runSub_invariant {s : ℕ} (sys : LinSys s) (d : Fin s → ℕ) :
    ∀ (len : ℕ) (γ : CarryVec sys),
      ((List.range len).foldl
        (fun st pos => stepSub sys st (fun j => (d j).testBit pos)) (startSub sys)) γ = true ↔
      ∃ yLo : Fin sys.R → ℕ, (∀ r, yLo r < 2 ^ len) ∧
        ∀ i : Fin sys.E,
          (2 : ℤ) ^ len * decCarry sys i (γ i) =
            ((sys.cL i : ℤ) - (sys.cR i : ℤ))
            + (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
            - (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
            - (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) := by
  intro len
  induction len with
  | zero =>
    intro γ
    simp only [List.range_zero, List.foldl_nil, startSub, decide_eq_true_eq, pow_zero, one_mul,
      Nat.mod_one, Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
    constructor
    · intro h
      refine ⟨fun _ => 0, fun _ => Nat.zero_lt_one, fun i => ?_⟩
      simpa using h i
    · rintro ⟨yLo, hy, h⟩ i
      have hy0 : ∀ r, yLo r = 0 := fun r => Nat.lt_one_iff.mp (hy r)
      have hi := h i
      simp [hy0] at hi
      exact hi
  | succ len ih =>
    intro γ'
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set S := (List.range len).foldl
      (fun st pos => stepSub sys st (fun j => (d j).testBit pos)) (startSub sys)
    simp only [stepSub, decide_eq_true_eq]
    constructor
    · rintro ⟨γ, hS, η, hstep⟩
      rcases (ih γ).mp hS with ⟨yLo, hyLo, hγ⟩
      refine ⟨fun r => yLo r + if η r then 2 ^ len else 0, ?_, ?_⟩
      · intro r
        have := hyLo r
        cases hη : η r <;> simp [hη, pow_succ] <;> omega
      · intro i
        have h1 := hstep i
        have h2 := hγ i
        have h3 : (2 : ℤ) ^ (len + 1) * decCarry sys i (γ' i) =
            (2 : ℤ) ^ len * (2 * decCarry sys i (γ' i)) := by
          rw [pow_succ]
          ring
        rw [h3, h1]
        have hP1 : (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PL i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hP2 : (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PR i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) *
            ((yLo r + if η r then 2 ^ len else 0 : ℕ) : ℤ)) =
            (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) +
            (2 : ℤ) ^ len * (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          push_cast
          ring
        rw [hP1, hP2, hQ]
        linarith
    · rintro ⟨yLo', hyLo', hγ'⟩
      let yLo : Fin sys.R → ℕ := fun r => yLo' r % 2 ^ len
      let η : Fin sys.R → Bool := fun r => (yLo' r).testBit len
      have hyLo_lt : ∀ r, yLo r < 2 ^ len := fun r => Nat.mod_lt _ (Nat.two_pow_pos len)
      have hyLo_split : ∀ r, yLo' r = yLo r + if η r then 2 ^ len else 0 := by
        intro r
        have hmod := mod_two_pow_succ (yLo' r) len
        rw [Nat.mod_eq_of_lt (hyLo' r)] at hmod
        exact hmod
      have hz_exists : ∀ i : Fin sys.E, ∃ u : Fin (2 * carryBound sys i + 1),
          decCarry sys i u =
            2 * decCarry sys i (γ' i)
            - (∑ j : Fin s, if (d j).testBit len then (sys.PL i j : ℤ) else 0)
            + (∑ j : Fin s, if (d j).testBit len then (sys.PR i j : ℤ) else 0)
            + (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0) := by
        intro i
        set z : ℤ :=
          2 * decCarry sys i (γ' i)
          - (∑ j : Fin s, if (d j).testBit len then (sys.PL i j : ℤ) else 0)
          + (∑ j : Fin s, if (d j).testBit len then (sys.PR i j : ℤ) else 0)
          + (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0)
        have hP1 : (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PL i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hP2 : (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PR i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo' r : ℤ)) =
            (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) +
            (2 : ℤ) ^ len * (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hyLo_split r]
          push_cast
          ring
        have hmul : (2 : ℤ) ^ len * z =
            ((sys.cL i : ℤ) - (sys.cR i : ℤ))
            + (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
            - (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
            - (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) := by
          have hi := hγ' i
          have hpow : (2 : ℤ) ^ (len + 1) * decCarry sys i (γ' i) =
              (2 : ℤ) ^ len * (2 * decCarry sys i (γ' i)) := by
            rw [pow_succ]
            ring
          rw [hpow, hP1, hP2, hQ] at hi
          dsimp only [z]
          linarith
        have hbounds := carry_rhs_bounds sys i len (fun j => d j % 2 ^ len) yLo
          (fun j => Nat.mod_lt _ (Nat.two_pow_pos len)) hyLo_lt
        rw [← hmul] at hbounds
        have hpos : (0 : ℤ) < (2 : ℤ) ^ len := by
          exact_mod_cast Nat.two_pow_pos len
        have hlo : -(carryBound sys i : ℤ) ≤ z := by nlinarith
        have hhi : z ≤ (carryBound sys i : ℤ) := by nlinarith
        exact exists_carry_of_bounds sys i z hlo hhi
      choose γ hγ_eq using hz_exists
      refine ⟨γ, ?_, η, ?_⟩
      · rw [ih γ]
        refine ⟨yLo, hyLo_lt, fun i => ?_⟩
        have hP1 : (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PL i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hP2 : (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ (len + 1) : ℕ) : ℤ)) =
            (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ)) +
            (2 : ℤ) ^ len * (∑ j : Fin s, if (d j).testBit len then (sys.PR i j : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mod_two_pow_succ]
          push_cast
          ring
        have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo' r : ℤ)) =
            (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) +
            (2 : ℤ) ^ len * (∑ r : Fin sys.R, if η r then (sys.Q i r : ℤ) else 0) := by
          rw [sum_if_mul_pow, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hyLo_split r]
          push_cast
          ring
        have hi := hγ' i
        have hpow : (2 : ℤ) ^ (len + 1) * decCarry sys i (γ' i) =
            (2 : ℤ) ^ len * (2 * decCarry sys i (γ' i)) := by
          rw [pow_succ]
          ring
        rw [hpow, hP1, hP2, hQ] at hi
        rw [hγ_eq i]
        linarith
      · intro i
        linarith [hγ_eq i]

private lemma accSub_iff_solves {s : ℕ} (sys : LinSys s) (d : Fin s → ℕ) (len : ℕ)
    (hd : ∀ j, d j < 2 ^ len) :
    accSub sys ((List.range len).foldl
      (fun st pos => stepSub sys st (fun j => (d j).testBit pos)) (startSub sys)) = true ↔
    Solves sys d := by
  simp only [accSub, decide_eq_true_eq]
  have hd_mod : ∀ j, d j % 2 ^ len = d j := fun j => Nat.mod_eq_of_lt (hd j)
  constructor
  · rintro ⟨γ, hS, yHi, hγHi⟩
    rcases (runSub_invariant sys d len γ).mp hS with ⟨yLo, _, hγLo⟩
    refine ⟨fun r => yLo r + 2 ^ len * yHi r, fun i => ?_⟩
    have h1 := hγLo i
    have h2 := hγHi i
    rw [h2] at h1
    have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) * ((yLo r : ℤ) + (2 : ℤ) ^ len * (yHi r : ℤ))) =
        (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) +
        (2 : ℤ) ^ len * (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yHi r : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hz : ((∑ j : Fin s, sys.PL i j * d j) + sys.cL i : ℤ) =
        ((∑ j : Fin s, sys.PR i j * d j) +
          (∑ r : Fin sys.R, sys.Q i r * (yLo r + 2 ^ len * yHi r)) + sys.cR i : ℤ) := by
      push_cast
      simp only [hd_mod] at h1
      rw [hQ]
      linarith
    exact_mod_cast hz
  · rintro ⟨y, hy⟩
    let yLo : Fin sys.R → ℕ := fun r => y r % 2 ^ len
    let yHi : Fin sys.R → ℕ := fun r => y r / 2 ^ len
    have hyLo_lt : ∀ r, yLo r < 2 ^ len := fun r => Nat.mod_lt _ (Nat.two_pow_pos len)
    have hy_split : ∀ r, y r = yLo r + 2 ^ len * yHi r := fun r => by
      have := Nat.div_add_mod (y r) (2 ^ len)
      dsimp only [yLo, yHi]
      omega
    have hγ_ex : ∀ i : Fin sys.E, ∃ u : Fin (2 * carryBound sys i + 1),
        decCarry sys i u = ∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yHi r : ℤ) := by
      intro i
      set z : ℤ := ∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yHi r : ℤ)
      have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (y r : ℤ)) =
          (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) + (2 : ℤ) ^ len * z := by
        dsimp only [z]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hy_split r]
        push_cast
        ring
      have hi : ((∑ j : Fin s, sys.PL i j * d j) + sys.cL i : ℤ) =
          ((∑ j : Fin s, sys.PR i j * d j) +
            (∑ r : Fin sys.R, sys.Q i r * y r) + sys.cR i : ℤ) := by
        exact_mod_cast hy i
      push_cast at hi
      have hmul : (2 : ℤ) ^ len * z =
          ((sys.cL i : ℤ) - (sys.cR i : ℤ))
          + (∑ j : Fin s, (sys.PL i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
          - (∑ j : Fin s, (sys.PR i j : ℤ) * ((d j % 2 ^ len : ℕ) : ℤ))
          - (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) := by
        simp only [hd_mod]
        linarith
      have hbounds := carry_rhs_bounds sys i len (fun j => d j % 2 ^ len) yLo
        (fun j => Nat.mod_lt _ (Nat.two_pow_pos len)) hyLo_lt
      rw [← hmul] at hbounds
      have hpos : (0 : ℤ) < (2 : ℤ) ^ len := by exact_mod_cast Nat.two_pow_pos len
      exact exists_carry_of_bounds sys i z (by nlinarith) (by nlinarith)
    choose γ hγ_eq using hγ_ex
    refine ⟨γ, ?_, yHi, hγ_eq⟩
    rw [runSub_invariant sys d len γ]
    refine ⟨yLo, hyLo_lt, fun i => ?_⟩
    rw [hγ_eq i]
    have hQ : (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (y r : ℤ)) =
        (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yLo r : ℤ)) +
        (2 : ℤ) ^ len * (∑ r : Fin sys.R, (sys.Q i r : ℤ) * (yHi r : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hy_split r]
      push_cast
      ring
    have hi : ((∑ j : Fin s, sys.PL i j * d j) + sys.cL i : ℤ) =
        ((∑ j : Fin s, sys.PR i j * d j) +
          (∑ r : Fin sys.R, sys.Q i r * y r) + sys.cR i : ℤ) := by
      exact_mod_cast hy i
    push_cast at hi
    simp only [hd_mod]
    linarith

private lemma foldl_prod_coord {ι : Type*} {s : ℕ} (fam : ι → LinSys s)
    (l : List ℕ) (d : Fin s → ℕ) (st0 : ∀ k : ι, SubState (fam k)) (k : ι) :
    (l.foldl (fun st pos k' => stepSub (fam k') (st k') (fun j => (d j).testBit pos)) st0) k =
      l.foldl (fun st pos => stepSub (fam k) st (fun j => (d j).testBit pos)) (st0 k) := by
  induction l generalizing st0 with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.foldl_cons]
    exact ih _

private lemma foldl_equiv {α β : Type*} (e : α ≃ β) (l : List ℕ)
    (f : α → ℕ → α) (a0 : α) :
    l.foldl (fun b pos => e (f (e.symm b) pos)) (e a0) = e (l.foldl f a0) := by
  induction l generalizing a0 with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.foldl_cons, Equiv.symm_apply_apply]
    exact ih _

private lemma dfa_of_linSys_family {s : ℕ} {ι : Type} [Fintype ι] (fam : ι → LinSys s) :
    ∃ (states : ℕ) (start : Fin states)
      (step : Fin states → (Fin s → Bool) → Fin states)
      (accept : Fin states → Bool),
      ∀ (depths : Fin s → ℕ) (len : ℕ), (∀ j, depths j < 2 ^ len) →
        let finish := (List.range len).foldl (fun state pos =>
          step state (fun j => (depths j).testBit pos)) start
        (accept finish = true ↔ ∃ k : ι, Solves (fam k) depths) := by
  let ProdState := ∀ k : ι, SubState (fam k)
  let e : ProdState ≃ Fin (Fintype.card ProdState) := Fintype.equivFin ProdState
  let startP : ProdState := fun k => startSub (fam k)
  let stepP : ProdState → (Fin s → Bool) → ProdState :=
    fun st inp k => stepSub (fam k) (st k) inp
  let acceptP : ProdState → Bool := fun st => decide (∃ k : ι, accSub (fam k) (st k) = true)
  refine ⟨Fintype.card ProdState, e startP,
    fun st inp => e (stepP (e.symm st) inp),
    fun st => acceptP (e.symm st), ?_⟩
  intro depths len hlen
  dsimp only
  have hfold : (List.range len).foldl
      (fun state pos => e (stepP (e.symm state) (fun j => (depths j).testBit pos))) (e startP) =
      e ((List.range len).foldl
        (fun st pos => stepP st (fun j => (depths j).testBit pos)) startP) :=
    foldl_equiv e (List.range len) (fun st pos => stepP st (fun j => (depths j).testBit pos)) startP
  rw [hfold, Equiv.symm_apply_apply]
  simp only [acceptP, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk⟩
    rw [foldl_prod_coord fam (List.range len) depths startP k] at hk
    exact ⟨k, (accSub_iff_solves (fam k) depths len hlen).mp hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [foldl_prod_coord fam (List.range len) depths startP k]
    exact (accSub_iff_solves (fam k) depths len hlen).mpr hk

noncomputable def mkLinSys {s : ℕ} {EqIdx VarIdx : Type} [Fintype EqIdx] [Fintype VarIdx]
    (PL PR : EqIdx → Fin s → ℕ) (Q : EqIdx → VarIdx → ℕ)
    (cL cR : EqIdx → ℕ) : LinSys s where
  E := Fintype.card EqIdx
  R := Fintype.card VarIdx
  PL := fun i j => PL ((Fintype.equivFin EqIdx).symm i) j
  PR := fun i j => PR ((Fintype.equivFin EqIdx).symm i) j
  Q := fun i r => Q ((Fintype.equivFin EqIdx).symm i) ((Fintype.equivFin VarIdx).symm r)
  cL := fun i => cL ((Fintype.equivFin EqIdx).symm i)
  cR := fun i => cR ((Fintype.equivFin EqIdx).symm i)

private lemma solves_mkLinSys {s : ℕ} {EqIdx VarIdx : Type} [Fintype EqIdx] [Fintype VarIdx]
    (PL PR : EqIdx → Fin s → ℕ) (Q : EqIdx → VarIdx → ℕ)
    (cL cR : EqIdx → ℕ) (d : Fin s → ℕ) :
    Solves (mkLinSys PL PR Q cL cR) d ↔
      ∃ y : VarIdx → ℕ, ∀ i : EqIdx,
        (∑ j : Fin s, PL i j * d j) + cL i =
        (∑ j : Fin s, PR i j * d j) + (∑ r : VarIdx, Q i r * y r) + cR i := by
  let eE := Fintype.equivFin EqIdx
  let eR := Fintype.equivFin VarIdx
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun r => y (eR r), fun i => ?_⟩
    have hi := hy (eE i)
    dsimp only [mkLinSys] at hi
    rw [Equiv.symm_apply_apply] at hi
    have hsum : (∑ r : Fin (Fintype.card VarIdx), Q i (eR.symm r) * y r) =
        ∑ r : VarIdx, Q i r * y (eR r) := by
      refine Fintype.sum_equiv eR.symm _ _ fun r => ?_
      simp
    convert hi using 1
    congr 1
    congr 1
    exact hsum.symm
  · rintro ⟨y, hy⟩
    refine ⟨fun r => y (eR.symm r), fun i => ?_⟩
    have hi := hy (eE.symm i)
    have hsum : (∑ r : Fin (Fintype.card VarIdx), Q (eE.symm i) (eR.symm r) * y (eR.symm r)) =
        ∑ r : VarIdx, Q (eE.symm i) r * y r := by
      refine Fintype.sum_equiv eR.symm _ _ fun r => rfl
    change (∑ j : Fin s, PL (eE.symm i) j * d j) + cL (eE.symm i) =
      (∑ j : Fin s, PR (eE.symm i) j * d j) +
        (∑ r : Fin (Fintype.card VarIdx), Q (eE.symm i) (eR.symm r) * y (eR.symm r)) +
        cR (eE.symm i)
    rw [hsum]
    exact hi

def mass (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Bool => ∀ c ∈ A,
    x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2)).card

def nonTaut {n : ℕ} (c : (Fin n × Bool) × (Fin n × Bool)) : Bool :=
  decide (¬ (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2))

def stripTaut {n : ℕ} (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    Finset ((Fin n × Bool) × (Fin n × Bool)) :=
  A.filter (fun c => nonTaut c = true)

private lemma mass_stripTaut {n : ℕ} (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    mass n (stripTaut A) = mass n A := by
  unfold mass stripTaut
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, nonTaut, decide_eq_true_eq]
  constructor
  · intro h c hc
    by_cases ht : c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2
    · rcases ht with ⟨h1, h2⟩
      rw [← h1]
      by_cases hx : x c.1.1 = c.1.2
      · right
        rw [hx]
        exact h2
      · left
        exact hx
    · exact h c ⟨hc, ht⟩
  · intro h c hc
    exact h c hc.1

def clauseVars {n : ℕ} (c : (Fin n × Bool) × (Fin n × Bool)) : Finset (Fin n) :=
  {c.1.1, c.2.1}

def IsVarDisjoint {n : ℕ} (M : Finset ((Fin n × Bool) × (Fin n × Bool))) : Prop :=
  ∀ c1 ∈ M, ∀ c2 ∈ M, c1 ≠ c2 → Disjoint (clauseVars c1) (clauseVars c2)

private lemma card_split_finset {n : ℕ} (S : Finset (Fin n))
    (P : ({i : Fin n // i ∈ S} → Bool) → Prop)
    (Q : ({i : Fin n // i ∉ S} → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter (fun x : Fin n → Bool =>
      P (fun i => x i.1) ∧ Q (fun i => x i.1))).card =
    (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  let e : (Fin n → Bool) ≃ ({i : Fin n // i ∈ S} → Bool) × ({i : Fin n // i ∉ S} → Bool) :=
    { toFun := fun x => (fun i => x i.1, fun i => x i.1)
      invFun := fun p i => if hi : i ∈ S then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩
      left_inv := fun x => by
        funext i
        by_cases hi : i ∈ S <;> simp [hi]
      right_inv := fun p => by
        rcases p with ⟨p1, p2⟩
        ext i
        · simp [i.2]
        · simp [i.2] }
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [Finset.mem_product, e, hx]
  · intro x1 _ x2 _ h
    exact e.injective h
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (fun i : {i : Fin n // i ∈ S} => e.symm p i.1) = p.1 := by
      funext i
      simp [e, i.2]
    have h2 : (fun i : {i : Fin n // i ∉ S} => e.symm p i.1) = p.2 := by
      funext i
      simp [e, i.2]
    rw [h1, h2]
    exact hp

private lemma mass_insert_disjoint_step {n : ℕ} (c : (Fin n × Bool) × (Fin n × Bool))
    (M : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hc : nonTaut c = true)
    (hdisj : ∀ c' ∈ M, Disjoint (clauseVars c) (clauseVars c')) :
    4 * mass n (insert c M) ≤ 3 * mass n M := by
  set V := clauseVars c
  let P : ({i : Fin n // i ∈ V} → Bool) → Prop := fun y =>
    y ⟨c.1.1, by simp [V, clauseVars]⟩ ≠ c.1.2 ∨
    y ⟨c.2.1, by simp [V, clauseVars]⟩ ≠ c.2.2
  have hM_out : ∀ c' ∈ M, c'.1.1 ∉ V ∧ c'.2.1 ∉ V := by
    intro c' hc'
    have hd := hdisj c' hc'
    rw [Finset.disjoint_left] at hd
    constructor
    · intro hm
      exact hd hm (by simp [clauseVars])
    · intro hm
      exact hd hm (by simp [clauseVars])
  let Q : ({i : Fin n // i ∉ V} → Bool) → Prop := fun z =>
    ∀ c' : (Fin n × Bool) × (Fin n × Bool), ∀ hc' : c' ∈ M,
      z ⟨c'.1.1, (hM_out c' hc').1⟩ ≠ c'.1.2 ∨
      z ⟨c'.2.1, (hM_out c' hc').2⟩ ≠ c'.2.2
  have hmass_ins : mass n (insert c M) =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
    rw [← card_split_finset V P Q]
    unfold mass
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, P, Q]
    constructor
    · intro h
      refine ⟨h c (Or.inl rfl), fun c' hc' => h c' (Or.inr hc')⟩
    · rintro ⟨h1, h2⟩ c' (rfl | hc')
      · exact h1
      · exact h2 c' hc'
  have hmass_M : mass n M =
      (Finset.univ.filter (fun _ : {i : Fin n // i ∈ V} → Bool => True)).card *
      (Finset.univ.filter Q).card := by
    rw [← card_split_finset V (fun _ => True) Q]
    unfold mass
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q]
  have hVcard_all : (Finset.univ.filter (fun _ : {i : Fin n // i ∈ V} → Bool => True)).card =
      2 ^ V.card := by
    simp
  have hbad : ∃ y0 : {i : Fin n // i ∈ V} → Bool, ¬ P y0 := by
    refine ⟨fun i => if i.1 = c.1.1 then c.1.2 else c.2.2, ?_⟩
    simp only [P, not_or, not_ne_iff]
    constructor
    · simp
    · by_cases heq : c.2.1 = c.1.1
      · simp only [heq, ite_true]
        simp only [nonTaut, decide_eq_true_eq, not_and, not_not] at hc
        exact hc heq.symm
      · simp [heq]
  rcases hbad with ⟨y0, hy0⟩
  have hP_lt : (Finset.univ.filter P).card < 2 ^ V.card := by
    have hsub : Finset.univ.filter P ⊂ (Finset.univ : Finset ({i : Fin n // i ∈ V} → Bool)) := by
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨y0, Finset.mem_univ y0, by simp [hy0]⟩
    have hlt := Finset.card_lt_card hsub
    simpa [Fintype.card_pi_const] using hlt
  have hV_le : V.card ≤ 2 := by
    dsimp only [V, clauseVars]
    exact Finset.card_le_two
  have hV_pos : 1 ≤ V.card := by
    dsimp only [V, clauseVars]
    exact Finset.card_pos.mpr ⟨c.1.1, by simp⟩
  have h43 : 4 * (Finset.univ.filter P).card ≤ 3 * 2 ^ V.card := by
    have hcases : V.card = 1 ∨ V.card = 2 := by omega
    rcases hcases with h1 | h2
    · rw [h1] at hP_lt ⊢
      omega
    · rw [h2] at hP_lt ⊢
      omega
  rw [hmass_ins, hmass_M, hVcard_all]
  calc
    4 * ((Finset.univ.filter P).card * (Finset.univ.filter Q).card)
      = (4 * (Finset.univ.filter P).card) * (Finset.univ.filter Q).card := by ring
    _ ≤ (3 * 2 ^ V.card) * (Finset.univ.filter Q).card :=
        Nat.mul_le_mul_right _ h43
    _ = 3 * (2 ^ V.card * (Finset.univ.filter Q).card) := by ring

private lemma mass_disjoint_bound {n : ℕ}
    (M : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hnt : ∀ c ∈ M, nonTaut c = true) (hdisj : IsVarDisjoint M) :
    4 ^ M.card * mass n M ≤ 3 ^ M.card * 2 ^ n := by
  induction M using Finset.induction_on with
  | empty =>
    simp [mass]
  | insert c M hnot ih =>
    have hntM : ∀ c' ∈ M, nonTaut c' = true := fun c' hc' => hnt c' (Finset.mem_insert_of_mem hc')
    have hdisjM : IsVarDisjoint M := fun c1 h1 c2 h2 hne =>
      hdisj c1 (Finset.mem_insert_of_mem h1) c2 (Finset.mem_insert_of_mem h2) hne
    have hdisjC : ∀ c' ∈ M, Disjoint (clauseVars c) (clauseVars c') := fun c' hc' =>
      hdisj c (Finset.mem_insert_self c M) c' (Finset.mem_insert_of_mem hc')
        (fun h => hnot (h ▸ hc'))
    have hstep := mass_insert_disjoint_step c M (hnt c (Finset.mem_insert_self c M)) hdisjC
    have hih := ih hntM hdisjM
    rw [Finset.card_insert_of_notMem hnot, pow_succ, pow_succ]
    calc
      4 ^ M.card * 4 * mass n (insert c M)
        = 4 ^ M.card * (4 * mass n (insert c M)) := by ring
      _ ≤ 4 ^ M.card * (3 * mass n M) := Nat.mul_le_mul_left _ hstep
      _ = 3 * (4 ^ M.card * mass n M) := by ring
      _ ≤ 3 * (3 ^ M.card * 2 ^ n) := Nat.mul_le_mul_left _ hih
      _ = 3 ^ M.card * 3 * 2 ^ n := by ring

private lemma mass_antitone {n : ℕ} {A B : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (h : A ⊆ B) : mass n B ≤ mass n A := by
  unfold mass
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro c hc
  exact hx c (h hc)

private lemma exists_small_vertex_cover {n a : ℕ}
    (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hpos : 0 < mass n A) (hdense : 2 ^ n ≤ 2 ^ a * mass n A) :
    ∃ U : Finset (Fin n), U.card ≤ 8 * (a + 1) ∧
      ∀ c ∈ stripTaut A, c.1.1 ∈ U ∨ c.2.1 ∈ U := by
  set A' := stripTaut A
  let Cands := A'.powerset.filter IsVarDisjoint
  have hne : Cands.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Cands, IsVarDisjoint]
  rcases Finset.exists_max_image Cands Finset.card hne with ⟨M, hM, hmax⟩
  simp only [Cands, Finset.mem_filter, Finset.mem_powerset] at hM
  rcases hM with ⟨hMA', hMdisj⟩
  have hMnt : ∀ c ∈ M, nonTaut c = true := fun c hc => (Finset.mem_filter.mp (hMA' hc)).2
  have hbound := mass_disjoint_bound M hMnt hMdisj
  have hmass_le : mass n A ≤ mass n M := by
    rw [← mass_stripTaut A]
    exact mass_antitone hMA'
  have h43 : 4 ^ M.card ≤ 3 ^ M.card * 2 ^ a := by
    have h1 : 4 ^ M.card * mass n A ≤ 3 ^ M.card * 2 ^ a * mass n A := by
      calc
        4 ^ M.card * mass n A ≤ 4 ^ M.card * mass n M := Nat.mul_le_mul_left _ hmass_le
        _ ≤ 3 ^ M.card * 2 ^ n := hbound
        _ ≤ 3 ^ M.card * (2 ^ a * mass n A) := Nat.mul_le_mul_left _ hdense
        _ = 3 ^ M.card * 2 ^ a * mass n A := by ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hMcard : M.card < 4 * (a + 1) := by
    by_contra hge
    push Not at hge
    have hstep4 : 2 * 3 ^ 4 ≤ 4 ^ 4 := by decide
    have hpow4 : (2 * 3 ^ 4) ^ (a + 1) ≤ (4 ^ 4) ^ (a + 1) := Nat.pow_le_pow_left hstep4 (a + 1)
    rw [mul_pow, ← pow_mul, ← pow_mul] at hpow4
    have hrem : 3 ^ (M.card - 4 * (a + 1)) ≤ 4 ^ (M.card - 4 * (a + 1)) :=
      Nat.pow_le_pow_left (by decide) _
    have hprod : 2 ^ (a + 1) * 3 ^ M.card ≤ 4 ^ M.card := by
      have hsplit : 4 * (a + 1) + (M.card - 4 * (a + 1)) = M.card := Nat.add_sub_of_le hge
      calc
        2 ^ (a + 1) * 3 ^ M.card
          = 2 ^ (a + 1) * (3 ^ (4 * (a + 1)) * 3 ^ (M.card - 4 * (a + 1))) := by
              rw [← pow_add, hsplit]
        _ = (2 ^ (a + 1) * 3 ^ (4 * (a + 1))) * 3 ^ (M.card - 4 * (a + 1)) := by ring
        _ ≤ 4 ^ (4 * (a + 1)) * 4 ^ (M.card - 4 * (a + 1)) :=
              Nat.mul_le_mul hpow4 hrem
        _ = 4 ^ M.card := by rw [← pow_add, hsplit]
    have hlt : 3 ^ M.card * 2 ^ a < 2 ^ (a + 1) * 3 ^ M.card := by
      have h3pos : 0 < 3 ^ M.card := Nat.pow_pos (by decide)
      have h2pos : 0 < 2 ^ a := Nat.two_pow_pos a
      rw [pow_succ]
      nlinarith
    omega
  refine ⟨M.biUnion clauseVars, ?_, ?_⟩
  · calc
      (M.biUnion clauseVars).card ≤ ∑ c ∈ M, (clauseVars c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ M, 2 := Finset.sum_le_sum fun c _ => Finset.card_le_two
      _ = M.card * 2 := by simp
      _ ≤ 8 * (a + 1) := by omega
  · intro c hc
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨h1, h2⟩
    have hc_not_M : c ∉ M := by
      intro hmem
      exact h1 (Finset.mem_biUnion.mpr ⟨c, hmem, by simp [clauseVars]⟩)
    have hdisj_ins : IsVarDisjoint (insert c M) := by
      intro c1 hc1 c2 hc2 hne
      simp only [Finset.mem_insert] at hc1 hc2
      rcases hc1 with rfl | hc1'
      · rcases hc2 with rfl | hc2'
        · exact absurd rfl hne
        · rw [Finset.disjoint_left]
          intro v hv1 hv2
          simp only [clauseVars, Finset.mem_insert, Finset.mem_singleton] at hv1
          rcases hv1 with rfl | rfl
          · exact h1 (Finset.mem_biUnion.mpr ⟨c2, hc2', hv2⟩)
          · exact h2 (Finset.mem_biUnion.mpr ⟨c2, hc2', hv2⟩)
      · rcases hc2 with rfl | hc2'
        · rw [Finset.disjoint_right]
          intro v hv2 hv1
          simp only [clauseVars, Finset.mem_insert, Finset.mem_singleton] at hv2
          rcases hv2 with rfl | rfl
          · exact h1 (Finset.mem_biUnion.mpr ⟨c1, hc1', hv1⟩)
          · exact h2 (Finset.mem_biUnion.mpr ⟨c1, hc1', hv1⟩)
        · exact hMdisj c1 hc1' c2 hc2' hne
    have hins_mem : insert c M ∈ Cands := by
      simp only [Cands, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hc hMA', hdisj_ins⟩
    have hle := hmax (insert c M) hins_mem
    rw [Finset.card_insert_of_notMem hc_not_M] at hle
    omega

abbrev Sig (c : ℕ) := (Fin c × Bool) × Bool → Bool

noncomputable def goodVal (c : ℕ) (σ : Sig c) (α : Fin c → Bool) (b : Bool) : Bool :=
  decide (∀ u : Fin c × Bool, σ (u, b) = true → α u.1 ≠ u.2)

noncomputable def isAlive (c : ℕ)
    (Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool)
    (Spres : Sig c → Bool) (α : Fin c → Bool) : Bool :=
  decide (
    (∀ cl : (Fin c × Bool) × (Fin c × Bool),
      Aint cl = true → (α cl.1.1 ≠ cl.1.2 ∨ α cl.2.1 ≠ cl.2.2)) ∧
    (∀ σ : Sig c, Spres σ = true → ∃ b : Bool, goodVal c σ α b = true))

noncomputable def forced (c : ℕ) (σ : Sig c) (α : Fin c → Bool) : ℕ :=
  if (∀ b : Bool, goodVal c σ α b = true) then 0 else 1

private lemma forced_le_one (c : ℕ) (σ : Sig c) (α : Fin c → Bool) :
    forced c σ α ≤ 1 := by
  unfold forced
  split_ifs <;> omega

private lemma goodVal_card_eq_pow (c : ℕ) (σ : Sig c) (α : Fin c → Bool)
    (hex : ∃ b : Bool, goodVal c σ α b = true) :
    (Finset.univ.filter (fun b : Bool => goodVal c σ α b = true)).card =
      2 ^ (1 - forced c σ α) := by
  unfold forced
  by_cases hall : ∀ b : Bool, goodVal c σ α b = true
  · simp only [hall, ite_true, Nat.sub_zero, pow_one]
    simp
  · simp only [hall, ite_false, Nat.sub_self, pow_zero]
    rcases hex with ⟨b0, hb0⟩
    have hnot : ∃ b1 : Bool, goodVal c σ α b1 = false := by
      by_contra h
      push_neg at h
      exact hall fun b => by
        cases hv : goodVal c σ α b
        · exact absurd hv (h b)
        · rfl
    rcases hnot with ⟨b1, hb1⟩
    have hne : b0 ≠ b1 := by
      intro h
      rw [h, hb1] at hb0
      cases hb0
    have hf : Finset.univ.filter (fun b : Bool => goodVal c σ α b = true) = {b0} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hb
        cases b0 <;> cases b1 <;> cases b <;> simp_all
      · intro h
        rw [h]
        exact hb0
    rw [hf]
    simp

private lemma fiber_mass_formula {c : ℕ} {Out : Type} [Fintype Out]
    (Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool)
    (sigOf : Out → Sig c) (Spres : Sig c → Bool)
    (hSpres : ∀ σ : Sig c, Spres σ = true ↔ ∃ y : Out, sigOf y = σ) :
    ((Finset.univ.filter (fun p : (Fin c → Bool) × (Out → Bool) =>
      (∀ cl, Aint cl = true → p.1 cl.1.1 ≠ cl.1.2 ∨ p.1 cl.2.1 ≠ cl.2.2) ∧
      (∀ y : Out, goodVal c (sigOf y) p.1 (p.2 y) = true))).card : ℚ) /
      (2 : ℚ) ^ (c + Fintype.card Out) =
    ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
      (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
        forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card) := by
  let P := fun p : (Fin c → Bool) × (Out → Bool) =>
    (∀ cl, Aint cl = true → p.1 cl.1.1 ≠ cl.1.2 ∨ p.1 cl.2.1 ≠ cl.2.2) ∧
    (∀ y : Out, goodVal c (sigOf y) p.1 (p.2 y) = true)
  have hcard_sum : (Finset.univ.filter P).card =
      ∑ α : Fin c → Bool,
        (Finset.univ.filter (fun β : Out → Bool => P (α, β))).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij
      (fun p _ => (⟨p.1, p.2⟩ : Σ _ : Fin c → Bool, Out → Bool)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Finset.mem_sigma, hp]
    · intro p1 _ p2 _ h
      rcases p1 with ⟨a1, b1⟩
      rcases p2 with ⟨a2, b2⟩
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      exact Prod.ext h.1 h.2
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at hq
      exact ⟨(q.1, q.2), by simp [hq], rfl⟩
  have hfiber_zero : ∀ α : Fin c → Bool, isAlive c Aint Spres α = false →
      (Finset.univ.filter (fun β : Out → Bool => P (α, β))).card = 0 := by
    intro α hdead
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro β _ hP
    have halive : isAlive c Aint Spres α = true := by
      simp only [isAlive, decide_eq_true_eq]
      refine ⟨hP.1, fun σ hσ => ?_⟩
      rcases (hSpres σ).mp hσ with ⟨y, rfl⟩
      exact ⟨β y, hP.2 y⟩
    rw [halive] at hdead
    cases hdead
  have hfiber_alive : ∀ α : Fin c → Bool, isAlive c Aint Spres α = true →
      ((Finset.univ.filter (fun β : Out → Bool => P (α, β))).card : ℚ) /
        (2 : ℚ) ^ (c + Fintype.card Out) =
      (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
        forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card) := by
    intro α halive
    have halive' := halive
    simp only [isAlive, decide_eq_true_eq] at halive'
    rcases halive' with ⟨hAint, hSig⟩
    have hfilt : Finset.univ.filter (fun β : Out → Bool => P (α, β)) =
        Fintype.piFinset (fun y : Out =>
          Finset.univ.filter (fun b : Bool => goodVal c (sigOf y) α b = true)) := by
      ext β
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, P]
      exact ⟨fun h => h.2, fun h => ⟨hAint, h⟩⟩
    rw [hfilt, Fintype.card_piFinset]
    have hprod : (∏ y : Out,
        (Finset.univ.filter (fun b : Bool => goodVal c (sigOf y) α b = true)).card) =
        2 ^ (∑ y : Out, (1 - forced c (sigOf y) α)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y _ => ?_
      exact goodVal_card_eq_pow c (sigOf y) α (hSig (sigOf y) ((hSpres _).mpr ⟨y, rfl⟩))
    rw [hprod]
    set F : ℕ := ∑ y : Out, forced c (sigOf y) α
    have hF_sum : (∑ y : Out, (1 - forced c (sigOf y) α)) + F = Fintype.card Out := by
      dsimp only [F]
      rw [← Finset.sum_add_distrib]
      have h1 : ∀ y : Out, (1 - forced c (sigOf y) α) + forced c (sigOf y) α = 1 := fun y =>
        Nat.sub_add_cancel (forced_le_one c (sigOf y) α)
      simp [h1]
    have hF_group : F = ∑ σ : {σ : Sig c // Spres σ = true},
        forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card := by
      dsimp only [F]
      have hmap : ∀ y ∈ (Finset.univ : Finset Out),
          (⟨sigOf y, (hSpres _).mpr ⟨y, rfl⟩⟩ : {σ : Sig c // Spres σ = true}) ∈ Finset.univ :=
        fun _ _ => Finset.mem_univ _
      rw [← Finset.sum_fiberwise_of_maps_to hmap]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hsub : (Finset.univ.filter (fun y : Out =>
          (⟨sigOf y, (hSpres _).mpr ⟨y, rfl⟩⟩ : {σ : Sig c // Spres σ = true}) = σ)) =
          Finset.univ.filter (fun y : Out => sigOf y = σ.1) := by
        ext y
        simp [Subtype.ext_iff]
      rw [hsub]
      have hcongr : (∑ y ∈ Finset.univ.filter (fun y : Out => sigOf y = σ.1),
          forced c (sigOf y) α) =
          ∑ _y ∈ Finset.univ.filter (fun y : Out => sigOf y = σ.1), forced c σ.1 α := by
        refine Finset.sum_congr rfl fun y hy => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rw [hy]
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hF_group]
    have h2pos1 : (2 : ℚ) ^ (c + Fintype.card Out) ≠ 0 := by positivity
    have h2pos2 : (2 : ℚ) ^ (c + F) ≠ 0 := by positivity
    rw [div_eq_div_iff h2pos1 h2pos2]
    push_cast
    rw [one_mul, ← pow_add]
    congr 1
    omega
  have hstep1 : ((Finset.univ.filter P).card : ℚ) / (2 : ℚ) ^ (c + Fintype.card Out) =
      ∑ α : Fin c → Bool,
        ((Finset.univ.filter (fun β : Out → Bool => P (α, β))).card : ℚ) /
          (2 : ℚ) ^ (c + Fintype.card Out) := by
    rw [hcard_sum]
    push_cast
    rw [Finset.sum_div]
  have hstep2 : (∑ α : Fin c → Bool,
        ((Finset.univ.filter (fun β : Out → Bool => P (α, β))).card : ℚ) /
          (2 : ℚ) ^ (c + Fintype.card Out)) =
      ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
        ((Finset.univ.filter (fun β : Out → Bool => P (α, β))).card : ℚ) /
          (2 : ℚ) ^ (c + Fintype.card Out) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun α _ hnot => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnot
    rw [hfiber_zero α hnot]
    simp
  have hstep3 : (∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
        ((Finset.univ.filter (fun β : Out → Bool => P (α, β))).card : ℚ) /
          (2 : ℚ) ^ (c + Fintype.card Out)) =
      ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
        (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
          forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card) := by
    refine Finset.sum_congr rfl fun α hα => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
    exact hfiber_alive α hα
  exact hstep1.trans (hstep2.trans hstep3)

private lemma forward_representation {n c : ℕ}
    (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (U : Finset (Fin n)) (hc : U.card = c)
    (hcov : ∀ cl ∈ stripTaut A, cl.1.1 ∈ U ∨ cl.2.1 ∈ U) :
    ∃ (Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool)
      (Spres : Sig c → Bool)
      (m : {σ : Sig c // Spres σ = true} → ℕ),
      (mass n A : ℚ) / (2 : ℚ) ^ n =
        ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
          (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
            forced c σ.1 α * (m σ + 1)) := by
  subst hc
  set c := U.card
  set A' := stripTaut A
  let eU : Fin c ≃ {i : Fin n // i ∈ U} := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  let Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool := fun cl =>
    decide ((((eU cl.1.1).1, cl.1.2), ((eU cl.2.1).1, cl.2.2)) ∈ A')
  let Out := {y : Fin n // y ∉ U}
  let sigOf : Out → Sig c := fun y p =>
    decide (((((eU p.1.1).1, p.1.2), (y.1, p.2)) ∈ A') ∨
            (((y.1, p.2), ((eU p.1.1).1, p.1.2)) ∈ A'))
  let Spres : Sig c → Bool := fun σ => decide (∃ y : Out, sigOf y = σ)
  have hSpres : ∀ σ : Sig c, Spres σ = true ↔ ∃ y : Out, sigOf y = σ := fun σ => by
    simp [Spres]
  let m : {σ : Sig c // Spres σ = true} → ℕ := fun σ =>
    (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card - 1
  refine ⟨Aint, Spres, m, ?_⟩
  have hm_eq : ∀ σ : {σ : Sig c // Spres σ = true},
      (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card = m σ + 1 := by
    intro σ
    rcases (hSpres σ.1).mp σ.2 with ⟨y, hy⟩
    have hpos : 0 < (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card :=
      Finset.card_pos.mpr ⟨y, by simp [hy]⟩
    dsimp only [m]
    omega
  have hcard_n : c + Fintype.card Out = n := by
    have h1 : Fintype.card Out = (Finset.univ \ U).card := by
      have : Fintype.card Out = (Finset.univ.filter (fun y : Fin n => y ∉ U)).card :=
        Fintype.card_subtype _
      rw [this]
      congr 1
      ext y
      simp
    rw [h1, Finset.card_sdiff]
    have hUle : U.card ≤ n := by
      have := Finset.card_le_univ U
      simpa using this
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  let eSplit : (Fin n → Bool) ≃ (Fin c → Bool) × (Out → Bool) :=
    { toFun := fun x => (fun i => x (eU i).1, fun y => x y.1)
      invFun := fun p i =>
        if hi : i ∈ U then p.1 (eU.symm ⟨i, hi⟩) else p.2 ⟨i, hi⟩
      left_inv := fun x => by
        funext i
        by_cases hi : i ∈ U <;> simp [hi]
      right_inv := fun p => by
        rcases p with ⟨α, β⟩
        ext i
        · simp [(eU i).2]
        · simp [i.2] }
  have hmass_eq : mass n A =
      (Finset.univ.filter (fun p : (Fin c → Bool) × (Out → Bool) =>
        (∀ cl, Aint cl = true → p.1 cl.1.1 ≠ cl.1.2 ∨ p.1 cl.2.1 ≠ cl.2.2) ∧
        (∀ y : Out, goodVal c (sigOf y) p.1 (p.2 y) = true))).card := by
    rw [← mass_stripTaut A]
    unfold mass
    refine Finset.card_bij (fun x _ => eSplit x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨?_, ?_⟩
      · intro cl hcl
        simp only [Aint, decide_eq_true_eq] at hcl
        exact hx _ hcl
      · intro y
        simp only [goodVal, decide_eq_true_eq, sigOf]
        intro u hu
        rcases hu with hu1 | hu2
        · have h := hx _ hu1
          simpa [eSplit] using h
        · have h := hx _ hu2
          simpa [eSplit] using h
    · intro x1 _ x2 _ h
      exact eSplit.injective h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨eSplit.symm p, ?_, eSplit.apply_symm_apply p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro cl hcl
      rcases cl with ⟨⟨v1, b1⟩, ⟨v2, b2⟩⟩
      rcases hp with ⟨h1, h2⟩
      by_cases h1U : v1 ∈ U
      · by_cases h2U : v2 ∈ U
        · let i1 := eU.symm ⟨v1, h1U⟩
          let i2 := eU.symm ⟨v2, h2U⟩
          have hmem : Aint ((i1, b1), (i2, b2)) = true := by
            simp only [Aint, decide_eq_true_eq, i1, i2, Equiv.apply_symm_apply]
            exact hcl
          have := h1 _ hmem
          simpa [eSplit, h1U, h2U, i1, i2] using this
        · let i1 := eU.symm ⟨v1, h1U⟩
          let y : Out := ⟨v2, h2U⟩
          have hy := h2 y
          simp only [goodVal, decide_eq_true_eq] at hy
          by_cases hpol : p.2 y = b2
          · left
            have hsig : sigOf y ((i1, b1), p.2 y) = true := by
              simp only [sigOf, decide_eq_true_eq, i1, y, Equiv.apply_symm_apply, hpol]
              exact Or.inl hcl
            have := hy (i1, b1) hsig
            simpa [eSplit, h1U, i1] using this
          · right
            simpa [eSplit, h2U, y] using hpol
      · have h2U : v2 ∈ U := (hcov _ hcl).resolve_left h1U
        let i2 := eU.symm ⟨v2, h2U⟩
        let y : Out := ⟨v1, h1U⟩
        have hy := h2 y
        simp only [goodVal, decide_eq_true_eq] at hy
        by_cases hpol : p.2 y = b1
        · right
          have hsig : sigOf y ((i2, b2), p.2 y) = true := by
            simp only [sigOf, decide_eq_true_eq, i2, y, Equiv.apply_symm_apply, hpol]
            exact Or.inr hcl
          have := hy (i2, b2) hsig
          simpa [eSplit, h2U, i2] using this
        · left
          simpa [eSplit, h1U, y] using hpol
  have hpow_n : (2 : ℚ) ^ n = (2 : ℚ) ^ (c + Fintype.card Out) :=
    congrArg ((2 : ℚ) ^ ·) hcard_n.symm
  have hmain := fiber_mass_formula Aint sigOf Spres hSpres
  have hstep : (mass n A : ℚ) / (2 : ℚ) ^ n =
      ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
        (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
          forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card) := by
    rw [← hmain, hmass_eq, hpow_n]
    apply congrArg (fun k : ℕ => (k : ℚ) / (2 : ℚ) ^ (c + Fintype.card Out))
    apply congrArg Finset.card
    ext p
    simp
  rw [hstep]
  refine Finset.sum_congr rfl fun α _ => ?_
  apply congrArg (fun e : ℕ => (1 : ℚ) / (2 : ℚ) ^ (c + e))
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hm_eq σ]

private lemma converse_realization (c : ℕ)
    (Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool)
    (Spres : Sig c → Bool)
    (m : {σ : Sig c // Spres σ = true} → ℕ) :
    ∃ (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))),
      (mass n A : ℚ) / (2 : ℚ) ^ n =
        ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
          (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
            forced c σ.1 α * (m σ + 1)) := by
  let Out := Σ σ : {σ : Sig c // Spres σ = true}, Fin (m σ + 1)
  let V := Fin c ⊕ Out
  let n := Fintype.card V
  let eV : V ≃ Fin n := Fintype.equivFin V
  let A1 : Finset ((Fin n × Bool) × (Fin n × Bool)) :=
    (Finset.univ.filter (fun cl : (Fin c × Bool) × (Fin c × Bool) => Aint cl = true)).image
      (fun cl => ((eV (Sum.inl cl.1.1), cl.1.2), (eV (Sum.inl cl.2.1), cl.2.2)))
  let A2 : Finset ((Fin n × Bool) × (Fin n × Bool)) :=
    (Finset.univ.filter (fun q : (Fin c × Bool) × (Out × Bool) =>
      q.2.1.1.1 (q.1, q.2.2) = true)).image
      (fun q => ((eV (Sum.inl q.1.1), q.1.2), (eV (Sum.inr q.2.1), q.2.2)))
  refine ⟨n, A1 ∪ A2, ?_⟩
  let sigOf : Out → Sig c := fun y => y.1.1
  have hSpres : ∀ σ : Sig c, Spres σ = true ↔ ∃ y : Out, sigOf y = σ := by
    intro σ
    constructor
    · intro hσ
      exact ⟨⟨⟨σ, hσ⟩, ⟨0, Nat.succ_pos _⟩⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.1.2
  have hcard_n : c + Fintype.card Out = n := by
    dsimp only [n, V]
    rw [Fintype.card_sum, Fintype.card_fin]
  have hcard_fib : ∀ σ : {σ : Sig c // Spres σ = true},
      (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card = m σ + 1 := by
    intro σ
    have hfin : m σ + 1 = (Finset.univ : Finset (Fin (m σ + 1))).card := by simp
    rw [hfin]
    refine Finset.card_bij
      (fun (y : Out) (hy : y ∈ Finset.univ.filter (fun y : Out => sigOf y = σ.1)) =>
        (cast (congrArg (fun τ : {τ : Sig c // Spres τ = true} => Fin (m τ + 1))
          (Subtype.ext (Finset.mem_filter.mp hy).2 : y.1 = σ)) y.2)) ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro y1 hy1 y2 hy2 heq
      have h1 : y1.1 = σ := Subtype.ext (Finset.mem_filter.mp hy1).2
      have h2 : y2.1 = σ := Subtype.ext (Finset.mem_filter.mp hy2).2
      cases y1 with
      | mk s1 t1 =>
        cases y2 with
        | mk s2 t2 =>
          dsimp only at h1 h2 heq
          subst h1
          subst h2
          simp only [cast_eq] at heq
          rw [heq]
    · intro t _
      refine ⟨⟨σ, t⟩, ?_, ?_⟩
      · simp [sigOf]
      · simp
  let eSplit : (Fin n → Bool) ≃ (Fin c → Bool) × (Out → Bool) :=
    { toFun := fun x => (fun i => x (eV (Sum.inl i)), fun y => x (eV (Sum.inr y)))
      invFun := fun p k =>
        match eV.symm k with
        | Sum.inl i => p.1 i
        | Sum.inr y => p.2 y
      left_inv := fun x => by
        funext k
        cases hk : eV.symm k with
        | inl i =>
          have : k = eV (Sum.inl i) := by rw [← hk, Equiv.apply_symm_apply]
          simp [this]
        | inr y =>
          have : k = eV (Sum.inr y) := by rw [← hk, Equiv.apply_symm_apply]
          simp [this]
      right_inv := fun p => by
        rcases p with ⟨α, β⟩
        ext i <;> simp }
  have hmass_eq : mass n (A1 ∪ A2) =
      (Finset.univ.filter (fun p : (Fin c → Bool) × (Out → Bool) =>
        (∀ cl, Aint cl = true → p.1 cl.1.1 ≠ cl.1.2 ∨ p.1 cl.2.1 ≠ cl.2.2) ∧
        (∀ y : Out, goodVal c (sigOf y) p.1 (p.2 y) = true))).card := by
    unfold mass
    refine Finset.card_bij (fun x _ => eSplit x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨?_, ?_⟩
      · intro cl hcl
        have hmem : ((eV (Sum.inl cl.1.1), cl.1.2), (eV (Sum.inl cl.2.1), cl.2.2)) ∈ A1 ∪ A2 :=
          Finset.mem_union_left A2 (Finset.mem_image.mpr ⟨cl, by simp [hcl], rfl⟩)
        exact hx _ hmem
      · intro y
        simp only [goodVal, decide_eq_true_eq, sigOf]
        intro u hu
        have hmem : ((eV (Sum.inl u.1), u.2), (eV (Sum.inr y), x (eV (Sum.inr y)))) ∈ A1 ∪ A2 :=
          Finset.mem_union_right A1
            (Finset.mem_image.mpr ⟨(u, (y, x (eV (Sum.inr y)))), by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              simpa [eSplit] using hu, rfl⟩)
        have h := hx _ hmem
        simpa [eSplit] using h
    · intro x1 _ x2 _ h
      exact eSplit.injective h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨eSplit.symm p, ?_, eSplit.apply_symm_apply p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro cl hcl
      rcases Finset.mem_union.mp hcl with h1 | h2
      · rcases Finset.mem_image.mp h1 with ⟨cl0, hcl0, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcl0
        simpa [eSplit] using hp.1 cl0 hcl0
      · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hy := hp.2 q.2.1
        simp only [goodVal, decide_eq_true_eq, sigOf] at hy
        by_cases hpol : p.2 q.2.1 = q.2.2
        · left
          rw [← hpol] at hq
          simpa [eSplit] using hy q.1 hq
        · right
          simpa [eSplit] using hpol
  have hpow_n : (2 : ℚ) ^ n = (2 : ℚ) ^ (c + Fintype.card Out) :=
    congrArg ((2 : ℚ) ^ ·) hcard_n.symm
  have hmain := fiber_mass_formula Aint sigOf Spres hSpres
  have hstep : (mass n (A1 ∪ A2) : ℚ) / (2 : ℚ) ^ n =
      ∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
        (1 : ℚ) / (2 : ℚ) ^ (c + ∑ σ : {σ : Sig c // Spres σ = true},
          forced c σ.1 α * (Finset.univ.filter (fun y : Out => sigOf y = σ.1)).card) := by
    rw [← hmain, hmass_eq, hpow_n]
    apply congrArg (fun k : ℕ => (k : ℚ) / (2 : ℚ) ^ (c + Fintype.card Out))
    apply congrArg Finset.card
    ext p
    simp
  rw [hstep]
  refine Finset.sum_congr rfl fun α _ => ?_
  apply congrArg (fun e : ℕ => (1 : ℚ) / (2 : ℚ) ^ (c + e))
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hcard_fib σ]

private lemma sum_pow_two_inj_aux (X Y : Finset ℕ) (h : ∑ x ∈ X, 2 ^ x = ∑ y ∈ Y, 2 ^ y)
    (hne : (X \ Y).Nonempty)
    (hle : ∀ z ∈ (X \ Y) ∪ (Y \ X), (X \ Y).min' hne ≤ z) : False := by
  set m := (X \ Y).min' hne
  have hmX : m ∈ X \ Y := Finset.min'_mem (X \ Y) hne
  have hcancel : ∑ x ∈ X \ Y, 2 ^ x = ∑ y ∈ Y \ X, 2 ^ y := by
    have hX : ∑ x ∈ X, 2 ^ x = (∑ x ∈ X \ Y, 2 ^ x) + (∑ x ∈ X ∩ Y, 2 ^ x) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter X Y), Finset.sdiff_union_inter]
    have hY : ∑ y ∈ Y, 2 ^ y = (∑ y ∈ Y \ X, 2 ^ y) + (∑ y ∈ Y ∩ X, 2 ^ y) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Y X), Finset.sdiff_union_inter]
    rw [Finset.inter_comm] at hY
    omega
  have hdvdY : 2 ^ (m + 1) ∣ ∑ y ∈ Y \ X, 2 ^ y := by
    refine Finset.dvd_sum fun y hy => ?_
    have hmy : m ≤ y := hle y (Finset.mem_union_right _ hy)
    have hne_my : m ≠ y := by
      intro heq
      rw [← heq] at hy
      exact (Finset.mem_sdiff.mp hmX).2 (Finset.mem_sdiff.mp hy).1
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdvdX_rest : 2 ^ (m + 1) ∣ ∑ x ∈ (X \ Y).erase m, 2 ^ x := by
    refine Finset.dvd_sum fun x hx => ?_
    rcases Finset.mem_erase.mp hx with ⟨hne_xm, hx'⟩
    have hmx : m ≤ x := hle x (Finset.mem_union_left _ hx')
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsplitX : ∑ x ∈ X \ Y, 2 ^ x = 2 ^ m + ∑ x ∈ (X \ Y).erase m, 2 ^ x := by
    rw [add_comm]
    exact (Finset.sum_erase_add (X \ Y) (fun x => 2 ^ x) hmX).symm
  rw [hsplitX] at hcancel
  have hdvd_m : 2 ^ (m + 1) ∣ 2 ^ m := by
    have : 2 ^ (m + 1) ∣ 2 ^ m + ∑ x ∈ (X \ Y).erase m, 2 ^ x := by
      rw [hcancel]
      exact hdvdY
    exact (Nat.dvd_add_left hdvdX_rest).mp this
  have hle_pow : 2 ^ (m + 1) ≤ 2 ^ m := Nat.le_of_dvd (Nat.two_pow_pos m) hdvd_m
  rw [pow_succ] at hle_pow
  have := Nat.two_pow_pos m
  omega

private lemma sum_pow_two_inj (X Y : Finset ℕ) (h : ∑ x ∈ X, 2 ^ x = ∑ y ∈ Y, 2 ^ y) :
    X = Y := by
  by_contra hne
  have hS : ((X \ Y) ∪ (Y \ X)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty,
      Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset] at hempty
    exact hne (Finset.Subset.antisymm hempty.1 hempty.2)
  set m := ((X \ Y) ∪ (Y \ X)).min' hS
  have hm : m ∈ (X \ Y) ∪ (Y \ X) := Finset.min'_mem _ hS
  rcases Finset.mem_union.mp hm with hm1 | hm2
  · have hne1 : (X \ Y).Nonempty := ⟨m, hm1⟩
    have hmin_eq : (X \ Y).min' hne1 = m := by
      apply le_antisymm
      · exact Finset.min'_le _ m hm1
      · exact Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.min'_mem _ hne1))
    exact sum_pow_two_inj_aux X Y h hne1 (fun z hz => by
      rw [hmin_eq]
      exact Finset.min'_le _ z hz)
  · have hne2 : (Y \ X).Nonempty := ⟨m, hm2⟩
    have hmin_eq : (Y \ X).min' hne2 = m := by
      apply le_antisymm
      · exact Finset.min'_le _ m hm2
      · exact Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.min'_mem _ hne2))
    exact sum_pow_two_inj_aux Y X h.symm hne2 (fun z hz => by
      rw [hmin_eq]
      exact Finset.min'_le _ z (by simpa [Finset.union_comm] using hz))

private lemma dyadic_finset_inj (A B : Finset ℕ)
    (h : ∑ a ∈ A, (1 : ℚ) / 2 ^ a = ∑ b ∈ B, (1 : ℚ) / 2 ^ b) : A = B := by
  set M := (A ∪ B).sup id
  have hA : ∀ a ∈ A, a ≤ M := fun a ha => Finset.le_sup (f := id) (Finset.mem_union_left B ha)
  have hB : ∀ b ∈ B, b ≤ M := fun b hb => Finset.le_sup (f := id) (Finset.mem_union_right A hb)
  have hmul : (2 : ℚ) ^ M * (∑ a ∈ A, (1 : ℚ) / 2 ^ a) =
      (2 : ℚ) ^ M * (∑ b ∈ B, (1 : ℚ) / 2 ^ b) := congrArg ((2 : ℚ) ^ M * ·) h
  have hcast : ∀ S : Finset ℕ, (∀ x ∈ S, x ≤ M) →
      (2 : ℚ) ^ M * (∑ x ∈ S, (1 : ℚ) / 2 ^ x) = ((∑ x ∈ S, 2 ^ (M - x) : ℕ) : ℚ) := by
    intro S hS
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    have hle := hS x hx
    have h2 : (2 : ℚ) ^ x ≠ 0 := by positivity
    rw [mul_one_div, div_eq_iff h2, ← pow_add, Nat.sub_add_cancel hle]
  rw [hcast A hA, hcast B hB] at hmul
  have hnat : ∑ a ∈ A, 2 ^ (M - a) = ∑ b ∈ B, 2 ^ (M - b) := by exact_mod_cast hmul
  have hImgA : ∑ x ∈ A.image (fun a => M - a), 2 ^ x = ∑ a ∈ A, 2 ^ (M - a) := by
    refine Finset.sum_image fun a1 ha1 a2 ha2 heq => ?_
    have := hA a1 ha1
    have := hA a2 ha2
    omega
  have hImgB : ∑ y ∈ B.image (fun b => M - b), 2 ^ y = ∑ b ∈ B, 2 ^ (M - b) := by
    refine Finset.sum_image fun b1 hb1 b2 hb2 heq => ?_
    have := hB b1 hb1
    have := hB b2 hb2
    omega
  have himg_eq : A.image (fun a => M - a) = B.image (fun b => M - b) :=
    sum_pow_two_inj _ _ (by rw [hImgA, hImgB, hnat])
  ext x
  constructor
  · intro hx
    have hmem : M - x ∈ B.image (fun b => M - b) := by
      rw [← himg_eq]
      exact Finset.mem_image_of_mem _ hx
    rcases Finset.mem_image.mp hmem with ⟨b, hb, hbx⟩
    have := hA x hx
    have := hB b hb
    have : b = x := by omega
    rwa [← this]
  · intro hx
    have hmem : M - x ∈ A.image (fun a => M - a) := by
      rw [himg_eq]
      exact Finset.mem_image_of_mem _ hx
    rcases Finset.mem_image.mp hmem with ⟨a, ha, hax⟩
    have := hB x hx
    have := hA a ha
    have : a = x := by omega
    rwa [← this]

private lemma sum_range_dyadic (M : ℕ) :
    ∑ a ∈ Finset.range (M + 1), (1 : ℚ) / 2 ^ a = 2 - (1 : ℚ) / 2 ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private lemma dyadic_finset_sum_lt_two (A : Finset ℕ) :
    ∑ a ∈ A, (1 : ℚ) / 2 ^ a < 2 := by
  set M := A.sup id
  have hsub : A ⊆ Finset.range (M + 1) := by
    intro a ha
    rw [Finset.mem_range]
    have : a ≤ M := Finset.le_sup (f := id) ha
    omega
  have hle : ∑ a ∈ A, (1 : ℚ) / 2 ^ a ≤ ∑ a ∈ Finset.range (M + 1), (1 : ℚ) / 2 ^ a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rw [sum_range_dyadic] at hle
  have hpos : (0 : ℚ) < (1 : ℚ) / 2 ^ M := by positivity
  linarith

private lemma sum_univ_succAbove_eq {M : Type*} [AddCommMonoid M] {n : ℕ}
    (i : Fin (n + 1)) (g : Fin (n + 1) → M) :
    ∑ x : Fin (n + 1), g x = g i + ∑ k : Fin n, g (i.succAbove k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  refine (Finset.sum_bij (fun k _ => i.succAbove k) ?_ ?_ ?_ ?_).symm
  · intro k _
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩
  · intro k1 _ k2 _ h
    exact Fin.succAbove_right_injective h
  · intro x hx
    rcases Fin.exists_succAbove_eq (Finset.mem_erase.mp hx).1 with ⟨k, rfl⟩
    exact ⟨k, Finset.mem_univ k, rfl⟩
  · intro _ _
    rfl

private lemma dyadic_partition {s : ℕ} (d : Fin s → ℕ) (hd : StrictMono d) :
    ∀ (K : ℕ) (f : Fin K → ℕ),
      (∑ i : Fin K, (1 : ℚ) / 2 ^ (f i)) = (∑ j : Fin s, (1 : ℚ) / 2 ^ (d j)) →
      ∃ (owner : Fin K → Fin s) (off : Fin K → Fin (K + 1)),
        (∀ j : Fin s,
          (∑ i : Fin K, if owner i = j then 2 ^ (K - (off i).val) else 0) = 2 ^ K) ∧
        (∀ i : Fin K, f i = d (owner i) + (off i).val) := by
  intro K
  induction K with
  | zero =>
    intro f hf
    refine ⟨Fin.elim0, Fin.elim0, ?_, fun i => Fin.elim0 i⟩
    intro j
    have hpos : (0 : ℚ) < (1 : ℚ) / 2 ^ (d j) := by positivity
    have hge : (1 : ℚ) / 2 ^ (d j) ≤ ∑ j' : Fin s, (1 : ℚ) / 2 ^ (d j') :=
      Finset.single_le_sum (f := fun j' : Fin s => (1 : ℚ) / 2 ^ (d j'))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hf
    linarith
  | succ K ih =>
    intro f hf
    by_cases hinj : Function.Injective f
    · have hImgF : ∑ i : Fin (K + 1), (1 : ℚ) / 2 ^ (f i) =
          ∑ a ∈ Finset.univ.image f, (1 : ℚ) / 2 ^ a :=
        (Finset.sum_image (f := fun a : ℕ => (1 : ℚ) / 2 ^ a) fun _ _ _ _ h => hinj h).symm
      have hImgD : ∑ j : Fin s, (1 : ℚ) / 2 ^ (d j) =
          ∑ b ∈ Finset.univ.image d, (1 : ℚ) / 2 ^ b :=
        (Finset.sum_image (f := fun a : ℕ => (1 : ℚ) / 2 ^ a) fun _ _ _ _ h => hd.injective h).symm
      rw [hImgF, hImgD] at hf
      have heq_img : Finset.univ.image f = Finset.univ.image d := dyadic_finset_inj _ _ hf
      have hex : ∀ i : Fin (K + 1), ∃ j : Fin s, d j = f i := by
        intro i
        have hmem : f i ∈ Finset.univ.image d := by
          rw [← heq_img]
          exact Finset.mem_image_of_mem f (Finset.mem_univ i)
        rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
        exact ⟨j, hj⟩
      choose owner howner using hex
      refine ⟨owner, fun _ => ⟨0, Nat.succ_pos _⟩, ?_, fun i => by simp [howner i]⟩
      intro j
      have hmem : d j ∈ Finset.univ.image f := by
        rw [heq_img]
        exact Finset.mem_image_of_mem d (Finset.mem_univ j)
      rcases Finset.mem_image.mp hmem with ⟨i0, _, hi0⟩
      have hi0_own : owner i0 = j := hd.injective (by rw [howner i0, hi0])
      have huniq : ∀ i : Fin (K + 1), owner i = j ↔ i = i0 := by
        intro i
        constructor
        · intro h
          apply hinj
          rw [← howner i, h, hi0]
        · rintro rfl
          exact hi0_own
      simp only [Nat.sub_zero, huniq]
      simp
    · unfold Function.Injective at hinj
      push Not at hinj
      rcases hinj with ⟨i1, i2, hfeq, hne⟩
      have hfpos : 1 ≤ f i1 := by
        by_contra h0
        have hf0 : f i1 = 0 := by omega
        have hf0' : f i2 = 0 := by omega
        have hge2 : (2 : ℚ) ≤ ∑ i : Fin (K + 1), (1 : ℚ) / 2 ^ (f i) := by
          have hsub : ({i1, i2} : Finset (Fin (K + 1))) ⊆ Finset.univ := Finset.subset_univ _
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (f := fun i => (1 : ℚ) / 2 ^ (f i)) (fun _ _ _ => by positivity)
          rw [Finset.sum_pair hne, hf0, hf0'] at hle
          linarith [show (1 : ℚ) / 2 ^ 0 + (1 : ℚ) / 2 ^ 0 = 2 by norm_num]
        have hImgD : ∑ j : Fin s, (1 : ℚ) / 2 ^ (d j) =
            ∑ b ∈ Finset.univ.image d, (1 : ℚ) / 2 ^ b :=
          (Finset.sum_image (f := fun a : ℕ => (1 : ℚ) / 2 ^ a) fun _ _ _ _ h => hd.injective h).symm
        have hlt2 := dyadic_finset_sum_lt_two (Finset.univ.image d)
        linarith
      rcases Fin.exists_succAbove_eq hne with ⟨k1, hk1⟩
      let f' : Fin K → ℕ := fun k => if k = k1 then f i1 - 1 else f (i2.succAbove k)
      have hf'_sum : (∑ k : Fin K, (1 : ℚ) / 2 ^ (f' k)) =
          ∑ j : Fin s, (1 : ℚ) / 2 ^ (d j) := by
        rw [← hf, sum_univ_succAbove_eq i2]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k1)]
        conv_rhs => rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K)) _ (Finset.mem_univ k1)]
        have hrest : (∑ k ∈ Finset.univ.erase k1, (1 : ℚ) / 2 ^ (f' k)) =
            ∑ k ∈ Finset.univ.erase k1, (1 : ℚ) / 2 ^ (f (i2.succAbove k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hne_k : k ≠ k1 := (Finset.mem_erase.mp hk).1
          simp [f', hne_k]
        rw [hrest]
        have hhead : (1 : ℚ) / 2 ^ (f' k1) =
            (1 : ℚ) / 2 ^ (f i2) + (1 : ℚ) / 2 ^ (f (i2.succAbove k1)) := by
          simp only [f', ite_true, hk1, ← hfeq]
          have hpow : (2 : ℚ) ^ (f i1) = 2 * (2 : ℚ) ^ (f i1 - 1) := by
            have : f i1 = (f i1 - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ]
            ring
          rw [hpow]
          ring
        linarith
      rcases ih f' hf'_sum with ⟨owner', off', hsum', hval'⟩
      let owner : Fin (K + 1) → Fin s := fun i =>
        if hi : i = i2 then owner' k1
        else owner' (Classical.choose (Fin.exists_succAbove_eq hi))
      let off : Fin (K + 1) → Fin (K + 2) := fun i =>
        if hi : i = i2 then ⟨(off' k1).val + 1, by omega⟩
        else
          let k := Classical.choose (Fin.exists_succAbove_eq hi)
          if k = k1 then ⟨(off' k1).val + 1, by omega⟩
          else ⟨(off' k).val, by omega⟩
      have hchoose : ∀ k : Fin K,
          Classical.choose (Fin.exists_succAbove_eq (Fin.succAbove_ne i2 k)) = k := by
        intro k
        exact Fin.succAbove_right_injective
          (Classical.choose_spec (Fin.exists_succAbove_eq (Fin.succAbove_ne i2 k)))
      have hown_sa : ∀ k : Fin K, owner (i2.succAbove k) = owner' k := by
        intro k
        simp only [owner, Fin.succAbove_ne i2 k, dite_false, hchoose k]
      have hoff_sa : ∀ k : Fin K, (off (i2.succAbove k)).val =
          if k = k1 then (off' k1).val + 1 else (off' k).val := by
        intro k
        simp only [off, Fin.succAbove_ne i2 k, dite_false, hchoose k]
        split_ifs <;> rfl
      refine ⟨owner, off, ?_, ?_⟩
      · intro j
        rw [sum_univ_succAbove_eq i2]
        have htarget : 2 ^ (K + 1) =
            2 * ∑ k : Fin K, if owner' k = j then 2 ^ (K - (off' k).val) else 0 := by
          rw [hsum' j, pow_succ]
          ring
        rw [htarget, Finset.mul_sum]
        rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K)) _ (Finset.mem_univ k1)]
        conv_rhs => rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K)) _ (Finset.mem_univ k1)]
        have hrest : (∑ k ∈ Finset.univ.erase k1,
            if owner (i2.succAbove k) = j then 2 ^ (K + 1 - (off (i2.succAbove k)).val) else 0) =
            ∑ k ∈ Finset.univ.erase k1,
            2 * (if owner' k = j then 2 ^ (K - (off' k).val) else 0) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hne_k : k ≠ k1 := (Finset.mem_erase.mp hk).1
          rw [hown_sa k, hoff_sa k]
          simp only [hne_k, ite_false]
          have hle : (off' k).val ≤ K := by omega
          split_ifs
          · have : K + 1 - (off' k).val = (K - (off' k).val) + 1 := by omega
            rw [this, pow_succ]
            ring
          · simp
        rw [hrest]
        have hown_i2 : owner i2 = owner' k1 := by simp [owner]
        have hoff_i2 : (off i2).val = (off' k1).val + 1 := by simp [off]
        rw [hown_i2, hoff_i2, hown_sa k1, hoff_sa k1]
        simp only [ite_true]
        have hsub : K + 1 - ((off' k1).val + 1) = K - (off' k1).val := by omega
        rw [hsub]
        split_ifs <;> ring
      · intro i
        by_cases hi : i = i2
        · rw [hi]
          have hown_i2 : owner i2 = owner' k1 := by simp [owner]
          have hoff_i2 : (off i2).val = (off' k1).val + 1 := by simp [off]
          rw [hown_i2, hoff_i2]
          have hv := hval' k1
          simp only [f', ite_true] at hv
          omega
        · rcases Fin.exists_succAbove_eq hi with ⟨k, rfl⟩
          rw [hown_sa k, hoff_sa k]
          have hv := hval' k
          by_cases hk : k = k1
          · subst hk
            simp only [ite_true]
            simp only [f', ite_true] at hv
            rw [hk1]
            omega
          · simp only [hk, ite_false]
            simp only [f', hk, ite_false] at hv
            exact hv

private lemma strictMono_iff_step {s : ℕ} (hs : 0 < s) (a : ℕ) (d : Fin s → ℕ) :
    (StrictMono d ∧ ∃ j : Fin s, d j ≤ a) ↔
      (∀ k : Fin (s - 1), d ⟨k.val, by omega⟩ + 1 ≤ d ⟨k.val + 1, by omega⟩) ∧
      d ⟨0, hs⟩ ≤ a := by
  constructor
  · rintro ⟨hsm, j, hj⟩
    refine ⟨fun k => ?_, ?_⟩
    · have hlt : (⟨k.val, by omega⟩ : Fin s) < ⟨k.val + 1, by omega⟩ := by
        simp [Fin.lt_def]
      exact Nat.succ_le_of_lt (hsm hlt)
    · have hle : (⟨0, hs⟩ : Fin s) ≤ j := Nat.zero_le j.val
      exact le_trans (hsm.monotone hle) hj
  · rintro ⟨hstep, h0⟩
    refine ⟨?_, ⟨0, hs⟩, h0⟩
    have haux : ∀ (b x : ℕ) (hb : b < s) (hx : x < s), x < b → d ⟨x, hx⟩ < d ⟨b, hb⟩ := by
      intro b
      induction b with
      | zero =>
        intro _ _ _ h
        omega
      | succ b ih =>
        intro x hb hx hxb
        have hstep_b := hstep ⟨b, by omega⟩
        dsimp only at hstep_b
        by_cases heq : x = b
        · subst heq
          omega
        · have h1 := ih x (by omega) hx (by omega)
          omega
    intro i j hij
    exact haux j.val i.val j.isLt i.isLt hij

abbrev Template (a s : ℕ) :=
  Σ (c : Fin (8 * (a + 1) + 1)),
    (((Fin c.val × Bool) × (Fin c.val × Bool)) → Bool) ×
    (Sig c.val → Bool) ×
    ((Fin c.val → Bool) → Fin s) ×
    ((Fin c.val → Bool) → Fin (2 ^ c.val + 1))

noncomputable def validTemplate (a s : ℕ) (t : Template a s) : Bool :=
  let c := t.1.val
  let Aint := t.2.1
  let Spres := t.2.2.1
  let owner := t.2.2.2.1
  let off := t.2.2.2.2
  decide (∀ j : Fin s,
    (∑ α : Fin c → Bool,
      if isAlive c Aint Spres α = true ∧ owner α = j
      then 2 ^ (2 ^ c - (off α).val) else 0) = 2 ^ (2 ^ c))

abbrev ValidTemplate (a s : ℕ) := {t : Template a s // validTemplate a s t = true}

noncomputable def sysOfTemplate (a s : ℕ) (hs : 0 < s) (t : ValidTemplate a s) : LinSys s :=
  let c := t.1.1.val
  let Aint := t.1.2.1
  let Spres := t.1.2.2.1
  let owner := t.1.2.2.2.1
  let off := t.1.2.2.2.2
  let EqIdx := Fin (s - 1) ⊕ Unit ⊕ {α : Fin c → Bool // isAlive c Aint Spres α = true}
  let VarIdx := {σ : Sig c // Spres σ = true} ⊕ Fin (s - 1) ⊕ Unit
  let PL : EqIdx → Fin s → ℕ := fun e j =>
    match e with
    | Sum.inl k => if j = ⟨k.val + 1, by omega⟩ then 1 else 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr α) => if j = owner α.1 then 1 else 0
  let PR : EqIdx → Fin s → ℕ := fun e j =>
    match e with
    | Sum.inl k => if j = ⟨k.val, by omega⟩ then 1 else 0
    | Sum.inr (Sum.inl _) => if j = ⟨0, hs⟩ then 1 else 0
    | Sum.inr (Sum.inr _) => 0
  let Q : EqIdx → VarIdx → ℕ := fun e r =>
    match e, r with
    | Sum.inl k, Sum.inr (Sum.inl k') => if k = k' then 1 else 0
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
    | Sum.inr (Sum.inr α), Sum.inl σ => forced c σ.1 α.1
    | _, _ => 0
  let cL : EqIdx → ℕ := fun e =>
    match e with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => a
    | Sum.inr (Sum.inr α) => (off α.1).val
  let cR : EqIdx → ℕ := fun e =>
    match e with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr α) => c + ∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α.1
  mkLinSys PL PR Q cL cR

private lemma solves_sysOfTemplate_iff (a s : ℕ) (hs : 0 < s) (t : ValidTemplate a s)
    (d : Fin s → ℕ) :
    Solves (sysOfTemplate a s hs t) d ↔
      (∀ k : Fin (s - 1), d ⟨k.val, by omega⟩ + 1 ≤ d ⟨k.val + 1, by omega⟩) ∧
      d ⟨0, hs⟩ ≤ a ∧
      ∃ m : {σ : Sig t.1.1.val // t.1.2.2.1 σ = true} → ℕ,
        ∀ α : Fin t.1.1.val → Bool, isAlive t.1.1.val t.1.2.1 t.1.2.2.1 α = true →
          d (t.1.2.2.2.1 α) + (t.1.2.2.2.2 α).val =
            t.1.1.val + ∑ σ : {σ : Sig t.1.1.val // t.1.2.2.1 σ = true},
              forced t.1.1.val σ.1 α * (m σ + 1) := by
  rcases t with ⟨⟨⟨c, hc⟩, Aint, Spres, owner, off⟩, hvalid⟩
  dsimp only [sysOfTemplate]
  rw [solves_mkLinSys]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun k => ?_, ?_, fun σ => y (Sum.inl σ), fun α hα => ?_⟩
    · have hk := hy (Sum.inl k)
      simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add] at hk
      omega
    · have h0 := hy (Sum.inr (Sum.inl ()))
      simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add,
        Fintype.sum_unique] at h0
      omega
    · have ha := hy (Sum.inr (Sum.inr ⟨α, hα⟩))
      simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add] at ha
      have hmul : (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α * (y (Sum.inl σ) + 1)) =
          (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α * y (Sum.inl σ)) +
          (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ _ => by ring
      rw [hmul]
      omega
  · rintro ⟨hstep, h0, m, hm⟩
    let y : ({σ : Sig c // Spres σ = true} ⊕ Fin (s - 1) ⊕ Unit) → ℕ := fun r =>
      match r with
      | Sum.inl σ => m σ
      | Sum.inr (Sum.inl k) => d ⟨k.val + 1, by omega⟩ - (d ⟨k.val, by omega⟩ + 1)
      | Sum.inr (Sum.inr _) => a - d ⟨0, hs⟩
    refine ⟨y, fun e => ?_⟩
    rcases e with k | (⟨⟩ | ⟨α, hα⟩)
    · have hk := hstep k
      simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add]
      dsimp only [y]
      omega
    · simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add,
        Fintype.sum_unique]
      dsimp only [y]
      omega
    · have ha := hm α hα
      simp only [Fintype.sum_sum_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add]
      dsimp only [y]
      have hmul : (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α * (m σ + 1)) =
          (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α * m σ) +
          (∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ _ => by ring
      rw [hmul] at ha
      omega

private lemma dyadic_combine {c s : ℕ}
    (Aint : ((Fin c × Bool) × (Fin c × Bool)) → Bool)
    (Spres : Sig c → Bool)
    (owner : (Fin c → Bool) → Fin s)
    (off : (Fin c → Bool) → Fin (2 ^ c + 1))
    (e : (Fin c → Bool) → ℕ)
    (d : Fin s → ℕ)
    (hvalid : ∀ j : Fin s,
      (∑ α : Fin c → Bool,
        if isAlive c Aint Spres α = true ∧ owner α = j
        then 2 ^ (2 ^ c - (off α).val) else 0) = 2 ^ (2 ^ c))
    (heq : ∀ α : Fin c → Bool, isAlive c Aint Spres α = true →
      d (owner α) + (off α).val = e α) :
    (∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
      (1 : ℚ) / (2 : ℚ) ^ (e α)) =
    ∑ j : Fin s, (1 : ℚ) / (2 : ℚ) ^ (d j) := by
  have h1 : (∑ α ∈ Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true),
      (1 : ℚ) / (2 : ℚ) ^ (e α)) =
      ∑ j : Fin s, ∑ α : Fin c → Bool,
        if isAlive c Aint Spres α = true ∧ owner α = j
        then (1 : ℚ) / (2 : ℚ) ^ (e α) else 0 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hα : isAlive c Aint Spres α = true
    · simp [hα]
    · simp [hα]
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm : (∑ α : Fin c → Bool,
      if isAlive c Aint Spres α = true ∧ owner α = j
      then (1 : ℚ) / (2 : ℚ) ^ (e α) else 0) =
      ((∑ α : Fin c → Bool,
        if isAlive c Aint Spres α = true ∧ owner α = j
        then 2 ^ (2 ^ c - (off α).val) else 0 : ℕ) : ℚ) /
      ((2 : ℚ) ^ (d j) * (2 : ℚ) ^ (2 ^ c)) := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs with h
    · rcases h with ⟨hα, hown⟩
      have hde := heq α hα
      rw [hown] at hde
      rw [← hde]
      have hle : (off α).val ≤ 2 ^ c := by omega
      have h2ne : (2 : ℚ) ^ (d j + (off α).val) ≠ 0 := by positivity
      have h2ne' : (2 : ℚ) ^ (d j) * (2 : ℚ) ^ (2 ^ c) ≠ 0 := by positivity
      rw [div_eq_div_iff h2ne h2ne', one_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    · simp
  rw [hterm, hvalid j]
  have h2ne : (2 : ℚ) ^ (2 ^ c) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma spectrum_iff_exists_solves (a s : ℕ) (hs : 0 < s) (d : Fin s → ℕ) :
    (StrictMono d ∧ (∃ j : Fin s, d j ≤ a) ∧
      ∃ (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))),
        (mass n A : ℚ) / (2 : ℚ) ^ n = ∑ j : Fin s, (1 : ℚ) / (2 : ℚ) ^ (d j)) ↔
    ∃ t : ValidTemplate a s, Solves (sysOfTemplate a s hs t) d := by
  constructor
  · rintro ⟨hsm, ⟨j, hj⟩, n, A, hmass⟩
    have ⟨hstep, hd0⟩ := (strictMono_iff_step hs a d).mp ⟨hsm, j, hj⟩
    have hge_a : (1 : ℚ) / (2 : ℚ) ^ a ≤ (mass n A : ℚ) / (2 : ℚ) ^ n := by
      rw [hmass]
      have h1 : (1 : ℚ) / (2 : ℚ) ^ a ≤ (1 : ℚ) / (2 : ℚ) ^ (d ⟨0, hs⟩) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact pow_le_pow_right₀ (by norm_num) hd0
      have h2 : (1 : ℚ) / (2 : ℚ) ^ (d ⟨0, hs⟩) ≤ ∑ j' : Fin s, (1 : ℚ) / (2 : ℚ) ^ (d j') :=
        Finset.single_le_sum (f := fun j' : Fin s => (1 : ℚ) / (2 : ℚ) ^ (d j'))
          (fun _ _ => by positivity) (Finset.mem_univ (⟨0, hs⟩ : Fin s))
      exact le_trans h1 h2
    have hdense : 2 ^ n ≤ 2 ^ a * mass n A := by
      have h2a : (0 : ℚ) < (2 : ℚ) ^ a := by positivity
      have h2n : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
      have hq : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ a * (mass n A : ℚ) := by
        rw [div_le_div_iff₀ h2a h2n] at hge_a
        linarith
      exact_mod_cast hq
    have hpos : 0 < mass n A := by
      by_contra h0
      have hm0 : mass n A = 0 := by omega
      rw [hm0, mul_zero] at hdense
      have := Nat.two_pow_pos n
      omega
    rcases exists_small_vertex_cover A hpos hdense with ⟨U, hUcard, hUcov⟩
    generalize hc_eq : U.card = c at hUcard
    rcases forward_representation A U hc_eq hUcov with ⟨Aint, Spres, m, hrep⟩
    set Alive := Finset.univ.filter (fun α : Fin c → Bool => isAlive c Aint Spres α = true)
    let K := Alive.card
    let eAl : Fin K ≃ {α : Fin c → Bool // α ∈ Alive} :=
      (Fintype.equivFinOfCardEq (Fintype.card_coe Alive)).symm
    let expOf : (Fin c → Bool) → ℕ := fun α =>
      c + ∑ σ : {σ : Sig c // Spres σ = true}, forced c σ.1 α * (m σ + 1)
    have hK_le : K ≤ 2 ^ c := by
      have hle := Finset.card_le_univ Alive
      simpa [K, Fintype.card_pi_const] using hle
    have hsumK : (∑ i : Fin K, (1 : ℚ) / (2 : ℚ) ^ (expOf (eAl i).1)) =
        ∑ j' : Fin s, (1 : ℚ) / (2 : ℚ) ^ (d j') := by
      rw [← hmass, hrep]
      rw [← Finset.sum_coe_sort Alive]
      exact Fintype.sum_equiv eAl _ _ (fun _ => rfl)
    rcases dyadic_partition d hsm K (fun i => expOf (eAl i).1) hsumK with
      ⟨ownerK, offK, hsum_offK, hval_offK⟩
    let owner : (Fin c → Bool) → Fin s := fun α =>
      if hα : α ∈ Alive then ownerK (eAl.symm ⟨α, hα⟩) else ⟨0, hs⟩
    let off : (Fin c → Bool) → Fin (2 ^ c + 1) := fun α =>
      if hα : α ∈ Alive then ⟨(offK (eAl.symm ⟨α, hα⟩)).val, by
        have := (offK (eAl.symm ⟨α, hα⟩)).isLt
        omega⟩
      else ⟨0, Nat.succ_pos _⟩
    let rawT : Template a s := ⟨⟨c, by omega⟩, Aint, Spres, owner, off⟩
    have hvalid : validTemplate a s rawT = true := by
      simp only [validTemplate, decide_eq_true_eq]
      intro j'
      have hmul_eq : (∑ α : Fin c → Bool,
          if isAlive c Aint Spres α = true ∧ owner α = j'
          then 2 ^ (2 ^ c - (off α).val) else 0) =
          2 ^ (2 ^ c - K) *
            (∑ i : Fin K, if ownerK i = j' then 2 ^ (K - (offK i).val) else 0) := by
        rw [Finset.mul_sum]
        have hstep1 : (∑ α : Fin c → Bool,
            if isAlive c Aint Spres α = true ∧ owner α = j'
            then 2 ^ (2 ^ c - (off α).val) else 0) =
            ∑ α ∈ Alive, if owner α = j' then 2 ^ (2 ^ c - (off α).val) else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun α _ => ?_
          by_cases hα : isAlive c Aint Spres α = true <;> simp [hα]
        rw [hstep1, ← Finset.sum_coe_sort Alive]
        refine (Fintype.sum_equiv eAl _ _ fun i => ?_).symm
        have hmem : (eAl i).1 ∈ Alive := (eAl i).2
        have hown_i : owner (eAl i).1 = ownerK i := by
          simp [owner, hmem]
        have hoff_i : (off (eAl i).1).val = (offK i).val := by
          simp [off, hmem]
        rw [hown_i, hoff_i]
        split_ifs
        · rw [← pow_add]
          congr 1
          have := (offK i).isLt
          omega
        · simp
      rw [hmul_eq, hsum_offK j', ← pow_add, Nat.sub_add_cancel hK_le]
    refine ⟨⟨rawT, hvalid⟩, ?_⟩
    rw [solves_sysOfTemplate_iff]
    refine ⟨hstep, hd0, m, fun α hα => ?_⟩
    have hmem : α ∈ Alive := by
      simp only [Alive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hα
    have hown : owner α = ownerK (eAl.symm ⟨α, hmem⟩) := by simp [owner, hmem]
    have hoff : (off α).val = (offK (eAl.symm ⟨α, hmem⟩)).val := by simp [off, hmem]
    change d (owner α) + (off α).val = expOf α
    rw [hown, hoff]
    have hv := hval_offK (eAl.symm ⟨α, hmem⟩)
    simpa using hv.symm
  · rintro ⟨t, hsol⟩
    rw [solves_sysOfTemplate_iff] at hsol
    rcases hsol with ⟨hstep, hd0, m, hm⟩
    have ⟨hsm, hj⟩ := (strictMono_iff_step hs a d).mpr ⟨hstep, hd0⟩
    refine ⟨hsm, hj, ?_⟩
    rcases converse_realization t.1.1.val t.1.2.1 t.1.2.2.1 m with ⟨n, A, hmass⟩
    refine ⟨n, A, ?_⟩
    rw [hmass]
    have hvalid := t.2
    simp only [validTemplate, decide_eq_true_eq] at hvalid
    exact dyadic_combine t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2
      (fun α => t.1.1.val + ∑ σ : {σ : Sig t.1.1.val // t.1.2.2.1 σ = true},
        forced t.1.1.val σ.1 α * (m σ + 1))
      d hvalid hm

end PEqualNP.Outside.L_lib_723_aux

theorem PEqualNP.Outside.L_lib_723 : (let mass := fun (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))) =>
  (Finset.univ.filter (fun x : Fin n → Bool => ∀ c ∈ A,
    x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2)).card
∀ a s : ℕ,
  let spectrum := fun depths : Fin s → ℕ =>
    StrictMono depths ∧ (∃ j : Fin s, depths j ≤ a) ∧
      ∃ (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))),
        (mass n A : ℚ) / 2 ^ n = ∑ j : Fin s, (1 : ℚ) / 2 ^ (depths j)
  ∃ (states : ℕ) (start : Fin states)
    (step : Fin states → (Fin s → Bool) → Fin states)
    (accept : Fin states → Bool),
    ∀ (depths : Fin s → ℕ) (len : ℕ), (∀ j, depths j < 2 ^ len) →
      let finish := (List.range len).foldl (fun state pos =>
        step state (fun j => (depths j).testBit pos)) start
      (accept finish = true ↔ spectrum depths)) := by
  intro mass a s spectrum
  by_cases hs : 0 < s
  · rcases PEqualNP.Outside.L_lib_723_aux.dfa_of_linSys_family
        (PEqualNP.Outside.L_lib_723_aux.sysOfTemplate a s hs) with
      ⟨states, start, step, accept, hdfa⟩
    refine ⟨states, start, step, accept, fun depths len hlen => ?_⟩
    dsimp only [spectrum, mass]
    have h1 := hdfa depths len hlen
    dsimp only at h1
    rw [h1]
    exact (PEqualNP.Outside.L_lib_723_aux.spectrum_iff_exists_solves a s hs depths).symm
  · have hs0 : s = 0 := by omega
    subst hs0
    refine ⟨1, ⟨0, by decide⟩, fun st _ => st, fun _ => false, fun depths len _ => ?_⟩
    dsimp only [spectrum]
    constructor
    · intro h
      cases h
    · rintro ⟨_, ⟨j, _⟩, _⟩
      exact Fin.elim0 j
