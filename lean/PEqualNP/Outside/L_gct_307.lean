import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

namespace PEqualNP.Outside.L_gct_307

namespace G280

noncomputable section

abbrev V3 := Fin 3 → ℂ
abbrev Triple := V3 × V3 × V3

def had (u : V3) : Fin 4 → ℂ :=
  ![u 0 + u 1 + u 2, u 0 - u 1 - u 2, -u 0 + u 1 - u 2, -u 0 - u 1 + u 2]

def invHad (v : Fin 4 → ℂ) : V3 :=
  ![(v 0 + v 1) / 2, (v 0 + v 2) / 2, (v 0 + v 3) / 2]

theorem had_invHad (v : Fin 4 → ℂ) (hv : (∑ i : Fin 4, v i) = 0) :
    had (invHad v) = v := by
  rw [Fin.sum_univ_four] at hv
  funext i
  fin_cases i
  · change (v 0 + v 1) / 2 + (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 0
    linear_combination hv / 2
  · change (v 0 + v 1) / 2 - (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 1
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) + (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 2
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) - (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 3
    linear_combination -hv / 2

def toTriple : (Fin 3 → Fin 4 → ℂ) →ₗ[ℂ] Triple where
  toFun X := (invHad (X 0), invHad (X 1), invHad (X 2))
  map_add' X Y := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring
  map_smul' c X := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring

theorem toTriple_inj_on_zeroSum {X Y : Fin 3 → Fin 4 → ℂ}
    (hX : ∀ r : Fin 3, (∑ i : Fin 4, X r i) = 0)
    (hY : ∀ r : Fin 3, (∑ i : Fin 4, Y r i) = 0)
    (heq : toTriple X = toTriple Y) : X = Y := by
  funext r
  have h1 : invHad (X r) = invHad (Y r) := by
    fin_cases r
    · exact congrArg Prod.fst heq
    · exact congrArg (fun p => p.2.1) heq
    · exact congrArg (fun p => p.2.2) heq
  rw [← had_invHad (X r) (hX r), ← had_invHad (Y r) (hY r), h1]

def c1 (a : ℕ) : ℤ := if a % 5 = 0 then 5 else 0
def c2 (a b : ℕ) : ℤ := c1 a * c1 b - c1 (a + b)
def c3 (a b c : ℕ) : ℤ := c2 a b * c1 c - c2 (a + c) b - c2 a (b + c)
def c4 (a b c d : ℕ) : ℤ := c3 a b c * c1 d - c3 (a + d) b c - c3 a (b + d) c - c3 a b (c + d)

def S1 (ζ : ℂ) (a : ℕ) : ℂ := ∑ x0 : Fin 5, ζ ^ (a * x0.val)

def S2 (ζ : ℂ) (a b : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)

def S3 (ζ : ℂ) (a b c : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ζ ^ (a * x0.val + b * x1.val + c * x2.val)

def S4 (ζ : ℂ) (a b c d : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
      ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)

theorem S1_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) : S1 ζ a = (c1 a : ℂ) := by
  unfold S1 c1
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  by_cases hmod : a % 5 = 0
  · simp only [hmod, ↓reduceIte, Int.cast_ofNat]
    have hdvd : 5 ∣ a := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, rfl⟩ := hdvd
    have hterm : ∀ x : Fin 5, ζ ^ (5 * q * x.val) = 1 := by
      intro x
      rw [show 5 * q * x.val = 5 * (q * x.val) by ring, pow_mul, h5, one_pow]
    simp [hterm]
  · simp only [hmod, ↓reduceIte, Int.cast_zero]
    have hne : ζ ^ a ≠ 1 := by
      intro h1
      have hdvd : 5 ∣ a := hζ.pow_eq_one_iff_dvd a |>.mp h1
      exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
    have hmul : (ζ ^ a - 1) * (∑ x0 : Fin 5, ζ ^ (a * x0.val)) = 0 := by
      rw [Fin.sum_univ_five]
      have hpow : ∀ k : ℕ, ζ ^ (a * k) = (ζ ^ a) ^ k := fun k => pow_mul ζ a k
      have hv3 : (3 : Fin 5).val = 3 := rfl
      have hv4 : (4 : Fin 5).val = 4 := rfl
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hv3, hv4, hpow]
      have h5a : (ζ ^ a) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
      linear_combination h5a
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

theorem S2_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b : ℕ) : S2 ζ a b = (c2 a b : ℂ) := by
  unfold S2 c2
  have hinner : ∀ x0 : Fin 5,
      (∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)) =
      ζ ^ (a * x0.val) * S1 ζ b - ζ ^ ((a + b) * x0.val) := by
    intro x0
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x1 : Fin 5, ζ ^ (a * x0.val + b * x1.val)) = ζ ^ (a * x0.val) * S1 ζ b := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x1 _ => ?_
      rw [pow_add]
    rw [hsplit, add_mul]
  simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change S1 ζ a * S1 ζ b - S1 ζ (a + b) = _
  rw [S1_eq hζ, S1_eq hζ, S1_eq hζ]
  push_cast
  rfl

theorem S3_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c : ℕ) : S3 ζ a b c = (c3 a b c : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0,
      (∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
      ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
      ζ ^ ((a + c) * x0.val + b * x1.val) -
      ζ ^ (a * x0.val + (b + c) * x1.val) := by
    intro x0 x1 hx1
    rw [Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x2 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
        ζ ^ (a * x0.val + b * x1.val) * S1 ζ c := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x0.val = (a + c) * x0.val + b * x1.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x1.val = a * x0.val + (b + c) * x1.val := by ring
    rw [h1, h2]
  have hsum : S3 ζ a b c = S2 ζ a b * S1 ζ c - S2 ζ (a + c) b - S2 ζ a (b + c) := by
    unfold S3 S2
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            ∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            (ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
             ζ ^ ((a + c) * x0.val + b * x1.val) -
             ζ ^ (a * x0.val + (b + c) * x1.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 => hinner x0 x1 hx1
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S2_eq hζ, S2_eq hζ, S2_eq hζ, S1_eq hζ]
  unfold c3
  push_cast
  rfl

theorem S4_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c d : ℕ) : S4 ζ a b c d = (c4 a b c d : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0, ∀ x2 ∈ (Finset.univ.erase x0).erase x1,
      (∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
        ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
      ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
      ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val) := by
    intro x0 x1 hx1 x2 hx2
    rw [Finset.sum_erase_eq_sub hx2, Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x3 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
        ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x3 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x2.val + d * x0.val = (a + d) * x0.val + b * x1.val + c * x2.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x2.val + d * x1.val = a * x0.val + (b + d) * x1.val + c * x2.val := by ring
    have h3 : a * x0.val + b * x1.val + c * x2.val + d * x2.val = a * x0.val + b * x1.val + (c + d) * x2.val := by ring
    rw [h1, h2, h3]
  have hsum : S4 ζ a b c d = S3 ζ a b c * S1 ζ d - S3 ζ (a + d) b c - S3 ζ a (b + d) c - S3 ζ a b (c + d) := by
    unfold S4 S3
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
              ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            (ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
             ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 =>
            Finset.sum_congr rfl fun x2 hx2 => hinner x0 x1 hx1 x2 hx2
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S3_eq hζ, S3_eq hζ, S3_eq hζ, S3_eq hζ, S1_eq hζ]
  unfold c4
  push_cast
  rfl

theorem sum_emb_eq_S4 (ζ : ℂ) (a b c d : ℕ) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (a * (f 0).val + b * (f 1).val + c * (f 2).val + d * (f 3).val)) =
    S4 ζ a b c d := by
  unfold S4
  let Q : Finset (Σ x0 : Fin 5, Σ x1 : Fin 5, Σ x2 : Fin 5, Fin 5) :=
    Finset.univ.sigma fun x0 => (Finset.univ.erase x0).sigma fun x1 =>
      ((Finset.univ.erase x0).erase x1).sigma fun x2 => (((Finset.univ.erase x0).erase x1).erase x2)
  have hQ : (∑ p ∈ Q, ζ ^ (a * p.1.val + b * p.2.1.val + c * p.2.2.1.val + d * p.2.2.2.val)) =
      ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
        ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
          ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val) := by
    simp only [Q, Finset.sum_sigma]
  rw [← hQ]
  refine Finset.sum_bij (fun f _ => ⟨f 0, f 1, f 2, f 3⟩) ?_ ?_ ?_ ?_
  · intro f _
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
    refine ⟨f.injective.ne (by decide : (1 : Fin 4) ≠ 0),
      ⟨f.injective.ne (by decide : (2 : Fin 4) ≠ 1), f.injective.ne (by decide : (2 : Fin 4) ≠ 0)⟩,
      f.injective.ne (by decide : (3 : Fin 4) ≠ 2),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 1),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 0)⟩
  · intro f _ g _ heq
    apply Function.Embedding.ext
    intro i
    have h0 : f 0 = g 0 := congrArg Sigma.fst heq
    have h1 : f 1 = g 1 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.1) heq
    have h2 : f 2 = g 2 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.1) heq
    have h3 : f 3 = g 3 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.2) heq
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro p hp
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and] at hp
    rcases p with ⟨x0, x1, x2, x3⟩
    rcases hp with ⟨h10, ⟨h21, h20⟩, h32, h31, h30⟩
    have hinj : Function.Injective ![x0, x1, x2, x3] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | exact absurd hij h10 | exact absurd hij.symm h10
        | exact absurd hij h20 | exact absurd hij.symm h20
        | exact absurd hij h21 | exact absurd hij.symm h21
        | exact absurd hij h30 | exact absurd hij.symm h30
        | exact absurd hij h31 | exact absurd hij.symm h31
        | exact absurd hij h32 | exact absurd hij.symm h32
    refine ⟨⟨![x0, x1, x2, x3], hinj⟩, Finset.mem_univ _, rfl⟩
  · intro f _
    rfl

def dot3 (u v : V3) : ℂ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def C3 (u : V3) : V3 := ![u 1 * u 2, u 2 * u 0, u 0 * u 1]

def D3 (u : V3) : V3 :=
  ![u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2),
    u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2),
    u 2 * (u 2 ^ 2 - u 0 ^ 2 - u 1 ^ 2)]

def Q2 (y z : V3) : ℂ := dot3 y z

def Q3 (x y z : V3) : ℂ := dot3 z (C3 x) + dot3 x (C3 y)

def R4 (y z : V3) : ℂ :=
  120 * (y 0 ^ 2 * z 0 ^ 2 + y 1 ^ 2 * z 1 ^ 2 + y 2 ^ 2 * z 2 ^ 2) -
  40 * (y 0 ^ 2 * z 1 ^ 2 + y 0 ^ 2 * z 2 ^ 2 + y 1 ^ 2 * z 0 ^ 2 +
        y 1 ^ 2 * z 2 ^ 2 + y 2 ^ 2 * z 0 ^ 2 + y 2 ^ 2 * z 1 ^ 2) -
  160 * (y 0 * y 1 * z 0 * z 1 + y 1 * y 2 * z 1 * z 2 + y 2 * y 0 * z 2 * z 0)

def P4 (x y z : V3) : ℂ :=
  -120 * dot3 y (D3 x) - 120 * dot3 x (D3 z) + R4 y z

theorem sum_c4_a0 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 0 0 * R b 1 * R c 2 * R d 3 * (c4 0 b.val c.val d.val : ℂ)) =
    (120 : ℂ) * (R 0 0 * R 0 1 * R 0 2 * R 0 3) +
    (-30 : ℂ) * (R 0 0 * R 0 1 * R 2 2 * R 3 3) +
    (-30 : ℂ) * (R 0 0 * R 0 1 * R 3 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 2 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 1 1 * R 3 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 2 1 * R 0 2 * R 3 3) +
    (20 : ℂ) * (R 0 0 * R 2 1 * R 1 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 2 1 * R 2 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 2 1 * R 3 2 * R 0 3) +
    (-30 : ℂ) * (R 0 0 * R 3 1 * R 0 2 * R 2 3) +
    (20 : ℂ) * (R 0 0 * R 3 1 * R 1 2 * R 1 3) +
    (-30 : ℂ) * (R 0 0 * R 3 1 * R 2 2 * R 0 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a1 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 1 0 * R b 1 * R c 2 * R d 3 * (c4 1 b.val c.val d.val : ℂ)) =
    (20 : ℂ) * (R 1 0 * R 0 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 1 0 * R 0 1 * R 2 2 * R 2 3) +
    (20 : ℂ) * (R 1 0 * R 0 1 * R 3 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 1 1 * R 0 2 * R 3 3) +
    (-30 : ℂ) * (R 1 0 * R 1 1 * R 1 2 * R 2 3) +
    (-30 : ℂ) * (R 1 0 * R 1 1 * R 2 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 1 1 * R 3 2 * R 0 3) +
    (20 : ℂ) * (R 1 0 * R 2 1 * R 0 2 * R 2 3) +
    (-30 : ℂ) * (R 1 0 * R 2 1 * R 1 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 2 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 1 0 * R 3 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 1 0 * R 3 1 * R 1 2 * R 0 3) +
    (-30 : ℂ) * (R 1 0 * R 3 1 * R 3 2 * R 3 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a2 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 2 0 * R b 1 * R c 2 * R d 3 * (c4 2 b.val c.val d.val : ℂ)) =
    (-30 : ℂ) * (R 2 0 * R 0 1 * R 0 2 * R 3 3) +
    (20 : ℂ) * (R 2 0 * R 0 1 * R 1 2 * R 2 3) +
    (20 : ℂ) * (R 2 0 * R 0 1 * R 2 2 * R 1 3) +
    (-30 : ℂ) * (R 2 0 * R 0 1 * R 3 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 1 1 * R 0 2 * R 2 3) +
    (-30 : ℂ) * (R 2 0 * R 1 1 * R 1 2 * R 1 3) +
    (20 : ℂ) * (R 2 0 * R 1 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 1 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 2 1 * R 3 2 * R 3 3) +
    (-30 : ℂ) * (R 2 0 * R 3 1 * R 0 2 * R 0 3) +
    (20 : ℂ) * (R 2 0 * R 3 1 * R 2 2 * R 3 3) +
    (20 : ℂ) * (R 2 0 * R 3 1 * R 3 2 * R 2 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem sum_c4_a3 (R : Fin 4 → Fin 4 → ℂ) :
    (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      R 3 0 * R b 1 * R c 2 * R d 3 * (c4 3 b.val c.val d.val : ℂ)) =
    (-30 : ℂ) * (R 3 0 * R 0 1 * R 0 2 * R 2 3) +
    (20 : ℂ) * (R 3 0 * R 0 1 * R 1 2 * R 1 3) +
    (-30 : ℂ) * (R 3 0 * R 0 1 * R 2 2 * R 0 3) +
    (20 : ℂ) * (R 3 0 * R 1 1 * R 0 2 * R 1 3) +
    (20 : ℂ) * (R 3 0 * R 1 1 * R 1 2 * R 0 3) +
    (-30 : ℂ) * (R 3 0 * R 1 1 * R 3 2 * R 3 3) +
    (-30 : ℂ) * (R 3 0 * R 2 1 * R 0 2 * R 0 3) +
    (20 : ℂ) * (R 3 0 * R 2 1 * R 2 2 * R 3 3) +
    (20 : ℂ) * (R 3 0 * R 2 1 * R 3 2 * R 2 3) +
    (-30 : ℂ) * (R 3 0 * R 3 1 * R 1 2 * R 3 3) +
    (20 : ℂ) * (R 3 0 * R 3 1 * R 2 2 * R 2 3) +
    (-30 : ℂ) * (R 3 0 * R 3 1 * R 3 2 * R 1 3) := by
  simp only [Fin.sum_univ_four]
  norm_num [c4, c3, c2, c1]
  ring

theorem permSum_had {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (x y z : V3) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
      (1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
        had z i * ζ ^ (3 * (f i).val))) =
    120 + 120 * Q2 y z + 160 * Q3 x y z + P4 x y z := by
  let R : Fin 4 → Fin 4 → ℂ := ![fun _ => 1, had x, had y, had z]
  have hfactor : ∀ f : Fin 4 ↪ Fin 5,
      (∏ i : Fin 4, (1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
        had z i * ζ ^ (3 * (f i).val))) =
      ∑ g : Fin 4 → Fin 4,
        (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val) := by
    intro f
    have hrow : ∀ i : Fin 4,
        1 + had x i * ζ ^ (f i).val + had y i * ζ ^ (2 * (f i).val) +
          had z i * ζ ^ (3 * (f i).val) =
        ∑ k : Fin 4, R k i * ζ ^ (k.val * (f i).val) := by
      intro i
      rw [Fin.sum_univ_four]
      simp [R]
    simp_rw [hrow]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [pow_add, mul_assoc]
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  have hstep : ∀ g : Fin 4 → Fin 4,
      (∑ f : Fin 4 ↪ Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val)) =
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ) := by
    intro g
    rw [← Finset.mul_sum, sum_emb_eq_S4, S4_eq hζ, Fin.prod_univ_four]
  simp_rw [hstep]
  have hfun : (∑ g : Fin 4 → Fin 4,
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ)) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a 0 * R b 1 * R c 2 * R d 3 * (c4 a.val b.val c.val d.val : ℂ) := by
    let e : (Fin 4 → Fin 4) ≃ Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
      { toFun := fun g => (g 0, g 1, g 2, g 3)
        invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
        left_inv := fun g => by funext i; fin_cases i <;> rfl
        right_inv := fun ⟨a, b, c, d⟩ => rfl }
    have he := Fintype.sum_equiv e
      (fun g => R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ))
      (fun p => R p.1 0 * R p.2.1 1 * R p.2.2.1 2 * R p.2.2.2 3 *
        (c4 p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val : ℂ))
      (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using he
  rw [hfun, Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hval3 : (3 : Fin 4).val = 3 := rfl
  rw [hval3, sum_c4_a0, sum_c4_a1, sum_c4_a2, sum_c4_a3]
  have hdeg2 :
      (-30 : ℂ) * (R 0 0 * R 0 1 * R 2 2 * R 3 3) +
      (-30 : ℂ) * (R 0 0 * R 0 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 0 0 * R 2 1 * R 0 2 * R 3 3) +
      (-30 : ℂ) * (R 0 0 * R 2 1 * R 3 2 * R 0 3) +
      (-30 : ℂ) * (R 0 0 * R 3 1 * R 0 2 * R 2 3) +
      (-30 : ℂ) * (R 0 0 * R 3 1 * R 2 2 * R 0 3) +
      (-30 : ℂ) * (R 2 0 * R 0 1 * R 0 2 * R 3 3) +
      (-30 : ℂ) * (R 2 0 * R 0 1 * R 3 2 * R 0 3) +
      (-30 : ℂ) * (R 2 0 * R 3 1 * R 0 2 * R 0 3) +
      (-30 : ℂ) * (R 3 0 * R 0 1 * R 0 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 0 1 * R 2 2 * R 0 3) +
      (-30 : ℂ) * (R 3 0 * R 2 1 * R 0 2 * R 0 3) =
      120 * Q2 y z := by
    simp only [R, had, Q2, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg3 :
      (20 : ℂ) * (R 0 0 * R 1 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 0 0 * R 1 1 * R 2 2 * R 2 3) +
      (20 : ℂ) * (R 0 0 * R 1 1 * R 3 2 * R 1 3) +
      (20 : ℂ) * (R 0 0 * R 2 1 * R 1 2 * R 2 3) +
      (20 : ℂ) * (R 0 0 * R 2 1 * R 2 2 * R 1 3) +
      (20 : ℂ) * (R 0 0 * R 3 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 2 2 * R 2 3) +
      (20 : ℂ) * (R 1 0 * R 0 1 * R 3 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 1 1 * R 0 2 * R 3 3) +
      (20 : ℂ) * (R 1 0 * R 1 1 * R 3 2 * R 0 3) +
      (20 : ℂ) * (R 1 0 * R 2 1 * R 0 2 * R 2 3) +
      (20 : ℂ) * (R 1 0 * R 2 1 * R 2 2 * R 0 3) +
      (20 : ℂ) * (R 1 0 * R 3 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 1 0 * R 3 1 * R 1 2 * R 0 3) +
      (20 : ℂ) * (R 2 0 * R 0 1 * R 1 2 * R 2 3) +
      (20 : ℂ) * (R 2 0 * R 0 1 * R 2 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 1 1 * R 0 2 * R 2 3) +
      (20 : ℂ) * (R 2 0 * R 1 1 * R 2 2 * R 0 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 1 2 * R 0 3) +
      (20 : ℂ) * (R 3 0 * R 0 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 3 0 * R 1 1 * R 0 2 * R 1 3) +
      (20 : ℂ) * (R 3 0 * R 1 1 * R 1 2 * R 0 3) =
      160 * Q3 x y z := by
    simp only [R, had, Q3, C3, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg4 :
      (-30 : ℂ) * (R 1 0 * R 1 1 * R 1 2 * R 2 3) +
      (-30 : ℂ) * (R 1 0 * R 1 1 * R 2 2 * R 1 3) +
      (-30 : ℂ) * (R 1 0 * R 2 1 * R 1 2 * R 1 3) +
      (-30 : ℂ) * (R 1 0 * R 3 1 * R 3 2 * R 3 3) +
      (-30 : ℂ) * (R 2 0 * R 1 1 * R 1 2 * R 1 3) +
      (20 : ℂ) * (R 2 0 * R 2 1 * R 3 2 * R 3 3) +
      (20 : ℂ) * (R 2 0 * R 3 1 * R 2 2 * R 3 3) +
      (20 : ℂ) * (R 2 0 * R 3 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 1 1 * R 3 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 2 1 * R 2 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 2 1 * R 3 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 3 1 * R 1 2 * R 3 3) +
      (20 : ℂ) * (R 3 0 * R 3 1 * R 2 2 * R 2 3) +
      (-30 : ℂ) * (R 3 0 * R 3 1 * R 3 2 * R 1 3) =
      P4 x y z := by
    simp only [R, had, P4, R4, D3, dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hdeg0 : (120 : ℂ) * (R 0 0 * R 0 1 * R 0 2 * R 0 3) = 120 := by
    simp [R]
  linear_combination hdeg0 + hdeg2 + hdeg3 + hdeg4

theorem extract_homog {x y z : V3}
    (h : ∀ t : ℂ, 120 * Q2 (t • y) (t • z) + 160 * Q3 (t • x) (t • y) (t • z) +
      P4 (t • x) (t • y) (t • z) = 0) :
    Q2 y z = 0 ∧ Q3 x y z = 0 ∧ P4 x y z = 0 := by
  have hscale : ∀ t : ℂ,
      t ^ 2 * (120 * Q2 y z) + t ^ 3 * (160 * Q3 x y z) + t ^ 4 * P4 x y z = 0 := by
    intro t
    have ht := h t
    have h2 : Q2 (t • y) (t • z) = t ^ 2 * Q2 y z := by
      simp only [Q2, dot3, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : Q3 (t • x) (t • y) (t • z) = t ^ 3 * Q3 x y z := by
      simp only [Q3, C3, dot3, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]; ring
    have h4 : P4 (t • x) (t • y) (t • z) = t ^ 4 * P4 x y z := by
      simp only [P4, R4, D3, dot3, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]; ring
    rw [h2, h3, h4] at ht
    linear_combination ht
  have h1 := hscale 1
  have hm1 := hscale (-1)
  have h2 := hscale 2
  have hQ3 : Q3 x y z = 0 := by linear_combination (h1 - hm1) / 320
  have hQ2 : Q2 y z = 0 := by linear_combination (16 * h1 - h2 - 1280 * hQ3) / 1440
  have hP4 : P4 x y z = 0 := by linear_combination h1 - 120 * hQ2 - 160 * hQ3
  exact ⟨hQ2, hQ3, hP4⟩

theorem extract_zC {x y z u : V3}
    (h : ∀ h : ℂ, Q3 (x + h • u) y z = 0) : dot3 z (C3 u) = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  simp only [Q3, C3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 hm1 ⊢
  linear_combination (h1 + hm1 - 2 * h0) / 2

theorem extract_yD {x y z u : V3}
    (h : ∀ h : ℂ, P4 (x + h • u) y z = 0) : dot3 y (D3 u) = 0 := by
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [P4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h2 hm2 ⊢
  linear_combination -(h2 - hm2 - 2 * h1 + 2 * hm1) / 1440

def swapBilin : (V3 × V3) ≃ₗ[ℂ] Module.Dual ℂ (V3 × V3) where
  toFun p :=
    { toFun := fun q => dot3 p.1 q.2 + dot3 q.1 p.2
      map_add' := fun q1 q2 => by simp only [dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c q => by simp only [dot3, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' p1 p2 := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, dot3, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun f :=
    (fun i => f (0, Pi.single i 1), fun i => f (Pi.single i 1, 0))
  left_inv p := by
    ext i <;> fin_cases i <;> simp [dot3]
  right_inv f := by
    apply LinearMap.ext
    rintro ⟨y, z⟩
    have hdecomp : (y, z) =
        y 0 • (Pi.single 0 1, 0) + y 1 • (Pi.single 1 1, 0) + y 2 • (Pi.single 2 1, 0) +
        z 0 • (0, Pi.single 0 1) + z 1 • (0, Pi.single 1 1) + z 2 • (0, Pi.single 2 1) := by
      ext i <;> fin_cases i <;> simp
    conv_rhs => rw [hdecomp]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dot3, map_add, map_smul, smul_eq_mul]
    ring

theorem isotropic_finrank_le_three (W : Submodule ℂ (V3 × V3))
    (hiso : ∀ p ∈ W, dot3 p.1 p.2 = 0) : Module.finrank ℂ W ≤ 3 := by
  have hle : W.map swapBilin.toLinearMap ≤ W.dualAnnihilator := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro q hq
    have hpq : p + q ∈ W := W.add_mem hp hq
    have h1 := hiso p hp
    have h2 := hiso q hq
    have h3 := hiso (p + q) hpq
    simp only [swapBilin, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [dot3, Prod.fst_add, Prod.snd_add, Pi.add_apply] at h1 h2 h3 ⊢
    linear_combination h3 - h1 - h2
  have h1 : Module.finrank ℂ (W.map swapBilin.toLinearMap) = Module.finrank ℂ W :=
    LinearEquiv.finrank_map_eq swapBilin W
  have h2 : Module.finrank ℂ (W.map swapBilin.toLinearMap) ≤ Module.finrank ℂ W.dualAnnihilator :=
    Submodule.finrank_mono hle
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdim : Module.finrank ℂ (V3 × V3) = 6 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega

def permV3 (σ : Equiv.Perm (Fin 3)) : V3 ≃ₗ[ℂ] V3 where
  toFun u := u ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u ∘ σ.symm
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp

def permTriple (σ : Equiv.Perm (Fin 3)) : Triple ≃ₗ[ℂ] Triple :=
  (permV3 σ).prodCongr ((permV3 σ).prodCongr (permV3 σ))

theorem perm_Q2 (i j : Fin 3) (y z : V3) :
    Q2 (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = Q2 y z := by
  fin_cases i <;> fin_cases j <;>
    simp [Q2, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

theorem perm_Q3 (i j : Fin 3) (x y z : V3) :
    Q3 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = Q3 x y z := by
  fin_cases i <;> fin_cases j <;>
    simp [Q3, C3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

theorem perm_P4 (i j : Fin 3) (x y z : V3) :
    P4 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y) (permV3 (Equiv.swap i j) z) = P4 x y z := by
  fin_cases i <;> fin_cases j <;>
    simp [P4, R4, D3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

def projYZ : Triple →ₗ[ℂ] V3 × V3 := LinearMap.snd ℂ V3 (V3 × V3)
def projX : Triple →ₗ[ℂ] V3 := LinearMap.fst ℂ V3 (V3 × V3)

def ValidSubspace (M : Submodule ℂ Triple) : Prop :=
  ∀ p ∈ M, Q2 p.2.1 p.2.2 = 0 ∧ Q3 p.1 p.2.1 p.2.2 = 0 ∧ P4 p.1 p.2.1 p.2.2 = 0

theorem valid_swap {M : Submodule ℂ Triple} (hM : ValidSubspace M) (i j : Fin 3) :
    ValidSubspace (M.map (permTriple (Equiv.swap i j)).toLinearMap) := by
  rintro _ ⟨⟨x, y, z⟩, hp, rfl⟩
  obtain ⟨h2, h3, h4⟩ := hM ⟨x, y, z⟩ hp
  refine ⟨?_, ?_, ?_⟩
  · exact (perm_Q2 i j y z).trans h2
  · exact (perm_Q3 i j x y z).trans h3
  · exact (perm_P4 i j x y z).trans h4

theorem pureX_mem_M {M : Submodule ℂ Triple} {u : V3}
    (hu : u ∈ (LinearMap.ker (projYZ.domRestrict M)).map (projX.comp M.subtype)) :
    (u, 0, 0) ∈ M := by
  rcases hu with ⟨⟨⟨x, y, z⟩, hmem⟩, hker, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker
  have hy : y = 0 := congrArg Prod.fst hker
  have hz : z = 0 := congrArg Prod.snd hker
  subst hy; subst hz
  exact hmem

theorem kernel_laws {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    {x y z u : V3} (hp : (x, y, z) ∈ M) (hu : (u, 0, 0) ∈ M) :
    dot3 z (C3 u) = 0 ∧ dot3 y (D3 u) = 0 := by
  have htr : ∀ h : ℂ, (x + h • u, y, z) ∈ M := by
    intro h
    have h1 := M.add_mem hp (M.smul_mem h hu)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using h1
  exact ⟨extract_zC (fun h => (hM _ (htr h)).2.1), extract_yD (fun h => (hM _ (htr h)).2.2)⟩

theorem case_all_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 ≠ 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  have hz_zero : ∀ p ∈ M, p.2.2 = 0 := by
    intro ⟨x, y, z⟩ hp
    let p0 : ℂ := -α 0 / α 2
    let q0 : ℂ := -α 1 / α 2
    have hp0 : p0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
    have hq0 : q0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
    have hu1 : (![1, 0, p0], 0, 0) ∈ M := hU ![1, 0, p0] (by
      simp only [dot3, p0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have hu2 : (![0, 1, q0], 0, 0) ∈ M := hU ![0, 1, q0] (by
      simp only [dot3, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have hu3 : (![1, 1, p0 + q0], 0, 0) ∈ M := hU ![1, 1, p0 + q0] (by
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring)
    have h1 := (kernel_laws hM hp hu1).1
    have h2 := (kernel_laws hM hp hu2).1
    have h3 := (kernel_laws hM hp hu3).1
    simp only [dot3, C3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2 h3
    have hz1 : z 1 = 0 := by
      have : p0 * z 1 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left hp0
    have hz0 : z 0 = 0 := by
      have : q0 * z 0 = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_left hq0
    have hz2 : z 2 = 0 := by linear_combination h3 - (p0 + q0) * hz0 - (p0 + q0) * hz1
    funext i
    fin_cases i <;> assumption
  let S : Submodule ℂ (V3 × V3) := LinearMap.range (LinearMap.inl ℂ V3 V3)
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ S := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hz : z = 0 := hz_zero ⟨x, y, z⟩ hp
    refine ⟨y, ?_⟩
    simp [projYZ, hz]
  have hfinS : Module.finrank ℂ S = 3 := by
    rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  have heqS : LinearMap.range (projYZ.domRestrict M) = S :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hD_zero : ∀ u : V3, dot3 α u = 0 → D3 u = 0 := by
    intro u hu
    have huM : (u, 0, 0) ∈ M := hU u hu
    have hall_y : ∀ y : V3, dot3 y (D3 u) = 0 := by
      intro y
      have hyS : (y, (0 : V3)) ∈ S := ⟨y, rfl⟩
      rw [← heqS] at hyS
      rcases hyS with ⟨⟨⟨x, y', z'⟩, hp⟩, hpyz⟩
      have hy_eq : y' = y := congrArg Prod.fst hpyz
      subst hy_eq
      exact (kernel_laws hM hp huM).2
    funext i
    have hi := hall_y (Pi.single i 1)
    fin_cases i <;> simp [dot3, Fin.ext_iff] at hi ⊢ <;> exact hi
  let p0 : ℂ := -α 0 / α 2
  let q0 : ℂ := -α 1 / α 2
  have hp0 : p0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
  have hq0 : q0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hex_u : ∃ u : V3, dot3 α u = 0 ∧ u 0 ≠ 0 ∧ u 1 ≠ 0 ∧ u 2 ≠ 0 := by
    by_cases hpq : p0 + q0 ≠ 0
    · refine ⟨![1, 1, p0 + q0], ?_, by norm_num, by norm_num, hpq⟩
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring
    · push Not at hpq
      have hp2q : p0 + 2 * q0 ≠ 0 := by
        intro h0
        apply hq0
        linear_combination h0 - hpq
      refine ⟨![1, 2, p0 + 2 * q0], ?_, by norm_num, by norm_num, hp2q⟩
      simp only [dot3, p0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hα2]; ring
  obtain ⟨u, hu, hu0, hu1, hu2⟩ := hex_u
  have hDu := hD_zero u hu
  have hD0 : u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2) = 0 := congrFun hDu 0
  have hD1 : u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2) = 0 := congrFun hDu 1
  have hf0 : u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2 = 0 := (mul_eq_zero.mp hD0).resolve_left hu0
  have hf1 : u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2 = 0 := (mul_eq_zero.mp hD1).resolve_left hu1
  have hu2_sq : u 2 ^ 2 = 0 := by linear_combination -(hf0 + hf1) / 2
  exact hu2 (sq_eq_zero_iff.mp hu2_sq)

theorem case_two_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 = 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  let s : ℂ := -α 1 / α 2
  have hs : s ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hmem : ∀ a b : ℂ, (![a, b, s * b], 0, 0) ∈ M := fun a b => hU ![a, b, s * b] (by
    simp only [dot3, hα0, s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring)
  let Ψ : (Fin 2 → ℂ) →ₗ[ℂ] V3 × V3 :=
    { toFun := fun t => (![0, -s * t 0, t 0], ![0, t 1, -s * t 1])
      map_add' := fun t1 t2 => by ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := fun c t => by ext i <;> fin_cases i <;> simp <;> ring }
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ LinearMap.range Ψ := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hc1 := (kernel_laws hM hp (hmem 0 1)).1
    have hc2 := (kernel_laws hM hp (hmem 1 1)).1
    have hd0 := (kernel_laws hM hp (hmem 1 0)).2
    have hd1 := (kernel_laws hM hp (hmem 0 1)).2
    have hd2 := (kernel_laws hM hp (hmem 1 1)).2
    simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc1 hc2 hd0 hd1 hd2
    have hz0 : z 0 = 0 := (mul_eq_zero.mp (by linear_combination hc1 : s * z 0 = 0)).resolve_left hs
    have hz2 : z 2 = -s * z 1 := by linear_combination hc2 - s * hz0
    have hy0 : y 0 = 0 := by linear_combination hd0
    have hy1 : y 1 = -s * y 2 := by linear_combination -(hd2 - hd1) - s ^ 2 * hy0
    refine ⟨![y 2, z 1], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ, projYZ, hy0, hy1, hz0, hz2]
  have hle_rank : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) ≤ Module.finrank ℂ (LinearMap.range Ψ) :=
    Submodule.finrank_mono hle
  have hrank_Psi : Module.finrank ℂ (LinearMap.range Ψ) ≤ 2 := by
    have h1 := LinearMap.finrank_range_le Ψ
    rw [Module.finrank_fin_fun] at h1
    exact h1
  omega

theorem case_one_nonzero {M : Submodule ℂ Triple} (hM : ValidSubspace M)
    (hW : Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M)) = 3)
    (α : V3) (hα0 : α 0 = 0) (hα1 : α 1 = 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M) : False := by
  have hmem : ∀ a b : ℂ, (![a, b, 0], 0, 0) ∈ M := fun a b => hU ![a, b, 0] (by
    simp [dot3, hα0, hα1])
  let Ψ : (Fin 3 → ℂ) →ₗ[ℂ] V3 × V3 :=
    { toFun := fun t => (![0, 0, t 2], ![t 0, t 1, 0])
      map_add' := fun t1 t2 => by ext i <;> fin_cases i <;> simp
      map_smul' := fun c t => by ext i <;> fin_cases i <;> simp }
  have hle : LinearMap.range (projYZ.domRestrict M) ≤ LinearMap.range Ψ := by
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    have hc := (kernel_laws hM hp (hmem 1 1)).1
    have hd0 := (kernel_laws hM hp (hmem 1 0)).2
    have hd1 := (kernel_laws hM hp (hmem 0 1)).2
    simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc hd0 hd1
    have hz2 : z 2 = 0 := by linear_combination hc
    have hy0 : y 0 = 0 := by linear_combination hd0
    have hy1 : y 1 = 0 := by linear_combination hd1
    refine ⟨![z 0, z 1, y 2], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ, projYZ, hy0, hy1, hz2]
  have hrank_Psi : Module.finrank ℂ (LinearMap.range Ψ) = 3 := by
    have h1 := LinearMap.finrank_range_le Ψ
    rw [Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_mono hle
    omega
  have heq : LinearMap.range (projYZ.domRestrict M) = LinearMap.range Ψ :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have he0 : ((0 : V3), (![1, 0, 0] : V3)) ∈ LinearMap.range (projYZ.domRestrict M) := by
    rw [heq]
    refine ⟨![1, 0, 0], ?_⟩
    ext i <;> fin_cases i <;> simp [Ψ]
  rcases he0 with ⟨⟨⟨x, y, z⟩, hp⟩, hpyz⟩
  have hy : y = 0 := congrArg Prod.fst hpyz
  have hz : z = ![1, 0, 0] := congrArg Prod.snd hpyz
  subst hy; subst hz
  have hw : ((![0, 0, x 2] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hsub := M.sub_mem hp (hmem (x 0) (x 1))
    convert hsub using 1
    ext i
    · fin_cases i
      · change (0 : ℂ) = x 0 - x 0; ring
      · change (0 : ℂ) = x 1 - x 1; ring
      · change x 2 = x 2 - 0; ring
    · simp
    · simp
  have hw' : ((![0, 1, x 2] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hadd := M.add_mem hw (hmem 0 1)
    convert hadd using 1
    ext i <;> fin_cases i <;> simp
  have hx2 : x 2 = 0 := by
    have hq3 := (hM _ hw').2.1
    simp only [Q3, C3, dot3, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hq3
    linear_combination hq3
  have hv : ((![1, 0, 0] : V3), (0 : V3), (![1, 0, 0] : V3)) ∈ M := by
    have hadd := M.add_mem hw (hmem 1 0)
    convert hadd using 1
    ext i <;> fin_cases i <;> simp [hx2]
  have hp4 := (hM _ hv).2.2
  simp only [P4, R4, D3, dot3, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp4
  norm_num at hp4

theorem valid_finrank_le_four (M : Submodule ℂ Triple) (hM : ValidSubspace M) :
    Module.finrank ℂ M ≤ 4 := by
  by_contra hgt
  have h5 : 5 ≤ Module.finrank ℂ M := by omega
  let π : M →ₗ[ℂ] V3 × V3 := projYZ.domRestrict M
  have hW_le : Module.finrank ℂ (LinearMap.range π) ≤ 3 := by
    apply isotropic_finrank_le_three
    rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
    exact (hM ⟨x, y, z⟩ hp).1
  have hrn : Module.finrank ℂ (LinearMap.range π) + Module.finrank ℂ (LinearMap.ker π) =
      Module.finrank ℂ M := LinearMap.finrank_range_add_finrank_ker π
  let U : Submodule ℂ V3 := (LinearMap.ker π).map (projX.comp M.subtype)
  have hker_inj : Set.InjOn (projX.comp M.subtype) (LinearMap.ker π) := by
    rintro ⟨⟨x1, y1, z1⟩, h1⟩ hk1 ⟨⟨x2, y2, z2⟩, h2⟩ hk2 heq
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hk1 hk2
    have hy1 : y1 = 0 := congrArg Prod.fst hk1
    have hz1 : z1 = 0 := congrArg Prod.snd hk1
    have hy2 : y2 = 0 := congrArg Prod.fst hk2
    have hz2 : z2 = 0 := congrArg Prod.snd hk2
    have hx : x1 = x2 := heq
    subst hx hy1 hz1 hy2 hz2
    rfl
  have hU_finrank : Module.finrank ℂ U = Module.finrank ℂ (LinearMap.ker π) := by
    have hinj : Function.Injective ((projX.comp M.subtype).domRestrict (LinearMap.ker π)) := by
      rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
      exact Subtype.ext (hker_inj hv1 hv2 heq)
    have h1 := LinearMap.finrank_range_of_inj hinj
    have hrange : LinearMap.range ((projX.comp M.subtype).domRestrict (LinearMap.ker π)) = U := by
      ext u
      simp [U]
    rw [hrange] at h1
    exact h1
  have hU_le3 : Module.finrank ℂ U ≤ 3 := by
    have := Submodule.finrank_le U
    rwa [Module.finrank_fin_fun] at this
  have hU_ge2 : 2 ≤ Module.finrank ℂ U := by omega
  by_cases hU3 : Module.finrank ℂ U = 3
  · have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hU3)
    have hallU : ∀ u : V3, (u, 0, 0) ∈ M := fun u => pureX_mem_M (by change u ∈ U; rw [hUtop]; trivial)
    have hWbot : LinearMap.range π = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩
      have hz0 : z 0 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 1, 1])).1
        simp [dot3, C3] at h; exact h
      have hz1 : z 1 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 0, 1])).1
        simp [dot3, C3] at h; exact h
      have hz2 : z 2 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 1, 0])).1
        simp [dot3, C3] at h; exact h
      have hy0 : y 0 = 0 := by
        have h := (kernel_laws hM hp (hallU ![1, 0, 0])).2
        simp [dot3, D3] at h; exact h
      have hy1 : y 1 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 1, 0])).2
        simp [dot3, D3] at h; exact h
      have hy2 : y 2 = 0 := by
        have h := (kernel_laws hM hp (hallU ![0, 0, 1])).2
        simp [dot3, D3] at h; exact h
      ext i <;> fin_cases i <;> simp [π, projYZ, hy0, hy1, hy2, hz0, hz1, hz2]
    have hW0 : Module.finrank ℂ (LinearMap.range π) = 0 := by rw [hWbot, finrank_bot]
    omega
  · have hU2 : Module.finrank ℂ U = 2 := by omega
    have hW3 : Module.finrank ℂ (LinearMap.range π) = 3 := by omega
    have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    rw [Module.finrank_fin_fun] at hann
    have hann1 : Module.finrank ℂ U.dualAnnihilator = 1 := by omega
    have hne_bot : U.dualAnnihilator ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hann1
      omega
    obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    let α : V3 := fun i => f (Pi.single i 1)
    have hf_eq : ∀ u : V3, f u = dot3 α u := by
      intro u
      have hu : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
        ext i; fin_cases i <;> simp
      conv_lhs => rw [hu]
      simp only [map_add, map_smul, smul_eq_mul, dot3, α]
      ring
    have hα_ne : α ≠ 0 := by
      intro h0
      apply hf_ne
      apply LinearMap.ext
      intro u
      rw [hf_eq, h0]
      simp [dot3]
    have hU_eq_ker : U = LinearMap.ker f := by
      have hle : U ≤ LinearMap.ker f := by
        intro u hu
        rw [Submodule.mem_dualAnnihilator] at hf_mem
        exact hf_mem u hu
      have hfr := LinearMap.finrank_range_add_finrank_ker f
      rw [Module.finrank_fin_fun] at hfr
      have hex_ne : ∃ u0 : V3, f u0 ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hf_ne (LinearMap.ext hall)
      obtain ⟨u0, hu0⟩ := hex_ne
      have hrange_top : LinearMap.range f = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / f u0) • u0, ?_⟩
        rw [map_smul, smul_eq_mul]
        exact div_mul_cancel₀ c hu0
      have hrange1 : Module.finrank ℂ (LinearMap.range f) = 1 := by
        rw [hrange_top, finrank_top, Module.finrank_self]
      exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hU_char : ∀ u : V3, dot3 α u = 0 → (u, 0, 0) ∈ M := by
      intro u hu
      apply pureX_mem_M
      change u ∈ U
      rw [hU_eq_ker, LinearMap.mem_ker, hf_eq]
      exact hu
    have hswap_red : ∀ i j : Fin 3,
        let M' := M.map (permTriple (Equiv.swap i j)).toLinearMap
        ValidSubspace M' ∧
        Module.finrank ℂ (LinearMap.range (projYZ.domRestrict M')) = 3 ∧
        ∀ u : V3, dot3 (permV3 (Equiv.swap i j) α) u = 0 → (u, 0, 0) ∈ M' := by
      intro i j
      let σ := Equiv.swap i j
      let M' := M.map (permTriple σ).toLinearMap
      refine ⟨valid_swap hM i j, ?_, ?_⟩
      · have hrange : LinearMap.range (projYZ.domRestrict M') =
            (LinearMap.range π).map ((permV3 σ).prodCongr (permV3 σ)).toLinearMap := by
          ext ⟨y', z'⟩
          constructor
          · rintro ⟨⟨⟨x', y1, z1⟩, ⟨⟨x, y, z⟩, hp, hmap⟩⟩, hproj⟩
            have hy1 : y1 = y' := congrArg Prod.fst hproj
            have hz1 : z1 = z' := congrArg Prod.snd hproj
            have hy2 : permV3 σ y = y1 := congrArg (fun p : Triple => p.2.1) hmap
            have hz2 : permV3 σ z = z1 := congrArg (fun p : Triple => p.2.2) hmap
            refine ⟨(y, z), ⟨⟨⟨x, y, z⟩, hp⟩, rfl⟩, ?_⟩
            exact Prod.ext (hy2.trans hy1) (hz2.trans hz1)
          · rintro ⟨⟨y, z⟩, ⟨⟨⟨x, y1, z1⟩, hp⟩, hproj⟩, hmap⟩
            have hy1 : y1 = y := congrArg Prod.fst hproj
            have hz1 : z1 = z := congrArg Prod.snd hproj
            refine ⟨⟨permTriple σ (x, y1, z1), ⟨(x, y1, z1), hp, rfl⟩⟩, ?_⟩
            change (permV3 σ y1, permV3 σ z1) = (y', z')
            rw [hy1, hz1]
            exact hmap
        rw [hrange, LinearEquiv.finrank_map_eq]
        exact hW3
      · intro u hu
        have hu' : dot3 α (permV3 σ u) = 0 := by
          have h1 := perm_Q2 i j (permV3 σ α) u
          simp only [Q2, permV3, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at h1 hu ⊢
          have h2 : (α ∘ σ) ∘ σ = α := by funext k; simp [σ]
          rw [h2] at h1
          exact h1.trans hu
        refine ⟨(permV3 σ u, 0, 0), hU_char (permV3 σ u) hu', ?_⟩
        ext k <;> simp [permTriple, permV3, σ]
    by_cases h0 : α 0 = 0
    · by_cases h1 : α 1 = 0
      · have h2 : α 2 ≠ 0 := by
          intro h2; apply hα_ne; funext k; fin_cases k <;> assumption
        exact case_one_nonzero hM hW3 α h0 h1 h2 hU_char
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 1 2
          exact case_one_nonzero hM' hW' (permV3 (Equiv.swap 1 2) α)
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h0])
            (by simp [permV3, h2])
            (by simp [permV3, h1]) hU'
        · exact case_two_nonzero hM hW3 α h0 h1 h2 hU_char
    · by_cases h1 : α 1 = 0
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 2
          exact case_one_nonzero hM' hW' (permV3 (Equiv.swap 0 2) α)
            (by simp [permV3, h2])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h1])
            (by simp [permV3, h0]) hU'
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 1
          exact case_two_nonzero hM' hW' (permV3 (Equiv.swap 0 1) α)
            (by simp [permV3, h1])
            (by simp [permV3, h0])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h2]) hU'
      · by_cases h2 : α 2 = 0
        · obtain ⟨hM', hW', hU'⟩ := hswap_red 0 2
          exact case_two_nonzero hM' hW' (permV3 (Equiv.swap 0 2) α)
            (by simp [permV3, h2])
            (by simp [permV3, Equiv.swap_apply_def, Fin.ext_iff, h1])
            (by simp [permV3, h0]) hU'
        · exact case_all_nonzero hM hW3 α h0 h1 h2 hU_char

end

theorem main : (∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
  ∀ L : Submodule ℂ (Fin 3 → Fin 4 → ℂ),
    (∀ x ∈ L, (∀ r : Fin 3, (∑ i, x r i) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + x 0 i * ζ ^ (f i).val + x 1 i * ζ ^ (2 * (f i).val) +
          x 2 i * ζ ^ (3 * (f i).val))) = 120) →
      Module.finrank ℂ L ≤ 4) := by
  intro ζ hζ L hL
  let M : Submodule ℂ Triple :=
    L.map toTriple
  have hfin : Module.finrank ℂ M = Module.finrank ℂ L := by
    have hker : LinearMap.ker (toTriple.domRestrict L) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro ⟨X, hX⟩ h0
      rw [LinearMap.mem_ker] at h0
      have hzero : toTriple X =
          toTriple 0 := by
        simpa using h0
      have hX0 := toTriple_inj_on_zeroSum
        (hL X hX).1 (fun _ => by simp) hzero
      exact Subtype.ext hX0
    have h1 := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
    have hrange : LinearMap.range (toTriple.domRestrict L) = M := by
      ext p
      simp [M]
    rw [hrange] at h1
    exact h1
  have hvalid : ValidSubspace M := by
    rintro _ ⟨X, hX, rfl⟩
    apply extract_homog
    intro t
    have htX : t • X ∈ L := L.smul_mem t hX
    obtain ⟨hsum, hperm⟩ := hL (t • X) htX
    have hhad : ∀ r : Fin 3,
        had (t • invHad (X r)) = (t • X) r := by
      intro r
      have hlin : t • invHad (X r) =
          invHad ((t • X) r) := by
        ext i; fin_cases i <;> simp [invHad] <;> ring
      rw [hlin, had_invHad _ (hsum r)]
    have heval := permSum_had hζ
      (t • invHad (X 0))
      (t • invHad (X 1))
      (t • invHad (X 2))
    rw [hhad 0, hhad 1, hhad 2, hperm] at heval
    dsimp only [toTriple]
    linear_combination -heval
  rw [← hfin]
  exact valid_finrank_le_four M hvalid
end G280

namespace G284

noncomputable section Proof

private abbrev V3 := Fin 3 → ℂ

private def had (u : V3) : Fin 4 → ℂ :=
  ![u 0 + u 1 + u 2, u 0 - u 1 - u 2, -u 0 + u 1 - u 2, -u 0 - u 1 + u 2]

private def invHad (v : Fin 4 → ℂ) : V3 :=
  ![(v 0 + v 1) / 2, (v 0 + v 2) / 2, (v 0 + v 3) / 2]

private theorem had_invHad (v : Fin 4 → ℂ) (hv : (∑ i : Fin 4, v i) = 0) :
    had (invHad v) = v := by
  rw [Fin.sum_univ_four] at hv
  funext i
  fin_cases i
  · change (v 0 + v 1) / 2 + (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 0
    linear_combination hv / 2
  · change (v 0 + v 1) / 2 - (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 1
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) + (v 0 + v 2) / 2 - (v 0 + v 3) / 2 = v 2
    linear_combination -hv / 2
  · change -((v 0 + v 1) / 2) - (v 0 + v 2) / 2 + (v 0 + v 3) / 2 = v 3
    linear_combination -hv / 2

private def dot3 (u v : V3) : ℂ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private def C3 (u : V3) : V3 := ![u 1 * u 2, u 2 * u 0, u 0 * u 1]

private def D3 (u : V3) : V3 :=
  ![u 0 * (u 0 ^ 2 - u 1 ^ 2 - u 2 ^ 2),
    u 1 * (u 1 ^ 2 - u 0 ^ 2 - u 2 ^ 2),
    u 2 * (u 2 ^ 2 - u 0 ^ 2 - u 1 ^ 2)]

private def R4 (y z : V3) : ℂ :=
  120 * (y 0 ^ 2 * z 0 ^ 2 + y 1 ^ 2 * z 1 ^ 2 + y 2 ^ 2 * z 2 ^ 2) -
  40 * (y 0 ^ 2 * z 1 ^ 2 + y 0 ^ 2 * z 2 ^ 2 + y 1 ^ 2 * z 0 ^ 2 +
        y 1 ^ 2 * z 2 ^ 2 + y 2 ^ 2 * z 0 ^ 2 + y 2 ^ 2 * z 1 ^ 2) -
  160 * (y 0 * y 1 * z 0 * z 1 + y 1 * y 2 * z 1 * z 2 + y 2 * y 0 * z 2 * z 0)

private def c1 (a : ℕ) : ℤ := if a % 5 = 0 then 5 else 0
private def c2 (a b : ℕ) : ℤ := c1 a * c1 b - c1 (a + b)
private def c3 (a b c : ℕ) : ℤ := c2 a b * c1 c - c2 (a + c) b - c2 a (b + c)
private def c4 (a b c d : ℕ) : ℤ := c3 a b c * c1 d - c3 (a + d) b c - c3 a (b + d) c - c3 a b (c + d)

private def S1 (ζ : ℂ) (a : ℕ) : ℂ := ∑ x0 : Fin 5, ζ ^ (a * x0.val)

private def S2 (ζ : ℂ) (a b : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)

private def S3 (ζ : ℂ) (a b c : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ζ ^ (a * x0.val + b * x1.val + c * x2.val)

private def S4 (ζ : ℂ) (a b c d : ℕ) : ℂ :=
  ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
    ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
      ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)

private theorem S1_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) : S1 ζ a = (c1 a : ℂ) := by
  unfold S1 c1
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  by_cases hmod : a % 5 = 0
  · simp only [hmod, ↓reduceIte, Int.cast_ofNat]
    have hdvd : 5 ∣ a := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, rfl⟩ := hdvd
    have hterm : ∀ x : Fin 5, ζ ^ (5 * q * x.val) = 1 := by
      intro x
      rw [show 5 * q * x.val = 5 * (q * x.val) by ring, pow_mul, h5, one_pow]
    simp [hterm]
  · simp only [hmod, ↓reduceIte, Int.cast_zero]
    have hne : ζ ^ a ≠ 1 := by
      intro h1
      have hdvd : 5 ∣ a := hζ.pow_eq_one_iff_dvd a |>.mp h1
      exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
    have hmul : (ζ ^ a - 1) * (∑ x0 : Fin 5, ζ ^ (a * x0.val)) = 0 := by
      rw [Fin.sum_univ_five]
      have hpow : ∀ k : ℕ, ζ ^ (a * k) = (ζ ^ a) ^ k := fun k => pow_mul ζ a k
      have hv3 : (3 : Fin 5).val = 3 := rfl
      have hv4 : (4 : Fin 5).val = 4 := rfl
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hv3, hv4, hpow]
      have h5a : (ζ ^ a) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
      linear_combination h5a
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

private theorem S2_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b : ℕ) : S2 ζ a b = (c2 a b : ℂ) := by
  unfold S2 c2
  have hinner : ∀ x0 : Fin 5,
      (∑ x1 ∈ Finset.univ.erase x0, ζ ^ (a * x0.val + b * x1.val)) =
      ζ ^ (a * x0.val) * S1 ζ b - ζ ^ ((a + b) * x0.val) := by
    intro x0
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x1 : Fin 5, ζ ^ (a * x0.val + b * x1.val)) = ζ ^ (a * x0.val) * S1 ζ b := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x1 _ => ?_
      rw [pow_add]
    rw [hsplit, add_mul]
  simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change S1 ζ a * S1 ζ b - S1 ζ (a + b) = _
  rw [S1_eq hζ, S1_eq hζ, S1_eq hζ]
  push_cast
  rfl

private theorem S3_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c : ℕ) : S3 ζ a b c = (c3 a b c : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0,
      (∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
      ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
      ζ ^ ((a + c) * x0.val + b * x1.val) -
      ζ ^ (a * x0.val + (b + c) * x1.val) := by
    intro x0 x1 hx1
    rw [Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x2 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val)) =
        ζ ^ (a * x0.val + b * x1.val) * S1 ζ c := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x0.val = (a + c) * x0.val + b * x1.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x1.val = a * x0.val + (b + c) * x1.val := by ring
    rw [h1, h2]
  have hsum : S3 ζ a b c = S2 ζ a b * S1 ζ c - S2 ζ (a + c) b - S2 ζ a (b + c) := by
    unfold S3 S2
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            ∑ x2 ∈ (Finset.univ.erase x0).erase x1, ζ ^ (a * x0.val + b * x1.val + c * x2.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0,
            (ζ ^ (a * x0.val + b * x1.val) * S1 ζ c -
             ζ ^ ((a + c) * x0.val + b * x1.val) -
             ζ ^ (a * x0.val + (b + c) * x1.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 => hinner x0 x1 hx1
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S2_eq hζ, S2_eq hζ, S2_eq hζ, S1_eq hζ]
  unfold c3
  push_cast
  rfl

private theorem S4_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a b c d : ℕ) : S4 ζ a b c d = (c4 a b c d : ℂ) := by
  have hinner : ∀ x0 : Fin 5, ∀ x1 ∈ Finset.univ.erase x0, ∀ x2 ∈ (Finset.univ.erase x0).erase x1,
      (∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
        ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
      ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
      ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
      ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val) := by
    intro x0 x1 hx1 x2 hx2
    rw [Finset.sum_erase_eq_sub hx2, Finset.sum_erase_eq_sub hx1, Finset.sum_erase_eq_sub (Finset.mem_univ x0)]
    have hsplit : (∑ x3 : Fin 5, ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val)) =
        ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d := by
      rw [S1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x3 _ => ?_
      rw [pow_add]
    rw [hsplit]
    have h1 : a * x0.val + b * x1.val + c * x2.val + d * x0.val = (a + d) * x0.val + b * x1.val + c * x2.val := by ring
    have h2 : a * x0.val + b * x1.val + c * x2.val + d * x1.val = a * x0.val + (b + d) * x1.val + c * x2.val := by ring
    have h3 : a * x0.val + b * x1.val + c * x2.val + d * x2.val = a * x0.val + b * x1.val + (c + d) * x2.val := by ring
    rw [h1, h2, h3]
  have hsum : S4 ζ a b c d = S3 ζ a b c * S1 ζ d - S3 ζ (a + d) b c - S3 ζ a (b + d) c - S3 ζ a b (c + d) := by
    unfold S4 S3
    calc (∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
              ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val))
        = ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
            (ζ ^ (a * x0.val + b * x1.val + c * x2.val) * S1 ζ d -
             ζ ^ ((a + d) * x0.val + b * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + (b + d) * x1.val + c * x2.val) -
             ζ ^ (a * x0.val + b * x1.val + (c + d) * x2.val)) := by
          refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 hx1 =>
            Finset.sum_congr rfl fun x2 hx2 => hinner x0 x1 hx1 x2 hx2
      _ = _ := by
          simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, S3_eq hζ, S3_eq hζ, S3_eq hζ, S3_eq hζ, S1_eq hζ]
  unfold c4
  push_cast
  rfl

private theorem sum_emb_eq_S4 (ζ : ℂ) (a b c d : ℕ) :
    (∑ f : Fin 4 ↪ Fin 5, ζ ^ (a * (f 0).val + b * (f 1).val + c * (f 2).val + d * (f 3).val)) =
    S4 ζ a b c d := by
  unfold S4
  let Q : Finset (Σ x0 : Fin 5, Σ x1 : Fin 5, Σ x2 : Fin 5, Fin 5) :=
    Finset.univ.sigma fun x0 => (Finset.univ.erase x0).sigma fun x1 =>
      ((Finset.univ.erase x0).erase x1).sigma fun x2 => (((Finset.univ.erase x0).erase x1).erase x2)
  have hQ : (∑ p ∈ Q, ζ ^ (a * p.1.val + b * p.2.1.val + c * p.2.2.1.val + d * p.2.2.2.val)) =
      ∑ x0 : Fin 5, ∑ x1 ∈ Finset.univ.erase x0, ∑ x2 ∈ (Finset.univ.erase x0).erase x1,
        ∑ x3 ∈ ((Finset.univ.erase x0).erase x1).erase x2,
          ζ ^ (a * x0.val + b * x1.val + c * x2.val + d * x3.val) := by
    simp only [Q, Finset.sum_sigma]
  rw [← hQ]
  refine Finset.sum_bij (fun f _ => ⟨f 0, f 1, f 2, f 3⟩) ?_ ?_ ?_ ?_
  · intro f _
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and]
    refine ⟨f.injective.ne (by decide : (1 : Fin 4) ≠ 0),
      ⟨f.injective.ne (by decide : (2 : Fin 4) ≠ 1), f.injective.ne (by decide : (2 : Fin 4) ≠ 0)⟩,
      f.injective.ne (by decide : (3 : Fin 4) ≠ 2),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 1),
      f.injective.ne (by decide : (3 : Fin 4) ≠ 0)⟩
  · intro f _ g _ heq
    apply Function.Embedding.ext
    intro i
    have h0 : f 0 = g 0 := congrArg Sigma.fst heq
    have h1 : f 1 = g 1 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.1) heq
    have h2 : f 2 = g 2 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.1) heq
    have h3 : f 3 = g 3 :=
      congrArg (fun p : Σ _ : Fin 5, Σ _ : Fin 5, Σ _ : Fin 5, Fin 5 => p.2.2.2) heq
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro p hp
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, and_true, true_and] at hp
    rcases p with ⟨x0, x1, x2, x3⟩
    rcases hp with ⟨h10, ⟨h21, h20⟩, h32, h31, h30⟩
    have hinj : Function.Injective ![x0, x1, x2, x3] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | exact absurd hij h10 | exact absurd hij.symm h10
        | exact absurd hij h20 | exact absurd hij.symm h20
        | exact absurd hij h21 | exact absurd hij.symm h21
        | exact absurd hij h30 | exact absurd hij.symm h30
        | exact absurd hij h31 | exact absurd hij.symm h31
        | exact absurd hij h32 | exact absurd hij.symm h32
    refine ⟨⟨![x0, x1, x2, x3], hinj⟩, Finset.mem_univ _, rfl⟩
  · intro f _
    rfl

abbrev Quad := V3 × V3 × V3 × V3

private def invHadLinear : (Fin 4 → ℂ) →ₗ[ℂ] V3 where
  toFun := invHad
  map_add' x y := by
    ext i; fin_cases i <;> simp [invHad] <;> ring
  map_smul' t x := by
    ext i; fin_cases i <;> simp [invHad] <;> ring

private def toQuad : (Fin 4 → Fin 4 → ℂ) →ₗ[ℂ] Quad where
  toFun X := (invHad (X 0), invHad (X 1), invHad (X 2), invHad (X 3))
  map_add' X Y := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring
  map_smul' c X := by
    ext i <;> fin_cases i <;> simp [invHad] <;> ring

private lemma toQuad_inj_on_zeroSum {X Y : Fin 4 → Fin 4 → ℂ}
    (hX : ∀ r : Fin 4, (∑ i : Fin 4, X r i) = 0)
    (hY : ∀ r : Fin 4, (∑ i : Fin 4, Y r i) = 0)
    (heq : toQuad X = toQuad Y) : X = Y := by
  funext r
  have h : invHad (X r) = invHad (Y r) := by
    fin_cases r
    · exact congrArg Prod.fst heq
    · exact congrArg (fun p => p.2.1) heq
    · exact congrArg (fun p => p.2.2.1) heq
    · exact congrArg (fun p => p.2.2.2) heq
  rw [← had_invHad (X r) (hX r), ← had_invHad (Y r) (hY r), h]

private def pure : V3 →ₗ[ℂ] Quad := LinearMap.inl ℂ V3 (V3 × V3 × V3)

private lemma pure_mem_of_row {L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)}
    {v : Fin 4 → ℂ} (hv : (fun r : Fin 4 => if r = 0 then v else 0) ∈ L) :
    pure (invHadLinear v) ∈ L.map toQuad := by
  refine ⟨_, hv, ?_⟩
  simp [toQuad, invHadLinear, pure, invHad]

private def Q2 (x y z w : V3) : ℂ := dot3 x w + dot3 y z

private def Q3 (x y z w : V3) : ℂ :=
  dot3 z (C3 x) + dot3 x (C3 y) + dot3 w (C3 z) + dot3 y (C3 w)

private def X4 (x y z w : V3) : ℂ :=
  40 * (dot3 x y * dot3 z w + dot3 x z * dot3 y w + dot3 x w * dot3 y z) -
  240 * (x 0 * y 0 * z 0 * w 0 + x 1 * y 1 * z 1 * w 1 + x 2 * y 2 * z 2 * w 2)

private theorem X4_comp (e : Equiv.Perm (Fin 3)) (x y z w : V3) :
    X4 (x ∘ e) (y ∘ e) (z ∘ e) (w ∘ e) = X4 x y z w := by
  have hdot (a b : V3) : dot3 (a ∘ e) (b ∘ e) = dot3 a b := by
    have h := Fintype.sum_equiv e (fun i => a (e i) * b (e i))
      (fun i => a i * b i) (fun _ => rfl)
    simpa only [dot3, Fin.sum_univ_three, Function.comp_apply] using h
  have hdiag := Fintype.sum_equiv e (fun i => x (e i) * y (e i) * z (e i) * w (e i))
    (fun i => x i * y i * z i * w i) (fun _ => rfl)
  simp only [Fin.sum_univ_three] at hdiag
  simp only [X4, hdot, Function.comp_apply, hdiag]

private def P4 (x y z w : V3) : ℂ :=
  -120 * (dot3 y (D3 x) + dot3 x (D3 z) + dot3 w (D3 y) + dot3 z (D3 w)) +
  R4 x w + R4 y z + X4 x y z w

private def mixedHad (x y z w : V3) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    if a.val ≠ b.val ∧ a.val ≠ c.val ∧ a.val ≠ d.val ∧
      b.val ≠ c.val ∧ b.val ≠ d.val ∧ c.val ≠ d.val then
      had x a * had y b * had z c * had w d
    else 0

set_option maxHeartbeats 1000000 in
private theorem mixedHad_eq (x y z w : V3) :
    (c4 1 2 3 4 : ℂ) * mixedHad x y z w = X4 x y z w := by
  norm_num [c4, c3, c2, c1, mixedHad, Fin.sum_univ_four]
  simp only [X4, dot3, had, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private def modeRows (x y z w : V3) : Fin 5 → Fin 4 → ℂ :=
  ![fun _ => 1, had x, had y, had z, had w]

set_option maxHeartbeats 2000000 in
private theorem sum_c4_modes (x y z w : V3) :
    let R := modeRows x y z w
    (∑ a : Fin 5, ∑ b : Fin 5, ∑ c : Fin 5, ∑ d : Fin 5,
      R a 0 * R b 1 * R c 2 * R d 3 * (c4 a.val b.val c.val d.val : ℂ)) =
    120 + 120 * Q2 x y z w + 160 * Q3 x y z w + P4 x y z w := by
  dsimp only
  rw [P4, ← mixedHad_eq]

  simp only [Fin.sum_univ_five]
  norm_num [c4, c3, c2, c1, mixedHad, Fin.sum_univ_four]
  simp only [modeRows, had, Q2, Q3, dot3, C3, D3, R4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul, mul_one]
  ring

private theorem permSum_had {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (x y z w : V3) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
      (1 + ∑ r : Fin 4, (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r i *
        ζ ^ ((r.val + 1) * (f i).val))) =
    120 + 120 * Q2 x y z w + 160 * Q3 x y z w + P4 x y z w := by
  let R := modeRows x y z w
  have hrow (f : Fin 4 ↪ Fin 5) (i : Fin 4) :
      (1 + ∑ r : Fin 4, (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r i *
        ζ ^ ((r.val + 1) * (f i).val)) =
      ∑ a : Fin 5, R a i * ζ ^ (a.val * (f i).val) := by
    have hsucc (r : Fin 4) :
        R r.succ = (![had x, had y, had z, had w] : Fin 4 → Fin 4 → ℂ) r := by
      fin_cases r <;> rfl
    have hzero : R 0 i = 1 := rfl
    symm
    rw [Fin.sum_univ_succ]
    simp only [hzero, hsucc, Fin.val_zero, Fin.val_succ, zero_mul, pow_zero, one_mul]
  have hfactor (f : Fin 4 ↪ Fin 5) :
      (∏ i : Fin 4, ∑ a : Fin 5, R a i * ζ ^ (a.val * (f i).val)) =
      ∑ g : Fin 4 → Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [pow_add, mul_assoc]
  simp_rw [hrow, hfactor]
  rw [Finset.sum_comm]
  have hstep (g : Fin 4 → Fin 5) :
      (∑ f : Fin 4 ↪ Fin 5, (∏ i : Fin 4, R (g i) i) *
        ζ ^ ((g 0).val * (f 0).val + (g 1).val * (f 1).val +
             (g 2).val * (f 2).val + (g 3).val * (f 3).val)) =
      R (g 0) 0 * R (g 1) 1 * R (g 2) 2 * R (g 3) 3 *
        (c4 (g 0).val (g 1).val (g 2).val (g 3).val : ℂ) := by
    rw [← Finset.mul_sum, sum_emb_eq_S4, S4_eq hζ, Fin.prod_univ_four]
  simp_rw [hstep]
  let e : (Fin 4 → Fin 5) ≃ Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
    { toFun := fun g => (g 0, g 1, g 2, g 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := fun g => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨a, b, c, d⟩ => rfl }
  calc
    _ = ∑ p : Fin 5 × Fin 5 × Fin 5 × Fin 5,
        R p.1 0 * R p.2.1 1 * R p.2.2.1 2 * R p.2.2.2 3 *
        (c4 p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val : ℂ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simpa only [Fintype.sum_prod_type] using sum_c4_modes x y z w

private abbrev PlaneV2 := Fin 2 → ℂ

private def planeDot (u v : PlaneV2) : ℂ := u 0 * v 0 + u 1 * v 1

private def planeSwapBilin : (PlaneV2 × PlaneV2) ≃ₗ[ℂ] Module.Dual ℂ (PlaneV2 × PlaneV2) where
  toFun p :=
    { toFun := fun q => planeDot p.1 q.2 + planeDot q.1 p.2
      map_add' := fun q1 q2 => by simp only [planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c q => by simp only [planeDot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' p1 p2 := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c p := by
    apply LinearMap.ext
    intro q
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, planeDot, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun f := (fun i => f (0, Pi.single i 1), fun i => f (Pi.single i 1, 0))
  left_inv p := by
    ext i <;> fin_cases i <;> simp [planeDot]
  right_inv f := by
    apply LinearMap.ext
    rintro ⟨y, z⟩
    have hdecomp : (y, z) =
        y 0 • (Pi.single 0 1, 0) + y 1 • (Pi.single 1 1, 0) +
        z 0 • (0, Pi.single 0 1) + z 1 • (0, Pi.single 1 1) := by
      ext i <;> fin_cases i <;> simp
    conv_rhs => rw [hdecomp]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, planeDot, map_add, map_smul, smul_eq_mul]
    ring

private theorem plane_isotropic_finrank (W : Submodule ℂ (PlaneV2 × PlaneV2))
    (hiso : ∀ p ∈ W, planeDot p.1 p.2 = 0) : Module.finrank ℂ W ≤ 2 := by
  have hle : W.map planeSwapBilin.toLinearMap ≤ W.dualAnnihilator := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro q hq
    have h1 := hiso p hp
    have h2 := hiso q hq
    have h3 := hiso (p + q) (W.add_mem hp hq)
    simp only [planeSwapBilin, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [planeDot, Prod.fst_add, Prod.snd_add, Pi.add_apply] at h1 h2 h3 ⊢
    linear_combination h3 - h1 - h2
  have h1 := LinearEquiv.finrank_map_eq planeSwapBilin W
  have h2 := Submodule.finrank_mono hle
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hdim : Module.finrank ℂ (PlaneV2 × PlaneV2) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega

private theorem plane_nonzero (M : Submodule ℂ Quad) (s : ℂ) (hs : s ≠ 0)
    (hquad : ∀ x y z w : V3, (x, y, z, w) ∈ M → Q2 x y z w = 0)
    (hshape : ∀ x y z w : V3, (x, y, z, w) ∈ M →
      y 0 = 0 ∧ y 1 = -s * y 2 ∧ z 0 = 0 ∧ z 2 = -s * z 1 ∧
        w 0 = 0 ∧ w 1 = -s * w 2) : Module.finrank ℂ M ≤ 4 := by
  let f : M →ₗ[ℂ] (PlaneV2 × PlaneV2) :=
    { toFun := fun u =>
        (![u.val.1 2 - s * u.val.1 1, u.val.2.1 2], ![u.val.2.2.2 2, -2 * s * u.val.2.2.1 1])
      map_add' := by
        intro a b
        ext i <;> fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c a
        ext i <;> fin_cases i <;> simp <;> ring }
  have hr : Module.finrank ℂ (LinearMap.range f) ≤ 2 := by
    apply plane_isotropic_finrank
    rintro _ ⟨⟨⟨x, y, z, w⟩, hm⟩, rfl⟩
    obtain ⟨hy0, hy1, hz0, hz2, hw0, hw1⟩ := hshape x y z w hm
    have h := hquad x y z w hm
    simp [Q2, dot3, hy0, hy1, hz0, hz2, hw0, hw1] at h
    change (x 2 - s * x 1) * w 2 + y 2 * (-2 * s * z 1) = 0
    linear_combination h
  let g : LinearMap.ker f →ₗ[ℂ] (ℂ × ℂ) :=
    { toFun := fun u => (u.val.val.1 0, u.val.val.1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    suffices hzero : ∀ u, g u = 0 → u = 0 by
      intro u v huv
      apply sub_eq_zero.mp
      exact hzero (u - v) ((map_sub g u v).trans (sub_eq_zero.mpr huv))
    rintro ⟨⟨⟨x, y, z, w⟩, hm⟩, hk⟩ h0
    have hx0 : x 0 = 0 := congrArg Prod.fst h0
    have hx1 : x 1 = 0 := congrArg Prod.snd h0
    have hf : f ⟨(x, y, z, w), hm⟩ = 0 := LinearMap.mem_ker.mp hk
    have hx2 : x 2 - s * x 1 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.1 0) hf
    have hy2 : y 2 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.1 1) hf
    have hw2 : w 2 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.2 0) hf
    have hz : -2 * s * z 1 = 0 := congrArg (fun p : PlaneV2 × PlaneV2 => p.2 1) hf
    have hz1 : z 1 = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hs)
    obtain ⟨hy0, hy1, hz0, hz2, hw0, hw1⟩ := hshape x y z w hm
    apply Subtype.ext
    apply Subtype.ext
    change (x, y, z, w) = 0
    ext i <;> fin_cases i <;> simp_all
  have hk := LinearMap.finrank_le_finrank_of_injective hg
  have hd : Module.finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
  have hn := LinearMap.finrank_range_add_finrank_ker f
  omega

private def Valid (M : Submodule ℂ Quad) : Prop :=
  ∀ x y z w : V3, (x, y, z, w) ∈ M → Q2 x y z w = 0 ∧ Q3 x y z w = 0 ∧ P4 x y z w = 0

set_option maxHeartbeats 1000000 in
private lemma extract_homog {x y z w : V3}
    (h : ∀ t : ℂ, 120 * Q2 (t • x) (t • y) (t • z) (t • w) +
      160 * Q3 (t • x) (t • y) (t • z) (t • w) + P4 (t • x) (t • y) (t • z) (t • w) = 0) :
    Q2 x y z w = 0 ∧ Q3 x y z w = 0 ∧ P4 x y z w = 0 := by
  have hscale (t : ℂ) : t ^ 2 * (120 * Q2 x y z w) + t ^ 3 * (160 * Q3 x y z w) +
      t ^ 4 * P4 x y z w = 0 := by
    have h2 : Q2 (t • x) (t • y) (t • z) (t • w) = t ^ 2 * Q2 x y z w := by
      simp only [Q2, dot3, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : Q3 (t • x) (t • y) (t • z) (t • w) = t ^ 3 * Q3 x y z w := by
      simp only [Q3, C3, dot3, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have h4 : P4 (t • x) (t • y) (t • z) (t • w) = t ^ 4 * P4 x y z w := by
      simp only [P4, X4, R4, D3, dot3, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have ht := h t
    rw [h2, h3, h4] at ht
    linear_combination ht
  have h1 := hscale 1
  have hm1 := hscale (-1)
  have h2 := hscale 2
  have hc : Q3 x y z w = 0 := by linear_combination (h1 - hm1) / 320
  have hb : Q2 x y z w = 0 := by linear_combination (16 * h1 - h2 - 1280 * hc) / 1440
  exact ⟨hb, hc, by linear_combination h1 - 120 * hb - 160 * hc⟩

private lemma translate_mem {M : Submodule ℂ Quad} {x y z w u : V3}
    (hp : (x, y, z, w) ∈ M) (hu : (u, 0, 0, 0) ∈ M) (t : ℂ) :
    (x + t • u, y, z, w) ∈ M := by
  simpa [Prod.smul_mk, Prod.mk_add_mk] using M.add_mem hp (M.smul_mem t hu)

set_option maxHeartbeats 1000000 in
private lemma kernel_laws {M : Submodule ℂ Quad} (hM : Valid M)
    {x y z w u : V3} (hp : (x, y, z, w) ∈ M) (hu : (u, 0, 0, 0) ∈ M) :
    dot3 u w = 0 ∧ dot3 z (C3 u) = 0 ∧ dot3 y (D3 u) = 0 := by
  have ht (t : ℂ) := hM _ _ _ _ (translate_mem hp hu t)
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (ht 1).1
    have h0 := (hM _ _ _ _ hp).1
    simp only [Q2, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h0 ⊢
    linear_combination h1 - h0
  · have h1 := (ht 1).2.1
    have hm1 := (ht (-1)).2.1
    have h0 := (hM _ _ _ _ hp).2.1
    simp only [Q3, C3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h0 ⊢
    linear_combination (h1 + hm1 - 2 * h0) / 2
  · have h1 := (ht 1).2.2
    have hm1 := (ht (-1)).2.2
    have h2 := (ht 2).2.2
    have hm2 := (ht (-2)).2.2
    simp only [P4, X4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 hm1 h2 hm2 ⊢
    linear_combination -(h2 - hm2 - 2 * h1 + 2 * hm1) / 1440

private lemma axis_free {M : Submodule ℂ Quad} (hM : Valid M)
    (α : V3) (hα0 : α 0 ≠ 0) (hα1 : α 1 ≠ 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) :
    ∀ p ∈ M, p.2.2.1 = 0 := by
  rintro ⟨x, y, z, w⟩ hp
  let a : ℂ := -α 0 / α 2
  let b : ℂ := -α 1 / α 2
  have ha : a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα0) hα2
  have hb : b ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα1) hα2
  have hu (p q : ℂ) : (![p, q, p * a + q * b], 0, 0, 0) ∈ M := by
    apply hU
    simp only [dot3, a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring
  have h1 := (kernel_laws hM hp (hu 1 0)).2.1
  have h2 := (kernel_laws hM hp (hu 0 1)).2.1
  have h3 := (kernel_laws hM hp (hu 1 1)).2.1
  simp only [dot3, C3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2 h3
  have hz1 : z 1 = 0 := (mul_eq_zero.mp (by linear_combination h1 : a * z 1 = 0)).resolve_left ha
  have hz0 : z 0 = 0 := (mul_eq_zero.mp (by linear_combination h2 : b * z 0 = 0)).resolve_left hb
  have hz2 : z 2 = 0 := by linear_combination h3 - (a + b) * hz0 - (a + b) * hz1
  funext i
  fin_cases i <;> assumption

private lemma axis_shapes {M : Submodule ℂ Quad} (hM : Valid M) (s : ℂ)
    (hU : ∀ a b : ℂ, (![a, b, s * b], 0, 0, 0) ∈ M)
    {x y z w : V3} (hp : (x, y, z, w) ∈ M) :
    y 0 = 0 ∧ y 1 = -s * y 2 ∧ z 2 = -s * z 1 ∧
      s * z 0 = 0 ∧ w 0 = 0 ∧ w 1 = -s * w 2 := by
  obtain ⟨hw0, _, hy0⟩ := kernel_laws hM hp (hU 1 0)
  obtain ⟨hw1, hz0, hy1⟩ := kernel_laws hM hp (hU 0 1)
  obtain ⟨_, hz2, hy2⟩ := kernel_laws hM hp (hU 1 1)
  simp only [dot3, C3, D3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    at hw0 hw1 hy0 hy1 hy2 hz0 hz2
  have hy : y 0 = 0 := by linear_combination hy0
  exact ⟨hy, by linear_combination hy1 - hy2 - s ^ 2 * hy,
    by linear_combination hz2 - hz0, by linear_combination hz0,
    by linear_combination hw0, by linear_combination hw1⟩

set_option maxHeartbeats 1000000 in
private lemma axis_coordinate {M : Submodule ℂ Quad} (hM : Valid M)
    (hU : ∀ a b : ℂ, (![a, b, 0], 0, 0, 0) ∈ M) : ∀ p ∈ M, p.2.2.2 = 0 := by
  rintro ⟨x, y, z, w⟩ hp
  obtain ⟨hy0, hy1, hz2, _, hw0, hw1⟩ := axis_shapes hM 0 (by simpa using hU) hp
  simp only [neg_zero, zero_mul] at hy1 hz2 hw1
  by_cases hw2 : w 2 = 0
  · funext i
    fin_cases i <;> assumption
  · exfalso
    have hquad := (hM _ _ _ _ hp).1
    simp [Q2, dot3, hy0, hy1, hz2, hw0, hw1] at hquad
    have hx2 : x 2 = 0 := hquad.resolve_right hw2
    have ht (t : ℂ) := (hM _ _ _ _ (translate_mem hp (hU 1 0) t)).2.2
    have h1 := ht 1
    have hm1 := ht (-1)
    have h0 := (hM _ _ _ _ hp).2.2
    simp only [P4, X4, R4, D3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hy0, hy1, hz2, hw0, hw1, hx2]
      at h1 hm1 h0
    have hsq : w 2 ^ 2 = 0 := by linear_combination -(h1 + hm1 - 2 * h0) / 80
    exact hw2 (sq_eq_zero_iff.mp hsq)

private lemma axis_normal {M : Submodule ℂ Quad} (hM : Valid M) (hfin : 5 ≤ Module.finrank ℂ M)
    (α : V3) (hα0 : α 0 = 0) (hα2 : α 2 ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) :
    ∀ p ∈ M, p.2.2.2 = 0 := by
  let s : ℂ := -α 1 / α 2
  have hmem (a b : ℂ) : (![a, b, s * b], 0, 0, 0) ∈ M := by
    apply hU
    simp only [dot3, hα0, s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [hα2]; ring
  by_cases hs : s = 0
  · exact axis_coordinate hM (by simpa [hs] using hmem)
  · have hdim := plane_nonzero M s hs (fun x y z w hp => (hM x y z w hp).1) (by
      intro x y z w hp
      obtain ⟨hy0, hy1, hz2, hz0, hw0, hw1⟩ := axis_shapes hM s hmem hp
      exact ⟨hy0, hy1, (mul_eq_zero.mp hz0).resolve_left hs, hz2, hw0, hw1⟩)
    omega

private def permV3 (σ : Equiv.Perm (Fin 3)) : V3 ≃ₗ[ℂ] V3 where
  toFun u := u ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u ∘ σ.symm
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp

private def permQuad (σ : Equiv.Perm (Fin 3)) : Quad ≃ₗ[ℂ] Quad :=
  (permV3 σ).prodCongr ((permV3 σ).prodCongr ((permV3 σ).prodCongr (permV3 σ)))

private lemma perm_dot (i j : Fin 3) (u v : V3) :
    dot3 (permV3 (Equiv.swap i j) u) (permV3 (Equiv.swap i j) v) = dot3 u v := by
  fin_cases i <;> fin_cases j <;> simp [dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

set_option maxHeartbeats 1500000 in
private lemma perm_Q3 (i j : Fin 3) (x y z w : V3) :
    let p := permV3 (Equiv.swap i j)
    Q3 (p x) (p y) (p z) (p w) = Q3 x y z w := by
  fin_cases i <;> fin_cases j <;>
    simp [Q3, C3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

set_option maxHeartbeats 2500000 in
private lemma perm_P4 (i j : Fin 3) (x y z w : V3) :
    let p := permV3 (Equiv.swap i j)
    P4 (p x) (p y) (p z) (p w) = P4 x y z w := by
  dsimp only
  have hx := X4_comp (Equiv.swap i j) x y z w
  change X4 (permV3 (Equiv.swap i j) x) (permV3 (Equiv.swap i j) y)
    (permV3 (Equiv.swap i j) z) (permV3 (Equiv.swap i j) w) = X4 x y z w at hx
  simp only [P4, hx]
  fin_cases i <;> fin_cases j <;>
    simp [R4, D3, dot3, permV3, Equiv.swap_apply_def, Fin.ext_iff] <;> ring

private def Conclusion (M : Submodule ℂ Quad) : Prop :=
  (∀ p ∈ M, p.2.2.1 = 0) ∨ (∀ p ∈ M, p.2.2.2 = 0)

private lemma swap_reduction {M : Submodule ℂ Quad} {α : V3} (hM : Valid M)
    (hfin : 5 ≤ Module.finrank ℂ M)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) (i j : Fin 3) :
    let σ := Equiv.swap i j
    let M' := M.map (permQuad σ).toLinearMap
    Valid M' ∧ 5 ≤ Module.finrank ℂ M' ∧
      (∀ u : V3, dot3 (permV3 σ α) u = 0 → (u, 0, 0, 0) ∈ M') ∧
      (Conclusion M' → Conclusion M) := by
  let σ := Equiv.swap i j
  let e := permV3 σ
  let E := permQuad σ
  let M' := M.map E.toLinearMap
  change Valid M' ∧ 5 ≤ Module.finrank ℂ M' ∧
    (∀ u : V3, dot3 (e α) u = 0 → (u, 0, 0, 0) ∈ M') ∧ (Conclusion M' → Conclusion M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x y z w ⟨⟨a, b, c, d⟩, hp, heq⟩
    change (e a, e b, e c, e d) = (x, y, z, w) at heq
    have hx := congrArg (fun p : Quad => p.1) heq
    have hy := congrArg (fun p : Quad => p.2.1) heq
    have hz := congrArg (fun p : Quad => p.2.2.1) heq
    have hw := congrArg (fun p : Quad => p.2.2.2) heq
    dsimp only at hx hy hz hw
    subst x y z w
    obtain ⟨h2, h3, h4⟩ := hM _ _ _ _ hp
    exact ⟨by simpa only [Q2, e, σ, perm_dot] using h2,
      (perm_Q3 i j _ _ _ _).trans h3, (perm_P4 i j _ _ _ _).trans h4⟩
  · rw [LinearEquiv.finrank_map_eq]; exact hfin
  · intro u hu
    have hαu : dot3 α (e.symm u) = 0 := by
      have h0 := perm_dot i j α (e.symm u)
      change dot3 (e α) (e (e.symm u)) = dot3 α (e.symm u) at h0
      rw [e.apply_symm_apply] at h0
      exact h0.symm.trans hu
    refine ⟨(e.symm u, 0, 0, 0), hU _ hαu, ?_⟩
    change (e (e.symm u), e 0, e 0, e 0) = (u, 0, 0, 0)
    simp
  · rintro (hz | hw)
    · left
      rintro ⟨x, y, z, w⟩ hp
      have h := hz (E (x, y, z, w)) ⟨_, hp, rfl⟩
      change e z = 0 at h
      exact e.injective (h.trans (map_zero e).symm)
    · right
      rintro ⟨x, y, z, w⟩ hp
      have h := hw (E (x, y, z, w)) ⟨_, hp, rfl⟩
      change e w = 0 at h
      exact e.injective (h.trans (map_zero e).symm)

private lemma classify {M : Submodule ℂ Quad} {α : V3} (hM : Valid M)
    (hfin : 5 ≤ Module.finrank ℂ M) (hα : α ≠ 0)
    (hU : ∀ u : V3, dot3 α u = 0 → (u, 0, 0, 0) ∈ M) : Conclusion M := by
  by_cases h0 : α 0 = 0
  · by_cases h2 : α 2 = 0
    · have h1 : α 1 ≠ 0 := by
        intro h1; apply hα; funext i; fin_cases i <;> assumption
      obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 1 2
      apply hback; right
      exact axis_normal hM' hfin' _ (by simpa [permV3, Equiv.swap_apply_def, Fin.ext_iff] using h0)
        (by simpa [permV3] using h1) hU'
    · exact Or.inr (axis_normal hM hfin α h0 h2 hU)
  · by_cases h1 : α 1 = 0
    · by_cases h2 : α 2 = 0
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 2
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h2)
          (by simpa [permV3] using h0) hU'
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 1
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h1)
          (by simpa [permV3, Equiv.swap_apply_def, Fin.ext_iff] using h2) hU'
    · by_cases h2 : α 2 = 0
      · obtain ⟨hM', hfin', hU', hback⟩ := swap_reduction hM hfin hU 0 2
        apply hback; right
        exact axis_normal hM' hfin' _ (by simpa [permV3] using h2)
          (by simpa [permV3] using h0) hU'
      · exact Or.inl (axis_free hM α h0 h1 h2 hU)

private lemma choose_plane (U : Submodule ℂ V3) (hU : 2 ≤ Module.finrank ℂ U) :
    ∃ α : V3, α ≠ 0 ∧ ∀ u : V3, dot3 α u = 0 → u ∈ U := by
  by_cases htop : U = ⊤
  · exact ⟨![0, 0, 1], by intro h; have := congrFun h 2; norm_num at this,
      fun u _ => by simp [htop]⟩
  have hn : Module.finrank ℂ U = 2 := by
    have hk := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at hk
    by_contra! hne
    have h3 : Module.finrank ℂ U = 3 := by omega
    exact htop (Submodule.eq_top_of_finrank_eq (by rwa [Module.finrank_fin_fun]))
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [Module.finrank_fin_fun, hn] at hann
  have hne_bot : U.dualAnnihilator ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hann
    omega
  obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  let α : V3 := fun i => f (Pi.single i 1)
  have hf_eq (u : V3) : f u = dot3 α u := by
    have hu : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hu]
    simp only [map_add, map_smul, smul_eq_mul, dot3, α]
    ring
  have hα : α ≠ 0 := by
    intro h0
    apply hf_ne
    apply LinearMap.ext
    intro u
    rw [hf_eq, h0]
    simp [dot3]
  have hU_eq : U = LinearMap.ker f := by
    have hle : U ≤ LinearMap.ker f := by
      intro u hu
      rw [Submodule.mem_dualAnnihilator] at hf_mem
      exact hf_mem u hu
    have hfr := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at hfr
    have hex_ne : ∃ u : V3, f u ≠ 0 := by
      by_contra! hall
      exact hf_ne (LinearMap.ext hall)
    obtain ⟨u, hu⟩ := hex_ne
    have hrange_top : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro c _
      refine ⟨(c / f u) • u, ?_⟩
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ c hu
    rw [hrange_top, finrank_top, Module.finrank_self] at hfr
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  exact ⟨α, hα, fun u hu => by rw [hU_eq, LinearMap.mem_ker, hf_eq]; exact hu⟩

private lemma solve (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5)
    (L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)) (U : Submodule ℂ (Fin 4 → ℂ))
    (hL : ∀ x ∈ L, (∀ r : Fin 4, (∑ i, x r i) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val+1)*(f i).val))) = 120)
    (hUL : ∀ u ∈ U, (fun r : Fin 4 => if r = 0 then u else 0) ∈ L)
    (hU : 2 ≤ Module.finrank ℂ U) (hfin : 5 ≤ Module.finrank ℂ L) :
    (∀ x ∈ L, x 2 = 0) ∨ (∀ x ∈ L, x 3 = 0) := by
  classical
  let M := L.map toQuad
  have hdim : Module.finrank ℂ M = Module.finrank ℂ L := by
    have hinj : Function.Injective (toQuad.domRestrict L) := by
      intro a b h
      exact Subtype.ext (toQuad_inj_on_zeroSum (hL a a.property).1 (hL b b.property).1 h)
    have hrange : LinearMap.range (toQuad.domRestrict L) = M := by ext p; simp [M]
    exact hrange ▸ LinearMap.finrank_range_of_inj hinj
  have hValid : Valid M := by
    rintro x y z w ⟨X, hX, heq⟩
    change (invHad (X 0), invHad (X 1), invHad (X 2), invHad (X 3)) = (x, y, z, w) at heq
    have hx := congrArg (fun p : Quad => p.1) heq
    have hy := congrArg (fun p : Quad => p.2.1) heq
    have hz := congrArg (fun p : Quad => p.2.2.1) heq
    have hw := congrArg (fun p : Quad => p.2.2.2) heq
    dsimp only at hx hy hz hw
    subst x y z w
    apply extract_homog
    intro t
    obtain ⟨hsum, hperm⟩ := hL (t • X) (L.smul_mem t hX)
    have hhad (r : Fin 4) : had (t • invHad (X r)) = (t • X) r := by
      have hlin : t • invHad (X r) = invHad ((t • X) r) := by
        ext i; fin_cases i <;> simp [invHad] <;> ring
      rw [hlin, had_invHad _ (hsum r)]
    have hrows : (![had (t • invHad (X 0)), had (t • invHad (X 1)),
        had (t • invHad (X 2)), had (t • invHad (X 3))] : Fin 4 → Fin 4 → ℂ) = t • X := by
      funext r
      fin_cases r
      · exact hhad 0
      · exact hhad 1
      · exact hhad 2
      · exact hhad 3
    have heval := permSum_had hζ (t • invHad (X 0)) (t • invHad (X 1))
      (t • invHad (X 2)) (t • invHad (X 3))
    rw [hrows, hperm] at heval
    linear_combination -heval
  let P := M.comap pure
  have hUzero (u : Fin 4 → ℂ) (hu : u ∈ U) : ∑ i, u i = 0 := by
    simpa using (hL _ (hUL u hu)).1 0
  have hP : 2 ≤ Module.finrank ℂ P := by
    have hinj : Function.Injective (invHadLinear.domRestrict U) := by
      intro a b h
      apply Subtype.ext
      change invHad (a : Fin 4 → ℂ) = invHad (b : Fin 4 → ℂ) at h
      rw [← had_invHad _ (hUzero a a.property), ← had_invHad _ (hUzero b b.property), h]
    have hle : LinearMap.range (invHadLinear.domRestrict U) ≤ P := by
      rintro _ ⟨u, rfl⟩
      exact pure_mem_of_row (hUL u u.property)
    have hr := Submodule.finrank_mono hle
    rw [LinearMap.finrank_range_of_inj hinj] at hr
    exact hU.trans hr
  obtain ⟨α, hα, hnormal⟩ := choose_plane P hP
  rcases classify hValid (hdim.symm ▸ hfin) hα (fun u hu => hnormal u hu) with hz | hw
  · left
    intro X hX
    have h : invHad (X 2) = 0 := hz (toQuad X) ⟨X, hX, rfl⟩
    rw [← had_invHad _ ((hL X hX).1 2), h]
    simp [had]
  · right
    intro X hX
    have h : invHad (X 3) = 0 := hw (toQuad X) ⟨X, hX, rfl⟩
    rw [← had_invHad _ ((hL X hX).1 3), h]
    simp [had]

end Proof

theorem main :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
      ∀ (L : Submodule ℂ (Fin 4 → Fin 4 → ℂ)) (U : Submodule ℂ (Fin 4 → ℂ)),
        (∀ x ∈ L, (∀ r : Fin 4, (∑ i, x r i) = 0) ∧
          (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
            (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val+1)*(f i).val))) = 120) →
        (∀ u ∈ U, (fun r : Fin 4 => if r = 0 then u else 0) ∈ L) →
        2 ≤ Module.finrank ℂ U → 5 ≤ Module.finrank ℂ L →
          (∀ x ∈ L, x 2 = 0) ∨ (∀ x ∈ L, x 3 = 0) :=
  solve
end G284

namespace G306

open scoped BigOperators
variable {n : Nat}
abbrev Vec (n : Nat) := Fin n → ℂ
abbrev Mat (n : Nat) := Fin 4 → Fin n → ℂ
def dot (a b : Vec n) : ℂ := ∑ j, a j * b j
def mult3 (n : Nat) : ℂ := ((n-3 : Nat) : ℂ)
def mult2 (n : Nat) : ℂ := ((n-2 : Nat) : ℂ) * mult3 n
noncomputable def e0 (n : Nat) : ℂ := ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)

noncomputable def e1 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3))

noncomputable def e2 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
     X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3))

noncomputable def e3 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
     X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3))

noncomputable def e4 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)

lemma poly_expand (X : Mat n) (t : ℂ) :
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) =
      e0 n + t * e1 X + t ^ 2 * e2 X + t ^ 3 * e3 X + t ^ 4 * e4 X := by
  have hterm : ∀ f : Fin 4 ↪ Fin n,
      (∏ i : Fin 4, (1 + (t • X) i (f i))) =
        (1 : ℂ) +
        t * (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3)) +
        t ^ 2 * (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
          X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3)) +
        t ^ 3 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
          X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) +
        t ^ 4 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) := by
    intro f
    rw [Fin.prod_univ_four]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma coeffs_zero_of_const (X : Mat n)
    (h : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) = e0 n) :
    e2 X = 0 ∧ e3 X = 0 ∧ e4 X = 0 := by
  have h0 := h 0; rw [poly_expand] at h0
  have h1 := h 1; rw [poly_expand] at h1
  have hm1 := h (-1); rw [poly_expand] at hm1
  have h2 := h 2; rw [poly_expand] at h2
  have hm2 := h (-2); rw [poly_expand] at hm2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0) / 24
  · linear_combination (h2 - hm2 - 2 * h1 + 2 * hm1) / 12
  · linear_combination (h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0) / 24

def validTuple (t : Fin n × Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

instance : DecidablePred (validTuple (n:=n)) := fun t => by
  unfold validTuple; infer_instance

lemma sum_emb_eq_nested (g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 := by
  have h1 : (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ t ∈ Finset.univ.filter validTuple, g t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    refine Finset.sum_nbij (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, validTuple]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := f.injective h <;> omega
    · intro f1 _ f2 _ h
      have h0 : f1 0 = f2 0 := congrArg Prod.fst h
      have h1' : f1 1 = f2 1 := congrArg (fun p => p.2.1) h
      have h2' : f1 2 = f2 2 := congrArg (fun p => p.2.2.1) h
      have h3' : f1 3 = f2 3 := congrArg (fun p => p.2.2.2) h
      exact DFunLike.ext f1 f2 fun i => by fin_cases i <;> assumption
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ht
      rcases t with ⟨j0, j1, j2, j3⟩
      rcases ht with ⟨h01, h02, h03, h12, h13, h23⟩
      refine ⟨⟨![j0, j1, j2, j3], ?_⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Ne.symm]
    · intro f _
      rfl
  rw [h1]
  rw [Finset.sum_filter]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j0 _ => ?_
  have hf1 : ∀ x : Fin n, (∑ j2 : Fin n, ∑ j3 : Fin n,
      if validTuple (j0, x, j2, j3) then g j0 x j2 j3 else 0) =
      if x ∈ Finset.univ.erase j0 then
        ∑ j2 ∈ (Finset.univ.erase j0).erase x,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase x).erase j2, g j0 x j2 j3
      else 0 := by
    intro j1
    by_cases h01 : j0 = j1
    · subst h01
      simp [validTuple]
    · have hm1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ _⟩
      rw [if_pos hm1]
      trans ∑ j2 : Fin n, if j2 ∈ (Finset.univ.erase j0).erase j1 then
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 else 0
      · refine Finset.sum_congr rfl fun j2 _ => ?_
        by_cases h2 : j2 ∈ (Finset.univ.erase j0).erase j1
        · rw [if_pos h2]
          have h02 : j0 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h2))
          have h12 : j1 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase h2)
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j3
          simp [validTuple, h01, h02, h12]; exact ⟨fun ⟨a, b, c⟩ => ⟨Ne.symm c, Ne.symm b, Ne.symm a⟩, fun ⟨c, b, a⟩ => ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩⟩
        · rw [if_neg h2]
          have h2' : j0 = j2 ∨ j1 = j2 := by
            simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h2
            by_cases h12 : j2 = j1
            · exact Or.inr h12.symm
            · exact Or.inl (h2 h12).symm
          apply Finset.sum_eq_zero
          intro j3 _
          rcases h2' with rfl | rfl <;> simp [validTuple]
      · rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j2; simp
  simp_rw [hf1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j1; simp

lemma sum_emb_01 (a b : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1)) = -(mult2 n) * dot a b := by
  rw [sum_emb_eq_nested (fun j0 j1 _ _ => a j0 * b j1)]
  have hinner : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) = (mult2 n) * (a j0 * b j1) := by
    intro j0 j1 hj1
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    have hstep : ∀ j2 ∈ ((Finset.univ : Finset (Fin n)).erase j0).erase j1,
        (∑ j3 ∈ (((Finset.univ : Finset (Fin n)).erase j0).erase j1).erase j2, a j0 * b j1) =
          (mult3 n) * (a j0 * b j1) := by
      intro j2 hj2
      rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
      simp [mult3, nsmul_eq_mul, Nat.sub_sub]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hcard2]
    simp [mult2,mult3,nsmul_eq_mul,mul_assoc]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => hinner j0 j1 hj1
  rw [h1]
  have h2 : ∀ j0 : Fin n, (∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1)) = -(mult2 n) * (a j0 * b j0) := by
    intro j0
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h2, ← Finset.mul_sum]
  rfl

lemma sum_emb_pair_eq (i1 i2 : Fin 4) (hi : i1 ≠ i2) (a b : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) = -(mult2 n) * dot a b := by
  have hswap : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 := by
    have he : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 := ⟨Equiv.swap 0 i1, by simp⟩
    rcases he with ⟨σ1, hσ1⟩
    have hne : σ1.symm i2 ≠ 0 := by
      intro h
      have := congrArg σ1 h
      rw [Equiv.apply_symm_apply, hσ1] at this
      exact hi this.symm
    refine ⟨σ1 * Equiv.swap 1 (σ1.symm i2), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) hne.symm, hσ1]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  rcases hswap with ⟨σ, hσ0, hσ1⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1]
  rw [hbij]
  exact sum_emb_01 a b ha hb

lemma e2_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0) :
    e2 X = (mult2 n / 2) * (dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3)) := by
  unfold e2
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_pair_eq 0 1 (by decide) (X 0) (X 1) (hr 0) (hr 1),
      sum_emb_pair_eq 0 2 (by decide) (X 0) (X 2) (hr 0) (hr 2),
      sum_emb_pair_eq 0 3 (by decide) (X 0) (X 3) (hr 0) (hr 3),
      sum_emb_pair_eq 1 2 (by decide) (X 1) (X 2) (hr 1) (hr 2),
      sum_emb_pair_eq 1 3 (by decide) (X 1) (X 3) (hr 1) (hr 3),
      sum_emb_pair_eq 2 3 (by decide) (X 2) (X 3) (hr 2) (hr 3)]
  have hsq : ∑ j : Fin n, (X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    rw [Fin.sum_univ_four] at hj
    rw [hj]; ring
  unfold dot
  have hcomb : ∑ j : Fin n,
      ((X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 -
       (X 0 j * X 0 j + X 1 j * X 1 j + X 2 j * X 2 j + X 3 j * X 3 j) -
       2 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
            X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
  linear_combination (mult2 n / 2) * hcomb - (mult2 n / 2) * hsq

lemma sum_emb_012 (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 _ => a j0 * b j1 * c j2)]
  have hstep3 : ∀ (j0 : Fin n) (j1 : Fin n) (j2 : Fin n),
      j1 ∈ Finset.univ.erase j0 → j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
        (mult3 n) * (a j0 * b j1 * c j2) := by
    intro j0 j1 j2 hj1 hj2
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
    simp [mult3,nsmul_eq_mul,Nat.sub_sub]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => hstep3 j0 j1 j2 hj1 hj2
  rw [h1]
  have h2 : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
        (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) := by
    intro j0 j1 hj1
    have : ∀ j2, (mult3 n) * (a j0 * b j1 * c j2) = ((mult3 n) * a j0 * b j1) * c j2 := fun _ => by ring
    simp_rw [this, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc]
    ring
  have h3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [h3]
  have h4 : ∀ j0 : Fin n,
      (∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1))) =
        (2 * mult3 n) * (a j0 * b j0 * c j0) - (mult3 n) * a j0 * (∑ j1, b j1 * c j1) := by
    intro j0
    have hsplit : ∀ j1, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) =
        (-(mult3 n) * a j0 * c j0) * b j1 - ((mult3 n) * a j0) * (b j1 * c j1) := fun _ => by ring
    simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h4, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [ha]; ring

lemma sum_emb_triple_eq (i1 i2 i3 : Fin 4) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  have hperm : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 ∧ σ 2 = i3 := by
    have hi4 : ∃ i4 : Fin 4, i4 ≠ i1 ∧ i4 ≠ i2 ∧ i4 ≠ i3 := by
      fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;> simp_all <;> decide
    rcases hi4 with ⟨i4, h41, h42, h43⟩
    have hinj : Function.Injective ![i1, i2, i3, i4] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]
    refine ⟨Equiv.ofBijective ![i1, i2, i3, i4] (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl⟩
  rcases hperm with ⟨σ, hσ0, hσ1, hσ2⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1, hσ2]
  rw [hbij]
  exact sum_emb_012 a b c ha hb hc

lemma e3_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) :
    e3 X = (2 * mult3 n) * ∑ j, (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
      X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
  unfold e3
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_triple_eq 0 1 2 (by decide) (by decide) (by decide) (X 0) (X 1) (X 2) (hr 0) (hr 1) (hr 2),
      sum_emb_triple_eq 0 1 3 (by decide) (by decide) (by decide) (X 0) (X 1) (X 3) (hr 0) (hr 1) (hr 3),
      sum_emb_triple_eq 0 2 3 (by decide) (by decide) (by decide) (X 0) (X 2) (X 3) (hr 0) (hr 2) (hr 3),
      sum_emb_triple_eq 1 2 3 (by decide) (by decide) (by decide) (X 1) (X 2) (X 3) (hr 1) (hr 2) (hr 3)]
  ring

lemma e4_eq (a b c d : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) (hd : ∑ j, d j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) * d (f 3)) =
      dot a b * dot c d + dot a c * dot b d + dot a d * dot b c -
        6 * ∑ j, a j * b j * c j * d j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 j3 => a j0 * b j1 * c j2 * d j3)]
  have h3 : ∀ (j0 j1 j2 : Fin n), j1 ∈ Finset.univ.erase j0 →
      j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
        a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) := by
    intro j0 j1 j2 hj1 hj2
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj2, Finset.sum_erase_eq_sub hj1,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0), hd]
    ring
  have hs3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => h3 j0 j1 j2 hj1 hj2
  rw [hs3]
  have h2 : ∀ (j0 j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) := by
    intro j0 j1 hj1
    have hsp : ∀ j2, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) =
        (a j0 * b j1 * (- d j0 - d j1)) * c j2 - (a j0 * b j1) * (c j2 * d j2) := fun _ => by ring
    simp_rw [hsp, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc,
        Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  have hs2 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [hs2]
  have h1 : ∀ j0 : Fin n,
      (∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1)) =
        a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
          2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) := by
    intro j0
    have hsp : ∀ j1, a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) =
        (a j0 * (2 * c j0 * d j0 - dot c d)) * b j1 +
        (a j0 * d j0) * (b j1 * c j1) +
        (a j0 * c j0) * (b j1 * d j1) +
        (2 * a j0) * (b j1 * c j1 * d j1) := fun _ => by ring
    simp_rw [hsp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  simp_rw [h1]
  have h0sp : ∀ j0, a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
      2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) =
      dot b c * (a j0 * d j0) + dot b d * (a j0 * c j0) + dot c d * (a j0 * b j0) +
      (2 * ∑ j1, b j1 * c j1 * d j1) * a j0 - 6 * (a j0 * b j0 * c j0 * d j0) := fun _ => by ring
  simp_rw [h0sp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ha]
  unfold dot; ring

open scoped BigOperators
variable {n : Nat}

def Level (L : Submodule ℂ (Mat n)) :=
  ∀ X ∈ L, (∀ i, (∑ j, X i j)=0) ∧ (∀ j, (∑ i, X i j)=0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1+X i (f i))) = e0 n

def sqSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^2 + (X 1 j)^2 + (X 2 j)^2 + (X 3 j)^2)
def cubeSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^3 + (X 1 j)^3 + (X 2 j)^3 + (X 3 j)^3)
def ringProd (X : Mat n) : ℂ := ∑ j, X 0 j * X 1 j * X 2 j * X 3 j
def pairs (X : Mat n) : ℂ := dot (X 0) (X 1) * dot (X 2) (X 3) +
  dot (X 0) (X 2) * dot (X 1) (X 3) + dot (X 0) (X 3) * dot (X 1) (X 2)

theorem forms (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X : Mat n} (mem : X∈L) :
    sqSum X=0 ∧ cubeSum X=0 ∧ pairs X=6*ringProd X := by
  obtain ⟨row,col,_⟩ := valid X mem
  obtain ⟨q,c,k⟩ := coeffs_zero_of_const X (fun t => (valid _ (L.smul_mem t mem)).2.2)
  have nz : mult3 n ≠ 0 := by unfold mult3; exact_mod_cast (show n-3≠0 by omega)
  have nz2 : mult2 n ≠ 0 := by unfold mult2; exact mul_ne_zero (by exact_mod_cast (show n-2≠0 by omega)) nz
  rw [e2_eq X row col] at q
  rw [e3_eq X row] at c
  have sqz := (mul_eq_zero.mp q).resolve_left (div_ne_zero nz2 (by norm_num))
  have cub := (mul_eq_zero.mp c).resolve_left (mul_ne_zero (by norm_num) nz)
  refine ⟨?_,?_,?_⟩
  · simpa [dot,sqSum,Finset.sum_add_distrib,pow_two] using sqz
  · have point (j : Fin n) :
        (X 0 j)^3+(X 1 j)^3+(X 2 j)^3+(X 3 j)^3 =
        3*(X 0 j*X 1 j*X 2 j+X 0 j*X 1 j*X 3 j+X 0 j*X 2 j*X 3 j+X 1 j*X 2 j*X 3 j) := by
      have h := col j
      rw [Fin.sum_univ_four] at h
      linear_combination ((X 0 j)^2+(X 1 j)^2+(X 2 j)^2+(X 3 j)^2 -
        (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j + X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) * h
    simp only [cubeSum,point,← Finset.mul_sum,cub,mul_zero]
  · change (∑ f : Fin 4 ↪ Fin n, X 0 (f 0)*X 1 (f 1)*X 2 (f 2)*X 3 (f 3)) = 0 at k
    rw [e4_eq (X 0) (X 1) (X 2) (X 3) (row 0) (row 1) (row 2) (row 3)] at k
    exact sub_eq_zero.mp k

def pairing (X Y : Mat n) : ℂ := ∑ j, (X 0 j*Y 0 j + X 1 j*Y 1 j + X 2 j*Y 2 j + X 3 j*Y 3 j)

theorem isotropic (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X Y : Mat n}
    (hx : X∈L) (hy : Y∈L) : pairing X Y = 0 := by
  have id : sqSum (X+Y) = sqSum X + sqSum Y + 2*pairing X Y := by
    simp only [sqSum,pairing,Pi.add_apply,←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [(forms hn valid (L.add_mem hx hy)).1,(forms hn valid hx).1,(forms hn valid hy).1] at id
  linear_combination -id/2

theorem cubeSlope (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X Y : Mat n}
    (hx : X∈L) (hy : Y∈L) :
    (∑ j, (X 0 j*(Y 0 j)^2+X 1 j*(Y 1 j)^2+X 2 j*(Y 2 j)^2+X 3 j*(Y 3 j)^2))=0 := by
  have id : cubeSum (X+Y)+cubeSum (X-Y)-2*cubeSum X =
      6*(∑ j, (X 0 j*(Y 0 j)^2+X 1 j*(Y 1 j)^2+X 2 j*(Y 2 j)^2+X 3 j*(Y 3 j)^2)) := by
    simp only [cubeSum,Pi.add_apply,Pi.sub_apply,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [(forms hn valid (L.add_mem hx hy)).2.1,(forms hn valid (L.sub_mem hx hy)).2.1,(forms hn valid hx).2.1] at id
  linear_combination -id/6

def rowScale (w : Fin 4 → ℂ) (v : Vec n) : Mat n := fun i j => w i*v j

theorem dotShift (X : Mat n) (w : Fin 4 → ℂ) (v : Vec n) (null : dot v v=0) (a : ℂ) (i j : Fin 4) :
    dot ((X+a • rowScale w v) i) ((X+a • rowScale w v) j) =
    dot (X i) (X j) + a*(w i*dot v (X j)+w j*dot (X i) v) := by
  have id : dot ((X+a • rowScale w v) i) ((X+a • rowScale w v) j) =
      dot (X i) (X j)+a*(w i*dot v (X j)+w j*dot (X i) v)+a^2*w i*w j*dot v v := by
    simp only [dot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,rowScale,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  simpa [null] using id

theorem quarticSlope (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X : Mat n} (hx : X∈L)
    (w : Fin 4 → ℂ) (v : Vec n) (null : dot v v=0) (hy : rowScale w v ∈ L) :
    (∑ j, (X 0 j*w 1*w 2*w 3+w 0*X 1 j*w 2*w 3+w 0*w 1*X 2 j*w 3+w 0*w 1*w 2*X 3 j)*(v j)^3)=0 := by
  let B (s : ℂ) := X + s • rowScale w v
  let F := ∑ j, (X 0 j*w 1*w 2*w 3+w 0*X 1 j*w 2*w 3+w 0*w 1*X 2 j*w 3+w 0*w 1*w 2*X 3 j)*(v j)^3
  have eq (s : ℂ) : pairs (B s)=6*ringProd (B s) := (forms hn valid (L.add_mem hx (L.smul_mem s hy))).2.2
  have lhs : pairs (B 2)-pairs (B (-2))-2*pairs (B 1)+2*pairs (B (-1))=0 := by
    simp only [B,pairs,dotShift X w v null]
    ring
  have rhs : ringProd (B 2)-ringProd (B (-2))-2*ringProd (B 1)+2*ringProd (B (-1))=12*F := by
    simp only [F,B,ringProd,rowScale,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
      ←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  change F=0
  linear_combination (lhs - eq 2 + eq (-2) + 2*eq 1 - 2*eq (-1) - 6*rhs)/72

open scoped BigOperators
variable {n : Nat}
abbrev Space (n : Nat) := Fin 3 × Fin n → ℂ

def channel (X : Mat n) (k : Fin 3) (j : Fin n) : ℂ :=
  ![X 0 j-X 1 j+X 2 j-X 3 j, X 0 j-X 1 j-X 2 j+X 3 j, X 0 j+X 1 j-X 2 j-X 3 j] k

def encode (n : Nat) : Mat n →ₗ[ℂ] Space n where
  toFun X := fun w => channel X w.1 w.2
  map_add' X Y := by ext ⟨k,j⟩; fin_cases k <;> simp [channel] <;> ring
  map_smul' a X := by ext ⟨k,j⟩; fin_cases k <;> simp [channel] <;> ring

def coords (L : Submodule ℂ (Mat n)) : L →ₗ[ℂ] Space n := (encode n).comp L.subtype

theorem encodeIdent {X Y : Mat n} (cx : ∀ j, (∑ i, X i j)=0) (cy : ∀ j, (∑ i, Y i j)=0)
    (eq : encode n X = encode n Y) : X=Y := by
  funext i j
  have e (k : Fin 3) : channel X k j=channel Y k j := congrFun eq (k,j)
  have ea := e 0; have eb := e 1; have ec := e 2
  have ax := cx j; have ay := cy j
  simp [channel,Fin.sum_univ_four] at ea eb ec ax ay
  fin_cases i
  · change X 0 j=Y 0 j
    linear_combination (ea+eb+ec+ax-ay)/4
  · change X 1 j=Y 1 j
    linear_combination (-ea-eb+ec+ax-ay)/4
  · change X 2 j=Y 2 j
    linear_combination (ea-eb-ec+ax-ay)/4
  · change X 3 j=Y 3 j
    linear_combination (-ea+eb-ec+ax-ay)/4

theorem coordsInj {L : Submodule ℂ (Mat n)} (valid : Level L) : Function.Injective (coords L) := by
  intro x y eq
  exact Subtype.ext (encodeIdent (valid _ x.property).2.1 (valid _ y.property).2.1 eq)

def B (n : Nat) : LinearMap.BilinForm ℂ (Space n) := dotProductBilin ℂ ℂ

theorem proj (a b : Space n) : (B n) a b =
    ∑ j, (a (0,j)*b (0,j)+a (1,j)*b (1,j)+a (2,j)*b (2,j)) := by
  change (∑ w : Fin 3 × Fin n, a w * b w) = _
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,Finset.sum_add_distrib]

theorem bNondeg : (B n).Nondegenerate := by
  constructor
  · intro x hx; funext i
    have h := hx (Pi.single i 1)
    change dotProduct x (Pi.single i 1) = 0 at h
    simpa using h
  · intro y hy; funext i
    have h := hy (Pi.single i 1)
    change dotProduct (Pi.single i 1) y = 0 at h
    simpa using h

theorem gram (X Y : Mat n) (cx : ∀ j, (∑ i, X i j)=0) (cy : ∀ j, (∑ i, Y i j)=0) :
    (B n) (encode n X) (encode n Y) = 4*pairing X Y := by
  rw [proj]
  simp only [pairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ax := cx j; have ay := cy j
  rw [Fin.sum_univ_four] at ax ay
  change channel X 0 j*channel Y 0 j+channel X 1 j*channel Y 1 j+channel X 2 j*channel Y 2 j = _
  simp [channel]
  linear_combination -(X 0 j + X 1 j + X 2 j + X 3 j)*ay

theorem rankCriterion (S T : Submodule ℂ (Space n)) (dimT : Module.finrank ℂ T=5)
    (dis : Disjoint S T) (orth : S ≤ (B n).orthogonal (S ⊔ T)) :
    2*Module.finrank ℂ S+5≤3*n ∧
    (2*Module.finrank ℂ S+5=3*n → S=(B n).orthogonal (S⊔T)) := by
  have ambient : Module.finrank ℂ (Space n) = 3*n := by simp [Space]
  have sup := S.finrank_sup_add_finrank_inf_eq T
  rw [dis.eq_bot,finrank_bot,add_zero,dimT] at sup
  have perp := LinearMap.BilinForm.finrank_orthogonal (B:=B n) bNondeg (S⊔T)
  rw [ambient,sup] at perp
  have le := Submodule.finrank_mono orth
  have cap := (S⊔T : Submodule ℂ (Space n)).finrank_le
  rw [sup,ambient] at cap
  exact ⟨by omega,fun eq => Submodule.eq_of_le_of_finrank_eq orth (by omega)⟩

open scoped BigOperators
variable {n : Nat}
def mom (u : Vec n) (k : Nat) : ℂ := ∑ j, (u j)^k
def mass (v : Space n) (i : Fin 3) := ∑ j, v (i,j)
def weighted (v : Space n) (i : Fin 3) (u : Vec n) (k : Nat) := ∑ j, v (i,j) * (u j)^k

def cleanSpace (u : Vec n) (v : Space n) := (∀ i, mass v i=0) ∧ weighted v 0 u 3=0 ∧ weighted v 1 u 3=0
def plane (L : Submodule ℂ (Mat n)) (u : Vec n) := ∀ s t : ℂ, rowScale ![s,-s,t,-t] u ∈ L

theorem directions (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {u : Vec n}
    (planeMem : plane L u) (p2 : mom u 2=0) {X : Mat n} (hx : X∈L) :
    cleanSpace u (encode n X) ∧ weighted (encode n X) 2 u 2=0 := by
  have row := (valid X hx).1
  have null : dot u u=0 := by simpa [dot,mom,pow_two] using p2
  have h0 := quarticSlope hn valid hx _ u null (planeMem 1 1)
  have h1 := quarticSlope hn valid hx _ u null (planeMem 1 (-1))
  have a := cubeSlope hn valid hx (planeMem 1 0)
  have b := cubeSlope hn valid hx (planeMem 0 1)
  have eq (i : Fin 3) : mass (encode n X) i=0 := by
    fin_cases i <;> simp [mass,encode,channel,Finset.sum_add_distrib,Finset.sum_sub_distrib,row]
  refine ⟨⟨eq,?_,?_⟩,?_⟩
  · change (∑ j, channel X 0 j*(u j)^3)=0
    convert h0 using 1
    apply Finset.sum_congr rfl; intro j _; simp [channel] <;> first | exact Or.inl trivial | ring_nf <;> simp
  · change (∑ j, channel X 1 j*(u j)^3)=0
    convert h1 using 1
    apply Finset.sum_congr rfl; intro j _; simp [channel] <;> first | exact Or.inl trivial | ring_nf <;> simp
  · have eq : weighted (encode n X) 2 u 2 =
        (∑ j, (X 0 j*(u j)^2 + X 1 j*(u j)^2)) - (∑ j, (X 2 j*(u j)^2 + X 3 j*(u j)^2)) := by
      rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; simp [encode,channel]; ring
    simp [rowScale] at a b
    rw [eq,a,b,sub_self]

def noiseAt (u : Vec n) (c : Fin 5 → ℂ) (i : Fin 3) (j : Fin n) :=
  ![c 0+c 3*(u j)^3,c 1+c 4*(u j)^3,c 2] i

def noise (u : Vec n) : (Fin 5 → ℂ) →ₗ[ℂ] Space n where
  toFun c := fun w => noiseAt u c w.1 w.2
  map_add' a b := by ext ⟨i,j⟩; fin_cases i <;> simp [noiseAt] <;> ring
  map_smul' a b := by ext ⟨i,j⟩; fin_cases i <;> simp [noiseAt] <;> ring

theorem noiseEval (u : Vec n) (c : Fin 5 → ℂ) (v : Space n) :
    (B n) (noise u c) v = c 0*mass v 0+c 1*mass v 1+c 2*mass v 2+
      c 3*weighted v 0 u 3+c 4*weighted v 1 u 3 := by
  rw [proj]
  simp only [mass,weighted,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; simp [noise,noiseAt]; ring

theorem noNoise (hn : 4≤n) (u : Vec n) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2)
    (c : Fin 5 → ℂ) (hc : cleanSpace u (noise u c)) : c=0 := by
  obtain ⟨mean,a,b⟩ := hc
  have m0 := mean 0; have m1 := mean 1; have m2 := mean 2
  have npos : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  simp [mass,noise,noiseAt,Finset.sum_add_distrib,←Finset.mul_sum] at m0 m1 m2
  have weight (i l : Fin 5) : (∑ j, (c i + c l * (u j)^3) * (u j)^3)=c i*mom u 3+c l*mom u 6 := by
    simp only [mom,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  change (∑ j, (c 0+c 3*(u j)^3)*(u j)^3)=0 at a
  change (∑ j, (c 1+c 4*(u j)^3)*(u j)^3)=0 at b
  rw [weight] at a b
  have elim (x y : ℂ) (h : (n:ℂ)*x + y*mom u 3=0) (h' : x*mom u 3+y*mom u 6=0) : x=0 ∧ y=0 := by
    have z : ((n:ℂ)*mom u 6-(mom u 3)^2)*y=0 := by linear_combination (n:ℂ)*h' - mom u 3*h
    have yz := (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr det)
    rw [yz,zero_mul,add_zero] at h
    exact ⟨(mul_eq_zero.mp h).resolve_left npos,yz⟩
  obtain ⟨c0,c3⟩ := elim (c 0) (c 3) m0 a
  obtain ⟨c1,c4⟩ := elim (c 1) (c 4) m1 b
  have c2 := m2.resolve_left (show n≠0 by omega)
  funext i; fin_cases i <;> assumption

theorem zeroClean (u : Vec n) : cleanSpace u (0 : Space n) := by simp [cleanSpace,mass,weighted]
theorem injNoise (hn : 4≤n) (u : Vec n) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) : Function.Injective (noise u) := by
  intro a b eq; apply sub_eq_zero.mp; apply noNoise hn u det
  rw [map_sub,eq,sub_self]; exact zeroClean u

open scoped BigOperators
variable {n : Nat}
def Z (v : Vec n) : Mat n := rowScale ![1,1,-1,-1] v

theorem zcols (v : Vec n) (j : Fin n) : (∑ i, Z v i j)=0 := by simp [Z,rowScale,Fin.sum_univ_four]

theorem zChannel (v : Vec n) (k : Fin 3) (j : Fin n) :
    encode n (Z v) (k,j) = if k=2 then 4*v j else 0 := by
  fin_cases k <;> simp [encode,channel,Z,rowScale] <;> ring

theorem zClean (v u : Vec n) (hv : (∑ j, v j)=0) : cleanSpace u (encode n (Z v)) := by
  have mean (i : Fin 3) : mass (encode n (Z v)) i=0 := by
    fin_cases i <;> simp [mass,zChannel,←Finset.mul_sum,hv]
  exact ⟨mean,by simp [weighted,zChannel],by simp [weighted,zChannel]⟩

theorem zGram (v : Vec n) (a : Space n) : (B n) a (encode n (Z v)) = 4*∑ j, a (2,j)*v j := by
  rw [proj,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; simp [zChannel]; ring

theorem rankAndRadical (hn : 4≤n) {u : Vec n} {L : Submodule ℂ (Mat n)} (valid : Level L)
    (hplane : plane L u) (p2 : mom u 2=0) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) :
    2*Module.finrank ℂ L + 5 ≤ 3*n ∧
    (2*Module.finrank ℂ L+5=3*n → ∀ v : Vec n, (∑ j, v j)=0 →
      (∀ X∈L, (∑ j, (encode n X) (2,j)*v j)=0) → Z v∈L) := by
  let S := LinearMap.range (coords L)
  let T := LinearMap.range (noise u)
  have s : Module.finrank ℂ S=Module.finrank ℂ L := LinearMap.finrank_range_of_inj (coordsInj valid)
  have t : Module.finrank ℂ T=5 := by
    change Module.finrank ℂ (LinearMap.range _)=_
    rw [LinearMap.finrank_range_of_inj (injNoise hn u det)]
    simp
  have allClean (v : Space n) (h : v∈S) : cleanSpace u v := by
    obtain ⟨X,rfl⟩ := h
    exact (directions hn valid hplane p2 X.property).1
  have dis : Disjoint S T := by
    apply Submodule.disjoint_def.mpr
    intro v hs ht
    obtain ⟨c,rfl⟩ := ht
    have zero := noNoise hn u det c (allClean _ hs)
    simp [zero]
  have ortho : S ≤ (B n).orthogonal (S⊔T) := by
    intro v hv
    obtain ⟨Y,rfl⟩ := hv
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    obtain ⟨a,⟨X,rfl⟩,b,⟨c,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add,LinearMap.add_apply,noiseEval]
    have eq := gram (X : Mat n) Y (valid _ X.property).2.1 (valid _ Y.property).2.1
    rw [isotropic hn valid X.property Y.property,mul_zero] at eq
    obtain ⟨m,d0,d1⟩ := (directions hn valid hplane p2 Y.property).1
    change (B n) (encode n X) (encode n Y) + _ = 0
    simp only [coords,LinearMap.comp_apply,Submodule.subtype_apply,eq,m,d0,d1,mul_zero,add_zero]
  obtain ⟨upper,full⟩ := rankCriterion S T t dis ortho
  refine ⟨by simpa [s] using upper,?_⟩
  intro equality v mean orthv
  have present : encode n (Z v) ∈ S := by
    rw [full (by rwa [s])]
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    obtain ⟨a,⟨X,rfl⟩,b,⟨c,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add,LinearMap.add_apply,zGram,noiseEval]
    obtain ⟨m,d0,d1⟩ := zClean v u mean
    have h := orthv X X.property
    simpa only [coords,LinearMap.comp_apply,Submodule.subtype_apply,h,m,d0,d1,mul_zero,add_zero]
  obtain ⟨X,hX⟩ := present
  have eq := encodeIdent (valid _ X.property).2.1 (zcols v) hX
  exact eq ▸ X.property

theorem finish (hn : 4≤n) {u : Vec n} {L : Submodule ℂ (Mat n)} (valid : Level L)
    (hplane : plane L u) (p2 : mom u 2=0) (p4 : mom u 4=0) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) :
    2*Module.finrank ℂ L + 5 ≤ 3*n ∧
    (2*Module.finrank ℂ L+5=3*n → mom u 8=0 ∧ (n:ℂ)*mom u 12=(mom u 6)^2) := by
  obtain ⟨upper,atEq⟩ := rankAndRadical hn valid hplane p2 det
  refine ⟨upper,?_⟩
  intro equality
  have zMem := atEq equality
  let v : Vec n := fun j => (u j)^2
  have zv : Z v ∈ L := zMem v p2 (fun X hx => (directions hn valid hplane p2 hx).2)
  have null : dot v v=0 := by simpa [v,dot,mom,←pow_add] using p4
  have sixth (X : Mat n) (hX : X∈L) : weighted (encode n X) 2 u 6=0 := by
    have h := quarticSlope hn valid hX ![1,1,-1,-1] v null zv
    convert h using 1
    apply Finset.sum_congr rfl; intro j _
    change channel X 2 j * (u j)^6 = _
    simp [channel,v]; ring
  have p8 := sixth _ zv
  have z8 : weighted (encode n (Z v)) 2 u 6=4*mom u 8 := by
    simp only [weighted,zChannel,if_true,mom,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; dsimp [v]; ring
  rw [z8] at p8
  refine ⟨(mul_eq_zero.mp p8).resolve_left (by norm_num),?_⟩
  let avg := mom u 6 / (n:ℂ)
  let w : Vec n := fun j => (u j)^6 - avg
  have nz : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have center : (∑ j, w j)=0 := by
    simp only [w,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change mom u 6-(n:ℂ)*avg=0
    dsimp [avg]; field_simp <;> ring
  have ort (X : Mat n) (hX : X∈L) : (∑ j, encode n X (2,j)*w j)=0 := by
    have clean := (directions hn valid hplane p2 hX).1.1 2
    have sixthX := sixth X hX
    change (∑ j, (encode n X) (2,j))=0 at clean
    change (∑ j, (encode n X) (2,j)*(u j)^6)=0 at sixthX
    simp only [w,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,sixthX,clean,zero_mul,sub_zero]
  have h := sixth _ (zMem w center ort)
  have id : weighted (encode n (Z w)) 2 u 6 = 4*(mom u 12 - avg*mom u 6) := by
    simp only [weighted,zChannel,if_true,mom,Finset.mul_sum,←Finset.sum_sub_distrib,mul_sub]
    apply Finset.sum_congr rfl; intro j _; dsimp [w]; ring
  rw [id] at h
  have z := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))
  rw [z]; dsimp [avg]; field_simp

theorem main : (∀ (n : ℕ), 4 ≤ n →
  ∀ (u : Fin n → ℂ) (L : Submodule ℂ (Fin 4 → Fin n → ℂ)),
  let p := fun k : ℕ => ∑ j, (u j)^k
  p 1 = 0 → p 2 = 0 → p 4 = 0 → (n : ℂ) * p 6 ≠ (p 3)^2 →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + X i (f i))) =
      (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) →
  (∀ s t : ℂ, (fun i j => (![s,-s,t,-t] : Fin 4 → ℂ) i * u j) ∈ L) →
  2 * Module.finrank ℂ L + 5 ≤ 3 * n ∧
    (2 * Module.finrank ℂ L + 5 = 3 * n →
      p 8 = 0 ∧ (n : ℂ) * p 12 = (p 6)^2)) := by
  intro n hn u L
  dsimp only
  intro _ p2 p4 determinant valid shared
  exact finish hn valid shared p2 p4 determinant
end G306

namespace Finish

open scoped BigOperators
open Finset

abbrev Mat45 := Fin 4 → Fin 5 → ℂ

lemma e0_five : G306.e0 5 = 120 := by
  unfold G306.e0
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fin]
  norm_num [Nat.descFactorial]

def rowPerm_equiv (τ : Equiv.Perm (Fin 4)) : (Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun a i := a (τ i)
  invFun a i := a (τ.symm i)
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matRowPerm_equiv (τ : Equiv.Perm (Fin 4)) : Mat45 ≃ₗ[ℂ] Mat45 where
  toFun X i j := X (τ i) j
  invFun X i j := X (τ.symm i) j
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matColPerm_equiv (σ : Equiv.Perm (Fin 5)) : Mat45 ≃ₗ[ℂ] Mat45 where
  toFun X i j := X i (σ j)
  invFun X i j := X i (σ.symm j)
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma matRowPerm_valid (τ : Equiv.Perm (Fin 4)) (X : Mat45)
    (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0)
    (hp : (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) :
    (∀ i, ∑ j, matRowPerm_equiv τ X i j = 0) ∧
    (∀ j, ∑ i, matRowPerm_equiv τ X i j = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + matRowPerm_equiv τ X i (f i))) = 120 := by
  refine ⟨fun i => hr (τ i), fun j => ?_, ?_⟩
  · simpa [matRowPerm_equiv] using (Equiv.sum_comp τ (fun i => X i j)).trans (hc j)
  · rw [← hp]
    refine Finset.sum_nbij (fun f => τ.symm.toEmbedding.trans f)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun i => by
        have := DFunLike.congr_fun h (τ i)
        simpa using this
    · intro f _
      exact ⟨τ.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _),
        DFunLike.ext _ _ fun i => by simp⟩
    · intro f _
      change (∏ i : Fin 4, (1 + X (τ i) (f i))) =
        ∏ i : Fin 4, (1 + X i (f (τ.symm i)))
      simpa using Equiv.prod_comp τ (fun i => 1 + X i (f (τ.symm i)))

lemma matColPerm_valid (σ : Equiv.Perm (Fin 5)) (X : Mat45)
    (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0)
    (hp : (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) :
    (∀ i, ∑ j, matColPerm_equiv σ X i j = 0) ∧
    (∀ j, ∑ i, matColPerm_equiv σ X i j = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + matColPerm_equiv σ X i (f i))) = 120 := by
  refine ⟨fun i => ?_, fun j => hc (σ j), ?_⟩
  · simpa [matColPerm_equiv] using (Equiv.sum_comp σ (fun j => X i j)).trans (hr i)
  · rw [← hp]
    refine Finset.sum_nbij (fun f => f.trans σ.toEmbedding)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun i => σ.injective (DFunLike.congr_fun h i)
    · intro f _
      exact ⟨f.trans σ.symm.toEmbedding, Finset.mem_coe.mpr (Finset.mem_univ _),
        DFunLike.ext _ _ fun i => by simp⟩
    · intro f _
      rfl

lemma finrank_map_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (S : Submodule ℂ V) :
    Module.finrank ℂ (S.map e.toLinearMap) = Module.finrank ℂ S := by
  have hinj : Function.Injective (e.toLinearMap.domRestrict S) := fun x y h =>
    Subtype.ext (e.injective h)
  have h1 := LinearMap.finrank_range_of_inj hinj
  have hr : LinearMap.range (e.toLinearMap.domRestrict S) = S.map e.toLinearMap := by
    ext w; simp
  rw [hr] at h1
  exact h1

lemma quad_cubic_of_L {L : Submodule ℂ Mat45}
    (hL : ∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    {X : Mat45} (hX : X ∈ L) :
    (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 2) = 0 ∧
    (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3) = 0 ∧
    G306.e4 X = 0 := by
  have hconst : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) = G306.e0 5 := by
    intro t
    rw [e0_five]
    exact (hL (t • X) (L.smul_mem t hX)).2.2
  obtain ⟨he2, he3, he4⟩ := G306.coeffs_zero_of_const X hconst
  obtain ⟨hr, hc, _⟩ := hL X hX
  have hp2 : (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 2) = 0 := by
    rw [G306.e2_eq X hr hc] at he2
    have hm : G306.mult2 5 / 2 ≠ 0 := by
      unfold G306.mult2 G306.mult3
      norm_num
    have hsum := (mul_eq_zero.mp he2).resolve_left hm
    rw [Fin.sum_univ_four]
    unfold G306.dot at hsum
    simpa [pow_two] using hsum
  have hp3 : (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3) = 0 := by
    rw [G306.e3_eq X hr] at he3
    have hm : 2 * G306.mult3 5 ≠ 0 := by
      unfold G306.mult3
      norm_num
    have hsum := (mul_eq_zero.mp he3).resolve_left hm
    have hrel : ∀ j : Fin 5,
        (X 0 j) ^ 3 + (X 1 j) ^ 3 + (X 2 j) ^ 3 + (X 3 j) ^ 3 =
          3 * (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
            X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
      intro j
      have hcj := hc j
      rw [Fin.sum_univ_four] at hcj
      have h3 : X 3 j = -(X 0 j + X 1 j + X 2 j) := by linear_combination hcj
      rw [h3]; ring
    calc
      (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3)
          = ∑ j : Fin 5, ((X 0 j) ^ 3 + (X 1 j) ^ 3 + (X 2 j) ^ 3 + (X 3 j) ^ 3) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [Fin.sum_univ_four]
      _ = 3 * ∑ j : Fin 5, (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
            X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
            simp_rw [hrel, ← Finset.mul_sum]
      _ = 0 := by rw [hsum, mul_zero]
  exact ⟨hp2, hp3, he4⟩

def V0Space : Submodule ℂ (Fin 4 → ℂ) :=
  { carrier := {a | ∑ i : Fin 4, a i = 0}, add_mem' := fun {a b} ha hb => by
      change ∑ i : Fin 4, (a i + b i) = 0
      rw [Finset.sum_add_distrib]
      have ha' : ∑ i : Fin 4, a i = 0 := ha
      have hb' : ∑ i : Fin 4, b i = 0 := hb
      rw [ha', hb', add_zero]
    zero_mem' := by change ∑ i : Fin 4, (0 : ℂ) = 0; simp
    smul_mem' := fun c {a} ha => by
      change ∑ i : Fin 4, c * a i = 0
      rw [← Finset.mul_sum]
      have ha' : ∑ i : Fin 4, a i = 0 := ha
      rw [ha', mul_zero] }

lemma finrank_V0Space : Module.finrank ℂ V0Space ≤ 3 := by
  let proj : V0Space →ₗ[ℂ] (Fin 3 → ℂ) :=
    { toFun := fun x i => x.1 i.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext; ext i
    have h0 : x.1 0 = y.1 0 := congrFun hxy 0
    have h1 : x.1 1 = y.1 1 := congrFun hxy 1
    have h2 : x.1 2 = y.1 2 := congrFun hxy 2
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · have hx : ∑ k : Fin 4, x.1 k = 0 := x.2
      have hy : ∑ k : Fin 4, y.1 k = 0 := y.2
      rw [Fin.sum_univ_four] at hx hy
      change x.1 3 = y.1 3
      linear_combination hx - hy - h0 - h1 - h2
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi] using hle

lemma exists_p2_ne_zero (A : Submodule ℂ (Fin 4 → ℂ))
    (hdim : 2 ≤ Module.finrank ℂ A) (hsum : ∀ a ∈ A, ∑ i, a i = 0) :
    ∃ a ∈ A, ∑ i : Fin 4, (a i) ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have horth : ∀ a ∈ A, ∀ b ∈ A, ∑ i : Fin 4, a i * b i = 0 := by
    intro a ha b hb
    have h1 := h (a + b) (A.add_mem ha hb)
    have h2 := h a ha
    have h3 := h b hb
    have hpol : ∀ i : Fin 4, (a i + b i) ^ 2 = (a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2 := fun _ => by ring
    simp only [Pi.add_apply] at h1
    simp_rw [hpol, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    linear_combination (h1 - h2 - h3) / 2
  let A' : Submodule ℂ V0Space := A.comap V0Space.subtype
  have hA'_dim : Module.finrank ℂ A' = Module.finrank ℂ A := by
    have hle : A ≤ LinearMap.range V0Space.subtype := by
      rw [Submodule.range_subtype]
      exact fun a ha => hsum a ha
    have hmap : A'.map V0Space.subtype = A := Submodule.map_comap_eq_of_le hle
    have := Submodule.finrank_map_subtype_eq V0Space A'
    rw [hmap] at this
    exact this.symm
  let Φ : A' →ₗ[ℂ] Module.Dual ℂ (V0Space ⧸ A') :=
    { toFun := fun a => Submodule.liftQ A'
        { toFun := fun b => ∑ i : Fin 4, a.1.1 i * b.1 i
          map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun c x => by
            simp only [RingHom.id_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
            have : ∀ i, a.1.1 i * (c * x.1 i) = c * (a.1.1 i * x.1 i) := fun _ => by ring
            simp_rw [this, ← Finset.mul_sum] }
        (fun b hb => horth a.1.1 a.2 b.1 hb)
      map_add' := fun a1 a2 => by
        ext b
        change ∑ i : Fin 4, (a1.1.1 i + a2.1.1 i) * b.1 i =
          (∑ i : Fin 4, a1.1.1 i * b.1 i) + (∑ i : Fin 4, a2.1.1 i * b.1 i)
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        ext b
        change ∑ i : Fin 4, (c * a.1.1 i) * b.1 i = c * ∑ i : Fin 4, a.1.1 i * b.1 i
        have : ∀ i, c * a.1.1 i * b.1 i = c * (a.1.1 i * b.1 i) := fun _ => by ring
        simp_rw [this, ← Finset.mul_sum] }
  have hΦ_inj : Function.Injective Φ := by
    intro a1 a2 h12
    apply Subtype.ext; apply Subtype.ext; ext k
    let vk : V0Space := ⟨fun i => (if i = k then (1 : ℂ) else 0) - (1 / 4 : ℂ), by
      change ∑ i : Fin 4, ((if i = k then (1 : ℂ) else 0) - 1 / 4) = 0
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num⟩
    have hv : (∑ i : Fin 4, a1.1.1 i * vk.1 i) = ∑ i : Fin 4, a2.1.1 i * vk.1 i :=
      LinearMap.congr_fun h12 (Submodule.Quotient.mk vk)
    have heval : ∀ x : V0Space,
        (∑ i : Fin 4, x.1 i * vk.1 i) = x.1 k := by
      intro x
      have hx : ∑ i : Fin 4, x.1 i = 0 := x.2
      change (∑ i : Fin 4, x.1 i * ((if i = k then (1 : ℂ) else 0) - 1 / 4)) = x.1 k
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul, hx, zero_mul, sub_zero]
    rw [heval a1.1, heval a2.1] at hv
    exact hv
  have h1 : Module.finrank ℂ A' ≤ Module.finrank ℂ (V0Space ⧸ A') := by
    have := LinearMap.finrank_le_finrank_of_injective hΦ_inj
    rwa [Subspace.dual_finrank_eq] at this
  have h2 := Submodule.finrank_quotient_add_finrank A'
  have hV0_dim := finrank_V0Space
  omega

lemma subspace_union_avoid {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Submodule ℂ V) :
    ∀ (fs : List (V →ₗ[ℂ] ℂ)),
      (∀ a ∈ A, ∃ f ∈ fs, f a = 0) →
      ∃ f ∈ fs, ∀ a ∈ A, f a = 0 := by
  intro fs
  induction fs with
  | nil =>
    intro h
    obtain ⟨_, hf, _⟩ := h 0 A.zero_mem
    simp at hf
  | cons f rest ih =>
    intro h
    by_cases hf : ∀ a ∈ A, f a = 0
    · exact ⟨f, List.mem_cons_self, hf⟩
    · push Not at hf
      obtain ⟨a0, ha0, hfa0⟩ := hf
      have hrest : ∀ b ∈ A, ∃ g ∈ rest, g b = 0 := by
        intro b hb
        let N := rest.length + 2
        let S : Finset (Fin N) := Finset.univ.filter (fun k => f (b + (k.val : ℂ) • a0) ≠ 0)
        have hbad_card : (Finset.univ.filter (fun k : Fin N => f (b + (k.val : ℂ) • a0) = 0)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro k1 hk1 k2 hk2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
          have h1 : f b + (k1.val : ℂ) * f a0 = 0 := by simpa [map_add, map_smul] using hk1
          have h2 : f b + (k2.val : ℂ) * f a0 = 0 := by simpa [map_add, map_smul] using hk2
          have hd : ((k1.val : ℂ) - (k2.val : ℂ)) * f a0 = 0 := by linear_combination h1 - h2
          have hkeq : (k1.val : ℂ) = (k2.val : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hfa0)
          exact Fin.ext (Nat.cast_injective hkeq)
        have hScard : rest.length < S.card := by
          have hpart := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin N))) (p := fun k : Fin N => f (b + (k.val : ℂ) • a0) = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at hpart
          have hpart' : (Finset.univ.filter (fun k : Fin N => f (b + (k.val : ℂ) • a0) = 0)).card + S.card = rest.length + 2 := hpart
          omega
        have hex : ∀ k ∈ S, ∃ j : Fin rest.length, (rest.get j) (b + (k.val : ℂ) • a0) = 0 := by
          intro k hk
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          obtain ⟨g, hg, hgz⟩ := h (b + (k.val : ℂ) • a0) (A.add_mem hb (A.smul_mem _ ha0))
          rcases List.mem_cons.mp hg with rfl | hg'
          · exact absurd hgz hk
          · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg'
            exact ⟨j, hgz⟩
        classical
        have hrest_pos : 0 < rest.length := by
          have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨k, hk⟩ := hSne
          obtain ⟨j, _⟩ := hex k hk
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
        let pick : Fin N → Fin rest.length := fun k =>
          if hk : k ∈ S then (hex k hk).choose else ⟨0, hrest_pos⟩
        have hlt : (Finset.univ : Finset (Fin rest.length)).card < S.card := by
          simp only [Finset.card_univ, Fintype.card_fin]; exact hScard
        obtain ⟨k1, hk1, k2, hk2, hne, hpeq⟩ :=
          Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun _ _ => Finset.mem_univ _)
        let j := pick k1
        have hj1 : (rest.get j) (b + (k1.val : ℂ) • a0) = 0 := by
          dsimp [j, pick]
          rw [dif_pos hk1]
          exact (hex k1 hk1).choose_spec
        have hj2 : (rest.get j) (b + (k2.val : ℂ) • a0) = 0 := by
          have : j = pick k2 := hpeq
          rw [this]
          dsimp [pick]
          rw [dif_pos hk2]
          exact (hex k2 hk2).choose_spec
        have h1 : (rest.get j) b + (k1.val : ℂ) * (rest.get j) a0 = 0 := by
          simpa [map_add, map_smul] using hj1
        have h2 : (rest.get j) b + (k2.val : ℂ) * (rest.get j) a0 = 0 := by
          simpa [map_add, map_smul] using hj2
        have hne' : (k1.val : ℂ) - (k2.val : ℂ) ≠ 0 := by
          intro hc
          exact hne (Fin.ext (Nat.cast_injective (sub_eq_zero.mp hc)))
        have hga0 : (rest.get j) a0 = 0 :=
          (mul_eq_zero.mp (by linear_combination h1 - h2 : ((k1.val : ℂ) - k2.val) * (rest.get j) a0 = 0)).resolve_left hne'
        have hgb : (rest.get j) b = 0 := by linear_combination h1 - (k1.val : ℂ) * hga0
        exact ⟨rest.get j, List.get_mem rest j, hgb⟩
      obtain ⟨g, hg, hgall⟩ := ih hrest
      exact ⟨g, List.mem_cons_of_mem f hg, hgall⟩

lemma newton5_poly (u : Fin 5 → ℂ)
    (hp1 : ∑ j : Fin 5, u j = 0)
    (hp2 : ∑ j : Fin 5, (u j) ^ 2 = 0)
    (hp4 : ∑ j : Fin 5, (u j) ^ 4 = 0) :
    ∀ j : Fin 5, (u j) ^ 5 =
      ((∑ k : Fin 5, (u k) ^ 3) / 3) * (u j) ^ 2 + (∑ k : Fin 5, (u k) ^ 5) / 5 := by
  let a := u 0; let b := u 1; let c := u 2; let d := u 3; let e := u 4
  have h1 : a + b + c + d + e = 0 := by simpa [a, b, c, d, e, Fin.sum_univ_five] using hp1
  have h2 : a^2 + b^2 + c^2 + d^2 + e^2 = 0 := by simpa [a, b, c, d, e, Fin.sum_univ_five] using hp2
  have h4 : a^4 + b^4 + c^4 + d^4 + e^4 = 0 := by simpa [a, b, c, d, e, Fin.sum_univ_five] using hp4
  let p3 := a^3 + b^3 + c^3 + d^3 + e^3
  let p5 := a^5 + b^5 + c^5 + d^5 + e^5
  let e1 := a + b + c + d + e
  let e2 := a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e
  let e3 := a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e
  let e4 := a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e
  let e5 := a*b*c*d*e
  have he1 : e1 = 0 := h1
  have he2 : e2 = 0 := by
    have : 2 * e2 = e1 ^ 2 - (a^2 + b^2 + c^2 + d^2 + e^2) := by dsimp [e1, e2]; ring
    rw [he1, h2] at this; linear_combination this / 2
  have he3 : e3 = p3 / 3 := by
    have : 3 * e3 = p3 - e1 * (a^2 + b^2 + c^2 + d^2 + e^2) + e2 * e1 := by dsimp [e1, e2, e3, p3]; ring
    rw [he1, he2, h2] at this; linear_combination this / 3
  have he4 : e4 = 0 := by
    have : 4 * e4 = e1 * p3 - e2 * (a^2 + b^2 + c^2 + d^2 + e^2) + e3 * e1 - (a^4 + b^4 + c^4 + d^4 + e^4) := by
      dsimp [e1, e2, e3, e4, p3]; ring
    rw [he1, he2, h2, h4] at this; linear_combination this / 4
  have he5 : e5 = p5 / 5 := by
    have : 5 * e5 = p5 - e1 * (a^4 + b^4 + c^4 + d^4 + e^4) + e2 * p3 - e3 * (a^2 + b^2 + c^2 + d^2 + e^2) + e4 * e1 := by
      dsimp [e1, e2, e3, e4, e5, p3, p5]; ring
    rw [he1, he2, he4, h2, h4] at this; linear_combination this / 5
  have hroot : ∀ z : ℂ, (z - a) * (z - b) * (z - c) * (z - d) * (z - e) =
      z^5 - e1 * z^4 + e2 * z^3 - e3 * z^2 + e4 * z - e5 := fun z => by
    dsimp [e1, e2, e3, e4, e5]; ring
  intro j
  have hz0 : (u j - a) * (u j - b) * (u j - c) * (u j - d) * (u j - e) = 0 := by
    fin_cases j <;> simp [a, b, c, d, e]
  rw [hroot (u j), he1, he2, he3, he4, he5] at hz0
  have hp3' : ∑ k : Fin 5, (u k) ^ 3 = p3 := by simp [p3, a, b, c, d, e, Fin.sum_univ_five]
  have hp5' : ∑ k : Fin 5, (u k) ^ 5 = p5 := by simp [p5, a, b, c, d, e, Fin.sum_univ_five]
  rw [hp3', hp5']
  linear_combination hz0

lemma case1_contra (u : Fin 5 → ℂ)
    (hp1 : ∑ j : Fin 5, u j = 0) (hp2 : ∑ j : Fin 5, (u j) ^ 2 = 0)
    (hp3 : ∑ j : Fin 5, (u j) ^ 3 ≠ 0) (hp4 : ∑ j : Fin 5, (u j) ^ 4 = 0) :
    5 * (∑ j : Fin 5, (u j) ^ 6) ≠ (∑ j : Fin 5, (u j) ^ 3) ^ 2 ∧
    ((∑ j : Fin 5, (u j) ^ 8) = 0 →
      5 * (∑ j : Fin 5, (u j) ^ 12) = (∑ j : Fin 5, (u j) ^ 6) ^ 2 → False) := by
  have h5 := newton5_poly u hp1 hp2 hp4
  set p3 := ∑ j : Fin 5, (u j) ^ 3
  set p5 := ∑ j : Fin 5, (u j) ^ 5
  have hp6 : ∑ j : Fin 5, (u j) ^ 6 = p3 ^ 2 / 3 := by
    have : ∀ j : Fin 5, (u j) ^ 6 = (p3 / 3) * (u j) ^ 3 + (p5 / 5) * u j := fun j => by
      have hj := h5 j; linear_combination u j * hj
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hp1]
    change (p3 / 3) * p3 + (p5 / 5) * 0 = p3 ^ 2 / 3
    ring
  have hp8 : ∑ j : Fin 5, (u j) ^ 8 = (8 / 15 : ℂ) * p3 * p5 := by
    have : ∀ j : Fin 5, (u j) ^ 8 = (p3 / 3) * (u j) ^ 5 + (p5 / 5) * (u j) ^ 3 := fun j => by
      have hj := h5 j; linear_combination (u j) ^ 3 * hj
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    change (p3 / 3) * p5 + (p5 / 5) * p3 = (8 / 15 : ℂ) * p3 * p5
    ring
  refine ⟨?_, ?_⟩
  · rw [hp6]
    intro heq
    have : p3 ^ 2 = 0 := by linear_combination (3 / 2 : ℂ) * heq
    exact hp3 (eq_zero_of_pow_eq_zero this)
  · intro h8 h12
    rw [hp8] at h8
    have hp5z : p5 = 0 := by
      have h8' : ((8 / 15 : ℂ) * p3) * p5 = 0 := by linear_combination h8
      have hnz : (8 / 15 : ℂ) * p3 ≠ 0 := mul_ne_zero (by norm_num) hp3
      exact (mul_eq_zero.mp h8').resolve_left hnz
    have hp12 : ∑ j : Fin 5, (u j) ^ 12 = p3 ^ 4 / 27 := by
      have h6j : ∀ j : Fin 5, (u j) ^ 6 = (p3 / 3) * (u j) ^ 3 := fun j => by
        have hj := h5 j; rw [hp5z] at hj; linear_combination u j * hj
      have h12j : ∀ j : Fin 5, (u j) ^ 12 = (p3 / 3) ^ 2 * (u j) ^ 6 := fun j => by
        have hj := h6j j; linear_combination ((u j) ^ 6 + (p3 / 3) * (u j) ^ 3) * hj
      simp_rw [h12j, ← Finset.mul_sum, hp6]
      ring
    rw [hp12, hp6] at h12
    have : p3 ^ 4 = 0 := by linear_combination (27 / 2 : ℂ) * h12
    exact hp3 (eq_zero_of_pow_eq_zero this)

def V45 : Submodule ℂ Mat45 :=
  { carrier := {X | (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0)}, add_mem' := fun {a b} ha hb => ⟨fun i => by
      change ∑ j, (a i j + b i j) = 0
      rw [Finset.sum_add_distrib, ha.1 i, hb.1 i, add_zero],
      fun j => by
      change ∑ i, (a i j + b i j) = 0
      rw [Finset.sum_add_distrib, ha.2 j, hb.2 j, add_zero]⟩
    zero_mem' := ⟨fun _ => by change ∑ j : Fin 5, (0 : ℂ) = 0; simp,
      fun _ => by change ∑ i : Fin 4, (0 : ℂ) = 0; simp⟩
    smul_mem' := fun c {a} ha => ⟨fun i => by
      change ∑ j, c * a i j = 0
      rw [← Finset.mul_sum, ha.1 i, mul_zero],
      fun j => by
      change ∑ i, c * a i j = 0
      rw [← Finset.mul_sum, ha.2 j, mul_zero]⟩ }

lemma finrank_V45 : Module.finrank ℂ V45 ≤ 12 := by
  let proj : V45 →ₗ[ℂ] (Fin 3 → Fin 4 → ℂ) :=
    { toFun := fun X i j => X.1 i.castSucc j.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective proj := by
    intro X Y hXY
    apply Subtype.ext; ext i j
    have h34 : ∀ (a : Fin 3) (b : Fin 4), X.1 a.castSucc b.castSucc = Y.1 a.castSucc b.castSucc :=
      fun a b => congrFun (congrFun hXY a) b
    have hrow_eq : ∀ a : Fin 3, ∀ j : Fin 5, X.1 a.castSucc j = Y.1 a.castSucc j := by
      intro a j
      have e0 : X.1 a.castSucc 0 = Y.1 a.castSucc 0 := h34 a 0
      have e1 : X.1 a.castSucc 1 = Y.1 a.castSucc 1 := h34 a 1
      have e2 : X.1 a.castSucc 2 = Y.1 a.castSucc 2 := h34 a 2
      have e3 : X.1 a.castSucc 3 = Y.1 a.castSucc 3 := h34 a 3
      fin_cases j
      · exact e0
      · exact e1
      · exact e2
      · exact e3
      · have hx : ∑ k : Fin 5, X.1 a.castSucc k = 0 := X.2.1 a.castSucc
        have hy : ∑ k : Fin 5, Y.1 a.castSucc k = 0 := Y.2.1 a.castSucc
        rw [Fin.sum_univ_five] at hx hy
        change X.1 a.castSucc 4 = Y.1 a.castSucc 4
        linear_combination hx - hy - e0 - e1 - e2 - e3
    have r0 : X.1 0 j = Y.1 0 j := hrow_eq 0 j
    have r1 : X.1 1 j = Y.1 1 j := hrow_eq 1 j
    have r2 : X.1 2 j = Y.1 2 j := hrow_eq 2 j
    fin_cases i
    · exact r0
    · exact r1
    · exact r2
    · have hx : ∑ k : Fin 4, X.1 k j = 0 := X.2.2 j
      have hy : ∑ k : Fin 4, Y.1 k j = 0 := Y.2.2 j
      rw [Fin.sum_univ_four] at hx hy
      change X.1 3 j = Y.1 3 j
      linear_combination hx - hy - r0 - r1 - r2
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim12 : Module.finrank ℂ (Fin 3 → Fin 4 → ℂ) = 12 := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_pi]
  omega

noncomputable def V45_test (i0 : Fin 4) (j0 : Fin 5) : V45 :=
  ⟨fun i j => ((if i = i0 then (1 : ℂ) else 0) - 1 / 4) *
      ((if j = j0 then (1 : ℂ) else 0) - 1 / 5),
    ⟨fun i => by
      change ∑ j : Fin 5, ((if i = i0 then (1 : ℂ) else 0) - 1 / 4) *
        ((if j = j0 then (1 : ℂ) else 0) - 1 / 5) = 0
      rw [← Finset.mul_sum]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num,
     fun j => by
      change ∑ i : Fin 4, ((if i = i0 then (1 : ℂ) else 0) - 1 / 4) *
        ((if j = j0 then (1 : ℂ) else 0) - 1 / 5) = 0
      rw [← Finset.sum_mul]
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num⟩⟩

lemma V45_eval (X : V45) (i0 : Fin 4) (j0 : Fin 5) :
    (∑ i : Fin 4, ∑ j : Fin 5, X.1 i j * (V45_test i0 j0).1 i j) = X.1 i0 j0 := by
  have hinner : ∀ i : Fin 4,
      (∑ j : Fin 5, X.1 i j * (V45_test i0 j0).1 i j) =
        ((if i = i0 then (1 : ℂ) else 0) - 1 / 4) * X.1 i j0 := by
    intro i
    have hri : ∑ j : Fin 5, X.1 i j = 0 := X.2.1 i
    have : ∀ j : Fin 5, X.1 i j * (V45_test i0 j0).1 i j =
        ((if i = i0 then (1 : ℂ) else 0) - 1 / 4) * (X.1 i j * ((if j = j0 then (1 : ℂ) else 0) - 1 / 5)) :=
      fun _ => by dsimp [V45_test]; ring
    simp_rw [this, ← Finset.mul_sum, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul, hri, zero_mul, sub_zero]
  have hcj : ∑ i : Fin 4, X.1 i j0 = 0 := X.2.2 j0
  simp_rw [hinner, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, hcj, mul_zero, sub_zero]

def Wmap45 (w : Fin 5 → ℂ) (hw : ∑ j : Fin 5, w j = 0) : (Fin 3 → ℂ) →ₗ[ℂ] V45 where
  toFun c := ⟨fun i j => (![c 0, c 1, c 2, -(c 0 + c 1 + c 2)] : Fin 4 → ℂ) i * w j,
    ⟨fun i => by
      change ∑ j : Fin 5, _ = 0
      rw [← Finset.mul_sum, hw, mul_zero],
     fun j => by
      change ∑ i : Fin 4, _ = 0
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring⟩⟩
  map_add' c1 c2 := by
    apply Subtype.ext; ext i j
    fin_cases i <;> simp <;> ring
  map_smul' r c := by
    apply Subtype.ext; ext i j
    fin_cases i <;> simp <;> ring

lemma case2_bound (L : Submodule ℂ Mat45) (u : Fin 5 → ℂ)
    (hp2 : ∑ j : Fin 5, (u j) ^ 2 = 0)
    (hp4 : ∑ j : Fin 5, (u j) ^ 4 ≠ 0)
    (hL : ∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (hR : ∀ s t : ℂ, (fun i j => (![s, t, -s - t, 0] : Fin 4 → ℂ) i * u j) ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  have hLqc : ∀ X ∈ L, (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 2) = 0 ∧
      (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3) = 0 := fun X hX =>
    ⟨(quad_cubic_of_L hL hX).1, (quad_cubic_of_L hL hX).2.1⟩
  have horthLL : ∀ X ∈ L, ∀ Y ∈ L, ∑ i : Fin 4, ∑ j : Fin 5, X i j * Y i j = 0 := by
    intro X hX Y hY
    have h1 := (hLqc (X + Y) (L.add_mem hX hY)).1
    have h2 := (hLqc X hX).1
    have h3 := (hLqc Y hY).1
    have hpol : ∀ i : Fin 4, ∀ j : Fin 5,
        (X i j + Y i j) ^ 2 = (X i j) ^ 2 + 2 * (X i j * Y i j) + (Y i j) ^ 2 := fun _ _ => by ring
    simp only [Pi.add_apply] at h1
    simp_rw [hpol, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    linear_combination (h1 - h2 - h3) / 2
  have hrow_u2 : ∀ X ∈ L, ∀ i : Fin 4, ∑ j : Fin 5, X i j * (u j) ^ 2 = 0 := by
    intro X hX
    have hlin : ∀ s t : ℂ,
        ∑ i : Fin 4, ∑ j : Fin 5, X i j * ((![s, t, -s - t, 0] : Fin 4 → ℂ) i) ^ 2 * (u j) ^ 2 = 0 := by
      intro s t
      let R : Mat45 := fun i j => (![s, t, -s - t, 0] : Fin 4 → ℂ) i * u j
      have hRm : R ∈ L := hR s t
      have hlam : ∀ c : ℂ, ∑ i : Fin 4, ∑ j : Fin 5, (X i j + c * R i j) ^ 3 = 0 := by
        intro c
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          (hLqc (X + c • R) (L.add_mem hX (L.smul_mem c hRm))).2
      have hexp : ∀ c : ℂ,
          (∑ i : Fin 4, ∑ j : Fin 5, (X i j + c * R i j) ^ 3) =
            (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3) +
            c * (3 * ∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 2 * R i j) +
            c ^ 2 * (3 * ∑ i : Fin 4, ∑ j : Fin 5, X i j * (R i j) ^ 2) +
            c ^ 3 * (∑ i : Fin 4, ∑ j : Fin 5, (R i j) ^ 3) := by
        intro c
        have pt : ∀ i j, (X i j + c * R i j) ^ 3 =
            (X i j) ^ 3 + c * (3 * ((X i j) ^ 2 * R i j)) +
            c ^ 2 * (3 * (X i j * (R i j) ^ 2)) + c ^ 3 * (R i j) ^ 3 := fun _ _ => by ring
        simp_rw [pt, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h0 := hlam 0; rw [hexp] at h0
      have h1 := hlam 1; rw [hexp] at h1
      have hm1 := hlam (-1); rw [hexp] at hm1
      have hq : ∑ i : Fin 4, ∑ j : Fin 5, X i j * (R i j) ^ 2 = 0 := by
        linear_combination (h1 + hm1 - 2 * h0) / 6
      convert hq using 1
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      dsimp [R]; ring
    have hst : ∀ s t : ℂ,
        s ^ 2 * (∑ j : Fin 5, X 0 j * (u j) ^ 2) +
        t ^ 2 * (∑ j : Fin 5, X 1 j * (u j) ^ 2) +
        (s + t) ^ 2 * (∑ j : Fin 5, X 2 j * (u j) ^ 2) = 0 := by
      intro s t
      have hl := hlin s t
      rw [Fin.sum_univ_four] at hl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hl
      have h0' : ∀ j : Fin 5, X 0 j * s ^ 2 * u j ^ 2 = s ^ 2 * (X 0 j * u j ^ 2) := fun _ => by ring
      have h1' : ∀ j : Fin 5, X 1 j * t ^ 2 * u j ^ 2 = t ^ 2 * (X 1 j * u j ^ 2) := fun _ => by ring
      have h2' : ∀ j : Fin 5, X 2 j * (-s - t) ^ 2 * u j ^ 2 = (s + t) ^ 2 * (X 2 j * u j ^ 2) := fun _ => by ring
      simp_rw [h0', h1', h2', ← Finset.mul_sum] at hl
      exact hl
    have e10 := hst 1 0
    have e01 := hst 0 1
    have e11 := hst 1 1
    have h2z : ∑ j : Fin 5, X 2 j * (u j) ^ 2 = 0 := by linear_combination (e11 - e10 - e01) / 2
    have h0z : ∑ j : Fin 5, X 0 j * (u j) ^ 2 = 0 := by linear_combination e10 - h2z
    have h1z : ∑ j : Fin 5, X 1 j * (u j) ^ 2 = 0 := by linear_combination e01 - h2z
    have h3z : ∑ j : Fin 5, X 3 j * (u j) ^ 2 = 0 := by
      have hc : ∑ j : Fin 5, (X 0 j + X 1 j + X 2 j + X 3 j) * (u j) ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro j _
        have hcj := (hL X hX).2.1 j
        rw [Fin.sum_univ_four] at hcj
        rw [hcj, zero_mul]
      simp only [add_mul, Finset.sum_add_distrib] at hc
      linear_combination hc - h0z - h1z - h2z
    intro i; fin_cases i <;> assumption
  let w : Fin 5 → ℂ := fun j => (u j) ^ 2
  have hw_sq : ∑ j : Fin 5, (w j) ^ 2 ≠ 0 := by
    have : ∀ j : Fin 5, (w j) ^ 2 = (u j) ^ 4 := fun j => by dsimp [w]; ring
    simp_rw [this]; exact hp4
  let L' : Submodule ℂ V45 := L.comap V45.subtype
  have hL'_dim : Module.finrank ℂ L' = Module.finrank ℂ L := by
    have hle : L ≤ LinearMap.range V45.subtype := by
      rw [Submodule.range_subtype]
      exact fun X hX => ⟨(hL X hX).1, (hL X hX).2.1⟩
    have hmap : L'.map V45.subtype = L := Submodule.map_comap_eq_of_le hle
    have := Submodule.finrank_map_subtype_eq V45 L'
    rw [hmap] at this; exact this.symm
  let W : Submodule ℂ V45 := LinearMap.range (Wmap45 w hp2)
  have hW_dim : Module.finrank ℂ W = 3 := by
    have hinj : Function.Injective (Wmap45 w hp2) := by
      intro c1 c2 h
      have hw0 : ∃ j0 : Fin 5, w j0 ≠ 0 := by
        by_contra hall; push Not at hall
        apply hw_sq
        apply Finset.sum_eq_zero; intro j _; rw [hall j]; ring
      obtain ⟨j0, hj0⟩ := hw0
      ext k
      have hk := congrFun (congrFun (congrArg Subtype.val h) k.castSucc) j0
      dsimp [Wmap45] at hk
      fin_cases k
      · exact mul_right_cancel₀ hj0 (by simpa using hk)
      · exact mul_right_cancel₀ hj0 (by simpa using hk)
      · exact mul_right_cancel₀ hj0 (by simpa using hk)
    have hr := LinearMap.finrank_range_of_inj hinj
    simpa [W, Module.finrank_pi] using hr
  have horthLW : ∀ X ∈ L', ∀ Y ∈ W, ∑ i : Fin 4, ∑ j : Fin 5, X.1 i j * Y.1 i j = 0 := by
    rintro X hX _ ⟨c, rfl⟩
    dsimp [Wmap45]
    apply Finset.sum_eq_zero; intro i _
    have : ∀ j : Fin 5, X.1 i j * ((![c 0, c 1, c 2, -(c 0 + c 1 + c 2)] : Fin 4 → ℂ) i * w j) =
        (![c 0, c 1, c 2, -(c 0 + c 1 + c 2)] : Fin 4 → ℂ) i * (X.1 i j * (u j) ^ 2) :=
      fun j => by dsimp [w]; ring
    simp_rw [this, ← Finset.mul_sum, hrow_u2 X.1 hX i, mul_zero]
  have hdisj : L' ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro X ⟨hXL, ⟨c, rfl⟩⟩
    rw [Submodule.mem_bot]
    have h0 : ∀ d : Fin 3 → ℂ,
        ∑ i : Fin 4, ∑ j : Fin 5, (Wmap45 w hp2 c).1 i j * (Wmap45 w hp2 d).1 i j = 0 :=
      fun d => horthLW (Wmap45 w hp2 c) hXL (Wmap45 w hp2 d) ⟨d, rfl⟩
    have hfact : ∀ d : Fin 3 → ℂ,
        (∑ i : Fin 4, (![c 0, c 1, c 2, -(c 0 + c 1 + c 2)] : Fin 4 → ℂ) i *
          (![d 0, d 1, d 2, -(d 0 + d 1 + d 2)] : Fin 4 → ℂ) i) = 0 := by
      intro d
      have hd := h0 d
      have hsp : (∑ i : Fin 4, ∑ j : Fin 5, (Wmap45 w hp2 c).1 i j * (Wmap45 w hp2 d).1 i j) =
          (∑ i : Fin 4, (![c 0, c 1, c 2, -(c 0 + c 1 + c 2)] : Fin 4 → ℂ) i *
            (![d 0, d 1, d 2, -(d 0 + d 1 + d 2)] : Fin 4 → ℂ) i) * (∑ j : Fin 5, (w j) ^ 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        dsimp [Wmap45]; ring
      rw [hsp] at hd
      exact (mul_eq_zero.mp hd).resolve_right hw_sq
    have e0 := hfact ![1, 0, 0]
    have e1 := hfact ![0, 1, 0]
    have e2 := hfact ![0, 0, 1]
    rw [Fin.sum_univ_four] at e0 e1 e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e0 e1 e2
    have hc0 : c 0 = 0 := by linear_combination (3 * e0 - e1 - e2) / 4
    have hc1 : c 1 = 0 := by linear_combination (3 * e1 - e0 - e2) / 4
    have hc2 : c 2 = 0 := by linear_combination (3 * e2 - e0 - e1) / 4
    have hc : c = 0 := by ext i; fin_cases i <;> assumption
    rw [hc, map_zero]
  let Φ : L' →ₗ[ℂ] Module.Dual ℂ (V45 ⧸ (L' ⊔ W)) :=
    { toFun := fun X => Submodule.liftQ (L' ⊔ W)
        { toFun := fun Y => ∑ i : Fin 4, ∑ j : Fin 5, X.1.1 i j * Y.1 i j
          map_add' := fun Y1 Y2 => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun r Y => by
            simp only [RingHom.id_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
            have : ∀ i j, X.1.1 i j * (r * Y.1 i j) = r * (X.1.1 i j * Y.1 i j) := fun _ _ => by ring
            simp_rw [this, ← Finset.mul_sum] }
        (by
          intro Y hY
          rcases Submodule.mem_sup.mp hY with ⟨Y1, hY1, Y2, hY2, rfl⟩
          change ∑ i : Fin 4, ∑ j : Fin 5, X.1.1 i j * (Y1.1 i j + Y2.1 i j) = 0
          simp only [mul_add, Finset.sum_add_distrib]
          rw [horthLL X.1.1 X.2 Y1.1 hY1, horthLW X.1 X.2 Y2 hY2, add_zero])
      map_add' := fun X1 X2 => by
        ext Y
        change ∑ i : Fin 4, ∑ j : Fin 5, (X1.1.1 i j + X2.1.1 i j) * Y.1 i j =
          (∑ i : Fin 4, ∑ j : Fin 5, X1.1.1 i j * Y.1 i j) +
          (∑ i : Fin 4, ∑ j : Fin 5, X2.1.1 i j * Y.1 i j)
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        ext Y
        change ∑ i : Fin 4, ∑ j : Fin 5, (r * X.1.1 i j) * Y.1 i j =
          r * ∑ i : Fin 4, ∑ j : Fin 5, X.1.1 i j * Y.1 i j
        have : ∀ i j, r * X.1.1 i j * Y.1 i j = r * (X.1.1 i j * Y.1 i j) := fun _ _ => by ring
        simp_rw [this, ← Finset.mul_sum] }
  have hΦ_inj : Function.Injective Φ := by
    intro X1 X2 h12
    apply Subtype.ext; apply Subtype.ext; ext i0 j0
    have hv : (∑ i : Fin 4, ∑ j : Fin 5, X1.1.1 i j * (V45_test i0 j0).1 i j) =
        ∑ i : Fin 4, ∑ j : Fin 5, X2.1.1 i j * (V45_test i0 j0).1 i j :=
      LinearMap.congr_fun h12 (Submodule.Quotient.mk (V45_test i0 j0))
    rw [V45_eval X1.1 i0 j0, V45_eval X2.1 i0 j0] at hv
    exact hv
  have h1 : Module.finrank ℂ L' ≤ Module.finrank ℂ (V45 ⧸ (L' ⊔ W)) := by
    have := LinearMap.finrank_le_finrank_of_injective hΦ_inj
    rwa [Subspace.dual_finrank_eq] at this
  have h2 := Submodule.finrank_quotient_add_finrank (L' ⊔ W)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq L' W
  have hV_dim := finrank_V45
  rw [hdisj, finrank_bot, add_zero, hW_dim] at h3
  omega

lemma root5_classify {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) {z : ℂ} (hz : z ^ 5 = 1) :
    ∃ k : Fin 5, z = ζ ^ k.val := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have h6 : ζ ^ 6 = ζ := by linear_combination ζ * h5
  have h7 : ζ ^ 7 = ζ ^ 2 := by linear_combination ζ ^ 2 * h5
  have h8 : ζ ^ 8 = ζ ^ 3 := by linear_combination ζ ^ 3 * h5
  have h9 : ζ ^ 9 = ζ ^ 4 := by linear_combination ζ ^ 4 * h5
  have h10 : ζ ^ 10 = 1 := by linear_combination (ζ ^ 5 + 1) * h5
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by norm_num))
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 :=
    (mul_eq_zero.mp (by linear_combination h5 : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) = 0)).resolve_left hne
  have hfac : (z - 1) * (z - ζ) * (z - ζ ^ 2) * (z - ζ ^ 3) * (z - ζ ^ 4) = 0 := by
    have hpoly : (z - 1) * (z - ζ) * (z - ζ ^ 2) * (z - ζ ^ 3) * (z - ζ ^ 4) =
        z ^ 5 - (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) * z ^ 4
        + (ζ + ζ ^ 2 + 2 * ζ ^ 3 + 2 * ζ ^ 4 + 2 * ζ ^ 5 + ζ ^ 6 + ζ ^ 7) * z ^ 3
        - (ζ ^ 3 + ζ ^ 4 + 2 * ζ ^ 5 + 2 * ζ ^ 6 + 2 * ζ ^ 7 + ζ ^ 8 + ζ ^ 9) * z ^ 2
        + (ζ ^ 6 + ζ ^ 7 + ζ ^ 8 + ζ ^ 9 + ζ ^ 10) * z
        - ζ ^ 10 := by ring
    rw [hpoly, hz, h10, h9, h8, h7, h6, h5]
    linear_combination (-z ^ 4 + 2 * z ^ 3 - 2 * z ^ 2 + z) * hsum
  rcases mul_eq_zero.mp hfac with h1234 | h4
  · rcases mul_eq_zero.mp h1234 with h123 | h3
    · rcases mul_eq_zero.mp h123 with h12 | h2
      · rcases mul_eq_zero.mp h12 with h0 | h1
        · exact ⟨0, by simpa using sub_eq_zero.mp h0⟩
        · exact ⟨1, by simpa using sub_eq_zero.mp h1⟩
      · exact ⟨2, sub_eq_zero.mp h2⟩
    · exact ⟨3, sub_eq_zero.mp h3⟩
  · exact ⟨4, sub_eq_zero.mp h4⟩

lemma geom5_sum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) :
    (∑ d : Fin 5, ζ ^ (m * d.val)) = if 5 ∣ m then 5 else 0 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  split_ifs with hdvd
  · obtain ⟨q, rfl⟩ := hdvd
    have : ∀ d : Fin 5, ζ ^ (5 * q * d.val) = 1 := fun d => by
      rw [show 5 * q * d.val = 5 * (q * d.val) by ring, pow_mul, h5, one_pow]
    simp [this]
  · have hne : ζ ^ m ≠ 1 := fun h => hdvd (hζ.dvd_of_pow_eq_one m h)
    have hmul : (ζ ^ m - 1) * (∑ d : Fin 5, ζ ^ (m * d.val)) = 0 := by
      rw [Fin.sum_univ_five]
      have hpow : (ζ ^ m) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
      have hpw : ∀ k : ℕ, ζ ^ (m * k) = (ζ ^ m) ^ k := fun k => pow_mul ζ m k
      change (ζ ^ m - 1) * (ζ ^ (m * 0) + ζ ^ (m * 1) + ζ ^ (m * 2) + ζ ^ (m * 3) + ζ ^ (m * 4)) = 0
      simp only [hpw]
      linear_combination hpow
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

lemma case3_perm (u : Fin 5 → ℂ) (hu : u ≠ 0)
    (hp1 : ∑ j : Fin 5, u j = 0) (hp2 : ∑ j : Fin 5, (u j) ^ 2 = 0)
    (hp3 : ∑ j : Fin 5, (u j) ^ 3 = 0) (hp4 : ∑ j : Fin 5, (u j) ^ 4 = 0) :
    ∃ (ζ : ℂ) (r : ℂ) (σ : Equiv.Perm (Fin 5)),
      IsPrimitiveRoot ζ 5 ∧ r ≠ 0 ∧ ∀ j : Fin 5, u j = r * ζ ^ (σ j).val := by
  have h5 := newton5_poly u hp1 hp2 hp4
  rw [hp3] at h5
  simp only [zero_div, zero_mul, zero_add] at h5
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 5, u j0 ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  let r := u j0
  have hr : r ≠ 0 := hj0
  have hpow1 : ∀ j : Fin 5, (u j / r) ^ 5 = 1 := by
    intro j
    rw [div_pow, h5 j, ← h5 j0]
    exact div_self (pow_ne_zero 5 hr)
  let ζ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hroot : ∀ j : Fin 5, ∃ k : Fin 5, u j / r = ζ ^ k.val :=
    fun j => root5_classify hζ (hpow1 j)
  choose f hf using hroot
  have hfu : ∀ j : Fin 5, u j = r * ζ ^ (f j).val := fun j => by
    have := hf j; field_simp [hr] at this; linear_combination this
  have hpow_zero : ∀ d : Fin 5, d.val ≠ 0 → ∑ j : Fin 5, ζ ^ ((f j).val * d.val) = 0 := by
    intro d hd
    have hsum : ∑ j : Fin 5, (u j / r) ^ d.val = 0 := by
      simp_rw [div_pow, div_eq_mul_inv, ← Finset.sum_mul]
      have : ∑ j : Fin 5, (u j) ^ d.val = 0 := by
        fin_cases d
        · exact absurd rfl hd
        · simpa using hp1
        · exact hp2
        · exact hp3
        · exact hp4
      rw [this, zero_mul]
    convert hsum using 1
    apply Finset.sum_congr rfl; intro j _
    rw [hf j, ← pow_mul]
  have hsurj : Function.Surjective f := by
    intro m
    by_contra hno
    push Not at hno
    have hS : ∑ d : Fin 5, ζ ^ ((5 - m.val) * d.val) * (∑ j : Fin 5, ζ ^ ((f j).val * d.val)) = 5 := by
      rw [Fin.sum_univ_five]
      simp only [Fin.val_zero, mul_zero, pow_zero, one_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hpow_zero 1 (by decide), hpow_zero 2 (by decide), hpow_zero 3 (by decide),
        hpow_zero 4 (by decide)]
      ring
    have hS2 : ∑ d : Fin 5, ζ ^ ((5 - m.val) * d.val) * (∑ j : Fin 5, ζ ^ ((f j).val * d.val)) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro j _
      have hcomb : ∀ d : Fin 5, ζ ^ ((5 - m.val) * d.val) * ζ ^ ((f j).val * d.val) =
          ζ ^ ((5 - m.val + (f j).val) * d.val) := fun d => by
        rw [← pow_add, ← add_mul]
      simp_rw [hcomb, geom5_sum hζ]
      have hndvd : ¬ 5 ∣ (5 - m.val + (f j).val) := by
        have hne : f j ≠ m := hno j
        have hm := m.isLt; have hf' := (f j).isLt
        intro hdvd
        have hne' : (f j).val ≠ m.val := fun h => hne (Fin.ext h)
        omega
      rw [if_neg hndvd]
    rw [hS] at hS2
    norm_num at hS2
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective f (Finite.surjective_iff_bijective.mp hsurj)
  exact ⟨ζ, r, σ, hζ, hr, hfu⟩

lemma case3_bound (L : Submodule ℂ Mat45) (u : Fin 5 → ℂ) (A : Submodule ℂ (Fin 4 → ℂ))
    (hu : u ≠ 0) (hA_dim : 2 ≤ Module.finrank ℂ A)
    (hp1 : ∑ j : Fin 5, u j = 0) (hp2 : ∑ j : Fin 5, (u j) ^ 2 = 0)
    (hp3 : ∑ j : Fin 5, (u j) ^ 3 = 0) (hp4 : ∑ j : Fin 5, (u j) ^ 4 = 0)
    (hL : ∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (hA : ∀ a ∈ A, (fun i j => a i * u j) ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  by_contra hgt
  have hge5 : 5 ≤ Module.finrank ℂ L := by omega
  obtain ⟨ζ, r, σ, hζ, hr, huζ⟩ := case3_perm u hu hp1 hp2 hp3 hp4
  let L1 : Submodule ℂ Mat45 := L.map (matColPerm_equiv σ.symm).toLinearMap
  have hL1_dim : Module.finrank ℂ L1 = Module.finrank ℂ L :=
    finrank_map_equiv (matColPerm_equiv σ.symm) L
  have hL1_val : ∀ X ∈ L1, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120 := by
    rintro _ ⟨X, hX, rfl⟩
    exact matColPerm_valid σ.symm X (hL X hX).1 (hL X hX).2.1 (hL X hX).2.2
  have hL1_A : ∀ a ∈ A, (fun i j : Fin _ => a i * ζ ^ j.val) ∈ L1 := by
    intro a ha
    have hmem : (fun i j => (r⁻¹ • a) i * u j) ∈ L := hA (r⁻¹ • a) (A.smul_mem r⁻¹ ha)
    refine ⟨_, hmem, ?_⟩
    ext i j
    change (r⁻¹ * a i) * u (σ.symm j) = a i * ζ ^ j.val
    rw [huζ (σ.symm j), Equiv.apply_symm_apply]
    field_simp [hr]
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  let dft : Mat45 →ₗ[ℂ] (Fin 4 → Fin 4 → ℂ) :=
    { toFun := fun X r i => (1 / 5 : ℂ) * ∑ j : Fin 5, X i j * ζ ^ ((4 - r.val) * j.val)
      map_add' := fun X Y => by
        ext r i; simp [add_mul, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c X => by
        ext r i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have : ∀ j : Fin 5, c * X i j * ζ ^ ((4 - r.val) * j.val) =
            c * (X i j * ζ ^ ((4 - r.val) * j.val)) := fun _ => by ring
        simp_rw [this, ← Finset.mul_sum]; ring }
  have hdft_inv : ∀ (X : Mat45), (∀ i, ∑ j : Fin 5, X i j = 0) →
      ∀ i : Fin 4, ∀ k : Fin 5,
        (∑ r : Fin 4, dft X r i * ζ ^ ((r.val + 1) * k.val)) = X i k := by
    intro X hX i k
    simp only [dft, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (∑ r : Fin 4, (1 / 5 : ℂ) * (∑ j : Fin 5, X i j * ζ ^ ((4 - r.val) * j.val)) *
          ζ ^ ((r.val + 1) * k.val)) =
        (1 / 5 : ℂ) * ∑ j : Fin 5, X i j *
          (∑ r : Fin 4, ζ ^ ((4 - r.val) * j.val) * ζ ^ ((r.val + 1) * k.val)) := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ r : Fin 4, ∑ j : Fin 5, (1 / 5 : ℂ) * (X i j *
              (ζ ^ ((4 - r.val) * j.val) * ζ ^ ((r.val + 1) * k.val))) := by
          apply Finset.sum_congr rfl; intro r _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ j : Fin 5, ∑ r : Fin 4, (1 / 5 : ℂ) * (X i j *
              (ζ ^ ((4 - r.val) * j.val) * ζ ^ ((r.val + 1) * k.val))) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl; intro j _
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [h1]
    have hinner : ∀ j : Fin 5,
        (∑ r : Fin 4, ζ ^ ((4 - r.val) * j.val) * ζ ^ ((r.val + 1) * k.val)) =
          (if j = k then (5 : ℂ) else 0) - 1 := by
      intro j
      have hterm : ∀ r : Fin 4,
          ζ ^ ((4 - r.val) * j.val) * ζ ^ ((r.val + 1) * k.val) =
            ζ ^ ((5 - j.val + k.val) * (r.val + 1)) := by
        intro r
        rw [← pow_add]
        have hstep : (5 - j.val + k.val) * (r.val + 1) =
            (4 - r.val) * j.val + (r.val + 1) * k.val + 5 * (r.val + 1 - j.val) ∨
            (4 - r.val) * j.val + (r.val + 1) * k.val =
            (5 - j.val + k.val) * (r.val + 1) + 5 * (j.val - (r.val + 1)) := by
          have hr' := r.isLt; have hj' := j.isLt
          by_cases hle : j.val ≤ r.val + 1
          · left; zify [show r.val ≤ 4 by omega, show j.val ≤ 5 by omega, hle]; ring
          · right; zify [show r.val ≤ 4 by omega, show j.val ≤ 5 by omega, show r.val + 1 ≤ j.val by omega]; ring
        have h5pow : ∀ t : ℕ, ζ ^ (5 * t) = 1 := fun t => by rw [pow_mul, hζ5, one_pow]
        rcases hstep with h | h
        · rw [h, pow_add ζ ((4 - r.val) * j.val + (r.val + 1) * k.val), h5pow, mul_one]
        · rw [h, pow_add ζ ((5 - j.val + k.val) * (r.val + 1)), h5pow, mul_one]
      simp_rw [hterm]
      have hfull := geom5_sum hζ (5 - j.val + k.val)
      rw [Fin.sum_univ_five] at hfull
      rw [Fin.sum_univ_four]
      have hdvd_iff : 5 ∣ (5 - j.val + k.val) ↔ j = k := by
        constructor
        · intro hdvd
          have hj' := j.isLt; have hk' := k.isLt
          exact Fin.ext (by omega)
        · rintro rfl
          have hj' := j.isLt
          rw [show 5 - j.val + j.val = 5 by omega]
      rw [if_congr hdvd_iff rfl rfl] at hfull
      set m := 5 - j.val + k.val
      change ζ ^ (m * 0) + ζ ^ (m * 1) + ζ ^ (m * 2) + ζ ^ (m * 3) + ζ ^ (m * 4) = _ at hfull
      change ζ ^ (m * 1) + ζ ^ (m * 2) + ζ ^ (m * 3) + ζ ^ (m * 4) = _
      simp only [mul_zero, pow_zero] at hfull
      linear_combination hfull
    simp_rw [hinner, mul_sub, mul_ite, mul_zero, mul_one, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hX i, sub_zero]
    ring
  let L' : Submodule ℂ (Fin 4 → Fin 4 → ℂ) := L1.map dft
  have hL'_dim : Module.finrank ℂ L' = Module.finrank ℂ L1 := by
    have hinj : Function.Injective (dft.domRestrict L1) := by
      intro X Y h
      apply Subtype.ext; ext i k
      rw [← hdft_inv X.1 (hL1_val X.1 X.2).1 i k, ← hdft_inv Y.1 (hL1_val Y.1 Y.2).1 i k]
      have h' : dft X.1 = dft Y.1 := h
      rw [h']
    have h1 := LinearMap.finrank_range_of_inj hinj
    have hr' : LinearMap.range (dft.domRestrict L1) = L' := by ext x; simp [L']
    rw [hr'] at h1; exact h1
  have hL'_val : ∀ x ∈ L', (∀ r : Fin 4, (∑ i, x r i) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + ∑ r : Fin 4, x r i * ζ ^ ((r.val + 1) * (f i).val))) = 120 := by
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨fun r => ?_, ?_⟩
    · simp only [dft, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ j : Fin 5, (∑ i : Fin 4, X i j * ζ ^ ((4 - r.val) * j.val)) = 0 := fun j => by
        rw [← Finset.sum_mul, (hL1_val X hX).2.1 j, zero_mul]
      simp [this]
    · simp_rw [hdft_inv X (hL1_val X hX).1]
      exact (hL1_val X hX).2.2
  have hL'_A : ∀ a ∈ A, (fun r : Fin 4 => if r = 0 then a else 0) ∈ L' := by
    intro a ha
    refine ⟨fun i j => a i * ζ ^ j.val, hL1_A a ha, ?_⟩
    ext r i
    simp only [dft, LinearMap.coe_mk, AddHom.coe_mk]
    have hterm : ∀ j : Fin 5, a i * ζ ^ j.val * ζ ^ ((4 - r.val) * j.val) =
        a i * ζ ^ ((5 - r.val) * j.val) := fun j => by
      have hr' := r.isLt
      rw [mul_assoc, ← pow_add]
      congr 2; zify [show r.val ≤ 4 by omega, show r.val ≤ 5 by omega]; ring
    simp_rw [hterm, ← Finset.mul_sum, geom5_sum hζ]
    have hdvd_iff : 5 ∣ (5 - r.val) ↔ r = 0 := by
      have hr' := r.isLt
      constructor
      · intro hdvd; exact Fin.ext (by omega)
      · rintro rfl; simp
    rw [if_congr hdvd_iff rfl rfl]
    split_ifs <;> simp <;> ring
  have h5' : 5 ≤ Module.finrank ℂ L' := by omega
  rcases G284.main ζ hζ L' A hL'_val hL'_A hA_dim h5' with hx2 | hx3
  · let φ : (Fin 4 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → Fin 4 → ℂ) :=
      { toFun := fun x => ![x 1, x 3, x 0]
        map_add' := fun x y => by ext r i; fin_cases r <;> rfl
        map_smul' := fun c x => by ext r i; fin_cases r <;> rfl }
    let M : Submodule ℂ (Fin 3 → Fin 4 → ℂ) := L'.map φ
    have hM_dim : Module.finrank ℂ M = Module.finrank ℂ L' := by
      have hinj : Function.Injective (φ.domRestrict L') := by
        intro x y h
        apply Subtype.ext; ext r i
        fin_cases r
        · exact congrFun (congrFun h 2) i
        · exact congrFun (congrFun h 0) i
        · change x.1 2 i = y.1 2 i
          rw [hx2 x.1 x.2, hx2 y.1 y.2]
        · exact congrFun (congrFun h 1) i
      have h1 := LinearMap.finrank_range_of_inj hinj
      have hr' : LinearMap.range (φ.domRestrict L') = M := by ext z; simp [M]
      rw [hr'] at h1; exact h1
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) 5 := hζ.pow_of_coprime 2 (by decide)
    have hM_val : ∀ y ∈ M, (∀ r : Fin 3, (∑ i, y r i) = 0) ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
          (1 + y 0 i * (ζ ^ 2) ^ (f i).val + y 1 i * (ζ ^ 2) ^ (2 * (f i).val) +
            y 2 i * (ζ ^ 2) ^ (3 * (f i).val))) = 120 := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨fun r => ?_, ?_⟩
      · fin_cases r
        · exact (hL'_val x hx).1 1
        · exact (hL'_val x hx).1 3
        · exact (hL'_val x hx).1 0
      · rw [← (hL'_val x hx).2]
        apply Finset.sum_congr rfl; intro f _
        apply Finset.prod_congr rfl; intro i _
        rw [Fin.sum_univ_four, hx2 x hx]
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Pi.zero_apply, zero_mul, add_zero]
        have hp6 : (ζ ^ 2) ^ (3 * (f i).val) = ζ ^ (f i).val := by
          rw [← pow_mul, show 2 * (3 * (f i).val) = 5 * (f i).val + (f i).val by ring,
            pow_add, pow_mul, hζ5, one_pow, one_mul]
        have hp4' : (ζ ^ 2) ^ (2 * (f i).val) = ζ ^ (4 * (f i).val) := by
          rw [← pow_mul]; congr 1; ring
        have hp2' : (ζ ^ 2) ^ (f i).val = ζ ^ (2 * (f i).val) := by
          rw [← pow_mul]
        rw [hp6, hp4', hp2']
        change 1 + x 1 i * ζ ^ (2 * (f i).val) + x 3 i * ζ ^ (4 * (f i).val) + x 0 i * ζ ^ (f i).val =
          1 + (x 0 i * ζ ^ (1 * (f i).val) + x 1 i * ζ ^ (2 * (f i).val) + x 3 i * ζ ^ (4 * (f i).val))
        rw [one_mul]
        ring
    have hle4 := G280.main (ζ ^ 2) hζ2 M hM_val
    omega
  · let φ : (Fin 4 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → Fin 4 → ℂ) :=
      { toFun := fun x r => x r.castSucc
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let M : Submodule ℂ (Fin 3 → Fin 4 → ℂ) := L'.map φ
    have hM_dim : Module.finrank ℂ M = Module.finrank ℂ L' := by
      have hinj : Function.Injective (φ.domRestrict L') := by
        intro x y h
        apply Subtype.ext; ext r i
        fin_cases r
        · exact congrFun (congrFun h 0) i
        · exact congrFun (congrFun h 1) i
        · exact congrFun (congrFun h 2) i
        · change x.1 3 i = y.1 3 i
          rw [hx3 x.1 x.2, hx3 y.1 y.2]
      have h1 := LinearMap.finrank_range_of_inj hinj
      have hr' : LinearMap.range (φ.domRestrict L') = M := by ext z; simp [M]
      rw [hr'] at h1; exact h1
    have hM_val : ∀ y ∈ M, (∀ r : Fin 3, (∑ i, y r i) = 0) ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
          (1 + y 0 i * ζ ^ (f i).val + y 1 i * ζ ^ (2 * (f i).val) +
            y 2 i * ζ ^ (3 * (f i).val))) = 120 := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨fun r => (hL'_val x hx).1 r.castSucc, ?_⟩
      rw [← (hL'_val x hx).2]
      apply Finset.sum_congr rfl; intro f _
      apply Finset.prod_congr rfl; intro i _
      rw [Fin.sum_univ_four, hx3 x hx]
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_mul, add_zero]
      change 1 + x 0 i * ζ ^ (f i).val + x 1 i * ζ ^ (2 * (f i).val) +
          x 2 i * ζ ^ (3 * (f i).val) =
        1 + (x 0 i * ζ ^ (1 * (f i).val) + x 1 i * ζ ^ (2 * (f i).val) +
          x 2 i * ζ ^ (3 * (f i).val))
      rw [one_mul]
      ring
    have hle4 := G280.main ζ hζ M hM_val
    omega

theorem solve : ∀ (L : Submodule ℂ (Fin 4 → Fin 5 → ℂ))
    (u : Fin 5 → ℂ) (A : Submodule ℂ (Fin 4 → ℂ)),
    u ≠ 0 → 2 ≤ Module.finrank ℂ A →
    (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
    (∀ a ∈ A, (fun i j => a i * u j) ∈ L) →
    Module.finrank ℂ L ≤ 4 := by
  intro L u A hu hA_dim hL hA
  have hA_ne : ∃ a0 ∈ A, a0 ≠ 0 := by
    by_contra h; push Not at h
    have hbot : A = ⊥ := eq_bot_iff.2 (fun x hx => by rw [Submodule.mem_bot]; exact h x hx)
    rw [hbot, finrank_bot] at hA_dim; omega
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 5, u j0 ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  have hA_sum : ∀ a ∈ A, ∑ i : Fin 4, a i = 0 := by
    intro a ha
    have hc := (hL _ (hA a ha)).2.1 j0
    rw [← Finset.sum_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_right hj0
  have hu_sum : ∑ j : Fin 5, u j = 0 := by
    obtain ⟨a0, ha0, hne0⟩ := hA_ne
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 4, a0 i0 ≠ 0 := by
      by_contra h; push Not at h; exact hne0 (funext h)
    have hr := (hL _ (hA a0 ha0)).1 i0
    rw [← Finset.mul_sum] at hr
    exact (mul_eq_zero.mp hr).resolve_left hi0
  have hp2_u : ∑ j : Fin 5, (u j) ^ 2 = 0 := by
    obtain ⟨a, ha, ha2⟩ := exists_p2_ne_zero A hA_dim hA_sum
    have hq := (quad_cubic_of_L hL (hA a ha)).1
    have hfact : (∑ i : Fin 4, ∑ j : Fin 5, (a i * u j) ^ 2) =
        (∑ i : Fin 4, (a i) ^ 2) * (∑ j : Fin 5, (u j) ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hfact] at hq
    exact (mul_eq_zero.mp hq).resolve_left ha2
  by_cases hp3_u : ∑ j : Fin 5, (u j) ^ 3 = 0
  · by_cases hp4_u : ∑ j : Fin 5, (u j) ^ 4 = 0
    · exact case3_bound L u A hu hA_dim hu_sum hp2_u hp3_u hp4_u hL hA
    · have ha4 : ∀ a ∈ A, a 0 * a 1 * a 2 * a 3 = 0 := by
        intro a ha
        have he4 := (quad_cubic_of_L hL (hA a ha)).2.2
        unfold G306.e4 at he4
        have hr := (hL _ (hA a ha)).1
        rw [G306.e4_eq _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)] at he4
        have hdot : ∀ i1 i2 : Fin 4, G306.dot (fun j => a i1 * u j) (fun j => a i2 * u j) = 0 := by
          intro i1 i2
          unfold G306.dot
          have : ∀ j : Fin 5, a i1 * u j * (a i2 * u j) = (a i1 * a i2) * (u j) ^ 2 := fun _ => by ring
          simp_rw [this, ← Finset.mul_sum, hp2_u, mul_zero]
        rw [hdot 0 1, hdot 2 3, hdot 0 2, hdot 1 3, hdot 0 3, hdot 1 2] at he4
        have hfact : (∑ j : Fin 5, a 0 * u j * (a 1 * u j) * (a 2 * u j) * (a 3 * u j)) =
            (a 0 * a 1 * a 2 * a 3) * (∑ j : Fin 5, (u j) ^ 4) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        rw [hfact] at he4
        have hmul : (a 0 * a 1 * a 2 * a 3) * (∑ j : Fin 5, (u j) ^ 4) = 0 := by
          linear_combination -he4 / 6
        exact (mul_eq_zero.mp hmul).resolve_right hp4_u
      let coord : Fin 4 → (Fin 4 → ℂ) →ₗ[ℂ] ℂ := fun k =>
        { toFun := fun a => a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have hunion : ∀ a ∈ A, ∃ f ∈ [coord 0, coord 1, coord 2, coord 3], f a = 0 := by
        intro a ha
        have h4 := ha4 a ha
        rcases mul_eq_zero.mp h4 with h012 | h3
        · rcases mul_eq_zero.mp h012 with h01 | h2
          · rcases mul_eq_zero.mp h01 with h0 | h1
            · exact ⟨coord 0, by simp, h0⟩
            · exact ⟨coord 1, by simp, h1⟩
          · exact ⟨coord 2, by simp, h2⟩
        · exact ⟨coord 3, by simp, h3⟩
      obtain ⟨f, hf, hfall⟩ := subspace_union_avoid A [coord 0, coord 1, coord 2, coord 3] hunion
      have hex_k : ∃ k : Fin 4, ∀ a ∈ A, a k = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact ⟨0, hfall⟩
        · exact ⟨1, hfall⟩
        · exact ⟨2, hfall⟩
        · exact ⟨3, hfall⟩
      obtain ⟨k, hk⟩ := hex_k
      let τ : Equiv.Perm (Fin 4) := Equiv.swap k 3
      let L' : Submodule ℂ Mat45 := L.map (matRowPerm_equiv τ).toLinearMap
      let A' : Submodule ℂ (Fin 4 → ℂ) := A.map (rowPerm_equiv τ).toLinearMap
      have hL'_dim : Module.finrank ℂ L' = Module.finrank ℂ L :=
        finrank_map_equiv (matRowPerm_equiv τ) L
      have hA'_dim : Module.finrank ℂ A' = Module.finrank ℂ A :=
        finrank_map_equiv (rowPerm_equiv τ) A
      have hL'_val : ∀ X ∈ L', (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
          (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120 := by
        rintro _ ⟨X, hX, rfl⟩
        exact matRowPerm_valid τ X (hL X hX).1 (hL X hX).2.1 (hL X hX).2.2
      have hA'_in : ∀ a ∈ A', (fun i j => a i * u j) ∈ L' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨fun i j => a i * u j, hA a ha, rfl⟩
      let Q : Submodule ℂ (Fin 4 → ℂ) :=
        { carrier := {a | a 3 = 0 ∧ a 0 + a 1 + a 2 = 0}, add_mem' := fun {a b} ha hb => ⟨by change a 3 + b 3 = 0; rw [ha.1, hb.1, add_zero],
            by change (a 0 + b 0) + (a 1 + b 1) + (a 2 + b 2) = 0; linear_combination ha.2 + hb.2⟩
          zero_mem' := ⟨rfl, by change (0 : ℂ) + 0 + 0 = 0; ring⟩
          smul_mem' := fun c {a} ha => ⟨by change c * a 3 = 0; rw [ha.1, mul_zero],
            by change c * a 0 + c * a 1 + c * a 2 = 0; linear_combination c * ha.2⟩ }
      have hA'_le_Q : A' ≤ Q := by
        rintro _ ⟨a, ha, rfl⟩
        have h3 : rowPerm_equiv τ a 3 = 0 := by
          simp [rowPerm_equiv, τ, hk a ha]
        have hs : ∑ i : Fin 4, rowPerm_equiv τ a i = 0 := by
          simpa [rowPerm_equiv] using (Equiv.sum_comp τ a).trans (hA_sum a ha)
        rw [Fin.sum_univ_four, h3, add_zero] at hs
        exact ⟨h3, hs⟩
      have hQ_dim : Module.finrank ℂ Q ≤ 2 := by
        let proj : Q →ₗ[ℂ] (Fin 2 → ℂ) :=
          { toFun := fun a => ![a.1 0, a.1 1]
            map_add' := fun _ _ => by ext i; fin_cases i <;> rfl
            map_smul' := fun _ _ => by ext i; fin_cases i <;> rfl }
        have hinj : Function.Injective proj := by
          intro x y h
          apply Subtype.ext; ext i
          have h0 : x.1 0 = y.1 0 := congrFun h 0
          have h1 : x.1 1 = y.1 1 := congrFun h 1
          fin_cases i
          · exact h0
          · exact h1
          · change x.1 2 = y.1 2; linear_combination x.2.2 - y.2.2 - h0 - h1
          · change x.1 3 = y.1 3; rw [x.2.1, y.2.1]
        simpa [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hinj
      have hA'_eq_Q : A' = Q := Submodule.eq_of_le_of_finrank_eq hA'_le_Q (by
        have hle := Submodule.finrank_mono hA'_le_Q; omega)
      have hR : ∀ s t : ℂ, (fun i j => (![s, t, -s - t, 0] : Fin 4 → ℂ) i * u j) ∈ L' := by
        intro s t
        apply hA'_in
        rw [hA'_eq_Q]
        exact ⟨rfl, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring⟩
      rw [← hL'_dim]
      exact case2_bound L' u hp2_u hp4_u hL'_val hR
  · have ha3 : ∀ a ∈ A, (a 0 + a 1) * (a 0 + a 2) * (a 0 + a 3) = 0 := by
      intro a ha
      have hc3 := (quad_cubic_of_L hL (hA a ha)).2.1
      have hfact : (∑ i : Fin 4, ∑ j : Fin 5, (a i * u j) ^ 3) =
          (∑ i : Fin 4, (a i) ^ 3) * (∑ j : Fin 5, (u j) ^ 3) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [hfact] at hc3
      have ha_cub : ∑ i : Fin 4, (a i) ^ 3 = 0 := (mul_eq_zero.mp hc3).resolve_right hp3_u
      have hsum := hA_sum a ha
      rw [Fin.sum_univ_four] at ha_cub hsum
      have ha3' : a 3 = -(a 0 + a 1 + a 2) := by linear_combination hsum
      rw [ha3'] at ha_cub ⊢
      linear_combination ha_cub / 3
    let f01 : (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun a => a 0 + a 1, map_add' := fun _ _ => by simp only [Pi.add_apply]; ring,
        map_smul' := fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    let f02 : (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun a => a 0 + a 2, map_add' := fun _ _ => by simp only [Pi.add_apply]; ring,
        map_smul' := fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    let f03 : (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun a => a 0 + a 3, map_add' := fun _ _ => by simp only [Pi.add_apply]; ring,
        map_smul' := fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hunion : ∀ a ∈ A, ∃ f ∈ [f01, f02, f03], f a = 0 := by
      intro a ha
      rcases mul_eq_zero.mp (ha3 a ha) with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · exact ⟨f01, by simp, h1⟩
        · exact ⟨f02, by simp, h2⟩
      · exact ⟨f03, by simp, h3⟩
    obtain ⟨f, hf, hfall⟩ := subspace_union_avoid A [f01, f02, f03] hunion
    have hex_τ : ∃ τ : Equiv.Perm (Fin 4), ∀ a ∈ A, a (τ 0) + a (τ 1) = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact ⟨1, hfall⟩
      · exact ⟨Equiv.swap 1 2, fun a ha => by
          rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_left]
          exact hfall a ha⟩
      · exact ⟨Equiv.swap 1 3, fun a ha => by
          rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_left]
          exact hfall a ha⟩
    obtain ⟨τ, hτ⟩ := hex_τ
    let L' : Submodule ℂ Mat45 := L.map (matRowPerm_equiv τ).toLinearMap
    let A' : Submodule ℂ (Fin 4 → ℂ) := A.map (rowPerm_equiv τ).toLinearMap
    have hL'_dim : Module.finrank ℂ L' = Module.finrank ℂ L :=
      finrank_map_equiv (matRowPerm_equiv τ) L
    have hA'_dim : Module.finrank ℂ A' = Module.finrank ℂ A :=
      finrank_map_equiv (rowPerm_equiv τ) A
    have hL'_val : ∀ X ∈ L', (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120 := by
      rintro _ ⟨X, hX, rfl⟩
      exact matRowPerm_valid τ X (hL X hX).1 (hL X hX).2.1 (hL X hX).2.2
    have hA'_in : ∀ a ∈ A', (fun i j => a i * u j) ∈ L' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨fun i j => a i * u j, hA a ha, rfl⟩
    let P : Submodule ℂ (Fin 4 → ℂ) :=
      { carrier := {a | a 0 + a 1 = 0 ∧ a 2 + a 3 = 0}, add_mem' := fun {a b} ha hb => ⟨by change (a 0 + b 0) + (a 1 + b 1) = 0; linear_combination ha.1 + hb.1,
          by change (a 2 + b 2) + (a 3 + b 3) = 0; linear_combination ha.2 + hb.2⟩
        zero_mem' := ⟨by change (0 : ℂ) + 0 = 0; ring, by change (0 : ℂ) + 0 = 0; ring⟩
        smul_mem' := fun c {a} ha => ⟨by change c * a 0 + c * a 1 = 0; linear_combination c * ha.1,
          by change c * a 2 + c * a 3 = 0; linear_combination c * ha.2⟩ }
    have hA'_le_P : A' ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      have h01 : rowPerm_equiv τ a 0 + rowPerm_equiv τ a 1 = 0 := hτ a ha
      have hs : ∑ i : Fin 4, rowPerm_equiv τ a i = 0 := by
        simpa [rowPerm_equiv] using (Equiv.sum_comp τ a).trans (hA_sum a ha)
      rw [Fin.sum_univ_four] at hs
      exact ⟨h01, by linear_combination hs - h01⟩
    have hP_dim : Module.finrank ℂ P ≤ 2 := by
      let proj : P →ₗ[ℂ] (Fin 2 → ℂ) :=
        { toFun := fun a => ![a.1 0, a.1 2]
          map_add' := fun _ _ => by ext i; fin_cases i <;> rfl
          map_smul' := fun _ _ => by ext i; fin_cases i <;> rfl }
      have hinj : Function.Injective proj := by
        intro x y h
        apply Subtype.ext; ext i
        have h0 : x.1 0 = y.1 0 := congrFun h 0
        have h2 : x.1 2 = y.1 2 := congrFun h 1
        fin_cases i
        · exact h0
        · change x.1 1 = y.1 1; linear_combination x.2.1 - y.2.1 - h0
        · exact h2
        · change x.1 3 = y.1 3; linear_combination x.2.2 - y.2.2 - h2
      simpa [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hinj
    have hA'_eq_P : A' = P := Submodule.eq_of_le_of_finrank_eq hA'_le_P (by
      have hle := Submodule.finrank_mono hA'_le_P; omega)
    have hR : ∀ s t : ℂ, (fun i j => (![s, -s, t, -t] : Fin 4 → ℂ) i * u j) ∈ L' := by
      intro s t
      apply hA'_in
      rw [hA'_eq_P]
      exact ⟨by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring,
        by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring⟩
    have hp4_u : ∑ j : Fin 5, (u j) ^ 4 = 0 := by
      have h11 : (fun i j => (![1, -1, 1, -1] : Fin 4 → ℂ) i * u j) ∈ L' := hR 1 1
      have he4 := (quad_cubic_of_L hL'_val h11).2.2
      unfold G306.e4 at he4
      have hr := (hL'_val _ h11).1
      rw [G306.e4_eq _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)] at he4
      have hdot : ∀ i1 i2 : Fin 4,
          G306.dot (fun j => (![1, -1, 1, -1] : Fin 4 → ℂ) i1 * u j)
                   (fun j => (![1, -1, 1, -1] : Fin 4 → ℂ) i2 * u j) = 0 := by
        intro i1 i2; unfold G306.dot
        have : ∀ j : Fin 5, (![1, -1, 1, -1] : Fin 4 → ℂ) i1 * u j *
            ((![1, -1, 1, -1] : Fin 4 → ℂ) i2 * u j) =
          ((![1, -1, 1, -1] : Fin 4 → ℂ) i1 * (![1, -1, 1, -1] : Fin 4 → ℂ) i2) * (u j) ^ 2 :=
          fun _ => by ring
        simp_rw [this, ← Finset.mul_sum, hp2_u, mul_zero]
      rw [hdot 0 1, hdot 2 3, hdot 0 2, hdot 1 3, hdot 0 3, hdot 1 2] at he4
      have hfact : (∑ j : Fin 5,
          (![1, -1, 1, -1] : Fin 4 → ℂ) 0 * u j * ((![1, -1, 1, -1] : Fin 4 → ℂ) 1 * u j) *
          ((![1, -1, 1, -1] : Fin 4 → ℂ) 2 * u j) * ((![1, -1, 1, -1] : Fin 4 → ℂ) 3 * u j)) =
          ∑ j : Fin 5, (u j) ^ 4 := by
        apply Finset.sum_congr rfl; intro j _
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      rw [hfact] at he4
      linear_combination -he4 / 6
    obtain ⟨hdet, hcontra⟩ := case1_contra u hu_sum hp2_u hp3_u hp4_u
    have hL'_val306 : ∀ X ∈ L', (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) =
          (∑ _f : Fin 4 ↪ Fin 5, (1 : ℂ)) := by
      intro X hX
      refine ⟨(hL'_val X hX).1, (hL'_val X hX).2.1, ?_⟩
      change _ = G306.e0 5
      rw [e0_five]
      exact (hL'_val X hX).2.2
    have h306 := G306.main 5 (by norm_num) u L' (by simpa using hu_sum) hp2_u hp4_u
      (by simpa using hdet) hL'_val306 hR
    by_contra hgt
    have hgt' : ¬ Module.finrank ℂ L' ≤ 4 := by rwa [hL'_dim]
    have hle5 : 2 * Module.finrank ℂ L' + 5 ≤ 3 * 5 := h306.1
    have heq5 : 2 * Module.finrank ℂ L' + 5 = 3 * 5 := by omega
    obtain ⟨h8, h12⟩ := h306.2 heq5
    exact hcontra h8 (by simpa using h12)

end Finish

end PEqualNP.Outside.L_gct_307

theorem PEqualNP.Outside.L_gct_307 : (∀ (L : Submodule ℂ (Fin 4 → Fin 5 → ℂ))
  (u : Fin 5 → ℂ) (A : Submodule ℂ (Fin 4 → ℂ)),
  u ≠ 0 → 2 ≤ Module.finrank ℂ A →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
  (∀ a ∈ A, (fun i j => a i * u j) ∈ L) →
  Module.finrank ℂ L ≤ 4) :=
  PEqualNP.Outside.L_gct_307.Finish.solve
