import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_889

open Finset

def eps (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem two0 : (2 : ZMod 2) = 0 := by decide

@[simp] theorem eps_zero : eps 0 = 1 := rfl
@[simp] theorem eps_one : eps 1 = -1 := rfl

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  rcases z2 a with h | h <;> rcases z2 b with h' | h' <;> subst h <;> subst h' <;> rfl

theorem eq_iff_add : ∀ x y : ZMod 2, x = y ↔ x + y = 0 := by decide

theorem sum_eps_add {G : Type*} [AddCommGroup G] [Fintype G] (φ : G → ZMod 2)
    (hφ : ∀ a b, φ (a + b) = φ a + φ b) :
    ∑ g, eps (φ g) = if ∀ g, φ g = 0 then (Fintype.card G : ℤ) else 0 := by
  split_ifs with h
  · simp [h, eps, Finset.card_univ]
  · push Not at h
    obtain ⟨g0, hg0⟩ := h
    have h1 : φ g0 = 1 := by
      rcases z2 (φ g0) with e | e
      · exact absurd e hg0
      · exact e
    have key := Fintype.sum_equiv (Equiv.addRight g0)
      (fun g => eps (φ (g + g0))) (fun g => eps (φ g)) (fun _ => rfl)
    simp only [hφ, h1, eps_add, eps_one, mul_neg, mul_one, Finset.sum_neg_distrib] at key
    linarith

theorem sum_eps_dot {n : ℕ} (c : Fin n → ZMod 2) :
    ∑ u : Fin n → ZMod 2, eps (u ⬝ᵥ c) = if c = 0 then 2 ^ n else 0 := by
  rw [sum_eps_add (fun u => u ⬝ᵥ c) (fun a b => add_dotProduct a b c)]
  have hc : (Fintype.card (Fin n → ZMod 2) : ℤ) = 2 ^ n := by
    simp [Fintype.card_fun, ZMod.card]
  have hiff : (∀ u : Fin n → ZMod 2, u ⬝ᵥ c = 0) ↔ c = 0 := by
    constructor
    · intro h; funext i
      have := h (Pi.single i 1)
      simpa [single_dotProduct] using this
    · intro h u; simp [h]
  by_cases h : c = 0
  · rw [if_pos (hiff.2 h), if_pos h, hc]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

section main

variable {l r s : ℕ}

abbrev U (l : ℕ) := Fin l → ZMod 2

def S (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s) (b : U s)
    (α : U s) : ℤ :=
  ∑ x : U l, ∑ y : U r, eps (α ⬝ᵥ (B x y + A (x, y) + b))

theorem A_split (A : (U l × U r) →ₗ[ZMod 2] U s) (x : U l) (y : U r) :
    A (x, y) = A (x, 0) + A (0, y) := by
  rw [← map_add]; simp

theorem count_eq (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s))
    (A : (U l × U r) →ₗ[ZMod 2] U s) (b : U s) :
    (2 : ℤ) ^ s * (((Finset.univ : Finset (U l × U r)).filter
      (fun p => B p.1 p.2 = A p + b)).card : ℤ) = ∑ α, S B A b α := by
  simp only [S]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (U s)))]
  simp_rw [sum_eps_dot]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  have hiff : B x y = A (x, y) + b ↔ B x y + A (x, y) + b = 0 := by
    constructor
    · intro h; rw [h]; funext i; simp only [Pi.add_apply, Pi.zero_apply]
      linear_combination (A (x, y) i + b i) * two0
    · intro h; funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Pi.add_apply]
      linear_combination this - (A (x, y) i + b i) * two0
  by_cases h : B x y = A (x, y) + b
  · rw [if_pos h, if_pos (hiff.1 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; simp

/-- The left linear map u ↦ (y ↦ α ⬝ B u y). -/
def Phi (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (α : U s) :
    U l →ₗ[ZMod 2] (U r → ZMod 2) where
  toFun u := fun y => α ⬝ᵥ B u y
  map_add' a c := by funext y; simp [dotProduct_add]
  map_smul' a c := by funext y; simp [dotProduct_smul]

theorem S00 (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (α : U s) :
    S B 0 0 α = 2 ^ (l + r - Module.finrank (ZMod 2) (LinearMap.range (Phi B α))) := by
  classical
  simp only [S, LinearMap.zero_apply, add_zero]
  have inner : ∀ x : U l, ∑ y : U r, eps (α ⬝ᵥ B x y) =
      if Phi B α x = 0 then (2 : ℤ) ^ r else 0 := by
    intro x
    rw [sum_eps_add (fun y => α ⬝ᵥ B x y) (fun a c => by simp [dotProduct_add])]
    have hc : (Fintype.card (U r) : ℤ) = 2 ^ r := by
      simp [Fintype.card_fun, ZMod.card]
    have hiff : (∀ y : U r, α ⬝ᵥ B x y = 0) ↔ Phi B α x = 0 := by
      constructor
      · intro h; funext y; exact h y
      · intro h y; exact congrFun h y
    by_cases h : Phi B α x = 0
    · rw [if_pos (hiff.2 h), if_pos h, hc]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  simp_rw [inner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h1 : ((univ.filter (fun x : U l => Phi B α x = 0)).card) =
      Fintype.card (LinearMap.ker (Phi B α)) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by simp))
  have h2 : Fintype.card (LinearMap.ker (Phi B α)) =
      2 ^ (Module.finrank (ZMod 2) (LinearMap.ker (Phi B α))) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have h3 := (Phi B α).finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h3
  rw [h1, h2]
  push_cast
  rw [← pow_add]
  congr 1
  omega

def P (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s) (α : U s)
    (p : U l) : Prop := ∀ v : U r, α ⬝ᵥ A (0, v) = α ⬝ᵥ B p v

def Q (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s) (α : U s)
    (q : U r) : Prop := ∀ u : U l, α ⬝ᵥ A (u, 0) = α ⬝ᵥ B u q

theorem S_noP (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s)
    (b : U s) (α : U s) (h : ∀ p, ¬ P B A α p) : S B A b α = 0 := by
  simp only [S]
  apply Finset.sum_eq_zero; intro x _
  have e : ∀ y, eps (α ⬝ᵥ (B x y + A (x, y) + b)) =
      eps (α ⬝ᵥ A (x, 0) + α ⬝ᵥ b) * eps (α ⬝ᵥ B x y + α ⬝ᵥ A (0, y)) := by
    intro y; rw [← eps_add, A_split]; congr 1
    simp only [dotProduct_add]; ring
  simp_rw [e, ← Finset.mul_sum]
  rw [sum_eps_add (fun y => α ⬝ᵥ B x y + α ⬝ᵥ A (0, y))]
  · rw [if_neg, mul_zero]
    intro hall; apply h x; intro v
    have := hall v
    linear_combination this - (α ⬝ᵥ B x v) * two0
  · intro a c
    have : ((0 : U l), a + c) = ((0 : U l), a) + (0, c) := by simp
    rw [map_add, this, map_add]; simp only [dotProduct_add]; ring

theorem S_noQ (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s)
    (b : U s) (α : U s) (h : ∀ q, ¬ Q B A α q) : S B A b α = 0 := by
  simp only [S]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro y _
  have e : ∀ x, eps (α ⬝ᵥ (B x y + A (x, y) + b)) =
      eps (α ⬝ᵥ A (0, y) + α ⬝ᵥ b) * eps (α ⬝ᵥ B x y + α ⬝ᵥ A (x, 0)) := by
    intro x; rw [← eps_add, A_split]; congr 1
    simp only [dotProduct_add]; ring
  simp_rw [e, ← Finset.mul_sum]
  rw [sum_eps_add (fun x => α ⬝ᵥ B x y + α ⬝ᵥ A (x, 0))]
  · rw [if_neg, mul_zero]
    intro hall; apply h y; intro u
    have := hall u
    linear_combination this - (α ⬝ᵥ B u y) * two0
  · intro a c
    have : (a + c, (0 : U r)) = (a, (0 : U r)) + (c, 0) := by simp
    rw [map_add, LinearMap.add_apply, this, map_add]; simp only [dotProduct_add]; ring

theorem S_PQ (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s)
    (b : U s) (α : U s) (p : U l) (q : U r) (hp : P B A α p) (hq : Q B A α q) :
    S B A b α = eps (α ⬝ᵥ b + α ⬝ᵥ B p q) * S B 0 0 α := by
  simp only [S, LinearMap.zero_apply, add_zero]
  rw [Finset.mul_sum]
  rw [← Fintype.sum_equiv (Equiv.addRight p) (fun x => ∑ y : U r,
    eps (α ⬝ᵥ (B (x + p) y + A (x + p, y) + b))) _ (fun _ => rfl)]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  rw [← Fintype.sum_equiv (Equiv.addRight q) (fun y =>
    eps (α ⬝ᵥ (B (x + p) (y + q) + A (x + p, y + q) + b))) _ (fun _ => rfl)]
  apply Finset.sum_congr rfl; intro y _
  rw [← eps_add]; congr 1
  rw [A_split, dotProduct_add, dotProduct_add, dotProduct_add, hp, hq]
  simp only [map_add, LinearMap.add_apply, dotProduct_add]
  linear_combination (α ⬝ᵥ B x q + α ⬝ᵥ B p y + α ⬝ᵥ B p q) * two0

theorem S00_pos (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (α : U s) : 0 < S B 0 0 α := by
  rw [S00]; positivity

theorem S_cases (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (A : (U l × U r) →ₗ[ZMod 2] U s)
    (b : U s) (α : U s) :
    S B A b α ≤ S B 0 0 α ∧ (S B A b α = S B 0 0 α ↔ ∃ (p : U l) (q : U r),
      Q B A α q ∧ P B A α p ∧ α ⬝ᵥ b = α ⬝ᵥ B p q) := by
  have hpos := S00_pos B α
  by_cases hP : ∃ p, P B A α p
  · by_cases hQ : ∃ q, Q B A α q
    · obtain ⟨p, hp⟩ := hP
      obtain ⟨q, hq⟩ := hQ
      rw [S_PQ B A b α p q hp hq]
      rcases z2 (α ⬝ᵥ b + α ⬝ᵥ B p q) with e | e
      · rw [e, eps_zero, one_mul]
        refine ⟨le_rfl, ?_⟩
        simp only [true_iff]
        exact ⟨p, q, hq, hp, (eq_iff_add _ _).2 e⟩
      · rw [e, eps_one]
        refine ⟨by linarith, ?_⟩
        constructor
        · intro h; linarith
        · rintro ⟨p', q', hq', hp', he⟩
          exfalso
          -- the sign is independent of the choice of p, q
          have h2 := S_PQ B A b α p' q' hp' hq'
          have h1 := S_PQ B A b α p q hp hq
          rw [e, eps_one] at h1
          rw [(eq_iff_add _ _).1 he, eps_zero, one_mul] at h2
          rw [h1] at h2; linarith
    · push Not at hQ
      rw [S_noQ B A b α hQ]
      refine ⟨hpos.le, ?_⟩
      constructor
      · intro h; linarith
      · rintro ⟨p, q, hq, -, -⟩; exact absurd hq (hQ q)
  · push Not at hP
    rw [S_noP B A b α hP]
    refine ⟨hpos.le, ?_⟩
    constructor
    · intro h; linarith
    · rintro ⟨p, q, -, hp, -⟩; exact absurd hp (hP p)

theorem rank_eq (B : U l →ₗ[ZMod 2] (U r →ₗ[ZMod 2] U s)) (α : U s) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun u : U l => fun y : U r => α ⬝ᵥ B u y))) =
    Module.finrank (ZMod 2) (LinearMap.range (Phi B α)) := by
  have : Set.range (fun u : U l => fun y : U r => α ⬝ᵥ B u y) =
      ((LinearMap.range (Phi B α) : Submodule (ZMod 2) (U r → ZMod 2)) : Set (U r → ZMod 2)) := by
    rw [LinearMap.coe_range]; rfl
  rw [this, Submodule.span_eq]

end main

end PEqualNP.Outside.L_lib_889

open PEqualNP.Outside.L_lib_889 in
theorem PEqualNP.Outside.L_lib_889 : ∀ (l r s : Nat),
  let F := ZMod 2
  let U := Fin l → F
  let V := Fin r → F
  let Z := Fin s → F
  ∀ B : U →ₗ[F] (V →ₗ[F] Z),
    let scalar := fun (a : Z) (x : U) (y : V) => dotProduct a (B x y)
    let rank := fun frequency : Z =>
      Module.finrank F (Submodule.span F (Set.range (fun u : U => scalar frequency u)))
    let hits := fun (L : (U × V) →ₗ[F] Z) (c : Z) =>
      ((Finset.univ : Finset (U × V)).filter (fun p => B p.1 p.2 = L p + c)).card
    2^s * hits 0 0 = (∑ mask : Z, 2^(l+r-rank mask)) ∧
    ∀ (A : (U × V) →ₗ[F] Z) (b : Z),
      hits A b ≤ hits 0 0 ∧
      (hits A b = hits 0 0 ↔ ∀ α : Z, ∃ (p : U) (q : V),
        (∀ u : U, dotProduct α (A (u,0)) = scalar α u q) ∧
        (∀ v : V, dotProduct α (A (0,v)) = scalar α p v) ∧
        dotProduct α b = scalar α p q) := by
  intro l r s F U V Z B scalar rank hits
  have hc : ∀ A b, ((2 : ℤ) ^ s * (hits A b : ℤ)) = ∑ α, S B A b α := fun A b => count_eq B A b
  have h00 : ∀ α : Z, S B 0 0 α = ((2 ^ (l + r - rank α) : ℕ) : ℤ) := by
    intro α; rw [S00]; simp only [rank, scalar]; rw [rank_eq]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · have := hc 0 0
    simp_rw [h00] at this
    exact_mod_cast this
  · intro A b
    have hle : (hits A b : ℤ) ≤ hits 0 0 := by
      have h1 := hc A b
      have h2 := hc 0 0
      have : ∑ α, S B A b α ≤ ∑ α, S B 0 0 α :=
        Finset.sum_le_sum (fun α _ => (S_cases B A b α).1)
      have hp : (0 : ℤ) < 2 ^ s := by positivity
      nlinarith
    refine ⟨by exact_mod_cast hle, ?_⟩
    have hp : (0 : ℤ) < 2 ^ s := by positivity
    constructor
    · intro heq α
      have hsum : ∑ α, S B A b α = ∑ α, S B 0 0 α := by
        rw [← hc, ← hc, heq]
      have := (Finset.sum_eq_sum_iff_of_le (fun α _ => (S_cases B A b α).1)).1 hsum α
        (Finset.mem_univ _)
      obtain ⟨p, q, hq, hp, he⟩ := (S_cases B A b α).2.1 this
      exact ⟨p, q, hq, hp, he⟩
    · intro h
      have hsum : ∑ α, S B A b α = ∑ α, S B 0 0 α := by
        apply Finset.sum_congr rfl; intro α _
        obtain ⟨p, q, hq, hp, he⟩ := h α
        exact (S_cases B A b α).2.2 ⟨p, q, hq, hp, he⟩
      have h1 := hc A b
      have h2 := hc 0 0
      have : (2 : ℤ) ^ s * hits A b = 2 ^ s * hits 0 0 := by rw [h1, h2, hsum]
      have := mul_left_cancel₀ hp.ne' this
      exact_mod_cast this
