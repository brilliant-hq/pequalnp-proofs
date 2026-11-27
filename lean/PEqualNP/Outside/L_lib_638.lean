import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_638_aux

theorem s_add (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (b c : ZMod 2) :
    s (b + c) = s b * s c := by
  rw [hs, hs, hs]
  fin_cases b <;> fin_cases c <;> decide

theorem char_sum (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (z : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a z) = if z = 0 then (2 : ℤ) ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp only [dotProduct_zero, hs, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    have hzi : z i = 1 := by
      have h2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      exact h2 _ hi
    let e : Fin n → ZMod 2 := Pi.single i 1
    have hez : dotProduct e z = 1 := by
      simp only [e, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hzi]
    have key : ∀ a : Fin n → ZMod 2, s (dotProduct (a + e) z) = - s (dotProduct a z) := by
      intro a
      rw [add_dotProduct, s_add s hs, hez, hs 1]
      simp
    have h := Fintype.sum_equiv (Equiv.addRight e) (fun a => s (dotProduct (a + e) z))
      (fun a => s (dotProduct a z)) (fun a => rfl)
    simp only [key, Finset.sum_neg_distrib] at h
    linarith

theorem ortho (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (x y : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) =
      if x = y then (2 : ℤ) ^ n else 0 := by
  have h1 : ∀ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) = s (dotProduct a (x + y)) := by
    intro a
    rw [dotProduct_add, s_add s hs]
  simp only [h1]
  rw [char_sum s hs n (x + y)]
  have h2 : ∀ t u : ZMod 2, t + u = 0 ↔ t = u := by decide
  have h3 : (x + y = 0) ↔ (x = y) := by
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h2]
  simp only [h3]

def sg (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

def W {n : ℕ} (h : (Fin n → ZMod 2) → ℤ) (a : Fin n → ZMod 2) : ℤ := ∑ x, h x * sg (dotProduct a x)

lemma invW {n : ℕ} (f : (Fin n → ZMod 2) → ℤ) (y : Fin n → ZMod 2) : W (W f) y = (2:ℤ)^n * f y := by
  let V := Fin n → ZMod 2
  let sign := sg
  have hs : ∀ b, sign b = if b = 0 then 1 else -1 := fun b => rfl
  have P1 : ∀ y : V, W (W f) y = (2:ℤ)^n * f y := by
    intro y
    show ∑ a : V, (∑ x : V, f x * sign (dotProduct a x)) * sign (dotProduct y a) = _
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have inner : ∀ x : V, ∑ a : V, f x * sign (dotProduct a x) * sign (dotProduct y a) =
        f x * (if x = y then (2:ℤ)^n else 0) := by
      intro x
      rw [← ortho sign hs n x y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [dotProduct_comm y a]
      ring
    simp only [inner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  exact P1 y

noncomputable def mask {d : ℕ} (U : Submodule (ZMod 2) (Fin d → ZMod 2)) (z a : Fin d → ZMod 2) : ℤ := by
  classical
  exact if a ∈ U then sg (dotProduct a z) else 0

lemma maskW {d : ℕ} (U : Submodule (ZMod 2) (Fin d → ZMod 2)) (z x : Fin d → ZMod 2) :
    W (mask U z) x = @ite ℤ (∀ a ∈ U, dotProduct a x = dotProduct a z) (Classical.propDecidable _) ((2:ℤ)^Module.finrank (ZMod 2) U) 0 := by
  classical
  let v := x+z
  have key (a : Fin d → ZMod 2) : mask U z a * sg (dotProduct x a) = if a ∈ U then sg (dotProduct a v) else 0 := by
    rw [dotProduct_comm x a]; unfold mask; split_ifs <;> simp [v, dotProduct_add, s_add sg (fun _ => rfl), mul_comm]
  simp only [W, key]
  have iff0 (a : Fin d → ZMod 2) : dotProduct a v = 0 ↔ dotProduct a x = dotProduct a z := by
    rw [show dotProduct a v = dotProduct a x + dotProduct a z from dotProduct_add ..]
    exact (show ∀ b c : ZMod 2, b+c=0 ↔ b=c by decide) _ _
  by_cases h : ∀ a ∈ U, dotProduct a x = dotProduct a z
  · rw [if_pos h]
    have k (a : Fin d → ZMod 2) : (if a ∈ U then sg (dotProduct a v) else 0) = (if a ∈ U then (1:ℤ) else 0) := by
      split_ifs with ha; simp [sg, (iff0 a).2 (h a ha)]; rfl
    simp_rw [k]
    have cardU : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    simpa [Finset.sum_boole, Fintype.card_subtype] using (show (Fintype.card U : ℤ) = (2:ℤ)^Module.finrank (ZMod 2) U by exact_mod_cast cardU)
  · rw [if_neg h]; push_neg at h
    obtain ⟨e, he, hn⟩ := h
    let q := fun a : Fin d → ZMod 2 => if a ∈ U then sg (dotProduct a v) else 0
    have hev : dotProduct e v ≠ 0 := fun heq => hn ((iff0 e).1 heq)
    have he' : sg (dotProduct e v) = -1 := by simp [sg, hev]
    have shift (a) : q (a+e) = -q a := by
      simp only [q, U.add_mem_iff_left he, add_dotProduct, s_add sg (fun _ => rfl), he']; split_ifs <;> ring
    have hs := Fintype.sum_equiv (Equiv.addRight e) (fun a => q (a+e)) q (fun _ => rfl)
    simp only [shift, Finset.sum_neg_distrib] at hs
    change (∑ a, q a) = 0; omega

lemma coeff {d : ℕ} (F : (Fin d → ZMod 2) → ℕ) (z : Fin d → ZMod 2) (hz : 0 < F z)
    (N : ℤ) (ht : ∑ x, (F x : ℤ) = N) (a : Fin d → ZMod 2) (hd : N ∣ W (fun x => (F x : ℤ)) a)
    (hbad : ¬∀ x, 0 < F x → dotProduct a x = dotProduct a z) : W (fun x => (F x : ℤ)) a = 0 := by
  classical
  push_neg at hbad
  obtain ⟨w, hw, hn⟩ := hbad
  let f := fun x => (F x:ℤ)*sg (dotProduct a x)
  have sgcases (x) : sg (dotProduct a x) = 1 ∨ sg (dotProduct a x) = -1 := by unfold sg; split <;> simp
  have hop : sg (dotProduct a w) ≠ sg (dotProduct a z) := by
    exact fun heq => hn ((show Function.Injective sg by decide) heq)
  have plus : ∃ x, 0 < F x ∧ sg (dotProduct a x) = 1 := by rcases sgcases w with h|h <;> rcases sgcases z with h'|h' <;> first | exact ⟨w,hw,h⟩ | exact ⟨z,hz,h'⟩ | simp_all
  have minus : ∃ x, 0 < F x ∧ sg (dotProduct a x) = -1 := by rcases sgcases w with h|h <;> rcases sgcases z with h'|h' <;> first | exact ⟨w,hw,h⟩ | exact ⟨z,hz,h'⟩ | simp_all
  obtain ⟨u, hu, su⟩ := plus; obtain ⟨v, hv, sv⟩ := minus
  have ltN : ∑ x, f x < N := by
    rw [← ht]; apply Finset.sum_lt_sum
    · intro x _; rcases sgcases x with hs|hs <;> simp [f, hs]
    · exact ⟨v, Finset.mem_univ _, by simp [f, sv]; omega⟩
  have gtN : -N < ∑ x, f x := by
    rw [← ht, ← Finset.sum_neg_distrib]; apply Finset.sum_lt_sum
    · intro x _; rcases sgcases x with hs|hs <;> simp [f, hs]
    · exact ⟨u, Finset.mem_univ _, by simp [f, su]; omega⟩
  change N ∣ ∑ x, f x at hd
  change (∑ x, f x) = 0
  obtain ⟨k,hk⟩ := hd
  have hn' : 0 < N := by omega
  rcases lt_trichotomy k 0 with h|h|h
  · have hk' : k ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hk' hn'.le]
  · simp [hk,h]
  · have hk' : 1 ≤ k := by omega
    nlinarith [mul_le_mul_of_nonneg_left hk' hn'.le]

end PEqualNP.Outside.L_lib_638_aux

open PEqualNP.Outside.L_lib_638_aux

theorem PEqualNP.Outside.L_lib_638 : ∀ d : ℕ,
  let V := Fin d → ZMod 2
  let dot := fun (a x : V) => ∑ i, a i * x i
  let spin := fun (a x : V) => if dot a x = 0 then (1 : ℤ) else -1
  ∀ F : V → ℕ, (∑ x, F x) = 2^d →
    ((∀ a : V, (2^d : ℤ) ∣ ∑ x : V, (F x : ℤ) * spin a x) ↔
      ∃ (U : Submodule (ZMod 2) V) (z : V),
        ∀ x : V, F x = @ite ℕ (∀ a ∈ U, dot a x = dot a z)
          (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0) := by
  classical
  intro d V dot spin F hsum
  let f : V → ℤ := fun x => F x
  let N : ℤ := 2^d
  have hn : 0 < N := by dsimp [N]; positivity
  have ht : ∑ x, (F x : ℤ) = N := by dsimp [N]; exact_mod_cast hsum
  constructor
  · intro hdiv
    obtain ⟨z,hz⟩ : ∃ z, 0 < F z := by
      by_contra! h
      have hall (x) : F x = 0 := by simpa using h x
      simp [hall] at hsum
      exact (pow_ne_zero d (by decide : (2:ℕ) ≠ 0)) hsum.symm
    let P := fun a : V => ∀ x, 0 < F x → dotProduct a x = dotProduct a z
    have hzero : P 0 := by simp [P]
    have hadd {a b : V} (ha : P a) (hb : P b) : P (a+b) := by
      intro x hx
      exact (add_dotProduct a b x).trans ((congrArg₂ (· + ·) (ha x hx) (hb x hx)).trans (add_dotProduct a b z).symm)
    have hsmul (c : ZMod 2) {a : V} (ha : P a) : P (c • a) := by
      intro x hx
      exact (smul_dotProduct c a x).trans ((congrArg (c • ·) (ha x hx)).trans (smul_dotProduct c a z).symm)
    let U : Submodule (ZMod 2) V := { carrier := {a | P a}, zero_mem' := hzero, add_mem' := hadd, smul_mem' := hsmul }
    refine ⟨U,z,fun x => ?_⟩
    have hW : W f = fun a => N * mask U z a := by
      funext a
      by_cases h : a ∈ U
      · have key (y) : (F y : ℤ)*sg (dotProduct a y) = (F y : ℤ)*sg (dotProduct a z) := by
          by_cases hpos : 0 < F y
          · rw [(show ∀ t, 0 < F t → dotProduct a t = dotProduct a z from h) y hpos]
          · simp [show F y = 0 by omega]
        simp only [W, f, mask, if_pos h, key, ← Finset.sum_mul]
        exact congrArg (· * sg (dotProduct a z)) ht
      · have k := coeff F z hz N ht a (hdiv a) h
        simpa only [mask, if_neg h, mul_zero] using k
    have hh := invW f x
    rw [hW] at hh
    have hscale : W (fun a => N * mask U z a) x = N * W (mask U z) x := by simp [W, Finset.mul_sum, mul_assoc]
    rw [hscale] at hh
    have hx : (F x : ℤ) = W (mask U z) x := by change f x = _; nlinarith [hh]
    rw [maskW] at hx
    by_cases h : ∀ a ∈ U, dotProduct a x = dotProduct a z
    · rw [if_pos h] at hx; rw [if_pos (show ∀ a ∈ U, dot a x = dot a z from h)]; exact_mod_cast hx
    · rw [if_neg h] at hx; rw [if_neg (show ¬∀ a ∈ U, dot a x = dot a z from h)]; exact_mod_cast hx
  · rintro ⟨U,z,hU⟩ a
    have hf : f = W (mask U z) := by
      funext x; rw [maskW]; dsimp only [f]; rw [hU x]
      by_cases hx : ∀ a ∈ U, dotProduct a x = dotProduct a z
      · rw [if_pos hx, if_pos (show ∀ a ∈ U, dot a x = dot a z from hx)]; norm_cast
      · rw [if_neg hx, if_neg (show ¬∀ a ∈ U, dot a x = dot a z from hx)]; norm_cast
    change N ∣ W f a
    rw [hf, invW]
    exact dvd_mul_right _ _
