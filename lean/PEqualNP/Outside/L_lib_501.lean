import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

namespace PEqualNP.Outside.L_lib_501

open Finset

theorem flip1 : ∀ F K w : ZMod 2, F ≠ K + w → ¬ F ≠ K + (w + 1) := by decide

theorem flip2 : ∀ F K w : ZMod 2, ¬ F ≠ K + w → F ≠ K + (w + 1) := by decide

theorem add_self2 : ∀ z : ZMod 2, z + z = 0 := by decide

theorem ne_zero_eq_one : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide

theorem exists_sep {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) {y : Fin n → ZMod 2}
    (hy : y ∉ U) :
    ∃ d₀ : Fin n → ZMod 2, (∀ u ∈ U, dotProduct d₀ u = 0) ∧ dotProduct d₀ y = 1 := by
  obtain ⟨φ, hφy, hφU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have key : ∀ v, dotProduct (fun i => φ (fun j => if i = j then 1 else 0)) v = φ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨fun i => φ (fun j => if i = j then 1 else 0), ?_, ?_⟩
  · intro u hu
    rw [key]
    have h : φ u ∈ U.map φ := Submodule.mem_map_of_mem hu
    rw [hφU] at h
    simpa using h
  · rw [key]
    exact ne_zero_eq_one _ hφy

theorem balanced {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (S : Finset (Fin n → ZMod 2))
    (hS : ∀ d, d ∈ S ↔ ∀ u ∈ U, dotProduct d u = 0) {y : Fin n → ZMod 2} (hy : y ∉ U)
    (F K : ZMod 2) :
    2 * (S.filter fun d => F ≠ K + dotProduct d y).card = S.card := by
  obtain ⟨d₀, hd₀U, hd₀y⟩ := exists_sep U hy
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun d => F ≠ K + dotProduct d y)
  have hshift : ∀ d, dotProduct (d + d₀) y = dotProduct d y + 1 := by
    intro d; rw [add_dotProduct, hd₀y]
  have hmem : ∀ d, d ∈ S → d + d₀ ∈ S := by
    intro d hd
    rw [hS] at hd ⊢
    intro u hu
    rw [add_dotProduct, hd u hu, hd₀U u hu, add_zero]
  have hinv : ∀ d : Fin n → ZMod 2, d + d₀ + d₀ = d := by
    intro d; funext i; simp only [Pi.add_apply, add_assoc, add_self2, add_zero]
  have heq : (S.filter fun d => F ≠ K + dotProduct d y).card
      = (S.filter fun d => ¬ (F ≠ K + dotProduct d y)).card := by
    apply Finset.card_nbij' (fun d => d + d₀) (fun d => d + d₀)
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hd ⊢
      exact ⟨hmem d hd.1, by rw [hshift]; exact flip1 _ _ _ hd.2⟩
    · intro d hd
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hd ⊢
      exact ⟨hmem d hd.1, by rw [hshift]; exact flip2 _ _ _ hd.2⟩
    · intro d _; exact hinv d
    · intro d _; exact hinv d
  omega

theorem main (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (p c : Fin n → ZMod 2) (e : ZMod 2)
    (hf : ∀ x ∈ U, f (p + x) = dotProduct c (p + x) + e) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
      2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => f x ≠ dotProduct a x + b)).card +
        2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
  classical
  set S : Finset (Fin n → ZMod 2) := Finset.univ.filter (fun d => ∀ u ∈ U, dotProduct d u = 0)
    with hSdef
  have hS : ∀ d, d ∈ S ↔ ∀ u ∈ U, dotProduct d u = 0 := by intro d; simp [hSdef]
  have h0S : (0 : Fin n → ZMod 2) ∈ S := (hS 0).2 (fun u _ => by simp)
  have hform : ∀ d x, dotProduct (c + d) x + (e - dotProduct d p)
      = (dotProduct c x + e) + dotProduct d (x - p) := by
    intro d x; rw [add_dotProduct, dotProduct_sub]; ring
  have hpt : ∀ x, 2 * (S.filter fun d => f x ≠ (dotProduct c x + e) + dotProduct d (x - p)).card
      = if x - p ∈ U then 0 else S.card := by
    intro x
    split_ifs with hx
    · have hfx : f x = dotProduct c x + e := by
        have h := hf (x - p) hx
        have hx' : p + (x - p) = x := by abel
        rwa [hx'] at h
      have h0 : (S.filter fun d => f x ≠ (dotProduct c x + e) + dotProduct d (x - p)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro d hd
        rw [(hS d).1 hd (x - p) hx, hfx, add_zero]
        exact fun h => h rfl
      rw [h0]; simp
    · exact balanced U S hS hx _ _
  have hsum : 2 * ∑ d ∈ S, ((Finset.univ : Finset (Fin n → ZMod 2)).filter
      (fun x => f x ≠ dotProduct (c + d) x + (e - dotProduct d p))).card
      = S.card * ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∉ U).card := by
    have h1 : ∑ d ∈ S, ((Finset.univ : Finset (Fin n → ZMod 2)).filter
        (fun x => f x ≠ dotProduct (c + d) x + (e - dotProduct d p))).card
        = ∑ x, (S.filter fun d => f x ≠ (dotProduct c x + e) + dotProduct d (x - p)).card := by
      simp only [Finset.card_filter, hform]
      exact Finset.sum_comm
    rw [h1, Finset.mul_sum]
    simp only [hpt]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_comm]
  have hin : ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∈ U).card
      = 2 ^ Module.finrank (ZMod 2) U := by
    have h1 : ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∈ U).card
        = ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x ∈ U).card := by
      apply Finset.card_nbij' (fun x => x - p) (fun x => x + p) <;> intro x hx <;> simp_all
    rw [h1, ← Fintype.card_subtype]
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]
  have htot : ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∈ U).card
      + ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∉ U).card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt : ∀ d ∈ S, 2 ^ n < 2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter
      (fun x => f x ≠ dotProduct (c + d) x + (e - dotProduct d p))).card
      + 2 ^ Module.finrank (ZMod 2) U := fun d _ => hcon (c + d) (e - dotProduct d p)
  have hl := Finset.sum_lt_sum_of_nonempty ⟨0, h0S⟩ hlt
  rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    smul_eq_mul] at hl
  rw [hin] at htot
  have h3 : S.card * 2 ^ n = S.card * 2 ^ Module.finrank (ZMod 2) U
      + S.card * ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun x => x - p ∉ U).card := by
    rw [← htot, mul_add]
  linarith

end PEqualNP.Outside.L_lib_501

theorem PEqualNP.Outside.L_lib_501 : (∀ n : ℕ,
  let V := Fin n → ZMod 2
  ∀ (f : V → ZMod 2) (U : Submodule (ZMod 2) V) (p c : V) (e : ZMod 2),
    (∀ x ∈ U, f (p+x) = dotProduct c (p+x) + e) →
    ∃ (a : V) (b : ZMod 2), 2*((Finset.univ : Finset V).filter (fun x => f x ≠ dotProduct a x + b)).card +
      2^(Module.finrank (ZMod 2) U) ≤ 2^n) := by
  intro n V f U p c e hf
  exact PEqualNP.Outside.L_lib_501.main n f U p c e hf
