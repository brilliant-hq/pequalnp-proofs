import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_831

open Finset

section
variable {E K : Type} [Field E] [Fintype E] [Field K] [Algebra E K] [FiniteDimensional E K]
  [Fintype K]

theorem card_sub (W : Submodule E K) [DecidablePred (fun x => x ∈ W)] :
    (univ.filter (fun x => x ∈ W)).card = Fintype.card E ^ Module.finrank E W := by
  rw [← Fintype.card_subtype]
  convert Module.card_eq_pow_finrank (K := E) (V := W)

theorem tri_card (g : ℕ) :
    (univ.filter (fun p : Fin g × Fin g => p.2 ≤ p.1)).card = g * (g + 1) / 2 := by
  have h1 : (univ.filter (fun p : Fin g × Fin g => p.2 ≤ p.1)).card
      = ∑ i : Fin g, (i.val + 1) := by
    rw [card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (univ.filter (fun j : Fin g => j ≤ i)) = Iic i := by ext j; simp
    rw [this, Fin.card_Iic]
  have h2 : ∀ n : ℕ, 2 * ∑ i ∈ range n, (i + 1) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, mul_add, ih]; ring
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => i + 1) g]
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  rw [← h2 g, mul_comm]

/-- the triangular system has no nonzero solution -/
theorem tri_zero (g : ℕ) (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (w : K)
    (hw : ∀ i j : Fin g, j ≤ i → f i (w * u j) = 0) (S : Finset (Fin g)) (a : Fin g → E) (x : K)
    (hx : x = w * ∑ i ∈ S, (a i * f i x) • u i) : x = 0 := by
  have hf : ∀ k, f k x = ∑ i ∈ S, (a i * f i x) * f k (w * u i) := by
    intro k
    conv_lhs => rw [hx]
    rw [mul_sum, map_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_smul_comm, map_smul, smul_eq_mul]
  have key : ∀ n : ℕ, ∀ k : Fin g, g ≤ k.val + n → f k x = 0 := by
    intro n
    induction n with
    | zero => intro k hk; have := k.isLt; omega
    | succ n ih =>
      intro k hk
      rw [hf k]
      apply sum_eq_zero
      intro i _
      by_cases hik : i ≤ k
      · rw [hw k i hik, mul_zero]
      · push Not at hik
        have : g ≤ i.val + n := by
          have : k.val < i.val := hik
          omega
        rw [ih i this, mul_zero, zero_mul]
  have hall : ∀ k, f k x = 0 := fun k => key g k (by omega)
  rw [hx]
  simp [hall]

theorem part_a (g : ℕ) (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (Z : Finset K)
    (hZ : ∀ w ∈ Z, w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
        S.card ≤ g ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * f i x) • u i) :
    Z.card + Fintype.card E ^ (Module.finrank E K - g * (g + 1) / 2)
      ≤ Fintype.card E ^ Module.finrank E K := by
  classical
  let T := {p : Fin g × Fin g // p.2 ≤ p.1}
  let L : K →ₗ[E] (T → E) :=
    LinearMap.pi (fun p : T => (f p.1.1).comp ((LinearMap.mul E K).flip (u p.1.2)))
  have hL : ∀ w p, L w p = f p.1.1 (w * u p.1.2) := fun _ _ => rfl
  have hcardT : Fintype.card T = g * (g + 1) / 2 := by
    rw [Fintype.card_subtype, tri_card]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank E (LinearMap.range L) ≤ Fintype.card T := by
    calc Module.finrank E (LinearMap.range L) ≤ Module.finrank E (T → E) :=
          Submodule.finrank_le _
      _ = Fintype.card T := Module.finrank_fintype_fun_eq_card E
  have hq : 0 < Fintype.card E := Fintype.card_pos
  have hker : Fintype.card E ^ (Module.finrank E K - g * (g + 1) / 2)
      ≤ (univ.filter (fun x => x ∈ LinearMap.ker L)).card := by
    rw [card_sub]
    apply Nat.pow_le_pow_right hq
    omega
  have hdisj : Disjoint Z (univ.filter (fun x => x ∈ LinearMap.ker L)) := by
    rw [disjoint_left]
    intro w hwZ hwk
    rw [mem_filter, LinearMap.mem_ker] at hwk
    obtain ⟨_, S, a, x, _, hx0, hx⟩ := hZ w hwZ
    apply hx0
    apply tri_zero g u f w _ S a x hx
    intro i j hji
    have := congrFun hwk.2 ⟨(i, j), hji⟩
    rw [hL] at this
    exact this
  calc Z.card + Fintype.card E ^ (Module.finrank E K - g * (g + 1) / 2)
      ≤ Z.card + (univ.filter (fun x => x ∈ LinearMap.ker L)).card := by omega
    _ = (Z ∪ univ.filter (fun x => x ∈ LinearMap.ker L)).card := (card_union_of_disjoint hdisj).symm
    _ ≤ Fintype.card K := card_le_univ _
    _ = Fintype.card E ^ Module.finrank E K := Module.card_eq_pow_finrank

def Bf (ell : K →ₗ[E] E) : LinearMap.BilinForm E K := (LinearMap.mul E K).compr₂ ell

theorem Bf_apply (ell : K →ₗ[E] E) (x y : K) : Bf ell x y = ell (x * y) := rfl

theorem Bf_nondeg (ell : K →ₗ[E] E) (h : ell ≠ 0) : (Bf ell).Nondegenerate := by
  constructor
  · intro x hx
    by_contra hx0
    apply h
    refine LinearMap.ext fun z => ?_
    have := hx (x⁻¹ * z)
    rw [Bf_apply, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at this
    simpa using this
  · intro y hy
    by_contra hy0
    apply h
    refine LinearMap.ext fun z => ?_
    have := hy (z * y⁻¹)
    rw [Bf_apply, mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
    simpa using this

theorem fx (ell : K →ₗ[E] E) (c x : K) : (ell.comp (Algebra.lmul E K c)) x = ell (c * x) := by
  simp

theorem part_b1 {g : ℕ} (ell : K →ₗ[E] E) (d : Fin g → K) (w : K) (t : ℕ)
    (h : w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
        S.card ≤ t ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * (ell.comp (Algebra.lmul E K (d i))) x) • d i) :
    ∃ y ∈ Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)),
      ell (w * y) ≠ 0 := by
  obtain ⟨_, S, a, x, _, hx0, hx⟩ := h
  by_contra hall
  push Not at hall
  have hk : ∀ k, ell (d k * x) = 0 := by
    intro k
    conv_lhs => rw [hx]
    rw [mul_sum, mul_sum, map_sum]
    apply sum_eq_zero
    intro i _
    have hm : d i * d k ∈ Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)) :=
      Submodule.subset_span ⟨(i, k), rfl⟩
    have := hall _ hm
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul]
    rw [show d k * (w * d i) = w * (d i * d k) by ring, this, mul_zero]
  apply hx0
  rw [hx]
  simp [fx, hk]

theorem part_b2 {g : ℕ} (ell : K →ₗ[E] E) (d : Fin g → K) (w : K)
    (h : ∃ y ∈ Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)),
      ell (w * y) ≠ 0) :
    w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
        S.card ≤ 2 ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * (ell.comp (Algebra.lmul E K (d i))) x) • d i := by
  obtain ⟨y, hy, hne⟩ := h
  have hij : ∃ i j, ell (w * (d i * d j)) ≠ 0 := by
    by_contra hc
    push Not at hc
    have hz : ∀ z ∈ Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)),
        ell (w * z) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hz
        exact hc i j
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add, map_add, ha, hb, add_zero]
      | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]
    exact hne (hz y hy)
  have hw : w ≠ 0 := by
    rintro rfl
    obtain ⟨i, j, h⟩ := hij
    simp at h
  refine ⟨hw, ?_⟩
  by_cases hdiag : ∃ i, ell (w * (d i * d i)) ≠ 0
  · obtain ⟨i, hi⟩ := hdiag
    set u := ell (w * (d i * d i)) with hu
    have hdi : d i ≠ 0 := by
      intro h0; apply hi; rw [hu, h0]; simp
    refine ⟨{i}, fun _ => u⁻¹, w * d i, by simp, mul_ne_zero hw hdi, ?_⟩
    rw [sum_singleton, fx, show d i * (w * d i) = w * (d i * d i) by ring, ← hu,
      inv_mul_cancel₀ hi, one_smul]
  · push Not at hdiag
    obtain ⟨i, j, hu0⟩ := hij
    set u := ell (w * (d i * d j)) with hu
    have hne : i ≠ j := by
      rintro rfl
      exact hu0 (hdiag i)
    have hfi : ell (d i * (w * (d i + d j))) = u := by
      rw [show d i * (w * (d i + d j)) = w * (d i * d i) + w * (d i * d j) by ring,
        map_add, hdiag i, zero_add]
    have hfj : ell (d j * (w * (d i + d j))) = u := by
      rw [show d j * (w * (d i + d j)) = w * (d i * d j) + w * (d j * d j) by ring,
        map_add, hdiag j, add_zero]
    have hx0 : w * (d i + d j) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, map_zero] at hfi
      exact hu0 hfi.symm
    refine ⟨{i, j}, fun _ => u⁻¹, w * (d i + d j), card_le_two, hx0, ?_⟩
    rw [sum_pair hne, fx, fx, hfi, hfj, inv_mul_cancel₀ hu0, one_smul, one_smul]

end

end PEqualNP.Outside.L_lib_831

open PEqualNP.Outside.L_lib_831 Finset in
theorem PEqualNP.Outside.L_lib_831 : ∀ (E K : Type) [Field E] [CharP E 2] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [Fintype K], 2 < Fintype.card E →
  ∀ (g : ℕ) (ell : K →ₗ[E] E), ell ≠ 0 →
    let m := Module.finrank E K
    let q := Fintype.card E
    let meet := fun (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (w : K) (t : ℕ) =>
      w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
        S.card ≤ t ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * f i x) • u i
    (∀ (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (Z : Finset K),
      (∀ w ∈ Z, meet u f w g) → Z.card + q^(m-g*(g+1)/2) ≤ q^m) ∧
    ∀ d : Fin g → K,
      let P := Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))
      let good := meet d (fun i => ell.comp (Algebra.lmul E K (d i)))
      (∀ w : K, (good w g ↔ good w 2) ∧ (good w 2 ↔ ∃ y ∈ P, ell (w*y) ≠ 0)) ∧
        (@Finset.filter K (fun w => good w 2) (fun w => Classical.propDecidable (good w 2))
          Finset.univ).card + q^(m-Module.finrank E P) = q^m := by
  intro E K _ _ _ _ _ _ _ _ g ell hell m q meet
  refine ⟨fun u f Z hZ => part_a g u f Z hZ, ?_⟩
  intro d P good
  have hiff : ∀ w : K, good w 2 ↔ ∃ y ∈ P, ell (w*y) ≠ 0 := fun w =>
    ⟨fun h => part_b1 ell d w 2 h, fun h => part_b2 ell d w h⟩
  refine ⟨fun w => ⟨⟨fun h => (hiff w).mpr (part_b1 ell d w g h), fun h => ?_⟩, hiff w⟩, ?_⟩
  · obtain ⟨hw, S, a, x, _, hx0, hx⟩ := part_b2 ell d w ((hiff w).mp h)
    exact ⟨hw, S, a, x, card_le_univ S |>.trans (by simp), hx0, hx⟩
  · classical
    let Q := (Bf ell).orthogonal P
    have hQ : ∀ w, good w 2 ↔ w ∉ Q := by
      intro w
      rw [hiff w, LinearMap.BilinForm.mem_orthogonal_iff]
      simp only [Bf_apply, not_forall]
      constructor
      · rintro ⟨y, hy, hne⟩
        exact ⟨y, hy, by rwa [mul_comm]⟩
      · rintro ⟨y, hy, hne⟩
        exact ⟨y, hy, by rwa [mul_comm]⟩
    have hfil : (@Finset.filter K (fun w => good w 2) (fun w => Classical.propDecidable (good w 2))
        Finset.univ) = univ.filter (fun w => ¬ (w ∈ Q)) := by
      ext w
      simp only [mem_filter, mem_univ, true_and]
      exact hQ w
    rw [hfil]
    have hdim : Module.finrank E Q = m - Module.finrank E P :=
      LinearMap.BilinForm.finrank_orthogonal (Bf_nondeg ell hell) P
    have hc := card_filter_add_card_filter_not (s := (univ : Finset K)) (fun w => w ∈ Q)
    rw [card_sub Q, hdim, card_univ, Module.card_eq_pow_finrank (K := E) (V := K)] at hc
    simp only [m, q] at hc ⊢
    omega
