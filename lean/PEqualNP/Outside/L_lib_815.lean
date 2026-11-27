import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_815_aux

open Module


noncomputable section

open Classical

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K] [Fintype K]

def perp (S : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  (Algebra.traceForm (ZMod 2) K).orthogonal S

omit [FiniteDimensional (ZMod 2) K] [Fintype K] in
lemma mem_perp (S : Submodule (ZMod 2) K) (b : K) :
    b ∈ perp S ↔ ∀ s ∈ S, Algebra.trace (ZMod 2) K (b * s) = 0 := by
  unfold perp
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Algebra.traceForm_apply]
  constructor <;> intro h s hs <;> simpa [mul_comm] using h s hs

lemma finrank_perp (S : Submodule (ZMod 2) K) :
    finrank (ZMod 2) (perp S) = finrank (ZMod 2) K - finrank (ZMod 2) S :=
  LinearMap.BilinForm.finrank_orthogonal (traceForm_nondegenerate (ZMod 2) K) S

lemma card_filter_mem (S : Submodule (ZMod 2) K) [DecidablePred (· ∈ S)] :
    (Finset.univ.filter (· ∈ S)).card = 2 ^ finrank (ZMod 2) S := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [show Nat.card {x // x ∈ S} = Nat.card S from rfl, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod]

omit [FiniteDimensional (ZMod 2) K] in
lemma card_K : Fintype.card K = 2 ^ finrank (ZMod 2) K := by
  rw [card_eq_pow_finrank (K := ZMod 2), ZMod.card]

omit [Fintype K] in
lemma finrank_pos' : 0 < finrank (ZMod 2) K := Module.finrank_pos

def sqrtK (b : K) : K := b ^ (2 ^ (finrank (ZMod 2) K - 1))

lemma sqrtK_sq (b : K) : sqrtK b ^ 2 = b := by
  unfold sqrtK
  rw [← pow_mul, ← pow_succ]
  have h := finrank_pos' (K := K)
  rw [Nat.sub_add_cancel h, ← card_K]
  exact FiniteField.pow_card b

lemma sqrtK_of_sq (a : K) : sqrtK (a ^ 2) = a := by
  unfold sqrtK
  rw [← pow_mul, mul_comm, pow_mul]
  exact sqrtK_sq a

lemma sqrtK_ne_zero {b : K} (hb : b ≠ 0) : sqrtK b ≠ 0 := by
  intro h
  apply hb
  rw [← sqrtK_sq b, h]
  ring

omit [FiniteDimensional (ZMod 2) K] in
lemma trace_sq (y : K) :
    Algebra.trace (ZMod 2) K (y ^ 2) = Algebra.trace (ZMod 2) K y := by
  have h := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) y
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] at h
  exact h

def sqS (L : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))

omit [FiniteDimensional (ZMod 2) K] [Fintype K] in
lemma mem_perp_sqS (M : Submodule (ZMod 2) K) (b : K) :
    b ∈ perp (sqS M) ↔ ∀ y ∈ M, ∀ z ∈ M, Algebra.trace (ZMod 2) K (b * (y * z)) = 0 := by
  rw [mem_perp]
  constructor
  · intro h y hy z hz
    exact h _ (Submodule.subset_span ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩)
  · intro h s hs
    let φ : K →ₗ[ZMod 2] ZMod 2 :=
      (Algebra.trace (ZMod 2) K).comp (LinearMap.mulLeft (ZMod 2) b)
    have hle : sqS M ≤ LinearMap.ker φ := by
      unfold sqS
      rw [Submodule.span_le]
      rintro _ ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩
      simpa [φ] using h y hy z hz
    simpa [φ] using hle hs

def T (L : Submodule (ZMod 2) K) (b : K) : Submodule (ZMod 2) K :=
  L.map (LinearMap.mulLeft (ZMod 2) b) ⊔ Submodule.span (ZMod 2) {sqrtK b}

omit [FiniteDimensional (ZMod 2) K] [Fintype K] in
lemma mem_perp_T (L : Submodule (ZMod 2) K) (b x : K) : x ∈ perp (T L b) ↔
    (∀ l ∈ L, Algebra.trace (ZMod 2) K (x * (b * l)) = 0) ∧
      Algebra.trace (ZMod 2) K (x * sqrtK b) = 0 := by
  rw [mem_perp]
  constructor
  · intro h
    exact ⟨fun l hl => h _ (Submodule.mem_sup_left ⟨l, hl, rfl⟩),
      h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))⟩
  · rintro ⟨h1, h2⟩ t ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ht
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp only [LinearMap.mulLeft_apply, mul_add, mul_smul_comm, map_add, map_smul, h1 l hl, h2,
      smul_zero, add_zero]

lemma trace_bxx (b x : K) :
    Algebra.trace (ZMod 2) K (b * (x * x)) = Algebra.trace (ZMod 2) K (x * sqrtK b) := by
  rw [← trace_sq (x * sqrtK b), mul_pow, sqrtK_sq]
  congr 1
  ring

lemma perp_ext_iff (L : Submodule (ZMod 2) K) (x b : K) :
    b ∈ perp (sqS (L ⊔ Submodule.span (ZMod 2) {x})) ↔
      b ∈ perp (sqS L) ∧ x ∈ perp (T L b) := by
  rw [mem_perp_sqS, mem_perp_sqS, mem_perp_T]
  have hx : x ∈ L ⊔ Submodule.span (ZMod 2) {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  constructor
  · intro h
    refine ⟨fun y hy z hz => h y (Submodule.mem_sup_left hy) z (Submodule.mem_sup_left hz),
      fun l hl => ?_, ?_⟩
    · have := h x hx l (Submodule.mem_sup_left hl)
      rw [← this]
      congr 1
      ring
    · rw [← trace_bxx]
      exact h x hx x hx
  · rintro ⟨hW, h1, h2⟩ y hy z hz
    obtain ⟨l1, hl1, v1, hv1, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨l2, hl2, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a1, rfl⟩ := Submodule.mem_span_singleton.mp hv1
    obtain ⟨a2, rfl⟩ := Submodule.mem_span_singleton.mp hv2
    have e1 : Algebra.trace (ZMod 2) K (b * (l1 * x)) = 0 := by
      rw [← h1 l1 hl1]
      congr 1
      ring
    have e2 : Algebra.trace (ZMod 2) K (b * (x * l2)) = 0 := by
      rw [← h1 l2 hl2]
      congr 1
      ring
    have e3 : Algebra.trace (ZMod 2) K (b * (x * x)) = 0 := by
      rw [trace_bxx]
      exact h2
    have e0 := hW l1 hl1 l2 hl2
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, e0, e1, e2,
      e3, smul_zero, add_zero]

omit [FiniteDimensional (ZMod 2) K] [Fintype K] in
lemma finrank_map_mul (L : Submodule (ZMod 2) K) {b : K} (hb : b ≠ 0) :
    finrank (ZMod 2) (L.map (LinearMap.mulLeft (ZMod 2) b)) = finrank (ZMod 2) L :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (mul_right_injective₀ hb) L)).symm

lemma sqrt_mem_map_iff (L : Submodule (ZMod 2) K) {b : K} (hb : b ≠ 0) :
    sqrtK b ∈ L.map (LinearMap.mulLeft (ZMod 2) b) ↔ (sqrtK b)⁻¹ ∈ L := by
  have hs := sqrtK_ne_zero hb
  have hsq := sqrtK_sq b
  constructor
  · rintro ⟨l, hl, hbl⟩
    simp only [LinearMap.mulLeft_apply] at hbl
    have : l = (sqrtK b)⁻¹ := by
      have h3 : sqrtK b * (sqrtK b * l) = sqrtK b * 1 := by
        rw [← mul_assoc, ← pow_two, hsq, hbl, mul_one]
      exact eq_inv_of_mul_eq_one_right (mul_left_cancel₀ hs h3)
    rw [← this]
    exact hl
  · intro h
    refine ⟨(sqrtK b)⁻¹, h, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    calc b * (sqrtK b)⁻¹ = sqrtK b ^ 2 * (sqrtK b)⁻¹ := by rw [hsq]
      _ = sqrtK b := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hs, mul_one]

lemma finrank_T (L : Submodule (ZMod 2) K) {b : K} (hb : b ≠ 0) :
    finrank (ZMod 2) (T L b) =
      if (sqrtK b)⁻¹ ∈ L then finrank (ZMod 2) L else finrank (ZMod 2) L + 1 := by
  unfold T
  split_ifs with h
  · rw [← sqrt_mem_map_iff L hb] at h
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h), finrank_map_mul L hb]
  · rw [← sqrt_mem_map_iff L hb] at h
    rw [Submodule.finrank_sup_span_singleton h, finrank_map_mul L hb]

lemma key_pow (L : Submodule (ZMod 2) K) {b : K} (hb : b ≠ 0) :
    2 ^ (finrank (ZMod 2) L + 1) * 2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (T L b)) =
      2 ^ finrank (ZMod 2) K * (if (sqrtK b)⁻¹ ∈ L then 2 else 1) := by
  have hle : finrank (ZMod 2) (T L b) ≤ finrank (ZMod 2) K := Submodule.finrank_le _
  rw [finrank_T L hb] at hle ⊢
  split_ifs at hle ⊢ with h
  · rw [← pow_add, ← pow_succ]
    congr 1
    omega
  · rw [← pow_add, mul_one]
    congr 1
    omega

lemma card_perp_ne (S : Submodule (ZMod 2) K) :
    (Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp S)).card =
      2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) S) - 1 := by
  have h : Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp S) =
      (Finset.univ.filter (· ∈ perp S)).erase 0 := by
    ext b
    simp
  rw [h, Finset.card_erase_of_mem (by simp [(perp S).zero_mem]), card_filter_mem, finrank_perp]

lemma card_perp' (S : Submodule (ZMod 2) K) :
    (Finset.univ.filter (fun b : K => b ∈ perp S)).card =
      2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) S) := by
  rw [card_filter_mem, finrank_perp]

lemma sum_eq (L : Submodule (ZMod 2) K) :
    (∑ x : K, (2 ^ (finrank (ZMod 2) K -
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ)) =
      ∑ b ∈ Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp (sqS L)),
        2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (T L b)) := by
  have h1 : ∀ x : K, (2 ^ (finrank (ZMod 2) K -
      finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ) =
      ∑ b : K, if (b ≠ 0 ∧ b ∈ perp (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) then 1 else 0 := by
    intro x
    rw [← Finset.card_filter, card_perp_ne]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [perp_ext_iff]
  by_cases hb : b ≠ 0 ∧ b ∈ perp (sqS L)
  · rw [ite_eq_left hb, ← card_perp', Finset.card_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp [hb]
  · rw [ite_eq_right hb]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [ite_eq_right]
    tauto

def excP (L : Submodule (ZMod 2) K) (a : K) : Prop :=
  a ≠ 0 ∧ a ∈ L ∧ ∀ w ∈ sqS L, Algebra.trace (ZMod 2) K ((a⁻¹) ^ 2 * w) = 0

def Ecard (L : Submodule (ZMod 2) K) : ℕ :=
  (@Finset.filter K (excP L) (fun a => Classical.propDecidable (excP L a)) Finset.univ).card

lemma Ecard_eq (L : Submodule (ZMod 2) K) :
    Ecard L = ((Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp (sqS L))).filter
      (fun b => (sqrtK b)⁻¹ ∈ L)).card := by
  unfold Ecard
  apply Finset.card_nbij' (fun a => (a⁻¹) ^ 2) (fun b => (sqrtK b)⁻¹)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    obtain ⟨ha0, haL, haW⟩ := ha
    refine ⟨⟨pow_ne_zero _ (inv_ne_zero ha0), (mem_perp _ _).mpr haW⟩, ?_⟩
    rw [sqrtK_of_sq, inv_inv]
    exact haL
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨⟨hb0, hbW⟩, hbL⟩ := hb
    refine ⟨inv_ne_zero (sqrtK_ne_zero hb0), hbL, ?_⟩
    rw [inv_inv, sqrtK_sq]
    exact (mem_perp _ _).mp hbW
  · intro a _
    simp only
    rw [sqrtK_of_sq, inv_inv]
  · intro b _
    simp only
    rw [inv_inv, sqrtK_sq]

theorem claim1 (L : Submodule (ZMod 2) K) :
    2 ^ (finrank (ZMod 2) L + 1) * (∑ x : K, (2 ^ (finrank (ZMod 2) K -
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ)) =
      2 ^ finrank (ZMod 2) K * ((2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) - 1) +
        Ecard L) := by
  rw [sum_eq, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun b hb => key_pow L (Finset.mem_filter.mp hb).2.1)]
  rw [← Finset.mul_sum, Ecard_eq, ← card_perp_ne]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one]
  have := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp (sqS L)))
    (fun b => (sqrtK b)⁻¹ ∈ L)
  omega

lemma ar_lt (R P A E S N : ℕ) (hAR : A ≤ R) (hA : 1 ≤ A) (hP : 1 ≤ P) (hE1 : E + 1 ≤ A)
    (hS : S + P = P * (A + E)) (hN : N + R = 2 * R * P)
    (H : R * A + N * 2 ≤ S + R + N) : False := by
  nlinarith [Nat.mul_le_mul (Nat.sub_le_sub_right hAR A) (Nat.sub_le_sub_right hP 1)]

lemma ar_gt (R P D E S N : ℕ) (hR : 1 ≤ R) (hP : 1 ≤ P) (hD : 2 ≤ D) (hE2 : E + 1 ≤ R)
    (hS : S + P = P * (2 * R * D + E)) (hN : N + R = 2 * R * P)
    (H : R * (2 * R * D) + N * (2 * D) ≤ S + R + N) : False := by
  have h1 : (N + R) * D = 2 * R * P * D := by rw [hN]
  have h2 : P * (E + 1) ≤ P * R := Nat.mul_le_mul_left P hE2
  have h3 : R * D * 1 ≤ R * D * R := Nat.mul_le_mul_left (R * D) hR
  have h4 : P * R * 2 ≤ P * R * D := Nat.mul_le_mul_left (P * R) hD
  nlinarith

lemma ar_eq1 (R P E S N : ℕ) (hR : 1 ≤ R) (hP : 1 ≤ P) (hE2 : E + 1 ≤ R)
    (hS : S + P = P * (2 * R + E)) (hN : N + R = 2 * R * P)
    (H : R * (2 * R) + N * 4 ≤ S + R + N) : False := by
  nlinarith

lemma ar_eq0 (R P E S N : ℕ) (hR : 1 ≤ R) (hP : 1 ≤ P)
    (hS : S + P = P * (2 * R + E)) (hN : N + R = 2 * R * P)
    (H : R * (2 * R) + N * 2 ≤ S + R + N) : 0 < E ∧ R * (2 * R - 2) ≤ (E - 1) * P := by
  rcases Nat.eq_zero_or_pos E with h | h
  · subst h
    nlinarith
  · refine ⟨h, ?_⟩
    obtain ⟨E1, rfl⟩ : ∃ E1, E = E1 + 1 := ⟨E - 1, by omega⟩
    obtain ⟨R1, rfl⟩ : ∃ R1, R = R1 + 1 := ⟨R - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 2 * (R1 + 1) - 2 = 2 * R1 := by omega
    rw [this]
    nlinarith

lemma Ecard_le_A (L : Submodule (ZMod 2) K) :
    Ecard L + 1 ≤ 2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) := by
  have h1 := Ecard_eq L
  have h2 := Finset.card_filter_le (Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ perp (sqS L)))
    (fun b => (sqrtK b)⁻¹ ∈ L)
  rw [card_perp_ne] at h2
  have h3 : 1 ≤ 2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) := Nat.one_le_two_pow
  omega

lemma Ecard_le_R (L : Submodule (ZMod 2) K) :
    Ecard L + 1 ≤ 2 ^ finrank (ZMod 2) L := by
  have h1 : Ecard L ≤ ((Finset.univ.filter (· ∈ L)).erase 0).card := by
    unfold Ecard
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, excP] at ha
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ha.1, ha.2.1⟩
  rw [Finset.card_erase_of_mem (by simp [L.zero_mem]), card_filter_mem] at h1
  have h3 : 1 ≤ 2 ^ finrank (ZMod 2) L := Nat.one_le_two_pow
  omega

lemma sum_lower (L : Submodule (ZMod 2) K) (m : ℕ)
    (hm : ∀ x : K, x ∉ L → m ≤ finrank (ZMod 2) K -
      finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) :
    2 ^ finrank (ZMod 2) L * (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) - 1) +
      (2 ^ finrank (ZMod 2) K - 2 ^ finrank (ZMod 2) L) * (2 ^ m - 1) ≤
      ∑ x : K, (2 ^ (finrank (ZMod 2) K -
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ L)]
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K)) (· ∈ L)
  rw [Finset.card_univ, card_K, card_filter_mem] at hcard
  apply add_le_add
  · apply le_of_eq
    rw [Finset.sum_congr rfl (g := fun _ => 2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) - 1),
      Finset.sum_const, card_filter_mem, smul_eq_mul]
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hx.2)]
  · have h := Finset.card_nsmul_le_sum (Finset.univ.filter (fun x => ¬ x ∈ L))
      (fun x => (2 ^ (finrank (ZMod 2) K -
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ)) (2 ^ m - 1)
      (by
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (hm x hx.2)) 1)
    rw [smul_eq_mul] at h
    have he : (Finset.univ.filter (fun x => ¬ x ∈ L)).card =
        2 ^ finrank (ZMod 2) K - 2 ^ finrank (ZMod 2) L := by omega
    rw [he] at h
    exact h

theorem claim2 (L : Submodule (ZMod 2) K) :
    ∃ x : K, finrank (ZMod 2) ↥(L ⊔ Submodule.span (ZMod 2) {x}) =
        min (finrank (ZMod 2) K) (finrank (ZMod 2) L + 1) ∧
      min (finrank (ZMod 2) K) (finrank (ZMod 2) (sqS L) + (finrank (ZMod 2) L + 1)) -
        (if finrank (ZMod 2) K - finrank (ZMod 2) (sqS L) = finrank (ZMod 2) L + 1 ∧
            0 < Ecard L ∧
            2 ^ finrank (ZMod 2) L * (2 ^ (finrank (ZMod 2) L + 1) - 2) ≤
              (Ecard L - 1) * 2 ^ (finrank (ZMod 2) K - (finrank (ZMod 2) L + 1))
          then 1 else 0) ≤
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) := by
  have hrk : finrank (ZMod 2) L ≤ finrank (ZMod 2) K := Submodule.finrank_le L
  have hwk : finrank (ZMod 2) (sqS L) ≤ finrank (ZMod 2) K := Submodule.finrank_le _
  rcases Nat.lt_or_ge (finrank (ZMod 2) L) (finrank (ZMod 2) K) with hlt | hge
  · have H1 := claim1 L
    have hE1 := Ecard_le_A L
    have hE2 := Ecard_le_R L
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hfr : ∀ x : K, x ∉ L → finrank (ZMod 2) ↥(L ⊔ Submodule.span (ZMod 2) {x}) =
        min (finrank (ZMod 2) K) (finrank (ZMod 2) L + 1) := by
      intro x hx
      rw [Submodule.finrank_sup_span_singleton hx]
      omega
    have hS : ∀ x : K, finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) ≤
        finrank (ZMod 2) K := fun x => Submodule.finrank_le _
    generalize hloss : (if finrank (ZMod 2) K - finrank (ZMod 2) (sqS L) = finrank (ZMod 2) L + 1 ∧
            0 < Ecard L ∧
            2 ^ finrank (ZMod 2) L * (2 ^ (finrank (ZMod 2) L + 1) - 2) ≤
              (Ecard L - 1) * 2 ^ (finrank (ZMod 2) K - (finrank (ZMod 2) L + 1))
          then 1 else 0) = loss at hcon
    have hm : ∀ x : K, x ∉ L →
        (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L) - (finrank (ZMod 2) L + 1)) + loss + 1 ≤
          finrank (ZMod 2) K - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) := by
      intro x hx
      have h1 := hcon x (hfr x hx)
      have h2 := hS x
      omega
    have H2 := sum_lower L _ hm
    generalize (∑ x : K, (2 ^ (finrank (ZMod 2) K -
        finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ)) = S at H1 H2
    generalize Ecard L = E at H1 H2 hE1 hE2 hloss
    generalize hw : finrank (ZMod 2) (sqS L) = w at H1 H2 hE1 hloss hwk
    generalize hr : finrank (ZMod 2) L = r at H1 H2 hE2 hloss hlt hrk
    generalize hk : finrank (ZMod 2) K = k at H1 H2 hE1 hloss hlt hrk hwk
    clear hcon hm hfr hS hw hr hk

    have hR : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hP : 1 ≤ 2 ^ (k - (r + 1)) := Nat.one_le_two_pow
    have hA : 1 ≤ 2 ^ (k - w) := Nat.one_le_two_pow
    have hQ : 2 ^ k = 2 * 2 ^ r * 2 ^ (k - (r + 1)) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    have hRk : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hrk
    have hN : (2 ^ k - 2 ^ r) + 2 ^ r = 2 * 2 ^ r * 2 ^ (k - (r + 1)) := by omega
    have hS' : S + 2 ^ (k - (r + 1)) = 2 ^ (k - (r + 1)) * (2 ^ (k - w) + E) := by
      have H1' : 2 ^ (r + 1) * S = 2 ^ (r + 1) * (2 ^ (k - (r + 1)) * (2 ^ (k - w) - 1 + E)) := by
        rw [H1, hQ, pow_succ']
        ring
      have := Nat.eq_of_mul_eq_mul_left (by positivity) H1'
      rw [this]
      have : 2 ^ (k - w) - 1 + E + 1 = 2 ^ (k - w) + E := by omega
      rw [← this]
      ring
    have hM : 1 ≤ 2 ^ ((k - w - (r + 1)) + loss + 1) := Nat.one_le_two_pow
    have H : 2 ^ r * 2 ^ (k - w) + (2 ^ k - 2 ^ r) * 2 ^ ((k - w - (r + 1)) + loss + 1) ≤
        S + 2 ^ r + (2 ^ k - 2 ^ r) := by
      have e1 : 2 ^ r * 2 ^ (k - w) = 2 ^ r * (2 ^ (k - w) - 1) + 2 ^ r := by
        obtain ⟨a, ha⟩ : ∃ a, 2 ^ (k - w) = a + 1 := ⟨_, (Nat.sub_add_cancel hA).symm⟩
        rw [ha, Nat.add_sub_cancel]
        ring
      have e2 : (2 ^ k - 2 ^ r) * 2 ^ ((k - w - (r + 1)) + loss + 1) =
          (2 ^ k - 2 ^ r) * (2 ^ ((k - w - (r + 1)) + loss + 1) - 1) + (2 ^ k - 2 ^ r) := by
        obtain ⟨a, ha⟩ : ∃ a, 2 ^ ((k - w - (r + 1)) + loss + 1) = a + 1 :=
          ⟨_, (Nat.sub_add_cancel hM).symm⟩
        rw [ha, Nat.add_sub_cancel]
        ring
      omega
    generalize 2 ^ k - 2 ^ r = N at hN H
    rcases lt_trichotomy (k - w) (r + 1) with hc | hc | hc
    · have hl0 : loss = 0 := by
        rw [← hloss, ite_eq_right]
        omega
      subst hl0
      have hm1 : k - w - (r + 1) + 0 + 1 = 1 := by omega
      rw [hm1, pow_one] at H
      have hAR : 2 ^ (k - w) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ar_lt (2 ^ r) (2 ^ (k - (r + 1))) (2 ^ (k - w)) E S N hAR hA hP hE1 hS' hN H
    · have hA2 : 2 ^ (k - w) = 2 * 2 ^ r := by rw [hc, pow_succ']
      rw [hA2] at hS' H
      by_cases hcond : k - w = r + 1 ∧ 0 < E ∧
          2 ^ r * (2 ^ (r + 1) - 2) ≤ (E - 1) * 2 ^ (k - (r + 1))
      · rw [ite_eq_left hcond] at hloss
        subst hloss
        have hm1 : k - w - (r + 1) + 1 + 1 = 2 := by omega
        rw [hm1] at H
        norm_num at H
        exact ar_eq1 (2 ^ r) (2 ^ (k - (r + 1))) E S N hR hP hE2 hS' hN H
      · rw [ite_eq_right hcond] at hloss
        subst hloss
        have hm1 : k - w - (r + 1) + 0 + 1 = 1 := by omega
        rw [hm1, pow_one] at H
        have := ar_eq0 (2 ^ r) (2 ^ (k - (r + 1))) E S N hR hP hS' hN H
        apply hcond
        refine ⟨hc, this.1, ?_⟩
        rw [pow_succ']
        exact this.2
    · have hl0 : loss = 0 := by
        rw [← hloss, ite_eq_right]
        omega
      subst hl0
      have hD : 2 ≤ 2 ^ (k - w - (r + 1)) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k - w - (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hA2 : 2 ^ (k - w) = 2 * 2 ^ r * 2 ^ (k - w - (r + 1)) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      have hM2 : 2 ^ (k - w - (r + 1) + 0 + 1) = 2 * 2 ^ (k - w - (r + 1)) := by
        rw [add_zero, pow_succ']
      rw [hA2] at hS' H
      rw [hM2] at H
      exact ar_gt (2 ^ r) (2 ^ (k - (r + 1))) (2 ^ (k - w - (r + 1))) E S N hR hP hD hE2 hS' hN H
  · have hrk' : finrank (ZMod 2) L = finrank (ZMod 2) K := le_antisymm hrk hge
    have hLtop : L = ⊤ := Submodule.eq_top_of_finrank_eq hrk'
    have hsup : L ⊔ Submodule.span (ZMod 2) {(0 : K)} = L := by simp
    refine ⟨0, ?_, ?_⟩
    · rw [hsup]
      omega
    · rw [hsup]
      have hLW : L ≤ sqS L := by
        intro y hy
        have h1 : (1 : K) ∈ L := by rw [hLtop]; trivial
        have := Submodule.subset_span (R := ZMod 2)
          (s := Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K))) ⟨(⟨1, h1⟩, ⟨y, hy⟩), rfl⟩
        unfold sqS
        simpa using this
      have := Submodule.finrank_mono hLW
      omega

end

end PEqualNP.Outside.L_lib_815_aux

theorem PEqualNP.Outside.L_lib_815 : (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
  let k := Module.finrank F K
  let dim := fun (L : Submodule F K) => Module.finrank F L
  let sq := fun (L : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule F K) (x : K) => L ⊔ Submodule.span F {x}
  k % 2 = 0 → ∀ L : Submodule F K,
    let W := sq L
    let c := k - dim W
    let e := dim L + 1
    let exceptional := fun a : K => a ≠ 0 ∧ a ∈ L ∧
      ∀ w ∈ W, Algebra.trace F K ((a⁻¹)^2 * w) = 0
    let E := (@Finset.filter K exceptional (fun a => Classical.propDecidable (exceptional a))
      Finset.univ).card
    let loss := if c = e ∧ 0 < E ∧
      2^(dim L) * (2^e - 2) ≤ (E-1) * 2^(k-e) then 1 else 0
    2^e * (∑ x : K, (2^(k - dim (sq (extend L x))) - 1 : ℕ)) =
      2^k * ((2^c - 1) + E) ∧
    ∃ x : K, dim (extend L x) = min k e ∧
      min k (dim W + e) - loss ≤ dim (sq (extend L x))) := by
  intro F K _ _ _ _ k dim sq extend hk L W c e exceptional E loss
  exact ⟨PEqualNP.Outside.L_lib_815_aux.claim1 L, PEqualNP.Outside.L_lib_815_aux.claim2 L⟩
