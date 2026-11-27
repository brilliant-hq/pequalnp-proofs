import Mathlib
import PEqualNP.Defs

open Finset

namespace PEqualNP.Outside.L_lib_1095_aux

def dot {m : ℕ} (μ w : Fin m → ZMod 2) : ZMod 2 := ∑ r, μ r * w r

def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  unfold chi; fin_cases a <;> fin_cases b <;> decide

theorem chi_add_one (a : ZMod 2) : chi (a + 1) = - chi a := by
  unfold chi; fin_cases a <;> decide

theorem chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

theorem sum_chi_mul (a : ZMod 2) : ∑ c : ZMod 2, chi (c * a) = if a = 0 then 2 else 0 := by
  fin_cases a <;> decide

theorem orth {m : ℕ} (w : Fin m → ZMod 2) :
    ∑ μ : Fin m → ZMod 2, chi (dot μ w) = if w = 0 then (2:ℤ)^m else 0 := by
  have : ∀ μ : Fin m → ZMod 2, chi (dot μ w) = ∏ r, chi (μ r * w r) := fun μ => chi_sum _ _
  simp_rw [this]
  rw [← Fintype.prod_sum (fun r c => chi (c * w r))]
  simp_rw [sum_chi_mul]
  split_ifs with h
  · subst h; simp
  · obtain ⟨r, hr⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp only [Pi.zero_apply] at hr; simp [hr])

theorem dot_sub {m : ℕ} (μ a b : Fin m → ZMod 2) : dot μ (a - b) = dot μ a - dot μ b := by
  unfold dot; rw [← Finset.sum_sub_distrib]; congr 1; ext r; simp [mul_sub]

theorem dot_add_left {m : ℕ} (μ ν a : Fin m → ZMod 2) : dot (μ + ν) a = dot μ a + dot ν a := by
  unfold dot; rw [← Finset.sum_add_distrib]; congr 1; ext r; simp [add_mul]

theorem dot_smul_left {m : ℕ} (c : ZMod 2) (μ a : Fin m → ZMod 2) :
    dot (c • μ) a = c * dot μ a := by
  unfold dot; rw [Finset.mul_sum]; congr 1; ext r; simp [mul_assoc]

theorem dot_zero_left {m : ℕ} (a : Fin m → ZMod 2) : dot 0 a = 0 := by simp [dot]

theorem count_of_balanced {m : ℕ} {Z : Type*} [Fintype Z] (F : Z → Fin m → ZMod 2)
    (hb : ∀ μ : Fin m → ZMod 2, μ ≠ 0 → ∑ z, chi (dot μ (F z)) = 0) (v : Fin m → ZMod 2) :
    2^m * (univ.filter (fun z => F z = v)).card = Fintype.card Z := by
  have key : ((2:ℤ)^m * (univ.filter (fun z => F z = v)).card : ℤ) = Fintype.card Z := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    have h1 : ∀ z, (2:ℤ)^m * ((if F z = v then 1 else 0 : ℕ) : ℤ)
        = ∑ μ : Fin m → ZMod 2, chi (dot μ (F z) - dot μ v) := by
      intro z
      have := orth (F z - v)
      simp only [dot_sub] at this
      rw [this]
      by_cases h : F z = v
      · simp [h]
      · have h' : F z - v ≠ 0 := sub_ne_zero.mpr h
        simp [h, h']
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ μ : Fin m → ZMod 2, ∑ z, chi (dot μ (F z) - dot μ v)
        = chi (- dot μ v) * ∑ z, chi (dot μ (F z)) := by
      intro μ; rw [Finset.mul_sum]; congr 1; ext z
      rw [sub_eq_add_neg, chi_add, mul_comm]
    simp_rw [h2]
    rw [Finset.sum_eq_single (0 : Fin m → ZMod 2)]
    · simp [dot_zero_left, chi]
    · intro μ _ hμ; rw [hb μ hμ, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact_mod_cast key

theorem sum_chi_flip {Z : Type*} [Fintype Z] (g : Z → ZMod 2) (f : Z → Z)
    (hf : Function.Involutive f) (hg : ∀ z, g (f z) = g z + 1) : ∑ z, chi (g z) = 0 := by
  have h := Equiv.sum_comp hf.toPerm (fun z => chi (g z))
  simp only [Function.Involutive.coe_toPerm, hg, chi_add_one, Finset.sum_neg_distrib] at h
  linarith

theorem zmod2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

def localRule (n : ℕ) (D : Fin n → Finset (Fin n)) (T : Fin n → (Fin n → ZMod 2) → ZMod 2) :
    Prop := ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

def xOf (n : ℕ) (U : Finset (Fin n)) (b : Fin n → ZMod 2) (z : U → ZMod 2) : Fin n → ZMod 2 :=
  fun i => if h : i ∈ U then z ⟨i, h⟩ else b i

def observed (n m : ℕ) (Q : Fin n → Fin m → ZMod 2) (U : Finset (Fin n))
    (T : Fin n → (Fin n → ZMod 2) → ZMod 2) (b : Fin n → ZMod 2) (z : U → ZMod 2) :
    Fin m → ZMod 2 :=
  fun r => ∑ i, (xOf n U b z i + T i (xOf n U b z)) * Q i r

def uniform (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → Fin m → ZMod 2)
    (U : Finset (Fin n)) : Prop :=
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card

def Cond (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → Fin m → ZMod 2)
    (U : Finset (Fin n)) (μ : Fin m → ZMod 2) : Prop :=
  ∃ k ∈ U, dot μ (Q k) ≠ 0 ∧ ∀ i, k ∈ D i → dot μ (Q i) = 0

theorem dot_observed (n m : ℕ) (Q : Fin n → Fin m → ZMod 2) (U : Finset (Fin n))
    (T : Fin n → (Fin n → ZMod 2) → ZMod 2) (b : Fin n → ZMod 2) (z : U → ZMod 2)
    (μ : Fin m → ZMod 2) :
    dot μ (observed n m Q U T b z) =
      ∑ i, (xOf n U b z i + T i (xOf n U b z)) * dot μ (Q i) := by
  unfold dot observed
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext r; ring

theorem xOf_flip (n : ℕ) (U : Finset (Fin n)) (b : Fin n → ZMod 2) (z : U → ZMod 2)
    (k : Fin n) (hk : k ∈ U) (i : Fin n) :
    xOf n U b (Function.update z ⟨k, hk⟩ (z ⟨k, hk⟩ + 1)) i
      = xOf n U b z i + if i = k then 1 else 0 := by
  unfold xOf
  by_cases hi : i ∈ U
  · simp only [hi, dif_pos, Function.update_apply, Subtype.mk.injEq]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  · have : i ≠ k := fun h => hi (h ▸ hk)
    simp [hi, this]

theorem uniform_of_cond (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → Fin m → ZMod 2)
    (U : Finset (Fin n)) (h : ∀ μ : Fin m → ZMod 2, μ ≠ 0 → Cond n m D Q U μ) :
    uniform n m D Q U := by
  intro T hT b v
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [count_of_balanced (fun z => observed n m Q U T b z) _ v]
  · simp
  intro μ hμ
  obtain ⟨k, hk, hck, hrd⟩ := h μ hμ
  apply sum_chi_flip _ (fun z => Function.update z ⟨k, hk⟩ (z ⟨k, hk⟩ + 1))
  · intro z
    simp only [Function.update_idem, Function.update_self]
    rw [add_assoc, zmod2_add_self, add_zero, Function.update_eq_self]
  · intro z
    simp only [dot_observed]
    have hterm : ∀ i, (xOf n U b (Function.update z ⟨k, hk⟩ (z ⟨k, hk⟩ + 1)) i
        + T i (xOf n U b (Function.update z ⟨k, hk⟩ (z ⟨k, hk⟩ + 1)))) * dot μ (Q i)
        = (xOf n U b z i + T i (xOf n U b z)) * dot μ (Q i)
          + if i = k then dot μ (Q k) else 0 := by
      intro i
      by_cases hc : dot μ (Q i) = 0
      · by_cases hik : i = k
        · subst hik; exact absurd hc hck
        · simp [hc, hik]
      · have hTi : T i (xOf n U b (Function.update z ⟨k, hk⟩ (z ⟨k, hk⟩ + 1)))
            = T i (xOf n U b z) := by
          apply hT
          intro j hj
          rw [xOf_flip]
          have : j ≠ k := by
            rintro rfl; exact hc (hrd i hj)
          simp [this]
        rw [hTi, xOf_flip]
        by_cases hik : i = k
        · subst hik; simp; ring
        · simp [hik]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [zmod2_ne_zero hck]

theorem cond_of_uniform (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → Fin m → ZMod 2)
    (U : Finset (Fin n)) (hu : uniform n m D Q U) (μ : Fin m → ZMod 2) (hμ : μ ≠ 0) :
    Cond n m D Q U μ := by
  classical
  by_contra hC
  simp only [Cond, not_exists, not_and, not_forall] at hC
  set c : Fin n → ZMod 2 := fun i => dot μ (Q i) with hcdef
  have H : ∀ k ∈ U, c k ≠ 0 → ∃ i, k ∈ D i ∧ c i ≠ 0 := by
    intro k hk hck
    obtain ⟨i, hi, hci⟩ := hC k hk hck
    exact ⟨i, hi, hci⟩
  let rd : Fin n → Fin n := fun k =>
    if h : k ∈ U ∧ c k ≠ 0 then Classical.choose (H k h.1 h.2) else k
  have rd_spec : ∀ k, k ∈ U → c k ≠ 0 → k ∈ D (rd k) ∧ c (rd k) ≠ 0 := by
    intro k hk hck
    have h : k ∈ U ∧ c k ≠ 0 := ⟨hk, hck⟩
    simp only [rd, dif_pos h]
    exact Classical.choose_spec (H k h.1 h.2)
  let S : Finset (Fin n) := U.filter (fun k => c k ≠ 0)
  let T : Fin n → (Fin n → ZMod 2) → ZMod 2 := fun i x => ∑ k ∈ S.filter (fun k => rd k = i), x k
  have hT : localRule n D T := by
    intro i x y hxy
    apply Finset.sum_congr rfl
    intro k hk
    simp only [S, Finset.mem_filter] at hk
    apply hxy
    rw [← hk.2]
    exact (rd_spec k hk.1.1 hk.1.2).1
  have hconst : ∀ b z, dot μ (observed n m Q U T b z) = ∑ i ∈ Uᶜ, b i * c i := by
    intro b z
    rw [dot_observed]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i, T i (xOf n U b z) * dot μ (Q i) = ∑ k ∈ S, xOf n U b z k := by
      have : ∀ i, T i (xOf n U b z) * dot μ (Q i) = T i (xOf n U b z) := by
        intro i
        simp only [T]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [S, Finset.mem_filter] at hk
        have := (rd_spec k hk.1.1 hk.1.2).2
        rw [hk.2] at this
        have h1 : dot μ (Q i) = 1 := zmod2_ne_zero this
        rw [h1, mul_one]
      simp_rw [this]
      exact Finset.sum_fiberwise S rd _
    have e2 : ∑ i, xOf n U b z i * dot μ (Q i)
        = ∑ k ∈ S, xOf n U b z k + ∑ i ∈ Uᶜ, b i * c i := by
      rw [← Finset.sum_add_sum_compl U]
      congr 1
      · simp only [S]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with h
        · have h1 : dot μ (Q i) = 1 := zmod2_ne_zero h
          rw [h1, mul_one]
        · have h0 : dot μ (Q i) = 0 := not_not.mp h
          rw [h0, mul_zero]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_compl] at hi
        simp [xOf, hi, hcdef]
    rw [e1, e2, add_comm, ← add_assoc, zmod2_add_self, zero_add]
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hμ
  have hr1 : μ r = 1 := zmod2_ne_zero hr
  have hu' := hu T hT 0 (Pi.single r (∑ i ∈ Uᶜ, (0 : Fin n → ZMod 2) i * c i + 1))
  have hempty : IsEmpty {z : U → ZMod 2 //
      observed n m Q U T 0 z = Pi.single r (∑ i ∈ Uᶜ, (0 : Fin n → ZMod 2) i * c i + 1)} := by
    refine ⟨fun ⟨z, hz⟩ => ?_⟩
    have h1 := hconst 0 z
    rw [hz] at h1
    simp [dot, Pi.single_apply, hr1] at h1
  rw [Nat.card_of_isEmpty, mul_zero] at hu'
  exact (pow_pos (by norm_num : (0:ℕ) < 2) _).ne hu'

def readers (n : ℕ) (D : Fin n → Finset (Fin n)) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => j ∈ D i)).card

def wires (n : ℕ) (D : Fin n → Finset (Fin n)) : ℕ := ∑ i, (D i).card

theorem wires_eq (n : ℕ) (D : Fin n → Finset (Fin n)) : wires n D = ∑ j, readers n D j := by
  unfold wires readers
  have h : ∀ i, (D i).card = ∑ j, if j ∈ D i then 1 else 0 := by
    intro i; rw [Finset.sum_boole]; simp
  simp_rw [h, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem card_nonzero (m : ℕ) :
    (Finset.univ.filter (fun v : Fin m → ZMod 2 => v ≠ 0)).card = 2^m - 1 := by
  rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

def dotMap {m : ℕ} {ι : Type*} (q : ι → Fin m → ZMod 2) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun μ i := dot μ (q i)
  map_add' μ ν := by ext i; simp [dot_add_left]
  map_smul' c μ := by ext i; simp [dot_smul_left]

theorem rank_bound (m : ℕ) {ι : Type*} [Fintype ι] (q : ι → Fin m → ZMod 2)
    (μ0 : Fin m → ZMod 2)
    (h : ∀ μ, (∀ i, dot μ (q i) = 0) → μ = 0 ∨ μ = μ0) : m ≤ Fintype.card ι + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (dotMap q)
  have h1 := Submodule.finrank_le (LinearMap.range (dotMap q))
  have hker : LinearMap.ker (dotMap q) ≤ Submodule.span (ZMod 2) {μ0} := by
    intro μ hμ
    rw [LinearMap.mem_ker] at hμ
    have : ∀ i, dot μ (q i) = 0 := fun i => congrFun hμ i
    rcases h μ this with h0 | h0
    · rw [h0]; exact Submodule.zero_mem _
    · rw [h0]; exact Submodule.mem_span_singleton_self _
  have h2 := Submodule.finrank_mono hker
  have h3 := finrank_span_le_card (R := ZMod 2) ({μ0} : Set (Fin m → ZMod 2))
  simp only [Set.toFinset_singleton, Finset.card_singleton] at h3
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn h1
  omega

theorem part2 (m : ℕ) (n : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → Fin m → ZMod 2)
    (W : Finset (Fin n)) (hW : W.card = 2^m - 1) (hu : uniform n m D Q Finset.univ)
    (hc : ∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) :
    2^m - 1 ≤ n ∧ (∀ j ∈ W, m - 1 ≤ readers n D j) ∧ (2^m - 1) * (m - 1) ≤ wires n D := by
  classical
  have hB := cond_of_uniform n m D Q _ hu

  let P : Fin n → (Fin m → ZMod 2) → Prop := fun j μ =>
    μ ≠ 0 ∧ dot μ (Q j) ≠ 0 ∧ (∀ i, j ∈ D i → dot μ (Q i) = 0) ∧
      (∀ k, k ≠ j → dot μ (Q k) ≠ 0 → ∃ i, k ∈ D i ∧ dot μ (Q i) ≠ 0)
  have hex : ∀ j ∈ W, ∃ μ, P j μ := by
    intro j hj
    have := hc j hj
    have hnc : ¬ ∀ μ : Fin m → ZMod 2, μ ≠ 0 → Cond n m D Q (Finset.univ.erase j) μ :=
      fun hh => this (uniform_of_cond n m D Q _ hh)
    push_neg at hnc
    obtain ⟨μ, hμ, hnC⟩ := hnc
    simp only [Cond, not_exists, not_and, not_forall] at hnC
    obtain ⟨k, _, hck, hrd⟩ := hB μ hμ
    have hkj : k = j := by
      by_contra hkj
      obtain ⟨i, hi, hci⟩ := hnC k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩) hck
      exact hci (hrd i hi)
    subst hkj
    refine ⟨μ, hμ, hck, hrd, ?_⟩
    intro k' hk' hck'
    obtain ⟨i, hi, hci⟩ := hnC k' (Finset.mem_erase.mpr ⟨hk', Finset.mem_univ _⟩) hck'
    exact ⟨i, hi, hci⟩
  let f : Fin n → (Fin m → ZMod 2) := fun j =>
    if h : j ∈ W then Classical.choose (hex j h) else 0
  have hf : ∀ j ∈ W, P j (f j) := by
    intro j hj; simp only [f, dif_pos hj]; exact Classical.choose_spec (hex j hj)
  have hinj : Set.InjOn f W := by
    intro j hj j' hj' heq
    by_contra hne
    have Pj := hf j hj
    have Pj' := hf j' hj'
    rw [heq] at Pj
    obtain ⟨i, hi, hci⟩ := Pj.2.2.2 j' (Ne.symm hne) Pj'.2.1
    exact hci (Pj'.2.2.1 i hi)
  have hsurj : ∀ μ : Fin m → ZMod 2, μ ≠ 0 → ∃ j ∈ W, f j = μ := by
    have hsub : W.image f ⊆ Finset.univ.filter (fun v : Fin m → ZMod 2 => v ≠ 0) := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      simp [(hf j hj).1]
    have hcard : (Finset.univ.filter (fun v : Fin m → ZMod 2 => v ≠ 0)).card ≤ (W.image f).card := by
      rw [Finset.card_image_of_injOn hinj, hW, card_nonzero]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro μ hμ
    have : μ ∈ W.image f := by rw [heq]; simp [hμ]
    obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp this
    exact ⟨j, hj, hfj⟩
  have hread : ∀ j ∈ W, m - 1 ≤ readers n D j := by
    intro j hj
    obtain ⟨hμ0, hc0, hr0, _⟩ := hf j hj
    have key1 : ∀ ν : Fin m → ZMod 2, (∀ i, j ∈ D i → dot ν (Q i) = 0) →
        dot ν (Q j) ≠ 0 → ν = f j := by
      intro ν hν hνj
      have hν0 : ν ≠ 0 := by rintro rfl; exact hνj (dot_zero_left _)
      obtain ⟨j', hj', hfj'⟩ := hsurj ν hν0
      by_cases hjj : j' = j
      · rw [← hfj', hjj]
      · have := (hf j' hj').2.2.2 j (Ne.symm hjj)
        rw [hfj'] at this
        obtain ⟨i, hi, hci⟩ := this hνj
        exact absurd (hν i hi) hci
    have hb := rank_bound m (fun i : (Finset.univ.filter (fun i => j ∈ D i)) => Q i.1) (f j)
      (by
        intro ν hν
        have hν' : ∀ i, j ∈ D i → dot ν (Q i) = 0 := by
          intro i hi
          exact hν ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        by_cases hνj : dot ν (Q j) = 0
        · left
          have h2 := key1 (ν + f j)
            (by intro i hi; rw [dot_add_left, hν' i hi, hr0 i hi, add_zero])
            (by rw [dot_add_left, hνj, zero_add]; exact hc0)
          have : ν = ν + f j - f j := by abel
          rw [this, h2, sub_self]
        · right; exact key1 ν hν' hνj)
    simp only [Fintype.card_coe] at hb
    unfold readers
    omega
  refine ⟨?_, hread, ?_⟩
  · have := Finset.card_le_univ W
    simp only [Fintype.card_fin] at this
    omega
  · rw [wires_eq]
    calc (2^m - 1) * (m - 1) = W.card * (m - 1) := by rw [hW]
      _ ≤ ∑ j ∈ W, readers n D j := by
          have := Finset.card_nsmul_le_sum W (readers n D) (m - 1) hread
          simpa [smul_eq_mul] using this
      _ ≤ ∑ j, readers n D j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def sig {m : ℕ} (b : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun r => ∑ t, if t.val ≤ r.val then b t else 0

def del {m : ℕ} (l : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun r => l r - (if h : 0 < r.val then l ⟨r.val - 1, by omega⟩ else 0)

theorem del_sig {m : ℕ} (b : Fin m → ZMod 2) : del (sig b) = b := by
  ext r
  unfold del sig
  by_cases h : 0 < r.val
  · rw [dif_pos h, ← Finset.sum_sub_distrib]
    have hp : ∀ t : Fin m, ((if t.val ≤ r.val then b t else 0) -
        (if t.val ≤ (⟨r.val - 1, by omega⟩ : Fin m).val then b t else 0))
        = if t = r then b t else 0 := by
      intro t
      simp only
      by_cases htr : t = r
      · subst htr
        have : ¬ (t.val ≤ t.val - 1) := by omega
        simp [this]
      · have hv : t.val ≠ r.val := fun e => htr (Fin.ext e)
        by_cases h1 : t.val ≤ r.val - 1
        · have : t.val ≤ r.val := by omega
          simp [h1, this, htr]
        · have : ¬ t.val ≤ r.val := by omega
          simp [h1, this, htr]
    simp_rw [hp]
    simp
  · rw [dif_neg h, sub_zero]
    have hp : ∀ t : Fin m, (if t.val ≤ r.val then b t else 0) = if t = r then b t else 0 := by
      intro t
      by_cases htr : t = r
      · subst htr; simp
      · have hv : t.val ≠ r.val := fun e => htr (Fin.ext e)
        have : ¬ t.val ≤ r.val := by omega
        simp [this, htr]
    simp_rw [hp]
    simp

def wt {m : ℕ} (v : Fin m → ZMod 2) : ℕ := (Finset.univ.filter (fun r => v r ≠ 0)).card

def bb {m : ℕ} (l : Fin m → ZMod 2) (p r : Fin m) : Fin m → ZMod 2 :=
  fun s => (if s = r then 1 else 0) + l r * (if s = p then 1 else 0)

theorem sig_bb {m : ℕ} (l : Fin m → ZMod 2) (p r s : Fin m) :
    sig (bb l p r) s = (if r.val ≤ s.val then 1 else 0) + l r * (if p.val ≤ s.val then 1 else 0) := by
  unfold sig bb
  have hp : ∀ t : Fin m, (if t.val ≤ s.val then
      ((if t = r then 1 else 0) + l r * (if t = p then 1 else 0)) else 0)
      = (if t = r then (if r.val ≤ s.val then (1 : ZMod 2) else 0) else 0)
        + (if t = p then l r * (if p.val ≤ s.val then 1 else 0) else 0) := by
    intro t
    by_cases h1 : t = r <;> by_cases h2 : t = p <;> by_cases h3 : t.val ≤ s.val <;>
      simp_all <;> (try split_ifs) <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem dot_bb_split {m : ℕ} (x l : Fin m → ZMod 2) (p r : Fin m) :
    dot x (bb l p r) = x r + l r * x p := by
  unfold dot bb
  have hp : ∀ s : Fin m, x s * ((if s = r then 1 else 0) + l r * (if s = p then 1 else 0))
      = (if s = r then x s else 0) + (if s = p then l r * x s else 0) := by
    intro s
    by_cases h1 : s = r <;> by_cases h2 : s = p <;> simp [h1, h2] <;> (try split_ifs) <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem dot_sig_bb {m : ℕ} (l : Fin m → ZMod 2) (p r : Fin m) (hrp : r ≠ p) :
    dot (sig (bb l p r)) (bb l p r) = 1 := by
  have hv : r.val ≠ p.val := fun e => hrp (Fin.ext e)
  unfold dot
  have hp : ∀ s : Fin m, sig (bb l p r) s * bb l p r s
      = (if s = r then sig (bb l p r) s else 0) + (if s = p then l r * sig (bb l p r) s else 0) := by
    intro s
    rw [show bb l p r s = (if s = r then 1 else 0) + l r * (if s = p then 1 else 0) from rfl]
    by_cases h1 : s = r <;> by_cases h2 : s = p <;> simp [h1, h2] <;> (try split_ifs) <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, sig_bb, le_refl]
  generalize l r = a
  rcases Nat.lt_or_gt_of_ne hv with h | h
  · have h1 : ¬ p.val ≤ r.val := by omega
    have h2 : r.val ≤ p.val := by omega
    simp only [h1, h2, if_true, if_false]
    revert a; decide
  · have h1 : p.val ≤ r.val := by omega
    have h2 : ¬ r.val ≤ p.val := by omega
    simp only [h1, h2, if_true, if_false]
    revert a; decide

theorem wt_bb {m : ℕ} (l : Fin m → ZMod 2) (p r : Fin m) : wt (bb l p r) ≤ 2 := by
  unfold wt
  have hsub : Finset.univ.filter (fun s => bb l p r s ≠ 0) ⊆ {r, p} := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    push_neg at hc
    apply hs
    simp [bb, hc.1, hc.2]
  calc _ ≤ ({r, p} : Finset (Fin m)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

def Qv {m : ℕ} (l : Fin m → ZMod 2) (p : Fin m) : Fin m → ZMod 2 :=
  if dot l (del l) = 1 ∧ wt (del l) ≤ 2 then del l else Pi.single p 1

theorem Qv_sig {m : ℕ} (l : Fin m → ZMod 2) (p r q : Fin m) (hrp : r ≠ p) :
    Qv (sig (bb l p r)) q = bb l p r := by
  unfold Qv
  rw [del_sig, if_pos ⟨dot_sig_bb l p r hrp, wt_bb l p r⟩]

theorem dot_Qv {m : ℕ} (l : Fin m → ZMod 2) (p : Fin m) (hp : l p = 1) : dot l (Qv l p) = 1 := by
  unfold Qv
  split_ifs with h
  · exact h.1
  · simp [dot, Pi.single_apply, hp]

theorem wt_Qv {m : ℕ} (l : Fin m → ZMod 2) (p : Fin m) : wt (Qv l p) ≤ 2 := by
  unfold Qv
  split_ifs with h
  · exact h.2
  · unfold wt
    have hsub : Finset.univ.filter (fun s => (Pi.single p (1 : ZMod 2) : Fin m → ZMod 2) s ≠ 0)
        ⊆ {p} := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [Finset.mem_singleton]
      by_contra hc
      exact hs (by simp [Pi.single_apply, hc])
    exact (Finset.card_le_card hsub).trans (by simp)

abbrev NZ (m : ℕ) := {v : Fin m → ZMod 2 // v ≠ 0}

theorem card_NZ (m : ℕ) : Fintype.card (NZ m) = 2^m - 1 := by
  rw [Fintype.card_subtype, card_nonzero]

theorem piv_ex {m : ℕ} (l : NZ m) : ∃ r, l.1 r ≠ 0 := by
  obtain ⟨r, hr⟩ := Function.ne_iff.mp l.2
  exact ⟨r, hr⟩

noncomputable def piv {m : ℕ} (l : NZ m) : Fin m := Classical.choose (piv_ex l)

theorem piv_spec {m : ℕ} (l : NZ m) : l.1 (piv l) = 1 :=
  zmod2_ne_zero (Classical.choose_spec (piv_ex l))

noncomputable def Qc {m N : ℕ} (e : Fin N ≃ NZ m) (i : Fin N) : Fin m → ZMod 2 :=
  Qv (e i).1 (piv (e i))

noncomputable def Dc {m N : ℕ} (e : Fin N ≃ NZ m) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => ∃ r, r ≠ piv (e j) ∧ (e i).1 = sig (bb (e j).1 (piv (e j)) r))

theorem mem_Dc {m N : ℕ} (e : Fin N ≃ NZ m) (i k : Fin N) :
    k ∈ Dc e i ↔ ∃ r, r ≠ piv (e k) ∧ (e i).1 = sig (bb (e k).1 (piv (e k)) r) := by
  simp [Dc]

theorem Qc_reader {m N : ℕ} (e : Fin N ≃ NZ m) (i k : Fin N) (r : Fin m) (hr : r ≠ piv (e k))
    (h : (e i).1 = sig (bb (e k).1 (piv (e k)) r)) : Qc e i = bb (e k).1 (piv (e k)) r := by
  unfold Qc; rw [h]; exact Qv_sig _ _ _ _ hr

theorem dot_self_bb {m : ℕ} (l : NZ m) (r : Fin m) : dot l.1 (bb l.1 (piv l) r) = 0 := by
  rw [dot_bb_split, piv_spec, mul_one, zmod2_add_self]

theorem sig_ne_zero {m : ℕ} (l : Fin m → ZMod 2) (p r : Fin m) (hrp : r ≠ p) :
    sig (bb l p r) ≠ 0 := by
  intro h
  have h2 := del_sig (bb l p r)
  rw [h] at h2
  have h3 := congrFun h2 r
  simp [del, bb, hrp] at h3

theorem sep {m : ℕ} (l μ : NZ m) (hne : l ≠ μ) :
    ∃ r, r ≠ piv μ ∧ dot l.1 (bb μ.1 (piv μ) r) ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hzz : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have h1 : ∀ r, r ≠ piv μ → l.1 r = μ.1 r * l.1 (piv μ) := by
    intro r hr; have := hc r hr; rw [dot_bb_split] at this; exact hzz _ _ this
  by_cases hp : l.1 (piv μ) = 0
  · apply l.2
    funext r
    by_cases hr : r = piv μ
    · rw [hr, hp]; rfl
    · rw [h1 r hr, hp, mul_zero]; rfl
  · have hp1 := zmod2_ne_zero hp
    apply hne
    apply Subtype.ext
    funext r
    by_cases hr : r = piv μ
    · rw [hr, hp1, piv_spec]
    · rw [h1 r hr, hp1, mul_one]

theorem part1 (m N : ℕ) (e : Fin N ≃ NZ m) :
    (∀ i, i ∉ Dc e i) ∧
    (∀ i, (Finset.univ.filter (fun r => Qc e i r ≠ 0)).card ≤ 2) ∧
    (∀ j, readers N (Dc e) j = m - 1) ∧ wires N (Dc e) = N * (m - 1) ∧
    (∀ U, uniform N m (Dc e) (Qc e) U ↔ U = Finset.univ) := by
  classical
  have hread : ∀ j, readers N (Dc e) j = m - 1 := by
    intro j
    unfold readers
    have hp : (Finset.univ.filter (fun r : Fin m => r ≠ piv (e j))).card = m - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    rw [← hp]
    symm
    apply Finset.card_bij (fun r hr => e.symm ⟨sig (bb (e j).1 (piv (e j)) r),
      sig_ne_zero _ _ _ (by simpa using hr)⟩)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rw [mem_Dc]
      exact ⟨r, hr, by simp⟩
    · intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
      have h1 := congrArg (fun x => (e x).1) heq
      simp only [Equiv.apply_symm_apply] at h1
      have h2 := congrArg del h1
      simp only [del_sig] at h2
      have h3 := congrFun h2 r1
      by_contra hne
      simp [bb, hr1, hne] at h3
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [mem_Dc] at hi
      obtain ⟨r, hr, h⟩ := hi
      refine ⟨r, by simpa using hr, ?_⟩
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext h.symm
  refine ⟨?_, ?_, hread, ?_, ?_⟩
  · intro i hi
    rw [mem_Dc] at hi
    obtain ⟨r, hr, h⟩ := hi
    have hQ := Qc_reader e i i r hr h
    have h1 : dot (e i).1 (Qc e i) = 1 := dot_Qv _ _ (piv_spec _)
    rw [hQ, dot_self_bb] at h1
    exact zero_ne_one h1
  · intro i; exact wt_Qv _ _
  · rw [wires_eq]; simp [hread]
  · intro U
    constructor
    · intro hu
      by_contra hU
      obtain ⟨j, hj⟩ : ∃ j, j ∉ U := by
        by_contra hh; push_neg at hh; exact hU (Finset.eq_univ_of_forall hh)
      have hl : (e j).1 ≠ 0 := (e j).2
      obtain ⟨k, hk, _, hrd⟩ := cond_of_uniform N m (Dc e) (Qc e) U hu _ hl
      have hkj : k ≠ j := by rintro rfl; exact hj hk
      have hne : e j ≠ e k := fun h => hkj (e.injective h).symm
      obtain ⟨r, hr, hdot⟩ := sep (e j) (e k) hne
      let i := e.symm ⟨sig (bb (e k).1 (piv (e k)) r), sig_ne_zero _ _ _ hr⟩
      have hi : (e i).1 = sig (bb (e k).1 (piv (e k)) r) := by simp [i]
      have hki : k ∈ Dc e i := (mem_Dc e i k).mpr ⟨r, hr, hi⟩
      have := hrd i hki
      rw [Qc_reader e i k r hr hi] at this
      exact hdot this
    · rintro rfl
      apply uniform_of_cond
      intro μ hμ
      refine ⟨e.symm ⟨μ, hμ⟩, Finset.mem_univ _, ?_, ?_⟩
      · have : dot μ (Qc e (e.symm ⟨μ, hμ⟩)) = 1 := by
          have := dot_Qv (e (e.symm ⟨μ, hμ⟩)).1 (piv (e (e.symm ⟨μ, hμ⟩))) (piv_spec _)
          simpa [Qc] using this
        rw [this]; exact one_ne_zero
      · intro i hi
        rw [mem_Dc] at hi
        obtain ⟨r, hr, h⟩ := hi
        rw [Qc_reader e i _ r hr h]
        have := dot_self_bb (e (e.symm ⟨μ, hμ⟩)) r
        simpa using this

end PEqualNP.Outside.L_lib_1095_aux

open PEqualNP.Outside.L_lib_1095_aux

theorem PEqualNP.Outside.L_lib_1095 : (let Word := fun k : Nat => Fin k → ZMod 2
let localRule := fun (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) =>
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
let observed := fun (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) =>
  let x := fun i : Fin n => if h : i ∈ U then z ⟨i,h⟩ else b i
  ∑ i, (x i + T i x) * Q i r
let uniform := fun (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) =>
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card
let readers := fun (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) =>
  (Finset.univ.filter (fun i => j ∈ D i)).card
let wires := fun (n : Nat) (D : Fin n → Finset (Fin n)) => ∑ i, (D i).card
∀ m : Nat, 1 ≤ m →
  let N := 2^m - 1
  (∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → Word m),
    (∀ i, i ∉ D i) ∧
    (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, readers N D j = m-1) ∧ wires N D = N*(m-1) ∧
    (∀ U, uniform N m D Q U ↔ U = Finset.univ)) ∧
  (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (W : Finset (Fin n)),
    W.card = N → uniform n m D Q Finset.univ →
    (∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) →
    N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D)) := by
  intro Word localRule observed uniform readers wires m hm N
  refine ⟨?_, ?_⟩
  · obtain e := (Fintype.equivFinOfCardEq (card_NZ m)).symm
    exact ⟨Dc e, Qc e, part1 m N e⟩
  · intro n D Q W hW hu hc
    exact part2 m n D Q W hW hu hc
