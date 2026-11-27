import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25802

open Finset Fin.CommRing

def cov {n : ℕ} (S U : Finset (Fin (n+1))) : Prop := ∀ i ∈ S, i + 1 ∈ U ∨ i + 1 + 1 ∈ U

def muN {n : ℕ} (S : Finset (Fin (n+1))) : ℕ :=
  (S.powerset.filter (fun E => ∀ i ∈ E, i + 1 ∉ E)).sup Finset.card

theorem mu_ge {n : ℕ} {S E : Finset (Fin (n+1))} (hE : E ⊆ S) (hi : ∀ i ∈ E, i + 1 ∉ E) :
    E.card ≤ muN S :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hE, hi⟩)

theorem mu_att {n : ℕ} (S : Finset (Fin (n+1))) :
    ∃ E, E ⊆ S ∧ (∀ i ∈ E, i + 1 ∉ E) ∧ E.card = muN S := by
  obtain ⟨E, hE, h⟩ := Finset.exists_mem_eq_sup
    (S.powerset.filter (fun E => ∀ i ∈ E, i + 1 ∉ E)) ⟨∅, by simp⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hE
  exact ⟨E, hE.1, hE.2, h.symm⟩

theorem mu_mono {n : ℕ} {S T : Finset (Fin (n+1))} (h : S ⊆ T) : muN S ≤ muN T := by
  obtain ⟨E, hE, hi, he⟩ := mu_att S
  rw [← he]; exact mu_ge (hE.trans h) hi

theorem cov_ge {n : ℕ} {S U : Finset (Fin (n+1))} (hU : cov S U) : muN S ≤ U.card := by
  classical
  obtain ⟨E, hE, hi, he⟩ := mu_att S
  rw [← he]
  apply Finset.card_le_card_of_injOn (fun i => if i + 1 ∈ U then i + 1 else i + 1 + 1)
  · intro i hiE
    rcases hU i (hE hiE) with h | h
    · simp [h]
    · by_cases h' : i + 1 ∈ U
      · simp [h']
      · simp [h', h]
  · intro i hiE j hjE hij
    simp only at hij
    split_ifs at hij with h1 h2 h2
    · exact add_right_cancel hij
    · have : i = j + 1 := add_right_cancel hij
      exact absurd (this ▸ (Finset.mem_coe.1 hiE)) (hi j hjE)
    · have : i + 1 = j := add_right_cancel hij
      exact absurd (this ▸ (Finset.mem_coe.1 hjE)) (hi i hiE)
    · exact add_right_cancel (add_right_cancel hij)

theorem odd_bound {n : ℕ} (hodd : (n+1) % 2 = 1) {E : Finset (Fin (n+1))}
    (hi : ∀ i ∈ E, i + 1 ∉ E) : 2 * E.card + 1 ≤ n + 1 := by
  classical
  have hd : Disjoint E (E.image (fun i => i + 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hj'
    exact hi i hi' hj
  have hc := Finset.card_union_of_disjoint hd
  rw [Finset.card_image_of_injective _ (add_left_injective 1)] at hc
  have hle := Finset.card_le_univ (E ∪ E.image (fun i => i + 1))
  rw [Fintype.card_fin] at hle
  omega

theorem cov_univ_odd {n : ℕ} (hodd : (n+1) % 2 = 1) {U : Finset (Fin (n+1))}
    (hU : cov Finset.univ U) : muN (Finset.univ : Finset (Fin (n+1))) + 1 ≤ U.card := by
  classical
  set X := (Finset.univ : Finset (Fin (n+1))).filter (fun i => i + 1 ∉ U) with hX
  have hXi : ∀ i ∈ X, i + 1 ∉ X := by
    intro i hi hi'
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    rcases hU i (Finset.mem_univ _) with h | h
    · exact hi h
    · exact hi' h
  have h1 : X.card ≤ muN (Finset.univ : Finset (Fin (n+1))) :=
    mu_ge (Finset.subset_univ _) hXi
  have h2 : X.image (fun i => i + 1) = Uᶜ := by
    ext j
    simp only [hX, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hj; exact ⟨j - 1, by simpa using hj, by simp⟩
  have h3 := Finset.card_image_of_injective X (add_left_injective (1 : Fin (n+1)))
  rw [h2, Finset.card_compl, Fintype.card_fin] at h3
  have hUle := Finset.card_le_univ U
  rw [Fintype.card_fin] at hUle
  obtain ⟨E, -, hi, he⟩ := mu_att (Finset.univ : Finset (Fin (n+1)))
  have h4 := odd_bound hodd hi
  omega

theorem upper_ne {n : ℕ} {S : Finset (Fin (n+1))} (hS : S ≠ Finset.univ) :
    ∃ U, cov S U ∧ U.card ≤ muN S := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m ∉ S := by
    by_contra h; push Not at h; exact hS (Finset.eq_univ_iff_forall.2 h)
  have hex : ∀ i : Fin (n+1), ∃ j : ℕ, i - (j : Fin (n+1)) ∉ S := fun i =>
    ⟨(i - m).val, by rw [Fin.cast_val_eq_self, sub_sub_cancel]; exact hm⟩
  have p0 : ∀ i, i ∉ S → Nat.find (hex i) = 0 := fun i hi =>
    (Nat.find_eq_zero (hex i)).2 (by simpa using hi)
  have hpos : ∀ i, i ∈ S → Nat.find (hex i) ≠ 0 := by
    intro i hi h
    rw [Nat.find_eq_zero] at h
    simp at h
    exact h hi
  have psucc : ∀ i, i ∈ S → Nat.find (hex i) = Nat.find (hex (i - 1)) + 1 := by
    intro i hi
    apply le_antisymm
    · apply Nat.find_min'
      have := Nat.find_spec (hex (i - 1))
      have e : i - ((Nat.find (hex (i - 1)) + 1 : ℕ) : Fin (n+1)) =
          i - 1 - ((Nat.find (hex (i - 1)) : ℕ) : Fin (n+1)) := by push_cast; ring
      rw [e]; exact this
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (hpos i hi)
      rw [hr]
      apply Nat.succ_le_succ
      apply Nat.find_min'
      have := Nat.find_spec (hex i)
      rw [hr] at this
      have e : i - ((r.succ : ℕ) : Fin (n+1)) = i - 1 - ((r : ℕ) : Fin (n+1)) := by
        push_cast; ring
      rw [e] at this; exact this
  set E := (Finset.univ : Finset (Fin (n+1))).filter (fun i => Nat.find (hex i) % 2 = 1) with hE
  have hES : E ⊆ S := by
    intro i hi
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra h
    rw [p0 i h] at hi
    simp at hi
  have hEi : ∀ i ∈ E, i + 1 ∉ E := by
    intro i hi hi'
    have hs := psucc (i + 1) (hES hi')
    rw [add_sub_cancel_right] at hs
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    omega
  refine ⟨E.image (fun i => i + 1 + 1), ?_, (Finset.card_image_le).trans (mu_ge hES hEi)⟩
  intro i hi
  by_cases h : Nat.find (hex i) % 2 = 1
  · right
    exact Finset.mem_image.2 ⟨i, by simp [hE, h], rfl⟩
  · left
    have hs := psucc i hi
    refine Finset.mem_image.2 ⟨i - 1, ?_, by ring⟩
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem upper_even {n : ℕ} (hev : (n+1) % 2 = 0) :
    ∃ U, cov (Finset.univ : Finset (Fin (n+1))) U ∧
      U.card ≤ muN (Finset.univ : Finset (Fin (n+1))) := by
  classical
  set E := (Finset.univ : Finset (Fin (n+1))).filter (fun i => i.val % 2 = 0) with hE
  have hv : ∀ i : Fin (n+1), (i + 1).val % 2 = 0 ↔ ¬ (i.val % 2 = 0) := by
    intro i
    rw [Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last]; omega
    · omega
  have hEi : ∀ i ∈ E, i + 1 ∉ E := by
    intro i hi hi'
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact (hv i).1 hi' hi
  refine ⟨E.image (fun i => i + 1), ?_,
    (Finset.card_image_le).trans (mu_ge (Finset.subset_univ _) hEi)⟩
  intro i _
  by_cases h : i.val % 2 = 0
  · left; exact Finset.mem_image.2 ⟨i, by simp [hE, h], rfl⟩
  · right; exact Finset.mem_image.2 ⟨i + 1, by simp [hE, (hv i).2 h], rfl⟩

theorem upper_odd {n : ℕ} :
    ∃ U, cov (Finset.univ : Finset (Fin (n+1))) U ∧
      U.card ≤ muN (Finset.univ : Finset (Fin (n+1))) + 1 := by
  classical
  have hne : (Finset.univ : Finset (Fin (n+1))).erase 0 ≠ Finset.univ := by
    intro h
    have : (0 : Fin (n+1)) ∈ (Finset.univ : Finset (Fin (n+1))).erase 0 := by
      rw [h]; exact Finset.mem_univ _
    simp at this
  obtain ⟨U, hU, hc⟩ := upper_ne hne
  refine ⟨insert (0 + 1) U, ?_, ?_⟩
  · intro i _
    by_cases h : i = 0
    · subst h; left; exact Finset.mem_insert_self _ _
    · rcases hU i (by simp [h]) with h' | h'
      · left; exact Finset.mem_insert_of_mem h'
      · right; exact Finset.mem_insert_of_mem h'
  · have := mu_mono (Finset.erase_subset 0 (Finset.univ : Finset (Fin (n+1))))
    have := Finset.card_insert_le (0 + 1 : Fin (n+1)) U
    omega

theorem lower_cost {n : ℕ} {S U : Finset (Fin (n+1))} (hU : cov S U) :
    (if S = Finset.univ ∧ 1 < n + 1 ∧ (n+1) % 2 = 1 then muN S + 1 else muN S) ≤ U.card := by
  split_ifs with h
  · obtain ⟨rfl, -, hodd⟩ := h
    exact cov_univ_odd hodd hU
  · exact cov_ge hU

theorem upper_cost {n : ℕ} (hn : 1 ≤ n) (S : Finset (Fin (n+1))) :
    ∃ U, cov S U ∧
      U.card ≤ (if S = Finset.univ ∧ 1 < n + 1 ∧ (n+1) % 2 = 1 then muN S + 1 else muN S) := by
  split_ifs with h
  · obtain ⟨rfl, -, -⟩ := h
    exact upper_odd
  · by_cases hS : S = Finset.univ
    · subst hS
      exact upper_even (by by_contra h'; exact h ⟨rfl, by omega, by omega⟩)
    · exact upper_ne hS



theorem two_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M} (h : x + y = 0) :
    x = y := by
  have hy : y + y = 0 := by
    rw [← two_smul (ZMod 2) y]
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  calc x = x + y + y := by rw [add_assoc, hy, add_zero]
    _ = y := by rw [h, zero_add]

theorem lin_lower {n : ℕ} (hn : 1 ≤ n) {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] (hdim : Module.finrank (ZMod 2) M = n + 1)
    (Y : Fin (n+1) → M) (hY : Submodule.span (ZMod 2) (Set.range Y) = ⊤)
    (P : Submodule (ZMod 2) M) (S : Finset (Fin (n+1))) (pick : Fin (n+1) → M)
    (hP : ∀ i, pick i ∈ P)
    (hpick : ∀ i ∈ S, pick i = Y (i+1) ∨ pick i = Y (i+1+1) ∨ pick i = Y (i+1) + Y (i+1+1)) :
    ∃ U, cov S U ∧ U.card ≤ Module.finrank (ZMod 2) P := by
  classical
  have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  set g : Fin (n+1) → M ⧸ P := fun j => P.mkQ (Y j) with hg
  have hspan : Submodule.span (ZMod 2) (Set.range g) = ⊤ := by
    have : Set.range g = P.mkQ '' Set.range Y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hY, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨b, hb, hbs, hbli⟩ := exists_linearIndependent (ZMod 2) (Set.range g)
  set B := (Finset.univ : Finset (Fin (n+1))).filter
    (fun j => g j ∈ b ∧ ∀ j', g j' = g j → j ≤ j') with hB
  have hBmem : ∀ j, j ∈ B ↔ g j ∈ b ∧ ∀ j', g j' = g j → j ≤ j' := by
    intro j; simp [hB]
  have hB0 : ∀ j ∈ B, g j ≠ 0 := by
    intro j hj
    have h := ((hBmem j).1 hj).1
    exact hbli.ne_zero ⟨g j, h⟩
  have hBinj : ∀ u ∈ B, ∀ v ∈ B, g u = g v → u = v := by
    intro u hu v hv h
    exact le_antisymm (((hBmem u).1 hu).2 v h.symm) (((hBmem v).1 hv).2 u h)
  have hcard : Module.finrank (ZMod 2) (M ⧸ P) ≤ B.card := by
    have hsub : b ⊆ ((B.image g : Finset (M ⧸ P)) : Set (M ⧸ P)) := by
      intro v hv
      obtain ⟨j0, hj0⟩ := hb hv
      have hne : ((Finset.univ : Finset (Fin (n+1))).filter (fun j => g j = v)).Nonempty :=
        ⟨j0, by simp [hj0]⟩
      set j1 := ((Finset.univ : Finset (Fin (n+1))).filter (fun j => g j = v)).min' hne
      have hj1 : g j1 = v := by
        have := Finset.min'_mem _ hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨j1, (hBmem j1).2 ⟨hj1 ▸ hv, ?_⟩, hj1⟩)
      intro j' hj'
      exact Finset.min'_le _ _ (by simp [hj', hj1])
    have h1 : Module.finrank (ZMod 2) (M ⧸ P) =
        Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (M ⧸ P)) := (finrank_top (ZMod 2) (M ⧸ P)).symm
    rw [h1, ← hspan, ← hbs]
    calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) b)
        ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
            ((B.image g : Finset (M ⧸ P)) : Set (M ⧸ P))) :=
          Submodule.finrank_mono (Submodule.span_mono hsub)
      _ ≤ (B.image g).card := finrank_span_finset_le_card _
      _ ≤ B.card := Finset.card_image_le
  have hq := Submodule.finrank_quotient_add_finrank P
  rw [hdim] at hq
  refine ⟨Bᶜ, ?_, ?_⟩
  · intro i hi
    by_contra hc
    push Not at hc
    have ha : i + 1 ∈ B := by simpa using hc.1
    have hb2 : i + 1 + 1 ∈ B := by simpa using hc.2
    have hz : P.mkQ (pick i) = 0 := (Submodule.Quotient.mk_eq_zero P).2 (hP i)
    rcases hpick i hi with h | h | h
    · rw [h] at hz; exact hB0 _ ha hz
    · rw [h] at hz; exact hB0 _ hb2 hz
    · rw [h, map_add] at hz
      have := hBinj _ ha _ hb2 (two_eq hz)
      have h10 : (1 : Fin (n+1)) = 0 := by simpa using this
      exact one_ne_zero h10
  · rw [Finset.card_compl, Fintype.card_fin]
    omega


def Lm (n : ℕ) (s a : Fin (n+1)) : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] (Fin (n+1) → ZMod 2) where
  toFun x j := x (j - s) + x (j + a - s) + x (j - a - s)
  map_add' x y := by funext j; simp only [Pi.add_apply]; ring
  map_smul' r x := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Lm_apply (n : ℕ) (s a : Fin (n+1)) (x : Fin (n+1) → ZMod 2) (j : Fin (n+1)) :
    Lm n s a x j = x (j - s) + x (j + a - s) + x (j - a - s) := rfl

def Yf (n : ℕ) (s a : Fin (n+1)) (j : Fin (n+1)) : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj j) ∘ₗ Lm n s a

theorem Yf_apply (n : ℕ) (s a : Fin (n+1)) (j : Fin (n+1)) (x : Fin (n+1) → ZMod 2) :
    Yf n s a j x = x (j - s) + x (j + a - s) + x (j - a - s) := rfl

theorem kernel {n : ℕ} (h3 : (n+1) % 3 ≠ 0) (a : Fin (n+1)) (z : Fin (n+1) → ZMod 2)
    (hz : ∀ j, z j + z (j + a) + z (j - a) = 0) : ∀ j, z j = 0 := by
  have e1 : ∀ p q r : ZMod 2, p + q + r = 0 → q = p + r := by decide
  have e2 : ∀ p q : ZMod 2, p + q + p = q := by decide
  have e3 : ∀ p q : ZMod 2, p + p + q = 0 → q = 0 := by decide
  have s1 : ∀ j, z (j + a) = z j + z (j - a) := fun j => e1 _ _ _ (hz j)
  have s2 : ∀ j, z (j + a + a) = z (j - a) := by
    intro j
    rw [s1 (j + a), add_sub_cancel_right, s1 j, e2]
  have s3 : ∀ j, z (j + a + a + a) = z j := by
    intro j
    rw [s2 (j + a), add_sub_cancel_right]
  have s4 : ∀ m : ℕ, ∀ j, z (j + ((3 * m : ℕ) : Fin (n+1)) * a) = z j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      have : j + ((3 * (m + 1) : ℕ) : Fin (n+1)) * a =
          j + ((3 * m : ℕ) : Fin (n+1)) * a + a + a + a := by push_cast; ring
      rw [this, s3, ih]
  have hcop : Nat.Coprime 3 (n+1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨c, hc⟩; omega
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (by omega)
  have hm1 : ((3 * m : ℕ) : Fin (n+1)) = 1 := by
    apply Fin.ext
    rw [Fin.val_natCast, hm, Fin.val_one']
  have s5 : ∀ j, z (j + a) = z j := by
    intro j
    have := s4 m j
    rw [hm1, one_mul] at this
    exact this
  have s6 : ∀ j, z (j - a) = 0 := by
    intro j
    have := hz j
    rw [s5 j] at this
    exact e3 _ _ this
  intro j
  have := s6 (j + a)
  rwa [add_sub_cancel_right] at this

theorem Lm_inj {n : ℕ} (h3 : (n+1) % 3 ≠ 0) (s a : Fin (n+1)) :
    Function.Injective (Lm n s a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hz := kernel h3 a (fun j => x (j - s)) (fun j => by
    have := congrFun hx j
    rwa [Lm_apply] at this)
  funext i
  have := hz (i + s)
  simp only [add_sub_cancel_right] at this
  exact this

theorem span_top {n : ℕ} (L G : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] (Fin (n+1) → ZMod 2))
    (hG : ∀ x, G (L x) = x) :
    Submodule.span (ZMod 2) (Set.range (fun j : Fin (n+1) =>
      (LinearMap.proj j : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2) ∘ₗ L)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  have key : f = ∑ j, (f (G (fun i => if j = i then 1 else 0))) •
      ((LinearMap.proj j : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2) ∘ₗ L) := by
    apply LinearMap.ext
    intro x
    calc f x = (f ∘ₗ G) (L x) := by simp [hG]
      _ = _ := LinearMap.pi_apply_eq_sum_univ _ _
      _ = _ := by simp [LinearMap.sum_apply, mul_comm]
  rw [key]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem add_self2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (y : M) : y + y = 0 := by
  rw [← two_smul (ZMod 2) y]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

def eta (n : ℕ) (name : Fin (n+1) → ZMod 2) (a : Fin (n+1)) (j : Fin (n+1)) : ZMod 2 :=
  name j + name (j + a) + name (j - a)

def Af (n : ℕ) (S : Finset (Fin (n+1))) (s a : Fin (n+1)) (i : Fin (n+1)) :
    (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 := if i ∈ S then Yf n s a (i+1) else 0

def Bf (n : ℕ) (S : Finset (Fin (n+1))) (s a : Fin (n+1)) (i : Fin (n+1)) :
    (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 := if i ∈ S then Yf n s a (i+1+1) else 0

def Cf (n : ℕ) (S : Finset (Fin (n+1))) (s a t : Fin (n+1)) (i : Fin (n+1)) :
    (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if i ∈ S then Yf n s a i + LinearMap.proj (i - t) else 0

def Uf (n : ℕ) (S : Finset (Fin (n+1))) (name : Fin (n+1) → ZMod 2) (a : Fin (n+1))
    (i : Fin (n+1)) : ZMod 2 := if i ∈ S then 1 + eta n name a (i+1) else 0

def Vf (n : ℕ) (S : Finset (Fin (n+1))) (name : Fin (n+1) → ZMod 2) (a : Fin (n+1))
    (i : Fin (n+1)) : ZMod 2 := if i ∈ S then eta n name a (i+1+1) else 0

def Ef (n : ℕ) (S : Finset (Fin (n+1))) (name c : Fin (n+1) → ZMod 2) (a : Fin (n+1))
    (i : Fin (n+1)) : ZMod 2 := if i ∈ S then eta n name a i + c i else 0

theorem finrank_D (n : ℕ) :
    Module.finrank (ZMod 2) ((Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2) = n + 1 := by
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_self, mul_one]

theorem mu_zero (S : Finset (Fin (0+1))) : muN S = 0 := by
  obtain ⟨E, -, hi, he⟩ := mu_att S
  rw [← he, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro i hiE
  have e : i + 1 = i := Fin.ext (by have := (i+1).isLt; have := i.isLt; omega)
  exact hi i hiE (by rwa [e])

end PEqualNP.Outside.L_meta_25802

open Finset Fin.CommRing PEqualNP.Outside.L_meta_25802 in
theorem PEqualNP.Outside.L_meta_25802 :
let productCriterion : Prop :=
  ∀ (n t d : ℕ),
    let F := ZMod 2
    let V := Fin n → F
    let D := V →ₗ[F] F
    ∀ (a b c : Fin t → D) (u v e : Fin t → F),
      let target := fun (i : Fin t) (x : V) =>
        (a i x + u i) * (b i x + v i) + c i x + e i
      let run := fun (ask : Fin d → ℕ → D) (x : V) =>
        (List.finRange d).foldl (fun h j =>
          2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
      (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin t → D)
          (bias : ℕ → Fin t → F),
        ∀ x i, target i x = readout (run ask x) i x + bias (run ask x) i) ↔
      (∃ pick : Fin t → D,
        (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
        Module.finrank F (Submodule.span F (Set.range pick)) ≤ d)
let conclusion : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), k % 3 ≠ 0 →
    let F := ZMod 2
    let W := Fin k → F
    let D := W →ₗ[F] F
    let ix := fun z : ℕ => (⟨z % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (q : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - q % k))
    ∀ (spacing s t : ℕ) (name c : W) (S : Finset (Fin k)) (d : ℕ),
      let out := fun (x : W) (i : Fin k) =>
        let z := rot s x + name
        let y := fun j : Fin k =>
          z j + z (ix (j.val + spacing)) + z (ix (j.val + k - spacing % k))
        y i + (1 + y (ix (i.val + 1))) * y (ix (i.val + 2)) + rot t x i + c i
      let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix (i.val + 1) ∉ E)).sup Finset.card
      let run := fun (ask : Fin d → ℕ → D) (x : W) =>
        (List.finRange d).foldl (fun h j =>
          2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
      let cost := if S = Finset.univ ∧ 1 < k ∧ k % 2 = 1 then mu + 1 else mu
      (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin k → D) (bias : ℕ → Fin k → F),
        ∀ x, ∀ i ∈ S, out x i = readout (run ask x) i x + bias (run ask x) i) ↔
        cost ≤ d
productCriterion → conclusion := by
  intro pc concl hcrit k hk h3
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  intro F W D ix rot sp s t name c S d out mu run cost
  have hcast : ∀ z : ℕ, ix z = (z : Fin (n+1)) := fun z => Fin.ext (by simp [ix, Fin.val_natCast])
  have hA : ∀ i : Fin (n+1), ix (i.val + 1) = i + 1 := by
    intro i; rw [hcast]; push_cast; rfl
  have hB : ∀ i : Fin (n+1), ix (i.val + 2) = i + 1 + 1 := by
    intro i; rw [hcast]; push_cast; first | rfl | ring
  have hC : ∀ i : Fin (n+1), ix (i.val + sp) = i + (sp : Fin (n+1)) := by
    intro i; rw [hcast]; push_cast; first | rfl | simp
  have hD : ∀ (i : Fin (n+1)) (q : ℕ), ix (i.val + (n+1) - q % (n+1)) = i - (q : Fin (n+1)) := by
    intro i q
    apply Fin.ext
    rw [Fin.val_sub]
    simp only [ix, Fin.val_natCast]
    have := Nat.mod_lt q (show 0 < n + 1 by omega)
    congr 1
    omega
  have hout : ∀ x i, out x i =
      (Yf n (s : Fin (n+1)) (sp : Fin (n+1)) (i+1) x + (1 + eta n name (sp : Fin (n+1)) (i+1))) *
      (Yf n (s : Fin (n+1)) (sp : Fin (n+1)) (i+1+1) x + eta n name (sp : Fin (n+1)) (i+1+1)) +
      (Yf n (s : Fin (n+1)) (sp : Fin (n+1)) i x + x (i - (t : Fin (n+1)))) +
      (eta n name (sp : Fin (n+1)) i + c i) := by
    intro x i
    have hpa : ∀ (f g : W) j, (f + g) j = f j + g j := fun _ _ _ => rfl
    simp only [out, rot, hA, hB, hC, hD, Yf_apply, eta, hpa]
    ring
  have hmu : mu = muN S := by
    show (S.powerset.filter _).sup Finset.card = _
    unfold muN
    congr 1
    apply Finset.filter_congr
    intro E _
    simp only [hA]
  have hcost : cost = (if S = Finset.univ ∧ 1 < n + 1 ∧ (n + 1) % 2 = 1 then muN S + 1
      else muN S) := by
    show (if _ then mu + 1 else mu) = _
    rw [hmu]
  have hc := hcrit (n+1) (n+1) d (Af n S (s : Fin (n+1)) (sp : Fin (n+1)))
    (Bf n S (s : Fin (n+1)) (sp : Fin (n+1)))
    (Cf n S (s : Fin (n+1)) (sp : Fin (n+1)) (t : Fin (n+1)))
    (Uf n S name (sp : Fin (n+1))) (Vf n S name (sp : Fin (n+1)))
    (Ef n S name c (sp : Fin (n+1)))
  dsimp only at hc
  have hdim := finrank_D n
  rw [hcost]
  constructor
  · rintro ⟨ask, ro, bi, h⟩
    obtain ⟨pick, hp1, hp2⟩ := hc.1 ⟨ask, fun h i => if i ∈ S then ro h i else 0,
      fun h i => if i ∈ S then bi h i else 0, by
        intro x i
        by_cases hi : i ∈ S
        · simp only [if_pos hi]
          refine Eq.trans ?_ (h x i hi)
          rw [hout x i]
          simp only [Af, Bf, Cf, Uf, Vf, Ef, if_pos hi, LinearMap.add_apply, LinearMap.proj_apply]
        · simp [hi, Af, Bf, Cf, Uf, Vf, Ef]⟩
    by_cases hn : n = 0
    · subst hn
      rw [if_neg (fun h => absurd h.2.1 (by omega)), mu_zero]
      exact Nat.zero_le _
    · have hY : Submodule.span (ZMod 2) (Set.range (Yf n (s : Fin (n+1)) (sp : Fin (n+1)))) = ⊤ := by
        have hinj := Lm_inj h3 (s : Fin (n+1)) (sp : Fin (n+1))
        set Le := LinearEquiv.ofInjectiveEndo _ hinj
        exact span_top (Lm n (s : Fin (n+1)) (sp : Fin (n+1))) Le.symm.toLinearMap
          (fun x => Le.symm_apply_apply x)
      obtain ⟨U, hU, hUc⟩ := lin_lower (by omega) hdim (Yf n (s : Fin (n+1)) (sp : Fin (n+1))) hY
        (Submodule.span (ZMod 2) (Set.range pick)) S pick
        (fun i => Submodule.subset_span ⟨i, rfl⟩) (by
          intro i hi
          have := hp1 i
          simp only [Af, Bf, if_pos hi] at this
          exact this)
      exact (lower_cost hU).trans (hUc.trans hp2)
  · intro hd
    refine (fun H => ?_) (hc.2 ?_)
    · obtain ⟨ask, ro, bi, h⟩ := H
      refine ⟨ask, ro, bi, fun x i hi => Eq.trans ?_ (h x i)⟩
      rw [hout x i]
      simp only [Af, Bf, Cf, Uf, Vf, Ef, if_pos hi, LinearMap.add_apply, LinearMap.proj_apply]
    by_cases hn : n = 0
    · subst hn
      refine ⟨fun i => Af 0 S (s : Fin (0+1)) (sp : Fin (0+1)) i +
        Bf 0 S (s : Fin (0+1)) (sp : Fin (0+1)) i, fun i => Or.inr (Or.inr rfl), ?_⟩
      have hz : ∀ i : Fin (0+1), Af 0 S (s : Fin (0+1)) (sp : Fin (0+1)) i +
          Bf 0 S (s : Fin (0+1)) (sp : Fin (0+1)) i = 0 := by
        intro i
        have e : i + 1 + 1 = i + 1 := Fin.ext (by have := (i+1+1).isLt; have := (i+1).isLt; omega)
        simp only [Af, Bf, e]
        exact add_self2 _
      rw [Submodule.span_eq_bot.2 (by rintro _ ⟨i, rfl⟩; exact hz i), finrank_bot]
      exact Nat.zero_le _
    · obtain ⟨U, hU, hUc⟩ := upper_cost (by omega) S
      refine ⟨fun i => if i + 1 ∈ U then Af n S (s : Fin (n+1)) (sp : Fin (n+1)) i
        else Bf n S (s : Fin (n+1)) (sp : Fin (n+1)) i, ?_, ?_⟩
      · intro i
        by_cases h : i + 1 ∈ U
        · left; simp only [if_pos h]
        · right; left; simp only [if_neg h]
      · have hle : Submodule.span (ZMod 2) (Set.range (fun i => if i + 1 ∈ U then
            Af n S (s : Fin (n+1)) (sp : Fin (n+1)) i
            else Bf n S (s : Fin (n+1)) (sp : Fin (n+1)) i)) ≤
            Submodule.span (ZMod 2) ((U.image (Yf n (s : Fin (n+1)) (sp : Fin (n+1))) :
              Finset ((Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2)) :
              Set ((Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2)) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          by_cases hi : i ∈ S
          · by_cases h : i + 1 ∈ U
            · simp only [if_pos h, Af, if_pos hi]
              exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ h))
            · have h2 : i + 1 + 1 ∈ U := (hU i hi).resolve_left h
              simp only [if_neg h, Bf, if_pos hi]
              exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ h2))
          · by_cases h : i + 1 ∈ U
            · simp only [if_pos h, Af, if_neg hi]
              exact Submodule.zero_mem _
            · simp only [if_neg h, Bf, if_neg hi]
              exact Submodule.zero_mem _
        calc _ ≤ _ := Submodule.finrank_mono hle
          _ ≤ (U.image (Yf n (s : Fin (n+1)) (sp : Fin (n+1)))).card :=
            finrank_span_finset_le_card _
          _ ≤ U.card := Finset.card_image_le
          _ ≤ _ := hUc
          _ ≤ d := hd
