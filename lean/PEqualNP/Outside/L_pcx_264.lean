import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_264

abbrev FF := ZMod 2

def low (k d : ℕ) : Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)

def inD (k d : ℕ) (f : (Fin k → FF) → FF) : Prop :=
  ∃ coeff : Finset (Fin k) → FF, ∀ y : (Fin k → FF),
    (∑ S ∈ low k d, coeff S * ∏ j ∈ S, y j) = f y

lemma lowCard (k d : ℕ) :
    (low k d).card = ∑ j ∈ Finset.range (min k d + 1), k.choose j := by
  rw [low, Finset.card_eq_sum_card_fiberwise
      (f := Finset.card) (t := Finset.range (min k d + 1))]
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hset : ((Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).filter
        (fun S => S.card = j)) = Finset.powersetCard j (Finset.univ) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · intro hS
        exact hS.2
      · intro hS
        refine ⟨?_, hS⟩
        rw [hS]
        exact le_trans hj (min_le_right _ _)
    rw [hset, Finset.card_powersetCard, Finset.card_fin]
  · intro S hS
    have h2 : S.card ≤ d := by simpa [low] using hS
    simp only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact le_min (by simpa using Finset.card_le_univ S) h2

lemma card_le_of_delta {k d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → (Fin k → FF) → FF) (pt : ι → (Fin k → FF))
    (hdelta : ∀ i j : ι, f i (pt j) = if i = j then 1 else 0)
    (hmem : ∀ i, inD k d (f i)) : Fintype.card ι ≤ (low k d).card := by
  choose coeff hcoeff using hmem
  set g : (ι → FF) → (↥(low k d) → FF) := fun c S => ∑ i, c i * coeff i S.1 with hg
  have hinj : Function.Injective g := by
    intro c c1 hcc
    have hco : ∀ S ∈ low k d, (∑ i, c i * coeff i S) = ∑ i, c1 i * coeff i S := by
      intro S hS
      have := congrFun hcc ⟨S, hS⟩
      simpa [hg] using this
    have key : ∀ y, (∑ i, c i * f i y) = ∑ i, c1 i * f i y := by
      intro y
      have expand : ∀ e : ι → FF,
          (∑ i, e i * f i y) = ∑ S ∈ low k d, (∑ i, e i * coeff i S) * (∏ j ∈ S, y j) := by
        intro e
        calc (∑ i, e i * f i y)
            = ∑ i, ∑ S ∈ low k d, e i * (coeff i S * ∏ j ∈ S, y j) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                rw [← hcoeff i y, Finset.mul_sum]
          _ = ∑ S ∈ low k d, ∑ i, e i * (coeff i S * ∏ j ∈ S, y j) := Finset.sum_comm
          _ = ∑ S ∈ low k d, (∑ i, e i * coeff i S) * (∏ j ∈ S, y j) := by
                refine Finset.sum_congr rfl ?_
                intro S _
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
      rw [expand c, expand c1]
      exact Finset.sum_congr rfl (fun S hS => by rw [hco S hS])
    funext j
    have hkey := key (pt j)
    simp only [hdelta, mul_ite, mul_one, mul_zero] at hkey
    simpa using hkey
  have hle := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_fun, Fintype.card_coe, ZMod.card] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

lemma classBound {k r c : ℕ}
    (send : ((Fin k → FF) × (Fin r → FF)) → (Fin k → FF))
    (tag : ((Fin k → FF) × (Fin r → FF)) → Fin c → Bool)
    (H : ∀ a b t : ((Fin k → FF) × (Fin r → FF)),
      a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t)
    (d : ℕ)
    (hspan : ∀ u : Fin k → FF, inD k d (fun y =>
      if y ∈ Finset.univ.image (fun z : Fin r → FF => send (u, z)) then (1 : FF) else 0))
    (h : Fin c → Bool) :
    (Finset.univ.filter (fun w : ((Fin k → FF) × (Fin r → FF)) => tag w = h)).card
      ≤ (low k d).card := by
  classical
  set T := Finset.univ.filter (fun w : ((Fin k → FF) × (Fin r → FF)) => tag w = h) with hTdef
  have hTtag : ∀ w ∈ T, tag w = h := by
    intro w hw
    simpa [hTdef] using hw
  have hfst : ∀ a ∈ T, ∀ b ∈ T, a.1 = b.1 → a = b := by
    intro a ha b hb hab
    exact (H a b b hab rfl (by rw [hTtag b hb, hTtag a ha])).1
  set U := T.image Prod.fst with hUdef
  have hcardU : U.card = T.card :=
    Finset.card_image_of_injOn (fun a ha b hb hab => hfst a ha b hb hab)
  have hex : ∀ i : ↥U, ∃ w, w ∈ T ∧ w.1 = (i : Fin k → FF) := by
    intro i
    obtain ⟨w, hw, hw2⟩ := Finset.mem_image.mp i.2
    exact ⟨w, hw, hw2⟩
  choose w hwT hw1 using hex
  have hdelta : ∀ i j : ↥U,
      (fun y => if y ∈ Finset.univ.image (fun z : Fin r → FF => send ((i : Fin k → FF), z))
        then (1 : FF) else 0) (send (w j)) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hmem : send (w i) ∈
          Finset.univ.image (fun z : Fin r → FF => send ((i : Fin k → FF), z)) := by
        refine Finset.mem_image.mpr ⟨(w i).2, Finset.mem_univ _, ?_⟩
        rw [← hw1 i]
      simp [hmem]
    · have hnot : send (w j) ∉
          Finset.univ.image (fun z : Fin r → FF => send ((i : Fin k → FF), z)) := by
        intro hmem
        obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hmem
        have h2 := (H (w i) ((i : Fin k → FF), z) (w j) (hw1 i) hz
          (by rw [hTtag _ (hwT j), hTtag _ (hwT i)])).2
        apply hij
        apply Subtype.ext
        have h3 : ((i : Fin k → FF), z).1 = (w j).1 := by rw [h2]
        rw [hw1 j] at h3
        exact h3
      simp [hnot, hij]
  have hmain := card_le_of_delta
    (f := fun i : ↥U => fun y =>
      if y ∈ Finset.univ.image (fun z : Fin r → FF => send ((i : Fin k → FF), z))
        then (1 : FF) else 0)
    (pt := fun i : ↥U => send (w i)) hdelta (fun i => hspan _)
  rw [Fintype.card_coe] at hmain
  rw [← hcardU]
  exact hmain

lemma globalCount {k r c : ℕ} (tag : ((Fin k → FF) × (Fin r → FF)) → Fin c → Bool) (V : ℕ)
    (hb : ∀ h : Fin c → Bool,
      (Finset.univ.filter (fun w : ((Fin k → FF) × (Fin r → FF)) => tag w = h)).card ≤ V) :
    2 ^ (k + r) ≤ 2 ^ c * V := by
  classical
  have hpart : (Finset.univ : Finset ((Fin k → FF) × (Fin r → FF))).card
      = ∑ h : Fin c → Bool,
        (Finset.univ.filter (fun w : ((Fin k → FF) × (Fin r → FF)) => tag w = h)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  have hW : (Finset.univ : Finset ((Fin k → FF) × (Fin r → FF))).card = 2 ^ (k + r) := by
    simp [Finset.card_univ, Fintype.card_prod, pow_add]
  calc 2 ^ (k + r)
      = ∑ h : Fin c → Bool,
          (Finset.univ.filter (fun w : ((Fin k → FF) × (Fin r → FF)) => tag w = h)).card := by
        rw [← hpart, hW]
    _ ≤ ∑ _h : Fin c → Bool, V := Finset.sum_le_sum (fun h _ => hb h)
    _ = 2 ^ c * V := by
        simp [Finset.sum_const, Finset.card_univ]

lemma mem_low {k d : ℕ} {S : Finset (Fin k)} : S ∈ low k d ↔ S.card ≤ d := by
  simp [low]

lemma low_subset {k : ℕ} {d d' : ℕ} (h : d ≤ d') : low k d ⊆ low k d' := by
  intro S hS
  rw [mem_low] at hS ⊢
  exact hS.trans h

lemma ff_sq : ∀ x : FF, x * x = x := by decide


lemma inD_mono {k d d' : ℕ} {f : (Fin k → FF) → FF} (h : d ≤ d') (hf : inD k d f) :
    inD k d' f := by
  classical
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun S => if S ∈ low k d then c S else 0, ?_⟩
  intro y
  rw [← Finset.sum_subset (low_subset (k := k) h) (fun S _ hS => by simp [hS])]
  refine (Finset.sum_congr rfl ?_).trans (hc y)
  intro S hS
  simp [hS]


lemma inD_const (k : ℕ) (c : FF) : inD k 0 (fun _ => c) := by
  classical
  refine ⟨fun _ => c, ?_⟩
  intro y
  have h0 : low k 0 = {(∅ : Finset (Fin k))} := by
    ext S
    simp [mem_low, Finset.card_eq_zero]
  rw [h0]
  simp


lemma low_one_eq (k : ℕ) :
    low k 1 =
      insert (∅ : Finset (Fin k))
        (Finset.univ.image (fun j : Fin k => ({j} : Finset (Fin k)))) := by
  classical
  ext S
  simp only [mem_low, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · exact Or.inl (Finset.card_eq_zero.mp h0)
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      exact Or.inr ⟨a, ha.symm⟩
  · rintro (rfl | ⟨a, rfl⟩)
    · simp
    · simp

lemma sum_low_one {k : ℕ} (coeff : Finset (Fin k) → FF) (y : Fin k → FF) :
    (∑ S ∈ low k 1, coeff S * ∏ j ∈ S, y j)
      = coeff ∅ + ∑ j : Fin k, coeff {j} * y j := by
  classical
  rw [low_one_eq]
  rw [Finset.sum_insert (by simp)]
  rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  simp

lemma inD_affine {k : ℕ} (φ : (Fin k → FF) →ₗ[FF] FF) (c : FF) :
    inD k 1 (fun y => φ y + c) := by
  classical
  refine ⟨fun S => if S = ∅ then c else ∑ j ∈ S, if S = {j} then φ (Pi.single j 1) else 0, ?_⟩
  intro y
  rw [sum_low_one]
  have e1 : (if (∅ : Finset (Fin k)) = ∅ then c
      else ∑ j ∈ (∅ : Finset (Fin k)), if (∅ : Finset (Fin k)) = {j} then φ (Pi.single j 1) else 0)
      = c := by simp
  have e2 : ∀ j₀ : Fin k,
      (if ({j₀} : Finset (Fin k)) = ∅ then c
        else ∑ j ∈ ({j₀} : Finset (Fin k)), if ({j₀} : Finset (Fin k)) = {j} then φ (Pi.single j 1) else 0)
      = φ (Pi.single j₀ 1) := by
    intro j₀; simp
  rw [e1]
  rw [Finset.sum_congr rfl (fun j _ => by rw [e2 j])]
  show c + ∑ j : Fin k, φ (Pi.single j 1) * y j = φ y + c
  rw [φ.pi_apply_eq_sum_univ y]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_eq_mul, mul_comm]
  have hps : (Pi.single j (1 : FF)) = (fun j' => if j = j' then (1 : FF) else 0) := by
    funext j'
    rw [Pi.single_apply]
    by_cases hj : j = j'
    · simp [hj]
    · simp [hj, Ne.symm hj]
  rw [hps]


lemma ff_prod_absorb {k : ℕ} (y : Fin k → FF) {i : Fin k} {T : Finset (Fin k)} (hiT : i ∈ T) :
    y i * ∏ j ∈ T, y j = ∏ j ∈ T, y j := by
  classical
  rw [← Finset.prod_erase_mul T y hiT]
  calc y i * ((∏ j ∈ T.erase i, y j) * y i)
      = (∏ j ∈ T.erase i, y j) * (y i * y i) := by ring
    _ = (∏ j ∈ T.erase i, y j) * y i := by rw [ff_sq]

lemma ff_prod_union {k : ℕ} (y : Fin k → FF) (T : Finset (Fin k)) :
    ∀ S : Finset (Fin k), (∏ j ∈ S, y j) * (∏ j ∈ T, y j) = ∏ j ∈ S ∪ T, y j := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.insert_union]
      by_cases hmem : i ∈ s ∪ T
      · rw [Finset.insert_eq_self.mpr hmem, ← ih]
        have hiT : i ∈ T := by
          rcases Finset.mem_union.mp hmem with h | h
          · exact absurd h hi
          · exact h
        calc y i * (∏ j ∈ s, y j) * ∏ j ∈ T, y j
            = (∏ j ∈ s, y j) * (y i * ∏ j ∈ T, y j) := by ring
          _ = (∏ j ∈ s, y j) * ∏ j ∈ T, y j := by rw [ff_prod_absorb y hiT]
      · rw [Finset.prod_insert hmem, ← ih]
        ring

lemma inD_mul {k a b : ℕ} {f g : (Fin k → FF) → FF} (hf : inD k a f) (hg : inD k b g) :
    inD k (a + b) (fun y => f y * g y) := by
  classical
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨cg, hcg⟩ := hg
  refine ⟨fun U => ∑ p ∈ (low k a ×ˢ low k b).filter (fun p => p.1 ∪ p.2 = U), cf p.1 * cg p.2, ?_⟩
  intro y
  have hmaps : ∀ p ∈ low k a ×ˢ low k b, p.1 ∪ p.2 ∈ low k (a + b) := by
    intro p hp
    rw [Finset.mem_product] at hp
    rw [mem_low]
    exact le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add (mem_low.mp hp.1) (mem_low.mp hp.2))
  calc (∑ U ∈ low k (a + b),
          (∑ p ∈ (low k a ×ˢ low k b).filter (fun p => p.1 ∪ p.2 = U), cf p.1 * cg p.2)
            * ∏ j ∈ U, y j)
      = ∑ U ∈ low k (a + b), ∑ p ∈ (low k a ×ˢ low k b).filter (fun p => p.1 ∪ p.2 = U),
            (cf p.1 * cg p.2 * ∏ j ∈ p.1 ∪ p.2, y j) := by
        refine Finset.sum_congr rfl (fun U _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ p ∈ low k a ×ˢ low k b, (cf p.1 * cg p.2 * ∏ j ∈ p.1 ∪ p.2, y j) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = (∑ S ∈ low k a, cf S * ∏ j ∈ S, y j) * (∑ T ∈ low k b, cg T * ∏ j ∈ T, y j) := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← ff_prod_union y p.2 p.1]
        ring
    _ = f y * g y := by rw [hcf, hcg]


lemma inD_prod_aux {k : ℕ} : ∀ (m : ℕ) (fs : Fin m → ((Fin k → FF) → FF)),
    (∀ i, inD k 1 (fs i)) → inD k m (fun y => ∏ i, fs i y) := by
  intro m
  induction m with
  | zero =>
      intro fs _
      simpa using inD_const k 1
  | succ n ih =>
      intro fs h
      have hhead : inD k 1 (fs 0) := h 0
      have htail : inD k n (fun y => ∏ i : Fin n, fs i.succ y) :=
        ih (fun i => fs i.succ) (fun i => h i.succ)
      have hfun : (fun y => ∏ i : Fin (n + 1), fs i y)
          = (fun y : Fin k → FF => fs 0 y * ∏ i : Fin n, fs i.succ y) := by
        funext y
        rw [Fin.prod_univ_succ]
      rw [hfun]
      exact inD_mono (by omega) (inD_mul hhead htail)

lemma inD_prod {k m : ℕ} (fs : Fin m → ((Fin k → FF) → FF)) (h : ∀ i, inD k 1 (fs i)) :
    inD k m (fun y => ∏ i, fs i y) := inD_prod_aux m fs h


lemma inD_affine_image {k r : ℕ} (A : (Fin r → FF) →ₗ[FF] (Fin k → FF))
    (hA : Function.Injective A) (v : Fin k → FF) :
    inD k (k - r) (fun y => if y ∈ Finset.univ.image (fun z : Fin r → FF => A z + v) then (1 : FF) else 0) := by
  classical
  set W := LinearMap.range A with hW
  have hk : Module.finrank FF (Fin k → FF) = k := Module.finrank_fin_fun FF
  have hr : Module.finrank FF W = r := by
    rw [hW, LinearMap.finrank_range_of_inj hA]
    exact Module.finrank_fin_fun FF
  have hsum := Submodule.finrank_quotient_add_finrank W
  have hq : Module.finrank FF ((Fin k → FF) ⧸ W) = k - r := by
    rw [hk, hr] at hsum
    omega
  let b := Module.finBasisOfFinrankEq FF ((Fin k → FF) ⧸ W) hq
  let P : (Fin k → FF) →ₗ[FF] (Fin (k - r) → FF) :=
    (b.equivFun : ((Fin k → FF) ⧸ W) ≃ₗ[FF] (Fin (k - r) → FF)).toLinearMap.comp W.mkQ
  have hker : ∀ x : Fin k → FF, P x = 0 ↔ x ∈ W := by
    intro x
    have h1 : P x = b.equivFun (W.mkQ x) := rfl
    rw [h1, show (0 : Fin (k - r) → FF) = b.equivFun 0 from (map_zero _).symm,
      b.equivFun.injective.eq_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hmem : ∀ y : Fin k → FF,
      (y ∈ Finset.univ.image (fun z : Fin r → FF => A z + v)) ↔ P y = P v := by
    intro y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, rfl⟩
      have h0 : P (A z) = 0 := (hker _).mpr (LinearMap.mem_range.mpr ⟨z, rfl⟩)
      rw [map_add, h0, zero_add]
    · intro h
      have h0 : P (y - v) = 0 := by rw [map_sub, h, sub_self]
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp ((hker _).mp h0)
      exact ⟨z, by rw [hz]; abel⟩
  have hfs : ∀ i : Fin (k - r), inD k 1 (fun y => P y i + (1 + P v i)) := by
    intro i
    exact inD_affine ((LinearMap.proj i).comp P) (1 + P v i)
  have hprod : inD k (k - r) (fun y => ∏ i : Fin (k - r), (P y i + (1 + P v i))) :=
    inD_prod (fun i y => P y i + (1 + P v i)) hfs
  have hfun : (fun y : Fin k → FF =>
        if y ∈ Finset.univ.image (fun z : Fin r → FF => A z + v) then (1 : FF) else 0)
      = (fun y : Fin k → FF => ∏ i : Fin (k - r), (P y i + (1 + P v i))) := by
    funext y
    by_cases h : P y = P v
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((hmem y).mpr h))]
      symm
      refine Finset.prod_eq_one (fun i _ => ?_)
      rw [h]
      generalize P v i = t
      revert t
      decide
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun hh => h ((hmem y).mp hh)))]
      symm
      obtain ⟨i, hi⟩ : ∃ i, P y i ≠ P v i := by
        by_contra hc
        exact h (funext fun i => not_not.mp (fun hni => hc ⟨i, hni⟩))
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      revert hi
      generalize P y i = s
      generalize P v i = t
      revert s t
      decide
  rw [hfun]
  exact hprod

end PEqualNP.Outside.L_pcx_264

theorem PEqualNP.Outside.L_pcx_264 : (∀ (k r c : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin r → F
  let W := X × Z
  ∀ (send : W → X) (tag : W → Fin c → Bool),
    (∀ a b t : W, a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t) →
    let volume := fun d : ℕ => ∑ j ∈ Finset.range (min k d + 1), k.choose j
    (∀ d : ℕ,
      (∀ u : X, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
          coeff S * ∏ j ∈ S, y j) =
        (if y ∈ Finset.univ.image (fun z : Z => send (u,z)) then (1 : F) else 0)) →
      (∀ h : Fin c → Bool, (Finset.univ.filter (fun w : W => tag w = h)).card ≤ volume d) ∧
      2^(k+r) ≤ 2^c * volume d) ∧
    ((∀ u : X, ∃ (A : Z →ₗ[F] X) (v : X), ∀ z : Z, send (u,z) = A z + v) →
      r ≤ k ∧ 2^(k+r) ≤ 2^c * volume (k-r))) := by
  intro k r c F X Z W send tag H volume
  have hvol : ∀ d : ℕ, volume d = (PEqualNP.Outside.L_pcx_264.low k d).card :=
    fun d => (PEqualNP.Outside.L_pcx_264.lowCard k d).symm
  have main : ∀ d : ℕ,
      (∀ u : Fin k → PEqualNP.Outside.L_pcx_264.FF,
        PEqualNP.Outside.L_pcx_264.inD k d (fun y =>
          if y ∈ Finset.univ.image (fun z : Fin r → PEqualNP.Outside.L_pcx_264.FF => send (u, z))
            then (1 : PEqualNP.Outside.L_pcx_264.FF) else 0)) →
      (∀ h : Fin c → Bool,
          (Finset.univ.filter (fun w : W => tag w = h)).card ≤ volume d) ∧
        2 ^ (k + r) ≤ 2 ^ c * volume d := by
    intro d hspan
    have hb : ∀ h : Fin c → Bool,
        (Finset.univ.filter (fun w : W => tag w = h)).card
          ≤ (PEqualNP.Outside.L_pcx_264.low k d).card :=
      fun h => PEqualNP.Outside.L_pcx_264.classBound send tag H d hspan h
    refine ⟨?_, ?_⟩
    · intro h
      rw [hvol d]
      exact hb h
    · rw [hvol d]
      exact PEqualNP.Outside.L_pcx_264.globalCount tag _ hb
  refine ⟨fun d hspan => main d hspan, ?_⟩
  intro haff
  have hrowinj : ∀ (u : Fin k → PEqualNP.Outside.L_pcx_264.FF)
      (z1 z2 : Fin r → PEqualNP.Outside.L_pcx_264.FF),
      send (u, z1) = send (u, z2) → z1 = z2 := by
    intro u z1 z2 hz
    have h2 := (H (u, z1) (u, z2) (u, z1) rfl hz.symm rfl).1
    exact congrArg Prod.snd h2
  have hinj : ∀ (u : Fin k → PEqualNP.Outside.L_pcx_264.FF)
      (A : (Fin r → PEqualNP.Outside.L_pcx_264.FF) →ₗ[PEqualNP.Outside.L_pcx_264.FF]
        (Fin k → PEqualNP.Outside.L_pcx_264.FF)) (v : Fin k → PEqualNP.Outside.L_pcx_264.FF),
      (∀ z, send (u, z) = A z + v) → Function.Injective A := by
    intro u A v hAv z1 z2 hz
    refine hrowinj u z1 z2 ?_
    rw [hAv z1, hAv z2, hz]
  obtain ⟨A, v, hA⟩ := haff (0 : Fin k → PEqualNP.Outside.L_pcx_264.FF)
  have hinjA : Function.Injective A :=
    hinj (0 : Fin k → PEqualNP.Outside.L_pcx_264.FF) A v hA
  have hrk : r ≤ k := by
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := A) hinjA
    have h2 : Module.finrank PEqualNP.Outside.L_pcx_264.FF
          (Fin r → PEqualNP.Outside.L_pcx_264.FF)
        ≤ Module.finrank PEqualNP.Outside.L_pcx_264.FF
          (Fin k → PEqualNP.Outside.L_pcx_264.FF) := h1
    simpa using h2
  refine ⟨hrk, ?_⟩
  refine (main (k - r) ?_).2
  intro u
  obtain ⟨A1, v1, hA1⟩ := haff u
  have himg : (Finset.univ.image
        (fun z : Fin r → PEqualNP.Outside.L_pcx_264.FF => send (u, z)))
      = (Finset.univ.image
        (fun z : Fin r → PEqualNP.Outside.L_pcx_264.FF => A1 z + v1)) := by
    refine Finset.image_congr ?_
    intro z _
    exact hA1 z
  rw [himg]
  exact PEqualNP.Outside.L_pcx_264.inD_affine_image A1
    (hinj u A1 v1 hA1) v1
