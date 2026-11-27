import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_lib_382

lemma coeff_X_pow_mul_pos (P : Polynomial ℕ) (m k : ℕ) :
    0 < (Polynomial.X ^ m * P).coeff k ↔ m ≤ k ∧ 0 < P.coeff (k - m) := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · exact ⟨fun hp => ⟨h, hp⟩, fun ⟨_, hp⟩ => hp⟩
  · exact ⟨fun hp => (Nat.lt_irrefl 0 hp).elim, fun ⟨hm, _⟩ => (h hm).elim⟩

lemma coeff_prod_add_X_pow_pos {α : Type*} [DecidableEq α] (s : Finset α) (a b : α → ℕ) :
    ∀ k : ℕ, 0 < (∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff k ↔
      ∃ f : α → Bool, (∑ i ∈ s, if f i then b i else a i) = k := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]
    constructor
    · intro h
      refine ⟨fun _ => false, ?_⟩
      by_cases hk : k = 0
      · exact hk.symm
      · simp [hk] at h
    · rintro ⟨_, rfl⟩
      simp
  | @insert x s hx ih =>
    intro k
    rw [Finset.prod_insert hx, add_mul, Polynomial.coeff_add]
    constructor
    · intro h
      have hdisj : 0 < (Polynomial.X ^ a x * ∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff k ∨
          0 < (Polynomial.X ^ b x * ∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff k := by
        omega
      rcases hdisj with h1 | h2
      · rw [coeff_X_pow_mul_pos] at h1
        obtain ⟨hle, hp⟩ := h1
        obtain ⟨f, hf⟩ := (ih (k - a x)).mp hp
        refine ⟨Function.update f x false, ?_⟩
        rw [Finset.sum_insert hx]
        simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte]
        have hsum : (∑ i ∈ s, if Function.update f x false i then b i else a i) =
            ∑ i ∈ s, if f i then b i else a i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ x := fun h => hx (h ▸ hi)
          simp [Function.update_of_ne hne]
        rw [hsum, hf]
        omega
      · rw [coeff_X_pow_mul_pos] at h2
        obtain ⟨hle, hp⟩ := h2
        obtain ⟨f, hf⟩ := (ih (k - b x)).mp hp
        refine ⟨Function.update f x true, ?_⟩
        rw [Finset.sum_insert hx]
        simp only [Function.update_self, ↓reduceIte]
        have hsum : (∑ i ∈ s, if Function.update f x true i then b i else a i) =
            ∑ i ∈ s, if f i then b i else a i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ x := fun h => hx (h ▸ hi)
          simp [Function.update_of_ne hne]
        rw [hsum, hf]
        omega
    · rintro ⟨f, hf⟩
      rw [Finset.sum_insert hx] at hf
      cases hfx : f x
      · simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hf
        have hle : a x ≤ k := by omega
        have hsub : (∑ i ∈ s, if f i then b i else a i) = k - a x := by omega
        have hp : 0 < (∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff (k - a x) :=
          (ih (k - a x)).mpr ⟨f, hsub⟩
        have h1 : 0 < (Polynomial.X ^ a x * ∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff k :=
          (coeff_X_pow_mul_pos _ _ _).mpr ⟨hle, hp⟩
        omega
      · simp only [hfx, ↓reduceIte] at hf
        have hle : b x ≤ k := by omega
        have hsub : (∑ i ∈ s, if f i then b i else a i) = k - b x := by omega
        have hp : 0 < (∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff (k - b x) :=
          (ih (k - b x)).mpr ⟨f, hsub⟩
        have h2 : 0 < (Polynomial.X ^ b x * ∏ i ∈ s, (Polynomial.X ^ a i + Polynomial.X ^ b i : Polynomial ℕ)).coeff k :=
          (coeff_X_pow_mul_pos _ _ _).mpr ⟨hle, hp⟩
        omega

lemma card_filter_lt_half (N : ℕ) :
    (Finset.univ.filter (fun w : Fin (2 * N) => w.val < N)).card = N := by
  let emb : Fin N ↪ Fin (2 * N) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  have heq : Finset.univ.filter (fun w : Fin (2 * N) => w.val < N) = Finset.univ.map emb := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hw
      exact ⟨⟨w.val, hw⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [heq, Finset.card_map, Finset.card_fin]

lemma card_filter_eq_sum_sides {N t : ℕ} (base : Fin (2 * N) → Bool) (comp : Fin (2 * N) → Fin t)
    (f : Fin t → Bool) :
    (Finset.univ.filter (fun v : Fin (2 * N) => base v = f (comp v))).card =
      ∑ c : Fin t, (Finset.univ.filter (fun v : Fin (2 * N) => comp v = c ∧ base v = f c)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := comp) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hb, hc⟩
    exact ⟨hc, hc ▸ hb⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc.symm ▸ hb, hc⟩

lemma bool_align_eq (b1 b2 c1 c2 : Bool) (hb : b1 ≠ b2) (hc : c1 ≠ c2) :
    (if c1 then b1 else !b1) = (if c2 then b2 else !b2) := by
  cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> simp_all

lemma bool_align_iff (b c : Bool) : (c = true) ↔ (b = if c then b else !b) := by
  cases b <;> cases c <;> simp

lemma perm_of_balanced_coloring (N : ℕ) (col : Fin (2 * N) → Bool)
    (hcard : (Finset.univ.filter (fun v : Fin (2 * N) => col v = true)).card = N) :
    ∃ π : Equiv.Perm (Fin (2 * N)), ∀ v, decide ((π v).val < N) = col v := by
  have hlt : (Finset.univ.filter (fun w : Fin (2 * N) => decide (w.val < N) = true)).card = N := by
    simpa [decide_eq_true_eq] using card_filter_lt_half N
  have hT : Fintype.card {v : Fin (2 * N) // col v = true} =
      Fintype.card {w : Fin (2 * N) // decide (w.val < N) = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hcard, hlt]
  have hF : Fintype.card {v : Fin (2 * N) // ¬ (col v = true)} =
      Fintype.card {w : Fin (2 * N) // ¬ (decide (w.val < N) = true)} := by
    have h1 := Fintype.card_subtype_compl (fun v : Fin (2 * N) => col v = true)
    have h2 := Fintype.card_subtype_compl (fun w : Fin (2 * N) => decide (w.val < N) = true)
    omega
  let e1 : {v : Fin (2 * N) // col v = true} ≃ {w : Fin (2 * N) // decide (w.val < N) = true} :=
    Fintype.equivOfCardEq hT
  let e2 : {v : Fin (2 * N) // ¬ (col v = true)} ≃ {w : Fin (2 * N) // ¬ (decide (w.val < N) = true)} :=
    Fintype.equivOfCardEq hF
  let π : Equiv.Perm (Fin (2 * N)) :=
    (Equiv.sumCompl (fun v : Fin (2 * N) => col v = true)).symm.trans
      ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (fun w : Fin (2 * N) => decide (w.val < N) = true)))
  refine ⟨π, fun v => ?_⟩
  by_cases hv : col v = true
  · have hsymm : (Equiv.sumCompl (fun u : Fin (2 * N) => col u = true)).symm v = Sum.inl ⟨v, hv⟩ :=
      (Equiv.sumCompl (fun u : Fin (2 * N) => col u = true)).symm_apply_eq.mpr rfl
    have hpi : π v = (e1 ⟨v, hv⟩).val := by
      dsimp only [π]
      rw [Equiv.trans_apply, Equiv.trans_apply, hsymm,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hpi, (e1 ⟨v, hv⟩).property, hv]
  · have hcolf : col v = false := by cases h : col v <;> simp_all
    have hsymm : (Equiv.sumCompl (fun u : Fin (2 * N) => col u = true)).symm v = Sum.inr ⟨v, hv⟩ :=
      (Equiv.sumCompl (fun u : Fin (2 * N) => col u = true)).symm_apply_eq.mpr rfl
    have hpi : π v = (e2 ⟨v, hv⟩).val := by
      dsimp only [π]
      rw [Equiv.trans_apply, Equiv.trans_apply, hsymm,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have hnot : ¬ (decide ((π v).val < N) = true) := by
      rw [hpi]
      exact (e2 ⟨v, hv⟩).property
    have hdecf : decide ((π v).val < N) = false := by
      cases h : decide ((π v).val < N)
      · rfl
      · exact (hnot h).elim
    rw [hdecf, hcolf]

end PEqualNP.Outside.L_lib_382

theorem PEqualNP.Outside.L_lib_382 : (∀ (n N t : ℕ) (left right : Fin n → Fin (2 * N))
  (base : Fin (2 * N) → Bool) (comp : Fin (2 * N) → Fin t),
  (∀ z, base (left z) ≠ base (right z)) →
  Function.Surjective comp →
  (∀ x y, comp x = comp y ↔
    Relation.EqvGen (fun u v => ∃ z, left z = u ∧ right z = v) x y) →
  let sides := fun (c : Fin t) (b : Bool) =>
    (Finset.univ.filter (fun v => comp v = c ∧ base v = b)).card
  let orientations : Polynomial ℕ :=
    ∏ c : Fin t, (Polynomial.X ^ (sides c false) + Polynomial.X ^ (sides c true))
  (∃ π : Equiv.Perm (Fin (2 * N)), ∀ z,
    decide ((π (left z)).val < N) ≠ decide ((π (right z)).val < N)) ↔
    0 < orientations.coeff N) := by
  intro n N t left right base comp hbase hsurj hcomp sides orientations
  dsimp only [orientations]
  rw [PEqualNP.Outside.L_lib_382.coeff_prod_add_X_pow_pos]
  constructor
  · rintro ⟨π, hπ⟩
    let col : Fin (2 * N) → Bool := fun v => decide ((π v).val < N)
    let align : Fin (2 * N) → Bool := fun v => if col v then base v else !base v
    have halign_eqv : ∀ x y, Relation.EqvGen (fun u v => ∃ z, left z = u ∧ right z = v) x y →
        align x = align y := by
      intro x y hxy
      induction hxy with
      | rel u v huv =>
        rcases huv with ⟨z, rfl, rfl⟩
        exact PEqualNP.Outside.L_lib_382.bool_align_eq (base (left z)) (base (right z))
          (col (left z)) (col (right z)) (hbase z) (hπ z)
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    let f : Fin t → Bool := fun c => align (Classical.choose (hsurj c))
    have hf_eq : ∀ v : Fin (2 * N), f (comp v) = align v := by
      intro v
      apply halign_eqv
      rw [← hcomp]
      exact Classical.choose_spec (hsurj (comp v))
    refine ⟨f, ?_⟩
    have hsum_eq : (∑ c : Fin t, if f c then sides c true else sides c false) =
        ∑ c : Fin t, sides c (f c) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      cases f c <;> rfl
    rw [hsum_eq]
    have hfib := PEqualNP.Outside.L_lib_382.card_filter_eq_sum_sides base comp f
    dsimp only [sides]
    rw [← hfib]
    have hfilt : Finset.univ.filter (fun v : Fin (2 * N) => base v = f (comp v)) =
        Finset.univ.filter (fun v : Fin (2 * N) => (π v).val < N) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf_eq v]
      rw [← PEqualNP.Outside.L_lib_382.bool_align_iff (base v) (col v)]
      simp [col]
    rw [hfilt]
    have hmap : (Finset.univ.filter (fun v : Fin (2 * N) => (π v).val < N)).card =
        (Finset.univ.filter (fun w : Fin (2 * N) => w.val < N)).card := by
      refine Finset.card_bij (fun v _ => π v) (fun v hv => ?_) (fun v1 _ v2 _ h => π.injective h) (fun w hw => ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact hv
      · refine ⟨π.symm w, ?_, π.apply_symm_apply w⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        simpa using hw
    rw [hmap, PEqualNP.Outside.L_lib_382.card_filter_lt_half]
  · rintro ⟨f, hf⟩
    have hsum_eq : (∑ c : Fin t, if f c then sides c true else sides c false) =
        ∑ c : Fin t, sides c (f c) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      cases f c <;> rfl
    rw [hsum_eq] at hf
    let col : Fin (2 * N) → Bool := fun v => decide (base v = f (comp v))
    have hcard : (Finset.univ.filter (fun v : Fin (2 * N) => col v = true)).card = N := by
      have h1 : Finset.univ.filter (fun v : Fin (2 * N) => col v = true) =
          Finset.univ.filter (fun v : Fin (2 * N) => base v = f (comp v)) := by
        ext v
        simp [col]
      rw [h1, PEqualNP.Outside.L_lib_382.card_filter_eq_sum_sides base comp f]
      exact hf
    obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_lib_382.perm_of_balanced_coloring N col hcard
    refine ⟨π, fun z => ?_⟩
    rw [hπ (left z), hπ (right z)]
    have hc : comp (left z) = comp (right z) :=
      (hcomp (left z) (right z)).mpr (Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩)
    dsimp only [col]
    rw [hc]
    have hb := hbase z
    cases h1 : base (left z) <;> cases h2 : base (right z) <;> cases h3 : f (comp (right z)) <;> simp_all
