import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47146

section Helpers

variable {r n : Nat}

def blockF (y : Finset (Fin r × Fin n)) (a : Fin r) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => (a, i) ∈ y)

lemma mem_blockF (y : Finset (Fin r × Fin n)) (a : Fin r) (i : Fin n) :
    i ∈ blockF y a ↔ (a, i) ∈ y := by
  simp [blockF]

def indep (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, edge a i j = false

def alphaF (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (x : Finset (Fin n)) : Nat :=
  (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, edge a i j = false)).sup Finset.card

lemma exists_max_indep (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (x : Finset (Fin n)) :
    ∃ s ⊆ x, indep edge a s ∧ s.card = alphaF edge a x := by
  let F := x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, edge a i j = false)
  have hne : F.Nonempty := ⟨∅, by simp [F]⟩
  obtain ⟨s, hsF, hmax⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hsF
  exact ⟨s, hsF.1, hsF.2, hmax.symm⟩

lemma card_le_alphaF (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r)
    {x s : Finset (Fin n)} (hsx : s ⊆ x) (hind : indep edge a s) :
    s.card ≤ alphaF edge a x := by
  unfold alphaF
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsx, hind⟩)

lemma alphaF_mono (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r)
    {x₁ x₂ : Finset (Fin n)} (hsub : x₁ ⊆ x₂) :
    alphaF edge a x₁ ≤ alphaF edge a x₂ := by
  obtain ⟨s, hsx, hind, hcard⟩ := exists_max_indep edge a x₁
  rw [← hcard]
  exact card_le_alphaF edge a (hsx.trans hsub) hind

lemma alphaF_insert_le (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r)
    (v : Fin n) (x : Finset (Fin n)) :
    alphaF edge a (insert v x) ≤ alphaF edge a x + 1 := by
  obtain ⟨s, hs, hind, hcard⟩ := exists_max_indep edge a (insert v x)
  have herase_sub : s.erase v ⊆ x := by
    intro u hu
    rcases Finset.mem_erase.mp hu with ⟨hne, hus⟩
    rcases Finset.mem_insert.mp (hs hus) with rfl | hux
    · exact absurd rfl hne
    · exact hux
  have herase_ind : indep edge a (s.erase v) := fun i hi j hj =>
    hind i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)
  have hle : (s.erase v).card ≤ alphaF edge a x := card_le_alphaF edge a herase_sub herase_ind
  by_cases hv : v ∈ s
  · have hc : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
    omega
  · have hc : s.erase v = s := Finset.erase_eq_of_notMem hv
    rw [hc] at hle
    omega

lemma alphaF_insert_eq_of_ne (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r)
    (v : Fin n) (x : Finset (Fin n))
    (hne : alphaF edge a (insert v x) ≠ alphaF edge a x + 1) :
    alphaF edge a (insert v x) = alphaF edge a x := by
  have h1 := alphaF_mono edge a (Finset.subset_insert v x)
  have h2 := alphaF_insert_le edge a v x
  omega

def rankF (edge : Fin r → Fin n → Fin n → Bool) (y : Finset (Fin r × Fin n)) : Nat :=
  ∑ a : Fin r, alphaF edge a (blockF y a)

def packF (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) :
    Nat → Finset (Fin r × Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin r × Fin n) → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset (Fin r × Fin n)) (k : Fin r × Fin n),
      prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)

lemma packF_mono_set (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    {m : Nat} {y₁ y₂ : Finset (Fin r × Fin n)} (hsub : y₁ ⊆ y₂) :
    packF f m y₁ → packF f m y₂ := by
  cases m with
  | zero => intro _; trivial
  | succ m =>
    rintro ⟨u, v, k, hu, huv, hvy, hfu, hfv⟩
    exact ⟨u, v, k, hu, huv, hvy.trans hsub, hfu, hfv⟩

lemma packF_pred (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    {m : Nat} {y : Finset (Fin r × Fin n)} :
    packF f (m + 1) y → packF f m y := by
  rintro ⟨u, v, k, hu, huv, hvy, _, _⟩
  exact packF_mono_set f (huv.trans hvy) hu

lemma packF_mono_nat (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    {m₁ m₂ : Nat} {y : Finset (Fin r × Fin n)} (hle : m₁ ≤ m₂) :
    packF f m₂ y → packF f m₁ y := by
  induction m₂ with
  | zero =>
    have : m₁ = 0 := by omega
    subst this; exact id
  | succ m₂ ih =>
    intro h
    by_cases heq : m₁ = m₂ + 1
    · subst heq; exact h
    · exact ih (by omega) (packF_pred f h)

lemma packF_indep_step (edge : Fin r → Fin n → Fin n → Bool)
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (hf1 : ∀ y a i, ((a, i) ∉ y ∧ ∀ k ∈ blockF y a, edge a k i = false) → f y (a, i) = true)
    (hf2 : ∀ y a i, (a, i) ∈ y → f y (a, i) = false)
    (a : Fin r) (u0 : Finset (Fin r × Fin n)) (hu0 : ∀ i : Fin n, (a, i) ∉ u0)
    (m : Nat) (hm : packF f m u0)
    (s : Finset (Fin n)) (hind : indep edge a s) :
    packF f (m + s.card) (u0 ∪ s.image (fun i => (a, i))) := by
  induction s using Finset.induction_on with
  | empty => simpa using hm
  | @insert v s hv ih =>
    have hind_s : indep edge a s := fun i hi j hj =>
      hind i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hprev : packF f (m + s.card) (u0 ∪ s.image (fun i => (a, i))) := ih hind_s
    let u := u0 ∪ s.image (fun i => (a, i))
    let w := u0 ∪ (insert v s).image (fun i => (a, i))
    have hnotu : (a, v) ∉ u := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hmem0 | hmemS
      · exact hu0 v hmem0
      · rcases Finset.mem_image.mp hmemS with ⟨i, his, heq⟩
        cases heq
        exact hv his
    have hnoedge : ∀ k ∈ blockF u a, edge a k v = false := by
      intro k hk
      rw [mem_blockF] at hk
      rcases Finset.mem_union.mp hk with hk0 | hkS
      · exact absurd hk0 (hu0 k)
      · rcases Finset.mem_image.mp hkS with ⟨i, his, heq⟩
        cases heq
        exact hind k (Finset.mem_insert_of_mem his) v (Finset.mem_insert_self v s)
    have hfu : f u (a, v) = true := hf1 u a v ⟨hnotu, hnoedge⟩
    have hvw : (a, v) ∈ w :=
      Finset.mem_union_right u0 (Finset.mem_image.mpr ⟨v, Finset.mem_insert_self v s, rfl⟩)
    have hfw : f w (a, v) = false := hf2 w a v hvw
    have huw : u ⊆ w :=
      Finset.union_subset_union_right (Finset.image_subset_image (Finset.subset_insert v s))
    have hcard : m + (insert v s).card = (m + s.card) + 1 := by
      rw [Finset.card_insert_of_notMem hv]; omega
    rw [hcard]
    exact ⟨u, w, (a, v), hprev, huw, Finset.Subset.rfl, hfu, hfw⟩

def endAtF (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (ans : Fin r → Bool) (a : Fin r) : Finset (Fin n) :=
  if ans a then insert (j a) (x a) else x a

def queryF (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (ans : Fin r → Bool) (a : Fin r) : Finset (Fin r × Fin n) :=
  (Finset.univ : Finset (Fin r × Fin n)).filter (fun p =>
    (p.1 < a ∧ p.2 ∈ endAtF x j ans p.1) ∨ (p.1 = a ∧ p.2 ∈ x a))

lemma queryF_congr (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (ans₁ ans₂ : Fin r → Bool) (a : Fin r)
    (h : ∀ b : Fin r, b.val < a.val → ans₁ b = ans₂ b) :
    queryF x j ans₁ a = queryF x j ans₂ a := by
  ext ⟨b, i⟩
  simp only [queryF, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hba, hmem⟩ | ⟨rfl, hmem⟩)
    · left
      refine ⟨hba, ?_⟩
      unfold endAtF at hmem ⊢
      rwa [← h b hba]
    · exact Or.inr ⟨rfl, hmem⟩
  · rintro (⟨hba, hmem⟩ | ⟨rfl, hmem⟩)
    · left
      refine ⟨hba, ?_⟩
      unfold endAtF at hmem ⊢
      rwa [h b hba]
    · exact Or.inr ⟨rfl, hmem⟩

def buildAnsAux (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (k : Nat) (hk : k < r) : Bool :=
  let cur : Fin r → Bool := fun b =>
    if h : b.val < k then buildAnsAux f x j b.val (lt_trans h hk) else false
  f (queryF x j cur ⟨k, hk⟩) (⟨k, hk⟩, j ⟨k, hk⟩)
termination_by k

lemma buildAnsAux_eq (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (k : Nat) (hk : k < r) :
    buildAnsAux f x j k hk =
      f (queryF x j (fun b => if h : b.val < k then buildAnsAux f x j b.val (lt_trans h hk) else false)
          ⟨k, hk⟩) (⟨k, hk⟩, j ⟨k, hk⟩) := by
  rw [buildAnsAux]

lemma exists_unique_consistent
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) :
    ∃! ans : Fin r → Bool, ∀ a : Fin r, ans a = f (queryF x j ans a) (a, j a) := by
  let ans0 : Fin r → Bool := fun a => buildAnsAux f x j a.val a.isLt
  refine ⟨ans0, ?_, ?_⟩
  · intro a
    dsimp only [ans0]
    rw [buildAnsAux_eq]
    have hq : queryF x j (fun b => if h : b.val < a.val then
        buildAnsAux f x j b.val (lt_trans h a.isLt) else false) a =
        queryF x j ans0 a := by
      apply queryF_congr
      intro b hba
      simp [ans0, hba]
    have ha : (⟨a.val, a.isLt⟩ : Fin r) = a := Fin.eta a a.isLt
    rw [ha, hq]
  · intro ans hcons
    funext a
    have hstrong : ∀ k (hk : k < r), ans ⟨k, hk⟩ = ans0 ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        have h1 := hcons ⟨k, hk⟩
        have h2 : ans0 ⟨k, hk⟩ = f (queryF x j ans0 ⟨k, hk⟩) (⟨k, hk⟩, j ⟨k, hk⟩) := by
          dsimp only [ans0]
          rw [buildAnsAux_eq]
          congr 1
          apply queryF_congr
          intro b hbk
          simp [ans0, hbk]
        rw [h1, h2]
        congr 1
        apply queryF_congr
        intro b hbk
        exact ih b.val hbk b.isLt
    exact hstrong a.val a.isLt

lemma solve_47146 (r n : Nat) (edge : Fin r → Fin n → Fin n → Bool)
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (hf1 : ∀ y a i, ((a, i) ∉ y ∧ ∀ k ∈ blockF y a, edge a k i = false) → f y (a, i) = true)
    (hf2 : ∀ y a i, (a, i) ∈ y → f y (a, i) = false) :
    let gain := fun a => decide (alphaF edge a (insert (j a) (x a)) = alphaF edge a (x a) + 1)
    let consistent := fun (ans : Fin r → Bool) =>
      ∀ a, ans a = f (queryF x j ans a) (a, j a)
    (∃! ans, consistent ans) ∧
    ∀ ans, consistent ans →
      let y := (Finset.univ : Finset (Fin r × Fin n)).filter (fun p => p.2 ∈ endAtF x j ans p.1)
      let errors := (Finset.univ.filter (fun a : Fin r => ans a ≠ gain a)).card
      let ones := (Finset.univ.filter (fun a : Fin r => ans a = true)).card
      packF f (rankF edge y + errors) y ∧
      ∀ e : Nat, (∀ z, ¬ packF f (rankF edge z + e + 1) z) →
        errors ≤ e ∧ ∀ b : Bool, (∀ a, gain a = b) → 2 * e < r →
          decide (r < 2 * ones) = b := by
  intro gain consistent
  refine ⟨exists_unique_consistent f x j, ?_⟩
  intro ans hcons y errors ones
  let partY : Nat → Finset (Fin r × Fin n) := fun k =>
    (Finset.univ : Finset (Fin r × Fin n)).filter (fun p => p.1.val < k ∧ p.2 ∈ endAtF x j ans p.1)
  let partSet : Nat → Finset (Fin r) := fun k =>
    (Finset.univ : Finset (Fin r)).filter (fun a => a.val < k)
  let term : Fin r → Nat := fun a =>
    alphaF edge a (endAtF x j ans a) + if ans a ≠ gain a then 1 else 0
  let partScore : Nat → Nat := fun k => ∑ a ∈ partSet k, term a
  have hpart : ∀ k ≤ r, packF f (partScore k) (partY k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hs0 : partSet 0 = ∅ := by ext a; simp [partSet]
      have hsc0 : partScore 0 = 0 := by simp [partScore, hs0]
      rw [hsc0]; trivial
    | succ k ih =>
      intro hkr
      have hprev : packF f (partScore k) (partY k) := ih (by omega)
      let a : Fin r := ⟨k, by omega⟩
      have hset_eq : partSet (k + 1) = insert a (partSet k) := by
        ext b
        simp only [partSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, a]
        omega
      have ha_not : a ∉ partSet k := by simp [partSet, a]
      have hsc_eq : partScore (k + 1) = partScore k + term a := by
        simp only [partScore, hset_eq, Finset.sum_insert ha_not]
        omega
      have hu0 : ∀ i : Fin n, (a, i) ∉ partY k := by
        intro i hi
        simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and, a] at hi
        omega
      have hsub_end : ∀ s : Finset (Fin n), s ⊆ endAtF x j ans a →
          partY k ∪ s.image (fun i => (a, i)) ⊆ partY (k + 1) := by
        intro s hs p hp
        rcases Finset.mem_union.mp hp with hp0 | hpS
        · simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and] at hp0 ⊢
          exact ⟨by omega, hp0.2⟩
        · rcases Finset.mem_image.mp hpS with ⟨i, his, rfl⟩
          simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and, a]
          exact ⟨by omega, hs his⟩
      have hsub_q : ∀ s : Finset (Fin n), s ⊆ x a →
          partY k ∪ s.image (fun i => (a, i)) ⊆ queryF x j ans a := by
        intro s hs p hp
        rcases Finset.mem_union.mp hp with hp0 | hpS
        · simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and] at hp0
          simp only [queryF, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl ⟨by change p.1.val < a.val; simp [a]; exact hp0.1, hp0.2⟩
        · rcases Finset.mem_image.mp hpS with ⟨i, his, rfl⟩
          simp only [queryF, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr (hs his)
      have hq_sub : queryF x j ans a ⊆ partY (k + 1) := by
        intro p hp
        simp only [queryF, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hp with ⟨hpa, hmem⟩ | ⟨hpa, hmem⟩
        · have hlt : p.1.val < k := hpa
          exact ⟨by omega, hmem⟩
        · rw [hpa]
          refine ⟨by simp [a], ?_⟩
          unfold endAtF
          split
          · exact Finset.mem_insert_of_mem hmem
          · exact hmem
      rw [hsc_eq]
      dsimp only [term]
      cases ha_val : ans a <;> cases hg_val : gain a
      · -- ans a = false, gain a = false (no error)
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
        obtain ⟨s, hs, hind, hcard⟩ := exists_max_indep edge a (endAtF x j ans a)
        have h1 := packF_indep_step edge f hf1 hf2 a (partY k) hu0 (partScore k) hprev s hind
        rw [hcard] at h1
        exact packF_mono_set f (hsub_end s hs) h1
      · -- ans a = false, gain a = true (wrong zero: +1 error)
        simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        have hgain_eq : alphaF edge a (insert (j a) (x a)) = alphaF edge a (x a) + 1 := by
          simpa [gain] using hg_val
        have hend_eq : endAtF x j ans a = x a := by simp [endAtF, ha_val]
        obtain ⟨s', hs', hind', hcard'⟩ := exists_max_indep edge a (insert (j a) (x a))
        have hj_mem : j a ∈ s' := by
          by_contra hnot
          have hs'_sub : s' ⊆ x a := by
            intro v hv
            rcases Finset.mem_insert.mp (hs' hv) with rfl | hvx
            · exact absurd hv hnot
            · exact hvx
          have hle := card_le_alphaF edge a hs'_sub hind'
          omega
        let s := s'.erase (j a)
        have hs_sub : s ⊆ x a := by
          intro v hv
          rcases Finset.mem_erase.mp hv with ⟨hne, hvs⟩
          rcases Finset.mem_insert.mp (hs' hvs) with rfl | hvx
          · exact absurd rfl hne
          · exact hvx
        have hs_ind : indep edge a s := fun u hu v hv =>
          hind' u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)
        have hs_card : s.card = alphaF edge a (x a) := by
          have hc : s.card + 1 = s'.card := Finset.card_erase_add_one hj_mem
          omega
        let u := partY k ∪ s.image (fun i => (a, i))
        have hpu : packF f (partScore k + alphaF edge a (endAtF x j ans a)) u := by
          rw [hend_eq, ← hs_card]
          exact packF_indep_step edge f hf1 hf2 a (partY k) hu0 (partScore k) hprev s hs_ind
        have hnotu : (a, j a) ∉ u := by
          intro hmem
          rcases Finset.mem_union.mp hmem with h0 | hS
          · exact hu0 (j a) h0
          · rcases Finset.mem_image.mp hS with ⟨i, his, heq⟩
            cases heq
            exact (Finset.mem_erase.mp his).1 rfl
        have hnoedge : ∀ v ∈ blockF u a, edge a v (j a) = false := by
          intro v hv
          rw [mem_blockF] at hv
          rcases Finset.mem_union.mp hv with h0 | hS
          · exact absurd h0 (hu0 v)
          · rcases Finset.mem_image.mp hS with ⟨i, his, heq⟩
            cases heq
            exact hind' v (Finset.mem_of_mem_erase his) (j a) hj_mem
        have hfu : f u (a, j a) = true := hf1 u a (j a) ⟨hnotu, hnoedge⟩
        have hfq : f (queryF x j ans a) (a, j a) = false := by
          have hc := hcons a
          rw [ha_val] at hc
          exact hc.symm
        rw [← Nat.add_assoc]
        exact ⟨u, queryF x j ans a, (a, j a), hpu, hsub_q s hs_sub, hq_sub, hfu, hfq⟩
      · -- ans a = true, gain a = false (wrong one: +1 error)
        simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte]
        have hgain_ne : alphaF edge a (insert (j a) (x a)) ≠ alphaF edge a (x a) + 1 := by
          simpa [gain] using hg_val
        have halpha_eq : alphaF edge a (insert (j a) (x a)) = alphaF edge a (x a) :=
          alphaF_insert_eq_of_ne edge a (j a) (x a) hgain_ne
        have hend_eq : endAtF x j ans a = insert (j a) (x a) := by simp [endAtF, ha_val]
        obtain ⟨s, hs, hind, hcard⟩ := exists_max_indep edge a (x a)
        have hpu0 : packF f (partScore k + alphaF edge a (endAtF x j ans a))
            (partY k ∪ s.image (fun i => (a, i))) := by
          rw [hend_eq, halpha_eq, ← hcard]
          exact packF_indep_step edge f hf1 hf2 a (partY k) hu0 (partScore k) hprev s hind
        have hpq : packF f (partScore k + alphaF edge a (endAtF x j ans a)) (queryF x j ans a) :=
          packF_mono_set f (hsub_q s hs) hpu0
        have hfq : f (queryF x j ans a) (a, j a) = true := by
          have hc := hcons a
          rw [ha_val] at hc
          exact hc.symm
        have hj_in : (a, j a) ∈ partY (k + 1) := by
          simp only [partY, Finset.mem_filter, Finset.mem_univ, true_and, hend_eq, a]
          exact ⟨by omega, Finset.mem_insert_self (j a) (x a)⟩
        have hfv : f (partY (k + 1)) (a, j a) = false := hf2 (partY (k + 1)) a (j a) hj_in
        rw [← Nat.add_assoc]
        exact ⟨queryF x j ans a, partY (k + 1), (a, j a), hpq, hq_sub, Finset.Subset.rfl, hfq, hfv⟩
      · -- ans a = true, gain a = true (no error)
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
        obtain ⟨s, hs, hind, hcard⟩ := exists_max_indep edge a (endAtF x j ans a)
        have h1 := packF_indep_step edge f hf1 hf2 a (partY k) hu0 (partScore k) hprev s hind
        rw [hcard] at h1
        exact packF_mono_set f (hsub_end s hs) h1
  have hpartY_r : partY r = y := by
    ext p
    simp only [partY, y, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨p.1.isLt, h⟩⟩
  have hpartSet_r : partSet r = Finset.univ := by
    ext a; simp [partSet, a.isLt]
  have hblock_y : ∀ a : Fin r, blockF y a = endAtF x j ans a := by
    intro a; ext i
    simp [blockF, y]
  have hpartScore_r : partScore r = rankF edge y + errors := by
    simp only [partScore, hpartSet_r, term, Finset.sum_add_distrib, rankF, hblock_y, errors]
    congr 1
    exact (Finset.card_filter (fun a : Fin r => ans a ≠ gain a) Finset.univ).symm
  have hpack_main : packF f (rankF edge y + errors) y := by
    have h := hpart r le_rfl
    rwa [hpartY_r, hpartScore_r] at h
  refine ⟨hpack_main, ?_⟩
  intro e hno
  have herr_le : errors ≤ e := by
    by_contra hgt
    have hle : rankF edge y + e + 1 ≤ rankF edge y + errors := by omega
    exact hno y (packF_mono_nat f hle hpack_main)
  refine ⟨herr_le, ?_⟩
  intro b hgain h2e
  have hcard_split :
      (Finset.univ.filter (fun a : Fin r => ans a = true)).card +
      (Finset.univ.filter (fun a : Fin r => ans a = false)).card = r := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    trans ∑ _a : Fin r, 1
    · exact Finset.sum_congr rfl fun a _ => by cases ans a <;> simp
    · simp
  cases b
  · -- b = false: errors = ones
    have herr_eq : errors = ones := by
      dsimp only [errors, ones]
      congr 1; ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgain a]
      cases ans a <;> simp
    have hnot : ¬ (r < 2 * ones) := by omega
    simp [hnot]
  · -- b = true: errors = card(ans = false)
    have herr_eq : errors = (Finset.univ.filter (fun a : Fin r => ans a = false)).card := by
      dsimp only [errors]
      congr 1; ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgain a]
      cases ans a <;> simp
    have hlt : r < 2 * ones := by
      change r < 2 * (Finset.univ.filter (fun a : Fin r => ans a = true)).card
      omega
    simp [hlt]

end Helpers

end PEqualNP.Outside.L_meta_47146

open PEqualNP.Outside.L_meta_47146 in
theorem PEqualNP.Outside.L_meta_47146 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (r n : Nat) (edge : Fin r → Fin n → Fin n → Bool),
  (∀ a i, edge a i i = false) → (∀ a i j, edge a i j = edge a j i) →
  let V := Fin r × Fin n
  let X := Finset (Fin n)
  let Y := Finset V
  let block := fun (y : Y) (a : Fin r) =>
    (Finset.univ : X).filter (fun i => (a,i) ∈ y)
  let alpha := fun (a : Fin r) (x : X) =>
    (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, edge a i j = false)).sup Finset.card
  let rank := fun (y : Y) => ∑ a : Fin r, alpha a (block y a)
  ∀ (f : Y → V → Bool) (x : Fin r → X) (j : Fin r → Fin n),
    (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge a k i = false) →
      f y (a,i) = true) →
    (∀ y a i, (a,i) ∈ y → f y (a,i) = false) →
    let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Y) (k : V), prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        f u k = true ∧ f v k = false)
    let gain := fun a => decide (alpha a (insert (j a) (x a)) = alpha a (x a)+1)
    let endAt := fun (ans : Fin r → Bool) a =>
      if ans a then insert (j a) (x a) else x a
    let query := fun (ans : Fin r → Bool) (a : Fin r) =>
      (Finset.univ : Y).filter (fun p =>
        (p.1 < a ∧ p.2 ∈ endAt ans p.1) ∨ (p.1 = a ∧ p.2 ∈ x a))
    let consistent := fun (ans : Fin r → Bool) =>
      ∀ a, ans a = f (query ans a) (a,j a)
    (∃! ans, consistent ans) ∧
    ∀ ans, consistent ans →
      let y := (Finset.univ : Y).filter (fun p => p.2 ∈ endAt ans p.1)
      let errors := (Finset.univ.filter (fun a : Fin r => ans a ≠ gain a)).card
      let ones := (Finset.univ.filter (fun a : Fin r => ans a = true)).card
      pack (rank y + errors) y ∧
      ∀ e : Nat, (∀ z, ¬ pack (rank z+e+1) z) →
        errors ≤ e ∧ ∀ b : Bool, (∀ a, gain a = b) → 2*e < r →
          decide (r < 2*ones) = b := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro r n edge _ _ V X Y block alpha rank f x j hf1 hf2 pack gain endAt query consistent
  have hblock_eq : ∀ y a, block y a = blockF y a := fun y a => by
    ext i; simp [block, blockF]
  have halpha_eq : ∀ a s, alpha a s = alphaF edge a s := fun a s => by
    dsimp only [alpha, alphaF]
    congr 1; ext t; simp
  have hrank_eq : ∀ y, rank y = rankF edge y := fun y => by
    dsimp only [rank, rankF]
    exact Finset.sum_congr rfl fun a _ => by rw [hblock_eq, halpha_eq]
  have hinsert_eq : ∀ (v : Fin n) (s : Finset (Fin n)),
      @Insert.insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (fun a b => Classical.propDecidable (a = b))) v s =
      @Insert.insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) v s :=
    fun v s => Finset.ext fun u => by simp
  have hendAt_eq : ∀ ans a, endAt ans a = endAtF x j ans a := fun ans a => by
    dsimp only [endAt, endAtF]
    split <;> [exact hinsert_eq (j a) (x a); rfl]
  have hquery_eq : ∀ ans a, query ans a = queryF x j ans a := fun ans a => by
    ext p
    simp only [query, queryF, Finset.mem_filter, Finset.mem_univ, true_and, hendAt_eq]
  have hgain_eq : ∀ a, gain a =
      @decide (alphaF edge a
        (@Insert.insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) (j a) (x a)) =
        alphaF edge a (x a) + 1) (Nat.decEq _ _) := by
    intro a
    dsimp only [gain]
    rw [halpha_eq, halpha_eq, hinsert_eq]
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  have hf1' : ∀ y a i, ((a, i) ∉ y ∧ ∀ k ∈ blockF y a, edge a k i = false) → f y (a, i) = true := by
    intro y a i h
    exact hf1 y a i ⟨h.1, fun k hk => h.2 k (by rwa [← hblock_eq])⟩
  have hres := solve_47146 r n edge f x j hf1' hf2
  have hcons_iff : ∀ ans, consistent ans ↔ ∀ a, ans a = f (queryF x j ans a) (a, j a) :=
    fun ans => by simp only [consistent, hquery_eq]
  have hpack_eq : pack = packF f := rfl
  refine ⟨?_, ?_⟩
  · rcases hres.1 with ⟨ans0, h0, huniq⟩
    exact ⟨ans0, (hcons_iff ans0).mpr h0, fun ans hc => huniq ans ((hcons_iff ans).mp hc)⟩
  · intro ans hcons
    have h2 := hres.2 ans ((hcons_iff ans).mp hcons)
    dsimp only at h2 ⊢
    have hy_eq : (Finset.univ : Finset (Fin r × Fin n)).filter (fun p => p.2 ∈ endAt ans p.1) =
        @Finset.filter (Fin r × Fin n) (fun p => p.2 ∈ endAtF x j ans p.1)
          (fun p => @Finset.decidableMem (Fin n) (instDecidableEqFin n) p.2 (endAtF x j ans p.1))
          Finset.univ := by
      ext p; simp [hendAt_eq]
    have herr_eq : (Finset.univ.filter (fun a : Fin r => ans a ≠ gain a)).card =
        (@Finset.filter (Fin r)
          (fun a : Fin r => ans a ≠ @decide (alphaF edge a
            (@Insert.insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) (j a) (x a)) =
            alphaF edge a (x a) + 1) (Nat.decEq _ _))
          (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) Finset.univ).card := by
      congr 1; ext a; simp [hgain_eq]
    have hones_eq : (Finset.univ.filter (fun a : Fin r => ans a = true)).card =
        (@Finset.filter (Fin r) (fun a : Fin r => ans a = true)
          (fun a => instDecidableEqBool _ _) Finset.univ).card := by
      congr 1; ext a; simp
    rw [hpack_eq, hy_eq, herr_eq, hones_eq, hrank_eq]
    refine ⟨h2.1, fun e hno => ?_⟩
    have hno' : ∀ z, ¬ packF f (rankF edge z + e + 1) z := fun z hz =>
      hno z (by rw [hrank_eq]; exact hz)
    obtain ⟨hle, hmaj⟩ := h2.2 e hno'
    refine ⟨hle, fun b hgb h2e => ?_⟩
    have hgb' : ∀ a, @decide (alphaF edge a
        (@Insert.insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) (j a) (x a)) =
        alphaF edge a (x a) + 1) (Nat.decEq _ _) = b :=
      fun a => by rw [← hgain_eq]; exact hgb a
    have hdec := hmaj b hgb' h2e
    rw [← hdec]
    exact congrArg (@decide _) (Subsingleton.elim _ _)
