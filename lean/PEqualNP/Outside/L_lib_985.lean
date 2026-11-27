import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_985

def col {n : ℕ} (e : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ e then 1 else 0

noncomputable def rk {n : ℕ} (S : Finset (Finset (Fin n))) : ℕ :=
  Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) ((S.image col : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)))

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma col_mem_span {n : ℕ} {S : Finset (Finset (Fin n))} {e : Finset (Fin n)} (he : e ∈ S) :
    col e ∈ Submodule.span (ZMod 2) ((S.image col : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) :=
  Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨e, he, rfl⟩)

lemma span_mono' {n : ℕ} {A B : Finset (Finset (Fin n))} (h : A ⊆ B) :
    Submodule.span (ZMod 2) ((A.image col : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) ≤
    Submodule.span (ZMod 2) ((B.image col : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) :=
  Submodule.span_mono (by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx ⊢
    obtain ⟨e, he, rfl⟩ := hx
    exact ⟨e, h he, rfl⟩)

lemma rk_mono {n : ℕ} {A B : Finset (Finset (Fin n))} (h : A ⊆ B) : rk A ≤ rk B :=
  Submodule.finrank_mono (span_mono' h)

lemma rk_le_card {n : ℕ} (S : Finset (Finset (Fin n))) : rk S ≤ S.card :=
  le_trans (finrank_span_finset_le_card _) Finset.card_image_le

lemma rk_lt {n : ℕ} {A B : Finset (Finset (Fin n))} (h : A ⊆ B) (i : Fin n)
    (hA : ∀ e ∈ A, i ∉ e) {e : Finset (Fin n)} (he : e ∈ B) (hi : i ∈ e) : rk A < rk B := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (span_mono' h) ?_
  intro heq
  have hP : Submodule.span (ZMod 2) ((A.image col : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2))
      ≤ LinearMap.ker (LinearMap.proj i : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    simp [col, hA f hf]
  have hm := hP (heq ▸ col_mem_span he)
  simp [col, hi] at hm

lemma pair_eq {n : ℕ} {e : Finset (Fin n)} (he : e.card = 2) {v u : Fin n} (hv : v ∈ e) (hu : u ∈ e)
    (hne : v ≠ u) : e = {v, u} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne, he]

lemma star {n : ℕ} (v : Fin n) (T : Finset (Finset (Fin n))) (hT : ∀ e ∈ T, v ∈ e ∧ e.card = 2) :
    T.card ≤ rk T := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert e T0 heT ih =>
    have h0 := ih (fun f hf => hT f (Finset.mem_insert_of_mem hf))
    obtain ⟨hve, hce⟩ := hT e (Finset.mem_insert_self _ _)
    obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
    have hA : ∀ f ∈ T0, u ∉ f := by
      intro f hf huf
      obtain ⟨hvf, hcf⟩ := hT f (Finset.mem_insert_of_mem hf)
      have h1 := pair_eq hcf hvf huf (Ne.symm huv)
      have h2 := pair_eq hce hve hu (Ne.symm huv)
      exact heT (h2 ▸ h1 ▸ hf)
    have hlt := rk_lt (Finset.subset_insert e T0) u hA (Finset.mem_insert_self e T0) hu
    rw [Finset.card_insert_of_notMem heT]
    omega

lemma deg_le {n : ℕ} (S : Finset (Finset (Fin n))) (hS : ∀ e ∈ S, e.card = 2) (v : Fin n) :
    (S.filter (fun e => v ∈ e)).card ≤ rk S :=
  le_trans (star v _ (fun e he => by
    rw [Finset.mem_filter] at he
    exact ⟨he.2, hS e he.1⟩)) (rk_mono (Finset.filter_subset _ _))

lemma choose_succ (r : ℕ) : (r + 1).choose 2 = r.choose 2 + r := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring

lemma lemA {n : ℕ} : ∀ (k : ℕ) (S : Finset (Finset (Fin n))), S.card = k → (∀ e ∈ S, e.card = 2) →
    S.card ≤ (rk S + 1).choose 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · simp
  obtain ⟨v, hv⟩ : e.Nonempty := by rw [← Finset.card_pos, hS e he]; omega
  set S' := S.filter (fun f => v ∉ f) with hS'
  have hsplit : (S.filter (fun f => v ∈ f)).card + S'.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hlt : rk S' < rk S := rk_lt (Finset.filter_subset _ _) v (fun f hf => (Finset.mem_filter.1 hf).2) he hv
  have hdeg := deg_le S hS v
  have hpos : 0 < (S.filter (fun f => v ∈ f)).card :=
    Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hv⟩⟩
  have hih := ih S'.card (by omega) S' rfl (fun f hf => hS f (Finset.mem_filter.1 hf).1)
  have hmono : (rk S' + 1).choose 2 ≤ (rk S).choose 2 := Nat.choose_le_choose 2 (by omega)
  have hc := choose_succ (rk S)
  omega

lemma handshake {n : ℕ} (S : Finset (Finset (Fin n))) (hS : ∀ e ∈ S, e.card = 2) :
    ∑ w ∈ S.biUnion id, (S.filter (fun e => w ∈ e)).card = 2 * S.card := by
  have h0 : ∀ w, (S.filter (fun e => w ∈ e)).card = ∑ e ∈ S, if w ∈ e then 1 else 0 :=
    fun w => Finset.card_filter _ _
  simp_rw [h0]
  rw [Finset.sum_comm]
  have h2 : ∀ e ∈ S, (∑ w ∈ S.biUnion id, if w ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter]
    have h3 : (S.biUnion id).filter (fun w => w ∈ e) = e := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_biUnion, id]
      exact ⟨fun h => h.2, fun h => ⟨⟨e, he, h⟩, h⟩⟩
    rw [h3, hS e he]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

lemma two_choose (r : ℕ) : 2 * (r + 1).choose 2 = (r + 1) * r := by
  induction r with
  | zero => simp
  | succ r ih => rw [choose_succ (r + 1), mul_add, ih]; ring

lemma lemB {n : ℕ} : ∀ (k : ℕ) (S : Finset (Finset (Fin n))), S.card = k → (∀ e ∈ S, e.card = 2) →
    rk S + 2 ≤ (S.biUnion id).card → S.card ≤ (rk S).choose 2 + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hS hV
  rcases S.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · simp
  have hVne : (S.biUnion id).Nonempty := by
    obtain ⟨v, hv⟩ : e.Nonempty := by rw [← Finset.card_pos, hS e he]; omega
    exact ⟨v, Finset.mem_biUnion.2 ⟨e, he, hv⟩⟩
  obtain ⟨v, hvV, hmin⟩ :=
    Finset.exists_min_image (S.biUnion id) (fun w => (S.filter (fun f => w ∈ f)).card) hVne
  obtain ⟨e1, he1, hv1⟩ := Finset.mem_biUnion.1 hvV
  set S' := S.filter (fun f => v ∉ f) with hS'
  have hsplit : (S.filter (fun f => v ∈ f)).card + S'.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hlt : rk S' < rk S :=
    rk_lt (Finset.filter_subset _ _) v (fun f hf => (Finset.mem_filter.1 hf).2) he1 hv1
  have hpos : 0 < (S.filter (fun f => v ∈ f)).card :=
    Finset.card_pos.2 ⟨e1, Finset.mem_filter.2 ⟨he1, hv1⟩⟩
  have hA := lemA S.card S rfl hS
  have htwo := two_choose (rk S)
  have hhs := handshake S hS
  have hcard : (S.biUnion id).card • (S.filter (fun f => v ∈ f)).card ≤
      ∑ w ∈ S.biUnion id, (S.filter (fun f => w ∈ f)).card :=
    Finset.card_nsmul_le_sum _ _ _ hmin
  rw [smul_eq_mul] at hcard
  have hd : (S.filter (fun f => v ∈ f)).card + 1 ≤ rk S := by
    by_contra hcon
    push Not at hcon
    have h1 : (rk S + 2) * rk S ≤ (S.biUnion id).card * (S.filter (fun f => v ∈ f)).card :=
      Nat.mul_le_mul hV (by omega)
    have hr : 0 < rk S := by omega
    nlinarith
  have hS'2 : ∀ f ∈ S', f.card = 2 := fun f hf => hS f (Finset.mem_filter.1 hf).1
  by_cases hcase : ∀ w ∈ S.biUnion id, w ≠ v → w ∈ S'.biUnion id
  · have hsub : (S.biUnion id).erase v ⊆ S'.biUnion id := fun w hw =>
      hcase w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hvV] at hc1
    have hih := ih S'.card (by omega) S' rfl hS'2 (by omega)
    have hmono : (rk S').choose 2 ≤ (rk S - 1).choose 2 := Nat.choose_le_choose 2 (by omega)
    have hc := choose_succ (rk S - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ rk S)] at hc
    omega
  · push Not at hcase
    obtain ⟨w, hwV, hwv, hw'⟩ := hcase
    have hdw : (S.filter (fun f => w ∈ f)).card ≤ 1 := by
      apply Finset.card_le_one.2
      have key : ∀ f ∈ S.filter (fun f => w ∈ f), f = {v, w} := by
        intro f hf
        rw [Finset.mem_filter] at hf
        by_cases hvf : v ∈ f
        · exact pair_eq (hS f hf.1) hvf hf.2 (Ne.symm hwv)
        · exact absurd (Finset.mem_biUnion.2 ⟨f, Finset.mem_filter.2 ⟨hf.1, hvf⟩, hf.2⟩) hw'
      intro a ha b hb
      rw [key a ha, key b hb]
    have hmw := hmin w hwV
    have hA' := lemA S'.card S' rfl hS'2
    have hmono : (rk S' + 1).choose 2 ≤ (rk S).choose 2 := Nat.choose_le_choose 2 (by omega)
    omega

def gv {n : ℕ} (a0 a : Fin n) : Fin n → ZMod 2 :=
  fun k => (if k = a0 then 1 else 0) + (if k = a then 1 else 0)

lemma col_pair {n : ℕ} {e : Finset (Fin n)} (he : e.card = 2) (a0 : Fin n) :
    ∃ i j, i ∈ e ∧ j ∈ e ∧ col e = gv a0 i + gv a0 j := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 he
  refine ⟨i, j, by simp, by simp, ?_⟩
  funext k
  simp only [col, gv, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply]
  split_ifs <;> simp_all <;> decide

lemma lemRup {n : ℕ} (S X : Finset (Finset (Fin n))) (U : Finset (Fin n)) (a0 : Fin n)
    (ha0 : a0 ∈ U) (hS : ∀ e ∈ S, e.card = 2) (hcov : ∀ e ∈ S, e ⊆ U ∨ e ∈ X) :
    rk S ≤ (U.card - 1) + X.card := by
  set B : Finset (Fin n → ZMod 2) := (U.erase a0).image (gv a0) ∪ X.image col with hB
  have hg : ∀ a ∈ U, gv a0 a ∈ Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2)) := by
    intro a ha
    by_cases h : a = a0
    · have h0 : gv a0 a = 0 := by
        subst h; funext k; simp only [gv, Pi.zero_apply]; exact z2_add_self _
      rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨h, ha⟩))))
  have hle : Submodule.span (ZMod 2) ((S.image col : Finset (Fin n → ZMod 2)) :
      Set (Fin n → ZMod 2)) ≤ Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2)) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rcases hcov e he with hU | hX
    · obtain ⟨i, j, hi, hj, hc⟩ := col_pair (hS e he) a0
      rw [hc]
      exact Submodule.add_mem _ (hg i (hU hi)) (hg j (hU hj))
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hX)))
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2))) ≤ B.card :=
    finrank_span_finset_le_card (R := ZMod 2) B
  have h3 : B.card ≤ (U.erase a0).card + X.card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  rw [Finset.card_erase_of_mem ha0] at h3
  unfold rk
  omega

end PEqualNP.Outside.L_lib_985

open PEqualNP.Outside.L_lib_985 in
theorem PEqualNP.Outside.L_lib_985 :
    let F := ZMod 2
    let rank := fun (n : Nat) (S : Finset (Finset (Fin n))) =>
      let col := fun (e : Finset (Fin n)) (i : Fin n) => if i ∈ e then (1 : F) else 0
      Module.finrank F (Submodule.span F ((S.image col : Finset (Fin n → F)) : Set (Fin n → F)))
    ∀ (t : Nat), 3 ≤ t →
      (∀ (n δ : Nat) (S : Finset (Finset (Fin n))), δ < t-2 → (∀ e ∈ S, e.card = 2) →
        ((rank n S ≤ t-1 ∧ (t-1).choose 2 ≤ S.card - rank n S + δ) ↔
          ((S.biUnion id).card = t ∧ t.choose 2 ≤ S.card + δ))) ∧
      ∃ S : Finset (Finset (Fin (t+1))), (∀ e ∈ S, e.card = 2) ∧
        rank (t+1) S = t-1 ∧ S.card - rank (t+1) S + (t-2) = (t-1).choose 2 ∧
        (S.biUnion id).card = t+1 := by
  intro F rank t ht
  have hr : ∀ n (S : Finset (Finset (Fin n))), rank n S = rk S := fun _ _ => rfl
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
  simp only [hr]
  have e1 : s + 3 - 1 = s + 2 := rfl
  have e2 : s + 3 - 2 = s + 1 := rfl
  rw [e1, e2]
  have c2 : (s + 2).choose 2 = (s + 1).choose 2 + (s + 1) := choose_succ (s + 1)
  have c3 : (s + 3).choose 2 = (s + 2).choose 2 + (s + 2) := choose_succ (s + 2)
  refine ⟨fun n δ S hδ hS => ?_, ?_⟩
  · have hA := lemA S.card S rfl hS
    have hcs := choose_succ (rk S)
    have hrc := rk_le_card S
    have hcovV : ∀ e ∈ S, e ⊆ S.biUnion id ∨ e ∈ (∅ : Finset (Finset (Fin n))) := by
      intro e he
      left
      intro x hx
      exact Finset.mem_biUnion.2 ⟨e, he, hx⟩
    constructor
    · rintro ⟨hr1, hr2⟩
      have hreq : rk S = s + 2 := by
        by_contra hne
        have hm : (rk S).choose 2 ≤ (s + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
        omega
      obtain ⟨e, he⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨a0, ha0⟩ : e.Nonempty := by rw [← Finset.card_pos, hS e he]; omega
      have hup := lemRup S ∅ (S.biUnion id) a0 (Finset.mem_biUnion.2 ⟨e, he, ha0⟩) hS hcovV
      rw [Finset.card_empty] at hup
      have hVeq : (S.biUnion id).card = s + 3 := by
        by_contra hne
        have hB := lemB S.card S rfl hS (by omega)
        rw [hreq] at hB
        omega
      exact ⟨hVeq, by omega⟩
    · rintro ⟨hV, hc⟩
      obtain ⟨a0, ha0⟩ : (S.biUnion id).Nonempty := Finset.card_pos.1 (by omega)
      have hup := lemRup S ∅ (S.biUnion id) a0 ha0 hS hcovV
      rw [Finset.card_empty] at hup
      exact ⟨by omega, by omega⟩
  · let U : Finset (Fin (s + 3 + 1)) := Finset.univ.filter (fun i => i.val < s + 2)
    have hU : U.card = s + 2 := by
      have := Fin.card_filter_val_lt (n := s + 3 + 1) (m := s + 2)
      rw [this]; omega
    let p : Fin (s + 3 + 1) := ⟨s + 2, by omega⟩
    let q : Fin (s + 3 + 1) := ⟨s + 3, by omega⟩
    have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
    let e0 : Finset (Fin (s + 3 + 1)) := {p, q}
    have he0 : e0.card = 2 := Finset.card_pair hpq
    have hpU : p ∉ U := by simp [U, p]
    have hdisj : e0 ∉ U.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      intro h
      exact hpU (h.1 (by simp [e0]))
    refine ⟨U.powersetCard 2 ∪ {e0}, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact (Finset.mem_powersetCard.1 h).2
      · rw [Finset.mem_singleton.1 h]; exact he0
    have hS2 : ∀ e ∈ U.powersetCard 2 ∪ {e0}, e.card = 2 := by
      intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact (Finset.mem_powersetCard.1 h).2
      · rw [Finset.mem_singleton.1 h]; exact he0
    have hcard : (U.powersetCard 2 ∪ {e0}).card = (s + 2).choose 2 + 1 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hdisj),
        Finset.card_powersetCard, hU, Finset.card_singleton]
    have h0U : (⟨0, by omega⟩ : Fin (s + 3 + 1)) ∈ U := by simp [U]
    have hup := lemRup (U.powersetCard 2 ∪ {e0}) {e0} U _ h0U hS2 (by
      intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact Or.inl (Finset.mem_powersetCard.1 h).1
      · exact Or.inr h)
    rw [hU, Finset.card_singleton] at hup
    have hA := lemA _ (U.powersetCard 2 ∪ {e0}) rfl hS2
    have hreq : rk (U.powersetCard 2 ∪ {e0}) = s + 2 := by
      by_contra hne
      have hm : (rk (U.powersetCard 2 ∪ {e0}) + 1).choose 2 ≤ (s + 2).choose 2 :=
        Nat.choose_le_choose 2 (by omega)
      omega
    have hV : (U.powersetCard 2 ∪ {e0}).biUnion id = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      rw [Finset.mem_biUnion]
      by_cases hi : i.val < s + 2
      · let j : Fin (s + 3 + 1) := ⟨if i.val = 0 then 1 else 0, by split_ifs <;> omega⟩
        have hj : j.val < s + 2 := by
          simp only [j]; split_ifs <;> omega
        have hij : i ≠ j := by
          intro h
          have := congrArg Fin.val h
          simp only [j] at this
          split_ifs at this <;> omega
        refine ⟨{i, j}, Finset.mem_union_left _ (Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hij⟩), by simp⟩
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [U, hi]
        · simp [U, hj]
      · refine ⟨e0, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
        have : i = p ∨ i = q := by
          have := i.isLt
          simp only [p, q, Fin.ext_iff]
          omega
        rcases this with rfl | rfl <;> simp [e0]
    refine ⟨hreq, ?_, ?_⟩
    · rw [hcard, hreq]; omega
    · rw [hV, Finset.card_univ, Fintype.card_fin]
