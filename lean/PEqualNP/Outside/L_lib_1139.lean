import Mathlib
import PEqualNP.Defs

open Finset
open scoped symmDiff

namespace PEqualNP.Outside.L_lib_1139_aux

theorem card_symmDiff_mod {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card % 2 = (s.card + t.card) % 2 := by
  have h1 : s ∆ t = (s ∪ t) \ (s ∩ t) := symmDiff_eq_sup_sdiff_inf s t
  have h2 := card_union_add_card_inter s t
  have h3 : (s ∩ t) ⊆ s ∪ t := inter_subset_left.trans subset_union_left
  have h5 : ((s ∪ t) \ (s ∩ t)).card + (s ∩ t).card = (s ∪ t).card :=
    card_sdiff_add_card_eq_card h3
  rw [h1]
  omega

theorem sd3 {α : Type*} [DecidableEq α] (a b d : Finset α) : (a ∆ b) ∆ (a ∆ d) = b ∆ d := by
  ext x; simp only [mem_symmDiff]; tauto

theorem sdc {α : Type*} [DecidableEq α] (a d : Finset α) : a ∆ (a ∆ d) = d := by
  ext x; simp only [mem_symmDiff]; tauto

def pt {r s : ℕ} (owner : Fin r → Fin s) (i : Fin s) (d : Finset (Fin r)) : Finset (Fin r) :=
  d.filter (fun j => owner j = i)

variable {r s : ℕ} (owner : Fin r → Fin s)

theorem pt_sd (i : Fin s) (a b : Finset (Fin r)) :
    pt owner i (a ∆ b) = pt owner i a ∆ pt owner i b := by
  ext x; simp only [pt, mem_filter, mem_symmDiff]; tauto

theorem pt_empty (i : Fin s) : pt owner i (∅ : Finset (Fin r)) = ∅ := by
  simp [pt]

theorem swap_part (a d : Finset (Fin r)) (i j : Fin s) :
    pt owner j (a ∆ pt owner i a ∆ pt owner i d) = if j = i then pt owner i d else pt owner j a := by
  split_ifs with h
  · subst h
    ext x; simp only [pt, mem_filter, mem_symmDiff]; tauto
  · ext x
    simp only [pt, mem_filter, mem_symmDiff]
    by_cases hx : owner x = j
    · have : ¬ owner x = i := fun e => h (hx.symm.trans e)
      tauto
    · tauto

variable (V : Finset (Finset (Fin r)))

theorem glue (hV0 : (∅ : Finset (Fin r)) ∈ V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a ∆ b ∈ V)
    (e : Finset (Fin r)) (h : ∀ i, pt owner i e ∈ V) : e ∈ V := by
  have key : ∀ S : Finset (Fin s), e.filter (fun j => owner j ∈ S) ∈ V := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hV0
    | insert i S hi ih =>
      have hh : e.filter (fun j => owner j ∈ insert i S) =
          pt owner i e ∆ e.filter (fun j => owner j ∈ S) := by
        ext j
        simp only [pt, mem_filter, mem_symmDiff, mem_insert]
        by_cases h1 : owner j = i
        · have : owner j ∉ S := h1 ▸ hi
          tauto
        · tauto
      rw [hh]
      exact hVc _ (h i) _ ih
  simpa using key univ

theorem cover_le (hVc : ∀ a ∈ V, ∀ b ∈ V, a ∆ b ∈ V) (K : ℕ)
    (acc : Fin K → Fin s → Finset (Fin r) → Bool)
    (hacc : ∀ d, d ∈ V ↔ ∃ z : Fin K, ∀ i : Fin s, acc z i (pt owner i d) = true) :
    V.card ≤ K * (V.filter (fun d => ∀ i, pt owner i d ∈ V)).card := by
  set W := V.filter (fun d => ∀ i, pt owner i d ∈ V) with hW
  let R : Fin K → Finset (Finset (Fin r)) := fun z =>
    (univ : Finset (Finset (Fin r))).filter (fun d => ∀ i, acc z i (pt owner i d) = true)
  have hR : ∀ z, (R z).card ≤ W.card := by
    intro z
    rcases (R z).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · rw [h]; simp
    have ha' : ∀ i, acc z i (pt owner i a) = true := (mem_filter.1 ha).2
    have haV : a ∈ V := (hacc a).2 ⟨z, ha'⟩
    apply card_le_card_of_injOn (fun d => a ∆ d)
    · intro d hd
      have hd' : ∀ i, acc z i (pt owner i d) = true := (mem_filter.1 hd).2
      have hdV : d ∈ V := (hacc d).2 ⟨z, hd'⟩
      show a ∆ d ∈ (↑W : Set (Finset (Fin r)))
      rw [Finset.mem_coe, hW, mem_filter]
      refine ⟨hVc _ haV _ hdV, fun i => ?_⟩
      have heR : ∀ j, acc z j (pt owner j (a ∆ pt owner i a ∆ pt owner i d)) = true := by
        intro j
        rw [swap_part]
        split_ifs with h
        · subst h; exact hd' j
        · exact ha' j
      have heV := (hacc _).2 ⟨z, heR⟩
      have hx : pt owner i (a ∆ d) = a ∆ (a ∆ pt owner i a ∆ pt owner i d) := by
        rw [pt_sd, symmDiff_assoc, sdc]
      rw [hx]
      exact hVc _ haV _ heV
    · intro x _ y _ hxy
      have := congrArg (fun t => a ∆ t) hxy
      simpa [sdc] using this
  have hsub : V ⊆ (univ : Finset (Fin K)).biUnion R := by
    intro d hd
    obtain ⟨z, hz⟩ := (hacc d).1 hd
    exact mem_biUnion.2 ⟨z, mem_univ _, mem_filter.2 ⟨mem_univ _, hz⟩⟩
  calc V.card ≤ ((univ : Finset (Fin K)).biUnion R).card := card_le_card hsub
    _ ≤ ∑ z, (R z).card := card_biUnion_le
    _ ≤ ∑ _z : Fin K, W.card := sum_le_sum (fun z _ => hR z)
    _ = K * W.card := by simp

theorem partition (hs : 0 < s) (hV0 : (∅ : Finset (Fin r)) ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a ∆ b ∈ V) (K : ℕ)
    (hK : V.card ≤ K * (V.filter (fun d => ∀ i, pt owner i d ∈ V)).card) :
    ∃ c : Fin K → Finset (Finset (Fin r)), (∀ z, c z ⊆ V) ∧
      (∀ z d, d ∈ c z ↔ ∀ i, pt owner i d ∈ (c z).image (pt owner i)) ∧
      (∀ d ∈ V, ∃ z, d ∈ c z ∧ ∀ z', d ∈ c z' → z' = z) := by
  set W := V.filter (fun d => ∀ i, pt owner i d ∈ V) with hW
  have hWV : W ⊆ V := filter_subset _ _
  have hW0 : (∅ : Finset (Fin r)) ∈ W :=
    mem_filter.2 ⟨hV0, fun i => by rw [pt_empty]; exact hV0⟩
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a ∆ b ∈ W := by
    intro a ha b hb
    rw [hW, mem_filter] at ha hb ⊢
    exact ⟨hVc _ ha.1 _ hb.1, fun i => by rw [pt_sd]; exact hVc _ (ha.2 i) _ (hb.2 i)⟩
  let coset : Finset (Fin r) → Finset (Finset (Fin r)) := fun a => W.image (fun w => a ∆ w)
  have mem_coset : ∀ a d, d ∈ coset a ↔ a ∆ d ∈ W := by
    intro a d
    constructor
    · intro h
      obtain ⟨w, hw, rfl⟩ := mem_image.1 h
      rw [sdc]; exact hw
    · intro h
      exact mem_image.2 ⟨a ∆ d, h, sdc a d⟩
  have coset_sub : ∀ a ∈ V, coset a ⊆ V := by
    intro a ha d hd
    rw [mem_coset] at hd
    have := hVc _ ha _ (hWV hd)
    rwa [sdc] at this
  have card_coset : ∀ a, (coset a).card = W.card := by
    intro a
    apply card_image_of_injective
    exact symmDiff_right_injective a
  have coset_eq : ∀ a b, a ∆ b ∈ W → coset a = coset b := by
    intro a b hab
    ext d
    rw [mem_coset, mem_coset]
    constructor
    · intro h
      have := hWc _ hab _ h
      rwa [sd3] at this
    · intro h
      have hba : b ∆ a ∈ W := by rw [symmDiff_comm]; exact hab
      have := hWc _ hba _ h
      rwa [sd3] at this
  have self_mem : ∀ d, d ∈ coset d := by
    intro d; rw [mem_coset, symmDiff_self]; exact hW0
  have rect : ∀ a ∈ V, ∀ d, d ∈ coset a ↔ ∀ i, pt owner i d ∈ (coset a).image (pt owner i) := by
    intro a ha d
    constructor
    · intro h i; exact mem_image_of_mem _ h
    · intro h
      rw [mem_coset]
      have hp : ∀ i, pt owner i (a ∆ d) ∈ V := by
        intro i
        obtain ⟨e, he, hed⟩ := mem_image.1 (h i)
        rw [mem_coset, hW, mem_filter] at he
        rw [pt_sd, ← hed, ← pt_sd]
        exact he.2 i
      exact mem_filter.2 ⟨glue owner V hV0 hVc _ hp, hp⟩
  let C := V.image coset
  have hC : ∀ c ∈ C, ∃ a ∈ V, c = coset a := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
    exact ⟨a, ha, rfl⟩
  have hCeq : ∀ c ∈ C, ∀ d ∈ c, c = coset d := by
    intro c hc d hd
    obtain ⟨a, _, rfl⟩ := hC c hc
    exact coset_eq a d ((mem_coset a d).1 hd)
  have hVC : V = C.biUnion (fun c => c) := by
    ext d
    constructor
    · intro hd
      exact mem_biUnion.2 ⟨coset d, mem_image_of_mem _ hd, self_mem d⟩
    · intro hd
      obtain ⟨c, hc, hdc⟩ := mem_biUnion.1 hd
      obtain ⟨a, ha, rfl⟩ := hC c hc
      exact coset_sub a ha hdc
  have hcardV : V.card = C.card * W.card := by
    have h1 : (C.biUnion (fun c => c)).card = ∑ c ∈ C, c.card := by
      apply card_biUnion
      intro x hx y hy hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro d hdx hdy
      exact hxy ((hCeq x hx d hdx).trans (hCeq y hy d hdy).symm)
    have h2 : ∑ c ∈ C, c.card = ∑ _c ∈ C, W.card := by
      apply sum_congr rfl
      intro c hc
      obtain ⟨a, _, rfl⟩ := hC c hc
      exact card_coset a
    rw [hVC, h1, h2, sum_const, smul_eq_mul]
  have hWpos : 0 < W.card := card_pos.2 ⟨_, hW0⟩
  have hCK : C.card ≤ K := by
    rw [hcardV] at hK
    exact Nat.le_of_mul_le_mul_right hK hWpos
  let c : Fin K → Finset (Finset (Fin r)) := fun z =>
    if h : z.val < C.card then (C.equivFin.symm ⟨z.val, h⟩).val else ∅
  have hcC : ∀ z, c z = ∅ ∨ c z ∈ C := by
    intro z
    by_cases h : z.val < C.card
    · right
      simp only [c, h, ↓reduceDIte]
      exact (C.equivFin.symm ⟨z.val, h⟩).2
    · left
      simp only [c, h, ↓reduceDIte]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro z
    rcases hcC z with h | h
    · rw [h]; exact empty_subset _
    · obtain ⟨a, ha, hca⟩ := hC _ h
      rw [hca]; exact coset_sub a ha
  · intro z d
    rcases hcC z with h | h
    · rw [h]
      simp only [image_empty, notMem_empty, false_iff, not_forall]
      exact ⟨⟨0, hs⟩, not_false⟩
    · obtain ⟨a, ha, hca⟩ := hC _ h
      rw [hca]; exact rect a ha d
  · intro d hd
    have hdC : coset d ∈ C := mem_image_of_mem _ hd
    let k := C.equivFin ⟨coset d, hdC⟩
    have hkK : k.val < K := lt_of_lt_of_le k.isLt hCK
    refine ⟨⟨k.val, hkK⟩, ?_, ?_⟩
    · have : c ⟨k.val, hkK⟩ = coset d := by
        simp only [c, k.isLt, ↓reduceDIte]
        simp [k]
      rw [this]; exact self_mem d
    · intro z' hz'
      by_cases h : z'.val < C.card
      · have hz2 : c z' = (C.equivFin.symm ⟨z'.val, h⟩).val := by
          simp only [c, h, ↓reduceDIte]
        have hmem : c z' ∈ C := by rw [hz2]; exact (C.equivFin.symm ⟨z'.val, h⟩).2
        have heq : c z' = coset d := hCeq _ hmem d hz'
        have h3 : C.equivFin.symm ⟨z'.val, h⟩ = ⟨coset d, hdC⟩ := by
          apply Subtype.ext
          rw [← hz2, heq]
        have h4 : (⟨z'.val, h⟩ : Fin C.card) = k := by
          have h5 := congrArg C.equivFin h3
          simpa [k] using h5
        apply Fin.ext
        simp only
        exact congrArg Fin.val h4
      · have : c z' = ∅ := by simp only [c, h, ↓reduceDIte]
        rw [this] at hz'
        exact absurd hz' (notMem_empty _)

theorem main : (∀ (m r s : Nat), 0 < s →
  ∀ (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s),
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let parties := (Finset.univ : Finset (Fin s))
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun j => ((rows j) ∩ x).card % 2 = 1)
  let part := fun (d : Finset (Fin r)) (i : Fin s) => d.filter (fun j => owner j = i)
  let imageSet := xs.image syn
  let independent := imageSet.filter (fun d => ∀ i : Fin s, part d i ∈ imageSet)
  let mass := fun (d : Finset (Fin r)) => (xs.filter (fun x => syn x = d)).card
  ∀ K : Nat,
    let cover := ∃ accept : Fin K → Fin s → Finset (Fin r) → Bool,
      ∀ d : Finset (Fin r), (d ∈ imageSet ↔
        ∃ z : Fin K, ∀ i : Fin s, accept z i (part d i) = true)
    let exactCount := ∃ weight : Fin K → Fin s → Finset (Fin r) → Nat,
      ∀ d : Finset (Fin r), mass d =
        (Finset.univ : Finset (Fin K)).sum
          (fun z => parties.prod (fun i => weight z i (part d i)))
    (cover ↔ imageSet.card ≤ K * independent.card) ∧
      (exactCount ↔ imageSet.card ≤ K * independent.card)) := by
  intro m r s hs rows owner
  intro xs parties syn part imageSet independent mass K cover exactCount
  have hsyn : ∀ x y, syn (x ∆ y) = syn x ∆ syn y := by
    intro x y
    ext j
    simp only [syn, mem_filter, mem_univ, true_and, mem_symmDiff]
    have hi : rows j ∩ (x ∆ y) = (rows j ∩ x) ∆ (rows j ∩ y) := by
      ext t; simp only [mem_inter, mem_symmDiff]; tauto
    have := card_symmDiff_mod (rows j ∩ x) (rows j ∩ y)
    rw [hi]
    omega
  have hsyn0 : syn ∅ = ∅ := by
    ext j; simp [syn]
  have hV0 : (∅ : Finset (Fin r)) ∈ imageSet := mem_image.2 ⟨∅, mem_univ _, hsyn0⟩
  have hVc : ∀ a ∈ imageSet, ∀ b ∈ imageSet, a ∆ b ∈ imageSet := by
    intro a ha b hb
    obtain ⟨x, _, rfl⟩ := mem_image.1 ha
    obtain ⟨y, _, rfl⟩ := mem_image.1 hb
    exact mem_image.2 ⟨x ∆ y, mem_univ _, hsyn x y⟩
  have hmass : ∀ d, mass d = if d ∈ imageSet then mass ∅ else 0 := by
    intro d
    split_ifs with hd
    · obtain ⟨x0, _, hx0⟩ := mem_image.1 hd
      symm
      apply card_nbij' (fun x => x ∆ x0) (fun x => x ∆ x0)
      · intro x hx
        have hx' := (mem_filter.1 hx).2
        exact mem_filter.2 ⟨mem_univ _, by rw [hsyn, hx', ← hx0]; simp⟩
      · intro x hx
        have hx' := (mem_filter.1 hx).2
        exact mem_filter.2 ⟨mem_univ _, by rw [hsyn, hx', ← hx0]; simp⟩
      · intro x _; simp
      · intro x _; simp
    · apply card_eq_zero.2
      apply filter_eq_empty_iff.2
      intro x _ hx
      exact hd (mem_image.2 ⟨x, mem_univ _, hx⟩)
  have hM : 0 < mass ∅ := card_pos.2 ⟨∅, mem_filter.2 ⟨mem_univ _, hsyn0⟩⟩
  have h1 : cover → imageSet.card ≤ K * independent.card := by
    rintro ⟨acc, hacc⟩
    exact cover_le owner imageSet hVc K acc hacc
  have h2 : imageSet.card ≤ K * independent.card → exactCount := by
    intro hK
    obtain ⟨c, hcV, hrect, huniq⟩ := partition owner imageSet hs hV0 hVc K hK
    refine ⟨fun z i t => if t ∈ (c z).image (pt owner i) then
      (if i = ⟨0, hs⟩ then mass ∅ else 1) else 0, ?_⟩
    intro d
    have hterm : ∀ z, parties.prod (fun i => (if part d i ∈ (c z).image (pt owner i) then
        (if i = (⟨0, hs⟩ : Fin s) then mass ∅ else 1) else 0)) =
        if d ∈ c z then mass ∅ else 0 := by
      intro z
      rw [prod_ite_zero]
      have hiff : (∀ i ∈ parties, part d i ∈ (c z).image (pt owner i)) ↔ d ∈ c z := by
        rw [hrect z d]
        simp [parties, part, pt]
      simp only [hiff]
      split_ifs
      · simp [parties]
      · rfl
    show mass d = ∑ z, parties.prod (fun i => (if part d i ∈ (c z).image (pt owner i) then
        (if i = (⟨0, hs⟩ : Fin s) then mass ∅ else 1) else 0))
    rw [sum_congr rfl (fun z _ => hterm z), hmass d]
    split_ifs with hd
    · obtain ⟨z0, hz0, hu⟩ := huniq d hd
      rw [sum_eq_single z0]
      · rw [if_pos hz0]
      · intro z _ hz
        rw [if_neg]
        intro hdz
        exact hz (hu z hdz)
      · intro h; exact absurd (mem_univ z0) h
    · symm
      apply sum_eq_zero
      intro z _
      rw [if_neg]
      intro hdz
      exact hd (hcV z hdz)
  have h3 : exactCount → cover := by
    rintro ⟨w, hw⟩
    refine ⟨fun z i t => decide (w z i t ≠ 0), ?_⟩
    intro d
    have hd : d ∈ imageSet ↔ mass d ≠ 0 := by
      rw [hmass d]
      split_ifs with h
      · exact ⟨fun _ => hM.ne', fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd rfl h'⟩
    rw [hd, hw d]
    simp [Finset.sum_eq_zero_iff, Finset.prod_eq_zero_iff, parties]
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h1 (h3 h), h2⟩⟩

end PEqualNP.Outside.L_lib_1139_aux

theorem PEqualNP.Outside.L_lib_1139 : (∀ (m r s : Nat), 0 < s →
  ∀ (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s),
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let parties := (Finset.univ : Finset (Fin s))
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun j => ((rows j) ∩ x).card % 2 = 1)
  let part := fun (d : Finset (Fin r)) (i : Fin s) => d.filter (fun j => owner j = i)
  let imageSet := xs.image syn
  let independent := imageSet.filter (fun d => ∀ i : Fin s, part d i ∈ imageSet)
  let mass := fun (d : Finset (Fin r)) => (xs.filter (fun x => syn x = d)).card
  ∀ K : Nat,
    let cover := ∃ accept : Fin K → Fin s → Finset (Fin r) → Bool,
      ∀ d : Finset (Fin r), (d ∈ imageSet ↔
        ∃ z : Fin K, ∀ i : Fin s, accept z i (part d i) = true)
    let exactCount := ∃ weight : Fin K → Fin s → Finset (Fin r) → Nat,
      ∀ d : Finset (Fin r), mass d =
        (Finset.univ : Finset (Fin K)).sum
          (fun z => parties.prod (fun i => weight z i (part d i)))
    (cover ↔ imageSet.card ≤ K * independent.card) ∧
      (exactCount ↔ imageSet.card ≤ K * independent.card)) :=
  PEqualNP.Outside.L_lib_1139_aux.main
