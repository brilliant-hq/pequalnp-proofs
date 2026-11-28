import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1265_aux

open Classical

lemma card_sdiff_sub {α : Type*} [DecidableEq α] {s t : Finset α} (h : t ⊆ s) :
    (s \ t).card = s.card - t.card := by
  have := Finset.card_sdiff_add_card_eq_card h
  omega

lemma natAbs_sign_mul (P : Prop) [Decidable P] (m : ℕ) :
    ((if P then (1 : ℤ) else -1) * (m : ℤ)).natAbs = m := by
  split_ifs <;> simp

section BoolSeqParity

lemma bool_seq_delete_parity (d : ℕ) (hd : 1 ≤ d) (s : Fin d → Bool) :
    let good : Fin d → Prop := fun i =>
      ∀ j : Fin d, j ≠ i →
        s j = decide ((if j.val < i.val then j.val else j.val - 1) % 2 = 0)
    ((Finset.univ : Finset (Fin d)).filter good).card % 2 =
      if (∀ j : Fin d, s j = decide (j.val % 2 = 0)) ∨
         (∀ j : Fin d, s j = decide (j.val % 2 = 1)) then 1 else 0 := by
  intro good
  by_cases hbad : ∃ r : ℕ, ∃ hr : r + 1 < d, s ⟨r, by omega⟩ = s ⟨r + 1, hr⟩
  · rcases hbad with ⟨r, hr, hsr⟩
    have hnot : ¬ ((∀ j : Fin d, s j = decide (j.val % 2 = 0)) ∨
                   (∀ j : Fin d, s j = decide (j.val % 2 = 1))) := by
      rintro (h0 | h1)
      · have a := h0 ⟨r, by omega⟩
        have b := h0 ⟨r + 1, hr⟩
        rw [hsr] at a; rw [a] at b
        have := Bool.eq_iff_iff.mp b
        simp only [decide_eq_true_eq] at this
        omega
      · have a := h1 ⟨r, by omega⟩
        have b := h1 ⟨r + 1, hr⟩
        rw [hsr] at a; rw [a] at b
        have := Bool.eq_iff_iff.mp b
        simp only [decide_eq_true_eq] at this
        omega
    rw [if_neg hnot]
    let ir : Fin d := ⟨r, by omega⟩
    let ir1 : Fin d := ⟨r + 1, hr⟩
    have hne_ir : ir ≠ ir1 := by intro h; have := congrArg Fin.val h; dsimp [ir, ir1] at this; omega
    have hsub : (Finset.univ : Finset (Fin d)).filter good ⊆ {ir, ir1} := by
      intro i hi
      have hgi : good i := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnotmem
      push Not at hnotmem
      rcases hnotmem with ⟨h1, h2⟩
      have ha := hgi ir h1.symm
      have hb := hgi ir1 h2.symm
      rw [hsr] at ha; rw [ha] at hb
      have hval1 : i.val ≠ r := fun h => h1 (Fin.ext h)
      have hval2 : i.val ≠ r + 1 := fun h => h2 (Fin.ext h)
      have hiff := Bool.eq_iff_iff.mp hb
      simp only [decide_eq_true_eq, ir, ir1] at hiff
      split_ifs at hiff <;> omega
    have hiff_good : good ir ↔ good ir1 := by
      have haux : ∀ (a b : Fin d), a.val = r → b.val = r + 1 →
          (good a → good b) := by
        intro a b ha hb hga j hj
        by_cases hja : j = a
        · subst hja
          have h1 := hga b (by intro h; have := congrArg Fin.val h; omega)
          have hsab : s j = s b := by
            have hr' : r < d := Nat.lt_of_succ_lt hr
            have he1 : j = ⟨r, hr'⟩ := Fin.ext ha
            have he2 : b = ⟨r + 1, hr⟩ := Fin.ext hb
            exact (congrArg s he1).trans (hsr.trans (congrArg s he2).symm)
          rw [hsab, h1]
          congr 3
          split_ifs <;> omega
        · have h1 := hga j hja
          rw [h1]
          congr 3
          have hjb : j.val ≠ r + 1 := fun h => hj (Fin.ext (by omega))
          have hja' : j.val ≠ r := fun h => hja (Fin.ext (by omega))
          split_ifs <;> omega
      have haux2 : good ir1 → good ir := by
        intro hgb j hj
        by_cases hjb : j = ir1
        · subst hjb
          have h1 := hgb ir hne_ir
          rw [← hsr, h1]
          congr 3
          simp only [ir, ir1]
          split_ifs <;> omega
        · have h1 := hgb j hjb
          rw [h1]
          congr 3
          have hja' : j.val ≠ r := fun h => hj (Fin.ext h)
          have hjb' : j.val ≠ r + 1 := fun h => hjb (Fin.ext h)
          simp only [ir, ir1]
          split_ifs <;> omega
      exact ⟨haux ir ir1 rfl rfl, haux2⟩
    by_cases hgr : good ir
    · have hgr1 : good ir1 := hiff_good.mp hgr
      have heq : (Finset.univ : Finset (Fin d)).filter good = {ir, ir1} := by
        refine Finset.Subset.antisymm hsub ?_
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
      rw [heq, Finset.card_pair hne_ir]
    · have hgr1 : ¬ good ir1 := fun h => hgr (hiff_good.mpr h)
      have heq : (Finset.univ : Finset (Fin d)).filter good = ∅ := by
        ext x; simp only [Finset.notMem_empty, iff_false]
        intro hx
        have hx2 := hsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · exact hgr (Finset.mem_filter.mp hx).2
        · exact hgr1 (Finset.mem_filter.mp hx).2
      rw [heq]; simp
  · push Not at hbad
    have halt : ∀ (k : ℕ) (hk : k < d),
        s ⟨k, hk⟩ = if s ⟨0, by omega⟩ then decide (k % 2 = 0) else decide (k % 2 = 1) := by
      intro k
      induction k with
      | zero =>
        intro _; cases s ⟨0, by omega⟩ <;> simp
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hne := hbad k hk
        cases hs0 : s ⟨0, by omega⟩ <;> rw [hs0] at hprev <;> simp only [↓reduceIte, Bool.false_eq_true] at hprev ⊢
        · cases h1 : s ⟨k + 1, hk⟩ <;> cases h2 : s ⟨k, by omega⟩ <;> rw [h1, h2] at hne
          · exact absurd rfl hne
          · rw [h2] at hprev; have := of_decide_eq_true hprev.symm; symm; exact decide_eq_false (by omega)
          · rw [h2] at hprev; have := of_decide_eq_false hprev.symm; symm; exact decide_eq_true (by omega)
          · exact absurd rfl hne
        · cases h1 : s ⟨k + 1, hk⟩ <;> cases h2 : s ⟨k, by omega⟩ <;> rw [h1, h2] at hne
          · exact absurd rfl hne
          · rw [h2] at hprev; have := of_decide_eq_true hprev.symm; symm; exact decide_eq_false (by omega)
          · rw [h2] at hprev; have := of_decide_eq_false hprev.symm; symm; exact decide_eq_true (by omega)
          · exact absurd rfl hne
    cases hs0 : s ⟨0, by omega⟩
    · have hneg : ∀ j : Fin d, s j = decide (j.val % 2 = 1) := by
        intro j; have := halt j.val j.isLt; rw [hs0] at this; simpa using this
      rw [if_pos (Or.inr hneg)]
      have heq : (Finset.univ : Finset (Fin d)).filter good = {⟨0, by omega⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hgi
          by_contra hne
          have h0 := hgi ⟨0, by omega⟩ (Ne.symm hne)
          have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
          simp only [hs0, hi_pos, ↓reduceIte] at h0
          cases h0
        · rintro rfl j hj
          have hj_pos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
          rw [hneg j]
          simp only [Nat.not_lt_zero, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [heq, Finset.card_singleton]
    · have hpos : ∀ j : Fin d, s j = decide (j.val % 2 = 0) := by
        intro j; have := halt j.val j.isLt; rw [hs0] at this; simpa using this
      rw [if_pos (Or.inl hpos)]
      have heq : (Finset.univ : Finset (Fin d)).filter good = {⟨d - 1, by omega⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hgi
          by_contra hne
          have hi_lt : i.val + 1 < d := by have := i.isLt; have : i.val ≠ d - 1 := fun h => hne (Fin.ext h); omega
          have hnext := hgi ⟨i.val + 1, hi_lt⟩ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
          rw [hpos ⟨i.val + 1, hi_lt⟩] at hnext
          have hiff := Bool.eq_iff_iff.mp hnext
          simp only [decide_eq_true_eq] at hiff
          split_ifs at hiff <;> omega
        · rintro rfl j hj
          have hj_lt : j.val < d - 1 := by
            have := j.isLt; have : j.val ≠ d - 1 := fun h => hj (Fin.ext h); omega
          rw [hpos j]
          simp only [hj_lt, ↓reduceIte]
      rw [heq, Finset.card_singleton]

end BoolSeqParity

section KyFanTucker

abbrev SVec (d : ℕ) := Fin d → Option Bool

def negV {d : ℕ} (v : SVec d) : SVec d := fun i => (v i).map (!·)

lemma negV_invol {d : ℕ} (v : SVec d) : negV (negV v) = v := by
  funext i; dsimp only [negV]; cases v i <;> simp

lemma negV_inj {d : ℕ} : Function.Injective (@negV d) :=
  Function.LeftInverse.injective negV_invol

def supp {d : ℕ} (v : SVec d) : Finset (Fin d) :=
  Finset.univ.filter (fun i : Fin d => (v i).isSome)

lemma mem_supp {d : ℕ} {v : SVec d} {i : Fin d} : i ∈ supp v ↔ (v i).isSome := by
  simp [supp]

lemma supp_negV {d : ℕ} (v : SVec d) : supp (negV v) = supp v := by
  ext i; simp only [mem_supp, negV]; cases v i <;> simp

def leV {d : ℕ} (u v : SVec d) : Prop :=
  ∀ i : Fin d, ∀ b : Bool, u i = some b → v i = some b

lemma leV_refl {d : ℕ} (u : SVec d) : leV u u := fun _ _ h => h

lemma leV_trans {d : ℕ} {u v w : SVec d} (h1 : leV u v) (h2 : leV v w) : leV u w :=
  fun i b h => h2 i b (h1 i b h)

lemma leV_antisymm {d : ℕ} {u v : SVec d} (h1 : leV u v) (h2 : leV v u) : u = v := by
  funext i
  cases hu : u i with
  | none =>
    cases hv : v i with
    | none => rfl
    | some b => have := h2 i b hv; rw [hu] at this; cases this
  | some b => exact (h1 i b hu).symm

lemma leV_negV {d : ℕ} {u v : SVec d} (h : leV u v) : leV (negV u) (negV v) := by
  intro i b hu
  dsimp only [negV] at hu ⊢
  cases hui : u i with
  | none => rw [hui] at hu; cases hu
  | some c =>
    rw [hui] at hu; simp only [Option.map_some, Option.some.injEq] at hu
    rw [h i c hui]; simp [hu]

lemma supp_subset_of_leV {d : ℕ} {u v : SVec d} (h : leV u v) : supp u ⊆ supp v := by
  intro i hi
  rw [mem_supp] at hi ⊢
  cases hui : u i with
  | none => rw [hui] at hi; cases hi
  | some b => rw [h i b hui]; rfl

lemma eq_of_leV_card_eq {d : ℕ} {u v : SVec d} (h : leV u v) (hc : (supp u).card = (supp v).card) :
    u = v := by
  have hsub := supp_subset_of_leV h
  have hsupp_eq := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine leV_antisymm h ?_
  intro i b hvi
  have his : i ∈ supp u := by rw [hsupp_eq, mem_supp, hvi]; rfl
  rw [mem_supp] at his
  cases hui : u i with
  | none => rw [hui] at his; cases his
  | some c =>
    have := h i c hui
    rw [hvi] at this; injection this with hcb; rw [← hcb]

def isChain {d : ℕ} (k : ℕ) (C : Finset (SVec d)) : Prop :=
  C.card = k ∧ (∀ v ∈ C, (supp v).Nonempty) ∧ (∀ u ∈ C, ∀ v ∈ C, leV u v ∨ leV v u)

lemma chain_supp_inj {d k : ℕ} {C : Finset (SVec d)} (hC : isChain k C) :
    Set.InjOn (fun v => (supp v).card) (C : Set (SVec d)) := by
  intro u hu v hv hc
  rcases hC.2.2 u hu v hv with hle | hle
  · exact eq_of_leV_card_eq hle hc
  · exact (eq_of_leV_card_eq hle hc.symm).symm

lemma chain_supp_image_subset {d k : ℕ} {C : Finset (SVec d)} (hC : isChain k C) :
    C.image (fun v => (supp v).card) ⊆ Finset.Icc 1 d := by
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨v, hv, rfl⟩
  rw [Finset.mem_Icc]
  exact ⟨Finset.card_pos.mpr (hC.2.1 v hv), le_trans (Finset.card_le_univ _) (by simp)⟩

lemma chain_le_of_card_le {d k : ℕ} {C : Finset (SVec d)} (hC : isChain k C)
    {u v : SVec d} (hu : u ∈ C) (hv : v ∈ C) (hc : (supp u).card ≤ (supp v).card) :
    leV u v := by
  rcases hC.2.2 u hu v hv with hle | hle
  · exact hle
  · have hsub := Finset.card_le_card (supp_subset_of_leV hle)
    have heq := eq_of_leV_card_eq hle (by omega)
    rw [heq]; exact leV_refl u

def isAlt {d : ℕ} (lam : SVec d → ℤ) (startPos : Bool) (C : Finset (SVec d)) : Prop :=
  (∀ u ∈ C, ∀ v ∈ C, u ≠ v → (lam u).natAbs ≠ (lam v).natAbs) ∧
  ∀ u ∈ C, (0 < lam u) ↔
    ((C.filter (fun v => (lam v).natAbs < (lam u).natAbs)).card % 2 = if startPos then 0 else 1)

lemma isAlt_negV_image {d : ℕ} (lam : SVec d → ℤ)
    (hanti : ∀ v, lam (negV v) = - lam v)
    (hnz : ∀ v, (supp v).Nonempty → lam v ≠ 0)
    (C : Finset (SVec d)) (hCnz : ∀ v ∈ C, (supp v).Nonempty) :
    isAlt lam true (C.image negV) ↔ isAlt lam false C := by
  have h1 : (∀ u ∈ C.image negV, ∀ v ∈ C.image negV, u ≠ v → (lam u).natAbs ≠ (lam v).natAbs) ↔
      (∀ u ∈ C, ∀ v ∈ C, u ≠ v → (lam u).natAbs ≠ (lam v).natAbs) := by
    constructor
    · intro h u hu v hv hne
      have := h (negV u) (Finset.mem_image_of_mem _ hu) (negV v) (Finset.mem_image_of_mem _ hv)
        (fun heq => hne (negV_inj heq))
      simpa [hanti] using this
    · intro h u hu v hv hne
      rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      have := h u' hu' v' hv' (fun heq => hne (congrArg negV heq))
      simpa [hanti] using this
  have hcard : ∀ u ∈ C,
      ((C.image negV).filter (fun v => (lam v).natAbs < (lam (negV u)).natAbs)).card =
      (C.filter (fun v => (lam v).natAbs < (lam u).natAbs)).card := by
    intro u _
    have heq : (C.image negV).filter (fun v => (lam v).natAbs < (lam (negV u)).natAbs) =
        (C.filter (fun v => (lam v).natAbs < (lam u).natAbs)).image negV := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨w', hw', rfl⟩, hlt⟩
        exact ⟨w', ⟨hw', by simpa [hanti] using hlt⟩, rfl⟩
      · rintro ⟨w', ⟨hw', hlt⟩, rfl⟩
        exact ⟨⟨w', hw', rfl⟩, by simpa [hanti] using hlt⟩
    rw [heq, Finset.card_image_of_injective _ negV_inj]
  constructor
  · rintro ⟨hd, hs⟩
    refine ⟨h1.mp hd, fun u hu => ?_⟩
    have hsu := hs (negV u) (Finset.mem_image_of_mem _ hu)
    rw [hcard u hu, hanti u] at hsu
    simp only [↓reduceIte, Bool.false_eq_true] at hsu ⊢
    have hne0 := hnz u (hCnz u hu)
    omega
  · rintro ⟨hd, hs⟩
    refine ⟨h1.mpr hd, fun w hw => ?_⟩
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    have hsu := hs u hu
    rw [hcard u hu, hanti u]
    simp only [↓reduceIte, Bool.false_eq_true] at hsu ⊢
    have hne0 := hnz u (hCnz u hu)
    omega

lemma isAlt_disjoint {d : ℕ} (lam : SVec d → ℤ) (C : Finset (SVec d)) (hC : C.Nonempty) :
    ¬ (isAlt lam true C ∧ isAlt lam false C) := by
  rintro ⟨⟨_, ht⟩, ⟨_, hf⟩⟩
  rcases hC with ⟨u, hu⟩
  have h1 := ht u hu
  have h2 := hf u hu
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h2
  omega

lemma facet_subchain_parity {d : ℕ} (hd : 1 ≤ d) (lam : SVec d → ℤ)
    (F : Finset (SVec d)) (hcard : F.card = d)
    (hnz : ∀ u ∈ F, lam u ≠ 0)
    (hnocomp : ∀ u ∈ F, ∀ v ∈ F, lam u ≠ - lam v) :
    (F.filter (fun u => isAlt lam true (F.erase u))).card % 2 =
      if isAlt lam true F ∨ isAlt lam false F then 1 else 0 := by
  by_cases hdup : ∃ u ∈ F, ∃ v ∈ F, u ≠ v ∧ (lam u).natAbs = (lam v).natAbs
  · rcases hdup with ⟨u, hu, v, hv, hne, habs⟩
    have hlam_eq : lam u = lam v := by
      have hnc := hnocomp u hu v hv
      omega
    have hnot : ¬ (isAlt lam true F ∨ isAlt lam false F) := by
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h u hu v hv hne habs
    rw [if_neg hnot]
    have hsub : F.filter (fun w => isAlt lam true (F.erase w)) ⊆ {u, v} := by
      intro w hw
      have hwa := (Finset.mem_filter.mp hw).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnotmem
      push Not at hnotmem
      exact hwa.1 u (Finset.mem_erase.mpr ⟨Ne.symm hnotmem.1, hu⟩)
        v (Finset.mem_erase.mpr ⟨Ne.symm hnotmem.2, hv⟩) hne habs
    have hswap_iff : isAlt lam true (F.erase u) ↔ isAlt lam true (F.erase v) := by
      have haux : ∀ (a b : SVec d), a ∈ F → b ∈ F → a ≠ b → lam a = lam b →
          isAlt lam true (F.erase a) → isAlt lam true (F.erase b) := by
        intro a b ha hb hab hlab ⟨hd_a, hs_a⟩
        let φ : SVec d → SVec d := fun x => if x = a then b else x
        have hφ_mem : ∀ x ∈ F.erase b, φ x ∈ F.erase a := by
          intro x hx
          rcases Finset.mem_erase.mp hx with ⟨hxb, hxF⟩
          dsimp only [φ]
          split_ifs with hxa
          · exact Finset.mem_erase.mpr ⟨hab.symm, hb⟩
          · exact Finset.mem_erase.mpr ⟨hxa, hxF⟩
        have hφ_lam : ∀ x, lam (φ x) = lam x := by
          intro x; dsimp only [φ]; split_ifs with hxa
          · subst hxa; exact hlab.symm
          · rfl
        have hφ_inj : Set.InjOn φ (F.erase b : Set (SVec d)) := by
          intro x hx y hy heq
          rcases Finset.mem_erase.mp hx with ⟨hxb, _⟩
          rcases Finset.mem_erase.mp hy with ⟨hyb, _⟩
          dsimp only [φ] at heq
          split_ifs at heq with hxa hya
          · rw [hxa, hya]
          · exact absurd heq.symm hyb
          · exact absurd heq hxb
          · exact heq
        have hφ_img : (F.erase b).image φ = F.erase a := by
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro y hy; rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩; exact hφ_mem x hx
          · rw [Finset.card_image_of_injOn hφ_inj, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
        refine ⟨?_, ?_⟩
        · intro x hx y hy hxy
          rw [← hφ_lam x, ← hφ_lam y]
          exact hd_a (φ x) (hφ_mem x hx) (φ y) (hφ_mem y hy) (fun h => hxy (hφ_inj hx hy h))
        · intro x hx
          have h1 := hs_a (φ x) (hφ_mem x hx)
          rw [hφ_lam x] at h1
          have hfc : ((F.erase b).filter (fun z => (lam z).natAbs < (lam x).natAbs)).card =
              ((F.erase a).filter (fun z => (lam z).natAbs < (lam x).natAbs)).card := by
            rw [← hφ_img]
            have heq : ((F.erase b).image φ).filter (fun z => (lam z).natAbs < (lam x).natAbs) =
                ((F.erase b).filter (fun z => (lam z).natAbs < (lam x).natAbs)).image φ := by
              ext z; simp only [Finset.mem_filter, Finset.mem_image]
              constructor
              · rintro ⟨⟨w, hw, rfl⟩, hlt⟩; exact ⟨w, ⟨hw, by rwa [hφ_lam] at hlt⟩, rfl⟩
              · rintro ⟨w, ⟨hw, hlt⟩, rfl⟩; exact ⟨⟨w, hw, rfl⟩, by rwa [hφ_lam]⟩
            rw [heq, Finset.card_image_of_injOn (hφ_inj.mono (Finset.filter_subset _ _))]
          rw [hfc]; exact h1
      exact ⟨haux u v hu hv hne hlam_eq, haux v u hv hu hne.symm hlam_eq.symm⟩
    by_cases hgu : isAlt lam true (F.erase u)
    · have hgv : isAlt lam true (F.erase v) := hswap_iff.mp hgu
      have heq : F.filter (fun w => isAlt lam true (F.erase w)) = {u, v} := by
        refine Finset.Subset.antisymm hsub ?_
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨by assumption, by assumption⟩
      rw [heq, Finset.card_pair hne]
    · have hgv : ¬ isAlt lam true (F.erase v) := fun h => hgu (hswap_iff.mpr h)
      have heq : F.filter (fun w => isAlt lam true (F.erase w)) = ∅ := by
        ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
        have hx2 := hsub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl
        · exact hgu (Finset.mem_filter.mp hx).2
        · exact hgv (Finset.mem_filter.mp hx).2
      rw [heq]; simp
  · push Not at hdup
    let rk : SVec d → ℕ := fun u => (F.filter (fun v => (lam v).natAbs < (lam u).natAbs)).card
    have hrk_lt : ∀ u ∈ F, rk u < d := by
      intro u hu
      have hss : F.filter (fun v => (lam v).natAbs < (lam u).natAbs) ⊂ F := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ F, ?_⟩
        intro heq
        have : u ∈ F.filter (fun v => (lam v).natAbs < (lam u).natAbs) := heq.symm ▸ hu
        exact Nat.lt_irrefl _ (Finset.mem_filter.mp this).2
      have := Finset.card_lt_card hss
      dsimp only [rk]
      omega
    have hrk_strict : ∀ u ∈ F, ∀ v ∈ F, (lam u).natAbs < (lam v).natAbs → rk u < rk v := by
      intro u hu v hv hlt
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
      · intro w hw
        rcases Finset.mem_filter.mp hw with ⟨hwF, hwu⟩
        exact Finset.mem_filter.mpr ⟨hwF, lt_trans hwu hlt⟩
      · intro heq
        have : u ∈ F.filter (fun w => (lam w).natAbs < (lam u).natAbs) :=
          heq ▸ Finset.mem_filter.mpr ⟨hu, hlt⟩
        exact Nat.lt_irrefl _ (Finset.mem_filter.mp this).2
    have hrk_inj : ∀ u ∈ F, ∀ v ∈ F, rk u = rk v → u = v := by
      intro u hu v hv hrk
      by_contra hne
      have hne_abs := hdup u hu v hv hne
      rcases lt_or_gt_of_ne hne_abs with hlt | hgt
      · exact absurd hrk (ne_of_lt (hrk_strict u hu v hv hlt))
      · exact absurd hrk (ne_of_gt (hrk_strict v hv u hu hgt))
    have hrk_bij : ∀ k : Fin d, ∃! u, u ∈ F ∧ rk u = k.val := by
      have himg : F.image (fun u => rk u) = Finset.range d := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro k hk; rcases Finset.mem_image.mp hk with ⟨u, hu, rfl⟩
          exact Finset.mem_range.mpr (hrk_lt u hu)
        · rw [Finset.card_range, Finset.card_image_of_injOn (fun u hu v hv h => hrk_inj u hu v hv h), hcard]
      intro k
      have hk : k.val ∈ F.image (fun u => rk u) := by rw [himg]; exact Finset.mem_range.mpr k.isLt
      rcases Finset.mem_image.mp hk with ⟨u, hu, hru⟩
      exact ⟨u, ⟨hu, hru⟩, fun v ⟨hv, hrv⟩ => hrk_inj v hv u hu (hrv.trans hru.symm)⟩
    let e : Fin d → SVec d := fun k => (hrk_bij k).choose
    have he_mem : ∀ k, e k ∈ F := fun k => (hrk_bij k).choose_spec.1.1
    have he_rk : ∀ k, rk (e k) = k.val := fun k => (hrk_bij k).choose_spec.1.2
    have he_inj : Function.Injective e := by
      intro k1 k2 heq
      exact Fin.ext (by rw [← he_rk k1, ← he_rk k2, heq])
    have he_surj : ∀ u ∈ F, ∃ k : Fin d, e k = u := by
      intro u hu
      let k : Fin d := ⟨rk u, hrk_lt u hu⟩
      exact ⟨k, ((hrk_bij k).choose_spec.2 u ⟨hu, rfl⟩).symm⟩
    have he_lt_iff : ∀ k1 k2 : Fin d, (lam (e k1)).natAbs < (lam (e k2)).natAbs ↔ k1.val < k2.val := by
      intro k1 k2
      constructor
      · intro hlt; have := hrk_strict (e k1) (he_mem k1) (e k2) (he_mem k2) hlt; rw [he_rk, he_rk] at this; exact this
      · intro hlt
        have hne : e k1 ≠ e k2 := fun h => by have := he_inj h; omega
        have hne_abs := hdup (e k1) (he_mem k1) (e k2) (he_mem k2) hne
        rcases lt_or_gt_of_ne hne_abs with h | h
        · exact h
        · have := hrk_strict (e k2) (he_mem k2) (e k1) (he_mem k1) h; rw [he_rk, he_rk] at this; omega
    let s : Fin d → Bool := fun k => decide (0 < lam (e k))
    have hpar := bool_seq_delete_parity d hd s
    dsimp only at hpar
    have hcard_eq : (F.filter (fun u => isAlt lam true (F.erase u))).card =
        ((Finset.univ : Finset (Fin d)).filter fun i =>
          ∀ j : Fin d, j ≠ i → s j = decide ((if j.val < i.val then j.val else j.val - 1) % 2 = 0)).card := by
      refine Finset.card_bij (fun u hu => ⟨rk u, hrk_lt u (Finset.mem_filter.mp hu).1⟩) ?_ ?_ ?_
      · intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huF, halt⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro j hj
        have hju : e j ≠ u := fun h => hj (Fin.ext (by rw [← he_rk j, h]))
        have heu : e ⟨rk u, hrk_lt u huF⟩ = u := ((hrk_bij ⟨rk u, hrk_lt u huF⟩).choose_spec.2 u ⟨huF, rfl⟩).symm
        have hmem_er : e j ∈ F.erase u := Finset.mem_erase.mpr ⟨hju, he_mem j⟩
        have hsj := halt.2 (e j) hmem_er
        simp only [↓reduceIte] at hsj
        have hrc : ((F.erase u).filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card =
            if j.val < rk u then j.val else j.val - 1 := by
          have hfilt_eq : (F.erase u).filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) =
              (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).erase u := by
            ext w; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
          rw [hfilt_eq]
          by_cases hlt : j.val < rk u
          · rw [if_pos hlt]
            have hunot : u ∉ F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) := by
              intro hm
              have habs := (Finset.mem_filter.mp hm).2
              rw [← heu, he_lt_iff] at habs; dsimp at habs; omega
            rw [Finset.erase_eq_of_notMem hunot]; exact he_rk j
          · rw [if_neg hlt]
            have huin : u ∈ F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) := by
              refine Finset.mem_filter.mpr ⟨huF, ?_⟩
              rw [← heu, he_lt_iff]; dsimp
              have hne' : j.val ≠ rk u := fun h => hj (Fin.ext h)
              omega
            rw [Finset.card_erase_of_mem huin]; exact congrArg (· - 1) (he_rk j)
        rw [hrc] at hsj
        dsimp only [s]
        exact Bool.eq_iff_iff.mpr (by simpa [decide_eq_true_eq] using hsj)
      · intro u1 h1 u2 h2 heq
        have := congrArg Fin.val heq
        exact hrk_inj u1 (Finset.mem_filter.mp h1).1 u2 (Finset.mem_filter.mp h2).1 this
      · intro i hi
        have hgi := (Finset.mem_filter.mp hi).2
        refine ⟨e i, Finset.mem_filter.mpr ⟨he_mem i, ?_, ?_⟩, Fin.ext (he_rk i)⟩
        · intro u hu v hv hne
          exact hdup u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv) hne
        · intro u hu
          rcases he_surj u (Finset.mem_of_mem_erase hu) with ⟨j, rfl⟩
          have hji : j ≠ i := fun h => (Finset.mem_erase.mp hu).1 (congrArg e h)
          have hgj := hgi j hji
          have hrc : ((F.erase (e i)).filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card =
              if j.val < i.val then j.val else j.val - 1 := by
            have hfilt_eq : (F.erase (e i)).filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) =
                (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).erase (e i) := by
              ext w; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
            rw [hfilt_eq]
            by_cases hlt : j.val < i.val
            · rw [if_pos hlt]
              have hinot : e i ∉ F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) := by
                intro hm; have := (he_lt_iff i j).mp (Finset.mem_filter.mp hm).2; omega
              rw [Finset.erase_eq_of_notMem hinot]; exact he_rk j
            · rw [if_neg hlt]
              have hiin : e i ∈ F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs) :=
                Finset.mem_filter.mpr ⟨he_mem i, (he_lt_iff i j).mpr (by have : j.val ≠ i.val := fun h => hji (Fin.ext h); omega)⟩
              rw [Finset.card_erase_of_mem hiin]; exact congrArg (· - 1) (he_rk j)
          rw [hrc]; simp only [↓reduceIte]
          have hiff := Bool.eq_iff_iff.mp hgj
          simpa [s, decide_eq_true_eq] using hiff
    have hiff_alt : (isAlt lam true F ∨ isAlt lam false F) ↔
        ((∀ j : Fin d, s j = decide (j.val % 2 = 0)) ∨ (∀ j : Fin d, s j = decide (j.val % 2 = 1))) := by
      have h1 : isAlt lam true F ↔ ∀ j : Fin d, s j = decide (j.val % 2 = 0) := by
        constructor
        · rintro ⟨_, hs⟩ j
          have := hs (e j) (he_mem j)
          rw [show (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card = j.val from he_rk j] at this
          simp only [↓reduceIte] at this
          exact Bool.eq_iff_iff.mpr (by simpa [s, decide_eq_true_eq] using this)
        · intro hs
          refine ⟨hdup, fun u hu => ?_⟩
          rcases he_surj u hu with ⟨j, rfl⟩
          rw [show (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card = j.val from he_rk j]
          simp only [↓reduceIte]
          have hiff := Bool.eq_iff_iff.mp (hs j)
          simpa [s, decide_eq_true_eq] using hiff
      have h2 : isAlt lam false F ↔ ∀ j : Fin d, s j = decide (j.val % 2 = 1) := by
        constructor
        · rintro ⟨_, hs⟩ j
          have := hs (e j) (he_mem j)
          rw [show (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card = j.val from he_rk j] at this
          simp only [Bool.false_eq_true, ↓reduceIte] at this
          exact Bool.eq_iff_iff.mpr (by simpa [s, decide_eq_true_eq] using this)
        · intro hs
          refine ⟨hdup, fun u hu => ?_⟩
          rcases he_surj u hu with ⟨j, rfl⟩
          rw [show (F.filter (fun v => (lam v).natAbs < (lam (e j)).natAbs)).card = j.val from he_rk j]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hiff := Bool.eq_iff_iff.mp (hs j)
          simpa [s, decide_eq_true_eq] using hiff
      rw [h1, h2]
    rw [hcard_eq, hpar]
    simp only [hiff_alt]

def inU {d : ℕ} (C : Finset (SVec (d + 1))) : Prop :=
  ∀ v ∈ C, v (Fin.last d) ≠ some false

def inE {d : ℕ} (C : Finset (SVec (d + 1))) : Prop :=
  ∀ v ∈ C, v (Fin.last d) = none

def embedV {d : ℕ} (v : SVec d) : SVec (d + 1) :=
  fun i => if h : i.val < d then v ⟨i.val, h⟩ else none

def projV {d : ℕ} (v : SVec (d + 1)) : SVec d :=
  fun i => v i.castSucc

lemma embedV_last {d : ℕ} (v : SVec d) : embedV v (Fin.last d) = none := by
  simp [embedV]

lemma projV_embedV {d : ℕ} (v : SVec d) : projV (embedV v) = v := by
  funext i; simp [projV, embedV, i.isLt]

lemma embedV_projV {d : ℕ} {v : SVec (d + 1)} (h : v (Fin.last d) = none) :
    embedV (projV v) = v := by
  funext i
  dsimp only [embedV, projV]
  split_ifs with hi
  · rfl
  · have : i = Fin.last d := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
    rw [this, h]

lemma embedV_inj {d : ℕ} : Function.Injective (@embedV d) :=
  Function.LeftInverse.injective projV_embedV

lemma embedV_negV {d : ℕ} (v : SVec d) : embedV (negV v) = negV (embedV v) := by
  funext i; dsimp only [embedV, negV]; split_ifs <;> simp

lemma embedV_leV {d : ℕ} {u v : SVec d} : leV (embedV u) (embedV v) ↔ leV u v := by
  constructor
  · intro h i b hui
    have := h i.castSucc b (by simp [embedV, i.isLt, hui])
    simpa [embedV, i.isLt] using this
  · intro h i b hui
    dsimp only [embedV] at hui ⊢
    by_cases hi : i.val < d
    · rw [dif_pos hi] at hui ⊢
      exact h ⟨i.val, hi⟩ b hui
    · rw [dif_neg hi] at hui
      cases hui

lemma embedV_supp_nonempty {d : ℕ} {v : SVec d} :
    (supp (embedV v)).Nonempty ↔ (supp v).Nonempty := by
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_supp] at hi
    dsimp only [embedV] at hi
    split_ifs at hi with hlt
    · exact ⟨⟨i.val, hlt⟩, mem_supp.mpr hi⟩
    · cases hi
  · rintro ⟨i, hi⟩
    exact ⟨i.castSucc, by rw [mem_supp]; simpa [embedV, i.isLt] using mem_supp.mp hi⟩

lemma ridge_facets_card {d : ℕ} (hd : 1 ≤ d) (R : Finset (SVec (d + 1)))
    (hR : isChain d R) (hRU : inU R) :
    ((Finset.univ : Finset (Finset (SVec (d + 1)))).filter
      (fun F => isChain (d + 1) F ∧ inU F ∧ R ⊆ F)).card =
      if inE R then 1 else 2 := by
  -- Map each facet F extending R to its unique new element w ∈ F \ R
  let extW : Finset (SVec (d + 1)) :=
    (Finset.univ : Finset (SVec (d + 1))).filter
      (fun w => w ∉ R ∧ (supp w).Nonempty ∧ w (Fin.last d) ≠ some false ∧
        ∀ u ∈ R, leV w u ∨ leV u w)
  have hbij : ((Finset.univ : Finset (Finset (SVec (d + 1)))).filter
      (fun F => isChain (d + 1) F ∧ inU F ∧ R ⊆ F)).card = extW.card := by
    refine Finset.card_bij (fun F hF => ?_) ?_ ?_ ?_
    · have hmem := (Finset.mem_filter.mp hF).2
      have hcard_sdiff : (F \ R).card = 1 := by
        rw [card_sdiff_sub hmem.2.2, hmem.1.1, hR.1]; omega
      exact (Finset.card_eq_one.mp hcard_sdiff).choose
    · intro F hF
      have hmem := (Finset.mem_filter.mp hF).2
      have hcard_sdiff : (F \ R).card = 1 := by
        rw [card_sdiff_sub hmem.2.2, hmem.1.1, hR.1]; omega
      set w := (Finset.card_eq_one.mp hcard_sdiff).choose
      have hw_eq : F \ R = {w} := (Finset.card_eq_one.mp hcard_sdiff).choose_spec
      have hw_sdiff : w ∈ F \ R := hw_eq.symm ▸ Finset.mem_singleton_self w
      rcases Finset.mem_sdiff.mp hw_sdiff with ⟨hwF, hwR⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwR, hmem.1.2.1 w hwF, hmem.2.1 w hwF,
        fun u hu => hmem.1.2.2 w hwF u (hmem.2.2 hu)⟩
    · intro F1 hF1 F2 hF2 heq
      have hm1 := (Finset.mem_filter.mp hF1).2
      have hm2 := (Finset.mem_filter.mp hF2).2
      have hc1 : (F1 \ R).card = 1 := by rw [card_sdiff_sub hm1.2.2, hm1.1.1, hR.1]; omega
      have hc2 : (F2 \ R).card = 1 := by rw [card_sdiff_sub hm2.2.2, hm2.1.1, hR.1]; omega
      have hs1 : F1 \ R = {(Finset.card_eq_one.mp hc1).choose} := (Finset.card_eq_one.mp hc1).choose_spec
      have hs2 : F2 \ R = {(Finset.card_eq_one.mp hc2).choose} := (Finset.card_eq_one.mp hc2).choose_spec
      have h1 : F1 = (F1 \ R) ∪ R := (Finset.sdiff_union_of_subset hm1.2.2).symm
      have h2 : F2 = (F2 \ R) ∪ R := (Finset.sdiff_union_of_subset hm2.2.2).symm
      rw [h1, h2, hs1, hs2, heq]
    · intro w hw
      rcases (Finset.mem_filter.mp hw).2 with ⟨hwR, hwnz, hwU, hwcomp⟩
      let F := insert w R
      have hFmem : F ∈ (Finset.univ : Finset (Finset (SVec (d + 1)))).filter
          (fun F => isChain (d + 1) F ∧ inU F ∧ R ⊆ F) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ F, ⟨?_, ?_, ?_⟩, ?_, Finset.subset_insert w R⟩
        · rw [Finset.card_insert_of_notMem hwR, hR.1]
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hvR
          · exact hwnz
          · exact hR.2.1 v hvR
        · intro u hu v hv
          rcases Finset.mem_insert.mp hu with rfl | huR
          · rcases Finset.mem_insert.mp hv with rfl | hvR
            · exact Or.inl (leV_refl _)
            · exact hwcomp v hvR
          · rcases Finset.mem_insert.mp hv with rfl | hvR
            · exact (hwcomp u huR).symm
            · exact hR.2.2 u huR v hvR
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hvR
          · exact hwU
          · exact hRU v hvR
      refine ⟨F, hFmem, ?_⟩
      have hc : (F \ R).card = 1 := by
        have hsd : F \ R = {w} := by
          ext x; simp only [F, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hR', hnot⟩
            · rfl
            · exact absurd hR' hnot
          · rintro rfl; exact ⟨Or.inl rfl, hwR⟩
        rw [hsd, Finset.card_singleton]
      have hspec := (Finset.card_eq_one.mp hc).choose_spec
      have hmem : (Finset.card_eq_one.mp hc).choose ∈ F \ R :=
        (Finset.ext_iff.mp hspec _).mpr (Finset.mem_singleton_self _)
      rcases Finset.mem_sdiff.mp hmem with ⟨hF', hnotR⟩
      rcases Finset.mem_insert.mp hF' with h | h
      · exact h
      · exact absurd h hnotR
  rw [hbij]
  -- Determine the unique missing size s* in Icc 1 (d + 1) \ R.image (fun v => (supp v).card)
  let sizes := R.image (fun v => (supp v).card)
  have hsizes_sub : sizes ⊆ Finset.Icc 1 (d + 1) := chain_supp_image_subset hR
  have hsizes_card : sizes.card = d := by
    rw [Finset.card_image_of_injOn (chain_supp_inj hR), hR.1]
  have hmiss_card : (Finset.Icc 1 (d + 1) \ sizes).card = 1 := by
    rw [card_sdiff_sub hsizes_sub, Nat.card_Icc, hsizes_card]; omega
  rcases Finset.card_eq_one.mp hmiss_card with ⟨s, hs_eq⟩
  have hs_mem : s ∈ Finset.Icc 1 (d + 1) \ sizes := hs_eq.symm ▸ Finset.mem_singleton_self s
  rcases Finset.mem_sdiff.mp hs_mem with ⟨hs_icc, hs_not⟩
  rw [Finset.mem_Icc] at hs_icc
  have hother_mem : ∀ t : ℕ, 1 ≤ t → t ≤ d + 1 → t ≠ s → ∃ u ∈ R, (supp u).card = t := by
    intro t ht1 ht2 hts
    have ht_icc : t ∈ Finset.Icc 1 (d + 1) := Finset.mem_Icc.mpr ⟨ht1, ht2⟩
    have ht_in : t ∈ sizes := by
      by_contra hnot
      have : t ∈ Finset.Icc 1 (d + 1) \ sizes := Finset.mem_sdiff.mpr ⟨ht_icc, hnot⟩
      rw [hs_eq, Finset.mem_singleton] at this
      exact hts this
    exact Finset.mem_image.mp ht_in
  have hw_size : ∀ w ∈ extW, (supp w).card = s := by
    intro w hw
    rcases (Finset.mem_filter.mp hw).2 with ⟨hwR, hwnz, _, hwcomp⟩
    have hcard_in : (supp w).card ∈ Finset.Icc 1 (d + 1) :=
      Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hwnz, le_trans (Finset.card_le_univ _) (by simp)⟩
    have hnot_in : (supp w).card ∉ sizes := by
      intro hin
      rcases Finset.mem_image.mp hin with ⟨u, huR, hcu⟩
      rcases hwcomp u huR with hle | hle
      · exact hwR (eq_of_leV_card_eq hle hcu.symm ▸ huR)
      · exact hwR ((eq_of_leV_card_eq hle hcu).symm ▸ huR)
    have : (supp w).card ∈ Finset.Icc 1 (d + 1) \ sizes := Finset.mem_sdiff.mpr ⟨hcard_in, hnot_in⟩
    rw [hs_eq, Finset.mem_singleton] at this
    exact this
  -- Case split on s = d + 1 vs s = 1 vs 2 ≤ s ≤ d
  by_cases hsd : s = d + 1
  · rcases hother_mem d (by omega) (by omega) (by omega) with ⟨umax, humaxR, humaxC⟩
    have humax_top : ∀ u ∈ R, leV u umax := by
      intro u huR
      have hcu : (supp u).card ≤ d := by
        have h1 : (supp u).card ∈ sizes := Finset.mem_image_of_mem _ huR
        have h2 := hsizes_sub h1
        rw [Finset.mem_Icc] at h2
        have hne : (supp u).card ≠ d + 1 := fun heq => hs_not (hsd ▸ heq ▸ h1)
        omega
      exact chain_le_of_card_le hR huR humaxR (by omega)
    have hmiss_coord_card : (Finset.univ \ supp umax).card = 1 := by
      rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, humaxC]; omega
    rcases Finset.card_eq_one.mp hmiss_coord_card with ⟨i0, hi0_eq⟩
    have hi0_not : i0 ∉ supp umax := by
      have : i0 ∈ Finset.univ \ supp umax := hi0_eq.symm ▸ Finset.mem_singleton_self i0
      exact (Finset.mem_sdiff.mp this).2
    have hi0_none : umax i0 = none := by
      rw [mem_supp] at hi0_not; cases h : umax i0 <;> simp_all
    have hother_some : ∀ i : Fin (d + 1), i ≠ i0 → (umax i).isSome := by
      intro i hi
      by_contra hnot
      have : i ∈ Finset.univ \ supp umax := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by rw [mem_supp]; exact hnot⟩
      rw [hi0_eq, Finset.mem_singleton] at this
      exact hi this
    let extB : Bool → SVec (d + 1) := fun b i => if i = i0 then some b else umax i
    have hextB_le : ∀ b, leV umax (extB b) := by
      intro b i c hui
      dsimp only [extB]
      split_ifs with hi
      · subst hi; rw [hi0_none] at hui; cases hui
      · exact hui
    have hextB_supp : ∀ b, supp (extB b) = Finset.univ := by
      intro b; ext i; simp only [mem_supp, extB, Finset.mem_univ, iff_true]
      split_ifs with hi
      · rfl
      · exact hother_some i hi
    have hextB_notR : ∀ b, extB b ∉ R := by
      intro b hmem
      have : (supp (extB b)).card ∈ sizes := Finset.mem_image_of_mem _ hmem
      rw [hextB_supp b, Finset.card_univ, Fintype.card_fin] at this
      exact hs_not (hsd ▸ this)
    have hextB_inj : extB true ≠ extB false := by
      intro h; have := congrFun h i0; simp [extB] at this
    have hw_is_extB : ∀ w ∈ extW, w = extB true ∨ w = extB false := by
      intro w hw
      have hwc : (supp w).card = d + 1 := by rw [hw_size w hw, hsd]
      have hw_le : leV umax w := by
        rcases (Finset.mem_filter.mp hw).2.2.2.2 umax humaxR with hle | hle
        · have := Finset.card_le_card (supp_subset_of_leV hle); omega
        · exact hle
      have hwsupp : supp w = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hwc, Fintype.card_fin])
      have hwi0 : (w i0).isSome := mem_supp.mp (hwsupp.symm ▸ Finset.mem_univ i0)
      cases hb : w i0 with
      | none => rw [hb] at hwi0; cases hwi0
      | some b =>
        have hweq : w = extB b := by
          funext i; dsimp only [extB]
          split_ifs with hi
          · subst hi; exact hb
          · have hs := hother_some i hi
            cases huc : umax i with
            | none => rw [huc] at hs; cases hs
            | some c => exact hw_le i c huc
        cases b
        · exact Or.inr hweq
        · exact Or.inl hweq
    have hinE_iff : inE R ↔ i0 = Fin.last d := by
      constructor
      · intro hE
        have hlast := hE umax humaxR
        by_contra hne
        have := hother_some (Fin.last d) (Ne.symm hne)
        rw [hlast] at this; cases this
      · intro hi0_last u huR
        have hle := humax_top u huR
        cases hu : u (Fin.last d) with
        | none => rfl
        | some b =>
          have := hle (Fin.last d) b hu
          rw [← hi0_last, hi0_none] at this; cases this
    by_cases hE : inE R
    · rw [if_pos hE]
      have hi0_last : i0 = Fin.last d := hinE_iff.mp hE
      have heq : extW = {extB true} := by
        ext w; simp only [Finset.mem_singleton]
        constructor
        · intro hw
          rcases hw_is_extB w hw with rfl | rfl
          · rfl
          · exfalso
            have hU := (Finset.mem_filter.mp hw).2.2.2.1
            rw [← hi0_last] at hU; simp [extB] at hU
        · rintro rfl
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hextB_notR true, ?_, ?_, ?_⟩
          · rw [hextB_supp]; exact ⟨Fin.last d, Finset.mem_univ _⟩
          · rw [← hi0_last]; simp [extB]
          · intro u huR; exact Or.inr (leV_trans (humax_top u huR) (hextB_le true))
      rw [heq, Finset.card_singleton]
    · rw [if_neg hE]
      have hi0_ne : i0 ≠ Fin.last d := fun h => hE (hinE_iff.mpr h)
      have heq : extW = {extB true, extB false} := by
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact hw_is_extB w
        · rintro (rfl | rfl) <;>
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hextB_notR _, ?_, ?_, ?_⟩
            · rw [hextB_supp]; exact ⟨Fin.last d, Finset.mem_univ _⟩
            · dsimp only [extB]; rw [if_neg hi0_ne.symm]; exact hRU umax humaxR
            · intro u huR; exact Or.inr (leV_trans (humax_top u huR) (hextB_le _))
      rw [heq, Finset.card_pair hextB_inj]
  · -- s ≤ d: so R contains an element umax of size d + 1, hence ¬ inE R!
    have hnotE : ¬ inE R := by
      intro hE
      rcases hother_mem (d + 1) (by omega) (le_refl _) (by omega) with ⟨umax, humaxR, humaxC⟩
      have hfull : supp umax = Finset.univ := Finset.eq_univ_of_card _ (by rw [humaxC, Fintype.card_fin])
      have hs := mem_supp.mp (hfull.symm ▸ Finset.mem_univ (Fin.last d))
      rw [hE umax humaxR] at hs; cases hs
    rw [if_neg hnotE]
    by_cases hs1 : s = 1
    · rcases hother_mem 2 (by omega) (by omega) (by omega) with ⟨u2, hu2R, hu2C⟩
      have hu2_bot : ∀ u ∈ R, leV u2 u := by
        intro u huR
        have hcu : 2 ≤ (supp u).card := by
          have h1 : (supp u).card ∈ sizes := Finset.mem_image_of_mem _ huR
          have h2 := hsizes_sub h1; rw [Finset.mem_Icc] at h2
          have hne : (supp u).card ≠ 1 := fun heq => hs_not (hs1 ▸ heq ▸ h1)
          omega
        exact chain_le_of_card_le hR hu2R huR (by omega)
      rcases Finset.card_eq_two.mp hu2C with ⟨i1, i2, hi12, hsupp2⟩
      let wOf : Fin (d + 1) → SVec (d + 1) := fun idx i => if i = idx then u2 idx else none
      have hwOf_mem : ∀ idx ∈ ({i1, i2} : Finset (Fin (d + 1))), wOf idx ∈ extW := by
        intro idx hidx
        have hidx_supp : idx ∈ supp u2 := hsupp2.symm ▸ hidx
        have hidx_some : (u2 idx).isSome := mem_supp.mp hidx_supp
        have hle : leV (wOf idx) u2 := by
          intro i b hw
          by_cases hi : i = idx
          · subst hi; simpa [wOf] using hw
          · simp [wOf, hi] at hw
        have hsupp_w : supp (wOf idx) = {idx} := by
          ext i; simp only [mem_supp, wOf, Finset.mem_singleton]
          split_ifs with hi
          · subst hi; simpa using hidx_some
          · simp [hi]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
        · intro hmem
          have : (supp (wOf idx)).card ∈ sizes := Finset.mem_image_of_mem _ hmem
          rw [hsupp_w, Finset.card_singleton] at this; exact hs_not (hs1 ▸ this)
        · rw [hsupp_w]; exact Finset.singleton_nonempty idx
        · intro hf
          have := hle (Fin.last d) false hf
          exact hRU u2 hu2R this
        · intro u huR; exact Or.inl (leV_trans hle (hu2_bot u huR))
      have hw_ne : wOf i1 ≠ wOf i2 := by
        intro heq
        have h1 := congrFun heq i1
        have hsome : (u2 i1).isSome := mem_supp.mp (hsupp2.symm ▸ Finset.mem_insert_self i1 {i2})
        simp only [wOf, ↓reduceIte, hi12, ↓reduceIte] at h1
        rw [h1] at hsome; cases hsome
      have heq : extW = {wOf i1, wOf i2} := by
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hw
          have hwc : (supp w).card = 1 := by rw [hw_size w hw, hs1]
          have hw_le : leV w u2 := by
            rcases (Finset.mem_filter.mp hw).2.2.2.2 u2 hu2R with hle | hle
            · exact hle
            · have := Finset.card_le_card (supp_subset_of_leV hle); omega
          rcases Finset.card_eq_one.mp hwc with ⟨idx, hidx_eq⟩
          have hidx_in : idx ∈ supp u2 := supp_subset_of_leV hw_le (hidx_eq.symm ▸ Finset.mem_singleton_self idx)
          rw [hsupp2, Finset.mem_insert, Finset.mem_singleton] at hidx_in
          have hweq : w = wOf idx := by
            funext i; dsimp only [wOf]
            split_ifs with hi
            · subst hi
              have hs : (w i).isSome := mem_supp.mp (hidx_eq.symm ▸ Finset.mem_singleton_self i)
              cases hwc' : w i with
              | none => rw [hwc'] at hs; cases hs
              | some b => exact (hw_le i b hwc').symm
            · by_contra hne
              have : i ∈ supp w := by rw [mem_supp]; cases h : w i <;> simp_all
              rw [hidx_eq, Finset.mem_singleton] at this; exact hi this
          rcases hidx_in with rfl | rfl
          · exact Or.inl hweq
          · exact Or.inr hweq
        · rintro (rfl | rfl)
          · exact hwOf_mem i1 (Finset.mem_insert_self i1 {i2})
          · exact hwOf_mem i2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self i2))
      rw [heq, Finset.card_pair hw_ne]
    · -- 2 ≤ s ≤ d
      rcases hother_mem (s - 1) (by omega) (by omega) (by omega) with ⟨ulo, huloR, huloC⟩
      rcases hother_mem (s + 1) (by omega) (by omega) (by omega) with ⟨uhi, huhiR, huhiC⟩
      have hlo_hi : leV ulo uhi := chain_le_of_card_le hR huloR huhiR (by omega)
      have hsplit_R : ∀ u ∈ R, leV u ulo ∨ leV uhi u := by
        intro u huR
        have h1 : (supp u).card ∈ sizes := Finset.mem_image_of_mem _ huR
        have hne : (supp u).card ≠ s := fun heq => hs_not (heq ▸ h1)
        by_cases hlt : (supp u).card < s
        · exact Or.inl (chain_le_of_card_le hR huR huloR (by omega))
        · exact Or.inr (chain_le_of_card_le hR huhiR huR (by omega))
      have hsdiff_card : (supp uhi \ supp ulo).card = 2 := by
        rw [card_sdiff_sub (supp_subset_of_leV hlo_hi), huhiC, huloC]; omega
      rcases Finset.card_eq_two.mp hsdiff_card with ⟨i1, i2, hi12, hsdiff_eq⟩
      let wOf : Fin (d + 1) → SVec (d + 1) := fun idx i => if i = idx then uhi idx else ulo i
      have hwOf_mem : ∀ idx ∈ ({i1, i2} : Finset (Fin (d + 1))), wOf idx ∈ extW := by
        intro idx hidx
        have hidx_sd : idx ∈ supp uhi \ supp ulo := hsdiff_eq.symm ▸ hidx
        rcases Finset.mem_sdiff.mp hidx_sd with ⟨hidx_hi, hidx_nlo⟩
        have hidx_hi_s : (uhi idx).isSome := mem_supp.mp hidx_hi
        have hidx_lo_n : ulo idx = none := by rw [mem_supp] at hidx_nlo; cases h : ulo idx <;> simp_all
        have hle1 : leV ulo (wOf idx) := by
          intro i b h; dsimp only [wOf]; split_ifs with hi
          · subst hi; rw [hidx_lo_n] at h; cases h
          · exact h
        have hle2 : leV (wOf idx) uhi := by
          intro i b h; dsimp only [wOf] at h; split_ifs at h with hi
          · subst hi; exact h
          · exact hlo_hi i b h
        have hsupp_w : supp (wOf idx) = insert idx (supp ulo) := by
          ext i; simp only [mem_supp, wOf, Finset.mem_insert]
          split_ifs with hi
          · subst hi; simpa using hidx_hi_s
          · simp [hi]
        have hwcard : (supp (wOf idx)).card = s := by
          rw [hsupp_w, Finset.card_insert_of_notMem hidx_nlo, huloC]; omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
        · intro hmem
          have : (supp (wOf idx)).card ∈ sizes := Finset.mem_image_of_mem _ hmem
          rw [hwcard] at this; exact hs_not this
        · exact Finset.card_pos.mp (by omega)
        · intro hf; exact hRU uhi huhiR (hle2 (Fin.last d) false hf)
        · intro u huR
          rcases hsplit_R u huR with h | h
          · exact Or.inr (leV_trans h hle1)
          · exact Or.inl (leV_trans hle2 h)
      have hw_ne : wOf i1 ≠ wOf i2 := by
        intro heq
        have h1 := congrFun heq i1
        have hidx_sd : i1 ∈ supp uhi \ supp ulo := hsdiff_eq.symm ▸ Finset.mem_insert_self i1 {i2}
        rcases Finset.mem_sdiff.mp hidx_sd with ⟨hhi, hnlo⟩
        have hlo_n : ulo i1 = none := by rw [mem_supp] at hnlo; cases h : ulo i1 <;> simp_all
        have hhi_s : (uhi i1).isSome := mem_supp.mp hhi
        simp only [wOf, ↓reduceIte, hi12, ↓reduceIte, hlo_n] at h1
        rw [h1] at hhi_s; cases hhi_s
      have heq : extW = {wOf i1, wOf i2} := by
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hw
          have hwc : (supp w).card = s := hw_size w hw
          have hcomp := (Finset.mem_filter.mp hw).2.2.2.2
          have hle1 : leV ulo w := by
            rcases hcomp ulo huloR with hle | hle
            · have := Finset.card_le_card (supp_subset_of_leV hle); omega
            · exact hle
          have hle2 : leV w uhi := by
            rcases hcomp uhi huhiR with hle | hle
            · exact hle
            · have := Finset.card_le_card (supp_subset_of_leV hle); omega
          have hsd_w : (supp w \ supp ulo).card = 1 := by
            rw [card_sdiff_sub (supp_subset_of_leV hle1), hwc, huloC]; omega
          rcases Finset.card_eq_one.mp hsd_w with ⟨idx, hidx_eq⟩
          have hidx_in : idx ∈ supp w \ supp ulo := hidx_eq.symm ▸ Finset.mem_singleton_self idx
          rcases Finset.mem_sdiff.mp hidx_in with ⟨hidx_w, hidx_nlo⟩
          have hidx_hi : idx ∈ supp uhi \ supp ulo :=
            Finset.mem_sdiff.mpr ⟨supp_subset_of_leV hle2 hidx_w, hidx_nlo⟩
          rw [hsdiff_eq, Finset.mem_insert, Finset.mem_singleton] at hidx_hi
          have hweq : w = wOf idx := by
            funext i; dsimp only [wOf]
            split_ifs with hi
            · subst hi
              have hs := mem_supp.mp hidx_w
              cases hwb : w i with
              | none => rw [hwb] at hs; cases hs
              | some b => exact (hle2 i b hwb).symm
            · by_cases hilo : i ∈ supp ulo
              · have hs := mem_supp.mp hilo
                cases hub : ulo i with
                | none => rw [hub] at hs; cases hs
                | some b => exact hle1 i b hub
              · have hlo_n : ulo i = none := by rw [mem_supp] at hilo; cases h : ulo i <;> simp_all
                rw [hlo_n]
                by_contra hne
                have hiw : i ∈ supp w := by rw [mem_supp]; cases h : w i <;> simp_all
                have : i ∈ supp w \ supp ulo := Finset.mem_sdiff.mpr ⟨hiw, hilo⟩
                rw [hidx_eq, Finset.mem_singleton] at this; exact hi this
          rcases hidx_hi with rfl | rfl
          · exact Or.inl hweq
          · exact Or.inr hweq
        · rintro (rfl | rfl)
          · exact hwOf_mem i1 (Finset.mem_insert_self i1 {i2})
          · exact hwOf_mem i2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self i2))
      rw [heq, Finset.card_pair hw_ne]

lemma ky_fan_odd : ∀ (d : ℕ), 1 ≤ d →
    ∀ (lam : SVec d → ℤ),
      (∀ v, (supp v).Nonempty → lam v ≠ 0) →
      (∀ v, lam (negV v) = - lam v) →
      (∀ u v, (supp u).Nonempty → (supp v).Nonempty → leV u v → lam u ≠ - lam v) →
      ((Finset.univ : Finset (Finset (SVec d))).filter (fun F => isChain d F ∧ isAlt lam true F)).card % 2 = 1 := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
    intro _ lam hnz hanti hnocomp
    cases d with
    | zero =>
      let vp : SVec 1 := fun _ => some true
      let vm : SVec 1 := fun _ => some false
      have hne_pm : vp ≠ vm := by intro h; have := congrFun h 0; simp [vp, vm] at this
      have hneg_pm : negV vp = vm := by funext i; simp [negV, vp, vm]
      have hsupp_p : (supp vp).Nonempty := ⟨0, by simp [mem_supp, vp]⟩
      have hsupp_m : (supp vm).Nonempty := ⟨0, by simp [mem_supp, vm]⟩
      have hchain_iff : ∀ F : Finset (SVec 1), isChain 1 F ↔ F = {vp} ∨ F = {vm} := by
        intro F
        constructor
        · rintro ⟨hcard, hne, _⟩
          rcases Finset.card_eq_one.mp hcard with ⟨v, rfl⟩
          have hv0 : (v 0).isSome := by
            rcases hne v (Finset.mem_singleton_self v) with ⟨i, hi⟩
            have hi0 : i = 0 := Fin.ext (by omega)
            rw [← hi0]; exact mem_supp.mp hi
          cases hvb : v 0 with
          | none => rw [hvb] at hv0; cases hv0
          | some b =>
            have hveq : v = if b then vp else vm := by
              funext i; have hi0 : i = 0 := Fin.ext (by omega); rw [hi0, hvb]; cases b <;> rfl
            cases b
            · exact Or.inr (by rw [hveq]; rfl)
            · exact Or.inl (by rw [hveq]; rfl)
        · rintro (rfl | rfl)
          · exact ⟨Finset.card_singleton _, fun v hv => by simp at hv; subst hv; exact hsupp_p,
              fun u hu v hv => by simp at hu hv; subst hu; subst hv; exact Or.inl (leV_refl _)⟩
          · exact ⟨Finset.card_singleton _, fun v hv => by simp at hv; subst hv; exact hsupp_m,
              fun u hu v hv => by simp at hu hv; subst hu; subst hv; exact Or.inl (leV_refl _)⟩
      have halt_sing : ∀ v : SVec 1, isAlt lam true {v} ↔ 0 < lam v := by
        intro v
        constructor
        · rintro ⟨_, hs⟩
          have := hs v (Finset.mem_singleton_self v)
          have hfilt : ({v} : Finset (SVec 1)).filter (fun w => (lam w).natAbs < (lam v).natAbs) = ∅ := by
            ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl; exact Nat.lt_irrefl _
          rw [hfilt] at this; simpa using this
        · intro hpos
          refine ⟨fun u hu w hw hne => by simp at hu hw; subst hu; subst hw; exact absurd rfl hne,
            fun u hu => ?_⟩
          simp at hu; subst hu
          have hfilt : ({u} : Finset (SVec 1)).filter (fun w => (lam w).natAbs < (lam u).natAbs) = ∅ := by
            ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl; exact Nat.lt_irrefl _
          rw [hfilt]; simpa using hpos
      have hlam_ne0 : lam vp ≠ 0 := hnz vp hsupp_p
      have hlam_neg : lam vm = - lam vp := by rw [← hneg_pm, hanti]
      by_cases hp : 0 < lam vp
      · have heq : (Finset.univ : Finset (Finset (SVec 1))).filter
            (fun F => isChain 1 F ∧ isAlt lam true F) = {{vp}} := by
          ext F; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hchain_iff]
          constructor
          · rintro ⟨rfl | rfl, ha⟩
            · rfl
            · have := (halt_sing vm).mp ha; omega
          · rintro rfl; exact ⟨Or.inl rfl, (halt_sing vp).mpr hp⟩
        rw [heq, Finset.card_singleton]
      · have hm : 0 < lam vm := by omega
        have heq : (Finset.univ : Finset (Finset (SVec 1))).filter
            (fun F => isChain 1 F ∧ isAlt lam true F) = {{vm}} := by
          ext F; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hchain_iff]
          constructor
          · rintro ⟨rfl | rfl, ha⟩
            · have := (halt_sing vp).mp ha; omega
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, (halt_sing vm).mpr hm⟩
        rw [heq, Finset.card_singleton]
    | succ d' =>
      let m := d' + 1
      have hd : 1 ≤ m := by omega
      let lamE : SVec m → ℤ := fun v => lam (embedV v)
      have hih := ih hd lamE
        (fun v hv => hnz (embedV v) (embedV_supp_nonempty.mpr hv))
        (fun v => by dsimp only [lamE]; rw [embedV_negV, hanti])
        (fun u v hu hv hle => hnocomp (embedV u) (embedV v)
          (embedV_supp_nonempty.mpr hu) (embedV_supp_nonempty.mpr hv) (embedV_leV.mpr hle))
      let FacetsAll := (Finset.univ : Finset (Finset (SVec (m + 1)))).filter (fun F => isChain (m + 1) F)
      let FacetsU := FacetsAll.filter inU
      let FacetsL := FacetsAll.filter (fun F => ¬ inU F)
      let RidgesU := (Finset.univ : Finset (Finset (SVec (m + 1)))).filter
        (fun R => isChain m R ∧ inU R ∧ isAlt lam true R)
      -- Bipartite incidence double count between FacetsU and RidgesU
      have hdouble :
          (∑ F ∈ FacetsU, (F.filter (fun u => isAlt lam true (F.erase u))).card) =
          (∑ R ∈ RidgesU, (FacetsU.filter (fun F => R ⊆ F)).card) := by
        have h1 : ∀ F ∈ FacetsU, (F.filter (fun u => isAlt lam true (F.erase u))).card =
            (RidgesU.filter (fun R => R ⊆ F)).card := by
          intro F hF
          have hFc : isChain (m + 1) F := (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).2
          have hFU : inU F := (Finset.mem_filter.mp hF).2
          refine Finset.card_bij (fun u _ => F.erase u) ?_ ?_ ?_
          · intro u hu
            rcases Finset.mem_filter.mp hu with ⟨huF, halt⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, ?_, halt⟩,
              Finset.erase_subset u F⟩
            · rw [Finset.card_erase_of_mem huF, hFc.1]; omega
            · intro v hv; exact hFc.2.1 v (Finset.mem_of_mem_erase hv)
            · intro a ha b hb; exact hFc.2.2 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
            · intro v hv; exact hFU v (Finset.mem_of_mem_erase hv)
          · intro u1 h1 u2 h2 heq
            have hu1 := (Finset.mem_filter.mp h1).1
            have hu2 := (Finset.mem_filter.mp h2).1
            by_contra hne
            have : u1 ∈ F.erase u2 := Finset.mem_erase.mpr ⟨hne, hu1⟩
            rw [← heq] at this
            exact (Finset.mem_erase.mp this).1 rfl
          · intro R hR
            rcases Finset.mem_filter.mp hR with ⟨hRU, hRF⟩
            rcases (Finset.mem_filter.mp hRU).2 with ⟨hRc, _, hRalt⟩
            have hsd : (F \ R).card = 1 := by rw [card_sdiff_sub hRF, hFc.1, hRc.1]; omega
            rcases Finset.card_eq_one.mp hsd with ⟨u, hu_eq⟩
            have hu_sd : u ∈ F \ R := hu_eq.symm ▸ Finset.mem_singleton_self u
            rcases Finset.mem_sdiff.mp hu_sd with ⟨huF, huR⟩
            have her : F.erase u = R := by
              ext x; simp only [Finset.mem_erase]
              constructor
              · rintro ⟨hxu, hxF⟩
                by_contra hxR
                have : x ∈ F \ R := Finset.mem_sdiff.mpr ⟨hxF, hxR⟩
                rw [hu_eq, Finset.mem_singleton] at this; exact hxu this
              · intro hxR
                exact ⟨fun h => huR (h ▸ hxR), hRF hxR⟩
            exact ⟨u, Finset.mem_filter.mpr ⟨huF, her.symm ▸ hRalt⟩, her⟩
        rw [Finset.sum_congr rfl h1]
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
      -- LHS mod 2 = (FacetsU pos-alt + FacetsU neg-alt) mod 2
      have hLHS : (∑ F ∈ FacetsU, (F.filter (fun u => isAlt lam true (F.erase u))).card) % 2 =
          ((FacetsU.filter (isAlt lam true)).card + (FacetsU.filter (isAlt lam false)).card) % 2 := by
        rw [Finset.sum_nat_mod]
        have hterm : ∀ F ∈ FacetsU,
            (F.filter (fun u => isAlt lam true (F.erase u))).card % 2 =
              (if isAlt lam true F then 1 else 0) + (if isAlt lam false F then 1 else 0) := by
          intro F hF
          have hFc : isChain (m + 1) F := (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).2
          have hpar := facet_subchain_parity (by omega) lam F hFc.1
            (fun u hu => hnz u (hFc.2.1 u hu))
            (fun u hu v hv => by
              rcases hFc.2.2 u hu v hv with hle | hle
              · exact hnocomp u v (hFc.2.1 u hu) (hFc.2.1 v hv) hle
              · intro heq; exact hnocomp v u (hFc.2.1 v hv) (hFc.2.1 u hu) hle (by omega))
          rw [hpar]
          have hFne : F.Nonempty := Finset.card_pos.mp (by rw [hFc.1]; omega)
          have hdisj := isAlt_disjoint lam F hFne
          by_cases ht : isAlt lam true F
          · have hf : ¬ isAlt lam false F := fun h => hdisj ⟨ht, h⟩
            simp [ht, hf]
          · by_cases hf : isAlt lam false F <;> simp [ht, hf]
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
            ← Finset.card_filter, ← Finset.card_filter]
      -- RHS mod 2 = (RidgesU in E).card mod 2
      have hRHS : (∑ R ∈ RidgesU, (FacetsU.filter (fun F => R ⊆ F)).card) % 2 =
          (RidgesU.filter inE).card % 2 := by
        rw [Finset.sum_nat_mod]
        have hterm : ∀ R ∈ RidgesU,
            (FacetsU.filter (fun F => R ⊆ F)).card % 2 = if inE R then 1 else 0 := by
          intro R hR
          rcases (Finset.mem_filter.mp hR).2 with ⟨hRc, hRU, _⟩
          have hfilt_eq : FacetsU.filter (fun F => R ⊆ F) =
              (Finset.univ : Finset (Finset (SVec (m + 1)))).filter
                (fun F => isChain (m + 1) F ∧ inU F ∧ R ⊆ F) := by
            ext F; simp only [FacetsU, FacetsAll, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
          rw [hfilt_eq, ridge_facets_card hd R hRc hRU]
          split_ifs <;> rfl
        rw [Finset.sum_congr rfl hterm, ← Finset.card_filter]
      -- Equator ridges in RidgesU are in bijection with pos-alt facets of S_m
      have hEq_card : (RidgesU.filter inE).card =
          ((Finset.univ : Finset (Finset (SVec m))).filter (fun F => isChain m F ∧ isAlt lamE true F)).card := by
        refine Finset.card_bij (fun R _ => R.image projV) ?_ ?_ ?_
        · intro R hR
          rcases Finset.mem_filter.mp hR with ⟨hRU, hRE⟩
          rcases (Finset.mem_filter.mp hRU).2 with ⟨hRc, _, hRalt⟩
          have hproj_inj : Set.InjOn projV (R : Set (SVec (m + 1))) := by
            intro u hu v hv heq
            rw [← embedV_projV (hRE u hu), ← embedV_projV (hRE v hv), heq]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · rw [Finset.card_image_of_injOn hproj_inj, hRc.1]
          · intro w hw; rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
            exact embedV_supp_nonempty.mp (by rw [embedV_projV (hRE u hu)]; exact hRc.2.1 u hu)
          · intro w1 hw1 w2 hw2
            rcases Finset.mem_image.mp hw1 with ⟨u1, hu1, rfl⟩
            rcases Finset.mem_image.mp hw2 with ⟨u2, hu2, rfl⟩
            rcases hRc.2.2 u1 hu1 u2 hu2 with hle | hle
            · exact Or.inl (embedV_leV.mp (by rw [embedV_projV (hRE u1 hu1), embedV_projV (hRE u2 hu2)]; exact hle))
            · exact Or.inr (embedV_leV.mp (by rw [embedV_projV (hRE u2 hu2), embedV_projV (hRE u1 hu1)]; exact hle))
          · intro w1 hw1 w2 hw2 hne
            rcases Finset.mem_image.mp hw1 with ⟨u1, hu1, rfl⟩
            rcases Finset.mem_image.mp hw2 with ⟨u2, hu2, rfl⟩
            dsimp only [lamE]
            rw [embedV_projV (hRE u1 hu1), embedV_projV (hRE u2 hu2)]
            exact hRalt.1 u1 hu1 u2 hu2 (fun h => hne (congrArg projV h))
          · intro w hw
            rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
            have heu : lamE (projV u) = lam u := by dsimp only [lamE]; rw [embedV_projV (hRE u hu)]
            rw [heu]
            have hfc : ((R.image projV).filter (fun z => (lamE z).natAbs < (lam u).natAbs)).card =
                (R.filter (fun z => (lam z).natAbs < (lam u).natAbs)).card := by
              have heq : (R.image projV).filter (fun z => (lamE z).natAbs < (lam u).natAbs) =
                  (R.filter (fun z => (lam z).natAbs < (lam u).natAbs)).image projV := by
                ext z; simp only [Finset.mem_filter, Finset.mem_image]
                constructor
                · rintro ⟨⟨x, hx, rfl⟩, hlt⟩
                  exact ⟨x, ⟨hx, by dsimp [lamE] at hlt; rwa [embedV_projV (hRE x hx)] at hlt⟩, rfl⟩
                · rintro ⟨x, ⟨hx, hlt⟩, rfl⟩
                  exact ⟨⟨x, hx, rfl⟩, by dsimp [lamE]; rwa [embedV_projV (hRE x hx)]⟩
              rw [heq, Finset.card_image_of_injOn (hproj_inj.mono (Finset.filter_subset _ _))]
            rw [hfc]
            exact hRalt.2 u hu
        · intro R1 h1 R2 h2 heq
          have hE1 := (Finset.mem_filter.mp h1).2
          have hE2 := (Finset.mem_filter.mp h2).2
          have hback : ∀ R : Finset (SVec (m + 1)), inE R → (R.image projV).image embedV = R := by
            intro R hE
            ext v; simp only [Finset.mem_image]
            constructor
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; rwa [embedV_projV (hE u hu)]
            · intro hv; exact ⟨projV v, ⟨v, hv, rfl⟩, embedV_projV (hE v hv)⟩
          rw [← hback R1 hE1, ← hback R2 hE2, heq]
        · intro F hF
          rcases (Finset.mem_filter.mp hF).2 with ⟨hFc, hFalt⟩
          refine ⟨F.image embedV, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
          · rw [Finset.card_image_of_injective _ embedV_inj, hFc.1]
          · intro v hv; rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
            exact embedV_supp_nonempty.mpr (hFc.2.1 u hu)
          · intro v1 hv1 v2 hv2
            rcases Finset.mem_image.mp hv1 with ⟨u1, hu1, rfl⟩
            rcases Finset.mem_image.mp hv2 with ⟨u2, hu2, rfl⟩
            rw [embedV_leV, embedV_leV]; exact hFc.2.2 u1 hu1 u2 hu2
          · intro v hv; rcases Finset.mem_image.mp hv with ⟨u, _, rfl⟩
            rw [embedV_last]; intro h; cases h
          · intro v1 hv1 v2 hv2 hne
            rcases Finset.mem_image.mp hv1 with ⟨u1, hu1, rfl⟩
            rcases Finset.mem_image.mp hv2 with ⟨u2, hu2, rfl⟩
            exact hFalt.1 u1 hu1 u2 hu2 (fun h => hne (congrArg embedV h))
          · intro v hv
            rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
            have hfc : ((F.image embedV).filter (fun z => (lam z).natAbs < (lam (embedV u)).natAbs)).card =
                (F.filter (fun z => (lamE z).natAbs < (lamE u).natAbs)).card := by
              have heq : (F.image embedV).filter (fun z => (lam z).natAbs < (lam (embedV u)).natAbs) =
                  (F.filter (fun z => (lamE z).natAbs < (lamE u).natAbs)).image embedV := by
                ext z; simp only [Finset.mem_filter, Finset.mem_image]
                constructor
                · rintro ⟨⟨x, hx, rfl⟩, hlt⟩; exact ⟨x, ⟨hx, hlt⟩, rfl⟩
                · rintro ⟨x, ⟨hx, hlt⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hlt⟩
              rw [heq, Finset.card_image_of_injective _ embedV_inj]
            rw [hfc]; exact hFalt.2 u hu
          · intro v hv; rcases Finset.mem_image.mp hv with ⟨u, _, rfl⟩; exact embedV_last u
          · ext w; simp only [Finset.mem_image]
            constructor
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; rwa [projV_embedV]
            · intro hw; exact ⟨embedV w, ⟨w, hw, rfl⟩, projV_embedV w⟩
      -- Antipodal bijection between FacetsU (neg-alt) and FacetsL (pos-alt)
      have hAntipodal : (FacetsU.filter (isAlt lam false)).card = (FacetsL.filter (isAlt lam true)).card := by
        have hneg_inU : ∀ F ∈ FacetsAll, inU (F.image negV) ↔ ¬ inU F := by
          intro F hF
          have hFc : isChain (m + 1) F := (Finset.mem_filter.mp hF).2
          have himg : F.image (fun v => (supp v).card) = Finset.Icc 1 (m + 1) := by
            refine Finset.eq_of_subset_of_card_le (chain_supp_image_subset hFc) ?_
            rw [Nat.card_Icc, Finset.card_image_of_injOn (chain_supp_inj hFc), hFc.1]; omega
          have hmax_mem : m + 1 ∈ F.image (fun v => (supp v).card) := by rw [himg]; simp
          rcases Finset.mem_image.mp hmax_mem with ⟨vmax, hvmaxF, hvmaxC⟩
          have hvmax_top : ∀ v ∈ F, leV v vmax := fun v hv =>
            chain_le_of_card_le hFc hv hvmaxF (by rw [hvmaxC]; exact le_trans (Finset.card_le_univ _) (by simp))
          have hvmax_full : (vmax (Fin.last m)).isSome :=
            mem_supp.mp ((Finset.eq_univ_of_card _ (by rw [hvmaxC, Fintype.card_fin])).symm ▸ Finset.mem_univ _)
          cases hlast : vmax (Fin.last m) with
          | none => rw [hlast] at hvmax_full; cases hvmax_full
          | some b =>
            have hU_iff : inU F ↔ b = true := by
              constructor
              · intro hU; have := hU vmax hvmaxF; rw [hlast] at this; cases b <;> simp_all
              · intro hb v hv hf
                have := hvmax_top v hv (Fin.last m) false hf
                rw [hlast, hb] at this; cases this
            have hnegU_iff : inU (F.image negV) ↔ b = false := by
              constructor
              · intro hU
                have := hU (negV vmax) (Finset.mem_image_of_mem _ hvmaxF)
                simp only [negV, hlast, Option.map_some] at this
                cases b <;> simp_all
              · intro hb w hw hf
                rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
                have hle := leV_negV (hvmax_top v hv)
                have := hle (Fin.last m) false hf
                simp only [negV, hlast, hb, Option.map_some, Bool.not_false] at this
                cases this
            rw [hU_iff, hnegU_iff]; cases b <;> simp
        refine Finset.card_bij (fun F _ => F.image negV) ?_ ?_ ?_
        · intro F hF
          rcases Finset.mem_filter.mp hF with ⟨hFU, hFalt⟩
          rcases Finset.mem_filter.mp hFU with ⟨hFall, hU⟩
          have hFc : isChain (m + 1) F := (Finset.mem_filter.mp hFall).2
          have hnegChain : isChain (m + 1) (F.image negV) := by
            refine ⟨by rw [Finset.card_image_of_injective _ negV_inj, hFc.1], ?_, ?_⟩
            · intro w hw; rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
              rw [supp_negV]; exact hFc.2.1 v hv
            · intro w1 hw1 w2 hw2
              rcases Finset.mem_image.mp hw1 with ⟨v1, hv1, rfl⟩
              rcases Finset.mem_image.mp hw2 with ⟨v2, hv2, rfl⟩
              rcases hFc.2.2 v1 hv1 v2 hv2 with h | h
              · exact Or.inl (leV_negV h)
              · exact Or.inr (leV_negV h)
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnegChain⟩, ?_⟩, ?_⟩
          · exact fun h => (hneg_inU F hFall).mp h hU
          · exact (isAlt_negV_image lam hanti hnz F hFc.2.1).mpr hFalt
        · intro F1 _ F2 _ heq
          have hback : ∀ F : Finset (SVec (m + 1)), (F.image negV).image negV = F := by
            intro F; ext v; simp only [Finset.mem_image]
            constructor
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; rwa [negV_invol]
            · intro hv; exact ⟨negV v, ⟨v, hv, rfl⟩, negV_invol v⟩
          rw [← hback F1, ← hback F2, heq]
        · intro G hG
          rcases Finset.mem_filter.mp hG with ⟨hGL, hGalt⟩
          rcases Finset.mem_filter.mp hGL with ⟨hGall, hnotU⟩
          have hGc : isChain (m + 1) G := (Finset.mem_filter.mp hGall).2
          let F := G.image negV
          have hback : F.image negV = G := by
            ext v; simp only [F, Finset.mem_image]
            constructor
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; rwa [negV_invol]
            · intro hv; exact ⟨negV v, ⟨v, hv, rfl⟩, negV_invol v⟩
          have hFchain : isChain (m + 1) F := by
            refine ⟨by rw [Finset.card_image_of_injective _ negV_inj, hGc.1], ?_, ?_⟩
            · intro w hw; rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
              rw [supp_negV]; exact hGc.2.1 v hv
            · intro w1 hw1 w2 hw2
              rcases Finset.mem_image.mp hw1 with ⟨v1, hv1, rfl⟩
              rcases Finset.mem_image.mp hw2 with ⟨v2, hv2, rfl⟩
              rcases hGc.2.2 v1 hv1 v2 hv2 with h | h
              · exact Or.inl (leV_negV h)
              · exact Or.inr (leV_negV h)
          have hFU : inU F := (hneg_inU G hGall).mpr hnotU
          have hFalt : isAlt lam false F := by
            rw [← isAlt_negV_image lam hanti hnz F hFchain.2.1, hback]; exact hGalt
          exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFchain⟩, hFU⟩, hFalt⟩, hback⟩
      -- Total pos-alt facets = FacetsU pos-alt + FacetsL pos-alt
      have hTot : ((Finset.univ : Finset (Finset (SVec (m + 1)))).filter
          (fun F => isChain (m + 1) F ∧ isAlt lam true F)).card =
          (FacetsU.filter (isAlt lam true)).card + (FacetsL.filter (isAlt lam true)).card := by
        have hdisj : Disjoint (FacetsU.filter (isAlt lam true)) (FacetsL.filter (isAlt lam true)) := by
          refine Finset.disjoint_left.mpr fun F h1 h2 => ?_
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
        rw [← Finset.card_union_of_disjoint hdisj]
        congr 1; ext F
        simp only [FacetsU, FacetsL, FacetsAll, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      rw [hTot, ← hAntipodal, ← hLHS, hdouble, hRHS, hEq_card]
      exact hih

lemma octahedral_tucker (d m : ℕ) (hd : 1 ≤ d) (lam : SVec d → ℤ)
    (hpos : ∀ v, (supp v).Nonempty → 1 ≤ (lam v).natAbs)
    (hbound : ∀ v, (supp v).Nonempty → (lam v).natAbs ≤ m)
    (hanti : ∀ v, lam (negV v) = - lam v)
    (hnocomp : ∀ u v, (supp u).Nonempty → (supp v).Nonempty → leV u v → lam u ≠ - lam v) :
    d ≤ m := by
  have hodd := ky_fan_odd d hd lam (fun v hv => by have := hpos v hv; omega) hanti hnocomp
  have hne : ((Finset.univ : Finset (Finset (SVec d))).filter (fun F => isChain d F ∧ isAlt lam true F)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hne with ⟨F, hF⟩
  rcases (Finset.mem_filter.mp hF).2 with ⟨hFc, hFalt⟩
  have hinj : Set.InjOn (fun v => (lam v).natAbs) (F : Set (SVec d)) := by
    intro u hu v hv heq
    by_contra hne'
    exact hFalt.1 u hu v hv hne' heq
  have hsub : F.image (fun v => (lam v).natAbs) ⊆ Finset.Icc 1 m := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨v, hv, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hpos v (hFc.2.1 v hv), hbound v (hFc.2.1 v hv)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, hFc.1, Nat.card_Icc] at hle
  omega

end KyFanTucker

section MainProof

def runsOf {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) : ℕ → Finset (Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)

lemma runsOf_mono_x {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) :
    ∀ k {x y : Finset (Fin n)}, x ⊆ y → runsOf g k x → runsOf g k y
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hxy, ⟨u, v, j, hu, huv, hvx, hgu, hgv⟩ =>
    ⟨u, v, j, hu, huv, hvx.trans hxy, hgu, hgv⟩

lemma runsOf_anti_k {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) {k : ℕ} {x : Finset (Fin n)}
    (h : runsOf g (k + 1) x) : runsOf g k x := by
  rcases h with ⟨u, v, j, hu, huv, hvx, _, _⟩
  exact runsOf_mono_x g k (huv.trans hvx) hu

lemma runsOf_le_k {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) {a b : ℕ} {x : Finset (Fin n)}
    (hab : a ≤ b) (hb : runsOf g b x) : runsOf g a x := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact hb
  | succ b ih =>
    by_cases h : a = b + 1
    · subst h; exact hb
    · exact ih (by omega) (runsOf_anti_k g hb)

lemma not_runsOf_empty {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) :
    ¬ runsOf g 1 ∅ := by
  rintro ⟨u, v, j, _, huv, hv0, hgu, hgv⟩
  have hv : v = ∅ := Finset.subset_empty.mp hv0
  have hu : u = ∅ := Finset.subset_empty.mp (huv.trans hv0)
  subst hu; subst hv; rw [hgu] at hgv; cases hgv

noncomputable def rankOf {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) : ℕ → Finset (Fin n) → ℕ
  | 0, _ => 0
  | h + 1, x => if runsOf g (h + 1) x then h + 1 else rankOf g h x

lemma rankOf_le {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ) (x : Finset (Fin n)) :
    rankOf g h x ≤ h := by
  induction h with
  | zero => exact le_refl 0
  | succ h ih => dsimp only [rankOf]; split_ifs <;> omega

lemma runsOf_rankOf {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ) (x : Finset (Fin n)) :
    runsOf g (rankOf g h x) x := by
  induction h with
  | zero => trivial
  | succ h ih => dsimp only [rankOf]; split_ifs with h1; exact h1; exact ih

lemma le_rankOf_of_runsOf {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h k : ℕ) (x : Finset (Fin n))
    (hk : k ≤ h) (hr : runsOf g k x) : k ≤ rankOf g h x := by
  induction h with
  | zero => omega
  | succ h ih =>
    dsimp only [rankOf]
    split_ifs with h1
    · exact hk
    · have hk' : k ≤ h := by
        by_contra hgt
        have heq : k = h + 1 := by omega
        subst heq; exact h1 hr
      exact ih hk'

lemma runsOf_iff_le_rankOf {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hbound : ¬ runsOf g (h + 1) Finset.univ) (k : ℕ) (x : Finset (Fin n)) :
    runsOf g k x ↔ k ≤ rankOf g h x := by
  constructor
  · intro hr
    have hk : k ≤ h := by
      by_contra hgt
      exact hbound (runsOf_mono_x g (h + 1) (Finset.subset_univ x) (runsOf_le_k g (by omega) hr))
    exact le_rankOf_of_runsOf g h k x hk hr
  · intro hk
    exact runsOf_le_k g hk (runsOf_rankOf g h x)

lemma rankOf_mono {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hbound : ¬ runsOf g (h + 1) Finset.univ) {x y : Finset (Fin n)} (hxy : x ⊆ y) :
    rankOf g h x ≤ rankOf g h y :=
  (runsOf_iff_le_rankOf g h hbound (rankOf g h x) y).mp
    (runsOf_mono_x g (rankOf g h x) hxy (runsOf_rankOf g h x))

lemma rankOf_lt_of_fall {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hbound : ¬ runsOf g (h + 1) Finset.univ) {x y : Finset (Fin n)} {j : Fin n}
    (hxy : x ⊆ y) (hgx : g x j = true) (hgy : g y j = false) :
    rankOf g h x < rankOf g h y := by
  have hr : runsOf g (rankOf g h x + 1) y :=
    ⟨x, y, j, runsOf_rankOf g h x, hxy, Finset.Subset.refl y, hgx, hgy⟩
  have hle := (runsOf_iff_le_rankOf g h hbound (rankOf g h x + 1) y).mp hr
  omega

lemma rankOf_empty {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hbound : ¬ runsOf g (h + 1) Finset.univ) : rankOf g h ∅ = 0 := by
  by_contra hne
  have h1 : runsOf g 1 ∅ := (runsOf_iff_le_rankOf g h hbound 1 ∅).mpr (by omega)
  exact not_runsOf_empty g h1

lemma freeze_of_rank_eq {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hbound : ¬ runsOf g (h + 1) Finset.univ)
    (hdec : ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true)
    {x y : Finset (Fin n)} (hxy : x ⊆ y) (hr : rankOf g h x = rankOf g h y) :
    g x = g y := by
  funext j
  cases hgx : g x j <;> cases hgy : g y j
  · rfl
  · have := hdec x y hxy j hgy; rw [hgx] at this; cases this
  · have hlt := rankOf_lt_of_fall g h hbound hxy hgx hgy; omega
  · rfl

lemma exists_max_pair {d : ℕ} (P : Finset (Fin d) × Finset (Fin d) → Prop)
    (h0 : P (∅, ∅)) :
    ∃ a b : Finset (Fin d), P (a, b) ∧
      ∀ a' b' : Finset (Fin d), P (a', b') → a'.card + b'.card ≤ a.card + b.card := by
  let S : Finset (Finset (Fin d) × Finset (Fin d)) := Finset.univ.filter P
  have hSne : S.Nonempty := ⟨(∅, ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
  rcases Finset.exists_max_image S (fun p => p.1.card + p.2.card) hSne with ⟨⟨a, b⟩, hab, hmax⟩
  exact ⟨a, b, (Finset.mem_filter.mp hab).2, fun a' b' h' =>
    hmax (a', b') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)⟩

theorem main_aux
    (d n : ℕ) (E : Fin n → Finset (Fin d)) (hE : ∀ i, (E i).Nonempty)
    (g : Finset (Fin n) → Fin n → Bool) (h : ℕ)
    (hpos : ∀ x j, (∀ i ∈ x, Disjoint (E i) (E j)) → g x j = true)
    (hneg : ∀ x j, j ∈ x → g x j = false)
    (hdec : ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true)
    (hbound : ¬ runsOf g (h + 1) Finset.univ) :
    ∃ a b : Finset (Fin d), Disjoint a b ∧
      (∀ i, ¬ E i ⊆ a ∧ ¬ E i ⊆ b) ∧
      d ≤ a.card + b.card + max h (2 * (h - 1)) := by
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨∅, ∅, Finset.disjoint_empty_left ∅, ?_, Nat.zero_le _⟩
    intro i
    have hne := hE i
    exact ⟨fun hsub => Finset.not_nonempty_empty (hne.mono hsub),
      fun hsub => Finset.not_nonempty_empty (hne.mono hsub)⟩
  have hd : 1 ≤ d := by omega
  let P0 : Finset (Fin d) × Finset (Fin d) → Prop :=
    fun p => Disjoint p.1 p.2 ∧ ∀ i, ¬ E i ⊆ p.1 ∧ ¬ E i ⊆ p.2
  have hP0_empty : P0 (∅, ∅) := by
    refine ⟨Finset.disjoint_empty_left ∅, fun i => ?_⟩
    have hne := hE i
    exact ⟨fun hsub => Finset.not_nonempty_empty (hne.mono hsub),
      fun hsub => Finset.not_nonempty_empty (hne.mono hsub)⟩
  rcases exists_max_pair P0 hP0_empty with ⟨a0, b0, ⟨hdisj0, hfree0⟩, hmax0⟩
  set t := a0.card + b0.card
  refine ⟨a0, b0, hdisj0, hfree0, ?_⟩
  let posSet : SVec d → Finset (Fin d) := fun v => Finset.univ.filter (fun i => v i = some true)
  let negSet : SVec d → Finset (Fin d) := fun v => Finset.univ.filter (fun i => v i = some false)
  have hdisj_pn : ∀ v : SVec d, Disjoint (posSet v) (negSet v) := by
    intro v; refine Finset.disjoint_left.mpr fun i h1 h2 => ?_
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rw [e1] at e2; cases e2
  have hunion_pn : ∀ v : SVec d, posSet v ∪ negSet v = supp v := by
    intro v; ext i; simp only [posSet, negSet, mem_supp, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases v i with
    | none => simp
    | some b => cases b <;> simp
  have hcard_pn : ∀ v : SVec d, (posSet v).card + (negSet v).card = (supp v).card := by
    intro v; rw [← Finset.card_union_of_disjoint (hdisj_pn v), hunion_pn]
  have hneg_pos : ∀ v : SVec d, posSet (negV v) = negSet v := by
    intro v; ext i; simp only [posSet, negSet, negV, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hv : v i with
    | none => simp [hv]
    | some b => cases b <;> simp [hv]
  have hneg_neg : ∀ v : SVec d, negSet (negV v) = posSet v := by
    intro v; ext i; simp only [posSet, negSet, negV, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hv : v i with
    | none => simp [hv]
    | some b => cases b <;> simp [hv]
  have hle_pos : ∀ {u v : SVec d}, leV u v → posSet u ⊆ posSet v := by
    intro u v hle i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hle i true (Finset.mem_filter.mp hi).2⟩
  have hle_neg : ∀ {u v : SVec d}, leV u v → negSet u ⊆ negSet v := by
    intro u v hle i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hle i false (Finset.mem_filter.mp hi).2⟩
  let keys : Finset (Fin d) → Finset (Fin n) := fun s => Finset.univ.filter (fun i => E i ⊆ s)
  have hkeys_mono : ∀ {s1 s2 : Finset (Fin d)}, s1 ⊆ s2 → keys s1 ⊆ keys s2 := by
    intro s1 s2 hsub i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.trans hsub⟩
  have hkeys_disj_true : ∀ {s1 s2 : Finset (Fin d)}, Disjoint s1 s2 →
      ∀ j ∈ keys s2, g (keys s1) j = true := by
    intro s1 s2 hdisj j hj
    refine hpos (keys s1) j fun i hi => ?_
    exact hdisj.mono (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hkeys_g_ne : ∀ v : SVec d, (keys (posSet v)).Nonempty ∨ (keys (negSet v)).Nonempty →
      g (keys (posSet v)) ≠ g (keys (negSet v)) := by
    intro v hne heq
    rcases hne with ⟨i, hi⟩ | ⟨j, hj⟩
    · have h1 := hneg (keys (posSet v)) i hi
      have h2 := hkeys_disj_true (hdisj_pn v).symm i hi
      rw [heq] at h1; rw [h1] at h2; cases h2
    · have h1 := hkeys_disj_true (hdisj_pn v) j hj
      have h2 := hneg (keys (negSet v)) j hj
      rw [heq] at h1; rw [h1] at h2; cases h2
  have hrank_pos_of_ne : ∀ {s : Finset (Fin d)}, (keys s).Nonempty → 1 ≤ rankOf g h (keys s) := by
    intro s ⟨i, hi⟩
    have hlt := rankOf_lt_of_fall g h hbound (Finset.empty_subset (keys s))
      (hpos ∅ i (by simp)) (hneg (keys s) i hi)
    omega
  have hrank_lt_of_both : ∀ v : SVec d, (keys (posSet v)).Nonempty → (keys (negSet v)).Nonempty →
      rankOf g h (keys (posSet v)) < h ∧ rankOf g h (keys (negSet v)) < h := by
    intro v ⟨i, hi⟩ ⟨j, hj⟩
    have h1 : rankOf g h (keys (posSet v)) < rankOf g h (keys (posSet v) ∪ keys (negSet v)) :=
      rankOf_lt_of_fall g h hbound Finset.subset_union_left
        (hkeys_disj_true (hdisj_pn v) j hj)
        (hneg _ j (Finset.mem_union_right _ hj))
    have h2 : rankOf g h (keys (negSet v)) < rankOf g h (keys (posSet v) ∪ keys (negSet v)) :=
      rankOf_lt_of_fall g h hbound Finset.subset_union_right
        (hkeys_disj_true (hdisj_pn v).symm i hi)
        (hneg _ i (Finset.mem_union_left _ hi))
    have hle := rankOf_le g h (keys (posSet v) ∪ keys (negSet v))
    omega
  let ord : (Fin n → Bool) ≃ Fin (Fintype.card (Fin n → Bool)) := Fintype.equivFin (Fin n → Bool)
  let lam : SVec d → ℤ := fun v =>
    if hfree : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅ then
      if hne : (supp v).Nonempty then
        (if (supp v).min' hne ∈ posSet v then (1 : ℤ) else -1) * ((supp v).card : ℤ)
      else 0
    else
      (if (ord (g (keys (posSet v)))).val < (ord (g (keys (negSet v)))).val then (1 : ℤ) else -1) *
        ((t + rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) : ℕ) : ℤ)
  have hlam_pos : ∀ v, (supp v).Nonempty → 1 ≤ (lam v).natAbs := by
    intro v hv
    dsimp only [lam]
    by_cases hfree : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅
    · rw [dif_pos hfree, dif_pos hv, natAbs_sign_mul]
      exact Finset.card_pos.mpr hv
    · rw [dif_neg hfree, natAbs_sign_mul]
      have hne_k : (keys (posSet v)).Nonempty ∨ (keys (negSet v)).Nonempty := by
        by_contra hall
        exact hfree ⟨Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).1,
          Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).2⟩
      have hr : 1 ≤ rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) := by
        rcases hne_k with hp | hn
        · have := hrank_pos_of_ne hp; omega
        · have := hrank_pos_of_ne hn; omega
      omega
  have hlam_bound : ∀ v, (supp v).Nonempty → (lam v).natAbs ≤ t + max h (2 * (h - 1)) := by
    intro v hv
    dsimp only [lam]
    by_cases hfree : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅
    · rw [dif_pos hfree, dif_pos hv, natAbs_sign_mul]
      have hP : P0 (posSet v, negSet v) := by
        refine ⟨hdisj_pn v, fun i => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
        · have : i ∈ keys (posSet v) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
          rw [hfree.1] at this; cases this
        · have : i ∈ keys (negSet v) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2⟩
          rw [hfree.2] at this; cases this
      have hle := hmax0 (posSet v) (negSet v) hP
      rw [hcard_pn v] at hle
      omega
    · rw [dif_neg hfree, natAbs_sign_mul]
      have hrsum : rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) ≤ max h (2 * (h - 1)) := by
        by_cases hp : (keys (posSet v)).Nonempty
        · by_cases hn : (keys (negSet v)).Nonempty
          · have hlt := hrank_lt_of_both v hp hn
            have : rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) ≤ 2 * (h - 1) := by omega
            exact le_trans this (le_max_right _ _)
          · have hne0 : keys (negSet v) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
            rw [hne0, rankOf_empty g h hbound, add_zero]
            exact le_trans (rankOf_le g h _) (le_max_left _ _)
        · have hpe0 : keys (posSet v) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
          rw [hpe0, rankOf_empty g h hbound, zero_add]
          exact le_trans (rankOf_le g h _) (le_max_left _ _)
      omega
  have hlam_anti : ∀ v, lam (negV v) = - lam v := by
    intro v
    dsimp only [lam]
    simp only [hneg_pos, hneg_neg, supp_negV]
    by_cases hfree : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅
    · have hfree' : keys (negSet v) = ∅ ∧ keys (posSet v) = ∅ := ⟨hfree.2, hfree.1⟩
      rw [dif_pos hfree', dif_pos hfree]
      by_cases hne : (supp v).Nonempty
      · rw [dif_pos hne, dif_pos hne]
        have hmin_mem : (supp v).min' hne ∈ posSet v ∪ negSet v := by
          rw [hunion_pn]; exact Finset.min'_mem _ hne
        by_cases hm : (supp v).min' hne ∈ posSet v
        · have hm2 : (supp v).min' hne ∉ negSet v := Finset.disjoint_left.mp (hdisj_pn v) hm
          rw [if_neg hm2, if_pos hm]; ring
        · have hm2 : (supp v).min' hne ∈ negSet v := (Finset.mem_union.mp hmin_mem).resolve_left hm
          rw [if_pos hm2, if_neg hm]; ring
      · rw [dif_neg hne, dif_neg hne]; simp
    · have hfree' : ¬ (keys (negSet v) = ∅ ∧ keys (posSet v) = ∅) := fun h => hfree ⟨h.2, h.1⟩
      rw [dif_neg hfree', dif_neg hfree]
      have hne_k : (keys (posSet v)).Nonempty ∨ (keys (negSet v)).Nonempty := by
        by_contra hall
        exact hfree ⟨Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).1,
          Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).2⟩
      have hgne := hkeys_g_ne v hne_k
      have hord_ne : (ord (g (keys (posSet v)))).val ≠ (ord (g (keys (negSet v)))).val :=
        fun heq => hgne (ord.injective (Fin.ext heq))
      have hsum_eq : t + rankOf g h (keys (negSet v)) + rankOf g h (keys (posSet v)) =
          t + rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) := by omega
      rw [hsum_eq]
      split_ifs <;> omega
  have hlam_nocomp : ∀ u v, (supp u).Nonempty → (supp v).Nonempty → leV u v → lam u ≠ - lam v := by
    intro u v hu hv hle heq
    have habs : (lam u).natAbs = (lam v).natAbs := by omega
    have hfree_bound : ∀ w : SVec d, keys (posSet w) = ∅ ∧ keys (negSet w) = ∅ →
        (supp w).Nonempty → (lam w).natAbs ≤ t := by
      intro w hfw hne
      dsimp only [lam]
      rw [dif_pos hfw, dif_pos hne, natAbs_sign_mul]
      have hP : P0 (posSet w, negSet w) := by
        refine ⟨hdisj_pn w, fun i => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
        · have : i ∈ keys (posSet w) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
          rw [hfw.1] at this; cases this
        · have : i ∈ keys (negSet w) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2⟩
          rw [hfw.2] at this; cases this
      have hmax := hmax0 (posSet w) (negSet w) hP
      rw [hcard_pn w] at hmax
      exact hmax
    have hocc_bound : ∀ w : SVec d, ¬ (keys (posSet w) = ∅ ∧ keys (negSet w) = ∅) →
        t + 1 ≤ (lam w).natAbs := by
      intro w hfw
      dsimp only [lam]
      rw [dif_neg hfw, natAbs_sign_mul]
      have hne_k : (keys (posSet w)).Nonempty ∨ (keys (negSet w)).Nonempty := by
        by_contra hall
        exact hfw ⟨Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).1,
          Finset.not_nonempty_iff_eq_empty.mp (not_or.mp hall).2⟩
      have hr : 1 ≤ rankOf g h (keys (posSet w)) + rankOf g h (keys (negSet w)) := by
        rcases hne_k with hp | hn
        · have := hrank_pos_of_ne hp; omega
        · have := hrank_pos_of_ne hn; omega
      omega
    by_cases hfu : keys (posSet u) = ∅ ∧ keys (negSet u) = ∅
    · by_cases hfv : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅
      · have hcu : (lam u).natAbs = (supp u).card := by
          dsimp only [lam]; rw [dif_pos hfu, dif_pos hu, natAbs_sign_mul]
        have hcv : (lam v).natAbs = (supp v).card := by
          dsimp only [lam]; rw [dif_pos hfv, dif_pos hv, natAbs_sign_mul]
        have huv : u = v := eq_of_leV_card_eq hle (by omega)
        subst huv
        have hposu := hlam_pos u hu
        omega
      · have h1 := hfree_bound u hfu hu
        have h2 := hocc_bound v hfv
        omega
    · by_cases hfv : keys (posSet v) = ∅ ∧ keys (negSet v) = ∅
      · have h1 := hocc_bound u hfu
        have h2 := hfree_bound v hfv hv
        omega
      · have hcu : (lam u).natAbs = t + rankOf g h (keys (posSet u)) + rankOf g h (keys (negSet u)) := by
          dsimp only [lam]; rw [dif_neg hfu, natAbs_sign_mul]
        have hcv : (lam v).natAbs = t + rankOf g h (keys (posSet v)) + rankOf g h (keys (negSet v)) := by
          dsimp only [lam]; rw [dif_neg hfv, natAbs_sign_mul]
        have hr1 : rankOf g h (keys (posSet u)) ≤ rankOf g h (keys (posSet v)) :=
          rankOf_mono g h hbound (hkeys_mono (hle_pos hle))
        have hr2 : rankOf g h (keys (negSet u)) ≤ rankOf g h (keys (negSet v)) :=
          rankOf_mono g h hbound (hkeys_mono (hle_neg hle))
        have hr1_eq : rankOf g h (keys (posSet u)) = rankOf g h (keys (posSet v)) := by omega
        have hr2_eq : rankOf g h (keys (negSet u)) = rankOf g h (keys (negSet v)) := by omega
        have hg1 : g (keys (posSet u)) = g (keys (posSet v)) :=
          freeze_of_rank_eq g h hbound hdec (hkeys_mono (hle_pos hle)) hr1_eq
        have hg2 : g (keys (negSet u)) = g (keys (negSet v)) :=
          freeze_of_rank_eq g h hbound hdec (hkeys_mono (hle_neg hle)) hr2_eq
        have hlu_eq : lam u = lam v := by
          dsimp only [lam]
          rw [dif_neg hfu, dif_neg hfv, hg1, hg2, hr1_eq, hr2_eq]
        have hposu := hlam_pos u hu
        omega
  exact octahedral_tucker d (t + max h (2 * (h - 1))) hd lam hlam_pos hlam_bound hlam_anti hlam_nocomp

end MainProof

end PEqualNP.Outside.L_lib_1265_aux

theorem PEqualNP.Outside.L_lib_1265 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (d n : Nat) (E : Fin n → Finset (Fin d)), (∀ i, (E i).Nonempty) →
  ∀ (g : Finset (Fin n) → Fin n → Bool) (h : Nat),
  (∀ x j, (∀ i ∈ x, Disjoint (E i) (E j)) → g x j = true) →
  (∀ x j, j ∈ x → g x j = false) →
  (∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true) →
  let runs := Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)
  ¬ runs (h+1) Finset.univ →
  ∃ a b : Finset (Fin d), Disjoint a b ∧
    (∀ i, ¬ E i ⊆ a ∧ ¬ E i ⊆ b) ∧
    d ≤ a.card + b.card + max h (2 * (h-1)) :=
  fun d n E hE g h hpos hneg hdec hbound =>
    PEqualNP.Outside.L_lib_1265_aux.main_aux d n E hE g h hpos hneg hdec hbound
