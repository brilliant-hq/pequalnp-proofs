import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49527_aux

theorem tele_ge : ∀ (l : ℕ) (a : Fin (l+1) → ℕ),
    a 0 - a (Fin.last l) ≤ ∑ i : Fin l, (a i.castSucc - a i.succ)
  | 0, a => by simp
  | l+1, a => by
    rw [Fin.sum_univ_castSucc]
    have ih := tele_ge l (fun i => a i.castSucc)
    have hsl : (Fin.last l).succ = Fin.last (l+1) := Fin.ext (by simp)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero, hsl] at ih ⊢
    omega

theorem tele_le : ∀ (l : ℕ) (a : Fin (l+1) → ℕ), (∀ i : Fin l, a i.castSucc ≤ a i.succ) →
    ∑ i : Fin l, (a i.succ - a i.castSucc) ≤ a (Fin.last l)
  | 0, a, _ => by simp
  | l+1, a, ha => by
    rw [Fin.sum_univ_castSucc]
    have ih := tele_le l (fun i => a i.castSucc)
      (fun i => by have h3 := ha i.castSucc; rw [Fin.succ_castSucc] at h3; exact h3)
    have h2 := ha (Fin.last l)
    have hsl : (Fin.last l).succ = Fin.last (l+1) := Fin.ext (by simp)
    simp only [Fin.succ_castSucc, hsl] at ih h2 ⊢
    omega

theorem extend {α : Type*} (R : α → α → Prop) (w : α → α → ℕ) (l : ℕ)
    (p : Fin (l+1) → α) (hinj : Function.Injective p)
    (hR : ∀ i : Fin l, R (p i.castSucc) (p i.succ)) (v : α) (hv : R (p (Fin.last l)) v) :
    ∃ (l' : ℕ) (q : Fin (l'+1) → α), Function.Injective q ∧ q 0 = p 0 ∧
      q (Fin.last l') = v ∧ (∀ i : Fin l', R (q i.castSucc) (q i.succ)) ∧
      ∑ i : Fin l', w (q i.castSucc) (q i.succ) ≤
        ∑ i : Fin l, w (p i.castSucc) (p i.succ) + w (p (Fin.last l)) v := by
  by_cases hmem : ∃ i, p i = v
  · obtain ⟨i, rfl⟩ := hmem
    have hi : (i : ℕ) + 1 ≤ l + 1 := i.isLt
    refine ⟨i.val, fun k => p (Fin.castLE hi k), ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact Fin.castLE_injective _ (hinj hab)
    · exact congrArg p (Fin.ext (by simp))
    · exact congrArg p (Fin.ext (by simp))
    · intro k
      have hk : (k : ℕ) < l := by omega
      exact hR ⟨k, hk⟩
    · let T : ℕ → ℕ := fun k => if hk : k < l then
        w (p ⟨k, by omega⟩) (p ⟨k+1, by omega⟩) else 0
      have e1 : ∑ k : Fin i.val, w (p (Fin.castLE hi k.castSucc)) (p (Fin.castLE hi k.succ))
          = ∑ k : Fin i.val, T k :=
        Finset.sum_congr rfl (fun k _ => by
          simp only [T]; rw [dif_pos (show (k : ℕ) < l by omega)]; all_goals rfl)
      have e2 : ∑ k : Fin l, w (p k.castSucc) (p k.succ) = ∑ k : Fin l, T k :=
        Finset.sum_congr rfl (fun k _ => by
          simp only [T]; rw [dif_pos k.isLt]; all_goals rfl)
      rw [e1, e2, Fin.sum_univ_eq_sum_range T, Fin.sum_univ_eq_sum_range T]
      have : ∑ k ∈ Finset.range i.val, T k ≤ ∑ k ∈ Finset.range l, T k :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      omega
  · push_neg at hmem
    refine ⟨l+1, Fin.snoc p v, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      induction a using Fin.lastCases <;> induction b using Fin.lastCases
      · rfl
      · rename_i b
        simp at hab
        exact absurd hab.symm (hmem b)
      · rename_i a
        simp at hab
        exact absurd hab (hmem a)
      · rename_i a b
        simp at hab
        rw [hinj hab]
    · have : (0 : Fin (l+2)) = Fin.castSucc 0 := by simp
      rw [this, Fin.snoc_castSucc]
    · simp
    · intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]; exact hv
      | cast k => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hR k
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
      exact le_refl _

end PEqualNP.Outside.L_meta_49527_aux

open PEqualNP.Outside.L_meta_49527_aux in
theorem PEqualNP.Outside.L_meta_49527 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n D : Nat) (g : Fin n → Fin n → Prop),
  Symmetric g → (∀ i, ¬g i i) →
  let X := Finset (Fin n)
  let C := fun (x : X) => (Finset.univ : X).filter (fun j => ∀ i ∈ x, g i j)
  let cl := fun (x : X) => C (C x)
  let F := {x : X // cl x = x}
  let M := ((Finset.univ : Finset X).image C).card
  ∀ B : X → Nat,
    (∃ f : X → Fin n → Nat,
      (∀ x j, f x j ≤ D) ∧ (∀ x j, j ∈ C x → f x j = D) ∧
      (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
      ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → Fin n),
        (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
        Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
          ≤ B (cl (p (Fin.last l)))) ↔
    ∃ h : F → Nat,
      (∀ u, u.val = ∅ → h u = 0) ∧ (∀ u, h u ≤ B u.val) ∧
      (∀ u v, u.val ⊆ v.val → h u ≤ h v) ∧
      ∀ (j : Fin n) (l : Nat) (p : Fin (l+1) → F),
        l < M → Function.Injective p →
        (p 0).val = C {j} → (p (Fin.last l)).val = cl {j} →
        (∀ i : Fin l, (p i.castSucc).val ⊆ (p i.succ).val ∨ (p i.succ).val ⊆ (p i.castSucc).val) →
        D ≤ Finset.univ.sum (fun i : Fin l => h (p i.succ) - h (p i.castSucc)) := by
  intro n D g hsym hirr X C cl F M B
  classical
  have memC : ∀ (x : X) j, j ∈ C x ↔ ∀ i ∈ x, g i j := by
    intro x j; simp [C]
  have Canti : ∀ x y : X, x ⊆ y → C y ⊆ C x := by
    intro x y hxy j; rw [memC, memC]; exact fun h i hi => h i (hxy hi)
  have hext : ∀ x : X, x ⊆ C (C x) := by
    intro x i hi; rw [memC]; intro k hk; rw [memC] at hk; exact hsym (hk i hi)
  have trip : ∀ x : X, C (C (C x)) = C x := fun x =>
    Finset.Subset.antisymm (Canti _ _ (hext x)) (hext (C x))
  have clcl : ∀ x : X, cl (cl x) = cl x := by
    intro x; show C (C (C (C x))) = C (C x); rw [trip]
  have clmono : ∀ x y : X, x ⊆ y → cl x ⊆ cl y := fun x y h => Canti _ _ (Canti _ _ h)
  have jself : ∀ j, j ∈ cl {j} := fun j => hext {j} (Finset.mem_singleton_self j)
  have cardF : ∀ l (p : Fin (l+1) → F), Function.Injective p → l < M := by
    intro l p hp
    have h1 : Fintype.card F ≤ M := by
      have := Fintype.card_le_of_injective
        (fun u : F => (⟨u.val, Finset.mem_image.2 ⟨C u.val, Finset.mem_univ _, u.prop⟩⟩ :
          ((Finset.univ : Finset X).image C)))
        (by intro a b hab; apply Subtype.ext; have := congrArg Subtype.val hab; exact this)
      rw [Fintype.card_coe] at this
      convert this
    have h2 := Fintype.card_le_of_injective p hp
    simp at h2
    omega
  constructor
  · rintro ⟨f, hfD, hfC, hfx, hfanti, hch⟩
    let S : X → Set ℕ := fun y => {s | ∃ (l : ℕ) (p : Fin (l+1) → X) (a : Fin l → Fin n),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) ∧ p (Fin.last l) = y ∧
      s = ∑ i : Fin l, (f (p i.castSucc) (a i) - f (p i.succ) (a i))}
    have hSbdd : ∀ y, ∀ s ∈ S y, s ≤ B (cl y) := by
      rintro y s ⟨l, p, a, hp, rfl, rfl⟩
      exact hch l p a hp
    have hSne : ∀ y, 0 ∈ S y := fun y =>
      ⟨0, fun _ => y, Fin.elim0, fun i => Fin.elim0 i, rfl, by simp⟩
    have hSext : ∀ x y s j, s ∈ S x → x ⊆ y → s + (f x j - f y j) ∈ S y := by
      rintro x y s j ⟨l, p, a, hp, hl, rfl⟩ hxy
      refine ⟨l+1, Fin.snoc (α := fun _ => X) p y, Fin.snoc (α := fun _ => Fin n) a j,
        ?_, by simp, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hl]; exact hxy
        | cast k => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hp k
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, hl]
    let h : F → ℕ := fun u => sSup (S u.val)
    have hbdd : ∀ y, BddAbove (S y) := fun y => ⟨B (cl y), fun s hs => hSbdd y s hs⟩
    have hmem : ∀ u : F, h u ∈ S u.val := fun u => Nat.sSup_mem ⟨0, hSne _⟩ (hbdd _)
    have hle : ∀ (u : F) s, s ∈ S u.val → s ≤ h u := fun u s hs => le_csSup (hbdd _) hs
    have hgain : ∀ (u v : F) j, u.val ⊆ v.val → h u + (f u.val j - f v.val j) ≤ h v :=
      fun u v j huv => hle v _ (hSext _ _ _ j (hmem u) huv)
    refine ⟨h, ?_, ?_, ?_, ?_⟩
    · intro u hu
      have hm := hmem u
      rw [hu] at hm
      obtain ⟨l, p, a, hp, hl, he⟩ := hm
      rw [he]
      have hmono : Monotone p := Fin.monotone_iff_le_succ.2 hp
      have hall : ∀ i, p i = ∅ := fun i =>
        Finset.subset_empty.1 (hl ▸ hmono (Fin.le_last i))
      apply Finset.sum_eq_zero
      intro i _
      rw [hall, hall]; simp
    · intro u
      have := hSbdd _ _ (hmem u)
      rwa [u.prop] at this
    · intro u v huv
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨j⟩⟩
      · have : u = v := Subtype.ext (by
          rw [Finset.eq_empty_of_isEmpty u.val, Finset.eq_empty_of_isEmpty v.val])
        rw [this]
      · have := hgain u v j huv
        omega
    · intro j l p hl hinj hp0 hpl hstep
      have key : ∀ i : Fin l, f (p i.castSucc).val j - f (p i.succ).val j ≤
          h (p i.succ) - h (p i.castSucc) := by
        intro i
        rcases hstep i with hs | hs
        · have := hgain _ _ j hs
          omega
        · have := hfanti _ _ hs j
          omega
      have t := tele_ge l (fun i => f (p i).val j)
      rw [hp0, hpl, hfC _ _ (jself j), hfx _ _ (jself j)] at t
      calc D = D - 0 := by simp
        _ ≤ _ := t
        _ ≤ _ := Finset.sum_le_sum (fun i _ => key i)
  · rintro ⟨h, h0, hB, hmono, hpath⟩
    let sj : Fin n → F := fun j => ⟨C {j}, trip _⟩
    let clF : X → F := fun x => ⟨cl x, clcl x⟩
    let P : Fin n → F → Set ℕ := fun j u => {c | ∃ (l : ℕ) (p : Fin (l+1) → F),
      Function.Injective p ∧ p 0 = sj j ∧ p (Fin.last l) = u ∧
      (∀ i : Fin l, (p i.castSucc).val ⊆ (p i.succ).val ∨ (p i.succ).val ⊆ (p i.castSucc).val) ∧
      c = ∑ i : Fin l, (h (p i.succ) - h (p i.castSucc))}
    have Pext : ∀ j (u v : F) c, c ∈ P j u → (u.val ⊆ v.val ∨ v.val ⊆ u.val) →
        ∃ c' ∈ P j v, c' ≤ c + (h v - h u) := by
      rintro j u v c ⟨l, p, hinj, hp0, hpl, hR, rfl⟩ huv
      subst hpl
      obtain ⟨l', q, hq, hq0, hql, hqR, hqs⟩ := extend
        (fun a b : F => a.val ⊆ b.val ∨ b.val ⊆ a.val) (fun a b => h b - h a) l p hinj hR v huv
      exact ⟨_, ⟨l', q, hq, hq0.trans hp0, hql, hqR, rfl⟩, hqs⟩
    have P0 : ∀ j, 0 ∈ P j (sj j) := fun j =>
      ⟨0, fun _ => sj j, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega), rfl, rfl,
        fun i => Fin.elim0 i, by simp⟩
    have Pne : ∀ j u, (P j u).Nonempty := by
      intro j u
      have hb : (clF ∅).val ⊆ (sj j).val := by
        have := clmono ∅ (C {j}) (Finset.empty_subset _)
        simpa [clF, sj, cl, trip] using this
      obtain ⟨c1, hc1, -⟩ := Pext j (sj j) (clF ∅) 0 (P0 j) (Or.inr hb)
      have hu : (clF ∅).val ⊆ u.val := by
        have := clmono ∅ u.val (Finset.empty_subset _)
        rw [u.prop] at this
        exact this
      obtain ⟨c2, hc2, -⟩ := Pext j (clF ∅) u c1 hc1 (Or.inl hu)
      exact ⟨c2, hc2⟩
    let d : Fin n → F → ℕ := fun j u => sInf (P j u)
    have Pmin : ∀ j u c, c ∈ P j u → d j u ≤ c := fun j u c hc => Nat.sInf_le hc
    have Pmem : ∀ j u, d j u ∈ P j u := fun j u => Nat.sInf_mem (Pne j u)
    have P2 : ∀ j (u v : F), (u.val ⊆ v.val ∨ v.val ⊆ u.val) → d j v ≤ d j u + (h v - h u) := by
      intro j u v huv
      obtain ⟨c', hc', hle⟩ := Pext j u v _ (Pmem j u) huv
      exact (Pmin j v c' hc').trans hle
    have P4 : ∀ j, D ≤ d j (clF {j}) := by
      intro j
      obtain ⟨l, p, hinj, hp0, hpl, hR, he⟩ := Pmem j (clF {j})
      rw [he]
      exact hpath j l p (cardF l p hinj) hinj (congrArg Subtype.val hp0)
        (congrArg Subtype.val hpl) hR
    refine ⟨fun x j => D - d j (clF x), ?_, ?_, ?_, ?_, ?_⟩
    · intro x j; exact Nat.sub_le _ _
    · intro x j hj
      have hsub : x ⊆ C {j} := by
        intro i hi
        rw [memC] at hj ⊢
        intro k hk
        rw [Finset.mem_singleton] at hk
        subst hk
        exact hsym (hj i hi)
      have hcl : (clF x).val ⊆ (sj j).val := by
        have := clmono _ _ hsub
        simpa [clF, sj, cl, trip] using this
      have e1 := P2 j (sj j) (clF x) (Or.inr hcl)
      have e2 := hmono _ _ hcl
      have e3 := Pmin j (sj j) 0 (P0 j)
      show D - d j (clF x) = D
      omega
    · intro x j hj
      have hcl : (clF {j}).val ⊆ (clF x).val :=
        clmono _ _ (Finset.singleton_subset_iff.2 hj)
      have e1 := P2 j (clF x) (clF {j}) (Or.inr hcl)
      have e2 := hmono _ _ hcl
      have e3 := P4 j
      show D - d j (clF x) = 0
      omega
    · intro x y hxy j
      have hcl : (clF x).val ⊆ (clF y).val := clmono _ _ hxy
      have e1 := P2 j (clF y) (clF x) (Or.inr hcl)
      have e2 := hmono _ _ hcl
      show D - d j (clF y) ≤ D - d j (clF x)
      omega
    · intro l p a hp
      have key : ∀ i : Fin l, (D - d (a i) (clF (p i.castSucc))) - (D - d (a i) (clF (p i.succ)))
          ≤ h (clF (p i.succ)) - h (clF (p i.castSucc)) := by
        intro i
        have hcl : (clF (p i.castSucc)).val ⊆ (clF (p i.succ)).val := clmono _ _ (hp i)
        have e1 := P2 (a i) _ _ (Or.inl hcl)
        omega
      have t := tele_le l (fun i => h (clF (p i)))
        (fun i => hmono _ _ (clmono _ _ (hp i)))
      calc _ ≤ ∑ i : Fin l, (h (clF (p i.succ)) - h (clF (p i.castSucc))) :=
            Finset.sum_le_sum (fun i _ => key i)
        _ ≤ h (clF (p (Fin.last l))) := t
        _ ≤ B (cl (p (Fin.last l))) := hB _
