import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47145

section Helpers

def satClauses (m n : Nat) (x : Finset (Fin m × (Fin n × Bool))) (s : Fin n → Bool) :
    Finset (Fin m) :=
  (x.filter (fun p => s p.2.1 = p.2.2)).image Prod.fst

lemma mem_satClauses {m n : Nat} {x : Finset (Fin m × (Fin n × Bool))} {s : Fin n → Bool}
    {c : Fin m} :
    c ∈ satClauses m n x s ↔ ∃ v b, (c, v, b) ∈ x ∧ s v = b := by
  simp only [satClauses, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨c', v, b, ⟨hmem, hsat⟩, rfl⟩
    exact ⟨v, b, hmem, hsat⟩
  · rintro ⟨v, b, hmem, hsat⟩
    exact ⟨c, v, b, ⟨hmem, hsat⟩, rfl⟩

def scoreF (m n : Nat) (x : Finset (Fin m × (Fin n × Bool))) : Nat :=
  (Finset.univ : Finset (Fin n → Bool)).sup (fun s => (satClauses m n x s).card)

lemma card_satClauses_le_scoreF (m n : Nat) (x : Finset (Fin m × (Fin n × Bool)))
    (s : Fin n → Bool) :
    (satClauses m n x s).card ≤ scoreF m n x :=
  Finset.le_sup (f := fun s => (satClauses m n x s).card) (Finset.mem_univ s)

lemma exists_scoreF_eq (m n : Nat) (x : Finset (Fin m × (Fin n × Bool))) :
    ∃ s : Fin n → Bool, (satClauses m n x s).card = scoreF m n x := by
  obtain ⟨s, _, hs⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Bool)) Finset.univ_nonempty
      (fun s => (satClauses m n x s).card)
  exact ⟨s, hs.symm⟩

lemma scoreF_le_iff (m n : Nat) (x : Finset (Fin m × (Fin n × Bool))) (k : Nat) :
    scoreF m n x ≤ k ↔ ∀ s : Fin n → Bool, (satClauses m n x s).card ≤ k := by
  simp [scoreF, Finset.sup_le_iff]

lemma scoreF_mono {m n : Nat} {x₁ x₂ : Finset (Fin m × (Fin n × Bool))} (hsub : x₁ ⊆ x₂) :
    scoreF m n x₁ ≤ scoreF m n x₂ := by
  rw [scoreF_le_iff]
  intro s
  have h1 : satClauses m n x₁ s ⊆ satClauses m n x₂ s := by
    intro c hc
    rw [mem_satClauses] at hc ⊢
    rcases hc with ⟨v, b, hm, hs⟩
    exact ⟨v, b, hsub hm, hs⟩
  exact (Finset.card_le_card h1).trans (card_satClauses_le_scoreF m n x₂ s)

def lIdx {m : Nat} (i : Fin m) : Fin (m + m + 1) := (i.castAdd m).castSucc
def rIdx {m : Nat} (i : Fin m) : Fin (m + m + 1) := (Fin.natAdd m i).castSucc

lemma lIdx_inj {m : Nat} : Function.Injective (@lIdx m) := by
  intro i₁ i₂ h
  have hv := congrArg Fin.val h
  simp only [lIdx, Fin.val_castSucc, Fin.val_castAdd] at hv
  exact Fin.ext hv

lemma rIdx_inj {m : Nat} : Function.Injective (@rIdx m) := by
  intro i₁ i₂ h
  have hv := congrArg Fin.val h
  simp only [rIdx, Fin.val_castSucc, Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

lemma lIdx_ne_rIdx {m : Nat} (i₁ i₂ : Fin m) : lIdx i₁ ≠ rIdx i₂ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lIdx, rIdx, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma lIdx_ne_last {m : Nat} (i : Fin m) : lIdx i ≠ Fin.last (m + m) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lIdx, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hv
  omega

lemma rIdx_ne_last {m : Nat} (i : Fin m) : rIdx i ≠ Fin.last (m + m) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [rIdx, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv
  omega

def extS {n : Nat} (s₀ : Fin n → Bool) (bit : Bool) (v : Fin (n + 1)) : Bool :=
  if h : v.val < n then s₀ ⟨v.val, h⟩ else bit

lemma extS_castSucc {n : Nat} (s₀ : Fin n → Bool) (bit : Bool) (v : Fin n) :
    extS s₀ bit v.castSucc = s₀ v := by
  simp [extS, v.isLt]

lemma extS_last {n : Nat} (s₀ : Fin n → Bool) (bit : Bool) :
    extS s₀ bit (Fin.last n) = bit := by
  simp [extS]

def restrS {n : Nat} (s : Fin (n + 1) → Bool) (v : Fin n) : Bool := s v.castSucc

lemma card_disjoint_lr {m : Nat} (S T : Finset (Fin m)) :
    (S.image lIdx ∪ T.image rIdx).card = S.card + T.card := by
  have hdisj : Disjoint (S.image lIdx) (T.image rIdx) := by
    rw [Finset.disjoint_left]
    intro c hcS hcT
    rcases Finset.mem_image.mp hcS with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hcT with ⟨i₂, _, heq⟩
    exact lIdx_ne_rIdx i₁ i₂ heq.symm
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective S lIdx_inj,
    Finset.card_image_of_injective T rIdx_inj]

end Helpers

end PEqualNP.Outside.L_meta_47145

open PEqualNP.Outside.L_meta_47145 in
theorem PEqualNP.Outside.L_meta_47145 :
let score := fun (m n : Nat) (x : Finset (Fin m × (Fin n × Bool))) =>
  (Finset.univ : Finset (Fin n → Bool)).sup (fun s =>
    ((x.filter (fun p => s p.2.1 = p.2.2)).image Prod.fst).card)
∀ (m n : Nat),
  let V := Fin m × (Fin n × Bool)
  let U := Fin (m+m+1) × (Fin (n+1) × Bool)
  let l := fun (i : Fin m) => (i.castAdd m).castSucc
  let r := fun (i : Fin m) => (Fin.natAdd m i).castSucc
  let j : U := (Fin.last (m+m), Fin.last n, true)
  let allow := (Finset.univ : Finset U).filter (fun p =>
    p ≠ j ∧ ¬ (p.1 = j.1 ∨ p.2.1 = j.2.1 ∧ p.2.2 ≠ j.2.2))
  ∀ (A B : Finset V),
    let z : Finset U :=
      A.image (fun p => (l p.1, p.2.1.castSucc, p.2.2)) ∪
      B.image (fun p => (r p.1, p.2.1.castSucc, p.2.2)) ∪
      (Finset.univ : Finset (Fin m)).image (fun i => (l i, Fin.last n, false)) ∪
      (Finset.univ : Finset (Fin m)).image (fun i => (r i, Fin.last n, true))
    let a := score m n A
    let b := score m n B
    let value := score (m+m+1) (n+1)
    value z = m + max a b ∧ value (insert j z) = m + max (a+1) b ∧
      ((∃ u : Finset U, u ⊆ z ∧ u ⊆ allow ∧ value u = value z) ↔ b ≤ a) := by
  intro score m n V U l r j allow A B z a b value
  have hscore_eq : ∀ (m' n' : Nat) (x : Finset (Fin m' × (Fin n' × Bool))),
      score m' n' x = scoreF m' n' x := fun _ _ _ => rfl
  have hl_eq : l = @lIdx m := rfl
  have hr_eq : r = @rIdx m := rfl
  have hmem_z : ∀ c v bb, (c, v, bb) ∈ z ↔
      (∃ i v₀, c = lIdx i ∧ v = v₀.castSucc ∧ (i, v₀, bb) ∈ A) ∨
      (∃ i v₀, c = rIdx i ∧ v = v₀.castSucc ∧ (i, v₀, bb) ∈ B) ∨
      (∃ i, c = lIdx i ∧ v = Fin.last n ∧ bb = false) ∨
      (∃ i, c = rIdx i ∧ v = Fin.last n ∧ bb = true) := by
    intro c v bb
    simp only [z, hl_eq, hr_eq, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro (((⟨⟨i, v₀, bb'⟩, hA, h1, h2, h3⟩ | ⟨⟨i, v₀, bb'⟩, hB, h1, h2, h3⟩) |
        ⟨i, h1, h2, h3⟩) | ⟨i, h1, h2, h3⟩)
      · subst h1 h2 h3; exact Or.inl ⟨i, v₀, rfl, rfl, hA⟩
      · subst h1 h2 h3; exact Or.inr (Or.inl ⟨i, v₀, rfl, rfl, hB⟩)
      · subst h1 h2 h3; exact Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl, rfl⟩))
      · subst h1 h2 h3; exact Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl, rfl⟩))
    · rintro (⟨i, v₀, rfl, rfl, hA⟩ | ⟨i, v₀, rfl, rfl, hB⟩ |
        ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨(i, v₀, bb), hA, rfl, rfl, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨(i, v₀, bb), hB, rfl, rfl, rfl⟩))
      · exact Or.inl (Or.inr ⟨i, rfl, rfl, rfl⟩)
      · exact Or.inr ⟨i, rfl, rfl, rfl⟩
  have hsat_z_true : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = true →
      satClauses (m + m + 1) (n + 1) z s =
        (satClauses m n A (restrS s)).image lIdx ∪ Finset.univ.image rIdx := by
    intro s hsT
    ext c
    simp only [mem_satClauses, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, bb, hz, hsv⟩
      rcases (hmem_z c v bb).mp hz with
        ⟨i, v₀, rfl, rfl, hA⟩ | ⟨i, v₀, rfl, rfl, _⟩ | ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩
      · exact Or.inl ⟨i, ⟨v₀, bb, hA, hsv⟩, rfl⟩
      · exact Or.inr ⟨i, rfl⟩
      · rw [hsT] at hsv; cases hsv
      · exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, rfl⟩)
      · rcases hi with ⟨v₀, bb, hA, hsv⟩
        exact ⟨v₀.castSucc, bb, (hmem_z _ _ _).mpr (Or.inl ⟨i, v₀, rfl, rfl, hA⟩), hsv⟩
      · exact ⟨Fin.last n, true, (hmem_z _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl, rfl⟩))), hsT⟩
  have hsat_z_false : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = false →
      satClauses (m + m + 1) (n + 1) z s =
        Finset.univ.image lIdx ∪ (satClauses m n B (restrS s)).image rIdx := by
    intro s hsF
    ext c
    simp only [mem_satClauses, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, bb, hz, hsv⟩
      rcases (hmem_z c v bb).mp hz with
        ⟨i, v₀, rfl, rfl, _⟩ | ⟨i, v₀, rfl, rfl, hB⟩ | ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, ⟨v₀, bb, hB, hsv⟩, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · rw [hsF] at hsv; cases hsv
    · rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨Fin.last n, false, (hmem_z _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl, rfl⟩))), hsF⟩
      · rcases hi with ⟨v₀, bb, hB, hsv⟩
        exact ⟨v₀.castSucc, bb, (hmem_z _ _ _).mpr (Or.inr (Or.inl ⟨i, v₀, rfl, rfl, hB⟩)), hsv⟩
  have hcard_z_true : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = true →
      (satClauses (m + m + 1) (n + 1) z s).card = m + (satClauses m n A (restrS s)).card := by
    intro s hsT
    rw [hsat_z_true s hsT, card_disjoint_lr, Finset.card_univ, Fintype.card_fin]
    omega
  have hcard_z_false : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = false →
      (satClauses (m + m + 1) (n + 1) z s).card = m + (satClauses m n B (restrS s)).card := by
    intro s hsF
    rw [hsat_z_false s hsF, card_disjoint_lr, Finset.card_univ, Fintype.card_fin]
  have hlast_not_z : ∀ s : Fin (n + 1) → Bool,
      Fin.last (m + m) ∉ satClauses (m + m + 1) (n + 1) z s := by
    intro s hmem
    rcases mem_satClauses.mp hmem with ⟨v, bb, hz, _⟩
    rcases (hmem_z _ v bb).mp hz with
      ⟨i, _, h, _, _⟩ | ⟨i, _, h, _, _⟩ | ⟨i, h, _, _⟩ | ⟨i, h, _, _⟩
    · exact lIdx_ne_last i h.symm
    · exact rIdx_ne_last i h.symm
    · exact lIdx_ne_last i h.symm
    · exact rIdx_ne_last i h.symm
  have hcard_jz_true : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = true →
      (satClauses (m + m + 1) (n + 1) (insert j z) s).card =
        m + (satClauses m n A (restrS s)).card + 1 := by
    intro s hsT
    have hset : satClauses (m + m + 1) (n + 1) (insert j z) s =
        insert (Fin.last (m + m)) (satClauses (m + m + 1) (n + 1) z s) := by
      ext c
      simp only [mem_satClauses, Finset.mem_insert, Prod.mk.injEq, j]
      constructor
      · rintro ⟨v, bb, (⟨rfl, rfl, rfl⟩ | hz), hsv⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v, bb, hz, hsv⟩
      · rintro (rfl | ⟨v, bb, hz, hsv⟩)
        · exact ⟨Fin.last n, true, Or.inl ⟨rfl, rfl, rfl⟩, hsT⟩
        · exact ⟨v, bb, Or.inr hz, hsv⟩
    rw [hset, Finset.card_insert_of_notMem (hlast_not_z s), hcard_z_true s hsT]
  have hcard_jz_false : ∀ s : Fin (n + 1) → Bool, s (Fin.last n) = false →
      (satClauses (m + m + 1) (n + 1) (insert j z) s).card =
        m + (satClauses m n B (restrS s)).card := by
    intro s hsF
    have hset : satClauses (m + m + 1) (n + 1) (insert j z) s =
        satClauses (m + m + 1) (n + 1) z s := by
      ext c
      simp only [mem_satClauses, Finset.mem_insert, Prod.mk.injEq, j]
      constructor
      · rintro ⟨v, bb, (⟨rfl, rfl, rfl⟩ | hz), hsv⟩
        · rw [hsF] at hsv; cases hsv
        · exact ⟨v, bb, hz, hsv⟩
      · rintro ⟨v, bb, hz, hsv⟩
        exact ⟨v, bb, Or.inr hz, hsv⟩
    rw [hset, hcard_z_false s hsF]
  -- Part 1: value z = m + max a b
  have hval_z : value z = m + max a b := by
    change scoreF (m + m + 1) (n + 1) z = m + max (scoreF m n A) (scoreF m n B)
    apply le_antisymm
    · rw [scoreF_le_iff]
      intro s
      cases hs : s (Fin.last n)
      · rw [hcard_z_false s hs]
        have := card_satClauses_le_scoreF m n B (restrS s)
        omega
      · rw [hcard_z_true s hs]
        have := card_satClauses_le_scoreF m n A (restrS s)
        omega
    · obtain ⟨sA, hsA⟩ := exists_scoreF_eq m n A
      obtain ⟨sB, hsB⟩ := exists_scoreF_eq m n B
      have hgeA : m + scoreF m n A ≤ scoreF (m + m + 1) (n + 1) z := by
        have h1 := card_satClauses_le_scoreF (m + m + 1) (n + 1) z (extS sA true)
        rw [hcard_z_true (extS sA true) (extS_last sA true)] at h1
        have hrA : restrS (extS sA true) = sA := funext (extS_castSucc sA true)
        rw [hrA, hsA] at h1
        exact h1
      have hgeB : m + scoreF m n B ≤ scoreF (m + m + 1) (n + 1) z := by
        have h1 := card_satClauses_le_scoreF (m + m + 1) (n + 1) z (extS sB false)
        rw [hcard_z_false (extS sB false) (extS_last sB false)] at h1
        have hrB : restrS (extS sB false) = sB := funext (extS_castSucc sB false)
        rw [hrB, hsB] at h1
        exact h1
      omega
  -- Part 2: value (insert j z) = m + max (a + 1) b
  have hval_jz : value (insert j z) = m + max (a + 1) b := by
    change scoreF (m + m + 1) (n + 1) (insert j z) = m + max (scoreF m n A + 1) (scoreF m n B)
    apply le_antisymm
    · rw [scoreF_le_iff]
      intro s
      cases hs : s (Fin.last n)
      · rw [hcard_jz_false s hs]
        have := card_satClauses_le_scoreF m n B (restrS s)
        omega
      · rw [hcard_jz_true s hs]
        have := card_satClauses_le_scoreF m n A (restrS s)
        omega
    · obtain ⟨sA, hsA⟩ := exists_scoreF_eq m n A
      obtain ⟨sB, hsB⟩ := exists_scoreF_eq m n B
      have hgeA : m + (scoreF m n A + 1) ≤ scoreF (m + m + 1) (n + 1) (insert j z) := by
        have h1 := card_satClauses_le_scoreF (m + m + 1) (n + 1) (insert j z) (extS sA true)
        rw [hcard_jz_true (extS sA true) (extS_last sA true)] at h1
        have hrA : restrS (extS sA true) = sA := funext (extS_castSucc sA true)
        rw [hrA, hsA] at h1
        omega
      have hgeB : m + scoreF m n B ≤ scoreF (m + m + 1) (n + 1) (insert j z) := by
        have h1 := card_satClauses_le_scoreF (m + m + 1) (n + 1) (insert j z) (extS sB false)
        rw [hcard_jz_false (extS sB false) (extS_last sB false)] at h1
        have hrB : restrS (extS sB false) = sB := funext (extS_castSucc sB false)
        rw [hrB, hsB] at h1
        exact h1
      omega
  -- Part 3: value (z ∩ allow) = m + a
  have hval_za : value (z ∩ allow) = m + a := by
    change scoreF (m + m + 1) (n + 1) (z ∩ allow) = m + scoreF m n A
    apply le_antisymm
    · rw [scoreF_le_iff]
      intro s
      cases hs : s (Fin.last n)
      · have hsub_sat : satClauses (m + m + 1) (n + 1) (z ∩ allow) s ⊆
            (satClauses m n A (restrS s)).image lIdx ∪ Finset.univ.image rIdx := by
          intro c hc
          rcases mem_satClauses.mp hc with ⟨v, bb, hmem, hsv⟩
          rcases Finset.mem_inter.mp hmem with ⟨hz, hall⟩
          simp only [allow, Finset.mem_filter, Finset.mem_univ, true_and, j] at hall
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          rcases (hmem_z c v bb).mp hz with
            ⟨i, v₀, rfl, rfl, hA⟩ | ⟨i, v₀, rfl, rfl, _⟩ | ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩
          · exact Or.inl ⟨i, mem_satClauses.mpr ⟨v₀, bb, hA, hsv⟩, rfl⟩
          · exact Or.inr ⟨i, rfl⟩
          · exact absurd (Or.inr ⟨rfl, by decide⟩) hall.2
          · exact Or.inr ⟨i, rfl⟩
        have h1 := Finset.card_le_card hsub_sat
        rw [card_disjoint_lr, Finset.card_univ, Fintype.card_fin] at h1
        have h2 := card_satClauses_le_scoreF m n A (restrS s)
        omega
      · have h1 := Finset.card_le_card (show satClauses (m + m + 1) (n + 1) (z ∩ allow) s ⊆
            satClauses (m + m + 1) (n + 1) z s from fun c hc => by
              rcases mem_satClauses.mp hc with ⟨v, bb, hm, hsv⟩
              exact mem_satClauses.mpr ⟨v, bb, (Finset.mem_inter.mp hm).1, hsv⟩)
        rw [hcard_z_true s hs] at h1
        have h2 := card_satClauses_le_scoreF m n A (restrS s)
        omega
    · obtain ⟨sA, hsA⟩ := exists_scoreF_eq m n A
      let s := extS sA true
      have hsT : s (Fin.last n) = true := extS_last sA true
      have hrA : restrS s = sA := funext (extS_castSucc sA true)
      have hsup_sat : (satClauses m n A sA).image lIdx ∪ Finset.univ.image rIdx ⊆
          satClauses (m + m + 1) (n + 1) (z ∩ allow) s := by
        intro c hc
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hc
        rw [mem_satClauses]
        rcases hc with ⟨i, hi, rfl⟩ | ⟨i, rfl⟩
        · rcases mem_satClauses.mp hi with ⟨v₀, bb, hA, hsv⟩
          refine ⟨v₀.castSucc, bb, Finset.mem_inter.mpr ⟨(hmem_z _ _ _).mpr (Or.inl ⟨i, v₀, rfl, rfl, hA⟩), ?_⟩, ?_⟩
          · simp only [allow, Finset.mem_filter, Finset.mem_univ, true_and, j]
            refine ⟨fun h => lIdx_ne_last i (congrArg Prod.fst h), ?_⟩
            rintro (h1 | ⟨h2, _⟩)
            · exact lIdx_ne_last i h1
            · exact Fin.castSucc_ne_last v₀ h2
          · simpa [s, extS_castSucc] using hsv
        · refine ⟨Fin.last n, true, Finset.mem_inter.mpr ⟨(hmem_z _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl, rfl⟩))), ?_⟩, hsT⟩
          simp only [allow, Finset.mem_filter, Finset.mem_univ, true_and, j]
          refine ⟨fun h => rIdx_ne_last i (congrArg Prod.fst h), ?_⟩
          rintro (h1 | h2)
          · exact rIdx_ne_last i h1
          · exact h2 rfl
      have h1 := (Finset.card_le_card hsup_sat).trans
        (card_satClauses_le_scoreF (m + m + 1) (n + 1) (z ∩ allow) s)
      rw [card_disjoint_lr, Finset.card_univ, Fintype.card_fin, hsA] at h1
      omega
  refine ⟨hval_z, hval_jz, ?_⟩
  constructor
  · rintro ⟨u, huz, hua, hvu⟩
    have hsub : u ⊆ z ∩ allow := Finset.subset_inter huz hua
    have hle : value u ≤ value (z ∩ allow) := scoreF_mono hsub
    rw [hvu, hval_z, hval_za] at hle
    omega
  · intro hba
    refine ⟨z ∩ allow, Finset.inter_subset_left, Finset.inter_subset_right, ?_⟩
    rw [hval_za, hval_z]
    omega
