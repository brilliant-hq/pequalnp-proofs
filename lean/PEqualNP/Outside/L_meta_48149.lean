import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48149

section Core

def graphF (n : Nat) (g : Fin n → Fin n → Bool) : Prop :=
  (∀ i, g i i = false) ∧ (∀ i j, g i j = g j i)

def indepF {n : Nat} (g : Fin n → Fin n → Bool) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, g i j = false

def alphaF {n : Nat} (g : Fin n → Fin n → Bool) (x : Finset (Fin n)) : Nat :=
  (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup Finset.card

lemma exists_max_indep {n : Nat} (g : Fin n → Fin n → Bool) (x : Finset (Fin n)) :
    ∃ s ⊆ x, indepF g s ∧ s.card = alphaF g x := by
  let F := x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)
  have hne : F.Nonempty := ⟨∅, by simp [F]⟩
  obtain ⟨s, hsF, hmax⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hsF
  exact ⟨s, hsF.1, hsF.2, hmax.symm⟩

lemma card_le_alphaF {n : Nat} (g : Fin n → Fin n → Bool) {x s : Finset (Fin n)}
    (hsx : s ⊆ x) (hind : indepF g s) : s.card ≤ alphaF g x := by
  unfold alphaF
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsx, hind⟩)

lemma alphaF_empty {n : Nat} (g : Fin n → Fin n → Bool) : alphaF g ∅ = 0 := by
  obtain ⟨s, hs, _, hc⟩ := exists_max_indep g ∅
  rw [Finset.subset_empty.mp hs] at hc
  simpa using hc.symm

lemma alphaF_insert_pair_le {n : Nat} (g : Fin n → Fin n → Bool)
    (y : Finset (Fin n)) {u v : Fin n} (huv : g u v = true) :
    alphaF g (insert u (insert v y)) ≤ alphaF g y + 1 := by
  obtain ⟨s, hs, hind, hcard⟩ := exists_max_indep g (insert u (insert v y))
  have hnotboth : ¬ (u ∈ s ∧ v ∈ s) := by
    rintro ⟨hu, hv⟩
    have := hind u hu v hv
    rw [huv] at this; cases this
  by_cases hu : u ∈ s
  · have hv : v ∉ s := fun h => hnotboth ⟨hu, h⟩
    have hsub : s.erase u ⊆ y := by
      intro w hw
      rcases Finset.mem_erase.mp hw with ⟨hne, hws⟩
      rcases Finset.mem_insert.mp (hs hws) with rfl | hw2
      · exact absurd rfl hne
      · rcases Finset.mem_insert.mp hw2 with rfl | hwy
        · exact absurd hws hv
        · exact hwy
    have hind' : indepF g (s.erase u) := fun i hi j hj =>
      hind i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)
    have h1 := card_le_alphaF g hsub hind'
    have h2 : (s.erase u).card + 1 = s.card := Finset.card_erase_add_one hu
    omega
  · by_cases hv : v ∈ s
    · have hsub : s.erase v ⊆ y := by
        intro w hw
        rcases Finset.mem_erase.mp hw with ⟨hne, hws⟩
        rcases Finset.mem_insert.mp (hs hws) with rfl | hw2
        · exact absurd hws hu
        · rcases Finset.mem_insert.mp hw2 with rfl | hwy
          · exact absurd rfl hne
          · exact hwy
      have hind' : indepF g (s.erase v) := fun i hi j hj =>
        hind i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)
      have h1 := card_le_alphaF g hsub hind'
      have h2 : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
      omega
    · have hsub : s ⊆ y := by
        intro w hws
        rcases Finset.mem_insert.mp (hs hws) with rfl | hw2
        · exact absurd hws hu
        · rcases Finset.mem_insert.mp hw2 with rfl | hwy
          · exact absurd hws hv
          · exact hwy
      have h1 := card_le_alphaF g hsub hind
      omega

def packF {n : Nat} (f : Finset (Fin n) → Fin n → Bool) : Nat → Finset (Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ (u v : Finset (Fin n)) (j : Fin n),
      prev u ∧ u ⊆ v ∧ v ⊆ x ∧ f u j = true ∧ f v j = false)

lemma packF_mono_set {n : Nat} (f : Finset (Fin n) → Fin n → Bool)
    {l : Nat} {x₁ x₂ : Finset (Fin n)} (hsub : x₁ ⊆ x₂) :
    packF f l x₁ → packF f l x₂ := by
  cases l with
  | zero => intro _; trivial
  | succ l =>
    rintro ⟨u, v, j, hu, huv, hvx, hfu, hfv⟩
    exact ⟨u, v, j, hu, huv, hvx.trans hsub, hfu, hfv⟩

lemma packF_pred {n : Nat} (f : Finset (Fin n) → Fin n → Bool)
    {l : Nat} {x : Finset (Fin n)} :
    packF f (l + 1) x → packF f l x := by
  rintro ⟨u, v, j, hu, huv, hvx, _, _⟩
  exact packF_mono_set f (huv.trans hvx) hu

lemma packF_mono_nat {n : Nat} (f : Finset (Fin n) → Fin n → Bool)
    {l₁ l₂ : Nat} {x : Finset (Fin n)} (hle : l₁ ≤ l₂) :
    packF f l₂ x → packF f l₁ x := by
  induction l₂ with
  | zero =>
    have : l₁ = 0 := by omega
    subst this; exact id
  | succ l₂ ih =>
    intro h
    by_cases heq : l₁ = l₂ + 1
    · subst heq; exact h
    · exact ih (by omega) (packF_pred f h)

def admitsF (n : Nat) (g : Fin n → Fin n → Bool) (e : Nat) : Prop :=
  ∃ f : Finset (Fin n) → Fin n → Bool,
    (∀ x j, (j ∉ x ∧ ∀ i ∈ x, g i j = false) → f x j = true) ∧
    (∀ x j, j ∈ x → f x j = false) ∧
    (∀ x y j, x ⊆ y → f y j = true → f x j = true) ∧
    ∀ x l, packF f l x → l ≤ alphaF g x + e

def clusterF {n : Nat} (g : Fin n → Fin n → Bool) (D : Finset (Fin n)) : Prop :=
  ∀ i ∉ D, ∀ j ∉ D, ∀ k ∉ D, g i j = true → g j k = true → i = k ∨ g i k = true

/-! ### Part 1: Additivity Across Disjoint Union `bothG` -/

def bothG {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool) :
    Fin (a + b) → Fin (a + b) → Bool :=
  Fin.addCases (fun i => Fin.addCases (g i) (fun _ => false))
    (fun j => Fin.addCases (fun _ => false) (h j))

def inlA {a b : Nat} (i : Fin a) : Fin (a + b) := Fin.castAdd b i
def inrB {a b : Nat} (j : Fin b) : Fin (a + b) := Fin.natAdd a j

lemma inlA_inj {a b : Nat} : Function.Injective (@inlA a b) := by
  intro i₁ i₂ h; exact Fin.ext (by have := congrArg Fin.val h; simpa [inlA] using this)

lemma inrB_inj {a b : Nat} : Function.Injective (@inrB a b) := by
  intro j₁ j₂ h; exact Fin.ext (by have := congrArg Fin.val h; simp [inrB] at this; omega)

lemma inlA_ne_inrB {a b : Nat} (i : Fin a) (j : Fin b) : inlA i ≠ inrB j := by
  intro h; have := congrArg Fin.val h; simp [inlA, inrB] at this; omega

lemma bothG_inl_inl {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool)
    (i₁ i₂ : Fin a) : bothG g h (inlA i₁) (inlA i₂) = g i₁ i₂ := by
  simp [bothG, inlA]

lemma bothG_inl_inr {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool)
    (i : Fin a) (j : Fin b) : bothG g h (inlA i) (inrB j) = false := by
  simp [bothG, inlA, inrB]

lemma bothG_inr_inl {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool)
    (j : Fin b) (i : Fin a) : bothG g h (inrB j) (inlA i) = false := by
  simp [bothG, inlA, inrB]

lemma bothG_inr_inr {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool)
    (j₁ j₂ : Fin b) : bothG g h (inrB j₁) (inrB j₂) = h j₁ j₂ := by
  simp [bothG, inrB]

def projL {a b : Nat} (x : Finset (Fin (a + b))) : Finset (Fin a) :=
  Finset.univ.filter (fun i => inlA i ∈ x)

def projR {a b : Nat} (x : Finset (Fin (a + b))) : Finset (Fin b) :=
  Finset.univ.filter (fun j => inrB j ∈ x)

def embL {a b : Nat} (x₁ : Finset (Fin a)) : Finset (Fin (a + b)) := x₁.image inlA
def embR {a b : Nat} (x₂ : Finset (Fin b)) : Finset (Fin (a + b)) := x₂.image inrB

lemma mem_projL {a b : Nat} {x : Finset (Fin (a + b))} {i : Fin a} :
    i ∈ projL x ↔ inlA i ∈ x := by simp [projL]

lemma mem_projR {a b : Nat} {x : Finset (Fin (a + b))} {j : Fin b} :
    j ∈ projR x ↔ inrB j ∈ x := by simp [projR]

lemma projL_mono {a b : Nat} {x y : Finset (Fin (a + b))} (h : x ⊆ y) : projL x ⊆ projL y := by
  intro i hi; exact mem_projL.mpr (h (mem_projL.mp hi))

lemma projR_mono {a b : Nat} {x y : Finset (Fin (a + b))} (h : x ⊆ y) : projR x ⊆ projR y := by
  intro j hj; exact mem_projR.mpr (h (mem_projR.mp hj))

lemma embL_mono {a b : Nat} {x y : Finset (Fin a)} (h : x ⊆ y) : embL (b := b) x ⊆ embL y :=
  Finset.image_subset_image h

lemma embR_mono {a b : Nat} {x y : Finset (Fin b)} (h : x ⊆ y) : embR (a := a) x ⊆ embR y :=
  Finset.image_subset_image h

lemma projL_embLR {a b : Nat} (x₁ : Finset (Fin a)) (x₂ : Finset (Fin b)) :
    projL (embL x₁ ∪ embR x₂) = x₁ := by
  ext i
  simp only [mem_projL, Finset.mem_union, embL, embR, Finset.mem_image]
  constructor
  · rintro (⟨i', hi', heq⟩ | ⟨j, _, heq⟩)
    · cases inlA_inj heq; exact hi'
    · exact absurd heq.symm (inlA_ne_inrB i j)
  · intro hi; exact Or.inl ⟨i, hi, rfl⟩

lemma projR_embLR {a b : Nat} (x₁ : Finset (Fin a)) (x₂ : Finset (Fin b)) :
    projR (embL x₁ ∪ embR x₂) = x₂ := by
  ext j
  simp only [mem_projR, Finset.mem_union, embL, embR, Finset.mem_image]
  constructor
  · rintro (⟨i, _, heq⟩ | ⟨j', hj', heq⟩)
    · exact absurd heq (inlA_ne_inrB i j)
    · cases inrB_inj heq; exact hj'
  · intro hj; exact Or.inr ⟨j, hj, rfl⟩

lemma embLR_proj {a b : Nat} (x : Finset (Fin (a + b))) :
    embL (projL x) ∪ embR (projR x) = x := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · change inlA i ∈ embL (projL x) ∪ embR (projR x) ↔ inlA i ∈ x
    simp only [Finset.mem_union, embL, embR, Finset.mem_image, mem_projL]
    constructor
    · rintro (⟨i', hi', heq⟩ | ⟨j, _, heq⟩)
      · cases inlA_inj heq; exact hi'
      · exact absurd heq.symm (inlA_ne_inrB i j)
    · intro hi; exact Or.inl ⟨i, hi, rfl⟩
  · change inrB j ∈ embL (projL x) ∪ embR (projR x) ↔ inrB j ∈ x
    simp only [Finset.mem_union, embL, embR, Finset.mem_image, mem_projR]
    constructor
    · rintro (⟨i, _, heq⟩ | ⟨j', hj', heq⟩)
      · exact absurd heq (inlA_ne_inrB i j)
      · cases inrB_inj heq; exact hj'
    · intro hj; exact Or.inr ⟨j, hj, rfl⟩

lemma card_embLR {a b : Nat} (x₁ : Finset (Fin a)) (x₂ : Finset (Fin b)) :
    (embL x₁ ∪ embR x₂).card = x₁.card + x₂.card := by
  have hdisj : Disjoint (embL (b := b) x₁) (embR (a := a) x₂) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rcases Finset.mem_image.mp hk1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hk2 with ⟨j, _, heq⟩
    exact inlA_ne_inrB i j heq.symm
  rw [Finset.card_union_of_disjoint hdisj]
  dsimp only [embL, embR]
  rw [Finset.card_image_of_injective x₁ inlA_inj,
    Finset.card_image_of_injective x₂ inrB_inj]

lemma alphaF_both {a b : Nat} (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool)
    (x : Finset (Fin (a + b))) :
    alphaF (bothG g h) x = alphaF g (projL x) + alphaF h (projR x) := by
  apply le_antisymm
  · obtain ⟨s, hsx, hind, hcard⟩ := exists_max_indep (bothG g h) x
    have hindL : indepF g (projL s) := fun i₁ hi₁ i₂ hi₂ => by
      have := hind (inlA i₁) (mem_projL.mp hi₁) (inlA i₂) (mem_projL.mp hi₂)
      rwa [bothG_inl_inl] at this
    have hindR : indepF h (projR s) := fun j₁ hj₁ j₂ hj₂ => by
      have := hind (inrB j₁) (mem_projR.mp hj₁) (inrB j₂) (mem_projR.mp hj₂)
      rwa [bothG_inr_inr] at this
    have hL := card_le_alphaF g (projL_mono hsx) hindL
    have hR := card_le_alphaF h (projR_mono hsx) hindR
    have hsc : s.card = (projL s).card + (projR s).card := by
      rw [← card_embLR, embLR_proj]
    omega
  · obtain ⟨s₁, hs₁, hind₁, hc₁⟩ := exists_max_indep g (projL x)
    obtain ⟨s₂, hs₂, hind₂, hc₂⟩ := exists_max_indep h (projR x)
    have hsub : embL s₁ ∪ embR s₂ ⊆ x := by
      rw [← embLR_proj x]
      exact Finset.union_subset_union (embL_mono hs₁) (embR_mono hs₂)
    have hind : indepF (bothG g h) (embL s₁ ∪ embR s₂) := by
      intro k₁ hk₁ k₂ hk₂
      rcases Finset.mem_union.mp hk₁ with h1 | h1 <;>
      rcases Finset.mem_union.mp hk₂ with h2 | h2
      · rcases Finset.mem_image.mp h1 with ⟨i₁, hi₁, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨i₂, hi₂, rfl⟩
        rw [bothG_inl_inl]; exact hind₁ i₁ hi₁ i₂ hi₂
      · rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
        exact bothG_inl_inr g h i j
      · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
        exact bothG_inr_inl g h j i
      · rcases Finset.mem_image.mp h1 with ⟨j₁, hj₁, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨j₂, hj₂, rfl⟩
        rw [bothG_inr_inr]; exact hind₂ j₁ hj₁ j₂ hj₂
    have hle := card_le_alphaF (bothG g h) hsub hind
    rw [card_embLR, hc₁, hc₂] at hle
    exact hle

lemma exists_min_excess {a : Nat} (g : Fin a → Fin a → Bool) (f₁ : Finset (Fin a) → Fin a → Bool)
    (e : Nat) (hPe : ∀ x₁ l, packF f₁ l x₁ → l ≤ alphaF g x₁ + e) :
    ∃ (u : Nat) (x₁ : Finset (Fin a)), u ≤ e ∧ packF f₁ (alphaF g x₁ + u) x₁ ∧
      ∀ x l, packF f₁ l x → l ≤ alphaF g x + u := by
  classical
  let P : Nat → Prop := fun u => ∀ x l, packF f₁ l x → l ≤ alphaF g x + u
  have hex : ∃ u, P u := ⟨e, hPe⟩
  let u := Nat.find hex
  have hu_spec : P u := Nat.find_spec hex
  have hu_le : u ≤ e := Nat.find_min' hex hPe
  by_cases hu0 : u = 0
  · refine ⟨u, ∅, hu_le, ?_, hu_spec⟩
    rw [hu0, alphaF_empty]; trivial
  · have hnot : ¬ P (u - 1) := Nat.find_min hex (by omega)
    dsimp only [P] at hnot
    push Not at hnot
    rcases hnot with ⟨x₁, l, hpl, hgt⟩
    refine ⟨u, x₁, hu_le, packF_mono_nat f₁ (by omega) hpl, hu_spec⟩

lemma admits_both_iff (a b : Nat) (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool) (e : Nat) :
    admitsF (a + b) (bothG g h) e ↔ ∃ u v : Nat, u + v ≤ e ∧ admitsF a g u ∧ admitsF b h v := by
  constructor
  · rintro ⟨f, hf1, hf2, hf3, hf4⟩
    let f₁ : Finset (Fin a) → Fin a → Bool := fun x₁ i => f (embL x₁) (inlA i)
    have hf₁_1 : ∀ x₁ i, (i ∉ x₁ ∧ ∀ k ∈ x₁, g k i = false) → f₁ x₁ i = true := by
      intro x₁ i ⟨hni, hno⟩
      refine hf1 (embL x₁) (inlA i) ⟨?_, ?_⟩
      · intro hm; rcases Finset.mem_image.mp hm with ⟨k, hk, heq⟩; cases inlA_inj heq; exact hni hk
      · intro k hk; rcases Finset.mem_image.mp hk with ⟨i', hi', rfl⟩
        rw [bothG_inl_inl]; exact hno i' hi'
    have hf₁_2 : ∀ x₁ i, i ∈ x₁ → f₁ x₁ i = false := fun x₁ i hi =>
      hf2 (embL x₁) (inlA i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hf₁_3 : ∀ x₁ y₁ i, x₁ ⊆ y₁ → f₁ y₁ i = true → f₁ x₁ i = true := fun x₁ y₁ i hsub =>
      hf3 (embL x₁) (embL y₁) (inlA i) (embL_mono hsub)
    have hlift1 : ∀ l x₁, packF f₁ l x₁ → packF f l (embL x₁) := by
      intro l
      induction l with
      | zero => intro _ _; trivial
      | succ l ih =>
        intro x₁ ⟨u₁, v₁, i, hu₁, huv₁, hv₁x, hfu, hfv⟩
        exact ⟨embL u₁, embL v₁, inlA i, ih u₁ hu₁, embL_mono huv₁, embL_mono hv₁x, hfu, hfv⟩
    have hPe : ∀ x₁ l, packF f₁ l x₁ → l ≤ alphaF g x₁ + e := by
      intro x₁ l hpl
      have h1 := hf4 (embL x₁) l (hlift1 l x₁ hpl)
      have h2 : alphaF (bothG g h) (embL x₁) = alphaF g x₁ := by
        have hun : embL (b := b) x₁ = embL x₁ ∪ embR ∅ := by simp [embR]
        rw [hun, alphaF_both, projL_embLR, projR_embLR, alphaF_empty, add_zero]
      omega
    obtain ⟨u, x₁, hu_le, hpx₁, hPu⟩ := exists_min_excess g f₁ e hPe
    let f₂ : Finset (Fin b) → Fin b → Bool := fun x₂ j => f (embL x₁ ∪ embR x₂) (inrB j)
    have hf₂_1 : ∀ x₂ j, (j ∉ x₂ ∧ ∀ k ∈ x₂, h k j = false) → f₂ x₂ j = true := by
      intro x₂ j ⟨hnj, hno⟩
      refine hf1 (embL x₁ ∪ embR x₂) (inrB j) ⟨?_, ?_⟩
      · intro hm
        rcases Finset.mem_union.mp hm with hL | hR
        · rcases Finset.mem_image.mp hL with ⟨i, _, heq⟩; exact inlA_ne_inrB i j heq
        · rcases Finset.mem_image.mp hR with ⟨k, hk, heq⟩; cases inrB_inj heq; exact hnj hk
      · intro k hk
        rcases Finset.mem_union.mp hk with hL | hR
        · rcases Finset.mem_image.mp hL with ⟨i, _, rfl⟩; exact bothG_inl_inr g h i j
        · rcases Finset.mem_image.mp hR with ⟨k', hk', rfl⟩
          rw [bothG_inr_inr]; exact hno k' hk'
    have hf₂_2 : ∀ x₂ j, j ∈ x₂ → f₂ x₂ j = false := fun x₂ j hj =>
      hf2 (embL x₁ ∪ embR x₂) (inrB j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    have hf₂_3 : ∀ x₂ y₂ j, x₂ ⊆ y₂ → f₂ y₂ j = true → f₂ x₂ j = true := fun x₂ y₂ j hsub =>
      hf3 (embL x₁ ∪ embR x₂) (embL x₁ ∪ embR y₂) (inrB j)
        (Finset.union_subset_union_right (embR_mono hsub))
    have happend : ∀ l₂ x₂, packF f₂ l₂ x₂ →
        packF f (alphaF g x₁ + u + l₂) (embL x₁ ∪ embR x₂) := by
      intro l₂
      induction l₂ with
      | zero =>
        intro x₂ _
        exact packF_mono_set f Finset.subset_union_left (hlift1 (alphaF g x₁ + u) x₁ hpx₁)
      | succ l₂ ih =>
        intro x₂ ⟨u₂, v₂, j, hu₂, huv₂, hv₂x, hfu, hfv⟩
        have hprev := ih u₂ hu₂
        exact ⟨embL x₁ ∪ embR u₂, embL x₁ ∪ embR v₂, inrB j, hprev,
          Finset.union_subset_union_right (embR_mono huv₂),
          Finset.union_subset_union_right (embR_mono hv₂x), hfu, hfv⟩
    have hf₂_4 : ∀ x₂ l₂, packF f₂ l₂ x₂ → l₂ ≤ alphaF h x₂ + (e - u) := by
      intro x₂ l₂ hpl₂
      have h1 := hf4 (embL x₁ ∪ embR x₂) (alphaF g x₁ + u + l₂) (happend l₂ x₂ hpl₂)
      rw [alphaF_both, projL_embLR, projR_embLR] at h1
      omega
    exact ⟨u, e - u, by omega, ⟨f₁, hf₁_1, hf₁_2, hf₁_3, hPu⟩, ⟨f₂, hf₂_1, hf₂_2, hf₂_3, hf₂_4⟩⟩
  · rintro ⟨u, v, huv, ⟨f₁, hf₁_1, hf₁_2, hf₁_3, hf₁_4⟩, ⟨f₂, hf₂_1, hf₂_2, hf₂_3, hf₂_4⟩⟩
    let f : Finset (Fin (a + b)) → Fin (a + b) → Bool := fun x k =>
      Fin.addCases (f₁ (projL x)) (f₂ (projR x)) k
    have hf_inl : ∀ x i, f x (inlA i) = f₁ (projL x) i := fun x i => by simp [f, inlA]
    have hf_inr : ∀ x j, f x (inrB j) = f₂ (projR x) j := fun x j => by simp [f, inrB]
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro x k ⟨hnk, hno⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k hnk hno
      · intro hni hnoi
        change f x (inlA i) = true
        rw [hf_inl]
        refine hf₁_1 (projL x) i ⟨fun hm => hni (mem_projL.mp hm), fun i' hi' => ?_⟩
        simpa [bothG, inlA] using hnoi (inlA i') (mem_projL.mp hi')
      · intro hnj hnoj
        change f x (inrB j) = true
        rw [hf_inr]
        refine hf₂_1 (projR x) j ⟨fun hm => hnj (mem_projR.mp hm), fun j' hj' => ?_⟩
        simpa [bothG, inrB] using hnoj (inrB j') (mem_projR.mp hj')
    · intro x k hk
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k hk
      · intro hi; change f x (inlA i) = false; rw [hf_inl]; exact hf₁_2 (projL x) i (mem_projL.mpr hi)
      · intro hj; change f x (inrB j) = false; rw [hf_inr]; exact hf₂_2 (projR x) j (mem_projR.mpr hj)
    · intro x y k hxy hfy
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k hfy
      · intro hfi; change f x (inlA i) = true; rw [hf_inl]
        exact hf₁_3 (projL x) (projL y) i (projL_mono hxy) (by simpa [f] using hfi)
      · intro hfj; change f x (inrB j) = true; rw [hf_inr]
        exact hf₂_3 (projR x) (projR y) j (projR_mono hxy) (by simpa [f] using hfj)
    · have hsplit : ∀ l x, packF f l x →
          ∃ l₁ l₂, l₁ + l₂ = l ∧ packF f₁ l₁ (projL x) ∧ packF f₂ l₂ (projR x) := by
        intro l
        induction l with
        | zero => intro x _; exact ⟨0, 0, rfl, trivial, trivial⟩
        | succ l ih =>
          intro x ⟨ux, vx, k, hux, huvx, hvxx, hfu, hfv⟩
          obtain ⟨l₁, l₂, hsum, hp1, hp2⟩ := ih ux hux
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k hfu hfv
          · intro hfu' hfv'
            simp only [f, Fin.addCases_left] at hfu' hfv'
            exact ⟨l₁ + 1, l₂, by omega,
              ⟨projL ux, projL vx, i, hp1, projL_mono huvx, projL_mono hvxx, hfu', hfv'⟩,
              packF_mono_set f₂ (projR_mono (huvx.trans hvxx)) hp2⟩
          · intro hfu' hfv'
            simp only [f, Fin.addCases_right] at hfu' hfv'
            exact ⟨l₁, l₂ + 1, by omega,
              packF_mono_set f₁ (projL_mono (huvx.trans hvxx)) hp1,
              ⟨projR ux, projR vx, j, hp2, projR_mono huvx, projR_mono hvxx, hfu', hfv'⟩⟩
      intro x l hpl
      obtain ⟨l₁, l₂, hsum, hp1, hp2⟩ := hsplit l x hpl
      have h1 := hf₁_4 (projL x) l₁ hp1
      have h2 := hf₂_4 (projR x) l₂ hp2
      rw [alphaF_both]
      omega

/-! ### Part 2: Cluster Deletion Upper Bound -/

lemma cluster_admits {n : Nat} (g : Fin n → Fin n → Bool) (hgr : graphF n g)
    (D : Finset (Fin n)) (hclust : clusterF g D) :
    admitsF n g D.card := by
  let f : Finset (Fin n) → Fin n → Bool := fun x j =>
    decide (j ∉ x ∧ (j ∈ D ∨ ∀ i ∈ x, i ∉ D → g i j = false))
  let clique : Fin n → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i => i ∉ D ∧ (i = j ∨ g i j = true))
  have hclique_eq : ∀ u v : Fin n, u ∉ D → v ∉ D → g u v = true → clique u = clique v := by
    intro u v hu hv huv
    ext w
    simp only [clique, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, rfl | hwu⟩
      · exact ⟨hw, Or.inr huv⟩
      · exact ⟨hw, hclust w hw u hu v hv hwu huv⟩
    · rintro ⟨hw, rfl | hwv⟩
      · exact ⟨hw, Or.inr (by rw [hgr.2]; exact huv)⟩
      · exact ⟨hw, hclust w hw v hv u hu hwv (by rw [hgr.2]; exact huv)⟩
  let cliquesHit : Finset (Fin n) → Finset (Finset (Fin n)) := fun x =>
    (x \ D).image clique
  have hcliques_le_alpha : ∀ x : Finset (Fin n), (cliquesHit x).card ≤ alphaF g x := by
    intro x
    by_cases hn : n = 0
    · subst hn
      have hx0 : x = ∅ := by ext i; exact Fin.elim0 i
      simp [hx0, cliquesHit]
    · classical
      have hex : ∀ C ∈ cliquesHit x, ∃ u ∈ x \ D, clique u = C := fun C hC =>
        Finset.mem_image.mp hC
      let rep : Finset (Fin n) → Fin n := fun C =>
        if hC : C ∈ cliquesHit x then (hex C hC).choose else ⟨0, Nat.pos_of_ne_zero hn⟩
      let S := (cliquesHit x).image rep
      have hrep_mem : ∀ C (hC : C ∈ cliquesHit x), rep C ∈ x \ D ∧ clique (rep C) = C := by
        intro C hC
        simp only [rep, hC, ↓reduceDIte]
        exact (hex C hC).choose_spec
      have hS_sub : S ⊆ x := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨C, hC, rfl⟩
        exact (Finset.mem_sdiff.mp (hrep_mem C hC).1).1
      have hS_card : S.card = (cliquesHit x).card := by
        refine Finset.card_image_of_injOn ?_
        intro C₁ hC₁ C₂ hC₂ heq
        have h1 := (hrep_mem C₁ hC₁).2
        have h2 := (hrep_mem C₂ hC₂).2
        rw [← h1, ← h2, heq]
      have hS_ind : indepF g S := by
        intro u hu v hv
        rcases Finset.mem_image.mp hu with ⟨C₁, hC₁, rfl⟩
        rcases Finset.mem_image.mp hv with ⟨C₂, hC₂, rfl⟩
        by_contra hne
        have htrue : g (rep C₁) (rep C₂) = true := by cases hgv : g (rep C₁) (rep C₂) <;> simp_all
        have h1 := hrep_mem C₁ hC₁
        have h2 := hrep_mem C₂ hC₂
        have hceq : C₁ = C₂ := by
          rw [← h1.2, ← h2.2]
          exact hclique_eq (rep C₁) (rep C₂)
            (Finset.mem_sdiff.mp h1.1).2 (Finset.mem_sdiff.mp h2.1).2 htrue
        rw [hceq, hgr.1] at htrue
        cases htrue
      rw [← hS_card]
      exact card_le_alphaF g hS_sub hS_ind
  let pot : Finset (Fin n) → Nat := fun x => (x ∩ D).card + (cliquesHit x).card
  have hpot_step : ∀ u v j, u ⊆ v → f u j = true → f v j = false → pot u + 1 ≤ pot v := by
    intro u v j huv hfu hfv
    have hsub1 : u ∩ D ⊆ v ∩ D := Finset.inter_subset_inter_right huv
    have hsub2 : cliquesHit u ⊆ cliquesHit v :=
      Finset.image_subset_image (Finset.sdiff_subset_sdiff huv Finset.Subset.rfl)
    have hle1 : (u ∩ D).card ≤ (v ∩ D).card := Finset.card_le_card hsub1
    have hle2 : (cliquesHit u).card ≤ (cliquesHit v).card := Finset.card_le_card hsub2
    simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at hfu hfv
    by_cases hjD : j ∈ D
    · have hjv : j ∈ v := by
        by_contra hnv
        exact hfv ⟨hnv, Or.inl hjD⟩
      have hss : u ∩ D ⊂ v ∩ D := Finset.ssubset_iff_subset_ne.mpr ⟨hsub1, fun heq => by
        have : j ∈ u ∩ D := by rw [heq]; exact Finset.mem_inter.mpr ⟨hjv, hjD⟩
        exact hfu.1 (Finset.mem_inter.mp this).1⟩
      have hlt1 : (u ∩ D).card < (v ∩ D).card := Finset.card_lt_card hss
      dsimp only [pot]; omega
    · have hnot_u : clique j ∉ cliquesHit u := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨i, hi, heq⟩
        rcases Finset.mem_sdiff.mp hi with ⟨hiu, hiD⟩
        have himem : i ∈ clique j := by
          rw [← heq]; simp [clique, hiD]
        rcases (Finset.mem_filter.mp himem).2.2 with rfl | hgij
        · exact hfu.1 hiu
        · rcases hfu.2 with hcontra | hall
          · exact hjD hcontra
          · have := hall i hiu hiD
            rw [hgij] at this; cases this
      have hin_v : clique j ∈ cliquesHit v := by
        by_cases hjv : j ∈ v
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hjv, hjD⟩, rfl⟩
        · have hex_i : ∃ i ∈ v, i ∉ D ∧ g i j = true := by
            by_contra hnone
            push Not at hnone
            exact hfv ⟨hjv, Or.inr fun i hiv hiD => by
              cases hgv : g i j
              · rfl
              · exact absurd hgv (hnone i hiv hiD)⟩
          rcases hex_i with ⟨i, hiv, hiD, hgij⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hiv, hiD⟩,
            hclique_eq i j hiD hjD hgij⟩
      have hss : cliquesHit u ⊂ cliquesHit v := Finset.ssubset_iff_subset_ne.mpr ⟨hsub2, fun heq => by
        rw [heq] at hnot_u; exact hnot_u hin_v⟩
      have hlt2 : (cliquesHit u).card < (cliquesHit v).card := Finset.card_lt_card hss
      dsimp only [pot]; omega
  have hpot_pack : ∀ l x, packF f l x → l ≤ pot x := by
    intro l
    induction l with
    | zero => intro _ _; omega
    | succ l ih =>
      intro x ⟨u, v, j, hu, huv, hvx, hfu, hfv⟩
      have h1 := ih u hu
      have h2 := hpot_step u v j huv hfu hfv
      have h3 : pot v ≤ pot x := by
        dsimp only [pot, cliquesHit]
        have := Finset.card_le_card (Finset.inter_subset_inter hvx (Finset.Subset.rfl : D ⊆ D))
        have := Finset.card_le_card (Finset.image_subset_image (f := clique)
          (Finset.sdiff_subset_sdiff hvx (Finset.Subset.rfl : D ⊆ D)))
        omega
      omega
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x j ⟨hnj, hno⟩
    simp only [f, decide_eq_true_eq]
    exact ⟨hnj, Or.inr fun i hi _ => hno i hi⟩
  · intro x j hj
    simp [f, hj]
  · intro x y j hxy hfy
    simp only [f, decide_eq_true_eq] at hfy ⊢
    exact ⟨fun hx => hfy.1 (hxy hx), hfy.2.imp id (fun hall i hi hiD => hall i (hxy hi) hiD)⟩
  · intro x l hpl
    have h1 := hpot_pack l x hpl
    have h2 := hcliques_le_alpha x
    have h3 : (x ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
    dsimp only [pot] at h1
    omega

/-! ### Part 3: Induced P₃ Lower Bound & Zero-Slack Characterization -/

lemma p3_lower_bound {n : Nat} (g : Fin n → Fin n → Bool)
    (p e : Nat) (v : Fin p × Fin 3 → Fin n) (hv_inj : Function.Injective v)
    (hv_edge : ∀ x y, g (v x) (v y) =
      decide (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)))
    (hadm : admitsF n g e) : p ≤ e := by
  rcases hadm with ⟨f, hf1, hf2, hf3, hf4⟩
  have hbuild : ∀ k ≤ p, ∃ y : Finset (Fin n),
      (∀ u ∈ y, ∃ r : Fin p, r.val < k ∧ ∃ c : Fin 3, u = v (r, c)) ∧
      packF f (2 * k) y ∧ alphaF g y ≤ k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, by simp, trivial, ?_⟩
      rw [alphaF_empty]
    | succ k ih =>
      intro hkp
      obtain ⟨y, hy_supp, hy_pack, hy_alpha⟩ := ih (by omega)
      let r : Fin p := ⟨k, by omega⟩
      let a := v (r, ⟨0, by decide⟩)
      let b := v (r, ⟨1, by decide⟩)
      let c := v (r, ⟨2, by decide⟩)
      have hab : g a b = true := by simp [a, b, hv_edge]
      have hbc : g b c = true := by simp [b, c, hv_edge]
      have hca : g c a = false := by simp [c, a, hv_edge]
      have hnot_y : ∀ t : Fin 3, v (r, t) ∉ y := by
        intro t hm
        rcases hy_supp _ hm with ⟨r', hr', c', heq⟩
        have hpair := hv_inj heq
        have hr_eq : r = r' := congrArg Prod.fst hpair
        have : r.val = r'.val := congrArg Fin.val hr_eq
        simp only [r] at this
        omega
      have hno_edge : ∀ t : Fin 3, ∀ u ∈ y, g u (v (r, t)) = false := by
        intro t u hu
        rcases hy_supp u hu with ⟨r', hr', c', rfl⟩
        rw [hv_edge, decide_eq_false_iff_not]
        rintro ⟨heq, _⟩
        have : r'.val = r.val := congrArg Fin.val heq
        simp only [r] at this
        omega
      have hsupp_add : ∀ t₁ t₂ : Fin 3, ∀ u ∈ insert (v (r, t₁)) (insert (v (r, t₂)) y),
          ∃ r' : Fin p, r'.val < k + 1 ∧ ∃ c' : Fin 3, u = v (r', c') := by
        intro t₁ t₂ u hu
        rcases Finset.mem_insert.mp hu with rfl | hu2
        · exact ⟨r, by simp [r], t₁, rfl⟩
        · rcases Finset.mem_insert.mp hu2 with rfl | huy
          · exact ⟨r, by simp [r], t₂, rfl⟩
          · rcases hy_supp u huy with ⟨r', hr', c', rfl⟩
            exact ⟨r', by omega, c', rfl⟩
      cases hfba : f (insert b y) a
      · -- Case f (insert b y) a = false: insert c, then insert b (tap a falls!)
        have hfyc : f y c = true := hf1 y c ⟨hnot_y ⟨2, by decide⟩, hno_edge ⟨2, by decide⟩⟩
        have hfcc : f (insert c y) c = false := hf2 (insert c y) c (Finset.mem_insert_self c y)
        have hp1 : packF f (2 * k + 1) (insert c y) :=
          ⟨y, insert c y, c, hy_pack, Finset.subset_insert c y, Finset.Subset.rfl, hfyc, hfcc⟩
        have hne_ac : a ≠ c := fun h => by
          have := congrArg (fun p => p.2.val) (hv_inj h); simp at this
        have hfca : f (insert c y) a = true := by
          refine hf1 (insert c y) a ⟨?_, ?_⟩
          · intro hm
            rcases Finset.mem_insert.mp hm with heq | hay
            · exact hne_ac heq
            · exact hnot_y ⟨0, by decide⟩ hay
          · intro u hu
            rcases Finset.mem_insert.mp hu with rfl | huy
            · exact hca
            · exact hno_edge ⟨0, by decide⟩ u huy
        have hfbca : f (insert b (insert c y)) a = false := by
          cases hval : f (insert b (insert c y)) a
          · rfl
          · have hsub : insert b y ⊆ insert b (insert c y) :=
              Finset.insert_subset_insert b (Finset.subset_insert c y)
            have := hf3 (insert b y) (insert b (insert c y)) a hsub hval
            rw [hfba] at this; cases this
        have hp2 : packF f (2 * (k + 1)) (insert b (insert c y)) :=
          ⟨insert c y, insert b (insert c y), a, hp1, Finset.subset_insert b _, Finset.Subset.rfl,
            hfca, hfbca⟩
        have halpha2 : alphaF g (insert b (insert c y)) ≤ k + 1 :=
          (alphaF_insert_pair_le g y hbc).trans (by omega)
        exact ⟨insert b (insert c y), hsupp_add ⟨1, by decide⟩ ⟨2, by decide⟩, hp2, halpha2⟩
      · -- Case f (insert b y) a = true: insert b, then insert a (tap a falls!)
        have hfyb : f y b = true := hf1 y b ⟨hnot_y ⟨1, by decide⟩, hno_edge ⟨1, by decide⟩⟩
        have hfbb : f (insert b y) b = false := hf2 (insert b y) b (Finset.mem_insert_self b y)
        have hp1 : packF f (2 * k + 1) (insert b y) :=
          ⟨y, insert b y, b, hy_pack, Finset.subset_insert b y, Finset.Subset.rfl, hfyb, hfbb⟩
        have hfaab : f (insert a (insert b y)) a = false :=
          hf2 (insert a (insert b y)) a (Finset.mem_insert_self a _)
        have hp2 : packF f (2 * (k + 1)) (insert a (insert b y)) :=
          ⟨insert b y, insert a (insert b y), a, hp1, Finset.subset_insert a _, Finset.Subset.rfl,
            hfba, hfaab⟩
        have halpha2 : alphaF g (insert a (insert b y)) ≤ k + 1 :=
          (alphaF_insert_pair_le g y hab).trans (by omega)
        exact ⟨insert a (insert b y), hsupp_add ⟨0, by decide⟩ ⟨1, by decide⟩, hp2, halpha2⟩
  obtain ⟨y, _, hpy, hay⟩ := hbuild p le_rfl
  have hle := hf4 y (2 * p) hpy
  omega

lemma admits_zero_iff_cluster_empty {n : Nat} (g : Fin n → Fin n → Bool) (hgr : graphF n g) :
    admitsF n g 0 ↔ clusterF g ∅ := by
  constructor
  · intro hadm
    by_contra hnot
    dsimp only [clusterF] at hnot
    push Not at hnot
    rcases hnot with ⟨i, _, j, _, k, _, hgij, hgjk, hnik, hgik_ne⟩
    have hgik : g i k = false := by cases h : g i k <;> simp_all
    have hnij : i ≠ j := by rintro rfl; rw [hgr.1] at hgij; cases hgij
    have hnjk : j ≠ k := by rintro rfl; rw [hgr.1] at hgjk; cases hgjk
    let v : Fin 1 × Fin 3 → Fin n := fun p =>
      match p.2.val with
      | 0 => i
      | 1 => j
      | _ => k
    have hv_inj : Function.Injective v := by
      intro x y hxy
      rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
      fin_cases x1; fin_cases y1; fin_cases x2 <;> fin_cases y2 <;>
        simp only [v, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Prod.mk.injEq,
          true_and] at hxy ⊢ <;>
        first | rfl | exact absurd hxy hnij | exact absurd hxy.symm hnij | exact absurd hxy hnjk | exact absurd hxy.symm hnjk | exact absurd hxy hnik | exact absurd hxy.symm hnik
    have hv_edge : ∀ x y, g (v x) (v y) =
        decide (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) := by
      intro x y
      rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
      fin_cases x1; fin_cases y1; fin_cases x2 <;> fin_cases y2 <;>
        simp [v, hgr.1, hgij, hgjk, hgik, hgr.2 j i, hgr.2 k j, hgr.2 k i]
    have h1 := p3_lower_bound g 1 0 v hv_inj hv_edge hadm
    omega
  · intro hcl
    simpa using cluster_admits g hgr ∅ hcl

end Core

end PEqualNP.Outside.L_meta_48149

open PEqualNP.Outside.L_meta_48149 in
theorem PEqualNP.Outside.L_meta_48149 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
let graph := fun (n : Nat) (g : Fin n → Fin n → Bool) =>
  (∀ i, g i i = false) ∧ (∀ i j, g i j = g j i)
let admits := fun (n : Nat) (g : Fin n → Fin n → Bool) (e : Nat) =>
  let X := Finset (Fin n)
  let alpha := fun (x : X) =>
    (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup Finset.card
  ∃ f : X → Fin n → Bool,
    (∀ x j, (j ∉ x ∧ ∀ i ∈ x, g i j = false) → f x j = true) ∧
    (∀ x j, j ∈ x → f x j = false) ∧
    (∀ x y j, x ⊆ y → f y j = true → f x j = true) ∧
    let pack := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
      (fun _ prev x => ∃ (u v : X) (j : Fin n),
        prev u ∧ u ⊆ v ∧ v ⊆ x ∧ f u j = true ∧ f v j = false)
    ∀ x l, pack l x → l ≤ alpha x + e
(∀ (a b : Nat) (g : Fin a → Fin a → Bool) (h : Fin b → Fin b → Bool) (e : Nat),
  graph a g → graph b h →
  let both : Fin (a+b) → Fin (a+b) → Bool :=
    Fin.addCases (fun i => Fin.addCases (g i) (fun _ => false))
      (fun j => Fin.addCases (fun _ => false) (h j))
  admits (a+b) both e ↔ ∃ u v : Nat, u+v ≤ e ∧ admits a g u ∧ admits b h v) ∧
∀ (n : Nat) (g : Fin n → Fin n → Bool), graph n g →
  let cluster := fun (D : Finset (Fin n)) =>
    ∀ i ∉ D, ∀ j ∉ D, ∀ k ∉ D,
      g i j = true → g j k = true → i = k ∨ g i k = true
  (∀ D, cluster D → admits n g D.card) ∧
  (∀ (p e : Nat) (v : Fin p × Fin 3 → Fin n), Function.Injective v →
    (∀ x y, g (v x) (v y) =
      decide (x.1 = y.1 ∧ (x.2.val+1 = y.2.val ∨ y.2.val+1 = x.2.val))) →
    admits n g e → p ≤ e) ∧
  (admits n g 0 ↔ cluster ∅) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro graph admits
  have hadmits_iff : ∀ n g e, admits n g e ↔ admitsF n g e := by
    intro n g e
    dsimp only [admits, admitsF]
    have halpha : ∀ x : Finset (Fin n),
        (x.powerset.filter (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup Finset.card =
        alphaF g x := fun x => by
      dsimp only [alphaF]
      congr 1; ext s; simp
    simp only [halpha]
    rfl
  refine ⟨?_, ?_⟩
  · intro a b g h e _ _ both
    have hboth : both = bothG g h := rfl
    rw [hboth, hadmits_iff]
    refine (admits_both_iff a b g h e).trans ?_
    simp only [hadmits_iff]
  · intro n g hgr cluster
    have hgr' : graphF n g := hgr
    have hcl_iff : ∀ D, cluster D ↔ clusterF g D := fun _ => Iff.rfl
    refine ⟨?_, ?_, ?_⟩
    · intro D hD
      rw [hadmits_iff]
      exact cluster_admits g hgr' D hD
    · intro p e v hv_inj hv_edge hadm
      rw [hadmits_iff] at hadm
      refine p3_lower_bound g p e v hv_inj (fun x y => ?_) hadm
      rw [hv_edge x y]
      exact congrArg (@decide _) (Subsingleton.elim _ _)
    · rw [hadmits_iff, hcl_iff]
      exact admits_zero_iff_cluster_empty g hgr'
