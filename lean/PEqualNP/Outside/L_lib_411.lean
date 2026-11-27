import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_411

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

def Sep (k t : ℕ) (F : Fin t → Finset X) : Prop :=
  ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
    ∃ j : Fin t, a ∈ F j ∧ Disjoint (F j) S

def Ex (k t : ℕ) (F : Fin t → Finset X) : Prop :=
  ∀ (R : X → X → Bool) (a : X),
    (((Finset.univ : Finset X).filter (fun u => R u a)).card ≤ k ∨
     ((Finset.univ : Finset X).filter (fun v => R a v)).card ≤ k) →
    (R a a = true ↔ ∀ j : Fin t, a ∈ F j →
      (∃ b ∈ F j, R b a = true) ∧ (∃ c ∈ F j, R a c = true))

theorem ex_iff_sep (k t : ℕ) (F : Fin t → Finset X) : Ex k t F ↔ Sep k t F := by
  constructor
  · intro h a S haS hS
    by_contra hne
    push Not at hne
    let R : X → X → Bool := fun u v => decide ((u = a ∧ v ∈ S) ∨ (u ∈ S ∧ v = a))
    have hfil : (univ.filter (fun u => R u a = true)) = S := by
      ext u
      simp only [R, mem_filter, mem_univ, true_and, decide_eq_true_eq, and_true]
      constructor
      · rintro (⟨-, h2⟩ | h2)
        · exact absurd h2 haS
        · exact h2
      · intro h2; exact Or.inr h2
    have key := (h R a (Or.inl (by rw [hfil]; exact hS))).2 (by
      intro j hj
      obtain ⟨x, hxF, hxS⟩ := Finset.not_disjoint_iff.1 (hne j hj)
      exact ⟨⟨x, hxF, by simp [R, hxS]⟩, ⟨x, hxF, by simp [R, hxS]⟩⟩)
    simp [R, haS] at key
  · intro h R a hdeg
    constructor
    · intro haa j hj
      exact ⟨⟨a, hj, haa⟩, ⟨a, hj, haa⟩⟩
    · intro hall
      by_contra hne
      have hne' : R a a = false := by simpa using hne
      rcases hdeg with hd | hd
      · obtain ⟨j, hj, hdis⟩ := h a _ (by simp [hne']) hd
        obtain ⟨⟨b, hb, hba⟩, -⟩ := hall j hj
        exact Finset.disjoint_left.1 hdis hb (by simp [hba])
      · obtain ⟨j, hj, hdis⟩ := h a _ (by simp [hne']) hd
        obtain ⟨-, ⟨c, hc, hac⟩⟩ := hall j hj
        exact Finset.disjoint_left.1 hdis hc (by simp [hac])

theorem sep_one_iff (t : ℕ) [Nonempty X] :
    (∃ F : Fin t → Finset X, Sep 1 t F) ↔
      0 < t ∧ Fintype.card X ≤ t.choose (t / 2) := by
  constructor
  · rintro ⟨F, hF⟩
    let J : X → Finset (Fin t) := fun a => univ.filter (fun j => a ∈ F j)
    have hne : ∀ a, (J a).Nonempty := by
      intro a
      obtain ⟨j, hj, -⟩ := hF a ∅ (by simp) (by simp)
      exact ⟨j, by simp [J, hj]⟩
    have hsub : ∀ a b, a ≠ b → ¬ J a ⊆ J b := by
      intro a b hab hs
      obtain ⟨j, hj, hdis⟩ := hF a {b} (by simpa using hab) (by simp)
      have hjb : j ∈ J b := hs (by simp [J, hj])
      simp only [J, mem_filter, mem_univ, true_and] at hjb
      exact Finset.disjoint_left.1 hdis hjb (by simp)
    have hinj : Function.Injective J := by
      intro a b hab
      by_contra h
      exact hsub a b h (le_of_eq hab)
    refine ⟨?_, ?_⟩
    · obtain ⟨a⟩ := ‹Nonempty X›
      obtain ⟨j, -⟩ := hne a
      exact lt_of_le_of_lt (Nat.zero_le _) j.isLt
    · have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (univ.image J)) := by
        intro x hx y hy hxy
        simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact hsub a b (fun h => hxy (by rw [h]))
      have hs := hanti.sperner
      rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin] at hs
      exact hs
  · rintro ⟨ht, hc⟩
    let s := t - t / 2
    have hs1 : 1 ≤ s := by omega
    have hcs : (powersetCard s (univ : Finset (Fin t))).card = t.choose (t / 2) := by
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      exact Nat.choose_symm (Nat.div_le_self t 2)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := X) (β := {x // x ∈ powersetCard s (univ : Finset (Fin t))})
      (by rw [Fintype.card_coe, hcs]; exact hc)
    have hcard : ∀ a, ((e a).1).card = s := fun a => (mem_powersetCard.1 (e a).2).2
    refine ⟨fun j => univ.filter (fun a => j ∈ (e a).1), ?_⟩
    intro a S haS hS
    have hj : ∃ j ∈ (e a).1, ∀ x ∈ S, j ∉ (e x).1 := by
      rcases S.eq_empty_or_nonempty with h0 | ⟨b, hb⟩
      · have : ((e a).1).Nonempty := by
          rw [← Finset.card_pos, hcard a]; omega
        obtain ⟨j, hj⟩ := this
        exact ⟨j, hj, by simp [h0]⟩
      · have hall : ∀ x ∈ S, x = b := fun x hx => Finset.card_le_one.1 hS x hx b hb
        have hab : a ≠ b := fun h => haS (h ▸ hb)
        have hns : ¬ (e a).1 ⊆ (e b).1 := by
          intro hsub
          have := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard])
          exact hab (e.injective (Subtype.ext this))
        obtain ⟨j, hja, hjb⟩ := Finset.not_subset.1 hns
        exact ⟨j, hja, fun x hx => by rw [hall x hx]; exact hjb⟩
    obtain ⟨j, hja, hjS⟩ := hj
    refine ⟨j, by simp [hja], ?_⟩
    rw [Finset.disjoint_left]
    intro x hx hxS
    simp only [mem_filter, mem_univ, true_and] at hx
    exact hjS x hxS hx


theorem small_family (k : ℕ) :
    ((univ : Finset (Finset X)).filter (fun S => S.card ≤ k)).card ≤
      (Fintype.card X + 1) ^ k := by
  have hsub : (univ : Finset (Finset X)).filter (fun S => S.card ≤ k) ⊆
      (univ : Finset (Fin k → Option X)).image (fun v => (univ.image v).eraseNone) := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    simp only [mem_image, mem_univ, true_and]
    let e : Fin S.card ≃ S := S.equivFin.symm
    refine ⟨fun i => if h : i.val < S.card then some (e ⟨i.val, h⟩).1 else none, ?_⟩
    ext x
    simp only [mem_eraseNone, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i.val < S.card
      · rw [dif_pos h] at hi
        cases hi
        exact (e ⟨i.val, h⟩).2
      · rw [dif_neg h] at hi
        cases hi
    · intro hx
      refine ⟨⟨(e.symm ⟨x, hx⟩).val, lt_of_lt_of_le (e.symm ⟨x, hx⟩).isLt hS⟩, ?_⟩
      simp only
      rw [dif_pos (e.symm ⟨x, hx⟩).isLt]
      simp
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

theorem hash_exists (k r : ℕ)
    (hr : Fintype.card X * (Fintype.card X + 1) ^ k < 2 ^ r) :
    ∃ h : Fin r → X → Fin (2 * (k + 1)), ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
      ∃ i, ∀ s ∈ S, h i s ≠ h i a := by
  set B := 2 * (k + 1) with hB
  set N := Fintype.card X with hN
  by_contra hno
  push Not at hno
  let T := (univ : Finset (Finset X)).filter (fun S => S.card ≤ k)
  let P := ((univ : Finset X) ×ˢ T).filter (fun p => p.1 ∉ p.2)
  let G : X → Finset X → Finset (X → Fin B) := fun a S =>
    univ.filter (fun g => ∃ s ∈ S, g s = g a)
  let Bad : X × Finset X → Finset (Fin r → X → Fin B) := fun p =>
    Fintype.piFinset (fun _ => G p.1 p.2)
  have hcover : (univ : Finset (Fin r → X → Fin B)) ⊆ P.biUnion Bad := by
    intro h _
    obtain ⟨a, S, haS, hS, hall⟩ := hno h
    simp only [mem_biUnion]
    refine ⟨(a, S), ?_, ?_⟩
    · simp [P, T, haS, hS]
    · simp only [Bad, G, Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
      exact hall
  have hGs : ∀ a s : X, a ≠ s →
      (univ.filter (fun g : X → Fin B => g s = g a)).card * B ≤ B ^ N := by
    intro a s has
    have := Finset.card_le_card_of_injOn (s := (univ.filter (fun g : X → Fin B => g s = g a)) ×ˢ
        (univ : Finset (Fin B))) (t := (univ : Finset (X → Fin B)))
      (fun p => Function.update p.1 s p.2) (fun _ _ => mem_coe.2 (mem_univ _)) (by
        rintro ⟨g, c⟩ hg ⟨g', c'⟩ hg' heq
        simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_setOf_eq,
          coe_univ, Set.mem_univ, and_true] at hg hg'
        simp only at heq
        have hc : c = c' := by
          have := congrFun heq s
          simpa using this
        subst hc
        have hga : g a = g' a := by
          have := congrFun heq a
          simpa [Function.update_of_ne has] using this
        congr 1
        funext x
        by_cases hx : x = s
        · subst hx; rw [hg, hg', hga]
        · have := congrFun heq x
          simpa [Function.update_of_ne hx] using this)
    simpa [card_product] using this
  have hG : ∀ a S, a ∉ S → S.card ≤ k → (G a S).card * B ≤ k * B ^ N := by
    intro a S haS hS
    have h1 : G a S ⊆ S.biUnion (fun s => univ.filter (fun g : X → Fin B => g s = g a)) := by
      intro g hg
      simp only [G, mem_filter, mem_univ, true_and] at hg
      obtain ⟨s, hs, hgs⟩ := hg
      simp only [mem_biUnion, mem_filter, mem_univ, true_and]
      exact ⟨s, hs, hgs⟩
    calc (G a S).card * B
        ≤ (∑ s ∈ S, (univ.filter (fun g : X → Fin B => g s = g a)).card) * B :=
          Nat.mul_le_mul_right _ ((card_le_card h1).trans card_biUnion_le)
      _ = ∑ s ∈ S, (univ.filter (fun g : X → Fin B => g s = g a)).card * B := by
          rw [Finset.sum_mul]
      _ ≤ ∑ s ∈ S, B ^ N := Finset.sum_le_sum (fun s hs =>
          hGs a s (fun h => haS (h ▸ hs)))
      _ = S.card * B ^ N := by rw [sum_const, smul_eq_mul]
      _ ≤ k * B ^ N := Nat.mul_le_mul_right _ hS
  have hBad : ∀ p ∈ P, B ^ r * (Bad p).card ≤ k ^ r * (B ^ N) ^ r := by
    intro p hp
    simp only [P, T, mem_filter, mem_product, mem_univ, true_and] at hp
    simp only [Bad, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    rw [← mul_pow, ← mul_pow, mul_comm]
    exact Nat.pow_le_pow_left (hG p.1 p.2 hp.2 hp.1) r
  have hPc : P.card ≤ N * (N + 1) ^ k := by
    calc P.card ≤ ((univ : Finset X) ×ˢ T).card := card_filter_le _ _
      _ = N * T.card := by rw [card_product, card_univ]
      _ ≤ N * (N + 1) ^ k := Nat.mul_le_mul_left _ (small_family k)
  have htot : (B ^ N) ^ r ≤ ∑ p ∈ P, (Bad p).card := by
    have := (card_le_card hcover).trans card_biUnion_le
    simpa [card_univ, Fintype.card_fun, Fintype.card_fin] using this
  have hmain : B ^ r * (B ^ N) ^ r ≤ P.card * (k ^ r * (B ^ N) ^ r) := by
    calc B ^ r * (B ^ N) ^ r ≤ B ^ r * ∑ p ∈ P, (Bad p).card := Nat.mul_le_mul_left _ htot
      _ = ∑ p ∈ P, B ^ r * (Bad p).card := by rw [mul_sum]
      _ ≤ ∑ p ∈ P, k ^ r * (B ^ N) ^ r := sum_le_sum hBad
      _ = P.card * (k ^ r * (B ^ N) ^ r) := by rw [sum_const, smul_eq_mul]
  have hpos : 0 < (B ^ N) ^ r := by positivity
  have h2 : B ^ r ≤ P.card * k ^ r := by
    rw [← mul_assoc] at hmain
    exact Nat.le_of_mul_le_mul_right hmain hpos
  have h3 : P.card * k ^ r < B ^ r := by
    rw [hB, mul_pow]
    calc P.card * k ^ r ≤ P.card * (k + 1) ^ r :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) r)
      _ < 2 ^ r * (k + 1) ^ r :=
          Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_lt hPc hr) le_rfl (by positivity)
  omega

theorem exists_exact (k : ℕ) (w : ℕ) (hX : Fintype.card X = 2 ^ w) :
    ∃ (t : ℕ) (F : Fin t → Finset X),
      t ≤ min (2 ^ w) (2 * (k + 1) * ((k + 1) * (w + 1) + 1)) ∧ Sep k t F := by
  by_cases hsmall : 2 ^ w ≤ 2 * (k + 1) * ((k + 1) * (w + 1) + 1)
  · let eq : Fin (2 ^ w) ≃ X := (Fintype.equivFinOfCardEq hX).symm
    refine ⟨2 ^ w, fun j => {eq j}, le_min le_rfl hsmall, ?_⟩
    intro a S haS _
    refine ⟨eq.symm a, by simp, ?_⟩
    simpa using haS
  · set r := (k + 1) * (w + 1) + 1 with hr
    have hb : Fintype.card X * (Fintype.card X + 1) ^ k < 2 ^ r := by
      rw [hX]
      have h1 : 2 ^ w + 1 ≤ 2 ^ (w + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := w); omega
      calc 2 ^ w * (2 ^ w + 1) ^ k ≤ 2 ^ w * (2 ^ (w + 1)) ^ k :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k)
        _ = 2 ^ (w + (w + 1) * k) := by rw [← pow_mul, ← pow_add]
        _ < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by rw [hr]; nlinarith)
    obtain ⟨h, hh⟩ := hash_exists k r hb
    let e : Fin (2 * (k + 1)) × Fin r ≃ Fin (2 * (k + 1) * r) := finProdFinEquiv
    refine ⟨2 * (k + 1) * r, fun j => univ.filter (fun x => h (e.symm j).2 x = (e.symm j).1),
      le_min (by omega) le_rfl, ?_⟩
    intro a S haS hS
    obtain ⟨i, hi⟩ := hh a S haS hS
    refine ⟨e (h i a, i), by simp, ?_⟩
    rw [Finset.disjoint_left]
    intro x hx hxS
    simp only [Equiv.symm_apply_apply, mem_filter, mem_univ, true_and] at hx
    exact hi x hxS hx

end PEqualNP.Outside.L_lib_411

open PEqualNP.Outside.L_lib_411 in
theorem PEqualNP.Outside.L_lib_411 : 
    ∀ w : ℕ,
      let X := Fin w → Bool
      let separates := fun (k t : ℕ) (F : Fin t → Finset X) =>
        ∀ (a : X) (S : Finset X), a ∉ S → S.card ≤ k →
          ∃ j : Fin t, a ∈ F j ∧ Disjoint (F j) S
      let exact := fun (k t : ℕ) (F : Fin t → Finset X) =>
        ∀ (R : X → X → Bool) (a : X),
          (((Finset.univ : Finset X).filter (fun u => R u a)).card ≤ k ∨
           ((Finset.univ : Finset X).filter (fun v => R a v)).card ≤ k) →
          (R a a = true ↔ ∀ j : Fin t, a ∈ F j →
            (∃ b ∈ F j, R b a = true) ∧ (∃ c ∈ F j, R a c = true))
      (∀ k t : ℕ, ∀ F : Fin t → Finset X, exact k t F ↔ separates k t F) ∧
        (∀ k : ℕ, ∃ (t : ℕ) (F : Fin t → Finset X),
          t ≤ min (2 ^ w) (2 * (k + 1) * ((k + 1) * (w + 1) + 1)) ∧ exact k t F) ∧
        ∀ t : ℕ, (∃ F : Fin t → Finset X, exact 1 t F) ↔
          0 < t ∧ 2 ^ w ≤ t.choose (t / 2) := by
  intro w X separates exact
  have hX : Fintype.card X = 2 ^ w := by simp [X]
  refine ⟨fun k t F => ex_iff_sep (X := X) k t F, fun k => ?_, fun t => ?_⟩
  · obtain ⟨t, F, ht, hF⟩ := exists_exact (X := X) k w hX
    exact ⟨t, F, ht, (ex_iff_sep k t F).2 hF⟩
  · have h1 := sep_one_iff (X := X) t
    rw [hX] at h1
    rw [← h1]
    exact ⟨fun ⟨F, hF⟩ => ⟨F, (ex_iff_sep 1 t F).1 hF⟩, fun ⟨F, hF⟩ => ⟨F, (ex_iff_sep 1 t F).2 hF⟩⟩
