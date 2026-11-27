import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_733

private lemma sum_two_pow_lt_two (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (1 : ℚ) / 2 ^ k) < 2 := by
  have h : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / 2 ^ k) = 2 - 1 / 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hne : (2 : ℚ) ^ n ≠ 0 := by positivity
      field_simp
      ring
  rw [h N]
  have hpos : (0 : ℚ) < 1 / 2 ^ N := by positivity
  linarith

private lemma sum_inj_dyadic_lt_two {s : ℕ} (root : Fin s → ℕ) (hinj : Function.Injective root) :
    (∑ j : Fin s, (1 : ℚ) / 2 ^ (root j)) < 2 := by
  let S : Finset ℕ := Finset.univ.image root
  have h1 : (∑ j : Fin s, (1 : ℚ) / 2 ^ (root j)) = ∑ k ∈ S, (1 : ℚ) / 2 ^ k := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [h1]
  let N : ℕ := S.sup id
  have hsub : S ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_range]
    have hle : k ≤ N := Finset.le_sup (f := id) hk
    omega
  have hle_sum : (∑ k ∈ S, (1 : ℚ) / 2 ^ k) ≤ ∑ k ∈ Finset.range (N + 1), (1 : ℚ) / 2 ^ k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    positivity
  exact lt_of_le_of_lt hle_sum (sum_two_pow_lt_two N)

private lemma sum_two_pow_mod_two (S : Finset ℕ) :
    (∑ x ∈ S, 2 ^ x) % 2 = if 0 ∈ S then 1 else 0 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : 0 ∉ s := ha
      simp [h0] at ih
      simp
      omega
    · have h2 : 2 ∣ 2 ^ a := dvd_pow_self 2 ha0
      obtain ⟨q, hq⟩ := h2
      rw [hq]
      have hmem : (0 ∈ Finset.cons a s ha) ↔ 0 ∈ s := by
        simp [Ne.symm ha0]
      simp only [hmem]
      omega

private lemma eq_of_sum_two_pow_eq :
    ∀ n : ℕ, ∀ S T : Finset ℕ, (∑ x ∈ S, 2 ^ x) = n → (∑ y ∈ T, 2 ^ y) = n → S = T := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro S T hS hT
    by_cases hn : n = 0
    · subst hn
      have hSe : S = ∅ := by
        by_contra hne
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
        have hle : 2 ^ a ≤ ∑ x ∈ S, 2 ^ x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
        omega
      have hTe : T = ∅ := by
        by_contra hne
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
        have hle : 2 ^ a ≤ ∑ y ∈ T, 2 ^ y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
        omega
      rw [hSe, hTe]
    · have h0 : 0 ∈ S ↔ 0 ∈ T := by
        have h1 := sum_two_pow_mod_two S
        have h2 := sum_two_pow_mod_two T
        rw [hS] at h1
        rw [hT] at h2
        split_ifs at h1 h2 with hs ht ht <;> simp_all
      let S1 := S.erase 0
      let T1 := T.erase 0
      have hS1_eq : ∑ x ∈ S1, 2 ^ x = ∑ y ∈ T1, 2 ^ y := by
        by_cases h0s : 0 ∈ S
        · have h0t : 0 ∈ T := h0.mp h0s
          have hs' := Finset.add_sum_erase S (fun x => 2 ^ x) h0s
          have ht' := Finset.add_sum_erase T (fun y => 2 ^ y) h0t
          simp only [pow_zero] at hs' ht'
          change ∑ x ∈ S.erase 0, 2 ^ x = ∑ y ∈ T.erase 0, 2 ^ y
          omega
        · have h0t : 0 ∉ T := fun h => h0s (h0.mpr h)
          simp only [S1, T1, Finset.erase_eq_of_notMem h0s, Finset.erase_eq_of_notMem h0t, hS, hT]
      let S2 := S1.image (fun x => x - 1)
      let T2 := T1.image (fun y => y - 1)
      have hS1_sum : ∑ x ∈ S1, 2 ^ x = 2 * ∑ x ∈ S2, 2 ^ x := by
        rw [Finset.mul_sum, Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have : x = (x - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        · intro a ha b hb hab
          dsimp only at hab
          have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
          have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
          omega
      have hT1_sum : ∑ y ∈ T1, 2 ^ y = 2 * ∑ y ∈ T2, 2 ^ y := by
        rw [Finset.mul_sum, Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro y hy
          have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
          have : y = (y - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        · intro a ha b hb hab
          dsimp only at hab
          have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
          have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
          omega
      have h2eq : ∑ x ∈ S2, 2 ^ x = ∑ y ∈ T2, 2 ^ y := by omega
      have hle_n : ∑ x ∈ S1, 2 ^ x ≤ n := by
        rw [← hS]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 S) (fun _ _ _ => Nat.zero_le _)
      have hlt : ∑ x ∈ S2, 2 ^ x < n := by omega
      have hS2T2 : S2 = T2 := ih (∑ x ∈ S2, 2 ^ x) hlt S2 T2 rfl h2eq.symm
      ext a
      by_cases ha0 : a = 0
      · subst ha0; exact h0
      · have hmemS : a ∈ S ↔ a - 1 ∈ S2 := by
          simp only [S2, S1, Finset.mem_image, Finset.mem_erase]
          constructor
          · intro ha; exact ⟨a, ⟨ha0, ha⟩, rfl⟩
          · rintro ⟨b, ⟨hb0, hb⟩, hba⟩
            have : a = b := by omega
            subst this; exact hb
        have hmemT : a ∈ T ↔ a - 1 ∈ T2 := by
          simp only [T2, T1, Finset.mem_image, Finset.mem_erase]
          constructor
          · intro ha; exact ⟨a, ⟨ha0, ha⟩, rfl⟩
          · rintro ⟨b, ⟨hb0, hb⟩, hba⟩
            have : a = b := by omega
            subst this; exact hb
        rw [hmemS, hmemT, hS2T2]

private lemma eq_of_sum_inv_two_pow_eq (A B : Finset ℕ)
    (h : (∑ a ∈ A, (1 : ℚ) / 2 ^ a) = ∑ b ∈ B, (1 : ℚ) / 2 ^ b) : A = B := by
  let M : ℕ := (A ∪ B).sup id
  have hA : ∀ a ∈ A, a ≤ M := fun a ha => Finset.le_sup (f := id) (Finset.mem_union_left B ha)
  have hB : ∀ b ∈ B, b ≤ M := fun b hb => Finset.le_sup (f := id) (Finset.mem_union_right A hb)
  have hmul : (2 : ℚ) ^ M * (∑ a ∈ A, (1 : ℚ) / 2 ^ a) = (2 : ℚ) ^ M * (∑ b ∈ B, (1 : ℚ) / 2 ^ b) :=
    congrArg (fun z => (2 : ℚ) ^ M * z) h
  rw [Finset.mul_sum, Finset.mul_sum] at hmul
  have h1 : (∑ a ∈ A, (2 : ℚ) ^ M * ((1 : ℚ) / 2 ^ a)) = ∑ a ∈ A, ((2 ^ (M - a) : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hle := hA a ha
    have hne : (2 : ℚ) ^ a ≠ 0 := by positivity
    push_cast
    rw [mul_one_div, div_eq_iff hne, ← pow_add, Nat.sub_add_cancel hle]
  have h2 : (∑ b ∈ B, (2 : ℚ) ^ M * ((1 : ℚ) / 2 ^ b)) = ∑ b ∈ B, ((2 ^ (M - b) : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro b hb
    have hle := hB b hb
    have hne : (2 : ℚ) ^ b ≠ 0 := by positivity
    push_cast
    rw [mul_one_div, div_eq_iff hne, ← pow_add, Nat.sub_add_cancel hle]
  rw [h1, h2] at hmul
  have hnat : (∑ a ∈ A, 2 ^ (M - a)) = ∑ b ∈ B, 2 ^ (M - b) := by
    exact_mod_cast hmul
  let A' := A.image (fun a => M - a)
  let B' := B.image (fun b => M - b)
  have hA' : ∑ x ∈ A', 2 ^ x = ∑ a ∈ A, 2 ^ (M - a) := by
    apply Finset.sum_image
    intro x hx y hy hxy
    dsimp only at hxy
    have hxM := hA x hx
    have hyM := hA y hy
    omega
  have hB' : ∑ y ∈ B', 2 ^ y = ∑ b ∈ B, 2 ^ (M - b) := by
    apply Finset.sum_image
    intro x hx y hy hxy
    dsimp only at hxy
    have hxM := hB x hx
    have hyM := hB y hy
    omega
  have hAB' : A' = B' := eq_of_sum_two_pow_eq (∑ x ∈ A', 2 ^ x) A' B' rfl (by rw [hA', hB', hnat])
  ext x
  constructor
  · intro hx
    have hx' : M - x ∈ B' := by
      rw [← hAB']
      exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
    have hxM := hA x hx
    have hyM := hB y hy
    have : x = y := by omega
    subst this; exact hy
  · intro hx
    have hx' : M - x ∈ A' := by
      rw [hAB']
      exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
    have hxM := hB x hx
    have hyM := hA y hy
    have : x = y := by omega
    subst this; exact hy

private structure Block (m : ℕ) (leaf : Fin m → ℕ) where
  depth : ℕ
  verts : Finset (Fin m)
  nonempty : verts.Nonempty
  depth_le : ∀ i ∈ verts, depth ≤ leaf i
  off_le : ∀ i ∈ verts, leaf i - depth ≤ verts.card - 1
  weight_eq : (∑ i ∈ verts, 2 ^ (m - (leaf i - depth))) = 2 ^ m

private def ValidState {m : ℕ} {leaf : Fin m → ℕ} (bs : List (Block m leaf)) : Prop :=
  (∀ i : Fin m, ∃ p ∈ bs, i ∈ p.verts) ∧
  bs.Pairwise (fun p q => Disjoint p.verts q.verts)

private lemma sum_list_dyadic_lt_two_of_eq {m : ℕ} {leaf : Fin m → ℕ} (bs : List (Block m leaf))
    (hsum : (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum < 2)
    {i j : ℕ} (hi : i < bs.length) (hj : j < bs.length) (hij : i < j)
    (heq : bs[i].depth = bs[j].depth) : 1 ≤ bs[i].depth := by
  by_contra hlt
  have h0 : bs[i].depth = 0 := by omega
  have h0j : bs[j].depth = 0 := by omega
  have hge : ∀ (l : List ℚ), (∀ x ∈ l, 0 ≤ x) → ∀ (a b : ℕ) (ha : a < l.length) (hb : b < l.length),
      a < b → l[a] + l[b] ≤ l.sum := by
    intro l
    induction l with
    | nil => intro _ a b ha; simp at ha
    | cons x xs ih =>
      intro hnn a b ha hb hab
      have hnn_xs : ∀ y ∈ xs, 0 ≤ y := fun y hy => hnn y (List.mem_cons_of_mem x hy)
      have hxs_nn : 0 ≤ xs.sum := List.sum_nonneg hnn_xs
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.sum_cons]
          have hb' : b' < xs.length := by simpa using hb
          have h1 : xs[b'] ≤ xs.sum := List.single_le_sum hnn_xs xs[b'] (List.getElem_mem hb')
          linarith
      | succ a' =>
        cases b with
        | zero => omega
        | succ b' =>
          simp only [List.getElem_cons_succ, List.sum_cons]
          have ha' : a' < xs.length := by simpa using ha
          have hb' : b' < xs.length := by simpa using hb
          have hsub := ih hnn_xs a' b' ha' hb' (by omega)
          have hx : 0 ≤ x := hnn x List.mem_cons_self
          linarith
  let l := bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)
  have hnn : ∀ x ∈ l, 0 ≤ x := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    positivity
  have hle := hge l hnn i j (by simpa [l] using hi) (by simpa [l] using hj) hij
  simp only [l, List.getElem_map, h0, h0j, pow_zero, div_one] at hle
  linarith

private lemma merge_blocks {m : ℕ} {leaf : Fin m → ℕ}
    (p q : Block m leaf) (hdisj : Disjoint p.verts q.verts)
    (hdepth : p.depth = q.depth) (hpos : 1 ≤ p.depth) :
    ∃ r : Block m leaf,
      r.depth = p.depth - 1 ∧
      r.verts = p.verts ∪ q.verts ∧
      (1 : ℚ) / 2 ^ r.depth = (1 : ℚ) / 2 ^ p.depth + (1 : ℚ) / 2 ^ q.depth := by
  have hcard : (p.verts ∪ q.verts).card = p.verts.card + q.verts.card :=
    Finset.card_union_of_disjoint hdisj
  have hpc : 1 ≤ p.verts.card := Finset.card_pos.mpr p.nonempty
  have hqc : 1 ≤ q.verts.card := Finset.card_pos.mpr q.nonempty
  have hcm : (p.verts ∪ q.verts).card ≤ m := by
    calc (p.verts ∪ q.verts).card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
    _ = m := by simp
  have hdl : ∀ i ∈ p.verts ∪ q.verts, p.depth - 1 ≤ leaf i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hq
    · have := p.depth_le i hp; omega
    · have := q.depth_le i hq; omega
  have hol : ∀ i ∈ p.verts ∪ q.verts, leaf i - (p.depth - 1) ≤ (p.verts ∪ q.verts).card - 1 := by
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hq
    · have := p.depth_le i hp
      have := p.off_le i hp
      omega
    · have := q.depth_le i hq
      have := q.off_le i hq
      omega
  have hw : (∑ i ∈ p.verts ∪ q.verts, 2 ^ (m - (leaf i - (p.depth - 1)))) = 2 ^ m := by
    have h2 : 2 * (∑ i ∈ p.verts ∪ q.verts, 2 ^ (m - (leaf i - (p.depth - 1)))) = 2 * 2 ^ m := by
      rw [Finset.sum_union hdisj, mul_add, Finset.mul_sum, Finset.mul_sum]
      have hsp : (∑ i ∈ p.verts, 2 * 2 ^ (m - (leaf i - (p.depth - 1)))) = 2 ^ m := by
        rw [← p.weight_eq]
        apply Finset.sum_congr rfl
        intro i hi
        have h1 := p.depth_le i hi
        have h2 := p.off_le i hi
        have h3 : m - (leaf i - p.depth) = (m - (leaf i - (p.depth - 1))) + 1 := by omega
        rw [h3, pow_succ']
      have hsq : (∑ i ∈ q.verts, 2 * 2 ^ (m - (leaf i - (p.depth - 1)))) = 2 ^ m := by
        rw [← q.weight_eq]
        apply Finset.sum_congr rfl
        intro i hi
        have h1 := q.depth_le i hi
        have h2 := q.off_le i hi
        have h3 : m - (leaf i - q.depth) = (m - (leaf i - (p.depth - 1))) + 1 := by omega
        rw [h3, pow_succ']
      rw [hsp, hsq]; ring
    omega
  refine ⟨⟨p.depth - 1, p.verts ∪ q.verts, p.nonempty.mono Finset.subset_union_left, hdl, hol, hw⟩, rfl, rfl, ?_⟩
  rw [← hdepth]
  have hd : p.depth = (p.depth - 1) + 1 := by omega
  have hne : (2 : ℚ) ^ (p.depth - 1) ≠ 0 := by positivity
  conv_rhs => rw [hd, pow_succ]
  field_simp
  ring

private lemma list_extract_pair {α : Type*} (l : List α) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    ∃ (rest : List α),
      rest.length + 2 = l.length ∧
      (∀ x, x ∈ l ↔ x = l[i] ∨ x = l[j] ∨ x ∈ rest) ∧
      (∀ (f : α → ℚ), (l.map f).sum = f l[i] + f l[j] + (rest.map f).sum) ∧
      (∀ (R : α → α → Prop), (∀ a b, R a b → R b a) → l.Pairwise R →
        R l[i] l[j] ∧ rest.Pairwise R ∧ (∀ z ∈ rest, R l[i] z ∧ R l[j] z)) := by
  let a := l[i]
  let b := l[j]
  let p1 := l.take i
  let p2 := (l.drop (i + 1)).take (j - i - 1)
  let p3 := l.drop (j + 1)
  have hsplit : l = p1 ++ a :: p2 ++ b :: p3 := by
    have h1 : l = l.take i ++ l[i] :: l.drop (i + 1) := by
      have := List.take_append_drop i l
      rw [List.drop_eq_getElem_cons hi] at this
      exact this.symm
    have hj' : j - i - 1 < (l.drop (i + 1)).length := by simp; omega
    have h2 : l.drop (i + 1) = p2 ++ l[j] :: p3 := by
      have := List.take_append_drop (j - i - 1) (l.drop (i + 1))
      rw [List.drop_eq_getElem_cons hj'] at this
      have hidx : (l.drop (i + 1))[j - i - 1] = l[j] := by
        rw [List.getElem_drop]
        congr 1; omega
      have hdrop : (l.drop (i + 1)).drop (j - i - 1 + 1) = p3 := by
        rw [List.drop_drop]
        congr 1; omega
      rw [hidx, hdrop] at this
      exact this.symm
    rw [h1, h2]
    simp only [p1, a, b, List.append_assoc, List.cons_append]
  refine ⟨p1 ++ p2 ++ p3, ?_, ?_, ?_, ?_⟩
  · have hl := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons] at hl ⊢
    omega
  · intro x
    conv_lhs => rw [hsplit]
    simp only [List.mem_append, List.mem_cons]
    tauto
  · intro f
    conv_lhs => rw [hsplit]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  · intro R hsym hpw
    rw [hsplit] at hpw
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_append, List.mem_cons] at hpw
    rcases hpw with ⟨⟨hp1, ⟨ha_p2, hp2⟩, hp1_ap2⟩, ⟨hb_p3, hp3⟩, hleft_bp3⟩
    have hab : R a b := (hleft_bp3 a (Or.inr (Or.inl rfl))) b (Or.inl rfl)
    refine ⟨hab, ?_, ?_⟩
    · simp only [List.pairwise_append, List.mem_append]
      refine ⟨⟨hp1, hp2, fun x hx y hy => hp1_ap2 x hx y (Or.inr hy)⟩, hp3, ?_⟩
      rintro x (hx | hx) y hy
      · exact hleft_bp3 x (Or.inl hx) y (Or.inr hy)
      · exact hleft_bp3 x (Or.inr (Or.inr hx)) y (Or.inr hy)
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with (hz | hz) | hz
      · exact ⟨hsym _ _ (hp1_ap2 z hz a (Or.inl rfl)), hsym _ _ (hleft_bp3 z (Or.inl hz) b (Or.inl rfl))⟩
      · exact ⟨ha_p2 z hz, hsym _ _ (hleft_bp3 z (Or.inr (Or.inr hz)) b (Or.inl rfl))⟩
      · exact ⟨hleft_bp3 a (Or.inr (Or.inl rfl)) z (Or.inr hz), hb_p3 z hz⟩

private lemma reduce_to_nodup {m : ℕ} {leaf : Fin m → ℕ} :
    ∀ k : ℕ, ∀ bs : List (Block m leaf), bs.length = k →
      ValidState bs →
      (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum < 2 →
      ∃ bs' : List (Block m leaf),
        ValidState bs' ∧
        (bs'.map (fun b => b.depth)).Nodup ∧
        (bs'.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum =
          (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro bs hlen hval hlt
    by_cases hnd : (bs.map (fun b => b.depth)).Nodup
    · exact ⟨bs, hval, hnd, rfl⟩
    · have hex : ∃ i j : ℕ, ∃ hi : i < bs.length, ∃ hj : j < bs.length, i < j ∧ bs[i].depth = bs[j].depth := by
        by_contra hnone
        apply hnd
        rw [List.nodup_iff_injective_getElem]
        intro i j heq
        have hi : i.val < bs.length := by simpa using i.isLt
        have hj : j.val < bs.length := by simpa using j.isLt
        have hdeq : bs[i.val].depth = bs[j.val].depth := by simpa using heq
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt_ij | hgt_ij
        · exact hnone ⟨i.val, j.val, hi, hj, hlt_ij, hdeq⟩
        · exact hnone ⟨j.val, i.val, hj, hi, hgt_ij, hdeq.symm⟩
      obtain ⟨i, j, hi, hj, hij, hdeq⟩ := hex
      have hpos : 1 ≤ bs[i].depth := sum_list_dyadic_lt_two_of_eq bs hlt hi hj hij hdeq
      obtain ⟨rest, hrest_len, hrest_mem, hrest_sum, hrest_pw⟩ := list_extract_pair bs hi hj hij
      obtain ⟨hdisj_ij, hpw_rest, hdisj_rest⟩ :=
        hrest_pw (fun p q => Disjoint p.verts q.verts) (fun _ _ h => h.symm) hval.2
      obtain ⟨r, hr_depth, hr_verts, hr_sum⟩ := merge_blocks bs[i] bs[j] hdisj_ij hdeq hpos
      let bs1 : List (Block m leaf) := r :: rest
      have hlen1 : bs1.length < k := by simp only [bs1, List.length_cons]; omega
      have hval1 : ValidState bs1 := by
        constructor
        · intro x
          obtain ⟨p, hp, hxp⟩ := hval.1 x
          rw [hrest_mem] at hp
          rcases hp with rfl | rfl | hpr
          · exact ⟨r, List.mem_cons_self, by rw [hr_verts]; exact Finset.mem_union_left _ hxp⟩
          · exact ⟨r, List.mem_cons_self, by rw [hr_verts]; exact Finset.mem_union_right _ hxp⟩
          · exact ⟨p, List.mem_cons_of_mem _ hpr, hxp⟩
        · rw [List.pairwise_cons]
          refine ⟨fun z hz => ?_, hpw_rest⟩
          rw [hr_verts]
          exact Finset.disjoint_union_left.mpr (hdisj_rest z hz)
      have hsum1 : (bs1.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum =
          (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum := by
        simp only [bs1, List.map_cons, List.sum_cons]
        rw [hrest_sum (fun b => (1 : ℚ) / 2 ^ b.depth), hr_sum]
      obtain ⟨bs', hval', hnd', hsum'⟩ := ih bs1.length hlen1 bs1 rfl hval1 (by rw [hsum1]; exact hlt)
      exact ⟨bs', hval', hnd', by rw [hsum', hsum1]⟩

end PEqualNP.Outside.L_lib_733

theorem PEqualNP.Outside.L_lib_733 : ∀ (m s : ℕ) (leaf : Fin m → ℕ) (root : Fin s → ℕ), Function.Injective root →
  (((∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i)) =
    ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j)) ↔
    ∃ (group : Fin m → Fin s) (offset : Fin m → Fin m),
      (∀ i, leaf i = root (group i) + (offset i).val) ∧
      ∀ j : Fin s,
        (∑ i ∈ (Finset.univ.filter (fun k : Fin m => group k = j)),
          2 ^ (m - (offset i).val) : ℕ) = 2 ^ m) := by
  intro m s leaf root hinj
  constructor
  · intro heq
    by_cases hm : m = 0
    · subst hm
      have hs0 : s = 0 := by
        by_contra hne
        have hpos : (0 : ℚ) < ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j) := by
          apply Finset.sum_pos
          · intro j _; positivity
          · exact ⟨⟨0, Nat.pos_of_ne_zero hne⟩, Finset.mem_univ _⟩
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
        linarith
      subst hs0
      exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩
    · let init : List (PEqualNP.Outside.L_lib_733.Block m leaf) :=
        (List.finRange m).map (fun i =>
          ⟨leaf i, {i}, Finset.singleton_nonempty i,
           fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; exact le_rfl,
           fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; simp,
           by simp⟩)
      have hval0 : PEqualNP.Outside.L_lib_733.ValidState init := by
        constructor
        · intro i
          refine ⟨⟨leaf i, {i}, Finset.singleton_nonempty i,
            fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; exact le_rfl,
            fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; simp,
            by simp⟩, ?_, Finset.mem_singleton_self i⟩
          exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
        · rw [List.pairwise_map]
          have hnd : (List.finRange m).Nodup := List.nodup_finRange m
          rw [List.nodup_iff_pairwise_ne] at hnd
          exact hnd.imp (fun {a b} hab => Finset.disjoint_singleton.mpr hab)
      have hsum0 : (init.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum =
          ∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i) := by
        simp only [init, List.map_map, Function.comp_def]
        have htf : (List.finRange m).toFinset = (Finset.univ : Finset (Fin m)) := by
          ext i; simp
        rw [← htf, List.sum_toFinset _ (List.nodup_finRange m)]
      have hlt0 : (init.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum < 2 := by
        rw [hsum0, heq]
        exact PEqualNP.Outside.L_lib_733.sum_inj_dyadic_lt_two root hinj
      obtain ⟨bs, hval, hnd, hsum_bs⟩ :=
        PEqualNP.Outside.L_lib_733.reduce_to_nodup init.length init rfl hval0 hlt0
      let A : Finset ℕ := (bs.map (fun b => b.depth)).toFinset
      let B : Finset ℕ := Finset.univ.image root
      have hsumA : (∑ a ∈ A, (1 : ℚ) / 2 ^ a) = ∑ b ∈ B, (1 : ℚ) / 2 ^ b := by
        have h1 : (∑ a ∈ A, (1 : ℚ) / 2 ^ a) = (bs.map (fun b => (1 : ℚ) / 2 ^ b.depth)).sum := by
          rw [List.sum_toFinset _ hnd, List.map_map]
          rfl
        have h2 : (∑ b ∈ B, (1 : ℚ) / 2 ^ b) = ∑ j : Fin s, (1 : ℚ) / 2 ^ (root j) := by
          rw [Finset.sum_image (fun x _ y _ h => hinj h)]
        rw [h1, h2, hsum_bs, hsum0, heq]
      have hAB : A = B := PEqualNP.Outside.L_lib_733.eq_of_sum_inv_two_pow_eq A B hsumA
      have hex_j : ∀ b ∈ bs, ∃ j : Fin s, root j = b.depth := by
        intro b hb
        have hmemA : b.depth ∈ A := List.mem_toFinset.mpr (List.mem_map_of_mem hb)
        rw [hAB] at hmemA
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmemA
        exact ⟨j, hj⟩
      have hex_b : ∀ j : Fin s, ∃ b ∈ bs, b.depth = root j := by
        intro j
        have hmemB : root j ∈ B := Finset.mem_image_of_mem root (Finset.mem_univ j)
        rw [← hAB] at hmemB
        obtain ⟨b, hb, hbd⟩ := List.mem_map.mp (List.mem_toFinset.mp hmemB)
        exact ⟨b, hb, hbd⟩
      have huniq_b : ∀ b1 ∈ bs, ∀ b2 ∈ bs, b1.depth = b2.depth → b1 = b2 := by
        intro b1 hb1 b2 hb2 hdeq
        obtain ⟨k1, hk1, rfl⟩ := List.getElem_of_mem hb1
        obtain ⟨k2, hk2, rfl⟩ := List.getElem_of_mem hb2
        have hkeq : k1 = k2 := by
          rw [List.nodup_iff_injective_getElem] at hnd
          have := @hnd ⟨k1, by simpa using hk1⟩ ⟨k2, by simpa using hk2⟩ (by simpa using hdeq)
          exact Fin.mk.inj this
        subst hkeq; rfl
      have huniq_vert : ∀ b1 ∈ bs, ∀ b2 ∈ bs, ∀ i : Fin m, i ∈ b1.verts → i ∈ b2.verts → b1 = b2 := by
        intro b1 hb1 b2 hb2 i hi1 hi2
        obtain ⟨k1, hk1, rfl⟩ := List.getElem_of_mem hb1
        obtain ⟨k2, hk2, rfl⟩ := List.getElem_of_mem hb2
        by_contra hne
        have hk_ne : k1 ≠ k2 := fun h => hne (by subst h; rfl)
        have hdisj : Disjoint bs[k1].verts bs[k2].verts := by
          rcases lt_or_gt_of_ne hk_ne with hlt | hgt
          · exact List.pairwise_iff_getElem.mp hval.2 k1 k2 hk1 hk2 hlt
          · exact (List.pairwise_iff_getElem.mp hval.2 k2 k1 hk2 hk1 hgt).symm
        exact Finset.disjoint_left.mp hdisj hi1 hi2
      choose blk hblk_mem hblk_in using hval.1
      choose grp hgrp_eq using fun i : Fin m => hex_j (blk i) (hblk_mem i)
      have hoff_lt : ∀ i : Fin m, leaf i - root (grp i) < m := by
        intro i
        rw [hgrp_eq i]
        have h1 := (blk i).off_le i (hblk_in i)
        have h2 : (blk i).verts.card ≤ m := by
          calc (blk i).verts.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
          _ = m := by simp
        have h3 : 1 ≤ (blk i).verts.card := Finset.card_pos.mpr (blk i).nonempty
        omega
      refine ⟨grp, fun i => ⟨leaf i - root (grp i), hoff_lt i⟩, ?_, ?_⟩
      · intro i
        have hle := (blk i).depth_le i (hblk_in i)
        rw [← hgrp_eq i] at hle
        simp only
        omega
      · intro j
        obtain ⟨b, hb_mem, hb_depth⟩ := hex_b j
        have hfilt : Finset.univ.filter (fun k : Fin m => grp k = j) = b.verts := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hgi
            have hdeq : (blk i).depth = b.depth := by rw [← hgrp_eq i, hgi, hb_depth]
            have hbeq : blk i = b := huniq_b (blk i) (hblk_mem i) b hb_mem hdeq
            rw [← hbeq]
            exact hblk_in i
          · intro hib
            have hbeq : blk i = b := huniq_vert (blk i) (hblk_mem i) b hb_mem i (hblk_in i) hib
            apply hinj
            rw [hgrp_eq i, hbeq, hb_depth]
        rw [hfilt]
        have hcongr : (∑ i ∈ b.verts, 2 ^ (m - (leaf i - root (grp i)))) =
            ∑ i ∈ b.verts, 2 ^ (m - (leaf i - b.depth)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hbeq : blk i = b := huniq_vert (blk i) (hblk_mem i) b hb_mem i (hblk_in i) hi
          rw [hgrp_eq i, hbeq]
        simpa only [hcongr] using b.weight_eq
  · rintro ⟨group, offset, hleaf, hwt⟩
    have hpart : (∑ i : Fin m, (1 : ℚ) / 2 ^ (leaf i)) =
        ∑ j : Fin s, ∑ i ∈ Finset.univ.filter (fun k : Fin m => group k = j),
          (1 : ℚ) / 2 ^ (leaf i) := by
      rw [← Finset.sum_fiberwise Finset.univ group (fun i => (1 : ℚ) / 2 ^ (leaf i))]
    rw [hpart]
    apply Finset.sum_congr rfl
    intro j _
    have hterm : ∀ i ∈ Finset.univ.filter (fun k : Fin m => group k = j),
        (1 : ℚ) / 2 ^ (leaf i) =
          ((2 ^ (m - (offset i).val) : ℕ) : ℚ) * (((2 : ℚ) ^ (root j) * (2 : ℚ) ^ m)⁻¹) := by
      intro i hi
      have hgj : group i = j := (Finset.mem_filter.mp hi).2
      have hli : leaf i = root j + (offset i).val := by rw [← hgj]; exact hleaf i
      have hle : (offset i).val ≤ m := le_of_lt (offset i).isLt
      rw [hli, ← div_eq_mul_inv]
      push_cast
      have hne1 : (2 : ℚ) ^ (root j + (offset i).val) ≠ 0 := by positivity
      have hne2 : (2 : ℚ) ^ (root j) * (2 : ℚ) ^ m ≠ 0 := by positivity
      rw [div_eq_div_iff hne1 hne2, one_mul]
      calc (2 : ℚ) ^ root j * (2 : ℚ) ^ m
          = (2 : ℚ) ^ (root j + m) := by rw [pow_add]
        _ = (2 : ℚ) ^ (root j + ((offset i).val + (m - (offset i).val))) := by rw [Nat.add_sub_cancel' hle]
        _ = (2 : ℚ) ^ (root j + (offset i).val) * (2 : ℚ) ^ (m - (offset i).val) := by
            rw [← Nat.add_assoc, pow_add]
        _ = (2 : ℚ) ^ (m - (offset i).val) * (2 : ℚ) ^ (root j + (offset i).val) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hnum : (∑ i ∈ Finset.univ.filter (fun k : Fin m => group k = j),
        ((2 ^ (m - (offset i).val) : ℕ) : ℚ)) = (2 : ℚ) ^ m := by
      have hw := hwt j
      exact_mod_cast hw
    rw [hnum, ← div_eq_mul_inv]
    have hne : (2 : ℚ) ^ m ≠ 0 := by positivity
    have hne2 : (2 : ℚ) ^ (root j) ≠ 0 := by positivity
    field_simp
