import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1253_aux

open Classical

section CardPair

abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

lemma card_pair : ∀ n : ℕ, Fintype.card (Pair n) = n.choose 2
  | 0 => by
    have : IsEmpty (Pair 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => Fin.elim0 a⟩
    simp
  | n + 1 => by
    let e : Pair (n + 1) ≃ Pair n ⊕ Fin n :=
      { toFun := fun ⟨⟨a, b⟩, h⟩ =>
          if hb : b.val < n then
            Sum.inl ⟨(⟨a.val, by have hab : a.val < b.val := h; omega⟩, ⟨b.val, hb⟩), h⟩
          else
            Sum.inr ⟨a.val, by have hab : a.val < b.val := h; have := b.isLt; omega⟩
        invFun := Sum.elim
          (fun ⟨⟨a, b⟩, h⟩ => ⟨(a.castSucc, b.castSucc), h⟩)
          (fun a => ⟨(a.castSucc, Fin.last n), by simp [Fin.lt_def]⟩)
        left_inv := fun ⟨⟨a, b⟩, h⟩ => by
          by_cases hb : b.val < n
          · simp only [hb, ↓reduceDIte, Sum.elim_inl]
            apply Subtype.ext; apply Prod.ext <;> exact Fin.ext rfl
          · simp only [hb, ↓reduceDIte, Sum.elim_inr]
            apply Subtype.ext; apply Prod.ext
            · exact Fin.ext rfl
            · exact Fin.ext (by simp only [Fin.val_last]; have := b.isLt; omega)
        right_inv := fun x => by
          rcases x with ⟨⟨a, b⟩, h⟩ | a
          · simp only [Sum.elim_inl, Fin.val_castSucc, b.isLt, ↓reduceDIte]
          · simp only [Sum.elim_inr, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
            exact congrArg Sum.inr (Fin.ext rfl) }
    rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, card_pair n,
      Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

lemma card_pair_inst (n : ℕ) (inst : Fintype (Pair n)) : @Fintype.card (Pair n) inst = n.choose 2 := by
  convert card_pair n

end CardPair

section Helpers

lemma exists_eq_sup {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) :
    ∃ a ∈ s, s.sup f = f a := by
  induction s using Finset.induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert x t hx ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨x, Finset.mem_singleton_self x, by simp⟩
    · rcases ih ht with ⟨y, hy, hsup⟩
      rw [Finset.sup_insert, hsup]
      by_cases h : f x ≤ f y
      · exact ⟨y, Finset.mem_insert_of_mem hy, max_eq_right h⟩
      · exact ⟨x, Finset.mem_insert_self x t, max_eq_left (by omega)⟩

lemma nat_0_ne_2 : (0 : ℕ) ≠ 2 := by decide
lemma nat_1_ne_0 : (1 : ℕ) ≠ 0 := by decide
lemma nat_1_ne_2 : (1 : ℕ) ≠ 2 := by decide
lemma nat_2_ne_0 : (2 : ℕ) ≠ 0 := by decide
lemma nat_2_ne_1 : (2 : ℕ) ≠ 1 := by decide
lemma nat_0_lt_2 : (0 : ℕ) < 2 := by decide
lemma nat_1_lt_2 : (1 : ℕ) < 2 := by decide
lemma nat_not_2_lt_2 : ¬ ((2 : ℕ) < 2) := by decide
lemma val_fin3_2 : ((2 : Fin 3) : ℕ) = 2 := rfl

end Helpers

section MainProof

theorem main :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ n : Nat,
  let Pair := {p : Fin n × Fin n // p.1 < p.2}
  let Occ := Fin n ⊕ (Pair × Fin 3)
  let clause : Occ → Fin n ⊕ Pair := Sum.elim Sum.inl (fun pk => Sum.inr pk.1)
  let var : Occ → Option (Fin n) := Sum.elim some (fun pk =>
    if pk.2.val=0 then some pk.1.val.1 else if pk.2.val=1 then some pk.1.val.2 else none)
  let sign : Occ → Bool := Sum.elim (fun _ => true) (fun pk => decide (pk.2.val=2))
  let allowed := fun (j : Occ) => (Finset.univ : Finset Occ).filter
    (fun i => clause i ≠ clause j ∧ ¬(var i=var j ∧ sign i≠sign j))
  let pack := Nat.rec (motive := fun _ => Finset Occ → Prop) (fun _ => True)
    (fun _ prev x => ∃ (u v : Finset Occ) (j : Occ), prev u ∧ u ⊆ v ∧ v ⊆ x ∧
      u ⊆ allowed j ∧ j ∈ v)
  let score := fun (x : Finset Occ) =>
    (Finset.univ : Finset (Option (Fin n) → Bool)).sup (fun s =>
      ((x.filter (fun i => s (var i)=sign i)).image clause).card)
  let canonical := fun (x : Finset Occ) (j : Occ) =>
    ∃ u : Finset Occ, u ⊆ x ∧ u ⊆ allowed j ∧ score u = score x
  let mask := fun (A : Finset (Fin n)) (E : Finset Pair) => (Finset.univ : Finset Occ).filter
    (Sum.elim (fun v => v∈A) (fun pk => pk.2.val<2 ∨ pk.1∈E))
  let omega := fun (A : Finset (Fin n)) (E : Finset Pair) =>
    (A.powerset.filter (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E)).sup Finset.card
  Fintype.card Pair = n.choose 2 ∧
  ∀ (A : Finset (Fin n)) (E : Finset Pair),
    score (mask A E) = n.choose 2 + omega A E ∧
    (∀ l, pack l (mask A E) ↔ l ≤ n.choose 2 + omega A E) ∧
    (∀ v, canonical (mask A E) (Sum.inl v) ↔ omega (insert v A) E = omega A E+1) ∧
    ∀ p : Pair, canonical (mask A E) (Sum.inr (p,(2 : Fin 3))) ↔
      omega A (insert p E) = omega A E+1 := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n
  dsimp only
  let Pair := {p : Fin n × Fin n // p.1 < p.2}
  let Occ := Fin n ⊕ (Pair × Fin 3)
  let clause : Occ → Fin n ⊕ Pair := Sum.elim Sum.inl (fun pk => Sum.inr pk.1)
  let var : Occ → Option (Fin n) := Sum.elim some (fun pk =>
    if pk.2.val=0 then some pk.1.val.1 else if pk.2.val=1 then some pk.1.val.2 else none)
  let sign : Occ → Bool := Sum.elim (fun _ => true) (fun pk => decide (pk.2.val=2))
  let allowed : Occ → Finset Occ := fun j => (Finset.univ : Finset Occ).filter
    (fun i => clause i ≠ clause j ∧ ¬(var i=var j ∧ sign i≠sign j))
  let pack : ℕ → Finset Occ → Prop := Nat.rec (motive := fun _ => Finset Occ → Prop) (fun _ => True)
    (fun _ prev x => ∃ (u v : Finset Occ) (j : Occ), prev u ∧ u ⊆ v ∧ v ⊆ x ∧
      u ⊆ allowed j ∧ j ∈ v)
  let score : Finset Occ → ℕ := fun x =>
    (Finset.univ : Finset (Option (Fin n) → Bool)).sup (fun s =>
      ((x.filter (fun i => s (var i)=sign i)).image clause).card)
  let canonical : Finset Occ → Occ → Prop := fun x j =>
    ∃ u : Finset Occ, u ⊆ x ∧ u ⊆ allowed j ∧ score u = score x
  let mask : Finset (Fin n) → Finset Pair → Finset Occ := fun A E => (Finset.univ : Finset Occ).filter
    (Sum.elim (fun v => v∈A) (fun pk => pk.2.val<2 ∨ pk.1∈E))
  let om : Finset (Fin n) → Finset Pair → ℕ := fun A E =>
    (A.powerset.filter (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E)).sup Finset.card
  have hCardPair : Fintype.card Pair = n.choose 2 := card_pair_inst n _
  let Feas : Finset Occ → Prop := fun S =>
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → i ∈ allowed j
  have hAllowedSym : ∀ i j : Occ, i ∈ allowed j → j ∈ allowed i := by
    intro i j hij
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    exact ⟨hij.1.symm, fun h => hij.2 ⟨h.1.symm, h.2.symm⟩⟩
  have hAllowedIrr : ∀ j : Occ, j ∉ allowed j := by
    intro j hj
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj.1 rfl
  have hFeasSub : ∀ {S T : Finset Occ}, Feas T → S ⊆ T → Feas S := by
    intro S T hT hST i hi j hj hne
    exact hT i (hST hi) j (hST hj) hne
  have hFeasInsert : ∀ {S : Finset Occ} {j : Occ}, Feas S → S ⊆ allowed j → Feas (insert j S) := by
    intro S j hS hSj a ha b hb hne
    rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact absurd rfl hne
      · exact hAllowedSym b a (hSj hbS)
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact hSj haS
      · exact hS a haS b hbS hne
  have hFeasLeScore : ∀ {x S : Finset Occ}, S ⊆ x → Feas S → S.card ≤ score x := by
    intro x S hSx hS
    let s : Option (Fin n) → Bool := fun w => decide (∃ i ∈ S, var i = w ∧ sign i = true)
    have hSub : S ⊆ x.filter (fun i => s (var i) = sign i) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨hSx hi, ?_⟩
      cases hsi : sign i
      · simp only [s, decide_eq_false_iff_not]
        rintro ⟨k, hk, hvk, hsk⟩
        by_cases hki : k = i
        · subst hki; rw [hsi] at hsk; cases hsk
        · have hall := hS k hk i hi hki
          simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hall
          exact hall.2 ⟨hvk, by rw [hsk, hsi]; intro h; cases h⟩
      · simp only [s, decide_eq_true_eq]
        exact ⟨i, hi, rfl, hsi⟩
    have hInj : Set.InjOn clause (S : Set Occ) := by
      intro i hi j hj hcl
      by_contra hne
      have hall := hS i hi j hj hne
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hall
      exact hall.1 hcl
    have hCard : S.card = (S.image clause).card := (Finset.card_image_of_injOn hInj).symm
    have hLe : (S.image clause).card ≤ ((x.filter (fun i => s (var i) = sign i)).image clause).card :=
      Finset.card_le_card (Finset.image_subset_image hSub)
    have hSup : ((x.filter (fun i => s (var i) = sign i)).image clause).card ≤ score x :=
      Finset.le_sup (f := fun s => ((x.filter (fun i => s (var i) = sign i)).image clause).card)
        (Finset.mem_univ s)
    exact hCard.le.trans (hLe.trans hSup)
  have hScoreExistsFeas : ∀ x : Finset Occ, ∃ S ⊆ x, Feas S ∧ S.card = score x := by
    intro x
    have hne : (Finset.univ : Finset (Option (Fin n) → Bool)).Nonempty :=
      ⟨fun _ => false, Finset.mem_univ _⟩
    rcases exists_eq_sup Finset.univ hne
      (fun s => ((x.filter (fun i => s (var i) = sign i)).image clause).card) with ⟨s, _, hs⟩
    let F := x.filter (fun i => s (var i) = sign i)
    let C := F.image clause
    let rep : {c // c ∈ C} → Occ := fun c => (Finset.mem_image.mp c.2).choose
    have hrep_mem : ∀ c : {c // c ∈ C}, rep c ∈ F := fun c => (Finset.mem_image.mp c.2).choose_spec.1
    have hrep_cl : ∀ c : {c // c ∈ C}, clause (rep c) = c.1 := fun c => (Finset.mem_image.mp c.2).choose_spec.2
    have hrep_inj : Function.Injective rep := by
      intro c1 c2 heq
      apply Subtype.ext
      rw [← hrep_cl c1, ← hrep_cl c2, heq]
    let S := C.attach.image rep
    refine ⟨S, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_image.mp hi with ⟨c, _, rfl⟩
      exact (Finset.mem_filter.mp (hrep_mem c)).1
    · intro i hi j hj hne
      rcases Finset.mem_image.mp hi with ⟨c1, _, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨c2, _, rfl⟩
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro hcl
        apply hne
        have hc : c1 = c2 := Subtype.ext (by rw [← hrep_cl c1, ← hrep_cl c2, hcl])
        rw [hc]
      · rintro ⟨hvar, hsign⟩
        have hs1 := (Finset.mem_filter.mp (hrep_mem c1)).2
        have hs2 := (Finset.mem_filter.mp (hrep_mem c2)).2
        rw [← hs1, ← hs2, hvar] at hsign
        exact hsign rfl
    · rw [Finset.card_image_of_injective _ hrep_inj, Finset.card_attach]
      exact hs.symm
  have hScoreMono : ∀ {u x : Finset Occ}, u ⊆ x → score u ≤ score x := by
    intro u x hux
    rcases hScoreExistsFeas u with ⟨S, hSu, hSfeas, hScard⟩
    rw [← hScard]
    exact hFeasLeScore (hSu.trans hux) hSfeas
  have hScoreInsertLe : ∀ (x : Finset Occ) (j : Occ), score (insert j x) ≤ score x + 1 := by
    intro x j
    refine Finset.sup_le ?_
    intro s _
    have hSub : ((insert j x).filter (fun i => s (var i) = sign i)).image clause ⊆
        insert (clause j) ((x.filter (fun i => s (var i) = sign i)).image clause) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
      rcases Finset.mem_filter.mp hi with ⟨hiins, hisat⟩
      rcases Finset.mem_insert.mp hiins with rfl | hix
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hix, hisat⟩, rfl⟩)
    have h1 := Finset.card_le_card hSub
    have h2 := Finset.card_insert_le (clause j) ((x.filter (fun i => s (var i) = sign i)).image clause)
    have h3 : ((x.filter (fun i => s (var i) = sign i)).image clause).card ≤ score x :=
      Finset.le_sup (f := fun s => ((x.filter (fun i => s (var i) = sign i)).image clause).card)
        (Finset.mem_univ s)
    exact h1.trans (h2.trans (Nat.add_le_add_right h3 1))
  have hPackIff : ∀ (l : ℕ) (x : Finset Occ), pack l x ↔ l ≤ score x := by
    intro l
    induction l with
    | zero =>
      intro x
      exact ⟨fun _ => Nat.zero_le _, fun _ => trivial⟩
    | succ l ih =>
      intro x
      constructor
      · rintro ⟨u, v, j, hpu, huv, hvx, huj, hjv⟩
        have hle : l ≤ score u := (ih u).mp hpu
        rcases hScoreExistsFeas u with ⟨S, hSu, hSfeas, hScard⟩
        have hSj : S ⊆ allowed j := hSu.trans huj
        have hjnot : j ∉ S := fun hjS => hAllowedIrr j (hSj hjS)
        have hInsSub : insert j S ⊆ x := Finset.insert_subset (hvx hjv) (hSu.trans (huv.trans hvx))
        have hInsFeas : Feas (insert j S) := hFeasInsert hSfeas hSj
        have hCard : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hjnot
        have hLeScore := hFeasLeScore hInsSub hInsFeas
        calc l + 1 ≤ score u + 1 := Nat.add_le_add_right hle 1
          _ = S.card + 1 := by rw [hScard]
          _ = (insert j S).card := hCard.symm
          _ ≤ score x := hLeScore
      · intro hle
        rcases hScoreExistsFeas x with ⟨S, hSx, hSfeas, hScard⟩
        have hSpos : 0 < S.card := by
          rw [hScard]
          exact Nat.lt_of_lt_of_le (Nat.succ_pos l) hle
        rcases Finset.card_pos.mp hSpos with ⟨j, hjS⟩
        let u := S.erase j
        have huS : u ⊆ S := Finset.erase_subset j S
        have huFeas : Feas u := hFeasSub hSfeas huS
        have huCard : u.card = S.card - 1 := Finset.card_erase_of_mem hjS
        have huScore : u.card ≤ score u := hFeasLeScore (Finset.Subset.refl u) huFeas
        have hl_le : l ≤ score u := by
          have h1 : l ≤ S.card - 1 := Nat.le_sub_one_of_lt (by rw [hScard]; exact hle)
          exact h1.trans (huCard ▸ huScore)
        have hpu : pack l u := (ih u).mpr hl_le
        have huj : u ⊆ allowed j := by
          intro i hi
          rcases Finset.mem_erase.mp hi with ⟨hij, hiS⟩
          exact hSfeas i hiS j hjS hij
        exact ⟨u, S, j, hpu, huS, hSx, huj, hjS⟩
  have hCanonIff : ∀ (x : Finset Occ) (j : Occ), canonical x j ↔ score (insert j x) = score x + 1 := by
    intro x j
    constructor
    · rintro ⟨u, hux, huj, hsu⟩
      rcases hScoreExistsFeas u with ⟨S, hSu, hSfeas, hScard⟩
      have hSj : S ⊆ allowed j := hSu.trans huj
      have hjnot : j ∉ S := fun hjS => hAllowedIrr j (hSj hjS)
      have hInsSub : insert j S ⊆ insert j x :=
        Finset.insert_subset (Finset.mem_insert_self j x)
          ((hSu.trans hux).trans (Finset.subset_insert j x))
      have hInsFeas : Feas (insert j S) := hFeasInsert hSfeas hSj
      have hGe := hFeasLeScore hInsSub hInsFeas
      have hCard := Finset.card_insert_of_notMem hjnot
      have hLe := hScoreInsertLe x j
      exact le_antisymm hLe (by rw [← hsu, ← hScard, ← hCard]; exact hGe)
    · intro heq
      rcases hScoreExistsFeas (insert j x) with ⟨S, hSins, hSfeas, hScard⟩
      have hjS : j ∈ S := by
        by_contra hjnot
        have hSx : S ⊆ x := by
          intro i hi
          rcases Finset.mem_insert.mp (hSins hi) with rfl | hix
          · exact absurd hi hjnot
          · exact hix
        have hLe := hFeasLeScore hSx hSfeas
        exact Nat.not_succ_le_self (score x) (by rw [Nat.succ_eq_add_one, ← heq, ← hScard]; exact hLe)
      let u := S.erase j
      have hux : u ⊆ x := by
        intro i hi
        rcases Finset.mem_erase.mp hi with ⟨hij, hiS⟩
        rcases Finset.mem_insert.mp (hSins hiS) with rfl | hix
        · exact absurd rfl hij
        · exact hix
      have huj : u ⊆ allowed j := by
        intro i hi
        rcases Finset.mem_erase.mp hi with ⟨hij, hiS⟩
        exact hSfeas i hiS j hjS hij
      have huFeas : Feas u := hFeasSub hSfeas (Finset.erase_subset j S)
      have huCard : u.card = S.card - 1 := Finset.card_erase_of_mem hjS
      have hGe : u.card ≤ score u := hFeasLeScore (Finset.Subset.refl u) huFeas
      have hLe : score u ≤ score x := hScoreMono hux
      have hEqU : score u = score x := le_antisymm hLe (by
        have h1 : score x = u.card := by rw [huCard, hScard, heq, Nat.add_sub_cancel]
        exact h1 ▸ hGe)
      exact ⟨u, hux, huj, hEqU⟩
  have hSatDecomp : ∀ (A : Finset (Fin n)) (E : Finset Pair) (s : Option (Fin n) → Bool),
      (((mask A E).filter (fun i => s (var i) = sign i)).image clause).card =
        (A.filter (fun v => s (some v) = true)).card +
        ((Finset.univ : Finset Pair).filter (fun p =>
          s (some p.val.1) = false ∨ s (some p.val.2) = false ∨ (p ∈ E ∧ s none = true))).card := by
    intro A E s
    let V := A.filter (fun v => s (some v) = true)
    let Psat := (Finset.univ : Finset Pair).filter (fun p =>
      s (some p.val.1) = false ∨ s (some p.val.2) = false ∨ (p ∈ E ∧ s none = true))
    have hEq : ((mask A E).filter (fun i => s (var i) = sign i)).image clause =
        V.image Sum.inl ∪ Psat.image Sum.inr := by
      ext c
      rcases c with v | p
      · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_union,
          V, Psat, mask, Finset.mem_univ, true_and, reduceCtorEq, and_false, exists_false, or_false]
        constructor
        · rintro ⟨i, ⟨him, his⟩, hcl⟩
          rcases i with w | pk
          · simp only [clause, Sum.elim_inl, Sum.inl.injEq] at hcl
            subst hcl
            simp only [Sum.elim_inl, var, sign] at him his
            exact ⟨w, ⟨him, his⟩, rfl⟩
          · simp only [clause, Sum.elim_inr, reduceCtorEq] at hcl
        · rintro ⟨w, ⟨hwA, hsw⟩, hwv⟩
          injection hwv with hwv
          subst hwv
          exact ⟨Sum.inl w, ⟨hwA, hsw⟩, rfl⟩
      · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_union,
          V, Psat, mask, Finset.mem_univ, true_and, reduceCtorEq, and_false, exists_false, false_or]
        constructor
        · rintro ⟨i, ⟨him, his⟩, hcl⟩
          rcases i with w | ⟨q, k⟩
          · simp only [clause, Sum.elim_inl, reduceCtorEq] at hcl
          · simp only [clause, Sum.elim_inr, Sum.inr.injEq] at hcl
            subst hcl
            refine ⟨q, ?_, rfl⟩
            rcases k with ⟨k, hk⟩
            simp only [Sum.elim_inr, var, sign] at him his
            rcases k with _ | _ | _ | k
            · simp only [ite_true, decide_eq_false nat_0_ne_2] at his
              exact Or.inl his
            · simp only [if_neg nat_1_ne_0, ite_true, decide_eq_false nat_1_ne_2] at his
              exact Or.inr (Or.inl his)
            · simp only [if_neg nat_2_ne_0, if_neg nat_2_ne_1, decide_true] at his
              exact Or.inr (Or.inr ⟨him.resolve_left nat_not_2_lt_2, his⟩)
            · exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 3 k))
        · rintro ⟨q, hq, hqp⟩
          injection hqp with hqp
          subst hqp
          rcases hq with h0 | h1 | ⟨hqE, hsnone⟩
          · exact ⟨Sum.inr (q, (0 : Fin 3)),
              ⟨Or.inl nat_0_lt_2, by
                simp only [var, sign, Sum.elim_inr, Fin.val_zero, ite_true, decide_eq_false nat_0_ne_2, h0]⟩,
              rfl⟩
          · exact ⟨Sum.inr (q, (1 : Fin 3)),
              ⟨Or.inl nat_1_lt_2, by
                simp only [var, sign, Sum.elim_inr, Fin.val_one, if_neg nat_1_ne_0, ite_true,
                  decide_eq_false nat_1_ne_2, h1]⟩,
              rfl⟩
          · exact ⟨Sum.inr (q, (2 : Fin 3)),
              ⟨Or.inr hqE, by
                simp only [var, sign, Sum.elim_inr, val_fin3_2, if_neg nat_2_ne_0, if_neg nat_2_ne_1,
                  decide_true, hsnone]⟩,
              rfl⟩
    rw [hEq, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ Sum.inl_injective,
          Finset.card_image_of_injective _ Sum.inr_injective]
    · refine Finset.disjoint_left.mpr ?_
      intro c hc1 hc2
      rcases Finset.mem_image.mp hc1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hc2 with ⟨_, _, h⟩
      cases h
  have hLeScore : ∀ (x : Finset Occ) (s : Option (Fin n) → Bool),
      ((x.filter (fun i => s (var i) = sign i)).image clause).card ≤ score x := fun x s =>
    Finset.le_sup (f := fun s => ((x.filter (fun i => s (var i) = sign i)).image clause).card)
      (Finset.mem_univ s)
  have hScoreMask : ∀ (A : Finset (Fin n)) (E : Finset Pair),
      score (mask A E) = n.choose 2 + om A E := by
    intro A E
    have hCliqueBound : ∀ T ∈ A.powerset.filter (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E),
        n.choose 2 + T.card ≤ score (mask A E) := by
      intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTsub, hTclique⟩
      have hTA : T ⊆ A := Finset.mem_powerset.mp hTsub
      let s : Option (Fin n) → Bool := fun w =>
        match w with
        | none => true
        | some v => decide (v ∈ T)
      have hLe := hLeScore (mask A E) s
      rw [hSatDecomp A E s] at hLe
      have hV : A.filter (fun v => s (some v) = true) = T := by
        ext v
        simp only [Finset.mem_filter, s, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun hv => ⟨hTA hv, hv⟩⟩
      have hP : (Finset.univ : Finset Pair).filter (fun p =>
          s (some p.val.1) = false ∨ s (some p.val.2) = false ∨ (p ∈ E ∧ s none = true)) = Finset.univ := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, s,
          decide_eq_false_iff_not, and_true]
        by_cases h1 : p.val.1 ∈ T
        · by_cases h2 : p.val.2 ∈ T
          · exact Or.inr (Or.inr (hTclique p h1 h2))
          · exact Or.inr (Or.inl h2)
        · exact Or.inl h1
      rw [hV, hP, Finset.card_univ, hCardPair, add_comm] at hLe
      exact hLe
    have hLower : n.choose 2 + om A E ≤ score (mask A E) := by
      have hEmptyMem : (∅ : Finset (Fin n)) ∈ A.powerset.filter
          (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E) := by
        simp
      have hBase := hCliqueBound ∅ hEmptyMem
      simp only [Finset.card_empty, add_zero] at hBase
      have hSupLe : om A E ≤ score (mask A E) - n.choose 2 := by
        refine Finset.sup_le ?_
        intro T hT
        exact Nat.le_sub_of_add_le' (hCliqueBound T hT)
      calc n.choose 2 + om A E
          ≤ n.choose 2 + (score (mask A E) - n.choose 2) := Nat.add_le_add_left hSupLe _
        _ = score (mask A E) := Nat.add_sub_of_le hBase
    have hUpper : score (mask A E) ≤ n.choose 2 + om A E := by
      refine Finset.sup_le ?_
      intro s _
      rw [hSatDecomp A E s]
      let V := A.filter (fun v => s (some v) = true)
      let Psat := (Finset.univ : Finset Pair).filter (fun p =>
        s (some p.val.1) = false ∨ s (some p.val.2) = false ∨ (p ∈ E ∧ s none = true))
      let Bad := (Finset.univ : Finset Pair).filter (fun p =>
        p.val.1 ∈ V ∧ p.val.2 ∈ V ∧ p ∉ E)
      have hDisj : Disjoint Psat Bad := by
        refine Finset.disjoint_left.mpr ?_
        intro p hp1 hp2
        simp only [Psat, Bad, V, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        rcases hp2 with ⟨⟨_, hs1⟩, ⟨_, hs2⟩, hpE⟩
        rcases hp1 with h0 | h1 | ⟨hpE', _⟩
        · rw [hs1] at h0; cases h0
        · rw [hs2] at h1; cases h1
        · exact hpE hpE'
      have hPairBound : Psat.card + Bad.card ≤ n.choose 2 := by
        rw [← Finset.card_union_of_disjoint hDisj, ← hCardPair, ← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      let D := Bad.image (fun p => p.val.1)
      let T := V \ D
      have hTmem : T ∈ A.powerset.filter (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
        · intro v hv
          exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
        · intro p hp1 hp2
          by_contra hpE
          have hv1 : p.val.1 ∈ V := (Finset.mem_sdiff.mp hp1).1
          have hv2 : p.val.2 ∈ V := (Finset.mem_sdiff.mp hp2).1
          have hpBad : p ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hv1, hv2, hpE⟩
          have hpD : p.val.1 ∈ D := Finset.mem_image.mpr ⟨p, hpBad, rfl⟩
          exact (Finset.mem_sdiff.mp hp1).2 hpD
      have hTle : T.card ≤ om A E :=
        Finset.le_sup (f := Finset.card) hTmem
      have hVsub : V ⊆ T ∪ D := by
        intro v hv
        by_cases hvD : v ∈ D
        · exact Finset.mem_union_right _ hvD
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hvD⟩)
      have hVle : V.card ≤ T.card + Bad.card :=
        (Finset.card_le_card hVsub).trans
          ((Finset.card_union_le T D).trans (Nat.add_le_add_left Finset.card_image_le T.card))
      refine Nat.le_of_add_le_add_right (b := Bad.card) ?_
      calc V.card + Psat.card + Bad.card
          = V.card + (Psat.card + Bad.card) := Nat.add_assoc _ _ _
        _ ≤ (T.card + Bad.card) + n.choose 2 := Nat.add_le_add hVle hPairBound
        _ ≤ (om A E + Bad.card) + n.choose 2 := Nat.add_le_add_right (Nat.add_le_add_right hTle _) _
        _ = n.choose 2 + om A E + Bad.card := by ac_rfl
    exact le_antisymm hUpper hLower
  have hMaskInsertV : ∀ (A : Finset (Fin n)) (E : Finset Pair) (v : Fin n),
      insert (Sum.inl v) (mask A E) = mask (insert v A) E := by
    intro A E v
    ext i
    rcases i with w | pk
    · simp only [mask, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Sum.elim_inl]
      constructor
      · rintro (h | h)
        · injection h with h; exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h
    · simp only [mask, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Sum.elim_inr, reduceCtorEq, false_or]
  have hMaskInsertE : ∀ (A : Finset (Fin n)) (E : Finset Pair) (p : Pair),
      insert (Sum.inr (p, (2 : Fin 3))) (mask A E) = mask A (insert p E) := by
    intro A E p
    ext i
    rcases i with w | ⟨q, ⟨k, hk⟩⟩
    · simp only [mask, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Sum.elim_inl, reduceCtorEq, false_or]
    · simp only [mask, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Sum.elim_inr]
      rcases k with _ | _ | _ | k
      · exact ⟨fun _ => Or.inl nat_0_lt_2, fun _ => Or.inr (Or.inl nat_0_lt_2)⟩
      · exact ⟨fun _ => Or.inl nat_1_lt_2, fun _ => Or.inr (Or.inl nat_1_lt_2)⟩
      · have h2 : (⟨2, hk⟩ : Fin 3) = (2 : Fin 3) := Fin.ext rfl
        rw [h2]
        constructor
        · rintro (h | hlt | hE)
          · injection h with h
            injection h with hqp _
            exact Or.inr (Or.inl hqp)
          · exact absurd hlt nat_not_2_lt_2
          · exact Or.inr (Or.inr hE)
        · rintro (hlt | hE)
          · exact absurd hlt nat_not_2_lt_2
          · rcases hE with rfl | hE'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hE')
      · exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 3 k))
  refine ⟨hCardPair, ?_⟩
  intro A E
  refine ⟨hScoreMask A E, ?_, ?_, ?_⟩
  · intro l
    change pack l (mask A E) ↔ l ≤ n.choose 2 + om A E
    rw [hPackIff l (mask A E), hScoreMask A E]
  · intro v
    change canonical (mask A E) (Sum.inl v) ↔ om (insert v A) E = om A E + 1
    rw [hCanonIff (mask A E) (Sum.inl v), hMaskInsertV A E v, hScoreMask (insert v A) E, hScoreMask A E]
    exact ⟨fun h => Nat.add_left_cancel (by rw [← Nat.add_assoc]; exact h),
      fun h => by rw [h, Nat.add_assoc]⟩
  · intro p
    change canonical (mask A E) (Sum.inr (p, (2 : Fin 3))) ↔ om A (insert p E) = om A E + 1
    rw [hCanonIff (mask A E) (Sum.inr (p, (2 : Fin 3))), hMaskInsertE A E p,
      hScoreMask A (insert p E), hScoreMask A E]
    exact ⟨fun h => Nat.add_left_cancel (by rw [← Nat.add_assoc]; exact h),
      fun h => by rw [h, Nat.add_assoc]⟩

end MainProof

end PEqualNP.Outside.L_lib_1253_aux

theorem PEqualNP.Outside.L_lib_1253 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ n : Nat,
  let Pair := {p : Fin n × Fin n // p.1 < p.2}
  let Occ := Fin n ⊕ (Pair × Fin 3)
  let clause : Occ → Fin n ⊕ Pair := Sum.elim Sum.inl (fun pk => Sum.inr pk.1)
  let var : Occ → Option (Fin n) := Sum.elim some (fun pk =>
    if pk.2.val=0 then some pk.1.val.1 else if pk.2.val=1 then some pk.1.val.2 else none)
  let sign : Occ → Bool := Sum.elim (fun _ => true) (fun pk => decide (pk.2.val=2))
  let allowed := fun (j : Occ) => (Finset.univ : Finset Occ).filter
    (fun i => clause i ≠ clause j ∧ ¬(var i=var j ∧ sign i≠sign j))
  let pack := Nat.rec (motive := fun _ => Finset Occ → Prop) (fun _ => True)
    (fun _ prev x => ∃ (u v : Finset Occ) (j : Occ), prev u ∧ u ⊆ v ∧ v ⊆ x ∧
      u ⊆ allowed j ∧ j ∈ v)
  let score := fun (x : Finset Occ) =>
    (Finset.univ : Finset (Option (Fin n) → Bool)).sup (fun s =>
      ((x.filter (fun i => s (var i)=sign i)).image clause).card)
  let canonical := fun (x : Finset Occ) (j : Occ) =>
    ∃ u : Finset Occ, u ⊆ x ∧ u ⊆ allowed j ∧ score u = score x
  let mask := fun (A : Finset (Fin n)) (E : Finset Pair) => (Finset.univ : Finset Occ).filter
    (Sum.elim (fun v => v∈A) (fun pk => pk.2.val<2 ∨ pk.1∈E))
  let omega := fun (A : Finset (Fin n)) (E : Finset Pair) =>
    (A.powerset.filter (fun T => ∀ p : Pair, p.val.1 ∈ T → p.val.2 ∈ T → p ∈ E)).sup Finset.card
  Fintype.card Pair = n.choose 2 ∧
  ∀ (A : Finset (Fin n)) (E : Finset Pair),
    score (mask A E) = n.choose 2 + omega A E ∧
    (∀ l, pack l (mask A E) ↔ l ≤ n.choose 2 + omega A E) ∧
    (∀ v, canonical (mask A E) (Sum.inl v) ↔ omega (insert v A) E = omega A E+1) ∧
    ∀ p : Pair, canonical (mask A E) (Sum.inr (p,(2 : Fin 3))) ↔
      omega A (insert p E) = omega A E+1 :=
  PEqualNP.Outside.L_lib_1253_aux.main
