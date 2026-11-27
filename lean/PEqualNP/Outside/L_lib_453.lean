import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_453

variable {α : Type*} [DecidableEq α]

def parts (S : Finset α) : Finset (Finset (Finset α)) :=
  S.powerset.powerset.filter (fun P => ∅ ∉ P ∧ (∀ i ∈ S, ∃ B ∈ P, i ∈ B) ∧
    (∀ B ∈ P, ∀ B' ∈ P, ∀ i ∈ B, i ∈ B' → B = B'))

theorem mem_parts {S : Finset α} {P : Finset (Finset α)} :
    P ∈ parts S ↔ (∀ B ∈ P, B ⊆ S) ∧ ∅ ∉ P ∧ (∀ i ∈ S, ∃ B ∈ P, i ∈ B) ∧
      (∀ B ∈ P, ∀ B' ∈ P, ∀ i ∈ B, i ∈ B' → B = B') := by
  unfold parts
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun B hB => Finset.mem_powerset.mp (h1 hB), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun B hB => Finset.mem_powerset.mpr (h1 B hB), h2⟩

theorem not_mem_block {S : Finset α} {a : α} (ha : a ∉ S) {P : Finset (Finset α)}
    (hP : P ∈ parts S) {B : Finset α} (hB : B ∈ P) : a ∉ B :=
  fun h => ha ((mem_parts.mp hP).1 B hB h)

theorem nonempty_block {S : Finset α} {P : Finset (Finset α)} (hP : P ∈ parts S)
    {B : Finset α} (hB : B ∈ P) : B.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  exact (mem_parts.mp hP).2.1 hB

theorem ins_mem {S : Finset α} {a : α} (ha : a ∉ S) {P : Finset (Finset α)}
    (hP : P ∈ parts S) : insert {a} P ∈ parts (insert a S) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  rw [mem_parts]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · exact (h1 B hB).trans (Finset.subset_insert _ _)
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.singleton_ne_empty a h.symm
    · exact h2 h
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | hi
    · exact ⟨{a}, Finset.mem_insert_self _ _, by rw [h]; exact Finset.mem_singleton_self _⟩
    · obtain ⟨B, hB, hiB⟩ := h3 i hi
      exact ⟨B, Finset.mem_insert_of_mem hB, hiB⟩
  · intro B hB B' hB' i hiB hiB'
    rcases Finset.mem_insert.mp hB with rfl | hB <;>
      rcases Finset.mem_insert.mp hB' with rfl | hB'
    · rfl
    · rw [Finset.mem_singleton] at hiB
      rw [hiB] at hiB'
      exact absurd (h1 B' hB' hiB') ha
    · rw [Finset.mem_singleton] at hiB'
      rw [hiB'] at hiB
      exact absurd (h1 B hB hiB) ha
    · exact h4 B hB B' hB' i hiB hiB'

theorem join_mem {S : Finset α} {a : α} (ha : a ∉ S) {P : Finset (Finset α)}
    (hP : P ∈ parts S) {B : Finset α} (hB : B ∈ P) :
    insert (insert a B) (P.erase B) ∈ parts (insert a S) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  rw [mem_parts]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Finset.insert_subset_insert a (h1 B hB)
    · exact (h1 C (Finset.mem_of_mem_erase hC)).trans (Finset.subset_insert _ _)
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.insert_ne_empty a B h.symm
    · exact h2 (Finset.mem_of_mem_erase h)
  · intro i hi
    by_cases hiB : i ∈ B
    · exact ⟨insert a B, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hiB⟩
    rcases Finset.mem_insert.mp hi with h | hi
    · exact ⟨insert a B, Finset.mem_insert_self _ _, by rw [h]; exact Finset.mem_insert_self _ _⟩
    · obtain ⟨C, hC, hiC⟩ := h3 i hi
      have hCB : C ≠ B := by rintro rfl; exact hiB hiC
      exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCB, hC⟩), hiC⟩
  · have key : ∀ C ∈ P.erase B, ∀ i ∈ insert a B, i ∈ C → False := by
      intro C hC i hi hiC
      obtain ⟨hCB, hC⟩ := Finset.mem_erase.mp hC
      rcases Finset.mem_insert.mp hi with h | hi
      · rw [h] at hiC
        exact ha (h1 C hC hiC)
      · exact hCB (h4 C hC B hB i hiC hi)
    intro C hC C' hC' i hiC hiC'
    rcases Finset.mem_insert.mp hC with rfl | hC <;>
      rcases Finset.mem_insert.mp hC' with rfl | hC'
    · rfl
    · exact (key C' hC' i hiC hiC').elim
    · exact (key C hC i hiC' hiC).elim
    · exact h4 C (Finset.mem_of_mem_erase hC) C' (Finset.mem_of_mem_erase hC') i hiC hiC'

theorem surj_ins {S : Finset α} {a : α} (ha : a ∉ S) {P : Finset (Finset α)}
    (hP : P ∈ parts (insert a S)) (hs : {a} ∈ P) :
    P.erase {a} ∈ parts S ∧ insert {a} (P.erase {a}) = P := by
  refine ⟨?_, Finset.insert_erase hs⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  rw [mem_parts]
  refine ⟨?_, fun h => h2 (Finset.mem_of_mem_erase h), ?_, ?_⟩
  · intro B hB x hx
    obtain ⟨hBa, hB⟩ := Finset.mem_erase.mp hB
    rcases Finset.mem_insert.mp (h1 B hB hx) with h | h
    · exfalso
      apply hBa
      exact h4 B hB {a} hs x hx (by rw [h]; exact Finset.mem_singleton_self a)
    · exact h
  · intro i hi
    obtain ⟨B, hB, hiB⟩ := h3 i (Finset.mem_insert_of_mem hi)
    refine ⟨B, Finset.mem_erase.mpr ⟨?_, hB⟩, hiB⟩
    rintro rfl
    rw [Finset.mem_singleton] at hiB
    rw [hiB] at hi
    exact ha hi
  · intro B hB B' hB' i hiB hiB'
    exact h4 B (Finset.mem_of_mem_erase hB) B' (Finset.mem_of_mem_erase hB') i hiB hiB'

theorem surj_join {S : Finset α} {a : α} (ha : a ∉ S) {P : Finset (Finset α)}
    (hP : P ∈ parts (insert a S)) (hs : {a} ∉ P) :
    ∃ P' ∈ parts S, ∃ B ∈ P', insert (insert a B) (P'.erase B) = P := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  obtain ⟨Ba, hBa, haBa⟩ := h3 a (Finset.mem_insert_self a S)
  have hBne : (Ba.erase a).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hs
    have : Ba = {a} := by
      ext x
      constructor
      · intro hx
        by_contra hxa
        rw [Finset.mem_singleton] at hxa
        have : x ∈ Ba.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rw [hne] at this
        exact Finset.notMem_empty x this
      · intro hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact haBa
    rw [← this]
    exact hBa
  have hBnot : Ba.erase a ∉ P.erase Ba := by
    intro h
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
    obtain ⟨x, hx⟩ := hBne
    exact hne (h4 _ hmem Ba hBa x hx (Finset.mem_of_mem_erase hx))
  refine ⟨insert (Ba.erase a) (P.erase Ba), ?_, Ba.erase a, Finset.mem_insert_self _ _, ?_⟩
  · rw [mem_parts]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro C hC x hx
      rcases Finset.mem_insert.mp hC with rfl | hC
      · obtain ⟨hxa, hx⟩ := Finset.mem_erase.mp hx
        rcases Finset.mem_insert.mp (h1 Ba hBa hx) with h | h
        · exact absurd h hxa
        · exact h
      · obtain ⟨hCB, hC⟩ := Finset.mem_erase.mp hC
        rcases Finset.mem_insert.mp (h1 C hC hx) with h | h
        · rw [h] at hx
          exact absurd (h4 C hC Ba hBa a hx haBa) hCB
        · exact h
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hBne.ne_empty h.symm
      · exact h2 (Finset.mem_of_mem_erase h)
    · intro i hi
      obtain ⟨C, hC, hiC⟩ := h3 i (Finset.mem_insert_of_mem hi)
      by_cases hCB : C = Ba
      · rw [hCB] at hiC
        refine ⟨Ba.erase a, Finset.mem_insert_self _ _, Finset.mem_erase.mpr ⟨?_, hiC⟩⟩
        rintro rfl
        exact ha hi
      · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCB, hC⟩), hiC⟩
    · intro C hC C' hC' i hiC hiC'
      rcases Finset.mem_insert.mp hC with rfl | hC <;>
        rcases Finset.mem_insert.mp hC' with rfl | hC'
      · rfl
      · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hC'
        exact absurd (h4 C' hmem Ba hBa i hiC' (Finset.mem_of_mem_erase hiC)) hne
      · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hC
        exact absurd (h4 C hmem Ba hBa i hiC (Finset.mem_of_mem_erase hiC')) hne
      · exact h4 C (Finset.mem_of_mem_erase hC) C' (Finset.mem_of_mem_erase hC') i hiC hiC'
  · rw [Finset.erase_insert hBnot, Finset.insert_erase haBa, Finset.insert_erase hBa]

theorem sum_parts_insert {S : Finset α} {a : α} (ha : a ∉ S) (G : Finset (Finset α) → ℤ) :
    ∑ P ∈ parts (insert a S), G P =
      ∑ P ∈ parts S, (G (insert {a} P) + ∑ B ∈ P, G (insert (insert a B) (P.erase B))) := by
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not (parts (insert a S)) (fun P => {a} ∈ P)]
  congr 1
  · symm
    refine Finset.sum_bij (fun P _ => insert {a} P) ?_ ?_ ?_ ?_
    · intro P hP
      exact Finset.mem_filter.mpr ⟨ins_mem ha hP, Finset.mem_insert_self _ _⟩
    · intro P hP Q hQ h
      have hPa : {a} ∉ P := fun h' => not_mem_block ha hP h' (Finset.mem_singleton_self a)
      have hQa : {a} ∉ Q := fun h' => not_mem_block ha hQ h' (Finset.mem_singleton_self a)
      rw [← Finset.erase_insert hPa, ← Finset.erase_insert hQa]
      exact congrArg (fun X => Finset.erase X {a}) h
    · intro P hP
      obtain ⟨hP, hs⟩ := Finset.mem_filter.mp hP
      obtain ⟨h1, h2⟩ := surj_ins ha hP hs
      exact ⟨P.erase {a}, h1, h2⟩
    · intro P _
      rfl
  · rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij (fun x _ => insert (insert a x.2) (x.1.erase x.2)) ?_ ?_ ?_ ?_
    · rintro ⟨P, B⟩ hx
      rw [Finset.mem_sigma] at hx
      refine Finset.mem_filter.mpr ⟨join_mem ha hx.1 hx.2, ?_⟩
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · obtain ⟨x, hx'⟩ := nonempty_block hx.1 hx.2
        have hxm : x ∈ insert a B := Finset.mem_insert_of_mem hx'
        rw [← h, Finset.mem_singleton] at hxm
        rw [hxm] at hx'
        exact not_mem_block ha hx.1 hx.2 hx'
      · exact not_mem_block ha hx.1 (Finset.mem_of_mem_erase h) (Finset.mem_singleton_self a)
    · rintro ⟨P, B⟩ hx ⟨Q, C⟩ hy h
      replace hx : P ∈ parts S ∧ B ∈ P := Finset.mem_sigma.mp hx
      replace hy : Q ∈ parts S ∧ C ∈ Q := Finset.mem_sigma.mp hy
      simp only at h
      have hB : insert a B = insert a C := by
        have hmem : insert a B ∈ insert (insert a C) (Q.erase C) := by
          rw [← h]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hmem with h' | h'
        · exact h'
        · exact absurd (Finset.mem_insert_self a B)
            (not_mem_block ha hy.1 (Finset.mem_of_mem_erase h'))
      have hBC : B = C := by
        rw [← Finset.erase_insert (not_mem_block ha hx.1 hx.2), hB,
          Finset.erase_insert (not_mem_block ha hy.1 hy.2)]
      subst hBC
      have nP : insert a B ∉ P.erase B := fun h' =>
        not_mem_block ha hx.1 (Finset.mem_of_mem_erase h') (Finset.mem_insert_self a B)
      have nQ : insert a B ∉ Q.erase B := fun h' =>
        not_mem_block ha hy.1 (Finset.mem_of_mem_erase h') (Finset.mem_insert_self a B)
      have hPQ : P.erase B = Q.erase B := by
        rw [← Finset.erase_insert nP, ← Finset.erase_insert nQ]
        exact congrArg (fun X => Finset.erase X (insert a B)) h
      have : P = Q := by
        rw [← Finset.insert_erase hx.2, ← Finset.insert_erase hy.2, hPQ]
      subst this
      rfl
    · intro P hP
      obtain ⟨hP, hs⟩ := Finset.mem_filter.mp hP
      obtain ⟨P', hP', B, hB, h⟩ := surj_join ha hP hs
      exact ⟨⟨P', B⟩, Finset.mem_sigma.mpr ⟨hP', hB⟩, h⟩
    · intro x _
      rfl

theorem biUnion_eq {S : Finset α} {P : Finset (Finset α)} (hP : P ∈ parts S) :
    P.biUnion (fun B => B) = S := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨B, hB, hx⟩
    exact h1 B hB hx
  · intro hx
    exact h3 x hx

theorem pdisj {S : Finset α} {P : Finset (Finset α)} (hP : P ∈ parts S) :
    (P : Set (Finset α)).PairwiseDisjoint (fun B => B) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  intro B hB B' hB' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne (h4 B hB B' hB' x hx hx')

theorem card_filter_eq {S : Finset α} {P : Finset (Finset α)} (hP : P ∈ parts S)
    (p : α → Prop) [DecidablePred p] :
    (S.filter p).card = ∑ B ∈ P, (B.filter p).card := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  rw [← biUnion_eq hP, Finset.filter_biUnion, Finset.card_biUnion]
  intro B hB B' hB' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne (h4 B hB B' hB' x (Finset.mem_of_mem_filter x hx) (Finset.mem_of_mem_filter x hx'))

def mu (t : ℕ) : ℤ := (-1 : ℤ) ^ (t - 1) * (Nat.factorial (t - 1) : ℤ)

theorem mu_one : mu 1 = 1 := by simp [mu]

theorem mu_succ {t : ℕ} (ht : 0 < t) : mu (t + 1) = -(t : ℤ) * mu t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [mu, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  ring

variable {β : Type*} [DecidableEq β]

def W (f : α → β) (S : Finset α) : ℤ :=
  ∑ P ∈ parts S, if (∀ B ∈ P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j') then ∏ B ∈ P, mu B.card else 0

theorem W_insert (f : α → β) {S : Finset α} {a : α} (ha : a ∉ S) :
    W f (insert a S) = W f S * (1 - ((S.filter (fun j => f j = f a)).card : ℤ)) := by
  unfold W
  rw [sum_parts_insert ha, Finset.sum_mul]
  beta_reduce
  apply Finset.sum_congr rfl
  intro P hP
  have hsP : {a} ∉ P := fun h' => not_mem_block ha hP h' (Finset.mem_singleton_self a)
  have hjoin : ∀ B ∈ P, insert a B ∉ P.erase B := fun B _ h' =>
    not_mem_block ha hP (Finset.mem_of_mem_erase h') (Finset.mem_insert_self a B)
  by_cases hm : ∀ B ∈ P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j'
  · rw [if_pos hm]
    have hm1 : ∀ B ∈ insert {a} P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j' := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · intro j hj j' hj'
        rw [Finset.mem_singleton] at hj hj'
        rw [hj, hj']
      · exact hm B hB
    rw [if_pos hm1, Finset.prod_insert hsP, Finset.card_singleton, mu_one, one_mul]
    have hterm : ∀ B ∈ P,
        (if (∀ C ∈ insert (insert a B) (P.erase B), ∀ j ∈ C, ∀ j' ∈ C, f j = f j') then
          ∏ C ∈ insert (insert a B) (P.erase B), mu C.card else 0) =
        -(((B.filter (fun j => f j = f a)).card : ℤ)) * ∏ C ∈ P, mu C.card := by
      intro B hB
      have hne := nonempty_block hP hB
      have haB := not_mem_block ha hP hB
      by_cases hall : ∀ j ∈ B, f j = f a
      · have hmj : ∀ C ∈ insert (insert a B) (P.erase B), ∀ j ∈ C, ∀ j' ∈ C, f j = f j' := by
          intro C hC
          rcases Finset.mem_insert.mp hC with rfl | hC
          · intro j hj j' hj'
            have e : ∀ x ∈ insert a B, f x = f a := by
              intro x hx
              rcases Finset.mem_insert.mp hx with h | h
              · rw [h]
              · exact hall x h
            rw [e j hj, e j' hj']
          · exact hm C (Finset.mem_of_mem_erase hC)
        rw [if_pos hmj, Finset.prod_insert (hjoin B hB), Finset.card_insert_of_notMem haB,
          mu_succ (Finset.card_pos.mpr hne), Finset.filter_true_of_mem hall, mul_assoc,
          Finset.mul_prod_erase P (fun C => mu C.card) hB]
      · have hmj : ¬ ∀ C ∈ insert (insert a B) (P.erase B), ∀ j ∈ C, ∀ j' ∈ C, f j = f j' := by
          intro h
          apply hall
          intro j hj
          exact h (insert a B) (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) a
            (Finset.mem_insert_self _ _)
        have hfe : B.filter (fun j => f j = f a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          push_neg at hall
          obtain ⟨j0, hj0, hfj0⟩ := hall
          intro x hx hfx
          exact hfj0 ((hm B hB j0 hj0 x hx).trans hfx)
        rw [if_neg hmj, hfe, Finset.card_empty]
        simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_neg_distrib, ← Nat.cast_sum,
      ← card_filter_eq hP]
    ring
  · rw [if_neg hm, zero_mul]
    have hm1 : ¬ ∀ B ∈ insert {a} P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j' :=
      fun h => hm (fun B hB => h B (Finset.mem_insert_of_mem hB))
    rw [if_neg hm1, zero_add]
    apply Finset.sum_eq_zero
    intro B hB
    rw [if_neg]
    intro h
    apply hm
    intro C hC
    by_cases hCB : C = B
    · rw [hCB]
      intro j hj j' hj'
      exact h (insert a B) (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) j'
        (Finset.mem_insert_of_mem hj')
    · exact h C (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCB, hC⟩))

theorem parts_empty : parts (∅ : Finset α) = {∅} := by
  ext P
  rw [mem_parts, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro B hB
    have : B = ∅ := Finset.subset_empty.mp (h1 B hB)
    rw [this] at hB
    exact h2 hB
  · rintro rfl
    simp

theorem W_eq (f : α → β) (S : Finset α) : W f S = if Set.InjOn f S then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    unfold W
    rw [parts_empty]
    simp
  | insert a s ha ih =>
    have hiff : Set.InjOn f ↑(insert a s) ↔ Set.InjOn f ↑s ∧ f a ∉ f '' ↑s := by
      rw [Finset.coe_insert]
      exact Set.injOn_insert (Finset.mem_coe.not.mpr ha)
    rw [W_insert f ha, ih]
    by_cases hi : Set.InjOn f (s : Set α)
    · rw [if_pos hi, one_mul]
      by_cases hfa : f a ∈ f '' (s : Set α)
      · obtain ⟨j, hj, hfj⟩ := hfa
        have hN : (s.filter (fun j => f j = f a)).card = 1 := by
          rw [Finset.card_eq_one]
          refine ⟨j, ?_⟩
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hfx⟩
            exact hi hx hj (hfx.trans hfj.symm)
          · rintro rfl
            exact ⟨hj, hfj⟩
        rw [hN, if_neg (fun h => (hiff.mp h).2 ⟨j, hj, hfj⟩)]
        norm_num
      · have hN : (s.filter (fun j => f j = f a)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hx hfx
          exact hfa ⟨x, hx, hfx⟩
        rw [hN, if_pos (hiff.mpr ⟨hi, hfa⟩)]
        norm_num
    · rw [if_neg hi, zero_mul, if_neg (fun h => hi (hiff.mp h).1)]

theorem expand [Fintype α] [Fintype β] (A : α → β → ℤ) {P : Finset (Finset α)}
    (hP : P ∈ parts (Finset.univ : Finset α)) :
    ∏ B ∈ P, ∑ c : β, ∏ j ∈ B, A j c =
      ∑ f : α → β, if (∀ B ∈ P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j') then ∏ i, A i (f i) else 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_parts.mp hP
  choose blk hblkP hxblk using fun x => h3 x (Finset.mem_univ x)
  have hrep : ∀ B : {B // B ∈ P}, ∃ x, x ∈ B.1 := fun B => nonempty_block hP B.2
  choose rep hrepB using hrep
  have hblk_eq : ∀ B ∈ P, ∀ x ∈ B, blk x = B :=
    fun B hB x hx => h4 _ (hblkP x) B hB x (hxblk x) hx
  rw [← Finset.sum_filter, ← Finset.prod_coe_sort P, Finset.prod_univ_sum,
    Fintype.piFinset_univ]
  refine Finset.sum_nbij' (fun h x => h ⟨blk x, hblkP x⟩) (fun f B => f (rep B))
    ?_ ?_ ?_ ?_ ?_
  · intro h _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro B hB j hj j' hj'
    have : (⟨blk j, hblkP j⟩ : {B // B ∈ P}) = ⟨blk j', hblkP j'⟩ :=
      Subtype.ext ((hblk_eq B hB j hj).trans (hblk_eq B hB j' hj').symm)
    simp only [this]
  · intro f _
    simp
  · intro h _
    funext B
    simp only []
    congr 1
    exact Subtype.ext (hblk_eq B.1 B.2 (rep B) (hrepB B))
  · intro f hf
    have hf' : ∀ B ∈ P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j' := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hf
    funext x
    exact hf' (blk x) (hblkP x) _ (hrepB _) x (hxblk x)
  · intro h _
    have e : ∀ B : {B // B ∈ P}, ∏ j ∈ B.1, A j (h B) = ∏ j ∈ B.1, A j (h ⟨blk j, hblkP j⟩) := by
      intro B
      apply Finset.prod_congr rfl
      intro j hj
      have : (⟨blk j, hblkP j⟩ : {B // B ∈ P}) = B := Subtype.ext (hblk_eq B.1 B.2 j hj)
      rw [this]
    rw [Finset.prod_congr rfl (fun B _ => e B),
      Finset.prod_coe_sort P (fun B => ∏ j ∈ B, A j (h ⟨blk j, hblkP j⟩)),
      ← Finset.prod_biUnion (pdisj hP), biUnion_eq hP]

theorem card_one_iff {P : Finset (Finset α)} (i : α) :
    (P.filter (fun B => i ∈ B)).card = 1 ↔
      (∃ B ∈ P, i ∈ B) ∧ ∀ B ∈ P, ∀ B' ∈ P, i ∈ B → i ∈ B' → B = B' := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨B0, hB0⟩
    have hmem : ∀ B, B ∈ P ∧ i ∈ B ↔ B = B0 := fun B => by
      rw [← Finset.mem_singleton, ← hB0, Finset.mem_filter]
    refine ⟨⟨B0, ((hmem B0).mpr rfl).1, ((hmem B0).mpr rfl).2⟩, ?_⟩
    intro B hB B' hB' hi hi'
    rw [(hmem B).mp ⟨hB, hi⟩, (hmem B').mp ⟨hB', hi'⟩]
  · rintro ⟨⟨B0, hB0, hi0⟩, huniq⟩
    refine ⟨B0, ?_⟩
    ext B
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hB, hi⟩
      exact huniq B hB B0 hB0 hi hi0
    · rintro rfl
      exact ⟨hB0, hi0⟩

theorem parts_univ [Fintype α] :
    (Finset.univ.filter (fun P : Finset (Finset α) =>
      ∅ ∉ P ∧ ∀ i : α, (P.filter (fun B => i ∈ B)).card = 1)) = parts Finset.univ := by
  ext P
  rw [Finset.mem_filter, mem_parts]
  simp only [Finset.mem_univ, true_and, card_one_iff]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨fun B _ => Finset.subset_univ B, h2, fun i _ => (h i).1, ?_⟩
    intro B hB B' hB' i hi hi'
    exact (h i).2 B hB B' hB' hi hi'
  · rintro ⟨_, h2, h3, h4⟩
    exact ⟨h2, fun i => ⟨h3 i (by simp),
      fun B hB B' hB' hi hi' => h4 B hB B' hB' i hi hi'⟩⟩

theorem main (m n : ℕ) (A : Fin m → Fin n → ℤ) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f),
      ∏ i : Fin m, A i (f i)) =
    ∑ P ∈ Finset.univ.filter (fun P : Finset (Finset (Fin m)) =>
        ∅ ∉ P ∧ ∀ i : Fin m, (P.filter (fun B => i ∈ B)).card = 1), ∏ B ∈ P,
      ((-1 : ℤ)^(B.card-1) * (Nat.factorial (B.card-1) : ℤ) *
        ∑ c : Fin n, ∏ j ∈ B, A j c) := by
  have hp : (Finset.univ.filter (fun P : Finset (Finset (Fin m)) =>
      ∅ ∉ P ∧ ∀ i : Fin m, (P.filter (fun B => i ∈ B)).card = 1)) =
      PEqualNP.Outside.L_lib_453.parts Finset.univ := by
    convert PEqualNP.Outside.L_lib_453.parts_univ (α := Fin m)
  rw [hp]
  have key : ∀ P ∈ PEqualNP.Outside.L_lib_453.parts (Finset.univ : Finset (Fin m)),
      ∏ B ∈ P, ((-1 : ℤ) ^ (B.card - 1) * (Nat.factorial (B.card - 1) : ℤ) *
        ∑ c : Fin n, ∏ j ∈ B, A j c) =
      ∑ f : Fin m → Fin n, (∏ i, A i (f i)) *
        (if (∀ B ∈ P, ∀ j ∈ B, ∀ j' ∈ B, f j = f j') then
          ∏ B ∈ P, PEqualNP.Outside.L_lib_453.mu B.card else 0) := by
    intro P hP
    rw [Finset.prod_mul_distrib, PEqualNP.Outside.L_lib_453.expand A hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs
    · simp only [PEqualNP.Outside.L_lib_453.mu]
      ring
    · simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Finset.mul_sum]
  have hW := PEqualNP.Outside.L_lib_453.W_eq f (Finset.univ : Finset (Fin m))
  unfold PEqualNP.Outside.L_lib_453.W at hW
  have hinj : Set.InjOn f ↑(Finset.univ : Finset (Fin m)) ↔ Function.Injective f := by
    rw [Finset.coe_univ, Set.injOn_univ]
  calc (if Function.Injective f then ∏ i, A i (f i) else 0)
      = (∏ i, A i (f i)) * (if Function.Injective f then 1 else 0) := by
        split_ifs <;> simp
    _ = _ := by
        congr 1
        by_cases hf : Function.Injective f
        · rw [if_pos (hinj.mpr hf)] at hW
          rw [if_pos hf]
          convert hW.symm
        · rw [if_neg (fun h => hf (hinj.mp h))] at hW
          rw [if_neg hf]
          convert hW.symm

end PEqualNP.Outside.L_lib_453


theorem PEqualNP.Outside.L_lib_453 : (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ),
  let parts := Finset.univ.filter (fun P : Finset (Finset (Fin m)) =>
    ∅ ∉ P ∧ ∀ i : Fin m, (P.filter (fun B => i ∈ B)).card = 1)
  (∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => Function.Injective f),
    ∏ i : Fin m, A i (f i)) =
    ∑ P ∈ parts, ∏ B ∈ P,
      ((-1 : ℤ)^(B.card-1) * (Nat.factorial (B.card-1) : ℤ) *
        ∑ c : Fin n, ∏ j ∈ B, A j c)) := by
  intro m n A
  exact PEqualNP.Outside.L_lib_453.main m n A
