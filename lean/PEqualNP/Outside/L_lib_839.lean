import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_839

open Finset Function

theorem tle {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem fle (b : Bool) : false ≤ b := by cases b <;> decide

theorem inter_mem {α : Type} [DecidableEq α] {i : α} {s : Finset α} (h : i ∈ s) :
    {i} ∩ s = {i} := by
  rw [Finset.singleton_inter]
  simp [h]

theorem inter_not {α : Type} [DecidableEq α] {i : α} {s : Finset α} (h : i ∉ s) :
    {i} ∩ s = ∅ := by
  rw [Finset.singleton_inter]
  simp [h]

theorem core (n m : Nat) (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool)
    (P : Finset (Fin n)) (Q : Finset (Fin m))
    (hP : P = (Finset.univ.erase r) \ R) (hQ : Q = (Finset.univ.erase c) \ K)
    (hrR : r ∉ R) (hcK : c ∉ K) (hA : Function.Injective A)
    (hAT : Function.Injective (fun j i => A i j))
    (hH0 : H ∅ ∅ = false) (hD0 : D ∅ ∅ false = false)
    (hHm : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → H X Y ≤ H X' Y')
    (hDm : ∀ X X' Y Y' a b, X ⊆ X' → Y ⊆ Y' → a ≤ b → D X Y a ≤ D X' Y' b)
    (hAD : ∀ i j, A i j = D ({i} ∩ P) ({j} ∩ Q) (!(H ({i} ∩ R) ({j} ∩ K)))) :
    (A r c = false → R.card ≤ 1 ∧ K.card ≤ 1 ∧
      ∀ X ⊆ R, ∀ Y ⊆ K, H X Y = decide (X.Nonempty ∨ Y.Nonempty)) ∧
    (A r c = true → P.card ≤ 1 ∧ Q.card ≤ 1 ∧
      ∀ X ⊆ P, ∀ Y ⊆ Q, ∀ b : Bool, D X Y b = (b || decide (X.Nonempty ∨ Y.Nonempty))) := by
  have rP : r ∉ P := by rw [hP]; simp
  have cQ : c ∉ Q := by rw [hQ]; simp
  have RP : ∀ i, i ∈ R → i ∉ P := by intro i hi; rw [hP]; simp [hi]
  have KQ : ∀ j, j ∈ K → j ∉ Q := by intro j hj; rw [hQ]; simp [hj]
  have PR : ∀ i, i ∈ P → i ∉ R := by intro i hi h; exact RP i h hi
  have QK : ∀ j, j ∈ Q → j ∉ K := by intro j hj h; exact KQ j h hj
  have hrow : ∀ j, A r j = D ∅ ({j} ∩ Q) (!(H ∅ ({j} ∩ K))) := by
    intro j; rw [hAD, inter_not rP, inter_not hrR]
  have hcol : ∀ i, A i c = D ({i} ∩ P) ∅ (!(H ({i} ∩ R) ∅)) := by
    intro i; rw [hAD, inter_not cQ, inter_not hcK]
  have hrc : A r c = D ∅ ∅ true := by
    rw [hrow, inter_not cQ, inter_not hcK, hH0]; rfl
  have colEq : ∀ j, (∀ i, A i j = A i c) → j = c := by
    intro j h
    exact hAT (show (fun j i => A i j) j = (fun j i => A i j) c from funext h)
  have colEq2 : ∀ j j', (∀ i, A i j = A i j') → j = j' := by
    intro j j' h
    exact hAT (show (fun j i => A i j) j = (fun j i => A i j) j' from funext h)
  constructor
  · intro hf
    have hD1 : D ∅ ∅ true = false := by rw [← hrc]; exact hf
    have hDe : ∀ b, D ∅ ∅ b = false := by intro b; cases b; exact hD0; exact hD1
    have hiR : ∀ i ∈ R, ∀ j, A i j = D ∅ ({j} ∩ Q) (!(H {i} ({j} ∩ K))) := by
      intro i hi j; rw [hAD, inter_not (RP i hi), inter_mem hi]
    have hjK : ∀ j ∈ K, ∀ i, A i j = D ({i} ∩ P) ∅ (!(H ({i} ∩ R) {j})) := by
      intro j hj i; rw [hAD, inter_not (KQ j hj), inter_mem hj]
    have HR : ∀ i ∈ R, H {i} ∅ = true := by
      intro i hi
      by_contra hne
      have hf' : H {i} ∅ = false := by simpa using hne
      have e : i = r := hA (funext fun j => by
        rw [hiR i hi j, hrow j]
        by_cases hj : j ∈ K
        · rw [inter_not (KQ j hj), hDe, hDe]
        · rw [inter_not hj, hf', hH0])
      exact hrR (e ▸ hi)
    have HK : ∀ j ∈ K, H ∅ {j} = true := by
      intro j hj
      by_contra hne
      have hf' : H ∅ {j} = false := by simpa using hne
      have e : j = c := colEq j (fun i => by
        rw [hjK j hj i, hcol i]
        by_cases hi : i ∈ R
        · rw [inter_not (RP i hi), hDe, hDe]
        · rw [inter_not hi, hf', hH0])
      exact hcK (e ▸ hj)
    have Hup : ∀ i ∈ R, ∀ X Y, i ∈ X → H X Y = true := by
      intro i hi X Y hX
      have h := hHm {i} X ∅ Y (Finset.singleton_subset_iff.2 hX) (Finset.empty_subset _)
      rw [HR i hi] at h
      exact tle h
    have Kup : ∀ j ∈ K, ∀ X Y, j ∈ Y → H X Y = true := by
      intro j hj X Y hY
      have h := hHm ∅ X {j} Y (Finset.empty_subset _) (Finset.singleton_subset_iff.2 hY)
      rw [HK j hj] at h
      exact tle h
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.card_le_one.2 (fun i hi i' hi' => hA (funext fun j => ?_))
      rw [hiR i hi j, hiR i' hi' j, Hup i hi _ _ (Finset.mem_singleton_self _),
        Hup i' hi' _ _ (Finset.mem_singleton_self _)]
    · refine Finset.card_le_one.2 (fun j hj j' hj' => colEq2 j j' (fun i => ?_))
      rw [hjK j hj i, hjK j' hj' i, Kup j hj _ _ (Finset.mem_singleton_self _),
        Kup j' hj' _ _ (Finset.mem_singleton_self _)]
    · intro X hX Y hY
      by_cases hx : X.Nonempty
      · obtain ⟨i, hi⟩ := hx
        rw [Hup i (hX hi) X Y hi]
        exact (decide_eq_true (Or.inl ⟨i, hi⟩)).symm
      · by_cases hy : Y.Nonempty
        · obtain ⟨j, hj⟩ := hy
          rw [Kup j (hY hj) X Y hj]
          exact (decide_eq_true (Or.inr ⟨j, hj⟩)).symm
        · rw [Finset.not_nonempty_iff_eq_empty] at hx hy
          subst hx hy
          simp [hH0]
  · intro ht
    have hD1 : D ∅ ∅ true = true := by rw [← hrc]; exact ht
    have hDb : ∀ b, D ∅ ∅ b = b := by intro b; cases b; exact hD0; exact hD1
    have Dup0 : ∀ X Y, D X Y true = true := by
      intro X Y
      have h := hDm ∅ X ∅ Y true true (Finset.empty_subset _) (Finset.empty_subset _) le_rfl
      rw [hD1] at h
      exact tle h
    have hiP : ∀ i ∈ P, ∀ j, A i j = D {i} ({j} ∩ Q) (!(H ∅ ({j} ∩ K))) := by
      intro i hi j; rw [hAD, inter_mem hi, inter_not (PR i hi)]
    have hjQ : ∀ j ∈ Q, ∀ i, A i j = D ({i} ∩ P) {j} (!(H ({i} ∩ R) ∅)) := by
      intro j hj i; rw [hAD, inter_mem hj, inter_not (QK j hj)]
    have DP : ∀ i ∈ P, D {i} ∅ false = true := by
      intro i hi
      by_contra hne
      have hf' : D {i} ∅ false = false := by simpa using hne
      have e : i = r := hA (funext fun j => by
        rw [hiP i hi j, hrow j]
        by_cases hj : j ∈ K
        · rw [inter_not (KQ j hj), inter_mem hj]
          generalize (!(H ∅ {j})) = b
          cases b
          · rw [hf', hD0]
          · rw [Dup0, Dup0]
        · rw [inter_not hj, hH0]
          exact (Dup0 _ _).trans (Dup0 _ _).symm)
      exact rP (e ▸ hi)
    have DQ : ∀ j ∈ Q, D ∅ {j} false = true := by
      intro j hj
      by_contra hne
      have hf' : D ∅ {j} false = false := by simpa using hne
      have e : j = c := colEq j (fun i => by
        rw [hjQ j hj i, hcol i]
        by_cases hi : i ∈ R
        · rw [inter_not (RP i hi), inter_mem hi]
          generalize (!(H {i} ∅)) = b
          cases b
          · rw [hf', hD0]
          · rw [Dup0, Dup0]
        · rw [inter_not hi, hH0]
          exact (Dup0 _ _).trans (Dup0 _ _).symm)
      exact cQ (e ▸ hj)
    have Pup : ∀ i ∈ P, ∀ X Y b, i ∈ X → D X Y b = true := by
      intro i hi X Y b hX
      have h := hDm {i} X ∅ Y false b (Finset.singleton_subset_iff.2 hX)
        (Finset.empty_subset _) (fle b)
      rw [DP i hi] at h
      exact tle h
    have Qup : ∀ j ∈ Q, ∀ X Y b, j ∈ Y → D X Y b = true := by
      intro j hj X Y b hY
      have h := hDm ∅ X {j} Y false b (Finset.empty_subset _)
        (Finset.singleton_subset_iff.2 hY) (fle b)
      rw [DQ j hj] at h
      exact tle h
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.card_le_one.2 (fun i hi i' hi' => hA (funext fun j => ?_))
      rw [hiP i hi j, hiP i' hi' j, Pup i hi _ _ _ (Finset.mem_singleton_self _),
        Pup i' hi' _ _ _ (Finset.mem_singleton_self _)]
    · refine Finset.card_le_one.2 (fun j hj j' hj' => colEq2 j j' (fun i => ?_))
      rw [hjQ j hj i, hjQ j' hj' i, Qup j hj _ _ _ (Finset.mem_singleton_self _),
        Qup j' hj' _ _ _ (Finset.mem_singleton_self _)]
    · intro X hX Y hY b
      by_cases hx : X.Nonempty
      · obtain ⟨i, hi⟩ := hx
        rw [Pup i (hX hi) X Y b hi, decide_eq_true (Or.inl ⟨i, hi⟩), Bool.or_true]
      · by_cases hy : Y.Nonempty
        · obtain ⟨j, hj⟩ := hy
          rw [Qup j (hY hj) X Y b hj, decide_eq_true (Or.inr ⟨j, hj⟩), Bool.or_true]
        · rw [Finset.not_nonempty_iff_eq_empty] at hx hy
          subst hx hy
          simp [hDb]

end PEqualNP.Outside.L_lib_839

open PEqualNP.Outside.L_lib_839 in
theorem PEqualNP.Outside.L_lib_839 :
∀ (n m : Nat) (A : Fin n → Fin m → Bool) (r : Fin n) (c : Fin m)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
  let P := (Finset.univ.erase r) \ R
  let Q := (Finset.univ.erase c) \ K
  r ∉ R → c ∉ K → Function.Injective A → Function.Injective (fun j i => A i j) →
  H ∅ ∅ = false → D ∅ ∅ false = false →
  (∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → H X Y ≤ H X' Y') →
  (∀ X X' Y Y' a b, X ⊆ X' → Y ⊆ Y' → a ≤ b → D X Y a ≤ D X' Y' b) →
  (∀ i j, A i j = D ({i} ∩ P) ({j} ∩ Q) (!(H ({i} ∩ R) ({j} ∩ K)))) →
  (A r c = false → R.card ≤ 1 ∧ K.card ≤ 1 ∧
    ∀ X ⊆ R, ∀ Y ⊆ K, H X Y = decide (X.Nonempty ∨ Y.Nonempty)) ∧
  (A r c = true → P.card ≤ 1 ∧ Q.card ≤ 1 ∧
    ∀ X ⊆ P, ∀ Y ⊆ Q, ∀ b : Bool, D X Y b = (b || decide (X.Nonempty ∨ Y.Nonempty))) := by
  intro n m A r c R K H D P Q hrR hcK hA hAT hH0 hD0 hHm hDm hAD
  exact core n m A r c R K H D P Q rfl rfl hrR hcK hA hAT hH0 hD0 hHm hDm hAD
