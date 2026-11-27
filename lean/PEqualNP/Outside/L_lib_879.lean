import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_879_aux

theorem sum_pow_union {α : Type} [DecidableEq α] (K : Finset α) :
    ∀ M : Finset α, Disjoint K M → ∀ f : Finset α → ℤ,
      ∑ S ∈ (K ∪ M).powerset, f S = ∑ T ∈ M.powerset, ∑ J ∈ K.powerset, f (J ∪ T) := by
  intro M
  refine Finset.induction_on M ?_ ?_
  · intro _ f
    simp
  · intro a M ha ih hd f
    rw [Finset.disjoint_insert_right] at hd
    have haKM : a ∉ K ∪ M := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hd.1, ha⟩
    rw [Finset.union_insert, Finset.sum_powerset_insert haKM, Finset.sum_powerset_insert ha,
      ih hd.2 f, ih hd.2 (fun S => f (insert a S))]
    simp only [Finset.union_insert]

theorem mob0 {α : Type} [DecidableEq α] (f : Finset α → ℤ) :
    ∀ X : Finset α, (∀ M, M ⊆ X → ∑ T ∈ M.powerset, f T = 0) → f X = 0 := by
  intro X
  refine Finset.strongInduction (p := fun X => (∀ M, M ⊆ X → ∑ T ∈ M.powerset, f T = 0) → f X = 0) ?_ X
  intro X ih h
  have h1 := h X (Finset.Subset.refl X)
  rw [Finset.sum_eq_single_of_mem X (Finset.mem_powerset_self X)] at h1
  · exact h1
  · intro T hT hne
    have hTX : T ⊆ X := Finset.mem_powerset.mp hT
    have hss : T ⊂ X := Finset.ssubset_iff_subset_ne.mpr ⟨hTX, hne⟩
    exact ih T hss (fun M hM => h M (hM.trans hTX))

theorem absA {α : Type} [DecidableEq α] (valid : Finset α → Prop)
    (hv : ∀ S T, valid S → T ⊆ S → valid T) (F c : Finset α → ℤ) (C : ℤ)
    (hF : ∀ N, F N = C + ∑ S ∈ N.powerset, c S) (I : Finset α) (d : ℕ) :
    (∀ K, K ⊆ I → valid K → ∃ h : Finset α → ℤ, ∀ M : Finset α, Disjoint M I → valid (K ∪ M) →
        F (K ∪ M) = ∑ T ∈ M.powerset.filter (fun V => V.card ≤ d), h T) ↔
      ∀ S, valid S → c S ≠ 0 → (S \ I).card ≤ d := by
  constructor
  · intro L S hS hc
    by_contra hlt
    rw [not_le] at hlt
    have hT0 : S \ I ≠ ∅ := by
      intro h0
      rw [h0] at hlt
      simp at hlt
    have key : ∀ K, K ⊆ S ∩ I → ∑ J ∈ K.powerset, c (J ∪ S \ I) = 0 := by
      intro K hK
      obtain ⟨h, hh⟩ := L K (hK.trans Finset.inter_subset_right)
        (hv _ _ hS (hK.trans Finset.inter_subset_left))
      have hd : Disjoint K (S \ I) :=
        Finset.disjoint_sdiff.mono_left (hK.trans Finset.inter_subset_right)
      have m := mob0 (fun T => (if T = ∅ then C else 0) + ∑ J ∈ K.powerset, c (J ∪ T)
          - (if T.card ≤ d then h T else 0)) (S \ I) ?_
      · simp only [if_neg hT0, if_neg (not_le.mpr hlt)] at m
        simpa using m
      · intro M hM
        have hMI : Disjoint M I := Finset.sdiff_disjoint.mono_left hM
        have hval : valid (K ∪ M) := hv _ _ hS
          (Finset.union_subset (hK.trans Finset.inter_subset_left)
            (hM.trans Finset.sdiff_subset))
        have e := hh M hMI hval
        rw [hF, sum_pow_union K M (hd.mono_right hM) c, Finset.sum_filter] at e
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← e]
        simp
    have fin := mob0 (fun J => c (J ∪ S \ I)) (S ∩ I) key
    have hSe : S ∩ I ∪ S \ I = S := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    apply hc
    simpa only [hSe] using fin
  · intro H K hKI hK
    refine ⟨fun T => (if T = ∅ then C else 0) + ∑ J ∈ K.powerset, c (J ∪ T), ?_⟩
    intro M hMI hKM
    have hd : Disjoint K M := (Disjoint.mono_right hKI hMI).symm
    rw [Finset.sum_filter_of_ne, hF, sum_pow_union K M hd c, Finset.sum_add_distrib]
    · simp
    · intro T hT hne
      by_contra hcard
      rw [not_le] at hcard
      have hTM : T ⊆ M := Finset.mem_powerset.mp hT
      apply hne
      have hTne : T ≠ ∅ := by
        intro h0
        rw [h0] at hcard
        simp at hcard
      simp only [if_neg hTne, zero_add]
      apply Finset.sum_eq_zero
      intro J hJ
      have hJK : J ⊆ K := Finset.mem_powerset.mp hJ
      by_contra hcne
      have h1 := H (J ∪ T) (hv _ _ hKM (Finset.union_subset_union hJK hTM)) hcne
      have h2 : T ⊆ (J ∪ T) \ I := by
        intro x hx
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_union_right _ hx, fun hxI => Finset.disjoint_left.mp hMI (hTM hx) hxI⟩
      have h3 := Finset.card_le_card h2
      omega

theorem key {α : Type} [DecidableEq α] (B N : Finset α) :
    ∑ S ∈ N.powerset, (if S ⊆ B then (-1 : ℤ) ^ S.card else 0) =
      if (N ∩ B).Nonempty then 0 else 1 := by
  rw [← Finset.sum_filter]
  have h : N.powerset.filter (fun S => S ⊆ B) = (N ∩ B).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  rw [h, Finset.sum_powerset_neg_one_pow_card]
  by_cases h0 : N ∩ B = ∅
  · simp [h0]
  · simp [h0, Finset.nonempty_iff_ne_empty]

theorem pert {α : Type} [DecidableEq α] (B N : Finset α) (f g : Bool) :
    (if (f || decide (N ∩ B).Nonempty) ≠ g then (1 : ℤ) else 0) =
      (if g = true then 0 else 1) + ∑ S ∈ N.powerset, (-1 : ℤ) ^ S.card *
        ((if f = false ∧ S ⊆ B ∧ g = true then 1 else 0) -
          (if f = false ∧ S ⊆ B ∧ g = false then 1 else 0)) := by
  have k := key B N
  cases f <;> cases g
  · have e : ∀ S : Finset α, (-1 : ℤ) ^ S.card *
        ((if false = false ∧ S ⊆ B ∧ false = true then 1 else 0) -
          (if false = false ∧ S ⊆ B ∧ false = false then 1 else 0)) =
        -(if S ⊆ B then (-1 : ℤ) ^ S.card else 0) := by
      intro S
      by_cases h : S ⊆ B <;> simp [h]
    rw [Finset.sum_congr rfl (fun S _ => e S), Finset.sum_neg_distrib, k]
    by_cases h : (N ∩ B).Nonempty <;> simp [h]
  · have e : ∀ S : Finset α, (-1 : ℤ) ^ S.card *
        ((if false = false ∧ S ⊆ B ∧ true = true then 1 else 0) -
          (if false = false ∧ S ⊆ B ∧ true = false then 1 else 0)) =
        (if S ⊆ B then (-1 : ℤ) ^ S.card else 0) := by
      intro S
      by_cases h : S ⊆ B <;> simp [h]
    rw [Finset.sum_congr rfl (fun S _ => e S), k]
    by_cases h : (N ∩ B).Nonempty <;> simp [h]
  · simp
  · simp

theorem expand {α : Type} [DecidableEq α] {q : ℕ} (D : Fin q → Finset α)
    (fixed target : Fin q → Bool) (N : Finset α) :
    (((Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((N ∩ D t).Nonempty)) ≠ target t)).card : ℕ) : ℤ) =
      (∑ t : Fin q, (if target t = true then (0 : ℤ) else 1)) + ∑ S ∈ N.powerset,
        (-1 : ℤ) ^ S.card *
        (((Finset.univ.filter (fun t : Fin q =>
            fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
          ((Finset.univ.filter (fun t : Fin q =>
            fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ)) := by
  have e : ∀ S : Finset α,
      (((Finset.univ.filter (fun t : Fin q =>
            fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
          ((Finset.univ.filter (fun t : Fin q =>
            fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ)) =
        ∑ t : Fin q, ((if fixed t = false ∧ S ⊆ D t ∧ target t = true then (1 : ℤ) else 0) -
          (if fixed t = false ∧ S ⊆ D t ∧ target t = false then 1 else 0)) := by
    intro S
    rw [Finset.sum_sub_distrib, Finset.card_filter, Finset.card_filter]
    push_cast
    rfl
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  exact pert (D t) N (fixed t) (target t)

end PEqualNP.Outside.L_lib_879_aux

theorem PEqualNP.Outside.L_lib_879 : ∀ (k q : Nat) (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool),
  let valid := fun (M : Finset (Finset (Fin k))) =>
    (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)
  let err := fun (M : Finset (Finset (Fin k))) =>
    (Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card
  let signed := fun (S : Finset (Finset (Fin k))) =>
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)
  let low := fun (I : Finset (Finset (Fin k))) (d : Nat) =>
    ∀ K ⊆ I, valid K → ∃ h : Finset (Finset (Fin k)) → Int,
      ∀ M : Finset (Finset (Fin k)), Disjoint M I → valid (K ∪ M) →
        (err (K ∪ M) : Int) =
          ∑ T ∈ M.powerset.filter (fun V => V.card ≤ d), h T
  (∀ (I : Finset (Finset (Fin k))) (d : Nat), low I d ↔
    ∀ S, valid S → signed S ≠ 0 → (S \ I).card ≤ d) ∧
  ((∀ S, valid S → 3 ≤ S.card → signed S = 0) →
    ∀ j : Nat, ((∃ I : Finset (Finset (Fin k)), I.card ≤ j ∧ low I 1) ↔
      ∃ J : Finset (Finset (Fin k)), J.card ≤ j ∧
        ∀ a b : Finset (Fin k), a.card = 2 → b.card = 2 → Disjoint a b →
          signed {a,b} ≠ 0 → a ∈ J ∨ b ∈ J)) := by
  intro k q D fixed target valid err signed low
  have hv : ∀ S T, valid S → T ⊆ S → valid T := by
    intro S T hS hT
    exact ⟨fun e he => hS.1 e (hT he), fun e he g hg => hS.2 e (hT he) g (hT hg)⟩
  have hA : ∀ (I : Finset (Finset (Fin k))) (d : Nat), low I d ↔
      ∀ S, valid S → signed S ≠ 0 → (S \ I).card ≤ d := by
    intro I d
    refine (PEqualNP.Outside.L_lib_879_aux.absA valid hv (fun N => (err N : ℤ))
      (fun S => (-1 : ℤ) ^ S.card * signed S)
      (∑ t : Fin q, (if target t = true then (0 : ℤ) else 1))
      (fun N => PEqualNP.Outside.L_lib_879_aux.expand D fixed target N) I d).trans ?_
    refine forall_congr' (fun S => forall_congr' (fun _ => ?_))
    have hne : ((-1 : ℤ) ^ S.card) ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [ne_eq, mul_eq_zero, hne, false_or]
  refine ⟨hA, ?_⟩
  intro h3 j
  constructor
  · rintro ⟨I, hI, hlow⟩
    refine ⟨I, hI, ?_⟩
    intro a b ha hb hab hs
    have hne : a ≠ b := by
      intro h
      subst h
      rw [disjoint_self, Finset.bot_eq_empty] at hab
      rw [hab] at ha
      simp at ha
    have hval : valid {a, b} := by
      constructor
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact ha
        · exact hb
      · intro e he g hg heg
        simp only [Finset.mem_insert, Finset.mem_singleton] at he hg
        rcases he with rfl | rfl <;> rcases hg with rfl | rfl
        · exact absurd rfl heg
        · exact hab
        · exact hab.symm
        · exact absurd rfl heg
    have hc := (hA I 1).1 hlow {a, b} hval hs
    by_contra hcon
    rw [not_or] at hcon
    have hsd : ({a, b} : Finset (Finset (Fin k))) \ I = {a, b} := by
      rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hcon.1
      · exact hcon.2
    rw [hsd, Finset.card_pair hne] at hc
    omega
  · rintro ⟨J, hJ, h⟩
    refine ⟨J, hJ, (hA J 1).2 ?_⟩
    intro S hS hs
    by_contra hcon
    rw [not_le] at hcon
    have hS2 : S.card ≤ 2 := by
      by_contra h2
      exact hs (h3 S hS (by omega))
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
    rw [Finset.mem_sdiff] at ha hb
    have hsub : ({a, b} : Finset (Finset (Fin k))) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha.1
      · exact hb.1
    have heq : ({a, b} : Finset (Finset (Fin k))) = S :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hS2)
    rw [← heq] at hs
    rcases h a b (hS.1 a ha.1) (hS.1 b hb.1) (hS.2 a ha.1 b hb.1 hab) hs with h1 | h1
    · exact ha.2 h1
    · exact hb.2 h1
