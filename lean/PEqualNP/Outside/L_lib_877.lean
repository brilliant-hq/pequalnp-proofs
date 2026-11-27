import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_877

open Finset

theorem inner {β : Type} [DecidableEq β] (A M : Finset β) :
    (∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
      (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (if M ∩ A = ∅ then 1 else 0) - 1 := by
  have h1 : (∑ S ∈ M.powerset, (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (if M ∩ A = ∅ then 1 else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_powerset_neg_one_pow_card]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  have h2 : (∑ S ∈ M.powerset, (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) =
      (∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
        (if S ⊆ A then (-1 : ℤ) ^ S.card else 0)) +
      ∑ S ∈ M.powerset.filter (fun T => ¬ T.Nonempty),
        (if S ⊆ A then (-1 : ℤ) ^ S.card else 0) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h3 : M.powerset.filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h3, Finset.sum_singleton] at h2
  simp only [Finset.empty_subset, ite_true, Finset.card_empty, pow_zero] at h2
  linarith

theorem per_test {β : Type} [DecidableEq β] (A M : Finset β) (f g : Bool) :
    ((if (f || decide ((M ∩ A).Nonempty)) ≠ g then 1 else 0 : ℤ)) =
      (if (f || decide ((∅ ∩ A).Nonempty)) ≠ g then 1 else 0 : ℤ) +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty),
        (-1 : ℤ) ^ S.card * (if f = false ∧ S ⊆ A then (if g then 1 else -1) else 0) := by
  have key : ∀ S : Finset β, (-1 : ℤ) ^ S.card * (if f = false ∧ S ⊆ A then (if g then 1 else -1) else 0)
      = (if f = false then (if g then 1 else -1) else 0) * (if S ⊆ A then (-1 : ℤ) ^ S.card else 0) := by
    intro S
    by_cases hf : f = false <;> by_cases hS : S ⊆ A <;> simp [hf, hS, mul_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, inner]
  have hne : ((M ∩ A).Nonempty) ↔ ¬ (M ∩ A = ∅) := Finset.nonempty_iff_ne_empty
  by_cases hE : M ∩ A = ∅
  · have : ¬ (M ∩ A).Nonempty := by rw [hne]; simp [hE]
    cases f <;> cases g <;> simp [hE, this]
  · have : (M ∩ A).Nonempty := by rw [hne]; exact hE
    cases f <;> cases g <;> simp [hE, this]

theorem signed_eq {ι β : Type} [Fintype ι] [DecidableEq β] (D : ι → Finset β) (fixed target : ι → Bool)
    (S : Finset β) :
    ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
    ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ) =
    ∑ t, (if fixed t = false ∧ S ⊆ D t then (if target t then 1 else -1) else 0 : ℤ) := by
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hf : fixed t = false <;> by_cases hS : S ⊆ D t <;> cases h : target t <;> simp [hf, hS, h]

theorem expand {ι β : Type} [Fintype ι] [DecidableEq β] (D : ι → Finset β) (fixed target : ι → Bool)
    (M : Finset β) :
    (((Finset.univ.filter (fun t : ι =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card : ℕ) : ℤ) =
    (((Finset.univ.filter (fun t : ι =>
      (fixed t || decide ((∅ ∩ D t).Nonempty)) ≠ target t)).card : ℕ) : ℤ) +
    ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : ℤ) ^ S.card *
      (((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : ℤ) -
      ((Finset.univ.filter (fun t : ι => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : ℤ)) := by
  simp_rw [signed_eq, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  exact per_test (D t) M (fixed t) (target t)

theorem mobius {β : Type} [DecidableEq β] (P : Finset β → Prop)
    (hP : ∀ M S, P M → S ⊆ M → P S) (g h : Finset β → ℤ)
    (H : ∀ M, P M → ∑ S ∈ M.powerset, g S = ∑ S ∈ M.powerset, h S) :
    ∀ M, P M → g M = h M := by
  intro M
  induction M using Finset.strongInduction with
  | H M ih =>
    intro hM
    have e1 := Finset.sum_erase_add M.powerset g (Finset.mem_powerset_self M)
    have e2 := Finset.sum_erase_add M.powerset h (Finset.mem_powerset_self M)
    have e3 : ∑ S ∈ M.powerset.erase M, g S = ∑ S ∈ M.powerset.erase M, h S := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mem_erase, Finset.mem_powerset] at hS
      have hss : S ⊂ M := Finset.ssubset_iff_subset_ne.mpr ⟨hS.2, hS.1⟩
      exact ih S hss (hP M S hM hS.2)
    have := H M hM
    linarith

theorem split_empty {β : Type} [DecidableEq β] (M : Finset β) (c : ℤ) (f : Finset β → ℤ) :
    ∑ S ∈ M.powerset, (if S = ∅ then c else f S) =
      c + ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), f S := by
  rw [Finset.sum_ite]
  have h3 : M.powerset.filter (fun T => T = ∅) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h; subst h; exact ⟨Finset.empty_subset _, rfl⟩
  have h4 : M.powerset.filter (fun T => ¬ T = ∅) = M.powerset.filter (fun T => T.Nonempty) := by
    apply Finset.filter_congr
    intro S _
    rw [Finset.nonempty_iff_ne_empty]
  rw [h3, h4, Finset.sum_singleton]

end PEqualNP.Outside.L_lib_877

open PEqualNP.Outside.L_lib_877 in
theorem PEqualNP.Outside.L_lib_877 : ∀ (k q : Nat) (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool),
  let valid := fun (M : Finset (Finset (Fin k))) =>
    (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)
  let err := fun (M : Finset (Finset (Fin k))) =>
    (Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card
  let signed := fun (S : Finset (Finset (Fin k))) =>
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)
  (∀ M, valid M → (err M : Int) = (err ∅ : Int) +
    ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int)^S.card * signed S) ∧
  ∀ d : Nat, ((∃ h : Finset (Finset (Fin k)) → Int, ∀ M, valid M →
    (err M : Int) = ∑ S ∈ M.powerset.filter (fun T => T.card ≤ d), h S) ↔
    ∀ S, valid S → d < S.card → signed S = 0) := by
  intro k q D fixed target valid err signed
  have hexp : ∀ M, (err M : Int) = (err ∅ : Int) +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int)^S.card * signed S :=
    fun M => expand D fixed target M
  have hdown : ∀ M S, valid M → S ⊆ M → valid S := by
    intro M S hM hS
    exact ⟨fun e he => hM.1 e (hS he), fun e he g hg hne => hM.2 e (hS he) g (hS hg) hne⟩
  let g : Finset (Finset (Fin k)) → Int := fun S =>
    if S = ∅ then (err ∅ : Int) else (-1 : Int)^S.card * signed S
  have hg : ∀ M, (err M : Int) = ∑ S ∈ M.powerset, g S := by
    intro M
    rw [hexp M]
    exact (split_empty M _ _).symm
  refine ⟨fun M _ => hexp M, fun d => ⟨?_, ?_⟩⟩
  · rintro ⟨h, hh⟩ S hS hd
    let h' : Finset (Finset (Fin k)) → Int := fun S => if S.card ≤ d then h S else 0
    have H : ∀ M, valid M → ∑ S ∈ M.powerset, g S = ∑ S ∈ M.powerset, h' S := by
      intro M hM
      rw [← hg M, hh M hM, Finset.sum_filter]
    have := mobius valid hdown g h' H S hS
    have hne : S ≠ ∅ := by
      intro h0; rw [h0, Finset.card_empty] at hd; exact Nat.not_lt_zero _ hd
    have hnd : ¬ S.card ≤ d := by omega
    simp only [g, h', hne, hnd, ite_false] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact h1
  · intro H
    refine ⟨g, fun M hM => ?_⟩
    rw [hg M]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hS'
    rw [Finset.mem_filter] at hS'
    have hSM : S ⊆ M := Finset.mem_powerset.mp hS
    have hd : d < S.card := by
      by_contra hc; exact hS' ⟨hS, by omega⟩
    have hne : S ≠ ∅ := by
      intro h0; rw [h0, Finset.card_empty] at hd; exact Nat.not_lt_zero _ hd
    simp only [g, hne, ite_false, H S (hdown M S hM hSM) hd, mul_zero]
