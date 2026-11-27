import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_490_aux

open PEqualNP.ProofComplexity

def Fx {n : ℕ} (C : Clause (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun a => ∀ l ∈ C, a l.1 ≠ l.2)

theorem card_Fx {n : ℕ} (C : Clause (Fin n)) (hC : ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) :
    (Fx C).card = 2 ^ (n - C.card) := by
  classical
  let T : Fin n → Finset Bool := fun i => Finset.univ.filter (fun x => ∀ b, (i, b) ∈ C → x ≠ b)
  have hpi : Fx C = Fintype.piFinset T := by
    ext a
    simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, T, Prod.forall]
  have hfst : ∀ i b b', (i, b) ∈ C → (i, b') ∈ C → b = b' := by
    intro i b b' h1 h2
    cases b <;> cases b'
    · rfl
    · exact absurd ⟨h2, h1⟩ (hC i)
    · exact absurd ⟨h1, h2⟩ (hC i)
    · rfl
  let vars := C.image Prod.fst
  have hvars : vars.card = C.card := by
    apply Finset.card_image_of_injOn
    rintro ⟨i, b⟩ h1 ⟨i', b'⟩ h2 (hi : i = i')
    subst hi
    rw [hfst i b b' h1 h2]
  have hT : ∀ i, (T i).card = if i ∈ vars then 1 else 2 := by
    intro i
    split_ifs with hi
    · obtain ⟨⟨i', b0⟩, hl, hi'⟩ := Finset.mem_image.1 hi
      simp only at hi'
      subst hi'
      have : T i' = {!b0} := by
        ext x
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          cases x <;> cases b0 <;> simp_all
        · rintro rfl b hb
          rw [hfst i' b b0 hb hl]
          cases b0 <;> decide
      rw [this, Finset.card_singleton]
    · have : T i = Finset.univ := by
        ext x
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro b hb
        exact absurd (Finset.mem_image.2 ⟨(i, b), hb, rfl⟩) hi
      rw [this]
      rfl
  rw [hpi, Fintype.card_piFinset]
  simp only [hT]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have h1 : (Finset.univ.filter (fun i => i ∉ vars)).card = n - vars.card := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [h1, hvars]

end PEqualNP.Outside.L_lib_490_aux

open PEqualNP.Outside.L_lib_490_aux in
theorem PEqualNP.Outside.L_lib_490 : (∀ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
  (∀ C ∈ F, ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) →
  let mass := F.sum (fun C => 2 ^ (n - C.card))
  2 ^ n ≤ mass ∧
    (mass = 2 ^ n ↔ ∀ C ∈ F, ∀ E ∈ F, C ≠ E →
      ∃ i : Fin n, ∃ b : Bool, (i,b) ∈ C ∧ (i,!b) ∈ E)) := by
  intro n F hproper hunsat mass
  classical
  let cnt : (Fin n → Bool) → ℕ := fun a => (F.filter (fun C => a ∈ Fx C)).card
  have hmass : mass = ∑ a : Fin n → Bool, cnt a := by
    show F.sum (fun C => 2 ^ (n - C.card)) = _
    rw [← Finset.sum_congr rfl (fun C hC => card_Fx C (hproper C hC))]
    simp only [cnt, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_filter]
  have hpos : ∀ a, 1 ≤ cnt a := by
    intro a
    have : ∃ C ∈ F, a ∈ Fx C := by
      by_contra h
      push_neg at h
      apply hunsat
      refine ⟨a, fun C hC => ?_⟩
      have hn := h C (Finset.mem_coe.1 hC)
      simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hn
      obtain ⟨l, hl, he⟩ := hn
      exact ⟨l, hl, he⟩
    obtain ⟨C, hC, ha⟩ := this
    exact Finset.card_pos.2 ⟨C, Finset.mem_filter.2 ⟨hC, ha⟩⟩
  have hcube : (2 : ℕ) ^ n = ∑ _a : Fin n → Bool, 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hmass, hcube]
    exact Finset.sum_le_sum (fun a _ => hpos a)
  · constructor
    · intro heq C hC E hE hCE
      by_contra hno
      push_neg at hno
      let a : Fin n → Bool := fun i => if (i, true) ∈ C ∨ (i, true) ∈ E then false else true
      have hfal : ∀ D ∈ ({C, E} : Finset _), a ∈ Fx D := by
        intro D hD
        simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro l hl
        obtain ⟨i, b⟩ := l
        have hDCE : D = C ∨ D = E := by simpa using hD
        cases b
        · show (if (i, true) ∈ C ∨ (i, true) ∈ E then false else true) ≠ false
          rw [if_neg]
          · decide
          · rintro (h | h)
            · rcases hDCE with rfl | rfl
              · exact hproper D hC i ⟨h, hl⟩
              · exact hno i true h hl
            · rcases hDCE with rfl | rfl
              · exact hno i false hl h
              · exact hproper D hE i ⟨h, hl⟩
        · show (if (i, true) ∈ C ∨ (i, true) ∈ E then false else true) ≠ true
          rw [if_pos]
          · decide
          · rcases hDCE with rfl | rfl
            · exact Or.inl hl
            · exact Or.inr hl
      have h2 : 2 ≤ cnt a := by
        have hsub : ({C, E} : Finset _) ⊆ F.filter (fun D => a ∈ Fx D) := by
          intro D hD
          refine Finset.mem_filter.2 ⟨?_, hfal D hD⟩
          rcases (by simpa using hD : D = C ∨ D = E) with rfl | rfl
          · exact hC
          · exact hE
        have := Finset.card_le_card hsub
        rw [Finset.card_pair hCE] at this
        exact this
      have hlt : ∑ _a : Fin n → Bool, 1 < ∑ a : Fin n → Bool, cnt a :=
        Finset.sum_lt_sum (fun a _ => hpos a) ⟨a, Finset.mem_univ _, by omega⟩
      rw [← hmass, ← hcube] at hlt
      omega
    · intro hall
      rw [hmass, hcube]
      apply Finset.sum_congr rfl
      intro a _
      apply le_antisymm _ (hpos a)
      rw [Finset.card_le_one]
      intro C hC E hE
      by_contra hCE
      obtain ⟨hCF, haC⟩ := Finset.mem_filter.1 hC
      obtain ⟨hEF, haE⟩ := Finset.mem_filter.1 hE
      obtain ⟨i, b, hib, hinb⟩ := hall C hCF E hEF hCE
      simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and] at haC haE
      have h1 := haC (i, b) hib
      have h2 := haE (i, !b) hinb
      simp only at h1 h2
      cases b <;> cases (a i) <;> simp_all
