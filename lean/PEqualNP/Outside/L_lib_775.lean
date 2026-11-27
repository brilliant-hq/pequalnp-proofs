import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_775

open Finset

/-- Words of length L with a given prefix p are at most 2 ^ (L - length p). -/
theorem card_bad (L : ℕ) (p : List Bool) :
    (univ.filter (fun v : List.Vector Bool L => p <+: v.toList)).card ≤ 2 ^ (L - p.length) := by
  have h := card_le_card_of_injOn (s := univ.filter (fun v : List.Vector Bool L => p <+: v.toList))
    (t := (univ : Finset (List.Vector Bool (L - p.length))))
    (fun v => ⟨v.toList.drop p.length, by simp⟩) (fun _ _ => mem_coe.mpr (mem_univ _)) (by
      intro v hv w hw hvw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
      have e1 := congrArg Subtype.val hvw
      simp only at e1
      apply List.Vector.toList_injective
      rw [← List.take_append_drop p.length v.toList, ← List.take_append_drop p.length w.toList,
        ← List.prefix_iff_eq_take.mp hv, ← List.prefix_iff_eq_take.mp hw]
      exact congrArg (p ++ ·) e1)
  simpa [card_vector] using h

theorem gen {k : ℕ} (l : Fin k → ℕ) (s : Finset (Fin k)) :
    (∑ i ∈ s, ((1 : ℚ) / 2) ^ (l i)) ≤ 1 →
      ∃ c : Fin k → List Bool, (∀ i, (c i).length = l i) ∧
        ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ (c i <+: c j) := by
  induction s using Finset.induction_on_max_value l with
  | empty => intro _; exact ⟨fun i => List.replicate (l i) false, by simp, by simp⟩
  | insert a s ha hmax ih =>
    intro hsum
    rw [sum_insert ha] at hsum
    have hpos : (0 : ℚ) < ((1 : ℚ) / 2) ^ (l a) := by positivity
    obtain ⟨c, hcl, hcp⟩ := ih (by linarith)
    set L := l a with hL
    -- counting bad words of length L
    let bad : Finset (List.Vector Bool L) :=
      s.biUnion (fun j => univ.filter (fun v : List.Vector Bool L => c j <+: v.toList))
    have hbad : (bad.card : ℚ) < 2 ^ L := by
      have h1 : bad.card ≤ ∑ j ∈ s, 2 ^ (L - l j) := by
        refine (card_biUnion_le).trans (sum_le_sum fun j hj => ?_)
        have := card_bad L (c j)
        rwa [hcl] at this
      have h2 : ((∑ j ∈ s, 2 ^ (L - l j) : ℕ) : ℚ) =
          (2 : ℚ) ^ L * ∑ j ∈ s, ((1 : ℚ) / 2) ^ (l j) := by
        push_cast
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        have hj := hmax j hj
        rw [div_pow, one_pow, ← mul_div_assoc, mul_one, eq_div_iff (by positivity), ← pow_add,
          Nat.sub_add_cancel hj]
      have h3 : (2 : ℚ) ^ L * ((1 : ℚ) / 2) ^ L = 1 := by
        rw [← mul_pow]; norm_num
      have h4 : (2 : ℚ) ^ L * ∑ j ∈ s, ((1 : ℚ) / 2) ^ (l j) ≤ 2 ^ L - 1 := by
        have : ∑ j ∈ s, ((1 : ℚ) / 2) ^ (l j) ≤ 1 - ((1 : ℚ) / 2) ^ L := by linarith
        nlinarith [pow_pos (show (0 : ℚ) < 2 by norm_num) L]
      have h5 : (bad.card : ℚ) ≤ ((∑ j ∈ s, 2 ^ (L - l j) : ℕ) : ℚ) := by exact_mod_cast h1
      linarith
    have hex : ∃ v : List.Vector Bool L, v ∉ bad := by
      by_contra hno
      push Not at hno
      have : bad = univ := eq_univ_of_forall hno
      rw [this, card_univ, card_vector, Fintype.card_bool] at hbad
      push_cast at hbad
      exact lt_irrefl _ hbad
    obtain ⟨v, hv⟩ := hex
    have hv' : ∀ j ∈ s, ¬ (c j <+: v.toList) := by
      intro j hj h
      exact hv (mem_biUnion.mpr ⟨j, hj, by simp [h]⟩)
    refine ⟨Function.update c a v.toList, ?_, ?_⟩
    · intro i
      by_cases hi : i = a
      · subst hi; simp [hL]
      · simp [Function.update_of_ne hi, hcl]
    · intro i hi j hj hij
      rw [mem_insert] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · exact absurd rfl hij
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hj)]
        intro h
        have hle := h.length_le
        rw [hcl, List.Vector.toList_length] at hle
        have heq := h.eq_of_length (by
          rw [hcl, List.Vector.toList_length]; exact le_antisymm hle (hmax j hj))
        exact hv' j hj (heq ▸ List.prefix_refl _)
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)]
        exact hv' i hi
      · rw [Function.update_of_ne (by rintro rfl; exact ha hi),
          Function.update_of_ne (by rintro rfl; exact ha hj)]
        exact hcp i hi j hj hij

end PEqualNP.Outside.L_lib_775

open PEqualNP.Outside.L_lib_775 in
theorem PEqualNP.Outside.L_lib_775 : ∀ (k : ℕ) (l : Fin k → ℕ), (∑ i, ((1 : ℚ) / 2) ^ (l i)) ≤ 1 →
  ∃ c : Fin k → List Bool, (∀ i, (c i).length = l i) ∧ ∀ i j, i ≠ j → ¬ (c i <+: c j) := by
  intro k l h
  obtain ⟨c, h1, h2⟩ := gen l Finset.univ h
  exact ⟨c, h1, fun i j hij => h2 i (Finset.mem_univ _) j (Finset.mem_univ _) hij⟩
