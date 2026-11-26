import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_137_aux

noncomputable def p (x : ℝ) : ℝ := 200 * x ^ 14 - 200 * x ^ 13 + 25 * x ^ 2 - 25 * x + 6

theorem pc (a b : ℝ) : ContinuousOn p (Set.Icc a b) := by
  unfold p
  fun_prop

theorem dn (a b : ℝ) (hab : a ≤ b) (ha : 0 < p a) (hb : p b < 0) :
    ∃ x, a < x ∧ x < b ∧ p x = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' hab (pc a b) ⟨hb, ha⟩
  exact ⟨x, h1, h2, h3⟩

theorem up (a b : ℝ) (hab : a ≤ b) (ha : p a < 0) (hb : 0 < p b) :
    ∃ x, a < x ∧ x < b ∧ p x = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo hab (pc a b) ⟨ha, hb⟩
  exact ⟨x, h1, h2, h3⟩

end PEqualNP.Outside.L_gct_137_aux

open PEqualNP.Outside.L_gct_137_aux in
theorem PEqualNP.Outside.L_gct_137 : ∃ S : Finset ℝ, 4 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ x < 1 ∧ 200 * x ^ 14 - 200 * x ^ 13 + 25 * x ^ 2 - 25 * x + 6 = 0 := by
  obtain ⟨a, a1, a2, a3⟩ := dn 0 (1 / 2) (by norm_num) (by unfold p; norm_num) (by unfold p; norm_num)
  obtain ⟨b, b1, b2, b3⟩ := up (1 / 2) (7 / 10) (by norm_num) (by unfold p; norm_num) (by unfold p; norm_num)
  obtain ⟨c, c1, c2, c3⟩ := dn (7 / 10) (9 / 10) (by norm_num) (by unfold p; norm_num) (by unfold p; norm_num)
  obtain ⟨d, d1, d2, d3⟩ := up (9 / 10) 1 (by norm_num) (by unfold p; norm_num) (by unfold p; norm_num)
  unfold p at a3 b3 c3 d3
  refine ⟨{a, b, c, d}, ?_, ?_⟩
  · have h1 : a ≠ b := by intro h; linarith
    have h2 : a ≠ c := by intro h; linarith
    have h3 : a ≠ d := by intro h; linarith
    have h4 : b ≠ c := by intro h; linarith
    have h5 : b ≠ d := by intro h; linarith
    have h6 : c ≠ d := by intro h; linarith
    simp [Finset.card_insert_of_notMem, h1, h2, h3, h4, h5, h6]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨a1, by linarith, a3⟩
    · exact ⟨by linarith, by linarith, b3⟩
    · exact ⟨by linarith, by linarith, c3⟩
    · exact ⟨by linarith, d2, d3⟩
