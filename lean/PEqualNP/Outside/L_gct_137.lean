import PEqualNP.Defs
import Mathlib.Topology.Order.IntermediateValue

namespace PEqualNP.Outside.L_gct_137_aux

def f137 (x : ℝ) : ℝ := 200 * x ^ 14 - 200 * x ^ 13 + 25 * x ^ 2 - 25 * x + 6

lemma f137_cont : Continuous f137 := by
  unfold f137
  fun_prop

lemma root_of_pos_neg {a b : ℝ} (hab : a < b) (ha : 0 < f137 a) (hb : f137 b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ f137 x = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f137 b) (f137 a) := ⟨hb.le, ha.le⟩
  obtain ⟨x, ⟨hax, hxb⟩, hx⟩ := intermediate_value_Icc' hab.le f137_cont.continuousOn hmem
  refine ⟨x, lt_of_le_of_ne hax ?_, lt_of_le_of_ne hxb ?_, hx⟩
  · intro heq; rw [← heq] at hx; linarith
  · intro heq; rw [heq] at hx; linarith

lemma root_of_neg_pos {a b : ℝ} (hab : a < b) (ha : f137 a < 0) (hb : 0 < f137 b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ f137 x = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f137 a) (f137 b) := ⟨ha.le, hb.le⟩
  obtain ⟨x, ⟨hax, hxb⟩, hx⟩ := intermediate_value_Icc hab.le f137_cont.continuousOn hmem
  refine ⟨x, lt_of_le_of_ne hax ?_, lt_of_le_of_ne hxb ?_, hx⟩
  · intro heq; rw [← heq] at hx; linarith
  · intro heq; rw [heq] at hx; linarith

lemma main : ∃ S : Finset ℝ, 4 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ x < 1 ∧ f137 x = 0 := by
  have hp0 : 0 < f137 (1 / 10 : ℝ) := by unfold f137; norm_num
  have hp1 : f137 (2 / 5 : ℝ) < 0 := by unfold f137; norm_num
  have hp2 : 0 < f137 (7 / 10 : ℝ) := by unfold f137; norm_num
  have hp3 : f137 (9 / 10 : ℝ) < 0 := by unfold f137; norm_num
  have hp4 : 0 < f137 (99 / 100 : ℝ) := by unfold f137; norm_num
  obtain ⟨r1, hr1a, hr1b, hr1⟩ := root_of_pos_neg (by norm_num) hp0 hp1
  obtain ⟨r2, hr2a, hr2b, hr2⟩ := root_of_neg_pos (by norm_num) hp1 hp2
  obtain ⟨r3, hr3a, hr3b, hr3⟩ := root_of_pos_neg (by norm_num) hp2 hp3
  obtain ⟨r4, hr4a, hr4b, hr4⟩ := root_of_neg_pos (by norm_num) hp3 hp4
  refine ⟨{r1, r2, r3, r4}, ?_, ?_⟩
  · have h12 : r1 ≠ r2 := ne_of_lt (by linarith)
    have h13 : r1 ≠ r3 := ne_of_lt (by linarith)
    have h14 : r1 ≠ r4 := ne_of_lt (by linarith)
    have h23 : r2 ≠ r3 := ne_of_lt (by linarith)
    have h24 : r2 ≠ r4 := ne_of_lt (by linarith)
    have h34 : r3 ≠ r4 := ne_of_lt (by linarith)
    simp [h12, h13, h14, h23, h24, h34]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨by linarith, by linarith, hr1⟩
    · exact ⟨by linarith, by linarith, hr2⟩
    · exact ⟨by linarith, by linarith, hr3⟩
    · exact ⟨by linarith, by linarith, hr4⟩

end PEqualNP.Outside.L_gct_137_aux

theorem PEqualNP.Outside.L_gct_137 : ∃ S : Finset ℝ, 4 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ x < 1 ∧ 200 * x ^ 14 - 200 * x ^ 13 + 25 * x ^ 2 - 25 * x + 6 = 0 :=
  PEqualNP.Outside.L_gct_137_aux.main
