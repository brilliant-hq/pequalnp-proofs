import PEqualNP.Defs
import Mathlib.Topology.Order.IntermediateValue

namespace PEqualNP.Outside.L_gct_141_aux

def f141 (x : ℝ) : ℝ :=
  (26281829643807702458406 * x ^ 18 - 315357758844690494658 * x ^ 35) * (7705 + 21 * x ^ 25) -
    (-150303984092195142770 + 673011295193275874620 * x ^ 4) * (8817 + 375016 * x ^ 13)

lemma f141_cont : Continuous f141 := by
  unfold f141
  fun_prop

lemma root_of_pos_neg {a b : ℝ} (hab : a < b) (ha : 0 < f141 a) (hb : f141 b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ f141 x = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f141 b) (f141 a) := ⟨hb.le, ha.le⟩
  obtain ⟨x, ⟨hax, hxb⟩, hx⟩ := intermediate_value_Icc' hab.le f141_cont.continuousOn hmem
  refine ⟨x, lt_of_le_of_ne hax ?_, lt_of_le_of_ne hxb ?_, hx⟩
  · intro heq; rw [← heq] at hx; linarith
  · intro heq; rw [heq] at hx; linarith

lemma root_of_neg_pos {a b : ℝ} (hab : a < b) (ha : f141 a < 0) (hb : 0 < f141 b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ f141 x = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f141 a) (f141 b) := ⟨ha.le, hb.le⟩
  obtain ⟨x, ⟨hax, hxb⟩, hx⟩ := intermediate_value_Icc hab.le f141_cont.continuousOn hmem
  refine ⟨x, lt_of_le_of_ne hax ?_, lt_of_le_of_ne hxb ?_, hx⟩
  · intro heq; rw [← heq] at hx; linarith
  · intro heq; rw [heq] at hx; linarith

lemma main : ∃ S : Finset ℝ, 7 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ f141 x = 0 := by
  have hp0 : 0 < f141 (1 / 2 : ℝ) := by unfold f141; norm_num
  have hp1 : f141 (4 / 5 : ℝ) < 0 := by unfold f141; norm_num
  have hp2 : 0 < f141 (9 / 10 : ℝ) := by unfold f141; norm_num
  have hp3 : f141 (1 : ℝ) < 0 := by unfold f141; norm_num
  have hp4 : 0 < f141 (9 / 8 : ℝ) := by unfold f141; norm_num
  have hp5 : f141 (8 / 7 : ℝ) < 0 := by unfold f141; norm_num
  have hp6 : 0 < f141 (22 / 19 : ℝ) := by unfold f141; norm_num
  have hp7 : f141 (3 / 2 : ℝ) < 0 := by unfold f141; norm_num
  obtain ⟨r1, hr1a, hr1b, hr1⟩ := root_of_pos_neg (by norm_num) hp0 hp1
  obtain ⟨r2, hr2a, hr2b, hr2⟩ := root_of_neg_pos (by norm_num) hp1 hp2
  obtain ⟨r3, hr3a, hr3b, hr3⟩ := root_of_pos_neg (by norm_num) hp2 hp3
  obtain ⟨r4, hr4a, hr4b, hr4⟩ := root_of_neg_pos (by norm_num) hp3 hp4
  obtain ⟨r5, hr5a, hr5b, hr5⟩ := root_of_pos_neg (by norm_num) hp4 hp5
  obtain ⟨r6, hr6a, hr6b, hr6⟩ := root_of_neg_pos (by norm_num) hp5 hp6
  obtain ⟨r7, hr7a, hr7b, hr7⟩ := root_of_pos_neg (by norm_num) hp6 hp7
  have hlt12 : r1 < r2 := by linarith
  have hlt23 : r2 < r3 := by linarith
  have hlt34 : r3 < r4 := by linarith
  have hlt45 : r4 < r5 := by linarith
  have hlt56 : r5 < r6 := by linarith
  have hlt67 : r6 < r7 := by linarith
  let v : Fin 7 → ℝ := ![r1, r2, r3, r4, r5, r6, r7]
  have hv_mono : StrictMono v := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simpa [v] using ‹_›
  refine ⟨Finset.univ.image v, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hv_mono.injective, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    fin_cases i
    · dsimp [v]; exact ⟨by linarith, hr1⟩
    · dsimp [v]; exact ⟨by linarith, hr2⟩
    · dsimp [v]; exact ⟨by linarith, hr3⟩
    · dsimp [v]; exact ⟨by linarith, hr4⟩
    · dsimp [v]; exact ⟨by linarith, hr5⟩
    · dsimp [v]; exact ⟨by linarith, hr6⟩
    · dsimp [v]; exact ⟨by linarith, hr7⟩

end PEqualNP.Outside.L_gct_141_aux

theorem PEqualNP.Outside.L_gct_141 : ∃ S : Finset ℝ, 7 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ (26281829643807702458406 * x ^ 18 - 315357758844690494658 * x ^ 35) * (7705 + 21 * x ^ 25) - (-150303984092195142770 + 673011295193275874620 * x ^ 4) * (8817 + 375016 * x ^ 13) = 0 :=
  PEqualNP.Outside.L_gct_141_aux.main
