import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_141_aux

noncomputable def f (x : ℝ) : ℝ :=
  (26281829643807702458406 * x ^ 18 - 315357758844690494658 * x ^ 35) * (7705 + 21 * x ^ 25) - (-150303984092195142770 + 673011295193275874620 * x ^ 4) * (8817 + 375016 * x ^ 13)

lemma f_cont : Continuous f := by
  unfold f
  fun_prop

lemma root_pn {a b : ℝ} (hab : a < b) (ha : 0 < f a) (hb : f b < 0) :
    ∃ r ∈ Set.Ioo a b, f r = 0 :=
  intermediate_value_Ioo' hab.le f_cont.continuousOn ⟨hb, ha⟩

lemma root_np {a b : ℝ} (hab : a < b) (ha : f a < 0) (hb : 0 < f b) :
    ∃ r ∈ Set.Ioo a b, f r = 0 :=
  intermediate_value_Ioo hab.le f_cont.continuousOn ⟨ha, hb⟩

lemma s0 : 0 < f 0 := by unfold f; norm_num
lemma s1 : f (4 / 5) < 0 := by unfold f; norm_num
lemma s2 : 0 < f (8 / 9) := by unfold f; norm_num
lemma s3 : f 1 < 0 := by unfold f; norm_num
lemma s4 : 0 < f (9 / 8) := by unfold f; norm_num
lemma s5 : f (8 / 7) < 0 := by unfold f; norm_num
lemma s6 : 0 < f (22 / 19) := by unfold f; norm_num
lemma s7 : f (3 / 2) < 0 := by unfold f; norm_num

end PEqualNP.Outside.L_gct_141_aux

open PEqualNP.Outside.L_gct_141_aux in
theorem PEqualNP.Outside.L_gct_141 : ∃ S : Finset ℝ, 7 ≤ S.card ∧ ∀ x ∈ S, 0 < x ∧ (26281829643807702458406 * x ^ 18 - 315357758844690494658 * x ^ 35) * (7705 + 21 * x ^ 25) - (-150303984092195142770 + 673011295193275874620 * x ^ 4) * (8817 + 375016 * x ^ 13) = 0 := by
  obtain ⟨r1, h1, e1⟩ := root_pn (by norm_num) s0 s1
  obtain ⟨r2, h2, e2⟩ := root_np (by norm_num) s1 s2
  obtain ⟨r3, h3, e3⟩ := root_pn (by norm_num) s2 s3
  obtain ⟨r4, h4, e4⟩ := root_np (by norm_num) s3 s4
  obtain ⟨r5, h5, e5⟩ := root_pn (by norm_num) s4 s5
  obtain ⟨r6, h6, e6⟩ := root_np (by norm_num) s5 s6
  obtain ⟨r7, h7, e7⟩ := root_pn (by norm_num) s6 s7
  let ρ : Fin 7 → ℝ := ![r1, r2, r3, r4, r5, r6, r7]
  have hmono : StrictMono ρ := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · exact h1.2.trans h2.1
    · exact h2.2.trans h3.1
    · exact h3.2.trans h4.1
    · exact h4.2.trans h5.1
    · exact h5.2.trans h6.1
    · exact h6.2.trans h7.1
  refine ⟨Finset.univ.image ρ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_fin]
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    fin_cases i
    · exact ⟨h1.1, e1⟩
    · exact ⟨show (0 : ℝ) < r2 by linarith [h2.1], e2⟩
    · exact ⟨show (0 : ℝ) < r3 by linarith [h3.1], e3⟩
    · exact ⟨show (0 : ℝ) < r4 by linarith [h4.1], e4⟩
    · exact ⟨show (0 : ℝ) < r5 by linarith [h5.1], e5⟩
    · exact ⟨show (0 : ℝ) < r6 by linarith [h6.1], e6⟩
    · exact ⟨show (0 : ℝ) < r7 by linarith [h7.1], e7⟩
