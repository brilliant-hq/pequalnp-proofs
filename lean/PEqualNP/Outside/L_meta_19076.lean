import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19076_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def c_19076 : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩

theorem main_19076 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
      Represents (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨c_19076, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c_19076, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by decide⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl

end PEqualNP.Outside.L_meta_19076_aux

theorem PEqualNP.Outside.L_meta_19076 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact PEqualNP.Outside.L_meta_19076_aux.main_19076
