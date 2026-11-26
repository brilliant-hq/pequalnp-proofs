import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_23228_aux

private def gs : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [9]⟩,
   ⟨.and, [8, 10]⟩]

private def circ : Circuit := ⟨gs, 11⟩

private theorem fan : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, gs, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Or.inr (Or.inl rfl), le_refl _⟩
  · exact ⟨Or.inl rfl, le_refl _⟩
  · exact ⟨Or.inr (Or.inl rfl), le_refl _⟩
  · exact ⟨Or.inl rfl, le_refl _⟩
  · exact ⟨Or.inr (Or.inr rfl), by decide⟩
  · exact ⟨Or.inl rfl, le_refl _⟩

private theorem sz : circ.size ≤ 6 := by decide +kernel

private theorem ev : ∀ (i j : Fin 6),
    circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (36797 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23228_aux

theorem PEqualNP.Outside.L_meta_23228 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36797 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨L_meta_23228_aux.circ, L_meta_23228_aux.fan, L_meta_23228_aux.sz, L_meta_23228_aux.ev⟩
