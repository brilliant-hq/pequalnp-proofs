import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18675

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_18675

theorem PEqualNP.Outside.L_meta_18675 : ∀ (x1 : ℕ) (x2 : List PEqualNP.CircuitLowerBounds.Gate),   (∀ (x3 : Fin x2.length),       have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.getD ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };       (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x4.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < x1 + ↑x3 ∧ x6 < x1 + ↑x3) →     PEqualNP.TopForm.IsAO2 x1 { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ x4 ∈ x2, x4.inputs.Nodup := by
  intro x1 x2 h
  have hm : ∀ g ∈ x2, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have := h ⟨k, hk⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this
    obtain ⟨hop, a, b, hab, hne, _, _⟩ := this
    exact ⟨hop, by simp [hab], by simp [hab, hne]⟩
  refine ⟨⟨fun g hg => (hm g hg).1, ?_, fun g hg => (hm g hg).2.1⟩, fun g hg => (hm g hg).2.2⟩
  intro j hj i hi
  have := h ⟨j, hj⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  obtain ⟨_, a, b, hab, _, ha, hb⟩ := this
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hab, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> assumption
