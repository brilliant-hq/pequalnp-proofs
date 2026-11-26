import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18675 : ∀ (x1 : ℕ) (x2 : List PEqualNP.CircuitLowerBounds.Gate),   (∀ (x3 : Fin x2.length),       have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.getD ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };       (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x4.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < x1 + ↑x3 ∧ x6 < x1 + ↑x3) →     PEqualNP.TopForm.IsAO2 x1 { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ x4 ∈ x2, x4.inputs.Nodup := by
  intro n gs h
  have hh : ∀ (i : ℕ) (hi : i < gs.length), ((gs[i]).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gs[i]).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b, (gs[i]).inputs = [a, b] ∧ a ≠ b ∧ a < n + i ∧ b < n + i := by
    intro i hi
    have := h ⟨i, hi⟩
    dsimp only at this
    rw [List.getD_eq_getElem _ _ hi] at this
    exact this
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact (hh i hi).1
  · intro j hj k hk
    obtain ⟨-, a, b, h2, -, h4, h5⟩ := hh j hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj] at hk
    rw [h2] at hk
    simp at hk
    omega
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨-, a, b, h2, -⟩ := hh i hi
    rw [h2]
    rfl
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨-, a, b, h2, h3, -⟩ := hh i hi
    rw [h2]
    simp [h3]
