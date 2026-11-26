import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17721`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17721_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → x1.eval x4 = Bool.true) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → x1.eval x4 = Bool.true) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
