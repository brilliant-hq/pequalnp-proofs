import PEqualNP.Defs.SyntacticFold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
  Reader counts and excess fan-out for circuits on N primary inputs. Gate j has wire N + j.
  A gate that lists the same wire twice is one reader. The selected output adds one reader.
  Excess sums the number of readers above one for each input and gate wire. An unread wire
  contributes zero. For a folded circuit, only the first output contributes to this count.

  A folded AND/OR circuit uses distinct earlier operands and has no dead gates.
  Zeroing fixes the selected primary inputs to false. A wire becomes zero when it is
  one of those inputs or the folding pass produces a constant false at that gate.
  A gate can compute the constant false on all inputs without this syntactic simplification.
-/

namespace PEqualNP.FoldExtra

open PEqualNP.CircuitLowerBounds PEqualNP.SyntacticFold

/-- The gates of `gs` reading wire `w`, plus one if `w` is the output. -/
def readers (gs : List Gate) (out : Option ℕ) (w : ℕ) : ℕ :=
  (gs.filter fun g => decide (w ∈ g.inputs)).length + if out = some w then 1 else 0

/-- The sum of readers minus one over the wires below `N + gs.length`. -/
def extra (N : ℕ) (gs : List Gate) (out : Option ℕ) : ℕ :=
  ∑ w ∈ Finset.range (N + gs.length), (readers gs out w - 1)

/-- EXTRA of a circuit, read at its output. -/
def circuitExtra (N : ℕ) (C : Circuit) : ℕ :=
  extra N C.gates (some C.output)

/-- The first output of a folded circuit, as a wire, or none when it is a constant. -/
def foldedOut (F : Folded) : Option ℕ :=
  match F.outs.headD (Val.const false) with
  | Val.wire u => some u
  | Val.const _ => none

/-- EXTRA of a folded circuit, read at its first output. -/
def foldedExtra (N : ℕ) (F : Folded) : ℕ :=
  extra N F.gates (foldedOut F)

/-- A folded AND/OR circuit: two distinct earlier reads per gate, an existing output, no dead gate. -/
def IsFolded (N : ℕ) (C : Circuit) : Prop :=
  C.output < N + C.gates.length ∧
    ∀ j < C.gates.length,
      ((C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨ (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.or) ∧
      (C.gates.getD j ⟨GateOp.or, []⟩).inputs.length = 2 ∧ (C.gates.getD j ⟨GateOp.or, []⟩).inputs.Nodup ∧
      (∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + j) ∧
      1 ≤ readers C.gates (some C.output) (N + j)

/-- Fix every input in `Z` to `false`. -/
def zeroing (Z : Finset ℕ) : ℕ → Option Bool :=
  fun k => if k ∈ Z then some false else none

/-- Wire `w` becomes `0` under `zeroing Z`: an input in `Z`, or a gate whose pass value is the constant `false`. -/
abbrev BecomesZero (N : ℕ) (Z : Finset ℕ) (C : Circuit) (w : ℕ) : Prop :=
  (w < N ∧ w ∈ Z) ∨ (N ≤ w ∧ (pass N (zeroing Z) C).2.getD w (Val.const true) = Val.const false)

/-- The decision procedure for a wire becoming zero. -/
def instDecidableBecomesZero (N : ℕ) (Z : Finset ℕ) (C : Circuit) (w : ℕ) :
    Decidable (BecomesZero N Z C w) := inferInstance

end PEqualNP.FoldExtra
