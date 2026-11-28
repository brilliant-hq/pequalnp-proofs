import PEqualNP.Defs.EdgeOwnership
import PEqualNP.Defs.Represents

/-!
  A silent wire is distinct from the output and is absent from the input lists of the
  output gate and every gate in its strict cone. The criterion inspects all listed
  operands, including unused operands of NOT gates and wires read before they exist.
  If the output lies past the last wire, every wire distinct from the output is silent.

  On the one-hot promise, row u occupies input u and column v occupies input n + v.
-/

namespace PEqualNP.Silent

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

/-- Wire `i` is SILENT in `C` on `N` inputs: it is not the output, and no gate that is the output
  gate or lies in the output gate's strict cone reads it. -/
abbrev Silent (N : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  C.output ≠ i ∧ ∀ g < C.gates.length,
    (C.output = N + g ∨ (N ≤ C.output ∧ InCone N C g (C.output - N))) →
      i ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs

/-- Row `u` is SILENT in `C` on the promise with `n` rows and `m` columns: the wire of `u` is silent. -/
abbrev SilentRow {n : ℕ} (m : ℕ) (C : Circuit) (u : Fin n) : Prop := Silent (n + m) C u.val

/-- Column `v` is SILENT in `C` on the promise with `n` rows and `m` columns: the wire `n + v` is silent. -/
abbrev SilentCol (n : ℕ) {m : ℕ} (C : Circuit) (v : Fin m) : Prop := Silent (n + m) C (n + v.val)

/-- The decision procedure for a silent wire. -/
def instDecidableSilent (N : ℕ) (C : Circuit) (i : ℕ) : Decidable (Silent N C i) :=
  inferInstance

/-- The decision procedure for a silent row. -/
def instDecidableSilentRow {n : ℕ} (m : ℕ) (C : Circuit) (u : Fin n) : Decidable (SilentRow m C u) :=
  inferInstance

/-- The decision procedure for a silent column. -/
def instDecidableSilentCol (n : ℕ) {m : ℕ} (C : Circuit) (v : Fin m) : Decidable (SilentCol n C v) :=
  inferInstance

end PEqualNP.Silent
