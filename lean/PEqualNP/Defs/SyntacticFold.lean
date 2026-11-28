import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Dedup

/-!
  Folding a circuit fixes selected primary inputs and computes a value for each old wire.
  Each value denotes a constant or a wire in the new circuit. Missing reads yield false.
  The pass evaluates NOT on constants. In an AND, false absorbs and true disappears.
  OR uses the dual rules. Repeated wires count once. Empty AND and OR keep their usual
  values, and a single remaining operand replaces the gate. MOD and MAJ are retained
  when all operands are wires and otherwise reduce to false.

  The pruning pass keeps the union of the requested output cones and renumbers their gates.
  An output can become a constant without needing a gate. The folded circuit retains the
  list of outputs in order. Input deletion then compacts the surviving input indices.
-/

namespace PEqualNP.SyntacticFold

open PEqualNP.CircuitLowerBounds

/-- The value of a wire after folding: a constant, or a wire of the new circuit. -/
inductive Val where
  /-- The wire is the constant `b`. -/
  | const (b : Bool)
  /-- The wire is (a copy of) wire `u` of the new circuit. -/
  | wire (u : ℕ)
  deriving DecidableEq

/-- The wire a value names, if any. -/
def Val.wireOf : Val → Option ℕ
  | Val.const _ => none
  | Val.wire u => some u

/-- All wire indices in a list of values, each occurring once. -/
def wiresOf (rs : List Val) : List ℕ :=
  (rs.filterMap Val.wireOf).dedup

/-- What one gate becomes: a value (the gate is folded away), or a kept gate. -/
inductive Step where
  /-- The gate is folded away: its wire takes this value. -/
  | val (v : Val)
  /-- The gate is kept, with this operation and these reads of new wires. -/
  | keep (op : GateOp) (ins : List ℕ)

/-- The folding rule for one gate, from the values of the wires it reads, in order. -/
def simpGate (op : GateOp) (rs : List Val) : Step :=
  match op with
  | GateOp.not =>
    match rs.headD (Val.const false) with
    | Val.const b => Step.val (Val.const (!b))
    | Val.wire u => Step.keep GateOp.not [u]
  | GateOp.and =>
    if Val.const false ∈ rs then Step.val (Val.const false) else
      match wiresOf rs with
      | [] => Step.val (Val.const true)
      | [u] => Step.val (Val.wire u)
      | ws => Step.keep GateOp.and ws
  | GateOp.or =>
    if Val.const true ∈ rs then Step.val (Val.const true) else
      match wiresOf rs with
      | [] => Step.val (Val.const false)
      | [u] => Step.val (Val.wire u)
      | ws => Step.keep GateOp.or ws
  | op =>
    if rs.all (fun v => (Val.wireOf v).isSome) then Step.keep op (rs.filterMap Val.wireOf)
    else Step.val (Val.const false)

/-- The values of the input wires under `rho`. -/
def initVals (N : ℕ) (rho : ℕ → Option Bool) : List Val :=
  (List.range N).map fun k =>
    match rho k with
    | some b => Val.const b
    | none => Val.wire k

/-- One step of the pass: the new gates so far and the values of the old wires so far. -/
def passStep (N : ℕ) (st : List Gate × List Val) (g : Gate) : List Gate × List Val :=
  match simpGate g.op (g.inputs.map fun i => st.2.getD i (Val.const false)) with
  | Step.val v => (st.1, st.2 ++ [v])
  | Step.keep op ws => (st.1 ++ [⟨op, ws⟩], st.2 ++ [Val.wire (N + st.1.length)])

/-- The pass over all gates of `C`: the kept gates, and the value of every old wire. -/
def pass (N : ℕ) (rho : ℕ → Option Bool) (C : Circuit) : List Gate × List Val :=
  C.gates.foldl (passStep N) ([], initVals N rho)

/-- A circuit read at a list of outputs, each a value: a constant or a wire. -/
structure Folded where
  /-- The gates, in evaluation order; gate `j` is wire `(input length) + j`. -/
  gates : List Gate
  /-- The outputs. -/
  outs : List Val

/-- Output `k` of `F` on the input list `x` (`false` past the last output). -/
def Folded.eval (F : Folded) (x : List Bool) (k : ℕ) : Bool :=
  match F.outs.getD k (Val.const false) with
  | Val.const b => b
  | Val.wire u => ((⟨F.gates, 0⟩ : Circuit).wires x).getD u false

/-- The size of a folded circuit: its number of gates. -/
def Folded.size (F : Folded) : ℕ :=
  F.gates.length

/-- The wires a list of outputs names. -/
def outWires (outs : List Val) : Finset ℕ :=
  (outs.filterMap Val.wireOf).toFinset

/-- The wires in the union of the cones of `outs`, among the gates `gs` on `N` inputs: the output
  wires and the inputs of all gates in the cones. Gates are visited in reverse order. -/
def coneWires (N : ℕ) (gs : List Gate) (outs : List Val) : Finset ℕ :=
  (List.range gs.length).reverse.foldl
    (fun need j =>
      if N + j ∈ need then need ∪ (gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset else need)
    (outWires outs)

/-- The live gates: the indices of the gates whose wires lie in the union of the output cones. -/
def liveOf (N : ℕ) (gs : List Gate) (outs : List Val) : Finset ℕ :=
  (Finset.range gs.length).filter fun j => N + j ∈ coneWires N gs outs

/-- The new index of a wire when only the gates `keep` holds for are kept: inputs unchanged, a
  gate wires move down past the erased gates before them. -/
def renum (N : ℕ) (keep : ℕ → Bool) (w : ℕ) : ℕ :=
  if w < N then w else N + ((List.range (w - N)).filter keep).length

/-- Erase every gate outside the union of the output cones and renumber the rest. -/
def prune (N : ℕ) (F : Folded) : Folded :=
  let keep : ℕ → Bool := fun j => decide (N + j ∈ coneWires N F.gates F.outs)
  ⟨((List.range F.gates.length).filter keep).map fun j =>
      let g := F.gates.getD j ⟨GateOp.or, []⟩
      ⟨g.op, g.inputs.map (renum N keep)⟩,
    F.outs.map fun v =>
      match v with
      | Val.const b => Val.const b
      | Val.wire u => Val.wire (renum N keep u)⟩

/-- The one pass, before pruning: the kept gates and the values of the outputs `outs`. -/
def foldCore (N : ℕ) (rho : ℕ → Option Bool) (C : Circuit) (outs : List ℕ) : Folded :=
  ⟨(pass N rho C).1, outs.map fun o => (pass N rho C).2.getD o (Val.const false)⟩

/-- The syntactic fold of `C` on `N` inputs under `rho`, read at the output wires `outs`. -/
def fold (N : ℕ) (rho : ℕ → Option Bool) (C : Circuit) (outs : List ℕ) : Folded :=
  prune N (foldCore N rho C outs)

/-- The number of gates the fold removes. -/
def deaths (N : ℕ) (rho : ℕ → Option Bool) (C : Circuit) (outs : List ℕ) : ℕ :=
  C.size - (fold N rho C outs).size

/-- Delete the inputs `drop` holds for (among the first `N`): input `k` becomes input number
  `(inputs kept below k)` and gate `j` keeps its index. A deleted operand becomes the current
  gate's own wire, which still reads as false. A deleted output input becomes constant false. -/
def dropInputs (N : ℕ) (drop : ℕ → Bool) (F : Folded) : Folded :=
  let N' := ((List.range N).filter fun k => !drop k).length
  let ren : ℕ → ℕ → ℕ := fun self w =>
    if w < N then (if drop w then self else ((List.range w).filter fun k => !drop k).length)
    else N' + (w - N)
  ⟨F.gates.mapIdx fun j g => ⟨g.op, g.inputs.map (ren (N' + j))⟩,
    F.outs.map fun v =>
      match v with
      | Val.const b => Val.const b
      | Val.wire u => if u < N ∧ drop u = true then Val.const false else Val.wire (ren 0 u)⟩

end PEqualNP.SyntacticFold
