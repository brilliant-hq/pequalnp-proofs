import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20784

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readWire (w : List Bool) (i : Nat) : Bool := w.getD i false

def pushGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (readWire w))]

def runGates (gs : List Gate) (w : List Bool) : List Bool := gs.foldl pushGate w

theorem readSnoc (w : List Bool) (v : Bool) (i : Nat) :
    readWire (w ++ [v]) i = if i = w.length then v else readWire w i := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [readWire, List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne]
  · subst i
    simp [readWire, List.getD_eq_getElem?_getD]
  · have ho : w.getD i false = false := List.getD_eq_default _ _ (by omega)
    have hn : (w ++ [v]).getD i false = false := List.getD_eq_default _ _ (by simp; omega)
    simpa only [readWire, ite_eq_right (by omega : i ≠ w.length), ho] using hn

theorem runLength (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    change (runGates gs (pushGate w g)).length = _
    rw [ih]
    simp [pushGate]; omega

theorem preservesInput (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    readWire (runGates gs w) i = readWire w i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change readWire (runGates gs (pushGate w g)) i = _
    rw [ih _ (by simp [pushGate]; omega)]
    simp [pushGate, readSnoc, hi.ne]

def xorBlock (a b p : Nat) : List Gate :=
  [⟨.or, [a,b]⟩, ⟨.and, [a,b]⟩, ⟨.not, [p+1]⟩, ⟨.and, [p,p+2]⟩]

theorem xorBlockValue (a b p : Nat) (w : List Bool) (hw : p = w.length)
    (ha : a < p) (hb : b < p) :
    readWire (runGates (xorBlock a b p) w) (p+3) = Bool.xor (readWire w a) (readWire w b) := by
  subst p
  cases hx : readWire w a <;> cases hy : readWire w b <;>
    simp (disch := omega) [runGates, xorBlock, pushGate, GateOp.eval, readSnoc, hx, hy, ha.ne, hb.ne] <;>
    simp (disch := omega) [readWire, List.getD_eq_getElem?_getD, List.getElem?_append_right] <;> rfl

def resultWire (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => n + 4*k + 3

def parityGates (n : Nat) : Nat → List Gate
  | 0 => []
  | k+1 => parityGates n k ++ xorBlock (resultWire n k) (k+1) (n+4*k)

theorem gateCount (n k : Nat) : (parityGates n k).length = 4*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [parityGates, xorBlock, ih, Nat.mul_succ]

theorem legalGates (n k : Nat) : ∀ g ∈ parityGates n k,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [parityGates]
  | succ k ih =>
    intro g hg
    rcases List.mem_append.mp hg with old | newGate
    · exact ih g old
    · simp only [xorBlock, List.mem_cons, List.not_mem_nil, or_false] at newGate
      rcases newGate with rfl | rfl | rfl | rfl <;> simp

theorem countXor (m : Nat) (b : Bool) :
    Bool.xor (decide (m % 2 = 1)) b = decide ((m + [b].count true) % 2 = 1) := by
  cases b <;> by_cases h : m % 2 = 1 <;> simp [h] <;> omega

theorem prefixValue (n k : Nat) (x : List Bool) (len : x.length = n) (hk : k < n) :
    readWire (runGates (parityGates n k) x) (resultWire n k) =
      decide ((x.take (k+1)).count true % 2 = 1) := by
  induction k with
  | zero =>
    cases x with
    | nil => simp at len; omega
    | cons b xs => cases b <;> simp [readWire, runGates, parityGates, resultWire]
  | succ k ih =>
    have hlen : (runGates (parityGates n k) x).length = n+4*k := by
      rw [runLength, gateCount, len]
    have hout : resultWire n k < n+4*k := by cases k <;> simp [resultWire] <;> omega
    have hinput : k+1 < x.length := by omega
    change readWire (runGates (parityGates n k ++ xorBlock (resultWire n k) (k+1) (n+4*k)) x) (n+4*k+3) = _
    rw [show runGates (parityGates n k ++ xorBlock (resultWire n k) (k+1) (n+4*k)) x =
      runGates (xorBlock (resultWire n k) (k+1) (n+4*k)) (runGates (parityGates n k) x) by
        simp [runGates, List.foldl_append]]
    rw [xorBlockValue _ _ _ _ hlen.symm hout (by omega), ih (by omega), preservesInput _ _ _ hinput]
    rw [List.take_succ_eq_append_getElem hinput, List.count_append]
    have hread : readWire x (k+1) = x[k+1] := by
      simp [readWire, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hinput]
    rw [hread, countXor]

end PEqualNP.Outside.L_meta_20784

theorem PEqualNP.Outside.L_meta_20784 : (∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((List.ofFn x).count true % 2 = 1)) (4 * (n - 1))) := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨PEqualNP.Outside.L_meta_20784.parityGates (k+1) k, PEqualNP.Outside.L_meta_20784.resultWire (k+1) k⟩
    refine ⟨C, PEqualNP.Outside.L_meta_20784.legalGates _ _, ?_, ?_⟩
    · simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_20784.gateCount]
    · intro x
      change PEqualNP.Outside.L_meta_20784.readWire
        (PEqualNP.Outside.L_meta_20784.runGates (PEqualNP.Outside.L_meta_20784.parityGates (k+1) k) (List.ofFn x))
        (PEqualNP.Outside.L_meta_20784.resultWire (k+1) k) = _
      have htake : (List.ofFn x).take (k+1) = List.ofFn x :=
        List.take_of_length_le (by rw [List.length_ofFn])
      simpa only [htake] using
        PEqualNP.Outside.L_meta_20784.prefixValue (k+1) k (List.ofFn x) List.length_ofFn (by omega)
