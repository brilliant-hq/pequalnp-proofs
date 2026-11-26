import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18868

abbrev Word := BitVec 32768

def inputAt (r : Fin 32768) (i : Fin 15) : Bool := r.val.testBit i.val


def joinHalves {n : Nat} (hi lo : BitVec (2^n)) : BitVec (2^(n+1)) :=
  (hi ++ lo).cast (by rw [Nat.pow_succ, Nat.mul_two])

theorem joinBit {n : Nat} (hi lo : BitVec (2^n)) (r : Nat) :
    (joinHalves hi lo).getLsbD r =
      if r < 2^n then lo.getLsbD r else hi.getLsbD (r - 2^n) := by
  simp only [joinHalves, BitVec.getLsbD_cast, BitVec.getLsbD_append]

def binaryColumn : (n i : Nat) → BitVec (2^n)
  | 0, _ => 0
  | n+1, i =>
      if i < n then
        let old := binaryColumn n i
        joinHalves old old
      else
        joinHalves (BitVec.allOnes (2^n)) 0

theorem binaryColumnBit {n i r : Nat} (hi : i < n) (hr : r < 2^n) :
    (binaryColumn n i).getLsbD r = r.testBit i := by
  induction n generalizing i r with
  | zero => omega
  | succ n ih =>
    have half : r - 2^n < 2^n := by rw [Nat.pow_succ, Nat.mul_two] at hr; omega
    by_cases lower : i < n
    · rw [binaryColumn, if_pos lower, joinBit]
      by_cases head : r < 2^n
      · exact (if_pos head).trans (ih lower head)
      · rw [if_neg head, ih lower half]
        have split : 2^n+(r-2^n)=r := by omega
        exact ((congrArg (fun t : Nat => t.testBit i) split).symm.trans
          (Nat.testBit_two_pow_add_gt lower (r-2^n))).symm
    · have eq : i=n := by omega
      subst i
      rw [binaryColumn, if_neg (by omega), joinBit]
      by_cases head : r < 2^n
      · rw [if_pos head, Nat.testBit_lt_two_pow head]
        simp [BitVec.getLsbD]
      · rw [if_neg head, BitVec.getLsbD_allOnes,
          Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_gt head) hr]
        exact decide_eq_true half

def source (i : Fin 15) : Word := binaryColumn 15 i.val

theorem sourceBit (r : Fin 32768) (i : Fin 15) :
    (source i).getLsbD r.val = inputAt r i :=
  binaryColumnBit i.isLt r.isLt


def inputRow (x : Fin 15 → Bool) : Fin 32768 :=
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  ⟨bits.toNat, by simpa using bits.isLt⟩

theorem rowCorrect (x : Fin 15 → Bool) : inputAt (inputRow x) = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dif_pos, Option.getD_some]

def observe (r : Fin 32768) (w : Word) : Bool := w.getLsbD r.val

def allBits (xs : List Word) : Word := xs.foldr (· &&& ·) (BitVec.allOnes 32768)
def anyBits (xs : List Word) : Word := xs.foldr (· ||| ·) 0

theorem allBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (allBits xs) = (xs.map (observe r)).all id := by
  induction xs with
  | nil =>
    change (BitVec.allOnes 32768).getLsbD r.val = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true r.isLt
  | cons x xs ih =>
    change observe r (x &&& allBits xs) = (observe r x && (xs.map (observe r)).all id)
    exact (BitVec.getLsbD_and).trans (congrArg (fun b => observe r x && b) ih)

theorem anyBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (anyBits xs) = (xs.map (observe r)).any id := by
  induction xs with
  | nil => simp [anyBits, observe]
  | cons x xs ih =>
    change observe r (x ||| anyBits xs) = (observe r x || (xs.map (observe r)).any id)
    exact (BitVec.getLsbD_or).trans (congrArg (fun b => observe r x || b) ih)

theorem observedRead (r : Fin 32768) (xs : List Word) (i : ℕ) :
    observe r (xs.getD i 0) = (xs.map (observe r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]

def packedGate (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => allBits xs
  | .or => anyBits xs
  | .not => ~~~(xs.headD 0)
  | _ => 0

theorem gateMatches (r : Fin 32768) (g : Gate) (ws : List Word)
    (ops : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    observe r (packedGate g.op (g.inputs.map (fun i => ws.getD i 0))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe r)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i 0)).map (observe r) =
      g.inputs.map (fun i => (ws.map (observe r)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead r ws i
  rcases ops with h | h | h
  · rw [h]
    change observe r (allBits _) = _
    rw [allBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (anyBits _) = _
    rw [anyBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (~~~((g.inputs.map fun i => ws.getD i 0).headD 0)) = !_
    rw [← reads]
    simp only [List.headD_eq_getD, ← observedRead]
    simp [observe, BitVec.getLsbD_not, r.isLt]

def packedRun : List Gate → List Word → List Word
  | [], ws => ws
  | g :: gs, ws => packedRun gs (ws ++ [packedGate g.op (g.inputs.map (fun i => ws.getD i 0))])

theorem runMatches (r : Fin 32768) (gs : List Gate) (ws : List Word)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (packedRun gs ws).map (observe r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (ws.map (observe r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [packedRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches r g ws (ops g (by simp))]



def witness : Circuit :=
  ⟨[⟨.or, [10, 12]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [13, 19]⟩, ⟨.and, [14, 20]⟩, ⟨.and, [17, 21]⟩, ⟨.or, [9, 22]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [2, 24]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [13, 26]⟩, ⟨.or, [10, 27]⟩, ⟨.or, [7, 28]⟩, ⟨.or, [3, 29]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [19, 31]⟩, ⟨.or, [12, 32]⟩, ⟨.and, [30, 33]⟩, ⟨.and, [25, 34]⟩, ⟨.or, [5, 35]⟩, ⟨.or, [1, 36]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [14, 38]⟩, ⟨.and, [11, 39]⟩, ⟨.or, [12, 40]⟩, ⟨.or, [7, 41]⟩, ⟨.or, [3, 42]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [38, 44]⟩, ⟨.or, [10, 45]⟩, ⟨.and, [43, 46]⟩, ⟨.or, [6, 47]⟩, ⟨.or, [2, 48]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [50, 51]⟩, ⟨.or, [7, 52]⟩, ⟨.or, [3, 53]⟩, ⟨.or, [14, 50]⟩, ⟨.and, [18, 55]⟩, ⟨.or, [12, 56]⟩, ⟨.or, [10, 57]⟩, ⟨.and, [54, 58]⟩, ⟨.or, [9, 59]⟩, ⟨.and, [49, 60]⟩, ⟨.and, [37, 61]⟩, ⟨.or, [0, 62]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [13, 64]⟩, ⟨.or, [14, 65]⟩, ⟨.and, [8, 66]⟩, ⟨.or, [12, 67]⟩, ⟨.or, [10, 68]⟩, ⟨.or, [3, 69]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [65, 71]⟩, ⟨.or, [7, 72]⟩, ⟨.and, [70, 73]⟩, ⟨.or, [9, 74]⟩, ⟨.or, [2, 75]⟩, ⟨.or, [14, 64]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [77, 78]⟩, ⟨.or, [10, 79]⟩, ⟨.or, [3, 80]⟩, ⟨.or, [14, 78]⟩, ⟨.and, [64, 82]⟩, ⟨.or, [12, 83]⟩, ⟨.or, [7, 84]⟩, ⟨.and, [81, 85]⟩, ⟨.or, [6, 86]⟩, ⟨.and, [76, 87]⟩, ⟨.or, [1, 88]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [14, 91]⟩, ⟨.and, [90, 92]⟩, ⟨.or, [12, 93]⟩, ⟨.or, [3, 94]⟩, ⟨.or, [14, 90]⟩, ⟨.and, [91, 96]⟩, ⟨.or, [10, 97]⟩, ⟨.or, [7, 98]⟩, ⟨.and, [95, 99]⟩, ⟨.or, [2, 100]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [13, 90]⟩, ⟨.and, [102, 103]⟩, ⟨.or, [3, 104]⟩, ⟨.or, [14, 103]⟩, ⟨.and, [4, 106]⟩, ⟨.or, [12, 107]⟩, ⟨.or, [10, 108]⟩, ⟨.or, [7, 109]⟩, ⟨.and, [105, 110]⟩, ⟨.or, [9, 111]⟩, ⟨.or, [6, 112]⟩, ⟨.and, [101, 113]⟩, ⟨.or, [5, 114]⟩, ⟨.and, [89, 115]⟩, ⟨.and, [63, 116]⟩, ⟨.not, [117]⟩], 118⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem witnessOps : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (witnessFit g hg).1


def packedWitness : Word := (packedRun witness.gates (List.ofFn source)).getD witness.output 0

theorem packedCorrect (r : Fin 32768) :
    observe r packedWitness = witness.eval (List.ofFn (inputAt r)) := by
  have inputs : (List.ofFn source).map (observe r) = List.ofFn (inputAt r) := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin 15 → Bool => List.ofFn f) (funext (fun i => sourceBit r i))
  unfold packedWitness Circuit.eval Circuit.wires
  rw [observedRead, runMatches r witness.gates _ witnessOps, inputs]

def expected : Word := (~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 1) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 2) &&& ~~~(source 5) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 14)) ||| (~~~(source 3) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 11) &&& ~~~(source 13)) ||| (~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 12)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 5) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 2) &&& ~~~(source 6) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 3) &&& ~~~(source 7) &&& ~~~(source 9) &&& ~~~(source 11) &&& ~~~(source 13)) ||| (~~~(source 0) &&& ~~~(source 4) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 12)) ||| (~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 14)) ||| (~~~(source 1) &&& ~~~(source 3) &&& ~~~(source 6) &&& ~~~(source 8) &&& ~~~(source 10) &&& ~~~(source 13)) ||| (~~~(source 1) &&& ~~~(source 4) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 11) &&& ~~~(source 12)) ||| (~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 5) &&& ~~~(source 8) &&& ~~~(source 11) &&& ~~~(source 12)) ||| (~~~(source 2) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 7) &&& ~~~(source 10) &&& ~~~(source 13)) ||| (~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 9) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 9) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 3) &&& ~~~(source 5) &&& ~~~(source 7) &&& ~~~(source 10) &&& ~~~(source 13)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 8) &&& ~~~(source 11) &&& ~~~(source 12)) ||| (~~~(source 0) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 11) &&& ~~~(source 12)) ||| (~~~(source 0) &&& ~~~(source 2) &&& ~~~(source 4) &&& ~~~(source 6) &&& ~~~(source 8) &&& ~~~(source 10) &&& ~~~(source 13)) ||| (~~~(source 0) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 14)) ||| (~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 12)) ||| (~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 4) &&& ~~~(source 7) &&& ~~~(source 9) &&& ~~~(source 11) &&& ~~~(source 13)) ||| (~~~(source 1) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 6) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 14)) ||| (~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 12)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 11) &&& ~~~(source 13)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14)) ||| (~~~(source 0) &&& ~~~(source 1) &&& ~~~(source 2) &&& ~~~(source 3) &&& ~~~(source 4) &&& ~~~(source 5) &&& ~~~(source 6) &&& ~~~(source 7) &&& ~~~(source 8) &&& ~~~(source 9) &&& ~~~(source 10) &&& ~~~(source 11) &&& ~~~(source 12) &&& ~~~(source 13) &&& ~~~(source 14))
def target (x : Fin 15 → Bool) : Bool := (!(x 5) && !(x 6) && !(x 7) && !(x 8) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 1) && !(x 6) && !(x 7) && !(x 8) && !(x 12) && !(x 13) && !(x 14)) || (!(x 2) && !(x 5) && !(x 7) && !(x 8) && !(x 10) && !(x 11) && !(x 14)) || (!(x 3) && !(x 5) && !(x 6) && !(x 8) && !(x 9) && !(x 11) && !(x 13)) || (!(x 4) && !(x 5) && !(x 6) && !(x 7) && !(x 9) && !(x 10) && !(x 12)) || (!(x 0) && !(x 1) && !(x 5) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 2) && !(x 6) && !(x 10) && !(x 11) && !(x 14)) || (!(x 0) && !(x 3) && !(x 7) && !(x 9) && !(x 11) && !(x 13)) || (!(x 0) && !(x 4) && !(x 8) && !(x 9) && !(x 10) && !(x 12)) || (!(x 1) && !(x 2) && !(x 7) && !(x 8) && !(x 9) && !(x 14)) || (!(x 1) && !(x 3) && !(x 6) && !(x 8) && !(x 10) && !(x 13)) || (!(x 1) && !(x 4) && !(x 6) && !(x 7) && !(x 11) && !(x 12)) || (!(x 2) && !(x 3) && !(x 5) && !(x 8) && !(x 11) && !(x 12)) || (!(x 2) && !(x 4) && !(x 5) && !(x 7) && !(x 10) && !(x 13)) || (!(x 3) && !(x 4) && !(x 5) && !(x 6) && !(x 9) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 5) && !(x 6) && !(x 9) && !(x 14)) || (!(x 0) && !(x 1) && !(x 3) && !(x 5) && !(x 7) && !(x 10) && !(x 13)) || (!(x 0) && !(x 1) && !(x 4) && !(x 5) && !(x 8) && !(x 11) && !(x 12)) || (!(x 0) && !(x 2) && !(x 3) && !(x 6) && !(x 7) && !(x 11) && !(x 12)) || (!(x 0) && !(x 2) && !(x 4) && !(x 6) && !(x 8) && !(x 10) && !(x 13)) || (!(x 0) && !(x 3) && !(x 4) && !(x 7) && !(x 8) && !(x 9) && !(x 14)) || (!(x 1) && !(x 2) && !(x 3) && !(x 8) && !(x 9) && !(x 10) && !(x 12)) || (!(x 1) && !(x 2) && !(x 4) && !(x 7) && !(x 9) && !(x 11) && !(x 13)) || (!(x 1) && !(x 3) && !(x 4) && !(x 6) && !(x 10) && !(x 11) && !(x 14)) || (!(x 2) && !(x 3) && !(x 4) && !(x 5) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 3) && !(x 5) && !(x 6) && !(x 7) && !(x 9) && !(x 10) && !(x 12)) || (!(x 0) && !(x 1) && !(x 2) && !(x 4) && !(x 5) && !(x 6) && !(x 8) && !(x 9) && !(x 11) && !(x 13)) || (!(x 0) && !(x 1) && !(x 3) && !(x 4) && !(x 5) && !(x 7) && !(x 8) && !(x 10) && !(x 11) && !(x 14)) || (!(x 0) && !(x 2) && !(x 3) && !(x 4) && !(x 6) && !(x 7) && !(x 8) && !(x 12) && !(x 13) && !(x 14)) || (!(x 1) && !(x 2) && !(x 3) && !(x 4) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 3) && !(x 4) && !(x 5) && !(x 6) && !(x 7) && !(x 8) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14))

set_option maxRecDepth 16000 in
theorem expectedCorrect (r : Fin 32768) :
    observe r expected = target (inputAt r) := by
  simp only [expected, target, observe, BitVec.getLsbD_not, r.isLt, decide_true,
    Bool.true_and, BitVec.getLsbD_and, BitVec.getLsbD_or, sourceBit]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 60000000 in
theorem wordsMatch : packedWitness = expected := by
  decide +kernel

end PEqualNP.Outside.L_meta_18868

open PEqualNP.Outside.L_meta_18868 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_18868 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (!(x 5) && !(x 6) && !(x 7) && !(x 8) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 1) && !(x 6) && !(x 7) && !(x 8) && !(x 12) && !(x 13) && !(x 14)) || (!(x 2) && !(x 5) && !(x 7) && !(x 8) && !(x 10) && !(x 11) && !(x 14)) || (!(x 3) && !(x 5) && !(x 6) && !(x 8) && !(x 9) && !(x 11) && !(x 13)) || (!(x 4) && !(x 5) && !(x 6) && !(x 7) && !(x 9) && !(x 10) && !(x 12)) || (!(x 0) && !(x 1) && !(x 5) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 2) && !(x 6) && !(x 10) && !(x 11) && !(x 14)) || (!(x 0) && !(x 3) && !(x 7) && !(x 9) && !(x 11) && !(x 13)) || (!(x 0) && !(x 4) && !(x 8) && !(x 9) && !(x 10) && !(x 12)) || (!(x 1) && !(x 2) && !(x 7) && !(x 8) && !(x 9) && !(x 14)) || (!(x 1) && !(x 3) && !(x 6) && !(x 8) && !(x 10) && !(x 13)) || (!(x 1) && !(x 4) && !(x 6) && !(x 7) && !(x 11) && !(x 12)) || (!(x 2) && !(x 3) && !(x 5) && !(x 8) && !(x 11) && !(x 12)) || (!(x 2) && !(x 4) && !(x 5) && !(x 7) && !(x 10) && !(x 13)) || (!(x 3) && !(x 4) && !(x 5) && !(x 6) && !(x 9) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 5) && !(x 6) && !(x 9) && !(x 14)) || (!(x 0) && !(x 1) && !(x 3) && !(x 5) && !(x 7) && !(x 10) && !(x 13)) || (!(x 0) && !(x 1) && !(x 4) && !(x 5) && !(x 8) && !(x 11) && !(x 12)) || (!(x 0) && !(x 2) && !(x 3) && !(x 6) && !(x 7) && !(x 11) && !(x 12)) || (!(x 0) && !(x 2) && !(x 4) && !(x 6) && !(x 8) && !(x 10) && !(x 13)) || (!(x 0) && !(x 3) && !(x 4) && !(x 7) && !(x 8) && !(x 9) && !(x 14)) || (!(x 1) && !(x 2) && !(x 3) && !(x 8) && !(x 9) && !(x 10) && !(x 12)) || (!(x 1) && !(x 2) && !(x 4) && !(x 7) && !(x 9) && !(x 11) && !(x 13)) || (!(x 1) && !(x 3) && !(x 4) && !(x 6) && !(x 10) && !(x 11) && !(x 14)) || (!(x 2) && !(x 3) && !(x 4) && !(x 5) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 3) && !(x 5) && !(x 6) && !(x 7) && !(x 9) && !(x 10) && !(x 12)) || (!(x 0) && !(x 1) && !(x 2) && !(x 4) && !(x 5) && !(x 6) && !(x 8) && !(x 9) && !(x 11) && !(x 13)) || (!(x 0) && !(x 1) && !(x 3) && !(x 4) && !(x 5) && !(x 7) && !(x 8) && !(x 10) && !(x 11) && !(x 14)) || (!(x 0) && !(x 2) && !(x 3) && !(x 4) && !(x 6) && !(x 7) && !(x 8) && !(x 12) && !(x 13) && !(x 14)) || (!(x 1) && !(x 2) && !(x 3) && !(x 4) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14)) || (!(x 0) && !(x 1) && !(x 2) && !(x 3) && !(x 4) && !(x 5) && !(x 6) && !(x 7) && !(x 8) && !(x 9) && !(x 10) && !(x 11) && !(x 12) && !(x 13) && !(x 14))) 120 := by
  change PEqualNP.MetaComplexity.HasCircuitSize 15 target 120
  refine ⟨witness, witnessFit, by decide, ?_⟩
  intro x
  have h := packedCorrect (inputRow x)
  rw [wordsMatch, expectedCorrect, rowCorrect] at h
  exact h.symm
