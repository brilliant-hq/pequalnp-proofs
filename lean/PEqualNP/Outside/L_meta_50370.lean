import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50370_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateValue {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def step {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [gateValue bank g]

theorem readBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem andBits {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem orBits {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem gateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (gateValue bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval, andBits, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact readBit bank i.val k
  · simp only [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval, orBits, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact readBit bank i.val k
  · simp only [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, readBit]

theorem foldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl step bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (step bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [step, List.map_append, List.map_cons, List.map_nil,
        gateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (step bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

abbrev Word := BitVec 6

def seed : List Word := [62, 60, 56, 48, 32, 0, 63]

def targets : List Word := [6#6, 34#6, 50#6]

def binaryResults (bank : List Word) : List Word :=
  (bank.flatMap fun x => bank.flatMap fun y => [x &&& y, x ||| y]).dedup

def unaryResults (bank : List Word) : List Word :=
  (bank.map fun x => ~~~x).dedup

theorem binaryMem {bank : List Word} {x y : Word}
    (hx : x ∈ bank) (hy : y ∈ bank) :
    x &&& y ∈ binaryResults bank ∧ x ||| y ∈ binaryResults bank := by
  unfold binaryResults
  simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨x, hx, y, hy, Or.inl rfl⟩, ⟨x, hx, y, hy, Or.inr rfl⟩⟩

theorem binaryCopy {bank : List Word} {x : Word} (hx : x ∈ bank) :
    x ∈ binaryResults bank := by
  simpa using (binaryMem hx hx).1

theorem unaryMem {bank : List Word} {x : Word} (hx : x ∈ bank) :
    ~~~x ∈ unaryResults bank := by
  exact List.mem_dedup.mpr (List.mem_map_of_mem hx)

theorem readMem {bank wires : List Word} (hz : 0 ∈ bank)
    (hsub : ∀ w ∈ wires, w ∈ bank) (i : Nat) : wires.getD i 0 ∈ bank := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : wires[i]? with
  | none => exact hz
  | some x => exact hsub x (List.mem_of_getElem? hi)

def isInverter (g : Gate) : Bool :=
  @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)

theorem gateResult {bank wires : List Word} (hz : 0 ∈ bank)
    (ho : BitVec.allOnes 6 ∈ bank) (sub : ∀ w ∈ wires, w ∈ bank)
    (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (small : g.inputs.length ≤ 2) :
    if isInverter g then gateValue wires g ∈ unaryResults bank
    else gateValue wires g ∈ binaryResults bank := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have rd (i : Nat) := readMem hz sub i
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · simpa [gateValue, isInverter] using binaryCopy ho
    · change (wires.getD i 0 &&& BitVec.allOnes 6) ∈ binaryResults bank
      simpa only [BitVec.and_allOnes] using binaryCopy (rd i)
    · change (wires.getD i 0 &&& (wires.getD j 0 &&& BitVec.allOnes 6)) ∈ binaryResults bank
      simpa only [BitVec.and_allOnes] using (binaryMem (rd i) (rd j)).1
    · simp at small
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · simpa [gateValue, isInverter] using binaryCopy hz
    · simpa [gateValue, isInverter] using binaryCopy (rd i)
    · simpa [gateValue, isInverter] using (binaryMem (rd i) (rd j)).2
    · simp at small
  · cases ins with
    | nil => simpa [gateValue, isInverter] using unaryMem hz
    | cons i rest => simpa [gateValue, isInverter] using unaryMem (rd i)

def allPresent (bank : List Word) : Bool :=
  targets.all bank.contains

def missing (bank : List Word) : Nat :=
  (if 6#6 ∈ bank then 0 else 1) +
  (if 34#6 ∈ bank then 0 else 1) +
  (if 50#6 ∈ bank then 0 else 1)

theorem missingStep (bank : List Word) (w : Word) :
    missing bank ≤ missing (w :: bank) + 1 := by
  have h₁ : 6#6 ≠ 34#6 := by decide
  have h₂ : 6#6 ≠ 50#6 := by decide
  have h₃ : 34#6 ≠ 50#6 := by decide
  have bound (p : Prop) [Decidable p] : (if p then 0 else (1 : Nat)) ≤ 1 := by
    split <;> decide
  by_cases h₆ : 6#6 = w
  · subst w
    have b := bound (6#6 ∈ bank)
    simp [missing, Ne.symm h₁, Ne.symm h₂]
    omega
  · by_cases h₃₄ : 34#6 = w
    · subst w
      have b := bound (34#6 ∈ bank)
      simp [missing, h₁, Ne.symm h₃]
      omega
    · by_cases h₅₀ : 50#6 = w
      · subst w
        have b := bound (50#6 ∈ bank)
        simp [missing, h₂, h₃]
        omega
      · simp [missing, h₆, h₃₄, h₅₀]

theorem stepSub {wires bank : List Word} {g : Gate}
    (sub : ∀ w ∈ wires, w ∈ bank) (added : gateValue wires g ∈ bank) :
    ∀ w ∈ step wires g, w ∈ bank := by
  intro w hw
  change w ∈ wires ++ [gateValue wires g] at hw
  rcases List.mem_append.mp hw with left | right
  · exact sub w left
  · rwa [List.mem_singleton.mp right]

theorem missingLower (gs : List Gate) {bank wires : List Word}
    (sub : ∀ w ∈ wires, w ∈ bank)
    (hits : ∀ w ∈ targets, w ∈ gs.foldl step wires) : missing bank ≤ gs.length := by
  induction gs generalizing bank wires with
  | nil =>
    have h₆ := sub 6#6 (hits 6#6 (by simp [targets]))
    have h₃₄ := sub 34#6 (hits 34#6 (by simp [targets]))
    have h₅₀ := sub 50#6 (hits 50#6 (by simp [targets]))
    simp [missing, h₆, h₃₄, h₅₀]
  | cons g tail ih =>
    have sub' : ∀ w ∈ step wires g, w ∈ gateValue wires g :: bank :=
      stepSub (fun w hw => List.mem_cons_of_mem _ (sub w hw)) List.mem_cons_self
    have lower := ih sub' hits
    exact (missingStep bank (gateValue wires g)).trans (Nat.add_le_add_right lower 1)

def canBuild : Nat → Nat → List Word → Bool
  | 0, _, bank => allPresent bank
  | n+1, negs, bank =>
      if n+1 < missing bank then false else
      allPresent bank || canBuild n negs bank ||
      (binaryResults bank).any (fun w => !bank.contains w && canBuild n negs (w :: bank)) ||
      (negs != 0 && (unaryResults bank).any
        (fun w => !bank.contains w && canBuild n (negs-1) (w :: bank)))

def notGates (gs : List Gate) : Nat :=
  (gs.filter isInverter).length

theorem allPresentOf {bank : List Word} (h : ∀ w ∈ targets, w ∈ bank) :
    allPresent bank = true :=
  List.all_eq_true.mpr fun w hw => List.contains_iff_mem.mpr (h w hw)

theorem buildSound (n : Nat) {negs : Nat} {bank wires : List Word} {gs : List Gate}
    (hz : 0 ∈ bank) (ho : BitVec.allOnes 6 ∈ bank)
    (sub : ∀ w ∈ wires, w ∈ bank)
    (fan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
      ∧ g.inputs.length ≤ 2)
    (gates : gs.length ≤ n) (inverters : notGates gs ≤ negs)
    (hits : ∀ w ∈ targets, w ∈ gs.foldl step wires) :
    canBuild n negs bank = true := by
  induction n generalizing negs bank wires gs with
  | zero =>
    cases gs with
    | nil => exact allPresentOf (fun w hw => sub w (hits w hw))
    | cons g gs => simp at gates
  | succ n ih =>
    have cap := Nat.not_lt_of_ge ((missingLower gs sub hits).trans gates)
    cases gs with
    | nil =>
      have ok := allPresentOf (fun w hw => sub w (hits w hw))
      simp [canBuild, cap, ok]
    | cons g gs =>
      let w := gateValue wires g
      let nextWires := step wires g
      have tailFan k hk := fan k (List.mem_cons_of_mem g hk)
      have leftGates : gs.length ≤ n := by simpa using gates
      have nextHits : ∀ u ∈ targets, u ∈ gs.foldl step nextWires := hits
      have thisFan := fan g List.mem_cons_self
      have gate := gateResult hz ho sub g thisFan.1 thisFan.2
      have noDuplicate (h : w ∉ bank) : bank.contains w = false := by
        simpa using h
      have nextSub : ∀ u ∈ nextWires, u ∈ w :: bank :=
        stepSub (fun u hu => List.mem_cons_of_mem _ (sub u hu)) List.mem_cons_self
      have hz' := List.mem_cons_of_mem w hz
      have ho' := List.mem_cons_of_mem w ho
      by_cases hw : w ∈ bank
      · have le : notGates gs ≤ negs := by
          by_cases h : isInverter g = true <;> simp [notGates, h] at inverters ⊢ <;> omega
        have follow := ih hz ho (stepSub sub hw)
          tailFan leftGates le nextHits
        simp [canBuild, cap, follow]
      · by_cases hg : isInverter g = true
        · have avail : w ∈ unaryResults bank := by simpa [hg, w] using gate
          have le : notGates gs + 1 ≤ negs := by simpa [notGates, hg] using inverters
          have nonzero : negs ≠ 0 := by omega
          have nextLe : notGates gs ≤ negs - 1 := by omega
          have follow := ih hz' ho' nextSub tailFan leftGates nextLe nextHits
          have any : (unaryResults bank).any
              (fun u => !bank.contains u && canBuild n (negs-1) (u :: bank)) = true :=
            List.any_eq_true.mpr ⟨w, avail, by rw [noDuplicate hw, follow]; rfl⟩
          have someNeg : (negs != 0) = true := by simpa using nonzero
          simp only [canBuild, cap, ite_false, someNeg, any, Bool.and_self, Bool.or_true]
        · have avail : w ∈ binaryResults bank := by simpa [hg, w] using gate
          have le : notGates gs ≤ negs := by simpa [notGates, hg] using inverters
          have follow := ih hz' ho' nextSub tailFan leftGates le nextHits
          have any : (binaryResults bank).any
              (fun u => !bank.contains u && canBuild n negs (u :: bank)) = true :=
            List.any_eq_true.mpr ⟨w, avail, by rw [noDuplicate hw, follow]; rfl⟩
          simp only [canBuild, cap, ite_false, any, Bool.or_true, Bool.true_or]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem excluded : canBuild 5 2 seed = false := by
  decide +kernel

theorem inputBits : ∀ t : Fin 6, seed.map (fun x => x.getLsbD t.val) =
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] := by
  decide +kernel

theorem outputMem (C : Circuit) (fan : FanInTwo C) (i : Nat) (word : Word)
    (nz : word ≠ 0)
    (h : ∀ t : Fin 6,
      (C.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD i false =
        word.getLsbD t.val) : word ∈ C.gates.foldl step seed := by
  let bank := C.gates.foldl step seed
  have same : bank.getD i 0 = word := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let t : Fin 6 := ⟨j, hj⟩
    change (bank.getD i 0).getLsbD t.val = word.getLsbD t.val
    rw [readBit, foldBits seed t C.gates fan, inputBits t]
    exact h t
  rw [List.getD_eq_getElem?_getD] at same
  cases heq : bank[i]? with
  | none =>
    simp only [heq, Option.getD_none] at same
    exact (nz same.symm).elim
  | some v =>
    have hv : v = word := by simpa [heq] using same
    rw [← hv]
    exact List.mem_of_getElem? heq

end PEqualNP.Outside.L_meta_50370_aux

theorem PEqualNP.Outside.L_meta_50370 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val)) := by
  intro ⟨C, p, q, r, fan, _, inv, size, truth⟩
  have hp := L_meta_50370_aux.outputMem C fan p.val 6 (by decide) (fun t => (truth t).1)
  have hq := L_meta_50370_aux.outputMem C fan q.val 34 (by decide) (fun t => (truth t).2.1)
  have hr := L_meta_50370_aux.outputMem C fan r.val 50 (by decide) (fun t => (truth t).2.2)
  have hits : ∀ w ∈ L_meta_50370_aux.targets,
      w ∈ C.gates.foldl L_meta_50370_aux.step L_meta_50370_aux.seed := by
    intro w hw
    simp only [L_meta_50370_aux.targets, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have builds := L_meta_50370_aux.buildSound 5 (negs := 2) (by decide) (by decide)
    (fun _ h => h) fan size inv hits
  rw [L_meta_50370_aux.excluded] at builds
  contradiction
