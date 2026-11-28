import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51216_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def andWord (a b : Nat) : Nat := (a &&& b) % 64
def orWord (a b : Nat) : Nat := (a ||| b) % 64
def notWord (a : Nat) : Nat := (63 ^^^ a) % 64

def applyWord : GateOp → List Nat → Nat
  | .and, xs => andWord (xs.headD 63) (xs.tail.headD 63)
  | .or, xs => orWord (xs.headD 0) (xs.tail.headD 0)
  | .not, xs => notWord (xs.headD 0)
  | .mod _, _ | .maj, _ => 0

def gateWord (g : Gate) (wires : List Nat) : Nat :=
  applyWord g.op (g.inputs.map (fun i => wires.getD i 0))

def wordWires : List Gate → List Nat → List Nat
  | [], ws => ws
  | g :: rest, ws => wordWires rest (ws ++ [gateWord g ws])

def legalOp (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not


def isInverter (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def charge (g : Gate) : Nat := if isInverter g then 1 else 0

def usedNots (gs : List Gate) : Nat := (gs.filter isInverter).length

theorem usedNots_cons (g : Gate) (gs : List Gate) :
    usedNots (g :: gs) = charge g + usedNots gs := by
  cases h : isInverter g <;> simp [usedNots, charge, h, Nat.add_comm]

theorem notCount_bridge (D : Circuit) : usedNots D.gates = PEqualNP.NotBracket.notCount D := by
  unfold usedNots PEqualNP.NotBracket.notCount
  apply congrArg List.length
  apply List.filter_congr
  intro g _
  obtain ⟨op, xs⟩ := g
  cases op <;> simp [isInverter]

def grow (bank : List Nat) (w : Nat) : List Nat :=
  if w ∈ bank then bank else w :: bank

theorem mem_grow_left {bank : List Nat} {w v : Nat} (h : v ∈ bank) :
    v ∈ grow bank w := by
  by_cases hw : w ∈ bank <;> simp [grow, hw, h]

theorem mem_grow_word (bank : List Nat) (w : Nat) : w ∈ grow bank w := by
  by_cases hw : w ∈ bank <;> simp [grow, hw]

def binaryWords (bank : List Nat) : List Nat :=
  (bank.flatMap (fun a => bank.flatMap (fun b => [andWord a b, orWord a b]))).eraseDups

theorem andChoice {bank : List Nat} {a b : Nat} (ha : a ∈ bank) (hb : b ∈ bank) :
    andWord a b ∈ binaryWords bank := by
  unfold binaryWords
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, by simp⟩⟩

theorem orChoice {bank : List Nat} {a b : Nat} (ha : a ∈ bank) (hb : b ∈ bank) :
    orWord a b ∈ binaryWords bank := by
  unfold binaryWords
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, by simp⟩⟩

def moves (bank : List Nat) (k : Nat) : List (Nat × Nat) :=
  (binaryWords bank).map (fun w => (w, k)) ++
    if k = 0 then [] else bank.map (fun w => (notWord w, k - 1))

theorem getD_mem_or_default {xs : List Nat} {v : Nat} (i : Nat) :
    xs.getD i v ∈ xs ∨ xs.getD i v = v := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem head_in {xs bank : List Nat} {fallback : Nat} (h : ∀ w ∈ xs, w ∈ bank)
    (hd : fallback ∈ bank) : xs.headD fallback ∈ bank := by
  cases xs with
  | nil => exact hd
  | cons w rest => exact h w (by simp)

theorem gateMove {g : Gate} {ws bank : List Nat} {k : Nat}
    (h0 : 0 ∈ bank) (h1 : 63 ∈ bank) (hp : ∀ w ∈ ws, w ∈ bank)
    (hop : legalOp g.op) (hbudget : charge g ≤ k) :
    (gateWord g ws, k - charge g) ∈ moves bank k := by
  let args := g.inputs.map (fun i => ws.getD i 0)
  have allArgs : ∀ w ∈ args, w ∈ bank := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    rcases getD_mem_or_default (xs := ws) (v := 0) i with hi | hi
    · exact hp _ hi
    · rwa [hi]
  have tailArgs : ∀ w ∈ args.tail, w ∈ bank := by
    intro w hw
    exact allArgs w (List.mem_of_mem_tail hw)
  unfold gateWord
  change (applyWord g.op args, k - charge g) ∈ moves bank k
  rcases hop with ho | ho | ho
  · have hz := andChoice (head_in allArgs h1) (head_in tailArgs h1)
    apply List.mem_append_left
    simpa [ho, applyWord, charge, isInverter] using (List.mem_map_of_mem (f := fun w => (w, k)) hz)
  · have hz := orChoice (head_in allArgs h0) (head_in tailArgs h0)
    apply List.mem_append_left
    simpa [ho, applyWord, charge, isInverter] using (List.mem_map_of_mem (f := fun w => (w, k)) hz)
  · have hk : k ≠ 0 := by simp [charge, isInverter, ho] at hbudget; omega
    unfold moves
    rw [if_neg hk]
    apply List.mem_append_right
    simpa [ho, applyWord, charge, isInverter] using
      (List.mem_map_of_mem (f := fun w => (notWord w, k - 1)) (head_in allArgs h0))

def countMissing (bank goals : List Nat) : Nat :=
  (goals.filter (fun w => !bank.contains w)).length

def blocked : Nat → Nat → List Nat → List Nat → Bool
  | 0, _, bank, goals => !goals.all bank.contains
  | n + 1, k, bank, goals =>
      if n + 1 < countMissing bank goals then true
      else !goals.all bank.contains &&
        (moves bank k).all (fun t => blocked n t.2 (grow bank t.1) goals)

theorem wordWires_append (gs : List Gate) (ws : List Nat) :
    ∃ extra : List Nat, wordWires gs ws = ws ++ extra ∧ extra.length = gs.length := by
  induction gs generalizing ws with
  | nil => exact ⟨[], by simp [wordWires]⟩
  | cons g gs ih =>
    obtain ⟨extra, he, hl⟩ := ih (ws ++ [gateWord g ws])
    exact ⟨gateWord g ws :: extra, by simpa [wordWires, List.append_assoc] using he, by simp [hl]⟩

theorem missing_le_gates {gs : List Gate} {bank ws goals : List Nat} (hn : goals.Nodup)
    (hs : ∀ w ∈ ws, w ∈ bank) (hit : ∀ w ∈ goals, w ∈ wordWires gs ws) :
    countMissing bank goals ≤ gs.length := by
  obtain ⟨extra, he, ht⟩ := wordWires_append gs ws
  let pending := goals.filter (fun w => !bank.contains w)
  have hs' : pending.toFinset ⊆ extra.toFinset := by
    intro w hw
    obtain ⟨hg, hb⟩ := List.mem_filter.mp (List.mem_toFinset.mp hw)
    have hnmem : w ∉ bank := by simpa using hb
    have h' := hit w hg
    rw [he] at h'
    rcases List.mem_append.mp h' with hw | hw
    · exact (hnmem (hs _ hw)).elim
    · exact List.mem_toFinset.mpr hw
  have hc : pending.Nodup := hn.filter _
  have hl : pending.length = pending.toFinset.card := by
    symm
    exact List.toFinset_card_of_nodup hc
  change pending.length ≤ gs.length
  rw [hl, ← ht]
  exact le_trans (Finset.card_le_card hs') (List.toFinset_card_le _)

theorem blocked_sound {gs : List Gate} {n k : Nat} {bank ws goals : List Nat}
    (proof : blocked n k bank goals = true) (hn : goals.Nodup)
    (zeroIn : 0 ∈ bank) (fullIn : 63 ∈ bank) (seen : ∀ w ∈ ws, w ∈ bank)
    (sizeFits : gs.length ≤ n) (notsFit : usedNots gs ≤ k)
    (legal : ∀ g ∈ gs, legalOp g.op) (hit : ∀ w ∈ goals, w ∈ wordWires gs ws) : False := by
  induction gs generalizing n k bank ws with
  | nil =>
    have hneeded : countMissing bank goals ≤ 0 := missing_le_gates hn seen hit
    have found : goals.all bank.contains = true := List.all_eq_true.mpr
      (fun w hw => List.contains_iff_mem.mpr (seen w (hit w hw)))
    cases n with
    | zero => simp [blocked, found] at proof
    | succ n => simp [blocked, found, show ¬ n + 1 < countMissing bank goals by omega] at proof
  | cons g gs ih =>
    cases n with
    | zero => simp at sizeFits
    | succ n =>
      have lengthFits : gs.length ≤ n := by simpa using sizeFits
      have hneeded := missing_le_gates hn seen hit
      have hop := legal g (by simp)
      rw [usedNots_cons] at notsFit
      have hmove : (gateWord g ws, k - charge g) ∈ moves bank k :=
        gateMove zeroIn fullIn seen hop (by omega)
      rw [blocked, if_neg (show ¬ n + 1 < countMissing bank goals from
        Nat.not_lt.mpr (le_trans hneeded sizeFits))] at proof
      simp only [Bool.and_eq_true] at proof
      have next := List.all_eq_true.mp proof.2 _ hmove
      have extendSeen : ∀ w ∈ ws ++ [gateWord g ws], w ∈ grow bank (gateWord g ws) := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact mem_grow_left (seen w hw)
        · rw [List.mem_singleton.mp hw]
          exact mem_grow_word _ _
      exact ih next (mem_grow_left zeroIn) (mem_grow_left fullIn) extendSeen lengthFits
        (by omega) (fun h hh => legal h (List.mem_cons_of_mem _ hh)) hit

def initial : List Nat := [62, 60, 56, 48, 32, 0, 63]
def readRow (t : Fin 6) (w : Nat) : Bool := w.testBit t.val


theorem fullBit (t : Fin 6) : (63 : Nat).testBit t.val = true := by
  revert t
  decide +kernel

theorem modBit (t : Fin 6) (a : Nat) : (a % 64).testBit t.val = a.testBit t.val := by
  change (a % (2 ^ 6)).testBit t.val = a.testBit t.val
  rw [Nat.testBit_mod_two_pow]
  simp [t.isLt]

theorem gateBit {op : GateOp} {xs : List Nat} (t : Fin 6) (h : legalOp op)
    (size : xs.length ≤ 2) : readRow t (applyWord op xs) = op.eval (xs.map (readRow t)) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases h with he | he | he <;> subst op <;>
      simp [applyWord, andWord, orWord, notWord, GateOp.eval, readRow, fullBit]
  · rcases h with he | he | he <;> subst op <;>
      simp [applyWord, andWord, orWord, notWord, GateOp.eval, readRow, modBit, fullBit,
        Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  · rcases h with he | he | he <;> subst op <;>
      simp [applyWord, andWord, orWord, notWord, GateOp.eval, readRow, modBit, fullBit,
        Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  · simp at size

theorem readGetD (t : Fin 6) (ws : List Nat) (i : Nat) :
    (ws.map (readRow t)).getD i false = readRow t (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> simp [readRow]

theorem gateReads (t : Fin 6) (ws : List Nat) (g : Gate)
    (valid : legalOp g.op ∧ g.inputs.length ≤ 2) :
    readRow t (gateWord g ws) = g.op.eval (g.inputs.map
      (fun i => (ws.map (readRow t)).getD i false)) := by
  rw [gateWord, gateBit t valid.1 (by simpa using valid.2)]
  simp only [List.map_map, Function.comp_def, readGetD]

theorem wordWires_reads (t : Fin 6) (gs : List Gate) (ws : List Nat)
    (fan : ∀ g ∈ gs, legalOp g.op ∧ g.inputs.length ≤ 2) :
    (wordWires gs ws).map (readRow t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (ws.map (readRow t)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have htail : ∀ h ∈ gs, legalOp h.op ∧ h.inputs.length ≤ 2 :=
      fun h hh => fan h (List.mem_cons_of_mem _ hh)
    change (wordWires gs (ws ++ [gateWord g ws])).map (readRow t) = _
    rw [ih _ htail, List.map_append]
    simp only [List.foldl_cons, List.map_cons, List.map_nil]
    rw [gateReads t ws g (fan g (by simp))]

theorem readInitial : ∀ t : Fin 6, initial.map (readRow t) =
    List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false,true] := by
  decide +kernel

theorem wordBound (g : Gate) (ws : List Nat) : gateWord g ws < 64 := by
  unfold gateWord
  cases g.op <;> simp [applyWord, andWord, orWord, notWord, Nat.mod_lt]

theorem wordWires_bound (gs : List Gate) (ws : List Nat) (h : ∀ w ∈ ws, w < 64) :
    ∀ w ∈ wordWires gs ws, w < 64 := by
  induction gs generalizing ws with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h w hw
    · rw [List.mem_singleton.mp hw]
      exact wordBound g ws

theorem sameSixRows {a b : Nat} (ha : a < 64) (hb : b < 64)
    (eq : ∀ t : Fin 6, readRow t a = readRow t b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact eq ⟨i, hi⟩
  · have hk : 6 ≤ i := by omega
    have pow : 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha pow), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb pow)]

theorem bitPort (D : Circuit) {i a : Nat} (ha : a < 64)
    (fan : ∀ g ∈ D.gates, legalOp g.op ∧ g.inputs.length ≤ 2)
    (hp : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false,true])).getD i false =
        a.testBit t.val) : a ∈ wordWires D.gates initial := by
  let ys := wordWires D.gates initial
  let v := ys.getD i 0
  have hzero : 0 ∈ ys := by
    obtain ⟨extra, he, _⟩ := wordWires_append D.gates initial
    change 0 ∈ wordWires D.gates initial
    rw [he]
    exact List.mem_append_left _ (by decide)
  have hv : v ∈ ys := by
    rcases getD_mem_or_default (xs := ys) (v := 0) i with h | h
    · exact h
    · change v = 0 at h
      rwa [h]
  have hsmall : v < 64 := wordWires_bound _ _ (by decide) _ hv
  have he : v = a := by
    apply sameSixRows hsmall ha
    intro t
    change readRow t (ys.getD i 0) = _
    rw [← readGetD, show ys.map (readRow t) = D.wires
        ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false,true]) by
        unfold ys Circuit.wires
        rw [wordWires_reads t _ _ fan, readInitial]]
    exact hp t
  rwa [he] at hv

def targets : List Nat := [10, 42, 58]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verdict : blocked 5 2 initial targets = true := by decide +kernel

theorem legalCircuit {D : Circuit} (h : FanInTwo D) :
    ∀ g ∈ D.gates, legalOp g.op ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simpa [legalOp] using h g hg

end PEqualNP.Outside.L_meta_51216_aux

open PEqualNP.Outside.L_meta_51216_aux in

theorem PEqualNP.Outside.L_meta_51216 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (42 : Nat).testBit t.val ∧
    w.getD r.val false = (58 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, reports⟩
  have legal := legalCircuit hfan
  have hp := bitPort D (i := p.val) (a := 10) (by decide) legal (fun x => (reports x).1)
  have hq := bitPort D (i := q.val) (a := 42) (by decide) legal (fun x => (reports x).2.1)
  have hr := bitPort D (i := r.val) (a := 58) (by decide) legal (fun x => (reports x).2.2)
  exact blocked_sound verdict (by decide) (by decide) (by decide) (fun _ hw => hw) hsize
    (by rw [notCount_bridge D]; exact hnot)
    (fun g hg => (legal g hg).1) (by
      intro w hw
      simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hp
      · exact hq
      · exact hr)

