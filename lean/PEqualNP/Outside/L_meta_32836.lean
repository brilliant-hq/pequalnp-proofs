import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32836.Contraction
abbrev Forest := Nat → Nat × Nat
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
abbrev CutCheck := RowState → Bool
def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token
def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
abbrev Bound := Nat × List Word × Nat × Word
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws
def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
variable {mask : Nat} {target : Word}
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _
theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]
theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m
def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m
theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]
theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]
theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..
theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
namespace PackedRect
def full : ℕ := 22300745198530623141535718272648361505980415
def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')
def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)
end PackedRect
abbrev Witness := Word × Nat × Nat
def witnessWord (w : Witness) : Word := w.1
def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)
def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal
abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right
def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true
theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]
theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩
theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩
theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩
theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih
def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w
theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]
theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)
def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0
theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩
theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]
theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]
theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]
def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word
theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl
def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont
theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws
theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢
theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail
abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word
def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use
theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]
def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2
def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))
def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use
theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl
def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)
abbrev DagTagged := Word × DagSignals
def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0
def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token
def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank
def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]
theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]
theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h
theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd
theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)
def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w
abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)
def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray
def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal
def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)
theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok
theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩
def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)
def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)
theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0
theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp
theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c
theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]
def GateWordMono (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)
def WordBuildsMono (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWordMono mask roots w ∧ WordBuildsMono mask (w :: roots) ws
def MonoLower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsMono mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
theorem gateMonoOfAvailable {mask : Nat} {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWordMono mask bank w :=
  ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩
def maskFlatF (mask word : Word) : Bool :=
  dagForceWord (word &&& mask) (fun v => v == 0 || v == mask)
theorem maskFlatF_eq (mask word : Word) : maskFlatF mask word = maskFlat mask word := by
  simp [maskFlatF, maskFlat, dagForceWordEq]
def flatCountF (mask : Word) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlatF mask word then count + 1 else count) words
theorem flatCountF_eq (mask : Word) (words : List Word) : flatCountF mask words = flatCount mask words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if maskFlatF mask w then flatCountF mask ws + 1 else flatCountF mask ws) =
      (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws)
    rw [maskFlatF_eq, ih]
def dagBoundHeaderOK (target : Word) (bound : Bound) : Bool :=
  let (mask, _, _, goal) := bound
  (target &&& mask) == goal && goal != 0 && goal != mask
abbrev DagLinkList := Nat → List (Nat × Nat × Nat)
def dagUnpackLinksGo (data width tokenBits destBits tokMask destMask : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, pos =>
      dagForceWord (unpack data width pos) (fun code =>
        dagForceWord (code &&& tokMask) (fun tk =>
          dagForceWord ((code >>> tokenBits) &&& destMask) (fun ds =>
            dagForceWord (code >>> (tokenBits + destBits)) (fun au =>
              (tk, ds, au) :: dagUnpackLinksGo data width tokenBits destBits tokMask destMask n (pos + 1)))))
def dagExtractLinks (index data indexWidth sizeBits tokenBits destBits autoBits : Nat) : DagLinkList :=
  fun parent =>
    dagForceWord (unpack index indexWidth parent) (fun entry =>
      dagForceWord (entry &&& fullMask sizeBits) (fun size =>
        dagForceWord (entry >>> sizeBits) (fun offset =>
          dagUnpackLinksGo data (tokenBits + destBits + autoBits) tokenBits destBits
            (fullMask tokenBits) (fullMask destBits) size offset)))
def dagFindLink : List (Nat × Nat × Nat) → Nat → Option DagLink
  | [], _ => none
  | (tk, ds, au) :: rest, token =>
      if Nat.beq tk token then some (ds, au) else dagFindLink rest token
def dagForceLinkList (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun e _ next k =>
      dagForceWord e.1 (fun tk =>
        dagForceWord e.2.1 (fun ds =>
          dagForceWord e.2.2 (fun au =>
            next (fun rest => k ((tk, ds, au) :: rest)))))) ls) cont
theorem dagForceLinkListEq (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) :
    dagForceLinkList ls cont = cont ls := by
  induction ls generalizing cont with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨tk, ds, au⟩ := e
    change dagForceWord tk (fun tk' => dagForceWord ds (fun ds' => dagForceWord au (fun au' =>
      dagForceLinkList es (fun rest => cont ((tk', ds', au') :: rest))))) = _
    rw [dagForceWordEq, dagForceWordEq, dagForceWordEq, ih]
def dagHighest7 (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset + shift))) 7) value 0
def dagSamplePairOK (mask goal : Word) (code : Nat) : Bool :=
  let p := code &&& 511
  let n := code >>> 9
  goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 256 && Nat.blt n 256
def dagSampleValid (mask goal : Word) (sample : DagSample) : Bool :=
  treeBlock 0 sample.2 (fun k => dagSamplePairOK mask goal (unpack sample.1 18 k))
def dagPackWords256 (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 256) ||| (tail <<< 256)) ws
def dagLaneMarks256 (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 256)) n
def dagOmitted256 (aBit bBit : Word) (left right : Bool) : Word :=
  (if left then 0 else aBit) ||| (if right then 0 else bBit)
theorem dagPackBits256 {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 256) :
    (dagPackWords256 ws).testBit (256 * i + row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 256) ||| (dagPackWords256 ws <<< 256)).testBit (256 * i + row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 256 ≤ 256 * i.succ + row := by omega
      have offset : 256 * i.succ + row - 256 = 256 * i + row := by omega
      have past : ¬ 256 * i.succ + row < 256 := by omega
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [crossed, offset, past, ih hi]
theorem dagMarkBits256 {length i : Nat} (inside : i < length) :
    (dagLaneMarks256 length).testBit (256 * i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks256 length <<< 256)).testBit (256 * i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 256 ≤ 256 * i.succ := by omega
      have offset : 256 * i.succ - 256 = 256 * i := by omega
      simp [crossed, offset, ih hi]
def dagPackedPair256 (packed marks erased out : Word) (directed : Bool) (code : Nat) : Bool :=
  dagForceWord (code &&& 511) (fun p =>
    dagForceWord (code >>> 9) (fun n =>
      let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
      gateOK &&
        dagForceWord ((packed >>> p) &&& marks) (fun up =>
          dagForceWord ((packed >>> n) &&& marks) (fun down =>
            let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
            Nat.beq (contrast &&& (marks ^^^ erased)) 0))))
theorem dagPackedPair256Sound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {code a b : Nat} {left right : Bool}
    (nd : ws.Nodup) (pairOK : dagSamplePairOK mask goal code = true)
    (checked : dagPackedPair256 (dagPackWords256 ws) (dagLaneMarks256 ws.length)
      (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right) out directed code = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) [code] = true := by
  apply List.any_eq_true.mpr
  refine ⟨code, List.mem_cons_self, ?_⟩
  simp only [dagSamplePairOK, Bool.and_eq_true, Nat.blt_eq] at pairOK
  obtain ⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩ := pairOK
  simp only [dagPackedPair256, dagForceWordEq, Bool.and_eq_true] at checked
  obtain ⟨output, closure⟩ := checked
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp, hn⟩, neg⟩, List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i, inside, eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right).testBit (256 * i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (256 * j)).testBit (256 * i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 256 * j ≠ 256 * i by omega]
    simp [dagOmitted256, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks256 ws.length
  let signal := dagPackWords256 ws
  have mark : marks.testBit (256 * i) = true := dagMarkBits256 inside
  have test {j : Nat} (within : j < 256) :
      ((signal >>> j) &&& marks).testBit (256 * i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits256 inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (256 * i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right)).testBit (256 * i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px, nx, pt, nt, Nat.testBit_and, Nat.testBit_xor, mark, omitted, p, n] at h ⊢
def dagSampleKill256 (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (directed ka kb : Bool) : Bool :=
  let dx := if ka then 0 else xC
  let dy := if kb then 0 else yC
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| outC) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then false
    else dagForceWord (dagHighest7 missing) (fun idx =>
      if Nat.blt idx sample.2 then
        dagForceWord (unpack sample.1 18 idx) (fun code =>
          dagPackedPair256 packed marks (dagOmitted256 aBit bBit ka kb) out directed code)
      else false))
def dagNodeBoundsGo (bounds : Array Bound) (dataPacked cutBits : Nat) : Nat → Nat → List Bound
  | 0, _ => []
  | n + 1, pos =>
      match bounds[unpack dataPacked cutBits pos]? with
      | none => dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
      | some b => b :: dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
theorem dagNodeBoundsGo_mem {bounds : Array Bound} {dataPacked cutBits : Nat} :
    ∀ cnt off b, b ∈ dagNodeBoundsGo bounds dataPacked cutBits cnt off → b ∈ bounds.toList := by
  intro cnt
  induction cnt with
  | zero => intro _ _ h; cases h
  | succ n ih =>
    intro off b h
    unfold dagNodeBoundsGo at h
    split at h
    · exact ih _ _ h
    next x hx =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
      · exact ih _ _ h
def dagNodeBounds (bounds : Array Bound) (idxPacked dataPacked indexWidth sizeBits cutBits i : Nat) : List Bound :=
  let entry := unpack idxPacked indexWidth i
  dagNodeBoundsGo bounds dataPacked cutBits (entry &&& fullMask sizeBits) (entry >>> sizeBits)
theorem dagNodeBounds_mem {bounds : Array Bound} {idxPacked dataPacked indexWidth sizeBits cutBits i : Nat} :
    ∀ b ∈ dagNodeBounds bounds idxPacked dataPacked indexWidth sizeBits cutBits i, b ∈ bounds.toList :=
  fun b h => dagNodeBoundsGo_mem _ _ b h
def normWord (mask w : Word) : Word :=
  if w < mask ^^^ w then w else mask ^^^ w
theorem xor_cancel_left (mask w : Word) : mask ^^^ (mask ^^^ w) = w := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
theorem normWord_symm (mask w : Word) : normWord mask (mask ^^^ w) = normWord mask w := by
  unfold normWord
  rw [xor_cancel_left]
  by_cases h : w < mask ^^^ w
  · have h' : ¬(mask ^^^ w < w) := Nat.lt_asymm h
    simp [h, h']
  · by_cases h' : mask ^^^ w < w
    · simp [h, h']
    · have eq : w = mask ^^^ w := Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h)
      rw [if_neg h', if_neg h]; exact eq
theorem normWord_eq_or (mask w : Word) : normWord mask w = w ∨ normWord mask w = mask ^^^ w := by
  unfold normWord; split <;> simp
theorem normWord_idem (mask w : Word) : normWord mask (normWord mask w) = normWord mask w := by
  rcases normWord_eq_or mask w with h | h
  · rw [h, h]
  · rw [h, normWord_symm, h]
theorem normWord_zero (mask : Word) : normWord mask 0 = 0 := by
  unfold normWord
  rw [Nat.xor_zero]
  by_cases h : 0 < mask
  · rw [if_pos h]
  · have hm : mask = 0 := Nat.eq_zero_of_not_pos h
    rw [hm]; rfl
theorem normWord_mask (mask : Word) : normWord mask mask = 0 := by
  have h : normWord mask (mask ^^^ 0) = normWord mask 0 := normWord_symm mask 0
  rwa [Nat.xor_zero, normWord_zero] at h
theorem masked_xor {mask w : Word} (hw : Masked mask w) : Masked mask (mask ^^^ w) := by
  apply Nat.eq_of_testBit_eq; intro i
  have bit := congrArg (fun n : Nat => n.testBit i) hw
  simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
  cases hm : mask.testBit i <;> simp_all
theorem masked_norm {mask w : Word} (hw : Masked mask w) : Masked mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; exact masked_xor hw
theorem proper_xor {mask w : Word} (hp : properWord mask w) : properWord mask (mask ^^^ w) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_self] at this
    exact hp.1 this
theorem proper_norm {mask w : Word} (hp : properWord mask w) : properWord mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hp
  · rw [h]; exact proper_xor hp
theorem demorgan_and {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
theorem demorgan_or {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a ||| b) = (mask ^^^ a) &&& (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
theorem masked_and_self_xor {mask a : Word} (ma : Masked mask a) : a &&& (mask ^^^ a) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem masked_or_self_xor {mask a : Word} (ma : Masked mask a) : a ||| (mask ^^^ a) = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem masked_or_mask {mask a : Word} (ma : Masked mask a) : a ||| mask = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all
def AvBin (mask : Word) (bank : List Word) (w : Word) : Prop :=
  w = 0 ∨ w = mask ∨ w ∈ bank ∨ (mask ^^^ w) ∈ bank
theorem avBin_not {mask : Word} {bank : List Word} {w : Word}
    (h : AvBin mask bank w) : AvBin mask bank (mask ^^^ w) := by
  rcases h with rfl | hmask | hm | hm
  · exact Or.inr (Or.inl (Nat.xor_zero mask))
  · rw [hmask]; exact Or.inl (Nat.xor_self mask)
  · exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  · exact Or.inr (Or.inr (Or.inl hm))
theorem avBin_weaken {mask : Word} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (av : AvBin mask small w) : AvBin mask big w := by
  rcases av with rfl | rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
  · simpa [xor_cancel_left] using avBin_not (sub (mask ^^^ w) h)
theorem avBin_of_av {mask : Word} {bank : List Word} {w : Word}
    (h : AvailableWord mask bank w) : AvBin mask bank w := by
  rcases h with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl hm))
theorem masked_avBin {mask : Word} {bank : List Word} {w : Word}
    (all : ∀ x ∈ bank, Masked mask x) (av : AvBin mask bank w) : Masked mask w := by
  rcases av with rfl | rfl | hm | hm
  · simp [Masked]
  · simp [Masked]
  · exact all _ hm
  · simpa [xor_cancel_left] using masked_xor (all _ hm)
def GateBin (mask : Word) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvBin mask bank a ∧ AvBin mask bank b ∧ (out = a &&& b ∨ out = a ||| b)
theorem gateBin_weaken {mask : Word} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (g : GateBin mask small out) : GateBin mask big out := by
  rcases g with ⟨a, b, ha, hb, eq⟩
  exact ⟨a, b, avBin_weaken sub ha, avBin_weaken sub hb, eq⟩
theorem masked_gateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ x ∈ bank, Masked mask x) (g : GateBin mask bank out) : Masked mask out := by
  rcases g with ⟨a, b, ha, hb, rfl | rfl⟩
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    simp only [Masked] at ma mb ⊢; rw [Nat.land_assoc, mb]
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    apply Nat.eq_of_testBit_eq; intro i
    have ba := congrArg (fun n : Nat => n.testBit i) ma
    have bb := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at ba bb ⊢
    cases hm : mask.testBit i <;> simp_all
def WordBuildsBin (mask : Word) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateBin mask roots w ∧ WordBuildsBin mask (w :: roots) ws
def BinLower (mask : Word) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsBin mask roots values →
    AvBin mask (values ++ roots) target → minimum ≤ values.length
theorem buildsBin_weaken {mask : Word} {small big values : List Word}
    (supply : ∀ w ∈ small, AvBin mask big w) (build : WordBuildsBin mask small values) :
    WordBuildsBin mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_weaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
    · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)
theorem buildsBin_append {mask : Word} {roots first second : List Word}
    (left : WordBuildsBin mask roots first)
    (right : WordBuildsBin mask (first ++ roots) second) :
    WordBuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    exact buildsBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) right
def binOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  if op == 0 then a &&& b
  else if op == 1 then a ||| b
  else if op == 2 then a &&& (mask ^^^ b)
  else (mask ^^^ a) &&& b
def normBinOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  normWord mask (binOp4 mask op a b)
def swapOp4 (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op
theorem swapOp4_lt {op : Nat} (h : op < 4) : swapOp4 op < 4 := by
  unfold swapOp4
  split
  · decide
  · split
    · decide
    · exact h
theorem binOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask (swapOp4 op) b a = binOp4 mask op a b := by
  have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp [binOp4, swapOp4, Nat.land_comm, Nat.lor_comm]
theorem normBinOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    normBinOp4 mask (swapOp4 op) b a = normBinOp4 mask op a b := by
  unfold normBinOp4; rw [binOp4_swap mask hop]
theorem gateBin_normBinOp4 {mask : Word} {bank : List Word} {op : Nat} {a b : Word}
    (hop : op < 4) (ma : Masked mask a) (mb : Masked mask b)
    (ha : AvBin mask bank a) (hb : AvBin mask bank b) :
    GateBin mask bank (normBinOp4 mask op a b) := by
  have hna := avBin_not ha
  have hnb := avBin_not hb
  have mna := masked_xor ma
  have mnb := masked_xor mb
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  unfold normBinOp4
  rcases normWord_eq_or mask (binOp4 mask op a b) with heq | heq
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨a, b, ha, hb, Or.inl rfl⟩
    · exact ⟨a, b, ha, hb, Or.inr rfl⟩
    · exact ⟨a, mask ^^^ b, ha, hnb, Or.inl rfl⟩
    · exact ⟨mask ^^^ a, b, hna, hb, Or.inl rfl⟩
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inr (demorgan_and ma mb)⟩
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inl (demorgan_or ma mb)⟩
    · refine ⟨mask ^^^ a, b, hna, hb, Or.inr ?_⟩
      change mask ^^^ (a &&& (mask ^^^ b)) = (mask ^^^ a) ||| b
      rw [demorgan_and ma mnb, xor_cancel_left]
    · refine ⟨a, mask ^^^ b, ha, hnb, Or.inr ?_⟩
      change mask ^^^ ((mask ^^^ a) &&& b) = a ||| (mask ^^^ b)
      rw [demorgan_and mna mb, xor_cancel_left]
def LiveBin (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {normWord mask target} ∧ properWord mask target
  | k + 1, S =>
    ∃ (U : Finset Word) (a b : Word) (op : Nat),
      op < 4 ∧ S = insert a (insert b U) ∧
      properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      normWord mask a = a ∧ normWord mask b = b ∧
      normBinOp4 mask op a b ∉ insert a (insert b U) ∧
      LiveBin mask target k (insert (normBinOp4 mask op a b) U)
theorem LiveBin.stop {mask target : Word} (hp : properWord mask target) :
    LiveBin mask target 0 {normWord mask target} := ⟨rfl, hp⟩
theorem LiveBin.step {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
    (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (na : normWord mask a = a) (nb : normWord mask b = b)
    (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)) :
    LiveBin mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hfresh, tail⟩
theorem LiveBin.ind {mask target : Word}
    {motive : ∀ (k : Nat) (S : Finset Word), LiveBin mask target k S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 {normWord mask target} (LiveBin.stop hp))
    (step : ∀ {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
      (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (na : normWord mask a = a) (nb : normWord mask b = b)
      (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
      (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)),
      motive k (insert (normBinOp4 mask op a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBin.step hop ha hb hab na nb hfresh tail))
    {k : Nat} {S : Finset Word} (h : LiveBin mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hf, tail⟩ := h
    exact step hop ha hb hab na nb hf tail (ih tail)
theorem liveBinProps {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : ∀ a ∈ S, properWord mask a ∧ normWord mask a = a := by
  induction h using LiveBin.ind with
  | stop hp =>
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact ⟨proper_norm hp, normWord_idem mask target⟩
  | step hop ha hb hab na nb hf tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha, na⟩, ⟨hb, nb⟩, fun w hw => ih w (Finset.mem_insert_of_mem hw)⟩
theorem liveBinSize {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : S.card ≤ k + 1 := by
  induction h using LiveBin.ind with
  | stop => simp
  | @step k U a b op hop ha hb hab na nb hf tail ih =>
    have hu : normBinOp4 mask op a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
def binWitness (mask : Word) (nws : List Word) (w : Word) : Prop :=
  ∃ op a b, op < 4 ∧ a ∈ nws ∧ b ∈ nws ∧ properWord mask a ∧ properWord mask b ∧
    normWord mask a = a ∧ normWord mask b = b ∧ a ≠ b ∧ w = normBinOp4 mask op a b
theorem classifyGateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateBin mask bank out) :
    wordRep mask (bank.map (normWord mask)) (normWord mask out) ∨
    binWitness mask (bank.map (normWord mask)) (normWord mask out) := by
  let nbank := bank.map (normWord mask)
  have c0 : wordRep mask nbank 0 := Or.inr fun h => h.1 rfl
  have cnorm (x : Word) (hx : AvBin mask bank x) :
      x = 0 ∨ x = mask ∨ (normWord mask x ∈ nbank ∧ properWord mask (normWord mask x)) := by
    by_cases hz : x = 0
    · exact Or.inl hz
    by_cases hm : x = mask
    · exact Or.inr (Or.inl hm)
    have hp : properWord mask x := ⟨hz, hm⟩
    refine Or.inr (Or.inr ⟨?_, proper_norm hp⟩)
    rcases (hx.resolve_left hz).resolve_left hm with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  rcases g with ⟨a, b, ha, hb, eq⟩
  have ma := masked_avBin all ha
  have mb := masked_avBin all hb
  have trivial_word (w : Word) (hw : AvBin mask bank w) : wordRep mask nbank (normWord mask w) := by
    rcases cnorm w hw with rfl | rfl | ⟨hm, _⟩
    · rw [normWord_zero]; exact c0
    · rw [normWord_mask]; exact c0
    · exact Or.inl hm
  rcases cnorm a ha with rfl | rfl | ⟨hma, pa⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.zero_and, normWord_zero]; exact Or.inl c0
    · simp only [Nat.zero_or]; exact Or.inl (trivial_word b hb)
  · rcases eq with rfl | rfl
    · rw [Nat.land_comm, mb]; exact Or.inl (trivial_word b hb)
    · rw [Nat.lor_comm, masked_or_mask mb, normWord_mask]; exact Or.inl c0
  rcases cnorm b hb with rfl | rfl | ⟨hmb, pb⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.and_zero, normWord_zero]; exact Or.inl c0
    · simp only [Nat.or_zero]; exact Or.inl (trivial_word a ha)
  · rcases eq with rfl | rfl
    · rw [ma]; exact Or.inl (trivial_word a ha)
    · rw [masked_or_mask ma, normWord_mask]; exact Or.inl c0
  let na := normWord mask a
  let nb := normWord mask b
  have mna : Masked mask na := masked_norm ma
  have mnb : Masked mask nb := masked_norm mb
  by_cases same : na = nb
  · have hrel : b = a ∨ b = mask ^^^ a := by
      rcases normWord_eq_or mask a with ea | ea <;> rcases normWord_eq_or mask b with eb | eb
      · left; exact eb.symm.trans (same.symm.trans ea)
      · right
        have h1 : a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left] at this; exact this.symm
      · right; exact eb.symm.trans (same.symm.trans ea)
      · left
        have h1 : mask ^^^ a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left, xor_cancel_left] at this; exact this.symm
    rcases hrel with rfl | rfl <;> rcases eq with rfl | rfl
    · rw [Nat.and_self]; exact Or.inl (Or.inl hma)
    · rw [Nat.or_self]; exact Or.inl (Or.inl hma)
    · rw [masked_and_self_xor ma, normWord_zero]; exact Or.inl c0
    · rw [masked_or_self_xor ma, normWord_mask]; exact Or.inl c0
  have ea : a = na ∨ a = mask ^^^ na := by
    rcases normWord_eq_or mask a with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have eb : b = nb ∨ b = mask ^^^ nb := by
    rcases normWord_eq_or mask b with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have mkWit (op : Nat) (hop : op < 4) (heq : normWord mask out = normBinOp4 mask op na nb) :
      binWitness mask nbank (normWord mask out) :=
    ⟨op, na, nb, hop, hma, hmb, pa, pb, normWord_idem mask a, normWord_idem mask b, same, heq⟩
  right
  rcases eq with hout | hout <;> rcases ea with hea | hea <;> rcases eb with heb | heb
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 2 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb, ← demorgan_or mna mnb, normWord_symm]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by
      have h1 : mask ^^^ ((mask ^^^ na) &&& nb) = na ||| (mask ^^^ nb) := by
        rw [demorgan_and (masked_xor mna) mnb, xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 2 (by decide) (by
      have h1 : mask ^^^ (na &&& (mask ^^^ nb)) = (mask ^^^ na) ||| nb := by
        rw [demorgan_and mna (masked_xor mnb), xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb, ← demorgan_and mna mnb, normWord_symm]; rfl)
theorem pullBin {mask target : Word} {nws : List Word} {z : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S)
    (hz : wordRep mask nws z ∨ binWitness mask nws z) (sub : ∀ a ∈ S, a ∈ nws ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ LiveBin mask target k' S' ∧ ∀ a ∈ S', a ∈ nws := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ nws
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ nws ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := (liveBinProps h z hm).1
      rcases hz with hr | ⟨op, a, b, hop, ha, hb, pa, pb, na, nb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (normBinOp4 mask op a b)
        have ht : LiveBin mask target k (insert (normBinOp4 mask op a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ nws := by
          intro v hv
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hmem
        have hf : normBinOp4 mask op a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k + 1, insert a (insert b U), Nat.le_refl _,
          LiveBin.step hop pa pb hab na nb hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractBinLive {mask target : Word} {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuildsBin mask roots values)
    (hit : AvBin mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveBin mask target k S ∧ ∀ w ∈ S, w ∈ roots.map (normWord mask) := by
  have hm : normWord mask target ∈ (values ++ roots).map (normWord mask) := by
    rcases (hit.resolve_left p.1).resolve_left p.2 with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {normWord mask target}, Nat.zero_le _, LiveBin.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact masked_gateBin all builds.1
      · exact all _ hv
    have ht : AvBin mask (ws ++ w :: roots) target := by
      rcases hit with rfl | rfl | hmem | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
    have hm' : normWord mask target ∈ (ws ++ w :: roots).map (normWord mask) := by
      rcases (ht.resolve_left p.1).resolve_left p.2 with hmem | hmem
      · exact List.mem_map_of_mem hmem
      · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
    obtain ⟨k, S, hk, live, sub⟩ := ih next builds.2 ht hm'
    have available : ∀ v ∈ S, v ∈ roots.map (normWord mask) ++ [normWord mask w] := by
      intro v h
      simpa [List.map_cons, or_comm] using sub v h
    obtain ⟨k', S', hk', hl, hsub⟩ := pullBin live (classifyGateBin all builds.1) available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem agreesNorm {i j mask w : Word} (m : AgreesAt i j mask) (hw : AgreesAt i j w) :
    AgreesAt i j (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; simp only [AgreesAt, Nat.testBit_xor] at m hw ⊢; rw [m, hw]
theorem liveBinAgrees {mask target : Word} {i j k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveBin.ind with
  | stop =>
    have hn := all _ (Finset.mem_singleton_self _)
    rcases normWord_eq_or mask target with h | h
    · rwa [h] at hn
    · rw [h] at hn
      change mask.testBit i = mask.testBit j at m
      change (mask ^^^ target).testBit i = (mask ^^^ target).testBit j at hn
      rw [Nat.testBit_xor, Nat.testBit_xor, m] at hn
      change target.testBit i = target.testBit j
      cases hmj : mask.testBit j <;> cases hti : target.testBit i <;> cases htj : target.testBit j <;> simp_all
  | @step k U a b op hop pa pb hab na nb hf tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · unfold normBinOp4
      apply agreesNorm m
      have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have mm : mask.testBit i = mask.testBit j := m
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl <;>
        simp [binOp4, AgreesAt, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, aa, bb, mm]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
theorem dagPartitionLiveBin {mask goal : Word} {ws : List Word} {k : Nat}
    (goalMask : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPartition false ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition false ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition false ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  have same := liveBinAgrees live (pm.trans nm.1.symm) (fun w hw => by
    simpa [AgreesAt] using agree w (List.mem_toFinset.mp hw))
  simp [AgreesAt, hp, nm.2] at same
theorem dagPairsOpenBin {mask goal : Word} {ws : List Word} {pairs : List Nat} {k : Nat}
    (masked : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPairReject mask goal false ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code, _, check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  have h := liveBinAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
    have pair := bank _ (List.mem_toFinset.mp hw)
    simpa [AgreesAt] using pair)
  simp [AgreesAt, hp, neg] at h
theorem essentialRequiredBin {mask target : Word} {stock : List Word} {entry : Witness}
    {S : Finset Word} {k : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    normWord mask (witnessWord entry) ∈ S := by
  obtain ⟨w, p, n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp, mn⟩, tp⟩, tn⟩, unequal⟩, rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
    have horig : orig ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    have h := List.all_eq_true.mp rest orig omem
    have hag : AgreesAt p n orig := by simpa [horig, AgreesAt] using h
    exact agreesNorm (mp.trans mn.symm) hag
  have agree := liveBinAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree
theorem essentialWordsInBin {mask target : Word} {stock : List Word} {witnesses : List Witness}
    {S : Finset Word} {k : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequiredBin (List.all_eq_true.mp ok entry mem) sub live
theorem essentialLowerBin {mask target : Word} {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset.card - 1) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsInBin ok sub live)
  have size := liveBinSize live
  omega
def buildableBin (m g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s ∨ (m ^^^ g) ∈ s
  | n + 1, s => buildableBin m g n s ∨
      ∃ a b, (a ∈ s ∨ m ^^^ a ∈ s) ∧ (b ∈ s ∨ m ^^^ b ∈ s) ∧
        ∃ d : Bool, buildableBin m g n (insert (binWord d a b) s)
theorem supplyPoolBin {m g : Word} {n : Nat} {s q : Finset Word}
    (sub : ∀ w ∈ s, w ∈ q ∨ m ^^^ w ∈ q) (h : buildableBin m g n s) : buildableBin m g n q := by
  induction n generalizing s q with
  | zero =>
    rcases h with h1 | h1
    · exact sub g h1
    · rcases sub (m ^^^ g) h1 with h2 | h2
      · exact Or.inr h2
      · rw [xor_cancel_left] at h2; exact Or.inl h2
  | succ n ih =>
    have subPair {x : Word} (hx : x ∈ s ∨ m ^^^ x ∈ s) : x ∈ q ∨ m ^^^ x ∈ q := by
      rcases hx with h1 | h1
      · exact sub x h1
      · rcases sub (m ^^^ x) h1 with h2 | h2
        · exact Or.inr h2
        · rw [xor_cancel_left] at h2; exact Or.inl h2
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · exact Or.inl (ih sub h)
    · refine Or.inr ⟨a, b, subPair ha, subPair hb, d, ih ?_ h⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inl (Finset.mem_insert_self _ _)
      · rcases sub w hw with hq | hq
        · exact Or.inl (Finset.mem_insert_of_mem hq)
        · exact Or.inr (Finset.mem_insert_of_mem hq)
theorem buildableBinWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildableBin mask goal n pool) (supply : ∀ w ∈ pool, AvBin mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuildsBin mask bank values ∧
      AvBin mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero =>
    refine ⟨[], Nat.le_refl _, trivial, ?_⟩
    rcases h with h1 | h1
    · exact supply goal h1
    · simpa [xor_cancel_left] using avBin_not (supply _ h1)
  | succ n ih =>
    have supPair {w : Word} (hw : w ∈ pool ∨ mask ^^^ w ∈ pool) : AvBin mask bank w := by
      rcases hw with h1 | h1
      · exact supply w h1
      · simpa [xor_cancel_left] using avBin_not (supply _ h1)
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · let w := binWord d a b
      have g : GateBin mask bank w :=
        ⟨a, b, supPair ha, supPair hb, by cases d <;> simp [w, binWord]⟩
      have growing : ∀ v ∈ insert w pool, AvBin mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun _ hh => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hh)))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih h growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
        simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)))) hit
theorem cofBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask op a b &&& m = binOp4 m op (a &&& m) (b &&& m) := by
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact cofBinary m a b false
  · exact cofBinary m a b true
  · change (a &&& (mask ^^^ b)) &&& m = (a &&& m) &&& (m ^^^ (b &&& m))
    rw [← cofNot sub b]; exact cofBinary m a (mask ^^^ b) false
  · change ((mask ^^^ a) &&& b) &&& m = (m ^^^ (a &&& m)) &&& (b &&& m)
    rw [← cofNot sub a]; exact cofBinary m (mask ^^^ a) b false
theorem flNorm {mask m : Word} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (normWord mask a) ↔ maskedFlat m a := by
  rcases normWord_eq_or mask a with h | h
  · rw [h]
  · rw [h]; exact flNot sub a
theorem flBothOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (ha : maskedFlat m a) (hb : maskedFlat m b) : maskedFlat m (normBinOp4 mask op a b) := by
  rw [normBinOp4, flNorm sub]
  unfold maskedFlat at *
  rw [cofBinOp4 sub hop]
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [binOp4, ha, hb]
theorem simpleBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (h : maskedFlat m a ∨ maskedFlat m b) :
    binOp4 mask op a b &&& m = 0 ∨ binOp4 mask op a b &&& m = m ∨
    binOp4 mask op a b &&& m = a &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (a &&& m) ∨
    binOp4 mask op a b &&& m = b &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (b &&& m) := by
  rw [cofBinOp4 sub hop]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]; simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by rw [Nat.lor_comm]; exact masked_or_mask (restrictWord m x)
  have top3 (x : Word) : (m ^^^ (x &&& m)) &&& m = m ^^^ (x &&& m) :=
    masked_xor (restrictWord m x)
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  have right3 (x : Word) : m &&& (m ^^^ (x &&& m)) = m ^^^ (x &&& m) := by
    rw [Nat.land_comm]; exact top3 x
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;> rcases h with (ha | ha) | (hb | hb) <;>
    simp [binOp4, *, top1, top2, top3, right1, right2, right3]
theorem maskedBuildBin {mask goal : Word} {k : Nat} {s : Finset Word}
    (run : LiveBin mask goal k s) (m : Word) (submask : mask &&& m = m)
    (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n + (flatSet m s).card ≤ k ∧ buildableBin m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveBin.ind with
  | stop =>
    refine ⟨0, ?_, ?_⟩
    · have pgn : ¬ maskedFlat m (normWord mask goal) := by rwa [flNorm submask]
      simp only [flatSet, Finset.filter_singleton, pgn, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · rcases normWord_eq_or mask goal with h | h
      · left; simp [projectedStock, visibleWords, h]
      · right; rw [← cofNot submask goal, ← h]; simp [projectedStock, visibleWords]
  | @step k u a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    obtain ⟨n, cap, built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n + (flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    have hv_rel : v &&& m = binOp4 mask op a b &&& m ∨
        v &&& m = m ^^^ (binOp4 mask op a b &&& m) := by
      rcases normWord_eq_or mask (binOp4 mask op a b) with h | h
      · left; simp [v, normBinOp4, h]
      · right; simp [v, normBinOp4, h, cofNot submask]
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k + 1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa, fb, ite_true, ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBothOp4 submask hop fa fb; simp only [vf, ite_true] at cap; omega | omega | tauto
      refine ⟨n, budget, supplyPoolBin ?_ built⟩
      intro w hw
      simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl | rfl | h
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · have sc := simpleBinOp4 submask hop simple
        rcases hv_rel with e | e <;> rw [e]
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inr (Or.inl (Nat.xor_zero m)))
          · exact Or.inl (Or.inl (Nat.xor_self m))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa, fb, ite_false] at ca cb
      have ha_in : a &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hb_in : b &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hna_in : m ^^^ (m ^^^ (a &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have hnb_in : m ^^^ (m ^^^ (b &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have mkStep {a' b' : Word} {d : Bool}
          (ha' : a' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ a' ∈ projectedStock m (insert a (insert b u)))
          (hb' : b' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ b' ∈ projectedStock m (insert a (insert b u)))
          (heq : binOp4 mask op a b &&& m = binWord d a' b') :
          ∃ n', n' + (flatSet m (insert a (insert b u))).card ≤ k + 1 ∧
            buildableBin m (goal &&& m) n' (projectedStock m (insert a (insert b u))) := by
        refine ⟨n + 1, by omega, Or.inr ⟨a', b', ha', hb', d, supplyPoolBin ?_ built⟩⟩
        intro w hw
        simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
        rcases hw with rfl | rfl | rfl | h
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hv_rel with e | e
          · exact Or.inl (Or.inl (e.trans heq))
          · exact Or.inr (by rw [e, xor_cancel_left]; exact Or.inl heq)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 0) submask (by decide) a b)
      · exact mkStep (d := true) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 1) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inr hnb_in) (cofBinOp4 (op := 2) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inr hna_in) (Or.inl hb_in) (cofBinOp4 (op := 3) submask (by decide) a b)
theorem essentialLiftBin {mask target : Word} {stock cutStock : List Word} {witnesses : List Witness}
    {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvBin cut cutStock (w &&& cut))
    (known : BinLower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset).card) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have subW := essentialWordsInBin ok sub live
  have subFlat : flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuildBin live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvBin cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
      rcases normWord_eq_or mask orig with e | e
      · rw [e]; exact supplies _ omem
      · rw [e, cofNot submask]; exact avBin_not (supplies _ omem)
  obtain ⟨ys, len, built', out⟩ := buildableBinWords built starts
  have lower := known ys built' out
  omega
def normWordFast (mask w : Word) : Word :=
  dagForceWord (mask ^^^ w) (fun c => if Nat.blt w c then w else c)
theorem normWordFast_eq (mask w : Word) : normWordFast mask w = normWord mask w := by
  simp [normWordFast, normWord, dagForceWordEq, Nat.blt_eq]
def normBinOp4Fast (mask op x y : Word) : Word :=
  normWordFast mask (binOp4 mask op x y)
theorem normBinOp4Fast_eq (mask op x y : Word) : normBinOp4Fast mask op x y = normBinOp4 mask op x y :=
  normWordFast_eq mask (binOp4 mask op x y)
def availableNormB (bank : List Word) (v : Word) : Bool :=
  v == 0 || bank.contains v
theorem availableNormB_spec {mask : Word} {orig bank : List Word} {w : Word}
    (mw : Masked mask w) (hbank : ∀ x ∈ bank, AvBin mask orig x)
    (h : availableNormB bank (normWord mask w) = true) : AvBin mask orig w := by
  simp only [availableNormB, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with hz | hm
  · rcases normWord_eq_or mask w with e | e
    · exact Or.inl (e.symm.trans hz)
    · have : mask ^^^ w = 0 := e.symm.trans hz
      have h1 : w = mask := by
        have h2 := congrArg (fun z => mask ^^^ z) this
        rw [xor_cancel_left, Nat.xor_zero] at h2
        exact h2
      exact Or.inr (Or.inl h1)
  · have hav := hbank _ hm
    rcases normWord_eq_or mask w with e | e
    · rwa [e] at hav
    · rw [e] at hav
      have := avBin_not hav
      rwa [xor_cancel_left] at this
def stockWordBinF (mask : Word) (nstock needed : List Word) (word : Word) : List Word :=
  dagForceWord (normWordFast mask (word &&& mask)) (fun v =>
    if availableNormB nstock v || needed.contains v then needed else v :: needed)
def recipeStartBinF (mask : Word) (nstock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBinF mask nstock seen word)) words) []
def recipeClosureBinF (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (dagForceWord (normWordFast mask (out &&& mask)) (fun vo =>
        if seen.contains vo then
          stockWordBinF mask nstock (stockWordBinF mask nstock seen a) b else seen)))
    history start
def recipeGateBinNorm (mask : Word) (nbank : List Word) (v ma mb : Word) : Bool :=
  availableNormB nbank (normWordFast mask ma) && availableNormB nbank (normWordFast mask mb) &&
    (v == normWordFast mask (ma &&& mb) || v == normWordFast mask (ma ||| mb) ||
     v == normWordFast mask (ma &&& (mask ^^^ mb)) || v == normWordFast mask ((mask ^^^ ma) &&& mb))
theorem recipeGateBinNorm_spec {mask : Word} {orig nbank : List Word} {v ma mb : Word}
    (hma : Masked mask ma) (hmb : Masked mask mb)
    (hbank : ∀ x ∈ nbank, AvBin mask orig x)
    (h : recipeGateBinNorm mask nbank v ma mb = true) : GateBin mask orig v := by
  simp only [recipeGateBinNorm, normWordFast_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  have havA := availableNormB_spec hma hbank ha
  have havB := availableNormB_spec hmb hbank hb
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 1) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 2) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 3) (by decide) hma hmb havA havB
def replayRecipesBinF (mask : Word) (needed : List Word) : List (Word × Word × Word) → List Word → List Word
  | [], _ => []
  | (w, a, b) :: rs, nbank =>
      dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
        if needed.contains v && !availableNormB nbank v then
          dagForceWord (a &&& mask) (fun ma =>
            dagForceWord (b &&& mask) (fun mb =>
              if recipeGateBinNorm mask nbank v ma mb then
                v :: replayRecipesBinF mask needed rs (v :: nbank)
              else replayRecipesBinF mask needed rs nbank))
        else replayRecipesBinF mask needed rs nbank)
theorem replayRecipesBinFBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (orig nbank : List Word) (hbank : ∀ x ∈ nbank, AvBin mask orig x) :
    WordBuildsBin mask orig (replayRecipesBinF mask needed recipes nbank) ∧
      ∀ x ∈ replayRecipesBinF mask needed recipes nbank, x ∈ replayRecipesBinF mask needed recipes nbank := by
  refine ⟨?_, fun _ h => h⟩
  induction recipes generalizing orig nbank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask orig (dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
      if needed.contains v && !availableNormB nbank v then
        dagForceWord (a &&& mask) (fun ma =>
          dagForceWord (b &&& mask) (fun mb =>
            if recipeGateBinNorm mask nbank v ma mb then
              v :: replayRecipesBinF mask needed recipes (v :: nbank)
            else replayRecipesBinF mask needed recipes nbank))
      else replayRecipesBinF mask needed recipes nbank))
    simp only [dagForceWordEq, normWordFast_eq]
    split
    · split
      · rename_i h1 h2
        refine ⟨recipeGateBinNorm_spec (restrictWord mask a) (restrictWord mask b) hbank h2, ?_⟩
        apply ih (normWord mask (w &&& mask) :: orig) (normWord mask (w &&& mask) :: nbank)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hy)))) (hbank x hx)
      · exact ih orig nbank hbank
    · exact ih orig nbank hbank
def dagBoundClosesBinNoHdr (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, _) := bound
  let (fuel, ws, history) := state
  dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
    if Nat.blt remaining lower then
      dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
        if Nat.blt (start.length + remaining) lower then
          dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
            if Nat.blt (needed.length + remaining) lower then
              dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                Nat.blt (replay.length + remaining) lower &&
                  ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                    availableNormB (replay ++ nstock) v)))
            else false)
        else false)
    else false)
def dagKnownClosesBinNoHdr (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBinNoHdr state bound || later) bounds
def dagFilterForceBoundsBin (target : Word) (bounds : List Bound) (cont : List Bound → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Bound → Bool) → Bool) (fun k => k [])
    (fun b _ next k =>
      dagForceWord b.1 (fun m' =>
        dagForceWord b.2.2.2 (fun g' =>
          if (target &&& m') == g' && g' != 0 && g' != m' then
            dagForceWords (b.2.1.map (fun w => normWordFast m' w)) (fun nst' =>
              next (fun rest => k ((m', nst', b.2.2.1, g') :: rest)))
          else next k))) bounds) cont
theorem dagFilterForceBoundsBinEq (target : Word) (bounds : List Bound) (cont : List Bound → Bool) :
    dagFilterForceBoundsBin target bounds cont =
      cont ((bounds.filter (dagBoundHeaderOK target)).map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) := by
  induction bounds generalizing cont with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨m, st, lo, g⟩ := b
    change dagForceWord m (fun m' => dagForceWord g (fun g' =>
      if (target &&& m') == g' && g' != 0 && g' != m' then
        dagForceWords (st.map (fun w => normWordFast m' w)) (fun nst' =>
          dagFilterForceBoundsBin target bs (fun rest => cont ((m', nst', lo, g') :: rest)))
      else dagFilterForceBoundsBin target bs cont)) = _
    simp only [dagForceWordEq, dagForceWordsEq, List.filter_cons, dagBoundHeaderOK]
    have hm : st.map (fun w => normWordFast m w) = st.map (normWord m) := by
      congr 1; funext w; exact normWordFast_eq m w
    by_cases hc : ((target &&& m) == g && g != 0 && g != m) = true
    · simp only [hc, ite_true, hm, List.map_cons]; exact ih _
    · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, ite_false]; exact ih _
def dagBoundClosesBinFast (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                  Nat.blt (replay.length + remaining) lower &&
                    ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                      availableNormB (replay ++ nstock) v)))
              else false)
          else false)
      else false)
def availableBinB (mask : Word) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w || bank.contains (mask ^^^ w)
theorem availableBinB_spec {mask : Word} {bank : List Word} {v : Word} :
    availableBinB mask bank v = true ↔ AvBin mask bank v := by
  simp [availableBinB, AvBin, or_assoc]
def stockWordBin (mask : Word) (stock needed : List Word) (word : Word) : List Word :=
  let v := normWord mask (word &&& mask)
  if availableBinB mask stock v || needed.contains v then needed else v :: needed
def recipeStartBin (mask : Word) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBin mask stock seen word)) words) []
def recipeClosureBin (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (normWord mask (out &&& mask)) then
        stockWordBin mask stock (stockWordBin mask stock seen a) b else seen))
    history start
def recipeGateBin (mask : Word) (bank : List Word) (w a b : Word) : Bool :=
  availableBinB mask bank a && availableBinB mask bank b &&
    (w == normWord mask (a &&& b) || w == normWord mask (a ||| b) ||
     w == normWord mask (a &&& (mask ^^^ b)) || w == normWord mask ((mask ^^^ a) &&& b))
theorem recipeGateBin_spec {mask : Word} {bank : List Word} {v a b : Word}
    (ma : Masked mask a) (mb : Masked mask b)
    (h : recipeGateBin mask bank v a b = true) : GateBin mask bank v := by
  simp only [recipeGateBin, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableBinB_spec] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 1) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 2) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 3) (by decide) ma mb ha hb
def replayRecipesBin (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := normWord mask (w &&& mask)
      if needed.contains v && !availableBinB mask bank v &&
          recipeGateBin mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank
theorem replayRecipesBinBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuildsBin mask bank (replayRecipesBin mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask bank
      (if needed.contains (normWord mask (w &&& mask)) && !availableBinB mask bank (normWord mask (w &&& mask)) &&
          recipeGateBin mask bank (normWord mask (w &&& mask)) (a &&& mask) (b &&& mask) then
        normWord mask (w &&& mask) :: replayRecipesBin mask needed recipes (normWord mask (w &&& mask) :: bank)
      else replayRecipesBin mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGateBin_spec (restrictWord mask a) (restrictWord mask b) (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _
def dagBoundClosesBin (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBin mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBin mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBin mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableBinB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)
def dagKnownClosesBin (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBin target state bound || later) bounds
def KnownBin (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1
theorem extendKnownBin {bound : Bound} {bounds : List Bound}
    (old : KnownBin bounds)
    (new : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    KnownBin (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h
def BinViable (mask target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k, k ≤ state.1 ∧ LiveBin mask target k state.2.1.toFinset
theorem boundClosesBinSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBin target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let needed := recipeClosureBin cut stock history (recipeStartBin cut stock ws)
  let replay := replayRecipesBin cut needed history.reverse stock
  simp only [dagBoundClosesBin, dagForceWordEq, dagForceWordsEq, Nat.blt_eq,
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableBinB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append (replayRecipesBinBuilds cut needed history.reverse stock) built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega
theorem knownClosesBinSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : BinViable mask target state) :
    dagKnownClosesBin target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBin target state bound || dagKnownClosesBin target bounds state) = false
    rw [boundClosesBinSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
theorem boundClosesBinFastSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let nstock := stock.map (normWord cut)
  let needed := recipeClosureBinF cut nstock history (recipeStartBinF cut nstock ws)
  let replay := replayRecipesBinF cut needed history.reverse nstock
  simp only [dagBoundClosesBinFast, dagForceWordEq, dagForceWordsEq, flatCountF_eq, normWordFast_eq,
    Nat.blt_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := Nat.blt_eq.mp length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have hnst : ∀ x ∈ nstock, AvBin cut stock x := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    rcases normWord_eq_or cut s with e | e
    · rw [e]; exact Or.inr (Or.inr (Or.inl hs))
    · rw [e]; exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  have hrep := (replayRecipesBinFBuilds cut needed history.reverse stock nstock hnst).1
  have hbank : ∀ x ∈ replay ++ nstock, AvBin cut (replay ++ stock) x := by
    intro x hx
    rcases List.mem_append.mp hx with hr | hs
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left stock hr)))
    · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_append_right replay hy)))) (hnst x hs)
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableNormB_spec (restrictWord cut v) hbank (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append hrep built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega
theorem knownClosesBinNoHdrSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hdr : ∀ b ∈ bounds, dagBoundHeaderOK target b = true)
    (viable : BinViable mask target state) :
    dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) ||
      dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state) = false
    have h1 := boundClosesBinFastSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable
    have hh := hdr bound List.mem_cons_self
    have heq : dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) =
        dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) := by
      obtain ⟨f, ws, hist⟩ := state
      obtain ⟨m, st, lo, g⟩ := bound
      simp only [dagBoundHeaderOK] at hh
      simp only [dagBoundClosesBinNoHdr, dagBoundClosesBinFast, hh, Bool.true_and]
    rw [heq, h1]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
      (fun b hb => hdr b (List.mem_cons_of_mem _ hb))
theorem buildsBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    {values : List Word} (h : WordBuildsBin m roots values) :
    WordBuildsBin n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvBin n bank (f v))
      (h : AvBin m roots v) : AvBin n bank (f v) := by
    rcases h with rfl | rfl | hv | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
    · have h1 := src _ hv; rw [invert] at h1; simpa [xor_cancel_left] using avBin_not h1
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, b, ha, hb, eq | eq⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)
theorem lowerBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    (bound : BinLower n bank (f goal) minimum) :
    BinLower m roots goal minimum := by
  intro values build hit
  suffices AvBin n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsBinMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ (List.mem_map_of_mem hv))))
    · exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw)))) (supply _ hr)
  · rcases List.mem_append.mp mem with hv | hr
    · have h1 : f (m ^^^ goal) ∈ values.map f ++ bank := List.mem_append_left _ (List.mem_map_of_mem hv)
      rw [invert] at h1
      exact Or.inr (Or.inr (Or.inr h1))
    · have h1 := supply _ hr
      rw [invert] at h1
      exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw))))
        (by simpa [xor_cancel_left] using avBin_not h1)
theorem suppliesBinOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableBinB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvBin oldMask old (rename w) := by
  intro w hw
  exact availableBinB_spec.mp (List.all_eq_true.mp h w hw)
def dagShiftCheckBin (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableBinB oldMask old (dagShift mask move w))
theorem dagShiftLowerBin {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : BinLower oldMask old oldGoal min)
    (ok : dagShiftCheckBin width mask goal oldMask oldGoal stock old move = true) :
    BinLower mask stock goal min := by
  simp only [dagShiftCheckBin, Bool.and_eq_true, Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded, unique⟩, masks⟩, goals⟩, supply⟩ := ok
  obtain ⟨andG, orG, xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr; rw [dagShiftLinear]; simp
  apply lowerBinMap (dagShift mask move) zero masks (fun w => by rw [xorG, masks]) andG orG (suppliesBinOfCheck supply)
  rwa [goals]
def gateTokenBin (a b op keep : Nat) : Nat := ((a * 64 + b) * 4 + op) * 4 + keep
theorem gateTokenBinFields {a b op keep : Nat} (hb : b < 64) (ho : op < 4) (hk : keep < 4) :
    gateTokenBin a b op keep % 4 = keep ∧
    gateTokenBin a b op keep / 4 % 4 = op ∧
    gateTokenBin a b op keep / (4 * 4 * 64) = a ∧
    gateTokenBin a b op keep / (4 * 4) % 64 = b := by
  unfold gateTokenBin; omega
def normStock (mask : Word) (stock : List Word) : List Word :=
  List.rec [] (fun w _ rest => insertWord (normWord mask w) rest) stock
theorem normStockSet (mask : Word) (stock : List Word) :
    (normStock mask stock).toFinset = (stock.map (normWord mask)).toFinset := by
  induction stock with
  | nil => simp [normStock]
  | cons w ws ih =>
    change (insertWord (normWord mask w) (normStock mask ws)).toFinset = _
    rw [insertWordSet, ih]; simp
def childStateBin (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 4
  let a := token / (4 * 4 * 64)
  let b := (token / (4 * 4)) % 64
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := normBinOp4 mask op x y
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def dagDirectChildBin (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    some (fuel - 1, insertWord out rest, (out, x, y) :: history)
theorem dagDirectChildBinEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 4) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChildBin mask state a b op keep x y (normBinOp4 mask op x y) =
      childStateBin mask (gateTokenBin a b op keep) state := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨keepEq, opEq, aEq, bEq⟩ := gateTokenBinFields (a := a) hb hop hk
  simp only [childStateBin, dagDirectChildBin, keepWord, keepEq, opEq, aEq, bEq]
def dagTraceBin (mask : Word) (nstock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ nstock.length then some (rootState nstock fuel token) else none
      else (previous (parent - 1)).bind (childStateBin mask token)) (fuel + 1)) i
def dagMoveWordsBin (mask : Word) (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (normWord mask (mixMove m w)) next) ws
theorem dagMoveSetBin {mask : Word} {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWordsBin mask m ws).toFinset = ws.toFinset.image (fun w => normWord mask (relabel select w)) := by
  induction ws with
  | nil => simp [dagMoveWordsBin]
  | cons w ws ih =>
    change (insertWord (normWord mask (mixMove m w)) (dagMoveWordsBin mask m ws)).toFinset = _
    rw [insertWordSet, ih (fun u hu => agree _ (List.mem_cons_of_mem _ hu)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
def dagRefBin (mask : Word) (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto - 1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWordsBin mask m state.2.1
theorem liveBinMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k : Nat} {S : Finset Word} (live : LiveBin mask goal k S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveBin mask goal k (S.image (fun w => normWord mask (relabel select w))) := by
  let g := relabel select
  let f := fun w => normWord mask (g w)
  have hmask : g mask = mask := auto.2.1
  have hxor (w : Word) : g (mask ^^^ w) = mask ^^^ g w := by dsimp only [g]; rw [relabelXor, auto.2.1]
  have fnrm (w : Word) : f (normWord mask w) = f w := by
    rcases normWord_eq_or mask w with h | h
    · rw [h]
    · simp only [f, h, hxor, normWord_symm]
  have injG {a b : Word} (ma : Masked mask a) (mb : Masked mask b) : g a = g b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have injF {a b : Word} (ma : Masked mask a) (mb : Masked mask b)
      (na : normWord mask a = a) (nb : normWord mask b = b) (eq : f a = f b) : a = b := by
    have hrel : g a = g b ∨ g a = mask ^^^ g b := by
      rcases normWord_eq_or mask (g a) with ea | ea <;> rcases normWord_eq_or mask (g b) with eb | eb
      · left; exact ea.symm.trans (eq.trans eb)
      · right; exact ea.symm.trans (eq.trans eb)
      · right
        have h1 : mask ^^^ g a = g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left] at this; exact this
      · left
        have h1 : mask ^^^ g a = mask ^^^ g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left, xor_cancel_left] at this; exact this
    rcases hrel with h1 | h1
    · exact injG ma mb h1
    · rw [← hxor] at h1
      have h2 := injG ma (masked_xor mb) h1
      rw [← na, h2, normWord_symm, nb]
  have properF {a : Word} (ma : Masked mask a) (ha : properWord mask a) : properWord mask (f a) := by
    apply proper_norm
    exact ⟨fun eq => ha.1 (injG ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (injG ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : Masked mask v) (nv : normWord mask v = v)
      (ms : ∀ w ∈ T, Masked mask w) (ns : ∀ w ∈ T, normWord mask w = w) : f v ∉ T.image f := by
    intro hw
    obtain ⟨w, hs, eq⟩ := Finset.mem_image.mp hw
    exact hv (injF (ms w hs) mv (ns w hs) nv eq ▸ hs)
  have opImage {a b : Word} (ma : Masked mask a) (mb : Masked mask b) {op : Nat} (hop : op < 4) :
      ∃ op', op' < 4 ∧ f (normBinOp4 mask op a b) = normBinOp4 mask op' (f a) (f b) := by
    have mfa : Masked mask (f a) := masked_norm (maskedTransfer hmask ma)
    have mfb : Masked mask (f b) := masked_norm (maskedTransfer hmask mb)
    have ga_rel : g a = f a ∨ g a = mask ^^^ f a := by
      rcases normWord_eq_or mask (g a) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have gb_rel : g b = f b ∨ g b = mask ^^^ f b := by
      rcases normWord_eq_or mask (g b) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have hstep : f (normBinOp4 mask op a b) = normWord mask (binOp4 mask op (g a) (g b)) := by
      rw [normBinOp4, fnrm]
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [f, binOp4, g, relabelAnd]
      · simp [f, binOp4, g, relabelOr]
      · simp [f, binOp4, g, relabelAnd, hxor]
      · simp [f, binOp4, g, relabelAnd, hxor]
    rw [hstep]
    have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;> rcases ga_rel with hga | hga <;> rcases gb_rel with hgb | hgb
    · exact ⟨0, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by
        rw [hga, hgb]; change normWord mask (f a ||| (mask ^^^ f b)) = _
        have h1 : mask ^^^ ((mask ^^^ f a) &&& f b) = f a ||| (mask ^^^ f b) := by
          rw [demorgan_and (masked_xor mfa) mfb, xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by
        rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| f b) = _
        have h1 : mask ^^^ (f a &&& (mask ^^^ f b)) = (mask ^^^ f a) ||| f b := by
          rw [demorgan_and mfa (masked_xor mfb), xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| (mask ^^^ f b)) = _; rw [← demorgan_and mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask (f a &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& f b) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& (mask ^^^ f b)) = _; rw [xor_cancel_left]; rfl⟩
  induction live using LiveBin.ind with
  | stop hp =>
    rw [Finset.image_singleton]
    have hfg : f (normWord mask goal) = normWord mask goal := by
      rw [fnrm]; simp only [f, g, auto.2.2]
    change LiveBin mask goal 0 {f (normWord mask goal)}
    rw [hfg]
    exact LiveBin.stop hp
  | @step k U a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply masked_norm
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, mask ^^^ b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨mask ^^^ a, b, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have hns : ∀ w ∈ insert a (insert b U), normWord mask w = w := fun w hw =>
      (liveBinProps (LiveBin.step hop pa pb ab na nb fresh tail) w hw).2
    obtain ⟨op', hop', fve⟩ := opImage ma mb hop
    have ht := ih hnew
    have hf := freshImage fresh mv (normWord_idem mask _) masked hns
    change LiveBin mask goal (k + 1) ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveBin mask goal k (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveBin.step hop' (properF ma pa) (properF mb pb)
      (fun h => ab (injF ma mb na nb h)) (normWord_idem mask _) (normWord_idem mask _) hf ht
theorem dagLinkedBin {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRefBin mask count states moves links parent token state = true)
    {k : Nat} (live : LiveBin mask goal k state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveBin mask goal k saved.2.1.toFinset := by
  unfold dagRefBin at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination, saved, hd, eq, finish.1, ?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select, hauto, agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWordsBin mask m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSetBin (fun w hw => agree w (masked w hw))]
          exact liveBinMaskedImage hauto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
def dagLocalBinFast (mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains ngoal &&
      (fuel == 0 || cut state || !dagPartition false ws goal negGoal))
def dagLocalBin (mask goal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains (normWord mask goal) &&
      (fuel == 0 || cut state || !dagPartition false ws goal (mask ^^^ goal)))
theorem dagLocalBinFast_eq (mask goal : Word) (cut : CutCheck) (state : RowState) :
    dagLocalBinFast mask goal (normWord mask goal) (mask ^^^ goal) cut state =
      dagLocalBin mask goal cut state := rfl
theorem dagLocalBinOpen {mask goal : Word} {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (viable : BinViable mask goal state) (noCut : cut state = false) :
    dagLocalBin mask goal cut state = false := by
  obtain ⟨fuel, ws, history⟩ := state
  have ⟨nd, k, cap, live⟩ := viable
  change k ≤ fuel at cap
  have card := liveBinSize live
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨eq, _⟩ := live
    have hm : normWord mask goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocalBin, fit, hm]
  have sep := dagPartitionLiveBin masked live
  simp [dagLocalBin, fit, hz, sep, noCut]
def dagSizeFloorBin (n keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1)) + 1
def dagTooWideBin (n fuel token : Nat) : Bool :=
  dagSizeFloorBin n (token % 4) > (fuel - 1) + 1
theorem dagWideChildBin {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (wide : dagTooWideBin state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let i := token / (4 * 4 * 64)
  let j := token / (4 * 4) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := normBinOp4 mask op x y
  let a := keep.testBit 0
  let b := keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || i ≥ j
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega
def dagTagStepBin (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 4
  let x := bank.getD (token / (4 * 4 * 64)) (0, 0, 0)
  let y := bank.getD (token / (4 * 4) % 64) (0, 0, 0)
  let raw := binOp4 mask op x.1 y.1
  let comp := mask ^^^ raw
  let up0 := binOp4 full op x.2.1 y.2.1
  let dn0 := binOp4 full op x.2.2 y.2.2
  let tag := if raw < comp then (raw, up0, dn0) else (comp, full ^^^ up0, full ^^^ dn0)
  dagTagInsert tag (dagTagKeep (keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))
def dagTraceTagsBin (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStepBin mask (fullMask width) token (previous (parent - 1))) (fuel + 1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags
def dagCheckChildrenBin (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  dagForceWord (normWordFast mask goal) (fun ngoal =>
  dagForceWord (mask ^^^ goal) (fun negGoal =>
  (n ≤ 64) && !state.2.1.contains ngoal &&
  dagForceWord (dagPackWords256 state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks256 n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        treeBlock 0 n (fun a =>
          dagForceWord (state.2.1.getD a 0) (fun x =>
            dagForceWord (1 <<< (256 * a)) (fun aBit =>
              let xs := tags.getD a (0, 0)
              dagForceWord (dagSignalContrast false full xs) (fun xC =>
                treeBlock (a + 1) (n - (a + 1)) (fun b =>
                  dagForceWord (state.2.1.getD b 0) (fun y =>
                    dagForceWord (1 <<< (256 * b)) (fun bBit =>
                      let ys := tags.getD b (0, 0)
                      dagForceWord (dagSignalContrast false full ys) (fun yC =>
                        treeBlock 0 4 (fun op =>
                          dagForceWord (normBinOp4Fast mask op x y) (fun out =>
                            if out == 0 || out == mask || state.2.1.contains out then true else
                            dagForceWord (binOp4 full op xs.1 ys.1) (fun up =>
                              dagForceWord (binOp4 full op xs.2 ys.2) (fun down =>
                                dagForceWord (dagSignalContrast false full (up, down)) (fun outC =>
                                  treeBlock 0 4 (fun keep =>
                                    let ka := keep.testBit 0
                                    let kb := keep.testBit 1
                                    let nAfter := n - (if ka then 0 else 1) - (if kb then 0 else 1) + 1
                                    if Nat.blt state.1 nAfter then true
                                    else if dagSampleKill256 sample full normal xC yC outC packed marks aBit bBit out false ka kb then true
                                    else match dagDirectChildBin mask state a b op keep x y out with
                                    | none => true
                                    | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                                      let child := (fuel, forced, history)
                                      let token := gateTokenBin a b op keep
                                      reference token child || dagLocalBinFast mask goal ngoal negGoal cut child))))))))))))))))))))))
theorem dagEarlyOpenBin256 {mask goal a b op keep out : Nat} {state child : RowState}
    {sample : DagSample} (full : Word) (counts : DagCounts) (xC yC outC : Word)
    (masked : Masked mask goal) (viable : BinViable mask goal child)
    (parent : state.2.1.Nodup) (svalid : dagSampleValid mask goal sample = true)
    (eval : dagDirectChildBin mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) :
    dagSampleKill256 sample full counts xC yC outC
      (dagPackWords256 state.2.1) (dagLaneMarks256 state.2.1.length)
      (1 <<< (256 * a)) (1 <<< (256 * b)) out false (keep.testBit 0) (keep.testBit 1) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  unfold dagSampleKill256 at closed
  simp only [dagForceWordEq] at closed
  generalize hmiss :
    (((counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& (if keep.testBit 0 then 0 else xC) &&& (if keep.testBit 1 then 0 else yC))) |||
       (counts.1 ^^^ (counts.1 &&& ((if keep.testBit 0 then 0 else xC) ||| (if keep.testBit 1 then 0 else yC))))) ||| outC) ^^^ full) = missing at closed
  by_cases hm : Nat.beq missing 0 = true
  · simp only [hm, ite_true] at closed; cases closed
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ite_false] at closed
    by_cases hlt : Nat.blt (dagHighest7 missing) sample.2 = true
    · simp only [hlt, ite_true] at closed
      have hidx : dagHighest7 missing < sample.2 := Nat.blt_eq.mp hlt
      have pairOK := treeBlock_at svalid (Nat.zero_le _) (by simpa using hidx)
      have closed' := dagPackedPair256Sound parent pairOK closed
      let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
      let stale : Bool := out == 0 || out == mask || ws.contains out
      let bank := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
      change (if bad then none else if stale then none else
        some (fuel - 1, insertWord out bank, (out, x, y) :: history)) = some child at eval
      by_cases h : bad = true
      · simp [h] at eval
      by_cases h' : stale = true
      · simp [h, h'] at eval
      have eq : (fuel - 1, insertWord out bank, (out, x, y) :: history) = child := by simpa [h, h'] using eval
      subst child
      obtain ⟨nd, k, cap, live⟩ := viable
      have same : (out :: bank).toFinset = (insertWord out bank).toFinset := by
        ext w
        simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
      have refuses := dagPairsOpenBin (pairs := [unpack sample.1 18 (dagHighest7 missing)]) masked
        (show LiveBin mask goal k (out :: bank).toFinset by rwa [same])
      exact Bool.noConfusion (closed'.symm.trans refuses)
    · simp only [Bool.not_eq_true] at hlt
      simp only [hlt, Bool.false_eq_true, ite_false] at closed
theorem dagChildAtBin {mask goal : Word} {cut : CutCheck} {ref : Nat → RowState → Bool}
    {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildrenBin mask goal cut ref state sample tags = true)
    (svalid : dagSampleValid mask goal sample = true)
    (ha : a < state.2.1.length) (hab : a < b) (hb : b < state.2.1.length) (hop : op < 4) (hk : keep < 4)
    (eval : childStateBin mask (gateTokenBin a b op keep) state = some child)
    (masked : Masked mask goal) (viable : BinViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocalBin mask goal cut child = false) :
    ref (gateTokenBin a b op keep) child = true := by
  have narrow : Nat.blt state.1 (state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hlt : state.1 < state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1 := Nat.blt_eq.mp h
    have hb64 : b < 64 := by
      simp only [dagCheckChildrenBin, dagForceWordEq, dagForceCacheEq, dagCountSignsEq, normWordFast_eq,
        Bool.and_eq_true, decide_eq_true_eq] at checked
      omega
    obtain ⟨ke, _, _, _⟩ := gateTokenBinFields (a := a) hb64 hop hk
    have hpos : 0 < state.1 := by
      rcases state with ⟨sf, sws, shist⟩
      by_contra! hz
      have h0 : sf = 0 := by omega
      subst h0
      simp [childStateBin] at eval
    have hwide : dagTooWideBin state.2.1.length state.1 (gateTokenBin a b op keep) = true := by
      simp only [dagTooWideBin, dagSizeFloorBin, ke, decide_eq_true_eq]
      omega
    have tooMany := dagWideChildBin eval hwide
    obtain ⟨f, w, path⟩ := child
    simp [dagLocalBin, tooMany] at openChild
  simp only [dagCheckChildrenBin, dagForceCacheEq, dagForceWordEq, dagCountSignsEq, normWordFast_eq, normBinOp4Fast_eq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  have atB := treeBlock_at atA (i := b) (by omega) (by omega)
  have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
  have fields := dagDirectChildBinEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
    (keep := keep) (by omega) hop hk
  have direct := fields.trans eval
  have notStale : (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == 0 ||
      normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == mask ||
      state.2.1.contains (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    rcases state with ⟨f, ws, hist⟩
    dsimp only [dagDirectChildBin] at hs direct
    by_cases hbad : (f == 0 || b ≥ ws.length || a ≥ b) = true
    · simp only [hbad, ite_true] at direct; cases direct
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, Bool.false_eq_true, ite_false, hs, ite_true] at direct
      cases direct
  simp only [notStale, Bool.false_eq_true, ite_false] at atOp
  have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
  have early := fun full counts xC yC outC => dagEarlyOpenBin256 full counts xC yC outC masked viable nd svalid direct
  rcases child with ⟨fuel, ws, history⟩
  simpa only [narrow, Bool.false_eq_true, ite_false, fields, eval, dagForceWordsEq, early,
    dagLocalBinFast_eq, openChild, Bool.or_false] using atKeep
def HasChildBin (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧ a < b ∧ b < state.2.1.length ∧ op < 4 ∧ keep < 4 ∧
    childStateBin mask (gateTokenBin a b op keep) state = some child
theorem binaryChildBin {mask fuel a b op : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (hop : op < 4) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (normBinOp4 mask op x y)) (fresh : normBinOp4 mask op x y ∉ ws) :
    childStateBin mask (gateTokenBin a b op keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (normBinOp4 mask op x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (normBinOp4 mask op x y, x, y) :: history) := by
  obtain ⟨ke, ope, aa, bb⟩ := gateTokenBinFields (a := a) hb64 hop hk
  simp only [childStateBin, ke, ope, aa, bb, hx, hy]
  simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, properWord]
theorem stepProgressBin {mask fuel k op : Nat} {x y target : Word} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel) (hop : op < 4)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : normBinOp4 mask op x y ∉ insert x (insert y U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op x y) U)) :
    ∃ child, HasChildBin mask (fuel, ws, history) child ∧ BinViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := normBinOp4 mask op x y
  have p := (liveBinProps tail v (Finset.mem_insert_self _ _)).1
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep; cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, op, keep, ha, hab, hb, hop, keepLt, ?_⟩, ?_⟩
  · have eq := binaryChildBin (fuel := fuel) (history := history) hop hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveBin mask target k (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
theorem wordProgressBin {mask target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : BinViable mask target state) :
    normWord mask target ∈ state.2.1 ∨ ∃ child, HasChildBin mask state child ∧ BinViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := live
    left
    change ws.toFinset = {normWord mask target} at eq
    rw [← List.mem_toFinset, eq]; simp
  | succ k =>
    right
    obtain ⟨U, x, y, op, hop, eq, px, py, xy, nx, ny, fresh, tail⟩ := live
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same; apply xy; rw [← getWord xm, same, getWord ym]
    by_cases hord : ws.idxOf x < ws.idxOf y
    · exact stepProgressBin nd width cap hop eq xy hord fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : normBinOp4 mask (swapOp4 op) y x ∉ insert y (insert x U) := by
        rw [normBinOp4_swap mask hop, Finset.insert_comm]; exact fresh
      have tail' : LiveBin mask target k (insert (normBinOp4 mask (swapOp4 op) y x) U) := by
        rw [normBinOp4_swap mask hop]; exact tail
      exact stepProgressBin nd width cap (swapOp4_lt hop) eq' xy.symm (by omega) fresh' tail'
theorem childStateBinData {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let a := token / (4 * 4 * 64)
  let b := token / (4 * 4) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := normBinOp4 mask op x y
  let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega, ?_⟩
  have mx : Masked mask x := readWordMasked masked a
  have my : Masked mask y := readWordMasked masked b
  have hm : Masked mask z := by
    apply masked_norm
    unfold binOp4
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, mask ^^^ y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨mask ^^^ x, y, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (keep.testBit 1) y _ w other
def dagCheckNodeBin (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) =>
    dagForceWord goal (fun goal' =>
      dagFilterForceBoundsBin goal' (nodeBounds i) (fun activeBounds =>
        dagForceLinkList (linkList (i + 1)) (fun nlinks =>
          dagForceWords ws (fun forced =>
            dagStateOK mask forced && dagCheckChildrenBin mask goal' (dagKnownClosesBinNoHdr activeBounds)
              (dagRefBin mask count states moves (fun _ tok => dagFindLink nlinks tok) 0)
              (fuel, forced, history) sample (tags i)))))
def dagAllowedRootBin (mask : Word) (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (normWord mask (witnessWord entry)))
def dagCheckRootsBin (mask goal : Word) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (nstock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ nstock.length) fun token =>
    let state := rootState nstock fuel token
    !dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal cut state || reference token state
theorem dagAllNodesBin {mask goal : Word} {width fuel count : Nat}
    {nstock : List Word} {nodeBounds : Nat → List Bound} {forest : Forest} {moves : Array WordMove}
    {linkList : DagLinkList} {sample : DagSample} {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (cutSound : ∀ i s, BinViable mask goal s →
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds count
      (dagTraceBin mask nstock fuel forest) moves linkList sample tags) = true) :
    ∀ cap i saved, i < count → dagTraceBin mask nstock fuel forest i = some saved →
      saved.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTraceBin mask nstock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNodeBin mask goal nodeBounds count states moves linkList sample tags i = true at checked
    simp only [dagCheckNodeBin, stateEq, dagForceWordEq, dagFilterForceBoundsBinEq, dagForceLinkListEq,
      dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd, masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : BinViable mask goal s := ⟨nd, k, sFuel ▸ kBound, live⟩
    have scanned := ok
    simp only [dagCheckChildrenBin, dagForceWordEq, normWordFast_eq, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgressBin wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a, b, op, keep, ha, hab, hb, hop, hk, eval⟩ := possible
    have r := dagChildAtBin ok svalid ha hab hb hop hk eval goalMask cv nd
      (dagLocalBinOpen goalMask cv (cutSound i _ cv))
    have ⟨less, cm⟩ := childStateBinData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_, k', fits, clive⟩ := cv
    obtain ⟨j, dest, bound, restore, fuelEq, tail⟩ := dagLinkedBin maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' fits tail
theorem lowerDagBin {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {forest : Forest} {moves : Array WordMove} {linkList : DagLinkList}
    {sample : DagSample} {tags : Nat → List DagSignals}
    {bounds : List Bound} {nodeBounds : Nat → List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w)
    (nstockNd : (normStock mask stock).Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : KnownBin bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nodeSub : ∀ i b, b ∈ nodeBounds i → b ∈ bounds)
    (rootCheck : dagCheckRootsBin mask goal (dagKnownClosesBin goal bounds) witnesses
      (dagRefBin mask count (dagTraceBin mask (normStock mask stock) fuel forest) moves
        (fun p tok => dagFindLink (linkList p) tok) 0)
      (normStock mask stock) fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds
      count (dagTraceBin mask (normStock mask stock) fuel forest) moves linkList sample tags) = true) :
    BinLower mask stock goal (fuel + 1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive stockMasked build hit proper
  let nstock := normStock mask stock
  have included : S ⊆ nstock.toFinset := by
    intro w hw
    rw [normStockSet, List.mem_toFinset]
    exact sub w hw
  obtain ⟨token, tokenBound, eq⟩ := rootToken nstock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState nstock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : BinViable mask goal state := by
    refine ⟨(rootWordSublist nstock token).nodup nstockNd, k, ?_, ?_⟩
    · change k ≤ fuel; omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : BinViable mask goal s) : dagKnownClosesBin goal bounds s = false :=
    knownClosesBinSound known submasks h
  have nodeCutOpen (i : Nat) (s : RowState) (h : BinViable mask goal s) :
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false :=
    knownClosesBinNoHdrSound
      (fun b hb => known b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => submasks b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => (List.mem_filter.mp hb).2) h
  have openRoot := dagLocalBinOpen goalMask v (cutOpen _ v)
  have allowed : dagAllowedRootBin mask witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequiredBin (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) state ||
    dagRefBin mask count (dagTraceBin mask nstock fuel forest) moves
      (fun p tok => dagFindLink (linkList p) tok) 0 token state) = true at checked
  simp only [allowed, openRoot, Bool.not_true, Bool.false_or] at checked
  have finish := dagAllNodesBin maskBounds goalMask svalid nodeCutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveBin mask goal k state.2.1.toFinset := by rwa [eq']
  have nstockMasked : ∀ w ∈ nstock, Masked mask w := by
    intro w hw
    have h1 : w ∈ nstock.toFinset := List.mem_toFinset.mpr hw
    rw [normStockSet, List.mem_toFinset] at h1
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp h1
    exact masked_norm (stockMasked orig omem)
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact nstockMasked _ ((rootWordSublist nstock token).subset hw)
  obtain ⟨i, s, hi, restore, cap, plan⟩ := dagLinkedBin maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k fits plan
theorem hcsGateWordMono {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    GateWordMono (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) := Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
def isNotOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.not => true
  | _ => false
def countNonNot : List PEqualNP.CircuitLowerBounds.Gate → Nat
  | [] => 0
  | g :: rest => (if isNotOp g.op then 0 else 1) + countNonNot rest
theorem countNonNot_le_sub {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (h : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
    countNonNot gs + 1 ≤ gs.length := by
  induction gs with
  | nil => obtain ⟨_, hm, _⟩ := h; simp at hm
  | cons g gs ih =>
    have hle : ∀ l, countNonNot l ≤ l.length := by
      intro l; induction l with
      | nil => simp [countNonNot]
      | cons x xs ihx => simp only [countNonNot, List.length_cons]; cases isNotOp x.op <;> simp <;> omega
    obtain ⟨g', hm, hop⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [countNonNot, hop, isNotOp, ite_true, Nat.zero_add, List.length_cons]
      have := hle gs; omega
    · have := ih ⟨g', hm, hop⟩
      simp only [countNonNot, List.length_cons]
      cases isNotOp g.op <;> simp <;> omega
theorem hcsBuildsBin {rows : Nat} (raw : List (BitVec rows)) (bank : List Word)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (sub0 : ∀ v ∈ raw, AvBin (fullMask rows) bank v.toNat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length ≤ countNonNot gs ∧ WordBuildsBin (fullMask rows) bank vs ∧
      ∀ v ∈ gs.foldl hcsStep raw, AvBin (fullMask rows) (vs ++ bank) v.toNat := by
  induction gs generalizing raw bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, fun v hv => sub0 v hv⟩
  | cons g gs ih =>
    let v := hcsGateVal raw g
    have hg := hfan g List.mem_cons_self
    have hop := hg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have avRaw (i : Nat) : AvBin (fullMask rows) bank (raw.getD i 0).toNat := by
      rw [List.getD_eq_getElem?_getD]
      cases h : raw[i]? with
      | none => exact Or.inl rfl
      | some a => exact sub0 a (List.mem_of_getElem? h)
    rcases hop with h_and | h_or | h_not
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inl h_and) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_and, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inr h_or) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_or, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have hv : AvBin (fullMask rows) bank v.toNat := by
        obtain ⟨op, ins⟩ := g
        simp only at h_not; subst op
        cases ins with
        | nil =>
          have : v.toNat = fullMask rows ^^^ 0 := by simpa [v, hcsGateVal] using notNat (0 : BitVec rows)
          rw [this]; exact avBin_not (Or.inl rfl)
        | cons a _ =>
          have : v.toNat = fullMask rows ^^^ (raw.getD a 0).toNat := by
            simpa [v, hcsGateVal] using notNat (raw.getD a 0)
          rw [this]; exact avBin_not (avRaw a)
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) bank u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact sub0 u hu
        · exact hv
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) bank sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨xs, ?_, built, reach⟩
      simp only [countNonNot, h_not, isNotOp, ite_true, Nat.zero_add]; exact len
end PEqualNP.Outside.L_meta_32836.Contraction

namespace PEqualNP.Outside.L_meta_32836.Cert
open PEqualNP.Outside.L_meta_32836.Contraction

def qS0 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def qS1 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def qS2 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def qS3 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def qS4 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def qS5 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def qS6 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def qS7 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def qS8 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def qS9 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def qS10 : WordMoveStep := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def qS11 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def qS12 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def qS13 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 2)])
def qS14 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 16)])
def qS15 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 8)])
def qS16 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 32)])
def qS17 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS18 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def qS19 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def qS20 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def qS21 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS22 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def qS23 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 0)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def qS24 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def qS25 : WordMoveStep := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 1)])
def qS26 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 16)], [])
def qS27 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS28 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 0)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def qS29 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS30 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def qS31 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def qS32 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def qS33 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff, 0), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000, 112)])
def qS34 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333, 0), (0xcccccccccccccccccccccccccccccccc, 126)], [(0x3333333333333333333333333333333300000000000000000000000000000000, 126)])
def qS35 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def qS36 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0), (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 32)], [])
def qS37 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def qS38 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 0)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def qS39 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0), (0x5555555555555555555555555555555555555555555555555555555555555555, 64)], [])
def qS40 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 128)], [])
def qS41 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555, 0), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0x5555555555555555555555555555555500000000000000000000000000000000, 127)])
def qBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def qGoal : Word := 0xfffffffffffffffffffffffefffffffeffffffeeffffeeeeffeeffaaeeccaa00
def q0M : Word := 0x30300000303
abbrev q0G : Word := qGoal &&& q0M
abbrev q0W : List Word := projectDAGStock q0M qBase [0, 3, 5]
def q0F : Bound := (q0M, q0W, 4, q0G)
def q0E := unpackWitnesses q0W [16928, 282656, 544776]
abbrev q0N : List Word := normStock q0M q0W
def q0C : List Bound := []
def q0S : DagSample := (0x40244021008840209100a01028, 6)
def q0L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 3
def q0D : Forest := fun i => decodeNode 1 4 0xe i
def q0T := dagTraceTagsBin q0M 6 (dagTagBases q0N 0x3624 0x337ad 6) 3 q0D
def q0St := dagTraceBin q0M q0N 3 q0D
def q0Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q0Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q0Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q0Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q0Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q0Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q0Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q0Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q0Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q0Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q0Mv := dagMoves ([([qS0], q0Mp0, q0Mi0), ([qS1], q0Mp1, q0Mi1), ([qS2, qS0], q0Mp2, q0Mi2), ([qS1, qS0], q0Mp3, q0Mi3), ([qS2], q0Mp4, q0Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0A : DagMovesOK q0M q0G 256 q0Mv := dagMovesOfCheck (by decide +kernel)
def q0NB : Nat → List Bound := dagNodeBounds q0C.toArray 0x0 0x0 2 1 1
def q0Ck := dagCheckNodeBin q0M q0G q0NB 1 q0St q0Mv q0L q0S q0T
def q0RA (token : Nat) : Bool :=
  let s := rootState q0N 3 token
  !dagAllowedRootBin q0M q0E s.2.1 || dagLocalBin q0M q0G (dagKnownClosesBin q0G q0C) s ||
  dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0RB0 : treeBlock 0 8 q0RA = true := by decide +kernel
theorem q0R : dagCheckRootsBin q0M q0G (dagKnownClosesBin q0G q0C) q0E (dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0) q0N 3 = true := q0RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0B0 : treeBlock 0 1 q0Ck = true := by decide +kernel
theorem q0Bk : treeBlock 0 1 q0Ck = true := q0B0
theorem q0K : KnownBin q0C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Bin : BinLower q0M q0W q0G 4 := by
  apply lowerDagBin _ _ _ _ q0A _ _ _ q0K _ (fun _ b hb => dagNodeBounds_mem b hb) q0R q0Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q0C.all (fun b => q0M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q1M : Word := 0xf0f00
abbrev q1G : Word := qGoal &&& q1M
abbrev q1W : List Word := projectDAGStock q1M qBase [0, 1, 3]
def q1E := unpackWitnesses q1W [5642, 271889, 533514]
abbrev q1N : List Word := normStock q1M q1W
def q1C : List Bound := []
def q1S : DagSample := (0x1009080481409088241412, 5)
def q1L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 1
def q1D : Forest := fun i => decodeNode 1 4 0xe i
def q1T := dagTraceTagsBin q1M 5 (dagTagBases q1N 0x26d6 0x7755 5) 2 q1D
def q1St := dagTraceBin q1M q1N 2 q1D
def q1Mv := dagMoves ([] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1A : DagMovesOK q1M q1G 256 q1Mv := dagMovesOfCheck (by decide +kernel)
def q1NB : Nat → List Bound := dagNodeBounds q1C.toArray 0x0 0x0 2 1 1
def q1Ck := dagCheckNodeBin q1M q1G q1NB 1 q1St q1Mv q1L q1S q1T
def q1RA (token : Nat) : Bool :=
  let s := rootState q1N 2 token
  !dagAllowedRootBin q1M q1E s.2.1 || dagLocalBin q1M q1G (dagKnownClosesBin q1G q1C) s ||
  dagRefBin q1M 1 q1St q1Mv (fun p tok => dagFindLink (q1L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1RB0 : treeBlock 0 8 q1RA = true := by decide +kernel
theorem q1R : dagCheckRootsBin q1M q1G (dagKnownClosesBin q1G q1C) q1E (dagRefBin q1M 1 q1St q1Mv (fun p tok => dagFindLink (q1L p) tok) 0) q1N 2 = true := q1RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1B0 : treeBlock 0 1 q1Ck = true := by decide +kernel
theorem q1Bk : treeBlock 0 1 q1Ck = true := q1B0
theorem q1K : KnownBin q1C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1Bin : BinLower q1M q1W q1G 3 := by
  apply lowerDagBin _ _ _ _ q1A _ _ _ q1K _ (fun _ b hb => dagNodeBounds_mem b hb) q1R q1Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q1C.all (fun b => q1M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q2M : Word := 0x500050000000000050005
abbrev q2G : Word := qGoal &&& q2M
abbrev q2W : List Word := projectDAGStock q2M qBase [1, 4, 6]
def q2F : Bound := (q2M, q2W, 4, q2G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2Bin : BinLower q2M q2W q2G 4 := dagShiftLowerBin (width := 256) [qS3, qS4, qS5] q0Bin (by decide +kernel)
def q3M : Word := 0x30300000000000000000000000000000303
abbrev q3G : Word := qGoal &&& q3M
abbrev q3W : List Word := projectDAGStock q3M qBase [0, 3, 7]
def q3F : Bound := (q3M, q3W, 4, q3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q3Bin : BinLower q3M q3W q3G 4 := dagShiftLowerBin (width := 256) [qS6, qS7] q0Bin (by decide +kernel)
def q4M : Word := 0x5000500000000000000000000000000050005
abbrev q4G : Word := qGoal &&& q4M
abbrev q4W : List Word := projectDAGStock q4M qBase [1, 4, 7]
def q4F : Bound := (q4M, q4W, 4, q4G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4Bin : BinLower q4M q4W q4G 4 := dagShiftLowerBin (width := 256) [qS3, qS4, qS6, qS7] q0Bin (by decide +kernel)
def q5M : Word := 0x3000000000000000300000000000000030000000000000003
abbrev q5G : Word := qGoal &&& q5M
abbrev q5W : List Word := projectDAGStock q5M qBase [0, 6, 7]
def q5F : Bound := (q5M, q5W, 4, q5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5Bin : BinLower q5M q5W q5G 4 := dagShiftLowerBin (width := 256) [qS8, qS9, qS6] q0Bin (by decide +kernel)
def q6M : Word := 0x5000000000000000500000000000000050000000000000005
abbrev q6G : Word := qGoal &&& q6M
abbrev q6W : List Word := projectDAGStock q6M qBase [1, 6, 7]
def q6F : Bound := (q6M, q6W, 4, q6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6Bin : BinLower q6M q6W q6G 4 := dagShiftLowerBin (width := 256) [qS3, qS8, qS9, qS6] q0Bin (by decide +kernel)
def q7M : Word := 0x10001000000000001000100000000000100010000000000010001
abbrev q7G : Word := qGoal &&& q7M
abbrev q7W : List Word := projectDAGStock q7M qBase [4, 6, 7]
def q7F : Bound := (q7M, q7W, 4, q7G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q7Bin : BinLower q7M q7W q7G 4 := dagShiftLowerBin (width := 256) [qS10, qS11, qS12, qS8, qS6] q0Bin (by decide +kernel)
def q8M : Word := 0xc0c00000c0c
abbrev q8G : Word := qGoal &&& q8M
abbrev q8W : List Word := projectDAGStock q8M qBase [0, 3, 5]
def q8F : Bound := (q8M, q8W, 4, q8G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8Bin : BinLower q8M q8W q8G 4 := dagShiftLowerBin (width := 256) [qS13] q0Bin (by decide +kernel)
def q9M : Word := 0x303000003030000
abbrev q9G : Word := qGoal &&& q9M
abbrev q9W : List Word := projectDAGStock q9M qBase [0, 3, 5]
def q9F : Bound := (q9M, q9W, 4, q9G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q9Bin : BinLower q9M q9W q9G 4 := dagShiftLowerBin (width := 256) [qS14] q0Bin (by decide +kernel)
def q10M : Word := 0x50005000000000005000500
abbrev q10G : Word := qGoal &&& q10M
abbrev q10W : List Word := projectDAGStock q10M qBase [1, 4, 6]
def q10F : Bound := (q10M, q10W, 4, q10G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q10Bin : BinLower q10M q10W q10G 4 := dagShiftLowerBin (width := 256) [qS15, qS3, qS4, qS5] q0Bin (by decide +kernel)
def q11M : Word := 0x50005000000000005000500000000
abbrev q11G : Word := qGoal &&& q11M
abbrev q11W : List Word := projectDAGStock q11M qBase [1, 4, 6]
def q11F : Bound := (q11M, q11W, 4, q11G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q11Bin : BinLower q11M q11W q11G 4 := dagShiftLowerBin (width := 256) [qS16, qS3, qS4, qS5] q0Bin (by decide +kernel)
def q12M : Word := 0x500050000000000000000000000000005000500000000
abbrev q12G : Word := qGoal &&& q12M
abbrev q12W : List Word := projectDAGStock q12M qBase [1, 4, 7]
def q12F : Bound := (q12M, q12W, 4, q12G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Bin : BinLower q12M q12W q12G 4 := dagShiftLowerBin (width := 256) [qS16, qS3, qS4, qS6, qS7] q0Bin (by decide +kernel)
def q13M : Word := 0x500000000000000050000000000000005000000000000000500000000
abbrev q13G : Word := qGoal &&& q13M
abbrev q13W : List Word := projectDAGStock q13M qBase [1, 6, 7]
def q13F : Bound := (q13M, q13W, 4, q13G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q13Bin : BinLower q13M q13W q13G 4 := dagShiftLowerBin (width := 256) [qS16, qS3, qS8, qS9, qS6] q0Bin (by decide +kernel)
def q14M : Word := 0xc030000000000000c03
abbrev q14G : Word := qGoal &&& q14M
abbrev q14W : List Word := projectDAGStock q14M qBase [0, 1, 6]
def q14F : Bound := (q14M, q14W, 4, q14G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Bin : BinLower q14M q14W q14G 4 := dagShiftLowerBin (width := 256) [qS17, qS18, qS19, qS5] q0Bin (by decide +kernel)
def q15M : Word := 0xc000000030000000c00000003
abbrev q15G : Word := qGoal &&& q15M
abbrev q15W : List Word := projectDAGStock q15M qBase [0, 1, 6]
def q15F : Bound := (q15M, q15W, 4, q15G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Bin : BinLower q15M q15W q15G 4 := dagShiftLowerBin (width := 256) [qS20, qS18, qS19, qS5] q0Bin (by decide +kernel)
def q16M : Word := 0x30000030000000003000003
abbrev q16G : Word := qGoal &&& q16M
abbrev q16W : List Word := projectDAGStock q16M qBase [0, 3, 6]
def q16F : Bound := (q16M, q16W, 4, q16G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Bin : BinLower q16M q16W q16G 4 := dagShiftLowerBin (width := 256) [qS21, qS5] q0Bin (by decide +kernel)
def q17M : Word := 0x30000000000030003000000000003
abbrev q17G : Word := qGoal &&& q17M
abbrev q17W : List Word := projectDAGStock q17M qBase [0, 4, 6]
def q17F : Bound := (q17M, q17W, 4, q17G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Bin : BinLower q17M q17W q17G 4 := dagShiftLowerBin (width := 256) [qS20, qS4, qS5] q0Bin (by decide +kernel)
def q18M : Word := 0xc0300000000000000000000000000000c03
abbrev q18G : Word := qGoal &&& q18M
abbrev q18W : List Word := projectDAGStock q18M qBase [0, 1, 7]
def q18F : Bound := (q18M, q18W, 4, q18G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q18Bin : BinLower q18M q18W q18G 4 := dagShiftLowerBin (width := 256) [qS17, qS18, qS19, qS6, qS7] q0Bin (by decide +kernel)
def q19M : Word := 0xc0000000300000000000000000000000c00000003
abbrev q19G : Word := qGoal &&& q19M
abbrev q19W : List Word := projectDAGStock q19M qBase [0, 1, 7]
def q19F : Bound := (q19M, q19W, 4, q19G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q19Bin : BinLower q19M q19W q19G 4 := dagShiftLowerBin (width := 256) [qS20, qS18, qS19, qS6, qS7] q0Bin (by decide +kernel)
def q20M : Word := 0xa0005000000000000000000000000000a0005
abbrev q20G : Word := qGoal &&& q20M
abbrev q20W : List Word := projectDAGStock q20M qBase [0, 1, 7]
def q20F : Bound := (q20M, q20W, 4, q20G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q20Bin : BinLower q20M q20W q20G 4 := dagShiftLowerBin (width := 256) [qS21, qS18, qS19, qS6, qS7] q0Bin (by decide +kernel)
def q21M : Word := 0x4040000010100000000000000000000040400000101
abbrev q21G : Word := qGoal &&& q21M
abbrev q21W : List Word := projectDAGStock q21M qBase [1, 3, 7]
def q21F : Bound := (q21M, q21W, 4, q21G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q21Bin : BinLower q21M q21W q21G 4 := dagShiftLowerBin (width := 256) [qS20, qS3, qS6, qS7] q0Bin (by decide +kernel)
def q22M : Word := 0x300000000000300000000000000000003000000000003
abbrev q22G : Word := qGoal &&& q22M
abbrev q22W : List Word := projectDAGStock q22M qBase [0, 4, 7]
def q22F : Bound := (q22M, q22W, 4, q22G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q22Bin : BinLower q22M q22W q22G 4 := dagShiftLowerBin (width := 256) [qS20, qS4, qS6, qS7] q0Bin (by decide +kernel)
def q23M : Word := 0x10100000000010100000000000000000101000000000101
abbrev q23G : Word := qGoal &&& q23M
abbrev q23W : List Word := projectDAGStock q23M qBase [3, 4, 7]
def q23F : Bound := (q23M, q23W, 4, q23G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q23Bin : BinLower q23M q23W q23G 4 := dagShiftLowerBin (width := 256) [qS20, qS1, qS22, qS19, qS4, qS6, qS7] q0Bin (by decide +kernel)
def q24M : Word := 0x10100000000000000000000010100000101000000000000000000000101
abbrev q24G : Word := qGoal &&& q24M
abbrev q24W : List Word := projectDAGStock q24M qBase [3, 5, 7]
def q24F : Bound := (q24M, q24W, 4, q24G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24Bin : BinLower q24M q24W q24G 4 := dagShiftLowerBin (width := 256) [qS23, qS1, qS22, qS19, qS0, qS24, qS6, qS7] q0Bin (by decide +kernel)
def q25M : Word := 0x5050000000000000a0a
abbrev q25G : Word := qGoal &&& q25M
abbrev q25W : List Word := projectDAGStock q25M qBase [0, 1, 3]
def q25F : Bound := (q25M, q25W, 3, q25G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25Bin : BinLower q25M q25W q25G 3 := dagShiftLowerBin (width := 256) [qS23, qS25, qS3, qS22, qS26] q1Bin (by decide +kernel)
def q26M : Word := 0xf000f0000
abbrev q26G : Word := qGoal &&& q26M
abbrev q26W : List Word := projectDAGStock q26M qBase [0, 1, 4]
def q26F : Bound := (q26M, q26W, 3, q26G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26Bin : BinLower q26M q26W q26G 3 := dagShiftLowerBin (width := 256) [qS20, qS27, qS4, qS26] q1Bin (by decide +kernel)
def q27M : Word := 0x5000500000000000a000a
abbrev q27G : Word := qGoal &&& q27M
abbrev q27W : List Word := projectDAGStock q27M qBase [0, 1, 4]
def q27F : Bound := (q27M, q27W, 4, q27G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27Bin : BinLower q27M q27W q27G 4 := dagShiftLowerBin (width := 256) [qS23, qS25, qS18, qS19, qS24] q0Bin (by decide +kernel)
def q28M : Word := 0x30303030000
abbrev q28G : Word := qGoal &&& q28M
abbrev q28W : List Word := projectDAGStock q28M qBase [0, 3, 4]
def q28F : Bound := (q28M, q28W, 4, q28G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q28Bin : BinLower q28M q28W q28G 4 := dagShiftLowerBin (width := 256) [qS20, qS27, qS24] q0Bin (by decide +kernel)
def q29M : Word := 0x30300000000000000000000000003030000
abbrev q29G : Word := qGoal &&& q29M
abbrev q29W : List Word := projectDAGStock q29M qBase [0, 3, 4]
def q29F : Bound := (q29M, q29W, 4, q29G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q29Bin : BinLower q29M q29W q29G 4 := dagShiftLowerBin (width := 256) [qS28, qS27, qS24] q0Bin (by decide +kernel)
def q30M : Word := 0x10101010000000002020202
abbrev q30G : Word := qGoal &&& q30M
abbrev q30W : List Word := projectDAGStock q30M qBase [0, 3, 4]
def q30F : Bound := (q30M, q30W, 3, q30G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Bin : BinLower q30M q30W q30G 3 := dagShiftLowerBin (width := 256) [qS23, qS1, qS11, qS12, qS26] q1Bin (by decide +kernel)
def q31M : Word := 0x50505050000
abbrev q31G : Word := qGoal &&& q31M
abbrev q31W : List Word := projectDAGStock q31M qBase [1, 3, 4]
def q31F : Bound := (q31M, q31W, 3, q31G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Bin : BinLower q31M q31W q31G 3 := dagShiftLowerBin (width := 256) [qS20, qS3, qS22, qS19, qS4, qS26] q1Bin (by decide +kernel)
def q32M : Word := 0x5000500000000000000000000000005000500
abbrev q32G : Word := qGoal &&& q32M
abbrev q32W : List Word := projectDAGStock q32M qBase [1, 3, 4]
def q32F : Bound := (q32M, q32W, 4, q32G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Bin : BinLower q32M q32W q32G 4 := dagShiftLowerBin (width := 256) [qS28, qS29, qS3, qS24] q0Bin (by decide +kernel)
def q33M : Word := 0x5000000050000000a0000000a
abbrev q33G : Word := qGoal &&& q33M
abbrev q33W : List Word := projectDAGStock q33M qBase [0, 1, 5]
def q33F : Bound := (q33M, q33W, 3, q33G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Bin : BinLower q33M q33W q33G 3 := dagShiftLowerBin (width := 256) [qS23, qS25, qS3, qS30, qS0, qS24, qS26] q1Bin (by decide +kernel)
def q34M : Word := 0x101000001010000020200000202
abbrev q34G : Word := qGoal &&& q34M
abbrev q34W : List Word := projectDAGStock q34M qBase [0, 3, 5]
def q34F : Bound := (q34M, q34W, 4, q34G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Bin : BinLower q34M q34W q34G 4 := dagShiftLowerBin (width := 256) [qS23] q0Bin (by decide +kernel)
def q35M : Word := 0x50000000500000000000000000000050000000500
abbrev q35G : Word := qGoal &&& q35M
abbrev q35W : List Word := projectDAGStock q35M qBase [1, 3, 5]
def q35F : Bound := (q35M, q35W, 3, q35G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Bin : BinLower q35M q35W q35G 3 := dagShiftLowerBin (width := 256) [qS28, qS29, qS3, qS30, qS31, qS24, qS26] q1Bin (by decide +kernel)
def q36M : Word := 0x10001000100010002000200020002
abbrev q36G : Word := qGoal &&& q36M
abbrev q36W : List Word := projectDAGStock q36M qBase [0, 4, 5]
def q36F : Bound := (q36M, q36W, 3, q36G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q36Bin : BinLower q36M q36W q36G 3 := dagShiftLowerBin (width := 256) [qS23, qS25, qS10, qS30, qS31, qS4, qS24, qS26] q1Bin (by decide +kernel)
def q37M : Word := 0x100010001000100000000000000000100010001000100
abbrev q37G : Word := qGoal &&& q37M
abbrev q37W : List Word := projectDAGStock q37M qBase [3, 4, 5]
def q37F : Bound := (q37M, q37W, 3, q37G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q37Bin : BinLower q37M q37W q37G 3 := dagShiftLowerBin (width := 256) [qS28, qS29, qS10, qS30, qS12, qS24, qS26] q1Bin (by decide +kernel)
def q38M : Word := 0x5000000000000000500000000000005000000000000000500
abbrev q38G : Word := qGoal &&& q38M
abbrev q38W : List Word := projectDAGStock q38M qBase [1, 3, 6]
def q38F : Bound := (q38M, q38W, 4, q38G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q38Bin : BinLower q38M q38W q38G 4 := dagShiftLowerBin (width := 256) [qS28, qS29, qS3, qS5] q0Bin (by decide +kernel)
def q39M : Word := 0x10001000000000001000100000000010001000000000001000100
abbrev q39G : Word := qGoal &&& q39M
abbrev q39W : List Word := projectDAGStock q39M qBase [3, 4, 6]
def q39F : Bound := (q39M, q39W, 4, q39G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q39Bin : BinLower q39M q39W q39G 4 := dagShiftLowerBin (width := 256) [qS28, qS29, qS1, qS22, qS19, qS4, qS5] q0Bin (by decide +kernel)
def q40M : Word := 0x100000001000000010000000100000100000001000000010000000100
abbrev q40G : Word := qGoal &&& q40M
abbrev q40W : List Word := projectDAGStock q40M qBase [3, 5, 6]
def q40F : Bound := (q40M, q40W, 3, q40G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Bin : BinLower q40M q40W q40G 3 := dagShiftLowerBin (width := 256) [qS28, qS2, qS32, qS31, qS9, qS26] q1Bin (by decide +kernel)
def q41M : Word := 0x50005000000000005000500000000000500050000000000050005
abbrev q41G : Word := qGoal &&& q41M
abbrev q41W : List Word := projectDAGStock q41M qBase [1, 4, 6, 7]
def q41F : Bound := (q41M, q41W, 7, q41G)
def q41E := unpackWitnesses q41W [66688, 336000, 622720, 884800]
abbrev q41N : List Word := normStock q41M q41W
def q41C : List Bound := [q4F, q2F, q6F, q7F]
def q41S : DagSample := (0x2010880500814020124020804124024020900120804424030080c0, 12)
def q41L : DagLinkList := dagExtractLinks 0x884420300789e02c01 0x68300504c3c8420c83234442044323304e320420303e020328183369433194236103311023010130000f 9 4 12 3 5
def q41D : Forest := fun i => decodeNode 3 15 0x10614131a19203e4064804c8078 i
def q41T := dagTraceTagsBin q41M 12 (dagTagBases q41N 0x63388f1f8f44 0xfb3cef3fef5d 12) 6 q41D
def q41St := dagTraceBin q41M q41N 6 q41D
def q41Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q41Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q41Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q41Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q41Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 7, 5, 4, 6] 0 i.val)
def q41Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 7, 4] 0 i.val)
def q41Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 7, 4] 0 i.val)
def q41Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 7, 5, 4, 6] 0 i.val)
def q41Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 7, 5, 6, 4] 0 i.val)
def q41Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 7, 5, 6, 4] 0 i.val)
def q41Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q41Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q41Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 7, 6] 0 i.val)
def q41Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 7, 6] 0 i.val)
def q41Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q41Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q41Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 1, 5, 4, 6] 0 i.val)
def q41Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 7, 1] 0 i.val)
def q41Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 7, 4] 0 i.val)
def q41Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 7, 5, 1, 6] 0 i.val)
def q41Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 1, 5, 6, 4] 0 i.val)
def q41Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 7, 5, 6, 1] 0 i.val)
def q41Mp11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q41Mi11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q41Mp12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 7, 5, 1, 6] 0 i.val)
def q41Mi12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 7, 4] 0 i.val)
def q41Mp13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q41Mi13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q41Mp14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 4, 5, 1, 6] 0 i.val)
def q41Mi14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 7, 1] 0 i.val)
def q41Mp15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 7, 5, 1, 4] 0 i.val)
def q41Mi15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 7, 5, 1, 4] 0 i.val)
def q41Mv := dagMoves ([([qS7], q41Mp0, q41Mi0), ([qS9], q41Mp1, q41Mi1), ([qS33, qS7], q41Mp2, q41Mi2), ([qS9, qS7], q41Mp3, q41Mi3), ([qS33], q41Mp4, q41Mi4), ([qS11], q41Mp5, q41Mi5), ([qS11, qS7], q41Mp6, q41Mi6), ([qS32, qS9], q41Mp7, q41Mi7), ([qS34, qS33, qS7], q41Mp8, q41Mi8), ([qS32, qS9, qS7], q41Mp9, q41Mi9), ([qS34, qS33], q41Mp10, q41Mi10), ([qS11, qS9], q41Mp11, q41Mi11), ([qS11, qS33, qS7], q41Mp12, q41Mi12), ([qS32], q41Mp13, q41Mi13), ([qS34, qS7], q41Mp14, q41Mi14), ([qS32, qS33], q41Mp15, q41Mi15)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41A : DagMovesOK q41M q41G 256 q41Mv := dagMovesOfCheck (by decide +kernel)
def q41NB : Nat → List Bound := dagNodeBounds q41C.toArray 0x16ac4a9105204 0x63e1e1 7 3 2
def q41Ck := dagCheckNodeBin q41M q41G q41NB 7 q41St q41Mv q41L q41S q41T
def q41RA (token : Nat) : Bool :=
  let s := rootState q41N 6 token
  !dagAllowedRootBin q41M q41E s.2.1 || dagLocalBin q41M q41G (dagKnownClosesBin q41G q41C) s ||
  dagRefBin q41M 7 q41St q41Mv (fun p tok => dagFindLink (q41L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41RB0 : treeBlock 0 16 q41RA = true := by decide +kernel
theorem q41R : dagCheckRootsBin q41M q41G (dagKnownClosesBin q41G q41C) q41E (dagRefBin q41M 7 q41St q41Mv (fun p tok => dagFindLink (q41L p) tok) 0) q41N 6 = true := q41RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41B0 : treeBlock 0 7 q41Ck = true := by decide +kernel
theorem q41Bk : treeBlock 0 7 q41Ck = true := q41B0
theorem q41K : KnownBin q41C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q7Bin) q6Bin) q2Bin) q4Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Bin : BinLower q41M q41W q41G 7 := by
  apply lowerDagBin _ _ _ _ q41A _ _ _ q41K _ (fun _ b hb => dagNodeBounds_mem b hb) q41R q41Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q41C.all (fun b => q41M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q42M : Word := 0xf0f0f0f0000
abbrev q42G : Word := qGoal &&& q42M
abbrev q42W : List Word := projectDAGStock q42M qBase [0, 1, 3, 4]
def q42E := unpackWitnesses q42W [17954, 275480, 545826, 806936]
abbrev q42N : List Word := normStock q42M q42W
def q42C : List Bound := [q28F, q26F, q31F]
def q42S : DagSample := (0x80a0441a0884c442308848442a0c06830120c0644021088842012088644412100a03028, 16)
def q42L : DagLinkList := dagExtractLinks 0x8888888179785c4a3a0e01 0x483c4820bc3eb4323c2e3422443c38303430284c2433903f88331821101f0813000f 8 3 11 4 1
def q42D : Forest := fun i => decodeNode 4 15 0x10343c306070c082614331042207c409880f0 i
def q42T := dagTraceTagsBin q42M 16 (dagTagBases q42N 0xcf1780eb39746b9c 0xd7d7abfbfc7eabb9 16) 5 q42D
def q42St := dagTraceBin q42M q42N 5 q42D
def q42Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q42Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q42Mv := dagMoves ([([qS1], q42Mp0, q42Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42A : DagMovesOK q42M q42G 256 q42Mv := dagMovesOfCheck (by decide +kernel)
def q42NB : Nat → List Bound := dagNodeBounds q42C.toArray 0x39ce7399ac5a3 0x10a4 5 2 2
def q42Ck := dagCheckNodeBin q42M q42G q42NB 10 q42St q42Mv q42L q42S q42T
def q42RA (token : Nat) : Bool :=
  let s := rootState q42N 5 token
  !dagAllowedRootBin q42M q42E s.2.1 || dagLocalBin q42M q42G (dagKnownClosesBin q42G q42C) s ||
  dagRefBin q42M 10 q42St q42Mv (fun p tok => dagFindLink (q42L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42RB0 : treeBlock 0 16 q42RA = true := by decide +kernel
theorem q42R : dagCheckRootsBin q42M q42G (dagKnownClosesBin q42G q42C) q42E (dagRefBin q42M 10 q42St q42Mv (fun p tok => dagFindLink (q42L p) tok) 0) q42N 5 = true := q42RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42B0 : treeBlock 0 10 q42Ck = true := by decide +kernel
theorem q42Bk : treeBlock 0 10 q42Ck = true := q42B0
theorem q42K : KnownBin q42C := (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q31Bin) q26Bin) q28Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Bin : BinLower q42M q42W q42G 6 := by
  apply lowerDagBin _ _ _ _ q42A _ _ _ q42K _ (fun _ b hb => dagNodeBounds_mem b hb) q42R q42Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q42C.all (fun b => q42M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q43M : Word := 0x5000500000000000500050000000000050005000000000005000500000000
abbrev q43G : Word := qGoal &&& q43M
abbrev q43W : List Word := projectDAGStock q43M qBase [1, 4, 6, 7]
def q43F : Bound := (q43M, q43W, 7, q43G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Bin : BinLower q43M q43W q43G 7 := dagShiftLowerBin (width := 256) [qS16] q41Bin (by decide +kernel)
def q44M : Word := 0xc0c00000303000000000000000000000c0c00000303
abbrev q44G : Word := qGoal &&& q44M
abbrev q44W : List Word := projectDAGStock q44M qBase [0, 1, 3, 7]
def q44F : Bound := (q44M, q44W, 7, q44G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Bin : BinLower q44M q44W q44G 7 := dagShiftLowerBin (width := 256) [qS20, qS35, qS18, qS12, qS0, qS5] q41Bin (by decide +kernel)
def q45M : Word := 0x30300000000030300000000000000000303000000000303
abbrev q45G : Word := qGoal &&& q45M
abbrev q45W : List Word := projectDAGStock q45M qBase [0, 3, 4, 7]
def q45F : Bound := (q45M, q45W, 7, q45G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45Bin : BinLower q45M q45W q45G 7 := dagShiftLowerBin (width := 256) [qS20, qS3, qS0, qS24, qS5] q41Bin (by decide +kernel)
def q46M : Word := 0x30300000000000000000000030300000303000000000000000000000303
abbrev q46G : Word := qGoal &&& q46M
abbrev q46W : List Word := projectDAGStock q46M qBase [0, 3, 5, 7]
def q46F : Bound := (q46M, q46W, 7, q46G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Bin : BinLower q46M q46W q46G 7 := dagShiftLowerBin (width := 256) [qS23, qS3, qS4, qS5] q41Bin (by decide +kernel)
def q47M : Word := 0xc030000000000000c030000000000000c030000000000000c03
abbrev q47G : Word := qGoal &&& q47M
abbrev q47W : List Word := projectDAGStock q47M qBase [0, 1, 6, 7]
def q47F : Bound := (q47M, q47W, 7, q47G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q47Bin : BinLower q47M q47W q47G 7 := dagShiftLowerBin (width := 256) [qS17, qS35, qS18, qS19, qS4] q41Bin (by decide +kernel)
def q48M : Word := 0xc000000030000000c000000030000000c000000030000000c00000003
abbrev q48G : Word := qGoal &&& q48M
abbrev q48W : List Word := projectDAGStock q48M qBase [0, 1, 6, 7]
def q48F : Bound := (q48M, q48W, 7, q48G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48Bin : BinLower q48M q48W q48G 7 := dagShiftLowerBin (width := 256) [qS20, qS35, qS18, qS19, qS4] q41Bin (by decide +kernel)
def q49M : Word := 0x3000003000000000300000300000000030000030000000003000003
abbrev q49G : Word := qGoal &&& q49M
abbrev q49W : List Word := projectDAGStock q49M qBase [0, 3, 6, 7]
def q49F : Bound := (q49M, q49W, 7, q49G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49Bin : BinLower q49M q49W q49G 7 := dagShiftLowerBin (width := 256) [qS21, qS3, qS4] q41Bin (by decide +kernel)
def q50M : Word := 0x3000000000003000300000000000300030000000000030003000000000003
abbrev q50G : Word := qGoal &&& q50M
abbrev q50W : List Word := projectDAGStock q50M qBase [0, 4, 6, 7]
def q50F : Bound := (q50M, q50W, 7, q50G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q50Bin : BinLower q50M q50W q50G 7 := dagShiftLowerBin (width := 256) [qS20, qS3] q41Bin (by decide +kernel)
def q51M : Word := 0x5050505000000000a0a0a0a
abbrev q51G : Word := qGoal &&& q51M
abbrev q51W : List Word := projectDAGStock q51M qBase [0, 1, 3, 4]
def q51F : Bound := (q51M, q51W, 6, q51G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q51Bin : BinLower q51M q51W q51G 6 := dagShiftLowerBin (width := 256) [qS23, qS3, qS22, qS4, qS36] q42Bin (by decide +kernel)
def q52M : Word := 0x5050000050500000a0a00000a0a
abbrev q52G : Word := qGoal &&& q52M
abbrev q52W : List Word := projectDAGStock q52M qBase [0, 1, 3, 5]
def q52F : Bound := (q52M, q52W, 6, q52G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q52Bin : BinLower q52M q52W q52G 6 := dagShiftLowerBin (width := 256) [qS23, qS25, qS1, qS0, qS24, qS36] q42Bin (by decide +kernel)
def q53M : Word := 0x5000500050005000a000a000a000a
abbrev q53G : Word := qGoal &&& q53M
abbrev q53W : List Word := projectDAGStock q53M qBase [0, 1, 4, 5]
def q53F : Bound := (q53M, q53W, 6, q53G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q53Bin : BinLower q53M q53W q53G 6 := dagShiftLowerBin (width := 256) [qS23, qS3, qS30, qS4, qS24, qS36] q42Bin (by decide +kernel)
def q54M : Word := 0x50005000500050000000000000000000a000a000a000a
abbrev q54G : Word := qGoal &&& q54M
abbrev q54W : List Word := projectDAGStock q54M qBase [0, 1, 4, 5]
def q54F : Bound := (q54M, q54W, 6, q54G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q54Bin : BinLower q54M q54W q54G 6 := dagShiftLowerBin (width := 256) [qS28, qS3, qS30, qS4, qS24, qS36] q42Bin (by decide +kernel)
def q55M : Word := 0x1010101010101010202020202020202
abbrev q55G : Word := qGoal &&& q55M
abbrev q55W : List Word := projectDAGStock q55M qBase [0, 3, 4, 5]
def q55F : Bound := (q55M, q55W, 6, q55G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q55Bin : BinLower q55M q55W q55G 6 := dagShiftLowerBin (width := 256) [qS23, qS25, qS1, qS11, qS12, qS0, qS24, qS36] q42Bin (by decide +kernel)
def q56M : Word := 0x500050005000500000000000000000500050005000500
abbrev q56G : Word := qGoal &&& q56M
abbrev q56W : List Word := projectDAGStock q56M qBase [1, 3, 4, 5]
def q56F : Bound := (q56M, q56W, 6, q56G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q56Bin : BinLower q56M q56W q56G 6 := dagShiftLowerBin (width := 256) [qS28, qS3, qS30, qS31, qS4, qS36] q42Bin (by decide +kernel)
def q57M : Word := 0x50005000000000005000500000000050005000000000005000500
abbrev q57G : Word := qGoal &&& q57M
abbrev q57W : List Word := projectDAGStock q57M qBase [1, 3, 4, 6]
def q57F : Bound := (q57M, q57W, 7, q57G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q57Bin : BinLower q57M q57W q57G 7 := dagShiftLowerBin (width := 256) [qS28, qS29, qS0, qS24, qS6, qS7] q41Bin (by decide +kernel)
def q58M : Word := 0x500000005000000050000000500000500000005000000050000000500
abbrev q58G : Word := qGoal &&& q58M
abbrev q58W : List Word := projectDAGStock q58M qBase [1, 3, 5, 6]
def q58F : Bound := (q58M, q58W, 6, q58G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q58Bin : BinLower q58M q58W q58G 6 := dagShiftLowerBin (width := 256) [qS28, qS3, qS30, qS31, qS8, qS9, qS36] q42Bin (by decide +kernel)
def q59M : Word := 0x1000100010001000100010001000101000100010001000100010001000100
abbrev q59G : Word := qGoal &&& q59M
abbrev q59W : List Word := projectDAGStock q59M qBase [3, 4, 5, 6]
def q59F : Bound := (q59M, q59W, 6, q59G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q59Bin : BinLower q59M q59W q59G 6 := dagShiftLowerBin (width := 256) [qS28, qS10, qS30, qS12, qS8, qS9, qS36] q42Bin (by decide +kernel)
def q60M : Word := 0x500050000000000050005000000000005000500000000000500050000
abbrev q60G : Word := qGoal &&& q60M
abbrev q60W : List Word := projectDAGStock q60M qBase [1, 4, 6, 7]
def q60F : Bound := (q60M, q60W, 7, q60G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q60Bin : BinLower q60M q60W q60G 7 := dagShiftLowerBin (width := 256) [qS20] q41Bin (by decide +kernel)
def q61M : Word := 0xf0f0f0f000000000f0f0f0f
abbrev q61G : Word := qGoal &&& q61M
abbrev q61W : List Word := projectDAGStock q61M qBase [0, 1, 3, 4, 6]
def q61F : Bound := (q61M, q61W, 7, q61G)
def q61E := unpackWitnesses q61W [37448, 300104, 537105, 831560, 1093656]
abbrev q61N : List Word := normStock q61M q61W
def q61C : List Bound := [q2F, q10F, q14F, q16F]
def q61S : DagSample := (0x14030500884c140b05024060b0c06806090184c30190c024141a08864220904024804108048804200824144a051080241010482050201402241, 26)
def q61L : DagLinkList := dagExtractLinks 0xe38e31341 0x8130e19d03f9066407c409801f 6 3 11 3 1
def q61D : Forest := fun i => decodeNode 3 14 0x26286640f902640f8 i
def q61T := dagTraceTagsBin q61M 26 (dagTagBases q61N 0x308436ec96f25f82073f1d277c4fffa88 0x369cf6ee26fe5e96379f9d937ebfffafd 26) 6 q61D
def q61St := dagTraceBin q61M q61N 6 q61D
def q61Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q61Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q61Mv := dagMoves ([([qS11], q61Mp0, q61Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61A : DagMovesOK q61M q61G 256 q61Mv := dagMovesOfCheck (by decide +kernel)
def q61NB : Nat → List Bound := dagNodeBounds q61C.toArray 0x4072a9084 0x9378 7 3 2
def q61Ck := dagCheckNodeBin q61M q61G q61NB 5 q61St q61Mv q61L q61S q61T
def q61RA (token : Nat) : Bool :=
  let s := rootState q61N 6 token
  !dagAllowedRootBin q61M q61E s.2.1 || dagLocalBin q61M q61G (dagKnownClosesBin q61G q61C) s ||
  dagRefBin q61M 5 q61St q61Mv (fun p tok => dagFindLink (q61L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61RB0 : treeBlock 0 32 q61RA = true := by decide +kernel
theorem q61R : dagCheckRootsBin q61M q61G (dagKnownClosesBin q61G q61C) q61E (dagRefBin q61M 5 q61St q61Mv (fun p tok => dagFindLink (q61L p) tok) 0) q61N 6 = true := q61RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61B0 : treeBlock 0 5 q61Ck = true := by decide +kernel
theorem q61Bk : treeBlock 0 5 q61Ck = true := q61B0
theorem q61K : KnownBin q61C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q16Bin) q14Bin) q10Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61Bin : BinLower q61M q61W q61G 7 := by
  apply lowerDagBin _ _ _ _ q61A _ _ _ q61K _ (fun _ b hb => dagNodeBounds_mem b hb) q61R q61Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q61C.all (fun b => q61M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q62M : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev q62G : Word := qGoal &&& q62M
abbrev q62W : List Word := projectDAGStock q62M qBase [0, 1, 3, 4, 7]
def q62F : Bound := (q62M, q62W, 8, q62G)
def q62E := unpackWitnesses q62W [66176, 328832, 594048, 860288, 1126424]
abbrev q62N : List Word := normStock q62M q62W
def q62C : List Bound := [q4F, q3F, q29F, q18F, q20F]
def q62S : DagSample := (0x24022910c26022130502c14090182c301a0182406130c064300905068221908824100940204201201209008201a040209042210088052080281010482090402402281, 30)
def q62L : DagLinkList := dagExtractLinks 0x1c0e070363b0d86c36165923543801 0x170b8980c430108701d1403224056422f474521087c1d0ca342906832880bc14130201f53c43270670d10c1a11e204fc2086480fc8819a202f420460807c08098001f 9 4 12 4 3
def q62D : Forest := fun i => decodeNode 4 16 0x85c90194015443e34323832204c203e2423101f1013101f0 i
def q62T := dagTraceTagsBin q62M 30 (dagTagBases q62N 0x28421ceee4b78f5f4103e3f0e93bfc47ffd108 0x2b4e7ceef137d75f4b1bf5f8ec9bfebfffdbbd 30) 7 q62D
def q62St := dagTraceBin q62M q62N 7 q62D
def q62Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q62Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q62Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q62Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q62Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 0, 2, 1, 3, 5, 6, 7] 0 i.val)
def q62Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 4, 0, 5, 6, 7] 0 i.val)
def q62Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q62Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q62Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q62Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q62Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 4, 0, 5, 6, 7] 0 i.val)
def q62Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 0, 2, 1, 3, 5, 6, 7] 0 i.val)
def q62Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def q62Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def q62Mv := dagMoves ([([qS11], q62Mp0, q62Mi0), ([qS3, qS4], q62Mp1, q62Mi1), ([qS10, qS11, qS4], q62Mp2, q62Mi2), ([qS1], q62Mp3, q62Mi3), ([qS1, qS11], q62Mp4, q62Mi4), ([qS3, qS22, qS4], q62Mp5, q62Mi5), ([qS10, qS22], q62Mp6, q62Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62A : DagMovesOK q62M q62G 256 q62Mv := dagMovesOfCheck (by decide +kernel)
def q62NB : Nat → List Bound := dagNodeBounds q62C.toArray 0x90907469685a5858432b1302 0x2304028140a041 8 3 3
def q62Ck := dagCheckNodeBin q62M q62G q62NB 12 q62St q62Mv q62L q62S q62T
def q62RA (token : Nat) : Bool :=
  let s := rootState q62N 7 token
  !dagAllowedRootBin q62M q62E s.2.1 || dagLocalBin q62M q62G (dagKnownClosesBin q62G q62C) s ||
  dagRefBin q62M 12 q62St q62Mv (fun p tok => dagFindLink (q62L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62RB0 : treeBlock 0 32 q62RA = true := by decide +kernel
theorem q62R : dagCheckRootsBin q62M q62G (dagKnownClosesBin q62G q62C) q62E (dagRefBin q62M 12 q62St q62Mv (fun p tok => dagFindLink (q62L p) tok) 0) q62N 7 = true := q62RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62B0 : treeBlock 0 12 q62Ck = true := by decide +kernel
theorem q62Bk : treeBlock 0 12 q62Ck = true := q62B0
theorem q62K : KnownBin q62C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q20Bin) q18Bin) q29Bin) q3Bin) q4Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62Bin : BinLower q62M q62W q62G 8 := by
  apply lowerDagBin _ _ _ _ q62A _ _ _ q62K _ (fun _ b hb => dagNodeBounds_mem b hb) q62R q62Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q62C.all (fun b => q62M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q63M : Word := 0x5050505050505050a0a0a0a0a0a0a0a
abbrev q63G : Word := qGoal &&& q63M
abbrev q63W : List Word := projectDAGStock q63M qBase [0, 1, 3, 4, 5]
def q63F : Bound := (q63M, q63W, 9, q63G)
def q63E := unpackWitnesses q63W [16992, 312416, 577632, 843872, 1101896]
abbrev q63N : List Word := normStock q63M q63W
def q63C : List Bound := [q27F, q34F, q51F, q52F, q53F, q25F, q55F, q30F, q33F, q36F]
def q63S : DagSample := (0x801320188c0420084c0650008640268201a080702414002312408480523014006520090822522402c227001928c029240a48009300c402290094090190198880210182c904a0182490580886422090188cc062018842231301c022210884c8042019080209301a00613201402250008849009241a0c021, 53)
def q63L : DagLinkList := dagExtractLinks 0x15100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054402a2015100a88054306a1035080a84054202a1015080a8405400a9f054f02a741539069c814e01a6e0d37029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a6e0537029b814dc0a681d2a2a93874903a421d172a8b814581a2a0d140689834442a1e150f02878143c0a1e050e0686834301a160d090a838541c0a0a15050282814140a0a050502820340c1a0605030281034041a000d000280014000a000500027f833fc09fe04ff027e853f019f414f70e7a073cc19e604f20679013c419e00cf00277833bc09de04ef0277033b419d614ea06738739429c80ce4027183364a9b204d8066b8335c09ae04d7026b0334849a404d2026901338499c04cd06660332c19940cca026501318498a0cc502620330c198604c302618130c098604c2066083304097e14bf025e072f009760cbb025d812dc496e04b60659092c8096404b20257092b4195a04ac0656012b0095804ac0255832ac095214a9025385294294a04a4065201290094414a00a4f05278093a0c9c064e01248a9220c9006480123c191c0c8c0a45832281914048906438521c090e04860642832101900247e0a3e051e828f014760a3a051c828e20c700637831b818ce3c640e308718018be0c581e2a8714838a20c4f0a2685128388e1c46062301114188a04440621051080880143f061e850f018760c390a18910c0185e0c2d0a15850a818520c251211850842842041f0a0e850701838041b060d03064182e1416060a0504828220c11020881044082204100608010400820040f060703034181a040d02060303008160c0b020503020280c140506020300c18040c02020101008080013fe09fe04ff007f60bfa05fd00fe807f403f905fc80fe017ee0bf605fa82fd017e60bea25f092f58b7926bbc35d896ea8775403a029cc8ee64071e538b11c28cdfc66f623780db59ad9c46ae834d29a116cc126582320318e08c60461082f93d7812b9c95c81ad735690ab14d58222b5315516a74d5206a8d0d40989c8f4da2a60352d0c94494904a393d1a888a4c43c5a1135021a80433ea61f014f19a774639a81c814dd9a6d8534a89a110c7a4610b2f4516848b286560d2a82144409f8a4c0f256291a448b86428d20c20f6407908398c1c420d240621c2d4f14c788f5c383e13e105d080f7c009c0001 0x38e44cf8c04cb8c03c38e01cb8c03cf8c01cb8c04c38a02cb8c04c38c02c38c03c38a04438a03c386850b76840776450780c42b7c84eb7684237c44e37644236c03db70029ae40213700192e4011389050780c50b78840386c5077ec40b7e45038705077ec40b76850784c4e77ec42b7884238444e37e44275603d76e0352f202135601d36e015384430384830ada05c382c4038105037e840b7f05037ec4037c45037c85037a05c6ecc40777050376850379050376c50374018372014370850370c50ada05c36e84036ec406ec44c2da83430c01030a02036c85030802036cc5036805cae2020756c4074e04c2f002070e04036a03470604036605c2da43c36402036442c368450b66448366450302430ae04202e403036305c36485c2e202036284cf6044eee044236243db6042eae042276004e6e004236203d36002e2e0022362c503000202fe02072a04c32a02c32001c2ee01071a03e6fc03231a01e2fc01236445c36245036485c362c5071403e6fa03231401e2fa0122f802036005071804c360c502e602035e05c35c03c35684034e04c34c03c34803cb3405033403034202c31c02034603cb4044eb3244234042e332422b3e04eb3004233e02e33002233c03cb3805035004c35a44c35842c356840704040356c4074c04c35444cb4a04eb360426ec44c35242c6ec44c2ec42c3524442ce010f50c4eb4cc4275083934c831b5044ef4c44235042e74c4222ce03a2ce01a2ce4303500403160302d401034e44034804c34403c34204c34c44034ec4034c84034a04c34884033c03c34683234444e34244231642d73e04c34001c73e04c33e01c33c04c2d401c31643c33a05c33a44c2d202033845c33444c32a05c31804c33885033644c32805c32605c33484232e04e32c04d32404c31e04531c04231602d73044c33242c32205c73044c33042c32005c32e03c32c44c32a43232803e32603d32403c3220353200322d201d31e44cb1a05c31403c31c44cb1a05c31a03c31844031644c31405430e43c2ec024b0245030843cae405031044030443c2f2040b0c45c31202c304830310c406e843c30e4286f004030a420b08450308430306420304430b0885030c43c30a84e30884230683e304832aea04eae20422f603e2f00322d443c2d242c302850ae0050302c5030045c3004502f842c2fe4422f403e2ee0322d201dafc45c2fa43cafc45c2fc43c2fa4542e642c2f845c2e643c2d002c2f602c2f60202f405c2ce42c6d002c6d044c2f2c402f043c6f0c402f04302ee45c2e80402ec4282ea05c2ea0502e8c402e602c2e643c2e48502e04502e4c502e245c2e24502e0c502de05c2dc05c2de03e2dc032ada05c2d603cada05c2da03c2d805c2d60542d443c2ce0402d004c2d443c2d245c2d00402ce44cec54606c50506b4c50ac48602c48402b4830aa24602a244029c4302ccc606c8c506b6c40ac88602c6850aa0840ab64606a045029c4402cd0516b6c422ca8502c48422aa44e2a2442a4805126c03d15e0212900190ee0116c90526bec5e6b6c522c88522c28402be45e2b645255c0415c803d68603515c0211c801d286015ac90512cac502c8c42aa884eaa08422a844e2a0442a6a05d26a03da8e0298ec02128e0190ec0112c70522c4c522c2c40aa08522bc45e2b44525f804d26803d1180211c601d2840152c0c492be8322bc432a7005d2ba0492b804515a011ab70512b6c422b48422b244e29c4421580211c201d2b00192ae0150d80112acc5e2aa8522a84525600412a60392a403526602d6a10522a2c522a085229e45e29c45226403d1b801d29a0192980150d401129645c29444c29243c28842c290c5228e85226243d28c05e28a04e28801e286c4228484228245228044215602127801d27e06c27c04c27a03c27802ca7486022283c24e06ca7505d676c49658c4166e83227644925844126e42125005d5a003e54a0322220211a001e14a012a74c6c220c4ca5084ca46060e6d05166cc42a7485d67284e5c284227483da6c45126c4312724291c2421a2005159e04e54804222003119e01e148012a6cc6026a84025c83827044c2584381c2430a4c06c14202019201c8ea0106690505c6c502688401c68302644402544381b843059805c19802c18801c11601026ec5e26cc5265ec4e5c8c4226a85226884226083a26644e2644420e243a24c05ea440525a204e54c04214e0211400202620190e20112608401b48300e244019602c25ec4225c85225a45e25845225644e2544421b442d24a05ea4205259c04e5460421a802d1b483825245c1a444c13e020a50c5825086ca1e06021e030a1f05de4cc51e4ac49592c41a4e84a64c83224e45d64a43ed9243221e42da4c051a4a04919204124c02124a01999201164905124885124045123e45058044e53a44222043d18042e13a42223c05d61004e4ee04222003d21002e0ee02224906024446c13843017a42c8e842023806c0ec03020a02c0d802057e45c17e43c17042c11442022e06c60e05c20e03c20602c0d4020220c50a1c46021e43ca1d05d644c51642c4957ac4124684224445124244917a44160403e4ea03221e02d20401e0ea012241060a1c86c21c84c22a44ca2a06c23ec50a1c45de0244ece8442a3a43da0242e8e842223a05d60204e4e804221c03d20202e0e802223cc60220c5023a460a28060a2905d638c51636c4960ac4123845123644920a441a2a05156e03e53603216e01e136012234c5256c44e53444221a43d16c42e13442261404e5fe04221a03d21402e1fe022632c4b630c4323244b23044322e43358203f56a03e53c03353203218201f16a01e13c01313201256844e53044221843d16842e13042222c05da2605c61204e5fc04221803d21603c21202e1fc022a2846c22c06c22a04c56644e52e44216642e12e422a2805da2605c62404e4d804222803d22603c22402e0d8022222c5e220c5221e45e21c45256244e52a44216242e12a42221a05d21805521605460004e4e204220002e0e202212843021406c21206420004c0d0030210c5220e84220c45e20a45220844e2064420d042d20405e20205256404e52c04220003d0f00211fe46c1fc4640e244c0d043c1fa06c0f604c9da46c1ee45c1da44c1d643c1c243098006018004019e03c1660301f88501f445c1c84401d243c1b84305520501a204c19a03c4e60309f90521f8c419d085e9c68521f684d1d083e1c68320bc42a99805e97e0521b204d1ae04c19803e17e0320bc0111f68500bc8405e24501ac05c9f50529f2c5e9d2c525e2c4d1f48411f28391d283199005e9780521b004d19002e1780221f08429de45e9ce4521de43e1ce4320ce42d98e05e97605218e03e1760320ce0219ecc4f9eac431ee8431ec83b1ea8339a604f98c04e9840439740421a602f18c02e1840231740229dc45e9cc4521e644d5e044c1dc43e1cc4320cc42d1e842c98a05e97205218a03e1720320cc0215e285c1e645c5b043c9e445e9b84525e244d5e044c1e443e1b84321e242d1e042c98805e97005218803e1700321de45c1dc4541b64400ca42c18604c1dac521d885e1d68521d484e1d28421b683d1d044299405e97c0521aa04e5540421a403d0ca0111ce85c1cc8541b684c0c883c1ca45c1a843c1c8c421c68421c445e1c24521c044e1be44d1bc44c1ba4451b84421b643d1b442d99205e97a05259a04e5440420c80211b28505b08481b045c4c60500c6020daac5e99ac524c6c4d5aa83919a8311ae4405ac43a9aa05ed9a0521ac04d1aa02e59a0220c601d1a88381a645c1a444c1620400c20201a2c421a085e19e85219c84e19a84216283d19844219642a19405e19205219004e18e04d18c04c18a04518804218603d0c201d18485c16244c0c043018206c180c5217e84217c45e17a45217844e17644d17444c1724451704420c042d16e05e16c05d16a05c16805516605216404e4e604216203d95e86015e84015883093a46013a44014843c12e4308ee0600ee04010603c0d803015c84016083855045014c44c14443c4e443051805010a04c10203c0d403015ec5215cc4215a85e15885294245e93845215244e15044214e43d14043c0c842d15642590005e8ec05212204e11804210e03d0c802d4c44500c642c4bc050954c5e944c524c4c4d1548391448319524521524228fa05e8e605211c0410fa02e0e60220c601d4c485c0c483c11a43c51a05cd51052550c41950852150832cf845ece44524c444d4f843e4e443252642d8f805e8e405212604d0f803e0e40320c402d14e8400c883012a4400c242c0e204014cc4214a85e14885214684e14484212a83d14245214043013e4228fe05e8ea05212004e1160420f40310c201d12a84c0c083c13c46c0f043c0f604c13ac5213885213645e13445d13245c13045512e45212c44e4e444212a43d12842d8fc05e8e805211e04e11404210c03d0c002d1264505100500be02c924c5e902c52510c4d12483910283192245212242292005e91e05251a04112002e11e0220be01d11c85c51045c0bc43c11a03cd19052518c4191885211883291645e9144524bc44d11643e1144320bc42d91205e8d405251004d11203e0d403211002d10e8400c883010c4400d204010ac4210885e10685210484e1028420d283d1004520fe05e0fc0520fa04e0f80420f60310f484c0d244c0f206c0f003c0eec520ec8520ea45e0e84520e644e0e44420e243d0e005e0de05d0dc05c0da0550d80520d604e0d40420d203d0d002d8ca85e8c88520ce84d0cc8450ca83e0c88328c245e8c04520c644e0c44420c243e0c04320be04e0bc042cb70514b6c424aa8428b64510ba4430b64310aa42188205145e04f43604308203109402d06802105e01f036013cb10520bac534b0c418b08520b08328a44520a443289005f87e05345a04d09003f07e03305a02d04c01d01a0110b90530b6c520b4c420b28520b08420ae45e0ac4530aa4520a844e0a64430a444289205f88005345c04f43404308e03d0320210a201f04401d0a001909e01509c01301201149305348ec4209a85f09885e09685309485248c84f48a84e48884344484206683d09245309044308e43108c42b08a42908842304442108605f08405e87c05387a05243e04f43c04e42804342604206603103e01f03c01e028013026012481053082c5208085307e84307c45f07a45e07845307645243a44f43844e42444342244206643d03a42f03842e02442302242207405f07205e07005d06e05c06c05506a05306805246404f46204e46004341204206603d06402f06202e06002301202285d05305ec5305cc4305a84284a45f84845e84645384445205844f05644e05444d05244c05044504e44304c44204a43f04843e04643304443201042d83e05f83c05e83a05383805204204f04004e43004342e04203e03f03c03e03a033038032010021835053036c53034c4383285203283282845f82645e82445382245203044f02e44e02c44302a44202843f02643e02443302243201042d81805f81605e81405381205202004f01e04e01c04301a04201803f01603e01403301203201002dc0ac4300e84340a83380a44300c43300a42380804f80604340403f40203300802f00602300401f00201300001f 17 6 13 9 2
def q63D : Forest := fun i => decodeNode 9 22 0xe6480798e01e62e0a16582858d0615f6205760a15c62056d0a15502e5520a1516285440314f00a53d8a14862050d8a13601a4c88a1272284990b91062843d8a10202e3fc078ff22639c858e7620390898e222236c080d6620335080cd026329080c941931c89cc722131c038c600e314098c42263090a0bf2262f9084bb2162e8858b901e2e0898b72192d807cb601ead8078b601aad8064b62262d4898b401e2d0880b32262c80a8b20162b1880a921429c878a2427285084a141f285064a16282748a09c2212688789822a2588b8950102440b8906202348608c22e22c850820282018807d21e1e58a0772281d98a07501f1bc0646f01e1b40b86b02a1a88786222e1840806022617e0a25c6281698845a8291658a459620165892584191608645802496008a58621159084562271580325600a9598bc554291548a45501c95406a5562914d0a45322f14c8a45300c94c02a5322e1488985221e1498a4514291440bc5102714403c51621141084502291408845003613c0984f01e13c0584f22493507a4b21492c8984a62f1218a448429121084482271208844800c921080476211190a44622f1188a4462271188844622e1150d84422e90c0424300c90e0c0414210f88a23e2248fa0c03d6280f18c03b2300ec8a23a2248e98a4392258e0886382198e00d8360260d807a3501e0d405c3562f0d18a43422f0d08a43402e8d00aa3402a0d00d8330320cd8a4324210c88bc322290c889c322210c80bc320290c807a322360c48c8310360c58822e4280b50822c41c8b10842b4218a90762a4198a88582922e0a087c2721689c8582722e0988a8266290950bc2542909509c254210948842542e0910a82422e0918842342108c8bc2322908c89c2322688c8982322288c8842321e88c85a234280888b82222008409a210170850702022e0808982062107d0bc1f42907d09c1f42107c8841f21507c0bc1f02907c09c1f02687c0981f02287c0841f01e87d0b81e0360798a41d4210748bc1d22907489c1d2268748981d2228748841d02f0740ba1d02e0740aa1d02907409c1d01e8750701b6290698841a42f0690a41a21286907218211061064164200558841442f0510a41442705108414229050860142110508d8136290490a41222f0488ba1222e0488aa1222904889c1221e84885a122280450721021104005c100110410b80f01e03d0640e21f0388640e01f03805a0e4200348800d6210310bc0c42903109c0c4210308a40c02f0300a40c0270300840c0188310980b03602c0780b6290290a40a22f0288a40a2270288840a21e8280bc0a02e8280b80a02a8280a40a0270280840a01e82805a0a42682508a0941f025064092270248840921f024864090270240840962981e0a606629019884064290190840622f0188a60622901889c062218188840600f8180320600a8180260642f8150bc054298150a40522981488605218814856052148148460502f8140bc056290110a6044218108be0422f0108a6042290100be0402f0100ba0402e0100aa040298100a40401e81005e040170100460462980d8860342100c89e0322700c89a0322600c88a0322180c8840321f80c87c0321980c8640302780c09c0301f80c07c0301980c064036298098860241900889e022270088860222100887e0221f0088660221900809e020270080860202100807e0201f0080660201900805a024218048660121180405e0101180403e0100980403e00 i
def q63T := dagTraceTagsBin q63M 53 (dagTagBases q63N 0x1fe85fd3cf1bff8ffa1581ff3cb188af4f9e5e3ef13f499f81ee928609f5aed94d 0x1effbdfd5d7dbfffafbbdd7fffcffffafffce9fbf7fefdbffdbefc3c4761aaedb58 53) 8 q63D
def q63St := dagTraceBin q63M q63N 8 q63D
def q63Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q63Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q63Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q63Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q63Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q63Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q63Mv := dagMoves ([([qS0], q63Mp0, q63Mi0), ([qS11], q63Mp1, q63Mi1), ([qS11, qS0], q63Mp2, q63Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63A : DagMovesOK q63M q63G 256 q63Mv := dagMovesOfCheck (by decide +kernel)
def q63NB : Nat → List Bound := dagNodeBounds q63C.toArray 0xf20f20f20f20f19f18f18f18f11f10f10f10f09f08f08f01ef9ef1ef0ee9ee8ee1ed9ed8ed8ed8ed8ed8ed1ed0ed0ed0ed0ec9ec8ec8ec8ec1eb9eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb8eb1eb0eb0eb0eb0eb0ea9ea8ea8ea8ea8ea8ea8ea8ea1e99e98e91e90e90e90e90e89e81e79e78e78e78e78e78e78e71e69e61e59e4ae48e41e40e32e30e30e29e28e21e19e11e10e10e09e08e01e00df9df8df1de9de8de8de1de0de0dd9dd1dc9dc1dc0db9db1da9da1d99d98d98d91d89d81d80d79d78d78d78d6ad5ad58d58d51d50d49d41d39d38d38d31d29d28d21d19d11d10d09d01cf9cf8cf1ce9ce1cd9cd1cc9cc1cc0cc0cb9cb1ca9ca1ca0ca0c99c91c89c81c79c71c69c61c60c59c51c50c50c50c50c42c40c40c39c38c31c29c21c19c11c09c01c00c00bf9bf1bf0be9be8be1be0bd9bd8bd8bd8bd8bd1bc9bc8bc1bb9bb1bb0ba9ba8ba1ba0ba0ba0b99b91b89b81b79b71b70b69b61b59b58b51b42b39b31b30b30b22b19b11b09af3ae9ae1ae0ad9ad1ad0ad0ad0ad0ad0ad0ac9ac8ac8ac8ac8ac1ac0ac0ac0ac0ac0ac0ab2ab0aa9aa8a9aa91a89a81a79a71a69a61a52a49a41a32a29a28a28a21a19a039f99f19e29e09e09d99d89d89d19c99c19b99aa9a199299098998198097997196996896896195995195095094993a9389319299219129099089018f28f08e98e88e88e88e88e18d98d18c98c18c08b28a98a189989188988186485283b81c7fc7e37cb7b378d77375b73572270b6f36e26d26bb6aa69367b66364b63a61c6035f25e25d95d15bb5aa59a59158957a5555345144fb4f14e24d94ca4ac49347b47146945a4354143f43db3d13c23b239437b35534934132b3132fb2e32cb2b329b28a27a26a25a24321d2031eb1da1c31b219b18a16c15312d11a0fc0dc0b509406d045024004 0x5011011110063004021114005015100900119110001701801000110100241420117171111021211011111112103171801303000210800000000000430630206113362300643210140505463240654122243210400440010221020636366600113110101100001000440032109525185107501350105751725011058508351050105015516160131301617210512123412425313117620313111314320143214123421101112301221543180206321063206032630010033012305325100040362364532530140850340402020532645326124324041020210032603635325014034212630325106423634214263064326432 12 3 4
def q63Ck := dagCheckNodeBin q63M q63G q63NB 456 q63St q63Mv q63L q63S q63T
def q63RA (token : Nat) : Bool :=
  let s := rootState q63N 8 token
  !dagAllowedRootBin q63M q63E s.2.1 || dagLocalBin q63M q63G (dagKnownClosesBin q63G q63C) s ||
  dagRefBin q63M 456 q63St q63Mv (fun p tok => dagFindLink (q63L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63RB0 : treeBlock 0 32 q63RA = true := by decide +kernel
theorem q63R : dagCheckRootsBin q63M q63G (dagKnownClosesBin q63G q63C) q63E (dagRefBin q63M 456 q63St q63Mv (fun p tok => dagFindLink (q63L p) tok) 0) q63N 8 = true := q63RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B0 : treeBlock 0 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B16 : treeBlock 16 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B32 : treeBlock 32 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B48 : treeBlock 48 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B64 : treeBlock 64 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B80 : treeBlock 80 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B96 : treeBlock 96 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B112 : treeBlock 112 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B128 : treeBlock 128 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B144 : treeBlock 144 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B160 : treeBlock 160 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B176 : treeBlock 176 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B192 : treeBlock 192 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B208 : treeBlock 208 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B224 : treeBlock 224 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B240 : treeBlock 240 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B256 : treeBlock 256 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B272 : treeBlock 272 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B288 : treeBlock 288 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B304 : treeBlock 304 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B320 : treeBlock 320 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B336 : treeBlock 336 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B352 : treeBlock 352 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B368 : treeBlock 368 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B384 : treeBlock 384 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B400 : treeBlock 400 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B416 : treeBlock 416 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B432 : treeBlock 432 16 q63Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63B448 : treeBlock 448 8 q63Ck = true := by decide +kernel
theorem q63Bk : treeBlock 0 456 q63Ck = true := (@treeBlock_merge 0 240 216 q63Ck (@treeBlock_merge 0 128 112 q63Ck (@treeBlock_merge 0 64 64 q63Ck (@treeBlock_merge 0 32 32 q63Ck (@treeBlock_merge 0 16 16 q63Ck q63B0 q63B16) (@treeBlock_merge 32 16 16 q63Ck q63B32 q63B48)) (@treeBlock_merge 64 32 32 q63Ck (@treeBlock_merge 64 16 16 q63Ck q63B64 q63B80) (@treeBlock_merge 96 16 16 q63Ck q63B96 q63B112))) (@treeBlock_merge 128 64 48 q63Ck (@treeBlock_merge 128 32 32 q63Ck (@treeBlock_merge 128 16 16 q63Ck q63B128 q63B144) (@treeBlock_merge 160 16 16 q63Ck q63B160 q63B176)) (@treeBlock_merge 192 32 16 q63Ck (@treeBlock_merge 192 16 16 q63Ck q63B192 q63B208) q63B224))) (@treeBlock_merge 240 112 104 q63Ck (@treeBlock_merge 240 64 48 q63Ck (@treeBlock_merge 240 32 32 q63Ck (@treeBlock_merge 240 16 16 q63Ck q63B240 q63B256) (@treeBlock_merge 272 16 16 q63Ck q63B272 q63B288)) (@treeBlock_merge 304 32 16 q63Ck (@treeBlock_merge 304 16 16 q63Ck q63B304 q63B320) q63B336)) (@treeBlock_merge 352 64 40 q63Ck (@treeBlock_merge 352 32 32 q63Ck (@treeBlock_merge 352 16 16 q63Ck q63B352 q63B368) (@treeBlock_merge 384 16 16 q63Ck q63B384 q63B400)) (@treeBlock_merge 416 32 8 q63Ck (@treeBlock_merge 416 16 16 q63Ck q63B416 q63B432) q63B448))))
theorem q63K : KnownBin q63C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q36Bin) q33Bin) q30Bin) q55Bin) q25Bin) q53Bin) q52Bin) q51Bin) q34Bin) q27Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63Bin : BinLower q63M q63W q63G 9 := by
  apply lowerDagBin _ _ _ _ q63A _ _ _ q63K _ (fun _ b hb => dagNodeBounds_mem b hb) q63R q63Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q63C.all (fun b => q63M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q64M : Word := 0x5000500050005000500050005000505000500050005000500050005000500
abbrev q64G : Word := qGoal &&& q64M
abbrev q64W : List Word := projectDAGStock q64M qBase [1, 3, 4, 5, 6]
def q64F : Bound := (q64M, q64W, 9, q64G)
def q64E := unpackWitnesses q64W [83104, 360520, 614560, 839752, 1163424]
abbrev q64N : List Word := normStock q64M q64W
def q64C : List Bound := [q10F, q58F, q59F, q56F, q32F, q57F, q35F, q40F, q37F, q38F, q39F]
def q64S : DagSample := (0xc24900c20530900d0401610092500a81058500e010c0501a0142a5028814280c0e140b00c0a0904a241603058503809068240a0301a4020814820506900900c24010280512940284030090c0, 34)
def q64L : DagLinkList := dagExtractLinks 0x3460d183460d183460d00f3e1cf833c1cf033c0ce873a0ce833a0ce07380ce03361cd83360cd83360cd83360cd83341cd03340cd03340cd03340cd03340cd03340cd03340cd03321cc83320cc07300cc03300cc032a3c90f221c8071e1c41f0c2c3030c0c287081c203042c087001bd96ee4b992e03b786d83b586d22b406ce1b28ac24af8abc1ae0ab23aa92a43a712963a40e8e1a20e823a0067a39b9a6c1998e587929e44390864208f8a3c18e863628d063218c06265880e1e1870616385061028385fc97e85f817d09ec47911e027421c657181ba66c15a656791793592952952154234f0d26b43b10453f10ea936a0c0d2e10a69279084d1a384af0f1c17300a8001 0x72444052443012442092244c92204c12644c122424122428524040124430124c4092204c32003c12002c92204c32203c12202c12202012004412002071e0496d604111c03151e0294d602111e0190d601111a4308c205c11803011f0501164308c205c11403011203011d0508f24502f24404d04300d042090845c11a4482f04300f04208ee4502ee4400ee4300c442031844c11843c11642c11642c11405c31204c11203c11002c2ec84010e44010ec402ea44010c05c10a02c0c24248fc0502fc0401080309000501060201040200c24381020208fe0502fe0406d403010883850645c10644c10243c106c4210484e1028424fa4506d24400f24304d60504fc45c0f84300f04204f64500f64400ee4301004500fe4424e604e4d4042100c5c0fe8380fc44c0f48400fb0500f6840ad24500f884e0f68426e444e6d24424e404e4d20420f48400f4c400d883c2d804c4f28500f28400ee8308d00502d00400e003c0c40300f2c420f084e0ee8420ec4314de04e4d00420e803d0ecc400ea43c0dc04c0e84300e88402c00400e20200e00200e40500de0200e64480e44502d84400e284e0e08422c083d0de4420dc0312c044c0da05c0d803c0da4300d84300d70500d24500d04300d48482d30500d28500ca05c2d0c420d08420ce04e0cc04d0c804c0c60450c40422c003d0c002d0ce0200cc4300ca0210c80200c64308c205c2be04c0be02c0c44308c205c2c204c0c202c0c04300be0540bd0508840512840410a80314b202944e0210b201904e01189205d0ba0492820310a60210820118800512800410a40310800210b801903c0112b445c0b644c0b443c0ae42c0a20402b30520b28520a04310b005e0ae01e09e4400ac06c2aa05c0aa03c2a90520a8c520a685e0a485288845e86e45227244126c44007243106c4300a242e0a042909e42204842104642029a04109a03109c02909402149ac5209ac4286a85226a84249845209844249605e49405209604e09404209284849046c09045c08c44c08a43c87a06027a05064c04008803009105208ec5e08cc5287e05208602008ac4387c04227c032088c4348644e08643e48486008485008084087646027645064a44006e43084e06024e05006004c03c04008505208285e08085247a45e47645207844107444007243106c43045e05e44e05206804d07ec5e07c83807a45245c05e44c052078c5007084005043c25005c27705207685207484065a45e64a45226642d45a05e44a05206604d472c52072c4247085207084245805e44805205804e04804206ec4346c84206c83246a44306a43346404f45604e45404344604206403f05603e05403304603206885006645006443023a050062c5e060c5223ac4d05e45205c05e05a05225004105802105602005484023a45c05206c05003c24f05204e85204c45e04a45204843104643004405e04205d04005c03e05503c05223a04d03a02d23905203885203645e03445303245282605f81e05321c04102a03101c02103001f02e01902c01300a01162ac4342a84302a83382044e81444381244222043e21443321243202042e01442301242282804322803302802302705342445e02444e02243c81a05221a04202003001f05341c85201c84241a45e41845341645201a44e01844301644201443101243041005f40e05e40c05340a05201004f00e04e00c04300a042608c4340844300843380404f80204320403f20203300602100401f00201300001f 14 5 13 8 3
def q64D : Forest := fun i => decodeNode 8 21 0x22644b101a4040c4020608282d414154890a843c5221628817140078a002c4f6202681712c05896838456212221391108488c5c3e41c1f1130fa0a07884e3b4211db100e58846e84e374211bb100d88786c84033224179140b909c588422c2211600c4b086054430298281421209d0a04c842240101190c08804242020212181010c07c0583e4301e02a0f414074092380191a2260c90f0650a43005e1800f0c01b05c0782ec521642f0b21485885c2c429162110b00a4598842a442150270a810855090290521362f09b1484d88624c431121f08c1483d0bc1e8520f62f0720e0388a41cc500d42906210031884168420b6218520c82886614850092280490c0258bc10c5208229040178200a410021080100421001c0d80e03c07429031178188a40c43106218030178180ba0c05c0602a8301481805a0c8520522f02914c148a40a01f0500c82804c1506608023048298191380c87806030038298121080889c04443022210110c4088600404f0202701010c08084044330101080807c040260201f00 i
def q64T := dagTraceTagsBin q64M 34 (dagTagBases q64N 0x679ef877627ccec7ff501c7eb869f83fd02edbdc9c 0x37faffe777ffd6ef7ff55bdffbffff99ffa855bddb9 34) 8 q64D
def q64St := dagTraceBin q64M q64N 8 q64D
def q64Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q64Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q64Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q64Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q64Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q64Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q64Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q64Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q64Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q64Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q64Mv := dagMoves ([([qS9], q64Mp0, q64Mi0), ([qS11], q64Mp1, q64Mi1), ([qS32, qS9], q64Mp2, q64Mi2), ([qS11, qS9], q64Mp3, q64Mi3), ([qS32], q64Mp4, q64Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64A : DagMovesOK q64M q64G 256 q64Mv := dagMovesOfCheck (by decide +kernel)
def q64NB : Nat → List Bound := dagNodeBounds q64C.toArray 0xe00e00e00e00e00de2de0de0de0dd1dd0dd0db2db0db0db0db0db0db0db0db0db0db0db0db0da1da0da0da0d91d90d90d90d90d81d71d61d51d50d50d41d40d31d30d30d30d30d30d30d30d30d30d30cf4cf0ce1cd1cc1cb1cb0ca1c91c81c62c51c41c31c30c12c10be3bc2ba2b91b90b81b80b80b62b33b03af1af0ae1ae0ab3ab0a83a80a44a22a119f29c39939819719529419319219209119018c48b18b08a18918818718618338308218118108108017a67647246a86736436045b55655154d44944544143c53843443042c42842532141e31951360e5095045004 0x143404421202625135346234210033014040402210140130701035405013013144019046001212212013202262130250865421250673867820613534625626302401321430154072130210321031407650416130501350132130210340125312616135a6021352513052130521302135 12 4 4
def q64Ck := dagCheckNodeBin q64M q64G q64NB 148 q64St q64Mv q64L q64S q64T
def q64RA (token : Nat) : Bool :=
  let s := rootState q64N 8 token
  !dagAllowedRootBin q64M q64E s.2.1 || dagLocalBin q64M q64G (dagKnownClosesBin q64G q64C) s ||
  dagRefBin q64M 148 q64St q64Mv (fun p tok => dagFindLink (q64L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64RB0 : treeBlock 0 32 q64RA = true := by decide +kernel
theorem q64R : dagCheckRootsBin q64M q64G (dagKnownClosesBin q64G q64C) q64E (dagRefBin q64M 148 q64St q64Mv (fun p tok => dagFindLink (q64L p) tok) 0) q64N 8 = true := q64RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B0 : treeBlock 0 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B16 : treeBlock 16 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B32 : treeBlock 32 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B48 : treeBlock 48 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B64 : treeBlock 64 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B80 : treeBlock 80 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B96 : treeBlock 96 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B112 : treeBlock 112 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B128 : treeBlock 128 16 q64Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64B144 : treeBlock 144 4 q64Ck = true := by decide +kernel
theorem q64Bk : treeBlock 0 148 q64Ck = true := (@treeBlock_merge 0 80 68 q64Ck (@treeBlock_merge 0 48 32 q64Ck (@treeBlock_merge 0 32 16 q64Ck (@treeBlock_merge 0 16 16 q64Ck q64B0 q64B16) q64B32) (@treeBlock_merge 48 16 16 q64Ck q64B48 q64B64)) (@treeBlock_merge 80 48 20 q64Ck (@treeBlock_merge 80 32 16 q64Ck (@treeBlock_merge 80 16 16 q64Ck q64B80 q64B96) q64B112) (@treeBlock_merge 128 16 4 q64Ck q64B128 q64B144)))
theorem q64K : KnownBin q64C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q39Bin) q38Bin) q37Bin) q40Bin) q35Bin) q57Bin) q32Bin) q56Bin) q59Bin) q58Bin) q10Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64Bin : BinLower q64M q64W q64G 9 := by
  apply lowerDagBin _ _ _ _ q64A _ _ _ q64K _ (fun _ b hb => dagNodeBounds_mem b hb) q64R q64Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q64C.all (fun b => q64M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q65M : Word := 0xf0f00000f0f00000f0f00000f0f
abbrev q65G : Word := qGoal &&& q65M
abbrev q65W : List Word := projectDAGStock q65M qBase [0, 1, 3, 5, 6]
def q65F : Bound := (q65M, q65W, 7, q65G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q65Bin : BinLower q65M q65W q65G 7 := dagShiftLowerBin (width := 256) [qS37, qS22, qS24] q61Bin (by decide +kernel)
def q66M : Word := 0xf000f000f000f000f000f000f000f
abbrev q66G : Word := qGoal &&& q66M
abbrev q66W : List Word := projectDAGStock q66M qBase [0, 1, 4, 5, 6]
def q66F : Bound := (q66M, q66W, 7, q66G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q66Bin : BinLower q66M q66W q66G 7 := dagShiftLowerBin (width := 256) [qS0] q61Bin (by decide +kernel)
def q67M : Word := 0x3030303030303030303030303030303
abbrev q67G : Word := qGoal &&& q67M
abbrev q67W : List Word := projectDAGStock q67M qBase [0, 3, 4, 5, 6]
def q67F : Bound := (q67M, q67W, 7, q67G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67Bin : BinLower q67M q67W q67G 7 := dagShiftLowerBin (width := 256) [qS37, qS22, qS19, qS4, qS24] q61Bin (by decide +kernel)
def q68M : Word := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev q68G : Word := qGoal &&& q68M
abbrev q68W : List Word := projectDAGStock q68M qBase [0, 1, 4, 5, 7]
def q68F : Bound := (q68M, q68W, 7, q68G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68Bin : BinLower q68M q68W q68G 7 := dagShiftLowerBin (width := 256) [qS0, qS7] q61Bin (by decide +kernel)
def q69M : Word := 0x50505050505050500000000000000000505050505050505
abbrev q69G : Word := qGoal &&& q69M
abbrev q69W : List Word := projectDAGStock q69M qBase [1, 3, 4, 5, 7]
def q69F : Bound := (q69M, q69W, 7, q69G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69Bin : BinLower q69M q69W q69G 7 := dagShiftLowerBin (width := 256) [qS1, qS19, qS0, qS7] q61Bin (by decide +kernel)
def q70M : Word := 0x50500000505000005050000050500000505000005050000050500000505
abbrev q70G : Word := qGoal &&& q70M
abbrev q70W : List Word := projectDAGStock q70M qBase [1, 3, 5, 6, 7]
def q70F : Bound := (q70M, q70W, 7, q70G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70Bin : BinLower q70M q70W q70G 7 := dagShiftLowerBin (width := 256) [qS1, qS19, qS0, qS9, qS7] q61Bin (by decide +kernel)
def q71M : Word := 0x101010101010101010101010101010101010101010101010101010101010101
abbrev q71G : Word := qGoal &&& q71M
abbrev q71W : List Word := projectDAGStock q71M qBase [3, 4, 5, 6, 7]
def q71F : Bound := (q71M, q71W, 7, q71G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71Bin : BinLower q71M q71W q71G 7 := dagShiftLowerBin (width := 256) [qS1, qS11, qS19, qS0, qS9, qS5, qS7] q61Bin (by decide +kernel)
def q72M : Word := 0xf0f0f0f00000000000000000f0f0f0f
abbrev q72G : Word := qGoal &&& q72M
abbrev q72W : List Word := projectDAGStock q72M qBase [0, 1, 3, 4, 5]
def q72F : Bound := (q72M, q72W, 8, q72G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q72Bin : BinLower q72M q72W q72G 8 := dagShiftLowerBin (width := 256) [qS23, qS5, qS7] q62Bin (by decide +kernel)
def q73M : Word := 0xf0f0f0f000000000000000000000000000000000f0f0f0f
abbrev q73G : Word := qGoal &&& q73M
abbrev q73W : List Word := projectDAGStock q73M qBase [0, 1, 3, 4, 5]
def q73F : Bound := (q73M, q73W, 8, q73G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q73Bin : BinLower q73M q73W q73G 8 := dagShiftLowerBin (width := 256) [qS28, qS5, qS7] q62Bin (by decide +kernel)
def q74M : Word := 0xf000f000f000f00000f000f000f000f
abbrev q74G : Word := qGoal &&& q74M
abbrev q74W : List Word := projectDAGStock q74M qBase [0, 1, 3, 4, 5]
def q74F : Bound := (q74M, q74W, 8, q74G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q74Bin : BinLower q74M q74W q74G 8 := dagShiftLowerBin (width := 256) [qS23, qS0, qS5, qS7] q62Bin (by decide +kernel)
def q75M : Word := 0xa0a05050a0a05050a0a05050a0a0505
abbrev q75G : Word := qGoal &&& q75M
abbrev q75W : List Word := projectDAGStock q75M qBase [0, 1, 3, 5, 6]
def q75F : Bound := (q75M, q75W, 8, q75G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q75Bin : BinLower q75M q75W q75G 8 := dagShiftLowerBin (width := 256) [qS21, qS3, qS22, qS8, qS24, qS7] q62Bin (by decide +kernel)
def q76M : Word := 0x9090909090909090909090909090909
abbrev q76G : Word := qGoal &&& q76M
abbrev q76W : List Word := projectDAGStock q76M qBase [0, 3, 4, 5, 6]
def q76F : Bound := (q76M, q76W, 8, q76G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q76Bin : BinLower q76M q76W q76G 8 := dagShiftLowerBin (width := 256) [qS38, qS1, qS11, qS12, qS0, qS9, qS5, qS7] q62Bin (by decide +kernel)
def q77M : Word := 0xf0f0f0f000000000f0f0f0f0000
abbrev q77G : Word := qGoal &&& q77M
abbrev q77W : List Word := projectDAGStock q77M qBase [0, 1, 3, 4, 6]
def q77F : Bound := (q77M, q77W, 9, q77G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q77Bin : BinLower q77M q77W q77G 9 := dagShiftLowerBin (width := 256) [qS20, qS10, qS11, qS4, qS5, qS39] q63Bin (by decide +kernel)
def q78M : Word := 0x30303030c0c0c0c030303030c0c0c0c
abbrev q78G : Word := qGoal &&& q78M
abbrev q78W : List Word := projectDAGStock q78M qBase [0, 1, 3, 4, 6]
def q78F : Bound := (q78M, q78W, 9, q78G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q78Bin : BinLower q78M q78W q78G 9 := dagShiftLowerBin (width := 256) [qS20, qS3, qS4, qS5, qS39] q63Bin (by decide +kernel)
def q79M : Word := 0xf0f00000f0f00000f0f00000f0f00
abbrev q79G : Word := qGoal &&& q79M
abbrev q79W : List Word := projectDAGStock q79M qBase [0, 1, 3, 5, 6]
def q79F : Bound := (q79M, q79W, 9, q79G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q79Bin : BinLower q79M q79W q79G 9 := dagShiftLowerBin (width := 256) [qS21, qS29, qS1, qS22, qS24, qS5, qS39] q63Bin (by decide +kernel)
def q80M : Word := 0x30c030c030c030c030c030c030c030c
abbrev q80G : Word := qGoal &&& q80M
abbrev q80W : List Word := projectDAGStock q80M qBase [0, 1, 4, 5, 6]
def q80F : Bound := (q80M, q80W, 9, q80G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q80Bin : BinLower q80M q80W q80G 9 := dagShiftLowerBin (width := 256) [qS17, qS3, qS4, qS24, qS5, qS39] q63Bin (by decide +kernel)
def q81M : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f0000
abbrev q81G : Word := qGoal &&& q81M
abbrev q81W : List Word := projectDAGStock q81M qBase [0, 1, 3, 4, 7]
def q81F : Bound := (q81M, q81W, 9, q81G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q81Bin : BinLower q81M q81W q81G 9 := dagShiftLowerBin (width := 256) [qS20, qS10, qS11, qS4, qS6, qS7, qS39] q63Bin (by decide +kernel)
def q82M : Word := 0x30303030c0c0c0c0000000000000000030303030c0c0c0c
abbrev q82G : Word := qGoal &&& q82M
abbrev q82W : List Word := projectDAGStock q82M qBase [0, 1, 3, 4, 7]
def q82F : Bound := (q82M, q82W, 9, q82G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q82Bin : BinLower q82M q82W q82G 9 := dagShiftLowerBin (width := 256) [qS20, qS3, qS4, qS6, qS7, qS39] q63Bin (by decide +kernel)
def q83M : Word := 0x30300000c0c0000030300000c0c0000030300000c0c0000030300000c0c
abbrev q83G : Word := qGoal &&& q83M
abbrev q83W : List Word := projectDAGStock q83M qBase [0, 1, 3, 6, 7]
def q83F : Bound := (q83M, q83W, 9, q83G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q83Bin : BinLower q83M q83W q83G 9 := dagShiftLowerBin (width := 256) [qS20, qS3, qS8, qS9, qS6, qS39] q63Bin (by decide +kernel)
def q84M : Word := 0xf000f00000000000f000f00000000000f000f00000000000f000f0000
abbrev q84G : Word := qGoal &&& q84M
abbrev q84W : List Word := projectDAGStock q84M qBase [0, 1, 4, 6, 7]
def q84F : Bound := (q84M, q84W, 9, q84G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q84Bin : BinLower q84M q84W q84G 9 := dagShiftLowerBin (width := 256) [qS20, qS27, qS35, qS19, qS4, qS9, qS5, qS7, qS40] q64Bin (by decide +kernel)
def q85M : Word := 0x30303030000000003030303000000000303030300000000030303030000
abbrev q85G : Word := qGoal &&& q85M
abbrev q85W : List Word := projectDAGStock q85M qBase [0, 3, 4, 6, 7]
def q85F : Bound := (q85M, q85W, 9, q85G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q85Bin : BinLower q85M q85W q85G 9 := dagShiftLowerBin (width := 256) [qS20, qS10, qS11, qS12, qS8, qS9, qS6, qS39] q63Bin (by decide +kernel)
def q86M : Word := 0x50505050000000005050505000000000505050500000000050505050000
abbrev q86G : Word := qGoal &&& q86M
abbrev q86W : List Word := projectDAGStock q86M qBase [1, 3, 4, 6, 7]
def q86F : Bound := (q86M, q86W, 9, q86G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q86Bin : BinLower q86M q86W q86G 9 := dagShiftLowerBin (width := 256) [qS20, qS27, qS4, qS9, qS5, qS7, qS40] q64Bin (by decide +kernel)
def q87M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q87G : Word := qGoal &&& q87M
abbrev q87W : List Word := projectDAGStock q87M qBase [0, 1, 3, 4, 5, 6]
def q87F : Bound := (q87M, q87W, 10, q87G)
def q87E := unpackWitnesses q87W [49760, 312416, 577632, 843872, 1101896, 1368112]
abbrev q87N : List Word := normStock q87M q87W
def q87C : List Bound := [q61F, q0F, q66F, q67F, q77F, q2F, q11F, q65F, q63F, q9F, q8F, q10F, q52F, q72F, q74F, q75F, q76F, q78F, q79F, q80F]
def q87S : DagSample := (0x301840021301046031110a86038050a83038100a01028001409058301c022510c16060700884c140b05024060b0c06806090184c30190c024141a088642209100840623180c86012088c4443211048100920104201220108020905128c068300a00412081408050089040241008844462241a09028, 52)
def q87L : DagLinkList := dagExtractLinks 0xa82a0a8291a4290a06809c652905f5695553d8f007801 0x408981e4340e03646a170340d81806c2e62d96b14c388b61a4530c21985b14d240be8c0530901f8300ccaa0d7510630a235c4118c248865106b278318421ac1d0c60c8430502e60c14e8d8b744c5381429c2210e0c8b70445304219a1813d08086420330301781008c040260003f 10 4 13 5 3
def q87D : Forest := fun i => decodeNode 5 18 0x898e21a2c8b66229988666629948d64221910d634318d086302e0c86610178404610098407e0 i
def q87T := dagTraceTagsBin q87M 52 (dagTagBases q87N 0xffb084366fc7f5ff25b8996fbf02d820fee1fceac0749c1be3f2036fff13f9f05fc0fffff5309 0xfffb69cb7efc7f5ff89bb9f6fbfcad963fef7fceaf8764c7bf5f4376fff49f9fb5fe7fffff59bc 52) 9 q87D
def q87St := dagTraceBin q87M q87N 9 q87D
def q87Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q87Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q87Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q87Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q87Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q87Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def q87Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 5, 4, 0, 7] 0 i.val)
def q87Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 5, 4, 0, 7] 0 i.val)
def q87Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 1, 3, 4, 0, 7] 0 i.val)
def q87Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 4, 5, 1, 0, 7] 0 i.val)
def q87Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 4, 5, 1, 0, 7] 0 i.val)
def q87Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 1, 3, 4, 0, 7] 0 i.val)
def q87Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q87Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q87Mv := dagMoves ([([qS0], q87Mp0, q87Mi0), ([qS11], q87Mp1, q87Mi1), ([qS11, qS0], q87Mp2, q87Mi2), ([qS37, qS22, qS24], q87Mp3, q87Mi3), ([qS37, qS30, qS0, qS24], q87Mp4, q87Mi4), ([qS37, qS22, qS4, qS24], q87Mp5, q87Mi5), ([qS37, qS30, qS4], q87Mp6, q87Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87A : DagMovesOK q87M q87G 256 q87Mv := dagMovesOfCheck (by decide +kernel)
def q87NB : Nat → List Bound := dagNodeBounds q87C.toArray 0x3a0e83a0e4781d1331c0ed3a525488dd559d153500d 0x4038024400a418483105030048200460398ac598402846202425524d3944907b9a819c40 10 4 5
def q87Ck := dagCheckNodeBin q87M q87G q87NB 17 q87St q87Mv q87L q87S q87T
def q87RA (token : Nat) : Bool :=
  let s := rootState q87N 9 token
  !dagAllowedRootBin q87M q87E s.2.1 || dagLocalBin q87M q87G (dagKnownClosesBin q87G q87C) s ||
  dagRefBin q87M 17 q87St q87Mv (fun p tok => dagFindLink (q87L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87RB0 : treeBlock 0 64 q87RA = true := by decide +kernel
theorem q87R : dagCheckRootsBin q87M q87G (dagKnownClosesBin q87G q87C) q87E (dagRefBin q87M 17 q87St q87Mv (fun p tok => dagFindLink (q87L p) tok) 0) q87N 9 = true := q87RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87B0 : treeBlock 0 16 q87Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87B16 : treeBlock 16 1 q87Ck = true := by decide +kernel
theorem q87Bk : treeBlock 0 17 q87Ck = true := (@treeBlock_merge 0 16 1 q87Ck q87B0 q87B16)
theorem q87K : KnownBin q87C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q80Bin) q79Bin) q78Bin) q76Bin) q75Bin) q74Bin) q72Bin) q52Bin) q10Bin) q8Bin) q9Bin) q63Bin) q65Bin) q11Bin) q2Bin) q77Bin) q67Bin) q66Bin) q0Bin) q61Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87Bin : BinLower q87M q87W q87G 10 := by
  apply lowerDagBin _ _ _ _ q87A _ _ _ q87K _ (fun _ b hb => dagNodeBounds_mem b hb) q87R q87Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q87C.all (fun b => q87M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q88M : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev q88G : Word := qGoal &&& q88M
abbrev q88W : List Word := projectDAGStock q88M qBase [0, 1, 3, 4, 5, 7]
def q88F : Bound := (q88M, q88W, 10, q88G)
def q88E := unpackWitnesses q88W [82592, 345248, 610464, 876704, 1077272, 1400880]
abbrev q88N : List Word := normStock q88M q88W
def q88C : List Bound := [q68F, q0F, q9F, q12F, q4F, q62F, q44F, q3F, q45F, q69F, q8F, q54F, q56F, q73F]
def q88S : DagSample := (0x140a11108c60380022140a8052280090502c022910c26060b01824022130502c14090182c301a0182406130c06430090506822190882440210188c6032180484028040a02231110c8441204025008108049008200824108840221402801048209040240228100a040221112884482, 49)
def q88L : DagLinkList := dagExtractLinks 0xe83a0e83a0e4790e4390e0771c5b01c02c4a4e729866098260819f1785d16c9835890607c01 0x384243605c36438328437004f680433002f280233401932448ae87c2e85c2a84c304482f0622cc6e2ac62288482606c26c5322853244385e05f5a0531e02f1a023230632086e1601014421124201f0639c86e1c84e1b0631805c9645e94453924521643e1443312432cd05310c534cc438c8530e8430c8338a05f880534604f440430a03f080330602f04023020110003f 10 4 13 5 2
def q88D : Forest := fun i => decodeNode 5 18 0x849921c5003332244889108313d8dcf6313d090e629b48709831a10dc78319109c48318c0b8321f088662219098a6142185066101f8406610178404610088407e0 i
def q88T := dagTraceTagsBin q88M 49 (dagTagBases q88N 0xfdc210f66fc777e4b71ccf7cc3b820f3b87fee03a4e637c7c5b7ffc43fdf2c01fffffa984 0x3fdda72f7efc777f1377cff7cfbb963fbbdffef83b266f7ebc5b3ffd19fdf8edffffffacdf 49) 9 q88D
def q88St := dagTraceBin q88M q88N 9 q88D
def q88Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q88Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q88Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q88Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q88Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q88Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q88Mv := dagMoves ([([qS11], q88Mp0, q88Mi0), ([qS1], q88Mp1, q88Mi1), ([qS1, qS11], q88Mp2, q88Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88A : DagMovesOK q88M q88G 256 q88Mv := dagMovesOfCheck (by decide +kernel)
def q88NB : Nat → List Bound := dagNodeBounds q88C.toArray 0x5f0be1786e8dc1b636c2c9581ac54ce7a4d290b111fabb4724dc9a1a9b48a810d31461ea2582a005 0x4644348078640627420731403418072190511313a23c805a32b614960276732db0531a2015cd90519801525a2398065 11 4 4
def q88Ck := dagCheckNodeBin q88M q88G q88NB 29 q88St q88Mv q88L q88S q88T
def q88RA (token : Nat) : Bool :=
  let s := rootState q88N 9 token
  !dagAllowedRootBin q88M q88E s.2.1 || dagLocalBin q88M q88G (dagKnownClosesBin q88G q88C) s ||
  dagRefBin q88M 29 q88St q88Mv (fun p tok => dagFindLink (q88L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88RB0 : treeBlock 0 64 q88RA = true := by decide +kernel
theorem q88R : dagCheckRootsBin q88M q88G (dagKnownClosesBin q88G q88C) q88E (dagRefBin q88M 29 q88St q88Mv (fun p tok => dagFindLink (q88L p) tok) 0) q88N 9 = true := q88RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88B0 : treeBlock 0 16 q88Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88B16 : treeBlock 16 13 q88Ck = true := by decide +kernel
theorem q88Bk : treeBlock 0 29 q88Ck = true := (@treeBlock_merge 0 16 13 q88Ck q88B0 q88B16)
theorem q88K : KnownBin q88C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q73Bin) q56Bin) q54Bin) q8Bin) q69Bin) q45Bin) q3Bin) q44Bin) q62Bin) q4Bin) q12Bin) q9Bin) q0Bin) q68Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88Bin : BinLower q88M q88W q88G 10 := by
  apply lowerDagBin _ _ _ _ q88A _ _ _ q88K _ (fun _ b hb => dagNodeBounds_mem b hb) q88R q88Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q88C.all (fun b => q88M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q89M : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
abbrev q89G : Word := qGoal &&& q89M
abbrev q89W : List Word := projectDAGStock q89M qBase [0, 1, 3, 4, 6, 7]
def q89F : Bound := (q89M, q89W, 10, q89G)
def q89E := unpackWitnesses q89W [66176, 328832, 594048, 860288, 1147008, 1413192]
abbrev q89N : List Word := normStock q89M q89W
def q89C : List Bound := [q41F, q3F, q29F, q61F, q2F, q5F, q47F, q62F, q49F]
def q89S : DagSample := (0x68305228904a08a4430980884c140b05024060b0c06806090184c30190c024141a08864220920104804205128144208140805008904100940204201201209008201a04020904221008805208041208241009008a0402810090480c0403009088, 43)
def q89L : DagLinkList := dagExtractLinks 0x68c366c588690581 0x74507c50e051603130216c525452405e3052284390431023003f 7 3 12 3 1
def q89D : Forest := fun i => decodeNode 4 16 0xc506c522452205e205228431023103f0 i
def q89T := dagTraceTagsBin q89M 43 (dagTagBases q89N 0x1a108f8e7e38c96e3e3cff94106f7c7fdc749f3bf8ff7ffe03fff893ffffd1108 0x1ad39fbe7e39e26f3f5cff94b1e77ebfdc764f5bfd7f7ffe77fffd7fffffdbbbd 43) 9 q89D
def q89St := dagTraceBin q89M q89N 9 q89D
def q89Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q89Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q89Mv := dagMoves ([([qS11], q89Mp0, q89Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89A : DagMovesOK q89M q89G 256 q89Mv := dagMovesOfCheck (by decide +kernel)
def q89NB : Nat → List Bound := dagNodeBounds q89C.toArray 0x7db71789c419745c05 0x4013201042530251026410562731086370 9 3 4
def q89Ck := dagCheckNodeBin q89M q89G q89NB 8 q89St q89Mv q89L q89S q89T
def q89RA (token : Nat) : Bool :=
  let s := rootState q89N 9 token
  !dagAllowedRootBin q89M q89E s.2.1 || dagLocalBin q89M q89G (dagKnownClosesBin q89G q89C) s ||
  dagRefBin q89M 8 q89St q89Mv (fun p tok => dagFindLink (q89L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89RB0 : treeBlock 0 64 q89RA = true := by decide +kernel
theorem q89R : dagCheckRootsBin q89M q89G (dagKnownClosesBin q89G q89C) q89E (dagRefBin q89M 8 q89St q89Mv (fun p tok => dagFindLink (q89L p) tok) 0) q89N 9 = true := q89RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89B0 : treeBlock 0 8 q89Ck = true := by decide +kernel
theorem q89Bk : treeBlock 0 8 q89Ck = true := q89B0
theorem q89K : KnownBin q89C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q49Bin) q62Bin) q47Bin) q5Bin) q2Bin) q61Bin) q29Bin) q3Bin) q41Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89Bin : BinLower q89M q89W q89G 10 := by
  apply lowerDagBin _ _ _ _ q89A _ _ _ q89K _ (fun _ b hb => dagNodeBounds_mem b hb) q89R q89Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q89C.all (fun b => q89M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q90M : Word := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
abbrev q90G : Word := qGoal &&& q90M
abbrev q90W : List Word := projectDAGStock q90M qBase [0, 1, 3, 5, 6, 7]
def q90F : Bound := (q90M, q90W, 10, q90G)
def q90E := unpackWitnesses q90W [82592, 345248, 610464, 839752, 1163424, 1425504]
abbrev q90N : List Word := normStock q90M q90W
def q90C : List Bound := [q13F, q0F, q8F, q3F, q52F, q58F, q5F, q70F, q48F, q6F, q19F, q65F, q47F, q15F, q44F, q46F, q83F]
def q90S : DagSample := (0x2420440c01108c442a050a8026124104904911084c041301854088100a010280190c064150285402150288068301a0540a80522804825038090c830380c0c00502c14090182c904a0182440210188cc06201884804105128c068300a04462241a090280402500812010900820082410884022140280088444a21120802810090480c0403009088, 60)
def q90L : DagLinkList := dagExtractLinks 0xbe0be0be0be0be0be0be0bc1ba1b81b80b80b61b60b60b60b60b03ac2a82a80a61a60a60a60a60a60a41a219e29c19c09449219018c28637e47c162d6205094c24634033e1326266032001 0x6046060850610605e838cf4704e4305a02c564404c4305c44e5a442544405845054440590505642f54831c8c4852850504704806c4606c4406c530624e462510614e8424c42d4b05e48c5346853448339d063b146ea94629b062b6862c246ec04633e0633604130039280311a0214201940013a7460990613e8432643018422bc04fba04e3c02f3a02e9f06338c6336841244303402e3305ead052308332e02e2d05e2b0522883326452244322202f210631ec631cc431a842184621605c8905e870538505282c5390c438c853948338a4531444312433104230e0530c0430a033080290602304021020130003f 12 5 13 6 1
def q90D : Forest := fun i => decodeNode 6 19 0x4182841c4a44e78884f41414217a88314e0c474184d4211a42d360bc6314cc42998833300325004ca4219002f2005c4318c74208c02e1a0bc2a0cc50170905e0e0a41a0cc3229064320c05e1c18c263184c430908411188202e04443048660908c10298204304066080a410118202104026080fc0 i
def q90T := dagTraceTagsBin q90M 60 (dagTagBases q90N 0x581c27f113f3767c7fdccf4cdbcf9fe6e3f9b07c470fec3531b5f860fe3fb89cff0ee89dff13fef400ffffa988 0xfbfce7fd57ff767c77ce4f155bff9f74fbfdb2fdc7bfe8f071b4fae3fe9f7c9fff8eea4dffaffef1b7ffffacfd 60) 9 q90D
def q90St := dagTraceBin q90M q90N 9 q90D
def q90Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 5, 2, 6, 4, 1, 3, 0] 0 i.val)
def q90Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 5, 2, 6, 4, 1, 3, 0] 0 i.val)
def q90Mv := dagMoves ([([qS41, qS30, qS8], q90Mp0, q90Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90A : DagMovesOK q90M q90G 256 q90Mv := dagMovesOfCheck (by decide +kernel)
def q90NB : Nat → List Bound := dagNodeBounds q90C.toArray 0xa50a50a32a30a129f29c39a29829539419319219209208d58948458137c57a27647156f26d26b26926726526145e35c25755435224a84554143d43493222a82642061a6164106079007 0x3008041142030ca45104208c600954d2882a2004520043090020c06028460095a14a4200802200024104051000128cc408d200194430860404a401c4740c273086a720a43080300d64114e0484e23056801845591891184c081845880179ca4120030c1ee3ad88 12 4 5
def q90Ck := dagCheckNodeBin q90M q90G q90NB 49 q90St q90Mv q90L q90S q90T
def q90RA (token : Nat) : Bool :=
  let s := rootState q90N 9 token
  !dagAllowedRootBin q90M q90E s.2.1 || dagLocalBin q90M q90G (dagKnownClosesBin q90G q90C) s ||
  dagRefBin q90M 49 q90St q90Mv (fun p tok => dagFindLink (q90L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90RB0 : treeBlock 0 64 q90RA = true := by decide +kernel
theorem q90R : dagCheckRootsBin q90M q90G (dagKnownClosesBin q90G q90C) q90E (dagRefBin q90M 49 q90St q90Mv (fun p tok => dagFindLink (q90L p) tok) 0) q90N 9 = true := q90RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90B0 : treeBlock 0 16 q90Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90B16 : treeBlock 16 16 q90Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90B32 : treeBlock 32 16 q90Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90B48 : treeBlock 48 1 q90Ck = true := by decide +kernel
theorem q90Bk : treeBlock 0 49 q90Ck = true := (@treeBlock_merge 0 32 17 q90Ck (@treeBlock_merge 0 16 16 q90Ck q90B0 q90B16) (@treeBlock_merge 32 16 1 q90Ck q90B32 q90B48))
theorem q90K : KnownBin q90C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q83Bin) q46Bin) q44Bin) q15Bin) q47Bin) q65Bin) q19Bin) q6Bin) q48Bin) q70Bin) q5Bin) q58Bin) q52Bin) q3Bin) q8Bin) q0Bin) q13Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90Bin : BinLower q90M q90W q90G 10 := by
  apply lowerDagBin _ _ _ _ q90A _ _ _ q90K _ (fun _ b hb => dagNodeBounds_mem b hb) q90R q90Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q90C.all (fun b => q90M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q91M : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev q91G : Word := qGoal &&& q91M
abbrev q91W : List Word := projectDAGStock q91M qBase [0, 1, 4, 5, 6, 7]
def q91F : Bound := (q91M, q91W, 10, q91G)
def q91E := unpackWitnesses q91W [82592, 345248, 614560, 811537, 1163424, 1425504]
abbrev q91N : List Word := normStock q91M q91W
def q91C : List Bound := [q5F, q43F, q15F, q68F, q41F, q66F, q48F, q4F, q50F, q2F, q19F, q17F, q22F]
def q91S : DagSample := (0x205220148005000240064101108607018140c07050288068301a040482301882251502c02291182c060905038140c030380c0c00884c4423088480613180c406120188c6032180482231110c8441220104804208140805008904446211108402140204201240208041208241009008a04022111288448200a0402414030080c0, 57)
def q91L : DagLinkList := dagExtractLinks 0x9e09e09e09e09e09e09e09e09e09e09e09b39659339309219029008f18f08e18e08e08b38838268117f27f07f07f07e17e07c27a27a07a07a07827627516f66695f75875535505054d34b241a3983633152f22691f714b07d016001 0xe086168420740183d2106e485d68422390171a0088ed8a0f4850b32181b8080e98a06c430390281cc140e10a0ec840b40281c4141d90816c450774273b2108dc89c6c442b5027598108dc8616c850364201a9141d10a0684503482819a142c80b86204cb202e190130c40a8608516b420979140908445202e1a011185181b98a0d6850ae2301190c26484156060590180a0081b98a4d885e6b429171148888605805e2b02917c142b90a25c841a72174c90889c05c320222d2249610c484025568512b420901088a805c28022298291411789c0a44c06c2502e722181910a0c0840a423012114080881340601a0280e8130500804905223429112100848bc404529c02f4c81487c09abe8501f228098140798bc3ac5213626ae1148700a42645c1b0360d4149650a4324521802f0b8174580b82a05514029098137488a2a44414c218c90144480821803109009894148450a6208410f229041088380bc1a0530c0290580b8280460802209829e4214921085104520822143817e180bd0a0538402903813c1809c0a0430402101b10f0888684433820218100cc040260003f 12 4 13 6 2
def q91D : Forest := fun i => decodeNode 6 19 0x6285ec50b20a144142421844840848a0ec141a4283404c540a8a518128282084140892790c4f4209a02e360a461178c0291806c2c0b85c148942912840248bc49148922810c5e1d8a43814870360d052148a428178502e8a05c140aa2814850268b0520d0a61a10432290605e0c0a6181483017060230e0a61110820278404e080861010826218203304026080fc0 i
def q91T := dagTraceTagsBin q91M 57 (dagTagBases q91N 0x3df35f92dbb3e667727fc212e63cf0c7c1e8419f47ffe9d55b49fafe7c41e787ff80fff1df0c03ffffd444 0x3df35fa4dfbfe67e78ffea73e7bcf7cfd1eac7af6bffe1d40b64f8ff3efdefe7ff97fffdff7dcfffffd6fd 57) 9 q91D
def q91St := dagTraceBin q91M q91N 9 q91D
def q91Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q91Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q91Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q91Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q91Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 7, 6] 0 i.val)
def q91Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 7, 6] 0 i.val)
def q91Mv := dagMoves ([([qS7], q91Mp0, q91Mi0), ([qS11], q91Mp1, q91Mi1), ([qS11, qS7], q91Mp2, q91Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91A : DagMovesOK q91M q91G 256 q91Mv := dagMovesOfCheck (by decide +kernel)
def q91NB : Nat → List Bound := dagNodeBounds q91C.toArray 0x8410821041983104608409811022044017d6fa1f0bd97a2f25e0bc0780f01dcbb8762e35c0b796e2da5ad351676cc594b28642c4988310612bb16d2ae50a99125a1e3f878cde98e2ca4d87f8c713a19c1b006 0x270291033710021746537981685140001405210c2a24035b21903120b20b5271003420a26175012496343196381645a856142a620354635106123504186354813564 11 3 4
def q91Ck := dagCheckNodeBin q91M q91G q91NB 60 q91St q91Mv q91L q91S q91T
def q91RA (token : Nat) : Bool :=
  let s := rootState q91N 9 token
  !dagAllowedRootBin q91M q91E s.2.1 || dagLocalBin q91M q91G (dagKnownClosesBin q91G q91C) s ||
  dagRefBin q91M 60 q91St q91Mv (fun p tok => dagFindLink (q91L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91RB0 : treeBlock 0 64 q91RA = true := by decide +kernel
theorem q91R : dagCheckRootsBin q91M q91G (dagKnownClosesBin q91G q91C) q91E (dagRefBin q91M 60 q91St q91Mv (fun p tok => dagFindLink (q91L p) tok) 0) q91N 9 = true := q91RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B0 : treeBlock 0 16 q91Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B16 : treeBlock 16 16 q91Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B32 : treeBlock 32 16 q91Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B48 : treeBlock 48 12 q91Ck = true := by decide +kernel
theorem q91Bk : treeBlock 0 60 q91Ck = true := (@treeBlock_merge 0 32 28 q91Ck (@treeBlock_merge 0 16 16 q91Ck q91B0 q91B16) (@treeBlock_merge 32 16 12 q91Ck q91B32 q91B48))
theorem q91K : KnownBin q91C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q22Bin) q17Bin) q19Bin) q2Bin) q50Bin) q4Bin) q48Bin) q66Bin) q41Bin) q68Bin) q15Bin) q43Bin) q5Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91Bin : BinLower q91M q91W q91G 10 := by
  apply lowerDagBin _ _ _ _ q91A _ _ _ q91K _ (fun _ b hb => dagNodeBounds_mem b hb) q91R q91Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q91C.all (fun b => q91M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q92M : Word := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev q92G : Word := qGoal &&& q92M
abbrev q92W : List Word := projectDAGStock q92M qBase [1, 3, 4, 5, 6, 7]
def q92F : Bound := (q92M, q92W, 10, q92G)
def q92E := unpackWitnesses q92W [83104, 348320, 614560, 839752, 1163424, 1425504]
abbrev q92N : List Word := normStock q92M q92W
def q92C : List Bound := [q71F, q2F, q70F, q43F, q41F, q69F, q21F, q4F, q24F, q23F]
def q92S : DagSample := (0x100520824900c20130900d040140805205220005024128c0625028940b00c26060b024160c0700c16060700030140e024320c0e030300442a0c068301205068603805048142a180c860120c0e0443211048804205128c068300a08050081404462241a09028080490082100a01088402214028010482090402403088040a044a21120804820110880c0403009088, 63)
def q92L : DagLinkList := dagExtractLinks 0x1780bc05e02f01780bc05e02f01780bc05e02d8d6a1b505a82d03680b30d982cc1603af0d782b83563a91538a983482a40508e6cd3609b04d826c13419a04c866413209714b825452a09504a824871e38e0c39e0c90607e2bd8ddc8e836d3b4917d4aaa512270d1528433b39c0cb5640d1b28544052001 0x71c092e0010547014a8002111c0322000463e03608f0608f80d81f10924503018a0409180c01f10e14423037e4405000c0a291b0432182844601088802311804663608a44c1120c0212102bf23008685e1090a4e09179bf22928205e4fc0a4208180412300810600fc8c05fc1803f43047c06c2f40981e80b23e03617c04c0f80581e81903c83045e0612bc0829c00a51e0108700190780231981b43b02c95c0310b8023168184ad02085a0210e80320b8044b922e07243c0d88585c41883843106e06e0d803c1a81f0b402e06803c0cd0909911f03222e06044c8ac0e05581419d0200650620c58dc18318a2c03125e8700bd0a016a102292381524506708810f01c09e02804804c05c08017c1882e43705a8624ac8dc9491882a22085044048c0dc8f018827026858c6e0ac8c49101b91d031054c5007c8784f8170a98310528620a1080d091b99c23114c42d4840dc8e01882602684e8500988a04b014025637048c6225989a1191882203704206227c0824b11702003e03e03c27a0c40f21881d23703846206c0dc0d01b41903603006505c0c44b01341601692b0620550c40a11b8132318244628380df06018c8b02081602104403e0800640f00980801103a0c68691b80d22741406222808406418d0b4310168424288dc84918d0823101444e02488604110907037a0c06e4140c68201880702780c04e01408602010983629a0645300c86701017e0102990403f20406601007c0100980003f 13 5 13 7 3
def q92D : Forest := fun i => decodeNode 7 20 0x830396362c2262c8302a42f2942929230228301f4301d01618032178301602c9500c9321e12431110371100f1103e1001e104240f8310e6370e6310e8310c4370c4310c6370b2310b6280a43109420094280822808637076310723107037070310703e0601e064310523705231050370503685036050328503105016854310423704231842310400f8400c840098483183227038318242102227022218222102027820270202182021022198100f810098101f80 i
def q92T := dagTraceTagsBin q92M 63 (dagTagBases q92N 0x363ffc210f67bc3ff5d5d92dc730e7e31701f820f3be3ffff8aaae9398dbcfd047803ffc43fff8c370f07ffffe9888 0x3bbfffda72f7fbc3ff5d5dc4ddf3be7ebff99f963fbbf5ffff8aa8ec99bdbe7ff679e3ffd19fffd29f3fbfffffecdfd 63) 9 q92D
def q92St := dagTraceBin q92M q92N 9 q92D
def q92Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q92Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q92Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q92Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q92Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q92Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q92Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 6, 5, 1, 7] 0 i.val)
def q92Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 1, 5, 4, 7] 0 i.val)
def q92Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q92Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q92Mv := dagMoves ([([qS9], q92Mp0, q92Mi0), ([qS11], q92Mp1, q92Mi1), ([qS32, qS9], q92Mp2, q92Mi2), ([qS11, qS9], q92Mp3, q92Mi3), ([qS32], q92Mp4, q92Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92A : DagMovesOK q92M q92G 256 q92Mv := dagMovesOfCheck (by decide +kernel)
def q92NB : Nat → List Bound := dagNodeBounds q92C.toArray 0x9309309309309309309309219119109108c58c08b18a18918908818718618608518508508418408318308307f47f07b47a17917817717617607517507417317217117107016e26e06e06d16766255e45595144d44944454043c43663242d52942632151e31861170b6056005 0x63042537605708134711425610200100603413049623014685968390162543576304606513271802512718361742625134125142571230245062362504301625430425130125430254 12 4 4
def q92Ck := dagCheckNodeBin q92M q92G q92NB 72 q92St q92Mv q92L q92S q92T
def q92RA (token : Nat) : Bool :=
  let s := rootState q92N 9 token
  !dagAllowedRootBin q92M q92E s.2.1 || dagLocalBin q92M q92G (dagKnownClosesBin q92G q92C) s ||
  dagRefBin q92M 72 q92St q92Mv (fun p tok => dagFindLink (q92L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92RB0 : treeBlock 0 64 q92RA = true := by decide +kernel
theorem q92R : dagCheckRootsBin q92M q92G (dagKnownClosesBin q92G q92C) q92E (dagRefBin q92M 72 q92St q92Mv (fun p tok => dagFindLink (q92L p) tok) 0) q92N 9 = true := q92RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92B0 : treeBlock 0 16 q92Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92B16 : treeBlock 16 16 q92Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92B32 : treeBlock 32 16 q92Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92B48 : treeBlock 48 16 q92Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92B64 : treeBlock 64 8 q92Ck = true := by decide +kernel
theorem q92Bk : treeBlock 0 72 q92Ck = true := (@treeBlock_merge 0 48 24 q92Ck (@treeBlock_merge 0 32 16 q92Ck (@treeBlock_merge 0 16 16 q92Ck q92B0 q92B16) q92B32) (@treeBlock_merge 48 16 8 q92Ck q92B48 q92B64))
theorem q92K : KnownBin q92C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q23Bin) q24Bin) q4Bin) q21Bin) q69Bin) q41Bin) q43Bin) q70Bin) q2Bin) q71Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92Bin : BinLower q92M q92W q92G 10 := by
  apply lowerDagBin _ _ _ _ q92A _ _ _ q92K _ (fun _ b hb => dagNodeBounds_mem b hb) q92R q92Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q92C.all (fun b => q92M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q93M : Word := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000
abbrev q93G : Word := qGoal &&& q93M
abbrev q93W : List Word := projectDAGStock q93M qBase [0, 1, 3, 4, 6, 7]
def q93F : Bound := (q93M, q93W, 11, q93G)
def q93E := unpackWitnesses q93W [82592, 345248, 610464, 860320, 1163424, 1425504]
abbrev q93N : List Word := normStock q93M q93W
def q93C : List Bound := [q60F, q77F, q81F, q84F, q85F, q86F]
def q93S : DagSample := (0x884c442308848442a0c06830120c064222108864302808944c06130084c062111883058301a0c02830140402108a4540a15008420125028844a2100a03098502a1402811049409008240205050380c0e0, 36)
def q93L : DagLinkList := dagExtractLinks 0x9 0x3f 2 1 6 1 4
def q93D : Forest := fun i => decodeNode 1 7 0x7e i
def q93T := dagTraceTagsBin q93M 36 (dagTagBases q93N 0x3c47e1fff03f9fe3dfe53e3fc3faea12913cffc85fff8fffff3264 0x5e5ff7fffaffdffbdff1beffeffafe10910cffe31fffefffff972d 36) 10 q93D
def q93St := dagTraceBin q93M q93N 10 q93D
def q93Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q93Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def q93Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q93Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q93Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 4, 5, 1, 6] 0 i.val)
def q93Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 7, 1] 0 i.val)
def q93Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 7, 1] 0 i.val)
def q93Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 4, 5, 1, 6] 0 i.val)
def q93Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 4, 5, 6, 1] 0 i.val)
def q93Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 2, 3, 4, 5, 6, 1] 0 i.val)
def q93Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 7, 6] 0 i.val)
def q93Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 7, 6] 0 i.val)
def q93Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q93Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q93Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 7, 2, 0, 4, 5, 1, 6] 0 i.val)
def q93Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 7, 1] 0 i.val)
def q93Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 7, 1] 0 i.val)
def q93Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 7, 2, 0, 4, 5, 1, 6] 0 i.val)
def q93Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 7, 2, 0, 4, 5, 6, 1] 0 i.val)
def q93Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 7, 2, 0, 4, 5, 6, 1] 0 i.val)
def q93Mv := dagMoves ([([qS7], q93Mp0, q93Mi0), ([qS32], q93Mp1, q93Mi1), ([qS34, qS7], q93Mp2, q93Mi2), ([qS32, qS7], q93Mp3, q93Mi3), ([qS34], q93Mp4, q93Mi4), ([qS1], q93Mp5, q93Mi5), ([qS1, qS7], q93Mp6, q93Mi6), ([qS1, qS32], q93Mp7, q93Mi7), ([qS1, qS34, qS7], q93Mp8, q93Mi8), ([qS1, qS32, qS7], q93Mp9, q93Mi9), ([qS1, qS34], q93Mp10, q93Mi10)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93A : DagMovesOK q93M q93G 256 q93Mv := dagMovesOfCheck (by decide +kernel)
def q93NB : Nat → List Bound := dagNodeBounds q93C.toArray 0x6 0x2b888 6 3 3
def q93Ck := dagCheckNodeBin q93M q93G q93NB 1 q93St q93Mv q93L q93S q93T
def q93RA (token : Nat) : Bool :=
  let s := rootState q93N 10 token
  !dagAllowedRootBin q93M q93E s.2.1 || dagLocalBin q93M q93G (dagKnownClosesBin q93G q93C) s ||
  dagRefBin q93M 1 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93RB0 : treeBlock 0 64 q93RA = true := by decide +kernel
theorem q93R : dagCheckRootsBin q93M q93G (dagKnownClosesBin q93G q93C) q93E (dagRefBin q93M 1 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0) q93N 10 = true := q93RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B0 : treeBlock 0 1 q93Ck = true := by decide +kernel
theorem q93Bk : treeBlock 0 1 q93Ck = true := q93B0
theorem q93K : KnownBin q93C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q86Bin) q85Bin) q84Bin) q81Bin) q77Bin) q60Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93Bin : BinLower q93M q93W q93G 11 := by
  apply lowerDagBin _ _ _ _ q93A _ _ _ q93K _ (fun _ b hb => dagNodeBounds_mem b hb) q93R q93Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q93C.all (fun b => q93M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q94M : Word := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev q94G : Word := qGoal &&& q94M
abbrev q94W : List Word := projectDAGStock q94M qBase [0, 3, 4, 5, 6, 7]
def q94F : Bound := (q94M, q94W, 10, q94G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94Bin : BinLower q94M q94W q94G 10 := dagShiftLowerBin (width := 256) [qS11, qS12] q90Bin (by decide +kernel)
def q95M : Word := 0x30303030c0c0c0c030303030c0c0c0c030303030c0c0c0c030303030c0c0c0c
abbrev q95G : Word := qGoal &&& q95M
abbrev q95W : List Word := projectDAGStock q95M qBase [0, 1, 3, 4, 6, 7]
def q95F : Bound := (q95M, q95W, 11, q95G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95Bin : BinLower q95M q95W q95G 11 := dagShiftLowerBin (width := 256) [qS20, qS11, qS36] q93Bin (by decide +kernel)
def q96M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q96G : Word := qGoal &&& q96M
abbrev q96W : List Word := projectDAGStock q96M qBase [0, 1, 3, 4, 5, 6, 7]
def q96E := unpackWitnesses q96W [82592, 345248, 610464, 876704, 1101896, 1425568, 1687648]
abbrev q96N : List Word := normStock q96M q96W
def q96C : List Bound := [q8F, q43F, q41F, q0F, q90F, q9F, q94F, q3F, q63F, q87F, q92F, q10F, q62F, q64F, q91F, q5F, q88F, q65F, q79F, q2F, q44F, q54F, q4F, q80F, q68F, q70F, q89F, q46F, q45F, q67F, q75F, q52F, q69F, q71F, q48F, q61F, q66F, q49F, q81F, q74F, q83F, q93F, q53F, q82F, q95F, q76F]
def q96S : DagSample := (0x44c2052209081100a06021180a030120824820190104c20510884820521024040c020340104900a24309004160029120148305008a40005000240605000048141201848c0210c220064150288068124128c062008c40261241044423180c4c041110a86038050a940880c0e090493018490090190c102824160c070089443058181c140a1500840683502a0148a502c022910c2600482182c060905038090c830380c0c00884c140b05024060b0c06806090184c30190c024141a088642209100840623180c86012088c4443211048804120108144a301a0c028081408050089044462241a090280402500810804900820082410884022140280104820904024022810088444a21120802810090480c0403009088, 123)
def q96L : DagLinkList := dagExtractLinks 0x2bd815ec0af6057b02bd815ec0af6057b02bd815ec0af6057b02bd815ec0af6057b02bd815ec0af6057b02bd815ec0af6057b02bd815ea1af40d7986bb0f5d61aeb057582bac15d60aea0d7486ba035d00ae8057402ba015d00ae8057402ba015ce1ae41d7186b8075be1add156b9ab5455aa0ad40d6986b40759e1acf056782b38359c0ace056702b3435962aca0d6502b2815940aca056486b2415901ac70d6382b1c158e0ac7056382b1c158e0ac705620eb0c35822ac1056082b0415820abe1d5d8eae835740aba055d02ad0d5661ab3055982ac835640ab2055886ac415601ab0055802ab8555c0aad0d5682ab4155a0aad055682ab4155a0aad055682ab415581aab0d5506aa815540aa90d5482aa0354e1aa60d5302a9055442aa10d5082a84153e2a9e0d4f02a78153a1a9d054e82a74153a0a9d054d8aa6455301a98054c02a5c352c1a96054b02a5815244a8e25460aa3015123a880d4402a2015100a88054212a0c35060a83054182a0c15060a83054182a0c14fe4a77453a8a9b514da0a6545328299414c81a611d2f0e97814b44a5a052d0296434b20a59052c8294cd4a41a4f1d268a92c54941a490d238a918348c0a46052286914148a0a4505220690854802a3e151e868e874721a380d1c028e014700a370d1b828d8346a1a35051a828d034642a310d18068bc345c1a273d120e88c34349a1625098e840741a3a0b15021e80093fa39fa1cfc0a7dc33ec19f31cf88a7bc53d079e804f02278013c009dd1ceb9a748b3a219cf14e592720738a39c21cdf8e6fc137839bb0cdd826ec137419b814db866d8336c09b12cd78a6b0735429a814d28e68c534609a304d106688133e399d14ce0666c3334199a04cd02660532a39940cc9866445320199004c80263c331e098f04c78263c131c198c14c6026301318098b0cc5826283312198904c4826241312098904c4826241312098904c40661c330c19850cc2066101308097a54bb125b912d259661cb18e58072be195e0cad1256052ac295224a6965341298194824a40251c328c19450ca282514127a89382c9a8e4c8725c492b1c940e49472424921049006464f226690d34850e41c720e0907048382410720619020c80863f871f448f8147b0a3d431e438f20479023bc71da28ec0c750a3a811d408ea04740a39c31cc18e604720a38c31c608e304708a370b1b808db0c6d0636811b408da046d0236811b408da046d0236051ae18d60c6a0a34c31a418cf1c668a32c519228c714630630c718608c304608a2f8717c08b54c590e2c0515c28ab1c540e298514828a11c4f0e270513428971c4b06258112c08950c4a8225411281894044a02244711e288d14450e220510c28831c408a20030fe187e0c3d121e810f408771c3b821dc10ee0877043b821dc10ee0877043b821dc10d6c86b0435821ac10d6086b0435061a810c8686404308e18030b6585b042d0616430b208580c2b8615c10ae0857042b8215c10ae0857042b8215070a8085404298614830a218500c280213c309c184e042702138109c084e042686134108c78460422860f13076183a0c1c860e4107018342419860c0706008300417860bc105e082f0417820bc105e082e0c17020b43042c8200c0f8607c103e081f040b2605430281812140696020affe97fd13f6c1fa0afc657e303f181f8c0fc417e10bee15f684fae37d41be88df402f9277c523e091efc4f7e07bf03df81eec8f7607b913dc81ee40f6e27b60bd98dec44f5e27ac1bd411e984f3e779d13cb99e544f28179023c595e244f08578023be11de08eee177513b989db4ced8176823b385d982eca176503b281d940ec817630bb105d804eba375d03ad0dd642eb0175803ab09d504ea4275013a785d382e9c074e03a701d380e9c07435ba105d080e7297380b9b85ccc8e587726338e29c58ce1a97044b7f95bf82df446f243759db90edbc66da236a95b502d9696c9135e35ad4ed5c76ac135319a942d4a06a40b5185a8c0d4416a2035101a880d3a569a1b4b8da506d24268e234701a342d1a068d03431da04acf856791b3a159cc2ce606730337159b80cd4466a03331198c6cc0365d1b2e819648cac365413290993c6c98364c0326019300c98064c0326019300c96164a0b25019280c9406490b24059200c90064803240191c2c8e06460b218d9044c80163d1b1d0d8e04c6a362f331499890ac40461d1b0d0d854ac2816102308018400c06d5f66af6297894bb485d812e9957254b8e25c03adc216c10b5655a532cea16686b28658c42c29d6140b0a057e3aba295cc2ad8756442ae21558ca9e75426aa0094fc2a745534329a014d00a6615330299814cc0a6605320a98854acca4e45241a908d4748a30551422879543c0a1075051a82814140a0434fe227d8d3d8a9e254f10276913a489c854e212700937469b244d80a689d31d498e04c22a5ca52c1295654a62a518d280693a34982a4995238a91a148c0a460122c290874757a36251ac28d2246902329119028c044600229391252890143c621c8d0e4085ac42c0a129d08c483684162a08950386812540521fda8fd0e7dc63ea21f218f8c27c033db29e82cefa477063b329d80cebc275643aa09d484e986742539469c88ce0dc6e5136851af28d362696234a099e38cec265cd32c119584c90e63e531c198b18c25a5f6e2f53175a8b9c85c452dc316c10b50859e52c839609caf4857052b519590cab0c53ed2974144b89f964e6b267612fa094d849e4241711e908f40470522e51158c87d843c1216410894834840c72050900147eca3ee41f608f89479d43ca21de38ea28740839e11ce08df406dce350f19b68c734605a2e4f15ea0a6c452c428c514318a1804ed0260b123688d24435a21a0105407e24396e195b0c1485d982d4c1589096b03e681e460c9505c402358100c0784031580b6c006a0001 0x7c0c607bec607c10607be0497b20417c0039fbc029fa00217bc0197a00117bf0587bc8607bd0607bcc587ba4607ae430f9e4207a00307b84607b6460f9c4307b20607ac4207b44607aa4307ba8497b4841fb042ef9e4227b002e79e0227bb0587b8c607b8c587b94627b6c607b4860f9c4307b70587b50587a80207b2c607a64307b30587b00607b10607b0c58fae4607a6440fa00607ac430faa4607aa4407ae8607aa840f9e0607af0607aa840fa64607aec587ac85e7aa8527a845e7a6452fa405ef9c0527ac8387aac487a84307a8838fa68607a68407a6c487a40607a44607a48587a207c7a24707a28607a34707a086079e4607a106079c4607a0c5879f06079c86079ec5879cc58f9a06c79804cf9a06c79a04c79a848798064798848f8e86178e841796839780831f66061766041796039794019794c58790860f8c86178c84179202e792c58770071f6206176204179002979147278f06278ac6278486e780862788860f6406178c04973e04178e03971a02177c0196b801178d058786c70789060f6006176004178a039f7a029eb602177a0196b6011788c5876e07178604973c041f78029eb40217780196b401178746373a051eb20216b2011738051eb00216b001178205975e031784029718011782c58f5c06175c04178003971602177e01969801177ec5877d06277a86277606e77cc5877887077907077ac5877946377684877407c77205c774c58772c58770c70770c5871443077188076802c76ec8071243076f48076f87172244076c06e71042070e43076885076c87076d07072044076a85e76885276a43876884871e44071c44076486176684975c84175a46070c42273202e6b8022767058762c60758470756470765470760c5075c850f5047070a430eae420f3e0706b6030698020765068708430eac4206b4030706430eaa4206b2030704430ea84206b0030762c58754470702430763472752460760c6275e86e75c86275046270043074006e73e06276105874e470ea643073c07074c470ea443073a07074a470ea243073807075ec486fe4206fc4206fa42075d0587484706f84307464706f64307444706f443075b060f50861750841f2e42eeae42272e02e6ae02275ac58754861758849748841f2c42eeac42272c02e6ac022759463757063752c52756859746851f2a42eeaa42272a02e6aa022744851f2842eea842272802e6a8022755470755872752c5875105874ec70748870ea643074cc70746870ea443074ac70744870ea243074f46374d06374b0537494637470637450537424597404316f2012742c586f0020740c486ee0206ec0206ea020f3e86173e8416e842273602e6980226e643073403c73f05873cc706e443073ac706e2430738c706e043073d46373b063739053736c5873486073547273306273046e72e062732c5872c07072a07072807073084872d07072ec5872d46372ac63728c5372b47072947072607c72405c726c58724c5871e45072246271c45272043d722c60723060720c4871ec5071ec4871cc6071d060f1a87071a850716840f0c47070c4506e8440eb80706b80506d004c698040714480f024707024506e644071b06271886e716862f0a462700440ece06eeb60626de04d71ac58712480f084706e4440eb4070f064706e2450eb2070f044706e0450eb00707188487104806fe4306fc4406fa440716c5870e480ef84706f8440ef64706f6450ef44706f4450f1288071487071285070e840715063edc06fec40636dc04f6c404371588071307271087e70e8726da04d71347171107170f47170d06270a8627008406f246e6e8462ecc06eeae0626d804d70cc587088707028606f8840eac0707068706f6850eaa0707048706f4850ea807070907070ac586f8840ee4470709463706c63704c537074706f6850ee24707054706f4850ee04707030626f046e6e64626d604d703472700c486fe86e6f88626ee46e6e4462eca06eea60626fc86e6f68626ec46e6e2462ec806eea40626fa86e6f48626ea46e6e0462ec606eea20626fec636fc8636fa8336f90636f6c636f4c436f28486f04506ee4306ec4406ea4406f10726eec636ec8636ea8336e8c58ee48706e68606e4840ee28706e2850ee08706e08506e74726e50636e2c636e0c436de8506d84506900506dc4806d64506d44406dec586da4806dc8706da8506dd8806db4716d8c586d68606d48426d74726d507e6d2c6e6d0c62690c4d6ce4626cc0626d28486d08586ce8586ca0706c80706c60706cc8586ca4706c84706c64706cb4636c88636c685369045c6c207c6c48806c007c6c4c706be08c6c58806bc07c6ba07c6c2c586c08606be4806c14726bc4726bf4716bc8526ba42d6b90626b68626ae4626a006e69e06d69c06c69a06569806269004d6b8c586b48706ac4706b28706aa4706b08706a84706b50706b6c586a64706b54636b2c636b0c536b34706a44706b14706a24706ad0706aec586a68706ad4636aac636a8c536ab4706a48706a94706a28706a74636a4c636a2c536a084869ec5869c84869ac58e9607c68e04ce9407c68a05ce9207c68805c698c58e9607c69604ce9407c69405ce9207c69205c697063694863692843690c5868e07468c05468a07468807468f06368cc6e68a863688843686c53e5e85365e833e5c46165c441684439680433638431dec0615ec04167e03967a033594031686029524013674471684c5867286061a081dea0715ea041682019683473676c73670852680c6867ec58e5a87166e86165a84167c02e67d47367ac68679470679870de80715e805167601966c85266a86267548c66886066686066485066c880672848618081dde0715de05166e04959204152202166a880673472662473616073ddc0615f00515dc04155603167002966001366f882668880666870664872e6987266746066d07e66b07266b08066987166747066506e662c58660c5864847c65d06265886264646e63a463638462de60635da04165e03952002163401962a01345c01164246c65687065cc58654870614081de407165a04959004151e02163201945a01165285065086065b47364ec6064c870de207158e05151c02145801164a870de007158c05151a021456011655070658c58612081dd80715d8041e30029c5402163001945401165787065106065546365306e65106264cc6364ac536100635ee05364e04958a04155a039558033554031e2e029c5202162e01945201164d470dd60715d6051c5002145001164b470dd40715d4051c4e02144e01164905964505164684860e0816400695d203151801164587e64307e63e0695d004151601163c0695ce04151401164147363ec7363cc5363b068638c5860c081dcc0715cc04151202163601942a011dca0715ca051510021428011dc80715c805150e021426011637473552430633072634c5863087262c07e63347362e86063147362f06062d07362b06862808c62205c62608c61e06c62408c61c06c629473626c73624c5362347362107e61ec7361cc5355043060a05fe1488161887161485161a84960c84150c42260807d54e43060606f61b881616c6254c44060406e5f803d5f603c61947350a430508430619c90616c585064305f202c615482612c8260e88e60c88250443054a440502430615881610c7054844050043060006e6138816114705464405fe06e60f4815444304fe4205fc05e60d8815424404fc4305fa06e60907360b08e607082609c90607090e004716024595f24516004416044395fa4316030636010725fe8725fc47e5fa47254043053e43053c44053a8405384305364305344404fa4305f8c585324404f84305f68485f446e5f24625f4c635f30635f0c605304405f0c5852e4405eec7052c4405ef47052a4405284305264405ed0625e68635da8415c64624f64225a606e59606359406257e02e56802345c0225c44705ecc585e48715de8615ea8495cc8415c24704f442257c02e45a0225c04505be4605eb4735e90735dcc525bc4605e28715e88595ca8515ba4704f242257a02e4580225e08715c88515b84704f042257802e4560225e54805e70685d8c505cc850db24804ee430c4c420d9008045403042a0205e58735e30735e10634ec430c4a4204520305e38805d6c605ca860db04804ea430c48420d8e0804500304280205e18805d4c605c8860dae4804e8430c46420d8c08044e0304260205df4725b64724e643059e07e5920724e44305df8825dcc585b44704e24305db0585d8c725d287e5cc8725b24724e043059c07e5900725d6c725d087e5ca8725b04724de43059a07e58e0725d4c725ce87e5c88725ae4724dc43059807e58c0725d94735d70735d50535ac460c4443058a0605d30735d0c735cec434da4205cd4735cb0735c90535aa4604d84305a84705c30705c6c58db28715b68615b2841d7042ec4c42257002e44c0225c58705bf0605c34635c106e5bf0625bac635b8c535b48535bc8495aa8415a8833d6e42ec4a42256e02e44a0225bb470db08715b0851d6c42ec4842256c02e4480225b9470dae8715ae851d6a42ec4642256a02e4460225b78825b54705b34735b10735af0535acc605aa860c444305a94704d60204d40204d24305a68485a446959e45159c4314d00125a246959a4414ce0125a04695984414cc0125a54735a2c735a0c5359f4824ca02059d07359ac73598c434c8020597068594c58d908715928615908414c642258802e42a022d8e87158e8514c442258602e428022d8c87158c8514c242258402e4260225938824c043058203c59147358f07358d05358ac604be43058003c589473586c73584c5358285258083257d07257ec5857647e57007257d47357ac73578c5356e06057b47257447e56c07257947257247e56a07257707357487357284357147356f06056cc7356ac5356906856608c56005c56408c55e06c56208c55c06c567473564c73562c5356147355ec7355cc5355ac6055b060558c7055947055047054e470556c5254c472530452556c4852e46054a470554c6054847252c45255506054647252a452544472528442542472526452552428550c6e54ec6254a841d4046fd3a46353442f54ec70d4886154884154c83954283153242f54b070549062546c6254486e54286254187153ec6e53c839d3846253b87153886e53646ed35871535071533063d2c86152e85152c84153083952683152f05352d06252ac6252886e526862525063d20862520842cf64624f6442cb806fc9806ec72063c5c0624b804f49804e47204345c042524c68d1e88052287051e85051284050c490cf44804f44504c6440c5a08045a05049204c42a040d1c88051c860510850cf24804f24604c4450c5808045806048605c428050d1a88051a86050e850cf04804f04604c2450c5608045606048205c42605052306350a470ce64624e6442cb606fc700634b604f4700435084804e4450523882506482ce24704e24504c044051f072520c5851887e512872504480cee4724e0440c8007ec540724b204d5024704d244051f47351cc7351ac53500472cec4604be440c5206051d47251687e510872cea4724de450c7e07ec500724ae05d51b47251487e50e872ce84724dc450c7c07ec4e0724ac05d5190735168735148434fe4724da430513473510c7350ec534fc472cd84604d844050d073d0487250a860504842caa07fc6e0734aa04f46e0435088625028504fa42d50d881d008705068625008504fc8404f842dd0987150b470509071507063ca806fc6c0634a804f46c0435054715030705010624fe86e4fc8624d24404a604dcfb8714fb0714f9063ca406fc6a0634a404f46a0434f50724f6c584ee8724e68604e08404d047e4c6472c7a07ec4c0724a204d4e48524f54734f2c734f0c534ec8604e28524d8840c4a0604f34724ea8724de8504ce47e4c4472c7807ec4807249e05d4f14724e88724dc8504cc47e4c2472c7607ec4607249c05d4ef4734ed0604eac734e8c534d8840cbe4604e74724e50724e30624d647e4ca46e4c046249a04d4e10634dec634dcc434da85e4d88524d446e4d24624c845e4be452c7405ec440524ba0434180334d64424d44304d28404d10734ce8734cc8434ca4424c84304c74734c4c734c2c53cbe8604c08524be8404bcc6c4ba8504bac504b8c684b68704b28504aa4904a24504220504b48524b08404a04404200404ae86049e46041e0604ac86049c46041c0604b78824b508e4a848249a4504b34734b107e4aec734acc534a64724ab8814a88624a68504a442d4a34734a107e49ec7349cc5349a852494c7e492c7248ec6d422c4d49885848047247a07249747948ac5e420c4c495073488873484843493473490c7e48687348285348f88248d48e48ac8e48907e48707241f05d47e47247807248507e48307241d05d47c47247607248147347e87347c85347406047b473478873476853474460473068470c7046e89042245c46808c41e46c46608c41c46c46408c47188246c88246207c46f88146cc6246a83d46007c45e07c469473466c73464c5346285246047245e05241603245b07245cc5845487244c47244207e43c07d43607c43007542a07242204d45b473458c73456c5345286044a46045947245087244847244007e43a07d43407c42e07542807241e05d45747244e87244647243e07e43807d43207c42c07542607241c05d455473453060450c7344ec5344446044d47344b060448c73446c5344486044307344087343e84343d47343ac73438c5343706343486343284343147342ec7342cc53c2406c41a04c42b473428c73426c53c2406c42404c42347342107e41ec7341cc5341a064418850418c5041647c3fec53b76453376433abc0532bc0334140291de013bdd4713dd052b72471c0a4693ac45337244140a439aba071c02069a780612ba04140203927803122c02920a0213c24714124593aa44336e4313180714100592b803122a02920802140ec6eb7846340c44940b871bdf46340846e40645e40446e4038713a885336c84140006e3fe858b6a4713a646136a4413ee4393e843333e431316081ab60712b60413e60393e003325a0311dc0133fd069b684513a44433684313fa069ab40512b40312280292060213f8c6e3f6c5f3c0471b664613a2453366441314071ab20612b20413f403924c0312260292040213f307e3be4733f04493ef4733c8c733a08523ec45e312073ab00612d20532b00412240392160332020313ea0193e98833e74733c6c73b6486139e8533648413e407e3e202e3e18833c4c83bdb4703dd0803d6c7c3bc481b704713de46939c4513d0439bdb8723db0723ba473bce4593ce4393dd8713db4623b847139a4513cc4393d9469b744533984413d78723d547e3b64733d24593964413d18733cf4623cd0723ca46eb624713624513c844933c441aae0712ae0513c60493c40432580411da013b6047136045133a441aac0712ac0512560411d8013bbd8733b94623c307e3c1072394862bb247e3c10803bf06e3928623b446e3bdc813bb8723b94803b707e390860bb047e3b4c633b38713b14633aec6e3a7063310071aa20632a20431d60213adc81b9d87239b4603ab07e3a3072394880b8847e30e0812a00513a80491d40213a78823a508e3a30823928823a084838c48e38a48330c083a9e0712d006129e05139e0492540412220392000311d202137e01937c01339d87339b47239907e39706e390872b8646eb95871b91462395071393063391051b8f46938ec6938cc5338b473389873387462384c7e382c6e38047e37f06337d473b7a07e37a05e379469373080367060b5c87034e47c36b072376c5835e87234a47e34047333e47230a081aaa07329c0411d002133001932201315001137548e37108234847c37387137146336f06e36706235c86233445e30807136c0492760412200391fe0311ce02132e01914e01136b47336907e367072362c73360c5335a860306073aa80612ce05336404925204121e0392140331fc0311cc02132c01914c01136347235887234647e33c472aa607329a0511ca02132a01932001314a01136147235687234447e33a472aa40732980511c802132801931e013148011b5d87235f47335d07235b060358c73356c53304073a960612cc05329604121c0392120331fa031b2602994602132601914601135546935306935046e34f87234d47e34b0733490613468733448433020733420592ca04329403121a0292100231f80211c601134188333f47333cc7333ac53300073a920612c805329204121803920e0331f60311c402133801913a01133707e334c7233248e33147332f07232d06232ac73328c5332686232406e32388332108331f06331c07c31a05ca90071290051250041317073b0a87331086130a8431c24222fe06d31907e31507230e8633088511f44301c0422af207faec07eae6073a780722fc06f2e002f2dc02e317881315080b0687130c8633068513128493008411f24301be4222fa06f2f806e24c0402de02f2da02eb0fc8131188030f48130d4731bc4302d602c30b881309480307472304c7230287e3008721f04401ba4302f406e276050afdc812ff8802fd0812fb0732f8c63af44632f64492d64412f44332f3c812f107e2ee8491ee4301b8422ae40722ed8712eac6e2e84391b60122e7c811ec8402e447e2e207eae1c812e14812df4731ea4401b4430add8712dd0712db063ad446e2d845e2d64522d444eace8712d08612ce8512d28492c88411e84302c002e2d14631e6440ac406e2c405e2cf4722ccc722ca87e2c88721e44402c6c6e2c44512c24392c1063abe46e2be44e2bb0802b3060a8c47027808027207c24c0602b70722bcc582aa8732a286129c84128e4721b242226e07e26007325a07224602e2360231500222bb8712b906e2b30622a085328c4621b042224402e14e0222b74732b507e2b30722aec732acc532a886129e8532b084929284129083328a4601ae42224202e14c0222af4722a687329a8512884721ac42226c07e25e07325807224002e23402314a0222ad4722a48732988512864721aa42226a07e25c07325607223e02e2320231480222ab8832a94702a70832a5063296c50292850a824701a8430944420a5207014603013a0202a38822a148229f4722844721a643027c08e26607e25407229d47329b073299053296c6229486e2928622824621a443027a07e27607226406e25206229147228047226207e250072a8d87228f47328d07228b060288c73286c53a82861284853282841280833a3842e94442223802e14402227f46927c44327a4311a20122798712768411a042227406e24c06227387227147e26f07326c87326a84326845926644326443126242319e01226188325f08325d06325b473258c73256c53a5286125485325284125083319c42224e07e24c07224a02e13a022248449247473245072243062240c7323ec5323c46e23a45e23806223788323508323306323007c22e05c22d87122ac6e226c62220841228c7e226c72a1e86122285321e84122483921883122306322107221f06221cc6221a86e218862a1487121485121684920e84120c02e215472212c7221087e20e87220d06320b871208c6e204c621fe8411f4470206c7e204c729fc8612008531fc8412028391f68311f24721e84521e002f2010631e64501ff0721fd0621fac621f886e1f68621f04721e44529f54611f4c611f2c539f08531f08339ee45f9ec4531ee43f1ec4331ea42f1e8c539e48531e68411e48331e28391e10631dd0731dec589d08721d68601d08421c24809b24721b244298807f97607e95e07395007218804f17604e15e0431500421d48621ce8501c04801b04501a044014e05017004c1dd8831dac831d8c639cc8701d28621cc8501c48401be4829ae4701ae45019c44094c07014c05016c04c13a0401db4739ca8721ca8529ac4721ac45298407f96807e95c07394a07218405f16805e15c05314a0521d94739c88721c88529aa4721aa45298207f96607e95a07394807218205f16605e15a0531480529d58731d74721d50731d30631bc4729a64621a644219a07f19407e98006f95806318004f1580431d14731cf0721cd0621cac731c8c531c686e1c48621ba4729a84621a444096206e94606218c05317e04d1360339c18711c34711c10711bf0639ba8621bc8521ba8429b846f9b646e9a04621b844f1b644e1a04421b442d19807d97c06f95606318e05f17c04f1560431b34731b10721af0621acc731aac531a88621a68521a48401a247e1a047219e46e19c46296006e94406218a05317a04d13403319a852198480997469971461196c69170c6119444219348e190c5818e48298cc7218cc5298a87218a85297847e95447217845e15445218988318708e184c83182c6318086217e85017c48217a450178062138050132032177473174c7f172c7e170c7216ec6e16cc6216ac5f138c4d16887316685316483b16246216006215f88315d08315b063158c6215688215446213845c13044215207c15147314f07214d06214ac73148c5314686214446214206e14006d13e06c13c06513a06213804d936c72136c5293487213485293247e93047213245e13045211ac6312e8488d44630ec4510d44330b207188e06308e03304a01312d87190746310305212ac6e128c63114c62126c5e124c530f64718d64630ea4530d04411224391204330b007189006308c04111e03911c03307603106802905a02104801311b473118c7e116c73114c72112c5e110c530fa8730f88530f44738ce4610e84530ce44110e43910c4330be4310b44230ae07388a06109a05308a04110a039108033070031066029060023058021046013107873105462103072100c7e0fec6e0f24738d24630e64510fc4390fb0638cc4630cc4438880630880430440130f90638ca4630ca4438860630860430420138f78718f34630f70710f50630f30530e48528ee46e0f045e0ee44e8eb8730ed4728e74620eb0730e90630e70510e48720e247e0e04738de46e8dc4630de44e0dc4430ac0738820630980510820430640390560310400210da0190d80130d78730d54730d34630d10720cf0620ccc730cac530c88620c647e0c44730c246e0c04630be4620bc45e0ba4530aa07388406309605308004106203905e03305403103e0210b80190b60130280110b506387e06307e0438b18710b34710b10710af0638aa8630ac8530aa84305243003c4228a406f8a206e8a00638760620a805f0a605e0a404f0a204e0a004307604209e02f09c02e09b06389686309885109684305043089406e09404e09202e09187308f47308d07208b062088c73086c5308486308285308084107e83307c46203a42207a07e07807307607207406e07206307006206e05e06c02e06a023028022869463068c63066c5386285306484306283306106385e86305e84305c02e85b46305ac63058c5385485305684305483305246205044284e05f04e03f04c02f84987304b473049073047063044c73042c5383e86204085203e84203c47283a46203a44203807f03607e82e06f82c06e82a06382806203405f03205e03005302e04f02c04e02a04302804202603f02403382146302306381d053020c6301ec5301cc4301a86301884301646381245301444301243301042300e06380a05300c04300a03300802900602300402100201300007f 17 5 13 10 1
def q96D : Forest := fun i => decodeNode 10 23 0xe7c582c788c58ef60b1d6d18baa82c751058e960b1cfb1639762c70a838e01891bea0e3786246e6858d9a8e1afb1635b62c6aec58d51091a621234801ce86c58d098b19fd1cb3901ce5f058cb807396b1632ba31e50029c918b19080e71d62c638c58c698b18cd18f1842462ec58c558b18962030cc38e13070c008717da122fa82c5ed068bce8e577c162ed6245d5058b9d8b171518edf42cdbd872b6d8b16dc162daa31daf063b5e0a76bd18ed6831dad053b598b169b122cf82c593463b1a0c763414ec662c58b472b098b15fa122bc62c573463ae28e15bd1c2b662c568c58ac60c15231229a624531060a598b14821228d62c515880a128e340c1c680a38cfec589ed8b13c518e77a384ed4709d68e539312271631cdc8639b906737418e6d631cdac439b509134c1ca66631cca86399506732b16264a394c30639818c730310e6062c4b58809568e32a316252a3949d07e93909125a1624a42c4828588fa8c71da18e3b429c778808dd8b11ad1ca32a38c628528c485b18b1622e62c4574638aa8e114d1c22862c44f46389a8e112d1c224a31c46c6388d8a711a1222262c43e8488718b10cb16216831c2686384d08709b16212831c1cc6e8390c707210e0e014c00c587e28e6fb31a1f562c3e94737c98d0f8e1c1ee00cbcb48c7828e4e880a5d1c413a107e72e100e561c5c9a3839306e7258b0e33161bf01cb78c586da8e6d9b161b0c3835f4636ba0dcd74189ae024b5d4706b68e0d64165a842434d87e6960fcd2d1cda2639b44c5368a0d0d0b161a0a39b3ac586668e6cbd1cd9483032907364e0d0c951cd8f639b1ec5363e8e6c741f98e639b1cc5363b102c572418762c30f881613102c1d1c183a40b0588160611cbff2417e8482fc4395f60c6be41c97b4392f647e5ec8e4bdb161704242dcc635b60c6b6316169a382cec585728e6aca165588342ad873557100aa620153c412a0c585420b0a7d1cd4c839a990535320e6a5b1cd4b621a9747352a0e6a5414d4a62c29187051e8c6a341b94683128c84951a8e0a2d1c144c4128747050e8e6a141cd42829a84c605090c0a151c1414242714734d58e69ab14d35a412690734cd8e699b10d33834262c584bb10495d1cd2a839a550534a98c09551cd26639a4cc534990a49320c92662c24947348a8e490d1c920839a3e87347d0868fd1cd1d83023ac734758a68ec1a11ca39a32c734658a68cd1cd18639a30c534620c087d1c10a6242030603f88507e31b8fb6381f48393ea0e07cc188f96311f286e3e50c47ce1c4f86371f08393e30e27ba1b8f72371ef0713da0c67b20e4f58299e90623cd8c479a1b8f34311e6c683bf104753160e9a399cf47239a8e472c1cce44399c88433928e671b1cce36299c78813828e06fc1c4df8319bf47137a0e06f4188de4371bc86237a0e26dc18cdb62c1b54733628e46bd1c8d6a399ab0603558e66ab14cd5a391a90723520c46a418cd36319a6c4334d0bc69a148d32211a443034908068c1ccd04399a08433408846810c0d0a3999ec7333d8a667a148cf42019ec6c3318a06331a0c5c4118308e3068e66041f8c0639980c533031025fa188bf42817e42d2fe8e65f41f8be63997cc532f90a45f2160bca3c9770732e28e65bb1f8b7c4116d48e2d991c5b41f8b583916b07e2d20e45a51ccb24399648532ca8e658a1ccb14299624602c60d0586208adc40958c622b107a5651ccaa639954c532a90a45511c8aa029154c582a68e653d1c8a6a3914b4732920c05231cca462994947328e0c051b1cca362994686028e0e65121cca24219454732858e650b14ca18319408632810865051cc9f63993ec5327e8e64f31cc9e62993c04c27a8e64ec1f89d63993ac532740c84eb1409b23e1320292608b24b01649663712a4492530e24911b89222f12446e2470e24801b89042c11d0692340d246b1b88c62f91603922e0fc4511248aa3991045e22003244620c87a3990c07e21805c43620c8523490987120a8c44151a481c3910147e2008b24061cc7fa310ff0721fc8dc3f91247e0248fc0431fa0fc3e42007b8370f7c811eb0e43d52007a83f0f4c631e70e23c518c786370f1c811da0fc3b012476c410eb08e1d61043aa120750248eb8731d28e43a41f8748370e90711ce0c639c144736348e4c531ca8e638e1cc70a310e0c7e1c18dc3811f86f8318dd4731b40bc36d1a46c62c0d748e1ab0e234d18c698370d20491a68e63441f8688390d00491a28e433d1c866a398cb0721960c032b1cc656298cb4691920d23211b863c390c547e18a0e6314184624398c48431880b231620c61a398c0c731818a63000646083f0bec7217c91c2f51cc5d8390bb0621758e62eb14c5d4310ba06e1771062e420c5c8318b807c1700b82e41f859c408b10801610922c620057a408af47315f1022b520056a390acc721590fc2b21c856c400ab0811560e62ab18c542248a843315390229c1f8534248a78711498dc2910e452e408a247e1440fc28d20450a398a107113e0c62791784f22909e44e13d09227518c4da39098c721310fc2621c84c63709645112c87225c18c4a227094c581230e223c1b847a3988d07e11a0e423212446a3908b47211310621d1c04384188706310f10421520842a390854731060e620c14c4163108286e1050c420d1c840a3987f0720fe0c01fb1cc3f62987e8530fd0821fa0cc3fa3487c4430f88621f61c43c42087806e0f30e41dd1f83b8398768730ed0861d91643b2218764310ec8461de20c3a8418750630ea8e61cb1cc396298728530e50821ca0cc3903f0720720e405c1c912438a3986f0720de0c41bb1cc3762986e46e0dc8bc1b818837c4186d0830da0c61b01f03602e06d8710d58dc1ab1f8346390688390d20c619c1c832831064c620c90dc192188324248634720c18e41821f8304390610630bf0e21731b82e63f05ac720b507216c18c2c8390570620ad8c415a1b82b431056c610a98a61520cc2a21f8544330a885e15314c294208528330a507214418c2762c04d8830928e611d1cc22a390430730860c610d1cc208390410620818e610314c204370408620828e20fc1c41f83183e85207d0840f913c1f22703e42d07e8e60f41c81e83103cc730798a60f21881e42903c8400788fc0f11c81e23703c4620790a40e92001d63483844207291c0db1601b241036c520650a40ce20c18847030c830618c60c2188184280304820608a00c018818a3982ec7f05d8fc0bb1c81763702ec6205d8be0ba1cc1742982e83b05c8c40b818817c4182d08305a0c60b31881644102c4620580f80b51cc1583902b0620558e60ab14c1543102a4620540dc0a81b41503602a0650540c40a81341562902685204c8bc099148134240258710458dc08b18c1162f022c530448720890cc1101c8220330468e60831f810639820c720418bc08314c1021c8204330400720800cc10c3981f46203e0e407b1f80f63701e43903e0c607418c0d8388190630320a60611780c22701947202e0e605c18c0b82881687202c8fc0591cc0b22701644302c03205804c0bc3981547302a8c60541c80a831014c730298a60521880a23f0144730288dc05118c0a23101445e0288a60500640a0098150630268e20441c40883181085302108604017c0802f01004f02009c04010c0801781002e0220c603a1440742180e04e01c05c03e1cc06a3980d07201a0c40331cc0662980c8630190a60321040641980c4620180fc0301cc0603900c06e0180c60301880602f00c02e01804603318c0562980a84301506602c18c0442180802e0118c601b14c0342180683300c8c40191080301f80602f00e8e60141cc02831804c730098a6012148024210044720088840101fc0203f00405f0080bc01014c0202780404e0080860101080201f80403300a0c600b18c01629802c430050c600a10c0123180244300486600908c010318020430040660080a4010118020210040260081fc00 i
def q96T := dagTraceTagsBin q96M 123 (dagTagBases q96N 0x1ae3e6ffab03e1d8eff08436fdcdf99df29fef8e9dafbfd77e4b7127de7bcfd5bf97ff77f029bcdee083fe3c70ffefc02c003fbb6f83e27ba4e0f9fbe3ffc7fffffb62456b15d5fff13ce3fbcfdff51a57d937ca0ffe1ffffc20ffff88f7c4b5f4ffeffe8003fffffffa9888 0x1ffdf6df6b3ffddeeff69cb7fdfdf99cfeffffcd7dafbfd77f137737dffbcfceffa6fb777d29bedee58ffefc7bffef047dcdeffb6fe3f27bb263fafbf5fec7f3ffbb6e0b7b15c4fff49ceffbe7f7ffbeff79b7c67fff1ffffc967fffd7fffffffdffeffe57dffffffffacdfd 123) 12 q96D
def q96St := dagTraceBin q96M q96N 12 q96D
def q96Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q96Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q96Mv := dagMoves ([([qS11], q96Mp0, q96Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96A : DagMovesOK q96M q96G 256 q96Mv := dagMovesOfCheck (by decide +kernel)
def q96NB : Nat → List Bound := dagNodeBounds q96C.toArray 0x10dc186e0437021b810db186d8436c21b610db086d8436c21b610db086d8436c21b610da186c8c36421b210d9086c8436421b210d8186b8c35c21ac30d248688c34421a030d008678c338619c10cd186684334219830ca28639c310e18810c3186184308618230c108600c2fc617690b9285c842d8e16670b308590c2c8216410b02858042c0215e30ae18568c2b0615810ac0856042a8a15230a90854842a0615010a808540429c614690a2184f9c270e138109b184d0c260a1301096284a8c254212a1094184a042502124508e48459c22c211610892844842242110308718430c218210c108518420c20c6106108308410c20461021080183f141f460f8307b183d0c1e460f03078083c041d8a0ec10751839941c4a0e0306f18370c1b0a0d6306a18348c19ca0cc306518320c19020c8106408318c18860c4106208308c18420c21060182f8c17860bc105e082bbc14d20a0704c482424118a084903f381e940eca06cb03338181c0b1204eb02438109c078e036701928093c03560183006680123fe65fea8ff057f623fa11fca6fe327efa3f749fb64fd657e99bf40df9a6fc587e11bef91f784fbb17db2bed09f608fae27d613ea89f522fa817d38be985f466f9e57cd23e5cdf286f8d77c4a3e18df066f8127bea3de8deee6f7437b89bdb51ed46f6917b393d895ebe6f5c37ababd495ea04f5007a713d309e962f4a17a39bd10de7eaf3e179f03cf81e748f39179c0bcd89e6a2f34179733ca91e450f1d578c2bc511e1eaf0c37849bc061dfc6efe077f03be91deaaef2377723ba91dce6ee437709bb7c9dbc2edd176d1bb4a1d9e6ece17668bb305d8eaec4376113b009d76aeb9275aa3acc9d642eb117571bab09d544ea82751aba8c1d460ea0374e9ba6c9d324e97274b0ba545d228e8d474593a195d066e80373e239e4dcec6e724737239acdcd06e6537311b9809cb88e59372b1b9509c9eae4c37233390cdc806e3d371d1b8d91c62ae2c57158b8ac1c560e2747130b8945c464e2217108b8715c308e162709238319c0eae0437009b7f8dbf84dfa26faab7c8dbe40df206f79b7a95bd40dea06f3237909bbeadd786e92b7355b90adc356e0936f51b70adb536da0b6cc5b5cada866d3136945b482d9f56cd2b6609b26ad9036c69b628db122d8636c28b6105b008d7d36bd1b5e45aec6d7336b90b5c45ad8ad6756b2935851aba8d5856ab135545aa46d4f36a61b524da8a8d4326a10b5045a7c6d3d169e0b4e11a688d2f56952b4955a446d1d568d93460da24cd0d5684a3409da004cff167f0b3f099ecccf5167a0b3c4d9d6ccea16748b39159c08cdd366d1b35919a66cd0366533320998c4cc33660932fc99786cba265c132d119662cb216588b2c059588ca846531327dd9386c99364b93249591e6c8a56439b21499046c7d563bb31d498e0ac6d36351b19558c28c5d462bb315498a28c4b6622b310158788c366619230bcd8586c2a26141309898466c1f460e1b06898304c14460823029980e6c0255ff22fe557ea8bf235f79afa1d7c88be135ef1af6917ae6bd345e45af099778cbb755d9a2ec0d75c4bab35d3a2e81d7310b9445c912e2dd708eb8135bf1adf096f26b7635b7bada956ce6b6345aeb2d6516aa8b5055a69ad25167f4b3b459b2acc9165c8b2b3590d2c7156290b1045869ac28d60c8b04258022bed55e52aef3575a2b9d15c2cadc556862b3115908ac4456022aed55724ab275579aaa5954a8aa1454db2a5d1520ea8c454422a0d54fe8a7a5538ca9ad94caca5e752caa949d4950a44651eba8d6145cea286511aa8795430ca0f95043a80213f889f934fb1a7c913de69ec34f2ba78513b8a9d844e9aa73d1390e9c264df226e9136e69b074d5aa6995342a99c54cc9a651531ea98874c1aa5f592f2897634b6ca5a152c6a95f44acb255512a0a94a64a3225091278c9393498c24a61246c91d648bb24459216c908347fca3e591e128ea6472aa37251aea8d434689a338d19488c64460aa2f8d17488b554573a2a5514a889e744b4223dd11868866440aa1f510e388698431b217590b0a85534282a129908aa841441d3a0dcd062c82c5413aa0895040481b540ab20415016a806540031ff4cff647f833fa99fcc8fde87ec33f421f8d4fbe87dc33ec21f510fa087cc43e421f110f8267bf23de19ee4cf6a87b053d699ea14f44c79d53cc29e498f15078193bdb1dd94ee2a76a73b0c9d660eae475343a729d1dce82c73a739aa9cc50e512720838da9c594e20c70a638231bf98ded06ee837341b818dad46d33367a1b294d8326bc535b31ac18d54c6a4634cd9a424d188686633f419e18cea66714336a19a50ccc6664232fa9961cca2e64a7321418f54c6ec62f8315a188e0c3ac6176306d18250c0305fc52fb317bdcbd4a5e462ef3176ccbaac5d052e3c97058b7305afa2d3c16858b38a591b2c6296198afd057682b7b95a58ac8a55e62abb95494a9aa54942a2294fd4a7865384299a94a68a43051b628ab14414a12e503627d493d189d364e0926cb9333498ae4bf625bc12be094b449c924a41235c910a482623db91ce08d8e466622f4114ec8970444721e410c6c847c416d206c9019c802a3f981f938fb187c543dd51e9d0f22c782e3b7a1d748e9dc740e39791c8b0e2d8707037c71b770d9a06c0c356a1a6c8d21467d4332c192e8c76061de307717ed0bdd85dd22e4a16f30b4ec58f82bcb158d8aa9c5432297a146d0a0704ed626f713438985c4a7c248b121308db04594225710c6883e440f01f8f0f7c879a43bd01d770e6d0712437541b190d448685c334e18fb0c3485eec2eca16f70b4b0589c2b1414f90a2d04fd8272c12dc091d0462c21d4107707f483ddc1dd20e1d06cc033ac18940b6e059982ae01416095b0455820dc0fac07760383819300b180535024580fa8063a02890104005e4013c0009 0x41cf3c71843c24041c908f1d36013440440550111c94c23cb1001c701900f0c70074105871c23c74c40c10000030440432531001400071c05842421401c01d01c758c1d60d33032c610618718330d2182033cf3c71c73cf1c71c73c91d31c32d64c62440904c23c700370450f25608f00774444f6402c00c32cd0583c200f0c23c020508020458201600b5852c500b8010830062d340910240250f18771458218410214034114f00c0c40840020c40d408028f0071010871c13c20062425021420091c01432450c91437143dc1904c450f0801c124f0943c71ca00e1c30071915091471431433034d334100d10160060d06a34174d10134a1010020cd04014d04035304404d1012410031000c60551015410050c10032000c405600711354d3c010108d0d13c21890077114471c71c08403c34144422472450072491cb4d375108610b10214068800f48310210b0020c42c30802803c31c910109304f1cb65404720200e0c500728e1c328e0070c30471900914071433050cc1431c21501cc31d44f7462564443c208c00c1c72803870c72c20424c13831c10000503c244f1c71c70030030030072803870c64543050c50c50cc2d34c40021c40c11c10041c00430010c30401130400c10130451950401050400011400431804c04c54c51460400c04c504015330810300100f34c1030401810c40430011400431164cf10f1d30045160891c91401c92472d34cd20458018408b2c560810034401209504b54214a0c028500a0c04c51004444d00880071401ca00e1c310c08b2c53881c00cc00d1032140871090421c424108a38714028e0070cb0cb1420d42c30854081cc30e20714028500e1c320c1c738800c0ca00e1c308304c14d0d64c44cc0cb58330a8031c73482d56080ca4030c830b7cb0d34cc2c838340624408b0861c00c41cb4c404b4c30c27df2c21800c40531800c42d30c61c618600718628e1c319111418c1140cd1912036062050c614334c0880c108108360c04838334804a0c108d0d01141912423c71c73c729100e1c31c73c01ca5003870c71ca14e1c31c50031400c500330f1431c50c71433101490c20420421c50c50c50c700300300328e1c33034d328e1c31050430c124b19011308508014200214b02a1420850012c308004214214214004b0c200f40918408b3c12d508310200408004b5420080db2c804b0cd4080013c03ca00f0dc1143c01c85890013c12c308028f00774444300f3c008584214414b0800800851420060053c53c00853c04c10872410877444470032010045080402162c71880021541402d60851420060032040a01820053c05850801021400021485852cd04b3c76065d010210b5820cf2042d60806080c23c22003c500b14b8852c114b01918b5852021832d600420208814b14b1800c810262020404b5828405855807d614200300b1010803580e41180c00c52c584200640911408508f00608014650214064200b64214d04750f1434060860020c60d408028f0071810873c11dc35404830318409c2840852863901440071010873c11c00833c500b0852c304004b0c214d0471402465020c10090421c91c13ca24e1c501c50f14770d4140473c61080c24c10874c204728e0070c050b4c05052c214f1c014950250114a5003870c90421c90811ca1403870ca3801c64541c914344314744314728e1c314a38c0cd0450803481954c010904d10148200d2810800d834610140b3480452cd1012036003460041495413422d504534a0460020cd2840450020cd28100214334a0420031840554cd1815533440d54c13465530c9100046005110a821801050c90551850130131444c519300501315f2c56460420151400c54c10855402021532048000c804b14c1012020031810845531845530c12c53403cc10108334018130d0c40423430423450010833400131433412c504b21314404234390004335315119010908608014508068844f1431890862c008318348200a00f0c94471810912413c701c15129100e1c314044714044719030408b2052c604708020e0cc0101515090911cc2410911cc24108a1403870ca24e1c500a24e0070c304769121d48018409748a10215a48a38811b14019d4440427514c13d404720214038328e1c50070400c20162c32c50834420052c35021450802c304004b0c215a20519009118c0510913013ca4003871433880470801432901403870c004569d44f1437511c50dd4413da74620f59110024309d1894441c109d4491c13ce20130300a00e3030c11c12c008320b0e608028e1c00c134b0cc3c040544244114a4403870cc1c144230704244a3870032c528e1470063115050c64471433d11c50ca38c0c57ca2ce3031820020040831020003c40803cc0851800871050021c00851c20070c100f0c60471030471c50400c00471030401810010040431010070010cc10004330114600c0431071400431c01410c91c00437862041412005531840c11902130045450461087854c64440551842154d230610d0015d84902c610d0521804043450411440010c611024234430020f0c40562001c405609300718c1022d520b1581013c73880c010034c15424264b28214a00e1c31161c90421161c90422893871402893801c334614020454248d20211504534c20404a0c060620454b34a04810b54200521314420b1465442133513002051100920c80852883801c34444cc0424444cc04228e14700348e54404c21800b15228838424c14048a08350354808529020500e1c328800e3035432c90550c61420c81402c20cb0432010832d80421053439012cc14d0cd0c810c2c234a0562c27c31d31010870814c40d830b0483960ca38c0cd28b4080530d228e20c0cb3c108d0d030b0067c310909f0420c604b4000c27ca04b0832863870032842ce0470df3810833062440423062440424c10ca1803870ca18e1c034644c1140880c64441c10864440421c50d818c1140483850cd1912012850c604214d0ca20e30344c1140064052430862c304528600e1c319110930704244424f3070422911403870ca50e14700a38714028638c0c528e2503050ca3870c528e1c00ca38c0c71050438c41410c70431850431901090a164d20508418100d51704608066105b0991571904990a248108519004808566005409915721c48904215934279904568d20148640911b08d28450120309b6418446c20216d948d50a2011060801142c30929623849403ca0502023c36dc2846d43c01cd2885012420cf6dd6ca44424f0c08481621920025c61000523c61121422064120a25060520808864080520858961891011c210c08904f64640c10804548a1a04160040481e21905122050974861088024865012021605d234630140460b0976523554011882d810509234e21819b40b1000475d840b10c14148c2d61842021842180a01880440962c650148215888650460b5d22423461012d81a71182e148a10220650100d30100819024450222519250101234a18265050114a18e6c551000718c24404708f3091011c228639c1541001c100620252064150215728e04c24651b29c3941476dc48a1813885101020075c10060922d462205408534824194a3870142864543891c314424c0475d23462044d524179765234620224404578d28654804b25b10200d1981012152de28655424d2c80444000853462440554cd55748640911305e1881054d22849482c115e64a189782101155182108553b5e2950862040502d238c26418b0443cd0176120861090502cd1a448424140008d15770d0421645d234218440191784a11208644101a20048640425109748a18234864944115a48620a3911496c018c1090510843093c144229c39130014639055148810c2400452d228839150c24540010724c1415dd48a44e19a20414048d28170800309179948144215765521e49c2890440855ca20e05a40645a75b29138315d6cd1880e644424a39a1405c12dc00d0c244a20140638c01128650e44c0c530810624509a21218c2440803d74962cc18424248620500c10908730902318468304624502310c0c1ae618432304c2041891416a348c2031891010176122d01842418d218c2100091011462044015d219010d06818c16306b9861108c130800634511024265234a30420114d2843886c13000c610c24108610c0890675d218830460124e2d228810e30025415748d18810229540148a44e10c21000534a5012020d034501b04808338c2019c20d749b3813430a791818e1022454013402d228110e20c0c905219000a38c10528644810e50c14335120450118940a38c0053010e318424530005769234620140424265234a20609024406848a38605025a11b18e40210148630424108630424108a40610c2015d848d390206109301a1240852918a38910c18424c05748d1882821102415d218239010904da171884a968a40938445769220610c242b296864042415da48621010906b99748d18804e40428932ca5a286390109 17 4 6
def q96Ck := dagCheckNodeBin q96M q96G q96NB 993 q96St q96Mv q96L q96S q96T
def q96RA (token : Nat) : Bool :=
  let s := rootState q96N 12 token
  !dagAllowedRootBin q96M q96E s.2.1 || dagLocalBin q96M q96G (dagKnownClosesBin q96G q96C) s ||
  dagRefBin q96M 993 q96St q96Mv (fun p tok => dagFindLink (q96L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96RB0 : treeBlock 0 64 q96RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96RB64 : treeBlock 64 64 q96RA = true := by decide +kernel
theorem q96R : dagCheckRootsBin q96M q96G (dagKnownClosesBin q96G q96C) q96E (dagRefBin q96M 993 q96St q96Mv (fun p tok => dagFindLink (q96L p) tok) 0) q96N 12 = true := (@treeBlock_merge 0 64 64 q96RA q96RB0 q96RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B0 : treeBlock 0 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B16 : treeBlock 16 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B32 : treeBlock 32 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B48 : treeBlock 48 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B64 : treeBlock 64 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B80 : treeBlock 80 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B96 : treeBlock 96 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B112 : treeBlock 112 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B128 : treeBlock 128 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B144 : treeBlock 144 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B160 : treeBlock 160 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B176 : treeBlock 176 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B192 : treeBlock 192 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B208 : treeBlock 208 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B224 : treeBlock 224 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B240 : treeBlock 240 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B256 : treeBlock 256 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B272 : treeBlock 272 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B288 : treeBlock 288 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B304 : treeBlock 304 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B320 : treeBlock 320 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B336 : treeBlock 336 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B352 : treeBlock 352 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B368 : treeBlock 368 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B384 : treeBlock 384 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B400 : treeBlock 400 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B416 : treeBlock 416 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B432 : treeBlock 432 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B448 : treeBlock 448 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B464 : treeBlock 464 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B480 : treeBlock 480 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B496 : treeBlock 496 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B512 : treeBlock 512 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B528 : treeBlock 528 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B544 : treeBlock 544 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B560 : treeBlock 560 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B576 : treeBlock 576 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B592 : treeBlock 592 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B608 : treeBlock 608 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B624 : treeBlock 624 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B640 : treeBlock 640 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B656 : treeBlock 656 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B672 : treeBlock 672 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B688 : treeBlock 688 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B704 : treeBlock 704 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B720 : treeBlock 720 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B736 : treeBlock 736 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B752 : treeBlock 752 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B768 : treeBlock 768 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B784 : treeBlock 784 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B800 : treeBlock 800 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B816 : treeBlock 816 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B832 : treeBlock 832 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B848 : treeBlock 848 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B864 : treeBlock 864 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B880 : treeBlock 880 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B896 : treeBlock 896 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B912 : treeBlock 912 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B928 : treeBlock 928 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B944 : treeBlock 944 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B960 : treeBlock 960 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B976 : treeBlock 976 16 q96Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96B992 : treeBlock 992 1 q96Ck = true := by decide +kernel
theorem q96Bk : treeBlock 0 993 q96Ck = true := (@treeBlock_merge 0 512 481 q96Ck (@treeBlock_merge 0 256 256 q96Ck (@treeBlock_merge 0 128 128 q96Ck (@treeBlock_merge 0 64 64 q96Ck (@treeBlock_merge 0 32 32 q96Ck (@treeBlock_merge 0 16 16 q96Ck q96B0 q96B16) (@treeBlock_merge 32 16 16 q96Ck q96B32 q96B48)) (@treeBlock_merge 64 32 32 q96Ck (@treeBlock_merge 64 16 16 q96Ck q96B64 q96B80) (@treeBlock_merge 96 16 16 q96Ck q96B96 q96B112))) (@treeBlock_merge 128 64 64 q96Ck (@treeBlock_merge 128 32 32 q96Ck (@treeBlock_merge 128 16 16 q96Ck q96B128 q96B144) (@treeBlock_merge 160 16 16 q96Ck q96B160 q96B176)) (@treeBlock_merge 192 32 32 q96Ck (@treeBlock_merge 192 16 16 q96Ck q96B192 q96B208) (@treeBlock_merge 224 16 16 q96Ck q96B224 q96B240)))) (@treeBlock_merge 256 128 128 q96Ck (@treeBlock_merge 256 64 64 q96Ck (@treeBlock_merge 256 32 32 q96Ck (@treeBlock_merge 256 16 16 q96Ck q96B256 q96B272) (@treeBlock_merge 288 16 16 q96Ck q96B288 q96B304)) (@treeBlock_merge 320 32 32 q96Ck (@treeBlock_merge 320 16 16 q96Ck q96B320 q96B336) (@treeBlock_merge 352 16 16 q96Ck q96B352 q96B368))) (@treeBlock_merge 384 64 64 q96Ck (@treeBlock_merge 384 32 32 q96Ck (@treeBlock_merge 384 16 16 q96Ck q96B384 q96B400) (@treeBlock_merge 416 16 16 q96Ck q96B416 q96B432)) (@treeBlock_merge 448 32 32 q96Ck (@treeBlock_merge 448 16 16 q96Ck q96B448 q96B464) (@treeBlock_merge 480 16 16 q96Ck q96B480 q96B496))))) (@treeBlock_merge 512 256 225 q96Ck (@treeBlock_merge 512 128 128 q96Ck (@treeBlock_merge 512 64 64 q96Ck (@treeBlock_merge 512 32 32 q96Ck (@treeBlock_merge 512 16 16 q96Ck q96B512 q96B528) (@treeBlock_merge 544 16 16 q96Ck q96B544 q96B560)) (@treeBlock_merge 576 32 32 q96Ck (@treeBlock_merge 576 16 16 q96Ck q96B576 q96B592) (@treeBlock_merge 608 16 16 q96Ck q96B608 q96B624))) (@treeBlock_merge 640 64 64 q96Ck (@treeBlock_merge 640 32 32 q96Ck (@treeBlock_merge 640 16 16 q96Ck q96B640 q96B656) (@treeBlock_merge 672 16 16 q96Ck q96B672 q96B688)) (@treeBlock_merge 704 32 32 q96Ck (@treeBlock_merge 704 16 16 q96Ck q96B704 q96B720) (@treeBlock_merge 736 16 16 q96Ck q96B736 q96B752)))) (@treeBlock_merge 768 128 97 q96Ck (@treeBlock_merge 768 64 64 q96Ck (@treeBlock_merge 768 32 32 q96Ck (@treeBlock_merge 768 16 16 q96Ck q96B768 q96B784) (@treeBlock_merge 800 16 16 q96Ck q96B800 q96B816)) (@treeBlock_merge 832 32 32 q96Ck (@treeBlock_merge 832 16 16 q96Ck q96B832 q96B848) (@treeBlock_merge 864 16 16 q96Ck q96B864 q96B880))) (@treeBlock_merge 896 64 33 q96Ck (@treeBlock_merge 896 32 32 q96Ck (@treeBlock_merge 896 16 16 q96Ck q96B896 q96B912) (@treeBlock_merge 928 16 16 q96Ck q96B928 q96B944)) (@treeBlock_merge 960 32 1 q96Ck (@treeBlock_merge 960 16 16 q96Ck q96B960 q96B976) q96B992)))))
theorem q96K : KnownBin q96C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q76Bin) q95Bin) q82Bin) q53Bin) q93Bin) q83Bin) q74Bin) q81Bin) q49Bin) q66Bin) q61Bin) q48Bin) q71Bin) q69Bin) q52Bin) q75Bin) q67Bin) q45Bin) q46Bin) q89Bin) q70Bin) q68Bin) q80Bin) q4Bin) q54Bin) q44Bin) q2Bin) q79Bin) q65Bin) q88Bin) q5Bin) q91Bin) q64Bin) q62Bin) q10Bin) q92Bin) q87Bin) q63Bin) q3Bin) q94Bin) q9Bin) q90Bin) q0Bin) q41Bin) q43Bin) q8Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96Bin : BinLower q96M q96W q96G 13 := by
  apply lowerDagBin _ _ _ _ q96A _ _ _ q96K _ (fun _ b hb => dagNodeBounds_mem b hb) q96R q96Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q96C.all (fun b => q96M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q97M : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev q97G : Word := qGoal &&& q97M
abbrev q97W : List Word := projectDAGStock q97M qBase [0, 1, 2, 3, 4, 5, 6, 7]
def q97E := unpackWitnesses q97W [82592, 345248, 608416, 872608, 1138848, 1366092, 1687712, 1951844]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97Bin : BinLower q97M q97W q97G 14 := by
  apply essentialLiftBin (witnesses := q97E) (cut := q96M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := q96W) (by decide +kernel)
  · exact q96Bin
  · decide +kernel
theorem binLowerEq {m m2 : Word} {s s2 : List Word} {t t2 : Word} {k : Nat}
    (hm : m = m2) (hs : s = s2) (ht : t = t2) (h : BinLower m s t k) : BinLower m2 s2 t2 k := by
  subst hm; subst hs; subst ht; exact h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootLower : BinLower (fullMask 256) qBase qGoal 14 :=
  binLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) q97Bin

end PEqualNP.Outside.L_meta_32836.Cert

namespace PEqualNP.Outside.L_meta_32836

open PEqualNP.CircuitLowerBounds

def upperGates : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [15, 14]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [18, 13]⟩, ⟨.and, [21, 20]⟩]

def graphList : List Nat := [0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]

def edgeValue (s : List Bool) : Bool := decide (∃ i < graphList.length / 2,
  s.getD (graphList.getD (2*i) 0) false = true ∧ s.getD (graphList.getD (2*i+1) 0) false = true)

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem upper_sem (x : Fin 8 → Bool) :
    Circuit.eval ⟨upperGates, 22⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  have h : ∀ a b c d e f g h : Bool,
      Circuit.eval ⟨upperGates, 22⟩ [a,b,c,d,e,f,g,h] = edgeValue [a,b,c,d,e,f,g,h] := by decide
  simp only [List.ofFn_succ, List.ofFn_zero]
  apply h

end PEqualNP.Outside.L_meta_32836

namespace PEqualNP.Outside.L_meta_32836
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_32836.Contraction

def truthInputs : List (BitVec 256) := Cert.qBase.map (BitVec.ofNat 256)
def truthGoal : BitVec 256 := BitVec.ofNat 256 Cert.qGoal

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem countBinary (lb : BinLower (fullMask 256) Cert.qBase Cert.qGoal 14)
    (gates : List Gate) (o : Nat) (hfan : FanInTwo ⟨gates, o⟩)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    14 ≤ countNonNot gates := by
  let eb := gates.foldl hcsStep truthInputs
  have same : eb.getD o 0 = truthGoal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let x : Fin 8 → Bool := fun k => j.testBit k.val
    have hbank : ∀ i : Fin 256, truthInputs.map (fun v => v.getLsbD i.val) =
        List.ofFn (fun k : Fin 8 => i.val.testBit k.val) := by decide +kernel
    have hgraph : ∀ i : Fin 256, truthGoal.getLsbD i.val =
        edgeValue (List.ofFn (fun k : Fin 8 => i.val.testBit k.val)) := by decide +kernel
    have bits := hcsFoldBits truthInputs ⟨j,hj⟩ gates hfan
    calc
      (eb.getD o 0).getLsbD j = (eb.map fun v => v.getLsbD j).getD o false := hcsGetDBit eb j o
      _ = edgeValue (List.ofFn x) := by
        dsimp only [eb]
        rw [bits, hbank ⟨j,hj⟩]
        exact he x
      _ = truthGoal.getLsbD j := (hgraph ⟨j,hj⟩).symm
  have hroot : truthInputs.map BitVec.toNat = Cert.qBase := by decide +kernel
  have hr : ∀ v ∈ truthInputs, AvBin (fullMask 256) Cert.qBase v.toNat := by
    intro v hv
    apply Or.inr (Or.inr (Or.inl ?_))
    rw [← hroot]
    exact List.mem_map_of_mem hv
  obtain ⟨vs, len, built, reach⟩ := hcsBuildsBin truthInputs Cert.qBase gates hr hfan
  have av : AvBin (fullMask 256) (vs ++ Cert.qBase) Cert.qGoal := by
    rw [show Cert.qGoal = truthGoal.toNat by decide +kernel, ← same, List.getD_eq_getElem?_getD]
    cases h : eb[o]? with
    | none => exact Or.inl rfl
    | some v => exact reach v (List.mem_of_getElem? h)
  exact (lb vs built av).trans len

theorem finish (lb : BinLower (fullMask 256) Cert.qBase Cert.qGoal 14)
    (gates : List Gate) (o : Nat)
    (hg : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    ∃ (out : List Gate) (p : Nat),
      (∀ g ∈ out, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ out.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨out,p⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hfan : FanInTwo ⟨gates,o⟩ := by
      intro g h
      obtain ⟨hop, len⟩ := hg g h
      refine ⟨?_, len⟩
      rcases hop with h | h | h <;> simp [h]
    have floor := countBinary lb gates o hfan he
    have used := countNonNot_le_sub hn
    refine ⟨upperGates,22,upper_shape,?_,upper_sem⟩
    change 15 ≤ gates.length
    omega
  · refine ⟨gates,o,?_,Nat.le_refl _,he⟩
    intro g h
    obtain ⟨hop, len⟩ := hg g h
    refine ⟨?_,len⟩
    rcases hop with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · exact (hn ⟨g,h,h₃⟩).elim

end PEqualNP.Outside.L_meta_32836

theorem PEqualNP.Outside.L_meta_32836 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ hu
  apply PEqualNP.Outside.L_meta_32836.finish _ gates o hg hu
  exact PEqualNP.Outside.L_meta_32836.Cert.rootLower
