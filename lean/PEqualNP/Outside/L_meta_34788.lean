import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34788.Contraction
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
end PEqualNP.Outside.L_meta_34788.Contraction

namespace PEqualNP.Outside.L_meta_34788.Cert
open PEqualNP.Outside.L_meta_34788.Contraction

def qS0 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def qS1 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def qS2 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def qS3 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def qS4 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def qS5 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def qS6 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def qS7 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def qS8 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def qS9 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def qS10 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def qS11 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def qS12 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def qS13 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def qS14 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def qS15 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 4)])
def qS16 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 16)])
def qS17 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 64)])
def qS18 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 1)])
def qS19 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 8)])
def qS20 : WordMoveStep := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def qS21 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def qS22 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def qS23 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555, 0), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0x5555555555555555555555555555555500000000000000000000000000000000, 127)])
def qS24 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def qS25 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def qS26 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333, 0), (0xcccccccccccccccccccccccccccccccc, 126)], [(0x3333333333333333333333333333333300000000000000000000000000000000, 126)])
def qS27 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def qS28 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def qS29 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def qBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def qGoal : Word := 0xfffffffffffffffffffffffffffefffefffffffefffffefcffeeffeeeeccaa00
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
def q1M : Word := 0x500050000000000050005
abbrev q1G : Word := qGoal &&& q1M
abbrev q1W : List Word := projectDAGStock q1M qBase [1, 4, 6]
def q1F : Bound := (q1M, q1W, 4, q1G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1Bin : BinLower q1M q1W q1G 4 := dagShiftLowerBin (width := 256) [qS3, qS4, qS5] q0Bin (by decide +kernel)
def q2M : Word := 0x30300000000000000000000000000000303
abbrev q2G : Word := qGoal &&& q2M
abbrev q2W : List Word := projectDAGStock q2M qBase [0, 3, 7]
def q2F : Bound := (q2M, q2W, 4, q2G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2Bin : BinLower q2M q2W q2G 4 := dagShiftLowerBin (width := 256) [qS6, qS7] q0Bin (by decide +kernel)
def q3M : Word := 0x30000000300000000000000000000000300000003
abbrev q3G : Word := qGoal &&& q3M
abbrev q3W : List Word := projectDAGStock q3M qBase [0, 5, 7]
def q3F : Bound := (q3M, q3W, 4, q3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q3Bin : BinLower q3M q3W q3G 4 := dagShiftLowerBin (width := 256) [qS0, qS8, qS6, qS7] q0Bin (by decide +kernel)
def q4M : Word := 0x50000000500000000000000000000000500000005
abbrev q4G : Word := qGoal &&& q4M
abbrev q4W : List Word := projectDAGStock q4M qBase [1, 5, 7]
def q4F : Bound := (q4M, q4W, 4, q4G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4Bin : BinLower q4M q4W q4G 4 := dagShiftLowerBin (width := 256) [qS3, qS0, qS8, qS6, qS7] q0Bin (by decide +kernel)
def q5M : Word := 0x1010000010100000000000000000000010100000101
abbrev q5G : Word := qGoal &&& q5M
abbrev q5W : List Word := projectDAGStock q5M qBase [3, 5, 7]
def q5F : Bound := (q5M, q5W, 4, q5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5Bin : BinLower q5M q5W q5G 4 := dagShiftLowerBin (width := 256) [qS1, qS9, qS10, qS0, qS8, qS6, qS7] q0Bin (by decide +kernel)
def q6M : Word := 0x5000000000000000500000000000000050000000000000005
abbrev q6G : Word := qGoal &&& q6M
abbrev q6W : List Word := projectDAGStock q6M qBase [1, 6, 7]
def q6F : Bound := (q6M, q6W, 4, q6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6Bin : BinLower q6M q6W q6G 4 := dagShiftLowerBin (width := 256) [qS3, qS11, qS12, qS6] q0Bin (by decide +kernel)
def q7M : Word := 0x11000000000000001100000000000000110000000000000011
abbrev q7G : Word := qGoal &&& q7M
abbrev q7W : List Word := projectDAGStock q7M qBase [2, 6, 7]
def q7F : Bound := (q7M, q7W, 4, q7G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q7Bin : BinLower q7M q7W q7G 4 := dagShiftLowerBin (width := 256) [qS13, qS14, qS11, qS12, qS6] q0Bin (by decide +kernel)
def q8M : Word := 0x303000003030
abbrev q8G : Word := qGoal &&& q8M
abbrev q8W : List Word := projectDAGStock q8M qBase [0, 3, 5]
def q8F : Bound := (q8M, q8W, 4, q8G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8Bin : BinLower q8M q8W q8G 4 := dagShiftLowerBin (width := 256) [qS15] q0Bin (by decide +kernel)
def q9M : Word := 0x303000003030000
abbrev q9G : Word := qGoal &&& q9M
abbrev q9W : List Word := projectDAGStock q9M qBase [0, 3, 5]
def q9F : Bound := (q9M, q9W, 4, q9G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q9Bin : BinLower q9M q9W q9G 4 := dagShiftLowerBin (width := 256) [qS16] q0Bin (by decide +kernel)
def q10M : Word := 0x303000003030000000000000000
abbrev q10G : Word := qGoal &&& q10M
abbrev q10W : List Word := projectDAGStock q10M qBase [0, 3, 5]
def q10F : Bound := (q10M, q10W, 4, q10G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q10Bin : BinLower q10M q10W q10G 4 := dagShiftLowerBin (width := 256) [qS17] q0Bin (by decide +kernel)
def q11M : Word := 0xa000a00000000000a000a
abbrev q11G : Word := qGoal &&& q11M
abbrev q11W : List Word := projectDAGStock q11M qBase [1, 4, 6]
def q11F : Bound := (q11M, q11W, 4, q11G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q11Bin : BinLower q11M q11W q11G 4 := dagShiftLowerBin (width := 256) [qS18, qS3, qS4, qS5] q0Bin (by decide +kernel)
def q12M : Word := 0x50005000000000005000500
abbrev q12G : Word := qGoal &&& q12M
abbrev q12W : List Word := projectDAGStock q12M qBase [1, 4, 6]
def q12F : Bound := (q12M, q12W, 4, q12G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Bin : BinLower q12M q12W q12G 4 := dagShiftLowerBin (width := 256) [qS19, qS3, qS4, qS5] q0Bin (by decide +kernel)
def q13M : Word := 0x303000000000000000000000000000003030000
abbrev q13G : Word := qGoal &&& q13M
abbrev q13W : List Word := projectDAGStock q13M qBase [0, 3, 7]
def q13F : Bound := (q13M, q13W, 4, q13G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q13Bin : BinLower q13M q13W q13G 4 := dagShiftLowerBin (width := 256) [qS16, qS6, qS7] q0Bin (by decide +kernel)
def q14M : Word := 0x300000003000000000000000000000003000000030000
abbrev q14G : Word := qGoal &&& q14M
abbrev q14W : List Word := projectDAGStock q14M qBase [0, 5, 7]
def q14F : Bound := (q14M, q14W, 4, q14G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Bin : BinLower q14M q14W q14G 4 := dagShiftLowerBin (width := 256) [qS16, qS0, qS8, qS6, qS7] q0Bin (by decide +kernel)
def q15M : Word := 0xf000f000f000f
abbrev q15G : Word := qGoal &&& q15M
abbrev q15W : List Word := projectDAGStock q15M qBase [0, 1, 4, 5]
def q15F : Bound := (q15M, q15W, 4, q15G)
def q15E := unpackWitnesses q15W [25136, 287792, 534019, 811537]
abbrev q15N : List Word := normStock q15M q15W
def q15C : List Bound := []
def q15S : DagSample := (0x88480612180884021018882012180480412008842221, 10)
def q15L : DagLinkList := dagExtractLinks 0x9 0xf 2 1 4 1 1
def q15D : Forest := fun i => decodeNode 1 5 0x1e i
def q15T := dagTraceTagsBin q15M 10 (dagTagBases q15N 0xef04338f1c 0x372db59b37 10) 3 q15D
def q15St := dagTraceBin q15M q15N 3 q15D
def q15Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 3, 0, 1, 6, 7] 0 i.val)
def q15Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 3, 0, 1, 6, 7] 0 i.val)
def q15Mv := dagMoves ([([qS20, qS21], q15Mp0, q15Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15A : DagMovesOK q15M q15G 256 q15Mv := dagMovesOfCheck (by decide +kernel)
def q15NB : Nat → List Bound := dagNodeBounds q15C.toArray 0x0 0x0 2 1 1
def q15Ck := dagCheckNodeBin q15M q15G q15NB 1 q15St q15Mv q15L q15S q15T
def q15RA (token : Nat) : Bool :=
  let s := rootState q15N 3 token
  !dagAllowedRootBin q15M q15E s.2.1 || dagLocalBin q15M q15G (dagKnownClosesBin q15G q15C) s ||
  dagRefBin q15M 1 q15St q15Mv (fun p tok => dagFindLink (q15L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15RB0 : treeBlock 0 16 q15RA = true := by decide +kernel
theorem q15R : dagCheckRootsBin q15M q15G (dagKnownClosesBin q15G q15C) q15E (dagRefBin q15M 1 q15St q15Mv (fun p tok => dagFindLink (q15L p) tok) 0) q15N 3 = true := q15RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15B0 : treeBlock 0 1 q15Ck = true := by decide +kernel
theorem q15Bk : treeBlock 0 1 q15Ck = true := q15B0
theorem q15K : KnownBin q15C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Bin : BinLower q15M q15W q15G 4 := by
  apply lowerDagBin _ _ _ _ q15A _ _ _ q15K _ (fun _ b hb => dagNodeBounds_mem b hb) q15R q15Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q15C.all (fun b => q15M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q16M : Word := 0x3030000030300000000000000000000030300000303
abbrev q16G : Word := qGoal &&& q16M
abbrev q16W : List Word := projectDAGStock q16M qBase [0, 3, 5, 7]
def q16F : Bound := (q16M, q16W, 7, q16G)
def q16E := unpackWitnesses q16W [66176, 331904, 606336, 868384]
abbrev q16N : List Word := normStock q16M q16W
def q16C : List Bound := [q2F, q0F, q3F, q5F]
def q16S : DagSample := (0x100844028040a0100940204020940220108800a0402214028040a0, 12)
def q16L : DagLinkList := dagExtractLinks 0x884420300789e02c01 0x68300504c3c8420c83234442044323304e320420303e020328183369433194236103311023010130000f 9 4 12 3 5
def q16D : Forest := fun i => decodeNode 3 15 0x10614131a19203e4064804c8078 i
def q16T := dagTraceTagsBin q16M 12 (dagTagBases q16N 0x63388f1f8f44 0xfb3cef3fef5d 12) 6 q16D
def q16St := dagTraceBin q16M q16N 6 q16D
def q16Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q16Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q16Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q16Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q16Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q16Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q16Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q16Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q16Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q16Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q16Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q16Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q16Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q16Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q16Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q16Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q16Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 3, 6, 5] 0 i.val)
def q16Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 7, 6, 0] 0 i.val)
def q16Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q16Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q16Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 5, 6, 3] 0 i.val)
def q16Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 5, 6, 0] 0 i.val)
def q16Mp11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q16Mi11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q16Mp12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q16Mi12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q16Mp13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q16Mi13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q16Mp14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 3, 4, 0, 6, 5] 0 i.val)
def q16Mi14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 7, 6, 0] 0 i.val)
def q16Mp15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q16Mi15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q16Mv := dagMoves ([([qS6], q16Mp0, q16Mi0), ([qS0], q16Mp1, q16Mi1), ([qS22, qS6], q16Mp2, q16Mi2), ([qS0, qS6], q16Mp3, q16Mi3), ([qS22], q16Mp4, q16Mi4), ([qS1], q16Mp5, q16Mi5), ([qS1, qS6], q16Mp6, q16Mi6), ([qS2, qS0], q16Mp7, q16Mi7), ([qS23, qS22, qS6], q16Mp8, q16Mi8), ([qS2, qS0, qS6], q16Mp9, q16Mi9), ([qS23, qS22], q16Mp10, q16Mi10), ([qS1, qS0], q16Mp11, q16Mi11), ([qS1, qS22, qS6], q16Mp12, q16Mi12), ([qS2], q16Mp13, q16Mi13), ([qS23, qS6], q16Mp14, q16Mi14), ([qS2, qS22], q16Mp15, q16Mi15)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16A : DagMovesOK q16M q16G 256 q16Mv := dagMovesOfCheck (by decide +kernel)
def q16NB : Nat → List Bound := dagNodeBounds q16C.toArray 0x16ac4a9105204 0x63e1e1 7 3 2
def q16Ck := dagCheckNodeBin q16M q16G q16NB 7 q16St q16Mv q16L q16S q16T
def q16RA (token : Nat) : Bool :=
  let s := rootState q16N 6 token
  !dagAllowedRootBin q16M q16E s.2.1 || dagLocalBin q16M q16G (dagKnownClosesBin q16G q16C) s ||
  dagRefBin q16M 7 q16St q16Mv (fun p tok => dagFindLink (q16L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16RB0 : treeBlock 0 16 q16RA = true := by decide +kernel
theorem q16R : dagCheckRootsBin q16M q16G (dagKnownClosesBin q16G q16C) q16E (dagRefBin q16M 7 q16St q16Mv (fun p tok => dagFindLink (q16L p) tok) 0) q16N 6 = true := q16RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16B0 : treeBlock 0 7 q16Ck = true := by decide +kernel
theorem q16Bk : treeBlock 0 7 q16Ck = true := q16B0
theorem q16K : KnownBin q16C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q5Bin) q3Bin) q0Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Bin : BinLower q16M q16W q16G 7 := by
  apply lowerDagBin _ _ _ _ q16A _ _ _ q16K _ (fun _ b hb => dagNodeBounds_mem b hb) q16R q16Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q16C.all (fun b => q16M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q17M : Word := 0x505050505050505
abbrev q17G : Word := qGoal &&& q17M
abbrev q17W : List Word := projectDAGStock q17M qBase [1, 3, 4, 5]
def q17F : Bound := (q17M, q17W, 4, q17G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Bin : BinLower q17M q17W q17G 4 := dagShiftLowerBin (width := 256) [qS1, qS10] q15Bin (by decide +kernel)
def q18M : Word := 0x55000000550000005500000055
abbrev q18G : Word := qGoal &&& q18M
abbrev q18W : List Word := projectDAGStock q18M qBase [1, 2, 5, 6]
def q18F : Bound := (q18M, q18W, 4, q18G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q18Bin : BinLower q18M q18W q18G 4 := dagShiftLowerBin (width := 256) [qS13, qS8, qS5] q15Bin (by decide +kernel)
def q19M : Word := 0xf000f000000000000000000000000000f000f
abbrev q19G : Word := qGoal &&& q19M
abbrev q19W : List Word := projectDAGStock q19M qBase [0, 1, 4, 7]
def q19F : Bound := (q19M, q19W, 4, q19G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q19Bin : BinLower q19M q19W q19G 4 := dagShiftLowerBin (width := 256) [qS6, qS7] q15Bin (by decide +kernel)
def q20M : Word := 0x505050500000000000000000000000005050505
abbrev q20G : Word := qGoal &&& q20M
abbrev q20W : List Word := projectDAGStock q20M qBase [1, 3, 4, 7]
def q20F : Bound := (q20M, q20W, 4, q20G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q20Bin : BinLower q20M q20W q20G 4 := dagShiftLowerBin (width := 256) [qS1, qS10, qS6, qS7] q15Bin (by decide +kernel)
def q21M : Word := 0x30003000000000003000300000000000300030000000000030003
abbrev q21G : Word := qGoal &&& q21M
abbrev q21W : List Word := projectDAGStock q21M qBase [0, 4, 6, 7]
def q21F : Bound := (q21M, q21W, 4, q21G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q21Bin : BinLower q21M q21W q21G 4 := dagShiftLowerBin (width := 256) [qS24, qS25, qS11, qS6] q15Bin (by decide +kernel)
def q22M : Word := 0x1000100010001000100010001000100010001000100010001000100010001
abbrev q22G : Word := qGoal &&& q22M
abbrev q22W : List Word := projectDAGStock q22M qBase [4, 5, 6, 7]
def q22F : Bound := (q22M, q22W, 4, q22G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q22Bin : BinLower q22M q22W q22G 4 := dagShiftLowerBin (width := 256) [qS20, qS26, qS27, qS22, qS8, qS5] q15Bin (by decide +kernel)
def q23M : Word := 0x30300000303000000000000000000000303000003030000
abbrev q23G : Word := qGoal &&& q23M
abbrev q23W : List Word := projectDAGStock q23M qBase [0, 3, 5, 7]
def q23F : Bound := (q23M, q23W, 7, q23G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q23Bin : BinLower q23M q23W q23G 7 := dagShiftLowerBin (width := 256) [qS16] q16Bin (by decide +kernel)
def q24M : Word := 0xf0f0f0f0f0f0f0f
abbrev q24G : Word := qGoal &&& q24M
abbrev q24W : List Word := projectDAGStock q24M qBase [0, 1, 3, 4, 5]
def q24F : Bound := (q24M, q24W, 7, q24G)
def q24E := unpackWitnesses q24W [25136, 287792, 553008, 799754, 1077272]
abbrev q24N : List Word := normStock q24M q24W
def q24C : List Bound := [q0F, q9F, q15F, q17F]
def q24S : DagSample := (0xa030280884c140b05024060b0c06806090184c30190c024141a088642209040244021080480422100886012008241028100a01422008840412088c42221, 28)
def q24L : DagLinkList := dagExtractLinks 0xe38e31341 0x405c3843a04f9043202f1023001f 6 3 12 3 1
def q24D : Forest := fun i => decodeNode 3 15 0x2e2843205e408c80f8 i
def q24T := dagTraceTagsBin q24M 28 (dagTagBases q24N 0xc210f74c96f0eb2081f1fdd276f93ffe984 0xda73f74e26fbeba58dfaf9d936fcfffecdf 28) 6 q24D
def q24St := dagTraceBin q24M q24N 6 q24D
def q24Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q24Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q24Mv := dagMoves ([([qS1], q24Mp0, q24Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24A : DagMovesOK q24M q24G 256 q24Mv := dagMovesOfCheck (by decide +kernel)
def q24NB : Nat → List Bound := dagNodeBounds q24C.toArray 0x4072a9084 0x9378 7 3 2
def q24Ck := dagCheckNodeBin q24M q24G q24NB 5 q24St q24Mv q24L q24S q24T
def q24RA (token : Nat) : Bool :=
  let s := rootState q24N 6 token
  !dagAllowedRootBin q24M q24E s.2.1 || dagLocalBin q24M q24G (dagKnownClosesBin q24G q24C) s ||
  dagRefBin q24M 5 q24St q24Mv (fun p tok => dagFindLink (q24L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24RB0 : treeBlock 0 32 q24RA = true := by decide +kernel
theorem q24R : dagCheckRootsBin q24M q24G (dagKnownClosesBin q24G q24C) q24E (dagRefBin q24M 5 q24St q24Mv (fun p tok => dagFindLink (q24L p) tok) 0) q24N 6 = true := q24RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24B0 : treeBlock 0 5 q24Ck = true := by decide +kernel
theorem q24Bk : treeBlock 0 5 q24Ck = true := q24B0
theorem q24K : KnownBin q24C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q17Bin) q15Bin) q9Bin) q0Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24Bin : BinLower q24M q24W q24G 7 := by
  apply lowerDagBin _ _ _ _ q24A _ _ _ q24K _ (fun _ b hb => dagNodeBounds_mem b hb) q24R q24Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q24C.all (fun b => q24M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q25M : Word := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev q25G : Word := qGoal &&& q25M
abbrev q25W : List Word := projectDAGStock q25M qBase [0, 1, 4, 5, 7]
def q25F : Bound := (q25M, q25W, 7, q25G)
def q25E := unpackWitnesses q25W [74384, 337040, 534019, 876688, 1138736]
abbrev q25N : List Word := normStock q25M q25W
def q25C : List Bound := [q4F, q14F, q15F, q3F, q19F]
def q25S : DagSample := (0x120a0182802213088480613180c4061201088402218048223108884402140204201201209008248048041208a44228100a0402214028040a0, 25)
def q25L : DagLinkList := dagExtractLinks 0xd59 0x15c24c1f 3 1 7 2 1
def q25D : Forest := fun i => decodeNode 2 9 0x5c89a7c i
def q25T := dagTraceTagsBin q25M 25 (dagTagBases q25N 0x1a787c3c43c1fe0cec7ce91ff07ff4c4 0x18b9fc3f4fedf85c6d3eecdffcfff67d 25) 6 q25D
def q25St := dagTraceBin q25M q25N 6 q25D
def q25Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q25Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q25Mv := dagMoves ([([qS6], q25Mp0, q25Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25A : DagMovesOK q25M q25G 256 q25Mv := dagMovesOfCheck (by decide +kernel)
def q25NB : Nat → List Bound := dagNodeBounds q25C.toArray 0x101585 0x444283 7 3 3
def q25Ck := dagCheckNodeBin q25M q25G q25NB 3 q25St q25Mv q25L q25S q25T
def q25RA (token : Nat) : Bool :=
  let s := rootState q25N 6 token
  !dagAllowedRootBin q25M q25E s.2.1 || dagLocalBin q25M q25G (dagKnownClosesBin q25G q25C) s ||
  dagRefBin q25M 3 q25St q25Mv (fun p tok => dagFindLink (q25L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25RB0 : treeBlock 0 32 q25RA = true := by decide +kernel
theorem q25R : dagCheckRootsBin q25M q25G (dagKnownClosesBin q25G q25C) q25E (dagRefBin q25M 3 q25St q25Mv (fun p tok => dagFindLink (q25L p) tok) 0) q25N 6 = true := q25RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25B0 : treeBlock 0 3 q25Ck = true := by decide +kernel
theorem q25Bk : treeBlock 0 3 q25Ck = true := q25B0
theorem q25K : KnownBin q25C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q19Bin) q3Bin) q15Bin) q14Bin) q4Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25Bin : BinLower q25M q25W q25G 7 := by
  apply lowerDagBin _ _ _ _ q25A _ _ _ q25K _ (fun _ b hb => dagNodeBounds_mem b hb) q25R q25Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q25C.all (fun b => q25M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q26M : Word := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
abbrev q26G : Word := qGoal &&& q26M
abbrev q26W : List Word := projectDAGStock q26M qBase [0, 1, 3, 6, 7]
def q26F : Bound := (q26M, q26W, 8, q26G)
def q26E := unpackWitnesses q26W [66176, 328832, 594048, 884864, 1151048]
abbrev q26N : List Word := normStock q26M q26W
def q26C : List Bound := [q2F, q6F]
def q26S : DagSample := (0x30082c12432082430502c14090182c904a01824064324124900905128824920824100940204804201209008201a0402090422100880520802810110880c0403008281, 30)
def q26L : DagLinkList := dagExtractLinks 0xa0280a028098a519425094250942328c1d65d8da07001 0x50450104400f85c4e05c0e04c49031090210a01d0d0190c015050118b45e8a4520b43e0a4320442d0402189852098320442d8605e850520804d0704c0603e050320402da3c43238338344303423c204fc10432203f210334202f410230201f010130001f 10 4 12 5 3
def q26D : Forest := fun i => decodeNode 5 17 0x880d85c602618064802a443e1a190e0c8409a204c101f080c8405a2423080f8404c203e0 i
def q26T := dagTraceTagsBin q26M 30 (dagTagBases q26N 0x28421ceee4b78f5f4103e3f0e93bfc47ffd108 0x2b4e7ceef137d75f4b1bf5f8ec9bfebfffdbbd 30) 7 q26D
def q26St := dagTraceBin q26M q26N 7 q26D
def q26Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q26Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q26Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q26Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q26Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 0, 2, 1, 4, 5, 3, 7] 0 i.val)
def q26Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 6, 4, 5, 0, 7] 0 i.val)
def q26Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q26Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q26Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q26Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q26Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 6, 4, 5, 0, 7] 0 i.val)
def q26Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 0, 2, 1, 4, 5, 3, 7] 0 i.val)
def q26Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 4, 5, 0, 7] 0 i.val)
def q26Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 4, 5, 0, 7] 0 i.val)
def q26Mv := dagMoves ([([qS24], q26Mp0, q26Mi0), ([qS3, qS11], q26Mp1, q26Mi1), ([qS28, qS24, qS11], q26Mp2, q26Mi2), ([qS1], q26Mp3, q26Mi3), ([qS1, qS24], q26Mp4, q26Mi4), ([qS3, qS9, qS11], q26Mp5, q26Mi5), ([qS28, qS9], q26Mp6, q26Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26A : DagMovesOK q26M q26G 256 q26Mv := dagMovesOfCheck (by decide +kernel)
def q26NB : Nat → List Bound := dagNodeBounds q26C.toArray 0x44891223e72e192d58b13213448502 0x164aa 7 2 1
def q26Ck := dagCheckNodeBin q26M q26G q26NB 17 q26St q26Mv q26L q26S q26T
def q26RA (token : Nat) : Bool :=
  let s := rootState q26N 7 token
  !dagAllowedRootBin q26M q26E s.2.1 || dagLocalBin q26M q26G (dagKnownClosesBin q26G q26C) s ||
  dagRefBin q26M 17 q26St q26Mv (fun p tok => dagFindLink (q26L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26RB0 : treeBlock 0 32 q26RA = true := by decide +kernel
theorem q26R : dagCheckRootsBin q26M q26G (dagKnownClosesBin q26G q26C) q26E (dagRefBin q26M 17 q26St q26Mv (fun p tok => dagFindLink (q26L p) tok) 0) q26N 7 = true := q26RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26B0 : treeBlock 0 16 q26Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26B16 : treeBlock 16 1 q26Ck = true := by decide +kernel
theorem q26Bk : treeBlock 0 17 q26Ck = true := (@treeBlock_merge 0 16 1 q26Ck q26B0 q26B16)
theorem q26K : KnownBin q26C := (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q6Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26Bin : BinLower q26M q26W q26G 8 := by
  apply lowerDagBin _ _ _ _ q26A _ _ _ q26K _ (fun _ b hb => dagNodeBounds_mem b hb) q26R q26Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q26C.all (fun b => q26M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q27M : Word := 0x550055000000000055005500000000005500550000000000550055
abbrev q27G : Word := qGoal &&& q27M
abbrev q27W : List Word := projectDAGStock q27M qBase [1, 2, 4, 6, 7]
def q27F : Bound := (q27M, q27W, 7, q27G)
def q27E := unpackWitnesses q27W [74896, 338064, 565312, 893072, 1146944]
abbrev q27N : List Word := normStock q27M q27W
def q27C : List Bound := [q1F, q7F]
def q27S : DagSample := (0xa05828120305920940304880420211020502014028440804900822011100840104828940a21004820110880c0403012050, 22)
def q27L : DagLinkList := dagExtractLinks 0x9 0x1f 2 1 5 1 1
def q27D : Forest := fun i => decodeNode 1 6 0x3e i
def q27T := dagTraceTagsBin q27M 22 (dagTagBases q27N 0x4f3674db27c1973ef837c3bfa89 0x35ff6715be7cba79efb77efbfafc 22) 6 q27D
def q27St := dagTraceBin q27M q27N 6 q27D
def q27Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q27Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q27Mv := dagMoves ([([qS26, qS27], q27Mp0, q27Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27A : DagMovesOK q27M q27G 256 q27Mv := dagMovesOfCheck (by decide +kernel)
def q27NB : Nat → List Bound := dagNodeBounds q27C.toArray 0x2 0x2 4 2 1
def q27Ck := dagCheckNodeBin q27M q27G q27NB 1 q27St q27Mv q27L q27S q27T
def q27RA (token : Nat) : Bool :=
  let s := rootState q27N 6 token
  !dagAllowedRootBin q27M q27E s.2.1 || dagLocalBin q27M q27G (dagKnownClosesBin q27G q27C) s ||
  dagRefBin q27M 1 q27St q27Mv (fun p tok => dagFindLink (q27L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27RB0 : treeBlock 0 32 q27RA = true := by decide +kernel
theorem q27R : dagCheckRootsBin q27M q27G (dagKnownClosesBin q27G q27C) q27E (dagRefBin q27M 1 q27St q27Mv (fun p tok => dagFindLink (q27L p) tok) 0) q27N 6 = true := q27RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27B0 : treeBlock 0 1 q27Ck = true := by decide +kernel
theorem q27Bk : treeBlock 0 1 q27Ck = true := q27B0
theorem q27K : KnownBin q27C := (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q7Bin) q1Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27Bin : BinLower q27M q27W q27G 7 := by
  apply lowerDagBin _ _ _ _ q27A _ _ _ q27K _ (fun _ b hb => dagNodeBounds_mem b hb) q27R q27Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q27C.all (fun b => q27M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q28M : Word := 0xf0f00000f0f00000f0f00000f0f
abbrev q28G : Word := qGoal &&& q28M
abbrev q28W : List Word := projectDAGStock q28M qBase [0, 1, 3, 5, 6]
def q28F : Bound := (q28M, q28W, 7, q28G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q28Bin : BinLower q28M q28W q28G 7 := dagShiftLowerBin (width := 256) [qS12] q24Bin (by decide +kernel)
def q29M : Word := 0xf000f000f000f000f000f000f000f
abbrev q29G : Word := qGoal &&& q29M
abbrev q29W : List Word := projectDAGStock q29M qBase [0, 1, 4, 5, 6]
def q29F : Bound := (q29M, q29W, 7, q29G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q29Bin : BinLower q29M q29W q29G 7 := dagShiftLowerBin (width := 256) [qS20, qS21, qS11] q24Bin (by decide +kernel)
def q30M : Word := 0x5050505050505050505050505050505
abbrev q30G : Word := qGoal &&& q30M
abbrev q30W : List Word := projectDAGStock q30M qBase [1, 3, 4, 5, 6]
def q30F : Bound := (q30M, q30W, 7, q30G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Bin : BinLower q30M q30W q30G 7 := dagShiftLowerBin (width := 256) [qS20, qS21, qS27, qS11, qS12] q24Bin (by decide +kernel)
def q31M : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev q31G : Word := qGoal &&& q31M
abbrev q31W : List Word := projectDAGStock q31M qBase [0, 1, 3, 4, 7]
def q31F : Bound := (q31M, q31W, 7, q31G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Bin : BinLower q31M q31W q31G 7 := dagShiftLowerBin (width := 256) [qS6, qS7] q24Bin (by decide +kernel)
def q32M : Word := 0x50505050505050500000000000000000505050505050505
abbrev q32G : Word := qGoal &&& q32M
abbrev q32W : List Word := projectDAGStock q32M qBase [1, 3, 4, 5, 7]
def q32F : Bound := (q32M, q32W, 7, q32G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Bin : BinLower q32M q32W q32G 7 := dagShiftLowerBin (width := 256) [qS1, qS10] q25Bin (by decide +kernel)
def q33M : Word := 0x3333000000000000333300000000000033330000000000003333
abbrev q33G : Word := qGoal &&& q33M
abbrev q33W : List Word := projectDAGStock q33M qBase [0, 2, 3, 6, 7]
def q33F : Bound := (q33M, q33W, 8, q33G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Bin : BinLower q33M q33W q33G 8 := dagShiftLowerBin (width := 256) [qS14] q26Bin (by decide +kernel)
def q34M : Word := 0xf000f00000000000f000f00000000000f000f00000000000f000f
abbrev q34G : Word := qGoal &&& q34M
abbrev q34W : List Word := projectDAGStock q34M qBase [0, 1, 4, 6, 7]
def q34F : Bound := (q34M, q34W, 7, q34G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Bin : BinLower q34M q34W q34G 7 := dagShiftLowerBin (width := 256) [qS20, qS26, qS6, qS7] q25Bin (by decide +kernel)
def q35M : Word := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
abbrev q35G : Word := qGoal &&& q35M
abbrev q35W : List Word := projectDAGStock q35M qBase [0, 1, 5, 6, 7]
def q35F : Bound := (q35M, q35W, 7, q35G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Bin : BinLower q35M q35W q35G 7 := dagShiftLowerBin (width := 256) [qS13, qS12, qS5, qS7] q27Bin (by decide +kernel)
def q36M : Word := 0x3300000033000000330000003300000033000000330000003300000033
abbrev q36G : Word := qGoal &&& q36M
abbrev q36W : List Word := projectDAGStock q36M qBase [0, 2, 5, 6, 7]
def q36F : Bound := (q36M, q36W, 8, q36G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q36Bin : BinLower q36M q36W q36G 8 := dagShiftLowerBin (width := 256) [qS14, qS0, qS8] q26Bin (by decide +kernel)
def q37M : Word := 0x5500000055000000550000005500000055000000550000005500000055
abbrev q37G : Word := qGoal &&& q37M
abbrev q37W : List Word := projectDAGStock q37M qBase [1, 2, 5, 6, 7]
def q37F : Bound := (q37M, q37W, 7, q37G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q37Bin : BinLower q37M q37W q37G 7 := dagShiftLowerBin (width := 256) [qS8, qS7] q27Bin (by decide +kernel)
def q38M : Word := 0x111100001111000011110000111100001111000011110000111100001111
abbrev q38G : Word := qGoal &&& q38M
abbrev q38W : List Word := projectDAGStock q38M qBase [2, 3, 5, 6, 7]
def q38F : Bound := (q38M, q38W, 8, q38G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q38Bin : BinLower q38M q38W q38G 8 := dagShiftLowerBin (width := 256) [qS13, qS9, qS11, qS12, qS5] q26Bin (by decide +kernel)
def q39M : Word := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev q39G : Word := qGoal &&& q39M
abbrev q39W : List Word := projectDAGStock q39M qBase [0, 4, 5, 6, 7]
def q39F : Bound := (q39M, q39W, 7, q39G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q39Bin : BinLower q39M q39W q39G 7 := dagShiftLowerBin (width := 256) [qS24, qS25, qS0, qS6] q24Bin (by decide +kernel)
def q40M : Word := 0x5000500050005000500050005000500050005000500050005000500050005
abbrev q40G : Word := qGoal &&& q40M
abbrev q40W : List Word := projectDAGStock q40M qBase [1, 4, 5, 6, 7]
def q40F : Bound := (q40M, q40W, 7, q40G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Bin : BinLower q40M q40W q40G 7 := dagShiftLowerBin (width := 256) [qS26, qS27, qS4, qS8, qS7] q27Bin (by decide +kernel)
def q41M : Word := 0xf0f0f0f0f0f0f0f0
abbrev q41G : Word := qGoal &&& q41M
abbrev q41W : List Word := projectDAGStock q41M qBase [0, 1, 3, 4, 5]
def q41F : Bound := (q41M, q41W, 7, q41G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Bin : BinLower q41M q41W q41G 7 := dagShiftLowerBin (width := 256) [qS15] q24Bin (by decide +kernel)
def q42M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q42G : Word := qGoal &&& q42M
abbrev q42W : List Word := projectDAGStock q42M qBase [0, 1, 3, 4, 5, 6]
def q42F : Bound := (q42M, q42W, 10, q42G)
def q42E := unpackWitnesses q42W [49760, 312416, 577632, 843872, 1101896, 1368112]
abbrev q42N : List Word := normStock q42M q42W
def q42C : List Bound := [q0F, q10F, q1F, q30F, q24F, q29F, q12F, q28F, q11F, q9F]
def q42S : DagSample := (0x280008860320188c142a00108824324128c06230088c068209449058089443058081400261241a022130502c14090182c301a0182406130c0643009050682219088244021010884022180481028100a01422088c4c0700888410090190c9049240242012201080209051288249208240412201400442008846070209848221, 57)
def q42L : DagLinkList := dagExtractLinks 0x1e83d07a0f03e03c0780ec3d83a0f02ccb98330641c81886d25a09cd09a103856c2d801d001 0x3246c180220b80f2590f82c04c95629ab917d588a62e43f162198aa1f05085da74609362819a1404c0a11906352437e8218c4909f208431101745c18d410de9e8631042787a10c380781b0634c437a5a18c3109e168430a01e61417f060a706c5382625c0b10d910a64c84b254219220cf188bf8a4538922784912c2088e0e4438621fc290cc8885e424234402983012c14086080330301181006c040260003f 11 5 13 5 3
def q42D : Forest := fun i => decodeNode 5 18 0x2365c089321fbc866f43e3085ca0282509e70171d09e64219807868319109e44219007832258488e12218409610218406610118403610098407e0 i
def q42T := dagTraceTagsBin q42M 57 (dagTagBases q42N 0x3b7ad0847e834e9007f92dc6f65af76d5a083cf4c3feff06e93dcfbe6c1c7cfff103ffe1f0807ffffb34c9 0x3b7ad69cfeaf4e9cfffc4ddef7daff6f5a58fd74effeffc6ec9dd7bfef7c7ffff4b7fff7f80f7ffffb965c 57) 9 q42D
def q42St := dagTraceBin q42M q42N 9 q42D
def q42Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q42Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q42Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q42Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q42Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 6, 5, 4, 7] 0 i.val)
def q42Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 6, 5, 4, 7] 0 i.val)
def q42Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q42Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q42Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 0, 1, 3, 7] 0 i.val)
def q42Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 3, 1, 0, 7] 0 i.val)
def q42Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 3, 1, 0, 7] 0 i.val)
def q42Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 0, 1, 3, 7] 0 i.val)
def q42Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q42Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q42Mv := dagMoves ([([qS12], q42Mp0, q42Mi0), ([qS1], q42Mp1, q42Mi1), ([qS1, qS12], q42Mp2, q42Mi2), ([qS20, qS21, qS11], q42Mp3, q42Mi3), ([qS28, qS21, qS4, qS12], q42Mp4, q42Mi4), ([qS20, qS21, qS11, qS12], q42Mp5, q42Mi5), ([qS28, qS21, qS4], q42Mp6, q42Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42A : DagMovesOK q42M q42G 256 q42Mv := dagMovesOfCheck (by decide +kernel)
def q42NB : Nat → List Bound := dagNodeBounds q42C.toArray 0xa0280a02799c66294a428920b7b1d36d19b5f16a5311e3b8be254821744309004 0x34200220682071073103504510410431021682074352068912068352073510614351072106817435 10 3 4
def q42Ck := dagCheckNodeBin q42M q42G q42NB 26 q42St q42Mv q42L q42S q42T
def q42RA (token : Nat) : Bool :=
  let s := rootState q42N 9 token
  !dagAllowedRootBin q42M q42E s.2.1 || dagLocalBin q42M q42G (dagKnownClosesBin q42G q42C) s ||
  dagRefBin q42M 26 q42St q42Mv (fun p tok => dagFindLink (q42L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42RB0 : treeBlock 0 64 q42RA = true := by decide +kernel
theorem q42R : dagCheckRootsBin q42M q42G (dagKnownClosesBin q42G q42C) q42E (dagRefBin q42M 26 q42St q42Mv (fun p tok => dagFindLink (q42L p) tok) 0) q42N 9 = true := q42RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42B0 : treeBlock 0 16 q42Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42B16 : treeBlock 16 10 q42Ck = true := by decide +kernel
theorem q42Bk : treeBlock 0 26 q42Ck = true := (@treeBlock_merge 0 16 10 q42Ck q42B0 q42B16)
theorem q42K : KnownBin q42C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q9Bin) q11Bin) q28Bin) q12Bin) q29Bin) q24Bin) q30Bin) q1Bin) q10Bin) q0Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Bin : BinLower q42M q42W q42G 10 := by
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
def q43M : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev q43G : Word := qGoal &&& q43M
abbrev q43W : List Word := projectDAGStock q43M qBase [0, 1, 3, 4, 5, 7]
def q43F : Bound := (q43M, q43W, 10, q43G)
def q43E := unpackWitnesses q43W [74384, 337040, 602256, 799754, 1138832, 1400880]
abbrev q43N : List Word := normStock q43M q43W
def q43C : List Bound := [q4F, q23F, q15F, q24F, q31F, q16F, q25F, q13F, q32F, q0F, q19F, q17F, q20F]
def q43S : DagSample := (0x1029100a400280022006220c0e03028180e1209101a080683180c4142a48260148a0c2603088482c120a0182c060a00884c140b05024060b0c06806090184c30190c024141a088642209100840422100886012040a0402805088223108884100940204201201209008248048020904221008805208041208a44228100a0402214028040a0, 59)
def q43L : DagLinkList := dagExtractLinks 0x9e09e09e09e09e09e09e09e09e09e09e09b39659339309219029008f18f08e18e08e08b38838268117f27f07f07f07e17e07c27a27a07a07a07827627516f66695f75875535505054d34b241a3983633152f22691f714b07d016001 0xe086168420740183d2106e485d68422390171a0088ed8c0f4860b32181b8080e98c06c430390301cc180e10c0ec840b40301c4181d90816c4607742f3b2148dc8bc6c452b502f598148dc8616c860364201a9181d10c0684603483019a182c80d86204cb2036190130c40c8608616b420979180908445202e1a0111851c1b98a0d6850ae2381190c26484156070590180a0081b98c4d886e6b431171188888605806e2b03117c182b90c25c841a72174c90889c05c320222d22c9610c484025568612b420901088a805c28022298311411b89c0c44c07c2502e7221c1910a0c0840a423812114080881340701a0280e8130500804906223431112100848dc404629c0374c81887c09abe8501f228098140798dc3ac6213626ae1188700c42645c1b03e0d4189650c432462180370b81b4580d82a06514031098137488c2a44414c218c90184480821803109009894188450c6208410f231041088380dc1a0630c0310580b8280460802209831e421892108510462082214381be180dd0a0638403103813c1809c0a0430402101b14f088a684433820298100cc040260003f 12 4 13 6 2
def q43D : Forest := fun i => decodeNode 6 19 0x6305ec60b20c144182421844840848c0ec181a4303404c540c8a51c1283020841408b2790c4f4209a02e360c4611b8c0311807c2c0b85c188943112840248dc49188922810c6e1d8c438188703e0d062148c4281b850368a06c140ca2818850268b0620d0c61a10432310606e0c0c6181883017060230e0c61110820278404e080861010826298203304026080fc0 i
def q43T := dagTraceTagsBin q43M 59 (dagTagBases q43N 0xfd3fe108fc3de1fbcafc96e37873f08f07c1079df1fff4d55749eeede7c439e1ffe20fffc778c03fffff4c44 0x3de7fed39fcfde1fbcafe26ef7df3f79f47cb1fadfafff0d40764ee6df3efbbf9ffe97ffff7fbdcffffff66fd 59) 9 q43D
def q43St := dagTraceBin q43M q43N 9 q43D
def q43Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Mv := dagMoves ([([qS6], q43Mp0, q43Mi0), ([qS1], q43Mp1, q43Mi1), ([qS1, qS6], q43Mp2, q43Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43A : DagMovesOK q43M q43G 256 q43Mv := dagMovesOfCheck (by decide +kernel)
def q43NB : Nat → List Bound := dagNodeBounds q43C.toArray 0x8510a2144218410660c411821042084097e6fc1f4be17b2f45e4bc8790f21e0bc0772e55c4b816f2dc5adb51676cc594b28642c4988310612bb16d2ae50a99125a1e3f878cde98e2ca4d87f8c713a19c1b006 0x2702910447100210543479867083150001503210c2a25043b21904120b20b3271004520a26173012596416753618453a863152a620435643106124305186435816435 11 3 4
def q43Ck := dagCheckNodeBin q43M q43G q43NB 60 q43St q43Mv q43L q43S q43T
def q43RA (token : Nat) : Bool :=
  let s := rootState q43N 9 token
  !dagAllowedRootBin q43M q43E s.2.1 || dagLocalBin q43M q43G (dagKnownClosesBin q43G q43C) s ||
  dagRefBin q43M 60 q43St q43Mv (fun p tok => dagFindLink (q43L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43RB0 : treeBlock 0 64 q43RA = true := by decide +kernel
theorem q43R : dagCheckRootsBin q43M q43G (dagKnownClosesBin q43G q43C) q43E (dagRefBin q43M 60 q43St q43Mv (fun p tok => dagFindLink (q43L p) tok) 0) q43N 9 = true := q43RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43B0 : treeBlock 0 16 q43Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43B16 : treeBlock 16 16 q43Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43B32 : treeBlock 32 16 q43Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43B48 : treeBlock 48 12 q43Ck = true := by decide +kernel
theorem q43Bk : treeBlock 0 60 q43Ck = true := (@treeBlock_merge 0 32 28 q43Ck (@treeBlock_merge 0 16 16 q43Ck q43B0 q43B16) (@treeBlock_merge 32 16 12 q43Ck q43B32 q43B48))
theorem q43K : KnownBin q43C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q20Bin) q17Bin) q19Bin) q0Bin) q32Bin) q13Bin) q25Bin) q16Bin) q31Bin) q24Bin) q15Bin) q23Bin) q4Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Bin : BinLower q43M q43W q43G 10 := by
  apply lowerDagBin _ _ _ _ q43A _ _ _ q43K _ (fun _ b hb => dagNodeBounds_mem b hb) q43R q43Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q43C.all (fun b => q43M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q44M : Word := 0x333300003333000033330000333300003333000033330000333300003333
abbrev q44G : Word := qGoal &&& q44M
abbrev q44W : List Word := projectDAGStock q44M qBase [0, 2, 3, 5, 6, 7]
def q44F : Bound := (q44M, q44W, 11, q44G)
def q44E := unpackWitnesses q44W [66176, 329856, 594048, 868480, 1147008, 1425504]
abbrev q44N : List Word := normStock q44M q44W
def q44C : List Bound := [q7F, q0F, q36F, q10F, q16F, q33F, q2F, q38F, q8F, q5F, q3F]
def q44S : DagSample := (0x100a9040a50089400850029100250009041240021008a002a000a8400a80428040680092500a1402a10028008a48068100a40289042240a8402a140028042a0106804320902824300908812094c0610022040a80623040e030300c0a0120b0182c301a090680028048a40030082c124320c0e020914180d060240a0d241300a09100840a25301900a21100a0102802914904924024184c20924820912190826120884100940204804402211008402a0402090422100880621002211028100a01221002810211080c0403008281, 91)
def q44L : DagLinkList := dagExtractLinks 0x5e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817940bca05e502f2817883bc405e202f1017880bc20de006f0017800bc005e002f0017800bc005e002ee0976c1bb40dda02ed017680bb20dd902ec037600bb005d802ec017600bb005d706eb037541baa05d406ea0174c1ba40dd202e9017480ba20dd102e80373c1b9c0dce02e6057300b960dcb02e5037241b900dc412e1056f06b7805bc02de016ec1b7605b90adc816e01b6e0db606da056d00b6805b10ed7856b42b5615a90ad4816a40b5205a70ad28568c2b4605a10ad0036800b3e0d9e06ce0566c1b3215970acb036541b280d920ac80563c1b1c0d8e02c7016341b1a058d02c6816340b1a058d02c6816301b18058b06c5816242b1205870ac3816142b0a058406c1056080b04058106c0816001b00058002c0016000b00058002c0015f82afc057c0abe015e82af4057a02bd015e80af4057a02bc835d44aea05730ab9815c81ae20d7102b8035b43ad80d6c02b6015b00ad8056c02b6015b00ad8056c02b5835a81ad20d6806b38359c0acc0d6602b3015980ac61d6206b1015880ac4056106b00357c1abe055e06af015780abc055e02af015780abc055e02ae835740aba055c06ac875583aaa0d5406aa015500aa60d5302a98154c0aa6055302a9815481aa4055202a9015480aa4055202a8835401a9e0d4f02a78153c0a9c0d4d06a6815301a98054c02a6015300a98054c02a6015300a98054c02a5835107a7e2d3f029e074dc5a6c0d35069a034c04a6005300296874a83a463d210a90814801a40051a1a8a8b4540a2615130289814385a1a0d0a0e84053ecd9ee24f40e79053bc39d624e80e728738839ba2cdd026d8536819b404d31e659131c49881cc20a5f872e859720cb8065a872c8395c24aa12530928c3946049e164b8f228d90e1c7e263a1517188b60c551a280b1286888343e1a1e050ec18701c321a1805098a840341e0a0e0505c5826240e16060502c18140c070e0206ffc57f03bf315f68cfb017d21be319f006f7437b02bd609e614f20478a1bc309df88ee4676633b109d784eac474e239f21cc0ee4c57144b8029bb14dc846d8336325b084d6876a8334f15a50ad20268e0b4605a204d0c16840b41059f06cec36701b350d9a02cc4365243260d908ac74463223160d8a82c4836220b0f098684c2c26101b011d7c90bdc25e232ee0d7214b8045ba1adb096c06b5c15ac0ad4096904b3c359c0ace016682b2c258e22c6056204b08258012bf055e84af4056a42ad215584aa0354c12a4095182a84253c1a98194792a14a4fa427c053a1099cd4c42a5f0d289c91ca48a123f191f028f4146e32244d0f0c854942612110907847d5a3b2e1d120e412708637249a64cc4ba5cd62bca9466096b2490923451170c86163dd51dc48e0386e8634ca18290bc1459922c0315430a514508826c6102d0723c2fa60e2704e88144c00a60001 0xc0c050081808010680c020d230041906048248c0105114020922004164380829890104b120208226440a060081c8b8103a0e0202218040c46048048c030011012002300bd844048108c02f5b1305ec626040a84c08158ba10221b02034300408c6c080e0c08fb21325f723643ee06c17f887a0ff0134a01628840285157fc8ba30111151ff02e840404508060d810031615f92360bd644007fc8c08fe01b11fe23043e606007fd8b92fc11705f202823fd06047f40d82f5b1611fa03603fcc6087c40c00ff41801fd03623f8c6c47f40c08fd31b01fd43003f886007e80c02f9c1701fc62e03f206087a80c10f551b05f722803f605c07ed0c02f8c1701fa62e0be4c4d07e009a0fc91701f84300be645c17c48b80fb81305f222e03ec04c17ce0c02f8c1801f663003ee46007d88c00fbc1801f66300be604d07cc07a2f901341f101e8be706017c60c00f8b1801f583003e845c07cd8c00f911801f383003e246007ca0c00f8b1801ee02e03e006c07b40b82f781301ef01e03dc06c07b40c88f611811eb23003d8c6c07b18c00f5b1601ea23603d486c07910700f481701e802e03d244007a58800f401b15e622e23cc44c07988790f251821e443603ce86007808588f331801e683003c001187910d82f2a1301e541e43c886c17910980f220f01e543203c843407910700f181b01e202e03c205c078e0c00f111001e262003c206c07810d8499017c90f029aada04145b40620b6808413200f821e013a74e8c30e9a1861c923682c006d85700d82df11401be2200298430077c8e00ef11805bd028037a04007680600eea1705bc02083b846c057c0db0ae01b05db02683b603d05308500ed10901d703e0bac05c07580980ea00f05d983103b2c6287090d40ec21889d742903ae421075005a0eb01f01d502e03a807c86ec0c22dd81041d301c8214021046403a0e800561ba03083a405986e40a20db008410900883a206e86e40c40e831211ce238039e46007388a00e611001cf829839d06207348dc0e611881cb22f839445347218da4e0b1789196290390c4d558506c0ae20d01c121c823243186cc0c30d701805b30208b5c04007240520e431201c743e029683c86c00e08e2a1f014a41e436407055858900a4a0f01c7838038b06847158f80e341b61b4030c35e060052c0420e341c11c36384362070470e8db0cf818414a010a38707c07158b80e220e11c36368386c4d07090740ae20e01490108382c4807008d80e0314d1ad230a35046055b0882ab59101182030a2da060067009acddc1851bb430a36646d46b88d80d610c41a7218233c06d06fc0aa8d591851a6230035644106988800d291401be214037a42406f18b80d211401bb82e234647016888a00dd31a05a1220231807c06e40d00dc01901b70160b4045046888e00d1114156a220036cc6e46848c40da80d41b4638033ec68151c8808c501f01b483e0366c5c46a88e02a41140547626036087006c90d08c481f01af430036285a466c0da0d831b41af6360a90c4d06b90988cd01b41ada38035705046a50e02a4217256c23802e244c15cc0b80d641b81ab831035486e06a50c4489a178908429034884e044d07c08420c95882372ad846246200dc8b601881aa62002e043c15c0098ad4d1c11a9838035305055bd0b88b7a13256f23e02de44c85bc0f82b781701a88301b4505206998802d12105581230cad6460152089a2cb10f5198036832a04d268e0a60d3b1781a6629134ac43068d0a60d2a0cd59922fab0a45e56008a6ab59148d412279a76443069087e2a090bc53b211a33205f46140bc8c0014d16b029128204f24ec0860d200fc1410178276023068e0a00d141881a14372b0846e55a88c40d01094193026833ec6806758800cb910118f03e0ab404046718e00ce3141196238032c45085640e02ac814119c838033cc5c06648e00ca914119103e0ab605006760dc0ce418819a237033046206440dc8bf818814462e0328450064c8a00cdc1a019a4200ab0040465a0e00ccb1c01986284b0645c46400f82ab814014342602dc44c065e0dc0cb41881956311326c5206518840c9a0c419221e832006e45f80c40a180f418f834231ec7c46450e00c8a101190038032004046398e02ad313118ea368ae4031463a0f82acc17018f62e031a87006180e08c731b418e626c2e206115c40820c6b18455b626831006106140c02b9810418c22e0308070062c8d80a0117018a834428c07015c00810a351b418962d0ab083d85c60e00c431c214623e0ade450061c0b84c251841866308aaec4d06150c00c21186146036830604d060a0e00c0a1c017d2380ab245c05cc0980c151c018043802fe47c156c8b80be01f017102602f207c15608980bc01f017001e030347006020e00bf11f055722e02f607c05bc0982acc18017f63802fc47005f68e02af117215e03e02f8c7005c58c00bc11f017b23842bc07015588b80ba813017a63112f2c5205e50620bc11b814221e927e05e24e80a40a100f413f017027402215548b88bb81f017602e02e804c45dc0f80bb817156602602ec07405b80980a9917017503e02e807405b80b80b9c18817263702e2c6205c08dc0b7918816e02682db06005b08c20b591801690368ab604d056407a0b511c016703e428a47005840f90a2d1b41640368ab003d056005a2b651c016c838428a87c05980f84b5518456b83002d6c6005a90c30a291b41680368aae04d055c07a2b4c1c055983002d2c7005658c00b211f016823842ba07085768da4b3c18416723082c206d05980c22b2c18816563102c846e25480bc4a8014855602682ac03d054805c0a8008896382d92c5053058c8b60b1114c16102f82c005b244409e483810c11100f820e013057c0db0ae01b095102f129e052155409a2aa013015501e82a803c054405c0a7808a15d23e02be07c15780b80af013215d036c2b806c157409a2ae013015d01e82b803c056e0c40ad31b815963102b046e055c8c40ab01b415503282a8064054c09a0a901f015103a02a047c053c8e80a701f014d036026605c14cc0980a600b114b63e0296c5c05258988a411c0148228028a440052e0c40a531b8149631228e462051009a0a44188147637028c46e05148c40a1813414462e028645005080f80a09140114624028005c05060a00a0117013f03e227c47c04f88b809e113013e831027ac6e04f18c409da140139036026a05c04ee0a009c01b013402e026e06c04e88f809b01b013302e2272c6204e588489c1188138221226e06e44d80c409b8138136021026ac5004d08a00998140132a38425247c14a48b8890113012021e423247004c48c8294113012821e424e47c149c8b8093913011b21e026087c14bd0b8097a13012d21e0a5c45c04b889809690f012c012025445c03d885829091700f52160256c7c03d085809531401216240a4285c44a58e0094b140127620424087014810a0092213011b4200253062448d8dc8903188126626825086e049d0c428a81040f6008824cc5014690a0092b1b81246310a34c4d048d0c428a01040f50088a34c5c04890f8090a1305208310240c62047d0dc08f21b411d4360238865046d0c428d213411a41e81e8011046589088c11f011822e022c44c04620c408bb1b8116631022a85c044c8a008ab140114624022405c044e0a0089117011103e0220024043e8e008301b210a43841fc07c04140b808201b01030360a1c85c043909808681f010c0360a1605c042c098085312010963741f406e04210a008101b0108828020206c04000d808391f00ff0360a0d06204198c4082a1b81044310a04041040806208180a40ff010a204c6204098848809188101221220006e43fc0c408001380ff02101fcc4803f109807eb1b80fc63121f646203ed0dc07d11b80f903601ee04c03e58a607c31b80f763109ec85c03d909807a20f10f663101ecc4243d50dc87a21880f542701e884203ce0c1064818486802f90a0053132408284500c408a01080d001f0140027470c1860e1230c1ae06d03c80b2433813c84f02189900310320042033807c04f009c18e06121980be427014c4c7020818e03101f8042033007c04e00981e245c13180a206301040e8018809a021018c03a07800640ef00a809401123b10dc431a1884ee42e89da85c03b909a076a1300e341e81d683c03b085203190844c5028818a041038c062431117c84c22980c442f013084607580780ea43011d285003a484047431880e841881c643d039c0fa07301f08e2037109406213940ba27201700e502681c804c038c07a07100b804a01101c2c4883100e226201454890208180031012404202b80740dc00c81b601500f4022a6fa1b90df23701c0c6e037c8c5061818c0de01c817e021012002206e91b80dc83181b706343648c486c11800da22801b2442036088006bb1210d643ea1a487c23310dc42ba1880d642e81a485c035109a067213007a41e8198429015c84305e81c60b9038097a05112e40a0a44010548702000f4031035a8e406ac1f80d483901a687e01e507905e01c80d283101a2c6f03418dc067b18c0ce631219406e82f80c705d8188079010819a86e82e80c4066418c0cb22e0994c6e03288dc864b1c08c06310192c50031d88006020c60b8238c16847012e08a225a11400ba226290c441521488003d10f5099038c11407021c00dc41e8188099028891405002bc09a051013008e02080fc04001e807a03800b803d011318946303260c406431b80c7631118cc5343110c606320cd0bd237a17246e42e08c685a118885522f908e45302dc88205991000c521f80aa42f011c84685701bd0a1037213006342280c443a817c86e029815a04d031407e03a80bc06e0118189072030d0fc85911c84b1228214007e42240e406100a40c1012818106342fd0dc05fa1390b1231016244242ac0de84b818c0ab027812e04302fa0fc05eb1c90b623908f045042740fc84401c80bc6378176c6e02e98c423c31340b9431215406f42700dc84b018d087031097147202e20e405bc1400b643f016a872214d0dc423218847842e00f084c014d07c02320c949b23f290c47212a089a045913109b03f210c07202a00ba24581708b2a31896906232c60a405a31888b16290166c4002c90c6258a1040b1418a95246f52688dca4a918d48523118e645f31b48a623c11344a721e88e642f11b484685481bd09a037212a06342140c4439817c86d029814e04d01e007a03980bc06d011816107e02be0e4046c1740ae6391156c6202b58a005631080ab418815447e02a48e405411440a722800ee43d02980fc84a01c887203710d806202340a223e814007701e80e402e01b0044450518c0a56378148c6e028d8c6051318889f62f913cc5311f589a050a1880a0231813e43b027886604e81bc09c037013606302680c4429017c8450298916041014803e022804c099a390131072225e0c404bb10409643f012a87201d909a04a11f809323910e246e21ac8c4046917447d22e00ec44d01c487c03590c809203f012207d02400f804781d408e039011a05d023009a0458130889a31891506202298c4044a18c088237810e46e02188c6042918885122f9088453014485e022108c084037810606e02080da04081b008003280fe06301f80c443e017c87b02988fa04d01f407a03e00bc07b01180f506341e58dc03cb13907823100f044241dc0de83b018c07702780ec04341d60e403ac14907443f00e885e41cc8e4039914907203f20e207201c80bc0388148070831a0de46e01bc89c83741c806e82920da87201b50a483611f906b23900d845e01ac8a483481f806a03600d205e11a28e403441c806763f00ccc7281748fd02b91c846122e88b845c018489a02e113006521f00be43d016087803210d4063219007442d11540a202a810406201c80a203100e8042830c1c806182920c0c7e417d8e4030317805f62920bc47e01788bc01c90b005d831a0b8c62017188482da1bd05a43720b286341610c402da13c05a42700b2843016108502a018c4540218072011015e0c682b11b805622720ab07201560a482a21f805442f20a6472014c8a482901f905103900a405e01440a422851c8050839009ec7e01398e5024a1c804d419088e451011c88202610e4044218807442d81000fd01e81c8043036808406c012c07c02500c803a016809306341210dc024213a03e037087c04e411e0e4023c149046439008c85241148fc82211c804522f008845201040d8a21c18d0436318086c4351098a6821214c042419c0820531104066020808c040831a07e86e00fd09c81f118803e221007b06340ec0dc01e017003b027287506340e98c601d310e039437087284e00e507d417d18c4388310070c6200dd0dc01b218883542f106885320b10a5017918c035214806842300b084301481be023031902605f20380a62110104022018806602f009805a01900a403101280600230060042009807c00e009805f06340b90c4017210902d237205846200b489c016110a02103188420430080062006808401000e805601900a802a0040044029831a05086f409d0dc813218882542f102085200a109e013a138026421002e83d00948520081085024037403e06380780c4012013841f021883c042005c062c10d18c023831904305340898c441031480226212042863008508601020c501f237a03c46e40748c680e118880f22f9018453007c89e00f113801d2218038442005c87a00790bc00c211a03606f40680dc80c818d018031102c05f20540bc40a014c808029003604f006809c00c810c018021002e03d005805e00a80b80140118010022504e0c6809b18c013621c02446f80448dd0081188412227882244e104088400910fc01121f0020432001c85b007818c40f021801e033001c042a07418d00e631801cc4380350c4206a10800d4194018463103088600610cc007216c01206e80200c4005817400a02e081204e102008400480f8008019000e02da0160a6a03314cc05621a00c853201508600320ce005229880a4330014847002017e003029900404f200408620200fc403019800802f000c046001007c001009800003f 17 6 13 10 4
def q44D : Forest := fun i => decodeNode 10 23 0x8c0edc181da21c3a2c48741890e79131cb41c3824606f98bad7b1b1ab8303540456a20d8d23161a262e3350606590c0c8b1718e430310c5c61c8b8c2a181848302e0c605c20c0b31171648302b50605618c0ac01b15001e2a006c5380c8a731814862c29086c51d8809c81b13743025b0604850c88da0e11783020ec404080d88021b0f52381e04603c10b87791b0ed01e9d84243a58c473a188e72109ce07c3980b87301f0e401c9c40593840dc6fb120dc8299b70623688dc6d1188da22f9b24533640526c3120d78381a90703498b86820e0d062699e83a33d89066b14ccc02a99242831c84863b170c682e18ac683100d0620190c4016186c6e30006a6041f0be62e17c8682f50b45e31b4ba63617484c2ea8e05cc1b8b8831170c402de0a05b4180b562f168c522d10665a00fcb48281670622c90dc591094b2634162c5c2be0dc574188ae8341568402ad8e0553140aa8371510622a18c4543108a841895043d2a1080538100a762e148c4d28d8c2511170a12361410682798b44eb1c09c02e138c6126d0c04d91849b0269374702668e04b41c09663812a4702568e04a31c093238126c622450624891b89102e11e0742380f84681d08d831118c6e2318c44611b88c23111804d2320c045c1c08763010c8612198e04291c0852309080612118c44191b88322d9044532080be41016c8203e10004c20007a3f80f07f8310fcc6e1f98c43f11b87e2310fc06d1f80ca3f01907e0268fc07c1f40e83e91f07c23a0f807c1f00d83e00b07c8310f4c6e1e98c43d4188796370f246e1e48c43cb170782280f007c1de0a03a11707303e0e50621c18dc383188708280dc47c1b18843591086b0270d60421ad8a03511406a0280d54701a48c83421f0664260cc44c1908783200906363e0c0c5017e0c42ea1b85d4310bac501718dc2db1885b4310b687c1690982d3188594370b286d1650d82ca194594310b283d1658902c4188576370aec6215d8a02ab120558280a845c14c0f829009052a380a284c1300f82581b04b026096c481298dc24c1404723e08ac6210d0dc21a18843014886c4210888421013842021084c481058dc2031884043707e46e0fd8a61eb1b83c631078c420e909c1d21083a8300720590e08b81b00643500a86a84d0d10981a10a43400f0668600c88401920c43103e86207c0c409a1881303101e86202e0c58901831b82e23105c0390b88dc16c18c2c8318564500ac8841591002b6240554720a60fc14c1c82943f0530620a18de1431b828631850c620a10dc13c18c2622e04c46e0960c411b1b82363104683308c07e11c1c82243f04402908804a11418c2142704307e0818e41031bc1f63703ec6207d0c40fc1c81e82803c87e0790e40f31881d62003a8630750620ec1f81c839038c720718a00e31081c41883847e0708e40e11441c22803807e0718de0db1b81b631836c6206d0c40d918c1b21d83643306c0de0d81b81b03183606206e8e40d41c81a62083487e0690e40d11f81a23903407e0680fa0d01f01a03a8340720680ba0d01341a026034c620650c60c91bc192370324630648c40c81bc1903703206d0640d80c81941903183206206407a0c80bc1901183306306189c0c1108180278300430620a40ba1781722902e05e05c0a40bc18c1622702d0520550a40a91781522902a06c0540bc0ac1c81463f028c7205087c0a10d4142190280390520a409b1781362902645e04e0c60931081242782484e0490860921081283182244e0460a40821781022902005e0400a40841c80f63f01ec7203d0640790e40f01f01e03203e0c60721380e82901a8520348bc0691480d62181883302c04605c18c0a42701444202a0c604817009027012c4302107c0431880743700e86201c85203908c0701780e02901c04a03808c0783180c84201889c0311080600c80c01501a0c602a13c0542700a84201485202813805831808c420110860220c40422780844e0108860211080402780804e0100860201080401e80802f01005c02008c0462180643f00c87c0190c803019806c430090640110cc0202e80405c00807c0100c8020168048330048460080bc0101180201f0040260080fc00 i
def q44T := dagTraceTagsBin q44M 91 (dagTagBases q44N 0x1b9a2fe7ffd845890e7777fffff9fddcef2676de3dd710b480c16387b079077c7fe4e02078b2a03bf03f1ff8fffbf3dfcb73983bb9277ff8afe19e15303c0fffffd1108 0x3fe3bb4fffffdb55b93e7777fffff9fddcef8ab6df5dd7befbfee07bd7b2fd1f7ebfff7fbf7ff285bbf57f7ffd7fffffdff1799c3bbc937ffd22ff8fffffffffffffdbbbd 91) 10 q44D
def q44St := dagTraceBin q44M q44N 10 q44D
def q44Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q44Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q44Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q44Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q44Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q44Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q44Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q44Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q44Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q44Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q44Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q44Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q44Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 0, 4, 3, 2, 7] 0 i.val)
def q44Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 5, 4, 0, 2, 7] 0 i.val)
def q44Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q44Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q44Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q44Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q44Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 5, 4, 0, 2, 7] 0 i.val)
def q44Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 0, 4, 3, 2, 7] 0 i.val)
def q44Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)
def q44Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)
def q44Mv := dagMoves ([([qS0], q44Mp0, q44Mi0), ([qS25], q44Mp1, q44Mi1), ([qS25, qS0], q44Mp2, q44Mi2), ([qS1], q44Mp3, q44Mi3), ([qS2, qS0], q44Mp4, q44Mi4), ([qS1, qS25], q44Mp5, q44Mi5), ([qS2, qS25, qS0], q44Mp6, q44Mi6), ([qS1, qS0], q44Mp7, q44Mi7), ([qS2], q44Mp8, q44Mi8), ([qS1, qS25, qS0], q44Mp9, q44Mi9), ([qS2, qS25], q44Mp10, q44Mi10)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44A : DagMovesOK q44M q44G 256 q44Mv := dagMovesOfCheck (by decide +kernel)
def q44NB : Nat → List Bound := dagNodeBounds q44C.toArray 0x208040f181e103c207840f081e103c207840f081e103c207840f081e103c207840f081e103c207840f081e10386068c0d081830302058c0b0816102c205840b0816102c2050c0a081410246048409080e50186030405180650086008c0017fe2ffc1ff0bfd17fa0ff05fd8bfb07f60fec1fd83fa17f04fd89fa8bf327e60fc49f80bef17da4fb05f58beb07d42fa81f503e827d00f9c5f30be517ca0f905f18be217c22f841f083df27bc2f745ee0bdb17b06f5c5eb0bd517a64f449e80bcf17986f24de31bc517864f085e08bc0177e2ef85de8bbc17762ee85dc13b7176e0ed85da8bb417662ec85d88bb107602ebc5d70bad175a0eb05d603ab17542ea81d48ba907502e9c5d30ba517482e8c5d10ba117402e7c5cf0b9e073c0e745ce0b9b17342e681cc8b9907302e601cb8b96172a2e505c98b9217222e405c78b8e171a2e341c6838d07182e2c5c50b8a07122e205c38b86170a2e105c18b8217040e081c1038026fe2df85bf037d16f64dec1bd0b7916f20de41bc0b7716ec2dd45b9937216e40dc45b8837016da6db05b58b6a16d40da45b3936616ca2d88db1036116c02d7c5af0b5d16ba0d6c9ad0b5a06b22d605ab8b5616aa2d541aa0b5316a60d485a88b5106a20d405a8034f169e0d3c1a6934c16944d245a48349068c6d145a20b4316842d0099f8b3b46742ce099c033806700cdc59b0b36066a2cd059a033316660ccc1990b3116602cbc5970b2d16528c95191931e5632ac6058a2311361a8c2c984930546064bfd17f0afc25f44bdcd7a92f235e04bb117512e735c68b7d16da2d835ae2b5496a0ad315a24b38d6612c8458e2b0d16092bc55708ad895a8ab2355e6ab0d558aa9254c6a94551929d65346a6094b129425226a3c9461a8a250aaa0c9410a7f34f2c9dc939a27124dc69acd34926724c6898492f1a5b34ae895492a0a4f549c292552392443484490091f8a3e147848e891c8a381466a8c85188a2f245c28acd1492254448288c5110a202436a86850c1217142c285450a0a11341a8825102a203240427f90fe11fa23ee67d0cf899ee33da27a8cf411e533c64780cef11db33ae874d0e729cb338e870d0e019bd337646e48db19b6036a26d40d919b0235c46b08d499a5434646794ce1198432886410c6998a331046188c2898232fc85eccbb297422e445b90b4316622c485790ad995832a8853d4a5a14652866500c9e2138426884c4c97192a424aa48148e99176224a439084310351fca3e907b20f151da839d87038dc41acc34906630c84182e2ed85ab0b051588299850309c41290235c43387f70f681d5838a06980c6c17d02d285640a0c125c22283e6070c0cd417a02a504aa08140d3013701e802940230004 0x602664515050000002660120760010010266601301100111830001010100830830a600303331000101001103501003100000000000004000000000000110040010000000094401010101106110141642676017206500006101072710041012161124605500464361492269332324442450831030a5360a51600853053483101010506350245005050543401603020363023624607261172676101000108301083100831010246317251100830830a600303a03432436012361010108301083010854301008308245303040237021071050104361107105128035207783107823107030934340070700072304002002502024500002082035039000025083402540254040083102034304210215120572021324633047a2302053461243016a3473047253612920101050150120290252601642122174572250426102051621162616299424301431a546034535601243016362431436143193453619231592512360105103123407253475351454174208431084310430a5436085340834072541021540236405403230654603723654172682543102501832510250174235125018254310854320a254037462325018325102458032540785430127832540782354078235407521725043725372546013912540725117254725192605193215047425392453174253172531725147253742517254072543684372517254725147253147254 15 4 4
def q44Ck := dagCheckNodeBin q44M q44G q44NB 526 q44St q44Mv q44L q44S q44T
def q44RA (token : Nat) : Bool :=
  let s := rootState q44N 10 token
  !dagAllowedRootBin q44M q44E s.2.1 || dagLocalBin q44M q44G (dagKnownClosesBin q44G q44C) s ||
  dagRefBin q44M 526 q44St q44Mv (fun p tok => dagFindLink (q44L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44RB0 : treeBlock 0 64 q44RA = true := by decide +kernel
theorem q44R : dagCheckRootsBin q44M q44G (dagKnownClosesBin q44G q44C) q44E (dagRefBin q44M 526 q44St q44Mv (fun p tok => dagFindLink (q44L p) tok) 0) q44N 10 = true := q44RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B0 : treeBlock 0 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B16 : treeBlock 16 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B32 : treeBlock 32 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B48 : treeBlock 48 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B64 : treeBlock 64 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B80 : treeBlock 80 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B96 : treeBlock 96 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B112 : treeBlock 112 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B128 : treeBlock 128 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B144 : treeBlock 144 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B160 : treeBlock 160 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B176 : treeBlock 176 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B192 : treeBlock 192 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B208 : treeBlock 208 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B224 : treeBlock 224 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B240 : treeBlock 240 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B256 : treeBlock 256 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B272 : treeBlock 272 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B288 : treeBlock 288 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B304 : treeBlock 304 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B320 : treeBlock 320 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B336 : treeBlock 336 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B352 : treeBlock 352 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B368 : treeBlock 368 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B384 : treeBlock 384 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B400 : treeBlock 400 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B416 : treeBlock 416 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B432 : treeBlock 432 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B448 : treeBlock 448 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B464 : treeBlock 464 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B480 : treeBlock 480 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B496 : treeBlock 496 16 q44Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44B512 : treeBlock 512 14 q44Ck = true := by decide +kernel
theorem q44Bk : treeBlock 0 526 q44Ck = true := (@treeBlock_merge 0 272 254 q44Ck (@treeBlock_merge 0 144 128 q44Ck (@treeBlock_merge 0 80 64 q44Ck (@treeBlock_merge 0 48 32 q44Ck (@treeBlock_merge 0 32 16 q44Ck (@treeBlock_merge 0 16 16 q44Ck q44B0 q44B16) q44B32) (@treeBlock_merge 48 16 16 q44Ck q44B48 q44B64)) (@treeBlock_merge 80 32 32 q44Ck (@treeBlock_merge 80 16 16 q44Ck q44B80 q44B96) (@treeBlock_merge 112 16 16 q44Ck q44B112 q44B128))) (@treeBlock_merge 144 64 64 q44Ck (@treeBlock_merge 144 32 32 q44Ck (@treeBlock_merge 144 16 16 q44Ck q44B144 q44B160) (@treeBlock_merge 176 16 16 q44Ck q44B176 q44B192)) (@treeBlock_merge 208 32 32 q44Ck (@treeBlock_merge 208 16 16 q44Ck q44B208 q44B224) (@treeBlock_merge 240 16 16 q44Ck q44B240 q44B256)))) (@treeBlock_merge 272 128 126 q44Ck (@treeBlock_merge 272 64 64 q44Ck (@treeBlock_merge 272 32 32 q44Ck (@treeBlock_merge 272 16 16 q44Ck q44B272 q44B288) (@treeBlock_merge 304 16 16 q44Ck q44B304 q44B320)) (@treeBlock_merge 336 32 32 q44Ck (@treeBlock_merge 336 16 16 q44Ck q44B336 q44B352) (@treeBlock_merge 368 16 16 q44Ck q44B368 q44B384))) (@treeBlock_merge 400 64 62 q44Ck (@treeBlock_merge 400 32 32 q44Ck (@treeBlock_merge 400 16 16 q44Ck q44B400 q44B416) (@treeBlock_merge 432 16 16 q44Ck q44B432 q44B448)) (@treeBlock_merge 464 32 30 q44Ck (@treeBlock_merge 464 16 16 q44Ck q44B464 q44B480) (@treeBlock_merge 496 16 14 q44Ck q44B496 q44B512)))))
theorem q44K : KnownBin q44C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q3Bin) q5Bin) q8Bin) q38Bin) q2Bin) q33Bin) q16Bin) q10Bin) q36Bin) q0Bin) q7Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Bin : BinLower q44M q44W q44G 11 := by
  apply lowerDagBin _ _ _ _ q44A _ _ _ q44K _ (fun _ b hb => dagNodeBounds_mem b hb) q44R q44Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q44C.all (fun b => q44M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q45M : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev q45G : Word := qGoal &&& q45M
abbrev q45W : List Word := projectDAGStock q45M qBase [0, 1, 4, 5, 6, 7]
def q45F : Bound := (q45M, q45W, 10, q45G)
def q45E := unpackWitnesses q45W [74384, 337040, 581728, 876688, 1155216, 1425504]
abbrev q45N : List Word := normStock q45M q45W
def q45C : List Bound := [q11F, q14F, q1F, q3F, q15F, q4F, q35F, q19F, q29F, q25F, q39F, q34F, q40F, q21F]
def q45S : DagSample := (0x3020820a00010800c0008c46022180c8062330088824320908c06220944225148301209101a09209201a0d20b0182c060a03030120d020b04c0e00884c22120184c6031018480422100886012088c4c07008884064330184c021201088050181c0826120884402140204201201209008248048041208a4422810088500a01028002810110880c0403012050, 62)
def q45L : DagLinkList := dagExtractLinks 0xcd066833419a0cd066833419a0cd06683341981cc065872c1903c6163031818c0c50e283103880c30e00ef47762ba0dd02e81740ba05d02e81740ba05c86e03700b70db06d05680b40588ec41620a7551928073c29e04f027813c09d0ce06609300970c81e3c3145852c0920410017b2bb91c0ed276713289902c045d1ae055caae05702b051de8a23679910c425472148a34066001 0x1af0505a2282d310351080a80305a6286a214164898b045057216ac210355060aa040d54192b00f950064b0c50d54282bd181580a0ac450552282a1141558a0a8850c36296621494c0bd7f060ca630582181288807e430302105c8100e4060a202c2e01067e1c3258c07c430370182910f9448646e42dcec381b90f1408a07a430508286131053c87e9c4334703e26b103190b9628404b2302301f0c40605c0204503e26b149310bd628524a2295c814b018a0968514a418a490f4c00449105947621a3110d1486684460444205920c1048c0640402e0185920c9008a06a03e310192231490d0bd648523f2291e9100ec0bc7205242a3020b145010a07e8323e2169a00f8c00647a832330199e2124ec8447403c394191c00f8b80646e02d3642f1a9148d00a4668503262918a148c08a45e05e2e0290e00ce968d343461946294da14ab48bd584538c22915014c94092420411b0188a0084b4032580130c00895c14e790a74146093628cd2144a9066404401a21909908aa407f5003ea7019c780c8a405e5002e270118780889a0b3470519862192a0cc9007c4705922828cbb10c8506640442122110f80fc7a0a72ac521d4298e210c6d0623445219036478148300443146917a308b314c550a42883213229091100440bc200530f0290700f834066180328582cc2414e0e0a216c5387621c4a14e05087148330a229c1110c24866104230702983010c14072080330301881008c040260003f 13 5 13 7 1
def q45D : Forest := fun i => decodeNode 7 20 0x6284b2264762840a303f22835628314283102f2e21f29219298282121fa1219a16291c42f1c4289b4189b21e9b82c9a6219a2219a2199a6291542f15a30146289442814419142169441913424922111201e114191001f100169042f0f2290f0290f4280e6290d4290d2290d02f0d0290d00c8900989829884198701787017070118782c864198601f0582c8482884419842210401f84829834298342183418832290303603a3482a3082629824290241902229022200202f02029820290201f02019820190262981229812198121181029810218101c810198101881011810098101f80 i
def q45T := dagTraceTagsBin q45M 62 (dagTagBases q45N 0xf6b2df53d0e1f1bd603c7f10edf83f7f5f2a6c18f9ec7fac1bf8ee9130ff1fcf81fc3fe90fffc0bff000fffff4c89 0xf6935f45d3e7f1bffbfd7fd3effdbf7b9f8a2cb97ded3f9e5bfc6ecb36ffdf7f07fd3fec27ffeffff2bbfffff67bc 62) 9 q45D
def q45St := dagTraceBin q45M q45N 9 q45D
def q45Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q45Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q45Mv := dagMoves ([([qS20, qS26, qS5], q45Mp0, q45Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45A : DagMovesOK q45M q45G 256 q45Mv := dagMovesOfCheck (by decide +kernel)
def q45NB : Nat → List Bound := dagNodeBounds q45C.toArray 0x1c4388710e21c4388709df5bab746dada3b0b596a9d51a6b48e89d11a0740672cd396b2c64ac838e711e12c13806f5de8bb5762ec5d1b856cad4d9ab155cea6d2ca3540e794d49772aa4d48a8f51aa2d44386506dfe3ea76ee6dbe36a6b4cf18e2ee5a6ad14a27b4aa8b5061d73846c8ca15f278438728c413a19c1b006 0x3130201002652700260110303024120211132130020330302015013277402027012108214133232121201120211251365321576501921a0a6922101d1044081740132403402102144134012301324740274901320505b815b769105a052a8012382603062160821ca01692498105cba698 11 3 4
def q45Ck := dagCheckNodeBin q45M q45G q45NB 91 q45St q45Mv q45L q45S q45T
def q45RA (token : Nat) : Bool :=
  let s := rootState q45N 9 token
  !dagAllowedRootBin q45M q45E s.2.1 || dagLocalBin q45M q45G (dagKnownClosesBin q45G q45C) s ||
  dagRefBin q45M 91 q45St q45Mv (fun p tok => dagFindLink (q45L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45RB0 : treeBlock 0 64 q45RA = true := by decide +kernel
theorem q45R : dagCheckRootsBin q45M q45G (dagKnownClosesBin q45G q45C) q45E (dagRefBin q45M 91 q45St q45Mv (fun p tok => dagFindLink (q45L p) tok) 0) q45N 9 = true := q45RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B0 : treeBlock 0 16 q45Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B16 : treeBlock 16 16 q45Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B32 : treeBlock 32 16 q45Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B48 : treeBlock 48 16 q45Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B64 : treeBlock 64 16 q45Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B80 : treeBlock 80 11 q45Ck = true := by decide +kernel
theorem q45Bk : treeBlock 0 91 q45Ck = true := (@treeBlock_merge 0 48 43 q45Ck (@treeBlock_merge 0 32 16 q45Ck (@treeBlock_merge 0 16 16 q45Ck q45B0 q45B16) q45B32) (@treeBlock_merge 48 32 11 q45Ck (@treeBlock_merge 48 16 16 q45Ck q45B48 q45B64) q45B80))
theorem q45K : KnownBin q45C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q21Bin) q40Bin) q34Bin) q39Bin) q25Bin) q29Bin) q19Bin) q35Bin) q4Bin) q15Bin) q3Bin) q1Bin) q14Bin) q11Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45Bin : BinLower q45M q45W q45G 10 := by
  apply lowerDagBin _ _ _ _ q45A _ _ _ q45K _ (fun _ b hb => dagNodeBounds_mem b hb) q45R q45Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q45C.all (fun b => q45M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q46M : Word := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev q46G : Word := qGoal &&& q46M
abbrev q46W : List Word := projectDAGStock q46M qBase [1, 2, 4, 5, 6, 7]
def q46F : Bound := (q46M, q46W, 9, q46G)
def q46E := unpackWitnesses q46W [74896, 338064, 581728, 876688, 1155216, 1425504]
abbrev q46N : List Word := normStock q46M q46W
def q46C : List Bound := [q1F, q4F, q7F, q18F, q22F, q27F, q37F, q40F]
def q46S : DagSample := (0x30088c0a0120886050480480c460321860a048340c0e00a058281203059209403048402203098c0640308920b0301c0c0502010820502014028441219048440804900822011100840104828940a21004221028100a01221004820110880c0403012050, 44)
def q46L : DagLinkList := dagExtractLinks 0x1242484819011c63844388110209c01788ec5c9390702e01c0344662b5951a464266d8c917220e1e40b001 0x3a0401d6202db141ec8a0364301c4280da0c1e40a0390501b6210d0138640843003d1a2103cc1406506030830178292a3149d08a4244301602e49a180d10616646014220480180300b9674601543019a0c0520a42685212418088178400a41c04d0c8281890804406121460304180811013c0b85e04c0f01e1720c0388801b05e0c82935c149250a61683167229039089a80a61402309a311421889d06010462072200301b8140c40805d0302e414149048a644421610298100c4040260003f 11 4 13 5 3
def q46D : Forest := fun i => decodeNode 5 18 0x6206a0a146214c841241845060f829300b8b430260a484292106080181c880601e18880582f120a444188c0463a31088c42220080dc2031080ba202e0806210098407e0 i
def q46T := dagTraceTagsBin q46M 44 (dagTagBases q46N 0x51c45df36e7f9d33f8c9dfe741e2773fe1ebe07dfe3feb3fb00dff0bc3beffa909 0xf9f55fff6e7d9c55f8f9dfe64beeb79fe0ebeb3cff5f3fbfb17dffbf77beffafbc 44) 8 q46D
def q46St := dagTraceBin q46M q46N 8 q46D
def q46Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q46Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q46Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q46Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q46Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q46Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q46Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q46Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q46Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q46Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q46Mv := dagMoves ([([qS8, qS7], q46Mp0, q46Mi0), ([qS26, qS27, qS8, qS7], q46Mp1, q46Mi1), ([qS24, qS29], q46Mp2, q46Mi2), ([qS26, qS27], q46Mp3, q46Mi3), ([qS24, qS29, qS8, qS7], q46Mp4, q46Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46A : DagMovesOK q46M q46G 256 q46Mv := dagMovesOfCheck (by decide +kernel)
def q46NB : Nat → List Bound := dagNodeBounds q46C.toArray 0xe8e8e8e8e8e8e8e8e8e8e8e1e0d9d8d8d8d8cac1b9b19b9182796a4c3306 0x24185820804344223ea88 8 3 3
def q46Ck := dagCheckNodeBin q46M q46G q46NB 30 q46St q46Mv q46L q46S q46T
def q46RA (token : Nat) : Bool :=
  let s := rootState q46N 8 token
  !dagAllowedRootBin q46M q46E s.2.1 || dagLocalBin q46M q46G (dagKnownClosesBin q46G q46C) s ||
  dagRefBin q46M 30 q46St q46Mv (fun p tok => dagFindLink (q46L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RB0 : treeBlock 0 64 q46RA = true := by decide +kernel
theorem q46R : dagCheckRootsBin q46M q46G (dagKnownClosesBin q46G q46C) q46E (dagRefBin q46M 30 q46St q46Mv (fun p tok => dagFindLink (q46L p) tok) 0) q46N 8 = true := q46RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46B0 : treeBlock 0 16 q46Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46B16 : treeBlock 16 14 q46Ck = true := by decide +kernel
theorem q46Bk : treeBlock 0 30 q46Ck = true := (@treeBlock_merge 0 16 14 q46Ck q46B0 q46B16)
theorem q46K : KnownBin q46C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q40Bin) q37Bin) q27Bin) q22Bin) q18Bin) q7Bin) q4Bin) q1Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Bin : BinLower q46M q46W q46G 9 := by
  apply lowerDagBin _ _ _ _ q46A _ _ _ q46K _ (fun _ b hb => dagNodeBounds_mem b hb) q46R q46Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q46C.all (fun b => q46M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q47M : Word := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev q47G : Word := qGoal &&& q47M
abbrev q47W : List Word := projectDAGStock q47M qBase [1, 3, 4, 5, 6, 7]
def q47F : Bound := (q47M, q47W, 10, q47G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q47Bin : BinLower q47M q47W q47G 10 := dagShiftLowerBin (width := 256) [qS1, qS10] q45Bin (by decide +kernel)
def q48M : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev q48G : Word := qGoal &&& q48M
abbrev q48W : List Word := projectDAGStock q48M qBase [0, 1, 2, 3, 4, 6, 7]
def q48F : Bound := (q48M, q48W, 11, q48G)
def q48E := unpackWitnesses q48W [74384, 337040, 600208, 864400, 1093704, 1417360, 1675336]
abbrev q48N : List Word := normStock q48M q48W
def q48C : List Bound := [q1F, q33F, q13F, q12F, q11F, q31F, q27F, q26F]
def q48S : DagSample := (0x2a850e2300a45031180c860a250184c0c160008848260148a0623030980a21030880030120d020b0490c80884c140b0502482450603418090a05828120182c301a018240a0d241300a090184c30190c0240c16482500c12050682219088240643241249009201080844051288249208242050201402844040250081080480482402092012201100884402100a8100824108840220148201048229108a0402810110880c0403012050, 75)
def q48L : DagLinkList := dagExtractLinks 0x3c1e0f0783c1e0e170381c0d1646e561b050a6303712903201 0x51175345c48175005c441352431450c100213e0e0e439341f0b42e2908c9422310f0b030290c4943020174705c9918c6433941be4063140fc40330c084201f0404c007f 9 4 12 5 1
def q48D : Forest := fun i => decodeNode 5 17 0x8baf45c7a18a50c120428838321c981f0a87830301a18890c040ba205c1219840fc20661021080f8404c20fe0 i
def q48T := dagTraceTagsBin q48M 75 (dagTagBases q48N 0xbfff40d21e0e73f9e3f9f7f9e1ed36bf87f3b80f5fe5e79fefbf1fffbc05d2604e263bfe3fff56edf2f20ff9dbfcfb33f877fbff211fbff819800ffffdfffe98889 0xbfff5bd27e3e7ff9e3f9f7fcfaed37bfdff3b80f5ff0ebafefbfafffbcc5d276cee6fbff5fe7562df2f967fadbfe7bfffe77fbff8cbfbffdffdfbffffdfffecddfc 75) 10 q48D
def q48St := dagTraceBin q48M q48N 10 q48D
def q48Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q48Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q48Mv := dagMoves ([([qS1], q48Mp0, q48Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48A : DagMovesOK q48M q48G 256 q48Mv := dagMovesOfCheck (by decide +kernel)
def q48NB : Nat → List Bound := dagNodeBounds q48C.toArray 0x1e9ed74777aacd62af56aad52a59056eb0d568c3292c4a04 0x102341204108201461460d8e914b446644650a44748a77 9 3 3
def q48Ck := dagCheckNodeBin q48M q48G q48NB 21 q48St q48Mv q48L q48S q48T
def q48RA (token : Nat) : Bool :=
  let s := rootState q48N 10 token
  !dagAllowedRootBin q48M q48E s.2.1 || dagLocalBin q48M q48G (dagKnownClosesBin q48G q48C) s ||
  dagRefBin q48M 21 q48St q48Mv (fun p tok => dagFindLink (q48L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48RB0 : treeBlock 0 64 q48RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48RB64 : treeBlock 64 64 q48RA = true := by decide +kernel
theorem q48R : dagCheckRootsBin q48M q48G (dagKnownClosesBin q48G q48C) q48E (dagRefBin q48M 21 q48St q48Mv (fun p tok => dagFindLink (q48L p) tok) 0) q48N 10 = true := (@treeBlock_merge 0 64 64 q48RA q48RB0 q48RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48B0 : treeBlock 0 16 q48Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48B16 : treeBlock 16 5 q48Ck = true := by decide +kernel
theorem q48Bk : treeBlock 0 21 q48Ck = true := (@treeBlock_merge 0 16 5 q48Ck q48B0 q48B16)
theorem q48K : KnownBin q48C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q26Bin) q27Bin) q31Bin) q11Bin) q12Bin) q13Bin) q33Bin) q1Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48Bin : BinLower q48M q48W q48G 11 := by
  apply lowerDagBin _ _ _ _ q48A _ _ _ q48K _ (fun _ b hb => dagNodeBounds_mem b hb) q48R q48Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q48C.all (fun b => q48M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q49M : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev q49G : Word := qGoal &&& q49M
abbrev q49W : List Word := projectDAGStock q49M qBase [0, 1, 2, 3, 4, 5, 6, 7]
def q49E := unpackWitnesses q49W [74384, 337040, 600208, 864400, 1106016, 1400976, 1679504, 1949792]
abbrev q49N : List Word := normStock q49M q49W
def q49C : List Bound := [q44F, q12F, q1F, q10F, q45F, q41F, q23F, q42F, q31F, q48F, q11F, q43F, q47F, q29F, q27F, q25F, q46F, q30F, q32F, q28F]
def q49S : DagSample := (0xe2300e0f1a21068b41a290026100300c0283008406220188c225148244068201a0c0a85120946031301841c1e008649058008c40a45031180c860a2500c260a8d4482c180e0142a060b03038301a0184c0c1609068181c1209805228188c0c26028840c22120b01229060b01828120d020b0490c83038022130502c140920914180d0602428160a048060b0c068060902834904c0282406130c064300903059209403048141a08864220910084042210088601202894c064028841028100a01422088c4c07008884064324124900920108144a2092482090814080500a1104864209848221040250081080480482402092012201100884402100a8100824108840220148201048229108a0402211028100a01221002810110880c0403012050, 128)
def q49L : DagLinkList := dagExtractLinks 0xe101c2038407080e101c187820f021e003c0038007000e001c0038007000e001c0038007000e001c0038007000e001bf877f06fe0dfc1bf837f06fe0dfc1bf837f06fe0dfc1bf837f06fe0dfc1bf837f06fe0dfc1bf837f06fe0df45bd8b7a0ef21de41bc07770eec1dd81ba87721ee02db85b6876c0ed61dac1b507690ed01da01b30b6416c61d883b087600ebe1d783ad135626a82d447a8835106a20d441a8074f0e9e0d3c1a7834f069e0d3c1a7834f069e0d3c1a7834f069e0d3c1a7834a2e940d281a5034a06940d281a5034a06940d281a5034a06940d281a5034a06940d281a5034a06940d281a5034a06940d281a5034a06940d281a5034a06940d243a4074806900d147a10f410e7e2cf839e873d06781cf019d0b390e701cc4f970f2c16561cac195072a06521c9c5928b240e480c8c391832306441c88191032206440c881900b1e163a1c7038e031c06361c6838c87180e300c5c38b0716062c0c5818b03131e241c40587870c1e161c2c185070626063be937c0af235e02bb477682ec0dd61ba457482e905d01b9857302e50dc81b885700ade15b82b7016e02dc05b42b6056b86d705ae0b5c16b82d705ae0b507688ecf15983b1115e22b825684ac47570eac15561aa45538aa515481a74f4b9a922d186a18d40967e1cf449d0d38126e14d6399c933826704ce099c1328a6314c2297c52f825f04be097c12f825f04be097c12f825f04ba296492b0e5414a61944528824e1c9a1930326024b0c960910f1e9e363c5e78a8b1502290c4e289070cae13342608293021a04040047fc2fa2de95bc667882eca5d42b9e571d0df25b54b6056a10cfa595532056400c42184230426004bf85783ae275a8eb1216012ba35458a32d403264e49d6909919422a44296838d0131ecb3a9870a4d75198b30945c28b2315c42a8851209d292e622d8402c8000e1017e227443d8866a07e806c80160001 0x5c80dab91141728402e54805b4844b881b56f0362e006d5b80d8b8a181718302e049c5bc8a0b7b1416e0462da4505b00fab181f16d8402d606d5b6900b501b56902ead006d59c09ab3017565036ac805d5b2120b591416cc482d44505a4880b41141672182cc440594880b210c36b640ad6c515a1882b2a0c96ba412d50825a591cb432096743f2cc83e5960e7b221f9644272c6c8058e900ae014559020e8e03151c0429c004d620462c5483560881a310c1470202c2480d14880ae0201572182c0480558880aa91015f2402bc480574920aa1101532202a44405818a2af21455d419eb443ed18864ad00f9460192c3080581901a291015f6402bc880577120a880c1500182b908053c880a711015b0262b6431568100ad52015984026e4225669009b1089352112684224cc8409910c1312102604304bc8409710c35824029e450d1c100ab9103562402ac4505548a1aa12415423029c45054c8a0a91141586402acc50551063a3020158a402acc50d3c900abb1f9566392aa839549062a891f94f23969207ed140e4a1008d536202a4840552904a9b141524282a048e538904a60175514202a0421d3d900a7b1414e418a9a4605308c0a6a1654c418a9208052c8faa511f14944029009c521062a080894764028c48051e900a2920146a4028ac80d10118a181734404628805c50c108a121814003ea7807c50a0c09f81f53b03e27c07d4e80f8a092713d03ea7207cd02124a0418b3f44927e862cf893d9e92493e23727a462cf19049e314b3b241276452ce811d9c82093a02f2720524e21209b91412d03ea3a07c4e31209b11412c03ea3807c4d48809581b51b0362684504a80fa8d01f13321825205d4c888098910128036a6044049c0fa9790c126036a5c440cdd9029bb14534620a648404c10649281b515019a6f4824da1049ab2393464125c8304900da99a1f93243926283e4b906491817530839e5e87ecb90e497a1392e42124405dcb592296b1852a628a4e8324948808a00c92dc492590924ad93c9532492422825288e4a107c91910127a41e4c88e4990bc91110125839e48c7349188791a1c923421244832c751028fa1ad1d428a3484148611c9021251fa41e3c88e4790bc8ed2091c64123688e4691048c82391702723008e45807c8c91011803622e4504580f88aa1411424622b483c4c11c8981791101e229483c4811c8901791322022407c4448808801f50f03e221483c3811c8701790f839a1c07c434118863202e60409a40513140825a00c499010908013432901728204e5028988041a600624c008483009e0848142c8f28501e4e40209860312cc04241004cef210dc608138c0a2610104b20189240212040268491b0e20289820412c40628400650701720c09c4140d88231b2f14181de430bf907d78a0c8fe21f1e2432b84102708144c0020df80299940427e006465008a068793e08448101e4e002097e0312000227ba0c90121f1de432b7c1026f8144be0208fe021400032310044ff4471fc4823780a25e8104fd0148fc0113f11047b20c8fb0471f403e3e40f87ba140ef2285ba0913740c2688144bc0209600311f4042768064ea0098ac0113e111c7ba20af42475e24823700a25d8104af0189ec029190042760064550089eb08e3d0904798124ba01895c0211f0022791278f14411e048e3bc9046d8144b902095a0311ec042770064500089db483bb110476214aeb0471d605e3ab127740278e903e1d006e39c078733204e36289be8513750666d1200ac21919c03e264064736240e58301c6c60b64920559102972185a40902600804900c0e58411c8c8e38d9047120e4db4189b24822a88806a8238d20411c2c6037d0c16c1240650180c40203859046e3108e04471be88237909c6da108d82411524423771246e3180db4301ae4922a0880698278d10490c80301400406d5202d96409b2c51b611026c2144d7419d9643ea5c8646580f8970191ac8793550826a11e4d321194e022b49902693144d141994c43234007c4900c8cf0170c402233a90466a238cc2149960823281386481b0c824718e43e3180f962b204c5628984c412f90825e20cc7a21116c03f316904624208c3647184c823050725ca0c479211180c822ed8845fa238be44117a84e2e50843c10c0bca41d76c822ed8a55d223ab944117485e2e50a43b90c0b884716ec492da9075ab238b562f568c902d18c0593140b0418d584902b08c0531142990481320602800b8490140560111694822cd91c593208b141c95a831aac9045511429f0475300822940ba45008caf62015a8402a48c02a80c08c0160a00202c290757b208af62955c88eab5104572178ad4295504822a08a551823e9b04194605f26c0a64780f4aca41156c822a98a054a144a841894e48e2989054e023a9704114405d22404652b180a442c9468312888c04881808801114308e28210448c1749f44113c44b2748924611049c041136c412448d84390c89a04e1334822619044b92089604712a08d2501184982149204112205d24005c2800888f62011c85c13c06146923a8c24111a45e2308a44591344f216d1509222a0c544a2488943151049ea1c9244411b88723109e43c2180fa4281f284648908c612058a23fa1407d4190f44401d80fa3881f0620280bc03e16c0662b00c884c4910709220993c40b2487b4180f24501d40fa3701f05001810088e1fd1043f20f87b4190f04409ac11d328208740368b803e1540643ed20e7c4474f68821f10bc3da148772204d408e9901043981b46a02f0c80521ea0e73cb1cc79621cf08721e10843ba0ca690398e405d1a40862d00cc76a41ceac831d58a73a2208744290e68321c8881340208680290b20329c28fe38c1cc7082dcdc8731bd0b637210c6d8470d88491ac904351088694280d047c19c13c330138654410c883218c11c310208610368c006c17c07c2800c85ea41cba88e1750bd2e12085c2290b78931690a02c91f25804f0b006e15c0782b520e554410aa85294811f28823a500410a806d14c0d829017c5102f0a005213c05b2722044e4288968411088821e908e3604086c0510b40821400c42201182c01313a90426b2084c4470968829189062510a4492118724218d41061a01442702084203112005223808c1a01082a01311990622a2083c41908848e10c9062112084121f0804330e486519820c3202884c0410800660a00843f00c87c0130340221ed20e3c4410788528ec91d1d120e3924107645e0e88a61c914a310418620530940820f80c4130108700190dc02605004436a4106ac830d18a219a20c324288628330c09040f10c82f04705c0830b41041600f82b0198340320a805c14808c0d01105107389d8e613b10e2643984c84309506609108a2403f84804f08c07e11520e21641042c5288110610214c1f418c3c4820788a50e823e1c0474360838681040e817c1c02f0360530680a40c80bc1801702e0230280440b520e1564182ac538511040a21481341902444083c11d07020e0d04102206d0400d80781780e02981a05203007c0580cc0a01901307381d0e604214c07421c0c47301888602908e0403980804300c06201008c010098000ff 15 5 13 9 1
def q49D : Forest := fun i => decodeNode 9 22 0x29016b8305009393e6284f01193aa404df1212da41496105256474959052543f49107d24839c8d09d23a40476906ea840369900da640365100d9c48362100d3218b46900cca40316900ac63f2ad8e4ab41caae904a96282a50a0a94202a0842a862829d062a742ca8d062a323ea7c8f89f4402750629ba40266900986402600b89304224a0c08a24e2220c48743121c8dc8723121d8a4862292180bc8602921b12084a411ea1047a6471e99047a43f1e50e47941f1e60e6784271e108478c491da1247664f1d9924764471d507c75a419d10bc748399cd886734211cd064738471c509271a419c10bc70a411bd9046f4471bd1046f2201a00d86822819c0f867a4196e9065a2201640f859220162906558399500f8530461469004e23c9340f24d23612c0324b017124138480361218d84743c9140f24521f10c03243447108904420149091044004710007c4003e0fd11c3d4410f40523d8470f09043c0248f093c3b4410e891c3a2410e80323aa418e50a43902f0e71263803e0e00dc3801e0e3120368410d591c356410d5072356410cd11c334410cd09c33c490c98c0324300ca900316288c50a2314198c50f2304208c08f2302118c18a22e4198b807c2e0170ba9042d4470b48522d0410b41382c0360b091c2b21f0ac0f82aa410a2104286470a19042841c8a19042744709d1042742709e906266290990bc2642909a11c256248969062462f092904226470899042241c88a906206290810bc204290829041f64107d8a01f42887d0621f24707c9041f6300790b21e4188788c01e8470761041d4410748961d2248741041d6208701381ca4106d9041b24106c11c1b04686c1181b04286c1041b02e86c05c1b6200690b81a22f0648a4192268660c4184310608dc182310600fa1803e0631241684905993c1664905911c1544105507c15a418510bc144290520e61362184d0841341904e906126298490a412419048880128398460b61142d84508611847041092102410408441042803c8f80f04f03c09c0f4410390640e0470381040e0368380d80e01f03a9060d42f0348a40dc498310a00c23e0300dc0c01e0329060b42902c0da0b03602c0be0b02f02c0a40b01682e9040864102111c0844102085208211820052080118219060744101c91c0724181c9040721f01c8660700c81c02607a418190a40622f0188a6062290180320600981a904056418158a2054418150a205419814904050470141060504101407c0501981405c050118160e6046218110860441981009e0401f8129060362900d0a60341880c8a40302f80c0bc0302980c0a40301780c05c0301180e906026298090a402419008880020368080d80202f0080a60202900807c02019808064028398050a6014218048860121180408601018804046010098041fe00 i
def q49T := dagTraceTagsBin q49M 128 (dagTagBases q49N 0xbb4414f7ffffd81a43c75d0cf0fe78efbf99ef2eff7ff9e1ed38fbb3ff0fe7f707fe6e036fadff2f3cff3fffcff1ffdf3effe3f80217ec98138fe7c8fdff1fffefe7a1d5b4dabbe5e41efcff3f6ff3fee21f1de019f877fffff1007fe3fffe3ff9efda7fc1ff877fbfffbe9107f7fff045f0ff9ffe0007fffefffffffe988909 0xbb88f4f7ffffdb7a4fcf5d3cf3fe78efbf99ef2eff7ffcfaed3bfbbbffbfe7f707fe6e036fadff875d7f5fffcffaffdf7fffebfe2317ec9db3bfebcbfdffafff47e7bfd5b4c23be5f2cefd7f5f6ff9fec67f1ff9ddfc77fffff4b6ffefffff5ffe7fdbffdbffc77fbfffbec4b3f7fffbfff7fffffefbbffffefffffffecddfbc 128) 13 q49D
def q49St := dagTraceBin q49M q49N 13 q49D
def q49Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q49Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q49Mv := dagMoves ([([qS1], q49Mp0, q49Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49A : DagMovesOK q49M q49G 256 q49Mv := dagMovesOfCheck (by decide +kernel)
def q49NB : Nat → List Bound := dagNodeBounds q49C.toArray 0x17a06f315e51bc47780aee9ddc1bb637686ec15d71baa574cae81dce2b96771d2e295c23b8056f8adcadb72b6876c8ad725ac2b509694ed11d9f3b3a566cacc95963b285644ec71d8b3b125618ec215813afc75ecebc95772aea55c52b6a56a3ace7594ab11d5f3ab69560eaa25513a9c752cea41d453a847500a9e9d376a6874c8a988d301a5c54b0a9515282a4a748ca8eb5158a247439286150a2a0e7414a811cff39f693e0e7b14f429e273bca75a4e839cc5390a7114df39b69364a6b94d259a0532d6641cc629885304e5f94bb497072d4e58a4af295872a4e531ca429445280a4f149b39307258a499c90391a7228e439c8439045200a3dac7928ee51c9637246b38d07194e31945e58b4915ce2a9452389e7130e23ac45288470ede1ba433485ad0a52131c22483ab068e0aac1238205034e051c0648067000dfe9bfa37ec8fccdf7a3eb47ccaf891ef9bdc37b44f609eb13d2479e6f349e593c9278e4f0d1e093bf2774aed91d99bad67564ea0dd29ba2373c8e5a1c9238c67126e18dc19b7f46f68de0dba236f56d86da4db22b6046b2ed58da99b5036988d211a2233e66766ce0d9b133426644cc09969b29464c6c8198d3314661ccc1657fb2fc35f26bd157822ed35d46b9cd6fc2db45b06b45d644ac4457aead9d56caaa354aaa8154bca92551aaa0ad3f9a7c34f269d5137b26964cc698cd301a5d34b469591299a50349a69215229a42347aa8e1519322f345868999119a1e5432a858d099a0f4418681d50129fd53f0a7d10f731ea43caa77d8ec39d2639aa7160e029bb536ca6c54d4c1a2733aa6650c8498b530ca5fdcbcb17182d8a5998add952929aa51d89f49386264c4b54942921722f4449485b9065202a3e607848eb51c7036a46a30cc818902e6c5aa0ae71458266447588680fd01e1839a86c70cea17e02bc0525096e10a41e3036605ee09e01038197026c03580338006 0xd2a040088406984d8b5410846119201185a01408340043008611860f1804010402009a03080250c02180451880110c23080400a802400451880311845008024004d009c010040100480804828048090a40bc4c0880512005114026002278051309a6104ca088ca30461298242c026108c11862d5044108c23240230910329a1150469290c608d8448c2308c8208c31009a0101411002250c2330461190a20904118461188820900110c2309160138613a820100ae1886100440100460a8015002030c230ac011814b0046118461185e00a0611854008c0a580221a9c30a801184612090008c23091058058440c43098626804011d43008e3008a310c23004e3080613406010c27185413ac1012820100430a82f1804908049008a6184ca0804800906004400886268040088a618540100221804202806188a00c406134c01014130801308a6134613046130490305a30982309826090460982011d43008e3008a311105038230806138c21009410090a091603880218488028614804800900120a31010311c02601422186013002300462854362802611c85804b009c01340272802504027002249c2b00801100220086210cc20804030c40188882840240ca1009e819402620a100989228281146c224402c80278046028223002278027185e00c085020c11184009c61220a311a1150469290461942640d842a4c440c408162a08d22010a508d852246c490a622167188058450508cac224713a8234ac850094009401181461002d430a11c5a8284621a8a11b46140c2a004a6184c309401580241140128023004882882c291234158448c4309862220a0105a30b0a448d84480a21856009623098625804c711601388b01dc5580ee3816e7a006704c03b9a07044078dc60be4058470620e00be4f80c327a0e05c0298802f73d0309dc00bda51bc3020d0702dc91bd00204910050f7206f21d2e42c01610e0430a440dab004f01282e6804e6a82049c526ac0a7b4e05852e69d0402d430c5aa0ace080969031b168201145a809d608092a5b80d639a0089c2581af281a19900931e114cd41380861260709923430873452134d2c21a6921cc170049505cb01c827a5600b124581071b5413ac092090b290024a98758082611cb680226248a734275804758049338eb0098921d412a00b1888b28d2031e1171c6a490a0585e5198e0205844140748d87490a6624802acec49005238012c5ed414811bdae29d600b08901507614891acac4910038c87481704b08b01d893ac0473d60624e6224ec22c08625ab01c8c490e0324ec201692b08b01d8922c07 15 4 5
def q49Ck := dagCheckNodeBin q49M q49G q49NB 371 q49St q49Mv q49L q49S q49T
def q49RA (token : Nat) : Bool :=
  let s := rootState q49N 13 token
  !dagAllowedRootBin q49M q49E s.2.1 || dagLocalBin q49M q49G (dagKnownClosesBin q49G q49C) s ||
  dagRefBin q49M 371 q49St q49Mv (fun p tok => dagFindLink (q49L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49RB0 : treeBlock 0 64 q49RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49RB64 : treeBlock 64 64 q49RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49RB128 : treeBlock 128 64 q49RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49RB192 : treeBlock 192 64 q49RA = true := by decide +kernel
theorem q49R : dagCheckRootsBin q49M q49G (dagKnownClosesBin q49G q49C) q49E (dagRefBin q49M 371 q49St q49Mv (fun p tok => dagFindLink (q49L p) tok) 0) q49N 13 = true := (@treeBlock_merge 0 128 128 q49RA (@treeBlock_merge 0 64 64 q49RA q49RB0 q49RB64) (@treeBlock_merge 128 64 64 q49RA q49RB128 q49RB192))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B0 : treeBlock 0 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B16 : treeBlock 16 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B32 : treeBlock 32 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B48 : treeBlock 48 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B64 : treeBlock 64 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B80 : treeBlock 80 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B96 : treeBlock 96 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B112 : treeBlock 112 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B128 : treeBlock 128 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B144 : treeBlock 144 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B160 : treeBlock 160 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B176 : treeBlock 176 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B192 : treeBlock 192 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B208 : treeBlock 208 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B224 : treeBlock 224 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B240 : treeBlock 240 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B256 : treeBlock 256 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B272 : treeBlock 272 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B288 : treeBlock 288 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B304 : treeBlock 304 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B320 : treeBlock 320 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B336 : treeBlock 336 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B352 : treeBlock 352 16 q49Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49B368 : treeBlock 368 3 q49Ck = true := by decide +kernel
theorem q49Bk : treeBlock 0 371 q49Ck = true := (@treeBlock_merge 0 192 179 q49Ck (@treeBlock_merge 0 96 96 q49Ck (@treeBlock_merge 0 48 48 q49Ck (@treeBlock_merge 0 32 16 q49Ck (@treeBlock_merge 0 16 16 q49Ck q49B0 q49B16) q49B32) (@treeBlock_merge 48 32 16 q49Ck (@treeBlock_merge 48 16 16 q49Ck q49B48 q49B64) q49B80)) (@treeBlock_merge 96 48 48 q49Ck (@treeBlock_merge 96 32 16 q49Ck (@treeBlock_merge 96 16 16 q49Ck q49B96 q49B112) q49B128) (@treeBlock_merge 144 32 16 q49Ck (@treeBlock_merge 144 16 16 q49Ck q49B144 q49B160) q49B176))) (@treeBlock_merge 192 96 83 q49Ck (@treeBlock_merge 192 48 48 q49Ck (@treeBlock_merge 192 32 16 q49Ck (@treeBlock_merge 192 16 16 q49Ck q49B192 q49B208) q49B224) (@treeBlock_merge 240 32 16 q49Ck (@treeBlock_merge 240 16 16 q49Ck q49B240 q49B256) q49B272)) (@treeBlock_merge 288 48 35 q49Ck (@treeBlock_merge 288 32 16 q49Ck (@treeBlock_merge 288 16 16 q49Ck q49B288 q49B304) q49B320) (@treeBlock_merge 336 32 3 q49Ck (@treeBlock_merge 336 16 16 q49Ck q49B336 q49B352) q49B368))))
theorem q49K : KnownBin q49C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q28Bin) q32Bin) q30Bin) q46Bin) q25Bin) q27Bin) q29Bin) q47Bin) q43Bin) q11Bin) q48Bin) q31Bin) q42Bin) q23Bin) q41Bin) q45Bin) q10Bin) q1Bin) q12Bin) q44Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49Bin : BinLower q49M q49W q49G 14 := by
  apply lowerDagBin _ _ _ _ q49A _ _ _ q49K _ (fun _ b hb => dagNodeBounds_mem b hb) q49R q49Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q49C.all (fun b => q49M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
theorem binLowerEq {m m2 : Word} {s s2 : List Word} {t t2 : Word} {k : Nat}
    (hm : m = m2) (hs : s = s2) (ht : t = t2) (h : BinLower m s t k) : BinLower m2 s2 t2 k := by
  subst hm; subst hs; subst ht; exact h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootLower : BinLower (fullMask 256) qBase qGoal 14 :=
  binLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) q49Bin

end PEqualNP.Outside.L_meta_34788.Cert

namespace PEqualNP.Outside.L_meta_34788

open PEqualNP.CircuitLowerBounds

def upperGates : List Gate :=
  [⟨.and, [0, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [18, 12]⟩, ⟨.or, [20, 15]⟩, ⟨.and, [19, 21]⟩]

def graphList : List Nat := [0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7]

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

end PEqualNP.Outside.L_meta_34788

namespace PEqualNP.Outside.L_meta_34788
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_34788.Contraction

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

end PEqualNP.Outside.L_meta_34788

theorem PEqualNP.Outside.L_meta_34788 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ hu
  apply PEqualNP.Outside.L_meta_34788.finish _ gates o hg hu
  exact PEqualNP.Outside.L_meta_34788.Cert.rootLower
