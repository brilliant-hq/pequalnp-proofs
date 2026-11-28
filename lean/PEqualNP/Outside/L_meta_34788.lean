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

def qS0 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def qS1 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def qS2 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 0)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def qS3 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 0)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def qS4 : WordMoveStep := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 1)])
def qS5 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def qS6 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def qS7 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0), (0x5555555555555555555555555555555555555555555555555555555555555555, 16)], [])
def qS8 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0), (0x3333333333333333333333333333333333333333333333333333333333333333, 8)], [])
def qS9 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS10 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def qS11 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def qS12 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def qS13 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 0)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def qS14 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def qS15 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def qS16 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def qS17 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def qS18 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def qS19 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def qS20 : WordMoveStep := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def qS21 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def qS22 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def qS23 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def qS24 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def qS25 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def qS26 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def qS27 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def qS28 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def qS29 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 4)])
def qS30 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 16)])
def qS31 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 64)])
def qS32 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 1)])
def qS33 : WordMoveStep := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 8)])
def qS34 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS35 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 4)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 4)])
def qS36 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def qS37 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def qS38 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 32)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def qS39 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def qS40 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555, 0), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0x5555555555555555555555555555555500000000000000000000000000000000, 127)])
def qS41 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 64)], [])
def qS42 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def qS43 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 2)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def qS44 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def qS45 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def qS46 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff, 0), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000, 112)])
def qS47 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333, 0), (0xcccccccccccccccccccccccccccccccc, 126)], [(0x3333333333333333333333333333333300000000000000000000000000000000, 126)])
def qBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def qGoal : Word := 0xfffffffffffffffffffffffffffefffefffffffefffffefcffeeffeeeeccaa00
def q0M : Word := 0x1040208
abbrev q0G : Word := qGoal &&& q0M
abbrev q0W : List Word := projectDAGStock q0M qBase [0, 1]
def q0E := unpackWitnesses q0W [4632, 271384]
abbrev q0N : List Word := normStock q0M q0W
def q0C : List Bound := []
def q0S : DagSample := (0x184806090c0483009, 4)
def q0L : DagLinkList := dagExtractLinks 0x9 0x3 2 1 2 1 1
def q0D : Forest := fun i => decodeNode 1 3 0x6 i
def q0T := dagTraceTagsBin q0M 4 (dagTagBases q0N 0xa5 0xcc 4) 2 q0D
def q0St := dagTraceBin q0M q0N 2 q0D
def q0Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q0Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q0Mv := dagMoves ([([qS0, qS1], q0Mp0, q0Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0A : DagMovesOK q0M q0G 256 q0Mv := dagMovesOfCheck (by decide +kernel)
def q0NB : Nat → List Bound := dagNodeBounds q0C.toArray 0x0 0x0 2 1 1
def q0Ck := dagCheckNodeBin q0M q0G q0NB 1 q0St q0Mv q0L q0S q0T
def q0RA (token : Nat) : Bool :=
  let s := rootState q0N 2 token
  !dagAllowedRootBin q0M q0E s.2.1 || dagLocalBin q0M q0G (dagKnownClosesBin q0G q0C) s ||
  dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0RB0 : treeBlock 0 4 q0RA = true := by decide +kernel
theorem q0R : dagCheckRootsBin q0M q0G (dagKnownClosesBin q0G q0C) q0E (dagRefBin q0M 1 q0St q0Mv (fun p tok => dagFindLink (q0L p) tok) 0) q0N 2 = true := q0RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0B0 : treeBlock 0 1 q0Ck = true := by decide +kernel
theorem q0Bk : treeBlock 0 1 q0Ck = true := q0B0
theorem q0K : KnownBin q0C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Bin : BinLower q0M q0W q0G 3 := by
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
def q1M : Word := 0x60000000000000600
abbrev q1G : Word := qGoal &&& q1M
abbrev q1W : List Word := projectDAGStock q1M qBase [0, 3]
def q1F : Bound := (q1M, q1W, 3, q1G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1Bin : BinLower q1M q1W q1G 3 := dagShiftLowerBin (width := 256) [qS2, qS3, qS4, qS5, qS6, qS7, qS8] q0Bin (by decide +kernel)
def q2M : Word := 0x100020000000001000200
abbrev q2G : Word := qGoal &&& q2M
abbrev q2W : List Word := projectDAGStock q2M qBase [0, 3]
def q2F : Bound := (q2M, q2W, 3, q2G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2Bin : BinLower q2M q2W q2G 3 := dagShiftLowerBin (width := 256) [qS9, qS3, qS4, qS5, qS6, qS7, qS8] q0Bin (by decide +kernel)
def q3M : Word := 0x1000000040000010000000400
abbrev q3G : Word := qGoal &&& q3M
abbrev q3W : List Word := projectDAGStock q3M qBase [1, 3]
def q3F : Bound := (q3M, q3W, 3, q3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q3Bin : BinLower q3M q3W q3G 3 := dagShiftLowerBin (width := 256) [qS10, qS3, qS0, qS5, qS6, qS7, qS8] q0Bin (by decide +kernel)
def q4M : Word := 0x1000100000000010001000000
abbrev q4G : Word := qGoal &&& q4M
abbrev q4W : List Word := projectDAGStock q4M qBase [3, 4]
def q4F : Bound := (q4M, q4W, 3, q4G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4Bin : BinLower q4M q4W q4G 3 := dagShiftLowerBin (width := 256) [qS10, qS3, qS11, qS12, qS6, qS1, qS7, qS8] q0Bin (by decide +kernel)
def q5M : Word := 0x1000200000000000100020000000000000000
abbrev q5G : Word := qGoal &&& q5M
abbrev q5W : List Word := projectDAGStock q5M qBase [0, 6]
def q5F : Bound := (q5M, q5W, 3, q5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5Bin : BinLower q5M q5W q5G 3 := dagShiftLowerBin (width := 256) [qS9, qS13, qS14, qS15, qS16, qS17, qS18, qS7, qS8] q0Bin (by decide +kernel)
def q6M : Word := 0x1010000000000000101000000000000000000
abbrev q6G : Word := qGoal &&& q6M
abbrev q6W : List Word := projectDAGStock q6M qBase [3, 6]
def q6F : Bound := (q6M, q6W, 3, q6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6Bin : BinLower q6M q6W q6G 3 := dagShiftLowerBin (width := 256) [qS9, qS13, qS11, qS14, qS6, qS16, qS17, qS18, qS7, qS8] q0Bin (by decide +kernel)
def q7M : Word := 0x10001000000000001000100000000000000000000
abbrev q7G : Word := qGoal &&& q7M
abbrev q7W : List Word := projectDAGStock q7M qBase [4, 6]
def q7F : Bound := (q7M, q7W, 3, q7G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q7Bin : BinLower q7M q7W q7G 3 := dagShiftLowerBin (width := 256) [qS10, qS13, qS19, qS20, qS14, qS21, qS16, qS18, qS7, qS8] q0Bin (by decide +kernel)
def q8M : Word := 0x30300000303
abbrev q8G : Word := qGoal &&& q8M
abbrev q8W : List Word := projectDAGStock q8M qBase [0, 3, 5]
def q8F : Bound := (q8M, q8W, 4, q8G)
def q8E := unpackWitnesses q8W [16928, 282656, 544776]
abbrev q8N : List Word := normStock q8M q8W
def q8C : List Bound := []
def q8S : DagSample := (0x40244021008840209100a01028, 6)
def q8L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 3
def q8D : Forest := fun i => decodeNode 1 4 0xe i
def q8T := dagTraceTagsBin q8M 6 (dagTagBases q8N 0x3624 0x337ad 6) 3 q8D
def q8St := dagTraceBin q8M q8N 3 q8D
def q8Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q8Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q8Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q8Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q8Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q8Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q8Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q8Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q8Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q8Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q8Mv := dagMoves ([([qS22], q8Mp0, q8Mi0), ([qS11], q8Mp1, q8Mi1), ([qS23, qS22], q8Mp2, q8Mi2), ([qS11, qS22], q8Mp3, q8Mi3), ([qS23], q8Mp4, q8Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8A : DagMovesOK q8M q8G 256 q8Mv := dagMovesOfCheck (by decide +kernel)
def q8NB : Nat → List Bound := dagNodeBounds q8C.toArray 0x0 0x0 2 1 1
def q8Ck := dagCheckNodeBin q8M q8G q8NB 1 q8St q8Mv q8L q8S q8T
def q8RA (token : Nat) : Bool :=
  let s := rootState q8N 3 token
  !dagAllowedRootBin q8M q8E s.2.1 || dagLocalBin q8M q8G (dagKnownClosesBin q8G q8C) s ||
  dagRefBin q8M 1 q8St q8Mv (fun p tok => dagFindLink (q8L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8RB0 : treeBlock 0 8 q8RA = true := by decide +kernel
theorem q8R : dagCheckRootsBin q8M q8G (dagKnownClosesBin q8G q8C) q8E (dagRefBin q8M 1 q8St q8Mv (fun p tok => dagFindLink (q8L p) tok) 0) q8N 3 = true := q8RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8B0 : treeBlock 0 1 q8Ck = true := by decide +kernel
theorem q8Bk : treeBlock 0 1 q8Ck = true := q8B0
theorem q8K : KnownBin q8C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8Bin : BinLower q8M q8W q8G 4 := by
  apply lowerDagBin _ _ _ _ q8A _ _ _ q8K _ (fun _ b hb => dagNodeBounds_mem b hb) q8R q8Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q8C.all (fun b => q8M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q9M : Word := 0x500050000000000050005
abbrev q9G : Word := qGoal &&& q9M
abbrev q9W : List Word := projectDAGStock q9M qBase [1, 4, 6]
def q9F : Bound := (q9M, q9W, 4, q9G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q9Bin : BinLower q9M q9W q9G 4 := dagShiftLowerBin (width := 256) [qS0, qS1, qS18] q8Bin (by decide +kernel)
def q10M : Word := 0x30300000000000000000000000000000303
abbrev q10G : Word := qGoal &&& q10M
abbrev q10W : List Word := projectDAGStock q10M qBase [0, 3, 7]
def q10F : Bound := (q10M, q10W, 4, q10G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q10Bin : BinLower q10M q10W q10G 4 := dagShiftLowerBin (width := 256) [qS24, qS25] q8Bin (by decide +kernel)
def q11M : Word := 0x30000000300000000000000000000000300000003
abbrev q11G : Word := qGoal &&& q11M
abbrev q11W : List Word := projectDAGStock q11M qBase [0, 5, 7]
def q11F : Bound := (q11M, q11W, 4, q11G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q11Bin : BinLower q11M q11W q11G 4 := dagShiftLowerBin (width := 256) [qS22, qS26, qS24, qS25] q8Bin (by decide +kernel)
def q12M : Word := 0x50000000500000000000000000000000500000005
abbrev q12G : Word := qGoal &&& q12M
abbrev q12W : List Word := projectDAGStock q12M qBase [1, 5, 7]
def q12F : Bound := (q12M, q12W, 4, q12G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Bin : BinLower q12M q12W q12G 4 := dagShiftLowerBin (width := 256) [qS0, qS22, qS26, qS24, qS25] q8Bin (by decide +kernel)
def q13M : Word := 0x1010000010100000000000000000000010100000101
abbrev q13G : Word := qGoal &&& q13M
abbrev q13W : List Word := projectDAGStock q13M qBase [3, 5, 7]
def q13F : Bound := (q13M, q13W, 4, q13G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q13Bin : BinLower q13M q13W q13G 4 := dagShiftLowerBin (width := 256) [qS11, qS5, qS6, qS22, qS26, qS24, qS25] q8Bin (by decide +kernel)
def q14M : Word := 0x5000000000000000500000000000000050000000000000005
abbrev q14G : Word := qGoal &&& q14M
abbrev q14W : List Word := projectDAGStock q14M qBase [1, 6, 7]
def q14F : Bound := (q14M, q14W, 4, q14G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Bin : BinLower q14M q14W q14G 4 := dagShiftLowerBin (width := 256) [qS0, qS16, qS17, qS24] q8Bin (by decide +kernel)
def q15M : Word := 0x11000000000000001100000000000000110000000000000011
abbrev q15G : Word := qGoal &&& q15M
abbrev q15W : List Word := projectDAGStock q15M qBase [2, 6, 7]
def q15F : Bound := (q15M, q15W, 4, q15G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Bin : BinLower q15M q15W q15G 4 := dagShiftLowerBin (width := 256) [qS27, qS28, qS16, qS17, qS24] q8Bin (by decide +kernel)
def q16M : Word := 0x303000003030
abbrev q16G : Word := qGoal &&& q16M
abbrev q16W : List Word := projectDAGStock q16M qBase [0, 3, 5]
def q16F : Bound := (q16M, q16W, 4, q16G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Bin : BinLower q16M q16W q16G 4 := dagShiftLowerBin (width := 256) [qS29] q8Bin (by decide +kernel)
def q17M : Word := 0x303000003030000
abbrev q17G : Word := qGoal &&& q17M
abbrev q17W : List Word := projectDAGStock q17M qBase [0, 3, 5]
def q17F : Bound := (q17M, q17W, 4, q17G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Bin : BinLower q17M q17W q17G 4 := dagShiftLowerBin (width := 256) [qS30] q8Bin (by decide +kernel)
def q18M : Word := 0x303000003030000000000000000
abbrev q18G : Word := qGoal &&& q18M
abbrev q18W : List Word := projectDAGStock q18M qBase [0, 3, 5]
def q18F : Bound := (q18M, q18W, 4, q18G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q18Bin : BinLower q18M q18W q18G 4 := dagShiftLowerBin (width := 256) [qS31] q8Bin (by decide +kernel)
def q19M : Word := 0xa000a00000000000a000a
abbrev q19G : Word := qGoal &&& q19M
abbrev q19W : List Word := projectDAGStock q19M qBase [1, 4, 6]
def q19F : Bound := (q19M, q19W, 4, q19G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q19Bin : BinLower q19M q19W q19G 4 := dagShiftLowerBin (width := 256) [qS32, qS0, qS1, qS18] q8Bin (by decide +kernel)
def q20M : Word := 0x50005000000000005000500
abbrev q20G : Word := qGoal &&& q20M
abbrev q20W : List Word := projectDAGStock q20M qBase [1, 4, 6]
def q20F : Bound := (q20M, q20W, 4, q20G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q20Bin : BinLower q20M q20W q20G 4 := dagShiftLowerBin (width := 256) [qS33, qS0, qS1, qS18] q8Bin (by decide +kernel)
def q21M : Word := 0x300000003000000000000000000000003000000030000
abbrev q21G : Word := qGoal &&& q21M
abbrev q21W : List Word := projectDAGStock q21M qBase [0, 5, 7]
def q21F : Bound := (q21M, q21W, 4, q21G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q21Bin : BinLower q21M q21W q21G 4 := dagShiftLowerBin (width := 256) [qS30, qS22, qS26, qS24, qS25] q8Bin (by decide +kernel)
def q22M : Word := 0xa0005000a0005
abbrev q22G : Word := qGoal &&& q22M
abbrev q22W : List Word := projectDAGStock q22M qBase [0, 1, 5]
def q22F : Bound := (q22M, q22W, 4, q22G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q22Bin : BinLower q22M q22W q22G 4 := dagShiftLowerBin (width := 256) [qS9, qS28, qS6] q8Bin (by decide +kernel)
def q23M : Word := 0x500000505000005
abbrev q23G : Word := qGoal &&& q23M
abbrev q23W : List Word := projectDAGStock q23M qBase [1, 3, 5]
def q23F : Bound := (q23M, q23W, 4, q23G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q23Bin : BinLower q23M q23W q23G 4 := dagShiftLowerBin (width := 256) [qS9, qS0] q8Bin (by decide +kernel)
def q24M : Word := 0x50000000050000005000000005
abbrev q24G : Word := qGoal &&& q24M
abbrev q24W : List Word := projectDAGStock q24M qBase [1, 2, 6]
def q24F : Bound := (q24M, q24W, 4, q24G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24Bin : BinLower q24M q24W q24G 4 := dagShiftLowerBin (width := 256) [qS10, qS0, qS6, qS18] q8Bin (by decide +kernel)
def q25M : Word := 0xc0300000000000000000000000000000c03
abbrev q25G : Word := qGoal &&& q25M
abbrev q25W : List Word := projectDAGStock q25M qBase [0, 1, 7]
def q25F : Bound := (q25M, q25W, 4, q25G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25Bin : BinLower q25M q25W q25G 4 := dagShiftLowerBin (width := 256) [qS34, qS28, qS6, qS24, qS25] q8Bin (by decide +kernel)
def q26M : Word := 0xa0005000000000000000000000000000a0005
abbrev q26G : Word := qGoal &&& q26M
abbrev q26W : List Word := projectDAGStock q26M qBase [0, 1, 7]
def q26F : Bound := (q26M, q26W, 4, q26G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26Bin : BinLower q26M q26W q26G 4 := dagShiftLowerBin (width := 256) [qS9, qS28, qS6, qS24, qS25] q8Bin (by decide +kernel)
def q27M : Word := 0xa0000000000000005000000000000000a0000000000000005
abbrev q27G : Word := qGoal &&& q27M
abbrev q27W : List Word := projectDAGStock q27M qBase [0, 1, 7]
def q27F : Bound := (q27M, q27W, 4, q27G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27Bin : BinLower q27M q27W q27G 4 := dagShiftLowerBin (width := 256) [qS3, qS28, qS6, qS24, qS25] q8Bin (by decide +kernel)
def q28M : Word := 0x22000000000000001100000000000000220000000000000011
abbrev q28G : Word := qGoal &&& q28M
abbrev q28W : List Word := projectDAGStock q28M qBase [0, 2, 7]
def q28F : Bound := (q28M, q28W, 4, q28G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q28Bin : BinLower q28M q28W q28G 4 := dagShiftLowerBin (width := 256) [qS3, qS6, qS24, qS25] q8Bin (by decide +kernel)
def q29M : Word := 0x500000500000000000000000000000005000005
abbrev q29G : Word := qGoal &&& q29M
abbrev q29W : List Word := projectDAGStock q29M qBase [1, 3, 7]
def q29F : Bound := (q29M, q29W, 4, q29G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q29Bin : BinLower q29M q29W q29G 4 := dagShiftLowerBin (width := 256) [qS9, qS0, qS24, qS25] q8Bin (by decide +kernel)
def q30M : Word := 0x1100000000000000001100000000000011000000000000000011
abbrev q30G : Word := qGoal &&& q30M
abbrev q30W : List Word := projectDAGStock q30M qBase [2, 3, 7]
def q30F : Bound := (q30M, q30W, 4, q30G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Bin : BinLower q30M q30W q30G 4 := dagShiftLowerBin (width := 256) [qS3, qS27, qS28, qS24, qS25] q8Bin (by decide +kernel)
def q31M : Word := 0x1000000000001000100000000000100010000000000010001000000000001
abbrev q31G : Word := qGoal &&& q31M
abbrev q31W : List Word := projectDAGStock q31M qBase [4, 6, 7]
def q31F : Bound := (q31M, q31W, 4, q31G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Bin : BinLower q31M q31W q31G 4 := dagShiftLowerBin (width := 256) [qS10, qS20, qS12, qS21, qS16, qS24] q8Bin (by decide +kernel)
def q32M : Word := 0x500050000000000500050
abbrev q32G : Word := qGoal &&& q32M
abbrev q32W : List Word := projectDAGStock q32M qBase [1, 2, 4]
def q32F : Bound := (q32M, q32W, 4, q32G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Bin : BinLower q32M q32W q32G 4 := dagShiftLowerBin (width := 256) [qS3, qS35, qS0, qS6, qS26] q8Bin (by decide +kernel)
def q33M : Word := 0x500050000000005000500
abbrev q33G : Word := qGoal &&& q33M
abbrev q33W : List Word := projectDAGStock q33M qBase [1, 3, 4]
def q33F : Bound := (q33M, q33W, 4, q33G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Bin : BinLower q33M q33W q33G 4 := dagShiftLowerBin (width := 256) [qS3, qS36, qS0, qS26] q8Bin (by decide +kernel)
def q34M : Word := 0x3000000030000030000000300
abbrev q34G : Word := qGoal &&& q34M
abbrev q34W : List Word := projectDAGStock q34M qBase [0, 3, 5]
def q34F : Bound := (q34M, q34W, 4, q34G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Bin : BinLower q34M q34W q34G 4 := dagShiftLowerBin (width := 256) [qS3] q8Bin (by decide +kernel)
def q35M : Word := 0x11000000000000001100000000000000220000000000000022
abbrev q35G : Word := qGoal &&& q35M
abbrev q35W : List Word := projectDAGStock q35M qBase [0, 2, 6]
def q35F : Bound := (q35M, q35W, 4, q35G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Bin : BinLower q35M q35W q35G 4 := dagShiftLowerBin (width := 256) [qS13, qS4, qS6, qS18] q8Bin (by decide +kernel)
def q36M : Word := 0x30300000000000003030000000000000000
abbrev q36G : Word := qGoal &&& q36M
abbrev q36W : List Word := projectDAGStock q36M qBase [0, 3, 6]
def q36F : Bound := (q36M, q36W, 4, q36G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q36Bin : BinLower q36M q36W q36G 4 := dagShiftLowerBin (width := 256) [qS13, qS37, qS18] q8Bin (by decide +kernel)
def q37M : Word := 0x11000000000000001100000000000011000000000000001100
abbrev q37G : Word := qGoal &&& q37M
abbrev q37W : List Word := projectDAGStock q37M qBase [2, 3, 6]
def q37F : Bound := (q37M, q37W, 4, q37G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q37Bin : BinLower q37M q37W q37G 4 := dagShiftLowerBin (width := 256) [qS13, qS36, qS27, qS28, qS18] q8Bin (by decide +kernel)
def q38M : Word := 0x30000000300000003000000030000000000000000
abbrev q38G : Word := qGoal &&& q38M
abbrev q38W : List Word := projectDAGStock q38M qBase [0, 5, 6]
def q38F : Bound := (q38M, q38W, 4, q38G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q38Bin : BinLower q38M q38W q38G 4 := dagShiftLowerBin (width := 256) [qS13, qS37, qS22, qS26, qS18] q8Bin (by decide +kernel)
def q39M : Word := 0x11000000000000001100000011000000000000001100000000
abbrev q39G : Word := qGoal &&& q39M
abbrev q39W : List Word := projectDAGStock q39M qBase [2, 5, 6]
def q39F : Bound := (q39M, q39W, 4, q39G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q39Bin : BinLower q39M q39W q39G 4 := dagShiftLowerBin (width := 256) [qS13, qS38, qS27, qS28, qS22, qS26, qS18] q8Bin (by decide +kernel)
def q40M : Word := 0x11000000000011000000000000000000110000000000110000
abbrev q40G : Word := qGoal &&& q40M
abbrev q40W : List Word := projectDAGStock q40M qBase [2, 4, 7]
def q40F : Bound := (q40M, q40W, 4, q40G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Bin : BinLower q40M q40W q40G 4 := dagShiftLowerBin (width := 256) [qS3, qS19, qS27, qS28, qS1, qS24, qS25] q8Bin (by decide +kernel)
def q41M : Word := 0xa000a0000000005000500
abbrev q41G : Word := qGoal &&& q41M
abbrev q41W : List Word := projectDAGStock q41M qBase [0, 1, 4]
def q41F : Bound := (q41M, q41W, 4, q41G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Bin : BinLower q41M q41W q41G 4 := dagShiftLowerBin (width := 256) [qS34, qS3, qS28, qS6, qS26] q8Bin (by decide +kernel)
def q42M : Word := 0x30000000300000c0000000c00
abbrev q42G : Word := qGoal &&& q42M
abbrev q42W : List Word := projectDAGStock q42M qBase [0, 1, 5]
def q42F : Bound := (q42M, q42W, 4, q42G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Bin : BinLower q42M q42W q42G 4 := dagShiftLowerBin (width := 256) [qS34, qS3, qS28, qS6] q8Bin (by decide +kernel)
def q43M : Word := 0x3000000030300000003000000
abbrev q43G : Word := qGoal &&& q43M
abbrev q43W : List Word := projectDAGStock q43M qBase [0, 3, 5]
def q43F : Bound := (q43M, q43W, 4, q43G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Bin : BinLower q43M q43W q43G 4 := dagShiftLowerBin (width := 256) [qS9, qS3] q8Bin (by decide +kernel)
def q44M : Word := 0x50005000000000000000005000500
abbrev q44G : Word := qGoal &&& q44M
abbrev q44W : List Word := projectDAGStock q44M qBase [1, 3, 4]
def q44F : Bound := (q44M, q44W, 4, q44G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Bin : BinLower q44M q44W q44G 4 := dagShiftLowerBin (width := 256) [qS10, qS3, qS36, qS0, qS26] q8Bin (by decide +kernel)
def q45M : Word := 0x3030000030300000000000000000000030300000303
abbrev q45G : Word := qGoal &&& q45M
abbrev q45W : List Word := projectDAGStock q45M qBase [0, 3, 5, 7]
def q45F : Bound := (q45M, q45W, 7, q45G)
def q45E := unpackWitnesses q45W [66176, 331904, 606336, 868384]
abbrev q45N : List Word := normStock q45M q45W
def q45C : List Bound := [q10F, q8F, q11F, q13F]
def q45S : DagSample := (0x100844028040a0100940204020940220108800a0402214028040a0, 12)
def q45L : DagLinkList := dagExtractLinks 0x884420300789e02c01 0x68300504c3c8420c83234442044323304e320420303e020328183369433194236103311023010130000f 9 4 12 3 5
def q45D : Forest := fun i => decodeNode 3 15 0x10614131a19203e4064804c8078 i
def q45T := dagTraceTagsBin q45M 12 (dagTagBases q45N 0x63388f1f8f44 0xfb3cef3fef5d 12) 6 q45D
def q45St := dagTraceBin q45M q45N 6 q45D
def q45Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q45Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q45Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q45Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q45Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q45Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q45Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q45Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q45Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q45Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q45Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q45Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q45Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q45Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q45Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q45Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q45Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 3, 6, 5] 0 i.val)
def q45Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 7, 6, 0] 0 i.val)
def q45Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q45Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q45Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 5, 6, 3] 0 i.val)
def q45Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 5, 6, 0] 0 i.val)
def q45Mp11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q45Mi11 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q45Mp12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q45Mi12 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q45Mp13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q45Mi13 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q45Mp14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 3, 4, 0, 6, 5] 0 i.val)
def q45Mi14 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 7, 6, 0] 0 i.val)
def q45Mp15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q45Mi15 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q45Mv := dagMoves ([([qS24], q45Mp0, q45Mi0), ([qS22], q45Mp1, q45Mi1), ([qS39, qS24], q45Mp2, q45Mi2), ([qS22, qS24], q45Mp3, q45Mi3), ([qS39], q45Mp4, q45Mi4), ([qS11], q45Mp5, q45Mi5), ([qS11, qS24], q45Mp6, q45Mi6), ([qS23, qS22], q45Mp7, q45Mi7), ([qS40, qS39, qS24], q45Mp8, q45Mi8), ([qS23, qS22, qS24], q45Mp9, q45Mi9), ([qS40, qS39], q45Mp10, q45Mi10), ([qS11, qS22], q45Mp11, q45Mi11), ([qS11, qS39, qS24], q45Mp12, q45Mi12), ([qS23], q45Mp13, q45Mi13), ([qS40, qS24], q45Mp14, q45Mi14), ([qS23, qS39], q45Mp15, q45Mi15)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45A : DagMovesOK q45M q45G 256 q45Mv := dagMovesOfCheck (by decide +kernel)
def q45NB : Nat → List Bound := dagNodeBounds q45C.toArray 0x16ac4a9105204 0x63e1e1 7 3 2
def q45Ck := dagCheckNodeBin q45M q45G q45NB 7 q45St q45Mv q45L q45S q45T
def q45RA (token : Nat) : Bool :=
  let s := rootState q45N 6 token
  !dagAllowedRootBin q45M q45E s.2.1 || dagLocalBin q45M q45G (dagKnownClosesBin q45G q45C) s ||
  dagRefBin q45M 7 q45St q45Mv (fun p tok => dagFindLink (q45L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45RB0 : treeBlock 0 16 q45RA = true := by decide +kernel
theorem q45R : dagCheckRootsBin q45M q45G (dagKnownClosesBin q45G q45C) q45E (dagRefBin q45M 7 q45St q45Mv (fun p tok => dagFindLink (q45L p) tok) 0) q45N 6 = true := q45RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45B0 : treeBlock 0 7 q45Ck = true := by decide +kernel
theorem q45Bk : treeBlock 0 7 q45Ck = true := q45B0
theorem q45K : KnownBin q45C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q13Bin) q11Bin) q8Bin) q10Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45Bin : BinLower q45M q45W q45G 7 := by
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
def q46M : Word := 0xf000f000000000f000f00
abbrev q46G : Word := qGoal &&& q46M
abbrev q46W : List Word := projectDAGStock q46M qBase [0, 1, 3, 4]
def q46F : Bound := (q46M, q46W, 6, q46G)
def q46E := unpackWitnesses q46W [12824, 296513, 565272, 827969]
abbrev q46N : List Word := normStock q46M q46W
def q46C : List Bound := [q2F, q33F, q1F]
def q46S : DagSample := (0x414082192090c140b0502482510c064300904024301a201081442050688209201403050, 16)
def q46L : DagLinkList := dagExtractLinks 0x808079717054493a0e01 0x403c4030bc3eb4323c2e342238403440283c24231831902f8823101f0813000f 8 3 11 4 1
def q46D : Forest := fun i => decodeNode 4 15 0x306080710081e14231062207c409880f0 i
def q46T := dagTraceTagsBin q46M 16 (dagTagBases q46N 0x807bcf8739b45bcc 0x9bfbe7e7fcbe9bd9 16) 5 q46D
def q46St := dagTraceBin q46M q46N 5 q46D
def q46Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q46Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q46Mv := dagMoves ([([qS12], q46Mp0, q46Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46A : DagMovesOK q46M q46G 256 q46Mv := dagMovesOfCheck (by decide +kernel)
def q46NB : Nat → List Bound := dagNodeBounds q46C.toArray 0x2082081d652343 0x9109 6 2 2
def q46Ck := dagCheckNodeBin q46M q46G q46NB 9 q46St q46Mv q46L q46S q46T
def q46RA (token : Nat) : Bool :=
  let s := rootState q46N 5 token
  !dagAllowedRootBin q46M q46E s.2.1 || dagLocalBin q46M q46G (dagKnownClosesBin q46G q46C) s ||
  dagRefBin q46M 9 q46St q46Mv (fun p tok => dagFindLink (q46L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RB0 : treeBlock 0 16 q46RA = true := by decide +kernel
theorem q46R : dagCheckRootsBin q46M q46G (dagKnownClosesBin q46G q46C) q46E (dagRefBin q46M 9 q46St q46Mv (fun p tok => dagFindLink (q46L p) tok) 0) q46N 5 = true := q46RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46B0 : treeBlock 0 9 q46Ck = true := by decide +kernel
theorem q46Bk : treeBlock 0 9 q46Ck = true := q46B0
theorem q46K : KnownBin q46C := (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q1Bin) q33Bin) q2Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Bin : BinLower q46M q46W q46G 6 := by
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
def q47M : Word := 0x30300000303000000000000000000000303000003030000
abbrev q47G : Word := qGoal &&& q47M
abbrev q47W : List Word := projectDAGStock q47M qBase [0, 3, 5, 7]
def q47F : Bound := (q47M, q47W, 7, q47G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q47Bin : BinLower q47M q47W q47G 7 := dagShiftLowerBin (width := 256) [qS30] q45Bin (by decide +kernel)
def q48M : Word := 0x30300000030300000000000000000000303000000303
abbrev q48G : Word := qGoal &&& q48M
abbrev q48W : List Word := projectDAGStock q48M qBase [0, 2, 3, 7]
def q48F : Bound := (q48M, q48W, 7, q48G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q48Bin : BinLower q48M q48W q48G 7 := dagShiftLowerBin (width := 256) [qS10, qS21, qS1, qS26] q45Bin (by decide +kernel)
def q49M : Word := 0xa0005000a00050000000000000000000a0005000a0005
abbrev q49G : Word := qGoal &&& q49M
abbrev q49W : List Word := projectDAGStock q49M qBase [0, 1, 5, 7]
def q49F : Bound := (q49M, q49W, 7, q49G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q49Bin : BinLower q49M q49W q49G 7 := dagShiftLowerBin (width := 256) [qS9, qS28, qS6] q45Bin (by decide +kernel)
def q50M : Word := 0xa0000000a00000005000000050000000a0000000a0000000500000005
abbrev q50G : Word := qGoal &&& q50M
abbrev q50W : List Word := projectDAGStock q50M qBase [0, 1, 5, 7]
def q50F : Bound := (q50M, q50W, 7, q50G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q50Bin : BinLower q50M q50W q50G 7 := dagShiftLowerBin (width := 256) [qS3, qS28, qS6] q45Bin (by decide +kernel)
def q51M : Word := 0x30300000000000000000000030300000303000000000000000000000303
abbrev q51G : Word := qGoal &&& q51M
abbrev q51W : List Word := projectDAGStock q51M qBase [0, 3, 5, 7]
def q51F : Bound := (q51M, q51W, 7, q51G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q51Bin : BinLower q51M q51W q51G 7 := dagShiftLowerBin (width := 256) [qS3] q45Bin (by decide +kernel)
def q52M : Word := 0x50000050500000500000000000000000500000505000005
abbrev q52G : Word := qGoal &&& q52M
abbrev q52W : List Word := projectDAGStock q52M qBase [1, 3, 5, 7]
def q52F : Bound := (q52M, q52W, 7, q52G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q52Bin : BinLower q52M q52W q52G 7 := dagShiftLowerBin (width := 256) [qS9, qS0] q45Bin (by decide +kernel)
def q53M : Word := 0xa000500000000000a000500000000000a000500000000000a0005
abbrev q53G : Word := qGoal &&& q53M
abbrev q53W : List Word := projectDAGStock q53M qBase [0, 1, 6, 7]
def q53F : Bound := (q53M, q53W, 7, q53G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q53Bin : BinLower q53M q53W q53G 7 := dagShiftLowerBin (width := 256) [qS9, qS28, qS6, qS18] q45Bin (by decide +kernel)
def q54M : Word := 0x500005000000000050000500000000005000050000000000500005
abbrev q54G : Word := qGoal &&& q54M
abbrev q54W : List Word := projectDAGStock q54M qBase [1, 2, 6, 7]
def q54F : Bound := (q54M, q54W, 7, q54G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q54Bin : BinLower q54M q54W q54G 7 := dagShiftLowerBin (width := 256) [qS9, qS0, qS6, qS18] q45Bin (by decide +kernel)
def q55M : Word := 0x5000000005000000500000000500000050000000050000005000000005
abbrev q55G : Word := qGoal &&& q55M
abbrev q55W : List Word := projectDAGStock q55M qBase [1, 2, 6, 7]
def q55F : Bound := (q55M, q55W, 7, q55G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q55Bin : BinLower q55M q55W q55G 7 := dagShiftLowerBin (width := 256) [qS10, qS0, qS6, qS18] q45Bin (by decide +kernel)
def q56M : Word := 0x5000000000005000500000000000500050000000000050005000000000005
abbrev q56G : Word := qGoal &&& q56M
abbrev q56W : List Word := projectDAGStock q56M qBase [1, 4, 6, 7]
def q56F : Bound := (q56M, q56W, 7, q56G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q56Bin : BinLower q56M q56W q56G 7 := dagShiftLowerBin (width := 256) [qS10, qS0, qS1, qS18] q45Bin (by decide +kernel)
def q57M : Word := 0x30303030c0c0c0c
abbrev q57G : Word := qGoal &&& q57M
abbrev q57W : List Word := projectDAGStock q57M qBase [0, 1, 3, 4]
def q57F : Bound := (q57M, q57W, 6, q57G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q57Bin : BinLower q57M q57W q57G 6 := dagShiftLowerBin (width := 256) [qS10, qS20, qS12, qS1, qS41] q46Bin (by decide +kernel)
def q58M : Word := 0xf0000000f00000f0000000f00
abbrev q58G : Word := qGoal &&& q58M
abbrev q58W : List Word := projectDAGStock q58M qBase [0, 1, 3, 5]
def q58F : Bound := (q58M, q58W, 6, q58G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q58Bin : BinLower q58M q58W q58G 6 := dagShiftLowerBin (width := 256) [qS3, qS36, qS0, qS26, qS41] q46Bin (by decide +kernel)
def q59M : Word := 0x3030000030300000000000000000000303000003030
abbrev q59G : Word := qGoal &&& q59M
abbrev q59W : List Word := projectDAGStock q59M qBase [0, 2, 3, 5]
def q59F : Bound := (q59M, q59W, 7, q59G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q59Bin : BinLower q59M q59W q59G 7 := dagShiftLowerBin (width := 256) [qS13, qS35, qS21, qS1, qS17, qS18, qS25] q45Bin (by decide +kernel)
def q60M : Word := 0x30003000300030300030003000300
abbrev q60G : Word := qGoal &&& q60M
abbrev q60W : List Word := projectDAGStock q60M qBase [0, 3, 4, 5]
def q60F : Bound := (q60M, q60W, 6, q60G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q60Bin : BinLower q60M q60W q60G 6 := dagShiftLowerBin (width := 256) [qS3, qS36, qS20, qS12, qS21, qS26, qS41] q46Bin (by decide +kernel)
def q61M : Word := 0x50005000500050500050005000500
abbrev q61G : Word := qGoal &&& q61M
abbrev q61W : List Word := projectDAGStock q61M qBase [1, 3, 4, 5]
def q61F : Bound := (q61M, q61W, 6, q61G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q61Bin : BinLower q61M q61W q61G 6 := dagShiftLowerBin (width := 256) [qS3, qS23, qS42, qS41] q46Bin (by decide +kernel)
def q62M : Word := 0x30003000c000c00030003000c000c
abbrev q62G : Word := qGoal &&& q62M
abbrev q62W : List Word := projectDAGStock q62M qBase [0, 1, 4, 6]
def q62F : Bound := (q62M, q62W, 6, q62G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q62Bin : BinLower q62M q62W q62G 6 := dagShiftLowerBin (width := 256) [qS10, qS43, qS12, qS1, qS17, qS18, qS41] q46Bin (by decide +kernel)
def q63M : Word := 0x303030300000000030303030000000000000000
abbrev q63G : Word := qGoal &&& q63M
abbrev q63W : List Word := projectDAGStock q63M qBase [0, 3, 4, 6]
def q63F : Bound := (q63M, q63W, 6, q63G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q63Bin : BinLower q63M q63W q63G 6 := dagShiftLowerBin (width := 256) [qS13, qS20, qS12, qS21, qS16, qS17, qS18, qS41] q46Bin (by decide +kernel)
def q64M : Word := 0x3030000030300000303000003030000000000000000
abbrev q64G : Word := qGoal &&& q64M
abbrev q64W : List Word := projectDAGStock q64M qBase [0, 3, 5, 6]
def q64F : Bound := (q64M, q64W, 7, q64G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q64Bin : BinLower q64M q64W q64G 7 := dagShiftLowerBin (width := 256) [qS13, qS37, qS25] q45Bin (by decide +kernel)
def q65M : Word := 0x300030003000300030003000300030000000000000000
abbrev q65G : Word := qGoal &&& q65M
abbrev q65W : List Word := projectDAGStock q65M qBase [0, 4, 5, 6]
def q65F : Bound := (q65M, q65W, 6, q65G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q65Bin : BinLower q65M q65W q65G 6 := dagShiftLowerBin (width := 256) [qS13, qS20, qS12, qS21, qS16, qS26, qS41] q46Bin (by decide +kernel)
def q66M : Word := 0x10101010101010101010101010101010000000000000000
abbrev q66G : Word := qGoal &&& q66M
abbrev q66W : List Word := projectDAGStock q66M qBase [3, 4, 5, 6]
def q66F : Bound := (q66M, q66W, 6, q66G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q66Bin : BinLower q66M q66W q66G 6 := dagShiftLowerBin (width := 256) [qS13, qS20, qS5, qS21, qS16, qS26, qS18, qS41] q46Bin (by decide +kernel)
def q67M : Word := 0x30300000303000000000303000003030000000000000000
abbrev q67G : Word := qGoal &&& q67M
abbrev q67W : List Word := projectDAGStock q67M qBase [0, 3, 4, 5]
def q67F : Bound := (q67M, q67W, 7, q67G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q67Bin : BinLower q67M q67W q67G 7 := dagShiftLowerBin (width := 256) [qS3, qS13, qS17, qS18, qS25] q45Bin (by decide +kernel)
def q68M : Word := 0xf0f0f0f0f0f0f0f
abbrev q68G : Word := qGoal &&& q68M
abbrev q68W : List Word := projectDAGStock q68M qBase [0, 1, 3, 4, 5]
def q68F : Bound := (q68M, q68W, 7, q68G)
def q68E := unpackWitnesses q68W [25136, 287792, 553008, 799754, 1077272]
abbrev q68N : List Word := normStock q68M q68W
def q68C : List Bound := [q8F, q17F, q22F, q23F]
def q68S : DagSample := (0xa030280884c140b05024060b0c06806090184c30190c024141a088642209040244021080480422100886012008241028100a01422008840412088c42221, 28)
def q68L : DagLinkList := dagExtractLinks 0xe38e31341 0x405c3843a04f9043202f1023001f 6 3 12 3 1
def q68D : Forest := fun i => decodeNode 3 15 0x2e2843205e408c80f8 i
def q68T := dagTraceTagsBin q68M 28 (dagTagBases q68N 0xc210f74c96f0eb2081f1fdd276f93ffe984 0xda73f74e26fbeba58dfaf9d936fcfffecdf 28) 6 q68D
def q68St := dagTraceBin q68M q68N 6 q68D
def q68Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q68Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q68Mv := dagMoves ([([qS11], q68Mp0, q68Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68A : DagMovesOK q68M q68G 256 q68Mv := dagMovesOfCheck (by decide +kernel)
def q68NB : Nat → List Bound := dagNodeBounds q68C.toArray 0x4072a9084 0x9378 7 3 2
def q68Ck := dagCheckNodeBin q68M q68G q68NB 5 q68St q68Mv q68L q68S q68T
def q68RA (token : Nat) : Bool :=
  let s := rootState q68N 6 token
  !dagAllowedRootBin q68M q68E s.2.1 || dagLocalBin q68M q68G (dagKnownClosesBin q68G q68C) s ||
  dagRefBin q68M 5 q68St q68Mv (fun p tok => dagFindLink (q68L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68RB0 : treeBlock 0 32 q68RA = true := by decide +kernel
theorem q68R : dagCheckRootsBin q68M q68G (dagKnownClosesBin q68G q68C) q68E (dagRefBin q68M 5 q68St q68Mv (fun p tok => dagFindLink (q68L p) tok) 0) q68N 6 = true := q68RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68B0 : treeBlock 0 5 q68Ck = true := by decide +kernel
theorem q68Bk : treeBlock 0 5 q68Ck = true := q68B0
theorem q68K : KnownBin q68C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q23Bin) q22Bin) q17Bin) q8Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q68Bin : BinLower q68M q68W q68G 7 := by
  apply lowerDagBin _ _ _ _ q68A _ _ _ q68K _ (fun _ b hb => dagNodeBounds_mem b hb) q68R q68Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q68C.all (fun b => q68M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q69M : Word := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
abbrev q69G : Word := qGoal &&& q69M
abbrev q69W : List Word := projectDAGStock q69M qBase [0, 1, 3, 6, 7]
def q69E := unpackWitnesses q69W [66176, 328832, 594048, 884864, 1151048]
abbrev q69N : List Word := normStock q69M q69W
def q69C : List Bound := [q14F, q10F, q36F, q25F, q27F]
def q69S : DagSample := (0x30082c12432082430502c14090182c904a01824064324124900905128824920824100940204804201209008201a0402090422100880520802810110880c0403008281, 30)
def q69L : DagLinkList := dagExtractLinks 0x1c0e070363b0d86c36165923543801 0x170b8980c430108701d1403224056422f474521087c1d0ca342906832880bc14130201f53c43270670d10c1a11e204fc2086480fc8819a202f420460807c08098001f 9 4 12 4 3
def q69D : Forest := fun i => decodeNode 4 16 0x85c90194015443e34323832204c203e2423101f1013101f0 i
def q69T := dagTraceTagsBin q69M 30 (dagTagBases q69N 0x28421ceee4b78f5f4103e3f0e93bfc47ffd108 0x2b4e7ceef137d75f4b1bf5f8ec9bfebfffdbbd 30) 7 q69D
def q69St := dagTraceBin q69M q69N 7 q69D
def q69Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q69Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 2, 3, 4, 5, 1, 7] 0 i.val)
def q69Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q69Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 4, 5, 3, 7] 0 i.val)
def q69Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 0, 2, 1, 4, 5, 3, 7] 0 i.val)
def q69Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 6, 4, 5, 0, 7] 0 i.val)
def q69Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q69Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q69Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q69Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 6, 2, 0, 4, 5, 1, 7] 0 i.val)
def q69Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 6, 4, 5, 0, 7] 0 i.val)
def q69Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 0, 2, 1, 4, 5, 3, 7] 0 i.val)
def q69Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 4, 5, 0, 7] 0 i.val)
def q69Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 3, 2, 1, 4, 5, 0, 7] 0 i.val)
def q69Mv := dagMoves ([([qS14], q69Mp0, q69Mi0), ([qS0, qS16], q69Mp1, q69Mi1), ([qS44, qS14, qS16], q69Mp2, q69Mi2), ([qS11], q69Mp3, q69Mi3), ([qS11, qS14], q69Mp4, q69Mi4), ([qS0, qS5, qS16], q69Mp5, q69Mi5), ([qS44, qS5], q69Mp6, q69Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69A : DagMovesOK q69M q69G 256 q69Mv := dagMovesOfCheck (by decide +kernel)
def q69NB : Nat → List Bound := dagNodeBounds q69C.toArray 0x90907469685a5858432b1302 0x2304028140a041 8 3 3
def q69Ck := dagCheckNodeBin q69M q69G q69NB 12 q69St q69Mv q69L q69S q69T
def q69RA (token : Nat) : Bool :=
  let s := rootState q69N 7 token
  !dagAllowedRootBin q69M q69E s.2.1 || dagLocalBin q69M q69G (dagKnownClosesBin q69G q69C) s ||
  dagRefBin q69M 12 q69St q69Mv (fun p tok => dagFindLink (q69L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69RB0 : treeBlock 0 32 q69RA = true := by decide +kernel
theorem q69R : dagCheckRootsBin q69M q69G (dagKnownClosesBin q69G q69C) q69E (dagRefBin q69M 12 q69St q69Mv (fun p tok => dagFindLink (q69L p) tok) 0) q69N 7 = true := q69RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69B0 : treeBlock 0 12 q69Ck = true := by decide +kernel
theorem q69Bk : treeBlock 0 12 q69Ck = true := q69B0
theorem q69K : KnownBin q69C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q27Bin) q25Bin) q36Bin) q10Bin) q14Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q69Bin : BinLower q69M q69W q69G 8 := by
  apply lowerDagBin _ _ _ _ q69A _ _ _ q69K _ (fun _ b hb => dagNodeBounds_mem b hb) q69R q69Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q69C.all (fun b => q69M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q70M : Word := 0xf000f000f000f0f000f000f000f00
abbrev q70G : Word := qGoal &&& q70M
abbrev q70W : List Word := projectDAGStock q70M qBase [0, 1, 3, 4, 5]
def q70F : Bound := (q70M, q70W, 9, q70G)
def q70E := unpackWitnesses q70W [49760, 312416, 544864, 843872, 1098305]
abbrev q70N : List Word := normStock q70M q70W
def q70C : List Bound := [q33F, q46F, q58F, q4F, q34F, q2F, q61F, q1F, q3F, q43F, q44F, q60F, q41F, q42F]
def q70S : DagSample := (0x801a301081061201c08250040e080523014014520410830522082c30700510cc029208a48009300e010290414082190518880282090c140b0502482510c0643009050a8c062050a03038301c0302804024c0610c068804205108141a201403050040a0820920984c028, 47)
def q70L : DagLinkList := dagExtractLinks 0x19a8335066a0cd419a8335066a0cd419a8335066a0cd419a8335066a0cd419a8335066a0cd419a07330e660ccc199833306660ccc199833306622cbc5968b2b16541ca4394072806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500c947910f2206440c8819103210e401c80190031f0e3c1c7818f031e063a1c7038d0b18162c2c5438a8315062a0c50389871306260c4c1888b100e1e1c3c187830f06164c2838313050e024c0417e92fc0df80bec37d06fa05f40be817c86f80dee1bd837a86f125da4bb417492e80dd00b9c37382e705cc1b9817302e225c21b8036f86dd15ba0b7036d86da0db40b6436c06d425a42b4056802ce15982b285640ac6158a1b1035e9eba1d6e3ad835a86b40d661ab0f548ea61d482a8c3508a9f153c1a7814f029e053c0a7054e029a15321a6034b0a94151c6a34346068b0d122a2414406870d064a0453f8a7d14f629e833c86780cec29d0539867304e609cc139067204e409c433882700cde19bc137066e04da19b4136066b0cd419a813296602cb65958b2a0a511c9e293072396422c8408f0d1e023254548890d0abe1314168820704020043eca7b90f511ea03c8678c2ef15d833a4671d6dfa1b7436076b08d1299e232c86314c3198032eab5b50b2a16122aea5582aa85502a9844f5e9c91298246646d0863d0c020c641807f20fb19dcd3a886dbcdb01aa6354065a8c9118282f865e84b73150f265e43c868f897d0bba07fc0170001 0x24a43ce4803c64804c24a01c64804ce4801c64803c24602c64803c24802c24804c24603424604ca420351e402124201524003d644029244019244840244c40242850242c501fc0101f80202408401f6020a3605c1e2020240c4023e04c9fe0509fa05023c04c23e44063c43823c4401f4430e3a44e63a42ea3a04e23a02e1f2020a1605c21602c20c01c1e00101f0020a0604e9ee04220601e1ee012a0204e9ec04220201e1ec0121ea02023a040a1c05c23ac401da02023604c23403c23203c62404022403022e02c20802062c43e62243222c42e22242262a03e62003222a02e22002222803c61e04023805ce38c49a3884963843e23842e2380502040301d801023645023405c23005c22e05c236c5023485022803c23284223043e22e43220442da2a05c22c01ca2a05c22a01c22805c1d801c20443c22604c22645c1d602022445c21e44c21c05c21604c21403c21204c22483221a03e21803d21003c20a03520803220402da2045c22242c20e04ca2045c22042c20c04c21e84021c45021a05c21845c21644221404e21204d21004c20e04520c0421d601d20a45c60604c20203c20845c60604c20603c20445c2020441fe43c2004501e40505f44401f643c5fc44c200c509de43c1fe4289e20501fa4201f84205f64401f64305f68401fc43c1fa84e1f883e1f68321e804e1e20425dc03e1d843c1d642c1f48401f4c401f244c1f24401ea42c1f04321e604e1e00421d601d5ee44c1ec43c5ee44c1ee43c1ec4441da42c1ea44c1da43c1e802c1e80201e603c1e4c501e243c9e2c501e24301e044c1de0501dc04c1dec501dc0401da02c1da43c1d843c1d843c1d644c1d485090a0519c003510a0211c00151d28405960411b203d1080211c80191d4c5096e05d1b003d0ce0211be0151d2c405ae04d1ae03d5c60291c601990c0511ac02d1aa03d1d00191ce0155b604d1060111040211cc0191ca0151c8c421c68421a843d1c405e1c204e1c0c521be8521bc4521ba4421020219b48521b442194405e8f405214401e0f4012db30529b2c529b885e5b24411b24311b842994205e8f205214201e0f20129b10601b08401aa4401a043894006c14002c13401c0cc0105b2c501ae8401a28381b644c59a05c0f00209a4c5e1b4c4e1b2c421b08521ae8421a683a1ac45e1aa45294805e8f805219a04e5940420fa0210ee0201a80191a684013e02c1a4c521a28421a045219e44e94605e8f605219804e59204219c46c14a44c0ec020d9b052d98c5e99a85299845e59a04159803919a02119801999705219684192a45e8e845219044118e44012a42e0e842297c05e17c02e92846c12843c11e42c0ca42097a06c18a05c17a03c17802c19705019445c0e643018c05c995052992c5e19444119243997405e17401e19105018ec40d7245e57242e97205e17202e98d05218c44191805e8e205211801e0e201291645e8e045211642e0e042298005e18002e988c4318a44318843392c04f91404e8ea0438de04212c01f11401e0ea0130de01291245e8dc45211242e0dc42297e05e58604c18203c17e02e91045e8da45211042e0da42298405e58604c18603c18402e90e45e8d845210e42e0d842297005e18204417002e0d643018005c17e05417004c17cc4217a85217845217644e91a05e8e405217404e17204217003d0ae02116e86016c46c8fe06014804c16846c55c45c15c44c15843c52a05012a04014203c11003056f05116ec5155684e15683e15205d15005c54004e52804214003e12803256cc5116c85153c03e52603213c02e12602256044e16043e53a04e52404213a03e12403256ac4316a84316883354c03f53803e52e03352203214c02f13802e12e02312202296245c55e44e15e43e16642c53604e52004213603e12003296245c56444e16443e16242c53404e51e04213403e11e03216046c15e4640aa42c13004c15cc4215a85e15884215645214e05e90005253204e51c04214a03d0aa01115445c152860d4ec4994e84915045054e03e14e02e14c46c14a44c10e0400a8020148c5214685e14484e14284210e83d14045213e42a13c05e13a05d13805c13605513405213204e13003d0a801d12e86c10e44c0a643012c05c12ac4212885212645e12445d12245c12045511e45211c44e0a642d11a05e11804e11604d11404c11204511004210e03d10a84010c8388fc4600f844c8ce0600c204c5088501088401048304e84500e84400f243c0da4300be03c10ac52108c4210684e1048420fe45e0fc4524f044e4e64420fa43d0ee43c1024250d405e0ce0524bc04e0c603d500c491008494fe4320fe4224ba03e0ba02ecfd0518fcc514fc8420fc832cb844e8b843e4b804e0b803e0fa8400d84400a842c0f8c520f685e0f484e0f28420d883d0f04420ee4300ec4220d205e0cc0524b604e0b20310a801d0d884c0a683c0ea45c0ae43c0e8c420e68420e445e0e244e0e044d0de44c0dc4450da4420d843d0d642d0d005e0ca0524b404e0c403d0a602d4d44320d44224d203e4d00320d202e0d0022ccf0518cec514ce8420ce8324cc44e4ca4420cc43e0ca4324c804e0c803e0c68400c44400c2c520c085e0be8420bc4420ba05e0b80520b604e0b40420b284c0b005c0ae03c0ac04c4aa84e0aa83e4a844e4a64420a843e0a6432ca10528a0c528948520a44534a04410a043109442185605f83405347604107603108802d06002105601f034013c9f05189ec510a4c4349e84209e83249844209843285405d48604f47404308603f07403305402d04a01d01a0110a2c520a0c4209e85209c84209a45e09845209644e09444285805f83605348404f47204308203d03202104401d092019090015012011885053882c5288085f87e85e87c85384485208e84f08c84e08a84308884205e83d08645308444308243108042b07e42907c42304442183e05f83c05e82805382605207a04f07804e47004346e04205e03103e01f03c01e028013026012873053076c4207485307284383a45f83845e82445382245207044f06e44e06c44306a44205e43d03a42f03842e02442302242285c05f85a05e81205206804e06604d06404c06204506004205e03d05c02f05a02e012022459053058c53056c4305485205245e05045d04e45c04c45504a45244844f44644e44444204843f04643e04443201042d04205f04005e83005382e05243e04f43c04e43a04343804203e03f03c03e03a033038032010021437053036c53034c4343284203283203045f02e45e02c45302a45242844f42644e42444342244202843f02643e02443302243201042d02005f01e05e01c05301a05241804f41604e41404341204201803f01603e01403301203201002dc0ac4380a84300e83300c44340a43300a42380404f80204340803f40603300802f00602300401f00201300001f 15 5 13 9 2
def q70D : Forest := fun i => decodeNode 9 22 0xe42009904026409880e4628381880d8220338880cd6202e80a0a86282850a09f42127487c9d2192740389c00e26c0b89922e25d064922162448589042023c8a08e02e2348b88c22122c09c8b026a2c0988b022a2c0848b22e2288b88901e2248b8880222218a07f2141f4878794271e107c784191e1880742201c88647021e1b88886d2261b00406a01e1a58a06821819c898666281740805c21e160878552261518a05062013c0324d00a9340324b00a92d8844a4211280bc4a0271298a4494291248a4492211248524522610d89c426211090a4424211088bc42229108032424201058a4404211008a4402271008d83f0108f40323d8280e88823821c8e20a0376200d8882352218cc8663301e0c405c310220c00b82f02a0bd8842e4290b88a42e2270b809c2e0210b807a2e6288ad0a22a4218a10662821609c87c262160988d8252320958842442f091084242290908b8234300888a0210170848d8202260818a41f42f07d09c1f42107c8a41f21507c0bc1f02e87c0b81f02a87c0a41f02707c07a1f4360780b81e6210750a41d22f0748ba1d22e0748aa1d22907489c1d02f07409c1d0268740981d0228740841d01e8750701c6290698841a4270690841a21286909218211061064164200558a41442f05109c14421050884142180508441422e04d884124210488bc1222704889a1222604888a1222104887a12216848844100170400441041903887c0e21903807c0e4200348800d6290310bc0c4210308840c02f0300a40c0270300840c42602c0b80b01e02c0980a41f02487c0921902588607629019884064290190840622f0188a4062270188840600c81802a0642781509c054218150840522981488605218814856052148148460502781409c056210110a60442181089e042270108860422101009c04026810098040228100840401e81005e040170118a60362180d0a40322f00c8ba0322e00c8aa0322900c87e0321f00c8640302f80c0bc0301f80c07c0301980c06403629809886024190088be0222f0088a60222900887e0221f008866022190080be0202f0080a60202900807e0201f0080660201900805a024198048860121180405e0101180403e0100980403e00 i
def q70T := dagTraceTagsBin q70M 47 (dagTagBases q70N 0x6ff42b03f3f93d0bfa79f87ec0af4f9e763f2fd267e05fa4209f56eda4d 0x7bf77b6ffff9ff7bfb3afe7fffafffceb7befbf6fff6dff12761a6edad8 47) 8 q70D
def q70St := dagTraceBin q70M q70N 8 q70D
def q70Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q70Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q70Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q70Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q70Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 4, 2, 3, 1, 0, 6, 7] 0 i.val)
def q70Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 4, 2, 3, 1, 0, 6, 7] 0 i.val)
def q70Mv := dagMoves ([([qS12], q70Mp0, q70Mi0), ([qS23], q70Mp1, q70Mi1), ([qS23, qS12], q70Mp2, q70Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70A : DagMovesOK q70M q70G 256 q70Mv := dagMovesOfCheck (by decide +kernel)
def q70NB : Nat → List Bound := dagNodeBounds q70C.toArray 0x3f01f80fc07dc7ec3f51fa0fd03e81f40fa07d03e81f31f90fc83e41f20f907c83e41f20f907c83e41f20f907c83e41f20f907c83e41f20f907c83e41f11f887c43e21f10f887c43e21f10f887c43e21f10f80fbc7de1ee1f707b83dc1ee0f68fa8fce7e61f307983ca3e41f18f887c41e11f00f803be3df0ef0f783ba3dc1ed17683b23d81eb8f587aa3d41ea07503a63d30e81f38b9c1cc2e49f2078e3c70e3871c38c3c51e287107863c30e18704b821c10df1ef477a1bc1dd8eec3761ba1dd06e47721b90dc0edc76a5b23d906c47603b00d78eb87585ab1d586a87523a63d28e907445a20d08e807401a00d0068033e39f0cf867c33e19f0cf867873c19e0cf067473659a1cd06647303962ca164c7243911c80e3c71c38d1c51e20b0e3861c30610b063821bf9df86fa37d0be85f42f837b1bd0de46ee5770bb0dd82ea3750ba0dcc6e61730b90dc46de56f0b70db46da16c1b58d8e2c075d3ad1d5ceaa5523a81534e947473a1a4f5a72932796aca5248b2138db45d22690b88494152046fe47c33d4de46e99722b811b88d936b9350d9eacc364231897d0b955aa2c515c6ab3532a8193a69a34b224551c689542a2014f6a77438b1b50cb06052cb9550a0a4c4233109078c39319b0bd052c263112079030c1440730218088004 0x4044b206016305843044508073958909134548353594d94014140243587201405a0ca0205b20522b1200b7b62155a84a60570765b2b857671860116214066a117103333b00366281534070351432034833720537143037437db949350bdd924d92370413450b48595741391a258136137d924d928357449b150385d924d28794d944d9d628170946214961923549409943718153235862340acb2157a0b210ab2a1830a40a30225831a27013ca00ca6a02b8152b6728157608528034a8702c6a06a83c0ca10ca813570a9721b685721b94162581c6a0a8346cca10ca15703a2925813b2379147236a026141b20270413b612b926146a1b20b621b621 13 4 4
def q70Ck := dagCheckNodeBin q70M q70G q70NB 294 q70St q70Mv q70L q70S q70T
def q70RA (token : Nat) : Bool :=
  let s := rootState q70N 8 token
  !dagAllowedRootBin q70M q70E s.2.1 || dagLocalBin q70M q70G (dagKnownClosesBin q70G q70C) s ||
  dagRefBin q70M 294 q70St q70Mv (fun p tok => dagFindLink (q70L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70RB0 : treeBlock 0 32 q70RA = true := by decide +kernel
theorem q70R : dagCheckRootsBin q70M q70G (dagKnownClosesBin q70G q70C) q70E (dagRefBin q70M 294 q70St q70Mv (fun p tok => dagFindLink (q70L p) tok) 0) q70N 8 = true := q70RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B0 : treeBlock 0 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B16 : treeBlock 16 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B32 : treeBlock 32 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B48 : treeBlock 48 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B64 : treeBlock 64 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B80 : treeBlock 80 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B96 : treeBlock 96 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B112 : treeBlock 112 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B128 : treeBlock 128 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B144 : treeBlock 144 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B160 : treeBlock 160 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B176 : treeBlock 176 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B192 : treeBlock 192 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B208 : treeBlock 208 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B224 : treeBlock 224 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B240 : treeBlock 240 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B256 : treeBlock 256 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B272 : treeBlock 272 16 q70Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70B288 : treeBlock 288 6 q70Ck = true := by decide +kernel
theorem q70Bk : treeBlock 0 294 q70Ck = true := (@treeBlock_merge 0 160 134 q70Ck (@treeBlock_merge 0 80 80 q70Ck (@treeBlock_merge 0 48 32 q70Ck (@treeBlock_merge 0 32 16 q70Ck (@treeBlock_merge 0 16 16 q70Ck q70B0 q70B16) q70B32) (@treeBlock_merge 48 16 16 q70Ck q70B48 q70B64)) (@treeBlock_merge 80 48 32 q70Ck (@treeBlock_merge 80 32 16 q70Ck (@treeBlock_merge 80 16 16 q70Ck q70B80 q70B96) q70B112) (@treeBlock_merge 128 16 16 q70Ck q70B128 q70B144))) (@treeBlock_merge 160 80 54 q70Ck (@treeBlock_merge 160 48 32 q70Ck (@treeBlock_merge 160 32 16 q70Ck (@treeBlock_merge 160 16 16 q70Ck q70B160 q70B176) q70B192) (@treeBlock_merge 208 16 16 q70Ck q70B208 q70B224)) (@treeBlock_merge 240 32 22 q70Ck (@treeBlock_merge 240 16 16 q70Ck q70B240 q70B256) (@treeBlock_merge 272 16 6 q70Ck q70B272 q70B288))))
theorem q70K : KnownBin q70C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q42Bin) q41Bin) q60Bin) q44Bin) q43Bin) q3Bin) q1Bin) q61Bin) q2Bin) q34Bin) q4Bin) q58Bin) q46Bin) q33Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q70Bin : BinLower q70M q70W q70G 9 := by
  apply lowerDagBin _ _ _ _ q70A _ _ _ q70K _ (fun _ b hb => dagNodeBounds_mem b hb) q70R q70Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q70C.all (fun b => q70M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q71M : Word := 0x30303030303030303030303030303030000000000000000
abbrev q71G : Word := qGoal &&& q71M
abbrev q71W : List Word := projectDAGStock q71M qBase [0, 3, 4, 5, 6]
def q71F : Bound := (q71M, q71W, 9, q71G)
def q71E := unpackWitnesses q71W [74384, 340112, 581728, 876688, 1130592]
abbrev q71N : List Word := normStock q71M q71W
def q71C : List Bound := [q63F, q18F, q65F, q66F, q5F, q64F, q7F, q36F, q6F, q67F, q38F]
def q71S : DagSample := (0x2422500a120a8500a8401a100894814480684816080a0481c0825148244825024161209824140c061301a09068482c0c07030140904940204828120925008824220805020985205040280c0a0, 34)
def q71L : DagLinkList := dagExtractLinks 0xc983260c983260c983203c7871e0c7071c0c7031a1c6831a0c683181c603180c587160c583160c583160c583141c503140c503140c503140c503140c503140c503140c487120c407100c403100c4030a3c10f021c006fe1bc1eec2bb02ea1ba06e80b90ae21b806d65b392c64b00ebe1ae0eb61ac8ab01ab86aa2a8929e2a706982a4128a3a0927c39d8e7419c0a6e19a0e5c69686543919e3878c8e3018c022c28a86281890a2408886201859610383860c1818e060808a0017ba5ec17a85e627791d647489c286e15b806b19a4466959245b4d58a52213e54e0d22b42b10243e90e893620bed2d90a49271082d19b848f0f1817300a8001 0x71644051643011642091444c91404c11844c114424114428516040116430116c4091404c31203c11202c91404c31403c11402c1140201120441120207100496cc04110e0315100294cc0211100190cc01110c4308ba05c10a0301110501084308ba05c10603010403010f0508e64502e64404c84300c84208fa45c10c4482e44300e44208e24502e24400e24300bc42030a44c10a43c10842c10842c10605c30404c10403c10202c2e0840100440100c402de4400fe05c0fc02c0ba4248f00502f00400fa0308f20500f80200f60200ba4380f40200fa8384f845c0f844c0f443c0f8c420f684e0f48424ee4506ca4400e64304cc0504f045c0ec4300e44204ea4500ea4400e24300f24500f2c5c0f044c0e88400ef0500ea840aca4500ec84e0ea8426da44e6ca4424da04e4ca0420e88400e8c400ce83c2ce04c4e68500e68400e28308c80502c80400d603c0bc0300e6c420e484e0e28420e04314d404e4c80420dc03d0e0c400de43c0d204c0dc4300dc8402b80400d80200d60200da0500d40200da4502ce4400d884e0d68422b883d0d44420d20312b844c0d005c0ce03c0d04300ce4300cd0500ca4500c84302cb0500ca8500c205c2c8c420c88420c604e0c404d0c004c0be0450bc0422b803d0b802d0c60200c44300c20210c00200be4308ba05c2b604c0b602c0bc4308ba05c2ba04c0ba02c0b84300b60540b50508800512800410a20314ac02944c0210ac01904c01188c05d0b204927e0310a002107e01187c05127c04109e03107c0210b001903a0112ae45c0ae43c0a842c09c0402ad0520ac85209a4310aa05e0a801e0984400a606c2a405c0a403c2a30520a2c520a085e09e85288445e86c45227044126a44007043106a43009c42e09a42909842204642104442029404109403109602908e021494c52094c4286885226884249245209244249005e48e05209004e08e04208c84848a46c08a45c08644c87806027805064a04008403008b052088c5e086c5287a052082020084c4348244e08243e48086008085007c84087446027445064844006c43084c06024c05005e04c03a04008105207e85e07c85247845e47445207644107244007043106a43045c05e44c05206604d07ac5e07845245a05e44a052076c5006e84004e43c24e05c27505207485207284065845e64845226442d45805e44805206404d470c52070c4246e85206e84245605e44605205604e04604206cc4346a84206a83246844306843346204f45404e45204344404206203f05403e052033044032066850064450062430238050060c5e05ec52238c4d05c45205a05e05805224e04105602105402005284023845c05006c04e03c24d05204c85204a45e04845204643104443004205e04005d03e05c03c05503a05223804d03802d23705203685203445e03245303045282405f81e05321c04102803101c02102e01f02c01902a01300a011628c4342884302883382044e81444381244222043e21443321243202042e01442301242282604322603302602302505342245e02244e81a05221a04202003001f05341c85201c84241a45e41845341645201a44e01844301644201443101243041005f40e05e40c05340a05201004f00e04e00c04300a042608c4340844300843380404f80204320403f20203300602100401f00201300001f 14 5 13 8 3
def q71D : Forest := fun i => decodeNode 8 21 0x44c8262032808178040b905057828291121448789e42c4e02e2680f13405898c404a02e2400b12107086c4242427212109098b87a44c3d8281da138e908474c40386211b2138d90846cc403521e1aa100c88a05a84e2b421159108ac06256430292181441409d0a04a842230101110c08404240020202180f90c0780583c4301d02a0ec14070092360191921e0c21485c0bc2e01e170360b00f0598a42a85e154290a90b8548522a422150148ab108508842804e140210a21204e0a424c5e1262909310c4487c230520f42f07a1483d8bc1c4520e62806a1483108018c420b42105b10c29064144330a4280491402486012c5e08629041148200bc1005208010840080210800e06c0701e03a148188bc0c452062188310c0180bc0c05d0602e030154180a40c02d06429029178148a60a4520500f828064140260a8330401182414c0c89c06030038298121080889c04443022210110c4088600404f0202701010c08084044330101080807c040260201f00 i
def q71T := dagTraceTagsBin q71M 34 (dagTagBases q71N 0x679ef877627ccec7ff501c7eb869f83fd02edbdc9c 0x37faffe777ffd6ef7ff55bdffbffff99ffa855bddb9 34) 8 q71D
def q71St := dagTraceBin q71M q71N 8 q71D
def q71Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q71Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q71Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q71Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q71Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q71Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q71Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q71Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q71Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q71Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q71Mv := dagMoves ([([qS22], q71Mp0, q71Mi0), ([qS11], q71Mp1, q71Mi1), ([qS23, qS22], q71Mp2, q71Mi2), ([qS11, qS22], q71Mp3, q71Mi3), ([qS23], q71Mp4, q71Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71A : DagMovesOK q71M q71G 256 q71Mv := dagMovesOfCheck (by decide +kernel)
def q71NB : Nat → List Bound := dagNodeBounds q71C.toArray 0xdb0db0db0db0db0d92d90d90d90d81d80d80d62d60d60d60d60d60d60d60d60d60d60d60d51d50d50d50d41d40d40d40d31d21d11d01d00d00cf1ce1ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ca4ca0c91c81c71c70c61c51c41c22c11c01bf1bf0bd2bd0ba3b82b62b51b50b41b40b40b13ae3ad1ad0ac1ac0ab1a83a80a44a22a119f29c39939819719529419319219119018f18b48a18a08918818628518418138108017f17f07f07e17957547146986546235e45955454f54b44744343e53953543142d42942632241f31a51460f5096045004 0x200010032313432505443043211001271017133201201618501125012020012a10411232343231203133443201351384523154608468312045970435430413712032701250163201321020160145292041512012503201321041230523242043531420535201935201325013205 12 4 4
def q71Ck := dagCheckNodeBin q71M q71G q71NB 141 q71St q71Mv q71L q71S q71T
def q71RA (token : Nat) : Bool :=
  let s := rootState q71N 8 token
  !dagAllowedRootBin q71M q71E s.2.1 || dagLocalBin q71M q71G (dagKnownClosesBin q71G q71C) s ||
  dagRefBin q71M 141 q71St q71Mv (fun p tok => dagFindLink (q71L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71RB0 : treeBlock 0 32 q71RA = true := by decide +kernel
theorem q71R : dagCheckRootsBin q71M q71G (dagKnownClosesBin q71G q71C) q71E (dagRefBin q71M 141 q71St q71Mv (fun p tok => dagFindLink (q71L p) tok) 0) q71N 8 = true := q71RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B0 : treeBlock 0 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B16 : treeBlock 16 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B32 : treeBlock 32 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B48 : treeBlock 48 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B64 : treeBlock 64 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B80 : treeBlock 80 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B96 : treeBlock 96 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B112 : treeBlock 112 16 q71Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71B128 : treeBlock 128 13 q71Ck = true := by decide +kernel
theorem q71Bk : treeBlock 0 141 q71Ck = true := (@treeBlock_merge 0 80 61 q71Ck (@treeBlock_merge 0 48 32 q71Ck (@treeBlock_merge 0 32 16 q71Ck (@treeBlock_merge 0 16 16 q71Ck q71B0 q71B16) q71B32) (@treeBlock_merge 48 16 16 q71Ck q71B48 q71B64)) (@treeBlock_merge 80 32 29 q71Ck (@treeBlock_merge 80 16 16 q71Ck q71B80 q71B96) (@treeBlock_merge 112 16 13 q71Ck q71B112 q71B128)))
theorem q71K : KnownBin q71C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q38Bin) q67Bin) q6Bin) q36Bin) q7Bin) q64Bin) q5Bin) q66Bin) q65Bin) q18Bin) q63Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q71Bin : BinLower q71M q71W q71G 9 := by
  apply lowerDagBin _ _ _ _ q71A _ _ _ q71K _ (fun _ b hb => dagNodeBounds_mem b hb) q71R q71Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q71C.all (fun b => q71M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q72M : Word := 0xf0f00000f0f00000f0f00000f0f
abbrev q72G : Word := qGoal &&& q72M
abbrev q72W : List Word := projectDAGStock q72M qBase [0, 1, 3, 5, 6]
def q72F : Bound := (q72M, q72W, 7, q72G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q72Bin : BinLower q72M q72W q72G 7 := dagShiftLowerBin (width := 256) [qS17] q68Bin (by decide +kernel)
def q73M : Word := 0xf000f000f000f000f000f000f000f
abbrev q73G : Word := qGoal &&& q73M
abbrev q73W : List Word := projectDAGStock q73M qBase [0, 1, 4, 5, 6]
def q73F : Bound := (q73M, q73W, 7, q73G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q73Bin : BinLower q73M q73W q73G 7 := dagShiftLowerBin (width := 256) [qS20, qS45, qS16] q68Bin (by decide +kernel)
def q74M : Word := 0x5050505050505050505050505050505
abbrev q74G : Word := qGoal &&& q74M
abbrev q74W : List Word := projectDAGStock q74M qBase [1, 3, 4, 5, 6]
def q74F : Bound := (q74M, q74W, 7, q74G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q74Bin : BinLower q74M q74W q74G 7 := dagShiftLowerBin (width := 256) [qS20, qS45, qS21, qS16, qS17] q68Bin (by decide +kernel)
def q75M : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev q75G : Word := qGoal &&& q75M
abbrev q75W : List Word := projectDAGStock q75M qBase [0, 1, 3, 4, 7]
def q75F : Bound := (q75M, q75W, 7, q75G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q75Bin : BinLower q75M q75W q75G 7 := dagShiftLowerBin (width := 256) [qS24, qS25] q68Bin (by decide +kernel)
def q76M : Word := 0x3333000000000000333300000000000033330000000000003333
abbrev q76G : Word := qGoal &&& q76M
abbrev q76W : List Word := projectDAGStock q76M qBase [0, 2, 3, 6, 7]
def q76F : Bound := (q76M, q76W, 8, q76G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q76Bin : BinLower q76M q76W q76G 8 := dagShiftLowerBin (width := 256) [qS28] q69Bin (by decide +kernel)
def q77M : Word := 0x3300000033000000330000003300000033000000330000003300000033
abbrev q77G : Word := qGoal &&& q77M
abbrev q77W : List Word := projectDAGStock q77M qBase [0, 2, 5, 6, 7]
def q77F : Bound := (q77M, q77W, 8, q77G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q77Bin : BinLower q77M q77W q77G 8 := dagShiftLowerBin (width := 256) [qS28, qS22, qS26] q69Bin (by decide +kernel)
def q78M : Word := 0x111100001111000011110000111100001111000011110000111100001111
abbrev q78G : Word := qGoal &&& q78M
abbrev q78W : List Word := projectDAGStock q78M qBase [2, 3, 5, 6, 7]
def q78F : Bound := (q78M, q78W, 8, q78G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q78Bin : BinLower q78M q78W q78G 8 := dagShiftLowerBin (width := 256) [qS27, qS5, qS16, qS17, qS18] q69Bin (by decide +kernel)
def q79M : Word := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev q79G : Word := qGoal &&& q79M
abbrev q79W : List Word := projectDAGStock q79M qBase [0, 4, 5, 6, 7]
def q79F : Bound := (q79M, q79W, 7, q79G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q79Bin : BinLower q79M q79W q79G 7 := dagShiftLowerBin (width := 256) [qS14, qS15, qS22, qS24] q68Bin (by decide +kernel)
def q80M : Word := 0xf0f0f0f00000000000000000f0f0f0f
abbrev q80G : Word := qGoal &&& q80M
abbrev q80W : List Word := projectDAGStock q80M qBase [0, 1, 3, 4, 5]
def q80F : Bound := (q80M, q80W, 8, q80G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q80Bin : BinLower q80M q80W q80G 8 := dagShiftLowerBin (width := 256) [qS3, qS17, qS24] q69Bin (by decide +kernel)
def q81M : Word := 0xf0f000000000f0f0f0f000000000f0f
abbrev q81G : Word := qGoal &&& q81M
abbrev q81W : List Word := projectDAGStock q81M qBase [0, 1, 3, 4, 6]
def q81F : Bound := (q81M, q81W, 8, q81G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q81Bin : BinLower q81M q81W q81G 8 := dagShiftLowerBin (width := 256) [qS10, qS26, qS24] q69Bin (by decide +kernel)
def q82M : Word := 0xc030c030c030c030c030c030c030c03
abbrev q82G : Word := qGoal &&& q82M
abbrev q82W : List Word := projectDAGStock q82M qBase [0, 1, 4, 5, 6]
def q82F : Bound := (q82M, q82W, 8, q82G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q82Bin : BinLower q82M q82W q82G 8 := dagShiftLowerBin (width := 256) [qS34, qS12, qS22, qS26, qS24] q69Bin (by decide +kernel)
def q83M : Word := 0x9090909090909090909090909090909
abbrev q83G : Word := qGoal &&& q83M
abbrev q83W : List Word := projectDAGStock q83M qBase [0, 3, 4, 5, 6]
def q83F : Bound := (q83M, q83W, 8, q83G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q83Bin : BinLower q83M q83W q83G 8 := dagShiftLowerBin (width := 256) [qS2, qS11, qS12, qS21, qS22, qS24] q69Bin (by decide +kernel)
def q84M : Word := 0x5050505050505050a0a0a0a0a0a0a0a
abbrev q84G : Word := qGoal &&& q84M
abbrev q84W : List Word := projectDAGStock q84M qBase [0, 1, 3, 4, 5]
def q84F : Bound := (q84M, q84W, 9, q84G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q84Bin : BinLower q84M q84W q84G 9 := dagShiftLowerBin (width := 256) [qS3, qS4, qS0, qS5, qS26, qS41] q70Bin (by decide +kernel)
def q85M : Word := 0x30303030c0c0c0c030303030c0c0c0c
abbrev q85G : Word := qGoal &&& q85M
abbrev q85W : List Word := projectDAGStock q85M qBase [0, 1, 3, 4, 6]
def q85F : Bound := (q85M, q85W, 9, q85G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q85Bin : BinLower q85M q85W q85G 9 := dagShiftLowerBin (width := 256) [qS10, qS43, qS12, qS1, qS17, qS18, qS41] q70Bin (by decide +kernel)
def q86M : Word := 0xf0f00000f0f00000f0f00000f0f00
abbrev q86G : Word := qGoal &&& q86M
abbrev q86W : List Word := projectDAGStock q86M qBase [0, 1, 3, 5, 6]
def q86F : Bound := (q86M, q86W, 9, q86G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q86Bin : BinLower q86M q86W q86G 9 := dagShiftLowerBin (width := 256) [qS9, qS17, qS41] q70Bin (by decide +kernel)
def q87M : Word := 0x5050a0a05050a0a05050a0a05050a0a
abbrev q87G : Word := qGoal &&& q87M
abbrev q87W : List Word := projectDAGStock q87M qBase [0, 1, 3, 5, 6]
def q87F : Bound := (q87M, q87W, 9, q87G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q87Bin : BinLower q87M q87W q87G 9 := dagShiftLowerBin (width := 256) [qS9, qS4, qS0, qS5, qS26, qS18, qS41] q70Bin (by decide +kernel)
def q88M : Word := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f00
abbrev q88G : Word := qGoal &&& q88M
abbrev q88W : List Word := projectDAGStock q88M qBase [0, 1, 3, 6, 7]
def q88F : Bound := (q88M, q88W, 9, q88G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q88Bin : BinLower q88M q88W q88G 9 := dagShiftLowerBin (width := 256) [qS9, qS17, qS24, qS41] q70Bin (by decide +kernel)
def q89M : Word := 0x5050a0a0000000005050a0a0000000005050a0a0000000005050a0a
abbrev q89G : Word := qGoal &&& q89M
abbrev q89W : List Word := projectDAGStock q89M qBase [0, 1, 3, 6, 7]
def q89F : Bound := (q89M, q89W, 9, q89G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q89Bin : BinLower q89M q89W q89G 9 := dagShiftLowerBin (width := 256) [qS9, qS4, qS0, qS5, qS46, qS18, qS25, qS41] q70Bin (by decide +kernel)
def q90M : Word := 0x5000a0005000a0005000a0005000a0005000a0005000a0005000a0005000a
abbrev q90G : Word := qGoal &&& q90M
abbrev q90W : List Word := projectDAGStock q90M qBase [0, 1, 5, 6, 7]
def q90F : Bound := (q90M, q90W, 9, q90G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q90Bin : BinLower q90M q90W q90G 9 := dagShiftLowerBin (width := 256) [qS9, qS4, qS0, qS45, qS22, qS46, qS18, qS41] q70Bin (by decide +kernel)
def q91M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q91G : Word := qGoal &&& q91M
abbrev q91W : List Word := projectDAGStock q91M qBase [0, 1, 3, 4, 5, 6]
def q91F : Bound := (q91M, q91W, 10, q91G)
def q91E := unpackWitnesses q91W [49760, 312416, 577632, 843872, 1101896, 1368112]
abbrev q91N : List Word := normStock q91M q91W
def q91C : List Bound := [q8F, q74F, q68F, q73F, q70F, q72F, q18F, q85F, q19F, q20F, q9F, q57F, q80F, q81F, q82F, q83F, q84F, q86F, q87F]
def q91S : DagSample := (0x50a8c068000a0603800108824324128c0623008882512416022510c1602050241a022130502c14090182c301a0182406130c0643009050682219088244021010884022180481028100a01422088c4c0700888410090190c9049240242012201080209051288249208240412201400442008846070209848221, 54)
def q91L : DagLinkList := dagExtractLinks 0xa82a0a8291a42819c65281600801f1695463d4f007801 0x408d81e0440e01e46a1f03409918c534e22fa6914c3887e1a4330c43e43418d2d0df948630b427c5210e160c69486f4943185213c250861003c07831a321bd150c60c84f05421e0c14e098a702c432442591a10f108bf864538421fc190cc848460804b0302181008c040260003f 10 4 13 5 3
def q91D : Forest := fun i => decodeNode 5 18 0x8d8e0223087e9219a50f864279509e44219007848318d09e34218c09610218404610098407e0 i
def q91T := dagTraceTagsBin q91M 54 (dagTagBases q91N 0xfbae108fd069d1c1f92dc6f65af0dd5041e7a61ffbe0ba4f73ef9b0e7dffe207ffc2c207ffffb34c9 0xfbaed39fd5e9d1fffc4ddef7daf7dd52c7eba77ffbf8bb2775effbae7fffe96fffeee077ffffb965c 54) 9 q91D
def q91St := dagTraceBin q91M q91N 9 q91D
def q91Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q91Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)
def q91Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q91Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q91Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 6, 5, 4, 7] 0 i.val)
def q91Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 6, 5, 4, 7] 0 i.val)
def q91Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q91Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 0, 1, 3, 7] 0 i.val)
def q91Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 0, 1, 3, 7] 0 i.val)
def q91Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 3, 1, 0, 7] 0 i.val)
def q91Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 6, 3, 1, 0, 7] 0 i.val)
def q91Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 0, 1, 3, 7] 0 i.val)
def q91Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q91Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def q91Mv := dagMoves ([([qS17], q91Mp0, q91Mi0), ([qS11], q91Mp1, q91Mi1), ([qS11, qS17], q91Mp2, q91Mi2), ([qS20, qS45, qS16], q91Mp3, q91Mi3), ([qS44, qS45, qS1, qS17], q91Mp4, q91Mi4), ([qS20, qS45, qS16, qS17], q91Mp5, q91Mi5), ([qS44, qS45, qS1], q91Mp6, q91Mi6)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91A : DagMovesOK q91M q91G 256 q91Mv := dagMovesOfCheck (by decide +kernel)
def q91NB : Nat → List Bound := dagNodeBounds q91C.toArray 0x3a0e83a0e4781dc743c12d3a5263891b7595153500d 0x22394042840708c021808201041011694046a0142330041198004a0d28c08f7358728823 10 4 5
def q91Ck := dagCheckNodeBin q91M q91G q91NB 17 q91St q91Mv q91L q91S q91T
def q91RA (token : Nat) : Bool :=
  let s := rootState q91N 9 token
  !dagAllowedRootBin q91M q91E s.2.1 || dagLocalBin q91M q91G (dagKnownClosesBin q91G q91C) s ||
  dagRefBin q91M 17 q91St q91Mv (fun p tok => dagFindLink (q91L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91RB0 : treeBlock 0 64 q91RA = true := by decide +kernel
theorem q91R : dagCheckRootsBin q91M q91G (dagKnownClosesBin q91G q91C) q91E (dagRefBin q91M 17 q91St q91Mv (fun p tok => dagFindLink (q91L p) tok) 0) q91N 9 = true := q91RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B0 : treeBlock 0 16 q91Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q91B16 : treeBlock 16 1 q91Ck = true := by decide +kernel
theorem q91Bk : treeBlock 0 17 q91Ck = true := (@treeBlock_merge 0 16 1 q91Ck q91B0 q91B16)
theorem q91K : KnownBin q91C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q87Bin) q86Bin) q84Bin) q83Bin) q82Bin) q81Bin) q80Bin) q57Bin) q9Bin) q20Bin) q19Bin) q85Bin) q18Bin) q72Bin) q70Bin) q73Bin) q68Bin) q74Bin) q8Bin)
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
def q92M : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev q92G : Word := qGoal &&& q92M
abbrev q92W : List Word := projectDAGStock q92M qBase [0, 1, 3, 4, 5, 7]
def q92F : Bound := (q92M, q92W, 10, q92G)
def q92E := unpackWitnesses q92W [74384, 337040, 602256, 799754, 1138832, 1400880]
abbrev q92N : List Word := normStock q92M q92W
def q92C : List Bound := [q12F, q75F, q47F, q22F, q68F, q45F, q49F, q52F, q8F, q26F, q23F, q29F]
def q92S : DagSample := (0x1029100a400280022006220c0e03028180e1209101a080683180c4142a48260148a0c2603088482c120a0182c060a00884c140b05024060b0c06806090184c30190c024141a088642209100840422100886012040a0402805088223108884100940204201201209008248048020904221008805208041208a44228100a0402214028040a0, 59)
def q92L : DagLinkList := dagExtractLinks 0x9e09e09e09e09e09e09e09e09e09e09e09b39659339309219029008f18f08e18e08e08b38838268117f27f07f07f07e17e07c27a27a07a07a07827627516f66695f75875535505054d34b241a3983633152f22691f714b07d016001 0xe086168420740183d2106e485d68422390171a0088ed8c0f4860b32181b8080e98c06c430390301cc180e10c0ec840b40301c4181d90816c4607742f3b2148dc8bc6c452b502f598148dc8616c860364201a9181d10c0684603483019a182c80d86204cb2036190130c40c8608616b420979180908445202e1a0111851c1b98a0d6850ae2381190c26484156070590180a0081b98c4d886e6b431171188888605806e2b03117c182b90c25c841a72174c90889c05c320222d22c9610c484025568612b420901088a805c28022298311411b89c0c44c07c2502e7221c1910a0c0840a423812114080881340701a0280e8130500804906223431112100848dc404629c0374c81887c09abe8501f228098140798dc3ac6213626ae1188700c42645c1b03e0d4189650c432462180370b81b4580d82a06514031098137488c2a44414c218c90184480821803109009894188450c6208410f231041088380dc1a0630c0310580b8280460802209831e421892108510462082214381be180dd0a0638403103813c1809c0a0430402101b14f088a684433820298100cc040260003f 12 4 13 6 2
def q92D : Forest := fun i => decodeNode 6 19 0x6305ec60b20c144182421844840848c0ec181a4303404c540c8a51c1283020841408b2790c4f4209a02e360c4611b8c0311807c2c0b85c188943112840248dc49188922810c6e1d8c438188703e0d062148c4281b850368a06c140ca2818850268b0620d0c61a10432310606e0c0c6181883017060230e0c61110820278404e080861010826298203304026080fc0 i
def q92T := dagTraceTagsBin q92M 59 (dagTagBases q92N 0xfd3fe108fc3de1fbcafc96e37873f08f07c1079df1fff4d55749eeede7c439e1ffe20fffc778c03fffff4c44 0x3de7fed39fcfde1fbcafe26ef7df3f79f47cb1fadfafff0d40764ee6df3efbbf9ffe97ffff7fbdcffffff66fd 59) 9 q92D
def q92St := dagTraceBin q92M q92N 9 q92D
def q92Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q92Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q92Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q92Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q92Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q92Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q92Mv := dagMoves ([([qS24], q92Mp0, q92Mi0), ([qS11], q92Mp1, q92Mi1), ([qS11, qS24], q92Mp2, q92Mi2)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92A : DagMovesOK q92M q92G 256 q92Mv := dagMovesOfCheck (by decide +kernel)
def q92NB : Nat → List Bound := dagNodeBounds q92C.toArray 0x8410821041983104608409811022044017d6fa1f0bd97a2f25e0bc0780f01dcbb8762e35c0b796e2da5ad351676cc594b28642c4988310612bb16d2ae50a99125a1e3f878cde98e2ca4d87f8c713a19c1b006 0x310382011120031256411872674250002504320b3935014a32801230a30a143200153093162402385611245617265479462539630145164206231450271645721465 11 3 4
def q92Ck := dagCheckNodeBin q92M q92G q92NB 60 q92St q92Mv q92L q92S q92T
def q92RA (token : Nat) : Bool :=
  let s := rootState q92N 9 token
  !dagAllowedRootBin q92M q92E s.2.1 || dagLocalBin q92M q92G (dagKnownClosesBin q92G q92C) s ||
  dagRefBin q92M 60 q92St q92Mv (fun p tok => dagFindLink (q92L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q92RB0 : treeBlock 0 64 q92RA = true := by decide +kernel
theorem q92R : dagCheckRootsBin q92M q92G (dagKnownClosesBin q92G q92C) q92E (dagRefBin q92M 60 q92St q92Mv (fun p tok => dagFindLink (q92L p) tok) 0) q92N 9 = true := q92RB0
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
theorem q92B48 : treeBlock 48 12 q92Ck = true := by decide +kernel
theorem q92Bk : treeBlock 0 60 q92Ck = true := (@treeBlock_merge 0 32 28 q92Ck (@treeBlock_merge 0 16 16 q92Ck q92B0 q92B16) (@treeBlock_merge 32 16 12 q92Ck q92B32 q92B48))
theorem q92K : KnownBin q92C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q29Bin) q23Bin) q26Bin) q8Bin) q52Bin) q49Bin) q45Bin) q68Bin) q22Bin) q47Bin) q75Bin) q12Bin)
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
def q93M : Word := 0x333300003333000033330000333300003333000033330000333300003333
abbrev q93G : Word := qGoal &&& q93M
abbrev q93W : List Word := projectDAGStock q93M qBase [0, 2, 3, 5, 6, 7]
def q93F : Bound := (q93M, q93W, 11, q93G)
def q93E := unpackWitnesses q93W [66176, 329856, 594048, 868480, 1147008, 1425504]
abbrev q93N : List Word := normStock q93M q93W
def q93C : List Bound := [q15F, q18F, q8F, q45F, q76F, q77F, q39F, q10F, q16F, q78F, q37F, q35F, q11F, q64F, q13F, q28F, q30F, q48F, q51F, q59F]
def q93S : DagSample := (0x4002400a8402a41029402250021400a440684028402a1402a10028201a0402900a249028042240a8402a140028041a010c824300908812094c0610022040a80623040e030300c0a0120b0182c301a090680028048a40030082c124320c0e020914180d060240a0d241300a09100840a25301900a21100a0102802914904924024184c20924820912190826120884100940204804402211008402a0402090422100880621002211028100a01221002810211080c0403008281, 82)
def q93L : DagLinkList := dagExtractLinks 0xea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea40ea01ea00ea00ea00ea00ea00ea00e943e901e900e900e8c1e8c0e881e880e841e801e800e800e7c1e781e780e741e740e740e701e6c1e6c0e681e680e641e601e5c1e581e580e502e500e500e500e4c1e4c0e442e440e440e401e3c1e381e380e341e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e340e301e243e201e200e200e200e1c1e181e180e180e141e140e140e140e140e140e140e140e140e101e100e100e100e043df83df41df01df00df00dec1dec0dec0dec0dec0dec0dec0de81de80de80de41de01ddc1ddc0ddc0ddc0dd81dd41dd40dd01dd00db47da44da40da40d944d901d8c1d881d841d840d840d7c2d703d586d502d500d4c1d4c0d346d283d280d280d280d280d184d102d082cd4dcc83cc80cc41cc01cb82cb80cb41cb40cac2ca81ca80c945c7c6c6c4c642c5c2c503c404c3c1c303c243c201c143c101c0c1c0c0c003bf04bbcdbb81bac3b985b590b541b3c6b3c0b381b380b302b300b300b282b202b1c1b1c0b1c0b142b083b041af44af40ae83ae02adc1adc0ad42ac44ab83ab02a947a805a743a701a682a680a680a641a5c2a581a541a501a443a383a380a245a144a0449f839f419e839e419e019dc19d819cc39b07994798c2978596c39489938492c39242918391419101908290028f828f418f408f018f008ec18e428dc28d428d018c828a8888888880888088418609838a818881417f877c4d7b057a43774c75097482730672c1728171456d116b8669c7694268c2684263d25dd85c0759c95846568751d34c954a88465144873f553e443bca3b033ac13613340830cd30032d8a2a4d290526c9254624051d9a1a0e15530c25084f050d00530001 0x29f0604a6918029a4400a710e029ac480a611322940600a591702968384a3918068c4404a311812924600a52130294c5d0a4a1b02908600a4b1b02910602a3b14428e8510a3c1b028cc585a211b02880600a2817028a8600a211702808385a1117128444c0a110f22814608a021b02868604a131802850608a021b068284c0a0a0f228086c1a0213028083c0a0a1902804340a020e027e06c09f017027a05c09fc18027c44009f310027a06c27a817c9a4053583010520c03108300841ea01f069004ea65461899218625846d87f81b0278460193814024e04009c80c027685c193010427446c87f81b027242409b01f066a05c09a813026603c19c4188270c6209ba188a6c85209b108426602d09a81f026805c09981f224a061192810426403906880841b801d098805624806109100841a0011098b121260470098114025e440098418825e462097117c25a453495b1b4a52c5e26e3148256c4d58020d81fe83409490e41b843188f818623806018f810463804009600a4256c4809521f223c0705803120255070890018623a06007fa0e0252c4809411b0250c5348d918522c46058291056084404830181a4b061492a18523e46d48e11b023443108a90c123246148a118023244108a1100226450093909024cc5c089114024b05c48891c062045009231a061e44048601f02460641871141220470088114160644009131b921e46209080d4240c7009041f023ec5c48c11c023c87008ea18023cc6d08eb1b023884c08dd1c023305048ba1c260a47008d41b823306208c21b822e86226b217899e85208921381ac83e067a0c961646e582918921606e4828188230c4058bd1c122f07008bc14022d0603884148228c401882106608460288c14c22ac5e08a3148a26c43088a14c226833584917960845237d913c22443f17d90bd21205e48201489f604f08900fc1f602f088c140221062087a1b961046e581918821c425086813421a450286b14821a8310858184212060086117021007007d1170216c700850170a11461084a18021046108381f0a0ec52083a0c49f205e07c80b820d060082918420846008191c020407c08001f060b470082c1c0a074611824180208c60081a184a05061081118420006d27e81781fa02e280c14c202453080017c9a804f267010c1a801f067004e1fe06c27e01785fc04c07f00f01f802e87f81b05fe04c07f80f01fc06407e81f01f807407d91401aec4807d01701f705007d11701f207c47c11f01f045c07b11301f106207bb1b81ecc6207ad1c21d847c17611711c644c07190f21b847007a11905d644c07590f21d447c17511701d444c06f10f01e687c17921701e484c07810f05e245c07891301e043c07780901da45c17211701dcc7c076b1401c8c4817221711d8c7007631401d4c40871a1c05c6850073a1301bc84007641891ccc6e471b1881d2c4d075a1b81d486216c01041d2c5016ea1401d0c6e073b1885bac4d07321885ae04116eb1701ca87c07221305c7062071b1881c486e070a1b41c086c06fa1941bc86216ea1341ba83d06e31211b647c06d91701b244c06dc1881b4c6e06cb1881b085c06b11401b0c5006bb1201aa05c06b41401aa45c06a01f01a602406951c019a06c868a1c019805c06581b019406c068b1201a0c6e86281b819e85006481b019f05006401b018e06c06711f018c06c166c18819ac6206621b8196862164810419203106500a418c021464b188192c42464118819044246381b918c062063813818c04206291b818906084e81848bc05f223014c53a04143a80c40ea02102f007c08c013a59418616446185481b418605922e813c88a04314e00c413802102e807c08a01384d81848b805f222014c53604104d80c40d602102e007c088013061117053405104d010417203102180840b201d060806418001525ea1b88b286215fa17457c85c05fa13417c84c05a20f417883c05e90a40b242114c814413204105a00c48b045f221114c0b042f021108c17801e05da18097485005d1080972c6205ca0c416843d05c01f416e07c25981b856c05d15a817016c04d05a813016803d05980b8164c4884c01c453005153a010412a031020008409a01d056806415801555821b916046e058b1b816046284b818c15e03904a008407e01105711b815b063056418d15646245511801564420551100152c4845421f514887c25021b889a862054217414885c053213414484c05010a409a42184901c611c070149014451c05053981054e404005451c814f07e05341c814a87e03420f21220720524188146c6e051318913c06e849818e120062034008414286e847818814106304f917053cc6e04f11b913ac7024ab18813ac5004db10012a83184691c6112470146914451245004791314e244153811020ea07023081b84ea05004001300d604003080b993146304ec188138c6e04db188934c5344c218c13483344911bd11c46e446918d112462225917c87c453046110411044004c90fc09642f01f108d0fe06e43a81888cc05f042813413203f03300bc13107204ba1f910e47214311410fc07e43a01c812c02504ac18d12886e04a213910c462043110910806f43c018c10804f03c010c12707e04931c911647213391410f807e43981c8122c6f04831b811ec62133b13411c86243d81b90e4062146d1c811b072046414011687e04521c889286e21ea1884ce85c033a13009283e01ea0c94f447e53891c850644d03b11310f407e43881c810605d13b017090f463144c188d0d052044b18890cc52044310010e863143210410c83153c91b94e0462332117c4ce44d14110f44c842f43c81b90e0062232017c10404d03380f40c802f242318810ac5004220c410645104111408c606e13501400c602e23f518c102c6e04031888fac5313531340fe86203f118c0fa43303e01bc0f606e03d018c0f2062224017c87805313b010409001f01e004c8f106203c31048c446e13511700c443e03b81f00ec04c23a518c4eb06203ab1880e886303991bc0e446e038918c0e0462223917c87645302390bc07642303781b80dc06d03681b00d806503581888d205f13501340d403d03480bd0d0c6e03431390ce46203391090cd07203341490ca87e032a1790c847203211490c607e43101c80c605e03101480c306343011b80c044e02f81b04bd47202f41c80bac7e02e31ca0a647e82691c84ae45d12911700ae44d02911300b643e02a90f409c43c02d10d40b2432125814409604102c00e408e03142bc1c80af05242b31f90aac7202b31780aac5242a11f80a845e029c18d0a4c6202931090a286f42821b909e86342721880a284f028213809e843027210a094063125010c09b06342611b809844e425c1c809705242521f809485e42491c809245242401f908e072024017808e05212351c808d072022b1f8088c7282021c808683211f114407c44102110e407643181c01f807406c02080f808106341fa1b807e84e81b01b846c04e41f41c807d05241ea1c807a85241e11f907647201e117807645201c81b1474c5341d214c07483381c814c47203301c808c07106341ba1b806e84e41b118806c442a16518c46b06201ab18806886e019a18886485e218a14c852852816118c064429018908c05242181301be040063208017c81605310f810403e03101800bc04602d01780a405c025016808c02a021008007c016013016418d056862015a10905446e414918805444e014910a03c06310f010c03a031005008401a01d014006404e015013418d04a86f41221b9046862211217881a852012a13c04884e011a10802883d01110a401a42141081ba03806380d818804204e10e010c43604200a00c583d463010418c83d05340fb18883ac5200fb10903c86300f210c03a83140e11bd03646e40d118d032462206117c81245300e113c03644e00d110c03244200a10f401842f004908d03006f40b81b902c06340a818882605f209017882205300c013c02e04e00b010c02a04200a00f402602f00900b8022023508418d020c63008310e01e46f80711ba01a462107913c41c44e106910801e43f00710f801a432806018c41804300600cd417063405b18c016c43805218841484200520ca012463104910c01243380381b801005c103813800e03ea02c14d40cc53302b10d00c853202a10c00c833802914c40a433002908e00805f801814c80404f200810c40803f10180cc00802f001808c00401f000804c00003f 16 6 13 9 4
def q93D : Forest := fun i => decodeNode 9 22 0x8304e4871326244c48992e41c4a58bb1d6364660c1188364498b11043042c8b9094303c20c0e4432379070da830339880c903631c8c0c142e3008d8be2122e98c4b84312e0842b803e2dc0b8b703e2d4072b36242b60c4ac2312b08beab229aac052aa6242a60e0a66242858a6a021226d8b89a82e2658d0980322618dc9501aa560f89362e24d8da8f63623d0988fa3823a0dc8d8312358808c82822e0c08a62f2258a489419a2407e898282220c48743721c84a87418a0c8b87f6381ec0b87b4301e88c27a4189e20c0768381c98c0714309c48c2702299b80be6e01e1b00c86b03e1a80e86a8281948b86403e18e0c4616371858c461a3817c8c85e43e1710985c2261688785a0121658f8566281560c45343714d0c4536281498dc516311450c45143e1410985063113d0dc4f43693d0d84f43293d0c44f41e93d8904e8311358dc4d6311358a04b62412e0a04a22e1240f8480121228e0476241058dc408280f88f83c6310ed0dc3b4310ec0523b6210e88843a0270e80843a2370de0c03602c8d48b83300c8c802a324268c5098312148c403c304300bc8402f4188b80fa2e03e0b809a2e0260b807a2e0170b98902d6370ac8c42b01c8ac8dc2a8318a60c6282210a08802862409e8e42683f09a0e42643f09a0c4256370958c4254370920c62322e08c8dc228310818dc206310810662001f8820e41f43f07c04a1f83187909c1e83f0758e41d6378718dc1c6310710c41c83906e0a01b43f06d0e41b6310698801a4318690621a628065062192288648a0196370618c4184310608c6182198600de180370600c6180310618821703e05c098176310590c6162378588dc162318588c4160370580da160360580ca1603105807a1601785989c152210560a41442f0508a41402f0500a41483184c89c1303604a0e41163f0458e41121f04486a11219044072118290418bc106290408bc1083183d8840f42783d09c0f42183d0840f83183889c0e8290350bc0d2290340bc0d0290360e40c63f0318e40c4190308720c01f0320c60b42702e0a40a4290288bc0a229029066090118260c6084270208840863101d0dc0743101c8520721181c05e0701481c04a0701181e0c60642101889c062210180320600a81a0c60542781509c05421014852050270160c6046210110860441881089e042270108860422101009e040270100860402101007a0401781005c040118118860321f80c87c0321900c06603621809064022198080b80201f0090660121180405e0101180403e0100980407e00 i
def q93T := dagTraceTagsBin q93M 82 (dagTagBases q93N 0x41395f3ffec22c4873bbbfffe7ddcef2676de3dd704c062c70f60f20ef8ffe200b9ca80efc0fc7fe3ffef7f1b9cc1ddc93bffc65c746303c0fffffd1108 0xffbd9ffffedaadc9f3bbbfffe7ddcef8ab6df5dd7effe70f7af65fa3efd7fffbeffca16efd5fdfff5ffff6fcbcce1dde49bffe9453ffffffffffffdbbbd 82) 10 q93D
def q93St := dagTraceBin q93M q93N 10 q93D
def q93Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q93Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q93Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q93Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 3, 4, 5, 2, 7] 0 i.val)
def q93Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q93Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 6, 5, 4, 3, 2, 7] 0 i.val)
def q93Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q93Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q93Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q93Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q93Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 0, 4, 5, 2, 7] 0 i.val)
def q93Mp6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 0, 4, 3, 2, 7] 0 i.val)
def q93Mi6 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 5, 4, 0, 2, 7] 0 i.val)
def q93Mp7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q93Mi7 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q93Mp8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q93Mi8 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q93Mp9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 6, 5, 4, 0, 2, 7] 0 i.val)
def q93Mi9 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 0, 4, 3, 2, 7] 0 i.val)
def q93Mp10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)
def q93Mi10 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)
def q93Mv := dagMoves ([([qS22], q93Mp0, q93Mi0), ([qS15], q93Mp1, q93Mi1), ([qS15, qS22], q93Mp2, q93Mi2), ([qS11], q93Mp3, q93Mi3), ([qS23, qS22], q93Mp4, q93Mi4), ([qS11, qS15], q93Mp5, q93Mi5), ([qS23, qS15, qS22], q93Mp6, q93Mi6), ([qS11, qS22], q93Mp7, q93Mi7), ([qS23], q93Mp8, q93Mi8), ([qS11, qS15, qS22], q93Mp9, q93Mi9), ([qS23, qS15], q93Mp10, q93Mi10)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93A : DagMovesOK q93M q93G 256 q93Mv := dagMovesOfCheck (by decide +kernel)
def q93NB : Nat → List Bound := dagNodeBounds q93C.toArray 0xe3078c0e3038c0e3038c0e3038c0e3038c0e3038c0e3038b1e2c38b0e24b881e203871e187851e107831e087820e047801e003800df8b7d1df077c0dec77a1de47772ddc3752dccb721dc83711dc07700dc036d3db076a2d9cf661d947641d88b602d78b5d1d617553d48f511d3cb4e1d3474c1d2c74a1d20b471d10f440d0c7412d0073e2cf473c1cf033c0cf033b1cec33b0ce4b381ce03371cdc3361cccf330cc87311cc072f1cb872d1cacb2a1ca83291ca07271c987251c943241c8c7230c887202c803200c7c71f0c7871e0c7831c2c6c7192c607180c603153c507131c3d30e1c30b0c0c3030c0c2c70a1c283091c243054c016fe2be1af26bc46ed4ba8ee55b8cae12b716da2b592d51b4cad12b38ecc2b1d6c43b08ac02af4eb85acd6b03abc6ac3aa4ea72a8d29e5a5de916a3ca8a5a192842a08a7e49ece7749d867429c126e29a1a65398165d3968e564950a4f5930e47590d23f48e963378c4a2d48aca274890e204865e11883520a3820a053808dfe47e91f557c8dee47b09e937a05e5378c9e037699d647455ce37255c727149c327049bf26f0dba26e09b626ccdaf46b49aa36a09a6268cda306885a2067919b3660d96264cd8e5630986661097f55ed17745d0d7135bc96d25b05693591561357155a255cd52554094c45211453508d3d54e513454c892f34ad126548551e345dd1254391086405cfb63dd0f343b94ea43918dd73650d273390c863110bd72d9caf72a94a6427dc98724988b720e07b81ce07031a9866418545a715544f612d04560f603850c982d50a50245075c16704180a60118004 0x30e72008f000008821080002014ef380405080050901000020080232cca404c04040c38001004210854002cc0198003000201c420098039000001a71004049522001a31004511c4260cf238c2710dcc61dc519008088060814409c067b082380082040408d01100c200806200232006620004010041840351847000273982f284f128ce0789253a447018405980602d42029060816830440520c1009425946708925208403010608101018ec0002060406184a309c02284eb518405080a5990608040520c1028c040c81028c202d46029013010418546004001942600c27100464182a4a901100cb2a901008c95180e098235a80b50169501693012a0806321901018c00b8cb5980b02cc05a02618083018a0190c301901008c600462308c511423384664b0a1014800982e6004010080111a0115a02b5c0610a70344719445694491912569480194e20148011ca211ca711cae70d8b180221844c20ce008d443145209c2760c22184e21844e08dc50888e61045504461296112465020611010308803081ac204e302081181011812520c409b4c220c05304e30106009420390670052509e22924a72a0c408c052004552024100a40092328482290022a08130c0820c25300a6610030a4e5184a4008c4404a200d0101444518a3201030944432506204650254820460324a809883008864948018525204671182d708a400da92904d124a41a4a41398401c4e0944020da9194817306408925204492904929060684e9290680a4a320a6d494836892520d252086d49483 14 4 5
def q93Ck := dagCheckNodeBin q93M q93G q93NB 336 q93St q93Mv q93L q93S q93T
def q93RA (token : Nat) : Bool :=
  let s := rootState q93N 10 token
  !dagAllowedRootBin q93M q93E s.2.1 || dagLocalBin q93M q93G (dagKnownClosesBin q93G q93C) s ||
  dagRefBin q93M 336 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93RB0 : treeBlock 0 64 q93RA = true := by decide +kernel
theorem q93R : dagCheckRootsBin q93M q93G (dagKnownClosesBin q93G q93C) q93E (dagRefBin q93M 336 q93St q93Mv (fun p tok => dagFindLink (q93L p) tok) 0) q93N 10 = true := q93RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B0 : treeBlock 0 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B16 : treeBlock 16 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B32 : treeBlock 32 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B48 : treeBlock 48 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B64 : treeBlock 64 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B80 : treeBlock 80 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B96 : treeBlock 96 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B112 : treeBlock 112 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B128 : treeBlock 128 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B144 : treeBlock 144 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B160 : treeBlock 160 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B176 : treeBlock 176 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B192 : treeBlock 192 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B208 : treeBlock 208 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B224 : treeBlock 224 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B240 : treeBlock 240 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B256 : treeBlock 256 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B272 : treeBlock 272 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B288 : treeBlock 288 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B304 : treeBlock 304 16 q93Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q93B320 : treeBlock 320 16 q93Ck = true := by decide +kernel
theorem q93Bk : treeBlock 0 336 q93Ck = true := (@treeBlock_merge 0 176 160 q93Ck (@treeBlock_merge 0 96 80 q93Ck (@treeBlock_merge 0 48 48 q93Ck (@treeBlock_merge 0 32 16 q93Ck (@treeBlock_merge 0 16 16 q93Ck q93B0 q93B16) q93B32) (@treeBlock_merge 48 32 16 q93Ck (@treeBlock_merge 48 16 16 q93Ck q93B48 q93B64) q93B80)) (@treeBlock_merge 96 48 32 q93Ck (@treeBlock_merge 96 32 16 q93Ck (@treeBlock_merge 96 16 16 q93Ck q93B96 q93B112) q93B128) (@treeBlock_merge 144 16 16 q93Ck q93B144 q93B160))) (@treeBlock_merge 176 80 80 q93Ck (@treeBlock_merge 176 48 32 q93Ck (@treeBlock_merge 176 32 16 q93Ck (@treeBlock_merge 176 16 16 q93Ck q93B176 q93B192) q93B208) (@treeBlock_merge 224 16 16 q93Ck q93B224 q93B240)) (@treeBlock_merge 256 48 32 q93Ck (@treeBlock_merge 256 32 16 q93Ck (@treeBlock_merge 256 16 16 q93Ck q93B256 q93B272) q93B288) (@treeBlock_merge 304 16 16 q93Ck q93B304 q93B320))))
theorem q93K : KnownBin q93C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q59Bin) q51Bin) q48Bin) q30Bin) q28Bin) q13Bin) q64Bin) q11Bin) q35Bin) q37Bin) q78Bin) q16Bin) q10Bin) q39Bin) q77Bin) q76Bin) q45Bin) q8Bin) q18Bin) q15Bin)
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
def q94M : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev q94G : Word := qGoal &&& q94M
abbrev q94W : List Word := projectDAGStock q94M qBase [0, 1, 4, 5, 6, 7]
def q94F : Bound := (q94M, q94W, 10, q94G)
def q94E := unpackWitnesses q94W [74384, 337040, 581728, 876688, 1155216, 1425504]
abbrev q94N : List Word := normStock q94M q94W
def q94C : List Bound := [q9F, q21F, q19F, q65F, q62F, q50F, q12F, q11F, q49F, q73F, q79F, q26F, q53F, q22F, q56F, q90F]
def q94S : DagSample := (0x3020820a02090c023118088603220908c02230188062320944225148301209101a09209201a0d20b0182c060a03030120d020b04c0e00884c22120184c6031018480422100886012088c4c07008884064330184c021201088050181c0826120884402140204201201209008248048041208a4422810088500a01028002810110880c0403012050, 60)
def q94L : DagLinkList := dagExtractLinks 0xbe0be0be0be0be0be0bc1ba1b81b80b80b80b61b60b60b60b60b60b03ac2a82a80a80a80a80a61a41a02a009e19649419028a38248017e17e07e07c162d5e24c94634413862c6263032001 0x6045060c4060c505e44cd0c60504405a02cd7870cec605c43e5a4325845044430590505643f4a07c54c40c885c524604807c4607c54c525045252851508314e43d4d0594ac434844346433444404483222033b5469ad4619ac52a0852c245ec04533c053340492c041200311a02142019400133f053a6853ab4609e8513c8332a4401e432ba03fb803e3a02f3802e37059b1051348333203e310592f0512c8332a442184222803f270532485322843208311e4521c06c1a832184401603e8b05989053870518ec43928538284394833144538444312433104230e0530c0430a039080330603104023020130003f 12 5 13 6 1
def q94D : Forest := fun i => decodeNode 6 19 0x314292264a43e74864ec141621facc52450a2820c5021ea10593d8867910cf2199e832340324804c9829908331c05e380b8782c8c8331807c2c16448288883310884200fc4829868530d0861a0c432290606c0d06411100201f04453048660908c10298204304072080cc10188202304026080fc0 i
def q94T := dagTraceTagsBin q94M 60 (dagTagBases q94N 0xcf8b7d4f4387c6f503c7f10edf83f7ebca9b063e7b1fea23f8ee9130ff1fdd47f0ffa43fff03ff000fffff4c89 0xcd8d7d174f9fc6fffbd7fd3effdbf7b3e28b2e5f7b4fe727fc6ecb36ffdf5c5ff4ffb09fffbfff2bbfffff67bc 60) 9 q94D
def q94St := dagTraceBin q94M q94N 9 q94D
def q94Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q94Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 7, 2, 3, 0, 6, 5, 1] 0 i.val)
def q94Mv := dagMoves ([([qS20, qS47, qS18], q94Mp0, q94Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94A : DagMovesOK q94M q94G 256 q94Mv := dagMovesOfCheck (by decide +kernel)
def q94NB : Nat → List Bound := dagNodeBounds q94C.toArray 0xa50a50a32a30a129f29d29b29839719619609519509238d58948728257f37a57827627427227026e26a46826536055e25685154d44944634153f23b43292e42682061c41660d9076007 0x2021425643b422053011703bd3200fb4123301273017007101021104201106173564016b5621480431a2a58017303211703d26c916bc4358126a2609423a1079425702501945210ea4321580981263feca958 12 4 4
def q94Ck := dagCheckNodeBin q94M q94G q94NB 49 q94St q94Mv q94L q94S q94T
def q94RA (token : Nat) : Bool :=
  let s := rootState q94N 9 token
  !dagAllowedRootBin q94M q94E s.2.1 || dagLocalBin q94M q94G (dagKnownClosesBin q94G q94C) s ||
  dagRefBin q94M 49 q94St q94Mv (fun p tok => dagFindLink (q94L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94RB0 : treeBlock 0 64 q94RA = true := by decide +kernel
theorem q94R : dagCheckRootsBin q94M q94G (dagKnownClosesBin q94G q94C) q94E (dagRefBin q94M 49 q94St q94Mv (fun p tok => dagFindLink (q94L p) tok) 0) q94N 9 = true := q94RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B0 : treeBlock 0 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B16 : treeBlock 16 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B32 : treeBlock 32 16 q94Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94B48 : treeBlock 48 1 q94Ck = true := by decide +kernel
theorem q94Bk : treeBlock 0 49 q94Ck = true := (@treeBlock_merge 0 32 17 q94Ck (@treeBlock_merge 0 16 16 q94Ck q94B0 q94B16) (@treeBlock_merge 32 16 1 q94Ck q94B32 q94B48))
theorem q94K : KnownBin q94C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q90Bin) q56Bin) q22Bin) q53Bin) q26Bin) q79Bin) q73Bin) q49Bin) q11Bin) q12Bin) q50Bin) q62Bin) q65Bin) q19Bin) q21Bin) q9Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q94Bin : BinLower q94M q94W q94G 10 := by
  apply lowerDagBin _ _ _ _ q94A _ _ _ q94K _ (fun _ b hb => dagNodeBounds_mem b hb) q94R q94Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q94C.all (fun b => q94M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q95M : Word := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev q95G : Word := qGoal &&& q95M
abbrev q95W : List Word := projectDAGStock q95M qBase [1, 2, 4, 5, 6, 7]
def q95F : Bound := (q95M, q95W, 9, q95G)
def q95E := unpackWitnesses q95W [74896, 338064, 581728, 876688, 1155216, 1425504]
abbrev q95N : List Word := normStock q95M q95W
def q95C : List Bound := [q9F, q12F, q15F, q24F, q32F, q31F, q39F, q40F, q54F, q55F, q56F]
def q95S : DagSample := (0xc022302806050480480c460321860a048340c0e00a058281203059209403048402203098c0640308920b0301c0c0502010820502014028441219048440804900822011100840104828940a21004221028100a01221004820110880c0403012050, 43)
def q95L : DagLinkList := dagExtractLinks 0x4508a11062043186100e003d3782e11b8b52682d01a0304600a9939a163c66ccc917220e1e40b001 0x360401b6202cb141e48a0324301a4280ca0c1dc0a035050196210c01385c0842c03d182103bc1405d0602c8301582929b149cc8a4224309243019a0c2c88c0264408f030060172ca8c0288603241809c148490a4228301002f0781483809a19050302100800c23e8c05e8300f2201720c0388801b05e0c82935c149250a61683167229039089a80a61402309a311421889d06010462072200301b8140c40805d0302e414149048a644421610298100c4040260003f 11 4 13 5 3
def q95D : Forest := fun i => decodeNode 5 18 0x620620a1362148841141841060f829310c09829210a4841820060722018880582f120a444188c0463a31088c42220080dc2031080ba202e0806210098407e0 i
def q95T := dagTraceTagsBin q95M 43 (dagTagBases q95N 0x18e22ef9b73f9d33f8c9dfce83c4ee7fc7af81f7f8ff59fd806ff85c3beffa909 0x3cfaafffb73f9c55f8f9dfcc97dd6f3fc3afacf3fd7cfdfd8beffdf77beffafbc 43) 8 q95D
def q95St := dagTraceBin q95M q95N 8 q95D
def q95Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q95Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 5, 4, 7, 6] 0 i.val)
def q95Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q95Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q95Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q95Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 4, 2, 1, 7] 0 i.val)
def q95Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q95Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 2, 5, 6, 1] 0 i.val)
def q95Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 6, 5, 3, 2, 4, 7, 1] 0 i.val)
def q95Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 7, 4, 3, 5, 2, 1, 6] 0 i.val)
def q95Mv := dagMoves ([([qS26, qS25], q95Mp0, q95Mi0), ([qS47, qS21, qS26, qS25], q95Mp1, q95Mi1), ([qS14, qS42], q95Mp2, q95Mi2), ([qS47, qS21], q95Mp3, q95Mi3), ([qS14, qS42, qS26, qS25], q95Mp4, q95Mi4)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95A : DagMovesOK q95M q95G 256 q95Mv := dagMovesOfCheck (by decide +kernel)
def q95NB : Nat → List Bound := dagNodeBounds q95C.toArray 0x80402010080402010080401f2f878bc1e0f07134992c155a850879351306606 0x1104151301074600103210210a98210 9 3 4
def q95Ck := dagCheckNodeBin q95M q95G q95NB 28 q95St q95Mv q95L q95S q95T
def q95RA (token : Nat) : Bool :=
  let s := rootState q95N 8 token
  !dagAllowedRootBin q95M q95E s.2.1 || dagLocalBin q95M q95G (dagKnownClosesBin q95G q95C) s ||
  dagRefBin q95M 28 q95St q95Mv (fun p tok => dagFindLink (q95L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95RB0 : treeBlock 0 64 q95RA = true := by decide +kernel
theorem q95R : dagCheckRootsBin q95M q95G (dagKnownClosesBin q95G q95C) q95E (dagRefBin q95M 28 q95St q95Mv (fun p tok => dagFindLink (q95L p) tok) 0) q95N 8 = true := q95RB0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B0 : treeBlock 0 16 q95Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95B16 : treeBlock 16 12 q95Ck = true := by decide +kernel
theorem q95Bk : treeBlock 0 28 q95Ck = true := (@treeBlock_merge 0 16 12 q95Ck q95B0 q95B16)
theorem q95K : KnownBin q95C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q56Bin) q55Bin) q54Bin) q40Bin) q39Bin) q31Bin) q32Bin) q24Bin) q15Bin) q12Bin) q9Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q95Bin : BinLower q95M q95W q95G 9 := by
  apply lowerDagBin _ _ _ _ q95A _ _ _ q95K _ (fun _ b hb => dagNodeBounds_mem b hb) q95R q95Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q95C.all (fun b => q95M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q96M : Word := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev q96G : Word := qGoal &&& q96M
abbrev q96W : List Word := projectDAGStock q96M qBase [1, 3, 4, 5, 6, 7]
def q96F : Bound := (q96M, q96W, 10, q96G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q96Bin : BinLower q96M q96W q96G 10 := dagShiftLowerBin (width := 256) [qS11, qS6] q94Bin (by decide +kernel)
def q97M : Word := 0xf0f00f0f00000000f0f00f0f00000000f0f00f0f00000000f0f00f0f
abbrev q97G : Word := qGoal &&& q97M
abbrev q97W : List Word := projectDAGStock q97M qBase [0, 1, 2, 3, 6, 7]
def q97F : Bound := (q97M, q97W, 11, q97G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q97Bin : BinLower q97M q97W q97G 11 := dagShiftLowerBin (width := 256) [qS9, qS0, qS12, qS21, qS1, qS26, qS18] q93Bin (by decide +kernel)
def q98M : Word := 0xf0f0f0f0f0f0f0ff0f0f0f0f0f0f0f0
abbrev q98G : Word := qGoal &&& q98M
abbrev q98W : List Word := projectDAGStock q98M qBase [0, 1, 2, 3, 4, 5]
def q98F : Bound := (q98M, q98W, 10, q98G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q98Bin : BinLower q98M q98W q98G 10 := dagShiftLowerBin (width := 256) [qS3, qS35, qS15, qS17] q91Bin (by decide +kernel)
def q99M : Word := 0xf0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0
abbrev q99G : Word := qGoal &&& q99M
abbrev q99W : List Word := projectDAGStock q99M qBase [0, 1, 2, 3, 4, 5]
def q99F : Bound := (q99M, q99W, 10, q99G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q99Bin : BinLower q99M q99W q99G 10 := dagShiftLowerBin (width := 256) [qS13, qS35, qS15, qS18, qS25] q92Bin (by decide +kernel)
def q100M : Word := 0x333300003333333300003333000000003333000033333333000033330000
abbrev q100G : Word := qGoal &&& q100M
abbrev q100W : List Word := projectDAGStock q100M qBase [0, 2, 3, 4, 5, 7]
def q100F : Bound := (q100M, q100W, 11, q100G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q100Bin : BinLower q100M q100W q100G 11 := dagShiftLowerBin (width := 256) [qS3, qS19, qS17] q93Bin (by decide +kernel)
def q101M : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q101G : Word := qGoal &&& q101M
abbrev q101W : List Word := projectDAGStock q101M qBase [0, 1, 3, 4, 5, 6, 7]
def q101F : Bound := (q101M, q101W, 12, q101G)
def q101E := unpackWitnesses q101W [74384, 337040, 602256, 843872, 1138832, 1417360, 1687648]
abbrev q101N : List Word := normStock q101M q101W
def q101C : List Bound := [q45F, q47F, q85F, q88F, q91F, q92F, q94F, q96F]
def q101S : DagSample := (0x884c140b05024060b0c06806090184c30190c024141a088642209100840422100886012040a04028050882231301c022210190c9049240248042051288249208248050181c0826120884100940204201201209008248048020904221008805208041208a4422810088500a01028002810110880c0403012050, 54)
def q101L : DagLinkList := dagExtractLinks 0x9 0x7f 2 1 7 1 1
def q101D : Forest := fun i => decodeNode 1 8 0xfe i
def q101T := dagTraceTagsBin q101M 54 (dagTagBases q101N 0x211fa1987bc6f25b8dd9fe1cfde083cf91ef8fff749ee7f9ede7fbffc40ff1fff1ffffff488ffffc3ffffffff4c489 0x1a73fa799fbc6f89bbdddff7cfde58fd797efd7ff764eebfdedf3fbffd2dff7fffdffffff6227fffefffffffff66fbc 54) 11 q101D
def q101St := dagTraceBin q101M q101N 11 q101D
def q101Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q101Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q101Mv := dagMoves ([([qS11], q101Mp0, q101Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101A : DagMovesOK q101M q101G 256 q101Mv := dagMovesOfCheck (by decide +kernel)
def q101NB : Nat → List Bound := dagNodeBounds q101C.toArray 0x8 0x54bfa0 8 4 3
def q101Ck := dagCheckNodeBin q101M q101G q101NB 1 q101St q101Mv q101L q101S q101T
def q101RA (token : Nat) : Bool :=
  let s := rootState q101N 11 token
  !dagAllowedRootBin q101M q101E s.2.1 || dagLocalBin q101M q101G (dagKnownClosesBin q101G q101C) s ||
  dagRefBin q101M 1 q101St q101Mv (fun p tok => dagFindLink (q101L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101RB0 : treeBlock 0 64 q101RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101RB64 : treeBlock 64 64 q101RA = true := by decide +kernel
theorem q101R : dagCheckRootsBin q101M q101G (dagKnownClosesBin q101G q101C) q101E (dagRefBin q101M 1 q101St q101Mv (fun p tok => dagFindLink (q101L p) tok) 0) q101N 11 = true := (@treeBlock_merge 0 64 64 q101RA q101RB0 q101RB64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101B0 : treeBlock 0 1 q101Ck = true := by decide +kernel
theorem q101Bk : treeBlock 0 1 q101Ck = true := q101B0
theorem q101K : KnownBin q101C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q96Bin) q94Bin) q92Bin) q91Bin) q88Bin) q85Bin) q47Bin) q45Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q101Bin : BinLower q101M q101W q101G 12 := by
  apply lowerDagBin _ _ _ _ q101A _ _ _ q101K _ (fun _ b hb => dagNodeBounds_mem b hb) q101R q101Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q101C.all (fun b => q101M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
def q102M : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev q102G : Word := qGoal &&& q102M
abbrev q102W : List Word := projectDAGStock q102M qBase [0, 1, 2, 3, 4, 5, 6, 7]
def q102E := unpackWitnesses q102W [74384, 337040, 600208, 864400, 1106016, 1400976, 1679504, 1949792]
abbrev q102N : List Word := normStock q102M q102W
def q102C : List Bound := [q93F, q9F, q20F, q94F, q54F, q47F, q70F, q92F, q19F, q91F, q97F, q95F, q71F, q18F, q75F, q84F, q96F, q73F, q49F, q68F, q98F, q39F, q72F, q80F, q74F, q99F, q88F, q89F, q90F, q100F, q101F]
def q102S : DagSample := (0x30982a35201a04029000a00088240a090c024220c02830084225101888062348244068201a0c0a85120946031301841c1e008649058008c40a45031180c860a250482c180e0142a060b03038301a0184c0c1609068181c1209805228188c0c26028840c22120b01229060b01828120d020b0490c83038022130502c140920914180d0602428160a048060b0c068060902834904c0282406130c064300903059209403048141a08864220910084042210088601202894c064028841028100a01422088c4c07008884064324124900920108144a2092482090814080500a1104864209848221040250081080480482402092012201100884402100a8100824108840220148201048229108a0402211028100a01221002810110880c0403012050, 128)
def q102L : DagLinkList := dagExtractLinks 0xe183860e183860e183860e183860e107840e103840e103840e103840e103840e103840e103840e103840e103840e103802df877c1df037c0df037a1de07780de036e5db836e0db836e0db836e0db836e0db836e0db836e0db836e0da0f623d8075c2d60b4c6d18f441d103421d0073c2ce0b361cd07340cd03321cc83320cc832e2ca8b281c987241c903240c78f1c1c60b123c293043bd9eee4ba8ae43b902e21b806e00b802de1b782dc1b686d62b48ace2b28aca0b282ca0b18ac22b006be1af06bc0ae86b43ab8eaa2a98aa41a712944a4868c3a112840a102840a1028409d9e687971a506940250094024c29286462908a3e28ba22a2898a24188861c3839dfc97b9de457521cc47301c066e11b426c85a66671598265859415fad6c9579d4aa50153464b111a946811a042a0fc73c18e843810da3350cce32ea89cf249476e17344c80ac418900ac001 0x1784225e11417607c5e4201794805db201774805b814568041d400c55002150804d66440d390c1500405d12034c4405b8201644305c9201624405c1241604405cb14570833da90fb4e4325a80f94e0325d420172c80d31101718905780c15c0305bc2015a4405611016c04c5b10c56a0805ad20169080501089694804f90893c4224e908938430d992015a450d4020164440d8920162450d812416046056114166c8058b14160831d382016748058b1435a4805931f962c725791f95a472d501fb4c07251808d61482571239584825581755e8405710875ac8056b1415883155918156831550201548805482715283151008950c80539201514805312014f4805332034a08c5201734a08c5281714808451a18147060511271430905011413607c50e2413e4504d01f13c4404c81b13a4504c01f138440d0320540c514eb105388325052093f0824f32393ac824e41cf368814da145308414dd20934c824ca239308824bb203100813e8144e60413600c4b002125804d2f480c382050e051390106ae0312b808494013c992052c079430104e203135808492013c282050a051380104d4031288084900134a82712806c49b1b32083e4810f9248794790892288e48120b08091420184f8051378104d20312380851601945004d1e88ec692391d08e4692091849e45d20d15893c482791206e4432050ac514220cd064803410c8f403e2c00c91189043c1810ac60c11240ce440ab10c2fa0902b8100a203043c2090cc8e42b20904482331100fe08e3e820909892409248ca4403f0278f809241d20304c8141314502833bb90faac4323b80f8ac0324021e4fe8413f108cc8022beb204fac513e20ccc64323d80f8a20323d5208f288e3c10a4ee0823b0270ea06c3a10fae6c8139b144e0c4137a0cc8c4223680fce7482394208e2c8e3832088a42237d20c88430373124db483b63240d8c60353140d2831b41240d0460319142b00902c0180bc05c288140d948235b238d4c82b39208cc450ae823aae0823101749e02334d20eca48232914ac208fad020cc205f2d014cd148233b208ccc5032a0c4c848e31920ab608eab0208c005d27008cc4c6030a0c4c04602801809a0222fc238bd082284174ba8822e112cb60822d3104a046c2610c8b209c2c5208aec822b1208aa08e2a0234a608c290214a20822801769f09227c18a9c89227218a9a49ea612489a46e26118a96c9125b18490c5123a0c88c4402181f07c03e25e2489509224b27890c922291408407c23d20c884409f82387e05e2341ce8ac7322b10c8883221c1ce8487321210c8308e2021247e4221f520e7a88e1ea17a788811e21447284118108e54081150144460410f80c43402307804c794821db2087488e1ca20a684831c10a46e42394820c500510f0104320311b00a46a0230980841c0131a320c6688217a0c86448e1890f86148397a2085e85297123a5a4831711785a45393820c4e0530e8104300310680845801915804c5548214b20c50c5113a0cc4c4820b90c84a08e12020c460821100f8420330980c84002e0fc1ce3cc730f310c3a83306108a3807f0e013c3603f0d520e32c820cb148308318b92082e4528b023e2a08e8a020e260820b017c2a05e0a014c260520900bc2202e08008c1f48387320c1cc5306a0c8184408502381606c0501781203e0441ce0e87303a10e0c47303110c0a4238201cc080430180c40402300804c000ff 14 5 13 8 1
def q102D : Forest := fun i => decodeNode 8 21 0x1480a0a404dc2020d90107890828403f10c5f2900f148073a403431f99d8e4cf48266420329085958a0c883164418b0a20171062b548058a402bb2015c0b8a408451830279271371209748246841233239199048d07345a4121b2090d11c8688243a401e01e4ec1386c06c366361aa1e4cd11c6448232447184238bc9045e49e2ea4196e24cb00dc598902a84114b238a59045389228a4013b1449d0664e8792642093108c998a2488332401f1252088d11c4642923041118270880d84443e21a410fc2087d91c3ec821fa418f312476906394821a6470d32086a90633482186410c3140610623048e182410c31805d0622e460178470b4208591042c44b160410b3104541382b482146410a12085011c2808d140460a0214501042805d1483108a188448dc2246211c4907c2483d93c1ec920fa418741cc358861a8320d83986210c3211c168490b21105d20c290bc15482086410422382110410429082118400a42004610c83074410392381c87c0f48306429031178188a60c01906009835208159060ac51054198292081411c0a083050410280f8140660a02e0583982310c110660804f0401f82520c0d8a4068310322901817c0c0bc06053030290180bc0c05c0602303a4181314c0906404440020360101780807c050730142180910c04846020430101880808c04026020ff00 i
def q102T := dagTraceTagsBin q102M 128 (dagTagBases q102N 0xafc9053fffffd81a43c75d0cf0fe78ef7ff27bceff7ff9e1ed38fbb3ff0fe7f73fff9b836fadff2f3cff3fffcff1ffdfc13ff8f80217ec98138fe7c8fdff1fffbfede875b4dabbe5e41efcff3f6ff3fe0593c77819f877fffff1007fe3fffe3fdeeff69fc1ff877fbfffbe9107f7fff0fa7c3fe7fe0007fffefffffffe988909 0xbfe23d3fffffdb7a4fcf5d3cf3fe78ef7ff27bceff7ffcfaed3bfbbbffbfe7f73fff9b836fadff875d7f5fffcffaffdffc7ffafe2317ec9db3bfebcbfdffafffbfedeff5b4c23be5f2cefd7f5f6ff9feef9fc7f9ddfc77fffff4b6ffefffff5fdc1ff6ffdbffc77fbfffbec4b3f7fffbfffdfffffefbbffffefffffffecddfbc 128) 13 q102D
def q102St := dagTraceBin q102M q102N 13 q102D
def q102Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q102Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q102Mv := dagMoves ([([qS11], q102Mp0, q102Mi0)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102A : DagMovesOK q102M q102G 256 q102Mv := dagMovesOfCheck (by decide +kernel)
def q102NB : Nat → List Bound := dagNodeBounds q102C.toArray 0x3ae4eacfa92e98fa15e7cb9c3e68b964e50b913e38f8b3e24b863e10b813df8f7c2de4f763dccf712dbcb6d2da17653d8535d4d653554d48f4c6d24f463d0933f3ce97355cc8f302cb13293c98f233c80f1d3c68f173c4970c6c24f063c10b004bf4ef85bc5eed4b9dae34b80edc4b64ed45b44ece3b2cec74b10ec13af8eba4ad92b24ab92aa4a992a42a8129e2a692973a45a8e3a2928289ede7839d4e7239b926b399d262597ce5b495d2507934e4a391ce4348fd23b48d5a3238bce2d289da207871217584d20f482d20748095fc67d21eb97869d89754dd237391c95718dc156f15b666c19ac469d5a25675597664d18f462958195e617455c1169758d95b855594c9503136a4c192a648291a645190e641a0fca3ce4ed6399cde83564cba30e0bd62d24ac8286c9c5252086e1eec6fc19685e715dc516129c4370ee03560aac219066010901e4007 0x24c286400802d00572680200940100620284017802d00402080201200170020684017002400480080200803470aa1a54326002c594326142c4144c2886b608a158032004081040208ce1011281002200401004a240044009a0448024004d0202d40c2e00b239d562089a4004014bc01300255b401484c702d0810028149a00a8400a80128102200242880110024004400d0ad120011002d004056856028620284022a0022846b288a2184a20052f004c008dd301042005020048830ce9004ce00d0d1280120024005ae004c00c10008cad006000d0b50c1000c06e21c013802400480091000a040090400a92238022004400803470c550d1d368aa1a4aa1a40550ad800c9800b0081302010cac5886e331655990a1b0457c0ca1b5c560dcc3a5a19816b4a0ca1cc0140047008a10086198047008e1800833840478ce9010663a404a00c493880130a049224008207c8851180b790c0910c014963638c901c8f1b4ae200c43080e911cd79a03481d985c6e6c4c71240b0a2222002689102524015448672408195a27e226389205a1e750171c456010711610293ac02520e4045712004179027046c3301454ad763014940ca27b8cd540692f16ab08bbd406ab1543618a400548310e34802f81ae3724076a1463c403110c71802a440c93806180e27208015a86c8a5043805d3dc01798a438417a406e99c0a424ad1307331c0d524ac5acc01cda9520a263e061b9255358f819436160a1a4e063d841026f3406a04cca19d205acca3a48018d47580cf719901a40a395eb899474806f819430152f332033a80979a0a1a4e067a0a19d20 14 4 5
def q102Ck := dagCheckNodeBin q102M q102G q102NB 189 q102St q102Mv q102L q102S q102T
def q102RA (token : Nat) : Bool :=
  let s := rootState q102N 13 token
  !dagAllowedRootBin q102M q102E s.2.1 || dagLocalBin q102M q102G (dagKnownClosesBin q102G q102C) s ||
  dagRefBin q102M 189 q102St q102Mv (fun p tok => dagFindLink (q102L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102RB0 : treeBlock 0 64 q102RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102RB64 : treeBlock 64 64 q102RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102RB128 : treeBlock 128 64 q102RA = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102RB192 : treeBlock 192 64 q102RA = true := by decide +kernel
theorem q102R : dagCheckRootsBin q102M q102G (dagKnownClosesBin q102G q102C) q102E (dagRefBin q102M 189 q102St q102Mv (fun p tok => dagFindLink (q102L p) tok) 0) q102N 13 = true := (@treeBlock_merge 0 128 128 q102RA (@treeBlock_merge 0 64 64 q102RA q102RB0 q102RB64) (@treeBlock_merge 128 64 64 q102RA q102RB128 q102RB192))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B0 : treeBlock 0 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B16 : treeBlock 16 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B32 : treeBlock 32 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B48 : treeBlock 48 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B64 : treeBlock 64 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B80 : treeBlock 80 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B96 : treeBlock 96 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B112 : treeBlock 112 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B128 : treeBlock 128 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B144 : treeBlock 144 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B160 : treeBlock 160 16 q102Ck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102B176 : treeBlock 176 13 q102Ck = true := by decide +kernel
theorem q102Bk : treeBlock 0 189 q102Ck = true := (@treeBlock_merge 0 96 93 q102Ck (@treeBlock_merge 0 48 48 q102Ck (@treeBlock_merge 0 32 16 q102Ck (@treeBlock_merge 0 16 16 q102Ck q102B0 q102B16) q102B32) (@treeBlock_merge 48 32 16 q102Ck (@treeBlock_merge 48 16 16 q102Ck q102B48 q102B64) q102B80)) (@treeBlock_merge 96 48 45 q102Ck (@treeBlock_merge 96 32 16 q102Ck (@treeBlock_merge 96 16 16 q102Ck q102B96 q102B112) q102B128) (@treeBlock_merge 144 32 13 q102Ck (@treeBlock_merge 144 16 16 q102Ck q102B144 q102B160) q102B176)))
theorem q102K : KnownBin q102C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) q101Bin) q100Bin) q90Bin) q89Bin) q88Bin) q99Bin) q74Bin) q80Bin) q72Bin) q39Bin) q98Bin) q68Bin) q49Bin) q73Bin) q96Bin) q84Bin) q75Bin) q18Bin) q71Bin) q95Bin) q97Bin) q91Bin) q19Bin) q92Bin) q70Bin) q47Bin) q54Bin) q94Bin) q20Bin) q9Bin) q93Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q102Bin : BinLower q102M q102W q102G 14 := by
  apply lowerDagBin _ _ _ _ q102A _ _ _ q102K _ (fun _ b hb => dagNodeBounds_mem b hb) q102R q102Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : q102C.all (fun b => q102M &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
theorem binLowerEq {m m2 : Word} {s s2 : List Word} {t t2 : Word} {k : Nat}
    (hm : m = m2) (hs : s = s2) (ht : t = t2) (h : BinLower m s t k) : BinLower m2 s2 t2 k := by
  subst hm; subst hs; subst ht; exact h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootLower : BinLower (fullMask 256) qBase qGoal 14 :=
  binLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) q102Bin

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
