import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_35260

open PEqualNP.CircuitLowerBounds

abbrev Word := Nat
abbrev Row := Fin 256

def fullMask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def bit (r : Row) (w : Word) : Bool := w.testBit r.val

def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (Nat.add m 1)) n

@[simp] theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
@[simp] theorem nat_land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
@[simp] theorem nat_lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
@[simp] theorem nat_xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
@[simp] theorem nat_shl_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
@[simp] theorem nat_shr_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nat_beq_eq (a b : Nat) : Nat.beq a b = (a == b) := rfl
theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]
theorem nat_blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]

theorem testBit_one_shl (j k : Nat) : (Nat.shiftLeft 1 j).testBit k = decide (k = j) := by
  rw [nat_shl_eq, Nat.testBit_shiftLeft]
  by_cases hge : k ≥ j
  · by_cases heq : k = j
    · subst heq; simp
    · have hne : k - j ≠ 0 := by omega
      have h0 : (1 : Nat).testBit (k - j) = false := by
        cases h : (1 : Nat).testBit (k - j)
        · rfl
        · rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; omega
      simp [hge, heq, h0]
  · have hne : k ≠ j := by omega
    simp [hge, hne]

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := by
  cases n with
  | zero => rfl
  | succ m => rfl

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => match check i with | false => false | true => next (Nat.add i 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (match check start with | false => false | true => treeBlock (Nat.add start 1) count check) = true at h
    cases hc : check start with
    | false => simp [hc] at h
    | true =>
      rw [hc] at h
      by_cases eq : i = start
      · simpa [eq] using hc
      · exact ih (by simpa using h) (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (match check start with | false => false | true => treeBlock (Nat.add start 1) (left + right) check) = true
    change (match check start with | false => false | true => treeBlock (Nat.add start 1) left check) = true at a
    cases hc : check start with
    | false => simp [hc] at a
    | true =>
      have ha' : treeBlock (start + 1) left check = true := by simp only [hc, nat_add_eq] at a; exact a
      exact ih ha' (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)

inductive BTree (α : Type) where
  | empty : BTree α
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α

def btreeGet {α : Type} (defv : α) : Nat → BTree α → Nat → α
  | _, .empty, _ => defv
  | _, .leaf v, _ => v
  | 0, .node _ _, _ => defv
  | d + 1, .node l r, i =>
    match Nat.mod i 2 with
    | 0 => btreeGet defv d l (Nat.div i 2)
    | _ => btreeGet defv d r (Nat.div i 2)

def btreeAll {α : Type} (p : α → Bool) : BTree α → Bool
  | .empty => true
  | .leaf v => p v
  | .node l r => match btreeAll p l with | false => false | true => btreeAll p r

theorem btreeGet_prop {α : Type} {p : α → Bool} {defv : α} (hd : p defv = true)
    {t : BTree α} (ht : btreeAll p t = true) (d i : Nat) :
    p (btreeGet defv d t i) = true := by
  induction d generalizing t i with
  | zero =>
    cases t with
    | empty => exact hd
    | leaf v => exact ht
    | node _ _ => exact hd
  | succ d ih =>
    cases t with
    | empty => exact hd
    | leaf v => exact ht
    | node l r =>
      change (match btreeAll p l with | false => false | true => btreeAll p r) = true at ht
      cases hl : btreeAll p l with
      | false => simp [hl] at ht
      | true =>
        rw [hl] at ht
        simp only [btreeGet]
        split
        · exact ih hl _
        · exact ih ht _

def Masked (mask w : Word) : Prop := Nat.land w mask = w

def Proper (mask w : Word) : Prop := Masked mask w ∧ w ≠ 0 ∧ w ≠ mask

def binOp (mask d a b : Word) : Word :=
  match d with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.land a (Nat.xor mask b)
  | _ => Nat.land (Nat.xor mask a) b

def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d

theorem mask_testBit_ge {mask : Word} (hm : Masked fullMask mask) {k : Nat} (hk : 256 ≤ k) :
    mask.testBit k = false := by
  have h1 : (Nat.land mask fullMask).testBit k = mask.testBit k := congrArg (fun x => x.testBit k) hm
  rw [nat_land_eq, Nat.testBit_and] at h1
  have h2 : fullMask.testBit k = false := by
    have hlt : fullMask < 2 ^ 256 := by decide
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hk))
  rw [h2, Bool.and_false] at h1
  exact h1.symm

theorem masked_testBit_false {mask w : Word} (hm : Masked mask w) {k : Nat}
    (hk : mask.testBit k = false) : w.testBit k = false := by
  have h1 : (Nat.land w mask).testBit k = w.testBit k := congrArg (fun x => x.testBit k) hm
  rw [nat_land_eq, Nat.testBit_and, hk, Bool.and_false] at h1
  exact h1.symm

theorem masked_ext {mask a b : Word} (hm : Masked fullMask mask)
    (ha : Masked mask a) (hb : Masked mask b)
    (heq : ∀ r : Row, bit r a = bit r b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 256
  · exact heq ⟨k, hk⟩
  · have hm0 : mask.testBit k = false := mask_testBit_ge hm (by omega)
    rw [masked_testBit_false ha hm0, masked_testBit_false hb hm0]

theorem masked_land_left {mask a b : Word} (ha : Masked mask a) : Masked mask (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  simp only [nat_land_eq, Nat.testBit_and] at h1 ⊢
  cases hm : mask.testBit k <;> cases hb : b.testBit k <;> simp_all

theorem masked_land_right {mask a b : Word} (hb : Masked mask b) : Masked mask (Nat.land a b) := by
  rw [nat_land_eq, Nat.and_comm]
  exact masked_land_left hb

theorem masked_lor {mask a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (Nat.lor a b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  have h2 : (Nat.land b mask).testBit k = b.testBit k := congrArg (fun x => x.testBit k) hb
  simp only [nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or] at h1 h2 ⊢
  cases hm : mask.testBit k <;> simp_all

theorem masked_xor {mask a : Word} (ha : Masked mask a) : Masked mask (Nat.xor mask a) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha
  simp only [nat_land_eq, Nat.testBit_and, Nat.testBit_xor] at h1 ⊢
  cases hm : mask.testBit k <;> simp_all

theorem masked_self (mask : Word) : Masked mask mask := by
  apply Nat.eq_of_testBit_eq; intro k; simp [nat_land_eq, Nat.testBit_and]

theorem masked_zero (mask : Word) : Masked mask 0 := by
  apply Nat.eq_of_testBit_eq; intro k; simp [nat_land_eq, Nat.testBit_and]

theorem masked_binOp {mask d a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (binOp mask d a b) := by
  unfold binOp
  split
  · exact masked_land_left ha
  · exact masked_lor ha hb
  · exact masked_land_left ha
  · exact masked_land_right hb

theorem binOp_flip {mask a b : Word} {d : Nat} (hd : d < 4) :
    binOp mask d a b = binOp mask (flipOp d) b a := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · simp [binOp, flipOp, Nat.and_comm]
  · simp [binOp, flipOp, Nat.or_comm]
  · simp [binOp, flipOp, Nat.and_comm]
  · simp [binOp, flipOp, Nat.and_comm]

theorem flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> decide

theorem binOp_testBit {mask a b : Word} {d : Nat} (hd : d < 4) (ha : Masked mask a) (hb : Masked mask b) (k : Nat) :
    (binOp mask d a b).testBit k =
      if mask.testBit k then
        match d with
        | 0 => a.testBit k && b.testBit k
        | 1 => a.testBit k || b.testBit k
        | 2 => a.testBit k && !b.testBit k
        | _ => !a.testBit k && b.testBit k
      else false := by
  cases hm : mask.testBit k with
  | false =>
    rw [masked_testBit_false (masked_binOp ha hb) hm]
    simp
  | true =>
    have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [binOp, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, Nat.testBit_xor, hm]

def nrm (mask a : Word) : Word := if a.testBit 0 then Nat.xor mask a else a

theorem masked_nrm {mask a : Word} (ha : Masked mask a) : Masked mask (nrm mask a) := by
  unfold nrm
  split
  · exact masked_xor ha
  · exact ha

theorem nrm_zero_bit {mask a : Word} (hm0 : mask.testBit 0 = true) :
    (nrm mask a).testBit 0 = false := by
  unfold nrm
  cases h : a.testBit 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_self]

theorem nrm_id {mask a : Word} (h : a.testBit 0 = false) : nrm mask a = a := by
  simp [nrm, h]

theorem xor_xor_self {mask a : Word} (ha : Masked mask a) : Nat.xor mask (Nat.xor mask a) = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [nat_xor_eq, Nat.testBit_xor]

theorem nrm_xor {mask a : Word} (hm0 : mask.testBit 0 = true) (ha : Masked mask a) :
    nrm mask (Nat.xor mask a) = nrm mask a := by
  unfold nrm
  cases h : a.testBit 0
  · simp only [nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_false, Bool.false_eq_true, ite_true, ite_false]
    exact xor_xor_self ha
  · simp only [nat_xor_eq, Nat.testBit_xor, hm0, h, Bool.xor_self, Bool.false_eq_true, ite_true, ite_false]

theorem proper_xor {mask a : Word} (ha : Masked mask a) (h : Proper mask (Nat.xor mask a)) :
    Proper mask a := by
  refine ⟨ha, ?_, ?_⟩
  · rintro rfl
    apply h.2.2
    apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_xor]
  · rintro rfl
    apply h.2.1
    apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_xor]

theorem proper_nrm {mask a : Word} (ha : Masked mask a) (h : Proper mask (nrm mask a)) :
    Proper mask a := by
  unfold nrm at h
  split at h
  · exact proper_xor ha h
  · exact h

def primeW (d : Bool) (a b : Word) : Word := if d then Nat.lor a b else Nat.land a b

theorem masked_primeW {mask : Word} (d : Bool) {a b : Word} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (primeW d a b) := by
  cases d
  · exact masked_land_left ha
  · exact masked_lor ha hb

theorem nrm_primeW {mask : Word} (hm0 : mask.testBit 0 = true) (d : Bool) {a b : Word}
    (ha : Masked mask a) (hb : Masked mask b) :
    ∃ e : Nat, e < 4 ∧ nrm mask (primeW d a b) = binOp mask e (nrm mask a) (nrm mask b) := by
  let e : Nat := if d then (if a.testBit 0 then (if b.testBit 0 then 0 else 2) else (if b.testBit 0 then 3 else 1))
    else (if a.testBit 0 then (if b.testBit 0 then 1 else 3) else (if b.testBit 0 then 2 else 0))
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e]; split_ifs <;> omega
  · apply Nat.eq_of_testBit_eq
    intro k
    cases hm : mask.testBit k with
    | false =>
      have h1 := masked_testBit_false (masked_nrm (masked_primeW d ha hb)) hm
      have h2 := masked_testBit_false (masked_binOp (d := e) (masked_nrm ha) (masked_nrm hb)) hm
      rw [h1, h2]
    | true =>
      dsimp only [e]
      cases d <;> cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0 <;>
        simp only [nrm, primeW, binOp, nat_land_eq, nat_lor_eq, nat_xor_eq,
          Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha0, hb0, hm0, hm,
          Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false,
          Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
          Bool.false_eq_true, ite_true, ite_false] <;>
        cases hx : a.testBit k <;> cases hy : b.testBit k <;> rfl

def Live (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {target} ∧ Proper mask target
  | k + 1, S => ∃ (U : Finset Word) (a b : Word) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ Proper mask a ∧ Proper mask b ∧ a ≠ b ∧
      binOp mask d a b ∉ insert a (insert b U) ∧ Live mask target k (insert (binOp mask d a b) U)

theorem Live.stop {mask target : Word} (hp : Proper mask target) : Live mask target 0 {target} := ⟨rfl, hp⟩

theorem Live.binary {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {d : Nat}
    (hd : d < 4) (ha : Proper mask a) (hb : Proper mask b) (hab : a ≠ b)
    (hfresh : binOp mask d a b ∉ insert a (insert b U))
    (tail : Live mask target k (insert (binOp mask d a b) U)) :
    Live mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem Live.ind {mask target : Word} {motive : ∀ (k : Nat) (S : Finset Word), Live mask target k S → Prop}
    (stop : ∀ (hp : Proper mask target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Word} {a b : Word} {d : Nat} (hd : d < 4)
      (ha : Proper mask a) (hb : Proper mask b) (hab : a ≠ b)
      (hfresh : binOp mask d a b ∉ insert a (insert b U))
      (tail : Live mask target k (insert (binOp mask d a b) U)),
      motive k (insert (binOp mask d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Word} (h : Live mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

theorem live_proper {mask target k S} (h : Live mask target k S) : ∀ a ∈ S, Proper mask a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem live_size {mask target k S} (h : Live mask target k S) : S.card ≤ k + 1 := by
  induction h using Live.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : binOp mask d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def represented (mask : Word) (w : List Word) (v : Word) : Prop := v ∈ w ∨ ¬Proper mask v
def Repr (mask : Word) (w : List Word) (v : Word) : Prop := represented mask w (nrm mask v)

def witnessBin (mask : Word) (w : List Word) (z : Word) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ Proper mask a ∧ Proper mask b ∧ a ≠ b ∧ z = binOp mask d a b

theorem bin_laws {mask a : Word} (ha : Masked mask a) :
    binOp mask 0 a mask = a ∧ binOp mask 1 a 0 = a ∧
    binOp mask 0 a 0 = 0 ∧ binOp mask 1 a mask = mask ∧
    binOp mask 0 a a = a ∧ binOp mask 1 a a = a ∧
    binOp mask 2 a a = 0 ∧ binOp mask 3 a a = 0 ∧
    binOp mask 2 a 0 = a ∧ binOp mask 3 0 a = a ∧
    binOp mask 2 0 a = 0 ∧ binOp mask 3 a 0 = 0 ∧
    binOp mask 0 0 a = 0 ∧ binOp mask 1 0 a = a ∧
    binOp mask 0 mask a = a ∧ binOp mask 1 mask a = mask := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    (apply Nat.eq_of_testBit_eq; intro k;
     have h1 : (Nat.land a mask).testBit k = a.testBit k := congrArg (fun x => x.testBit k) ha;
     simp only [binOp, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit] at h1 ⊢;
     cases hm : mask.testBit k <;> cases hx : a.testBit k <;> simp_all)

theorem bin_rep {mask w a b} (d : Nat) (hd : d < 4)
    (ma : Masked mask a) (mb : Masked mask b)
    (ha : represented mask w a) (hb : represented mask w b)
    (no : a ≠ mask ∧ b ≠ mask) :
    represented mask w (binOp mask d a b) ∨ witnessBin mask w (binOp mask d a b) := by
  have rz : represented mask w 0 := Or.inr (fun h => h.2.1 rfl)
  have ro : represented mask w mask := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws ma
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws mb
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  by_cases he : a = b
  · subst b; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  by_cases az : a = 0
  · subst a; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  by_cases bz : b = 0
  · subst b; left
    rcases h4 with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  have pa : Proper mask a := ⟨ma, az, no.1⟩
  have pb : Proper mask b := ⟨mb, bz, no.2⟩
  exact Or.inr ⟨d, a, b, hd, ha.resolve_right (fun x => x pa), hb.resolve_right (fun x => x pb), pa, pb, he, rfl⟩

theorem norm_ne_mask {mask a : Word} (hm0 : mask.testBit 0 = true) : nrm mask a ≠ mask := by
  intro h
  have := nrm_zero_bit (a := a) hm0
  rw [h, hm0] at this
  exact Bool.noConfusion this

theorem primeW_rep {mask w a b} (hm0 : mask.testBit 0 = true) (d : Bool)
    (ma : Masked mask a) (mb : Masked mask b)
    (ha : Repr mask w a) (hb : Repr mask w b) :
    Repr mask w (primeW d a b) ∨ witnessBin mask w (nrm mask (primeW d a b)) := by
  obtain ⟨e, he, eq⟩ := nrm_primeW hm0 d ma mb
  unfold Repr
  rw [eq]
  exact bin_rep e he (masked_nrm ma) (masked_nrm mb) ha hb ⟨norm_ne_mask hm0, norm_ne_mask hm0⟩

theorem repr_const {mask : Word} {w : List Word} {v : Word} (mv : Masked mask v) (h : v = 0 ∨ v = mask) : Repr mask w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm mv hp
  rcases h with rfl | rfl
  · exact this.2.1 rfl
  · exact this.2.2 rfl

theorem pull_gate {mask target : Word} {w : List Word} {z : Word} {k S c}
    (h : Live mask target k S)
    (hz : represented mask w z ∨ (c = 1 ∧ witnessBin mask w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ Live mask target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases List.mem_append.mp (sub a ha) with hu | hu
      · exact hu
      · rw [List.mem_singleton.mp hu]; exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binOp mask d a b)
        have ht : Live mask target k (insert (binOp mask d a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm'
        have hf : binOp mask d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary hd pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

abbrev WireFn (R : Type) := R → Bool

def obs (w : Word) : WireFn Row := fun r => bit r w

def inv {R} (a : WireFn R) : WireFn R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : WireFn R) : WireFn R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : WireFn R) : WireFn R :=
  if d = 0 then combine false a b
  else if d = 1 then combine true a b
  else if d = 2 then combine false a (inv b)
  else combine false (inv a) b

def Constant {R} (a : WireFn R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : WireFn R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (WireFn R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (WireFn R)) (v : WireFn R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool

def supply {R} (pool xs : List (WireFn R)) : Prop := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (WireFn R)) : Nat → List (WireFn R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (WireFn R)) (a b : WireFn R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank

theorem Reach.start {R} {roots : List (WireFn R)} : Reach roots 0 roots := rfl

theorem Reach.two {R} {roots : List (WireFn R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩

theorem Reach.ind {R} {roots : List (WireFn R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih =>
    obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs

def Run {R} (goal : WireFn R) : Nat → List (WireFn R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : WireFn R) (rest : List (WireFn R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R} {goal : WireFn R} : Run goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R} {goal : WireFn R} {s : Nat} {xs zs : List (WireFn R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h
    exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩

theorem Run.two {R} {goal : WireFn R} {s : Nat} {a b : WireFn R} {rest : List (WireFn R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) : Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩

theorem Run.ind {R} {goal : WireFn R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : op < 4) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : WireFn R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_kept {R} (a : WireFn R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]
theorem inv_constant {R} {a : WireFn R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
theorem inv_inv' {R} (a : WireFn R) : inv (inv a) = a := by funext r; simp [inv]
theorem cost_inv {R} (a : WireFn R) : cost (inv a) = cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (this.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (this.mp x))]
theorem avail_inv {R} {bank : List (WireFn R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : WireFn R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩
theorem from_constant {R} (op) {a b : WireFn R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R} {bank v} (w : WireFn R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))

theorem extend_two {R} (roots : List (WireFn R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem comb_prime {R} {bank : List (WireFn R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩

theorem extend_comb {R} (roots : List (WireFn R)) {p bank a b} (d) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : WireFn R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (WireFn R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : WireFn R) : WireFn S := fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : WireFn R) (ws) :
    (kept k a ws).map (restrictRows rows) = kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : WireFn R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (WireFn S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev SubRow (mask : Word) := { r : Row // bit r mask = true }

def obsM (mask : Word) (w : Word) : WireFn (SubRow mask) := fun r => bit r.1 w

theorem obsM_binOp {mask a b : Word} {d : Nat} (hd : d < 4) (ha : Masked mask a) (hb : Masked mask b) :
    obsM mask (binOp mask d a b) = comb d (obsM mask a) (obsM mask b) := by
  funext r
  have h := binOp_testBit hd ha hb r.1.val
  have hm : mask.testBit r.1.val = true := r.2
  simp only [obsM, bit, comb, combine, inv] at h ⊢
  rw [hm] at h
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> simpa using h

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]

theorem kept_fin (k : Bool) (a : Word) (l : List Word) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {mask T : Word} {k S} (h : Live mask T k S) (v : List Word)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (obsM mask T) k (v.map (obsM mask)) := by
  classical
  induction h using Live.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : binOp mask d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (binOp mask d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((binOp mask d a b :: kept ka a (kept kb b rest)).map (obsM mask)) at progress
    rw [List.map_cons, map_kept, map_kept, obsM_binOp hd ha.1 hb.1] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

def tableM (mask : Word) (f : WireFn (SubRow mask)) : Word :=
  (List.finRange 256).foldl (fun acc r =>
    if h : bit r mask = true then if f ⟨r, h⟩ then Nat.lor acc (Nat.shiftLeft 1 r.val) else acc else acc) 0

theorem foldl_testBit_set (l : List Row) (acc : Word) (p : Row → Bool) (r : Row)
    (hn : l.Nodup) :
    (l.foldl (fun a x => if p x then Nat.lor a (Nat.shiftLeft 1 x.val) else a) acc).testBit r.val =
      (acc.testBit r.val || (decide (r ∈ l) && p r)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.nodup_cons] at hn ⊢
    rw [ih _ hn.2]
    by_cases hxr : r = x
    · subst hxr
      have hnot : r ∉ xs := hn.1
      simp only [List.mem_cons, true_or, decide_true, hnot, decide_false, Bool.false_and, Bool.or_false, Bool.true_and]
      cases hp : p r
      · simp
      · simp [nat_lor_eq, Nat.testBit_or, Nat.testBit_shiftLeft]
    · simp only [List.mem_cons, hxr, false_or]
      cases hp : p x
      · rfl
      · have hne : r.val ≠ x.val := fun e => hxr (Fin.ext e)
        have htb : (Nat.shiftLeft 1 x.val).testBit r.val = false := by rw [testBit_one_shl]; simp [hne]
        simp only [ite_true, nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]

theorem tableM_masked {mask : Word} (hm : Masked fullMask mask) (f : WireFn (SubRow mask)) :
    Masked mask (tableM mask f) := by
  have hstep : ∀ (l : List Row) (acc : Word), Masked mask acc →
      Masked mask (l.foldl (fun a x => if h : bit x mask = true then if f ⟨x, h⟩ then Nat.lor a (Nat.shiftLeft 1 x.val) else a else a) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc hacc
      apply ih
      dsimp only
      split_ifs with hx hf
      · apply masked_lor hacc
        apply Nat.eq_of_testBit_eq
        intro k
        rw [nat_land_eq, Nat.testBit_and]
        by_cases hkx : k = x.val
        · subst hkx; have : mask.testBit x.val = true := hx; simp [this]
        · have htb : (Nat.shiftLeft 1 x.val).testBit k = false := by rw [testBit_one_shl]; simp [hkx]
          rw [htb]; simp
      · exact hacc
      · exact hacc
  exact hstep _ 0 (masked_zero mask)

theorem tableM_bit {mask : Word} (f : WireFn (SubRow mask)) (r : SubRow mask) :
    bit r.1 (tableM mask f) = f r := by
  let p : Row → Bool := fun x => if h : bit x mask = true then f ⟨x, h⟩ else false
  have heq : tableM mask f = (List.finRange 256).foldl (fun a x => if p x then Nat.lor a (Nat.shiftLeft 1 x.val) else a) 0 := by
    unfold tableM
    congr 1; funext a x; simp only [p]
    by_cases h : bit x mask = true
    · simp [h]
    · simp [h]
  rw [bit, heq, foldl_testBit_set _ _ _ r.1 (List.nodup_finRange 256)]
  simp [p, r.2]

theorem tableM_obsM {mask : Word} (hm : Masked fullMask mask) {w : Word} (hw : Masked mask w) :
    tableM mask (obsM mask w) = w := by
  apply masked_ext hm (tableM_masked hm _) hw
  intro r
  by_cases hr : bit r mask = true
  · exact tableM_bit (obsM mask w) ⟨r, hr⟩
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit, masked_testBit_false hw hfalse]

theorem tableM_inv {mask : Word} (hm : Masked fullMask mask) (f : WireFn (SubRow mask)) :
    tableM mask (inv f) = Nat.xor mask (tableM mask f) := by
  apply masked_ext hm (tableM_masked hm _) (masked_xor (tableM_masked hm _))
  intro r
  by_cases hr : bit r mask = true
  · rw [tableM_bit (inv f) ⟨r, hr⟩]
    change inv f ⟨r, hr⟩ = (mask ^^^ tableM mask f).testBit r.val
    rw [Nat.testBit_xor]
    have h1 : mask.testBit r.val = true := hr
    have h2 : (tableM mask f).testBit r.val = f ⟨r, hr⟩ := tableM_bit f ⟨r, hr⟩
    rw [h1, h2]; simp [inv]
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit,
      masked_testBit_false (masked_xor (tableM_masked hm _)) hfalse]

theorem tableM_combine {mask : Word} (hm : Masked fullMask mask) (d : Bool) (f g : WireFn (SubRow mask)) :
    tableM mask (combine d f g) = primeW d (tableM mask f) (tableM mask g) := by
  apply masked_ext hm (tableM_masked hm _) (masked_primeW d (tableM_masked hm _) (tableM_masked hm _))
  intro r
  by_cases hr : bit r mask = true
  · rw [tableM_bit (combine d f g) ⟨r, hr⟩]
    have hf := tableM_bit f ⟨r, hr⟩
    have hg := tableM_bit g ⟨r, hr⟩
    cases d <;> simp [combine, primeW, bit, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or] at hf hg ⊢ <;> rw [hf, hg]
  · have hfalse : mask.testBit r.val = false := by simpa [bit] using hr
    rw [bit, masked_testBit_false (tableM_masked hm _) hfalse, bit,
      masked_testBit_false (masked_primeW d (tableM_masked hm _) (tableM_masked hm _)) hfalse]

theorem available_rep {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {bank : List (WireFn (SubRow mask))} {a : WireFn (SubRow mask)} (h : Available bank a) :
    Repr mask ((bank.map (tableM mask)).map (nrm mask)) (tableM mask a) := by
  rcases h with hmem | ⟨b, rfl⟩ | hinv
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hmem))
  · apply repr_const (tableM_masked hm _)
    cases b
    · left
      apply masked_ext hm (tableM_masked hm _) (masked_zero mask)
      intro r
      by_cases hr : bit r mask = true
      · exact (tableM_bit _ ⟨r, hr⟩).trans (by simp [bit])
      · have hf : mask.testBit r.val = false := by simpa [bit] using hr
        rw [bit, masked_testBit_false (tableM_masked hm _) hf]; simp [bit]
    · right
      apply masked_ext hm (tableM_masked hm _) (masked_self mask)
      intro r
      by_cases hr : bit r mask = true
      · exact (tableM_bit _ ⟨r, hr⟩).trans hr.symm
      · have hf : mask.testBit r.val = false := by simpa [bit] using hr
        rw [bit, masked_testBit_false (tableM_masked hm _) hf, bit, hf]
  · have hi := tableM_inv hm a
    refine Or.inl ?_
    rw [← nrm_xor hm0 (tableM_masked hm a), ← hi]
    exact List.mem_map_of_mem (List.mem_map_of_mem hinv)

theorem reach_live_sub {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List (WireFn (SubRow mask))} {p bank}
    (h : Reach roots p bank) {T k S} (run : Live mask T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map (tableM mask)).map (nrm mask)) :
    ∃ l V, l ≤ p + k ∧ Live mask T l V ∧ ∀ a ∈ V, a ∈ (roots.map (tableM mask)).map (nrm mask) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, tableM_combine hm] at sub
    have rep := primeW_rep hm0 d (tableM_masked hm a) (tableM_masked hm b)
      (available_rep hm hm0 ha) (available_rep hm hm0 hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pull_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun w hw => by simpa [or_comm] using sub w hw)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def plainWord (mask a : Word) : Bool := Nat.beq (Nat.land a mask) a && !a.testBit 0

theorem nrm_map {mask : Word} {w : List Word} (h : w.all (plainWord mask) = true) :
    w.map (nrm mask) = w := by
  have e : w.map (nrm mask) = w.map id := by
    apply List.map_congr_left
    intro a ha
    have hp := List.all_eq_true.mp h a ha
    simp only [plainWord, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact nrm_id hp.2
  rw [e, List.map_id]

def LowerM (mask : Word) (roots : List Word) (T : Word) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map (obsM mask)) p bank → Available bank (obsM mask T) → L ≤ p

def Impossible (mask T : Word) (cap : Nat) (S : Finset Word) : Prop :=
  ∀ k, k ≤ cap → ¬Live mask T k S

def Essential (mask T : Word) (roots : List Word) (a : Word) : Prop :=
  ∃ r s : Row, bit r mask = true ∧ bit s mask = true ∧ bit r T ≠ bit s T ∧
    ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem live_row_difference {mask T k S} (h : Live mask T k S) {r s : Row}
    (hr : bit r mask = true) (hs : bit s mask = true) (diff : bit r T ≠ bit s T) :
    ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d hd ha hb _ _ _ ih =>
    obtain ⟨v, hv, hdv⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b, by simp, ?_⟩
        intro beq
        apply hdv
        have h1 := binOp_testBit hd ha.1 hb.1 r.val
        have h2 := binOp_testBit hd ha.1 hb.1 s.val
        simp only [bit] at hr hs aeq beq ⊢
        rw [hr] at h1; rw [hs] at h2
        rw [h1, h2, aeq, beq]
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hdv⟩

theorem raw_required {mask T k S} (h : Live mask T k S) (roots : List Word) (a : Word)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (hr : bit r mask = true) (hs : bit s mask = true)
    (diff : bit r T ≠ bit s T) (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := live_row_difference h hr hs diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

theorem reach_live {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List Word} {p bank T} (hp : Proper mask T) (nT : plainWord mask T = true)
    (nR : roots.all (plainWord mask) = true)
    (h : Reach (roots.map (obsM mask)) p bank) (hit : Available bank (obsM mask T)) :
    ∃ k S, k ≤ p ∧ Live mask T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm' := available_rep hm hm0 hit
  rw [tableM_obsM hm hp.1] at hm'
  unfold Repr at hm'
  have nT0 : T.testBit 0 = false := by
    simp only [plainWord, Bool.and_eq_true, Bool.not_eq_true'] at nT; exact nT.2
  rw [nrm_id nT0] at hm'
  have mem := hm'.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reach_live_sub hm hm0 h (Live.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map (obsM mask)).map (tableM mask) = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha
    have hpa := List.all_eq_true.mp nR a ha
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at hpa
    exact tableM_obsM hm hpa.1
  rw [e, nrm_map nR] at hs
  exact hs

theorem lower_impossible {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {roots : List Word} {T L} (hp : Proper mask T) (nT : plainWord mask T = true)
    (nR : roots.all (plainWord mask) = true)
    (essential : ∀ a ∈ roots, Essential mask T roots a)
    (noRun : Impossible mask T L roots.toFinset) : LowerM mask roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reach_live hm hm0 hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm' => ?_, hs a⟩
    obtain ⟨r, s, hr, hs', hd, iso⟩ := essential _ hm'
    exact raw_required run roots a hs r s hr hs' hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {mask v : Word} (hm : Masked fullMask mask) (hv : Proper mask v) :
    ¬Constant (obsM mask v) := by
  rintro ⟨b, h⟩
  cases b
  · apply hv.2.1
    apply masked_ext hm hv.1 (masked_zero mask)
    intro r
    by_cases hr : bit r mask = true
    · exact (congrFun h ⟨r, hr⟩).trans (by simp [bit])
    · have hf : mask.testBit r.val = false := by simpa [bit] using hr
      rw [bit, masked_testBit_false hv.1 hf]; simp [bit]
  · apply hv.2.2
    apply masked_ext hm hv.1 (masked_self mask)
    intro r
    by_cases hr : bit r mask = true
    · exact (congrFun h ⟨r, hr⟩).trans hr.symm
    · have hf : mask.testBit r.val = false := by simpa [bit] using hr
      rw [bit, masked_testBit_false hv.1 hf, bit, hf]

def Slice (mask : Word) (raw : List Word) (T dom : Word) (L : Nat) : Prop :=
  ∃ (subMask : Word) (f : SubRow subMask → SubRow mask) (roots : List Word),
    (∀ r, bit (f r).1 dom = true) ∧
    (∀ a ∈ raw, Available (roots.map (obsM subMask)) (restrictRows f (obsM mask a))) ∧
    ¬Constant (restrictRows f (obsM mask T)) ∧
    ∀ p bank, Reach (roots.map (obsM subMask)) p bank →
      Available bank (restrictRows f (obsM mask T)) → L ≤ p

def checkSlice (f : Row → Row) (mask : Word) (raw : List Word) (T dom : Word)
    (subMask : Word) (roots : List Word) (subT : Word) : Bool :=
  (List.finRange 256).all (fun r =>
    !bit r subMask || (bit (f r) mask && bit (f r) dom && (bit (f r) T == bit r subT))) &&
  raw.all (fun a =>
    (List.finRange 256).all (fun r => !bit r subMask || !bit (f r) a) ||
    (List.finRange 256).all (fun r => !bit r subMask || bit (f r) a) ||
    roots.any (fun b => (List.finRange 256).all (fun r => !bit r subMask || (bit (f r) a == bit r b))) ||
    roots.any (fun b => (List.finRange 256).all (fun r => !bit r subMask || (bit (f r) a == !bit r b))))

theorem checkSlice_sound {f : Row → Row} {mask : Word} {raw : List Word} {T dom subMask : Word}
    {roots : List Word} {subT : Word} {L : Nat}
    (hmSub : Masked fullMask subMask) (hpSub : Proper subMask subT)
    (hL : LowerM subMask roots subT L)
    (hc : checkSlice f mask raw T dom subMask roots subT = true) :
    Slice mask raw T dom L := by
  simp only [checkSlice, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, List.any_eq_true] at hc
  obtain ⟨hrows, hraw⟩ := hc
  have hfM : ∀ r : SubRow subMask, bit (f r.1) mask = true := by
    intro r
    have h := hrows r.1 (List.mem_finRange r.1)
    rcases h with h0 | ⟨⟨h1, _⟩, _⟩
    · exact absurd r.2 (by simp [h0])
    · exact h1
  let g : SubRow subMask → SubRow mask := fun r => ⟨f r.1, hfM r⟩
  have hdom : ∀ r : SubRow subMask, bit (g r).1 dom = true := by
    intro r
    have h := hrows r.1 (List.mem_finRange r.1)
    rcases h with h0 | ⟨⟨_, h2⟩, _⟩
    · exact absurd r.2 (by simp [h0])
    · exact h2
  have hTeq : restrictRows g (obsM mask T) = obsM subMask subT := by
    funext r
    have h := hrows r.1 (List.mem_finRange r.1)
    rcases h with h0 | ⟨_, h3⟩
    · exact absurd r.2 (by simp [h0])
    · exact h3
  refine ⟨subMask, g, roots, hdom, ?_, hTeq ▸ observe_proper hmSub hpSub, hTeq ▸ hL⟩
  intro a ha
  rcases hraw a ha with ((hz | ho) | ⟨b, hb, he⟩) | ⟨b, hb, hne⟩
  · refine Or.inr (Or.inl ⟨false, funext fun r => ?_⟩)
    rcases hz r.1 (List.mem_finRange r.1) with h0 | h1
    · exact absurd r.2 (by simp [h0])
    · exact h1
  · refine Or.inr (Or.inl ⟨true, funext fun r => ?_⟩)
    rcases ho r.1 (List.mem_finRange r.1) with h0 | h1
    · exact absurd r.2 (by simp [h0])
    · exact h1
  · refine Or.inl (List.mem_map.mpr ⟨b, hb, funext fun r => ?_⟩)
    rcases he r.1 (List.mem_finRange r.1) with h0 | h1
    · exact absurd r.2 (by simp [h0])
    · exact h1.symm
  · refine Or.inr (Or.inr (List.mem_map.mpr ⟨b, hb, funext fun r => ?_⟩))
    rcases hne r.1 (List.mem_finRange r.1) with h0 | h1
    · exact absurd r.2 (by simp [h0])
    · change bit r.1 b = !(bit (f r.1) a)
      rw [h1]; simp

def checkEssential (mask T : Word) (roots : List Word) (a : Word) (r s : Row) : Bool :=
  bit r mask && bit s mask && (bit r T != bit s T) &&
    roots.all (fun w => Nat.beq w a || (bit r w == bit s w))

theorem checkEssential_sound {mask T : Word} {roots : List Word} {a : Word} {r s : Row}
    (h : checkEssential mask T roots a r s = true) : Essential mask T roots a := by
  simp only [checkEssential, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true,
    Nat.beq_eq, beq_iff_eq] at h
  exact ⟨r, s, h.1.1.1, h.1.1.2, h.1.2, fun w hw hne => (h.2 w hw).resolve_left hne⟩

def checkAllEss (mask T : Word) (roots : List Word) (ps : List Nat) : Bool :=
  (List.zip roots ps).length == roots.length &&
  (List.zip roots ps).all (fun (a, x) =>
    checkEssential mask T roots a
      ⟨Nat.mod (Nat.div x 256) 256, Nat.mod_lt _ (by decide)⟩
      ⟨Nat.mod x 256, Nat.mod_lt _ (by decide)⟩)

theorem checkAllEss_sound {mask T : Word} {roots : List Word} {ps : List Nat}
    (h : checkAllEss mask T roots ps = true) : ∀ a ∈ roots, Essential mask T roots a := by
  simp only [checkAllEss, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (List.zip roots ps).length := by omega
  have hmem : (List.zip roots ps)[i] ∈ List.zip roots ps := List.getElem_mem hi'
  have he := hall _ hmem
  simp only [List.getElem_zip] at he
  exact checkEssential_sound he

def isConst (dom a : Word) : Bool :=
  forceNat (Nat.land a dom) fun m =>
    match Nat.beq m 0 with | true => true | false => Nat.beq m dom

theorem isConst_eq (dom a : Word) :
    isConst dom a = (Nat.beq (Nat.land a dom) 0 || Nat.beq (Nat.land a dom) dom) := by
  unfold isConst
  rw [forceNat_eq]
  cases Nat.beq (Nat.land a dom) 0 <;> rfl

theorem masked_zero_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (hz : Nat.land a dom = 0) :
    restrictRows f (obsM mask a) = fun _ => false := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) hz
  simp only [nat_land_eq, Nat.testBit_and, Nat.zero_testBit] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true] at h1
  exact h1

theorem masked_one_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (ho : Nat.land a dom = dom) :
    restrictRows f (obsM mask a) = fun _ => true := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) ho
  simp only [nat_land_eq, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true] at h1
  exact h1

theorem masked_eq_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a b : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (heq : Nat.land a dom = Nat.land b dom) :
    restrictRows f (obsM mask a) = restrictRows f (obsM mask b) := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) heq
  simp only [nat_land_eq, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true, Bool.and_true] at h1
  exact h1

theorem masked_neg_fn {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom a b : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (heq : Nat.xor (Nat.land a dom) dom = Nat.land b dom) :
    inv (restrictRows f (obsM mask a)) = restrictRows f (obsM mask b) := by
  funext r
  have h1 := congrArg (fun x => x.testBit (f r).1.val) heq
  simp only [nat_xor_eq, nat_land_eq, Nat.testBit_xor, Nat.testBit_and] at h1
  have hd : dom.testBit (f r).1.val = true := hdom r
  rw [hd, Bool.and_true, Bool.and_true] at h1
  simpa [inv, restrictRows, obsM, bit] using h1

theorem count_constants {mask subMask : Word} {f : SubRow subMask → SubRow mask} {dom : Word}
    (hdom : ∀ r, bit (f r).1 dom = true) (ws : List Word) :
    ws.countP (isConst dom) ≤ mass ((ws.map (obsM mask)).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases hc : isConst dom a
    · simpa using ih.trans (Nat.le_add_left _ _)
    · rw [isConst_eq, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hc
      have hcon : Constant (restrictRows f (obsM mask a)) := by
        rcases hc with hz | ho
        · exact ⟨false, masked_zero_fn hdom hz⟩
        · exact ⟨true, masked_one_fn hdom ho⟩
      simpa [cost, hcon, Nat.add_comm] using Nat.succ_le_succ ih

theorem slice_lift {mask : Word} (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    {raw : List Word} {T dom : Word} {L : Nat}
    (hp : Proper mask T) (nT : plainWord mask T = true) (nR : raw.all (plainWord mask) = true)
    (nd : raw.Nodup) (ess : ∀ a ∈ raw, Essential mask T raw a)
    (hsl : Slice mask raw T dom L) :
    LowerM mask raw T (L + raw.countP (isConst dom)) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reach_live hm hm0 hp nT nR hr hit
  have he : raw.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun h => ?_, sub a⟩
    obtain ⟨r, s, hrm, hsm, hd, iso⟩ := ess a h
    exact raw_required run raw a sub r s hrm hsm hd iso
  obtain ⟨subMask, f, roots, hdom, hsup, hnc, hlo⟩ := hsl
  have rrun := list_run run raw nd he
  have psup : supply (roots.map (obsM subMask)) ((raw.map (obsM mask)).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h1
    exact hsup a ha
  have pb := projected_bound f rrun hnc Reach.start psup hlo
  have cc := count_constants hdom raw
  omega

def containsNat (z : Word) : List Word → Bool
  | [] => false
  | w :: ws => match Nat.beq w z with | true => true | false => containsNat z ws

theorem containsNat_iff (z : Word) (ws : List Word) : containsNat z ws = true ↔ z ∈ ws := by
  induction ws with
  | nil => simp [containsNat]
  | cons w ws ih =>
    unfold containsNat
    cases h : Nat.beq w z
    · have hne : z ≠ w := fun e => by rw [Nat.beq_eq.mpr e.symm] at h; exact Bool.noConfusion h
      simp [ih, hne]
    · simp [Nat.beq_eq.mp h]

def availableB (dom : Word) (bank : List Word) (a : Word) : Bool :=
  forceNat (Nat.land a dom) fun m =>
    match Nat.beq m 0 with
    | true => true
    | false =>
      match Nat.beq m dom with
      | true => true
      | false =>
        match containsNat m bank with
        | true => true
        | false => containsNat (Nat.xor m dom) bank

def poolSupply {mask subMask : Word} (f : SubRow subMask → SubRow mask)
    (bank : List (WireFn (SubRow subMask))) (ws : List Word) : Prop :=
  ∀ a ∈ ws, Available bank (restrictRows f (obsM mask a))

theorem availableB_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom a : Word} {bank : List (WireFn (SubRow subMask))} {pool : List Word}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hpool : ∀ v ∈ pool, Masked dom v ∧ Available bank (restrictRows f (obsM mask v)))
    (hc : availableB dom pool a = true) :
    Available bank (restrictRows f (obsM mask a)) := by
  unfold availableB at hc
  rw [forceNat_eq] at hc
  cases h0 : Nat.beq (Nat.land a dom) 0 with
  | true =>
    exact Or.inr (Or.inl ⟨false, masked_zero_fn hdom (Nat.beq_eq.mp h0)⟩)
  | false =>
    rw [h0] at hc
    cases h1 : Nat.beq (Nat.land a dom) dom with
    | true =>
      exact Or.inr (Or.inl ⟨true, masked_one_fn hdom (Nat.beq_eq.mp h1)⟩)
    | false =>
      rw [h1] at hc
      cases h2 : containsNat (Nat.land a dom) pool with
      | true =>
        have hm := (containsNat_iff _ _).mp h2
        obtain ⟨md, av⟩ := hpool _ hm
        have heq : Nat.land a dom = Nat.land (Nat.land a dom) dom := (md).symm
        exact masked_eq_fn hdom heq ▸ av
      | false =>
        rw [h2] at hc
        have hm := (containsNat_iff _ _).mp hc
        obtain ⟨md, av⟩ := hpool _ hm
        have heq : Nat.xor (Nat.land a dom) dom = Nat.land (Nat.xor (Nat.land a dom) dom) dom := md.symm
        have hinv := masked_neg_fn hdom heq
        have hav := avail_inv (hinv ▸ av)
        rwa [inv_inv'] at hav

structure CutSpec where
  dom : Word
  bound : Nat
  stock : List Word

def ValidCut (mask : Word) (raw : List Word) (T : Word) (c : CutSpec) : Prop :=
  Slice mask raw T c.dom c.bound ∧
  ∀ v ∈ c.stock, Masked c.dom v ∧ ∃ a ∈ raw, Nat.land a c.dom = v

def mkPairs (ps : List Nat) : List (Row × Row) :=
  ps.map (fun x => (⟨Nat.mod (Nat.div x 256) 256, Nat.mod_lt _ (by decide)⟩,
                    ⟨Nat.mod x 256, Nat.mod_lt _ (by decide)⟩))

def mkCut (raw : List Word) (dom : Word) (bound : Nat) : CutSpec :=
  ⟨dom, bound, (raw.map (fun a => Nat.land a dom)).filter (fun v => !Nat.beq v 0 && !Nat.beq v dom)⟩

theorem mkCut_valid {f : Row → Row} {mask : Word} {raw : List Word} {T dom subMask : Word}
    {roots : List Word} {subT : Word} {L : Nat}
    (hL : LowerM subMask roots subT L)
    (hc : (Nat.beq (Nat.land subMask fullMask) subMask &&
           Nat.beq (Nat.land subT subMask) subT &&
           !Nat.beq subT 0 && !Nat.beq subT subMask &&
           checkSlice f mask raw T dom subMask roots subT) = true) :
    ValidCut mask raw T (mkCut raw dom L) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have h3' : subT ≠ 0 := fun e => by rw [e] at h3; cases h3
  have h4' : subT ≠ subMask := fun e => by rw [e] at h4; exact absurd (Nat.beq_eq.mpr rfl) (by rw [h4]; decide)
  refine ⟨checkSlice_sound h1 ⟨h2, h3', h4'⟩ hL h5, fun v hv => ?_⟩
  simp only [mkCut, List.mem_filter, List.mem_map] at hv
  obtain ⟨⟨a, ha, rfl⟩, _⟩ := hv
  exact ⟨masked_land_right (masked_self dom), a, ha, rfl⟩

structure MatPool where
  dom : Word
  bound : Nat
  paid : Nat
  bank : List Word
  wsConstMask : Nat
  wsConstCnt : Nat

def ValidPool (mask : Word) (raw : List Word) (T : Word) (ws : List Word) (p : MatPool) : Prop :=
  ∃ (subMask : Word) (f : SubRow subMask → SubRow mask) (roots : List Word)
    (bank : List (WireFn (SubRow subMask))),
    (∀ r, bit (f r).1 p.dom = true) ∧
    ¬Constant (restrictRows f (obsM mask T)) ∧
    (∀ q bs, Reach (roots.map (obsM subMask)) q bs → Available bs (restrictRows f (obsM mask T)) → p.bound ≤ q) ∧
    Reach (roots.map (obsM subMask)) p.paid bank ∧
    (∀ v ∈ p.bank, Masked p.dom v ∧ Available bank (restrictRows f (obsM mask v))) ∧
    poolSupply f bank ws ∧
    (∀ i < ws.length, (Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 i)) 2 == 1) = isConst p.dom (ws.getD i 0)) ∧
    p.wsConstCnt = ws.countP (isConst p.dom)

def recipeGateD (dom : Word) (bank : List Word) (w a b : Word) : Bool :=
  match availableB dom bank a with
  | false => false
  | true =>
    match availableB dom bank b with
    | false => false
    | true =>
      forceNat (Nat.land w dom) fun mw =>
        forceNat (Nat.land a dom) fun ma =>
          forceNat (Nat.land b dom) fun mb =>
            match Nat.beq mw (Nat.land ma mb) with
            | true => true
            | false =>
              match Nat.beq mw (Nat.lor ma mb) with
              | true => true
              | false =>
                match Nat.beq mw (Nat.land ma (Nat.xor dom mb)) with
                | true => true
                | false =>
                  match Nat.beq mw (Nat.land (Nat.xor dom ma) mb) with
                  | true => true
                  | false =>
                    match Nat.beq (Nat.xor mw dom) (Nat.land ma mb) with
                    | true => true
                    | false =>
                      match Nat.beq (Nat.xor mw dom) (Nat.lor ma mb) with
                      | true => true
                      | false =>
                        match Nat.beq (Nat.xor mw dom) (Nat.land ma (Nat.xor dom mb)) with
                        | true => true
                        | false =>
                          Nat.beq (Nat.xor mw dom) (Nat.land (Nat.xor dom ma) mb)

theorem recipeGateD_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom w a b : Word} {roots : List (WireFn (SubRow subMask))} {p : Nat}
    {bank : List (WireFn (SubRow subMask))} {pool : List Word}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hr : Reach roots p bank)
    (hpool : ∀ v ∈ pool, Masked dom v ∧ Available bank (restrictRows f (obsM mask v)))
    (hg : recipeGateD dom pool w a b = true) :
    ∃ next, Reach roots (p + 1) next ∧
      ∀ v ∈ (Nat.land w dom) :: pool, Masked dom v ∧ Available next (restrictRows f (obsM mask v)) := by
  unfold recipeGateD at hg
  cases ha : availableB dom pool a with
  | false => simp [ha] at hg
  | true =>
    rw [ha] at hg
    cases hb : availableB dom pool b with
    | false => simp [hb] at hg
    | true =>
      rw [hb, forceNat_eq, forceNat_eq, forceNat_eq] at hg
      have hva := availableB_sound hdom hpool ha
      have hvb := availableB_sound hdom hpool hb
      have mkGate (d : Nat) (hd : d < 4) (flip : Bool)
          (heq : (if flip then Nat.xor (Nat.land w dom) dom else Nat.land w dom) = binOp dom d (Nat.land a dom) (Nat.land b dom)) :
          ∃ next, Reach roots (p + 1) next ∧
            ∀ v ∈ (Nat.land w dom) :: pool, Masked dom v ∧ Available next (restrictRows f (obsM mask v)) := by
        obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime hd hva hvb
        refine ⟨combine op x y :: bank, Reach.two op hr hx hy, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · refine ⟨masked_land_right (masked_self dom), ?_⟩
          have hfn : (if flip then inv (restrictRows f (obsM mask (Nat.land w dom))) else restrictRows f (obsM mask (Nat.land w dom))) =
              comb d (restrictRows f (obsM mask a)) (restrictRows f (obsM mask b)) := by
            funext r
            have hbit := congrArg (fun t => t.testBit (f r).1.val) heq
            have hdr : dom.testBit (f r).1.val = true := hdom r
            have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
            cases flip <;> rcases h4 with rfl | rfl | rfl | rfl <;>
              simp only [ite_true, ite_false, Bool.false_eq_true, binOp, comb, combine, inv, restrictRows, obsM, bit,
                nat_land_eq, nat_lor_eq, nat_xor_eq,
                Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hdr, Bool.and_true,
                show (1 = 0) = False by decide, show (2 = 0) = False by decide, show (3 = 0) = False by decide,
                show (2 = 1) = False by decide, show (3 = 1) = False by decide, show (3 = 2) = False by decide] at hbit ⊢ <;>
              cases hw : w.testBit (f r).1.val <;> cases ha' : a.testBit (f r).1.val <;> cases hb' : b.testBit (f r).1.val <;>
              simp only [hw, ha', hb', Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
                Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, Bool.xor_true, Bool.xor_false,
                Bool.not_true, Bool.not_false] at hbit ⊢ <;> exact hbit
          rw [e] at hfn
          cases flip
          · simp only [Bool.false_eq_true, ite_false] at hfn
            rw [hfn]; exact Or.inl (by simp)
          · simp only [ite_true] at hfn
            have h1 : Available (combine op x y :: bank) (inv (restrictRows f (obsM mask (Nat.land w dom)))) := by
              rw [hfn]; exact Or.inl (by simp)
            have h2 := avail_inv h1
            rwa [inv_inv'] at h2
        · obtain ⟨md, av⟩ := hpool v hmem
          exact ⟨md, available_cons _ av⟩
      cases h0 : Nat.beq (Nat.land w dom) (Nat.land (Nat.land a dom) (Nat.land b dom))
      · rw [h0] at hg
        cases h1 : Nat.beq (Nat.land w dom) (Nat.lor (Nat.land a dom) (Nat.land b dom))
        · rw [h1] at hg
          cases h2 : Nat.beq (Nat.land w dom) (Nat.land (Nat.land a dom) (Nat.xor dom (Nat.land b dom)))
          · rw [h2] at hg
            cases h3 : Nat.beq (Nat.land w dom) (Nat.land (Nat.xor dom (Nat.land a dom)) (Nat.land b dom))
            · rw [h3] at hg
              cases h4 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.land (Nat.land a dom) (Nat.land b dom))
              · rw [h4] at hg
                cases h5 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.lor (Nat.land a dom) (Nat.land b dom))
                · rw [h5] at hg
                  cases h6 : Nat.beq (Nat.xor (Nat.land w dom) dom) (Nat.land (Nat.land a dom) (Nat.xor dom (Nat.land b dom)))
                  · rw [h6] at hg
                    exact mkGate 3 (by omega) true (Nat.beq_eq.mp hg)
                  · exact mkGate 2 (by omega) true (Nat.beq_eq.mp h6)
                · exact mkGate 1 (by omega) true (Nat.beq_eq.mp h5)
              · exact mkGate 0 (by omega) true (Nat.beq_eq.mp h4)
            · exact mkGate 3 (by omega) false (Nat.beq_eq.mp h3)
          · exact mkGate 2 (by omega) false (Nat.beq_eq.mp h2)
        · exact mkGate 1 (by omega) false (Nat.beq_eq.mp h1)
      · exact mkGate 0 (by omega) false (Nat.beq_eq.mp h0)

abbrev HistStep := Word × Word × Word

def addNeed (dom : Word) (stock needed : List Word) (w : Word) : List Word :=
  forceNat (Nat.land w dom) fun m =>
    match Nat.beq m 0 with
    | true => needed
    | false =>
      match Nat.beq m dom with
      | true => needed
      | false =>
        match containsNat m stock with
        | true => needed
        | false =>
          match containsNat (Nat.xor m dom) stock with
          | true => needed
          | false =>
            match containsNat m needed with
            | true => needed
            | false =>
              match containsNat (Nat.xor m dom) needed with
              | true => needed
              | false => m :: needed

def needStart (dom : Word) (stock : List Word) : List Word → List Word → List Word
  | [], acc => acc
  | w :: ws, acc => needStart dom stock ws (addNeed dom stock acc w)

def needClose (dom : Word) (stock : List Word) : List HistStep → List Word → List Word
  | [], acc => acc
  | (w, a, b) :: hs, acc =>
    forceNat (Nat.land w dom) fun m =>
      let acc' := match containsNat m acc with
        | true => addNeed dom stock (addNeed dom stock acc a) b
        | false =>
          match containsNat (Nat.xor m dom) acc with
          | true => addNeed dom stock (addNeed dom stock acc a) b
          | false => acc
      needClose dom stock hs acc'

def replayHist (dom : Word) (needed : List Word) : List HistStep → Nat → List Word → Nat × List Word
  | [], paid, bank => (paid, bank)
  | (w, a, b) :: hs, paid, bank =>
    forceNat (Nat.land w dom) fun m =>
      let want := match containsNat m needed with | true => true | false => containsNat (Nat.xor m dom) needed
      match want with
      | false => replayHist dom needed hs paid bank
      | true =>
        match availableB dom bank w with
        | true => replayHist dom needed hs paid bank
        | false =>
          match recipeGateD dom bank w a b with
          | false => replayHist dom needed hs paid bank
          | true => forceNat (Nat.add paid 1) fun p' => replayHist dom needed hs p' (m :: bank)

theorem replayHist_sound {mask subMask : Word} {f : SubRow subMask → SubRow mask}
    {dom : Word} {needed : List Word} {roots : List (WireFn (SubRow subMask))}
    (hdom : ∀ r, bit (f r).1 dom = true)
    (hs : List HistStep) :
    ∀ {paid0 : Nat} {bank0 : List (WireFn (SubRow subMask))} {pool0 : List Word},
      Reach roots paid0 bank0 →
      (∀ v ∈ pool0, Masked dom v ∧ Available bank0 (restrictRows f (obsM mask v))) →
      ∃ bank1, Reach roots (replayHist dom needed hs paid0 pool0).1 bank1 ∧
        ∀ v ∈ (replayHist dom needed hs paid0 pool0).2,
          Masked dom v ∧ Available bank1 (restrictRows f (obsM mask v)) := by
  induction hs with
  | nil => intro paid0 bank0 pool0 hr hp; exact ⟨bank0, hr, hp⟩
  | cons st hs ih =>
    obtain ⟨w, a, b⟩ := st
    intro paid0 bank0 pool0 hr hp
    simp only [replayHist, forceNat_eq]
    split
    · exact ih hr hp
    · split
      · exact ih hr hp
      · cases hg : recipeGateD dom pool0 w a b with
        | false => exact ih hr hp
        | true =>
          obtain ⟨next, hr', hp'⟩ := recipeGateD_sound hdom hr hp hg
          exact ih hr' hp'

def buildConstInfo (dom : Word) : List Word → Nat → Nat → Nat → Nat × Nat
  | [], _, cm, cnt => (cm, cnt)
  | w :: ws, idx, cm, cnt =>
    match isConst dom w with
    | false => buildConstInfo dom ws (Nat.add idx 1) cm cnt
    | true =>
      forceNat (Nat.lor cm (Nat.shiftLeft 1 idx)) fun cm' =>
        forceNat (Nat.add cnt 1) fun cnt' =>
          buildConstInfo dom ws (Nat.add idx 1) cm' cnt'

theorem buildConstInfo_low (dom : Word) :
    ∀ (l : List Word) (i0 c0 n0 k : Nat), k < i0 →
      ((buildConstInfo dom l i0 c0 n0).1).testBit k = c0.testBit k := by
  intro l
  induction l with
  | nil => intro i0 c0 n0 k _; rfl
  | cons u us ihu =>
    intro i0 c0 n0 k hk
    simp only [buildConstInfo]
    cases isConst dom u
    · exact ihu (i0 + 1) c0 n0 k (by omega)
    · simp only [forceNat_eq, nat_add_eq]
      rw [ihu (i0 + 1) _ _ k (by omega)]
      have hne : k ≠ i0 := by omega
      have htb : (Nat.shiftLeft 1 i0).testBit k = false := by rw [testBit_one_shl]; simp [hne]
      rw [nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]

theorem mod_div_shl_eq_testBit (x k : Nat) :
    (Nat.mod (Nat.div x (Nat.shiftLeft 1 k)) 2 == 1) = x.testBit k := by
  simp only [nat_mod_eq, nat_div_eq, nat_shl_eq]
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_eq_decide_div_mod_eq]
  cases h : x / 2 ^ k % 2 == 1 <;> simp_all

theorem buildConstInfo_spec (dom : Word) (ws : List Word) :
    ∀ (idx cm cnt : Nat),
      (∀ j ≥ idx, Nat.mod (Nat.div cm (Nat.shiftLeft 1 j)) 2 = 0) →
      (let res := buildConstInfo dom ws idx cm cnt
       (∀ j < ws.length, (Nat.mod (Nat.div res.1 (Nat.shiftLeft 1 (idx + j))) 2 == 1) = isConst dom (ws.getD j 0)) ∧
       res.2 = cnt + ws.countP (isConst dom)) := by
  induction ws with
  | nil =>
    intro idx cm cnt _
    exact ⟨fun j hj => by simp at hj, by simp [buildConstInfo]⟩
  | cons w ws ih =>
    intro idx cm cnt hhi
    simp only [buildConstInfo]
    cases hc : isConst dom w with
    | false =>
      have hhi' : ∀ j ≥ idx + 1, Nat.mod (Nat.div cm (Nat.shiftLeft 1 j)) 2 = 0 := fun j hj => hhi j (by omega)
      obtain ⟨hbits, hcnt⟩ := ih (idx + 1) cm cnt hhi'
      refine ⟨fun j hj => ?_, ?_⟩
      · cases j with
        | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero, hc, nat_add_eq]
          rw [mod_div_shl_eq_testBit, buildConstInfo_low dom ws (idx + 1) cm cnt idx (by omega)]
          have h0 := hhi idx (Nat.le_refl _)
          have hmt := mod_div_shl_eq_testBit cm idx
          rw [h0] at hmt
          exact hmt.symm
        | succ j' =>
          have hstep : idx + (j' + 1) = (idx + 1) + j' := by omega
          rw [hstep]
          exact hbits j' (by simp at hj; omega)
      · simp only [List.countP_cons, hc, Bool.false_eq_true, ite_false, nat_add_eq]
        exact hcnt
    | true =>
      simp only [forceNat_eq]
      let cm' := Nat.lor cm (Nat.shiftLeft 1 idx)
      have hbit_cm' : ∀ k, cm'.testBit k = (cm.testBit k || decide (k = idx)) := by
        intro k
        rw [show cm' = Nat.lor cm (Nat.shiftLeft 1 idx) from rfl, nat_lor_eq, Nat.testBit_or, testBit_one_shl]
      have hhi' : ∀ j ≥ idx + 1, Nat.mod (Nat.div cm' (Nat.shiftLeft 1 j)) 2 = 0 := by
        intro j hj
        have h0 := hhi j (by omega)
        have ht0 : cm.testBit j = false := by
          have := mod_div_shl_eq_testBit cm j; rw [h0] at this; exact this.symm
        have ht1 : cm'.testBit j = false := by
          rw [hbit_cm', ht0]; simp [show j ≠ idx by omega]
        have hmt := mod_div_shl_eq_testBit cm' j
        rw [ht1] at hmt
        simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at hmt ⊢
        have hlt : cm' / (1 <<< j) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hne : cm' / (1 <<< j) % 2 ≠ 1 := by
          intro he; rw [he] at hmt; exact Bool.noConfusion hmt
        omega
      obtain ⟨hbits, hcnt⟩ := ih (idx + 1) cm' (cnt + 1) hhi'
      refine ⟨fun j hj => ?_, ?_⟩
      · cases j with
        | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero, hc, nat_add_eq]
          rw [mod_div_shl_eq_testBit, buildConstInfo_low dom ws (idx + 1) cm' (cnt + 1) idx (by omega), hbit_cm']
          simp
        | succ j' =>
          have hstep : idx + (j' + 1) = (idx + 1) + j' := by omega
          rw [hstep]
          exact hbits j' (by simp at hj; omega)
      · simp only [List.countP_cons, hc, ite_true, nat_add_eq]
        rw [hcnt]; omega

def materializeCut (c : CutSpec) (ws : List Word) (hist : List HistStep) : Option MatPool :=
  let needed := needClose c.dom c.stock hist (needStart c.dom c.stock ws [])
  let (paid, bank) := replayHist c.dom needed hist.reverse 0 c.stock
  match ws.all (availableB c.dom bank) with
  | false => none
  | true =>
    let (cm, cnt) := buildConstInfo c.dom ws 0 0 0
    some ⟨c.dom, c.bound, paid, bank, cm, cnt⟩

theorem materializeCut_sound {mask : Word} {raw : List Word} {T : Word} {c : CutSpec}
    (hc : ValidCut mask raw T c) {ws : List Word} {hist : List HistStep} {mp : MatPool}
    (hm : materializeCut c ws hist = some mp) :
    ValidPool mask raw T ws mp := by
  obtain ⟨⟨subMask, f, roots, hdom, hsup, hnc, hlo⟩, hstock⟩ := hc
  have hstockPool : ∀ v ∈ c.stock, Masked c.dom v ∧ Available (roots.map (obsM subMask)) (restrictRows f (obsM mask v)) := by
    intro v hv
    obtain ⟨md, a, ha, rfl⟩ := hstock v hv
    refine ⟨md, ?_⟩
    have heq : Nat.land (Nat.land a c.dom) c.dom = Nat.land a c.dom := md
    exact masked_eq_fn hdom heq ▸ hsup a ha
  unfold materializeCut at hm
  dsimp only at hm
  cases hall : ws.all (availableB c.dom (replayHist c.dom (needClose c.dom c.stock hist (needStart c.dom c.stock ws [])) hist.reverse 0 c.stock).2) with
  | false => simp [hall] at hm
  | true =>
    rw [hall] at hm
    injection hm with hmp
    subst hmp
    obtain ⟨bank1, hreach, hbank⟩ := replayHist_sound hdom hist.reverse Reach.start hstockPool
    obtain ⟨hbits, hcnt⟩ := buildConstInfo_spec c.dom ws 0 0 0 (fun j _ => by simp [nat_mod_eq, nat_div_eq])
    refine ⟨subMask, f, roots, bank1, hdom, hnc, hlo, hreach, hbank, ?_, ?_, ?_⟩
    · intro w hw
      exact availableB_sound hdom hbank (List.all_eq_true.mp hall w hw)
    · intro i hi
      simpa using hbits i hi
    · simpa using hcnt

def scalarPoolCut (p : MatPool) (childFuel : Nat) (idxA idxB : Nat) (ka kb : Bool) (z : Word) : Bool :=
  forceNat (Nat.land z p.dom) fun mz =>
    let flatZ := match Nat.beq mz 0 with | true => true | false => Nat.beq mz p.dom
    let extra := match flatZ with
      | true => 0
      | false =>
        match containsNat mz p.bank with
        | true => 0
        | false =>
          match containsNat (Nat.xor mz p.dom) p.bank with
          | true => 0
          | false => 1
    let dropA := match ka with
      | true => 0
      | false => Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxA)) 2
    let dropB := match kb with
      | true => 0
      | false => Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxB)) 2
    let addZ := match flatZ with | true => 1 | false => 0
    Nat.blt (Nat.add (Nat.add childFuel p.paid) extra)
      (Nat.add p.bound (Nat.add (Nat.sub (Nat.sub p.wsConstCnt dropA) dropB) addZ))

theorem countP_erase_two {α : Type} [DecidableEq α] (p : α → Bool) (ws : List α) (hnd : ws.Nodup)
    (a b : α) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (ka kb : Bool) :
    (kept ka a (kept kb b ((ws.erase a).erase b))).countP p =
      ws.countP p - (if ka then 0 else if p a then 1 else 0) - (if kb then 0 else if p b then 1 else 0) := by
  have hb' : b ∈ ws.erase a := (List.mem_erase_of_ne hab.symm).mpr hb
  have h1 : ws.countP p = (if p a then 1 else 0) + (ws.erase a).countP p := by
    have hp := List.perm_cons_erase ha
    rw [hp.countP_eq, List.countP_cons]
    cases p a <;> omega
  have h2 : (ws.erase a).countP p = (if p b then 1 else 0) + ((ws.erase a).erase b).countP p := by
    have hp := List.perm_cons_erase hb'
    rw [hp.countP_eq, List.countP_cons]
    cases p b <;> omega
  cases ka <;> cases kb <;> cases hpa : p a <;> cases hpb : p b <;>
    simp only [kept, List.countP_cons, hpa, hpb, ite_true, ite_false, Bool.false_eq_true] at h1 h2 ⊢ <;> omega

theorem selfPoolCut_sound {mask : Word} {raw : List Word} {T : Word} {ws : List Word}
    {p : MatPool} (vp : ValidPool mask raw T ws p)
    {fuel : Nat} (hnd : ws.Nodup)
    (hcut : Nat.blt (Nat.add fuel p.paid) (Nat.add p.bound p.wsConstCnt) = true) :
    Impossible mask T fuel ws.toFinset := by
  intro k hk run
  obtain ⟨subMask, f, roots, bank, hdom, hnc, hlo, hreach, _, hsup, _, hcnt⟩ := vp
  have rrun := list_run run ws hnd rfl
  have psup : supply bank ((ws.map (obsM mask)).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
    exact hsup w hw
  have pb := projected_bound f rrun hnc hreach psup hlo
  have cc := count_constants hdom ws
  have hlt : fuel + p.paid < p.bound + p.wsConstCnt := by
    simpa [nat_add_eq] using Nat.blt_eq.mp hcut
  omega

theorem scalarPoolCut_sound {mask : Word} {raw : List Word} {T : Word} {ws : List Word}
    {p : MatPool} (vp : ValidPool mask raw T ws p)
    {childFuel idxA idxB d : Nat} {ka kb : Bool}
    (hnd : ws.Nodup) (ha : idxA < ws.length) (hb : idxB < ws.length) (hab : idxA < idxB) (hd : d < 4)
    (hmask : ∀ w ∈ ws, Masked mask w)
    (hfresh : binOp mask d (ws.getD idxA 0) (ws.getD idxB 0) ∉ ws)
    (hcut : scalarPoolCut p childFuel idxA idxB ka kb (binOp mask d (ws.getD idxA 0) (ws.getD idxB 0)) = true) :
    let a := ws.getD idxA 0
    let b := ws.getD idxB 0
    let z := binOp mask d a b
    let child := z :: kept ka a (kept kb b ((ws.erase a).erase b))
    Impossible mask T childFuel child.toFinset := by
  intro a b z child k hk run
  obtain ⟨subMask, f, roots, bank, hdom, hnc, hlo, hreach, hbank, hsup, hcm, hcnt⟩ := vp
  have ham : a ∈ ws := by
    have : ws.getD idxA 0 = ws[idxA] := by simp [List.getD_eq_getElem?_getD, ha]
    rw [show a = ws[idxA] from this]; exact List.getElem_mem ha
  have hbm : b ∈ ws := by
    have : ws.getD idxB 0 = ws[idxB] := by simp [List.getD_eq_getElem?_getD, hb]
    rw [show b = ws[idxB] from this]; exact List.getElem_mem hb
  have hne : a ≠ b := by
    have ea : a = ws[idxA] := by simp [a, List.getD_eq_getElem?_getD, ha]
    have eb : b = ws[idxB] := by simp [b, List.getD_eq_getElem?_getD, hb]
    rw [ea, eb]
    intro eq
    exact Nat.ne_of_lt hab ((List.Nodup.getElem_inj_iff hnd).mp eq)
  have hndc : child.Nodup := by
    let rest := (ws.erase a).erase b
    have hrnd : rest.Nodup := (hnd.erase a).erase b
    have har : a ∉ rest := fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
    have hbr : b ∉ rest := (hnd.erase a).not_mem_erase
    have hamid : a ∉ kept kb b rest := by cases kb <;> simp [kept, har, hne]
    have hfresh' : z ∉ ws := hfresh
    refine List.nodup_cons.mpr ⟨?_, kept_nd ka a _ (kept_nd kb b _ hrnd hbr) hamid⟩
    intro hm
    rcases mem_kept hm with hza | hm
    · exact hfresh' (by rw [hza]; exact ham)
    rcases mem_kept hm with hzb | hm
    · exact hfresh' (by rw [hzb]; exact hbm)
    · exact hfresh' (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
  have hcount : child.countP (isConst p.dom) =
      ws.countP (isConst p.dom) -
        (if ka then 0 else if isConst p.dom a then 1 else 0) -
        (if kb then 0 else if isConst p.dom b then 1 else 0) +
        (if isConst p.dom z then 1 else 0) := by
    simp only [child, List.countP_cons, countP_erase_two (isConst p.dom) ws hnd a b ham hbm hne ka kb]
  have hbitA : Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxA)) 2 = if isConst p.dom a then 1 else 0 := by
    have h := hcm idxA ha
    simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at h ⊢
    have hlt : p.wsConstMask / (1 <<< idxA) % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hca : isConst p.dom a
    · rw [hca] at h; simp only [beq_eq_false_iff_ne] at h; simp; omega
    · rw [hca] at h; simp [beq_iff_eq.mp h]
  have hbitB : Nat.mod (Nat.div p.wsConstMask (Nat.shiftLeft 1 idxB)) 2 = if isConst p.dom b then 1 else 0 := by
    have h := hcm idxB hb
    simp only [nat_mod_eq, nat_div_eq, nat_shl_eq] at h ⊢
    have hlt : p.wsConstMask / (1 <<< idxB) % 2 < 2 := Nat.mod_lt _ (by omega)
    cases hcb : isConst p.dom b
    · rw [hcb] at h; simp only [beq_eq_false_iff_ne] at h; simp; omega
    · rw [hcb] at h; simp [beq_iff_eq.mp h]
  have hflatZ_eq : (match Nat.beq (Nat.land z p.dom) 0 with | true => true | false => Nat.beq (Nat.land z p.dom) p.dom) = isConst p.dom z := by
    rw [isConst_eq]; cases Nat.beq (Nat.land z p.dom) 0 <;> rfl
  have hextra_eq : (match (match Nat.beq (Nat.land z p.dom) 0 with | true => true | false => Nat.beq (Nat.land z p.dom) p.dom) with
      | true => 0
      | false => match containsNat (Nat.land z p.dom) p.bank with
        | true => 0
        | false => match containsNat (Nat.xor (Nat.land z p.dom) p.dom) p.bank with | true => 0 | false => 1) =
      if availableB p.dom p.bank z then 0 else 1 := by
    unfold availableB; rw [forceNat_eq]
    cases Nat.beq (Nat.land z p.dom) 0 <;> cases Nat.beq (Nat.land z p.dom) p.dom <;>
      cases containsNat (Nat.land z p.dom) p.bank <;> cases containsNat (Nat.xor (Nat.land z p.dom) p.dom) p.bank <;> rfl
  unfold scalarPoolCut at hcut
  dsimp only at hcut
  rw [forceNat_eq] at hcut
  change Nat.blt (Nat.add (Nat.add childFuel p.paid) _) _ = true at hcut
  rw [hextra_eq, hflatZ_eq, hbitA, hbitB, hcnt] at hcut
  have hlt_cut : childFuel + p.paid + (if availableB p.dom p.bank z then 0 else 1) < p.bound + child.countP (isConst p.dom) := by
    have h1 := Nat.blt_eq.mp hcut
    rw [hcount]
    cases ka <;> cases kb <;> cases hz : isConst p.dom z <;> simp only [hz, ite_true, ite_false, Bool.false_eq_true, nat_add_eq, nat_sub_eq] at h1 ⊢ <;> omega
  have hsub_rest : ∀ w ∈ kept ka a (kept kb b ((ws.erase a).erase b)), w ∈ ws := by
    intro w hw
    rcases mem_kept hw with rfl | hw
    · exact ham
    rcases mem_kept hw with rfl | hw
    · exact hbm
    · exact List.mem_of_mem_erase (List.mem_of_mem_erase hw)
  have rrun := list_run run child hndc rfl
  have hcc := count_constants hdom child
  cases havz : availableB p.dom p.bank z with
  | true =>
    simp only [havz, ite_true] at hlt_cut
    have hsupc : supply bank ((child.map (obsM mask)).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact availableB_sound hdom hbank havz
      · exact hsup w (hsub_rest w hw')
    have pb := projected_bound f rrun hnc hreach hsupc hlo
    omega
  | false =>
    simp only [havz, Bool.false_eq_true, ite_false] at hlt_cut
    obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime hd (hsup a ham) (hsup b hbm)
    let bank' := combine op x y :: bank
    have hreach' : Reach (roots.map (obsM subMask)) (p.paid + 1) bank' := Reach.two op hreach hx hy
    have hsupc : supply bank' ((child.map (obsM mask)).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h1
      rcases List.mem_cons.mp hw with rfl | hw'
      · change Available bank' (restrictRows f (obsM mask (binOp mask d a b)))
        rw [obsM_binOp hd (hmask a ham) (hmask b hbm), restrict_comb, e]
        exact Or.inl (by simp [bank'])
      · exact available_cons _ (hsup w (hsub_rest w hw'))
    have pb := projected_bound f rrun hnc hreach' hsupc hlo
    omega

structure Wire where
  val : Word
  pos : Nat
  neg : Nat
  sep : Nat

def packBitsFrom (idx : Nat) : List Row → Word → Nat → Nat
  | [], _, acc => acc
  | r :: rs, w, acc =>
    packBitsFrom (idx + 1) rs w (if bit r w then Nat.lor acc (Nat.shiftLeft 1 idx) else acc)

def packBits (rows : List Row) (w : Word) : Nat := packBitsFrom 0 rows w 0

def pairValid (mask T : Word) (p : Row × Row) : Bool :=
  bit p.1 mask && bit p.2 mask && bit p.1 T && !bit p.2 T

def wireMatchesPairs (pairs : List (Row × Row)) (w : Wire) : Bool :=
  Nat.beq w.pos (packBits (pairs.map Prod.fst) w.val) &&
  Nat.beq w.neg (packBits (pairs.map Prod.snd) w.val) &&
  Nat.beq w.sep (Nat.xor w.pos w.neg)

def Faithful (pairs : List (Row × Row)) (w : Wire) : Prop :=
  (∀ i < pairs.length, w.pos.testBit i = bit (pairs.getD i (0, 0)).1 w.val) ∧
  (∀ i < pairs.length, w.neg.testBit i = bit (pairs.getD i (0, 0)).2 w.val) ∧
  (∀ i ≥ pairs.length, w.pos.testBit i = false ∧ w.neg.testBit i = false) ∧
  w.sep = Nat.xor w.pos w.neg

theorem packBits_testBit (rows : List Row) (w : Word) (i : Nat) :
    (packBits rows w).testBit i = if h : i < rows.length then bit rows[i] w else false := by
  have hgen : ∀ (l : List Row) (base acc : Nat),
      (∀ k ≥ base, acc.testBit k = false) →
      (packBitsFrom base l w acc).testBit i =
        if i < base then acc.testBit i
        else if h : i - base < l.length then bit l[i - base] w else false := by
    intro l
    induction l with
    | nil =>
      intro base acc hacc
      simp only [packBitsFrom, List.length_nil]
      by_cases hi : i < base
      · simp [hi]
      · simp [hi, hacc i (by omega)]
    | cons r rs ih =>
      intro base acc hacc
      simp only [packBitsFrom]
      have hacc' : ∀ k ≥ base + 1, (if bit r w then Nat.lor acc (Nat.shiftLeft 1 base) else acc).testBit k = false := by
        intro k hk
        cases bit r w
        · exact hacc k (by omega)
        · have hne : k ≠ base := by omega
          have htb : (Nat.shiftLeft 1 base).testBit k = false := by rw [testBit_one_shl]; simp [hne]
          simp only [ite_true, nat_lor_eq, Nat.testBit_or, hacc k (by omega), htb, Bool.or_false]
      rw [ih (base + 1) _ hacc']
      by_cases hlt : i < base
      · have hlt1 : i < base + 1 := by omega
        simp only [hlt, hlt1, ite_true]
        cases bit r w
        · rfl
        · have hne : i ≠ base := by omega
          have htb : (Nat.shiftLeft 1 base).testBit i = false := by rw [testBit_one_shl]; simp [hne]
          simp only [ite_true, nat_lor_eq, Nat.testBit_or, htb, Bool.or_false]
      · by_cases heq : i = base
        · subst heq
          have hlt1 : i < i + 1 := by omega
          simp only [hlt, hlt1, ite_true, ite_false, Nat.sub_self, List.length_cons, Nat.zero_lt_succ,
            List.getElem_cons_zero]
          cases hb : bit r w
          · simp [hacc i (Nat.le_refl _)]
          · simp [nat_lor_eq, Nat.testBit_or, testBit_one_shl]
        · have hng1 : ¬ (i < base + 1) := by omega
          simp only [hlt, hng1, ite_false]
          have hsub : i - base = (i - (base + 1)) + 1 := by omega
          rw [hsub]
          by_cases hs : i - (base + 1) < rs.length
          · simp [hs]
          · simp [hs]
  have h0 := hgen rows 0 0 (fun _ _ => by simp)
  simpa [packBits] using h0

theorem wireMatchesPairs_sound {pairs : List (Row × Row)} {w : Wire}
    (h : wireMatchesPairs pairs w = true) : Faithful pairs w := by
  simp only [wireMatchesPairs, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hpos, hneg⟩, hsep⟩ := h
  refine ⟨?_, ?_, ?_, hsep⟩
  · intro i hi
    rw [hpos, packBits_testBit]
    have hi' : i < (pairs.map Prod.fst).length := by simpa using hi
    simp [hi', List.getD_eq_getElem?_getD, hi]
  · intro i hi
    rw [hneg, packBits_testBit]
    have hi' : i < (pairs.map Prod.snd).length := by simpa using hi
    simp [hi', List.getD_eq_getElem?_getD, hi]
  · intro i hi
    rw [hpos, hneg, packBits_testBit, packBits_testBit]
    have h1 : ¬ (i < (pairs.map Prod.fst).length) := by rw [List.length_map]; omega
    have h2 : ¬ (i < (pairs.map Prod.snd).length) := by rw [List.length_map]; omega
    simp only [dif_neg h1, dif_neg h2, and_self]

theorem faithful_bin {mask : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {a b : Wire} (ha : Faithful pairs a) (hb : Faithful pairs b)
    (hma : Masked mask a.val) (hmb : Masked mask b.val)
    (d : Nat) (hd : d < 4) :
    let p0 := Nat.land a.pos b.pos
    let n0 := Nat.land a.neg b.neg
    let sep0 := Nat.xor p0 n0
    let posZ := match d with | 0 => p0 | 1 => Nat.lor a.pos b.pos | 2 => Nat.xor a.pos p0 | _ => Nat.xor b.pos p0
    let negZ := match d with | 0 => n0 | 1 => Nat.lor a.neg b.neg | 2 => Nat.xor a.neg n0 | _ => Nat.xor b.neg n0
    let sepZ := match d with | 0 => sep0 | 1 => Nat.xor a.sep (Nat.xor b.sep sep0) | 2 => Nat.xor a.sep sep0 | _ => Nat.xor b.sep sep0
    Faithful pairs ⟨binOp mask d a.val b.val, posZ, negZ, sepZ⟩ := by
  intro p0 n0 sep0 posZ negZ sepZ
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have hpm : ∀ i < pairs.length, bit (pairs.getD i (0, 0)).1 mask = true ∧ bit (pairs.getD i (0, 0)).2 mask = true := by
    intro i hi
    have hmem : pairs.getD i (0, 0) ∈ pairs := by
      simp [List.getD_eq_getElem?_getD, hi]
    have hv := hpairs _ hmem
    simp only [pairValid, Bool.and_eq_true] at hv
    exact ⟨hv.1.1.1, hv.1.1.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := (hpm i hi).1
    have ha1 := ha.1 i hi
    have hb1 := hb.1 i hi
    have hbt := binOp_testBit hd hma hmb (pairs.getD i (0, 0)).1.val
    simp only [bit] at h1 ha1 hb1 ⊢
    rw [h1] at hbt
    rw [hbt]
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [posZ, p0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha1, hb1] <;>
      cases a.val.testBit (pairs.getD i (0, 0)).1.val <;>
      cases b.val.testBit (pairs.getD i (0, 0)).1.val <;> rfl
  · intro i hi
    have h2 := (hpm i hi).2
    have ha2 := ha.2.1 i hi
    have hb2 := hb.2.1 i hi
    have hbt := binOp_testBit hd hma hmb (pairs.getD i (0, 0)).2.val
    simp only [bit] at h2 ha2 hb2 ⊢
    rw [h2] at hbt
    rw [hbt]
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [negZ, n0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha2, hb2] <;>
      cases a.val.testBit (pairs.getD i (0, 0)).2.val <;>
      cases b.val.testBit (pairs.getD i (0, 0)).2.val <;> rfl
  · intro i hi
    obtain ⟨ha1, ha2⟩ := ha.2.2.1 i hi
    obtain ⟨hb1, hb2⟩ := hb.2.2.1 i hi
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [posZ, negZ, p0, n0, nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor, ha1, ha2, hb1, hb2]
  · apply Nat.eq_of_testBit_eq
    intro i
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp only [sepZ, sep0, posZ, negZ, p0, n0, ha.2.2.2, hb.2.2.2,
        nat_land_eq, Nat.testBit_and, nat_lor_eq, Nat.testBit_or, nat_xor_eq, Nat.testBit_xor] <;>
      cases a.pos.testBit i <;> cases b.pos.testBit i <;> cases a.neg.testBit i <;> cases b.neg.testBit i <;> rfl

theorem sep_required {mask T : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {ws : List Wire} (hfaith : ∀ w ∈ ws, Faithful pairs w)
    {k : Nat} (run : Live mask T k (ws.map Wire.val).toFinset) :
    ws.foldr (fun w acc => Nat.lor w.sep acc) 0 = Nat.sub (Nat.shiftLeft 1 pairs.length) 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hfold : ∀ (l : List Wire), (l.foldr (fun w acc => Nat.lor w.sep acc) 0).testBit i =
      l.any (fun w => w.sep.testBit i) := by
    intro l; induction l with
    | nil => simp
    | cons w ws ih =>
      change (Nat.lor w.sep (ws.foldr (fun w acc => Nat.lor w.sep acc) 0)).testBit i = _
      rw [nat_lor_eq, Nat.testBit_or, ih, List.any_cons]
  rw [hfold]
  have hmask : (Nat.sub (Nat.shiftLeft 1 pairs.length) 1).testBit i = decide (i < pairs.length) := by
    rw [nat_sub_eq, nat_shl_eq, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.testBit_two_pow_sub_one (n := pairs.length) (i := i)
  rw [hmask]
  by_cases hi : i < pairs.length
  · simp only [hi, decide_true, List.any_eq_true]
    have hmem : pairs.getD i (0, 0) ∈ pairs := by simp [List.getD_eq_getElem?_getD, hi]
    have hv := hpairs _ hmem
    simp only [pairValid, Bool.and_eq_true, Bool.not_eq_true'] at hv
    have hdiff : bit (pairs.getD i (0, 0)).1 T ≠ bit (pairs.getD i (0, 0)).2 T := by
      rw [hv.1.2, hv.2]; decide
    obtain ⟨v, hvS, hdv⟩ := live_row_difference run hv.1.1.1 hv.1.1.2 hdiff
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hvS)
    refine ⟨w, hw, ?_⟩
    have hf := hfaith w hw
    rw [hf.2.2.2, nat_xor_eq, Nat.testBit_xor, hf.1 i hi, hf.2.1 i hi]
    cases h1 : bit (pairs.getD i (0, 0)).1 w.val <;> cases h2 : bit (pairs.getD i (0, 0)).2 w.val <;>
      simp_all
  · simp only [hi, decide_false, Bool.eq_false_iff]
    intro hany
    obtain ⟨w, hw, hbit⟩ := List.any_eq_true.mp hany
    have hf := hfaith w hw
    obtain ⟨h1, h2⟩ := hf.2.2.1 i (by omega)
    rw [hf.2.2.2, nat_xor_eq, Nat.testBit_xor, h1, h2] at hbit
    simp at hbit

def SymOK (mask T : Word) (sym : Word → Word) : Prop :=
  ∃ (f : Row → Row), Function.Bijective f ∧
    (∀ r : Row, bit (f r) mask = bit r mask) ∧
    (∀ w, Masked mask w → Masked mask (sym w) ∧ ∀ r : Row, bit r (sym w) = bit (f r) w) ∧
    sym T = T

theorem sym_id_ok (mask T : Word) : SymOK mask T id :=
  ⟨id, Function.bijective_id, fun _ => rfl, fun _ hw => ⟨hw, fun _ => rfl⟩, rfl⟩

def swapWord (mEq m01 m10 sh : Word) (w : Word) : Word :=
  Nat.lor (Nat.land w mEq)
    (Nat.lor (Nat.shiftRight (Nat.land w m01) sh) (Nat.shiftLeft (Nat.land w m10) sh))

def swapSpecOK (mEq m01 m10 sh : Word) (f : Row → Row) : Bool :=
  Nat.beq (Nat.land mEq fullMask) mEq &&
  Nat.beq (Nat.land m01 fullMask) m01 &&
  Nat.beq (Nat.land m10 fullMask) m10 &&
  Nat.beq (Nat.land (Nat.shiftLeft m10 sh) fullMask) (Nat.shiftLeft m10 sh) &&
  (List.finRange 256).all fun r =>
    decide (f (f r) = r) &&
    ((bit r mEq && !m01.testBit (sh + r.val) && !(decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide (f r = r)) ||
     (!bit r mEq && m01.testBit (sh + r.val) && !(decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide ((f r).val = sh + r.val)) ||
     (!bit r mEq && !m01.testBit (sh + r.val) && (decide (sh ≤ r.val) && m10.testBit (r.val - sh)) && decide ((f r).val = r.val - sh)))

theorem swapWord_spec {mEq m01 m10 sh : Word} {f : Row → Row}
    (hok : swapSpecOK mEq m01 m10 sh f = true) :
    Function.Bijective f ∧
    (∀ w, Masked fullMask (swapWord mEq m01 m10 sh w) ∧
      ∀ r : Row, bit r (swapWord mEq m01 m10 sh w) = bit (f r) w) := by
  simp only [swapSpecOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmEq, hm01⟩, hm10⟩, hmSh⟩, hall⟩ := hok
  have hbij : Function.Bijective f :=
    Function.Involutive.bijective (fun r => (hall r (List.mem_finRange r)).1)
  refine ⟨hbij, fun w => ⟨?_, ?_⟩⟩
  · apply masked_lor (masked_land_right hmEq)
    apply masked_lor
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [nat_land_eq, Nat.testBit_and]
      by_cases hk : k < 256
      · have hfm : fullMask.testBit k = true := by
          have : fullMask = 2 ^ 256 - 1 := by decide
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        simp [hfm]
      · have hfm : fullMask.testBit k = false := mask_testBit_ge (masked_self fullMask) (by omega)
        have h0 : (Nat.land w m01).testBit (sh + k) = false := by
          rw [nat_land_eq, Nat.testBit_and, mask_testBit_ge hm01 (by omega), Bool.and_false]
        rw [hfm, Bool.and_false, nat_shr_eq, Nat.testBit_shiftRight, h0]
    · apply Nat.eq_of_testBit_eq
      intro k
      rw [nat_land_eq, Nat.testBit_and]
      by_cases hk : k < 256
      · have hfm : fullMask.testBit k = true := by
          have : fullMask = 2 ^ 256 - 1 := by decide
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        simp [hfm]
      · have hfm : fullMask.testBit k = false := mask_testBit_ge (masked_self fullMask) (by omega)
        have hsh0 : (Nat.shiftLeft m10 sh).testBit k = false := mask_testBit_ge hmSh (by omega)
        have h1 : (Nat.shiftLeft (Nat.land w m10) sh).testBit k = false := by
          rw [nat_shl_eq, Nat.testBit_shiftLeft] at hsh0 ⊢
          by_cases hge : k ≥ sh
          · simp only [hge, decide_true, Bool.true_and] at hsh0 ⊢
            rw [nat_land_eq, Nat.testBit_and, hsh0, Bool.and_false]
          · simp [hge]
        rw [hfm, Bool.and_false, h1]
  · intro r
    have hr := (hall r (List.mem_finRange r)).2
    simp only [bit, swapWord, nat_lor_eq, Nat.testBit_or, nat_land_eq, Nat.testBit_and,
      nat_shr_eq, Nat.testBit_shiftRight, nat_shl_eq, Nat.testBit_shiftLeft]
    rcases hr with (⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · simp only [bit] at h1
      have h3' : (decide (r.val ≥ sh) && (w.testBit (r.val - sh) && m10.testBit (r.val - sh))) = false := by
        by_cases hge : sh ≤ r.val
        · simp only [hge, decide_true, Bool.true_and] at h3
          simp [hge, h3]
        · have : ¬ (r.val ≥ sh) := by omega
          simp [this]
      rw [h1, h2, h4]; simp [h3']
    · simp only [bit] at h1
      have h3' : (decide (r.val ≥ sh) && (w.testBit (r.val - sh) && m10.testBit (r.val - sh))) = false := by
        by_cases hge : sh ≤ r.val
        · simp only [hge, decide_true, Bool.true_and] at h3
          simp [hge, h3]
        · have : ¬ (r.val ≥ sh) := by omega
          simp [this]
      rw [h1, h2, h4]; simp [h3']
    · simp only [bit] at h1
      have h3a : sh ≤ r.val := h3.1
      have h3b : m10.testBit (r.val - sh) = true := h3.2
      have hge : r.val ≥ sh := h3a
      rw [h1, h2, h4]; simp [hge, h3b]

theorem sym_of_row {mask T : Word} {f : Row → Row} {sym : Word → Word}
    (hm : Masked fullMask mask) (hbij : Function.Bijective f)
    (hsw : ∀ w, Masked fullMask (sym w) ∧ ∀ r : Row, bit r (sym w) = bit (f r) w)
    (hmask : (List.finRange 256).all (fun r => bit (f r) mask == bit r mask) = true)
    (hT : Nat.beq (sym T) T = true) :
    SymOK mask T sym := by
  have hfM : ∀ r : Row, bit (f r) mask = bit r mask := fun r =>
    beq_iff_eq.mp (List.all_eq_true.mp hmask r (List.mem_finRange r))
  refine ⟨f, hbij, hfM, fun w hw => ⟨?_, (hsw w).2⟩, Nat.beq_eq.mp hT⟩
  apply Nat.eq_of_testBit_eq
  intro k
  rw [nat_land_eq, Nat.testBit_and]
  by_cases hk : k < 256
  · let r : Row := ⟨k, hk⟩
    have h1 : (sym w).testBit r.val = w.testBit (f r).val := (hsw w).2 r
    cases hmr : mask.testBit r.val with
    | true => simp
    | false =>
      have hmf : mask.testBit (f r).val = false := by
        have := hfM r; simp only [bit] at this; rw [this, hmr]
      rw [h1, masked_testBit_false hw hmf]; simp
  · have h0 := mask_testBit_ge (hsw w).1 (show 256 ≤ k by omega)
    rw [h0]; simp

theorem sym_comp_spec {f1 f2 : Row → Row} {s1 s2 : Word → Word}
    (h1 : Function.Bijective f1 ∧ ∀ w, Masked fullMask (s1 w) ∧ ∀ r, bit r (s1 w) = bit (f1 r) w)
    (h2 : Function.Bijective f2 ∧ ∀ w, Masked fullMask (s2 w) ∧ ∀ r, bit r (s2 w) = bit (f2 r) w) :
    Function.Bijective (fun r => f1 (f2 r)) ∧
    ∀ w, Masked fullMask (s2 (s1 w)) ∧ ∀ r, bit r (s2 (s1 w)) = bit (f1 (f2 r)) w := by
  refine ⟨h1.1.comp h2.1, fun w => ⟨(h2.2 (s1 w)).1, fun r => ?_⟩⟩
  rw [(h2.2 (s1 w)).2 r, (h1.2 w).2 (f2 r)]

theorem live_sym {mask T : Word} {sym : Word → Word} (hm : Masked fullMask mask)
    (hsym : SymOK mask T sym) {k : Nat} {S : Finset Word} (h : Live mask T k S) :
    Live mask T k (S.image sym) := by
  obtain ⟨f, hbij, hfM, hsw, hT⟩ := hsym
  have hinj : ∀ a b, Masked mask a → Masked mask b → sym a = sym b → a = b := by
    intro a b ha hb heq
    apply masked_ext hm ha hb
    intro r
    obtain ⟨q, hq⟩ := hbij.2 r
    have h1 := (hsw a ha).2 q
    have h2 := (hsw b hb).2 q
    rw [heq] at h1
    rw [← hq, ← h1, h2]
  have hzero : sym 0 = 0 := by
    apply masked_ext hm (hsw 0 (masked_zero mask)).1 (masked_zero mask)
    intro r; rw [(hsw 0 (masked_zero mask)).2 r]; simp [bit]
  have hmask : sym mask = mask := by
    apply masked_ext hm (hsw mask (masked_self mask)).1 (masked_self mask)
    intro r; rw [(hsw mask (masked_self mask)).2 r, hfM r]
  have hprop : ∀ a, Proper mask a → Proper mask (sym a) := by
    intro a ha
    refine ⟨(hsw a ha.1).1, ?_, ?_⟩
    · intro hz; exact ha.2.1 (hinj a 0 ha.1 (masked_zero mask) (hz.trans hzero.symm))
    · intro hma; exact ha.2.2 (hinj a mask ha.1 (masked_self mask) (hma.trans hmask.symm))
  have hbin : ∀ d a b, d < 4 → Masked mask a → Masked mask b →
      sym (binOp mask d a b) = binOp mask d (sym a) (sym b) := by
    intro d a b hd ha hb
    apply masked_ext hm (hsw _ (masked_binOp ha hb)).1 (masked_binOp (hsw a ha).1 (hsw b hb).1)
    intro r
    rw [(hsw _ (masked_binOp ha hb)).2 r]
    simp only [bit]
    rw [binOp_testBit hd ha hb (f r).val, binOp_testBit hd (hsw a ha).1 (hsw b hb).1 r.val]
    have hfm : mask.testBit (f r).val = mask.testBit r.val := hfM r
    have hsa : (sym a).testBit r.val = a.testBit (f r).val := (hsw a ha).2 r
    have hsb : (sym b).testBit r.val = b.testBit (f r).val := (hsw b hb).2 r
    rw [hfm, hsa, hsb]
  induction h using Live.ind with
  | stop hp =>
    rw [Finset.image_singleton, hT]
    exact Live.stop hp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hUm : ∀ u ∈ U, Masked mask u := fun u hu =>
      (live_proper tail u (Finset.mem_insert_of_mem hu)).1
    have hfresh : binOp mask d (sym a) (sym b) ∉ (insert a (insert b U)).image sym := by
      intro hmem
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
      have hvm : Masked mask v := by
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact ha.1
        rcases Finset.mem_insert.mp hv' with rfl | hv''
        · exact hb.1
        · exact hUm v hv''
      have hv_eq : v = binOp mask d a b := hinj v (binOp mask d a b) hvm (masked_binOp ha.1 hb.1)
        (heq.trans (hbin d a b hd ha.1 hb.1).symm)
      exact hf (hv_eq ▸ hv)
    simp only [Finset.image_insert, hbin d a b hd ha.1 hb.1] at hfresh ih ⊢
    exact Live.binary hd (hprop a ha) (hprop b hb)
      (fun e => hab (hinj a b ha.1 hb.1 e)) hfresh ih

def eraseWord (x : Word) : List Word → List Word
  | [] => []
  | w :: ws => match Nat.beq w x with | true => ws | false => w :: eraseWord x ws

theorem eraseWord_eq (x : Word) (ws : List Word) : eraseWord x ws = ws.erase x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [eraseWord, List.erase_cons]
    cases h : Nat.beq w x
    · have hne : w ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
      have h' : (w == x) = false := beq_eq_false_iff_ne.mpr hne
      simp [h', ih]
    · have h' : (w == x) = true := beq_iff_eq.mpr (Nat.beq_eq.mp h)
      simp [h']

def eraseWire (x : Word) : List Wire → List Wire
  | [] => []
  | w :: ws => match Nat.beq w.val x with | true => ws | false => w :: eraseWire x ws

theorem eraseWire_map (x : Word) (ws : List Wire) :
    (eraseWire x ws).map Wire.val = (ws.map Wire.val).erase x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [eraseWire, List.map_cons, List.erase_cons]
    cases h : Nat.beq w.val x
    · have hne : w.val ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
      have h' : (w.val == x) = false := beq_eq_false_iff_ne.mpr hne
      simp [h', ih]
    · have h' : (w.val == x) = true := beq_iff_eq.mpr (Nat.beq_eq.mp h)
      simp [h']

def childWires (ws : List Wire) (a b z : Wire) (ka kb : Bool) : List Wire :=
  z :: kept ka a (kept kb b (eraseWire b.val (eraseWire a.val ws)))

theorem childWires_map (ws : List Wire) (a b z : Wire) (ka kb : Bool) :
    (childWires ws a b z ka kb).map Wire.val =
      z.val :: kept ka a.val (kept kb b.val (((ws.map Wire.val).erase a.val).erase b.val)) := by
  simp [childWires, map_kept, eraseWire_map]

def makeWireBin (mask : Word) (d : Nat) (a b : Wire) : Wire :=
  forceNat (binOp mask d a.val b.val) fun valZ =>
    forceNat (Nat.land a.pos b.pos) fun p0 =>
      forceNat (Nat.land a.neg b.neg) fun n0 =>
        forceNat (Nat.xor p0 n0) fun sep0 =>
          let posE := match d with | 0 => p0 | 1 => Nat.lor a.pos b.pos | 2 => Nat.xor a.pos p0 | _ => Nat.xor b.pos p0
          let negE := match d with | 0 => n0 | 1 => Nat.lor a.neg b.neg | 2 => Nat.xor a.neg n0 | _ => Nat.xor b.neg n0
          let sepE := match d with | 0 => sep0 | 1 => Nat.xor a.sep (Nat.xor b.sep sep0) | 2 => Nat.xor a.sep sep0 | _ => Nat.xor b.sep sep0
          forceNat posE fun posZ =>
            forceNat negE fun negZ =>
              forceNat sepE fun sepZ =>
                ⟨valZ, posZ, negZ, sepZ⟩

theorem makeWireBin_val (mask : Word) (d : Nat) (a b : Wire) : (makeWireBin mask d a b).val = binOp mask d a.val b.val := by
  simp [makeWireBin, forceNat_eq]

theorem makeWireBin_sep (mask : Word) (d : Nat) (a b : Wire) :
    (makeWireBin mask d a b).sep =
      match d with
      | 0 => Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)
      | 1 => Nat.xor a.sep (Nat.xor b.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)))
      | 2 => Nat.xor a.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg))
      | _ => Nat.xor b.sep (Nat.xor (Nat.land a.pos b.pos) (Nat.land a.neg b.neg)) := by
  unfold makeWireBin
  simp only [forceNat_eq]

theorem makeWireBin_faithful {mask T : Word} {pairs : List (Row × Row)}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    {a b : Wire} (ha : Faithful pairs a) (hb : Faithful pairs b)
    (hma : Masked mask a.val) (hmb : Masked mask b.val) (d : Nat) (hd : d < 4) :
    Faithful pairs (makeWireBin mask d a b) := by
  have h := faithful_bin hpairs ha hb hma hmb d hd
  have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> simpa [makeWireBin, forceNat_eq] using h

def getWire (ws : List Wire) (i : Nat) : Wire := ws.getD i ⟨0, 0, 0, 0⟩

def applyTok (mask : Word) (tok : Nat) (st : Nat × List Wire × List HistStep) :
    Option (Nat × List Wire × List HistStep) :=
  let (fuel, ws, hist) := st
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let keep := Nat.mod tok 4
    let d := Nat.mod (Nat.div tok 4) 4
    let b := Nat.mod (Nat.div tok 16) 16
    let a := Nat.div tok 256
    match Nat.blt a b && Nat.blt b ws.length with
    | false => none
    | true =>
      let wa := getWire ws a
      let wb := getWire ws b
      let wz := makeWireBin mask d wa wb
      match Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws.map Wire.val) with
      | true => none
      | false =>
        let ka := Nat.beq (Nat.div keep 2) 1
        let kb := Nat.beq (Nat.mod keep 2) 1
        some (fuel', childWires ws wa wb wz ka kb, (wz.val, wa.val, wb.val) :: hist)

def applyTokVals (mask : Word) (tok : Nat) (st : Nat × List Word) : Option (Nat × List Word) :=
  let (fuel, vs) := st
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let keep := Nat.mod tok 4
    let d := Nat.mod (Nat.div tok 4) 4
    let b := Nat.mod (Nat.div tok 16) 16
    let a := Nat.div tok 256
    match Nat.blt a b && Nat.blt b vs.length with
    | false => none
    | true =>
      let va := vs.getD a 0
      let vb := vs.getD b 0
      forceNat (binOp mask d va vb) fun vz =>
        match Nat.beq vz 0 || Nat.beq vz mask || containsNat vz vs with
        | true => none
        | false =>
          let ka := Nat.beq (Nat.div keep 2) 1
          let kb := Nat.beq (Nat.mod keep 2) 1
          some (fuel', vz :: kept ka va (kept kb vb (eraseWord vb (eraseWord va vs))))

theorem applyTokVals_eq (mask : Word) (tok : Nat) (fuel : Nat) (ws : List Wire) (hist : List HistStep)
    {st' : Nat × List Wire × List HistStep}
    (h : applyTok mask tok (fuel, ws, hist) = some st') :
    applyTokVals mask tok (fuel, ws.map Wire.val) = some (st'.1, st'.2.1.map Wire.val) := by
  unfold applyTok at h
  unfold applyTokVals
  cases fuel with
  | zero => simp at h
  | succ fuel' =>
    dsimp only at h ⊢
    rw [List.length_map]
    cases hc : (Nat.blt (Nat.div tok 256) (Nat.mod (Nat.div tok 16) 16) && Nat.blt (Nat.mod (Nat.div tok 16) 16) ws.length) with
    | false => rw [hc] at h; simp at h
    | true =>
      rw [hc] at h
      have ha_lt : Nat.div tok 256 < ws.length := by
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc; omega
      have hb_lt : Nat.mod (Nat.div tok 16) 16 < ws.length := by
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.2
      have hva : (ws.map Wire.val).getD (Nat.div tok 256) 0 = (getWire ws (Nat.div tok 256)).val := by
        simp only [getWire, List.getD_eq_getElem?_getD, List.getElem?_map, ha_lt, getElem?_pos, Option.map_some, Option.getD_some]
      have hvb : (ws.map Wire.val).getD (Nat.mod (Nat.div tok 16) 16) 0 = (getWire ws (Nat.mod (Nat.div tok 16) 16)).val := by
        simp only [getWire, List.getD_eq_getElem?_getD, List.getElem?_map, hb_lt, getElem?_pos, Option.map_some, Option.getD_some]
      rw [hva, hvb, forceNat_eq, ← makeWireBin_val]
      cases hz : (Nat.beq (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val 0 ||
          Nat.beq (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val mask ||
          containsNat (makeWireBin mask (Nat.mod (Nat.div tok 4) 4) (getWire ws (Nat.div tok 256)) (getWire ws (Nat.mod (Nat.div tok 16) 16))).val (ws.map Wire.val)) with
      | true => rw [hz] at h; simp at h
      | false =>
        rw [hz] at h
        injection h with hst
        subst hst
        simp only [childWires_map, eraseWord_eq]

abbrev NodeRec := Nat × List Nat × List Nat

def traceState (mask : Word) (rootFuel : Nat) (rootWs : List Wire)
    (dag : BTree NodeRec) (fdepth : Nat) : Nat → Nat → Option (Nat × List Wire × List HistStep)
  | _, 0 => some (rootFuel, rootWs, [])
  | 0, _ + 1 => none
  | gas + 1, i + 1 =>
    let pt := (btreeGet (0, [], []) fdepth dag (Nat.add i 1)).1
    let par := Nat.div pt 4096
    let tok := Nat.mod pt 4096
    match Nat.blt par (Nat.add i 1) with
    | false => none
    | true =>
      match traceState mask rootFuel rootWs dag fdepth gas par with
      | none => none
      | some st => applyTok mask tok st

def traceVals (mask : Word) (rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) : Nat → Nat → Option (Nat × List Word)
  | _, 0 => some (rootFuel, rootVals)
  | 0, _ + 1 => none
  | gas + 1, i + 1 =>
    let pt := (btreeGet (0, [], []) fdepth dag (Nat.add i 1)).1
    let par := Nat.div pt 4096
    let tok := Nat.mod pt 4096
    match Nat.blt par (Nat.add i 1) with
    | false => none
    | true =>
      match traceVals mask rootFuel rootVals dag fdepth gas par with
      | none => none
      | some st => applyTokVals mask tok st

theorem traceVals_eq (mask : Word) (rootFuel : Nat) (rootWs : List Wire)
    (dag : BTree NodeRec) (fdepth : Nat) :
    ∀ gas i st, traceState mask rootFuel rootWs dag fdepth gas i = some st →
      traceVals mask rootFuel (rootWs.map Wire.val) dag fdepth gas i = some (st.1, st.2.1.map Wire.val) := by
  intro gas
  induction gas with
  | zero =>
    intro i st h
    cases i with
    | zero => cases h; rfl
    | succ _ => simp [traceState] at h
  | succ gas ih =>
    intro i st h
    cases i with
    | zero => cases h; rfl
    | succ i' =>
      unfold traceState at h
      unfold traceVals
      dsimp only at h ⊢
      cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) (Nat.add i' 1) with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hpar : traceState mask rootFuel rootWs dag fdepth gas (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) with
        | none => rw [hpar] at h; cases h
        | some st0 =>
          rw [hpar] at h
          rw [ih _ _ hpar]
          exact applyTokVals_eq mask _ st0.1 st0.2.1 st0.2.2 h

theorem traceState_inv {mask T : Word} {pairs : List (Row × Row)} {rootFuel : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {fdepth : Nat}
    (hpairs : ∀ p ∈ pairs, pairValid mask T p = true)
    (hrootM : ∀ w ∈ rootWs, Masked mask w.val)
    (hrootF : ∀ w ∈ rootWs, Faithful pairs w)
    (hrootNd : (rootWs.map Wire.val).Nodup) :
    ∀ gas i st, traceState mask rootFuel rootWs dag fdepth gas i = some st →
      (∀ w ∈ st.2.1, Masked mask w.val) ∧
      (∀ w ∈ st.2.1, Faithful pairs w) ∧
      (st.2.1.map Wire.val).Nodup := by
  intro gas
  induction gas with
  | zero =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨hrootM, hrootF, hrootNd⟩
    | succ _ => simp [traceState] at h
  | succ gas ih =>
    intro i st h
    cases i with
    | zero => cases h; exact ⟨hrootM, hrootF, hrootNd⟩
    | succ i' =>
      unfold traceState at h
      dsimp only at h
      cases hlt : Nat.blt (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) (Nat.add i' 1) with
      | false => rw [hlt] at h; cases h
      | true =>
        rw [hlt] at h
        cases hpar : traceState mask rootFuel rootWs dag fdepth gas (Nat.div (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096) with
        | none => rw [hpar] at h; cases h
        | some st0 =>
          rw [hpar] at h
          obtain ⟨hM, hF, hNd⟩ := ih _ _ hpar
          obtain ⟨fuel0, ws0, hist0⟩ := st0
          unfold applyTok at h
          cases fuel0 with
          | zero => simp at h
          | succ fuel' =>
            dsimp only at h
            let tok := Nat.mod (btreeGet (0, [], []) fdepth dag (Nat.add i' 1)).1 4096
            cases hc : (Nat.blt (Nat.div tok 256) (Nat.mod (Nat.div tok 16) 16) && Nat.blt (Nat.mod (Nat.div tok 16) 16) ws0.length) with
            | false => simp only [tok] at hc; rw [hc] at h; simp at h
            | true =>
              simp only [tok] at hc
              rw [hc] at h
              have hab : Nat.div tok 256 < Nat.mod (Nat.div tok 16) 16 := by
                simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.1
              have hb_lt : Nat.mod (Nat.div tok 16) 16 < ws0.length := by
                simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.2
              have ha_lt : Nat.div tok 256 < ws0.length := Nat.lt_trans hab hb_lt
              let wa := getWire ws0 (Nat.div tok 256)
              let wb := getWire ws0 (Nat.mod (Nat.div tok 16) 16)
              let d := Nat.mod (Nat.div tok 4) 4
              have hd : d < 4 := Nat.mod_lt _ (by omega)
              have ham : wa ∈ ws0 := by
                simp only [wa, getWire, List.getD_eq_getElem?_getD, ha_lt, getElem?_pos, Option.getD_some]
                exact List.getElem_mem ha_lt
              have hbm : wb ∈ ws0 := by
                simp only [wb, getWire, List.getD_eq_getElem?_getD, hb_lt, getElem?_pos, Option.getD_some]
                exact List.getElem_mem hb_lt
              let wz := makeWireBin mask d wa wb
              cases hz : (Nat.beq wz.val 0 || Nat.beq wz.val mask || containsNat wz.val (ws0.map Wire.val)) with
              | true => simp only [wa, wb, d, wz] at hz; rw [hz] at h; simp at h
              | false =>
                simp only [wa, wb, d, wz] at hz
                rw [hz] at h
                injection h with hst
                subst hst
                have hfresh : wz.val ∉ ws0.map Wire.val := by
                  simp only [Bool.or_eq_false_iff] at hz
                  intro hm
                  have hc' := (containsNat_iff _ _).mpr hm
                  simp only [wa, wb, d, wz] at hc'
                  rw [hz.2] at hc'
                  exact Bool.noConfusion hc'
                have hne : wa.val ≠ wb.val := by
                  have ha_m : Nat.div tok 256 < (ws0.map Wire.val).length := by rw [List.length_map]; exact ha_lt
                  have hb_m : Nat.mod (Nat.div tok 16) 16 < (ws0.map Wire.val).length := by rw [List.length_map]; exact hb_lt
                  have ea : wa.val = (ws0.map Wire.val)[Nat.div tok 256]'ha_m := by
                    simp only [wa, getWire, List.getD_eq_getElem?_getD, ha_lt, getElem?_pos, Option.getD_some, List.getElem_map]
                  have eb : wb.val = (ws0.map Wire.val)[Nat.mod (Nat.div tok 16) 16]'hb_m := by
                    simp only [wb, getWire, List.getD_eq_getElem?_getD, hb_lt, getElem?_pos, Option.getD_some, List.getElem_map]
                  rw [ea, eb]
                  intro e
                  exact Nat.ne_of_lt hab ((List.Nodup.getElem_inj_iff hNd).mp e)
                have hsubW : ∀ w ∈ childWires ws0 wa wb wz (Nat.beq (Nat.div (Nat.mod tok 4) 2) 1) (Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1),
                    w = wz ∨ w ∈ ws0 := by
                  intro w hw
                  rcases List.mem_cons.mp hw with rfl | hw'
                  · exact Or.inl rfl
                  · right
                    rcases mem_kept hw' with rfl | hw''
                    · exact ham
                    rcases mem_kept hw'' with rfl | hw'''
                    · exact hbm
                    · have hsub1 : ∀ x (l : List Wire), ∀ u ∈ eraseWire x l, u ∈ l := by
                        intro x l; induction l with
                        | nil => intro u hu; cases hu
                        | cons y ys ihy =>
                          intro u hu; simp only [eraseWire] at hu
                          cases hbeq : Nat.beq y.val x
                          · rw [hbeq] at hu
                            rcases List.mem_cons.mp hu with rfl | hu'
                            · exact List.mem_cons_self
                            · exact List.mem_cons_of_mem _ (ihy u hu')
                          · rw [hbeq] at hu
                            exact List.mem_cons_of_mem _ hu
                      exact hsub1 _ _ _ (hsub1 _ _ _ hw''')
                refine ⟨?_, ?_, ?_⟩
                · intro w hw
                  rcases hsubW w hw with rfl | hmem
                  · rw [makeWireBin_val]; exact masked_binOp (hM wa ham) (hM wb hbm)
                  · exact hM w hmem
                · intro w hw
                  rcases hsubW w hw with rfl | hmem
                  · exact makeWireBin_faithful hpairs (hF wa ham) (hF wb hbm) (hM wa ham) (hM wb hbm) d hd
                  · exact hF w hmem
                · rw [childWires_map]
                  let vs0 := ws0.map Wire.val
                  let rest := (vs0.erase wa.val).erase wb.val
                  have hrnd : rest.Nodup := (hNd.erase _).erase _
                  have har : wa.val ∉ rest := fun hm => hNd.not_mem_erase (List.mem_of_mem_erase hm)
                  have hbr : wb.val ∉ rest := (hNd.erase _).not_mem_erase
                  have hamid : wa.val ∉ kept (Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1) wb.val rest := by
                    cases Nat.beq (Nat.mod (Nat.mod tok 4) 2) 1 <;> simp [kept, har, hne]
                  refine List.nodup_cons.mpr ⟨?_, kept_nd _ wa.val _ (kept_nd _ wb.val _ hrnd hbr) hamid⟩
                  intro hm
                  rcases mem_kept hm with hza | hm'
                  · exact hfresh (by rw [hza]; exact List.mem_map_of_mem ham)
                  rcases mem_kept hm' with hzb | hm''
                  · exact hfresh (by rw [hzb]; exact List.mem_map_of_mem hbm)
                  · exact hfresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm''))

def sameSet (xs ys : List Word) : Bool :=
  xs.all (fun x => containsNat x ys) && ys.all (fun y => containsNat y xs)

theorem sameSet_sound {xs ys : List Word} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, containsNat_iff] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def withSuffix : List Wire → List (Wire × Nat) × Nat
  | [] => ([], 0)
  | w :: ws =>
    let (tail, s) := withSuffix ws
    forceNat (Nat.lor w.sep s) fun s' => ((w, s) :: tail, s')

theorem withSuffix_len (ws : List Wire) : (withSuffix ws).1.length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [withSuffix, forceNat_eq, ih]

theorem withSuffix_fold (ws : List Wire) :
    (withSuffix ws).2 = ws.foldr (fun w acc => Nat.lor w.sep acc) 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [withSuffix, forceNat_eq, ih]

theorem withSuffix_spec (ws : List Wire) :
    ∀ i < ws.length,
      ((withSuffix ws).1.getD i (⟨0,0,0,0⟩, 0)).1 = ws.getD i ⟨0,0,0,0⟩ ∧
      ((withSuffix ws).1.getD i (⟨0,0,0,0⟩, 0)).2 = (ws.drop (i + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
  induction ws with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
    intro i hi
    simp only [withSuffix, forceNat_eq]
    cases i with
    | zero => simp [withSuffix_fold]
    | succ i' =>
      have hi' : i' < ws.length := by simp at hi; omega
      simpa using ih i' hi'

def findLink (tok : Nat) : List Nat → Option (Nat × Bool)
  | [] => none
  | e :: rest =>
    match Nat.beq (Nat.div e 8192) tok with
    | true => some (Nat.mod (Nat.div e 2) 4096, Nat.beq (Nat.mod e 2) 1)
    | false => findLink tok rest

def materializeList (cutTree : BTree CutSpec) (cdepth : Nat) (ws : List Word) (hist : List HistStep) :
    List Nat → List MatPool
  | [] => []
  | ci :: cis =>
    match materializeCut (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci) ws hist with
    | none => materializeList cutTree cdepth ws hist cis
    | some mp => mp :: materializeList cutTree cdepth ws hist cis

theorem materializeList_sound {mask : Word} {raw : List Word} {T : Word}
    {cutTree : BTree CutSpec} {cdepth : Nat}
    (ws : List Word) (hist : List HistStep) (cis : List Nat)
    (hvalid : ∀ ci ∈ cis, ValidCut mask raw T (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci)) :
    ∀ p ∈ materializeList cutTree cdepth ws hist cis, ValidPool mask raw T ws p := by
  induction cis with
  | nil => intro p hp; cases hp
  | cons ci cis ih =>
    intro p hp
    unfold materializeList at hp
    cases hm : materializeCut (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci) ws hist with
    | none =>
      rw [hm] at hp
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) p hp
    | some mp =>
      rw [hm] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact materializeCut_sound (hvalid ci (List.mem_cons_self)) hm
      · exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) p hp'

def checkChild (mask goal : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List MatPool)
    (childFuel : Nat) (ws : List Word) (idxA idxB d : Nat) (ka kb : Bool) (va vb vz : Word) : Bool :=
  match childFuel with
  | 0 => !Nat.beq vz goal
  | _ =>
    let keep := match ka with | true => (match kb with | true => 3 | false => 2) | false => (match kb with | true => 1 | false => 0)
    let tok := Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4) keep
    match findLink tok nlinks with
    | some (tid, isSym) =>
      match Nat.blt tid count with
      | false => false
      | true =>
        match traceVals mask rootFuel rootVals dag fdepth (Nat.add rootFuel 1) tid with
        | none => false
        | some (tf, tvs) =>
          match Nat.beq tf childFuel with
          | false => false
          | true =>
            let rest := kept ka va (kept kb vb (eraseWord vb (eraseWord va ws)))
            let cvals := vz :: rest
            let mapped := match isSym with | false => cvals | true => cvals.map sym
            sameSet mapped tvs
    | none =>
      pools.any (fun p => scalarPoolCut p childFuel idxA idxB ka kb vz)

def checkOp (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List MatPool)
    (childFuel : Nat) (can1 can2 : Bool) (ws : List Word) (idxA idxB : Nat)
    (va vb : Word) (otherSep sepA0 sepB0 sepAB0 sepZ : Nat) (d : Nat) : Bool :=
  let ok00 := Nat.beq (Nat.lor otherSep sepZ) allSep
  let ok01 := match can1 with | false => false | true => Nat.beq (Nat.lor sepB0 sepZ) allSep
  let ok10 := match can1 with | false => false | true => Nat.beq (Nat.lor sepA0 sepZ) allSep
  let ok11 := match can2 with | false => false | true => Nat.beq (Nat.lor sepAB0 sepZ) allSep
  let anyOk := match ok00 with | true => true | false => match ok01 with | true => true | false => match ok10 with | true => true | false => ok11
  match anyOk with
  | false => true
  | true =>
    forceNat (binOp mask d va vb) fun vz =>
      match Nat.beq vz 0 || Nat.beq vz mask || containsNat vz ws with
      | true => true
      | false =>
        (match ok00 with | false => true | true => checkChild mask goal sym count rootFuel rootVals dag fdepth nlinks pools childFuel ws idxA idxB d false false va vb vz) &&
        (match ok01 with | false => true | true => checkChild mask goal sym count rootFuel rootVals dag fdepth nlinks pools childFuel ws idxA idxB d false true va vb vz) &&
        (match ok10 with | false => true | true => checkChild mask goal sym count rootFuel rootVals dag fdepth nlinks pools childFuel ws idxA idxB d true false va vb vz) &&
        (match ok11 with | false => true | true => checkChild mask goal sym count rootFuel rootVals dag fdepth nlinks pools childFuel ws idxA idxB d true true va vb vz)

def checkLoopB (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List MatPool)
    (childFuel : Nat) (can1 can2 : Bool) (ws : List Word) (idxA : Nat) (wa : Wire)
    (preMid : Nat) (idxB : Nat) : List (Wire × Nat) → Bool
  | [] => true
  | (wb, sufB) :: bs =>
    forceNat (Nat.lor preMid sufB) fun otherSep =>
      forceNat (match can1 with | false => 0 | true => Nat.lor otherSep wa.sep) fun sepA0 =>
        forceNat (match can1 with | false => 0 | true => Nat.lor otherSep wb.sep) fun sepB0 =>
          forceNat (match can2 with | false => 0 | true => Nat.lor sepA0 wb.sep) fun sepAB0 =>
            forceNat (Nat.land wa.pos wb.pos) fun p0 =>
              forceNat (Nat.land wa.neg wb.neg) fun n0 =>
                forceNat (Nat.xor p0 n0) fun sep0 =>
                  forceNat (Nat.xor wa.sep sep0) fun sep2 =>
                    forceNat (Nat.xor wb.sep sep0) fun sep3 =>
                      forceNat (Nat.xor wa.sep sep3) fun sep1 =>
                        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep0 0 &&
                        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep1 1 &&
                        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep2 2 &&
                        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA idxB wa.val wb.val otherSep sepA0 sepB0 sepAB0 sep3 3 &&
                        forceNat (Nat.lor preMid wb.sep) fun preMid' =>
                          checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA wa preMid' (Nat.add idxB 1) bs

def checkLoopA (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat) (rootVals : List Word)
    (dag : BTree NodeRec) (fdepth : Nat) (nlinks : List Nat) (pools : List MatPool)
    (childFuel : Nat) (can1 can2 : Bool) (ws : List Word)
    (pre : Nat) (idxA : Nat) : List (Wire × Nat) → Bool
  | [] => true
  | (wa, _) :: tail =>
    checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA wa pre (Nat.add idxA 1) tail &&
    forceNat (Nat.lor pre wa.sep) fun pre' =>
      checkLoopA mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws pre' (Nat.add idxA 1) tail

def checkNode (mask goal allSep : Word) (sym : Word → Word) (count rootFuel : Nat)
    (rootWs : List Wire) (dag : BTree NodeRec) (fdepth : Nat)
    (cutTree : BTree CutSpec) (cdepth : Nat) (i : Nat) : Bool :=
  match traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) i with
  | none => false
  | some (fuel, ws, hist) =>
    let vals := ws.map Wire.val
    match containsNat goal vals with
    | true => false
    | false =>
      match fuel with
      | 0 => true
      | childFuel + 1 =>
        let wsLen := ws.length
        match Nat.ble wsLen (Nat.add childFuel 2) with
        | false => true
        | true =>
          let nd := btreeGet (0, [], []) fdepth dag i
          let pools := materializeList cutTree cdepth vals hist nd.2.1
          match pools.any (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) with
          | true => true
          | false =>
            let can1 := Nat.ble wsLen (Nat.add childFuel 1)
            let can2 := Nat.ble (Nat.add wsLen 1) (Nat.add childFuel 1)
            let (wsSuf, _) := withSuffix ws
            checkLoopA mask goal allSep sym count rootFuel (rootWs.map Wire.val) dag fdepth nd.2.2 pools childFuel can1 can2 vals 0 0 wsSuf

theorem foldr_or_erase_two (ws : List Wire) (idxA idxB : Nat) (ha : idxA < ws.length)
    (hb : idxB < ws.length) (hab : idxA < idxB) :
    let wa := ws.getD idxA ⟨0,0,0,0⟩
    let wb := ws.getD idxB ⟨0,0,0,0⟩
    let pre := (ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0
    let mid := ((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0
    let suf := (ws.drop (idxB + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0
    ∀ (ka kb : Bool), (ws.map Wire.val).Nodup →
      (childWires ws wa wb z ka kb).foldr (fun w acc => Nat.lor w.sep acc) 0 =
        Nat.lor (Nat.lor (Nat.lor (Nat.lor pre mid) suf)
          (Nat.lor (if ka then wa.sep else 0) (if kb then wb.sep else 0))) z.sep := by
  intro wa wb pre mid suf ka kb hnd
  have hfold_bit : ∀ (l : List Wire) (k : Nat),
      (l.foldr (fun w acc => Nat.lor w.sep acc) 0).testBit k = l.any (fun w => w.sep.testBit k) := by
    intro l k; induction l with
    | nil => simp
    | cons w ws ih =>
      change (Nat.lor w.sep (ws.foldr (fun w acc => Nat.lor w.sep acc) 0)).testBit k = _
      rw [nat_lor_eq, Nat.testBit_or, ih, List.any_cons]
  have hmem_erase : ∀ (l : List Wire) (x : Word), (l.map Wire.val).Nodup → ∀ w, w ∈ eraseWire x l ↔ w ∈ l ∧ w.val ≠ x := by
    intro l x
    induction l with
    | nil => intro _ w; simp [eraseWire]
    | cons u us ih =>
      intro hnd' w
      simp only [List.map_cons, List.nodup_cons] at hnd'
      simp only [eraseWire]
      cases h : Nat.beq u.val x with
      | true =>
        have hux : u.val = x := Nat.beq_eq.mp h
        constructor
        · intro hw
          refine ⟨List.mem_cons_of_mem _ hw, ?_⟩
          intro hwx
          exact hnd'.1 (hux ▸ hwx ▸ List.mem_map_of_mem hw)
        · rintro ⟨hw, hne⟩
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact absurd hux hne
          · exact hw'
      | false =>
        have hux : u.val ≠ x := fun e => by rw [Nat.beq_eq.mpr e] at h; exact Bool.noConfusion h
        rw [List.mem_cons, List.mem_cons, ih hnd'.2]
        constructor
        · rintro (rfl | ⟨hw, hne⟩)
          · exact ⟨Or.inl rfl, hux⟩
          · exact ⟨Or.inr hw, hne⟩
        · rintro ⟨rfl | hw, hne⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hw, hne⟩
  have hwa_eq : wa = ws[idxA] := by
    simp only [wa, List.getD_eq_getElem?_getD, ha, getElem?_pos, Option.getD_some]
  have hwb_eq : wb = ws[idxB] := by
    simp only [wb, List.getD_eq_getElem?_getD, hb, getElem?_pos, Option.getD_some]
  have hsplit : ws = ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1) := by
    have h1 : ws = ws.take idxA ++ ws[idxA] :: ws.drop (idxA + 1) := by
      have := (List.take_append_drop idxA ws).symm
      rwa [List.drop_eq_getElem_cons ha] at this
    have hb' : idxB - idxA - 1 < (ws.drop (idxA + 1)).length := by simp; omega
    have h2 : ws.drop (idxA + 1) = (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++
        (ws.drop (idxA + 1))[idxB - idxA - 1] :: (ws.drop (idxA + 1)).drop (idxB - idxA - 1 + 1) := by
      have := (List.take_append_drop (idxB - idxA - 1) (ws.drop (idxA + 1))).symm
      rwa [List.drop_eq_getElem_cons hb'] at this
    have hidx : (ws.drop (idxA + 1))[idxB - idxA - 1] = wb := by
      simp only [List.getElem_drop, hwb_eq]; congr 1; omega
    have hdrop2 : (ws.drop (idxA + 1)).drop (idxB - idxA - 1 + 1) = ws.drop (idxB + 1) := by
      rw [List.drop_drop]; congr 1; omega
    rw [hidx, hdrop2] at h2
    rw [← hwa_eq] at h1
    calc ws = ws.take idxA ++ wa :: ws.drop (idxA + 1) := h1
      _ = ws.take idxA ++ wa :: ((ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ wb :: ws.drop (idxB + 1)) :=
        congrArg (fun t => ws.take idxA ++ wa :: t) h2
      _ = ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1) := by
        simp [List.append_assoc]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [hfold_bit]
  dsimp only [pre, mid, suf]
  rw [nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or,
      nat_lor_eq, Nat.testBit_or, nat_lor_eq, Nat.testBit_or, hfold_bit, hfold_bit, hfold_bit]
  have hrest_mem : ∀ w, w ∈ eraseWire wb.val (eraseWire wa.val ws) ↔
      w ∈ ws.take idxA ∨ w ∈ (ws.drop (idxA + 1)).take (idxB - idxA - 1) ∨ w ∈ ws.drop (idxB + 1) := by
    intro w
    have hnd1 : ((eraseWire wa.val ws).map Wire.val).Nodup := by
      rw [eraseWire_map]; exact hnd.erase _
    rw [hmem_erase _ _ hnd1, hmem_erase _ _ hnd]
    constructor
    · rintro ⟨⟨hw, hna⟩, hnb⟩
      rw [hsplit] at hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with (((h1 | rfl) | h2) | rfl) | h3
      · exact Or.inl h1
      · exact absurd rfl hna
      · exact Or.inr (Or.inl h2)
      · exact absurd rfl hnb
      · exact Or.inr (Or.inr h3)
    · intro hor
      have hw : w ∈ ws := by
        rw [hsplit]; simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
        · exact Or.inl (Or.inl (Or.inr h2))
        · exact Or.inr h3
      have hnd_split := hnd
      rw [hsplit, List.map_append, List.map_append, List.map_append, List.map_append] at hnd_split
      have hne_from : ∀ (l1 l2 : List Wire) (u : Wire),
          (l1.map Wire.val ++ u.val :: l2.map Wire.val).Nodup → ∀ v ∈ l1 ++ l2, v.val ≠ u.val := by
        intro l1 l2 u hnu v hv heq
        rw [List.nodup_append] at hnu
        rcases List.mem_append.mp hv with hv1 | hv2
        · exact hnu.2.2 _ (List.mem_map_of_mem hv1) _ (List.mem_cons_self) heq
        · exact (List.nodup_cons.mp hnu.2.1).1 (heq ▸ List.mem_map_of_mem hv2)
      refine ⟨⟨hw, ?_⟩, ?_⟩
      · have hndA : ((ws.take idxA).map Wire.val ++ wa.val :: ((ws.drop (idxA + 1)).take (idxB - idxA - 1) ++ [wb] ++ ws.drop (idxB + 1)).map Wire.val).Nodup := by
          simpa [List.map_append, List.append_assoc] using hnd_split
        apply hne_from _ _ wa hndA w
        simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl (Or.inl h2))
        · exact Or.inr (Or.inr h3)
      · have hndB : ((ws.take idxA ++ [wa] ++ (ws.drop (idxA + 1)).take (idxB - idxA - 1)).map Wire.val ++ wb.val :: (ws.drop (idxB + 1)).map Wire.val).Nodup := by
          simpa [List.map_append, List.append_assoc] using hnd_split
        apply hne_from _ _ wb hndB w
        simp only [List.mem_append]
        rcases hor with h1 | h2 | h3
        · exact Or.inl (Or.inl (Or.inl h1))
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3
  apply Bool.eq_iff_iff.mpr
  simp only [childWires, List.any_cons, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (hz | ⟨w, hw, hwk⟩)
    · exact Or.inr hz
    · left
      cases ka with
      | true =>
        simp only [kept, ite_true, List.mem_cons] at hw
        rcases hw with rfl | hw'
        · exact Or.inr (Or.inl (by simp [hwk]))
        · cases kb with
          | true =>
            simp only [kept, ite_true, List.mem_cons] at hw'
            rcases hw' with rfl | hw''
            · exact Or.inr (Or.inr (by simp [hwk]))
            · rcases (hrest_mem w).mp hw'' with h1 | h2 | h3
              · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
              · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
              · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
          | false =>
            simp only [kept, Bool.false_eq_true, ite_false] at hw'
            rcases (hrest_mem w).mp hw' with h1 | h2 | h3
            · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
            · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
      | false =>
        simp only [kept, Bool.false_eq_true, ite_false] at hw
        cases kb with
        | true =>
          simp only [kept, ite_true, List.mem_cons] at hw
          rcases hw with rfl | hw''
          · exact Or.inr (Or.inr (by simp [hwk]))
          · rcases (hrest_mem w).mp hw'' with h1 | h2 | h3
            · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
            · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
            · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
        | false =>
          simp only [kept, Bool.false_eq_true, ite_false] at hw
          rcases (hrest_mem w).mp hw with h1 | h2 | h3
          · exact Or.inl (Or.inl (Or.inl ⟨w, h1, hwk⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨w, h2, hwk⟩))
          · exact Or.inl (Or.inr ⟨w, h3, hwk⟩)
  · rintro ((((⟨w, h1, hwk⟩ | ⟨w, h2, hwk⟩) | ⟨w, h3, hwk⟩) | (hka | hkb)) | hz)
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inl h1)
      cases ka <;> cases kb <;> simp [kept, hm]
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inr (Or.inl h2))
      cases ka <;> cases kb <;> simp [kept, hm]
    · right; refine ⟨w, ?_, hwk⟩
      have hm := (hrest_mem w).mpr (Or.inr (Or.inr h3))
      cases ka <;> cases kb <;> simp [kept, hm]
    · cases ka with
      | false => simp at hka
      | true => right; exact ⟨wa, by simp [kept], by simpa using hka⟩
    · cases kb with
      | false => simp at hkb
      | true => right; exact ⟨wb, by cases ka <;> simp [kept], by simpa using hkb⟩
    · exact Or.inl hz

theorem checkLoopB_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List MatPool} {childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} {idxA : Nat} {wa : Wire} :
    ∀ (bs : List (Wire × Nat)) (preMid idxB : Nat),
      checkLoopB mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA wa preMid idxB bs = true →
      ∀ j < bs.length, ∀ d < 4,
        let wb := (bs.getD j (⟨0,0,0,0⟩, 0)).1
        let sufB := (bs.getD j (⟨0,0,0,0⟩, 0)).2
        let mid := (bs.take j).foldr (fun x acc => Nat.lor x.1.sep acc) 0
        let otherSep := Nat.lor (Nat.lor preMid mid) sufB
        let sepA0 := if can1 then Nat.lor otherSep wa.sep else 0
        let sepB0 := if can1 then Nat.lor otherSep wb.sep else 0
        let sepAB0 := if can2 then Nat.lor sepA0 wb.sep else 0
        let p0 := Nat.land wa.pos wb.pos
        let n0 := Nat.land wa.neg wb.neg
        let sep0 := Nat.xor p0 n0
        let sepZ := match d with | 0 => sep0 | 1 => Nat.xor wa.sep (Nat.xor wb.sep sep0) | 2 => Nat.xor wa.sep sep0 | _ => Nat.xor wb.sep sep0
        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA (idxB + j) wa.val wb.val otherSep sepA0 sepB0 sepAB0 sepZ d = true := by
  intro bs
  induction bs with
  | nil => intro _ _ _ j hj; simp at hj
  | cons p bs ih =>
    obtain ⟨wb0, suf0⟩ := p
    intro preMid idxB h j hj d hd
    simp only [checkLoopB, forceNat_eq, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hrest⟩ := h
    cases j with
    | zero =>
      have h4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      have h0' : Nat.lor preMid 0 = preMid := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
      have h0l : Nat.lor 0 wb0.sep = wb0.sep := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
      cases can1 <;> cases can2 <;> rcases h4 with rfl | rfl | rfl | rfl <;>
        (dsimp only at h0 h1 h2 h3 ⊢;
         simp only [List.getD_cons_zero, List.take_zero, List.foldr_nil, h0', h0l,
           Nat.add_zero, ite_true, ite_false, Bool.false_eq_true] at h0 h1 h2 h3 ⊢;
         first | exact h0 | exact h1 | exact h2 | exact h3)
    | succ j' =>
      have hj' : j' < bs.length := by simp at hj; omega
      have hrec := ih (Nat.lor preMid wb0.sep) (Nat.add idxB 1) hrest j' hj' d hd
      have hidx : idxB + (j' + 1) = Nat.add idxB 1 + j' := by simp only [nat_add_eq]; omega
      have hlor : Nat.lor (Nat.lor preMid wb0.sep) ((bs.take j').foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
          Nat.lor preMid (Nat.lor wb0.sep ((bs.take j').foldr (fun x acc => Nat.lor x.1.sep acc) 0)) := by
        apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
      dsimp only at hrec ⊢
      simp only [List.getD_cons_succ, List.take_succ_cons, List.foldr_cons]
      rw [hidx, ← hlor]
      exact hrec

theorem checkLoopA_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List MatPool} {childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} :
    ∀ (xs : List (Wire × Nat)) (pre idxA : Nat),
      checkLoopA mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws pre idxA xs = true →
      ∀ i j, i < j → j < xs.length → ∀ d < 4,
        let wa := (xs.getD i (⟨0,0,0,0⟩, 0)).1
        let wb := (xs.getD j (⟨0,0,0,0⟩, 0)).1
        let sufB := (xs.getD j (⟨0,0,0,0⟩, 0)).2
        let preI := Nat.lor pre ((xs.take i).foldr (fun x acc => Nat.lor x.1.sep acc) 0)
        let mid := ((xs.drop (i + 1)).take (j - i - 1)).foldr (fun x acc => Nat.lor x.1.sep acc) 0
        let otherSep := Nat.lor (Nat.lor preI mid) sufB
        let sepA0 := if can1 then Nat.lor otherSep wa.sep else 0
        let sepB0 := if can1 then Nat.lor otherSep wb.sep else 0
        let sepAB0 := if can2 then Nat.lor sepA0 wb.sep else 0
        let p0 := Nat.land wa.pos wb.pos
        let n0 := Nat.land wa.neg wb.neg
        let sep0 := Nat.xor p0 n0
        let sepZ := match d with | 0 => sep0 | 1 => Nat.xor wa.sep (Nat.xor wb.sep sep0) | 2 => Nat.xor wa.sep sep0 | _ => Nat.xor wb.sep sep0
        checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws (idxA + i) (idxA + j) wa.val wb.val otherSep sepA0 sepB0 sepAB0 sepZ d = true := by
  intro xs
  induction xs with
  | nil => intro _ _ _ i j _ hj; simp at hj
  | cons p xs ih =>
    obtain ⟨wa0, _⟩ := p
    intro pre idxA h i j hij hj d hd
    simp only [checkLoopA, forceNat_eq, Bool.and_eq_true] at h
    obtain ⟨hB, hA⟩ := h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < xs.length := by simp at hj; omega
        have h0' : Nat.lor pre 0 = pre := by
          apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or]
        have hstep : idxA + (j' + 1) = Nat.add idxA 1 + j' := by simp only [nat_add_eq]; omega
        simpa [h0', hstep] using checkLoopB_at xs pre (Nat.add idxA 1) hB j' hj' d hd
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hij' : i' < j' := by omega
        have hj' : j' < xs.length := by simp at hj; omega
        have hlor : Nat.lor (Nat.lor pre wa0.sep) ((xs.take i').foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
            Nat.lor pre (Nat.lor wa0.sep ((xs.take i').foldr (fun x acc => Nat.lor x.1.sep acc) 0)) := by
          apply Nat.eq_of_testBit_eq; intro k; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
        have hi_eq : idxA + (i' + 1) = Nat.add idxA 1 + i' := by simp only [nat_add_eq]; omega
        have hj_eq : idxA + (j' + 1) = Nat.add idxA 1 + j' := by simp only [nat_add_eq]; omega
        have hsub : j' + 1 - (i' + 1) - 1 = j' - i' - 1 := by omega
        have hrec := ih (Nat.lor pre wa0.sep) (Nat.add idxA 1) hA i' j' hij' hj' d hd
        dsimp only at hrec ⊢
        simp only [List.getD_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.foldr_cons]
        rw [hi_eq, hj_eq, hsub, ← hlor]
        exact hrec

theorem restoreSet (U : Finset Word) (a b : Word) (hab : a ≠ b) :
    (if decide (a ∈ U) = true then insert a (if decide (b ∈ U) = true then insert b (((insert a (insert b U)).erase a).erase b) else ((insert a (insert b U)).erase a).erase b)
     else (if decide (b ∈ U) = true then insert b (((insert a (insert b U)).erase a).erase b) else ((insert a (insert b U)).erase a).erase b)) = U := by
  ext u
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
  · simp only [ha, hb, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true,
      Finset.mem_insert, Finset.mem_erase]
    by_cases hua : u = a
    · subst hua; simp [hab, ha]
    · by_cases hub : u = b
      · subst hub; simp [Ne.symm hab, hb]
      · simp [hua, hub]

theorem checkOp_at {mask goal allSep : Word} {sym : Word → Word} {count rootFuel : Nat}
    {rootVals : List Word} {dag : BTree NodeRec} {fdepth : Nat}
    {nlinks : List Nat} {pools : List MatPool} {childFuel : Nat} {can1 can2 : Bool}
    {ws : List Word} {idxA idxB d : Nat} {va vb : Word}
    {otherSep sepA0 sepB0 sepAB0 sepZ : Nat}
    (hop : checkOp mask goal allSep sym count rootFuel rootVals dag fdepth nlinks pools childFuel can1 can2 ws idxA idxB va vb otherSep sepA0 sepB0 sepAB0 sepZ d = true)
    (h1 : binOp mask d va vb ≠ 0) (h2 : binOp mask d va vb ≠ mask) (h3 : binOp mask d va vb ∉ ws)
    (ka kb : Bool)
    (hcan1 : (ka = true ∨ kb = true) → can1 = true)
    (hcan2 : (ka = true ∧ kb = true) → can2 = true)
    (hsep : (if ka then (if kb then Nat.lor sepAB0 sepZ else Nat.lor sepA0 sepZ)
             else (if kb then Nat.lor sepB0 sepZ else Nat.lor otherSep sepZ)) = allSep) :
    checkChild mask goal sym count rootFuel rootVals dag fdepth nlinks pools childFuel ws idxA idxB d ka kb va vb (binOp mask d va vb) = true := by
  have hnot_stale : (Nat.beq (binOp mask d va vb) 0 || Nat.beq (binOp mask d va vb) mask || containsNat (binOp mask d va vb) ws) = false := by
    have hb1 : Nat.beq (binOp mask d va vb) 0 = false := by
      cases h : Nat.beq (binOp mask d va vb) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp h) h1
    have hb2 : Nat.beq (binOp mask d va vb) mask = false := by
      cases h : Nat.beq (binOp mask d va vb) mask
      · rfl
      · exact absurd (Nat.beq_eq.mp h) h2
    have hb3 : containsNat (binOp mask d va vb) ws = false := by
      cases h : containsNat (binOp mask d va vb) ws
      · rfl
      · exact absurd ((containsNat_iff _ _).mp h) h3
    simp [hb1, hb2, hb3]
  unfold checkOp at hop
  simp only [forceNat_eq] at hop
  cases ka <;> cases kb
  · have hok : Nat.beq (Nat.lor otherSep sepZ) allSep = true := Nat.beq_eq.mpr hsep
    simp only [hok, hnot_stale, Bool.and_eq_true] at hop
    exact hop.1.1.1
  · have hc1 := hcan1 (Or.inr rfl)
    have hok : Nat.beq (Nat.lor sepB0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
    simp only [hc1, hok, hnot_stale] at hop
    cases h0 : Nat.beq (Nat.lor otherSep sepZ) allSep <;>
      simp only [h0, Bool.and_eq_true] at hop <;> exact hop.1.1.2
  · have hc1 := hcan1 (Or.inl rfl)
    have hok : Nat.beq (Nat.lor sepA0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
    simp only [hc1, hok, hnot_stale] at hop
    cases h0 : Nat.beq (Nat.lor otherSep sepZ) allSep <;>
      cases h1' : Nat.beq (Nat.lor sepB0 sepZ) allSep <;>
      simp only [h0, h1', Bool.and_eq_true] at hop <;> exact hop.1.2
  · have hc1 := hcan1 (Or.inl rfl)
    have hc2 := hcan2 ⟨rfl, rfl⟩
    have hok : Nat.beq (Nat.lor sepAB0 sepZ) allSep = true := Nat.beq_eq.mpr hsep
    simp only [hc1, hc2, hok, hnot_stale] at hop
    cases h0 : Nat.beq (Nat.lor otherSep sepZ) allSep <;>
      cases h1' : Nat.beq (Nat.lor sepB0 sepZ) allSep <;>
      cases h2' : Nat.beq (Nat.lor sepA0 sepZ) allSep <;>
      simp only [h0, h1', h2', Bool.and_eq_true] at hop <;> exact hop.2

set_option maxHeartbeats 800000 in
theorem dagAllNodes {mask goal : Word} {pairs : List (Row × Row)} {sym : Word → Word}
    {count rootFuel fdepth cdepth : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {cutTree : BTree CutSpec}
    (hm : Masked fullMask mask)
    (hpairs : ∀ p ∈ pairs, pairValid mask goal p = true)
    (hsym : SymOK mask goal sym)
    (hrootM : ∀ w ∈ rootWs, Masked mask w.val)
    (hrootF : ∀ w ∈ rootWs, Faithful pairs w)
    (hrootNd : (rootWs.map Wire.val).Nodup)
    (hcuts : ∀ i < count, ∀ ci ∈ (btreeGet (0, [], []) fdepth dag i).2.1,
      ValidCut mask (rootWs.map Wire.val) goal (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci))
    (hcheck : treeBlock 0 count (checkNode mask goal (Nat.sub (Nat.shiftLeft 1 pairs.length) 1) sym
      count rootFuel rootWs dag fdepth cutTree cdepth) = true) :
    ∀ cap i st, i < count →
      traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) i = some st →
      st.1 = cap → Impossible mask goal cap (st.2.1.map Wire.val).toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk run
    obtain ⟨fuel, ws, hist⟩ := st
    dsimp only at hcap
    subst hcap
    obtain ⟨hM, hF, hNd⟩ := traceState_inv hpairs hrootM hrootF hrootNd _ _ _ htr
    dsimp only at hM hF hNd
    have hck := treeBlock_at hcheck (Nat.zero_le i) (by omega)
    unfold checkNode at hck
    rw [htr] at hck
    dsimp only at hck
    cases hgoal : containsNat goal (ws.map Wire.val) with
    | true => simp [hgoal] at hck
    | false =>
      rw [hgoal] at hck
      have hnoGoal : goal ∉ ws.map Wire.val := fun hmem =>
        absurd ((containsNat_iff _ _).mpr hmem) (by simp [hgoal])
      cases fuel with
      | zero =>
        have hk0 : k = 0 := by omega
        subst hk0
        obtain ⟨heq, _⟩ := run
        have hmem : goal ∈ (ws.map Wire.val).toFinset := by rw [heq]; simp
        exact hnoGoal (List.mem_toFinset.mp hmem)
      | succ childFuel =>
        dsimp only at hck
        have hsz : (ws.map Wire.val).length ≤ childFuel + 2 := by
          have hs := live_size run
          rw [List.toFinset_card_of_nodup hNd] at hs
          have hkle : k ≤ childFuel + 1 := hk
          omega
        have hble : Nat.ble ws.length (Nat.add childFuel 2) = true := by
          rw [Nat.ble_eq]; rw [List.length_map] at hsz; simp only [nat_add_eq]; omega
        rw [hble] at hck
        dsimp only at hck
        have hsf : (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1).any
            (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) = false := by
          cases hself : (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1).any
              (fun p => Nat.blt (Nat.add (Nat.add childFuel 1) p.paid) (Nat.add p.bound p.wsConstCnt)) with
          | false => rfl
          | true =>
            rw [List.any_eq_true] at hself
            obtain ⟨mp, hmp_mem, hmp_cut⟩ := hself
            have hvp := materializeList_sound (ws.map Wire.val) hist _ (hcuts i hi) mp hmp_mem
            exact absurd run (selfPoolCut_sound hvp hNd hmp_cut k (by simpa [nat_add_eq] using hk))
        rw [hsf] at hck
        dsimp only at hck

        cases k with
        | zero =>
          obtain ⟨heq, _⟩ := run
          have hmem : goal ∈ (ws.map Wire.val).toFinset := by rw [heq]; simp
          exact hnoGoal (List.mem_toFinset.mp hmem)
        | succ k' =>
          obtain ⟨U, x, y, d0, hd0, hSeq, hpx, hpy, hxy, hfresh0, tail0⟩ := run
          have hx_mem : x ∈ ws.map Wire.val := List.mem_toFinset.mp (hSeq ▸ Finset.mem_insert_self _ _)
          have hy_mem : y ∈ ws.map Wire.val := List.mem_toFinset.mp (hSeq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          have hidx_ne : (ws.map Wire.val).idxOf x ≠ (ws.map Wire.val).idxOf y := by
            intro heq
            have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'(List.idxOf_lt_length_of_mem hx_mem) = x :=
              List.getElem_idxOf (List.idxOf_lt_length_of_mem hx_mem)
            have h2 : (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'(List.idxOf_lt_length_of_mem hy_mem) = y :=
              List.getElem_idxOf (List.idxOf_lt_length_of_mem hy_mem)
            have h12 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'(List.idxOf_lt_length_of_mem hx_mem) =
                (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'(List.idxOf_lt_length_of_mem hy_mem) := by
              congr 1
            exact hxy (h1.symm.trans (h12.trans h2))

          have hstep : ∃ (idxA idxB d : Nat), idxA < idxB ∧ idxB < ws.length ∧ d < 4 ∧
              let wa := ws.getD idxA ⟨0,0,0,0⟩
              let wb := ws.getD idxB ⟨0,0,0,0⟩
              wa.val ≠ wb.val ∧
              (ws.map Wire.val).toFinset = insert wa.val (insert wb.val U) ∧
              binOp mask d wa.val wb.val ∉ ws.map Wire.val ∧
              Proper mask (binOp mask d wa.val wb.val) ∧
              Live mask goal k' (insert (binOp mask d wa.val wb.val) U) := by
            have hix := List.idxOf_lt_length_of_mem hx_mem
            have hiy := List.idxOf_lt_length_of_mem hy_mem
            have hgx : (ws.getD ((ws.map Wire.val).idxOf x) ⟨0,0,0,0⟩).val = x := by
              have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf x]'hix = x := List.getElem_idxOf hix
              have hix' : (ws.map Wire.val).idxOf x < ws.length := by simpa using hix
              simp only [List.getD_eq_getElem?_getD, hix', getElem?_pos, Option.getD_some]
              rw [← List.getElem_map (f := Wire.val)]; exact h1
            have hgy : (ws.getD ((ws.map Wire.val).idxOf y) ⟨0,0,0,0⟩).val = y := by
              have h1 : (ws.map Wire.val)[(ws.map Wire.val).idxOf y]'hiy = y := List.getElem_idxOf hiy
              have hiy' : (ws.map Wire.val).idxOf y < ws.length := by simpa using hiy
              simp only [List.getD_eq_getElem?_getD, hiy', getElem?_pos, Option.getD_some]
              rw [← List.getElem_map (f := Wire.val)]; exact h1
            have hfresh' : binOp mask d0 x y ∉ ws.map Wire.val := fun hm =>
              hfresh0 (hSeq ▸ List.mem_toFinset.mpr hm)
            have hpropZ := live_proper tail0 _ (Finset.mem_insert_self _ _)
            rcases lt_or_gt_of_ne hidx_ne with hlt | hgt
            · refine ⟨(ws.map Wire.val).idxOf x, (ws.map Wire.val).idxOf y, d0, hlt, by simpa using hiy, hd0, ?_⟩
              simp only [hgx, hgy]
              exact ⟨hxy, hSeq, hfresh', hpropZ, tail0⟩
            · refine ⟨(ws.map Wire.val).idxOf y, (ws.map Wire.val).idxOf x, flipOp d0, hgt, by simpa using hix, flipOp_lt hd0, ?_⟩
              simp only [hgx, hgy, ← binOp_flip hd0]
              exact ⟨hxy.symm, by rw [hSeq, Finset.insert_comm], hfresh', hpropZ, tail0⟩
          obtain ⟨idxA, idxB, d, hab, hb, hd, hne, hSeq', hfresh, hpropZ, tail⟩ := hstep
          have ha : idxA < ws.length := by omega
          let wa := ws.getD idxA ⟨0,0,0,0⟩
          let wb := ws.getD idxB ⟨0,0,0,0⟩
          let wz := makeWireBin mask d wa wb
          let ka := decide (wa.val ∈ U)
          let kb := decide (wb.val ∈ U)
          let child := childWires ws wa wb wz ka kb
          have hchildSet : (child.map Wire.val).toFinset = insert (binOp mask d wa.val wb.val) U := by
            rw [childWires_map, makeWireBin_val]
            simp only [List.toFinset_cons, kept_fin]
            have he1 : ((ws.map Wire.val).erase wa.val).toFinset = (ws.map Wire.val).toFinset.erase wa.val := by
              ext u; simp [hNd.mem_erase_iff]
            have he2 : (((ws.map Wire.val).erase wa.val).erase wb.val).toFinset =
                ((ws.map Wire.val).toFinset.erase wa.val).erase wb.val := by
              ext u
              rw [List.mem_toFinset, (hNd.erase _).mem_erase_iff, Finset.mem_erase, ← List.mem_toFinset, he1]
            rw [he2, hSeq']
            exact congrArg (insert (binOp mask d wa.val wb.val)) (restoreSet U wa.val wb.val hne)
          have hwa_m : wa ∈ ws := by
            simp only [wa, List.getD_eq_getElem?_getD, ha, getElem?_pos, Option.getD_some]
            exact List.getElem_mem ha
          have hwb_m : wb ∈ ws := by
            simp only [wb, List.getD_eq_getElem?_getD, hb, getElem?_pos, Option.getD_some]
            exact List.getElem_mem hb
          have hchildLen : child.length ≤ childFuel + 1 := by
            have hsz' := live_size tail
            rw [← hchildSet] at hsz'
            have hndC : (child.map Wire.val).Nodup := by
              rw [childWires_map, makeWireBin_val]
              let rest := ((ws.map Wire.val).erase wa.val).erase wb.val
              have hrnd : rest.Nodup := (hNd.erase _).erase _
              have har : wa.val ∉ rest := fun hm => hNd.not_mem_erase (List.mem_of_mem_erase hm)
              have hbr : wb.val ∉ rest := (hNd.erase _).not_mem_erase
              have hamid : wa.val ∉ kept kb wb.val rest := by
                cases kb
                · simp only [kept, Bool.false_eq_true, ite_false]; exact har
                · simp only [kept, ite_true, List.mem_cons, not_or]; exact ⟨hne, har⟩
              refine List.nodup_cons.mpr ⟨?_, kept_nd ka wa.val _ (kept_nd kb wb.val _ hrnd hbr) hamid⟩
              intro hm
              rcases mem_kept hm with hza | hm'
              · exact hfresh (by rw [hza]; exact List.mem_map_of_mem hwa_m)
              rcases mem_kept hm' with hzb | hm''
              · exact hfresh (by rw [hzb]; exact List.mem_map_of_mem hwb_m)
              · exact hfresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm''))
            rw [List.toFinset_card_of_nodup hndC, List.length_map] at hsz'
            omega
          have hclen_eq : child.length = ws.length - 1 + (if ka then 1 else 0) + (if kb then 1 else 0) := by
            have hwa_mv : wa.val ∈ ws.map Wire.val := List.mem_map_of_mem hwa_m
            have hwb_mv : wb.val ∈ (ws.map Wire.val).erase wa.val :=
              (List.mem_erase_of_ne hne.symm).mpr (List.mem_map_of_mem hwb_m)
            have hl : (child.map Wire.val).length = child.length := List.length_map _
            rw [← hl, childWires_map]
            have h1 := List.length_erase_of_mem hwa_mv
            have h2 := List.length_erase_of_mem hwb_mv
            have hws2 : 2 ≤ ws.length := by omega
            cases ka <;> cases kb <;> simp only [kept, List.length_cons, List.length_map, ite_true, ite_false, Bool.false_eq_true, h1, h2] at h1 h2 ⊢ <;> omega

          have hchildFaith : ∀ w ∈ child, Faithful pairs w := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact makeWireBin_faithful hpairs (hF wa hwa_m) (hF wb hwb_m) (hM wa hwa_m) (hM wb hwb_m) d hd
            rcases mem_kept hw' with rfl | hw''
            · exact hF wa hwa_m
            rcases mem_kept hw'' with rfl | hw'''
            · exact hF wb hwb_m
            · have hsub1 : ∀ x (l : List Wire), ∀ u ∈ eraseWire x l, u ∈ l := by
                intro x l; induction l with
                | nil => intro u hu; cases hu
                | cons y ys ihy =>
                  intro u hu; simp only [eraseWire] at hu
                  cases hbeq : Nat.beq y.val x
                  · rw [hbeq] at hu
                    rcases List.mem_cons.mp hu with rfl | hu'
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem _ (ihy u hu')
                  · rw [hbeq] at hu
                    exact List.mem_cons_of_mem _ hu
              exact hF w (hsub1 _ _ _ (hsub1 _ _ _ hw'''))
          have hsep := sep_required hpairs hchildFaith (hchildSet.symm ▸ tail)
          have hfoldEq := foldr_or_erase_two (z := wz) ws idxA idxB ha hb hab ka kb hNd

          have hop := checkLoopA_at (withSuffix ws).1 0 0 hck idxA idxB hab (by rw [withSuffix_len]; exact hb) d hd
          have hwsA := withSuffix_spec ws idxA ha
          have hwsB := withSuffix_spec ws idxB hb
          have htake_eq : ((withSuffix ws).1.take idxA).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
              (ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
            have : ∀ (l : List Wire) (m : Nat), ((withSuffix l).1.take m).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
                (l.take m).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
              intro l; induction l with
              | nil => intro m; simp [withSuffix]
              | cons u us ihu =>
                intro m; cases m with
                | zero => simp [withSuffix, forceNat_eq]
                | succ m' => simp only [withSuffix, forceNat_eq, List.take_succ_cons, List.foldr_cons, ihu m']
            exact this ws idxA
          have hmid_eq : (((withSuffix ws).1.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
              ((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
            have hmap : ∀ l : List Wire, (withSuffix l).1.map Prod.fst = l := by
              intro l
              induction l with
              | nil => rfl
              | cons u us ihu =>
                simp only [withSuffix, forceNat_eq, List.map_cons]
                exact congrArg (u :: ·) ihu
            have h1 : ∀ (l : List (Wire × Nat)), l.foldr (fun x acc => Nat.lor x.1.sep acc) 0 =
                (l.map Prod.fst).foldr (fun w acc => Nat.lor w.sep acc) 0 := by
              intro l; induction l with
              | nil => rfl
              | cons x xs ihx =>
                change Nat.lor x.1.sep (xs.foldr (fun x acc => Nat.lor x.1.sep acc) 0) =
                  Nat.lor x.1.sep ((xs.map Prod.fst).foldr (fun w acc => Nat.lor w.sep acc) 0)
                rw [ihx]
            rw [h1, List.map_take, List.map_drop, hmap ws]
          have h0lor : ∀ x, Nat.lor 0 x = x := fun x => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or]
          simp only [Nat.zero_add, hwsA.1, hwsB.1, hwsB.2, htake_eq, hmid_eq, h0lor] at hop

          have hcan1 : (ka = true ∨ kb = true) → Nat.ble ws.length (Nat.add childFuel 1) = true := by
            intro hor; rw [Nat.ble_eq]; simp only [nat_add_eq]
            rcases hor with hka | hkb
            · simp only [hka, ite_true] at hclen_eq
              cases hkb' : kb <;> simp only [hkb', ite_true, ite_false, Bool.false_eq_true] at hclen_eq <;> omega
            · simp only [hkb, ite_true] at hclen_eq
              cases hka' : ka <;> simp only [hka', ite_true, ite_false, Bool.false_eq_true] at hclen_eq <;> omega
          have hcan2 : (ka = true ∧ kb = true) → Nat.ble (Nat.add ws.length 1) (Nat.add childFuel 1) = true := by
            rintro ⟨hka, hkb⟩; rw [Nat.ble_eq]; simp only [nat_add_eq]
            simp only [hka, hkb, ite_true] at hclen_eq; omega
          have hsep_ok : Nat.lor (Nat.lor (Nat.lor (Nat.lor ((ws.take idxA).foldr (fun w acc => Nat.lor w.sep acc) 0)
                (((ws.drop (idxA + 1)).take (idxB - idxA - 1)).foldr (fun w acc => Nat.lor w.sep acc) 0))
              ((ws.drop (idxB + 1)).foldr (fun w acc => Nat.lor w.sep acc) 0))
              (Nat.lor (if ka then wa.sep else 0) (if kb then wb.sep else 0))) wz.sep =
              Nat.sub (Nat.shiftLeft 1 pairs.length) 1 := by
            rw [← hfoldEq]; exact hsep
          have hlor_comm : ∀ x y, Nat.lor x y = Nat.lor y x := fun x y => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or, Bool.or_comm]
          have hlor_assoc : ∀ x y z, Nat.lor (Nat.lor x y) z = Nat.lor x (Nat.lor y z) := fun x y z => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or, Bool.or_assoc]
          have hlor_zero : ∀ x, Nat.lor x 0 = x := fun x => by
            apply Nat.eq_of_testBit_eq; intro j; simp [nat_lor_eq, Nat.testBit_or]

          have hcc : checkChild mask goal sym count rootFuel (rootWs.map Wire.val) dag fdepth
              (btreeGet (0, [], []) fdepth dag i).2.2
              (materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1)
              childFuel (ws.map Wire.val) idxA idxB d ka kb wa.val wb.val (binOp mask d wa.val wb.val) = true := by
            have hsepZ := (makeWireBin_sep mask d wa wb).symm
            change checkOp mask goal _ sym count rootFuel (rootWs.map Wire.val) dag fdepth _ _ childFuel _ _ (ws.map Wire.val) idxA idxB wa.val wb.val _ _ _ _ _ d = true at hop
            rw [hsepZ] at hop
            apply checkOp_at hop hpropZ.2.1 hpropZ.2.2 hfresh ka kb hcan1 hcan2
            by_cases hka : ka = true <;> by_cases hkb : kb = true
            · have hc1 := hcan1 (Or.inl hka)
              have hc2 := hcan2 ⟨hka, hkb⟩
              simp only [hka, hkb, hc1, hc2, ite_true] at hsep_ok ⊢
              rw [← hlor_assoc] at hsep_ok
              exact hsep_ok
            · have hkb' : kb = false := Bool.eq_false_iff.mpr hkb
              have hc1 := hcan1 (Or.inl hka)
              simp only [hka, hkb', hc1, ite_true, ite_false, Bool.false_eq_true, hlor_zero] at hsep_ok ⊢
              exact hsep_ok
            · have hka' : ka = false := Bool.eq_false_iff.mpr hka
              have hc1 := hcan1 (Or.inr hkb)
              simp only [hka', hkb, hc1, ite_true, ite_false, Bool.false_eq_true, h0lor] at hsep_ok ⊢
              exact hsep_ok
            · have hka' : ka = false := Bool.eq_false_iff.mpr hka
              have hkb' : kb = false := Bool.eq_false_iff.mpr hkb
              simp only [hka', hkb', ite_false, Bool.false_eq_true, hlor_zero] at hsep_ok ⊢
              exact hsep_ok

          unfold checkChild at hcc
          cases childFuel with
          | zero =>
            have hk0 : k' = 0 := by omega
            subst hk0
            obtain ⟨heq, _⟩ := tail
            have hmem : goal ∈ insert (binOp mask d wa.val wb.val) U := by rw [heq]; simp
            rcases Finset.mem_insert.mp hmem with hzg | hgu
            · simp only [Bool.not_eq_true', hzg] at hcc
              exact absurd (Nat.beq_eq.mpr rfl) (by rw [hcc]; decide)
            · have hgu' : goal ∈ (ws.map Wire.val).toFinset := by
                rw [hSeq']; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hgu)
              exact hnoGoal (List.mem_toFinset.mp hgu')
          | succ cf' =>
            dsimp only [checkChild] at hcc
            cases hfl : findLink (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul idxA 16) idxB) 4) d) 4)
                (match ka with | true => (match kb with | true => 3 | false => 2) | false => (match kb with | true => 1 | false => 0)))
                (btreeGet (0, [], []) fdepth dag i).2.2 with
            | some p =>
              obtain ⟨tid, isSym⟩ := p
              rw [hfl] at hcc
              change (match Nat.blt tid count with | false => false | true => _) = true at hcc
              cases htid : Nat.blt tid count with
              | false => simp [htid] at hcc
              | true =>
                rw [htid] at hcc
                have htid_lt : tid < count := Nat.blt_eq.mp htid
                have hck_tid := treeBlock_at hcheck (Nat.zero_le tid) (by omega)
                unfold checkNode at hck_tid
                cases htr_t : traceState mask rootFuel rootWs dag fdepth (Nat.add rootFuel 1) tid with
                | none => simp [htr_t] at hck_tid
                | some stT =>
                  have htv := traceVals_eq mask rootFuel rootWs dag fdepth _ _ _ htr_t
                  rw [htv] at hcc
                  dsimp only at hcc
                  cases htf : Nat.beq stT.1 (cf' + 1) with
                  | false => simp [htf] at hcc
                  | true =>
                    rw [htf] at hcc
                    have htf_eq : stT.1 = cf' + 1 := Nat.beq_eq.mp htf
                    have himp := ih (cf' + 1) (by omega) tid stT htid_lt htr_t htf_eq
                    have hsame := sameSet_sound hcc
                    have hcv : (binOp mask d wa.val wb.val :: kept ka wa.val (kept kb wb.val (eraseWord wb.val (eraseWord wa.val (ws.map Wire.val))))) = child.map Wire.val := by
                      rw [childWires_map, makeWireBin_val, eraseWord_eq, eraseWord_eq]
                    cases isSym
                    · dsimp only at hsame
                      rw [hcv, hchildSet] at hsame
                      exact himp k' (by omega) (hsame ▸ tail)
                    · dsimp only at hsame
                      have hmapF : ∀ (l : List Word), (l.map sym).toFinset = l.toFinset.image sym := by
                        intro l; ext x; simp
                      rw [hcv, hmapF, hchildSet] at hsame
                      exact himp k' (by omega) (hsame ▸ live_sym hm hsym tail)
            | none =>
              rw [hfl] at hcc
              change ((materializeList cutTree cdepth (ws.map Wire.val) hist (btreeGet (0, [], []) fdepth dag i).2.1).any
                (fun p => scalarPoolCut p (cf' + 1) idxA idxB ka kb (binOp mask d wa.val wb.val))) = true at hcc
              rw [List.any_eq_true] at hcc
              obtain ⟨mp, hmp_mem, hmp_cut⟩ := hcc
              have hvp := materializeList_sound (ws.map Wire.val) hist _ (hcuts i hi) mp hmp_mem
              have hwa_get : (ws.map Wire.val).getD idxA 0 = wa.val := by
                simp [wa, List.getD_eq_getElem?_getD, ha]
              have hwb_get : (ws.map Wire.val).getD idxB 0 = wb.val := by
                simp [wb, List.getD_eq_getElem?_getD, hb]
              have hMvals : ∀ v ∈ ws.map Wire.val, Masked mask v := by
                intro v hv; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv; exact hM w hw
              rw [← hwa_get, ← hwb_get] at hfresh hmp_cut
              have himp := scalarPoolCut_sound hvp hNd (by simpa using ha) (by simpa using hb) hab hd hMvals hfresh hmp_cut
              dsimp only at himp
              have heq_child : (binOp mask d ((ws.map Wire.val).getD idxA 0) ((ws.map Wire.val).getD idxB 0) ::
                  kept ka ((ws.map Wire.val).getD idxA 0) (kept kb ((ws.map Wire.val).getD idxB 0)
                    (((ws.map Wire.val).erase ((ws.map Wire.val).getD idxA 0)).erase ((ws.map Wire.val).getD idxB 0)))).toFinset =
                  insert (binOp mask d wa.val wb.val) U := by
                rw [hwa_get, hwb_get]
                rw [← makeWireBin_val (mask := mask) (d := d) (a := wa) (b := wb)]
                rw [← childWires_map ws wa wb wz ka kb]
                rw [makeWireBin_val]
                exact hchildSet
              rw [heq_child] at himp
              exact himp k' (by omega) tail

theorem lowerPoolDAG {mask goal : Word} {pairs : List (Row × Row)} {sym : Word → Word}
    {count rootFuel fdepth cdepth : Nat} {rootWs : List Wire}
    {dag : BTree NodeRec} {cutTree : BTree CutSpec}
    (hm : Masked fullMask mask) (hm0 : mask.testBit 0 = true)
    (hp : Proper mask goal) (nT : plainWord mask goal = true)
    (nR : (rootWs.map Wire.val).all (plainWord mask) = true)
    (hpairs : pairs.all (pairValid mask goal) = true)
    (hsym : SymOK mask goal sym)
    (hrootF : rootWs.all (wireMatchesPairs pairs) = true)
    (hrootNd : (rootWs.map Wire.val).Nodup)
    (hcount : 0 < count)
    (hess : ∀ a ∈ rootWs.map Wire.val, Essential mask goal (rootWs.map Wire.val) a)
    (hcuts : ∀ i < count, ∀ ci ∈ (btreeGet (0, [], []) fdepth dag i).2.1,
      ValidCut mask (rootWs.map Wire.val) goal (btreeGet ⟨0, 0, []⟩ cdepth cutTree ci))
    (hcheck : treeBlock 0 count (checkNode mask goal (Nat.sub (Nat.shiftLeft 1 pairs.length) 1) sym
      count rootFuel rootWs dag fdepth cutTree cdepth) = true) :
    LowerM mask (rootWs.map Wire.val) goal (rootFuel + 1) := by
  have hrootM : ∀ w ∈ rootWs, Masked mask w.val := by
    intro w hw
    have hp' := List.all_eq_true.mp nR w.val (List.mem_map_of_mem hw)
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at hp'
    exact hp'.1
  have hnoRun := dagAllNodes hm (fun p hp' => List.all_eq_true.mp hpairs p hp') hsym hrootM
    (fun w hw => wireMatchesPairs_sound (List.all_eq_true.mp hrootF w hw)) hrootNd hcuts hcheck
    rootFuel 0 (rootFuel, rootWs, []) hcount rfl rfl
  exact lower_impossible hm hm0 hp nT nR hess hnoRun

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def gv (w : List Word) (g : Gate) : Word :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (primeW false) fullMask
  | .or => xs.foldr (primeW true) 0
  | .not => Nat.xor fullMask (xs.headD 0)
  | _ => 0

def execute (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun l g => l ++ [gv l g]) w

theorem gv_masked {w : List Word} (hw : ∀ a ∈ w, Masked fullMask a) (g : Gate) :
    Masked fullMask (gv w g) := by
  have hget : ∀ i, Masked fullMask (w.getD i 0) := by
    intro i; simp only [List.getD_eq_getElem?_getD]
    cases h : w[i]? with
    | none => exact masked_zero fullMask
    | some a => exact hw a (List.mem_of_getElem? h)
  unfold gv
  cases g.op <;> dsimp only
  · induction g.inputs with
    | nil => exact masked_self fullMask
    | cons i is ih => exact masked_primeW false (hget i) ih
  · induction g.inputs with
    | nil => exact masked_zero fullMask
    | cons i is ih => exact masked_primeW true (hget i) ih
  · cases g.inputs with
    | nil => exact masked_xor (masked_zero fullMask)
    | cons i _ => exact masked_xor (hget i)
  · exact masked_zero fullMask
  · exact masked_zero fullMask

theorem execute_masked (gs : List Gate) {w : List Word} (hw : ∀ a ∈ w, Masked fullMask a) :
    ∀ a ∈ execute gs w, Masked fullMask a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hw a h1
    · rw [List.mem_singleton.mp h2]; exact gv_masked hw g

theorem run_bit (r : Row) (g : Gate) (w : List Word)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    bit r (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit r)).getD j false) := by
  have hbread : ∀ j, (w.map (bit r)).getD j false = bit r (w.getD j 0) := by
    intro j; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[j]? <;> simp [bit]
  have hfm : fullMask.testBit r.val = true := by
    have : fullMask = 2 ^ 256 - 1 := by decide
    rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true r.isLt
  obtain ⟨o, l⟩ := g
  simp only [hbread]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => simp [gv, bit, hfm, GateOp.eval]
    | cons a l ih =>
      simp only [gv, List.map_cons, List.foldr_cons, primeW, Bool.false_eq_true, ite_false, bit, nat_land_eq, Nat.testBit_and,
        GateOp.eval, List.all_cons, id_eq] at ih ⊢
      rw [ih]
  · induction l with
    | nil => simp [gv, bit, GateOp.eval]
    | cons a l ih =>
      simp only [gv, List.map_cons, List.foldr_cons, primeW, ite_true, bit, nat_lor_eq, Nat.testBit_or,
        GateOp.eval, List.any_cons, id_eq] at ih ⊢
      rw [ih]
  · cases l with
    | nil => simp [gv, bit, nat_xor_eq, Nat.testBit_xor, hfm, GateOp.eval]
    | cons a l => simp [gv, bit, nat_xor_eq, Nat.testBit_xor, hfm, GateOp.eval]

theorem execute_bits (gs : List Gate) (r : Row) (w : List Word)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (execute gs w).map (bit r) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit r g w (hg g (List.mem_cons_self))]

theorem gate_rep (w : List Word) (hw : ∀ a ∈ w, Masked fullMask a) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    Repr fullMask (w.map (nrm fullMask)) (gv w g) ∨
      (isNot g = false ∧ witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g))) := by
  have hm0 : fullMask.testBit 0 = true := by decide
  have hget : ∀ i, Masked fullMask (w.getD i 0) ∧ Repr fullMask (w.map (nrm fullMask)) (w.getD i 0) := by
    intro i; simp only [List.getD_eq_getElem?_getD]
    cases h : w[i]? with
    | none => exact ⟨masked_zero fullMask, repr_const (masked_zero fullMask) (Or.inl rfl)⟩
    | some a => exact ⟨hw a (List.mem_of_getElem? h), Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))⟩
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := hg
  have prim (d : Bool) : Repr fullMask (w.map (nrm fullMask)) ((l.map (fun i => w.getD i 0)).foldr (primeW d) (if d then 0 else fullMask)) ∨
      witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask ((l.map (fun i => w.getD i 0)).foldr (primeW d) (if d then 0 else fullMask))) := by
    have unit (v : Word) (mv : Masked fullMask v) : primeW d v (if d then 0 else fullMask) = v := by
      cases d
      · exact mv
      · apply Nat.eq_of_testBit_eq; intro k; simp [primeW, nat_lor_eq, Nat.testBit_or]
    cases l with
    | nil =>
      left; cases d
      · exact repr_const (masked_self fullMask) (Or.inr rfl)
      · exact repr_const (masked_zero fullMask) (Or.inl rfl)
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit _ (hget i).1]
        exact Or.inl (hget i).2
      | cons j l =>
        cases l with
        | cons _ _ => simp at hl
        | nil =>
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit _ (hget j).1]
          exact primeW_rep hm0 d (hget i).1 (hget j).1 (hget i).2 (hget j).2
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl, h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl, h⟩)
  · left
    cases l with
    | nil =>
      have : gv w ⟨.not, []⟩ = fullMask := by
        apply Nat.eq_of_testBit_eq; intro k; simp [gv, Nat.testBit_xor]
      rw [this]; exact repr_const (masked_self fullMask) (Or.inr rfl)
    | cons i _ =>
      change Repr fullMask (w.map (nrm fullMask)) (Nat.xor fullMask (w.getD i 0))
      unfold Repr
      rw [nrm_xor hm0 (hget i).1]
      exact (hget i).2

theorem extract_live (gs : List Gate) (w : List Word) (hw : ∀ a ∈ w, Masked fullMask a)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    {target : Word} (hp : Proper fullMask target) (hout : target ∈ (execute gs w).map (nrm fullMask)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live fullMask target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm fullMask) := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Masked fullMask a := by
      intro a ha
      rcases List.mem_append.mp ha with h1 | h2
      · exact hw a h1
      · rw [List.mem_singleton.mp h2]; exact gv_masked hw g
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw'
      (fun a ha => legal a (List.mem_cons_of_mem _ ha)) hout
    have rep := gate_rep w hw g (legal g (List.mem_cons_self))
    rw [List.map_append] at hs
    have rep' : represented fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g)) ∨
        ((if isNot g then 0 else 1) = 1 ∧ witnessBin fullMask (w.map (nrm fullMask)) (nrm fullMask (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1], h.2⟩)
    obtain ⟨l, T, hl, hu, hT⟩ := pull_gate ht rep' hs
    refine ⟨l, T, ?_, hu, hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem physical_lower {vars8 : List Word} {goal8 : Word} {L : Nat}
    {targetFn : (Fin 8 → Bool) → Bool}
    (hp : Proper fullMask goal8) (nT : goal8.testBit 0 = false)
    (nR : vars8.all (plainWord fullMask) = true)
    (hlow : LowerM fullMask vars8 goal8 L)
    (hsample : ∀ r : Row, vars8.map (bit r) = List.ofFn (fun i : Fin 8 => r.val.testBit i.val))
    (hgoal : ∀ r : Row, bit r goal8 = targetFn (fun i : Fin 8 => r.val.testBit i.val))
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFn x) :
    L ≤ gates.countP (fun g => !isNot g) := by
  have hw : ∀ a ∈ vars8, Masked fullMask a := by
    intro a ha
    have h := List.all_eq_true.mp nR a ha
    simp only [plainWord, Bool.and_eq_true, Nat.beq_eq] at h; exact h.1
  have heq : (execute gates vars8).getD o 0 = goal8 := by
    refine masked_ext (masked_self fullMask) ?_ hp.1 ?_
    · simp only [List.getD_eq_getElem?_getD]
      cases h : (execute gates vars8)[o]? with
      | none => exact masked_zero fullMask
      | some a => exact execute_masked gates hw a (List.mem_of_getElem? h)
    · intro r
      have hbread : bit r ((execute gates vars8).getD o 0) = ((execute gates vars8).map (bit r)).getD o false := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execute gates vars8)[o]? <;> simp [bit]
      rw [hbread, execute_bits gates r vars8 (fun g hg => (legal g hg).1), hsample r]
      exact (computes (fun i : Fin 8 => r.val.testBit i.val)).trans (hgoal r).symm
  have hmem : goal8 ∈ (execute gates vars8).map (nrm fullMask) := by
    rw [← nrm_id nT, ← heq]
    simp only [List.getD_eq_getElem?_getD]
    cases h : (execute gates vars8)[o]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, h] at heq
      exact absurd heq.symm hp.2.1
    | some a =>
      exact List.mem_map_of_mem (List.mem_of_getElem? h)
  obtain ⟨k, S, hk, run, sub⟩ := extract_live gates vars8 hw legal hp hmem
  rw [nrm_map nR] at sub
  have hnd := Finset.nodup_toList S
  have hrun := list_run run S.toList hnd (by simp)
  have hsup : supply (vars8.map (obsM fullMask)) (S.toList.map (obsM fullMask)) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, hreach, hav, hq⟩ := contraction (observe_proper (masked_self fullMask) hp) hrun
    (vars8.map (obsM fullMask)) Reach.start hsup
  have hL := hlow q bank hreach hav
  omega

abbrev N {α : Type} := @BTree.node α
abbrev L {α : Type} := @BTree.leaf α
abbrev E {α : Type} := @BTree.empty α
abbrev e0 (x : Nat) : BTree NodeRec := L (x,[],[])
abbrev e1 (x c : Nat) : BTree NodeRec := L (x,[c],[])
abbrev ec (x : Nat) (cs : List Nat) : BTree NodeRec := L (x,cs,[])
abbrev ez (x : Nat) (ls : List Nat) : BTree NodeRec := L (x,[],ls)
abbrev ef (x c : Nat) (ls : List Nat) : BTree NodeRec := L (x,[c],ls)
abbrev el (x : Nat) (cs ls : List Nat) : BTree NodeRec := L (x,cs,ls)
abbrev mc (r : List Word) (d b : Nat) : BTree CutSpec := L (mkCut r d b)
abbrev tb := treeBlock
theorem tm {c : Nat → Bool} (s l r : Nat) (a : tb s l c = true) (b : tb (s + l) r c = true) : tb s (l + r) c = true := treeBlock_merge a b
def mw (v p n : Nat) : Wire := ⟨v, p, n, Nat.xor p n⟩

def mr (p0 p1 p2 p3 p4 p5 p6 p7 ones : Nat) (r : Row) : Row :=
  ⟨Nat.mod (Nat.lor ones
    (Nat.lor (if r.val.testBit 0 then Nat.shiftLeft 1 p0 else 0)
    (Nat.lor (if r.val.testBit 1 then Nat.shiftLeft 1 p1 else 0)
    (Nat.lor (if r.val.testBit 2 then Nat.shiftLeft 1 p2 else 0)
    (Nat.lor (if r.val.testBit 3 then Nat.shiftLeft 1 p3 else 0)
    (Nat.lor (if r.val.testBit 4 then Nat.shiftLeft 1 p4 else 0)
    (Nat.lor (if r.val.testBit 5 then Nat.shiftLeft 1 p5 else 0)
    (Nat.lor (if r.val.testBit 6 then Nat.shiftLeft 1 p6 else 0)
             (if r.val.testBit 7 then Nat.shiftLeft 1 p7 else 0))))))))) 256, Nat.mod_lt _ (by decide)⟩

def mrP (code : Nat) : Row → Row :=
  mr (Nat.mod code 8) (Nat.mod (Nat.div code 8) 8) (Nat.mod (Nat.div code 64) 8) (Nat.mod (Nat.div code 512) 8)
     (Nat.mod (Nat.div code 4096) 8) (Nat.mod (Nat.div code 32768) 8) (Nat.mod (Nat.div code 262144) 8)
     (Nat.mod (Nat.div code 2097152) 8) (Nat.div code 16777216)

theorem cv (code : Nat) {mask : Word} {raw : List Word} {T dom subMask : Word} {roots : List Word} {subT : Word} {L : Nat}
    (hL : LowerM subMask roots subT L)
    (hc : (Nat.beq (Nat.land subMask fullMask) subMask && Nat.beq (Nat.land subT subMask) subT &&
           !Nat.beq subT 0 && !Nat.beq subT subMask && checkSlice (mrP code) mask raw T dom subMask roots subT) = true) :
    ValidCut mask raw T (mkCut raw dom L) := mkCut_valid hL hc

def sw12 (w : Word) : Word := swapWord 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3 0x3030303030303030303030303030303030303030303030303030303030303030 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c 2 w
def sw12Row : Row → Row := mr 0 2 1 3 4 5 6 7 0
theorem sw12_spec : Function.Bijective sw12Row ∧ ∀ w, Masked fullMask (sw12 w) ∧ ∀ r : Row, bit r (sw12 w) = bit (sw12Row r) w :=
  swapWord_spec (by decide +kernel)

def sw46 (w : Word) : Word := swapWord 0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 0xffff0000ffff00000000000000000000ffff0000ffff0000 48 w
def sw46Row : Row → Row := mr 0 1 2 3 6 5 4 7 0
theorem sw46_spec : Function.Bijective sw46Row ∧ ∀ w, Masked fullMask (sw46 w) ∧ ∀ r : Row, bit r (sw46 w) = bit (sw46Row r) w :=
  swapWord_spec (by decide +kernel)

def symMain (w : Word) : Word := sw46 (sw12 w)
def symMainRow (r : Row) : Row := sw12Row (sw46Row r)
theorem symMain_spec : Function.Bijective symMainRow ∧ ∀ w, Masked fullMask (symMain w) ∧ ∀ r : Row, bit r (symMain w) = bit (symMainRow r) w :=
  sym_comp_spec (f1 := sw12Row) (f2 := sw46Row) (s1 := sw12) (s2 := sw46) sw12_spec sw46_spec

def sw07 (w : Word) : Word := swapWord 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555 0x5555555555555555555555555555555500000000000000000000000000000000 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 127 w
def sw07Row : Row → Row := mr 7 1 2 3 4 5 6 0 0
theorem sw07_spec : Function.Bijective sw07Row ∧ ∀ w, Masked fullMask (sw07 w) ∧ ∀ r : Row, bit r (sw07 w) = bit (sw07Row r) w :=
  swapWord_spec (by decide +kernel)

def sw14 (w : Word) : Word := swapWord 0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333 0x3333000033330000333300003333000033330000333300003333000033330000 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc 14 w
def sw14Row : Row → Row := mr 0 4 2 3 1 5 6 7 0
theorem sw14_spec : Function.Bijective sw14Row ∧ ∀ w, Masked fullMask (sw14 w) ∧ ∀ r : Row, bit r (sw14 w) = bit (sw14Row r) w :=
  swapWord_spec (by decide +kernel)

def sw56 (w : Word) : Word := swapWord 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff 0xffffffff000000000000000000000000ffffffff0000000000000000 0xffffffff000000000000000000000000ffffffff00000000 32 w
def sw56Row : Row → Row := mr 0 1 2 3 4 6 5 7 0
theorem sw56_spec : Function.Bijective sw56Row ∧ ∀ w, Masked fullMask (sw56 w) ∧ ∀ r : Row, bit r (sw56 w) = bit (sw56Row r) w :=
  swapWord_spec (by decide +kernel)

def sym251 (w : Word) : Word := sw56 (sw14 (sw07 w))
def sym251Row (r : Row) : Row := sw07Row (sw14Row (sw56Row r))
theorem sym251_spec : Function.Bijective sym251Row ∧ ∀ w, Masked fullMask (sym251 w) ∧ ∀ r : Row, bit r (sym251 w) = bit (sym251Row r) w :=
  sym_comp_spec (f1 := fun r => sw07Row (sw14Row r)) (f2 := sw56Row) (s1 := fun w => sw14 (sw07 w)) (s2 := sw56) (sym_comp_spec (f1 := sw07Row) (f2 := sw14Row) (s1 := sw07) (s2 := sw14) sw07_spec sw14_spec) sw56_spec

def m81Mask : Word := 0x300030000000000030003
def m81Goal : Word := 0x300020000000000020000
def m81Raw : List Word := [0x200020000000000020002, 0x300000000000000030000, 0x300030000000000000000]
theorem m81Ess : ∀ a ∈ m81Raw, Essential m81Mask m81Goal m81Raw a :=
  checkAllEss_sound (ps := [4113,273,321]) (by decide +kernel)
def m81Pairs : List (Row × Row) := mkPairs [4353,4368,16641,16704,20496,20544,4352,16640,20480,20737,20752,20800,4416,16656,20481,20736]
def m81Ws : List Wire := [mw 0x200020000000000020002 0xbecf 0x4205,mw 0x300000000000000030000 0xdf73 0x2412,mw 0x300030000000000000000 0xefbc 0x1828]
def m81Cuts : BTree CutSpec := E
theorem m81CutValid : ∀ ci < 0, ValidCut m81Mask m81Raw m81Goal (btreeGet ⟨0,0,[]⟩ 0 m81Cuts ci) := by
  intro ci hci
  omega
def m81D : BTree NodeRec := (e0 0)
def m81Ck : Nat → Bool := checkNode m81Mask m81Goal (Nat.sub (Nat.shiftLeft 1 m81Pairs.length) 1) symMain 1 3 m81Ws m81D 0 m81Cuts 0
theorem q0 : tb 0 1 m81Ck = true := by decide +kernel
theorem m81All : treeBlock 0 1 m81Ck = true := q0
theorem m81Low : LowerM m81Mask m81Raw m81Goal 4 := by
  have hraw : m81Ws.map Wire.val = m81Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 0)) m81D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m81Pairs) (sym := symMain) (count := 1) (rootFuel := 3) (fdepth := 0) (cdepth := 0) (dag := m81D) (cutTree := m81Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m81Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 0)) (defv := (0,[],[])) rfl hnc 0 i
      rw [hraw]; exact m81CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m81All

def m86Mask : Word := 0x5500550000000000550055
def m86Goal : Word := 0x5500500000000000440000
def m86Raw : List Word := [0x4400440000000000440044, 0x5000500000000000500050, 0x5500000000000000550000, 0x5500550000000000000000]
theorem m86Ess : ∀ a ∈ m86Raw, Essential m86Mask m86Goal m86Raw a :=
  checkAllEss_sound (ps := [4114,16452,530,1092]) (by decide +kernel)
def m86Pairs : List (Row × Row) := mkPairs [4610,4624,17412,17472,20496,20544,5638,5652,17926,17986,21058,21524,4614,4628,4674,17414,17428,17474,20500,20546,4608,17408,20480,5634,5636,5648,17922,17924,17984,20994,21008,21056,21508,21520,21568,22022,22036,22082,4612,4672,17410,17424,20482,20484,5698,17940,20998,21012,21510,21570,5632,17920,20992,21504,22018,22020,22032,22080,20486,5696,17936,20996,21506,22016]
def m86Ws : List Wire := [mw 0x4400440000000000440044 0xbbdcf0f8ff9077c3 0x44435528248ad741,mw 0x5000500000000000500050 0xdbef333f1fa38bcc 0x2481e8590905b9c4,mw 0x5500000000000000550000 0xeff7dcffe3dc7cf3 0x1100a21242052892,mw 0x5500550000000000000000 0xf7fbef3ffc6f8f3c 0xa0210a4900a4628]
def m86Cuts : BTree CutSpec := E
theorem m86CutValid : ∀ ci < 0, ValidCut m86Mask m86Raw m86Goal (btreeGet ⟨0,0,[]⟩ 0 m86Cuts ci) := by
  intro ci hci
  omega
def m86D : BTree NodeRec := (e0 0)
def m86Ck : Nat → Bool := checkNode m86Mask m86Goal (Nat.sub (Nat.shiftLeft 1 m86Pairs.length) 1) symMain 1 3 m86Ws m86D 0 m86Cuts 0
theorem q1 : tb 0 1 m86Ck = true := by decide +kernel
theorem m86All : treeBlock 0 1 m86Ck = true := q1
theorem m86Low : LowerM m86Mask m86Raw m86Goal 4 := by
  have hraw : m86Ws.map Wire.val = m86Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 0)) m86D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m86Pairs) (sym := symMain) (count := 1) (rootFuel := 3) (fdepth := 0) (cdepth := 0) (dag := m86D) (cutTree := m86Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m86Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 0)) (defv := (0,[],[])) rfl hnc 0 i
      rw [hraw]; exact m86CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m86All

def m89Mask : Word := 0x30303030000000003030303
def m89Goal : Word := 0x30302020000000002020200
def m89Raw : List Word := [0x20202020000000002020202, 0x30003000000000003000300, 0x30300000000000003030000, 0x30303030000000000000000]
theorem m89Ess : ∀ a ∈ m89Raw, Essential m89Mask m89Goal m89Raw a :=
  checkAllEss_sound (ps := [2057,265,273,321]) (by decide +kernel)
theorem m89Low : LowerM m89Mask m89Raw m89Goal 5 := by
  have hsl : Slice m89Mask m89Raw m89Goal 0x300030000000000030003 4 :=
    checkSlice_sound (f := mr 0 0 0 0 4 0 6 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m81Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m89Ess hsl
  have hcnt : m89Raw.countP (isConst 0x300030000000000030003) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m166Mask : Word := 0x550000005500000000000000000000005500000055
def m166Goal : Word := 0x550000005400000000000000000000005400000000
def m166Raw : List Word := [0x440000004400000000000000000000004400000044, 0x500000005000000000000000000000005000000050, 0x550000000000000000000000000000005500000000, 0x550000005500000000000000000000000000000000]
theorem m166Ess : ∀ a ∈ m166Raw, Essential m166Mask m166Goal m166Raw a :=
  checkAllEss_sound (ps := [8226,8228,546,642]) (by decide +kernel)
theorem m166Low : LowerM m166Mask m166Raw m166Goal 5 := by
  have hsl : Slice m166Mask m166Raw m166Goal 0x110000001100000000000000000000001100000011 4 :=
    checkSlice_sound (f := mr 2 0 0 0 5 0 7 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m81Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m166Ess hsl
  have hcnt : m166Raw.countP (isConst 0x110000001100000000000000000000001100000011) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m55Mask : Word := 0xff00ff00ff00ff
def m55Goal : Word := 0xfe00fc00ee0000
def m55Raw : List Word := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
theorem m55Ess : ∀ a ∈ m55Raw, Essential m55Mask m55Goal m55Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546]) (by decide +kernel)
theorem m55Low : LowerM m55Mask m55Raw m55Goal 5 := by
  have hsl : Slice m55Mask m55Raw m55Goal 0x55005500550055 4 :=
    checkSlice_sound (f := mr 0 2 4 0 5 0 1 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m86Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m55Ess hsl
  have hcnt : m55Raw.countP (isConst 0x55005500550055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m87Mask : Word := 0xff00ff0000000000ff00ff
def m87Goal : Word := 0xff00fa0000000000ee0000
def m87Raw : List Word := [0xaa00aa0000000000aa00aa, 0xcc00cc0000000000cc00cc, 0xf000f00000000000f000f0, 0xff00000000000000ff0000, 0xff00ff0000000000000000]
theorem m87Ess : ∀ a ∈ m87Raw, Essential m87Mask m87Goal m87Raw a :=
  checkAllEss_sound (ps := [4113,4114,16452,273,321]) (by decide +kernel)
theorem m87Low : LowerM m87Mask m87Raw m87Goal 6 := by
  have hsl : Slice m87Mask m87Raw m87Goal 0x3300330000000000330033 5 :=
    checkSlice_sound (f := mr 6 0 0 2 0 0 4 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m89Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m87Ess hsl
  have hcnt : m87Raw.countP (isConst 0x3300330000000000330033) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m118Mask : Word := 0x550055005500550055005500550055
def m118Goal : Word := 0x550054005500500054005400440000
def m118Raw : List Word := [0x440044004400440044004400440044, 0x500050005000500050005000500050, 0x550000005500000055000000550000, 0x550055000000000055005500000000, 0x550055005500550000000000000000]
theorem m118Ess : ∀ a ∈ m118Raw, Essential m118Mask m118Goal m118Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,1092]) (by decide +kernel)
def m118Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,17412,17472,20496,20544,5638,5652,9734,12848,13332,13360,17926,17986,21058,21524,25154,25184,25696,28720,28768,4614,4628,4656,4674,8710,8752,8770,8800,9222,9236,9264,9312,17414,17428,17474,17504,20500,20528,20546,20576,4608,8704,9216,17408,20480,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,17922,17924,17984,20994,21008,21056,21508,21520,21568,25090,25120,25152,25604,25632,25664,28688,28704,28736,13830,13844,13872,22022,22036,22082,26118,26178,26208,29232,29250,29280,29716,29744,29792,4612,4640,4672,8708,8720,8768,9218,9232,9280,17410,17424,17440,20482,20484,20512,5680,5698,9748,9776,9794,9824,12806,12820,12866,12896,13318,13408,17940,18016,20998,21012,21040,21088]
def m118Ws : List Wire := [mw 0x440044004400440044004400440044 0xfcffc01f8fff038fc7fc6001fe373c0f 0x1154892004e90082412408a2b2171405,mw 0x500050005000500050005000500050 0xf0fc7e071ff1c71f8fd81fe004bdcf0 0x35311004905b04108848026626095c50,mw 0x550000005500000055000000550000 0xf3f0f803fe3fe07e3f1e3e001f8cef03 0x64234248321620241210064c4c88e902,mw 0x550055000000000055005500000000 0x3ff00fc7fc7ff803fe0c01fe1f0f03c 0xca8a64016b0449002480151949e0a028,mw 0x550055005500550000000000000000 0xfc003f007ff8ffffc0031fe001ff03c0 0x8acc80924da092490000199191760280]
def m118Cuts : BTree CutSpec := (N (N (N (mc m118Raw 0x55005500550055 4) (mc m118Raw 0x110011001100110011001100110011 4)) (N (mc m118Raw 0x55000000550000005500000055 4) E)) (N (N (mc m118Raw 0x5500550000000000550055 4) E) (N (mc m118Raw 0x50005000500050005000500050005 4) E)))
theorem m118CutValid : ∀ ci < 5, ValidCut m118Mask m118Raw m118Goal (btreeGet ⟨0,0,[]⟩ 3 m118Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 1589384 m86Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 549216 m86Low (by decide +kernel)
def m118D : BTree NodeRec := (N (N (N (N (el 0 [0,1,2,3,4] [188418,319492,450566,581640,2416649,2547719,2678789,4644874,4775948,6873099]) (e0 4168)) (N (ez 71 [524306,589844]) (e0 20536))) (N (N (e0 39) (e0 16456)) (N (e0 583) E))) (N (N (N (ez 23 [524302,589840]) (e1 16448 2)) (N (ez 567 [393238,458776]) E)) (N (N (e0 55) (e1 20528 4)) (N (e1 4160 1) E))))
def m118Ck : Nat → Bool := checkNode m118Mask m118Goal (Nat.sub (Nat.shiftLeft 1 m118Pairs.length) 1) symMain 13 6 m118Ws m118D 4 m118Cuts 3
theorem q2 : tb 0 13 m118Ck = true := by decide +kernel
theorem m118All : treeBlock 0 13 m118Ck = true := q2
theorem m118Low : LowerM m118Mask m118Raw m118Goal 7 := by
  have hraw : m118Ws.map Wire.val = m118Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 5)) m118D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m118Pairs) (sym := symMain) (count := 13) (rootFuel := 6) (fdepth := 4) (cdepth := 3) (dag := m118D) (cutTree := m118Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m118Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 5)) (defv := (0,[],[])) rfl hnc 4 i
      rw [hraw]; exact m118CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m118All

def m143Mask : Word := 0xffff0000000000000000000000000000ffff
def m143Goal : Word := 0xfffe0000000000000000000000000000aa00
def m143Raw : List Word := [0xaaaa0000000000000000000000000000aaaa, 0xcccc0000000000000000000000000000cccc, 0xf0f00000000000000000000000000000f0f0, 0xff000000000000000000000000000000ff00, 0xffff00000000000000000000000000000000]
theorem m143Ess : ∀ a ∈ m143Raw, Essential m143Mask m143Goal m143Raw a :=
  checkAllEss_sound (ps := [2057,32898,32900,265,385]) (by decide +kernel)
theorem m143Low : LowerM m143Mask m143Raw m143Goal 6 := by
  have hsl : Slice m143Mask m143Raw m143Goal 0x333300000000000000000000000000003333 5 :=
    checkSlice_sound (f := mr 7 0 0 2 0 0 3 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m89Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m143Ess hsl
  have hcnt : m143Raw.countP (isConst 0x333300000000000000000000000000003333) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m151Mask : Word := 0xff00ff00000000000000000000000000ff00ff
def m151Goal : Word := 0xfe00fe00000000000000000000000000ee0000
def m151Raw : List Word := [0xaa00aa00000000000000000000000000aa00aa, 0xcc00cc00000000000000000000000000cc00cc, 0xf000f000000000000000000000000000f000f0, 0xff000000000000000000000000000000ff0000, 0xff00ff00000000000000000000000000000000]
theorem m151Ess : ∀ a ∈ m151Raw, Essential m151Mask m151Goal m151Raw a :=
  checkAllEss_sound (ps := [4113,4114,32900,273,385]) (by decide +kernel)
theorem m151Low : LowerM m151Mask m151Raw m151Goal 5 := by
  have hsl : Slice m151Mask m151Raw m151Goal 0x55005500000000000000000000000000550055 4 :=
    checkSlice_sound (f := mr 0 2 4 0 7 0 1 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m86Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m151Ess hsl
  have hcnt : m151Raw.countP (isConst 0x55005500000000000000000000000000550055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m155Mask : Word := 0xf0f0f0f0000000000000000000000000f0f0f0f
def m155Goal : Word := 0xf0e0f0e0000000000000000000000000e0e0a00
def m155Raw : List Word := [0xa0a0a0a0000000000000000000000000a0a0a0a, 0xc0c0c0c0000000000000000000000000c0c0c0c, 0xf000f000000000000000000000000000f000f00, 0xf0f00000000000000000000000000000f0f0000, 0xf0f0f0f00000000000000000000000000000000]
theorem m155Ess : ∀ a ∈ m155Raw, Essential m155Mask m155Goal m155Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,385]) (by decide +kernel)
theorem m155Low : LowerM m155Mask m155Raw m155Goal 6 := by
  have hsl : Slice m155Mask m155Raw m155Goal 0x303030300000000000000000000000003030303 5 :=
    checkSlice_sound (f := mr 0 0 0 4 3 0 7 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m89Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m155Ess hsl
  have hcnt : m155Raw.countP (isConst 0x303030300000000000000000000000003030303) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m158Mask : Word := 0x5555555500000000000000000000000055555555
def m158Goal : Word := 0x5554555400000000000000000000000044440000
def m158Raw : List Word := [0x4444444400000000000000000000000044444444, 0x5050505000000000000000000000000050505050, 0x5500550000000000000000000000000055005500, 0x5555000000000000000000000000000055550000, 0x5555555500000000000000000000000000000000]
theorem m158Ess : ∀ a ∈ m158Raw, Essential m158Mask m158Goal m158Raw a :=
  checkAllEss_sound (ps := [4114,32900,32904,530,642]) (by decide +kernel)
theorem m158Low : LowerM m158Mask m158Raw m158Goal 5 := by
  have hsl : Slice m158Mask m158Raw m158Goal 0x505050500000000000000000000000005050505 4 :=
    checkSlice_sound (f := mr 0 3 4 0 7 0 1 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m86Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m158Ess hsl
  have hcnt : m158Raw.countP (isConst 0x505050500000000000000000000000005050505) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m167Mask : Word := 0xff000000ff0000000000000000000000ff000000ff
def m167Goal : Word := 0xff000000fe0000000000000000000000fc00000000
def m167Raw : List Word := [0xaa000000aa0000000000000000000000aa000000aa, 0xcc000000cc0000000000000000000000cc000000cc, 0xf0000000f00000000000000000000000f0000000f0, 0xff000000000000000000000000000000ff00000000, 0xff000000ff00000000000000000000000000000000]
theorem m167Ess : ∀ a ∈ m167Raw, Essential m167Mask m167Goal m167Raw a :=
  checkAllEss_sound (ps := [32897,8226,8228,546,385]) (by decide +kernel)
theorem m167Low : LowerM m167Mask m167Raw m167Goal 6 := by
  have hsl : Slice m167Mask m167Raw m167Goal 0x550000005500000000000000000000005500000055 5 :=
    checkSlice_sound (f := mr 0 1 2 0 0 5 0 7 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m166Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m167Ess hsl
  have hcnt : m167Raw.countP (isConst 0x550000005500000000000000000000005500000055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m182Mask : Word := 0x5500550055005500000000000000000055005500550055
def m182Goal : Word := 0x5500550054005400000000000000000054005400440000
def m182Raw : List Word := [0x4400440044004400000000000000000044004400440044, 0x5000500050005000000000000000000050005000500050, 0x5500000055000000000000000000000055000000550000, 0x5500550000000000000000000000000055005500000000, 0x5500550055005500000000000000000000000000000000]
theorem m182Ess : ∀ a ∈ m182Raw, Essential m182Mask m182Goal m182Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,642]) (by decide +kernel)
def m182Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,33282,33408,33796,33920,40992,41088,5638,5652,9734,12848,13332,13360,34310,37520,37908,38032,45104,45200,4614,4628,4656,4752,8710,8752,9222,9236,9264,33286,33424,33798,33812,33936,41008,41104,4608,8704,9216,33280,33792,40960,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,34306,34308,34432,37378,37392,37504,37892,37904,38016,41474,41504,41600,41988,42016,42112,45072,45088,45184,13830,13844,13872,38406,38420,38544,42502,45616,45712,46100,46128,46224,4612,4640,4736,8708,8720,8832,9218,9232,9344,33284,33296,33312,33794,33808,33824,40962,40964,40976,5680,5776,9748,9776,12806,12820,12944,13318,13456,34324,34448,37382,37396,37424,37894,37936,41478,41520,41616,41990,42004,42032]
def m182Ws : List Wire := [mw 0x4400440044004400000000000000000044004400440044 0x1cf9fc0e3f1ff038fc7fcb063f0cf0cf 0x25224090400490082412400a51045045,mw 0x5000500050005000000000000000000050005000500050 0xe31e3c71c0e7f1c71f8fd439c0377330 0x656ad1020925b0410884801ad3157110,mw 0x5500000055000000000000000000000055000000550000 0x3e7cc0007fbfe07e3f1c1000ffbb003 0xdaddbe2490fb6202412100f5aefba002,mw 0x5500550000000000000000000000000055005500000000 0xfc07f381f8fc7ff803fe26c1f0c3cc3c 0x8a802448024844900248004124428428,mw 0x5500550055005500000000000000000000000000000000 0xfff803fe00ff8ffffc0038fe00fc0fc0 0x1015080124920924900000a408a80a80]
def m182Cuts : BTree CutSpec := (N (N (N (mc m182Raw 0x550000005500000000000000000000005500000055 5) (mc m182Raw 0x1100000011000000000000000000000011000000110000 4)) (N (mc m182Raw 0x55005500550055 4) E)) (N (N (mc m182Raw 0x500050005000500000000000000000005000500050005 5) E) (N (mc m182Raw 0x55005500000000000000000000000000550055 4) E)))
theorem m182CutValid : ∀ ci < 5, ValidCut m182Mask m182Raw m182Goal (btreeGet ⟨0,0,[]⟩ 3 m182Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 14844040 m166Low (by decide +kernel)
  · exact cv 1857537 m89Low (by decide +kernel)
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
def m182D : BTree NodeRec := (N (N (el 0 [0,1,2,3,4] [6873090]) (e0 4168)) (N (el 839 [0,1,2,4] [589828]) E))
def m182Ck : Nat → Bool := checkNode m182Mask m182Goal (Nat.sub (Nat.shiftLeft 1 m182Pairs.length) 1) id 3 6 m182Ws m182D 2 m182Cuts 3
theorem q3 : tb 0 3 m182Ck = true := by decide +kernel
theorem m182All : treeBlock 0 3 m182Ck = true := q3
theorem m182Low : LowerM m182Mask m182Raw m182Goal 7 := by
  have hraw : m182Ws.map Wire.val = m182Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 5)) m182D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m182Pairs) (sym := id) (count := 3) (rootFuel := 6) (fdepth := 2) (cdepth := 3) (dag := m182D) (cutTree := m182Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m182Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 5)) (defv := (0,[],[])) rfl hnc 2 i
      rw [hraw]; exact m182CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m182All

def m217Mask : Word := 0x3030303000000000303030300000000030303030000000003030303
def m217Goal : Word := 0x3030302000000000302030200000000030302020000000002020200
def m217Raw : List Word := [0x2020202000000000202020200000000020202020000000002020202, 0x3000300000000000300030000000000030003000000000003000300, 0x3030000000000000303000000000000030300000000000003030000, 0x3030303000000000000000000000000030303030000000000000000, 0x3030303000000000303030300000000000000000000000000000000]
theorem m217Ess : ∀ a ∈ m217Raw, Essential m217Mask m217Goal m217Raw a :=
  checkAllEss_sound (ps := [2057,265,273,321,385]) (by decide +kernel)
def m217Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,16641,16704,20496,20544,33025,33152,34824,34944,6424,18760,22552,22600,37264,38936,39056,49600,51272,51392,53392,53440,2328,2376,4376,4496,16712,16832,20504,20552,20624,20672,33168,33216,34840,34888,34960,35008,2304,4352,16640,20480,33024,34816,6401,6408,6416,18689,18696,18752,20737,20752,20800,22536,22544,22592,35073,35080,35200,37121,37136,37248,38920,38928,39040,49409,49472,49536,51208,51264,51328,53264,53312,53376,22808,22856,39192,39312,51528,51648,53648,53696,55320,55368,55440,55488,2320,2368,2432,4360,4416,4480,16648,16656,16768,20481,20488,20608,33032,33040,33088,34817,34832,34880,6472,6544,18712,18880,20760,20808,20880,20928,22672,22720,35096,35144,35216,35264,37144,37312,38984,39104,49480,49552,51224,51344]
def m217Ws : List Wire := [mw 0x2020202000000000202020200000000020202020000000002020202 0x33f3fc71ff0ff038fc7fd70c3f09333f 0x82000000082412400000000115,mw 0x3000300000000000300030000000000030003000000000003000300 0xccfc3f8007f3f1c71f8fe1f00336fc03 0x5530d4144831704108848030d712f402,mw 0x3030000000000000303000000000000030300000000000003030000 0xf0fcc0e38fcfe07e3f1ca03ccc7d0cc 0xe15559208154d202412100554d475048,mw 0x3030303000000000000000000000000030303030000000000000000 0xf00ff00fc0ff3ff803fe0c03f0f8e0f0 0x1eaaa64012ab2490024800aab2b8a0a0,mw 0x3030303000000000303030300000000000000000000000000000000 0xfff003f000ffcffffc0030fc00ff0f00 0xaacf280924ce8924900000cf28ed0a00]
def m217Cuts : BTree CutSpec := (N (N (N (mc m217Raw 0x30303030000000003030303 5) (mc m217Raw 0x300030000000000030003 4)) (N (mc m217Raw 0x303000000000000030300000000000003030000000000000303 5) E)) (N (N (mc m217Raw 0x303030300000000000000000000000003030303 5) (mc m217Raw 0x30300000000000000000000000000000303 4)) (N (mc m217Raw 0x30003000000000003000300000000000300030000000000030003 5) E)))
theorem m217CutValid : ∀ ci < 6, ValidCut m217Mask m217Raw m217Goal (btreeGet ⟨0,0,[]⟩ 3 m217Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1590784 m89Low (by decide +kernel)
  · exact cv 1849344 m89Low (by decide +kernel)
  · exact cv 1850368 m89Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
  · exact cv 1589248 m81Low (by decide +kernel)
  · exact cv 1847296 m81Low (by decide +kernel)
def m217D : BTree NodeRec := (N (N (N (N (N (N (el 0 [0,1,2,3,4,5] [188418,221188,319494,352264,450567,483337,581642,614412,2416654,2547727,4775952,6873105]) (ec 21061 [2,4])) (N (e0 8249) (e0 147524))) (N (N (el 583 [0,1,2,3,4,5] [401480,434218,467018,499766,2531376,4628544]) (e0 61512)) (N (ec 12885 [0,5]) E))) (N (N (N (el 43 [0,1,2,3,5] [311330,434226,466976,696372,729142,2408482]) (el 32817 [0,2,4,5] [557152,688226])) (N (e1 12362 1) E)) (N (N (e0 4184) (e0 106568)) (N (ec 20522 [0,4]) E)))) (N (N (N (N (el 27 [0,1,2,3,4] [311314,434206,466976,565279,598049,2408466]) (el 28721 [2,3,4,5] [557148,688222])) (N (e0 12345) E)) (N (N (el 4149 [4,5] [589900,720974]) (e0 86104)) (N (ef 16469 4 [589912]) E))) (N (N (N (el 75 [0,1,2,3,4] [311352,565314,598070,696387,729143,2408504]) (e0 41032)) (N (e0 12377) E)) (N (N (ec 4661 [2,4]) (e0 139332)) (N (e1 20538 3) E))))) (N (N (N (N (N (el 23 [0,1,2,3,4] [344082,434196,466966,565269,598039,720920,737306,2441234,4628508,4759581]) (ef 24645 5 [720986])) (N (ec 12330 [2,5]) (e0 147540))) (N (N (ec 4138 [3,4]) (e0 86088)) (N (ef 16437 4 [720982]) E))) (N (N (N (el 71 [0,1,2,3,4] [344120,458810,475196,565290,598078,696363,729151,2441272,4759616,4890689]) (e0 32825)) (N (el 12373 [4,5] [589906,720980]) E)) (N (N (e1 4186 0) (e0 135256)) (N (e0 20536) E)))) (N (N (N (N (el 39 [0,1,2,3,5] [344098,434196,466980,589862,606248,696362,729132,2441250,4628526,4890672]) (e0 28729)) (N (e0 12360) E)) (N (N (e0 4153) (e0 102488)) (N (e0 16473) E))) (N (N (N (el 295 [0,1,2,3,4,5] [401476,434196,467014,499744,2531356,4628526]) (e0 41048)) (N (ec 12853 [3,5]) E)) (N (N (ef 8245 5 [589904]) (e0 139348)) (N (e0 20553) E))))))
def m217Ck : Nat → Bool := checkNode m217Mask m217Goal (Nat.sub (Nat.shiftLeft 1 m217Pairs.length) 1) symMain 50 7 m217Ws m217D 6 m217Cuts 3
theorem q4 : tb 0 24 m217Ck = true := by decide +kernel
theorem q5 : tb 24 24 m217Ck = true := by decide +kernel
theorem q6 : tb 48 2 m217Ck = true := by decide +kernel
theorem m217All : treeBlock 0 50 m217Ck = true := (tm 0 24 26 q4 (tm 24 24 2 q5 q6))
theorem m217Low : LowerM m217Mask m217Raw m217Goal 8 := by
  have hraw : m217Ws.map Wire.val = m217Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 6)) m217D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m217Pairs) (sym := symMain) (count := 50) (rootFuel := 7) (fdepth := 6) (cdepth := 3) (dag := m217D) (cutTree := m217Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m217Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 6)) (defv := (0,[],[])) rfl hnc 6 i
      rw [hraw]; exact m217CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m217All

def m241Mask : Word := 0x3000300030003000300030003000300030003000300030003000300030003
def m241Goal : Word := 0x3000300030002000300030002000200030002000300020002000000020000
def m241Raw : List Word := [0x2000200020002000200020002000200020002000200020002000200020002, 0x3000000030000000300000003000000030000000300000003000000030000, 0x3000300000000000300030000000000030003000000000003000300000000, 0x3000300030003000000000000000000030003000300030000000000000000, 0x3000300030003000300030003000300000000000000000000000000000000]
theorem m241Ess : ∀ a ∈ m241Raw, Essential m241Mask m241Goal m241Raw a :=
  checkAllEss_sound (ps := [4113,273,32928,321,385]) (by decide +kernel)
def m241Pairs : List (Row × Row) := mkPairs [4353,4368,16641,16704,20496,20544,33025,33152,40992,41088,12577,12592,24865,24928,28720,28768,37264,41249,45104,45200,49600,53392,53440,57440,57536,4385,4400,4496,16673,16736,16832,20528,20576,20624,20672,33057,33168,33216,40993,41008,41056,41104,41152,4352,16640,20480,33024,40960,12545,12560,12576,20737,20752,20800,24833,24864,24896,28688,28704,28736,37121,37136,37248,41217,41248,41344,45072,45088,45184,49409,49472,49536,53264,53312,53376,57376,57408,57472,28961,28976,29024,45345,45360,45456,53648,53696,57633,57696,57792,61488,61536,61584,61632,4384,4416,4480,16656,16672,16768,20481,20512,20608,33040,33056,33088,40961,40976,41024,12640,12688,20769,20784,20832,20880,20928,24880,25024,28705,28816,28864,37153,37168,37312,41264,41312,41360,41408,45089]
def m241Ws : List Wire := [mw 0x2000200020002000200020002000200020002000200020002000200020002 0x7f1ff1c7e1ffc0e3f1ff58387e133ccf 0x81204208004240209049004812021445,mw 0x3000000030000000300000003000000030000000300000003000000030000 0x87e7f038fe3fc71c7e3f28078e6dcc33 0x2a4aa4410a1c8104221202928c2d4812,mw 0x3000300000000000300030000000000030003000000000003000300000000 0xf8f83e001fcff81f8fc787c0018eff00 0x9b29d09226c7c809048401c9b686fd00,mw 0x3000300030003000000000000000000030003000300030000000000000000 0xffc03f1ff1ffe00ff83007f1f0f03c 0x5495190055a112400920052561d0a028,mw 0x3000300030003000300030003000300000000000000000000000000000000 0xff000fc01ffe3ffff000c7f801ff03c0 0x64d62024993824924000063649790280]
def m241Cuts : BTree CutSpec := (N (N (mc m241Raw 0x30003000000000003000300000000000300030000000000030003 5) (mc m241Raw 0x300030003000300000000000000000003000300030003 4)) (N (mc m241Raw 0x30003000000000003000300000000 4) (mc m241Raw 0x300000003000000030000000300000003000000030000000300000003 4)))
theorem m241CutValid : ∀ ci < 4, ValidCut m241Mask m241Raw m241Goal (btreeGet ⟨0,0,[]⟩ 2 m241Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1592832 m89Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 1835360 m86Low (by decide +kernel)
  · exact cv 29096 m86Low (by decide +kernel)
def m241D : BTree NodeRec := (N (N (N (el 0 [0,1,2,3] [188418,221188,450563,483333,2547718]) (e1 4160 2)) (N (ec 27 [0,1]) E)) (N (N (ez 23 [524296,589834]) (e0 4168)) (N (e1 311 2) E)))
def m241Ck : Nat → Bool := checkNode m241Mask m241Goal (Nat.sub (Nat.shiftLeft 1 m241Pairs.length) 1) symMain 6 6 m241Ws m241D 3 m241Cuts 2
theorem q7 : tb 0 6 m241Ck = true := by decide +kernel
theorem m241All : treeBlock 0 6 m241Ck = true := q7
theorem m241Low : LowerM m241Mask m241Raw m241Goal 7 := by
  have hraw : m241Ws.map Wire.val = m241Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 4)) m241D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m241Pairs) (sym := symMain) (count := 6) (rootFuel := 6) (fdepth := 3) (cdepth := 2) (dag := m241D) (cutTree := m241Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m241Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 4)) (defv := (0,[],[])) rfl hnc 3 i
      rw [hraw]; exact m241CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m241All

def m63Mask : Word := 0xffffffffffffffff
def m63Goal : Word := 0xfefefefceeeeaa00
def m63Raw : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
theorem m63Ess : ∀ a ∈ m63Raw, Essential m63Mask m63Goal m63Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546]) (by decide +kernel)
def m63Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,2307,2309,2314,2316,2328,2337,2344,4355,4357,4372,4376,4385,4400,4611,4614,4618,4628,4632,4656,8707,8710,8714,8737,8744,8752,9221,9222,9228,9236,9249,9256,9264,2304,4352,4608,8704,9216,2823,2830,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6456,6670,6684,6712,8967,9479,9735,9742,10552,10766,10808,11278,11292,11320,12600,12856,13340,13368,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380]
def m63Ws : List Wire := [mw 0xaaaaaaaaaaaaaaaa 0xffe2098c7f8c00007ffc53c61bc9fc0f 0x49200380b2808920a68c11420bc0d405,mw 0xcccccccccccccccc 0x38e436f391b007ff8000bdc864f64cf0 0x10405791b78010e3821435c024524c50,mw 0xf0f0f0f0f0f0f0f0 0xc719c703ee43f80000033ff18707b300 0x8208d7b7ff8078450c293fd08507b100,mw 0xff00ff00ff00ff00 0x7e1f87c0f84000001ffeec1f8383c03 0x49ffc7f4d01228a1173ee81f0382802,mw 0xffff0000ffff0000 0xf81e007ff018001ffe03cf3e003fc03c 0x201fa86e4802441c5843ca3c002d0028,mw 0xffffffff00000000 0x1fff800063ffe00003f03fffc003c0 0x172848000387106182c02f5a800280]
def m63Cuts : BTree CutSpec := (N (N (mc m63Raw 0xff00ff00ff00ff 5) (mc m63Raw 0xf0f0f0f0 4)) (N (mc m63Raw 0xf0f0f0f0f0f0f0f 5) (mc m63Raw 0x5500550055005500 4)))
theorem m63CutValid : ∀ ci < 4, ValidCut m63Mask m63Raw m63Goal (btreeGet ⟨0,0,[]⟩ 2 m63Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 33123 m55Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
def m63D : BTree NodeRec := (ec 0 [0,1,2,3])
def m63Ck : Nat → Bool := checkNode m63Mask m63Goal (Nat.sub (Nat.shiftLeft 1 m63Pairs.length) 1) id 1 6 m63Ws m63D 0 m63Cuts 2
theorem q8 : tb 0 1 m63Ck = true := by decide +kernel
theorem m63All : treeBlock 0 1 m63Ck = true := q8
theorem m63Low : LowerM m63Mask m63Raw m63Goal 7 := by
  have hraw : m63Ws.map Wire.val = m63Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 4)) m63D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m63Pairs) (sym := id) (count := 1) (rootFuel := 6) (fdepth := 0) (cdepth := 2) (dag := m63D) (cutTree := m63Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m63Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 4)) (defv := (0,[],[])) rfl hnc 0 i
      rw [hraw]; exact m63CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m63All

def m95Mask : Word := 0xffffffff00000000ffffffff
def m95Goal : Word := 0xfffffafa00000000eeeeaa00
def m95Raw : List Word := [0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000, 0xffffffff0000000000000000]
theorem m95Ess : ∀ a ∈ m95Raw, Essential m95Mask m95Goal m95Raw a :=
  checkAllEss_sound (ps := [2057,4114,16452,265,273,321]) (by decide +kernel)
def m95Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,3847,3854,5895,7452,7694,7708,18183,19274,19982,20042,23114,23580,2307,2309,2314,2316,2328,2376,4355,4357,4372,4376,4611,4614,4618,4628,4632,4674,16643,16645,16706,16712,17413,17414,17420,17428,17474,17480,20500,20504,20546,20552,2304,4352,4608,16640,17408,20480,2823,2830,2890,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6670,6684,6730,17159,17226,17671,17927,17934,17994,18762,19470,19484,19530,21066,21532,22556,22602,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380,5392,5634,5636]
def m95Ws : List Wire := [mw 0xaaaaaaaa00000000aaaaaaaa 0x3ffc04711ff2c00f03ff0cf02727f0cf 0x92400d02c90001304c3045005035045,mw 0xcccccccc00000000cccccccc 0xc71c43bee4710000fc007f711bd93030 0x420a6ffa6df011259c457d711b493010,mw 0xf0f0f0f000000000f0f0f0f0 0xf8e0bbc0fb8403f00000b7f2dc1ec300 0x904199d7ffb004f2298a97f24c1ec100,mw 0xff00ff0000000000ff00ff00 0xff3c0f03f04000003ffbbce0e0f003 0x93ff2fd3602a48523cfbace0e0a002,mw 0xffff000000000000ffff0000 0xff03c00ffc09bc00ffc0c3cf00ff0c3c 0x2401900592000c806310828600b40428,mw 0xffffffff0000000000000000 0x3fff0000e3fff0000fc0fff000fc0 0x266280040330c80206809b2000a80]
def m95Cuts : BTree CutSpec := (N (N (N (mc m95Raw 0xff00ff0000000000ff00ff 6) (mc m95Raw 0xcccc000000000000cccc 4)) (N (mc m95Raw 0x333333330000000033333333 6) E)) (N (N (mc m95Raw 0xf0f0f0f000000000f0f0f0f 6) (mc m95Raw 0x550055000000000055005500 4)) (N (mc m95Raw 0xf0f0f0f0 4) E)))
theorem m95CutValid : ∀ ci < 6, ValidCut m95Mask m95Raw m95Goal (btreeGet ⟨0,0,[]⟩ 3 m95Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 16590 m87Low (by decide +kernel)
  · exact cv 24788 m87Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
def m95D : BTree NodeRec := (N (N (N (N (N (el 0 [0,1,2,3,4,5] [180226,311299,475140,581638,712711,2727944,2793482,4759563,4956169,6856716,6987789,9101326]) (ez 17245 [294956])) (N (e0 4185) E)) (N (N (el 333 [0,1,2,4] [303132,696350,4636691,4800534,7053344,9084962]) (e1 28772 5)) (N (e0 8789) E))) (N (N (N (el 58 [0,1,2,5] [565268,696341,4825110,4890648,6856729,7053335]) (e0 20521)) (N (e0 8261) E)) (N (N (el 837 [0,1,2,4,5] [729126,9150499]) (e0 65572)) (N (e0 16421) E)))) (N (N (N (N (el 22 [0,1,2,4,5] [729104,4956178]) (e0 17493)) (N (e0 4701) E)) (N (N (el 341 [0,1,2,3,4] [335908,4800536]) (e0 45092)) (N (e1 12356 3) E))) (N (N (N (el 71 [0,1,2,4,5] [557082]) (e0 24665)) (N (ez 8781 [294954]) E)) (N (N (el 1111 [0,1,2,3,4] [819240]) E) (N (e0 16469) E)))))
def m95Ck : Nat → Bool := checkNode m95Mask m95Goal (Nat.sub (Nat.shiftLeft 1 m95Pairs.length) 1) symMain 23 7 m95Ws m95D 5 m95Cuts 3
theorem q9 : tb 0 23 m95Ck = true := by decide +kernel
theorem m95All : treeBlock 0 23 m95Ck = true := q9
theorem m95Low : LowerM m95Mask m95Raw m95Goal 8 := by
  have hraw : m95Ws.map Wire.val = m95Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 6)) m95D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m95Pairs) (sym := symMain) (count := 23) (rootFuel := 7) (fdepth := 5) (cdepth := 3) (dag := m95D) (cutTree := m95Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m95Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 6)) (defv := (0,[],[])) rfl hnc 5 i
      rw [hraw]; exact m95CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m95All

def m119Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff
def m119Goal : Word := 0xff00fe00ff00fa00fe00fc00ee0000
def m119Raw : List Word := [0xaa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff00000000, 0xff00ff00ff00ff0000000000000000]
theorem m119Ess : ∀ a ∈ m119Raw, Essential m119Mask m119Goal m119Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,321]) (by decide +kernel)
def m119Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,21058,21524,24865,24928,25154,25184,25696,28720,28768,5895,9991,18183,4355,4357,4372,4385,4400,4611,4614,4628,4656,4674,8707,8710,8737,8752,8770,8800,9221,9222,9236,9249,9264,9312,16643,16645,16673,16706,16736,17413,17414,17428,17474,17504,20500,20528,20546,20576,4352,4608,8704,9216,16640,17408,20480,4871,5383,5639,8967,9479,9735,17159,17671,17927,4865,4866,4880,5377,5380,5392,5634,5636,5648,8961,8962,8992,9473,9476,9504,9730,9732,9760,12545,12560,12576,12802,12816,12832,13316,13328,13344,17153,17154,17216]
def m119Ws : List Wire := [mw 0xaa00aa00aa00aa00aa00aa00aa00aa 0xe071f8fdb64401f00007f830e379c303 0x20104827fe000272450af810a178c101,mw 0xcc00cc00cc00cc00cc00cc00cc00cc 0xe38e3f1eda1800003ff838c7649e403c 0x4082110bfe01149093987847608a4014,mw 0xf000f000f000f000f000f000f000f0 0x1c0fc7e36ca03e0fc000390b98e78cc0 0x4048243fe004e21c231b80988a78440,mw 0xff000000ff000000ff000000ff0000 0x1ff007fc0f0fc00000ffce0c1f07f00f 0x92004900000c805086502081e05100a,mw 0xff00ff0000000000ff00ff00000000 0x1ffff8007030000fff0017f01ff800f0 0x124920000002a14e2c4607b0175000a0,mw 0xff00ff00ff00ff0000000000000000 0xe000000381c3fff0000027ffe0003f00 0x8000000000033188308005e640002a00]
def m119Cuts : BTree CutSpec := (N (N (N (mc m119Raw 0xf000f000f000f000f000f000f000f 7) (mc m119Raw 0x30003000000000003000300000000 4)) (N (mc m119Raw 0x550055005500550055005500550055 7) (mc m119Raw 0xff000000ff000000ff000000ff 5))) (N (N (mc m119Raw 0x330033003300330033003300330033 7) (mc m119Raw 0xff00ff00ff00ff 5)) (N (mc m119Raw 0xff00ff0000000000ff00ff 6) E)))
theorem m119CutValid : ∀ ci < 7, ValidCut m119Mask m119Raw m119Goal (btreeGet ⟨0,0,[]⟩ 3 m119Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 1753224 m118Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
def m119D : BTree NodeRec := (N (N (N (N (el 0 [0,1,2,3,4] [6971394,7004164,7036934,7069703]) (e0 8248)) (N (ec 4148 [5,6]) E)) (N (N (el 855 [0,1,2,3,5,6,4] [458768,475154]) (ef 12325 2 [458774])) (N (e1 4196 4) E))) (N (N (N (el 851 [0,1,2,3,5,6,4] [425992,557066,688139,819212,884750]) (e1 8250 2)) (N (ec 4164 [5,6]) E)) (N (N (el 859 [0,1,2,3,5,6,4] [303124]) (e0 41016)) (N (e1 4204 3) E))))
def m119Ck : Nat → Bool := checkNode m119Mask m119Goal (Nat.sub (Nat.shiftLeft 1 m119Pairs.length) 1) symMain 12 8 m119Ws m119D 4 m119Cuts 3
theorem q10 : tb 0 12 m119Ck = true := by decide +kernel
theorem m119All : treeBlock 0 12 m119Ck = true := q10
theorem m119Low : LowerM m119Mask m119Raw m119Goal 9 := by
  have hraw : m119Ws.map Wire.val = m119Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 7)) m119D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m119Pairs) (sym := symMain) (count := 12) (rootFuel := 8) (fdepth := 4) (cdepth := 3) (dag := m119D) (cutTree := m119Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m119Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 7)) (defv := (0,[],[])) rfl hnc 4 i
      rw [hraw]; exact m119CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m119All

def m123Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def m123Goal : Word := 0xf0f0e0e0f0f0a0a0e0e0e0c0e0e0a00
def m123Raw : List Word := [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f00000000, 0xf0f0f0f0f0f0f0f0000000000000000]
theorem m123Ess : ∀ a ∈ m123Raw, Essential m123Mask m123Goal m123Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,321]) (by decide +kernel)
theorem m123Low : LowerM m123Mask m123Raw m123Goal 8 := by
  have hsl : Slice m123Mask m123Raw m123Goal 0xf000f000f000f000f000f000f000f 7 :=
    checkSlice_sound (f := mr 4 0 0 0 0 5 6 1 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m241Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m123Ess hsl
  have hcnt : m123Raw.countP (isConst 0xf000f000f000f000f000f000f000f) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m159Mask : Word := 0xffffffff000000000000000000000000ffffffff
def m159Goal : Word := 0xfffefffe000000000000000000000000eeeeaa00
def m159Raw : List Word := [0xaaaaaaaa000000000000000000000000aaaaaaaa, 0xcccccccc000000000000000000000000cccccccc, 0xf0f0f0f0000000000000000000000000f0f0f0f0, 0xff00ff00000000000000000000000000ff00ff00, 0xffff0000000000000000000000000000ffff0000, 0xffffffff00000000000000000000000000000000]
theorem m159Ess : ∀ a ∈ m159Raw, Essential m159Mask m159Goal m159Raw a :=
  checkAllEss_sound (ps := [2057,4114,32900,265,273,385]) (by decide +kernel)
def m159Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,33025,33152,33282,33408,33796,33920,34824,34944,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,3847,3854,5895,7452,7694,7708,34567,36366,39964,2307,2309,2314,2316,2328,4355,4357,4372,4376,4496,4611,4614,4618,4628,4632,4752,33027,33029,33168,33283,33286,33290,33424,33797,33798,33804,33812,33936,34826,34828,34840,34960,2304,4352,4608,33024,33280,33792,34816,2823,2830,3335,3342,3356,4871,5383,5404,5639,5646,5660,6428,6670,6684,33543,34055,34311,34318,35342,35854,35868,37916,38940,2817,2818,2824,3329,3332,3336,4865,4866,4880,5377,5380,5392,5634,5636,5648,6401,6408,6416,6658,6664]
def m159Ws : List Wire := [mw 0xaaaaaaaa000000000000000000000000aaaaaaaa 0x38fff0191fe2c001c0ffc9e08c9fc0cf 0x82490382ca00022c118c8a00c0d4045,mw 0xcccccccc000000000000000000000000cccccccc 0xc71c70eee465001e3f001ee13764c330 0x410821fa6de0044e47095ae03524c110,mw 0xf0f0f0f0000000000000000000000000f0f0f0f0 0x7e38770fb8803e000003fe6587b0c00 0x2410fffffe009e48a32bfe2587b0400,mw 0xff00ff00000000000000000000000000ff00ff00 0xf803fb8703f07c000007f7786383f003 0x90024fc7d3401c881447374863829002,mw 0xffff0000000000000000000000000000ffff0000 0xfffc0c07fc0180003ff8279f83fc003c 0x24900e059200331138e4251f82d00028,mw 0xffffffff00000000000000000000000000000000 0xff8001e3fffc000381ffc003fc0 0x22112080001580002a80]
def m159Cuts : BTree CutSpec := (N (N (N (mc m159Raw 0xffff0000000000000000000000000000ffff 6) (mc m159Raw 0x5555555500000000000000000000000055555555 5)) (N (mc m159Raw 0x3333333300000000000000000000000033333333 6) (mc m159Raw 0x55005500000000000000000000000000550055 4))) (N (N (mc m159Raw 0xf0f0f0f0000000000000000000000000f0f0f0f 6) (mc m159Raw 0xf0f0f0f0 4)) (N (mc m159Raw 0xff00ff00000000000000000000000000ff00ff 5) (mc m159Raw 0x303030300000000000000000000000003030303 5))))
theorem m159CutValid : ∀ ci < 8, ValidCut m159Mask m159Raw m159Goal (btreeGet ⟨0,0,[]⟩ 3 m159Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 14681736 m143Low (by decide +kernel)
  · exact cv 14697992 m155Low (by decide +kernel)
  · exact cv 28947 m87Low (by decide +kernel)
  · exact cv 14696584 m151Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 1849344 m89Low (by decide +kernel)
def m159D : BTree NodeRec := (N (N (N (N (N (el 0 [0,1,2,3,4,5,6] [180226,311300,712710,4628488,4956170,7004172,9084942]) (e0 20549)) (N (ec 4134 [0,7]) E)) (N (N (ec 565 [0,1,2,3,4,5,6]) (e0 49184)) (N (ez 5205 [262184,2523172]) E))) (N (N (N (ec 38 [0,1,2,4,5,6]) (e0 41300)) (N (ef 4437 6 [2785316]) E)) (N (N (ec 855 [1,5]) E) (N (ef 12900 5 [4620324]) E)))) (N (N (N (N (el 22 [0,1,2,3,4,6] [311312,606226,2793492,4956182,9084952]) (e0 28730)) (N (e0 4170) E)) (N (N (el 605 [0,1,2,5] [303134,565280,4636694]) (e0 61512)) (N (e0 12376) E))) (N (N (N (el 87 [1,5,6] [720922,2523156,5013532]) (e0 45108)) (N (ez 4701 [426022]) E)) (N (N (el 1109 [0,1,2,5] [475170,2400284,4636696]) E) (N (ez 20517 [589866,2523174]) E)))))
def m159Ck : Nat → Bool := checkNode m159Mask m159Goal (Nat.sub (Nat.shiftLeft 1 m159Pairs.length) 1) id 22 7 m159Ws m159D 5 m159Cuts 3
theorem q11 : tb 0 22 m159Ck = true := by decide +kernel
theorem m159All : treeBlock 0 22 m159Ck = true := q11
theorem m159Low : LowerM m159Mask m159Raw m159Goal 8 := by
  have hraw : m159Ws.map Wire.val = m159Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 8)) m159D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m159Pairs) (sym := id) (count := 22) (rootFuel := 7) (fdepth := 5) (cdepth := 3) (dag := m159D) (cutTree := m159Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m159Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 8)) (defv := (0,[],[])) rfl hnc 5 i
      rw [hraw]; exact m159CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m159All

def m175Mask : Word := 0xffff0000ffff00000000000000000000ffff0000ffff
def m175Goal : Word := 0xffff0000fffe00000000000000000000fefc0000aa00
def m175Raw : List Word := [0xaaaa0000aaaa00000000000000000000aaaa0000aaaa, 0xcccc0000cccc00000000000000000000cccc0000cccc, 0xf0f00000f0f000000000000000000000f0f00000f0f0, 0xff000000ff0000000000000000000000ff000000ff00, 0xffff0000000000000000000000000000ffff00000000, 0xffff0000ffff00000000000000000000000000000000]
theorem m175Ess : ∀ a ∈ m175Raw, Essential m175Mask m175Goal m175Raw a :=
  checkAllEss_sound (ps := [2057,8226,8228,265,546,385]) (by decide +kernel)
theorem m175Low : LowerM m175Mask m175Raw m175Goal 9 := by
  have hsl : Slice m175Mask m175Raw m175Goal 0x33330000333300000000000000000000333300003333 8 :=
    checkSlice_sound (f := mr 7 0 0 0 2 0 5 3 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m217Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m175Ess hsl
  have hcnt : m175Raw.countP (isConst 0x33330000333300000000000000000000333300003333) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m183Mask : Word := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def m183Goal : Word := 0xff00ff00fe00fe000000000000000000fe00fc00ee0000
def m183Raw : List Word := [0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa, 0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc, 0xf000f000f000f0000000000000000000f000f000f000f0, 0xff000000ff0000000000000000000000ff000000ff0000, 0xff00ff00000000000000000000000000ff00ff00000000, 0xff00ff00ff00ff00000000000000000000000000000000]
theorem m183Ess : ∀ a ∈ m183Raw, Essential m183Mask m183Goal m183Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,385]) (by decide +kernel)
def m183Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,33025,33152,33282,33408,33796,33920,40992,41088,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,33539,34053,34310,37264,37520,37908,38032,41249,45104,45200,5895,9991,34567,4355,4357,4372,4385,4400,4496,4611,4614,4628,4656,4752,8707,8710,8737,8752,9221,9222,9236,9249,9264,33027,33029,33057,33168,33283,33286,33424,33797,33798,33812,33936,40993,41008,41104,4352,4608,8704,9216,33024,33280,33792,40960,4871,5383,5639,8967,9479,9735,33543,34055,34311,4865,4866,4880,5377,5380,5392,5634,5636,5648,8961,8962,8992,9473,9476,9504,9730,9732,9760,12545,12560,12576,12802,12816,12832,13316,13328,13344,33537,33538,33664,34049,34052,34176]
def m183Ws : List Wire := [mw 0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa 0xfc0e3f1fb6c4400f0003fe458de70303 0x24020904ffc008974a84be4185e30101,mw 0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc 0x1c71c7e3db49807007fc0e0a92790c3c 0x81042217fc00131118c1e0282290414,mw 0xf000f000f000f0000000000000000000f000f000f000f0 0xe381f8fc6d920780f8000e33639e30c0 0x408090487fc003a239186e13229e1040,mw 0xff000000ff0000000000000000000000ff000000ff0000 0x3fe00ff81c0c000007ff3bc7c1f000f 0x124009200003648a47341bc7814000a,mw 0xff00ff00000000000000000000000000ff00ff00000000 0x3ffff000e233800ff8005c07fe0c0f0 0x249240000001804c62180c05d4040a0,mw 0xff00ff00ff00ff00000000000000000000000000000000 0xfc000000703c3fff000009ff8000ff00 0x90000000000024480042012c0000aa00]
def m183Cuts : BTree CutSpec := (N (N (N (N (mc m183Raw 0x3300330033003300000000000000000033003300330033 7) (mc m183Raw 0xff00ff00ff00ff 5)) (N (mc m183Raw 0xf0000000f00000000000000000000000f0000000f 5) E)) (N (N (mc m183Raw 0xff000000ff0000000000000000000000ff000000ff 6) E) (N (mc m183Raw 0xff00ff00000000000000000000000000ff00ff 5) E))) (N (N (N (mc m183Raw 0x5500550055005500000000000000000055005500550055 7) (mc m183Raw 0x33003300000000000000000000000000330033 4)) (N (mc m183Raw 0x1100000011000000000000000000000011000000110000 4) E)) (N (N (mc m183Raw 0xf000f000f000f0000000000000000000f000f000f000f 6) E) (N (mc m183Raw 0xf000f000f000f 4) E))))
theorem m183CutValid : ∀ ci < 10, ValidCut m183Mask m183Raw m183Goal (btreeGet ⟨0,0,[]⟩ 4 m183Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1449991 m241Low (by decide +kernel)
  · exact cv 14860424 m182Low (by decide +kernel)
  · exact cv 14844040 m167Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
  · exact cv 1314823 m89Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 14696584 m151Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 28944 m86Low (by decide +kernel)
def m183D : BTree NodeRec := (N (N (N (N (N (N (el 0 [0,1,2,3,4,5] [4775938,4841476,4907014,4972552,6987786,7020556,9068558,9101328,9134098,9166868]) (ec 28740 [1,8,6,7,9])) (N (ef 5477 7 [2457694]) (e0 53556))) (N (N (el 1111 [0,1,2,3,8,6,5] [655434,671820,696342,720974,729168,737362,2793500,2826278,4890668,4923444,5029942,5095482]) (e0 32857)) (N (ez 16485 [327772,2424932]) E))) (N (N (N (el 607 [0,1,2,3,8,4] [688174,827440,892978,2990116,5021748]) (e1 28780 2)) (N (e0 9573) (e0 110696))) (N (N (ez 4201 [2916446]) (e1 41060 5)) (N (e1 20831 8) E)))) (N (N (N (N (el 591 [0,1,2,3,6,4,7] [827426,2990116,5021734,11313192]) (e1 28764 3)) (N (ez 8557 [295004,426084,2392162,2523238]) (e0 73780))) (N (N (el 1119 [0,1,2,3,8,6,7,5] [172116,819288,884826]) (ef 36901 7 [720988])) (N (ef 16997 3 [2556006]) E))) (N (N (N (el 857 [0,1,2,3,8,4,5] [2809914,2875452]) (ez 32850 [229468,688236])) (N (ef 12901 3 [2523232]) (e0 155732))) (N (N (ef 4709 3 [2523232]) (e0 45096)) (N (e0 24927) E))))) (N (N (N (N (N (el 583 [0,1,2,3,6,4,7] [827414,860184,2924570,5021724,5054494,11313184]) (ec 28756 [0,8,6])) (N (ez 8293 [327772,2424930]) (e0 69928))) (N (N (el 1115 [0,1,2,3,8,6,5] [303188,696406,2793502,5029944,5095484]) (e1 32858 3)) (N (e1 16493 6) E))) (N (N (N (el 853 [0,1,2,3,8,7,5] [2809910,2875448,9101344,9166888]) (e1 32848 3)) (N (e1 12397 6) (e0 118888))) (N (N (ef 4453 7 [2523232]) (e1 41068 2)) (N (ef 24919 4 [852074]) E)))) (N (N (N (N (el 599 [0,1,2,3,8,4,7] [827414,892970,2924570,5021740]) (e1 28772 5)) (N (ef 8805 3 [2556006]) (e0 74036))) (N (N (ez 4197 [327772]) (e0 36949)) (N (el 20823 [8,7] [852072]) E))) (N (N (N (el 1107 [0,1,2,3,8,6,7,5] [426046,557120,688194,753732,819270,884808]) (ef 32856 0 [4898920,4964458])) (N (e1 16468 5) E)) (N (N (e0 4713) (e0 49508)) (N (ec 28724 [0,8]) E))))))
def m183Ck : Nat → Bool := checkNode m183Mask m183Goal (Nat.sub (Nat.shiftLeft 1 m183Pairs.length) 1) id 55 8 m183Ws m183D 6 m183Cuts 4
theorem q12 : tb 0 24 m183Ck = true := by decide +kernel
theorem q13 : tb 24 24 m183Ck = true := by decide +kernel
theorem q14 : tb 48 7 m183Ck = true := by decide +kernel
theorem m183All : treeBlock 0 55 m183Ck = true := (tm 0 24 31 q12 (tm 24 24 7 q13 q14))
theorem m183Low : LowerM m183Mask m183Raw m183Goal 9 := by
  have hraw : m183Ws.map Wire.val = m183Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 10)) m183D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m183Pairs) (sym := id) (count := 55) (rootFuel := 8) (fdepth := 6) (cdepth := 4) (dag := m183D) (cutTree := m183Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m183Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 10)) (defv := (0,[],[])) rfl hnc 6 i
      rw [hraw]; exact m183CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m183All

def m187Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def m187Goal : Word := 0xf0f0f0f0f0e0f0e00000000000000000e0e0e0c0e0e0a00
def m187Raw : List Word := [0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c, 0xf000f000f000f0000000000000000000f000f000f000f00, 0xf0f00000f0f000000000000000000000f0f00000f0f0000, 0xf0f0f0f0000000000000000000000000f0f0f0f00000000, 0xf0f0f0f0f0f0f0f00000000000000000000000000000000]
theorem m187Ess : ∀ a ∈ m187Raw, Essential m187Mask m187Goal m187Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,385]) (by decide +kernel)
theorem m187Low : LowerM m187Mask m187Raw m187Goal 9 := by
  have hsl : Slice m187Mask m187Raw m187Goal 0xf0f00000f0f000000000000000000000f0f00000f0f 8 :=
    checkSlice_sound (f := mr 7 0 0 0 1 0 5 3 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m217Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m187Ess hsl
  have hcnt : m187Raw.countP (isConst 0xf0f00000f0f000000000000000000000f0f00000f0f) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m190Mask : Word := 0x555555555555555500000000000000005555555555555555
def m190Goal : Word := 0x555555555554555400000000000000005454545444440000
def m190Raw : List Word := [0x444444444444444400000000000000004444444444444444, 0x505050505050505000000000000000005050505050505050, 0x550055005500550000000000000000005500550055005500, 0x555500005555000000000000000000005555000055550000, 0x555555550000000000000000000000005555555500000000, 0x555555555555555500000000000000000000000000000000]
theorem m190Ess : ∀ a ∈ m190Raw, Essential m190Mask m190Goal m190Raw a :=
  checkAllEss_sound (ps := [4114,8228,32904,530,546,642]) (by decide +kernel)
theorem m190Low : LowerM m190Mask m190Raw m190Goal 8 := by
  have hsl : Slice m190Mask m190Raw m190Goal 0x5500550055005500000000000000000055005500550055 7 :=
    checkSlice_sound (f := mr 0 1 2 0 4 5 0 7 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m182Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m190Ess hsl
  have hcnt : m190Raw.countP (isConst 0x5500550055005500000000000000000055005500550055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m215Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def m215Goal : Word := 0xff00fe0000000000fe00fe0000000000ff00fa0000000000ee0000
def m215Raw : List Word := [0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa, 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc, 0xf000f00000000000f000f00000000000f000f00000000000f000f0, 0xff00000000000000ff00000000000000ff00000000000000ff0000, 0xff00ff00000000000000000000000000ff00ff0000000000000000, 0xff00ff0000000000ff00ff00000000000000000000000000000000]
theorem m215Ess : ∀ a ∈ m215Raw, Essential m215Mask m215Goal m215Raw a :=
  checkAllEss_sound (ps := [4113,4114,16452,273,321,385]) (by decide +kernel)
def m215Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,4867,5381,5396,5638,5652,17155,17218,17669,17926,17986,21058,21524,33539,34053,34310,37264,37520,37908,38032,49600,49730,49856,50368,53392,53440,5895,18183,34567,4355,4357,4372,4496,4611,4614,4628,4674,4752,16643,16645,16706,16832,17413,17414,17428,17474,17600,20500,20546,20624,20672,33027,33029,33168,33216,33283,33286,33346,33424,33472,33797,33798,33812,33936,33984,4352,4608,16640,17408,20480,33024,33280,33792,4871,5383,5639,17159,17671,17927,33543,34055,34311,4865,4866,4880,5377,5380,5392,5634,5636,5648,17153,17154,17216,17665,17668,17728,17922,17924,17984,20737,20752,20800,20994,21008,21056,21508,21520,21568,33537,33538,33664,34049]
def m215Ws : List Wire := [mw 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa 0xf038fc7edb25003c01e0fe08b0e70c33 0x90082413ff00084c02613e0030a30411,mw 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc 0x71c71f8f6d4207c0001f0e315779300c 0x20410885ff0011c494ab1e1057691004,mw 0xf000f00000000000f000f00000000000f000f00000000000f000f0 0x8e07e3f1b688f8003e000e466b9ec0c0 0x2024121ff0038884e466e02699e4040,mw 0xff00000000000000ff00000000000000ff00000000000000ff0000 0xff803fe07130003c01ff3878c1f030f 0x4900248000062114814c0878814010a,mw 0xff00ff00000000000000000000000000ff00ff0000000000000000 0xffffc00381c0003ffe005f80fe003f0 0x924900000008522b1880178064002a0,mw 0xff00ff0000000000ff00ff00000000000000000000000000000000 0xf0000001c0e0fffc000009fff000fc00 0x400000000000c633211081ed8000a800]
def m215Cuts : BTree CutSpec := (N (N (N (N (mc m215Raw 0x550055000000000055005500000000005500550000000000550055 7) (mc m215Raw 0x33003300000000000000000000000000330033 4)) (N (mc m215Raw 0xf000f00000000000f000f 5) E)) (N (N (mc m215Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6) (mc m215Raw 0xf000000000000000f000000000000000f000000000000000f 4)) (N (mc m215Raw 0x30003000000000003000300000000000300030000000000030003 5) E))) (N (N (N (mc m215Raw 0xff00ff0000000000ff00ff 6) (mc m215Raw 0xff00ff00000000000000000000000000ff00ff 5)) (N (mc m215Raw 0x3300330000000000330033 5) E)) (N (N (mc m215Raw 0x330033000000000033003300000000003300330000000000330033 6) (mc m215Raw 0x55005500000000000000000000000000550055 4)) (N (mc m215Raw 0xff00000000000000ff00000000000000ff00000000000000ff 5) E))))
theorem m215CutValid : ∀ ci < 12, ValidCut m215Mask m215Raw m215Goal (btreeGet ⟨0,0,[]⟩ 4 m215Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
  · exact cv 12613648 m155Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 1049606 m89Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
  · exact cv 14704720 m151Low (by decide +kernel)
  · exact cv 28944 m86Low (by decide +kernel)
  · exact cv 14696584 m151Low (by decide +kernel)
  · exact cv 29064 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
def m215D : BTree NodeRec := (N (N (N (N (N (N (el 0 [0,1,2,3,4,5,6] [2547714,2613252,2678790,2744328,4644871,4710409,4775939,4841477,6840330,6873100,6905870,6938639,7004176,7036946,9101329,9134099]) (ef 28773 5 [720996])) (N (e0 16469) (e0 114760))) (N (N (el 855 [0,1,2,3,4,5,7] [589894,606280,794698,827448,860236,893006,2891828,2990147,5021776]) (el 33381 [4,5] [262246,2490462])) (N (e0 20581) E))) (N (N (N (el 335 [0,1,2,3,5,9,6] [696352,761890,819236,4890662]) (e1 32842 3)) (N (el 20532 [9,7,8,11] [2793560,4890713]) (e0 180532))) (N (N (e1 4437 8) (ez 82261 [2523240])) (N (el 24677 [0,4,5] [589920,720994,852067]) E)))) (N (N (N (N (el 319 [0,1,2,3,5,7,6,8] [696346]) (e0 29289)) (N (e1 16484 0) (e0 131160))) (N (N (e0 4181) (e1 36965 1)) (N (ef 20837 1 [2523230,4751448,4882522,5013597]) E))) (N (N (N (el 839 [0,1,2,3,9,7] [565268,598070,696341,729143,827448,860218,2793503,2826279,4759582,4792358]) (e1 32873 1)) (N (e1 20556 3) E)) (N (N (e1 12381 7) (ez 86613 [2523242])) (N (e0 28709) E))))) (N (N (N (N (N (el 311 [0,1,2,3,5,7,6,8] [696340,729110,2793496]) (e1 29285 1)) (N (e1 16477 7) (e0 114776))) (N (N (el 859 [0,1,2,3,4,5,7] [688210,827476,893014,2990149]) (e1 36948 0)) (N (e1 20588 1) E))) (N (N (N (el 835 [0,1,2,3,9,7,8,10] [426024,557098,622636,688171,753709,819246,827440,884786,2924596,5021749]) (e1 32865 9)) (N (el 20548 [0,9,7] [2793562,4890716]) (e0 184628))) (N (N (e0 8277) (ez 86357 [2523242])) (N (e0 24681) E)))) (N (N (N (N (el 327 [0,1,2,3,5,9,6,8] [696340,761884,2793496,4890654]) (e1 32840 0)) (N (e0 16981) (e1 163872 9))) (N (N (e0 4185) (e1 36973 9)) (N (e0 24649) E))) (N (N (N (el 843 [0,1,2,3,9,7,10] [303164,565310,827456,5021762,5054532]) (e1 32877 9)) (N (e1 20580 0) E)) (N (N (e1 12885 3) (ez 106804 [4620392,4751466,4882539])) (N (e0 28741) E))))))
def m215Ck : Nat → Bool := checkNode m215Mask m215Goal (Nat.sub (Nat.shiftLeft 1 m215Pairs.length) 1) symMain 54 8 m215Ws m215D 6 m215Cuts 4
theorem q15 : tb 0 24 m215Ck = true := by decide +kernel
theorem q16 : tb 24 24 m215Ck = true := by decide +kernel
theorem q17 : tb 48 6 m215Ck = true := by decide +kernel
theorem m215All : treeBlock 0 54 m215Ck = true := (tm 0 24 30 q15 (tm 24 24 6 q16 q17))
theorem m215Low : LowerM m215Mask m215Raw m215Goal 9 := by
  have hraw : m215Ws.map Wire.val = m215Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 12)) m215D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m215Pairs) (sym := symMain) (count := 54) (rootFuel := 8) (fdepth := 6) (cdepth := 4) (dag := m215D) (cutTree := m215Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m215Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 12)) (defv := (0,[],[])) rfl hnc 6 i
      rw [hraw]; exact m215CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m215All

def m222Mask : Word := 0x55555555000000005555555500000000555555550000000055555555
def m222Goal : Word := 0x55555554000000005554555400000000555550500000000044440000
def m222Raw : List Word := [0x44444444000000004444444400000000444444440000000044444444, 0x50505050000000005050505000000000505050500000000050505050, 0x55005500000000005500550000000000550055000000000055005500, 0x55550000000000005555000000000000555500000000000055550000, 0x55555555000000000000000000000000555555550000000000000000, 0x55555555000000005555555500000000000000000000000000000000]
theorem m222Ess : ∀ a ∈ m222Raw, Essential m222Mask m222Goal m222Raw a :=
  checkAllEss_sound (ps := [4114,16452,32904,530,1092,642]) (by decide +kernel)
theorem m222Low : LowerM m222Mask m222Raw m222Goal 8 := by
  have hsl : Slice m222Mask m222Raw m222Goal 0x550055000000000055005500000000005500550000000000550055 7 :=
    checkSlice_sound (f := mr 0 1 2 0 4 7 6 0 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m118Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m222Ess hsl
  have hcnt : m222Raw.countP (isConst 0x550055000000000055005500000000005500550000000000550055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m243Mask : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def m243Goal : Word := 0xf000f000f000e000f000f000e000e000f000e000f000a000e000c000e0000
def m243Raw : List Word := [0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000, 0xf000f00000000000f000f00000000000f000f00000000000f000f00000000, 0xf000f000f000f0000000000000000000f000f000f000f0000000000000000, 0xf000f000f000f000f000f000f000f00000000000000000000000000000000]
theorem m243Ess : ∀ a ∈ m243Raw, Essential m243Mask m243Goal m243Raw a :=
  checkAllEss_sound (ps := [4113,4114,273,546,321,385]) (by decide +kernel)
def m243Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,16641,16704,20496,20544,33025,33152,33282,33408,40992,41088,4867,8963,8993,12577,12592,12848,17155,17218,21058,24865,24928,25154,25184,28720,28768,33539,37264,37520,41249,45104,45200,49600,49730,49856,53392,53440,57440,57536,4355,4385,4400,4496,4611,4656,4674,4752,8707,8737,8752,8770,8800,16643,16673,16706,16736,16832,20528,20546,20576,20624,20672,33027,33057,33168,33216,33283,33346,33424,33472,40993,41008,41056,41104,41152,4352,4608,8704,16640,20480,33024,33280,40960,4865,4866,4880,8961,8962,8992,12545,12560,12576,12802,12816,12832,17153,17154,17216,20737,20752,20800,20994,21008,21056,24833,24864,24896,25090,25120,25152,28688,28704,28736,33537,33538,33664,37121,37136,37248,37378,37392,37504,41217]
def m243Ws : List Wire := [mw 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a 0x8fc0e3f1ff2900783e00f02586df0cc3 0x824020904900089806313004824f0441,mw 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c 0x71c71c7e3f46078001ff00c299e7303c 0x10810422120001888a95104089c31014,mw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000 0x7e381f8fc7130007c00ff31b6139030f 0x2408090484005222404ac11b2030010a,mw 0xf000f00000000000f000f00000000000f000f00000000000f000f00000000 0x803fe00ff884f80001f00c1c7e3ec030 0x124009200038115562640c763c4020,mw 0xf000f000f000f0000000000000000000f000f000f000f0000000000000000 0x3ffff000180007fe000fe07fc003c0 0x2492400000a545b9840ee05d800280,mw 0xf000f000f000f000f000f000f000f00000000000000000000000000000000 0xffc0000000e0fff800000fff8000fc00 0x490000000000c66620088bb30000a800]
def m243Cuts : BTree CutSpec := (N (N (N (mc m243Raw 0xf000f000f000f000f000f000f000f 7) (mc m243Raw 0xf000f000f000f0000000000000000000f000f000f000f 6)) (N (mc m243Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) (mc m243Raw 0x30003000000000003000300000000 4))) (N (N (mc m243Raw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f 7) (mc m243Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6)) (N (mc m243Raw 0x5000500050005000500050005000500050005000500050005000500050005 7) E)))
theorem m243CutValid : ∀ ci < 7, ValidCut m243Mask m243Raw m243Goal (btreeGet ⟨0,0,[]⟩ 3 m243Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 1511431 m241Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 10440705 m241Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
def m243D : BTree NodeRec := (ec 0 [0,1,2,3,4,5,6])
def m243Ck : Nat → Bool := checkNode m243Mask m243Goal (Nat.sub (Nat.shiftLeft 1 m243Pairs.length) 1) id 1 8 m243Ws m243D 0 m243Cuts 3
theorem q18 : tb 0 1 m243Ck = true := by decide +kernel
theorem m243All : treeBlock 0 1 m243Ck = true := q18
theorem m243Low : LowerM m243Mask m243Raw m243Goal 9 := by
  have hraw : m243Ws.map Wire.val = m243Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 7)) m243D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m243Pairs) (sym := id) (count := 1) (rootFuel := 8) (fdepth := 0) (cdepth := 3) (dag := m243D) (cutTree := m243Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m243Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 7)) (defv := (0,[],[])) rfl hnc 0 i
      rw [hraw]; exact m243CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m243All

def m246Mask : Word := 0x55005500550055005500550055005500550055005500550055005500550055
def m246Goal : Word := 0x55005500550054005500550054005400550054005500500054005400440000
def m246Raw : List Word := [0x44004400440044004400440044004400440044004400440044004400440044, 0x50005000500050005000500050005000500050005000500050005000500050, 0x55000000550000005500000055000000550000005500000055000000550000, 0x55005500000000005500550000000000550055000000000055005500000000, 0x55005500550055000000000000000000550055005500550000000000000000, 0x55005500550055005500550055005500000000000000000000000000000000]
theorem m246Ess : ∀ a ∈ m246Raw, Essential m246Mask m246Goal m246Raw a :=
  checkAllEss_sound (ps := [4114,8228,530,546,1092,642]) (by decide +kernel)
def m246Pairs : List (Row × Row) := mkPairs [4610,4624,8706,8736,9220,9248,17412,17472,20496,20544,33282,33408,33796,33920,40992,41088,5638,5652,9734,12848,13332,13360,17926,17986,21058,21524,25154,25184,25696,28720,28768,34310,37520,37908,38032,45104,45200,49730,49856,50368,53392,53440,57440,57536,4614,4628,4656,4674,4752,8710,8752,8770,8800,9222,9236,9264,9312,17414,17428,17474,17504,17600,20500,20528,20546,20576,20624,20672,33286,33346,33424,33472,33798,33812,33936,33984,41008,41056,41104,41152,4608,8704,9216,17408,20480,33280,33792,40960,5634,5636,5648,9730,9732,9760,12802,12816,12832,13316,13328,13344,17922,17924,17984,20994,21008,21056,21508,21520,21568,25090,25120,25152,25604,25632,25664,28688,28704,28736,34306,34308,34432,37378,37392,37504,37892,37904,38016,41474]
def m246Ws : List Wire := [mw 0x44004400440044004400440044004400440044004400440044004400440044 0x8fc0e3f1ff2300f0001ff0618dcf0c0f 0x82402090490001310a2a902085c50405,mw 0x50005000500050005000500050005000500050005000500050005000500050 0x71c71c7e3f4c0f003fe0008692f730f0 0x10810422120003104662300282571050,mw 0x55000000550000005500000055000000550000005500000055000000550000 0x7e381f8fc711000fc001f31f633b0303 0x2408090484005644c4c5611f223a0102,mw 0x55005500000000005500550000000000550055000000000055005500000000 0x803fe00ff886f00001fe0c187c3cc03c 0x124009200030029194440878284028,mw 0x55005500550055000000000000000000550055005500550000000000000000 0x3ffff00018000ffe000fe07fc003c0 0x2492400000a8ab39188ee05d800280,mw 0x55005500550055005500550055005500000000000000000000000000000000 0xffc0000000e0fff000000fff8000fc00 0x490000000000cccc20010bd50000a800]
def m246Cuts : BTree CutSpec := (N (N (N (N (N (mc m246Raw 0x550055005500550055005500550055 7) (mc m246Raw 0x55005500000000000000000000000000550055 4)) (N (mc m246Raw 0x1100000011000000110000001100000011000000110000001100000011 5) E)) (N (N (mc m246Raw 0x5000500050005000500050005000500050005000500050005000500050005 7) E) (N (mc m246Raw 0x55000000550000005500000055 4) E))) (N (N (N (mc m246Raw 0x550055000000000055005500000000005500550000000000550055 7) (mc m246Raw 0x55005500550055 4)) (N (mc m246Raw 0x110011001100110011001100110011 4) E)) (N (N (mc m246Raw 0x500000005000000000000000000000005000000050000000000000000 4) E) (N (mc m246Raw 0x50005000000000005000500000000000500050000000000050005 4) E)))) (N (N (N (N (mc m246Raw 0x5500550055005500000000000000000055005500550055 7) (mc m246Raw 0x110000001100000000000000000000001100000011 4)) (N (mc m246Raw 0x110011000000000011001100000000001100110000000000110011 4) E)) (N (N (mc m246Raw 0x11001100110011001100110011001100110011001100110011001100110011 7) E) (N (mc m246Raw 0x5500550000000000550055 4) E))) (N (N (N (mc m246Raw 0x5500000055000000550000005500000055000000550000005500000055 7) (mc m246Raw 0x55000000000000005500000000000000550000000000000055 4)) (N (mc m246Raw 0x550000005500000000000000000000005500000055 5) E)) (N (N (mc m246Raw 0x1100000011000000000000000000000011000000110000 4) E) (N (mc m246Raw 0x50005000500050005000500050005 4) E)))))
theorem m246CutValid : ∀ ci < 20, ValidCut m246Mask m246Raw m246Goal (btreeGet ⟨0,0,[]⟩ 5 m246Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1753224 m118Low (by decide +kernel)
  · exact cv 14860424 m182Low (by decide +kernel)
  · exact cv 1818760 m118Low (by decide +kernel)
  · exact cv 14868560 m182Low (by decide +kernel)
  · exact cv 10440705 m241Low (by decide +kernel)
  · exact cv 14569474 m241Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 1858562 m89Low (by decide +kernel)
  · exact cv 549344 m86Low (by decide +kernel)
  · exact cv 549216 m86Low (by decide +kernel)
  · exact cv 14844040 m166Low (by decide +kernel)
  · exact cv 545160 m86Low (by decide +kernel)
  · exact cv 1589384 m86Low (by decide +kernel)
  · exact cv 279024 m86Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 1855490 m81Low (by decide +kernel)
  · exact cv 282896 m86Low (by decide +kernel)
  · exact cv 553352 m86Low (by decide +kernel)
noncomputable def m246D : BTree NodeRec := (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5] [188418,319492,450566,581640,712714,2416649,2547719,2678789,2809867,4644876,4775950,4907024,6873101,7004178,9101329]) (e0 200789)) (N (e1 41066 0) E)) (N (N (el 12645 [0,2,5,10,7,9] [565408,598228,2523350,4759684,4792516]) E) (N (e0 98424) E))) (N (N (N (el 4201 [0,1,2,3,4,5,6,7] [180370,696486,729228,4890792,6987945]) (e1 442416 15)) (N (ef 57941 2 [2523416]) E)) (N (N (el 24649 [0,1,2,3,4,5,6,7,19] [827646]) E) (N (e1 143408 18) E)))) (N (N (N (N (el 599 [0,1,2,3,4,5,12,6,7] [598118,729192,9101383]) (e0 245788)) (N (e0 53812) E)) (N (N (el 20537 [0,1,2,3,4,5,10,6,7] [696560,4890836,6988018]) E) (N (e1 127077 6) E))) (N (N (N (el 12343 [4,14,9] [590012,917694,983232]) E) (N (ez 74085 [2523416,2654490]) E)) (N (N (el 36951 [0,3,13,12,19] [655626,721164]) E) (N (e0 163925) E))))) (N (N (N (N (N (el 71 [0,1,2,3,4,5,6,7] [524360,589898,11329612]) (e1 221285 6)) (N (e0 45176) E)) (N (N (e1 16448 3) E) (N (e0 118857) E))) (N (N (N (el 5223 [0,2,4,5] [393400,426106,458938,491660,557228,688301,2523266,2654384,2785457,4620446,4751542,4882615]) E) (N (e1 66133 2) E)) (N (N (el 32857 [0,1,2,3,4,5,12,6,7] [696580]) E) (N (e1 156528 3) E)))) (N (N (N (N (el 4169 [0,1,2,3,4,5,6,7] [180340,827530,860300,5021838,7118991]) (e1 323892 2)) (N (e0 57432) E)) (N (N (ec 20583 [1,18,10,7,17]) E) (N (ez 135493 [393504,557336,2523413,2654490]) E))) (N (N (N (e1 12377 6) E) (N (e1 81968 13) E)) (N (N (ez 41058 [229648,2425102]) E) (N (e1 172389 1) E)))))) (N (N (N (N (N (N (el 39 [0,1,2,3,4,5,8,6,7] [6873130,7135276,9232430]) (e0 213077)) (N (ef 41573 0 [2523412]) E)) (N (N (el 13159 [4,5] [393434,426106,458972,491742,557216,2523269,2654386,4882648]) E) (N (ez 103013 [2654492]) E))) (N (N (N (el 4421 [1,2,3,4,5,6,7,9] [827564,860334,2465936,2924720,5021856,5054632,7119026]) E) (N (e0 61544) E)) (N (N (ec 30055 [0,11,6]) E) (N (e1 152663 0) E)))) (N (N (N (N (el 4165 [0,1,2,3,4,5,6,7,14,9] [213108,786550,802936,827514,852092,860286,868480,2924674,5021828,7118981]) (e1 266548 0)) (N (e1 57424 2) E)) (N (N (el 20569 [0,1,2,3,4,5,10,7] [565492,827638,2924792,4759732]) E) (N (ez 131145 [4751646]) E))) (N (N (N (e1 12373 6) E) (N (e1 77913 4) E)) (N (N (ef 40986 2 [2883854]) E) (N (e1 172101 4) E))))) (N (N (N (N (N (el 567 [0,1,2,3,4,5,6,7] [598112,860258,9232479]) (e1 229464 0)) (N (e1 49257 0) E)) (N (N (el 17767 [0,1,5,6,7] [590054,7209192,7274724]) E) (N (e1 118889 6) E))) (N (N (N (ec 9063 [8,7]) E) (N (e1 73829 4) E)) (N (N (el 36921 [0,1,2,3,4,5,13,7] [565510,827656,2924774]) E) (N (e1 159840 2) E)))) (N (N (N (N (el 4197 [0,1,2,3,4,5,15,10,6,7] [213138,655508,671894,696442,721048,729242,737436,2793630,4890784,6987937]) (e0 401732)) (N (e1 57434 2) E)) (N (N (el 21077 [0,2,5,13,10,7] [2523350,2662617,4759710,4792562,6856886]) E) (N (e1 139320 15) E))) (N (N (N (ec 12391 [0,13,10,9]) E) (N (e1 98376 2) E)) (N (N (e0 41064) E) (N (e1 192568 16) E))))))) (N (N (N (N (N (N (N (el 23 [0,1,2,3,4,5,6,7] [565268,581654,598040,614426,827420,843806,860192,876578,2662436,2924582,4759589,5021735,9232424]) (e0 208981)) (N (ef 41317 0 [2523412,2654485]) E)) (N (N (el 12901 [0,2,5,13,7,9] [2523350,2662616,4759682,4792518,6856880]) E) (N (e0 102501) E))) (N (N (N (el 4203 [0,4,5] [2392210,4620458,4751531]) (e1 471904 3)) (N (e1 61536 2) E)) (N (N (el 24681 [0,1,2,3,4,5,6,7,19] [696576]) E) (N (e1 143416 18) E)))) (N (N (N (N (el 855 [0,1,2,3,4,5,13] [434234,450666,467052,565307,581739,598125,696430,712816,729202,827503,843889,860275,2531394,2662467,4628572,4759645,6873128,7004206,7135308,9101389,9232431,11329636]) (e0 249896)) (N (ef 57370 0 [2752790]) E)) (N (N (ec 20567 [2,13,10,9]) E) (N (e1 127333 1) E))) (N (N (N (el 12345 [0,1,2,3,4,5,6,7,9] [827586,5021892,7119046]) E) (N (ez 74597 [2523418]) E)) (N (N (e1 36953 7) E) (N (ef 164693 2 [2654494]) E))))) (N (N (N (N (N (el 87 [0,1,2,3,4,5,10,7] [434204,450638,467024,696378,712786,729172,827478,843864,860250,2531366,2793536,4890716,7004229,7135277,11329630]) (e1 229456 5)) (N (e1 49253 0) E)) (N (N (el 16456 [0,1,2,3,4,5,6] [9101540]) E) (N (e1 118885 6) E))) (N (N (N (ec 9031 [8,7]) E) (N (e0 70196) E)) (N (N (ec 36919 [0,5,13,10,9]) E) (N (e1 159816 0) E)))) (N (N (N (N (el 4171 [2,4,5] [2392180,4620432,4751505]) (e0 360772)) (N (e0 57433) E)) (N (N (e1 20585 6) E) (N (e1 139312 15) E))) (N (N (N (el 12389 [0,1,2,3,4,5,13,10,7,9] [565370,598216,827594,860364,4759724]) E) (N (e1 81976 13) E)) (N (N (ez 41061 [196880,327954]) E) (N (e1 192560 10) E)))))) (N (N (N (N (N (N (el 55 [0,1,2,3,4,5,7,9] [434196,450608,466994,696372,712758,729144,827450,843836,860222,2531364,2924608,5021762,7004203,7135300,11329606]) (e0 221253)) (N (e1 45168 0) E)) (N (N (el 13671 [0,1,6] [393440,458978,4686034]) E) (N (ef 103269 0 [2654492]) E))) (N (N (N (el 4453 [0,1,3,4,5,10,6,7] [696492,729268,2465962,2793654,4890756,4923534,6987955]) E) (N (e1 65621 2) E)) (N (N (el 32841 [0,1,2,3,4,5,12,6,7] [696578]) E) (N (ef 155720 1 [7078178]) E)))) (N (N (N (N (el 4167 [2,14,9] [917638,983176,2424948]) (e0 299344)) (N (ez 57426 [229650,2425110]) E)) (N (N (e1 20581 6) E) (N (el 131380 [0,2,5,7] [2531608,2564382,4628756,4661532]) E))) (N (N (N (ec 12375 [1,16,6,7,17]) E) (N (ez 78165 [2523412,2654491]) E)) (N (N (e1 41056 0) E) (N (e1 172133 6) E))))) (N (N (N (N (N (el 583 [0,1,2,3,4,5,11,6,7] [11329636]) (e0 237920)) (N (e1 49765 0) E)) (N (N (el 20535 [4,15,10] [590058,786668,852206]) E) (N (e1 127045 4) E))) (N (N (N (ec 9319 [0,3,8,7]) E) (N (e1 73833 4) E)) (N (N (e1 36949 7) E) (N (e0 159848) E)))) (N (N (N (N (el 4199 [0,15,10] [786594,852132,2424978]) (e0 434756)) (N (ef 57685 2 [2523416,2654489]) E)) (N (N (el 21863 [1,2,6] [393466,459004,2588920]) E) (N (e1 139324 9) E))) (N (N (N (el 12393 [0,1,2,3,4,5,7,9] [565454,827600,2924754,4759726]) E) (N (e1 98416 0) E)) (N (N (e0 41065) E) (N (e0 196709) E))))))))
noncomputable def m246Ck : Nat → Bool := checkNode m246Mask m246Goal (Nat.sub (Nat.shiftLeft 1 m246Pairs.length) 1) symMain 146 9 m246Ws m246D 8 m246Cuts 5
theorem q19 : tb 0 24 m246Ck = true := by decide +kernel
theorem q20 : tb 24 24 m246Ck = true := by decide +kernel
theorem q21 : tb 48 24 m246Ck = true := by decide +kernel
theorem q22 : tb 72 24 m246Ck = true := by decide +kernel
theorem q23 : tb 96 24 m246Ck = true := by decide +kernel
theorem q24 : tb 120 24 m246Ck = true := by decide +kernel
theorem q25 : tb 144 2 m246Ck = true := by decide +kernel
theorem m246All : treeBlock 0 146 m246Ck = true := (tm 0 72 74 (tm 0 24 48 q19 (tm 24 24 24 q20 q21)) (tm 72 48 26 (tm 72 24 24 q22 q23) (tm 120 24 2 q24 q25)))
theorem m246Low : LowerM m246Mask m246Raw m246Goal 10 := by
  have hraw : m246Ws.map Wire.val = m246Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 20)) m246D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m246Pairs) (sym := symMain) (count := 146) (rootFuel := 9) (fdepth := 8) (cdepth := 5) (dag := m246D) (cutTree := m246Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m246Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 20)) (defv := (0,[],[])) rfl hnc 8 i
      rw [hraw]; exact m246CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m246All

def m249Mask : Word := 0x303030303030303030303030303030303030303030303030303030303030303
def m249Goal : Word := 0x303030303030302030303030302030203030202030302020202020002020200
def m249Raw : List Word := [0x202020202020202020202020202020202020202020202020202020202020202, 0x300030003000300030003000300030003000300030003000300030003000300, 0x303000003030000030300000303000003030000030300000303000003030000, 0x303030300000000030303030000000003030303000000000303030300000000, 0x303030303030303000000000000000003030303030303030000000000000000, 0x303030303030303030303030303030300000000000000000000000000000000]
theorem m249Ess : ∀ a ∈ m249Raw, Essential m249Mask m249Goal m249Raw a :=
  checkAllEss_sound (ps := [2057,265,273,32928,321,385]) (by decide +kernel)
theorem m249Low : LowerM m249Mask m249Raw m249Goal 9 := by
  have hsl : Slice m249Mask m249Raw m249Goal 0x3030303000000000303030300000000030303030000000003030303 8 :=
    checkSlice_sound (f := mr 0 0 0 3 4 0 6 7 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m217Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m249Ess hsl
  have hcnt : m249Raw.countP (isConst 0x3030303000000000303030300000000030303030000000003030303) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m127Mask : Word := 0xffffffffffffffffffffffffffffffff
def m127Goal : Word := 0xfffffefefffffafafefefefceeeeaa00
def m127Raw : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
theorem m127Ess : ∀ a ∈ m127Raw, Essential m127Mask m127Goal m127Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,321]) (by decide +kernel)
def m127Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,24865,24928,25154,25184,25696,28720,28768,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,18183,19274,19982,20042,23114,23580,26984,27210,27240,27752,30776,30824,2307,2309,2314,2316,2328,2337,2344,2376,4355,4357,4372,4376,4385,4400,4611,4614,4618,4628,4632,4656,4674,8707,8710,8714,8737,8744,8752,8770,8800,9221,9222,9228,9236,9249,9256,9264,9312,16643,16645,16673,16706]
def m127Ws : List Wire := [mw 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 0xf000001fff8218a783027186f27f0c0f 0x711090299180082281005082f0350405,mw 0xcccccccccccccccccccccccccccccccc 0xfffe0000cf97b8c11b2193d9300f0 0x902478e08284f86b8411b00914930050,mw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 0xff0000000116e7f902dcc61c1ec3300 0x20f0214305012a7f8024c42141ec1100,mw 0xff00ff00ff00ff00ff00ff00ff00ff00 0x7ffff7dd80ce007e0e0f0003 0x24142846e7ff7dd00ce007c0e0a0002,mw 0xffff0000ffff0000ffff0000ffff0000 0xfff8061879e60f00f800ff0c03c 0x48207160821079420600f000b404028,mw 0xffffffff00000000ffffffff00000000 0xffff000007e07e07f000ffff00003c0 0x4f0b8418307a05807b000bd6a0000280,mw 0xffffffffffffffff0000000000000000 0xf0000000007ff8007ffff0000000fc00 0x880c0800405ed0005e9b20000000a800]
def m127Cuts : BTree CutSpec := (N (N (N (N (N (mc m127Raw 0xff00ff00ff00ff00ff00ff00ff00ff 9) (mc m127Raw 0x5000500050005000500050005000500 4)) (N (mc m127Raw 0xffff0000ffff0000ffff0000ffff 7) (mc m127Raw 0xf000f000f000f000f000f000f000f 7))) (N (N (mc m127Raw 0x55005500550055005500550055005500 7) (mc m127Raw 0x33000000330000003300000033 4)) (N (mc m127Raw 0x333333330000000033333333 6) E))) (N (N (N (mc m127Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 8) (mc m127Raw 0xf0f0f0f000000000f0f0f0f 6)) (N (mc m127Raw 0xf0f0f0f0 4) (mc m127Raw 0xff00ff0000000000ff00ff 6))) (N (N (mc m127Raw 0xcccc000000000000cccc 4) (mc m127Raw 0xff000000ff000000ff000000ff 5)) (N (mc m127Raw 0x30303030000000003030303 5) E)))) (N (N (N (N (mc m127Raw 0xffffffff00000000ffffffff 8) (mc m127Raw 0x550055000000000055005500 4)) (N (mc m127Raw 0x5500000055000000550000005500 4) (mc m127Raw 0x330033003300330033003300330033 7))) (N (N (mc m127Raw 0x3030303000000000303030300000000 5) (mc m127Raw 0xf0f0f0f0f0f0f0f 5)) (N (mc m127Raw 0xffffffffffffffff 7) E))) (N (N (N (mc m127Raw 0x33333333333333333333333333333333 8) (mc m127Raw 0x33330000000000003333 4)) (N (mc m127Raw 0x3333000033330000333300003333 5) E)) (N (N (mc m127Raw 0x11001100110011001100110011001100 4) (mc m127Raw 0xff00ff00ff00ff 5)) (N (mc m127Raw 0x5500550055005500 4) E)))))
theorem m127CutValid : ∀ ci < 27, ValidCut m127Mask m127Raw m127Goal (btreeGet ⟨0,0,[]⟩ 5 m127Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 1753224 m119Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 1754632 m123Low (by decide +kernel)
  · exact cv 1238544 m123Low (by decide +kernel)
  · exact cv 135970952 m118Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 134766944 m86Low (by decide +kernel)
  · exact cv 190032 m63Low (by decide +kernel)
  · exact cv 134762888 m86Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 65907 m55Low (by decide +kernel)
  · exact cv 24788 m87Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 1590784 m89Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 135270824 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 16590 m87Low (by decide +kernel)
  · exact cv 24784 m86Low (by decide +kernel)
  · exact cv 549184 m86Low (by decide +kernel)
  · exact cv 33123 m55Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
noncomputable def m127D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4] [188418,319491,475140,581638,647176,712714,843783,909321,2416652,2678798,2744336,2809874,2940948,3006486,4775957,4841495,4907027,5038095,5103633,6856728,7118873,9101338,9134108,9199646,9232416,9265186,9297955,11329563,11395101]) (ec 634980 [0,13,4])) (N (ef 152943 1 [427152,492690,558228,623766,820376,885914,4686950]) E)) (N (N (el 41017 [0,1,2,3,13,4,5,6] [566174,598944,828322,860870,2531961,4760382,5022562,7119780,7152550]) (e0 2576696)) (N (e1 335957 10) E))) (N (N (N (el 12871 [0,2,8,4,9] [590456]) (e0 1028212)) (N (e1 221264 3) E)) (N (N (el 69685 [0,1,2,3,13,8,4,6,9] [434832,697422,959568,2531997]) E) (N (e1 479357 13) E)))) (N (N (N (N (el 4951 [0,2,3,4,6] [393654,491960,4587962,4686228]) (ef 770152 0 [3048692])) (N (e1 180337 13) E)) (N (N (el 53369 [0,1,2,3,13,4,5,6] [566284,3064823,9388610]) E) (N (e1 410224 1) E))) (N (N (N (e1 24669 8) (e1 1692784 1)) (N (ec 286840 [0,4]) E)) (N (N (e1 135224 21) E) (N (e1 557344 8) E))))) (N (N (N (N (N (el 1127 [0,1,2,3,13,8,4] [434290,450918,467304,483690,565460,581996,598382,614768,696533,713069,729455,745841,819570,835956,958838,975224,991610,1007996,2531460,2547846,2564264,2679008,2793745,2810131,2826537,2933040,3072322,4628613,4644999,4661417,4759824,4776210,4792616,4907233,5030193,5169475,6873158,7004231,7159902,7266490,9101516,9363708,11460861]) (ec 692327 [0,15])) (N (e1 163965 13) E)) (N (N (el 45157 [0,1,2,3,13,4,5,10,6] [565960,820178,2663118,9257522]) E) (N (e1 376892 17) E))) (N (N (N (ec 16453 [0,1,2,3,8,4,5,10,6]) (e1 1073776 1)) (N (e1 253984 13) E)) (N (N (ec 106597 [0,4]) E) (N (e1 524361 10) E)))) (N (N (N (N (el 9323 [0,1,2,3,13,8,4] [303718,426600,696938,828012,959086,2458224,2523628,2925101,4637167]) (e0 966744)) (N (ef 192601 4 [558248]) E)) (N (N (el 61556 [0,1,2,3,13,8,4,5] [7160408]) E) (N (e1 446496 13) E))) (N (N (N (el 29303 [0,3,13,11,6] [951144]) (e0 2035832)) (N (e1 311356 9) E)) (N (N (ef 151663 9 [164962,427112]) E) (N (el 614697 [0,3,13,8,4,22] [2925788]) E)))))) (N (N (N (N (N (N (el 335 [0,1,2,3,8,4,5] [434410,565484,688366,958704,1024242,2662598,6873157,7028816,7266457,7332015,9363687,9429236,11444470]) (e1 660320 3)) (N (e1 159857 13) E)) (N (N (el 41573 [0,1,3,13,8,5,6] [836542,2360256,2663090,2794434,4793252,9257514]) E) (N (e1 356436 4) E))) (N (N (N (el 13175 [0,3,4,6] [393924,459462,4883122]) (e0 1048628)) (N (ec 241685 [0,4]) E)) (N (N (e1 86129 13) E) (N (e1 499828 4) E)))) (N (N (N (N (el 8783 [0,1,2,3,8,4,5] [426522,696860,959006,1024544,2793994,7250429]) (e1 786549 5)) (N (ec 188484 [13,8,4,23]) E)) (N (N (e1 57469 13) E) (N (e0 422517) E))) (N (N (N (el 28745 [0,1,2,3,8,4,5,11,10] [566098,4759982,9126414]) (e0 1945892)) (N (e1 299100 8) E)) (N (N (e1 147516 7) E) (N (e0 583013) E))))) (N (N (N (N (N (e1 4209 13) (e1 749653 10)) (N (e0 176213) E)) (N (N (el 49511 [0,1,2,3,13,8,4,6] [828249,861164,959470,992240,2925497,4686812,4703198]) E) (N (el 402517 [0,4] [861366]) E))) (N (N (N (el 18039 [0,1,8,4,5] [459538,918292,983830]) (e1 1396756 4)) (N (ec 270394 [8,4]) E)) (N (N (e0 123001) E) (N (el 545077 [0,6] [820428]) E)))) (N (N (N (N (e1 12401 13) (e0 999753)) (N (ec 196908 [0,13,8]) E)) (N (N (el 65611 [0,3,8,6] [951348,3048502]) E) (N (e1 467000 21) E))) (N (N (N (el 32885 [0,1,2,3,13,8,4,5] [565983,598916,697203,729990,820104,836490,2663141,2695953,2933644,4891446,9257502]) (e0 2212201)) (N (e1 315952 13) E)) (N (N (ez 152391 [787572,853110]) E) (N (e1 622713 5) E))))))) (N (N (N (N (N (N (N (el 79 [0,1,2,3,8,4,6] [434334,565408,827554,958628,1024166,5152936,9232554,9363628,9429166,13557936,13623474]) (ef 647527 0 [951526])) (N (el 155752 [0,4] [6988918,7119991]) E)) (N (N (e1 41057 8) E) (N (e1 344661 10) E))) (N (N (N (el 12921 [0,13,8,4,15,6,9] [172730,2540203,4891324]) (e0 1040452)) (N (e1 233545 6) E)) (N (N (e1 69749 5) E) (N (e1 491620 4) E)))) (N (N (N (N (el 5503 [0,3,13,4,6] [491984,2490834,2589078]) (el 782438 [0,23] [525558])) (N (e1 184428 2) E)) (N (N (el 57428 [0,1,2,3,8,4,5,10] [7029318,7135997,11314177]) E) (N (e1 418688 1) E))) (N (N (N (el 24949 [0,1,2,3,13,5,10,6] [598846,5112640,9126412]) (e0 1855568)) (N (ec 299060 [0,4]) E)) (N (N (e1 139324 7) E) (N (ef 569392 10 [4752600]) E))))) (N (N (N (N (N (e1 4177 8) (e1 737397 5)) (N (e1 172141 8) E)) (N (N (el 45669 [0,3,13,8,5,11,10,6] [836566,2663092,4760526,9257530]) E) (N (e1 380988 17) E))) (N (N (N (el 17013 [0,13,8,4,15,6] [4891400]) (e0 1245252)) (N (ec 254261 [0,8,4]) E)) (N (N (ec 115061 [4,6]) E) (N (ec 532549 [0,4]) E)))) (N (N (N (N (el 12361 [0,1,2,3,8,4,5,10] [565886]) (e0 983092)) (N (el 196660 [0,8,4] [304226]) E)) (N (N (el 65593 [0,1,2,3,13,8,4] [180868,566308,599078,697381,730151,959528,992298,2400910,2531983]) E) (N (e1 458868 4) E))) (N (N (N (el 30069 [0,1,2,3,13,8,4,5] [598906,2409304,2474846,2540388,5022588,5055358]) (e1 2117748 4)) (N (e1 315440 10) E)) (N (N (el 151909 [8,4,9] [2663534,2696304]) E) (N (el 618584 [0,8,4] [7152866]) E)))))) (N (N (N (N (N (N (el 837 [0,1,2,3,8,4] [860460,2547934,2679055,2810158,2941232,3006770,6873290,7004408,7135512,7201066,9101563,9232617,9298167,11329844,11395382]) (ec 684105 [0,4])) (N (ez 160117 [263330]) E)) (N (N (el 42341 [0,1,2,3,13,8,4,5,6] [598986,2360268,2458546,5055404]) E) (N (ec 364596 [0,4]) E))) (N (N (N (el 13439 [0,2,13,4] [426718,492256,557794,688868,754406]) (e0 1048676)) (N (ef 242037 1 [787626]) E)) (N (N (e1 102473 10) E) (N (e0 512121) E)))) (N (N (N (N (el 9303 [0,1,2,3,8,4,5] [655932,721470,926272,991810,2540006,7250431]) (e1 877168 1)) (N (ec 188532 [0,13,8]) E)) (N (N (el 61508 [0,1,2,3,13,8,4,11,10,6] [7029330,7136036]) E) (N (e0 434534) E))) (N (N (N (e1 28797 13) (e1 1970224 10)) (N (e1 307256 21) E)) (N (N (el 151639 [1,17] [656478,722016]) E) (N (ec 610344 [0,3,13,4,22]) E))))) (N (N (N (N (N (el 4437 [0,1,3,8,4,5,6] [3056040,5185954]) (el 761920 [0,1,2,3,13,8,4] [2663658,2696428,2794731,2827501,2925806,2958576,4891861,4924635,6857940,6890714])) (N (e1 176252 1) E)) (N (N (el 53305 [0,1,2,3,8,4,5,6] [959492,1025030]) E) (N (e1 406112 1) E))) (N (N (N (el 22131 [0,1,13,4,5] [492320,557858,820004,951077]) (e1 1675380 4)) (N (e1 270937 10) E)) (N (N (e1 131132 10) E) (N (ef 553317 3 [2458832,2491602]) E)))) (N (N (N (N (e1 12413 13) (e0 1028148)) (N (ec 208952 [0,4,9]) E)) (N (N (el 65655 [0,1,5,10,6] [787518,853056,918591,984129,3179578]) E) (N (e1 471156 4) E))) (N (N (N (el 38245 [0,1,2,3,8,4,12,5] [992150]) (e1 2302048 2)) (N (ec 319572 [13,4]) E)) (N (N (e0 152663) E) (N (e1 630896 2) E)))))))) (N (N (N (N (N (N (N (N (el 58 [0,1,2,3,4] [565322,827467,4644940,4776014,4841552,4907090,5038164,5103702,6873173,6938711,7004243,7135311,7200849,9101400,9134170,9199708,9232478,9265248,9298017,11329625,11395163]) (ec 639093 [0,4])) (N (e1 155741 8) E)) (N (N (el 41033 [0,1,2,3,4,5,10,6] [566184,828330,4759986,9126434,11314092]) (e0 2584664)) (N (e1 335989 5) E))) (N (N (N (el 12917 [0,13,8,4,9] [475824,2523814,2540201,2663090,2695860,4891318,4924088,6857128]) (e0 1040436)) (N (ec 233514 [0,15,9]) E)) (N (N (el 69717 [0,1,2,3,13,8,4,5,10,6] [599122,9257580]) E) (N (ec 491593 [0,4]) E)))) (N (N (N (N (el 4991 [0,2,3,13,4] [426438,491976,688586,2785708]) (ec 782393 [0,4])) (N (el 184372 [0,1,8,9] [828561]) E)) (N (N (el 53631 [0,1,13,8,5,6] [1082386,3179498,7078932,7144458]) E) (N (e1 414304 1) E))) (N (N (N (el 24680 [0,1,2,3,4,5,10,6] [6898184,7004864,7135937,9085744,9216817,11330354]) (e1 1700720 1)) (N (e1 294960 9) E)) (N (N (e1 135252 6) E) (N (e1 561268 4) E))))) (N (N (N (N (N (ec 4149 [0,1,2,3,4,5,14,10,6]) (e1 737349 6)) (N (e1 172129 8) E)) (N (N (el 45172 [0,1,2,3,13,4,5,6] [7029302,7135954,11314132]) E) (N (ec 376932 [0,4]) E))) (N (N (N (el 16501 [0,1,2,3,13,8,4,6] [697088,729858,959236,992006]) (e1 1134880 8)) (N (e1 254025 6) E)) (N (N (ef 107333 2 [918612]) E) (N (e1 525157 6) E)))) (N (N (N (N (el 12345 [0,1,2,3,8,4,5,6] [565874,959092,1024630]) (ez 979301 [787704])) (N (e1 192633 5) E)) (N (N (e1 61564 1) E) (N (e1 446822 13) E))) (N (N (N (ez 29815 [394092,426862,459632,492401]) (e1 2052704 3)) (N (ec 311380 [13,4]) E)) (N (N (e0 151879) E) (N (el 615015 [0,1,20] [853218,2720988]) E)))))) (N (N (N (N (N (N (el 359 [0,1,2,3,13,4,5,6] [434226,467200,483586,565439,598276,614662,794888,827604,860426,893196,2531390,2662600,2924762,4644993,4776157,4899086,5021968,5038354,5054740,6873153,7028820,7135376,9232662,11313432]) (e1 664416 3)) (N (e0 159865) E)) (N (N (el 41577 [0,1,3,13,8,5,11,10,6] [4793254,9257516]) E) (N (e1 360560 2) E))) (N (N (N (ec 13415 [0,4,18,5]) (e0 1048644)) (N (e1 241749 10) E)) (N (N (e1 90437 2) E) (N (e1 504421 10) E)))) (N (N (N (N (el 8807 [0,1,2,3,13,4,5] [696835,729634,795172,827922,860710,893480,2793996,2925080,4637157,5022250,5055020,7119348]) (e1 860272 1)) (N (e0 188501) E)) (N (N (el 61493 [0,1,2,3,13,8,4,10,15,6] [959522,2949712,3056418]) E) (N (ec 434249 [0,4]) E))) (N (N (N (el 28789 [0,1,2,3,4,5,11,6] [598868,729942,2933592,9257490]) (ef 1962064 3 [4588798])) (N (e1 299148 1) E)) (N (N (ec 151607 [3,7]) E) (N (ec 599397 [0,13,4]) E))))) (N (N (N (N (N (el 4217 [0,1,2,3,13,4,5,6,7] [565662,827808,5022114,6857124,7119270]) (e1 753780 4)) (N (e1 176237 8) E)) (N (N (el 50535 [0,1,2,3,13,8,4,5] [599030,918520,984058,4703202]) E) (N (ez 405573 [7079098]) E))) (N (N (N (e1 20577 8) (e0 1417284)) (N (ez 270665 [558260]) E)) (N (N (e1 127561 10) E) (N (e1 545638 4) E)))) (N (N (N (N (el 12407 [0,13,4,15,9] [459406]) (e1 1015904 1)) (N (e0 204917) E)) (N (N (el 65638 [0,1,2,3,13,8,4] [328669,336863,459740,467934,525368,2794540,2827318,2925613,2958391,3056698,3089468,5022655,5055447,6988734,7021526]) E) (N (e1 471100 11) E))) (N (N (N (el 33919 [0,2,3,13,8] [426894,951184,2655034,7242641]) (ez 2216040 [4850948])) (N (e1 319548 9) E)) (N (N (ez 152423 [4752494]) E) (N (e1 626805 5) E))))))) (N (N (N (N (N (N (N (el 295 [0,1,2,3,4,5,10,6] [434212,696510,762048,786626,852164,958655,1024193,2531386,2859206,3055816,4628539,4890825,5218503,6897740,7004300,7266445,9085130,9347275,11460812]) (ec 655429 [0,4])) (N (ef 156021 2 [5112992]) E)) (N (N (e1 41069 8) E) (N (e1 352564 10) E))) (N (N (N (el 13127 [0,2,3,4,5,6] [918206,983744,4620994]) (e1 1044592 2)) (N (e1 233593 5) E)) (N (N (e1 77909 2) E) (N (e1 491878 0) E)))) (N (N (N (N (el 8759 [0,1,2,3,4,5] [696834,762372,786950,852488,958979,1024517,2859530,3056140,4891149,5218827,6988272,7250417]) (e1 782457 5)) (N (e1 184445 13) E)) (N (N (e1 57444 4) E) (N (ec 422005 [0,4]) E))) (N (N (N (el 25975 [0,2,3,5,10,6] [951110,7340872,7406386]) (e1 1933412 4)) (N (el 299076 [13,4] [4752564]) E)) (N (N (e1 143408 7) E) (N (e1 573728 8) E))))) (N (N (N (N (N (el 4185 [0,1,2,3,8,4,5,6,7] [2662804,3121558]) (ez 745844 [656618,2557132])) (N (e0 172649) E)) (N (N (el 49257 [0,1,2,3,13,8,4,22,15,20] [2401244,2417630,2434016,2679754,2810747,2941922,4907959,5039076,9102146,9233302,11330457]) E) (N (ec 385324 [0,4]) E))) (N (N (N (el 17527 [0,2,8,4] [426752,459530,2523916]) (e1 1388853 6)) (N (e1 266320 3) E)) (N (N (el 119165 [3,5] [492630,5112920]) E) (N (e0 533861) E)))) (N (N (N (N (el 12391 [0,1,4,5,6,17] [656000,721538]) (e0 995416)) (N (e0 196709) E)) (N (N (el 65607 [0,3,11,6] [459696,3048492]) E) (N (e1 466992 21) E))) (N (N (N (el 32837 [0,1,2,3,8,4,5,10] [598914,9126428]) (e0 2207824)) (N (e1 315504 2) E)) (N (N (el 151913 [8,4,15] [173170]) E) (N (e1 622697 24) E)))))) (N (N (N (N (N (N (el 1115 [0,1,2,3,8,4,5] [434502,688456,753994,819532,958798,1024336,7159898,7266461,7332019,13541687]) (ec 684150 [0,22])) (N (e0 163925) E)) (N (N (el 45125 [0,1,2,3,13,4,21,5,10] [9126448,11314128]) E) (N (ec 372853 [0,4]) E))) (N (N (N (el 13951 [0,1,13,4] [426738,492276,557814,688888,754426,819964,885502,4686490]) (ez 1069124 [4850938])) (N (ec 249908 [0,4]) E)) (N (N (ec 102504 [0,4]) E) (N (e1 520324 4) E)))) (N (N (N (N (el 9315 [0,1,2,3,13,8,4] [426574,557648,688722,696916,754262,819795,827989,885335,950872,959066,1016412]) (e0 962680)) (N (e1 188540 1) E)) (N (N (e1 61516 3) E) (N (e1 438357 10) E))) (N (N (N (ec 29255 [2,3,11,6]) (e1 2031973 20)) (N (e1 307508 10) E)) (N (N (ec 151655 [15,9]) E) (N (el 614693 [0,13,8,4] [2794705]) E))))) (N (N (N (N (N (el 4693 [0,1,3,8,4,5,11,6] [598446,991664,5185958]) (ef 762233 26 [4850928])) (N (e1 180304 3) E)) (N (N (el 53320 [0,1,2,3,8,4,5] [2548398,2802664,2941960,3007498,7029310,7135983,7201559,11314171]) E) (N (el 406901 [2,5] [9307330]) E))) (N (N (N (el 22139 [0,1,8,4,5] [492330,2458412]) (e1 1684336 1)) (N (e1 279125 10) E)) (N (N (e1 135216 21) E) (N (e1 553581 8) E)))) (N (N (N (N (el 12661 [0,13,8,4,15,9] [262816,565922,598692,2523814,2532008,2540201,2564778,2605739,4891299,4924069]) (e0 1028164)) (N (ec 209032 [0,4]) E)) (N (N (el 65659 [0,1,5] [1082434,3179580]) E) (N (e1 475749 10) E))) (N (N (N (el 38519 [0,12,5] [1082266]) (e1 2487136 1)) (N (ec 319588 [0,4]) E)) (N (N (ef 152687 2 [427140,492678,558216,623754]) E) (N (ec 634940 [0,1,13,4]) E))))))))) (N (N (N (N (N (N (N (N (N (el 23 [0,1,2,3,4,5,6,7] [434212,466982,663592,696362,729132,761902,925744,958514,991284,1024054,2793528,4628538,4890684,5152830,7004224,7266370,7331908,11460678,11526216]) (e1 634988 3)) (N (ec 155733 [5,14]) E)) (N (N (ec 41019 [0,3,13,4,6]) (e1 2584656 3)) (N (e1 335961 10) E))) (N (N (N (el 12903 [0,1,8,4,5,6] [656044,721582]) (e1 1028220 1)) (N (ec 221272 [0,4]) E)) (N (N (el 69701 [0,1,2,3,13,8,4,5,11,6] [7128051,9257578]) E) (N (ec 483401 [0,4]) E)))) (N (N (N (N (el 4983 [0,3,4] [393660,426430,459200,491970,688580]) (e1 778372 4)) (N (e0 180345) E)) (N (N (el 53623 [0,1,13,8,5,6] [1082382,7078928,7144456]) E) (N (ez 413817 [7210182,7275702]) E))) (N (N (N (e1 24672 1) (e1 1696880 1)) (N (e1 287284 10) E)) (N (N (e1 135228 10) E) (N (ef 557397 10 [394456]) E))))) (N (N (N (N (N (el 1131 [0,1,2,3,13,8,4,6] [303486,434560,565634,696708,819590,958856,2457994,2531464,2793749,4645003,4907235,5030195,5169477,7004233,7159904,7266492,11460863]) (e1 696437 5)) (N (e0 172121) E)) (N (N (e1 45165 8) E) (N (ec 376900 [0,1,4]) E))) (N (N (N (e1 16485 5) (e1 1097760 13)) (N (e1 254021 6) E)) (N (N (e1 107109 4) E) (N (ec 524389 [0,4]) E)))) (N (N (N (N (ec 12343 [0,3,4,11,6,7]) (e0 978965)) (N (e1 192629 5) E)) (N (N (e1 61557 5) E) (N (e0 446537) E))) (N (N (N (el 29311 [0,3,13,8,11,6] [951146]) (e0 2039912)) (N (ec 311364 [13,4]) E)) (N (N (e0 151863) E) (N (ez 614759 [918750,984288]) E)))))) (N (N (N (N (N (N (el 343 [0,1,2,3,4,12,5,6] [7028818,7135374,7266453,7332011,11313400,11444474,13558012,13623550]) (e1 663684 4)) (N (e0 159861) E)) (N (N (el 41575 [0,3,13,8,6] [951236,3048376,4588486,4686768]) E) (N (e1 360504 10) E))) (N (N (N (el 13183 [0,3,13,4] [426696,492234,557772,688846,754384,1082066,1147604,4883124]) (e1 1048636 9)) (N (e1 241733 6) E)) (N (N (ec 86137 [0,4]) E) (N (ec 503848 [0,3,8,4]) E)))) (N (N (N (N (el 8791 [0,1,2,3,4,12,5] [7119346,7250425]) (ec 794697 [0,4])) (N (ec 188500 [0,13,8]) E)) (N (N (el 61492 [0,1,2,3,13,8,10,15,6] [738334,844832]) E) (N (ec 426053 [0,4]) E))) (N (N (N (e1 28785 13) (e1 1950000 8)) (N (ec 299140 [0,4]) E)) (N (N (e1 147760 8) E) (N (e1 589924 4) E))))) (N (N (N (N (N (el 4213 [0,1,2,3,4,5,15,6,7] [598424,786842,852380]) (e1 749668 4)) (N (ef 176229 4 [558200,2655356]) E)) (N (N (el 49519 [0,1,2,3,13,8,4,6] [828402,959476,3056618,4686816]) E) (N (ef 402791 0 [951480]) E))) (N (N (N (el 18047 [0,1,13,8,4,6,19] [426776,688922]) (e1 1413168 9)) (N (ef 270661 6 [394418]) E)) (N (N (e0 127049) E) (N (el 545124 [0,3,4] [468174]) E)))) (N (N (N (N (el 12405 [0,1,2,3,4,15,9] [344708,565894,598664,696967,729737,959114,991884]) (e0 1007637)) (N (e1 204869 10) E)) (N (N (e1 65636 4) E) (N (e1 471092 6) E))) (N (N (N (e1 32893 13) (e1 2216032 3)) (N (ec 319540 [0,1,4]) E)) (N (N (e0 152407) E) (N (e0 626789) E))))))) (N (N (N (N (N (N (N (el 87 [0,1,2,3,4,5] [794804,860342,925877,991415,13525176,13557946,13590716,13623485]) (el 647535 [0,8] [951528])) (N (el 155997 [2,5] [558236,4981918]) E)) (N (N (el 41065 [0,1,2,3,13,4,5,6] [598726,730030,2532272,2917298,7127988,9257510]) E) (N (e1 352312 21) E))) (N (N (N (el 12927 [0,13,8,4,9] [164538,426640,557724,4752042]) (e1 1040460 8)) (N (e1 233589 5) E)) (N (N (el 69932 [0,1,2,3,13,8,4,10,6] [4932208,5038892]) E) (N (el 491622 [0,22] [656584]) E)))) (N (N (N (N (el 8261 [0,1,2,3,8,4,9] [451028,582102,713176,827866,844252,860638,909792,2548194,2679268,2810342,2925032,2941418,2957804,3006958,6873584,7004658,7135732,7201270,9101816,9232890,9298428,11330046,11395584]) (e1 782453 5)) (N (ef 184437 4 [558225,2655381]) E)) (N (N (e1 57436 2) E) (N (e1 421957 10) E))) (N (N (N (el 25685 [0,1,2,3,8,4,5,6] [992066,4981572,5047088,9413437]) (e1 1863780 4)) (N (e1 299068 9) E)) (N (N (e1 139348 6) E) (N (ef 573513 20 [4687054]) E))))) (N (N (N (N (N (el 4181 [0,1,2,3,4,5,11,6] [598414,926096,991634]) (e1 737401 5)) (N (ef 172645 3 [2360484,2655342]) E)) (N (N (el 46437 [0,1,2,3,13,8,4,5,6] [328664,5022672,5145556,5211098]) E) (N (e1 385084 17) E))) (N (N (N (ec 17511 [0,8,4,18,5]) (e1 1359968 2)) (N (el 254265 [13,4] [165040]) E)) (N (N (e1 118880 1) E) (N (e1 532581 2) E)))) (N (N (N (N (e1 12389 5) (e1 995408 3)) (N (e0 196693) E)) (N (N (el 65595 [0,13,8,4] [2392708,4620976,4752049]) E) (N (e1 462964 4) E))) (N (N (N (el 32821 [0,1,2,3,8,4,5,9] [565703,959199,1024896,3056355,4760372]) (ez 2187344 [2557184])) (N (e1 315448 10) E)) (N (N (ec 151911 [8,4,9]) E) (N (el 618877 [0,1,6] [2720988,4981988]) E)))))) (N (N (N (N (N (N (el 1111 [0,1,2,3,8,4,5] [467256,524602,590140,926014,991552,2547842,2933038,3072322,3137860,7159896,7266459,7332017,13541685]) (e1 684148 4)) (N (el 163892 [0,1,3,8,9] [828549,2663580]) E)) (N (N (el 45109 [0,1,2,3,13,4,5,10,15,6] [828104,2925260,7119822]) E) (N (e1 364628 4) E))) (N (N (N (el 13943 [0,1,4,5] [393960,459498,918252,983790,4588272,4686488]) (e1 1048684 3)) (N (e0 242041) E)) (N (N (e1 102496 8) E) (N (e1 516228 4) E)))) (N (N (N (N (el 9307 [0,1,2,3,8,4,5] [426564,819782,885320,959050,1024588,7250433]) (e0 962672)) (N (e1 188533 5) E)) (N (N (el 61509 [0,1,2,3,13,8,4,5,11,10,6] [9257556]) E) (N (ec 438341 [0,4]) E))) (N (N (N (el 29045 [0,1,3,13,8,5,11,6] [263008,598882,2933604,4793168,4924262,9257496]) (e0 2011216)) (N (e1 307260 10) E)) (N (N (ec 151653 [0,15,9]) E) (N (e1 610940 1) E))))) (N (N (N (N (N (el 4661 [0,1,2,3,4,5,6] [786858,3121580,5185956]) (ez 762229 [787698,853236,918771,984309,4850926])) (N (ez 176741 [2655344,4752550]) E)) (N (N (e1 53312 3) E) (N (ez 406397 [296126,9307328]) E))) (N (N (N (el 22135 [0,1,4,5] [394022,492328]) (e1 1680224 1)) (N (el 278549 [13,4] [2524336]) E)) (N (N (e1 131632 8) E) (N (e1 553569 8) E)))) (N (N (N (N (el 12415 [0,13,4,9] [164496,426652,557726]) (e1 1028156 9)) (N (ec 209024 [0,4]) E)) (N (N (e1 65657 5) E) (N (e0 475209) E))) (N (N (N (el 38261 [0,1,2,3,13,4,12,5] [992152]) (e1 2417232 1)) (N (e1 319580 8) E)) (N (N (e0 152679) E) (N (el 630904 [0,4] [4703456]) E)))))))) (N (N (N (N (N (N (N (N (el 71 [0,1,2,3,8,4,9] [434218,450658,467044,565299,581734,598120,827498,843884,860270,925808,958578,974964,991350,1024120,1040506,2531384,3055740,4644990,4776064,5038210,5152900,5169286,5185672,5234826,6873228,7135374,7266448,7331986,9232532,9363606,9429144,13557914,13623452]) (e1 639101 13)) (N (e1 155744 1) E)) (N (N (ec 41035 [2,13,10]) E) (N (e1 335993 5) E))) (N (N (N (el 12919 [0,13,8,4,9] [590478,4752040]) (e1 1040444 9)) (N (e1 233541 6) E)) (N (N (e1 69732 4) E) (N (e1 491609 10) E)))) (N (N (N (N (el 5495 [0,3,4,6] [393676,491982,2654632]) (e1 782436 4)) (N (el 184420 [0,8,4] [7120025]) E)) (N (N (el 57397 [0,1,2,3,8,4,5,9] [959219,1025046,3056375]) E) (N (e1 417908 4) E))) (N (N (N (el 24925 [0,1,2,3,8,5] [566068,959286,4981560,6857133,7316282,9126410,11445052]) (e1 1708912 1)) (N (ec 294968 [0,4]) E)) (N (N (e1 139316 6) E) (N (e1 561712 8) E))))) (N (N (N (N (N (el 4153 [0,1,2,3,4,5,10,6] [696716]) (e1 737353 6)) (N (e1 172137 4) E)) (N (N (e1 45180 1) E) (N (e1 380976 17) E))) (N (N (N (e1 16509 13) (e0 1143381)) (N (el 254260 [0,13,8,4,15,9] [2532524,2565294,4760749,4793519]) E)) (N (N (e0 107365) E) (N (e0 525161) E)))) (N (N (N (N (el 12359 [0,2,4,9,16] [459384,1049210,1114748]) (e0 979305)) (N (ef 196645 4 [427106,2524275,4621426]) E)) (N (N (el 65591 [0,4,15,9] [2425476]) E) (N (e1 447065 10) E))) (N (N (N (el 29823 [0,2,3,13] [426866,492404,557942,951160]) (e1 2113652 4)) (N (e1 311388 8) E)) (N (N (ez 151895 [656490,722028]) E) (N (e1 618576 3) E)))))) (N (N (N (N (N (N (el 367 [0,1,2,3,13,4,5,10,6] [434458,565532,688414,827680,893218,950564,1016102,5021992,7028822,7135378,11313450]) (e1 667773 13)) (N (e1 159869 13) E)) (N (N (el 42087 [2,3,10,6] [394184,4883394]) E) (N (ec 360568 [0,4]) E))) (N (N (N (el 13431 [0,2,4] [393942,426631,459480,492250,2523868]) (e1 1048652 8)) (N (e1 241781 5) E)) (N (N (e1 90493 6) E) (N (e0 508025) E)))) (N (N (N (N (el 8815 [0,1,2,3,13,4,5] [426542,696880,827954,893492,950838,1016376,5022266,7119350]) (e1 876604 7)) (N (e1 188508 3) E)) (N (N (e1 61500 4) E) (N (e1 434265 10) E))) (N (N (N (el 28793 [0,1,2,3,13,4,5,11,6] [566106,697180,2933598,4759984,9257492]) (e1 1962544 8)) (N (e1 307248 21) E)) (N (N (el 151623 [2,16] [918618,984156]) E) (N (el 606310 [23,20] [656602]) E))))) (N (N (N (N (N (e1 4221 13) (ef 754036 25 [656620])) (N (el 176244 [0,13,4] [7120000]) E)) (N (N (el 50543 [0,1,2,3,13,8,4,5] [492540,566270,820224,885762]) E) (N (ef 405621 2 [7210172]) E))) (N (N (N (el 20585 [0,1,2,3,8,4,5,17] [959260,1024798]) (e0 1671273)) (N (e1 270933 10) E)) (N (N (e1 131120 7) E) (N (ef 553065 3 [2393296]) E)))) (N (N (N (N (el 12409 [0,1,2,3,13,8,4,9] [172688,565906,696980,959126,3056280,3089050]) (e0 1015912)) (N (e1 204925 13) E)) (N (N (e1 65653 5) E) (N (e1 471108 6) E))) (N (N (N (el 34165 [0,1,2,3,13,8,4,5] [328594,2409356,5022612,7119676]) (e0 2244672)) (N (ec 319556 [13,4]) E)) (N (N (ef 152431 3 [427128,492666,558204,623742,951424,1016962,4752496]) E) (N (e0 630857) E))))))) (N (N (N (N (N (N (N (el 327 [0,1,2,3,8,4,5,11,6] [434218,467150,565438,598224,925906,958676,991446,1024216,2531388,3055834,4644990,4776156,4899038,5169376,5234914,6873155,7028814,7266455,7332013,9363684,9429222,11444456]) (e1 659588 4)) (N (e0 159833) E)) (N (N (el 41558 [0,1,2,3,13,4,5,10] [861110,2925496,4989882,5022552,5055412,5088188,7119716]) E) (N (ec 356404 [0,4]) E))) (N (N (N (ec 13159 [0,4,12,5]) (e0 1044600)) (N (ec 237624 [0,4,9]) E)) (N (N (e1 86089 10) E) (N (ef 499764 0 [820426,2524350]) E)))) (N (N (N (N (el 8775 [0,1,2,3,8,4,5] [696834,729614,926224,958994,991764,1024534,3056152,4637154,7250427]) (e1 786517 10)) (N (ec 188468 [0,13,8]) E)) (N (N (el 57461 [0,1,2,3,13,8,4,5] [566003,599064,951322,967708,2663161,2695963,3064831,9388618]) E) (N (e1 422013 13) E))) (N (N (N (el 28729 [0,1,2,3,8,4,5,11] [566090,959308,1024846,5153616]) (e0 1937465)) (N (ec 299092 [13,4]) E)) (N (N (e1 143420 7) E) (N (ez 578405 [2524340]) E))))) (N (N (N (N (N (e1 4189 8) (ec 749637 [0,4])) (N (el 176180 [0,3,13,15] [697464,4891814]) E)) (N (N (el 49495 [0,1,2,3,8,4,5,6] [656358,721896,3122154,7283684]) E) (N (ec 389193 [0,4]) E))) (N (N (N (el 17535 [0,2,13,8,4] [426766,688912]) (e1 1388857 6)) (N (ec 266328 [0,4]) E)) (N (N (e0 122953) E) (N (e1 544857 10) E)))) (N (N (N (N (e1 12393 5) (e0 999749)) (N (e1 196725 5) E)) (N (N (el 65609 [0,1,2,3,13,8,4,5,6] [566318,697392,820274,7128045,9257568]) E) (N (e1 466996 10) E))) (N (N (N (e1 32852 4) (ez 2212197 [656642,722180,787715,853253])) (N (ec 315512 [0,4]) E)) (N (N (el 151919 [8,4,9] [164978,427106]) E) (N (e1 622709 5) E)))))) (N (N (N (N (N (N (el 1123 [0,1,2,3,13,8,4,10,6] [426322,434516,491862,557400,565594,622940,688473,696667,754013,819550,950624,958818,1016164,7159900,7266488]) (ec 692314 [0,13,8])) (N (ef 163957 4 [558213,2655369]) E)) (N (N (e1 45140 4) E) (N (e1 372861 13) E))) (N (N (N (ec 16437 [0,1,2,3,8,4,5,11,6]) (e1 1069664 1)) (N (ec 249924 [0,4]) E)) (N (N (e1 106565 10) E) (N (e1 524357 10) E)))) (N (N (N (N (el 9319 [0,1,2,3,13,8,4] [426458,442974,696850,729696,827923,860769,959074,991844,2523624,2540010,2925099,2957883,4620777,4637163,4891178,4923962]) (e1 966736 3)) (N (ec 192566 [4,15,9]) E)) (N (N (e1 61540 4) E) (N (e0 438630) E))) (N (N (N (ec 29270 [0,1,2,3,8,4,5,11,6,20]) (e1 2035824 2)) (N (ec 311348 [0,4]) E)) (N (N (el 151657 [2,4,9] [173154,2925668,2958438]) E) (N (ec 614695 [0,13]) E))))) (N (N (N (N (N (el 4725 [0,1,3,13,4,5,6] [598450,4792756]) (e1 770144 3)) (N (el 180312 [0,4] [2540652,7120015]) E)) (N (N (e1 53361 13) E) (N (ez 409673 [7210180]) E))) (N (N (N (el 24661 [0,1,2,3,8,4,5,14,11,10,6] [598830,9126402]) (ez 1691684 [7079164])) (N (e1 286832 1) E)) (N (N (e1 135220 10) E) (N (ef 557158 3 [328912,656596,4588758]) E)))) (N (N (N (N (ec 12855 [0,3,4,11,6]) (e1 1028172 8)) (N (e1 213061 6) E)) (N (N (el 69669 [0,1,2,3,13,8,4,10,6] [434832,468036,820294,836680,959562,992332,2532027,4629178,7160422]) E) (N (e1 475753 10) E))) (N (N (N (el 38527 [0,13,12,5,6] [1082268]) (e1 2531888 8)) (N (e1 319596 3) E)) (N (N (ez 152935 [918668,984206,4686948]) E) (N (e1 634949 0) E))))))))))
noncomputable def m127Ck : Nat → Bool := checkNode m127Mask m127Goal (Nat.sub (Nat.shiftLeft 1 m127Pairs.length) 1) symMain 643 10 m127Ws m127D 10 m127Cuts 5
theorem q26 : tb 0 24 m127Ck = true := by decide +kernel
theorem q27 : tb 24 24 m127Ck = true := by decide +kernel
theorem q28 : tb 48 24 m127Ck = true := by decide +kernel
theorem q29 : tb 72 24 m127Ck = true := by decide +kernel
theorem q30 : tb 96 24 m127Ck = true := by decide +kernel
theorem q31 : tb 120 24 m127Ck = true := by decide +kernel
theorem q32 : tb 144 24 m127Ck = true := by decide +kernel
theorem q33 : tb 168 24 m127Ck = true := by decide +kernel
theorem q34 : tb 192 24 m127Ck = true := by decide +kernel
theorem q35 : tb 216 24 m127Ck = true := by decide +kernel
theorem q36 : tb 240 24 m127Ck = true := by decide +kernel
theorem q37 : tb 264 24 m127Ck = true := by decide +kernel
theorem q38 : tb 288 24 m127Ck = true := by decide +kernel
theorem q39 : tb 312 24 m127Ck = true := by decide +kernel
theorem q40 : tb 336 24 m127Ck = true := by decide +kernel
theorem q41 : tb 360 24 m127Ck = true := by decide +kernel
theorem q42 : tb 384 24 m127Ck = true := by decide +kernel
theorem q43 : tb 408 24 m127Ck = true := by decide +kernel
theorem q44 : tb 432 24 m127Ck = true := by decide +kernel
theorem q45 : tb 456 24 m127Ck = true := by decide +kernel
theorem q46 : tb 480 24 m127Ck = true := by decide +kernel
theorem q47 : tb 504 24 m127Ck = true := by decide +kernel
theorem q48 : tb 528 24 m127Ck = true := by decide +kernel
theorem q49 : tb 552 24 m127Ck = true := by decide +kernel
theorem q50 : tb 576 24 m127Ck = true := by decide +kernel
theorem q51 : tb 600 24 m127Ck = true := by decide +kernel
theorem q52 : tb 624 19 m127Ck = true := by decide +kernel
theorem m127All : treeBlock 0 643 m127Ck = true := (tm 0 312 331 (tm 0 144 168 (tm 0 72 72 (tm 0 24 48 q26 (tm 24 24 24 q27 q28)) (tm 72 24 48 q29 (tm 96 24 24 q30 q31))) (tm 144 72 96 (tm 144 24 48 q32 (tm 168 24 24 q33 q34)) (tm 216 48 48 (tm 216 24 24 q35 q36) (tm 264 24 24 q37 q38)))) (tm 312 168 163 (tm 312 72 96 (tm 312 24 48 q39 (tm 336 24 24 q40 q41)) (tm 384 48 48 (tm 384 24 24 q42 q43) (tm 432 24 24 q44 q45))) (tm 480 72 91 (tm 480 24 48 q46 (tm 504 24 24 q47 q48)) (tm 552 48 43 (tm 552 24 24 q49 q50) (tm 600 24 19 q51 q52)))))
theorem m127Low : LowerM m127Mask m127Raw m127Goal 11 := by
  have hraw : m127Ws.map Wire.val = m127Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 27)) m127D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m127Pairs) (sym := symMain) (count := 643) (rootFuel := 10) (fdepth := 10) (cdepth := 5) (dag := m127D) (cutTree := m127Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m127Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 27)) (defv := (0,[],[])) rfl hnc 10 i
      rw [hraw]; exact m127CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m127All

def m191Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m191Goal : Word := 0xfffffffffffefffe0000000000000000fefefefceeeeaa00
def m191Raw : List Word := [0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 0xcccccccccccccccc0000000000000000cccccccccccccccc, 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 0xffff0000ffff00000000000000000000ffff0000ffff0000, 0xffffffff000000000000000000000000ffffffff00000000, 0xffffffffffffffff00000000000000000000000000000000]
theorem m191Ess : ∀ a ∈ m191Raw, Essential m191Mask m191Goal m191Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,385]) (by decide +kernel)
def m191Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,33025,33152,33282,33408,33796,33920,34824,34944,40992,41088,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,41249,43048,45104,45200,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,34567,36366,39964,47160,2307,2309,2314,2316,2328,2337,2344,4355,4357,4372,4376,4385,4400,4496,4611,4614,4618,4628,4632,4656,4752,8707,8710,8714,8737,8744,8752,9221,9222,9228,9236,9249,9256,9264,33027,33029,33057,33168,33283,33286,33290,33424,33797,33798,33804,33812,33936,34826,34828]
def m191Ws : List Wire := [mw 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa 0x1e00001fff88a78823186f27f00c0f 0x22e449024d188228803082f03500405,mw 0xcccccccccccccccc0000000000000000cccccccccccccccc 0x1e003ffe000197b804d2193d93030f0 0x44e20870e042986b800d009149301050,mw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 0x3e01fc0000003e7f8196c61c1ec0c300 0x9e443c2141853a7f809642141ec04100,mw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00 0xc0000000003ff7dd961807e0e0f30003 0xc8809142822e77dd121807c0e0a10002,mw 0xffff0000ffff00000000000000000000ffff0000ffff0000 0xfffc0679e67e0f800ff00003c 0x3111220f1b08679467e0f000b4000028,mw 0xffffffff000000000000000000000000ffffffff00000000 0x1fff0000047e07800ffff000c03c0 0x9c3840c3045803800bd6a00040280,mw 0xffffffffffffffff00000000000000000000000000000000 0xfffe0000000078007fff0000000ffc00 0x211000081000000045600000000aa800]
def m191Cuts : BTree CutSpec := (N (N (N (N (mc m191Raw 0xffff0000ffff00000000000000000000ffff0000ffff 9) (mc m191Raw 0x5500550055005500 4)) (N (mc m191Raw 0xffffffff000000000000000000000000ffffffff 8) (mc m191Raw 0x55005500000000000000000000000000550055 4))) (N (N (mc m191Raw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f 9) (mc m191Raw 0xf0f0f0f0 4)) (N (mc m191Raw 0x5555555500000000000000000000000055555555 5) E))) (N (N (N (mc m191Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9) (mc m191Raw 0x111100001111000000000000000000001111000011110000 5)) (N (mc m191Raw 0x555555555555555500000000000000005555555555555555 8) (mc m191Raw 0x50505050505050500000000000000000505050505050505 6))) (N (N (mc m191Raw 0x333333333333333300000000000000003333333333333333 9) (mc m191Raw 0x55550000555500000000000000000000555500005555 6)) (N (mc m191Raw 0xffffffffffffffff 7) E))))
theorem m191CutValid : ∀ ci < 14, ValidCut m191Mask m191Raw m191Goal (btreeGet ⟨0,0,[]⟩ 4 m191Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 14845576 m175Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
  · exact cv 14861832 m187Low (by decide +kernel)
  · exact cv 1451527 m249Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 14861960 m190Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 269755911 m89Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 14844043 m167Low (by decide +kernel)
  · exact cv 291088 m86Low (by decide +kernel)
  · exact cv 291101 m87Low (by decide +kernel)
def m191D : BTree NodeRec := (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5] [712706,843780,909318,9216008,11329546,11395084]) (el 110696 [0,3,7] [2662554])) (N (el 24629 [0,1,2,3,4,5,7,8] [852106]) E)) (N (N (el 8280 [0,1,2,3,4,5,7,8] [843882,4898924,5038190]) E) (N (el 53620 [1,2,3,4,5,7,9,8] [2965646]) E))) (N (N (N (el 4213 [0,1,2,3,4,5,6,10,8] [720964,737350,852040,868426,3063884]) (e1 192884 4)) (N (e0 36984) E)) (N (N (el 12405 [0,1,2,3,4,5,7,10] [721020]) E) (N (el 70005 [2,12] [852118]) E)))) (N (N (N (N (el 1125 [0,1,2,3,4,5,7,9] [876596,2400296,2416682,2433074,2940982,5038110]) (el 122935 [1,5] [852126])) (N (ec 32872 [0,2,3,8]) E)) (N (N (el 8804 [0,1,2,3,4,5,7,9,8] [2834546,2941046,5021792]) E) (N (el 57718 [5,7] [2654352]) E))) (N (N (N (el 4223 [0,7,6] [163922,426070,557144,1081434]) (e0 238708)) (N (ec 49220 [0,7]) E)) (N (N (el 20535 [1,2,5,6,10,8] [983170,2949252]) E) (N (el 86389 [2,4,10] [852122,2654352]) E))))) (N (N (N (N (N (el 103 [0,1,2,3,4,5,7,8] [720928,737314,958480,974884,991270,3055642,5013544,5029930,5169196]) (el 115048 [1,13] [2949276])) (N (ec 32856 [0,3,10]) E)) (N (N (el 8311 [1,2,4,6,10,8] [852084,3080304,9470070]) E) (N (ec 57434 [5,10]) E))) (N (N (N (el 4217 [0,1,2,3,4,5,6] [172114,3063892]) (e0 225384)) (N (e0 41334) E)) (N (N (el 16491 [0,1,2,3,4,5,9] [4628606]) E) (N (ef 73832 1 [2949270,9339032]) E)))) (N (N (N (N (el 1391 [0,1,2,3,4,5,7] [434240,950338]) (e0 143720)) (N (ec 33142 [1,2,10,8]) E)) (N (N (el 8823 [1,2,4,5,10,8] [852090,3178616,4751454,7274606]) E) (N (ec 66134 [0,1,2,3,5]) E))) (N (N (N (el 4725 [0,1,2,3,4,5,7,6,10] [737380,2359398,2539614,3063912]) (e0 266600)) (N (ef 53354 4 [5144718]) E)) (N (N (el 20568 [0,1,2,3,4,5,7,10] [450696,4644986,5030016]) E) (N (ec 98392 [0,3,5,7]) E)))))) (N (N (N (N (N (N (el 87 [0,1,2,3,4,5,6] [925710,958480,974866,991252,1024022,1040408,3055642,5152796,13541406]) (ef 114808 2 [2949276])) (N (ec 24692 [0,1,2,3,4,5,7,9]) E)) (N (N (el 8282 [0,1,2,3,4,5,7,8] [3055728,5152860,7110770]) E) (N (el 53622 [4,7] [2654352]) E))) (N (N (N (el 4215 [1,2,7,6,10,8] [852046,983120]) (e0 217192)) (N (ec 40981 [1,2,10,8]) E)) (N (N (ec 12900 [0,1,2,3,4,5,7,11,9]) E) (N (el 70500 [0,1,2,3,5,7,9] [7118990]) E)))) (N (N (N (N (el 1383 [0,1,2,3,4,5,7,10] [434192,450616,467002,720956,737342,2531356,4644908,5161014]) (ec 131176 [0,2,3,4,7])) (N (el 32874 [1,2] [2949260]) E)) (N (N (el 8806 [0,1,2,3,4,5,7,9,8] [3055736,5046380,5152844,7250018]) E) (N (el 65639 [2,4] [852114]) E))) (N (N (N (el 4469 [0,1,2,3,4,5,7,6,8] [868444,2539614,3047520,3063906]) (e0 245864)) (N (e1 49284 9) E)) (N (N (el 20537 [0,1,2,3,4,5,10] [950406]) E) (N (ef 90216 1 [3047578,7143572]) E))))) (N (N (N (N (N (el 111 [0,1,2,3,4,5,7] [819246,958512,5013554]) (e1 118900 9)) (N (el 32858 [1,2] [2949260]) E)) (N (N (ec 8313 [0,1,2,3,4,5,8]) E) (N (e1 57632 7) E))) (N (N (N (e1 4221 7) (e0 229480)) (N (e1 49204 0) E)) (N (N (el 16743 [0,1,2,3,4,5,7,10] [565324,852096,2662520,4694142,4759656]) E) (N (el 74884 [1,2,4,10,8] [2949272]) E)))) (N (N (N (N (e1 4209 7) (e0 189044)) (N (e0 36968) E)) (N (N (ec 12388 [0,1,2,3,4,5,7,9]) E) (N (ef 66151 2 [852116]) E))) (N (N (N (el 5749 [0,1,2,3,4,5,7,9] [2408524,2474068,2523232,2539618,2670696]) (e0 278632)) (N (el 53558 [4,5,7] [3047568]) E)) (N (N (el 20570 [0,1,2,3,4,5,7,10] [2662532,4759652]) E) (N (ec 107061 [0,4]) E)))))))
def m191Ck : Nat → Bool := checkNode m191Mask m191Goal (Nat.sub (Nat.shiftLeft 1 m191Pairs.length) 1) id 80 10 m191Ws m191D 7 m191Cuts 4
theorem q53 : tb 0 24 m191Ck = true := by decide +kernel
theorem q54 : tb 24 24 m191Ck = true := by decide +kernel
theorem q55 : tb 48 24 m191Ck = true := by decide +kernel
theorem q56 : tb 72 8 m191Ck = true := by decide +kernel
theorem m191All : treeBlock 0 80 m191Ck = true := (tm 0 48 32 (tm 0 24 24 q53 q54) (tm 48 24 8 q55 q56))
theorem m191Low : LowerM m191Mask m191Raw m191Goal 11 := by
  have hraw : m191Ws.map Wire.val = m191Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 14)) m191D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m191Pairs) (sym := id) (count := 80) (rootFuel := 10) (fdepth := 7) (cdepth := 4) (dag := m191D) (cutTree := m191Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_id_ok _ _)
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m191Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 14)) (defv := (0,[],[])) rfl hnc 7 i
      rw [hraw]; exact m191CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m191All

def m223Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def m223Goal : Word := 0xfffffffe00000000fffefffe00000000fffffafa00000000eeeeaa00
def m223Raw : List Word := [0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 0xffff000000000000ffff000000000000ffff000000000000ffff0000, 0xffffffff000000000000000000000000ffffffff0000000000000000, 0xffffffff00000000ffffffff00000000000000000000000000000000]
theorem m223Ess : ∀ a ∈ m223Raw, Essential m223Mask m223Goal m223Raw a :=
  checkAllEss_sound (ps := [2057,4114,16452,265,273,321,385]) (by decide +kernel)
def m223Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,34824,34944,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,49600,49730,49856,50368,51272,51392,53392,53440,3847,3854,5895,7452,7694,7708,18183,19274,19982,20042,23114,23580,34567,36366,39964,51786,2307,2309,2314,2316,2328,2376,4355,4357,4372,4376,4496,4611,4614,4618,4628,4632,4674,4752,16643,16645,16706,16712,16832,17413,17414,17420,17428,17474,17480,17600,20500,20504,20546,20552,20624,20672,33027,33029,33168,33216,33283,33286,33290,33346,33424,33472,33797,33798,33804]
def m223Ws : List Wire := [mw 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa 0x78003e03ff88678082302727f030cf 0x20980046046188228000300503501045,mw 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc 0x1f800001fc005bfb8304d11bd930c030 0x4788848a9c22dbeb8100d11b49304010,mw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 0xe0001fc000003dbf841962dc1ec30300 0xe11023c428c53cbf8009624c1ec10100,mw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 0x1ff7dd98618ce0e0fc0003 0x82014910511e77dd08218ce0e0a40002,mw 0xffff000000000000ffff000000000000ffff000000000000ffff0000 0x7e001ffe0261e607e0f00ff000c3c 0x822620163882414207e0600b4000428,mw 0xffffffff000000000000000000000000ffffffff0000000000000000 0x7fffe000047e07f800fff00000fc0 0x14459c38801043405f8009b200000a80,mw 0xffffffff00000000ffffffff00000000000000000000000000000000 0xfff80000000078007ffff000000ff000 0x186610210200000076d60000000aa000]
def m223Cuts : BTree CutSpec := (N (N (N (N (N (mc m223Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) (mc m223Raw 0x5555555500000000000000000000000055555555 5)) (N (mc m223Raw 0x550055000000000055005500 4) E)) (N (N (mc m223Raw 0xffffffff000000000000000000000000ffffffff 8) E) (N (mc m223Raw 0x11111111000000001111111100000000111111110000000011111111 5) E))) (N (N (N (mc m223Raw 0x33333333000000003333333300000000333333330000000033333333 9) (mc m223Raw 0x3030303000000000303030300000000030303030000000003030303 8)) (N (mc m223Raw 0xcccc000000000000cccc 4) E)) (N (N (mc m223Raw 0x55555555000000005555555500000000555555550000000055555555 8) E) (N (mc m223Raw 0x3333333300000000000000000000000033333333 6) E)))) (N (N (N (N (mc m223Raw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f 9) (mc m223Raw 0xf0f0f0f0 4)) (N (mc m223Raw 0xffff0000000000000000000000000000ffff 6) E)) (N (N (mc m223Raw 0xffff000000000000ffff000000000000ffff000000000000ffff 8) E) (N (mc m223Raw 0x1111000000000000111100000000000011110000000000001111 4) E))) (N (N (N (mc m223Raw 0xffffffff00000000ffffffff 8) (mc m223Raw 0x55000000000000005500000000000000550000000000000055 4)) (N (mc m223Raw 0x3333000000000000333300000000000033330000000000003333 6) E)) (N (N (mc m223Raw 0x5555000000000000555500000000000055550000000000005555 5) E) (N (mc m223Raw 0x333333330000000033333333 6) E)))))
theorem m223CutValid : ∀ ci < 20, ValidCut m223Mask m223Raw m223Goal (btreeGet ⟨0,0,[]⟩ 5 m223Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 105532 m187Low (by decide +kernel)
  · exact cv 108606 m187Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 14706256 m159Low (by decide +kernel)
  · exact cv 16270984 m222Low (by decide +kernel)
  · exact cv 14706256 m158Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 14681736 m143Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 14706192 m155Low (by decide +kernel)
  · exact cv 225555 m55Low (by decide +kernel)
  · exact cv 553368 m86Low (by decide +kernel)
  · exact cv 28947 m87Low (by decide +kernel)
  · exact cv 24788 m87Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 16270848 m217Low (by decide +kernel)
  · exact cv 553352 m86Low (by decide +kernel)
noncomputable def m223D : BTree NodeRec := (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5,6] [180226,311299,581636,712709,843782,9101320,9232394,11329547]) (e0 213096)) (N (el 57461 [1,10] [524572,852254,2785554,4882690]) E)) (N (N (el 13943 [0,3,9] [426130,491734,688338,7405764,9207934,9339007]) (e0 475240)) (N (ez 106616 [9208070]) E))) (N (N (N (el 5479 [0,1,2,3,4,5,6,10] [401544,499850,721036,737422,958592,991376,4751484,5152902,9347184]) (e1 299096 10)) (N (el 82026 [0,2] [2818344,6979836]) E)) (N (N (e0 41081) E) (N (el 139608 [0,10,13] [2949434]) E)))) (N (N (N (N (el 4183 [0,1,2,3,4,5,6,14,12,10] [786516,852054]) (e0 245848)) (N (el 65657 [3,5] [6979866]) E)) (N (N (el 21109 [0,1,2,3,4,5,17,10] [565413,598245,868593,2662585,4759716,4792548,4931824,6856888,9093254,9224327]) E) (N (el 127050 [5,10] [9077017]) E))) (N (N (N (el 8805 [0,1,2,4,5,6,9,7] [958642,2523310,6848620]) (e0 397400)) (N (ef 94581 4 [557354,2654508]) E)) (N (N (el 50535 [1,5] [557314,852230,4620542,4751620]) E) (N (ec 152437 [4,5]) E))))) (N (N (N (N (N (el 1111 [0,1,2,3,4,5,6,9] [434210,958530,2531376,4628529,6864924,6995997,7266368]) (e1 233813 2)) (N (e1 65585 12) E)) (N (N (el 20552 [0,1,2,3,4,5,6,10] [434406,450792,467076,844010,6865037,7135425]) E) (N (ef 115557 5 [9077002,9208077]) E))) (N (N (N (el 8309 [0,1,2,3,4,5,6,7,10,8] [589978,606364,852126,868512,958610,991394,3055780,4751462]) (e0 319848)) (N (ez 86136 [6979840]) E)) (N (N (el 49255 [0,2,7,10,8] [852224]) E) (N (el 147511 [0,6,10] [852288]) E)))) (N (N (N (N (el 4421 [0,1,2,3,4,5,6,7,10,13] [712804,827494,843880,860266,2465874,2793580,2924654,11329648]) (e0 254026)) (N (ec 78197 [1,3]) E)) (N (N (el 36932 [2,4,18,6,13] [7119094]) E) (N (el 135241 [1,2] [721204,852277]) E))) (N (N (N (el 12378 [0,1,2,3,4,5,6,8] [2924742,3055815,4751474,4882547,7119048,7250121]) (e0 450920)) (N (ef 102773 4 [393518,2654508,9076996]) E)) (N (N (el 53351 [0,1,4,16,8] [721168]) E) (N (e1 184424 8) E)))))) (N (N (N (N (N (N (el 71 [0,1,2,3,4,5,6,7] [827426,843812,860198,958504,974890,991276,2523160,2924590,5021744,5152818,13557812]) (e0 225637)) (N (ec 61496 [1,3,5,6,10]) E)) (N (N (el 20535 [0,2,6,7,10,8] [983262,2818272]) (e0 487528)) (N (e0 111975) E))) (N (N (N (el 8295 [4,9,16,7] [6979684]) (e1 307288 10)) (N (ef 82293 4 [6979838]) E)) (N (N (ec 49239 [4,16]) E) (N (e0 144245) E)))) (N (N (N (N (el 4199 [0,1,2,3,4,5,6,15,12,10] [720990,991328]) (e1 254001 12)) (N (e0 69753) E)) (N (N (e1 32864 5) E) (N (el 127097 [3,4,10] [9208091]) E))) (N (N (N (el 9847 [1,3,4,5] [393402,426130,458940,491710,688306,983232,2588824,2654384,4620452,4882616,9207920]) (e1 442456 10)) (N (ec 102474 [3,10]) E)) (N (N (el 53335 [0,2,7,10,8] [2949384]) E) (N (e1 159813 10) E))))) (N (N (N (N (N (ec 4167 [0,1,2,3,4,5,6,11,12,10,13]) (e0 234085)) (N (el 65624 [2,3,6] [9216262]) E)) (N (N (el 20599 [1,2,4,9,17,10] [983282,2949358]) E) (N (e0 122997) E))) (N (N (N (el 8313 [0,1,2,3,4,5,6,7] [688298,958636,4751466]) (e1 360772 4)) (N (e1 90229 3) E)) (N (N (el 49493 [0,4,5,6,9,7,10,13] [827650]) E) (N (ec 151621 [2,6,10]) E)))) (N (N (N (N (el 5207 [0,1,2,3,4,5,6,9,10,13] [958592,2654316,9347198]) (e1 262208 12)) (N (el 81994 [0,2,10] [2949416]) E)) (N (N (el 37749 [1,2,3,4,12] [4882678]) E) (N (el 135258 [1,2] [2949432]) E))) (N (N (N (el 12393 [0,1,2,3,4,5,6,8] [958668,4751478,7250126]) (e1 462952 17)) (N (e1 106552 17) E)) (N (N (el 53605 [0,1,3,4,5,6,10,8] [401684,499990,606488,827666,860442,4931852,5021950,5054734]) E) (N (e1 208986 2) E))))))) (N (N (N (N (N (N (N (el 22 [0,1,2,3,4,5,6] [581644,614414,712720,745490,843796,876566,2662424,2924570,9101340,9232414,11329568]) (e0 221285)) (N (ec 61488 [0,1,2,3,4,5,6,12]) E)) (N (N (el 16501 [0,1,2,3,4,5,6,9,17,10] [565394,598232,721114,737500,852187,868573,2662610,4759730,6856883,9093248,9224321]) (e0 479336)) (N (el 110679 [2,5] [721200]) E))) (N (N (N (el 8293 [0,1,2,3,4,5,6,9,16,7] [958610,991380]) (e1 299128 8)) (N (e0 82041) E)) (N (N (el 45620 [0,1,2,3,12,10] [606458]) E) (N (el 143477 [1,2,10] [852284]) E)))) (N (N (N (N (el 4187 [0,1,2,3,4,5,6,12,13] [557144,958554,7250012]) (e0 249957)) (N (el 69749 [0,1,2] [721184,852257,983330]) E)) (N (N (ec 29236 [0,2,5,12,10]) E) (N (ef 127093 6 [9077010,9208083]) E))) (N (N (N (el 8821 [0,1,2,3,4,5,6,7,10] [606388,958642,991414,3055800,6848622,7250097]) (e0 405592)) (N (ef 98421 6 [4751658,9076994]) E)) (N (N (el 53322 [0,2,3,6,8] [2793736,4694266,4890890,5021964]) E) (N (ef 155768 2 [2949444]) E))))) (N (N (N (N (N (el 1127 [0,1,2,3,4,5,6,10] [434216,450628,467014,589896,606282,958530,974924,991310,2531378,4628542,5152848,6864926,6996001,7266357]) (e0 234069)) (N (e1 65597 12) E)) (N (N (el 20554 [0,1,2,3,4,5,6,10] [565484,2662624,3055854,4759732,6856912,7250160,9093263]) E) (N (el 118872 [0,10] [2949426,6979857]) E))) (N (N (N (el 8311 [0,2,3,7,10,8] [721062,983208,6979688]) (e0 356453)) (N (ec 90196 [2,3,6]) E)) (N (N (ec 49257 [0,1,3,5,15,7]) E) (N (el 147559 [1,4] [852290]) E)))) (N (N (N (N (el 4453 [0,1,2,3,4,5,6,10,8] [606322,696422,712820,729206,843896,2465890,2793594,2924668,5070940,11329662]) (ec 254057 [3,5])) (N (ec 81992 [1,2,6]) E)) (N (N (el 36981 [0,3] [852216]) E) (N (el 135256 [1,10] [565558,9093407]) E))) (N (N (N (el 12391 [0,2,5,7,10,8] [721098,3080390,6979700,7110777]) (e0 455000)) (N (e1 106544 7) E)) (N (N (el 53589 [0,1,3,4,5,6,10,8] [827666,4931850]) E) (N (e0 200778) E)))))) (N (N (N (N (N (N (el 103 [0,1,2,3,4,5,6,8] [720950,737336,827432,843834,860220,958505,974907,991293,2523162,2654235,5021758,5152831,13557824]) (e0 229480)) (N (el 62069 [4,5] [4882686,6979844]) E)) (N (N (el 20537 [0,1,2,3,4,5,6,10] [589956,958690,7250148]) E) (N (el 115045 [2,19] [721202,6979848]) E))) (N (N (N (el 8297 [0,1,2,3,4,5,6,7] [958614,3055768]) (e1 307320 8)) (N (e1 86104 10) E)) (N (N (el 49253 [0,2,3,5,7,10,8] [737532,2924798]) E) (N (el 147509 [0,1,6,10] [737598]) E)))) (N (N (N (N (el 4203 [0,1,2,3,4,5,6,12,10] [4620386]) (e1 254013 12)) (N (el 77941 [0,2] [721188,983334]) E)) (N (N (ec 32872 [1,2,6,14,10]) E) (N (e1 131132 8) E))) (N (N (N (el 12376 [0,1,2,3,4,5,6,8] [712898,843971,11329732]) (e0 446533)) (N (e1 102521 10) E)) (N (N (el 53337 [3,5,11,8] [5021966]) E) (N (e0 181093) E))))) (N (N (N (N (N (el 4171 [0,1,2,3,4,5,6,12,10] [4620370]) (e0 242277)) (N (ef 65626 1 [6979864]) E)) (N (N (el 20601 [0,1,2,3,4,5,6,10] [565492,4759734,6856916,9224337]) E) (N (ef 123765 4 [9077006]) E))) (N (N (N (el 8549 [0,1,2,4,5,6,16,7] [2523310,3055792,7250097]) (e1 376880 7)) (N (el 94516 [0,1,2,4,5,6,9] [827690]) E)) (N (N (el 49509 [0,3,5,6,7,10] [827650,2924804]) E) (N (el 151925 [1,14] [852292]) E)))) (N (N (N (N (el 5223 [0,1,2,3,4,5,6,10] [393346,458884,557158,958592,2654318,4751482,5152902]) (e0 262248)) (N (ec 82024 [1,2,6]) E)) (N (N (ec 41048 [1,2,3,6,10]) E) (N (ef 139384 2 [2818362]) E))) (N (N (N (el 12901 [0,1,2,3,4,5,6,10,8] [606416,958674,991444,5062856,5152933,5185743,6848634,6979709]) (e0 471130)) (N (e1 106556 7) E)) (N (N (ef 54631 3 [557330]) E) (N (e0 209253) E))))))))
noncomputable def m223Ck : Nat → Bool := checkNode m223Mask m223Goal (Nat.sub (Nat.shiftLeft 1 m223Pairs.length) 1) symMain 163 10 m223Ws m223D 8 m223Cuts 5
theorem q57 : tb 0 24 m223Ck = true := by decide +kernel
theorem q58 : tb 24 24 m223Ck = true := by decide +kernel
theorem q59 : tb 48 24 m223Ck = true := by decide +kernel
theorem q60 : tb 72 24 m223Ck = true := by decide +kernel
theorem q61 : tb 96 24 m223Ck = true := by decide +kernel
theorem q62 : tb 120 24 m223Ck = true := by decide +kernel
theorem q63 : tb 144 19 m223Ck = true := by decide +kernel
theorem m223All : treeBlock 0 163 m223Ck = true := (tm 0 72 91 (tm 0 24 48 q57 (tm 24 24 24 q58 q59)) (tm 72 48 43 (tm 72 24 24 q60 q61) (tm 120 24 19 q62 q63)))
theorem m223Low : LowerM m223Mask m223Raw m223Goal 11 := by
  have hraw : m223Ws.map Wire.val = m223Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 20)) m223D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m223Pairs) (sym := symMain) (count := 163) (rootFuel := 10) (fdepth := 8) (cdepth := 5) (dag := m223D) (cutTree := m223Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m223Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 20)) (defv := (0,[],[])) rfl hnc 8 i
      rw [hraw]; exact m223CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m223All

def m247Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def m247Goal : Word := 0xff00ff00ff00fe00ff00ff00fe00fe00ff00fe00ff00fa00fe00fc00ee0000
def m247Raw : List Word := [0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000]
theorem m247Ess : ∀ a ∈ m247Raw, Essential m247Mask m247Goal m247Raw a :=
  checkAllEss_sound (ps := [4113,4114,8228,273,546,321,385]) (by decide +kernel)
def m247Pairs : List (Row × Row) := mkPairs [4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,40992,41088,4867,5381,5396,5638,5652,8963,8993,9477,9505,9734,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,21058,21524,24865,24928,25154,25184,25696,28720,28768,33539,34053,34310,37264,37520,37908,38032,41249,45104,45200,49600,49730,49856,50368,53392,53440,57440,57536,5895,9991,18183,34567,4355,4357,4372,4385,4400,4496,4611,4614,4628,4656,4674,4752,8707,8710,8737,8752,8770,8800,9221,9222,9236,9249,9264,9312,16643,16645,16673,16706,16736,16832,17413,17414,17428,17474,17504,17600,20500,20528,20546,20576,20624,20672,33027,33029,33057,33168,33216,33283,33286,33346,33424,33472,33797,33798,33812]
def m247Ws : List Wire := [mw 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa 0xf8007e00007fe0245830e379c0c303 0x2138008e48a097e0041810a178c04101,mw 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc 0x1f00000007ff81e0c0a8c7649e43003c 0x47088512126983e0402847608a410014,mw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0 0xe0001f81f80001e103310b98e78c0cc0 0xe210238438430de001300988a7840440,mw 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 0x7e000001ffe261bc60c1f07c0300f 0x88426200a11668021bc2081e0500100a,mw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 0x1ffe000581c07f01ff83000f0 0x214829c58430080c07b017501000a0,mw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 0x7fffe0000009fe007ffe000003f00 0x14859c710608001de005e64000002a00,mw 0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000 0xfff800000000011ffff80000003fc000 0x18c6104000104017b2c00000002a8000]
def m247Cuts : BTree CutSpec := (N (N (N (N (N (mc m247Raw 0x55005500550055005500550055005500550055005500550055005500550055 10) (mc m247Raw 0x500000005000000000000000000000005000000050000000000000000 4)) (N (mc m247Raw 0x30003000000000003000300000000 4) (mc m247Raw 0xf000f000f000f000f000f000f000f 7))) (N (N (mc m247Raw 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 9) (mc m247Raw 0xff00ff0000000000ff00ff 6)) (N (mc m247Raw 0x330033000000000033003300000000003300330000000000330033 6) (mc m247Raw 0xff000000ff000000ff000000ff 5)))) (N (N (N (mc m247Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9) (mc m247Raw 0xff000000ff0000000000000000000000ff000000ff 6)) (N (mc m247Raw 0x330000003300000000000000000000003300000033 5) (mc m247Raw 0xf000f000f000f0000000000000000000f000f000f000f 6))) (N (N (mc m247Raw 0x33003300330033003300330033003300330033003300330033003300330033 9) (mc m247Raw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f 7)) (N (mc m247Raw 0x30003000000000003000300000000000300030000000000030003 5) (mc m247Raw 0xf000f000f000f 4))))) (N (N (N (N (mc m247Raw 0xff00ff00ff00ff00ff00ff00ff00ff 9) (mc m247Raw 0x330033003300330033003300330033 7)) (N (mc m247Raw 0x3300000033000000330000003300000033000000330000003300000033 6) (mc m247Raw 0x33000000330000003300000033 4))) (N (N (mc m247Raw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f 9) (mc m247Raw 0xf000f00000000000f000f 5)) (N (mc m247Raw 0x3300330000000000330033 5) (mc m247Raw 0xff00ff00ff00ff 5)))) (N (N (N (mc m247Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) (mc m247Raw 0xf0000000f00000000000000000000000f0000000f 5)) (N (mc m247Raw 0x1100000011000000000000000000000011000000110000 4) (mc m247Raw 0xff00000000000000ff00000000000000ff00000000000000ff 5))) (N (N (mc m247Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) (mc m247Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6)) (N (mc m247Raw 0x3300330033003300000000000000000033003300330033 7) E)))))
theorem m247CutValid : ∀ ci < 31, ValidCut m247Mask m247Raw m247Goal (btreeGet ⟨0,0,[]⟩ 5 m247Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16433288 m246Low (by decide +kernel)
  · exact cv 1753224 m119Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 14868560 m183Low (by decide +kernel)
  · exact cv 16433160 m243Low (by decide +kernel)
  · exact cv 15917072 m243Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 14707202 m155Low (by decide +kernel)
  · exact cv 1318919 m89Low (by decide +kernel)
  · exact cv 270290946 m81Low (by decide +kernel)
  · exact cv 12613648 m155Low (by decide +kernel)
  · exact cv 1049606 m89Low (by decide +kernel)
  · exact cv 1592832 m89Low (by decide +kernel)
  · exact cv 1449991 m241Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 5406726 m241Low (by decide +kernel)
  · exact cv 14844040 m167Low (by decide +kernel)
  · exact cv 1314823 m89Low (by decide +kernel)
  · exact cv 1589384 m87Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 1511431 m241Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 549184 m86Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
  · exact cv 14704720 m151Low (by decide +kernel)
  · exact cv 188496 m55Low (by decide +kernel)
  · exact cv 180360 m55Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
noncomputable def m247D : BTree NodeRec := (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5,6] [2416642,2547716,2678790,2809864,2940938,4644873,4775943,4907013,5038091,6873100,7004174,7135248,9101325,9232402,11329553]) (e1 344960 3)) (N (el 26231 [0,1,2,3,4,5,6,8,16,11] [393446]) E)) (N (N (el 9591 [0,1,2,3,4,5,6,20,9,13,8] [7381182,7413952,9478342]) E) (N (ec 91767 [9,13,8]) E))) (N (N (N (el 5223 [0,1,2,3,4,5,6,7,18,19,10,8,16,11] [7250080,7381160,9347244,9478324,11444397,11575477]) E) (N (ec 46439 [19,14,8]) E)) (N (N (el 16981 [0,1,2,3,4,5,6,15,18,19,10,16] [13557978]) E) (N (e1 245840 6) E)))) (N (N (N (N (el 871 [0,1,2,3,4,5,6,11] [565294,598156,696415,729230,745616,827512,860306,876692,958598,991382,2662454,2793573,2924668,4759658,5152920,9101346,9232474,11329629,11460675,13557889]) E) (N (ec 32859 [0,1,2,3,4,5,6,28,8,25,16,11]) E)) (N (N (el 12661 [0,1,2,3,4,5,6,17,12,13,8] [2523346,2924756,13557974]) E) (N (ec 161399 [12,10,8]) E))) (N (N (N (el 8313 [0,1,2,3,4,5,6,9,10,8] [696516]) E) (N (e1 61557 16) E)) (N (N (ec 24649 [0,1,2,3,4,5,6,27,8,11]) E) (N (e1 282672 20) E))))) (N (N (N (N (N (el 343 [0,1,2,3,4,5,6,15,16,11] [565269,696362,827464,958558,2662428,2793522,4890720,5021794,5152868,9232471,9363558,13557864]) E) (N (el 28793 [0,1,2,3,4,5,6,18,19,10] [958702]) E)) (N (N (ec 12389 [0,1,2,3,4,5,6,15,12,8,16]) E) (N (e1 122940 9) E))) (N (N (N (ec 8281 [0,1,2,3,4,5,6,9,10,8]) E) (N (el 50551 [19,8,16] [7340288,7405822]) E)) (N (N (el 18039 [0,1,2,3,4,5,6,15,20,13,8] [590044,7381182,9478342,11575514]) E) (N (el 267895 [6,18,13,8] [590086]) E)))) (N (N (N (N (el 4213 [0,1,2,3,4,5,6,24,17,7,8] [696482,786596,852134,958627,11460776]) E) (N (ec 33397 [0,1,2,3,4,5,6,16,11]) E)) (N (N (el 13671 [0,1,2,3,4,5,6,18,12,10,8,11] [7250080,7282890,7381196,7413968,9347244,9478358,11575512]) E) (N (ef 173687 1 [9208066]) E))) (N (N (N (ec 9303 [0,1,2,3,4,5,6,23,9,14,8,16]) E) (N (ec 69704 [0,1,2,3,4,5,6,8,16,11]) E)) (N (N (el 24693 [0,1,2,3,4,5,6,20,8,11] [655584,721122]) E) (N (el 282745 [6,20,10,8] [2720006,2916612]) E)))))) (N (N (N (N (N (N (el 311 [0,1,2,3,4,5,6,9,10,11] [565268,598052,696358,729128,827434,860204,958510,991280,2924594,4890676,5152822,9101368,9232442,9363516,11329598,11460672,13557826]) (e1 446568 4)) (N (ec 28777 [0,1,2,3,4,5,6,18,19,10,8]) E)) (N (N (el 12361 [0,1,2,3,4,5,6,12,13,8] [11329738]) E) (N (ec 98389 [0,1,2,3,4,5,6,9,10,8]) E))) (N (N (N (el 8265 [0,1,2,3,4,5,6,9,10,8] [958650,7250108]) E) (N (e1 49248 3) E)) (N (N (ec 17013 [0,1,2,3,4,5,6,15,8,16]) E) (N (e1 249977 16) E)))) (N (N (N (N (el 4165 [0,1,2,3,4,5,6,22,7,9,8,16,11] [991390]) E) (N (ec 32875 [0,1,2,3,4,5,6,28,8,11]) E)) (N (N (el 12917 [0,1,2,3,4,5,6,20,12,21,13,8] [2523346,13557976]) E) (N (ec 164197 [0,1,2,3,4,6,17,12,13,8]) E))) (N (N (N (ec 8789 [0,1,2,3,4,5,6,9,10,8,11]) E) (N (ec 62839 [1,5,17,19,10,11]) E)) (N (N (ec 24677 [0,1,2,3,4,5,6,18,8]) E) (N (e1 282680 20) E))))) (N (N (N (N (N (el 839 [0,1,2,3,4,5,6,8,11] [565286,598128,696393,729202,827508,860278,958584,991354,2662452,2793571,3055740,4759634,5021822,11329599,13557888]) E) (N (el 32841 [0,1,2,3,4,5,6,28,8,11] [729270,2793656]) E)) (N (N (el 12405 [0,1,2,3,4,5,6,17,20,12,13,8] [13557964]) E) (N (ec 157303 [13,10,8]) E))) (N (N (N (el 8297 [0,1,2,3,4,5,6,9,16,11] [13557952]) E) (N (ec 54631 [3,5,19,10,11]) E)) (N (N (el 21093 [0,1,2,3,4,5,6,17,20,21,13,8] [2523346,13557982]) E) (N (e1 274553 8) E)))) (N (N (N (N (el 4453 [0,1,2,3,4,5,6,15,7,8,16] [7119019,7250094]) E) (N (ec 36969 [0,1,2,3,4,5,6,20,21,13,11]) E)) (N (N (el 13943 [0,1,2,3,4,5,6,12,13,8,11] [4686030]) E) (N (el 213064 [0,1,2,3,4,6,20,21,8] [9347332]) E))) (N (N (N (el 9335 [0,1,2,3,4,5,6,24,9,8,16,11] [426146,491720]) E) (N (ec 74613 [0,1,2,4,5,6,24,9,10,8,25]) E)) (N (N (ec 24949 [0,1,2,3,4,5,6,8,11]) E) (N (e1 299125 16) E))))))) (N (N (N (N (N (N (N (el 295 [0,1,2,3,4,5,6,7,8] [565268,696342,827413,958488,2793498,2924572,3055646,4759581,4890651,5152799,9232416,9363490,13557795]) (e0 431463)) (N (el 28745 [0,1,2,3,4,5,6,18,19,11] [13557992]) E)) (N (N (ec 9847 [0,1,2,3,4,5,6,9,10,8,16,11]) E) (N (ec 94297 [0,1,2,3,4,5,6,8,25,16]) E))) (N (N (N (el 5239 [0,1,2,3,4,5,6,7,8,25,16,11] [458934,590008,4751538]) E) (N (e1 49237 11) E)) (N (N (ec 16997 [0,1,2,3,4,5,6,15,8,16]) E) (N (ec 245848 [0,1,2,3,4,5,8]) E)))) (N (N (N (N (el 1127 [0,1,2,3,4,5,6,20,21,13,8] [565324,598170,696397,729243,827512,860316,958585,991389,2662484,2793557,4759660,4890733,9232448,9363560,11329641,11460673,13557898]) E) (N (el 32873 [0,1,2,3,4,5,6,28,8] [958716]) E)) (N (N (ec 12885 [0,1,2,3,4,5,6,12,13,14,8,11]) E) (N (el 164148 [0,1,2,3,4,5,6,17,20,12,21,13,8] [11329794]) E))) (N (N (N (el 8549 [0,1,2,3,4,5,6,15,9,10,16,11] [13557958]) E) (N (ec 61781 [0,1,2,4,5,6,17,7,8,25,16,11]) E)) (N (N (ec 24665 [0,1,2,3,4,5,6,27,8,16]) E) (N (e1 282676 8) E))))) (N (N (N (N (N (el 359 [0,1,2,3,4,5,6,17,8] [565272,696366,827468,958558,2662430,2924624,4890730,5021804,9101415,9363517,11460718]) E) (N (el 30327 [0,1,2,3,4,5,6,20,18,8,16] [393456,426226,458996,491766,958668,991480,1089741,1122553,3055832,3186905,5152990,5284063,7250110,7282920,7381183,7413993,9478363,11444442]) E)) (N (N (ec 12393 [0,1,2,3,4,5,6,12,13,14,16]) E) (N (ec 140647 [12,19,8]) E))) (N (N (N (el 8293 [0,1,2,3,4,5,6,15,18,9,10,16] [13557950]) E) (N (ec 54101 [0,2,3,4,5,6,22,7,12,14,8,11]) E)) (N (N (el 21077 [0,1,2,3,4,5,6,17,8,25,11] [6987954,7119060]) E) (N (ec 274504 [0,1,2,3,4,5,6,16,11]) E)))) (N (N (N (N (el 4437 [0,1,2,3,4,5,6,7,12,13,14,8] [6987946,11329708]) E) (N (el 36937 [0,1,2,3,4,5,6,20,21,8] [3055836,13558008]) E)) (N (N (el 13687 [0,1,2,3,4,5,6,12,13,8,11] [4751572]) E) (N (el 198263 [4,6,10,8] [852228]) E))) (N (N (N (ec 9319 [0,1,2,3,4,5,6,26,9,19,10,8,16,11]) E) (N (ec 73845 [0,1,2,3,4,5,6,9,10,8]) E)) (N (N (el 24697 [0,1,2,3,4,5,6,27,8] [991460]) E) (N (ec 290901 [0,1,2,3,4,5,6,28,8,25,16]) E)))))) (N (N (N (N (N (N (el 327 [0,1,2,3,4,5,6,12,13,14,8] [565270,598084,696358,729158,827464,860234,958540,991310,2662426,3055696,4890706,5152852,9101398,9232441,11329624,11460698,13557852]) (e1 475208 8)) (N (el 28789 [0,1,2,3,4,5,6,18,16,11] [590058,991468]) E)) (N (N (ec 12377 [0,1,2,3,4,5,6,12,13,14,11]) E) (N (ec 104055 [2,4,13,8]) E))) (N (N (N (ec 8277 [0,1,2,3,4,5,6,12,9,8,11]) E) (N (el 49256 [0,1,2,3,4,5,6,8] [11329790]) E)) (N (N (el 17527 [0,1,2,3,4,5,6,24,15,8,16] [2654382]) E) (N (ec 262192 [0,1,2,3,4,5,6,29,30,8]) E)))) (N (N (N (N (el 4181 [0,1,2,3,4,5,6,7,23,12,14,8] [11329696]) E) (N (ec 32889 [0,1,2,3,4,5,6,28,25,16,11]) E)) (N (N (el 13399 [0,1,2,3,4,5,6,22,12,14,8,11] [2654378]) E) (N (ef 165495 1 [9208066]) E))) (N (N (N (el 8821 [0,1,2,3,4,5,6,9,10,8,25,11] [4923580]) E) (N (ec 69688 [0,1,2,3,4,5,6,28,8,16]) E)) (N (N (ec 24681 [0,1,2,3,4,5,6,27,8,16,11]) E) (N (e1 282684 18) E))))) (N (N (N (N (N (el 855 [0,1,2,3,4,5,6,18,19,10,16] [565290,598146,696363,729219,827508,860292,958598,991368,2793569,4759648,9101344,9232472,9363566,11329625,11460719,13557898]) E) (N (el 32857 [0,1,2,3,4,5,6,28,8,25,16,11] [696570,729270]) E)) (N (N (el 12409 [0,1,2,3,4,5,6,12,14,8] [3055822,13557968]) E) (N (ec 160117 [0,1,2,3,4,6,12,14,8]) E))) (N (N (N (el 8309 [0,1,2,3,4,5,6,17,9,8,25,11] [729282]) E) (N (ec 58229 [0,1,2,4,5,6,24,15,7,8,16]) E)) (N (N (el 21879 [0,1,2,3,4,5,6,17,18,10,8,11] [7250088,7381196,9347252,9478358,11575518]) E) (N (e1 278645 8) E)))) (N (N (N (N (el 4469 [0,1,2,3,4,5,6,17,7,8] [958640,2793650,6987951,11460788]) E) (N (ec 41081 [0,1,2,3,4,5,6,8,16,11]) E)) (N (N (ec 16501 [0,1,2,3,4,5,6,17,15,8,16]) E) (N (ef 222839 3 [9208066]) E))) (N (N (N (ec 9575 [0,1,2,3,4,5,6,9,10,8,16,11]) E) (N (ec 87671 [13,10,8]) E)) (N (N (ec 25189 [0,1,2,3,4,5,6,8]) E) (N (e0 341351) E))))))))
noncomputable def m247Ck : Nat → Bool := checkNode m247Mask m247Goal (Nat.sub (Nat.shiftLeft 1 m247Pairs.length) 1) symMain 132 11 m247Ws m247D 8 m247Cuts 5
theorem q64 : tb 0 24 m247Ck = true := by decide +kernel
theorem q65 : tb 24 24 m247Ck = true := by decide +kernel
theorem q66 : tb 48 24 m247Ck = true := by decide +kernel
theorem q67 : tb 72 24 m247Ck = true := by decide +kernel
theorem q68 : tb 96 24 m247Ck = true := by decide +kernel
theorem q69 : tb 120 12 m247Ck = true := by decide +kernel
theorem m247All : treeBlock 0 132 m247Ck = true := (tm 0 72 60 (tm 0 24 48 q64 (tm 24 24 24 q65 q66)) (tm 72 24 36 q67 (tm 96 24 12 q68 q69)))
theorem m247Low : LowerM m247Mask m247Raw m247Goal 12 := by
  have hraw : m247Ws.map Wire.val = m247Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 31)) m247D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m247Pairs) (sym := symMain) (count := 132) (rootFuel := 11) (fdepth := 8) (cdepth := 5) (dag := m247D) (cutTree := m247Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m247Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 31)) (defv := (0,[],[])) rfl hnc 8 i
      rw [hraw]; exact m247CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m247All

def m251Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def m251Goal : Word := 0xf0f0f0f0f0f0f0e0f0f0f0f0f0e0f0e0f0f0e0e0f0f0a0a0e0e0e0c0e0e0a00
def m251Raw : List Word := [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000]
theorem m251Ess : ∀ a ∈ m251Raw, Essential m251Mask m251Goal m251Raw a :=
  checkAllEss_sound (ps := [2057,4114,265,273,546,321,385]) (by decide +kernel)
def m251Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,16641,16704,20496,20544,33025,33152,33282,33408,34824,34944,40992,41088,2819,2826,4867,6424,6666,6680,8963,8993,10529,10536,10762,10792,12577,12592,12848,17155,17218,18760,21058,22552,22600,24865,24928,25154,25184,28720,28768,33539,35338,37264,37520,38936,39056,41249,43048,45104,45200,49600,49730,49856,51272,51392,53392,53440,57440,57536,14648,14904,19274,23114,26984,27210,27240,30776,30824,47160,51786,59496,2307,2314,2328,2337,2344,2376,4355,4376,4385,4400,4496,4611,4618,4632,4656,4674,4752,8707,8714,8737,8744,8752,8770,8800,16643,16673,16706,16712,16736,16832,20504,20528,20546,20552,20576,20624,20672,33027,33057,33168,33216,33283,33290,33346,33424,33472,34826,34840,34856,34888]
def m251Ws : List Wire := [mw 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a 0x780fc001ffc0540222863b3cf0330f 0x9800c282524000002082091c501105,mw 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c 0xf80003ffe0011b80c05985ccf70c0f0 0x13884151a610d0b00401885845704050,mw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 0xf0000000000ffffc305901a0f3b30003 0xf10092050c2dbffc104901a0e3a10002,mw 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 0x7f0007ff00e2cc19e61c703c00c3c 0x2422300859a10a0c419e208602800428,mw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 0x3f80002fcf01e07e07fc0c00c0 0x401124ae10c62f4d00e07607b8040080,mw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000 0x7ffc0000037f3fe007ff800000f00 0x8a45cf30200835f3be005d7000000a00,mw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 0xfff8000000003803ffff8000000ff000 0xc66080041000002eb160000000aa000]
def m251Cuts : BTree CutSpec := (N (N (N (N (N (N (mc m251Raw 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f 9) (mc m251Raw 0x300000003000000030000000300000003000000030000000300000003 4)) (N (mc m251Raw 0x3000300030003000300030003000300030003000300030003000300030003 7) E)) (N (N (mc m251Raw 0x5000500050005000500050005000500050005000500050005000500050005 7) E) (N (mc m251Raw 0xf000f000f000f0000000000000000000f000f000f000f 6) E))) (N (N (N (mc m251Raw 0x303030303030303030303030303030303030303030303030303030303030303 9) (mc m251Raw 0xf0f00000000000000000000000000000f0f 5)) (N (mc m251Raw 0xf000f00000000000f000f 5) E)) (N (N (mc m251Raw 0x3030303000000000303030300000000 5) E) (N (mc m251Raw 0xf0f0f0f000000000f0f0f0f 6) E)))) (N (N (N (N (mc m251Raw 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f 9) (mc m251Raw 0xf0f0f0f0f0f0f0f 5)) (N (mc m251Raw 0x30303030303030300000000000000000303030303030303 6) E)) (N (N (mc m251Raw 0xf000f000f000f000f000f000f000f 7) E) (N (mc m251Raw 0x50005000500050005000500050005 4) E))) (N (N (N (mc m251Raw 0x3030303000000000303030300000000030303030000000003030303 8) (mc m251Raw 0x303030300000000000000000000000003030303 5)) (N (mc m251Raw 0x5000500050005000500050005000500 4) E)) (N (N (mc m251Raw 0x50505050505050500000000000000000505050505050505 6) E) (N (mc m251Raw 0x50005000000000005000500000000000500050000000000050005 4) E))))) (N (N (N (N (N (mc m251Raw 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f 9) (mc m251Raw 0x3030000030300000000000000000000030300000303 5)) (N (mc m251Raw 0x30300000303000003030000030300000303000003030000030300000303 6) E)) (N (N (mc m251Raw 0x50500000505000000000000000000000505000005050000000000000000 5) E) (N (mc m251Raw 0x500050005000500000000000000000005000500050005 5) E))) (N (N (N (mc m251Raw 0xf0f00000f0f000000000000000000000f0f00000f0f 8) (mc m251Raw 0x303000000000000030300000000000003030000000000000303 5)) (N (mc m251Raw 0xf0f0f0f0000000000000000000000000f0f0f0f 6) E)) (N (N (mc m251Raw 0x30003000000000003000300000000 4) E) (N (mc m251Raw 0x5050505000000000505050500000000050505050000000005050505 5) E)))) (N (N (N (N (mc m251Raw 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f 9) (mc m251Raw 0xf000f000f000f 4)) (N (mc m251Raw 0xf000f00000000000f000f00000000000f000f00000000000f000f 6) E)) (N (N (mc m251Raw 0x500000005000000000000000000000005000000050000000000000000 4) E) (N (mc m251Raw 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f 6) E))) (N (N (N (mc m251Raw 0x505050505050505050505050505050505050505050505050505050505050505 8) (mc m251Raw 0xf0f0f0f 4)) (N (mc m251Raw 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f 7) E)) (N (N (mc m251Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 8) E) (N (mc m251Raw 0x505050500000000000000000000000005050505 4) E))))))
theorem m251CutValid : ∀ ci < 40, ValidCut m251Mask m251Raw m251Goal (btreeGet ⟨0,0,[]⟩ 6 m251Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 14861832 m187Low (by decide +kernel)
  · exact cv 105532 m187Low (by decide +kernel)
  · exact cv 1512967 m249Low (by decide +kernel)
  · exact cv 16433160 m243Low (by decide +kernel)
  · exact cv 16434688 m249Low (by decide +kernel)
  · exact cv 7606279 m217Low (by decide +kernel)
  · exact cv 16270848 m217Low (by decide +kernel)
  · exact cv 1512999 m123Low (by decide +kernel)
  · exact cv 10440705 m241Low (by decide +kernel)
  · exact cv 1075058183 m89Low (by decide +kernel)
  · exact cv 3833860 m241Low (by decide +kernel)
  · exact cv 1075597313 m81Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 291101 m87Low (by decide +kernel)
  · exact cv 1754632 m123Low (by decide +kernel)
  · exact cv 16433152 m241Low (by decide +kernel)
  · exact cv 29099 m87Low (by decide +kernel)
  · exact cv 1835363 m87Low (by decide +kernel)
  · exact cv 8420360 m155Low (by decide +kernel)
  · exact cv 1573380 m89Low (by decide +kernel)
  · exact cv 14697992 m155Low (by decide +kernel)
  · exact cv 135270824 m86Low (by decide +kernel)
  · exact cv 1511431 m241Low (by decide +kernel)
  · exact cv 14699009 m155Low (by decide +kernel)
  · exact cv 1857537 m89Low (by decide +kernel)
  · exact cv 1053096 m86Low (by decide +kernel)
  · exact cv 29067 m87Low (by decide +kernel)
  · exact cv 16590 m87Low (by decide +kernel)
  · exact cv 160139 m55Low (by decide +kernel)
  · exact cv 279024 m86Low (by decide +kernel)
  · exact cv 291096 m86Low (by decide +kernel)
  · exact cv 29096 m86Low (by decide +kernel)
  · exact cv 788999 m89Low (by decide +kernel)
  · exact cv 33123 m55Low (by decide +kernel)
  · exact cv 278848 m86Low (by decide +kernel)
  · exact cv 786951 m89Low (by decide +kernel)
  · exact cv 1850368 m89Low (by decide +kernel)
  · exact cv 1849344 m89Low (by decide +kernel)
  · exact cv 16584 m86Low (by decide +kernel)
noncomputable def m251D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5,6] [188418,221188,319494,352264,450570,483340,581646,614416,712722,745492,811030,843800,876570,909339,2416668,2547742,2809888,2940939,3006477,4644893,4775970,4907043,5038087,5103625,6873121,7135235,7200773,9101348,9232403,9297941,11329551,11395089]) (e1 3981376 22)) (N (ec 843897 [0,2,3,4,15,5,6,10,16,8,24,25]) E)) (N (N (el 168053 [1,2,4,5,6,7,8,17,22] [404150,740412,2501304,2599884,2673726]) E) (N (e0 2027608) E))) (N (N (N (el 82773 [2,16,8] [2459728,2656356]) E) (N (e0 1450365) E)) (N (N (el 426036 [2,15,5,7,10,12,9,22] [568328,601764,2665988]) E) (N (ec 2936936 [5,9]) E)))) (N (N (N (N (e1 28785 15) (e0 5522261)) (N (ec 1220712 [5,9]) E)) (N (N (el 286793 [0,1,2,3,4,6,10,8,22,26,11] [699754]) E) (N (ez 2330692 [4886864]) E))) (N (N (N (e1 131205 9) E) (N (ef 1658952 2 [2429049]) E)) (N (N (el 663671 [15,6,8,22] [855862,1118008,2363188,2428623]) E) (N (e1 3367269 20) E))))) (N (N (N (N (N (el 8517 [0,1,2,3,4,5,6,7,8,17,9] [959297,3056775]) (e0 4608376)) (N (e0 1097784) E)) (N (N (e1 204917 9) E) (N (e1 2162805 9) E))) (N (N (N (ef 102471 3 [2427232]) E) (N (ef 1556820 2 [6852862]) E)) (N (N (ec 503893 [0,1,2,3,4,5,6,7,10,8,29,13]) E) (N (e0 3072089) E)))) (N (N (N (N (el 50039 [0,1,2,3,4,15,5,6,7,18,9,11] [395208,403402,460748,468942,731088,2655286,7145342,7161752]) (e0 7159912)) (N (e1 1327208 12) E)) (N (N (el 360502 [5,7,9] [462310]) E) (N (e1 2687044 22) E))) (N (N (N (el 143435 [3,22] [428168]) E) (N (e1 1839224 9) E)) (N (N (el 750951 [0,1,2,4,15,5,6,7,12,9] [405462,471000]) E) (N (ec 3805213 [3,6,13,22]) E)))))) (N (N (N (N (N (N (el 4211 [0,1,2,3,4,15,6,7,10] [230122,238316,492270,557808,688882,754420,819958,828152,885498,951036,1082110,1090304,1147650,2392836,2409222,2925164,2957992,3187402,3220190,4621064,4629258,4752140,7119630,7152400,9216786,9478932]) (e1 4206884 22)) (N (e0 958585) E)) (N (N (el 180329 [2,4,15,7,17,22] [560318,2395132]) E) (N (e1 2101354 1) E))) (N (N (N (el 94314 [0,1,2,3,4,6,17,9,11] [2443426,3025062,3057832,3090602,3123372,5154990]) E) (N (e0 1507464) E)) (N (N (el 459397 [3,5,20,12,22] [9506412]) E) (N (e0 3031125) E)))) (N (N (N (N (el 38519 [0,1,2,3,4,15,5,6,7,28,14,12,9] [394990,427760,460530,493299,566932,599769,959739,992979,2664094,3057387,4638357,4703960,4900511,7251194,7284434,11445994]) (e1 6332532 9)) (N (ef 1273960 5 [5181580]) E)) (N (N (el 328517 [2,3,4,5,6,7,10,16,9] [3059114,5049760,5156129,7253285]) E) (N (el 2429022 [2,4,5,6,10,8,13,11] [168116]) E))) (N (N (N (el 135513 [2,4,15,5,6,10,12,22] [371508,4934398]) E) (N (ez 1737557 [2658602]) E)) (N (N (e1 725129 9) E) (N (ef 3690632 8 [2953690]) E))))) (N (N (N (N (N (el 20567 [0,1,2,3,4,5,6,7,27,12,9,11] [591282,607668,1058230,1091000,1123770,1156540,3081662,3188160,9479299]) (e1 5194044 22)) (N (e1 1192021 22) E)) (N (N (ec 233528 [0,1,2,3,4,15,5,6,34,9,35]) E) (N (ec 2240588 [2,22]) E))) (N (N (N (e1 110705 15) E) (N (e1 1610348 3) E)) (N (N (el 581680 [0,1,2,3,4,15,5,6,7,34,12,9,35,13] [823072]) E) (N (ef 3248232 5 [3084728]) E)))) (N (N (N (N (ec 69733 [0,1,2,3,4,5,6,10,8,21,24,19,12,9]) (e0 7717240)) (N (el 1384492 [2,4,5,6] [299110,561255,692404,757942,823480,954553]) E)) (N (N (el 393605 [1,15,5,12,9,13] [986656,2362914,2460451]) E) (N (e0 2789512) E))) (N (N (N (el 148329 [4,7,17] [560076,6917034,9079754]) E) (N (ez 1938261 [2592954]) E)) (N (N (el 782409 [15,8,17] [559322,626720,692249,757794,6982829,9244622]) E) (N (ec 3916149 [0,1]) E))))))) (N (N (N (N (N (N (N (el 343 [0,1,2,3,4,5,6,18,9,11] [401836,434230,467374,500144,565656,598450,926132,958655,991670,1024440,2531426,4694348,4759994,5153043,7266688,7332245,9363611,9429173]) (e1 4063308 15)) (N (el 864308 [1,2,4,5,6,7,8,17] [3059795,7253225]) E)) (N (N (el 176438 [1,4,15,6,7,10,12] [698615,961664,2599876,2796597,3058818,4803676,4893487,4926582]) E) (N (e1 2052185 22) E))) (N (N (N (el 90249 [3,4,7,10,22] [2656396]) E) (N (e1 1478688 15) E)) (N (N (el 438389 [5,28,12] [9506394]) E) (N (ec 3014776 [5,9]) E)))) (N (N (N (N (el 32853 [0,1,2,3,4,5,6,7,8,12,9] [959685,3056849]) (e0 5779816)) (N (e1 1257568 3) E)) (N (N (el 307337 [8,17] [560512]) E) (N (e1 2388036 12) E))) (N (N (N (el 135239 [3,6,13,22,26] [330458,460886]) E) (N (e1 1675877 2) E)) (N (N (ec 692565 [0,1,2,3,4,15,5,6,7,10,12]) E) (N (ec 3539044 [0,1,2,4,5,6,34,9]) E))))) (N (N (N (N (N (el 16453 [0,1,2,3,4,5,6,7,10,9] [566566,697660,853310,959637,3056799,6858048,6989122,7316804,9364806,11461960]) (e0 4947992)) (N (ef 1159289 5 [364646]) E)) (N (N (el 221285 [2,4,8] [527666,559366,593204,625066,691236,822524,2656522,2788390,2919680,6982794]) E) (N (ef 2187313 9 [692578]) E))) (N (N (N (e1 106625 15) E) (N (ez 1589322 [331996,4886774,5148932]) E)) (N (N (el 544858 [1,3,4,15,6,7,12,22] [5024867,5156632]) E) (N (ec 3101032 [2,9]) E)))) (N (N (N (N (el 61495 [0,1,2,3,4,5,6,7,17,9] [591874,608260,697628,731142,985096,1001482,1058828,1091510,1124366,1157136,2795538,3188756,3254294,9479273]) (e1 7450912 15)) (N (e0 1355880) E)) (N (N (e1 381053 15) E) (N (el 2749253 [3,4,6,7,10] [2929012]) E))) (N (N (N (ec 144471 [3,23,22]) E) (N (ez 1917764 [3084592]) E)) (N (N (el 766056 [0,1,2,3,4,15,6,7,28,12,13,22] [2928527,3059722,9219199,9350943]) E) (N (e0 3907657) E)))))) (N (N (N (N (N (N (el 4677 [0,1,2,3,4,5,6,7,8,17] [566360,582756,599142,959059,975976,992362,1041516,2466484,3056750,4776452,4809266,5137170,5170038,5202884,5235672,7250996,7267400,7283794,7332950,9364592,9430130]) (e1 4345904 13)) (N (e1 1032516 22) E)) (N (N (el 192885 [3,4,6,7,10,16,8,22] [2657412,9088030]) E) (N (ez 2134617 [954698]) E))) (N (N (N (el 98424 [0,1,2,3,4,6,7,9,11] [3025166,3057936,3090706,3123476,7252246,9349400]) E) (N (el 1552402 [2,4,15,5,6,10,12] [561380,692454,954600]) E)) (N (N (el 471163 [4,15,7] [2395829,2461424,4624071]) E) (N (e0 3051593) E)))) (N (N (N (N (el 45911 [0,1,2,3,4,15,5,6,7,10,17] [427806,444198,460584,2524960,4622113,7112482,7178026,7243556,7374629]) (e1 6602836 22)) (N (e1 1311016 22) E)) (N (N (el 340280 [0,1,2,3,4,15,5,6,7,8,12,9,22] [2551242,2682318,6876626]) E) (N (e0 2581863) E))) (N (N (N (el 139384 [0,1,2,3,4,15,6,7,12,13] [2926914,2959838,3058202,3091008,7121754,7154524,9218910,9349984]) E) (N (e1 1770613 0) E)) (N (N (e1 729205 9) E) (N (ec 3776888 [3,4]) E))))) (N (N (N (N (N (el 21591 [0,1,2,3,4,5,6,7,10,8,19,12,9,11] [427242,460346,1090809,1123900,2590122,2786852,3187991,4621886,5285440,7275990,7381837,11576461]) (e0 5415781)) (N (e1 1200217 22) E)) (N (N (el 266314 [3,4,15,6,7,12,9,22] [2796890,4893793,7114070]) E) (N (e1 2310264 2) E))) (N (N (N (el 123269 [6,11] [330300,854590,1116736]) E) (N (ec 1634901 [2,6]) E)) (N (N (ec 635017 [15,21,14,9]) E) (N (e0 3321930) E)))) (N (N (N (N (el 78197 [3,4,15,6,7,10,16,8,22] [2525254]) (e0 8077340)) (N (e1 1397024 15) E)) (N (N (el 406647 [0,6,9] [560630,593550,1117797,2788346,5016611]) E) (N (ez 2842696 [6885765]) E))) (N (N (N (el 159865 [1,2,4,5,6,7,12,9,11] [174967,2673668]) E) (N (ec 1990741 [2,6]) E)) (N (N (el 802871 [4,6,10,12,22] [725040]) E) (N (ec 3936885 [0,13]) E)))))))) (N (N (N (N (N (N (N (N (el 75 [0,1,2,3,4,5,6,7,8,12,9] [426270,696608,827682,958756,1024294,3055912,11460725]) (e1 4042792 2)) (N (e1 852109 15) E)) (N (N (el 176199 [3,4,10,8,26] [330828]) E) (N (ec 2040949 [6,22]) E))) (N (N (N (el 86137 [0,1,2,3,4,15,6,7,10,8,22,11] [698484]) E) (N (ef 1462372 5 [5050564]) E)) (N (N (el 430469 [1,2,5,12,9] [2788483,9506380]) E) (N (e1 2998344 1) E)))) (N (N (N (N (el 29253 [0,1,2,3,4,5,6,7,10,8,19,20,12,11] [730804,2795190,2926264,4925064]) (e0 5656936)) (N (el 1245557 [6,11] [856204,987278]) E)) (N (N (ef 291927 3 [4754567,9211256]) E) (N (ef 2355573 38 [528748]) E))) (N (N (N (el 131945 [2,4,5,6,7,8] [297654,559800,2394750,5016154,5147276,5278394,9079468]) E) (N (e1 1663065 22) E)) (N (N (el 671834 [0,1,2,3,4,15,5,7,22] [2797378,3059530,9088844]) E) (N (ec 3428456 [0,2,6,9]) E))))) (N (N (N (N (N (el 12869 [0,1,2,3,4,5,6,7,10,23,8] [958945,3056737,4760028,4891892,7251212,9364754,11461908]) (e1 4821112 9)) (N (e1 1130820 22) E)) (N (N (el 213064 [0,1,3,4,5,6,7,24,9] [9350430]) E) (N (ez 2171989 [2396496]) E))) (N (N (N (e1 102525 15) E) (N (e1 1565813 0) E)) (N (N (el 528489 [0,1,2,3,4,5,6,28,12,13] [2534930]) E) (N (ef 3084356 10 [463286,856504]) E)))) (N (N (N (N (el 53548 [0,1,2,3,4,15,5,6,7,10,12,9] [4777970]) (e0 7385720)) (N (e1 1335381 22) E)) (N (N (e1 376961 15) E) (N (e0 2719832) E))) (N (N (N (el 143653 [4,15,6,7,8,9,22] [461512,609166,4893574,4925844]) E) (N (e0 1871960) E)) (N (N (el 758117 [0,1,2,4,6,28,20,12] [864242,995316]) E) (N (e0 3850325) E)))))) (N (N (N (N (N (N (el 4423 [0,1,2,3,4,5,6,7,8,9] [984048,1090367,1156082,3187700,3253238,4686484,4694706,5284856,7349242,7381828,7414682,7447548,9479166]) (e1 4239428 15)) (N (e0 1007940) E)) (N (N (el 184663 [2,4,15] [428919,527564,592279,690425,2526406,2788407,4623333,4885710]) E) (N (e0 2126169) E))) (N (N (N (el 94335 [15,5] [166106,428266,559340,690414,1083632,2427110,3213484]) E) (N (e0 1532468) E)) (N (N (el 466997 [15,5,10,9,22] [593624,986842,3214998]) E) (N (e0 3039321) E)))) (N (N (N (N (el 45108 [0,1,2,3,4,15,5,7,10,12,9] [583452]) (e0 6574420)) (N (el 1286468 [5,9] [2363546,2494614]) E)) (N (N (el 336765 [0,3,15,5,7] [699825,961980]) E) (N (ec 2482260 [0,2,4,34,9]) E))) (N (N (N (el 139336 [1,4,6,7,22] [699194,961340,2427592,2444088,4893502,6990656]) E) (N (e1 1754229 0) E)) (N (N (el 725353 [2,6,17,22,26] [2788423,5181302]) E) (N (ec 3760464 [3,26]) E))))) (N (N (N (N (N (el 20607 [0,1,2,3,4,15,5,7,10,12,9] [164731,427520,558594,697860,960006,2794908,3212766,6988770]) (e0 5341284)) (N (ef 1196120 2 [2429048]) E)) (N (N (ec 237652 [0,1,4,15,5,6,7,10,12]) E) (N (e0 2265145) E))) (N (N (N (el 115085 [0,15,5,9] [2460168,5179904]) E) (N (el 1618282 [4,12] [2691344]) E)) (N (N (ec 614757 [0,1,3,4,5,6,10,8,14,22]) E) (N (e0 3305576) E)))) (N (N (N (N (el 77850 [3,4,6,10,16,8,22,11] [567356]) (e0 7844200)) (N (e0 1392740) E)) (N (N (el 402247 [1,2,3,4,6,7,10,16,8,9,11] [961891,3059292,5156219]) E) (N (e0 2814037) E))) (N (N (N (e1 155781 9) E) (N (e1 1978400 18) E)) (N (N (el 786521 [0,7,10,18,9] [692260,4885684,9244628]) E) (N (e1 3928113 22) E))))))) (N (N (N (N (N (N (N (el 4167 [0,1,2,3,4,5,6,7,17,9] [344668,696810,729694,983648,1000034,1057380,1090150,1122920,1155690,2425398,2441820,2793970,2826786,3154540,3187310,3220080,3252850,5284468,7381622,7414392,9085562,9478780]) (e0 4128856)) (N (ec 897109 [0,1,2,3,4,5,6,10,8,18,9,22]) E)) (N (N (el 176505 [0,1,4,15,5,6,7,10,14,22] [502948,822438,4934756]) E) (N (ec 2065525 [6,7]) E))) (N (N (N (el 91013 [3,4,7,10,22] [2459788,2590864,2689180]) E) (N (ef 1495328 9 [823504]) E)) (N (N (el 454708 [0,1,2,3,4,15,5,6,10,22] [470706,478900,724662,741048,986810,1003196]) E) (N (el 3022965 [6,11] [856476,987550]) E)))) (N (N (N (N (e1 36977 15) (e1 6095224 9)) (N (e0 1261908) E)) (N (N (el 323703 [3,15,6,10,13,22] [724368,2428298]) E) (N (e0 2416729) E))) (N (N (N (el 135272 [0,1,2,3,4,15,5,6,7,10,8,12,13] [4909848,5040922]) E) (N (e1 1696085 22) E)) (N (N (el 725074 [3,4,6,12,13,22,26] [364378,2821968]) E) (N (ef 3666036 15 [2396628,4624841]) E))))) (N (N (N (N (N (el 17223 [0,1,2,3,4,5,6,7,10,17] [427302,443776,460162,1090139,1123716,2524470,5284979,7382374,9479540,11642238]) (e1 5099848 22)) (N (e0 1187868) E)) (N (N (el 229437 [2,4,15,7] [2526056,6851740,6982938]) E) (N (e1 2203737 22) E))) (N (N (N (el 107060 [1,2,4,5,7,9] [870886,2664878,2697350,3058108,3090890,6859240,7252458]) E) (N (e1 1602132 7) E)) (N (N (ec 548985 [1,2,15,27,12,22]) E) (N (e1 3240004 2) E)))) (N (N (N (N (e1 65597 7) (e0 7594312)) (N (e1 1380440 22) E)) (N (N (ec 389224 [0,1,2,3,4,5,6,7,8,27,12,9]) E) (N (ez 2760805 [7278970]) E))) (N (N (N (el 147758 [4,15,7] [166470,297628,428976,560050]) E) (N (e1 1933364 7) E)) (N (N (e1 774277 9) E) (N (ez 3907929 [5050862]) E)))))) (N (N (N (N (N (N (el 5247 [0,1,2,3,4,15,5,6,7,10] [427178,435372,492718,500912,558258,566452,623798,689336,1082554,4621120,4629358,4752426,4760646,4883590]) (e0 4546596)) (N (ec 1077544 [15,22]) E)) (N (N (ef 197751 2 [428283,494842,5016710]) E) (N (e1 2142312 4) E))) (N (N (N (el 98697 [2,5] [362824,460960,5310738]) E) (N (ec 1552949 [4,15,7,22]) E)) (N (N (el 479335 [1,8,12,29,22] [3084032]) E) (N (e0 3063881) E)))) (N (N (N (N (el 49225 [0,1,2,3,4,15,5,6,7,10,8,13,22,11] [181502,567170,583556,599896,698243,714629,730969,2664326,2795399,2926472,3057545,9103242]) (e0 6955380)) (N (ez 1323300 [200864,2396318]) E)) (N (N (el 344901 [3,4,15,6,7,10,16,9,22] [6990989]) E) (N (e1 2625596 26) E))) (N (N (N (el 140133 [2,6,12] [2460502,2657124,4918080,4983658,5049162,5180250]) E) (N (e0 1822809) E)) (N (N (el 741405 [0,1,2,3,4,15,7,10,8,13,22,11] [2666330,2797403,4762700,6990925]) E) (N (e0 3789144) E))))) (N (N (N (N (N (el 25975 [0,1,2,3,4,15,5,6,7,8,28,12] [427630,460408,2524794,4638324]) (e0 5456708)) (N (e1 1212548 9) E)) (N (N (el 275831 [5,20,13] [7408992]) E) (N (e1 2318428 7) E))) (N (N (N (e1 131140 7) E) (N (el 1651029 [5,6,23] [856344,987418]) E)) (N (N (e1 655412 12) E) (N (ez 3342636 [168398]) E)))) (N (N (N (N (el 82057 [3,4,15,10,16,8] [2394198,2656344,2787418]) (e0 8204645)) (N (e1 1421600 15) E)) (N (N (el 413785 [4,15,5] [592894,2394320,2657280,5312128]) E) (N (e1 2920520 2) E))) (N (N (N (el 163960 [0,1,2,3,4,6,7,8,33,9] [3058730,7220268,7252790,7285654,7318574,9350192]) E) (N (ez 2003268 [4755764]) E)) (N (N (ec 811113 [0,1,2,3,4,5,6,7,8,12]) E) (N (ec 3960920 [10,12]) E))))))))) (N (N (N (N (N (N (N (N (N (el 43 [0,1,2,3,4,5,6,7,10,9] [434334,565408,696482,827556,958630,3055784,4628650,4890796,5218478,6873264,7266482,9101492,9363565,11460790]) (ec 3989592 [3,22])) (N (el 852088 [0,1,2,3,4,5,6,7,17,9,11] [3059778,3125316,9350369]) E)) (N (N (e1 172941 15) E) (N (e1 2035780 2) E))) (N (N (N (el 86085 [0,1,2,3,4,5,6,10,8,22,11] [960616,993386,3057772,5220462]) E) (N (e0 1458472) E)) (N (N (e1 430209 15) E) (N (e0 2953337) E)))) (N (N (N (N (el 29031 [0,1,2,3,4,5,6,7,8,14,12,9,31] [3188378,7382676,7448220,9479838]) (e0 5546597)) (N (e0 1232956) E)) (N (N (el 290903 [3,5,9,22,11] [6983031]) E) (N (e1 2347072 7) E))) (N (N (N (el 131636 [1,4,15,6,7,10,22] [215710,608928,2468432,2656852,2787950,2796164,3050130,3058338,6990500,7252646]) E) (N (e1 1659000 12) E)) (N (N (ef 663679 15 [167597,429884,2428730]) E) (N (ec 3412074 [1,3]) E))))) (N (N (N (N (N (el 12373 [0,1,2,3,4,5,6,7,10,8,19,12,11] [730354,6989044,7120118]) (e0 4747364)) (N (ec 1110316 [3,22]) E)) (N (N (el 205175 [0,4,15,6,12] [527644,593172,2788482]) E) (N (e0 2170941) E))) (N (N (N (el 102517 [0,1,2,3,4,5,6,12] [207131,215410,657780,674166,698744,723322,731516,739710,854400,870786,4630916]) E) (N (el 1565252 [4,15,6,12] [5025998,5058774,6992128,7024898]) E)) (N (N (ec 504661 [1,2,3,4,5,6,7,23,8,12,29]) E) (N (el 3076132 [2,15,10,9] [741810]) E)))) (N (N (N (N (el 53301 [0,1,2,3,4,15,5,6,7,10,8,9] [435066,452576,698338,714724,731110,747496,2532867,2795498,7005269]) (e0 7316088)) (N (e0 1331304) E)) (N (N (el 364664 [0,2,3,4,15,7,10,12,13] [7122356,7253440]) E) (N (e0 2712116) E))) (N (N (N (e1 143477 9) E) (N (ec 1839673 [15,9]) E)) (N (N (el 754021 [0,1,2,3,4,15,6,7,10,8,20,12,22,11] [5025761]) E) (N (e1 3817849 9) E)))))) (N (N (N (N (N (N (el 4219 [0,1,2,3,4,15,6,7] [304036,312142,697254,729632,828328,860836,1090474,1123244,2392854,2401048,2409294,2458542,2474928,2793976,2826792,2925168,2957996,3187406,3220194,4621234,4629428,4637622,4662200,4752314,4768700,7119806,7152576,9085890,9216964,9479110]) (e0 4223272)) (N (e1 987477 22) E)) (N (N (el 181349 [2,7,8] [265410,363348,2657435,5049532]) E) (N (e1 2122325 22) E))) (N (N (N (el 94327 [15,5,6] [461004,592078,723152,788690,854228,985302,1116376,2361524,2427064,3213480]) E) (N (ef 1527893 5 [987354]) E)) (N (N (e1 462908 12) E) (N (e0 3035257) E)))) (N (N (N (N (el 41077 [0,1,2,3,4,15,5,6,7,10,8,22] [566863,583434,599820,722702,739088,960245,976658,993044,2680405,3073785,6858518]) (e0 6484308)) (N (ez 1277996 [299110]) E)) (N (N (el 329079 [3,5,20,9,13] [855478,2919852,7409064]) E) (N (e1 2433132 3) E))) (N (N (N (el 136005 [3,4,6,7,10,8,12,13,22] [4672210,6990642]) E) (N (ec 1753670 [15,6]) E)) (N (N (el 725336 [0,1,2,4,6,16,12,22] [2698128,2707288,2797418,2830190,2953072,2969468,3059590,3092360,9088089,9121115]) E) (N (ec 3699525 [0,2,4,5,7]) E))))) (N (N (N (N (N (e1 20593 15) (e0 5234792)) (N (e1 1192040 12) E)) (N (N (ec 237628 [0,1,2,3,4,15,5,6,10,9]) E) (N (ez 2249557 [2527588]) E))) (N (N (N (el 114825 [0,4,15,18,14,9] [2394630,2427400,2656778,2787852]) E) (N (e1 1618232 6) E)) (N (N (el 606311 [2,5,8,9,22] [593702,9211684]) E) (N (e1 3289156 1) E)))) (N (N (N (N (e1 73777 7) (e0 7794772)) (N (ez 1384788 [6852796]) E)) (N (N (el 401519 [0,1,2,3,4,15,5,10,9] [699968,962114]) E) (N (ec 2801720 [3,22]) E))) (N (N (N (el 155700 [1,4,15,6,7,10,22] [609234,699348,732118,2444208,4893656,6990810,7252956]) E) (N (ez 1954645 [2592956]) E)) (N (N (e1 786480 18) E) (N (e1 3924017 22) E))))))) (N (N (N (N (N (N (N (el 4151 [0,1,2,3,4,6,7,10,16,8,11] [344552,696810,729580,1090030,1122800,2425296,2441704,2793970,2826740,3187190,3219960,4891130,5153276,5284350,6988288,7381506,9085444,9478662]) (e1 4112500 22)) (N (e1 864397 15) E)) (N (N (el 176471 [2,4,15,7] [527512,592277,690423,2788405,4688703,4885658]) E) (N (ef 2060388 6 [2658616]) E))) (N (N (N (el 90505 [3,4,15,10,22] [2394248,2656400,2787474]) E) (N (ec 1486936 [0,2,4,9]) E)) (N (N (ec 443767 [3,22]) E) (N (e0 3018873) E)))) (N (N (N (N (el 33141 [0,1,2,3,4,15,5,6,7,10,8,28,12,9,22] [739014,845512,2925617,4753092]) (e0 5824632)) (N (e1 1261632 15) E)) (N (N (el 323655 [2,5,9] [2428290]) E) (N (e1 2396244 9) E))) (N (N (N (ec 135243 [3,4,6,13,22]) E) (N (el 1683560 [0,3,6] [3084582]) E)) (N (N (e1 720952 17) E) (N (e0 3608712) E))))) (N (N (N (N (N (el 16757 [0,1,2,3,4,15,5,6,7,10,9,13,22] [476520,583018,714092,2557294,2794533,4760890,6858096,7120242,9102708]) (e1 4989528 22)) (N (el 1180021 [6,11] [331882,856172,987246]) E)) (N (N (e1 225356 7) E) (N (e1 2203681 22) E))) (N (N (N (el 106881 [2,4,15,5,6] [362779,428386,690638,821712,887250,952788,1083862,2394552]) E) (N (e1 1593988 9) E)) (N (N (ec 544891 [0,1,7,12,9]) E) (N (ec 3186756 [5,10,9,22]) E)))) (N (N (N (N (el 61511 [0,1,2,3,4,5,6,10,23,16,8,17,32] [697628,1090845,2795538,3188755,6988900,9479269]) (e0 7553128)) (N (el 1368116 [6,12] [200868]) E)) (N (N (ec 385349 [2,3,4,5,6,10,16,8,9,22]) E) (N (ef 2749799 3 [856448,2920822]) E))) (N (N (N (el 147557 [2,4,15,5,17,9] [527258,1117084,2460058,4623046,4688798,6851488,6982562]) E) (N (e0 1929813) E)) (N (N (ec 766345 [21,22,26]) E) (N (ec 3907690 [1,4]) E)))))) (N (N (N (N (N (N (el 4967 [0,1,2,3,4,5,6,7,10,8,24,9,25] [590992,2523614,2531836,2786398,3253394,7381836,7414690,9479226,11576460]) (e0 4534324)) (N (ec 1065077 [5,22,11]) E)) (N (N (el 196727 [2,6,17,12] [527576,593114,658652,724190,986336]) E) (N (e1 2135157 9) E))) (N (N (N (el 98441 [2,4,15,17,9] [526632,2394410,2427180,2656558,2787632]) E) (N (ez 1552454 [266468,6852848]) E)) (N (N (ec 479305 [0,1,2,3,4,15,5,6,7,8,22]) E) (N (ef 3055685 10 [856488]) E)))) (N (N (N (N (e1 49216 3) (e1 6791268 12)) (N (e0 1323108) E)) (N (N (el 344122 [3,15,7,10,12,9,22] [568794,4893783,6860190]) E) (N (e0 2614087) E))) (N (N (N (el 139838 [4,15,6,10,12,22] [4918086]) E) (N (ec 1798204 [2,12,22]) E)) (N (N (e1 733317 9) E) (N (el 3781216 [5,6,13,11] [233952]) E))))) (N (N (N (N (N (ec 24661 [0,1,2,3,4,5,6,7,8,12]) (e0 5439604)) (N (e1 1204788 5) E)) (N (N (ec 270388 [0,1,2,3,4,15,5,6,7,10]) E) (N (e0 2318388) E))) (N (N (N (el 124037 [0,6,7,9] [2492986]) E) (N (e0 1642855) E)) (N (N (ec 643429 [0,1,2,3,4,5,6,7,10,8,24,14,19,9,25,22]) E) (N (e1 3330180 9) E)))) (N (N (N (N (ec 81962 [3,16,8]) (e0 8110184)) (N (ez 1409861 [2592960]) E)) (N (N (el 413752 [2,5,7,9,11] [446106,568988,601086,4639315]) E) (N (e0 2891844) E))) (N (N (N (el 160581 [1,2,3,4,5,6,7,16,9,11] [961564,2526220,2730132,3058718,5155633,6924776,7253018]) E) (N (e1 1991513 6) E)) (N (N (el 802907 [2,7] [2396210,4624436]) E) (N (e1 3952708 22) E)))))))) (N (N (N (N (N (N (N (N (el 103 [0,1,2,3,4,15,5,6,7,10,8] [434242,450914,467300,483686,524648,541034,565388,581996,590190,598384,606578,614772,696387,713059,729445,745831,827650,844150,860536,876922,958723,975223,991609,1007995,2531414,2547800,2564226,2662542,2695336,2810068,2924810,2941196,2957608,3072310,4645077,4759695,4792489,4890711,4907097,4923523,5038391,5153035,5169421,5185833,6873468,7004542,7266688,9101693,9232770,9363843,11329921,13558148]) (e1 4051012 2)) (N (el 856085 [0,1,2,3,4,5,6,8,9] [479318,929880,960730,993456,1028186,7253219]) E)) (N (N (el 176217 [1,2,4,5,6,7,17,22] [183001,404596,2403135,4770934]) E) (N (e1 2044230 6) E))) (N (N (N (el 87159 [2,3,10,22] [428136,460928,2525292,4622450,4884604,5015678]) E) (N (ef 1466472 5 [5050568]) E)) (N (N (el 434282 [2,3,15,5,9,22] [6982749,9506388]) E) (N (el 2998920 [6,11] [233874,2953614,3084688]) E)))) (N (N (N (N (el 29783 [0,1,2,3,4,5,6,7,10,23,8,12,13] [493182,2524404,2786998]) (e1 5734504 12)) (N (ec 1246325 [6,9]) E)) (N (N (ec 300663 [0,8,20,13]) E) (N (e1 2363480 6) E))) (N (N (N (el 135195 [6,10,12,22] [2820820]) E) (N (ef 1671767 5 [987428]) E)) (N (N (ec 679992 [0,1,2,3,4,5,6,7,8,18]) E) (N (e1 3474037 12) E))))) (N (N (N (N (N (el 13175 [0,1,2,3,4,15,6,7,10,8,12,13,11] [426456,827993,984354,2523620,5022701,7120110,7382264,11314450,11576598]) (e0 4878660)) (N (e0 1138756) E)) (N (N (el 221244 [0,1,2,3,4,15,6,8,11] [699694,731562]) E) (N (ef 2179136 12 [561285,692576,2658627]) E))) (N (N (N (el 103039 [4,15,7] [428452,4688278]) E) (N (ez 1581130 [2429194,4886770]) E)) (N (N (el 532773 [1,15,6,7,8,12,9,29] [741142]) E) (N (ec 3092580 [0,15]) E)))) (N (N (N (N (el 57445 [0,1,2,3,4,5,6,10,16,8,24,18,9] [993278]) (e0 7430248)) (N (ec 1335861 [5,7]) E)) (N (N (el 377208 [1,2,3,4,6,17,33,9,11] [2706926,3026428,3059190,3091962,3124734,9350415]) E) (N (e0 2732153) E))) (N (N (N (ec 143735 [0,9]) E) (N (e1 1913668 22) E)) (N (N (el 758903 [0,3,9] [528384,593922,2788456]) E) (N (e1 3891573 9) E)))))) (N (N (N (N (N (N (el 4471 [0,1,2,3,4,15,6,7,8,9,22] [590672,721980,738366,828223,861248,2925556,3187716,4588610,4596490,4686736,4694964,4703122,4768836,5022761,5055558,7119444,7152278,9217096]) (e1 4243569 15)) (N (e0 1016132) E)) (N (N (ec 192581 [1,2,3,4,5,6,7,23,16,8,17,22]) E) (N (e1 2134357 4) E))) (N (N (N (el 95351 [5,10,11] [428224,493792]) E) (N (e1 1545045 2) E)) (N (N (e1 471153 15) E) (N (ef 3043413 6 [987556]) E)))) (N (N (N (N (e1 45132 3) (e1 6594593 22)) (N (e0 1294380) E)) (N (N (el 340039 [3,4,6,13,22] [462280,2821574,7015882]) E) (N (ec 2539607 [5,8,9,22]) E))) (N (N (N (el 139352 [0,1,2,3,4,15,6,7,22] [183108,2435796,2795840,2828764,3058200,3091006,4705094,4770632,6990666,7023436,9087822,9349968]) E) (N (e0 1765716) E)) (N (N (el 729161 [0,1,2,3,4,15,6,7,10,8,22,11] [700304]) E) (N (ec 3760728 [4,12,22]) E))))) (N (N (N (N (N (el 21061 [0,1,2,3,4,5,6,7,10,23,8,9,11] [958949,2663970,2795044,3122551,5153609,6857700,9365030,11462184]) (e1 5382232 22)) (N (e1 1196168 9) E)) (N (N (el 246117 [0,1,2,3,4,15,5,6,7,10,8,12,9,22] [609622,716120,2796703]) E) (N (e1 2310208 7) E))) (N (N (N (e1 118909 15) E) (N (e1 1626709 12) E)) (N (N (ec 627063 [1,12]) E) (N (e1 3309640 1) E)))) (N (N (N (N (el 77941 [0,1,2,3,4,6,10,8,13,22,11] [329794,731204]) (e1 7991364 9)) (N (e1 1396776 2) E)) (N (N (el 402791 [1,2,3,4,15,6,7,9] [437808,470638,568902,601712,961893,994930,2666062,3059308]) E) (N (e1 2830396 22) E))) (N (N (N (ef 156773 2 [297952,2395116,2657266,4885466,6884268]) E) (N (ez 1983061 [2658610]) E)) (N (N (el 794681 [12,9,13] [954408,3084294]) E) (N (e0 3932217) E))))))) (N (N (N (N (N (N (N (el 4199 [0,1,2,3,4,5,6,7,18,14,9,11] [852676,1057478,1123016,3154634,3187404,3220174,3252944,7381714,9478868]) (e1 4169784 2)) (N (ec 909925 [0,1,2,3,4,5,6,7,10,8,24,14,19,20]) E)) (N (N (el 177239 [4,10,22] [559177,2722956,4623155,4754582]) E) (N (el 2080832 [2,5,9] [692548,2527554]) E))) (N (N (N (el 94279 [3,5,11,32] [460878,2427044]) E) (N (ez 1503364 [2789590]) E)) (N (N (el 454740 [0,2,4,15,5,6,7,10] [544452,609990,7294610]) E) (N (e0 3027033) E)))) (N (N (N (N (el 37247 [0,1,2,3,4,15,5,7,10,14,12,9] [698082,1091300]) (e0 6320212)) (N (e1 1269868 3) E)) (N (N (el 323957 [1,3,4,15,6,7,10,12,9,13] [593308,698635,2469268,2796583]) E) (N (e1 2429013 22) E))) (N (N (N (e1 135289 9) E) (N (e0 1732936) E)) (N (N (el 725097 [2,4] [723348,2394883,2788461,4984684,5050222]) E) (N (e0 3670152) E))))) (N (N (N (N (N (el 20535 [0,1,2,3,4,5,6,7,17,9,11] [590484,607630,1058192,1090962,1123732,1156502,3081624,3188122,3253660,9479291]) (e1 5111908 12)) (N (ef 1191962 2 [2429044,2560118,2691192]) E)) (N (N (ec 229460 [1,2,4,15,5,6,7,10,12]) E) (N (ec 2220086 [6,12]) E))) (N (N (N (el 107401 [2,7,12] [559602,9079278]) E) (N (ez 1605700 [2396396,4886754,5148942]) E)) (N (N (ec 557413 [0,1,2,3,4,5,6,7,8,24,19,12]) E) (N (el 3244122 [3,5] [3084736]) E)))) (N (N (N (N (e1 65661 15) (e0 7635048)) (N (ez 1380640 [233646,299166]) E)) (N (N (el 393349 [5,6,28,9,11] [593424,724498,855572,986646,5312024]) E) (N (e1 2777461 3) E))) (N (N (N (el 148025 [4,15] [166480,428614,560050]) E) (N (e0 1937482) E)) (N (N (e1 782392 17) E) (N (e1 3911797 9) E)))))) (N (N (N (N (N (N (el 8276 [0,1,2,3,4,5,7,8,12,9] [615638,2925784,9233595]) (e0 4571464)) (N (ec 1085508 [15,6,12]) E)) (N (N (el 204873 [1,3,4,6,7,10,8,12,22,11] [699654,9088032]) E) (N (e1 2154568 34) E))) (N (N (N (el 99209 [5,9] [362840]) E) (N (e1 1556556 7) E)) (N (N (e1 491576 28) E) (N (ec 3072040 [5,34]) E)))) (N (N (N (N (el 49257 [0,1,2,3,4,15,5,6,7,10,8,12,13] [829354,960428,5039642,5170912]) (ez 7151701 [856572])) (N (e1 1327189 22) E)) (N (N (el 352312 [0,1,2,4,5,6,7,10,19,20] [2665956]) E) (N (e0 2642759) E))) (N (N (N (el 140421 [0,6,12,9,11] [5049168,5311328,6818458]) E) (N (e0 1826905) E)) (N (N (el 749655 [0,1,2,3,4,15,6,7,28,12] [864188,995262,2928563,2961339,3059648,3092418]) E) (N (ef 3789173 13 [856552]) E))))) (N (N (N (N (N (ec 28763 [0,1,2,3,4,5,6,7,12,29,13]) (e0 5469029)) (N (ec 1216825 [15,5]) E)) (N (N (el 283767 [6,9,25] [1117540]) E) (N (e1 2323033 22) E))) (N (N (N (el 131173 [2,4,15] [362779,559734,625272,690810,2394290,2460002,2656892,2722430,2787968,4622978,6851204,6982278]) E) (N (el 1651061 [5,6,25] [856348,987422]) E)) (N (N (el 659525 [0,15,10,9] [986922]) E) (N (el 3354984 [6,16] [2953680]) E)))) (N (N (N (N (el 82313 [3,4,10,22] [2656352,2787426]) (e0 8527908)) (N (e1 1433888 15) E)) (N (N (el 417861 [0,1,2,3,4,15,5,6,7,17,9,11] [305370,2404002]) E) (N (e0 2924840) E))) (N (N (N (el 164485 [2,4,5,7,9] [527416,625048,2526260,2559030,2657070,2690106,2788377]) E) (N (ez 2024053 [2789686]) E)) (N (N (el 823385 [4,15,7,17] [559280,692282,4755510,4885712]) E) (N (e1 3973237 9) E)))))))))) (N (N (N (N (N (N (N (N (N (N (el 27 [0,1,2,3,4,5,6,7,8,9] [565366,688248,827514,958588,1024126,2662528,3055746,9363569,9429124]) (e1 3985472 22)) (N (el 852042 [2,5,17,9] [3084350]) E)) (N (N (ec 172421 [0,4,14,9]) E) (N (e1 2031942 6) E))) (N (N (N (el 83029 [2,16,8] [2459730]) E) (N (ec 1451125 [6,9]) E)) (N (N (el 426069 [4,5] [297178,560136,2394350,2657290,5312138]) E) (N (e1 2940996 4) E)))) (N (N (N (N (el 28793 [0,1,2,3,4,15,5,6,7,10,8,12,13,31] [861377,992918,2401944,5039628]) (e0 5541962)) (N (ec 1224772 [4,5]) E)) (N (N (el 290874 [3,15,7,10,8,13,22,11] [699762,4893803]) E) (N (e1 2334781 22) E))) (N (N (N (el 131364 [4,15,6,10,12,22] [199316,215702,608920,2787946,2796162,7252634]) E) (N (e1 1658976 3) E)) (N (N (el 663675 [4,15,7] [2395855,2461498,4624097]) E) (N (ec 3399784 [1,2,4,15,7]) E))))) (N (N (N (N (N (el 9343 [0,1,2,3,4,15,5,6,7,10,12,9] [427240,558303,4621534,4752614]) (e1 4698672 15)) (N (e1 1102676 11) E)) (N (N (e1 204921 9) E) (N (ec 2167108 [3,7,10,16,22]) E))) (N (N (N (e1 102513 15) E) (N (ef 1557316 4 [4755710]) E)) (N (N (el 503927 [1,15,12,29,13] [986890]) E) (N (ef 3072106 3 [2560430]) E)))) (N (N (N (N (el 50807 [0,1,2,3,4,15,5,6,7,21,12,9,13] [395218,403412,460758,468952,7276416,7292826]) (e0 7270428)) (N (ef 1327669 5 [4919464]) E)) (N (N (el 360585 [3,4,7,17] [560616,822762,4754840]) E) (N (e0 2699385) E))) (N (N (N (el 143447 [2,5] [1117066,2427278,2525894]) E) (N (ec 1839397 [2,5]) E)) (N (N (ec 753735 [3,4,6,13,22]) E) (N (ec 3809880 [3,22]) E)))))) (N (N (N (N (N (N (el 4215 [0,1,2,3,4,15,6,7,12] [336620,344910,590672,607058,656212,672598,696814,721752,729946,738140,828006,861022,983904,1000290,1090404,1123174,2360068,2376454,2425622,2433816,2442062,2793974,2826790,2925166,2957994,3187404,3220192,4703080,4768618,5022572,5055342,7119728,7152498,9085812,9216886,9479032]) (ef 4211069 9 [299512])) (N (e0 966745) E)) (N (N (el 180806 [4,15,6,7,10] [4918458]) E) (N (e1 2121845 9) E))) (N (N (N (el 94323 [2,15,5] [231600,428210,2394292,3213478,4622518]) E) (N (ef 1515556 10 [725208]) E)) (N (N (e1 462904 28) E) (N (e1 3035249 15) E)))) (N (N (N (N (el 41013 [0,1,2,3,4,5,6,7,8] [927484,943870,960079,976640,993026,1009412,1025798,1042184,3057239]) (e1 6406228 22)) (N (e1 1274144 15) E)) (N (N (el 328573 [2,3,15,5,7,9] [699822,830896,5180836]) E) (N (el 2429030 [1,2,4,5,12,13] [2789609,2920814,3051888]) E))) (N (N (N (el 135767 [2,5,6,8,12] [1116982,4688658,4754222,7146218,7277336]) E) (N (ec 1753110 [6,12]) E)) (N (N (el 725330 [4,6,12,13,22] [233306,364418,4919172]) E) (N (el 3698759 [4,6] [987612]) E))))) (N (N (N (N (N (el 20584 [0,1,2,3,4,6,7,8,9,11] [452034,714180,845254,910792,2548720,2811338,2942412,3007950,6874576,7136722,7202260,9102806,9233699,9299337,11331032,11396570]) (e0 5230692)) (N (e1 1192025 22) E)) (N (N (ec 237620 [0,1,2,3,4,15,5,6,10,12,9]) E) (N (e0 2248793) E))) (N (N (N (el 114792 [0,1,2,3,4,5,6,7,18,14,9,11] [3025402,3058172,3090942,3123712,7252482,9349636]) E) (N (e1 1613864 18) E)) (N (N (el 586085 [0,1,2,3,4,15,5,6,7,10,8,28,12,9,22] [610082,716580,2796711]) E) (N (ez 3260482 [299458,954820]) E)))) (N (N (N (N (el 69753 [0,1,2,3,4,15,5,6,10,8,19,12] [2925713,9233980,9365228]) (e0 7741556)) (N (ez 1384744 [168110]) E)) (N (N (el 401495 [0,1,2,3,4,5,6,27,9,11] [929326,962096,994866,1027636,3059254]) E) (N (ec 2797637 [3,4,12]) E))) (N (N (N (el 148581 [2,4,7] [265166,2460108,6917036,9079744]) E) (N (ec 1945924 [4,15,6]) E)) (N (N (e1 782441 22) E) (N (e0 3919973) E))))))) (N (N (N (N (N (N (N (el 1111 [0,1,2,3,4,5,6,21,12,9,13,11] [401864,434426,467402,500172,696768,729550,926153,958715,991691,1024461,2531604,5153045,7266692]) (e1 4091972 0)) (N (ec 864356 [0,1,2,3,4,5,6,7,8,17,12]) E)) (N (N (el 176457 [1,3,4,15,6,7,8,22,11] [502920,699530,2468950,2590842,2599068,2796684,3058830,9088144]) E) (N (e1 2060340 4) E))) (N (N (N (el 90457 [2,3] [428174,2394242]) E) (N (e1 1482784 15) E)) (N (N (ec 442709 [1,2,3,4,5,6,7,10,23,8,19,9,22,11]) E) (N (e1 3018865 15) E)))) (N (N (N (N (el 32885 [0,1,2,3,4,15,5,6,7,10,8,12,9] [828613,2925773]) (e0 5816440)) (N (e1 1257592 12) E)) (N (N (e1 315448 27) E) (N (ez 2388068 [6983992]) E))) (N (N (N (el 135241 [0,1,2,3,4,15,6,7,10,8,22,11] [699118]) E) (N (ec 1683544 [0,9]) E)) (N (N (ec 709463 [0,2,3,4,15,5,7,10,28,12]) E) (N (ec 3547223 [5,8,9,22]) E))))) (N (N (N (N (N (el 16485 [0,1,2,3,4,5,6,7,10,14,9] [6858060,7120206,7316816,9364818,13559124]) (e1 4960284 22)) (N (e1 1163560 22) E)) (N (N (el 225329 [2,4,5,6] [231707,297292,625272,690421,822598,888136,953674,1084748,2394446,2526050,2591726,4754450,4885748,6851730,6982677]) E) (N (e0 2195517) E))) (N (N (N (el 106633 [2,4,7] [362944,2394562,2427332,2656710,2787784,4622496,6851018,6982092]) E) (N (ez 1590101 [2527486,6983902,7246092]) E)) (N (N (el 544875 [1,2,7,12] [4623435]) E) (N (e0 3145801) E)))) (N (N (N (N (e1 61501 7) (e0 7520376)) (N (el 1359924 [2,6,10,12] [725162]) E)) (N (N (e1 385109 12) E) (N (el 2749293 [3,15,7] [700792,831866]) E))) (N (N (N (el 147493 [4,15,6,10,12,22] [723028]) E) (N (ec 1929237 [4,22]) E)) (N (N (e1 766089 9) E) (N (e0 3907673) E)))))) (N (N (N (N (N (N (el 4725 [0,1,2,3,4,15,5,6,7,10,8,12,13] [263286,271088,320362,451434,566362,599160,696915,713850,730236,869502,959616,976002,992388,2368268,2417514,2466746,2483132,2540576,2548804,2606158,2794471,2810873,2827398,3073160,4760036,4776454,4792854,4809268,4907644,4940476,5169876,5202664,6988778,7005182,7021570,7267338,9102474,9364620]) (e1 4460580 22)) (N (ec 1036612 [2,23,8]) E)) (N (N (ec 196679 [2,23,16,8,17,32]) E) (N (ez 2134649 [823628]) E))) (N (N (N (e1 98433 15) E) (N (ef 1552438 4 [6852842]) E)) (N (N (ef 471167 15 [167593,429810,2428656]) E) (N (e1 3051642 1) E)))) (N (N (N (N (el 49209 [0,1,2,3,4,15,5,6,7,10,8,22] [181018,567126,599896,698202,714588,730974,960352,976738,993124,2401104,2532845,4908564,5170906,6988825,7005249,7021797,7268017]) (e0 6697284)) (N (e1 1323084 7) E)) (N (N (el 340837 [1,3,4,15,6,7,10,28,19,12,9,22] [5025063,7122217]) E) (N (e0 2605192) E))) (N (N (N (e1 139397 9) E) (N (ef 1794372 2 [2494764,4788522]) E)) (N (N (e1 729209 9) E) (N (e1 3780712 22) E))))) (N (N (N (N (N (el 21887 [0,1,2,3,4,15,5,6,7,10,9] [427598,435792,493138,566868,689750,7407066,7423462]) (e1 5439556 7)) (N (e1 1200441 15) E)) (N (N (ec 266329 [2,4,5,6,7,22]) E) (N (e1 2314301 22) E))) (N (N (N (ez 123277 [297540]) E) (N (e1 1642599 0) E)) (N (N (ec 639109 [28,14,12]) E) (N (e0 3330148) E)))) (N (N (N (N (el 78709 [3,4,15,6,7,10,16,8,13,22] [2795594]) (e1 8081768 12)) (N (el 1404964 [2,6,10,12] [725182]) E)) (N (N (el 407159 [0,9] [560664,593556]) E) (N (ec 2867525 [1,2,4,6,7,19,20]) E))) (N (N (N (el 160069 [1,2,3,4,5,6,7,23,9,11] [501894,960587,2533476,2657292,3124238,5155635,9350160]) E) (N (ez 1991253 [2658612]) E)) (N (N (el 802903 [2,5,9] [2428978]) E) (N (e1 3952696 17) E)))))))) (N (N (N (N (N (N (N (N (el 91 [0,1,2,3,4,5,6,7,8] [434500,827718,958792,1024330,4628812,7266533,7332083,13558083,13623630]) (e0 4042856)) (N (el 852357 [15,5,6,7] [266314,297178,397388,461006,987203,2363469,2459855,5312578]) E)) (N (N (el 176203 [3,4,15,7,10,22] [4623466,4688982]) E) (N (ez 2043954 [561309,954688,2658457,4755775]) E))) (N (N (N (el 86645 [3,4,15,6,7,10,22,11] [2558074,2795644]) E) (N (ef 1462404 5 [2789582,5181638]) E)) (N (N (el 434265 [4,15,5,17,9] [560808,2394944,6982775,9506384]) E) (N (ef 2998376 5 [5181838]) E)))) (N (N (N (N (ec 29285 [0,1,2,3,4,5,6,7,8,21,12,13]) (e0 5705848)) (N (e0 1245565) E)) (N (N (ec 296311 [2,8,20,13]) E) (N (e1 2363464 34) E))) (N (N (N (el 132229 [0,4,5,6,9,11] [330436,5016158,5147252,5278352,6851226,9079462]) E) (N (e0 1667448) E)) (N (N (e1 671865 12) E) (N (e0 3437159) E))))) (N (N (N (N (N (el 12917 [0,1,2,3,4,15,5,6,7,10,8,13,11] [696801,2524426,4760032,9102618]) (e0 4878380)) (N (e1 1135429 22) E)) (N (N (el 221236 [0,1,2,3,4,15,6,7,8,12,22,11] [198722,215876,698630,732460,2796832,3058982]) E) (N (ef 2175300 17 [274776,373082,569692,602462,2502998,2511191,2576571,2601146,4739398,4804936]) E))) (N (N (N (el 102693 [0,2,4,5,8,9] [5155204,5187992]) E) (N (el 1581080 [4,15,6,10,12,22] [479494,5026056]) E)) (N (N (el 529015 [0,8,28,9] [7278356]) E) (N (ez 3088456 [430522]) E)))) (N (N (N (N (el 54631 [0,1,2,3,4,15,5,6,7,8,27,12] [460794]) (e0 7417960)) (N (e1 1335605 2) E)) (N (N (el 376969 [2,4,15,5] [723352,2394881,2428408,2788621,5311994]) E) (N (e0 2728500) E))) (N (N (N (el 143657 [4,15,6,7,10,9] [306066,2796436,4893576,4925846]) E) (N (e1 1876309 4) E)) (N (N (el 758121 [0,1,2,3,4,15,6,7,12] [831478,962552]) E) (N (e0 3879520) E)))))) (N (N (N (N (N (N (el 4455 [0,1,2,3,4,5,6,7,8,14,9] [3187716,7349254,7381830,7414684,7447560,9479178]) (e1 4239492 9)) (N (e0 1011768) E)) (N (N (el 188517 [2,4,17] [297847,559322,592154,625874,691168,2395142,2656516,2788564]) E) (N (ez 2126933 [2658630]) E))) (N (N (N (el 94839 [15,5,8,17,9] [395518,428250,854272,4589826,4688098,4753654]) E) (N (el 1544756 [1,4,15,6,7,10,22] [217308,6861022,7123168]) E)) (N (N (el 467013 [2,15,5,10,22] [986844,9506422]) E) (N (e1 3039338 3) E)))) (N (N (N (N (e1 45116 4) (e1 6590580 9)) (N (e1 1290272 15) E)) (N (N (el 337527 [3,14,20,9] [855490,2919866]) E) (N (e1 2494532 0) E))) (N (N (N (e1 139344 3) E) (N (e1 1765464 22) E)) (N (N (el 725385 [0,6,18,9,22,26] [5312378]) E) (N (ef 3760504 4 [4657424]) E))))) (N (N (N (N (N (el 20855 [0,1,2,3,4,15,5,7,8,9,22] [591340,697156,730644,853526,869912,960010,992794,2794484,3057168,4752417,4768837,6988372,7251484,7407052]) (e0 5353812)) (N (ef 1196136 5 [3084396]) E)) (N (N (e1 241789 15) E) (N (e0 2269524) E))) (N (N (N (el 115845 [5,6,18,14,9] [264740,2361894,2460172,2492950,5179908]) E) (N (e0 1622360) E)) (N (N (el 626757 [0,1,2,3,4,15,5,6,7,18,14,9,25] [2404043]) E) (N (e1 3305592 9) E)))) (N (N (N (N (el 77897 [0,1,2,3,4,5,6,10,16,8,22] [960574,993344]) (e0 7962916)) (N (e0 1392756) E)) (N (N (el 402287 [1,2,3,4,15,6,7,10,9] [437862,568936]) E) (N (e1 2830384 17) E))) (N (N (N (ef 156517 2 [297940,2395114,2657264,4885478,6884264]) E) (N (e1 1982549 2) E)) (N (N (e1 794673 22) E) (N (e0 3928153) E))))))) (N (N (N (N (N (N (N (el 4171 [0,1,2,3,4,5,6,7] [311900,696990,729628,1057440,1090210,1122980,1155750,2392630,2409052,2793972,2826788,3154600,3187370,3220140,3252910,4620976,4629170,4752052,7381686,7414456,9085626,9478844]) (e0 4145716)) (N (el 905337 [0,2,3,4,15,5,6,10,8,24,18,9] [2428389]) E)) (N (N (el 176981 [1,2,4,5,6,7,17] [273576,371882,436471,470188,699566,732336,2526356,2534554,2730476,4869204,4934758,6826660,6925248,6990982,7023760]) E) (N (el 2072884 [5,9] [397634,2691370]) E))) (N (N (N (el 91269 [3,6,7,10,22] [2590866]) E) (N (e0 1503332) E)) (N (N (e1 454716 9) E) (N (e1 3022973 15) E)))) (N (N (N (N (e1 36989 15) (e0 6234436)) (N (e1 1269844 7) E)) (N (N (el 323707 [4,15,7,10] [2395530,4623764,4754838]) E) (N (e0 2424904) E))) (N (N (N (e1 135285 9) E) (N (ec 1703981 [12,22]) E)) (N (N (el 725082 [3,4,6,12,22] [2821970,3084128]) E) (N (ez 3666212 [201174,2920916]) E))))) (N (N (N (N (N (el 17495 [0,1,2,3,4,5,6,7,10,27,12,13] [460170,4883834]) (e1 5111892 22)) (N (ez 1188132 [200818]) E)) (N (N (ec 229445 [4,15,7,22]) E) (N (e0 2207801) E))) (N (N (N (el 107076 [2,4,5,6,17] [3058110,3090892,7252460,7285230]) E) (N (e1 1602180 9) E)) (N (N (ec 557145 [1,2,3,4,5,6,7,8,19,20,12]) E) (N (ec 3244090 [2,22]) E)))) (N (N (N (N (e1 65649 15) (e0 7630900)) (N (ez 1380456 [6852780]) E)) (N (N (el 393290 [1,5,27,12,9] [5180942]) E) (N (ef 2764920 5 [7278974]) E))) (N (N (N (el 148021 [4,15,7] [592696]) E) (N (e1 1937466 4) E)) (N (N (e1 782385 22) E) (N (ef 3907961 0 [5181938]) E)))))) (N (N (N (N (N (N (el 5759 [0,1,2,3,4,15,5,6,7,10,9] [427204,435398,492744,500938,558284,623822,689360,951506,4752432]) (e0 4571432)) (N (ec 1081429 [5,11]) E)) (N (N (el 200825 [0,1,4,5,6,7,18,9,11] [503044,2673844]) E) (N (e1 2146353 17) E))) (N (N (N (el 98949 [2,5,17,9] [264524,395598,493728,2525510,2558282,2656592,2787666]) E) (N (ef 1553525 0 [6852852,9081080]) E)) (N (N (el 479591 [1,7,10,12] [7278334]) E) (N (ef 3067957 10 [987562]) E)))) (N (N (N (N (el 49227 [0,1,2,3,4,15,7,10,8,13,22,11] [698268,829341,2393342,2795338,2926411,4621572,4687208,4752645,4818281,6988820,9217045]) (e1 7143781 3)) (N (e1 1327184 3) E)) (N (N (ef 345175 3 [2788762,4754577,9244130]) E) (N (e1 2633784 22) E))) (N (N (N (el 140373 [3,6,12,13,22] [6884050]) E) (N (e1 1822841 9) E)) (N (N (el 749623 [0,1,2,3,4,15,6,7,12,22] [437432,568774,602016,700322,733092,855974,872360,962474,995244,2665924,2797486,2830256,3059634,3092404]) E) (N (el 3789157 [5,13] [856543,987622]) E))))) (N (N (N (N (N (el 28745 [0,1,2,3,4,5,6,7,10,8,12,29,13,11] [730750]) (e0 5460837)) (N (e1 1216546 15) E)) (N (N (ec 279381 [1,2,3,4,5,6,7,10,23,8,19,12]) E) (N (ef 2322481 2 [823656,2396462,4755798]) E))) (N (N (N (e1 131164 3) E) (N (e0 1651048) E)) (N (N (e1 659508 9) E) (N (ec 3354680 [2,22]) E)))) (N (N (N (N (el 82265 [3,23] [460894]) (e1 8511592 12)) (N (e1 1429804 22) E)) (N (N (el 413802 [3,15,5,9,22] [2690720,5312132]) E) (N (ef 2920568 5 [5181832]) E))) (N (N (N (el 164229 [2,4,5,8,9] [461820,723776,855090,2526260,5311530]) E) (N (e0 2011172) E)) (N (N (el 823350 [5,7,9] [462904]) E) (N (e1 3965049 9) E))))))))) (N (N (N (N (N (N (N (N (N (el 59 [0,1,2,3,4,5,6,7,8] [434406,696552,958698,1024236,2531410,7266527,7332078,11460848,11526386]) (ec 4026440 [1,22])) (N (e1 852097 15) E)) (N (N (el 176186 [1,4,6,7,22] [699458,961604,2796614,4697012,4893768,5155914]) E) (N (ec 2040132 [3,5,7,23,16,9,22,11]) E))) (N (N (N (ec 86089 [0,1,2,3,4,5,6,7,10,8,22]) E) (N (e0 1458516) E)) (N (N (el 430217 [1,2,5,12,29] [9506376]) E) (N (ez 2986101 [856460]) E)))) (N (N (N (N (el 29047 [0,1,2,3,4,15,6,7,8,12,9] [853676,870062,959299,992944,3057168,3188378,4589234,4687512,5153839,7284358]) (e1 5579636 9)) (N (e1 1233212 22) E)) (N (N (el 291669 [2,3,15,5,7,10,23,8,13,22] [428103,2526341]) E) (N (e1 2347096 6) E))) (N (N (N (el 131652 [4,15,6,12] [2468434,2787954,2796166,2919048,5155350,5188154,6990506,7023276]) E) (N (el 1659256 [5,37,13] [2953504,3084578]) E)) (N (N (ec 671817 [0,1,2,3,4,15,5,6,7,8,22]) E) (N (e1 3420216 22) E))))) (N (N (N (N (N (el 12405 [0,1,2,3,4,15,5,6,7,10,8,13,22,26,11] [460028,476414,565720,599296,696793,730369,9102594]) (e0 4751464)) (N (e1 1114436 22) E)) (N (N (el 205943 [6,10,8,9,22] [855326]) E) (N (e0 2171221) E))) (N (N (N (el 102521 [0,1,2,3,4,5,6,7] [174476,182642,313742,698768,731538,2533780,2566550,4630936]) E) (N (ez 1565545 [9081090]) E)) (N (N (e1 528464 3) E) (N (e0 3076213) E)))) (N (N (N (N (el 53349 [0,1,2,3,4,15,5,6,7,10,8,12,9] [862192]) (e1 7364712 22)) (N (el 1335317 [6,10,12] [725156]) E)) (N (N (el 372824 [1,3,6,7,10,28,13] [7122358,7253442]) E) (N (ec 2715722 [6,12]) E))) (N (N (N (e1 143481 9) E) (N (e0 1855608) E)) (N (N (el 757831 [3,4,6,7,12,22] [724972,987118,2624986]) E) (N (e1 3838048 3) E)))))) (N (N (N (N (N (N (el 4223 [0,1,2,3,4,15,6,7,10] [164730,172964,426952,435146,558028,828366,1090512,2425774,2442160,2925170,2957998,3187408,3220196,5022674,7119828,7152598,9216984,9479130]) (e1 4235312 7)) (N (el 995376 [6,10,13,22] [4886624]) E)) (N (N (el 184405 [1,2,4,5,6,7,8,12,9] [306039,2403301,2599410,4771018]) E) (N (e1 2125853 4) E))) (N (N (N (el 94331 [2,15,5] [460960,2394296,2459878,3213482,4622568]) E) (N (e1 1527929 9) E)) (N (N (el 462969 [3,5,28,13,22] [9506418]) E) (N (e1 3035509 1) E)))) (N (N (N (N (el 41525 [0,1,2,3,4,5,6,7,8,18,9] [460568,5154582]) (e0 6496356)) (N (e1 1286176 15) E)) (N (N (el 336709 [0,3,4,5,6,7,10,16,14,9] [3059128]) E) (N (e1 2433156 9) E))) (N (N (N (ec 136311 [0,3,6,9,25,13,22]) E) (N (e0 1753945) E)) (N (N (el 725338 [3,4,6,16,12,22] [4918158,5181298]) E) (N (e0 3703893) E))))) (N (N (N (N (N (el 20601 [0,1,2,3,4,15,5,6,7,10,8,9,11] [172923,566776,828922,2680316,2942462,4760544]) (e0 5280084)) (N (el 1196088 [2,5] [2429044]) E)) (N (N (ec 237636 [0,1,4,15,5,6,7,10,9]) E) (N (el 2261056 [4,7,12] [692582]) E))) (N (N (N (el 115077 [0,15,5,6,9,11] [854552,1116698,2361884,2460166,5179900]) E) (N (ec 1618242 [3,6,12,26]) E)) (N (N (e1 610429 15) E) (N (e0 3305529) E)))) (N (N (N (N (e1 73789 7) (e0 7803172)) (N (ez 1385300 [4755642]) E)) (N (N (el 401767 [1,2,3,4,15,7,8,9] [699190,732752,855634,872020,962118,994902,2796586,3059276]) E) (N (e0 2805845) E))) (N (N (N (el 155716 [1,4,15,6,10,12] [699360,961506,2444210,4893668,6990822,7023592]) E) (N (e0 1966148) E)) (N (N (e1 786488 18) E) (N (e1 3924029 22) E))))))) (N (N (N (N (N (N (N (el 4155 [0,1,2,3,4,6,7,10,8,11] [311784,696858,729628,1090078,1122848,2392528,2408936,2794018,2826788,3187238,3220008,4751914,5349932,6988334,7381552,9085490,9478708]) (e1 4124720 17)) (N (ec 872517 [0,1,2,3,4,5,6,10,8,17,22]) E)) (N (N (el 176501 [0,1,2,4,15,5,6,7,9,11] [404640,4803658,4934754]) E) (N (e1 2065265 15) E))) (N (N (N (el 90765 [3,15] [297044,428182,559256,690330,2394250,2656412]) E) (N (e1 1495128 22) E)) (N (N (e1 450616 12) E) (N (ef 3019125 4 [856472,2363802]) E)))) (N (N (N (N (el 36937 [0,1,2,3,4,5,6,7,10,8,14,11] [2664142,2926288,3122573,9365069,13559506]) (e0 5968180)) (N (e0 1261864) E)) (N (N (el 323659 [2,7] [2395522,4623752]) E) (N (e0 2400345) E))) (N (N (N (el 135257 [0,1,2,3,4,5,6,12] [182458,338203,699150,731920,2402591,2534162]) E) (N (e1 1683592 12) E)) (N (N (el 725066 [4,6,12,22] [2756432,2821970,3084116,4655818,4853590,4919128]) E) (N (e1 3666004 9) E))))) (N (N (N (N (N (el 16981 [0,1,2,3,4,5,6,7,10,19,20,12,9] [460152,2794874,3057020,4891970,5023054,5154148,7251314,11461779]) (e0 5088068)) (N (ez 1180029 [299120]) E)) (N (N (ec 229429 [15,12,22]) E) (N (e0 2203705) E))) (N (N (N (el 106889 [2,15] [428442,2394554,2427362]) E) (N (ez 1598297 [2527484,7115010]) E)) (N (N (el 548968 [0,1,2,3,4,15,6,7,20,12,9,22] [7155470]) E) (N (ec 3199044 [5,10,9,22]) E)))) (N (N (N (N (e1 65585 7) (e0 7581816)) (N (e1 1368380 22) E)) (N (N (el 386167 [3,6,9,13,22] [429574,986634,5016609]) E) (N (ef 2756981 3 [7278966]) E))) (N (N (N (e1 147593 9) E) (N (e0 1930069) E)) (N (N (e1 770165 9) E) (N (e1 3907705 9) E)))))) (N (N (N (N (N (N (el 4991 [0,1,2,3,4,15,6,7,8,11] [427156,435350,492696,500890,558236,689310,828576,2589202,2597420,2925710,3187858,4752420,7119450,7152284,9217006,11314290]) (e0 4538472)) (N (ec 1065333 [5,10,22]) E)) (N (N (el 196735 [2,5,17] [167138,429288,560362,625900,691438,756976,1084658]) E) (N (e0 2142296) E))) (N (N (N (el 98689 [2,4,5,6] [362802,428210,690484,821558,887096,952634,1083708,5310734]) E) (N (ec 1552678 [15,12,22]) E)) (N (N (el 479322 [0,1,2,3,4,15,5,7,22] [2797304,2928384,6990908]) E) (N (e1 3060341 3) E)))) (N (N (N (N (el 49223 [0,1,2,3,4,15,7,10,8,13,22,26,11] [329584,2426110,2795334,2926407,6988816,9217041]) (e1 6848576 7)) (N (e0 1323124) E)) (N (N (el 344151 [3,5,9,22] [593376,7015903]) E) (N (e1 2625584 17) E))) (N (N (N (el 139877 [2,15,12] [396130,494018,2525510,2657124,2788198,4918078]) E) (N (e0 1806380) E)) (N (N (el 733528 [0,1,2,3,4,15,6,7,22] [2797462,3059608,9088091]) E) (N (e0 3785312) E))))) (N (N (N (N (N (e1 24701 15) (e0 5451828)) (N (e1 1212484 2) E)) (N (N (el 274536 [0,1,2,3,4,5,6,7,10,23,8,9] [9235806,11332960]) E) (N (e1 2318412 7) E))) (N (N (N (el 131101 [4,15,7] [2394694,4622928,4754002]) E) (N (e0 1643111) E)) (N (N (ec 651401 [19,12]) E) (N (e0 3334248) E)))) (N (N (N (N (el 82009 [2,3,16,8] [2394190,2656336,2787410]) (ez 8204629 [856574])) (N (ez 1418101 [2592954]) E)) (N (N (el 413768 [2,5,7,9,22] [6859772]) E) (N (ec 2895940 [7,13]) E))) (N (N (N (el 160887 [2,4] [559179,822300,2919454]) E) (N (e0 1995092) E)) (N (N (e1 807013 12) E) (N (ec 3956824 [10,22]) E)))))))) (N (N (N (N (N (N (N (N (el 295 [0,1,2,3,4,5,6,10,16,8] [434214,565654,827800,958599,2531422,3055833,4694186,4759962,5022108,5152913,6873306,7135548,7266684,9363559,13558041]) (e1 4051052 3)) (N (el 856181 [0,1,2,3,4,15,5,6,7,17] [305370,338097,699777,733276,2404377,2437179]) E)) (N (N (el 176247 [0,4,14] [593016,724090,789628,855166]) E) (N (e1 2048117 6) E))) (N (N (N (el 90201 [3,4,7,23,22] [2656390]) E) (N (e1 1466656 15) E)) (N (N (e1 435061 12) E) (N (e1 3010929 15) E)))) (N (N (N (N (el 30327 [0,1,2,3,4,15,5,6,7,12,9,13] [394944,4753066]) (e0 5750888)) (N (e1 1257544 2) E)) (N (N (el 307254 [5,8,11] [462206]) E) (N (e1 2375744 34) E))) (N (N (N (e1 135232 3) E) (N (el 1675637 [5,38,13] [856358,987432]) E)) (N (N (ec 688199 [0,1,2,3,4,15,5,7,10,12]) E) (N (e1 3477640 1) E))))) (N (N (N (N (N (el 13687 [0,1,2,3,4,15,6,7,10,8,28,20,13] [7251184,7382266,11445524,11576600]) (e1 4886816 15)) (N (e0 1139012) E)) (N (N (el 221252 [1,3,4,15,6,7,22,11] [216246,699428,732464,2590838,2599064,2796834,3058984,9088258]) E) (N (e0 2183229) E))) (N (N (N (el 103551 [3,15] [428456,493994,2591148]) E) (N (e0 1585192) E)) (N (N (e1 541581 15) E) (N (e0 3096645) E)))) (N (N (N (N (el 57957 [0,1,2,3,4,5,6,10,16,8,24,9,22] [959733,993280,2664166,3057335,4760030,6857822,7251493]) (e0 7438440)) (N (ez 1339692 [168096]) E)) (N (N (el 377229 [4,15,5,9] [297178,428270,560644,690436,2461176]) E) (N (ec 2736200 [7,10]) E))) (N (N (N (ec 143991 [0,4,14,9]) E) (N (e1 1917064 9) E)) (N (N (el 761941 [3,4,6,12,13,22] [725000,6917594,6983027]) E) (N (e1 3903560 32) E)))))) (N (N (N (N (N (N (el 4479 [0,1,2,3,4,15,6,7,10,9] [164938,426874,435108,558028,828500,2925558,4686740,4694968,5022801,7119446,7152280,9217110]) (e1 4251737 22)) (N (e1 1019960 22) E)) (N (N (el 192837 [2,3,4,5,6,7,23,16,8,22] [2657292]) E) (N (ec 2134598 [4,15,6]) E))) (N (N (N (ec 98346 [2,5,17,9]) E) (N (ef 1545301 2 [9081054]) E)) (N (N (el 471159 [15,6,8,22] [855788,986862,2363114,2428597]) E) (N (e1 3047797 3) E)))) (N (N (N (N (ec 45157 [0,1,2,3,4,15,5,6,7,10,28,12]) (e1 6594629 22)) (N (e1 1302560 15) E)) (N (N (el 340055 [2,3,5,9,22] [2821305,7015886]) E) (N (e1 2560072 22) E))) (N (N (N (el 139354 [3,15,6,12,22] [3083090,4590232,4655822]) E) (N (e0 1770345) E)) (N (N (ec 729175 [2,22]) E) (N (el 3772757 [4,5,23] [987614]) E))))) (N (N (N (N (N (el 21367 [0,1,2,3,4,15,5,6,7,12,9] [394794,426566,435602,443795,460332,468526,493101,509487,566084,599549,828655,861613,984531,1000929,2655210,2663422,2926119,4637509,4703740,4883435,4899839,7120110,7153068,7407058,7423456,11314726]) (e0 5414938)) (N (e1 1200181 17) E)) (N (N (ec 254041 [0,1,2,3,4,15,5,6,7,8,22]) E) (N (e1 2310224 7) E))) (N (N (N (e1 123021 15) E) (N (el 1634645 [5,6,13,11] [332050]) E)) (N (N (ec 634984 [0,1,2,4,15,5,7,14,9]) E) (N (ef 3317880 5 [9376172]) E)))) (N (N (N (N (ec 78149 [2,3,4,5,6,7,10,23,16,8,22]) (e0 8003704)) (N (e0 1396840) E)) (N (N (el 405877 [1,2,3,4,9,11] [331384,347770,478844,609918,699894,732800,855682,872068,962072,994950,6990838]) E) (N (e1 2838584 22) E))) (N (N (N (el 159850 [0,1,2,4,6,7,9,11] [3058678,4696550,5155832,9350138]) E) (N (e0 1983349) E)) (N (N (el 798777 [0,1,2,3,4,15,6,7,10,9,22] [700458,4893893]) E) (N (e0 3936345) E))))))) (N (N (N (N (N (N (N (el 4203 [0,1,2,3,4,5,6,7,9,11] [1090266,1155804,3154654,3187424,3220194,3252964,7381734,9478888]) (ez 4198517 [856564])) (N (e1 950341 11) E)) (N (N (el 180312 [0,1,2,3,4,15,6,7,16,9,22] [183478,445624,2796594,4705168,4771002,6990080,7023008,9088188]) E) (N (e0 2097242) E))) (N (N (N (el 94283 [3,5,11] [2394276]) E) (N (e1 1507368 34) E)) (N (N (el 458889 [5,19,12] [2919711,9506410]) E) (N (ec 3027050 [3,9]) E)))) (N (N (N (N (el 37703 [0,1,2,3,4,5,6,7,10,16,8,14,9,25,11] [1090801,3188265,4687566,4884198,5285141]) (e1 6328436 9)) (N (e1 1269892 9) E)) (N (N (e1 327765 12) E) (N (e1 2429017 22) E))) (N (N (N (el 135509 [0,2,4,15,5,6,12] [371138,2468630,2534190,2796336,4803288,4868832,4934396,5065504,9087794]) E) (N (e1 1736821 9) E)) (N (N (el 725114 [1,4,12,13] [2821972,2953056,4655830,5050236]) E) (N (ec 3686452 [0,6]) E))))) (N (N (N (N (N (el 20553 [0,1,2,3,4,5,6,7,10,8,9] [566690,697764,959910,2663848,2794922,3122567,7251065,9364908,11462062]) (e0 5129028)) (N (e1 1192016 3) E)) (N (N (el 233520 [0,1,2,3,4,15,5,6,7,34,9,35,11] [691536]) E) (N (e1 2221141 2) E))) (N (N (N (el 107653 [2,4,6,7] [264694,395726,2361848,2460104,9079274]) E) (N (e1 1609768 17) E)) (N (N (ec 569449 [1,2,4,15,5,6,7,28,20,12]) E) (N (el 3244154 [0,10] [2953664]) E)))) (N (N (N (N (el 69689 [0,1,2,3,4,5,6,7,10,8,19,20,11] [698422,2426232,4892673,5023800,6989877]) (e1 7647288 34)) (N (ez 1381188 [2822316]) E)) (N (N (e1 393357 15) E) (N (e0 2785397) E))) (N (N (N (el 148038 [4,15,6] [2657220]) E) (N (e1 1937785 9) E)) (N (N (e1 782397 22) E) (N (e0 3915881) E)))))) (N (N (N (N (N (N (el 8309 [0,1,2,3,4,15,5,6,7,10,8,9,22] [697515,713946,730332,2794675,2811061,2827486]) (e1 4583452 22)) (N (e1 1089877 22) E)) (N (N (ec 204889 [1,2,4,5,6,7,12,9,13]) E) (N (e1 2154592 3) E))) (N (N (N (el 99461 [5,6,17,9] [264540,395572,2361694,2459952,2656594,5310744]) E) (N (ef 1556804 2 [6852858]) E)) (N (N (el 495668 [0,1,2,3,4,15,5,6,7,10,22] [855812]) E) (N (el 3072058 [2,9] [2691504]) E)))) (N (N (N (N (el 49991 [0,1,2,3,4,15,6,7,10,16,8,22,11] [426456,493400,557538,2523976,2655282,4687750,4818288,4883725,7119691,11314233]) (e0 7155816)) (N (e1 1327193 22) E)) (N (N (el 352629 [1,3,4,15,6,7,10,28,19,20,12] [7122348,7253434]) E) (N (e1 2666632 0) E))) (N (N (N (el 143429 [0,1,2,3,4,15,6,7,10,16,8,22,11] [732024]) E) (N (e1 1839189 22) E)) (N (N (el 750407 [0,1,2,4,15,5,6,7] [405448,438178,470986,503756,567552,602062,698625,733135,2665660,4893885]) E) (N (ec 3793512 [1,16]) E))))) (N (N (N (N (N (el 28777 [0,1,2,3,4,5,6,7,8,12,9,13,11] [960138]) (e0 5501764)) (N (e1 1217113 22) E)) (N (N (el 286776 [0,1,2,3,4,15,5,6,7,10,8,13,22,11] [453990,585063,6876520]) E) (N (ec 2330676 [6,8]) E))) (N (N (N (el 131188 [0,1,2,3,4,15,6,7,10,28,12] [2926906,2959828,3058196,3091000,4754056,7121546,7154316,9218702,9349776]) E) (N (e1 1651285 2) E)) (N (N (e1 663665 15) E) (N (e1 3362903 1) E)))) (N (N (N (N (ec 82549 [0,3,16,8,9,25]) (e0 9158760)) (N (el 1450357 [6,11] [856264,987338]) E)) (N (N (el 418119 [4,6] [428250,986721,4624034,4754436]) E) (N (e1 2933105 15) E))) (N (N (N (e1 164749 15) E) (N (e1 2027576 9) E)) (N (N (ec 831561 [0,1,2,3,4,5,6,10,8,22]) E) (N (ez 3977288 [430560]) E))))))))))) (N (N (N (N (N (N (N (N (N (N (N (el 23 [0,1,2,3,4,5,6,7,8] [434214,450600,466986,483372,565294,581680,598066,614452,827446,843832,860218,876604,925758,942144,958530,974916,991302,1007688,1024074,1040460,2662478,2678864,2695250,2941012,3055702,3072088,3088474,3137628,4628574,4759648,5021794,5152868,6873190,7135336,7266410,7331948,9363566,9429104,13557874,13623412]) (ec 3981384 [4,11])) (N (el 852040 [0,2,4,5,6,17] [962620,994523]) E)) (N (N (el 168821 [1,2,4,5,6,7,8,17,12] [871488,2411582,2632364,2730954]) E) (N (e1 2027624 2) E))) (N (N (N (el 82821 [3,4,10,16,8,22] [2459736,2590816,2656358]) E) (N (e1 1450869 4) E)) (N (N (el 426052 [0,2,15,5,10,12,9] [2664708,6859782]) E) (N (e1 2937120 15) E)))) (N (N (N (N (el 28789 [0,1,2,3,4,15,5,6,7,10,8,28,12,13] [657036,722574,861840,992914,5039626,5170836]) (e0 5522265)) (N (e1 1221168 15) E)) (N (N (ez 287831 [396652,428224,462190,494960,7146856]) E) (N (e0 2330724) E))) (N (N (N (e1 131212 0) E) (N (el 1658968 [2,6] [2429050]) E)) (N (N (el 663673 [0,1,2,3,4,5,6,7,8] [175789,184015]) E) (N (ec 3387480 [2,4,15,7]) E))))) (N (N (N (N (N (el 8565 [0,1,2,3,4,15,5,6,7,10,8,12,9,22] [607456,697153,713954,730340,2794539,2810951,2827494,5014744]) (e1 4640888 9)) (N (el 1102124 [2,5,9] [299108]) E)) (N (N (el 204919 [6,18,12] [527634,593172,658710,724248,3214608]) E) (N (el 2163061 [4,6,12] [528718]) E))) (N (N (N (ef 102475 3 [428162,2394464]) E) (N (e0 1557044) E)) (N (N (el 503925 [0,1,2,3,4,5,6,28,12,29,13] [855814,872200,4632076]) E) (N (e0 3072104) E)))) (N (N (N (N (el 50279 [0,1,2,3,4,15,6,7,10,8,19,20,12,22,11] [2590600,2721138,2786575,7250765,11445307]) (e0 7229468)) (N (el 1327210 [1,13] [2953382]) E)) (N (N (e1 360504 17) E) (N (ec 2699290 [2,5,9]) E))) (N (N (N (el 143445 [0,1,2,3,4,15,5,6,7,17] [215438,305370,437114,699260,732030,985984,1002370,2403204,4631430,4664200]) E) (N (e1 1839226 0) E)) (N (N (el 753733 [0,1,2,3,4,6,7,10,8,13,22,11] [700378,733148,4894686,5156832]) E) (N (ec 3809324 [3,4,22]) E)))))) (N (N (N (N (N (N (el 4213 [0,1,2,3,4,15,5,6,7,10,8,12] [205546,213782,221976,475930,525084,541470,565720,582432,590626,598820,607014,615208,696902,713514,729900,746286,852784,869170,959284,975670,992056,1008442,2794300,2810686,2827072,3072834,4907844,5169990,6857544,9102154,9364300]) (ef 4211061 6 [987638])) (N (e0 966696) E)) (N (N (e1 180784 15) E) (N (e1 2121813 22) E))) (N (N (N (e1 94321 15) E) (N (e1 1511720 15) E)) (N (N (e1 462896 28) E) (N (e0 3031157) E)))) (N (N (N (N (el 38527 [0,1,2,3,4,15,5,6,7,10,14,9] [427764,493302,567032,689914]) (el 6398000 [5,9] [561658])) (N (ef 1273976 5 [5181582]) E)) (N (N (el 328533 [1,2,3,4,5,6,7,10,27,19,9] [3059116,5049762,5156135,7253291]) E) (N (e1 2429028 12) E))) (N (N (N (el 135543 [0,6,10,12,9] [7146216]) E) (N (ef 1741176 4 [4657424]) E)) (N (N (el 725328 [0,1,2,3,4,6,10,8,12,13,22,11] [233342,241536,2707286,2797416,2830188,9088079]) E) (N (el 3690856 [6,16] [3084762]) E))))) (N (N (N (N (N (ec 20569 [0,1,2,3,4,5,6,7,8,12,13]) (e0 5230636)) (N (e0 1192024) E)) (N (N (ef 233529 9 [560468]) E) (N (e1 2244640 17) E))) (N (N (N (ec 110713 [0,1,2,3,4,15,5,6,7,18,9,11]) E) (N (e1 1610372 9) E)) (N (N (ec 585799 [0,1,2,3,4,5,7,8,12]) E) (N (ef 3256424 5 [9376168]) E)))) (N (N (N (N (ec 69737 [0,1,2,3,4,5,6,10,8,19,20,9]) (e0 7741476)) (N (e1 1384740 2) E)) (N (N (el 401463 [0,1,2,3,4,5,6,17,9,11] [929316,962086,994856,1027626,3059244]) E) (N (e0 2793576) E))) (N (N (N (el 148565 [3,4,7,10,22] [6851282,9079742]) E) (N (e1 1938293 9) E)) (N (N (e1 782437 22) E) (N (e0 3916153) E))))))) (N (N (N (N (N (N (N (el 583 [0,1,2,3,4,5,6,10,8,19,20,12] [434312,467388,696729,729534,827840,860610,958603,991684,2597036,2793885,2924998,3055763,4628752,4891067,5153083,7004384,7135550,7266690,11460713,13558043]) (e1 4063324 15)) (N (el 864324 [2,4,5,6,7,8,17,9] [961771,3059793]) E)) (N (N (el 176453 [1,3,4,15,6,7,10,22,11] [501900,698441,2468970,2525254,2533478,2657412,9088134]) E) (N (ef 2052202 1 [4755767]) E))) (N (N (N (ec 90453 [5,23,11]) E) (N (e1 1478944 15) E)) (N (N (el 442693 [2,3,4,5,6,7,10,23,16,8,9,22,11] [2657292]) E) (N (e1 3014944 15) E)))) (N (N (N (N (ec 32869 [0,1,2,3,4,5,6,7,8,14,12,9]) (e0 5788024)) (N (e0 1257576) E)) (N (N (el 311416 [0,2,3,4,15,7,10,8,12,13] [7122274,7253348,11316602,11447676]) E) (N (e0 2388052) E))) (N (N (N (el 135240 [0,1,2,3,4,15,5,6,7,12,22] [584418,846564,2681574,2943720,4778730,5040876]) E) (N (ec 1683528 [0,9]) E)) (N (N (ec 701255 [0,1,2,4,15,5,6,7,10]) E) (N (el 3547210 [3,7,12,9] [4895053]) E))))) (N (N (N (N (N (el 16469 [0,1,2,3,4,5,6,7,10,12,9] [730442]) (e0 4952100)) (N (ec 1159530 [0,2,17,9]) E)) (N (N (el 225328 [0,1,2,3,4,15,5,6,7] [166130,182880,379886,510959,559347,576097,691510,699704,707898,732476,757054,773440,822594,838980,953667,970053,2534456,4631705,4639896,4664525,4705484,4770873]) E) (N (e1 2191424 34) E))) (N (N (N (el 106629 [2,15,6,12] [723376,788914,854452,985526,2361784,2460090,4622494,6851004,6982078]) E) (N (e1 1589621 9) E)) (N (N (el 544871 [1,2,5,12,9,13] [986906,1117980]) E) (N (e1 3129637 2) E)))) (N (N (N (N (el 61497 [0,1,2,3,4,5,6,7,8,17] [174104,567322,960540,1026078,3073984,3139577,7251051,9364769,9430405]) (e0 7483512)) (N (e1 1356336 15) E)) (N (N (el 385093 [0,1,2,3,4,5,6,10,8,9] [962054,994824,9350407]) E) (N (el 2749269 [1,2,3,4,6,7,10,9] [2929014]) E))) (N (N (N (ec 144503 [0,3,9,25,22]) E) (N (e0 1917780) E)) (N (N (el 766073 [1,2,12,13] [724089,2394917,2788475,5181426]) E) (N (el 3907669 [5,6] [856554,987627]) E)))))) (N (N (N (N (N (N (el 4709 [0,1,2,3,4,5,6,7,8,18,9,11] [992372,5137172,5170040,5202886,5235674,7250998]) (e1 4354088 22)) (N (e0 1032532) E)) (N (N (el 193655 [3,16,8,22] [822065,2919450,4885298,5016727]) E) (N (e1 2134645 9) E))) (N (N (N (el 98426 [0,2,17,9] [4655266]) E) (N (ez 1552414 [299166]) E)) (N (N (e1 471165 15) E) (N (e0 3051640) E)))) (N (N (N (N (el 49207 [0,1,2,3,4,15,6,7,12,22] [590736,598930,608044,657198,673584,722738,739124,829238,862008,984890,1001276,1091390,1124160,2425626,2754370,2770756,2795334,2819912,2828106,2836300,2926414,2959184,3188562,3221332,6989062,7021930,9086217,9119085,9217047,9250019,9479843,9512649]) (e1 6619220 9)) (N (el 1323060 [2,15] [2396318]) E)) (N (N (el 340805 [3,4,15,6,7,10,16,9,22] [4893985,6991139]) E) (N (ef 2584696 5 [7278962]) E))) (N (N (N (el 139386 [1,15,12,13] [2820930,2952018,4655824]) E) (N (ez 1794096 [168082,364718,2527532,2658606]) E)) (N (N (ec 729207 [0,9]) E) (N (e1 3780704 3) E))))) (N (N (N (N (N (el 21879 [0,1,2,3,4,15,5,6,7,28,12,9] [394818,426805,435640,460356,468550,493128,566794,599626,959737,992844,2663954,3057216,4637511,4703742,4899851,7251184,7284142,7407064,7423460,11445800]) (e0 5427268)) (N (e1 1200437 2) E)) (N (N (el 266327 [5,8,9,22] [593244,2952538,9342296]) E) (N (ef 2314261 6 [397415]) E))) (N (N (N (el 123273 [0,15,9] [2394674,2427458]) E) (N (el 1642567 [2,5] [987412]) E)) (N (N (el 639061 [6,18,14,12,9] [1117992]) E) (N (ef 3330132 15 [2396620,4624835]) E)))) (N (N (N (N (el 78453 [3,4,15,6,7,10,16,8,22,11] [2525254,2795592]) (e1 8081436 32)) (N (e1 1401128 15) E)) (N (N (el 406655 [0,2,4,15,9] [560784,822930,5016641]) E) (N (e0 2847559) E))) (N (N (N (el 159871 [2,4,5,9] [166775,429062,560136,691210]) E) (N (e1 1990773 9) E)) (N (N (el 802901 [0,1,2,3,4,15,5,6,7,8,9] [217138,567514,600240,2665441]) E) (N (e1 3952688 17) E)))))))) (N (N (N (N (N (N (N (N (el 87 [0,1,2,3,4,5,6,7,8,14,9] [434230,467242,565386,598316,827642,860462,926000,958723,991538,1024308,2547796,2941192,3072310,3137848,4759866,5153047,6873404,7266531,7332081,9232702,9363613,9429175,13558080,13623618]) (e1 4042848 3)) (N (el 852309 [3,5,7,8,11,32] [2461760]) E)) (N (N (el 176202 [1,3,4,15,6,7,22] [281686,2796632,2829402,4598432,4697016,4770908,4893790,4926560,5155938,5188708,9088102,9350248]) E) (N (ef 2043953 2 [692538,954684,2396460,4755774]) E))) (N (N (N (el 86397 [3,4,15,6,8,22,11] [297026,428150,559224,2394224,2525306,4892782]) E) (N (ef 1462388 5 [364738,2789580]) E)) (N (N (el 430725 [2,5,7,12,9] [9506382]) E) (N (e1 2998360 1) E)))) (N (N (N (N (ec 29269 [0,1,2,3,4,5,6,7,8,27,12,13]) (e0 5693480)) (N (e0 1245561) E)) (N (N (el 296055 [2,6,8,13,22] [986490,4754463]) E) (N (e1 2363456 7) E))) (N (N (N (el 132197 [2,4,5,6] [297594,330428,2394752,4950718,5016156,5081792,5147278,5278402,9079460]) E) (N (ec 1663285 [2,5]) E)) (N (N (el 671863 [1,8,12,29,22] [3084106]) E) (N (e1 3428458 3) E))))) (N (N (N (N (N (el 12901 [0,1,2,3,4,5,6,7,10,8,24,9,25] [4760030,5022966,7251214,9364758,13559064]) (e1 4861984 15)) (N (e0 1130836) E)) (N (N (el 213389 [0,15,8,9,25] [560422,691496,822570,2788494]) E) (N (ez 2175025 [299162,692562,954708,2396310,4755798]) E))) (N (N (N (ef 102527 15 [166284,2427292]) E) (N (el 1569332 [1,4,15,6,7,10,9,22] [610564]) E)) (N (N (e1 528505 9) E) (N (ec 3084388 [0,15]) E)))) (N (N (N (N (el 54103 [0,1,2,3,4,15,5,6,7,8,17] [428002,444404,460790,696919,731128,2525162,2655314,4891735,6989790,9144306]) (e1 7389212 39)) (N (e1 1335385 22) E)) (N (N (el 376965 [5,6,12,9,11] [593392,723730,855538,986612,5311990]) E) (N (ec 2723925 [5,9]) E))) (N (N (N (el 143655 [4,15,10,22] [723856]) E) (N (ec 1876005 [4,22]) E)) (N (N (el 758119 [1,3,28,20,12] [724758]) E) (N (ec 3878984 [4,22]) E)))))) (N (N (N (N (N (N (el 4425 [0,1,2,3,4,5,6,7,8,17] [959488,5137168,5170034,5202880,5235670,7250946]) (ec 4239444 [15,5])) (N (e0 1007956) E)) (N (N (el 185173 [1,2,4,5,6,7,8,17,12] [436473,470224,2534606,2730478,4631752]) E) (N (ez 2126421 [2789702]) E))) (N (N (N (el 94581 [0,2,4,15,5,6,17,9] [264434,272562,280820,370848,2369718,2468072,2533622,2566392,4892922,4925692,5195950]) E) (N (e0 1532484) E)) (N (N (e1 467004 9) E) (N (e0 3039336) E)))) (N (N (N (N (el 45109 [0,1,2,3,4,15,5,6,7,10,12,9] [698142,2795296]) (e0 6590548)) (N (el 1286484 [5,17] [2363548,2494616]) E)) (N (N (el 337015 [3,6,14,9] [855486,1117632,2919864]) E) (N (el 2486372 [0,9] [6852962]) E))) (N (N (N (el 139338 [4,6,12,22,26] [2558776,3083074,4655818]) E) (N (e0 1761656) E)) (N (N (el 725381 [0,4,6,9,11] [461604,790412,855950,5050206,5312376]) E) (N (ec 3760472 [4,22]) E))))) (N (N (N (N (N (el 20823 [0,1,2,3,4,5,6,7,8,12,9,29] [591282,1058312,1091082,1123852,1156622,3188240,5285394,7275978,7381827,9479305]) (e1 5345608 22)) (N (e1 1196128 3) E)) (N (N (el 237684 [0,1,3,4,15,6,7,10,9] [4754598]) E) (N (e1 2269260 17) E))) (N (N (N (el 115589 [4,5,18,14,9] [264736,2361890,2460170,5179906]) E) (N (e1 1618757 12) E)) (N (N (ec 616055 [3,14,20,13,22]) E) (N (el 3305578 [3,5] [3084742]) E)))) (N (N (N (N (ec 77893 [0,1,2,3,4,5,6,10,8,22,11]) (e0 7852136)) (N (e1 1392748 3) E)) (N (N (el 402279 [1,2,3,4,15,6,7,9] [437798,470622,568118,601696,830819,863755,986722,1003108,2665520,2928220]) E) (N (e0 2818887) E))) (N (N (N (ef 156261 2 [396270,494020,2525514,2657264,2788338,4623222,4754392,4885476]) E) (N (e1 1982538 4) E)) (N (N (e1 794672 21) E) (N (ec 3928121 [4,9]) E))))))) (N (N (N (N (N (N (N (el 4169 [0,1,2,3,4,5,6,7,8] [180790,565886,582272,598540,615042,926340,942726,959112,975498,991884,1008270,1024656,1041042,2400916,5169814,5235352,9364122,9429660]) (ec 4132890 [2,5,9])) (N (ec 897877 [0,2,3,4,15,5,6,10,18,9]) E)) (N (N (el 176965 [1,3,4,6,7,10,16,22,11] [2526340,4893489,6925246,6990999]) E) (N (e1 2072680 2) E))) (N (N (N (ec 91221 [2,3,7,23]) E) (N (el 1495340 [0,9] [2691282]) E)) (N (N (el 454709 [15,5,10,9,22] [593598,855744,3214992]) E) (N (e0 3022969) E)))) (N (N (N (N (el 36985 [0,1,2,3,4,15,5,6,7,10,8,14,9,25] [566996,960214,2680395,3073752]) (e0 6209860)) (N (el 1269804 [2,5] [987280]) E)) (N (N (el 323705 [0,1,2,3,4,6,7,10,9] [183690,699794,732469]) E) (N (el 2424896 [2,4,15,5,6,8,12,11] [299188]) E))) (N (N (N (el 135274 [0,1,2,3,4,6,12,13] [2443984,2706134,2820852,2837238,2927372,2960148,3058460,3091230,5024544]) E) (N (e1 1696853 22) E)) (N (N (el 725080 [0,1,2,3,4,15,6,7,12,22] [2797404,3059550,9088113,9350939]) E) (N (ez 3666052 [4624843]) E))))) (N (N (N (N (N (el 17271 [0,1,2,3,4,15,6,7,10,12,9,13] [427310,722310,827995,984456,2524472,2786678,5022703,7120198,7382354]) (e1 5108072 12)) (N (ef 1187892 5 [3084392]) E)) (N (N (ec 229444 [1,2,4,15,5,6,7,10,22]) E) (N (e1 2207777 22) E))) (N (N (N (ec 107061 [2,4,5,7,9]) E) (N (e1 1602156 3) E)) (N (N (e1 549424 15) E) (N (e0 3244089) E)))) (N (N (N (N (ec 65609 [0,1,2,3,4,5,6,10,8,18,22,11]) (e0 7618650)) (N (e1 1380448 3) E)) (N (N (el 393288 [1,2,5,6,9,29,11] [962060]) E) (N (ez 2764904 [7278972]) E))) (N (N (N (el 148020 [1,4,15,6,7] [478132,543670,609208,2665368,2697356,2796448,2828742,3058618,3091388,4761696,4794512,6859710,6990784,7252930]) E) (N (e1 1933380 4) E)) (N (N (e1 782384 17) E) (N (el 3907957 [0,4] [5181936]) E)))))) (N (N (N (N (N (N (el 5751 [0,1,2,3,4,15,5,6,7,9,11] [394428,402622,459968,468162,4637506,4703128,4752428,4768814,4899976]) (e0 4562968)) (N (ec 1077589 [2,22]) E)) (N (N (el 197759 [2,3,8] [429308,494846,560384,822530,5016720]) E) (N (e1 2142344 4) E))) (N (N (N (el 98701 [2,15,5] [297178,428266,2459948,2525514,5310740]) E) (N (el 1552964 [4,15,6,12] [2543850,2609390,5025996,5058772]) E)) (N (N (e1 479337 12) E) (N (e0 3063929) E)))) (N (N (N (N (el 49226 [0,1,2,3,4,15,5,6,7,22] [279912,410985,583564,714637,845710,976783,2664264,2680652,2697068,2795337,2811725,2828141,2926480,2942866,2959252,3057553,3073939,3090325,4760594,4777022,4793568,4908568,5023392,5039790,5056198,5170910,6874649,6988819,7005247,7021793,7136991,7251617,7268015,7284423,9103254,9365400,11331481,13559706]) (e0 7008376)) (N (ef 1327130 2 [299170]) E)) (N (N (el 344933 [1,3,4,15,6,7,10,19,20,12,9] [7122063]) E) (N (ec 2629717 [3,9,11]) E))) (N (N (N (el 140137 [6,8,22] [363372,5049164,5180252]) E) (N (e1 1822837 9) E)) (N (N (ez 742487 [528282,561000,593820,626590,2788436,5016661,6917480]) E) (N (e1 3789146 3) E))))) (N (N (N (N (N (el 25983 [0,1,2,3,4,15,5,6,7,10] [427644]) (e0 5460042)) (N (e1 1216544 15) E)) (N (N (ec 278617 [0,1,2,3,4,5,6,10,8,12]) E) (N (e1 2318468 9) E))) (N (N (N (el 131156 [0,1,2,3,4,15,6,7,10] [2795830,2828752,3058192,3090996,4622932,4631126,6990424,7023194,9087580,9349726]) E) (N (e0 1651033) E)) (N (N (e1 655416 28) E) (N (ec 3350580 [2,6]) E)))) (N (N (N (N (el 82261 [2,3,5,11] [460892,2459726]) (e0 8204649)) (N (e0 1425476) E)) (N (N (el 413800 [0,1,2,3,4,15,5,7,9,22] [183693,2797056,2928160,3083906,4770633,6990850]) E) (N (ef 2920552 5 [5181830]) E))) (N (N (N (e1 163981 15) E) (N (ez 2003284 [4755762]) E)) (N (N (ec 819783 [0,1,2,3,4,15,5,6,7,10]) E) (N (e0 3965033) E))))))))) (N (N (N (N (N (N (N (N (N (el 55 [0,1,2,3,4,5,6,7,8,9,11] [434222,450744,467130,565382,598204,696510,712896,729282,852164,868550,925896,958531,975050,991436,1024206,1040592,2531406,2547792,2564224,2810066,3072212,3137750,4759768,5152869,6873306,7266524,7332062,9101536,9363609,9429171,11460834,11526372]) (ec 3998069 [1,25])) (N (el 852090 [0,7,17,9] [2822206]) E)) (N (N (ec 173189 [0,6,7,14]) E) (N (e0 2035796) E))) (N (N (N (el 86087 [2,5,22,11] [2525244]) E) (N (e0 1458500) E)) (N (N (el 430213 [2,5,8,28] [724498,986790,9506374]) E) (N (e0 2973816) E)))) (N (N (N (N (el 29045 [0,1,2,3,4,15,5,6,7,10,12,13] [738976,845474,878244,976550,1009320,2925613,3057322]) (e0 5550408)) (N (el 1232964 [15,5] [2592902]) E)) (N (N (el 291124 [0,1,2,3,4,15,5,6,7,10,8,13,22,11] [567367,2551158,2682231,4630598,6876536]) E) (N (e1 2347088 7) E))) (N (N (N (el 131637 [4,15,7,22] [4688462,4885078,5016176,5278376]) E) (N (el 1659016 [6,11] [2953498,3084578]) E)) (N (N (el 671815 [4,6,8,22] [462654,1118016,2953026]) E) (N (e0 3416184) E))))) (N (N (N (N (N (el 12389 [0,1,2,3,4,5,6,7,10,8,24,14,9,25] [9364728,13559034]) (e0 4747380)) (N (e0 1110328) E)) (N (N (el 205911 [6,10,13,22] [4754459,5016592]) E) (N (ez 2170965 [2789712]) E))) (N (N (N (el 102519 [15,6] [788870,854408,985482,2361712,2427250,2525342]) E) (N (ef 1565541 2 [9081088]) E)) (N (N (el 516213 [0,1,2,3,4,5,6,28,12,9,13] [855824,872210]) E) (N (e0 3076181) E)))) (N (N (N (N (el 53333 [0,1,2,3,4,15,5,6,7,10,8,9] [435067,567266,829420,985070,2532301,4760652,6874655,7136995]) (e0 7319580)) (N (e0 1331320) E)) (N (N (e1 368696 27) E) (N (ec 2715674 [3,22]) E))) (N (N (N (el 143479 [0,5,9] [985996]) E) (N (e0 1843336) E)) (N (N (ef 754775 3 [397282,430042,462820,495590,561128,593898]) E) (N (e1 3829856 3) E)))))) (N (N (N (N (N (N (e1 4221 15) (e1 4235296 12)) (N (ef 991573 22 [397408]) E)) (N (N (el 184341 [1,4,15,6,7,10,9,22] [609356,699255,732356,2796742,6991048]) E) (N (e1 2122357 9) E))) (N (N (N (el 94329 [0,1,2,3,4,15,5,6,7,17] [174298,182456,436444,698590,731360,2533602,2566372]) E) (N (e1 1527925 9) E)) (N (N (el 462921 [2,5,12] [691914,9506416]) E) (N (e1 3035261 15) E)))) (N (N (N (N (e1 41085 15) (e0 6488180)) (N (ec 1282356 [15,5]) E)) (N (N (ec 331865 [0,1,2,3,4,5,6,7,10,12]) E) (N (e1 2433140 12) E))) (N (N (N (el 136279 [3,6,23,13,22] [4754224]) E) (N (e1 1753941 2) E)) (N (N (ec 725337 [3,4,6,16,13,22]) E) (N (e1 3703157 20) E))))) (N (N (N (N (N (el 20599 [0,1,2,3,4,15,5,7,9,11] [460264,476650,591340,607726,697746,730608,853490,869876,959928,992758,2794906,3057088,3212764,4768619,6988766]) (e0 5234808)) (N (el 1192042 [1,5,13] [2953342,3084416]) E)) (N (N (el 237629 [4,15,7] [6851748]) E) (N (ef 2253382 6 [2527541]) E))) (N (N (N (el 115073 [0,4,5,6,9,11] [363022,821776,952850,1083924,2787862,5179898]) E) (N (el 1618234 [6,12,22,26] [2953488]) E)) (N (N (ec 610421 [0,1,2,3,4,5,6,14,25]) E) (N (ec 3289172 [1,5]) E)))) (N (N (N (N (ec 73785 [0,1,2,3,4,5,6,7,8,21,12,9,13]) (e0 7794804)) (N (ez 1385284 [4755644]) E)) (N (N (el 401751 [1,2,3,4,6,7,8,36,9] [929348,962118,994888,1027658,3059276,5156430]) E) (N (el 2802520 [6,12] [233858]) E))) (N (N (N (el 155701 [4,15,7,10] [723934,4656038]) E) (N (e0 1954649) E)) (N (N (e1 786481 22) E) (N (e0 3924025) E))))))) (N (N (N (N (N (N (N (el 4153 [0,1,2,3,4,5,6,7,10,8,22,11] [180688,565768,582154,598540,958990,991760,3121682,5153300,7250454,9363992]) (e0 4120661)) (N (e1 864653 22) E)) (N (N (el 176473 [1,2,4,15,5,6,7,10,9,22] [502940,953502,4934752]) E) (N (e1 2064757 4) E))) (N (N (N (el 90692 [3,4,6,16,8,22,11] [2664580,6858900]) E) (N (e1 1486938 3) E)) (N (N (e1 450608 12) E) (N (e1 3018877 15) E)))) (N (N (N (N (el 36921 [0,1,2,3,4,5,6,7,8,14,25] [960202,1025740,7251645]) (e0 5894468)) (N (ef 1261860 2 [331892]) E)) (N (N (el 323657 [0,1,2,3,4,5,6,7,10] [183682,961926,994613]) E) (N (e1 2396260 8) E))) (N (N (N (el 135255 [2,5,6] [461098,592640,723714,789252,854790,985864,1116938,2427066,2886364,2951920,3083020]) E) (N (el 1683576 [6,11] [2953500,3084584]) E)) (N (N (e1 721772 3) E) (N (e0 3653752) E))))) (N (N (N (N (N (el 16949 [0,1,2,3,4,5,6,7,10,16,9] [3057014,4760896,5023052,5154146,7251312,9364623]) (e1 5054552 22)) (N (e0 1180025) E)) (N (N (ec 229428 [0,1,2,3,4,15,5,6,10,12,22]) E) (N (e1 2203693 22) E))) (N (N (N (ef 106885 6 [330200,788954,854492,985566,2361824,2460098]) E) (N (ez 1598293 [2527482,7115008]) E)) (N (N (el 545141 [0,1,2,4,15,5,6,7,12,9,13] [5066520]) E) (N (e1 3191653 12) E)))) (N (N (N (N (el 61513 [0,1,2,3,4,5,6,10,8,17,22] [567340,960557,4760678,7251047]) (e0 7577720)) (N (e0 1368124) E)) (N (N (ec 385365 [1,2,3,4,5,6,10,8,9,22]) E) (N (ef 2752885 3 [2658617,7278964]) E))) (N (N (N (e1 147589 9) E) (N (e0 1929817) E)) (N (N (el 770149 [0,1,2,3,4,5,6,12,13] [470732]) E) (N (e1 3907701 9) E)))))) (N (N (N (N (N (N (el 4983 [0,1,2,3,4,15,6,7,10,8,11] [426456,434670,492048,500256,689242,827879,2523616,2531838,2786400,4752418,7119448,7152282,9217004,11314288]) (e1 4538408 34)) (N (e1 1065081 2) E)) (N (N (el 196729 [1,2,4,5,6,7,17] [175330,503012,699622,2673836,2739408]) E) (N (ec 2138676 [3,15,22]) E))) (N (N (N (e1 98445 15) E) (N (el 1552676 [4,6,10,12,22] [610546,7123188]) E)) (N (N (el 479320 [0,1,2,3,4,15,5,6,7,22] [585466,716540,2682563,2813694]) E) (N (e0 3059833) E)))) (N (N (N (N (el 49218 [0,1,2,3,4,15,5,6,7,10,8,13,22,11] [230652,239472,2664258,2680644,2697066,2795331,2811717,2828139,4760590,6988815,9103218]) (e1 6844736 7)) (N (e1 1323116 3) E)) (N (N (el 344135 [3,6,13,22] [462300,7015902]) E) (N (e0 2621525) E))) (N (N (N (el 139846 [15,6,7,10,12] [2460242,4918088]) E) (N (e1 1802848 3) E)) (N (N (el 733520 [0,1,2,3,4,15,6,7,10,8,22,11] [2797460,9088081]) E) (N (el 3781224 [5,6] [233954,2953700,3084773]) E))))) (N (N (N (N (N (el 24693 [0,1,2,3,4,15,5,6,7,10,8,22] [566833,583270,599656,722538,738924,829038,845424,861810,2680375,2942580,4760576]) (e0 5448516)) (N (ec 1212468 [2,5]) E)) (N (N (e1 274517 12) E) (N (e1 2318404 2) E))) (N (N (N (el 131100 [0,1,2,3,4,15,6,10] [182854,698952,731419,961098,993868,2402894]) E) (N (ef 1643079 5 [987414]) E)) (N (N (ec 644727 [3,22]) E) (N (ez 3330340 [201166,2658764]) E)))) (N (N (N (N (ec 82005 [5,23,11,32]) (e1 8196200 12)) (N (ef 1409909 6 [2592956]) E)) (N (N (el 413754 [2,5,9,11] [2690718,2952864,5312124]) E) (N (e1 2891876 22) E))) (N (N (N (el 160629 [1,2,4,5,6,7,12,9] [535216,699420,732192,871458,2411311,2477060,2526230,2542616,2632362,2730952,5196794,6924778,6990864]) E) (N (e0 1995076) E)) (N (N (el 803157 [1,2,4,5,6,7,8] [567557,602166,2469940,2665685]) E) (N (e1 3952712 22) E)))))))) (N (N (N (N (N (N (N (N (el 107 [0,1,2,3,4,15,5,6,7,10,8,9] [303494,434568,696714,827788,958862,2458000,2531418,2924814,4645079,4907101,5038393,7004562,11329940]) (e1 4051044 22)) (N (ec 856133 [0,1,2,3,4,5,6,10,8,17,22]) E)) (N (N (el 176219 [2,4,7,22] [2394841,2886736,2952282,4623433]) E) (N (e1 2045013 22) E))) (N (N (N (el 90197 [2,3,5,9,11] [2459778,4622396,6981764]) E) (N (ef 1466504 5 [5181642]) E)) (N (N (el 434297 [1,15,5,27,12] [560812,9506390]) E) (N (e0 3003016) E)))) (N (N (N (N (el 29799 [0,1,2,3,4,5,6,7,10,8,24,12,9,25,13] [2524406,2787000]) (e0 5734520)) (N (e0 1257512) E)) (N (N (ef 304215 10 [9211256]) E) (N (e0 2371645) E))) (N (N (N (el 135226 [4,6,12,22,26] [2427592,2443978,2968278,4893400]) E) (N (e0 1671783) E)) (N (N (el 684084 [0,1,2,3,4,15,5,6,7,10,22] [855886]) E) (N (e1 3477624 1) E))))) (N (N (N (N (N (el 13399 [0,1,2,3,4,5,6,7,10,8,27,12,13] [460068]) (e1 4882720 15)) (N (e0 1138772) E)) (N (N (el 221245 [4,15,7] [6851720]) E) (N (e0 2179668) E))) (N (N (N (el 103543 [3,10] [428408,493970,2525606]) E) (N (ez 1581941 [4657416,7114996]) E)) (N (N (ec 541061 [0,1,14,9]) E) (N (e0 3096630) E)))) (N (N (N (N (el 57925 [0,1,2,3,4,5,6,10,23,16,8,22] [958941,2663970,3056733,4760028,6857820,7251491]) (e1 7430432 15)) (N (el 1339444 [2,5,17,9] [2396322]) E)) (N (N (el 377221 [4,15,5,9,11] [461008,855552,2362882,2460417]) E) (N (ez 2732917 [2527569]) E))) (N (N (N (el 143959 [2,4,5,9] [1117078,2722708,4688280]) E) (N (e1 1916992 15) E)) (N (N (el 759415 [3,12,9] [528388,593926]) E) (N (e1 3903552 22) E)))))) (N (N (N (N (N (N (el 4473 [0,1,2,3,4,15,5,6,7,10,8,12,9] [173130,697420,2417512,2540622,2810960,4907640,4940472,6988882]) (e1 4243581 15)) (N (e1 1016148 6) E)) (N (N (el 192629 [1,3,4,6,7,10,16,8,12,13,22] [9088028]) E) (N (e0 2134361) E))) (N (N (N (el 95359 [2,3,15,5,11] [428294,493832,559370,2590988]) E) (N (ez 1545049 [561378]) E)) (N (N (el 471155 [2,4,15,5,6,7,8] [233139,691938,823012,954086,1085160,2395882,4624069]) E) (N (e0 3043445) E)))) (N (N (N (N (el 45156 [0,1,2,3,4,15,5,7,10,28,12,9] [7005988]) (e1 6594605 22)) (N (e1 1298732 22) E)) (N (N (el 340041 [0,1,2,3,4,15,6,7,10,9,22] [699852,4894001]) E) (N (e0 2556245) E))) (N (N (N (ec 139353 [3,4,15,22]) E) (N (e1 1770341 2) E)) (N (N (el 729173 [0,1,2,3,4,5,6,9,22] [470706,4631354]) E) (N (ec 3768364 [4,6,13]) E))))) (N (N (N (N (N (el 21319 [0,1,2,3,4,5,6,7,10,16,8,9,11] [426450,1090799,2655208,3188263,4687272,4884002,5285139,7275984,7381835,11576459]) (e1 5390456 9)) (N (el 1200149 [5,6,10,12] [725116,987266]) E)) (N (N (ec 254039 [2,9,22]) E) (N (e1 2310216 2) E))) (N (N (N (el 123013 [0,15,9,11] [723500,854574,2361904,2460210]) E) (N (ec 1634333 [3,6,13]) E)) (N (N (ec 634969 [15,18,14,9]) E) (N (ef 3309688 5 [3084734]) E)))) (N (N (N (N (el 77945 [0,1,2,3,4,15,6,7,10,16,8,22,11] [731200]) (e0 7995752)) (N (e1 1396832 3) E)) (N (N (el 402799 [1,2,3,4,15,6,7,10,9] [437876,568950]) E) (N (ec 2834501 [3,12]) E))) (N (N (N (el 156805 [0,9] [4885468,6884270]) E) (N (ez 1983317 [2658610]) E)) (N (N (el 798775 [4,6,10,12,22] [2821978]) E) (N (el 3936341 [5,6,13,11] [462972]) E))))))) (N (N (N (N (N (N (N (el 4201 [0,1,2,3,4,5,6,7,8,9,11] [959190,1024728]) (e1 4178004 15)) (N (ec 913477 [0,1,2,3,4,5,6,10,8,19,20]) E)) (N (N (el 177271 [4,10,9,25,22] [2722958]) E) (N (e1 2081096 15) E))) (N (N (N (ec 94281 [0,1,2,3,4,5,6,10,8,22]) E) (N (ez 1503572 [2920660,3051734]) E)) (N (N (e1 458808 19) E) (N (el 3027048 [0,2,9] [2797976]) E)))) (N (N (N (N (el 37445 [0,1,2,3,4,5,6,7,10,8,24,14,9,25] [2664166,2926312,3122557,9365057,13559530]) (e0 6328404)) (N (ef 1269876 5 [5181578]) E)) (N (N (el 324213 [1,3,4,15,6,7,10,9,22] [609694,2469270,2796683,6991258]) E) (N (el 2429014 [2,3,4,5,6] [2396390,2789607,2920814,3051887]) E))) (N (N (N (el 135291 [0,6,9,11] [2951930,3214110]) E) (N (e0 1736789) E)) (N (N (el 725112 [0,1,2,3,4,15,6,7,12,13] [2822000,2838386,2928500,2961270,3059576,3092346,9219187,9350941]) E) (N (ez 3678508 [168406]) E))))) (N (N (N (N (N (el 20537 [0,1,2,3,4,5,6,7,8,9,11] [959902,1025440,7251069]) (e0 5124932)) (N (el 1191978 [2,5] [2429044,2560121,2691194]) E)) (N (N (el 229508 [1,2,3,4,15,6,7,10,9] [4754590]) E) (N (ec 2220614 [15,6]) E))) (N (N (N (el 107605 [2,3,4,7,23] [2460148,9079272]) E) (N (e1 1606276 9) E)) (N (N (e1 569376 15) E) (N (e1 3244152 9) E)))) (N (N (N (N (el 66117 [0,1,2,3,4,5,6,10,8,24,18,9] [993332,3122555,5187634]) (e0 7643188)) (N (el 1380652 [2,12] [299170,2691248]) E)) (N (N (el 393353 [1,2,15,5,12] [724245,2394915,2788633,5312026]) E) (N (e1 2781557 3) E))) (N (N (N (el 148036 [4,15,6,12] [871366,2796450,2828744,4761698,4794514,6990792,7023562]) E) (N (e1 1937781 9) E)) (N (N (ez 782393 [166106,561176,692249,823322,888860,2887580,2953212]) E) (N (e0 3912053) E)))))) (N (N (N (N (N (N (ec 8293 [0,1,2,3,4,5,6,7,8,14,9]) (e0 4575560)) (N (ec 1085748 [4,15,10,8]) E)) (N (N (el 204887 [6,17,12] [527624,592281,658698,724236,3083534]) E) (N (e0 2154584) E))) (N (N (N (el 99413 [2,3,5,17,9,11] [2459994]) E) (N (e1 1556564 9) E)) (N (N (e1 491828 12) E) (N (el 3072042 [2,9,11] [2953646]) E)))) (N (N (N (N (el 49259 [0,1,2,3,4,15,6,7,12,13,22] [960430,1091504,2951060,3057493,3188649,9348127,9479849]) (e0 7151717)) (N (ec 1327192 [2,22]) E)) (N (N (el 352597 [1,2,3,4,5,6,7,10,27,19,12] [4787684]) E) (N (e1 2658424 2) E))) (N (N (N (el 143381 [0,1,2,3,4,15,6,10,12,22] [591938,608986,698586,732016,961394,994164,2796406]) E) (N (e1 1839157 17) E)) (N (N (el 749659 [0,1,2,3,4,15,6,7,12,22] [831428,962502,2928565,3059651]) E) (N (e0 3789177) E))))) (N (N (N (N (N (ec 28773 [0,1,2,3,4,5,6,7,8,21,14,12,13]) (e0 5497668)) (N (e1 1217109 22) E)) (N (N (ec 284279 [20,9,25]) E) (N (e1 2326588 17) E))) (N (N (N (e1 131180 2) E) (N (e0 1651065) E)) (N (N (e1 659540 9) E) (N (el 3362887 [4,6] [856530]) E)))) (N (N (N (N (el 82517 [2,3,23,16,8,22] [2656356]) (e1 9048132 22)) (N (el 1450353 [0,4,5,6,9,11] [364738,823492,954566]) E)) (N (N (e1 417893 12) E) (N (e0 2925192) E))) (N (N (N (e1 164737 15) E) (N (ef 2024565 6 [2658614]) E)) (N (N (e1 827448 27) E) (N (e1 3977280 22) E)))))))))) (N (N (N (N (N (N (N (N (N (N (el 39 [0,1,2,3,4,5,6,7,10,8,11] [434214,565382,696456,827530,958604,3055758,4759696,5021842,5152916,6873238,7266456,9101466,9363563,11460764]) (e1 3985480 13)) (N (el 852057 [3,7] [2396224]) E)) (N (N (e1 172929 15) E) (N (e0 2035764) E))) (N (N (N (el 83077 [3,6,10,16,8,22] [2459738,2590818]) E) (N (ec 1458468 [0,9]) E)) (N (N (el 426101 [1,5,12] [5312140]) E) (N (ec 2953333 [6,13,22]) E)))) (N (N (N (N (e1 28797 15) (e0 5546042)) (N (el 1232948 [5,6,12,11] [200828]) E)) (N (N (el 290887 [3,6,12,13,22] [462196,6983030]) E) (N (e0 2342997) E))) (N (N (N (el 131366 [15,12,22] [330396,2427462,5016172]) E) (N (el 1658984 [2,3,6] [2953504]) E)) (N (N (e1 663677 15) E) (N (ec 3412072 [2,22]) E))))) (N (N (N (N (N (el 12357 [0,1,2,3,4,5,6,7,10,23,8,9,22,11] [565714,697578,853228,958937,3056731,9364718,11461872]) (e1 4739388 22)) (N (e1 1106244 22) E)) (N (N (el 205145 [2,4,15,5,6,10,17,12] [503066]) E) (N (e0 2167893) E))) (N (N (N (el 102515 [4,15,5,6] [231707,428386,624996,690534,821608,887146,952684,1083758,2394480]) E) (N (ez 1557332 [4755706,4821244]) E)) (N (N (el 504439 [1,2,8,12,29] [462604,986894]) E) (N (e0 3072121) E)))) (N (N (N (N (el 53285 [0,1,2,3,4,15,5,6,7,10,12,9,22] [435066,452570,468956,591100,608112,697211,714715,731101,2794571,4629578,7006174]) (e0 7311992)) (N (e1 1331296 3) E)) (N (N (el 364632 [3,4,6,7,10,12] [428098,560620,2526620,6991282,7253438]) E) (N (el 2707573 [6,13] [725156]) E))) (N (N (N (ef 143451 2 [428474,2394510,2525634]) E) (N (e1 1839669 9) E)) (N (N (el 753989 [0,1,2,3,4,15,6,7,10,16,8,22,11] [4894687]) E) (N (e1 3817845 9) E)))))) (N (N (N (N (N (N (el 4217 [0,1,2,3,4,15,5,6,7,10,8] [172922,181014,189208,566140,582526,598544,615296,697218,713604,729740,746374,959368,975754,992140,1008526,2401168,2417554,2433940,2810774,3072920,4907930,5170076,6857630,9102240,9364386]) (e1 4223012 9)) (N (ec 983348 [3,4,15,6,7,10,16,8,22]) E)) (N (N (el 180841 [4,15,7,9,22] [625856]) E) (N (e0 2122069) E))) (N (N (N (el 94325 [0,1,2,3,4,5,6] [207024,215224,346298,469169,477369,608443,657596,673982,698560,723138,731332,739526,854216,870602,985289,1001675]) E) (N (ec 1527830 [4,12,22]) E)) (N (N (el 462905 [5,12,9] [560840,691914,3214996]) E) (N (ef 3035253 8 [987554]) E)))) (N (N (N (N (ec 41061 [0,1,2,3,4,5,6,7,8,12]) (e0 6459732)) (N (el 1274164 [2,5] [266386]) E)) (N (N (el 328823 [3,5,6,9,13] [428295,855474,986548,2919850,4754473,7409062]) E) (N (ez 2433124 [4755770,6852946]) E))) (N (N (N (el 135799 [0,6,8,12,9] [7146220,7408410]) E) (N (e0 1753662) E)) (N (N (el 725333 [3,4,6,13,22,26] [200538]) E) (N (e1 3698791 1) E))))) (N (N (N (N (N (el 20586 [0,1,2,3,4,6,7,8,9,11] [2663832,2926014,3057116,3122654,4760540,7251071,9364960,9430498,13559268,13624806]) (e0 5230708)) (N (el 1192026 [3,5,6] [2953342,3084415]) E)) (N (N (ec 237621 [15,12,9]) E) (N (ez 2249045 [2658660]) E))) (N (N (N (e1 114817 15) E) (N (e0 1618005) E)) (N (N (el 606298 [1,3,15,6,7,28,12,9] [5024869,6983458]) E) (N (e0 3260490) E)))) (N (N (N (N (el 69989 [0,1,2,3,4,5,6,10,8,24,19,20,12,9,22] [959735,993337,2664168,3057337,4760822,4794424,6858424,7251689]) (e0 7770488)) (N (ez 1384772 [6852794]) E)) (N (N (el 401511 [0,1,2,3,4,15,5,9,11] [699942,732728,855610,871996,962096,994878,2797100,3059254]) E) (N (ec 2797893 [6,12]) E))) (N (N (N (el 148613 [0,4,7,9] [265168,6917038,9079746]) E) (N (e0 1953898) E)) (N (N (e1 783200 3) E) (N (e1 3919989 9) E))))))) (N (N (N (N (N (N (N (el 4149 [0,1,2,3,4,5,6,7,10,16,8,22,11] [213456,565714,598484,614870,958936,991706,2662876,2925022,3056096,5153250,7250404,9363942]) (e1 4092004 22)) (N (el 864389 [2,15,17] [297178,331790,691435,2394349,2429022,2788591]) E)) (N (N (el 176469 [0,1,2,4,15,5,6,7] [404626,412819,477639,502214,575825,698441,731261,2468937,2533712,2657428,2796694,4803656,4869202,4934750,6989896,7022716,9088151]) E) (N (e0 2060356) E))) (N (N (N (ec 90501 [3,6,10,13,22]) E) (N (e1 1483040 15) E)) (N (N (el 443511 [3,6,22] [986717,2919440]) E) (N (el 3018869 [6,11] [856468,987542]) E)))) (N (N (N (N (e1 32893 15) (e0 5824616)) (N (e1 1257608 9) E)) (N (N (el 323653 [0,1,2,3,4,5,6,7,10,9] [216450,960775,994692,3058941]) E) (N (ec 2396228 [0,12]) E))) (N (N (N (el 135242 [0,1,2,3,4,6,12,22] [2435796,2443982,2796272,2829042,2951924,2968310,3058424,3091194,4893436,4926206]) E) (N (e1 1683552 3) E)) (N (N (ec 720950 [2,4,15,12,9]) E) (N (e0 3555400) E))))) (N (N (N (N (N (el 16501 [0,1,2,3,4,15,5,6,7,10,9,13,22] [460028,476502,566574,583000,599386,697493,714076,730462,2557280,2794653,6858082,7120228,9102694]) (e0 4977000)) (N (ez 1180017 [430184]) E)) (N (N (ez 225337 [166106,560462,691077]) E) (N (el 2195556 [0,1,4,15,6,7,10,9,22] [4936012]) E))) (N (N (N (e1 106637 15) E) (N (ef 1590133 9 [6983904,7115000]) E)) (N (N (el 544887 [0,1,14,12,13] [986910]) E) (N (ef 3166328 5 [9376162]) E)))) (N (N (N (N (el 61503 [0,1,2,3,4,5,6,7,8,17] [165912,428064,559138,821284,1091622,1157160,3188759,3254314,9479277]) (e0 7549032)) (N (e1 1364276 22) E)) (N (N (el 385141 [0,1,2,3,4,15,5,10,8,9,13,22] [329795,699910,2428397]) E) (N (el 2749543 [3,6] [856444,987518,2920820]) E))) (N (N (N (el 147541 [3,4,15,10,16,8,22] [6851480]) E) (N (e1 1929253 7) E)) (N (N (el 766341 [0,1,12,9,13,11] [987147,5181450]) E) (N (el 3907688 [3,7,12] [2798060,2830830,2929136,2961906]) E)))))) (N (N (N (N (N (N (el 4935 [0,1,2,3,4,5,6,7,10,23,8] [426450,434666,492044,500252,689240,1090023,2523612,2531834,2786396,3253390,4752356,5284963,7381834,7414688,9479224,11576458]) (e1 4522028 15)) (N (ec 1044804 [10,8,22]) E)) (N (N (ec 196681 [1,2,3,4,5,6,7,8,17,22]) E) (N (ez 2135125 [2658632]) E))) (N (N (N (el 98437 [5,6] [330010,592156,723230,788768,854306,985380,1116454]) E) (N (ez 1552446 [430316,6852846]) E)) (N (N (el 479303 [4,6,8,22] [462580,986870,2952952]) E) (N (ef 3055669 10 [856486]) E)))) (N (N (N (N (el 49211 [0,1,2,3,4,15,6,7,22] [829286,1091432,2392858,2754410,2819948,2926417,3188590,4621324,9217051,9479845]) (e1 6709332 22)) (N (e1 1323092 7) E)) (N (N (ez 341079 [396756,428295,462294,495064,4754691,7146856,9244114]) E) (N (ec 2613303 [4,6,13]) E))) (N (N (N (e1 139401 9) E) (N (el 1794388 [2,12] [2494766]) E)) (N (N (el 733285 [2,4,22] [593810,4984724,5050262,6851650]) E) (N (e1 3780728 12) E))))) (N (N (N (N (N (el 24629 [0,1,2,3,4,5,6,7,8] [927320,943706,960049,976476,992862,1009248,1025634,1042020,3057209]) (e1 5439572 22)) (N (ez 1204524 [168050]) E)) (N (N (ec 266585 [2,4,15,5,6,7,10,12,9,22]) E) (N (e1 2314325 22) E))) (N (N (N (ec 123781 [0,4,7,9]) E) (N (e0 1642823) E)) (N (N (ec 643397 [0,2,3,4,5,6,7,10,16,8,24,14,9,25,22]) E) (N (ez 3330164 [4624837]) E)))) (N (N (N (N (el 78967 [2,3,22] [395340,493632,4884552,5015626]) (e0 8102008)) (N (e0 1409130) E)) (N (N (el 407167 [0,1,2,15,9] [560790,822936]) E) (N (e1 2883640 2) E))) (N (N (N (el 160117 [1,2,4,5,6,7,9] [404498,412692,477641,502218,575827,698443,731263,2534244,2567152,2657302,2673688,5196792,9088026]) E) (N (ef 1991509 6 [2658612]) E)) (N (N (el 802905 [0,1,2,3,4,5,6,7,8] [184370,567692]) E) (N (e1 3952700 22) E)))))))) (N (N (N (N (N (N (N (N (el 99 [0,1,2,3,4,15,5,6,7,10,12,9] [426320,434514,491860,557398,622936,688465,696659,754005,819546,827740,885086,950619,958813,1016159,7004512]) (e1 4042872 12)) (N (el 852365 [15,5] [297178,364614,428268,495694,561232,692306,1085524,2461768,5312580]) E)) (N (N (el 176215 [4,5,9] [592277,724076,789614,855152,1117298,2427609,2821190,2886734,2952280]) E) (N (el 2044228 [5,6,12,9] [741687,2502974,2511167,2576573,2601148,5067062]) E))) (N (N (N (el 86901 [3,4,15,6,10,8,12,13,22] [2795646]) E) (N (ez 1462612 [2920652,3051726]) E)) (N (N (el 434280 [0,1,2,4,15,5,7,23,9,22] [445895,2796594,4771003,6990080,7122602,7278162]) E) (N (ef 2998392 5 [5181840]) E)))) (N (N (N (N (el 29301 [0,1,2,3,4,15,5,6,7,10,8,28,20,12,13] [263866,861884,992958,7136786,7267998]) (e0 5722232)) (N (e1 1246069 4) E)) (N (N (el 300151 [0,6,8,9,13,22] [1117564]) E) (N (e1 2363472 7) E))) (N (N (N (el 135194 [4,6,12] [699078,731586,2558664,2575050,2640588,2706126,2968272,6859474]) E) (N (e0 1667636) E)) (N (N (el 672581 [0,2,4,5,6,7,8,18] [4919112,4935500]) E) (N (ec 3457114 [1,12]) E))))) (N (N (N (N (N (el 13127 [0,1,2,3,4,5,6,7,10,8,17] [426450,443676,460062,1090137,1123616,5284977,7382274,9479440,11576602]) (e1 4878644 5)) (N (ec 1138740 [10,12]) E)) (N (N (el 221237 [3,15,6,12,22] [329812,2427030]) E) (N (e1 2175317 22) E))) (N (N (N (el 103031 [2,4,8] [461214,854432,4589986,4688276]) E) (N (el 1581082 [6,10,12,22] [2691338]) E)) (N (N (e1 532601 9) E) (N (ef 3092548 10 [463292,987582]) E)))) (N (N (N (N (el 57413 [0,1,2,3,4,5,6,10,23,16,8,17,22] [565714,600060,958931,993277,3056729,4760664]) (e0 7417976)) (N (e0 1335609) E)) (N (N (e1 376973 15) E) (N (e0 2728516) E))) (N (N (N (ef 143703 2 [428250,2526070,4623236]) E) (N (e0 1888392) E)) (N (N (ef 758871 3 [528378,561002,593916,626686,2788454,5016679]) E) (N (e0 3879528) E)))))) (N (N (N (N (N (N (el 4469 [0,1,2,3,4,15,5,6,7,10] [476172,541710,582672,607250,615444,697149,713750,730136,746522,975900,1008670,2368264,2466738,2483126,2540576,2663458,2696228,2794534,2810920,2827306,3056684,3073070,3089456,4760034,4776450,4792852,4809264,4907638,4940470,5169874,5202662,6857778,6988852,7250998,9102392,9364538]) (ec 4243514 [2,5,9])) (N (ec 1016100 [3,6,22]) E)) (N (N (el 189541 [2,7] [297952,330966,2395348,2657487,4623560]) E) (N (ec 2134050 [15,8]) E))) (N (N (N (el 94847 [2,15,5,7,9] [428250,493788,559364,4688100,4753656]) E) (N (ec 1544757 [4,7]) E)) (N (N (el 467028 [0,1,2,15,5,6,7,10] [544478,610016,7294616]) E) (N (e0 3039353) E)))) (N (N (N (N (el 45124 [0,1,2,3,4,15,5,6,7,10,12,9] [6874914]) (e0 6591044)) (N (e1 1290528 15) E)) (N (N (el 340026 [0,1,2,3,4,15,7,12,9,22] [568772,2665926,2796729,4893879]) E) (N (el 2539594 [3,7,12,9] [4895051]) E))) (N (N (N (el 139346 [15,6,10,12,13,26] [231508,4655820]) E) (N (e0 1765700) E)) (N (N (ec 729157 [0,1,2,3,4,6,10,8,22,26]) E) (N (ec 3760720 [3,6,12,22]) E))))) (N (N (N (N (N (el 20863 [0,1,2,3,4,15,5,7,10,12,9] [426875,558594,697886,960032,2794486,4752463,6988374,7407054]) (e0 5357908)) (N (ef 1196152 5 [3084398]) E)) (N (N (ec 245835 [0,1,2,3,4,5,6,7,8,12]) E) (N (e1 2273320 17) E))) (N (N (N (el 118901 [0,1,2,3,4,5,6,12,9,11] [723496,739882]) E) (N (el 1626474 [4,12] [2560272]) E)) (N (N (e1 626805 12) E) (N (el 3305594 [0,10] [3084742]) E)))) (N (N (N (N (ec 77899 [2,22]) (e0 7970840)) (N (e1 1392772 9) E)) (N (N (el 402519 [1,2,3,4,6,7,10,8,9,11] [961893,994922,3059069,5156460]) E) (N (e1 2830392 17) E))) (N (N (N (ez 156521 [297972,4885480,6884266]) E) (N (e0 1982553) E)) (N (N (e1 794680 21) E) (N (e1 3932209 22) E))))))) (N (N (N (N (N (N (N (el 4197 [0,1,2,3,4,5,6,7,8,18,14,9,11] [721598,926400,991938]) (e0 4149321)) (N (ec 909397 [0,1,2,3,4,5,6,10,8,19,20]) E)) (N (N (el 177013 [0,1,4,5,6,7,18,9,11] [273586,470196,4934760,6826662,6925250]) E) (N (ez 2076980 [2658612]) E))) (N (N (N (el 94234 [0,2,4,5,17,9] [960670,993440,2967714]) E) (N (ef 1503348 15 [2396368,2789588]) E)) (N (N (el 454725 [2,15,5,10,22] [855746,6982719,9506408]) E) (N (ef 3023221 1 [2363808]) E)))) (N (N (N (N (el 37239 [0,1,2,3,4,15,5,7,8,14,9] [697158,730842,853724,870110,1091220,1124064,2794500,3188378]) (e0 6275412)) (N (ef 1269860 5 [5181576]) E)) (N (N (el 323909 [1,2,3,4,5,6,7] [960779,994712,2469256,3058945,7253402]) E) (N (ec 2429012 [2,4,22]) E))) (N (N (N (el 135287 [0,5,6,9,11] [461318,592674,723748,789286,854824,985898,1116972,2951928,3214108]) E) (N (el 1712264 [6,8] [7147798,7278884]) E)) (N (N (el 725093 [5,6,17] [592099,723170,790370,855908,986982,1118055,4984680,5050218]) E) (N (e0 3670120) E))))) (N (N (N (N (N (el 17783 [0,1,2,3,4,15,6,7,10,28,20,9,13] [722316,2786684,7251272,7382356]) (e1 5111900 3)) (N (e0 1188404) E)) (N (N (e1 229452 7) E) (N (ec 2220054 [4,15]) E))) (N (N (N (el 107397 [2,4,7] [2361840,2460102,9079276]) E) (N (e1 1605668 17) E)) (N (N (ec 557397 [1,2,3,4,5,6,7,23,8,19,12]) E) (N (e0 3244120) E)))) (N (N (N (N (el 65657 [0,1,2,3,4,15,5,6,10,18,9,11] [567342,698416,2680784,4760692,6989874]) (e1 7635000 34)) (N (e1 1380472 12) E)) (N (N (e1 393345 15) E) (N (ez 2769000 [7278976]) E))) (N (N (N (el 148022 [4,15,7] [2657220]) E) (N (e0 1937474) E)) (N (N (el 782390 [5,6] [200718,331792,462865,790546,856084,987158,1118231]) E) (N (e0 3911765) E)))))) (N (N (N (N (N (N (el 8261 [0,1,2,3,4,5,6,7,8,9] [959659,1025236,3056825]) (e0 4571448)) (N (ec 1085492 [4,15,10]) E)) (N (N (e1 204832 15) E) (N (ef 2146886 6 [2527531]) E))) (N (N (N (el 99205 [4,5,17,9] [264532,2361686,2459950,2656592,5310742]) E) (N (e1 1556548 17) E)) (N (N (el 487476 [0,1,2,3,4,15,5,6,7,10,22] [724738]) E) (N (ef 3067973 10 [987564]) E)))) (N (N (N (N (el 49255 [0,1,2,3,4,15,6,7,28,12,13] [591512,788382,853920,993186,1124260,2951056,2967442,3057491,3090287,3188646,3221416,9348125,9479847]) (e1 7147877 3)) (N (el 1327186 [6,13] [233636]) E)) (N (N (el 348533 [3,4,15,6,7,10,16,12,13] [2796559,6991274,7253432]) E) (N (ec 2634580 [3,6,12,13,22]) E))) (N (N (N (el 140389 [2,6,12] [363348,2460504,2657126,4983662,5049166,5180254]) E) (N (e1 1823061 2) E)) (N (N (el 749627 [0,1,2,3,4,15,6,7,22] [700342,962488,2797489,3059642]) E) (N (e0 3789161) E))))) (N (N (N (N (N (el 28761 [0,1,2,3,4,5,6,7,8,12,29,13,30] [697984,730750,960130,976516,992449,2401714,5170822,6989448]) (e0 5468234)) (N (ef 1216821 5 [4591748]) E)) (N (N (ec 279397 [0,1,2,3,4,5,6,7,10,8,19,12]) E) (N (e1 2323029 22) E))) (N (N (N (el 131172 [0,1,2,3,4,15,6,7,10] [150112,182450,248418,445028,510566,576104,2394730,2411116,3058194,3090998,4622958,4631152,4754034,9349748]) E) (N (ec 1651050 [1,3]) E)) (N (N (e1 659516 14) E) (N (ef 3354744 8 [2953680]) E)))) (N (N (N (N (el 82309 [3,15,6,10,13,22] [2459734]) (e0 8523896)) (N (e1 1433632 12) E)) (N (N (el 413817 [1,15,5,12] [5312134]) E) (N (el 2921096 [6,11] [233866,2953606,3084680]) E))) (N (N (N (el 164237 [2,4,9] [297847,429062,691174,2526262,2722708]) E) (N (e1 2023797 4) E)) (N (N (e1 823352 17) E) (N (e0 3973221) E))))))))) (N (N (N (N (N (N (N (N (N (el 71 [0,1,2,3,4,5,6,7,8,12,13] [565384,598260,696510,729334,745720,827642,860412,876798,925952,958722,991492,1024262,2810066,2941192,3055882,3072268,3088654,4759824,4890898,5021972,5153046,9101592,9232666,11460723,13558044]) (e1 4042776 22)) (N (el 852105 [2,15,7,17] [299078,724187,2394319,2429000,2788575]) E)) (N (N (el 176194 [0,1,3,4,15,6,7,10,22,11] [240716,2796622,2829392,4697014,4893778,9088084]) E) (N (el 2040189 [2,23,11] [692536]) E))) (N (N (N (el 86133 [0,1,2,3,4,15,6,10,8,22,11] [329794,698472,2426992,2795634]) E) (N (el 1462316 [0,5] [856258]) E)) (N (N (e1 430221 15) E) (N (ec 2990712 [1,27,9]) E)))) (N (N (N (N (ec 29049 [0,1,2,3,4,15,5,6,7,10,8,28,12]) (e1 5620340 9)) (N (el 1245553 [2,4,5,6,9,11] [430184,823432,954506]) E)) (N (N (ec 291701 [0,2,3,15,5,7,10,8,24,9,25,13,22]) E) (N (ef 2347384 37 [2625898]) E))) (N (N (N (el 131941 [2,4,5,6] [330414,2394748,4885168,5016152,5081778,5147274,5278388,9079466]) E) (N (e1 1663061 22) E)) (N (N (el 671832 [0,1,2,3,4,15,5,6,7,22] [585540,847686,2682589,2944811,6860616]) E) (N (e0 3420280) E))))) (N (N (N (N (N (el 12661 [0,1,2,3,4,15,5,6,7,10,8,13,22,11] [476420,582918,713992,2524426,2794531,4760034,6989068,7251214,9102608]) (e0 4751480)) (N (e1 1122356 22) E)) (N (N (el 209293 [2,15,23,22] [560416,691490,822564,2788492,6982670]) E) (N (ec 2171253 [9,25]) E))) (N (N (N (ef 102523 15 [428442,2394482,2460060,2525344]) E) (N (e1 1565797 2) E)) (N (N (el 528472 [0,1,2,3,4,15,5,6,7,28,12,13] [4910758,5041940]) E) (N (ez 3080264 [430516]) E)))) (N (N (N (N (el 53365 [0,1,2,3,4,15,5,6,7,10,8,14,9] [6874657,7268069]) (e0 7381624)) (N (el 1335334 [2,5] [2396322]) E)) (N (N (el 376906 [2,4,5,17,9] [5180910]) E) (N (e0 2715737) E))) (N (N (N (el 143483 [0,9] [428594]) E) (N (ec 1867850 [4,22]) E)) (N (N (el 757863 [1,3,7,28,12,22] [724976]) E) (N (el 3838056 [0,6,16] [5181928]) E)))))) (N (N (N (N (N (N (el 4421 [0,1,2,3,4,5,6,7,9,11] [869340,959293,975838,992224,1041378,2466480,2663396,3056614,4776448,4809262,5137166,5170032,5202878,5235668,6857704,7250922,9364460,9429998]) (e1 4239420 7)) (N (el 1007908 [2,5] [331874]) E)) (N (N (el 184630 [1,4,15,6,7,10,12,9] [698617,2796599,4893898]) E) (N (ec 2126165 [4,5]) E))) (N (N (N (e1 94333 15) E) (N (ec 1528101 [4,22]) E)) (N (N (el 466996 [0,1,2,3,4,15,5,6,10,22] [470732,478926,855760,872146,986836,1003222]) E) (N (e1 3035765 7) E)))) (N (N (N (N (el 42623 [0,1,2,3,4,15,5,6,7,10] [427802]) (e1 6557760 34)) (N (el 1286192 [2,5] [364692,2527382,2658456]) E)) (N (N (el 336741 [0,1,3,4,5,6,7,10,21,14,19,9] [3059130]) E) (N (e1 2437188 2) E))) (N (N (N (el 139306 [4,15,12] [2689848]) E) (N (e1 1754197 2) E)) (N (N (el 725349 [2,4,5,6] [461570,790410,855901,1118069,2460419,4984715,5050204,5181300]) E) (N (ec 3723368 [0,1,2,4,15,5,6,7]) E))))) (N (N (N (N (N (e1 20605 15) (e0 5284180)) (N (ef 1196104 2 [2429046]) E)) (N (N (e1 237644 7) E) (N (ez 2261588 [4624740]) E))) (N (N (N (el 115081 [0,5,9] [363038,5179902]) E) (N (ec 1618250 [4,12,22]) E)) (N (N (ec 614725 [0,3,4,5,6,10,16,8,14,22]) E) (N (ec 3305530 [1,22]) E)))) (N (N (N (N (ec 73817 [0,1,2,3,4,5,6,10,8,21,13]) (e0 7819288)) (N (e1 1392724 7) E)) (N (N (el 401775 [1,2,3,4,15,7,10,9] [699992,962138]) E) (N (ec 2810712 [5,9,11]) E))) (N (N (N (ef 155749 2 [297178,560084,691168,2394346,2657258,2788332]) E) (N (e1 1974304 17) E)) (N (N (el 786489 [0,4,9,11] [561188,823334,2953218]) E) (N (e0 3924041) E))))))) (N (N (N (N (N (N (N (el 4165 [0,1,2,3,4,5,6,7,8,17,9] [213558,565714,582200,598586,614972,852542,868928,926274,942660,959046,975432,991818,1008204,1024590,1040976,3056210,5169748,5235286,9364056,9429594]) (e1 4124728 17)) (N (el 897093 [0,1,2,3,4,15,5,6,18,9,11] [2404388]) E)) (N (N (el 176503 [0,4,15,9] [527522,593016,2788482]) E) (N (e1 2065277 15) E))) (N (N (N (el 90965 [2,3,7] [2459782,9078932]) E) (N (ec 1495144 [0,9]) E)) (N (N (el 450617 [5,9] [166106,560816,691875,3214990]) E) (N (e1 3022961 15) E)))) (N (N (N (N (ec 36969 [0,1,2,3,4,5,6,7,8,14,12,25]) (e0 5968196)) (N (e0 1261892) E)) (N (N (el 323701 [0,1,2,3,4,6,7,10,9,13,22] [216458,591938,609676,698631,732558,2796581]) E) (N (ec 2408533 [5,11]) E))) (N (N (N (el 135259 [2,6] [461250,2394298,2886366,2951922,3083028,4623126]) E) (N (ec 1696053 [2,5]) E)) (N (N (e1 725072 3) E) (N (e0 3666020) E))))) (N (N (N (N (N (el 17021 [0,1,2,3,4,15,5,6,7,12,9] [296188,427361,566597,828753,2393440,2524526,4891972,5154128,9102718]) (e0 5095452)) (N (ef 1180277 0 [397416]) E)) (N (N (el 229436 [0,1,2,3,4,15,5,6,10] [314216,4631744]) E) (N (e1 2203733 22) E))) (N (N (N (ef 106893 15 [297444,2460100]) E) (N (e1 1601576 9) E)) (N (N (el 548970 [1,3,15,7,12,22] [6917910]) E) (N (ef 3207288 5 [9376164]) E)))) (N (N (N (N (el 65593 [0,1,2,3,4,5,6,7,8,18,9,11] [2557720]) (e0 7590248)) (N (e0 1372996) E)) (N (N (ec 386423 [3,20,9,13,22]) E) (N (ez 2760789 [856441,7278968]) E))) (N (N (N (el 147756 [1,4,15,6,7,10] [166548,175012,306086,2796446,2828740,4893608,4926378,6990764,7252910]) E) (N (ez 1930101 [4624648]) E)) (N (N (el 774261 [1,2,12,13,22] [593932,5181430]) E) (N (el 3907925 [2,4] [987629,5050860]) E)))))) (N (N (N (N (N (N (el 5239 [0,1,2,3,4,15,5,6,7] [394402,402596,410789,426566,434790,442983,459405,468134,475813,492172,500388,509095,557885,566079,574317,598935,623784,639955,688723,705141,827879,860697,2523730,2531956,2655206,2663416,2786414,2925667,4621116,4629356,4637502,4654249,4662226,4703126,4752422,4760617,4768808,4793425,4834384,4883431,4899833,7119334,7152152,11314274]) (e0 4538488)) (N (e1 1065597 11) E)) (N (N (el 196981 [2,4,5,6,17] [404724,412917,477645,502220,576359,642035,2534246,2567154,2657428,2665627,2673818,2698447,2739406,4893942,4926712]) E) (N (e1 2142304 3) E))) (N (N (N (el 98693 [2,15,5,6] [461004,788798,854336,985410,2361668,2459946,2525510,5310736]) E) (N (el 1552948 [1,4,15,6,7,10,22] [610550,2543856,7123192]) E)) (N (N (e1 479333 12) E) (N (e0 3063865) E)))) (N (N (N (N (el 49224 [0,1,2,3,4,15,5,6,7] [189783,320854,452468,485238,583541,616311,714616,747386,845689,878459,2418544,2548796,2680342,2811564,2942684,4646423,4777021,4908765,5039789,6875004,7137150,9103231,11331456]) (e0 6934884)) (N (e1 1323140 9) E)) (N (N (el 344376 [0,1,2,3,4,15,5,6,7,10,8,12,9,22] [2551262,2682335,6876642]) E) (N (e1 2625592 17) E))) (N (N (N (el 139881 [15,12,22] [494440]) E) (N (e1 1815136 3) E)) (N (N (ec 733573 [18,22,26]) E) (N (e0 3785320) E))))) (N (N (N (N (N (el 25471 [0,1,2,3,4,15,5,6,7,10] [427638]) (e0 5452612)) (N (e1 1212500 2) E)) (N (N (el 275575 [5,6,13,22,11] [986466,4754461,7408990]) E) (N (e0 2318420) E))) (N (N (N (e1 131132 7) E) (N (ec 1646677 [2,5,11]) E)) (N (N (e1 655408 28) E) (N (e0 3334264) E)))) (N (N (N (N (el 82053 [6,10,13,26] [460884]) (e0 8204633)) (N (e0 1418105) E)) (N (N (el 413770 [2,5,9,22,26] [2690718,5312126]) E) (N (ec 2912888 [2,17,33,9]) E))) (N (N (N (el 160895 [2,3,4,11] [429092,560166,822312,2657294]) E) (N (ec 2002992 [2,15]) E)) (N (N (el 807032 [0,1,2,3,4,15,6,7,10,8,9] [6876847,7139113]) E) (N (ec 3956856 [3,7,12]) E)))))))) (N (N (N (N (N (N (N (N (el 311 [0,1,2,3,4,5,6,17] [401822,434222,450976,467362,500132,516518,565654,582056,598442,926111,958511,975265,991651,1024421,1040807,2531424,5152865,6873238,6906032,7233888,7266686,7299474,7332243,9363607,9429169]) (e1 4059172 2)) (N (e1 856189 15) E)) (N (N (ec 176251 [0,4,7,9]) E) (N (e1 2048373 22) E))) (N (N (N (el 90245 [3,15,10,22] [460884,2459784,2558090]) E) (N (e1 1470508 34) E)) (N (N (el 438357 [4,5,6,17,12,9] [559322,986798,2395110,6982859,9506392]) E) (N (e1 3010941 15) E)))) (N (N (N (N (el 32820 [0,1,2,3,4,5,7,8,12,9] [583362,2926276,9233619]) (e1 5750904 12)) (N (e1 1257560 2) E)) (N (N (e1 307256 17) E) (N (e1 2383976 6) E))) (N (N (N (el 135234 [0,1,2,3,4,6,10,8,12,13,26,11] [231490,240346,2443980,2796252,2829022,4893408]) E) (N (e0 1675641) E)) (N (N (ec 692309 [0,1,2,3,4,15,5,6,7,10,12,9]) E) (N (e1 3485816 1) E))))) (N (N (N (N (N (el 16437 [0,1,2,3,4,5,6,7,10,9] [566566,582952,599338,615724,959790,976176,992562,1008948,2663734,3056952,5154106,9364641]) (e0 4919588)) (N (e1 1159285 5) E)) (N (N (el 221268 [1,3,4,15,6,7,8,12,11] [699644,2590840,2599066,2796836,3058986,9088040]) E) (N (el 2183284 [1,2,4,15,6,7,10,9,22] [4936010]) E))) (N (N (N (el 106581 [2,3,16,8,22] [6850990]) E) (N (ef 1589274 4 [594140]) E)) (N (N (ec 541829 [0,7,14]) E) (N (el 3101000 [5,9] [5181872]) E)))) (N (N (N (N (e1 61489 7) (e0 7438456)) (N (e1 1355832 22) E)) (N (N (ec 381045 [0,1,2,3,4,5,6,9,11]) E) (N (e0 2740298) E))) (N (N (N (el 144197 [3,4,6,7,10,8,22] [4639442]) E) (N (e0 1917500) E)) (N (N (e1 766048 3) E) (N (e1 3903564 22) E)))))) (N (N (N (N (N (N (el 4661 [0,1,2,3,4,5,6,7,10,16,8,11] [566360,959578,2466346,2663516,2925662,3056736,4776570,4809402,5153608,5170036,5186462,5202882,6857704,7250994,9364578]) (e1 4272424 22)) (N (e1 1024056 22) E)) (N (N (ec 192869 [0,2,3,4,5,6,7,16,8,24,9,25,22]) E) (N (ez 2134613 [2789704]) E))) (N (N (N (ec 98393 [2,3,9,22]) E) (N (ef 1545333 0 [9081056]) E)) (N (N (el 471161 [0,1,2,3,4,5,6,7,8] [175785,183989]) E) (N (e0 3051577) E)))) (N (N (N (N (e1 45164 1) (e1 6594633 22)) (N (e1 1302816 15) E)) (N (N (el 340057 [0,1,2,3,4,15,5,7,10,13,22] [699856]) E) (N (ef 2581607 6 [987506]) E))) (N (N (N (el 139369 [2,15,12] [723796,2394316,2657110,2788184]) E) (N (e1 1770597 2) E)) (N (N (ec 729177 [0,1,2,3,4,15,5,6,7,22]) E) (N (ec 3772789 [4,25]) E))))) (N (N (N (N (N (el 21375 [0,1,2,3,4,15,5,6,7,10,9] [427568,435762,493108,566838,689720,4883459,7407060,7423458]) (e0 5415749)) (N (e1 1200213 22) E)) (N (N (ec 254297 [2,4,15,5,6,7,10,9]) E) (N (e0 2310232) E))) (N (N (N (el 123265 [0,4,15,5,6,9,11] [821812,952886,1083960,2394672,2787898]) E) (N (e0 1634649) E)) (N (N (ec 634986 [0,3,15,14,9]) E) (N (ez 3321922 [692680,954826]) E)))) (N (N (N (N (ec 78181 [0,2,3,4,5,6,7,10,16,8,24,9,25,22]) (e0 8052856)) (N (e0 1396856) E)) (N (N (el 405885 [1,2,3,4,15,10,9] [298632,700042,962188]) E) (N (el 2839384 [6,12,13] [233860]) E))) (N (N (N (el 159863 [2,4,5,9,11] [461820,592894,723968,855042,3214326]) E) (N (e0 1986648) E)) (N (N (ef 799575 10 [397356,428250,462894,495630,2788552,4754633,7146856]) E) (N (e1 3936853 13) E))))))) (N (N (N (N (N (N (N (e1 4209 15) (ec 4202872 [2,17])) (N (ec 958581 [2,6,13,22]) E)) (N (N (el 180314 [3,4,15,7,22] [6917006]) E) (N (e1 2097478 6) E))) (N (N (N (ec 94312 [0,1,2,3,4,5,6,7,8,17,9,11]) E) (N (e0 1507432) E)) (N (N (e1 459316 12) E) (N (e0 3027065) E)))) (N (N (N (N (el 37991 [0,1,2,3,4,5,6,7,10,8,14,19,12,9,25,11] [1090811,1124076,2590416,2787048,3187993,5285611]) (e0 6328900)) (N (e1 1273952 3) E)) (N (N (el 327784 [0,1,2,3,4,6,7,10,9] [6860192,6991266,7187876,9235878,11333032]) E) (N (e1 2429020 3) E))) (N (N (N (el 135511 [2,15,6,10,12] [493851,4688159,7146214]) E) (N (ez 1737301 [2658602]) E)) (N (N (e1 725125 9) E) (N (el 3690552 [0,22] [561624]) E))))) (N (N (N (N (N (el 20565 [0,1,2,3,4,5,6,7,8,27,12,13] [853424]) (e1 5185624 22)) (N (el 1192018 [5,6,13,11] [233596]) E)) (N (N (el 233521 [0,4,9,11] [822610,6851744]) E) (N (e1 2228292 12) E))) (N (N (N (ec 110680 [0,1,2,3,4,5,6,7,8,18,9,11]) E) (N (e1 1610332 7) E)) (N (N (e1 569465 9) E) (N (e1 3248200 2) E)))) (N (N (N (N (el 69721 [0,1,2,3,4,5,6,10,8,19,20] [567354,6858420]) (e0 7647352)) (N (ez 1381204 [2953394]) E)) (N (N (el 393592 [1,2,3,4,6,27,36,9,11] [2706958,3026460,3059224,3091994,3124766,9350417]) E) (N (e0 2789480) E))) (N (N (N (el 148325 [2,4,7] [2460106,6917032,9079752]) E) (N (e1 1938245 22) E)) (N (N (ez 782398 [166106,299038,430111]) E) (N (e1 3915897 9) E)))))) (N (N (N (N (N (N (e1 8317 15) (e0 4600168)) (N (e0 1093973) E)) (N (N (el 204906 [1,4,15,7,12,13] [2927886,3058960,4697030,5024761,9219106,9251904]) E) (N (e1 2154600 4) E))) (N (N (N (ec 102469 [0,1,2,3,4,5,6,7,10,16,8,22]) E) (N (ez 1556812 [430316,6852860]) E)) (N (N (ec 499801 [0,1,2,3,4,5,6,7,10,8,12,29,13]) E) (N (el 3072074 [2,9] [2691504]) E)))) (N (N (N (N (el 50007 [0,1,2,3,4,15,5,6,7,17] [395186,403380,426566,436022,444342,460728,468922,493406,501692,509886,565844,600000,696917,731073,829378,862148,2655284,2663496,4883509,4891721,7079878,7096178,7120130,7145340,7153546,7161750,9217296,9250164,11314449,11347317]) (e0 7155832)) (N (el 1327194 [3,6] [2953382]) E)) (N (N (ez 357463 [6983016,7114195,9080274,9211362]) E) (N (e1 2678840 2) E))) (N (N (N (ec 143431 [3,22]) E) (N (e1 1839193 22) E)) (N (N (el 750439 [0,1,2,4,15,5,6,7,9] [405456,470994,733140]) E) (N (ec 3805212 [3,6,13,22]) E))))) (N (N (N (N (N (ec 28779 [0,1,2,3,4,5,6,7,12,9,29,13]) (e0 5505860)) (N (e1 1220656 15) E)) (N (N (ec 286778 [0,1,2,3,4,10,8,13,22,26]) E) (N (e1 2330684 17) E))) (N (N (N (el 131204 [0,1,2,3,4,15,6,7,10,9] [4622994]) E) (N (e0 1651289) E)) (N (N (el 663667 [0,4,15,5,6,7,8] [233165,692012,823086,954160,1085234,2395956,4624095]) E) (N (e0 3363159) E)))) (N (N (N (N (el 82565 [3,10,16,8,22] [2656358]) (e0 9396328)) (N (e0 1450361) E)) (N (N (ec 418151 [1,12]) E) (N (e1 2933117 15) E))) (N (N (N (el 164997 [5,6,7,9] [2657305,5311536]) E) (N (e1 2027592 2) E)) (N (N (ec 835705 [0,1,2,3,4,5,6,10,8,9]) E) (N (e1 3977292 22) E))))))))))))
noncomputable def m251Ck : Nat → Bool := checkNode m251Mask m251Goal (Nat.sub (Nat.shiftLeft 1 m251Pairs.length) 1) sym251 2304 11 m251Ws m251D 12 m251Cuts 6
theorem q70 : tb 0 24 m251Ck = true := by decide +kernel
theorem q71 : tb 24 24 m251Ck = true := by decide +kernel
theorem q72 : tb 48 24 m251Ck = true := by decide +kernel
theorem q73 : tb 72 24 m251Ck = true := by decide +kernel
theorem q74 : tb 96 24 m251Ck = true := by decide +kernel
theorem q75 : tb 120 24 m251Ck = true := by decide +kernel
theorem q76 : tb 144 24 m251Ck = true := by decide +kernel
theorem q77 : tb 168 24 m251Ck = true := by decide +kernel
theorem q78 : tb 192 24 m251Ck = true := by decide +kernel
theorem q79 : tb 216 24 m251Ck = true := by decide +kernel
theorem q80 : tb 240 24 m251Ck = true := by decide +kernel
theorem q81 : tb 264 24 m251Ck = true := by decide +kernel
theorem q82 : tb 288 24 m251Ck = true := by decide +kernel
theorem q83 : tb 312 24 m251Ck = true := by decide +kernel
theorem q84 : tb 336 24 m251Ck = true := by decide +kernel
theorem q85 : tb 360 24 m251Ck = true := by decide +kernel
theorem q86 : tb 384 24 m251Ck = true := by decide +kernel
theorem q87 : tb 408 24 m251Ck = true := by decide +kernel
theorem q88 : tb 432 24 m251Ck = true := by decide +kernel
theorem q89 : tb 456 24 m251Ck = true := by decide +kernel
theorem q90 : tb 480 24 m251Ck = true := by decide +kernel
theorem q91 : tb 504 24 m251Ck = true := by decide +kernel
theorem q92 : tb 528 24 m251Ck = true := by decide +kernel
theorem q93 : tb 552 24 m251Ck = true := by decide +kernel
theorem q94 : tb 576 24 m251Ck = true := by decide +kernel
theorem q95 : tb 600 24 m251Ck = true := by decide +kernel
theorem q96 : tb 624 24 m251Ck = true := by decide +kernel
theorem q97 : tb 648 24 m251Ck = true := by decide +kernel
theorem q98 : tb 672 24 m251Ck = true := by decide +kernel
theorem q99 : tb 696 24 m251Ck = true := by decide +kernel
theorem q100 : tb 720 24 m251Ck = true := by decide +kernel
theorem q101 : tb 744 24 m251Ck = true := by decide +kernel
theorem q102 : tb 768 24 m251Ck = true := by decide +kernel
theorem q103 : tb 792 24 m251Ck = true := by decide +kernel
theorem q104 : tb 816 24 m251Ck = true := by decide +kernel
theorem q105 : tb 840 24 m251Ck = true := by decide +kernel
theorem q106 : tb 864 24 m251Ck = true := by decide +kernel
theorem q107 : tb 888 24 m251Ck = true := by decide +kernel
theorem q108 : tb 912 24 m251Ck = true := by decide +kernel
theorem q109 : tb 936 24 m251Ck = true := by decide +kernel
theorem q110 : tb 960 24 m251Ck = true := by decide +kernel
theorem q111 : tb 984 24 m251Ck = true := by decide +kernel
theorem q112 : tb 1008 24 m251Ck = true := by decide +kernel
theorem q113 : tb 1032 24 m251Ck = true := by decide +kernel
theorem q114 : tb 1056 24 m251Ck = true := by decide +kernel
theorem q115 : tb 1080 24 m251Ck = true := by decide +kernel
theorem q116 : tb 1104 24 m251Ck = true := by decide +kernel
theorem q117 : tb 1128 24 m251Ck = true := by decide +kernel
theorem q118 : tb 1152 24 m251Ck = true := by decide +kernel
theorem q119 : tb 1176 24 m251Ck = true := by decide +kernel
theorem q120 : tb 1200 24 m251Ck = true := by decide +kernel
theorem q121 : tb 1224 24 m251Ck = true := by decide +kernel
theorem q122 : tb 1248 24 m251Ck = true := by decide +kernel
theorem q123 : tb 1272 24 m251Ck = true := by decide +kernel
theorem q124 : tb 1296 24 m251Ck = true := by decide +kernel
theorem q125 : tb 1320 24 m251Ck = true := by decide +kernel
theorem q126 : tb 1344 24 m251Ck = true := by decide +kernel
theorem q127 : tb 1368 24 m251Ck = true := by decide +kernel
theorem q128 : tb 1392 24 m251Ck = true := by decide +kernel
theorem q129 : tb 1416 24 m251Ck = true := by decide +kernel
theorem q130 : tb 1440 24 m251Ck = true := by decide +kernel
theorem q131 : tb 1464 24 m251Ck = true := by decide +kernel
theorem q132 : tb 1488 24 m251Ck = true := by decide +kernel
theorem q133 : tb 1512 24 m251Ck = true := by decide +kernel
theorem q134 : tb 1536 24 m251Ck = true := by decide +kernel
theorem q135 : tb 1560 24 m251Ck = true := by decide +kernel
theorem q136 : tb 1584 24 m251Ck = true := by decide +kernel
theorem q137 : tb 1608 24 m251Ck = true := by decide +kernel
theorem q138 : tb 1632 24 m251Ck = true := by decide +kernel
theorem q139 : tb 1656 24 m251Ck = true := by decide +kernel
theorem q140 : tb 1680 24 m251Ck = true := by decide +kernel
theorem q141 : tb 1704 24 m251Ck = true := by decide +kernel
theorem q142 : tb 1728 24 m251Ck = true := by decide +kernel
theorem q143 : tb 1752 24 m251Ck = true := by decide +kernel
theorem q144 : tb 1776 24 m251Ck = true := by decide +kernel
theorem q145 : tb 1800 24 m251Ck = true := by decide +kernel
theorem q146 : tb 1824 24 m251Ck = true := by decide +kernel
theorem q147 : tb 1848 24 m251Ck = true := by decide +kernel
theorem q148 : tb 1872 24 m251Ck = true := by decide +kernel
theorem q149 : tb 1896 24 m251Ck = true := by decide +kernel
theorem q150 : tb 1920 24 m251Ck = true := by decide +kernel
theorem q151 : tb 1944 24 m251Ck = true := by decide +kernel
theorem q152 : tb 1968 24 m251Ck = true := by decide +kernel
theorem q153 : tb 1992 24 m251Ck = true := by decide +kernel
theorem q154 : tb 2016 24 m251Ck = true := by decide +kernel
theorem q155 : tb 2040 24 m251Ck = true := by decide +kernel
theorem q156 : tb 2064 24 m251Ck = true := by decide +kernel
theorem q157 : tb 2088 24 m251Ck = true := by decide +kernel
theorem q158 : tb 2112 24 m251Ck = true := by decide +kernel
theorem q159 : tb 2136 24 m251Ck = true := by decide +kernel
theorem q160 : tb 2160 24 m251Ck = true := by decide +kernel
theorem q161 : tb 2184 24 m251Ck = true := by decide +kernel
theorem q162 : tb 2208 24 m251Ck = true := by decide +kernel
theorem q163 : tb 2232 24 m251Ck = true := by decide +kernel
theorem q164 : tb 2256 24 m251Ck = true := by decide +kernel
theorem q165 : tb 2280 24 m251Ck = true := by decide +kernel
theorem m251All : treeBlock 0 2304 m251Ck = true := (tm 0 1152 1152 (tm 0 576 576 (tm 0 288 288 (tm 0 144 144 (tm 0 72 72 (tm 0 24 48 q70 (tm 24 24 24 q71 q72)) (tm 72 24 48 q73 (tm 96 24 24 q74 q75))) (tm 144 72 72 (tm 144 24 48 q76 (tm 168 24 24 q77 q78)) (tm 216 24 48 q79 (tm 240 24 24 q80 q81)))) (tm 288 144 144 (tm 288 72 72 (tm 288 24 48 q82 (tm 312 24 24 q83 q84)) (tm 360 24 48 q85 (tm 384 24 24 q86 q87))) (tm 432 72 72 (tm 432 24 48 q88 (tm 456 24 24 q89 q90)) (tm 504 24 48 q91 (tm 528 24 24 q92 q93))))) (tm 576 288 288 (tm 576 144 144 (tm 576 72 72 (tm 576 24 48 q94 (tm 600 24 24 q95 q96)) (tm 648 24 48 q97 (tm 672 24 24 q98 q99))) (tm 720 72 72 (tm 720 24 48 q100 (tm 744 24 24 q101 q102)) (tm 792 24 48 q103 (tm 816 24 24 q104 q105)))) (tm 864 144 144 (tm 864 72 72 (tm 864 24 48 q106 (tm 888 24 24 q107 q108)) (tm 936 24 48 q109 (tm 960 24 24 q110 q111))) (tm 1008 72 72 (tm 1008 24 48 q112 (tm 1032 24 24 q113 q114)) (tm 1080 24 48 q115 (tm 1104 24 24 q116 q117)))))) (tm 1152 576 576 (tm 1152 288 288 (tm 1152 144 144 (tm 1152 72 72 (tm 1152 24 48 q118 (tm 1176 24 24 q119 q120)) (tm 1224 24 48 q121 (tm 1248 24 24 q122 q123))) (tm 1296 72 72 (tm 1296 24 48 q124 (tm 1320 24 24 q125 q126)) (tm 1368 24 48 q127 (tm 1392 24 24 q128 q129)))) (tm 1440 144 144 (tm 1440 72 72 (tm 1440 24 48 q130 (tm 1464 24 24 q131 q132)) (tm 1512 24 48 q133 (tm 1536 24 24 q134 q135))) (tm 1584 72 72 (tm 1584 24 48 q136 (tm 1608 24 24 q137 q138)) (tm 1656 24 48 q139 (tm 1680 24 24 q140 q141))))) (tm 1728 288 288 (tm 1728 144 144 (tm 1728 72 72 (tm 1728 24 48 q142 (tm 1752 24 24 q143 q144)) (tm 1800 24 48 q145 (tm 1824 24 24 q146 q147))) (tm 1872 72 72 (tm 1872 24 48 q148 (tm 1896 24 24 q149 q150)) (tm 1944 24 48 q151 (tm 1968 24 24 q152 q153)))) (tm 2016 144 144 (tm 2016 72 72 (tm 2016 24 48 q154 (tm 2040 24 24 q155 q156)) (tm 2088 24 48 q157 (tm 2112 24 24 q158 q159))) (tm 2160 72 72 (tm 2160 24 48 q160 (tm 2184 24 24 q161 q162)) (tm 2232 24 48 q163 (tm 2256 24 24 q164 q165)))))))
theorem m251Low : LowerM m251Mask m251Raw m251Goal 12 := by
  have hraw : m251Ws.map Wire.val = m251Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 40)) m251D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m251Pairs) (sym := sym251) (count := 2304) (rootFuel := 11) (fdepth := 12) (cdepth := 6) (dag := m251D) (cutTree := m251Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) sym251_spec.1 sym251_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m251Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 40)) (defv := (0,[],[])) rfl hnc 12 i
      rw [hraw]; exact m251CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m251All

def m254Mask : Word := 0x5555555555555555555555555555555555555555555555555555555555555555
def m254Goal : Word := 0x5555555555555554555555555554555455555454555550505454545444440000
def m254Raw : List Word := [0x4444444444444444444444444444444444444444444444444444444444444444, 0x5050505050505050505050505050505050505050505050505050505050505050, 0x5500550055005500550055005500550055005500550055005500550055005500, 0x5555000055550000555500005555000055550000555500005555000055550000, 0x5555555500000000555555550000000055555555000000005555555500000000, 0x5555555555555555000000000000000055555555555555550000000000000000, 0x5555555555555555555555555555555500000000000000000000000000000000]
theorem m254Ess : ∀ a ∈ m254Raw, Essential m254Mask m254Goal m254Raw a :=
  checkAllEss_sound (ps := [4114,8228,32904,530,546,1092,642]) (by decide +kernel)
theorem m254Low : LowerM m254Mask m254Raw m254Goal 11 := by
  have hsl : Slice m254Mask m254Raw m254Goal 0x55005500550055005500550055005500550055005500550055005500550055 10 :=
    checkSlice_sound (f := mr 0 1 2 0 4 5 6 7 0) (by unfold Masked; decide +kernel)
      (by unfold Proper Masked; decide +kernel) m246Low (by decide +kernel)
  have h := slice_lift (by unfold Masked; decide +kernel) (by decide +kernel)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) m254Ess hsl
  have hcnt : m254Raw.countP (isConst 0x55005500550055005500550055005500550055005500550055005500550055) = 1 := by decide +kernel
  rw [hcnt] at h; exact h

def m255Mask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def m255Goal : Word := 0xfffffffffffffffefffffffffffefffefffffefefffffafafefefefceeeeaa00
def m255Raw : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
theorem m255Ess : ∀ a ∈ m255Raw, Essential m255Mask m255Goal m255Raw a :=
  checkAllEss_sound (ps := [2057,4114,8228,265,273,546,321,385]) (by decide +kernel)
def m255Pairs : List (Row × Row) := mkPairs [2305,2312,4353,4368,4610,4624,8706,8736,9220,9248,16641,16704,17412,17472,20496,20544,33025,33152,33282,33408,33796,33920,34824,34944,40992,41088,2819,2826,3333,3340,4867,5381,5396,5638,5652,6424,6666,6680,8963,8993,9477,9505,9734,10529,10536,10762,10792,11276,11304,12577,12592,12848,13332,13360,17155,17218,17669,17926,17986,18760,19468,19528,21058,21524,22552,22600,24865,24928,25154,25184,25696,28720,28768,33539,34053,34310,35338,35852,37264,37520,37908,38032,38936,39056,41249,43048,45104,45200,49600,49730,49856,50368,51272,51392,53392,53440,57440,57536,3847,3854,5895,7452,7694,7708,9991,11790,14648,14904,15388,15416,18183,19274,19982,20042,23114,23580,26984,27210,27240,27752,30776,30824,34567,36366,39964,47160,51786,59496]
def m255Ws : List Wire := [mw 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 0x410c53c0110460c09c61bc9fc030c0f 0x40041140010060401420bc0d4010405,mw 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc 0x4c67cbdc06009a3046c864f64c0c00f0 0x4c27c35c02001a1046c024524c040050,mw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 0x1c8b73fc08032c40b7318707b0303300 0x1c0953fc00012c0093108507b0101100,mw 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 0xfbffbeec302c30033801f8383cc00003 0xfbffbee8102430033801f03828400002,mw 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 0x330c3cf0c0cfc183c03e003fc000c03c 0x31083ca040cfc081803c002d00004028,mw 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 0xa3f03f0300f001fc003fffc0030003c0 0xa3d02c01007001ec002f5a8001000280,mw 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 0xc3ffc003ff0001ffffc000000000fc00 0xc2f68003bf00017a6c8000000000a800,mw 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 0xfc000003fffffe000000000003ff0000 0x2ed8ac0000000000002aa0000]
def m255Cuts : BTree CutSpec := (N (N (N (N (N (N (mc m255Raw 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 12) (mc m255Raw 0x550000005500000000000000000000005500000055 5)) (N (mc m255Raw 0x50500000505000000000000000000000505000005050000000000000000 5) E)) (N (N (mc m255Raw 0x555500005555000055550000555500005555000055550000555500005555 8) E) (N (mc m255Raw 0x5555000000000000555500000000000055550000000000005555 5) E))) (N (N (N (mc m255Raw 0xffffffffffffffff0000000000000000ffffffffffffffff 11) E) (N (mc m255Raw 0x5500000055000000550000005500 4) E)) (N (N (mc m255Raw 0xffff0000ffff00000000000000000000ffff0000ffff 9) E) (N (mc m255Raw 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9) E)))) (N (N (N (N (mc m255Raw 0x3333333333333333333333333333333333333333333333333333333333333333 12) (mc m255Raw 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 9)) (N (mc m255Raw 0x55550000555500000000000000000000555500005555 6) E)) (N (N (mc m255Raw 0x55005500550055005500550055005500 7) E) (N (mc m255Raw 0xffffffffffffffff 7) E))) (N (N (N (mc m255Raw 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 11) E) (N (mc m255Raw 0xffff0000000000000000000000000000ffff 6) E)) (N (N (mc m255Raw 0x3030303000000000303030300000000 5) E) (N (mc m255Raw 0xf0f0f0f0 4) E))))) (N (N (N (N (N (mc m255Raw 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 12) (mc m255Raw 0x30003000000000003000300000000 4)) (N (mc m255Raw 0x555555555555555500000000000000005555555555555555 8) E)) (N (N (mc m255Raw 0x55555555000000005555555500000000555555550000000055555555 8) E) (N (mc m255Raw 0xcccc000000000000cccc 4) E))) (N (N (N (mc m255Raw 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff 11) E) (N (mc m255Raw 0x550055000000000055005500 4) E)) (N (N (mc m255Raw 0xffffffff00000000ffffffff 8) E) (N (mc m255Raw 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 9) E)))) (N (N (N (N (mc m255Raw 0xffffffffffffffffffffffffffffffff 11) E) (N (mc m255Raw 0xffffffff000000000000000000000000ffffffff 8) E)) (N (N (mc m255Raw 0xffff000000000000ffff000000000000ffff000000000000ffff 8) E) (N (mc m255Raw 0x5555555500000000000000000000000055555555 5) E))) (N (N (N (mc m255Raw 0x5555555555555555555555555555555555555555555555555555555555555555 11) E) (N (mc m255Raw 0xffff0000ffff0000ffff0000ffff 7) E)) (N (N (mc m255Raw 0x111100001111000000000000000000001111000011110000 5) E) (N (mc m255Raw 0x5500550055005500 4) E))))))
theorem m255CutValid : ∀ ci < 35, ValidCut m255Mask m255Raw m255Goal (btreeGet ⟨0,0,[]⟩ 6 m255Cuts ci) := by
  intro ci hci
  interval_cases ci
  · exact cv 16433288 m247Low (by decide +kernel)
  · exact cv 16434696 m251Low (by decide +kernel)
  · exact cv 15918608 m251Low (by decide +kernel)
  · exact cv 1754760 m127Low (by decide +kernel)
  · exact cv 14861960 m191Low (by decide +kernel)
  · exact cv 16270984 m223Low (by decide +kernel)
  · exact cv 14870096 m191Low (by decide +kernel)
  · exact cv 16434824 m254Low (by decide +kernel)
  · exact cv 14870096 m190Low (by decide +kernel)
  · exact cv 16270984 m222Low (by decide +kernel)
  · exact cv 135970952 m118Low (by decide +kernel)
  · exact cv 14706256 m159Low (by decide +kernel)
  · exact cv 14845576 m175Low (by decide +kernel)
  · exact cv 1590920 m95Low (by decide +kernel)
  · exact cv 538461696 m89Low (by decide +kernel)
  · exact cv 269755911 m89Low (by decide +kernel)
  · exact cv 1075058183 m89Low (by decide +kernel)
  · exact cv 14861960 m190Low (by decide +kernel)
  · exact cv 14844043 m167Low (by decide +kernel)
  · exact cv 14698120 m159Low (by decide +kernel)
  · exact cv 134762888 m86Low (by decide +kernel)
  · exact cv 135807112 m86Low (by decide +kernel)
  · exact cv 14681736 m143Low (by decide +kernel)
  · exact cv 190032 m63Low (by decide +kernel)
  · exact cv 14706256 m158Low (by decide +kernel)
  · exact cv 33579216 m86Low (by decide +kernel)
  · exact cv 181896 m63Low (by decide +kernel)
  · exact cv 14698120 m158Low (by decide +kernel)
  · exact cv 16269448 m215Low (by decide +kernel)
  · exact cv 14868560 m183Low (by decide +kernel)
  · exact cv 67125448 m86Low (by decide +kernel)
  · exact cv 134500624 m86Low (by decide +kernel)
  · exact cv 14844040 m166Low (by decide +kernel)
  · exact cv 538460160 m81Low (by decide +kernel)
  · exact cv 14860424 m183Low (by decide +kernel)
noncomputable def m255D : BTree NodeRec := (N (N (N (N (N (N (N (N (N (N (el 0 [0,1,2,3,4,5,6,7] [581634,712708,843779,974854,9101320,9232394,9363468,11329545,11460622,13557773]) (e1 1880184 10)) (N (el 241733 [0,1,2,3,4,5,6,7,23,20] [983938,1000324,1090175,1106822,1123208]) E)) (N (N (e1 90160 8) E) (N (el 714631 [4,29,16,15] [394216]) E))) (N (N (N (el 25221 [0,1,2,3,4,5,6,7,16,15] [475673,565441,598525,1139215,2466328,2662623,3187155,4759744,4792828,5333518,6856926,7381458,9494866]) E) (N (ec 536646 [0,4,8,16,31]) E)) (N (N (el 149383 [0,1,2,3,4,5,6,7,19,10,14,16] [459588]) E) (N (e1 1036425 14) E)))) (N (N (N (N (el 9863 [0,1,2,3,4,5,6,7,9,14,15] [393542,409928,426126,459082,475468,491854,688436,1220932,1253712,2523284,2785592,4751658,5415250,7512215,7545105,11706683]) E) (N (e1 340024 13) E)) (N (N (e1 127029 14) E) (N (ec 770120 [0,4,6,10,14,16,15]) E))) (N (N (N (ec 57733 [0,1,2,3,4,5,6,7,8,10,16,15]) E) (N (el 610437 [0,1,2,3,4,5,6,7,9,10,16] [525248,7422888]) E)) (N (N (ec 192585 [0,1,2,3,4,5,6,7,14,15]) E) (N (e1 1441856 9) E))))) (N (N (N (N (N (el 4233 [0,1,2,3,4,5,6,7,8,16] [958666,1089740]) E) (N (el 274488 [0,1,2,3,4,5,6,7,13,23] [566166,9495159]) E)) (N (N (el 108695 [0,3,4,5,12,13,9,10,14] [492194,7668384]) E) (N (ec 741448 [0,1,2,3,5,6,7,10,15]) E))) (N (N (N (ec 45177 [0,1,2,3,4,5,6,7,18,14]) E) (N (ec 583559 [4,5,12,9,14]) E)) (N (N (el 163989 [0,1,2,3,4,5,6,7,12,19,11,10,22,14] [525150,590688,598882,9634542,9650962]) E) (N (e1 1331589 34) E)))) (N (N (N (N (el 16519 [0,1,2,3,4,5,6,7,13,11,14,15] [590280,852426]) E) (N (e1 381061 16) E)) (N (N (el 140133 [0,1,2,3,4,5,6,7,29,10,15,20] [606982,1090312,1123082,3056396,7381759,9347750,15786766]) E) (N (e1 852040 22) E))) (N (N (N (el 79751 [0,1,2,3,4,5,6,7,19,8,16,15] [655982]) E) (N (el 696457 [0,1,2,3,4,5,6,7,10,16,15] [5284816]) E)) (N (N (el 213097 [0,1,2,3,4,5,6,7,11,26,14,16,15] [525168]) E) (N (e0 1552440) E)))))) (N (N (N (N (N (N (el 4197 [0,1,2,3,4,5,6,7,11,9,8,14,15] [958602,991372,1089678,1122448,3055762,7381140,15786134]) E) (N (el 249912 [0,1,2,3,4,5,6,7,26,23,15] [1090450,2425714]) E)) (N (N (el 100231 [0,1,2,3,4,5,6,7,9,16] [459410]) E) (N (el 725064 [1,2,3,4,5,6,7,11,10,33] [1090542]) E))) (N (N (N (el 32905 [0,1,2,3,4,5,6,7,14] [1122864]) E) (N (e1 549001 16) E)) (N (N (el 159877 [0,1,2,3,4,5,6,7,12,10,16] [7291656,7398216,9478848]) E) (N (e1 1065096 10) E)))) (N (N (N (N (el 13943 [0,1,2,3,4,5,6,7,11,10,14] [393624,426126,434538,459162,467356,491934,1221024,1253794,2785684,4751660,5415332,7405912,7422306,7512259,7528825,7545217,11706775]) E) (N (e1 361093 14) E)) (N (N (el 131225 [0,1,2,3,4,5,6,7,9,23,14,16,15] [6980290]) E) (N (e1 795289 16) E))) (N (N (N (el 70021 [0,1,2,3,4,5,6,7,17,8,16] [393832,557668,2654826]) E) (N (e1 651316 14) E)) (N (N (ec 204858 [0,1,2,3,4,5,6,7,11,23,14,15]) E) (N (e0 1507973) E))))) (N (N (N (N (N (el 8297 [0,1,2,3,4,5,6,7,9] [958730,1089804,7250190,15786256]) E) (N (e1 295049 16) E)) (N (N (ec 118901 [0,1,2,3,4,5,6,7,12,19,11,9,22,14]) E) (N (el 750229 [0,5,12,10] [2458610]) E))) (N (N (N (el 53637 [0,1,2,3,4,5,6,7,8,16] [1122894,5284432]) E) (N (el 606357 [0,3,5,10,18] [721844,852918]) E)) (N (N (ec 178055 [0,1,2,3,4,5,6,7,11,16,15]) E) (N (e1 1392777 16) E)))) (N (N (N (N (el 24633 [0,1,2,3,4,5,6,7,23,15] [180404,958968,991562,1090042,1122563,7381500,15786465]) E) (N (e1 475204 14) E)) (N (N (el 143513 [0,1,2,3,4,5,6,7,8,10,16,15] [5309180,5415730,9609906]) E) (N (e1 983104 11) E))) (N (N (N (el 86071 [0,2,3,6,13,8,24,25,21,20] [983666,1245812]) E) (N (ec 704649 [1,2,3,4,5,6,7,11,10,15]) E)) (N (N (el 221289 [0,1,2,3,4,5,6,7,12,13] [557946]) E) (N (e1 1609816 33) E))))))) (N (N (N (N (N (N (N (el 1111 [0,1,2,3,4,5,6,7,11] [434192,450644,467030,958552,974938,991324,1089630,1106016,1122402,3186788,4628538,5152870,7266345,7397456,15786088]) E) (N (el 245845 [0,1,2,3,4,5,6,7,23,10,15,20] [1115024]) E)) (N (N (ec 94345 [0,1,2,3,4,5,6,7,9,8,14]) E) (N (el 721029 [0,1,2,3,4,6,7,12,16] [11576232]) E))) (N (N (N (el 28793 [0,1,2,3,4,5,6,7,13,15] [565800,1090090,4759868]) E) (N (e1 548984 10) E)) (N (N (ec 155765 [0,1,2,3,4,5,6,7,10,15]) E) (N (e1 1048713 16) E)))) (N (N (N (N (el 12393 [0,1,2,3,4,5,6,7,10] [958842,1089916,7381374,15786368]) E) (N (e1 352393 14) E)) (N (N (e1 131122 23) E) (N (ec 794773 [0,4,5,7,12,13,9,10]) E))) (N (N (N (ec 61577 [0,1,2,3,4,5,6,7,8,16,15]) E) (N (e1 614432 11) E)) (N (N (ec 196680 [0,1,2,3,4,5,6,7,11,23,15]) E) (N (e1 1499269 16) E))))) (N (N (N (N (N (el 5751 [0,1,2,3,4,5,6,7,19,8,16] [393442,426122,458980,491750,1253608,2523282,4685998,7512258,11706592]) E) (N (ec 278597 [0,1,2,3,4,5,6,7,13,15]) E)) (N (N (el 114807 [0,1,2,3,4,5,6,7,9,8,10,14,20] [590508,721582,1221296,1254066,3318452,7512758,11707064]) E) (N (ec 746133 [0,6,19,10,15]) E))) (N (N (N (ec 51351 [3,4,6,12,17,8,18,16,15]) E) (N (el 603253 [0,1,2,3,5,6,7,11,9,10,14] [1123248,2655148,9479087]) E)) (N (N (ec 176245 [0,1,2,3,4,5,6,7,11,22,16]) E) (N (ef 1388677 4 [656386]) E)))) (N (N (N (N (el 18311 [0,1,2,3,4,5,6,7,11,14,16] [393686,410072,426420,459226,475612,491998,827587,860640,2589116,2785749,2924769,4751826,5022103,7118998,7152048,11313466]) E) (N (e1 426032 8) E)) (N (N (el 143418 [0,1,2,3,4,5,6,7,8,23,10,15,20] [5178100,5284638]) E) (N (e1 954416 11) E))) (N (N (N (el 82073 [0,1,2,3,4,5,6,7,19,8,16] [557680,6914636]) E) (N (ec 700537 [1,2,3,4,5,6,7,10,14,15]) E)) (N (N (ec 217227 [0,1,2,3,4,5,6,7,12,16]) E) (N (e1 1572912 19) E)))))) (N (N (N (N (N (N (el 4215 [0,1,2,3,4,5,6,7,12,17,8,18,16,15] [18014376]) E) (N (ec 258628 [0,1,2,3,4,5,6,7,23,16,15]) E)) (N (N (el 102523 [0,1,2,3,4,5,6,7,13,9,10,14,21] [1221274,3211926]) E) (N (e1 733301 14) E))) (N (N (N (ec 37017 [0,1,2,3,4,5,6,7,9,8,16,15]) E) (N (el 567175 [0,4,12,14] [623524]) E)) (N (N (e1 163888 11) E) (N (ec 1118357 [3,5,7,12,14]) E)))) (N (N (N (N (el 16501 [0,1,2,3,4,5,6,7,12,19,11,22,14] [565386,598450,1089972,1122742,6857008,9494944]) E) (N (e1 364612 16) E)) (N (N (el 136551 [0,1,2,3,4,5,6,7,11,10,14] [434906,467692,1090286,1123056,5284594,7398119]) E) (N (e1 827440 11) E))) (N (N (N (ec 77882 [0,1,2,3,4,5,6,7,8,23,15]) E) (N (e1 675973 16) E)) (N (N (e1 213042 26) E) (N (e1 1527860 14) E))))) (N (N (N (N (N (el 8581 [0,1,2,3,4,5,6,7,9,10,14] [868646,975144,1106217,3055914,3186987,7250220,7381293,15786286]) E) (N (e1 336005 14) E)) (N (N (el 119173 [0,1,2,3,4,5,6,7,11,9,14,15] [393934,2654916]) E) (N (e1 757913 16) E))) (N (N (N (el 57450 [0,1,2,3,4,5,6,7,8,10,15] [3088990]) E) (N (el 607637 [0,4,6,8,10,14,16] [263102]) E)) (N (N (ec 188485 [0,1,2,3,4,5,6,7,11,16,15]) E) (N (e1 1421392 9) E)))) (N (N (N (N (el 24699 [0,1,2,3,4,5,6,7,23,15] [696840,1221130,2392510,2793974,3318284,4620752,6987994,9085326,9609742]) E) (N (e1 516176 8) E)) (N (N (el 145559 [0,3,4,6,8,10,16,15] [394046,590656,2917048,7144220,9765632]) E) (N (ec 1011880 [3,4,12,13,14]) E))) (N (N (N (e1 86078 14) E) (N (el 712825 [1,2,3,4,5,6,7,29,10,14] [1090532]) E)) (N (N (el 229493 [0,1,2,3,4,5,6,7,23,14,15] [721790]) E) (N (e1 1810570 0) E)))))))) (N (N (N (N (N (N (N (N (el 87 [0,1,2,3,4,5,6,7,9] [827408,843822,860208,958481,974895,991281,1089586,1105972,1122358,3186744,5021754,5152827,5283900,13557822,13688896,15786049]) (e1 1925440 9)) (N (ec 241797 [0,1,2,3,4,5,6,7,23,16]) E)) (N (N (e1 90172 8) E) (N (el 718727 [4,12,28] [426986,492524]) E))) (N (N (N (el 28729 [0,1,2,3,4,5,6,7,13] [959006,1090079,15786480]) E) (N (e1 536676 15) E)) (N (N (el 152709 [0,1,2,3,4,5,6,7,13,9,10,21] [738118,1221448,1254218,2458444,5415758,5448528,7512893]) E) (N (el 1048698 [0,1,2,3,4,5,6,7,23,20] [3187706]) E)))) (N (N (N (N (el 12378 [0,1,2,3,4,5,6,7,10] [2924892,3055966,3187037,5153062,7119200,7381345,13558114,13689188,15786339]) E) (N (e1 340030 14) E)) (N (N (el 127125 [0,1,2,3,4,5,6,7,12,9,14,16] [525012,590550,2785984]) E) (N (e1 786488 19) E))) (N (N (N (ec 61496 [0,1,2,3,4,5,6,7,8,23,16,15]) E) (N (el 610628 [0,1,2,3,4,5,6,7,11,9,10,14,15] [263106,2491332,5063596]) E)) (N (N (ec 192602 [0,1,2,3,4,5,6,7,13,11,14,15]) E) (N (e1 1450288 9) E))))) (N (N (N (N (N (el 4725 [0,1,2,3,4,5,6,7,12,8,15] [1089748,2523342,15786198]) E) (N (el 274536 [0,1,2,3,4,5,6,7,13,11,14] [11592317]) E)) (N (N (el 112519 [0,1,2,3,4,5,6,7,12,9] [426660]) E) (N (el 741480 [0,1,2,3,4,5,6,7,11,10,14,15] [5178338]) E))) (N (N (N (el 45193 [0,1,2,3,4,5,6,7,18] [1090104]) E) (N (e1 598068 14) E)) (N (N (el 164501 [0,1,2,3,4,5,6,7,19,11,14,16,15] [9634546,9650966]) E) (N (e1 1359948 21) E)))) (N (N (N (N (el 16773 [0,1,2,3,4,5,6,7,11,14,15] [475600,2662804,3187154,4759700,4792748,6857016,7381460]) E) (N (ec 422005 [0,1,2,3,4,5,6,7,12,17,8,16]) E)) (N (N (el 140935 [0,1,2,3,4,5,6,7,12,10] [557818,819976,1221394,9609988,11707050]) E) (N (ec 893032 [0,1,2,3,4,5,6,7,14]) E))) (N (N (N (e1 81976 19) E) (N (el 696709 [0,1,2,4,6,7,10,16,15] [1123275,5317578]) E)) (N (N (el 217161 [0,1,2,3,4,5,6,7,16] [1123030]) E) (N (e1 1556613 16) E)))))) (N (N (N (N (N (N (el 4201 [0,1,2,3,4,5,6,7,8,16] [958618,1089692,7381150]) E) (N (ec 254021 [0,1,2,3,4,5,6,7,23,16,15]) E)) (N (N (el 102506 [0,1,2,3,4,5,6,7,13,9,10,14] [3089046,3220119,15786648]) E) (N (el 725145 [0,3,11,10,16,15] [7111600]) E))) (N (N (N (ec 33669 [0,1,2,3,4,5,6,7,11,9,8,14,15]) E) (N (ec 562807 [1,2,3,4,5,6,7,12,10]) E)) (N (N (el 160117 [0,1,2,3,4,5,6,7,11,10,14,15] [394072,2654916,7291660]) E) (N (ec 1106069 [3,6,17]) E)))) (N (N (N (N (ec 16439 [0,1,2,3,4,5,6,7,11,9,8,14,15]) E) (N (e1 364598 14) E)) (N (N (el 135255 [0,1,2,3,4,5,6,7,10,15,20] [959194,991964,1090270,1123040,3056354,3187428,15786726]) E) (N (e1 798780 16) E))) (N (N (N (el 73861 [0,1,2,3,4,5,6,7,12,8,16] [4751972]) E) (N (e1 663616 9) E)) (N (N (el 205701 [0,1,2,3,4,5,6,7,19,11,14,15] [263022,2524012]) E) (N (e1 1511561 16) E))))) (N (N (N (N (N (el 8327 [0,1,2,3,4,5,6,7,13,9,10,14] [983324,1122590,1253663,18014496]) E) (N (e1 331896 10) E)) (N (N (ec 118917 [0,1,2,3,4,5,6,7,13,11,9,14,15]) E) (N (e1 757816 15) E))) (N (N (N (ec 57386 [0,1,2,3,4,5,6,8,23,10,15]) E) (N (ec 606613 [3,4,5,6]) E)) (N (N (el 180357 [0,1,2,3,4,5,6,7,22,14,16] [852836,983909]) E) (N (e1 1409112 14) E)))) (N (N (N (N (el 24695 [0,1,2,3,4,5,6,7,13,11,23,14,15] [852478,2425278]) E) (N (e1 491672 10) E)) (N (N (el 143765 [0,1,2,3,4,5,6,7,17,8,10,16,15] [1254185,5448488,9609908]) E) (N (el 995413 [0,1,2,3,4,5,6,7,14] [1115126,1131512]) E))) (N (N (N (e1 86073 15) E) (N (ec 712762 [0,2,3,6,29,8,10,15]) E)) (N (N (ec 225417 [0,1,2,3,4,5,6,7,10,14,15]) E) (N (e1 1794080 19) E))))))) (N (N (N (N (N (N (N (el 1143 [0,1,2,3,4,5,6,7] [434204,450670,467056,483442,958558,974964,991350,1007736,1089642,1106042,1122428,1138814,2531366,3055716,4628558,5283968,7266368,7397421,15786089]) E) (N (ec 246165 [0,1,2,3,4,5,6,7,12,19,23,15]) E)) (N (N (el 98437 [0,1,2,3,4,5,6,7,9,21] [983688,1000074,1090188,1106574,1122960]) E) (N (el 721269 [0,1,2,3,4,5,6,7,11,10,15] [2786220]) E))) (N (N (N (ec 32889 [0,1,2,3,4,5,6,7,14,16,15]) E) (N (e1 548997 16) E)) (N (N (el 159802 [0,1,2,3,4,5,6,7,23,10,15] [7160582,7267142]) E) (N (el 1053077 [0,4,7,16] [459772,5440510]) E)))) (N (N (N (N (el 12409 [0,1,2,3,4,5,6,7,10] [958856,1089929,15786378]) E) (N (ec 356489 [1,2,3,4,5,6,7,19,8]) E)) (N (N (e1 131130 23) E) (N (e1 794924 15) E))) (N (N (N (ec 65669 [0,1,2,3,4,5,6,7,17,8,18,16]) E) (N (e1 618596 14) E)) (N (N (el 200773 [0,1,2,3,4,5,6,7,11,14] [1123174]) E) (N (e1 1503369 14) E))))) (N (N (N (N (N (el 6023 [0,1,2,3,4,5,6,7,8,16] [393472,426146,459010,491780,688340,1253638,2588848,2654416,4620480,4882654,7512214]) E) (N (ec 290904 [0,1,2,3,4,5,6,7,14]) E)) (N (N (el 115573 [0,1,2,3,4,5,6,7,11,9,10,14] [262856,1123018,2523844,5194408,5300921,7381703]) E) (N (el 749640 [0,1,2,3,4,6,7,10,16] [1123252]) E))) (N (N (N (el 53381 [0,1,2,3,4,5,6,7,8,15] [983622,1122888,5284426]) E) (N (e1 606280 23) E)) (N (N (ec 176773 [0,1,2,3,4,5,6,7,11,10,15]) E) (N (el 1388884 [0,2,11,9,10,14,15] [2622468]) E)))) (N (N (N (N (el 22407 [0,1,2,3,4,5,6,7,12,13] [426420,442858,459244,827674,844270,860656,2924862,7119014,9216214,11313367]) E) (N (e1 454704 8) E)) (N (N (el 143497 [0,1,2,3,4,5,6,7,10,14] [1221414,5309176,5415720,11707178]) E) (N (el 954692 [0,1,2,3,4,5,6,7,19,11,14,16,15] [263156,2491381]) E))) (N (N (N (e1 86069 15) E) (N (el 704569 [0,1,2,3,4,5,6,7,11,10] [1090524]) E)) (N (N (e1 221240 13) E) (N (e1 1581116 16) E)))))) (N (N (N (N (N (N (el 4229 [0,1,2,3,4,5,6,7,8,10,15] [344244,852150,868536,958606,991418,1007804,1089698,1122494,3186880,15786178]) E) (N (el 266377 [0,1,2,3,4,5,6,7,13,14,21] [1221524]) E)) (N (N (el 106616 [0,1,2,3,4,5,6,7,9,10,14] [15786656]) E) (N (ec 735111 [0,3,4,10,16]) E))) (N (N (N (ec 41093 [0,1,2,3,4,5,6,7,8,14,16]) E) (N (e1 577596 16) E)) (N (N (el 163897 [0,1,2,3,4,5,6,7,11,10,14,15] [1221468,3212048,3318593,11707227]) E) (N (e0 1232936) E)))) (N (N (N (N (el 16505 [0,1,2,3,4,5,6,7,11] [565688,1089978,3187132,6857010,9494946]) E) (N (ec 374391 [1,2,3,4,5,6,7,10]) E)) (N (N (el 139621 [0,1,2,3,4,5,6,7,29,8,10,15,20] [475892,959222,991992,1090298,1123068,9478910,15786752]) E) (N (e1 843925 16) E))) (N (N (N (ec 77961 [0,1,2,3,4,5,6,7,17,8,23,16]) E) (N (el 696441 [1,2,3,4,5,6,7,10,14] [1090504,5284810]) E)) (N (N (e1 213050 26) E) (N (e1 1532037 16) E))))) (N (N (N (N (N (el 8837 [0,1,2,3,4,5,6,7,13,9,14] [958772,991548,1089845,1122621,15786302]) E) (N (e1 340020 14) E)) (N (N (ec 123001 [0,1,2,3,4,5,6,7,13,9,14,15]) E) (N (ec 759189 [0,4,5,6,10,16,15]) E))) (N (N (N (el 57467 [0,1,2,3,4,5,6,7,8,10,15] [3211870]) E) (N (e1 610354 23) E)) (N (N (ec 188805 [0,1,2,3,4,5,6,7,11,16]) E) (N (e1 1421928 14) E)))) (N (N (N (N (el 24713 [0,1,2,3,4,5,6,7,23,16,15] [180707,565780,598275,1090070,1122779,4759772,6857106,9494864]) E) (N (ec 516248 [3,6,13,14]) E)) (N (N (ec 147589 [0,1,2,3,4,5,6,7,10,16,15]) E) (N (ec 1020281 [0,1,2,3,4,5,6,7,9,23,15]) E))) (N (N (N (el 86167 [1,3,4,6,13,19,14] [459382,655992,721530,1245820,4948570]) E) (N (ec 712841 [1,2,3,4,5,6,7,29,10,16,15]) E)) (N (N (ec 230277 [0,1,2,3,4,5,6,7,17,23,16,15]) E) (N (ec 1847352 [0,16]) E))))))))) (N (N (N (N (N (N (N (N (N (el 71 [0,1,2,3,4,5,6,7,8] [827408,843794,860180,958486,974872,991258,1089564,1105950,1122336,3055650,5152804,5283878,13557800,13688874,15786028]) (e1 1917008 9)) (N (el 241735 [0,1,2,3,4,5,6,7,23,15,20] [1115018,1221249,3318668]) E)) (N (N (ec 90168 [0,1,2,3,4,5,6,7,26,16]) E) (N (ec 716921 [1,2,3,4,5,6,7,28,10,14,15]) E))) (N (N (N (el 28727 [0,1,2,3,4,5,6,7,13,9,10,14] [983578,1122844,1253917,18014702]) E) (N (e1 536648 26) E)) (N (N (el 151689 [0,1,2,3,4,5,6,7,9,10,14,15] [5309186]) E) (N (e1 1048696 10) E)))) (N (N (N (N (el 12376 [0,1,2,3,4,5,6,7,10] [713044,844118,975189,11329880,11460954,13558105]) E) (N (e1 340028 18) E)) (N (N (e1 127036 9) E) (N (e1 774281 16) E))) (N (N (N (el 59271 [0,1,2,3,4,5,6,7,19,8,10,14,16,15] [393826,7537244]) E) (N (el 610441 [0,1,2,3,4,5,6,7,17,9,10,16] [7422890]) E)) (N (N (ec 192600 [0,1,2,3,4,5,6,7,14,15]) E) (N (e1 1450016 11) E))))) (N (N (N (N (N (el 4469 [0,1,2,3,4,5,6,7,17,8,16,15] [2523342,3186896,7381201,15786194]) E) (N (el 274521 [0,1,2,3,4,5,6,7,13,14,25] [1221528]) E)) (N (N (ec 110709 [0,1,2,3,4,5,6,7,9,14,15]) E) (N (ec 741464 [0,1,2,3,5,6,10,14,15]) E))) (N (N (N (el 45189 [0,1,2,3,4,5,6,7,18,16] [983604,1122870]) E) (N (e1 589884 16) E)) (N (N (el 163993 [0,1,2,3,4,5,6,7,11,10,16,15] [6980298,9634544,9650964]) E) (N (e0 1355909) E)))) (N (N (N (N (el 16521 [0,1,2,3,4,5,6,7,11] [565708,1089998,6857014,9494761]) E) (N (e1 397360 19) E)) (N (N (el 140919 [0,1,2,3,4,5,6,7,11,10,14] [557814,590608,1221394,1254164,2917132,4883112,5415702,9609985,13804303]) E) (N (el 852041 [0,3,10,14,16] [3343344]) E))) (N (N (N (e1 81968 19) E) (N (el 696693 [0,1,2,3,5,6,7,10,21,20] [1090514,1123284,5284814,5317584]) E)) (N (N (el 217130 [0,1,2,3,4,5,7,12,26,16] [2556786]) E) (N (e0 1552488) E)))))) (N (N (N (N (N (N (el 4199 [0,1,2,3,4,5,6,7,11,9,8,16,15] [1253528]) E) (N (ec 250009 [0,1,2,3,4,5,6,7,14,15]) E)) (N (N (el 102504 [0,1,2,3,4,5,6,7,10] [13558420]) E) (N (el 725141 [0,3,10,14] [721904]) E))) (N (N (N (ec 33141 [0,1,2,3,4,5,6,7,19,11,9,8,14]) E) (N (e1 557112 26) E)) (N (N (el 159881 [0,1,2,3,4,5,6,7,17,23,10,16] [7291658,7398218,9478850]) E) (N (e1 1081477 14) E)))) (N (N (N (N (el 13959 [0,1,2,3,4,5,6,7,12,10] [426146,434542,491942,688528,1221024,7405914,7422308,7512346,7528838,7545226,9609518]) E) (N (e1 364596 14) E)) (N (N (ec 131733 [0,1,2,3,4,5,6,7,14,16,15]) E) (N (e1 798772 14) E))) (N (N (N (el 71559 [0,1,2,3,4,5,6,7,17,8,16,15] [9208422]) E) (N (e1 651324 13) E)) (N (N (el 205189 [0,1,2,3,4,5,6,7,11,14,16,15] [394088,410474,2655084]) E) (N (e1 1511557 16) E))))) (N (N (N (N (N (el 8325 [0,1,2,3,4,5,6,7,13,9,10,14] [852242,868628,958606,991510,1007896,1089679,1122583,1138969,15786266]) E) (N (e1 307248 26) E)) (N (N (el 118905 [0,1,2,3,4,5,6,7,17,11,9,14,16,15] [9478858]) E) (N (ec 754325 [0,4,6,19,10,16]) E))) (N (N (N (el 55175 [0,1,2,3,4,5,6,7,13,8] [426578,442964,459350,557656,574042]) E) (N (ec 606361 [3,5,8,16]) E)) (N (N (ec 180297 [0,1,2,3,4,5,6,7,22,16]) E) (N (e1 1396852 14) E)))) (N (N (N (N (el 24635 [0,1,2,3,4,5,6,7,23,15] [2392244,4620504,4751756]) E) (N (ec 491640 [0,3,6,13,8]) E)) (N (N (el 143749 [0,1,2,3,4,5,6,7,13,9,8,10,21,20] [459572,1221430,1254200,2458426,4801310,5415728,5448498,11707196]) E) (N (ec 987448 [0,1,2,3,4,5,7,26,23,16]) E))) (N (N (N (e1 86072 13) E) (N (ec 705157 [1,2,3,4,5,6,7,19,11]) E)) (N (N (el 225400 [0,1,2,3,4,5,6,7,23,10,15] [3089276]) E) (N (e1 1671468 14) E))))))) (N (N (N (N (N (N (N (el 1127 [0,1,2,3,4,5,6,7,12] [434198,958552,1089642,2531364,4628517,7266366,7397458,15786092]) E) (N (ec 245909 [0,1,2,3,4,5,6,7,23,16,15]) E)) (N (N (ec 98421 [0,1,2,3,4,5,6,7,9,27,16,15]) E) (N (el 721033 [0,1,2,3,4,6,7,17,10,16] [11576234]) E))) (N (N (N (ec 32885 [0,1,2,3,4,5,6,7,22,18,14]) E) (N (el 548986 [0,1,2,3,4,5,6,7,9,21] [3187616]) E)) (N (N (el 157575 [0,1,2,3,4,5,6,7,12,10] [426838]) E) (N (el 1052808 [0,1,2,3,4,5,6,7,23] [3187710]) E)))) (N (N (N (N (el 12407 [0,1,2,3,4,5,6,7,13,9,10,14,21] [1089898,1122690,1220971,1253763,3080542,3187058,3318131,9478532,9609605,18014598]) E) (N (ec 352901 [0,1,2,3,4,5,6,7,13,19,8,15]) E)) (N (N (el 131128 [0,1,2,3,4,5,6,7,23] [1090264]) E) (N (ec 794777 [0,3,4,5,6,13,10,15]) E))) (N (N (N (ec 65653 [0,1,2,3,4,5,6,7,8,14,16]) E) (N (el 614537 [0,1,2,3,4,5,6,7,17,11,9,10,16] [7422896]) E)) (N (N (ec 196712 [0,1,2,3,4,5,6,7,13,11,14,15]) E) (N (e0 1499781) E))))) (N (N (N (N (N (el 5767 [0,1,2,3,4,5,6,7,13,8] [393450,426126,434412,442606,450800,458994,467188,491766,508152,1220858,1237244,1253630,7512230,7528616,7545010,9609426,11706582]) E) (N (ec 278661 [0,1,2,3,4,5,6,7,13,16]) E)) (N (N (el 115061 [0,1,2,3,4,5,6,7,9,10,14,15] [393914,410300,475838,1090240,1123010,2654916,5194406,5300919,9478854]) E) (N (ec 746901 [4,5,7,14]) E))) (N (N (N (ec 53365 [0,1,2,3,4,5,6,7,8,14]) E) (N (el 604039 [3,4,5] [689064,951218]) E)) (N (N (ec 176261 [0,1,2,3,4,5,6,7,11,15]) E) (N (ec 1388681 [3,4]) E)))) (N (N (N (N (el 20613 [0,1,2,3,4,5,6,7,12,16] [344546,475619,565410,598500,1089972,1122790,1139176,2662800,4759764,6856917,9494852]) E) (N (el 426308 [0,1,2,3,4,5,6,7,17,8,16,15] [263070,2491295]) E)) (N (N (el 143493 [0,1,2,3,4,5,6,7,11,10,14,15] [590624,721698,852772,5309174]) E) (N (e1 954418 26) E))) (N (N (N (e1 86064 13) E) (N (el 702343 [4,5,12,10] [426968,492506,558030]) E)) (N (N (e1 221238 14) E) (N (e1 1581108 14) E)))))) (N (N (N (N (N (N (el 4217 [0,1,2,3,4,5,6,7,8] [958634,1089708,3055790,3186864,15786162]) E) (N (el 266360 [0,1,2,3,4,5,6,7,13,10,14] [15786872]) E)) (N (N (el 104327 [0,1,2,3,4,5,6,7,12,13,9,10,14] [426556,492188,500382,7537300,7553688]) E) (N (ec 734085 [0,1,2,3,4,6,7,17,23,10,16,15]) E))) (N (N (N (ec 41077 [0,1,2,3,4,5,6,7,8,18,16]) E) (N (el 573589 [0,4,6,16] [5440418]) E)) (N (N (e1 163896 11) E) (N (ec 1126501 [3,4,8]) E)))) (N (N (N (N (ec 16503 [0,1,2,3,4,5,6,7,12,19,11,22,14]) E) (N (el 364614 [1,3,4,13,19] [328604]) E)) (N (N (el 136567 [0,1,2,3,4,5,6,7,12,10] [434910,1090286,7398122]) E) (N (ec 831577 [0,6,7,10,14,16,15]) E))) (N (N (N (ec 77947 [0,1,2,3,4,5,6,7,9,8,23,15]) E) (N (el 696437 [0,1,2,3,4,5,6,7,11,10,14,15] [852934]) E)) (N (N (ec 213048 [0,1,2,3,4,5,6,7,26,15]) E) (N (e1 1527868 16) E))))) (N (N (N (N (N (el 8805 [0,1,2,3,4,5,6,7,11,9,14] [958768,991538,1089844,1122614,3187000,5152915,5185807,7381292,15786298]) E) (N (e1 340016 13) E)) (N (N (el 120711 [0,1,2,3,4,5,6,7,11,9,14,16,15] [5014215]) E) (N (e1 758060 14) E))) (N (N (N (el 57465 [0,1,2,3,4,5,6,7,14] [1090144]) E) (N (e1 610352 9) E)) (N (N (ec 188549 [0,1,2,3,4,5,6,7,11,15]) E) (N (e1 1421912 23) E)))) (N (N (N (N (el 24711 [0,1,2,3,4,5,6,7,12,23,16,15] [459280,1253906,2425315,3351052]) E) (N (e1 516184 30) E)) (N (N (el 147573 [0,1,2,3,4,5,6,7,10,14] [1123138]) E) (N (e1 1015876 16) E))) (N (N (N (e1 86165 16) E) (N (el 712837 [1,2,3,4,5,6,7,10,18,32,16] [1123302]) E)) (N (N (el 229509 [0,1,2,3,4,5,6,7,23,16] [1123200]) E) (N (ec 1843589 [5,34]) E)))))))) (N (N (N (N (N (N (N (N (el 119 [0,1,2,3,4,5,6,7,10] [720962,737348,827420,843846,860232,958514,974922,991308,1089565,1105991,1122377,3055672,5021774,5283919,13557840,13688914,15786065]) E) (N (el 241799 [0,1,2,3,4,5,6,7,23] [828033,861070,2925452,5022343]) E)) (N (N (el 90265 [0,1,2,3,4,5,6,7,8,26,16] [557694,574080,590466,819844,836230,4817486]) E) (N (ec 720970 [0,1,2,3,4,6,7,23,10,15]) E))) (N (N (N (el 28791 [0,1,2,3,4,5,6,7,13,11,14] [459296,729634,852516,1253926,11723005]) E) (N (ec 536678 [4,6,7,26]) E)) (N (N (el 153751 [0,3,4,5,12,13,9,10] [426834,492372,557872,951112,9765636]) E) (N (el 1048711 [0,4,5,16,15,20] [459772,3343354]) E)))) (N (N (N (N (el 12391 [0,1,2,3,4,5,6,7,8,10,15,20] [459110,475496,1089898,1122668,1220974,1253744,3080540,3187058,3318132,7381288,9609590,18014584]) E) (N (e1 352376 10) E)) (N (N (e1 131120 9) E) (N (ec 794714 [0,5,6,7,9,10,15]) E))) (N (N (N (ec 61560 [0,1,2,3,4,5,6,7,8,10,16,15]) E) (N (el 611461 [0,1,2,3,4,5,6,7,19,9,10,14,15] [9520046]) E)) (N (N (ec 192649 [0,1,2,3,4,5,6,7,14,16]) E) (N (ec 1495144 [10,15]) E))))) (N (N (N (N (N (el 4741 [0,1,2,3,4,5,6,7,8,15] [475352,1007834,1089748,1122524,3186910,5152916,5185694,7381201,15786208]) E) (N (el 274585 [0,1,2,3,4,5,6,7,13,14,25] [828314]) E)) (N (N (el 114794 [0,1,2,3,4,5,6,7,28,9,10,14] [5153446,5284519,9347752,9478825,15786666]) E) (N (e1 745621 16) E))) (N (N (N (el 46983 [0,1,2,3,4,5,6,7,12,13,17,8,18,16] [393786,426556,442942,459328,492098,508484]) E) (N (el 602741 [0,1,2,3,4,5,6,7,9,10,14,15,20] [525222,1090472,1123242,2786220,11576238]) E)) (N (N (e1 167996 10) E) (N (e1 1388608 9) E)))) (N (N (N (N (el 17013 [0,1,2,3,4,5,6,7,19,11,14] [565395,598447,3187157,4759698,4792750,7381460,9494948]) E) (N (ec 423543 [0,1,2,3,4,5,6,7,12,17,8,16,15]) E)) (N (N (el 143416 [0,1,2,3,4,5,6,7,23,10] [959256,7381786,15786780]) E) (N (e1 942217 16) E))) (N (N (N (e1 81980 8) E) (N (el 698247 [4,6,10,16,15] [394198]) E)) (N (N (el 217225 [0,1,2,3,4,5,6,7,14] [697204]) E) (N (e1 1560713 14) E)))))) (N (N (N (N (N (N (el 4213 [0,1,2,3,4,5,6,7,12,17,8,18,16] [958602,991392,1089698,1122468,15786150]) E) (N (ec 254085 [0,1,2,3,4,5,6,7,23,14,15]) E)) (N (N (ec 102521 [0,1,2,3,4,5,6,7,14,15]) E) (N (ec 725653 [0,3,4,6,16,15]) E))) (N (N (N (el 34695 [0,1,2,3,4,5,6,7,11,9,8,14,16,15] [393778]) E) (N (el 565625 [0,1,2,3,4,5,6,7,10,14,21] [1090466]) E)) (N (N (el 161671 [0,1,2,3,4,5,6,7,19,10,16,15] [729946,2917062,11748110]) E) (N (el 1114181 [0,1,2,3,5,6,7,23,20] [984064]) E)))) (N (N (N (N (el 16441 [0,1,2,3,4,5,6,7,11] [958888,1089962,5284268,7250350,15786416]) E) (N (e1 364600 13) E)) (N (N (el 135271 [0,1,2,3,4,5,6,7,10,14,21] [959194,991976,1090267,1123049,3056354,3187427,15786730]) E) (N (e1 806964 16) E))) (N (N (N (el 75655 [0,1,2,3,4,5,6,7,12,8,15] [9208422]) E) (N (e1 663624 14) E)) (N (N (e1 213040 11) E) (N (e1 1519664 19) E))))) (N (N (N (N (N (el 8329 [0,1,2,3,4,5,6,7,9] [958754,1089827,15786276]) E) (N (e1 331913 14) E)) (N (N (ec 118921 [0,1,2,3,4,5,6,7,11,9,14]) E) (N (e1 757909 16) E))) (N (N (N (el 57448 [0,1,2,3,4,5,6,7,10] [13558364]) E) (N (el 607125 [0,3,4,5,6,8,10,16] [656312,4916154,5047228]) E)) (N (N (ec 180361 [0,1,2,3,4,5,6,7,22,14]) E) (N (e1 1409128 14) E)))) (N (N (N (N (el 24697 [0,1,2,3,4,5,6,7,23] [180670,565760,582146,598346,1090052,1106438,1122779,9494791]) E) (N (el 516152 [0,3,4,6,13] [4817820]) E)) (N (N (el 144533 [0,1,2,3,4,5,6,7,8,10,16,15] [4915994,5448490,7406334,7512892,11707062]) E) (N (e1 1011800 21) E))) (N (N (N (e1 86076 8) E) (N (el 712821 [1,2,3,4,5,6,7,10,14,15] [459744,852962]) E)) (N (N (el 225673 [0,1,2,3,4,5,6,7,9,8,23,10,15] [5309308]) E) (N (e1 1810568 10) E))))))) (N (N (N (N (N (N (N (el 1399 [0,1,2,3,4,5,6,7,13] [434226,450690,467076,958558,974982,991368,1089631,1106055,1122441,2531388,7266346,7397419,15786092]) E) (N (ec 246933 [0,1,2,3,4,5,6,7,19,23,15]) E)) (N (N (ec 99189 [0,1,2,3,4,5,6,7,12,19,9,14,16]) E) (N (el 722823 [4,6,7,15] [3048366]) E))) (N (N (N (el 32901 [0,1,2,3,4,5,6,7,14,15] [721452,983598]) E) (N (el 548999 [0,4,27,16,21] [3343264]) E)) (N (N (ec 159867 [0,1,2,3,4,5,6,7,9,23,10,15,20]) E) (N (el 1060969 [4,7] [2393084]) E)))) (N (N (N (N (el 12901 [0,1,2,3,4,5,6,7,10,15] [475532,1008014,1089936,1122706,3056020,5063008,5169540,5284033,5300599,5316991,7250218,15786390]) E) (N (ec 360585 [1,2,3,5,6,7,8,16]) E)) (N (N (e1 131132 9) E) (N (e1 795285 16) E))) (N (N (N (el 69940 [0,1,2,3,4,5,6,7,12,17,8,16,15] [959076,13558374]) E) (N (e1 639024 9) E)) (N (N (ec 200837 [0,1,2,3,4,5,6,7,19,11,22,14]) E) (N (e1 1503877 5) E))))) (N (N (N (N (N (el 8295 [0,1,2,3,4,5,6,7,11,9,8,14] [1122568]) E) (N (e1 290936 10) E)) (N (N (el 116615 [0,1,2,3,4,5,6,7,12,9,10,14] [434864,557760,819916,7553706]) E) (N (e1 749721 14) E))) (N (N (N (el 53621 [0,1,2,3,4,5,6,7,19,8,16] [1122892,5284426]) E) (N (e1 606296 14) E)) (N (N (ec 177013 [0,1,2,3,4,5,6,7,19,11,22,16,15]) E) (N (e1 1389957 15) E)))) (N (N (N (N (el 24631 [0,1,2,3,4,5,6,7,8,23,10,15] [983538,1122804,2425012,3219958]) E) (N (e1 458832 19) E)) (N (N (el 143509 [0,1,2,3,4,5,6,7,12,10,18,16] [590636,1254190,5309178,5415728,9609904]) E) (N (e1 958496 19) E))) (N (N (N (e1 86070 14) E) (N (el 704645 [1,2,3,4,5,6,7,12,19,11,10,14] [599006]) E)) (N (N (el 221287 [0,3,4,7,12,13,9,10,14] [721782,1377144]) E) (N (e1 1605765 16) E)))))) (N (N (N (N (N (N (el 4231 [0,1,2,3,4,5,6,7,8,10,16,15] [458948,983238,1122504]) E) (N (ec 270453 [0,1,2,3,4,5,6,7,13,15]) E)) (N (N (ec 106633 [0,1,2,3,4,5,6,7,9,10,14,15]) E) (N (ec 737925 [0,5,6,8,10,15]) E))) (N (N (N (ec 41861 [0,1,2,3,4,5,6,7,13,8,16]) E) (N (e1 577597 21) E)) (N (N (e1 163900 10) E) (N (e1 1265696 17) E)))) (N (N (N (N (el 16517 [0,1,2,3,4,5,6,7,13,11,14,15] [475582,565390,598464,721346,737732,1089972,1122758,6857012]) E) (N (ec 377209 [0,1,2,3,4,5,6,7,10,15]) E)) (N (N (el 139637 [0,1,2,3,4,5,6,7,28,13,9,10,14,21] [959222,992002,1090295,1123075,15786756]) E) (N (e1 852032 10) E))) (N (N (N (el 78213 [0,1,2,3,4,5,6,7,8,16,15] [393836,2654826]) E) (N (el 696453 [0,1,2,3,4,5,6,7,12,10,16] [1123276,5284814]) E)) (N (N (e1 213052 11) E) (N (e0 1536073) E))))) (N (N (N (N (N (el 9847 [0,1,2,3,4,5,6,7,12,9] [426122,434496,491842,688432,1220932,7512346,7528736,7545124,9609518,11706686]) E) (N (e1 340022 14) E)) (N (N (el 124807 [0,1,2,3,4,5,6,7,12,13,9,14] [426704,492242]) E) (N (e1 770096 19) E))) (N (N (N (ec 57481 [0,1,2,3,4,5,6,7,16,15]) E) (N (e1 610362 23) E)) (N (N (ec 192570 [0,1,2,3,4,5,6,7,13,11,23,14,15]) E) (N (e1 1425440 19) E)))) (N (N (N (N (el 24715 [0,1,2,3,4,5,6,7,23,15] [2392547,4751896]) E) (N (e1 536644 15) E)) (N (N (ec 148357 [0,1,2,3,4,5,6,7,12,10,16]) E) (N (ec 1032280 [0,1,2,3,4,5,6,7,14]) E))) (N (N (N (e1 86169 16) E) (N (ec 713861 [1,2,3,4,6,7,29,8,10,16,15]) E)) (N (N (ec 237672 [0,1,2,3,4,5,6,7,13,11,23,14,15]) E) (N (e0 1855877) E))))))))))
noncomputable def m255Ck : Nat → Bool := checkNode m255Mask m255Goal (Nat.sub (Nat.shiftLeft 1 m255Pairs.length) 1) symMain 515 13 m255Ws m255D 10 m255Cuts 6
theorem q166 : tb 0 24 m255Ck = true := by decide +kernel
theorem q167 : tb 24 24 m255Ck = true := by decide +kernel
theorem q168 : tb 48 24 m255Ck = true := by decide +kernel
theorem q169 : tb 72 24 m255Ck = true := by decide +kernel
theorem q170 : tb 96 24 m255Ck = true := by decide +kernel
theorem q171 : tb 120 24 m255Ck = true := by decide +kernel
theorem q172 : tb 144 24 m255Ck = true := by decide +kernel
theorem q173 : tb 168 24 m255Ck = true := by decide +kernel
theorem q174 : tb 192 24 m255Ck = true := by decide +kernel
theorem q175 : tb 216 24 m255Ck = true := by decide +kernel
theorem q176 : tb 240 24 m255Ck = true := by decide +kernel
theorem q177 : tb 264 24 m255Ck = true := by decide +kernel
theorem q178 : tb 288 24 m255Ck = true := by decide +kernel
theorem q179 : tb 312 24 m255Ck = true := by decide +kernel
theorem q180 : tb 336 24 m255Ck = true := by decide +kernel
theorem q181 : tb 360 24 m255Ck = true := by decide +kernel
theorem q182 : tb 384 24 m255Ck = true := by decide +kernel
theorem q183 : tb 408 24 m255Ck = true := by decide +kernel
theorem q184 : tb 432 24 m255Ck = true := by decide +kernel
theorem q185 : tb 456 24 m255Ck = true := by decide +kernel
theorem q186 : tb 480 24 m255Ck = true := by decide +kernel
theorem q187 : tb 504 11 m255Ck = true := by decide +kernel
theorem m255All : treeBlock 0 515 m255Ck = true := (tm 0 264 251 (tm 0 120 144 (tm 0 48 72 (tm 0 24 24 q166 q167) (tm 48 24 48 q168 (tm 72 24 24 q169 q170))) (tm 120 72 72 (tm 120 24 48 q171 (tm 144 24 24 q172 q173)) (tm 192 24 48 q174 (tm 216 24 24 q175 q176)))) (tm 264 120 131 (tm 264 48 72 (tm 264 24 24 q177 q178) (tm 312 24 48 q179 (tm 336 24 24 q180 q181))) (tm 384 72 59 (tm 384 24 48 q182 (tm 408 24 24 q183 q184)) (tm 456 24 35 q185 (tm 480 24 11 q186 q187)))))
theorem m255Low : LowerM m255Mask m255Raw m255Goal 14 := by
  have hraw : m255Ws.map Wire.val = m255Raw := by decide +kernel
  rw [← hraw]
  have hnc : btreeAll (fun r => r.2.1.all (fun ci => Nat.blt ci 35)) m255D = true := by decide +kernel
  refine lowerPoolDAG (pairs := m255Pairs) (sym := symMain) (count := 515) (rootFuel := 13) (fdepth := 10) (cdepth := 6) (dag := m255D) (cutTree := m255Cuts)
    (by unfold Masked; decide +kernel) (by decide +kernel) (by unfold Proper Masked; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sym_of_row (by unfold Masked; decide +kernel) symMain_spec.1 symMain_spec.2 (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (by rw [hraw]; exact m255Ess)
    (fun i _ ci hci => by
      have h1 := btreeGet_prop (p := fun r : NodeRec => r.2.1.all (fun x => Nat.blt x 35)) (defv := (0,[],[])) rfl hnc 10 i
      rw [hraw]; exact m255CutValid ci (Nat.blt_eq.mp (List.all_eq_true.mp h1 ci hci)))
    m255All

def flatEdges : List ℕ := [0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7]

def targetFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < flatEdges.length / 2,
    (List.ofFn x).getD (flatEdges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (flatEdges.getD (2 * i + 1) 0) false = true)

def witness15 : Circuit :=
  ⟨[⟨.or, [7, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 9]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [16, 9]⟩,
    ⟨.or, [1, 17]⟩, ⟨.and, [8, 18]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [13, 21]⟩], 22⟩

theorem witness15Legal : ∀ g ∈ witness15.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness15Correct : ∀ x : Fin 8 → Bool, witness15.eval (List.ofFn x) = targetFn x := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem sample8OK : ∀ r : Row, m255Raw.map (bit r) = List.ofFn (fun i : Fin 8 => r.val.testBit i.val) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem goal8OK : ∀ r : Row, bit r m255Goal = targetFn (fun i : Fin 8 => r.val.testBit i.val) := by decide +kernel

theorem mainLower (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFn x) :
    14 ≤ gates.countP (fun g => !isNot g) :=
  physical_lower (vars8 := m255Raw) (goal8 := m255Goal)
    (by unfold Proper Masked; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simpa [show m255Mask = fullMask by decide +kernel] using m255Low)
    sample8OK goal8OK gates o legal computes

end PEqualNP.Outside.L_meta_35260

theorem PEqualNP.Outside.L_meta_35260 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  by_cases hnot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hg, hgop⟩ := hnot
    have hlow := PEqualNP.Outside.L_meta_35260.mainLower gates o legal computes
    have hlt : gates.countP (fun w => !PEqualNP.Outside.L_meta_35260.isNot w) < gates.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [PEqualNP.Outside.L_meta_35260.isNot, hgop]⟩
    have hlen : PEqualNP.Outside.L_meta_35260.witness15.gates.length = 15 := rfl
    exact ⟨PEqualNP.Outside.L_meta_35260.witness15.gates, PEqualNP.Outside.L_meta_35260.witness15.output,
      PEqualNP.Outside.L_meta_35260.witness15Legal, by omega, PEqualNP.Outside.L_meta_35260.witness15Correct⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (legal g hg).2⟩, Nat.le_refl _, computes⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)
