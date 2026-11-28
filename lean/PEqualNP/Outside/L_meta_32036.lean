import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620

/- Guarded-row coordinate and correlation lemmas adapted from
   922415d552b30e9f8986d07175d7ab301f925448:lean/PEqualNP/Outside/L_meta_30706.lean. -/

namespace PEqualNP.Outside.L_meta_32036_aux.Base

open Finset

def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k))
    ((constant round).val.testBit (pos % k))

def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

lemma rotFn_lt {k : ℕ} (s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotFn_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsm : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hhi : word.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and, hmod]
  · have hlt : i < s % k := by omega
    have hdec : decide (s % k ≤ i) = false := decide_eq_false (by omega)
    have hmod : (i + k - s % k) % k = i + (k - s % k) := by
      have h1 : i + k - s % k = i + (k - s % k) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hdec, Bool.false_and, Bool.false_or, hmod, Nat.add_comm (k - s % k) i]

lemma mod_sub_one {k n : ℕ} (hk : 1 ≤ k) :
    (n % k + k - 1 % k) % k = (n + k - 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : n % k < k := Nat.mod_lt n (by omega)
    have hrew : n % k + k - 1 = n % k + (k - 1) := by omega
    have hrew2 : n + k - 1 = n + (k - 1) := by omega
    rw [hrew, hrew2, Nat.mod_add_mod]

lemma bitFn_zero {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    bitFn k constant row 0 key pos =
      xor (key.testBit ((pos + k - 1) % k)) (row.testBit (pos % k)) := by
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]

abbrev Block := Bool × Bool × Bool

def bxor (x y : Block) : Block :=
  (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2 y.2.2)

def affine (flag : Bool) (x : Block) : Bool :=
  if flag then x.1 else x.2.1

def point (flag : Bool) : Block := (true, true, flag)

def localValue (α β δ f₅ : Bool) (x : Block) : Bool :=
  let u := xor α x.1
  let v := xor β ((!x.1) && x.2.1)
  let w := xor δ ((x.1 == x.2.1) && x.2.2)
  let s₅ := xor (xor β f₅) u
  let s₆ := xor (xor f₅ u) v
  let s₇ := xor (xor u v) w
  xor s₅ ((!s₆) && s₇)

lemma localValue_eq (α β δ f₅ : Bool) (x : Block)
    (h : xor β f₅ = !α) :
    localValue α β δ f₅ x =
      xor (!affine (xor (xor α β) δ) x) (decide (x = point (xor (xor α β) δ))) := by
  rcases x with ⟨a, b, c⟩
  cases α <;> cases β <;> cases δ <;> cases f₅ <;> cases a <;> cases b <;> cases c <;>
    first | decide | contradiction

def shareBit (k : ℕ) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) : Bool :=
  xor (bitFn k constant row.val 0 key.val pos) (bitFn k constant row.val 0 ref.val pos)

lemma shareBit_eq {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key pos =
      xor (key.val.testBit ((pos + k - 1) % k)) (ref.val.testBit ((pos + k - 1) % k)) := by
  unfold shareBit
  rw [bitFn_zero hk constant key.isLt, bitFn_zero hk constant ref.isLt]
  cases key.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;>
    cases row.val.testBit (pos % k) <;> rfl

def combine {k : ℕ} (ref left right : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(left.val ^^^ right.val ^^^ ref.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

lemma shareBit_combine {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref (combine ref left right) pos =
      xor (shareBit k constant row ref left pos) (shareBit k constant row ref right pos) := by
  simp only [shareBit_eq hk, combine, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    decide_eq_true (Nat.mod_lt _ (by omega : 0 < k)), Bool.true_and]
  cases left.val.testBit ((pos + k - 1) % k) <;>
    cases right.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;> rfl

lemma shareBit_mod {k : ℕ} (_hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key (pos % k) = shareBit k constant row ref key pos := by
  unfold shareBit bitFn
  rw [Nat.mod_mod]

noncomputable def shareBitsEquiv {k : ℕ} (hk : 12 ≤ k)
    (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) : Fin (2 ^ k) ≃ (Fin k → Bool) := by
  classical
  apply Equiv.ofBijective (fun key j => shareBit k constant row ref key j.val)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · let j : Fin k := ⟨(i+1)%k, Nat.mod_lt _ (by omega)⟩
    have hh := congrFun hab j
    change shareBit k constant row ref a ((i + 1) % k) =
      shareBit k constant row ref b ((i + 1) % k) at hh
    rw [shareBit_mod hk, shareBit_mod hk, shareBit_eq hk, shareBit_eq hk,
      show i + 1 + k - 1 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi] at hh
    cases ref.val.testBit i <;> simpa using hh
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]

def toBlock (f : Fin 3 → Bool) : Block := (f 0, f 1, f 2)

def fromBlock (x : Block) (j : Fin 3) : Bool :=
  if j = 0 then x.1 else if j = 1 then x.2.1 else x.2.2

lemma toBlock_fromBlock (x : Block) : toBlock (fromBlock x) = x := by
  rcases x with ⟨a, b, c⟩
  rfl

lemma fromBlock_toBlock (f : Fin 3 → Bool) (j : Fin 3) : fromBlock (toBlock f) j = f j := by
  fin_cases j <;> rfl

abbrev Remainder {m k : ℕ} (pin : Finset (Fin k)) (coord : Fin m × Fin 3 → Fin k) :=
  {j : Fin k // j ∉ pin ∧ j ∉ Set.range coord}

noncomputable def splitBits {m k : ℕ} (pin : Finset (Fin k))
    (coord : Fin m × Fin 3 → Fin k) (hc : Function.Injective coord)
    (hf : ∀ ij, coord ij ∉ pin) :
    {f : Fin k → Bool // ∀ j ∈ pin, f j = false} ≃
      (Fin m → Block) × (Remainder pin coord → Bool) := by
  classical
  let tail := fun (g : Remainder pin coord → Bool) (j : Fin k) =>
    if h : j ∉ pin ∧ j ∉ Set.range coord then g ⟨j, h⟩ else false
  let pack := fun (p : (Fin m → Block) × (Remainder pin coord → Bool)) =>
    Function.extend coord (fun ij => fromBlock (p.1 ij.1) ij.2) (tail p.2)
  have hpack (p : (Fin m → Block) × (Remainder pin coord → Bool)) (j : Fin k) (hj : j ∉ Set.range coord) :
      pack p j = tail p.2 j := Function.extend_apply' _ _ _ hj
  refine
    { toFun := fun f => (fun i => toBlock (fun j => f.val (coord (i,j))), fun j => f.val j.val)
      invFun := fun p => ⟨pack p, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro j hj
    have hn : j ∉ Set.range coord := by
      rintro ⟨ij, rfl⟩
      exact hf ij hj
    rw [hpack _ _ hn]
    simp [tail, hj]
  · intro f
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range coord
    · obtain ⟨⟨i, t⟩, rfl⟩ := hj
      change pack _ (coord (i,t)) = f.val (coord (i,t))
      dsimp only [pack]
      rw [hc.extend_apply]
      exact fromBlock_toBlock _ _
    · change pack _ j = f.val j
      rw [hpack _ _ hj]
      by_cases hp : j ∈ pin
      · simp [tail, hp, f.property j hp]
      · have h : j ∉ pin ∧ j ∉ Set.range coord := ⟨hp, hj⟩
        simp only [tail, dite_eq_left h]
  · intro p
    apply Prod.ext
    · funext i
      change toBlock (fun j => pack p (coord (i,j))) = p.1 i
      simp_rw [pack, hc.extend_apply]
      exact toBlock_fromBlock _
    · funext j
      change pack p j.val = p.2 j
      rw [hpack _ _ j.property.2]
      simp only [tail, dite_eq_left j.property]

lemma extract_local {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (p : ℕ) :
    let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
    let first := fun j => bitFn k constant row.val 1 ref.val (p+j)
    let pair := xor (old 7) (old 8)
    let τ := xor (old 6) pair
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
    let β := xor τ (injectedFn k constant 1 ref.val (p+7))
    let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
    let x : Block :=
      (xor (bitFn k constant row.val 0 key.val (p+9)) pair,
       xor (bitFn k constant row.val 0 key.val (p+10)) (old 7),
       xor (bitFn k constant row.val 0 key.val (p+11)) (old 8))
    (∀ j < 9, bitFn k constant row.val 0 key.val (p+j) = old j) →
    τ = false → xor (first 4) (first 5) = !α → first 4 = β →
    bitFn k constant row.val 2 key.val (p+5) =
      xor (xor (!affine (xor (xor α β) δ) x) (decide (x = point (xor (xor α β) δ))))
        (injectedFn k constant 2 ref.val (p+5)) := by
  intro old first pair τ α β δ x hkey hτ h45 h4
  have hh45 : xor β (first 5) = !α := by simpa only [h4] using h45
  have hmerged := PEqualNP.Outside.L_meta_25620 k (by omega) constant hk row ref p
  have hmem : key ∈ (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun q => (List.range 9).all (fun j => bitFn k constant row.val 0 q.val (p+j) == old j)) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
      beq_iff_eq] using hkey
  have hb := (hmerged.1 key hmem).2 (3 : Fin 4)
  let n : ℕ := x.1.toNat + 2 * x.2.1.toNat + 4 * x.2.2.toNat
  let model : ℕ → Bool := fun j =>
    if j = 6 then xor α ((!τ) && n.testBit 0)
    else if j = 7 then xor β ((!n.testBit 0) && n.testBit 1)
    else if j = 8 then xor δ ((n.testBit 0 == n.testBit 1) && n.testBit 2)
    else first j
  change bitFn k constant row.val 2 key.val (p+5) =
    xor (xor (xor (xor (model 4) (model 5)) (model 6))
      (!(xor (xor (model 5) (model 6)) (model 7)) && xor (xor (model 6) (model 7)) (model 8)))
      (injectedFn k constant 2 ref.val (p+5)) at hb
  have bits (y : Block) :
      let v := y.1.toNat + 2 * y.2.1.toNat + 4 * y.2.2.toNat
      v.testBit 0 = y.1 ∧ v.testBit 1 = y.2.1 ∧ v.testBit 2 = y.2.2 := by
    rcases y with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> decide
  have hn := bits x
  change n.testBit 0 = x.1 ∧ n.testBit 1 = x.2.1 ∧ n.testBit 2 = x.2.2 at hn
  have hm : bitFn k constant row.val 2 key.val (p+5) =
      xor (localValue α β δ (first 5) x) (injectedFn k constant 2 ref.val (p+5)) := by
    rw [hb]
    simp only [model, h4, hτ, Bool.not_false, Bool.true_and, hn.1, hn.2.1, hn.2.2,
      show (4 : ℕ) ≠ 6 by decide, show (4 : ℕ) ≠ 7 by decide, show (4 : ℕ) ≠ 8 by decide,
      show (5 : ℕ) ≠ 6 by decide, show (5 : ℕ) ≠ 7 by decide, show (5 : ℕ) ≠ 8 by decide,
      show (7 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 7 by decide,
      ↓reduceIte, localValue]
  rw [hm, localValue_eq α β δ (first 5) x hh45]

def windowFlag {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Bool :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  let pair := xor (old 7) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
  let β := xor (xor (old 6) pair) (injectedFn k constant 1 ref.val (p+7))
  let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
  xor (xor α β) δ

def windowOffset {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  (xor (old 9) (xor (old 7) (old 8)), xor (old 10) (old 7), xor (old 11) (old 8))

def windowShare {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref key : Fin (2 ^ k)) (p : ℕ) : Block :=
  (shareBit k constant row ref key (p+9), shareBit k constant row ref key (p+10),
    shareBit k constant row ref key (p+11))

def windowShift {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  bxor (windowOffset constant row ref p) (point (windowFlag constant row ref p))

lemma xor_left_eq (a b c : Bool) : xor a b = c ↔ a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

lemma bxor_eq (a b c : Block) : bxor a b = c ↔ a = bxor b c := by
  rcases a with ⟨aa, ab, ac⟩
  rcases b with ⟨ba, bb, bc⟩
  rcases c with ⟨ca, cb, cc⟩
  simp only [bxor, Prod.mk.injEq, xor_left_eq]

lemma bxor_assoc (a b c : Block) : bxor (bxor a b) c = bxor a (bxor b c) := by
  simp [bxor]

lemma bxor_comm (a b : Block) : bxor a b = bxor b a := by
  simp [bxor, Bool.xor_comm]

lemma bxor_cancel (a b : Block) : bxor a (bxor a b) = b := by
  rcases b with ⟨b₁, b₂, b₃⟩
  simp [bxor]

lemma bxor_cancel_right (a b : Block) : bxor (bxor a b) b = a := by
  rw [bxor_comm (bxor a b) b, bxor_comm a b, bxor_cancel]

lemma xor_recover (a b c : Bool) : xor (xor a b) (xor b c) = xor a c := by
  cases a <;> cases b <;> cases c <;> rfl

lemma affine_bxor (f : Bool) (a b : Block) : affine f (bxor a b) = xor (affine f a) (affine f b) := by
  cases f <;> rfl

lemma guarded_window {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (p : ℕ) :
    let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
    let first := fun j => bitFn k constant row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
    let β := xor τ (injectedFn k constant 1 ref.val (p+7))
    let l := windowShare constant row ref left p
    let r := bxor (windowShare constant row ref right p) (windowShift constant row ref p)
    let f := windowFlag constant row ref p
    let base := xor (!affine f (point f)) (injectedFn k constant 2 ref.val (p+5))
    (∀ j < 9, shareBit k constant row ref left (p+j) = false) →
    (∀ j < 9, shareBit k constant row ref right (p+j) = false) →
    τ = false → xor (first 4) (first 5) = !α → first 4 = β →
    bitFn k constant row.val 2 (combine ref left right).val (p+5) =
      xor (xor (xor base (affine f l)) (affine f r)) (decide (l = r)) := by
  intro old first τ α β l r f base hl hr ht h45 h4
  let key := combine ref left right
  let o := windowOffset constant row ref p
  have hh j (hj : j < 9) : bitFn k constant row.val 0 key.val (p+j) = old j := by
    have h := shareBit_combine hk constant row ref left right (p+j)
    rw [hl j hj, hr j hj] at h
    change xor (bitFn k constant row.val 0 key.val (p+j)) (old j) = false at h
    exact (xor_left_eq _ _ _).mp h |>.trans (Bool.xor_false _)
  have ht' : xor (old 6) (xor (old 7) (old 8)) = false := by
    rw [← Bool.xor_assoc]
    exact ht
  have h4' : first 4 = xor (xor (old 6) (xor (old 7) (old 8)))
      (injectedFn k constant 1 ref.val (p+7)) := by
    rw [← Bool.xor_assoc]
    exact h4
  have hvalue := extract_local hk constant row ref key p hh ht' h45 h4'
  let x : Block := (xor (bitFn k constant row.val 0 key.val (p+9)) (xor (old 7) (old 8)),
    xor (bitFn k constant row.val 0 key.val (p+10)) (old 7),
    xor (bitFn k constant row.val 0 key.val (p+11)) (old 8))
  change bitFn k constant row.val 2 key.val (p+5) =
    xor (xor (!affine f x) (decide (x = point f))) (injectedFn k constant 2 ref.val (p+5)) at hvalue
  have hshift j : xor (bitFn k constant row.val 0 key.val (p+j)) (old j) =
      xor (shareBit k constant row ref left (p+j)) (shareBit k constant row ref right (p+j)) :=
    shareBit_combine hk constant row ref left right (p+j)
  have hx : x = bxor l (bxor r (point f)) := by
    have hxo : x = bxor (bxor l (windowShare constant row ref right p)) o := by
      dsimp only [x, bxor, l, windowShare, o, windowOffset]
      rw [← hshift 9, ← hshift 10, ← hshift 11]
      exact Prod.ext (xor_recover _ _ _).symm (Prod.ext (xor_recover _ _ _).symm (xor_recover _ _ _).symm)
    rw [hxo, bxor_assoc]
    change bxor l (bxor (windowShare constant row ref right p) o) =
      bxor l (bxor (bxor (windowShare constant row ref right p) (bxor o (point f))) (point f))
    rw [bxor_assoc (windowShare constant row ref right p), bxor_cancel_right]
  have heq : (x = point f) ↔ l = r := by
    rw [hx, bxor_eq, bxor_cancel_right]
  rw [hvalue, decide_eq_decide.mpr heq, hx, affine_bxor, affine_bxor]
  change xor (xor (!(xor (affine f l) (xor (affine f r) (affine f (point f))))) (decide (l = r)))
      (injectedFn k constant 2 ref.val (p+5)) = _
  dsimp only [base]
  generalize affine f l = a, affine f r = b, affine f (point f) = c,
    decide (l = r) = e, injectedFn k constant 2 ref.val (p+5) = j
  cases a <;> cases b <;> cases c <;> cases e <;> cases j <;> rfl

def parityOn {I : Type} (s : Finset I) (f : I → Bool) : Bool :=
  (∑ i ∈ s, (f i).toNat) % 2 == 1

lemma parity_add (a b : ℕ) : ((a+b)%2 == 1) = xor (a%2 == 1) (b%2 == 1) := by
  have ha : a%2 = 0 ∨ a%2 = 1 := by omega
  have hb : b%2 = 0 ∨ b%2 = 1 := by omega
  rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> rfl

lemma parity_insert {I : Type} [DecidableEq I] {s : Finset I} {i : I} (hi : i ∉ s) (f : I → Bool) :
    parityOn (insert i s) f = xor (f i) (parityOn s f) := by
  unfold parityOn
  rw [sum_insert hi, parity_add]
  cases f i <;> rfl

lemma parity_xor {I : Type} (s : Finset I) (f g : I → Bool) :
    parityOn s (fun i => xor (f i) (g i)) = xor (parityOn s f) (parityOn s g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    simp only [parity_insert hi, ih, Bool.xor_assoc, Bool.xor_left_comm]

noncomputable def bitSign (b : Bool) : ℝ := if b then -1 else 1

lemma sign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> norm_num [bitSign]

lemma sign_sq (a : Bool) : bitSign a ^ 2 = 1 := by cases a <;> norm_num [bitSign]

lemma sign_parity {I : Type} (s : Finset I) (f : I → Bool) :
    bitSign (parityOn s f) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [parityOn, bitSign]
  | @insert i s hi ih => rw [parity_insert hi, sign_xor, ih, prod_insert hi]

def modelTruth {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x y : Fin m → Block) : Bool :=
  xor (xor (φ x) (ψ y)) (parityOn univ fun i => decide (x i = y i))

def support {m : ℕ} {B : Type} (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (x : Fin m → B) : Finset (Fin m) := univ.filter (fun i => p i (x i))

lemma card_support {m : ℕ} {B : Type} [Fintype B] (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (a b : ℕ) (ha : ∀ i, (univ.filter (p i)).card = a)
    (hb : ∀ i, (univ.filter (fun x => ¬p i x)).card = b) (J : Finset ℕ) :
    (univ.filter (fun x => (support p x).card ∈ J)).card =
      ∑ j ∈ J, m.choose j * a ^ j * b ^ (m-j) := by
  classical
  have hfiber (s : Finset (Fin m)) :
      (univ.filter (fun x => support p x = s)).card = a ^ s.card * b ^ (m-s.card) := by
    let allow := fun i => if i ∈ s then univ.filter (p i) else univ.filter (fun x => ¬p i x)
    have hrect : univ.filter (fun x => support p x = s) = Fintype.piFinset allow := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl i
        by_cases hi : p i (x i) <;> simp [allow, support, hi]
      · intro h
        ext i
        have hh := h i
        by_cases hi : i ∈ s <;> simp_all [allow, support]
    rw [hrect, Fintype.card_piFinset]
    have hallow i : (allow i).card = if i ∈ s then a else b := by
      by_cases hi : i ∈ s <;> simp [allow, hi, ha, hb]
    simp_rw [hallow]
    rw [Finset.prod_ite]
    have hs : univ.filter (fun i => i ∈ s) = s := by ext i; simp
    have hc : (univ.filter (fun i => i ∉ s)).card = m - s.card := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (p := fun i => i ∈ s)
      rw [hs, card_univ, Fintype.card_fin] at h
      omega
    rw [hs, prod_const, prod_const, hc]
  rw [← sum_card_fiberwise_eq_card_filter univ J (fun x => (support p x).card)]
  apply sum_congr rfl
  intro j hj
  let S := (univ : Finset (Fin m)).powersetCard j
  have hm : ((univ : Finset (Fin m → B)).filter (fun x => (support p x).card = j) : Set (Fin m → B)).MapsTo
      (support p) S := by
    intro x hx
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hx).2⟩
  rw [card_eq_sum_card_fiberwise hm]
  have hterm (s : Finset (Fin m)) (hs : s ∈ S) :
      ((univ.filter (fun x => (support p x).card = j)).filter (fun x => support p x = s)).card =
      a ^ j * b ^ (m-j) := by
    have hs' := (mem_powersetCard.mp hs).2
    rw [← hs', ← hfiber s]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact And.right
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [sum_congr rfl hterm, sum_const, Nat.nsmul_eq_mul, mul_assoc]
  simp [S, card_powersetCard]

def distance {m : ℕ} (x y : Fin m → Block) : ℕ :=
  (univ.filter (fun i => x i ≠ y i)).card

lemma card_block_ne : ∀ x : Block, (univ.filter (fun y : Block => x ≠ y)).card = 7 := by
  decide +kernel

lemma card_near {m : ℕ} (h : ℕ) (x : Fin m → Block) :
    (univ.filter (fun y => distance x y ≤ h)).card = ∑ j ∈ range (h+1), m.choose j * 7^j := by
  classical
  let p := fun i (b : Block) => x i ≠ b
  let _ : ∀ i, DecidablePred (p i) := fun i b => inferInstanceAs (Decidable (x i ≠ b))
  have hp : ∀ i, (univ.filter (p i)).card = 7 := fun i => card_block_ne (x i)
  have hn : ∀ i, (univ.filter (fun b => ¬p i b)).card = 1 := by
    intro i
    have hs : (univ.filter (fun b => ¬p i b)) = {x i} := by
      ext b
      simp [p, eq_comm]
    simp [hs]
  have heq : univ.filter (fun y => distance x y ≤ h) =
      univ.filter (fun y => (support p y).card ∈ range (h+1)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_range, Nat.lt_succ_iff]
    rfl
  rw [heq, card_support p 7 1 hp hn]
  simp

lemma card_code (m : ℕ) : Fintype.card (Fin m → Block) = 8 ^ m := by
  simp [Fintype.card_prod]

def rationalSign (b : Bool) : ℚ := if b then -1 else 1

lemma rationalSign_cast (b : Bool) : ((rationalSign b : ℚ) : ℝ) = bitSign b := by
  cases b <;> norm_num [rationalSign, bitSign]

lemma local_correlation (x y : Block) :
    (∑ z : Block, bitSign (decide (x = z)) * bitSign (decide (y = z))) =
      if x ≠ y then (4 : ℝ) else 8 := by
  have hq : ∀ a b : Block,
      (∑ z : Block, rationalSign (decide (a = z)) * rationalSign (decide (b = z))) =
        if a ≠ b then (4 : ℚ) else 8 := by decide +kernel
  have hc := congrArg (fun q : ℚ => (q : ℝ)) (hq x y)
  split_ifs at hc ⊢ <;> simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, rationalSign_cast] using hc

lemma correlation {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x x' : Fin m → Block) :
    (∑ y : Fin m → Block, bitSign (modelTruth φ ψ x y) * bitSign (modelTruth φ ψ x' y)) =
      (bitSign (φ x) * bitSign (φ x')) * (8 : ℝ)^m * (1 / 2)^distance x x' := by
  classical
  have hfactor (y : Fin m → Block) :
      bitSign (modelTruth φ ψ x y) * bitSign (modelTruth φ ψ x' y) =
        (bitSign (φ x) * bitSign (φ x')) *
          (∏ i : Fin m, (bitSign (decide (x i = y i)) * bitSign (decide (x' i = y i)))) := by
    simp only [modelTruth, sign_xor, sign_parity, prod_mul_distrib]
    calc
      _ = (bitSign (φ x) * bitSign (φ x')) * bitSign (ψ y) ^ 2 *
          ((∏ i : Fin m, bitSign (decide (x i = y i))) * ∏ i : Fin m, bitSign (decide (x' i = y i))) := by ring
      _ = _ := by rw [sign_sq, mul_one]
  simp_rw [hfactor, ← mul_sum]
  rw [← Fintype.prod_sum (fun (i : Fin m) (z : Block) =>
    bitSign (decide (x i = z)) * bitSign (decide (x' i = z)))]
  simp_rw [local_correlation]
  rw [Finset.prod_ite, prod_const, prod_const]
  have hcompl : (univ.filter (fun i => ¬x i ≠ x' i)).card = m - distance x x' := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (p := fun i => x i ≠ x' i)
    rw [card_univ, Fintype.card_fin] at h
    change distance x x' + (univ.filter (fun i => ¬x i ≠ x' i)).card = m at h
    omega
  rw [hcompl]
  change bitSign (φ x) * bitSign (φ x') * (4 ^ distance x x' * 8 ^ (m-distance x x')) = _
  have hd : distance x x' ≤ m := by simpa [distance] using card_filter_le (univ : Finset (Fin m)) (fun i => x i ≠ x' i)
  have hp : (8 : ℝ)^m = 8^distance x x' * 8^(m-distance x x') := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  rw [hp, show (4 : ℝ) = 8 * (1/2) by norm_num, mul_pow]
  ring

lemma card_filter_fst {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) [DecidablePred p] :
    ((univ : Finset (A × B)).filter (fun z => p z.1)).card =
      (univ.filter p).card * Fintype.card B := by
  have heq : (univ : Finset (A × B)).filter (fun z => p z.1) = (univ.filter p).product univ := by
    ext z
    simp
  rw [heq]
  change ((univ.filter p) ×ˢ (univ : Finset B)).card = _
  rw [card_product, card_univ]

abbrev Input (m : ℕ) (R : Type) := (Fin m → Block) × R

lemma xor_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  rw [xor_left_eq, Bool.xor_false]

def shiftBlock {m : ℕ} (s : Fin m → Block) : (Fin m → Block) ≃ (Fin m → Block) where
  toFun x i := bxor (x i) (s i)
  invFun x i := bxor (x i) (s i)
  left_inv x := funext fun i => bxor_cancel_right (x i) (s i)
  right_inv x := funext fun i => bxor_cancel_right (x i) (s i)


lemma model_stats {m : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (φ ψ : (Fin m → Block) → Bool) (h : ℕ) :
    let ball := ∑ j ∈ range (h+1), m.choose j * 7^j
    let S := Input m R
    (Fintype.card S : ℝ) = 8^m * Fintype.card R ∧
    (∀ x : S, ((univ.filter (fun y : S => distance x.1 y.1 ≤ h)).card : ℝ) ≤
      (ball : ℝ) * Fintype.card R) ∧
    (∀ x x' : S, (∑ y : S, bitSign (modelTruth φ ψ x.1 y.1) * bitSign (modelTruth φ ψ x'.1 y.1)) ≤
      (Fintype.card S : ℝ) * ((1/2 : ℝ)^(h+1) + (1-(1/2 : ℝ)^(h+1)) *
        (if distance x.1 x'.1 ≤ h then 1 else 0))) := by
  intro ball S
  let close := fun (x y : Input m R) => distance x.1 y.1 ≤ h
  let N : ℝ := Fintype.card R
  let r : ℝ := (1/2)^(h+1)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcount : (Fintype.card (Input m R) : ℝ) = 8^m * N := by
    simp only [Input, Fintype.card_prod, card_code, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, N]
  have hnear (x : Input m R) : ((univ.filter (close x)).card : ℝ) ≤ (ball : ℝ) * N := by
    rw [card_filter_fst (fun y => distance x.1 y ≤ h), card_near, Nat.cast_mul]
  have hc (x x' : Input m R) :
      (∑ y : Input m R, bitSign (modelTruth φ ψ x.1 y.1) * bitSign (modelTruth φ ψ x'.1 y.1)) ≤
        (Fintype.card (Input m R) : ℝ) * (r + (1-r) * (if close x x' then 1 else 0)) := by
    rw [Fintype.sum_prod_type, hcount]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    rw [correlation]
    let d := distance x.1 x'.1
    have hf : bitSign (φ x.1) * bitSign (φ x'.1) ≤ 1 := by
      cases φ x.1 <;> cases φ x'.1 <;> norm_num [bitSign]
    have hd : (1/2 : ℝ)^d ≤ r + (1-r) * (if close x x' then 1 else 0) := by
      by_cases he : close x x'
      · rw [ite_eq_left he, mul_one, add_sub_cancel]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      · rw [ite_eq_right he, mul_zero, add_zero]
        have hh : h + 1 ≤ d := by simpa [close, d] using Nat.succ_le_iff.mpr (Nat.lt_of_not_ge he)
        calc
          _ = (1/2 : ℝ)^(h+1) * (1/2 : ℝ)^(d-(h+1)) := by rw [← pow_add, Nat.add_sub_of_le hh]
          _ ≤ (1/2 : ℝ)^(h+1) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr0
          _ = _ := by simp [r]
    change N * (bitSign (φ x.1) * bitSign (φ x'.1) * 8^m * (1/2)^d) ≤ _
    calc
      _ = (8^m * N) * ((bitSign (φ x.1) * bitSign (φ x'.1)) * (1/2)^d) := by ring
      _ ≤ (8^m * N) * ((1/2)^d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using mul_le_mul_of_nonneg_right hf (show (0 : ℝ) ≤ (1/2)^d by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  exact ⟨hcount, hnear, hc⟩

end PEqualNP.Outside.L_meta_32036_aux.Base

namespace PEqualNP.Outside.L_meta_32036_aux.Packing
open Finset

private theorem gram_expand {A B : Type*} (s : Finset A) (t : Finset B) (f : A → B → ℝ) :
    (∑ y ∈ t, (∑ x ∈ s, f x y)^2) = ∑ x ∈ s, ∑ x' ∈ s, ∑ y ∈ t, f x y * f x' y := by
  simp only [pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  rw [sum_comm]
  apply sum_congr rfl
  intro x' hx'
  exact sum_congr rfl (fun y _ => mul_comm _ _)

/-- The two second moments bound the density of a partition into sets whose
radius-two neighborhoods have small pairwise intersections. -/
theorem packing {A B M : Type} [Fintype A] [Fintype B] [Fintype M]
    [Nonempty A] [Nonempty B] [DecidableEq M]
    (send : A → M) (read : M → B → ℝ) (f : A → B → ℝ)
    (near : A → A → Prop) [∀ x, DecidablePred (near x)]
    (L : ℝ) (hL : 0 ≤ L)
    (hjoint : ∀ j (s : Finset A), s = univ.filter (fun x => send x = j) →
      ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' →
      ((s.filter (fun y => near x y ∧ near x' y)).card : ℝ) ≤ L)
    (hcorr : ∀ x x', (∑ y : B, f x y * f x' y) ≤
      (Fintype.card B : ℝ) * (1/8 + (7/8) * (if near x x' then 1 else 0)))
    (hread : ∀ j y, (read j y)^2 = 1)
    (hscore : (Fintype.card A : ℝ) * Fintype.card B / 2 ≤
      ∑ x : A, ∑ y : B, read (send x) y * f x y) :
    (Fintype.card A : ℝ) ≤ 49 * ((Fintype.card M : ℝ) * (1+L)) := by
  classical
  let s (j : M) := univ.filter (fun x => send x = j)
  let N : ℝ := Fintype.card A
  let Bn : ℝ := Fintype.card B
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hBn : 0 < Bn := by dsimp [Bn]; exact_mod_cast Fintype.card_pos
  let n (j : M) : ℝ := (s j).card
  have hn (j : M) : 0 ≤ n j := by dsimp [n]; positivity
  have hnSum : ∑ j : M, n j = N := by
    simp only [n, s, N, ← Nat.cast_sum, Nat.cast_inj]
    simpa using (sum_card_fiberwise_eq_card_filter (s := (univ : Finset A))
      (t := (univ : Finset M)) (g := send))
  let F (x y : A) : ℝ := if near x y then 1 else 0
  let E (j : M) := ∑ x ∈ s j, ∑ y ∈ s j, F x y
  let w (j : M) := E j / n j
  have hE (j : M) : 0 ≤ E j := by
    apply sum_nonneg; intro x hx; apply sum_nonneg; intro y hy; dsimp [F]; split <;> norm_num
  have hw (j : M) : 0 ≤ w j := div_nonneg (hE j) (hn j)
  have hEn (j : M) : E j = n j * w j := by
    by_cases h : n j = 0
    · have hs : s j = ∅ := card_eq_zero.mp (by dsimp [n] at h; exact_mod_cast h)
      simp [E, hs, h]
    · dsimp [w]; field_simp
  have hwSq (j : M) : w j ^ 2 ≤ n j * (1+L) := by
    by_cases h : n j = 0
    · simp [w, h]
    have hs : ∀ x ∈ s j, ∑ x' ∈ s j, ∑ y ∈ s j, F x y * F x' y ≤ n j * (1+L) := by
      intro x hx
      rw [← insert_erase hx, sum_insert (notMem_erase x (s j))]
      rw [insert_erase hx]
      have hdiag : ∑ y ∈ s j, F x y * F x y ≤ n j := by
        refine (sum_le_sum (g := fun _ => (1 : ℝ)) fun y _ => ?_).trans_eq ?_
        · dsimp [F]; split <;> norm_num
        · simp [n]
      have hoff : ∑ x' ∈ (s j).erase x, ∑ y ∈ s j, F x y * F x' y ≤ n j * L := by
        calc
          _ ≤ ∑ x' ∈ (s j).erase x, L := by
            apply sum_le_sum
            intro x' hx'
            have hh := hjoint j (s j) rfl x hx x' (mem_of_mem_erase hx') (Ne.symm (ne_of_mem_erase hx'))
            convert hh using 1
            calc
              _ = ∑ y ∈ s j, if near x y ∧ near x' y then (1 : ℝ) else 0 := by
                apply sum_congr rfl
                intro y hy
                dsimp [F]
                by_cases h₁ : near x y <;> by_cases h₂ : near x' y <;> simp [h₁, h₂]
              _ = _ := by rw [← sum_filter]; simp [nsmul_eq_mul]
          _ ≤ _ := by
            simp only [sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by dsimp [n]; exact_mod_cast card_le_card (erase_subset x (s j))) hL
      nlinarith
    have hmom : (∑ y ∈ s j, (∑ x ∈ s j, F x y)^2) ≤ n j * (n j * (1+L)) := by
      rw [gram_expand]
      exact (sum_le_sum (fun x hx => hs x hx)).trans_eq (by simp [n, nsmul_eq_mul])
    have hc := sum_mul_sq_le_sq_mul_sq (s j) (fun _ => (1 : ℝ)) (fun y => ∑ x ∈ s j, F x y)
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
    rw [sum_comm] at hc
    have hp : E j ^ 2 ≤ n j ^ 2 * (n j * (1+L)) := by
      calc
        _ ≤ n j * ∑ y ∈ s j, (∑ x ∈ s j, F x y)^2 := hc
        _ ≤ n j * (n j * (n j * (1+L))) := mul_le_mul_of_nonneg_left hmom (hn j)
        _ = _ := by ring
    dsimp [w]
    rw [div_pow, div_le_iff₀ (sq_pos_of_ne_zero h)]
    simpa [mul_comm] using hp
  have hW : (∑ j : M, w j)^2 ≤ (Fintype.card M : ℝ) * (N * (1+L)) := by
    have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset M) (fun _ => (1 : ℝ)) w
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, card_univ] at hc
    refine hc.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact (sum_le_sum fun j _ => hwSq j).trans_eq (by rw [← sum_mul, hnSum])
  let v (j : M) (y : B) := ∑ x ∈ s j, f x y
  let S (j : M) := ∑ y : B, read j y * v j y
  let u (j : M) := n j / 8 + (7/8)*w j
  have hu (j : M) : 0 ≤ u j := by
    exact add_nonneg (div_nonneg (hn j) (by norm_num)) (mul_nonneg (by norm_num) (hw j))
  have hS (j : M) : S j ^ 2 ≤ n j * (Bn^2*u j) := by
    have hgram : ∑ y : B, (v j y)^2 ≤ Bn * (n j * u j) := by
      unfold v
      rw [gram_expand]
      calc
        _ ≤ ∑ x ∈ s j, ∑ x' ∈ s j, Bn * (1/8 + (7/8) * F x x') :=
          sum_le_sum fun x _ => sum_le_sum fun x' _ => hcorr x x'
        _ = _ := by
          simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
          change Bn * (n j * (n j * (1/8)) + 7/8 * E j) = _
          rw [hEn]
          dsimp [u]; ring
    have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (read j) (v j)
    simp only [hread, sum_const, nsmul_eq_mul, mul_one, card_univ] at hc
    calc
      _ ≤ Bn * ∑ y : B, (v j y)^2 := hc
      _ ≤ Bn * (Bn * (n j * u j)) := mul_le_mul_of_nonneg_left hgram hBn.le
      _ = _ := by ring
  have htotal : (∑ j : M, S j)^2 ≤ N * (Bn^2 * (N/8 + (7/8) * ∑ j : M, w j)) := by
    calc
      _ ≤ (∑ j : M, n j) * ∑ j : M, Bn^2 * u j :=
        sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun j _ => hn j)
          (fun j _ => mul_nonneg (sq_nonneg _) (hu j)) (fun j _ => hS j)
      _ = _ := by simp only [u, ← mul_sum, sum_add_distrib, ← sum_div, hnSum]
  have hpartition : ∑ j : M, S j = ∑ x : A, ∑ y : B, read (send x) y * f x y := by
    simp only [S, v, mul_sum, s, sum_filter, mul_ite, mul_zero]
    rw [sum_comm (s := (univ : Finset M)), sum_comm (s := (univ : Finset A))]
    apply sum_congr rfl
    intro y hy
    rw [sum_comm]
    apply sum_congr rfl
    intro x hx
    simp [eq_comm]
  have hpositive : 0 ≤ N * Bn / 2 := by positivity
  have hlow : (N * Bn / 2)^2 ≤ (∑ j : M, S j)^2 :=
    pow_le_pow_left₀ hpositive (hpartition.symm ▸ hscore) _
  have hWlow : N / 7 ≤ ∑ j : M, w j := by
    have hc := hlow.trans htotal
    have hpos : 0 < N * Bn^2 := by positivity
    have hh : (N * Bn^2) * (N/4) ≤ (N * Bn^2) * (N/8 + (7/8) * ∑ j : M, w j) := by
      convert hc using 1 <;> ring
    linarith [(mul_le_mul_iff_right₀ hpos).mp hh]
  have hfinal := (pow_le_pow_left₀ (show 0 ≤ N/7 by positivity) hWlow 2).trans hW
  have hh : N * (N/49) ≤ N * ((Fintype.card M : ℝ) * (1+L)) := by convert hfinal using 1 <;> ring
  linarith [(mul_le_mul_iff_right₀ hN).mp hh]

end PEqualNP.Outside.L_meta_32036_aux.Packing

namespace PEqualNP.Outside.L_meta_32036_aux.Affine

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

def bf (b : Bool) : F := if b then 1 else 0

lemma bf_injective : Function.Injective bf := by
  intro b c h
  cases b <;> cases c <;> simp_all [bf]

private lemma bf_not (b : Bool) : bf (!b) = bf b + 1 := by
  cases b <;> decide

private lemma bf_xor (b c : Bool) : bf (xor b c) = bf b + bf c := by
  cases b <;> cases c <;> decide

noncomputable def paid (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

section Encode

variable {X V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The Boolean observable is an affine function of the given vector-valued encoding. -/
def IsAffine (z : X → V) (f : X → Bool) : Prop :=
  ∃ (L : V →ₗ[F] F) (a : F), ∀ x, bf (f x) = L (z x) + a

private lemma IsAffine.const (z : X → V) (b : Bool) : IsAffine z (fun _ => b) :=
  ⟨0, bf b, by simp⟩

private lemma IsAffine.not {z : X → V} {f : X → Bool} (hf : IsAffine z f) :
    IsAffine z (fun x => !(f x)) := by
  obtain ⟨L, a, h⟩ := hf
  exact ⟨L, a + 1, by intro x; rw [bf_not, h, add_assoc]⟩

private lemma IsAffine.xor {z : X → V} {f g : X → Bool}
    (hf : IsAffine z f) (hg : IsAffine z g) : IsAffine z (fun x => xor (f x) (g x)) := by
  obtain ⟨L, a, h⟩ := hf
  obtain ⟨M, b, h'⟩ := hg
  refine ⟨L + M, a + b, ?_⟩
  intro x
  rw [bf_xor, h, h', LinearMap.add_apply, add_add_add_comm]

private lemma IsAffine.comap {z : X → V} {f : X → Bool} (T : V →ₗ[F] W)
    (hf : IsAffine (fun x => T (z x)) f) : IsAffine z f := by
  obtain ⟨L, a, h⟩ := hf
  exact ⟨L.comp T, a, h⟩

abbrev AffineWires (z : X → V) (w : X → List Bool) : Prop :=
  ∀ i : ℕ, IsAffine z (fun x => (w x).getD i false)

private lemma affineWires_snoc {z : X → V} {w : X → List Bool} {f : X → Bool} {n : ℕ}
    (hn : ∀ x, (w x).length = n) (hw : AffineWires z w) (hf : IsAffine z f) :
    AffineWires z (fun x => w x ++ [f x]) := by
  intro i
  by_cases hlt : i < n
  · convert hw i using 1
    ext x
    rw [List.getD_append _ _ _ _ (by rw [hn]; exact hlt)]
  · by_cases heq : i = n
    · subst i
      convert hf using 1
      ext x
      rw [List.getD_append_right _ _ _ _ (by rw [hn]), hn, Nat.sub_self]
      rfl
    · convert IsAffine.const z false using 1
      ext x
      exact List.getD_eq_default _ _ (by simp [hn]; omega)

private def next (g : Gate) (w : X → List Bool) (x : X) : Bool :=
  g.op.eval (g.inputs.map (fun i => (w x).getD i false))

private def advance (g : Gate) (w : X → List Bool) (x : X) : List Bool :=
  w x ++ [next g w x]

private lemma affine_next {z : X → V} {w : X → List Bool}
    (hw : AffineWires z w) {g : Gate} (hg : allowed g) (hpay : paid g = false) :
    IsAffine z (next g w) := by
  rcases g with ⟨op, is⟩
  have hnandor : ¬ ((op = .and ∨ op = .or) ∧ is.length = 2) := by
    simpa [paid] using hpay
  rcases hg with ⟨hlen, hop⟩
  change is.length ≤ 2 at hlen
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ is.length = 1) at hop
  rcases is with _ | ⟨i, is⟩
  · rcases hop with h | h | h | ⟨h, hh⟩
    · subst op; exact IsAffine.const z true
    · subst op; exact IsAffine.const z false
    · subst op; exact IsAffine.const z true
    · simp at hh
  · rcases is with _ | ⟨j, is⟩
    · rcases hop with h | h | h | ⟨h, _⟩
      · subst op
        change IsAffine z (fun x => (GateOp.and).eval [(w x).getD i false])
        simpa [GateOp.eval] using hw i
      · subst op
        change IsAffine z (fun x => (GateOp.or).eval [(w x).getD i false])
        simpa [GateOp.eval] using hw i
      · subst op
        have hm (b : Bool) : GateOp.eval (.mod 2) [b] = !b := by cases b <;> decide
        change IsAffine z (fun x => (GateOp.mod 2).eval [(w x).getD i false])
        simpa [hm] using (hw i).not
      · subst op
        change IsAffine z (fun x => (GateOp.not).eval [(w x).getD i false])
        simpa [GateOp.eval] using (hw i).not
    · have hz : is = [] := by
        have hlen' : is.length + 1 + 1 ≤ 2 := hlen
        exact List.length_eq_zero_iff.mp (by omega)
      subst is
      rcases hop with h | h | h | ⟨h, hh⟩
      · exact (hnandor ⟨Or.inl h, rfl⟩).elim
      · exact (hnandor ⟨Or.inr h, rfl⟩).elim
      · subst op
        have hm (b c : Bool) : GateOp.eval (.mod 2) [b, c] = !(xor b c) := by
          cases b <;> cases c <;> decide
        change IsAffine z (fun x => (GateOp.mod 2).eval [(w x).getD i false, (w x).getD j false])
        simpa [hm] using ((hw i).xor (hw j)).not
      · simp at hh

private def splitPaid (d : ℕ) :
    (V × (Fin (d + 1) → F)) →ₗ[F] ((V × F) × (Fin d → F)) where
  toFun p := ((p.1, p.2 0), fun j => p.2 j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual outputs of the paid gates, in chronological order. Every gate still updates the
wires, even when its output does not enter this list. -/
noncomputable def paidTrace : List Gate → List Bool → List F
  | [], _ => []
  | g :: gs, w =>
    let b := g.op.eval (g.inputs.map (fun i => w.getD i false))
    let rest := paidTrace gs (w ++ [b])
    if paid g then bf b :: rest else rest

private lemma paidTrace_cons (g : Gate) (gs : List Gate) (w : X → List Bool) (x : X) :
    paidTrace (g :: gs) (w x) =
      if paid g then bf (next g w x) :: paidTrace gs (advance g w x)
      else paidTrace gs (advance g w x) := rfl

private theorem fold_affine (gs : List Gate) :
    ∀ {V : Type*} [AddCommGroup V] [Module F V] (z : X → V) (w : X → List Bool) {n : ℕ},
    (∀ x, (w x).length = n) → AffineWires z w → (∀ g ∈ gs, allowed g) →
    ∃ p : X → (Fin (gs.countP paid) → F),
      (∀ x, List.ofFn (p x) = paidTrace gs (w x)) ∧
      AffineWires (fun x => (z x, p x))
        (fun x => gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]) (w x)) := by
  induction gs with
  | nil =>
      intro V _ _ z w n hn hw hg
      exact ⟨fun _ _ => 0, by simp [paidTrace], fun i => IsAffine.comap (LinearMap.fst F V _) (hw i)⟩
  | cons g gs ih =>
      intro V _ _ z w n hn hw hg
      have hn' (x : X) : (advance g w x).length = n + 1 := by simp [advance, hn]
      have hg' : ∀ h ∈ gs, allowed h := fun h hh => hg h (List.mem_cons_of_mem _ hh)
      by_cases hp : paid g
      · rw [List.countP_cons_of_pos hp]
        let zp : X → V × F := fun x => (z x, bf (next g w x))
        have hw' : AffineWires zp w :=
          fun i => IsAffine.comap (LinearMap.fst F V F) (hw i)
        have hnext : IsAffine zp (next g w) :=
          ⟨LinearMap.snd F V F, 0, by intro x; simp [zp]⟩
        obtain ⟨p, htrace, hp'⟩ := ih zp (advance g w) hn' (affineWires_snoc hn hw' hnext) hg'
        refine ⟨fun x => Fin.cons (bf (next g w x)) (p x), ?_, fun i => ?_⟩
        · intro x
          simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, htrace, paidTrace_cons, hp, ite_eq_left]
        · apply IsAffine.comap (splitPaid (gs.countP paid))
          have he (x : X) : splitPaid (gs.countP paid)
              (z x, Fin.cons (bf (next g w x)) (p x)) = (zp x, p x) := by
            simp [splitPaid, zp, LinearMap.coe_mk, AddHom.coe_mk]
          rw [show (fun x => splitPaid (gs.countP paid) (z x, Fin.cons (bf (next g w x)) (p x))) =
            (fun x => (zp x, p x)) from funext he]
          exact hp' i
      · rw [List.countP_cons_of_neg hp]
        have hnext : IsAffine z (next g w) :=
          affine_next hw (hg g (by simp)) (Bool.eq_false_of_not_eq_true hp)
        obtain ⟨p, htrace, hp'⟩ := ih z (advance g w) hn' (affineWires_snoc hn hw hnext) hg'
        exact ⟨p, fun x => by rw [htrace, paidTrace_cons, ite_eq_right hp], hp'⟩

/-- All tapped outputs are affine over the original input variables and one new variable
per binary AND/OR. Invalid reads use zero, so the gate and tap index bounds are not needed. -/
theorem taps_affine (C : Circuit) {c n : ℕ} (tap : Fin c → ℕ) (raw : X → List Bool)
    (z : X → V) (hn : ∀ x, (raw x).length = n) (hw : AffineWires z raw)
    (hg : ∀ g ∈ C.gates, allowed g) :
    ∃ (p : X → (Fin (C.gates.countP paid) → F))
      (L : (V × (Fin (C.gates.countP paid) → F)) →ₗ[F] (Fin c → F)) (a : Fin c → F),
      (∀ x, List.ofFn (p x) = paidTrace C.gates (raw x)) ∧
      (∀ x j, bf ((C.wires (raw x)).getD (tap j) false) = L (z x, p x) j + a j) := by
  classical
  obtain ⟨p, htrace, hp⟩ := fold_affine C.gates z raw hn hw hg
  choose L a ha using fun j => hp (tap j)
  exact ⟨p, LinearMap.pi L, a, htrace, fun x j => ha j x⟩

/-- Convenient input specialization: each raw bit is affine in the original variables. -/
theorem affineWires_ofFn {z : X → V} {k : ℕ} (raw : X → Fin k → Bool)
    (hw : ∀ i, IsAffine z (fun x => raw x i)) : AffineWires z (fun x => List.ofFn (raw x)) := by
  intro i
  by_cases h : i < k
  · convert hw ⟨i, h⟩ using 1
    ext x
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · convert IsAffine.const z false using 1
    ext x
    exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)

end Encode

section Refinement

variable {D V : Type*} [AddCommGroup D] [Module F D] [FiniteDimensional F D]
  [AddCommGroup V] [Module F V]

/-- Refine any linear `c`-coordinate observation to a surjective observation of the same width.
An offset does not change which points have the same observation. After any linear projection,
each refined class is exactly the translate of one common submodule of dimension at most
`finrank D - c`. -/
theorem affine_refinement {c : ℕ} (hc : c ≤ Module.finrank F D)
    (L : D →ₗ[F] (Fin c → F)) (P : D →ₗ[F] V) :
    ∃ (Q : D →ₗ[F] (Fin c → F)) (U : Submodule F V) (base : (Fin c → F) → V),
      Function.Surjective Q ∧
      Module.finrank F U ≤ Module.finrank F D - c ∧
      (∀ x y, Q x = Q y → L x = L y) ∧
      (∀ q v, (∃ x, Q x = q ∧ P x = v) ↔ v - base q ∈ U) := by
  classical
  have hrank : Module.finrank F (LinearMap.range L) ≤ c := by
    simpa using (LinearMap.range L).finrank_le
  have hs : Module.finrank F D - c ≤ Module.finrank F (LinearMap.ker L) := by
    have h := L.finrank_range_add_finrank_ker
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hs
  let u := fun i => (LinearMap.ker L).subtype (v i)
  have hu : LinearIndependent F u :=
    hv.map' (LinearMap.ker L).subtype (by simp)
  let W : Submodule F D := Submodule.span F (Set.range u)
  have hwk : W ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).property)
  have hW : Module.finrank F W = Module.finrank F D - c := by
    simpa [W] using finrank_span_eq_card hu
  have hq : Module.finrank F (D ⧸ W) = c := by
    have h := W.finrank_quotient_add_finrank
    omega
  let e := (Module.finBasisOfFinrankEq F (D ⧸ W) hq).equivFun
  let Q := e.toLinearMap.comp W.mkQ
  have hQ : Function.Surjective Q := e.surjective.comp W.mkQ_surjective
  have hQ' := hQ
  choose s hs using hQ'
  have hdiff (x y : D) : Q x = Q y ↔ x - y ∈ W := by
    change e (W.mkQ x) = e (W.mkQ y) ↔ _
    exact e.injective.eq_iff.trans (Submodule.Quotient.eq W)
  refine ⟨Q, W.map P, fun q => P (s q), hQ, ?_, ?_, ?_⟩
  · rw [← hW]
    exact W.finrank_map_le P
  · intro x y he
    have hzero : L (x - y) = 0 := hwk ((hdiff x y).mp he)
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  · intro q a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x - s q, (hdiff _ _).mp (hx.trans (hs q).symm), map_sub P _ _⟩
    · rintro ⟨w, hw, hwa⟩
      refine ⟨w + s q, ?_, ?_⟩
      · apply Eq.trans ((hdiff _ _).mpr ?_) (hs q)
        simpa using hw
      · rw [map_add, hwa, sub_add_cancel]

end Refinement

section Pivots

variable {ι E : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F (ι → E)]

/-- At most `dim U` whole coordinates identify a point in any translate of `U`.
The coordinate values themselves may be vectors (e.g., three-bit symbols). -/
theorem affine_pivots (U : Submodule F (ι → E)) :
    ∃ s : Finset ι, s.card ≤ Module.finrank F U ∧
      ∀ (a x y : ι → E), x - a ∈ U → y - a ∈ U →
        (∀ i ∈ s, x i = y i) → x = y := by
  classical
  suffices h : ∃ s : Finset ι, s.card ≤ Module.finrank F U ∧
      ∀ x ∈ U, (∀ i ∈ s, x i = 0) → x = 0 by
    obtain ⟨s, hs, h⟩ := h
    refine ⟨s, hs, ?_⟩
    intro a x y hx hy he
    have hd : x - y ∈ U := by
      convert U.sub_mem hx hy using 1
      abel
    exact sub_eq_zero.mp (h (x - y) hd (fun i hi => sub_eq_zero.mpr (he i hi)))
  generalize hn : Module.finrank F U = n
  induction n using Nat.strong_induction_on generalizing U with
  | ind n ih =>
    by_cases hb : U = ⊥
    · refine ⟨∅, by simp, ?_⟩
      intro x hx _
      simpa [hb] using hx
    have ⟨x, hx, hx0⟩ : ∃ x ∈ U, x ≠ (0 : ι → E) := by
      by_contra! h
      exact hb (le_antisymm (fun y hy => by simpa using h y hy) bot_le)
    have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx0 (funext h)
    let U' := U ⊓ LinearMap.ker (LinearMap.proj i)
    have hlt : U' < U := lt_of_le_of_ne inf_le_left (by
      intro h
      have hx' : x ∈ U' := h.symm ▸ hx
      exact hi hx'.2)
    have hdim : Module.finrank F U' < n := by
      rw [← hn]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨s, hcard, hs⟩ := ih _ hdim U' rfl
    refine ⟨insert i s, (Finset.card_insert_le i s).trans (by omega), ?_⟩
    intro y hy hzero
    have hy' : y ∈ U' := ⟨hy, hzero i (Finset.mem_insert_self i s)⟩
    exact hs y hy' (fun j hj => hzero j (Finset.mem_insert_of_mem hj))

end Pivots

/-- The original tapped message is constant on each refined class. Each such class is
contained in an affine parent of dimension bounded by the input dimension plus the number of
paid gates minus the message width. -/
theorem taps_affine_parents {X V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (C : Circuit) {c n : ℕ} (tap : Fin c → ℕ) (raw : X → List Bool) (z : X → V)
    (hn : ∀ x, (raw x).length = n) (hw : AffineWires z raw)
    (hg : ∀ g ∈ C.gates, allowed g) (hc : c ≤ Module.finrank F V + C.gates.countP paid) :
    ∃ (label : X → Fin c → F) (U : Submodule F V) (base : (Fin c → F) → V),
      Module.finrank F U ≤ Module.finrank F V + C.gates.countP paid - c ∧
      (∀ x y, label x = label y →
        (fun j => (C.wires (raw x)).getD (tap j) false) =
        (fun j => (C.wires (raw y)).getD (tap j) false)) ∧
      (∀ x, z x - base (label x) ∈ U) := by
  obtain ⟨p, L, a, _, ha⟩ := taps_affine C tap raw z hn hw hg
  let d := C.gates.countP paid
  have hd : Module.finrank F (V × (Fin d → F)) = Module.finrank F V + d := by
    simp [Module.finrank_prod]
  have hc' : c ≤ Module.finrank F (V × (Fin d → F)) := by rwa [hd]
  obtain ⟨Q, U, base, _, hU, hL, hP⟩ := affine_refinement hc' L (LinearMap.fst F V _)
  refine ⟨fun x => Q (z x, p x), U, base, ?_, ?_, ?_⟩
  · simpa only [hd] using hU
  · intro x y h
    have hxy := hL (z x, p x) (z y, p y) h
    funext j
    apply bf_injective
    rw [ha x j, ha y j, hxy]
  · intro x
    exact (hP _ _).mp ⟨(z x, p x), rfl, rfl⟩

/-- Specialization to an input encoding by `m` blocks of `t` bits. A common set of at most
`m*t + cost - c` block positions separates the encoded points in every refined message class. -/
theorem taps_block_pivots {X : Type*} (C : Circuit) {c k m t : ℕ} (tap : Fin c → ℕ)
    (raw : X → Fin k → Bool) (z : X → Fin m → Fin t → F)
    (hw : ∀ i, IsAffine z (fun x => raw x i))
    (hg : ∀ g ∈ C.gates, allowed g) (hc : c ≤ m * t + C.gates.countP paid) :
    ∃ (label : X → Fin c → F) (S : Finset (Fin m)),
      S.card ≤ m * t + C.gates.countP paid - c ∧
      (∀ x y, label x = label y →
        (fun j => (C.wires (List.ofFn (raw x))).getD (tap j) false) =
        (fun j => (C.wires (List.ofFn (raw y))).getD (tap j) false)) ∧
      (∀ x y, label x = label y → (∀ i ∈ S, z x i = z y i) → z x = z y) := by
  have hv : Module.finrank F (Fin m → Fin t → F) = m * t := by
    rw [Module.finrank_pi_fintype]
    simp
  obtain ⟨label, U, base, hU, hlabel, hbase⟩ := taps_affine_parents C (n := k) tap
    (fun x => List.ofFn (raw x)) z (by simp) (affineWires_ofFn raw hw) hg (by rwa [hv])
  obtain ⟨S, hS, hpivot⟩ := affine_pivots U
  refine ⟨label, S, by simpa only [hv] using hS.trans hU, hlabel, ?_⟩
  intro x y he hs
  exact hpivot (base (label x)) (z x) (z y) (hbase x) (he ▸ hbase y) hs

theorem label_card (c : ℕ) : Fintype.card (Fin c → F) = 2 ^ c := by
  simp [ZMod.card]

end PEqualNP.Outside.L_meta_32036_aux.Affine

namespace PEqualNP.Outside.L_meta_32036_aux.Intersection

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def dist (x y : ι → Fin 8) : Nat := by
  classical
  exact (univ.filter fun i => x i ≠ y i).card

theorem dist_project_le (e : κ ↪ ι) (x y : ι → Fin 8) :
    dist (x ∘ e) (y ∘ e) ≤ dist x y := by
  classical
  unfold dist
  exact card_le_card_of_injOn e (by simp [Set.MapsTo])
    e.injective.injOn
variable [DecidableEq ι] [DecidableEq κ]


/-- A fixed differing coordinate consumes one of the two allowed changes to one center.
The point is encoded by its value there and a single optional overwrite of that center. -/
theorem intersection_card (a b : ι → Fin 8) (hab : a ≠ b) :
    ((univ : Finset (ι → Fin 8)).filter fun x => dist x a ≤ 2 ∧ dist x b ≤ 2).card ≤
      64 * Fintype.card ι := by
  classical
  have hp : ∃ p, a p ≠ b p := by
    by_contra! hn
    exact hab (funext hn)
  obtain ⟨p, hp⟩ := hp
  let encode : Fin 8 × ι × Fin 8 → (ι → Fin 8) := fun (v, j, w) i =>
    if i = p then v else if i = j then w else if v = a p then b i else a i
  refine (card_le_card (t := univ.image encode) ?_).trans (card_image_le.trans ?_)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    let c := if x p = a p then b else a
    have hpc : x p ≠ c p := by
      by_cases h : x p = a p
      · simpa [c, h] using hp
      · simp [c, h]
    have hcx : dist x c ≤ 2 := by
      dsimp [c]
      split_ifs
      · exact hx.2
      · exact hx.1
    change (univ.filter fun i => x i ≠ c i).card ≤ 2 at hcx
    have hone (j : ι) (hjp : j ≠ p) (hj : x j ≠ c j) (i : ι)
        (hip : i ≠ p) (hij : i ≠ j) : x i = c i := by
      by_contra hi
      have hsub : ({i, j, p} : Finset ι) ⊆ univ.filter (fun k => x k ≠ c k) := by
        intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all
      have hc := card_le_card hsub
      have h3 : ({i, j, p} : Finset ι).card = 3 := by simp [hij, hip, hjp]
      rw [h3] at hc
      exact (by omega : False)
    by_cases h : ∃ j, j ≠ p ∧ x j ≠ c j
    · obtain ⟨j, hjp, hj⟩ := h
      refine mem_image.mpr ⟨(x p, j, x j), mem_univ _, funext fun i => ?_⟩
      by_cases hip : i = p
      · simp [encode, hip]
      by_cases hij : i = j
      · subst i
        simp [encode, hjp]
      · have he := (hone j hjp hj i hip hij).symm
        by_cases hv : x p = a p <;> simpa [encode, hip, hij, c, hv] using he
    · push Not at h
      refine mem_image.mpr ⟨(x p, p, x p), mem_univ _, funext fun i => ?_⟩
      by_cases hip : i = p
      · simp [encode, hip]
      · have he := (h i hip).symm
        by_cases hv : x p = a p <;> simpa [encode, hip, c, hv] using he
  · simp [Fintype.card_prod]
    omega

omit [DecidableEq ι] in
/-- Projection need only be injective on the candidate set, not on the ambient space. -/
theorem projected_intersection_card (s : Finset (ι → Fin 8)) (e : κ ↪ ι)
    (a b : ι → Fin 8) (hab : a ∘ e ≠ b ∘ e)
    (hinj : Set.InjOn (fun x : ι → Fin 8 => x ∘ e) (s : Set (ι → Fin 8))) :
    (s.filter fun x => dist x a ≤ 2 ∧ dist x b ≤ 2).card ≤ 112 * Fintype.card κ := by
  classical
  refine (card_le_card_of_injOn (t := univ.filter fun x =>
    dist x (a ∘ e) ≤ 2 ∧ dist x (b ∘ e) ≤ 2) (fun x => x ∘ e) ?_ ?_).trans
      ((intersection_card _ _ hab).trans (Nat.mul_le_mul_right _ (by decide)))
  · intro x hx
    have h := (mem_filter.mp (show x ∈ s.filter _ from hx)).2
    exact mem_filter.mpr ⟨mem_univ _, (dist_project_le e x a).trans h.1,
      (dist_project_le e x b).trans h.2⟩
  · exact hinj.mono (fun _ h => (mem_filter.mp (show _ ∈ s.filter _ from h)).1)

end PEqualNP.Outside.L_meta_32036_aux.Intersection

namespace PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit
open PEqualNP.CircuitLowerBounds

noncomputable section
open Classical

def legal (k : Nat) (C : Circuit) : Prop :=
  (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < k+i.val) ∧
  (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

def charge (h : Gate) : Bool := @decide
  ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

def cost (C : Circuit) : Nat := C.gates.countP charge

def circ (gs : List Gate) : Circuit := ⟨gs, 0⟩

def run {k : Nat} (gs : List Gate) (x : Fin k → Bool) := (circ gs).wires (List.ofFn x)

def Has {k : Nat} (gs : List Gate) (w : Nat) (f : (Fin k → Bool) → Bool) : Prop :=
  w < k + gs.length ∧ ∀ x, (run gs x).getD w false = f x

def Ready {k : Nat} (gs : List Gate) (f : (Fin k → Bool) → Bool) : Prop := ∃ w, Has gs w f

def Ext (k : Nat) (gs hs : List Gate) (d : Nat) : Prop :=
  gs <+: hs ∧ legal k (circ hs) ∧ cost (circ hs) ≤ cost (circ gs) + d

private theorem run_length {k : Nat} (gs : List Gate) (x : Fin k → Bool) :
    (run gs x).length = k + gs.length := by
  have aux (gs : List Gate) (xs : List Bool) : ((circ gs).wires xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp [circ, Circuit.wires]
    | cons g gs ih =>
      change ((circ gs).wires (xs ++ [_])).length = _
      rw [ih]
      simp; omega
  simp [run, aux]

private theorem prefix_run {k : Nat} {gs hs : List Gate} (h : gs <+: hs) (x : Fin k → Bool) :
    run gs x <+: run hs x := by
  obtain ⟨ts, rfl⟩ := h
  suffices ∀ (ts : List Gate) (xs : List Bool), xs <+: (circ ts).wires xs by
    simpa [run, circ, Circuit.wires, List.foldl_append] using this ts (run gs x)
  intro ts
  induction ts with
  | nil => intro xs; exact List.prefix_rfl
  | cons t ts ih =>
    intro xs
    change xs <+: (circ ts).wires (xs ++ [_])
    exact (List.prefix_append _ _).trans (ih _)

private theorem has_mono {k : Nat} {gs hs : List Gate} {w f} (p : gs <+: hs)
    (h : @Has k gs w f) : Has hs w f := by
  refine ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left p.length_le _), fun x => ?_⟩
  obtain ⟨zs, hz⟩ := prefix_run p x
  rw [← hz, List.getD_append _ _ _ _ (by simpa [run_length] using h.1)]
  exact h.2 x

private theorem ready_mono {k : Nat} {gs hs : List Gate} {f} (p : gs <+: hs)
    (h : @Ready k gs f) : Ready hs f := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, has_mono p hw⟩

private theorem Ext.refl {k gs} (h : legal k (circ gs)) : Ext k gs gs 0 :=
  ⟨List.prefix_rfl, h, by simp⟩

private theorem Ext.trans {k gs hs is d e} (h : Ext k gs hs d) (i : Ext k hs is e) :
    Ext k gs is (d+e) :=
  ⟨h.1.trans i.1, i.2.1, by have := h.2.2; have := i.2.2; omega⟩

private theorem append_one {k gs} (hl : legal k (circ gs)) (g : Gate)
    (hb : ∀ w ∈ g.inputs, w < k+gs.length)
    (hx : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    Ext k gs (gs ++ [g]) (if charge g then 1 else 0) ∧
    @Has k (gs ++ [g]) (k+gs.length) (fun x => g.op.eval (g.inputs.map fun w => (run gs x).getD w false)) := by
  constructor
  · refine ⟨List.prefix_append _ _, ⟨?_, ?_⟩, ?_⟩
    · intro i w hw
      have hlt : i.val < (gs ++ [g]).length := i.isLt
      change w ∈ ((gs ++ [g])[i.val]'hlt).inputs at hw
      by_cases hi : i.val < gs.length
      · rw [List.getElem_append_left hi] at hw
        exact hl.1 ⟨i.val, hi⟩ _ hw
      · have he : i.val = gs.length := by simp at hlt; omega
        have hn : gs.length ≤ i.val := by omega
        have hh : w ∈ g.inputs := by
          simpa [List.getElem_append_right hn, show i.val - gs.length = 0 by omega] using hw
        exact he ▸ hb w hh
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact hl.2 h hh
      · obtain rfl := List.mem_singleton.mp hh
        exact hx
    · simp [cost, circ, List.countP_append, List.countP_cons]
  · refine ⟨by simp, fun x => ?_⟩
    have he : run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun w => (run gs x).getD w false)] := by
      simp [run, circ, Circuit.wires, List.foldl_append]
    rw [he, List.getD_append_right _ _ _ _ (by simp [run_length]), run_length, Nat.sub_self]
    rfl

private theorem emit {k gs} (hl : legal k (circ gs)) (op : GateOp)
    (args : List ((Fin k → Bool) → Bool))
    (ha : ∀ f ∈ args, Ready gs f)
    (hx : args.length ≤ 2 ∧
      (op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ args.length = 1))) :
    ∃ hs, Ext k gs hs (if op = .and ∨ op = .or then (if args.length = 2 then 1 else 0) else 0) ∧
      Ready hs (fun x => op.eval (args.map fun f => f x)) := by
  let ws := args.attach.map fun f => (ha f.val f.property).choose
  have len : ws.length = args.length := by simp [ws]
  have bound : ∀ w ∈ ws, w < k+gs.length := by
    intro w hw
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hw
    exact (ha f.val f.property).choose_spec.1
  obtain ⟨he, h⟩ := append_one hl ⟨op, ws⟩ bound (by simpa [len] using hx)
  have hg : (if charge ⟨op, ws⟩ then 1 else 0) =
      (if op = .and ∨ op = .or then (if args.length = 2 then 1 else 0) else 0) := by
    by_cases hh : op = .and ∨ op = .or <;> by_cases hh' : args.length = 2 <;> simp [charge, len, hh, hh']
  refine ⟨_, hg ▸ he, _, h.1, fun x => (h.2 x).trans ?_⟩
  apply congrArg (GateOp.eval op)
  simp only [ws, List.map_map]
  calc
    _ = args.attach.map (fun f => f.val x) := by
      apply List.map_congr_left
      intro f _
      exact (ha f.val f.property).choose_spec.2 x
    _ = _ := List.attach_map_val (l := args) (f := fun f => f x)


def parity (xs : List Bool) : Bool := xs.foldr xor false

private theorem emit_xor {k gs} (hl : legal k (circ gs))
    {f g : (Fin k → Bool) → Bool} (hf : Ready gs f) (hg : Ready gs g) :
    ∃ hs, Ext k gs hs 0 ∧ Ready hs (fun x => xor (f x) (g x)) := by
  obtain ⟨hs, he, hr⟩ := emit hl (.mod 2) [f,g] (by simpa using And.intro hf hg) (by simp)
  have ht : ∀ a b : Bool, GateOp.eval (.mod 2) [a,b] = !(xor a b) := by decide
  simp only [List.map_cons, List.map_nil, ht] at hr
  obtain ⟨is, hi, hf⟩ := emit he.2.1 .not [fun x => !(xor (f x) (g x))] (by simpa) (by simp)
  exact ⟨is, by simpa using he.trans hi, by simpa [GateOp.eval] using hf⟩

private theorem emit_and {k gs} (hl : legal k (circ gs))
    {f g : (Fin k → Bool) → Bool} (hf : Ready gs f) (hg : Ready gs g) :
    ∃ hs, Ext k gs hs 1 ∧ Ready hs (fun x => f x && g x) := by
  simpa [GateOp.eval] using emit hl .and [f,g] (by simpa using And.intro hf hg) (by simp)

private theorem emit_not {k gs} (hl : legal k (circ gs))
    {f : (Fin k → Bool) → Bool} (hf : Ready gs f) :
    ∃ hs, Ext k gs hs 0 ∧ Ready hs (fun x => !(f x)) := by
  simpa [GateOp.eval] using emit hl .not [f] (by simpa) (by simp)

private theorem emit_parity {k gs} (hl : legal k (circ gs))
    (fs : List ((Fin k → Bool) → Bool)) (hf : ∀ f ∈ fs, Ready gs f) :
    ∃ hs, Ext k gs hs 0 ∧ Ready hs (fun x => parity (fs.map fun f => f x)) := by
  induction fs generalizing gs with
  | nil =>
    simpa [GateOp.eval, parity] using emit hl .or ([] : List ((Fin k → Bool) → Bool)) (by simp) (by simp)
  | cons f fs ih =>
    obtain ⟨hs, he, hr⟩ := ih hl (fun g hg => hf g (List.mem_cons_of_mem _ hg))
    obtain ⟨is, hi, hw⟩ := emit_xor he.2.1 (ready_mono he.1 (hf f (by simp))) hr
    exact ⟨is, by simpa using he.trans hi, hw⟩

private theorem emit_family {α : Type} {k d : Nat} {gs : List Gate} (hl : legal k (circ gs))
    (is : Finset α) (f : α → (Fin k → Bool) → Bool)
    (hf : ∀ hs, Ext k gs hs (d * is.card) → ∀ a ∈ is,
      ∃ js, Ext k hs js d ∧ Ready js (f a)) :
    ∃ hs, Ext k gs hs (d * is.card) ∧ ∀ a ∈ is, Ready hs (f a) := by
  induction is using Finset.induction_on with
  | empty => exact ⟨gs, by simpa using Ext.refl hl, by simp⟩
  | @insert a is ha ih =>
    have hm : d * is.card ≤ d * (insert a is).card := Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.subset_insert _ _))
    obtain ⟨hs, he, hr⟩ := ih (fun hs hh b hb => hf hs ⟨hh.1, hh.2.1, by have := hh.2.2; omega⟩ b (Finset.mem_insert_of_mem hb))
    obtain ⟨js, hj, hw⟩ := hf hs ⟨he.1, he.2.1, by have := he.2.2; omega⟩ a (Finset.mem_insert_self _ _)
    refine ⟨js, by simpa [Finset.card_insert_of_notMem ha, Nat.mul_add] using he.trans hj, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hw
    · exact ready_mono hj.1 (hr b hb)

private theorem parity_eq_mem {α : Type} [DecidableEq α] (a : α) {xs : List α}
    (hn : xs.Nodup) : parity (xs.map fun b => decide (a = b)) = decide (a ∈ xs) := by
  induction xs with
  | nil => simp [parity]
  | cons b xs ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons, parity, List.foldr_cons]
    change xor (decide (a = b)) (parity (xs.map fun b => decide (a = b))) = _
    rw [ih hn'.2]
    by_cases h : a = b
    · subst b; simp [hn'.1]
    · simp [h]


private theorem budget_step (s : Nat) :
    (2^s-s-1) + (2^s-1) = 2^(s+1)-(s+1)-1 := by
  have hp : s+1 ≤ (2 : Nat)^s := by
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ]; omega
  rw [pow_succ]
  omega

-- For each nonzero lower pattern, one AND computes its high branch.
-- The high zero branch is recovered by parity, and every low branch by XOR.
private theorem emit_indicators {k s gs} (hl : legal k (circ gs))
    (σ : Fin s → (Fin k → Bool) → Bool)
    (hσ : ∀ i, Ready gs (σ i)) :
    ∃ hs, Ext k gs hs (2^s-s-1) ∧
      ∀ a : Fin s → Bool, Ready hs (fun x => decide ((fun i => σ i x) = a)) := by
  induction s generalizing gs with
  | zero =>
    obtain ⟨hs, he, hr⟩ := emit hl .and ([] : List ((Fin k → Bool) → Bool)) (by simp) (by simp)
    refine ⟨hs, by simpa using he, fun a => ?_⟩
    have ht : ∀ x : Fin k → Bool, (fun i => σ i x) = a := fun x => Subsingleton.elim _ _
    simpa [GateOp.eval, ht] using hr
  | succ s ih =>
    let σ' (x : Fin k → Bool) (i : Fin s) := σ i.succ x
    let bit := σ 0
    let L := Fin s → Bool
    let z : L := fun _ => false
    let nonzero : Finset L := Finset.univ.erase z
    let lo (a : L) (x : Fin k → Bool) := decide (σ' x = a)
    let hi (a : L) (x : Fin k → Bool) := bit x && lo a x
    let rest (a : L) (x : Fin k → Bool) := xor (lo a x) (hi a x)
    obtain ⟨hs, he, hlo⟩ := ih hl (fun i => σ i.succ) (fun i => hσ i.succ)
    change ∀ a : L, Ready hs (lo a) at hlo
    obtain ⟨js, hj, hhi⟩ := emit_family (d := 1) he.2.1 nonzero hi (by
      intro ts ht a _
      exact emit_and ht.2.1 (ready_mono (he.1.trans ht.1) (hσ 0)) (ready_mono ht.1 (hlo a)))
    obtain ⟨ps, hp, hpar⟩ := emit_parity hj.2.1 (nonzero.toList.map hi) (by
      intro f hf
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
      exact hhi a (by simpa using ha))
    obtain ⟨zs, hz, hz0⟩ := emit_xor hp.2.1 (ready_mono (he.1.trans (hj.1.trans hp.1)) (hσ 0)) hpar
    have hzval (x : Fin k → Bool) :
        xor (bit x) (parity ((nonzero.toList.map hi).map fun f => f x)) = hi z x := by
      rw [List.map_map]
      change xor (bit x) (parity (nonzero.toList.map fun a => hi a x)) = hi z x
      by_cases hb : bit x = true
      · simp only [hi, hb, Bool.true_and, lo]
        rw [parity_eq_mem _ nonzero.nodup_toList]
        simp [nonzero]
      · have hf : bit x = false := Bool.eq_false_of_not_eq_true hb
        have hz' (xs : List L) : parity (xs.map fun _ => false) = false := by
          induction xs with
          | nil => rfl
          | cons a xs ih => simpa [parity] using ih
        simpa [hi, hf] using hz' nonzero.toList
    have hhiall (a : L) : Ready zs (hi a) := by
      by_cases ha : a = z
      · subst a
        exact (funext hzval) ▸ hz0
      · exact ready_mono (hp.1.trans hz.1) (hhi a (by simp [nonzero, ha]))
    obtain ⟨ts, ht, hrest⟩ := emit_family (d := 0) hz.2.1 Finset.univ rest (by
      intro us hu a _
      exact emit_xor hu.2.1
        (ready_mono (hj.1.trans (hp.1.trans (hz.1.trans hu.1))) (hlo a))
        (ready_mono hu.1 (hhiall a)))
    have hcard : nonzero.card = 2^s-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ z)]
      simp [L]
    refine ⟨ts, ?_, fun a => ?_⟩
    · have h := he.trans (hj.trans (hp.trans (hz.trans ht)))
      simpa [hcard, budget_step] using h
    · let b : L := fun i => a i.succ
      have heq (x : Fin k → Bool) :
          ((fun i => σ i x) = a) ↔ bit x = a 0 ∧ σ' x = b := by
        constructor
        · intro h
          exact ⟨congrFun h 0, funext fun i => congrFun h i.succ⟩
        · rintro ⟨h, h'⟩
          funext i
          exact Fin.cases h (fun i => congrFun h' i) i
      cases ha : a 0
      · have hw (x : Fin k → Bool) : rest b x = decide ((fun i => σ i x) = a) := by
          simp only [heq, ha, rest, hi, lo]
          cases bit x <;> by_cases h : σ' x = b <;> simp [h]
        exact (funext hw) ▸ hrest b (Finset.mem_univ _)
      · have hw (x : Fin k → Bool) : hi b x = decide ((fun i => σ i x) = a) := by
          simp only [heq, ha, hi, lo]
          cases bit x <;> by_cases h : σ' x = b <;> simp [h]
        exact (funext hw) ▸ ready_mono ht.1 (hhiall b)

private theorem raw_ready {k : Nat} (gs : List Gate) (i : Fin k) :
    Ready gs (fun x => x i) := by
  apply ready_mono (gs := []) List.nil_prefix
  refine ⟨i.val, by simp, fun x => ?_⟩
  simp [run, circ, Circuit.wires, List.getD_eq_getElem?_getD]

private theorem emit_raw_parity {k gs} (hl : legal k (circ gs)) (xs : List (Fin k)) :
    ∃ hs, Ext k gs hs 0 ∧ Ready hs (fun x => parity (xs.map x)) := by
  obtain ⟨hs, he, hr⟩ := emit_parity hl (xs.map fun i x => x i) (by
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact raw_ready gs i)
  exact ⟨hs, he, by simpa [List.map_map, Function.comp_def] using hr⟩

def corrected {k s : Nat} (σ : Fin s → List (Fin k)) (label : Option (Fin s → Bool))
    (i : Fin k) (x : Fin k → Bool) : Bool :=
  match label with
  | none => x i
  | some a => xor (x i) (decide ((fun j => parity ((σ j).map x)) = a))

/-- A parity-syndrome encoder. Padding coordinates with no label remain unchanged. -/
theorem encoder {k s c : Nat} (σ : Fin s → List (Fin k)) (label : Fin c → Option (Fin s → Bool))
    (sel : Fin c → Fin k) (extra : List (Fin k)) :
    ∃ (C : Circuit) (tap : Fin c → Nat) (t : Nat),
      legal k C ∧ cost C ≤ 2^s-s-1 ∧
      (∀ j, tap j < k+C.gates.length) ∧ t < k+C.gates.length ∧
      (∀ (x : Fin k → Bool) j, (C.wires (List.ofFn x)).getD (tap j) false =
        corrected σ (label j) (sel j) x) ∧
      (∀ x : Fin k → Bool, (C.wires (List.ofFn x)).getD t false = parity (extra.map x)) := by
  have h0 : legal k (circ []) := by
    constructor
    · intro i; exact i.elim0
    · simp [circ]
  obtain ⟨gs, hg, hσ⟩ := emit_family (d := 0) h0 Finset.univ
    (fun i (x : Fin k → Bool) => parity ((σ i).map x)) (fun _ h i _ => emit_raw_parity h.2.1 (σ i))
  obtain ⟨hs, hh, hall⟩ := emit_indicators hg.2.1 _ (fun i => hσ i (Finset.mem_univ i))
  obtain ⟨js, hj, ht⟩ := emit_raw_parity hh.2.1 extra
  obtain ⟨ps, hp, htaps⟩ := emit_family (d := 0) hj.2.1 Finset.univ
    (fun i => corrected σ (label i) (sel i)) (by
      intro qs hq i _
      cases h : label i with
      | none => exact ⟨qs, Ext.refl hq.2.1, raw_ready qs (sel i)⟩
      | some a =>
        exact emit_xor hq.2.1 (raw_ready qs (sel i))
          (ready_mono (hj.1.trans hq.1) (hall a)))
  have htaps' (j : Fin c) := (htaps j (Finset.mem_univ _)).choose_spec
  obtain ⟨t, he⟩ := ready_mono hp.1 ht
  refine ⟨circ ps, fun j => (htaps j (Finset.mem_univ _)).choose, t, hp.2.1, ?_,
    fun j => (htaps' j).1, he.1, fun x j => (htaps' j).2 x, he.2⟩
  have h := (hg.trans (hh.trans (hj.trans hp))).2.2
  simpa [cost, circ] using h

end
end PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit

namespace PEqualNP.Outside.L_meta_32036_aux.SyndromeModel

open Finset
open scoped BigOperators

abbrev Word (I : Type) := I → ZMod 2

/-- Syndrome matrix with its identity columns first. -/
noncomputable def systematic {P D : Type} [Fintype D] (labels : D → Word P)
    (x : Word (P ⊕ D)) : Word P :=
  fun p => x (.inl p) + ∑ j, x (.inr j) * labels j p

noncomputable def rebuild {P D : Type} [Fintype D] (labels : D → Word P)
    (data : Word D) (syn : Word P) : Word (P ⊕ D) :=
  Sum.elim (fun p => syn p - ∑ j, data j * labels j p) data

@[simp] theorem systematic_rebuild {P D : Type} [Fintype D] (labels : D → Word P)
    (data : Word D) (syn : Word P) : systematic labels (rebuild labels data syn) = syn := by
  funext p
  simp [systematic, rebuild]

/-- Every syndrome fiber has the same freely specified data bits. -/
noncomputable def systematicEquiv {P D : Type} [Fintype D] (labels : D → Word P) :
    Word (P ⊕ D) ≃ Word D × Word P where
  toFun x := (fun j => x (.inr j), systematic labels x)
  invFun x := rebuild labels x.1 x.2
  left_inv x := by
    funext j
    cases j <;> simp [systematic, rebuild]
  right_inv x := by
    apply Prod.ext
    · rfl
    · exact systematic_rebuild labels x.1 x.2

noncomputable def syndromeFiber {P D : Type} [Fintype D] (labels : D → Word P)
    (syn : Word P) : {x : Word (P ⊕ D) // systematic labels x = syn} ≃ Word D where
  toFun x j := x.val (.inr j)
  invFun data := ⟨rebuild labels data syn, systematic_rebuild labels data syn⟩
  left_inv x := by
    apply Subtype.ext
    change rebuild labels (fun j => x.val (.inr j)) syn = x.val
    exact (congrArg (rebuild labels (fun j => x.val (.inr j))) x.property).symm.trans
      ((systematicEquiv labels).left_inv x.val)
  right_inv _ := rfl

namespace Systematic

variable {P D : Type} [Fintype D] [Fintype P] [DecidableEq P] [DecidableEq D]

noncomputable def unit (i : P) : Word P := fun p => if p = i then 1 else 0

noncomputable def columns (labels : D → Word P) : P ⊕ D → Word P :=
  Sum.elim unit labels

noncomputable def flip (x : Word (P ⊕ D)) (j : P ⊕ D) : Word (P ⊕ D) :=
  fun i => x i + if i = j then 1 else 0

 theorem systematic_flip (labels : D → Word P) (x : Word (P ⊕ D)) (j : P ⊕ D) :
    systematic labels (flip x j) = systematic labels x + columns labels j := by
  classical
  funext p
  cases j with
  | inl j => simp [systematic, flip, columns, unit]; ring
  | inr j => simp [systematic, flip, columns, add_mul, Finset.sum_add_distrib, add_assoc]

/-- The correcting operation; the indicator implementation is proved below. -/
noncomputable def correct (labels : D → Word P) (x : Word (P ⊕ D)) : Word (P ⊕ D) := by
  classical
  exact if h : systematic labels x ≠ 0 ∧ ∃ j, columns labels j = systematic labels x
    then flip x (Classical.choose h.2) else x

theorem correct_data (labels : D → Word P)
    (hinj : ∀ i j, columns labels i ≠ 0 → columns labels i = columns labels j → i = j)
    (x : Word (P ⊕ D)) (j : D) :
    correct labels x (.inr j) = x (.inr j) +
      if systematic labels x ≠ 0 ∧ systematic labels x = labels j then 1 else 0 := by
  classical
  unfold correct
  split
  next h =>
    have hc := Classical.choose_spec h.2
    have he : (Sum.inr j = Classical.choose h.2) ↔
        (systematic labels x ≠ 0 ∧ systematic labels x = labels j) := by
      constructor
      · intro he
        rw [← he] at hc
        exact ⟨h.1, hc.symm⟩
      · rintro ⟨hn, he⟩
        apply hinj (Sum.inr j) (Classical.choose h.2)
          (show labels j ≠ 0 from he ▸ hn)
        exact he.symm.trans hc.symm
    simp only [flip, he]
  next h =>
    have hn : ¬(systematic labels x ≠ 0 ∧ systematic labels x = labels j) := by
      rintro ⟨hn, he⟩
      exact h ⟨hn, .inr j, he.symm⟩
    simp [hn]

theorem correct_changes_one (labels : D → Word P) (x : Word (P ⊕ D)) :
    correct labels x = x ∨ ∃ j, ∀ i, i ≠ j → correct labels x i = x i := by
  classical
  unfold correct
  split
  next h => exact Or.inr ⟨Classical.choose h.2, fun i hi => by simp [flip, hi]⟩
  next _ => exact Or.inl rfl

theorem systematic_correct (labels : D → Word P)
    (hcover : ∀ syn : Word P, syn ≠ 0 → ∃ j, columns labels j = syn)
    (x : Word (P ⊕ D)) : systematic labels (correct labels x) = 0 := by
  classical
  unfold correct
  split
  next h =>
    rw [systematic_flip, Classical.choose_spec h.2]
    funext p
    change systematic labels x p + systematic labels x p = 0
    exact CharTwo.add_self_eq_zero _
  next h => exact Classical.not_not.mp fun hn => h ⟨hn, hcover _ hn⟩

 theorem reconstruct_correct (labels : D → Word P)
    (hcover : ∀ syn : Word P, syn ≠ 0 → ∃ j, columns labels j = syn)
    (x : Word (P ⊕ D)) :
    rebuild labels (fun j => correct labels x (.inr j)) 0 = correct labels x := by
  exact (syndromeFiber labels 0).left_inv ⟨correct labels x, systematic_correct labels hcover x⟩
    |> congrArg Subtype.val

theorem exists_labels (s d : ℕ) (hsize : 2^s ≤ s+d+1) :
    ∃ labels : Fin d → Word (Fin s),
      (∀ i j, columns labels i ≠ 0 → columns labels i = columns labels j → i = j) ∧
      (∀ syn : Word (Fin s), syn ≠ 0 → ∃ j, columns labels j = syn) := by
  classical
  let units : Option (Fin s) ↪ Word (Fin s) :=
    ⟨fun o => o.elim 0 unit, by
      intro a b h
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          have he := congrFun h b
          simp [unit] at he
      | some a =>
        cases b with
        | none =>
          have he := congrFun h a
          simp [unit] at he
        | some b =>
          by_cases hab : a = b
          · simp [hab]
          · have he := congrFun h a
            simp [unit, hab] at he⟩
  let Other := {v : Word (Fin s) // v ∉ Set.range units}
  let t := 2^s - (s+1)
  have hcard : Fintype.card (Fin t) = Fintype.card Other := by
    dsimp only [Other, t]
    rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_pi_const]
    simp [ZMod.card]
  let e := Fintype.equivOfCardEq hcard
  let labels : Fin d → Word (Fin s) :=
    fun j => if hj : j.val < t then (e ⟨j.val, hj⟩).val else 0
  have ht : t ≤ d := by dsimp [t]; omega
  have hzero : (0 : Word (Fin s)) ∈ Set.range units := ⟨none, rfl⟩
  have hunit (p : Fin s) : unit p ∈ Set.range units := ⟨some p, rfl⟩
  have hother (j : Fin d) (hj : j.val < t) : labels j ∉ Set.range units := by
    simpa [labels, hj] using (e ⟨j.val, hj⟩).property
  refine ⟨labels, ?_, ?_⟩
  · intro i j hn hij
    have hn' : columns labels j ≠ 0 := hij ▸ hn
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have h := units.injective (show units (some i) = units (some j) from hij)
        simpa using h
      | inr j =>
        have hj : j.val < t := by
          by_contra h
          exact hn' (by simp [columns, labels, h])
        change unit i = labels j at hij
        exact (hother j hj (hij ▸ hunit i)).elim
    | inr i =>
      have hi : i.val < t := by
        by_contra h
        exact hn (by simp [columns, labels, h])
      cases j with
      | inl j =>
        change labels i = unit j at hij
        exact (hother i hi (hij.symm ▸ hunit j)).elim
      | inr j =>
        have hj : j.val < t := by
          by_contra h
          exact hn' (by simp [columns, labels, h])
        have he : (e ⟨i.val, hi⟩).val = (e ⟨j.val, hj⟩).val := by
          simpa [columns, labels, hi, hj] using hij
        have hfin := e.injective (Subtype.ext he)
        exact congrArg Sum.inr (Fin.ext (congrArg (fun f : Fin t => f.val) hfin))
  · intro syn hn
    by_cases hr : syn ∈ Set.range units
    · obtain ⟨o, ho⟩ := hr
      cases o with
      | none => exact (hn ho.symm).elim
      | some p => exact ⟨.inl p, ho⟩
    · let j := e.symm ⟨syn, hr⟩
      refine ⟨.inr ⟨j.val, j.isLt.trans_le ht⟩, ?_⟩
      change labels ⟨j.val, j.isLt.trans_le ht⟩ = syn
      simp [labels, j.isLt, j]

end Systematic

def asZ (b : Bool) : ZMod 2 := if b then 1 else 0

def asBit (z : ZMod 2) : Bool := decide (z = 1)

@[simp] theorem asZ_asBit (z : ZMod 2) : asZ (asBit z) = z := by
  fin_cases z
  · change asZ (asBit 0) = (0 : ZMod 2)
    decide
  · change asZ (asBit 1) = (1 : ZMod 2)
    decide

@[simp] theorem asBit_asZ (b : Bool) : asBit (asZ b) = b := by
  cases b <;> decide

theorem asZ_xor (a b : Bool) : asZ (xor a b) = asZ a + asZ b := by
  cases a <;> cases b <;> decide

theorem asBit_add (a b : ZMod 2) : asBit (a+b) = xor (asBit a) (asBit b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem asZ_foldr_xor {I : Type} (l : List I) (x : I → Bool) :
    asZ ((l.map x).foldr xor false) = (l.map fun i => asZ (x i)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [asZ_xor, ih]

namespace Systematic

variable {P D I : Type} [Fintype D] [Fintype P] [DecidableEq P]

noncomputable def syndromeList (labels : D → Word P) (sel : P ⊕ D → I) (p : P) : List I :=
  ((univ.filter fun i => columns labels i p = 1).toList).map sel

theorem syndromeList_spec (labels : D → Word P) (sel : P ⊕ D → I) (x : I → Bool) (p : P) :
    (List.map x (syndromeList labels sel p)).foldr xor false =
      asBit (systematic labels (fun i => asZ (x (sel i))) p) := by
  apply Function.LeftInverse.injective asBit_asZ
  rw [asZ_asBit]
  unfold syndromeList
  rw [List.map_map, asZ_foldr_xor, Finset.sum_map_toList, Finset.sum_filter]
  calc
    _ = ∑ i : P ⊕ D, asZ (x (sel i)) * columns labels i p := by
      apply Finset.sum_congr rfl
      intro i _
      generalize columns labels i p = z
      fin_cases z
      · change (if (0 : ZMod 2) = 1 then asZ (x (sel i)) else 0) = asZ (x (sel i)) * 0
        simp
      · change (if (1 : ZMod 2) = 1 then asZ (x (sel i)) else 0) = asZ (x (sel i)) * 1
        simp
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [systematic, columns, Sum.elim_inl, Sum.elim_inr, unit, mul_ite, mul_one, mul_zero]
      congr 1
      simp

theorem correct_data_bit [DecidableEq D] (labels : D → Word P)
    (hinj : ∀ i j, columns labels i ≠ 0 → columns labels i = columns labels j → i = j)
    (sel : P ⊕ D → I) (x : I → Bool) (j : D) :
    asBit (correct labels (fun i => asZ (x (sel i))) (.inr j)) =
      if labels j = 0 then x (sel (.inr j)) else
        xor (x (sel (.inr j))) (decide
          ((fun p => (List.map x (syndromeList labels sel p)).foldr xor false) =
            (fun p => asBit (labels j p)))) := by
  classical
  have hs : (fun p => (List.map x (syndromeList labels sel p)).foldr xor false) =
      (fun p => asBit (systematic labels (fun i => asZ (x (sel i))) p)) :=
    funext (syndromeList_spec labels sel x)
  have he : ((fun p => asBit (systematic labels (fun i => asZ (x (sel i))) p)) =
      (fun p => asBit (labels j p))) ↔
      systematic labels (fun i => asZ (x (sel i))) = labels j := by
    constructor
    · intro h
      funext p
      simpa only [asZ_asBit] using congrArg asZ (congrFun h p)
    · intro h
      rw [h]
  rw [correct_data labels hinj, asBit_add, asBit_asZ, hs]
  by_cases hj : labels j = 0
  · rw [ite_eq_left hj]
    have hn : ¬(systematic labels (fun i => asZ (x (sel i))) ≠ 0 ∧
        systematic labels (fun i => asZ (x (sel i))) = labels j) := by simp [hj]
    simp [hn, asBit]
  · rw [ite_eq_right hj]
    by_cases h : systematic labels (fun i => asZ (x (sel i))) = labels j
    · simp [h, hj, asBit]
    · have hne := mt he.mp h
      rw [decide_eq_false hne]
      simp [h, asBit]

end Systematic

open Classical in
/-- Changing one flattened coordinate changes at most one projected block. -/
theorem block_distance_le_one {A J X V W : Type} [Fintype A]
    (coord : X ≃ A × J) (word word' : X → V) (block : A → (J → V) → W)
    (h : word' = word ∨ ∃ j, ∀ i, i ≠ j → word' i = word i) :
    ((univ : Finset A).filter (fun a =>
      block a (fun j => word (coord.symm (a,j))) ≠
        block a (fun j => word' (coord.symm (a,j))))).card ≤ 1 := by
  classical
  rcases h with rfl | ⟨i, hi⟩
  · simp
  · have hsub : (univ.filter (fun a =>
        block a (fun j => word (coord.symm (a,j))) ≠
          block a (fun j => word' (coord.symm (a,j))))) ⊆
        ({(coord i).1} : Finset A) := by
      intro a ha
      simp only [mem_filter, mem_univ, true_and, mem_singleton] at ha ⊢
      by_contra hne
      apply ha
      congr 1
      funext j
      symm
      apply hi
      intro he
      exact hne (by simpa using congrArg (fun z => (coord z).1) he)
    simpa using card_le_card hsub

end PEqualNP.Outside.L_meta_32036_aux.SyndromeModel

namespace PEqualNP.Outside.L_meta_32036_aux.Base
open Finset

theorem score_iff {K A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (fiber : Finset K) (ea : fiber ≃ A) (eb : fiber ≃ B) (guess truth : K → K → Bool) :
    (3 : ℚ) / 4 ≤ ((fiber.product fiber).filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card /
      ((fiber.product fiber).card : ℚ) ↔
    (Fintype.card A : ℝ) * Fintype.card B / 2 ≤
      ∑ x : A, ∑ y : B, bitSign (guess (ea.symm x).val (eb.symm y).val) *
        bitSign (truth (ea.symm x).val (eb.symm y).val) := by
  classical
  let P := fiber.product fiber
  let hit (z : K × K) : Prop := guess z.1 z.2 = truth z.1 z.2
  let F (z : K × K) : ℝ := bitSign (guess z.1 z.2) * bitSign (truth z.1 z.2)
  let N : ℝ := (Fintype.card A : ℝ) * Fintype.card B
  have hN : 0 < N := by dsimp [N]; have := Fintype.card_pos (α := A); have := Fintype.card_pos (α := B); positivity
  have hcard : P.card = Fintype.card A * Fintype.card B := by
    exact (card_product fiber fiber).trans (congrArg₂ (· * ·)
      (by simpa using Fintype.card_congr ea) (by simpa using Fintype.card_congr eb))
  have hcast : (P.card : ℝ) = N := by rw [hcard, Nat.cast_mul]
  have hPc : 0 < (P.card : ℚ) := by
    have hh : 0 < P.card := by exact_mod_cast hcast ▸ hN
    exact_mod_cast hh
  have hF (z : K × K) : F z = 2 * (if hit z then (1 : ℝ) else 0) - 1 := by
    dsimp [F, hit]; cases guess z.1 z.2 <;> cases truth z.1 z.2 <;> norm_num [bitSign]
  have hsum : (∑ x : A, ∑ y : B, F ((ea.symm x).val, (eb.symm y).val)) = ∑ z ∈ P, F z := by
    symm
    calc
      _ = ∑ x ∈ fiber, ∑ y ∈ fiber, F (x,y) := Finset.sum_product _ _ _
      _ = ∑ x : fiber, ∑ y : fiber, F (x.val,y.val) := by
        rw [← Finset.sum_coe_sort fiber (fun x => ∑ y ∈ fiber, F (x,y))]
        exact Finset.sum_congr rfl (fun x _ => (Finset.sum_coe_sort fiber (fun y => F (x.val,y))).symm)
      _ = _ := Fintype.sum_equiv ea _ _ (fun x => Fintype.sum_equiv eb _ _ (fun y => by simp))
  have hcount : ∑ z ∈ P, F z = 2 * ((P.filter hit).card : ℝ) - N := by
    simp only [hF, sum_sub_distrib, ← mul_sum, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, hcast]
  change (3 : ℚ)/4 ≤ ((P.filter hit).card : ℚ)/(P.card : ℚ) ↔
    N/2 ≤ ∑ x : A, ∑ y : B, F ((ea.symm x).val, (eb.symm y).val)
  rw [le_div_iff₀ hPc, hsum, hcount]
  have hc : ((3 : ℚ)/4 * (P.card : ℚ) ≤ ((P.filter hit).card : ℚ)) ↔
      ((3 : ℝ)/4 * (P.card : ℝ) ≤ ((P.filter hit).card : ℝ)) := by
    have hh := (Rat.cast_le (K := ℝ) (p := (3:ℚ)/4*(P.card:ℚ))
      (q := ((P.filter hit).card:ℚ))).symm
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hh
  rw [hc, hcast]
  constructor <;> intro h <;> linarith

theorem score_slice {A B R S : Type} [Fintype A] [Fintype B] [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (F : A × R → B × S → ℝ) (v : ℝ)
    (h : (Fintype.card R : ℝ) * Fintype.card S * v ≤
      ∑ x : A × R, ∑ y : B × S, F x y) :
    ∃ r : R, ∃ s : S, v ≤ ∑ x : A, ∑ y : B, F (x,r) (y,s) := by
  classical
  by_contra! hn
  have hh : (∑ r : R, ∑ s : S, ∑ x : A, ∑ y : B, F (x,r) (y,s)) <
      ∑ _ : R, ∑ _ : S, v := by
    refine sum_lt_sum_of_nonempty (univ_nonempty) ?_
    intro r hr
    refine sum_lt_sum_of_nonempty (univ_nonempty) ?_
    intro s hs
    exact hn r s
  have he : (∑ x : A × R, ∑ y : B × S, F x y) =
      ∑ r : R, ∑ s : S, ∑ x : A, ∑ y : B, F (x,r) (y,s) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (f := fun y => F _ y)]
    rw [sum_comm]
    apply sum_congr rfl; intro r hr
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  rw [← he] at hh
  simp only [sum_const, card_univ, nsmul_eq_mul] at hh
  nlinarith

end PEqualNP.Outside.L_meta_32036_aux.Base

namespace PEqualNP.Outside.L_meta_32036_aux.Base
open Finset PEqualNP.Outside.L_meta_32036_aux.Packing
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32036_aux.Affine

set_option maxHeartbeats 1500000 in
theorem circuit_lower {m k b g : ℕ} (hb : b ≤ 3*m)
    (C : Circuit) (tap : Fin (3*m-b) → ℕ)
    (hlegal : ∀ h ∈ C.gates, allowed h)
    (hcost : C.gates.countP paid ≤ g)
    (wire : Fin m × Fin 3 → Fin k) (hw : Function.Injective wire)
    (ref fixed : Fin k → Bool) (raw : (Fin m → Block) → Fin k → Bool)
    (hraw : ∀ x ij, raw x (wire ij) = xor (fromBlock (x ij.1) ij.2) (ref (wire ij)))
    (hfixed : ∀ x i, i ∉ Set.range wire → raw x i = fixed i)
    (φ ψ : (Fin m → Block) → Bool) (read : (Fin (3*m-b) → Bool) → (Fin m → Block) → Bool)
    (hscore : (Fintype.card (Fin m → Block) : ℝ)^2 / 2 ≤
      ∑ x : Fin m → Block, ∑ y : Fin m → Block,
        bitSign (read (fun j => (C.wires (List.ofFn (raw x))).getD (tap j) false) y) *
          bitSign (modelTruth φ ψ x y)) :
    2^b ≤ 49*(1+112*(b+g)) := by
  classical
  let W := Fin m → Block
  let V := Fin m → Fin 3 → ZMod 2
  let z (x : W) : V := fun i j => bf (fromBlock (x i) j)
  have hz : Function.Injective z := by
    intro x y he
    funext i
    rw [← toBlock_fromBlock (x i), ← toBlock_fromBlock (y i)]
    apply congrArg toBlock
    funext j
    exact bf_injective (congrFun (congrFun he i) j)
  have hAffine (i : Fin k) : IsAffine z (fun x => raw x i) := by
    by_cases hi : i ∈ Set.range wire
    · obtain ⟨⟨j, t⟩, rfl⟩ := hi
      let L : V →ₗ[ZMod 2] ZMod 2 := ⟨⟨fun v => v j t, by intros; rfl⟩, by intros; rfl⟩
      refine ⟨L, bf (ref (wire (j,t))), ?_⟩
      intro x
      change bf (raw x (wire (j,t))) = _
      rw [hraw x (j,t)]
      change bf (xor (fromBlock (x j) t) (ref (wire (j,t)))) =
        bf (fromBlock (x j) t) + bf (ref (wire (j,t)))
      cases fromBlock (x j) t <;> cases ref (wire (j,t)) <;> decide
    · exact ⟨0, bf (fixed i), fun x => by simp [hfixed x i hi]⟩
  obtain ⟨send, pivots, hpivots, hsame, hsep⟩ := taps_block_pivots C tap raw z hAffine hlegal (by omega)
  let oldSend (x : W) (j : Fin (3*m-b)) := (C.wires (List.ofFn (raw x))).getD (tap j) false
  let decode (q : Fin (3*m-b) → ZMod 2) (y : W) :=
    if h : ∃ x, send x = q then bitSign (read (oldSend (Classical.choose h)) y) else 1
  have hdecode (x y : W) : decode (send x) y = bitSign (read (oldSend x) y) := by
    have h : ∃ x', send x' = send x := ⟨x, rfl⟩
    simp only [decode, dif_pos h]
    rw [show oldSend (Classical.choose h) = oldSend x from hsame _ _ (Classical.choose_spec h)]
  let e : Block ≃ Fin 8 := Fintype.equivOfCardEq (by decide)
  let ew : W ≃ (Fin m → Fin 8) := Equiv.piCongrRight fun _ => e
  let ep : pivots ↪ Fin m := ⟨Subtype.val, Subtype.val_injective⟩
  have hdist (x y : W) : PEqualNP.Outside.L_meta_32036_aux.Intersection.dist (ew y) (ew x) = distance x y := by
    unfold PEqualNP.Outside.L_meta_32036_aux.Intersection.dist distance
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    change (e (y i) ≠ e (x i)) ↔ x i ≠ y i
    simp [e.injective.eq_iff, ne_comm]
  have hjoint (q : Fin (3*m-b) → ZMod 2) (s : Finset W)
      (hs : s = univ.filter (fun x => send x = q)) (x : W) (hx : x ∈ s)
      (x' : W) (hx' : x' ∈ s) (hn : x ≠ x') :
      ((s.filter (fun y => distance x y ≤ 2 ∧ distance x' y ≤ 2)).card : ℝ) ≤ 112*(b+g) := by
    have hmem (u : W) (hu : u ∈ s) : send u = q := by
      rw [hs] at hu
      exact (mem_filter.mp hu).2
    have hinj (u v : W) (hu : u ∈ s) (hv : v ∈ s) (he : ew u ∘ ep = ew v ∘ ep) : u = v := by
      apply hz
      apply hsep u v ((hmem u hu).trans (hmem v hv).symm)
      intro i hi
      have hh := e.injective (congrFun he ⟨i,hi⟩)
      exact congrArg (fun t j => bf (fromBlock t j)) hh
    have hsep' : ew x ∘ ep ≠ ew x' ∘ ep := fun h => hn (hinj x x' hx hx' h)
    have hp : Set.InjOn (fun t : Fin m → Fin 8 => t ∘ ep) (s.map ew.toEmbedding : Set (Fin m → Fin 8)) := by
      intro u hu v hv he
      have hu' : u ∈ s.map ew.toEmbedding := hu
      have hv' : v ∈ s.map ew.toEmbedding := hv
      obtain ⟨a, ha, h₁⟩ := Finset.mem_map.mp hu'
      obtain ⟨b, hb, h₂⟩ := Finset.mem_map.mp hv'
      change ew a = u at h₁
      change ew b = v at h₂
      rw [← h₁, ← h₂] at he ⊢
      exact congrArg ew (hinj a b ha hb he)
    have hm := PEqualNP.Outside.L_meta_32036_aux.Intersection.projected_intersection_card (s.map ew.toEmbedding) ep _ _ hsep' hp
    have heq : (s.filter (fun y => distance x y ≤ 2 ∧ distance x' y ≤ 2)).map ew.toEmbedding =
        (s.map ew.toEmbedding).filter (fun y => PEqualNP.Outside.L_meta_32036_aux.Intersection.dist y (ew x) ≤ 2 ∧
          PEqualNP.Outside.L_meta_32036_aux.Intersection.dist y (ew x') ≤ 2) := by
      ext y
      obtain ⟨v, rfl⟩ := ew.surjective y
      simp [hdist]
    rw [← heq, card_map] at hm
    have hdim' : pivots.card ≤ b+g := by omega
    have hh := hm.trans (Nat.mul_le_mul_left 112 (show Fintype.card pivots ≤ b+g by simpa using hdim'))
    exact_mod_cast hh
  have hcorr := (model_stats (R := Unit) φ ψ 2).2.2
  have hp := packing send decode (fun x y => bitSign (modelTruth φ ψ x y))
    (fun x y => distance x y ≤ 2) ((112:ℝ)*((b:ℝ)+g)) (by positivity) hjoint
    (fun x y => by
      have h := hcorr (x, ()) (y, ())
      rw [Fintype.sum_prod_type] at h
      norm_num [W, Input, card_code] at h ⊢
      exact h)
    (fun q y => by by_cases he : ∃ x, send x = q <;> simp [decode, he, sign_sq])
    (by simpa only [pow_two, hdecode, oldSend] using hscore)
  rw [show Fintype.card W = 8^m from card_code m, label_card, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at hp
  have hex : (8 : ℝ)^m = 2^(3*m-b) * 2^b := by
    rw [← pow_add, Nat.sub_add_cancel hb, pow_mul]
    norm_num
  rw [hex] at hp
  have hbound : (2 : ℝ)^b ≤ 49 * (1+112*((b : ℝ)+g)) := by
    apply (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ)^(3*m-b) by positivity)).mp
    convert hp using 1 <;> ring
  exact_mod_cast hbound

end PEqualNP.Outside.L_meta_32036_aux.Base

namespace PEqualNP.Outside.L_meta_32036_aux.Base
open Finset PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_32036_aux.SyndromeModel
open PEqualNP.Outside.L_meta_32036_aux.SyndromeModel.Systematic

private theorem parity_list {I : Type} [DecidableEq I] (l : List I) (h : l.Nodup) (f : I → Bool) :
    PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.parity (l.map f) = parityOn l.toFinset f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.nodup_cons] at h
    simp only [PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.parity, List.map_cons, List.foldr_cons, List.toFinset_cons]
    change xor (f x) (PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.parity (l.map f)) = _
    rw [ih h.2, parity_insert (by simpa using h.1)]

set_option maxHeartbeats 2000000 in
theorem circuit_upper {m k b : ℕ} (hsize : 2^(b+1) ≤ 3*m+1)
    (wire : Fin m × Fin 3 → Fin k)
    (ref : Fin k → Bool) (flag : Fin m → Bool) (phase₀ : Bool)
    (ψ : (Fin m → Block) → Bool) :
    ∃ (C : Circuit) (tap : Fin (3*m-b) → Nat)
      (read : (Fin (3*m-b) → Bool) → (Fin m → Block) → Bool),
      PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.legal k C ∧
      PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.cost C ≤ 2^(b+1)-(b+1)-1 ∧
      (∀ j, tap j < k+C.gates.length) ∧
      ∀ (raw : Fin k → Bool) (x : Fin m → Block),
        (∀ ij, raw (wire ij) = xor (fromBlock (x ij.1) ij.2) (ref (wire ij))) →
        (Fintype.card (Fin m → Block) : ℝ) / 2 ≤
          ∑ y : Fin m → Block, bitSign (read (fun j => (C.wires (List.ofFn raw)).getD (tap j) false) y) *
            bitSign (modelTruth (fun x => xor phase₀ (parityOn univ fun i => affine (flag i) (x i))) ψ x y) := by
  classical
  let s := b+1
  let d := 3*m-s
  have hpow (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  have hs : s ≤ 3*m := by have hh := hpow s; change 2^s ≤ 3*m+1 at hsize; omega
  have hsd : s+d = m*3 := by dsimp [d]; omega
  have hc : 3*m-b = d+1 := by dsimp [d, s] at *; omega
  let E : (Fin s ⊕ Fin d) ≃ Fin m × Fin 3 :=
    finSumFinEquiv.trans ((finCongr hsd).trans finProdFinEquiv.symm)
  obtain ⟨lab, hinj, hcover⟩ := exists_labels s d (by change 2^s ≤ 3*m+1 at hsize; omega)
  let sel (i : Fin s ⊕ Fin d) := wire (E i)
  let σ := syndromeList lab sel
  let label (j : Fin d) : Option (Fin s → Bool) := if lab j = 0 then none else some (fun p => asBit (lab j p))
  let which (i : Fin m) : Fin 3 := if flag i then 0 else 1
  let phaseWire (i : Fin m) := wire (i, which i)
  let extra := (List.finRange m).map phaseWire
  obtain ⟨C, taps, last, hl, hcost, htaps, hlast, hdata, hphase⟩ :=
    PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.encoder σ label (fun j => sel (.inr j)) extra
  let allTap : Fin (d+1) → Nat := Fin.lastCases last taps
  let ce : Fin (3*m-b) ≃ Fin (d+1) := finCongr hc
  let tap := allTap ∘ ce
  let block (i : Fin m) (v : Fin 3 → ZMod 2) := toBlock (fun t => xor (asBit (v t)) (ref (wire (i,t))))
  let unpack (v : Word (Fin s ⊕ Fin d)) (i : Fin m) := block i (fun t => v (E.symm (i,t)))
  let offset := xor phase₀ (parityOn univ (fun i => ref (phaseWire i)))
  let kern := modelTruth (fun _ : Fin m → Block => false) ψ
  let read (msg : Fin (3*m-b) → Bool) (y : Fin m → Block) :=
    let data := fun j : Fin d => asZ (msg (ce.symm j.castSucc))
    xor (xor offset (msg (ce.symm (Fin.last d)))) (kern (unpack (rebuild lab data 0)) y)
  refine ⟨C, tap, read, hl, hcost, ?_, ?_⟩
  · intro j
    change allTap (ce j) < _
    exact Fin.lastCases (by simpa [allTap] using hlast) (fun i => by simpa [allTap] using htaps i) (ce j)
  intro raw x hraw
  let v : Word (Fin s ⊕ Fin d) := fun i => asZ (raw (sel i))
  let msg := fun j => (C.wires (List.ofFn raw)).getD (tap j) false
  have hmsg (j : Fin d) : asZ (msg (ce.symm j.castSucc)) = correct lab v (.inr j) := by
    have he := correct_data_bit lab hinj sel raw j
    have ht : PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.corrected σ (label j) (sel (.inr j)) raw =
        asBit (correct lab v (.inr j)) := by
      rw [show v = (fun i => asZ (raw (sel i))) from rfl, he]
      by_cases h : lab j = 0 <;> simp [label, h, PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.corrected,
        PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.parity, σ]
      congr 1
    simp only [msg, tap, Function.comp_apply, Equiv.apply_symm_apply, allTap,
      Fin.lastCases_castSucc, hdata, ht, asZ_asBit]
  have hsum (f : Fin m → Bool) : PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.parity ((List.finRange m).map f) = parityOn univ f := by
    rw [parity_list _ (List.nodup_finRange m)]
    congr 1
    ext i
    simp
  have hp : msg (ce.symm (Fin.last d)) = parityOn univ (fun i => raw (phaseWire i)) := by
    simpa only [msg, tap, Function.comp_apply, Equiv.apply_symm_apply, allTap, Fin.lastCases_last,
      hphase, extra, List.map_map, Function.comp_def, hsum]
  have ha (i : Fin m) : affine (flag i) (x i) = fromBlock (x i) (which i) := by
    cases h : flag i <;> simp [which, affine, fromBlock, h]
  have hphase' : xor offset (msg (ce.symm (Fin.last d))) =
      xor phase₀ (parityOn univ (fun i => affine (flag i) (x i))) := by
    rw [hp]
    simp only [phaseWire, hraw, parity_xor, offset, ha]
    cases phase₀ <;> cases parityOn univ (fun i => ref (wire (i, which i))) <;>
      cases parityOn univ (fun i => fromBlock (x i) (which i)) <;> rfl
  have hv : unpack v = x := by
    funext i
    change toBlock (fun t => xor (asBit (asZ (raw (wire (E (E.symm (i,t))))))) (ref (wire (i,t)))) = x i
    simp only [Equiv.apply_symm_apply, asBit_asZ, hraw]
    rw [← toBlock_fromBlock (x i)]
    apply congrArg toBlock
    funext t
    rw [fromBlock_toBlock]
    cases fromBlock (x i) t <;> cases ref (wire (i,t)) <;> rfl
  have hdist : distance x (unpack (correct lab v)) ≤ 1 := by
    rw [← hv]
    unfold distance
    convert block_distance_le_one E v (correct lab v) block (correct_changes_one lab v) using 1
    congr 1
    ext i
    simp [unpack]
  have hread (y : Fin m → Block) : read msg y =
      xor (xor phase₀ (parityOn univ (fun i => affine (flag i) (x i))))
        (kern (unpack (correct lab v)) y) := by
    dsimp only [read]
    rw [hphase', funext hmsg, reconstruct_correct lab hcover]
  change _ ≤ ∑ y, bitSign (read msg y) * _
  simp_rw [hread, show ∀ y, modelTruth (fun x => xor phase₀ (parityOn univ fun i => affine (flag i) (x i))) ψ x y =
      xor (xor phase₀ (parityOn univ fun i => affine (flag i) (x i))) (kern x y) by
    intro y; simp [kern, modelTruth, Bool.xor_assoc]]
  simp_rw [sign_xor, mul_mul_mul_comm, ← pow_two, sign_sq, one_mul]
  simp_rw [mul_comm (bitSign (kern (unpack (correct lab v)) _)), kern]
  rw [correlation]
  simp only [bitSign, mul_one, one_mul, card_code, Nat.cast_pow, Nat.cast_ofNat]
  have hd : distance x (unpack (correct lab v)) = 0 ∨ distance x (unpack (correct lab v)) = 1 := by omega
  rcases hd with hd | hd <;> rw [hd] <;> norm_num
  nlinarith [pow_nonneg (show (0:ℝ) ≤ 8 by norm_num) m]

end PEqualNP.Outside.L_meta_32036_aux.Base

namespace PEqualNP.Outside.L_meta_32036_aux.Base
open Finset PEqualNP.CircuitLowerBounds

def eligible {K : Type} (k c : ℕ) (fiber : Finset K) (raw : K → Fin k → Bool)
    (truth : K → K → Bool) (g : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin c → ℕ) (read : (Fin c → Bool) → K → Bool),
    PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.legal k C ∧ PEqualNP.Outside.L_meta_32036_aux.SyndromeCircuit.cost C ≤ g ∧
    (∀ j, tap j < k+C.gates.length) ∧
    (3 : ℚ)/4 ≤ ((fiber.product fiber).filter (fun z =>
      read (fun j => (C.wires (List.ofFn (raw z.1))).getD (tap j) false) z.2 = truth z.1 z.2)).card /
      ((fiber.product fiber).card : ℚ)

set_option maxHeartbeats 150000 in
theorem transfer_bounds {K E : Type} [Fintype E] [Nonempty E] {k m b : ℕ} (hb : b ≤ 3*m)
    (fiber : Finset K) (left right : fiber ≃ Input m E)
    (raw : K → Fin k → Bool) (truth : K → K → Bool)
    (wire : Fin m × Fin 3 → Fin k) (hwire : Function.Injective wire) (ref : Fin k → Bool)
    (flag : Fin m → Bool) (phase : Bool) (ψ : (Fin m → Block) → Bool)
    (hTruth : ∀ x y, truth (left.symm x).val (right.symm y).val =
      modelTruth (fun x => xor phase (parityOn univ fun i => affine (flag i) (x i))) ψ x.1 y.1)
    (hcoord : ∀ x ij, raw (left.symm x).val (wire ij) = xor (fromBlock (x.1 ij.1) ij.2) (ref (wire ij)))
    (hfixed : ∀ x x', x.2 = x'.2 → ∀ i, i ∉ Set.range wire → raw (left.symm x).val i = raw (left.symm x').val i) :
    (∀ g, eligible k (3*m-b) fiber raw truth g → 2^b ≤ 49*(1+112*(b+g))) ∧
      (2^(b+1) ≤ 3*m+1 → eligible k (3*m-b) fiber raw truth (2^(b+1)-(b+1)-1)) := by
  classical
  let W := Fin m → Block
  let S := Input m E
  let c := 3*m-b
  let ka (x : S) := (left.symm x).val
  let kb (y : S) := (right.symm y).val
  let φ (x : W) := xor phase (parityOn univ fun i => affine (flag i) (x i))
  let model (x y : S) := modelTruth φ ψ x.1 y.1
  have hscore (guess : K → K → Bool) :
      (3 : ℚ)/4 ≤ ((fiber.product fiber).filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card /
        ((fiber.product fiber).card : ℚ) ↔
      (Fintype.card S : ℝ)^2/2 ≤ ∑ x : S, ∑ y : S,
        bitSign (guess (ka x) (kb y)) * bitSign (model x y) := by
    simpa only [pow_two, hTruth, ka, kb, model, φ] using score_iff fiber left right guess truth
  constructor
  · intro g hg
    obtain ⟨C, tap, read, hleg, hcost, _, hagree⟩ := hg
    let send (x : K) (j : Fin c) := (C.wires (List.ofFn (raw x))).getD (tap j) false
    have hsc := (hscore (fun x y => read (send x) y)).mp hagree
    let F (x y : S) := bitSign (read (send (ka x)) (kb y)) * bitSign (model x y)
    obtain ⟨r,t,hrt⟩ := score_slice F ((Fintype.card W : ℝ)^2/2) (by
      change _ ≤ ∑ x : S, ∑ y : S, F x y
      convert hsc using 1
      simp only [S, Input, Fintype.card_prod, Nat.cast_mul]
      ring)
    let R (x : W) := raw (ka (x,r))
    have hraw (x : W) (ij : Fin m × Fin 3) :
        R x (wire ij) = xor (fromBlock (x ij.1) ij.2) (ref (wire ij)) := hcoord (x,r) ij
    exact circuit_lower hb C tap hleg.2 hcost wire hwire ref (R (fun _ => (false,false,false))) R
      hraw (fun x i hi => hfixed (x,r) ((fun _ => (false,false,false)),r) rfl i hi)
      φ ψ (fun msg y => read msg (kb (y,t))) hrt
  · intro hsize
    obtain ⟨C, tap, read, hleg, hcost, htaps, hcorrect⟩ := circuit_upper (b := b) hsize wire ref flag phase ψ
    let decode (msg : Fin c → Bool) (key : K) :=
      if h : key ∈ fiber then read msg (right ⟨key,h⟩).1 else false
    refine ⟨C, tap, decode, hleg, hcost, htaps, ?_⟩
    let send (x : K) (j : Fin c) := (C.wires (List.ofFn (raw x))).getD (tap j) false
    apply (hscore (fun x y => decode (send x) y)).mpr
    change _ ≤ ∑ x : S, ∑ y : S, bitSign (decode (send (ka x)) (kb y)) * bitSign (model x y)
    have hdecode (msg : Fin c → Bool) (y : S) : decode msg (kb y) = read msg y.1 := by
      have h : kb y ∈ fiber := (right.symm y).property
      simp only [decode, dif_pos h]
      change read msg (right (right.symm y)).1 = _
      rw [Equiv.apply_symm_apply]
    simp_rw [hdecode]
    have hrow (x : S) : (Fintype.card S : ℝ)/2 ≤
        ∑ y : S, bitSign (read (send (ka x)) y.1) * bitSign (model x y) := by
      have h := hcorrect (raw (ka x)) x.1 (hcoord x)
      change _ ≤ ∑ y : W × E, bitSign (read (send (ka x)) y.1) * bitSign (modelTruth φ ψ x.1 y.1)
      rw [Fintype.sum_prod_type]
      simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum, S, Input, Fintype.card_prod, Nat.cast_mul]
      convert mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ Fintype.card E by positivity) using 1 <;> ring
    refine le_trans ?_ (sum_le_sum fun x _ => hrow x)
    simp only [sum_const, card_univ, nsmul_eq_mul]
    ring_nf
    exact le_rfl

end PEqualNP.Outside.L_meta_32036_aux.Base

open Finset PEqualNP.Outside.L_meta_32036_aux.Base
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_32036 :
∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < k+i.val) ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  ∀ b : Nat, b ≤ 3*m →
    let c := 3*m-b
    let feasible := fun (g : Nat) =>
      ∃ (C : Circ) (tap : Fin c → Nat) (read : (Fin c → Bool) → K → Bool),
        legal C ∧ cost C ≤ g ∧ (∀ j, tap j < k+C.gates.length) ∧
        let send := fun (x : K) (j : Fin c) =>
          let raw := List.ofFn (fun i : Fin k => x.val.testBit i.val)
          (C.wires raw).getD (tap j) false
        (3 : ℚ)/4 ≤ agree (fun x y => read (send x) y)
    (∀ g : Nat, feasible g → 2^b ≤ 49*(1+112*(b+g))) ∧
    (2^(b+1) ≤ 3*m+1 → feasible (2^(b+1)-(b+1)-1)) := by
  classical
  intro k hk0 constant rot step state injected bit m starts hm hinj good row ref hgood pin hpin hfree K fiber pairs truth agree Circ legal cost b hb c feasible
  let windows : Fin m × Fin 12 → Fin k := fun ij =>
    ⟨(starts ij.1 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  have hwin : Function.Injective windows := by
    intro a b h
    exact hinj (congrArg Fin.val h)
  have hk : 12 ≤ k := by
    have hc := Fintype.card_le_of_injective windows hwin
    simp [Fintype.card_prod] at hc
    omega
  let coord : Fin m × Fin 3 → Fin k := fun ij =>
    ⟨(starts ij.1 + 9 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  let lift : Fin m × Fin 3 → Fin m × Fin 12 := fun ij =>
    (ij.1, ⟨9 + ij.2.val, by omega⟩)
  have hcoord : Function.Injective coord := by
    intro a b h
    have hh : windows (lift a) = windows (lift b) := by
      apply Fin.ext
      simpa only [windows, lift, coord, Nat.add_assoc] using congrArg Fin.val h
    have he := hwin hh
    apply Prod.ext
    · have hfst := congrArg Prod.fst he
      exact hfst
    · apply Fin.ext
      have hn := congrArg (fun x : Fin m × Fin 12 => x.2.val) he
      change 9 + a.2.val = 9 + b.2.val at hn
      omega
  have hcFree (ij : Fin m × Fin 3) : coord ij ∉ pin := by
    intro h
    exact hfree ij.1 ij.2 (coord ij) h rfl
  let eBits := shareBitsEquiv hk constant row ref
  have hFiber (q : Fin (2^k)) : q ∈ fiber ↔ ∀ z ∈ pin, eBits q z = false := by
    change (q ∈ univ.filter (fun key : Fin (2^k) =>
      ∀ z ∈ pin, bitFn k constant row.val 0 key.val z.val = bitFn k constant row.val 0 ref.val z.val)) ↔ _
    simp only [mem_filter, mem_univ, true_and]
    change (∀ z ∈ pin, bitFn k constant row.val 0 q.val z.val = bitFn k constant row.val 0 ref.val z.val) ↔
      ∀ z ∈ pin, xor (bitFn k constant row.val 0 q.val z.val) (bitFn k constant row.val 0 ref.val z.val) = false
    simp only [xor_false_iff]
  let Extra := Remainder pin coord → Bool
  let Side := Input m Extra
  let left : fiber ≃ Side := (eBits.subtypeEquiv hFiber).trans (splitBits pin coord hcoord hcFree)
  let shifts := fun i => windowShift constant row ref (starts i)
  let right : fiber ≃ Side := left.trans (Equiv.prodCongr (shiftBlock shifts) (Equiv.refl Extra))
  let flag := fun i => windowFlag constant row ref (starts i)
  let base := fun i => xor (!affine (flag i) (point (flag i)))
    (injectedFn k constant 2 ref.val (starts i+5))
  let φ := fun x : Fin m → Block => xor (parityOn univ base)
    (parityOn univ (fun i => affine (flag i) (x i)))
  let ψ := fun y : Fin m → Block => parityOn univ (fun i => affine (flag i) (y i))
  let model : Side → Side → Bool := fun x y => modelTruth φ ψ x.1 y.1
  have hLeft (q : fiber) (i : Fin m) : (left q).1 i = windowShare constant row ref q.val (starts i) := by
    change toBlock (fun j => shareBit k constant row ref q.val (coord (i,j)).val) = _
    dsimp only [toBlock, coord, windowShare]
    rw [shareBit_mod hk, shareBit_mod hk, shareBit_mod hk]
    rfl
  have hRight (q : fiber) (i : Fin m) : (right q).1 i =
      bxor (windowShare constant row ref q.val (starts i)) (shifts i) := by
    change bxor ((left q).1 i) (shifts i) = _
    rw [hLeft]
  have hpinShare (q : fiber) (i : Fin m) (j : ℕ) (hj : j < 9) :
      shareBit k constant row ref q.val (starts i+j) = false := by
    obtain ⟨z, hz, hzval⟩ := hpin i ⟨j, hj⟩
    have hs := (hFiber q.val).mp q.property z hz
    change shareBit k constant row ref q.val z.val = false at hs
    rw [hzval, shareBit_mod hk] at hs
    exact hs
  have hTruth (x y : fiber) : truth x.val y.val = model (left x) (right y) := by
    have hrow (i : Fin m) :
        bitFn k constant row.val 2 (combine ref x.val y.val).val (starts i+5) =
          xor (xor (xor (base i) (affine (flag i) ((left x).1 i)))
            (affine (flag i) ((right y).1 i))) (decide ((left x).1 i = (right y).1 i)) := by
      rw [hLeft, hRight]
      exact guarded_window hk constant row ref x.val y.val (starts i) (hpinShare x i) (hpinShare y i)
        (hgood i).1 (hgood i).2.2.1 (hgood i).2.2.2
    change parityOn univ (fun i => bitFn k constant row.val 2 (combine ref x.val y.val).val (starts i+5)) = _
    rw [funext hrow]
    simp only [model, modelTruth, parity_xor, φ, ψ]
  let ka : Side → K := fun x => (left.symm x).val
  let kb : Side → K := fun y => (right.symm y).val
  let raw (key : K) (i : Fin k) := key.val.testBit i.val
  let back (z : Fin k) : Fin k := ⟨(z.val+k-1)%k, Nat.mod_lt _ hk0⟩
  let next (z : Fin k) : Fin k := ⟨(z.val+1)%k, Nat.mod_lt _ hk0⟩
  have hback (z : Fin k) : back (next z) = z := by
    apply Fin.ext
    change (((z.val + 1) % k) + k - 1) % k = z.val
    have hz := z.isLt
    by_cases h : z.val+1 < k
    · rw [Nat.mod_eq_of_lt h, show z.val+1+k-1 = z.val+k by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hz]
    · rw [show z.val+1 = k by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : k-1 < k)]
      omega
  have hnext (z : Fin k) : next (back z) = z := by
    apply Fin.ext
    change (((z.val+k-1)%k)+1)%k = z.val
    have hz := z.isLt
    by_cases h : z.val = 0
    · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k-1 < k),
        show k-1+1 = k by omega, Nat.mod_self]
    · rw [show z.val+k-1 = z.val-1+k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : z.val-1 < k), show z.val-1+1 = z.val by omega,
        Nat.mod_eq_of_lt hz]
  let wire (ij : Fin m × Fin 3) := back (coord ij)
  have hwire : Function.Injective wire := by
    intro a b hab
    apply hcoord
    simpa only [wire, hnext] using congrArg next hab
  have hshare (q : K) (z : Fin k) : eBits q z = xor (raw q (back z)) (raw ref (back z)) := by
    exact shareBit_eq hk constant row ref q z.val
  have hcoordRaw (x : Side) (ij : Fin m × Fin 3) :
      raw (ka x) (wire ij) = xor (fromBlock (x.1 ij.1) ij.2) (raw ref (wire ij)) := by
    have hh := congrArg (fun p : Side => fromBlock (p.1 ij.1) ij.2) (left.apply_symm_apply x)
    change fromBlock (toBlock (fun t => eBits (ka x) (coord (ij.1,t)))) ij.2 = _ at hh
    rw [fromBlock_toBlock, hshare] at hh
    exact (xor_left_eq (raw (ka x) (wire ij)) (raw ref (wire ij))
      (fromBlock (x.1 ij.1) ij.2)).mp hh |>.trans (Bool.xor_comm _ _)
  have hextraRaw (x x' : Side) (he : x.2 = x'.2) (i : Fin k) (hi : i ∉ Set.range wire) :
      raw (ka x) i = raw (ka x') i := by
    let z := next i
    have hz : z ∉ Set.range coord := by
      rintro ⟨ij, hij⟩
      exact hi ⟨ij, by simp only [wire, hij, z, hback]⟩
    have hh : eBits (ka x) z = eBits (ka x') z := by
      by_cases hp : z ∈ pin
      · rw [(hFiber _).mp (left.symm x).property z hp,
          (hFiber _).mp (left.symm x').property z hp]
      · let j : Remainder pin coord := ⟨z, hp, hz⟩
        have hx := congrArg (fun p : Side => p.2 j) (left.apply_symm_apply x)
        have hx' := congrArg (fun p : Side => p.2 j) (left.apply_symm_apply x')
        change eBits (ka x) z = x.2 j at hx
        change eBits (ka x') z = x'.2 j at hx'
        rw [hx, hx', he]
    rw [hshare, hshare, show back z = i from hback i] at hh
    cases raw ref i <;> simpa using hh
  have ht (x y : Side) : truth (ka x) (kb y) = model x y := by
    simpa only [ka, kb, Equiv.apply_symm_apply] using hTruth (left.symm x) (right.symm y)
  exact transfer_bounds hb fiber left right raw truth wire hwire (raw ref) flag
    (parityOn univ base) ψ ht hcoordRaw hextraRaw
