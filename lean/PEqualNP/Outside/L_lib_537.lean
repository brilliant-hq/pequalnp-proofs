import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_537_aux

def allOnes : Nat := (1 <<< 131072) - 1

def mkPlaneLoop (acc shift : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => mkPlaneLoop (acc ||| (acc <<< shift)) (shift <<< 1) n

def mkPlane (idx : Nat) : Nat :=
  let half := 1 <<< idx
  let period := 1 <<< (idx + 1)
  let block := ((1 <<< half) - 1) <<< half
  mkPlaneLoop block period (16 - idx)

structure Planes17 where
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p4 : Nat
  p5 : Nat
  p6 : Nat
  p7 : Nat
  p8 : Nat
  p9 : Nat
  p10 : Nat
  p11 : Nat
  p12 : Nat
  p13 : Nat
  p14 : Nat
  p15 : Nat
  p16 : Nat

def Planes17.get (a : Planes17) : Nat → Nat
  | 0 => a.p0
  | 1 => a.p1
  | 2 => a.p2
  | 3 => a.p3
  | 4 => a.p4
  | 5 => a.p5
  | 6 => a.p6
  | 7 => a.p7
  | 8 => a.p8
  | 9 => a.p9
  | 10 => a.p10
  | 11 => a.p11
  | 12 => a.p12
  | 13 => a.p13
  | 14 => a.p14
  | 15 => a.p15
  | 16 => a.p16
  | _ => 0

def Planes17.xor (a b : Planes17) : Planes17 :=
  ⟨a.p0 ^^^ b.p0, a.p1 ^^^ b.p1, a.p2 ^^^ b.p2, a.p3 ^^^ b.p3,
   a.p4 ^^^ b.p4, a.p5 ^^^ b.p5, a.p6 ^^^ b.p6, a.p7 ^^^ b.p7,
   a.p8 ^^^ b.p8, a.p9 ^^^ b.p9, a.p10 ^^^ b.p10, a.p11 ^^^ b.p11,
   a.p12 ^^^ b.p12, a.p13 ^^^ b.p13, a.p14 ^^^ b.p14, a.p15 ^^^ b.p15,
   a.p16 ^^^ b.p16⟩

def Planes17.xorConst (a : Planes17) (c : Nat) : Planes17 :=
  ⟨if c.testBit 0 then a.p0 ^^^ allOnes else a.p0,
   if c.testBit 1 then a.p1 ^^^ allOnes else a.p1,
   if c.testBit 2 then a.p2 ^^^ allOnes else a.p2,
   if c.testBit 3 then a.p3 ^^^ allOnes else a.p3,
   if c.testBit 4 then a.p4 ^^^ allOnes else a.p4,
   if c.testBit 5 then a.p5 ^^^ allOnes else a.p5,
   if c.testBit 6 then a.p6 ^^^ allOnes else a.p6,
   if c.testBit 7 then a.p7 ^^^ allOnes else a.p7,
   if c.testBit 8 then a.p8 ^^^ allOnes else a.p8,
   if c.testBit 9 then a.p9 ^^^ allOnes else a.p9,
   if c.testBit 10 then a.p10 ^^^ allOnes else a.p10,
   if c.testBit 11 then a.p11 ^^^ allOnes else a.p11,
   if c.testBit 12 then a.p12 ^^^ allOnes else a.p12,
   if c.testBit 13 then a.p13 ^^^ allOnes else a.p13,
   if c.testBit 14 then a.p14 ^^^ allOnes else a.p14,
   if c.testBit 15 then a.p15 ^^^ allOnes else a.p15,
   if c.testBit 16 then a.p16 ^^^ allOnes else a.p16⟩

def Planes17.rot1 (a : Planes17) : Planes17 :=
  ⟨a.p16, a.p0, a.p1, a.p2, a.p3, a.p4, a.p5, a.p6, a.p7,
   a.p8, a.p9, a.p10, a.p11, a.p12, a.p13, a.p14, a.p15⟩

def Planes17.rotIter : Nat → Planes17 → Planes17
  | 0, a => a
  | n + 1, a => Planes17.rotIter n a.rot1

def Planes17.rotN (s : Nat) (a : Planes17) : Planes17 :=
  Planes17.rotIter (s % 17) a

def Planes17.step (a : Planes17) : Planes17 :=
  ⟨a.p0 ^^^ ((allOnes ^^^ a.p1) &&& a.p2),
   a.p1 ^^^ ((allOnes ^^^ a.p2) &&& a.p3),
   a.p2 ^^^ ((allOnes ^^^ a.p3) &&& a.p4),
   a.p3 ^^^ ((allOnes ^^^ a.p4) &&& a.p5),
   a.p4 ^^^ ((allOnes ^^^ a.p5) &&& a.p6),
   a.p5 ^^^ ((allOnes ^^^ a.p6) &&& a.p7),
   a.p6 ^^^ ((allOnes ^^^ a.p7) &&& a.p8),
   a.p7 ^^^ ((allOnes ^^^ a.p8) &&& a.p9),
   a.p8 ^^^ ((allOnes ^^^ a.p9) &&& a.p10),
   a.p9 ^^^ ((allOnes ^^^ a.p10) &&& a.p11),
   a.p10 ^^^ ((allOnes ^^^ a.p11) &&& a.p12),
   a.p11 ^^^ ((allOnes ^^^ a.p12) &&& a.p13),
   a.p12 ^^^ ((allOnes ^^^ a.p13) &&& a.p14),
   a.p13 ^^^ ((allOnes ^^^ a.p14) &&& a.p15),
   a.p14 ^^^ ((allOnes ^^^ a.p15) &&& a.p16),
   a.p15 ^^^ ((allOnes ^^^ a.p16) &&& a.p0),
   a.p16 ^^^ ((allOnes ^^^ a.p0) &&& a.p1)⟩

def Planes17.hiZero (a : Planes17) : Nat :=
  allOnes ^^^ (a.p8 ||| a.p9 ||| a.p10 ||| a.p11 ||| a.p12 ||| a.p13 ||| a.p14 ||| a.p15 ||| a.p16)

def keyPlanes : Planes17 :=
  ⟨mkPlane 0, mkPlane 1, mkPlane 2, mkPlane 3, mkPlane 4, mkPlane 5, mkPlane 6, mkPlane 7,
   mkPlane 8, mkPlane 9, mkPlane 10, mkPlane 11, mkPlane 12, mkPlane 13, mkPlane 14, mkPlane 15,
   mkPlane 16⟩

def mateKeyPlanes : Planes17 := keyPlanes.xorConst 12

def outRound (w : Planes17) (x : Planes17) (t : Nat) : Planes17 :=
  let c := (3 ^ (17 + (t + 1))) % 131072
  let y := x.xor (x.rotN 1) |>.xor (x.rotN 16)
  (y.step.xor (w.rotN (2 * t))).xorConst c

def outPlanes (w : Planes17) : Planes17 :=
  let x0 := w.rotN 1
  let x1 := outRound w x0 0
  let x2 := outRound w x1 1
  let x3 := outRound w x2 2
  outRound w x3 3

def colRound (w : Planes17) (st : Planes17) (j : Nat) : Planes17 :=
  let c := (3 ^ (17 + (4 + (j + 1)))) % 131072
  let y := st.xor (st.rotN 2) |>.xor (st.rotN 15)
  (y.step.xor (w.rotN (3 * (j + 1) + 1))).xorConst c

def colMask (w : Planes17) (name : Nat) : Nat :=
  let s0 := (w.rotN 3).xorConst name
  let s1 := colRound w s0 0
  let s2 := colRound w s1 1
  let s3 := colRound w s2 2
  (colRound w s3 3).hiZero

def negCols : List Nat := [1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29]

def coversNames : List Nat → Nat → Nat → Bool
  | [], m0, mneg => m0 == 0 || mneg != 0
  | p :: ps, m0, mneg =>
    if m0 == 0 then true
    else
      coversNames ps (m0 &&& p) (mneg &&& p) &&
      coversNames ps (m0 &&& (allOnes ^^^ p)) (mneg &&& (allOnes ^^^ p))

def outZMask : Nat := (outPlanes keyPlanes).hiZero
def col0Mask : Nat := colMask keyPlanes 0
def colNegMask : Nat := negCols.foldl (fun acc name => acc ||| colMask keyPlanes name) 0
def bit2Mask : Nat := keyPlanes.p2
def nbit2Mask : Nat := allOnes ^^^ bit2Mask
def mateOutPlanes : Planes17 := outPlanes mateKeyPlanes
def mateHiList : List Nat :=
  [mateOutPlanes.p8, mateOutPlanes.p9, mateOutPlanes.p10, mateOutPlanes.p11,
   mateOutPlanes.p12, mateOutPlanes.p13, mateOutPlanes.p14, mateOutPlanes.p15, mateOutPlanes.p16]

def checkAll : Bool :=
  ((outZMask &&& col0Mask) != 0) &&
  ((outZMask &&& colNegMask) == 0) &&
  ((bit2Mask &&& outZMask &&& col0Mask) == 0) &&
  coversNames mateHiList (nbit2Mask &&& col0Mask) (nbit2Mask &&& colNegMask)

set_option maxHeartbeats 2000000 in
lemma checkAll_eq_true : checkAll = true := by
  rfl

lemma allOnes_eq : allOnes = 2 ^ 131072 - 1 := by
  dsimp only [allOnes]
  rw [Nat.shiftLeft_eq, one_mul]

lemma allOnes_testBit (j : Nat) : allOnes.testBit j = decide (j < 131072) := by
  rw [allOnes_eq, Nat.testBit_two_pow_sub_one]

lemma xor_allOnes_testBit {a w : Nat} (hw : w < 131072) :
    (a ^^^ allOnes).testBit w = !(a.testBit w) := by
  rw [Nat.testBit_xor, allOnes_testBit, decide_eq_true hw]
  cases a.testBit w <;> rfl

lemma allOnes_xor_testBit {a w : Nat} (hw : w < 131072) :
    (allOnes ^^^ a).testBit w = !(a.testBit w) := by
  rw [Nat.testBit_xor, allOnes_testBit, decide_eq_true hw]
  cases a.testBit w <;> rfl

def BoundedMask (m : Nat) : Prop := ∀ j, 131072 ≤ j → m.testBit j = false

lemma bounded_zero : BoundedMask 0 := by
  intro j _
  simp

lemma bounded_allOnes : BoundedMask allOnes := by
  intro j hj
  rw [allOnes_testBit]
  exact decide_eq_false (by omega)

lemma bounded_xor {a b : Nat} (ha : BoundedMask a) (hb : BoundedMask b) :
    BoundedMask (a ^^^ b) := by
  intro j hj
  rw [Nat.testBit_xor, ha j hj, hb j hj]
  rfl

lemma bounded_lor {a b : Nat} (ha : BoundedMask a) (hb : BoundedMask b) :
    BoundedMask (a ||| b) := by
  intro j hj
  rw [Nat.testBit_lor, ha j hj, hb j hj]
  rfl

lemma bounded_land_left {a b : Nat} (ha : BoundedMask a) :
    BoundedMask (a &&& b) := by
  intro j hj
  rw [Nat.testBit_land, ha j hj]
  rfl

lemma bounded_land_right {a b : Nat} (hb : BoundedMask b) :
    BoundedMask (a &&& b) := by
  intro j hj
  rw [Nat.testBit_land, hb j hj]
  cases a.testBit j <;> rfl

lemma exists_testBit_of_ne_zero {m : Nat} (hb : BoundedMask m) (hne : m ≠ 0) :
    ∃ w < 131072, m.testBit w = true := by
  by_contra h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < 131072
  · cases hmj : m.testBit j
    · rfl
    · exact absurd ⟨j, hj, hmj⟩ h
  · exact hb j (by omega)

lemma mkPlaneLoop_spec (fuel : Nat) :
    ∀ (acc shift : Nat), 0 < shift →
      (∀ j, shift ≤ j → acc.testBit j = false) →
      (∀ j, shift * 2 ^ fuel ≤ j → (mkPlaneLoop acc shift fuel).testBit j = false) ∧
      (∀ w < shift * 2 ^ fuel, (mkPlaneLoop acc shift fuel).testBit w = acc.testBit (w % shift)) := by
  induction fuel with
  | zero =>
    intro acc shift _ hacc
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hacc j (by simpa using hj)
    · intro w hw
      have hw' : w < shift := by simpa using hw
      simp [mkPlaneLoop, Nat.mod_eq_of_lt hw']
  | succ n ih =>
    intro acc shift hpos hacc
    let acc' := acc ||| (acc <<< shift)
    have hsh' : shift <<< 1 = 2 * shift := by
      rw [Nat.shiftLeft_eq]
      omega
    have hacc'_hi : ∀ j, 2 * shift ≤ j → acc'.testBit j = false := by
      intro j hj
      dsimp only [acc']
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hacc j (by omega)]
      have hge : shift ≤ j := by omega
      have hsub : shift ≤ j - shift := by omega
      rw [decide_eq_true hge, hacc (j - shift) hsub]
      rfl
    have hacc'_lo : ∀ r < 2 * shift, acc'.testBit r = acc.testBit (r % shift) := by
      intro r hr
      dsimp only [acc']
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
      by_cases hlt : r < shift
      · have hnot : ¬(shift ≤ r) := by omega
        rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, Nat.mod_eq_of_lt hlt]
      · have hge : shift ≤ r := by omega
        have hlt2 : r - shift < shift := by omega
        have hmod : r % shift = r - shift := by
          have h1 : r = (r - shift) + shift := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [hacc r hge, decide_eq_true hge, Bool.true_and, Bool.false_or, hmod]
    have hstep := ih acc' (shift <<< 1) (by omega) (by rw [hsh']; exact hacc'_hi)
    have hmul : shift <<< 1 * 2 ^ n = shift * 2 ^ (n + 1) := by
      rw [hsh', pow_succ]
      ring
    refine ⟨?_, ?_⟩
    · intro j hj
      dsimp only [mkPlaneLoop]
      exact hstep.1 j (by rw [hmul]; exact hj)
    · intro w hw
      dsimp only [mkPlaneLoop]
      rw [hstep.2 w (by rw [hmul]; exact hw), hsh', hacc'_lo (w % (2 * shift)) (Nat.mod_lt w (by omega))]
      have hdvd : shift ∣ 2 * shift := ⟨2, by ring⟩
      rw [Nat.mod_mod_of_dvd w hdvd]

lemma mkPlane_spec (idx : Nat) (hidx : idx < 17) :
    BoundedMask (mkPlane idx) ∧
    (∀ w < 131072, (mkPlane idx).testBit w = w.testBit idx) := by
  let half := 1 <<< idx
  let period := 1 <<< (idx + 1)
  let block := ((1 <<< half) - 1) <<< half
  have hhalf : half = 2 ^ idx := by dsimp only [half]; rw [Nat.shiftLeft_eq, one_mul]
  have hperiod : period = 2 ^ (idx + 1) := by dsimp only [period]; rw [Nat.shiftLeft_eq, one_mul]
  have hp2 : period = 2 * half := by rw [hperiod, hhalf, pow_succ]; ring
  have hpos : 0 < period := by rw [hperiod]; positivity
  have hblock_eq : block = (2 ^ half - 1) <<< half := by
    dsimp only [block]
    rw [Nat.shiftLeft_eq 1 half, one_mul]
  have hblock_hi : ∀ j, period ≤ j → block.testBit j = false := by
    intro j hj
    rw [hblock_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : half ≤ j
    · rw [decide_eq_true h1, Bool.true_and, decide_eq_false (by omega)]
    · rw [decide_eq_false h1, Bool.false_and]
  have hblock_lo : ∀ r < period, block.testBit r = decide (half ≤ r) := by
    intro r hr
    rw [hblock_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : half ≤ r
    · rw [decide_eq_true h1, Bool.true_and, decide_eq_true (by omega)]
    · rw [decide_eq_false h1, Bool.false_and]
  have hpow : period * 2 ^ (16 - idx) = 131072 := by
    rw [hperiod, ← pow_add]
    have hexp : idx + 1 + (16 - idx) = 17 := by omega
    rw [hexp]
    decide
  have hloop := mkPlaneLoop_spec (16 - idx) block period hpos hblock_hi
  rw [hpow] at hloop
  refine ⟨hloop.1, ?_⟩
  intro w hw
  change (mkPlaneLoop block period (16 - idx)).testBit w = w.testBit idx
  rw [hloop.2 w hw, hblock_lo (w % period) (Nat.mod_lt w hpos)]
  rw [Nat.testBit_eq_decide_div_mod_eq, hhalf, hperiod]
  have hdiv : w % (2 ^ (idx + 1)) = 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx := by
    have h1 := Nat.div_add_mod w (2 ^ idx)
    have h2 := Nat.div_add_mod (w / 2 ^ idx) 2
    have h3 : 2 ^ (idx + 1) = 2 ^ idx * 2 := by rw [pow_succ]
    have h4 : w = 2 ^ (idx + 1) * (w / 2 ^ idx / 2) + (2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) := by
      calc
        w = 2 ^ idx * (w / 2 ^ idx) + w % 2 ^ idx := h1.symm
        _ = 2 ^ idx * (2 * (w / 2 ^ idx / 2) + (w / 2 ^ idx) % 2) + w % 2 ^ idx := by rw [h2]
        _ = 2 ^ (idx + 1) * (w / 2 ^ idx / 2) + (2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) := by
          rw [h3]; ring
    have hlt_rem : 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx < 2 ^ (idx + 1) := by
      have hm1 : (w / 2 ^ idx) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hm2 : w % 2 ^ idx < 2 ^ idx := Nat.mod_lt _ (by positivity)
      have hpow2 : 2 ^ (idx + 1) = 2 ^ idx * 2 := by rw [pow_succ]
      nlinarith
    conv_lhs => rw [h4]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_rem]
  have hm1 : (w / 2 ^ idx) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hm2 : w % 2 ^ idx < 2 ^ idx := Nat.mod_lt _ (by positivity)
  rw [hdiv]
  have hiff : (2 ^ idx ≤ 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) ↔ ((w / 2 ^ idx) % 2 = 1) := by
    constructor
    · intro hge
      by_contra hne
      have hz : (w / 2 ^ idx) % 2 = 0 := by omega
      rw [hz, mul_zero, zero_add] at hge
      omega
    · intro heq
      rw [heq, mul_one]
      omega
  rw [decide_eq_decide.mpr hiff]

def BoundedPlanes (a : Planes17) : Prop := ∀ b < 17, BoundedMask (a.get b)

def RepPlanes (a : Planes17) (f : Nat → Nat) : Prop :=
  (∀ w < 131072, f w < 131072) ∧ BoundedPlanes a ∧
  ∀ w < 131072, ∀ b < 17, (a.get b).testBit w = (f w).testBit b

def scalarRot (s word : Nat) : Nat :=
  ((word <<< (s % 17)) ||| (word >>> (17 - s % 17))) % 2 ^ 17

def scalarStep (word : Nat) : Nat :=
  (List.range 17).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))).toNat <<< b)) 0

def scalarOut (w : Nat) : Nat :=
  ((List.range 4).foldl (fun x t =>
    scalarStep (x ^^^ scalarRot 1 x ^^^ scalarRot (17 - 1) x) ^^^ scalarRot (2 * t) w ^^^
      (3 ^ (17 + (t + 1)) % 2 ^ 17)) (scalarRot 1 w))

def scalarCol (key name : Nat) : Nat :=
  (List.range 4).foldl (fun state j =>
    scalarStep (state ^^^ scalarRot 2 state ^^^ scalarRot (17 - 2) state) ^^^
      scalarRot (3 * (j + 1) + 1) key ^^^ (3 ^ (17 + (4 + (j + 1))) % 2 ^ 17))
    (scalarRot 3 key ^^^ name)

lemma scalarRot_lt (s word : Nat) : scalarRot s word < 131072 := by
  exact Nat.mod_lt _ (by decide)

lemma scalarRot_testBit {word : Nat} (hword : word < 131072) (s b : Nat) (hb : b < 17) :
    (scalarRot s word).testBit b = word.testBit ((b + 17 - s % 17) % 17) := by
  dsimp only [scalarRot]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and,
    Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : s % 17 < 17 := Nat.mod_lt s (by omega)
  by_cases hle : s % 17 ≤ b
  · have hhi : word.testBit (17 - s % 17 + b) = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (show word < 2 ^ 17 from hword) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ 17 - s % 17 + b)))
    have hidx : (b + 17 - s % 17) % 17 = b - s % 17 := by
      have h1 : b + 17 - s % 17 = (b - s % 17) + 17 := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hidx : (b + 17 - s % 17) % 17 = 17 - s % 17 + b := by
      have h1 : b + 17 - s % 17 = 17 - s % 17 + b := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hidx]

lemma scalarStep_spec (word : Nat) :
    scalarStep word < 131072 ∧
    ∀ b < 17, (scalarStep word).testBit b =
      xor (word.testBit b) (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17)) := by
  let bitFn : Nat → Bool := fun b =>
    xor (word.testBit b) (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))
  have htake : ∀ m ≤ 17,
      let v := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      (∀ j, m ≤ j → v.testBit j = false) ∧ (∀ b < m, v.testBit b = bitFn b) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun j _ => by simp, fun b hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hrange : List.range (m + 1) = List.range m ++ [m] := List.range_succ
      dsimp only
      rw [hrange, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      set prev := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 j (by omega)]
        have h1 : m ≤ j := by omega
        have hgt : 1 ≤ j - m := by omega
        have hlt2 : (bitFn m).toNat < 2 ^ (j - m) := by
          have hle1 : (bitFn m).toNat ≤ 1 := by cases bitFn m <;> decide
          have hpow : 2 ≤ 2 ^ (j - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true h1, Bool.true_and, Nat.testBit_eq_false_of_lt hlt2]
        rfl
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b = m
        · subst hbm
          rw [hprev.1 b le_rfl, decide_eq_true le_rfl, Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
        · have hlt : b < m := by omega
          have hnot : ¬(m ≤ b) := by omega
          rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, hprev.2 b hlt]
  have hfull := htake 17 le_rfl
  refine ⟨?_, hfull.2⟩
  by_contra hge
  have h1 : 2 ^ 17 ≤ scalarStep word := by omega
  have hlog : 17 ≤ Nat.log2 (scalarStep word) := by
    have hne : scalarStep word ≠ 0 := by omega
    have := (Nat.le_log2 hne).mpr h1
    exact this
  have htrue : (scalarStep word).testBit (Nat.log2 (scalarStep word)) = true :=
    Nat.testBit_log2 (by omega)
  have hfalse : (scalarStep word).testBit (Nat.log2 (scalarStep word)) = false :=
    hfull.1 _ hlog
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

lemma keyPlanes_rep : RepPlanes keyPlanes id := by
  refine ⟨fun w hw => hw, ?_, ?_⟩
  · intro b hb
    interval_cases b <;> exact (mkPlane_spec _ (by omega)).1
  · intro w hw b hb
    interval_cases b <;> exact (mkPlane_spec _ (by omega)).2 w hw

lemma xor_rep {a b : Planes17} {f g : Nat → Nat}
    (ha : RepPlanes a f) (hb : RepPlanes b g) :
    RepPlanes (a.xor b) (fun w => f w ^^^ g w) := by
  refine ⟨fun w hw => Nat.xor_lt_two_pow (n := 17) (ha.1 w hw) (hb.1 w hw), ?_, ?_⟩
  · intro i hi
    have hget : (a.xor b).get i = a.get i ^^^ b.get i := by interval_cases i <;> rfl
    rw [hget]
    exact bounded_xor (ha.2.1 i hi) (hb.2.1 i hi)
  · intro w hw i hi
    have hget : (a.xor b).get i = a.get i ^^^ b.get i := by interval_cases i <;> rfl
    rw [hget, Nat.testBit_xor, Nat.testBit_xor, ha.2.2 w hw i hi, hb.2.2 w hw i hi]

lemma xorConst_rep {a : Planes17} {f : Nat → Nat} {c : Nat}
    (ha : RepPlanes a f) (hc : c < 131072) :
    RepPlanes (a.xorConst c) (fun w => f w ^^^ c) := by
  refine ⟨fun w hw => Nat.xor_lt_two_pow (n := 17) (ha.1 w hw) hc, ?_, ?_⟩
  · intro i hi
    have hget : (a.xorConst c).get i = if c.testBit i then a.get i ^^^ allOnes else a.get i := by
      interval_cases i <;> rfl
    rw [hget]
    split_ifs
    · exact bounded_xor (ha.2.1 i hi) bounded_allOnes
    · exact ha.2.1 i hi
  · intro w hw i hi
    have hget : (a.xorConst c).get i = if c.testBit i then a.get i ^^^ allOnes else a.get i := by
      interval_cases i <;> rfl
    rw [hget, Nat.testBit_xor, ← ha.2.2 w hw i hi]
    cases hci : c.testBit i
    · simp
    · simp only [↓reduceIte, xor_allOnes_testBit hw]
      cases (a.get i).testBit w <;> rfl

lemma rot1_get (a : Planes17) (b : Nat) (hb : b < 17) :
    a.rot1.get b = a.get ((b + 16) % 17) := by
  interval_cases b <;> rfl

lemma rotIter_get (n : Nat) : ∀ (a : Planes17) (b : Nat), b < 17 →
    (a.rotIter n).get b = a.get ((b + 17 - n % 17) % 17) := by
  induction n with
  | zero =>
    intro a b hb
    simp [Planes17.rotIter, Nat.mod_eq_of_lt hb]
  | succ n ih =>
    intro a b hb
    dsimp only [Planes17.rotIter]
    rw [ih a.rot1 b hb, rot1_get a _ (Nat.mod_lt _ (by omega))]
    congr 1
    have h1 : (b + 17 - n % 17) % 17 + 16 = (b + 17 - n % 17) % 17 + 16 := rfl
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hns : n % 17 < 17 := Nat.mod_lt n (by omega)
    by_cases h16 : n % 17 = 16
    · have hmod : (n + 1) % 17 = 0 := by
        rw [Nat.add_mod, h16]
      rw [hmod, h16]
      have heq : b + 17 - 16 + 16 = b + 17 := by omega
      rw [heq, Nat.sub_zero]
    · have hmod : (n + 1) % 17 = n % 17 + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 17), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have heq : b + 17 - n % 17 + 16 = (b + 17 - (n % 17 + 1)) + 17 := by omega
      rw [heq, Nat.add_mod_right]

lemma rotN_rep {a : Planes17} {f : Nat → Nat} (ha : RepPlanes a f) (s : Nat) :
    RepPlanes (a.rotN s) (fun w => scalarRot s (f w)) := by
  refine ⟨fun w _ => scalarRot_lt s (f w), ?_, ?_⟩
  · intro b hb
    dsimp only [Planes17.rotN]
    rw [rotIter_get (s % 17) a b hb]
    exact ha.2.1 _ (Nat.mod_lt _ (by omega))
  · intro w hw b hb
    dsimp only [Planes17.rotN]
    rw [rotIter_get (s % 17) a b hb, Nat.mod_mod,
      ha.2.2 w hw _ (Nat.mod_lt _ (by omega)),
      scalarRot_testBit (ha.1 w hw) s b hb]

lemma step_rep {a : Planes17} {f : Nat → Nat} (ha : RepPlanes a f) :
    RepPlanes a.step (fun w => scalarStep (f w)) := by
  refine ⟨fun w _ => (scalarStep_spec (f w)).1, ?_, ?_⟩
  · intro b hb
    have hget : a.step.get b =
        a.get b ^^^ ((allOnes ^^^ a.get ((b + 1) % 17)) &&& a.get ((b + 2) % 17)) := by
      interval_cases b <;> rfl
    rw [hget]
    exact bounded_xor (ha.2.1 b hb) (bounded_land_right (ha.2.1 _ (Nat.mod_lt _ (by omega))))
  · intro w hw b hb
    have hget : a.step.get b =
        a.get b ^^^ ((allOnes ^^^ a.get ((b + 1) % 17)) &&& a.get ((b + 2) % 17)) := by
      interval_cases b <;> rfl
    rw [hget, Nat.testBit_xor, Nat.testBit_land, allOnes_xor_testBit hw,
      ha.2.2 w hw b hb, ha.2.2 w hw _ (Nat.mod_lt _ (by omega)),
      ha.2.2 w hw _ (Nat.mod_lt _ (by omega)), (scalarStep_spec (f w)).2 b hb]

lemma hiZero_spec {a : Planes17} {f : Nat → Nat} (ha : RepPlanes a f) :
    BoundedMask a.hiZero ∧
    ∀ w < 131072, a.hiZero.testBit w = true ↔ f w < 256 := by
  refine ⟨?_, ?_⟩
  · dsimp only [Planes17.hiZero]
    refine bounded_xor bounded_allOnes ?_
    exact bounded_lor (bounded_lor (bounded_lor (bounded_lor (bounded_lor (bounded_lor
      (bounded_lor (bounded_lor (ha.2.1 8 (by omega)) (ha.2.1 9 (by omega)))
        (ha.2.1 10 (by omega))) (ha.2.1 11 (by omega))) (ha.2.1 12 (by omega)))
      (ha.2.1 13 (by omega))) (ha.2.1 14 (by omega))) (ha.2.1 15 (by omega)))
      (ha.2.1 16 (by omega))
  · intro w hw
    dsimp only [Planes17.hiZero]
    rw [allOnes_xor_testBit hw]
    simp only [Nat.testBit_lor, Bool.not_eq_true', Bool.or_eq_false_iff]
    have hrep : ∀ b, 8 ≤ b → b < 17 → (a.get b).testBit w = (f w).testBit b :=
      fun b _ hb => ha.2.2 w hw b hb
    change (((((((((a.get 8).testBit w = false ∧ (a.get 9).testBit w = false) ∧
      (a.get 10).testBit w = false) ∧ (a.get 11).testBit w = false) ∧
      (a.get 12).testBit w = false) ∧ (a.get 13).testBit w = false) ∧
      (a.get 14).testBit w = false) ∧ (a.get 15).testBit w = false) ∧
      (a.get 16).testBit w = false) ↔ f w < 256
    rw [hrep 8 (by omega) (by omega), hrep 9 (by omega) (by omega),
        hrep 10 (by omega) (by omega), hrep 11 (by omega) (by omega),
        hrep 12 (by omega) (by omega), hrep 13 (by omega) (by omega),
        hrep 14 (by omega) (by omega), hrep 15 (by omega) (by omega),
        hrep 16 (by omega) (by omega)]
    constructor
    · intro h
      have hdiv0 : f w / 2 ^ 8 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.zero_testBit, Nat.testBit_div_two_pow]
        by_cases hj : j < 9
        · interval_cases j
          · exact h.1.1.1.1.1.1.1.1
          · exact h.1.1.1.1.1.1.1.2
          · exact h.1.1.1.1.1.1.2
          · exact h.1.1.1.1.1.2
          · exact h.1.1.1.1.2
          · exact h.1.1.1.2
          · exact h.1.1.2
          · exact h.1.2
          · exact h.2
        · exact Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (show f w < 2 ^ 17 from ha.1 w hw)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ j + 8)))
      have hlt := (Nat.div_eq_zero_iff_lt (by omega : 0 < 2 ^ 8)).mp hdiv0
      exact hlt
    · intro hlt
      have hall : ∀ b, 8 ≤ b → (f w).testBit b = false := fun b hb =>
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (show f w < 2 ^ 8 from hlt) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hb))
      exact ⟨⟨⟨⟨⟨⟨⟨⟨hall 8 (by omega), hall 9 (by omega)⟩, hall 10 (by omega)⟩,
        hall 11 (by omega)⟩, hall 12 (by omega)⟩, hall 13 (by omega)⟩,
        hall 14 (by omega)⟩, hall 15 (by omega)⟩, hall 16 (by omega)⟩

lemma outRound_rep {w x : Planes17} {fw fx : Nat → Nat} (t : Nat)
    (hw : RepPlanes w fw) (hx : RepPlanes x fx) :
    RepPlanes (outRound w x t) (fun k =>
      scalarStep (fx k ^^^ scalarRot 1 (fx k) ^^^ scalarRot 16 (fx k)) ^^^
      scalarRot (2 * t) (fw k) ^^^ (3 ^ (17 + (t + 1)) % 131072)) := by
  dsimp only [outRound]
  exact xorConst_rep
    (xor_rep (step_rep (xor_rep (xor_rep hx (rotN_rep hx 1)) (rotN_rep hx 16))) (rotN_rep hw (2 * t)))
    (Nat.mod_lt _ (by decide))

lemma outPlanes_rep {w : Planes17} {fw : Nat → Nat} (hw : RepPlanes w fw) :
    RepPlanes (outPlanes w) (fun k => scalarOut (fw k)) := by
  dsimp only [outPlanes]
  have hr0 := rotN_rep hw 1
  have hr1 := outRound_rep 0 hw hr0
  have hr2 := outRound_rep 1 hw hr1
  have hr3 := outRound_rep 2 hw hr2
  have hr4 := outRound_rep 3 hw hr3
  exact hr4

lemma colRound_rep {w st : Planes17} {fw fst : Nat → Nat} (j : Nat)
    (hw : RepPlanes w fw) (hst : RepPlanes st fst) :
    RepPlanes (colRound w st j) (fun k =>
      scalarStep (fst k ^^^ scalarRot 2 (fst k) ^^^ scalarRot 15 (fst k)) ^^^
      scalarRot (3 * (j + 1) + 1) (fw k) ^^^ (3 ^ (17 + (4 + (j + 1))) % 131072)) := by
  dsimp only [colRound]
  exact xorConst_rep
    (xor_rep (step_rep (xor_rep (xor_rep hst (rotN_rep hst 2)) (rotN_rep hst 15)))
      (rotN_rep hw (3 * (j + 1) + 1)))
    (Nat.mod_lt _ (by decide))

lemma colMask_spec {name : Nat} (hname : name < 131072) :
    BoundedMask (colMask keyPlanes name) ∧
    ∀ w < 131072, (colMask keyPlanes name).testBit w = true ↔ scalarCol w name < 256 := by
  dsimp only [colMask]
  have hr0 := xorConst_rep (rotN_rep keyPlanes_rep 3) hname
  have hr1 := colRound_rep 0 keyPlanes_rep hr0
  have hr2 := colRound_rep 1 keyPlanes_rep hr1
  have hr3 := colRound_rep 2 keyPlanes_rep hr2
  have hr4 := colRound_rep 3 keyPlanes_rep hr3
  exact hiZero_spec hr4

lemma foldl_lor_spec (f : Nat → Nat) (l : List Nat) :
    ∀ init : Nat,
      (BoundedMask init → (∀ x ∈ l, BoundedMask (f x)) → BoundedMask (l.foldl (fun acc x => acc ||| f x) init)) ∧
      (∀ w, (l.foldl (fun acc x => acc ||| f x) init).testBit w = true ↔
        init.testBit w = true ∨ ∃ x ∈ l, (f x).testBit w = true) := by
  induction l with
  | nil =>
    intro init
    refine ⟨fun h _ => h, fun w => by simp⟩
  | cons a tl ih =>
    intro init
    refine ⟨?_, ?_⟩
    · intro hinit hall
      simp only [List.foldl_cons]
      exact (ih (init ||| f a)).1 (bounded_lor hinit (hall a (by simp))) (fun x hx => hall x (by simp [hx]))
    · intro w
      simp only [List.foldl_cons, (ih (init ||| f a)).2 w, Nat.testBit_lor, Bool.or_eq_true]
      constructor
      · rintro ((h1 | h2) | ⟨x, hx, hfx⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨a, by simp, h2⟩
        · exact Or.inr ⟨x, by simp [hx], hfx⟩
      · rintro (h1 | ⟨x, hx, hfx⟩)
        · exact Or.inl (Or.inl h1)
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | htl
          · exact Or.inl (Or.inr hfx)
          · exact Or.inr ⟨x, htl, hfx⟩

lemma coversNames_sound : ∀ (ps : List Nat) (m0 mneg : Nat),
    BoundedMask mneg →
    coversNames ps m0 mneg = true →
    ∀ w < 131072, m0.testBit w = true →
      ∃ w' < 131072, mneg.testBit w' = true ∧ ∀ p ∈ ps, p.testBit w' = p.testBit w := by
  intro ps
  induction ps with
  | nil =>
    intro m0 mneg hb hcov w hw hm0
    dsimp only [coversNames] at hcov
    have hm0_ne : m0 ≠ 0 := by
      intro h0
      rw [h0, Nat.zero_testBit] at hm0
      exact Bool.noConfusion hm0
    have hbe : (m0 == 0) = false := beq_false_of_ne hm0_ne
    rw [hbe, Bool.false_or] at hcov
    have hmneg_ne : mneg ≠ 0 := by
      intro h0
      rw [h0] at hcov
      exact Bool.noConfusion hcov
    rcases exists_testBit_of_ne_zero hb hmneg_ne with ⟨w', hw', hmw'⟩
    exact ⟨w', hw', hmw', fun _ hp => by simp at hp⟩
  | cons p ps ih =>
    intro m0 mneg hb hcov w hw hm0
    dsimp only [coversNames] at hcov
    have hm0_ne : m0 ≠ 0 := by
      intro h0
      rw [h0, Nat.zero_testBit] at hm0
      exact Bool.noConfusion hm0
    have hbe : (m0 == 0) = false := beq_false_of_ne hm0_ne
    rw [hbe] at hcov
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hcov
    cases hpw : p.testBit w
    · have hm0' : (m0 &&& (allOnes ^^^ p)).testBit w = true := by
        rw [Nat.testBit_land, allOnes_xor_testBit hw, hm0, hpw]
        rfl
      rcases ih (m0 &&& (allOnes ^^^ p)) (mneg &&& (allOnes ^^^ p))
        (bounded_land_left hb) hcov.2 w hw hm0' with ⟨w', hw', hmn', hrest⟩
      rw [Nat.testBit_land, allOnes_xor_testBit hw', Bool.and_eq_true] at hmn'
      refine ⟨w', hw', hmn'.1, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hqp | htl
      · subst q
        have hpw' : p.testBit w' = false := by
          cases h : p.testBit w'
          · rfl
          · rw [h] at hmn'
            exact Bool.noConfusion hmn'.2
        rw [hpw', hpw]
      · exact hrest q htl
    · have hm0' : (m0 &&& p).testBit w = true := by
        rw [Nat.testBit_land, hm0, hpw]
        rfl
      rcases ih (m0 &&& p) (mneg &&& p)
        (bounded_land_left hb) hcov.1 w hw hm0' with ⟨w', hw', hmn', hrest⟩
      rw [Nat.testBit_land, Bool.and_eq_true] at hmn'
      refine ⟨w', hw', hmn'.1, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hqp | htl
      · subst q
        rw [hmn'.2, hpw]
      · exact hrest q htl

end PEqualNP.Outside.L_lib_537_aux

open PEqualNP.Outside.L_lib_537_aux

theorem PEqualNP.Outside.L_lib_537 :
let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
let columnPass := fun (key name : Nat) =>
  ((List.range 4).foldl (fun state j =>
    step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (k + (4 + (j + 1))) % 2 ^ k))
    (rot 3 key ^^^ name)) < 2 ^ 8
let keys := List.range (2 ^ k)
∀ lookup : Nat → Bool, ∃ column : Fin (2 ^ k),
  column.val ∈ ([0, 1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29] : List Nat) ∧
  ¬ ((∃ w ∈ keys, output w = 0 ∧ columnPass w column.val) ↔
    (∃ candidate ∈ keys,
      (if candidate.testBit 2 then output candidate = 0
       else lookup (output (candidate ^^^ 12)) = true) ∧ columnPass candidate column.val)) := by
  intro k rot step output columnPass keys lookup
  have hchecks := checkAll_eq_true
  dsimp only [checkAll] at hchecks
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hchecks
  have ht1 : outZMask &&& col0Mask ≠ 0 := hchecks.1.1.1
  have ht2 : outZMask &&& colNegMask = 0 := hchecks.1.1.2
  have ht3 : bit2Mask &&& outZMask &&& col0Mask = 0 := hchecks.1.2
  have ht4 : coversNames mateHiList (nbit2Mask &&& col0Mask) (nbit2Mask &&& colNegMask) = true := hchecks.2
  have houtRep : RepPlanes (outPlanes keyPlanes) scalarOut := outPlanes_rep keyPlanes_rep
  have houtZ := hiZero_spec houtRep
  have hcol0 := colMask_spec (name := 0) (by decide)
  have hneg_lt : ∀ c ∈ negCols, c < 131072 := by
    intro c hc
    simp only [negCols, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hcolNeg_spec := foldl_lor_spec (colMask keyPlanes) negCols 0
  have hcolNeg_bd : BoundedMask colNegMask :=
    hcolNeg_spec.1 bounded_zero (fun c hc => (colMask_spec (hneg_lt c hc)).1)
  have hcolNeg_tb : ∀ w < 131072, colNegMask.testBit w = true ↔
      ∃ c ∈ negCols, columnPass w c := by
    intro w hw
    rw [colNegMask, hcolNeg_spec.2 w]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨c, hc, htb⟩
      exact ⟨c, hc, (colMask_spec (hneg_lt c hc)).2 w hw |>.mp htb⟩
    · rintro ⟨c, hc, hcp⟩
      exact ⟨c, hc, (colMask_spec (hneg_lt c hc)).2 w hw |>.mpr hcp⟩
  have hout_eq_zero_iff : ∀ w < 131072, outZMask.testBit w = true ↔ output w = 0 := by
    intro w hw
    rw [outZMask, houtZ.2 w hw]
    change scalarOut w < 256 ↔ scalarOut w >>> 8 = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_eq_zero_iff_lt (by omega : 0 < 2 ^ 8)).symm
  have hbit2_tb : ∀ w < 131072, bit2Mask.testBit w = w.testBit 2 := fun w hw =>
    (mkPlane_spec 2 (by omega)).2 w hw
  have hnbit2_tb : ∀ w < 131072, nbit2Mask.testBit w = !(w.testBit 2) := fun w hw => by
    dsimp only [nbit2Mask]
    rw [allOnes_xor_testBit hw, hbit2_tb w hw]
  have hmateKeyRep : RepPlanes mateKeyPlanes (fun w => w ^^^ 12) :=
    xorConst_rep keyPlanes_rep (by decide)
  have hmateOutRep : RepPlanes mateOutPlanes (fun w => scalarOut (w ^^^ 12)) :=
    outPlanes_rep hmateKeyRep
  by_cases haccept : ∃ w < 131072, w.testBit 2 = false ∧ columnPass w 0 ∧
      lookup (output (w ^^^ 12)) = true
  · rcases haccept with ⟨w, hw, hw2, hcw0, hlu⟩
    have hm0_tb : (nbit2Mask &&& col0Mask).testBit w = true := by
      dsimp only [col0Mask]
      rw [Nat.testBit_land, hnbit2_tb w hw, hw2, (hcol0.2 w hw).mpr hcw0]
      rfl
    have hmn_bd : BoundedMask (nbit2Mask &&& colNegMask) := bounded_land_right hcolNeg_bd
    rcases coversNames_sound mateHiList _ _ hmn_bd ht4 w hw hm0_tb with ⟨w', hw', hmn', hplanes⟩
    rw [Nat.testBit_land, hnbit2_tb w' hw', Bool.and_eq_true] at hmn'
    have hw'2 : w'.testBit 2 = false := by
      cases h : w'.testBit 2
      · rfl
      · rw [h] at hmn'
        exact Bool.noConfusion hmn'.1
    rcases (hcolNeg_tb w' hw').mp hmn'.2 with ⟨c, hc_mem, hcw'⟩
    have hc_lt : c < 2 ^ k := hneg_lt c hc_mem
    have hc_in_all : c ∈ ([0, 1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29] : List Nat) :=
      List.mem_cons_of_mem 0 hc_mem
    have hout_eq : output (w' ^^^ 12) = output (w ^^^ 12) := by
      change scalarOut (w' ^^^ 12) >>> 8 = scalarOut (w ^^^ 12) >>> 8
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      by_cases hj : j < 9
      · have hrep1 := hmateOutRep.2.2 w' hw' (8 + j) (by omega)
        have hrep2 := hmateOutRep.2.2 w hw (8 + j) (by omega)
        rw [← hrep1, ← hrep2]
        interval_cases j
        · exact hplanes mateOutPlanes.p8 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p9 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p10 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p11 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p12 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p13 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p14 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p15 (by simp [mateHiList])
        · exact hplanes mateOutPlanes.p16 (by simp [mateHiList])
      · have h1 := Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (show scalarOut (w' ^^^ 12) < 2 ^ 17 from hmateOutRep.1 w' hw')
            (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ 8 + j)))
        have h2 := Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (show scalarOut (w ^^^ 12) < 2 ^ 17 from hmateOutRep.1 w hw)
            (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ 8 + j)))
        rw [h1, h2]
    refine ⟨⟨c, hc_lt⟩, hc_in_all, ?_⟩
    intro hiff
    have hrhs : ∃ candidate ∈ keys,
        (if candidate.testBit 2 then output candidate = 0
         else lookup (output (candidate ^^^ 12)) = true) ∧ columnPass candidate c := by
      refine ⟨w', List.mem_range.mpr hw', ?_, hcw'⟩
      rw [hw'2]
      simp only [Bool.false_eq_true, ↓reduceIte, hout_eq, hlu]
    rcases hiff.mpr hrhs with ⟨u, hu_mem, hou, hcu⟩
    have hu_lt : u < 131072 := List.mem_range.mp hu_mem
    have htb : (outZMask &&& colNegMask).testBit u = true := by
      rw [Nat.testBit_land, (hout_eq_zero_iff u hu_lt).mpr hou,
        (hcolNeg_tb u hu_lt).mpr ⟨c, hc_mem, hcu⟩]
      rfl
    rw [ht2, Nat.zero_testBit] at htb
    exact Bool.noConfusion htb
  · refine ⟨⟨0, by decide⟩, by simp, ?_⟩
    intro hiff
    have hbd1 : BoundedMask (outZMask &&& col0Mask) := bounded_land_left houtZ.1
    rcases exists_testBit_of_ne_zero hbd1 ht1 with ⟨w0, hw0, htb0⟩
    rw [Nat.testBit_land, Bool.and_eq_true] at htb0
    have hlhs : ∃ w ∈ keys, output w = 0 ∧ columnPass w 0 :=
      ⟨w0, List.mem_range.mpr hw0, (hout_eq_zero_iff w0 hw0).mp htb0.1, (hcol0.2 w0 hw0).mp htb0.2⟩
    rcases hiff.mp hlhs with ⟨cand, hcand_mem, hcond, hcc0⟩
    have hcand_lt : cand < 131072 := List.mem_range.mp hcand_mem
    cases hb2 : cand.testBit 2
    · rw [hb2] at hcond
      simp only [Bool.false_eq_true, ↓reduceIte] at hcond
      exact haccept ⟨cand, hcand_lt, hb2, hcc0, hcond⟩
    · rw [hb2] at hcond
      simp only [↓reduceIte] at hcond
      have htb3 : (bit2Mask &&& outZMask &&& col0Mask).testBit cand = true := by
        dsimp only [col0Mask]
        rw [Nat.testBit_land, Nat.testBit_land, hbit2_tb cand hcand_lt, hb2,
          (hout_eq_zero_iff cand hcand_lt).mpr hcond, (hcol0.2 cand hcand_lt).mpr hcc0]
        rfl
      rw [ht3, Nat.zero_testBit] at htb3
      exact Bool.noConfusion htb3
