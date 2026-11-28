import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50199

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma decide_not_eq (op : GateOp) (inst : Decidable (op = GateOp.not)) :
    @decide (op = GateOp.not) inst = isNotOp op := by
  cases op <;> cases inst with
  | isTrue h =>
    first
    | rfl
    | cases h
  | isFalse h =>
    first
    | rfl
    | exact False.elim (h rfl)

lemma notCount_eq_filter (D : Circuit) :
    notCount D = (D.gates.filter fun g => isNotOp g.op).length := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  exact decide_not_eq g.op _

def inp (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

lemma pack6_lt_aux (b0 b1 b2 b3 b4 b5 : Bool) :
    (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) < 64 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

def pack6 (b : Fin 6 → Bool) : Fin 64 :=
  ⟨(if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) +
   (if b 3 then 8 else 0) + (if b 4 then 16 else 0) + (if b 5 then 32 else 0),
   pack6_lt_aux (b 0) (b 1) (b 2) (b 3) (b 4) (b 5)⟩

lemma pack6_bit_aux : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (i : Fin 6),
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
     (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)).testBit i.val =
    match i.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5 := by
  decide +kernel

lemma pack6_bit (b : Fin 6 → Bool) (t : Fin 6) :
    (pack6 b).val.testBit t.val = b t := by
  have h := pack6_bit_aux (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) t
  rcases t with ⟨v, hv⟩
  match v with
  | 0 => exact h
  | 1 => exact h
  | 2 => exact h
  | 3 => exact h
  | 4 => exact h
  | 5 => exact h
  | v + 6 => omega

lemma fin64_eq_of_bits (x y : Fin 64)
    (h : ∀ t : Fin 6, x.val.testBit t.val = y.val.testBit t.val) : x = y := by
  revert x y h
  decide +kernel

lemma and_lt64 (a b : Fin 64) : a.val &&& b.val < 64 := by revert a b; decide +kernel
lemma or_lt64 (a b : Fin 64) : a.val ||| b.val < 64 := by revert a b; decide +kernel
lemma not_lt64 (a : Fin 64) : 63 ^^^ a.val < 64 := by revert a; decide +kernel

lemma pack6_false : pack6 (fun _ => false) = ⟨0, by decide⟩ := by decide +kernel
lemma pack6_true : pack6 (fun _ => true) = ⟨63, by decide⟩ := by decide +kernel

lemma pack6_and (f g : Fin 6 → Bool) :
    pack6 (fun t => f t && g t) = ⟨(pack6 f).val &&& (pack6 g).val, and_lt64 _ _⟩ := by
  apply fin64_eq_of_bits
  intro t
  rw [pack6_bit, Nat.testBit_and, pack6_bit, pack6_bit]

lemma pack6_or (f g : Fin 6 → Bool) :
    pack6 (fun t => f t || g t) = ⟨(pack6 f).val ||| (pack6 g).val, or_lt64 _ _⟩ := by
  apply fin64_eq_of_bits
  intro t
  rw [pack6_bit, Nat.testBit_or, pack6_bit, pack6_bit]

lemma pack6_not (f : Fin 6 → Bool) :
    pack6 (fun t => !(f t)) = ⟨63 ^^^ (pack6 f).val, not_lt64 _⟩ := by
  apply fin64_eq_of_bits
  intro t
  rw [pack6_bit, Nat.testBit_xor, pack6_bit]
  have h63 : (63 : Nat).testBit t.val = true := by revert t; decide +kernel
  rw [h63]
  cases f t <;> rfl

def initSet : Nat := 0xd101000100000001

lemma init_sub_check : ∀ u : Fin 7,
    initSet.testBit (pack6 (fun t => (inp t).getD u.val false)).val = true := by
  decide +kernel

lemma init_bit0 : initSet.testBit 0 = true := by decide +kernel
lemma init_bit63 : initSet.testBit 63 = true := by decide +kernel

lemma inp_mem (w : Nat) : initSet.testBit (pack6 (fun t => (inp t).getD w false)).val = true := by
  by_cases hw : w < 7
  · exact init_sub_check ⟨w, hw⟩
  · have hfalse : (fun t : Fin 6 => (inp t).getD w false) = (fun _ => false) := by
      funext t
      exact List.getD_eq_default _ _ (by simp [inp]; omega)
    rw [hfalse, pack6_false]
    exact init_bit0

def goalCnt (s : Nat) : Nat :=
  (if s.testBit 34 then 1 else 0) + (if s.testBit 36 then 1 else 0) + (if s.testBit 50 then 1 else 0)

def subState (p q : Nat × Nat) : Bool :=
  ((p.1 &&& q.1) == p.1) && decide (q.2 ≤ p.2)

def cert : Nat → List (Nat × Nat)
  | 0 => [(0xd101000100000001, 0)]
  | 1 => [(0xd101000100000003, 1), (0xd101000100000009, 1), (0xd101000100000081, 1), (0xd101000100008001, 1), (0xd101000180000001, 1), (0xd101000100000001, 0)]
  | 2 => [(0xd181000100000081, 1), (0xd10100010000000d, 1), (0xd101800100008001, 1), (0xd109000100000009, 1), (0xd101008100000081, 1), (0xd301000100000003, 1), (0xd101000100000091, 1), (0xd10100010000c001, 1), (0xd1010001000000c1, 1), (0xf101000100000003, 1), (0xd901000100000009, 1), (0xd101000100009001, 1), (0xd101000300000003, 1), (0xd101000180010001, 1), (0xd101000900000009, 1), (0xd101000181000001, 1), (0xd103000100000003, 1), (0xd101000190000001, 1), (0xd1010001c0000001, 1), (0xd101000100008101, 1), (0xd101000100008003, 2), (0xd101000180000009, 2), (0xd101000100000083, 2), (0xd101000180008001, 2), (0xd101000100008009, 2), (0xd101000100000089, 2), (0xd101000180000081, 2), (0xd101000100008081, 2), (0xd10100010000000b, 2), (0xd101000180000003, 2), (0xd101000100000001, 0)]
  | 3 => [(0xd1010001000000d1, 1), (0xd10100010000d001, 1), (0xd10d000100000009, 1), (0xd10500010000000d, 1), (0xd1410001000000c1, 1), (0xd10140010000c001, 1), (0xd101000190010001, 1), (0xd101000181010001, 1), (0xd101000d00000009, 1), (0xd101810100008001, 1), (0xd103000300000003, 1), (0xd181008100000081, 1), (0xd101800100008101, 1), (0xd1810001000000c1, 1), (0xd10180010000c001, 1), (0xd101800100009001, 1), (0xd101000100009101, 1), (0xd1010041000000c1, 1), (0xd191000100000081, 1), (0xd10900010000000d, 1), (0xd101009100000081, 1), (0xd1010001c1000001, 1), (0xd111000100000091, 1), (0xd909000100000009, 1), (0xd90100010000000d, 1), (0xd181000100000091, 1), (0xd109000900000009, 1), (0xd1c1000100000081, 1), (0xd101008100000091, 1), (0xd10100c100000081, 1), (0xd301000300000003, 1), (0xf101000300000003, 1), (0xd303000100000003, 1), (0xf103000100000003, 1), (0xd101001100000091, 1), (0xd1010001d0000001, 1), (0xd101900100008001, 1), (0xd10100090000000d, 1), (0xd10100050000000d, 1), (0xd1010081000000c1, 1), (0xd901000900000009, 1), (0xd101100100009001, 1), (0xd1010001c0010001, 1), (0xd101010100008101, 1), (0xd50100010000000d, 1), (0xdd01000100000009, 1), (0xd101000191000001, 1), (0xf301000100000003, 1), (0xd101c00100008001, 1), (0xd10100010000c101, 1), (0xd101008181000001, 2), (0xd109000180000009, 2), (0xd101800100008009, 2), (0xd103000100000083, 2), (0xd101000180000091, 2), (0xd101000181000081, 2), (0xd101800180008001, 2), (0xd101008100000089, 2), (0xd101800100018001, 2), (0xd101000180010003, 2), (0xd103000100004003, 2), (0xd181000180000081, 2), (0xd10100018000000d, 2), (0xf10100010000000d, 2), (0xd30100010000000b, 2), (0xd101008100008081, 2), (0xd181000100000181, 2), (0xd301000100008003, 2), (0xd1010001000080c1, 2), (0xd101000100008103, 2), (0xd301000100000043, 2), (0xd101008100000083, 2), (0xd101000380000003, 2), (0xd10100010000c003, 2), (0xd103000180000003, 2), (0xd101000100009003, 2), (0xd10300010000c001, 2), (0xd101000990000001, 2), (0xd181000100000089, 2), (0xd109000100009001, 2), (0xd1010001000000c3, 2), (0xd101000900000089, 2), (0xd101000190000081, 2), (0xd101000100000099, 2), (0xf10100010000000b, 2), (0xd1010003c0000001, 2), (0xd101000100009009, 2), (0xd901000180000009, 2), (0xd101800100008081, 2), (0xd101000100008091, 2), (0xf101000100008003, 2), (0xd10100030000000b, 2), (0xd101000980000009, 2), (0xd109000100001009, 2), (0xd301000100000083, 2), (0xd10100010000c081, 2), (0xf101000100000083, 2), (0xd901000100000019, 2), (0xd101000910000009, 2), (0xd10900010000000b, 2), (0xd101000100009081, 2), (0xd1010001c0000009, 2), (0xd101000100000093, 2), (0xd101800100008003, 2), (0xd101000300008003, 2), (0xd101000180010081, 2), (0xd101000181008001, 2), (0xf101000100000007, 2), (0xd101000180008101, 2), (0xd101008180000081, 2), (0xd1010001c0008001, 2), (0xd181000100008081, 2), (0xd301000180000003, 2), (0xd109000100008009, 2), (0xd10100010000800d, 2), (0xd101000100008181, 2), (0xd1010001800000c1, 2), (0xd3010001000000c1, 2), (0xd1010001c0000003, 2), (0xd101000181000009, 2), (0xd901000100008009, 2), (0xd10100010000008d, 2), (0xd181000100000083, 2), (0xd10300010000000b, 2), (0xd101000190000009, 2), (0xd10100010000000f, 2), (0xd101800180010001, 2), (0xd101000300000083, 2), (0xd101000900008009, 2), (0xd101000100008109, 2), (0xd90100010000000b, 2), (0xd103000100008003, 2), (0xd901000100000091, 2), (0xd10100010000c009, 2), (0xd101000190008001, 2), (0xd181000100008101, 2), (0xd10100090000000b, 2), (0xd1010001000000c9, 2), (0xd10100018000c001, 2), (0xf101000180000003, 2), (0xd1010001c0000081, 2), (0xd101000180009001, 2), (0xd101000190000003, 2), (0xd101008101000081, 2), (0xd101000181000003, 2), (0xd109000100000089, 2), (0xd101000180010009, 2), (0xd901000100000089, 2), (0xd101000340000003, 2), (0xd101000180018001, 2), (0xd101000100000001, 0)]
  | 4 => [(0xd181009100000081, 1), (0xd10500050000000d, 1), (0xd10100d100000081, 1), (0xd10d00010000000d, 1), (0xd90100050000000d, 1), (0xd1010051000000c1, 1), (0xd105000d00000009, 1), (0xd101000d0000000d, 1), (0xd181001100000091, 1), (0xd50100050000000d, 1), (0xd90d000100000009, 1), (0xd90500010000000d, 1), (0xd109000d00000009, 1), (0xd10500090000000d, 1), (0xd901000d00000009, 1), (0xd1010091000000c1, 1), (0xd50500010000000d, 1), (0xd501000d00000009, 1), (0xd111009100000081, 1), (0xd10d000900000009, 1), (0xd10900050000000d, 1), (0xd101009100000091, 1), (0xd1010011000000d1, 1), (0xd50d000100000009, 1), (0xd111001100000091, 1), (0xd101000d00000089, 2), (0xd101009100000083, 2), (0xd10100050000800d, 2), (0xd101001108000091, 2), (0xd10500018000000d, 2), (0xf10500010000000d, 2), (0xd10100050000008d, 2), (0xd101000d80000009, 2), (0xd101009101000081, 2), (0xd10d000100002009, 2), (0xd101001100008091, 2), (0xd101000d90000001, 2), (0xf105000100000007, 2), (0xd901001100000019, 2), (0xd101001100000093, 2), (0xd10d000180000009, 2), (0xd10500010000800d, 2), (0xd101009180000081, 2), (0xd101000d10000009, 2), (0xd10100050000000f, 2), (0xd10d000100001009, 2), (0xd10100052000000d, 2), (0xd101000d0000000b, 2), (0xd10d000100009001, 2), (0xd101009100000089, 2), (0xd901001100000091, 2), (0xd10d000100008009, 2), (0xd101009100008081, 2), (0xd10500010000200d, 2), (0xd10500010000008d, 2), (0xd101000d00008009, 2), (0xd10d00010000000b, 2), (0xd10500010000000f, 2), (0xd10100058000000d, 2), (0xf10100050000000d, 2), (0xd101009108000081, 2), (0xd101009181000001, 2), (0xd101001100000099, 2), (0xd101000d20000009, 2), (0xd101001180000091, 2), (0xd10d000100000089, 2), (0xf101000500000007, 2)]
  | 5 => [(0xd10d00050000000d, 1), (0xd50500050000000d, 1), (0xd90500050000000d, 1), (0xd10d000d00000009, 1), (0xd105000d0000000d, 1), (0xd505000d00000009, 1), (0xd905000d00000009, 1), (0xd105000d00000089, 2), (0xd105000d00002009, 2), (0xd10500052000000d, 2), (0xd10500058000000d, 2), (0xf10500050000000d, 2), (0xd105000d0000000b, 2), (0xd10500050000800d, 2), (0xd105000d20000009, 2), (0xd10500050000200d, 2), (0xd10500050000008d, 2), (0xd105000d80000009, 2), (0xd10500050000000f, 2), (0xd105000d10000009, 2), (0xd105000d90000001, 2), (0xd105000d00008009, 2), (0xf105000500000007, 2)]
  | _ => []

def covered (k : Nat) (p : Nat × Nat) : Bool :=
  decide (goalCnt p.1 + (6 - k) < 3) || (cert k).any (fun q => subState p q)

lemma covered_init : covered 0 (initSet, 0) = true := by decide +kernel

lemma start_state : ∃ s0 : Nat,
    covered 0 (s0, 0) = true ∧
    s0.testBit 0 = true ∧
    s0.testBit 63 = true ∧
    ∀ w, s0.testBit (pack6 (fun t => (inp t).getD w false)).val = true :=
  ⟨initSet, covered_init, init_bit0, init_bit63, inp_mem⟩

lemma sub_testBit {s1 s2 : Nat} (h : (s1 &&& s2) = s1) {m : Nat} (hm : s1.testBit m = true) :
    s2.testBit m = true := by
  have h1 : (s1 &&& s2).testBit m = true := by rw [h]; exact hm
  rw [Nat.testBit_and, Bool.and_eq_true] at h1
  exact h1.2

lemma sub_trans {a b c : Nat} (h1 : (a &&& b) = a) (h2 : (b &&& c) = b) : (a &&& c) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 := congrArg (fun x => x.testBit i) h1
  have e2 := congrArg (fun x => x.testBit i) h2
  simp only [Nat.testBit_and] at e1 e2 ⊢
  revert e1 e2
  generalize a.testBit i = ba
  generalize b.testBit i = bb
  generalize c.testBit i = bc
  cases ba <;> cases bb <;> cases bc <;> decide

lemma sub_or_bit {s1 s2 v : Nat} (h : (s1 &&& s2) = s1) :
    ((s1 ||| (1 <<< v)) &&& (s2 ||| (1 <<< v))) = (s1 ||| (1 <<< v)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at e1 ⊢
  revert e1
  generalize s1.testBit i = b1
  generalize s2.testBit i = b2
  generalize (1 <<< v).testBit i = bv
  cases b1 <;> cases b2 <;> cases bv <;> decide

lemma goalCnt_mono {s1 s2 : Nat} (h : (s1 &&& s2) = s1) : goalCnt s1 ≤ goalCnt s2 := by
  unfold goalCnt
  have b1 : (if s1.testBit 34 then 1 else 0) ≤ (if s2.testBit 34 then 1 else 0) := by
    cases hs : s1.testBit 34
    · simp
    · simp [sub_testBit h hs]
  have b2 : (if s1.testBit 36 then 1 else 0) ≤ (if s2.testBit 36 then 1 else 0) := by
    cases hs : s1.testBit 36
    · simp
    · simp [sub_testBit h hs]
  have b3 : (if s1.testBit 50 then 1 else 0) ≤ (if s2.testBit 50 then 1 else 0) := by
    cases hs : s1.testBit 50
    · simp
    · simp [sub_testBit h hs]
  omega

lemma goalCnt_step_aux : ∀ (b1 b2 b3 : Bool) (u : Fin 64),
    (if (b1 || (1 <<< u.val).testBit 34) then 1 else 0) +
    (if (b2 || (1 <<< u.val).testBit 36) then 1 else 0) +
    (if (b3 || (1 <<< u.val).testBit 50) then 1 else 0) ≤
    (if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0) + 1 := by
  decide +kernel

lemma goalCnt_step (s : Nat) (v : Fin 64) : goalCnt (s ||| (1 <<< v.val)) ≤ goalCnt s + 1 := by
  simpa only [goalCnt, Nat.testBit_or] using goalCnt_step_aux (s.testBit 34) (s.testBit 36) (s.testBit 50) v

lemma subState_trans {p q r : Nat × Nat} (h1 : subState p q = true) (h2 : subState q r = true) :
    subState p r = true := by
  unfold subState at h1 h2 ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2 ⊢
  exact ⟨sub_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

lemma covered_mono {k : Nat} {p q : Nat × Nat} (hsub : subState p q = true) (hc : covered k q = true) :
    covered k p = true := by
  unfold covered at hc ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc ⊢
  have hs : (p.1 &&& q.1) = p.1 := by
    unfold subState at hsub
    simp only [Bool.and_eq_true, beq_iff_eq] at hsub
    exact hsub.1
  rcases hc with hlt | ⟨r, hr, hqr⟩
  · have hm := goalCnt_mono hs
    exact Or.inl (by omega)
  · exact Or.inr ⟨r, hr, subState_trans hsub hqr⟩

lemma shift_bit_lt64 : ∀ (v u : Fin 64),
    ((1 : Nat) <<< v.val).testBit u.val = decide (u.val = v.val) := by
  decide +kernel

lemma shift_lt_pow64 : ∀ (v : Fin 64), ((1 : Nat) <<< v.val) < 2 ^ 64 := by
  decide +kernel

lemma or_self_bit {s : Nat} (v : Fin 64) (hv : s.testBit v.val = true) :
    s ||| (1 <<< v.val) = s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 64
  · have hb : ((1 : Nat) <<< v.val).testBit i = decide (i = v.val) :=
      shift_bit_lt64 v ⟨i, hi⟩
    rw [hb]
    by_cases heq : i = v.val
    · subst heq
      simp [hv]
    · simp [heq]
  · have hp : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (shift_lt_pow64 v) hp), Bool.or_false]

lemma fin64_and_comm : ∀ (a b : Fin 64), a.val &&& b.val = b.val &&& a.val := by
  decide +kernel

lemma fin64_or_comm : ∀ (a b : Fin 64), a.val ||| b.val = b.val ||| a.val := by
  decide +kernel

def bits64 (s : Nat) : List (Fin 64) :=
  (List.finRange 64).filter (fun a => s.testBit a.val)

lemma mem_bits64 {s : Nat} {a : Fin 64} (h : s.testBit a.val = true) : a ∈ bits64 s := by
  unfold bits64
  exact List.mem_filter.mpr ⟨List.mem_finRange a, h⟩

def stepOk (k : Nat) (q : Nat × Nat) : Bool :=
  let bs := bits64 q.1
  covered (k + 1) q &&
  bs.all (fun a =>
    bs.all (fun b =>
      if decide (b.val ≤ a.val) then
        (if q.1.testBit (a.val &&& b.val) then true
         else covered (k + 1) (q.1 ||| (1 <<< (a.val &&& b.val)), q.2)) &&
        (if q.1.testBit (a.val ||| b.val) then true
         else covered (k + 1) (q.1 ||| (1 <<< (a.val ||| b.val)), q.2))
      else true)) &&
  (if decide (q.2 < 2) then
    bs.all (fun a =>
      covered (k + 1) (q.1 ||| (1 <<< (63 ^^^ a.val)), q.2 + 1))
   else true)

set_option maxHeartbeats 2000000 in
lemma cert_step_raw : ∀ (k : Fin 6), (cert k.val).all (fun q => stepOk k.val q) = true := by
  decide +kernel

lemma cert_step_le (k : Fin 6) (q : Nat × Nat) (hq : q ∈ cert k.val)
    (a b : Fin 64) (ha : q.1.testBit a.val = true) (hb : q.1.testBit b.val = true)
    (hle : b.val ≤ a.val) :
    covered (k.val + 1) (q.1 ||| (1 <<< (a.val &&& b.val)), q.2) = true ∧
    covered (k.val + 1) (q.1 ||| (1 <<< (a.val ||| b.val)), q.2) = true := by
  have hok : stepOk k.val q = true := List.all_eq_true.mp (cert_step_raw k) q hq
  dsimp only [stepOk] at hok
  simp only [Bool.and_eq_true] at hok
  have hcov_q : covered (k.val + 1) q = true := hok.1.1
  have h1 := List.all_eq_true.mp hok.1.2 a (mem_bits64 ha)
  have h2 := List.all_eq_true.mp h1 b (mem_bits64 hb)
  simp only [hle, decide_true, ite_true, Bool.and_eq_true] at h2
  refine ⟨?_, ?_⟩
  · cases ht : q.1.testBit (a.val &&& b.val)
    · simpa [ht] using h2.1
    · rw [or_self_bit ⟨a.val &&& b.val, and_lt64 a b⟩ ht]
      rcases q with ⟨qs, qc⟩
      exact hcov_q
  · cases ht : q.1.testBit (a.val ||| b.val)
    · simpa [ht] using h2.2
    · rw [or_self_bit ⟨a.val ||| b.val, or_lt64 a b⟩ ht]
      rcases q with ⟨qs, qc⟩
      exact hcov_q

lemma cert_step (k : Fin 6) (q : Nat × Nat) (hq : q ∈ cert k.val) :
    (∀ (a b : Fin 64), q.1.testBit a.val = true → q.1.testBit b.val = true →
      covered (k.val + 1) (q.1 ||| (1 <<< (a.val &&& b.val)), q.2) = true ∧
      covered (k.val + 1) (q.1 ||| (1 <<< (a.val ||| b.val)), q.2) = true) ∧
    (q.2 < 2 → ∀ (a : Fin 64), q.1.testBit a.val = true →
      covered (k.val + 1) (q.1 ||| (1 <<< (63 ^^^ a.val)), q.2 + 1) = true) := by
  refine ⟨?_, ?_⟩
  · intro a b ha hb
    by_cases hle : b.val ≤ a.val
    · exact cert_step_le k q hq a b ha hb hle
    · have hle' : a.val ≤ b.val := by omega
      have hswap := cert_step_le k q hq b a hb ha hle'
      rw [fin64_and_comm a b, fin64_or_comm a b]
      exact hswap
  · intro hq2 a ha
    have hok : stepOk k.val q = true := List.all_eq_true.mp (cert_step_raw k) q hq
    dsimp only [stepOk] at hok
    simp only [Bool.and_eq_true] at hok
    have hnot := hok.2
    simp only [hq2, decide_true, ite_true] at hnot
    exact List.all_eq_true.mp hnot a (mem_bits64 ha)

lemma cert_no_hit : ∀ (k : Fin 7) (q : Nat × Nat), q ∈ cert k.val → goalCnt q.1 < 3 := by
  decide +kernel

lemma covered_no_hit {k s c : Nat} (hk : k ≤ 6) (hc : covered k (s, c) = true) :
    goalCnt s < 3 := by
  unfold covered at hc
  dsimp only at hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  rcases hc with hlt | ⟨q, hq, hsub⟩
  · omega
  · unfold subState at hsub
    dsimp only at hsub
    simp only [Bool.and_eq_true, beq_iff_eq] at hsub
    have hm := goalCnt_mono hsub.1
    have hn := cert_no_hit ⟨k, by omega⟩ q hq
    omega

lemma covered_and {k s c : Nat} (hk : k < 6) (hc : covered k (s, c) = true)
    {a b : Fin 64} (ha : s.testBit a.val = true) (hb : s.testBit b.val = true) :
    covered (k + 1) (s ||| (1 <<< (a.val &&& b.val)), c) = true := by
  unfold covered at hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  rcases hc with hlt | ⟨q, hq, hsub⟩
  · have hst := goalCnt_step s ⟨a.val &&& b.val, and_lt64 a b⟩
    dsimp only at hst
    unfold covered
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (by omega)
  · unfold subState at hsub
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsub
    have hqa := sub_testBit hsub.1 ha
    have hqb := sub_testBit hsub.1 hb
    have hcs := ((cert_step ⟨k, hk⟩ q hq).1 a b hqa hqb).1
    refine covered_mono ?_ hcs
    unfold subState
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨sub_or_bit hsub.1, hsub.2⟩

lemma covered_or {k s c : Nat} (hk : k < 6) (hc : covered k (s, c) = true)
    {a b : Fin 64} (ha : s.testBit a.val = true) (hb : s.testBit b.val = true) :
    covered (k + 1) (s ||| (1 <<< (a.val ||| b.val)), c) = true := by
  unfold covered at hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  rcases hc with hlt | ⟨q, hq, hsub⟩
  · have hst := goalCnt_step s ⟨a.val ||| b.val, or_lt64 a b⟩
    dsimp only at hst
    unfold covered
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (by omega)
  · unfold subState at hsub
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsub
    have hqa := sub_testBit hsub.1 ha
    have hqb := sub_testBit hsub.1 hb
    have hcs := ((cert_step ⟨k, hk⟩ q hq).1 a b hqa hqb).2
    refine covered_mono ?_ hcs
    unfold subState
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨sub_or_bit hsub.1, hsub.2⟩

lemma covered_not {k s c : Nat} (hk : k < 6) (hc2 : c < 2) (hc : covered k (s, c) = true)
    {a : Fin 64} (ha : s.testBit a.val = true) :
    covered (k + 1) (s ||| (1 <<< (63 ^^^ a.val)), c + 1) = true := by
  unfold covered at hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  rcases hc with hlt | ⟨q, hq, hsub⟩
  · have hst := goalCnt_step s ⟨63 ^^^ a.val, not_lt64 a⟩
    dsimp only at hst
    unfold covered
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (by omega)
  · unfold subState at hsub
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsub
    have hqa := sub_testBit hsub.1 ha
    have hcs := (cert_step ⟨k, hk⟩ q hq).2 (by omega) a hqa
    refine covered_mono ?_ hcs
    unfold subState
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨sub_or_bit hsub.1, by omega⟩

lemma self_bit_shift (v : Fin 64) : ((1 : Nat) <<< v.val).testBit v.val = true := by
  revert v
  decide +kernel

lemma gate_step {k s c len : Nat} {ws : Fin 6 → List Bool} (g : Gate)
    (hk : k < 6)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hin : g.inputs.length ≤ 2)
    (hc2 : (if isNotOp g.op then 1 else 0) + c ≤ 2)
    (hcov : covered k (s, c) = true)
    (hs0 : s.testBit 0 = true)
    (hs63 : s.testBit 63 = true)
    (hlen : ∀ t, (ws t).length = len)
    (hw : ∀ w, s.testBit (pack6 (fun t => (ws t).getD w false)).val = true) :
    ∃ s' : Nat,
      let c' := c + (if isNotOp g.op then 1 else 0)
      let ws' := fun t : Fin 6 => ws t ++ [g.op.eval (g.inputs.map fun i => (ws t).getD i false)]
      covered (k + 1) (s', c') = true ∧
      s'.testBit 0 = true ∧
      s'.testBit 63 = true ∧
      (∀ t, (ws' t).length = len + 1) ∧
      (∀ w, s'.testBit (pack6 (fun t => (ws' t).getD w false)).val = true) := by
  let outFn : Fin 6 → Bool := fun t => g.op.eval (g.inputs.map fun i => (ws t).getD i false)
  let v : Fin 64 := pack6 outFn
  refine ⟨s ||| (1 <<< v.val), ?_, ?_, ?_, ?_, ?_⟩
  · have hops : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa using hop
    rcases hops with h_op | h_op | h_op
    · have hno : isNotOp g.op = false := by rw [h_op]; rfl
      simp only [hno, Bool.false_eq_true, ite_false, Nat.add_zero]
      match h_in : g.inputs with
      | [] =>
        have hv : v.val = (63 : Fin 64).val &&& (63 : Fin 64).val := by
          have ho : outFn = fun _ => true := by funext t; simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = 63 &&& 63
          rw [ho, pack6_true]
          decide +kernel
        rw [hv]
        exact covered_and hk hcov hs63 hs63
      | [i] =>
        let ai := pack6 (fun t => (ws t).getD i false)
        have hv : v.val = ai.val &&& ai.val := by
          have ho : outFn = fun t => (ws t).getD i false && (ws t).getD i false := by
            funext t
            simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = ai.val &&& ai.val
          rw [ho, pack6_and]
        rw [hv]
        exact covered_and hk hcov (hw i) (hw i)
      | [i, j] =>
        let ai := pack6 (fun t => (ws t).getD i false)
        let aj := pack6 (fun t => (ws t).getD j false)
        have hv : v.val = ai.val &&& aj.val := by
          have ho : outFn = fun t => (ws t).getD i false && (ws t).getD j false := by
            funext t
            simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = ai.val &&& aj.val
          rw [ho, pack6_and]
        rw [hv]
        exact covered_and hk hcov (hw i) (hw j)
      | _ :: _ :: _ :: _ =>
        rw [h_in] at hin
        simp at hin
    · have hno : isNotOp g.op = false := by rw [h_op]; rfl
      simp only [hno, Bool.false_eq_true, ite_false, Nat.add_zero]
      match h_in : g.inputs with
      | [] =>
        have hv : v.val = (0 : Fin 64).val ||| (0 : Fin 64).val := by
          have ho : outFn = fun _ => false := by funext t; simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = 0 ||| 0
          rw [ho, pack6_false]
          decide +kernel
        rw [hv]
        exact covered_or hk hcov hs0 hs0
      | [i] =>
        let ai := pack6 (fun t => (ws t).getD i false)
        have hv : v.val = ai.val ||| ai.val := by
          have ho : outFn = fun t => (ws t).getD i false || (ws t).getD i false := by
            funext t
            simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = ai.val ||| ai.val
          rw [ho, pack6_or]
        rw [hv]
        exact covered_or hk hcov (hw i) (hw i)
      | [i, j] =>
        let ai := pack6 (fun t => (ws t).getD i false)
        let aj := pack6 (fun t => (ws t).getD j false)
        have hv : v.val = ai.val ||| aj.val := by
          have ho : outFn = fun t => (ws t).getD i false || (ws t).getD j false := by
            funext t
            simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = ai.val ||| aj.val
          rw [ho, pack6_or]
        rw [hv]
        exact covered_or hk hcov (hw i) (hw j)
      | _ :: _ :: _ :: _ =>
        rw [h_in] at hin
        simp at hin
    · have hyes : isNotOp g.op = true := by rw [h_op]; rfl
      simp only [hyes, ite_true] at hc2 ⊢
      match h_in : g.inputs with
      | [] =>
        have hv : v.val = 63 ^^^ (0 : Fin 64).val := by
          have ho : outFn = fun _ => !(false) := by funext t; simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = 63 ^^^ 0
          rw [ho, pack6_not, pack6_false]
        rw [hv]
        exact covered_not hk (by omega) hcov hs0
      | i :: rest =>
        let ai := pack6 (fun t => (ws t).getD i false)
        have hv : v.val = 63 ^^^ ai.val := by
          have ho : outFn = fun t => !((ws t).getD i false) := by
            funext t
            simp [outFn, h_op, h_in, GateOp.eval]
          change (pack6 outFn).val = 63 ^^^ ai.val
          rw [ho, pack6_not]
        rw [hv]
        exact covered_not hk (by omega) hcov (hw i)
  · rw [Nat.testBit_or, hs0, Bool.true_or]
  · rw [Nat.testBit_or, hs63, Bool.true_or]
  · intro t
    simp [hlen t]
  · intro w
    by_cases hlt : w < len
    · have heq : (fun t : Fin 6 => (ws t ++ [outFn t]).getD w false) = (fun t => (ws t).getD w false) := by
        funext t
        exact List.getD_append _ _ _ _ (by rw [hlen t]; exact hlt)
      change (s ||| (1 <<< v.val)).testBit (pack6 (fun t => (ws t ++ [outFn t]).getD w false)).val = true
      rw [heq, Nat.testBit_or, hw w, Bool.true_or]
    · by_cases heq_len : w = len
      · rw [heq_len]
        have heq : (fun t : Fin 6 => (ws t ++ [outFn t]).getD len false) = outFn := by
          funext t
          rw [List.getD_append_right _ _ _ _ (by rw [hlen t]), hlen t, Nat.sub_self]
          rfl
        change (s ||| (1 <<< v.val)).testBit (pack6 (fun t => (ws t ++ [outFn t]).getD len false)).val = true
        rw [heq, Nat.testBit_or, self_bit_shift v, Bool.or_true]
      · have hgt : (fun t : Fin 6 => (ws t ++ [outFn t]).getD w false) = (fun _ => false) := by
          funext t
          exact List.getD_eq_default _ _ (by simp [hlen t]; omega)
        change (s ||| (1 <<< v.val)).testBit (pack6 (fun t => (ws t ++ [outFn t]).getD w false)).val = true
        rw [hgt, pack6_false, Nat.testBit_or, hs0, Bool.true_or]

lemma fold_gates (gs : List Gate) :
    ∀ {k s c len : Nat} {ws : Fin 6 → List Bool},
      k + gs.length ≤ 6 →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      c + (gs.filter fun g => isNotOp g.op).length ≤ 2 →
      covered k (s, c) = true →
      s.testBit 0 = true →
      s.testBit 63 = true →
      (∀ t, (ws t).length = len) →
      (∀ w, s.testBit (pack6 (fun t => (ws t).getD w false)).val = true) →
      ∃ s_end c_end : Nat,
        covered (k + gs.length) (s_end, c_end) = true ∧
        ∀ w, s_end.testBit (pack6 (fun t =>
          (gs.foldl (fun w0 g => w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)]) (ws t)).getD w false)).val = true := by
  induction gs with
  | nil =>
    intro k s c len ws _ _ _ hcov _ _ _ hw
    exact ⟨s, c, by simpa using hcov, fun w => by simpa using hw w⟩
  | cons g gs ih =>
    intro k s c len ws hlen_gs hfan hnot hcov hs0 hs63 hlen hw
    simp only [List.length_cons] at hlen_gs
    have hg := hfan g (by simp)
    have hnot_cons : (if isNotOp g.op then 1 else 0) + (gs.filter fun x => isNotOp x.op).length =
        ((g :: gs).filter fun x => isNotOp x.op).length := by
      cases hn : isNotOp g.op <;> simp [hn, Nat.add_comm]
    obtain ⟨s1, hcov1, hs0_1, hs63_1, hlen1, hw1⟩ :=
      gate_step g (by omega) hg.1 hg.2 (by omega) hcov hs0 hs63 hlen hw
    obtain ⟨s_end, c_end, hcov_end, hw_end⟩ :=
      ih (k := k + 1) (s := s1) (c := c + (if isNotOp g.op then 1 else 0)) (len := len + 1)
        (ws := fun t => ws t ++ [g.op.eval (g.inputs.map fun i => (ws t).getD i false)])
        (by omega)
        (fun g1 hg1 => hfan g1 (List.mem_cons_of_mem _ hg1))
        (by omega)
        hcov1 hs0_1 hs63_1 hlen1 hw1
    refine ⟨s_end, c_end, ?_, ?_⟩
    · simp only [List.length_cons]
      have hk_eq : k + 1 + gs.length = k + (gs.length + 1) := by omega
      rwa [← hk_eq]
    · intro w
      simpa only [List.foldl_cons] using hw_end w

lemma s1 (D : Circuit) (hnot : notCount D ≤ 2) :
    0 + (D.gates.filter fun g => isNotOp g.op).length ≤ 2 := by
  rw [notCount_eq_filter] at hnot
  rw [Nat.zero_add]
  exact hnot

lemma s2 (D : Circuit) (hsize : D.size ≤ 6) : 0 + D.gates.length ≤ 6 := by
  rw [Nat.zero_add]
  exact hsize

lemma s3 (D : Circuit) (hfan : FanInTwo D) :
    ∀ g ∈ D.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
  fun g hg => hfan g hg

lemma inp_len (t : Fin 6) : (inp t).length = 7 := by
  simp [inp]

lemma wires_eq (D : Circuit) (x : List Bool) :
    D.gates.foldl (fun w0 g => w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)]) x = D.wires x :=
  rfl

lemma inp_eq (t : Fin 6) :
    inp t = (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] :=
  rfl

lemma s4 (D : Circuit)
    (hsize : D.size ≤ 6)
    (hfan : FanInTwo D)
    (hnot : notCount D ≤ 2) :
    ∃ s_end : Nat, goalCnt s_end < 3 ∧
      ∀ w, s_end.testBit (pack6 (fun t => (D.wires (inp t)).getD w false)).val = true := by
  have hsize0 := s2 D hsize
  rcases start_state with ⟨s0, hcov0, hs0, hs63, hinp0⟩
  rcases @fold_gates D.gates 0 s0 0 7 inp hsize0 (s3 D hfan) (s1 D hnot) hcov0 hs0 hs63 inp_len hinp0 with
    ⟨s_end, c_end, hcov_end, hw_end⟩
  simp only [wires_eq] at hw_end
  exact ⟨s_end, covered_no_hit hsize0 hcov_end, hw_end⟩

lemma wire_bit (D : Circuit) (s_end w : Nat) (k : Nat) (hk_lt : k < 64)
    (hw : ∀ u, s_end.testBit (pack6 (fun t => (D.wires (inp t)).getD u false)).val = true)
    (hk : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD w false =
      k.testBit t.val) :
    s_end.testBit k = true := by
  have heq : pack6 (fun t => (D.wires (inp t)).getD w false) = ⟨k, hk_lt⟩ := by
    apply fin64_eq_of_bits
    intro t
    rw [pack6_bit, inp_eq t]
    exact hk t
  have hm := hw w
  rw [heq] at hm
  exact hm

lemma k34_lt : 34 < 64 := by decide
lemma k36_lt : 36 < 64 := by decide
lemma k50_lt : 50 < 64 := by decide

lemma goalCnt_contra {s : Nat} (h1 : s.testBit 34 = true) (h2 : s.testBit 36 = true)
    (h3 : s.testBit 50 = true) (hlt : goalCnt s < 3) : False := by
  unfold goalCnt at hlt
  rw [h1, h2, h3] at hlt
  exact absurd hlt (by decide)

set_option maxHeartbeats 800000 in
theorem main_proof : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (34 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) := by
  intro hex
  rcases hex with ⟨D, p, q, r, hfan, _, hnot, hsize, hout⟩
  obtain ⟨s_end, hlt3, hw⟩ := s4 D hsize hfan hnot
  exact goalCnt_contra
    (wire_bit D s_end p.val 34 k34_lt hw (fun t => (hout t).1))
    (wire_bit D s_end q.val 36 k36_lt hw (fun t => (hout t).2.1))
    (wire_bit D s_end r.val 50 k50_lt hw (fun t => (hout t).2.2))
    hlt3

end PEqualNP.Outside.L_meta_50199

theorem PEqualNP.Outside.L_meta_50199 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (34 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val)) :=
  PEqualNP.Outside.L_meta_50199.main_proof
