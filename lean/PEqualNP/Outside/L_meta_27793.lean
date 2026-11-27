import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27793

open PEqualNP.CircuitLowerBounds

def force {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | Nat.succ m => k (Nat.succ m)

theorem force_eq {α : Type} (n : ℕ) (k : ℕ → α) : force n k = k n := by
  cases n <;> rfl

def forceList {α : Type} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | x :: xs, k => force x fun x' => forceList xs fun xs' => k (x' :: xs')

theorem forceList_eq {α : Type} : ∀ (l : List ℕ) (k : List ℕ → α), forceList l k = k l := by
  intro l
  induction l with
  | nil => intro k; rfl
  | cons x xs ih => intro k; simp only [forceList, force_eq, ih]

def fullN (n : ℕ) : ℕ := 2 ^ n - 1

def full : ℕ := fullN 512

def lo (i : ℕ) : ℕ := full / (2 ^ 2 ^ i + 1)

def inp (i : ℕ) : ℕ := lo i * 2 ^ 2 ^ i

def tgt : ℕ :=
  (inp 0 &&& inp 4 &&& inp 8) ||| (inp 0 &&& inp 5 &&& inp 7) ||| (inp 1 &&& inp 3 &&& inp 8) |||
    (inp 1 &&& inp 5 &&& inp 6) ||| (inp 2 &&& inp 3 &&& inp 7) ||| (inp 2 &&& inp 4 &&& inp 6)

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
    (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def sens (f i : ℕ) : ℕ := ((f >>> 2 ^ i) ^^^ f) &&& lo i

abbrev St := ℕ × List ℕ × List ℕ × List ℕ

def wire (st : St) (a : ℕ) : ℕ := st.2.1.getD (st.1 - 1 - a) 0

def gateTT (g : Gate) (st : St) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => wire st a &&& wire st b
  | GateOp.or, [a, b] => wire st a ||| wire st b
  | GateOp.not, [a] => full ^^^ wire st a
  | _, _ => 0

def updUnc (ins : List ℕ) (tt : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | u :: us, i =>
    (if ins.contains i then u ^^^ (u &&& sens tt i) else u) :: updUnc ins tt us (i + 1)

def push (st : St) (g : Gate) (tt : ℕ) : St :=
  (st.1 + 1, tt :: st.2.1, st.2.2.1.filter (fun w => !g.inputs.contains w) ++ [st.1],
    updUnc g.inputs tt st.2.2.2 0)

def stepSt (st : St) (g : Gate) : St := push st g (gateTT g st)

def nzIdx : List ℕ → ℕ → List ℕ
  | [], _ => []
  | u :: us, i => if u != 0 then i :: nzIdx us (i + 1) else nzIdx us (i + 1)

def needList (st : St) : List ℕ := st.2.2.1 ++ nzIdx st.2.2.2 0

def cands (W : ℕ) : List Gate :=
  (List.range W).flatMap fun b =>
    ⟨GateOp.not, [b]⟩ ::
      (List.range b).flatMap fun a => [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [a, b]⟩]

def tryGate (tg r : ℕ) (st : St) (rec : St → Bool) (g : Gate) : Bool :=
  force (gateTT g st) fun tt =>
    ((tt ^^^ tg) &&& full != 0) &&
      forceList (st.2.2.1.filter (fun w => !g.inputs.contains w) ++ [st.1]) fun un =>
        forceList (updUnc g.inputs tt st.2.2.2 0) fun uc =>
          (decide (r + 1 < un.length + (nzIdx uc 0).length) ||
            rec (st.1 + 1, tt :: st.2.1, un, uc))

theorem tryGate_eq (tg r : ℕ) (st : St) (rec : St → Bool) (g : Gate) :
    tryGate tg r st rec g = (((gateTT g st ^^^ tg) &&& full != 0) &&
      (decide (r + 1 < (needList (stepSt st g)).length) || rec (stepSt st g))) := by
  unfold tryGate
  rw [force_eq]
  simp only [forceList_eq, needList, stepSt, push, List.length_append]

def candList (r : ℕ) (st : St) : List Gate :=
  forceList (needList st) fun A =>
    if r + 2 ≤ A.length then
      A.flatMap fun b => A.flatMap fun a =>
        if a < b then [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [a, b]⟩] else []
    else cands st.1

def search (tg : ℕ) : ℕ → St → Bool
  | 0, _ => true
  | r + 1, st => (candList r st).all (tryGate tg r st (search tg r))

def init : St :=
  (9, [inp 8, inp 7, inp 6, inp 5, inp 4, inp 3, inp 2, inp 1, inp 0], [],
    [sens tgt 0, sens tgt 1, sens tgt 2, sens tgt 3, sens tgt 4, sens tgt 5, sens tgt 6,
      sens tgt 7, sens tgt 8])

def run (n : ℕ) (gs : List Gate) : Bool :=
  force tgt fun tg =>
    forceList (gs.foldl stepSt init).2.1 fun rt =>
      forceList (gs.foldl stepSt init).2.2.1 fun un =>
        forceList (gs.foldl stepSt init).2.2.2 fun uc =>
          ((wire (gs.foldl stepSt init) ((gs.foldl stepSt init).1 - 1) ^^^ tg) &&& full != 0) &&
            search tg (n - gs.length) ((gs.foldl stepSt init).1, rt, un, uc)

theorem run_eq (n : ℕ) (gs : List Gate) :
    run n gs = (((wire (gs.foldl stepSt init) ((gs.foldl stepSt init).1 - 1) ^^^ tgt) &&& full != 0) &&
      search tgt (n - gs.length) (gs.foldl stepSt init)) := by
  simp only [run, force_eq, forceList_eq]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def pt (t : ℕ) : List Bool := (List.range 9).map t.testBit

def wiresAt (gs : List Gate) (t : ℕ) : List Bool := gs.foldl step (pt t)

def Shape (g : Gate) (W : ℕ) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < W ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < W ∧ g.inputs = [a, b])

def Valid (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (∀ j : Fin gs.length, Shape (gs.get j) (9 + j.val)) ∧
  (∀ j : Fin gs.length, j.val + 1 < gs.length →
    ∃ k : Fin gs.length, j.val < k.val ∧ 9 + j.val ∈ (gs.get k).inputs) ∧
  (∀ t < 512, (wiresAt gs t).getD (8 + gs.length) false = tgt.testBit t)

theorem step_set {i : ℕ} {b : Bool} {w : List Bool} {g : Gate} (hi : i < w.length)
    (hg : i ∉ g.inputs) : step (w.set i b) g = (step w g).set i b := by
  have hmap : (g.inputs.map fun k => (w.set i b).getD k false)
      = g.inputs.map fun k => w.getD k false := by
    apply List.map_congr_left
    intro k hk
    have hne : i ≠ k := fun h => hg (h ▸ hk)
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
  unfold step
  rw [hmap, List.set_append]
  simp only [hi, ite_true]

theorem foldl_set {i : ℕ} {b : Bool} : ∀ (gs : List Gate) (w : List Bool), i < w.length →
    (∀ g ∈ gs, i ∉ g.inputs) → gs.foldl step (w.set i b) = (gs.foldl step w).set i b := by
  intro gs
  induction gs with
  | nil => intro w _ _; rfl
  | cons g gs ih =>
    intro w hi hg
    rw [List.foldl_cons, List.foldl_cons, step_set hi (hg g (List.mem_cons_self ..))]
    exact ih (step w g) (by simp [step]; omega) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem reads_le : ∀ rest : List Gate, (∀ g ∈ rest, g.inputs.length ≤ 2) →
    (rest.flatMap fun g => g.inputs).length ≤ 2 * rest.length := by
  intro rest
  induction rest with
  | nil => intro _; simp
  | cons g gs ih =>
    intro h
    have h1 := h g (List.mem_cons_self ..)
    have h2 := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem length_le_of_nodup_subset {l m : List ℕ} (hn : l.Nodup) (hs : l ⊆ m) :
    l.length ≤ m.length :=
  (List.subperm_of_subset hn hs).length_le

theorem fullN_bit (n t : ℕ) : (fullN n).testBit t = decide (t < n) :=
  Nat.testBit_two_pow_sub_one n t

theorem full_bit (t : ℕ) : full.testBit t = decide (t < 512) := fullN_bit 512 t

theorem fullN_lt (n : ℕ) : fullN n < 2 ^ n :=
  Nat.sub_one_lt (Nat.two_pow_pos n).ne'

theorem inp_bit : ∀ i < 9, ∀ t < 512, (inp i).testBit t = t.testBit i := by
  decide +kernel

theorem tgt_bit : ∀ t < 512, tgt.testBit t = target (fun j => t.testBit j.val) := by
  decide +kernel

theorem lo_le (i : ℕ) : lo i ≤ full := Nat.div_le_self _ _

theorem lo_bit : ∀ i < 9, ∀ t < 512, (lo i).testBit t = true →
    (2 ^ i + t < 512 ∧ ∀ j < 9, (2 ^ i + t).testBit j = (if j = i then true else t.testBit j)) := by
  decide +kernel

theorem lo_spec {i t : ℕ} (hi : i < 9) (h : (lo i).testBit t = true) :
    t < 512 ∧ 2 ^ i + t < 512 ∧
      ∀ j < 9, (2 ^ i + t).testBit j = (if j = i then true else t.testBit j) := by
  have ht : t < 512 := by
    by_contra hge
    have h512 : 512 ≤ t := by omega
    have h1 : lo i < 2 ^ t :=
      lt_of_lt_of_le (lt_of_le_of_lt (lo_le i) (fullN_lt 512)) (Nat.pow_le_pow_right (by decide) h512)
    rw [Nat.testBit_lt_two_pow h1] at h
    exact Bool.false_ne_true h
  exact ⟨ht, lo_bit i hi t ht h⟩

theorem sens_bit (f i t : ℕ) :
    (sens f i).testBit t = ((f.testBit (2 ^ i + t) ^^ f.testBit t) && (lo i).testBit t) := by
  simp [sens, Nat.testBit_shiftRight]

theorem wire_init : ∀ a < 9, wire init a = inp a := by
  decide +kernel

theorem ofFn_pt (t : ℕ) : List.ofFn (fun j : Fin 9 => t.testBit j.val) = pt t := by
  rfl

theorem shape_lt {g : Gate} {W : ℕ} (hs : Shape g W) : ∀ w ∈ g.inputs, w < W := by
  rcases hs with ⟨-, a, ha, hin⟩ | ⟨-, a, b, hab, hb, hin⟩
  · intro w hw
    rw [hin] at hw
    simp at hw
    omega
  · intro w hw
    rw [hin] at hw
    simp at hw
    omega

theorem gateTT_bit {st : St} {g : Gate} (hs : Shape g st.1) {t : ℕ} (ht : t < 512) :
    (gateTT g st).testBit t = g.op.eval (g.inputs.map fun a => (wire st a).testBit t) := by
  obtain ⟨op, ins⟩ := g
  rcases hs with ⟨hop, a, -, hin⟩ | ⟨hop | hop, a, b, -, -, hin⟩ <;>
    simp only at hop hin <;> subst hop hin
  · simp [gateTT, GateOp.eval, full_bit, ht]
  · simp [gateTT, GateOp.eval]
  · simp [gateTT, GateOp.eval]

theorem wire_push_lt (st : St) (g : Gate) (tt : ℕ) {a : ℕ} (ha : a < st.1) :
    wire (push st g tt) a = wire st a := by
  have h : st.1 + 1 - 1 - a = (st.1 - 1 - a) + 1 := by omega
  simp only [wire, push, h, List.getD_cons_succ]

theorem wire_push_last (st : St) (g : Gate) (tt : ℕ) : wire (push st g tt) st.1 = tt := by
  simp [wire, push]

theorem updUnc_getD (ins : List ℕ) (tt : ℕ) : ∀ (us : List ℕ) (k j : ℕ),
    (updUnc ins tt us k).getD j 0 =
      if ins.contains (k + j) then us.getD j 0 ^^^ (us.getD j 0 &&& sens tt (k + j))
      else us.getD j 0 := by
  intro us
  induction us with
  | nil => intro k j; simp [updUnc]
  | cons u us ih =>
    intro k j
    cases j with
    | zero => simp [updUnc]
    | succ j =>
      have h : k + 1 + j = k + (j + 1) := by omega
      simp only [updUnc, List.getD_cons_succ, ih (k + 1) j, h]

theorem updUnc_length (ins : List ℕ) (tt : ℕ) : ∀ (us : List ℕ) (k : ℕ),
    (updUnc ins tt us k).length = us.length := by
  intro us
  induction us with
  | nil => intro k; rfl
  | cons u us ih => intro k; simp [updUnc, ih]

theorem mem_nzIdx : ∀ (us : List ℕ) (k i : ℕ),
    i ∈ nzIdx us k ↔ ∃ j, i = k + j ∧ j < us.length ∧ us.getD j 0 ≠ 0 := by
  intro us
  induction us with
  | nil => intro k i; simp [nzIdx]
  | cons u us ih =>
    intro k i
    constructor
    · intro h
      have hcase : (u ≠ 0 ∧ i = k) ∨ i ∈ nzIdx us (k + 1) := by
        simp only [nzIdx] at h
        split at h
        · rename_i hu
          rcases List.mem_cons.mp h with h | h
          · exact Or.inl ⟨by simpa using hu, h⟩
          · exact Or.inr h
        · exact Or.inr h
      rcases hcase with ⟨hu, rfl⟩ | h
      · exact ⟨0, rfl, by simp, by simpa using hu⟩
      · obtain ⟨j, rfl, hj, hne⟩ := (ih (k + 1) i).mp h
        exact ⟨j + 1, by omega, by simpa using hj, by simpa using hne⟩
    · rintro ⟨j, rfl, hj, hne⟩
      cases j with
      | zero =>
        have hu : (u != 0) = true := by simpa using hne
        simp [nzIdx, hu]
      | succ j =>
        have hmem : k + (j + 1) ∈ nzIdx us (k + 1) :=
          (ih (k + 1) (k + (j + 1))).mpr ⟨j, by omega, by simpa using hj, by simpa using hne⟩
        simp only [nzIdx]
        split
        · exact List.mem_cons_of_mem _ hmem
        · exact hmem

theorem nzIdx_sublist : ∀ (us : List ℕ) (k : ℕ),
    (nzIdx us k).Sublist (List.range' k us.length) := by
  intro us
  induction us with
  | nil => intro k; simp [nzIdx]
  | cons u us ih =>
    intro k
    simp only [nzIdx, List.length_cons, List.range'_succ]
    split
    · exact (ih (k + 1)).cons_cons k
    · exact (ih (k + 1)).cons k

theorem nzIdx_nodup (us : List ℕ) (k : ℕ) : (nzIdx us k).Nodup :=
  List.Nodup.sublist (nzIdx_sublist us k) (List.nodup_range' ..)

def Inv (pre : List Gate) (st : St) : Prop :=
  st.1 = 9 + pre.length ∧
  (∀ a < 9, wire st a = inp a) ∧
  (∀ t < 512, (wiresAt pre t).length = st.1 ∧
    ∀ a < st.1, (wiresAt pre t).getD a false = (wire st a).testBit t) ∧
  (st.2.2.1.Nodup ∧ ∀ w ∈ st.2.2.1, 9 ≤ w ∧ w < st.1 ∧ ∀ g ∈ pre, w ∉ g.inputs) ∧
  (st.2.2.2.length = 9 ∧ ∀ i < 9, ∀ t, (st.2.2.2.getD i 0).testBit t = true →
    (lo i).testBit t = true ∧ tgt.testBit t ≠ tgt.testBit (2 ^ i + t) ∧
      ∀ k, 9 ≤ k → k < st.1 → (wire st k).testBit t = (wire st k).testBit (2 ^ i + t)) ∧
  (∀ g ∈ pre, ∀ w ∈ g.inputs, w < st.1)

theorem pt_getD {t a : ℕ} (ha : a < 9) : (pt t).getD a false = t.testBit a := by
  simp [pt, List.getD_eq_getElem?_getD, ha]

theorem xor_and_true {a b c : Bool} (h : ((a ^^ b) && c) = true) : c = true ∧ b ≠ a := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem xor_and_false {a b : Bool} (h : ((a ^^ b) && true) = false) : b = a := by
  cases a <;> cases b <;> simp_all

theorem xor_and_self {u s : Bool} (h : (u ^^ (u && s)) = true) : u = true ∧ s = false := by
  cases u <;> cases s <;> simp_all

theorem inv_init : Inv [] init := by
  refine ⟨rfl, wire_init, ?_, ⟨List.nodup_nil, by simp [init]⟩, ⟨rfl, ?_⟩, by simp⟩
  · intro t ht
    refine ⟨by simp [wiresAt, pt, init], ?_⟩
    intro a ha
    have ha9 : a < 9 := ha
    rw [wire_init a ha9, inp_bit a ha9 t ht]
    exact pt_getD ha9
  · intro i hi t h
    have hu : init.2.2.2.getD i 0 = sens tgt i := by
      interval_cases i <;> rfl
    rw [hu, sens_bit] at h
    obtain ⟨h1, h2⟩ := xor_and_true h
    refine ⟨h1, h2, ?_⟩
    intro k hk9 hk
    have : k < 9 := hk
    omega

theorem inv_step {pre : List Gate} {st : St} {g : Gate} (hinv : Inv pre st) (hs : Shape g st.1) :
    Inv (pre ++ [g]) (stepSt st g) := by
  obtain ⟨hW, hinp, hsem, ⟨hnd, hun⟩, ⟨hul, hunc⟩, hbd⟩ := hinv
  have hlt := shape_lt hs
  have h9 : 9 ≤ st.1 := by omega
  have hW1 : (stepSt st g).1 = st.1 + 1 := rfl
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hW1, hW, List.length_append, List.length_singleton]
    omega
  · intro a ha
    rw [stepSt, wire_push_lt st g _ (by omega)]
    exact hinp a ha
  · intro t ht
    obtain ⟨hlen, hval⟩ := hsem t ht
    have hw : wiresAt (pre ++ [g]) t = wiresAt pre t ++ [(gateTT g st).testBit t] := by
      have hmap : (g.inputs.map fun i => (wiresAt pre t).getD i false)
          = g.inputs.map fun a => (wire st a).testBit t :=
        List.map_congr_left fun a ha => hval a (hlt a ha)
      rw [gateTT_bit hs ht, ← hmap]
      simp only [wiresAt, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
    refine ⟨by rw [hw, hW1, List.length_append, List.length_singleton, hlen], ?_⟩
    intro a ha
    rw [hW1] at ha
    rw [hw]
    by_cases hlt' : a < st.1
    · rw [stepSt, wire_push_lt st g _ hlt', List.getD_append _ _ _ _ (by omega)]
      exact hval a hlt'
    · have hEq : a = st.1 := by omega
      subst hEq
      rw [stepSt, wire_push_last]
      simp [List.getD_eq_getElem?_getD, hlen]
  · simp only [stepSt, push]
    rw [List.nodup_append]
    refine ⟨hnd.filter _, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    have hx' := (hun x (List.mem_filter.mp hx).1).2.1
    have hy' : y = st.1 := by simpa using hy
    omega
  · intro w hw
    simp only [stepSt, push, List.mem_append, List.mem_filter, List.mem_singleton] at hw
    rcases hw with ⟨hw, hc⟩ | rfl
    · obtain ⟨h1, h2, h3⟩ := hun w hw
      refine ⟨h1, by rw [hW1]; omega, ?_⟩
      intro g' hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact h3 g' hg'
      · have hEq : g' = g := by simpa using hg'
        subst hEq
        simpa using hc
    · refine ⟨h9, by rw [hW1]; omega, ?_⟩
      intro g' hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · intro hmem
        exact absurd (hbd g' hg' _ hmem) (lt_irrefl _)
      · have hEq : g' = g := by simpa using hg'
        subst hEq
        intro hmem
        exact absurd (hlt _ hmem) (lt_irrefl _)
  · simp [stepSt, push, updUnc_length, hul]
  · intro i hi t h
    have hget : (stepSt st g).2.2.2.getD i 0 =
        if g.inputs.contains i then
          st.2.2.2.getD i 0 ^^^ (st.2.2.2.getD i 0 &&& sens (gateTT g st) i)
        else st.2.2.2.getD i 0 := by
      have h0 := updUnc_getD g.inputs (gateTT g st) st.2.2.2 0 i
      simpa [stepSt, push] using h0
    rw [hget] at h
    have hu : (st.2.2.2.getD i 0).testBit t = true ∧
        (g.inputs.contains i = true → (sens (gateTT g st) i).testBit t = false) := by
      split at h
      · rw [Nat.testBit_xor, Nat.testBit_and] at h
        exact ⟨(xor_and_self h).1, fun _ => (xor_and_self h).2⟩
      · rename_i hc
        exact ⟨h, fun h' => absurd h' hc⟩
    obtain ⟨h1, h2, h3⟩ := hunc i hi t hu.1
    obtain ⟨ht, ht', hbits⟩ := lo_spec hi h1
    refine ⟨h1, h2, ?_⟩
    intro k hk9 hk
    rw [hW1] at hk
    by_cases hlt' : k < st.1
    · rw [stepSt, wire_push_lt st g _ hlt']
      exact h3 k hk9 hlt'
    · have hEq : k = st.1 := by omega
      subst hEq
      rw [stepSt, wire_push_last]
      by_cases hc : g.inputs.contains i = true
      · have hs0 := hu.2 hc
        rw [sens_bit, h1] at hs0
        exact xor_and_false hs0
      · rw [gateTT_bit hs ht, gateTT_bit hs ht']
        congr 1
        apply List.map_congr_left
        intro a ha
        have hai : a ≠ i := by
          rintro rfl
          exact hc (by simpa using ha)
        have haW := hlt a ha
        by_cases ha9 : a < 9
        · rw [hinp a ha9, inp_bit a ha9 t ht, inp_bit a ha9 _ ht', hbits a ha9]
          simp [hai]
        · exact h3 a (by omega) haW
  · intro g' hg' w hw
    rw [hW1]
    rcases List.mem_append.mp hg' with hg' | hg'
    · have := hbd g' hg' w hw
      omega
    · have hEq : g' = g := by simpa using hg'
      subst hEq
      have := hlt w hw
      omega

theorem needList_nodup {pre : List Gate} {st : St} (hinv : Inv pre st) : (needList st).Nodup := by
  obtain ⟨-, -, -, ⟨hnd, hun⟩, ⟨hul, -⟩, -⟩ := hinv
  unfold needList
  rw [List.nodup_append]
  refine ⟨hnd, nzIdx_nodup _ _, ?_⟩
  intro x hx y hy
  have h1 := (hun x hx).1
  obtain ⟨j, rfl, hj, -⟩ := (mem_nzIdx _ _ _).mp hy
  rw [hul] at hj
  omega

theorem wiresAt_append (pre rest : List Gate) (t : ℕ) :
    wiresAt (pre ++ rest) t = rest.foldl step (wiresAt pre t) := by
  simp [wiresAt, List.foldl_append]

theorem must_read {pre rest : List Gate} {st : St} (hv : Valid (pre ++ rest))
    (hpre : 1 ≤ pre.length) (hinv : Inv pre st) {i : ℕ} (hi : i ∈ nzIdx st.2.2.2 0) :
    ∃ g ∈ rest, i ∈ g.inputs := by
  obtain ⟨hW, hinp, hsem, -, ⟨hul, hunc⟩, -⟩ := hinv
  obtain ⟨j, hj0, hj, hne⟩ := (mem_nzIdx _ _ _).mp hi
  have hij : i = j := by omega
  subst hij
  rw [hul] at hj
  obtain ⟨t, htb⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨h1, h2, h3⟩ := hunc i hj t htb
  obtain ⟨ht, ht', hbits⟩ := lo_spec hj h1
  obtain ⟨hlen, hval⟩ := hsem t ht
  obtain ⟨hlen', hval'⟩ := hsem (2 ^ i + t) ht'
  have hiW : i < st.1 := by omega
  have hset : wiresAt pre (2 ^ i + t) = (wiresAt pre t).set i true := by
    apply List.ext_getElem
    · rw [List.length_set, hlen, hlen']
    · intro k hk1 hk2
      have hk : k < st.1 := by rw [← hlen']; exact hk1
      have hk3 : k < (wiresAt pre t).length := by rw [hlen]; exact hk
      have e1 : (wiresAt pre (2 ^ i + t))[k] = (wire st k).testBit (2 ^ i + t) := by
        rw [← hval' k hk, List.getD_eq_getElem _ _ hk1]
      have e2 : (wiresAt pre t)[k] = (wire st k).testBit t := by
        rw [← hval k hk, List.getD_eq_getElem _ _ hk3]
      rw [e1, List.getElem_set]
      by_cases hik : i = k
      · subst hik
        rw [hinp i hj, inp_bit i hj _ ht', hbits i hj]
        simp
      · rw [e2]
        simp only [hik, ↓reduceIte]
        by_cases hk9 : k < 9
        · rw [hinp k hk9, inp_bit k hk9 _ ht', inp_bit k hk9 t ht, hbits k hk9]
          simp [Ne.symm hik]
        · exact (h3 k (by omega) hk).symm
  by_contra hno
  have hno' : ∀ g ∈ rest, i ∉ g.inputs := fun g hg hmem => hno ⟨g, hg, hmem⟩
  obtain ⟨-, -, -, hev⟩ := hv
  have e1 := hev t ht
  have e2 := hev (2 ^ i + t) ht'
  rw [wiresAt_append] at e1 e2
  rw [hset, foldl_set rest (wiresAt pre t) (by rw [hlen]; exact hiW) hno'] at e2
  have hout : i ≠ 8 + (pre ++ rest).length := by
    rw [List.length_append]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hout, ← List.getD_eq_getElem?_getD, e1] at e2
  exact h2 e2

theorem unread_read {pre rest : List Gate} {st : St} (hv : Valid (pre ++ rest))
    (hinv : Inv pre st) {w : ℕ} (hw : w ∈ st.2.2.1) (hlast : w + 1 < 9 + (pre ++ rest).length) :
    ∃ g ∈ rest, w ∈ g.inputs := by
  obtain ⟨-, -, -, ⟨-, hun⟩, -, -⟩ := hinv
  obtain ⟨h9, -, hnot⟩ := hun w hw
  obtain ⟨-, -, huse, -⟩ := hv
  obtain ⟨k, -, hk⟩ := huse ⟨w - 9, by omega⟩ (by simp only; omega)
  have hw' : 9 + (w - 9) = w := by omega
  simp only [hw'] at hk
  have hmem := List.get_mem (pre ++ rest) k
  rcases List.mem_append.mp hmem with h | h
  · exact absurd hk (hnot _ h)
  · exact ⟨_, h, hk⟩

theorem rest_read {pre rest : List Gate} {st : St} (hv : Valid (pre ++ rest))
    (hinv : Inv pre st) {j : ℕ} (hj : j + 1 < rest.length) :
    ∃ g ∈ rest, st.1 + j ∈ g.inputs := by
  obtain ⟨hW, -, -, -, -, hbd⟩ := hinv
  obtain ⟨-, -, huse, -⟩ := hv
  obtain ⟨k, -, hk⟩ := huse ⟨pre.length + j, by rw [List.length_append]; omega⟩
    (by simp only [List.length_append]; omega)
  have hw' : 9 + (pre.length + j) = st.1 + j := by omega
  simp only [hw'] at hk
  have hmem := List.get_mem (pre ++ rest) k
  rcases List.mem_append.mp hmem with h | h
  · have := hbd _ h _ hk
    omega
  · exact ⟨_, h, hk⟩

theorem count_le {pre rest : List Gate} {st : St} (hv : Valid (pre ++ rest))
    (hpre : 1 ≤ pre.length) (hinv : Inv pre st) : (needList st).length ≤ rest.length + 1 := by
  have hnd := needList_nodup hinv
  have hW := hinv.1
  have hunW : ∀ w ∈ st.2.2.1, w < st.1 := fun w hw => (hinv.2.2.2.1.2 w hw).2.1
  have hnz9 : ∀ i ∈ nzIdx st.2.2.2 0, i < 9 := by
    intro i hi
    obtain ⟨j, rfl, hj, -⟩ := (mem_nzIdx _ _ _).mp hi
    rw [hinv.2.2.2.2.1.1] at hj
    omega
  by_cases hr : rest = []
  · subst hr
    have hsub : needList st ⊆ [st.1 - 1] := by
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · by_cases hl : w + 1 < 9 + (pre ++ ([] : List Gate)).length
        · obtain ⟨g, hg, -⟩ := unread_read hv hinv h hl
          simp at hg
        · have := hunW w h
          simp only [List.append_nil] at hl
          simp only [List.mem_singleton]
          omega
      · obtain ⟨g, hg, -⟩ := must_read hv hpre hinv h
        simp at hg
    have := length_le_of_nodup_subset hnd hsub
    simpa using this
  · have hrl : 1 ≤ rest.length := by
      cases rest with
      | nil => exact absurd rfl hr
      | cons _ _ => simp
    have hLnd : (needList st ++ (List.range (rest.length - 1)).map fun j => st.1 + j).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd, List.Nodup.map (fun a b h => by simpa using h) List.nodup_range, ?_⟩
      intro x hx y hy
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_append.mp hx with h | h
      · have := hunW x h
        omega
      · have := hnz9 x h
        omega
    have hLsub : (needList st ++ (List.range (rest.length - 1)).map fun j => st.1 + j) ⊆
        rest.flatMap fun g => g.inputs := by
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨g, hg, hwg⟩ := unread_read hv hinv h (by
            rw [List.length_append]
            have := hunW w h
            omega)
          exact List.mem_flatMap.mpr ⟨g, hg, hwg⟩
        · obtain ⟨g, hg, hwg⟩ := must_read hv hpre hinv h
          exact List.mem_flatMap.mpr ⟨g, hg, hwg⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        obtain ⟨g, hg, hwg⟩ := rest_read (j := j) hv hinv (by
          have := List.mem_range.mp hj
          omega)
        exact List.mem_flatMap.mpr ⟨g, hg, hwg⟩
    have h1 := length_le_of_nodup_subset hLnd hLsub
    have h2 := reads_le rest (fun g hg => hv.1 g (List.mem_append_right _ hg))
    simp only [List.length_append, List.length_map, List.length_range] at h1
    omega

theorem filter_bound {A ins : List ℕ} (hA : A.Nodup) :
    A.length ≤ (A.filter fun w => !ins.contains w).length +
      (ins.filter fun c => A.contains c).length := by
  have h1 : (A.filter fun w => ins.contains w).length ≤
      (ins.filter fun c => A.contains c).length := by
    apply length_le_of_nodup_subset (hA.filter _)
    intro w hw
    obtain ⟨hwA, hwi⟩ := List.mem_filter.mp hw
    exact List.mem_filter.mpr ⟨by simpa using hwi, by simpa using hwA⟩
  have h2 := List.length_eq_length_filter_add (l := A) (fun w => ins.contains w)
  beta_reduce at h2
  omega

theorem tight {pre : List Gate} {st : St} {g : Gate} (hinv : Inv pre st) (hs : Shape g st.1)
    (hlt : (needList (stepSt st g)).length < (needList st).length) :
    ∃ a b, a ∈ needList st ∧ b ∈ needList st ∧ a < b ∧
      (g = ⟨GateOp.and, [a, b]⟩ ∨ g = ⟨GateOp.or, [a, b]⟩) := by
  have hnd := needList_nodup hinv
  have h1 : ((nzIdx st.2.2.2 0).filter fun w => !g.inputs.contains w).length ≤
      (nzIdx (stepSt st g).2.2.2 0).length := by
    apply length_le_of_nodup_subset ((nzIdx_nodup _ _).filter _)
    intro i hi
    obtain ⟨hi1, hi2⟩ := List.mem_filter.mp hi
    obtain ⟨j, rfl, hj, hne⟩ := (mem_nzIdx _ _ _).mp hi1
    have h0 := updUnc_getD g.inputs (gateTT g st) st.2.2.2 0 j
    have hc : g.inputs.contains (0 + j) = false := by simpa using hi2
    rw [hc] at h0
    refine (mem_nzIdx _ _ _).mpr ⟨j, rfl, ?_, ?_⟩
    · simpa [stepSt, push, updUnc_length] using hj
    · have h0' : (stepSt st g).2.2.2.getD j 0 = st.2.2.2.getD j 0 := by
        simpa [stepSt, push] using h0
      rw [h0']
      exact hne
  have h2 : (needList (stepSt st g)).length =
      (st.2.2.1.filter fun w => !g.inputs.contains w).length + 1 +
        (nzIdx (stepSt st g).2.2.2 0).length := by
    simp only [needList, stepSt, push, List.length_append, List.length_singleton]
  have h3 : ((needList st).filter fun w => !g.inputs.contains w).length =
      (st.2.2.1.filter fun w => !g.inputs.contains w).length +
        ((nzIdx st.2.2.2 0).filter fun w => !g.inputs.contains w).length := by
    simp [needList, List.filter_append]
  have h4 := filter_bound (ins := g.inputs) hnd
  have hhits : 2 ≤ (g.inputs.filter fun c => (needList st).contains c).length := by omega
  obtain ⟨op, ins⟩ := g
  rcases hs with ⟨hop, a, -, hin⟩ | ⟨hop, a, b, hab, -, hin⟩
  · simp only at hin
    subst hin
    dsimp only at hhits
    have h5 := List.length_filter_le (fun c => (needList st).contains c) [a]
    simp only [List.length_singleton] at h5
    omega
  · simp only at hop hin
    subst hin
    dsimp only at hhits
    have hboth : a ∈ needList st ∧ b ∈ needList st := by
      by_cases ha : a ∈ needList st <;> by_cases hb : b ∈ needList st <;>
        simp [List.filter, ha, hb] at hhits ⊢
    refine ⟨a, b, hboth.1, hboth.2, hab, ?_⟩
    rcases hop with hop | hop <;> subst hop <;> simp

theorem mem_cands {g : Gate} {W : ℕ} (hs : Shape g W) : g ∈ cands W := by
  obtain ⟨op, ins⟩ := g
  rcases hs with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
  · simp only at hop hin
    subst hop hin
    exact List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, List.mem_cons_self ..⟩
  · simp only at hop hin
    subst hin
    refine List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨a, List.mem_range.mpr hab, ?_⟩)⟩
    rcases hop with hop | hop <;> subst hop <;> simp

theorem mem_candList {pre : List Gate} {st : St} {g : Gate} {r : ℕ} (hinv : Inv pre st)
    (hs : Shape g st.1) (hle : (needList (stepSt st g)).length ≤ r + 1) : g ∈ candList r st := by
  unfold candList
  rw [forceList_eq]
  split
  · obtain ⟨a, b, ha, hb, hab, hg⟩ := tight hinv hs (by omega)
    refine List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨a, ha, ?_⟩⟩
    rcases hg with rfl | rfl <;> simp [hab]
  · exact mem_cands hs

theorem complete_contra {pre : List Gate} {st : St} (hv : Valid pre) (hpre : 1 ≤ pre.length)
    (hinv : Inv pre st) : ((wire st (st.1 - 1) ^^^ tgt) &&& full) = 0 := by
  obtain ⟨hW, -, hsem, -, -, -⟩ := hinv
  obtain ⟨-, -, -, hev⟩ := hv
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, Nat.testBit_xor, full_bit, Nat.zero_testBit]
  by_cases ht : t < 512
  · have h1 := (hsem t ht).2 (st.1 - 1) (by omega)
    have h2 := hev t ht
    have h8 : 8 + pre.length = st.1 - 1 := by omega
    rw [h8, h1] at h2
    simp [h2]
  · simp [ht]

theorem sound {gs : List Gate} (hv : Valid gs) : ∀ (r : ℕ) (pre rest : List Gate) (st : St),
    gs = pre ++ rest → 1 ≤ pre.length → Inv pre st → rest ≠ [] → rest.length ≤ r →
    search tgt r st = true → False := by
  intro r
  induction r with
  | zero =>
    intro pre rest st _ _ _ hne hlen _
    cases rest with
    | nil => exact hne rfl
    | cons _ _ => simp at hlen
  | succ r ih =>
    intro pre rest st hgs hpre hinv hne hlen hsearch
    obtain _ | ⟨g, rest'⟩ := rest
    · exact hne rfl
    subst hgs
    have hshape : Shape g st.1 := by
      have h := hv.2.1 ⟨pre.length, by simp⟩
      have hg : (pre ++ g :: rest').get ⟨pre.length, by simp⟩ = g := by simp
      rw [hg, ← hinv.1] at h
      exact h
    have hinv' := inv_step hinv hshape
    have hv' : Valid ((pre ++ [g]) ++ rest') := by simpa using hv
    have hcount := count_le hv' (by simp) hinv'
    have hlen' : rest'.length ≤ r := by simpa using hlen
    have hmem : g ∈ candList r st := mem_candList hinv hshape (by omega)
    have htry : tryGate tgt r st (search tgt r) g = true := List.all_eq_true.mp hsearch g hmem
    rw [tryGate_eq] at htry
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at htry
    obtain ⟨hnt, hlt | hrec⟩ := htry
    · omega
    · by_cases hr : rest' = []
      · subst hr
        have hv'' : Valid (pre ++ [g]) := by simpa using hv'
        have hz := complete_contra hv'' (by simp) hinv'
        have hlast : wire (stepSt st g) ((stepSt st g).1 - 1) = gateTT g st := by
          have h1 : (stepSt st g).1 - 1 = st.1 := by simp [stepSt, push]
          rw [h1, stepSt, wire_push_last]
        rw [hlast] at hz
        simp [hz] at hnt
      · exact ih (pre ++ [g]) rest' (stepSt st g) (by simp) (by simp) hinv' hr hlen' hrec

theorem all_of_chunks {α : Type} (f : α → Bool) (c : ℕ) : ∀ (n : ℕ) (l : List α),
    l.length ≤ n * c → (∀ k < n, ((l.drop (k * c)).take c).all f = true) → l.all f = true := by
  intro n
  induction n with
  | zero =>
    intro l hl _
    cases l with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l hl h
    have h0 := h 0 (by omega)
    simp only [Nat.zero_mul, List.drop_zero] at h0
    have hrest : (l.drop c).all f = true := by
      apply ih
      · rw [List.length_drop]
        have e : (n + 1) * c = n * c + c := Nat.succ_mul n c
        omega
      · intro k hk
        have hk' := h (k + 1) (by omega)
        have e : (l.drop c).drop (k * c) = l.drop ((k + 1) * c) := by
          rw [List.drop_drop]
          congr 1
          ring
        rw [e]
        exact hk'
    have e := List.take_append_drop c l
    rw [← e, List.all_append, h0, hrest]
    rfl

def chunk (r : ℕ) (gs : List Gate) (c k : ℕ) : Bool :=
  force tgt fun tg =>
    forceList (gs.foldl stepSt init).2.1 fun rt =>
      forceList (gs.foldl stepSt init).2.2.1 fun un =>
        forceList (gs.foldl stepSt init).2.2.2 fun uc =>
          (((candList r ((gs.foldl stepSt init).1, rt, un, uc)).drop (k * c)).take c).all
            (tryGate tg r ((gs.foldl stepSt init).1, rt, un, uc) (search tg r))

theorem chunk_eq (r : ℕ) (gs : List Gate) (c k : ℕ) :
    chunk r gs c k = (((candList r (gs.foldl stepSt init)).drop (k * c)).take c).all
      (tryGate tgt r (gs.foldl stepSt init) (search tgt r)) := by
  simp only [chunk, force_eq, forceList_eq]

def startOk (gs : List Gate) : Bool :=
  force tgt fun tg =>
    (wire (gs.foldl stepSt init) ((gs.foldl stepSt init).1 - 1) ^^^ tg) &&& full != 0

theorem startOk_eq (gs : List Gate) : startOk gs =
    ((wire (gs.foldl stepSt init) ((gs.foldl stepSt init).1 - 1) ^^^ tgt) &&& full != 0) := by
  simp only [startOk, force_eq]

theorem root_of_chunks (r : ℕ) (gs : List Gate) (c n : ℕ)
    (hlen : (candList r (gs.foldl stepSt init)).length ≤ n * c)
    (h : ∀ k < n, chunk r gs c k = true) :
    search tgt (r + 1) (gs.foldl stepSt init) = true := by
  show (candList r (gs.foldl stepSt init)).all
    (tryGate tgt r (gs.foldl stepSt init) (search tgt r)) = true
  exact all_of_chunks _ c n _ hlen (fun k hk => by rw [← chunk_eq]; exact h k hk)

def tryGate2 (tg r : ℕ) (st : St) (c2 n2 k2 : ℕ) (g : Gate) : Bool :=
  force (gateTT g st) fun tt =>
    ((tt ^^^ tg) &&& full != 0) &&
      forceList (st.2.2.1.filter (fun w => !g.inputs.contains w) ++ [st.1]) fun un =>
        forceList (updUnc g.inputs tt st.2.2.2 0) fun uc =>
          (decide (r + 2 < un.length + (nzIdx uc 0).length) ||
            (decide ((candList r (st.1 + 1, tt :: st.2.1, un, uc)).length ≤ n2 * c2) &&
              (((candList r (st.1 + 1, tt :: st.2.1, un, uc)).drop (k2 * c2)).take c2).all
                (tryGate tg r (st.1 + 1, tt :: st.2.1, un, uc) (search tg r))))

theorem tryGate2_eq (tg r : ℕ) (st : St) (c2 n2 k2 : ℕ) (g : Gate) :
    tryGate2 tg r st c2 n2 k2 g = (((gateTT g st ^^^ tg) &&& full != 0) &&
      (decide (r + 2 < (needList (stepSt st g)).length) ||
        (decide ((candList r (stepSt st g)).length ≤ n2 * c2) &&
          (((candList r (stepSt st g)).drop (k2 * c2)).take c2).all
            (tryGate tg r (stepSt st g) (search tg r))))) := by
  unfold tryGate2
  rw [force_eq]
  simp only [forceList_eq, needList, stepSt, push, List.length_append]
  rfl

theorem tryGate_of_sub (r : ℕ) (st : St) (c2 n2 : ℕ) (g : Gate) (hn : 0 < n2)
    (h : ∀ k2 < n2, tryGate2 tgt r st c2 n2 k2 g = true) :
    tryGate tgt (r + 1) st (search tgt (r + 1)) g = true := by
  rw [tryGate_eq]
  have h0 := h 0 hn
  rw [tryGate2_eq] at h0
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h0 ⊢
  refine ⟨h0.1, ?_⟩
  by_cases hp : r + 2 < (needList (stepSt st g)).length
  · exact Or.inl (by omega)
  · right
    have hlen : (candList r (stepSt st g)).length ≤ n2 * c2 := by
      rcases h0.2 with h1 | h1
      · exact absurd h1 hp
      · exact h1.1
    show (candList r (stepSt st g)).all (tryGate tgt r (stepSt st g) (search tgt r)) = true
    apply all_of_chunks _ c2 n2 _ hlen
    intro k2 hk2
    have hk := h k2 hk2
    rw [tryGate2_eq] at hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk
    rcases hk.2 with h1 | h1
    · exact absurd h1 hp
    · exact h1.2

def chunk2 (r : ℕ) (gs : List Gate) (k c2 n2 k2 : ℕ) : Bool :=
  force tgt fun tg =>
    forceList (gs.foldl stepSt init).2.1 fun rt =>
      forceList (gs.foldl stepSt init).2.2.1 fun un =>
        forceList (gs.foldl stepSt init).2.2.2 fun uc =>
          (((candList (r + 1) ((gs.foldl stepSt init).1, rt, un, uc)).drop k).take 1).all
            (tryGate2 tg r ((gs.foldl stepSt init).1, rt, un, uc) c2 n2 k2)

theorem chunk2_eq (r : ℕ) (gs : List Gate) (k c2 n2 k2 : ℕ) :
    chunk2 r gs k c2 n2 k2 = (((candList (r + 1) (gs.foldl stepSt init)).drop k).take 1).all
      (tryGate2 tgt r (gs.foldl stepSt init) c2 n2 k2) := by
  simp only [chunk2, force_eq, forceList_eq]

theorem chunk_of_sub (r : ℕ) (gs : List Gate) (k c2 n2 : ℕ) (hn : 0 < n2)
    (h : ∀ k2 < n2, chunk2 r gs k c2 n2 k2 = true) : chunk (r + 1) gs 1 k = true := by
  rw [chunk_eq, Nat.mul_one, List.all_eq_true]
  intro g hg
  apply tryGate_of_sub r _ c2 n2 g hn
  intro k2 hk2
  have hk := h k2 hk2
  rw [chunk2_eq] at hk
  exact List.all_eq_true.mp hk g hg

theorem final (g0 g1 : Gate) (rest : List Gate) (output n : ℕ)
    (hfan : ∀ g ∈ g0 :: g1 :: rest, g.inputs.length ≤ 2)
    (hsize : (g0 :: g1 :: rest).length ≤ n + 3)
    (heval : ∀ x : Fin 9 → Bool,
      ((g0 :: g1 :: rest).foldl step (List.ofFn x)).getD output false = target x)
    (hout : output + 1 = 9 + (g0 :: g1 :: rest).length)
    (hshape : ∀ j : Fin (g0 :: g1 :: rest).length, Shape ((g0 :: g1 :: rest).get j) (9 + j.val))
    (huse : ∀ j : Fin (g0 :: g1 :: rest).length, j.val + 1 < (g0 :: g1 :: rest).length →
      ∃ k : Fin (g0 :: g1 :: rest).length,
        j.val < k.val ∧ 9 + j.val ∈ ((g0 :: g1 :: rest).get k).inputs)
    (hstart : startOk [g0, g1] = true)
    (hsearch : search tgt (n + 1) ([g0, g1].foldl stepSt init) = true) : False := by
  have hs0 : Shape g0 init.1 := hshape ⟨0, by simp⟩
  have hs1 : Shape g1 (stepSt init g0).1 := hshape ⟨1, by simp⟩
  have hinv0 : Inv [g0, g1] ([g0, g1].foldl stepSt init) := inv_step (inv_step inv_init hs0) hs1
  have hev : ∀ t < 512, (wiresAt (g0 :: g1 :: rest) t).getD (8 + (g0 :: g1 :: rest).length) false
      = tgt.testBit t := by
    intro t ht
    have h := heval (fun j => t.testBit j.val)
    rw [ofFn_pt] at h
    have ho : output = 8 + (g0 :: g1 :: rest).length := by omega
    rw [tgt_bit t ht, ← ho]
    exact h
  have hv : Valid (g0 :: g1 :: rest) := ⟨hfan, hshape, huse, hev⟩
  by_cases hr : rest = []
  · subst hr
    have hz := complete_contra hv (by simp) hinv0
    rw [startOk_eq, hz] at hstart
    simp at hstart
  · exact sound hv (n + 1) [g0, g1] rest _ rfl (by simp) hinv0 hr
      (by simp only [List.length_cons] at hsize; omega) hsearch

theorem start_ok : startOk [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] = true := by decide +kernel

theorem cand_len : (candList 9 ([⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩].foldl stepSt init)).length ≤ 110 * 1 := by
  decide +kernel

theorem c0 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 0 = true := by decide +kernel

theorem c1 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 1 = true := by decide +kernel

theorem c2 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 2 = true := by decide +kernel

theorem c3 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 3 = true := by decide +kernel

theorem c4 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 4 = true := by decide +kernel

theorem c5 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 5 = true := by decide +kernel

theorem c6 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 6 = true := by decide +kernel

theorem c7 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 7 = true := by decide +kernel

theorem c8 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 8 = true := by decide +kernel

theorem c9 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 9 = true := by decide +kernel

theorem c10 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 10 = true := by decide +kernel

theorem c11 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 11 = true := by decide +kernel

theorem c12 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 12 = true := by decide +kernel

theorem c13 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 13 = true := by decide +kernel

theorem c14 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 14 = true := by decide +kernel

theorem c15 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 15 = true := by decide +kernel

theorem c16 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 16 = true := by decide +kernel

theorem c17 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 17 = true := by decide +kernel

theorem c18 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 18 = true := by decide +kernel

theorem c19 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 19 = true := by decide +kernel

theorem c20 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 20 = true := by decide +kernel

theorem c21 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 21 = true := by decide +kernel

theorem c22 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 22 = true := by decide +kernel

theorem c23 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 23 = true := by decide +kernel

theorem c24 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 24 = true := by decide +kernel

theorem c25 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 25 = true := by decide +kernel

theorem c26 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 26 = true := by decide +kernel

theorem c27 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 27 = true := by decide +kernel

theorem c28 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 28 = true := by decide +kernel

theorem c29 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 29 = true := by decide +kernel

theorem c30 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 30 = true := by decide +kernel

theorem c31 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 31 = true := by decide +kernel

theorem c32 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 32 = true := by decide +kernel

theorem c33 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 33 = true := by decide +kernel

theorem c34 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 34 = true := by decide +kernel

theorem c35 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 35 = true := by decide +kernel

theorem c36 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 36 = true := by decide +kernel

theorem c37 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 37 = true := by decide +kernel

theorem c38 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 38 = true := by decide +kernel

theorem c39 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 39 = true := by decide +kernel

theorem c40 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 40 = true := by decide +kernel

theorem c41 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 41 = true := by decide +kernel

theorem c42 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 42 = true := by decide +kernel

theorem c43 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 43 = true := by decide +kernel

theorem c44 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 44 = true := by decide +kernel

theorem c45 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 45 = true := by decide +kernel

theorem c46 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 46 = true := by decide +kernel

theorem c47 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 47 = true := by decide +kernel

theorem c48 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 48 = true := by decide +kernel

theorem c49 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 49 = true := by decide +kernel

theorem s50_0 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 0 = true := by decide +kernel

theorem s50_1 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 1 = true := by decide +kernel

theorem s50_2 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 2 = true := by decide +kernel

theorem s50_3 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 3 = true := by decide +kernel

theorem s50_4 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 4 = true := by decide +kernel

theorem s50_5 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 5 = true := by decide +kernel

theorem s50_6 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 6 = true := by decide +kernel

theorem s50_7 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 7 = true := by decide +kernel

theorem s50_8 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 8 = true := by decide +kernel

theorem s50_9 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 9 = true := by decide +kernel

theorem s50_10 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 10 = true := by decide +kernel

theorem s50_11 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 50 8 12 11 = true := by decide +kernel

theorem c50 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 50 = true := by
  apply chunk_of_sub 8 _ 50 8 12 (by decide)
  intro k2 hk2
  interval_cases k2
  · exact s50_0
  · exact s50_1
  · exact s50_2
  · exact s50_3
  · exact s50_4
  · exact s50_5
  · exact s50_6
  · exact s50_7
  · exact s50_8
  · exact s50_9
  · exact s50_10
  · exact s50_11

theorem c51 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 51 = true := by decide +kernel

theorem c52 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 52 = true := by decide +kernel

theorem c53 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 53 = true := by decide +kernel

theorem c54 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 54 = true := by decide +kernel

theorem c55 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 55 = true := by decide +kernel

theorem c56 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 56 = true := by decide +kernel

theorem c57 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 57 = true := by decide +kernel

theorem c58 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 58 = true := by decide +kernel

theorem c59 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 59 = true := by decide +kernel

theorem c60 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 60 = true := by decide +kernel

theorem c61 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 61 = true := by decide +kernel

theorem c62 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 62 = true := by decide +kernel

theorem c63 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 63 = true := by decide +kernel

theorem c64 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 64 = true := by decide +kernel

theorem c65 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 65 = true := by decide +kernel

theorem c66 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 66 = true := by decide +kernel

theorem c67 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 67 = true := by decide +kernel

theorem c68 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 68 = true := by decide +kernel

theorem c69 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 69 = true := by decide +kernel

theorem c70 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 70 = true := by decide +kernel

theorem c71 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 71 = true := by decide +kernel

theorem c72 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 72 = true := by decide +kernel

theorem c73 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 73 = true := by decide +kernel

theorem c74 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 74 = true := by decide +kernel

theorem c75 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 75 = true := by decide +kernel

theorem c76 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 76 = true := by decide +kernel

theorem c77 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 77 = true := by decide +kernel

theorem c78 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 78 = true := by decide +kernel

theorem c79 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 79 = true := by decide +kernel

theorem c80 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 80 = true := by decide +kernel

theorem c81 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 81 = true := by decide +kernel

theorem c82 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 82 = true := by decide +kernel

theorem c83 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 83 = true := by decide +kernel

theorem s84_0 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 0 = true := by decide +kernel

theorem s84_1 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 1 = true := by decide +kernel

theorem s84_2 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 2 = true := by decide +kernel

theorem s84_3 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 3 = true := by decide +kernel

theorem s84_4 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 4 = true := by decide +kernel

theorem s84_5 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 5 = true := by decide +kernel

theorem s84_6 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 6 = true := by decide +kernel

theorem s84_7 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 7 = true := by decide +kernel

theorem s84_8 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 8 = true := by decide +kernel

theorem s84_9 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 9 = true := by decide +kernel

theorem s84_10 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 10 = true := by decide +kernel

theorem s84_11 : chunk2 8 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 84 8 12 11 = true := by decide +kernel

theorem c84 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 84 = true := by
  apply chunk_of_sub 8 _ 84 8 12 (by decide)
  intro k2 hk2
  interval_cases k2
  · exact s84_0
  · exact s84_1
  · exact s84_2
  · exact s84_3
  · exact s84_4
  · exact s84_5
  · exact s84_6
  · exact s84_7
  · exact s84_8
  · exact s84_9
  · exact s84_10
  · exact s84_11

theorem c85 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 85 = true := by decide +kernel

theorem c86 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 86 = true := by decide +kernel

theorem c87 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 87 = true := by decide +kernel

theorem c88 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 88 = true := by decide +kernel

theorem c89 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 89 = true := by decide +kernel

theorem c90 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 90 = true := by decide +kernel

theorem c91 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 91 = true := by decide +kernel

theorem c92 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 92 = true := by decide +kernel

theorem c93 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 93 = true := by decide +kernel

theorem c94 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 94 = true := by decide +kernel

theorem c95 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 95 = true := by decide +kernel

theorem c96 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 96 = true := by decide +kernel

theorem c97 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 97 = true := by decide +kernel

theorem c98 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 98 = true := by decide +kernel

theorem c99 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 99 = true := by decide +kernel

theorem c100 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 100 = true := by decide +kernel

theorem c101 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 101 = true := by decide +kernel

theorem c102 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 102 = true := by decide +kernel

theorem c103 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 103 = true := by decide +kernel

theorem c104 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 104 = true := by decide +kernel

theorem c105 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 105 = true := by decide +kernel

theorem c106 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 106 = true := by decide +kernel

theorem c107 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 107 = true := by decide +kernel

theorem c108 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 108 = true := by decide +kernel

theorem c109 : chunk 9 [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] 1 109 = true := by decide +kernel

theorem search_ok : search tgt 10 ([⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩].foldl stepSt init) = true := by
  apply root_of_chunks 9 _ 1 110 cand_len
  intro k hk
  interval_cases k
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c24
  · exact c25
  · exact c26
  · exact c27
  · exact c28
  · exact c29
  · exact c30
  · exact c31
  · exact c32
  · exact c33
  · exact c34
  · exact c35
  · exact c36
  · exact c37
  · exact c38
  · exact c39
  · exact c40
  · exact c41
  · exact c42
  · exact c43
  · exact c44
  · exact c45
  · exact c46
  · exact c47
  · exact c48
  · exact c49
  · exact c50
  · exact c51
  · exact c52
  · exact c53
  · exact c54
  · exact c55
  · exact c56
  · exact c57
  · exact c58
  · exact c59
  · exact c60
  · exact c61
  · exact c62
  · exact c63
  · exact c64
  · exact c65
  · exact c66
  · exact c67
  · exact c68
  · exact c69
  · exact c70
  · exact c71
  · exact c72
  · exact c73
  · exact c74
  · exact c75
  · exact c76
  · exact c77
  · exact c78
  · exact c79
  · exact c80
  · exact c81
  · exact c82
  · exact c83
  · exact c84
  · exact c85
  · exact c86
  · exact c87
  · exact c88
  · exact c89
  · exact c90
  · exact c91
  · exact c92
  · exact c93
  · exact c94
  · exact c95
  · exact c96
  · exact c97
  · exact c98
  · exact c99
  · exact c100
  · exact c101
  · exact c102
  · exact c103
  · exact c104
  · exact c105
  · exact c106
  · exact c107
  · exact c108
  · exact c109

end PEqualNP.Outside.L_meta_27793

theorem PEqualNP.Outside.L_meta_27793 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩)) := by
  rintro ⟨⟨gates, output⟩, hfan, hsize, heval, hout, hshape, -, huse, hh0, hh1⟩
  obtain _ | ⟨a0, _ | ⟨a1, rest⟩⟩ := gates
  · simp at hh0
  · simp at hh1
  simp only [List.head?_cons, List.tail_cons, Option.some.injEq] at hh0 hh1
  subst hh0 hh1
  exact PEqualNP.Outside.L_meta_27793.final _ _ rest output 9 (fun g hg => (hfan g hg).2) hsize heval hout
    hshape huse PEqualNP.Outside.L_meta_27793.start_ok PEqualNP.Outside.L_meta_27793.search_ok
