import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51096

open PEqualNP.CircuitLowerBounds

def mop (op : GateOp) (l : List ℕ) : ℕ :=
  match op with
  | .and => l.foldr (fun a b => a &&& b) 63
  | .or => l.foldr (fun a b => a ||| b) 0
  | .not => 63 ^^^ l.headD 0
  | _ => 0

def mw (gs : List Gate) (m : List ℕ) : List ℕ :=
  gs.foldl (fun w g => w ++ [mop g.op (g.inputs.map fun i => w.getD i 0)]) m

def m0 : List ℕ := [62, 60, 56, 48, 32, 0, 63]

def xs (t : ℕ) : List Bool := (List.ofFn (fun i : Fin 5 => decide (i.val < t))) ++ [false, true]

theorem getD_snoc {α : Type} (a : List α) (v d : α) (i : ℕ) :
    (a ++ [v]).getD i d = if i = a.length then v else a.getD i d := by
  by_cases h : i < a.length
  · rw [if_neg (Nat.ne_of_lt h)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · by_cases he : i = a.length
    · subst he; simp [List.getD_eq_getElem?_getD]
    · rw [if_neg he]
      have h1 : a.length < i := by omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem t63 (t : ℕ) (ht : t < 6) : (63 : ℕ).testBit t = true := by
  interval_cases t <;> decide

theorem fold_and (t : ℕ) (ht : t < 6) :
    ∀ l : List ℕ, (l.foldr (fun a b => a &&& b) 63).testBit t = l.all (fun a => a.testBit t)
  | [] => by simpa using t63 t ht
  | a :: l => by simp [Nat.testBit_and, fold_and t ht l]

theorem fold_or (t : ℕ) :
    ∀ l : List ℕ, (l.foldr (fun a b => a ||| b) 0).testBit t = l.any (fun a => a.testBit t)
  | [] => by simp
  | a :: l => by simp [Nat.testBit_or, fold_or t l]

theorem gate_bit (t : ℕ) (ht : t < 6) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (lm : List ℕ) :
    op.eval (lm.map fun a => a.testBit t) = (mop op lm).testBit t := by
  rcases hop with rfl | rfl | rfl
  · simp [GateOp.eval, mop, fold_and t ht, List.all_map]
  · simp [GateOp.eval, mop, fold_or t, List.any_map]
  · cases lm with
    | nil => simp [GateOp.eval, mop, Nat.testBit_xor, t63 t ht]
    | cons a l => simp [GateOp.eval, mop, Nat.testBit_xor, t63 t ht]

def OpOk (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem wires_bits (t : ℕ) (ht : t < 6) :
    ∀ (gs : List Gate), OpOk gs → ∀ (w : List Bool) (m : List ℕ), w.length = m.length →
      (∀ i, w.getD i false = (m.getD i 0).testBit t) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = ((mw gs m).getD i 0).testBit t := by
  intro gs
  induction gs with
  | nil => intro _ w m _ h i; exact h i
  | cons g gs ih =>
    intro hok w m hl h i
    have hg := hok g (by simp)
    have hrest : OpOk gs := fun g' hg' => hok g' (by simp [hg'])
    simp only [List.foldl_cons, mw] at *
    apply ih hrest
    · simp [hl]
    · intro j
      rw [getD_snoc, getD_snoc, hl]
      split
      · have hmap : (g.inputs.map fun i => w.getD i false)
            = ((g.inputs.map fun i => m.getD i 0).map fun a => a.testBit t) := by
          rw [List.map_map]; exact List.map_congr_left (fun a _ => h a)
        rw [hmap, gate_bit t ht g.op hg.1]
      · exact h j

theorem mop_lt (op : GateOp) (l : List ℕ) (hl : ∀ a ∈ l, a < 64) : mop op l < 64 := by
  cases op with
  | and =>
    simp only [mop]
    induction l with
    | nil => decide
    | cons a l ih =>
      simp only [List.foldr_cons]
      exact lt_of_le_of_lt Nat.and_le_left (hl a (by simp))
  | or =>
    simp only [mop]
    induction l with
    | nil => decide
    | cons a l ih =>
      simp only [List.foldr_cons]
      have ha := hl a (by simp)
      have hr := ih (fun b hb => hl b (by simp [hb]))
      exact Nat.or_lt_two_pow (n := 6) ha hr
  | not =>
    simp only [mop]
    have : l.headD 0 < 64 := by
      cases l with
      | nil => decide
      | cons a l => exact hl a (by simp)
    exact Nat.xor_lt_two_pow (n := 6) (by decide) this
  | mod m => simp [mop]
  | maj => simp [mop]

theorem getD_mem_or (m : List ℕ) (i : ℕ) : m.getD i 0 ∈ m ∨ m.getD i 0 = 0 := by
  by_cases h : i < m.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; rw [List.getD_eq_default _ _ (by omega)]

def mem (S v : ℕ) : Bool := S.testBit v
def tg : List ℕ := [14, 35, 40]
def covered (S : ℕ) : Bool := tg.all (fun t => mem S t)
def missing (S : ℕ) : ℕ := (tg.filter (fun t => !mem S t)).length
def members (S : ℕ) : List ℕ := (List.range 64).filter (fun v => mem S v)
def cands (S : ℕ) : List ℕ :=
  (members S).flatMap fun a => (members S).flatMap fun b => [a &&& b, a ||| b]
def add (S v : ℕ) : ℕ := S ||| 2 ^ v

def bad : ℕ → ℕ → ℕ → Bool
  | 0, _, S => covered S
  | k + 1, n, S => covered S ||
      (cands S).any (fun v => !mem S v && decide (missing (add S v) ≤ k) && bad k n (add S v)) ||
      (match n with
       | 0 => false
       | n' + 1 => (members S).any (fun a => !mem S (63 ^^^ a) &&
           decide (missing (add S (63 ^^^ a)) ≤ k) && bad k n' (add S (63 ^^^ a))))

def S0 : ℕ := 2 ^ 62 + 2 ^ 60 + 2 ^ 56 + 2 ^ 48 + 2 ^ 32 + 2 ^ 0 + 2 ^ 63

theorem search_fails : ∀ k ≤ 5, ∀ n ≤ 2, bad k n S0 = false := by
  decide +kernel

theorem bad_succ (k n S : ℕ) : bad (k + 1) n S = (covered S ||
      (cands S).any (fun v => !mem S v && decide (missing (add S v) ≤ k) && bad k n (add S v)) ||
      (match n with
       | 0 => false
       | n' + 1 => (members S).any (fun a => !mem S (63 ^^^ a) &&
           decide (missing (add S (63 ^^^ a)) ≤ k) && bad k n' (add S (63 ^^^ a))))) := rfl

theorem bad_mono : ∀ (k n S : ℕ), bad k n S = true → bad (k + 1) n S = true ∧ bad k (n + 1) S = true := by
  intro k
  induction k with
  | zero =>
    intro n S h
    simp only [bad] at h
    exact ⟨by simp [bad, h], by simp [bad, h]⟩
  | succ k ih =>
    intro n S h
    rw [bad_succ, Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · constructor
      · rw [bad_succ (k + 1) n S]; simp [h]
      · rw [bad_succ k (n + 1) S]; simp [h]
    · obtain ⟨v, hv, hh⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨⟨h1, h2⟩, h3⟩ := hh
      have h2' : missing (add S v) ≤ k + 1 := by omega
      constructor
      · have := (ih n _ h3).1
        rw [bad_succ (k + 1) n S, Bool.or_eq_true, Bool.or_eq_true]
        refine Or.inl (Or.inr (List.any_eq_true.mpr ⟨v, hv, ?_⟩))
        rw [this]; simp [h1, h2']
      · have := (ih n _ h3).2
        rw [bad_succ k (n + 1) S, Bool.or_eq_true, Bool.or_eq_true]
        refine Or.inl (Or.inr (List.any_eq_true.mpr ⟨v, hv, ?_⟩))
        rw [this]; simp [h1, h2]
    · cases n with
      | zero => simp at h
      | succ n' =>
        obtain ⟨a, ha, hh⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
        obtain ⟨⟨h1, h2⟩, h3⟩ := hh
        have h2' : missing (add S (63 ^^^ a)) ≤ k + 1 := by omega
        constructor
        · have := (ih n' _ h3).1
          rw [bad_succ (k + 1) (n' + 1) S, Bool.or_eq_true, Bool.or_eq_true]
          refine Or.inr (List.any_eq_true.mpr ⟨a, ha, ?_⟩)
          rw [this]; simp [h1, h2']
        · have := (ih n' _ h3).2
          rw [bad_succ k (n' + 1 + 1) S, Bool.or_eq_true, Bool.or_eq_true]
          refine Or.inr (List.any_eq_true.mpr ⟨a, ha, ?_⟩)
          rw [this]; simp [h1, h2]

theorem bad_mono' {k n S k' n' : ℕ} (hk : k ≤ k') (hn : n ≤ n') (h : bad k n S = true) :
    bad k' n' S = true := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : ∀ a, bad (k + a) n S = true := by
    intro a; induction a with
    | zero => simpa using h
    | succ a iha => exact (bad_mono _ _ _ iha).1
  have h2 : ∀ b, bad (k + a) (n + b) S = true := by
    intro b; induction b with
    | zero => simpa using h1 a
    | succ b ihb => exact (bad_mono _ _ _ ihb).2
  exact h2 b

def Rel (S : ℕ) (L : List ℕ) : Prop := ∀ v, mem S v = true ↔ v ∈ L

theorem mem_add (S v x : ℕ) : mem (add S v) x = (mem S x || decide (v = x)) := by
  simp [mem, add, Nat.testBit_or, Nat.testBit_two_pow]

theorem rel_add {S : ℕ} {L : List ℕ} (h : Rel S L) (v : ℕ) : Rel (add S v) (L ++ [v]) := by
  intro x
  rw [mem_add]
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_append, List.mem_singleton]
  rw [h x]
  exact or_congr_right eq_comm

theorem add_self {S v : ℕ} (h : mem S v = true) : add S v = S := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := mem_add S v i
  simp only [mem] at this h
  rw [this]
  by_cases hi : v = i
  · subst hi; simp [h]
  · simp [hi]

def coveredL (L : List ℕ) : Prop := ∀ t ∈ tg, t ∈ L

theorem missing_le {S : ℕ} {L A : List ℕ} (hr : Rel S L) (hc : coveredL (L ++ A)) :
    missing S ≤ A.length := by
  unfold missing
  apply List.Nodup.length_le_of_subset
  · exact List.Nodup.filter _ (by decide)
  · intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hxt, hxm⟩ := hx
    rcases List.mem_append.mp (hc x hxt) with h | h
    · have := (hr x).mpr h
      simp [this] at hxm
    · exact h

theorem mw_append (gs : List Gate) : ∀ L : List ℕ, ∃ A : List ℕ, mw gs L = L ++ A ∧ A.length = gs.length := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [mw]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨A, hA, hl⟩ := ih (L ++ [mop g.op (g.inputs.map fun i => L.getD i 0)])
    refine ⟨mop g.op (g.inputs.map fun i => L.getD i 0) :: A, ?_, by simp [hl]⟩
    have e : mw (g :: gs) L = mw gs (L ++ [mop g.op (g.inputs.map fun i => L.getD i 0)]) := rfl
    rw [e, hA]; simp

def notcnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length

def Inv (L : List ℕ) : Prop := 0 ∈ L ∧ 63 ∈ L ∧ ∀ a ∈ L, a < 64

theorem inputs_mem {L : List ℕ} (hI : Inv L) (ins : List ℕ) :
    ∀ a ∈ ins.map (fun i => L.getD i 0), a ∈ L := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  rcases getD_mem_or L i with h | h
  · exact h
  · rw [h]; exact hI.1

theorem and63 {b : ℕ} (hlt : b < 64) : b &&& 63 = b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and]
  by_cases hi : i < 6
  · simp [t63 i hi]
  · have : b.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
      (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 6 ≤ i by omega); simpa using this))
    simp [this]

theorem step_cases {L : List ℕ} (hI : Inv L) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hmem : ∀ a ∈ l, a ∈ L) (hlen : l.length ≤ 2) :
    (op ≠ GateOp.not → ∃ a ∈ L, ∃ b ∈ L, mop op l = a &&& b ∨ mop op l = a ||| b) ∧
    (op = GateOp.not → ∃ a ∈ L, mop op l = 63 ^^^ a) := by
  rcases hop with rfl | rfl | rfl
  · refine ⟨fun _ => ?_, fun he => by cases he⟩
    match l, hlen with
    | [], _ => exact ⟨63, hI.2.1, 63, hI.2.1, Or.inl (by simp [mop])⟩
    | [a], _ =>
      have ha := hmem a (by simp)
      refine ⟨a, ha, a, ha, Or.inl ?_⟩
      simp only [mop, List.foldr_cons, List.foldr_nil, Nat.and_self]
      exact and63 (hI.2.2 a ha)
    | [a, b], _ =>
      have ha := hmem a (by simp)
      have hb := hmem b (by simp)
      refine ⟨a, ha, b, hb, Or.inl ?_⟩
      simp only [mop, List.foldr_cons, List.foldr_nil]
      rw [and63 (hI.2.2 b hb)]
    | _ :: _ :: _ :: _, h => simp at h
  · refine ⟨fun _ => ?_, fun he => by cases he⟩
    match l, hlen with
    | [], _ => exact ⟨0, hI.1, 0, hI.1, Or.inr (by simp [mop])⟩
    | [a], _ =>
      have ha := hmem a (by simp)
      exact ⟨a, ha, a, ha, Or.inr (by simp [mop])⟩
    | [a, b], _ =>
      have ha := hmem a (by simp)
      have hb := hmem b (by simp)
      exact ⟨a, ha, b, hb, Or.inr (by simp [mop])⟩
    | _ :: _ :: _ :: _, h => simp at h
  · refine ⟨fun hne => absurd rfl hne, fun _ => ?_⟩
    cases l with
    | nil => exact ⟨0, hI.1, by simp [mop]⟩
    | cons a l => exact ⟨a, hmem a (by simp), by simp [mop]⟩

theorem members_mem {S : ℕ} {L : List ℕ} (hr : Rel S L) (hI : Inv L) {a : ℕ} (ha : a ∈ L) :
    a ∈ members S := by
  simp only [members, List.mem_filter, List.mem_range]
  exact ⟨hI.2.2 a ha, (hr a).mpr ha⟩

theorem sound : ∀ (gs : List Gate), OpOk gs → ∀ (L : List ℕ) (S k n : ℕ), Rel S L → Inv L →
    gs.length ≤ k → notcnt gs ≤ n → coveredL (mw gs L) → bad k n S = true := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  intro gs
  induction gs with
  | nil =>
    intro _ L S k n hr _ _ _ hc
    have hcS : covered S = true := by
      simp only [covered, List.all_eq_true]
      intro t ht
      exact (hr t).mpr (hc t ht)
    cases k with
    | zero => simpa [bad] using hcS
    | succ k => simp [bad, hcS]
  | cons g gs ih =>
    intro hok L S k n hr hI hk hn hc
    have hg := hok g (by simp)
    have hrest : OpOk gs := fun g' hg' => hok g' (by simp [hg'])
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hmem := inputs_mem hI g.inputs
    have hl2 : (g.inputs.map fun i => L.getD i 0).length ≤ 2 := by simpa using hg.2
    obtain ⟨hnn, hno⟩ := step_cases hI g.op hg.1 _ hmem hl2
    generalize hvdef : mop g.op (g.inputs.map fun i => L.getD i 0) = v at hnn hno
    have hvlt : v < 64 := by
      rw [← hvdef]; exact mop_lt _ _ (fun a ha => hI.2.2 a (hmem a ha))
    have hI' : Inv (L ++ [v]) := ⟨by simp [hI.1], by simp [hI.2.1],
      fun a ha => by
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | ha
        · exact hI.2.2 a ha
        · rw [ha]; exact hvlt⟩
    have hr' := rel_add hr v
    have hc' : coveredL (mw gs (L ++ [v])) := by
      have e : mw (g :: gs) L = mw gs (L ++ [mop g.op (g.inputs.map fun i => L.getD i 0)]) := rfl
      rw [e, hvdef] at hc; exact hc
    have hlen : gs.length ≤ k := by simp at hk; omega
    have hnc : notcnt (g :: gs) = (if g.op = GateOp.not then 1 else 0) + notcnt gs := by
      by_cases h : g.op = GateOp.not
      · simp [notcnt, List.filter_cons, h]; omega
      · simp [notcnt, List.filter_cons, h]
    obtain ⟨A, hA, hAl⟩ := mw_append gs (L ++ [v])
    have hmiss : missing (add S v) ≤ k := by
      have := missing_le hr' (by rw [← hA]; exact hc')
      omega
    by_cases hvS : mem S v = true
    · have hsame : add S v = S := add_self hvS
      have hn' : notcnt gs ≤ n := by rw [hnc] at hn; split at hn <;> omega
      have := ih hrest (L ++ [v]) (add S v) k n hr' hI' hlen hn' hc'
      rw [hsame] at this
      exact bad_mono' (by omega) le_rfl this
    · have hvS' : mem S v = false := by simpa using hvS
      by_cases hnot : g.op = GateOp.not
      · obtain ⟨a, ha, hva⟩ := hno hnot
        have hn1 : 1 + notcnt gs ≤ n := by rw [hnc, if_pos hnot] at hn; exact hn
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hb := ih hrest (L ++ [v]) (add S v) k n' hr' hI' hlen (by omega) hc'
        rw [hva] at hb hmiss hvS'
        simp only [bad, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr ⟨a, members_mem hr hI ha, by simp [hvS', hmiss, hb]⟩)
      · obtain ⟨a, ha, b, hb, hab⟩ := hnn hnot
        have hn' : notcnt gs ≤ n := by rw [hnc, if_neg hnot] at hn; omega
        have hb' := ih hrest (L ++ [v]) (add S v) k n hr' hI' hlen hn' hc'
        have hvc : v ∈ cands S := by
          simp only [cands, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
          exact ⟨a, members_mem hr hI ha, b, members_mem hr hI hb, hab⟩
        simp only [bad, Bool.or_eq_true]
        exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨v, hvc, by simp [hvS', hmiss, hb']⟩))

theorem rel0 : Rel S0 m0 := by
  intro v
  simp only [mem]
  by_cases hv : v < 64
  · interval_cases v <;> decide
  · have : S0.testBit v = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : S0 < 2 ^ 64)
      (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this]
    simp only [Bool.false_eq_true, false_iff, m0, List.mem_cons, List.mem_nil_iff, or_false]
    omega

theorem inv0 : Inv m0 := ⟨by decide, by decide, by decide⟩

theorem bits0 (t : ℕ) (ht : t < 6) : ∀ i, (xs t).getD i false = (m0.getD i 0).testBit t := by
  intro i
  by_cases hi : i < 7
  · interval_cases i <;> interval_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp [xs]; omega), List.getD_eq_default _ _ (by simp [m0]; omega)]
    simp

theorem eq_of_bits {x c : ℕ} (hx : x < 64) (hc : c < 64) (h : ∀ t < 6, x.testBit t = c.testBit t) : x = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h i hi
  · have hp : 64 ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 6 ≤ i by omega); simpa using this
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hp), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc hp)]

theorem mw_inv : ∀ (gs : List Gate) (L : List ℕ), Inv L → Inv (mw gs L) := by
  intro gs
  induction gs with
  | nil => intro L h; simpa [mw] using h
  | cons g gs ih =>
    intro L hI
    have hvlt := mop_lt g.op (g.inputs.map fun i => L.getD i 0) (fun a ha => hI.2.2 a (inputs_mem hI _ a ha))
    have h' := ih (L ++ [mop g.op (g.inputs.map fun i => L.getD i 0)])
      ⟨by simp [hI.1], by simp [hI.2.1], fun a ha => by
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | ha
        · exact hI.2.2 a ha
        · rw [ha]; exact hvlt⟩
    exact h'

end PEqualNP.Outside.L_meta_51096

open PEqualNP.Outside.L_meta_51096 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_51096 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (14 : Nat).testBit t.val ∧
    w.getD q.val false = (35 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hw⟩
  have hok : OpOk D.gates := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have hbits : ∀ t < 6, ∀ i, (D.wires (xs t)).getD i false = ((mw D.gates m0).getD i 0).testBit t :=
    fun t ht => wires_bits t ht D.gates hok (xs t) m0 (by simp [xs, m0]) (bits0 t ht)
  have hI := mw_inv D.gates m0 inv0
  have val : ∀ (i c : ℕ), c < 64 → c ≠ 0 →
      (∀ t < 6, (D.wires (xs t)).getD i false = c.testBit t) → c ∈ mw D.gates m0 := by
    intro i c hc hc0 h
    have hlt : (mw D.gates m0).getD i 0 < 64 := by
      rcases getD_mem_or (mw D.gates m0) i with h' | h'
      · exact hI.2.2 _ h'
      · rw [h']; decide
    have heq : (mw D.gates m0).getD i 0 = c :=
      eq_of_bits hlt hc (fun t ht => by rw [← hbits t ht i]; exact h t ht)
    rcases getD_mem_or (mw D.gates m0) i with h' | h'
    · rw [← heq]; exact h'
    · exact absurd (heq ▸ h') hc0
  have h14 : 14 ∈ mw D.gates m0 := val p.val 14 (by decide) (by decide) (fun t ht => (hw ⟨t, ht⟩).1)
  have h35 : 35 ∈ mw D.gates m0 := val q.val 35 (by decide) (by decide) (fun t ht => (hw ⟨t, ht⟩).2.1)
  have h40 : 40 ∈ mw D.gates m0 := val r.val 40 (by decide) (by decide) (fun t ht => (hw ⟨t, ht⟩).2.2)
  have hcov : coveredL (mw D.gates m0) := by
    intro t ht
    simp only [tg, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact h14
    · exact h35
    · exact h40
  have hb := sound D.gates hok m0 S0 5 2 rel0 inv0 hsize hnot hcov
  have := search_fails 5 le_rfl 2 le_rfl
  rw [this] at hb
  exact absurd hb (by decide)
