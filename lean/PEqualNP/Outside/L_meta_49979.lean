import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49979

open PEqualNP.CircuitLowerBounds


def enc (b : Fin 5 → Bool) : ℕ :=
  (b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat + 8 * (b 3).toNat + 16 * (b 4).toNat

lemma enc_lt (b : Fin 5 → Bool) : enc b < 32 := by
  have key : ∀ a0 a1 a2 a3 a4 : Bool,
      a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat + 16 * a4.toNat < 32 := by decide
  exact key _ _ _ _ _

lemma enc_and (a b : Fin 5 → Bool) : enc (fun t => a t && b t) = enc a &&& enc b := by
  have key : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      (a0 && b0).toNat + 2 * (a1 && b1).toNat + 4 * (a2 && b2).toNat + 8 * (a3 && b3).toNat
        + 16 * (a4 && b4).toNat =
      (a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat + 16 * a4.toNat) &&&
      (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat) := by decide
  exact key _ _ _ _ _ _ _ _ _ _

lemma enc_or (a b : Fin 5 → Bool) : enc (fun t => a t || b t) = enc a ||| enc b := by
  have key : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      (a0 || b0).toNat + 2 * (a1 || b1).toNat + 4 * (a2 || b2).toNat + 8 * (a3 || b3).toNat
        + 16 * (a4 || b4).toNat =
      (a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat + 16 * a4.toNat) |||
      (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat) := by decide
  exact key _ _ _ _ _ _ _ _ _ _

lemma enc_not (a : Fin 5 → Bool) : enc (fun t => !a t) = 31 ^^^ enc a := by
  have key : ∀ a0 a1 a2 a3 a4 : Bool,
      (!a0).toNat + 2 * (!a1).toNat + 4 * (!a2).toNat + 8 * (!a3).toNat + 16 * (!a4).toNat =
      31 ^^^ (a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat + 16 * a4.toNat) := by decide
  exact key _ _ _ _ _

lemma foldl_or_testBit (f : ℕ → ℕ) (l : List ℕ) (init v : ℕ) :
    (l.foldl (fun acc a => acc ||| f a) init).testBit v =
      (init.testBit v || l.any (fun a => (f a).testBit v)) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [List.foldl, ih, Nat.testBit_or, Bool.or_assoc]

def aoRow (S a : ℕ) : ℕ :=
  if S.testBit a then
    (List.range 32).foldl (fun acc b =>
      acc ||| (if S.testBit b then 2 ^ (a &&& b) ||| 2 ^ (a ||| b) else 0)) 0
  else 0

def ao (S : ℕ) : ℕ := (List.range 32).foldl (fun acc a => acc ||| aoRow S a) (2 ^ 0 ||| 2 ^ 31)

def nt (S : ℕ) : ℕ :=
  (List.range 32).foldl (fun acc a => acc ||| (if S.testBit a then 2 ^ (31 ^^^ a) else 0)) (2 ^ 31)

lemma ao_pair (S a b : ℕ) (ha : a < 32) (hb : b < 32) (hSa : S.testBit a = true)
    (hSb : S.testBit b = true) :
    (ao S).testBit (a &&& b) = true ∧ (ao S).testBit (a ||| b) = true := by
  have row : ∀ v, (v = a &&& b ∨ v = a ||| b) → (aoRow S a).testBit v = true := by
    intro v hv
    rw [aoRow, if_pos hSa, foldl_or_testBit]
    simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range]
    refine ⟨b, hb, ?_⟩
    rw [if_pos hSb, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
    rcases hv with rfl | rfl <;> simp
  constructor <;>
  · rw [ao, foldl_or_testBit]
    simp only [List.any_eq_true, List.mem_range, Bool.or_eq_true]
    exact Or.inr ⟨a, ha, row _ (by simp)⟩

lemma ao_const (S : ℕ) : (ao S).testBit 0 = true ∧ (ao S).testBit 31 = true := by
  constructor <;>
  · rw [ao, foldl_or_testBit]
    simp only [Bool.or_eq_true]
    exact Or.inl (by decide)

lemma nt_not (S a : ℕ) (ha : a < 32) (hSa : S.testBit a = true) :
    (nt S).testBit (31 ^^^ a) = true := by
  rw [nt, foldl_or_testBit]
  simp only [List.any_eq_true, List.mem_range, Bool.or_eq_true]
  exact Or.inr ⟨a, ha, by rw [if_pos hSa, Nat.testBit_two_pow]; simp⟩

lemma nt_const (S : ℕ) : (nt S).testBit 31 = true := by
  rw [nt, foldl_or_testBit]
  simp only [Bool.or_eq_true]
  exact Or.inl (by decide)

def notcov (S : ℕ) : Bool := !(S.testBit 6 && S.testBit 18 && S.testBit 26)

def check : ℕ → ℕ → ℕ → Bool
  | 0, _, S => notcov S
  | k + 1, m, S => notcov S && (List.range 32).all (fun v => S.testBit v ||
      ((!(ao S).testBit v || check k m (S ||| 2 ^ v)) &&
       (!(nt S).testBit v || m == 0 || check k (m - 1) (S ||| 2 ^ v))))

lemma check_notcov (k m S : ℕ) (h : check k m S = true) : notcov S = true := by
  cases k with
  | zero => exact h
  | succ k => simp only [check, Bool.and_eq_true] at h; exact h.1

def S0 : ℕ := 2 ^ 0 + 2 ^ 16 + 2 ^ 24 + 2 ^ 28 + 2 ^ 30 + 2 ^ 31

lemma check_ok : check 5 2 S0 = true := by decide +kernel

def stepRow (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def vecAt (R : Fin 5 → List Bool) (i : ℕ) : ℕ := enc (fun t => (R t).getD i false)

def Inv (S : ℕ) (R : Fin 5 → List Bool) (L : ℕ) : Prop :=
  (∀ t, (R t).length = L) ∧ ∀ i < L, S.testBit (vecAt R i) = true

def RB : ℕ → List Gate → Prop
  | _, [] => True
  | L, g :: gs => (∀ i ∈ g.inputs, i < L) ∧ RB (L + 1) gs

def FI (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def nc (gs : List Gate) : ℕ := (gs.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)).length

def newv (R : Fin 5 → List Bool) (g : Gate) : ℕ :=
  enc (fun t => g.op.eval (g.inputs.map fun i => (R t).getD i false))

lemma newvec (S : ℕ) (R : Fin 5 → List Bool) (L : ℕ) (g : Gate) (hI : Inv S R L) (hg : FI g)
    (hr : ∀ i ∈ g.inputs, i < L) :
    S.testBit (newv R g) = true ∨ (g.op ≠ GateOp.not ∧ (ao S).testBit (newv R g) = true) ∨
      (g.op = GateOp.not ∧ (nt S).testBit (newv R g) = true) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have mem : ∀ i ∈ ins, S.testBit (vecAt R i) = true := fun i hi => hI.2 i (hr i hi)
  have lt : ∀ i, vecAt R i < 32 := fun i => enc_lt _
  match ins, hlen, mem with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨by simp, by simpa [newv, GateOp.eval, enc] using (ao_const S).2⟩)
    · exact Or.inr (Or.inl ⟨by simp, by simpa [newv, GateOp.eval, enc] using (ao_const S).1⟩)
    · exact Or.inr (Or.inr ⟨rfl, by simpa [newv, GateOp.eval, enc] using nt_const S⟩)
  | [i], _, mem =>
    have hi := mem i (by simp)
    rcases hop with rfl | rfl | rfl
    · exact Or.inl (by simpa [newv, GateOp.eval, vecAt] using hi)
    · exact Or.inl (by simpa [newv, GateOp.eval, vecAt] using hi)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      have e : newv R ⟨GateOp.not, [i]⟩ = 31 ^^^ vecAt R i := by
        simp only [newv, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
        exact enc_not _
      rw [e]; exact nt_not S _ (lt i) hi
  | [i, j], _, mem =>
    have hi := mem i (by simp)
    have hj := mem j (by simp)
    rcases hop with rfl | rfl | rfl
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have e : newv R ⟨GateOp.and, [i, j]⟩ = vecAt R i &&& vecAt R j := by
        have : (fun t => GateOp.and.eval ([i, j].map fun k => (R t).getD k false)) =
            fun t => (R t).getD i false && (R t).getD j false := by
          funext t; simp [GateOp.eval]
        simp only [newv]; rw [this]; exact enc_and _ _
      rw [e]; exact (ao_pair S _ _ (lt i) (lt j) hi hj).1
    · refine Or.inr (Or.inl ⟨by simp, ?_⟩)
      have e : newv R ⟨GateOp.or, [i, j]⟩ = vecAt R i ||| vecAt R j := by
        have : (fun t => GateOp.or.eval ([i, j].map fun k => (R t).getD k false)) =
            fun t => (R t).getD i false || (R t).getD j false := by
          funext t; simp [GateOp.eval]
        simp only [newv]; rw [this]; exact enc_or _ _
      rw [e]; exact (ao_pair S _ _ (lt i) (lt j) hi hj).2
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      have e : newv R ⟨GateOp.not, [i, j]⟩ = 31 ^^^ vecAt R i := by
        simp only [newv, GateOp.eval, List.map_cons, List.headD_cons]
        exact enc_not _
      rw [e]; exact nt_not S _ (lt i) hi
  | _ :: _ :: _ :: _, h, _ => simp at h

lemma inv_step (S S' : ℕ) (R : Fin 5 → List Bool) (L : ℕ) (g : Gate) (hI : Inv S R L)
    (hmono : ∀ x, S.testBit x = true → S'.testBit x = true)
    (hnew : S'.testBit (newv R g) = true) :
    Inv S' (fun t => stepRow (R t) g) (L + 1) := by
  refine ⟨fun t => by simp [stepRow, hI.1 t], fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have e : vecAt (fun t => stepRow (R t) g) i = vecAt R i := by
      simp only [vecAt, stepRow]
      congr 1; funext t
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hI.1 t]; exact hi),
        ← List.getD_eq_getElem?_getD]
    rw [e]; exact hmono _ (hI.2 i hi)
  · have e : vecAt (fun t => stepRow (R t) g) i = newv R g := by
      simp only [vecAt, stepRow, newv]
      congr 1; funext t
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hI.1 t])]
      simp [hI.1 t]
    rw [e]; exact hnew

theorem main (gs : List Gate) : ∀ (k m S L : ℕ) (R : Fin 5 → List Bool),
    check k m S = true → Inv S R L → (∀ g ∈ gs, FI g) → RB L gs → nc gs ≤ m →
    gs.length ≤ k → ∀ p q r, p < L + gs.length → q < L + gs.length → r < L + gs.length →
    vecAt (fun t => gs.foldl stepRow (R t)) p = 6 →
    vecAt (fun t => gs.foldl stepRow (R t)) q = 18 →
    vecAt (fun t => gs.foldl stepRow (R t)) r = 26 → False := by
  induction gs with
  | nil =>
    intro k m S L R hc hI _ _ _ _ p q r hp hq hr ep eq er
    have h6 := hI.2 p (by simpa using hp)
    have h18 := hI.2 q (by simpa using hq)
    have h26 := hI.2 r (by simpa using hr)
    simp only [List.foldl_nil] at ep eq er
    rw [ep] at h6; rw [eq] at h18; rw [er] at h26
    have := check_notcov k m S hc
    simp [notcov, h6, h18, h26] at this
  | cons g gs ih =>
    intro k m S L R hc hI hfi hrb hnc hk p q r hp hq hr ep eq er
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hfi g (by simp)
    have hfi' : ∀ g ∈ gs, FI g := fun g' h => hfi g' (by simp [h])
    have hv := newvec S R L g hI hg hrb.1
    simp only [List.length_cons] at hp hq hr hk
    simp only [List.foldl_cons] at ep eq er
    have hp' : p < (L + 1) + gs.length := by omega
    have hq' : q < (L + 1) + gs.length := by omega
    have hr' : r < (L + 1) + gs.length := by omega
    have hnc1 : g.op = GateOp.not → nc (g :: gs) = nc gs + 1 := fun h => by
      simp [nc, List.filter_cons, h]
    have hnc0 : g.op ≠ GateOp.not → nc (g :: gs) = nc gs := fun h => by
      simp [nc, List.filter_cons, h]
    have hle : nc gs ≤ m := by
      by_cases h : g.op = GateOp.not
      · rw [hnc1 h] at hnc; omega
      · rw [hnc0 h] at hnc; omega
    by_cases hS : S.testBit (newv R g) = true
    · exact ih (k + 1) m S (L + 1) (fun t => stepRow (R t) g) hc
        (inv_step S S R L g hI (fun _ h => h) hS) hfi' hrb.2 hle (by omega)
        p q r hp' hq' hr' ep eq er
    · have hS' : S.testBit (newv R g) = false := by simpa using hS
      have hlt : newv R g < 32 := enc_lt _
      have hmono : ∀ x, S.testBit x = true → (S ||| 2 ^ newv R g).testBit x = true := by
        intro x hx; simp [Nat.testBit_or, hx]
      have hnew : (S ||| 2 ^ newv R g).testBit (newv R g) = true := by
        simp [Nat.testBit_or, Nat.testBit_two_pow]
      have hI' := inv_step S _ R L g hI hmono hnew
      simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
      have hcv := hc.2 _ hlt
      simp only [hS', Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq] at hcv
      rcases hv with h | ⟨hop, hao⟩ | ⟨hop, hnt⟩
      · exact absurd h hS
      · have hc' : check k m (S ||| 2 ^ newv R g) = true := by
          rcases hcv.1 with h | h
          · rw [hao] at h; exact absurd h (by simp)
          · exact h
        exact ih k m _ (L + 1) _ hc' hI' hfi' hrb.2 hle (by omega)
          p q r hp' hq' hr' ep eq er
      · have hm : 1 ≤ m := by rw [hnc1 hop] at hnc; omega
        have hc' : check k (m - 1) (S ||| 2 ^ newv R g) = true := by
          rcases hcv.2 with (h | h) | h
          · rw [hnt] at h; exact absurd h (by simp)
          · omega
          · exact h
        exact ih k (m - 1) _ (L + 1) _ hc' hI' hfi' hrb.2 (by rw [hnc1 hop] at hnc; omega)
          (by omega) p q r hp' hq' hr' ep eq er

lemma rb_of (gs : List Gate) : ∀ L,
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) → RB L gs := by
  induction gs with
  | nil => intro L _; trivial
  | cons g gs ih =>
    intro L h
    refine ⟨fun i hi => by simpa using h 0 (by simp) i (by simpa using hi), ih (L + 1) ?_⟩
    intro j hj i hi
    have := h (j + 1) (by simp; omega) i (by simpa using hi)
    omega

def R0 (t : Fin 5) : List Bool :=
  (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]

lemma inv0 : Inv S0 R0 6 := by
  refine ⟨fun t => by simp [R0], ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_49979

theorem PEqualNP.Outside.L_meta_49979 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (18 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfi, hrb, hnc, hsz, h⟩
  open PEqualNP.Outside.L_meta_49979 in
  have key := main D.gates 5 2 S0 6 R0 check_ok inv0 hfi (rb_of D.gates 6 hrb) hnc hsz
  have hp := p.isLt; have hq := q.isLt; have hr := r.isLt
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hp hq hr
  refine key p q r hp hq hr ?_ ?_ ?_
  · have e : (fun t => (D.gates.foldl PEqualNP.Outside.L_meta_49979.stepRow
        (PEqualNP.Outside.L_meta_49979.R0 t)).getD p.val false) =
        fun t : Fin 5 => Nat.testBit 6 t.val := funext fun t => (h t).1
    unfold PEqualNP.Outside.L_meta_49979.vecAt; rw [e]; decide
  · have e : (fun t => (D.gates.foldl PEqualNP.Outside.L_meta_49979.stepRow
        (PEqualNP.Outside.L_meta_49979.R0 t)).getD q.val false) =
        fun t : Fin 5 => Nat.testBit 18 t.val := funext fun t => (h t).2.1
    unfold PEqualNP.Outside.L_meta_49979.vecAt; rw [e]; decide
  · have e : (fun t => (D.gates.foldl PEqualNP.Outside.L_meta_49979.stepRow
        (PEqualNP.Outside.L_meta_49979.R0 t)).getD r.val false) =
        fun t : Fin 5 => Nat.testBit 26 t.val := funext fun t => (h t).2.2
    unfold PEqualNP.Outside.L_meta_49979.vecAt; rw [e]; decide
