import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27611
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def first : Gate := ⟨.or, [0, 4]⟩
def second : Gate := ⟨.and, [0, 2]⟩

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beforeTail (x : Fin 9 → Bool) : List Bool := step (step (List.ofFn x) first) second

def yes (i j : Fin 9) : Bool :=
  ([177, 98, 84, 140, 85, 98, 84, 140, 266] : List ℕ).getD i.val 0 |>.testBit j.val

def no (i j : Fin 9) : Bool := if j = i then false else yes i j

theorem separates : ∀ i : Fin 9, matching (yes i) = true ∧ matching (no i) = false := by
  decide +kernel

theorem prefixAgree : ∀ (i : Fin 9) (j : Fin 11), j.val ≠ i.val →
    (beforeTail (yes i)).getD j.val false = (beforeTail (no i)).getD j.val false := by
  decide +kernel

theorem beforeLen (x : Fin 9 → Bool) : (beforeTail x).length = 11 := by
  simp [beforeTail, step]

theorem agreeAll (i : Fin 9) (j : ℕ) (hne : j ≠ i.val) :
    (beforeTail (yes i)).getD j false = (beforeTail (no i)).getD j false := by
  by_cases hj : j < 11
  · exact prefixAgree i ⟨j, hj⟩ hne
  · simp [List.getD_eq_getElem?_getD, beforeLen, Nat.le_of_not_gt hj]

theorem agreeRun (gs : List Gate) (i : ℕ) (havoid : i ∉ gs.flatMap Gate.inputs)
    (u v : List Bool) (hlen : u.length = v.length)
    (hag : ∀ j, j ≠ i → u.getD j false = v.getD j false) :
    ∀ j, j ≠ i → (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing u v with
  | nil => exact hag
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at havoid
    change ∀ j, j ≠ i → (gs.foldl step (step u g)).getD j false =
      (gs.foldl step (step v g)).getD j false
    apply ih havoid.2 _ _ (by simp [step, hlen])
    have hm : (g.inputs.map fun j => u.getD j false) = (g.inputs.map fun j => v.getD j false) :=
      List.map_congr_left (fun j hj => hag j (fun e => havoid.1 (e ▸ hj)))
    intro j hj
    unfold step
    rw [hm]
    by_cases hj' : j < u.length
    · have hv : j < v.length := hlen ▸ hj'
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj',
        List.getElem?_append_left hv] using hag j hj
    · have hu : u.length ≤ j := Nat.le_of_not_gt hj'
      have hv : v.length ≤ j := hlen ▸ hu
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hu,
        List.getElem?_append_right hv, hlen]

theorem allInputReads (gs : List Gate) (o : ℕ) (ho : 9 ≤ o)
    (he : ∀ x, (Circuit.mk (first :: second :: gs) o).eval (List.ofFn x) = matching x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra ha
  have hs := agreeRun gs i.val ha (beforeTail (yes i)) (beforeTail (no i))
    (by rw [beforeLen, beforeLen]) (agreeAll i) o (by have := i.isLt; omega)
  change (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (yes i)) =
    (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (no i)) at hs
  rw [he, he, (separates i).1, (separates i).2] at hs
  contradiction

theorem allGateReads (gs : List Gate)
    (hlive : ∀ j : Fin (first :: second :: gs).length, j.val + 1 < (first :: second :: gs).length →
      ∃ k : Fin (first :: second :: gs).length, j.val < k.val ∧
        9 + j.val ∈ ((first :: second :: gs).get k).inputs)
    (j : ℕ) (hj : j + 1 < (first :: second :: gs).length) :
    9 + j ∈ gs.flatMap Gate.inputs := by
  obtain ⟨⟨k, hk⟩, hjk, hm⟩ := hlive ⟨j, by omega⟩ hj
  change j < k at hjk
  change 9 + j ∈ ((first :: second :: gs).get ⟨k, hk⟩).inputs at hm
  rcases k with _ | _ | k
  · omega
  · change 9 + j ∈ [0, 2] at hm
    simp at hm
    omega
  · have klt : k < gs.length := by simp at hk; omega
    exact List.mem_flatMap.mpr ⟨gs[k], List.getElem_mem klt, hm⟩

theorem sumInputs (gs : List Gate) (hs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hs g (by simp)
    have ht := ih (fun g hg => hs g (by simp [hg]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_27611

namespace PEqualNP.Outside.L_meta_27611

open PEqualNP.CircuitLowerBounds (Gate)
open scoped BigOperators

theorem nodup_and_toFinset_eq_of_card {α : Type*} [DecidableEq α] {xs : List α}
    {s : Finset α} (hcover : s ⊆ xs.toFinset) (hlen : xs.length ≤ s.card) :
    xs.Nodup ∧ xs.toFinset = s := by
  have hcard : xs.toFinset.card ≤ xs.length := List.toFinset_card_le xs
  have heq : s = xs.toFinset := Finset.eq_of_subset_of_card_le hcover (hcard.trans hlen)
  have hlength : xs.toFinset.card = xs.length :=
    le_antisymm hcard (hlen.trans (Finset.card_le_card hcover))
  exact ⟨List.nodup_iff_length_dedup_eq.mpr
    (by simpa only [List.card_toFinset] using hlength), heq.symm⟩

private theorem sum_flatMap_inputs (gs : List Gate) (w : ℕ → ℕ) :
    ((gs.flatMap Gate.inputs).map w).sum = (gs.map fun g => (g.inputs.map w).sum).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

theorem weight_bound (gs : List Gate) (o : ℕ) (w : ℕ → ℕ)
    (hflat : (gs.flatMap Gate.inputs).Nodup)
    (hcover : (gs.flatMap Gate.inputs).toFinset = Finset.range o)
    (hout : o = 11 + gs.length - 1) (hn : 0 < gs.length)
    (hgate : ∀ j : Fin gs.length, w (11 + j.val) ≤ ((gs.get j).inputs.map w).sum) :
    w o ≤ Finset.sum (Finset.range 11) w := by
  have hsum : (∑ j : Fin gs.length, w (11 + j.val)) ≤ ∑ i ∈ Finset.range o, w i := by
    calc
      _ ≤ ∑ j : Fin gs.length, ((gs.get j).inputs.map w).sum :=
        Finset.sum_le_sum (fun j _ => hgate j)
      _ = ((gs.flatMap Gate.inputs).map w).sum := by
        rw [sum_flatMap_inputs]
        exact Fin.sum_univ_fun_getElem gs (fun g => (g.inputs.map w).sum)
      _ = ∑ i ∈ Finset.range o, w i := by
        rw [← List.sum_toFinset w hflat, hcover]
  have ho : o + 1 = 11 + gs.length := by omega
  have hsplit :
      (∑ i ∈ Finset.range o, w i) + w o =
        (∑ i ∈ Finset.range 11, w i) + ∑ j : Fin gs.length, w (11 + j.val) := by
    calc
      _ = ∑ i ∈ Finset.range (o + 1), w i := (Finset.sum_range_succ w o).symm
      _ = ∑ i ∈ Finset.range (11 + gs.length), w i := by rw [ho]
      _ = _ := by
        rw [Finset.sum_range_add w 11 gs.length,
          Finset.sum_range (n := gs.length) (fun j => w (11 + j))]
  have h : w o ≤ ∑ i ∈ Finset.range 11, w i := by omega
  exact h

end PEqualNP.Outside.L_meta_27611

namespace PEqualNP.Outside.L_meta_27611

private abbrev ScoreRow := Bool × Bool × Bool × Bool

private def classifyScoreRow : ScoreRow → Option (Fin 6)
  | (false, false, false, false) => some 0
  | (true, true, true, true) => some 1
  | (false, true, false, true) => some 2
  | (false, false, true, true) => some 3
  | (false, false, false, true) => some 4
  | (false, true, true, true) => some 5
  | _ => none

private def decodeScoreRow (i : Fin 6) : ScoreRow :=
  match i.val with
  | 0 => (false, false, false, false)
  | 1 => (true, true, true, true)
  | 2 => (false, true, false, true)
  | 3 => (false, false, true, true)
  | 4 => (false, false, false, true)
  | _ => (false, true, true, true)

private theorem decode_classifyScoreRow (r : ScoreRow) (i : Fin 6)
    (h : classifyScoreRow r = some i) : decodeScoreRow i = r := by
  rcases r with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | have hi := Option.some.inj h
      subst i
      rfl
    | simp [classifyScoreRow] at h

private def scoreCodes (a b : Fin 6) : ℕ :=
  if a < 2 ∧ b < 2 then 0
  else if ((a < 2 ∨ a = 2) ∧ (b < 2 ∨ b = 2)) ∨
          ((a < 2 ∨ a = 3) ∧ (b < 2 ∨ b = 3)) then 1
  else if (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then 3
  else 2

private def scoreRows (a b : ScoreRow) : ℕ :=
  match classifyScoreRow a, classifyScoreRow b with
  | some i, some j => scoreCodes i j
  | _, _ => 3

private def scoreRow₀ (s : Fin 8 → Bool) : ScoreRow := (s 0, s 1, s 2, s 3)
private def scoreRow₁ (s : Fin 8 → Bool) : ScoreRow := (s 4, s 5, s 6, s 7)

def score (s : Fin 8 → Bool) : ℕ := scoreRows (scoreRow₀ s) (scoreRow₁ s)

private def scoreRowGate (isOr : Bool) (a b : ScoreRow) : ScoreRow :=
  let g := if isOr then Bool.or else Bool.and
  (g a.1 b.1, g a.2.1 b.2.1, g a.2.2.1 b.2.2.1, g a.2.2.2 b.2.2.2)

private theorem scoreRows_le_three (a b : ScoreRow) : scoreRows a b ≤ 3 := by
  unfold scoreRows
  split <;> (try unfold scoreCodes) <;> (try split_ifs) <;> decide

private theorem decoded_of_scoreRows_ne_three (a b : ScoreRow) (h : scoreRows a b ≠ 3) :
    ∃ i j : Fin 6, a = decodeScoreRow i ∧ b = decodeScoreRow j := by
  cases ha : classifyScoreRow a <;> cases hb : classifyScoreRow b
  · exact (h (by simp [scoreRows, ha, hb])).elim
  · exact (h (by simp [scoreRows, ha, hb])).elim
  · exact (h (by simp [scoreRows, ha, hb])).elim
  · exact ⟨_, _, (decode_classifyScoreRow a _ ha).symm, (decode_classifyScoreRow b _ hb).symm⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem scoreRows_gate_decoded :
    ∀ (isOr : Bool) (a₀ a₁ b₀ b₁ : Fin 6),
      scoreRows (scoreRowGate isOr (decodeScoreRow a₀) (decodeScoreRow b₀))
                (scoreRowGate isOr (decodeScoreRow a₁) (decodeScoreRow b₁)) ≤
      scoreRows (decodeScoreRow a₀) (decodeScoreRow a₁) +
      scoreRows (decodeScoreRow b₀) (decodeScoreRow b₁) := by
  decide +kernel

private theorem scoreRows_gate (isOr : Bool) (a₀ a₁ b₀ b₁ : ScoreRow) :
    scoreRows (scoreRowGate isOr a₀ b₀) (scoreRowGate isOr a₁ b₁) ≤
      scoreRows a₀ a₁ + scoreRows b₀ b₁ := by
  by_cases h : 3 ≤ scoreRows a₀ a₁ + scoreRows b₀ b₁
  · exact (scoreRows_le_three _ _).trans h
  have ha : scoreRows a₀ a₁ ≠ 3 := by omega
  have hb : scoreRows b₀ b₁ ≠ 3 := by omega
  obtain ⟨i, j, rfl, rfl⟩ := decoded_of_scoreRows_ne_three a₀ a₁ ha
  obtain ⟨k, l, rfl, rfl⟩ := decoded_of_scoreRows_ne_three b₀ b₁ hb
  exact scoreRows_gate_decoded isOr i j k l

theorem score_and (a b : Fin 8 → Bool) :
    score (fun i => a i && b i) ≤ score a + score b := by
  exact scoreRows_gate false (scoreRow₀ a) (scoreRow₁ a) (scoreRow₀ b) (scoreRow₁ b)

theorem score_or (a b : Fin 8 → Bool) :
    score (fun i => a i || b i) ≤ score a + score b := by
  exact scoreRows_gate true (scoreRow₀ a) (scoreRow₁ a) (scoreRow₀ b) (scoreRow₁ b)

end PEqualNP.Outside.L_meta_27611

namespace PEqualNP.Outside.L_meta_27611
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def probe (r : Fin 8) (i : Fin 9) : Bool :=
  ([5, 13, 133, 141, 295, 303, 423, 431] : List ℕ).getD r.val 0 |>.testBit i.val

def wSig (gs : List Gate) (w : ℕ) (r : Fin 8) : Bool :=
  (gs.foldl step (beforeTail (probe r))).getD w false

theorem getDAppend (w z : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ z).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = w.getD i false
    rw [ih _ (by simp [step]; omega)]
    exact getDAppend _ _ _ hi

theorem foldLen (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    change (gs.foldl step (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step]
    omega

theorem foldGate (gs : List Gate) (w : List Bool) (j : Fin gs.length)
    (hback : ∀ i ∈ (gs.get j).inputs, i < w.length + j.val) :
    (gs.foldl step w).getD (w.length + j.val) false =
      (gs.get j).op.eval ((gs.get j).inputs.map fun i => (gs.foldl step w).getD i false) := by
  let p := (gs.take j.val).foldl step w
  let g := gs.get j
  let s := gs.drop (j.val + 1)
  have hlen : p.length = w.length + j.val := by
    simp [p, foldLen]
  have hs : gs = gs.take j.val ++ g :: s := by
    simp [g, s]
  have hfold : gs.foldl step w = s.foldl step (step p g) := by
    conv_lhs => rw [hs]
    rw [List.foldl_append]
    rfl
  have hmap : (g.inputs.map fun i => (s.foldl step (step p g)).getD i false) =
      (g.inputs.map fun i => p.getD i false) := by
    apply List.map_congr_left
    intro i hi
    have hlt : i < p.length := by rw [hlen]; exact hback i hi
    rw [foldKeep _ _ _ (by simp [step]; omega)]
    exact getDAppend _ _ _ hlt
  change (gs.foldl step w).getD (w.length + j.val) false =
    g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false)
  rw [hfold, hmap, ← hlen, foldKeep _ _ _ (by simp [step])]
  simp [step, List.getD_eq_getElem?_getD]

theorem exactArity (gs : List Gate) (hs : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hs g (by simp)
    have hs' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g h => hs g (List.mem_cons_of_mem _ h)
    have htail := sumInputs gs hs'
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at he
    intro a ha
    rcases List.mem_cons.mp ha with h | h
    · subst a; omega
    · exact ih hs' (by omega) a h

theorem tailGate (gs : List Gate)
    (hform : ∀ j : Fin (first :: second :: gs).length,
      (((first :: second :: gs).get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ ((first :: second :: gs).get j).inputs = [a]) ∨
      ((((first :: second :: gs).get j).op = GateOp.and ∨
          ((first :: second :: gs).get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ ((first :: second :: gs).get j).inputs = [a, b]))
    (har : ∀ g ∈ gs, g.inputs.length = 2) (j : Fin gs.length) :
    ((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j.val ∧ (gs.get j).inputs = [a, b] := by
  let jj : Fin (first :: second :: gs).length := ⟨j.val + 2, by simp⟩
  have hget : (first :: second :: gs).get jj = gs.get j := rfl
  rcases hform jj with ⟨_, a, _, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
  · rw [hget] at hin
    have hh := har (gs.get j) (List.get_mem _ _)
    change ((gs.get j).inputs).length = 2 at hh
    rw [hin] at hh
    simp at hh
  · rw [hget] at hop hin
    exact ⟨hop, a, b, hab, by change b < 9 + (j.val + 2) at hb; omega, hin⟩

theorem wSigBefore (gs : List Gate) (i : Fin 11) :
    wSig gs i.val = fun r => (beforeTail (probe r)).getD i.val false := by
  funext r
  exact foldKeep _ _ _ (by rw [beforeLen]; exact i.isLt)

theorem probeCorrect (r : Fin 8) : matching (probe r) =
    if r.val < 4 then r.val.testBit 0 && r.val.testBit 1 else r.val.testBit 0 || r.val.testBit 1 := by
  revert r
  decide +kernel

end PEqualNP.Outside.L_meta_27611

namespace PEqualNP.Outside.L_meta_27611
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def targetSig (r : Fin 8) : Bool :=
  if r.val < 4 then r.val.testBit 0 && r.val.testBit 1 else r.val.testBit 0 || r.val.testBit 1

theorem costGate (gs : List Gate) (j : Fin gs.length)
    (h : ((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j.val ∧ (gs.get j).inputs = [a, b]) :
    score (wSig gs (11 + j.val)) ≤ ((gs.get j).inputs.map (fun i => score (wSig gs i))).sum := by
  obtain ⟨h, a, b, hab, hb, hin⟩ := h
  rw [hin]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hv (r : Fin 8) : wSig gs (11 + j.val) r = (gs.get j).op.eval [wSig gs a r, wSig gs b r] := by
    have wf := foldGate gs (beforeTail (probe r)) j (by
      intro i hi
      rw [hin] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, beforeLen] at hi ⊢
      rcases hi with rfl | rfl <;> omega)
    rw [beforeLen, hin] at wf
    exact wf
  rcases h with ha | ho
  · have eq : wSig gs (11 + j.val) = (fun r => wSig gs a r && wSig gs b r) := by
      funext r
      rw [hv, ha]
      simp [GateOp.eval]
    rw [eq]
    exact score_and _ _
  · have eq : wSig gs (11 + j.val) = (fun r => wSig gs a r || wSig gs b r) := by
      funext r
      rw [hv, ho]
      simp [GateOp.eval]
    rw [eq]
    exact score_or _ _

theorem initialCost : ((List.range 11).map (fun i => score (fun r =>
    (beforeTail (probe r)).getD i false))).sum = 2 := by
  decide +kernel

theorem targetCost : score targetSig = 3 := by decide +kernel

theorem contradictC (C : Circuit) (hfan : FanInTwo C) (hs : C.size ≤ 12)
    (he : ∀ x, C.eval (List.ofFn x) = matching x)
    (ho : C.output + 1 = 9 + C.size)
    (hform : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hh : C.gates.head? = some first) (ht : C.gates.tail.head? = some second) : False := by
  rcases C with ⟨_ | ⟨g, _ | ⟨h, gs⟩⟩, o⟩
  · simp at hh
  · simp at ht
  · simp only [List.head?_cons, Option.some.injEq] at hh
    change some h = some second at ht
    have ht' := Option.some.inj ht
    subst g; subst h
    change (first :: second :: gs).length ≤ 12 at hs
    change o + 1 = 9 + (first :: second :: gs).length at ho
    simp only [List.length_cons] at hs ho
    have hout : 9 ≤ o := by omega
    have hfan' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hg => (hfan g (by simp [hg])).2
    let reads := gs.flatMap Gate.inputs
    have hcount : reads.length ≤ 2 * gs.length := sumInputs gs hfan'
    have hall : Finset.range o ⊆ reads.toFinset := by
      intro w hw
      have hw' := Finset.mem_range.mp hw
      apply List.mem_toFinset.mpr
      by_cases h9 : w < 9
      · exact allInputReads gs o hout he ⟨w, h9⟩
      · have hj : (w - 9) + 1 < (first :: second :: gs).length := by simp; omega
        have hv := allGateReads gs hlive (w - 9) hj
        rwa [show 9 + (w - 9) = w by omega] at hv
    have hc := Finset.card_le_card hall
    rw [Finset.card_range] at hc
    have hlist : reads.toFinset.card ≤ reads.length := List.toFinset_card_le _
    have hlen : gs.length = 10 := by omega
    have hreads := nodup_and_toFinset_eq_of_card hall (by rw [Finset.card_range]; omega)
    have har := exactArity gs hfan' (by change reads.length = _; omega)
    have hbnd := weight_bound gs o (fun i => score (wSig gs i)) hreads.1 hreads.2
      (by omega) (by omega) (fun j => costGate gs j (tailGate gs hform har j))
    have hin : Finset.sum (Finset.range 11) (fun i => score (wSig gs i)) = 2 := by
      rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
      rw [← initialCost]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact congrArg score (wSigBefore gs ⟨i, List.mem_range.mp hi⟩)
    have heq : wSig gs o = targetSig := by
      funext r
      show (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (probe r)) = targetSig r
      exact (he (probe r)).trans (probeCorrect r)
    rw [heq, targetCost, hin] at hbnd
    omega

end PEqualNP.Outside.L_meta_27611

theorem PEqualNP.Outside.L_meta_27611 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩)) := by
  rintro ⟨C, hfan, hs, he, ho, hf, _, hl, hh, ht⟩
  exact L_meta_27611.contradictC C hfan hs he ho hf hl hh ht
