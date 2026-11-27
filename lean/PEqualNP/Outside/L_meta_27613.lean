import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27613
open PEqualNP.CircuitLowerBounds

def pack8 (f : Fin 8 → Bool) : Nat := (BitVec.ofBoolListLE (List.ofFn f)).toNat

theorem pack8_bit (f : Fin 8 → Bool) (i : Nat) :
    (pack8 f).testBit i = (List.ofFn f).getD i false := by
  exact BitVec.getLsbD_ofBoolListLE

private theorem pack8_value (f : Fin 8 → Bool) (i : Nat) :
    (pack8 f).testBit i = (if h : i < 8 then f ⟨i, h⟩ else false) := by
  by_cases hi : i < 8
  · simp only [pack8_bit, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some]
  · simp only [pack8_bit, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi,
      Option.getD_none]

theorem pack8_and (f g : Fin 8 → Bool) :
    pack8 (fun r => f r && g r) = pack8 f &&& pack8 g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · simp only [pack8_value, dite_eq_left hi]
  · simp only [pack8_value, dite_eq_right hi, Bool.false_and]

theorem pack8_or (f g : Fin 8 → Bool) :
    pack8 (fun r => f r || g r) = pack8 f ||| pack8 g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 8
  · simp only [pack8_value, dite_eq_left hi]
  · simp only [pack8_value, dite_eq_right hi, Bool.false_or]

private def cheapColumns : List Nat :=
  [0x00, 0xFF, 0xAA, 0xCC, 0xF0, 0x88, 0xA0, 0xC0, 0xEE, 0xFA, 0xFC,
   0x80, 0xFE, 0xEA, 0xEC, 0xF8, 0xA8, 0xC8, 0xE0]

def weight (x : Nat) : Nat :=
  if x ∈ cheapColumns then
    if x ∈ [0x00, 0xFF] then 0 else
    if x ∈ [0xAA, 0xCC, 0xF0] then 1 else
    if x ∈ [0x88, 0xA0, 0xC0, 0xEE, 0xFA, 0xFC] then 2 else 3
  else 5

theorem weight_bound (x : Nat) : weight x ≤ 5 := by
  unfold weight
  split
  · split
    · decide
    · split
      · decide
      · split <;> decide
  · decide

private def tested (op : Nat → Nat → Nat) : Bool :=
  cheapColumns.all fun x => cheapColumns.all fun y =>
    decide (weight (op x y) ≤ weight x + weight y)

set_option maxHeartbeats 2000000 in
private theorem and_table : tested (fun x y => x &&& y) = true := by decide

set_option maxHeartbeats 2000000 in
private theorem or_table : tested (fun x y => x ||| y) = true := by decide

private theorem lift_table (op : Nat → Nat → Nat) (ok : tested op = true) (x y : Nat) :
    weight (op x y) ≤ weight x + weight y := by
  have hb := weight_bound (op x y)
  by_cases hx : x ∈ cheapColumns
  · by_cases hy : y ∈ cheapColumns
    · unfold tested at ok
      have row := List.all_eq_true.mp ok x hx
      exact of_decide_eq_true (List.all_eq_true.mp row y hy)
    · have h5 : weight y = 5 := by simp only [weight, ite_eq_right hy]
      omega
  · have h5 : weight x = 5 := by simp only [weight, ite_eq_right hx]
    omega

theorem weight_and (x y : Nat) : weight (x &&& y) ≤ weight x + weight y :=
  lift_table _ and_table x y

theorem weight_or (x y : Nat) : weight (x ||| y) ≤ weight x + weight y :=
  lift_table _ or_table x y

theorem weight_target : weight 0xE8 = 5 := by decide

def seedColumns : List Nat :=
  [0xFF, 0xFF, 0xFF, 0x00, 0xF0, 0xAA, 0xCC, 0xF0, 0x00, 0xFF, 0xFF]

theorem raw_budget : (seedColumns.map weight).sum = 4 := by decide

theorem gate_budget {α : Type} (gates : List α) (out : α → Nat) (ins : α → List Nat)
    (w : Nat → Nat)
    (localBound : ∀ g ∈ gates, w (out g) ≤ ((ins g).map w).sum) :
    ((gates.map out).map w).sum ≤ ((gates.flatMap ins).map w).sum := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    have hfirst := localBound g (by simp)
    have hrest := ih (fun k hk => localBound k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append_nat]
    omega

theorem wire_budget {α : Type} (gates : List α) (out : α → Nat) (ins : α → List Nat)
    (w : Nat → Nat) (sources middles : List Nat) (last : Nat)
    (outputs : gates.map out = middles ++ [last])
    (reads : (gates.flatMap ins).Perm (sources ++ middles))
    (localBound : ∀ g ∈ gates, w (out g) ≤ ((ins g).map w).sum) :
    w last ≤ (sources.map w).sum := by
  have ht := gate_budget gates out ins w localBound
  have hperm := (reads.map w).sum_nat
  rw [outputs, hperm] at ht
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero] at ht
  omega



open PEqualNP.CircuitLowerBounds

def GateSlotForm (bound : Nat) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < bound ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, a < b ∧ b < bound ∧ g.inputs = [a, b])

theorem suffix_gateForm (g0 g1 : Gate) (gs : List Gate)
    (hfull : ∀ j : Fin (g0 :: g1 :: gs).length,
      GateSlotForm (9 + j.val) ((g0 :: g1 :: gs).get j)) (j : Fin gs.length) :
    GateSlotForm (11 + j.val) (gs.get j) := by
  have h := hfull j.succ.succ
  change GateSlotForm (9 + (j.val + 1 + 1)) (gs.get j) at h
  have heq : 9 + (j.val + 1 + 1) = 11 + j.val := by omega
  rwa [heq] at h

theorem suffix_arity (gs : List Gate)
    (hform : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j)) :
    ∀ g ∈ gs, g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.get_of_mem hg
  rcases hform j with ⟨_, a, _, h⟩ | ⟨_, a, b, _, _, h⟩
  · rw [h]
    exact (by decide : (1 : Nat) ≤ 2)
  · rw [h] <;> exact Nat.le_refl 2

theorem suffix_binary (gs : List Gate)
    (hform : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j))
    (hall : ∀ g ∈ gs, g.inputs.length = 2) (j : Fin gs.length) :
    ((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 11 + j.val ∧ (gs.get j).inputs = [a, b] := by
  rcases hform j with ⟨_, a, _, h⟩ | h
  · have hlen := hall (gs.get j) (List.get_mem gs j)
    rw [h] at hlen
    change 1 = 2 at hlen
    omega
  · exact h

theorem suffix_live (g0 g1 : Gate) (gs : List Gate)
    (hfull : ∀ j : Fin (g0 :: g1 :: gs).length,
      j.val + 1 < (g0 :: g1 :: gs).length →
      ∃ k : Fin (g0 :: g1 :: gs).length,
        j.val < k.val ∧ 9 + j.val ∈ ((g0 :: g1 :: gs).get k).inputs) :
    ∀ j < gs.length, 10 + j ∈ gs.flatMap Gate.inputs := by
  intro j hj
  have hstart : j + 1 < (g0 :: g1 :: gs).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨⟨k, hk⟩, hlt, hread⟩ := hfull ⟨j + 1, hstart⟩ (by
    change j + 1 + 1 < (g0 :: g1 :: gs).length
    simp only [List.length_cons]
    omega)
  change j + 1 < k at hlt
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ t =>
      simp only [List.length_cons] at hk
      have ht : t < gs.length := by omega
      refine List.mem_flatMap.mpr ⟨gs.get ⟨t, ht⟩, List.get_mem _ _, ?_⟩
      change 9 + (j + 1) ∈ (gs.get ⟨t, ht⟩).inputs at hread
      have heq : 9 + (j + 1) = 10 + j := by omega
      rwa [heq] at hread



open PEqualNP.CircuitLowerBounds

theorem slotLengthBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length ∧
      (2 * gs.length ≤ (gs.flatMap Gate.inputs).length →
        ∀ g ∈ gs, g.inputs.length = 2) := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    have hg : g.inputs.length ≤ 2 := h g (by simp)
    obtain ⟨hbound, hfull⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    constructor
    · omega
    · intro heq z hz
      rcases List.mem_cons.mp hz with he | ht
      · subst z
        omega
      · exact hfull (by omega) z ht

theorem slotPermOfCover (rows slots : List Nat) (hn : rows.Nodup)
    (hsub : rows ⊆ slots) (hlen : slots.length ≤ rows.length) : rows.Perm slots := by
  induction rows generalizing slots with
  | nil =>
    cases slots with
    | nil => exact List.Perm.nil
    | cons x xs => simp at hlen
  | cons a t ih =>
    obtain ⟨hnot, hnt⟩ := List.nodup_cons.mp hn
    have ha : a ∈ slots := hsub List.mem_cons_self
    have hsub' : t ⊆ slots.erase a := by
      intro x hx
      have hxa : x ≠ a := fun e => hnot (e ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem a hx))
    have hlen' : (slots.erase a).length ≤ t.length := by
      rw [List.length_erase_of_mem ha]
      simp only [List.length_cons] at hlen
      omega
    exact ((ih (slots.erase a) hnt hsub' hlen').cons a).trans (List.perm_cons_erase ha).symm

theorem caseWire9 (g0 g1 : Gate) (gs : List Gate) (hunread : 9 ∉ g1.inputs)
    (huse : ∀ j : Fin (g0 :: g1 :: gs).length, j.val + 1 < (g0 :: g1 :: gs).length →
      ∃ k : Fin (g0 :: g1 :: gs).length,
        j.val < k.val ∧ 9 + j.val ∈ ((g0 :: g1 :: gs).get k).inputs) :
    9 ∈ gs.flatMap Gate.inputs := by
  have hlen : 1 < (g0 :: g1 :: gs).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨⟨k, hk⟩, hlt, hr⟩ := huse ⟨0, by omega⟩ hlen
  change 0 < k at hlt
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => exact False.elim (hunread hr)
    | succ t =>
      simp only [List.length_cons] at hk
      have ht : t < gs.length := by omega
      exact List.mem_flatMap.mpr ⟨gs.get ⟨t, ht⟩, List.get_mem _ _, hr⟩

theorem caseAllSlots (gs : List Gate) (budget : gs.length ≤ 10)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (raw : ∀ i < 9, i ∈ gs.flatMap Gate.inputs)
    (read9 : 9 ∈ gs.flatMap Gate.inputs)
    (live : ∀ j < gs.length, 10 + j ∈ gs.flatMap Gate.inputs) :
    gs.length = 10 ∧ (∀ g ∈ gs, g.inputs.length = 2) ∧
      (gs.flatMap Gate.inputs).Perm (List.range 20) := by
  let slots := gs.flatMap Gate.inputs
  let required := List.range (10 + gs.length)
  have hn : required.Nodup := List.nodup_range
  have hsub : required ⊆ slots := by
    intro i hi
    have hb := List.mem_range.mp hi
    by_cases hraw : i < 9
    · exact raw i hraw
    by_cases h9 : i = 9
    · subst i
      exact read9
    have hj := live (i - 10) (by omega)
    rwa [show 10 + (i - 10) = i by omega] at hj
  have hr : required.length = 10 + gs.length := List.length_range
  have hlow := hn.length_le_of_subset hsub
  obtain ⟨hup, hfull⟩ := slotLengthBound gs arity
  change slots.length ≤ 2 * gs.length at hup
  have hs : gs.length = 10 := by omega
  have hp := (slotPermOfCover required slots hn hsub (by omega)).symm
  refine ⟨hs, hfull ?_, ?_⟩
  · change 2 * gs.length ≤ slots.length
    omega
  · simpa only [required, hs] using hp

theorem caseMissingSlots (gs : List Gate) (missingWire : Nat) (ho : missingWire < 9) (budget : gs.length ≤ 10)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (unary : ∃ g ∈ gs, g.inputs.length < 2)
    (rawExcept : ∀ i < 9, i ≠ missingWire → i ∈ gs.flatMap Gate.inputs)
    (read9 : 9 ∈ gs.flatMap Gate.inputs)
    (live : ∀ j < gs.length, 10 + j ∈ gs.flatMap Gate.inputs) :
    gs.length = 10 ∧ (gs.flatMap Gate.inputs).Perm ((List.range 20).erase missingWire) := by
  let slots := gs.flatMap Gate.inputs
  let required := (List.range (10 + gs.length)).erase missingWire
  have hrange : (List.range (10 + gs.length)).Nodup := List.nodup_range
  have hn : required.Nodup := List.Nodup.erase missingWire hrange
  have hsub : required ⊆ slots := by
    intro i hi
    obtain ⟨hne, hin⟩ := hrange.mem_erase_iff.mp hi
    have hb := List.mem_range.mp hin
    by_cases hraw : i < 9
    · exact rawExcept i hraw hne
    by_cases h9 : i = 9
    · subst i
      exact read9
    have hj := live (i - 10) (by omega)
    rwa [show 10 + (i - 10) = i by omega] at hj
  have hom : missingWire ∈ List.range (10 + gs.length) := List.mem_range.mpr (by omega)
  have hr : required.length = 9 + gs.length := by
    rw [show required = (List.range (10 + gs.length)).erase missingWire from rfl,
        List.length_erase_of_mem hom, List.length_range]
    omega
  have hlow := hn.length_le_of_subset hsub
  obtain ⟨_, hfull⟩ := slotLengthBound gs arity
  have hstrict : slots.length < 2 * gs.length := by
    apply Nat.lt_of_not_ge
    intro hge
    obtain ⟨g, hg, hu⟩ := unary
    have htwo := hfull hge g hg
    omega
  have hs : gs.length = 10 := by omega
  have hp := (slotPermOfCover required slots hn hsub (by omega)).symm
  refine ⟨hs, ?_⟩
  simpa only [required, hs] using hp




open PEqualNP.CircuitLowerBounds

def caseMiddleWires : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19]

theorem caseFullReadSplit (gs : List Gate)
    (h : (gs.flatMap Gate.inputs).Perm (List.range 20)) :
    (gs.flatMap Gate.inputs).Perm (List.range 11 ++ caseMiddleWires) := by
  have heq : List.range 20 = List.range 11 ++ caseMiddleWires := by decide
  rw [← heq]
  exact h

theorem caseErasedReadSplit (gs : List Gate) (missingWire : Nat) (homit : missingWire = 0 ∨ missingWire = 4)
    (h : (gs.flatMap Gate.inputs).Perm ((List.range 20).erase missingWire)) :
    (gs.flatMap Gate.inputs).Perm ((List.range 11).erase missingWire ++ caseMiddleWires) := by
  have heq : (List.range 20).erase missingWire = (List.range 11).erase missingWire ++ caseMiddleWires := by
    rcases homit with rfl | rfl <;> decide
  rw [← heq]
  exact h

theorem caseOutputBudget (gs : List Gate) (s : List Nat)
    (slots : (gs.flatMap Gate.inputs).Perm (s ++ caseMiddleWires))
    (hlen : gs.length = 10) (w : Nat → Nat)
    (localBound : ∀ j : Fin gs.length, w (11 + j.val) ≤ (((gs.get j).inputs).map w).sum) :
    w 20 ≤ (s.map w).sum := by
  let idxs := List.finRange 10
  let gateAt (j : Fin 10) := gs.get ⟨j.val, by rw [hlen]; exact j.isLt⟩
  have gateList : idxs.map gateAt = gs := by
    apply List.ext_getElem
    · simp [idxs, hlen]
    · intro i h1 h2
      simp [idxs, gateAt, List.get_eq_getElem]
  have hflat : idxs.flatMap (fun j => (gateAt j).inputs) = gs.flatMap Gate.inputs := by
    calc
      _ = (idxs.map gateAt).flatMap Gate.inputs := by simp [List.flatMap_map]
      _ = _ := congrArg (List.flatMap Gate.inputs) gateList
  have reads : (idxs.flatMap fun j => (gateAt j).inputs).Perm (s ++ caseMiddleWires) := by
    rw [hflat]
    exact slots
  have produced : idxs.map (fun j => 11 + j.val) = caseMiddleWires ++ [20] := by decide
  apply wire_budget idxs (fun j => 11 + j.val) (fun j => (gateAt j).inputs)
    w s caseMiddleWires 20 produced reads
  intro j _
  exact localBound ⟨j.val, by rw [hlen]; exact j.isLt⟩


open PEqualNP.CircuitLowerBounds

def mxPM (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def mxHead (C : Circuit) (tail : List Gate) : Prop :=
  C.gates = ⟨.or,[0,4]⟩ :: ⟨.and,[0,4]⟩ :: tail

def mxCorrect (C : Circuit) : Prop := ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = mxPM x

def mxStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def mxStart (x : Fin 9 → Bool) : List Bool :=
  mxStep (mxStep (List.ofFn x) ⟨.or,[0,4]⟩) ⟨.and,[0,4]⟩

def mxPreserves (R : Bool → Bool → Prop) (g : Gate) : Prop :=
  ∀ w v : List Bool, (∀ k ∈ g.inputs, R (w.getD k false) (v.getD k false)) →
    R (g.op.eval (g.inputs.map fun k => w.getD k false))
      (g.op.eval (g.inputs.map fun k => v.getD k false))

def mxLe (x y : Bool) : Prop := x = true → y = true

theorem mxPreservesEq (g : Gate) : mxPreserves Eq g := by
  intro w v h
  exact congrArg g.op.eval (List.map_congr_left h)

theorem mxPreservesLe (g : Gate) (hop : g.op = .and ∨ g.op = .or) : mxPreserves mxLe g := by
  intro w v h
  rcases hop with hop | hop
  · intro hw
    simp only [hop, GateOp.eval, List.all_map, List.all_eq_true] at hw ⊢
    intro k hk
    exact h k hk (hw k hk)
  · intro hw
    simp only [hop, GateOp.eval, List.any_map, List.any_eq_true] at hw ⊢
    obtain ⟨k, hk, hkw⟩ := hw
    exact ⟨k, hk, h k hk hkw⟩

theorem mxAppend (R : Bool → Bool → Prop) (empty : R false false) (keep : Nat → Prop)
    (w v : List Bool) (x y : Bool) (nextRel : R x y) (len : w.length = v.length)
    (agree : ∀ k, keep k → R (w.getD k false) (v.getD k false)) :
    ∀ k, keep k → R ((w ++ [x]).getD k false) ((v ++ [y]).getD k false) := by
  intro k hk
  by_cases old : k < w.length
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append, ← len, ite_eq_left old]
      using (agree k hk)
  · by_cases fresh : k = w.length
    · subst k
      simpa [List.getD_eq_getElem?_getD, ← len] using nextRel
    · have hw : (w ++ [x]).length ≤ k := by simp; omega
      have hv : (v ++ [y]).length ≤ k := by simp; omega
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw,
        List.getElem?_eq_none hv, Option.getD_none] using empty

theorem mxFold (R : Bool → Bool → Prop) (empty : R false false) (keep : Nat → Prop)
    (gs : List Gate) (w v : List Bool)
    (reads : ∀ k ∈ gs.flatMap Gate.inputs, keep k)
    (allowed : ∀ g ∈ gs, mxPreserves R g)
    (len : w.length = v.length) (agree : ∀ k, keep k → R (w.getD k false) (v.getD k false)) :
    ∀ k, keep k → R ((gs.foldl mxStep w).getD k false) ((gs.foldl mxStep v).getD k false) := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g gs ih =>
    have headReads : ∀ k ∈ g.inputs, keep k :=
      fun k hk => reads k (List.mem_append_left _ hk)
    have tailReads : ∀ k ∈ gs.flatMap Gate.inputs, keep k :=
      fun k hk => reads k (List.mem_append_right _ hk)
    have gate := allowed g (by simp) w v (fun k hk => agree k (headReads k hk))
    apply ih (w := mxStep w g) (v := mxStep v g) tailReads (fun z hz => allowed z (by simp [hz]))
    · simp [mxStep, len]
    · exact mxAppend R empty keep w v _ _ gate len agree

theorem mxOutBound (C : Circuit) (tail : List Gate) (hpref : mxHead C tail)
    (last : C.output + 1 = 9+C.size) : 9 < C.output := by
  unfold mxHead at hpref
  simp only [Circuit.size, hpref, List.length_cons] at last
  omega

theorem mxTransfer (C : Circuit) (tail : List Gate) (hpref : mxHead C tail)
    (correct : mxCorrect C) (R : Bool → Bool → Prop) (empty : R false false)
    (keep : Nat → Prop) (x y : Fin 9 → Bool)
    (initial : ∀ k : Fin 11, keep k.val → R ((mxStart x).getD k.val false) ((mxStart y).getD k.val false))
    (reads : ∀ k ∈ tail.flatMap Gate.inputs, keep k) (allowed : ∀ g ∈ tail, mxPreserves R g)
    (out : keep C.output) : R (mxPM x) (mxPM y) := by
  have startLen (z : Fin 9 → Bool) : (mxStart z).length = 11 := by simp [mxStart, mxStep]
  have base : ∀ k, keep k → R ((mxStart x).getD k false) ((mxStart y).getD k false) := by
    intro k hk
    by_cases small : k < 11
    · exact initial ⟨k,small⟩ hk
    · have hx : (mxStart x).length ≤ k := by rw [startLen]; omega
      have hy : (mxStart y).length ≤ k := by rw [startLen]; omega
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hx,
        List.getElem?_eq_none hy, Option.getD_none] using empty
  have heval (z : Fin 9 → Bool) : C.eval (List.ofFn z) =
      (tail.foldl mxStep (mxStart z)).getD C.output false := by
    change (C.gates.foldl mxStep (List.ofFn z)).getD C.output false = _
    unfold mxHead at hpref
    simp only [hpref, List.foldl_cons, mxStart]
  rw [← correct x, ← correct y, heval, heval]
  exact mxFold R empty keep tail _ _ reads allowed ((startLen _).trans (startLen _).symm) base _ out

def mxRow (i : Fin 9) (b : Bool) (j : Fin 9) : Bool :=
  if i = j then b else
    Nat.testBit (([274, 265, 136, 258, 257, 129, 34, 33, 17] : List Nat).getD i.val 0) j.val

theorem mxOtherCert : ∀ i : Fin 9, i.val ≠ 0 → i.val ≠ 4 →
    mxPM (mxRow i false) ≠ mxPM (mxRow i true) ∧
    ∀ k : Fin 11, k.val ≠ i.val →
      (mxStart (mxRow i false)).getD k.val false = (mxStart (mxRow i true)).getD k.val false := by
  decide +kernel

theorem mxOtherReads (C : Circuit) (tail : List Gate) (hpref : mxHead C tail)
    (last : C.output + 1 = 9+C.size) (correct : mxCorrect C)
    (i : Fin 9) (hi0 : i.val ≠ 0) (hi4 : i.val ≠ 4) : i.val ∈ tail.flatMap Gate.inputs := by
  apply Decidable.byContradiction
  intro hn
  have pair := mxOtherCert i hi0 hi4
  have hhi := i.isLt
  have ho := mxOutBound C tail hpref last
  apply pair.1
  apply mxTransfer C tail hpref correct Eq rfl (fun k => k ≠ i.val) _ _ pair.2
  · intro k hk e
    exact hn (e ▸ hk)
  · exact fun g _ => mxPreservesEq g
  · omega

def mxBits (n : Nat) (k : Fin 9) : Bool := n.testBit k.val

theorem mxSwapCert : mxPM (mxBits 161) ≠ mxPM (mxBits 176) ∧
    ∀ k : Fin 11, (k.val ≠ 0 ∧ k.val ≠ 4) →
      (mxStart (mxBits 161)).getD k.val false = (mxStart (mxBits 176)).getD k.val false := by
  decide +kernel

theorem mxOrientationRead (C : Circuit) (tail : List Gate) (hpref : mxHead C tail)
    (last : C.output + 1 = 9+C.size) (correct : mxCorrect C) :
    0 ∈ tail.flatMap Gate.inputs ∨ 4 ∈ tail.flatMap Gate.inputs := by
  by_cases ha : 0 ∈ tail.flatMap Gate.inputs
  · exact Or.inl ha
  · apply Or.inr
    apply Decidable.byContradiction
    intro hb
    have ho := mxOutBound C tail hpref last
    apply mxSwapCert.1
    apply mxTransfer C tail hpref correct Eq rfl (fun k => k ≠ 0 ∧ k ≠ 4) _ _ mxSwapCert.2
    · intro k hk
      exact ⟨fun h => ha (h ▸ hk), fun h => hb (h ▸ hk)⟩
    · exact fun g _ => mxPreservesEq g
    · constructor <;> omega

def mxOrientation (which : Bool) : Nat := if which then 4 else 0

def mxFrom (which : Bool) : Fin 9 → Bool := mxBits (if which then 84 else 161)

def mxTo (which : Bool) : Fin 9 → Bool := mxBits (if which then 69 else 176)

theorem mxOrderCert : ∀ w : Bool, ¬ mxLe (mxPM (mxFrom w)) (mxPM (mxTo w)) ∧
    ∀ k : Fin 11, k.val ≠ mxOrientation w →
      mxLe ((mxStart (mxFrom w)).getD k.val false) ((mxStart (mxTo w)).getD k.val false) := by
  unfold mxLe
  decide +kernel

theorem mxBothRead (C : Circuit) (tail : List Gate) (hpref : mxHead C tail)
    (last : C.output + 1 = 9+C.size) (correct : mxCorrect C)
    (hm : ∀ g ∈ tail, g.op = .and ∨ g.op = .or) :
    0 ∈ tail.flatMap Gate.inputs ∧ 4 ∈ tail.flatMap Gate.inputs := by
  have ho := mxOutBound C tail hpref last
  have both (w : Bool) : mxOrientation w ∈ tail.flatMap Gate.inputs := by
    apply Decidable.byContradiction
    intro hn
    have cert := mxOrderCert w
    apply cert.1
    apply mxTransfer C tail hpref correct mxLe (fun h => h) (fun k => k ≠ mxOrientation w) _ _ cert.2
    · intro k hk e
      exact hn (e ▸ hk)
    · exact fun g hg => mxPreservesLe g (hm g hg)
    · cases w
      · change C.output ≠ 0
        omega
      · change C.output ≠ 4
        omega
  exact ⟨both false, both true⟩



private def independent4 (x : BitVec 4) : Bool :=
  (x.getLsbD 0 == x.getLsbD 1) && (x.getLsbD 2 == x.getLsbD 3)

private def increasing4 (x : BitVec 4) : Bool :=
  (!x.getLsbD 0 || x.getLsbD 1) && (!x.getLsbD 2 || x.getLsbD 3)

private def decreasing4 (x : BitVec 4) : Bool :=
  (!x.getLsbD 1 || x.getLsbD 0) && (!x.getLsbD 3 || x.getLsbD 2)

private def cost4 (x : BitVec 4) : Nat :=
  if independent4 x then 0 else if increasing4 x || decreasing4 x then 1 else 2

def orientationCost (x : Nat) : Nat := cost4 (BitVec.ofNat 4 x)

set_option maxHeartbeats 2000000 in
private theorem gate_table : ∀ x y : BitVec 4,
    cost4 (x &&& y) ≤ cost4 x + cost4 y ∧ cost4 (x ||| y) ≤ cost4 x + cost4 y := by
  decide

private theorem not_table : ∀ x : BitVec 4, cost4 (x ^^^ 15) = cost4 x := by decide

theorem orientation_and (x y : Nat) :
    orientationCost (x &&& y) ≤ orientationCost x + orientationCost y := by
  unfold orientationCost
  rw [BitVec.ofNat_and]
  exact (gate_table _ _).1

theorem orientation_or (x y : Nat) :
    orientationCost (x ||| y) ≤ orientationCost x + orientationCost y := by
  unfold orientationCost
  rw [BitVec.ofNat_or]
  exact (gate_table _ _).2

theorem orientation_not (x : Nat) : orientationCost (x ^^^ 15) = orientationCost x := by
  unfold orientationCost
  rw [BitVec.ofNat_xor]
  exact not_table _

theorem raw_costs : orientationCost 0xA = 1 ∧ orientationCost 0x5 = 1 := by decide

theorem binate_costs : orientationCost 0x6 = 2 ∧ orientationCost 0x9 = 2 := by decide

def mixedSources (selectA : Bool) : List Nat :=
  [if selectA then 0xA else 0x5, 0, 0xC, 0, if selectA then 0x5 else 0xA,
   3, 0xC, 3, 0, 0xF, 0]

def mixedMatchingColumn (cols : List Nat) : Nat :=
  let x := fun (i : Nat) => cols.getD i 0
  (x 0 &&& x 4 &&& x 8) ||| (x 0 &&& x 5 &&& x 7) ||| (x 1 &&& x 3 &&& x 8) |||
  (x 1 &&& x 5 &&& x 6) ||| (x 2 &&& x 3 &&& x 7) ||| (x 2 &&& x 4 &&& x 6)

theorem mixed_target (selectA : Bool) : mixedMatchingColumn (mixedSources selectA) =
    (if selectA then 0x6 else 0x9) := by cases selectA <;> decide

def singleSourceIndices (selectA : Bool) : List Nat :=
  if selectA then [0,1,2,3,5,6,7,8,9,10] else [1,2,3,4,5,6,7,8,9,10]

theorem orientation_budget (selectA : Bool) :
    ((singleSourceIndices selectA).map (fun i => orientationCost ((mixedSources selectA).getD i 0))).sum = 1 ∧
    orientationCost (mixedMatchingColumn (mixedSources selectA)) = 2 := by
  cases selectA <;> decide



def sensStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

theorem colStepOld (w : List Bool) (g : Gate) (k : Nat) (hk : k < w.length) :
    (sensStep w g).getD k false = w.getD k false := by
  simp only [sensStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem colStepNew (w : List Bool) (g : Gate) :
    (sensStep w g).getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
  simp [sensStep, List.getD_eq_getElem?_getD]

theorem colStable (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (gs.foldl sensStep w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hb : k < (sensStep w g).length := by
      simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
      omega
    exact (ih (w := sensStep w g) hb).trans (colStepOld w g k hk)

theorem colFoldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl sensStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem colGateValue (C : Circuit) (j : Fin C.gates.length) (x : Fin 9 → Bool)
    (valid : ∀ k ∈ (C.gates.get j).inputs, k < 9+j.val) :
    (C.wires (List.ofFn x)).getD (9+j.val) false =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k =>
      (C.wires (List.ofFn x)).getD k false) := by
  let g := C.gates.get j
  let pre := C.gates.take j.val
  let post := C.gates.drop (j.val+1)
  let w := pre.foldl sensStep (List.ofFn x)
  have hsplit : C.gates = pre ++ g :: post := by
    dsimp only [pre, g, post]
    rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons j.isLt, List.take_append_drop]
  have len : w.length = 9+j.val := by
    simp only [w, pre, colFoldLength, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt j.isLt)]
  have after : C.wires (List.ofFn x) = post.foldl sensStep (sensStep w g) := by
    change C.gates.foldl sensStep (List.ofFn x) = _
    have eqFold := congrArg (fun gs : List Gate => gs.foldl sensStep (List.ofFn x)) hsplit
    simpa only [List.foldl_append, List.foldl_cons, w] using eqFold
  have old (k : Nat) (hk : k < 9+j.val) :
      (C.wires (List.ofFn x)).getD k false = w.getD k false := by
    have hkw : k < w.length := by omega
    have hkn : k < (sensStep w g).length := by
      simp only [sensStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [after]
    exact (colStable post _ k hkn).trans (colStepOld w g k hkw)
  have fresh : (C.wires (List.ofFn x)).getD (9+j.val) false =
      g.op.eval (g.inputs.map fun k => w.getD k false) := by
    rw [after, ← len]
    apply (colStable post _ _ ?_).trans (colStepNew w g)
    simp [sensStep]
  rw [fresh]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro k hk
  exact (old k (valid k hk)).symm

theorem colInputsValid (C : Circuit) (j : Fin C.gates.length) (a b : Nat)
    (hins : (C.gates.get j).inputs = [a,b]) (ha : a < 9+j.val) (hb : b < 9+j.val) :
    ∀ k ∈ (C.gates.get j).inputs, k < 9+j.val := by
  intro k hk
  simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> assumption



open PEqualNP.CircuitLowerBounds

def trialCol (C : Circuit) (rows : Fin 8 → Fin 9 → Bool) (k : Nat) : Nat :=
  pack8 (fun r => (C.wires (List.ofFn (rows r))).getD k false)

theorem pack8_not (f : Fin 8 → Bool) : pack8 (fun r => !f r) = pack8 f ^^^ 255 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, show (255 : Nat) = 2^8-1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 8
  · simp only [pack8_value, dite_eq_left hi, decide_eq_true hi, Bool.xor_true]
  · simp only [pack8_value, dite_eq_right hi, decide_eq_false hi, Bool.xor_false]

theorem trialCol_and (C : Circuit) (rows : Fin 8 → Fin 9 → Bool) (j : Fin C.gates.length)
    (a b : Nat) (hop : (C.gates.get j).op = .and) (hins : (C.gates.get j).inputs = [a,b])
    (ha : a < 9+j.val) (hb : b < 9+j.val) :
    trialCol C rows (9+j.val) = trialCol C rows a &&& trialCol C rows b := by
  unfold trialCol
  rw [← pack8_and]
  apply congrArg pack8
  funext r
  rw [colGateValue C j (rows r) (colInputsValid C j a b hins ha hb), hop, hins] <;>
    simp [GateOp.eval]

theorem trialCol_or (C : Circuit) (rows : Fin 8 → Fin 9 → Bool) (j : Fin C.gates.length)
    (a b : Nat) (hop : (C.gates.get j).op = .or) (hins : (C.gates.get j).inputs = [a,b])
    (ha : a < 9+j.val) (hb : b < 9+j.val) :
    trialCol C rows (9+j.val) = trialCol C rows a ||| trialCol C rows b := by
  unfold trialCol
  rw [← pack8_or]
  apply congrArg pack8
  funext r
  rw [colGateValue C j (rows r) (colInputsValid C j a b hins ha hb), hop, hins] <;>
    simp [GateOp.eval]

theorem trialCol_not (C : Circuit) (rows : Fin 8 → Fin 9 → Bool) (j : Fin C.gates.length)
    (a : Nat) (hop : (C.gates.get j).op = .not) (hins : (C.gates.get j).inputs = [a])
    (ha : a < 9+j.val) : trialCol C rows (9+j.val) = trialCol C rows a ^^^ 255 := by
  have valid : ∀ k ∈ (C.gates.get j).inputs, k < 9+j.val := by
    intro k hk
    simp only [hins, List.mem_singleton] at hk
    subst k
    exact ha
  unfold trialCol
  rw [← pack8_not]
  apply congrArg pack8
  funext r
  rw [colGateValue C j (rows r) valid, hop, hins] <;> simp [GateOp.eval]

theorem orientation_not8 (x : Nat) : orientationCost (x ^^^ 255) = orientationCost x := by
  have mask : BitVec.ofNat 4 255 = BitVec.ofNat 4 15 := by decide
  simpa only [orientationCost, BitVec.ofNat_xor, mask] using orientation_not x

def fullSeed : List Nat := [255,255,240,0,255,170,204,240,0,255,255]

def fullRows (r : Fin 8) (k : Fin 9) : Bool := (fullSeed.getD k.val 0).testBit r.val

def mixedSeed (selectA : Bool) : List Nat :=
  [if selectA then 170 else 85, 0, 204, 0, if selectA then 85 else 170,
   51, 204, 51, 0, 255, 0]

def mixedRows (selectA : Bool) (r : Fin 8) (k : Fin 9) : Bool :=
  ((mixedSeed selectA).getD k.val 0).testBit r.val

theorem trialCol_seed (C : Circuit) (tail : List Gate) (hg : mxHead C tail)
    (rows : Fin 8 → Fin 9 → Bool) (k : Fin 11) : trialCol C rows k.val =
      pack8 (fun r => (mxStart (rows r)).getD k.val false) := by
  unfold trialCol
  apply congrArg pack8
  funext r
  change (C.gates.foldl sensStep (List.ofFn (rows r))).getD k.val false = _
  unfold mxHead at hg
  rw [hg]
  apply colStable tail (mxStart (rows r)) k.val
  simp [mxStart, mxStep]

private theorem fullSeedsChecked : ∀ k : Fin 11,
    pack8 (fun r => (mxStart (fullRows r)).getD k.val false) = fullSeed.getD k.val 0 := by
  decide +kernel

private theorem mixedSeedsChecked : ∀ s : Bool, ∀ k : Fin 11,
    pack8 (fun r => (mxStart (mixedRows s r)).getD k.val false) = (mixedSeed s).getD k.val 0 := by
  decide +kernel

theorem fullCol_seed (C : Circuit) (tail : List Gate) (hg : mxHead C tail) (k : Fin 11) :
    trialCol C fullRows k.val = fullSeed.getD k.val 0 :=
  (trialCol_seed C tail hg fullRows k).trans (fullSeedsChecked k)

theorem mixedCol_seed (C : Circuit) (tail : List Gate) (hg : mxHead C tail)
    (s : Bool) (k : Fin 11) : trialCol C (mixedRows s) k.val = (mixedSeed s).getD k.val 0 :=
  (trialCol_seed C tail hg (mixedRows s) k).trans (mixedSeedsChecked s k)

theorem trialCol_target (C : Circuit) (h : mxCorrect C) (rows : Fin 8 → Fin 9 → Bool) :
    trialCol C rows C.output = pack8 (fun r => mxPM (rows r)) := by
  apply congrArg pack8
  funext r
  exact h (rows r)

theorem fullCol_target (C : Circuit) (h : mxCorrect C) : trialCol C fullRows C.output = 0xE8 :=
  (trialCol_target C h fullRows).trans (by decide +kernel)

theorem mixedCol_target (C : Circuit) (h : mxCorrect C) (s : Bool) :
    trialCol C (mixedRows s) C.output = (if s then 0x66 else 0x99) := by
  rw [trialCol_target C h]
  cases s <;> decide +kernel

theorem mixedBudget8 (s : Bool) :
    ((singleSourceIndices s).map (fun k => orientationCost ((mixedSeed s).getD k 0))).sum = 1 ∧
      orientationCost (if s then 0x66 else 0x99) = 2 := by
  cases s <;> decide +kernel

theorem fullBudget8 : (fullSeed.map weight).sum = 4 := by decide +kernel


open PEqualNP.CircuitLowerBounds

theorem caseGateBounds (C : Circuit) (gs : List Gate) (hpref : mxHead C gs)
    (form : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j))
    (cost : Nat → Nat)
    (andBound : ∀ x y, cost (x &&& y) ≤ cost x + cost y)
    (orBound : ∀ x y, cost (x ||| y) ≤ cost x + cost y)
    (notBound : ∀ j : Fin gs.length, (gs.get j).inputs.length = 1 →
      ∀ x, cost (x ^^^ 255) ≤ cost x)
    (rows : Fin 8 → Fin 9 → Bool) (j : Fin gs.length) :
    cost (trialCol C rows (11 + j.val)) ≤
      ((gs.get j).inputs.map (fun k => cost (trialCol C rows k))).sum := by
  have liftGate : ∃ k : Fin C.gates.length,
      k.val = j.val + 2 ∧ C.gates.get k = gs.get j := by
    unfold mxHead at hpref
    rw [hpref]
    exact ⟨j.succ.succ, rfl, rfl⟩
  obtain ⟨k, hk, heq⟩ := liftGate
  have hid : 9 + k.val = 11 + j.val := by omega
  rcases form j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
  · have hlen : (gs.get j).inputs.length = 1 := congrArg List.length hin
    have ha' : a < 9 + k.val := by rw [hid]; exact ha
    have hop' : (C.gates.get k).op = .not := by rw [heq]; exact hop
    have hin' : (C.gates.get k).inputs = [a] := by rw [heq]; exact hin
    rw [hin]
    change cost (trialCol C rows (11 + j.val)) ≤ cost (trialCol C rows a) + 0
    rw [Nat.add_zero, ← hid, trialCol_not C rows k a hop' hin' ha']
    exact notBound j hlen _
  · have ha' : a < 9 + k.val := by omega
    have hb' : b < 9 + k.val := by omega
    have hin' : (C.gates.get k).inputs = [a,b] := by rw [heq]; exact hin
    rw [hin]
    change cost (trialCol C rows (11 + j.val)) ≤
      cost (trialCol C rows a) + (cost (trialCol C rows b) + 0)
    rw [Nat.add_zero, ← hid]
    rcases hop with hand | hor
    · have hop' : (C.gates.get k).op = .and := by rw [heq]; exact hand
      rw [trialCol_and C rows k a b hop' hin' ha' hb']
      exact andBound _ _
    · have hop' : (C.gates.get k).op = .or := by rw [heq]; exact hor
      rw [trialCol_or C rows k a b hop' hin' ha' hb']
      exact orBound _ _

theorem fullGateBounds (C : Circuit) (gs : List Gate) (hpref : mxHead C gs)
    (form : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j))
    (binary : ∀ g ∈ gs, g.inputs.length = 2)
    (rows : Fin 8 → Fin 9 → Bool) (j : Fin gs.length) :
    weight (trialCol C rows (11 + j.val)) ≤
      ((gs.get j).inputs.map (fun k => weight (trialCol C rows k))).sum := by
  refine caseGateBounds C gs hpref form weight weight_and weight_or ?_ rows j
  intro i hs x
  have htwo := binary (gs.get i) (List.get_mem gs i)
  omega

theorem mixedGateBounds (C : Circuit) (gs : List Gate) (hpref : mxHead C gs)
    (form : ∀ j : Fin gs.length, GateSlotForm (11 + j.val) (gs.get j))
    (rows : Fin 8 → Fin 9 → Bool) (j : Fin gs.length) :
    orientationCost (trialCol C rows (11 + j.val)) ≤
      ((gs.get j).inputs.map (fun k => orientationCost (trialCol C rows k))).sum := by
  refine caseGateBounds C gs hpref form orientationCost orientation_and orientation_or ?_ rows j
  intro i hs x
  exact Nat.le_of_eq (orientation_not8 x)


open PEqualNP.CircuitLowerBounds

theorem caseFullEnd (C : Circuit) (gs : List Gate) (hpref : mxHead C gs) (correct : mxCorrect C)
    (form : ∀ j : Fin gs.length, GateSlotForm (11+j.val) (gs.get j))
    (len : gs.length = 10) (out : C.output = 20) (binary : ∀ g ∈ gs, g.inputs.length = 2)
    (slots : (gs.flatMap Gate.inputs).Perm (List.range 20)) : False := by
  let w (k : Nat) := weight (trialCol C fullRows k)
  have bound := caseOutputBudget gs (List.range 11) (caseFullReadSplit gs slots) len w
    (fullGateBounds C gs hpref form binary fullRows)
  have src : (List.range 11).map w = (List.range 11).map (fun k => weight (fullSeed.getD k 0)) := by
    apply List.map_congr_left
    intro k hk
    exact congrArg weight (fullCol_seed C gs hpref ⟨k, List.mem_range.mp hk⟩)
  have sourceWeight : ((List.range 11).map w).sum = 4 := by
    rw [src]
    decide +kernel
  have targetWeight : w 20 = 5 := by
    change weight (trialCol C fullRows 20) = 5
    rw [← out, fullCol_target C correct, weight_target]
  omega

theorem caseMissingEnd (C : Circuit) (gs : List Gate) (hpref : mxHead C gs) (correct : mxCorrect C)
    (form : ∀ j : Fin gs.length, GateSlotForm (11+j.val) (gs.get j))
    (missingWire : Nat) (ho : missingWire = 0 ∨ missingWire = 4) (len : gs.length = 10) (out : C.output = 20)
    (slots : (gs.flatMap Gate.inputs).Perm ((List.range 20).erase missingWire)) : False := by
  let s : Bool := decide (missingWire = 4)
  let w (k : Nat) := orientationCost (trialCol C (mixedRows s) k)
  have sources : (List.range 11).erase missingWire = singleSourceIndices s := by
    rcases ho with rfl | rfl <;> rfl
  have splitRead := caseErasedReadSplit gs missingWire ho slots
  rw [sources] at splitRead
  have bound := caseOutputBudget gs (singleSourceIndices s) splitRead len w
    (mixedGateBounds C gs hpref form (mixedRows s))
  have src : (singleSourceIndices s).map w =
      (singleSourceIndices s).map (fun k => orientationCost ((mixedSeed s).getD k 0)) := by
    apply List.map_congr_left
    intro k hk
    rw [← sources] at hk
    have hlt : k < 11 := List.mem_range.mp (List.mem_of_mem_erase hk)
    exact congrArg orientationCost (mixedCol_seed C gs hpref s ⟨k,hlt⟩)
  have sourceWeight : ((singleSourceIndices s).map w).sum = 1 := by
    rw [src]
    exact (mixedBudget8 s).1
  have targetWeight : w 20 = 2 := by
    change orientationCost (trialCol C (mixedRows s) 20) = 2
    rw [← out, mixedCol_target C correct]
    exact (mixedBudget8 s).2
  omega

theorem caseImpossible (C : Circuit) (gs : List Gate) (hpref : mxHead C gs)
    (hsize : C.size ≤ 12) (hcalc : mxCorrect C) (hout : C.output + 1 = 9 + C.size)
    (hform : ∀ j : Fin C.gates.length, GateSlotForm (9+j.val) (C.gates.get j))
    (huse : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs) : False := by
  have hg : C.gates = ⟨.or,[0,4]⟩ :: ⟨.and,[0,4]⟩ :: gs := hpref
  have budget : gs.length ≤ 10 := by
    simp only [Circuit.size, hg, List.length_cons] at hsize
    omega
  have output (len : gs.length = 10) : C.output = 20 := by
    simp only [Circuit.size, hg, List.length_cons, len] at hout
    omega
  rw [hg] at hform huse
  have form := suffix_gateForm _ _ gs hform
  have arity := suffix_arity gs form
  have live := suffix_live _ _ gs huse
  have read9 := caseWire9 (⟨.or,[0,4]⟩ : Gate) (⟨.and,[0,4]⟩ : Gate) gs (by decide) huse
  have other (i : Nat) (hi : i < 9) (ha : i ≠ 0) (hb : i ≠ 4) : i ∈ gs.flatMap Gate.inputs :=
    mxOtherReads C gs hpref hout hcalc ⟨i,hi⟩ ha hb
  have orientation := mxOrientationRead C gs hpref hout hcalc
  by_cases both : 0 ∈ gs.flatMap Gate.inputs ∧ 4 ∈ gs.flatMap Gate.inputs
  · have raw (i : Nat) (hi : i < 9) : i ∈ gs.flatMap Gate.inputs := by
      by_cases ha : i = 0
      · rw [ha]
        exact both.1
      by_cases hb : i = 4
      · rw [hb]
        exact both.2
      exact other i hi ha hb
    obtain ⟨len, binary, slots⟩ := caseAllSlots gs budget arity raw read9 live
    exact caseFullEnd C gs hpref hcalc form len (output len) binary slots
  · have unary : ∃ g ∈ gs, g.inputs.length < 2 := by
      apply Classical.byContradiction
      intro noUnary
      have binary (g : Gate) (hg' : g ∈ gs) : g.inputs.length = 2 := by
        have upper := arity g hg'
        have lower : ¬ g.inputs.length < 2 := fun h => noUnary ⟨g,hg',h⟩
        omega
      apply both
      apply mxBothRead C gs hpref hout hcalc
      intro g hg'
      obtain ⟨j,rfl⟩ := List.get_of_mem hg'
      exact (suffix_binary gs form binary j).1
    have missing (missingWire : Nat) (ho : missingWire = 0 ∨ missingWire = 4) (absent : missingWire ∉ gs.flatMap Gate.inputs) : False := by
      have raw (i : Nat) (hi : i < 9) (hne : i ≠ missingWire) : i ∈ gs.flatMap Gate.inputs := by
        by_cases ha : i = 0
        · subst i
          rcases orientation with ha | hb
          · exact ha
          · have e : missingWire = 4 := by omega
            exact False.elim (absent (e.symm ▸ hb))
        by_cases hb : i = 4
        · subst i
          rcases orientation with ha | hb
          · have e : missingWire = 0 := by omega
            exact False.elim (absent (e.symm ▸ ha))
          · exact hb
        exact other i hi ha hb
      have ho9 : missingWire < 9 := by omega
      obtain ⟨len, slots⟩ := caseMissingSlots gs missingWire ho9 budget arity unary raw read9 live
      exact caseMissingEnd C gs hpref hcalc form missingWire ho len (output len) slots
    by_cases ha : 0 ∈ gs.flatMap Gate.inputs
    · exact missing 4 (Or.inr rfl) (fun hb => both ⟨ha,hb⟩)
    · exact missing 0 (Or.inl rfl) ha
end PEqualNP.Outside.L_meta_27613

theorem PEqualNP.Outside.L_meta_27613 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩)) := by
  intro witness
  obtain ⟨C, _, hsize, hcalc, hout, hform, _, huse, hfirst, hsecond⟩ := witness
  obtain ⟨gs, hg⟩ : ∃ gs, C.gates =
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ::
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ :: gs := by
    cases ht : C.gates with
    | nil => simp [ht] at hfirst
    | cons g0 remain =>
      cases remain with
      | nil => simp [ht] at hsecond
      | cons g1 gs =>
        have h0 : g0 = _ := Option.some.inj (by simpa only [ht, List.head?_cons] using hfirst)
        have h1 : g1 = _ := Option.some.inj (by simpa only [ht, List.tail_cons, List.head?_cons] using hsecond)
        exact ⟨gs, by rw [h0, h1]⟩
  exact PEqualNP.Outside.L_meta_27613.caseImpossible C gs hg hsize hcalc hout hform huse
