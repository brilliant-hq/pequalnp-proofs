import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50051_aux

abbrev Sig := BitVec 5
abbrev Bank := List Sig

def initial : Bank := [30, 28, 24, 16, 0, 31]

inductive Reach : ℕ → ℕ → Bank → Prop where
  | init : Reach 0 0 initial
  | and {n k w a b} (h : Reach n k w) (ha : a ∈ w) (hb : b ∈ w) :
      Reach (n + 1) k (w ++ [a &&& b])
  | or {n k w a b} (h : Reach n k w) (ha : a ∈ w) (hb : b ∈ w) :
      Reach (n + 1) k (w ++ [a ||| b])
  | not {n k w a} (h : Reach n k w) (ha : a ∈ w) :
      Reach (n + 1) (k + 1) (w ++ [~~~a])
  | keep {n k w a} (h : Reach n k w) (ha : a ∈ w) :
      Reach (n + 1) k (w ++ [a])

private def insertSig (a : Sig) : Bank → Bank
  | [] => [a]
  | b :: bs => if a.toNat ≤ b.toNat then a :: b :: bs else b :: insertSig a bs

private theorem mem_insertSig {a b : Sig} {xs : Bank} :
    b ∈ insertSig a xs ↔ b = a ∨ b ∈ xs := by
  induction xs with
  | nil => simp [insertSig]
  | cons u us ih =>
    unfold insertSig
    split <;> simp [ih, or_left_comm]

private def binaryChoices (xs : Bank) : Bank :=
  (xs.flatMap fun a => xs.flatMap fun b => [a &&& b, a ||| b]).eraseDups

private def successors (s : ℕ × Bank) : List (ℕ × Bank) :=
  let (k, xs) := s
  s :: ((binaryChoices xs).filter fun a => !xs.contains a).map (fun a => (k, insertSig a xs)) ++
    (if k < 2 then
      ((xs.map fun a => ~~~a).filter fun a => !xs.contains a).map (fun a => (k + 1, insertSig a xs))
    else [])

private def frontier : ℕ → List (ℕ × Bank)
  | 0 => [(0, [0, 16, 24, 28, 30, 31])]
  | n + 1 => ((frontier n).flatMap successors).eraseDups

private theorem mem_next {n : ℕ} {s : ℕ × Bank} :
    s ∈ frontier (n + 1) ↔ s ∈ (frontier n).flatMap successors := by
  simp only [frontier, List.mem_eraseDups]

private theorem stay {n k xs} (h : (k, xs) ∈ frontier n) :
    (k, xs) ∈ frontier (n + 1) :=
  mem_next.mpr (List.mem_flatMap.mpr ⟨(k, xs), h, List.mem_cons_self⟩)

private theorem add_binary {n k xs a} (h : (k, xs) ∈ frontier n)
    (ha : a ∈ binaryChoices xs) (hfresh : a ∉ xs) :
    (k, insertSig a xs) ∈ frontier (n + 1) := by
  apply mem_next.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(k, xs), h, ?_⟩
  unfold successors
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa using hfresh⟩, rfl⟩

private theorem add_not {n k xs a} (h : (k, xs) ∈ frontier n)
    (ha : a ∈ xs) (hk : k < 2) (hfresh : ~~~a ∉ xs) :
    (k + 1, insertSig (~~~a) xs) ∈ frontier (n + 1) := by
  apply mem_next.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(k, xs), h, ?_⟩
  unfold successors
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  simp only [hk, ↓reduceIte]
  apply List.mem_map.mpr
  exact ⟨~~~a, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨a, ha, rfl⟩,
    by simpa using hfresh⟩, rfl⟩

private theorem fresh_cover {w xs : Bank} {a : Sig} (h : w ⊆ xs) :
    w ++ [a] ⊆ insertSig a xs := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact mem_insertSig.mpr (Or.inr (h ht))
  · exact mem_insertSig.mpr (Or.inl rfl)

private theorem dup_cover {w xs : Bank} {a : Sig} (h : w ⊆ xs) (ha : a ∈ xs) :
    w ++ [a] ⊆ xs := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact h ht
  · exact ha

private theorem simulate {n k w} (h : Reach n k w) (hk : k ≤ 2) :
    ∃ q xs, (q, xs) ∈ frontier n ∧ q ≤ k ∧ w ⊆ xs := by
  induction h with
  | init =>
    refine ⟨0, [0, 16, 24, 28, 30, 31],
      List.mem_cons_self, le_rfl, ?_⟩
    intro a ha
    simpa [initial, or_left_comm, or_assoc, or_comm] using ha
  | @and n k w a b h ha hb ih =>
    obtain ⟨q, xs, hq, hqk, hw⟩ := ih hk
    by_cases hd : a &&& b ∈ xs
    · exact ⟨q, xs, stay hq, hqk, dup_cover hw hd⟩
    have hm : a &&& b ∈ binaryChoices xs := by
      unfold binaryChoices
      apply List.mem_eraseDups.mpr
      exact List.mem_flatMap.mpr ⟨a, hw ha, List.mem_flatMap.mpr ⟨b, hw hb, by simp⟩⟩
    exact ⟨q, insertSig (a &&& b) xs, add_binary hq hm hd, hqk, fresh_cover hw⟩
  | @or n k w a b h ha hb ih =>
    obtain ⟨q, xs, hq, hqk, hw⟩ := ih hk
    by_cases hd : a ||| b ∈ xs
    · exact ⟨q, xs, stay hq, hqk, dup_cover hw hd⟩
    have hm : a ||| b ∈ binaryChoices xs := by
      unfold binaryChoices
      apply List.mem_eraseDups.mpr
      exact List.mem_flatMap.mpr ⟨a, hw ha, List.mem_flatMap.mpr ⟨b, hw hb, by simp⟩⟩
    exact ⟨q, insertSig (a ||| b) xs, add_binary hq hm hd, hqk, fresh_cover hw⟩
  | @not n k w a h ha ih =>
    obtain ⟨q, xs, hq, hqk, hw⟩ := ih (by omega)
    by_cases hd : ~~~a ∈ xs
    · exact ⟨q, xs, stay hq, by omega, dup_cover hw hd⟩
    exact ⟨q+1, insertSig (~~~a) xs, add_not hq (hw ha) (by omega) hd, by omega, fresh_cover hw⟩
  | @keep n k w a h ha ih =>
    obtain ⟨q, xs, hq, hqk, hw⟩ := ih hk
    exact ⟨q, xs, stay hq, hqk, dup_cover hw (hw ha)⟩

private theorem pad {n m k xs} (h : (k, xs) ∈ frontier n) (hm : n ≤ m) :
    (k, xs) ∈ frontier m := by
  induction hm with
  | refl => exact h
  | step _ ih => exact stay ih

private def fails (s : ℕ × Bank) : Bool :=
  !(s.2.contains 2 && s.2.contains 20 && s.2.contains 26)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem checked : ((frontier 4).flatMap successors).all fails = true := by
  decide +kernel

theorem excluded {n k w} (hr : Reach n k w) (hn : n ≤ 5) (hk : k ≤ 2) :
    ¬ ((2 : Sig) ∈ w ∧ (20 : Sig) ∈ w ∧ (26 : Sig) ∈ w) := by
  obtain ⟨q, xs, hq, _, hw⟩ := simulate hr hk
  rintro ⟨h2, h20, h26⟩
  have hfail := List.all_eq_true.mp checked (q, xs) (mem_next.mp (pad hq hn))
  simp [fails] at hfail
  rcases hfail with (h2' | h20') | h26'
  · exact h2' (hw h2)
  · exact h20' (hw h20)
  · exact h26' (hw h26)

end PEqualNP.Outside.L_meta_50051_aux

namespace PEqualNP.Outside.L_meta_50051_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

private def gateValue (w : Bank) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (· &&& ·) 31
  | .or => xs.foldr (· ||| ·) 0
  | .not => ~~~(xs.headD 0)
  | _ => 0

private def execute (gs : List Gate) (w : Bank) : Bank :=
  gs.foldl (fun w g => w ++ [gateValue w g]) w

def rows (t : Fin 5) : List Bool :=
  List.ofFn (fun i : Fin 4 => decide (i.val < t.val)) ++ [false, true]

private theorem initialRows (t : Fin 5) : initial.map (fun s => s.getLsbD t.val) = rows t := by
  revert t
  decide +kernel

private theorem getD_bit (t : Fin 5) (w : Bank) (i : ℕ) :
    (w.map (fun s => s.getLsbD t.val)).getD i false = (w.getD i 0).getLsbD t.val := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

private theorem one_bit (t : Fin 5) : (31 : Sig).getLsbD t.val = true := by
  revert t
  decide +kernel

private theorem not_bit (t : Fin 5) (x : Sig) :
    (~~~x).getLsbD t.val = !(x.getLsbD t.val) := by
  simp [t.isLt]

private theorem gateValue_bit (t : Fin 5) (w : Bank) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gateValue w g).getLsbD t.val =
      g.op.eval (g.inputs.map fun i => (w.map (fun s => s.getLsbD t.val)).getD i false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · simp only [gateValue, GateOp.eval, getD_bit]
    induction l with
    | nil => exact one_bit t
    | cons a l ih =>
      simp only [List.map_cons, List.foldr_cons, List.all_cons, id_eq, BitVec.getLsbD_and, ih]
  · simp only [gateValue, GateOp.eval, getD_bit]
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.foldr_cons, List.any_cons, id_eq, BitVec.getLsbD_or, ih]
  · simp only [gateValue, GateOp.eval, getD_bit]
    cases l with
    | nil => exact (not_bit t 0).trans (by simp)
    | cons a l => exact not_bit t (w.getD a 0)

private theorem execute_bit (gs : List Gate) (t : Fin 5) (w : Bank)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (fun s => s.getLsbD t.val) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
        (w.map (fun s => s.getLsbD t.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gateValue w g])).map _ = _
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton,
      gateValue_bit t w g (hg g List.mem_cons_self)]

private theorem getD_in {w : Bank} (h0 : 0 ∈ w) (i : ℕ) : w.getD i 0 ∈ w := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (by omega)]
    exact h0

private theorem execute_length (gs : List Gate) (w : Bank) :
    (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w ++ [gateValue w g])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem gateStep {n k : ℕ} {w : Bank} (h : Reach n k w)
    (h0 : 0 ∈ w) (h1 : 31 ∈ w) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Reach (n + 1) (k + if g.op = GateOp.not then 1 else 0) (w ++ [gateValue w g]) := by
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  have hor : ∀ a : Sig, a ||| 0 = a := by simp
  have hand : ∀ a : Sig, a &&& 31 = a := by
    intro a
    change a &&& BitVec.allOnes 5 = a
    exact BitVec.and_allOnes
  rcases ho with rfl | rfl | rfl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨u, l⟩⟩⟩
    · simpa [gateValue] using h.keep h1
    · change Reach (n + 1) k (w ++ [w.getD i 0 &&& (31 : Sig)])
      rw [hand]
      exact h.keep (getD_in h0 i)
    · change Reach (n + 1) k (w ++ [w.getD i 0 &&& (w.getD j 0 &&& (31 : Sig))])
      rw [hand]
      exact h.and (getD_in h0 i) (getD_in h0 j)
    · simp at hl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨u, l⟩⟩⟩
    · simpa [gateValue] using h.keep h0
    · simpa [gateValue, hor] using h.keep (getD_in h0 i)
    · simpa [gateValue, hor] using h.or (getD_in h0 i) (getD_in h0 j)
    · simp at hl
  · cases l with
    | nil => simpa [gateValue] using h.not h0
    | cons i l => simpa [gateValue] using h.not (getD_in h0 i)

private theorem execute_reach (gs : List Gate)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {n k : ℕ} {w : Bank} (h : Reach n k w) (h0 : 0 ∈ w) (h1 : 31 ∈ w) :
    Reach (n + gs.length) (k + (gs.filter fun g => decide (g.op = GateOp.not)).length)
      (execute gs w) := by
  induction gs generalizing n k w with
  | nil => simpa [execute] using h
  | cons g gs ih =>
    have hw := gateStep h h0 h1 g (hf g List.mem_cons_self)
    have hr := ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) hw
      (List.mem_append_left _ h0) (List.mem_append_left _ h1)
    have hc : ((g :: gs).filter fun g => decide (g.op = GateOp.not)).length =
        (if g.op = GateOp.not then 1 else 0) +
          (gs.filter fun g => decide (g.op = GateOp.not)).length := by
      by_cases hm : g.op = GateOp.not <;> simp [hm, Nat.add_comm]
    change Reach _ _ (execute gs (w ++ [gateValue w g]))
    convert hr using 1
    · simp only [List.length_cons]
      omega
    · rw [hc]
      omega

theorem trace (D : Circuit) (hf : FanInTwo D) :
    ∃ w, Reach D.size (PEqualNP.NotBracket.notCount D) w ∧
      ∀ i : Fin (6 + D.size), ∃ s ∈ w, ∀ t : Fin 5,
        s.getLsbD t.val = (D.wires (rows t)).getD i.val false := by
  let w := execute D.gates initial
  have h0 : (0 : Sig) ∈ initial := by decide
  have h1 : (31 : Sig) ∈ initial := by decide
  refine ⟨w, ?_, ?_⟩
  · simpa [w, Circuit.size, PEqualNP.NotBracket.notCount] using execute_reach D.gates hf Reach.init h0 h1
  · intro i
    have hlen : w.length = 6 + D.size := execute_length D.gates initial
    have hi : i.val < w.length := hlen.symm ▸ i.isLt
    refine ⟨w.getD i.val 0, ?_, ?_⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    · intro t
      rw [← getD_bit t w i.val]
      change ((execute D.gates initial).map (fun s => s.getLsbD t.val)).getD i.val false = _
      rw [execute_bit D.gates t initial (fun g hg => (hf g hg).1), initialRows]
      rfl

end PEqualNP.Outside.L_meta_50051_aux

namespace PEqualNP.Outside.L_meta_50051_aux

private theorem matchesMask {s target : BitVec 5} {m : Nat}
    (targetBits : ∀ t : Fin 5, target.getLsbD t.val = m.testBit t.val)
    (bits : ∀ t : Fin 5, s.getLsbD t.val = m.testBit t.val) : s = target :=
  BitVec.eq_of_getLsbD_eq fun j hj => (bits ⟨j, hj⟩).trans (targetBits ⟨j, hj⟩).symm

private theorem mask2 : ∀ t : Fin 5, (2 : BitVec 5).getLsbD t.val = (2 : Nat).testBit t.val := by
  decide +kernel

private theorem mask20 : ∀ t : Fin 5, (20 : BitVec 5).getLsbD t.val = (20 : Nat).testBit t.val := by
  decide +kernel

private theorem mask26 : ∀ t : Fin 5, (26 : BitVec 5).getLsbD t.val = (26 : Nat).testBit t.val := by
  decide +kernel

end PEqualNP.Outside.L_meta_50051_aux

open PEqualNP.Outside.L_meta_50051_aux in
theorem PEqualNP.Outside.L_meta_50051 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (20 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val)) := by
  intro h
  obtain ⟨D, p, q, r, fanIn, _, nots, size, table⟩ := h
  obtain ⟨bank, reached, taps⟩ := trace D fanIn
  obtain ⟨sp, hp, bp⟩ := taps p
  obtain ⟨sq, hq, bq⟩ := taps q
  obtain ⟨sr, hr, br⟩ := taps r
  have ep : sp = (2 : Sig) := matchesMask mask2 fun t => (bp t).trans (table t).1
  have eq : sq = (20 : Sig) := matchesMask mask20 fun t => (bq t).trans (table t).2.1
  have er : sr = (26 : Sig) := matchesMask mask26 fun t => (br t).trans (table t).2.2
  exact excluded reached size nots ⟨ep ▸ hp, eq ▸ hq, er ▸ hr⟩
