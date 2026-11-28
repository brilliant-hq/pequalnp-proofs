import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50528

open CircuitLowerBounds

abbrev Mask := BitVec 6

def initial : List Mask := [62, 60, 56, 48, 32, 0, 63]

def targets : List Mask := [8, 41, 45]

def missing (s : List Mask) : List Mask := targets.filter fun x => !s.contains x

def pairs : List Mask → List (Mask × Mask)
  | [] => []
  | a :: s => (a, a) :: (s.map fun b => (a, b)) ++ pairs s

def moves (s : List Mask) : List (Mask × Nat) :=
  ((pairs s).map (fun ab => (ab.1 &&& ab.2, (0 : Nat))) ++
    (pairs s).map (fun ab => (ab.1 ||| ab.2, (0 : Nat))) ++
    s.map (fun a => (~~~a, (1 : Nat))))

def canMerge (s : List Mask) (x : Mask) : Bool :=
  s.any fun a =>
    (a &&& x == x && s.any (fun b => a &&& b == x)) ||
    (a ||| x == x && s.any (fun b => a ||| b == x))

def next (s : List Mask) (g k : Nat) : List (Mask × Nat) :=
  let m := missing s
  if m.length = g then
    m.flatMap fun x =>
      (if canMerge s x then [(x, 0)] else []) ++
      (if decide (1 ≤ k) && s.contains (~~~x) then [(x, 1)] else [])
  else ((moves s).filter fun (x, c) => !s.contains x && decide (c ≤ k)).eraseDups

def search : Nat → Nat → List Mask → Bool
  | 0, _, s => (missing s).isEmpty
  | g + 1, k, s =>
    let m := (missing s).length
    if m = 0 then true
    else if g + 1 < m then false
    else (next s (g + 1) k).any fun (x, c) => search g (k - c) (x :: s)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_1_1_1 : search 5 1 (1 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_1_1_3 : search 5 1 (3 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_1_1_7 : search 5 1 (7 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_1_14_15 : search 4 1 (14 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_1_12_15 : search 4 1 (12 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_1_8_15 : search 4 1 (8 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_1_47_15 : search 4 1 (47 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_0_1_15 : search 4 0 (1 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_0_3_15 : search 4 0 (3 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_0_7_15 : search 4 0 (7 :: 15 :: initial) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_2_0_31_15 : search 4 0 (31 :: 15 :: initial) = false := by decide +kernel

lemma checked_1_1_15 : search 5 1 (15 :: initial) = false := by
  have h : next (15 :: initial) 5 1 = [(14, 0), (12, 0), (8, 0), (47, 0), (1, 1), (3, 1), (7, 1), (31, 1)] := by decide +kernel
  change (next (15 :: initial) 5 1).any
    (fun (x, c) => search 4 (1 - c) (x :: (15 :: initial))) = false
  rw [h]
  simp only [List.any_cons, List.any_nil, Nat.reduceSub, Bool.false_or,
    checked_2_1_14_15, checked_2_1_12_15, checked_2_1_8_15, checked_2_1_47_15, checked_2_0_1_15, checked_2_0_3_15, checked_2_0_7_15, checked_2_0_31_15]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma checked_1_1_31 : search 5 1 (31 :: initial) = false := by decide +kernel

lemma search_initial : search 6 2 initial = false := by
  have h : next initial 6 2 = [(1, 1), (3, 1), (7, 1), (15, 1), (31, 1)] := by decide +kernel
  change (next initial 6 2).any
    (fun (x, c) => search 5 (2 - c) (x :: initial)) = false
  rw [h]
  simp only [List.any_cons, List.any_nil, Nat.reduceSub, Bool.false_or,
    checked_1_1_1, checked_1_1_3, checked_1_1_7, checked_1_1_15, checked_1_1_31]

lemma mem_pairs {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    (a, b) ∈ pairs s ∨ (b, a) ∈ pairs s := by
  induction s with
  | nil => simp at ha
  | cons c s ih =>
    have hfront {x} (hx : x ∈ s) : (c, x) ∈ pairs (c :: s) := by
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
    have htail {x y} (hxy : (x, y) ∈ pairs s) : (x, y) ∈ pairs (c :: s) :=
      List.mem_cons_of_mem _ (List.mem_append_right _ hxy)
    rcases List.mem_cons.mp ha with rfl | ha'
    · left
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact List.mem_cons_self
      · exact hfront hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (hfront ha')
      · exact (ih ha' hb').imp htail htail

lemma move_and {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    (a &&& b, 0) ∈ moves s := by
  simp only [moves, List.mem_append]
  refine Or.inl (Or.inl ?_)
  rcases mem_pairs ha hb with h | h
  · exact List.mem_map.mpr ⟨(a, b), h, rfl⟩
  · exact List.mem_map.mpr ⟨(b, a), h, by exact congrArg (fun x : Mask => (x, 0)) (BitVec.and_comm _ _)⟩

lemma move_or {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    (a ||| b, 0) ∈ moves s := by
  simp only [moves, List.mem_append]
  refine Or.inl (Or.inr ?_)
  rcases mem_pairs ha hb with h | h
  · exact List.mem_map.mpr ⟨(a, b), h, rfl⟩
  · exact List.mem_map.mpr ⟨(b, a), h, by exact congrArg (fun x : Mask => (x, 0)) (BitVec.or_comm _ _)⟩

lemma move_not {s : List Mask} {a : Mask} (ha : a ∈ s) :
    (~~~a, 1) ∈ moves s := by
  simp only [moves, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)

lemma pair_operands {s : List Mask} {a b : Mask} (h : (a, b) ∈ pairs s) : a ∈ s ∧ b ∈ s := by
  induction s with
  | nil => simp [pairs] at h
  | cons c s ih =>
    change (a, b) ∈ (c, c) :: ((s.map fun x => (c, x)) ++ pairs s) at h
    rcases List.mem_cons.mp h with he | hs
    · cases he
      simp
    · rcases List.mem_append.mp hs with hm | hp
      · obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
        cases he
        exact ⟨by simp, List.mem_cons_of_mem _ hx⟩
      · exact (ih hp).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

lemma canMerge_and {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    canMerge s (a &&& b) = true := by
  apply List.any_eq_true.mpr
  refine ⟨a, ha, ?_⟩
  have h : s.any (fun x => a &&& x == a &&& b) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp⟩
  simp [← BitVec.and_assoc, h]

lemma canMerge_or {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    canMerge s (a ||| b) = true := by
  apply List.any_eq_true.mpr
  refine ⟨a, ha, ?_⟩
  have h : s.any (fun x => a ||| x == a ||| b) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp⟩
  simp [← BitVec.or_assoc, h]

lemma next_tight {s : List Mask} {g k c : Nat} {x : Mask}
    (he : (missing s).length = g) (hx : x ∈ targets) (hf : x ∉ s)
    (hv : (x, c) ∈ moves s) (hc : c ≤ k) : (x, c) ∈ next s g k := by
  simp only [next, he, ite_true, List.mem_flatMap]
  refine ⟨x, by simp [missing, hx, hf], ?_⟩
  simp only [moves, List.mem_append, List.mem_map] at hv
  rcases hv with (⟨⟨a, b⟩, hp, hh⟩ | ⟨⟨a, b⟩, hp, hh⟩) | ⟨a, ha, hh⟩
  · cases hh
    obtain ⟨ha, hb⟩ := pair_operands hp
    exact List.mem_append_left _ (by simp [canMerge_and ha hb])
  · cases hh
    obtain ⟨ha, hb⟩ := pair_operands hp
    exact List.mem_append_left _ (by simp [canMerge_or ha hb])
  · cases hh
    exact List.mem_append_right _ (by simp [ha, hc])

lemma search_done (s : List Mask) (g k : Nat) (h : targets ⊆ s) : search g k s = true := by
  have hm : missing s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hh := List.mem_filter.mp hx
    simpa [h hh.1] using hh.2
  cases g <;> simp [search, hm]

lemma search_step {s : List Mask} {g k c : Nat} {x : Mask}
    (hm : (missing s).length ≤ g + 1) (hx : x ∉ s) (hv : (x, c) ∈ moves s)
    (ht : (missing s).length = g + 1 → x ∈ targets) (hc : c ≤ k)
    (hr : search g (k - c) (x :: s) = true) : search (g + 1) k s = true := by
  simp only [search]
  split
  · rfl
  · rw [ite_eq_right (Nat.not_lt.mpr hm)]
    refine List.any_eq_true.mpr ⟨(x, c), ?_, hr⟩
    by_cases he : (missing s).length = g + 1
    · exact next_tight he (ht he) hx hv hc
    · simp [next, he, hv, hx, hc]

def full : Mask := BitVec.allOnes 6

def evalMask : GateOp → List Mask → Mask
  | .and, v => v.foldr (· &&& ·) full
  | .or, v => v.foldr (· ||| ·) 0
  | .not, v => ~~~(v.headD 0)
  | _, _ => 0

def supported (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

def valid (g : Gate) : Prop := supported g.op ∧ g.inputs.length ≤ 2

def isNot (op : GateOp) : Bool :=
  @decide (op = GateOp.not) (lineDegreeGateOpDecEq op GateOp.not)

def cost (op : GateOp) : Nat := if isNot op then 1 else 0

def notUsed (gs : List Gate) : Nat := (gs.filter fun g => isNot g.op).length

lemma notUsed_cons (g : Gate) (gs : List Gate) : notUsed (g :: gs) = cost g.op + notUsed gs := by
  cases h : isNot g.op <;> simp [notUsed, cost, h, Nat.add_comm]

lemma eval_move {op : GateOp} {v s : List Mask} (ho : supported op) (hl : v.length ≤ 2)
    (hv : v ⊆ s) (h0 : 0 ∈ s) (h1 : full ∈ s) :
    evalMask op v ∈ s ∨ (evalMask op v, cost op) ∈ moves s := by
  cases v with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h0
    · exact Or.inl h1
  | cons a v =>
    have ha : a ∈ s := hv (by simp)
    cases v with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · exact Or.inl (by simpa only [evalMask, List.foldr_cons, List.foldr_nil, full,
          BitVec.and_allOnes] using ha)
      · exact Or.inl (by simpa [evalMask] using ha)
      · exact Or.inr (move_not ha)
    | cons b v =>
      have hb : b ∈ s := hv (by simp)
      cases v with
      | nil =>
        rcases ho with rfl | rfl | rfl
        · change _ ∨ (evalMask .and [a, b], 0) ∈ moves s
          exact Or.inr (by simpa only [evalMask, List.foldr_cons, List.foldr_nil, full,
            BitVec.and_allOnes] using move_and ha hb)
        · change _ ∨ (evalMask .or [a, b], 0) ∈ moves s
          exact Or.inr (by simpa [evalMask] using move_or ha hb)
        · exact Or.inr (move_not ha)
      | cons c v => simp at hl

def appendMask (w : List Mask) (g : Gate) : List Mask :=
  w ++ [evalMask g.op (g.inputs.map fun i => w.getD i 0)]

def run (gs : List Gate) (w : List Mask) : List Mask := gs.foldl appendMask w

lemma run_append (gs : List Gate) (w : List Mask) :
    ∃ tail, run gs w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht, hl⟩ := ih (appendMask w g)
    refine ⟨evalMask g.op (g.inputs.map fun i => w.getD i 0) :: tail, ?_, ?_⟩
    · simpa [run, appendMask, List.append_assoc] using ht
    · simp [hl]

lemma getD_in_or_default {α : Type} (w : List α) (i : Nat) (d : α) :
    w.getD i d ∈ w ∨ w.getD i d = d := by
  by_cases hi : i < w.length
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  · exact Or.inr (List.getD_eq_default _ _ (Nat.le_of_not_gt hi))

lemma missing_le {gs : List Gate} {w s : List Mask}
    (hw : w ⊆ s) (ht : targets ⊆ run gs w) : (missing s).length ≤ gs.length := by
  obtain ⟨tail, he, hl⟩ := run_append gs w
  have hn : targets.Nodup := by decide
  rw [← hl]
  apply List.Nodup.length_le_of_subset (List.Pairwise.filter _ hn)
  intro x hx
  have hh := List.mem_filter.mp hx
  have hxs : x ∉ s := by simpa using hh.2
  have hxt := ht hh.1
  rw [he, List.mem_append] at hxt
  exact hxt.resolve_left (fun h => hxs (hw h))

lemma missing_cons {x : Mask} {s : List Mask} (hx : x ∉ targets) :
    missing (x :: s) = missing s := by
  apply List.filter_congr
  intro y hy
  have hyx : y ≠ x := fun he => hx (he ▸ hy)
  simp [hyx]

lemma search_complete (gs : List Gate) (w s : List Mask) (g k : Nat)
    (hf : ∀ x ∈ gs, valid x) (hg : gs.length ≤ g) (hk : notUsed gs ≤ k)
    (hw : w ⊆ s) (h0 : 0 ∈ s) (h1 : full ∈ s) (ht : targets ⊆ run gs w) :
    search g k s = true := by
  induction gs generalizing w s g k with
  | nil => exact search_done s g k (fun _ h => hw (ht h))
  | cons a gs ih =>
    have hva := hf a (by simp)
    have hrest : ∀ x ∈ gs, valid x := fun x hx => hf x (by simp [hx])
    have ht' : targets ⊆ run gs (appendMask w a) := ht
    have hv : (a.inputs.map fun i => w.getD i 0) ⊆ s := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      rcases getD_in_or_default w i 0 with hm | he
      · exact hw hm
      · rwa [he]
    let x := evalMask a.op (a.inputs.map fun i => w.getD i 0)
    have hx : x ∈ s ∨ (x, cost a.op) ∈ moves s :=
      eval_move hva.1 (by simpa using hva.2) hv h0 h1
    have extend {s' : List Mask} (hs' : s ⊆ s') (hx' : x ∈ s') : appendMask w a ⊆ s' := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hs' (hw hy)
      · rw [List.mem_singleton.mp hy]
        exact hx'
    rw [notUsed_cons] at hk
    simp only [List.length_cons] at hg
    by_cases hxs : x ∈ s
    · exact ih (appendMask w a) s g k hrest (by omega) (by omega)
        (extend (fun _ h => h) hxs) h0 h1 ht'
    · cases g with
      | zero => omega
      | succ g =>
        have hw' : appendMask w a ⊆ x :: s :=
          extend (fun _ => List.mem_cons_of_mem _) (by simp)
        have hm : (missing s).length ≤ g + 1 := (missing_le hw ht).trans hg
        have htarget (he : (missing s).length = g + 1) : x ∈ targets := by
          by_contra hn
          have htail := missing_le hw' ht'
          rw [missing_cons hn, he] at htail
          omega
        apply search_step hm hxs (hx.resolve_left hxs) htarget (Nat.le_trans (Nat.le_add_right _ _) hk)
        exact ih (appendMask w a) (x :: s) g (k - cost a.op) hrest (by omega) (by omega)
          hw' (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) ht'

def bit (t : Fin 6) (x : Mask) : Bool := x.getLsbD t.val

lemma bit_zero (t : Fin 6) : bit t 0 = false := by simp [bit]

lemma bit_full (t : Fin 6) : bit t full = true := by
  simp only [bit, full, BitVec.getLsbD_allOnes, t.isLt, decide_true]

lemma eval_map (t : Fin 6) (op : GateOp) (v : List Mask) (ho : supported op) :
    bit t (evalMask op v) = op.eval (v.map (bit t)) := by
  rcases ho with rfl | rfl | rfl
  · induction v with
    | nil => exact bit_full t
    | cons a v ih =>
      change bit t (a &&& evalMask .and v) = (bit t a && GateOp.and.eval (v.map (bit t)))
      rw [← ih]
      exact BitVec.getLsbD_and
  · induction v with
    | nil => exact bit_zero t
    | cons a v ih =>
      change bit t (a ||| evalMask .or v) = (bit t a || GateOp.or.eval (v.map (bit t)))
      rw [← ih]
      exact BitVec.getLsbD_or
  · cases v with
    | nil => exact bit_full t
    | cons a v =>
      change (~~~a).getLsbD t.val = !(a.getLsbD t.val)
      simp only [BitVec.getLsbD_not, t.isLt, decide_true, Bool.true_and]

lemma appendMask_map (t : Fin 6) (w : List Mask) (g : Gate) (h : supported g.op) :
    (appendMask w g).map (bit t) = (w.map (bit t)) ++
      [g.op.eval (g.inputs.map fun i => (w.map (bit t)).getD i false)] := by
  have hm : (g.inputs.map fun i => w.getD i 0).map (bit t) =
      g.inputs.map fun i => (w.map (bit t)).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    change bit t (w.getD i 0) = _
    rw [← List.getD_map w (0 : Mask) (bit t), bit_zero]
  simp only [appendMask, List.map_append, List.map_cons, List.map_nil, eval_map t _ _ h, hm]

lemma run_map (t : Fin 6) (gs : List Gate) (w : List Mask) (hf : ∀ g ∈ gs, valid g) :
    (run gs w).map (bit t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (bit t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h : valid g := hf g (by simp)
    have hgs : ∀ a ∈ gs, valid a := fun a ha => hf a (by simp [ha])
    change (run gs (appendMask w g)).map (bit t) = _
    rw [ih _ hgs, appendMask_map t w g h.1]
    rfl

def input (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]

lemma initial_map : ∀ t : Fin 6, initial.map (bit t) = input t := by decide +kernel

lemma gates_valid (D : Circuit) (hf : MetaComplexity.FanInTwo D) : ∀ g ∈ D.gates, valid g := by
  intro g hg
  simpa [valid, supported] using hf g hg

lemma output_mem (D : Circuit) (hf : ∀ g ∈ D.gates, valid g) (j : Fin (7 + D.size)) (m : Mask)
    (h : ∀ t : Fin 6, (D.wires (input t)).getD j.val false = bit t m) : m ∈ run D.gates initial := by
  let w := run D.gates initial
  have he : w.getD j.val 0 = m := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let t : Fin 6 := ⟨i, hi⟩
    change bit t (w.getD j.val 0) = bit t m
    rw [← List.getD_map w (0 : Mask) (bit t), bit_zero]
    change ((run D.gates initial).map (bit t)).getD j.val false = _
    rw [run_map t _ _ hf, initial_map t]
    exact h t
  rw [← he]
  obtain ⟨tail, ht, hl⟩ := run_append D.gates initial
  have hlt : j.val < w.length := by
    change j.val < (run D.gates initial).length
    rw [ht, List.length_append, hl]
    exact j.isLt
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

end PEqualNP.Outside.L_meta_50528

open PEqualNP.Outside.L_meta_50528 in
theorem PEqualNP.Outside.L_meta_50528 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (41 : Nat).testBit t.val ∧
    w.getD r.val false = (45 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hf, _, hk, hg, ht⟩
  have hv := gates_valid D hf
  have hp := output_mem D hv p 8 (fun t => (ht t).1)
  have hq := output_mem D hv q 41 (fun t => (ht t).2.1)
  have hr := output_mem D hv r 45 (fun t => (ht t).2.2)
  have hall : targets ⊆ run D.gates initial := by
    intro x hx
    simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hs := search_complete D.gates initial initial 6 2 hv hg hk (fun _ h => h)
    (by decide) (by decide) hall
  rw [search_initial] at hs
  cases hs
