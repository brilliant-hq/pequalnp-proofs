import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50269

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev Mask := BitVec 6

def bits (m : Mask) (t : Fin 6) : Bool := m.getLsbD t.val

def initial : List Mask := [62, 60, 56, 48, 32, 0, 63]

def row (t : Fin 6) : List Bool :=
  (List.ofFn fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]

def goal (W : List Mask) : Prop :=
  (4 : Mask) ∈ W ∧ (38 : Mask) ∈ W ∧ (40 : Mask) ∈ W

def missing (W : List Mask) : Nat :=
  (if (4 : Mask) ∈ W then 0 else 1) +
    (if (38 : Mask) ∈ W then 0 else 1) +
    (if (40 : Mask) ∈ W then 0 else 1)

def allowed (W : List Mask) (v : Mask) (cost : Nat) : Bool :=
  match cost with
  | 0 => W.any fun a => W.any fun b => decide (a &&& b = v ∨ a ||| b = v)
  | 1 => W.any fun a => decide (~~~a = v)
  | _ => false

def domain : List Mask := (List.finRange 64).map BitVec.ofFin

lemma in_domain (v : Mask) : v ∈ domain := by
  apply List.mem_map.mpr
  exact ⟨v.toFin, List.mem_finRange _, rfl⟩


def insertMask (v : Mask) : List Mask → List Mask
  | [] => [v]
  | w :: W => if v.toNat ≤ w.toNat then v :: w :: W else w :: insertMask v W

lemma mem_insertMask (v x : Mask) (W : List Mask) :
    x ∈ insertMask v W ↔ x = v ∨ x ∈ W := by
  induction W with
  | nil => simp [insertMask]
  | cons w W ih =>
    simp only [insertMask]
    split
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]
      exact or_left_comm

def branchCandidates (k : Nat) (W : List Mask) : List Mask :=
  if missing W ≤ k then domain else [4, 38, 40]

def branches (k n : Nat) (W : List Mask) : List (Nat × List Mask) :=
  (branchCandidates k W).flatMap fun v =>
    if v ∈ W then []
    else
      [0, 1].filterMap fun cost =>
        if n < cost then none
        else if allowed W v cost then some (n - cost, insertMask v W) else none


def search : Nat → Nat → List Mask → Bool
  | 0, _, W => decide (missing W = 0)
  | k + 1, n, W =>
    if missing W = 0 then true
    else if k + 1 < missing W then false
    else (branches k n W).any fun p => search k p.1 p.2

lemma search_dead (k n : Nat) (W : List Mask) (h : missing W ≠ 0)
    (bad : ∀ p ∈ branches k n W, search k p.1 p.2 = false) :
    search (k + 1) n W = false := by
  simp only [search, h, ite_false]
  split
  · rfl
  · exact List.any_eq_false.mpr (fun p hp => by simp [bad p hp])


def evaluate (W : List Mask) (g : Gate) : Mask :=
  let args := g.inputs.map fun i => W.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) 63
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def push (W : List Mask) (g : Gate) : List Mask := W ++ [evaluate W g]

def price (g : Gate) : Nat :=
  match g.op with
  | .not => 1
  | _ => 0

def priceList : List Gate → Nat
  | [] => 0
  | g :: gs => price g + priceList gs

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

lemma priceList_eq (gs : List Gate) :
    priceList gs = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  unfold PEqualNP.NotBracket.notCount
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨op, inputs⟩
    cases op <;> simp [priceList, price, ih, Nat.add_comm]

lemma bits_zero (t : Fin 6) : bits 0 t = false := by simp [bits]

lemma bits_all (t : Fin 6) : bits 63 t = true := by decide +kernel +revert

lemma bits_get (W : List Mask) (i : Nat) (t : Fin 6) :
    bits (W.getD i 0) t = (W.map (fun w => bits w t)).getD i false := by
  induction W generalizing i with
  | nil => simp [bits]
  | cons a W ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma all_bits_fold (L : List Mask) (t : Fin 6) :
    bits (L.foldr (· &&& ·) 63) t = (L.map fun w => bits w t).all id := by
  induction L with
  | nil => simpa using bits_all t
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.all_cons, id_eq]
    unfold bits at *
    rw [BitVec.getLsbD_and, ih]

lemma any_bits_fold (L : List Mask) (t : Fin 6) :
    bits (L.foldr (· ||| ·) 0) t = (L.map fun w => bits w t).any id := by
  induction L with
  | nil => simpa using bits_zero t
  | cons a L ih =>
    simp only [List.foldr_cons, List.map_cons, List.any_cons, id_eq]
    unfold bits at *
    rw [BitVec.getLsbD_or, ih]

lemma bits_head (L : List Mask) (t : Fin 6) :
    bits (L.headD 0) t = (L.map fun w => bits w t).headD false := by
  cases L with
  | nil => exact bits_zero t
  | cons => rfl

lemma evaluate_bits (W : List Mask) (g : Gate) (t : Fin 6)
    (h : legal g) :
    bits (evaluate W g) t =
      g.op.eval (g.inputs.map fun i => (W.map fun w => bits w t).getD i false) := by
  have he (L : List Nat) :
      ((L.map fun i => W.getD i 0).map fun w => bits w t) =
        L.map fun i => (W.map fun w => bits w t).getD i false := by
    simp only [List.map_map, Function.comp_def, bits_get]
  obtain ⟨op, inp⟩ := g
  rcases h.1 with ha | ho | hn
  · change op = .and at ha
    subst op
    change bits ((inp.map fun i => W.getD i 0).foldr (· &&& ·) 63) t = _
    exact (all_bits_fold _ t).trans (congrArg (fun L => L.all id) (he inp))
  · change op = .or at ho
    subst op
    change bits ((inp.map fun i => W.getD i 0).foldr (· ||| ·) 0) t = _
    exact (any_bits_fold _ t).trans (congrArg (fun L => L.any id) (he inp))
  · change op = .not at hn
    subst op
    change bits (~~~((inp.map fun i => W.getD i 0).headD 0)) t = _
    unfold bits
    rw [BitVec.getLsbD_not]
    have ht : t.val < 6 := t.isLt
    rw [decide_eq_true ht, Bool.true_and]
    exact congrArg Bool.not ((bits_head _ t).trans (congrArg (fun L => L.headD false) (he inp)))

lemma lift_fold (gs : List Gate) (h : ∀ g ∈ gs, legal g) (W : List Mask) (t : Fin 6) :
    (gs.foldl push W).map (fun w => bits w t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun w => bits w t) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have hgs : ∀ a ∈ gs, legal a := fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [List.foldl_cons]
    rw [ih hgs]
    simp [push, evaluate_bits _ _ _ hg]

lemma initial_row (t : Fin 6) : initial.map (fun w => bits w t) = row t := by
  decide +kernel +revert

lemma member_getD {W : List Mask} {S : List Mask} (sub : W ⊆ S)
    (z : (0 : Mask) ∈ S) (i : Nat) : W.getD i 0 ∈ S := by
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact sub (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact z

lemma move_and {a b : Mask} {S : List Mask} (ha : a ∈ S) (hb : b ∈ S) :
    allowed S (a &&& b) 0 = true := by
  exact List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, by simp⟩⟩

lemma move_or {a b : Mask} {S : List Mask} (ha : a ∈ S) (hb : b ∈ S) :
    allowed S (a ||| b) 0 = true := by
  exact List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, by simp⟩⟩

lemma move_not {a : Mask} {S : List Mask} (ha : a ∈ S) :
    allowed S (~~~a) 1 = true := by
  exact List.any_eq_true.mpr ⟨a, ha, by simp⟩

lemma and_identity (x : Mask) : x &&& (63 : Mask) = x := by
  exact (show x &&& BitVec.allOnes 6 = x from BitVec.and_allOnes)


lemma get_move (W S : List Mask) (g : Gate) (sub : W ⊆ S)
    (z : (0 : Mask) ∈ S) (o : (63 : Mask) ∈ S) (h : legal g) :
    allowed S (evaluate W g) (price g) = true := by
  have hw i := member_getD sub z i
  obtain ⟨op, inp⟩ := g
  have size : inp.length ≤ 2 := h.2
  rcases h.1 with ha | ho | hn
  · change op = .and at ha
    subst op
    rcases inp with _ | ⟨i, _ | ⟨j, _ | ⟨l, ls⟩⟩⟩
    · simpa [evaluate, price] using move_and o o
    · simpa [evaluate, price] using move_and (hw i) o
    · change allowed S (W.getD i 0 &&& (W.getD j 0 &&& 63)) 0 = true
      rw [and_identity]
      exact move_and (hw i) (hw j)
    · simp at size
  · change op = .or at ho
    subst op
    rcases inp with _ | ⟨i, _ | ⟨j, _ | ⟨l, ls⟩⟩⟩
    · simpa [evaluate, price] using move_or z z
    · simpa [evaluate, price] using move_or (hw i) z
    · simpa [evaluate, price] using move_or (hw i) (hw j)
    · simp at size
  · change op = .not at hn
    subst op
    rcases inp with _ | ⟨i, ls⟩
    · simpa [evaluate, price] using move_not z
    · simpa [evaluate, price] using move_not (hw i)

lemma missing_goal (S : List Mask) (h : goal S) : missing S = 0 := by
  obtain ⟨hp,hq,hr⟩ := h
  simp only [missing, hp, hq, hr, ite_true, Nat.zero_add]

lemma missing_step (v : Mask) (S : List Mask) :
    missing S ≤ missing (v :: S) + 1 := by
  have dpq : (4 : Mask) ≠ 38 := by decide
  have dpr : (4 : Mask) ≠ 40 := by decide
  have dqr : (38 : Mask) ≠ 40 := by decide
  by_cases hp : (4 : Mask) = v
  · subst v
    simp only [missing, List.mem_cons, true_or, ite_true, Ne.symm dpq, Ne.symm dpr, false_or,
      zero_add]
    split_ifs <;> omega
  by_cases hq : (38 : Mask) = v
  · subst v
    simp only [missing, List.mem_cons, true_or, ite_true, dpq, Ne.symm dqr, false_or, add_zero]
    split_ifs <;> omega
  by_cases hr : (40 : Mask) = v
  · subst v
    simp only [missing, List.mem_cons, true_or, ite_true, dpr, dqr, false_or, add_zero]
    split_ifs <;> omega
  simp only [missing, List.mem_cons, hp, hq, hr, false_or]
  omega

lemma missing_unchanged (v : Mask) (W : List Mask) (nv : v ∉ ([4, 38, 40] : List Mask)) :
    missing (insertMask v W) = missing W := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at nv
  obtain ⟨h4, h38, h40⟩ := nv
  simp only [missing, mem_insertMask, Ne.symm h4, Ne.symm h38, Ne.symm h40, false_or]


lemma sub_push (W S : List Mask) (g : Gate) (sub : W ⊆ S)
    (h : evaluate W g ∈ S) : push W g ⊆ S := by
  intro j hj
  simp only [push, List.mem_append, List.mem_singleton] at hj
  rcases hj with hw | rfl
  · exact sub hw
  · exact h

lemma missing_bound (gs : List Gate) (W S : List Mask) (sub : W ⊆ S)
    (g : goal (gs.foldl push W)) : missing S ≤ gs.length := by
  induction gs generalizing W S with
  | nil =>
    exact Nat.le_of_eq (missing_goal S ⟨sub g.1, sub g.2.1, sub g.2.2⟩)
  | cons a gs ih =>
    have hs : push W a ⊆ evaluate W a :: S :=
      sub_push W _ a (fun _ hx => List.mem_cons_of_mem _ (sub hx)) (by simp)
    have hb := ih _ _ hs g
    have hstep := missing_step (evaluate W a) S
    simp only [List.length_cons]
    omega

lemma search_hit (S : List Mask) (k n : Nat) (h : missing S = 0) :
    search k n S = true := by
  cases k <;> simp [search, h]

lemma search_sound (gs : List Gate) (W S : List Mask) (k n : Nat)
    (sub : W ⊆ S) (z : (0 : Mask) ∈ S) (o : (63 : Mask) ∈ S)
    (ok : ∀ g ∈ gs, legal g) (hLen : gs.length ≤ k) (hNot : priceList gs ≤ n)
    (go : goal (gs.foldl push W)) : search k n S = true := by
  induction gs generalizing W S k n with
  | nil =>
    exact search_hit S k n (missing_goal S ⟨sub go.1, sub go.2.1, sub go.2.2⟩)
  | cons a gs ih =>
    have ht : ∀ g ∈ gs, legal g := fun g hg => ok g (List.mem_cons_of_mem _ hg)
    have htail : gs.length ≤ k := by simpa using Nat.le_trans (Nat.le_succ gs.length) hLen
    have hn : price a + priceList gs ≤ n := hNot
    by_cases hv : evaluate W a ∈ S
    · exact ih _ _ k n (sub_push W S a sub hv) z o ht htail (by omega) go
    by_cases hhit : missing S = 0
    · exact search_hit S k n hhit
    have hm := missing_bound (a :: gs) W S sub go
    cases k with
    | zero => simp at hLen
    | succ k =>
      let S' := insertMask (evaluate W a) S
      have wsub : W ⊆ S' :=
        fun _ h => (mem_insertMask _ _ _).mpr (Or.inr (sub h))
      have ss : push W a ⊆ S' :=
        sub_push W _ a wsub ((mem_insertMask _ _ _).mpr (Or.inl rfl))
      simp only [List.length_cons] at hLen hm
      have hEnough : ¬k + 1 < missing S := by omega
      have hremain : missing S' ≤ k := Nat.le_trans (missing_bound gs _ _ ss go) (by omega)
      have hcost : ¬n < price a := by omega
      have hcandidate : evaluate W a ∈ branchCandidates k S := by
        unfold branchCandidates
        split
        · exact in_domain _
        · rename_i tight
          by_contra hv
          have hm' : missing S' = missing S :=
            missing_unchanged (evaluate W a) S hv
          omega
      have entry : (n - price a, S') ∈ branches k n S := by
        apply List.mem_flatMap.mpr
        refine ⟨evaluate W a, hcandidate, ?_⟩
        simp only [hv, ite_false]
        apply List.mem_filterMap.mpr
        refine ⟨price a, ?_, ?_⟩
        · cases ha : a.op <;> simp [price, ha]
        · simp only [hcost, ite_false, get_move W S a sub z o (ok a (by simp)), ite_true]
          rfl

      simp only [search, hhit, ite_false, hEnough]
      apply List.any_eq_true.mpr
      refine ⟨(n - price a, S'), entry, ?_⟩
      exact ih _ _ _ _ ss ((mem_insertMask _ _ _).mpr (Or.inr z))
        ((mem_insertMask _ _ _).mpr (Or.inr o)) ht (by omega) (by omega) go


lemma masks_eq (x y : Mask) (h : ∀ t : Fin 6, bits x t = bits y t) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact h ⟨j, hj⟩

lemma output_in (W : List Mask) (i : Nat) (hi : i < W.length) (v : Mask)
    (h : ∀ t : Fin 6, (W.map fun w => bits w t).getD i false = bits v t) : v ∈ W := by
  have hv : W.getD i 0 = v :=
    masks_eq _ _ (fun t => (bits_get W i t).trans (h t))
  rw [← hv, List.getD_eq_getElem _ _ hi]
  apply List.getElem_mem

lemma push_length (gs : List Gate) (W : List Mask) :
    (gs.foldl push W).length = W.length + gs.length := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, push, List.length_append, List.length_cons, List.length_nil]
    omega

theorem bank_0 : search 3 0 [0, 1, 2, 3, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 2, 3, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_1 : search 3 0 [0, 1, 3, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_2 : search 3 0 [0, 1, 3, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_3 : search 3 0 [0, 1, 3, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_4 : search 3 0 [0, 1, 3, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_5 : search 3 0 [0, 1, 3, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_6 : search 3 0 [0, 1, 3, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_7 : search 3 0 [0, 1, 3, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 3, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_8 : search 4 0 [0, 1, 3, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 1, 3, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 2, 3, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 3, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 3, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 1, 3, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 3, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 1, 3, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 3, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 1, 3, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_0
  · exact bank_1
  · exact bank_2
  · exact bank_3
  · exact bank_4
  · exact bank_5
  · exact bank_6
  · exact bank_7

theorem bank_9 : search 2 0 [0, 1, 4, 5, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 5, 7, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_10 : search 1 0 [0, 1, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 1, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_11 : search 2 0 [0, 1, 4, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_10

theorem bank_12 : search 2 0 [0, 1, 4, 7, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_13 : search 2 0 [0, 1, 4, 7, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 36, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_14 : search 1 0 [0, 1, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 1, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_15 : search 2 0 [0, 1, 4, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_14

theorem bank_16 : search 2 0 [0, 1, 4, 7, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_17 : search 2 0 [0, 1, 4, 7, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_18 : search 2 0 [0, 1, 4, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_19 : search 2 0 [0, 1, 4, 7, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_20 : search 2 0 [0, 1, 4, 7, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 7, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_21 : search 3 0 [0, 1, 4, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 4, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 5, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 4, 7, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_9
  · exact bank_11
  · exact bank_12
  · exact bank_13
  · exact bank_15
  · exact bank_16
  · exact bank_17
  · exact bank_18
  · exact bank_19
  · exact bank_20

theorem bank_22 : search 2 0 [0, 1, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_10

theorem bank_23 : search 3 0 [0, 1, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_11
  · exact bank_22

theorem bank_24 : search 3 0 [0, 1, 7, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 33, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 33, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_12

theorem bank_25 : search 2 0 [0, 1, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_14

theorem bank_26 : search 3 0 [0, 1, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_15
  · exact bank_25

theorem bank_27 : search 3 0 [0, 1, 7, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 48, 49, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 49, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_16

theorem bank_28 : search 3 0 [0, 1, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_18

theorem bank_29 : search 3 0 [0, 1, 7, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_19

theorem bank_30 : search 3 0 [0, 1, 7, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 7, 32, 48, 56, 60, 61, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_20

theorem bank_31 : search 4 0 [0, 1, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 1, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_21
  · exact bank_23
  · exact bank_24
  · exact bank_26
  · exact bank_27
  · exact bank_28
  · exact bank_29
  · exact bank_30

theorem bank_32 : search 2 0 [0, 1, 8, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 8, 15, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_33 : search 3 0 [0, 1, 8, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 8, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 8, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_32

theorem bank_34 : search 3 0 [0, 1, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 12, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_35 : search 3 0 [0, 1, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 14, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_36 : search 3 0 [0, 1, 15, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 15, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_37 : search 2 0 [0, 1, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_38 : search 3 0 [0, 1, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 15, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 1, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_37

theorem bank_39 : search 3 0 [0, 1, 15, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 15, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_40 : search 3 0 [0, 1, 15, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 15, 32, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_41 : search 3 0 [0, 1, 15, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 15, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_42 : search 4 0 [0, 1, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 1, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_33
  · exact bank_34
  · exact bank_35
  · exact bank_36
  · exact bank_38
  · exact bank_39
  · exact bank_40
  · exact bank_41

theorem bank_43 : search 3 0 [0, 1, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 16, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_44 : search 3 0 [0, 1, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 24, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_45 : search 3 0 [0, 1, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_46 : search 3 0 [0, 1, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_47 : search 3 0 [0, 1, 31, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 31, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_48 : search 3 0 [0, 1, 31, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 31, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_49 : search 3 0 [0, 1, 31, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 31, 32, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_50 : search 3 0 [0, 1, 31, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 31, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_51 : search 4 0 [0, 1, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 1, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_43
  · exact bank_44
  · exact bank_45
  · exact bank_46
  · exact bank_47
  · exact bank_48
  · exact bank_49
  · exact bank_50

theorem bank_52 : search 3 0 [0, 1, 30, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 30, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_53 : search 3 1 [0, 1, 32, 33, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 33, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_54 : search 3 1 [0, 1, 32, 33, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 33, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_55 : search 3 1 [0, 1, 32, 33, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 33, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_56 : search 4 1 [0, 1, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 1, 32, 33, 48, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 30, 32, 33, 48, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 33, 48, 56, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 49, 56, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_1
  · exact bank_24
  · exact bank_36
  · exact bank_52
  · exact bank_47
  · exact bank_53
  · exact bank_54
  · exact bank_55

theorem bank_57 : search 3 0 [0, 1, 14, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 14, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_58 : search 3 1 [0, 1, 32, 48, 49, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 48, 49, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_59 : search 3 1 [0, 1, 32, 48, 49, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 48, 49, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_60 : search 4 1 [0, 1, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 1, 32, 48, 49, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 14, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 49, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 49, 56, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 49, 56, 60, 62, 63]), (1, [0, 1, 32, 48, 49, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 48, 49, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_3
  · exact bank_27
  · exact bank_57
  · exact bank_39
  · exact bank_48
  · exact bank_53
  · exact bank_58
  · exact bank_59

theorem bank_61 : search 1 0 [0, 1, 4, 6, 32, 38, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 1, 4, 6, 32, 38, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_62 : search 2 0 [0, 1, 4, 6, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 4, 6, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 1, 4, 6, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_61

theorem bank_63 : search 2 0 [0, 1, 6, 32, 38, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 1, 6, 32, 38, 48, 56, 57, 60, 62, 63] = [(0, [0, 1, 4, 6, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_61

theorem bank_64 : search 3 0 [0, 1, 6, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 6, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 1, 4, 6, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 6, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_62
  · exact bank_63

theorem bank_65 : search 3 1 [0, 1, 32, 48, 56, 57, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 1, 32, 48, 56, 57, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_66 : search 4 1 [0, 1, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 1, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 6, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 48, 49, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 48, 56, 57, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_5
  · exact bank_64
  · exact bank_29
  · exact bank_40
  · exact bank_49
  · exact bank_54
  · exact bank_58
  · exact bank_65

theorem bank_67 : search 3 0 [0, 1, 2, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 1, 2, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_68 : search 4 1 [0, 1, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 1, 32, 48, 56, 60, 61, 62, 63] = [(0, [0, 1, 2, 32, 48, 56, 60, 61, 62, 63]), (0, [0, 1, 3, 32, 48, 56, 60, 61, 62, 63]), (0, [0, 1, 7, 32, 48, 56, 60, 61, 62, 63]), (0, [0, 1, 15, 32, 48, 56, 60, 61, 62, 63]), (0, [0, 1, 31, 32, 48, 56, 60, 61, 62, 63]), (1, [0, 1, 32, 33, 48, 56, 60, 61, 62, 63]), (1, [0, 1, 32, 48, 49, 56, 60, 61, 62, 63]), (1, [0, 1, 32, 48, 56, 57, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_67
  · exact bank_7
  · exact bank_30
  · exact bank_41
  · exact bank_50
  · exact bank_55
  · exact bank_59
  · exact bank_65

theorem bank_69 : search 5 1 [0, 1, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 4 1 [0, 1, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 1, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 1, 32, 33, 48, 56, 60, 62, 63]), (1, [0, 1, 32, 48, 49, 56, 60, 62, 63]), (1, [0, 1, 32, 48, 56, 57, 60, 62, 63]), (1, [0, 1, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_8
  · exact bank_31
  · exact bank_42
  · exact bank_51
  · exact bank_56
  · exact bank_60
  · exact bank_66
  · exact bank_68

theorem bank_70 : search 2 0 [0, 2, 3, 4, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 2, 3, 4, 7, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_71 : search 3 0 [0, 2, 3, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 2, 3, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 2, 3, 4, 7, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_70

theorem bank_72 : search 3 0 [0, 2, 3, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 2, 3, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_73 : search 3 0 [0, 2, 3, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 2, 3, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_74 : search 3 1 [0, 2, 3, 32, 34, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 34, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_75 : search 3 1 [0, 2, 3, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_76 : search 3 1 [0, 2, 3, 32, 48, 50, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 48, 50, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_77 : search 3 1 [0, 2, 3, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_78 : search 3 1 [0, 2, 3, 32, 48, 56, 58, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 48, 56, 58, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_79 : search 2 0 [0, 2, 3, 4, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 2, 3, 4, 32, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_80 : search 3 1 [0, 2, 3, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 2, 3, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 2, 3, 4, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_79

theorem bank_81 : search 3 0 [0, 2, 3, 32, 48, 56, 60, 61, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 2, 3, 32, 48, 56, 60, 61, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_82 : search 4 1 [0, 2, 3, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 2, 3, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 2, 3, 32, 48, 56, 60, 62, 63]), (0, [0, 2, 3, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 2, 3, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 2, 3, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 34, 48, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 35, 48, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 50, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 51, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 56, 58, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 2, 3, 32, 48, 56, 60, 61, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_0
  · exact bank_71
  · exact bank_72
  · exact bank_73
  · exact bank_74
  · exact bank_75
  · exact bank_76
  · exact bank_77
  · exact bank_78
  · exact bank_80
  · exact bank_81

theorem bank_83 : search 1 0 [0, 3, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 3, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_84 : search 2 0 [0, 3, 4, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_83

theorem bank_85 : search 2 0 [0, 3, 4, 7, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_86 : search 2 0 [0, 3, 4, 7, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 36, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_87 : search 1 0 [0, 3, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 3, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_88 : search 2 0 [0, 3, 4, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_87

theorem bank_89 : search 2 0 [0, 3, 4, 7, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_90 : search 2 0 [0, 3, 4, 7, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_91 : search 2 0 [0, 3, 4, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_92 : search 2 0 [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_93 : search 3 0 [0, 3, 4, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 4, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 2, 3, 4, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_70
  · exact bank_84
  · exact bank_85
  · exact bank_86
  · exact bank_88
  · exact bank_89
  · exact bank_90
  · exact bank_91
  · exact bank_92

theorem bank_94 : search 2 0 [0, 3, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_83

theorem bank_95 : search 3 0 [0, 3, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 6, 7, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_84
  · exact bank_94

theorem bank_96 : search 3 0 [0, 3, 7, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 7, 32, 35, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 35, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_85

theorem bank_97 : search 2 0 [0, 3, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_87

theorem bank_98 : search 3 0 [0, 3, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_88
  · exact bank_97

theorem bank_99 : search 3 0 [0, 3, 7, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 7, 32, 48, 51, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 48, 51, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_89

theorem bank_100 : search 3 0 [0, 3, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 7, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_91

theorem bank_101 : search 3 0 [0, 3, 7, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 7, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_92

theorem bank_102 : search 4 0 [0, 3, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 3, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 2, 3, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_71
  · exact bank_93
  · exact bank_95
  · exact bank_96
  · exact bank_98
  · exact bank_99
  · exact bank_100
  · exact bank_101

theorem bank_103 : search 2 0 [0, 3, 8, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 8, 15, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_104 : search 3 0 [0, 3, 8, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 8, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 3, 8, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_103

theorem bank_105 : search 3 0 [0, 3, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 12, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_106 : search 3 0 [0, 3, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 14, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_107 : search 3 0 [0, 3, 15, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 15, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_108 : search 2 0 [0, 3, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_109 : search 3 0 [0, 3, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 15, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 3, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_108

theorem bank_110 : search 3 0 [0, 3, 15, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 15, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_111 : search 3 0 [0, 3, 15, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 15, 32, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_112 : search 4 0 [0, 3, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 3, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 2, 3, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_72
  · exact bank_104
  · exact bank_105
  · exact bank_106
  · exact bank_107
  · exact bank_109
  · exact bank_110
  · exact bank_111

theorem bank_113 : search 3 0 [0, 3, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 16, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_114 : search 3 0 [0, 3, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 24, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_115 : search 3 0 [0, 3, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_116 : search 3 0 [0, 3, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_117 : search 3 0 [0, 3, 31, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 31, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_118 : search 3 0 [0, 3, 31, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 31, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_119 : search 3 0 [0, 3, 31, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 31, 32, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_120 : search 4 0 [0, 3, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 3, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 2, 3, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_73
  · exact bank_113
  · exact bank_114
  · exact bank_115
  · exact bank_116
  · exact bank_117
  · exact bank_118
  · exact bank_119

theorem bank_121 : search 3 0 [0, 3, 28, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 28, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_122 : search 3 1 [0, 3, 32, 34, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 34, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_123 : search 3 1 [0, 3, 32, 35, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 35, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_124 : search 2 0 [0, 3, 4, 32, 35, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 32, 35, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_125 : search 3 1 [0, 3, 32, 35, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 35, 48, 56, 59, 60, 62, 63] = [(0, [0, 3, 4, 32, 35, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_124

theorem bank_126 : search 4 1 [0, 3, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 3, 32, 35, 48, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 35, 48, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 28, 32, 35, 48, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 35, 48, 56, 60, 62, 63]), (1, [0, 3, 32, 34, 35, 48, 56, 60, 62, 63]), (1, [0, 3, 32, 35, 48, 51, 56, 60, 62, 63]), (1, [0, 3, 32, 35, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_2
  · exact bank_75
  · exact bank_96
  · exact bank_107
  · exact bank_121
  · exact bank_117
  · exact bank_122
  · exact bank_123
  · exact bank_125

theorem bank_127 : search 3 0 [0, 3, 12, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 12, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_128 : search 3 1 [0, 3, 32, 48, 50, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 48, 50, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_129 : search 2 0 [0, 3, 4, 32, 48, 51, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 32, 48, 51, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_130 : search 3 1 [0, 3, 32, 48, 51, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 48, 51, 56, 59, 60, 62, 63] = [(0, [0, 3, 4, 32, 48, 51, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_129

theorem bank_131 : search 4 1 [0, 3, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 3, 32, 48, 51, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 51, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 12, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 51, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 51, 56, 60, 62, 63]), (1, [0, 3, 32, 35, 48, 51, 56, 60, 62, 63]), (1, [0, 3, 32, 48, 50, 51, 56, 60, 62, 63]), (1, [0, 3, 32, 48, 51, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_4
  · exact bank_77
  · exact bank_99
  · exact bank_127
  · exact bank_110
  · exact bank_118
  · exact bank_123
  · exact bank_128
  · exact bank_130

theorem bank_132 : search 2 0 [0, 3, 4, 32, 36, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 32, 36, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_133 : search 2 0 [0, 3, 4, 32, 48, 52, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 32, 48, 52, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_134 : search 2 0 [0, 3, 4, 32, 48, 56, 58, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 3, 4, 32, 48, 56, 58, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_135 : search 3 0 [0, 3, 4, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 3, 4, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 2, 3, 4, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 35, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 36, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 48, 51, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 48, 52, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 48, 56, 58, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_79
  · exact bank_92
  · exact bank_124
  · exact bank_132
  · exact bank_129
  · exact bank_133
  · exact bank_134

theorem bank_136 : search 3 1 [0, 3, 32, 48, 56, 58, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 3, 32, 48, 56, 58, 59, 60, 62, 63] = [(0, [0, 3, 4, 32, 48, 56, 58, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_134

theorem bank_137 : search 4 1 [0, 3, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 3, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 56, 59, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 4, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 56, 59, 60, 62, 63]), (1, [0, 3, 32, 35, 48, 56, 59, 60, 62, 63]), (1, [0, 3, 32, 48, 51, 56, 59, 60, 62, 63]), (1, [0, 3, 32, 48, 56, 58, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_6
  · exact bank_80
  · exact bank_135
  · exact bank_101
  · exact bank_111
  · exact bank_119
  · exact bank_125
  · exact bank_130
  · exact bank_136

theorem bank_138 : search 5 1 [0, 3, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 4 1 [0, 3, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 3, 32, 48, 56, 60, 62, 63]), (1, [0, 2, 3, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 3, 32, 35, 48, 56, 60, 62, 63]), (1, [0, 3, 32, 48, 51, 56, 60, 62, 63]), (1, [0, 3, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_8
  · exact bank_82
  · exact bank_102
  · exact bank_112
  · exact bank_120
  · exact bank_126
  · exact bank_131
  · exact bank_137

theorem bank_139 : search 1 0 [0, 4, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_140 : search 2 0 [0, 4, 6, 7, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 6, 7, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_139

theorem bank_141 : search 1 0 [0, 4, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_142 : search 2 0 [0, 4, 6, 7, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 6, 7, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_141

theorem bank_143 : search 1 1 [0, 4, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_144 : search 2 1 [0, 4, 6, 7, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 36, 48, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_143

theorem bank_145 : search 1 0 [0, 4, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_146 : search 1 1 [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_147 : search 1 1 [0, 4, 6, 7, 32, 38, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 6, 7, 32, 38, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_148 : search 1 1 [0, 4, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_149 : search 1 1 [0, 4, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_150 : search 1 0 [0, 4, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_151 : search 1 0 [0, 4, 6, 7, 32, 38, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 6, 7, 32, 38, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_152 : search 2 1 [0, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63]), (0, [0, 4, 6, 7, 32, 38, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_10
  · exact bank_83
  · exact bank_139
  · exact bank_145
  · exact bank_141
  · exact bank_143
  · exact bank_146
  · exact bank_147
  · exact bank_148
  · exact bank_149
  · exact bank_150
  · exact bank_151

theorem bank_153 : search 2 1 [0, 4, 6, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_146

theorem bank_154 : search 2 1 [0, 4, 6, 7, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 48, 52, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 48, 52, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_147

theorem bank_155 : search 2 1 [0, 4, 6, 7, 32, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 48, 54, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_148

theorem bank_156 : search 2 1 [0, 4, 6, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 6, 7, 32, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_149

theorem bank_157 : search 2 0 [0, 4, 6, 7, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 6, 7, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 4, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_150

theorem bank_158 : search 2 0 [0, 4, 6, 7, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 6, 7, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 4, 6, 7, 32, 38, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_151

theorem bank_159 : search 3 1 [0, 4, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 4, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 36, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 54, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 6, 7, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 4, 6, 7, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_11
  · exact bank_84
  · exact bank_140
  · exact bank_142
  · exact bank_144
  · exact bank_152
  · exact bank_153
  · exact bank_154
  · exact bank_155
  · exact bank_156
  · exact bank_157
  · exact bank_158

theorem bank_160 : search 1 0 [0, 4, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_161 : search 2 0 [0, 4, 7, 8, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 8, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_160

theorem bank_162 : search 2 0 [0, 4, 7, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 12, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_163 : search 2 0 [0, 4, 7, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 14, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_164 : search 2 0 [0, 4, 7, 15, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 15, 32, 36, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_165 : search 1 0 [0, 4, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_166 : search 2 0 [0, 4, 7, 15, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 15, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_165

theorem bank_167 : search 1 0 [0, 4, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_168 : search 2 0 [0, 4, 7, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 15, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_167

theorem bank_169 : search 2 0 [0, 4, 7, 15, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 15, 32, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_170 : search 2 0 [0, 4, 7, 15, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 15, 32, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_171 : search 3 0 [0, 4, 7, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 4, 7, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_140
  · exact bank_161
  · exact bank_162
  · exact bank_163
  · exact bank_164
  · exact bank_166
  · exact bank_168
  · exact bank_169
  · exact bank_170

theorem bank_172 : search 2 0 [0, 4, 7, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 16, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_173 : search 2 0 [0, 4, 7, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 24, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_174 : search 2 0 [0, 4, 7, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_175 : search 2 0 [0, 4, 7, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_176 : search 2 0 [0, 4, 7, 31, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 31, 32, 36, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_177 : search 1 0 [0, 4, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_178 : search 2 0 [0, 4, 7, 31, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 31, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_177

theorem bank_179 : search 2 0 [0, 4, 7, 31, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 31, 32, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_180 : search 2 0 [0, 4, 7, 31, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 31, 32, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_181 : search 3 0 [0, 4, 7, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 4, 7, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_142
  · exact bank_172
  · exact bank_173
  · exact bank_174
  · exact bank_175
  · exact bank_176
  · exact bank_178
  · exact bank_179
  · exact bank_180

theorem bank_182 : search 2 0 [0, 4, 7, 27, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 27, 32, 36, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_183 : search 1 1 [0, 4, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_184 : search 2 1 [0, 4, 7, 32, 36, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 36, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_183

theorem bank_185 : search 2 1 [0, 4, 7, 32, 36, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 36, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_186 : search 2 1 [0, 4, 7, 32, 36, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 36, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_187 : search 2 0 [0, 4, 7, 32, 36, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 32, 36, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_188 : search 3 1 [0, 4, 7, 32, 36, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 4, 7, 32, 36, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 36, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 27, 32, 36, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 36, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 36, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_13
  · exact bank_86
  · exact bank_144
  · exact bank_164
  · exact bank_182
  · exact bank_176
  · exact bank_184
  · exact bank_185
  · exact bank_186
  · exact bank_187

theorem bank_189 : search 1 0 [0, 4, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_190 : search 2 0 [0, 4, 7, 24, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 24, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_189

theorem bank_191 : search 1 0 [0, 4, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_192 : search 1 1 [0, 4, 7, 32, 38, 39, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 7, 32, 38, 39, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_193 : search 1 1 [0, 4, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_194 : search 1 1 [0, 4, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 1 [0, 4, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_195 : search 1 0 [0, 4, 7, 32, 38, 39, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 32, 38, 39, 48, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_196 : search 2 1 [0, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 38, 39, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 38, 39, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_14
  · exact bank_87
  · exact bank_146
  · exact bank_165
  · exact bank_189
  · exact bank_191
  · exact bank_177
  · exact bank_183
  · exact bank_192
  · exact bank_193
  · exact bank_194
  · exact bank_195

theorem bank_197 : search 2 1 [0, 4, 7, 32, 39, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 39, 48, 52, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 38, 39, 48, 52, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_192

theorem bank_198 : search 2 1 [0, 4, 7, 32, 39, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 39, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_194

theorem bank_199 : search 2 0 [0, 4, 7, 32, 39, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 32, 39, 48, 56, 59, 60, 62, 63] = [(0, [0, 4, 7, 32, 38, 39, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_195

theorem bank_200 : search 3 1 [0, 4, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 4, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 24, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 39, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_15
  · exact bank_88
  · exact bank_153
  · exact bank_166
  · exact bank_190
  · exact bank_178
  · exact bank_184
  · exact bank_196
  · exact bank_197
  · exact bank_198
  · exact bank_199

theorem bank_201 : search 2 0 [0, 4, 7, 11, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 11, 32, 48, 52, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_202 : search 2 1 [0, 4, 7, 32, 48, 52, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 48, 52, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_203 : search 2 0 [0, 4, 7, 32, 48, 52, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 32, 48, 52, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_204 : search 3 1 [0, 4, 7, 32, 48, 52, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 4, 7, 32, 48, 52, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 4, 7, 11, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 48, 52, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 52, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 52, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_17
  · exact bank_90
  · exact bank_154
  · exact bank_201
  · exact bank_169
  · exact bank_179
  · exact bank_185
  · exact bank_197
  · exact bank_202
  · exact bank_203

theorem bank_205 : search 1 0 [0, 4, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 0 0 [0, 4, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_206 : search 2 0 [0, 4, 7, 8, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 8, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_205

theorem bank_207 : search 2 1 [0, 4, 7, 32, 48, 54, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 4, 7, 32, 48, 54, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_208 : search 2 0 [0, 4, 7, 32, 48, 55, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 32, 48, 55, 56, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_209 : search 3 1 [0, 4, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 4, 7, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 8, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 48, 55, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 55, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 52, 55, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 54, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 55, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_18
  · exact bank_91
  · exact bank_156
  · exact bank_206
  · exact bank_170
  · exact bank_180
  · exact bank_186
  · exact bank_198
  · exact bank_202
  · exact bank_207
  · exact bank_208

theorem bank_210 : search 2 0 [0, 4, 7, 32, 48, 56, 58, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 4, 7, 32, 48, 56, 58, 59, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_211 : search 3 0 [0, 4, 7, 32, 48, 56, 59, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 4, 7, 32, 48, 56, 59, 60, 62, 63] = [(0, [0, 3, 4, 7, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 4, 6, 7, 32, 48, 56, 59, 60, 62, 63]), (0, [0, 4, 7, 32, 36, 48, 56, 59, 60, 62, 63]), (0, [0, 4, 7, 32, 39, 48, 56, 59, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 52, 56, 59, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 55, 56, 59, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 56, 58, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_92
  · exact bank_158
  · exact bank_187
  · exact bank_199
  · exact bank_203
  · exact bank_208
  · exact bank_210

theorem bank_212 : search 4 1 [0, 4, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 4, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 4, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 4, 7, 32, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 4, 7, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 36, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 52, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 4, 7, 32, 48, 56, 59, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_21
  · exact bank_93
  · exact bank_159
  · exact bank_171
  · exact bank_181
  · exact bank_188
  · exact bank_200
  · exact bank_204
  · exact bank_209
  · exact bank_211

theorem bank_213 : search 2 0 [0, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_139

theorem bank_214 : search 3 0 [0, 6, 7, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 6, 7, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_140
  · exact bank_213

theorem bank_215 : search 2 0 [0, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_141

theorem bank_216 : search 3 0 [0, 6, 7, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 6, 7, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_142
  · exact bank_215

theorem bank_217 : search 2 0 [0, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 4, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_145

theorem bank_218 : search 2 1 [0, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_143

theorem bank_219 : search 2 1 [0, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_146

theorem bank_220 : search 2 1 [0, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_148

theorem bank_221 : search 2 1 [0, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_149

theorem bank_222 : search 2 0 [0, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63] = [(0, [0, 4, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_150

theorem bank_223 : search 3 1 [0, 6, 7, 32, 38, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 6, 7, 32, 38, 48, 56, 60, 62, 63] = [(0, [0, 1, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 3, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 15, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 25, 32, 38, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 31, 32, 38, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 36, 38, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63]), (0, [0, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_22
  · exact bank_94
  · exact bank_152
  · exact bank_213
  · exact bank_217
  · exact bank_215
  · exact bank_218
  · exact bank_219
  · exact bank_220
  · exact bank_221
  · exact bank_222

theorem bank_224 : search 3 1 [0, 6, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 6, 7, 32, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_153
  · exact bank_219

theorem bank_225 : search 3 1 [0, 6, 7, 32, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 6, 7, 32, 48, 54, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 48, 54, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 48, 54, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_155
  · exact bank_220

theorem bank_226 : search 3 1 [0, 6, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 6, 7, 32, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 6, 7, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_156
  · exact bank_221

theorem bank_227 : search 3 0 [0, 6, 7, 32, 48, 56, 57, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 6, 7, 32, 48, 56, 57, 60, 62, 63] = [(0, [0, 4, 6, 7, 32, 48, 56, 57, 60, 62, 63]), (0, [0, 6, 7, 32, 38, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_157
  · exact bank_222

theorem bank_228 : search 4 1 [0, 6, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 6, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 6, 7, 32, 48, 56, 60, 62, 63]), (1, [0, 4, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 48, 54, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 6, 7, 32, 48, 56, 57, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_23
  · exact bank_95
  · exact bank_159
  · exact bank_214
  · exact bank_216
  · exact bank_223
  · exact bank_224
  · exact bank_225
  · exact bank_226
  · exact bank_227

theorem bank_229 : search 2 0 [0, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_160

theorem bank_230 : search 3 0 [0, 7, 8, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 8, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_161
  · exact bank_229

theorem bank_231 : search 3 0 [0, 7, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 12, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 12, 15, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_162

theorem bank_232 : search 3 0 [0, 7, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 14, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 14, 15, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_163

theorem bank_233 : search 2 0 [0, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_165

theorem bank_234 : search 3 0 [0, 7, 15, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 15, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_166
  · exact bank_233

theorem bank_235 : search 2 0 [0, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_167

theorem bank_236 : search 3 0 [0, 7, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 15, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_168
  · exact bank_235

theorem bank_237 : search 3 0 [0, 7, 15, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 15, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_170

theorem bank_238 : search 4 0 [0, 7, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 7, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_171
  · exact bank_214
  · exact bank_230
  · exact bank_231
  · exact bank_232
  · exact bank_234
  · exact bank_236
  · exact bank_237

theorem bank_239 : search 3 0 [0, 7, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 16, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 16, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_172

theorem bank_240 : search 3 0 [0, 7, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 24, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 24, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_173

theorem bank_241 : search 3 0 [0, 7, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 28, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 28, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_174

theorem bank_242 : search 3 0 [0, 7, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 30, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 30, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_175

theorem bank_243 : search 2 0 [0, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_177

theorem bank_244 : search 3 0 [0, 7, 31, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 31, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 31, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_178
  · exact bank_243

theorem bank_245 : search 3 0 [0, 7, 31, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 31, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 4, 7, 31, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_180

theorem bank_246 : search 4 0 [0, 7, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 7, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 6, 7, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_181
  · exact bank_216
  · exact bank_239
  · exact bank_240
  · exact bank_241
  · exact bank_242
  · exact bank_244
  · exact bank_245

theorem bank_247 : search 2 0 [0, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_189

theorem bank_248 : search 3 0 [0, 7, 24, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 24, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 24, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_190
  · exact bank_247

theorem bank_249 : search 2 1 [0, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_183

theorem bank_250 : search 3 1 [0, 7, 32, 36, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 7, 32, 36, 39, 48, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 36, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_184
  · exact bank_249

theorem bank_251 : search 2 0 [0, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 4, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_191

theorem bank_252 : search 2 1 [0, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_193

theorem bank_253 : search 2 1 [0, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_194

theorem bank_254 : search 3 1 [0, 7, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 7, 32, 38, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 24, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 25, 32, 38, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 36, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 38, 39, 48, 54, 56, 60, 62, 63]), (1, [0, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_25
  · exact bank_97
  · exact bank_196
  · exact bank_219
  · exact bank_233
  · exact bank_247
  · exact bank_251
  · exact bank_243
  · exact bank_249
  · exact bank_252
  · exact bank_253

theorem bank_255 : search 3 1 [0, 7, 32, 39, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 7, 32, 39, 48, 55, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 39, 48, 55, 56, 60, 62, 63]), (1, [0, 7, 32, 38, 39, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_198
  · exact bank_253

theorem bank_256 : search 4 1 [0, 7, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 7, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 1, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 24, 32, 39, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 36, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 38, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 39, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_26
  · exact bank_98
  · exact bank_200
  · exact bank_224
  · exact bank_234
  · exact bank_248
  · exact bank_244
  · exact bank_250
  · exact bank_254
  · exact bank_255

theorem bank_257 : search 2 0 [0, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_205

theorem bank_258 : search 3 0 [0, 7, 8, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 7, 8, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 4, 7, 8, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 7, 8, 32, 40, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact bank_206
  · exact bank_257

theorem bank_259 : search 3 1 [0, 7, 32, 48, 52, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 7, 32, 48, 52, 55, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 48, 52, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_202

theorem bank_260 : search 3 1 [0, 7, 32, 48, 54, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 7, 32, 48, 54, 55, 56, 60, 62, 63] = [(1, [0, 4, 7, 32, 48, 54, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_207

theorem bank_261 : search 4 1 [0, 7, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 7, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 1, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 7, 8, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 48, 55, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 48, 55, 56, 60, 62, 63]), (1, [0, 7, 32, 39, 48, 55, 56, 60, 62, 63]), (1, [0, 7, 32, 48, 52, 55, 56, 60, 62, 63]), (1, [0, 7, 32, 48, 54, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_28
  · exact bank_100
  · exact bank_209
  · exact bank_226
  · exact bank_258
  · exact bank_237
  · exact bank_245
  · exact bank_255
  · exact bank_259
  · exact bank_260

theorem bank_262 : search 5 1 [0, 7, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 4 1 [0, 7, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 7, 32, 48, 56, 60, 62, 63]), (1, [0, 4, 7, 32, 48, 56, 60, 62, 63]), (1, [0, 6, 7, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 39, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_31
  · exact bank_102
  · exact bank_212
  · exact bank_228
  · exact bank_238
  · exact bank_246
  · exact bank_256
  · exact bank_261

theorem bank_263 : search 2 1 [0, 8, 12, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 8, 12, 15, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_264 : search 3 1 [0, 8, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 8, 12, 15, 32, 48, 56, 60, 62, 63] = [(1, [0, 8, 12, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_263

theorem bank_265 : search 2 1 [0, 8, 14, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 8, 14, 15, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_266 : search 3 1 [0, 8, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 8, 14, 15, 32, 48, 56, 60, 62, 63] = [(1, [0, 8, 14, 15, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_265

theorem bank_267 : search 2 0 [0, 8, 15, 31, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 8, 15, 31, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_268 : search 3 0 [0, 8, 15, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 8, 15, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 8, 15, 31, 32, 40, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_267

theorem bank_269 : search 2 0 [0, 8, 15, 23, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 8, 15, 23, 32, 40, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_270 : search 2 1 [0, 8, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 8, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_271 : search 2 0 [0, 8, 15, 32, 40, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 8, 15, 32, 40, 48, 55, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_272 : search 3 1 [0, 8, 15, 32, 40, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 8, 15, 32, 40, 48, 56, 60, 62, 63] = [(0, [0, 1, 8, 15, 32, 40, 48, 56, 60, 62, 63]), (0, [0, 3, 8, 15, 32, 40, 48, 56, 60, 62, 63]), (0, [0, 7, 8, 15, 32, 40, 48, 56, 60, 62, 63]), (1, [0, 8, 12, 15, 32, 40, 48, 56, 60, 62, 63]), (1, [0, 8, 14, 15, 32, 40, 48, 56, 60, 62, 63]), (0, [0, 8, 15, 23, 32, 40, 48, 56, 60, 62, 63]), (0, [0, 8, 15, 31, 32, 40, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 8, 15, 32, 40, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_32
  · exact bank_103
  · exact bank_229
  · exact bank_263
  · exact bank_265
  · exact bank_269
  · exact bank_267
  · exact bank_270
  · exact bank_271

theorem bank_273 : search 3 1 [0, 8, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 8, 15, 32, 47, 48, 56, 60, 62, 63] = [(1, [0, 8, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_270

theorem bank_274 : search 3 0 [0, 8, 15, 32, 48, 55, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 8, 15, 32, 48, 55, 56, 60, 62, 63] = [(0, [0, 8, 15, 32, 40, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_271

theorem bank_275 : search 4 1 [0, 8, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 8, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 8, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 8, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 12, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 8, 15, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 40, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 8, 15, 32, 48, 55, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_33
  · exact bank_104
  · exact bank_230
  · exact bank_264
  · exact bank_266
  · exact bank_268
  · exact bank_272
  · exact bank_273
  · exact bank_274

theorem bank_276 : search 3 1 [0, 12, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 12, 14, 15, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_277 : search 3 0 [0, 12, 15, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 12, 15, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_278 : search 2 1 [0, 12, 15, 32, 40, 44, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 12, 15, 32, 40, 44, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_279 : search 3 1 [0, 12, 15, 32, 44, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 12, 15, 32, 44, 48, 56, 60, 62, 63] = [(1, [0, 12, 15, 32, 40, 44, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_278

theorem bank_280 : search 2 1 [0, 12, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 12, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_281 : search 3 1 [0, 12, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 12, 15, 32, 47, 48, 56, 60, 62, 63] = [(1, [0, 12, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_280

theorem bank_282 : search 3 0 [0, 12, 15, 32, 48, 51, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 12, 15, 32, 48, 51, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_283 : search 4 1 [0, 12, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 12, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 12, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 12, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 12, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 12, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 12, 15, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 12, 15, 32, 44, 48, 56, 60, 62, 63]), (1, [0, 12, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 12, 15, 32, 48, 51, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_34
  · exact bank_105
  · exact bank_231
  · exact bank_264
  · exact bank_276
  · exact bank_277
  · exact bank_279
  · exact bank_281
  · exact bank_282

theorem bank_284 : search 3 0 [0, 14, 15, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 14, 15, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_285 : search 2 1 [0, 14, 15, 32, 40, 46, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 14, 15, 32, 40, 46, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_286 : search 3 1 [0, 14, 15, 32, 46, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 14, 15, 32, 46, 48, 56, 60, 62, 63] = [(1, [0, 14, 15, 32, 40, 46, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_285

theorem bank_287 : search 2 1 [0, 14, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 14, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_288 : search 3 1 [0, 14, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 14, 15, 32, 47, 48, 56, 60, 62, 63] = [(1, [0, 14, 15, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_287

theorem bank_289 : search 3 0 [0, 14, 15, 32, 48, 49, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 14, 15, 32, 48, 49, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_290 : search 4 1 [0, 14, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 14, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 14, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 14, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 12, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 14, 15, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 14, 15, 32, 46, 48, 56, 60, 62, 63]), (1, [0, 14, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 14, 15, 32, 48, 49, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_35
  · exact bank_106
  · exact bank_232
  · exact bank_266
  · exact bank_276
  · exact bank_284
  · exact bank_286
  · exact bank_288
  · exact bank_289

theorem bank_291 : search 3 0 [0, 15, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 16, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_292 : search 3 0 [0, 15, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 24, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_293 : search 3 0 [0, 15, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_294 : search 3 0 [0, 15, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_295 : search 2 0 [0, 15, 31, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 15, 31, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_296 : search 3 0 [0, 15, 31, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 31, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 15, 31, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_295

theorem bank_297 : search 4 0 [0, 15, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 0 [0, 15, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 8, 15, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 12, 15, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 14, 15, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 31, 32, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_268
  · exact bank_277
  · exact bank_284
  · exact bank_291
  · exact bank_292
  · exact bank_293
  · exact bank_294
  · exact bank_296

theorem bank_298 : search 2 0 [0, 15, 16, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 15, 16, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_299 : search 3 0 [0, 15, 16, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 15, 16, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 15, 16, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_298

theorem bank_300 : search 2 0 [0, 15, 23, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 15, 23, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_301 : search 2 1 [0, 15, 32, 40, 44, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 15, 32, 40, 44, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_302 : search 2 1 [0, 15, 32, 40, 46, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 1 [0, 15, 32, 40, 46, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_303 : search 3 1 [0, 15, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 15, 32, 40, 47, 48, 56, 60, 62, 63] = [(0, [0, 1, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (1, [0, 12, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (1, [0, 14, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 15, 16, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 15, 23, 32, 40, 47, 48, 56, 60, 62, 63]), (0, [0, 15, 31, 32, 40, 47, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 40, 44, 47, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 40, 46, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_37
  · exact bank_108
  · exact bank_235
  · exact bank_270
  · exact bank_280
  · exact bank_287
  · exact bank_298
  · exact bank_300
  · exact bank_295
  · exact bank_301
  · exact bank_302

theorem bank_304 : search 3 1 [0, 15, 32, 44, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 15, 32, 44, 47, 48, 56, 60, 62, 63] = [(1, [0, 15, 32, 40, 44, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_301

theorem bank_305 : search 3 1 [0, 15, 32, 46, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 15, 32, 46, 47, 48, 56, 60, 62, 63] = [(1, [0, 15, 32, 40, 46, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_302

theorem bank_306 : search 4 1 [0, 15, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 15, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 1, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 47, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 47, 48, 56, 60, 62, 63]), (1, [0, 12, 15, 32, 47, 48, 56, 60, 62, 63]), (1, [0, 14, 15, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 15, 16, 32, 47, 48, 56, 60, 62, 63]), (0, [0, 15, 31, 32, 47, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 40, 47, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 44, 47, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 46, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_38
  · exact bank_109
  · exact bank_236
  · exact bank_273
  · exact bank_281
  · exact bank_288
  · exact bank_299
  · exact bank_296
  · exact bank_303
  · exact bank_304
  · exact bank_305

theorem bank_307 : search 5 1 [0, 15, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 4 1 [0, 15, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 8, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 12, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 14, 15, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_42
  · exact bank_112
  · exact bank_238
  · exact bank_275
  · exact bank_283
  · exact bank_290
  · exact bank_297
  · exact bank_306

theorem bank_308 : search 3 1 [0, 16, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 16, 24, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_309 : search 3 1 [0, 16, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 16, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_310 : search 3 1 [0, 16, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 16, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_311 : search 2 0 [0, 16, 31, 32, 40, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 16, 31, 32, 40, 47, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_312 : search 3 0 [0, 16, 31, 32, 47, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 16, 31, 32, 47, 48, 56, 60, 62, 63] = [(0, [0, 16, 31, 32, 40, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_311

theorem bank_313 : search 4 1 [0, 16, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 16, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 16, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 16, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 24, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 16, 31, 32, 47, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_43
  · exact bank_113
  · exact bank_239
  · exact bank_291
  · exact bank_308
  · exact bank_309
  · exact bank_310
  · exact bank_312

theorem bank_314 : search 3 1 [0, 24, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 24, 28, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_315 : search 3 1 [0, 24, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 24, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_316 : search 2 0 [0, 24, 31, 32, 38, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 1 0 [0, 24, 31, 32, 38, 39, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_317 : search 3 0 [0, 24, 31, 32, 39, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 24, 31, 32, 39, 48, 56, 60, 62, 63] = [(0, [0, 24, 31, 32, 38, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · exact bank_316

theorem bank_318 : search 4 1 [0, 24, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 24, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 24, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 24, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 24, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 24, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 24, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 24, 31, 32, 39, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_44
  · exact bank_114
  · exact bank_240
  · exact bank_292
  · exact bank_308
  · exact bank_314
  · exact bank_315
  · exact bank_317

theorem bank_319 : search 3 1 [0, 28, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 1 [0, 28, 30, 31, 32, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_320 : search 3 0 [0, 28, 31, 32, 35, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 28, 31, 32, 35, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_321 : search 4 1 [0, 28, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 28, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 28, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 24, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 28, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 28, 31, 32, 35, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_45
  · exact bank_115
  · exact bank_241
  · exact bank_293
  · exact bank_309
  · exact bank_314
  · exact bank_319
  · exact bank_320

theorem bank_322 : search 3 0 [0, 30, 31, 32, 33, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 2 0 [0, 30, 31, 32, 33, 48, 56, 60, 62, 63] = [] := by rfl
  rw [hlist]
  intro next hn
  simp at hn

theorem bank_323 : search 4 1 [0, 30, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 3 1 [0, 30, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 30, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 30, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 24, 30, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 28, 30, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 30, 31, 32, 33, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_46
  · exact bank_116
  · exact bank_242
  · exact bank_294
  · exact bank_310
  · exact bank_315
  · exact bank_319
  · exact bank_322

theorem bank_324 : search 5 1 [0, 31, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 4 1 [0, 31, 32, 48, 56, 60, 62, 63] = [(0, [0, 1, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 3, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 7, 31, 32, 48, 56, 60, 62, 63]), (0, [0, 15, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 16, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 24, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 28, 31, 32, 48, 56, 60, 62, 63]), (1, [0, 30, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_51
  · exact bank_120
  · exact bank_246
  · exact bank_297
  · exact bank_313
  · exact bank_318
  · exact bank_321
  · exact bank_323

theorem bank_325 : search 6 2 [0, 32, 48, 56, 60, 62, 63] = false := by
  refine search_dead _ _ _ (by decide +kernel) ?_
  have hlist : branches 5 2 [0, 32, 48, 56, 60, 62, 63] = [(1, [0, 1, 32, 48, 56, 60, 62, 63]), (1, [0, 3, 32, 48, 56, 60, 62, 63]), (1, [0, 7, 32, 48, 56, 60, 62, 63]), (1, [0, 15, 32, 48, 56, 60, 62, 63]), (1, [0, 31, 32, 48, 56, 60, 62, 63])] := by rfl
  rw [hlist]
  intro next hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact bank_69
  · exact bank_138
  · exact bank_262
  · exact bank_307
  · exact bank_324

theorem no_search : search 6 2 [0, 32, 48, 56, 60, 62, 63] = false := bank_325

end PEqualNP.Outside.L_meta_50269


open PEqualNP.Outside.L_meta_50269 in
theorem PEqualNP.Outside.L_meta_50269 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val)) := by
  intro claimed
  obtain ⟨D, p, q, r, hfan, _, hnot, hsize, hval⟩ := claimed
  have ok : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_50269.legal g := hfan
  let W := D.gates.foldl push initial
  have hLift (t : Fin 6) : W.map (fun w => bits w t) = D.wires (row t) := by
    change (D.gates.foldl push initial).map _ = _
    rw [lift_fold _ ok, initial_row]
    rfl
  have hW : W.length = 7 + D.size := by
    change (D.gates.foldl push initial).length = _
    rw [push_length]
    rfl
  have hgoal : goal W := by
    refine ⟨output_in W p.val (by rw [hW]; exact p.isLt) 4 ?_,
      output_in W q.val (by rw [hW]; exact q.isLt) 38 ?_,
      output_in W r.val (by rw [hW]; exact r.isLt) 40 ?_⟩
    · intro t
      rw [hLift]
      exact (hval t).1
    · intro t
      rw [hLift]
      exact (hval t).2.1
    · intro t
      rw [hLift]
      exact (hval t).2.2
  have hprice : priceList D.gates ≤ 2 := by
    rw [priceList_eq]
    exact hnot
  have hs := search_sound D.gates initial [0,32,48,56,60,62,63] 6 2 (by decide +kernel)
    (by decide) (by decide) ok hsize hprice hgoal
  rw [no_search] at hs
  simp at hs
