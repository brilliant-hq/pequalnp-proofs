import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1257

open PEqualNP.CircuitLowerBounds

/-! ### Part 1: Helper lemmas for `Circuit.wires` under `ReadsBack` -/

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_exists_tail (gs : List Gate) : ∀ w : List Bool,
    ∃ tl : List Bool, wiresFrom gs w = w ++ tl ∧ tl.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    rcases ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) with ⟨tl, htl, hlen⟩
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tl, ?_, by simp [hlen]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [htl]; simp

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  rcases wiresFrom_exists_tail gs w with ⟨tl, htl, hlen⟩
  rw [htl, List.length_append, hlen]

private lemma getD_append_left {l1 l2 : List Bool} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  rcases wiresFrom_exists_tail gs w with ⟨tl, htl, _⟩
  rw [htl]
  exact getD_append_left hi

private lemma circuit_wires_gate (D : Circuit) (x : List Bool) (j : Nat) (hj : j < D.gates.length) :
    let w := D.wires x
    w.getD (x.length + j) false =
      (D.gates[j]'hj).op.eval ((D.gates[j]'hj).inputs.map (fun i =>
        (wiresFrom (D.gates.take j) x).getD i false)) := by
  dsimp only
  have hsplit : D.gates = D.gates.take j ++ [D.gates[j]'hj] ++ D.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j D.gates
    have h2 : D.gates.drop j = (D.gates[j]'hj) :: D.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  have hw : D.wires x = wiresFrom (D.gates.drop (j + 1))
      (wiresFrom [D.gates[j]'hj] (wiresFrom (D.gates.take j) x)) := by
    change wiresFrom D.gates x = _
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_append]
  rw [hw]
  set p := wiresFrom (D.gates.take j) x
  have hplen : p.length = x.length + j := by
    dsimp only [p]
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hstep : wiresFrom [D.gates[j]'hj] p =
      p ++ [(D.gates[j]'hj).op.eval ((D.gates[j]'hj).inputs.map (fun i => p.getD i false))] := rfl
  rw [hstep]
  have hlt : x.length + j < (p ++ [(D.gates[j]'hj).op.eval ((D.gates[j]'hj).inputs.map (fun i => p.getD i false))]).length := by
    rw [List.length_append, hplen]; simp
  rw [getD_wiresFrom_lt _ _ _ hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen]
  simp

private lemma circuit_wires_gate_readsBack (D : Circuit) (x : List Bool)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length D) (j : Nat) (hj : j < D.gates.length) :
    let w := D.wires x
    w.getD (x.length + j) false =
      (D.gates[j]'hj).op.eval ((D.gates[j]'hj).inputs.map (fun i => w.getD i false)) := by
  dsimp only
  rw [circuit_wires_gate D x j hj]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < x.length + j := by
    have h := hrb j hj i
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates[j]'hj := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hgat] at h
    exact h hi
  have hsplit : D.gates = D.gates.take j ++ D.gates.drop j := (List.take_append_drop j D.gates).symm
  have hw : D.wires x = wiresFrom (D.gates.drop j) (wiresFrom (D.gates.take j) x) := by
    change wiresFrom D.gates x = _
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]
  rw [hw]
  have hlen : (wiresFrom (D.gates.take j) x).length = x.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  exact (getD_wiresFrom_lt _ _ _ (by omega)).symm

private lemma circuit_wires_input (D : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (D.wires x).getD i false = x.getD i false := by
  exact getD_wiresFrom_lt D.gates x i hi

/-! ### Part 2: Variable, Clause, and Occurrence Construction -/

private abbrev VarT (q n sz : Nat) :=
  (Fin q × Fin n) ⊕ (Fin (q + 2 + sz) ⊕ (Unit ⊕ (Fin (q + 2) × Fin (q + 2))))

private def vBank {q n sz : Nat} (k : Fin q) (v : Fin n) : VarT q n sz := Sum.inl (k, v)
private def vWire {q n sz : Nat} (w : Fin (q + 2 + sz)) : VarT q n sz := Sum.inr (Sum.inl w)
private def vPin {q n sz : Nat} : VarT q n sz := Sum.inr (Sum.inr (Sum.inl ()))
private def vDP {q n sz : Nat} (i j : Fin (q + 2)) : VarT q n sz := Sum.inr (Sum.inr (Sum.inr (i, j)))

private def wireFin {q sz : Nat} (i : Nat) : Fin (q + 2 + sz) :=
  if h : i < q + 2 + sz then ⟨i, h⟩ else ⟨0, by omega⟩

private def gateTseitin {q n : Nat} (D : Circuit) (g : Fin D.size) : List (List (VarT q n D.size × Bool)) :=
  let gt := D.gates[g.val]'g.isLt
  let o : VarT q n D.size := vWire ⟨q + 2 + g.val, by have := g.isLt; omega⟩
  match gt.op with
  | .and =>
    match gt.inputs with
    | [] => [[(o, true)]]
    | [a] =>
      let va : VarT q n D.size := vWire (wireFin a)
      [[(o, false), (va, true)], [(o, true), (va, false)]]
    | [a, b] =>
      let va : VarT q n D.size := vWire (wireFin a)
      let vb : VarT q n D.size := vWire (wireFin b)
      [[(o, false), (va, true)], [(o, false), (vb, true)], [(o, true), (va, false), (vb, false)]]
    | _ => []
  | .or =>
    match gt.inputs with
    | [] => [[(o, false)]]
    | [a] =>
      let va : VarT q n D.size := vWire (wireFin a)
      [[(o, false), (va, true)], [(o, true), (va, false)]]
    | [a, b] =>
      let va : VarT q n D.size := vWire (wireFin a)
      let vb : VarT q n D.size := vWire (wireFin b)
      [[(o, true), (va, false)], [(o, true), (vb, false)], [(o, false), (va, true), (vb, true)]]
    | _ => []
  | .not =>
    match gt.inputs with
    | [] => [[(o, true)]]
    | a :: _ =>
      let va : VarT q n D.size := vWire (wireFin a)
      [[(o, false), (va, false)], [(o, true), (va, true)]]
  | _ => []

private def clauseSat {α : Type*} (s : α → Bool) (cl : List (α × Bool)) : Prop :=
  ∃ p ∈ cl, s p.1 = p.2

private lemma gateTseitin_len_le {q n : Nat} (D : Circuit) (g : Fin D.size) :
    (gateTseitin (q := q) (n := n) D g).length ≤ 3 ∧
    ∀ c ∈ gateTseitin (q := q) (n := n) D g, c.length ≤ 3 := by
  dsimp only [gateTseitin]
  cases (D.gates[g.val]'g.isLt).op <;>
  cases (D.gates[g.val]'g.isLt).inputs with
  | nil => simp
  | cons a tl =>
    cases tl with
    | nil => simp
    | cons b tl2 =>
      cases tl2 <;> simp

private lemma gateTseitin_iff {q n : Nat} (D : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (q + 2) D)
    (g : Fin D.size) (s : VarT q n D.size → Bool) :
    (∀ c ∈ gateTseitin D g, clauseSat s c) ↔
      s (vWire ⟨q + 2 + g.val, by have := g.isLt; omega⟩) =
        (D.gates[g.val]'g.isLt).op.eval
          ((D.gates[g.val]'g.isLt).inputs.map (fun i => s (vWire (wireFin i)))) := by
  set gt := D.gates[g.val]'g.isLt
  have hgt_mem : gt ∈ D.gates := List.getElem_mem g.isLt
  rcases hfan gt hgt_mem with ⟨hop, hlen⟩
  dsimp only [gateTseitin]
  set o : VarT q n D.size := vWire ⟨q + 2 + g.val, by have := g.isLt; omega⟩
  change (∀ c ∈ match gt.op with
    | .and => match gt.inputs with
      | [] => [[(o, true)]]
      | [a] => [[(o, false), (vWire (wireFin a), true)], [(o, true), (vWire (wireFin a), false)]]
      | [a, b] => [[(o, false), (vWire (wireFin a), true)], [(o, false), (vWire (wireFin b), true)],
          [(o, true), (vWire (wireFin a), false), (vWire (wireFin b), false)]]
      | _ => []
    | .or => match gt.inputs with
      | [] => [[(o, false)]]
      | [a] => [[(o, false), (vWire (wireFin a), true)], [(o, true), (vWire (wireFin a), false)]]
      | [a, b] => [[(o, true), (vWire (wireFin a), false)], [(o, true), (vWire (wireFin b), false)],
          [(o, false), (vWire (wireFin a), true), (vWire (wireFin b), true)]]
      | _ => []
    | .not => match gt.inputs with
      | [] => [[(o, true)]]
      | a :: _ => [[(o, false), (vWire (wireFin a), false)], [(o, true), (vWire (wireFin a), true)]]
    | _ => [], clauseSat s c) ↔ s o = gt.op.eval (gt.inputs.map (fun i => s (vWire (wireFin i))))
  rcases hop with hop | hop | hop
  · rw [hop]
    cases hin : gt.inputs with
    | nil =>
      simp only [GateOp.eval, List.map_nil, List.all_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, clauseSat, exists_eq_left]
    | cons a tl =>
      cases tl with
      | nil =>
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, clauseSat,
          exists_eq_or_imp, exists_eq_left]
        cases s o <;> cases s (vWire (wireFin a)) <;> decide
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, clauseSat,
            exists_eq_or_imp, exists_eq_left]
          cases s o <;> cases s (vWire (wireFin a)) <;> cases s (vWire (wireFin b)) <;> decide
        | cons _ _ => rw [hin] at hlen; simp at hlen
  · rw [hop]
    cases hin : gt.inputs with
    | nil =>
      simp only [GateOp.eval, List.map_nil, List.any_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, clauseSat, exists_eq_left]
    | cons a tl =>
      cases tl with
      | nil =>
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, clauseSat,
          exists_eq_or_imp, exists_eq_left]
        cases s o <;> cases s (vWire (wireFin a)) <;> decide
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, clauseSat,
            exists_eq_or_imp, exists_eq_left]
          cases s o <;> cases s (vWire (wireFin a)) <;> cases s (vWire (wireFin b)) <;> decide
        | cons _ _ => rw [hin] at hlen; simp at hlen
  · rw [Set.mem_singleton_iff] at hop; rw [hop]
    cases hin : gt.inputs with
    | nil =>
      simp only [GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq, clauseSat, exists_eq_left]
    | cons a tl =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, clauseSat,
        exists_eq_or_imp, exists_eq_left]
      cases s o <;> cases s (vWire (wireFin a)) <;> decide

private def uLit {q n sz : Nat} (i : Fin (q + 1)) : VarT q n sz × Bool :=
  if h : i.val < q then (vWire ⟨i.val, by omega⟩, true) else (vPin, false)

private def dpClauses (q n sz : Nat) : List (List (VarT q n sz × Bool)) :=
  let baseC : List (List (VarT q n sz × Bool)) :=
    (List.finRange (q + 1)).map (fun j => [(vDP 0 j.succ, false)])
  let step1 : List (List (VarT q n sz × Bool)) :=
    (List.finRange (q + 1)).flatMap (fun i =>
      (List.finRange (q + 1)).map (fun j =>
        [(vDP i.succ j.succ, false), (vDP i.castSucc j.succ, true), uLit i]))
  let step2 : List (List (VarT q n sz × Bool)) :=
    (List.finRange (q + 1)).flatMap (fun i =>
      (List.finRange q).map (fun j =>
        [(vDP i.succ ⟨j.val + 2, by have := j.isLt; omega⟩, false),
         (vDP i.castSucc ⟨j.val + 1, by have := j.isLt; omega⟩, true)]))
  baseC ++ step1 ++ step2

private lemma dpClauses_len_le (q n sz : Nat) :
    (dpClauses q n sz).length ≤ 3 * (q + 2) ^ 2 ∧
    ∀ c ∈ dpClauses q n sz, c.length ≤ 3 := by
  constructor
  · dsimp only [dpClauses]
    simp only [List.length_append, List.length_map, List.length_flatMap, List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]
    nlinarith
  · intro c hc
    dsimp only [dpClauses] at hc
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and] at hc
    rcases hc with (⟨_, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp

private def uVal {q n sz : Nat} (s : VarT q n sz → Bool) (i : Fin (q + 1)) : Bool :=
  if h : i.val < q then s (vWire ⟨i.val, by omega⟩) else !(s vPin)

private lemma uLit_sat {q n sz : Nat} (s : VarT q n sz → Bool) (i : Fin (q + 1)) :
    s (uLit (n := n) (sz := sz) i).1 = (uLit (n := n) (sz := sz) i).2 ↔ uVal s i = true := by
  dsimp only [uLit, uVal]
  split_ifs with h
  · rfl
  · cases s vPin <;> simp

private def uCount {q n sz : Nat} (s : VarT q n sz → Bool) (i : Nat) : Nat :=
  ((Finset.univ : Finset (Fin (q + 1))).filter (fun r => r.val < i ∧ uVal s r = true)).card

private lemma uCount_zero {q n sz : Nat} (s : VarT q n sz → Bool) : uCount s 0 = 0 := by
  simp [uCount]

private lemma uCount_succ {q n sz : Nat} (s : VarT q n sz → Bool) (i : Fin (q + 1)) :
    uCount s (i.val + 1) = uCount s i.val + if uVal s i = true then 1 else 0 := by
  dsimp only [uCount]
  by_cases hu : uVal s i = true
  · rw [ite_eq_left hu]
    have hEq : (Finset.univ.filter (fun r : Fin (q + 1) => r.val < i.val + 1 ∧ uVal s r = true)) =
        insert i (Finset.univ.filter (fun r : Fin (q + 1) => r.val < i.val ∧ uVal s r = true)) := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hlt, hr⟩
        by_cases hri : r = i
        · exact Or.inl hri
        · exact Or.inr ⟨by have : r.val ≠ i.val := fun h => hri (Fin.ext h); omega, hr⟩
      · rintro (rfl | ⟨hlt, hr⟩)
        · exact ⟨by omega, hu⟩
        · exact ⟨by omega, hr⟩
    rw [hEq, Finset.card_insert_of_notMem (by simp)]
  · rw [ite_eq_right hu, add_zero]
    apply congrArg Finset.card
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hlt, hr⟩
      have hne : r ≠ i := fun h => hu (h ▸ hr)
      have : r.val ≠ i.val := fun h => hne (Fin.ext h)
      exact ⟨by omega, hr⟩
    · rintro ⟨hlt, hr⟩
      exact ⟨by omega, hr⟩

private lemma dpClauses_sound {q n sz : Nat} (s : VarT q n sz → Bool)
    (hsat : ∀ c ∈ dpClauses q n sz, clauseSat s c) :
    ∀ (i : Fin (q + 2)) (j : Fin (q + 1)), s (vDP i j.succ) = true → j.val + 1 ≤ uCount s i.val := by
  have hbase : ∀ j : Fin (q + 1), s (vDP 0 j.succ) = false := by
    intro j
    have hmem : [(vDP 0 j.succ, false)] ∈ dpClauses q n sz := by
      dsimp only [dpClauses]; simp
    rcases hsat _ hmem with ⟨p, hp, hsp⟩
    simp at hp; subst hp; exact hsp
  have hstep1 : ∀ (i j : Fin (q + 1)),
      s (vDP i.succ j.succ) = false ∨ s (vDP i.castSucc j.succ) = true ∨ uVal s i = true := by
    intro i j
    have hmem : [(vDP i.succ j.succ, false), (vDP i.castSucc j.succ, true), uLit i] ∈ dpClauses q n sz := by
      dsimp only [dpClauses]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      exact ⟨i, j, rfl⟩
    rcases hsat _ hmem with ⟨p, hp, hsp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl hsp
    · exact Or.inr (Or.inl hsp)
    · exact Or.inr (Or.inr ((uLit_sat s i).mp hsp))
  have hstep2 : ∀ (i : Fin (q + 1)) (j : Fin q),
      s (vDP i.succ ⟨j.val + 2, by have := j.isLt; omega⟩) = false ∨
      s (vDP i.castSucc ⟨j.val + 1, by have := j.isLt; omega⟩) = true := by
    intro i j
    have hmem : [(vDP i.succ ⟨j.val + 2, by have := j.isLt; omega⟩, false),
                 (vDP i.castSucc ⟨j.val + 1, by have := j.isLt; omega⟩, true)] ∈ dpClauses q n sz := by
      dsimp only [dpClauses]
      refine List.mem_append_right _ ?_
      simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      exact ⟨i, j, rfl⟩
    rcases hsat _ hmem with ⟨p, hp, hsp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl hsp
    · exact Or.inr hsp
  intro i
  rcases i with ⟨iv, hiv⟩
  induction iv with
  | zero =>
    intro j hj
    have h0 := hbase j
    change s (vDP ⟨0, by omega⟩ j.succ) = false at h0
    rw [h0] at hj; simp at hj
  | succ iv ih =>
    intro j hj
    let ifin : Fin (q + 1) := ⟨iv, by omega⟩
    have hsucc_eq : (⟨iv + 1, hiv⟩ : Fin (q + 2)) = ifin.succ := Fin.ext rfl
    rw [hsucc_eq] at hj
    have huc := uCount_succ s ifin
    by_cases hu : uVal s ifin = true
    · rw [ite_eq_left hu] at huc
      by_cases hj0 : j.val = 0
      · change uCount s (iv + 1) = uCount s iv + 1 at huc
        rw [hj0, huc]; omega
      · let j' : Fin q := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j.succ = ⟨j'.val + 2, by have := j'.isLt; omega⟩ := Fin.ext (by dsimp [j']; omega)
        rw [hj_eq] at hj
        rcases hstep2 ifin j' with hfalse | hprev
        · rw [hfalse] at hj; simp at hj
        · have hjprev_eq : (⟨j'.val + 1, by have := j'.isLt; omega⟩ : Fin (q + 2)) = (⟨j'.val, by have := j'.isLt; omega⟩ : Fin (q + 1)).succ := Fin.ext rfl
          rw [hjprev_eq] at hprev
          have hih := ih (by omega) ⟨j'.val, by have := j'.isLt; omega⟩ hprev
          dsimp only [ifin, j'] at hih huc ⊢; omega
    · rw [ite_eq_right hu, add_zero] at huc
      rcases hstep1 ifin j with hfalse | hprev | htrue
      · rw [hfalse] at hj; simp at hj
      · have hih := ih (by omega) j hprev
        dsimp only [ifin] at hih huc ⊢; omega
      · exact absurd htrue hu

private lemma dpClauses_complete {q n sz : Nat} (s : VarT q n sz → Bool)
    (hdp : ∀ (i j : Fin (q + 2)), s (vDP i j) = decide (j.val ≤ uCount s i.val)) :
    ∀ c ∈ dpClauses q n sz, clauseSat s c := by
  intro c hc
  dsimp only [dpClauses] at hc
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with (⟨j, rfl⟩ | ⟨i, j, rfl⟩) | ⟨i, j, rfl⟩
  · refine ⟨(vDP 0 j.succ, false), by simp, ?_⟩
    rw [hdp, Fin.val_zero, uCount_zero]; simp
  · by_cases h1 : j.val + 1 ≤ uCount s (i.val + 1)
    · by_cases hu : uVal s i = true
      · exact ⟨uLit i, by simp, (uLit_sat s i).mpr hu⟩
      · refine ⟨(vDP i.castSucc j.succ, true), by simp, ?_⟩
        rw [hdp]; simp only [Fin.val_castSucc, Fin.val_succ, decide_eq_true_eq]
        have huc := uCount_succ s i; rw [ite_eq_right hu, add_zero] at huc; omega
    · refine ⟨(vDP i.succ j.succ, false), by simp, ?_⟩
      rw [hdp]; simp only [Fin.val_succ, decide_eq_false_iff_not]; exact h1
  · by_cases h1 : j.val + 2 ≤ uCount s (i.val + 1)
    · refine ⟨(vDP i.castSucc ⟨j.val + 1, by have := j.isLt; omega⟩, true), by simp, ?_⟩
      rw [hdp]; simp only [Fin.val_castSucc, decide_eq_true_eq]
      have huc := uCount_succ s i; split_ifs at huc <;> omega
    · refine ⟨(vDP i.succ ⟨j.val + 2, by have := j.isLt; omega⟩, false), by simp, ?_⟩
      rw [hdp]; simp only [Fin.val_succ, decide_eq_false_iff_not]; exact h1

private def hardClauses {q n : Nat} (D : Circuit) : List (List (VarT q n D.size × Bool)) :=
  let c0 : List (VarT q n D.size × Bool) := [(vWire ⟨q, by omega⟩, false)]
  let c1 : List (VarT q n D.size × Bool) := [(vWire ⟨q + 1, by omega⟩, true)]
  let cout1 : List (VarT q n D.size × Bool) := [(vPin, false), (vWire (wireFin D.output), true)]
  let cout2 : List (VarT q n D.size × Bool) := [(vPin, true), (vWire (wireFin D.output), false)]
  let cGates : List (List (VarT q n D.size × Bool)) :=
    (List.finRange D.size).flatMap (fun g => gateTseitin D g)
  [c0, c1, cout1, cout2] ++ cGates ++ dpClauses q n D.size

private lemma hardClauses_bounds {q n : Nat} (D : Circuit) :
    (hardClauses (q := q) (n := n) D).length ≤ 4 + 3 * D.size + 3 * (q + 2) ^ 2 ∧
    ∀ c ∈ hardClauses (q := q) (n := n) D, c.length ≤ 3 := by
  have hdp := dpClauses_len_le q n D.size
  constructor
  · dsimp only [hardClauses]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatMap]
    have hg : ((List.finRange D.size).map (fun g => (gateTseitin (q := q) (n := n) D g).length)).sum ≤ 3 * D.size := by
      have hle : ∀ l : List (Fin D.size), (l.map (fun g => (gateTseitin (q := q) (n := n) D g).length)).sum ≤ 3 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons g tl ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have h1 := (gateTseitin_len_le (q := q) (n := n) D g).1
          omega
      have := hle (List.finRange D.size)
      simpa using this
    omega
  · intro c hc
    dsimp only [hardClauses] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
      List.mem_finRange, true_and] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | ⟨g, hg⟩) | hdpC
    · simp
    · simp
    · simp
    · simp
    · exact (gateTseitin_len_le (q := q) (n := n) D g).2 c hg
    · exact hdp.2 c hdpC

private lemma hardClauses_wires_eval {q n : Nat} (D : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (q + 2) D)
    (hout : D.output < q + 2 + D.size)
    (s : VarT q n D.size → Bool)
    (hsat : ∀ c ∈ hardClauses D, clauseSat s c) :
    let inp := List.ofFn (fun k : Fin q => s (vWire ⟨k.val, by omega⟩)) ++ [false, true]
    (∀ w : Fin (q + 2 + D.size), s (vWire w) = (D.wires inp).getD w.val false) ∧
    s vPin = D.eval inp := by
  intro inp
  have hinp_len : inp.length = q + 2 := by simp [inp]
  have hc0 : s (vWire ⟨q, by omega⟩) = false := by
    have hmem : [(vWire (n := n) (sz := D.size) ⟨q, by omega⟩, false)] ∈ hardClauses (q := q) (n := n) D := by
      dsimp [hardClauses]; simp
    rcases hsat _ hmem with ⟨p, hp, hsp⟩; simp at hp; subst hp; exact hsp
  have hc1 : s (vWire ⟨q + 1, by omega⟩) = true := by
    have hmem : [(vWire (n := n) (sz := D.size) ⟨q + 1, by omega⟩, true)] ∈ hardClauses (q := q) (n := n) D := by
      dsimp [hardClauses]; simp
    rcases hsat _ hmem with ⟨p, hp, hsp⟩; simp at hp; subst hp; exact hsp
  have hwires : ∀ (idx : Nat) (hidx : idx < q + 2 + D.size),
      s (vWire ⟨idx, hidx⟩) = (D.wires inp).getD idx false := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | ind idx ih =>
      intro hidx
      by_cases hlt : idx < q + 2
      · rw [circuit_wires_input D inp idx (by omega)]
        dsimp only [inp]
        by_cases hq : idx < q
        · rw [getD_append_left (by simp; omega)]
          simp [List.getD_eq_getElem?_getD, hq]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
          simp only [List.length_ofFn]
          have hcases : idx = q ∨ idx = q + 1 := by omega
          rcases hcases with rfl | rfl
          · simpa using hc0
          · have hsub : q + 1 - q = 1 := by omega
            rw [hsub]; simpa using hc1
      · let g : Fin D.size := ⟨idx - (q + 2), by omega⟩
        have hg_sat : ∀ c ∈ gateTseitin D g, clauseSat s c := fun c hc => by
          apply hsat c
          dsimp only [hardClauses]
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          simp only [List.mem_flatMap, List.mem_finRange, true_and]
          exact ⟨g, hc⟩
        have hgate := (gateTseitin_iff D hfan hrb g s).mp hg_sat
        have hidx_eq : (⟨idx, hidx⟩ : Fin (q + 2 + D.size)) =
            ⟨q + 2 + g.val, by have := g.isLt; omega⟩ :=
          Fin.ext (by dsimp [g]; omega)
        rw [hidx_eq, hgate]
        have hrb_inp : PEqualNP.MetaComplexity.NestedCover.ReadsBack inp.length D := by
          rw [hinp_len]; exact hrb
        have heval := circuit_wires_gate_readsBack D inp hrb_inp g.val g.isLt
        rw [hinp_len] at heval
        have hidx_nat : idx = q + 2 + g.val := by dsimp [g]; omega
        rw [hidx_nat, heval]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        have hilt : i < q + 2 + g.val := by
          have h := hrb g.val g.isLt i
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D g.val = D.gates[g.val]'g.isLt := by
            dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem g.isLt]; rfl
          rw [hgat] at h
          exact h hi
        have hwf : wireFin (q := q) (sz := D.size) i = ⟨i, by omega⟩ := by
          dsimp only [wireFin]; rw [dite_eq_left (by omega)]
        rw [hwf]
        exact ih i (by omega) (by omega)
  refine ⟨fun w => hwires w.val w.isLt, ?_⟩
  have hwf_out : wireFin (q := q) (sz := D.size) D.output = ⟨D.output, hout⟩ := by
    dsimp only [wireFin]; rw [dite_eq_left hout]
  have h1 : s vPin = false ∨ s (vWire ⟨D.output, hout⟩) = true := by
    have hmem : [(vPin (q := q) (n := n) (sz := D.size), false),
        (vWire (q := q) (n := n) (sz := D.size) (wireFin D.output), true)] ∈ hardClauses (q := q) (n := n) D := by
      dsimp [hardClauses]; simp
    rcases hsat _ hmem with ⟨p, hp, hsp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl hsp
    · rw [hwf_out] at hsp; exact Or.inr hsp
  have h2 : s vPin = true ∨ s (vWire ⟨D.output, hout⟩) = false := by
    have hmem : [(vPin (q := q) (n := n) (sz := D.size), true),
        (vWire (q := q) (n := n) (sz := D.size) (wireFin D.output), false)] ∈ hardClauses (q := q) (n := n) D := by
      dsimp [hardClauses]; simp
    rcases hsat _ hmem with ⟨p, hp, hsp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl hsp
    · rw [hwf_out] at hsp; exact Or.inr hsp
  have hpin_eq : s vPin = s (vWire ⟨D.output, hout⟩) := by
    cases hp : s vPin <;> cases ho : s (vWire ⟨D.output, hout⟩) <;> simp_all
  rw [hpin_eq, hwires D.output hout]
  rfl

/-! ### Part 3: Full MaxSAT instance and main construction -/

private structure Cfg where
  q : Nat
  m : Nat
  n : Nat
  t : Nat
  bank : Fin t → Fin q
  row : Fin t → Fin m
  var : Fin t → Fin n
  sign : Fin t → Bool
  D : Circuit

private def hcList (G : Cfg) : List (List (VarT G.q G.n G.D.size × Bool)) :=
  hardClauses (q := G.q) (n := G.n) G.D

private abbrev hcLen (G : Cfg) : Nat := (hcList G).length
private abbrev wRep (G : Cfg) : Nat := G.q + 2
private abbrev softN (G : Cfg) : Nat := (G.q + 1) / 2

private abbrev ClT (G : Cfg) :=
  (Fin G.q × Fin G.m) ⊕ (Unit ⊕ ((Fin (hcLen G) × Fin (wRep G)) ⊕ Fin (softN G)))

private abbrev HardOcc (G : Cfg) :=
  Σ c : Fin (hcLen G), Fin ((hcList G)[c.val]'c.isLt).length × Fin (wRep G)

private abbrev OccT (G : Cfg) :=
  Fin G.t ⊕ (Unit ⊕ ((Fin G.q × Fin G.m) ⊕ (HardOcc G ⊕ Fin (softN G))))

private def numV (G : Cfg) : Nat := Fintype.card (VarT G.q G.n G.D.size)
private def numM (G : Cfg) : Nat := Fintype.card (ClT G)
private def numT (G : Cfg) : Nat := Fintype.card (OccT G)

private noncomputable def eVar (G : Cfg) : VarT G.q G.n G.D.size ≃ Fin (numV G) :=
  Fintype.equivFin _

private noncomputable def eCl (G : Cfg) : ClT G ≃ Fin (numM G) :=
  Fintype.equivFin _

private noncomputable def eOcc (G : Cfg) : OccT G ≃ Fin (numT G) :=
  Fintype.equivFin _

private noncomputable def cBank (G : Cfg) (p : Fin G.q × Fin G.m) : Fin (numM G) :=
  eCl G (Sum.inl p)

private noncomputable def cPin (G : Cfg) : Fin (numM G) :=
  eCl G (Sum.inr (Sum.inl ()))

private noncomputable def cHard (G : Cfg) (c : Fin (hcLen G)) (r : Fin (wRep G)) : Fin (numM G) :=
  eCl G (Sum.inr (Sum.inr (Sum.inl (c, r))))

private noncomputable def cSoft (G : Cfg) (r : Fin (softN G)) : Fin (numM G) :=
  eCl G (Sum.inr (Sum.inr (Sum.inr r)))

private noncomputable def crOf (G : Cfg) : (Fin G.q × Fin G.m) ↪ Fin (numM G) :=
  ⟨cBank G, fun _ _ h => Sum.inl.inj ((eCl G).injective h)⟩

private noncomputable def cvOf (G : Cfg) : (Fin G.q × Fin G.n) ↪ Fin (numV G) :=
  ⟨fun p => eVar G (vBank p.1 p.2), fun _ _ h => Sum.inl.inj ((eVar G).injective h)⟩

private noncomputable def ioOf (G : Cfg) : Fin G.t ↪ Fin (numT G) :=
  ⟨fun i => eOcc G (Sum.inl i), fun _ _ h => Sum.inl.inj ((eOcc G).injective h)⟩

private noncomputable def pinOf (G : Cfg) : Fin (numT G) :=
  eOcc G (Sum.inr (Sum.inl ()))

private noncomputable def clOf (G : Cfg) (o : OccT G) : Fin (numM G) :=
  match o with
  | Sum.inl i => crOf G (G.bank i, G.row i)
  | Sum.inr (Sum.inl ()) => cPin G
  | Sum.inr (Sum.inr (Sum.inl p)) => crOf G p
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, _, rep⟩))) => cHard G c rep
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr r))) => cSoft G r

private noncomputable def vrOf (G : Cfg) (o : OccT G) : Fin (numV G) :=
  match o with
  | Sum.inl i => cvOf G (G.bank i, G.var i)
  | Sum.inr (Sum.inl ()) => eVar G vPin
  | Sum.inr (Sum.inr (Sum.inl p)) => eVar G (vWire ⟨p.1.val, by have := p.1.isLt; omega⟩)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, lit, _⟩))) =>
      eVar G (((hcList G)[c.val]'c.isLt)[lit.val]'lit.isLt).1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr r))) =>
      eVar G (vDP (Fin.last (G.q + 1)) ⟨2 * r.val + 2, by have := r.isLt; dsimp [softN] at this; omega⟩)

private def sgOf (G : Cfg) (o : OccT G) : Bool :=
  match o with
  | Sum.inl i => G.sign i
  | Sum.inr (Sum.inl ()) => true
  | Sum.inr (Sum.inr (Sum.inl _)) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, lit, _⟩))) =>
      (((hcList G)[c.val]'c.isLt)[lit.val]'lit.isLt).2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => true

private noncomputable def clF (G : Cfg) (o : Fin (numT G)) : Fin (numM G) := clOf G ((eOcc G).symm o)
private noncomputable def vrF (G : Cfg) (o : Fin (numT G)) : Fin (numV G) := vrOf G ((eOcc G).symm o)
private noncomputable def sgF (G : Cfg) (o : Fin (numT G)) : Bool := sgOf G ((eOcc G).symm o)

private noncomputable def baseOf (G : Cfg) : Finset (Fin (numT G)) :=
  Finset.univ.filter (fun o => (match (eOcc G).symm o with | Sum.inr (Sum.inr _) => true | _ => false) = true)

private def Hval (G : Cfg) : Nat := G.q * G.m + hcLen G * wRep G

private noncomputable def satSet (G : Cfg) (Z : Finset (Fin (numT G))) (s : Fin (numV G) → Bool) :
    Finset (Fin (numM G)) :=
  (Z.filter (fun i => s (vrF G i) = sgF G i)).image (clF G)

private noncomputable def answersOf (G : Cfg) (X : Finset (Fin G.t)) : Finset (Fin G.q) :=
  @Finset.filter _ (fun k => ∃ s : Fin G.n → Bool, ∀ j : Fin G.m,
    ∃ i ∈ X, G.bank i = k ∧ G.row i = j ∧ s (G.var i) = G.sign i)
    (Classical.decPred _) Finset.univ

private noncomputable def bankSatOf (G : Cfg) (X : Finset (Fin G.t)) (s : Fin (numV G) → Bool) :
    Finset (Fin G.q × Fin G.m) :=
  @Finset.filter _ (fun p =>
    s (eVar G (vWire ⟨p.1.val, by have := p.1.isLt; omega⟩)) = false ∨
    ∃ i ∈ X, G.bank i = p.1 ∧ G.row i = p.2 ∧ s (eVar G (vBank p.1 (G.var i))) = G.sign i)
    (Classical.decPred _) Finset.univ

private noncomputable def hardSatOf (G : Cfg) (s : Fin (numV G) → Bool) : Finset (Fin (hcLen G)) :=
  @Finset.filter _ (fun c => clauseSat (fun v => s (eVar G v)) ((hcList G)[c.val]'c.isLt))
    (Classical.decPred _) Finset.univ

private noncomputable def softSatOf (G : Cfg) (s : Fin (numV G) → Bool) : Finset (Fin (softN G)) :=
  Finset.univ.filter (fun r =>
    s (eVar G (vDP (Fin.last (G.q + 1)) ⟨2 * r.val + 2, by have := r.isLt; dsimp [softN] at this; omega⟩)) = true)

private lemma crOf_apply (G : Cfg) (p : Fin G.q × Fin G.m) : crOf G p = cBank G p := rfl
private lemma cvOf_apply (G : Cfg) (p : Fin G.q × Fin G.n) : cvOf G p = eVar G (vBank p.1 p.2) := rfl
private lemma ioOf_apply (G : Cfg) (i : Fin G.t) : ioOf G i = eOcc G (Sum.inl i) := rfl

private lemma cBank_ne_cPin (G : Cfg) (p : Fin G.q × Fin G.m) : cBank G p ≠ cPin G := by
  intro h; have h1 := (eCl G).injective h; cases h1

private lemma cHard_ne_cPin (G : Cfg) (c : Fin (hcLen G)) (r : Fin (wRep G)) : cHard G c r ≠ cPin G := by
  intro h; have h1 := Sum.inr.inj ((eCl G).injective h); cases h1

private lemma cSoft_ne_cPin (G : Cfg) (r : Fin (softN G)) : cSoft G r ≠ cPin G := by
  intro h; have h1 := Sum.inr.inj ((eCl G).injective h); cases h1

private lemma cBank_ne_cHard (G : Cfg) (p : Fin G.q × Fin G.m) (c : Fin (hcLen G)) (r : Fin (wRep G)) :
    cBank G p ≠ cHard G c r := by
  intro h; have h1 := (eCl G).injective h; cases h1

private lemma cBank_ne_cSoft (G : Cfg) (p : Fin G.q × Fin G.m) (r : Fin (softN G)) :
    cBank G p ≠ cSoft G r := by
  intro h; have h1 := (eCl G).injective h; cases h1

private lemma cHard_ne_cSoft (G : Cfg) (c : Fin (hcLen G)) (rep : Fin (wRep G)) (r : Fin (softN G)) :
    cHard G c rep ≠ cSoft G r := by
  intro h; have h1 := Sum.inr.inj (Sum.inr.inj ((eCl G).injective h)); cases h1

private lemma cHard_inj (G : Cfg) {c1 c2 : Fin (hcLen G)} {r1 r2 : Fin (wRep G)}
    (h : cHard G c1 r1 = cHard G c2 r2) : c1 = c2 ∧ r1 = r2 :=
  Prod.mk.inj (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj ((eCl G).injective h))))

private lemma cSoft_inj (G : Cfg) {r1 r2 : Fin (softN G)} (h : cSoft G r1 = cSoft G r2) : r1 = r2 :=
  Sum.inr.inj (Sum.inr.inj (Sum.inr.inj ((eCl G).injective h)))

private lemma cfg_size_le (G : Cfg) :
    numT G + numM G + numV G ≤ 256 * (G.q + 2) * (G.t + G.q * G.m + G.q * G.n + G.D.size + (G.q + 2) ^ 2 + 1) := by
  have hHC_b := hardClauses_bounds (q := G.q) (n := G.n) G.D
  have hN_eq : numV G = G.q * G.n + (G.q + 2 + G.D.size) + 1 + (G.q + 2) * (G.q + 2) := by
    dsimp only [numV, VarT]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
    ring
  have hM_eq : numM G = G.q * G.m + 1 + hcLen G * wRep G + softN G := by
    dsimp only [numM, ClT]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
    ring
  have hHO_le : Fintype.card (HardOcc G) ≤ 3 * hcLen G * wRep G := by
    rw [Fintype.card_sigma]
    calc
      ∑ c : Fin (hcLen G), Fintype.card (Fin ((hcList G)[c.val]'c.isLt).length × Fin (wRep G))
          = ∑ c : Fin (hcLen G), ((hcList G)[c.val]'c.isLt).length * wRep G := by
              refine Finset.sum_congr rfl fun c _ => by simp only [Fintype.card_prod, Fintype.card_fin]
      _ ≤ ∑ _c : Fin (hcLen G), 3 * wRep G := Finset.sum_le_sum fun c _ =>
            Nat.mul_le_mul_right (wRep G) (hHC_b.2 _ (List.getElem_mem c.isLt))
      _ = hcLen G * (3 * wRep G) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = 3 * hcLen G * wRep G := by ring
  have hT_le : numT G ≤ G.t + 1 + G.q * G.m + 3 * hcLen G * wRep G + softN G := by
    have hTeq : numT G = G.t + 1 + G.q * G.m + Fintype.card (HardOcc G) + softN G := by
      dsimp only [numT, OccT]
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
      ring
    omega
  have hHC_le : hcLen G ≤ 4 + 3 * G.D.size + 3 * (G.q + 2) ^ 2 := hHC_b.1
  have hsoft_le : softN G ≤ G.q + 2 := by dsimp [softN]; omega
  have hHCW : hcLen G * wRep G ≤ (G.q + 2) * (4 + 3 * G.D.size + 3 * (G.q + 2) ^ 2) := by
    dsimp only [wRep]; rw [mul_comm]; exact Nat.mul_le_mul_left (G.q + 2) hHC_le
  have ht1 : G.t ≤ (G.q + 2) * G.t := Nat.le_mul_of_pos_left G.t (by omega)
  have hqm1 : G.q * G.m ≤ (G.q + 2) * (G.q * G.m) := Nat.le_mul_of_pos_left _ (by omega)
  have hqn1 : G.q * G.n ≤ (G.q + 2) * (G.q * G.n) := Nat.le_mul_of_pos_left _ (by omega)
  have hds1 : G.D.size ≤ (G.q + 2) * G.D.size := Nat.le_mul_of_pos_left _ (by omega)
  have hsq1 : (G.q + 2) * (G.q + 2) ≤ (G.q + 2) * (G.q + 2) ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

private lemma cfg_io_spec (G : Cfg) (i : Fin G.t) :
    clF G (ioOf G i) = crOf G (G.bank i, G.row i) ∧
    vrF G (ioOf G i) = cvOf G (G.bank i, G.var i) ∧
    sgF G (ioOf G i) = G.sign i := by
  rw [ioOf_apply]
  simp only [clF, vrF, sgF, Equiv.symm_apply_apply, clOf, vrOf, sgOf, and_self]

private lemma cfg_pin_not_base (G : Cfg) : pinOf G ∉ baseOf G := by
  simp only [pinOf, baseOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  decide

private lemma cfg_io_props (G : Cfg) (i : Fin G.t) : ioOf G i ∉ baseOf G ∧ ioOf G i ≠ pinOf G := by
  rw [ioOf_apply]
  refine ⟨?_, fun h => ?_⟩
  · simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]; decide
  · have h1 := (eOcc G).injective h; cases h1

private lemma cfg_sg_pin (G : Cfg) : sgF G (pinOf G) = true := by
  simp only [sgF, pinOf, Equiv.symm_apply_apply, sgOf]

private lemma cfg_cl_pin (G : Cfg) : clF G (pinOf G) = cPin G := by
  simp only [clF, pinOf, Equiv.symm_apply_apply, clOf]

private lemma cfg_vr_pin (G : Cfg) : vrF G (pinOf G) = eVar G vPin := by
  simp only [vrF, pinOf, Equiv.symm_apply_apply, vrOf]

private lemma cfg_cl_pin_uniq (G : Cfg) (v : Fin (numT G)) (hv : clF G v = clF G (pinOf G)) :
    v = pinOf G := by
  rw [cfg_cl_pin] at hv
  dsimp only [clF] at hv
  cases h : (eOcc G).symm v with
  | inl i =>
    rw [h] at hv; dsimp only [clOf] at hv; rw [crOf_apply] at hv
    exact absurd hv (cBank_ne_cPin G _)
  | inr x =>
    cases x with
    | inl u =>
      cases u
      exact (eOcc G).symm.injective (h.trans (by simp only [pinOf, Equiv.symm_apply_apply]))
    | inr y =>
      rw [h] at hv
      cases y with
      | inl p =>
        dsimp only [clOf] at hv; rw [crOf_apply] at hv
        exact absurd hv (cBank_ne_cPin G p)
      | inr z =>
        cases z with
        | inl ho =>
          rcases ho with ⟨c, lit, rep⟩
          dsimp only [clOf] at hv
          exact absurd hv (cHard_ne_cPin G c rep)
        | inr r =>
          dsimp only [clOf] at hv
          exact absurd hv (cSoft_ne_cPin G r)

private lemma cfg_sat_insert_pin (G : Cfg) (X : Finset (Fin G.t)) (s : Fin (numV G) → Bool) :
    let Y := baseOf G ∪ X.map (ioOf G)
    (satSet G (insert (pinOf G) Y) s).card = (satSet G Y s).card + (s (vrF G (pinOf G))).toNat := by
  intro Y
  have hcPin_notin : clF G (pinOf G) ∉ satSet G Y s := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨v, hv, hvcl⟩
    have hvp : v = pinOf G := cfg_cl_pin_uniq G v hvcl
    subst hvp
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hb | hx
    · exact cfg_pin_not_base G hb
    · rcases Finset.mem_map.mp hx with ⟨i, _, hi⟩
      exact (cfg_io_props G i).2 hi
  by_cases hsp : s (vrF G (pinOf G)) = true
  · have hEq : satSet G (insert (pinOf G) Y) s = insert (clF G (pinOf G)) (satSet G Y s) := by
      ext c
      simp only [satSet, Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨v, ⟨rfl | hvY, hvs⟩, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v, ⟨hvY, hvs⟩, rfl⟩
      · rintro (rfl | ⟨v, ⟨hvY, hvs⟩, rfl⟩)
        · exact ⟨pinOf G, ⟨Or.inl rfl, hsp.trans (cfg_sg_pin G).symm⟩, rfl⟩
        · exact ⟨v, ⟨Or.inr hvY, hvs⟩, rfl⟩
    rw [hEq, Finset.card_insert_of_notMem hcPin_notin, hsp]; rfl
  · have hspf : s (vrF G (pinOf G)) = false := by cases h : s (vrF G (pinOf G)) <;> simp_all
    have hEq : satSet G (insert (pinOf G) Y) s = satSet G Y s := by
      ext c
      simp only [satSet, Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨v, ⟨rfl | hvY, hvs⟩, rfl⟩
        · rw [hspf, cfg_sg_pin G] at hvs; cases hvs
        · exact ⟨v, ⟨hvY, hvs⟩, rfl⟩
      · rintro ⟨v, ⟨hvY, hvs⟩, rfl⟩
        exact ⟨v, ⟨Or.inr hvY, hvs⟩, rfl⟩
    rw [hEq, hspf]; rfl

private lemma cfg_sat_split (G : Cfg) (X : Finset (Fin G.t)) (s : Fin (numV G) → Bool) :
    let Y := baseOf G ∪ X.map (ioOf G)
    (satSet G Y s).card =
      (bankSatOf G X s).card + (hardSatOf G s).card * wRep G + (softSatOf G s).card := by
  intro Y
  have hmem_bank : ∀ p : Fin G.q × Fin G.m, crOf G p ∈ satSet G Y s ↔ p ∈ bankSatOf G X s := by
    intro p
    simp only [satSet, bankSatOf, Y, Finset.mem_image, Finset.mem_filter, Finset.mem_union,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨hb | ⟨i, hiX, rfl⟩, hvs⟩, hvcl⟩
      · cases he : (eOcc G).symm v with
        | inl i => simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
        | inr x =>
          cases x with
          | inl u => cases u; simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
          | inr y =>
            cases y with
            | inl p' =>
              dsimp only [clF, vrF, sgF] at hvcl hvs; rw [he] at hvcl hvs
              dsimp only [clOf, vrOf, sgOf] at hvcl hvs
              have hp : p' = p := (crOf G).injective hvcl
              subst hp; exact Or.inl hvs
            | inr z =>
              dsimp only [clF] at hvcl; rw [he] at hvcl
              cases z with
              | inl ho =>
                rcases ho with ⟨c, lit, rep⟩
                dsimp only [clOf] at hvcl; rw [crOf_apply] at hvcl
                exact absurd hvcl.symm (cBank_ne_cHard G p c rep)
              | inr r =>
                dsimp only [clOf] at hvcl; rw [crOf_apply] at hvcl
                exact absurd hvcl.symm (cBank_ne_cSoft G p r)
      · have hsp := cfg_io_spec G i
        rw [hsp.1] at hvcl; rw [hsp.2.1, hsp.2.2, cvOf_apply] at hvs
        have hp := (crOf G).injective hvcl
        have hbi : G.bank i = p.1 := congrArg Prod.fst hp
        have hri : G.row i = p.2 := congrArg Prod.snd hp
        rw [hbi] at hvs
        exact Or.inr ⟨i, hiX, hbi, hri, hvs⟩
    · rintro (hw | ⟨i, hiX, hbi, hri, hsi⟩)
      · refine ⟨eOcc G (Sum.inr (Sum.inr (Sum.inl p))), ⟨Or.inl ?_, ?_⟩, ?_⟩
        · simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
        · simp only [vrF, sgF, Equiv.symm_apply_apply, vrOf, sgOf]; exact hw
        · simp only [clF, Equiv.symm_apply_apply, clOf]
      · refine ⟨ioOf G i, ⟨Or.inr ⟨i, hiX, rfl⟩, ?_⟩, ?_⟩
        · rw [(cfg_io_spec G i).2.1, (cfg_io_spec G i).2.2, cvOf_apply, hbi]; exact hsi
        · rw [(cfg_io_spec G i).1, hbi, hri]
  have hmem_hard : ∀ (c : Fin (hcLen G)) (rep : Fin (wRep G)),
      cHard G c rep ∈ satSet G Y s ↔ c ∈ hardSatOf G s := by
    intro c rep
    simp only [hardSatOf, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [satSet, Y, Finset.mem_image, Finset.mem_filter, Finset.mem_union,
      Finset.mem_map, clauseSat]
    constructor
    · rintro ⟨v, ⟨hb | ⟨i, _, rfl⟩, hvs⟩, hvcl⟩
      · cases he : (eOcc G).symm v with
        | inl i => simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
        | inr x =>
          cases x with
          | inl u => cases u; simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
          | inr y =>
            cases y with
            | inl p' =>
              dsimp only [clF] at hvcl; rw [he] at hvcl
              dsimp only [clOf] at hvcl; rw [crOf_apply] at hvcl
              exact absurd hvcl (cBank_ne_cHard G p' c rep)
            | inr z =>
              cases z with
              | inl ho =>
                rcases ho with ⟨c', lit, rep'⟩
                dsimp only [clF, vrF, sgF] at hvcl hvs; rw [he] at hvcl hvs
                dsimp only [clOf, vrOf, sgOf] at hvcl hvs
                have hce : c' = c := (cHard_inj G hvcl).1
                subst hce
                exact ⟨((hcList G)[c'.val]'c'.isLt)[lit.val]'lit.isLt, List.getElem_mem lit.isLt, hvs⟩
              | inr r =>
                dsimp only [clF] at hvcl; rw [he] at hvcl
                dsimp only [clOf] at hvcl
                exact absurd hvcl.symm (cHard_ne_cSoft G c rep r)
      · rw [(cfg_io_spec G i).1, crOf_apply] at hvcl
        exact absurd hvcl (cBank_ne_cHard G _ c rep)
    · rintro ⟨p, hp, hsp⟩
      rcases List.getElem_of_mem hp with ⟨idx, hidx, rfl⟩
      refine ⟨eOcc G (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, ⟨idx, hidx⟩, rep⟩)))), ⟨Or.inl ?_, ?_⟩, ?_⟩
      · simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      · simp only [vrF, sgF, Equiv.symm_apply_apply, vrOf, sgOf]; exact hsp
      · simp only [clF, Equiv.symm_apply_apply, clOf]
  have hmem_soft : ∀ r : Fin (softN G), cSoft G r ∈ satSet G Y s ↔ r ∈ softSatOf G s := by
    intro r
    simp only [satSet, softSatOf, Y, Finset.mem_image, Finset.mem_filter, Finset.mem_union,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨hb | ⟨i, _, rfl⟩, hvs⟩, hvcl⟩
      · cases he : (eOcc G).symm v with
        | inl i => simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
        | inr x =>
          cases x with
          | inl u => cases u; simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, he] at hb; cases hb
          | inr y =>
            cases y with
            | inl p' =>
              dsimp only [clF] at hvcl; rw [he] at hvcl
              dsimp only [clOf] at hvcl; rw [crOf_apply] at hvcl
              exact absurd hvcl (cBank_ne_cSoft G p' r)
            | inr z =>
              cases z with
              | inl ho =>
                rcases ho with ⟨c', lit, rep'⟩
                dsimp only [clF] at hvcl; rw [he] at hvcl
                dsimp only [clOf] at hvcl
                exact absurd hvcl (cHard_ne_cSoft G c' rep' r)
              | inr r' =>
                dsimp only [clF, vrF, sgF] at hvcl hvs; rw [he] at hvcl hvs
                dsimp only [clOf, vrOf, sgOf] at hvcl hvs
                have hre : r' = r := cSoft_inj G hvcl
                subst hre; exact hvs
      · rw [(cfg_io_spec G i).1, crOf_apply] at hvcl
        exact absurd hvcl (cBank_ne_cSoft G _ r)
    · intro hr
      refine ⟨eOcc G (Sum.inr (Sum.inr (Sum.inr (Sum.inr r)))), ⟨Or.inl ?_, ?_⟩, ?_⟩
      · simp only [baseOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      · simp only [vrF, sgF, Equiv.symm_apply_apply, vrOf, sgOf]; exact hr
      · simp only [clF, Equiv.symm_apply_apply, clOf]
  have hno_pin : cPin G ∉ satSet G Y s := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨v, hv, hvcl⟩
    have hvp : v = pinOf G := cfg_cl_pin_uniq G v (hvcl.trans (cfg_cl_pin G).symm)
    subst hvp
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hb | hx
    · exact cfg_pin_not_base G hb
    · rcases Finset.mem_map.mp hx with ⟨i, _, hi⟩; exact (cfg_io_props G i).2 hi
  let SB := (bankSatOf G X s).image (crOf G)
  let SH := (hardSatOf G s ×ˢ (Finset.univ : Finset (Fin (wRep G)))).image (fun crp => cHard G crp.1 crp.2)
  let SS := (softSatOf G s).image (cSoft G)
  have hunion : satSet G Y s = SB ∪ SH ∪ SS := by
    ext c
    simp only [Finset.mem_union, SB, SH, SS, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    cases hc : (eCl G).symm c with
    | inl p =>
      have hce : c = crOf G p := by rw [← (eCl G).apply_symm_apply c, hc]; rfl
      subst hce
      rw [hmem_bank p]
      constructor
      · intro hp; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      · rintro ((⟨p', hp', heq⟩ | ⟨⟨c', rep'⟩, _, heq⟩) | ⟨r', _, heq⟩)
        · rwa [← (crOf G).injective heq]
        · rw [crOf_apply] at heq; exact absurd heq.symm (cBank_ne_cHard G p c' rep')
        · rw [crOf_apply] at heq; exact absurd heq.symm (cBank_ne_cSoft G p r')
    | inr x =>
      cases x with
      | inl u =>
        cases u
        have hce : c = cPin G := by rw [← (eCl G).apply_symm_apply c, hc]; rfl
        subst hce
        constructor
        · intro h; exact absurd h hno_pin
        · rintro ((⟨p', _, heq⟩ | ⟨⟨c', rep'⟩, _, heq⟩) | ⟨r', _, heq⟩)
          · rw [crOf_apply] at heq; exact absurd heq (cBank_ne_cPin G p')
          · exact absurd heq (cHard_ne_cPin G c' rep')
          · exact absurd heq (cSoft_ne_cPin G r')
      | inr y =>
        cases y with
        | inl p =>
          have hce : c = cHard G p.1 p.2 := by rw [← (eCl G).apply_symm_apply c, hc]; rfl
          subst hce
          rw [hmem_hard p.1 p.2]
          constructor
          · intro h; exact Or.inl (Or.inr ⟨(p.1, p.2), h, rfl⟩)
          · rintro ((⟨p', _, heq⟩ | ⟨⟨c', rep'⟩, hc', heq⟩) | ⟨r', _, heq⟩)
            · rw [crOf_apply] at heq; exact absurd heq (cBank_ne_cHard G p' p.1 p.2)
            · rwa [← (cHard_inj G heq).1]
            · exact absurd heq.symm (cHard_ne_cSoft G p.1 p.2 r')
        | inr r =>
          have hce : c = cSoft G r := by rw [← (eCl G).apply_symm_apply c, hc]; rfl
          subst hce
          rw [hmem_soft r]
          constructor
          · intro h; exact Or.inr ⟨r, h, rfl⟩
          · rintro ((⟨p', _, heq⟩ | ⟨⟨c', rep'⟩, _, heq⟩) | ⟨r', hr', heq⟩)
            · rw [crOf_apply] at heq; exact absurd heq (cBank_ne_cSoft G p' r)
            · exact absurd heq (cHard_ne_cSoft G c' rep' r)
            · rwa [← cSoft_inj G heq]
  have hd1 : Disjoint SB SH := by
    rw [Finset.disjoint_left]; intro c h1 h2
    rcases Finset.mem_image.mp h1 with ⟨p, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨⟨c', r'⟩, _, heq⟩
    rw [crOf_apply] at heq; exact cBank_ne_cHard G p c' r' heq.symm
  have hd2 : Disjoint (SB ∪ SH) SS := by
    rw [Finset.disjoint_left]; intro c h1 h2
    rcases Finset.mem_image.mp h2 with ⟨r, _, rfl⟩
    rcases Finset.mem_union.mp h1 with hB | hH
    · rcases Finset.mem_image.mp hB with ⟨p, _, heq⟩
      rw [crOf_apply] at heq; exact cBank_ne_cSoft G p r heq
    · rcases Finset.mem_image.mp hH with ⟨⟨c', r'⟩, _, heq⟩
      exact cHard_ne_cSoft G c' r' r heq
  have hcard_SB : SB.card = (bankSatOf G X s).card := Finset.card_image_of_injective _ (crOf G).injective
  have hcard_SH : SH.card = (hardSatOf G s).card * wRep G := by
    have hinj : Function.Injective (fun crp : Fin (hcLen G) × Fin (wRep G) => cHard G crp.1 crp.2) := by
      rintro ⟨c1, r1⟩ ⟨c2, r2⟩ heq
      have h := cHard_inj G heq
      exact Prod.ext h.1 h.2
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hcard_SS : SS.card = (softSatOf G s).card :=
    Finset.card_image_of_injective _ (fun _ _ h => cSoft_inj G h)
  rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    hcard_SB, hcard_SH, hcard_SS]

private lemma cfg_upper (G : Cfg)
    (hfan : PEqualNP.MetaComplexity.FanInTwo G.D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (G.q + 2) G.D)
    (hout : G.D.output < G.q + 2 + G.D.size)
    (X : Finset (Fin G.t)) (s : Fin (numV G) → Bool) :
    let S := answersOf G X
    let b := G.D.eval (List.ofFn (fun i : Fin G.q => decide (i ∈ S)) ++ [false, true])
    let Y := baseOf G ∪ X.map (ioOf G)
    let a := (S.card + 1 - b.toNat) / 2
    (satSet G Y s).card ≤ Hval G + a ∧
      (b = false → s (vrF G (pinOf G)) = true → (satSet G Y s).card + 1 ≤ Hval G + a) := by
  intro S b Y a
  let sV : VarT G.q G.n G.D.size → Bool := fun v => s (eVar G v)
  have hsp := cfg_sat_split G X s
  dsimp only at hsp
  have hbank_le_qm : (bankSatOf G X s).card ≤ G.q * G.m := by
    calc (bankSatOf G X s).card ≤ (Finset.univ : Finset (Fin G.q × Fin G.m)).card := Finset.card_le_univ _
    _ = G.q * G.m := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hsoft_le_q : (softSatOf G s).card ≤ G.q := by
    calc (softSatOf G s).card ≤ (Finset.univ : Finset (Fin (softN G))).card := Finset.card_le_univ _
    _ = softN G := by rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ G.q := by dsimp [softN]; omega
  by_cases hAllHard : (hardSatOf G s).card = hcLen G
  · have hall_hard : ∀ c ∈ hardClauses (q := G.q) (n := G.n) G.D, clauseSat sV c := by
      intro c hc
      rcases List.getElem_of_mem hc with ⟨idx, hidx, rfl⟩
      have hfull : hardSatOf G s = Finset.univ :=
        Finset.eq_univ_of_card (hardSatOf G s) (by rw [Fintype.card_fin]; exact hAllHard)
      have hmem : (⟨idx, hidx⟩ : Fin (hcLen G)) ∈ hardSatOf G s := by rw [hfull]; exact Finset.mem_univ _
      simp only [hardSatOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    have hdp_sat : ∀ c ∈ dpClauses G.q G.n G.D.size, clauseSat sV c := fun c hc =>
      hall_hard c (by dsimp only [hardClauses]; exact List.mem_append_right _ hc)
    have hwev := hardClauses_wires_eval G.D hfan hrb hout sV hall_hard
    let wSet : Finset (Fin G.q) :=
      Finset.univ.filter (fun k : Fin G.q => sV (vWire ⟨k.val, by have := k.isLt; omega⟩) = true)
    let bad := wSet \ S
    let good := wSet ∩ S
    have hw_split : good.card + bad.card = wSet.card := by
      have h := Finset.card_sdiff_add_card_inter wSet S
      dsimp only [good, bad]; omega
    have hgood_le : good.card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
    have hbank_loss : (bankSatOf G X s).card + bad.card ≤ G.q * G.m := by
      have hmiss : ∀ k ∈ bad, ∃ j : Fin G.m, (k, j) ∉ bankSatOf G X s := by
        intro k hk
        have hkw : sV (vWire ⟨k.val, by have := k.isLt; omega⟩) = true :=
          (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).2
        have hkS : k ∉ S := (Finset.mem_sdiff.mp hk).2
        have hnotSat : ¬ ∀ j : Fin G.m,
            ∃ i ∈ X, G.bank i = k ∧ G.row i = j ∧ sV (vBank k (G.var i)) = G.sign i := by
          intro hall
          apply hkS
          simp only [S, answersOf, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun v => sV (vBank k v), hall⟩
        push Not at hnotSat
        rcases hnotSat with ⟨j, hj⟩
        refine ⟨j, fun hmem => ?_⟩
        simp only [bankSatOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with hf | ⟨i, hiX, hbi, hri, hsi⟩
        · change sV (vWire ⟨k.val, by have := k.isLt; omega⟩) = false at hf
          rw [hkw] at hf; cases hf
        · exact hj i hiX hbi hri hsi
      choose jMiss hjMiss using fun (k : ↥bad) => hmiss k.val k.property
      let missSet : Finset (Fin G.q × Fin G.m) := Finset.univ.image (fun k : ↥bad => (k.val, jMiss k))
      have hmiss_card : missSet.card = bad.card := by
        have hinj : Function.Injective (fun k : ↥bad => (k.val, jMiss k)) := fun _ _ h =>
          Subtype.ext (congrArg Prod.fst h)
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
      have hdisj : Disjoint (bankSatOf G X s) missSet := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        rcases Finset.mem_image.mp hp2 with ⟨k, _, rfl⟩
        exact hjMiss k hp1
      calc
        (bankSatOf G X s).card + bad.card = (bankSatOf G X s).card + missSet.card := by rw [hmiss_card]
        _ = (bankSatOf G X s ∪ missSet).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (Finset.univ : Finset (Fin G.q × Fin G.m)).card := Finset.card_le_univ _
        _ = G.q * G.m := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have huc_eq : uCount sV (G.q + 1) = wSet.card + (if sV vPin = false then 1 else 0) := by
      dsimp only [uCount]
      let f : Fin G.q → Fin (G.q + 1) := fun k => ⟨k.val, by omega⟩
      have hlast_eq : (Finset.univ : Finset (Fin (G.q + 1))).filter (fun r => r.val < G.q + 1 ∧ uVal sV r = true) =
          (wSet.image f) ∪ (if sV vPin = false then {Fin.last G.q} else ∅) := by
        ext r
        simp only [wSet, Finset.mem_filter, Finset.mem_univ, true_and, r.isLt, Finset.mem_union, Finset.mem_image]
        by_cases hrq : r.val < G.q
        · have hneq : r ≠ Fin.last G.q := fun h => by
            have := congrArg Fin.val h; simp only [Fin.val_last] at this; omega
          have hnotin : r ∉ (if sV vPin = false then ({Fin.last G.q} : Finset (Fin (G.q + 1))) else ∅) := by
            split_ifs <;> simp [hneq]
          simp only [hnotin, or_false]
          have huv : uVal sV r = sV (vWire ⟨r.val, by omega⟩) := by dsimp [uVal]; rw [dite_eq_left hrq]
          rw [huv]
          constructor
          · intro h; exact ⟨⟨r.val, hrq⟩, h, Fin.ext rfl⟩
          · rintro ⟨k, hk, hke⟩
            have hkv : k.val = r.val := congrArg Fin.val hke
            have : (⟨r.val, by omega⟩ : Fin (G.q + 2 + G.D.size)) = ⟨k.val, by omega⟩ := Fin.ext hkv.symm
            rw [this]; exact hk
        · have hreq : r = Fin.last G.q := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
          subst hreq
          have huv : uVal sV (Fin.last G.q) = !(sV vPin) := by
            dsimp only [uVal, Fin.last]; rw [dite_eq_right (by omega)]
          rw [huv]
          constructor
          · intro h; right; cases hp : sV vPin <;> simp_all
          · rintro (⟨k, _, hk⟩ | h)
            · have := congrArg Fin.val hk; dsimp only [f, Fin.last] at this; have := k.isLt; omega
            · cases hp : sV vPin <;> simp_all
      rw [hlast_eq]
      have hdisj : Disjoint (wSet.image f) (if sV vPin = false then {Fin.last G.q} else ∅) := by
        rw [Finset.disjoint_left]; intro r h1 h2
        rcases Finset.mem_image.mp h1 with ⟨k, _, rfl⟩
        split_ifs at h2 with hp
        · rw [Finset.mem_singleton] at h2
          have := congrArg Fin.val h2; dsimp only [f, Fin.last] at this; have := k.isLt; omega
        · exact Finset.notMem_empty _ h2
      have hfinj : Function.Injective f := fun _ _ h => Fin.ext (congrArg (fun x : Fin (G.q + 1) => x.val) h)
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective wSet hfinj]
      split_ifs <;> simp
    have hsoft_bound : (softSatOf G s).card ≤ (wSet.card + 1 - (sV vPin).toNat) / 2 := by
      have hsub : softSatOf G s ⊆ Finset.univ.filter (fun r : Fin (softN G) => r.val < uCount sV (G.q + 1) / 2) := by
        intro r hr
        simp only [softSatOf, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        have hsnd := dpClauses_sound sV hdp_sat (Fin.last (G.q + 1))
          ⟨2 * r.val + 1, by have := r.isLt; dsimp [softN] at this; omega⟩ hr
        simp only [Fin.val_last] at hsnd
        omega
      have hcard_lt : (Finset.univ.filter (fun r : Fin (softN G) => r.val < uCount sV (G.q + 1) / 2)).card ≤
          uCount sV (G.q + 1) / 2 := by
        have hsub2 : (Finset.univ.filter (fun r : Fin (softN G) => r.val < uCount sV (G.q + 1) / 2)).image Fin.val ⊆
            Finset.range (uCount sV (G.q + 1) / 2) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
        calc
          (Finset.univ.filter (fun r : Fin (softN G) => r.val < uCount sV (G.q + 1) / 2)).card
              = ((Finset.univ.filter (fun r : Fin (softN G) => r.val < uCount sV (G.q + 1) / 2)).image Fin.val).card :=
                  (Finset.card_image_of_injective _ Fin.val_injective).symm
          _ ≤ (Finset.range (uCount sV (G.q + 1) / 2)).card := Finset.card_le_card hsub2
          _ = uCount sV (G.q + 1) / 2 := Finset.card_range _
      have hle := (Finset.card_le_card hsub).trans hcard_lt
      rw [huc_eq] at hle
      cases hp : sV vPin <;> simp [hp] at hle ⊢ <;> omega
    have hpin_eq_y : s (vrF G (pinOf G)) = sV vPin := by rw [cfg_vr_pin]
    have hscore_le : (satSet G Y s).card + bad.card ≤ Hval G + (wSet.card + 1 - (sV vPin).toNat) / 2 := by
      rw [hsp, hAllHard]; dsimp only [Hval]; omega
    by_cases hwS : wSet = S
    · have hbad0 : bad.card = 0 := by simp [bad, hwS]
      have hinp_eq : List.ofFn (fun k : Fin G.q => sV (vWire ⟨k.val, by omega⟩)) ++ [false, true] =
          List.ofFn (fun k : Fin G.q => decide (k ∈ S)) ++ [false, true] := by
        congr 1; apply List.ext_getElem (by simp)
        intro idx h1 h2; simp only [List.getElem_ofFn]
        have hmem : (⟨idx, by simpa using h1⟩ : Fin G.q) ∈ wSet ↔ (⟨idx, by simpa using h1⟩ : Fin G.q) ∈ S := by
          rw [hwS]
        simp only [wSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact Bool.eq_iff_iff.mpr (hmem.trans decide_eq_true_iff.symm)
      have hyb : sV vPin = b := by rw [hwev.2, hinp_eq]
      constructor
      · rw [hwS, hyb, hbad0, add_zero] at hscore_le; exact hscore_le
      · intro hbf hpt; rw [hpin_eq_y, hyb, hbf] at hpt; cases hpt
    · have hcase : 1 ≤ bad.card ∨ good.card + 1 ≤ S.card := by
        by_contra hnot; push Not at hnot
        have hbad0 : bad = ∅ := Finset.card_eq_zero.mp (by omega)
        have hsub : wSet ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp hbad0
        have hgeq : good = wSet := Finset.inter_eq_left.mpr hsub
        have hcard_eq : wSet.card = S.card := by rw [← hgeq]; omega
        exact hwS (Finset.eq_of_subset_of_card_le hsub (by omega))
      constructor
      · dsimp only [a]
        rcases hcase with hbad1 | hgoodlt <;> cases hb : b <;> cases hy : sV vPin <;> simp [hb, hy] at hscore_le ⊢ <;> omega
      · intro hbf hpt
        rw [hpin_eq_y] at hpt
        dsimp only [a]
        rw [hbf] at *; rw [hpt] at hscore_le
        rcases hcase with hbad1 | hgoodlt <;> simp at hscore_le ⊢ <;> omega
  · have hHC_le : (hardSatOf G s).card ≤ hcLen G := by
      calc (hardSatOf G s).card ≤ (Finset.univ : Finset (Fin (hcLen G))).card := Finset.card_le_univ _
      _ = hcLen G := by rw [Finset.card_univ, Fintype.card_fin]
    have hlt : (hardSatOf G s).card + 1 ≤ hcLen G := by omega
    have hmul : (hardSatOf G s).card * wRep G + wRep G ≤ hcLen G * wRep G := by
      calc (hardSatOf G s).card * wRep G + wRep G = ((hardSatOf G s).card + 1) * wRep G := by ring
      _ ≤ hcLen G * wRep G := Nat.mul_le_mul_right (wRep G) hlt
    constructor
    · rw [hsp]; dsimp only [Hval, wRep] at hmul ⊢; omega
    · intro _ _; rw [hsp]; dsimp only [Hval, wRep] at hmul ⊢; omega

private lemma cfg_opt (G : Cfg)
    (hfan : PEqualNP.MetaComplexity.FanInTwo G.D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (G.q + 2) G.D)
    (hout : G.D.output < G.q + 2 + G.D.size)
    (X : Finset (Fin G.t)) :
    let S := answersOf G X
    let b := G.D.eval (List.ofFn (fun i : Fin G.q => decide (i ∈ S)) ++ [false, true])
    let Y := baseOf G ∪ X.map (ioOf G)
    let a := (S.card + 1 - b.toNat) / 2
    ∃ sOpt : Fin (numV G) → Bool, (satSet G Y sOpt).card = Hval G + a ∧ sOpt (vrF G (pinOf G)) = b := by
  intro S b Y a
  have hbank_wit : ∀ k : Fin G.q, k ∈ S →
      ∃ sk : Fin G.n → Bool, ∀ j : Fin G.m, ∃ i ∈ X, G.bank i = k ∧ G.row i = j ∧ sk (G.var i) = G.sign i := by
    intro k hk; simp only [S, answersOf, Finset.mem_filter, Finset.mem_univ, true_and] at hk; exact hk
  let skOf : Fin G.q → Fin G.n → Bool := fun k =>
    if hk : k ∈ S then Classical.choose (hbank_wit k hk) else fun _ => false
  let inpS := List.ofFn (fun k : Fin G.q => decide (k ∈ S)) ++ [false, true]
  let wireVals := G.D.wires inpS
  let sBase : VarT G.q G.n G.D.size → Bool := fun v =>
    match v with
    | Sum.inl (k, u) => skOf k u
    | Sum.inr (Sum.inl w) => wireVals.getD w.val false
    | Sum.inr (Sum.inr (Sum.inl ())) => b
    | Sum.inr (Sum.inr (Sum.inr _)) => false
  let sOptV : VarT G.q G.n G.D.size → Bool := fun v =>
    match v with
    | Sum.inl (k, u) => skOf k u
    | Sum.inr (Sum.inl w) => wireVals.getD w.val false
    | Sum.inr (Sum.inr (Sum.inl ())) => b
    | Sum.inr (Sum.inr (Sum.inr (i, j))) => decide (j.val ≤ uCount sBase i.val)
  let sOpt : Fin (numV G) → Bool := fun v => sOptV ((eVar G).symm v)
  have hsOpt_eval : ∀ v : VarT G.q G.n G.D.size, sOpt (eVar G v) = sOptV v := fun v => by
    simp only [sOpt, Equiv.symm_apply_apply]
  have huVal_eq : ∀ i : Fin (G.q + 1), uVal sOptV i = uVal sBase i := by
    intro i; dsimp only [uVal]; split_ifs <;> rfl
  have huCount_eq : ∀ i : Nat, uCount sOptV i = uCount sBase i := by
    intro i; dsimp only [uCount]; apply congrArg Finset.card; ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, huVal_eq]
  have hwire_S : ∀ k : Fin G.q, sOptV (vWire ⟨k.val, by omega⟩) = decide (k ∈ S) := by
    intro k
    dsimp only [sOptV, vWire, wireVals]
    rw [circuit_wires_input G.D inpS k.val (by simp [inpS]; omega)]
    dsimp only [inpS]
    rw [getD_append_left (by simp)]
    simp [List.getD_eq_getElem?_getD, k.isLt]
  have hall_hard : ∀ c ∈ hardClauses (q := G.q) (n := G.n) G.D, clauseSat sOptV c := by
    intro c hc
    dsimp only [hardClauses] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
      List.mem_finRange, true_and] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | ⟨g, hg⟩) | hdpC
    · refine ⟨(vWire ⟨G.q, by omega⟩, false), by simp, ?_⟩
      dsimp only [sOptV, vWire, wireVals]
      rw [circuit_wires_input G.D inpS G.q (by simp [inpS])]
      dsimp only [inpS]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    · refine ⟨(vWire ⟨G.q + 1, by omega⟩, true), by simp, ?_⟩
      dsimp only [sOptV, vWire, wireVals]
      rw [circuit_wires_input G.D inpS (G.q + 1) (by simp [inpS])]
      dsimp only [inpS]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      have hsub : G.q + 1 - G.q = 1 := by omega
      simp [hsub]
    · have hwf : wireFin (q := G.q) (sz := G.D.size) G.D.output = ⟨G.D.output, hout⟩ := by
        dsimp [wireFin]; rw [dite_eq_left hout]
      have hout_eq : sOptV (vWire (wireFin G.D.output)) = b := by rw [hwf]; rfl
      cases hb : b
      · exact ⟨(vPin, false), by simp, by simp [sOptV, vPin, hb]⟩
      · exact ⟨(vWire (wireFin G.D.output), true), by simp, by rw [hout_eq, hb]⟩
    · have hwf : wireFin (q := G.q) (sz := G.D.size) G.D.output = ⟨G.D.output, hout⟩ := by
        dsimp [wireFin]; rw [dite_eq_left hout]
      have hout_eq : sOptV (vWire (wireFin G.D.output)) = b := by rw [hwf]; rfl
      cases hb : b
      · exact ⟨(vWire (wireFin G.D.output), false), by simp, by rw [hout_eq, hb]⟩
      · exact ⟨(vPin, true), by simp, by simp [sOptV, vPin, hb]⟩
    · refine ((gateTseitin_iff G.D hfan hrb g sOptV).mpr ?_) c hg
      have hinp_len : inpS.length = G.q + 2 := by simp [inpS]
      have hrb_inp : PEqualNP.MetaComplexity.NestedCover.ReadsBack inpS.length G.D := by
        rw [hinp_len]; exact hrb
      have heval := circuit_wires_gate_readsBack G.D inpS hrb_inp g.val g.isLt
      rw [hinp_len] at heval
      dsimp only [sOptV, vWire, wireVals]
      rw [heval]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      have hilt : i < G.q + 2 + g.val := by
        have h := hrb g.val g.isLt i
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt G.D g.val = G.D.gates[g.val]'g.isLt := by
          dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem g.isLt]; rfl
        rw [hgat] at h; exact h hi
      have hwf : wireFin (q := G.q) (sz := G.D.size) i = ⟨i, by omega⟩ := by
        dsimp [wireFin]; rw [dite_eq_left (by omega)]
      rw [hwf]
    · exact dpClauses_complete sOptV (fun i j => by dsimp only [sOptV, vDP]; rw [huCount_eq]) c hdpC
  have hsp := cfg_sat_split G X sOpt
  dsimp only at hsp
  have hbank_full : (bankSatOf G X sOpt).card = G.q * G.m := by
    have heq : bankSatOf G X sOpt = Finset.univ := by
      ext ⟨k, j⟩
      simp only [bankSatOf, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hsOpt_eval]
      rw [hwire_S k]
      by_cases hk : k ∈ S
      · right
        have hspec := Classical.choose_spec (hbank_wit k hk) j
        rcases hspec with ⟨i, hiX, hbi, hri, hsi⟩
        refine ⟨i, hiX, hbi, hri, ?_⟩
        dsimp only [sOptV, vBank, skOf]; rw [dite_eq_left hk]; exact hsi
      · left; simp [hk]
    rw [heq, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hhard_full : (hardSatOf G sOpt).card = hcLen G := by
    have heq : hardSatOf G sOpt = Finset.univ := by
      ext c
      simp only [hardSatOf, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have : (fun v => sOpt (eVar G v)) = sOptV := funext hsOpt_eval
      rw [this]
      exact hall_hard _ (List.getElem_mem c.isLt)
    rw [heq, Finset.card_univ, Fintype.card_fin]
  have huC_val : uCount sBase (G.q + 1) = S.card + 1 - b.toNat := by
    dsimp only [uCount]
    let f : Fin G.q → Fin (G.q + 1) := fun k => ⟨k.val, by omega⟩
    have hlast : (Finset.univ : Finset (Fin (G.q + 1))).filter (fun r => r.val < G.q + 1 ∧ uVal sBase r = true) =
        (S.image f) ∪ (if b = false then {Fin.last G.q} else ∅) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, r.isLt, Finset.mem_union, Finset.mem_image]
      by_cases hrq : r.val < G.q
      · have hneq : r ≠ Fin.last G.q := fun h => by
          have := congrArg Fin.val h; simp only [Fin.val_last] at this; omega
        have hnotin : r ∉ (if b = false then ({Fin.last G.q} : Finset (Fin (G.q + 1))) else ∅) := by
          split_ifs <;> simp [hneq]
        simp only [hnotin, or_false]
        have huv : uVal sBase r = decide ((⟨r.val, hrq⟩ : Fin G.q) ∈ S) := by
          dsimp only [uVal]; rw [dite_eq_left hrq]
          exact hwire_S ⟨r.val, hrq⟩
        rw [huv, decide_eq_true_eq]
        constructor
        · intro h; exact ⟨⟨r.val, hrq⟩, h, Fin.ext rfl⟩
        · rintro ⟨k, hk, hke⟩
          have : (⟨r.val, hrq⟩ : Fin G.q) = k := Fin.ext (congrArg Fin.val hke).symm
          rw [this]; exact hk
      · have hreq : r = Fin.last G.q := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
        subst hreq
        have huv : uVal sBase (Fin.last G.q) = !b := by
          dsimp only [uVal, sBase, vPin, Fin.last]; rw [dite_eq_right (by omega)]
        rw [huv]
        constructor
        · intro h; right; cases hb : b <;> simp_all
        · rintro (⟨k, _, hk⟩ | h)
          · have := congrArg Fin.val hk; dsimp only [f, Fin.last] at this; have := k.isLt; omega
          · cases hb : b <;> simp_all
    rw [hlast]
    have hdisj : Disjoint (S.image f) (if b = false then {Fin.last G.q} else ∅) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      rcases Finset.mem_image.mp h1 with ⟨k, _, rfl⟩
      split_ifs at h2 with hp
      · rw [Finset.mem_singleton] at h2
        have := congrArg Fin.val h2; dsimp only [f, Fin.last] at this; have := k.isLt; omega
      · exact Finset.notMem_empty _ h2
    have hfinj : Function.Injective f := fun _ _ h => Fin.ext (congrArg (fun x : Fin (G.q + 1) => x.val) h)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective S hfinj]
    cases hb : b <;> simp
  have hsoft_val : (softSatOf G sOpt).card = a := by
    have ha_le : a ≤ softN G := by
      dsimp only [a, softN]
      have hSc : S.card ≤ G.q := by simpa using Finset.card_le_univ S
      omega
    have hbij : (softSatOf G sOpt).card = (Finset.univ : Finset (Fin a)).card := by
      symm
      refine Finset.card_bij (fun r _ => ⟨r.val, lt_of_lt_of_le r.isLt ha_le⟩) ?_ ?_ ?_
      · intro r _
        simp only [softSatOf, Finset.mem_filter, Finset.mem_univ, true_and, hsOpt_eval,
          sOptV, vDP, Fin.val_last, decide_eq_true_eq, huC_val]
        have := r.isLt; dsimp only [a] at this; omega
      · intro _ _ _ _ h; exact Fin.ext (congrArg (fun x : Fin (softN G) => x.val) h)
      · intro r hr
        simp only [softSatOf, Finset.mem_filter, Finset.mem_univ, true_and, hsOpt_eval,
          sOptV, vDP, Fin.val_last, decide_eq_true_eq, huC_val] at hr
        exact ⟨⟨r.val, by dsimp only [a]; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  refine ⟨sOpt, ?_, ?_⟩
  · rw [hsp, hbank_full, hhard_full, hsoft_val]; rfl
  · rw [cfg_vr_pin, hsOpt_eval]; rfl

private lemma main_construction (q m n t : Nat) (bank : Fin t → Fin q) (row : Fin t → Fin m)
    (var : Fin t → Fin n) (sign : Fin t → Bool) (D : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (q + 2) D)
    (hout : D.output < q + 2 + D.size) :
    let answers := fun (X : Finset (Fin t)) =>
      @Finset.filter _ (fun k : Fin q => ∃ s : Fin n → Bool, ∀ j : Fin m,
        ∃ i ∈ X, bank i = k ∧ row i = j ∧ s (var i) = sign i)
        (Classical.decPred _) Finset.univ
    let bound := 256 * (q + 2) * (t + q * m + q * n + D.size + (q + 2) ^ 2 + 1)
    ∃ (T M N H : Nat) (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
      (io : Fin t ↪ Fin T) (cr : (Fin q × Fin m) ↪ Fin M) (cv : (Fin q × Fin n) ↪ Fin N)
      (base : Finset (Fin T)) (pin : Fin T),
      T + M + N ≤ bound ∧
      (∀ i, cl (io i) = cr (bank i, row i) ∧ vr (io i) = cv (bank i, var i) ∧ sg (io i) = sign i) ∧
      pin ∉ base ∧ (∀ i, io i ∉ base ∧ io i ≠ pin) ∧ sg pin = true ∧
      (∀ v, cl v = cl pin → v = pin) ∧
      let score := fun (Y : Finset (Fin T)) =>
        (Finset.univ : Finset (Fin N → Bool)).sup (fun s =>
          ((Y.filter (fun i => s (vr i) = sg i)).image cl).card)
      let allowed := @Finset.filter _ (fun i : Fin T =>
        cl i ≠ cl pin ∧ ¬ (vr i = vr pin ∧ sg i ≠ sg pin))
        (Classical.decPred _) Finset.univ
      ∀ X : Finset (Fin t),
        let S := answers X
        let b := D.eval (List.ofFn (fun i : Fin q => decide (i ∈ S)) ++ [false, true])
        let Y := base ∪ X.map io
        let a := (S.card + 1 - b.toNat) / 2
        score Y = H + a ∧ score (insert pin Y) = H + a + b.toNat ∧
          ((∃ U : Finset (Fin T), U ⊆ Y ∧ U ⊆ allowed ∧ score U = score Y) ↔ b = true) := by
  intro answers bound
  let G : Cfg := ⟨q, m, n, t, bank, row, var, sign, D⟩
  refine ⟨numT G, numM G, numV G, Hval G, clF G, vrF G, sgF G, ioOf G, crOf G, cvOf G,
    baseOf G, pinOf G, cfg_size_le G, cfg_io_spec G, cfg_pin_not_base G, cfg_io_props G,
    cfg_sg_pin G, cfg_cl_pin_uniq G, ?_⟩
  intro score allowed X S b Y a
  have hupper := cfg_upper G hfan hrb hout X
  have hex_opt := cfg_opt G hfan hrb hout X
  dsimp only at hupper hex_opt
  change ∀ s, (satSet G Y s).card ≤ Hval G + a ∧
    (b = false → s (vrF G (pinOf G)) = true → (satSet G Y s).card + 1 ≤ Hval G + a) at hupper
  change ∃ sOpt, (satSet G Y sOpt).card = Hval G + a ∧ sOpt (vrF G (pinOf G)) = b at hex_opt
  have hscore_Y : score Y = Hval G + a := by
    apply le_antisymm
    · exact Finset.sup_le fun s _ => (hupper s).1
    · rcases hex_opt with ⟨sOpt, hsc, _⟩
      rw [← hsc]
      exact Finset.le_sup (f := fun s => (satSet G Y s).card) (Finset.mem_univ sOpt)
  have hscore_pin : score (insert (pinOf G) Y) = Hval G + a + b.toNat := by
    apply le_antisymm
    · refine Finset.sup_le fun s _ => ?_
      have hpin := cfg_sat_insert_pin G X s
      dsimp only at hpin
      change (satSet G (insert (pinOf G) Y) s).card = (satSet G Y s).card + (s (vrF G (pinOf G))).toNat at hpin
      change (satSet G (insert (pinOf G) Y) s).card ≤ _
      rw [hpin]
      cases hb : b
      · cases hsp : s (vrF G (pinOf G))
        · have h1 := (hupper s).1; simp only [Bool.toNat_false, add_zero]; exact h1
        · have h2 := (hupper s).2 hb hsp; simpa only [Bool.toNat_true, Bool.toNat_false, add_zero] using h2
      · have h1 := (hupper s).1; cases s (vrF G (pinOf G)) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    · rcases hex_opt with ⟨sOpt, hsc, hpin⟩
      have hpin_eq := cfg_sat_insert_pin G X sOpt
      dsimp only at hpin_eq
      have hval : (satSet G (insert (pinOf G) Y) sOpt).card = Hval G + a + b.toNat := by
        rw [hpin_eq, hsc, hpin]
      rw [← hval]
      exact Finset.le_sup (f := fun s => (satSet G (insert (pinOf G) Y) s).card) (Finset.mem_univ sOpt)
  have hcanon_iff :
      (∃ U : Finset (Fin (numT G)), U ⊆ Y ∧ U ⊆ allowed ∧ score U = score Y) ↔ b = true := by
    constructor
    · rintro ⟨U, hUY, hUall, hscU⟩
      by_contra hnb
      have hbf : b = false := by cases h : b <;> simp_all
      rw [hscore_Y] at hscU
      have hex_s : ∃ s : Fin (numV G) → Bool, (satSet G U s).card = Hval G + a := by
        have hne : (Finset.univ : Finset (Fin (numV G) → Bool)).Nonempty := ⟨fun _ => false, Finset.mem_univ _⟩
        rcases Finset.exists_mem_eq_sup _ hne (fun s => (satSet G U s).card) with ⟨s, _, hs⟩
        exact ⟨s, hs.symm.trans hscU⟩
      rcases hex_s with ⟨s, hs⟩
      let s' : Fin (numV G) → Bool := Function.update s (vrF G (pinOf G)) true
      have hs'_pin : s' (vrF G (pinOf G)) = true := Function.update_self _ _ _
      have hsub_sat : satSet G U s ⊆ satSet G Y s' := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
        rcases Finset.mem_filter.mp hi with ⟨hiU, his⟩
        refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hUY hiU, ?_⟩, rfl⟩
        by_cases hv : vrF G i = vrF G (pinOf G)
        · have hall := hUall hiU
          simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at hall
          have hsgi : sgF G i = true := by
            by_contra hnot
            exact hall.2 ⟨hv, by rw [cfg_sg_pin G]; exact hnot⟩
          rw [hv, hs'_pin, hsgi]
        · dsimp only [s']; rw [Function.update_of_ne hv]; exact his
      have hge : Hval G + a ≤ (satSet G Y s').card := hs ▸ Finset.card_le_card hsub_sat
      have hlt := (hupper s').2 hbf hs'_pin
      omega
    · intro hbt
      refine ⟨Y ∩ allowed, Finset.inter_subset_left, Finset.inter_subset_right, ?_⟩
      apply le_antisymm
      · refine Finset.sup_le fun s _ => ?_
        have hsub : satSet G (Y ∩ allowed) s ⊆ satSet G Y s :=
          Finset.image_subset_image (Finset.filter_subset_filter _ Finset.inter_subset_left)
        exact (Finset.card_le_card hsub).trans (Finset.le_sup (f := fun s => (satSet G Y s).card) (Finset.mem_univ s))
      · rw [hscore_Y]
        rcases hex_opt with ⟨sOpt, hsc, hpin⟩
        have hsub : satSet G Y sOpt ⊆ satSet G (Y ∩ allowed) sOpt := by
          intro c hc
          rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
          rcases Finset.mem_filter.mp hi with ⟨hiY, his⟩
          refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hiY, ?_⟩, his⟩, rfl⟩
          simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · intro hcp
            have hip : i = pinOf G := cfg_cl_pin_uniq G i hcp
            subst hip
            rcases Finset.mem_union.mp hiY with hb | hx
            · exact cfg_pin_not_base G hb
            · rcases Finset.mem_map.mp hx with ⟨j, _, hj⟩; exact (cfg_io_props G j).2 hj
          · rintro ⟨hv, hsne⟩
            rw [hv, hpin, hbt] at his
            rw [cfg_sg_pin G] at hsne
            exact hsne his.symm
        calc
          Hval G + a = (satSet G Y sOpt).card := hsc.symm
          _ ≤ (satSet G (Y ∩ allowed) sOpt).card := Finset.card_le_card hsub
          _ ≤ score (Y ∩ allowed) := Finset.le_sup (f := fun s => (satSet G (Y ∩ allowed) s).card) (Finset.mem_univ sOpt)
  exact ⟨hscore_Y, hscore_pin, hcanon_iff⟩

private def stdScore {T M N : Nat} (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
    (Z : Finset (Fin T)) : Nat :=
  (Finset.univ : Finset (Fin N → Bool)).sup (fun s =>
    ((Z.filter (fun i => s (vr i) = sg i)).image cl).card)

private lemma bridge_eq {T H : Nat}
    {Y1 Y2 Yins1 Yins2 all1 all2 : Finset (Fin T)} {a1 a2 : Nat} {b1 b2 : Bool}
    {sc1 sc2 : Finset (Fin T) → Nat}
    (hY : Y1 = Y2) (hYins : Yins1 = Yins2) (hall : all1 = all2)
    (ha : a1 = a2) (hb : b1 = b2) (hsc : ∀ Z, sc1 Z = sc2 Z)
    (h : sc1 Y1 = H + a1 ∧ sc1 Yins1 = H + a1 + b1.toNat ∧
         ((∃ U : Finset (Fin T), U ⊆ Y1 ∧ U ⊆ all1 ∧ sc1 U = sc1 Y1) ↔ b1 = true)) :
    sc2 Y2 = H + a2 ∧ sc2 Yins2 = H + a2 + b2.toNat ∧
      ((∃ U : Finset (Fin T), U ⊆ Y2 ∧ U ⊆ all2 ∧ sc2 U = sc2 Y2) ↔ b2 = true) := by
  subst hY hYins hall ha hb
  have hsc_eq : sc1 = sc2 := funext hsc
  subst hsc_eq
  exact h

theorem main_proof :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (q m n t : Nat) (bank : Fin t → Fin q) (row : Fin t → Fin m)
      (var : Fin t → Fin n) (sign : Fin t → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.NestedCover.ReadsBack (q+2) D →
      D.output < q+2+D.size →
      let answers := fun (X : Finset (Fin t)) => (Finset.univ : Finset (Fin q)).filter
        (fun k => ∃ s : Fin n → Bool, ∀ j : Fin m,
          ∃ i ∈ X, bank i=k ∧ row i=j ∧ s (var i)=sign i)
      let bound := 256*(q+2)*(t+q*m+q*n+D.size+(q+2)^2+1)
      ∃ (T M N H : Nat) (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
        (io : Fin t ↪ Fin T) (cr : (Fin q × Fin m) ↪ Fin M) (cv : (Fin q × Fin n) ↪ Fin N)
        (base : Finset (Fin T)) (pin : Fin T),
        T+M+N ≤ bound ∧
        (∀ i, cl (io i)=cr (bank i,row i) ∧ vr (io i)=cv (bank i,var i) ∧ sg (io i)=sign i) ∧
        pin ∉ base ∧ (∀ i, io i ∉ base ∧ io i ≠ pin) ∧ sg pin=true ∧
        (∀ v, cl v=cl pin → v=pin) ∧
        let score := fun (Y : Finset (Fin T)) =>
          (Finset.univ : Finset (Fin N → Bool)).sup (fun s =>
            ((Y.filter (fun i => s (vr i)=sg i)).image cl).card)
        let allowed := (Finset.univ : Finset (Fin T)).filter (fun i =>
          cl i ≠ cl pin ∧ ¬(vr i=vr pin ∧ sg i≠sg pin))
        ∀ X : Finset (Fin t),
          let S := answers X
          let b := D.eval (List.ofFn (fun i : Fin q => decide (i∈S)) ++ [false,true])
          let Y := base ∪ X.map io
          let a := (S.card+1-b.toNat)/2
          score Y = H+a ∧ score (insert pin Y) = H+a+b.toNat ∧
            ((∃ U : Finset (Fin T), U ⊆ Y ∧ U ⊆ allowed ∧ score U=score Y) ↔ b=true) := by
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro q m n t bank row var sign D hfan hrb hout answers bound
  rcases main_construction q m n t bank row var sign D hfan hrb hout with
    ⟨T, M, N, H, cl, vr, sg, io, cr, cv, base, pin, hbound, hio, hpin_base, hio_base, hsg_pin, hcl_pin, hX⟩
  refine ⟨T, M, N, H, cl, vr, sg, io, cr, cv, base, pin, hbound, hio, hpin_base, hio_base, hsg_pin, hcl_pin, ?_⟩
  intro score allowed X S b Y a
  have h1 := hX X
  dsimp only at h1
  refine bridge_eq (sc1 := stdScore cl vr sg) (sc2 := score) ?_ ?_ ?_ ?_ ?_ ?_ h1
  · ext v; simp only [Y, Finset.mem_union]
  · ext v; simp only [Y, Finset.mem_insert, Finset.mem_union]
  · ext v; simp only [allowed, Finset.mem_filter]
  · dsimp only [a]
    congr 1; congr 1
    apply congrArg Bool.toNat; congr 2
    apply List.ext_getElem (by simp)
    intro idx _ _; simp only [List.getElem_ofFn]
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, S, answers, Finset.mem_filter]
  · dsimp only [b]
    congr 2; apply List.ext_getElem (by simp)
    intro idx _ _; simp only [List.getElem_ofFn]
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, S, answers, Finset.mem_filter]
  · intro Z; dsimp only [stdScore, score]
    refine Finset.sup_congr (by ext x; simp) fun s _ => ?_
    apply congrArg Finset.card; ext c; simp only [Finset.mem_image, Finset.mem_filter]

end PEqualNP.Outside.L_lib_1257

theorem PEqualNP.Outside.L_lib_1257 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (q m n t : Nat) (bank : Fin t → Fin q) (row : Fin t → Fin m)
  (var : Fin t → Fin n) (sign : Fin t → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.NestedCover.ReadsBack (q+2) D →
  D.output < q+2+D.size →
  let answers := fun (X : Finset (Fin t)) => (Finset.univ : Finset (Fin q)).filter
    (fun k => ∃ s : Fin n → Bool, ∀ j : Fin m,
      ∃ i ∈ X, bank i=k ∧ row i=j ∧ s (var i)=sign i)
  let bound := 256*(q+2)*(t+q*m+q*n+D.size+(q+2)^2+1)
  ∃ (T M N H : Nat) (cl : Fin T → Fin M) (vr : Fin T → Fin N) (sg : Fin T → Bool)
    (io : Fin t ↪ Fin T) (cr : (Fin q × Fin m) ↪ Fin M) (cv : (Fin q × Fin n) ↪ Fin N)
    (base : Finset (Fin T)) (pin : Fin T),
    T+M+N ≤ bound ∧
    (∀ i, cl (io i)=cr (bank i,row i) ∧ vr (io i)=cv (bank i,var i) ∧ sg (io i)=sign i) ∧
    pin ∉ base ∧ (∀ i, io i ∉ base ∧ io i ≠ pin) ∧ sg pin=true ∧
    (∀ v, cl v=cl pin → v=pin) ∧
    let score := fun (Y : Finset (Fin T)) =>
      (Finset.univ : Finset (Fin N → Bool)).sup (fun s =>
        ((Y.filter (fun i => s (vr i)=sg i)).image cl).card)
    let allowed := (Finset.univ : Finset (Fin T)).filter (fun i =>
      cl i ≠ cl pin ∧ ¬(vr i=vr pin ∧ sg i≠sg pin))
    ∀ X : Finset (Fin t),
      let S := answers X
      let b := D.eval (List.ofFn (fun i : Fin q => decide (i∈S)) ++ [false,true])
      let Y := base ∪ X.map io
      let a := (S.card+1-b.toNat)/2
      score Y = H+a ∧ score (insert pin Y) = H+a+b.toNat ∧
        ((∃ U : Finset (Fin T), U ⊆ Y ∧ U ⊆ allowed ∧ score U=score Y) ↔ b=true) :=
  PEqualNP.Outside.L_lib_1257.main_proof
