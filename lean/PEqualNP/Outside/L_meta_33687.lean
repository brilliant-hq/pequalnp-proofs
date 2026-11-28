import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33687_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- Part 1: Wires evaluation, FanInTwo, notCount helpers

def evalWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init

theorem evalWires_nil (init : List Bool) : evalWires [] init = init := rfl

theorem evalWires_cons (g : Gate) (gs : List Gate) (init : List Bool) :
    evalWires (g :: gs) init =
      evalWires gs (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]) := rfl

theorem evalWires_append (gs1 gs2 : List Gate) (init : List Bool) :
    evalWires (gs1 ++ gs2) init = evalWires gs2 (evalWires gs1 init) :=
  List.foldl_append

theorem evalWires_length (gs : List Gate) (init : List Bool) :
    (evalWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [evalWires]
  | cons g gs ih =>
    rw [evalWires_cons, ih]
    simp [List.length_append]
    omega

theorem getD_append_lt {α : Type*} (xs ys : List α) (d : α) {i : ℕ} (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right {α : Type*} (xs ys : List α) (d : α) {i : ℕ} (hi : xs.length ≤ i) :
    (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem getD_ofFn_lt {k : ℕ} (x : Fin k → Bool) {i : ℕ} (hi : i < k) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_ofFn_ge {k : ℕ} (x : Fin k → Bool) {i : ℕ} (hi : k ≤ i) :
    (List.ofFn x).getD i false = false := by
  rw [List.getD_eq_default]
  simp [hi]

theorem evalWires_prefix_getD (gs : List Gate) (init : List Bool) {i : ℕ} (hi : i < init.length) :
    (evalWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [evalWires_cons, ih _ (by simp; omega)]
    exact getD_append_lt init _ false hi

theorem evalWires_ge_false (gs : List Gate) (init : List Bool) {i : ℕ}
    (hi : init.length + gs.length ≤ i) :
    (evalWires gs init).getD i false = false := by
  rw [List.getD_eq_default]
  rw [evalWires_length]
  exact hi

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem notCount_eq (C : Circuit) :
    notCount C = (C.gates.filter fun g => isNotOp g.op).length := by
  unfold notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases h : g.op <;> simp [h, isNotOp]

theorem filter_not_append (gs1 gs2 : List Gate) :
    ((gs1 ++ gs2).filter fun g => isNotOp g.op).length =
      (gs1.filter fun g => isNotOp g.op).length + (gs2.filter fun g => isNotOp g.op).length := by
  simp [List.filter_append, List.length_append]

theorem filter_length_cons {α : Type*} (p : α → Bool) (x : α) (xs : List α) :
    ((x :: xs).filter p).length = (if p x then 1 else 0) + (xs.filter p).length := by
  by_cases h : p x <;> simp [List.filter_cons, h, Nat.add_comm]

theorem filter_map_isNotOp (f : Gate → Gate) (hf : ∀ g, isNotOp (f g).op = isNotOp g.op) :
    ∀ gs : List Gate, ((gs.map f).filter fun g => isNotOp g.op).length =
      (gs.filter fun g => isNotOp g.op).length := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change ((f g :: gs.map f).filter fun x => isNotOp x.op).length =
      ((g :: gs).filter fun x => isNotOp x.op).length
    rw [filter_length_cons, filter_length_cons, hf g, ih]

def fitsPred (q b k : Nat) (T : Fin q → (Fin k → Bool) → Bool) (s : Nat) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → Nat),
    FanInTwo C ∧ C.size ≤ s ∧ notCount C ≤ b ∧
    ∀ j x, (C.wires (List.ofFn x)).getD (tap j) false = T j x

-- Part 2: Relabeling inputs

def relabelWire (n1 n2 : ℕ) (e : Fin n1 → Fin n2) (w : ℕ) : ℕ :=
  if h : w < n1 then (e ⟨w, h⟩).val else n2 + (w - n1)

def relabelGate (n1 n2 : ℕ) (e : Fin n1 → Fin n2) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (relabelWire n1 n2 e)⟩

theorem relabelWire_ge {n1 n2 : ℕ} (e : Fin n1 → Fin n2) {w : ℕ} (hw : n1 ≤ w) :
    relabelWire n1 n2 e w = n2 + (w - n1) := by
  unfold relabelWire; rw [dif_neg (by omega)]

theorem relabelWire_lt_of_lt {n1 n2 : ℕ} (e : Fin n1 → Fin n2) {k t : ℕ} (ht : t < n1 + k) :
    relabelWire n1 n2 e t < n2 + k := by
  unfold relabelWire
  by_cases h : t < n1
  · rw [dif_pos h]; have := (e ⟨t, h⟩).isLt; omega
  · rw [dif_neg h]; omega

theorem evalWires_relabel {n1 n2 : ℕ} (e : Fin n1 → Fin n2)
    (gs : List Gate) (y2 : Fin n2 → Bool) :
    ∀ t : ℕ,
      (evalWires (gs.map (relabelGate n1 n2 e)) (List.ofFn y2)).getD (relabelWire n1 n2 e t) false =
        (evalWires gs (List.ofFn (y2 ∘ e))).getD t false := by
  have hmain : ∀ (gs : List Gate) (w1 w2 : List Bool) (k : ℕ),
      w1.length = n1 + k → w2.length = n2 + k →
      (∀ t, w2.getD (relabelWire n1 n2 e t) false = w1.getD t false) →
      ∀ t, (evalWires (gs.map (relabelGate n1 n2 e)) w2).getD (relabelWire n1 n2 e t) false =
        (evalWires gs w1).getD t false := by
    intro gs
    induction gs with
    | nil =>
      intro w1 w2 k _ _ hinv t
      exact hinv t
    | cons g gs ih =>
      intro w1 w2 k hw1 hw2 hinv t
      simp only [List.map_cons, evalWires_cons]
      have harg : g.inputs.map (fun i => w2.getD (relabelWire n1 n2 e i) false) =
          g.inputs.map (fun i => w1.getD i false) := by
        apply List.map_congr_left
        intro i _; exact hinv i
      have hbit : (relabelGate n1 n2 e g).op.eval
            ((relabelGate n1 n2 e g).inputs.map fun i => w2.getD i false) =
          g.op.eval (g.inputs.map fun i => w1.getD i false) := by
        change g.op.eval ((g.inputs.map (relabelWire n1 n2 e)).map fun i => w2.getD i false) = _
        rw [List.map_map]
        exact congrArg g.op.eval harg
      rw [hbit]
      refine ih (w1 ++ [_]) (w2 ++ [_]) (k + 1) (by simp [hw1]; omega) (by simp [hw2]; omega) ?_ t
      intro u
      by_cases hu : u < n1 + k
      · have hr := relabelWire_lt_of_lt e hu
        rw [getD_append_lt w2 _ false (by omega), getD_append_lt w1 _ false (by omega)]
        exact hinv u
      · by_cases hue : u = n1 + k
        · subst hue
          have hge : n1 ≤ n1 + k := by omega
          rw [relabelWire_ge e hge, getD_append_right w2 _ false (by omega), getD_append_right w1 _ false (by omega)]
          simp [hw1, hw2]
        · have hge : n1 ≤ u := by omega
          rw [relabelWire_ge e hge]
          rw [List.getD_eq_default _ false (by simp [hw2]; omega), List.getD_eq_default _ false (by simp [hw1]; omega)]
  refine hmain gs (List.ofFn (y2 ∘ e)) (List.ofFn y2) 0 (by simp) (by simp) ?_
  intro t
  unfold relabelWire
  by_cases ht : t < n1
  · rw [dif_pos ht, getD_ofFn_lt _ ht, getD_ofFn_lt _ (e ⟨t, ht⟩).isLt]; rfl
  · rw [dif_neg ht, getD_ofFn_ge _ (by omega), getD_ofFn_ge _ (by omega)]

theorem relabel_fits {n1 n2 q b s : ℕ} {T1 : Fin q → (Fin n1 → Bool) → Bool}
    (e : Fin n1 → Fin n2) (h : fitsPred q b n1 T1 s) :
    ∀ (T2 : Fin q → (Fin n2 → Bool) → Bool),
      (∀ j y2, T2 j y2 = T1 j (y2 ∘ e)) → fitsPred q b n2 T2 s := by
  intro T2 hT2
  obtain ⟨C, tap, hFan, hSz, hNot, hEval⟩ := h
  refine ⟨⟨C.gates.map (relabelGate n1 n2 e), 0⟩, fun j => relabelWire n1 n2 e (tap j), ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hFan g0 hg0).1, by simp [relabelGate, (hFan g0 hg0).2]⟩
  · simpa [Circuit.size] using hSz
  · rw [notCount_eq] at hNot ⊢
    rwa [filter_map_isNotOp (relabelGate n1 n2 e) (fun _ => rfl) C.gates]
  · intro j y2
    change (evalWires (C.gates.map (relabelGate n1 n2 e)) (List.ofFn y2)).getD (relabelWire n1 n2 e (tap j)) false = T2 j y2
    have he := hEval j (y2 ∘ e)
    change (evalWires C.gates (List.ofFn (y2 ∘ e))).getD (tap j) false = _ at he
    rw [evalWires_relabel, he, hT2]

-- Part 3: Forward direction (Block-OR tree)

def orFold (nextW w0 : ℕ) : List ℕ → ℕ × List Gate
  | [] => (w0, [])
  | w1 :: ws =>
    let res := orFold (nextW + 1) nextW ws
    (res.1, ⟨GateOp.or, [w0, w1]⟩ :: res.2)

theorem orFold_length (nextW w0 : ℕ) (ws : List ℕ) :
    (orFold nextW w0 ws).2.length = ws.length := by
  induction ws generalizing nextW w0 with
  | nil => rfl
  | cons w1 ws ih => simp [orFold, ih]

theorem orFold_fanIn (nextW w0 : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orFold nextW w0 ws).2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing nextW w0 with
  | nil => intro g hg; cases hg
  | cons w1 ws ih =>
    intro g hg
    dsimp only [orFold] at hg
    rcases List.mem_cons.mp hg with rfl | hg2
    · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · exact ih (nextW + 1) nextW g hg2

theorem orFold_noNot (nextW w0 : ℕ) (ws : List ℕ) :
    ((orFold nextW w0 ws).2.filter fun g => isNotOp g.op).length = 0 := by
  induction ws generalizing nextW w0 with
  | nil => rfl
  | cons w1 ws ih =>
    change ((⟨GateOp.or, [w0, w1]⟩ :: (orFold (nextW + 1) nextW ws).2).filter fun g => isNotOp g.op).length = 0
    rw [filter_length_cons, ih]
    rfl

theorem orFold_out_lt (nextW w0 : ℕ) (ws : List ℕ) (hw0 : w0 < nextW) :
    (orFold nextW w0 ws).1 < nextW + ws.length := by
  induction ws generalizing nextW w0 with
  | nil => simpa [orFold] using hw0
  | cons w1 ws ih =>
    have hlt := ih (nextW + 1) nextW (by omega)
    change (orFold (nextW + 1) nextW ws).1 < nextW + (ws.length + 1)
    omega

theorem orFold_eval (nextW w0 : ℕ) (ws : List ℕ) (pref : List Bool)
    (hp : pref.length = nextW) (hw0 : w0 < nextW) (hws : ∀ w ∈ ws, w < nextW) :
    (evalWires (orFold nextW w0 ws).2 pref).getD (orFold nextW w0 ws).1 false =
      (pref.getD w0 false || ws.any fun w => pref.getD w false) := by
  induction ws generalizing nextW w0 pref with
  | nil => simp [orFold, evalWires]
  | cons w1 ws ih =>
    have h1 : w1 < nextW := hws w1 (by simp)
    have hrest : ∀ w ∈ ws, w < nextW + 1 := fun w hw => Nat.lt_trans (hws w (by simp [hw])) (by omega)
    have hbit : GateOp.eval GateOp.or (List.map (fun i => pref.getD i false) [w0, w1]) =
        (pref.getD w0 false || pref.getD w1 false) := by simp [GateOp.eval]
    have hsub := ih (nextW + 1) nextW (pref ++ [pref.getD w0 false || pref.getD w1 false])
      (by simp [hp]) (by omega) hrest
    change (evalWires (⟨GateOp.or, [w0, w1]⟩ :: (orFold (nextW + 1) nextW ws).2) pref).getD (orFold (nextW + 1) nextW ws).1 false = _
    rw [evalWires_cons, hbit, hsub, getD_append_right pref _ false (hp ▸ Nat.le_refl nextW)]
    simp only [hp, Nat.sub_self, List.getD_cons_zero, List.any_cons]
    have hany : (ws.any fun w => (pref ++ [pref.getD w0 false || pref.getD w1 false]).getD w false) =
        (ws.any fun w => pref.getD w false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨w, hw, htw⟩
        exact ⟨w, hw, by rwa [getD_append_lt pref _ false (hp ▸ hws w (by simp [hw]))] at htw⟩
      · rintro ⟨w, hw, htw⟩
        exact ⟨w, hw, by rwa [getD_append_lt pref _ false (hp ▸ hws w (by simp [hw]))]⟩
    rw [hany, Bool.or_assoc]

def fiberList {n m : ℕ} (π : Fin m → Fin n) (i : Fin n) : List (Fin m) :=
  (List.finRange m).filter fun u => decide (π u = i)

theorem fiberList_nonempty {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π) (i : Fin n) :
    0 < (fiberList π i).length := by
  obtain ⟨u, hu⟩ := hπ i
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_finRange u, decide_eq_true hu⟩)

def blockOR {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (i : Fin n) : ℕ × List Gate :=
  match ((fiberList π i).map Fin.val) with
  | [] => (0, [])
  | w0 :: rest => orFold nextW w0 rest

theorem blockOR_length {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (i : Fin n) :
    (blockOR π nextW i).2.length + 1 = (fiberList π i).length := by
  unfold blockOR
  have hlen : 0 < ((fiberList π i).map Fin.val).length := by
    simpa using fiberList_nonempty π hπ i
  cases h : (fiberList π i).map Fin.val with
  | nil => simp [h] at hlen
  | cons w0 rest =>
    dsimp only
    rw [orFold_length]
    have hml : ((fiberList π i).map Fin.val).length = (fiberList π i).length := List.length_map (f := Fin.val)
    rw [← hml, h]; simp

theorem blockOR_fanIn {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (i : Fin n) :
    ∀ g ∈ (blockOR π nextW i).2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  unfold blockOR
  cases h : (fiberList π i).map Fin.val with
  | nil => intro g hg; cases hg
  | cons w0 rest => exact orFold_fanIn nextW w0 rest

theorem blockOR_noNot {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (i : Fin n) :
    ((blockOR π nextW i).2.filter fun g => isNotOp g.op).length = 0 := by
  unfold blockOR
  cases h : (fiberList π i).map Fin.val with
  | nil => rfl
  | cons w0 rest => exact orFold_noNot nextW w0 rest

theorem blockOR_out_lt {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (hm : m ≤ nextW) (i : Fin n) :
    (blockOR π nextW i).1 < nextW + (blockOR π nextW i).2.length := by
  unfold blockOR
  have hne := fiberList_nonempty π hπ i
  cases h : (fiberList π i).map Fin.val with
  | nil =>
    have h0 : ((fiberList π i).map Fin.val).length = 0 := by rw [h]; rfl
    rw [List.length_map] at h0; omega
  | cons w0 rest =>
    have hw0_mem : w0 ∈ (fiberList π i).map Fin.val := by rw [h]; exact List.mem_cons_self
    obtain ⟨u0, _, hu0⟩ := List.mem_map.mp hw0_mem
    have hw0_lt : w0 < nextW := by have := u0.isLt; omega
    dsimp only
    rw [orFold_length]
    exact orFold_out_lt nextW w0 rest hw0_lt

theorem blockOR_eval {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (i : Fin n) (y : Fin m → Bool) (pref : List Bool)
    (hp : pref.length = nextW) (hm : m ≤ nextW)
    (hpref : ∀ u : Fin m, pref.getD u.val false = y u) :
    (evalWires (blockOR π nextW i).2 pref).getD (blockOR π nextW i).1 false =
      decide (∃ u : Fin m, π u = i ∧ y u = true) := by
  unfold blockOR
  have hne := fiberList_nonempty π hπ i
  cases h : (fiberList π i).map Fin.val with
  | nil =>
    have h0 : ((fiberList π i).map Fin.val).length = 0 := by rw [h]; rfl
    rw [List.length_map] at h0; omega
  | cons w0 rest =>
    have hw_lt : ∀ w ∈ (fiberList π i).map Fin.val, w < nextW := by
      intro w hw
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
      have := u.isLt; omega
    have hw0_lt : w0 < nextW := hw_lt w0 (by rw [h]; simp)
    have hrest_lt : ∀ w ∈ rest, w < nextW := fun w hw => hw_lt w (by rw [h]; simp [hw])
    have hev := orFold_eval nextW w0 rest pref hp hw0_lt hrest_lt
    dsimp only
    rw [hev]
    have h1 : (pref.getD w0 false || rest.any fun w => pref.getD w false) =
        (((fiberList π i).map Fin.val).any fun w => pref.getD w false) := by
      rw [h]; rfl
    rw [h1, List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Function.comp_apply, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, htu⟩
      have hu' := List.mem_filter.mp hu
      exact ⟨u, decide_eq_true_eq.mp hu'.2, by rw [← hpref u]; exact htu⟩
    · rintro ⟨u, hpi, hyu⟩
      refine ⟨u, List.mem_filter.mpr ⟨List.mem_finRange u, decide_eq_true hpi⟩, ?_⟩
      rw [hpref u]; exact hyu

def buildBlocksAux {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (rep : Fin n → ℕ) :
    List (Fin n) → (Fin n → ℕ) × List Gate
  | [] => (rep, [])
  | i :: rest =>
    let blk := blockOR π nextW i
    let sub := buildBlocksAux π (nextW + blk.2.length) (fun k => if k = i then blk.1 else rep k) rest
    (sub.1, blk.2 ++ sub.2)

theorem sum_map_add_indicator {α : Type*} [DecidableEq α] (a : α) (f : α → ℕ) :
    ∀ ks : List α, ks.Nodup →
      (ks.map fun i => (if a = i then 1 else 0) + f i).sum =
        (if a ∈ ks then 1 else 0) + (ks.map f).sum := by
  intro ks hk
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [List.nodup_cons] at hk
    simp only [List.map_cons, List.sum_cons, ih hk.2]
    by_cases hka : a = k
    · subst hka; simp [hk.1]; omega
    · have hmem : (a ∈ k :: ks) ↔ (a ∈ ks) := by simp [hka]
      simp [hka, hmem]; omega

theorem sum_fiberList {n m : ℕ} (π : Fin m → Fin n) :
    ∀ (l : List (Fin m)), ((List.finRange n).map fun i => (l.filter fun u => decide (π u = i)).length).sum = l.length := by
  intro l
  induction l with
  | nil =>
    simp only [List.filter_nil, List.length_nil]
    clear π
    induction (List.finRange n) with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  | cons u l ih =>
    rw [List.length_cons]
    have hcongr : (List.finRange n).map (fun i => ((u :: l).filter fun x => decide (π x = i)).length) =
        (List.finRange n).map (fun i => (if π u = i then 1 else 0) + (l.filter fun x => decide (π x = i)).length) := by
      apply List.map_congr_left
      intro i _
      rw [filter_length_cons]
      by_cases heq : π u = i <;> simp [heq]
    rw [hcongr, sum_map_add_indicator (π u) _ (List.finRange n) (List.nodup_finRange n)]
    simp [List.mem_finRange, ih]
    omega

theorem buildBlocksAux_length {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (rep : Fin n → ℕ) (ks : List (Fin n)) :
    (buildBlocksAux π nextW rep ks).2.length + ks.length =
      (ks.map fun i => (fiberList π i).length).sum := by
  induction ks generalizing nextW rep with
  | nil => simp [buildBlocksAux]
  | cons i rest ih =>
    dsimp only [buildBlocksAux]
    have hblk := blockOR_length π hπ nextW i
    have hsub := ih (nextW + (blockOR π nextW i).2.length) (fun k => if k = i then (blockOR π nextW i).1 else rep k)
    rw [List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem buildBlocksAux_fanIn {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (rep : Fin n → ℕ)
    (ks : List (Fin n)) :
    ∀ g ∈ (buildBlocksAux π nextW rep ks).2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ks generalizing nextW rep with
  | nil => intro g hg; cases hg
  | cons i rest ih =>
    intro g hg
    dsimp only [buildBlocksAux] at hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact blockOR_fanIn π nextW i g hg1
    · exact ih _ _ g hg2

theorem buildBlocksAux_noNot {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (rep : Fin n → ℕ)
    (ks : List (Fin n)) :
    ((buildBlocksAux π nextW rep ks).2.filter fun g => isNotOp g.op).length = 0 := by
  induction ks generalizing nextW rep with
  | nil => rfl
  | cons i rest ih =>
    dsimp only [buildBlocksAux]
    rw [filter_not_append, blockOR_noNot, ih]

theorem buildBlocksAux_rep_not_mem {n m : ℕ} (π : Fin m → Fin n) (nextW : ℕ) (rep : Fin n → ℕ)
    (ks : List (Fin n)) {k : Fin n} (hk : k ∉ ks) :
    (buildBlocksAux π nextW rep ks).1 k = rep k := by
  induction ks generalizing nextW rep with
  | nil => rfl
  | cons i rest ih =>
    dsimp only [buildBlocksAux]
    have hki : k ≠ i := fun h => hk (h ▸ List.mem_cons_self)
    have hkr : k ∉ rest := fun h => hk (List.mem_cons_of_mem i h)
    rw [ih _ _ hkr]
    simp [hki]

theorem buildBlocksAux_rep_lt {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (hm : m ≤ nextW) (rep : Fin n → ℕ) (ks : List (Fin n)) (hnd : ks.Nodup) :
    ∀ k ∈ ks, (buildBlocksAux π nextW rep ks).1 k < nextW + (buildBlocksAux π nextW rep ks).2.length := by
  induction ks generalizing nextW rep with
  | nil => intro k hk; cases hk
  | cons i rest ih =>
    rw [List.nodup_cons] at hnd
    intro k hk
    dsimp only [buildBlocksAux]
    rw [List.length_append]
    rcases List.mem_cons.mp hk with rfl | hkr
    · rw [buildBlocksAux_rep_not_mem _ _ _ _ hnd.1]
      simp only [ite_true]
      have hlt := blockOR_out_lt π hπ nextW hm k
      omega
    · have hsub := ih (nextW + (blockOR π nextW i).2.length) (by omega)
        (fun r => if r = i then (blockOR π nextW i).1 else rep r) hnd.2 k hkr
      omega

theorem buildBlocksAux_eval {n m : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (nextW : ℕ) (rep : Fin n → ℕ) (ks : List (Fin n)) (hnd : ks.Nodup)
    (y : Fin m → Bool) (pref : List Bool)
    (hp : pref.length = nextW) (hm : m ≤ nextW)
    (hpref : ∀ u : Fin m, pref.getD u.val false = y u) :
    ∀ k ∈ ks,
      (evalWires (buildBlocksAux π nextW rep ks).2 pref).getD ((buildBlocksAux π nextW rep ks).1 k) false =
        decide (∃ u : Fin m, π u = k ∧ y u = true) := by
  induction ks generalizing nextW rep pref with
  | nil => intro k hk; cases hk
  | cons i rest ih =>
    rw [List.nodup_cons] at hnd
    intro k hk
    dsimp only [buildBlocksAux]
    rw [evalWires_append]
    set blk := blockOR π nextW i
    set pref1 := evalWires blk.2 pref
    have hp1 : pref1.length = nextW + blk.2.length := by
      simp [pref1, evalWires_length, hp]
    have hpref1 : ∀ u : Fin m, pref1.getD u.val false = y u := by
      intro u
      have hu : u.val < pref.length := by have := u.isLt; omega
      rw [evalWires_prefix_getD _ _ hu, hpref u]
    rcases List.mem_cons.mp hk with rfl | hkr
    · rw [buildBlocksAux_rep_not_mem _ _ _ _ hnd.1]
      simp only [ite_true]
      have hlt : blk.1 < pref1.length := by
        rw [hp1]
        exact blockOR_out_lt π hπ nextW hm k
      rw [evalWires_prefix_getD _ _ hlt]
      exact blockOR_eval π hπ nextW k y pref hp hm hpref
    · exact ih (nextW + blk.2.length) (fun r => if r = i then blk.1 else rep r) hnd.2
        pref1 hp1 (by omega) hpref1 k hkr

def mapWire (n W : ℕ) (rep : Fin n → ℕ) (w : ℕ) : ℕ :=
  if h : w < n then rep ⟨w, h⟩ else W + (w - n)

def mapGate (n W : ℕ) (rep : Fin n → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire n W rep)⟩

theorem mapWire_ge {n W : ℕ} (rep : Fin n → ℕ) {w : ℕ} (hw : n ≤ w) :
    mapWire n W rep w = W + (w - n) := by
  unfold mapWire; rw [dif_neg (by omega)]

theorem mapWire_lt_of_lt {n W : ℕ} (rep : Fin n → ℕ) (hrep : ∀ i : Fin n, rep i < W)
    {k t : ℕ} (ht : t < n + k) :
    mapWire n W rep t < W + k := by
  unfold mapWire
  by_cases h : t < n
  · rw [dif_pos h]; have := hrep ⟨t, h⟩; omega
  · rw [dif_neg h]; omega

theorem evalWires_mapWire {n W : ℕ} (rep : Fin n → ℕ) (hrep : ∀ i : Fin n, rep i < W)
    (gs : List Gate) (w1 w2 : List Bool) (k : ℕ)
    (hw1 : w1.length = n + k) (hw2 : w2.length = W + k)
    (hinv : ∀ t, w2.getD (mapWire n W rep t) false = w1.getD t false) :
    ∀ t, (evalWires (gs.map (mapGate n W rep)) w2).getD (mapWire n W rep t) false =
      (evalWires gs w1).getD t false := by
  induction gs generalizing w1 w2 k with
  | nil =>
    intro t; exact hinv t
  | cons g gs ih =>
    intro t
    simp only [List.map_cons, evalWires_cons]
    have harg : g.inputs.map (fun i => w2.getD (mapWire n W rep i) false) =
        g.inputs.map (fun i => w1.getD i false) := by
      apply List.map_congr_left
      intro i _; exact hinv i
    have hbit : (mapGate n W rep g).op.eval ((mapGate n W rep g).inputs.map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      change g.op.eval ((g.inputs.map (mapWire n W rep)).map fun i => w2.getD i false) = _
      rw [List.map_map]
      exact congrArg g.op.eval harg
    rw [hbit]
    refine ih (w1 ++ [_]) (w2 ++ [_]) (k + 1) (by simp [hw1]; omega) (by simp [hw2]; omega) ?_ t
    intro u
    by_cases hu : u < n + k
    · have hr := mapWire_lt_of_lt rep hrep hu
      rw [getD_append_lt w2 _ false (by omega), getD_append_lt w1 _ false (by omega)]
      exact hinv u
    · by_cases hue : u = n + k
      · subst hue
        have hge : n ≤ n + k := by omega
        rw [mapWire_ge rep hge, getD_append_right w2 _ false (by omega), getD_append_right w1 _ false (by omega)]
        simp [hw1, hw2]
      · have hge : n ≤ u := by omega
        rw [mapWire_ge rep hge]
        rw [List.getD_eq_default _ false (by simp [hw2]; omega), List.getD_eq_default _ false (by simp [hw1]; omega)]

theorem forward_fits {n m q b s : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
    (F : Fin q → (Fin n → Bool) → Bool)
    (h : fitsPred q b n F s) :
    fitsPred q b m (fun j y => F j fun i => decide (∃ u, π u = i ∧ y u = true)) (s + (m - n)) := by
  obtain ⟨C, tap, hFan, hSz, hNot, hEval⟩ := h
  set res := buildBlocksAux π m (fun _ => 0) (List.finRange n)
  set rep := res.1
  set bGs := res.2
  have hbLen : bGs.length + n = m := by
    have hlen := buildBlocksAux_length π hπ m (fun _ => 0) (List.finRange n)
    have hsum : ((List.finRange n).map fun i => (fiberList π i).length).sum = m := by
      have hsf := sum_fiberList π (List.finRange m)
      simpa [fiberList, List.length_finRange] using hsf
    change bGs.length + (List.finRange n).length = ((List.finRange n).map fun i => (fiberList π i).length).sum at hlen
    rw [List.length_finRange, hsum] at hlen
    exact hlen
  set W := m + bGs.length
  have hrep_lt : ∀ i : Fin n, rep i < W := by
    intro i
    exact buildBlocksAux_rep_lt π hπ m (Nat.le_refl m) (fun _ => 0) (List.finRange n)
      (List.nodup_finRange n) i (List.mem_finRange i)
  refine ⟨⟨bGs ++ C.gates.map (mapGate n W rep), 0⟩, fun j => mapWire n W rep (tap j), ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact buildBlocksAux_fanIn π m (fun _ => 0) (List.finRange n) g hg1
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg2
      exact ⟨(hFan g0 hg0).1, by simp [mapGate, (hFan g0 hg0).2]⟩
  · simp only [Circuit.size, List.length_append, List.length_map]
    simp only [Circuit.size] at hSz
    omega
  · rw [notCount_eq] at hNot ⊢
    rw [filter_not_append, buildBlocksAux_noNot, Nat.zero_add,
      filter_map_isNotOp (mapGate n W rep) (fun _ => rfl) C.gates]
    exact hNot
  · intro j y
    change (evalWires (bGs ++ C.gates.map (mapGate n W rep)) (List.ofFn y)).getD (mapWire n W rep (tap j)) false = _
    rw [evalWires_append]
    set w2 := evalWires bGs (List.ofFn y)
    have hw2_len : w2.length = W + 0 := by simp [w2, evalWires_length, W]
    have hw2_eval : ∀ i : Fin n, w2.getD (rep i) false = decide (∃ u : Fin m, π u = i ∧ y u = true) := by
      intro i
      exact buildBlocksAux_eval π hπ m (fun _ => 0) (List.finRange n) (List.nodup_finRange n)
        y (List.ofFn y) (by simp) (Nat.le_refl m) (fun u => getD_ofFn_lt y u.isLt) i (List.mem_finRange i)
    set x_exp : Fin n → Bool := fun i => decide (∃ u : Fin m, π u = i ∧ y u = true)
    have hinv : ∀ t, w2.getD (mapWire n W rep t) false = (List.ofFn x_exp).getD t false := by
      intro t
      unfold mapWire
      by_cases ht : t < n
      · rw [dif_pos ht, getD_ofFn_lt _ ht]
        exact hw2_eval ⟨t, ht⟩
      · rw [dif_neg ht, getD_ofFn_ge _ (by omega)]
        rw [List.getD_eq_default _ false (by rw [hw2_len]; omega)]
    have he := hEval j x_exp
    change (evalWires C.gates (List.ofFn x_exp)).getD (tap j) false = _ at he
    rw [evalWires_mapWire rep hrep_lt C.gates (List.ofFn x_exp) w2 0 (by simp) hw2_len hinv (tap j), he]

-- Part 4: Backward reduction (single-step elimination and induction)

def swapFin {k : ℕ} (a b x : Fin k) : Fin k :=
  if x = a then b else if x = b then a else x

theorem swapFin_invol {k : ℕ} (a b x : Fin k) : swapFin a b (swapFin a b x) = x := by
  unfold swapFin
  by_cases ha : x = a
  · by_cases hab : a = b <;> simp [ha, hab]
  · by_cases hb : x = b
    · simp [ha, hb, eq_comm]
    · simp [ha, hb]

theorem swapFin_right {k : ℕ} (a b : Fin k) : swapFin a b b = a := by
  unfold swapFin
  by_cases h : b = a <;> simp [h]

def snocBool {m : ℕ} (y' : Fin m → Bool) (c : Bool) (u : Fin (m + 1)) : Bool :=
  if h : u.val < m then y' ⟨u.val, h⟩ else c

theorem list_ofFn_snocBool {m : ℕ} (y' : Fin m → Bool) (c : Bool) :
    List.ofFn (snocBool y' c) = List.ofFn y' ++ [c] := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_ofFn] at hi1
    by_cases hm : i < m
    · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hm]), List.getElem_ofFn]
      simp [snocBool, hm]
    · have him : i = m := by omega
      subst him
      rw [List.getElem_ofFn, List.getElem_append_right (by simp)]
      simp [snocBool]

def effReads (m : ℕ) (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (m ∈ g.inputs)
  | GateOp.or => decide (m ∈ g.inputs)
  | GateOp.not => match g.inputs with
    | a :: _ => decide (a = m)
    | [] => false
  | _ => false

theorem gate_indep_of_not_effReads {m : ℕ} (g : Gate)
    (hFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (heff : effReads m g = false)
    (w1 w2 : List Bool) (hagree : ∀ t, t ≠ m → w1.getD t false = w2.getD t false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  cases h : g.op with
  | and =>
    have hm : m ∉ g.inputs := by
      simpa [effReads, h] using heff
    have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (fun heq => hm (heq ▸ hi))
    rw [hmap]
  | or =>
    have hm : m ∉ g.inputs := by
      simpa [effReads, h] using heff
    have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (fun heq => hm (heq ▸ hi))
    rw [hmap]
  | not =>
    cases hin : g.inputs with
    | nil => simp [GateOp.eval]
    | cons a rest =>
      have ham : a ≠ m := by
        simpa [effReads, h, hin] using heff
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      rw [hagree a ham]
  | _ =>
    simp [h] at hFan

theorem evalWires_indep_of_not_effReads {m : ℕ} (gs : List Gate)
    (hFan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (heff : ∀ g ∈ gs, effReads m g = false) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length → m < w1.length →
      (∀ t, t ≠ m → w1.getD t false = w2.getD t false) →
      ∀ t, t ≠ m → (evalWires gs w1).getD t false = (evalWires gs w2).getD t false := by
  induction gs with
  | nil =>
    intro w1 w2 _ _ hagree t ht
    exact hagree t ht
  | cons g gs ih =>
    intro w1 w2 hlen hm hagree t ht
    simp only [evalWires_cons]
    have hgFan := (hFan g List.mem_cons_self).1
    have hgeff := heff g List.mem_cons_self
    have hbit := gate_indep_of_not_effReads g hgFan hgeff w1 w2 hagree
    rw [hbit]
    refine ih (fun x hx => hFan x (List.mem_cons_of_mem g hx))
      (fun x hx => heff x (List.mem_cons_of_mem g hx))
      (w1 ++ [_]) (w2 ++ [_]) (by simp [hlen]) (by simp; omega) ?_ t ht
    intro u hu
    by_cases hul : u < w1.length
    · rw [getD_append_lt w1 _ false hul, getD_append_lt w2 _ false (by omega)]
      exact hagree u hu
    · by_cases hue : u = w1.length
      · subst hue
        rw [getD_append_right w1 _ false (le_refl _), getD_append_right w2 _ false (by omega)]
        simp [hlen]
      · rw [List.getD_eq_default _ false (by simp; omega), List.getD_eq_default _ false (by simp; omega)]

inductive WireRef
  | const (b : Bool)
  | wire (w : ℕ)

def evalRef (w : List Bool) : WireRef → Bool
  | .const b => b
  | .wire i => w.getD i false

def getRef (env : List WireRef) (t : ℕ) : WireRef :=
  env.getD t (.const false)

def refWf (bound : ℕ) : WireRef → Prop
  | .const _ => True
  | .wire i => i < bound

def evalNotRef (r : WireRef) (nextW : ℕ) : WireRef × List Gate :=
  match r with
  | .const b => (.const (!b), [])
  | .wire i => (.wire nextW, [⟨GateOp.not, [i]⟩])

def evalAndRef (r1 r2 : WireRef) (nextW : ℕ) : WireRef × List Gate :=
  match r1, r2 with
  | .const false, _ => (.const false, [])
  | _, .const false => (.const false, [])
  | .const true, r => (r, [])
  | r, .const true => (r, [])
  | .wire i, .wire j => (.wire nextW, [⟨GateOp.and, [i, j]⟩])

def evalOrRef (r1 r2 : WireRef) (nextW : ℕ) : WireRef × List Gate :=
  match r1, r2 with
  | .const true, _ => (.const true, [])
  | _, .const true => (.const true, [])
  | .const false, r => (r, [])
  | r, .const false => (r, [])
  | .wire i, .wire j => (.wire nextW, [⟨GateOp.or, [i, j]⟩])

def stepShrink (env : List WireRef) (nextW : ℕ) (g : Gate) : WireRef × List Gate :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => (.const true, [])
    | [a] => (getRef env a, [])
    | [a, b] => evalAndRef (getRef env a) (getRef env b) nextW
    | _ => (.const false, [])
  | GateOp.or => match g.inputs with
    | [] => (.const false, [])
    | [a] => (getRef env a, [])
    | [a, b] => evalOrRef (getRef env a) (getRef env b) nextW
    | _ => (.const false, [])
  | GateOp.not => match g.inputs with
    | [] => (.const true, [])
    | a :: _ => evalNotRef (getRef env a) nextW
  | _ => (.const false, [])

def shrinkFold (env : List WireRef) (accG : List Gate) (nextW : ℕ) : List Gate → List WireRef × List Gate
  | [] => (env, accG)
  | g :: gs =>
    let res := stepShrink env nextW g
    shrinkFold (env ++ [res.1]) (accG ++ res.2) (nextW + res.2.length) gs

theorem evalNotRef_spec (r : WireRef) (w : List Bool) (hr : refWf w.length r) :
    let res := evalNotRef r w.length
    refWf (w.length + res.2.length) res.1 ∧
    evalRef (evalWires res.2 w) res.1 = !(evalRef w r) ∧
    res.2.length ≤ 1 ∧
    (∀ g' ∈ res.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (res.2.filter fun g' => isNotOp g'.op).length ≤ 1 := by
  cases r with
  | const b => simp [evalNotRef, refWf, evalRef, evalWires]
  | wire i =>
    simp [evalNotRef, refWf, evalRef, evalWires_cons, evalWires_nil, GateOp.eval, isNotOp,
      getD_append_right w _ false (le_refl _)]

theorem evalAndRef_spec (r1 r2 : WireRef) (w : List Bool)
    (h1 : refWf w.length r1) (h2 : refWf w.length r2) :
    let res := evalAndRef r1 r2 w.length
    refWf (w.length + res.2.length) res.1 ∧
    evalRef (evalWires res.2 w) res.1 = (evalRef w r1 && evalRef w r2) ∧
    res.2.length ≤ 1 ∧
    (∀ g' ∈ res.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (res.2.filter fun g' => isNotOp g'.op).length = 0 := by
  dsimp only [refWf] at h1 h2
  cases r1 with
  | const b1 =>
    cases b1 <;> cases r2 with
    | const b2 => cases b2 <;> simp [evalAndRef, refWf, evalRef, evalWires]
    | wire j => simp [evalAndRef, refWf, evalRef, evalWires, h2]
  | wire i =>
    cases r2 with
    | const b2 => cases b2 <;> simp [evalAndRef, refWf, evalRef, evalWires, h1]
    | wire j =>
      simp [evalAndRef, refWf, evalRef, evalWires_cons, evalWires_nil, GateOp.eval, isNotOp,
        getD_append_right w _ false (le_refl _)]

theorem evalOrRef_spec (r1 r2 : WireRef) (w : List Bool)
    (h1 : refWf w.length r1) (h2 : refWf w.length r2) :
    let res := evalOrRef r1 r2 w.length
    refWf (w.length + res.2.length) res.1 ∧
    evalRef (evalWires res.2 w) res.1 = (evalRef w r1 || evalRef w r2) ∧
    res.2.length ≤ 1 ∧
    (∀ g' ∈ res.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (res.2.filter fun g' => isNotOp g'.op).length = 0 := by
  dsimp only [refWf] at h1 h2
  cases r1 with
  | const b1 =>
    cases b1 <;> cases r2 with
    | const b2 => cases b2 <;> simp [evalOrRef, refWf, evalRef, evalWires]
    | wire j => simp [evalOrRef, refWf, evalRef, evalWires, h2]
  | wire i =>
    cases r2 with
    | const b2 => cases b2 <;> simp [evalOrRef, refWf, evalRef, evalWires, h1]
    | wire j =>
      simp [evalOrRef, refWf, evalRef, evalWires_cons, evalWires_nil, GateOp.eval, isNotOp,
        getD_append_right w _ false (le_refl _)]

theorem getRef_wf (env : List WireRef) (bound : ℕ) (henv : ∀ r ∈ env, refWf bound r) (t : ℕ) :
    refWf bound (getRef env t) := by
  unfold getRef
  by_cases ht : t < env.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    exact henv _ (List.getElem_mem ht)
  · rw [List.getD_eq_default _ _ (by omega)]
    trivial

theorem refWf_mono {b1 b2 : ℕ} (h : b1 ≤ b2) {r : WireRef} (hr : refWf b1 r) : refWf b2 r := by
  cases r with
  | const _ => trivial
  | wire i => exact Nat.lt_of_lt_of_le hr h

theorem stepShrink_spec (m : ℕ) (env : List WireRef) (w : List Bool) (wOrig : List Bool) (g : Gate)
    (henvWf : ∀ r ∈ env, refWf w.length r)
    (hagree : ∀ t, evalRef w (getRef env t) = wOrig.getD t false)
    (hFan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hm_env : getRef env m = WireRef.const false) :
    let res := stepShrink env w.length g
    refWf (w.length + res.2.length) res.1 ∧
    evalRef (evalWires res.2 w) res.1 = g.op.eval (g.inputs.map fun i => wOrig.getD i false) ∧
    res.2.length ≤ 1 ∧
    (effReads m g = true → res.2.length = 0) ∧
    (∀ g' ∈ res.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (res.2.filter fun g' => isNotOp g'.op).length ≤ (if isNotOp g.op then 1 else 0) := by
  have h1 := hFan.1
  have h2 := hFan.2
  cases hop : g.op with
  | and =>
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
    · refine ⟨by simp [stepShrink, hop, hin, refWf], ?_, by simp [stepShrink, hop, hin], ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, GateOp.eval, evalRef, evalWires]
      · simp [effReads, hop, hin]
      · intro g' hg'; simp [stepShrink, hop, hin] at hg'
      · simp [stepShrink, hop, hin]
    · have ha := getRef_wf env w.length henvWf a
      refine ⟨by simpa [stepShrink, hop, hin] using ha, ?_, by simp [stepShrink, hop, hin], ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, evalWires, GateOp.eval, hagree a]
      · simp [stepShrink, hop, hin]
      · intro g' hg'; simp [stepShrink, hop, hin] at hg'
      · simp [stepShrink, hop, hin]
    · cases c with
      | nil =>
        have ha := getRef_wf env w.length henvWf a
        have hb := getRef_wf env w.length henvWf b
        have hsp := evalAndRef_spec (getRef env a) (getRef env b) w ha hb
        dsimp only at hsp
        refine ⟨by simpa [stepShrink, hop, hin] using hsp.1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [stepShrink, hop, hin, hsp.2.1, GateOp.eval, hagree a, hagree b]
        · simpa [stepShrink, hop, hin] using hsp.2.2.1
        · intro heff
          have hmem : m ∈ [a, b] := by simpa [effReads, hop, hin] using heff
          rcases List.mem_cons.mp hmem with rfl | hmem2
          · simp [stepShrink, hop, hin, hm_env, evalAndRef]
          · rcases List.mem_cons.mp hmem2 with rfl | hmem3
            · cases hga : getRef env a with
              | const b1 => cases b1 <;> simp [stepShrink, hop, hin, hm_env, hga, evalAndRef]
              | wire i => simp [stepShrink, hop, hin, hm_env, hga, evalAndRef]
            · cases hmem3
        · simpa [stepShrink, hop, hin] using hsp.2.2.2.1
        · have hnz := hsp.2.2.2.2
          simpa [stepShrink, hop, hin, isNotOp] using hnz
      | cons _ _ =>
        simp [hin] at h2
  | or =>
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
    · refine ⟨by simp [stepShrink, hop, hin, refWf], ?_, by simp [stepShrink, hop, hin], ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, GateOp.eval, evalRef, evalWires]
      · simp [effReads, hop, hin]
      · intro g' hg'; simp [stepShrink, hop, hin] at hg'
      · simp [stepShrink, hop, hin]
    · have ha := getRef_wf env w.length henvWf a
      refine ⟨by simpa [stepShrink, hop, hin] using ha, ?_, by simp [stepShrink, hop, hin], ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, evalWires, GateOp.eval, hagree a]
      · simp [stepShrink, hop, hin]
      · intro g' hg'; simp [stepShrink, hop, hin] at hg'
      · simp [stepShrink, hop, hin]
    · cases c with
      | nil =>
        have ha := getRef_wf env w.length henvWf a
        have hb := getRef_wf env w.length henvWf b
        have hsp := evalOrRef_spec (getRef env a) (getRef env b) w ha hb
        dsimp only at hsp
        refine ⟨by simpa [stepShrink, hop, hin] using hsp.1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [stepShrink, hop, hin, hsp.2.1, GateOp.eval, hagree a, hagree b]
        · simpa [stepShrink, hop, hin] using hsp.2.2.1
        · intro heff
          have hmem : m ∈ [a, b] := by simpa [effReads, hop, hin] using heff
          rcases List.mem_cons.mp hmem with rfl | hmem2
          · cases hgb : getRef env b with
            | const b2 => cases b2 <;> simp [stepShrink, hop, hin, hm_env, hgb, evalOrRef]
            | wire i => simp [stepShrink, hop, hin, hm_env, hgb, evalOrRef]
          · rcases List.mem_cons.mp hmem2 with rfl | hmem3
            · cases hga : getRef env a with
              | const b1 => cases b1 <;> simp [stepShrink, hop, hin, hm_env, hga, evalOrRef]
              | wire i => simp [stepShrink, hop, hin, hm_env, hga, evalOrRef]
            · cases hmem3
        · simpa [stepShrink, hop, hin] using hsp.2.2.2.1
        · have hnz := hsp.2.2.2.2
          simpa [stepShrink, hop, hin, isNotOp] using hnz
      | cons _ _ =>
        simp [hin] at h2
  | not =>
    rcases hin : g.inputs with _ | ⟨a, rest⟩
    · refine ⟨by simp [stepShrink, hop, hin, refWf], ?_, by simp [stepShrink, hop, hin], ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, GateOp.eval, evalRef, evalWires]
      · simp [effReads, hop, hin]
      · intro g' hg'; simp [stepShrink, hop, hin] at hg'
      · simp [stepShrink, hop, hin]
    · have ha := getRef_wf env w.length henvWf a
      have hsp := evalNotRef_spec (getRef env a) w ha
      dsimp only at hsp
      refine ⟨by simpa [stepShrink, hop, hin] using hsp.1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [stepShrink, hop, hin, hsp.2.1, GateOp.eval, hagree a]
      · simpa [stepShrink, hop, hin] using hsp.2.2.1
      · intro heff
        have ham : a = m := by simpa [effReads, hop, hin] using heff
        subst ham
        simp [stepShrink, hop, hin, hm_env, evalNotRef]
      · simpa [stepShrink, hop, hin] using hsp.2.2.2.1
      · have hnz := hsp.2.2.2.2
        simpa [stepShrink, hop, hin, isNotOp] using hnz
  | _ =>
    simp [hop] at h1

theorem shrinkFold_spec (m : ℕ) (gs : List Gate)
    (hFan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (env : List WireRef) (accG : List Gate) (initNew : List Bool) (wOrig : List Bool),
      (evalWires accG initNew).length = initNew.length + accG.length →
      m < env.length →
      env.length = wOrig.length →
      getRef env m = WireRef.const false →
      (∀ r ∈ env, refWf (initNew.length + accG.length) r) →
      (∀ t, evalRef (evalWires accG initNew) (getRef env t) = wOrig.getD t false) →
      (∀ g' ∈ accG, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) →
      let out := shrinkFold env accG (initNew.length + accG.length) gs
      (∀ t, evalRef (evalWires out.2 initNew) (getRef out.1 t) = (evalWires gs wOrig).getD t false) ∧
      out.2.length ≤ accG.length + gs.length ∧
      ((∃ g ∈ gs, effReads m g = true) → out.2.length < accG.length + gs.length) ∧
      (∀ g' ∈ out.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
      (out.2.filter fun g' => isNotOp g'.op).length ≤
        (accG.filter fun g' => isNotOp g'.op).length + (gs.filter fun g' => isNotOp g'.op).length := by
  induction gs with
  | nil =>
    intro env accG initNew wOrig _ _ _ _ _ hagree haccFan
    refine ⟨hagree, by simp [shrinkFold], ?_, haccFan, by simp [shrinkFold]⟩
    rintro ⟨g, hg, _⟩; cases hg
  | cons g gs ih =>
    intro env accG initNew wOrig hwLen hmlt hlen hm_env henvWf hagree haccFan
    dsimp only [shrinkFold]
    set w := evalWires accG initNew
    have hw_len_eq : w.length = initNew.length + accG.length := hwLen
    have hsp := stepShrink_spec m env w wOrig g (by simpa [hw_len_eq] using henvWf) hagree
      (hFan g List.mem_cons_self) hm_env
    dsimp only at hsp
    rw [hw_len_eq] at hsp
    set res := stepShrink env (initNew.length + accG.length) g
    have hres_wf : refWf (initNew.length + (accG ++ res.2).length) res.1 := by
      simpa [res, List.length_append, Nat.add_assoc] using hsp.1
    have henv1Wf : ∀ r ∈ env ++ [res.1], refWf (initNew.length + (accG ++ res.2).length) r := by
      intro r hr
      rcases List.mem_append.mp hr with hr1 | hr2
      · exact refWf_mono (by simp [List.length_append]) (henvWf r hr1)
      · rw [List.mem_singleton] at hr2; subst hr2; exact hres_wf
    have hw1Len : (evalWires (accG ++ res.2) initNew).length = initNew.length + (accG ++ res.2).length := by
      rw [evalWires_length]
    have hmlt1 : m < (env ++ [res.1]).length := by simp; omega
    have hlen1 : (env ++ [res.1]).length = (wOrig ++ [g.op.eval (g.inputs.map fun i => wOrig.getD i false)]).length := by
      simp [hlen]
    have hm_env1 : getRef (env ++ [res.1]) m = WireRef.const false := by
      unfold getRef at hm_env ⊢
      rw [getD_append_lt env [res.1] _ hmlt]
      exact hm_env
    have hagree1 : ∀ t, evalRef (evalWires (accG ++ res.2) initNew) (getRef (env ++ [res.1]) t) =
        (wOrig ++ [g.op.eval (g.inputs.map fun i => wOrig.getD i false)]).getD t false := by
      intro t
      rw [evalWires_append]
      by_cases ht : t < env.length
      · have hgt : getRef (env ++ [res.1]) t = getRef env t := by
          unfold getRef; exact getD_append_lt env _ _ ht
        rw [hgt, getD_append_lt wOrig _ false (hlen ▸ ht), ← hagree t]
        have hwf := getRef_wf env w.length (by simpa [hw_len_eq] using henvWf) t
        cases hgr : getRef env t with
        | const b => simp [evalRef]
        | wire i =>
          have hi : i < w.length := by simpa [hgr, refWf] using hwf
          simp only [evalRef]
          exact evalWires_prefix_getD res.2 w hi
      · by_cases hte : t = env.length
        · subst hte
          have hgt : getRef (env ++ [res.1]) env.length = res.1 := by
            unfold getRef; rw [getD_append_right env _ _ (le_refl _)]; simp
          rw [hgt, getD_append_right wOrig _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
          simpa [w, res] using hsp.2.1
        · have hgt : getRef (env ++ [res.1]) t = WireRef.const false := by
            unfold getRef; rw [List.getD_eq_default _ _ (by simp; omega)]
          rw [hgt, List.getD_eq_default _ false (by simp; omega)]
          rfl
    have hacc1Fan : ∀ g' ∈ accG ++ res.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg'
      rcases List.mem_append.mp hg' with hg1 | hg2
      · exact haccFan g' hg1
      · exact hsp.2.2.2.2.1 g' hg2
    have ihRes := ih (fun x hx => hFan x (List.mem_cons_of_mem g hx))
      (env ++ [res.1]) (accG ++ res.2) initNew
      (wOrig ++ [g.op.eval (g.inputs.map fun i => wOrig.getD i false)])
      hw1Len hmlt1 hlen1 hm_env1 henv1Wf hagree1 hacc1Fan
    have hnw_eq : initNew.length + (accG ++ res.2).length = (initNew.length + accG.length) + res.2.length := by
      simp [List.length_append, Nat.add_assoc]
    rw [← hnw_eq]
    set outG := shrinkFold (env ++ [res.1]) (accG ++ res.2) (initNew.length + (accG ++ res.2).length) gs
    set LG := outG.2.length
    set LN := (outG.2.filter fun g' => isNotOp g'.op).length
    have haccL : (accG ++ res.2).length = accG.length + res.2.length := List.length_append
    have haccN : ((accG ++ res.2).filter fun g' => isNotOp g'.op).length =
        (accG.filter fun g' => isNotOp g'.op).length + (res.2.filter fun g' => isNotOp g'.op).length :=
      filter_not_append accG res.2
    refine ⟨?_, ?_, ?_, ihRes.2.2.2.1, ?_⟩
    · simpa [evalWires_cons] using ihRes.1
    · have hlenB : LG ≤ (accG ++ res.2).length + gs.length := ihRes.2.1
      have hstepLen : res.2.length ≤ 1 := by simpa [res] using hsp.2.2.1
      change LG ≤ accG.length + (g :: gs).length
      rw [List.length_cons]
      omega
    · rintro ⟨g0, hg0, heff0⟩
      change LG < accG.length + (g :: gs).length
      rw [List.length_cons]
      rcases List.mem_cons.mp hg0 with rfl | hg0s
      · have hz : res.2.length = 0 := by simpa [res] using hsp.2.2.2.1 heff0
        have hlenB : LG ≤ (accG ++ res.2).length + gs.length := ihRes.2.1
        omega
      · have hltB : LG < (accG ++ res.2).length + gs.length := ihRes.2.2.1 ⟨g0, hg0s, heff0⟩
        have hstepLen : res.2.length ≤ 1 := by simpa [res] using hsp.2.2.1
        omega
    · have hnotB : LN ≤ ((accG ++ res.2).filter fun g' => isNotOp g'.op).length + (gs.filter fun g' => isNotOp g'.op).length :=
        ihRes.2.2.2.2
      have hstepNot : (res.2.filter fun g' => isNotOp g'.op).length ≤ if isNotOp g.op then 1 else 0 := by
        simpa [res] using hsp.2.2.2.2.2
      change LN ≤ (accG.filter fun g' => isNotOp g'.op).length + ((g :: gs).filter fun g' => isNotOp g'.op).length
      rw [filter_length_cons]
      cases hn : isNotOp g.op with
      | true => simp only [hn, ite_true] at hstepNot ⊢; omega
      | false => simp only [hn, Bool.false_eq_true, ite_false] at hstepNot ⊢; omega

theorem shrink_last {n m q b : ℕ} (πs : Fin (m + 1) → Fin n) (hπs : Function.Surjective πs)
    (F : Fin q → (Fin n → Bool) → Bool)
    (h_nonconst : ∀ j : Fin q, ∃ x y : Fin n → Bool, F j x ≠ F j y)
    (h_ess : ∀ i : Fin n, ∃ (j : Fin q) (x y : Fin n → Bool), (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y)
    (u1' : Fin (m + 1)) (hu1' : u1' ≠ Fin.last m) (hπeq : πs u1' = πs (Fin.last m))
    {s' : ℕ} (h_fits : fitsPred q b (m + 1) (fun j y => F j fun i => decide (∃ u, πs u = i ∧ y u = true)) s') :
    1 ≤ s' ∧
    let π' : Fin m → Fin n := fun v => πs v.castSucc
    Function.Surjective π' ∧
    fitsPred q b m (fun j y => F j fun i => decide (∃ v, π' v = i ∧ y v = true)) (s' - 1) := by
  have hu1_lt : u1'.val < m := by
    have := u1'.isLt
    have hne : u1'.val ≠ m := fun h => hu1' (Fin.ext h)
    omega
  set v1 : Fin m := ⟨u1'.val, hu1_lt⟩
  set π' : Fin m → Fin n := fun v => πs v.castSucc
  have hv1_cast : v1.castSucc = u1' := Fin.ext rfl
  have hπ'_eq : π' v1 = πs (Fin.last m) := by simp [π', hv1_cast, hπeq]
  have hπ'_surj : Function.Surjective π' := by
    intro i
    obtain ⟨u, hu⟩ := hπs i
    by_cases hlast : u = Fin.last m
    · exact ⟨v1, by rw [hπ'_eq, ← hlast, hu]⟩
    · have hult : u.val < m := by
        have := u.isLt
        have hne : u.val ≠ m := fun h => hlast (Fin.ext h)
        omega
      exact ⟨⟨u.val, hult⟩, by simpa [π'] using hu⟩
  have hexpand_snoc : ∀ (y' : Fin m → Bool) (i : Fin n),
      decide (∃ u, πs u = i ∧ snocBool y' false u = true) =
        decide (∃ v, π' v = i ∧ y' v = true) := by
    intro y' i
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, hpu, hyu⟩
      by_cases hu : u.val < m
      · exact ⟨⟨u.val, hu⟩, by simpa [π'] using hpu, by simpa [snocBool, hu] using hyu⟩
      · simp [snocBool, hu] at hyu
    · rintro ⟨v, hpv, hyv⟩
      exact ⟨v.castSucc, by simpa [π'] using hpv, by simp [snocBool, v.isLt, hyv]⟩
  obtain ⟨C, tap, hFan, hSz, hNot, hEval⟩ := h_fits
  have htap_ne : ∀ j : Fin q, tap j ≠ m := by
    intro j htm
    set yTrue : Fin m → Bool := fun _ => true
    have heq0 : F j (fun i => decide (∃ u, πs u = i ∧ snocBool yTrue false u = true)) = false := by
      have he := hEval j (snocBool yTrue false)
      change (evalWires C.gates (List.ofFn (snocBool yTrue false))).getD (tap j) false = _ at he
      rw [htm, evalWires_prefix_getD C.gates _ (by simp), list_ofFn_snocBool,
        getD_append_right (List.ofFn yTrue) [false] false (by simp)] at he
      simpa using he.symm
    have heq1 : F j (fun i => decide (∃ u, πs u = i ∧ snocBool yTrue true u = true)) = true := by
      have he := hEval j (snocBool yTrue true)
      change (evalWires C.gates (List.ofFn (snocBool yTrue true))).getD (tap j) false = _ at he
      rw [htm, evalWires_prefix_getD C.gates _ (by simp), list_ofFn_snocBool,
        getD_append_right (List.ofFn yTrue) [true] false (by simp)] at he
      simpa using he.symm
    have hexp : (fun i => decide (∃ u, πs u = i ∧ snocBool yTrue false u = true)) =
        (fun i => decide (∃ u, πs u = i ∧ snocBool yTrue true u = true)) := by
      funext i
      rw [hexpand_snoc yTrue i]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨v, hpv, hyv⟩
        exact ⟨v.castSucc, by simpa [π'] using hpv, by simp [snocBool, v.isLt, hyv]⟩
      · rintro ⟨u, hpu, hyu⟩
        by_cases hu : u.val < m
        · exact ⟨⟨u.val, hu⟩, by simpa [π'] using hpu, by simpa [snocBool, hu] using hyu⟩
        · have hlast : u = Fin.last m := Fin.ext (by have := u.isLt; simp [Fin.val_last]; omega)
          subst hlast
          exact ⟨v1, by rw [hπ'_eq, hpu], rfl⟩
    rw [hexp] at heq0
    rw [heq0] at heq1
    exact Bool.false_ne_true heq1
  have hex_eff : ∃ g ∈ C.gates, effReads m g = true := by
    by_contra hno
    have hno' : ∀ g ∈ C.gates, effReads m g = false := by
      intro g hg
      cases he : effReads m g with
      | false => rfl
      | true => exact False.elim (hno ⟨g, hg, he⟩)
    set i0 := πs (Fin.last m)
    obtain ⟨j, x0, x1, hdiff, hFne⟩ := h_ess i0
    have hx_ne : x0 i0 ≠ x1 i0 := by
      intro heq
      have hx : x0 = x1 := by
        funext i
        by_cases hi : i = i0
        · subst hi; exact heq
        · exact hdiff i hi
      exact hFne (congrArg (F j) hx)
    have hcase : ∀ (xA xB : Fin n → Bool),
        (∀ i, i ≠ i0 → xA i = xB i) → xA i0 = false → xB i0 = true → F j xA ≠ F j xB → False := by
      intro xA xB hAB hxA0 hxB0 hFAB
      set yA : Fin (m + 1) → Bool := fun u => if πs u = i0 then false else xA (πs u)
      set yB : Fin (m + 1) → Bool := fun u => if u = Fin.last m then true else yA u
      have hexpA : (fun i => decide (∃ u, πs u = i ∧ yA u = true)) = xA := by
        funext i
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨u, hpu, hyu⟩
          by_cases hi : i = i0
          · subst hi; simp [yA, hpu] at hyu
          · simpa [yA, hpu, hi] using hyu
        · intro hxi
          obtain ⟨u, hpu⟩ := hπs i
          refine ⟨u, hpu, ?_⟩
          by_cases hi : i = i0
          · subst hi; rw [hxi] at hxA0; exact absurd hxA0.symm Bool.false_ne_true
          · simp [yA, hpu, hi, hxi]
      have hexpB : (fun i => decide (∃ u, πs u = i ∧ yB u = true)) = xB := by
        funext i
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨u, hpu, hyu⟩
          by_cases hi : i = i0
          · subst hi; exact hxB0
          · have hne : u ≠ Fin.last m := fun he => hi (hpu.symm.trans (congrArg πs he))
            have hyAu : yA u = true := by simpa [yB, hne] using hyu
            rw [← hAB i hi]
            simpa [yA, hpu, hi] using hyAu
        · intro hxi
          by_cases hi : i = i0
          · subst hi; exact ⟨Fin.last m, rfl, by simp [yB]⟩
          · obtain ⟨u, hpu⟩ := hπs i
            have hne : u ≠ Fin.last m := fun he => hi (hpu.symm.trans (congrArg πs he))
            refine ⟨u, hpu, ?_⟩
            simp [yB, hne, yA, hpu, hi, hAB i hi, hxi]
      have hyAgree : ∀ t, t ≠ m → (List.ofFn yA).getD t false = (List.ofFn yB).getD t false := by
        intro t ht
        by_cases htm : t < m + 1
        · rw [getD_ofFn_lt yA htm, getD_ofFn_lt yB htm]
          have hne : (⟨t, htm⟩ : Fin (m + 1)) ≠ Fin.last m := fun he => ht (congrArg Fin.val he)
          simp [yB, hne]
        · rw [getD_ofFn_ge yA (by omega), getD_ofFn_ge yB (by omega)]
      have hCeq := evalWires_indep_of_not_effReads C.gates hFan hno' (List.ofFn yA) (List.ofFn yB)
        (by simp) (by simp) hyAgree (tap j) (htap_ne j)
      have heA := hEval j yA
      have heB := hEval j yB
      dsimp only at heA heB
      rw [hexpA] at heA
      rw [hexpB] at heB
      change (evalWires C.gates (List.ofFn yA)).getD (tap j) false = F j xA at heA
      change (evalWires C.gates (List.ofFn yB)).getD (tap j) false = F j xB at heB
      rw [heA, heB] at hCeq
      exact hFAB hCeq
    cases hx0 : x0 i0 with
    | false =>
      have hx1 : x1 i0 = true := by
        cases hx : x1 i0
        · simp [hx, hx0] at hx_ne
        · rfl
      exact hcase x0 x1 hdiff hx0 hx1 hFne
    | true =>
      have hx1 : x1 i0 = false := by
        cases hx : x1 i0
        · rfl
        · simp [hx, hx0] at hx_ne
      exact hcase x1 x0 (fun i hi => (hdiff i hi).symm) hx1 hx0 (fun h => hFne h.symm)
  set env0 : List WireRef := (List.range m).map WireRef.wire ++ [WireRef.const false]
  have hm_lt_env0 : m < env0.length := by simp [env0]
  have hm_env0 : getRef env0 m = WireRef.const false := by
    unfold getRef
    rw [getD_append_right ((List.range m).map WireRef.wire) [WireRef.const false] _ (by simp)]
    simp
  have henv0_wf : ∀ r ∈ env0, refWf m r := by
    intro r hr
    rcases List.mem_append.mp hr with hr1 | hr2
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr1
      exact List.mem_range.mp hi
    · rw [List.mem_singleton] at hr2; subst hr2; trivial
  set out := shrinkFold env0 [] m C.gates
  have hfold : ∀ (y' : Fin m → Bool),
      (∀ t, evalRef (evalWires out.2 (List.ofFn y')) (getRef out.1 t) = (evalWires C.gates (List.ofFn (snocBool y' false))).getD t false) ∧
      out.2.length ≤ C.gates.length ∧
      ((∃ g ∈ C.gates, effReads m g = true) → out.2.length < C.gates.length) ∧
      (∀ g' ∈ out.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
      (out.2.filter fun g' => isNotOp g'.op).length ≤ (C.gates.filter fun g' => isNotOp g'.op).length := by
    intro y'
    have hsp := shrinkFold_spec m C.gates hFan env0 [] (List.ofFn y') (List.ofFn (snocBool y' false))
      (by rw [evalWires_length]) hm_lt_env0 (by simp [env0]) hm_env0
      (by simpa [List.length_ofFn] using henv0_wf)
      (fun t => by
        rw [evalWires_nil, list_ofFn_snocBool]
        by_cases htm : t < m
        · have hgt : getRef env0 t = WireRef.wire t := by
            unfold getRef
            rw [getD_append_lt ((List.range m).map WireRef.wire) _ _ (by simp [htm])]
            simp [List.getD_eq_getElem?_getD, htm]
          rw [hgt, evalRef, getD_append_lt (List.ofFn y') [false] false (by simp [htm])]
        · by_cases hte : t = m
          · subst hte
            rw [hm_env0, evalRef, getD_append_right (List.ofFn y') [false] false (by simp)]
            simp
          · have hgt : getRef env0 t = WireRef.const false := by
              unfold getRef; rw [List.getD_eq_default _ _ (by simp [env0]; omega)]
            rw [hgt, evalRef, List.getD_eq_default _ false (by simp; omega)])
      (fun _ hg => by cases hg)
    simpa [out] using hsp
  have hfold0 := hfold (fun _ => false)
  have hlen_lt : out.2.length < C.gates.length := hfold0.2.2.1 hex_eff
  have hs_ge : 1 ≤ s' := by
    change C.gates.length ≤ s' at hSz
    omega
  refine ⟨hs_ge, hπ'_surj, ?_⟩
  have hnot_const : ∀ j : Fin q, ∃ wj : ℕ, getRef out.1 (tap j) = WireRef.wire wj := by
    intro j
    cases hgt : getRef out.1 (tap j) with
    | wire wj => exact ⟨wj, rfl⟩
    | const c =>
      exfalso
      obtain ⟨xA, xB, hAB⟩ := h_nonconst j
      have hEvalC : ∀ (x : Fin n → Bool), F j x = c := by
        intro x
        set y' : Fin m → Bool := fun v => x (π' v)
        have hExp : (fun i => decide (∃ v, π' v = i ∧ y' v = true)) = x := by
          funext i
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨v, hpv, hyv⟩
            simpa [y', hpv] using hyv
          · intro hxi
            obtain ⟨v, hpv⟩ := hπ'_surj i
            exact ⟨v, hpv, by simp [y', hpv, hxi]⟩
        have hspec := (hfold y').1 (tap j)
        have htapEval := hEval j (snocBool y' false)
        dsimp only at htapEval
        change (evalWires C.gates (List.ofFn (snocBool y' false))).getD (tap j) false = _ at htapEval
        rw [← hspec, hgt, evalRef] at htapEval
        have hEqSnoc : (fun i => decide (∃ u, πs u = i ∧ snocBool y' false u = true)) = x := by
          funext i; rw [hexpand_snoc y' i]; exact congrFun hExp i
        rw [hEqSnoc] at htapEval
        exact htapEval.symm
      rw [hEvalC xA, hEvalC xB] at hAB
      exact hAB rfl
  set tap' : Fin q → ℕ := fun j => match getRef out.1 (tap j) with
    | WireRef.wire wj => wj
    | WireRef.const _ => 0
  refine ⟨⟨out.2, 0⟩, tap', hfold0.2.2.2.1, ?_, ?_, ?_⟩
  · change out.2.length ≤ s' - 1
    change C.gates.length ≤ s' at hSz
    omega
  · rw [notCount_eq] at hNot ⊢
    exact Nat.le_trans hfold0.2.2.2.2 hNot
  · intro j y'
    obtain ⟨wj, hwj⟩ := hnot_const j
    have htap' : tap' j = wj := by simp [tap', hwj]
    have hspec := (hfold y').1 (tap j)
    have htapEval := hEval j (snocBool y' false)
    dsimp only at htapEval
    change (evalWires C.gates (List.ofFn (snocBool y' false))).getD (tap j) false = _ at htapEval
    change (evalWires out.2 (List.ofFn y')).getD (tap' j) false = _
    dsimp only
    rw [htap']
    rw [hwj, evalRef] at hspec
    rw [hspec, htapEval]
    congr 1
    funext i
    exact hexpand_snoc y' i

theorem shrink_one {n m q b : ℕ} (π : Fin (m + 1) → Fin n) (hπ : Function.Surjective π)
    (F : Fin q → (Fin n → Bool) → Bool)
    (h_nonconst : ∀ j : Fin q, ∃ x y : Fin n → Bool, F j x ≠ F j y)
    (h_ess : ∀ i : Fin n, ∃ (j : Fin q) (x y : Fin n → Bool), (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y)
    (u0 u1 : Fin (m + 1)) (hu : u0 ≠ u1) (hπeq : π u0 = π u1)
    {s' : ℕ} (h_fits : fitsPred q b (m + 1) (fun j y => F j fun i => decide (∃ u, π u = i ∧ y u = true)) s') :
    1 ≤ s' ∧
    ∃ (π' : Fin m → Fin n), Function.Surjective π' ∧
      fitsPred q b m (fun j y => F j fun i => decide (∃ v, π' v = i ∧ y v = true)) (s' - 1) := by
  set e := swapFin u0 (Fin.last m)
  set πs := π ∘ e
  have hπs_surj : Function.Surjective πs := by
    intro i
    obtain ⟨v, hv⟩ := hπ i
    exact ⟨e v, by simp [πs, e, swapFin_invol, hv]⟩
  have he_last : e (Fin.last m) = u0 := swapFin_right u0 (Fin.last m)
  have hu1'_ne : e u1 ≠ Fin.last m := by
    intro h
    have : e (e u1) = e (Fin.last m) := congrArg e h
    dsimp only [e] at this
    rw [swapFin_invol, swapFin_right] at this
    exact hu this.symm
  have hπs_eq : πs (e u1) = πs (Fin.last m) := by
    simp [πs, e, swapFin_invol, he_last, hπeq]
  have hfits_s : fitsPred q b (m + 1) (fun j y => F j fun i => decide (∃ u, πs u = i ∧ y u = true)) s' := by
    refine relabel_fits e h_fits _ ?_
    intro j y2
    congr 1
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, hpu, hyu⟩
      exact ⟨e u, hpu, by simpa [e, swapFin_invol] using hyu⟩
    · rintro ⟨v, hpv, hyv⟩
      exact ⟨e v, by simp [πs, e, swapFin_invol, hpv], hyv⟩
  obtain ⟨hs, hπ'_surj, hfits'⟩ :=
    shrink_last πs hπs_surj F h_nonconst h_ess (e u1) hu1'_ne hπs_eq hfits_s
  exact ⟨hs, _, hπ'_surj, hfits'⟩

theorem not_inj_of_lt {m n : ℕ} (π : Fin m → Fin n) (hlt : n < m) :
    ∃ u0 u1 : Fin m, u0 ≠ u1 ∧ π u0 = π u1 := by
  by_contra h
  have hinj : ∀ u0 u1 : Fin m, π u0 = π u1 → u0 = u1 := by
    intro u0 u1 heq
    by_contra hne
    exact h ⟨u0, u1, hne, heq⟩
  have hle_fiber : ∀ i : Fin n, (fiberList π i).length ≤ 1 := by
    intro i
    have hnd : (fiberList π i).Nodup := (List.nodup_finRange m).filter _
    cases hf : fiberList π i with
    | nil => simp
    | cons a t =>
      cases ht : t with
      | nil => simp
      | cons b r =>
        rw [hf, List.nodup_cons] at hnd
        have ha : a ∈ fiberList π i := by rw [hf]; simp
        have hb : b ∈ fiberList π i := by rw [hf, ht]; simp
        have hpa : π a = i := decide_eq_true_eq.mp (List.mem_filter.mp ha).2
        have hpb : π b = i := decide_eq_true_eq.mp (List.mem_filter.mp hb).2
        have hab : a = b := hinj a b (hpa.trans hpb.symm)
        subst hab
        exact absurd (show a ∈ t by rw [ht]; simp) hnd.1
  have hsum_le : ∀ ks : List (Fin n), (ks.map fun i => (fiberList π i).length).sum ≤ ks.length := by
    intro ks
    induction ks with
    | nil => simp
    | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hle_fiber i
      omega
  have hsum_eq : ((List.finRange n).map fun i => (fiberList π i).length).sum = m := by
    have := sum_fiberList π (List.finRange m)
    simpa [fiberList] using this
  have hle := hsum_le (List.finRange n)
  rw [hsum_eq, List.length_finRange] at hle
  omega

theorem shrink_ind (d : ℕ) :
    ∀ {n m q b : ℕ} (π : Fin m → Fin n) (hπ : Function.Surjective π)
      (F : Fin q → (Fin n → Bool) → Bool)
      (h_nonconst : ∀ j : Fin q, ∃ x y : Fin n → Bool, F j x ≠ F j y)
      (h_ess : ∀ i : Fin n, ∃ (j : Fin q) (x y : Fin n → Bool), (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y)
      (hd : m - n = d)
      {s' : ℕ} (h_fits : fitsPred q b m (fun j y => F j fun i => decide (∃ u, π u = i ∧ y u = true)) s'),
      d ≤ s' ∧ fitsPred q b n F (s' - d) := by
  induction d with
  | zero =>
    intro n m q b π hπ F _ _ hd s' h_fits
    rw [Nat.sub_zero]
    refine ⟨Nat.zero_le _, ?_⟩
    refine relabel_fits π h_fits F ?_
    intro j x
    congr 1
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Function.comp_apply]
    constructor
    · intro hxi
      obtain ⟨u, hpu⟩ := hπ i
      exact ⟨u, hpu, by rw [hpu]; exact hxi⟩
    · rintro ⟨u, hpu, hxu⟩
      rw [← hpu]; exact hxu
  | succ k ih =>
    intro n m q b π hπ F h_nonconst h_ess hd s' h_fits
    have hlt : n < m := by omega
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    obtain ⟨u0, u1, hu, hπeq⟩ := not_inj_of_lt π hlt
    obtain ⟨hs, π', hπ'_surj, hfits'⟩ := shrink_one π hπ F h_nonconst h_ess u0 u1 hu hπeq h_fits
    obtain ⟨hk, hfin⟩ := ih π' hπ'_surj F h_nonconst h_ess (by omega) hfits'
    refine ⟨by omega, ?_⟩
    rwa [show s' - 1 - k = s' - (k + 1) by omega] at hfin

end PEqualNP.Outside.L_meta_33687_aux

namespace PEqualNP.Outside

open PEqualNP.Outside.L_meta_33687_aux

theorem L_meta_33687 :
    ∀ (n m q b : Nat) (π : Fin m → Fin n) (F : Fin q → (Fin n → Bool) → Bool),
      Function.Surjective π →
      (∀ j, ∃ x y, F j x ≠ F j y) →
      (∀ i : Fin n, ∃ (j : Fin q) (x y : Fin n → Bool), (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y) →
      let expand := fun (y : Fin m → Bool) (i : Fin n) => decide (∃ u, π u = i ∧ y u = true)
      let fits := fun (k : Nat) (T : Fin q → (Fin k → Bool) → Bool) (s : Nat) =>
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → Nat),
          PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
          PEqualNP.NotBracket.notCount C ≤ b ∧
          ∀ j x, (C.wires (List.ofFn x)).getD (tap j) false = T j x
      let lifted := fun j y => F j (expand y)
      (∀ s, fits m lifted s → m-n ≤ s) ∧
      ∀ s, fits n F s ↔ fits m lifted (s+(m-n)) := by
  intro n m q b π F hπ h_nonconst h_ess
  dsimp only
  constructor
  · intro s hs
    exact (shrink_ind (m - n) π hπ F h_nonconst h_ess rfl hs).1
  · intro s
    constructor
    · intro hs
      exact forward_fits π hπ F hs
    · intro hs
      have hbk := (shrink_ind (m - n) π hπ F h_nonconst h_ess rfl hs).2
      rw [Nat.add_sub_cancel] at hbk
      exact hbk

end PEqualNP.Outside
