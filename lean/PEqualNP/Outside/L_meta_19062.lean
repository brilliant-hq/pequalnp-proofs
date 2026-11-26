import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19062_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wires_eq_evalGates (C : Circuit) (x : List Bool) :
    C.wires x = evalGates C.gates x := rfl

lemma evalGates_nil (w : List Bool) : evalGates [] w = w := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    evalGates (g :: gs) w = evalGates gs (step w g) := rfl

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) :=
  List.foldl_append

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih, step_length]
    simp; omega

lemma step_getD_lt {w : List Bool} {g : Gate} {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  exact List.getD_append w _ false i hi

lemma step_getD_eq (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right w _ false w.length (le_refl _)]
  simp

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (evalGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons]
    have hlt : i < (step w g).length := by rw [step_length]; omega
    rw [ih (step w g) hlt, step_getD_lt hi]

def gOr (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩
def gAnd (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def IsM2Gate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma isM2_gOr (a b : ℕ) : IsM2Gate (gOr a b) := by
  refine ⟨by simp [gOr], by simp [gOr]⟩

lemma isM2_gAnd (a b : ℕ) : IsM2Gate (gAnd a b) := by
  refine ⟨by simp [gAnd], by simp [gAnd]⟩

lemma step_gOr_val (w : List Bool) (a b : ℕ) :
    (step w (gOr a b)).getD w.length false = (w.getD a false || w.getD b false) := by
  rw [step_getD_eq]
  simp [gOr, GateOp.eval]

lemma step_gAnd_val (w : List Bool) (a b : ℕ) :
    (step w (gAnd a b)).getD w.length false = (w.getD a false && w.getD b false) := by
  rw [step_getD_eq]
  simp [gAnd, GateOp.eval]

def zGates (n : ℕ) : List Gate :=
  (List.range n).map fun i => gOr i (n + i)

lemma zGates_length (n : ℕ) : (zGates n).length = n := by
  simp [zGates]

lemma zGates_m2 (n : ℕ) : ∀ g ∈ zGates n, IsM2Gate g := by
  intro g hg
  simp only [zGates, List.mem_map] at hg
  rcases hg with ⟨i, _, rfl⟩
  exact isM2_gOr i (n + i)

lemma zGates_eval_aux (n : ℕ) : ∀ (k : ℕ) (w : List Bool),
    k ≤ n → w.length = 2 * n →
    ∀ i < k, (evalGates ((List.range k).map fun j => gOr j (n + j)) w).getD (2 * n + i) false =
      (w.getD i false || w.getD (n + i) false) := by
  intro k
  induction k with
  | zero => intro w _ _ i hi; omega
  | succ k ih =>
    intro w hk hw i hi
    rw [List.range_succ, List.map_append, List.map_singleton, evalGates_append]
    set w1 := evalGates ((List.range k).map fun j => gOr j (n + j)) w
    have hw1_len : w1.length = 2 * n + k := by
      rw [evalGates_length, hw, List.length_map, List.length_range]
    by_cases hik : i < k
    · have hlt : 2 * n + i < w1.length := by omega
      rw [evalGates_getD_lt _ _ hlt]
      exact ih w (by omega) hw i hik
    · have hieq : i = k := by omega
      subst hieq
      rw [evalGates_cons, evalGates_nil]
      have hidx : 2 * n + i = w1.length := by omega
      rw [hidx, step_gOr_val]
      have hi1 : i < w.length := by omega
      have hi2 : n + i < w.length := by omega
      rw [evalGates_getD_lt _ _ hi1, evalGates_getD_lt _ _ hi2]

lemma zGates_eval (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < n) :
    (evalGates (zGates n) (oneEach u v)).getD (2 * n + i) false =
      (decide (i = u.val) || decide (i = v.val)) := by
  have hlen : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
  rw [zGates, zGates_eval_aux n n (oneEach u v) (le_refl n) hlen i hi]
  have h1 : (oneEach u v).getD i false = decide (i = u.val) := by
    rw [oneEach, List.getD_append _ _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    simp [Fin.ext_iff]
  have h2 : (oneEach u v).getD (n + i) false = decide (i = v.val) := by
    rw [oneEach, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    simp [Fin.ext_iff]
  rw [h1, h2]

def orChainAcc (base acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | j :: js =>
    let res := orChainAcc (base + 1) base js
    (gOr acc j :: res.1, res.2)

lemma orChainAcc_length (base acc : ℕ) (js : List ℕ) :
    (orChainAcc base acc js).1.length = js.length := by
  induction js generalizing base acc with
  | nil => rfl
  | cons j js ih => simp [orChainAcc, ih]

lemma orChainAcc_m2 (base acc : ℕ) (js : List ℕ) :
    ∀ g ∈ (orChainAcc base acc js).1, IsM2Gate g := by
  induction js generalizing base acc with
  | nil => intro g hg; simp [orChainAcc] at hg
  | cons j js ih =>
    intro g hg
    simp only [orChainAcc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact isM2_gOr _ _
    · exact ih _ _ g hg

lemma orChainAcc_out_lt (base acc : ℕ) (js : List ℕ) (hacc : acc < base) :
    (orChainAcc base acc js).2 < base + js.length := by
  induction js generalizing base acc with
  | nil => simp [orChainAcc]; omega
  | cons j js ih =>
    simp only [orChainAcc, List.length_cons]
    have h := ih (base + 1) base (by omega)
    omega

lemma any_congr_mem {l : List ℕ} {p q : ℕ → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma orChainAcc_eval (base acc : ℕ) (js : List ℕ) (w : List Bool)
    (hw : w.length = base) (hacc : acc < base) (hjs : ∀ j ∈ js, j < base) :
    (evalGates (orChainAcc base acc js).1 w).getD (orChainAcc base acc js).2 false =
      (w.getD acc false || js.any (fun j => w.getD j false)) := by
  induction js generalizing base acc w with
  | nil => simp [orChainAcc, evalGates]
  | cons j js ih =>
    simp only [orChainAcc, evalGates_cons, List.any_cons]
    set w1 := step w (gOr acc j)
    have hw1 : w1.length = base + 1 := by rw [step_length, hw]
    have hjs' : ∀ x ∈ js, x < base + 1 := fun x hx => by
      have := hjs x (List.mem_cons_of_mem _ hx); omega
    rw [ih (base + 1) base w1 hw1 (by omega) hjs']
    have hbase : w1.getD base false = (w.getD acc false || w.getD j false) := by
      rw [← hw]; exact step_gOr_val w acc j
    have hany : js.any (fun x => w1.getD x false) = js.any (fun x => w.getD x false) := by
      apply any_congr_mem
      intro x hx
      have hxlt : x < w.length := by rw [hw]; exact hjs x (List.mem_cons_of_mem _ hx)
      exact step_getD_lt hxlt
    rw [hbase, hany, Bool.or_assoc]

def orGroups (base : ℕ) : List (List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | grp :: grps =>
    match grp with
    | [] => orGroups base grps
    | j0 :: js =>
      let r1 := orChainAcc base j0 js
      let r2 := orGroups (base + js.length) grps
      (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma orGroups_m2 (base : ℕ) (grps : List (List ℕ)) :
    ∀ g ∈ (orGroups base grps).1, IsM2Gate g := by
  induction grps generalizing base with
  | nil => intro g hg; simp [orGroups] at hg
  | cons grp grps ih =>
    cases grp with
    | nil => exact ih base
    | cons j0 js =>
      intro g hg
      simp only [orGroups, List.mem_append] at hg
      rcases hg with hg | hg
      · exact orChainAcc_m2 base j0 js g hg
      · exact ih (base + js.length) g hg

lemma orGroups_length (base : ℕ) (grps : List (List ℕ))
    (hne : ∀ grp ∈ grps, grp ≠ []) :
    (orGroups base grps).1.length + grps.length = (grps.map List.length).sum := by
  induction grps generalizing base with
  | nil => simp [orGroups]
  | cons grp grps ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] List.mem_cons_self)
    | cons j0 js =>
      have hne' : ∀ g ∈ grps, g ≠ [] := fun g hg => hne g (List.mem_cons_of_mem _ hg)
      have h := ih (base + js.length) hne'
      simp only [orGroups, List.length_append, orChainAcc_length, List.length_cons,
        List.map_cons, List.sum_cons]
      omega

lemma orGroups_outs_length (base : ℕ) (grps : List (List ℕ))
    (hne : ∀ grp ∈ grps, grp ≠ []) :
    (orGroups base grps).2.length = grps.length := by
  induction grps generalizing base with
  | nil => rfl
  | cons grp grps ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] List.mem_cons_self)
    | cons j0 js =>
      simp only [orGroups, List.length_cons]
      exact congrArg (· + 1) (ih (base + js.length) fun g hg => hne g (List.mem_cons_of_mem _ hg))

lemma orGroups_outs_lt (base : ℕ) (grps : List (List ℕ))
    (hne : ∀ grp ∈ grps, grp ≠ [])
    (hlt : ∀ grp ∈ grps, ∀ j ∈ grp, j < base) :
    ∀ o ∈ (orGroups base grps).2, o < base + (orGroups base grps).1.length := by
  induction grps generalizing base with
  | nil => intro o ho; simp [orGroups] at ho
  | cons grp grps ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] List.mem_cons_self)
    | cons j0 js =>
      intro o ho
      simp only [orGroups, List.mem_cons, List.length_append, orChainAcc_length] at ho ⊢
      rcases ho with rfl | ho
      · have h1 := orChainAcc_out_lt base j0 js (hlt (j0 :: js) List.mem_cons_self j0 List.mem_cons_self)
        omega
      · have hne' : ∀ g ∈ grps, g ≠ [] := fun g hg => hne g (List.mem_cons_of_mem _ hg)
        have hlt' : ∀ g ∈ grps, ∀ j ∈ g, j < base + js.length := fun g hg j hj => by
          have := hlt g (List.mem_cons_of_mem _ hg) j hj; omega
        have h2 := ih (base + js.length) hne' hlt' o ho
        omega

lemma orGroups_eval (base : ℕ) (grps : List (List ℕ)) (w : List Bool)
    (hw : w.length = base)
    (hne : ∀ grp ∈ grps, grp ≠ [])
    (hlt : ∀ grp ∈ grps, ∀ j ∈ grp, j < base) :
    ∀ k (hk : k < grps.length),
      (evalGates (orGroups base grps).1 w).getD ((orGroups base grps).2.getD k 0) false =
        (grps.getD k []).any (fun j => w.getD j false) := by
  induction grps generalizing base w with
  | nil => intro k hk; simp at hk
  | cons grp grps ih =>
    cases grp with
    | nil => exact absurd rfl (hne [] List.mem_cons_self)
    | cons j0 js =>
      intro k hk
      simp only [orGroups, evalGates_append]
      set r1 := orChainAcc base j0 js
      set w1 := evalGates r1.1 w
      have hw1 : w1.length = base + js.length := by
        rw [evalGates_length, hw, orChainAcc_length]
      have hj0 : j0 < base := hlt (j0 :: js) List.mem_cons_self j0 List.mem_cons_self
      have hjs : ∀ j ∈ js, j < base := fun j hj =>
        hlt (j0 :: js) List.mem_cons_self j (List.mem_cons_of_mem _ hj)
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.any_cons]
        have hout_lt : r1.2 < w1.length := by
          rw [hw1]; exact orChainAcc_out_lt base j0 js hj0
        rw [evalGates_getD_lt _ _ hout_lt]
        exact orChainAcc_eval base j0 js w hw hj0 hjs
      | succ k =>
        simp only [List.getD_cons_succ]
        have hk' : k < grps.length := by simp at hk; omega
        have hne' : ∀ g ∈ grps, g ≠ [] := fun g hg => hne g (List.mem_cons_of_mem _ hg)
        have hlt' : ∀ g ∈ grps, ∀ j ∈ g, j < base + js.length := fun g hg j hj => by
          have := hlt g (List.mem_cons_of_mem _ hg) j hj; omega
        rw [ih (base + js.length) w1 hw1 hne' hlt' k hk']
        apply any_congr_mem
        intro j hj
        have hmem : grps.getD k [] ∈ grps := by
          rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
        have hjlt : j < w.length := by rw [hw]; exact hlt _ (List.mem_cons_of_mem _ hmem) j hj
        exact evalGates_getD_lt _ _ hjlt

def th2Loop (base p t : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], t)
  | [wk] => ([gAnd p wk, gOr t base], base + 1)
  | wk :: wnext :: ws =>
    let res := th2Loop (base + 3) (base + 2) (base + 1) (wnext :: ws)
    (gAnd p wk :: gOr t base :: gOr p wk :: res.1, res.2)

def th2Gates (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [_] => ([], 0)
  | [w0, w1] => ([gAnd w0 w1], base)
  | w0 :: w1 :: w2 :: ws =>
    let res := th2Loop (base + 2) (base + 1) base (w2 :: ws)
    (gAnd w0 w1 :: gOr w0 w1 :: res.1, res.2)

lemma th2Loop_length (base p t : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (th2Loop base p t ws).1.length = 3 * ws.length - 1 := by
  induction ws generalizing base p t with
  | nil => exact absurd rfl hne
  | cons wk rest ih =>
    cases rest with
    | nil => simp [th2Loop]
    | cons wnext ws =>
      simp only [th2Loop, List.length_cons]
      have h := ih (base + 3) (base + 2) (base + 1) (List.cons_ne_nil _ _)
      simp only [List.length_cons] at h
      omega

lemma th2Gates_length (base : ℕ) (ws : List ℕ) (hm : 2 ≤ ws.length) :
    (th2Gates base ws).1.length = 3 * ws.length - 5 := by
  match ws with
  | [] => simp at hm
  | [_] => simp at hm
  | [w0, w1] => simp [th2Gates]
  | w0 :: w1 :: w2 :: ws =>
    simp only [th2Gates, List.length_cons]
    have h := th2Loop_length (base + 2) (base + 1) base (w2 :: ws) (List.cons_ne_nil _ _)
    simp only [List.length_cons] at h
    omega

lemma th2Loop_m2 (base p t : ℕ) (ws : List ℕ) :
    ∀ g ∈ (th2Loop base p t ws).1, IsM2Gate g := by
  induction ws generalizing base p t with
  | nil => intro g hg; simp [th2Loop] at hg
  | cons wk rest ih =>
    cases rest with
    | nil =>
      intro g hg
      simp only [th2Loop, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact isM2_gAnd _ _
      · exact isM2_gOr _ _
    | cons wnext ws =>
      intro g hg
      simp only [th2Loop, List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | hg
      · exact isM2_gAnd _ _
      · exact isM2_gOr _ _
      · exact isM2_gOr _ _
      · exact ih _ _ _ g hg

lemma th2Gates_m2 (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (th2Gates base ws).1, IsM2Gate g := by
  match ws with
  | [] => intro g hg; simp [th2Gates] at hg
  | [_] => intro g hg; simp [th2Gates] at hg
  | [w0, w1] =>
    intro g hg
    simp only [th2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact isM2_gAnd _ _
  | w0 :: w1 :: w2 :: ws =>
    intro g hg
    simp only [th2Gates, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact isM2_gAnd _ _
    · exact isM2_gOr _ _
    · exact th2Loop_m2 _ _ _ _ g hg

lemma th2Loop_out_lt (base p t : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (th2Loop base p t ws).2 < base + (th2Loop base p t ws).1.length := by
  induction ws generalizing base p t with
  | nil => exact absurd rfl hne
  | cons wk rest ih =>
    cases rest with
    | nil => simp [th2Loop]
    | cons wnext ws =>
      simp only [th2Loop, List.length_cons]
      have h := ih (base + 3) (base + 2) (base + 1) (List.cons_ne_nil _ _)
      omega

lemma th2Gates_out_lt (base : ℕ) (ws : List ℕ) (hm : 2 ≤ ws.length) :
    (th2Gates base ws).2 < base + (th2Gates base ws).1.length := by
  match ws with
  | [] => simp at hm
  | [_] => simp at hm
  | [w0, w1] => simp [th2Gates]
  | w0 :: w1 :: w2 :: ws =>
    simp only [th2Gates, List.length_cons]
    have h := th2Loop_out_lt (base + 2) (base + 1) base (w2 :: ws) (List.cons_ne_nil _ _)
    omega

def atLeastTwo (bs : List Bool) : Bool :=
  match bs with
  | [] => false
  | b :: rest => (b && rest.any id) || atLeastTwo rest

lemma atLeastTwo_eq_true_iff (bs : List Bool) :
    atLeastTwo bs = true ↔
      ∃ i j, i < j ∧ j < bs.length ∧ bs.getD i false = true ∧ bs.getD j false = true := by
  induction bs with
  | nil =>
    simp [atLeastTwo]
  | cons b rest ih =>
    simp only [atLeastTwo, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, id_eq, ih]
    constructor
    · rintro (⟨hb, ⟨x, hx, rfl⟩⟩ | ⟨i, j, hij, hj, hi, hje⟩)
      · rcases List.mem_iff_getElem.mp hx with ⟨j, hj, hxj⟩
        refine ⟨0, j + 1, Nat.zero_lt_succ j, by simp; omega, by simpa, ?_⟩
        simp only [List.getD_cons_succ, List.getD_eq_getElem _ _ hj, hxj]
      · exact ⟨i + 1, j + 1, by omega, by simp; omega, by simpa, by simpa⟩
    · rintro ⟨i, j, hij, hj, hi, hje⟩
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j =>
          left
          simp only [List.getD_cons_zero] at hi
          simp only [List.getD_cons_succ] at hje
          have hj' : j < rest.length := by simp at hj; omega
          rw [List.getD_eq_getElem _ _ hj'] at hje
          exact ⟨hi, true, hje ▸ List.getElem_mem hj', rfl⟩
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          right
          exact ⟨i, j, by omega, by simp at hj; omega, by simpa using hi, by simpa using hje⟩

lemma th2Loop_eval (base p t : ℕ) (ws : List ℕ) (w : List Bool)
    (hw : w.length = base) (hp : p < base) (ht : t < base)
    (hws : ∀ x ∈ ws, x < base) (hne : ws ≠ []) :
    (evalGates (th2Loop base p t ws).1 w).getD (th2Loop base p t ws).2 false =
      ((w.getD t false || (w.getD p false && ws.any (fun x => w.getD x false))) ||
        atLeastTwo (ws.map fun x => w.getD x false)) := by
  induction ws generalizing base p t w with
  | nil => exact absurd rfl hne
  | cons wk rest ih =>
    cases rest with
    | nil =>
      simp only [th2Loop, evalGates_cons, evalGates_nil, List.any_cons, List.any_nil,
        Bool.or_false, List.map_cons, List.map_nil, atLeastTwo, Bool.and_false, Bool.or_false]
      set w1 := step w (gAnd p wk)
      have hw1 : w1.length = base + 1 := by rw [step_length, hw]
      have hidx : base + 1 = w1.length := hw1.symm
      rw [hidx, step_gOr_val]
      have ht1 : w1.getD t false = w.getD t false := step_getD_lt (by omega)
      have hbase1 : w1.getD base false = (w.getD p false && w.getD wk false) := by
        rw [← hw]; exact step_gAnd_val w p wk
      rw [ht1, hbase1]
    | cons wnext ws =>
      simp only [th2Loop, evalGates_cons]
      set w1 := step w (gAnd p wk)
      set w2 := step w1 (gOr t base)
      set w3 := step w2 (gOr p wk)
      have hw1 : w1.length = base + 1 := by rw [step_length, hw]
      have hw2 : w2.length = base + 2 := by rw [step_length, hw1]
      have hw3 : w3.length = base + 3 := by rw [step_length, hw2]
      have hws' : ∀ x ∈ wnext :: ws, x < base + 3 := fun x hx => by
        have := hws x (List.mem_cons_of_mem _ hx); omega
      rw [ih (base + 3) (base + 2) (base + 1) w3 hw3 (by omega) (by omega) hws' (List.cons_ne_nil _ _)]
      have hval_a : w1.getD base false = (w.getD p false && w.getD wk false) := by
        rw [← hw]; exact step_gAnd_val w p wk
      have hval_t2 : w2.getD (base + 1) false = (w.getD t false || (w.getD p false && w.getD wk false)) := by
        have h1 : w2.getD (base + 1) false = (w1.getD t false || w1.getD base false) := by
          rw [← hw1]; exact step_gOr_val w1 t base
        rw [h1, step_getD_lt (by omega), hval_a]
      have hval_t3 : w3.getD (base + 1) false = (w.getD t false || (w.getD p false && w.getD wk false)) := by
        rw [step_getD_lt (by omega), hval_t2]
      have hwk_lt : wk < base := hws wk List.mem_cons_self
      have hval_p3 : w3.getD (base + 2) false = (w.getD p false || w.getD wk false) := by
        have h1 : w3.getD (base + 2) false = (w2.getD p false || w2.getD wk false) := by
          rw [← hw2]; exact step_gOr_val w2 p wk
        rw [h1, step_getD_lt (by omega), step_getD_lt (by omega),
          step_getD_lt (by omega), step_getD_lt (by omega)]
      have hrest_eq : ∀ x ∈ wnext :: ws, w3.getD x false = w.getD x false := fun x hx => by
        have hxlt : x < base := hws x (List.mem_cons_of_mem _ hx)
        rw [step_getD_lt (by omega), step_getD_lt (by omega), step_getD_lt (by omega)]
      have hany_eq : (wnext :: ws).any (fun x => w3.getD x false) =
          (wnext :: ws).any (fun x => w.getD x false) := any_congr_mem hrest_eq
      have hmap_eq : (wnext :: ws).map (fun x => w3.getD x false) =
          (wnext :: ws).map (fun x => w.getD x false) := List.map_congr_left hrest_eq
      rw [hval_t3, hval_p3, hany_eq, hmap_eq]
      simp only [List.any_cons, List.map_cons, atLeastTwo, id_eq]
      have hmap_any : (ws.map (fun x => w.getD x false)).any id =
          ws.any (fun x => w.getD x false) := by simp [List.any_map]
      rw [hmap_any]
      cases w.getD t false <;> cases w.getD p false <;> cases w.getD wk false <;>
        cases w.getD wnext false <;> cases ws.any (fun x => w.getD x false) <;>
        cases atLeastTwo (ws.map fun x => w.getD x false) <;> rfl

lemma th2Gates_eval (base : ℕ) (ws : List ℕ) (w : List Bool)
    (hw : w.length = base) (hm : 2 ≤ ws.length) (hws : ∀ x ∈ ws, x < base) :
    (evalGates (th2Gates base ws).1 w).getD (th2Gates base ws).2 false =
      atLeastTwo (ws.map fun x => w.getD x false) := by
  match ws with
  | [] => simp at hm
  | [_] => simp at hm
  | [w0, w1] =>
    simp only [th2Gates, evalGates_cons, evalGates_nil, List.map_cons, List.map_nil,
      atLeastTwo, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.and_false]
    rw [← hw]; exact step_gAnd_val w w0 w1
  | w0 :: w1 :: w2 :: ws =>
    simp only [th2Gates, evalGates_cons]
    set wA := step w (gAnd w0 w1)
    set wB := step wA (gOr w0 w1)
    have hwA : wA.length = base + 1 := by rw [step_length, hw]
    have hwB : wB.length = base + 2 := by rw [step_length, hwA]
    have hws' : ∀ x ∈ w2 :: ws, x < base + 2 := fun x hx => by
      have := hws x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)); omega
    rw [th2Loop_eval (base + 2) (base + 1) base (w2 :: ws) wB hwB (by omega) (by omega) hws' (List.cons_ne_nil _ _)]
    have hw0_lt : w0 < base := hws w0 List.mem_cons_self
    have hw1_lt : w1 < base := hws w1 (List.mem_cons_of_mem _ List.mem_cons_self)
    have ht0 : wB.getD base false = (w.getD w0 false && w.getD w1 false) := by
      rw [step_getD_lt (by omega), ← hw]; exact step_gAnd_val w w0 w1
    have hp0 : wB.getD (base + 1) false = (w.getD w0 false || w.getD w1 false) := by
      have h1 : wB.getD (base + 1) false = (wA.getD w0 false || wA.getD w1 false) := by
        rw [← hwA]; exact step_gOr_val wA w0 w1
      rw [h1, step_getD_lt (by omega), step_getD_lt (by omega)]
    have hrest_eq : ∀ x ∈ w2 :: ws, wB.getD x false = w.getD x false := fun x hx => by
      have hxlt : x < base := hws x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      rw [step_getD_lt (by omega), step_getD_lt (by omega)]
    have hany_eq : (w2 :: ws).any (fun x => wB.getD x false) =
        (w2 :: ws).any (fun x => w.getD x false) := any_congr_mem hrest_eq
    have hmap_eq : (w2 :: ws).map (fun x => wB.getD x false) =
        (w2 :: ws).map (fun x => w.getD x false) := List.map_congr_left hrest_eq
    rw [ht0, hp0, hany_eq, hmap_eq]
    simp only [List.any_cons, List.map_cons, atLeastTwo, id_eq]
    have hmap_any : (ws.map (fun x => w.getD x false)).any id =
        ws.any (fun x => w.getD x false) := by simp [List.any_map]
    rw [hmap_any]
    cases w.getD w0 false <;> cases w.getD w1 false <;> cases w.getD w2 false <;>
      cases ws.any (fun x => w.getD x false) <;>
      cases atLeastTwo (ws.map fun x => w.getD x false) <;> rfl

def rowGroup (n c a : ℕ) : List ℕ :=
  ((List.range n).filter fun i => decide (i / c = a)).map fun i => 2 * n + i

def colGroup (n c b : ℕ) : List ℕ :=
  ((List.range n).filter fun i => decide (i % c = b)).map fun i => 2 * n + i

def rowGroups (n r c : ℕ) : List (List ℕ) :=
  (List.range r).map fun a => rowGroup n c a

def colGroups (n c : ℕ) : List (List ℕ) :=
  (List.range c).map fun b => colGroup n c b

lemma sum_one_at (m v : ℕ) (hv : v < m) :
    ((List.range m).map fun k => if v = k then 1 else 0).sum = 1 := by
  induction m with
  | zero => omega
  | succ m ihm =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    by_cases heq : v = m
    · have hzero : ((List.range m).map fun k => if v = k then 1 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro u hu
        simp only [List.mem_map, List.mem_range] at hu
        rcases hu with ⟨k, hk, rfl⟩
        simp [show v ≠ k by omega]
      rw [hzero, heq]; simp
    · simp [heq, ihm (by omega)]

lemma sum_filter_partition (l : List ℕ) (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ x ∈ l, f x < m) :
    ((List.range m).map fun k => (l.filter fun x => decide (f x = k)).length).sum = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hfx : f x < m := hf x List.mem_cons_self
    have hfxs : ∀ y ∈ xs, f y < m := fun y hy => hf y (List.mem_cons_of_mem _ hy)
    have hih := ih hfxs
    have hstep : ∀ (k : ℕ),
        ((x :: xs).filter fun y => decide (f y = k)).length =
          (xs.filter fun y => decide (f y = k)).length + (if f x = k then 1 else 0) := by
      intro k
      simp only [List.filter_cons]
      split <;> simp_all
    have hmap : ((List.range m).map fun k => ((x :: xs).filter fun y => decide (f y = k)).length) =
        ((List.range m).map fun k =>
          (xs.filter fun y => decide (f y = k)).length + (if f x = k then 1 else 0)) := by
      apply List.map_congr_left
      intro k _
      exact hstep k
    rw [hmap]
    have hsum_add : ∀ (ks : List ℕ) (g1 g2 : ℕ → ℕ),
        (ks.map fun k => g1 k + g2 k).sum = (ks.map g1).sum + (ks.map g2).sum := by
      intro ks g1 g2
      induction ks with
      | nil => simp
      | cons k ks ihk => simp [ihk]; omega
    rw [hsum_add, hih, sum_one_at m (f x) hfx]
    simp

lemma rowGroups_sum_length (n r c : ℕ) (hrc : n ≤ r * c) :
    ((rowGroups n r c).map List.length).sum = n := by
  have hmap : (rowGroups n r c).map List.length =
      (List.range r).map fun a => ((List.range n).filter fun i => decide (i / c = a)).length := by
    simp [rowGroups, rowGroup, List.map_map, Function.comp_def]
  rw [hmap]
  have h := sum_filter_partition (List.range n) (fun i => i / c) r (fun i hi => by
    simp only [List.mem_range] at hi
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega))
  simpa using h

lemma colGroups_sum_length (n c : ℕ) (hc : 0 < c) :
    ((colGroups n c).map List.length).sum = n := by
  have hmap : (colGroups n c).map List.length =
      (List.range c).map fun b => ((List.range n).filter fun i => decide (i % c = b)).length := by
    simp [colGroups, colGroup, List.map_map, Function.comp_def]
  rw [hmap]
  have h := sum_filter_partition (List.range n) (fun i => i % c) c (fun i _ => Nat.mod_lt i hc)
  simpa using h

lemma rowGroups_nonempty (n r c : ℕ) (hc : 0 < c) (hrm : (r - 1) * c < n) :
    ∀ grp ∈ rowGroups n r c, grp ≠ [] := by
  intro grp hgrp
  simp only [rowGroups, List.mem_map, List.mem_range] at hgrp
  rcases hgrp with ⟨a, ha, rfl⟩
  intro hemp
  have hmem : a * c ∈ (List.range n).filter (fun i => decide (i / c = a)) := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨?_, by simp [Nat.mul_div_cancel a hc]⟩
    have ha1 : a ≤ r - 1 := by omega
    have := Nat.mul_le_mul_right c ha1
    omega
  have : 2 * n + a * c ∈ rowGroup n c a := List.mem_map.mpr ⟨a * c, hmem, rfl⟩
  rw [hemp] at this
  exact List.not_mem_nil this

lemma colGroups_nonempty (n c : ℕ) (hcn : c ≤ n) :
    ∀ grp ∈ colGroups n c, grp ≠ [] := by
  intro grp hgrp
  simp only [colGroups, List.mem_map, List.mem_range] at hgrp
  rcases hgrp with ⟨b, hb, rfl⟩
  intro hemp
  have hmem : b ∈ (List.range n).filter (fun i => decide (i % c = b)) := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨by omega, by simp [Nat.mod_eq_of_lt hb]⟩
  have : 2 * n + b ∈ colGroup n c b := List.mem_map.mpr ⟨b, hmem, rfl⟩
  rw [hemp] at this
  exact List.not_mem_nil this

def cVal (n : ℕ) : ℕ := Nat.sqrt (n - 1) + 1
def rVal (n : ℕ) : ℕ := (n + cVal n - 1) / cVal n

def crownCircuit (n : ℕ) : Circuit :=
  let c := cVal n
  let r := rVal n
  let gs1 := zGates n
  let b1 := 3 * n
  let resR := orGroups b1 (rowGroups n r c)
  let b2 := b1 + resR.1.length
  let resC := orGroups b2 (colGroups n c)
  let b3 := b2 + resC.1.length
  let resTR := th2Gates b3 resR.2
  let b4 := b3 + resTR.1.length
  let resTC := th2Gates b4 resC.2
  let b5 := b4 + resTC.1.length
  { gates := gs1 ++ resR.1 ++ resC.1 ++ resTR.1 ++ resTC.1 ++ [gOr resTR.2 resTC.2]
    output := b5 }

lemma crown_params (n : ℕ) (hn : 4 ≤ n) :
    2 ≤ cVal n ∧ 2 ≤ rVal n ∧ rVal n ≤ cVal n ∧ cVal n ≤ n ∧
      n ≤ rVal n * cVal n ∧ (rVal n - 1) * cVal n < n := by
  have hc_pos : 0 < cVal n := Nat.succ_pos _
  have hsq_le : (Nat.sqrt (n - 1)) * (Nat.sqrt (n - 1)) ≤ n - 1 := Nat.sqrt_le (n - 1)
  have hsq_gt : n - 1 < cVal n * cVal n := Nat.lt_succ_sqrt (n - 1)
  have hc2 : 2 ≤ cVal n := by
    have h1 : 1 ≤ Nat.sqrt (n - 1) := by
      have : 1 * 1 ≤ n - 1 := by omega
      exact Nat.le_sqrt.mpr this
    unfold cVal; omega
  have hcn : cVal n ≤ n := by
    have : Nat.sqrt (n - 1) ≤ n - 1 := Nat.sqrt_le_self (n - 1)
    unfold cVal; omega
  have hrc : n ≤ rVal n * cVal n := by
    have hdiv := Nat.div_add_mod (n + cVal n - 1) (cVal n)
    have hmod := Nat.mod_lt (n + cVal n - 1) hc_pos
    change cVal n * rVal n + (n + cVal n - 1) % cVal n = n + cVal n - 1 at hdiv
    rw [Nat.mul_comm] at hdiv
    omega
  have hr_pos : 0 < rVal n := by
    unfold rVal
    exact Nat.div_pos (by omega) hc_pos
  have hrm : (rVal n - 1) * cVal n < n := by
    have hdiv : rVal n * cVal n ≤ n + cVal n - 1 := Nat.div_mul_le_self (n + cVal n - 1) (cVal n)
    have hsub : (rVal n - 1) * cVal n + cVal n = rVal n * cVal n := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr_pos]
    omega
  have hr_le_c : rVal n ≤ cVal n := by
    have h1 : n + cVal n - 1 < (cVal n + 1) * cVal n := by
      have : (cVal n + 1) * cVal n = cVal n * cVal n + cVal n := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : rVal n < cVal n + 1 :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
    omega
  have hr2 : 2 ≤ rVal n := by
    have hcltn : cVal n < n := by
      by_cases hc2' : cVal n = 2
      · omega
      · have hs : 2 ≤ Nat.sqrt (n - 1) := by unfold cVal at hc2' hc2; omega
        have : 2 * Nat.sqrt (n - 1) ≤ Nat.sqrt (n - 1) * Nat.sqrt (n - 1) :=
          Nat.mul_le_mul_right _ hs
        unfold cVal; omega
    have h1 : 2 * cVal n ≤ n + cVal n - 1 := by omega
    unfold rVal
    exact (Nat.le_div_iff_mul_le hc_pos).mpr h1
  exact ⟨hc2, hr2, hr_le_c, hcn, hrc, hrm⟩

lemma crownCircuit_m2 (n : ℕ) : Monotone2 (crownCircuit n) := by
  intro g hg
  simp only [crownCircuit, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  have h : IsM2Gate g := by
    rcases hg with ((((hg | hg) | hg) | hg) | hg) | rfl
    · exact zGates_m2 n g hg
    · exact orGroups_m2 _ _ g hg
    · exact orGroups_m2 _ _ g hg
    · exact th2Gates_m2 _ _ g hg
    · exact th2Gates_m2 _ _ g hg
    · exact isM2_gOr _ _
  exact h

lemma crownCircuit_size (n : ℕ) (hn : 4 ≤ n) :
    (crownCircuit n).size ≤ 3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9 := by
  obtain ⟨hc2, hr2, hr_le_c, hcn, hrc, hrm⟩ := crown_params n hn
  set c := cVal n
  set r := rVal n
  have hc_pos : 0 < c := by omega
  have hr_ne := rowGroups_nonempty n r c hc_pos hrm
  have hc_ne := colGroups_nonempty n c hcn
  have hR_len : (orGroups (3 * n) (rowGroups n r c)).1.length + r = n := by
    have h1 := orGroups_length (3 * n) (rowGroups n r c) hr_ne
    have h2 := rowGroups_sum_length n r c hrc
    have h3 : (rowGroups n r c).length = r := by simp [rowGroups]
    omega
  have hR_outs : (orGroups (3 * n) (rowGroups n r c)).2.length = r := by
    rw [orGroups_outs_length _ _ hr_ne]; simp [rowGroups]
  set b2 := 3 * n + (orGroups (3 * n) (rowGroups n r c)).1.length
  have hC_len : (orGroups b2 (colGroups n c)).1.length + c = n := by
    have h1 := orGroups_length b2 (colGroups n c) hc_ne
    have h2 := colGroups_sum_length n c hc_pos
    have h3 : (colGroups n c).length = c := by simp [colGroups]
    omega
  have hC_outs : (orGroups b2 (colGroups n c)).2.length = c := by
    rw [orGroups_outs_length _ _ hc_ne]; simp [colGroups]
  set b3 := b2 + (orGroups b2 (colGroups n c)).1.length
  have hTR_len : (th2Gates b3 (orGroups (3 * n) (rowGroups n r c)).2).1.length = 3 * r - 5 := by
    rw [th2Gates_length _ _ (by omega), hR_outs]
  set b4 := b3 + (th2Gates b3 (orGroups (3 * n) (rowGroups n r c)).2).1.length
  have hTC_len : (th2Gates b4 (orGroups b2 (colGroups n c)).2).1.length = 3 * c - 5 := by
    rw [th2Gates_length _ _ (by omega), hC_outs]
  unfold Circuit.size crownCircuit
  simp only [List.length_append, List.length_singleton, zGates_length]
  change n + (orGroups (3 * n) (rowGroups n r c)).1.length +
      (orGroups b2 (colGroups n c)).1.length +
      (th2Gates b3 (orGroups (3 * n) (rowGroups n r c)).2).1.length +
      (th2Gates b4 (orGroups b2 (colGroups n c)).2).1.length + 1 ≤
    3 * n + 4 * c - 9
  omega

lemma crownCircuit_rep (n : ℕ) (hn : 4 ≤ n) :
    Represents (fun u v : Fin n => decide (u ≠ v)) (crownCircuit n) := by
  intro u v
  obtain ⟨hc2, hr2, hr_le_c, hcn, hrc, hrm⟩ := crown_params n hn
  set c := cVal n
  set r := rVal n
  have hc_pos : 0 < c := by omega
  have hr_ne := rowGroups_nonempty n r c hc_pos hrm
  have hc_ne := colGroups_nonempty n c hcn

  set x := oneEach u v
  have hx_len : x.length = 2 * n := by simp [x, oneEach]; omega
  set gs1 := zGates n
  set w1 := evalGates gs1 x
  have hw1_len : w1.length = 3 * n := by
    rw [evalGates_length, hx_len, zGates_length]; omega
  have hw1_z : ∀ i < n, w1.getD (2 * n + i) false = (decide (i = u.val) || decide (i = v.val)) :=
    fun i hi => zGates_eval n u v i hi

  set resR := orGroups (3 * n) (rowGroups n r c)
  set w2 := evalGates resR.1 w1
  have hw2_len : w2.length = 3 * n + resR.1.length := by rw [evalGates_length, hw1_len]
  have hR_lt : ∀ grp ∈ rowGroups n r c, ∀ j ∈ grp, j < 3 * n := by
    intro grp hgrp j hj
    simp only [rowGroups, List.mem_map] at hgrp
    rcases hgrp with ⟨a, _, rfl⟩
    simp only [rowGroup, List.mem_map, List.mem_filter, List.mem_range] at hj
    rcases hj with ⟨i, ⟨hi, _⟩, rfl⟩
    omega
  have hR_outs_len : resR.2.length = r := by rw [orGroups_outs_length _ _ hr_ne]; simp [rowGroups]
  have hR_outs_lt : ∀ o ∈ resR.2, o < 3 * n + resR.1.length :=
    orGroups_outs_lt (3 * n) (rowGroups n r c) hr_ne hR_lt
  have hw2_R : ∀ a (ha : a < r),
      w2.getD (resR.2.getD a 0) false = (decide (u.val / c = a) || decide (v.val / c = a)) := by
    intro a ha
    have ha' : a < (rowGroups n r c).length := by simp [rowGroups, ha]
    rw [orGroups_eval (3 * n) (rowGroups n r c) w1 hw1_len hr_ne hR_lt a ha']
    have hgrp : (rowGroups n r c).getD a [] = rowGroup n c a := by
      rw [List.getD_eq_getElem _ _ ha']
      simp [rowGroups]
    rw [hgrp]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hval⟩
      simp only [rowGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      rcases hj with ⟨i, ⟨hi, hidiv⟩, rfl⟩
      rw [hw1_z i hi] at hval
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hval
      rcases hval with rfl | rfl
      · left; exact hidiv
      · right; exact hidiv
    · rintro (hu | hv)
      · refine ⟨2 * n + u.val, ?_, ?_⟩
        · simp only [rowGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨u.val, ⟨u.isLt, hu⟩, rfl⟩
        · rw [hw1_z u.val u.isLt]; simp
      · refine ⟨2 * n + v.val, ?_, ?_⟩
        · simp only [rowGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨v.val, ⟨v.isLt, hv⟩, rfl⟩
        · rw [hw1_z v.val v.isLt]; simp

  set b2 := 3 * n + resR.1.length
  set resC := orGroups b2 (colGroups n c)
  set w3 := evalGates resC.1 w2
  have hw3_len : w3.length = b2 + resC.1.length := by rw [evalGates_length, hw2_len]
  have hC_lt : ∀ grp ∈ colGroups n c, ∀ j ∈ grp, j < b2 := by
    intro grp hgrp j hj
    simp only [colGroups, List.mem_map] at hgrp
    rcases hgrp with ⟨b, _, rfl⟩
    simp only [colGroup, List.mem_map, List.mem_filter, List.mem_range] at hj
    rcases hj with ⟨i, ⟨hi, _⟩, rfl⟩
    omega
  have hC_outs_len : resC.2.length = c := by rw [orGroups_outs_length _ _ hc_ne]; simp [colGroups]
  have hC_outs_lt : ∀ o ∈ resC.2, o < b2 + resC.1.length :=
    orGroups_outs_lt b2 (colGroups n c) hc_ne hC_lt
  have hw3_C : ∀ b (hb : b < c),
      w3.getD (resC.2.getD b 0) false = (decide (u.val % c = b) || decide (v.val % c = b)) := by
    intro b hb
    have hb' : b < (colGroups n c).length := by simp [colGroups, hb]
    rw [orGroups_eval b2 (colGroups n c) w2 hw2_len hc_ne hC_lt b hb']
    have hgrp : (colGroups n c).getD b [] = colGroup n c b := by
      rw [List.getD_eq_getElem _ _ hb']
      simp [colGroups]
    rw [hgrp]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hval⟩
      simp only [colGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      rcases hj with ⟨i, ⟨hi, himod⟩, rfl⟩
      rw [evalGates_getD_lt _ _ (by rw [hw1_len]; omega), hw1_z i hi] at hval
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hval
      rcases hval with rfl | rfl
      · left; exact himod
      · right; exact himod
    · rintro (hu | hv)
      · refine ⟨2 * n + u.val, ?_, ?_⟩
        · simp only [colGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨u.val, ⟨u.isLt, hu⟩, rfl⟩
        · rw [evalGates_getD_lt _ _ (by rw [hw1_len]; omega), hw1_z u.val u.isLt]; simp
      · refine ⟨2 * n + v.val, ?_, ?_⟩
        · simp only [colGroup, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨v.val, ⟨v.isLt, hv⟩, rfl⟩
        · rw [evalGates_getD_lt _ _ (by rw [hw1_len]; omega), hw1_z v.val v.isLt]; simp

  set b3 := b2 + resC.1.length
  set resTR := th2Gates b3 resR.2
  set w4 := evalGates resTR.1 w3
  have hw4_len : w4.length = b3 + resTR.1.length := by rw [evalGates_length, hw3_len]
  have hR_outs_lt3 : ∀ o ∈ resR.2, o < b3 := fun o ho => by
    have := hR_outs_lt o ho; omega
  have hw4_TR : w4.getD resTR.2 false = decide (u.val / c ≠ v.val / c) := by
    rw [th2Gates_eval b3 resR.2 w3 hw3_len (by omega) hR_outs_lt3]
    apply Bool.eq_iff_iff.mpr
    rw [atLeastTwo_eq_true_iff, decide_eq_true_eq]
    have hmap_len : (resR.2.map fun o => w3.getD o false).length = r := by
      simp [hR_outs_len]
    have hget : ∀ a (ha : a < r),
        (resR.2.map fun o => w3.getD o false).getD a false =
          (decide (u.val / c = a) || decide (v.val / c = a)) := by
      intro a ha
      have haR : a < resR.2.length := by omega
      rw [List.getD_eq_getElem _ _ (by simp [haR]), List.getElem_map]
      have hlt2 : resR.2[a] < w2.length := by
        rw [hw2_len]; exact hR_outs_lt _ (List.getElem_mem haR)
      rw [evalGates_getD_lt _ _ hlt2]
      have heq := hw2_R a ha
      rwa [List.getD_eq_getElem _ _ haR] at heq
    constructor
    · rintro ⟨a, b, hab, hbr, ha_t, hb_t⟩
      rw [hmap_len] at hbr
      rw [hget a (by omega)] at ha_t
      rw [hget b hbr] at hb_t
      simp only [Bool.or_eq_true, decide_eq_true_eq] at ha_t hb_t
      omega
    · intro hne
      have hu_lt : u.val / c < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hv_lt : v.val / c < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      by_cases hlt_uv : u.val / c < v.val / c
      · refine ⟨u.val / c, v.val / c, hlt_uv, by omega, ?_, ?_⟩
        · rw [hget _ hu_lt]; simp
        · rw [hget _ hv_lt]; simp
      · refine ⟨v.val / c, u.val / c, by omega, by omega, ?_, ?_⟩
        · rw [hget _ hv_lt]; simp
        · rw [hget _ hu_lt]; simp

  set b4 := b3 + resTR.1.length
  set resTC := th2Gates b4 resC.2
  set w5 := evalGates resTC.1 w4
  have hw5_len : w5.length = b4 + resTC.1.length := by rw [evalGates_length, hw4_len]
  have hC_outs_lt4 : ∀ o ∈ resC.2, o < b4 := fun o ho => by
    have := hC_outs_lt o ho; omega
  have hw5_TC : w5.getD resTC.2 false = decide (u.val % c ≠ v.val % c) := by
    rw [th2Gates_eval b4 resC.2 w4 hw4_len (by omega) hC_outs_lt4]
    apply Bool.eq_iff_iff.mpr
    rw [atLeastTwo_eq_true_iff, decide_eq_true_eq]
    have hmap_len : (resC.2.map fun o => w4.getD o false).length = c := by
      simp [hC_outs_len]
    have hget : ∀ b (hb : b < c),
        (resC.2.map fun o => w4.getD o false).getD b false =
          (decide (u.val % c = b) || decide (v.val % c = b)) := by
      intro b hb
      have hbC : b < resC.2.length := by omega
      rw [List.getD_eq_getElem _ _ (by simp [hbC]), List.getElem_map]
      have hlt3 : resC.2[b] < w3.length := by
        rw [hw3_len]; exact hC_outs_lt _ (List.getElem_mem hbC)
      rw [evalGates_getD_lt _ _ hlt3]
      have heq := hw3_C b hb
      rwa [List.getD_eq_getElem _ _ hbC] at heq
    constructor
    · rintro ⟨a, b, hab, hbc, ha_t, hb_t⟩
      rw [hmap_len] at hbc
      rw [hget a (by omega)] at ha_t
      rw [hget b hbc] at hb_t
      simp only [Bool.or_eq_true, decide_eq_true_eq] at ha_t hb_t
      omega
    · intro hne
      have hu_lt : u.val % c < c := Nat.mod_lt u.val hc_pos
      have hv_lt : v.val % c < c := Nat.mod_lt v.val hc_pos
      by_cases hlt_uv : u.val % c < v.val % c
      · refine ⟨u.val % c, v.val % c, hlt_uv, by omega, ?_, ?_⟩
        · rw [hget _ hu_lt]; simp
        · rw [hget _ hv_lt]; simp
      · refine ⟨v.val % c, u.val % c, by omega, by omega, ?_, ?_⟩
        · rw [hget _ hv_lt]; simp
        · rw [hget _ hu_lt]; simp

  have hw5_TR : w5.getD resTR.2 false = decide (u.val / c ≠ v.val / c) := by
    have htr_lt : resTR.2 < w4.length := by
      rw [hw4_len]; exact th2Gates_out_lt b3 resR.2 (by omega)
    rw [evalGates_getD_lt _ _ htr_lt, hw4_TR]

  rw [Circuit.eval, wires_eq_evalGates]
  change (evalGates (gs1 ++ resR.1 ++ resC.1 ++ resTR.1 ++ resTC.1 ++ [gOr resTR.2 resTC.2]) x).getD
      (b4 + resTC.1.length) false = decide (u ≠ v)
  rw [evalGates_append, evalGates_append, evalGates_append, evalGates_append, evalGates_append]
  rw [evalGates_cons, evalGates_nil]
  have hidx : b4 + resTC.1.length = w5.length := hw5_len.symm
  rw [hidx, step_gOr_val, hw5_TR, hw5_TC]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq, Fin.ext_iff]
  constructor
  · rintro (h | h) heq <;> exact h (by rw [heq])
  · intro hne
    by_cases hd : u.val / c = v.val / c
    · right
      intro hm
      have hu := Nat.div_add_mod u.val c
      have hv := Nat.div_add_mod v.val c
      rw [hd, hm] at hu
      omega
    · left; exact hd

end PEqualNP.Outside.L_meta_19062_aux

theorem PEqualNP.Outside.L_meta_19062 :
    ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_19062_aux.crownCircuit n,
    PEqualNP.Outside.L_meta_19062_aux.crownCircuit_m2 n,
    PEqualNP.Outside.L_meta_19062_aux.crownCircuit_size n hn,
    PEqualNP.Outside.L_meta_19062_aux.crownCircuit_rep n hn⟩
