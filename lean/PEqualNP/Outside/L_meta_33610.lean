import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33610

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Credit: wiresFrom lemmas below are copied from PEqualNP.MetaComplexity.Helpers
-- (Shannon), inlined because that module is not built here.

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc {α : Type} (V : List α) (e d : α) (i : ℕ) :
    (V ++ [e]).getD i d = if i = V.length then e else V.getD i d := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-! ## Propagating a constant false wire -/

/-- What a gate becomes when its renamed inputs are `ins` and `Z` is the false wire:
`some u` when it is the copy of new wire `u` (or false, `u = Z`), `none` when it stays. -/
def elim (Z : ℕ) (g : Gate) (ins : List ℕ) : Option ℕ :=
  if Z ∈ ins then
    (match g.op with
     | GateOp.and => some Z
     | GateOp.or =>
       (if (ins.filter fun u => u != Z).length ≤ 1 then
          some ((ins.filter fun u => u != Z).headD Z) else none)
     | _ => none)
  else none

/-- One gate of the restriction: new gates, and the new name of every old wire. -/
def step (n Z : ℕ) (s : List Gate × List ℕ) (g : Gate) : List Gate × List ℕ :=
  match elim Z g (g.inputs.map fun w => s.2.getD w Z) with
  | some u => (s.1, s.2 ++ [u])
  | none => (s.1 ++ [⟨g.op, g.inputs.map fun w => s.2.getD w Z⟩], s.2 ++ [n + s.1.length])

/-- The names of the input wires: input `a` is the false wire. -/
def tab0 (n a Z : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (n + 1) => if i.val < a then i.val else if i.val = a then Z else i.val - 1

def run (n a Z : ℕ) (gs : List Gate) : List Gate × List ℕ := gs.foldl (step n Z) ([], tab0 n a Z)

theorem run_snoc (n a Z : ℕ) (gs : List Gate) (g : Gate) :
    run n a Z (gs ++ [g]) = step n Z (run n a Z gs) g := by
  simp [run, List.foldl_append]

theorem any_filter (f : ℕ → Bool) (Z : ℕ) (hZ : f Z = false) (l : List ℕ) :
    (l.map f).any id = ((l.filter fun u => u != Z).map f).any id := by
  induction l with
  | nil => simp
  | cons u l ih =>
    by_cases h : u = Z
    · subst h; simp [hZ, ih]
    · simp [h, ih]

theorem any_short (f : ℕ → Bool) (Z : ℕ) (hZ : f Z = false) (l : List ℕ) (hl : l.length ≤ 1) :
    (l.map f).any id = f (l.headD Z) := by
  match l, hl with
  | [], _ => simp [hZ]
  | [u], _ => simp

theorem elim_val (Z : ℕ) (g : Gate) (ins : List ℕ) (u : ℕ) (h : elim Z g ins = some u)
    (f : ℕ → Bool) (hZ : f Z = false) : g.op.eval (ins.map f) = f u := by
  unfold elim at h
  by_cases h1 : Z ∈ ins
  · rw [if_pos h1] at h
    split at h
    · rename_i hop
      cases h
      rw [hZ, hop]
      simp only [GateOp.eval, Bool.eq_false_iff, ne_eq, List.all_eq_true, List.mem_map, id,
        not_forall]
      exact ⟨false, ⟨Z, h1, hZ⟩, by simp⟩
    · rename_i hop
      by_cases h4 : (ins.filter fun u => u != Z).length ≤ 1
      · rw [if_pos h4] at h
        cases h
        rw [hop]
        simp only [GateOp.eval]
        rw [any_filter f Z hZ, any_short f Z hZ _ h4]
      · rw [if_neg h4] at h; cases h
    · cases h
  · rw [if_neg h1] at h; cases h

/-- The invariant of the restriction. -/
theorem inv (n a Z : ℕ) (x y : List Bool) (hx : x.length = n + 1) (hy : y.length = n)
    (hxa : x.getD a false = false) (hlo : ∀ i, i < a → x.getD i false = y.getD i false)
    (hhi : ∀ i, a < i → x.getD i false = y.getD (i - 1) false) (ha : a < n + 1) :
    ∀ gs : List Gate, n + gs.length ≤ Z →
      (run n a Z gs).2.length = n + 1 + gs.length ∧
      (run n a Z gs).1.length ≤ gs.length ∧
      (∀ w, (run n a Z gs).2.getD w Z = Z ∨ (run n a Z gs).2.getD w Z < n + (run n a Z gs).1.length) ∧
      (∀ w, (wiresFrom (run n a Z gs).1 y).getD ((run n a Z gs).2.getD w Z) false
        = (wiresFrom gs x).getD w false) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro hZ
    simp only [List.length_nil, add_zero]
    have hrun : run n a Z [] = ([], tab0 n a Z) := rfl
    have ht : ∀ w, (tab0 n a Z).getD w Z =
        if w < n + 1 then (if w < a then w else if w = a then Z else w - 1) else Z := by
      intro w
      unfold tab0
      by_cases h : w < n + 1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [h]
      · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]
    rw [hrun]
    refine ⟨by simp [tab0], by simp, ?_, ?_⟩
    · intro w
      rw [ht]
      split_ifs <;> simp <;> omega
    · intro w
      rw [ht]
      show y.getD _ false = x.getD w false
      split_ifs with h1 h2 h3
      · exact (hlo w h2).symm
      · subst h3; rw [hxa]; exact List.getD_eq_default _ _ (by omega)
      · exact (hhi w (by omega)).symm
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro hZ
    simp only [List.length_append, List.length_singleton] at hZ ⊢
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [run_snoc]
    set R := run n a Z gs with hR
    have hW : (wiresFrom R.1 y).length = n + R.1.length := by rw [length_wiresFrom, hy]
    have hZf : (wiresFrom R.1 y).getD Z false = false :=
      List.getD_eq_default _ _ (by omega)
    have hins : g.op.eval ((g.inputs.map fun w => R.2.getD w Z).map
        fun i => (wiresFrom R.1 y).getD i false)
        = g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro w _
      exact h4 w
    have hold : ∀ w, (wiresFrom (gs ++ [g]) x).getD w false =
        if w = n + 1 + gs.length then g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)
        else (wiresFrom gs x).getD w false := by
      intro w
      rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, hx]
    unfold step
    split
    · rename_i u hu
      simp only
      refine ⟨by simp [h1]; omega, by omega, ?_, ?_⟩
      · intro w
        rw [getD_snoc]
        split_ifs
        · unfold elim at hu
          by_cases e1 : Z ∈ g.inputs.map fun w => R.2.getD w Z
          swap
          · rw [if_neg e1] at hu; cases hu
          rw [if_pos e1] at hu
          split at hu
          · cases hu; left; rfl
          · by_cases e4 : ((g.inputs.map fun w => R.2.getD w Z).filter fun u => u != Z).length ≤ 1
            swap
            · rw [if_neg e4] at hu; cases hu
            rw [if_pos e4] at hu
            cases hu
            cases hf : (List.filter (fun u => u != Z) (g.inputs.map fun w => R.2.getD w Z)) with
            | nil => left; simp
            | cons v l =>
              have hv : v ∈ List.filter (fun u => u != Z) (g.inputs.map fun w => R.2.getD w Z) := by
                rw [hf]; simp
              rw [List.mem_filter, List.mem_map] at hv
              obtain ⟨⟨w', _, hw'⟩, _⟩ := hv
              simp only [List.headD_cons]
              rw [← hw']; exact h3 w'
          · cases hu
        · exact h3 w
      · intro w
        rw [getD_snoc, hold, h1]
        split_ifs with e
        · rw [← hins, elim_val Z g _ u hu _ hZf]
        · exact h4 w
    · rename_i hu
      simp only
      refine ⟨by simp [h1]; omega, by simp; omega, ?_, ?_⟩
      · intro w
        rw [getD_snoc]
        simp only [List.length_append, List.length_singleton]
        split_ifs
        · right; omega
        · rcases h3 w with e | e
          · left; exact e
          · right; omega
      · intro w
        rw [getD_snoc, hold, h1, wiresFrom_snoc]
        split_ifs with e
        · rw [getD_snoc, if_pos hW.symm, ← hins]
        · rw [getD_snoc, if_neg]
          · exact h4 w
          · rcases h3 w with e' | e' <;> omega

/-! ## Bookkeeping of the restriction -/

def dg : Gate := ⟨GateOp.or, []⟩

theorem fold_ext (n Z : ℕ) : ∀ (l : List Gate) (s : List Gate × List ℕ),
    ∃ t, (l.foldl (step n Z) s).2 = s.2 ++ t := by
  intro l
  induction l with
  | nil => intro s; exact ⟨[], by simp⟩
  | cons g l ih =>
    intro s
    obtain ⟨t, ht⟩ := ih (step n Z s g)
    simp only [List.foldl_cons]
    rw [ht]
    unfold step
    split
    · rename_i u _
      exact ⟨u :: t, by simp⟩
    · exact ⟨(n + s.1.length) :: t, by simp⟩

theorem run_len (n a Z : ℕ) (gs : List Gate) : (run n a Z gs).2.length = n + 1 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, tab0]
  | append_singleton gs g ih =>
    rw [run_snoc]
    unfold step
    split <;> simp [ih] <;> omega

theorem run_prefix (n a Z : ℕ) (gs : List Gate) (k : ℕ) (w : ℕ) (hw : w < n + 1 + k)
    (hk : k ≤ gs.length) :
    (run n a Z (gs.take k)).2.getD w Z = (run n a Z gs).2.getD w Z := by
  have e : run n a Z gs = (gs.drop k).foldl (step n Z) (run n a Z (gs.take k)) := by
    unfold run
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.foldl_append]
  obtain ⟨t, ht⟩ := fold_ext n Z (gs.drop k) (run n a Z (gs.take k))
  rw [e, ht, List.getD_append]
  rw [run_len, List.length_take]; omega

/-- The renamed inputs of gate `k`. -/
def insK (n a Z : ℕ) (gs : List Gate) (k : ℕ) : List ℕ :=
  (gs.getD k dg).inputs.map fun w => (run n a Z (gs.take k)).2.getD w Z

theorem take_succ' (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    gs.take (k + 1) = gs.take k ++ [gs.getD k dg] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem entry (n a Z : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) (u : ℕ)
    (h : elim Z (gs.getD k dg) (insK n a Z gs k) = some u) :
    (run n a Z gs).2.getD (n + 1 + k) Z = u := by
  rw [← run_prefix n a Z gs (k + 1) _ (by omega) (by omega), take_succ' gs k hk, run_snoc]
  unfold step
  unfold insK at h
  rw [h]
  simp only
  rw [getD_snoc, if_pos]
  rw [run_len, List.length_take]; omega

theorem count_elim (n a Z : ℕ) (gs : List Gate) :
    (run n a Z gs).1.length +
      ((Finset.range gs.length).filter fun k =>
        elim Z (gs.getD k dg) (insK n a Z gs k) ≠ none).card = gs.length := by
  classical
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    have hsame : ∀ k ∈ Finset.range gs.length,
        (elim Z ((gs ++ [g]).getD k dg) (insK n a Z (gs ++ [g]) k) ≠ none ↔
          elim Z (gs.getD k dg) (insK n a Z gs k) ≠ none) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : (gs ++ [g]).getD k dg = gs.getD k dg := List.getD_append _ _ _ _ hk
      have h2 : (gs ++ [g]).take k = gs.take k := List.take_append_of_le_length (by omega)
      unfold insK
      rw [h1, h2]
    have hlast : (gs ++ [g]).getD gs.length dg = g := by simp
    have hins : insK n a Z (gs ++ [g]) gs.length =
        g.inputs.map fun w => (run n a Z gs).2.getD w Z := by
      unfold insK
      rw [hlast, List.take_left' rfl]
    simp only [List.length_append, List.length_singleton]
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_congr hsame, run_snoc]
    rw [hlast, hins]
    unfold step
    split
    · rename_i u hu
      rw [if_pos (by rw [hu]; simp), Finset.card_insert_of_notMem (by simp)]
      simp only
      omega
    · rename_i hu
      rw [if_neg (by rw [hu]; simp)]
      simp only [List.length_append, List.length_singleton]
      omega

theorem filt_le (Z : ℕ) (l : List ℕ) (hl : l.length ≤ 2) (hZ : Z ∈ l) :
    (l.filter fun u => u != Z).length ≤ 1 := by
  match l, hl with
  | [], _ => simp at hZ
  | [u], _ => by_cases hu : u = Z <;> simp_all
  | [u, v], _ =>
    by_cases hu : u = Z <;> by_cases hv : v = Z <;> simp_all
    rcases hZ with h | h
    · exact hu h.symm
    · exact hv h.symm

/-- A gate of the monotone circuit that reads a false wire is eliminated. -/
theorem elim_of_read (n a Z : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hm : (gs.getD k dg).op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hl : (gs.getD k dg).inputs.length ≤ 2) (w : ℕ) (hw : w ∈ (gs.getD k dg).inputs)
    (hwk : w < n + 1 + k) (hT : (run n a Z gs).2.getD w Z = Z) :
    elim Z (gs.getD k dg) (insK n a Z gs k) ≠ none := by
  have hZ : Z ∈ insK n a Z gs k := by
    unfold insK
    rw [List.mem_map]
    exact ⟨w, hw, by rw [run_prefix n a Z gs k w hwk (by omega)]; exact hT⟩
  have hl' : (insK n a Z gs k).length ≤ 2 := by unfold insK; simpa using hl
  unfold elim
  rw [if_pos hZ]
  rcases hm with h | h
  · rw [h]; simp
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    simp only
    rw [if_pos (filt_le Z _ hl' hZ)]
    simp

/-- A gate reading only false wires becomes false. -/
theorem elim_all (n a Z : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hm : (gs.getD k dg).op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hne : (gs.getD k dg).inputs ≠ [])
    (hall : ∀ w ∈ (gs.getD k dg).inputs, w < n + 1 + k ∧ (run n a Z gs).2.getD w Z = Z) :
    (run n a Z gs).2.getD (n + 1 + k) Z = Z := by
  have hall' : ∀ v ∈ insK n a Z gs k, v = Z := by
    intro v hv
    unfold insK at hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [run_prefix n a Z gs k w (hall w hw).1 (by omega)]
    exact (hall w hw).2
  have hZ : Z ∈ insK n a Z gs k := by
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    apply (List.mem_map).2
    exact ⟨w, hw, by rw [run_prefix n a Z gs k w (hall w hw).1 (by omega)]; exact (hall w hw).2⟩
  have hf : (insK n a Z gs k).filter (fun u => u != Z) = [] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    simp [hall' v hv]
  apply entry n a Z gs k hk
  unfold elim
  rw [if_pos hZ]
  rcases hm with h | h
  · rw [h]
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    simp only
    rw [hf]
    simp

theorem run_gates (n a Z : ℕ) (gs : List Gate) : ∀ g' ∈ (run n a Z gs).1,
    ∃ g ∈ gs, g'.op = g.op ∧ g'.inputs.length = g.inputs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc]
    unfold step
    split
    · intro g' hg'
      obtain ⟨g0, h0, e⟩ := ih g' hg'
      exact ⟨g0, by simp [h0], e⟩
    · intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | hg'
      · obtain ⟨g0, h0, e⟩ := ih g' hg'
        exact ⟨g0, by simp [h0], e⟩
      · subst hg'
        exact ⟨g, by simp, rfl, by simp⟩

theorem tab0_a (n a Z : ℕ) (ha : a < n + 1) (gs : List Gate) :
    (run n a Z (gs.take 0)).2.getD a Z = Z := by
  simp only [List.take_zero]
  show (tab0 n a Z).getD a Z = Z
  unfold tab0
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [ha]

/-! ## Inputs -/

theorem ofFn_getD {m : ℕ} (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  by_cases h : i < m
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]

theorem countP_ofFn' {α : Type} {m : ℕ} (f : Fin m → α) (q : α → Bool) :
    (List.ofFn f).countP q = (Finset.univ.filter fun j => q (f j) = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    exact add_comm _ _

theorem cnt {m : ℕ} (f : Fin m → Bool) :
    (List.ofFn f).count true = (Finset.univ.filter fun j => f j = true).card := by
  rw [List.count, countP_ofFn']
  simp

/-- The old input for a new input `y`: input `a` set to false. -/
def ext (a n : ℕ) (y : Fin n → Bool) : Fin (n + 1) → Bool := fun i =>
  if i.val < a then (List.ofFn y).getD i.val false
  else if i.val = a then false else (List.ofFn y).getD (i.val - 1) false

theorem ext_list (a n : ℕ) (ha : a ≤ n) (y : Fin n → Bool) :
    List.ofFn (ext a n y) = (List.ofFn y).take a ++ false :: (List.ofFn y).drop a := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn]
    unfold ext
    simp only
    by_cases hi : i < a
    · rw [if_pos hi, List.getElem_append_left (by rw [List.length_take, List.length_ofFn]; omega),
        List.getElem_take,
        List.getD_eq_getElem _ _ (by simp; omega)]
    · rw [if_neg hi, List.getElem_append_right (by simp; omega)]
      simp only [List.length_take, List.length_ofFn]
      by_cases hia : i = a
      · rw [if_pos hia]
        have e : i - min a n = 0 := by omega
        simp only [e, List.getElem_cons_zero]
      · rw [if_neg hia]
        have e : i - min a n = (i - a - 1) + 1 := by omega
        simp only [e, List.getElem_cons_succ, List.getElem_drop]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        congr 1
        omega

theorem ext_count (a n : ℕ) (ha : a ≤ n) (y : Fin n → Bool) :
    (List.ofFn (ext a n y)).count true = (List.ofFn y).count true := by
  rw [ext_list a n ha, List.count_append, List.count_cons]
  conv_rhs => rw [← List.take_append_drop a (List.ofFn y)]
  rw [List.count_append]
  simp

/-- The values of the old circuit on `ext` inputs read the old wires. -/
theorem agree (a b : ℕ) (gs : List Gate) (h0 : gs.getD 0 dg = ⟨GateOp.and, [a, b]⟩)
    (hno : ∀ k, k < gs.length → k ≠ 0 → a ∉ (gs.getD k dg).inputs) (x1 x2 : List Bool)
    (hl : x1.length = x2.length) (hxa : ∀ w, w ≠ a → x1.getD w false = x2.getD w false)
    (hb1 : x1.getD a false = false ∨ x1.getD b false = false)
    (hb2 : x2.getD a false = false ∨ x2.getD b false = false) :
    ∀ m, m ≤ gs.length → ∀ w, w ≠ a →
      (wiresFrom (gs.take m) x1).getD w false = (wiresFrom (gs.take m) x2).getD w false := by
  intro m
  induction m with
  | zero => intro _ w hw; exact hxa w hw
  | succ m ih =>
    intro hm w hw
    rw [take_succ' gs m (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hl]
    split_ifs with e
    · by_cases hm0 : m = 0
      · subst hm0
        rw [h0]
        have e1 : ∀ x : List Bool, (x.getD a false = false ∨ x.getD b false = false) →
            (GateOp.and).eval ([a, b].map fun i => (wiresFrom (gs.take 0) x).getD i false)
              = false := by
          intro x hx
          simp only [List.take_zero]
          show (GateOp.and).eval [x.getD a false, x.getD b false] = false
          generalize x.getD a false = p at hx ⊢
          generalize x.getD b false = q at hx ⊢
          rcases hx with rfl | rfl <;> simp [GateOp.eval]
        rw [e1 x1 hb1, e1 x2 hb2]
      · congr 1
        apply List.map_congr_left
        intro w' hw'
        apply ih (by omega) w'
        intro hwa
        subst hwa
        exact hno m (by omega) hm0 hw'
    · exact ih (by omega) w hw

theorem two_of (l : List ℕ) (hl : l.length ≤ 2) (p q : ℕ) (hp : p ∈ l) (hq : q ∈ l)
    (hpq : p ≠ q) : ∀ w ∈ l, w = p ∨ w = q := by
  match l, hl with
  | [], _ => simp at hp
  | [u], _ => simp at hp hq; omega
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq ⊢
    omega

theorem getD_mem (gs : List Gate) (k : ℕ) (hk : k < gs.length) : gs.getD k dg ∈ gs := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _

end PEqualNP.Outside.L_meta_33610

open PEqualNP.Outside.L_meta_33610 in
theorem PEqualNP.Outside.L_meta_33610 : ∀ (n a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → PEqualNP.MetaComplexity.Monotone2 C → a < b → b < n + 1 → C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → C.output + 1 = (n + 1) + C.size → (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length → ∃ k : Fin C.gates.length, j.val < k.val ∧ (n + 1) + j.val ∈ (C.gates.get k).inputs) → (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + 3 ≤ C.size ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → D.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → D.eval (List.ofFn x) = false) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro n a b C hn hM hab hb hhead hout hread hP
  obtain ⟨hT, hF⟩ := hP
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at hout
  have hlen : 0 < C.gates.length ∧ C.gates.getD 0 dg = ⟨GateOp.and, [a, b]⟩ := by
    cases hg : C.gates with
    | nil => rw [hg] at hhead; simp at hhead
    | cons g0 rest =>
      rw [hg] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨by simp, by simp [hhead]⟩
  have hget : ∀ k : Fin C.gates.length, C.gates.get k = C.gates.getD k.val dg := by
    intro k; rw [List.get_eq_getElem, List.getD_eq_getElem]
  have hmono : ∀ k, k < C.gates.length →
      (C.gates.getD k dg).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        (C.gates.getD k dg).inputs.length ≤ 2 := fun k hk => hM _ (getD_mem _ k hk)
  set Z := n + C.gates.length with hZ
  set R := run n a Z C.gates with hR
  have hc : ∀ y : Fin n → Bool,
      (List.ofFn (ext a n y)).count true = (List.ofFn y).count true :=
    ext_count a n (by omega)
  have hinv := fun y : Fin n → Bool =>
    inv n a Z (List.ofFn (ext a n y)) (List.ofFn y) (by simp) (by simp)
      (by rw [ofFn_getD, dif_pos (by omega)]; simp [ext])
      (by intro i hi; rw [ofFn_getD, dif_pos (by omega)]; simp [ext, hi])
      (by
        intro i hi
        rw [ofFn_getD]
        split_ifs with h
        · have h1 : ¬ i < a := by omega
          have h2 : i ≠ a := by omega
          simp [ext, h1, h2]
        · rw [List.getD_eq_default _ _ (by simp; omega)])
      (by omega) C.gates le_rfl
  let D : Circuit := ⟨R.1, R.2.getD C.output Z⟩
  have htr : ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (ext a n y)) :=
    fun y => (hinv y).2.2.2 C.output
  -- a weight two input on `n` wires
  have hy0 : (List.ofFn fun i : Fin n => decide (i.val < 2)).count true = 2 := by
    rw [cnt]
    have : (Finset.univ.filter fun j : Fin n => decide (j.val < 2) = true)
        = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      ext j; simp [Fin.ext_iff]; omega
    rw [this, Finset.card_pair (by simp [Fin.ext_iff])]
  have hTo : R.2.getD C.output Z ≠ Z := by
    intro h
    have h1 := hT _ (by rw [hc]; exact hy0)
    rw [← htr] at h1
    have h2 : R.1.length ≤ C.gates.length := (hinv fun i : Fin n => decide (i.val < 2)).2.1
    have : D.eval (List.ofFn fun i : Fin n => decide (i.val < 2)) = false := by
      show (wiresFrom R.1 _).getD (R.2.getD C.output Z) false = false
      rw [h]
      apply List.getD_eq_default
      rw [length_wiresFrom]; simp; omega
    rw [this] at h1; exact absurd h1 (by simp)
  have hTa : R.2.getD a Z = Z := by
    rw [← run_prefix n a Z C.gates 0 a (by omega) (by omega)]
    exact tab0_a n a Z (by omega) C.gates
  have hT1 : R.2.getD (n + 1) Z = Z := by
    have := entry n a Z C.gates 0 hlen.1 Z (by
      unfold elim insK
      rw [hlen.2, if_pos]
      simp only [List.map_cons, List.map_nil, List.mem_cons]
      left; exact (tab0_a n a Z (by omega) C.gates).symm)
    simpa using this
  have h2 : 1 < C.gates.length := by
    by_contra h
    apply hTo
    have : C.output = n + 1 := by omega
    rw [this]
    exact hT1
  obtain ⟨r, hr0, hrr⟩ := hread ⟨0, hlen.1⟩ (by simp; omega)
  rw [hget] at hrr
  have hr0' : 0 < r.val := hr0
  -- some other gate reads input `a`
  have hh : ∃ k, k < C.gates.length ∧ k ≠ 0 ∧ a ∈ (C.gates.getD k dg).inputs := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hcx : ∃ c, c < n + 1 ∧ c ≠ a ∧ c ≠ b := by
      by_cases h0 : a = 0
      · by_cases h1 : b = 1
        · exact ⟨2, by omega, by omega, by omega⟩
        · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨0, by omega, by omega, by omega⟩
    obtain ⟨c, hc1, hca, hcb⟩ := hcx
    let f1 : Fin (n + 1) → Bool := fun i => decide (i.val = c)
    let f2 : Fin (n + 1) → Bool := fun i => decide (i.val = a ∨ i.val = c)
    have hc1' : (List.ofFn f1).count true = 1 := by
      rw [cnt]
      have : (Finset.univ.filter fun j => f1 j = true) = {⟨c, hc1⟩} := by
        ext j; simp [f1, Fin.ext_iff]
      rw [this, Finset.card_singleton]
    have hc2' : (List.ofFn f2).count true = 2 := by
      rw [cnt]
      have : (Finset.univ.filter fun j => f2 j = true) = {⟨a, by omega⟩, ⟨c, hc1⟩} := by
        ext j; simp [f2, Fin.ext_iff]
      rw [this, Finset.card_pair (by simp [Fin.ext_iff]; omega)]
    have hag := agree a b C.gates hlen.2 (fun k hk hk0 => hno k hk hk0) (List.ofFn f1)
      (List.ofFn f2) (by simp)
      (by
        intro w hw
        rw [ofFn_getD, ofFn_getD]
        split_ifs <;> simp [f1, f2, hw])
      (by left; rw [ofFn_getD, dif_pos (by omega)]; simp [f1]; omega)
      (by right; rw [ofFn_getD, dif_pos (by omega)]; simp [f2]; omega)
      C.gates.length le_rfl C.output (by omega)
    rw [List.take_of_length_le (le_refl _)] at hag
    have e1 := hF f1 (by omega)
    have e2 := hT f2 hc2'
    have : C.eval (List.ofFn f1) = C.eval (List.ofFn f2) := hag
    rw [this, e2] at e1
    exact absurd e1 (by simp)
  obtain ⟨h, hhl, hh0, hha⟩ := hh
  -- three eliminated gates
  have hS : R.1.length + ((Finset.range C.gates.length).filter fun k =>
      elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none).card = C.gates.length :=
    count_elim n a Z C.gates
  have hmem : ∀ k, k < C.gates.length → elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none →
      k ∈ (Finset.range C.gates.length).filter fun k =>
        elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none := by
    intro k hk he
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hk, he⟩
  have e0 := hmem 0 hlen.1 (elim_of_read n a Z C.gates 0 hlen.1 (hmono 0 hlen.1).1
    (hmono 0 hlen.1).2 a (by rw [hlen.2]; simp) (by omega) hTa)
  have eh := hmem h hhl (elim_of_read n a Z C.gates h hhl (hmono h hhl).1
    (hmono h hhl).2 a hha (by omega) hTa)
  have hthree : ∃ k, k < C.gates.length ∧ k ≠ 0 ∧ k ≠ h ∧
      elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none := by
    by_cases hhr : h = r
    · rw [← hhr] at hrr
      have hall : R.2.getD (n + 1 + h) Z = Z := by
        apply elim_all n a Z C.gates h hhl (hmono h hhl).1 (List.ne_nil_of_mem hha)
        intro w hw
        rcases two_of _ (hmono h hhl).2 a (n + 1) hha hrr (by omega) w hw with e | e
        · subst e; exact ⟨by omega, hTa⟩
        · subst e; exact ⟨by omega, hT1⟩
      have hh1 : h + 1 < C.gates.length := by
        by_contra hc
        apply hTo
        rw [show C.output = n + 1 + h by omega]
        exact hall
      obtain ⟨r2, hr2, hrr2⟩ := hread ⟨h, hhl⟩ hh1
      rw [hget] at hrr2
      have hr2' : h < r2.val := hr2
      exact ⟨r2, r2.2, by omega, by omega, elim_of_read n a Z C.gates r2 r2.2 (hmono r2 r2.2).1
        (hmono r2 r2.2).2 _ hrr2 (by omega) hall⟩
    · exact ⟨r, r.2, by omega, by omega, elim_of_read n a Z C.gates r r.2 (hmono r r.2).1
        (hmono r r.2).2 _ hrr (by omega) hT1⟩
  obtain ⟨k, hk, hk0, hkh, hke⟩ := hthree
  have ek := hmem k hk hke
  have hcard : 3 ≤ ((Finset.range C.gates.length).filter fun k =>
      elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none).card := by
    have hsub : ({0, h, k} : Finset ℕ) ⊆ (Finset.range C.gates.length).filter fun k =>
        elim Z (C.gates.getD k dg) (insK n a Z C.gates k) ≠ none := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact e0
      · exact eh
      · exact ek
    have := Finset.card_le_card hsub
    rw [Finset.card_eq_three.mpr ⟨0, h, k, by omega, by omega, by omega, rfl⟩] at this
    exact this
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, e1, e2⟩ := run_gates n a Z C.gates g' hg'
    rw [e1, e2]
    exact hM g hg
  · show R.1.length + 3 ≤ C.gates.length
    omega
  · intro y hy
    rw [htr]
    exact hT _ (by rw [hc]; exact hy)
  · intro y hy
    rw [htr]
    exact hF _ (by rw [hc]; exact hy)
