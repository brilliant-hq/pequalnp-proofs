import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24694_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
  PEqualNP.MetaComplexity.NestedCover

abbrev Signal := Sum Bool ℕ
abbrev Plan := Sum Signal Gate

def read (w : List Signal) (i : ℕ) : Signal := w.getD i (.inl false)

def value (w : List Bool) : Signal → Bool
  | .inl b => b
  | .inr i => w.getD i false

def compute (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [compute w g]

def reduced (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)

def activeInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def reads (C : Circuit) (i : ℕ) : Prop :=
  (∃ g ∈ C.gates, i ∈ activeInputs g) ∨ C.output = i

def lists (C : Circuit) (i : ℕ) : Prop :=
  (∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i

theorem active_iff {g : Gate} {i : ℕ}
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    i ∈ activeInputs g ↔
      ((g.op = .and ∨ g.op = .or) ∧ i ∈ g.inputs) ∨
        (g.op = .not ∧ g.inputs.head? = some i) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with e | e | e <;> change op = _ at e <;> subst op <;>
    cases ins <;> simp [activeInputs, eq_comm]

theorem active_eval (w : List Bool) (g : Gate) :
    g.op.eval ((activeInputs g).map fun i => w.getD i false) = compute w g := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> rfl

theorem active_length (g : Gate) (h : g.inputs.length ≤ 2) :
    (activeInputs g).length ≤ 2 ∧ (g.op = .not → (activeInputs g).length ≤ 1) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [activeInputs] at h ⊢ <;> omega

def andPlan : Signal → Signal → Plan
  | .inl false, _ => .inl (.inl false)
  | .inl true, y => .inl y
  | _, .inl false => .inl (.inl false)
  | x, .inl true => .inl x
  | .inr i, .inr j => .inr ⟨.and, [i, j]⟩

def orPlan : Signal → Signal → Plan
  | .inl true, _ => .inl (.inl true)
  | .inl false, y => .inl y
  | _, .inl true => .inl (.inl true)
  | x, .inl false => .inl x
  | .inr i, .inr j => .inr ⟨.or, [i, j]⟩

def plan : GateOp → List Signal → Plan
  | .and, [] => .inl (.inl true)
  | .and, [x] => .inl x
  | .and, [x, y] => andPlan x y
  | .or, [] => .inl (.inl false)
  | .or, [x] => .inl x
  | .or, [x, y] => orPlan x y
  | .not, [] => .inl (.inl true)
  | .not, [.inl b] => .inl (.inl (!b))
  | .not, [.inr i] => .inr ⟨.not, [i]⟩
  | _, _ => .inl (.inl false)

def planValue (w : List Bool) : Plan → Bool
  | .inl s => value w s
  | .inr g => compute w g

def planShape (op : GateOp) (xs : List Signal) : Plan → Prop
  | .inl (.inl _) => True
  | .inl (.inr i) => Sum.inr i ∈ xs
  | .inr g => reduced g ∧ g.op = op ∧ xs = g.inputs.map Sum.inr

theorem plan_spec (op : GateOp) (xs : List Signal)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : xs.length ≤ 2)
    (hnot : op = .not → xs.length ≤ 1) :
    (∀ w, planValue w (plan op xs) = op.eval (xs.map (value w))) ∧
      planShape op xs (plan op xs) := by
  rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [plan, planValue, planShape, value, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> cases x <;>
      simp [plan, planValue, planShape, value, compute, reduced, GateOp.eval]
  · rcases hop with rfl | rfl | rfl
    · rcases x with a | i <;> rcases y with b | j <;>
        (try cases a) <;> (try cases b) <;>
        simp [plan, andPlan, planValue, planShape, value, compute, reduced, GateOp.eval]
    · rcases x with a | i <;> rcases y with b | j <;>
        (try cases a) <;> (try cases b) <;>
        simp [plan, orPlan, planValue, planShape, value, compute, reduced, GateOp.eval]
    · simp at hnot
  · simp at hlen

theorem gate_plan (g : Gate) (w : List Signal)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    let xs := (activeInputs g).map (read w)
    (∀ y, planValue y (plan g.op xs) = g.op.eval (xs.map (value y))) ∧
      planShape g.op xs (plan g.op xs) := by
  have he := active_length g hlen
  apply plan_spec
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
  · simpa using he.1
  · intro h
    simpa using he.2 h

def compile (len : ℕ) (w : List Signal) : List Gate → List Signal × List Gate
  | [] => (w, [])
  | g :: gs =>
    match plan g.op ((activeInputs g).map (read w)) with
    | .inl s => compile len (w ++ [s]) gs
    | .inr g' =>
      let next := compile (len + 1) (w ++ [.inr len]) gs
      (next.1, g' :: next.2)

theorem value_read (w : List Signal) (x : List Bool) (i : ℕ) :
    value x (read w i) = (w.map (value x)).getD i false :=
  (List.getD_map w (.inl false) (value x)).symm

theorem signal_mem {w : List Signal} {i j : ℕ} (h : read w i = .inr j) :
    Sum.inr j ∈ w := by
  by_cases hi : i < w.length
  · have hm : w[i] ∈ w := List.getElem_mem _
    rw [read, List.getD_eq_getElem _ _ hi] at h
    rwa [← h]
  · rw [read, List.getD_eq_default _ _ (by omega)] at h
    cases h

theorem get_origin {P : ℕ → Prop} {orig w : List Signal} {s : Signal}
    (hw : ∀ i j, read w i = .inr j → read orig i = .inr j ∨ P j)
    (hs : ∀ j, s = .inr j → P j) :
    ∀ i j, read (w ++ [s]) i = .inr j → read orig i = .inr j ∨ P j := by
  intro i j e
  rcases Nat.lt_trichotomy i w.length with hi | rfl | hi
  · have he : read (w ++ [s]) i = read w i := List.getD_append _ _ _ _ hi
    exact hw i j (he.symm.trans e)
  · have he : read (w ++ [s]) w.length = s := by simp [read]
    exact Or.inr (hs j (he.symm.trans e))
  · have he : read (w ++ [s]) i = .inl false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [he] at e
    cases e

def Wired : ℕ → List Gate → Prop
  | _, [] => True
  | len, g :: gs => reduced g ∧ (∀ i ∈ g.inputs, i < len) ∧ Wired (len + 1) gs

theorem wired_gate {len : ℕ} {gs : List Gate} (h : Wired len gs) :
    ∀ g ∈ gs, reduced g := by
  induction gs generalizing len with
  | nil => simp
  | cons g gs ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact ih h.2.2 f hf

theorem wired_back {len : ℕ} {gs : List Gate} (h : Wired len gs) :
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < len + j := by
  induction gs generalizing len with
  | nil => simp
  | cons g gs ih =>
    intro j hj i hi
    cases j with
    | zero => exact h.2.1 i hi
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hi' : i ∈ (gs.getD j ⟨.or, []⟩).inputs := hi
      have hb := ih h.2.2 j hj' i hi'
      omega

theorem reduced_fit {g : Gate} (h : reduced g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases h with ⟨h | h, hl⟩ | ⟨h, hl⟩ <;> simp [h, hl]

theorem compile_shape (P : ℕ → Prop) (orig : List Signal) (gs : List Gate) (len : ℕ) (w : List Signal)
    (hnew : ∀ j ≥ len, P j)
    (hsource : ∀ i j, read w i = .inr j → read orig i = .inr j ∨ P j)
    (hbound : ∀ i, Sum.inr i ∈ w → i < len)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hused : ∀ g ∈ gs, ∀ i ∈ activeInputs g, ∀ j, read orig i = .inr j → P j) :
    let result := compile len w gs
    (∀ i j, read result.1 i = .inr j → read orig i = .inr j ∨ P j) ∧ Wired len result.2 ∧
      (∀ g ∈ result.2, ∀ j ∈ g.inputs, P j) ∧
      (∀ i, Sum.inr i ∈ result.1 → i < len + result.2.length) ∧
      result.2.length ≤ gs.length ∧
      (⟨GateOp.or, []⟩ ∈ gs → result.2.length < gs.length) := by
  induction gs generalizing len w with
  | nil => simpa [compile, Wired] using And.intro hsource hbound
  | cons g gs ih =>
    have htail : ∀ f ∈ gs, f.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        f.inputs.length ≤ 2 := fun f hf => hfit f (List.mem_cons_of_mem _ hf)
    have htailUsed : ∀ f ∈ gs, ∀ i ∈ activeInputs f, ∀ j, read orig i = .inr j → P j :=
      fun f hf => hused f (List.mem_cons_of_mem _ hf)
    have hfitg := hfit g (by simp)
    have hs := (gate_plan g w hfitg.1 hfitg.2).2
    have origin (i : ℕ) (hi : Sum.inr i ∈ (activeInputs g).map (read w)) : P i ∧ i < len := by
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hi
      exact ⟨(hsource j i he).elim (hused g (by simp) j hj i) id,
        hbound i (signal_mem he)⟩
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl s =>
      have hin (i : ℕ) (e : s = .inr i) :
          Sum.inr i ∈ (activeInputs g).map (read w) := by simpa [hp, e, planShape] using hs
      have hb (i : ℕ) (hi : Sum.inr i ∈ w ++ [s]) : i < len := by
        rcases List.mem_append.mp hi with hi | hi
        · exact hbound i hi
        · exact (origin i (hin i (List.mem_singleton.mp hi).symm)).2
      obtain ⟨ho, hw, hu, hb', hl, _⟩ :=
        ih len (w ++ [s]) hnew (get_origin hsource fun i e => (origin i (hin i e)).1)
          hb htail htailUsed
      simp only [compile, hp, List.length_cons]
      exact ⟨ho, hw, hu, hb', by omega, fun _ => by omega⟩
    | inr f =>
      rw [hp] at hs
      obtain ⟨hred, _, he⟩ := hs
      have hfil (i : ℕ) (hi : i ∈ f.inputs) : P i ∧ i < len :=
        origin i (he.symm ▸ List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hb (i : ℕ) (hi : Sum.inr i ∈ w ++ [.inr len]) : i < len + 1 := by
        rcases List.mem_append.mp hi with hi | hi
        · have := hbound i hi
          omega
        · have hir := List.mem_singleton.mp hi
          cases hir
          omega
      obtain ⟨ho, hw, hu, hb', hl, hstrict⟩ :=
        ih (len + 1) (w ++ [.inr len]) (fun i hi => hnew i (by omega))
          (get_origin hsource fun i e => by cases e; exact hnew len le_rfl)
          hb htail htailUsed
      simp only [compile, hp, List.length_cons]
      refine ⟨ho, ⟨hred, fun i hi => (hfil i hi).2, hw⟩, ?_, ?_, by omega, ?_⟩
      · intro a ha i hi
        rcases List.mem_cons.mp ha with rfl | ha
        · exact (hfil i hi).1
        · exact hu a ha i hi
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using hb'
      · intro hm
        rcases List.mem_cons.mp hm with e | hm
        · rw [← e] at hp
          simp [activeInputs, plan] at hp
        · have h := hstrict hm
          omega


theorem compile_values (gs : List Gate) (len : ℕ) (w : List Signal) (x y : List Bool)
    (hlen : len = y.length) (hbound : ∀ i, Sum.inr i ∈ w → i < len)
    (hvals : w.map (value y) = x)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    let result := compile len w gs
    result.1.map (value (result.2.foldl step y)) = gs.foldl step x := by
  induction gs generalizing len w x y with
  | nil => exact hvals
  | cons g gs ih =>
    have htail : ∀ h ∈ gs, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        h.inputs.length ≤ 2 := fun h hh => hfit h (List.mem_cons_of_mem _ hh)
    have hg := hfit g (by simp)
    obtain ⟨hval, hin⟩ := gate_plan g w hg.1 hg.2
    have hcomp : planValue y (plan g.op ((activeInputs g).map (read w))) = compute x g := by
      rw [hval, List.map_map, ← active_eval x g]
      congr 1
      exact List.map_congr_left fun i _ => by
        change value y (read w i) = x.getD i false
        rw [value_read, hvals]
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl s =>
      have hsval : value y s = compute x g := by simpa [hp, planValue] using hcomp
      have hbound' (i : ℕ) (hi : Sum.inr i ∈ w ++ [s]) : i < len := by
        rcases List.mem_append.mp hi with hi | hi
        · exact hbound i hi
        · have he : s = Sum.inr i := (List.mem_singleton.mp hi).symm
          have hs : Sum.inr i ∈ (activeInputs g).map (read w) := by
            simpa [hp, he, planShape] using hin
          obtain ⟨_, _, hj⟩ := List.mem_map.mp hs
          exact hbound i (signal_mem hj)
      have hstep : (w ++ [s]).map (value y) = step x g := by simp [step, hvals, hsval]
      simpa only [compile, hp, List.foldl_cons] using
        ih len (w ++ [s]) (step x g) y hlen hbound' hstep htail
    | inr f =>
      have hsval : compute y f = compute x g := by simpa [hp, planValue] using hcomp
      have hlen' : len + 1 = (step y f).length := by simp [step, hlen]
      have hbound' (i : ℕ) (hi : Sum.inr i ∈ w ++ [.inr len]) : i < len + 1 := by
        rcases List.mem_append.mp hi with hi | hi
        · have := hbound i hi
          omega
        · have he := List.mem_singleton.mp hi
          cases he
          omega
      have hold : w.map (value (step y f)) = w.map (value y) := by
        apply List.map_congr_left
        intro s hs
        cases s with
        | inl b => rfl
        | inr i =>
          exact List.getD_append _ _ _ _ (by simpa [← hlen] using hbound i hs)
      have blast : value (step y f) (.inr len) = compute y f := by simp [value, step, hlen]
      have hstep : (w ++ [Sum.inr len]).map (value (step y f)) = step x g := by
        simp only [List.map_append, hold, hvals, List.map_cons, List.map_nil, blast]
        rw [step, hsval]
      simpa only [compile, hp, List.foldl_cons] using
        ih (len + 1) (w ++ [.inr len]) (step x g) (step y f) hlen' hbound' hstep htail

def initial (n : ℕ) : List Signal := (List.range n).map Sum.inr

theorem initial_mem {n i : ℕ} (hi : Sum.inr i ∈ initial n) : i < n := by
  obtain ⟨j, hj, e⟩ := List.mem_map.mp hi
  cases e
  exact List.mem_range.mp hj

theorem initial_at {n i : ℕ} (hi : i < n) : read (initial n) i = .inr i := by
  have hl : i < (initial n).length := by simpa [initial] using hi
  rw [read, List.getD_eq_getElem _ _ hl]
  simp [initial]

theorem initial_inv {n i j : ℕ} (h : read (initial n) i = .inr j) : i = j ∧ i < n := by
  by_cases hi : i < n
  · rw [initial_at hi] at h
    exact ⟨Sum.inr.inj h, hi⟩
  · rw [read, List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi)] at h
    cases h

theorem initial_values {n : ℕ} {x : List Bool} (hx : x.length = n) :
    (initial n).map (value x) = x := by
  apply List.ext_getElem (by simp [initial, hx])
  intro i hi hj
  simp [initial, value, List.getElem?_eq_getElem hj]

theorem compile_length (gs : List Gate) (len : ℕ) (w : List Signal) :
    (compile len w gs).2.length ≤ gs.length := by
  induction gs generalizing len w with
  | nil => simp [compile]
  | cons g gs ih =>
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl s =>
      have h := ih len (w ++ [s])
      simp only [compile, hp, List.length_cons]
      omega
    | inr f =>
      have h := ih (len + 1) (w ++ [.inr len])
      simp only [compile, hp, List.length_cons]
      omega

def Ready (n : ℕ) (D : Circuit) : Prop :=
  Wired n D.gates ∧ D.output < n + D.size

theorem normalize {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit)
    (hfit : FanInTwo C) (hrep : Represents A C)
    (hne : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ D : Circuit, Ready (n + m) D ∧ FanInTwo D ∧ Represents A D ∧ D.size ≤ C.size ∧
      (∀ i < n + m, lists D i → reads C i) ∧
      (⟨GateOp.or, []⟩ ∈ C.gates → D.size < C.size) := by
  let N := n + m
  let result := compile N (initial N) C.gates
  let P := fun i => N ≤ i ∨ reads C i
  have hP (g : Gate) (hg : g ∈ C.gates) (i : ℕ) (hi : i ∈ activeInputs g)
      (j : ℕ) (hj : read (initial N) i = .inr j) : P j := by
    have he := (initial_inv hj).1
    subst j
    exact Or.inr (Or.inl ⟨g, hg, hi⟩)
  obtain ⟨ho, hw, hu, hb, hle, hstrict⟩ :=
    compile_shape P (initial N) C.gates N (initial N) (fun _ hi => Or.inl hi)
      (fun _ _ h => Or.inl h) (fun _ hi => initial_mem hi) hfit hP
  have hval (u : Fin n) (v : Fin m) :
      value (result.2.foldl step (oneEach u v)) (read result.1 C.output) = A u v := by
    have hlen : (oneEach u v).length = N := by simp [oneEach, N]
    have hh := compile_values C.gates N (initial N) (oneEach u v) (oneEach u v) hlen.symm
      (fun _ hi => initial_mem hi) (initial_values hlen) hfit
    change result.1.map (value (result.2.foldl step (oneEach u v))) =
      C.gates.foldl step (oneEach u v) at hh
    rw [value_read, hh]
    exact hrep u v
  cases he : read result.1 C.output with
  | inl b =>
    obtain ⟨u, u2, v, v2, h⟩ := hne
    have h1 := hval u v
    have h2 := hval u2 v2
    rw [he] at h1 h2
    exact (h (h1.symm.trans h2)).elim
  | inr j =>
    let D : Circuit := ⟨result.2, j⟩
    refine ⟨D, ⟨hw, hb j (signal_mem he)⟩, ?_, ?_, hle, ?_, hstrict⟩
    · exact fun g hg => reduced_fit (wired_gate hw g hg)
    · intro u v
      have h := hval u v
      rw [he] at h
      exact h
    · intro i hi h
      rcases h with ⟨g, hg, hm⟩ | h
      · exact (hu g hg i hm).resolve_left (by omega)
      · change j = i at h
        subst i
        exact (ho C.output j he).elim (fun h => Or.inr (initial_inv h).1)
          (fun hh => hh.resolve_left (by omega))


theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_agree (cut : ℕ) (gs : List Gate) (x y : List Bool)
    (hlen : x.length = y.length)
    (hx : ∀ i, i ≠ cut → x.getD i false = y.getD i false)
    (hskip : ∀ g ∈ gs, cut ∉ g.inputs) :
    ∀ i, i ≠ cut → (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs generalizing x y with
  | nil => exact hx
  | cons g gs ih =>
    have he : compute x g = compute y g := by
      unfold compute
      congr 1
      exact List.map_congr_left fun i hi =>
        hx i (fun e => hskip g (by simp) (e ▸ hi))
    have hnext (i : ℕ) (hi : i ≠ cut) :
        (step x g).getD i false = (step y g).getD i false := by
      simp only [step, snoc, hlen, he, hx i hi]
    exact ih _ _ (by simp [step, hlen]) hnext
      (fun a ha => hskip a (List.mem_cons_of_mem _ ha))

def blank : Gate := ⟨.or, []⟩

theorem mask_mem {gs : List Gate} {j : ℕ} {g : Gate} (h : g ∈ gs.set j blank) :
    g = blank ∨ g ∈ gs := by
  induction gs generalizing j with
  | nil => simp at h
  | cons a gs ih =>
    cases j with
    | zero =>
      have hm : g ∈ blank :: gs := h
      exact (List.mem_cons.mp hm).elim Or.inl (fun e => Or.inr (List.mem_cons_of_mem _ e))
    | succ j =>
      have hm : g ∈ a :: gs.set j blank := h
      rcases List.mem_cons.mp hm with e | e
      · exact Or.inr (List.mem_cons.mpr (Or.inl e))
      · exact (ih e).imp_right (List.mem_cons_of_mem _)

theorem mask_has {gs : List Gate} {j : ℕ} (hj : j < gs.length) :
    blank ∈ gs.set j blank := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero => exact List.mem_cons_self
    | succ j => exact List.mem_cons_of_mem _ (ih (by simpa using hj))

theorem mask_value (gs : List Gate) (j out : ℕ) (x : List Bool)
    (hj : j < gs.length) (hout : out ≠ x.length + j)
    (hskip : ∀ g ∈ gs, x.length + j ∉ g.inputs) :
    ((gs.set j blank).foldl step x).getD out false = (gs.foldl step x).getD out false := by
  induction gs generalizing j x with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hx : ∀ i, i ≠ x.length →
          (step x blank).getD i false = (step x g).getD i false := by
        intro i hi
        simp only [step, snoc, ite_eq_right hi]
      exact fold_agree x.length gs (step x blank) (step x g) (by simp [step]) hx
        (fun a ha => by simpa using hskip a (List.mem_cons_of_mem _ ha)) out (by simpa using hout)
    | succ j =>
      have he : (step x g).length + j = x.length + (j + 1) := by simp [step]; omega
      exact ih j (step x g) (by simpa using hj)
        (by simpa only [he] using hout)
        (fun a ha => by simpa only [he] using hskip a (List.mem_cons_of_mem _ ha))

theorem active_subset {g : Gate} {i : ℕ} (h : i ∈ activeInputs g) : i ∈ g.inputs := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [activeInputs] at h ⊢ <;> try exact h
  exact List.mem_of_mem_take h

theorem no_reads {D : Circuit} {w : ℕ} (hz : readsIn D (Finset.range D.size) w = 0) :
    ∀ g ∈ D.gates, w ∉ g.inputs := by
  intro g hg hi
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  have hle : (gateAt D j).inputs.count w ≤ readsIn D (Finset.range D.size) w :=
    Finset.single_le_sum (f := fun k => (gateAt D k).inputs.count w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  rw [gateAt, List.getD_eq_getElem _ _ hj] at hle
  have hpos := List.count_pos_iff.mpr hi
  omega

theorem last_unread {N j : ℕ} {D : Circuit} (hback : ReadsBack N D) (hj : j + 1 = D.size) :
    readsIn D (Finset.range D.size) (N + j) = 0 := by
  unfold readsIn
  apply Finset.sum_eq_zero
  intro k hk
  have hlt : k < D.gates.length := Finset.mem_range.mp hk
  by_contra hz
  have hp : 0 < (gateAt D k).inputs.count (N + j) := by omega
  have hsmall := hback k hlt (N + j) (List.count_pos_iff.mp hp)
  change j + 1 = D.gates.length at hj
  omega

def Candidate {n m : ℕ} (A : Fin n → Fin m → Bool) (C D : Circuit) : Prop :=
  Ready (n + m) D ∧ FanInTwo D ∧ Represents A D ∧
    ∀ i < n + m, lists D i → reads C i

def Complete (N : ℕ) (D : Circuit) : Prop :=
  ((∀ g ∈ D.gates, reduced g) ∧ ReadsBack N D ∧ 0 < D.size ∧
    D.output + 1 = N + D.size ∧
    (∀ j < D.size, readsIn D (Finset.range D.size) (N + j) = 0 ↔ j + 1 = D.size)) ∨
  (D.size = 0 ∧ D.output < N)

theorem complete_min {n m : ℕ} {A : Fin n → Fin m → Bool} {C D : Circuit}
    (hne : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2)
    (hc : Candidate A C D)
    (hmin : ∀ E, Candidate A C E → D.size ≤ E.size) : Complete (n + m) D := by
  obtain ⟨⟨hwire, hbound⟩, hfan, hrep, hsupport⟩ := hc
  let N := n + m
  have hback : ReadsBack N D := wired_back hwire
  have onlyOutput (j : ℕ) (hj : j < D.size)
      (hz : readsIn D (Finset.range D.size) (N + j) = 0) : D.output = N + j := by
    by_contra hout
    let E : Circuit := ⟨D.gates.set j blank, D.output⟩
    have hEsize : E.size = D.size := by simp [E, Circuit.size]
    have hEfan : FanInTwo E := by
      intro g hg
      rcases mask_mem hg with e | hm
      · subst g
        simp [blank]
      · exact hfan g hm
    have hErep : Represents A E := by
      intro u v
      have hlen : (oneEach u v).length = N := by simp [oneEach, N]
      have hv := mask_value D.gates j D.output (oneEach u v) hj
        (by simpa only [hlen] using hout) (by simpa only [hlen] using no_reads hz)
      exact hv.trans (hrep u v)
    obtain ⟨F, hready, hf, hrepF, _, huses, hstrict⟩ := normalize A E hEfan hErep hne
    have hFsupport (i : ℕ) (hi : i < N) (hh : lists F i) : reads C i := by
      apply hsupport i hi
      rcases huses i hi hh with ⟨g, hg, hm⟩ | ho
      · rcases mask_mem hg with e | hD
        · subst g
          simp [blank, activeInputs] at hm
        · exact Or.inl ⟨g, hD, active_subset hm⟩
      · exact Or.inr ho
    have hle := hmin F ⟨hready, hf, hrepF, hFsupport⟩
    have hlt := hstrict (mask_has hj)
    omega
  by_cases hz : D.size = 0
  · exact Or.inr ⟨hz, by omega⟩
  · have hj : D.size - 1 < D.size := by omega
    have hh : D.size - 1 + 1 = D.size := by omega
    have ho := onlyOutput _ hj (last_unread hback hh)
    have hlast : D.output + 1 = N + D.size := by omega
    refine Or.inl ⟨wired_gate hwire, hback, by omega, hlast, ?_⟩
    intro j hj
    exact ⟨fun e => by have h := onlyOutput j hj e; omega, last_unread hback⟩

theorem active_full {g : Gate} (h : reduced g) : activeInputs g = g.inputs := by
  rcases h with ⟨e | e, _⟩ | ⟨e, hl⟩
  · simp [activeInputs, e]
  · simp [activeInputs, e]
  · simp only [activeInputs, e]
    exact List.take_of_length_le hl.le

theorem compile_cut (gs : List Gate) (len : ℕ) (w : List Signal) (cut : ℕ)
    (hcut : cut < w.length) (hfalse : read w cut = .inl false)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hread : ∃ g ∈ gs, cut ∈ activeInputs g) :
    (compile len w gs).2.length < gs.length := by
  induction gs generalizing w len with
  | nil => simp at hread
  | cons g gs ih =>
    have htail : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun a ha => hfit a (List.mem_cons_of_mem _ ha)
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl s =>
      have h := compile_length gs len (w ++ [s])
      simp only [compile, hp, List.length_cons]
      omega
    | inr f =>
      obtain ⟨a, ha, hi⟩ := hread
      rcases List.mem_cons.mp ha with e | ha
      · subst a
        have hg := hfit g (by simp)
        have hs := (gate_plan g w hg.1 hg.2).2
        rw [hp] at hs
        have hv : Sum.inl false ∈ (activeInputs g).map (read w) :=
          List.mem_map.mpr ⟨cut, hi, hfalse⟩
        rw [hs.2.2] at hv
        obtain ⟨i, _, he⟩ := List.mem_map.mp hv
        cases he
      · have hlo : cut < (w ++ [Sum.inr len]).length := by simp; omega
        have hval : read (w ++ [Sum.inr len]) cut = .inl false :=
          (List.getD_append _ _ _ _ hcut).trans hfalse
        have h := ih (len + 1) (w ++ [.inr len]) hlo hval htail ⟨a, ha, hi⟩
        simp only [compile, hp, List.length_cons]
        omega


theorem alias_only (op : GateOp) (xs : List Signal) (i j : ℕ)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : xs.length ≤ 2)
    (hnot : op = .not → xs.length ≤ 1)
    (hasAlias : plan op xs = .inl (.inr j)) (hi : Sum.inr i ∈ xs) : i = j := by
  rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
  · simp at hi
  · rcases hop with rfl | rfl | rfl <;> cases x <;> simp_all [plan]
  · rcases hop with rfl | rfl | rfl
    · rcases x with a | p <;> rcases y with b | q <;>
        (try cases a) <;> (try cases b) <;> simp_all [plan, andPlan]
    · rcases x with a | p <;> rcases y with b | q <;>
        (try cases a) <;> (try cases b) <;> simp_all [plan, orPlan]
    · simp at hnot
  · simp at hlen

def Used (gs : List Gate) (out i : ℕ) : Prop :=
  (∃ g ∈ gs, i ∈ activeInputs g) ∨ out = i

def Retained (result : List Signal × List Gate) (out : ℕ) (s : Signal) : Prop :=
  (∃ i, s = .inr i ∧ ∃ g ∈ result.2, i ∈ g.inputs) ∨ read result.1 out = s

def Live : ℕ → ℕ → List Gate → Prop
  | _, _, [] => True
  | len, out, _ :: gs => Used gs out len ∧ Live (len + 1) out gs

theorem retained_cons {x : List Signal} {gs : List Gate} {g : Gate} {out : ℕ} {s : Signal}
    (h : Retained (x, gs) out s) : Retained (x, g :: gs) out s := by
  rcases h with ⟨i, he, a, ha, hi⟩ | h
  · exact Or.inl ⟨i, he, a, List.mem_cons_of_mem _ ha, hi⟩
  · exact Or.inr h

theorem kept_operand {g f : Gate} {w : List Signal} {i : ℕ} {s : Signal}
    (hf : (activeInputs g).map (read w) = f.inputs.map Sum.inr)
    (hi : i ∈ activeInputs g) (hread : read w i = s) :
    ∃ j, s = .inr j ∧ j ∈ f.inputs := by
  have h : s ∈ (activeInputs g).map (read w) := List.mem_map.mpr ⟨i, hi, hread⟩
  rw [hf] at h
  obtain ⟨j, hj, he⟩ := List.mem_map.mp h
  exact ⟨j, he.symm, hj⟩

theorem full_uses (gs : List Gate) (len : ℕ) (w : List Signal) (out i : ℕ) (s : Signal)
    (hs : (compile len w gs).2.length = gs.length)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hi : i < w.length) (hread : read w i = s) (hu : Used gs out i) :
    Retained (compile len w gs) out s := by
  induction gs generalizing w len with
  | nil =>
    rcases hu with ⟨g, hg, _⟩ | h
    · simp at hg
    · exact Or.inr (h.symm ▸ hread)
  | cons g gs ih =>
    have htail : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        a.inputs.length ≤ 2 := fun a ha => hfit a (List.mem_cons_of_mem _ ha)
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl a =>
      have h := compile_length gs len (w ++ [a])
      simp only [compile, hp, List.length_cons] at hs
      omega
    | inr f =>
      have hlen : (compile (len + 1) (w ++ [.inr len]) gs).2.length = gs.length := by
        simp only [compile, hp, List.length_cons] at hs
        omega
      have newRead : read (w ++ [Sum.inr len]) i = s :=
        (List.getD_append _ _ _ _ hi).trans hread
      simp only [compile, hp]
      by_cases hhead : i ∈ activeInputs g
      · have hg := hfit g (by simp)
        have hplan := (gate_plan g w hg.1 hg.2).2
        rw [hp] at hplan
        obtain ⟨j, he, hj⟩ := kept_operand hplan.2.2 hhead hread
        exact Or.inl ⟨j, he, f, List.mem_cons_self, hj⟩
      · have hut : Used gs out i := by
          rcases hu with ⟨a, ha, hj⟩ | he
          · rcases List.mem_cons.mp ha with e | ha
            · exact (hhead (e ▸ hj)).elim
            · exact Or.inl ⟨a, ha, hj⟩
          · exact Or.inr he
        exact retained_cons (ih (len + 1) (w ++ [.inr len]) hlen htail
          (by simp; omega) newRead hut)

theorem one_drop_uses (gs : List Gate) (len : ℕ) (w : List Signal) (out i j : ℕ)
    (hs : gs.length ≤ (compile len w gs).2.length + 1)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hlive : Live w.length out gs) (hi : i < w.length) (hread : read w i = .inr j)
    (hu : Used gs out i) (hout : ∃ v, read (compile len w gs).1 out = .inr v) :
    Retained (compile len w gs) out (.inr j) := by
  induction gs generalizing w len with
  | nil =>
    rcases hu with ⟨g, hg, _⟩ | h
    · simp at hg
    · exact Or.inr (h.symm ▸ hread)
  | cons g gs ih =>
    have htail : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        a.inputs.length ≤ 2 := fun a ha => hfit a (List.mem_cons_of_mem _ ha)
    have hg := hfit g (by simp)
    have hut (hhead : i ∉ activeInputs g) : Used gs out i := by
      rcases hu with ⟨a, ha, hj⟩ | he
      · rcases List.mem_cons.mp ha with e | ha
        · exact (hhead (e ▸ hj)).elim
        · exact Or.inl ⟨a, ha, hj⟩
      · exact Or.inr he
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl a =>
      have hfull : (compile len (w ++ [a]) gs).2.length = gs.length := by
        have h := compile_length gs len (w ++ [a])
        simp only [compile, hp, List.length_cons] at hs
        omega
      simp only [compile, hp] at hout ⊢
      by_cases hhead : i ∈ activeInputs g
      · have hb : w.length < (w ++ [a]).length := by simp
        have ha : read (w ++ [a]) w.length = a := by simp [read]
        have h := full_uses gs len (w ++ [a]) out w.length a hfull htail hb ha hlive.1
        cases a with
        | inl b =>
          rcases h with ⟨_, hbad, _⟩ | h
          · cases hbad
          · obtain ⟨v, hv⟩ := hout
            rw [h] at hv
            cases hv
        | inr v =>
          have hin : Sum.inr j ∈ (activeInputs g).map (read w) :=
            List.mem_map.mpr ⟨i, hhead, hread⟩
          have hlen := active_length g hg.2
          have he : j = v := alias_only g.op _ j v
            (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1)
            (by simpa using hlen.1) (fun e => by simpa using hlen.2 e) hp hin
          exact he ▸ h
      · exact full_uses gs len (w ++ [a]) out i (.inr j) hfull htail (by simp; omega)
          ((List.getD_append _ _ _ _ hi).trans hread) (hut hhead)
    | inr f =>
      simp only [compile, hp, List.length_cons] at hs
      simp only [compile, hp] at hout ⊢
      by_cases hhead : i ∈ activeInputs g
      · have hplan := (gate_plan g w hg.1 hg.2).2
        rw [hp] at hplan
        obtain ⟨v, he, hj⟩ := kept_operand hplan.2.2 hhead hread
        exact Or.inl ⟨v, he, f, List.mem_cons_self, hj⟩
      · have hnext : read (w ++ [Sum.inr len]) i = .inr j :=
          (List.getD_append _ _ _ _ hi).trans hread
        exact retained_cons (ih (len + 1) (w ++ [.inr len]) (by omega) htail
          (by simpa using hlive.2) (by simp; omega) hnext (hut hhead) hout)


theorem live_indexed (N out : ℕ) (gs : List Gate)
    (h : ∀ j < gs.length, out = N + j ∨ ∃ k < gs.length, j < k ∧
      N + j ∈ activeInputs (gs.getD k ⟨.or, []⟩)) :
    Live N out gs := by
  induction gs generalizing N with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · rcases h 0 (by simp) with he | ⟨k, hk, hpos, hu⟩
      · exact Or.inr (by simpa using he)
      · cases k with
        | zero => omega
        | succ k =>
          have hlt : k < gs.length := by simpa using hk
          have hu' : N ∈ activeInputs (gs.getD k ⟨.or, []⟩) := hu
          rw [List.getD_eq_getElem _ _ hlt] at hu'
          exact Or.inl ⟨gs[k], List.getElem_mem _, hu'⟩
    · apply ih
      intro j hj
      have hj' : j + 1 < (g :: gs).length := by simpa using hj
      have eq : N + (j + 1) = N + 1 + j := by omega
      rcases h (j + 1) hj' with he | ⟨k, hk, hjk, hm⟩
      · exact Or.inl (he.trans eq)
      · cases k with
        | zero => omega
        | succ k =>
          have hk' : k < gs.length := by simpa using hk
          have hm' : N + (j + 1) ∈ activeInputs (gs.getD k ⟨.or, []⟩) := hm
          exact Or.inr ⟨k, hk', by omega, eq ▸ hm'⟩

theorem live_reduced (N : ℕ) (C : Circuit) (hshape : ∀ g ∈ C.gates, reduced g)
    (hback : ReadsBack N C) (hout : C.output + 1 = N + C.size)
    (hread : ∀ j < C.size, readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size) :
    Live N C.output C.gates := by
  apply live_indexed
  intro j hj
  by_cases hlast : j + 1 = C.size
  · exact Or.inl (by omega)
  right
  by_contra no
  have hzero : readsIn C (Finset.range C.size) (N + j) = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < C.gates.length := Finset.mem_range.mp hk
    by_contra e
    have hp := List.count_pos_iff.mp (Nat.pos_of_ne_zero e)
    have hlt := hback k hk' (N + j) hp
    have hm : gateAt C k ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hk']
      exact List.getElem_mem hk'
    have ha : N + j ∈ activeInputs (gateAt C k) :=
      (active_full (hshape _ hm)).symm ▸ hp
    exact no ⟨k, hk', by omega, ha⟩
  exact hlast ((hread j hj).mp hzero)

noncomputable def rowSignal {n : ℕ} (k i : Fin (n + 1)) : Signal :=
  if h : i = k then .inl false
  else .inr (Classical.choose (Fin.exists_succAbove_eq h)).val

noncomputable def cutInputs {n : ℕ} (k : Fin (n + 1)) (m : ℕ) : List Signal :=
  List.ofFn (rowSignal k) ++ List.ofFn (fun i : Fin m => .inr (n + i.val))

theorem rowSignal_at {n : ℕ} {k : Fin (n + 1)} (j : Fin n) :
    rowSignal k (k.succAbove j) = .inr j.val := by
  have h := Fin.succAbove_ne k j
  rw [rowSignal, dite_eq_right h]
  have hj : Classical.choose (Fin.exists_succAbove_eq h) = j :=
    Fin.succAbove_right_injective (Classical.choose_spec (Fin.exists_succAbove_eq h))
  rw [hj]

theorem cutInputs_row {n m : ℕ} (k i : Fin (n + 1)) :
    read (cutInputs k m) i.val = rowSignal k i := by
  have hi : i.val < (List.ofFn (rowSignal k)).length := by simpa only [List.length_ofFn] using i.isLt
  rw [read, cutInputs, List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  exact List.getElem_ofFn _

theorem cutInputs_col {n m : ℕ} (k : Fin (n + 1)) (i : Fin m) :
    read (cutInputs k m) (n + 1 + i.val) = .inr (n + i.val) := by
  rw [read, cutInputs, List.getD_append_right _ _ _ _ (by simp),
    List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn _

theorem cutInputs_length {n : ℕ} (m : ℕ) (k : Fin (n + 1)) :
    (cutInputs k m).length = n + 1 + m := by simp [cutInputs, Nat.add_right_comm]

theorem cutInputs_bound {n m : ℕ} (k : Fin (n + 1)) (i : ℕ)
    (hi : Sum.inr i ∈ cutInputs k m) : i < n + m := by
  simp only [cutInputs, List.mem_append, List.mem_ofFn] at hi
  rcases hi with ⟨j, h⟩ | ⟨j, h⟩
  · by_cases he : j = k
    · subst j
      simp [rowSignal] at h
    · obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq he
      rw [rowSignal_at] at h
      simp only [Sum.inr.injEq] at h
      have hv := v.isLt
      omega
  · simp only [Sum.inr.injEq] at h
    have hj := j.isLt
    omega

theorem cutInputs_values {n m : ℕ} (k : Fin (n + 1)) (u : Fin n) (v : Fin m) :
    (cutInputs k m).map (value (oneEach u v)) = oneEach (k.succAbove u) v := by
  have hrow (i : Fin (n + 1)) : value (oneEach u v) (rowSignal k i) =
      decide (i = k.succAbove u) := by
    by_cases h : i = k
    · subst i
      simp [rowSignal, value, Fin.ne_succAbove]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
      rw [rowSignal_at]
      simp [value, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, j.isLt]
  have hcol (i : Fin m) : value (oneEach u v) (.inr (n + i.val)) = decide (i = v) := by
    simp [value, oneEach, List.getD_eq_getElem?_getD]
  have rows : (value (oneEach u v) ∘ rowSignal k) = fun i => decide (i = k.succAbove u) :=
    funext hrow
  have cols : (value (oneEach u v) ∘ fun i : Fin m => .inr (n + i.val)) =
      fun i => decide (i = v) := funext hcol
  simp only [cutInputs, List.map_append, List.map_ofFn, rows, cols]
  rfl

def oldWire {n : ℕ} (k : Fin (n + 1)) (i : ℕ) : ℕ :=
  if h : i < n then (k.succAbove ⟨i, h⟩).val else i + 1

theorem oldWire_row {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    oldWire k i.val = (k.succAbove i).val := by simp [oldWire, i.isLt]

theorem oldWire_col {n m : ℕ} (k : Fin (n + 1)) (v : Fin m) :
    oldWire k (n + v.val) = n + 1 + v.val := by
  simp [oldWire, show ¬ n + v.val < n by omega]
  omega

theorem oldWire_of_read {n m : ℕ} (k : Fin (n + 1)) {i j : ℕ}
    (h : read (cutInputs k m) i = .inr j) : oldWire k j = i := by
  by_cases hi : i < n + 1
  · let r : Fin (n + 1) := ⟨i, hi⟩
    change read (cutInputs k m) r.val = .inr j at h
    rw [cutInputs_row] at h
    by_cases e : r = k
    · rw [e] at h
      simp [rowSignal] at h
    · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq e
      rw [← ha, rowSignal_at] at h
      have he := Sum.inr.inj h
      rw [← he, oldWire_row, ha]
  · by_cases hj : i < n + 1 + m
    · let v : Fin m := ⟨i - (n + 1), by omega⟩
      have hv : n + 1 + v.val = i := by dsimp [v]; omega
      rw [← hv, cutInputs_col] at h
      rw [← Sum.inr.inj h, oldWire_col, hv]
    · rw [read, List.getD_eq_default _ _ (by rw [cutInputs_length]; omega)] at h
      cases h


theorem compile_old_read (gs : List Gate) (len : ℕ) (w : List Signal) {i : ℕ}
    (hi : i < w.length) : read (compile len w gs).1 i = read w i := by
  induction gs generalizing len w with
  | nil => rfl
  | cons g gs ih =>
    cases hp : plan g.op ((activeInputs g).map (read w)) with
    | inl s =>
      simp only [compile, hp]
      exact (ih len (w ++ [s]) (by simp; omega)).trans (List.getD_append _ _ _ _ hi)
    | inr f =>
      simp only [compile, hp]
      exact (ih (len + 1) (w ++ [.inr len]) (by simp; omega)).trans
        (List.getD_append _ _ _ _ hi)

end PEqualNP.Outside.L_meta_24694_aux

open PEqualNP.Outside.L_meta_24694_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in

theorem PEqualNP.Outside.L_meta_24694 : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + m))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val))) := by
  intro n m A k C hfan hrep hred hhit hne
  classical
  let N := n + m
  let B := fun u v => A (k.succAbove u) v
  let orig := cutInputs k m
  let target := compile N orig C.gates
  let P := fun i => N ≤ i ∨ lists C (oldWire k i)
  have hused (g : Gate) (hg : g ∈ C.gates) (i : ℕ) (hi : i ∈ activeInputs g)
      (j : ℕ) (h : read orig i = .inr j) : P j := by
    have he := oldWire_of_read k h
    exact Or.inr (Or.inl ⟨g, hg, he.symm ▸ active_subset hi⟩)
  obtain ⟨hsource, hw, hinputs, hbound, _, _⟩ :=
    compile_shape P orig C.gates N orig (fun _ h => Or.inl h) (fun _ _ h => Or.inl h)
      (cutInputs_bound k) hfan hused
  have hshape : ∀ g ∈ C.gates, reduced g := by
    rcases hred with h | ⟨hz, _⟩
    · exact h.1
    · have hn : C.gates = [] := List.length_eq_zero_iff.mp hz
      simp [hn]
  have hLive : Live orig.length C.output C.gates := by
    change Live (cutInputs k m).length C.output C.gates
    rw [cutInputs_length]
    rcases hred with ⟨_, hback, _, hout, hreads⟩ | ⟨hz, _⟩
    · exact live_reduced _ C hshape hback hout hreads
    · have hn : C.gates = [] := List.length_eq_zero_iff.mp hz
      rw [hn]
      trivial
  have hcut : k.val < orig.length := by
    have hk := k.isLt
    change k.val < (cutInputs k m).length
    rw [cutInputs_length]
    omega
  have hz : read orig k.val = .inl false := by
    change read (cutInputs k m) k.val = _
    rw [cutInputs_row]
    simp [rowSignal]
  have hvalue (u : Fin n) (v : Fin m) :
      value (target.2.foldl step (oneEach u v)) (read target.1 C.output) = B u v := by
    have hlen : N = (oneEach u v).length := by simp [N, oneEach]
    have hh := compile_values C.gates N orig (oneEach (k.succAbove u) v) (oneEach u v) hlen
      (cutInputs_bound k) (cutInputs_values k u v) hfan
    change target.1.map (value (target.2.foldl step (oneEach u v))) =
      C.gates.foldl step (oneEach (k.succAbove u) v) at hh
    rw [value_read, hh]
    exact hrep (k.succAbove u) v
  cases he : read target.1 C.output with
  | inl b =>
    obtain ⟨u, u2, v, v2, h⟩ := hne
    have h1 := hvalue u v
    have h2 := hvalue u2 v2
    rw [he] at h1 h2
    exact (h (h1.symm.trans h2)).elim
  | inr j =>
    have hread : ∃ g ∈ C.gates, k.val ∈ activeInputs g := by
      rcases hhit with ⟨a, ha, hi⟩ | hout
      · exact ⟨a, ha, (active_full (hshape a ha)).symm ▸ hi⟩
      · have hh : read target.1 k.val = .inl false :=
          (compile_old_read C.gates N orig hcut).trans hz
        rw [hout, hh] at he
        cases he
    have hsaving : target.2.length < C.gates.length :=
      compile_cut C.gates N orig k.val hcut hz hfan hread
    let G : Circuit := ⟨target.2, j⟩
    have hready : Ready N G := ⟨hw, hbound j (signal_mem he)⟩
    have hfitG : FanInTwo G := fun g hg => reduced_fit (wired_gate hw g hg)
    have hrepG : Represents B G := by
      intro u v
      have h := hvalue u v
      rw [he] at h
      exact h
    have hGC (i : ℕ) (hi : i < N) (h : lists G i) : lists C (oldWire k i) := by
      rcases h with ⟨g, hg, hgi⟩ | h
      · exact (hinputs g hg i hgi).resolve_left (by omega)
      · change j = i at h
        subst i
        exact (hsource C.output j he).elim
          (fun hh => Or.inr (oldWire_of_read k hh).symm)
          (fun hh => hh.resolve_left (by omega))
    let good := fun p => ∃ D : Circuit, Candidate B G D ∧ D.size = p
    have hG : Candidate B G G := by
      refine ⟨hready, hfitG, hrepG, ?_⟩
      intro i _ h
      rcases h with ⟨g, hg, hi⟩ | ho
      · exact Or.inl ⟨g, hg, (active_full (wired_gate hw g hg)).symm ▸ hi⟩
      · exact Or.inr ho
    have hgood : ∃ p, good p := ⟨G.size, G, hG, rfl⟩
    obtain ⟨D, hD, hde⟩ := Nat.find_spec hgood
    have hsmall (E : Circuit) (hE : Candidate B G E) : D.size ≤ E.size :=
      hde.symm ▸ Nat.find_min' hgood (show good E.size from ⟨E, hE, rfl⟩)
    have hsize := hsmall G hG
    have hDC (i : ℕ) (hi : i < N) (hh : lists D i) : lists C (oldWire k i) := by
      apply hGC i hi
      rcases hD.2.2.2 i hi hh with ⟨g, hg, hm⟩ | ho
      · exact Or.inl ⟨g, hg, active_subset hm⟩
      · exact Or.inr ho
    have hRow {E : Circuit} (h : ∀ i < N, lists E i → lists C (oldWire k i))
        (u : Fin n) (hu : lists E u.val) : lists C (k.succAbove u).val := by
      have hi := u.isLt
      simpa only [oldWire_row k u] using h u.val (by dsimp [N]; omega) hu
    have hCol {E : Circuit} (h : ∀ i < N, lists E i → lists C (oldWire k i))
        (v : Fin m) (hv : lists E (n + v.val)) : lists C (n + 1 + v.val) := by
      have hi := v.isLt
      simpa only [oldWire_col k v] using h (n + v.val) (by dsimp [N]; omega) hv
    have hl : G.size < C.size := hsaving
    by_cases hs : D.size + 2 ≤ C.size
    · exact ⟨D, hD.2.1, hD.2.2.1, complete_min hne hD hsmall, by omega,
        hRow hDC, hCol hDC, Or.inl hs⟩
    · have hminG (E : Circuit) (hE : Candidate B G E) : G.size ≤ E.size := by
        have h := hsmall E hE
        omega
      refine ⟨G, hfitG, hrepG, complete_min hne hG hminG, by omega,
        hRow hGC, hCol hGC, Or.inr ?_⟩
      intro v hv
      have hlen : C.gates.length ≤ target.2.length + 1 := by
        change C.size ≤ G.size + 1
        omega
      have hvb : n + 1 + v.val < orig.length := by
        have hv' := v.isLt
        change n + 1 + v.val < (cutInputs k m).length
        rw [cutInputs_length]
        omega
      have hvu : Used C.gates C.output (n + 1 + v.val) := by
        rcases hv with ⟨g, hg, h⟩ | h
        · exact Or.inl ⟨g, hg, (active_full (hshape g hg)).symm ▸ h⟩
        · exact Or.inr h
      have ht := one_drop_uses C.gates N orig C.output (n + 1 + v.val) (n + v.val)
        hlen hfan hLive hvb (cutInputs_col k v) hvu ⟨j, he⟩
      rcases ht with ⟨i, hh, g, hg, hi⟩ | ho
      · have e := Sum.inr.inj hh
        subst i
        exact Or.inl ⟨g, hg, hi⟩
      · change read target.1 C.output = _ at ho
        rw [he] at ho
        exact Or.inr (Sum.inr.inj ho)

