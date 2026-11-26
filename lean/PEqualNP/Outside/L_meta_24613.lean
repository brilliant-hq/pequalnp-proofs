import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24613_aux

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

theorem get_origin {P : ℕ → Prop} {w : List Signal} {s : Signal}
    (hw : ∀ i j, read w i = .inr j → i = j ∨ P j)
    (hs : ∀ j, s = .inr j → P j) :
    ∀ i j, read (w ++ [s]) i = .inr j → i = j ∨ P j := by
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

theorem compile_shape (P : ℕ → Prop) (gs : List Gate) (len : ℕ) (w : List Signal)
    (hnew : ∀ j ≥ len, P j)
    (hsource : ∀ i j, read w i = .inr j → i = j ∨ P j)
    (hbound : ∀ i, Sum.inr i ∈ w → i < len)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hused : ∀ g ∈ gs, ∀ i ∈ activeInputs g, P i) :
    let result := compile len w gs
    (∀ i j, read result.1 i = .inr j → i = j ∨ P j) ∧ Wired len result.2 ∧
      (∀ g ∈ result.2, ∀ j ∈ g.inputs, P j) ∧
      (∀ i, Sum.inr i ∈ result.1 → i < len + result.2.length) ∧
      result.2.length ≤ gs.length ∧
      (⟨GateOp.or, []⟩ ∈ gs → result.2.length < gs.length) := by
  induction gs generalizing len w with
  | nil => simpa [compile, Wired] using And.intro hsource hbound
  | cons g gs ih =>
    have htail : ∀ f ∈ gs, f.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        f.inputs.length ≤ 2 := fun f hf => hfit f (List.mem_cons_of_mem _ hf)
    have htailUsed : ∀ f ∈ gs, ∀ i ∈ activeInputs f, P i :=
      fun f hf => hused f (List.mem_cons_of_mem _ hf)
    have hfitg := hfit g (by simp)
    have hs := (gate_plan g w hfitg.1 hfitg.2).2
    have origin (i : ℕ) (hi : Sum.inr i ∈ (activeInputs g).map (read w)) : P i ∧ i < len := by
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hi
      exact ⟨(hsource j i he).elim (fun e => e ▸ hused g (by simp) j hj) id,
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

theorem initial_push (n : ℕ) : initial n ++ [.inr n] = initial (n + 1) := by
  simp only [initial, List.range_succ, List.map_append, List.map_cons, List.map_nil]

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

def trim (g : Gate) : Gate := ⟨g.op, activeInputs g⟩

theorem compile_same (gs : List Gate) (len : ℕ)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hsize : (compile len (initial len) gs).2.length = gs.length) :
    (compile len (initial len) gs).1 = initial (len + gs.length) ∧
      (compile len (initial len) gs).2 = gs.map trim := by
  induction gs generalizing len with
  | nil => simp [compile]
  | cons g gs ih =>
    have ht : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g hg => hfit g (List.mem_cons_of_mem _ hg)
    have hg := hfit g (by simp)
    have hplan := (gate_plan g (initial len) hg.1 hg.2).2
    cases hp : plan g.op ((activeInputs g).map (read (initial len))) with
    | inl s =>
      have hle := compile_length gs len (initial len ++ [s])
      simp only [compile, hp, List.length_cons] at hsize
      omega
    | inr f =>
      rw [hp] at hplan
      obtain ⟨_, hop, hxs⟩ := hplan
      have hm : (activeInputs g).map (read (initial len)) = (activeInputs g).map Sum.inr := by
        apply List.map_congr_left
        intro i hi
        have hmi : read (initial len) i ∈ f.inputs.map Sum.inr :=
          hxs ▸ List.mem_map.mpr ⟨i, hi, rfl⟩
        obtain ⟨j, _, hj⟩ := List.mem_map.mp hmi
        exact initial_at (initial_inv hj.symm).2
      have hinput : activeInputs g = f.inputs := by
        have h := congrArg (List.map (fun s : Signal => s.elim (fun _ => 0) id)) (hm.symm.trans hxs)
        simpa [List.map_map, Function.comp_def] using h
      have hf : f = trim g := by
        cases g
        cases f
        simp_all [trim]
      simp only [compile, hp, List.length_cons, initial_push] at hsize ⊢
      obtain ⟨hval, hgates⟩ := ih (len + 1) ht (Nat.add_right_cancel hsize)
      rw [hval, hgates, hf, List.map_cons]
      simp [Nat.add_assoc, Nat.add_comm 1]

def Ready (n : ℕ) (D : Circuit) : Prop :=
  Wired n D.gates ∧ D.output < n + D.size

theorem normalize {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit)
    (hfit : FanInTwo C) (hrep : Represents A C)
    (hne : ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) :
    ∃ D : Circuit, Ready (n + m) D ∧ FanInTwo D ∧ Represents A D ∧ D.size ≤ C.size ∧
      (∀ i < n + m, lists D i → reads C i) ∧
      (D.size = C.size → ∀ i < n + m, reads C i → lists D i) ∧
      (⟨GateOp.or, []⟩ ∈ C.gates → D.size < C.size) := by
  let N := n + m
  let result := compile N (initial N) C.gates
  let P := fun i => N ≤ i ∨ reads C i
  have hP : ∀ g ∈ C.gates, ∀ i ∈ activeInputs g, P i :=
    fun g hg i hi => Or.inr (Or.inl ⟨g, hg, hi⟩)
  obtain ⟨ho, hw, hu, hb, hle, hstrict⟩ :=
    compile_shape P C.gates N (initial N) (fun _ hi => Or.inl hi)
      (fun _ _ h => Or.inl (initial_inv h).1) (fun _ hi => initial_mem hi) hfit hP
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
    refine ⟨D, ⟨hw, hb j (signal_mem he)⟩, ?_, ?_, hle, ?_, ?_, hstrict⟩
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
        exact (ho C.output j he).elim Or.inr (fun hh => hh.resolve_left (by omega))
    · intro hsize i hi h
      have hs : result.2.length = C.gates.length := hsize
      obtain ⟨hw', hg⟩ := compile_same C.gates N hfit hs
      change result.1 = _ at hw'
      change result.2 = _ at hg
      rcases h with ⟨g, hmem, hgi⟩ | h
      · have hm : trim g ∈ result.2 := hg.symm ▸ List.mem_map_of_mem hmem
        exact Or.inl ⟨trim g, hm, hgi⟩
      · rw [hw'] at he
        exact Or.inr ((initial_inv he).1.symm.trans h)


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
    obtain ⟨F, hready, hf, hrepF, _, huses, _, hstrict⟩ := normalize A E hEfan hErep hne
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

theorem reads_iff {C : Circuit} {w : ℕ} (hfit : FanInTwo C) :
    reads C w ↔
      (∃ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ w ∈ g.inputs) ∨
        (g.op = .not ∧ g.inputs.head? = some w)) ∨ C.output = w := by
  constructor
  · rintro (⟨g, hg, hi⟩ | ho)
    · exact Or.inl ⟨g, hg, (active_iff (hfit g hg).1).mp hi⟩
    · exact Or.inr ho
  · rintro (⟨g, hg, hi⟩ | ho)
    · exact Or.inl ⟨g, hg, (active_iff (hfit g hg).1).mpr hi⟩
    · exact Or.inr ho

end PEqualNP.Outside.L_meta_24613_aux

open PEqualNP.Outside.L_meta_24613_aux PEqualNP.CircuitLowerBounds in

theorem PEqualNP.Outside.L_meta_24613 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.Represents.Represents A D ∧ D.size ≤ C.size ∧ (((∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ 0 < D.size ∧ D.output + 1 = (n + m) + D.size ∧ (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) ((n + m) + j) = 0 ↔ j + 1 = D.size))) ∨ (D.size = 0 ∧ D.output < (n + m))) ∧ (∀ w < (n + m), ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w)) ∧ (D.size + 1 ≤ C.size ∨ ∀ w < (n + m), ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w) → ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w)) := by
  intro n m A C hfit hrep hne
  classical
  obtain ⟨D0, hready, hfan0, hrep0, hsize0, hsupport0, hreverse0, _⟩ :=
    normalize A C hfit hrep hne
  have hc0 : Candidate A C D0 := ⟨hready, hfan0, hrep0, hsupport0⟩
  let P := fun k => ∃ D : Circuit, Candidate A C D ∧ D.size = k
  have hex : ∃ k, P k := ⟨D0.size, D0, hc0, rfl⟩
  obtain ⟨D, hc, he⟩ := Nat.find_spec hex
  have hsmall (E : Circuit) (hE : Candidate A C E) : D.size ≤ E.size :=
    he.symm ▸ Nat.find_min' hex (show P E.size from ⟨E, hE, rfl⟩)
  have hle : D.size ≤ D0.size := hsmall D0 hc0
  by_cases hs : D.size < C.size
  · exact ⟨D, hc.2.1, hc.2.2.1, by omega, complete_min hne hc hsmall,
      (fun i hi h => (reads_iff hfit).mp (hc.2.2.2 i hi h)), Or.inl (by omega)⟩
  · have heq : D0.size = C.size := by omega
    have hmin0 (E : Circuit) (hE : Candidate A C E) : D0.size ≤ E.size := by
      have hh := hsmall E hE
      omega
    exact ⟨D0, hfan0, hrep0, hsize0, complete_min hne hc0 hmin0,
      (fun i hi h => (reads_iff hfit).mp (hsupport0 i hi h)),
      Or.inr (fun i hi h => hreverse0 heq i hi ((reads_iff hfit).mpr h))⟩

