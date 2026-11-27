import PEqualNP.Defs


namespace Cloud29722

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def appendGate (N : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], N + C.gates.length⟩

@[simp] theorem appendGate_size (N : ℕ) (C : Circuit) (g : Gate) :
    (appendGate N C g).size = C.size + 1 := by simp [appendGate, Circuit.size]

theorem appendGate_wires (N : ℕ) (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate N C g).wires x = C.wires x ++
      [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [appendGate, Circuit.wires, List.foldl_append]

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨gs, o⟩ := C
  unfold Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

theorem appendGate_eval (N : ℕ) (C : Circuit) (g : Gate) (x : List Bool) (hx : x.length = N) :
    (appendGate N C g).eval x =
      g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  rw [Circuit.eval, appendGate_wires]
  change (_ ++ [_]).getD (N + C.gates.length) false = _
  rw [← hx, ← wires_length C x, List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem appendGate_oldWire (N : ℕ) (C : Circuit) (g : Gate) (x : List Bool)
    (i : ℕ) (hi : i < x.length + C.gates.length) :
    ((appendGate N C g).wires x).getD i false = (C.wires x).getD i false := by
  rw [appendGate_wires, List.getD_append]
  simpa [wires_length] using hi

theorem appendGate_fanIn (N : ℕ) (C : Circuit) (g : Gate) (hc : FanInTwo C)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hsize : g.inputs.length ≤ 2) :
    FanInTwo (appendGate N C g) := by
  intro k hk
  simp only [appendGate, List.mem_append, List.mem_singleton] at hk
  rcases hk with hk | rfl
  · exact hc k hk
  · exact ⟨hop, hsize⟩

theorem appendGate_readsBack (N : ℕ) (C : Circuit) (g : Gate) (hc : ReadsBack N C)
    (hg : ∀ i ∈ g.inputs, i < N + C.gates.length) :
    ReadsBack N (appendGate N C g) := by
  intro j hj i hi
  change j < (C.gates ++ [g]).length at hj
  simp at hj
  change i ∈ ((C.gates ++ [g]).getD j _).inputs at hi
  by_cases h : j < C.gates.length
  · rw [List.getD_append _ _ _ _ h] at hi
    exact hc j h i hi
  · have h' : j = C.gates.length := by omega
    subst j
    rw [List.getD_append_right _ _ _ _ le_rfl] at hi
    simpa using hg i (by simpa using hi)

def isNot : Gate → Bool
  | ⟨.not, _⟩ => true
  | _ => false

@[simp] theorem isNot_eq (g : Gate) : isNot g = true ↔ g.op = .not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]

def notCount (C : Circuit) : ℕ := C.gates.countP isNot

@[simp] theorem appendGate_notCount (N : ℕ) (C : Circuit) (g : Gate) :
    notCount (appendGate N C g) = notCount C + (if isNot g then 1 else 0) := by
  simp [notCount, appendGate, List.countP_append, List.countP_cons]

theorem uniqueNot_of_count (C : Circuit) (h : notCount C = 1) :
    ∃! j : Fin C.gates.length, (C.gates.get j).op = GateOp.not := by
  have hc := List.countP_ofFn C.gates.get isNot
  rw [List.ofFn_get] at hc
  unfold notCount at h
  rw [hc, Finset.card_eq_one_iff_existsUnique] at h
  simpa using h

end Cloud29722


namespace Cloud29722

inductive Tree where
  | wire (i : Nat)
  | neg (a : Tree)
  | conj (a b : Tree)
  | disj (a b : Tree)

namespace Tree

def cost : Tree → Nat
  | wire _ => 0
  | neg a => a.cost + 1
  | conj a b => a.cost + b.cost + 1
  | disj a b => a.cost + b.cost + 1

def nots : Tree → Nat
  | wire _ => 0
  | neg a => a.nots + 1
  | conj a b => a.nots + b.nots
  | disj a b => a.nots + b.nots

def value (v : Nat → Bool) : Tree → Bool
  | wire i => v i
  | neg a => !(a.value v)
  | conj a b => a.value v && b.value v
  | disj a b => a.value v || b.value v

def withWires (base : Tree) : List Nat → Tree
  | [] => base
  | u :: xs => disj (wire u) (withWires base xs)

def withEdges (base : Tree) : List (Nat × Nat) → Tree
  | [] => base
  | e :: es => disj (conj (wire e.1) (wire e.2)) (withEdges base es)

@[simp] theorem cost_withWires (base : Tree) (xs : List Nat) :
    (withWires base xs).cost = base.cost + xs.length := by
  induction xs with
  | nil => simp [withWires]
  | cons x xs ih => simp [withWires, cost, ih, Nat.add_assoc]

@[simp] theorem nots_withWires (base : Tree) (xs : List Nat) :
    (withWires base xs).nots = base.nots := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [withWires, nots, ih]

@[simp] theorem value_withWires (v : Nat → Bool) (base : Tree) (xs : List Nat) :
    (withWires base xs).value v = (base.value v || xs.any v) := by
  induction xs with
  | nil => simp [withWires]
  | cons x xs ih => simp [withWires, value, ih, Bool.or_left_comm]

@[simp] theorem cost_withEdges (base : Tree) (es : List (Nat × Nat)) :
    (withEdges base es).cost = base.cost + 2 * es.length := by
  induction es with
  | nil => simp [withEdges]
  | cons e es ih =>
    simp only [withEdges, cost, ih, List.length_cons]
    omega

@[simp] theorem nots_withEdges (base : Tree) (es : List (Nat × Nat)) :
    (withEdges base es).nots = base.nots := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [withEdges, nots, ih]

@[simp] theorem value_withEdges (v : Nat → Bool) (base : Tree) (es : List (Nat × Nat)) :
    (withEdges base es).value v = (base.value v || es.any (fun e => v e.1 && v e.2)) := by
  induction es with
  | nil => simp [withEdges]
  | cons e es ih => simp [withEdges, value, ih, Bool.or_left_comm]

def selector (r2 c2 r3 c3 w : Nat) (xs : List Nat) (es : List (Nat × Nat)) : Tree :=
  withEdges
    (disj (conj (disj (wire r2) (wire c2)) (neg (wire w)))
      (conj (disj (wire r3) (wire c3)) (withWires (wire w) xs))) es

theorem selector_cost (r2 c2 r3 c3 w : Nat) (xs : List Nat) (es : List (Nat × Nat)) :
    (selector r2 c2 r3 c3 w xs es).cost = 6 + xs.length + 2 * es.length := by
  simp only [selector, cost_withEdges, cost, cost_withWires]
  omega

theorem selector_nots (r2 c2 r3 c3 w : Nat) (xs : List Nat) (es : List (Nat × Nat)) :
    (selector r2 c2 r3 c3 w xs es).nots = 1 := by
  simp [selector, nots]

theorem selector_value (v : Nat → Bool) (r2 c2 r3 c3 w : Nat)
    (xs : List Nat) (es : List (Nat × Nat)) :
    (selector r2 c2 r3 c3 w xs es).value v =
      ((((v r2 || v c2) && !v w) || ((v r3 || v c3) && (v w || xs.any v))) ||
        es.any (fun e => v e.1 && v e.2)) := by
  simp [selector, value]

end Tree
end Cloud29722


namespace PEqualNP.Outside.Selector29722

def outside4 {n : Nat} (x : Fin 4 ↪ Fin n) (i : Fin n) : Bool :=
  decide (i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2 ∧ i ≠ x 3)

def selector (w p q rowExt colExt : Bool) : Bool :=
  (p && !w) || (q && ((w || rowExt) || colExt))

theorem matrix_entry {n m : Nat} (A : Fin n → Fin m → Bool)
    (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (rows : ∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧
      A (x 2) j = decide (j ≠ y 1))
    (cols : ∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧
      A i (y 2) = decide (i ≠ x 1))
    (corner : A (x 3) (y 3) = false) (i : Fin n) (j : Fin m) :
    (selector
       (decide (i = x 1) || decide (j = y 1))
       (decide (i = x 2) || decide (j = y 2))
       (decide (i = x 3) || decide (j = y 3))
       (outside4 x i && A i (y 3))
       (outside4 y j && A (x 3) j) ||
     ((outside4 x i && outside4 y j) && A i j)) = A i j := by
  have rx0 := fun j => (rows j).1
  have rx1 := fun j => (rows j).2.1
  have rx2 := fun j => (rows j).2.2
  have cy0 := fun i => (cols i).1
  have cy1 := fun i => (cols i).2.1
  have cy2 := fun i => (cols i).2.2
  by_cases hi0 : i = x 0
  · subst i
    by_cases h2 : j = y 2
    · subst j; simp [selector, outside4, rx0, x.injective.eq_iff, y.injective.eq_iff]
    by_cases h3 : j = y 3
    · subst j; simp [selector, outside4, rx0, x.injective.eq_iff, y.injective.eq_iff]
    simp [selector, outside4, rx0, x.injective.eq_iff, h2, h3]
  by_cases hi1 : i = x 1
  · subst i
    simp [selector, outside4, rx1, x.injective.eq_iff]
  by_cases hi2 : i = x 2
  · subst i
    by_cases h3 : j = y 3
    · subst j; simp [selector, outside4, rx2, x.injective.eq_iff, y.injective.eq_iff]
    simp [selector, outside4, rx2, x.injective.eq_iff, h3]
  by_cases hi3 : i = x 3
  · subst i
    by_cases hj0 : j = y 0
    · subst j; simp [selector, outside4, cy0, corner, x.injective.eq_iff, y.injective.eq_iff]
    by_cases hj1 : j = y 1
    · subst j; simp [selector, outside4, cy1, corner, x.injective.eq_iff, y.injective.eq_iff]
    by_cases hj2 : j = y 2
    · subst j; simp [selector, outside4, cy2, corner, x.injective.eq_iff, y.injective.eq_iff]
    by_cases hj3 : j = y 3
    · subst j; simp [selector, outside4, corner, x.injective.eq_iff, y.injective.eq_iff]
    simp [selector, outside4, hj0, hj1, hj2, hj3, corner, x.injective.eq_iff]
  by_cases hj0 : j = y 0
  · subst j; simp [selector, outside4, cy0, hi0, hi1, hi2, hi3, y.injective.eq_iff]
  by_cases hj1 : j = y 1
  · subst j; simp [selector, outside4, cy1, hi0, hi1, hi2, hi3, y.injective.eq_iff]
  by_cases hj2 : j = y 2
  · subst j; simp [selector, outside4, cy2, hi0, hi1, hi2, hi3, y.injective.eq_iff]
  by_cases hj3 : j = y 3
  · subst j; simp [selector, outside4, hi0, hi1, hi2, hi3, y.injective.eq_iff]
  simp [selector, outside4, hi0, hi1, hi2, hi3, hj0, hj1, hj2, hj3]

end PEqualNP.Outside.Selector29722

namespace Cloud29722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def Tree.compile (N : ℕ) (C : Circuit) : Tree → Circuit
  | .wire i => ⟨C.gates, i⟩
  | .neg a => let A := a.compile N C; appendGate N A ⟨.not, [A.output]⟩
  | .conj a b =>
    let A := a.compile N C
    let B := b.compile N A
    appendGate N B ⟨.and, [A.output, B.output]⟩
  | .disj a b =>
    let A := a.compile N C
    let B := b.compile N A
    appendGate N B ⟨.or, [A.output, B.output]⟩

def Tree.Valid (bound : Nat) : Tree → Prop
  | .wire i => i < bound
  | .neg a => a.Valid bound
  | .conj a b | .disj a b => a.Valid bound ∧ b.Valid bound

theorem Tree.valid_mono {k l : ℕ} (t : Tree) (h : t.Valid k) (hle : k ≤ l) : t.Valid l := by
  induction t with
  | wire i => exact lt_of_lt_of_le h hle
  | neg a ih => exact ih h
  | conj a b ih jh | disj a b ih jh => exact ⟨ih h.1, jh h.2⟩

theorem compile_length_ge (N : ℕ) (C : Circuit) (t : Tree) :
    C.gates.length ≤ (t.compile N C).gates.length := by
  induction t generalizing C with
  | wire i => exact le_rfl
  | neg a ih => simpa [Tree.compile, appendGate] using Nat.le_succ_of_le (ih C)
  | conj a b ih jh | disj a b ih jh =>
    simpa [Tree.compile, appendGate] using Nat.le_succ_of_le ((ih C).trans (jh (a.compile N C)))

theorem compile_output_lt (N : ℕ) (C : Circuit) (t : Tree) (h : t.Valid (N+C.gates.length)) :
    (t.compile N C).output < N + (t.compile N C).gates.length := by
  cases t <;> first | exact h | simp [Tree.compile, appendGate]

theorem compile_old (N : ℕ) (C : Circuit) (t : Tree) (x : List Bool) (i : ℕ)
    (h : i < x.length + C.gates.length) :
    ((t.compile N C).wires x).getD i false = (C.wires x).getD i false := by
  induction t generalizing C with
  | wire j => rfl
  | neg a ih =>
    change ((appendGate N (a.compile N C) _).wires x).getD i false = _
    rw [appendGate_oldWire, ih C h]
    exact lt_of_lt_of_le h (Nat.add_le_add_left (compile_length_ge N C a) _)
  | conj a b ih jh | disj a b ih jh =>
    have ha := lt_of_lt_of_le h (Nat.add_le_add_left (compile_length_ge N C a) _)
    change ((appendGate N (b.compile N (a.compile N C)) _).wires x).getD i false = _
    rw [appendGate_oldWire, jh _ ha, ih C h]
    exact lt_of_lt_of_le ha (Nat.add_le_add_left (compile_length_ge N (a.compile N C) b) _)

theorem Tree.value_congr {k : Nat} (t : Tree) (ht : t.Valid k) {v w : Nat → Bool}
    (h : ∀ i < k, v i = w i) : t.value v = t.value w := by
  induction t with
  | wire i => exact h _ ht
  | neg a ih => simp only [Tree.value, ih ht]
  | conj a b ih jh | disj a b ih jh => simp only [Tree.value, ih ht.1, jh ht.2]

theorem compile_eval (N : ℕ) (C : Circuit) (t : Tree) (x : List Bool) (hx : x.length = N)
    (ht : t.Valid (N+C.gates.length)) :
    (t.compile N C).eval x = t.value (fun i => (C.wires x).getD i false) := by
  induction t generalizing C with
  | wire i => rfl
  | neg a ih =>
    simp only [Tree.compile, appendGate_eval _ _ _ _ hx, Tree.value, List.map_cons, List.map_nil,
      GateOp.eval, List.headD_cons]
    exact congrArg Bool.not (ih C ht)
  | conj a b ih jh | disj a b ih jh =>
    let A := a.compile N C
    have hb := b.valid_mono ht.2 (Nat.add_le_add_left (compile_length_ge N C a) N)
    have hold := compile_old N A b x A.output (hx ▸ compile_output_lt N C a ht.1)
    have hval := b.value_congr ht.2 (fun i hi => compile_old N C a x i (by simpa [hx] using hi))
    have ha : (A.wires x).getD A.output false = _ := ih C ht.1
    have hbb : ((b.compile N A).wires x).getD (b.compile N A).output false = _ := jh A hb
    change (appendGate N (b.compile N A) _).eval x = _
    rw [appendGate_eval _ _ _ _ hx]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, Tree.value]
    rw [hold, ha, hbb, hval]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace Tree

theorem compile_size (N : Nat) (C : Circuit) (t : Tree) :
    (t.compile N C).size = C.size + t.cost := by
  induction t generalizing C with
  | wire i => rfl
  | neg a ih => simp [compile, cost, ih, Nat.add_assoc]
  | conj a b ih jh | disj a b ih jh => simp [compile, cost, ih, jh, Nat.add_assoc]

theorem compile_notCount (N : Nat) (C : Circuit) (t : Tree) :
    notCount (t.compile N C) = notCount C + t.nots := by
  induction t generalizing C with
  | wire i => rfl
  | neg a ih => simp [compile, nots, ih, isNot, Nat.add_assoc]
  | conj a b ih jh | disj a b ih jh => simp [compile, nots, ih, jh, isNot, Nat.add_assoc]

theorem compile_fanIn (N : Nat) (C : Circuit) (t : Tree) (hc : FanInTwo C) :
    FanInTwo (t.compile N C) := by
  induction t generalizing C with
  | wire _ => exact hc
  | neg a ih =>
    apply appendGate_fanIn _ _ _ (ih _ hc) <;> simp
  | conj a b ia ib =>
    apply appendGate_fanIn _ _ _ (ib _ (ia _ hc)) <;> simp
  | disj a b ia ib =>
    apply appendGate_fanIn _ _ _ (ib _ (ia _ hc)) <;> simp

theorem compile_readsBack (N : Nat) (C : Circuit) (t : Tree) (hc : ReadsBack N C)
    (hv : t.Valid (N + C.gates.length)) : ReadsBack N (t.compile N C) := by
  induction t generalizing C with
  | wire _ => exact hc
  | neg a ih =>
    apply appendGate_readsBack _ _ _ (ih _ hc hv)
    intro i hi
    have he : i = (a.compile N C).output := by simpa using hi
    rw [he]
    exact compile_output_lt N C a hv
  | conj a b ia ib =>
    let A := a.compile N C
    let B := b.compile N A
    have ha : a.Valid (N + C.gates.length) := hv.1
    have hb : b.Valid (N + A.gates.length) := by
      exact b.valid_mono hv.2 (Nat.add_le_add_left (compile_length_ge N C a) N)
    apply appendGate_readsBack _ _ _ (ib A (ia C hc ha) hb)
    intro i hi
    change i ∈ [A.output, B.output] at hi
    change i < N + B.gates.length
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le (compile_output_lt N C a ha) (Nat.add_le_add_left (compile_length_ge N A b) N)
    · exact compile_output_lt N A b hb
  | disj a b ia ib =>
    let A := a.compile N C
    let B := b.compile N A
    have ha : a.Valid (N + C.gates.length) := hv.1
    have hb : b.Valid (N + A.gates.length) := by
      exact b.valid_mono hv.2 (Nat.add_le_add_left (compile_length_ge N C a) N)
    apply appendGate_readsBack _ _ _ (ib A (ia C hc ha) hb)
    intro i hi
    change i ∈ [A.output, B.output] at hi
    change i < N + B.gates.length
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le (compile_output_lt N C a ha) (Nat.add_le_add_left (compile_length_ge N A b) N)
    · exact compile_output_lt N A b hb

theorem valid_withWires (d : Nat) (base : Tree) (xs : List Nat)
    (hb : base.Valid d) (hx : ∀ x ∈ xs, x < d) : (withWires base xs).Valid d := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    exact ⟨hx x (by simp), ih (fun z hz => hx z (by simp [hz]))⟩

theorem valid_withEdges (d : Nat) (base : Tree) (es : List (Nat × Nat))
    (hb : base.Valid d) (he : ∀ e ∈ es, e.1 < d ∧ e.2 < d) : (withEdges base es).Valid d := by
  induction es with
  | nil => exact hb
  | cons e es ih =>
    exact ⟨he e (by simp), ih (fun z hz => he z (by simp [hz]))⟩

theorem selector_valid (d r2 c2 r3 c3 w : Nat) (xs : List Nat) (es : List (Nat × Nat))
    (hr2 : r2 < d) (hc2 : c2 < d) (hr3 : r3 < d) (hc3 : c3 < d) (hw : w < d)
    (hx : ∀ x ∈ xs, x < d) (he : ∀ e ∈ es, e.1 < d ∧ e.2 < d) :
    (selector r2 c2 r3 c3 w xs es).Valid d :=
  valid_withEdges _ _ _ ⟨⟨⟨hr2, hc2⟩, hw⟩, ⟨⟨hr3, hc3⟩, valid_withWires _ _ _ hw hx⟩⟩ he

end Tree


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def seed (N r c : Nat) : Circuit := ⟨[⟨.or, [r,c]⟩], N⟩

theorem seed_fanIn (N r c : Nat) : FanInTwo (seed N r c) := by
  intro g hg
  simp only [seed, List.mem_singleton] at hg
  subst g
  simp

theorem seed_readsBack (N r c : Nat) (hr : r < N) (hc : c < N) :
    ReadsBack N (seed N r c) := by
  intro j hj i hi
  have hj' : j = 0 := by simpa [seed] using hj
  subst j
  simp [gateAt, seed] at hi
  rcases hi with rfl | rfl <;> simpa

@[simp] theorem seed_size (N r c : Nat) : (seed N r c).size = 1 := rfl

@[simp] theorem seed_nots (N r c : Nat) : notCount (seed N r c) = 0 := rfl

theorem seed_wire_old (N r c : Nat) (x : List Bool) (hx : x.length = N)
    (i : Nat) (hi : i < N) : ((seed N r c).wires x).getD i false = x.getD i false := by
  change (x ++ [_]).getD i false = _
  exact List.getD_append _ _ _ _ (hx ▸ hi : i < x.length)

theorem seed_wire_new (N r c : Nat) (x : List Bool) (hx : x.length = N) :
    ((seed N r c).wires x).getD N false = (x.getD r false || x.getD c false) := by
  change (x ++ [_]).getD N false = _
  rw [List.getD_append_right _ _ _ _ (le_of_eq hx)]
  simp [hx, GateOp.eval]


theorem any_agree {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ i ∈ l, f i = g i) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem construct (N r1 c1 r2 c2 r3 c3 : Nat) (xs : List Nat) (es : List (Nat × Nat))
    (hr1 : r1 < N) (hc1 : c1 < N) (hr2 : r2 < N) (hc2 : c2 < N)
    (hr3 : r3 < N) (hc3 : c3 < N) (hx : ∀ i ∈ xs, i < N)
    (he : ∀ e ∈ es, e.1 < N ∧ e.2 < N) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack N C ∧
      C.size = 7 + xs.length + 2 * es.length ∧
      (∃! j : Fin C.gates.length, (C.gates.get j).op = GateOp.not) ∧
      ∀ (x : List Bool), x.length = N →
        let v := fun i => x.getD i false
        let w := v r1 || v c1
        C.eval x = ((((v r2 || v c2) && !w) || ((v r3 || v c3) && (w || xs.any v))) ||
          es.any (fun e => v e.1 && v e.2)) := by
  let S := seed N r1 c1
  let t := Tree.selector r2 c2 r3 c3 N xs es
  have ht : t.Valid (N + S.gates.length) := by
    change t.Valid (N + 1)
    exact Tree.selector_valid _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (fun i hi => Nat.lt_succ_of_lt (hx i hi))
      (fun e h => ⟨Nat.lt_succ_of_lt (he e h).1, Nat.lt_succ_of_lt (he e h).2⟩)
  refine ⟨t.compile N S, t.compile_fanIn N S (seed_fanIn N r1 c1),
    t.compile_readsBack N S (seed_readsBack _ _ _ hr1 hc1) ht, ?_, ?_, ?_⟩
  · rw [Tree.compile_size, Tree.selector_cost, seed_size]; omega
  · apply uniqueNot_of_count
    rw [Tree.compile_notCount, Tree.selector_nots, seed_nots]
  · intro x h
    dsimp only
    rw [compile_eval N S t x h ht, Tree.selector_value]
    let v := fun i : Nat => (S.wires x).getD i false
    let u := fun i : Nat => x.getD i false
    have hold : ∀ i, i < N → v i = u i := seed_wire_old N r1 c1 x h
    have hnew : v N = (u r1 || u c1) := seed_wire_new N r1 c1 x h
    change ((((v r2 || v c2) && !(v N)) || ((v r3 || v c3) && (v N || xs.any v))) ||
      es.any (fun e => v e.1 && v e.2)) = _
    rw [hold _ hr2, hold _ hc2, hold _ hr3, hold _ hc3, hnew,
      any_agree xs v u (fun i hi => hold i (hx i hi)),
      any_agree es (fun e => v e.1 && v e.2) (fun e => u e.1 && u e.2)
        (fun e hi => by rw [hold _ (he e hi).1, hold _ (he e hi).2])]

end Cloud29722

namespace Cloud29722
open PEqualNP.Represents

theorem row_lookup {n m : Nat} (u : Fin n) (v : Fin m) (r : Fin n) :
    (oneEach u v).getD r.val false = decide (u = r) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp [r.isLt, eq_comm]

theorem col_lookup {n m : Nat} (u : Fin n) (v : Fin m) (c : Fin m) :
    (oneEach u v).getD (n + c.val) false = decide (v = c) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [c.isLt, eq_comm]

theorem any_extension {n m : Nat} (u : Fin n) (v : Fin m)
    (look : Nat → Bool) (hr : ∀ r : Fin n, look r.val = decide (u = r))
    (hc : ∀ c : Fin m, look (n + c.val) = decide (v = c))
    (rs : List (Fin n)) (cs : List (Fin m)) :
    ((rs.map Fin.val ++ cs.map (fun c => n + c.val)).any look) =
      (decide (u ∈ rs) || decide (v ∈ cs)) := by
  have h₁ : (rs.map Fin.val).any look = decide (u ∈ rs) := by
    induction rs with
    | nil => simp
    | cons r rs ih => simp [ih, hr]
  have h₂ : (cs.map (fun c => n + c.val)).any look = decide (v ∈ cs) := by
    induction cs with
    | nil => simp
    | cons c cs ih => simp [ih, hc]
  rw [List.any_append, h₁, h₂]

theorem any_edges {n m : Nat} (u : Fin n) (v : Fin m)
    (look : Nat → Bool) (hr : ∀ r : Fin n, look r.val = decide (u = r))
    (hc : ∀ c : Fin m, look (n + c.val) = decide (v = c))
    (es : List (Fin n × Fin m)) :
    ((es.map (fun e => (e.1.val, n + e.2.val))).any (fun e => look e.1 && look e.2)) =
      decide ((u,v) ∈ es) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    rcases e with ⟨r,c⟩
    simp [hr, hc, ih]

end Cloud29722
namespace Cloud29722
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents
open PEqualNP.Outside.Selector29722

theorem of_lists {n m : Nat} (A : Fin n → Fin m → Bool)
    (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m)
    (rs : List (Fin n)) (cs : List (Fin m)) (es : List (Fin n × Fin m))
    (hr : ∀ i, decide (i ∈ rs) = (outside4 x i && A i (y 3)))
    (hc : ∀ j, decide (j ∈ cs) = (outside4 y j && A (x 3) j))
    (he : ∀ i j, decide ((i,j) ∈ es) = ((outside4 x i && outside4 y j) && A i j))
    (hcount : 7 + (rs.length + cs.length) + 2 * es.length = n+m-1)
    (rows : ∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧ A (x 2) j = decide (j ≠ y 1))
    (cols : ∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧ A i (y 2) = decide (i ≠ x 1))
    (corner : A (x 3) (y 3) = false) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (n+m) C ∧ Represents A C ∧
      C.size = n+m-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op = GateOp.not := by
  let xs := rs.map Fin.val ++ cs.map (fun c => n+c.val)
  let edges := es.map (fun e => (e.1.val, n+e.2.val))
  have hxs : ∀ i ∈ xs, i < n+m := by
    intro i hi
    simp only [xs, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨r, _, rfl⟩ | ⟨c, _, rfl⟩ <;> omega
  have hedges : ∀ e ∈ edges, e.1 < n+m ∧ e.2 < n+m := by
    intro e he
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    exact ⟨by have := p.1.isLt; omega, by have := p.2.isLt; omega⟩
  obtain ⟨C, hf, hb, hs, hn, hv⟩ := construct (n+m) (x 1).val (n+(y 1).val)
    (x 2).val (n+(y 2).val) (x 3).val (n+(y 3).val) xs edges
    (by have := (x 1).isLt; omega) (by have := (y 1).isLt; omega)
    (by have := (x 2).isLt; omega) (by have := (y 2).isLt; omega)
    (by have := (x 3).isLt; omega) (by have := (y 3).isLt; omega) hxs hedges
  refine ⟨C, hf, hb, ?_, ?_, hn⟩
  · intro i j
    have h := hv (oneEach i j) (by simp [oneEach])
    dsimp only at h
    rw [h]
    let look := fun k => (oneEach i j).getD k false
    have ha := any_extension i j look (row_lookup i j) (col_lookup i j) rs cs
    have hp := any_edges i j look (row_lookup i j) (col_lookup i j) es
    change xs.any look = _ at ha
    change edges.any _ = _ at hp
    rw [ha, hp, hr, hc, he]
    simp only [row_lookup, col_lookup, ← Bool.or_assoc]
    simpa only [selector, ← Bool.or_assoc] using matrix_entry A x y rows cols corner i j
  · simpa [xs, edges, List.length_append, hcount] using hs
end Cloud29722


namespace Cloud29722

theorem card_outside_four {n : Nat} (x : Fin 4 ↪ Fin n) :
    (Finset.univ.filter (fun i : Fin n =>
      i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2 ∧ i ≠ x 3)).card + 4 = n := by
  let special : Finset (Fin n) := {x 0, x 1, x 2, x 3}
  have hspecial : special.card = 4 := by
    simp [special, x.injective.eq_iff]
  have hcompl :
      Finset.univ.filter (fun i : Fin n => i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2 ∧ i ≠ x 3) =
        specialᶜ := by
    ext i
    simp [special]
  rw [hcompl, ← hspecial, Finset.card_compl_add_card]
  exact Fintype.card_fin n

end Cloud29722


namespace Cloud29722

theorem card_split_proj {α β : Type} [DecidableEq α] [DecidableEq β]
    (O S : Finset α) (E : Finset (α × β)) (hu : O = S ∪ E.image Prod.fst)
    (hd : Disjoint S (E.image Prod.fst)) (hi : Set.InjOn Prod.fst (↑E : Set (α × β))) :
    O.card = S.card + E.card := by
  rw [hu, Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hi]

theorem card_split_snd {α β : Type} [DecidableEq α] [DecidableEq β]
    (O S : Finset β) (E : Finset (α × β)) (hu : O = S ∪ E.image Prod.snd)
    (hd : Disjoint S (E.image Prod.snd)) (hi : Set.InjOn Prod.snd (↑E : Set (α × β))) :
    O.card = S.card + E.card := by
  rw [hu, Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hi]

end Cloud29722


namespace Cloud29722

section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def specialRows (rows : Finset α) (A : α → β → Bool) (c : β) : Finset α :=
  rows.filter (fun i => A i c = true)

def specialCols (cols : Finset β) (A : α → β → Bool) (r : α) : Finset β :=
  cols.filter (fun j => A r j = true)

def outsideEdges (rows : Finset α) (cols : Finset β) (A : α → β → Bool) :
    Finset (α × β) := (rows ×ˢ cols).filter (fun p => A p.1 p.2 = true)

theorem projectionCovers (rows : Finset α) (cols : Finset β) (A : α → β → Bool)
    (r : α) (c : β) (hr : r ∉ rows) (hc : c ∉ cols)
    (rowTotal : ∀ i ∈ rows, ∃ j, (j = c ∨ j ∈ cols) ∧ A i j = true)
    (rowUnique : ∀ i ∈ rows, ∀ j k, (j = c ∨ j ∈ cols) → (k = c ∨ k ∈ cols) →
      A i j = true → A i k = true → j = k)
    (colTotal : ∀ j ∈ cols, ∃ i, (i = r ∨ i ∈ rows) ∧ A i j = true)
    (colUnique : ∀ j ∈ cols, ∀ i k, (i = r ∨ i ∈ rows) → (k = r ∨ k ∈ rows) →
      A i j = true → A k j = true → i = k) :
    let E := outsideEdges rows cols A
    (rows = specialRows rows A c ∪ E.image Prod.fst) ∧
    Disjoint (specialRows rows A c) (E.image Prod.fst) ∧
    Set.InjOn Prod.fst (↑E : Set (α × β)) ∧
    (cols = specialCols cols A r ∪ E.image Prod.snd) ∧
    Disjoint (specialCols cols A r) (E.image Prod.snd) ∧
    Set.InjOn Prod.snd (↑E : Set (α × β)) := by
  dsimp only
  have edge (i : α) (j : β) : (i,j) ∈ outsideEdges rows cols A ↔
      (i ∈ rows ∧ j ∈ cols) ∧ A i j = true := by simp [outsideEdges]
  constructor
  · ext i
    constructor
    · intro hi
      obtain ⟨j, hj | hj, ha⟩ := rowTotal i hi
      · subst j
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ha⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(i,j), (edge i j).mpr ⟨⟨hi,hj⟩,ha⟩, rfl⟩)
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (Finset.mem_filter.mp hi).1
      · obtain ⟨⟨i',j⟩, h, rfl⟩ := Finset.mem_image.mp hi
        exact ((edge i' j).mp h).1.1
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi he
    obtain ⟨⟨i',j⟩, hm, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨hi',hj⟩,ha⟩ := (edge i' j).mp hm
    have eq := rowUnique i' hi' c j (Or.inl rfl) (Or.inr hj) (Finset.mem_filter.mp hi).2 ha
    exact hc (eq ▸ hj)
  constructor
  · rintro ⟨i,j⟩ hp ⟨k,l⟩ hq h
    change i = k at h
    subst k
    obtain ⟨⟨hi,hj⟩,ha⟩ := (edge i j).mp hp
    obtain ⟨⟨_,hl⟩,hb⟩ := (edge i l).mp hq
    have e := rowUnique i hi j l (Or.inr hj) (Or.inr hl) ha hb
    simp [e]
  constructor
  · ext j
    constructor
    · intro hj
      obtain ⟨i, hi | hi, ha⟩ := colTotal j hj
      · subst i
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, ha⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(i,j), (edge i j).mpr ⟨⟨hi,hj⟩,ha⟩, rfl⟩)
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (Finset.mem_filter.mp hj).1
      · obtain ⟨⟨i,j'⟩, h, rfl⟩ := Finset.mem_image.mp hj
        exact ((edge i j').mp h).1.2
  constructor
  · apply Finset.disjoint_left.mpr
    intro j hj he
    obtain ⟨⟨i,j'⟩, hm, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨hi,hj'⟩,ha⟩ := (edge i j').mp hm
    have eq := colUnique j' hj' r i (Or.inl rfl) (Or.inr hi) (Finset.mem_filter.mp hj).2 ha
    exact hr (eq ▸ hi)
  · rintro ⟨i,j⟩ hp ⟨k,l⟩ hq h
    change j = l at h
    subst l
    obtain ⟨⟨hi,hj⟩,ha⟩ := (edge i j).mp hp
    obtain ⟨⟨hk,_⟩,hb⟩ := (edge k j).mp hq
    have e := colUnique j hj i k (Or.inr hi) (Or.inr hk) ha hb
    simp [e]

end
end Cloud29722

open Cloud29722

theorem PEqualNP.Outside.L_meta_29722 : (
∀ (n m : Nat) (A : Fin n → Fin m → Bool) (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
  (
  let R := fun i : Fin n => i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2
  let T := fun j : Fin m => j ≠ y 0 ∧ j ≠ y 1 ∧ j ≠ y 2
  (∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧
    A (x 2) j = decide (j ≠ y 1)) ∧
  (∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧
    A i (y 2) = decide (i ≠ x 1)) ∧ A (x 3) (y 3) = false ∧
  (∀ i j l, R i → T j → T l → A i j = true → A i l = true → j = l) ∧
  (∀ j i k, T j → R i → R k → A i j = true → A k j = true → i = k) ∧
  (∀ i, R i → i ≠ x 3 → ∃ j, T j ∧ A i j = true) ∧
  (∀ j, T j → j ≠ y 3 → ∃ i, R i ∧ A i j = true)) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧ PEqualNP.Represents.Represents A C ∧
    C.size = n+m-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not
) := by
  classical
  intro n m A x y h
  obtain ⟨borderR, borderC, corner, uRow, uCol, eRow, eCol⟩ := h
  let O (k : Nat) (z : Fin 4 ↪ Fin k) := Finset.univ.filter (fun i : Fin k =>
    i ≠ z 0 ∧ i ≠ z 1 ∧ i ≠ z 2 ∧ i ≠ z 3)
  let rows := O n x
  let cols := O m y
  have memO {k} (z : Fin 4 ↪ Fin k) (i : Fin k) :
      i ∈ O k z ↔ (i ≠ z 0 ∧ i ≠ z 1 ∧ i ≠ z 2) ∧ i ≠ z 3 := by simp [O, and_assoc]
  have memT {k} (z : Fin 4 ↪ Fin k) (i : Fin k) :
      (i = z 3 ∨ i ∈ O k z) ↔ (i ≠ z 0 ∧ i ≠ z 1 ∧ i ≠ z 2) := by
    by_cases hi : i = z 3
    · subst i; simp [z.injective.eq_iff]
    · simp [memO, hi]
  have hr : x 3 ∉ rows := by simp [rows, memO]
  have hc : y 3 ∉ cols := by simp [cols, memO]
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := projectionCovers rows cols A (x 3) (y 3) hr hc
    (by
      intro i hi
      obtain ⟨j, hj, ha⟩ := eRow i ((memO x i).mp hi).1 ((memO x i).mp hi).2
      exact ⟨j,(memT y j).mpr hj,ha⟩)
    (by
      intro i hi j k hj hk
      exact uRow i j k ((memO x i).mp hi).1 ((memT y j).mp hj) ((memT y k).mp hk))
    (by
      intro j hj
      obtain ⟨i, hi, ha⟩ := eCol j ((memO y j).mp hj).1 ((memO y j).mp hj).2
      exact ⟨i,(memT x i).mpr hi,ha⟩)
    (by
      intro j hj i k hi hk
      exact uCol j i k ((memO y j).mp hj).1 ((memT x i).mp hi) ((memT x k).mp hk))
  let rs := specialRows rows A (y 3)
  let cs := specialCols cols A (x 3)
  let es := outsideEdges rows cols A
  have rn : rows.card + 4 = n := card_outside_four x
  have cn : cols.card + 4 = m := card_outside_four y
  have rc : rows.card = rs.card + es.card := card_split_proj rows rs es h1 h2 h3
  have cc : cols.card = cs.card + es.card := card_split_snd cols cs es h4 h5 h6
  apply of_lists A x y rs.toList cs.toList es.toList _ _ _ _ borderR borderC corner
  · intro i
    apply Bool.eq_iff_iff.mpr
    simp [rs, specialRows, rows, O, PEqualNP.Outside.Selector29722.outside4, and_assoc]
  · intro j
    apply Bool.eq_iff_iff.mpr
    simp [cs, specialCols, cols, O, PEqualNP.Outside.Selector29722.outside4, and_assoc]
  · intro i j
    apply Bool.eq_iff_iff.mpr
    simp [es, outsideEdges, rows, cols, O, PEqualNP.Outside.Selector29722.outside4, and_assoc]
  · simp only [Finset.length_toList]
    omega
