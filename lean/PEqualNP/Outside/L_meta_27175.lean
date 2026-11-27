import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27175_aux

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) ||
  (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def toggle (i : Fin 9) (x : Fin 9 → Bool) (j : Fin 9) : Bool :=
  if j = i then !x j else x j

def matchingWitness (i : Fin 9) (j : Fin 9) : Bool :=
  let a := i.val / 3
  let b := i.val % 3
  j.val % 3 = (j.val / 3 + b + 3 - a) % 3

private theorem matchingWitnessValid : ∀ i : Fin 9,
    matching (matchingWitness i) ≠ matching (toggle i (matchingWitness i)) := by decide

theorem everyInputEssential : ∀ i : Fin 9, ∃ x : Fin 9 → Bool,
    matching x ≠ matching (toggle i x) :=
  fun i => ⟨matchingWitness i, matchingWitnessValid i⟩

theorem wireCount (reads : List Nat) (g b : Nat)
    (lengthReads : reads.length = g + b)
    (coverage : ∀ i, 0 < i → i < g + 8 → i ∈ reads) :
    7 + reads.count 0 ≤ b ∧
    (b = 7 + reads.count 0 → (reads.filter fun i => !(i == 0)).Nodup) := by
  let rs := reads.filter fun i => !(i == 0)
  have hlen : reads.length = reads.count 0 + rs.length := by
    simp only [rs, List.count_eq_countP, ← List.countP_eq_length_filter]
    exact List.length_eq_countP_add_countP (fun i => i == 0)
  have hs : (Finset.range (g + 8)).erase 0 ⊆ rs.toFinset := by
    intro i hi
    have ne := Finset.ne_of_mem_erase hi
    have lt := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hm := coverage i (by omega) lt
    simp [rs, ne, hm]
  have hcard : ((Finset.range (g + 8)).erase 0).card = g + 7 := by
    have hh := Finset.card_erase_add_one (s := Finset.range (g + 8)) (a := 0) (by simp)
    simp only [Finset.card_range] at hh
    omega
  have hle := Finset.card_le_card hs
  rw [hcard] at hle
  have hslen := rs.toFinset_card_le
  refine ⟨by omega, fun hb => ?_⟩
  change rs.Nodup
  apply List.nodup_iff_length_dedup_eq.mpr
  rw [← List.card_toFinset]
  omega

def path (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def restrict (x : Fin 4 → Bool) (j : Fin 9) : Bool :=
  if j = 1 then x 0 else if j = 3 then x 1 else
  if j = 2 then x 2 else if j = 4 then x 3 else
  j = 6 || j = 7 || j = 8

theorem matchingRestriction : ∀ x : Fin 4 → Bool, matching (restrict x) = path x := by
  decide

def mix (part u v : Fin 4 → Bool) (j : Fin 4) : Bool :=
  if part j then u j else v j

def nontrivial (part : Fin 4 → Bool) : Prop :=
  (∃ i, part i = true) ∧ (∃ i, part i = false)

def code (part : Fin 4 → Bool) : Nat :=
  (part 0).toNat + 2 * (part 1).toNat + 4 * (part 2).toNat + 8 * (part 3).toNat

def splitPair (part : Fin 4 → Bool) (target : Bool) : Nat × Nat :=
  let pairs := if target then
    [(0,0),(6,3),(12,3),(6,3),(3,6),(3,12),(3,6),(12,3),
      (3,12),(3,12),(12,3),(6,3),(3,6),(3,12),(3,6),(0,0)]
  else
    [(0,0),(1,2),(2,1),(2,4),(4,2),(1,2),(2,1),(4,8),
      (8,4),(1,2),(2,1),(2,4),(4,2),(1,2),(2,1),(0,0)]
  pairs.getD (code part) (0,0)

def fromCode (n : Nat) (j : Fin 4) : Bool := n.testBit j.val

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
theorem splitTableValid : ∀ part : Fin 4 → Bool, nontrivial part →
    ∀ target : Bool,
      let u := fromCode (splitPair part target).1
      let v := fromCode (splitPair part target).2
      path u = target ∧ path v = target ∧ path (mix part u v) = !target := by
  unfold nontrivial
  decide

theorem splitWitnesses : ∀ part : Fin 4 → Bool, nontrivial part →
    ∀ target : Bool, ∃ u v : Fin 4 → Bool,
      path u = target ∧ path v = target ∧ path (mix part u v) = !target := by
  intro part hp target
  exact ⟨_, _, splitTableValid part hp target⟩

theorem noAndSplit (f g : (Fin 4 → Bool) → Bool)
    (s : Fin 4 → Bool) (hs : nontrivial s)
    (hf : ∀ u v, f (mix s u v) = f u)
    (hg : ∀ u v, g (mix s u v) = g v) :
    ¬ (∀ x, path x = (f x && g x)) := by
  intro h
  obtain ⟨u, v, hu, hv, hm⟩ := splitWitnesses s hs true
  have fu : f u = true := (Bool.and_eq_true_iff.mp ((h u).symm.trans hu)).1
  have gv : g v = true := (Bool.and_eq_true_iff.mp ((h v).symm.trans hv)).2
  rw [h, hf, hg, fu, gv] at hm
  contradiction

theorem noOrSplit (f g : (Fin 4 → Bool) → Bool)
    (s : Fin 4 → Bool) (hs : nontrivial s)
    (hf : ∀ u v, f (mix s u v) = f u)
    (hg : ∀ u v, g (mix s u v) = g v) :
    ¬ (∀ x, path x = (f x || g x)) := by
  intro h
  obtain ⟨u, v, hu, hv, hm⟩ := splitWitnesses s hs false
  have fu : f u = false := (Bool.or_eq_false_iff.mp ((h u).symm.trans hu)).1
  have gv : g v = false := (Bool.or_eq_false_iff.mp ((h v).symm.trans hv)).2
  rw [h, hf, hg, fu, gv] at hm
  contradiction

inductive Formula where
  | const (b : Bool)
  | var (i : Fin 4)
  | neg (f : Formula)
  | both (f g : Formula)
  | either (f g : Formula)

def Formula.eval (x : Fin 4 → Bool) : Formula → Bool
  | .const b => b
  | .var i => x i
  | .neg f => !f.eval x
  | .both f g => f.eval x && g.eval x
  | .either f g => f.eval x || g.eval x

def Formula.vars : Formula → Finset (Fin 4)
  | .const _ => ∅
  | .var i => {i}
  | .neg f => f.vars
  | .both f g | .either f g => f.vars ∪ g.vars

def Formula.linear : Formula → Prop
  | .const _ | .var _ => True
  | .neg f => f.linear
  | .both f g | .either f g => f.linear ∧ g.linear ∧ Disjoint f.vars g.vars

theorem Formula.eval_congr (f : Formula) (x y : Fin 4 → Bool)
    (h : ∀ i ∈ f.vars, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | const b => rfl
  | var i => exact h i (by simp [vars])
  | neg f ih => simp only [eval, ih h]
  | both f g ihf ihg =>
    simp only [eval, ihf (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihg (fun i hi => h i (Finset.mem_union_right _ hi))]
  | either f g ihf ihg =>
    simp only [eval, ihf (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihg (fun i hi => h i (Finset.mem_union_right _ hi))]

private theorem path_nonconstant : ∀ b : Bool, ¬ (∀ x : Fin 4 → Bool, path x = b) := by decide

private theorem path_not_literal : ∀ (i : Fin 4) (b : Bool),
    ¬ (∀ x : Fin 4 → Bool, path x = (if b then !x i else x i)) := by decide

private theorem constant_eval (f : Formula) (h : f.vars = ∅) (x : Fin 4 → Bool) :
    f.eval x = f.eval (fun _ => false) :=
  f.eval_congr _ _ (by simp [h])

private theorem disjoint_eval (f g : Formula) (hd : Disjoint f.vars g.vars)
    (u v : Fin 4 → Bool) :
    let s := fun i => decide (i ∈ f.vars)
    f.eval (mix s u v) = f.eval u ∧ g.eval (mix s u v) = g.eval v := by
  constructor
  · apply f.eval_congr
    intro i hi
    simp [mix, hi]
  · apply g.eval_congr
    intro i hi
    have hn : i ∉ f.vars := fun hf => (Finset.disjoint_left.mp hd) hf hi
    simp [mix, hn]

private theorem split_nontrivial (f g : Formula) (hd : Disjoint f.vars g.vars)
    (hf : f.vars ≠ ∅) (hg : g.vars ≠ ∅) : nontrivial (fun i => decide (i ∈ f.vars)) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hf
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hg
  refine ⟨⟨i, by simp [hi]⟩, ⟨j, ?_⟩⟩
  have hn : j ∉ f.vars := fun h => Finset.disjoint_left.mp hd h hj
  simp [hn]

private theorem noBinary (f g : Formula) (hd : Disjoint f.vars g.vars)
    (hf : f.vars ≠ ∅) (hg : g.vars ≠ ∅) (isAnd negated : Bool) :
    ¬ (∀ x, path x =
      (if negated then !(if isAnd then f.eval x && g.eval x else f.eval x || g.eval x)
        else (if isAnd then f.eval x && g.eval x else f.eval x || g.eval x))) := by
  let s : Fin 4 → Bool := fun i => decide (i ∈ f.vars)
  have hs : nontrivial s := split_nontrivial f g hd hf hg
  have h1 : ∀ u v, f.eval (mix s u v) = f.eval u := fun u v => (disjoint_eval f g hd u v).1
  have h2 : ∀ u v, g.eval (mix s u v) = g.eval v := fun u v => (disjoint_eval f g hd u v).2
  cases isAnd <;> cases negated
  · simpa using noOrSplit (fun x => f.eval x) (fun x => g.eval x) s hs h1 h2
  · simpa [Bool.not_or] using noAndSplit (fun x => !f.eval x) (fun x => !g.eval x) s hs
      (fun u v => congrArg Bool.not (h1 u v)) (fun u v => congrArg Bool.not (h2 u v))
  · simpa using noAndSplit (fun x => f.eval x) (fun x => g.eval x) s hs h1 h2
  · simpa [Bool.not_and] using noOrSplit (fun x => !f.eval x) (fun x => !g.eval x) s hs
      (fun u v => congrArg Bool.not (h1 u v)) (fun u v => congrArg Bool.not (h2 u v))

theorem noLinearFormula (f : Formula) (hf : f.linear) (negated : Bool) :
    ¬ (∀ x, path x = (if negated then !f.eval x else f.eval x)) := by
  induction f generalizing negated with
  | const b => simpa [Formula.eval] using path_nonconstant (if negated then !b else b)
  | var i => exact path_not_literal i negated
  | neg f ih =>
    cases negated
    · simpa [Formula.eval] using ih hf true
    · simpa [Formula.eval] using ih hf false
  | both f g ihf ihg =>
    obtain ⟨hf, hg, hd⟩ := hf
    by_cases ef : f.vars = ∅
    · have ec := constant_eval f ef
      cases ev : f.eval (fun _ => false)
      · simpa [Formula.eval, ec, ev] using path_nonconstant (if negated then true else false)
      · simpa [Formula.eval, ec, ev] using ihg hg negated
    by_cases eg : g.vars = ∅
    · have ec := constant_eval g eg
      cases ev : g.eval (fun _ => false)
      · simpa [Formula.eval, ec, ev] using path_nonconstant (if negated then true else false)
      · simpa [Formula.eval, ec, ev] using ihf hf negated
    simpa [Formula.eval] using noBinary f g hd ef eg true negated
  | either f g ihf ihg =>
    obtain ⟨hf, hg, hd⟩ := hf
    by_cases ef : f.vars = ∅
    · have ec := constant_eval f ef
      cases ev : f.eval (fun _ => false)
      · simpa [Formula.eval, ec, ev] using ihg hg negated
      · simpa [Formula.eval, ec, ev] using path_nonconstant (if negated then false else true)
    by_cases eg : g.vars = ∅
    · have ec := constant_eval g eg
      cases ev : g.eval (fun _ => false)
      · simpa [Formula.eval, ec, ev] using ihf hf negated
      · simpa [Formula.eval, ec, ev] using path_nonconstant (if negated then false else true)
    simpa [Formula.eval] using noBinary f g hd ef eg false negated

open PEqualNP.CircuitLowerBounds

def readFormula (rs : List Formula) (i : Nat) : Formula := rs.getD i (.const false)

def gateFormula (rs : List Formula) (g : Gate) : Formula :=
  match g.op, g.inputs with
  | .not, [a] => .neg (readFormula rs a)
  | .and, [a, b] => .both (readFormula rs a) (readFormula rs b)
  | .or, [a, b] => .either (readFormula rs a) (readFormula rs b)
  | _, _ => .const false

def gateOK (g : Gate) : Prop :=
  (∃ a, g.op = .not ∧ g.inputs = [a]) ∨
  (∃ a b, a < b ∧ (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a,b])

def active (rs : List Formula) (live : List Nat) : Prop :=
  (∀ i ∈ live, (readFormula rs i).linear) ∧
  ∀ i ∈ live, ∀ j ∈ live, i ≠ j → Disjoint (readFormula rs i).vars (readFormula rs j).vars

private theorem noRepeat (head tail : List Nat) (h : ((head ++ tail).filter fun i => !(i == 0)).Nodup)
    {i : Nat} (hh : i ∈ head) (ht : i ∈ tail) : i = 0 := by
  by_contra hn
  rw [List.filter_append, List.nodup_append] at h
  have hhead : i ∈ head.filter (fun i => !(i == 0)) := by simp [hh, hn]
  have htail : i ∈ tail.filter (fun i => !(i == 0)) := by simp [ht, hn]
  exact h.2.2 i hhead i htail rfl

private theorem newRegister (r : List Formula) (f : Formula) (i : Nat) :
    readFormula (r ++ [f]) i = if i = r.length then f else readFormula r i := by
  by_cases h : i < r.length
  · rw [ite_eq_right (Nat.ne_of_lt h)]
    exact List.getD_append _ _ _ _ h
  by_cases he : i = r.length
  · subst i
    simp [readFormula]
  · have hi : r.length + 1 ≤ i := by omega
    have hi' : (r ++ [f]).length ≤ i := by simpa using hi
    rw [ite_eq_right he]
    simp only [readFormula, List.getD_eq_default _ _ hi', List.getD_eq_default _ _ (by omega : r.length ≤ i)]

private theorem gateActive (rs : List Formula) (g : Gate) (tail : List Nat)
    (ok : gateOK g) (act : active rs (g.inputs ++ tail))
    (once : ((g.inputs ++ tail).filter fun i => !(i == 0)).Nodup)
    (zero : (readFormula rs 0).vars = ∅) :
    (gateFormula rs g).linear ∧ ∀ j ∈ tail,
      Disjoint (gateFormula rs g).vars (readFormula rs j).vars := by
  have lin : ∀ i ∈ g.inputs, (readFormula rs i).linear :=
    fun i hi => act.1 i (List.mem_append_left _ hi)
  have d : ∀ i ∈ g.inputs, ∀ j ∈ tail,
      Disjoint (readFormula rs i).vars (readFormula rs j).vars := by
    intro i hi j hj
    by_cases he : i = j
    · subst j
      have hz := noRepeat g.inputs tail once hi hj
      simp [hz, zero]
    · exact act.2 i (List.mem_append_left _ hi) j (List.mem_append_right _ hj) he
  rcases ok with ⟨a, hOp, hi⟩ | ⟨a, b, hl, hOp, hi⟩
  · simpa [gateFormula, hOp, hi, Formula.linear, Formula.vars] using
      And.intro (lin a (by simp [hi])) (d a (by simp [hi]))
  · have ha : a ∈ g.inputs := by simp [hi]
    have hb : b ∈ g.inputs := by simp [hi]
    have hd := act.2 a (List.mem_append_left _ ha) b (List.mem_append_left _ hb) (Nat.ne_of_lt hl)
    rcases hOp with hOp | hOp <;>
      simpa [gateFormula, hOp, hi, Formula.linear, Formula.vars, Finset.disjoint_union_left] using
        And.intro (And.intro (lin a ha) (And.intro (lin b hb) hd))
          (fun j hj => And.intro (d a ha j hj) (d b hb j hj))

def compile (gs : List Gate) (rs : List Formula) : List Formula :=
  gs.foldl (fun r g => r ++ [gateFormula r g]) rs

private theorem gateEval (rs : List Formula) (x : Fin 4 → Bool) (g : Gate) (ok : gateOK g) :
    (gateFormula rs g).eval x =
      g.op.eval (g.inputs.map fun i => (rs.map (Formula.eval x)).getD i false) := by
  have e (i : Nat) : (rs.map (Formula.eval x)).getD i false = (readFormula rs i).eval x :=
    List.getD_map rs (.const false) (Formula.eval x)
  rcases ok with ⟨a, hop, hi⟩ | ⟨a, b, _, hop, hi⟩
  · simp only [gateFormula, hi, hop, Formula.eval, GateOp.eval, List.map_cons, List.map_nil, e]
    rfl
  · rcases hop with hop | hop <;>
      simp only [gateFormula, hi, hop, Formula.eval, GateOp.eval, List.map_cons, List.map_nil, e] <;>
      simp [List.all, List.any]

theorem compileEval (gs : List Gate) (rs : List Formula) (x : Fin 4 → Bool)
    (ok : ∀ g ∈ gs, gateOK g) :
    (compile gs rs).map (Formula.eval x) =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (rs.map (Formula.eval x)) := by
  induction gs generalizing rs with
  | nil => rfl
  | cons g gs ih =>
    change (compile gs (rs ++ [gateFormula rs g])).map (Formula.eval x) = _
    rw [ih _ (fun g' h => ok g' (by simp [h]))]
    simp [gateEval rs x g (ok g (by simp))]

theorem compileLinear (gs : List Gate) (out : Nat) (rs : List Formula)
    (ok : ∀ g ∈ gs, gateOK g) (nonempty : 0 < rs.length)
    (zero : (readFormula rs 0).vars = ∅)
    (act : active rs (gs.flatMap Gate.inputs ++ [out]))
    (once : ((gs.flatMap Gate.inputs ++ [out]).filter fun i => !(i == 0)).Nodup) :
    (readFormula (compile gs rs) out).linear := by
  induction gs generalizing rs with
  | nil => exact act.1 out (by simp)
  | cons g gs ih =>
    let tail := gs.flatMap Gate.inputs ++ [out]
    let f := gateFormula rs g
    have ha : active rs (g.inputs ++ tail) := by
      simpa [tail, List.append_assoc] using act
    have hn : ((g.inputs ++ tail).filter fun i => !(i == 0)).Nodup := by
      simpa [tail, List.append_assoc] using once
    have hf := gateActive rs g tail (ok g (by simp)) ha hn zero
    have htail : (tail.filter fun i => !(i == 0)).Nodup := by
      rw [List.filter_append, List.nodup_append] at hn
      exact hn.2.1
    change (readFormula (compile gs (rs ++ [f])) out).linear
    apply ih (rs := rs ++ [f]) (fun g' hg' => ok g' (by simp [hg']))
      (by simp) (by simpa [newRegister, Nat.ne_of_lt nonempty] using zero) _ htail
    constructor
    · intro i hi
      rw [newRegister]
      split
      · exact hf.1
      · exact ha.1 i (List.mem_append_right _ hi)
    · intro i hi j hj hij
      simp only [newRegister]
      by_cases he : i = rs.length
      · have hn : j ≠ rs.length := fun hj' => hij (he.trans hj'.symm)
        simpa [he, hn] using hf.2 j hj
      · by_cases hj' : j = rs.length
        · simpa [he, hj'] using (hf.2 i hi).symm
        · simpa [he, hj'] using ha.2 i (List.mem_append_right _ hi) j
            (List.mem_append_right _ hj) hij

def initial : List Formula :=
  [.const false, .var 0, .var 2, .var 1, .var 3, .const false,
    .const true, .const true, .const true]

private theorem initialLinearSmall : ∀ i : Fin 9, (readFormula initial i.val).linear := by
  intro i
  fin_cases i <;> trivial

private theorem initialDisjointSmall : ∀ i j : Fin 9, i ≠ j →
    Disjoint (readFormula initial i.val).vars (readFormula initial j.val).vars := by decide

private theorem initialActive (live : List Nat) : active initial live := by
  have hlen : initial.length = 9 := rfl
  have no (i : Nat) (h : ¬ i < 9) : readFormula initial i = .const false :=
    List.getD_eq_default _ _ (by omega)
  constructor
  · intro i _
    by_cases hi : i < 9
    · exact initialLinearSmall ⟨i, hi⟩
    · simp [no i hi, Formula.linear]
  · intro i _ j _ hij
    by_cases hi : i < 9
    · by_cases hj : j < 9
      · exact initialDisjointSmall ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))
      · simp [no j hj, Formula.vars]
    · simp [no i hi, Formula.vars]

private theorem initialMap : ∀ x : Fin 4 → Bool,
    initial.map (Formula.eval x) = List.ofFn (restrict x) := by decide

theorem circuitMustShare (c : Circuit) (ok : ∀ g ∈ c.gates, gateOK g)
    (computes : ∀ x : Fin 9 → Bool, c.eval (List.ofFn x) = matching x) :
    ¬ ((c.gates.flatMap Gate.inputs ++ [c.output]).filter fun i => !(i == 0)).Nodup := by
  intro once
  let f := readFormula (compile c.gates initial) c.output
  have hf : f.linear := compileLinear c.gates c.output initial ok (by decide) rfl (initialActive _) once
  apply noLinearFormula f hf false
  intro x
  change path x = f.eval x
  rw [← matchingRestriction, ← computes]
  unfold Circuit.eval Circuit.wires
  rw [← initialMap, ← compileEval _ _ _ ok]
  exact List.getD_map _ (.const false) (Formula.eval x)

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [gateValue v g]) w

private theorem runCongr (gs : List Gate) (u v : List Bool) (excluded : Nat)
    (rel : Bool → Bool → Prop) (reflFalse : rel false false)
    (len : u.length = v.length)
    (inputs : ∀ j ≠ excluded, rel (u.getD j false) (v.getD j false))
    (step : ∀ g ∈ gs, excluded ∉ g.inputs ∧ ∀ w z : List Bool,
      (∀ j ∈ g.inputs, rel (w.getD j false) (z.getD j false)) →
        rel (gateValue w g) (gateValue z g)) :
    ∀ i ≠ excluded, rel ((run gs u).getD i false) ((run gs v).getD i false) := by
  induction gs generalizing u v with
  | nil => exact inputs
  | cons g gs ih =>
    obtain ⟨hn, hstep⟩ := step g (by simp)
    have hv := hstep u v (fun j hj => inputs j (fun h => hn (h ▸ hj)))
    refine ih (u ++ [gateValue u g]) (v ++ [gateValue v g]) (by simp [len]) ?_
      (fun g' hg' => step g' (by simp [hg']))
    intro j hj
    by_cases hlt : j < u.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (len ▸ hlt)]
      exact inputs j hj
    by_cases he : j = u.length
    · subst j
      have hl : v.length ≤ u.length := by omega
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), List.getD_append_right _ _ _ _ hl]
      simpa [len] using hv
    · have hu : (u ++ [gateValue u g]).length ≤ j := by simp; omega
      have hv' : (v ++ [gateValue v g]).length ≤ j := by simp [← len]; omega
      rw [List.getD_eq_default _ _ hu, List.getD_eq_default _ _ hv']
      exact reflFalse

private theorem gateEq (g : Gate) (w z : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = z.getD i false) :
    gateValue w g = gateValue z g := by
  unfold gateValue
  congr 1
  exact List.map_congr_left h

theorem essentialRead (c : Circuit) (computes : ∀ x : Fin 9 → Bool,
    c.eval (List.ofFn x) = matching x) (i : Fin 9) (hout : c.output ≠ i.val) :
    i.val ∈ c.gates.flatMap Gate.inputs := by
  by_contra h
  obtain ⟨x, hx⟩ := everyInputEssential i
  apply hx
  rw [← computes, ← computes]
  have eqs : ∀ j ≠ i.val, (List.ofFn x).getD j false = (List.ofFn (toggle i x)).getD j false := by
    intro j hj
    by_cases hj' : j < 9
    · have hne : (⟨j, hj'⟩ : Fin 9) ≠ i := fun h => hj (congrArg Fin.val h)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hj',
        Option.getD_some, toggle, ite_eq_right hne]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hj', Option.getD_none]
  exact runCongr c.gates (List.ofFn x) (List.ofFn (toggle i x)) i.val Eq rfl (by simp) eqs
    (fun g hg => ⟨fun hi => h (List.mem_flatMap.mpr ⟨g, hg, hi⟩), gateEq g⟩) c.output hout

def unaryCount (gs : List Gate) : Nat := gs.countP (fun g => g.inputs.length == 1)

theorem readsLength (gs : List Gate) (ok : ∀ g ∈ gs, gateOK g) :
    (gs.flatMap Gate.inputs).length + unaryCount gs = 2 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hh := ih (fun k hk => ok k (by simp [hk]))
    rcases ok g (by simp) with ⟨a, _, h⟩ | ⟨a, b, _, _, h⟩ <;>
      simp only [List.flatMap_cons, List.length_append, unaryCount, List.countP_cons, h,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceBEq, ite_true,
        Bool.false_eq_true, ite_false] at hh ⊢ <;> omega

theorem binaryOfNoUnary (gs : List Gate) (zero : unaryCount gs = 0) (g : Gate) (hg : g ∈ gs)
    (ok : gateOK g) : ∃ a b, (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a,b] := by
  rcases ok with ⟨a, _, ha⟩ | ⟨a, b, _, hab, h⟩
  · exfalso
    have hpos : 0 < unaryCount gs := by
      unfold unaryCount
      apply List.countP_pos_iff.mpr
      exact ⟨g, hg, by simp [ha]⟩
    omega
  · exact ⟨a, b, hab, h⟩

private theorem binaryMonotone (g : Gate) (a b : Nat)
    (op : g.op = .and ∨ g.op = .or) (hi : g.inputs = [a,b])
    (w z : List Bool) (h : ∀ i ∈ g.inputs, w.getD i false ≤ z.getD i false) :
    gateValue w g ≤ gateValue z g := by
  have ha := h a (by simp [hi])
  have hb := h b (by simp [hi])
  rcases op with hop | hop
  · have monotone : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by decide
    simpa only [gateValue, hop, hi, GateOp.eval, List.map_cons, List.map_nil, List.all,
      id_eq, Bool.and_true] using monotone _ _ _ _ ha hb
  · have monotone : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
    simpa only [gateValue, hop, hi, GateOp.eval, List.map_cons, List.map_nil, List.any,
      id_eq, Bool.or_false] using monotone _ _ _ _ ha hb

def firstAnd : Gate := ⟨.and, [0,1]⟩
def secondNot : Gate := ⟨.not, [0]⟩

private def withZero (i : Fin 9) : Bool := i = 0 || i = 4 || i = 8
private def withoutZero (i : Fin 9) : Bool := i = 4 || i = 8

private theorem twoGateComparison : ∀ i : Fin 11, i.val ≠ 0 →
    (run [firstAnd, secondNot] (List.ofFn withZero)).getD i.val false ≤
      (run [firstAnd, secondNot] (List.ofFn withoutZero)).getD i.val false := by decide

theorem andNeedsThirdRead (gs : List Gate) (out : Nat) (hout : out ≠ 0)
    (ok : ∀ g ∈ gs, gateOK g) (unary : unaryCount gs = 0)
    (comp : ∀ x : Fin 9 → Bool,
      (Circuit.mk (firstAnd :: secondNot :: gs) out).eval (List.ofFn x) = matching x) :
    0 ∈ gs.flatMap Gate.inputs := by
  by_contra hh
  let u := run [firstAnd, secondNot] (List.ofFn withZero)
  let v := run [firstAnd, secondNot] (List.ofFn withoutZero)
  have lenU : u.length = 11 := by decide
  have lenV : v.length = 11 := by decide
  have hu : ∀ j ≠ 0, u.getD j false ≤ v.getD j false := by
    intro j hj
    by_cases ht : j < 11
    · exact twoGateComparison ⟨j, ht⟩ hj
    · rw [List.getD_eq_default _ _ (by omega : u.length ≤ j),
        List.getD_eq_default _ _ (by omega : v.length ≤ j)]
  have he := runCongr gs u v 0 LE.le (by decide) (lenU.trans lenV.symm) hu
    (fun g hg => by
      obtain ⟨a, b, hop, hi⟩ := binaryOfNoUnary gs unary g hg (ok g hg)
      exact ⟨fun h => hh (List.mem_flatMap.mpr ⟨g, hg, h⟩), binaryMonotone g a b hop hi⟩) out hout
  change (Circuit.mk (firstAnd :: secondNot :: gs) out).eval (List.ofFn withZero) ≤
    (Circuit.mk (firstAnd :: secondNot :: gs) out).eval (List.ofFn withoutZero) at he
  rw [comp, comp] at he
  exact (by decide : ¬ matching withZero ≤ matching withoutZero) he

theorem noAndPrefix (c : Circuit) (size : c.size ≤ 11)
    (comp : ∀ x : Fin 9 → Bool, c.eval (List.ofFn x) = matching x)
    (out : c.output + 1 = 9 + c.size)
    (shape : ∀ j : Fin c.gates.length,
      ((c.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (c.gates.get j).inputs = [a]) ∨
      (((c.gates.get j).op = GateOp.and ∨ (c.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (c.gates.get j).inputs = [a,b]))
    (used : ∀ j : Fin c.gates.length, j.val + 1 < c.gates.length →
      ∃ k : Fin c.gates.length, j.val < k.val ∧ 9 + j.val ∈ (c.gates.get k).inputs)
    (head : c.gates.head? = some firstAnd) (next : c.gates.tail.head? = some secondNot) : False := by
  have prefixList : ∃ gs, c.gates = firstAnd :: secondNot :: gs := by
    cases h : c.gates with
    | nil => simp [h] at head
    | cons g gs =>
      have hg : g = firstAnd := by simpa [h] using head
      cases hh : gs with
      | nil => simp [h, hh] at next
      | cons k rest =>
        have hk : k = secondNot := by simpa [h, hh] using next
        exact ⟨rest, by simp [hg, hk]⟩
  obtain ⟨gs, hgs⟩ := prefixList
  let n := c.gates.length
  let reads := c.gates.flatMap Gate.inputs
  have hn : 2 ≤ n := by simp [n, hgs]
  have hn' : n ≤ 11 := size
  change c.output + 1 = 9 + n at out
  have ok : ∀ g ∈ c.gates, gateOK g := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
    rw [← hj]
    rcases shape j with ⟨hOp, a, _, hIn⟩ | ⟨hOp, a, b, hl, _, hIn⟩
    · exact Or.inl ⟨a, hOp, hIn⟩
    · exact Or.inr ⟨a, b, hl, hOp, hIn⟩
  have cover : ∀ i, 0 < i → i < n + 8 → i ∈ reads := by
    intro i _ hi
    by_cases il : i < 9
    · exact essentialRead c comp ⟨i, il⟩ (by change c.output ≠ i; omega)
    · let j : Fin c.gates.length := ⟨i - 9, by change i - 9 < n; omega⟩
      have hj : j.val + 1 < c.gates.length := by change i - 9 + 1 < n; omega
      obtain ⟨k, _, hk⟩ := used j hj
      change i ∈ c.gates.flatMap Gate.inputs
      apply List.mem_flatMap.mpr
      refine ⟨c.gates.get k, List.mem_iff_get.mpr ⟨k, rfl⟩, ?_⟩
      have h : 9 + j.val = i := by change 9 + (i - 9) = i; omega
      rwa [← h]
  have outputUnused : c.output ∉ reads := by
    intro hmem
    obtain ⟨g, hg, hi⟩ := List.mem_flatMap.mp hmem
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
    have hJ : j.val < n := j.isLt
    rw [← hj] at hi
    rcases shape j with ⟨_, a, ha, h⟩ | ⟨_, a, b, ha, hb, h⟩
    · rw [h] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    · rw [h] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi <;> omega
  have arity : reads.length + unaryCount c.gates = 2 * n := readsLength _ ok
  have hUnary : unaryCount c.gates = 1 + unaryCount gs := by
    simp [hgs, unaryCount, firstAnd, secondNot, Nat.add_comm]
  have huBound : unaryCount c.gates ≤ n := List.countP_le_length
  let b := n - unaryCount c.gates
  have lb : reads.length = n + b := by omega
  have ⟨lower, exactCount⟩ := wireCount reads n b lb cover
  have hs : reads.count 0 = 2 + (gs.flatMap Gate.inputs).count 0 := by
    simp [reads, hgs, firstAnd, secondNot]
    omega
  have exactB : b = 7 + reads.count 0 := by
    by_cases hu : unaryCount gs = 0
    · have hsok : ∀ g ∈ gs, gateOK g := fun g hg => ok g (by simp [hgs, hg])
      have cp : ∀ x : Fin 9 → Bool,
          (Circuit.mk (firstAnd :: secondNot :: gs) c.output).eval (List.ofFn x) = matching x := by
        intro x
        have h : (Circuit.mk (firstAnd :: secondNot :: gs) c.output) = c := by
          cases c
          simp_all
        rw [h, comp]
      have hThird := andNeedsThirdRead gs c.output (by omega) hsok hu cp
      have hc := List.count_pos_iff.mpr hThird
      omega
    · omega
  apply circuitMustShare c ok comp
  rw [List.filter_append, List.nodup_append]
  refine ⟨exactCount exactB, (by simp : ([c.output] : List Nat).Nodup).filter _, ?_⟩
  intro a ha z hz e
  have haa := (List.mem_filter.mp ha).1
  have hzz : z = c.output := by simpa using (List.mem_filter.mp hz).1
  exact outputUnused (e.trans hzz ▸ haa)

end PEqualNP.Outside.L_meta_27175_aux

theorem PEqualNP.Outside.L_meta_27175 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩)) := by
  rintro ⟨c, _, hs, hc, ho, hg, _, hu, hfirst, hsecond⟩
  exact PEqualNP.Outside.L_meta_27175_aux.noAndPrefix c hs hc ho hg hu hfirst hsecond
