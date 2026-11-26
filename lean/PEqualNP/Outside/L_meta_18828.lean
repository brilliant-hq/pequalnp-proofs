import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18828

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def index {n : ℕ} (f : Fin n → Fin n) (i : ℕ) : ℕ :=
  if bound : i < n then (f ⟨i, bound⟩).val else i

def gate {n : ℕ} (f : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (index f)⟩

def runStep {α : Type*} (op : GateOp → List α → α) (d : α) (w : List α) (g : Gate) : List α :=
  w ++ [op g.op (g.inputs.map fun j => w.getD j d)]


theorem readInput {α : Type*} (d : α) {n : ℕ} (f : Fin n → Fin n) (x : Fin n → α)
    (tail : List α) (i : ℕ) :
    (List.ofFn x ++ tail).getD (index f i) d =
      (List.ofFn (x ∘ f) ++ tail).getD i d := by
  by_cases h : i < n
  · have leftBound : (f ⟨i, h⟩).val < (List.ofFn x).length := by simp
    have rightBound : i < (List.ofFn (x ∘ f)).length := by simpa using h
    rw [index, dite_eq_left h, List.getD_append _ _ _ _ leftBound,
      List.getD_append _ _ _ _ rightBound,
      List.getD_eq_getElem _ _ leftBound, List.getD_eq_getElem _ _ rightBound,
      List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · have l : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt h
    have r : (List.ofFn (x ∘ f)).length ≤ i := by simpa using Nat.le_of_not_lt h
    rw [index, dite_eq_right h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right l,
      List.getElem?_append_right r, List.length_ofFn]

theorem readAfter {α : Type*} (op : GateOp → List α → α) (d : α) {n : ℕ} (f : Fin n → Fin n) (x : Fin n → α)
    (gs : List Gate) (tail : List α) (i : ℕ) :
    ((gs.map (gate f)).foldl (runStep op d) (List.ofFn x ++ tail)).getD (index f i) d =
      (gs.foldl (runStep op d) (List.ofFn (x ∘ f) ++ tail)).getD i d := by
  induction gs generalizing tail with
  | nil => exact readInput d f x tail i
  | cons g gs ih =>
    let v := op g.op (g.inputs.map fun j => (List.ofFn (x ∘ f) ++ tail).getD j d)
    have matchGate :
        op (gate f g).op ((gate f g).inputs.map fun j => (List.ofFn x ++ tail).getD j d) = v := by
      simp only [gate, List.map_map, v]
      congr 1
      exact List.map_congr_left (fun j _ => readInput d f x tail j)
    simp only [List.map_cons, List.foldl_cons, runStep, matchGate]
    simpa only [List.append_assoc] using ih (tail ++ [v])


private theorem indexBefore {n j i : ℕ} (f : Fin n → Fin n) (bound : i < n + j) :
    index f i < n + j := by
  by_cases h : i < n
  · simp only [index, dite_eq_left h]
    have valid := (f ⟨i,h⟩).isLt
    omega
  · simpa only [index, dite_eq_right h] using bound

private abbrev Side := Fin 13
private abbrev In := Fin (13+13)
private def incidence (p l : Side) : Prop := p ∈ PEqualNP.HeptadCover.singerLines3 l
instance (p l : Side) : Decidable (incidence p l) := by unfold incidence; infer_instance

private def graph (x : In → Bool) : Prop :=
  ∃ p l : Side, incidence p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

private def shift (c : Side) : In → In :=
  Fin.addCases (fun p => Fin.castAdd 13 (p-c)) (fun l => Fin.natAdd 13 (l-c))

private def flip (c : Side) : In → In :=
  Fin.addCases (fun p => Fin.natAdd 13 (c-p)) (fun l => Fin.castAdd 13 (c-l))

private def toZero (s : In) : In → In := Fin.addCases shift flip s
private def inverse (s : In) : In → In := Fin.addCases (fun c => shift (-c)) flip s

set_option maxRecDepth 18000 in
set_option maxHeartbeats 35000000 in
private theorem inverses : ∀ s k : In, inverse s (toZero s k) = k ∧ toZero s (inverse s k) = k := by
  decide +kernel

private theorem sendsZero : ∀ s : In, toZero s s = 0 := by decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 40000000 in
private theorem shiftInc : ∀ c p l : Side, incidence p l ↔ incidence (p-c) (l-c) := by
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 40000000 in
private theorem flipInc : ∀ c p l : Side, incidence p l ↔ incidence (c-l) (c-p) := by
  decide +kernel

private theorem subtractAdd : ∀ a c : Side, a+c-c = a := by decide +kernel
private theorem subtractTwice : ∀ a c : Side, c-(c-a) = a := by decide +kernel

private theorem keepsShift (c : Side) (x : In → Bool) : graph (x ∘ shift c) ↔ graph x := by
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨p-c,l-c,(shiftInc c p l).mp e,
      by simpa only [Function.comp_apply, shift, Fin.addCases_left, Fin.addCases_right] using hp,
      by simpa only [Function.comp_apply, shift, Fin.addCases_left, Fin.addCases_right] using hl⟩
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨p+c,l+c,(shiftInc c (p+c) (l+c)).mpr (by simpa [subtractAdd] using e),
      by simpa only [Function.comp_apply, shift, Fin.addCases_left, Fin.addCases_right, subtractAdd] using hp,
      by simpa only [Function.comp_apply, shift, Fin.addCases_left, Fin.addCases_right, subtractAdd] using hl⟩

private theorem keepsFlip (c : Side) (x : In → Bool) : graph (x ∘ flip c) ↔ graph x := by
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨c-l,c-p,(flipInc c p l).mp e,
      by simpa only [Function.comp_apply, flip, Fin.addCases_left, Fin.addCases_right] using hl,
      by simpa only [Function.comp_apply, flip, Fin.addCases_left, Fin.addCases_right] using hp⟩
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨c-l,c-p,(flipInc c (c-l) (c-p)).mpr (by simpa [subtractTwice] using e),
      by simpa only [Function.comp_apply, flip, Fin.addCases_left, Fin.addCases_right, subtractTwice] using hl,
      by simpa only [Function.comp_apply, flip, Fin.addCases_left, Fin.addCases_right, subtractTwice] using hp⟩

private theorem keeps (s : In) (x : In → Bool) : graph (x ∘ toZero s) ↔ graph x :=
  Fin.addCases
    (fun c => by simpa only [toZero, Fin.addCases_left] using keepsShift c x)
    (fun c => by simpa only [toZero, Fin.addCases_right] using keepsFlip c x) s

end PEqualNP.Outside.L_meta_18828

open PEqualNP.Outside.L_meta_18828 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18828 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → ∃ (x5 : Fin (26 : ℕ) → Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), Function.Bijective x5 ∧ x5 x2 = (0 : Fin (26 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size = x3.size ∧ (∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = x3.eval (List.ofFn (x7 ∘ x5))) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x1 (x7 ∘ x5) ↔ x1 x7 := by
  dsimp only
  intro s C ao
  let f := toZero s
  let D : Circuit := ⟨C.gates.map (gate f), index f C.output⟩
  have perm : Function.Bijective f := ⟨
    (fun i j e => by simpa only [f,(inverses s i).1,(inverses s j).1] using congrArg (inverse s) e),
    (fun i => ⟨inverse s i,(inverses s i).2⟩)⟩
  have len : D.size = C.size := by simp [D,Circuit.size]
  have member (h : Gate) (mem : h ∈ D.gates) : ∃ g ∈ C.gates, h = gate f g := by
    obtain ⟨g,hg,e⟩ := List.mem_map.mp mem
    exact ⟨g,hg,e.symm⟩
  refine ⟨f,D,perm,sendsZero s,⟨?_,?_,?_⟩,len,?_,keeps s⟩
  · intro h mem
    obtain ⟨g,hg,rfl⟩ := member h mem
    exact ao.1 g hg
  · intro k hk i hi
    have hk' : k < C.gates.length := by simpa [D] using hk
    change i ∈ ((C.gates.map (gate f)).getD k ⟨.or, []⟩).inputs at hi
    rw [List.getD_eq_getElem _ _ hk, List.getElem_map] at hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    apply indexBefore f
    apply ao.2.1 k hk' w
    simpa only [gateAt, List.getD_eq_getElem _ _ hk'] using hw
  · intro h mem
    obtain ⟨g,hg,rfl⟩ := member h mem
    simpa only [gate,List.length_map] using ao.2.2 g hg
  · intro x
    have h := readAfter GateOp.eval false f x C.gates [] C.output
    unfold runStep at h
    simpa only [D,Circuit.eval,Circuit.wires,List.append_nil] using h

