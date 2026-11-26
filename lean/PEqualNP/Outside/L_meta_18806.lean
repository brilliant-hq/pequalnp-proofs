import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18806

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


private theorem indexInjective {n : ℕ} {f : Fin n → Fin n} (one : Function.Injective f) :
    Function.Injective (index f) := by
  intro i j eq
  by_cases hi : i < n <;> by_cases hj : j < n
  · simp only [index, dite_eq_left hi, dite_eq_left hj] at eq
    exact congrArg Fin.val (one (Fin.ext eq))
  · simp only [index, dite_eq_left hi, dite_eq_right hj] at eq
    exact (hj (eq ▸ (f ⟨i,hi⟩).isLt)).elim
  · simp only [index, dite_eq_right hi, dite_eq_left hj] at eq
    exact (hi (eq.symm ▸ (f ⟨j,hj⟩).isLt)).elim
  · simpa only [index, dite_eq_right hi, dite_eq_right hj] using eq

private theorem indexBefore {n j i : ℕ} (f : Fin n → Fin n) (bound : i < n + j) :
    index f i < n + j := by
  by_cases h : i < n
  · simp only [index, dite_eq_left h]
    have valid := (f ⟨i,h⟩).isLt
    omega
  · simpa only [index, dite_eq_right h] using bound

private def degreeOp (o : GateOp) (xs : List ℕ) : ℕ :=
  letI := lineDegreeGateOpDecEq
  if o = .and then xs.sum else xs.foldr max 0

private theorem flags {n : ℕ} (j : Fin n) :
    ((List.range n).map fun i => if i ∈ ({j.val} : Finset ℕ) then 1 else 0) =
      List.ofFn (fun k : Fin n => if k = j then 1 else (0 : ℕ)) := by
  apply List.ext_getElem (by simp)
  intro i hp hq
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  simp only [Finset.mem_singleton, ← Fin.val_inj]

end PEqualNP.Outside.L_meta_18806

open PEqualNP.Outside.L_meta_18806 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18806 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x5 ∈ x2.gates, x5.inputs.Nodup) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2.size ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ (∀ x7 ∈ x6.gates, x7.inputs.Nodup) ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn (x7 ∘ ⇑x3))) ∧ ∀ (x7 : Fin x1), x6.lineDeg x1 {↑(x3 x7)} = x2.lineDeg x1 {↑x7} := by
  intro n C f ao distinct
  let D : Circuit := ⟨C.gates.map (gate f), index f C.output⟩
  have len : D.size = C.size := by simp [D, Circuit.size]
  have member (h : Gate) (mem : h ∈ D.gates) : ∃ g ∈ C.gates, h = gate f g := by
    obtain ⟨g, hg, e⟩ := List.mem_map.mp mem
    exact ⟨g,hg,e.symm⟩
  refine ⟨D, len, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · intro h mem
    obtain ⟨g,hg,rfl⟩ := member h mem
    exact (distinct g hg).map (indexInjective f.injective)
  · intro x
    have h := readAfter GateOp.eval false f x C.gates [] C.output
    unfold runStep at h
    simpa only [D, Circuit.eval, Circuit.wires, List.append_nil] using h
  · intro j
    let x : Fin n → ℕ := fun k => if k = f j then 1 else 0
    have marked : x ∘ f = fun k => if k = j then 1 else 0 := by
      funext k
      change (if f k = f j then 1 else 0) = (if k = j then 1 else 0)
      simp [f.injective.eq_iff]
    have h := readAfter degreeOp (0 : ℕ) f x C.gates [] C.output
    rw [marked] at h
    simp only [List.append_nil] at h
    unfold Circuit.lineDeg Circuit.lineDegrees
    rw [flags, flags]
    change ((C.gates.map (gate f)).foldl (runStep degreeOp 0) (List.ofFn x)).getD (index f C.output) 0 =
      (C.gates.foldl (runStep degreeOp 0) (List.ofFn fun k => if k = j then 1 else 0)).getD C.output 0
    exact h

