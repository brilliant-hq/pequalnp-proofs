import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18785

open PEqualNP.CircuitLowerBounds

private def rename (f : Fin 26 → Option (Fin 25)) (size i : ℕ) : ℕ :=
  if h : i < 26 then (f ⟨i,h⟩).elim (25 + size) Fin.val else i - 1

private def mapGate (f : Fin 26 → Option (Fin 25)) (size : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename f size)⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def restrictInput (f : Fin 26 → Option (Fin 25)) (x : Fin 25 → Bool) (i : Fin 26) : Bool :=
  (f i).elim false x

private theorem initial (f : Fin 26 → Option (Fin 25)) (size : ℕ)
    (x : Fin 25 → Bool) (tail : List Bool) (ht : tail.length ≤ size) (i : ℕ) :
    (List.ofFn x ++ tail).getD (rename f size i) false =
      (List.ofFn (restrictInput f x) ++ tail).getD i false := by
  by_cases input : i < 26
  · have old : i < (List.ofFn (restrictInput f x)).length := by simpa using input
    rw [List.getD_append _ _ _ _ old, List.getD_eq_getElem _ _ old, List.getElem_ofFn]
    rw [rename, dite_eq_left input]
    cases e : f ⟨i,input⟩ with
    | none =>
      have beyond : (List.ofFn x ++ tail).length ≤ 25 + size := by
        simp only [List.length_append, List.length_ofFn]
        omega
      rw [Option.elim_none, List.getD_eq_default _ _ beyond]
      simp [restrictInput,e]
    | some j =>
      have valid : j.val < (List.ofFn x).length := by simp
      rw [Option.elim_some, List.getD_append _ _ _ _ valid, List.getD_eq_getElem _ _ valid,
        List.getElem_ofFn]
      simp [restrictInput,e]
  · rw [rename, dite_eq_right input]
    have old : (List.ofFn (restrictInput f x)).length ≤ i := by
      simpa using Nat.le_of_not_lt input
    have new : (List.ofFn x).length ≤ i-1 := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right old,
      List.getElem?_append_right new, List.length_ofFn]
    have shift : i - 1 - 25 = i - 26 := by omega
    rw [shift]

private theorem preserve (f : Fin 26 → Option (Fin 25)) (size : ℕ) (x : Fin 25 → Bool)
    (gates : List Gate) (tail : List Bool) (fit : tail.length + gates.length ≤ size)
    (i : ℕ) :
    ((gates.map (mapGate f size)).foldl step (List.ofFn x ++ tail)).getD (rename f size i) false =
      (gates.foldl step (List.ofFn (restrictInput f x) ++ tail)).getD i false := by
  induction gates generalizing tail with
  | nil => exact initial f size x tail (by simpa using fit) i
  | cons g rest ih =>
    let v := g.op.eval (g.inputs.map (fun j => (List.ofFn (restrictInput f x) ++ tail).getD j false))
    have after : (mapGate f size g).op.eval
        ((mapGate f size g).inputs.map fun j => (List.ofFn x ++ tail).getD j false) = v := by
      simp only [mapGate, List.map_map, v]
      congr 1
      exact List.map_congr_left (fun j _ => initial f size x tail (by simp at fit; omega) j)
    have next : (tail ++ [v]).length + rest.length ≤ size := by simp at fit ⊢; omega
    simp only [List.map_cons, List.foldl_cons, step, after]
    simpa only [List.append_assoc] using ih (tail ++ [v]) next

end PEqualNP.Outside.L_meta_18785

open PEqualNP.Outside.L_meta_18785 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18785 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Option (Fin (25 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size = x1.size ∧ ∀ (x5 : Fin (25 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => (x2 x6).elim Bool.false x5) := by
  intro C f props
  let D : Circuit := ⟨C.gates.map (mapGate f C.size), rename f C.size C.output⟩
  refine ⟨D, ?_, by simp [D,Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (show g ∈ C.gates.map (mapGate f C.size) from hg)
    simpa only [mapGate,List.length_map] using props q hq
  · intro x
    have h := preserve f C.size x C.gates [] (by simp [Circuit.size]) C.output
    unfold step restrictInput at h
    simpa only [D,Circuit.eval,Circuit.wires,List.append_nil,restrictInput] using h

