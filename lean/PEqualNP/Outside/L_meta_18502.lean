import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18502_aux
open PEqualNP.CircuitLowerBounds

def gateOf (d : Bool × ℕ × ℕ) : Gate :=
  ⟨if d.1 = true then .and else .or, [d.2.1, d.2.2]⟩

def step {α : Type} (w : List (Set α)) (d : Bool × ℕ × ℕ) : List (Set α) :=
  w.concat (if d.1 = true then w.getD d.2.1 ∅ ∩ w.getD d.2.2 ∅
    else w.getD d.2.1 ∅ ∪ w.getD d.2.2 ∅)

noncomputable def bit {α : Type} (a : α) (s : Set α) : Bool := by
  classical
  exact decide (a ∈ s)

theorem getBit {α : Type} (a : α) (w : List (Set α)) (i : ℕ) :
    (w.map (bit a)).getD i false = bit a (w.getD i ∅) := by
  classical
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [bit]

theorem wires_eq {α : Type} (a : α) (l : List (Bool × ℕ × ℕ)) (w : List (Set α)) :
    (l.map gateOf).foldl (fun v (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (w.map (bit a)) = (l.foldl step w).map (bit a) := by
  classical
  induction l generalizing w with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih (step w d)]
    congr 1
    obtain ⟨b,i,j⟩ := d
    cases b <;> simp [step, gateOf, GateOp.eval, List.concat_eq_append, getBit, bit,
      Set.mem_inter_iff, Set.mem_union] <;>
      cases w[i]? <;> cases w[j]? <;> simp [bit]

end PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.Outside.L_meta_18502_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18502 : have x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); ∀ (x2 : Fin (25 : ℕ) → Set x1) (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.length ∧ x5.output = x4 ∧ ∀ (x6 : x1) (x7 : Fin (25 : ℕ) → Bool), (∀ (x8 : Fin (25 : ℕ)), x7 x8 = Bool.true ↔ x6 ∈ x2 x8) → ∀ (x9 : ℕ), (x5.wires (List.ofFn x7)).getD x9 Bool.false = Bool.true ↔ x6 ∈ (List.foldl (fun (x10 : List (Set x1)) (x11 : Bool × ℕ × ℕ) => x10.concat (if x11.1 = Bool.true then x10.getD x11.2.1 ∅ ∩ x10.getD x11.2.2 ∅ else x10.getD x11.2.1 ∅ ∪ x10.getD x11.2.2 ∅)) (List.ofFn x2) x3).getD x9 ∅ := by
  classical
  dsimp only
  intro seeds ops out
  refine ⟨⟨ops.map gateOf, out⟩, ?_, by simp [Circuit.size], rfl, ?_⟩
  · intro g hg
    obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp hg
    cases b <;> simp [gateOf]
  · intro a x hx i
    have he : List.ofFn x = (List.ofFn seeds).map (bit a) := by
      rw [List.map_ofFn]
      congr 1
      funext k
      exact Bool.eq_iff_iff.mpr (by simpa [bit] using hx k)
    change (((ops.map gateOf).foldl _ (List.ofFn x)).getD i false = true) ↔
      a ∈ (ops.foldl step (List.ofFn seeds)).getD i ∅
    rw [he, wires_eq, getBit]
    simp [bit]
