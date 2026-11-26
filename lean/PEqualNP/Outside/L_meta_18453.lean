import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18453_aux

open PEqualNP.CircuitLowerBounds

theorem getD_zip (w1 w2 : List Bool) (h : w1.length = w2.length) (i : ℕ) :
    (List.zipWith (fun a b => a || b) w1 w2).getD i false = (w1.getD i false || w2.getD i false) := by
  induction w1 generalizing w2 i with
  | nil => cases w2 <;> simp_all
  | cons a t ih =>
    cases w2 with
    | nil => simp at h
    | cons b s =>
      cases i with
      | zero => simp
      | succ i => simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact ih s (by simpa using h) i

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.map fun i => f i || g i).any id = ((l.map f).any id || (l.map g).any id) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.any_cons, ih, id]; cases f a <;> cases g a <;> simp

theorem fold_hom (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.or) (w1 w2 : List Bool)
    (h : w1.length = w2.length) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.zipWith (fun a b => a || b) w1 w2) =
    List.zipWith (fun a b => a || b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hop : g.op = GateOp.or := hg g (by simp)
    have e : (List.zipWith (fun a b => a || b) w1 w2 ++
        [g.op.eval (g.inputs.map fun i => (List.zipWith (fun a b => a || b) w1 w2).getD i false)]) =
        List.zipWith (fun a b => a || b) (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
          (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := by
      rw [List.zipWith_append h]
      simp only [getD_zip w1 w2 h, hop, GateOp.eval, any_or, List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [e]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [h])

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem eval_hom (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) {n : ℕ} (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
  have hz : (List.ofFn fun i => a i || b i) = List.zipWith (fun a b => a || b) (List.ofFn a) (List.ofFn b) := by
    apply List.ext_getElem <;> simp
  unfold Circuit.eval Circuit.wires
  rw [hz, fold_hom C.gates hg _ _ (by simp), getD_zip]
  rw [len_fold, len_fold]; simp


theorem eval_hom2 (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) (w1 w2 : List Bool)
    (h : w1.length = w2.length) :
    C.eval (List.zipWith (fun a b => a || b) w1 w2) = (C.eval w1 || C.eval w2) := by
  unfold Circuit.eval Circuit.wires
  rw [fold_hom C.gates hg _ _ h, getD_zip]
  rw [len_fold, len_fold, h]

end PEqualNP.Outside.L_meta_18453_aux

open PEqualNP.Outside.L_meta_18453_aux in
theorem PEqualNP.Outside.L_meta_18453 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (64 : ℕ) ≤ x1.size := by
  intro C hm hna hc _ _
  exfalso
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h1 := (hm g hgm).1
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgm
    rcases h1 with h1 | h1
    · exact absurd ⟨i, h1⟩ hna
    · exact h1
  have e : PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13)) =
      List.zipWith (fun a b => a || b)
        (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)))
        (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({0} : Finset (Fin 13))) := by
    decide
  have h1 := hc {0} {0}
  have h2 := hc {0} ∅
  have h3 := hc ∅ {0}
  rw [e, eval_hom2 C hg _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]), h2, h3] at h1
  revert h1
  decide
