import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18481

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_zip (u v : List Bool) (h : u.length = v.length) (i : ℕ) :
    (List.zipWith (fun a b => a || b) u v).getD i false = (u.getD i false || v.getD i false) := by
  induction u generalizing v i with
  | nil =>
    cases v with
    | nil => simp
    | cons b v => simp at h
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih v (by simpa using h) i

theorem any_or (l : List ℕ) (a b : ℕ → Bool) :
    (l.map fun i => a i || b i).any id = ((l.map a).any id || (l.map b).any id) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.any_cons, id] at ih ⊢
    rw [ih]
    cases a x <;> cases b x <;> simp

theorem key (gs : List Gate) (h : ∀ g ∈ gs, g.op = GateOp.or) :
    ∀ u v : List Bool, u.length = v.length →
      gs.foldl F (List.zipWith (fun a b => a || b) u v) =
        List.zipWith (fun a b => a || b) (gs.foldl F u) (gs.foldl F v) ∧
      (gs.foldl F u).length = (gs.foldl F v).length := by
  induction gs with
  | nil => intro u v hl; exact ⟨rfl, hl⟩
  | cons g gs ih =>
    intro u v hl
    have hg : g.op = GateOp.or := h g (by simp)
    have hrest : ∀ g ∈ gs, g.op = GateOp.or := fun g' hg' => h g' (by simp [hg'])
    have hstep : F (List.zipWith (fun a b => a || b) u v) g =
        List.zipWith (fun a b => a || b) (F u g) (F v g) := by
      simp only [F, hg, GateOp.eval]
      rw [List.zipWith_append (by exact hl)]
      congr 1
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right]
      congr 1
      have : (g.inputs.map fun i => (List.zipWith (fun a b => a || b) u v).getD i false) =
          (g.inputs.map fun i => (u.getD i false || v.getD i false)) := by
        apply List.map_congr_left; intro i _; exact getD_zip u v hl i
      rw [this, any_or]
    have hlen : (F u g).length = (F v g).length := by simp [F, hl]
    simp only [List.foldl_cons]
    rw [hstep]
    exact ih hrest (F u g) (F v g) hlen

end PEqualNP.Outside.L_meta_18481

open PEqualNP.Outside.L_meta_18481 in
theorem PEqualNP.Outside.L_meta_18481 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ)} → (29 : ℕ) ≤ (List.foldl (fun (x7 : List ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => x7 ++ [(List.map (fun (x9 : ℕ) => x7.getD x9 (0 : ℕ)) x8.inputs).sum]) (List.replicate (14 : ℕ) (1 : ℕ)) x1.gates).getD x1.output (0 : ℕ) := by
  intro C hm hno hf
  exfalso
  have hor : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    rcases hm.1 g hg with h1 | h1
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      exact absurd ⟨i, by rw [hi]; exact h1⟩ hno
    · exact h1
  let a : Fin 14 → Bool := fun i => decide (i = 0)
  let b : Fin 14 → Bool := fun i => decide (i = 7)
  let c : Fin 14 → Bool := fun i => decide (i = 0 ∨ i = 7)
  have ha : C.eval (List.ofFn a) = false := by
    cases h : C.eval (List.ofFn a)
    · rfl
    · exfalso; have := (hf a).mp h; revert this; decide
  have hb : C.eval (List.ofFn b) = false := by
    cases h : C.eval (List.ofFn b)
    · rfl
    · exfalso; have := (hf b).mp h; revert this; decide
  have hc : C.eval (List.ofFn c) = true := (hf c).mpr (by decide)
  have hz : List.ofFn c = List.zipWith (fun a b => a || b) (List.ofFn a) (List.ofFn b) := by
    decide
  have k := key C.gates hor (List.ofFn a) (List.ofFn b) (by simp)
  have e : C.eval (List.ofFn c) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [hz]
    change (C.gates.foldl F _).getD _ _ = ((C.gates.foldl F _).getD _ _ || (C.gates.foldl F _).getD _ _)
    rw [k.1]
    exact getD_zip _ _ k.2 _
  rw [ha, hb, hc] at e
  exact absurd e (by decide)
