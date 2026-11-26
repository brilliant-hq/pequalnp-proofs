import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4697_1
    (hMono : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)),
      (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = 3) →
      (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → 7 ≤ x7.length) →
      (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) →
      (∃ (x8 x9 : Fin x1), x2.Adj x8 x9) →
      ∀ (x9 : ℕ) (C : Circuit), Monotone2 C → C.size ≤ x9 → x1 ≤ C.output → C.output < x1 + C.size →
      (∀ x : Fin x1 → Bool, C.eval (List.ofFn x) = graphFun x2 ∅ x) →
      ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 x14 : Fin x12 → Finset (Fin x1)),
        (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ 1 ∨ x19 ∈ x17) ∧ (x20.card ≤ 1 ∨ x20 ∈ x17)) ∧
        (∀ x15 : Fin x12, ((x13 x15).card ≤ 1 ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ 1 ∨ x14 x15 ∈ x11)) ∧
        (∀ x15 : Fin x1 → Bool, (∃ x16 : Fin x12, (∃ x17 ∈ x13 x16, x15 x17 = true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = true) ↔ ∃ x16 x17 : Fin x1, x2.Adj x16 x17 ∧ x15 x16 = true ∧ x15 x17 = true) ∧
        x11.length + 2 * x12 ≤ x9 + 1)
    (hNot : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)),
      (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = 3) →
      (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → 7 ≤ x7.length) →
      (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) →
      (∃ (x8 x9 : Fin x1), x2.Adj x8 x9) →
      ∀ (x9 : ℕ) (C : Circuit), FanInTwo C → (∃ g ∈ C.gates, g.op = GateOp.not) → C.size ≤ x9 → x1 ≤ C.output → C.output < x1 + C.size →
      (∀ x : Fin x1 → Bool, C.eval (List.ofFn x) = graphFun x2 ∅ x) →
      ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 x14 : Fin x12 → Finset (Fin x1)),
        (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ 1 ∨ x19 ∈ x17) ∧ (x20.card ≤ 1 ∨ x20 ∈ x17)) ∧
        (∀ x15 : Fin x12, ((x13 x15).card ≤ 1 ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ 1 ∨ x14 x15 ∈ x11)) ∧
        (∀ x15 : Fin x1 → Bool, (∃ x16 : Fin x12, (∃ x17 ∈ x13 x16, x15 x17 = true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = true) ↔ ∃ x16 x17 : Fin x1, x2.Adj x16 x17 ∧ x15 x16 = true ∧ x15 x17 = true) ∧
        x11.length + 2 * x12 ≤ x9 + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  classical
  intro x1 x2 inst x4 hDeg hGirth hIso hEdge x9 hCirc
  rcases hCirc with ⟨C, hFan, hSize, hEval⟩
  have hWiresLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp; omega
  have hWiresPrefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih _ _ (by simp; omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp [List.getElem?_append_left hi]
  have hOutLt : C.output < x1 + C.size := by
    by_contra hge
    have hle : x1 + C.size ≤ C.output := Nat.le_of_not_lt hge
    rcases hEdge with ⟨u, v, huv⟩
    let fuv : Fin x1 → Bool := fun k => decide (k = u ∨ k = v)
    have hTrue : C.eval (List.ofFn fuv) = true := by
      rw [hEval fuv]
      simp [graphFun]
      exact ⟨u, v, huv, by simp [fuv], by simp [fuv]⟩
    unfold Circuit.eval Circuit.wires at hTrue
    have hFullLen : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fuv)).length = x1 + C.size := by
      rw [hWiresLen, List.length_ofFn]; rfl
    rw [List.getD_eq_default _ _ (by rw [hFullLen]; exact hle)] at hTrue
    cases hTrue
  have hOutGe : x1 ≤ C.output := by
    by_contra hlt
    have hlt1 : C.output < x1 := Nat.lt_of_not_ge hlt
    let fOne : Fin x1 → Bool := fun k => decide (k.val = C.output)
    have hEv : C.eval (List.ofFn fOne) = true := by
      unfold Circuit.eval Circuit.wires
      rw [hWiresPrefix _ _ _ (by simp [hlt1])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hlt1, fOne]
    rw [hEval fOne] at hEv
    simp [graphFun] at hEv
    rcases hEv with ⟨a, b, hab, ha, hb⟩
    simp only [fOne, decide_eq_true_eq] at ha hb
    have heq : a = b := Fin.ext (ha.trans hb.symm)
    subst heq
    exact x2.ne_of_adj hab rfl
  by_cases hHasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · exact hNot x1 x2 x4 hDeg hGirth hIso hEdge x9 C hFan hHasNot hSize hOutGe hOutLt hEval
  · have hM : Monotone2 C := by
      intro g hg
      have hf := hFan g hg
      refine ⟨?_, hf.2⟩
      rcases hf.1 with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd ⟨g, hg, h3⟩ hHasNot
    exact hMono x1 x2 x4 hDeg hGirth hIso hEdge x9 C hM hSize hOutGe hOutLt hEval
