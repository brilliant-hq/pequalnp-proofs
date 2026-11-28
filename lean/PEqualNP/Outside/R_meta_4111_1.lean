import Mathlib
import PEqualNP.Defs

-- Cut L-meta-4111 by the operation of the first gate of a least-size circuit for the
-- edge function: the gate-elimination argument is run separately for a first gate that
-- is an AND gate, an OR gate, a NOT gate, and for a circuit with no first gate.
theorem PEqualNP.Outside.R_meta_4111_1
    (hAnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit), ¬ G.Colorable 2 → (∀ a : Fin n, (∃ b : Fin n, G.Adj a b) → (G.neighborSet a).ncard = 3) → (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) → (∃ u v : Fin n, G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → D.size + 1 < G.edgeSet.ncard + T.card) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[0]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ u v : Fin n, G.Adj u v ∧ ∃ t : ℕ, t + 7 ≤ D.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t)
    (hOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit), ¬ G.Colorable 2 → (∀ a : Fin n, (∃ b : Fin n, G.Adj a b) → (G.neighborSet a).ncard = 3) → (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) → (∃ u v : Fin n, G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → D.size + 1 < G.edgeSet.ncard + T.card) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[0]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ u v : Fin n, G.Adj u v ∧ ∃ t : ℕ, t + 7 ≤ D.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t)
    (hNot : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit), ¬ G.Colorable 2 → (∀ a : Fin n, (∃ b : Fin n, G.Adj a b) → (G.neighborSet a).ncard = 3) → (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) → (∃ u v : Fin n, G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → D.size + 1 < G.edgeSet.ncard + T.card) → (∃ g : PEqualNP.CircuitLowerBounds.Gate, D.gates[0]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ u v : Fin n, G.Adj u v ∧ ∃ t : ℕ, t + 7 ≤ D.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t)
    (hNone : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (D : PEqualNP.CircuitLowerBounds.Circuit), ¬ G.Colorable 2 → (∀ a : Fin n, (∃ b : Fin n, G.Adj a b) → (G.neighborSet a).ncard = 3) → (∀ (a : Fin n) (w : G.Walk a a), w.IsCycle → 7 ≤ w.length) → (∃ u v : Fin n, G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → D.size + 1 < G.edgeSet.ncard + T.card) → (D.gates[0]? = Option.none) → ∃ u v : Fin n, G.Adj u v ∧ ∃ t : ℕ, t + 7 ≤ D.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) v false)) t) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14) := by
  intro n G f hNonbipartite hCubic hGirth hEdge hFunction s hBudget hSize
  classical
  have hex : ∃ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hSize⟩
  obtain ⟨D, hFanIn, hBound, hEval⟩ := Nat.find_spec hex
  have hDs : D.size ≤ s := hBound.trans (Nat.find_min' hex hSize)
  have hLeast : PEqualNP.MetaComplexity.IsMinimalCircuit n D := by
    refine ⟨hFanIn, ?_⟩
    intro E hEFanIn hEquivalent
    have hESize : PEqualNP.MetaComplexity.HasCircuitSize n f E.size := by
      refine ⟨E, hEFanIn, le_rfl, ?_⟩
      intro x
      exact (congrFun hEquivalent x).trans (hEval x)
    exact hBound.trans (Nat.find_min' hex hESize)
  have hDSemantics (x : Fin n → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [hEval x]
    exact hFunction x
  have hDBudget (T : Finset (Fin n))
      (hCover : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) :
      D.size + 1 < G.edgeSet.ncard + T.card :=
    lt_of_le_of_lt (Nat.add_le_add_right hDs 1) (hBudget T hCover)
  cases hcase : D.gates[0]? with
  | none =>
    obtain ⟨u, v, huv, t, ht, hHas⟩ :=
      hNone n G f D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics hDBudget hcase
    exact ⟨u, v, huv, t, ht.trans hDs, hHas⟩
  | some g =>
    have hgmem : g ∈ D.gates := List.mem_iff_getElem?.mpr ⟨0, hcase⟩
    rcases (hFanIn g hgmem).1 with hop | hop | hop
    · obtain ⟨u, v, huv, t, ht, hHas⟩ :=
        hAnd n G f D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics hDBudget ⟨g, hcase, hop⟩
      exact ⟨u, v, huv, t, ht.trans hDs, hHas⟩
    · obtain ⟨u, v, huv, t, ht, hHas⟩ :=
        hOr n G f D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics hDBudget ⟨g, hcase, hop⟩
      exact ⟨u, v, huv, t, ht.trans hDs, hHas⟩
    · obtain ⟨u, v, huv, t, ht, hHas⟩ :=
        hNot n G f D hNonbipartite hCubic hGirth hEdge hLeast hDSemantics hDBudget ⟨g, hcase, hop⟩
      exact ⟨u, v, huv, t, ht.trans hDs, hHas⟩
