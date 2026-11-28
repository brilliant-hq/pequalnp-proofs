import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8319_2
    (h1 : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (z : Fin n),
      ((∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) ∧
        (G.neighborSet z).ncard = 3 ∧ (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) ∧
        H = G.deleteEdges (G.incidenceSet z)) →
      let m := fun T : Finset (Fin n) => {e ∈ H.edgeSet | ∀ u ∈ T, u ∉ e}.ncard
      let F := PEqualNP.MetaComplexity.NestedCover.graphFun H
      ∀ (T : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalCircuit n C →
        let W := fun i (x : Fin n → Bool) => ({C with output := i}).eval (List.ofFn x)
        W C.output = F T →
        let num := fun j : Fin C.gates.length => n+j.val
        (∀ (J : Finset (Fin C.gates.length)) (p : Fin C.gates.length → Fin n),
          (∀ u v, H.Adj u v → ∃ x y, W C.output x ≠ W C.output y ∧
            (∀ a, a ≠ u → a ≠ v → x a = y a) ∧
            ∀ j ∈ J, p j ≠ u → p j ≠ v → W (num j) x = W (num j) y) → J.card < m T) →
        (∀ v, m (insert v T) < m T → ∀ J : Finset (Fin C.gates.length),
          (∀ j ∈ J, (num j = C.output ∨ ∃ k ∉ J, num j ∈ C.gates[k.val].inputs) →
            ∃ a < num j, (a < n ∨ ∃ k ∉ J, a = num k) ∧ ∀ x, x v = false → W (num j) x = W a x) →
          J.card ≤ m T - m (insert v T)) →
        ∃ v, m (insert v T) < m T ∧ ∃ t, t + m T ≤ C.size + m (insert v T) ∧
          PEqualNP.MetaComplexity.HasCircuitSize n (F (insert v T)) t)
    (h2 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (J : Finset (Fin C.gates.length)),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ j ∈ J, (n+j.val = C.output ∨ ∃ k ∉ J, n+j.val ∈ C.gates[k.val].inputs) →
        ∃ a < n+j.val, (a < n ∨ ∃ k ∉ J, a = n+k.val) ∧ ∀ x : Fin n → Bool, x v = false →
          ({C with output := n+j.val}).eval (List.ofFn x) = ({C with output := a}).eval (List.ofFn x)) →
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => x v || C.eval (List.ofFn x)) (C.size-J.card+1))
    (h3 : ∀ (n : ℕ) (z : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → ∀ (H : SimpleGraph (Fin n))
        (J : Finset (Fin C.gates.length)) (p : Fin C.gates.length → Fin n),
        let W := fun i (x : Fin n → Bool) => ({C with output := i}).eval (List.ofFn x)
        (∀ u v, H.Adj u v → ∃ x y, W C.output x ≠ W C.output y ∧
          (∀ a, a ≠ u → a ≠ v → x a = y a) ∧
          ∀ j ∈ J, p j ≠ u → p j ≠ v → W (n+j.val) x = W (n+j.val) y) →
        ∃ V : Finset (Fin n), H.IsVertexCover V ∧ V.card + J.card ≤ C.size+1)
    (h4 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ x, f x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ T : Finset (Fin n), H.IsVertexCover T →
      ∃ (k : ℕ) (A B : Fin k → (Fin n → Bool) → Bool) (p : Fin k → ℕ),
        PEqualNP.MetaComplexity.IsLiteralPartition n f k A B p (fun _ => true) ∧
          k = H.edgeSet.ncard + T.card) : ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool),   (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) →     (x3.neighborSet x5).ncard = (3 : ℕ) →       (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →         x4 = x3.deleteEdges (x3.incidenceSet x5) →           (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →             PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 →               ∃ (x13 : Finset (Fin x1)) (x14 : (Fin x1 → Bool) → Bool) (x15 : ℕ) (x16 : Fin x15 → (Fin x1 → Bool) → Bool) (x17 : Fin x15 → (Fin x1 → Bool) → Bool) (x18 : Fin x15 → ℕ) (x19 : Fin x15 → Bool) (x20 : Fin x15 → Finset (Fin x1)),                 PEqualNP.MetaComplexity.IsLiteralPartition x1 x14 x15 x16 x17 x18 x19 ∧                   (∀ (x21 : Fin x1 → Bool), x14 x21 = x6 x21 ∨ x14 x21 = Bool.true ∧ ∃ x22 ∈ x13, ∃ x23 ∈ x13, x22 ≠ x23 ∧ x21 x22 = Bool.true ∧ x21 x23 = Bool.true) ∧                     (∀ (x21 : Fin x15), x19 x21 = Bool.false → ∃ x23 ∈ x13, x18 x21 = ↑x23) ∧                       (∀ x21 ∈ x13, ∀ x23 ∈ x13, x21 ≠ x23 → ∀ (x26 : x4.Walk x21 x23), (3 : ℕ) < x26.length) ∧                         (∀ (x21 : Fin x15),                             x19 x21 = Bool.true →                               ∀ x23 ∈ x13,                                 x23 ∉ x20 x21 →                                   ∀ (x26 x27 : Fin x1),                                     x4.Adj x26 x27 →                                       have x29 : Fin x1 → Bool := fun (x29 : Fin x1) => x29 == x26 || x29 == x27;                                       x16 x21 (Function.update x29 x23 Bool.true) = x16 x21 x29) ∧                           ∑ x21 : { x21 : Fin x15 // x19 x21 = Bool.true }, ((1 : ℕ) + (x20 ↑x21).card) ≤ x2 + (1 : ℕ) := by
  classical
  intro n s G H z f deg dz gir del spec hc
  let m := fun T : Finset (Fin n) => {e ∈ H.edgeSet | ∀ u ∈ T, u ∉ e}.ncard
  let F := PEqualNP.MetaComplexity.NestedCover.graphFun H
  have start : f = F ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [F,PEqualNP.MetaComplexity.NestedCover.graphFun,spec]
  have descend (k : ℕ) : ∀ (T : Finset (Fin n)) (b : ℕ), m T = k →
      PEqualNP.MetaComplexity.HasCircuitSize n (F T) b →
      ∃ V : Finset (Fin n), H.IsVertexCover V ∧ V.card + k ≤ b+1 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro T b eq hb
      have ex : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n (F T) t := ⟨b,hb⟩
      obtain ⟨C,hf,ht,ev⟩ := Nat.find_spec ex
      have least : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize n (F T) t → C.size ≤ t :=
        fun t h => ht.trans (Nat.find_min' ex h)
      have hs := least b hb
      let W := fun i (x : Fin n → Bool) => ({C with output := i}).eval (List.ofFn x)
      have minimal : PEqualNP.MetaComplexity.IsMinimalCircuit n C := ⟨hf,fun D fan same =>
        least D.size ⟨D,fan,le_rfl,fun x => (congrFun same x).trans (ev x)⟩⟩
      let tests := fun (J : Finset (Fin C.gates.length)) (p : Fin C.gates.length → Fin n) =>
        ∀ u v, H.Adj u v → ∃ x y, W C.output x ≠ W C.output y ∧
          (∀ a, a ≠ u → a ≠ v → x a = y a) ∧ ∀ j ∈ J, p j ≠ u → p j ≠ v → W (n+j.val) x = W (n+j.val) y
      by_cases narrow : ∀ J p, tests J p → J.card < m T
      swap
      · push Not at narrow
        obtain ⟨J,p,ok,many⟩ := narrow
        obtain ⟨V,cover,bound⟩ := h3 n z C hf H J p ok
        exact ⟨V,cover,by omega⟩
      let Q := fun (v : Fin n) (J : Finset (Fin C.gates.length)) =>
        ∀ j ∈ J, (n+j.val = C.output ∨ ∃ k ∉ J, n+j.val ∈ C.gates[k.val].inputs) →
            ∃ a < n+j.val, (a < n ∨ ∃ k ∉ J, a = n+k.val) ∧ ∀ x, x v = false → W (n+j.val) x = W a x
      have step : ∃ v, m (insert v T) < m T ∧ ∃ t, t + m T ≤ C.size + m (insert v T) ∧
          PEqualNP.MetaComplexity.HasCircuitSize n (F (insert v T)) t := by
        by_cases low : ∀ v, m (insert v T) < m T → ∀ J, Q v J → J.card ≤ m T - m (insert v T)
        · exact h1 n G H z ⟨deg,dz,gir,del⟩ T C minimal (funext ev) narrow low
        push Not at low
        obtain ⟨v,lt,J,hJ,sz⟩ := low
        have wide := h2 n C v J hf hJ
        have cnt : J.card ≤ C.size := by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using J.card_le_univ
        have lift : F (insert v T) = fun x => x v || F T x := by
          funext x
          apply Bool.eq_iff_iff.mpr
          simp [F,PEqualNP.MetaComplexity.NestedCover.graphFun,Bool.or_eq_true,or_assoc]
        refine ⟨v,lt,C.size-J.card+1,by omega,?_⟩
        rw [lift]
        simpa only [ev] using wide
      obtain ⟨v,lt,t,cost,ht⟩ := step
      change m (insert v T) < m T at lt
      obtain ⟨V,cover,bound⟩ := ih (m (insert v T)) (by omega) (insert v T) t rfl ht
      exact ⟨V,cover,by omega⟩
  obtain ⟨T,cov,budget⟩ := descend (m ∅) ∅ s rfl (start ▸ hc)
  have full : m ∅ = H.edgeSet.ncard := by simp [m]
  rw [full] at budget
  obtain ⟨k,A,B,p,hp,hk⟩ := h4 n H f spec T cov
  refine ⟨∅,f,k,A,B,p,fun _ => true,fun _ => ∅,hp,fun _ => Or.inl rfl,?_,?_,?_,?_⟩
  · simp
  · simp
  · simp
  · simpa using (show k ≤ s+1 by omega)
