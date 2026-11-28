import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Fixing a vertex read by two non-OR gates gives two constant outputs.
-- The complementary case has at most one such reader at each vertex.

open Classical in
theorem PEqualNP.Outside.R_meta_1745_2 :
    (∀ (n : ℕ) (C : Circuit) (v : Fin n), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠
        circuitFun n C (Function.update y v false)) →
      2 ≤ (C.gates.filter fun g => !(g.op.eval [true,false]) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length →
      ∃ s : ℕ, s+4 ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update x v false)) s) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, let gs := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val);
        gs.length ≤ 3 ∧ (gs.length = 3 → ∀ g ∈ gs, g.op = GateOp.or)) →
      (∀ v ∉ A, (C.gates.filter fun g => !(g.op.eval [true,false]) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      ∃ v ∉ A, ∃ s : ℕ, s+4 ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update x v false)) s) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro absorb residual n G A f C degrees girth endpoints edge hspec fan hfun minimal readers
  have minimize : IsMinimalCircuit n C := by
    refine ⟨fan,fun D hD hEq => minimal D.size ⟨D,hD,le_rfl,fun x => ?_⟩⟩
    exact congrFun (hEq.trans hfun) x
  have hgraph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [hspec]
    change _ ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases many : ∃ v ∉ A, 2 ≤ (C.gates.filter fun g => !(g.op.eval [true,false]) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length
  · obtain ⟨v,hv,two⟩ := many
    have avoid : ∃ a b, a ≠ v ∧ b ≠ v ∧ G.Adj a b := by
      by_contra! none
      have endpointsMeet (a b : Fin n) (h : G.Adj a b) : a = v ∨ b = v := by
        by_contra! hn
        exact none a b hn.1 hn.2 h
      obtain ⟨a,b,hab⟩ := edge
      have hvertex : ∃ u, u ≠ v ∧ G.Adj u v := by
        rcases endpointsMeet a b hab with h | h
        · subst a
          exact ⟨b,hab.ne.symm,hab.symm⟩
        · subst b
          exact ⟨a,hab.ne,hab⟩
      obtain ⟨u,hu,huv⟩ := hvertex
      have hsub : G.neighborSet u ⊆ {v} := by
        intro t ht
        exact Set.mem_singleton_iff.mpr ((endpointsMeet u t ht).resolve_left hu)
      have small := Set.ncard_le_ncard hsub
      have degree := degrees u (endpoints u v huv)
      rw [degree, Set.ncard_singleton] at small
      omega
    obtain ⟨p,q,hp,hq,hpq⟩ := avoid
    let lo : Fin n → Bool := fun _ => false
    let hi : Fin n → Bool := fun i => decide (i = p ∨ i = q)
    have hLo : f lo = false := by
      cases e : f lo
      · rfl
      · obtain h | h := (hspec lo).mp e
        · obtain ⟨a,_,ha⟩ := h
          simp [lo] at ha
        · obtain ⟨a,b,_,ha,_⟩ := h
          simp [lo] at ha
    have loFix : Function.update lo v false = lo := by
      funext i
      by_cases hd : i = v
      · subst i; simp [lo]
      · simp [Function.update_of_ne hd]
    have hiFix : f (Function.update hi v false) = true :=
      (hspec _).mpr (Or.inr ⟨p,q,hpq,by simp [hi,Function.update_of_ne hp],
        by simp [hi,Function.update_of_ne hq]⟩)
    have nonconstant : ∃ x y : Fin n → Bool,
        circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false) := by
      refine ⟨lo,hi,?_⟩
      rw [hfun,loFix,hLo,hiFix]
      decide
    obtain ⟨s,hs,hC⟩ := absorb n C v minimize nonconstant two
    exact ⟨v,hv,s,hs,by rw [hfun] at hC; exact hC⟩
  · have fewer : ∀ v ∉ A, (C.gates.filter fun g => !(g.op.eval [true,false]) && (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1 := by
      intro v hv
      have h := fun h => many ⟨v,hv,h⟩
      exact Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    obtain ⟨v,hv,s,hs,hC⟩ := residual n G A C degrees girth endpoints edge minimize
      (hfun.trans hgraph) readers fewer
    exact ⟨v,hv,s,hs,by rw [hfun] at hC; exact hC⟩
