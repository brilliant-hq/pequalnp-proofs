import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2976_1
    (normalize : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 n C → C.output < n + C.gates.length →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.gates.length ∧ D.size = C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
        ∀ i < D.gates.length, ∀ a b : ℕ,
          D.gates[i]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ →
            ((n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n D b →
                PEqualNP.CircuitMoves.WireBelowOutput n D a) ∧
              (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n D a →
                PEqualNP.CircuitMoves.WireBelowOutput n D b)))
    (normalCase : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl,
        p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) C =
        (fun z => decide (∃ p : Fin Np, ∃ l : Fin Nl,
          I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (let below := PEqualNP.CircuitMoves.WireBelowOutput (Np + Nl) C
       ∀ i < C.gates.length, ∀ a b : ℕ,
        C.gates[i]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ →
          ((Np + Nl ≤ b → below b → below a) ∧
            (Np + Nl ≤ a → below a → below b))) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
        let O := PEqualNP.CircuitLowerBounds.GateOp.or
        ∃ P L : Finset ℕ,
        PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) D =
          (fun z => decide (∃ p : Fin Np, ∃ l : Fin Nl,
            I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) ∧
        D.size ≤ C.size ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length,
          w = Np + Nl + i ∧
          (g i).op = O ∧
          ∀ u ∈ (g i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length,
          w = Np + Nl + i ∧
          (g i).op = O ∧
          ∀ u ∈ (g i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length,
          (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ a b : ℕ, (g i).inputs = [a, b] ∧
            a ∈ P ∧ b ∈ L) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl,
        p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool,
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z =
          decide (∃ p : Fin Np, ∃ l : Fin Nl,
            I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, ∃ P L : Finset ℕ,
        PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        (∀ z : Fin (Np + Nl) → Bool,
          PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z =
            decide (∃ p : Fin Np, ∃ l : Fin Nl,
              I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) ∧
        D.size ≤ C.size ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length,
          w = Np + Nl + i ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length,
          w = Np + Nl + i ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧
            a ∈ P ∧ b ∈ L := by
  intro Np Nl I hI C hNoFour hAO hfun
  classical
  by_cases hEdge : ∃ p l, I p l
  · obtain ⟨p, l, hpl⟩ := hEdge
    let z : Fin (Np + Nl) → Bool :=
      fun w => decide (w = Fin.castAdd Nl p ∨ w = Fin.natAdd Np l)
    have hPointLine : Fin.castAdd Nl p ≠ Fin.natAdd Np l := by
      intro h
      have hv := congrArg Fin.val h
      have hpv : (Fin.castAdd Nl p).val < Np := by simp
      have hlv : Np ≤ (Fin.natAdd Np l).val := by simp
      omega
    have hzPoint : z (Fin.castAdd Nl p) = true := by
      simp [z, hPointLine]
    have hzLine : z (Fin.natAdd Np l) = true := by
      simp [z]
    have htrue : PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = true := by
      rw [hfun z]
      simpa only [decide_eq_true_eq] using (show
        ∃ p' l', I p' l' ∧ z (Fin.castAdd Nl p') = true ∧ z (Fin.natAdd Np l') = true from
          ⟨p, l, hpl, hzPoint, hzLine⟩)
    have hlen (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ xs : List Bool,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length =
          xs.length + gs.length := by
      intro xs
      induction gs generalizing xs with
      | nil => simp
      | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp
          omega
    have hwlen : (C.wires (List.ofFn z)).length = Np + Nl + C.gates.length := by
      simpa [PEqualNP.CircuitLowerBounds.Circuit.wires, List.length_ofFn] using
        hlen C.gates (List.ofFn z)
    have hidx : C.output < (C.wires (List.ofFn z)).length := by
      by_contra hnot
      have hnone : (C.wires (List.ofFn z))[C.output]? = none :=
        List.getElem?_eq_none (Nat.le_of_not_gt hnot)
      have hfalse : (C.wires (List.ofFn z)).getD C.output false = false := by
        simp [List.getD_eq_getElem?_getD, hnone]
      change C.eval (List.ofFn z) = true at htrue
      rw [PEqualNP.CircuitLowerBounds.Circuit.eval] at htrue
      rw [hfalse] at htrue
      contradiction
    have hout : C.output < Np + Nl + C.gates.length := by
      rw [← hwlen]
      exact hidx
    obtain ⟨D, hDAO, hDout, hDsize, hDfun, hDnormal⟩ := normalize (Np + Nl) C hAO hout
    have hfun' : PEqualNP.MetaComplexity.circuitFun (Np + Nl) D =
        (fun w => decide (∃ p : Fin Np, ∃ l : Fin Nl,
          I p l ∧ w (Fin.castAdd Nl p) = true ∧ w (Fin.natAdd Np l) = true)) := by
      calc
        _ = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C := hDfun
        _ = _ := funext hfun
    obtain ⟨E, P, L, hEAO, hEfun, hEsize, hP, hL, hAnd⟩ :=
      normalCase Np Nl I D hNoFour hDAO hfun' hDnormal
    refine ⟨E, P, L, hEAO, ?_, ?_, hP, hL, hAnd⟩
    · intro w
      exact congrFun hEfun w
    · calc
        E.size ≤ D.size := hEsize
        _ = C.size := hDsize
  · have hEmpty : ∀ p l, ¬ I p l := by
      intro p l hpl
      exact hEdge ⟨p, l, hpl⟩
    let C0 : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], Np + Nl⟩
    have hAO0 : PEqualNP.TopForm.IsAO2 (Np + Nl) C0 := by
      simp [PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
        PEqualNP.MetaComplexity.NestedCover.ReadsBack, C0]
    have hfun0 : ∀ z : Fin (Np + Nl) → Bool,
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C0 z =
          decide (∃ p : Fin Np, ∃ l : Fin Nl,
            I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) := by
      intro z
      simp [PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, C0, hEmpty]
    refine ⟨C0, ∅, ∅, hAO0, hfun0, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ C.size
      exact Nat.zero_le _
    · simp
    · simp
    · simp [C0]
