import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A cut of L-meta-3321.  `Clean` is an abstract predicate supplied with its defining
-- formula; `badCount` counts the gates it rejects.  The real content is `reduce`: an
-- unclean circuit can be replaced by a no-larger one with fewer bad gates.
theorem PEqualNP.Outside.R_meta_3321_1
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (Clean : Circuit → Prop) (badCount : Circuit → ℕ)
    (hClean : ∀ D : Circuit, Clean D ↔
      ∀ j < D.gates.length,
(gateAt D j).op = GateOp.and →
    (∀ z : Fin (N + N) → Bool,
      (D.wires (List.ofFn z)).getD (N + N + j) false = true →
        (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD
            (N + N + j) false = true ∨
        (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD
            (N + N + j) false = true ∨
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    (∀ p : Fin N,
      (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD
        (N + N + j) false = false) ∧
    (∀ l : Fin N,
      (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD
        (N + N + j) false = false))
    (reduce : ∀ D : Circuit,
      Monotone2 D → ReadsBack (N + N) D →
      (∀ z : Fin (N + N) → Bool,
    circuitFun (N + N) D z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ¬ Clean D →
        ∃ D' : Circuit,
          Monotone2 D' ∧ ReadsBack (N + N) D' ∧ D'.size ≤ D.size ∧
          (∀ z : Fin (N + N) → Bool,
    circuitFun (N + N) D' z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ badCount D' < badCount D) :
    ∀ C : Circuit,
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool,
    circuitFun (N + N) C z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        ∃ D : Circuit,
          Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
          (∀ j < D.gates.length,
(gateAt D j).op = GateOp.and →
    (∀ z : Fin (N + N) → Bool,
      (D.wires (List.ofFn z)).getD (N + N + j) false = true →
        (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD
            (N + N + j) false = true ∨
        (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD
            (N + N + j) false = true ∨
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    (∀ p : Fin N,
      (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD
        (N + N + j) false = false) ∧
    (∀ l : Fin N,
      (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD
        (N + N + j) false = false)) := by
  intro C h4 hmono hrb hsound
  have key : ∀ k : ℕ,
      (∀ D : Circuit, badCount D = k → D.size ≤ C.size →
        Monotone2 D → ReadsBack (N + N) D → (∀ z : Fin (N + N) → Bool,
    circuitFun (N + N) D z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          ∃ D' : Circuit,
            Monotone2 D' ∧ ReadsBack (N + N) D' ∧ D'.size ≤ C.size ∧
            (∀ z : Fin (N + N) → Bool,
    circuitFun (N + N) D' z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ Clean D') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro D hk hsizeD hmonoD hrbD hsoundD
      by_cases hc : Clean D
      · exact ⟨D, hmonoD, hrbD, hsizeD, hsoundD, hc⟩
      · obtain ⟨D', hmono', hrb', hsize', hsound', hbad'⟩ :=
          reduce D hmonoD hrbD hsoundD hc
        have hlt : badCount D' < k := by omega
        exact ih (badCount D') hlt D' rfl (le_trans hsize' hsizeD) hmono' hrb' hsound'
  obtain ⟨D, hmonoD, hrbD, hsizeD, hsoundD, hcleanD⟩ :=
    key (badCount C) C rfl (le_refl _) hmono hrb hsound
  exact ⟨D, hmonoD, hrbD, hsizeD, (hClean D).mp hcleanD⟩
