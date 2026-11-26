import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_17387_42
    (shannonLift : ∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Nat),
    PEqualNP.MetaComplexity.FanInTwo C → C.output < n+C.size →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size + 2 ∧
    ∀ (v : Bool) (xs : List Bool), xs.length = n → D.eval (v :: xs) =
      ((v && (PEqualNP.CircuitLowerBounds.Circuit.mk C.gates p).eval xs) || C.eval xs))
    (pairedCofactors : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ C.output < 8+C.size ∧
    ∀ y : Fin 8 → Bool, C.eval (List.ofFn y) = ((y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) || (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)) ∧
      (((y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) || (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)) = false → (PEqualNP.CircuitLowerBounds.Circuit.mk C.gates p).eval (List.ofFn y) = ((y 3 && y 7) || (y 4 && y 6)))) :
    PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) 13 := by
  have guard (v a b hi : Bool) (h : b = false → a = hi) :
     ((v && a) || b) = ((v && hi) || b) := by
    cases b with
    | false => rw [h rfl]
    | true => simp
  have factor : ∀ (a b c d e f g h i : Bool),
    ((a && ((e && i) || (f && h))) || ((b && d && i) || (b && f && g) || (c && d && h) || (c && e && g))) =
    ((a && e && i) || (a && f && h) || (b && d && i) || (b && f && g) || (c && d && h) || (c && e && g)) := by decide
  obtain ⟨C,p,hFan,hSize,hIdx,hEval⟩ := pairedCofactors
  obtain ⟨D,hD,hCost,hRun⟩ := shannonLift 8 C p hFan hIdx
  refine ⟨D,hD,by omega,?_⟩
  intro x
  let y : Fin 8 → Bool := fun i => x i.succ
  have hx : List.ofFn x = x 0 :: List.ofFn y := List.ofFn_succ
  rw [hx,hRun (x 0) _ (by simp), (hEval y).1,
    guard _ _ _ _ (hEval y).2]
  exact factor (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
