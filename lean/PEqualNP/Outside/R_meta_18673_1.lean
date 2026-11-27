import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18673_1
    (hWeightSumEquiv :
      ∀ (m : ℕ), m >>> (58 : ℕ) = (0 : ℕ) →
        List.foldl (fun (acc : ℕ) (p : ℕ × ℕ) => if m.testBit p.1 = Bool.true then acc else acc + p.2) (18 : ℕ)
          [((22 : ℕ), (6 : ℕ)), ((24 : ℕ), (2 : ℕ)), ((25 : ℕ), (2 : ℕ)), ((26 : ℕ), (3 : ℕ)), ((28 : ℕ), (3 : ℕ)), ((31 : ℕ), (2 : ℕ)), ((32 : ℕ), (2 : ℕ)), ((33 : ℕ), (2 : ℕ)), ((34 : ℕ), (6 : ℕ)), ((35 : ℕ), (1 : ℕ)), ((36 : ℕ), (4 : ℕ)), ((37 : ℕ), (2 : ℕ)), ((38 : ℕ), (2 : ℕ)), ((41 : ℕ), (1 : ℕ)), ((42 : ℕ), (3 : ℕ)), ((43 : ℕ), (6 : ℕ)), ((44 : ℕ), (4 : ℕ)), ((45 : ℕ), (1 : ℕ)), ((46 : ℕ), (5 : ℕ)), ((47 : ℕ), (1 : ℕ)), ((48 : ℕ), (3 : ℕ)), ((50 : ℕ), (2 : ℕ)), ((51 : ℕ), (4 : ℕ)), ((52 : ℕ), (2 : ℕ)), ((53 : ℕ), (4 : ℕ)), ((54 : ℕ), (3 : ℕ)), ((55 : ℕ), (4 : ℕ)), ((56 : ℕ), (5 : ℕ))] =
        ∑ x4 : Fin (39 : ℕ), if m.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ))
    (hActiveDAG :
      have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>
        have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
        have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ))
        x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]
      have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]
      have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) =>
        List.foldl (fun (acc : ℕ) (p : ℕ × ℕ) => if x3.1.testBit p.1 = Bool.true then acc else acc + p.2) (18 : ℕ)
          [((22 : ℕ), (6 : ℕ)), ((24 : ℕ), (2 : ℕ)), ((25 : ℕ), (2 : ℕ)), ((26 : ℕ), (3 : ℕ)), ((28 : ℕ), (3 : ℕ)), ((31 : ℕ), (2 : ℕ)), ((32 : ℕ), (2 : ℕ)), ((33 : ℕ), (2 : ℕ)), ((34 : ℕ), (6 : ℕ)), ((35 : ℕ), (1 : ℕ)), ((36 : ℕ), (4 : ℕ)), ((37 : ℕ), (2 : ℕ)), ((38 : ℕ), (2 : ℕ)), ((41 : ℕ), (1 : ℕ)), ((42 : ℕ), (3 : ℕ)), ((43 : ℕ), (6 : ℕ)), ((44 : ℕ), (4 : ℕ)), ((45 : ℕ), (1 : ℕ)), ((46 : ℕ), (5 : ℕ)), ((47 : ℕ), (1 : ℕ)), ((48 : ℕ), (3 : ℕ)), ((50 : ℕ), (2 : ℕ)), ((51 : ℕ), (4 : ℕ)), ((52 : ℕ), (2 : ℕ)), ((53 : ℕ), (4 : ℕ)), ((54 : ℕ), (3 : ℕ)), ((55 : ℕ), (4 : ℕ)), ((56 : ℕ), (5 : ℕ))] ≤ (4 : ℕ) * x3.2
      ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),
        x4.length ≤ (26 : ℕ) ∧
        (∀ (x7 : Fin x4.length),
          have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.getD ↑x7 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }
          (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x8.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + ↑x7 ∧ x10 < (14 : ℕ) + ↑x7) ∧
        x5 < x6 ∧
        x6 < (14 : ℕ) + x4.length ∧
        have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4
        have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ))
        have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ))
        x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) :
    (have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]; have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => (∑ x4 : Fin (39 : ℕ), if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * x3.2; ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),   x4.length ≤ (26 : ℕ) ∧     (∀ (x7 : Fin x4.length),         have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.getD ↑x7 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };         (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x8.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (14 : ℕ) + ↑x7 ∧ x10 < (14 : ℕ) + ↑x7) ∧       x5 < x6 ∧         x6 < (14 : ℕ) + x4.length ∧           have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;           have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));           have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));           x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) := by
  obtain ⟨x4, x5, x6, hLen, hG, h56, h6, hAnd, hSh8, hSh9, hW8, hW9⟩ := hActiveDAG
  refine ⟨x4, x5, x6, hLen, hG, h56, h6, hAnd, hSh8, hSh9, ?_, ?_⟩
  · dsimp only; rw [← hWeightSumEquiv _ hSh8]; exact hW8
  · dsimp only; rw [← hWeightSumEquiv _ hSh9]; exact hW9
