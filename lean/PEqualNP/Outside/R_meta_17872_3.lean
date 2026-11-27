import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17872_3
    (hStarCircuit :
      have f : (Fin (24 : ℕ) → Bool) → Bool := fun x =>
        (x (0 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
        (x (1 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (2 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (3 : Fin (24 : ℕ)) && (x (17 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (4 : Fin (24 : ℕ)) && (x (16 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (5 : Fin (24 : ℕ)) && (x (15 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (6 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)))) ||
        (x (7 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
        (x (8 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)))) ||
        (x (9 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (10 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (11 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (13 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ))));
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ps : List (ℕ × ℕ)) (w5 w6 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧
        ps ≠ [] ∧
        C.size + (2 : ℕ) * ps.length ≤ (59 : ℕ) ∧
        w5 < (24 : ℕ) + C.size ∧
        w6 < (24 : ℕ) + C.size ∧
        (∀ p ∈ ps, p.1 < (24 : ℕ) + C.size ∧ p.2 < (24 : ℕ) + C.size) ∧
        ∀ (x : Fin (24 : ℕ) → Bool),
          (ps.any fun p => PEqualNP.BlindGate.wireValue C (24 : ℕ) x p.1 && PEqualNP.BlindGate.wireValue C (24 : ℕ) x p.2) = f x ∧
          (f x = Bool.false →
            PEqualNP.BlindGate.wireValue C (24 : ℕ) x w5 = (x (0 : Fin (24 : ℕ)) || x (1 : Fin (24 : ℕ)) || x (3 : Fin (24 : ℕ))) ∧
            PEqualNP.BlindGate.wireValue C (24 : ℕ) x w6 = (x (15 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)))))
    (hStarEquiv :
      ∀ (x : Fin (24 : ℕ) → Bool),
        ((x (0 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
        (x (1 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (2 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (3 : Fin (24 : ℕ)) && (x (17 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (4 : Fin (24 : ℕ)) && (x (16 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (5 : Fin (24 : ℕ)) && (x (15 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (6 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)))) ||
        (x (7 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
        (x (8 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)))) ||
        (x (9 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
        (x (10 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
        (x (11 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (13 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ))))) = Bool.true ↔
        ∃ (u v : Fin (12 : ℕ)),
          (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v : Fin (13 : ℕ)) ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] ∧
          x (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
          x (Fin.natAdd (12 : ℕ) v) = Bool.true) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (24 : ℕ) → Bool) → Prop := fun (x2 : Fin (24 : ℕ) → Bool) => ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (12 : ℕ)), Fin.succAbove (9 : Fin (13 : ℕ)) x3 + Fin.succAbove (0 : Fin (13 : ℕ)) x4 ∈ x1 ∧ x2 (Fin.castAdd (12 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (ℕ × ℕ)) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4 ≠ [] ∧ x3.size + (2 : ℕ) * x4.length ≤ (59 : ℕ) ∧ x5 < (24 : ℕ) + x3.size ∧ x6 < (24 : ℕ) + x3.size ∧ (∀ x7 ∈ x4, x7.1 < (24 : ℕ) + x3.size ∧ x7.2 < (24 : ℕ) + x3.size) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), ((x4.any fun (x8 : ℕ × ℕ) => PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.1 && PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x8.2) = Bool.true ↔ x2 x7) ∧ (¬x2 x7 → PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x5 = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ PEqualNP.BlindGate.wireValue x3 (24 : ℕ) x7 x6 = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))))) := by
  dsimp only
  let mem_to : ∀ {z : Fin (13 : ℕ)},
      z ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] →
      z ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inl h)) fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))) fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))))) fun h =>
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (List.mem_singleton.mp h)))))))
  let mem_of : ∀ {z : Fin (13 : ℕ)},
      z ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) →
      z ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] := fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.head _) fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.tail _ (List.Mem.head _)) fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) fun h =>
    (Finset.mem_singleton.mp h) ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  exact Exists.elim hStarCircuit fun C hC =>
    Exists.elim hC fun ps hps =>
      Exists.elim hps fun w5 hw5 =>
        Exists.elim hw5 fun w6 h =>
          ⟨C, ps, w5, w6, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
            fun x =>
              let hx := h.2.2.2.2.2.2.2 x
              let heq : ∀ {b : Bool}, (b = Bool.true ↔ _) := fun {_} => Iff.rfl
              have hfx :
                  ((x (0 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
                  (x (1 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
                  (x (2 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
                  (x (3 : Fin (24 : ℕ)) && (x (17 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
                  (x (4 : Fin (24 : ℕ)) && (x (16 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
                  (x (5 : Fin (24 : ℕ)) && (x (15 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
                  (x (6 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ)))) ||
                  (x (7 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)) || x (20 : Fin (24 : ℕ)))) ||
                  (x (8 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (19 : Fin (24 : ℕ)))) ||
                  (x (9 : Fin (24 : ℕ)) && (x (14 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (17 : Fin (24 : ℕ)) || x (23 : Fin (24 : ℕ)))) ||
                  (x (10 : Fin (24 : ℕ)) && (x (13 : Fin (24 : ℕ)) || x (14 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (22 : Fin (24 : ℕ)))) ||
                  (x (11 : Fin (24 : ℕ)) && (x (12 : Fin (24 : ℕ)) || x (13 : Fin (24 : ℕ)) || x (15 : Fin (24 : ℕ)) || x (21 : Fin (24 : ℕ))))) = Bool.true ↔
                  ∃ (u v : Fin (12 : ℕ)),
                    Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∧
                    x (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
                    x (Fin.natAdd (12 : ℕ) v) = Bool.true :=
                Iff.trans (hStarEquiv x)
                  ⟨fun h1 => Exists.elim h1 fun u hu => Exists.elim hu fun v hv => ⟨u, v, mem_to hv.1, hv.2⟩,
                   fun h1 => Exists.elim h1 fun u hu => Exists.elim hu fun v hv => ⟨u, v, mem_of hv.1, hv.2⟩⟩
              ⟨Iff.trans (hx.1 ▸ Iff.rfl) hfx,
               fun hnx => hx.2 (Bool.eq_false_iff.mpr fun ht => hnx (hfx.mp ht))⟩⟩
