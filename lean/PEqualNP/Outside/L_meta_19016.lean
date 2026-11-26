import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19016_aux

open PEqualNP.CircuitLowerBounds

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_append (gs : List Gate) (w : List Bool) :
    ∃ T : List Bool, gs.foldl wireStep w = w ++ T := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g rest ih =>
    obtain ⟨T, hT⟩ := ih (wireStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: T, ?_⟩
    rw [List.foldl_cons, hT]
    simp [wireStep]

lemma eval_lt (C : Circuit) (x : Fin 26 → Bool) (hlt : C.output < 26) :
    C.eval (List.ofFn x) = x ⟨C.output, hlt⟩ := by
  unfold Circuit.eval Circuit.wires
  obtain ⟨T, hT⟩ := foldl_append C.gates (List.ofFn x)
  change (C.gates.foldl wireStep (List.ofFn x)).getD C.output false = x ⟨C.output, hlt⟩
  rw [hT, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt),
    List.getElem?_eq_getElem (by simpa using hlt)]
  simp only [Option.getD_some, List.getElem_ofFn]

end PEqualNP.Outside.L_meta_19016_aux

theorem PEqualNP.Outside.L_meta_19016 : (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ x1.output < (26 : ℕ)) := by
  rintro ⟨C, h⟩
  dsimp only at h
  rcases h with ⟨_, _, _, heval, _, _, _, _, _, _, _, _, _, _, _, hlt⟩
  let z : Fin 26 → Bool := fun i => decide (i.val = C.output)
  have hz : C.eval (List.ofFn z) = true := by
    rw [PEqualNP.Outside.L_meta_19016_aux.eval_lt C z hlt]
    simp [z]
  obtain ⟨p, l, _, hp, hl⟩ := (heval z).mp hz
  simp only [z, decide_eq_true_eq] at hp hl
  have h1 : (Fin.castAdd 13 p).val < 13 := p.isLt
  have h2 : 13 ≤ (Fin.natAdd 13 l).val := Nat.le_add_right 13 l.val
  omega
