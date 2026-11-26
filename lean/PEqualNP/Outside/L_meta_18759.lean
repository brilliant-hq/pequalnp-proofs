import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18759

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stp_ext : ∀ (gs : List Gate) (w : List Bool), ∃ r, gs.foldl stp w = w ++ r := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr⟩ := ih (stp w g)
    exact ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: r, by rw [List.foldl_cons, hr]; simp [stp]⟩

end PEqualNP.Outside.L_meta_18759

open PEqualNP.Outside.L_meta_18759 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18759 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (32 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (32 : ℕ)) (x7 : Fin (32 : ℕ)), (↑x6 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x7 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x6 (0 : ℕ)).testBit (↑x7 - (16 : ℕ)) = Bool.true) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (79 : ℕ) ≤ x1.size := by
  intro C ho hm _ hf
  exfalso
  let o : Fin 32 := ⟨C.output, ho⟩
  let e : Fin 32 → Bool := fun i => decide (i = o)
  have hev : C.eval (List.ofFn e) = true := by
    unfold Circuit.eval Circuit.wires
    obtain ⟨r, hr⟩ := stp_ext C.gates (List.ofFn e)
    change (C.gates.foldl stp (List.ofFn e)).getD C.output false = true
    rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ho)]
    simp only [List.getElem?_ofFn, ho, dite_true, Option.getD_some, e]
    exact decide_eq_true rfl
  obtain ⟨a, b, ⟨ha, hb, _⟩, hea, heb⟩ := (hf e).mp hev
  simp only [e, decide_eq_true_eq] at hea heb
  subst hea
  have : (b : ℕ) = (o : ℕ) := by rw [heb]
  omega
