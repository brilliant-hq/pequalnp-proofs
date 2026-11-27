import PEqualNP.Outside.L_meta_25825
import PEqualNP.Outside.L_meta_25826
import PEqualNP.MetaComplexity.Helpers.PermInputs

/-!
# Pre-bridge for the negative twin of L-meta-9753

This local scaffold fixes the exact finite targets and composes the two open
bridge statements with the checked mask-362 obstruction.  It is not a desk
submission: the bridge statements remain explicit hypotheses.
-/

namespace PEqualNP.Outside.Pre_L_meta_9753_bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents
open PEqualNP.MetaComplexity.Helpers.PermInputs

def localTarget (x : Fin 9 → Bool) : Bool :=
  (x 0 && (x 3 || x 4 || x 6)) ||
  (x 1 && (x 3 || x 5 || x 7)) ||
  (x 2 && (x 4 || x 5 || x 8))

def localGraph (u : Fin 3) (v : Fin 6) : Bool :=
  decide
    ((u = 0 ∧ (v = 0 ∨ v = 1 ∨ v = 3)) ∨
     (u = 1 ∧ (v = 0 ∨ v = 2 ∨ v = 4)) ∨
     (u = 2 ∧ (v = 1 ∨ v = 2 ∨ v = 5)))

def oneEachLocal (u : Fin 3) (v : Fin 6) : Fin 9 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 3 + v.val)

theorem localTarget_oneEach (u : Fin 3) (v : Fin 6) :
    localTarget (oneEachLocal u v) = localGraph u v := by
  fin_cases u <;> fin_cases v <;> decide

/-- Mask-362 column order `[8,3,7,6]` in the original nine-input numbering. -/
def col362 : Fin 4 → Fin 6
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 4
  | _ => 3

def restriction362 (u v : Fin 4) : Bool :=
  if h : u.val < 3 then localGraph ⟨u.val, h⟩ (col362 v) else false

theorem restriction362_eq_mask :
    restriction362 = fun u v : Fin 4 => (362 : Nat).testBit (4 * u.val + v.val) := by
  funext u v
  fin_cases u <;> fin_cases v <;> decide

/-- One mask-363 column order `[4,3,7,6]` in original input numbering. -/
def col363 : Fin 4 → Fin 6
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 4
  | _ => 3

def restriction363 (u : Fin 3) (v : Fin 4) : Bool :=
  localGraph u (col363 v)

theorem restriction363_eq_mask :
    restriction363 = fun u v => (363 : Nat).testBit (4 * u.val + v.val) := by
  funext u v
  fin_cases u <;> fin_cases v <;> decide

def Mask362Six : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ Represents restriction362 C

def LocalTenToMask362Six : Prop :=
  HasCircuitSize 9 localTarget 10 → Mask362Six

def restrictedFalse (x : Fin 9 → Bool) : Bool :=
  localTarget (Function.update (Function.update x (4 : Fin 9) false) (5 : Fin 9) false)

/-- Original inputs into the padded mask-362 order: rows 0,1,2; dummy row 3;
columns `[8,3,7,6]`.  Fixed inputs 4 and 5 may map arbitrarily. -/
def pi362 : Fin 9 → Fin 8
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 7
  | ⟨7, _⟩ => 6
  | _ => 4

def promise8 (u v : Fin 4) : Fin 8 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 4 + v.val)

theorem oneEach_eq_ofFn_promise8 (u v : Fin 4) :
    oneEach u v = List.ofFn (promise8 u v) := by
  fin_cases u <;> fin_cases v <;> decide

theorem restrictedFalse_promise8 (u v : Fin 4) :
    restrictedFalse (promise8 u v ∘ pi362) = restriction362 u v := by
  fin_cases u <;> fin_cases v <;> decide

def DoubleFalseSavesFour : Prop :=
  HasCircuitSize 9 localTarget 10 → HasCircuitSize 9 restrictedFalse 6

theorem local_to_mask_of_double_false (saving : DoubleFalseSavesFour) :
    LocalTenToMask362Six := by
  intro hlocal
  have h9 := saving hlocal
  have h8 := relabel_size pi362 restrictedFalse 6 h9
  obtain ⟨C, hfan, hsize, hev⟩ := h8
  refine ⟨C, hfan, hsize, ?_⟩
  intro u v
  rw [oneEach_eq_ofFn_promise8, hev]
  exact restrictedFalse_promise8 u v

theorem no_local_ten_of_bridge (bridge : LocalTenToMask362Six) :
    ¬ HasCircuitSize 9 localTarget 10 := by
  intro hlocal
  obtain ⟨C, hfan, hsize, hrep⟩ := bridge hlocal
  apply PEqualNP.Outside.L_meta_25825
  refine ⟨C, hfan, hsize, ?_⟩
  intro u v
  rw [← restriction362_eq_mask]
  exact hrep u v

theorem no_local_ten_of_double_false (saving : DoubleFalseSavesFour) :
    ¬ HasCircuitSize 9 localTarget 10 :=
  no_local_ten_of_bridge (local_to_mask_of_double_false saving)

def fullTarget (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) ||
  (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) ||
  (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) ||
  (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) ||
  (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) ||
  (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) ||
  (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)

def Full26ToLocalTen : Prop :=
  HasCircuitSize 14 fullTarget 26 → HasCircuitSize 9 localTarget 10

theorem no_full_26_of_bridges
    (outer : Full26ToLocalTen) (inner : LocalTenToMask362Six) :
    ¬ HasCircuitSize 14 fullTarget 26 := by
  intro full
  exact no_local_ten_of_bridge inner (outer full)

end PEqualNP.Outside.Pre_L_meta_9753_bridge
