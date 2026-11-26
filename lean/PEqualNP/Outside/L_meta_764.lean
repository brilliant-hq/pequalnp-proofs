import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem hcs_mono {m : Nat} {f : (Fin m -> Bool) -> Bool} {a b : Nat}
    (h : HasCircuitSize m f a) (hab : a <= b) : HasCircuitSize m f b := by
  obtain ⟨C, hfan, hsize, hsem⟩ := h
  exact ⟨C, hfan, Nat.le_trans hsize hab, hsem⟩

end PEqualNP.Outside.L_meta_764_aux

theorem PEqualNP.Outside.L_meta_764 :
    forall s : Nat, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 -> Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s
      ↔ 6 <= s := by
  intro s
  let g : (Fin 3 -> Bool) -> Bool := fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)
  have hfun : (fun x : Fin 5 -> Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
      = (fun x : Fin 5 -> Bool => (x 0 && x 1) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
    funext x
    revert x
    decide
  rw [hfun]
  have hnc : ∃ y y' : Fin 3 -> Bool, g y ≠ g y' :=
    ⟨fun _ => false, fun j => decide (j.val <= 1), by decide⟩
  have key : forall t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 -> Bool => (x 0 && x 1) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) (t + 2)
      ↔ PEqualNP.MetaComplexity.HasCircuitSize 3 g t := by
    intro t
    have h := PEqualNP.MetaComplexity.L153 3 t g hnc
    convert h using 2
    funext x
    revert x
    decide
  have hL : forall t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 3 g t ↔ 4 <= t := by
    intro t
    exact PEqualNP.MetaComplexity.L100 t
  rcases Nat.lt_or_ge s 2 with h2 | h2
  · constructor
    · intro h
      have h2' : PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 -> Bool => (x 0 && x 1) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) 2 :=
        PEqualNP.Outside.L_meta_764_aux.hcs_mono h (by omega)
      have h3 : PEqualNP.MetaComplexity.HasCircuitSize 3 g 0 := (key 0).1 h2'
      have h4 : 4 <= 0 := (hL 0).1 h3
      omega
    · intro hb
      omega
  · have hsub : s - 2 + 2 = s := by omega
    calc PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 -> Bool => (x 0 && x 1) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) s
        ↔ PEqualNP.MetaComplexity.HasCircuitSize 5
          (fun x : Fin 5 -> Bool => (x 0 && x 1) || g (fun j : Fin 3 => x (Fin.natAdd 2 j))) (s - 2 + 2) := by rw [hsub]
      _ ↔ PEqualNP.MetaComplexity.HasCircuitSize 3 g (s - 2) := key (s - 2)
      _ ↔ 4 <= s - 2 := hL (s - 2)
      _ ↔ 6 <= s := by omega
