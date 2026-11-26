import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19835_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 12]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [25, 17]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [30, 18]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [33, 16]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [36, 16]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10768418131862349930 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19835_aux

theorem PEqualNP.Outside.L_meta_19835 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10768418131862349930 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19835_aux.main
