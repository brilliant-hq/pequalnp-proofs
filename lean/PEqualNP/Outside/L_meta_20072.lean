import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20072

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def mk (b : Bool) (x y : ℕ) : Gate := ⟨if b then GateOp.or else GateOp.and, [x, y]⟩

def spec : List (Bool × ℕ × ℕ) :=
  [ (true, 8, 10), (true, 9, 14), (true, 13, 15), (true, 11, 12),
    (true, 11, 15), (true, 8, 12), (true, 9, 10), (true, 12, 14),
    (true, 17, 13), (true, 24, 11), (true, 16, 17), (true, 16, 19),
    (true, 20, 23), (true, 18, 22), (true, 21, 18), (true, 16, 20),
    (true, 24, 12),
    (false, 0, 25), (false, 1, 26), (false, 2, 27), (false, 3, 28),
    (false, 4, 29), (false, 5, 30), (false, 6, 31), (false, 7, 32),
    (true, 33, 34), (true, 35, 36), (true, 37, 38), (true, 39, 40),
    (true, 41, 42), (true, 43, 44), (true, 45, 46) ]

def gates : List Gate := spec.map (fun t => mk t.1 t.2.1 t.2.2)

def C : Circuit := ⟨gates, 47⟩

theorem mk_good (b : Bool) (x y : ℕ) :
    (mk b x y).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (mk b x y).inputs.length ≤ 2 := by
  refine ⟨?_, by simp [mk]⟩
  cases b <;> simp [mk]

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, gates, List.mem_map] at hg
  obtain ⟨t, -, rfl⟩ := hg
  exact mk_good t.1 t.2.1 t.2.2

theorem sz : C.size ≤ 32 := by decide

theorem represents :
    Represents (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide

end PEqualNP.Outside.L_meta_20072

theorem PEqualNP.Outside.L_meta_20072 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  ⟨PEqualNP.Outside.L_meta_20072.C, PEqualNP.Outside.L_meta_20072.mono,
    PEqualNP.Outside.L_meta_20072.sz, PEqualNP.Outside.L_meta_20072.represents⟩