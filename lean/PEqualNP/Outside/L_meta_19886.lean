import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19886

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mkGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def specs : List (Bool × Nat × Nat) :=
  [(true, 12, 13), (true, 8, 9), (true, 10, 11), (true, 14, 15), (true, 14, 18),
   (true, 9, 10), (true, 21, 15), (true, 22, 16), (false, 0, 23), (true, 16, 20),
   (false, 1, 25), (true, 9, 11), (true, 27, 13), (true, 28, 19), (false, 2, 29),
   (true, 8, 16), (true, 31, 19), (false, 3, 32), (true, 10, 17), (true, 34, 19),
   (false, 4, 35), (true, 11, 16), (true, 37, 17), (false, 5, 38), (true, 17, 20),
   (false, 6, 40), (true, 8, 12), (true, 42, 15), (true, 43, 18), (false, 7, 44),
   (true, 24, 26), (true, 46, 30), (true, 47, 33), (true, 48, 36), (true, 49, 39),
   (true, 50, 41), (true, 51, 45)]

def wit : Circuit := ⟨specs.map mkGate, 52⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ specs.map mkGate from hg)
  cases b <;> simp [mkGate]

end PEqualNP.Outside.L_meta_19886

open PEqualNP.Outside.L_meta_19886 in
theorem PEqualNP.Outside.L_meta_19886 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11335344517058034870 : ℕ).testBit (8 * u.val + v.val)) 37) :=
  ⟨wit, wit_mono, by decide, by decide +kernel⟩
