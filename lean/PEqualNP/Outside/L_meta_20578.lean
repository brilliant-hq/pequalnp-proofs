import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseColTree

namespace PEqualNP.Outside.L_meta_20578
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.PromiseColTree

def asGate (t : Nat × Nat × Nat) : Gate :=
  if t.1 = 0 then ⟨.and, [t.2.1, t.2.2]⟩ else if t.1 = 1 then ⟨.or, [t.2.1, t.2.2]⟩ else ⟨.not, [t.2.1]⟩

set_option maxRecDepth 100000 in
def codes : List (Nat × Nat × Nat) := [
(1,0,47),(1,21,25),(1,6,10),(1,13,52),(1,19,54),(1,9,62),(1,35,36),(1,24,42),(1,25,59),(1,10,51),(1,5,20),(1,28,44),(1,4,46),(1,15,36),
(1,29,37),(1,2,45),(1,3,41),(1,8,16),(1,14,43),(1,64,68),(1,26,42),(1,24,25),(1,48,65),(1,13,18),(1,18,60),(1,34,69),(1,55,61),(1,17,61),
(1,11,53),(1,45,62),(1,9,32),(1,0,66),(1,4,80),(1,39,64),(1,8,55),(1,27,71),(1,27,79),(1,28,60),(1,1,40),(1,1,101),(1,33,58),(1,58,82),
(1,2,94),(1,30,92),(1,50,74),(1,40,76),(1,23,73),(1,31,83),(1,67,81),(1,91,111),(1,69,74),(1,97,114),(1,104,115),(1,36,63),(1,79,117),(1,110,118),
(1,6,32),(1,82,120),(1,86,121),(1,93,122),(1,34,71),(1,98,124),(1,102,125),(1,49,63),(1,95,127),(1,105,128),(1,78,88),(1,106,130),(1,17,39),(1,85,132),
(1,89,133),(1,107,134),(1,22,70),(1,84,136),(1,112,137),(1,35,57),(1,33,139),(1,65,140),(1,95,141),(1,15,52),(1,69,143),(1,75,144),(1,109,145),(1,84,93),
(1,96,147),(1,102,148),(1,9,56),(1,70,150),(1,85,151),(1,88,152),(1,0,22),(1,7,154),(1,72,155),(1,90,156),(1,33,75),(1,99,158),(1,108,159),(1,12,38),
(1,28,161),(1,66,162),(1,87,100),(1,113,164),(1,16,28),(1,70,166),(1,78,167),(1,97,168),(1,4,57),(1,21,170),(1,26,171),(1,90,172),(1,99,173),(1,43,113),
(1,75,87),(1,98,176),(1,107,177),(1,54,77),(1,103,179),(1,112,180),(1,12,31),(1,72,182),(1,89,183),(1,86,103),(1,108,185),(1,18,41),(1,39,187),(1,77,188),
(1,110,189),(1,3,26),(1,11,191),(1,52,104),(1,53,66),(1,77,194),(1,80,195),(1,106,196),(1,13,68),(1,76,198),(1,105,199),(1,39,50),(1,81,201),(1,96,202),
(1,20,67),(1,72,204),(1,73,205),(1,78,206),(1,15,48),(1,83,208),(1,65,67),(1,100,210),(1,109,211),(0,116,119),(0,123,126),(0,129,131),(0,135,138),(0,142,146),
(0,149,153),(0,157,160),(0,163,165),(0,169,174),(0,175,178),(0,181,184),(0,186,190),(0,192,193),(0,197,200),(0,203,207),(0,209,212),(1,213,214),(1,215,229),(1,216,230),
(1,217,231),(1,218,232),(1,219,233),(1,220,234),(1,221,235),(1,222,236),(1,223,237),(1,224,238),(1,225,239),(1,226,240),(1,227,241),(1,228,242)]

def circuit : Circuit := ⟨codes.map asGate, 243⟩

def rows : List ℕ := [0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050]

theorem fan : FanInTwo circuit := by
  intro g hg
  obtain ⟨⟨a, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  simp only [asGate]
  split
  · simp
  · split <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem good : PEqualNP.Represents.Represents
    (fun u v : Fin 32 => (rows.getD u.val 0).testBit v.val) circuit := by
  apply represents_of_tcols (N := 10) (D := 8) (by decide) circuit rows
  · have hh : rows.all (fun x => decide (x < 2 ^ 32)) = true := by decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hh x hx)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_20578

open PEqualNP.Outside.L_meta_20578 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20578 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 180 ∧ PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨circuit, fan, by decide +kernel, good⟩
