import PEqualNP.MetaComplexity.L107
import PEqualNP.Outside.Pre_L_meta_9753_bridge

namespace PEqualNP.Outside.Pre_L_meta_9753_l107

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.Outside.Pre_L_meta_9753_bridge

def bits14 (n : ℕ) : Fin 14 → Bool := fun i => n.testBit i.val

theorem full_dep : ∃ p : Fin 14, Dep fullTarget p := by
  refine ⟨0, bits14 128, ?_⟩
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_restr_nc : RestrNC fullTarget := by
  intro p _ b
  fin_cases p <;> cases b
  all_goals first
    | exact ⟨bits14 0, bits14 384, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 640, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 1152, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 2176, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 4352, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 8704, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 257, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 513, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 1025, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 2050, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 4098, by decide +kernel⟩
    | exact ⟨bits14 0, bits14 8194, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_no_funnel : NoFunnel fullTarget := by
  apply noFunnel_of_sep
  intro p q hpq _ _
  fin_cases p <;> fin_cases q <;> simp_all
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | exact ⟨bits14 1, by decide +kernel⟩
    | exact ⟨bits14 2, by decide +kernel⟩
    | exact ⟨bits14 4, by decide +kernel⟩
    | exact ⟨bits14 8, by decide +kernel⟩
    | exact ⟨bits14 16, by decide +kernel⟩
    | exact ⟨bits14 32, by decide +kernel⟩
    | exact ⟨bits14 64, by decide +kernel⟩
    | exact ⟨bits14 128, by decide +kernel⟩
    | exact ⟨bits14 256, by decide +kernel⟩
    | exact ⟨bits14 512, by decide +kernel⟩
    | exact ⟨bits14 1024, by decide +kernel⟩
    | exact ⟨bits14 2048, by decide +kernel⟩
    | exact ⟨bits14 4096, by decide +kernel⟩
    | exact ⟨bits14 8192, by decide +kernel⟩

theorem full_fanout_step (h : HasCircuitSize 14 fullTarget 26) :
    ∃ y : Fin 14, Dep fullTarget y ∧ Pays fullTarget y 26 :=
  fanout_step 13 fullTarget 26 full_dep full_restr_nc full_no_funnel h

end PEqualNP.Outside.Pre_L_meta_9753_l107
