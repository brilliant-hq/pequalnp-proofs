import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[
  ⟨.or,[6,8]⟩,
  ⟨.or,[2,9]⟩,
  ⟨.or,[0,10]⟩,
  ⟨.or,[7,11]⟩,
  ⟨.or,[4,12]⟩,
  ⟨.or,[3,13]⟩,
  ⟨.or,[5,14]⟩,
  ⟨.or,[1,15]⟩,
  ⟨.or,[0,20]⟩,
  ⟨.or,[16,13]⟩,
  ⟨.or,[3,22]⟩,
  ⟨.or,[10,23]⟩,
  ⟨.or,[18,22]⟩,
  ⟨.or,[20,23]⟩,
  ⟨.or,[24,25]⟩,
  ⟨.or,[25,26]⟩,
  ⟨.and,[6,8]⟩,
  ⟨.and,[21,27]⟩,
  ⟨.and,[17,30]⟩,
  ⟨.and,[28,29]⟩,
  ⟨.and,[19,31]⟩,
  ⟨.or,[32,33]⟩,
  ⟨.or,[37,34]⟩,
  ⟨.or,[38,35]⟩,
  ⟨.or,[39,36]⟩],40⟩

theorem upper : RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨circuit,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19723

theorem PEqualNP.Outside.L_meta_19723 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  obtain ⟨C,hc,hs,hr⟩ := PEqualNP.Outside.L_meta_19723.upper
  exact ⟨C,hc,by omega,hr⟩
