import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_140_aux

def A (F : Type) [CommRing F] : Fin 6 → Fin 3 → F
  | 0, a => if a = 0 then 1 else 0
  | 1, a => if a = 1 then 1 else 0
  | 2, a => if a = 2 then 1 else 0
  | 3, a => if a = 0 ∨ a = 1 then 1 else 0
  | 4, a => if a = 0 ∨ a = 2 then 1 else 0
  | 5, a => if a = 1 ∨ a = 2 then 1 else 0

def C (F : Type) [CommRing F] : Fin 6 → Fin 3 → Fin 3 → F
  | 0, 0, c => if c = 0 then 1 else 0
  | 0, 1, c => if c = 0 then -1 else 0
  | 0, 2, c => if c = 0 then -1 else 0
  | 1, 0, c => if c = 1 then -1 else 0
  | 1, 1, c => if c = 1 then 1 else 0
  | 1, 2, c => if c = 1 then -1 else 0
  | 2, 0, c => if c = 2 then -1 else 0
  | 2, 1, c => if c = 2 then -1 else 0
  | 2, 2, c => if c = 2 then 1 else 0
  | 3, 0, c => if c = 1 then 1 else 0
  | 3, 1, c => if c = 0 then 1 else 0
  | 3, 2, _ => 0
  | 4, 0, c => if c = 2 then 1 else 0
  | 4, 1, _ => 0
  | 4, 2, c => if c = 0 then 1 else 0
  | 5, 0, _ => 0
  | 5, 1, c => if c = 2 then 1 else 0
  | 5, 2, c => if c = 1 then 1 else 0

def D (F : Type) [CommRing F] : Fin 6 → Fin 3 → Fin 3 → F
  | 0, _, d => if d = 0 then 1 else 0
  | 1, _, d => if d = 1 then 1 else 0
  | 2, _, d => if d = 2 then 1 else 0
  | 3, 0, d => if d = 1 then 1 else 0
  | 3, 1, d => if d = 0 then 1 else 0
  | 3, 2, _ => 0
  | 4, 0, d => if d = 2 then 1 else 0
  | 4, 1, _ => 0
  | 4, 2, d => if d = 0 then 1 else 0
  | 5, 0, _ => 0
  | 5, 1, d => if d = 2 then 1 else 0
  | 5, 2, d => if d = 1 then 1 else 0

end PEqualNP.Outside.L_gct_140_aux

theorem PEqualNP.Outside.L_gct_140 : ∀ (F : Type) [Field F], PEqualNP.RiffleRank.RiffleRankLe 6 (PEqualNP.RiffleRank.pairId (Fin 3) F) := by
  intro F _
  refine ⟨fun i a b c d =>
      PEqualNP.Outside.L_gct_140_aux.A F i a *
      PEqualNP.Outside.L_gct_140_aux.C F i b c *
      PEqualNP.Outside.L_gct_140_aux.D F i b d,
    fun i => ⟨PEqualNP.Outside.L_gct_140_aux.A F i,
      PEqualNP.Outside.L_gct_140_aux.C F i,
      PEqualNP.Outside.L_gct_140_aux.D F i,
      fun _ _ _ _ => rfl⟩,
    fun a b c d => ?_⟩
  rw [Fin.sum_univ_six]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [PEqualNP.RiffleRank.pairId, PEqualNP.Outside.L_gct_140_aux.A,
      PEqualNP.Outside.L_gct_140_aux.C, PEqualNP.Outside.L_gct_140_aux.D]
