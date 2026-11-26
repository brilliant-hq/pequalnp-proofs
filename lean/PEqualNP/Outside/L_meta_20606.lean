import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20606
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [ite_eq_right (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dep (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ S : Finset ℕ, S.card ≤ gs.length + T.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = true → y.getD i false = true) →
        ∀ t ∈ T, (run gs x).getD t false = true → (run gs y).getD t false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact fun T => ⟨T, by simp, fun x y _ _ h t ht => by simpa [run] using h t ht⟩
  | append_singleton gs g ih =>
    intro T
    have ih' := ih (fun g' h' => hg g' (by simp [h']))
    have hlen := (hg g (by simp)).2
    by_cases hk : n + gs.length ∈ T
    · obtain ⟨S, hS, hdet⟩ := ih' (T.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, ?_⟩
      · have h1 := Finset.card_union_le (T.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one hk
        have h3 := List.toFinset_card_le g.inputs
        rw [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy t ht
        have hd := hdet x y hx hy hxy
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy]
        by_cases htk : t = n + gs.length
        · rw [ite_eq_left htk, ite_eq_left htk]
          rcases (hg g (by simp)).1 with ho | ho
          · rw [ho]
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
            exact fun ha i hi => hd i (by simp [hi]) (ha i hi)
          · rw [ho]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
            rintro ⟨i, hi, hv⟩
            exact ⟨i, hi, hd i (by simp [hi]) hv⟩
        · rw [ite_eq_right htk, ite_eq_right htk]
          exact hd t (by simp [htk, ht])
    · obtain ⟨S, hS, hdet⟩ := ih' T
      refine ⟨S, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · intro x y hx hy hxy t ht
        have htk : t ≠ n + gs.length := fun h => hk (h ▸ ht)
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy,
          ite_eq_right htk, ite_eq_right htk]
        exact hdet x y hx hy hxy t ht

private def mask (u v : Fin 5) : Bool := (16235520 : ℕ).testBit (5 * u.val + v.val)

private theorem tests : ∀ i : Fin 10, 2 ≤ i.val → i.val ≤ 8 →
    ∃ u v u' v' : Fin 5, mask u v = true ∧ mask u' v' = false ∧
      ∀ j : Fin 10, j.val ≠ i.val → (oneEach u v).getD j.val false = true →
        (oneEach u' v').getD j.val false = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_20606

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_20606

theorem PEqualNP.Outside.L_meta_20606 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16235520 : ℕ).testBit (5 * u.val + v.val)) 6 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16235520 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  constructor
  · let C : Circuit := ⟨[⟨.or,[2,3]⟩, ⟨.or,[10,4]⟩, ⟨.or,[5,6]⟩,
        ⟨.or,[12,7]⟩, ⟨.or,[13,8]⟩, ⟨.and,[11,14]⟩], 15⟩
    refine ⟨C, ?_, by decide, by decide +kernel⟩
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rintro ⟨C, hmono, hsize, hrep⟩
    obtain ⟨S, hcard, hmonoS⟩ := dep 10 C.gates hmono {C.output}
    have sub : Finset.Icc 2 8 ⊆ S := by
      intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      by_contra hout
      obtain ⟨u,v,u',v',hpos,hneg,hh⟩ := tests ⟨i, by omega⟩ hlo hhi
      have hl : ∀ a b : Fin 5, (oneEach a b).length = 10 := by simp [oneEach]
      have h := hmonoS (oneEach u v) (oneEach u' v') (hl _ _) (hl _ _) (by
        intro j hj hjpos
        by_cases hj10 : j < 10
        · exact hh ⟨j, hj10⟩ (fun (heq : j = i) => hout (heq ▸ hj)) hjpos
        · rw [List.getD_eq_default _ _ (by rw [hl]; omega)] at hjpos
          contradiction) C.output (by simp)
      change C.eval (oneEach u v) = true → C.eval (oneEach u' v') = true at h
      rw [hrep, hrep] at h
      exact Bool.noConfusion (hneg.symm.trans (h hpos))
    have hseven : 7 ≤ S.card := by simpa using Finset.card_le_card sub
    change C.gates.length ≤ 5 at hsize
    simp only [Finset.card_singleton] at hcard
    omega
