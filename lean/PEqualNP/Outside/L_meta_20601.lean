import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20601_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

def graph (u v : Fin 5) := (32997376 : Nat).testBit (5 * u.val + v.val)

def witness : Circuit :=
  ⟨[⟨.or, [5,6]⟩, ⟨.or, [10,7]⟩, ⟨.or, [11,8]⟩,
    ⟨.and, [3,12]⟩, ⟨.or, [4,13]⟩], 14⟩

lemma upper : RepSizeAtMost graph 5 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

def readGate (g : Gate) (x : List Bool) := g.op.eval (g.inputs.map (fun i => x.getD i false))
def push (x : List Bool) (g : Gate) := x ++ [readGate g x]

lemma gate_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool)
    (h : ∀ i ∈ g.inputs, x.getD i false = true → y.getD i false = true) :
    readGate g x = true → readGate g y = true := by
  rcases hop with ha | ho
  · change g.op = GateOp.and at ha
    simp only [readGate, ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hx i hi => h i hi (hx i hi)
  · change g.op = GateOp.or at ho
    simp only [readGate, ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h i hi hv⟩

lemma oldWire (x : List Bool) (g : Gate) (i : Nat) (hi : i ≠ x.length) :
    (push x g).getD i false = x.getD i false := by
  by_cases h : i < x.length
  · simp [push, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default, List.getD_eq_default]
    · omega
    · simp [push]; omega

/-- Pull a sufficient set of wires back through the gates, starting at the output.
Replacing a required gate wire by its inputs increases the set size by at most one. -/
lemma support (gs : List Gate) (out N : Nat)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ S : Finset Nat, S.card ≤ gs.length + 1 ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ i ∈ S, x.getD i false = true → y.getD i false = true) →
        (gs.foldl push x).getD out false = true → (gs.foldl push y).getD out false = true := by
  induction gs generalizing N with
  | nil => exact ⟨{out}, by simp, fun _ _ _ _ h => h out (by simp)⟩
  | cons g gs ih =>
    obtain ⟨S, hcard, transfer⟩ := ih (N+1) (fun q hq => legal q (by simp [hq]))
    obtain ⟨hop, hlen⟩ := legal g (by simp)
    let T := if N ∈ S then S.erase N ∪ g.inputs.toFinset else S
    refine ⟨T, ?_, ?_⟩
    · by_cases hn : N ∈ S
      · have h₁ := Finset.card_union_le (S.erase N) g.inputs.toFinset
        have h₂ := Finset.card_erase_add_one hn
        have h₃ := g.inputs.toFinset_card_le
        simp only [T, hn, ↓reduceIte, List.length_cons]
        omega
      · simpa [T, hn] using (show S.card ≤ gs.length + 1 + 1 by omega)
    · intro x y hx hy h
      apply transfer (push x g) (push y g) (by simp [push,hx]) (by simp [push,hy])
      intro i hi
      by_cases he : i = N
      · subst i
        have atEnd (z : List Bool) (hz : z.length = N) :
            (push z g).getD N false = readGate g z := by
          rw [← hz]; simp [push, List.getD_eq_getElem?_getD]
        rw [atEnd x hx, atEnd y hy]
        apply gate_mono g hop
        intro j hj
        exact h j (by simp [T, hi, hj])
      · rw [oldWire x g i (by omega), oldWire y g i (by omega)]
        apply h i
        by_cases hn : N ∈ S <;> simp [T, hn, he, hi]

def required : Finset Nat := {3,4,5,6,7,8}

lemma separated : ∀ k : Fin 10, k.val ∈ required →
    ∃ u v u' v' : Fin 5, graph u v = true ∧ graph u' v' = false ∧
      ∀ i : Fin 10, i ≠ k → (oneEach u v).getD i.val false = true →
        (oneEach u' v').getD i.val false = true := by decide +kernel

lemma lower : ¬ RepSizeAtMost graph 4 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨S, hcard, transfer⟩ := support C.gates C.output 10 hm
  have hsub : required ⊆ S := by
    intro k hk
    have hlt : k < 10 := by
      simp [required] at hk
      rcases hk with h|h|h|h|h|h <;> omega
    obtain ⟨u,v,u',v',hpos,hneg,hord⟩ := separated ⟨k,hlt⟩ hk
    by_contra hmiss
    have hold : C.eval (oneEach u v) = true := (hr u v).trans hpos
    have hnew : C.eval (oneEach u' v') = true := by
      apply transfer (oneEach u v) (oneEach u' v') (by simp [oneEach]) (by simp [oneEach]) _ hold
      intro i hi
      by_cases hil : i < 10
      · exact hord ⟨i,hil⟩ (by intro e; have hik : i = k := congrArg Fin.val e; exact hmiss (hik ▸ hi))
      · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
        simp
    rw [hr, hneg] at hnew
    contradiction
  have hneed := Finset.card_le_card hsub
  have hsize : required.card = 6 := by decide
  change C.gates.length ≤ 4 at hs
  omega

end PEqualNP.Outside.L_meta_20601_aux

theorem PEqualNP.Outside.L_meta_20601 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32997376 : ℕ).testBit (5 * u.val + v.val)) 5 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32997376 : ℕ).testBit (5 * u.val + v.val)) 4 := by
  exact ⟨PEqualNP.Outside.L_meta_20601_aux.upper, PEqualNP.Outside.L_meta_20601_aux.lower⟩
