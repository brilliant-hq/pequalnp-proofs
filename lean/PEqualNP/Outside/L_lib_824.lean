import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_824

open PEqualNP.CircuitLowerBounds

def Legal (n : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))

noncomputable def paid (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

noncomputable def cost (C : Circuit) : ℕ := C.gates.countP paid

def wf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (C : Circuit) (p : ℕ) (x : List Bool) : List Bool := (C.gates.take p).foldl wf x

def F (C : Circuit) (p : ℕ) (x : List Bool) (b : Bool) : Bool :=
  ((C.gates.drop (p+1)).foldl wf (W C p x ++ [b])).getD C.output false

theorem set_eval (C : Circuit) (p : ℕ) (hp : p < C.gates.length) (g' : Gate) (x : List Bool) :
    (⟨C.gates.set p g', C.output⟩ : Circuit).eval x =
      F C p x (g'.op.eval (g'.inputs.map fun i => (W C p x).getD i false)) := by
  simp only [Circuit.eval, Circuit.wires]
  rw [List.set_eq_take_append_cons_drop, if_pos hp, List.foldl_append, List.foldl_cons]
  rfl

theorem decomp (l : List Gate) (p : ℕ) (hp : p < l.length) :
    l = l.take p ++ l[p] :: l.drop (p+1) := by
  conv_lhs => rw [← List.set_getElem_self hp]
  rw [List.set_eq_take_append_cons_drop, if_pos hp]

theorem set_cost (C : Circuit) (p : ℕ) (hp : p < C.gates.length) (g' : Gate)
    (h1 : paid C.gates[p] = true) (h2 : paid g' = false) :
    cost ⟨C.gates.set p g', C.output⟩ < cost C := by
  simp only [cost]
  rw [List.set_eq_take_append_cons_drop, if_pos hp]
  conv_rhs => rw [decomp C.gates p hp]
  rw [List.countP_append, List.countP_append, List.countP_cons, List.countP_cons, h1, h2]
  simp

theorem set_legal (n : ℕ) (C : Circuit) (hC : Legal n C) (p : ℕ) (hp : p < C.gates.length)
    (g' : Gate)
    (hop : g'.inputs.length ≤ 2 ∧
      (g'.op = .and ∨ g'.op = .or ∨ g'.op = .mod 2 ∨ (g'.op = .not ∧ g'.inputs.length = 1)))
    (hin : ∀ i ∈ g'.inputs, i ∈ (C.gates[p]).inputs) :
    Legal n ⟨C.gates.set p g', C.output⟩ := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_set] at hi
    by_cases hpj : p = j
    · subst hpj
      rw [if_pos rfl, if_pos hp] at hi
      have := hC.1 p hp i
      apply this
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hp]
      exact hin i (by simpa using hi)
    · rw [if_neg hpj] at hi
      exact hC.1 j hj' i (by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
        exact hi)
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hC.2 g h
    · subst h; exact hop

def s (v : Bool) : ℤ := if v then -1 else 1

theorem ident_and (G : Bool → Bool) (A B : Bool) :
    2 * s (G (GateOp.and.eval [A, B])) = s (G (GateOp.or.eval [])) + s (G (GateOp.or.eval [A])) +
      s (G ((GateOp.mod 2).eval [A, B])) - s (G (GateOp.not.eval [B])) := by
  cases A <;> cases B <;> cases h0 : G false <;> cases h1 : G true <;>
    simp [GateOp.eval, s, h0, h1]

theorem ident_or (G : Bool → Bool) (A B : Bool) :
    2 * s (G (GateOp.or.eval [A, B])) = s (G (GateOp.or.eval [A])) + s (G (GateOp.or.eval [B])) +
      s (G (GateOp.and.eval [])) - s (G ((GateOp.mod 2).eval [A, B])) := by
  cases A <;> cases B <;> cases h0 : G false <;> cases h1 : G true <;>
    simp [GateOp.eval, s, h0, h1]

theorem core (n : ℕ) (C : Circuit) (hC : Legal n C) (hc : 0 < cost C) :
    ∃ D : Fin 4 → Circuit, (∀ i, Legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        2 * s (C.eval (List.ofFn x)) = s ((D 0).eval (List.ofFn x)) + s ((D 1).eval (List.ofFn x)) +
          s ((D 2).eval (List.ofFn x)) - s ((D 3).eval (List.ofFn x)) := by
  obtain ⟨g, hg, hpd⟩ := List.countP_pos_iff.1 hc
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
  have hpd' := hpd
  simp only [paid, decide_eq_true_eq] at hpd'
  obtain ⟨hop, hlen⟩ := hpd'
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  have hCe : ∀ x, C.eval x = F C p x (C.gates[p].op.eval
      (C.gates[p].inputs.map fun i => (W C p x).getD i false)) := by
    intro x
    have := set_eval C p hp C.gates[p] x
    rw [List.set_getElem_self] at this
    exact this
  have mk : ∀ R : Fin 4 → Gate, (∀ i, paid (R i) = false ∧ (R i).inputs.length ≤ 2 ∧
      ((R i).op = .and ∨ (R i).op = .or ∨ (R i).op = .mod 2 ∨
        ((R i).op = .not ∧ (R i).inputs.length = 1)) ∧
      ∀ w ∈ (R i).inputs, w ∈ (C.gates[p]).inputs) →
      ∀ i, Legal n (⟨C.gates.set p (R i), C.output⟩ : Circuit) ∧
        cost (⟨C.gates.set p (R i), C.output⟩ : Circuit) < cost C := by
    intro R hR i
    obtain ⟨h1, h2, h3, h4⟩ := hR i
    exact ⟨set_legal n C hC p hp (R i) ⟨h2, h3⟩ h4, set_cost C p hp (R i) hpd h1⟩
  rcases hop with ho | ho
  · let R : Fin 4 → Gate := ![⟨.or, []⟩, ⟨.or, [a]⟩, ⟨.mod 2, [a, b]⟩, ⟨.not, [b]⟩]
    refine ⟨fun i => ⟨C.gates.set p (R i), C.output⟩, mk R ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [R, paid, hab]
    · intro x
      simp only []
      rw [set_eval C p hp, set_eval C p hp, set_eval C p hp, set_eval C p hp, hCe, ho, hab]
      exact ident_and (F C p (List.ofFn x)) _ _
  · let R : Fin 4 → Gate := ![⟨.or, [a]⟩, ⟨.or, [b]⟩, ⟨.and, []⟩, ⟨.mod 2, [a, b]⟩]
    refine ⟨fun i => ⟨C.gates.set p (R i), C.output⟩, mk R ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [R, paid, hab]
    · intro x
      simp only []
      rw [set_eval C p hp, set_eval C p hp, set_eval C p hp, set_eval C p hp, hCe, ho, hab]
      exact ident_or (F C p (List.ofFn x)) _ _

end PEqualNP.Outside.L_lib_824

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_824 in
theorem PEqualNP.Outside.L_lib_824 : ∀ n : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let sig := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ C : Circ, legal n C → 0 < cost C →
    ∃ D : Fin 4 → Circ,
      (∀ i, legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        let bits := List.ofFn x
        2*sig (C.eval bits) = sig ((D 0).eval bits) + sig ((D 1).eval bits) +
          sig ((D 2).eval bits) - sig ((D 3).eval bits) := by
  intro n Circ legal cost sig C hl hc
  exact core n C hl hc
