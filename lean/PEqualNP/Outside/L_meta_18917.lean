import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_18917_aux

noncomputable def deriv (n : ℕ) (C : Circuit) (w : ℕ → Bool) (s i : ℕ) : Bool :=
  Nat.strongRecOn i fun i rec =>
    if i < n then decide (i = s) else
      let g := gateAt C (i-n)
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      let da := if h : a < i then rec a h else false
      let db := if h : b < i then rec b h else false
      if g.op.eval [false,true] then da || db else w a && db || da && w b

lemma deriv_input (n : ℕ) (C : Circuit) (w : ℕ → Bool) (s i : ℕ) (hi : i < n) :
    deriv n C w s i = decide (i=s) := by
  rw [deriv, Nat.strongRecOn_eq]
  simp [hi]

lemma deriv_gate (n : ℕ) (C : Circuit) (w : ℕ → Bool) (s k : ℕ)
    (g : Gate) (a b : ℕ) (ao : IsAO2 n C)
    (hg : C.gates[k]? = some g) (hab : g.inputs = [a,b]) :
    (g.op = .and → deriv n C w s (n+k) = (w a && deriv n C w s b || deriv n C w s a && w b)) ∧
    (g.op = .or → deriv n C w s (n+k) = (deriv n C w s a || deriv n C w s b)) := by
  have hk : k < C.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
  have gat : gateAt C k = g := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, hg]
    rfl
  have ha : a < n+k := ao.2.1 k hk a (by rw [gat, hab]; simp)
  have hb : b < n+k := ao.2.1 k hk b (by rw [gat, hab]; simp)
  have eqn : deriv n C w s (n+k) =
      if g.op.eval [false,true] then deriv n C w s a || deriv n C w s b
      else w a && deriv n C w s b || deriv n C w s a && w b := by
    conv_lhs => rw [deriv, Nat.strongRecOn_eq]
    simp only [show ¬ n+k<n by omega, ↓reduceIte, Nat.add_sub_cancel_left, gat, hab]
    simp only [List.getD_cons_zero, List.getD_cons_succ, ha, hb, ↓reduceDIte]
    rfl
  constructor
  · intro hop
    simpa [hop, GateOp.eval] using eqn
  · intro hop
    simpa [hop, GateOp.eval] using eqn

theorem terminal
    (n : ℕ) (C : Circuit) (j u v s : ℕ) (x : Fin n → Bool)
    (ao : IsAO2 n C) (out : C.output = n+j) (_last : j+1 = C.size)
    (hg : C.gates[j]? = some ⟨.and,[u,v]⟩) :
    let w : ℕ → Bool := fun k => (C.wires (List.ofFn x)).getD k false
    w u = false → w v = false →
    ∃ d : ℕ → Bool,
      (∀ i < n, d i = decide (i=s)) ∧
      (∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (n+k) = (w a && d b || d a && w b)) ∧
        (g.op = .or → d (n+k) = (d a || d b))) ∧
      d C.output = false := by
  intro w hu hv
  refine ⟨deriv n C w s, deriv_input n C w s, ?_, ?_⟩
  · intro k g a b h1 h2
    exact deriv_gate n C w s k g a b ao h1 h2
  · rw [out, (deriv_gate n C w s j ⟨.and,[u,v]⟩ u v ao hg rfl).1 rfl, hu, hv]
    simp

end PEqualNP.Outside.L_meta_18917_aux

theorem PEqualNP.Outside.L_meta_18917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false := by
  exact PEqualNP.Outside.L_meta_18917_aux.terminal
