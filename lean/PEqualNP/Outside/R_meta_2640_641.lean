import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_4857
import PEqualNP.Outside.L_meta_7810

/-!
# Wip2640 — `L-meta-2640` from the cofactor statement

Given a minimal fan-in-two circuit `D` computing the nested-cover function of `G`,
the cofactor provides an induced odd cycle, an edge `(u, v)` of it and a circuit `B`
of size `≤ D.size − 7` computing the function of `G` under inputs pinned at `u, v`.

We attach seven explicit gates to `B` (the "OR-variables" star terms) and collapse
them again with a chain of seven `eraseGate` steps, exactly the shape required by
`L-meta-2640`.
-/

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover (graphFun)
open PEqualNP.Outside.L_meta_7810 (step wires_eq getD_snoc getD_big fold_len fold_stab
  len_erase out_erase)

/-- Pinning an input to `false` at the two vertices `u`, `v`. -/
def pinF {n : ℕ} (u v : Fin n) (y : Fin n → Bool) : Fin n → Bool :=
  Function.update (Function.update y u Bool.false) v Bool.false

theorem pinF_idem {n : ℕ} (u v : Fin n) (y : Fin n → Bool) :
    pinF u v (pinF u v y) = pinF u v y := by
  funext a
  unfold pinF
  by_cases h1 : a = u <;> by_cases h2 : a = v <;>
    simp [Function.update, h1, h2]

/-- The pinned value at `u` is `false`. -/
theorem pinU {n : ℕ} (u v : Fin n) (z : Fin n → Bool) : pinF u v z u = Bool.false := by
  unfold pinF
  by_cases huv : u = v
  · subst huv
    rw [Function.update_self]
  · rw [Function.update_of_ne huv, Function.update_self]

/-- The pinned value at `v` is `false`. -/
theorem pinV {n : ℕ} (u v : Fin n) (z : Fin n → Bool) : pinF u v z v = Bool.false := by
  unfold pinF
  rw [Function.update_self]

/-- Away from the endpoints the pinning is the identity. -/
theorem pinOther {n : ℕ} (u v : Fin n) (z : Fin n → Bool) {q : Fin n}
    (hu : q ≠ u) (hv : q ≠ v) : pinF u v z q = z q := by
  unfold pinF
  rw [Function.update_of_ne hv, Function.update_of_ne hu]

/-- Reads of a function-list agree with the function. -/
theorem ofg {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i Bool.false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h),
    List.getElem_ofFn]

/-- Binary OR of two explicit values. -/
theorem any2 : ∀ (x y : Bool), [x, y].any id = (x || y) := by
  decide

/-- Binary AND of two explicit values. -/
theorem all2 : ∀ (x y : Bool), [x, y].all id = (x && y) := by
  decide

/-- Binary OR gates evaluate as the disjunction of their two reads. -/
theorem eval_or2 (i j : ℕ) (f : ℕ → Bool) :
    (⟨GateOp.or, [i, j]⟩ : Gate).op.eval
      ((⟨GateOp.or, [i, j]⟩ : Gate).inputs.map f) = (f i || f j) := by
  show [f i, f j].any id = (f i || f j)
  rw [any2]

/-- Binary AND gates evaluate as the conjunction of their two reads. -/
theorem eval_and2 (i j : ℕ) (f : ℕ → Bool) :
    (⟨GateOp.and, [i, j]⟩ : Gate).op.eval
      ((⟨GateOp.and, [i, j]⟩ : Gate).inputs.map f) = (f i && f j) := by
  show [f i, f j].all id = (f i && f j)
  rw [all2]

/-- Reads below the base length survive an append. -/
theorem gd_lt : ∀ (W l : List Bool) (p : ℕ), p < W.length →
    (W ++ l).getD p Bool.false = W.getD p Bool.false := by
  intro W l p hp
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append, if_pos hp]

/-- Reads inside an appended block see the block's own values. -/
theorem gd_idx (W l : List Bool) (k : ℕ) (hk : k < l.length) :
    (W ++ l).getD (W.length + k) Bool.false = l.getD k Bool.false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append, if_neg (by omega : ¬(W.length + k < W.length)),
    Nat.add_sub_cancel_left]

/-- The seventh entry of a seven-element list. -/
theorem g7 : ∀ (v0 v1 v2 v3 v4 v5 v6 : Bool),
    ([v0, v1, v2, v3, v4, v5, v6] : List Bool).getD 6 Bool.false = v6 := by
  decide

/-! ## The seven attached gates -/

/-- The star-term gates for the edge `(u, v)` with neighbourhoods
`{v, a, b}` at `u` and `{u, c, d}` at `v`. -/
def addGates (n : ℕ) (B : Circuit) (u v a b c d : Fin n) : List Gate :=
  [⟨GateOp.or, [(v : ℕ), (a : ℕ)]⟩,
   ⟨GateOp.or, [n + B.size, (b : ℕ)]⟩,
   ⟨GateOp.and, [(u : ℕ), n + B.size + 1]⟩,
   ⟨GateOp.or, [(c : ℕ), (d : ℕ)]⟩,
   ⟨GateOp.and, [(v : ℕ), n + B.size + 3]⟩,
   ⟨GateOp.or, [n + B.size + 2, n + B.size + 4]⟩,
   ⟨GateOp.or, [B.output, n + B.size + 5]⟩]

/-- `B` extended with the seven star-term gates; the new output is the last wire. -/
def extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n) : Circuit :=
  ⟨B.gates ++ addGates n B u v a b c d, n + B.size + 6⟩

theorem len_addGates (n : ℕ) (B : Circuit) (u v a b c d : Fin n) :
    (addGates n B u v a b c d).length = 7 := by
  unfold addGates
  simp

theorem size_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n) :
    (extC n B u v a b c d).size = B.size + 7 := by
  unfold extC PEqualNP.CircuitLowerBounds.Circuit.size
  rw [List.length_append, len_addGates]

theorem fanInTwo_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
    (hB : FanInTwo B) : FanInTwo (extC n B u v a b c d) := by
  intro g hg
  unfold extC addGates at hg
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with hg | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hB g hg
  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
  · exact ⟨Or.inl rfl, Nat.le_refl _⟩
  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
  · exact ⟨Or.inl rfl, Nat.le_refl _⟩
  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
  · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩

/-! ## Valuing the extended circuit -/

theorem foldVals (n : ℕ) (B : Circuit) (u v a b c d : Fin n) (W : List Bool)
    (hW : W.length = n) (hbnd : B.output < n + B.size) :
    (addGates n B u v a b c d).foldl step (B.gates.foldl step W) =
      B.gates.foldl step W ++
        [W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false,
          (W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
            W.getD (b : ℕ) Bool.false,
          W.getD (u : ℕ) Bool.false &&
            ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
              W.getD (b : ℕ) Bool.false),
          W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false,
          W.getD (v : ℕ) Bool.false &&
            (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false),
          (W.getD (u : ℕ) Bool.false &&
            ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
              W.getD (b : ℕ) Bool.false)) ||
            (W.getD (v : ℕ) Bool.false &&
              (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false)),
          (B.gates.foldl step W).getD (B.output : ℕ) Bool.false ||
            ((W.getD (u : ℕ) Bool.false &&
              ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
                W.getD (b : ℕ) Bool.false)) ||
              (W.getD (v : ℕ) Bool.false &&
                (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false)))] := by
  set P := B.gates.foldl step W with hP
  have rdP : ∀ (l : List Bool) (j : Fin n),
      (P ++ l).getD (j : ℕ) Bool.false = W.getD (j : ℕ) Bool.false := by
    intro l j
    have hj : (j : ℕ) < n := Fin.isLt j
    have hl : (n : ℕ) ≤ P.length := by
      show (n : ℕ) ≤ (B.gates.foldl step W).length
      rw [fold_len, hW]
      omega
    rw [gd_lt P l _ (Nat.lt_of_lt_of_le hj hl)]
    exact fold_stab B.gates W _ (by rw [hW]; exact hj)
  have rd0 : ∀ j : Fin n,
      P.getD (j : ℕ) Bool.false = W.getD (j : ℕ) Bool.false :=
    fun j => fold_stab B.gates W j (by rw [hW]; exact Fin.isLt j)
  have rdg : ∀ (l : List Bool) (k : ℕ), k < l.length →
      (P ++ l).getD (P.length + k) Bool.false = l.getD k Bool.false :=
    fun l k hk => gd_idx P l k hk
  have rdg0 : ∀ (a : Bool) (rest : List Bool),
      (P ++ (a :: rest)).getD P.length Bool.false = (a :: rest).getD 0 Bool.false :=
    fun a rest => gd_idx P (a :: rest) 0 (by simp)
  have rdH : ∀ (l : List Bool) (p : ℕ), p < P.length →
      (P ++ l).getD p Bool.false = P.getD p Bool.false :=
    fun l p hp => gd_lt P l p hp
  unfold addGates
  simp only [List.foldl_cons, List.foldl_nil]
  have hlenP : (n + B.size : ℕ) = P.length := by
    show n + B.gates.length = (B.gates.foldl step W).length
    rw [fold_len, hW]
  have e0 : step P ⟨GateOp.or, [(v : ℕ), (a : ℕ)]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false] := by
    rw [step, eval_or2, rd0 v, rd0 a]
  have e1 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false])
      ⟨GateOp.or, [n + B.size, (b : ℕ)]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false] := by
    rw [step, eval_or2, hlenP, rdg0, rdP _ b]
    simp
  have e2 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
      (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false])
      ⟨GateOp.and, [(u : ℕ), n + B.size + 1]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)] := by
        rw [step, eval_and2, rdP _ u, hlenP, rdg _ 1 (by simp)]
        simp
  have e3 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
      (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
      W.getD (u : ℕ) false &&
        ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)])
      ⟨GateOp.or, [(c : ℕ), (d : ℕ)]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false] := by
    rw [step, eval_or2, rdP _ c, rdP _ d]
    simp
  have e4 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
      (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
      W.getD (u : ℕ) false &&
        ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
      W.getD (c : ℕ) false || W.getD (d : ℕ) false])
      ⟨GateOp.and, [(v : ℕ), n + B.size + 3]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false,
        W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)] := by
    rw [step, eval_and2, rdP _ v, hlenP, rdg _ 3 (by simp)]
    simp
  have e5 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
      (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
      W.getD (u : ℕ) false &&
        ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
      W.getD (c : ℕ) false || W.getD (d : ℕ) false,
      W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)])
      ⟨GateOp.or, [n + B.size + 2, n + B.size + 4]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false,
        W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
        (W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
          (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false))] := by
    rw [step, eval_or2, hlenP, rdg _ 2 (by simp), rdg _ 4 (by simp)]
    simp
  have e6 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
      (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
      W.getD (u : ℕ) false &&
        ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
      W.getD (c : ℕ) false || W.getD (d : ℕ) false,
      W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
      (W.getD (u : ℕ) false &&
        ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
        (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false))])
      ⟨GateOp.or, [B.output, n + B.size + 5]⟩ =
      P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false,
        W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
        (W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
          (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
        P.getD (B.output : ℕ) false ||
          ((W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
            (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))] := by
    rw [step, eval_or2, hlenP,
      rdH _ _ (by rw [← hlenP]; exact hbnd), rdg _ 5 (by simp)]
    simp
  rw [e0, e1, e2, e3, e4, e5, e6]

/-- The extended circuit computes `B`'s value plus the two star terms. -/
theorem eval_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
    (hbnd : B.output < n + B.size) (x : Fin n → Bool) :
    (extC n B u v a b c d).eval (List.ofFn x) =
      ((B.eval (List.ofFn x) || (x u && ((x v || x a) || x b))) ||
        (x v && (x c || x d))) := by
  unfold extC Circuit.eval
  rw [wires_eq, List.foldl_append,
    foldVals n B u v a b c d (List.ofFn x) (by simp) hbnd]
  set P := B.gates.foldl step (List.ofFn x)
  have hlen : P.length = n + B.size := by
    show (B.gates.foldl step (List.ofFn x)).length = n + B.gates.length
    rw [fold_len]
    simp
  rw [← hlen]
  rw [gd_idx P _ 6 (by simp)]
  rw [g7]
  have oget : P.getD (B.output : ℕ) Bool.false = B.eval (List.ofFn x) := by
    unfold Circuit.eval
    rw [wires_eq]
  simp only [ofg x (u : ℕ) (Fin.isLt u),
    ofg x (v : ℕ) (Fin.isLt v),
    ofg x (a : ℕ) (Fin.isLt a),
    ofg x (b : ℕ) (Fin.isLt b),
    ofg x (c : ℕ) (Fin.isLt c),
    ofg x (d : ℕ) (Fin.isLt d)]
  rw [oget]
  conv_lhs => rw [← Bool.or_assoc]
  rfl

/-! ## The seven-step erase chain -/

/-- Collapsing the seven attached gates, from the last one downwards. -/
theorem erase_chain (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
    (hout : B.output < n + B.size) :
    ∃ (f : ℕ → Circuit), f 0 = extC n B u v a b c d ∧
      ∀ t < 7, ∃ (m p : ℕ), m < (f t).size ∧
        (p < n + m ∨ n + (f t).size ≤ p) ∧
        f (t + 1) = eraseGate n (f t) m p ∧
        ((∀ z : Fin n → Bool,
            ((f t).wires (List.ofFn (pinF u v z))).getD (n + m) Bool.false =
              ((f t).wires (List.ofFn (pinF u v z))).getD p Bool.false) ∨
          ((f t).output ≠ n + m ∧
            ∀ g ∈ List.drop (m + 1) (f t).gates, n + m ∉ g.inputs)) := by
  set C := extC n B u v a b c d with hC
  set f : ℕ → Circuit := fun t =>
    Nat.rec C (fun i Ci => eraseGate n Ci (B.size + (6 - i))
      (if i = 0 then B.output else n + Ci.size)) t with hf
  have hf0 : f 0 = C := by rw [hf]; rfl
  have hstep : ∀ t, f (t + 1) =
      eraseGate n (f t) (B.size + (6 - t))
        (if t = 0 then B.output else n + (f t).size) := fun _ => rfl
  have hsz : ∀ t ≤ 7, (f t).size = B.size + 7 - t := by
    intro t ht
    induction t with
    | zero => rw [hf0]; exact size_extC n B u v a b c d
    | succ t ih =>
        have h1 : (f t).size = B.size + 7 - t := ih (by omega)
        have hlt : B.size + (6 - t) < (f t).gates.length := by
          show B.size + (6 - t) < (f t).size
          omega
        have heq := len_erase n (f t) (B.size + (6 - t))
          (if t = 0 then B.output else n + (f t).size) hlt
        have h1' : (f t).gates.length = B.size + 7 - t := h1
        rw [hstep]
        show (eraseGate n (f t) (B.size + (6 - t))
          (if t = 0 then B.output else n + (f t).size)).gates.length = _
        omega
  have houtF : ∀ t, 1 ≤ t → t ≤ 7 → (f t).output = B.output := by
    intro t ht1 ht7
    induction t with
    | zero => exact absurd ht1 (by omega)
    | succ t ih =>
        rcases Nat.eq_zero_or_pos t with rfl | ht0
        · -- first step: the output wire is the erased gate's replacement
          have hcl : C.gates.length = B.size + 7 := size_extC n B u v a b c d
          have hm0 : B.size + (6 - 0) < C.gates.length := by omega
          rw [hstep, if_pos rfl, hf0]
          rw [out_erase n C (B.size + (6 - 0)) B.output hm0]
          show eraseRedirect n (B.size + (6 - 0)) B.output (n + B.size + 6) = B.output
          unfold eraseRedirect
          rw [if_pos (by omega : (n + B.size + 6) = n + (B.size + (6 - 0)))]
        · -- later steps: the output sits below every erased wire
          have hszf := hsz t (by omega)
          have hlt : B.size + (6 - t) < (f t).gates.length := by
            show B.size + (6 - t) < (f t).size
            omega
          rw [hstep, if_neg (Nat.ne_of_gt ht0)]
          rw [out_erase n (f t) (B.size + (6 - t)) _ hlt, ih (by omega) (by omega)]
          unfold eraseRedirect
          have hb : (B.output : ℕ) < n + (B.size + (6 - t)) := by omega
          rw [if_neg (fun h : B.output = n + (B.size + (6 - t)) =>
            lt_irrefl _ (hb.trans_le (Nat.le_of_eq h.symm)))]
          rw [if_neg (fun h : n + (B.size + (6 - t)) < B.output => lt_asymm hb h)]
  refine ⟨f, hf0, ?_⟩
  intro t ht
  rcases t with _|s
  · -- erase the output gate; the star terms are false under pinned inputs
    refine ⟨B.size + 6, B.output, ?_, Or.inl (by omega), ?_, Or.inl ?_⟩
    · rw [hf0, size_extC]; omega
    · rw [hstep, if_pos rfl]
    intro z
    set W := List.ofFn (pinF u v z)
    set P := B.gates.foldl step W
    have hlen : P.length = n + B.size := by
      show (B.gates.foldl step W).length = n + B.gates.length
      rw [fold_len]
      simp [W]
    have w0 : (f 0).wires W =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false,
          W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
          (W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
            (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
          P.getD (B.output : ℕ) false ||
            ((W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
              (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))] := by
      rw [hf0, hC]
      unfold extC
      rw [wires_eq, List.foldl_append,
        foldVals n B u v a b c d W
          (by show (List.ofFn (pinF u v z)).length = n; simp) hout]
    have pu : W.getD (u : ℕ) Bool.false = false := by
      rw [ofg _ _ (Fin.isLt u), pinU]
    have pv : W.getD (v : ℕ) Bool.false = false := by
      rw [ofg _ _ (Fin.isLt v), pinV]
    have hlhs : (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false,
          W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
          (W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
            (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
          P.getD (B.output : ℕ) false ||
            ((W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
              (W.getD (v : ℕ) false &&
                (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))]).getD (n + (B.size + 6)) Bool.false =
        P.getD (B.output : ℕ) Bool.false := by
      rw [← Nat.add_assoc, ← hlen, gd_idx P _ 6 (by simp)]
      rw [g7]
      rw [pu, pv]
      simp
    rw [w0]
    exact hlhs.trans
      (gd_lt P _ (B.output : ℕ) (by rw [hlen]; exact hout)).symm
  · -- erase the topmost remaining gate: nothing lives above it
    refine ⟨B.size + (6 - (s + 1)), n + (f (s + 1)).size, ?_,
      Or.inr (le_refl _), ?_, Or.inr ⟨?_, ?_⟩⟩
    · have hszf := hsz (s + 1) (by omega)
      show B.size + (6 - (s + 1)) < (f (s + 1)).size
      omega
    · rw [hstep (s + 1), if_neg (Nat.succ_ne_zero s)]
    · rw [houtF (s + 1) (by omega) (by omega)]
      omega
    · intro g hg
      have hlen : (f (s + 1)).gates.length = B.size + 7 - (s + 1) :=
        hsz (s + 1) (by omega)
      have hdrop : List.drop (B.size + (6 - (s + 1)) + 1) (f (s + 1)).gates = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [hdrop] at hg
      cases hg

/-! ## The reduction -/

/-- `L_meta-2640` follows from the cofactor statement. -/
theorem R_meta_2640_641
    (cof : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (D : Circuit) (m : ℕ) (f g : Fin m ↪ Fin n),
      Odd m →
      (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
      (∀ i j, G.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val) →
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) →
      (7 : ℕ∞) ≤ G.egirth →
      IsMinimalCircuit n D → circuitFun n D = graphFun G A →
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧ ∃ B : Circuit,
        FanInTwo B ∧ B.size + 7 ≤ D.size ∧ B.output < n + B.size ∧
        ∀ x : Fin n → Bool, circuitFun n B x =
          graphFun G A (pinF (f i) (f j) x)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  classical
  intro n G A D notColor degree girth edgeOut hEdges minimal spec
  have G7 : (7 : ℕ∞) ≤ G.egirth :=
    (SimpleGraph.le_egirth (G := G)).2 (fun v w hw => by exact_mod_cast girth v w hw)
  obtain ⟨m, hm, odd, f, g, spokes, edges⟩ :=
    L_meta_4857 n G A notColor degree G7 edgeOut
  have nonIso {z w : Fin n} (h : G.Adj z w) : z ∉ A := fun hz => edgeOut z w h hz
  have deg (v : Fin n) : (G.neighborSet v).ncard = if v ∈ A then 0 else 3 := by
    by_cases hv : v ∈ A
    · have empty : G.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hu => nonIso hu hv)
      simp [hv, empty]
    · simpa [hv] using degree v hv
  have computes : circuitFun n D = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  obtain ⟨i, j, uv, B, fan, bound, hout, specB⟩ :=
    cof n G A D m f g odd spokes edges deg G7 minimal computes
  let u := f i
  let v := f j
  have uv' : G.Adj u v := uv
  have nbrs (z w : Fin n) (h : G.Adj z w) :
      ∃ a b : Fin n, ∀ k, G.Adj z k ↔ k = w ∨ k = a ∨ k = b := by
    have three : (G.neighborSet z).ncard = 3 := by
      simpa only [nonIso h, ite_false] using deg z
    have two : (G.neighborSet z \ {w}).ncard = 2 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show w ∈ G.neighborSet z from h), three]
    obtain ⟨a, b, _, rest⟩ := Set.ncard_eq_two.mp two
    refine ⟨a, b, ?_⟩
    intro k
    by_cases hk : k = w
    · subst k
      simp [h]
    · have same : k ∈ G.neighborSet z \ {w} ↔ G.Adj z k := by simp [hk]
      rw [← same, rest]
      simp [hk]
  obtain ⟨a, b, nbrU⟩ := nbrs u v uv'
  obtain ⟨c, d, nbrV⟩ := nbrs v u uv'.symm
  have split (x : Fin n → Bool) :
      ((B.eval (List.ofFn x) || (x u && ((x v || x a) || x b))) ||
        (x v && (x c || x d))) = graphFun G A x := by
    have yeq : B.eval (List.ofFn x) = graphFun G A (pinF u v x) := by
      change circuitFun n B x = _
      exact specB x
    have ytrue {q : Fin n} (hq : pinF u v x q = true) : x q = true := by
      have hu : q ≠ u := by
        intro h2
        rw [h2] at hq
        rw [pinU u v x] at hq
        exact absurd hq Bool.false_ne_true
      have hv : q ≠ v := by
        intro h2
        rw [h2] at hq
        rw [pinV u v x] at hq
        exact absurd hq Bool.false_ne_true
      exact (pinOther u v x hu hv).symm.trans hq
    have freeA {q : Fin n} (hq : q ∈ A) : pinF u v x q = x q := by
      refine pinOther u v x ?_ ?_
      · intro h2
        rw [h2] at hq
        exact absurd hq (nonIso uv)
      · intro h2
        rw [h2] at hq
        exact absurd hq (nonIso uv.symm)
    have incidentU {q : Fin n} (h : G.Adj u q) (hq : x q = true) :
        (x v = true ∨ x a = true) ∨ x b = true := by
      rcases (nbrU q).mp h with rfl | rfl | rfl
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
    have incidentV {q : Fin n} (hqU : q ≠ u) (h : G.Adj v q) (hq : x q = true) :
        x c = true ∨ x d = true := by
      rcases (nbrV q).mp h with ht | rfl | rfl
      · exact False.elim (hqU ht)
      · exact Or.inl hq
      · exact Or.inr hq
    rw [yeq]
    apply Bool.eq_iff_iff.mpr
    change (((decide (∃ q ∈ A, pinF u v x q = true) ||
      decide (∃ q r, G.Adj q r ∧ pinF u v x q = true ∧ pinF u v x r = true)) ||
      (x u && ((x v || x a) || x b))) || (x v && (x c || x d))) = true ↔
      (decide (∃ q ∈ A, x q = true) ||
        decide (∃ q r, G.Adj q r ∧ x q = true ∧ x r = true)) = true
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (((hA | edgeY) | starU) | starV)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl ⟨q, hq, ytrue val⟩
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeY
        exact Or.inr ⟨q, r, adj, ytrue hq, ytrue hr⟩
      · obtain ⟨hu, (hv | ha) | hb⟩ := starU
        · exact Or.inr ⟨u, v, uv, hu, hv⟩
        · exact Or.inr ⟨u, a, (nbrU a).mpr (Or.inr (Or.inl rfl)), hu, ha⟩
        · exact Or.inr ⟨u, b, (nbrU b).mpr (Or.inr (Or.inr rfl)), hu, hb⟩
      · obtain ⟨hv, hc | hd⟩ := starV
        · exact Or.inr ⟨v, c, (nbrV c).mpr (Or.inr (Or.inl rfl)), hv, hc⟩
        · exact Or.inr ⟨v, d, (nbrV d).mpr (Or.inr (Or.inr rfl)), hv, hd⟩
    · rintro (hA | edgeX)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl (Or.inl (Or.inl ⟨q, hq, (freeA hq).trans val⟩))
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeX
        by_cases huq : q = u
        · subst q
          exact Or.inl (Or.inr ⟨hq, incidentU adj hr⟩)
        by_cases hur : r = u
        · subst r
          exact Or.inl (Or.inr ⟨hr, incidentU adj.symm hq⟩)
        by_cases hvq : q = v
        · subst q
          exact Or.inr ⟨hq, incidentV hur adj hr⟩
        by_cases hvr : r = v
        · subst r
          exact Or.inr ⟨hr, incidentV huq adj.symm hq⟩
        exact Or.inl (Or.inl (Or.inr ⟨q, r, adj,
          (pinOther u v x huq hvq).trans hq, (pinOther u v x hur hvr).trans hr⟩))
  have hfun : circuitFun n (extC n B u v a b c d) = graphFun G A := by
    funext x
    unfold circuitFun
    rw [eval_extC n B u v a b c d hout]
    exact split x
  obtain ⟨F, hF0, hchain⟩ := erase_chain n B u v a b c d hout
  refine ⟨u, v, uv, F, ?_, ?_, ?_, hchain⟩
  · rw [hF0]
    exact fanInTwo_extC n B u v a b c d fan
  · rw [hF0, size_extC]
    exact bound
  · rw [hF0]
    exact hfun.trans computes.symm

end PEqualNP.Outside
