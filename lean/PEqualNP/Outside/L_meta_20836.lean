import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20836_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩

def pt (n u v : ℕ) : ℕ → Bool := fun k => decide (k = u ∨ k = n + v)

def onl (n : ℕ) (Q : ℕ → Bool) : List Bool := (List.range (n + n)).map Q

theorem onl_len (n : ℕ) (Q : ℕ → Bool) : (onl n Q).length = n + n := by simp [onl]

theorem onl_get (n : ℕ) (Q : ℕ → Bool) (k : ℕ) (hk : k < n + n) : (onl n Q).getD k false = Q k := by
  simp [onl, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem one_onl (n : ℕ) (u v : Fin n) : PEqualNP.Represents.oneEach u v = onl n (pt n u v) := by
  refine List.ext_getElem (by simp [PEqualNP.Represents.oneEach, onl]) fun k h1 h2 => ?_
  have hk : k < n + n := by simpa [onl] using h2
  simp only [PEqualNP.Represents.oneEach, onl, List.getElem_map, List.getElem_range, pt]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := v.isLt
    omega
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := u.isLt
    omega

theorem vmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (Q R : ℕ → Bool) (h : ∀ k, Q k = true → R k = true) (w : ℕ)
    (hw : (run C.gates (onl n Q)).getD w false = true) : (run C.gates (onl n R)).getD w false = true := by
  refine mono C.gates (onl n Q) (onl n R) (by simp [onl]) ?_ (fun g hg => by simpa using (hC g hg).1) w hw
  intro i hi
  by_cases hin : i < n + n
  · rw [onl_get n _ i hin] at hi ⊢; exact h i hi
  · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega)] at hi; cases hi


def adj (u v : Fin 5) := (31388771 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[10,6]⟩,⟨.or,[2,3]⟩,⟨.or,[12,4]⟩,⟨.or,[7,8]⟩,⟨.or,[14,9]⟩,⟨.and,[13,15]⟩,⟨.or,[5,11]⟩,⟨.or,[17,16]⟩],18⟩

theorem upper : PEqualNP.Represents.RepSizeAtMost adj 9 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem forced : ∀ k : Fin 10, ∃ a b c d : Fin 5, adj a b = true ∧ adj c d = false ∧
    ∀ j : Fin 10, j ≠ k → pt 5 a b j = true → pt 5 c d j = true := by decide +kernel

theorem lower : ¬ PEqualNP.Represents.RepSizeAtMost adj 8 := by
  rintro ⟨C, hC, hs, hr⟩
  obtain ⟨S, hS, hd⟩ := det C.gates 10 (fun g hg => (hC g hg).2) {C.output}
  have hv (u v : Fin 5) : (run C.gates (onl 5 (pt 5 u v))).getD C.output false = adj u v := by
    rw [← one_onl]
    exact hr u v
  have sub : Finset.range 10 ⊆ S := by
    intro k hk
    have hk' : k < 10 := Finset.mem_range.mp hk
    by_contra habs
    obtain ⟨a,b,c,d,hab,hcd,himp⟩ := forced ⟨k,hk'⟩
    let Q : ℕ → Bool := fun j => if j = k then false else pt 5 a b j
    have eq := hd (onl 5 (pt 5 a b)) (onl 5 Q) (by simp [onl]) (by simp [onl])
    have heq : (run C.gates (onl 5 (pt 5 a b))).getD C.output false =
        (run C.gates (onl 5 Q)).getD C.output false := by
      apply eq _ C.output (by simp)
      intro j hj
      by_cases h : j < 10
      · have hne : j ≠ k := fun e => habs (e ▸ hj)
        rw [onl_get, onl_get] <;> simp_all [Q]
      · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega), List.getD_eq_default _ _ (by rw [onl_len]; omega)]
    have hpos : (run C.gates (onl 5 Q)).getD C.output false = true := heq.symm.trans ((hv a b).trans hab)
    have hbad := vmono 5 C hC Q (pt 5 c d) (by
      intro j h
      by_cases he : j = k
      · simp [Q, he] at h
      · have hj : pt 5 a b j = true := by simpa [Q,he] using h
        have hjlt : j < 10 := by
          simp only [pt, decide_eq_true_eq] at hj
          have := a.isLt
          have := b.isLt
          omega
        exact himp ⟨j,hjlt⟩ (fun eq => he (congrArg Fin.val eq)) hj) C.output hpos
    rw [hv c d, hcd] at hbad
    contradiction
  have hcard := Finset.card_le_card sub
  simp only [Finset.card_range] at hcard
  simp only [Finset.card_singleton] at hS
  change C.gates.length ≤ 8 at hs
  omega

end PEqualNP.Outside.L_meta_20836_aux

theorem PEqualNP.Outside.L_meta_20836 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31388771 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31388771 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_20836_aux.upper, PEqualNP.Outside.L_meta_20836_aux.lower⟩
