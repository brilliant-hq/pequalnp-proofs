import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29763

open PEqualNP.CircuitLowerBounds

def Legal (n : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))

noncomputable def paid (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

noncomputable def cost (C : Circuit) : ℕ := C.gates.countP paid

def gA (C : Circuit) (j : ℕ) : Gate := PEqualNP.MetaComplexity.NestedCover.gateAt C j

theorem gA_def (C : Circuit) (j : ℕ) : gA C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl

def stp (e : Gate → (ℕ → Bool) → Bool) (w : List Bool) (g : Gate) : List Bool :=
  w ++ [e g (fun i => w.getD i false)]

theorem gd_app_left (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_app_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD]; simp

theorem gd_out (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem fold_spec (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V') :
    ∀ (l : List Gate) (x : List Bool),
      (l.foldl (stp e) x).length = x.length + l.length ∧
      (∀ i < x.length, (l.foldl (stp e) x).getD i false = x.getD i false) ∧
      ∀ j (hj : j < l.length), (∀ i ∈ (l[j]).inputs, i < x.length + j) →
        (l.foldl (stp e) x).getD (x.length + j) false =
          e l[j] (fun i => (l.foldl (stp e) x).getD i false) := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons g l ih =>
    intro x
    simp only [List.foldl_cons]
    have hx : (stp e x g).length = x.length + 1 := by simp [stp]
    obtain ⟨A, B, Cc⟩ := ih (stp e x g)
    refine ⟨by rw [A, hx]; simp; omega, ?_, ?_⟩
    · intro i hi
      rw [B i (by omega)]
      exact gd_app_left _ _ _ hi
    · intro j hj hin
      rcases j with _ | j
      · simp only [List.getElem_cons_zero, Nat.add_zero] at hin ⊢
        have h0 : (stp e x g).getD x.length false = e g (fun i => x.getD i false) :=
          gd_app_len _ _
        rw [B x.length (by omega), h0]
        apply he
        intro i hi
        have := hin i hi
        rw [B i (by omega)]
        exact (gd_app_left _ _ _ (hin i hi)).symm
      · simp only [List.getElem_cons_succ] at hin ⊢
        have := Cc j (by simp at hj; omega) (by intro i hi; have := hin i hi; omega)
        rw [hx] at this
        rw [show x.length + (j+1) = x.length + 1 + j by omega]
        exact this

theorem fold_get (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V')
    (C : Circuit) (x : List Bool)
    (hrb : ∀ j < C.gates.length, ∀ i ∈ (gA C j).inputs, i < x.length + j) :
    (∀ i < x.length, (C.gates.foldl (stp e) x).getD i false = x.getD i false) ∧
    (∀ j < C.gates.length, (C.gates.foldl (stp e) x).getD (x.length + j) false =
        e (gA C j) (fun i => (C.gates.foldl (stp e) x).getD i false)) ∧
    (∀ i, x.length + C.gates.length ≤ i → (C.gates.foldl (stp e) x).getD i false = false) := by
  obtain ⟨A, B, Cc⟩ := fold_spec e he C.gates x
  have hg : ∀ j (hj : j < C.gates.length), gA C j = C.gates[j] := by
    intro j hj
    rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  refine ⟨B, ?_, ?_⟩
  · intro j hj
    rw [hg j hj]
    exact Cc j hj (by rw [← hg j hj]; exact hrb j hj)
  · intro i hi
    exact gd_out _ _ (by omega)

def ev (g : Gate) (V : ℕ → Bool) : Bool := g.op.eval (g.inputs.map V)

theorem ev_loc : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → ev g V = ev g V' := by
  intro g V V' h
  simp only [ev]
  rw [List.map_congr_left h]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl (stp ev) x := rfl

noncomputable def gc (g : Gate) (V : ℕ → Bool) : Bool :=
  match g.inputs with
  | [a] => V a
  | [a, b] => @ite _ (g.op = .mod 2) (Classical.propDecidable _) (Bool.xor (V a) (V b)) false
  | _ => false

theorem gc_loc : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → gc g V = gc g V' := by
  intro g V V' h
  unfold gc
  split
  · rename_i a ha
    rw [ha] at h; simp at h; rw [h]
  · rename_i a b ha
    rw [ha] at h; simp at h; rw [h.1, h.2]
  · rfl


theorem facts (e : Gate → (ℕ → Bool) → Bool)
    (he : ∀ g V V', (∀ i ∈ g.inputs, V i = V' i) → e g V = e g V')
    (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : List Bool) (hx : x.length = n) :
    (∀ i < n, (C.gates.foldl (stp e) x).getD i false = x.getD i false) ∧
    (∀ j < C.gates.length, (C.gates.foldl (stp e) x).getD (n + j) false =
        e (gA C j) (fun i => (C.gates.foldl (stp e) x).getD i false)) ∧
    (∀ i, n + C.gates.length ≤ i → (C.gates.foldl (stp e) x).getD i false = false) := by
  subst hx
  exact fold_get e he C x (fun j hj i hi => hrb j hj i hi)

theorem gA_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gA C j ∈ C.gates := by
  rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

def WC (C : Circuit) (x : List Bool) (i : ℕ) : Bool := (C.wires x).getD i false

noncomputable def cl (C : Circuit) (t : ℕ) : List Bool := C.gates.foldl (stp gc) (true :: List.replicate t false)

noncomputable def cf (C : Circuit) (t : ℕ) (i : ℕ) : Bool := (cl C t).getD i false

def hit (C : Circuit) (t : ℕ) (j : ℕ) : Prop :=
  paid (gA C j) = true ∧ ∃ a ∈ (gA C j).inputs, cf C t a = true

theorem step_inv (g : Gate)
    (hl : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (Vu V0 c : ℕ → Bool) (u : Bool) (hin : ∀ i ∈ g.inputs, Vu i = Bool.xor (c i && u) (V0 i))
    (hno : ¬ (paid g = true ∧ ∃ a ∈ g.inputs, c a = true)) :
    ev g Vu = Bool.xor (gc g c && u) (ev g V0) := by
  obtain ⟨op, ins⟩ := g
  simp only at hl hin hno
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c', l⟩⟩⟩
  · simp [ev, gc]
  · have ha := hin a (by simp)
    simp only [ev, gc, List.map_cons, List.map_nil, ha]
    rcases hl.2 with h | h | h | ⟨h, _⟩ <;> subst h <;>
      cases c a <;> cases u <;> cases V0 a <;> decide
  · have ha := hin a (by simp)
    have hb := hin b (by simp)
    simp only [ev, gc, List.map_cons, List.map_nil, ha, hb]
    rcases hl.2 with h | h | h | ⟨h, h'⟩
    · subst h
      have hp : paid ⟨GateOp.and, [a, b]⟩ = true := by simp [paid]
      have hca : c a = false := by
        by_contra hc; exact hno ⟨hp, a, by simp, by simpa using hc⟩
      have hcb : c b = false := by
        by_contra hc; exact hno ⟨hp, b, by simp, by simpa using hc⟩
      simp [hca, hcb]
    · subst h
      have hp : paid ⟨GateOp.or, [a, b]⟩ = true := by simp [paid]
      have hca : c a = false := by
        by_contra hc; exact hno ⟨hp, a, by simp, by simpa using hc⟩
      have hcb : c b = false := by
        by_contra hc; exact hno ⟨hp, b, by simp, by simpa using hc⟩
      simp [hca, hcb]
    · subst h
      simp only [ite_true]
      cases c a <;> cases c b <;> cases u <;> cases V0 a <;> cases V0 b <;> decide
    · simp at h'
  · simp at hl

theorem inv (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (u : Bool) (zl : List Bool)
    (hz : zl.length = t) (h : ℕ) (hh : h ≤ C.gates.length) (hno : ∀ j < h, ¬ hit C t j) :
    ∀ w < 1+t+h, WC C (u::zl) w = Bool.xor (cf C t w && u) (WC C (false::zl) w) := by
  have Fu := facts ev ev_loc (1+t) C hC.1 (u::zl) (by simp; omega)
  have F0 := facts ev ev_loc (1+t) C hC.1 (false::zl) (by simp; omega)
  have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  simp only [WC, cf, cl, wires_eq] at ih ⊢
  by_cases hw1 : w < 1 + t
  · rw [Fu.1 w hw1, F0.1 w hw1, Fc.1 w hw1]
    rcases w with _ | i
    · simp
    · simp only [List.getD_cons_succ]
      have : (List.replicate t false).getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      rw [this]; simp
  · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1+t), by omega⟩
    have hj : j < C.gates.length := by omega
    rw [Fu.2.1 j hj, F0.2.1 j hj, Fc.2.1 j hj]
    apply step_inv (gA C j) (hC.2 _ (gA_mem C j hj))
    · intro i hi
      have hib := hC.1 j hj i hi
      exact ih i (by omega) (by omega)
    · exact hno j (by omega)


abbrev mk (F : ℕ → Gate) (M o : ℕ) : Circuit := ⟨(List.range M).map F, o⟩

theorem gA_mk (F : ℕ → Gate) (M o k : ℕ) (hk : k < M) : gA (mk F M o) k = F k := by
  rw [gA_def, List.getD_eq_getElem?_getD]; simp [hk]

theorem len_mk (F : ℕ → Gate) (M o : ℕ) : (mk F M o).gates.length = M := by simp

theorem legal_mk (t : ℕ) (F : ℕ → Gate) (M o : ℕ)
    (h1 : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k)
    (h2 : ∀ k < M, (F k).inputs.length ≤ 2 ∧
      ((F k).op = .and ∨ (F k).op = .or ∨ (F k).op = .mod 2 ∨
        ((F k).op = .not ∧ (F k).inputs.length = 1))) :
    Legal t (mk F M o) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    have hj' : j < M := by simpa using hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt (mk F M o) j = F j := gA_mk F M o j hj'
    rw [e] at hi
    exact h1 j hj' i hi
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact h2 k hk

theorem cost_mk (F : ℕ → Gate) (M o : ℕ) :
    cost (mk F M o) = ∑ k ∈ Finset.range M, if paid (F k) = true then 1 else 0 := by
  induction M with
  | zero => simp [cost]
  | succ M ih =>
    simp only [cost] at ih ⊢
    rw [List.range_succ, List.map_append, List.countP_append, ih, Finset.sum_range_succ]
    simp

theorem gates_eq (C : Circuit) : C.gates = (List.range C.gates.length).map (gA C) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [gA_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl

theorem cost_eq (C : Circuit) :
    cost C = ∑ k ∈ Finset.range C.gates.length, if paid (gA C k) = true then 1 else 0 := by
  have := cost_mk (gA C) C.gates.length C.output
  rw [← this]
  simp only [cost]
  rw [← gates_eq]

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem ev_ren (f : ℕ → ℕ) (g : Gate) (V : ℕ → Bool) : ev (ren f g) V = ev g (fun i => V (f i)) := by
  simp [ev, ren, List.map_map, Function.comp_def]

theorem paid_ren (f : ℕ → ℕ) (g : Gate) : paid (ren f g) = paid g := by
  unfold paid
  rw [decide_eq_decide]
  simp [ren]

def m1 (t w : ℕ) : ℕ := if w = 0 then t else if w ≤ t then w - 1 else w

theorem m1_zero (t : ℕ) : m1 t 0 = t := by simp [m1]

theorem m1_succ (t i : ℕ) (h : i < t) : m1 t (i+1) = i := by
  unfold m1; rw [if_neg (by omega), if_pos (by omega)]; omega

theorem m1_big (t w : ℕ) (h : t < w) : m1 t w = w := by
  unfold m1; rw [if_neg (by omega), if_neg (by omega)]

theorem m1_lt (t w j : ℕ) (h : w < 1 + t + j) : m1 t w < t + 1 + j := by
  unfold m1; split_ifs <;> omega

def Kg : Gate := ⟨.or, []⟩

def FE (C : Circuit) (t k : ℕ) : Gate := if k = 0 then Kg else ren (m1 t) (gA C (k-1))

theorem legal_ren (n : ℕ) (C : Circuit) (hC : Legal n C) (f : ℕ → ℕ) (j : ℕ)
    (hj : j < C.gates.length) :
    (ren f (gA C j)).inputs.length ≤ 2 ∧
      ((ren f (gA C j)).op = .and ∨ (ren f (gA C j)).op = .or ∨ (ren f (gA C j)).op = .mod 2 ∨
        ((ren f (gA C j)).op = .not ∧ (ren f (gA C j)).inputs.length = 1)) := by
  have := hC.2 _ (gA_mem C j hj)
  simpa [ren] using this

theorem rb_mk (t : ℕ) (F : ℕ → Gate) (M o : ℕ)
    (h1 : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack t (mk F M o) := by
  intro j hj i hi
  have hj' : j < M := by simpa using hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt (mk F M o) j = F j := gA_mk F M o j hj'
  rw [e] at hi
  exact h1 j hj' i hi

theorem copy0 (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (F : ℕ → Gate) (M o : ℕ) (h : ℕ)
    (hh : h ≤ C.gates.length) (hM : h + 1 ≤ M)
    (hF0 : F 0 = Kg) (hF : ∀ j < h, F (1 + j) = ren (m1 t) (gA C j))
    (hrb : ∀ k < M, ∀ i ∈ (F k).inputs, i < t + k)
    (zl : List Bool) (hz : zl.length = t) :
    ∀ w < 1 + t + h, WC (mk F M o) zl (m1 t w) = WC C (false :: zl) w := by
  have FD := facts ev ev_loc t (mk F M o) (rb_mk t F M o hrb) zl hz
  have F0 := facts ev ev_loc (1+t) C hC.1 (false::zl) (by simp; omega)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  simp only [WC, wires_eq] at ih ⊢
  by_cases hw0 : w = 0
  · subst hw0
    have e := FD.2.1 0 (by simp; omega)
    rw [gA_mk F M o 0 (by omega), hF0, Nat.add_zero] at e
    rw [m1_zero, e, F0.1 0 (by omega)]
    rfl
  · by_cases hw1 : w ≤ t
    · obtain ⟨i, rfl⟩ : ∃ i, w = i + 1 := ⟨w - 1, by omega⟩
      rw [m1_succ t i (by omega), FD.1 i (by omega), F0.1 (i+1) (by omega)]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1+t), by omega⟩
      have hj : j < h := by omega
      have e := FD.2.1 (1 + j) (by simp; omega)
      rw [gA_mk F M o _ (by omega), hF j hj, ev_ren, show t + (1 + j) = 1 + t + j by omega] at e
      rw [m1_big t _ (by omega), e,
        F0.2.1 j (by omega)]
      apply ev_loc
      intro i hi
      have := hC.1 j (by omega) i hi
      exact ih i (by omega) (by omega)


theorem paid_Kg : paid Kg = false := by simp [paid, Kg]

theorem rb_FE (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) :
    ∀ k < C.gates.length + 1, ∀ i ∈ (FE C t k).inputs, i < t + k := by
  intro k hk i hi
  rcases k with _ | j
  · simp [FE, Kg] at hi
  · simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, ren, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have := hC.1 j (by omega) a ha
    have := m1_lt t a j this
    omega

theorem caseA (t : ℕ) (C : Circuit) (hC : Legal (1+t) C)
    (hno : ∀ j < C.gates.length, ¬ hit C t j) :
    ∃ (a : Bool) (E : Circuit), Legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z)) := by
  let n := C.gates.length
  let E := mk (FE C t) (n+1) (m1 t C.output)
  refine ⟨cf C t C.output, E, ?_, ?_, ?_⟩
  · apply legal_mk t _ _ _ (rb_FE t C hC)
    intro k hk
    rcases k with _ | j
    · simp [FE, Kg]
    · simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact legal_ren (1+t) C hC _ j (by omega)
  · apply le_of_eq
    rw [cost_mk, cost_eq, Finset.sum_range_succ']
    simp only [FE, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, paid_ren, if_true,
      paid_Kg]
    simp [n]
  · intro u z
    have hz : (List.ofFn z).length = t := by simp
    have Fu := facts ev ev_loc (1+t) C hC.1 (u::List.ofFn z) (by simp; omega)
    have F0 := facts ev ev_loc (1+t) C hC.1 (false::List.ofFn z) (by simp; omega)
    have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
    have FE' := facts ev ev_loc t E (rb_mk t _ _ _ (rb_FE t C hC)) (List.ofFn z) hz
    have hcp := copy0 t C hC (FE C t) (n+1) (m1 t C.output) n le_rfl le_rfl (by simp [FE])
      (by intro j _; simp [FE]) (rb_FE t C hC) (List.ofFn z) hz
    have hiv := inv t C hC u (List.ofFn z) hz n le_rfl hno
    show WC C _ C.output = Bool.xor _ (WC E _ (m1 t C.output))
    by_cases ho : C.output < 1 + t + n
    · rw [hiv _ ho, hcp _ ho]
    · simp only [WC, wires_eq, cf, cl]
      rw [Fu.2.2 _ (by omega), Fc.2.2 _ (by omega), m1_big t _ (by omega),
        FE'.2.2 _ (by simp [E]; omega)]
      simp


def m2 (t n h w : ℕ) : ℕ :=
  if w = 0 then t + 1 + h else if w ≤ t then w - 1 else if w < 1 + t + n then w + 1 + h else t

theorem m2_zero (t n h : ℕ) : m2 t n h 0 = t + 1 + h := by simp [m2]

theorem m2_succ (t n h i : ℕ) (hi : i < t) : m2 t n h (i+1) = i := by
  unfold m2; rw [if_neg (by omega), if_pos (by omega)]; omega

theorem m2_mid (t n h w : ℕ) (h1 : t < w) (h2 : w < 1 + t + n) : m2 t n h w = w + 1 + h := by
  unfold m2; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem m2_big (t n h w : ℕ) (h1 : 1 + t + n ≤ w) : m2 t n h w = t := by
  unfold m2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem m2_lt (t n h w j : ℕ) (hw : w < 1 + t + j) (hj : j ≤ n) : m2 t n h w < t + (h + 2 + j) := by
  unfold m2; split_ifs <;> omega

theorem m2_le (t n h w : ℕ) : m2 t n h w ≤ t + 1 + h + n := by
  unfold m2; split_ifs <;> omega

def Ug (t x : ℕ) (b : Bool) : Gate := if b then ⟨.not, [m1 t x]⟩ else ⟨.and, [m1 t x]⟩

def Rg (t n h y : ℕ) (isAnd b : Bool) : Gate :=
  if isAnd then (if b then ⟨.and, [m2 t n h y]⟩ else ⟨.or, []⟩)
  else (if b then ⟨.and, []⟩ else ⟨.and, [m2 t n h y]⟩)

noncomputable def Sg (C : Circuit) (t h : ℕ) (R : Gate) (j : ℕ) : Gate :=
  if j < h ∧ paid (gA C j) = true then ⟨.and, [t+1+j]⟩
  else if j = h then R else ren (m2 t C.gates.length h) (gA C j)

noncomputable def FD (C : Circuit) (t h : ℕ) (U R : Gate) (d : Bool) (k : ℕ) : Gate :=
  if k = 0 then Kg
  else if k ≤ h then ren (m1 t) (gA C (k-1))
  else if k = h + 1 then U
  else if k < h + 2 + C.gates.length then Sg C t h R (k-h-2)
  else if k = h + 2 + C.gates.length then
    ⟨.mod 2, [m2 t C.gates.length h C.output, t+1+h]⟩
  else if d then ⟨.not, [t+2+h+C.gates.length]⟩ else ⟨.and, [m2 t C.gates.length h C.output]⟩

section
variable (C : Circuit) (t h : ℕ) (U R : Gate) (d : Bool)

theorem FD_0 : FD C t h U R d 0 = Kg := by simp [FD]

theorem FD_1 (j : ℕ) (hj : j < h) : FD C t h U R d (1 + j) = ren (m1 t) (gA C j) := by
  unfold FD; rw [if_neg (by omega), if_pos (by omega)]; simp

theorem FD_U : FD C t h U R d (h + 1) = U := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem FD_S (j : ℕ) (hj : j < C.gates.length) : FD C t h U R d (h + 2 + j) = Sg C t h R j := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem FD_g1 : FD C t h U R d (h + 2 + C.gates.length) =
    ⟨.mod 2, [m2 t C.gates.length h C.output, t+1+h]⟩ := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem FD_g2 : FD C t h U R d (h + 3 + C.gates.length) =
    if d then ⟨.not, [t+2+h+C.gates.length]⟩ else ⟨.and, [m2 t C.gates.length h C.output]⟩ := by
  unfold FD; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end

theorem regions (h n k : ℕ) (hk : k < h + n + 4) :
    k = 0 ∨ (∃ j < h, k = 1 + j) ∨ k = h + 1 ∨ (∃ j < n, k = h + 2 + j) ∨
      k = h + 2 + n ∨ k = h + 3 + n := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  by_cases h1 : k ≤ h
  · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega⟩)
  by_cases h2 : k = h + 1
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : k < h + 2 + n
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k - h - 2, by omega, by omega⟩)))
  by_cases h4 : k = h + 2 + n
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

theorem gc_paid (g : Gate) (hp : paid g = true) (V : ℕ → Bool) : gc g V = false := by
  simp only [paid, decide_eq_true_eq] at hp
  obtain ⟨hop, hlen⟩ := hp
  unfold gc
  split
  · rename_i a ha; rw [ha] at hlen; simp at hlen
  · rename_i a b ha
    rcases hop with hop | hop <;> rw [hop] <;> simp
  · rfl

theorem sum_split (f g : ℕ → ℕ) (h n : ℕ) (hhn : h < n) (h1 : ∀ k < h, f k = 0) (h2 : f h = 0)
    (h3 : g h = 1) (h4 : ∀ k, h < k → k < n → f k = g k) :
    ∑ k ∈ Finset.range h, g k + ∑ k ∈ Finset.range n, f k < ∑ k ∈ Finset.range n, g k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = h + (m + 1) := ⟨n - h - 1, by omega⟩
  rw [Finset.sum_range_add f h (m+1), Finset.sum_range_add g h (m+1)]
  simp only [Finset.sum_range_succ']
  have e1 : ∑ k ∈ Finset.range h, f k = 0 := Finset.sum_eq_zero (fun k hk => h1 k (by simpa using hk))
  have e2 : ∑ k ∈ Finset.range m, f (h + (k + 1)) = ∑ k ∈ Finset.range m, g (h + (k + 1)) :=
    Finset.sum_congr rfl (fun k hk => h4 _ (by omega) (by simp at hk; omega))
  rw [e1, e2, Nat.add_zero, h2, h3]
  omega


theorem factsW (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : List Bool) (hx : x.length = n) :
    (∀ i < n, WC C x i = x.getD i false) ∧
    (∀ j < C.gates.length, WC C x (n + j) = ev (gA C j) (WC C x)) ∧
    (∀ i, n + C.gates.length ≤ i → WC C x i = false) :=
  facts ev ev_loc n C hrb x hx

theorem Ug_in (t x : ℕ) (b : Bool) : ∀ i ∈ (Ug t x b).inputs, i = m1 t x := by
  cases b <;> simp [Ug]

theorem Ug_ops (t x : ℕ) (b : Bool) : (Ug t x b).inputs.length ≤ 2 ∧
    ((Ug t x b).op = .and ∨ (Ug t x b).op = .or ∨ (Ug t x b).op = .mod 2 ∨
      ((Ug t x b).op = .not ∧ (Ug t x b).inputs.length = 1)) := by
  cases b <;> simp [Ug]

theorem paid_Ug (t x : ℕ) (b : Bool) : paid (Ug t x b) = false := by
  cases b <;> simp [Ug, paid]

theorem ev_Ug (t x : ℕ) (b : Bool) (V : ℕ → Bool) :
    ev (Ug t x b) V = Bool.xor (V (m1 t x)) b := by
  cases b <;> simp [Ug, ev, GateOp.eval]

theorem Rg_in (t n h y : ℕ) (ia b : Bool) : ∀ i ∈ (Rg t n h y ia b).inputs, i = m2 t n h y := by
  cases ia <;> cases b <;> simp [Rg]

theorem Rg_ops (t n h y : ℕ) (ia b : Bool) : (Rg t n h y ia b).inputs.length ≤ 2 ∧
    ((Rg t n h y ia b).op = .and ∨ (Rg t n h y ia b).op = .or ∨ (Rg t n h y ia b).op = .mod 2 ∨
      ((Rg t n h y ia b).op = .not ∧ (Rg t n h y ia b).inputs.length = 1)) := by
  cases ia <;> cases b <;> simp [Rg]

theorem paid_Rg (t n h y : ℕ) (ia b : Bool) : paid (Rg t n h y ia b) = false := by
  cases ia <;> cases b <;> simp [Rg, paid]

theorem ev_Rg (t n h y : ℕ) (ia b : Bool) (V : ℕ → Bool) :
    ev (Rg t n h y ia b) V = if ia then (b && V (m2 t n h y)) else (b || V (m2 t n h y)) := by
  cases ia <;> cases b <;> simp [Rg, ev, GateOp.eval]

theorem caseB (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) (h : ℕ) (hhn : h < C.gates.length)
    (hhit : hit C t h) (hmin : ∀ j < h, ¬ hit C t j) :
    0 < cost C ∧ ∃ p : (Fin t → Bool) → Bool, ∀ (b d : Bool), ∃ D : Circuit, ∃ π : ℕ → ℕ,
      Legal t D ∧ cost D < cost C ∧ (∀ w, π w < t + D.gates.length) ∧ ∀ z : Fin t → Bool,
        D.eval (List.ofFn z) =
          Bool.xor (C.eval ((Bool.xor (p z) b) :: List.ofFn z)) (d && Bool.xor (p z) b) ∧
        ∀ w, WC D (List.ofFn z) (π w) = WC C ((Bool.xor (p z) b) :: List.ofFn z) w := by
  obtain ⟨hpaid, hsee⟩ := hhit
  have hp' := hpaid
  simp only [paid, decide_eq_true_eq] at hp'
  obtain ⟨hop, hlen⟩ := hp'
  obtain ⟨a1, a2, hins⟩ : ∃ a1 a2, (gA C h).inputs = [a1, a2] := by
    rcases hI : (gA C h).inputs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩
    · rw [hI] at hlen; simp at hlen
    · rw [hI] at hlen; simp at hlen
    · exact ⟨a1, a2, rfl⟩
    · rw [hI] at hlen; simp at hlen
  have ha1 : a1 < 1 + t + h := hC.1 h hhn a1 (by show a1 ∈ (gA C h).inputs; rw [hins]; simp)
  have ha2 : a2 < 1 + t + h := hC.1 h hhn a2 (by show a2 ∈ (gA C h).inputs; rw [hins]; simp)
  let x := if cf C t a1 = true then a1 else a2
  let y := if cf C t a1 = true then a2 else a1
  have hx : cf C t x = true := by
    obtain ⟨a, ha, hca⟩ := hsee
    rw [hins] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    by_cases h1 : cf C t a1 = true
    · simp [x, h1]
    · rcases ha with rfl | rfl
      · exact absurd hca h1
      · simp [x, h1, hca]
  have hxl : x < 1 + t + h := by simp only [x]; split_ifs <;> omega
  have hyl : y < 1 + t + h := by simp only [y]; split_ifs <;> omega
  let isAnd : Bool := @decide ((gA C h).op = .and) (Classical.propDecidable _)
  have hev : ∀ V : ℕ → Bool, ev (gA C h) V = if isAnd then (V x && V y) else (V x || V y) := by
    intro V
    simp only [ev, hins, List.map_cons, List.map_nil]
    rcases hop with hop | hop
    · have hA : isAnd = true := by simp only [isAnd, decide_eq_true_eq]; exact hop
      rw [hA, hop]
      by_cases h1 : cf C t a1 = true <;> simp [x, y, h1, GateOp.eval, Bool.and_comm]
    · have hA : isAnd = false := by
        simp only [isAnd, decide_eq_false_iff_not]; rw [hop]; simp
      rw [hA, hop]
      by_cases h1 : cf C t a1 = true <;> simp [x, y, h1, GateOp.eval, Bool.or_comm]
  refine ⟨?_, fun z => WC C (false :: List.ofFn z) x, ?_⟩
  · rw [cost_eq]
    have := Finset.single_le_sum (f := fun k => if paid (gA C k) = true then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hhn)
    simp only [hpaid, if_true] at this
    omega
  intro b d
  let U := Ug t x b
  let R := Rg t C.gates.length h y isAnd b
  let D := mk (FD C t h U R d) (h + C.gates.length + 4) (t + 3 + h + C.gates.length)
  have hrb : ∀ k < h + C.gates.length + 4, ∀ i ∈ (FD C t h U R d k).inputs, i < t + k := by
    intro k hk i hi
    rcases regions h C.gates.length k hk with rfl | ⟨j, hj, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    · rw [FD_0] at hi; simp [Kg] at hi
    · rw [FD_1 C t h U R d j hj] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have := m1_lt t a j (hC.1 j (by omega) a ha)
      omega
    · rw [FD_U] at hi
      have := m1_lt t x h hxl
      rw [Ug_in t x b i hi]
      omega
    · rw [FD_S C t h U R d j hj] at hi
      unfold Sg at hi
      split_ifs at hi with h1 h2
      · simp at hi; omega
      · rw [Rg_in _ _ _ _ _ _ i hi]
        have := m2_lt t C.gates.length h y h hyl (by omega)
        omega
      · simp only [ren, List.mem_map] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        exact m2_lt _ _ _ _ _ (hC.1 j hj a ha) (le_of_lt hj)
    · rw [FD_g1] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := m2_le t C.gates.length h C.output
      rcases hi with rfl | rfl <;> omega
    · rw [FD_g2] at hi
      have := m2_le t C.gates.length h C.output
      cases d <;> simp at hi <;> omega
  have hops : ∀ k < h + C.gates.length + 4, (FD C t h U R d k).inputs.length ≤ 2 ∧
      ((FD C t h U R d k).op = .and ∨ (FD C t h U R d k).op = .or ∨
        (FD C t h U R d k).op = .mod 2 ∨
        ((FD C t h U R d k).op = .not ∧ (FD C t h U R d k).inputs.length = 1)) := by
    intro k hk
    rcases regions h C.gates.length k hk with rfl | ⟨j, hj, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    · rw [FD_0]; simp [Kg]
    · rw [FD_1 C t h U R d j hj]; exact legal_ren (1+t) C hC _ j (by omega)
    · rw [FD_U]; exact Ug_ops t x b
    · rw [FD_S C t h U R d j hj]
      unfold Sg
      split_ifs
      · simp
      · exact Rg_ops _ _ _ _ _ _
      · exact legal_ren (1+t) C hC _ j hj
    · rw [FD_g1]; simp
    · rw [FD_g2]; cases d <;> simp
  refine ⟨D, m2 t C.gates.length h, legal_mk t _ _ _ hrb hops, ?_,
    fun w => by have := m2_le t C.gates.length h w; simp only [D, List.length_map, List.length_range]; omega, ?_⟩
  · rw [cost_mk, cost_eq]
    rw [show h + C.gates.length + 4 = (1 + h) + (1 + (C.gates.length + 2)) by omega,
      Finset.sum_range_add _ (1 + h), Finset.sum_range_add _ 1 h,
      Finset.sum_range_add _ 1 (C.gates.length + 2), Finset.sum_range_add _ C.gates.length 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
    have e1 : ∑ k ∈ Finset.range h, (if paid (FD C t h U R d (1 + k)) = true then 1 else 0) =
        ∑ k ∈ Finset.range h, (if paid (gA C k) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => by
        rw [FD_1 C t h U R d k (by simpa using hk), paid_ren])
    have e2 : ∑ k ∈ Finset.range C.gates.length,
        (if paid (FD C t h U R d (1 + h + (1 + k))) = true then 1 else 0) =
        ∑ k ∈ Finset.range C.gates.length, (if paid (Sg C t h R k) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => by
        rw [show 1 + h + (1 + k) = h + 2 + k by omega, FD_S C t h U R d k (by simpa using hk)])
    have e3 : paid (FD C t h U R d (1 + h)) = false := by
      rw [show 1 + h = h + 1 by omega, FD_U]; exact paid_Ug t x b
    have e4 : paid (FD C t h U R d (1 + h + (1 + C.gates.length))) = false := by
      rw [show 1 + h + (1 + C.gates.length) = h + 2 + C.gates.length by omega, FD_g1]
      simp [paid]
    have e5 : paid (FD C t h U R d (1 + h + (1 + (C.gates.length + 1)))) = false := by
      rw [show 1 + h + (1 + (C.gates.length + 1)) = h + 3 + C.gates.length by omega, FD_g2]
      cases d <;> simp [paid]
    simp only [e1, e2, e3, e4, e5, FD_0, paid_Kg]
    have key := sum_split (fun k => if paid (Sg C t h R k) = true then 1 else 0)
      (fun k => if paid (gA C k) = true then 1 else 0) h C.gates.length hhn
      (by
        intro k hk
        have e : paid (Sg C t h R k) = false := by
          unfold Sg
          by_cases hp : paid (gA C k) = true
          · rw [if_pos ⟨hk, hp⟩]; simp [paid]
          · rw [if_neg (by tauto), if_neg (by omega), paid_ren]; simpa using hp
        simp [e])
      (by
        have e : paid (Sg C t h R h) = false := by
          unfold Sg; rw [if_neg (by omega), if_pos rfl]; exact paid_Rg _ _ _ _ _ _
        simp [e])
      (by simp [hpaid])
      (by
        intro k hk1 hk2
        have e : paid (Sg C t h R k) = paid (gA C k) := by
          unfold Sg; rw [if_neg (by omega), if_neg (by omega), paid_ren]
        simp [e])
    simp only [Bool.false_eq_true, if_false]
    omega
  · intro z
    have hz : (List.ofFn z).length = t := by simp
    obtain ⟨uu, huu⟩ : ∃ uu, uu = Bool.xor (WC C (false :: List.ofFn z) x) b := ⟨_, rfl⟩
    show WC D (List.ofFn z) (t + 3 + h + C.gates.length) =
      Bool.xor (WC C (Bool.xor (WC C (false :: List.ofFn z) x) b :: List.ofFn z) C.output)
        (d && Bool.xor (WC C (false :: List.ofFn z) x) b) ∧
      ∀ w, WC D (List.ofFn z) (m2 t C.gates.length h w) =
        WC C (Bool.xor (WC C (false :: List.ofFn z) x) b :: List.ofFn z) w
    rw [← huu]
    have Fu := factsW (1+t) C hC.1 (uu :: List.ofFn z) (by simp; omega)
    have Fc := facts gc gc_loc (1+t) C hC.1 (true :: List.replicate t false) (by simp; omega)
    have FW := factsW t D (rb_mk t _ _ _ hrb) (List.ofFn z) hz
    have hcp := copy0 t C hC (FD C t h U R d) (h + C.gates.length + 4)
      (t + 3 + h + C.gates.length) h (le_of_lt hhn) (by omega) (FD_0 C t h U R d)
      (fun j hj => FD_1 C t h U R d j hj) hrb (List.ofFn z) hz
    have hiv := inv t C hC uu (List.ofFn z) hz h (le_of_lt hhn) hmin
    have gD : ∀ k < h + C.gates.length + 4, gA D k = FD C t h U R d k :=
      fun k hk => gA_mk _ _ _ k hk
    have hU : WC D (List.ofFn z) (t + 1 + h) = uu := by
      have e := FW.2.1 (h + 1) (by simp [D]; omega)
      rw [gD _ (by omega), FD_U, ev_Ug, hcp x hxl] at e
      rw [show t + 1 + h = t + (h + 1) by omega, e, huu]
    have hWx : WC C (uu :: List.ofFn z) x = b := by
      rw [hiv x hxl, hx, huu]
      cases b <;> simp
    have hV0 : WC D (List.ofFn z) t = false := by
      have e := FW.2.1 0 (by simp [D])
      rw [gD _ (by omega), FD_0, Nat.add_zero] at e
      rw [e]; simp [ev, Kg, GateOp.eval]
    have claim : ∀ w, WC D (List.ofFn z) (m2 t C.gates.length h w) = WC C (uu :: List.ofFn z) w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      by_cases w0 : w = 0
      · subst w0
        rw [m2_zero, hU, Fu.1 0 (by omega)]; simp
      by_cases w1 : w ≤ t
      · obtain ⟨i, rfl⟩ : ∃ i, w = i + 1 := ⟨w - 1, by omega⟩
        rw [m2_succ _ _ _ i (by omega), FW.1 i (by omega), Fu.1 (i+1) (by omega)]
        simp
      by_cases w2 : w < 1 + t + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = 1 + t + j := ⟨w - (1 + t), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [m2_mid _ _ _ _ (by omega) w2, show 1 + t + j + 1 + h = t + (h + 2 + j) by omega,
          FW.2.1 (h + 2 + j) (by simp [D]; omega), gD _ (by omega),
          FD_S C t h U R d j hj]
        unfold Sg
        split_ifs with hA hB
        · have e := hcp (1 + t + j) (by omega)
          rw [m1_big t _ (by omega)] at e
          have hc : cf C t (1 + t + j) = false := by
            have := Fc.2.1 j hj
            rw [gc_paid _ hA.2] at this
            exact this
          rw [hiv (1 + t + j) (by omega), hc, ← e, show 1 + t + j = t + 1 + j by omega]
          simp [ev, GateOp.eval]
          rfl
        · rw [Fu.2.1 j hj, hB, hev, ev_Rg, hWx, ih y (by omega)]
        · rw [Fu.2.1 j hj, ev_ren]
          apply ev_loc
          intro i hi
          exact ih i (by have := hC.1 j hj i hi; omega)
      · rw [m2_big _ _ _ _ (by omega), Fu.2.2 w (by omega), hV0]
    refine ⟨?_, claim⟩
    have e1 := FW.2.1 (h + 3 + C.gates.length) (by simp [D]; omega)
    rw [gD _ (by omega), FD_g2] at e1
    have e2 := FW.2.1 (h + 2 + C.gates.length) (by simp [D]; omega)
    rw [gD _ (by omega), FD_g1] at e2
    rw [show t + 3 + h + C.gates.length = t + (h + 3 + C.gates.length) by omega, e1]
    cases d
    · simp [ev, GateOp.eval, claim]
    · simp only [ev, GateOp.eval, List.map_cons, List.map_nil, if_true]
      rw [show t + 2 + h + C.gates.length = t + (h + 2 + C.gates.length) by omega, e2]
      simp only [ev, List.map_cons, List.map_nil, claim, hU]
      cases WC C (uu :: List.ofFn z) C.output <;> cases uu <;> decide


theorem main (t : ℕ) (C : Circuit) (hC : Legal (1+t) C) :
    (∃ (a : Bool) (E : Circuit), Legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z))) ∨
    (0 < cost C ∧ ∃ p : (Fin t → Bool) → Bool, ∀ (b d : Bool), ∃ D : Circuit, ∃ π : ℕ → ℕ,
      Legal t D ∧ cost D < cost C ∧ (∀ w, π w < t + D.gates.length) ∧ ∀ z : Fin t → Bool,
        D.eval (List.ofFn z) =
          Bool.xor (C.eval ((Bool.xor (p z) b) :: List.ofFn z)) (d && Bool.xor (p z) b) ∧
        ∀ w, WC D (List.ofFn z) (π w) = WC C ((Bool.xor (p z) b) :: List.ofFn z) w) := by
  classical
  by_cases hex : ∃ j, j < C.gates.length ∧ hit C t j
  · right
    have hs := Nat.find_spec hex
    exact caseB t C hC (Nat.find hex) hs.1 hs.2
      (fun j hj hh => Nat.find_min hex hj ⟨by omega, hh⟩)
  · left
    exact caseA t C hC (fun j hj hh => hex ⟨j, hj, hh⟩)

def b2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2_xor (a b : Bool) : b2 (Bool.xor a b) = b2 a + b2 b := by
  cases a <;> cases b <;> decide

theorem b2_and (a b : Bool) : b2 (a && b) = b2 a * b2 b := by
  cases a <;> cases b <;> decide

theorem b2_not (a : Bool) : b2 (!a) = 1 + b2 a := by cases a <;> decide

theorem b2_dec (v : ZMod 2) : b2 (decide (v = 1)) = v := by revert v; decide

theorem dec_b2 (b : Bool) : decide (b2 b = 1) = b := by cases b <;> decide

theorem eq_dec (b : Bool) (v : ZMod 2) (h : b2 b = v) : b = decide (v = 1) := by
  subst h; exact (dec_b2 b).symm

theorem two_z (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem ofl (l : List Bool) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i false) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem gd_rep (L i : ℕ) : (List.replicate L false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem gd_app_right (l l' : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l').getD i false = l'.getD (i - l.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem gd_one (e M j : ℕ) :
    (List.replicate e false ++ true :: List.replicate M false).getD j false = decide (j = e) := by
  by_cases h1 : j < e
  · rw [gd_app_left _ _ _ (by simpa using h1), gd_rep]
    simp; omega
  · rw [gd_app_right _ _ _ (by simpa using h1)]
    simp only [List.length_replicate]
    by_cases h2 : j = e
    · subst h2; simp
    · obtain ⟨c, hc⟩ : ∃ c, j - e = c + 1 := ⟨j - e - 1, by omega⟩
      rw [hc, List.getD_cons_succ, gd_rep]
      simp [h2]

theorem gd_take (l : List Bool) (n i : ℕ) (h : i < n) : (l.take n).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem gd_drop (l : List Bool) (n i : ℕ) : (l.drop n).getD i false = l.getD (n+i) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

def bits (n : ℕ) (u : Fin n → ZMod 2) : List Bool := List.ofFn (fun j : Fin n => decide (u j = 1))

theorem bits_len (n : ℕ) (u : Fin n → ZMod 2) : (bits n u).length = n := by simp [bits]

theorem gd_bits (n : ℕ) (u : Fin n → ZMod 2) (i : ℕ) (hi : i < n) :
    (bits n u).getD i false = decide (u ⟨i, hi⟩ = 1) := by
  simp [bits, List.getD_eq_getElem?_getD, hi]

def Inv (L m e : ℕ) (C : Circuit) (q : ℕ → ℕ) (τ : List Bool → ZMod 2) : Prop :=
  ∀ xs r : List Bool, xs.length = m → r.length = L →
    b2 (C.eval (xs ++ r)) =
      (∑ i ∈ Finset.range m, b2 (xs.getD i false) * b2 (r.getD (e+i) false)) +
      (∑ i ∈ Finset.range e, b2 (WC C (xs ++ r) (q i)) * b2 (r.getD i false)) + τ r

theorem iter (L : ℕ) (τ : List Bool → ZMod 2) : ∀ (m e : ℕ) (C : Circuit) (q : ℕ → ℕ),
    Legal (m+L) C → (∀ i < e, q i < m + L + C.gates.length) → Inv L m e C q τ → m + e ≤ L →
    ∃ (D : Circuit) (q' : ℕ → ℕ), Legal L D ∧ cost D + m ≤ cost C ∧
      (∀ i < m + e, q' i < L + D.gates.length) ∧ Inv L 0 (m+e) D q' τ := by
  intro m
  induction m with
  | zero =>
    intro e C q hC hq hI _
    rw [Nat.zero_add] at hC
    refine ⟨C, q, hC, by omega, fun i hi => by have := hq i (by omega); omega, ?_⟩
    rw [Nat.zero_add]; exact hI
  | succ m ih =>
    intro e C q hC hq hI hle
    have hC' : Legal (1 + (m+L)) C := by rw [show 1 + (m+L) = m+1+L by omega]; exact hC
    have hIv : ∀ (u : Bool) (r : List Bool), r.length = L →
        b2 (C.eval (u :: (List.replicate m false ++ r))) =
          (∑ i ∈ Finset.range (m+1), b2 ((u :: List.replicate m false).getD i false) *
            b2 (r.getD (e+i) false)) +
          (∑ i ∈ Finset.range e,
            b2 (WC C (u :: (List.replicate m false ++ r)) (q i)) * b2 (r.getD i false)) + τ r := by
      intro u r hr
      have := hI (u :: List.replicate m false) r (by simp) hr
      rwa [List.cons_append] at this
    rcases main (m+L) C hC' with ⟨a, E, -, -, hE⟩ | ⟨_, p, hp⟩
    · exfalso
      have he : e < L := by omega
      have key : ∀ (r : List Bool), r.length = L →
          b2 a = b2 (C.eval (true :: (List.replicate m false ++ r))) +
            b2 (C.eval (false :: (List.replicate m false ++ r))) := by
        intro r hr
        have hl : (List.replicate m false ++ r).length = m + L := by simp; omega
        have e1 := hE true (fun i => (List.replicate m false ++ r).getD i false)
        have e0 := hE false (fun i => (List.replicate m false ++ r).getD i false)
        rw [ofl _ _ hl] at e1 e0
        rw [e1, e0, b2_xor, b2_xor, Bool.and_true, Bool.and_false]
        generalize b2 a = A
        generalize b2 (E.eval (List.replicate m false ++ r)) = B
        have : b2 false = 0 := rfl
        rw [this]
        revert A B; decide
      have k0 := key (List.replicate L false) (by simp)
      have s0 : ∀ u, b2 (C.eval (u :: (List.replicate m false ++ List.replicate L false))) =
          τ (List.replicate L false) := by
        intro u
        rw [hIv u _ (by simp), Finset.sum_eq_zero, Finset.sum_eq_zero]
        · simp
        · intro i _; rw [gd_rep]; simp [b2]
        · intro i _; rw [gd_rep]; simp [b2]
      rw [s0, s0, two_z] at k0
      let r1 := List.replicate e false ++ true :: List.replicate (L - e - 1) false
      have hr1 : r1.length = L := by simp [r1]; omega
      have k1 := key r1 hr1
      have s1 : ∀ u, b2 (C.eval (u :: (List.replicate m false ++ r1))) = b2 u + τ r1 := by
        intro u
        rw [hIv u _ hr1, Finset.sum_range_succ', Finset.sum_eq_zero, Finset.sum_eq_zero (s := Finset.range e)]
        · simp only [r1, gd_one, List.getD_cons_zero, Nat.add_zero]
          simp [b2]
        · intro i hi
          simp only [r1, gd_one]
          simp at hi
          simp [b2, Nat.ne_of_lt hi]
        · intro i _
          simp only [r1, gd_one]
          simp [b2]
      rw [s1, s1, k0] at k1
      generalize τ r1 = T at k1
      revert T k1; decide
    · obtain ⟨D, π, hDl, hDc, hπ, hD⟩ := hp false false
      let q' : ℕ → ℕ := fun i => if i < e then π (q i) else π 0
      have hInv : Inv L m (e+1) D q' τ := by
        intro xs r hxs hr
        have hl : (xs ++ r).length = m + L := by simp; omega
        obtain ⟨hev, hw⟩ := hD (fun i => (xs ++ r).getD i false)
        rw [ofl _ _ hl] at hev hw
        simp only [Bool.xor_false, Bool.false_and] at hev hw
        obtain ⟨u, hu⟩ : ∃ u, u = p (fun i => (xs ++ r).getD i false) := ⟨_, rfl⟩
        rw [← hu] at hev hw
        rw [hev]
        have hI' := hI (u :: xs) r (by simp [hxs]) hr
        rw [List.cons_append] at hI'
        have hq0 : WC D (xs ++ r) (q' e) = u := by
          simp only [q', lt_irrefl, ite_false]; rw [hw 0]
          have := (factsW (1 + (m+L)) C hC'.1 (u :: (xs ++ r)) (by simp; omega)).1 0 (by omega)
          rw [this]; rfl
        have hA : (∑ i ∈ Finset.range (m+1), b2 ((u :: xs).getD i false) * b2 (r.getD (e+i) false)) =
            (∑ i ∈ Finset.range m, b2 (xs.getD i false) * b2 (r.getD (e+1+i) false)) +
              b2 u * b2 (r.getD e false) := by
          rw [Finset.sum_range_succ']
          congr 1
          · apply Finset.sum_congr rfl
            intro i _
            rw [List.getD_cons_succ, show e + (i+1) = e+1+i by omega]
          all_goals simp
        have hB : (∑ i ∈ Finset.range (e+1), b2 (WC D (xs ++ r) (q' i)) * b2 (r.getD i false)) =
            (∑ i ∈ Finset.range e, b2 (WC C (u :: (xs ++ r)) (q i)) * b2 (r.getD i false)) +
              b2 u * b2 (r.getD e false) := by
          rw [Finset.sum_range_succ, hq0]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range] at hi
          simp only [q', if_pos hi]
          rw [hw]
        rw [hI', hA, hB]
        ring
      obtain ⟨D', q'', h1, h2, h3, h4⟩ := ih (e+1) D q' hDl
        (fun i _ => by simp only [q']; split_ifs <;> exact hπ _) hInv (by omega)
      refine ⟨D', q'', h1, by omega, fun i hi => h3 i (by omega), ?_⟩
      rw [show m + 1 + e = m + (e+1) by omega]; exact h4

theorem norm (L : ℕ) (C : Circuit) (hC : Legal L C) :
    ∃ C' : Circuit, Legal L C' ∧ cost C' = cost C ∧ C'.output < L + C'.gates.length ∧
      C.gates.length ≤ C'.gates.length ∧ ∀ x : List Bool, x.length = L →
        C'.eval x = C.eval x ∧ ∀ i < L + C.gates.length, WC C' x i = WC C x i := by
  let G : Gate := if C.output < L + C.gates.length then ⟨.and, [C.output]⟩ else ⟨.or, []⟩
  let F : ℕ → Gate := fun j => if j < C.gates.length then gA C j else G
  have hrb : ∀ k < C.gates.length + 1, ∀ i ∈ (F k).inputs, i < L + k := by
    intro k hk i hi
    simp only [F] at hi
    split_ifs at hi with h1
    · exact hC.1 k h1 i hi
    · have hk : k = C.gates.length := by omega
      subst hk
      simp only [G] at hi
      split_ifs at hi with h2
      · simp at hi; omega
      · simp at hi
  have hops : ∀ k < C.gates.length + 1, (F k).inputs.length ≤ 2 ∧
      ((F k).op = .and ∨ (F k).op = .or ∨ (F k).op = .mod 2 ∨
        ((F k).op = .not ∧ (F k).inputs.length = 1)) := by
    intro k hk
    simp only [F]
    split_ifs with h1
    · exact hC.2 _ (gA_mem C k h1)
    · simp only [G]; split_ifs <;> simp
  refine ⟨mk F (C.gates.length+1) (L+C.gates.length), legal_mk L F _ _ hrb hops, ?_,
    by rw [len_mk]; show L + C.gates.length < L + (C.gates.length + 1); omega,
    by rw [len_mk]; omega, ?_⟩
  · rw [cost_mk, cost_eq, Finset.sum_range_succ]
    have e1 : ∑ k ∈ Finset.range C.gates.length, (if paid (F k) = true then 1 else 0) =
        ∑ k ∈ Finset.range C.gates.length, (if paid (gA C k) = true then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => by simp only [F, if_pos (Finset.mem_range.1 hk)])
    have e2 : paid (F C.gates.length) = false := by
      simp only [F, lt_irrefl, ite_false, G]; split_ifs <;> simp [paid]
    rw [e1, e2]; simp
  · intro x hx
    have FC := factsW L C hC.1 x hx
    have FN := factsW L (mk F (C.gates.length+1) (L+C.gates.length)) (rb_mk L F _ _ hrb) x hx
    have pre : ∀ i < L + C.gates.length,
        WC (mk F (C.gates.length+1) (L+C.gates.length)) x i = WC C x i := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
      intro hi
      by_cases hL : i < L
      · rw [FN.1 i hL, FC.1 i hL]
      · obtain ⟨j, rfl⟩ : ∃ j, i = L + j := ⟨i - L, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [FN.2.1 j (by simp; omega), FC.2.1 j hj, gA_mk F _ _ j (by omega)]
        simp only [F, if_pos hj]
        apply ev_loc
        intro a ha
        have := hC.1 j hj a ha
        exact ih a (by omega) (by omega)
    refine ⟨?_, pre⟩
    show WC (mk F (C.gates.length+1) (L+C.gates.length)) x (L+C.gates.length) = WC C x C.output
    rw [FN.2.1 C.gates.length (by simp), gA_mk F _ _ _ (by omega)]
    by_cases h2 : C.output < L + C.gates.length
    · have hF : F C.gates.length = ⟨.and, [C.output]⟩ := by
        simp only [F, lt_irrefl, ite_false, G, if_pos h2]
      rw [hF]
      simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id]
      exact pre _ h2
    · have hF : F C.gates.length = ⟨.or, []⟩ := by
        simp only [F, lt_irrefl, ite_false, G, if_neg h2]
      rw [hF]
      simp only [ev, GateOp.eval, List.map_nil, List.any_nil]
      rw [FC.2.2 _ (by omega)]

theorem fwd (k t : ℕ) (g : (Fin k → ZMod 2) → (Fin t → ZMod 2) → ZMod 2) (s : ℕ) (C : Circuit)
    (hC : Legal (2*k+t) C) (hc : cost C ≤ s)
    (hs : ∀ (x y : Fin k → ZMod 2) (z : Fin t → ZMod 2),
      C.eval (bits k x ++ bits k y ++ bits t z) = decide (dotProduct x y + g y z = 1)) :
    k ≤ s ∧ ∃ (D : Circuit) (tap : Fin k → ℕ), Legal (k+t) D ∧ cost D ≤ s - k ∧
      D.output < k+t+D.gates.length ∧ (∀ i, tap i < k+t+D.gates.length) ∧
      ∀ (y : Fin k → ZMod 2) (z : Fin t → ZMod 2),
        g y z = b2 (D.eval (bits k y ++ bits t z)) +
          dotProduct (fun i => b2 (WC D (bits k y ++ bits t z) (tap i))) y := by
  let τ : List Bool → ZMod 2 := fun r =>
    g (fun i : Fin k => b2 (r.getD i false)) (fun j : Fin t => b2 (r.getD (k + j) false))
  have hC' : Legal (k + (k+t)) C := by rw [show k + (k+t) = 2*k+t by omega]; exact hC
  have hI : Inv (k+t) k 0 C (fun _ => 0) τ := by
    intro xs r hxs hr
    have ex : bits k (fun i => b2 (xs.getD i false)) = xs := by
      unfold bits; simp only [dec_b2]; exact ofl xs k hxs
    have er : bits k (fun i : Fin k => b2 (r.getD i false)) ++
        bits t (fun j : Fin t => b2 (r.getD (k + j) false)) = r := by
      unfold bits; simp only [dec_b2]
      conv_rhs => rw [← List.take_append_drop k r]
      congr 1
      · rw [← ofl (r.take k) k (by simp; omega)]
        congr 1; funext j; rw [gd_take _ _ _ j.2]
      · rw [← ofl (r.drop k) t (by simp; omega)]
        congr 1; funext j; rw [gd_drop]
    have := hs (fun i => b2 (xs.getD i false)) (fun i : Fin k => b2 (r.getD i false))
      (fun j : Fin t => b2 (r.getD (k + j) false))
    rw [List.append_assoc, ex, er] at this
    rw [this, b2_dec]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.zero_add, τ]
    congr 1
    unfold dotProduct
    exact Fin.sum_univ_eq_sum_range (fun i => b2 (xs.getD i false) * b2 (r.getD i false)) k
  obtain ⟨D, q', hDl, hcost, hq', hInv⟩ := iter (k+t) τ k 0 C (fun _ => 0) hC'
    (fun i hi => absurd hi (by omega)) hI (by omega)
  obtain ⟨D', hD'l, hD'c, hout, hlen, hev⟩ := norm (k+t) D hDl
  refine ⟨by omega, D', fun i => q' i, hD'l, by omega, hout,
    fun i => by show q' i < k+t+D'.gates.length; have := hq' i (by omega); omega, ?_⟩
  intro y z
  have hlinp : (bits k y ++ bits t z).length = k + t := by simp [bits_len]
  obtain ⟨he1, he2⟩ := hev _ hlinp
  have hy : ∀ i : Fin k, b2 ((bits k y ++ bits t z).getD i false) = y i := by
    intro i
    rw [gd_app_left _ _ _ (by rw [bits_len]; exact i.2), gd_bits _ _ _ i.2, b2_dec]
  have hz : ∀ j : Fin t, b2 ((bits k y ++ bits t z).getD (k + j) false) = z j := by
    intro j
    rw [gd_app_right _ _ _ (by rw [bits_len]; omega), bits_len,
      show k + (j : ℕ) - k = j by omega, gd_bits _ _ _ j.2, b2_dec]
  have hτ : τ (bits k y ++ bits t z) = g y z := by
    simp only [τ]
    congr 1
    · funext i; exact hy i
    · funext j; exact hz j
  have hm := hInv [] (bits k y ++ bits t z) rfl hlinp
  simp only [List.nil_append, Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero] at hm
  rw [hτ] at hm
  rw [he1]
  have hS : dotProduct (fun i : Fin k => b2 (WC D' (bits k y ++ bits t z) (q' i))) y =
      ∑ i ∈ Finset.range k, b2 (WC D (bits k y ++ bits t z) (q' i)) *
        b2 ((bits k y ++ bits t z).getD i false) := by
    unfold dotProduct
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => b2 (WC D (bits k y ++ bits t z) (q' i)) * b2 ((bits k y ++ bits t z).getD i false)) k]
    apply Finset.sum_congr rfl
    intro i _
    beta_reduce
    rw [he2 _ (by have := hq' i i.2; omega), hy i]
  rw [hS, hm]
  generalize g y z = G
  generalize (∑ i ∈ Finset.range k, b2 (WC D (bits k y ++ bits t z) (q' i)) *
        b2 ((bits k y ++ bits t z).getD i false)) = S
  revert G S; decide

def accW (N nD o i : ℕ) : ℕ := if i = 0 then o else N + nD + 5 * i - 1

def blk (N nD o : ℕ) (tp : ℕ → ℕ) (k i r : ℕ) : Gate :=
  if r = 0 then ⟨.mod 2, [i, tp i + k]⟩
  else if r = 1 then ⟨.not, [N + nD + 5*i + 0]⟩
  else if r = 2 then ⟨.and, [N + nD + 5*i + 1, k + i]⟩
  else if r = 3 then ⟨.mod 2, [accW N nD o i, N + nD + 5*i + 2]⟩
  else ⟨.not, [N + nD + 5*i + 3]⟩

def FR (D : Circuit) (k t : ℕ) (tp : ℕ → ℕ) (j : ℕ) : Gate :=
  if j < D.gates.length then ren (fun a => a + k) (gA D j)
  else blk (2*k+t) D.gates.length (D.output + k) tp k ((j - D.gates.length) / 5)
    ((j - D.gates.length) % 5)

theorem FR_D (D : Circuit) (k t : ℕ) (tp : ℕ → ℕ) (j : ℕ) (hj : j < D.gates.length) :
    FR D k t tp j = ren (fun a => a + k) (gA D j) := by
  unfold FR; rw [if_pos hj]

theorem FR_blk (D : Circuit) (k t : ℕ) (tp : ℕ → ℕ) (i r : ℕ) (hr : r < 5) :
    FR D k t tp (D.gates.length + (5*i + r)) =
      blk (2*k+t) D.gates.length (D.output + k) tp k i r := by
  unfold FR
  rw [if_neg (by omega), show (D.gates.length + (5*i + r) - D.gates.length) / 5 = i by omega,
    show (D.gates.length + (5*i + r) - D.gates.length) % 5 = r by omega]

theorem ev_m2 (a b : ℕ) (V : ℕ → Bool) : ev ⟨.mod 2, [a, b]⟩ V = !(Bool.xor (V a) (V b)) := by
  simp only [ev, GateOp.eval, List.map_cons, List.map_nil]
  cases V a <;> cases V b <;> rfl

theorem ev_nt (a : ℕ) (V : ℕ → Bool) : ev ⟨.not, [a]⟩ V = !(V a) := by
  simp [ev, GateOp.eval]

theorem ev_an (a b : ℕ) (V : ℕ → Bool) : ev ⟨.and, [a, b]⟩ V = (V a && V b) := by
  simp [ev, GateOp.eval]

theorem bwd (k t : ℕ) (g : (Fin k → ZMod 2) → (Fin t → ZMod 2) → ZMod 2) (s : ℕ) (D : Circuit)
    (tap : Fin k → ℕ) (hks : k ≤ s) (hD : Legal (k+t) D) (hc : cost D ≤ s - k)
    (hout : D.output < k+t+D.gates.length) (htap : ∀ i, tap i < k+t+D.gates.length)
    (hg : ∀ (y : Fin k → ZMod 2) (z : Fin t → ZMod 2),
        g y z = b2 (D.eval (bits k y ++ bits t z)) +
          dotProduct (fun i => b2 (WC D (bits k y ++ bits t z) (tap i))) y) :
    ∃ C : Circuit, Legal (2*k+t) C ∧ cost C ≤ s ∧
      ∀ (x y : Fin k → ZMod 2) (z : Fin t → ZMod 2),
        C.eval (bits k x ++ bits k y ++ bits t z) = decide (dotProduct x y + g y z = 1) := by
  let tp : ℕ → ℕ := fun i => if h : i < k then tap ⟨i, h⟩ else 0
  have htpe : ∀ i (hi : i < k), tp i = tap ⟨i, hi⟩ := by
    intro i hi; simp only [tp, dif_pos hi]
  have htp : ∀ i < k, tp i < k + t + D.gates.length := by
    intro i hi; rw [htpe i hi]; exact htap _
  have hdec : ∀ j < D.gates.length + 5*k, j < D.gates.length ∨
      ∃ i r, i < k ∧ r < 5 ∧ j = D.gates.length + (5*i + r) := by
    intro j hj
    by_cases h : j < D.gates.length
    · exact Or.inl h
    · exact Or.inr ⟨(j - D.gates.length)/5, (j - D.gates.length) % 5, by omega, by omega, by omega⟩
  have hrb : ∀ j < D.gates.length + 5*k, ∀ a ∈ (FR D k t tp j).inputs, a < 2*k+t + j := by
    intro j hj a ha
    rcases hdec j hj with h | ⟨i, r, hi, hr, rfl⟩
    · rw [FR_D _ _ _ _ _ h] at ha
      simp only [ren, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have := hD.1 j h b hb
      omega
    · rw [FR_blk _ _ _ _ _ _ hr] at ha
      have := htp i hi
      unfold blk at ha
      split_ifs at ha with h0 h1 h2 h3
      · simp at ha; rcases ha with rfl | rfl <;> omega
      · simp at ha; omega
      · simp at ha; rcases ha with rfl | rfl <;> omega
      · simp at ha
        rcases ha with rfl | rfl
        · unfold accW; split_ifs <;> omega
        · omega
      · simp at ha; omega
  have hops : ∀ j < D.gates.length + 5*k, (FR D k t tp j).inputs.length ≤ 2 ∧
      ((FR D k t tp j).op = .and ∨ (FR D k t tp j).op = .or ∨ (FR D k t tp j).op = .mod 2 ∨
        ((FR D k t tp j).op = .not ∧ (FR D k t tp j).inputs.length = 1)) := by
    intro j hj
    rcases hdec j hj with h | ⟨i, r, hi, hr, rfl⟩
    · rw [FR_D _ _ _ _ _ h]; exact legal_ren (k+t) D hD _ j h
    · rw [FR_blk _ _ _ _ _ _ hr]; unfold blk; split_ifs <;> simp
  let C := mk (FR D k t tp) (D.gates.length + 5*k) (accW (2*k+t) D.gates.length (D.output + k) k)
  have hCl : Legal (2*k+t) C := legal_mk _ _ _ _ hrb hops
  refine ⟨C, hCl, ?_, ?_⟩
  · rw [cost_mk, Finset.sum_range_add]
    have e1 : ∑ j ∈ Finset.range D.gates.length, (if paid (FR D k t tp j) = true then 1 else 0) =
        cost D := by
      rw [cost_eq]; apply Finset.sum_congr rfl; intro j hj
      rw [FR_D _ _ _ _ _ (Finset.mem_range.1 hj), paid_ren]
    have e2 : ∀ i ≤ k, ∑ j ∈ Finset.range (5*i),
        (if paid (FR D k t tp (D.gates.length + j)) = true then 1 else 0) = i := by
      intro i
      induction i with
      | zero => intro; simp
      | succ i ih =>
        intro hi
        rw [show 5*(i+1) = 5*i + 5 by ring, Finset.sum_range_add, ih (by omega)]
        have : ∀ r ∈ Finset.range 5,
            (if paid (FR D k t tp (D.gates.length + (5*i + r))) = true then 1 else 0) =
              (if r = 2 then 1 else 0) := by
          intro r hr
          have hr' : r < 5 := Finset.mem_range.1 hr
          rw [FR_blk _ _ _ _ _ _ hr']
          unfold blk
          interval_cases r <;> simp [paid]
        rw [Finset.sum_congr rfl this]
        simp [Finset.sum_range_succ]
    rw [e1, e2 k le_rfl]; omega
  · intro x y z
    rw [List.append_assoc]
    obtain ⟨inpD, hinpD⟩ : ∃ l, l = bits k y ++ bits t z := ⟨_, rfl⟩
    rw [← hinpD]
    have hlD : inpD.length = k + t := by rw [hinpD]; simp [bits_len]
    have hl : (bits k x ++ inpD).length = 2*k+t := by simp [bits_len, hlD]; omega
    have FN := factsW (2*k+t) C (rb_mk _ _ _ _ hrb) (bits k x ++ inpD) hl
    have FDD := factsW (k+t) D hD.1 inpD hlD
    have c1 : ∀ w < k + t + D.gates.length, WC C (bits k x ++ inpD) (w + k) = WC D inpD w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      intro hw
      by_cases hL : w < k + t
      · rw [FN.1 (w+k) (by omega), FDD.1 w hL, gd_app_right _ _ _ (by rw [bits_len]; omega),
          bits_len, Nat.add_sub_cancel]
      · obtain ⟨j, rfl⟩ : ∃ j, w = k + t + j := ⟨w - (k+t), by omega⟩
        have hj : j < D.gates.length := by omega
        rw [show k + t + j + k = 2*k+t + j by omega, FN.2.1 j (by simp [C]; omega),
          gA_mk _ _ _ j (by omega), FR_D _ _ _ _ _ hj, ev_ren, FDD.2.1 j hj]
        apply ev_loc
        intro a ha
        have := hD.1 j hj a ha
        exact ih a (by omega) (by omega)
    have hX : ∀ i (hi : i < k), WC C (bits k x ++ inpD) i = decide (x ⟨i, hi⟩ = 1) := by
      intro i hi
      rw [FN.1 i (by omega), gd_app_left _ _ _ (by rw [bits_len]; exact hi), gd_bits _ _ _ hi]
    have hY : ∀ i (hi : i < k), WC C (bits k x ++ inpD) (k + i) = decide (y ⟨i, hi⟩ = 1) := by
      intro i hi
      rw [FN.1 (k+i) (by omega), gd_app_right _ _ _ (by rw [bits_len]; omega), bits_len,
        show k + i - k = i by omega, hinpD, gd_app_left _ _ _ (by rw [bits_len]; exact hi),
        gd_bits _ _ _ hi]
    have gv : ∀ i < k, ∀ r < 5, WC C (bits k x ++ inpD) (2*k+t + D.gates.length + 5*i + r) =
        ev (blk (2*k+t) D.gates.length (D.output + k) tp k i r) (WC C (bits k x ++ inpD)) := by
      intro i hi r hr
      rw [show 2*k+t + D.gates.length + 5*i + r = 2*k+t + (D.gates.length + (5*i + r)) by omega,
        FN.2.1 _ (by simp [C]; omega), gA_mk _ _ _ _ (by omega), FR_blk _ _ _ _ _ _ hr]
    have step : ∀ i (hi : i < k),
        b2 (WC C (bits k x ++ inpD) (accW (2*k+t) D.gates.length (D.output + k) (i+1))) =
          b2 (WC C (bits k x ++ inpD) (accW (2*k+t) D.gates.length (D.output + k) i)) +
            (x ⟨i, hi⟩ + b2 (WC D inpD (tap ⟨i, hi⟩))) * y ⟨i, hi⟩ := by
      intro i hi
      have ea : accW (2*k+t) D.gates.length (D.output + k) (i+1) =
          2*k+t + D.gates.length + 5*i + 4 := by
        unfold accW; rw [if_neg (by omega)]; omega
      have b4 : blk (2*k+t) D.gates.length (D.output + k) tp k i 4 =
          ⟨.not, [2*k+t + D.gates.length + 5*i + 3]⟩ := rfl
      have b3 : blk (2*k+t) D.gates.length (D.output + k) tp k i 3 =
          ⟨.mod 2, [accW (2*k+t) D.gates.length (D.output + k) i,
            2*k+t + D.gates.length + 5*i + 2]⟩ := rfl
      have b2' : blk (2*k+t) D.gates.length (D.output + k) tp k i 2 =
          ⟨.and, [2*k+t + D.gates.length + 5*i + 1, k + i]⟩ := rfl
      have b1 : blk (2*k+t) D.gates.length (D.output + k) tp k i 1 =
          ⟨.not, [2*k+t + D.gates.length + 5*i + 0]⟩ := rfl
      have b0 : blk (2*k+t) D.gates.length (D.output + k) tp k i 0 =
          ⟨.mod 2, [i, tp i + k]⟩ := rfl
      rw [ea, gv i hi 4 (by norm_num), b4, ev_nt, gv i hi 3 (by norm_num), b3, ev_m2,
        gv i hi 2 (by norm_num), b2', ev_an, gv i hi 1 (by norm_num), b1, ev_nt,
        gv i hi 0 (by norm_num), b0, ev_m2, hX i hi, hY i hi, c1 _ (htp i hi), htpe i hi]
      simp only [Bool.not_not, b2_xor, b2_and, b2_dec]
    have acc : ∀ i ≤ k,
        b2 (WC C (bits k x ++ inpD) (accW (2*k+t) D.gates.length (D.output + k) i)) =
          b2 (D.eval inpD) + ∑ j ∈ Finset.range i,
            (if h : j < k then (x ⟨j, h⟩ + b2 (WC D inpD (tap ⟨j, h⟩))) * y ⟨j, h⟩ else 0) := by
      intro i
      induction i with
      | zero =>
        intro _
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        unfold accW; rw [if_pos rfl, c1 _ hout]; rfl
      | succ i ih =>
        intro hi
        rw [step i (by omega), ih (by omega), Finset.sum_range_succ, dif_pos (by omega : i < k)]
        ring
    apply eq_dec
    have hfin := acc k le_rfl
    show b2 (WC C (bits k x ++ inpD) (accW (2*k+t) D.gates.length (D.output + k) k)) = _
    rw [hfin]
    have hgy := hg y z
    rw [← hinpD] at hgy
    rw [hgy]
    have hsum : ∑ j ∈ Finset.range k,
        (if h : j < k then (x ⟨j, h⟩ + b2 (WC D inpD (tap ⟨j, h⟩))) * y ⟨j, h⟩ else 0) =
          dotProduct x y + dotProduct (fun i => b2 (WC D inpD (tap i))) y := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => if h : j < k then (x ⟨j, h⟩ + b2 (WC D inpD (tap ⟨j, h⟩))) * y ⟨j, h⟩ else 0) k]
      unfold dotProduct
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      beta_reduce
      rw [dif_pos j.2]
      simp only [Fin.eta]
      ring
    rw [hsum]
    ring

end PEqualNP.Outside.L_meta_29763

open PEqualNP.Outside.L_meta_29763 in
theorem PEqualNP.Outside.L_meta_29763 : ∀ (k t : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let Z := Fin t → F
  let fits := fun (g : V → Z → F) (s : ℕ) =>
    ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
      ∀ (x y : V) (z : Z), C.eval (bits k x ++ bits k y ++ bits t z) =
        decide (dotProduct x y + g y z = 1)
  ∀ (g : V → Z → F) (s : ℕ), fits g s ↔
    k ≤ s ∧ ∃ (D : Circ) (tap : Fin k → ℕ), legal (k+t) D ∧ cost D ≤ s-k ∧
      D.output < k+t+D.size ∧ (∀ i, tap i < k+t+D.size) ∧
      ∀ (y : V) (z : Z),
        let inp := bits k y ++ bits t z
        let p := fun i : Fin k => if (D.wires inp).getD (tap i) false then (1 : F) else 0
        g y z = (if D.eval inp then 1 else 0) + dotProduct p y := by
  intro k t Circ F legal cost bits V Z fits g s
  constructor
  · intro h
    obtain ⟨C, hC, hc, hs⟩ := h
    exact fwd k t g s C hC hc hs
  · intro h
    obtain ⟨hks, D, tap, hD, hc, hout, htap, hg⟩ := h
    exact bwd k t g s D tap hks hD hc hout htap hg
