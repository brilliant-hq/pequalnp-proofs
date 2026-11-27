import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27136_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def pm3_0 (y : Fin 8 → Bool) : Bool :=
  (y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) || (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)

lemma pm3_cons_false (y : Fin 8 → Bool) : pm3 (Fin.cons false y) = pm3_0 y := by
  have h0 : (Fin.cons false y : Fin 9 → Bool) 0 = false := by simp
  have h1 : (Fin.cons false y : Fin 9 → Bool) 1 = y 0 := by rw [show (1 : Fin 9) = Fin.succ 0 from rfl, Fin.cons_succ]
  have h2 : (Fin.cons false y : Fin 9 → Bool) 2 = y 1 := by rw [show (2 : Fin 9) = Fin.succ 1 from rfl, Fin.cons_succ]
  have h3 : (Fin.cons false y : Fin 9 → Bool) 3 = y 2 := by rw [show (3 : Fin 9) = Fin.succ 2 from rfl, Fin.cons_succ]
  have h4 : (Fin.cons false y : Fin 9 → Bool) 4 = y 3 := by rw [show (4 : Fin 9) = Fin.succ 3 from rfl, Fin.cons_succ]
  have h5 : (Fin.cons false y : Fin 9 → Bool) 5 = y 4 := by rw [show (5 : Fin 9) = Fin.succ 4 from rfl, Fin.cons_succ]
  have h6 : (Fin.cons false y : Fin 9 → Bool) 6 = y 5 := by rw [show (6 : Fin 9) = Fin.succ 5 from rfl, Fin.cons_succ]
  have h7 : (Fin.cons false y : Fin 9 → Bool) 7 = y 6 := by rw [show (7 : Fin 9) = Fin.succ 6 from rfl, Fin.cons_succ]
  have h8 : (Fin.cons false y : Fin 9 → Bool) 8 = y 7 := by rw [show (8 : Fin 9) = Fin.succ 7 from rfl, Fin.cons_succ]
  simp only [pm3, pm3_0, h0, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.false_or]

def m0 (i : Fin 8) : Bool := i == 0 || i == 2 || i == 7
def m1 (i : Fin 8) : Bool := i == 0 || i == 4 || i == 5
def m2 (i : Fin 8) : Bool := i == 1 || i == 2 || i == 6
def m3 (i : Fin 8) : Bool := i == 1 || i == 3 || i == 5

lemma pm3_0_masks : pm3_0 m0 = true ∧ pm3_0 m1 = true ∧ pm3_0 m2 = true ∧ pm3_0 m3 = true := by
  decide

lemma pm3_0_essential (i : Fin 8) : ∃ y z : Fin 8 → Bool, (∀ k : Fin 8, k ≠ i → y k = z k) ∧ pm3_0 y ≠ pm3_0 z := by
  fin_cases i
  · exact ⟨fun k => k == 2 || k == 7, fun k => k == 0 || k == 2 || k == 7,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 2 || k == 6, fun k => k == 1 || k == 2 || k == 6,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 0 || k == 7, fun k => k == 0 || k == 2 || k == 7,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 1 || k == 5, fun k => k == 1 || k == 3 || k == 5,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 0 || k == 5, fun k => k == 0 || k == 4 || k == 5,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 0 || k == 4, fun k => k == 0 || k == 4 || k == 5,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 1 || k == 2, fun k => k == 1 || k == 2 || k == 6,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩
  · exact ⟨fun k => k == 0 || k == 2, fun k => k == 0 || k == 2 || k == 7,
      fun k hk => by fin_cases k <;> simp_all, by decide⟩

lemma pm3_0_sub_m0 (y : Fin 8 → Bool) (hy : ∀ i, y i = true → m0 i = true)
    (hne : ∃ i, m0 i = true ∧ y i = false) : pm3_0 y = false := by
  have h1 : y 1 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 1 h; simp [m0] at this)
  have h4 : y 4 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 4 h; simp [m0] at this)
  have h3 : y 3 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 3 h; simp [m0] at this)
  have h5 : y 5 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 5 h; simp [m0] at this)
  have h6 : y 6 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 6 h; simp [m0] at this)
  simp only [pm3_0, h1, h4, h3, h5, h6, Bool.false_and, Bool.and_false, Bool.or_false]
  rcases hne with ⟨i, hi, hyi⟩
  fin_cases i <;> simp_all [m0]

lemma pm3_0_sub_m1 (y : Fin 8 → Bool) (hy : ∀ i, y i = true → m1 i = true)
    (hne : ∃ i, m1 i = true ∧ y i = false) : pm3_0 y = false := by
  have h1 : y 1 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 1 h; simp [m1] at this)
  have h2 : y 2 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 2 h; simp [m1] at this)
  have h3 : y 3 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 3 h; simp [m1] at this)
  have h6 : y 6 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 6 h; simp [m1] at this)
  have h7 : y 7 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 7 h; simp [m1] at this)
  simp only [pm3_0, h1, h2, h3, h6, h7, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  rcases hne with ⟨i, hi, hyi⟩
  fin_cases i <;> simp_all [m1]

lemma pm3_0_sub_m2 (y : Fin 8 → Bool) (hy : ∀ i, y i = true → m2 i = true)
    (hne : ∃ i, m2 i = true ∧ y i = false) : pm3_0 y = false := by
  have h0 : y 0 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 0 h; simp [m2] at this)
  have h3 : y 3 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 3 h; simp [m2] at this)
  have h4 : y 4 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 4 h; simp [m2] at this)
  have h5 : y 5 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 5 h; simp [m2] at this)
  have h7 : y 7 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 7 h; simp [m2] at this)
  simp only [pm3_0, h0, h3, h4, h5, h7, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  rcases hne with ⟨i, hi, hyi⟩
  fin_cases i <;> simp_all [m2]

lemma pm3_0_sub_m3 (y : Fin 8 → Bool) (hy : ∀ i, y i = true → m3 i = true)
    (hne : ∃ i, m3 i = true ∧ y i = false) : pm3_0 y = false := by
  have h0 : y 0 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 0 h; simp [m3] at this)
  have h2 : y 2 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 2 h; simp [m3] at this)
  have h4 : y 4 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 4 h; simp [m3] at this)
  have h6 : y 6 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 6 h; simp [m3] at this)
  have h7 : y 7 = false := Bool.eq_false_iff.mpr (fun h => by have := hy 7 h; simp [m3] at this)
  simp only [pm3_0, h0, h2, h4, h6, h7, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  rcases hne with ⟨i, hi, hyi⟩
  fin_cases i <;> simp_all [m3]

lemma pm3_0_m0_or_m3 (y : Fin 8 → Bool) (hy4 : y 4 = false) (hy6 : y 6 = false)
    (h : pm3_0 y = true) : (y 0 = true ∧ y 2 = true ∧ y 7 = true) ∨ (y 1 = true ∧ y 3 = true ∧ y 5 = true) := by
  simp only [pm3_0, hy4, hy6, Bool.false_and, Bool.and_false, Bool.or_false] at h
  simpa [and_assoc] using h

lemma pm3_0_m1_or_m2 (y : Fin 8 → Bool) (hy3 : y 3 = false) (hy7 : y 7 = false)
    (h : pm3_0 y = true) : (y 0 = true ∧ y 4 = true ∧ y 5 = true) ∨ (y 1 = true ∧ y 2 = true ∧ y 6 = true) := by
  simp only [pm3_0, hy3, hy7, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or] at h
  simpa [and_assoc] using h

lemma and_cut_imp (p : Fin 8 → Bool) (ht : ∃ i, p i = true) (hf : ∃ i, p i = false)
    (h03 : pm3_0 (fun i => if p i then m0 i else m3 i) = true)
    (h30 : pm3_0 (fun i => if p i then m3 i else m0 i) = true)
    (h12 : pm3_0 (fun i => if p i then m1 i else m2 i) = true)
    (h21 : pm3_0 (fun i => if p i then m2 i else m1 i) = true) : False := by
  have a03 := pm3_0_m0_or_m3 _ (by simp [m0, m3]) (by simp [m0, m3]) h03
  have a30 := pm3_0_m0_or_m3 _ (by simp [m0, m3]) (by simp [m0, m3]) h30
  have a12 := pm3_0_m1_or_m2 _ (by simp [m1, m2]) (by simp [m1, m2]) h12
  have a21 := pm3_0_m1_or_m2 _ (by simp [m1, m2]) (by simp [m1, m2]) h21
  simp only [m0, m1, m2, m3] at a03 a30 a12 a21
  have h_eq : p 0 = p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 0 = p 4 ∧ p 0 = p 5 ∧ p 0 = p 6 ∧ p 0 = p 7 := by
    cases hp0 : p 0 <;> simp_all
  rcases ht with ⟨i, hi⟩
  rcases hf with ⟨j, hj⟩
  fin_cases i <;> fin_cases j <;> simp_all

lemma or_cut_imp (p : Fin 8 → Bool) (ht : ∃ i, p i = true) (hf : ∃ i, p i = false)
    (hm0 : (∀ i, m0 i = true → p i = true) ∨ (∀ i, m0 i = true → p i = false))
    (hm1 : (∀ i, m1 i = true → p i = true) ∨ (∀ i, m1 i = true → p i = false))
    (hm2 : (∀ i, m2 i = true → p i = true) ∨ (∀ i, m2 i = true → p i = false))
    (hm3 : (∀ i, m3 i = true → p i = true) ∨ (∀ i, m3 i = true → p i = false)) : False := by
  rcases hm0 with h0 | h0
  · have hp0 : p 0 = true := h0 0 (by simp [m0])
    have hp2 : p 2 = true := h0 2 (by simp [m0])
    have hp7 : p 7 = true := h0 7 (by simp [m0])
    have h1 : ∀ i, m1 i = true → p i = true := by
      rcases hm1 with h | h; exact h
      exfalso; have := h 0 (by simp [m1]); simp [hp0] at this
    have hp4 : p 4 = true := h1 4 (by simp [m1])
    have hp5 : p 5 = true := h1 5 (by simp [m1])
    have h2 : ∀ i, m2 i = true → p i = true := by
      rcases hm2 with h | h; exact h
      exfalso; have := h 2 (by simp [m2]); simp [hp2] at this
    have hp1 : p 1 = true := h2 1 (by simp [m2])
    have hp6 : p 6 = true := h2 6 (by simp [m2])
    have h3 : ∀ i, m3 i = true → p i = true := by
      rcases hm3 with h | h; exact h
      exfalso; have := h 1 (by simp [m3]); simp [hp1] at this
    have hp3 : p 3 = true := h3 3 (by simp [m3])
    rcases hf with ⟨j, hj⟩
    fin_cases j <;> simp_all
  · have hp0 : p 0 = false := h0 0 (by simp [m0])
    have hp2 : p 2 = false := h0 2 (by simp [m0])
    have hp7 : p 7 = false := h0 7 (by simp [m0])
    have h1 : ∀ i, m1 i = true → p i = false := by
      rcases hm1 with h | h
      exfalso; have := h 0 (by simp [m1]); simp [hp0] at this
      exact h
    have hp4 : p 4 = false := h1 4 (by simp [m1])
    have hp5 : p 5 = false := h1 5 (by simp [m1])
    have h2 : ∀ i, m2 i = true → p i = false := by
      rcases hm2 with h | h
      exfalso; have := h 2 (by simp [m2]); simp [hp2] at this
      exact h
    have hp1 : p 1 = false := h2 1 (by simp [m2])
    have hp6 : p 6 = false := h2 6 (by simp [m2])
    have h3 : ∀ i, m3 i = true → p i = false := by
      rcases hm3 with h | h
      exfalso; have := h 1 (by simp [m3]); simp [hp1] at this
      exact h
    have hp3 : p 3 = false := h3 3 (by simp [m3])
    rcases ht with ⟨i, hi⟩
    fin_cases i <;> simp_all

inductive BTree where
  | var : Fin 8 → BTree
  | node : Bool → BTree → BTree → BTree

def BTree.eval : BTree → (Fin 8 → Bool) → Bool
  | .var i, y => y i
  | .node op l r, y => bif op then (l.eval y || r.eval y) else (l.eval y && r.eval y)

def BTree.vars : BTree → List (Fin 8)
  | .var i => [i]
  | .node _ l r => l.vars ++ r.vars

lemma BTree.vars_nonempty (t : BTree) : ∃ i, i ∈ t.vars := by
  induction t with
  | var i => exact ⟨i, by simp [BTree.vars]⟩
  | node _ l _ ihl _ =>
    obtain ⟨i, hi⟩ := ihl
    exact ⟨i, List.mem_append_left _ hi⟩

lemma BTree.eval_eq_of_agree (t : BTree) (y z : Fin 8 → Bool) (h : ∀ i ∈ t.vars, y i = z i) :
    t.eval y = t.eval z := by
  induction t with
  | var i => exact h i (by simp [BTree.vars])
  | node op l r ihl ihr =>
    simp only [BTree.eval]
    rw [ihl (fun i hi => h i (List.mem_append_left _ hi)),
        ihr (fun i hi => h i (List.mem_append_right _ hi))]

lemma no_read_once_pm3_0 (t : BTree) (hnodup : t.vars.Nodup) (heval : ∀ y, t.eval y = pm3_0 y) : False := by
  cases t with
  | var i =>
    have h1 := heval (fun k => decide (k = i))
    have hpm : pm3_0 (fun k => decide (k = i)) = false := by
      fin_cases i <;> decide
    simp [BTree.eval, hpm] at h1
  | node op l r =>
    simp only [BTree.vars, List.nodup_append] at hnodup
    obtain ⟨il, hil⟩ := l.vars_nonempty
    obtain ⟨ir, hir⟩ := r.vars_nonempty
    let p : Fin 8 → Bool := fun i => decide (i ∈ l.vars)
    have hpt : ∃ i, p i = true := ⟨il, by simp [p, hil]⟩
    have hpf : ∃ i, p i = false := ⟨ir, by
      simp only [p, decide_eq_false_iff_not]
      intro h
      exact hnodup.2.2 ir h ir hir rfl⟩
    have hagree_L : ∀ m n : Fin 8 → Bool, l.eval (fun i => if p i then m i else n i) = l.eval m := by
      intro m n
      apply l.eval_eq_of_agree
      intro i hi
      simp [p, hi]
    have hagree_R : ∀ m n : Fin 8 → Bool, r.eval (fun i => if p i then m i else n i) = r.eval n := by
      intro m n
      apply r.eval_eq_of_agree
      intro i hi
      have hnl : i ∉ l.vars := fun h => hnodup.2.2 i h i hi rfl
      simp [p, hnl]
    cases op
    · have hpair : ∀ m n : Fin 8 → Bool, pm3_0 m = true → pm3_0 n = true →
          pm3_0 (fun i => if p i then m i else n i) = true := by
        intro m n hm hn
        have htm := (heval m).trans hm
        have htn := (heval n).trans hn
        simp only [BTree.eval, Bool.cond_false, Bool.and_eq_true] at htm htn
        rw [← heval]
        simp only [BTree.eval, Bool.cond_false, hagree_L, hagree_R, htm.1, htn.2, Bool.and_self]
      have hm := pm3_0_masks
      exact and_cut_imp p hpt hpf
        (hpair m0 m3 hm.1 hm.2.2.2) (hpair m3 m0 hm.2.2.2 hm.1)
        (hpair m1 m2 hm.2.1 hm.2.2.1) (hpair m2 m1 hm.2.2.1 hm.2.1)
    · have hsub : ∀ m : Fin 8 → Bool, pm3_0 m = true →
          (∀ y, (∀ i, y i = true → m i = true) → (∃ i, m i = true ∧ y i = false) → pm3_0 y = false) →
          (∀ i, m i = true → p i = true) ∨ (∀ i, m i = true → p i = false) := by
        intro m hm hmin
        by_contra hbad
        have h1 : ∃ i, m i = true ∧ p i = false := by
          by_contra hno
          apply hbad
          left
          intro i hi
          cases hp : p i
          · exfalso; exact hno ⟨i, hi, hp⟩
          · rfl
        have h2 : ∃ i, m i = true ∧ p i = true := by
          by_contra hno
          apply hbad
          right
          intro i hi
          cases hp : p i
          · rfl
          · exfalso; exact hno ⟨i, hi, hp⟩
        let yL : Fin 8 → Bool := fun i => p i && m i
        let yR : Fin 8 → Bool := fun i => !p i && m i
        have hyL_f : pm3_0 yL = false := hmin yL
          (fun i hi => by simp only [yL, Bool.and_eq_true] at hi; exact hi.2)
          (by rcases h1 with ⟨i, hi, hpi⟩; exact ⟨i, hi, by simp [yL, hpi]⟩)
        have hyR_f : pm3_0 yR = false := hmin yR
          (fun i hi => by simp only [yR, Bool.and_eq_true] at hi; exact hi.2)
          (by rcases h2 with ⟨i, hi, hpi⟩; exact ⟨i, hi, by simp [yR, hpi]⟩)
        have hl_f : l.eval m = false := by
          have htl := (heval yL).trans hyL_f
          simp only [BTree.eval, Bool.cond_true, Bool.or_eq_false_iff] at htl
          rw [← htl.1]
          apply l.eval_eq_of_agree
          intro i hi
          simp [yL, p, hi]
        have hr_f : r.eval m = false := by
          have htr := (heval yR).trans hyR_f
          simp only [BTree.eval, Bool.cond_true, Bool.or_eq_false_iff] at htr
          rw [← htr.2]
          apply r.eval_eq_of_agree
          intro i hi
          have hnl : i ∉ l.vars := fun h => hnodup.2.2 i h i hi rfl
          simp [yR, p, hnl]
        have htm := heval m
        simp only [BTree.eval, Bool.cond_true, hl_f, hr_f, Bool.or_false] at htm
        rw [hm] at htm
        exact Bool.false_ne_true htm
      have hm := pm3_0_masks
      exact or_cut_imp p hpt hpf
        (hsub m0 hm.1 pm3_0_sub_m0)
        (hsub m1 hm.2.1 pm3_0_sub_m1)
        (hsub m2 hm.2.2.1 pm3_0_sub_m2)
        (hsub m3 hm.2.2.2 pm3_0_sub_m3)

lemma nodup_of_toFinset_card_eq {α : Type*} [DecidableEq α] (l : List α)
    (h : l.toFinset.card = l.length) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.toFinset_cons, List.length_cons] at h
    by_cases ha : a ∈ t
    · have : insert a t.toFinset = t.toFinset := Finset.insert_eq_of_mem (List.mem_toFinset.mpr ha)
      rw [this] at h
      have := List.toFinset_card_le t
      omega
    · have ha' : a ∉ t.toFinset := by simpa using ha
      rw [Finset.card_insert_of_notMem ha'] at h
      exact List.nodup_cons.mpr ⟨ha, ih (by omega)⟩

lemma eq_of_mem_flatMap_nodup {α β : Type*} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hfm : (l.flatMap f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    {v : β} (hva : v ∈ f a) (hvb : v ∈ f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hfm
    rcases List.nodup_cons.mp hl with ⟨hx, hxs⟩
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exfalso; exact hfm.2.2 v hva v (List.mem_flatMap.mpr ⟨b, hb', hvb⟩) rfl
    · exfalso; exact hfm.2.2 v hvb v (List.mem_flatMap.mpr ⟨a, ha', hva⟩) rfl
    · exact ih hxs hfm.2.1 ha' hb'

lemma foldl_wires_take_succ (gates : List Gate) (x0 : List Bool) (k : Nat) (hk : k < gates.length) :
    (gates.take (k + 1)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x0 =
    let prev := (gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x0
    let g := gates.get ⟨k, hk⟩
    prev ++ [g.op.eval (g.inputs.map fun i => prev.getD i false)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

lemma foldl_wires_length (gates : List Gate) (x0 : List Bool) :
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x0).length =
    x0.length + gates.length := by
  induction gates generalizing x0 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_take (gates : List Gate) (x0 : List Bool) (k : Nat) (hk : k ≤ gates.length)
    (w : Nat) (hw : w < x0.length + k) :
    (gates.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) x0).getD w false =
    ((gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) x0).getD w false := by
  have htake : gates = gates.take k ++ gates.drop k := (List.take_append_drop k gates).symm
  conv_lhs => rw [htake, List.foldl_append]
  have hlen : ((gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) x0).length = x0.length + k := by
    rw [foldl_wires_length, List.length_take_of_le hk]
  have hgen : ∀ (ds : List Gate) (acc : List Bool), w < acc.length →
      (ds.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) acc).getD w false =
      acc.getD w false := by
    intro ds
    induction ds with
    | nil => intro acc _; rfl
    | cons d ds ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      rw [ih _ (by simp; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hacc]
  exact hgen (gates.drop k) _ (by rw [hlen]; exact hw)

def upd {α : Type*} (f : Nat → α) (idx : Nat) (val : α) : Nat → α :=
  fun w => if w = idx then val else f w

def stepNotVal (k : Nat) (ra : Bool ⊕ Nat) : (Bool ⊕ Nat) × Bool :=
  match ra with
  | .inl b => (.inl (!b), false)
  | .inr _ => (.inr (8 + k), true)

def stepAndVal (k : Nat) : Bool ⊕ Nat → Bool ⊕ Nat → (Bool ⊕ Nat) × Bool
  | .inl false, _ => (.inl false, false)
  | .inl true, rb => (rb, false)
  | .inr _, .inl false => (.inl false, false)
  | .inr wa, .inl true => (.inr wa, false)
  | .inr wa, .inr wb => if wa = wb then (.inr wa, false) else (.inr (8 + k), true)

def stepOrVal (k : Nat) : Bool ⊕ Nat → Bool ⊕ Nat → (Bool ⊕ Nat) × Bool
  | .inl true, _ => (.inl true, false)
  | .inl false, rb => (rb, false)
  | .inr _, .inl true => (.inl true, false)
  | .inr wa, .inl false => (.inr wa, false)
  | .inr wa, .inr wb => if wa = wb then (.inr wa, false) else (.inr (8 + k), true)

def stepBinVal (isOr : Bool) (k : Nat) (ra rb : Bool ⊕ Nat) : (Bool ⊕ Nat) × Bool :=
  if isOr then stepOrVal k ra rb else stepAndVal k ra rb

def gateStepOut (k : Nat) (c : Nat → Bool ⊕ Nat) (g : Gate) : (Bool ⊕ Nat) × Bool :=
  match g.op, g.inputs with
  | .not, [a] => stepNotVal k (c a)
  | .and, [a, b] => stepBinVal false k (c a) (c b)
  | .or, [a, b] => stepBinVal true k (c a) (c b)
  | _, _ => (c (9 + k), false)

def stepCanon (N : Nat) (gates : List Gate) (k : Nat)
    (st : (Nat → Bool ⊕ Nat) × Finset (Fin N)) : (Nat → Bool ⊕ Nat) × Finset (Fin N) :=
  if hk : k < N then
    if hlen : k < gates.length then
      let res := gateStepOut k st.1 (gates.get ⟨k, hlen⟩)
      (upd st.1 (9 + k) res.1, if res.2 then insert ⟨k, hk⟩ st.2 else st.2)
    else st
  else st

def canonRec (N : Nat) (gates : List Gate) : Nat → (Nat → Bool ⊕ Nat) × Finset (Fin N)
  | 0 => (fun w => if w = 0 then .inl false else .inr (w - 1), ∅)
  | k + 1 => stepCanon N gates k (canonRec N gates k)

lemma stepCanon_other (N : Nat) (gates : List Gate) (k : Nat)
    (st : (Nat → Bool ⊕ Nat) × Finset (Fin N)) (w : Nat) (hw : w ≠ 9 + k) :
    (stepCanon N gates k st).1 w = st.1 w := by
  dsimp only [stepCanon]
  split_ifs <;> simp [upd, hw]

lemma stepCanon_surv_mono (N : Nat) (gates : List Gate) (k : Nat)
    (st : (Nat → Bool ⊕ Nat) × Finset (Fin N)) :
    st.2 ⊆ (stepCanon N gates k st).2 := by
  dsimp only [stepCanon]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl
  · exact Finset.Subset.rfl
  · exact Finset.Subset.rfl

lemma stepCanon_surv_mem (N : Nat) (gates : List Gate) (k : Nat)
    (st : (Nat → Bool ⊕ Nat) × Finset (Fin N)) {j : Fin N}
    (hj : j ∈ (stepCanon N gates k st).2) : j ∈ st.2 ∨ j.val = k := by
  simp only [stepCanon] at hj
  split_ifs at hj with hk hlen h2
  · rcases Finset.mem_insert.mp hj with rfl | h
    · right; rfl
    · left; exact h
  · left; exact hj
  · left; exact hj
  · left; exact hj

def evalW (N : Nat) (S : Finset (Fin N)) (isUnary gateOp : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (y : Fin 8 → Bool) (w : Nat) : Bool :=
  if hw8 : w < 8 then y ⟨w, hw8⟩
  else if hN : w - 8 < N then
    if _ : (⟨w - 8, hN⟩ : Fin N) ∈ S then
      if isUnary ⟨w - 8, hN⟩ then
        if _ : in0 ⟨w - 8, hN⟩ < w then !(evalW N S isUnary gateOp in0 in1 y (in0 ⟨w - 8, hN⟩)) else false
      else
        if _ : in0 ⟨w - 8, hN⟩ < w then
          if _ : in1 ⟨w - 8, hN⟩ < w then
            bif gateOp ⟨w - 8, hN⟩ then
              (evalW N S isUnary gateOp in0 in1 y (in0 ⟨w - 8, hN⟩) || evalW N S isUnary gateOp in0 in1 y (in1 ⟨w - 8, hN⟩))
            else
              (evalW N S isUnary gateOp in0 in1 y (in0 ⟨w - 8, hN⟩) && evalW N S isUnary gateOp in0 in1 y (in1 ⟨w - 8, hN⟩))
          else false
        else false
    else false
  else false
termination_by w

def reachFrom (N : Nat) (S : Finset (Fin N)) (isUnary : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (w : Nat) : Finset (Fin N) :=
  if _ : 8 ≤ w then
    if hN : w - 8 < N then
      if _ : (⟨w - 8, hN⟩ : Fin N) ∈ S then
        if isUnary ⟨w - 8, hN⟩ then
          if _ : in0 ⟨w - 8, hN⟩ < w then
            insert ⟨w - 8, hN⟩ (reachFrom N S isUnary in0 in1 (in0 ⟨w - 8, hN⟩))
          else {⟨w - 8, hN⟩}
        else
          if _ : in0 ⟨w - 8, hN⟩ < w then
            if _ : in1 ⟨w - 8, hN⟩ < w then
              insert ⟨w - 8, hN⟩
                (reachFrom N S isUnary in0 in1 (in0 ⟨w - 8, hN⟩) ∪ reachFrom N S isUnary in0 in1 (in1 ⟨w - 8, hN⟩))
            else {⟨w - 8, hN⟩}
          else {⟨w - 8, hN⟩}
      else ∅
    else ∅
  else ∅
termination_by w

lemma reachFrom_subset (N : Nat) (S : Finset (Fin N)) (isUnary : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (w : Nat) :
    reachFrom N S isUnary in0 in1 w ⊆ S := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [reachFrom]
    by_cases h1 : 8 ≤ w
    · by_cases h2 : w - 8 < N
      · by_cases h3 : (⟨w - 8, h2⟩ : Fin N) ∈ S
        · by_cases h4 : isUnary ⟨w - 8, h2⟩ = true
          · by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
              exact Finset.insert_subset_iff.mpr ⟨h3, ih _ h5⟩
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
              exact Finset.singleton_subset_iff.mpr h3
          · have h4f : isUnary ⟨w - 8, h2⟩ = false := Bool.eq_false_iff.mpr h4
            by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · by_cases h6 : in1 ⟨w - 8, h2⟩ < w
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte]
                exact Finset.insert_subset_iff.mpr ⟨h3, Finset.union_subset (ih _ h5) (ih _ h6)⟩
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte]
                exact Finset.singleton_subset_iff.mpr h3
            · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, ↓reduceDIte, ↓reduceIte]
              exact Finset.singleton_subset_iff.mpr h3
        · simp only [h1, h2, h3, ↓reduceDIte, Finset.empty_subset]
      · simp only [h1, h2, ↓reduceDIte, Finset.empty_subset]
    · simp only [h1, ↓reduceDIte, Finset.empty_subset]

lemma reachFrom_lt (N : Nat) (S : Finset (Fin N)) (isUnary : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (w : Nat) :
    ∀ k ∈ reachFrom N S isUnary in0 in1 w, 8 + k.val ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk
    rw [reachFrom] at hk
    by_cases h1 : 8 ≤ w
    · by_cases h2 : w - 8 < N
      · by_cases h3 : (⟨w - 8, h2⟩ : Fin N) ∈ S
        · by_cases h4 : isUnary ⟨w - 8, h2⟩ = true
          · by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_insert.mp hk with rfl | hk'
              · simp only [Fin.val_mk]; omega
              · exact (ih _ h5 k hk').trans (le_of_lt h5)
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl; simp only [Fin.val_mk]; omega
          · have h4f : isUnary ⟨w - 8, h2⟩ = false := Bool.eq_false_iff.mpr h4
            by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · by_cases h6 : in1 ⟨w - 8, h2⟩ < w
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_insert.mp hk with rfl | hk'
                · simp only [Fin.val_mk]; omega
                · rcases Finset.mem_union.mp hk' with hk1 | hk2
                  · exact (ih _ h5 k hk1).trans (le_of_lt h5)
                  · exact (ih _ h6 k hk2).trans (le_of_lt h6)
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_singleton.mp hk with rfl; simp only [Fin.val_mk]; omega
            · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl; simp only [Fin.val_mk]; omega
        · simp only [h1, h2, h3, ↓reduceDIte] at hk; simp at hk
      · simp only [h1, h2, ↓reduceDIte] at hk; simp at hk
    · simp only [h1, ↓reduceDIte] at hk; simp at hk

lemma evalW_eq_of_agree (N : Nat) (S : Finset (Fin N)) (isUnary gateOp : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (y z : Fin 8 → Bool) (w : Nat)
    (hagree : ∀ k ∈ reachFrom N S isUnary in0 in1 w,
      ∀ v ∈ (if isUnary k then [in0 k] else [in0 k, in1 k]), ∀ hv : v < 8, y ⟨v, hv⟩ = z ⟨v, hv⟩)
    (hw_base : ∀ hv : w < 8, y ⟨w, hv⟩ = z ⟨w, hv⟩) :
    evalW N S isUnary gateOp in0 in1 y w = evalW N S isUnary gateOp in0 in1 z w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 8
    · rw [evalW, evalW]
      simp only [h1, ↓reduceDIte]
      exact hw_base h1
    · by_cases h2 : w - 8 < N
      · by_cases h3 : (⟨w - 8, h2⟩ : Fin N) ∈ S
        · by_cases h4 : isUnary ⟨w - 8, h2⟩ = true
          · by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · have hjR : ⟨w - 8, h2⟩ ∈ reachFrom N S isUnary in0 in1 w := by
                rw [reachFrom]; simp [show 8 ≤ w by omega, h2, h3, h4, h5]
              rw [evalW, evalW]
              simp only [h1, ↓reduceDIte, h2, h3, h4, ↓reduceIte, h5]
              congr 1
              refine ih _ h5 ?_ ?_
              · intro k hk v hv hvb
                apply hagree k _ v hv hvb
                rw [reachFrom]; simp [show 8 ≤ w by omega, h2, h3, h4, h5, hk]
              · intro hv
                exact hagree ⟨w - 8, h2⟩ hjR (in0 ⟨w - 8, h2⟩) (by simp [h4]) hv
            · rw [evalW, evalW]
              simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
          · have h4f : isUnary ⟨w - 8, h2⟩ = false := Bool.eq_false_iff.mpr h4
            by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · by_cases h6 : in1 ⟨w - 8, h2⟩ < w
              · have hjR : ⟨w - 8, h2⟩ ∈ reachFrom N S isUnary in0 in1 w := by
                  rw [reachFrom]; simp [show 8 ≤ w by omega, h2, h3, h4f, h5, h6]
                rw [evalW, evalW]
                simp only [h1, ↓reduceDIte, h2, h3, h4f, Bool.false_eq_true, ↓reduceIte, h5, h6]
                have hl := ih _ h5 (fun k hk v hv hvb => hagree k (by
                    rw [reachFrom]; simp [show 8 ≤ w by omega, h2, h3, h4f, h5, h6, hk]) v hv hvb)
                  (fun hv => hagree ⟨w - 8, h2⟩ hjR (in0 ⟨w - 8, h2⟩) (by simp [h4f]) hv)
                have hr := ih _ h6 (fun k hk v hv hvb => hagree k (by
                    rw [reachFrom]; simp [show 8 ≤ w by omega, h2, h3, h4f, h5, h6, hk]) v hv hvb)
                  (fun hv => hagree ⟨w - 8, h2⟩ hjR (in1 ⟨w - 8, h2⟩) (by simp [h4f]) hv)
                rw [hl, hr]
              · rw [evalW, evalW]
                simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte]
            · rw [evalW, evalW]
              simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, ↓reduceDIte, ↓reduceIte]
        · rw [evalW, evalW]
          simp only [h1, h2, h3, ↓reduceDIte]
      · rw [evalW, evalW]
        simp only [h1, h2, ↓reduceDIte]

lemma parent_in_reachFrom (N : Nat) (S : Finset (Fin N)) (isUnary : Fin N → Bool)
    (in0 in1 : Fin N → Nat)
    (hin_lt : ∀ j ∈ S, in0 j < 8 + j.val ∧ (isUnary j = false → in1 j < 8 + j.val))
    (w : Nat) (k : Fin N) (hk : k ∈ reachFrom N S isUnary in0 in1 w) (hne : 8 + k.val ≠ w) :
    ∃ p ∈ reachFrom N S isUnary in0 in1 w,
      8 + k.val ∈ (if isUnary p then [in0 p] else [in0 p, in1 p]) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [reachFrom] at hk
    by_cases h1 : 8 ≤ w
    · by_cases h2 : w - 8 < N
      · by_cases h3 : (⟨w - 8, h2⟩ : Fin N) ∈ S
        · by_cases h4 : isUnary ⟨w - 8, h2⟩ = true
          · by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_insert.mp hk with rfl | hk'
              · exfalso; apply hne; simp only [Fin.val_mk]; omega
              · by_cases he0 : 8 + k.val = in0 ⟨w - 8, h2⟩
                · refine ⟨⟨w - 8, h2⟩, ?_, by simp [h4, he0]⟩
                  rw [reachFrom]; simp [h1, h2, h3, h4, h5]
                · obtain ⟨p, hp, hmem⟩ := ih _ h5 hk' he0
                  refine ⟨p, ?_, hmem⟩
                  rw [reachFrom]; simp [h1, h2, h3, h4, h5, hp]
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl
              exfalso; apply hne; simp only [Fin.val_mk]; omega
          · have h4f : isUnary ⟨w - 8, h2⟩ = false := Bool.eq_false_iff.mpr h4
            by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · by_cases h6 : in1 ⟨w - 8, h2⟩ < w
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_insert.mp hk with rfl | hk'
                · exfalso; apply hne; simp only [Fin.val_mk]; omega
                · rcases Finset.mem_union.mp hk' with hk1 | hk2
                  · by_cases he0 : 8 + k.val = in0 ⟨w - 8, h2⟩
                    · refine ⟨⟨w - 8, h2⟩, ?_, by simp [h4f, he0]⟩
                      rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6]
                    · obtain ⟨p, hp, hmem⟩ := ih _ h5 hk1 he0
                      refine ⟨p, ?_, hmem⟩
                      rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6, hp]
                  · by_cases he1 : 8 + k.val = in1 ⟨w - 8, h2⟩
                    · refine ⟨⟨w - 8, h2⟩, ?_, by simp [h4f, he1]⟩
                      rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6]
                    · obtain ⟨p, hp, hmem⟩ := ih _ h6 hk2 he1
                      refine ⟨p, ?_, hmem⟩
                      rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6, hp]
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_singleton.mp hk with rfl
                exfalso; apply hne; simp only [Fin.val_mk]; omega
            · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl
              exfalso; apply hne; simp only [Fin.val_mk]; omega
        · simp only [h1, h2, h3, ↓reduceDIte] at hk; simp at hk
      · simp only [h1, h2, ↓reduceDIte] at hk; simp at hk
    · simp only [h1, ↓reduceDIte] at hk; simp at hk

lemma reachFrom_sub_self (N : Nat) (S : Finset (Fin N)) (isUnary : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (w : Nat) (k : Fin N) (hk : k ∈ reachFrom N S isUnary in0 in1 w) :
    reachFrom N S isUnary in0 in1 (8 + k.val) ⊆ reachFrom N S isUnary in0 in1 w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [reachFrom] at hk
    by_cases h1 : 8 ≤ w
    · by_cases h2 : w - 8 < N
      · by_cases h3 : (⟨w - 8, h2⟩ : Fin N) ∈ S
        · by_cases h4 : isUnary ⟨w - 8, h2⟩ = true
          · by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_insert.mp hk with rfl | hk'
              · have heq : 8 + (⟨w - 8, h2⟩ : Fin N).val = w := by simp only [Fin.val_mk]; omega
                rw [heq]
              · exact (ih _ h5 hk').trans (by
                  intro x hx; rw [reachFrom]; simp [h1, h2, h3, h4, h5, hx])
            · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl
              have heq : 8 + (⟨w - 8, h2⟩ : Fin N).val = w := by simp only [Fin.val_mk]; omega
              rw [heq]
          · have h4f : isUnary ⟨w - 8, h2⟩ = false := Bool.eq_false_iff.mpr h4
            by_cases h5 : in0 ⟨w - 8, h2⟩ < w
            · by_cases h6 : in1 ⟨w - 8, h2⟩ < w
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_insert.mp hk with rfl | hk'
                · have heq : 8 + (⟨w - 8, h2⟩ : Fin N).val = w := by simp only [Fin.val_mk]; omega
                  rw [heq]
                · rcases Finset.mem_union.mp hk' with hk1 | hk2
                  · exact (ih _ h5 hk1).trans (by
                      intro x hx; rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6, hx])
                  · exact (ih _ h6 hk2).trans (by
                      intro x hx; rw [reachFrom]; simp [h1, h2, h3, h4f, h5, h6, hx])
              · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, h6, ↓reduceDIte, ↓reduceIte] at hk
                rcases Finset.mem_singleton.mp hk with rfl
                have heq : 8 + (⟨w - 8, h2⟩ : Fin N).val = w := by simp only [Fin.val_mk]; omega
                rw [heq]
            · simp only [h1, h2, h3, h4f, Bool.false_eq_true, h5, ↓reduceDIte, ↓reduceIte] at hk
              rcases Finset.mem_singleton.mp hk with rfl
              have heq : 8 + (⟨w - 8, h2⟩ : Fin N).val = w := by simp only [Fin.val_mk]; omega
              rw [heq]
        · simp only [h1, h2, h3, ↓reduceDIte] at hk; simp at hk
      · simp only [h1, h2, ↓reduceDIte] at hk; simp at hk
    · simp only [h1, ↓reduceDIte] at hk; simp at hk

def buildTree (N : Nat) (S : Finset (Fin N)) (gateOp : Fin N → Bool)
    (in0 in1 : Fin N → Nat) (w : Nat) : BTree :=
  if hw8 : w < 8 then BTree.var ⟨w, hw8⟩
  else if hN : w - 8 < N then
    if _ : (⟨w - 8, hN⟩ : Fin N) ∈ S then
      if _ : in0 ⟨w - 8, hN⟩ < w then
        if _ : in1 ⟨w - 8, hN⟩ < w then
          BTree.node (gateOp ⟨w - 8, hN⟩) (buildTree N S gateOp in0 in1 (in0 ⟨w - 8, hN⟩)) (buildTree N S gateOp in0 in1 (in1 ⟨w - 8, hN⟩))
        else BTree.var 0
      else BTree.var 0
    else BTree.var 0
  else BTree.var 0
termination_by w

theorem main_aux (C : Circuit)
    (_hfan : FanInTwo C)
    (hsize : C.size ≤ 11)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x)
    (hout : C.output + 1 = 9 + C.size)
    (hform : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (_hnontriv : ∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hg0 : C.gates.head? = some ⟨GateOp.and, [0, 1]⟩)
    (hg1 : C.gates.tail.head? = some ⟨GateOp.and, [0, 3]⟩) : False := by
  have hgs_eq : ∃ gs, C.gates = ⟨GateOp.and, [0, 1]⟩ :: ⟨GateOp.and, [0, 3]⟩ :: gs := by
    cases h : C.gates with
    | nil => simp [h] at hg0
    | cons a as =>
      cases as with
      | nil => simp [h] at hg1
      | cons b bs =>
        simp only [h, List.head?_cons, List.tail_cons, Option.some.injEq] at hg0 hg1
        exact ⟨bs, by rw [hg0, hg1]⟩
  rcases hgs_eq with ⟨gs, hgs⟩
  let N := C.gates.length
  have hN_len : C.gates.length = N := rfl
  have hN_le : N ≤ 11 := hsize
  have hN_ge2 : 2 ≤ N := by rw [← hN_len, hgs]; simp
  have hg0_eq : C.gates.get ⟨0, by omega⟩ = ⟨GateOp.and, [0, 1]⟩ := by simp [hgs]
  have hg1_eq : C.gates.get ⟨1, by omega⟩ = ⟨GateOp.and, [0, 3]⟩ := by simp [hgs]
  have hN_ge3 : 3 ≤ N := by
    by_contra hlt
    have hgs_nil : gs = [] := by
      cases gs with
      | nil => rfl
      | cons _ _ => exfalso; simp [← hN_len, hgs] at hlt
    have hout10 : C.output = 10 := by
      have : C.size = N := rfl
      omega
    have hev := heval (fun i => i == 2 || i == 4 || i == 6)
    have hpm : pm3 (fun i => i == 2 || i == 4 || i == 6) = true := by decide
    have hc : C.eval (List.ofFn (fun i : Fin 9 => i == 2 || i == 4 || i == 6)) = false := by
      simp [Circuit.eval, Circuit.wires, hgs, hgs_nil, hout10, GateOp.eval]
    rw [hpm, hc] at hev
    exact Bool.false_ne_true hev
  have hstable : ∀ k₁ k₂ w, k₁ ≤ k₂ → w < 9 + k₁ →
      (canonRec N C.gates k₂).1 w = (canonRec N C.gates k₁).1 w := by
    intro k₁ k₂ w hle hw
    induction k₂ with
    | zero =>
      have : k₁ = 0 := by omega
      subst this; rfl
    | succ k₂ ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · rfl
      · rw [canonRec, stepCanon_other _ _ _ _ _ (by omega)]
        exact ih (by omega)
  have hsurv_iff : ∀ k (hk : k ≤ N) (j : Fin N), j.val < k →
      (j ∈ (canonRec N C.gates k).2 ↔ j ∈ (canonRec N C.gates N).2) := by
    intro k hk j hjk
    have hmono : ∀ k₁ k₂, k₁ ≤ k₂ → j ∈ (canonRec N C.gates k₁).2 → j ∈ (canonRec N C.gates k₂).2 := by
      intro k₁ k₂ hle hm
      induction k₂ with
      | zero =>
        obtain rfl : k₁ = 0 := by omega
        exact hm
      | succ k₂ ih =>
        rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · exact hm
        · rw [canonRec]; exact stepCanon_surv_mono _ _ _ _ (ih (by omega))
    have hback : ∀ k₁ k₂, k₁ ≤ k₂ → j.val < k₁ →
        j ∈ (canonRec N C.gates k₂).2 → j ∈ (canonRec N C.gates k₁).2 := by
      intro k₁ k₂ hle hlt1 hm
      induction k₂ with
      | zero =>
        obtain rfl : k₁ = 0 := by omega
        exact hm
      | succ k₂ ih =>
        rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · exact hm
        · apply ih (by omega)
          rw [canonRec] at hm
          rcases stepCanon_surv_mem _ _ _ _ hm with h | heq
          · exact h
          · exfalso; omega
    exact ⟨hmono k N hk, hback k N hk hjk⟩
  have hcanon_bound : ∀ k (hk : k ≤ N) w (hw : w < 9 + k),
      match (canonRec N C.gates k).1 w with
      | .inl _ => True
      | .inr wc => wc < 8 + k ∧
          (8 ≤ wc → ∃ h : wc - 8 < N, (⟨wc - 8, h⟩ : Fin N) ∈ (canonRec N C.gates k).2 ∧ wc - 8 < k) := by
    intro k hk
    induction k with
    | zero =>
      intro w hw
      simp only [canonRec]
      by_cases hw0 : w = 0
      · subst hw0; simp
      · simp only [hw0, ↓reduceIte]
        exact ⟨by omega, fun h8 => by exfalso; omega⟩
    | succ k ih =>
      intro w hw
      have ihk := ih (by omega)
      by_cases hwk : w < 9 + k
      · rw [canonRec, stepCanon_other _ _ _ _ _ (by omega)]
        have hb := ihk w hwk
        cases hc : (canonRec N C.gates k).1 w with
        | inl b => simp
        | inr wc =>
          rw [hc] at hb
          refine ⟨by omega, fun h8 => ?_⟩
          obtain ⟨hN', hm, hlt⟩ := hb.2 h8
          exact ⟨hN', stepCanon_surv_mono _ _ _ _ hm, by omega⟩
      · have hw_eq : w = 9 + k := by omega
        subst hw_eq
        let j : Fin N := ⟨k, by omega⟩
        simp only [canonRec, stepCanon, show k < N by omega, show k < C.gates.length by exact j.isLt,
          ↓reduceDIte, upd, ↓reduceIte]
        rcases hform j with ⟨hop, a, ha, hinp⟩ | ⟨hop, a, b, hab, hb, hinp⟩
        · have ha' : a < 9 + k := ha
          have hba := ihk a ha'
          have hj_eq : C.gates.get ⟨k, j.isLt⟩ = C.gates.get j := rfl
          simp only [gateStepOut, hj_eq, hop, hinp, stepNotVal]
          cases hca : (canonRec N C.gates k).1 a with
          | inl b => trivial
          | inr wa =>
            rw [hca] at hba
            simp only [Finset.mem_insert, ↓reduceIte]
            exact ⟨by omega, fun _ => ⟨by omega, by simpa [j] using Or.inl rfl, by omega⟩⟩
        · have hb' : b < 9 + k := hb
          have ha' : a < 9 + k := by omega
          have hba := ihk a ha'
          have hbb := ihk b hb'
          have hj_eq : C.gates.get ⟨k, j.isLt⟩ = C.gates.get j := rfl
          have hstepBin : ∀ (isOr : Bool),
              match (stepBinVal isOr k ((canonRec N C.gates k).1 a) ((canonRec N C.gates k).1 b)).1 with
              | .inl _ => True
              | .inr wc => wc < 8 + (k + 1) ∧
                  (8 ≤ wc → ∃ h : wc - 8 < N,
                    (⟨wc - 8, h⟩ : Fin N) ∈ (if (stepBinVal isOr k ((canonRec N C.gates k).1 a) ((canonRec N C.gates k).1 b)).2
                      then insert j (canonRec N C.gates k).2 else (canonRec N C.gates k).2) ∧ wc - 8 < k + 1) := by
            intro isOr
            cases hca : (canonRec N C.gates k).1 a with
            | inl ba =>
              cases hcb : (canonRec N C.gates k).1 b with
              | inl bb =>
                cases isOr <;> cases ba <;> cases bb <;> dsimp only [stepBinVal, stepAndVal, stepOrVal] <;> trivial
              | inr wb =>
                rw [hcb] at hbb
                cases isOr <;> cases ba <;> dsimp only [stepBinVal, stepAndVal, stepOrVal]
                · trivial
                · refine ⟨by omega, fun h8 => ?_⟩
                  obtain ⟨hN', hm, hlt⟩ := hbb.2 h8
                  exact ⟨hN', hm, by omega⟩
                · refine ⟨by omega, fun h8 => ?_⟩
                  obtain ⟨hN', hm, hlt⟩ := hbb.2 h8
                  exact ⟨hN', hm, by omega⟩
                · trivial
            | inr wa =>
              rw [hca] at hba
              cases hcb : (canonRec N C.gates k).1 b with
              | inl bb =>
                cases isOr <;> cases bb <;> dsimp only [stepBinVal, stepAndVal, stepOrVal]
                · trivial
                · refine ⟨by omega, fun h8 => ?_⟩
                  obtain ⟨hN', hm, hlt⟩ := hba.2 h8
                  exact ⟨hN', hm, by omega⟩
                · refine ⟨by omega, fun h8 => ?_⟩
                  obtain ⟨hN', hm, hlt⟩ := hba.2 h8
                  exact ⟨hN', hm, by omega⟩
                · trivial
              | inr wb =>
                rw [hcb] at hbb
                by_cases hww : wa = wb
                · rw [hww] at hba
                  cases isOr <;> dsimp only [stepBinVal, stepAndVal, stepOrVal] <;>
                    simp only [hww, ↓reduceIte, Bool.false_eq_true]
                  · refine ⟨by omega, fun h8 => ?_⟩
                    obtain ⟨hN', hm, hlt⟩ := hba.2 h8
                    exact ⟨hN', hm, by omega⟩
                  · refine ⟨by omega, fun h8 => ?_⟩
                    obtain ⟨hN', hm, hlt⟩ := hba.2 h8
                    exact ⟨hN', hm, by omega⟩
                · cases isOr <;> dsimp only [stepBinVal, stepAndVal, stepOrVal] <;>
                    simp only [hww, ↓reduceIte]
                  · exact ⟨by omega, fun _ => ⟨by omega, by simpa [j] using Finset.mem_insert_self j _, by omega⟩⟩
                  · exact ⟨by omega, fun _ => ⟨by omega, by simpa [j] using Finset.mem_insert_self j _, by omega⟩⟩
          rcases hop with hop | hop
          · simp only [gateStepOut, hj_eq, hop, hinp]
            exact hstepBin false
          · simp only [gateStepOut, hj_eq, hop, hinp]
            exact hstepBin true
  let st := canonRec N C.gates N
  let canon := st.1
  let S := st.2
  let isUnary : Fin N → Bool := fun j => match (C.gates.get j).op with | GateOp.not => true | _ => false
  let gateOp : Fin N → Bool := fun j => match (C.gates.get j).op with | GateOp.or => true | _ => false
  let extractW : Nat → Nat := fun a => match canon a with | .inr w => w | .inl _ => 0
  let in0 : Fin N → Nat := fun j => match (C.gates.get j).inputs.head? with | some a => extractW a | none => 0
  let in1 : Fin N → Nat := fun j => match (C.gates.get j).inputs.tail.head? with | some b => extractW b | none => 0
  have hsurv_props : ∀ j ∈ S,
      (isUnary j = true → (C.gates.get j).op = GateOp.not ∧
        ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a] ∧ ∃ wa, canon a = .inr wa ∧ in0 j = wa ∧ wa < 8 + j.val) ∧
      (isUnary j = false → ((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b] ∧
          ∃ wa wb, canon a = .inr wa ∧ canon b = .inr wb ∧ wa ≠ wb ∧
            in0 j = wa ∧ in1 j = wb ∧ wa < 8 + j.val ∧ wb < 8 + j.val) := by
    intro j hj
    have hj1 : j ∈ (canonRec N C.gates (j.val + 1)).2 := (hsurv_iff (j.val + 1) (by omega) j (by omega)).mpr hj
    have hnotj : j ∉ (canonRec N C.gates j.val).2 := by
      intro hbad
      have hb : ∀ k (x : Fin N), x ∈ (canonRec N C.gates k).2 → x.val < k := by
        intro k
        induction k with
        | zero => intro x hx; simp [canonRec] at hx
        | succ k ih =>
          intro x hx
          rw [canonRec] at hx
          rcases stepCanon_surv_mem _ _ _ _ hx with hx' | heq
          · have := ih x hx'; omega
          · omega
      have := hb j.val j hbad
      omega
    simp only [canonRec, stepCanon, j.isLt, show j.val < C.gates.length from j.isLt, ↓reduceDIte] at hj1
    split_ifs at hj1 with hadd
    · rcases hform j with ⟨hop, a, ha, hinp⟩ | ⟨hop, a, b, hab, hb, hinp⟩
      · constructor
        · intro _
          refine ⟨hop, a, ha, hinp, ?_⟩
          have hst_a : canon a = (canonRec N C.gates j.val).1 a := hstable j.val N a (by omega) ha
          simp only [gateStepOut, show C.gates.get ⟨j.val, j.isLt⟩ = C.gates.get j from rfl,
            hop, hinp, stepNotVal] at hadd
          cases hca : (canonRec N C.gates j.val).1 a with
          | inl b => rw [hca] at hadd; simp only [Bool.false_eq_true] at hadd
          | inr wa =>
            have hbd := hcanon_bound j.val (by omega) a ha
            rw [hca] at hbd
            have hca' : canon a = .inr wa := hst_a.trans hca
            refine ⟨wa, hca', ?_, hbd.1⟩
            dsimp only [in0, extractW]
            rw [hinp, List.head?_cons]
            dsimp only
            rw [hca']
        · intro hu
          dsimp only [isUnary] at hu
          rw [hop] at hu
          simp at hu
      · constructor
        · intro hu
          dsimp only [isUnary] at hu
          rcases hop with hop | hop <;> rw [hop] at hu <;> simp at hu
        · intro _
          refine ⟨hop, a, b, hab, hb, hinp, ?_⟩
          have hst_a : canon a = (canonRec N C.gates j.val).1 a := hstable j.val N a (by omega) (by omega)
          have hst_b : canon b = (canonRec N C.gates j.val).1 b := hstable j.val N b (by omega) hb
          have hba := hcanon_bound j.val (by omega) a (by omega)
          have hbb := hcanon_bound j.val (by omega) b hb
          have hinr : ∀ isOr : Bool,
              (stepBinVal isOr j.val ((canonRec N C.gates j.val).1 a) ((canonRec N C.gates j.val).1 b)).2 = true →
              ∃ wa wb, (canonRec N C.gates j.val).1 a = .inr wa ∧
                (canonRec N C.gates j.val).1 b = .inr wb ∧ wa ≠ wb := by
            intro isOr htr
            cases hca : (canonRec N C.gates j.val).1 a with
            | inl ba =>
              cases hcb : (canonRec N C.gates j.val).1 b with
              | inl bb =>
                cases isOr <;> cases ba <;> cases bb <;> simp [stepBinVal, stepAndVal, stepOrVal, hca, hcb] at htr
              | inr wb =>
                cases isOr <;> cases ba <;> simp [stepBinVal, stepAndVal, stepOrVal, hca, hcb] at htr
            | inr wa =>
              cases hcb : (canonRec N C.gates j.val).1 b with
              | inl bb =>
                cases isOr <;> cases bb <;> simp [stepBinVal, stepAndVal, stepOrVal, hca, hcb] at htr
              | inr wb =>
                by_cases hww : wa = wb
                · subst hww; cases isOr <;> simp [stepBinVal, stepAndVal, stepOrVal, hca, hcb] at htr
                · exact ⟨wa, wb, rfl, rfl, hww⟩
          have hex : ∃ wa wb, (canonRec N C.gates j.val).1 a = .inr wa ∧
              (canonRec N C.gates j.val).1 b = .inr wb ∧ wa ≠ wb := by
            have hj_eq : C.gates.get ⟨j.val, j.isLt⟩ = C.gates.get j := rfl
            rcases hop with hop | hop <;> simp only [gateStepOut, hj_eq, hop, hinp] at hadd
            · exact hinr false hadd
            · exact hinr true hadd
          rcases hex with ⟨wa, wb, hca, hcb, hne⟩
          rw [hca] at hba
          rw [hcb] at hbb
          have hca' : canon a = .inr wa := hst_a.trans hca
          have hcb' : canon b = .inr wb := hst_b.trans hcb
          refine ⟨wa, wb, hca', hcb', hne, ?_, ?_, hba.1, hbb.1⟩
          · dsimp only [in0, extractW]
            rw [hinp, List.head?_cons]
            dsimp only
            rw [hca']
          · dsimp only [in1, extractW]
            rw [hinp, List.tail_cons, List.head?_cons]
            dsimp only
            rw [hcb']
    · exfalso; exact hnotj hj1
  have hin_lt : ∀ j ∈ S, in0 j < 8 + j.val ∧ (isUnary j = false → in1 j < 8 + j.val) := by
    intro j hj
    have hp := hsurv_props j hj
    cases hu : isUnary j
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, h0, h1, h0lt, h1lt⟩ := hp.2 hu
      exact ⟨by omega, fun _ => by omega⟩
    · obtain ⟨_, _, _, _, _, h0, h0lt⟩ := hp.1 hu
      exact ⟨by omega, fun hbad => by simp at hbad⟩
  have hin_ne : ∀ j ∈ S, isUnary j = false → in0 j ≠ in1 j := by
    intro j hj hu
    obtain ⟨_, _, _, _, _, _, _, _, _, hne, h0, h1, _, _⟩ := (hsurv_props j hj).2 hu
    omega
  have heval_corr : ∀ (y : Fin 8 → Bool) (k : Nat) (hk : k ≤ N) (w : Nat) (hw : w < 9 + k),
      ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
        (List.ofFn (Fin.cons false y))).getD w false =
      match (canonRec N C.gates k).1 w with
      | .inl b => b
      | .inr wc => evalW N S isUnary gateOp in0 in1 y wc := by
    intro y k hk
    induction k with
    | zero =>
      intro w hw
      simp only [List.take_zero, List.foldl_nil, canonRec]
      by_cases hw0 : w = 0
      · subst hw0
        simp [List.getD_eq_getElem?_getD]
      · have hw8 : w - 1 < 8 := by omega
        have hlt9 : w < 9 := by omega
        simp only [hw0, ↓reduceIte, evalW, hw8, ↓reduceDIte]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt9, ↓reduceDIte, Option.getD_some]
        have heq : (Fin.cons false y : Fin 9 → Bool) ⟨w, hlt9⟩ = y ⟨w - 1, hw8⟩ := by
          obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
          rw [show (⟨w' + 1, hlt9⟩ : Fin 9) = Fin.succ ⟨w', hw8⟩ from Fin.ext rfl, Fin.cons_succ]
          simp
        exact heq
    | succ k ih =>
      intro w hw
      have ihk := ih (by omega)
      by_cases hwk : w < 9 + k
      · rw [canonRec, stepCanon_other _ _ _ _ _ (by omega)]
        rw [foldl_wires_take_succ C.gates _ k (by omega)]
        have hlen : ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
            (List.ofFn (Fin.cons false y))).length = 9 + k := by
          rw [foldl_wires_length, List.length_ofFn, List.length_take_of_le (by omega)]
        have hlt_len : w < ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
            (List.ofFn (Fin.cons false y))).length := by rw [hlen]; exact hwk
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt_len, ← List.getD_eq_getElem?_getD]
        exact ihk w hwk
      · have hw_eq : w = 9 + k := by omega
        subst hw_eq
        let j : Fin N := ⟨k, by omega⟩
        rw [foldl_wires_take_succ C.gates _ k (by omega)]
        have hlen : ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
            (List.ofFn (Fin.cons false y))).length = 9 + k := by
          rw [foldl_wires_length, List.length_ofFn, List.length_take_of_le (by omega)]
        have hle_len : ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
            (List.ofFn (Fin.cons false y))).length ≤ 9 + k := by rw [hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle_len, hlen, Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
        simp only [canonRec, stepCanon, show k < N by omega, show k < C.gates.length by omega, ↓reduceDIte, upd, ↓reduceIte]
        have hgj : C.gates.get ⟨k, j.isLt⟩ = C.gates.get j := rfl
        have hgj' : C.gates.get ⟨k, show k < C.gates.length by omega⟩ = C.gates.get j := rfl
        rcases hform j with ⟨hop, a, ha, hinp⟩ | ⟨hop, a, b, hab, hb, hinp⟩
        · have ha' : a < 9 + k := ha
          have iha := ihk a ha'
          have hev_g : (C.gates.get ⟨k, show k < C.gates.length by omega⟩).op.eval
              ((C.gates.get ⟨k, show k < C.gates.length by omega⟩).inputs.map (fun i =>
                ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                  (List.ofFn (Fin.cons false y))).getD i false)) =
              !(((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                (List.ofFn (Fin.cons false y))).getD a false) := by
            rw [hgj', hop, hinp]; rfl
          rw [hev_g, iha]
          simp only [gateStepOut, hgj', hop, hinp, stepNotVal]
          cases hca : (canonRec N C.gates k).1 a with
          | inl ba => simp
          | inr wa =>
            have hjS : j ∈ S := (hsurv_iff (k + 1) hk j (by simp [j])).mp (by
              simp only [canonRec, stepCanon, show k < N by omega, show k < C.gates.length by omega, ↓reduceDIte,
                gateStepOut, hgj', hop, hinp, stepNotVal, hca, ↓reduceIte]
              exact Finset.mem_insert.mpr (Or.inl rfl))
            have hst_a : canon a = .inr wa := (hstable k N a (by omega) ha').trans hca
            have hin0_eq : in0 j = wa := by
              dsimp only [in0, extractW]
              rw [hinp, List.head?_cons]
              dsimp only
              rw [hst_a]
            have hu_j : isUnary j = true := by
              dsimp only [isUnary]
              rw [hop]
            have hlt_j : in0 j < 8 + k := by
              rw [hin0_eq]; exact (hcanon_bound k (by omega) a ha' |> fun h => by rw [hca] at h; exact h.1)
            dsimp only
            conv_rhs => unfold evalW
            simp only [show ¬ 8 + k < 8 by omega, ↓reduceDIte,
              show 8 + k - 8 < N by omega, show (⟨8 + k - 8, _⟩ : Fin N) = j from Fin.ext (by simp [j]),
              hjS, hu_j, hlt_j, hin0_eq, ↓reduceIte]
            rw [dif_pos (hin0_eq ▸ hlt_j)]
        · have hb' : b < 9 + k := hb
          have ha' : a < 9 + k := by omega
          have iha := ihk a ha'
          have ihb := ihk b hb'
          have hbin : ∀ (isOr : Bool),
              ((C.gates.get j).op = if isOr then GateOp.or else GateOp.and) →
              (if isOr then
                ((match (canonRec N C.gates k).1 a with | .inl b => b | .inr wc => evalW N S isUnary gateOp in0 in1 y wc) ||
                 (match (canonRec N C.gates k).1 b with | .inl b => b | .inr wc => evalW N S isUnary gateOp in0 in1 y wc))
              else
                ((match (canonRec N C.gates k).1 a with | .inl b => b | .inr wc => evalW N S isUnary gateOp in0 in1 y wc) &&
                 (match (canonRec N C.gates k).1 b with | .inl b => b | .inr wc => evalW N S isUnary gateOp in0 in1 y wc))) =
              match (stepBinVal isOr k ((canonRec N C.gates k).1 a) ((canonRec N C.gates k).1 b)).1 with
              | .inl b => b
              | .inr wc => evalW N S isUnary gateOp in0 in1 y wc := by
            intro isOr hop_eq
            cases hca : (canonRec N C.gates k).1 a with
            | inl ba =>
              cases hcb : (canonRec N C.gates k).1 b with
              | inl bb => cases isOr <;> cases ba <;> cases bb <;> simp [stepBinVal, stepAndVal, stepOrVal]
              | inr wb => cases isOr <;> cases ba <;> simp [stepBinVal, stepAndVal, stepOrVal]
            | inr wa =>
              cases hcb : (canonRec N C.gates k).1 b with
              | inl bb => cases isOr <;> cases bb <;> simp [stepBinVal, stepAndVal, stepOrVal]
              | inr wb =>
                by_cases hww : wa = wb
                · subst hww; cases isOr <;> simp [stepBinVal, stepAndVal, stepOrVal]
                · have hjS : j ∈ S := (hsurv_iff (k + 1) hk j (by simp [j])).mp (by
                    cases isOr
                    · simp only [canonRec, stepCanon, show k < N by omega, show k < C.gates.length by omega, ↓reduceDIte,
                        gateStepOut, hgj', hop_eq, hinp, ↓reduceIte, Bool.false_eq_true,
                        stepBinVal, stepAndVal, hca, hcb, hww]
                      exact Finset.mem_insert.mpr (Or.inl rfl)
                    · simp only [canonRec, stepCanon, show k < N by omega, show k < C.gates.length by omega, ↓reduceDIte,
                        gateStepOut, hgj', hop_eq, hinp, ↓reduceIte, eq_self,
                        stepBinVal, stepOrVal, hca, hcb, hww]
                      exact Finset.mem_insert.mpr (Or.inl rfl))
                  have hst_a : canon a = .inr wa := (hstable k N a (by omega) ha').trans hca
                  have hst_b : canon b = .inr wb := (hstable k N b (by omega) hb').trans hcb
                  have hin0_eq : in0 j = wa := by
                    dsimp only [in0, extractW]
                    rw [hinp, List.head?_cons]
                    dsimp only
                    rw [hst_a]
                  have hin1_eq : in1 j = wb := by
                    dsimp only [in1, extractW]
                    rw [hinp, List.tail_cons, List.head?_cons]
                    dsimp only
                    rw [hst_b]
                  have hu_j : isUnary j = false := by
                    dsimp only [isUnary]
                    rw [hop_eq]
                    cases isOr <;> rfl
                  have hgo_j : gateOp j = isOr := by
                    dsimp only [gateOp]
                    rw [hop_eq]
                    cases isOr <;> rfl
                  have hlt0 : in0 j < 8 + k := by
                    rw [hin0_eq]; exact (hcanon_bound k (by omega) a ha' |> fun h => by rw [hca] at h; exact h.1)
                  have hlt1 : in1 j < 8 + k := by
                    rw [hin1_eq]; exact (hcanon_bound k (by omega) b hb' |> fun h => by rw [hcb] at h; exact h.1)
                  have hlt0w : wa < 8 + k := hin0_eq ▸ hlt0
                  have hlt1w : wb < 8 + k := hin1_eq ▸ hlt1
                  cases isOr <;> simp only [stepBinVal, stepAndVal, stepOrVal, hww, ↓reduceIte] <;>
                    (conv_rhs => unfold evalW) <;>
                    simp only [show ¬ 8 + k < 8 by omega, ↓reduceDIte,
                      show 8 + k - 8 < N by omega,
                      show (⟨8 + k - 8, _⟩ : Fin N) = j from Fin.ext (by simp [j]),
                      hjS, hu_j, hgo_j, hin0_eq, hin1_eq, hlt0w, hlt1w,
                      ↓reduceIte, Bool.false_eq_true] <;> rfl
          rcases hop with hop | hop
          · have hev_g : (C.gates.get ⟨k, show k < C.gates.length by omega⟩).op.eval
                ((C.gates.get ⟨k, show k < C.gates.length by omega⟩).inputs.map (fun i =>
                  ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                    (List.ofFn (Fin.cons false y))).getD i false)) =
                (((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                  (List.ofFn (Fin.cons false y))).getD a false &&
                ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                  (List.ofFn (Fin.cons false y))).getD b false) := by
              rw [hgj', hop, hinp]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            rw [hev_g, iha, ihb]
            simp only [gateStepOut, hgj', hop, hinp]
            exact hbin false hop
          · have hev_g : (C.gates.get ⟨k, show k < C.gates.length by omega⟩).op.eval
                ((C.gates.get ⟨k, show k < C.gates.length by omega⟩).inputs.map (fun i =>
                  ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                    (List.ofFn (Fin.cons false y))).getD i false)) =
                (((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                  (List.ofFn (Fin.cons false y))).getD a false ||
                ((C.gates.take k).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
                  (List.ofFn (Fin.cons false y))).getD b false) := by
              rw [hgj', hop, hinp]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            rw [hev_g, iha, ihb]
            simp only [gateStepOut, hgj', hop, hinp]
            exact hbin true hop
  have heval_wire : ∀ (y : Fin 8 → Bool) (w : Nat) (hw : w < 9 + N),
      (C.wires (List.ofFn (Fin.cons false y))).getD w false =
      match canon w with | .inl b => b | .inr wc => evalW N S isUnary gateOp in0 in1 y wc := by
    intro y w hw
    have htake := foldl_wires_getD_take C.gates (List.ofFn (Fin.cons false y)) N (le_refl N) w (by simpa using hw)
    rw [Circuit.wires, htake]
    exact heval_corr y N (le_refl N) w hw
  have hcanon9 : canon 9 = .inl false := by
    rw [show canon = (canonRec N C.gates N).1 from rfl, hstable 1 N 9 (by omega) (by omega)]
    simp [canonRec, stepCanon, show 0 < N by omega, hgs, gateStepOut, stepBinVal, stepAndVal, upd]
  have hcanon10 : canon 10 = .inl false := by
    rw [show canon = (canonRec N C.gates N).1 from rfl, hstable 2 N 10 (by omega) (by omega)]
    simp [canonRec, stepCanon, show 0 < N by omega, show 1 < N by omega, hgs, gateStepOut, stepBinVal, stepAndVal, upd]
  have h0_not_S : (⟨0, by omega⟩ : Fin N) ∉ S := by
    intro hmem
    have hu : isUnary ⟨0, by omega⟩ = false := by
      dsimp only [isUnary]; rw [hg0_eq]
    obtain ⟨_, a, b, _, _, hinp, wa, _, hca, _⟩ := (hsurv_props ⟨0, by omega⟩ hmem).2 hu
    rw [hg0_eq] at hinp
    simp only [List.cons.injEq, and_true] at hinp
    rcases hinp with ⟨rfl, _⟩
    have : canon 0 = .inl false := by
      rw [show canon = (canonRec N C.gates N).1 from rfl, hstable 0 N 0 (Nat.zero_le N) (by omega)]
      simp [canonRec]
    rw [this] at hca
    cases hca
  have h1_not_S : (⟨1, by omega⟩ : Fin N) ∉ S := by
    intro hmem
    have hu : isUnary ⟨1, by omega⟩ = false := by
      dsimp only [isUnary]; rw [hg1_eq]
    obtain ⟨_, a, b, _, _, hinp, wa, _, hca, _⟩ := (hsurv_props ⟨1, by omega⟩ hmem).2 hu
    rw [hg1_eq] at hinp
    simp only [List.cons.injEq, and_true] at hinp
    rcases hinp with ⟨rfl, _⟩
    have : canon 0 = .inl false := by
      rw [show canon = (canonRec N C.gates N).1 from rfl, hstable 0 N 0 (Nat.zero_le N) (by omega)]
      simp [canonRec]
    rw [this] at hca
    cases hca
  have hfalse_not_S : ∀ (k : Fin N) (a : Nat), a ∈ (C.gates.get k).inputs → canon a = .inl false → k ∉ S := by
    intro k a ha_in hca hkS
    cases hu : isUnary k
    · obtain ⟨_, a0, b0, _, _, hinp, wa, wb, ha0, hb0, _⟩ := (hsurv_props k hkS).2 hu
      rw [hinp] at ha_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_in
      rcases ha_in with rfl | rfl <;> simp_all
    · obtain ⟨_, a0, _, hinp, wa, ha0, _⟩ := (hsurv_props k hkS).1 hu
      rw [hinp] at ha_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_in
      subst ha_in
      simp_all
  have hout_val : C.output = 9 + (N - 1) := by
    have : C.size = N := rfl
    omega
  have hout_lt : C.output < 9 + N := by omega
  have hout_inr : ∃ outJ : Fin N, canon C.output = .inr (8 + outJ.val) ∧ outJ ∈ S := by
    cases hco : canon C.output with
    | inl b =>
      exfalso
      have h0 : pm3_0 (fun _ => false) = false := by decide
      have h1 : pm3_0 m0 = true := pm3_0_masks.1
      have hc0 : pm3 (Fin.cons false fun _ => false) = b := by
        rw [← heval]; dsimp only [Circuit.eval]; rw [heval_wire _ C.output hout_lt, hco]
      have hc1 : pm3 (Fin.cons false m0) = b := by
        rw [← heval]; dsimp only [Circuit.eval]; rw [heval_wire _ C.output hout_lt, hco]
      rw [pm3_cons_false] at hc0 hc1
      rw [h0] at hc0; rw [h1] at hc1
      exact Bool.false_ne_true (hc0.trans hc1.symm)
    | inr outW =>
      have hbd := hcanon_bound N (le_refl N) C.output hout_lt
      change match canon C.output with | .inl _ => True | .inr wc => _ at hbd
      rw [hco] at hbd
      by_cases h8 : 8 ≤ outW
      · obtain ⟨hN', hm, _⟩ := hbd.2 h8
        refine ⟨⟨outW - 8, hN'⟩, ?_, hm⟩
        try rw [hco]
        congr 1; simp; omega
      · exfalso
        let i : Fin 8 := ⟨outW, by omega⟩
        have h0 : pm3 (Fin.cons false fun k => decide (k = i)) =
            evalW N S isUnary gateOp in0 in1 (fun k => decide (k = i)) outW := by
          rw [← heval]; dsimp only [Circuit.eval]; rw [heval_wire _ C.output hout_lt, hco]
        rw [pm3_cons_false] at h0
        have hevW : evalW N S isUnary gateOp in0 in1 (fun k => decide (k = i)) outW = decide (i = i) := by
          conv_lhs => unfold evalW
          simp [show outW < 8 by omega, i]
        rw [hevW, decide_eq_true rfl] at h0
        have hpm_all : ∀ k : Fin 8, pm3_0 (fun j => decide (j = k)) = false := by decide
        rw [hpm_all i] at h0
        exact Bool.false_ne_true h0
  rcases hout_inr with ⟨outJ, hout_canon, houtJ_S⟩
  let outW := 8 + outJ.val
  have heval_out : ∀ y : Fin 8 → Bool, evalW N S isUnary gateOp in0 in1 y outW = pm3_0 y := by
    intro y
    have h : C.eval (List.ofFn (Fin.cons false y)) = pm3 (Fin.cons false y) := heval (Fin.cons false y)
    simp only [Circuit.eval] at h
    rw [heval_wire y C.output hout_lt, hout_canon, pm3_cons_false] at h
    dsimp only [outW]
    dsimp only at h
    exact h

  have hS_le7 : S.card ≤ 7 := by
    obtain ⟨k1, hk1_gt, hk1_in⟩ := hlive ⟨0, by rw [hN_len]; omega⟩ (by rw [Fin.val_mk, hN_len]; omega)
    obtain ⟨k2, hk2_gt, hk2_in⟩ := hlive ⟨1, by rw [hN_len]; omega⟩ (by rw [Fin.val_mk, hN_len]; omega)
    simp only [Fin.val_mk] at hk1_gt hk2_gt hk1_in hk2_in
    have hk1_ge2 : 2 ≤ k1.val := by
      by_contra hlt
      have hk1_eq : k1 = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hk1_eq, hg1_eq] at hk1_in
      simp at hk1_in
    have hk1_not_S : k1 ∉ S := hfalse_not_S k1 9 hk1_in hcanon9
    have hk2_not_S : k2 ∉ S := hfalse_not_S k2 10 hk2_in hcanon10
    have h4_notin : ∃ D : Finset (Fin N), D.card = 4 ∧ Disjoint D S := by
      by_cases h12 : k1 = k2
      · subst h12
        have hinp910 : (C.gates.get k1).inputs = [9, 10] := by
          rcases hform k1 with ⟨_, a, _, hinp⟩ | ⟨_, a, b, hab, _, hinp⟩
          · rw [hinp] at hk1_in hk2_in; simp at hk1_in hk2_in; omega
          · rw [hinp] at hk1_in hk2_in; simp at hk1_in hk2_in; rw [hinp]; simp [show a = 9 by omega, show b = 10 by omega]
        have hopk1 : (C.gates.get k1).op = GateOp.and ∨ (C.gates.get k1).op = GateOp.or := by
          rcases hform k1 with ⟨_, a, _, hinp⟩ | ⟨hop, _⟩
          · rw [hinp] at hk1_in hk2_in; simp at hk1_in hk2_in; omega
          · exact hop
        have hck1 : canon (9 + k1.val) = .inl false := by
          rw [show canon = (canonRec N C.gates N).1 from rfl,
            hstable (k1.val + 1) N (9 + k1.val) k1.isLt (by omega)]
          have ha9 : (canonRec N C.gates k1.val).1 9 = .inl false := by
            rw [← hstable k1.val N 9 (Nat.le_of_lt k1.isLt) (by omega)]; exact hcanon9
          have ha10 : (canonRec N C.gates k1.val).1 10 = .inl false := by
            rw [← hstable k1.val N 10 (Nat.le_of_lt k1.isLt) (by omega)]; exact hcanon10
          rw [canonRec, stepCanon, dif_pos k1.isLt, dif_pos (show k1.val < C.gates.length from k1.isLt)]
          dsimp only [gateStepOut]
          rw [show C.gates.get ⟨k1.val, _⟩ = C.gates.get k1 from rfl, hinp910]
          rcases hopk1 with hop | hop <;> (rw [hop]; simp [stepBinVal, stepAndVal, stepOrVal, ha9, ha10, upd])
        have hk1_last : k1.val + 1 < N := by
          by_contra hge
          have hk1_eq : k1.val = N - 1 := by omega
          have h9k1 : 9 + k1.val = C.output := by omega
          have hck1' := hck1
          rw [h9k1, hout_canon] at hck1'
          cases hck1'
        obtain ⟨l, hl_gt, hl_in⟩ := hlive k1 hk1_last
        have hl_not_S : l ∉ S := hfalse_not_S l (9 + k1.val) hl_in hck1
        refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩, k1, l}, ?_, ?_⟩
        · have hn0k : (⟨0, by omega⟩ : Fin N) ∉ ({⟨1, by omega⟩, k1, l} : Finset (Fin N)) := by
            simp [Fin.ext_iff]; omega
          have hn1k : (⟨1, by omega⟩ : Fin N) ∉ ({k1, l} : Finset (Fin N)) := by
            simp [Fin.ext_iff]; omega
          have hnkl : k1 ∉ ({l} : Finset (Fin N)) := by
            simp [Fin.ext_iff]; omega
          rw [Finset.card_insert_of_notMem hn0k, Finset.card_insert_of_notMem hn1k,
            Finset.card_insert_of_notMem hnkl, Finset.card_singleton]
        · rw [Finset.disjoint_left]
          intro x hx hxS
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact h0_not_S hxS
          · exact h1_not_S hxS
          · exact hk1_not_S hxS
          · exact hl_not_S hxS
      · refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩, k1, k2}, ?_, ?_⟩
        · have hn0k : (⟨0, by omega⟩ : Fin N) ∉ ({⟨1, by omega⟩, k1, k2} : Finset (Fin N)) := by
            simp [Fin.ext_iff]; omega
          have hn1k : (⟨1, by omega⟩ : Fin N) ∉ ({k1, k2} : Finset (Fin N)) := by
            simp [Fin.ext_iff]; exact ⟨by omega, by omega⟩
          have hnkl : k1 ∉ ({k2} : Finset (Fin N)) := by
            simp only [Finset.mem_singleton]; exact h12
          rw [Finset.card_insert_of_notMem hn0k, Finset.card_insert_of_notMem hn1k,
            Finset.card_insert_of_notMem hnkl, Finset.card_singleton]
        · rw [Finset.disjoint_left]
          intro x hx hxS
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact h0_not_S hxS
          · exact h1_not_S hxS
          · exact hk1_not_S hxS
          · exact hk2_not_S hxS
    obtain ⟨D, hDcard, hDdis⟩ := h4_notin
    have hsub : S ⊆ Finset.univ \ D := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_right.mp hDdis hx⟩
    have hcard := (Finset.card_le_card hsub).trans (by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hDcard])
    omega

  let R := reachFrom N S isUnary in0 in1 outW
  have hR_sub : R ⊆ S := reachFrom_subset N S isUnary in0 in1 outW
  have hR_card : R.card ≤ 7 := (Finset.card_le_card hR_sub).trans hS_le7
  have houtJ_R : outJ ∈ R := by
    dsimp only [R]
    rw [reachFrom]
    have h8 : 8 ≤ outW := by omega
    have hN' : outW - 8 < N := by omega
    have hj_eq : (⟨outW - 8, hN'⟩ : Fin N) = outJ := Fin.ext (by simp [outW])
    simp only [h8, hN', ↓reduceDIte, hj_eq, houtJ_S]
    split_ifs <;> simp
  let gateSlots : Fin N → List Nat := fun k => if isUnary k then [in0 k] else [in0 k, in1 k]
  let slots : List Nat := R.toList.flatMap gateSlots
  have hslots_len : slots.length =
      (R.filter (fun k => isUnary k)).card + 2 * (R.filter (fun k => !isUnary k)).card := by
    have hsum : ∀ (l : List (Fin N)), l.Nodup →
        (l.flatMap gateSlots).length =
          (l.filter (fun k => isUnary k)).length + 2 * (l.filter (fun k => !isUnary k)).length := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        rcases List.nodup_cons.mp hl with ⟨_, hxs⟩
        have ihx := ih hxs
        rw [List.flatMap_cons, List.length_append, ihx]
        cases hx : isUnary x <;>
          simp [gateSlots, hx] <;> omega
    have hf1 : (R.filter (fun k => isUnary k)).card = (R.toList.filter (fun k => isUnary k)).length := by
      rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList R).filter _)]
      congr 1; ext x; simp
    have hf2 : (R.filter (fun k => !isUnary k)).card = (R.toList.filter (fun k => !isUnary k)).length := by
      rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList R).filter _)]
      congr 1; ext x; simp
    rw [hf1, hf2]
    exact hsum R.toList (Finset.nodup_toList R)
  have hvars_sub : Finset.range 8 ⊆ slots.toFinset := by
    intro v hv
    rw [Finset.mem_range] at hv
    let i : Fin 8 := ⟨v, hv⟩
    obtain ⟨y, z, hyz, hne⟩ := pm3_0_essential i
    by_contra hnot
    have heq := evalW_eq_of_agree N S isUnary gateOp in0 in1 y z outW (fun k hk v' hv' hv8 => by
      by_cases hvi : v' = v
      · exfalso; apply hnot
        rw [← hvi, List.mem_toFinset]
        exact List.mem_flatMap.mpr ⟨k, Finset.mem_toList.mpr hk, hv'⟩
      · exact hyz ⟨v', hv8⟩ (by simp [Fin.ext_iff, i, hvi]))
      (fun h8 => by exfalso; omega)
    rw [heval_out y, heval_out z] at heq
    exact hne heq
  have hgates_sub : (R.erase outJ).image (fun k => 8 + k.val) ⊆ slots.toFinset := by
    intro v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨k, hk, rfl⟩
    rw [Finset.mem_erase] at hk
    have hne : 8 + k.val ≠ outW := fun heq => hk.1 (Fin.ext (by omega))
    obtain ⟨p, hpR, hmem⟩ := parent_in_reachFrom N S isUnary in0 in1 hin_lt outW k hk.2 hne
    rw [List.mem_toFinset]
    exact List.mem_flatMap.mpr ⟨p, Finset.mem_toList.mpr hpR, hmem⟩
  have hdis_rg : Disjoint (Finset.range 8) ((R.erase outJ).image (fun k => 8 + k.val)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rw [Finset.mem_range] at hv1
    rw [Finset.mem_image] at hv2
    rcases hv2 with ⟨k, _, rfl⟩
    omega
  have him_card : ((R.erase outJ).image (fun k => 8 + k.val)).card = R.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b hab => Fin.ext (by omega)),
      Finset.card_erase_of_mem houtJ_R]
  have hbound_card : 8 + (R.card - 1) ≤ slots.toFinset.card := by
    have hu := Finset.card_le_card (Finset.union_subset hvars_sub hgates_sub)
    rw [Finset.card_union_of_disjoint hdis_rg, Finset.card_range, him_card] at hu
    exact hu
  have htofin : slots.toFinset.card ≤ slots.length := List.toFinset_card_le slots
  have hR_sum : (R.filter (fun k => isUnary k)).card + (R.filter (fun k => !isUnary k)).card = R.card := by
    simpa [Finset.filter_not] using Finset.card_filter_add_card_filter_not (s := R) (p := fun k => isUnary k = true)
  have hR_ge1 : 1 ≤ R.card := Finset.card_pos.mpr ⟨outJ, houtJ_R⟩
  have hu0 : (R.filter (fun k => isUnary k)).card = 0 := by omega
  have hR7 : R.card = 7 := by omega
  have hslots_nodup : slots.Nodup := nodup_of_toFinset_card_eq slots (by omega)
  have hR_bin : ∀ k ∈ R, isUnary k = false := by
    intro k hk
    cases hu : isUnary k
    · rfl
    · exfalso
      have : k ∈ R.filter (fun k => isUnary k) := Finset.mem_filter.mpr ⟨hk, hu⟩
      rw [Finset.card_eq_zero.mp hu0] at this
      simp at this
  have hunique_slot : ∀ p₁ p₂, p₁ ∈ R → p₂ ∈ R → ∀ v, v ∈ gateSlots p₁ → v ∈ gateSlots p₂ → p₁ = p₂ := by
    intro p₁ p₂ hp1 hp2 v hv1 hv2
    exact eq_of_mem_flatMap_nodup R.toList gateSlots (Finset.nodup_toList R) hslots_nodup
      (Finset.mem_toList.mpr hp1) (Finset.mem_toList.mpr hp2) hv1 hv2

  have hdis_children : ∀ j ∈ R, Disjoint (reachFrom N S isUnary in0 in1 (in0 j)) (reachFrom N S isUnary in0 in1 (in1 j)) := by
    intro j hjR
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    let I := reachFrom N S isUnary in0 in1 (in0 j) ∩ reachFrom N S isUnary in0 in1 (in1 j)
    have hIne : I.Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hx0, hx1⟩⟩
    let km := I.max' hIne
    have hkmI : km ∈ I := Finset.max'_mem I hIne
    have hkm0 : km ∈ reachFrom N S isUnary in0 in1 (in0 j) := (Finset.mem_inter.mp hkmI).1
    have hkm1 : km ∈ reachFrom N S isUnary in0 in1 (in1 j) := (Finset.mem_inter.mp hkmI).2
    have hSub0 : reachFrom N S isUnary in0 in1 (in0 j) ⊆ R := by
      have := reachFrom_sub_self N S isUnary in0 in1 outW j hjR
      intro z hz; apply this
      rw [reachFrom]
      have hlt0 := (hin_lt j (hR_sub hjR)).1
      have hlt1 := (hin_lt j (hR_sub hjR)).2 (hR_bin j hjR)
      simp [show 8 ≤ 8 + j.val by omega, j.isLt, hR_sub hjR, hR_bin j hjR, hlt0, hlt1, hz]
    have hSub1 : reachFrom N S isUnary in0 in1 (in1 j) ⊆ R := by
      have := reachFrom_sub_self N S isUnary in0 in1 outW j hjR
      intro z hz; apply this
      rw [reachFrom]
      have hlt0 := (hin_lt j (hR_sub hjR)).1
      have hlt1 := (hin_lt j (hR_sub hjR)).2 (hR_bin j hjR)
      simp [show 8 ≤ 8 + j.val by omega, j.isLt, hR_sub hjR, hR_bin j hjR, hlt0, hlt1, hz]
    have hne_in : in0 j ≠ in1 j := hin_ne j (hR_sub hjR) (hR_bin j hjR)
    have hlt_km0 : 8 + km.val ≤ in0 j := reachFrom_lt N S isUnary in0 in1 (in0 j) km hkm0
    have hlt_km1 : 8 + km.val ≤ in1 j := reachFrom_lt N S isUnary in0 in1 (in1 j) km hkm1
    by_cases h0eq : 8 + km.val = in0 j
    · have hne1 : 8 + km.val ≠ in1 j := by omega
      obtain ⟨p, hp1, hmem⟩ := parent_in_reachFrom N S isUnary in0 in1 hin_lt (in1 j) km hkm1 hne1
      have hp_eq : p = j := hunique_slot p j (hSub1 hp1) hjR (8 + km.val) hmem (by simp [gateSlots, hR_bin j hjR, h0eq])
      have hp_lt := reachFrom_lt N S isUnary in0 in1 (in1 j) p hp1
      have hltj := (hin_lt j (hR_sub hjR)).2 (hR_bin j hjR)
      rw [hp_eq] at hp_lt
      omega
    · by_cases h1eq : 8 + km.val = in1 j
      · obtain ⟨p, hp0, hmem⟩ := parent_in_reachFrom N S isUnary in0 in1 hin_lt (in0 j) km hkm0 h0eq
        have hp_eq : p = j := hunique_slot p j (hSub0 hp0) hjR (8 + km.val) hmem (by simp [gateSlots, hR_bin j hjR, h1eq])
        have hp_lt := reachFrom_lt N S isUnary in0 in1 (in0 j) p hp0
        have hltj := (hin_lt j (hR_sub hjR)).1
        rw [hp_eq] at hp_lt
        omega
      · obtain ⟨p0, hp0, hmem0⟩ := parent_in_reachFrom N S isUnary in0 in1 hin_lt (in0 j) km hkm0 h0eq
        obtain ⟨p1, hp1, hmem1⟩ := parent_in_reachFrom N S isUnary in0 in1 hin_lt (in1 j) km hkm1 h1eq
        have hp_eq : p0 = p1 := hunique_slot p0 p1 (hSub0 hp0) (hSub1 hp1) (8 + km.val) hmem0 hmem1
        subst hp_eq
        have hp_I : p0 ∈ I := Finset.mem_inter.mpr ⟨hp0, hp1⟩
        have hle_m : p0 ≤ km := Finset.le_max' I p0 hp_I
        have hp_gt : km.val < p0.val := by
          have : 8 + km.val ∈ gateSlots p0 := hmem0
          simp only [gateSlots, hR_bin p0 (hSub0 hp0), Bool.false_eq_true, ↓reduceIte,
            List.mem_cons, List.not_mem_nil, or_false] at this
          have hlt0 := (hin_lt p0 (hR_sub (hSub0 hp0))).1
          have hlt1 := (hin_lt p0 (hR_sub (hSub0 hp0))).2 (hR_bin p0 (hSub0 hp0))
          rcases this with h | h <;> omega
        exact Nat.not_lt_of_ge hle_m hp_gt

  have htree : ∀ w, reachFrom N S isUnary in0 in1 w ⊆ R → w < 8 + N →
      (8 ≤ w → ∃ h : w - 8 < N, (⟨w - 8, h⟩ : Fin N) ∈ S) →
      (∀ y, (buildTree N S gateOp in0 in1 w).eval y = evalW N S isUnary gateOp in0 in1 y w) ∧
      (buildTree N S gateOp in0 in1 w).vars.length ≤ 1 + (reachFrom N S isUnary in0 in1 w).card := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwR hw_lt hwS
      by_cases hw8 : w < 8
      · simp only [buildTree, hw8, ↓reduceDIte, BTree.eval, BTree.vars, List.length_singleton]
        constructor
        · intro y; simp [evalW, hw8]
        · omega
      · have hN' : w - 8 < N := by omega
        obtain ⟨_, hjS⟩ := hwS (by omega)
        let j : Fin N := ⟨w - 8, hN'⟩
        have hjS' : (⟨w - 8, hN'⟩ : Fin N) ∈ S := hjS
        have hjR : j ∈ R := by
          apply hwR
          rw [reachFrom]
          simp only [show 8 ≤ w by omega, hN', hjS', ↓reduceDIte]
          split_ifs <;> simp [j]
        have hu_j : isUnary j = false := hR_bin j hjR
        have hj_val : j.val = w - 8 := rfl
        have hlt0 : in0 j < w := by have := (hin_lt j hjS).1; omega
        have hlt1 : in1 j < w := by have := (hin_lt j hjS).2 hu_j; omega
        have hR_eq : reachFrom N S isUnary in0 in1 w =
            insert j (reachFrom N S isUnary in0 in1 (in0 j) ∪ reachFrom N S isUnary in0 in1 (in1 j)) := by
          rw [reachFrom]
          simp only [show 8 ≤ w by omega, hN', ↓reduceDIte, hjS']
          rw [show (⟨w - 8, hN'⟩ : Fin N) = j from rfl]
          simp only [hu_j, Bool.false_eq_true, ↓reduceIte, hlt0, hlt1, ↓reduceDIte]
        have hsub0 : reachFrom N S isUnary in0 in1 (in0 j) ⊆ R := by
          intro z hz; exact hwR (by rw [hR_eq]; simp [hz])
        have hsub1 : reachFrom N S isUnary in0 in1 (in1 j) ⊆ R := by
          intro z hz; exact hwR (by rw [hR_eq]; simp [hz])
        have hs0 : 8 ≤ in0 j → ∃ h : in0 j - 8 < N, (⟨in0 j - 8, h⟩ : Fin N) ∈ S := by
          intro h8
          obtain ⟨_, a, b, _, hb, _, wa, wb, hca, _, _, h0, _, _, _⟩ := (hsurv_props j hjS).2 hu_j
          have hbd_a := hcanon_bound N (le_refl N) a (by omega)
          change match canon a with | .inl _ => True | .inr wc => _ at hbd_a
          rw [hca] at hbd_a
          rw [h0] at h8 ⊢
          obtain ⟨hNa, hma, _⟩ := hbd_a.2 h8
          exact ⟨hNa, hma⟩
        have hs1 : 8 ≤ in1 j → ∃ h : in1 j - 8 < N, (⟨in1 j - 8, h⟩ : Fin N) ∈ S := by
          intro h8
          obtain ⟨_, a, b, _, hb, _, wa, wb, _, hcb, _, _, h1, _, _⟩ := (hsurv_props j hjS).2 hu_j
          have hbd_b := hcanon_bound N (le_refl N) b (by omega)
          change match canon b with | .inl _ => True | .inr wc => _ at hbd_b
          rw [hcb] at hbd_b
          rw [h1] at h8 ⊢
          obtain ⟨hNb, hmb, _⟩ := hbd_b.2 h8
          exact ⟨hNb, hmb⟩
        obtain ⟨ih0_e, ih0_l⟩ := ih (in0 j) hlt0 hsub0 (by omega) hs0
        obtain ⟨ih1_e, ih1_l⟩ := ih (in1 j) hlt1 hsub1 (by omega) hs1
        constructor
        · intro y
          conv_lhs => rw [buildTree]
          conv_rhs => unfold evalW
          simp only [hw8, ↓reduceDIte, hN', hjS']
          rw [show (⟨w - 8, hN'⟩ : Fin N) = j from rfl]
          simp only [hlt0, hlt1, ↓reduceDIte, hu_j, Bool.false_eq_true, ↓reduceIte, BTree.eval, ih0_e, ih1_e]
        · rw [buildTree]
          simp only [hw8, ↓reduceDIte, hN', hjS']
          rw [show (⟨w - 8, hN'⟩ : Fin N) = j from rfl]
          simp only [hlt0, hlt1, ↓reduceDIte, BTree.vars, List.length_append]
          have hj_notin : j ∉ reachFrom N S isUnary in0 in1 (in0 j) ∪ reachFrom N S isUnary in0 in1 (in1 j) := by
            intro hmem
            rcases Finset.mem_union.mp hmem with hm | hm
            · have := reachFrom_lt N S isUnary in0 in1 (in0 j) j hm; omega
            · have := reachFrom_lt N S isUnary in0 in1 (in1 j) j hm; omega
          have hdis_j := hdis_children j hjR
          have hcard_eq : (reachFrom N S isUnary in0 in1 w).card =
              1 + (reachFrom N S isUnary in0 in1 (in0 j)).card +
                (reachFrom N S isUnary in0 in1 (in1 j)).card := by
            rw [hR_eq, Finset.card_insert_of_notMem hj_notin, Finset.card_union_of_disjoint hdis_j]
            omega
          omega
  have hout_S : 8 ≤ outW → ∃ h : outW - 8 < N, (⟨outW - 8, h⟩ : Fin N) ∈ S := fun _ =>
    ⟨by omega, by convert houtJ_S; simp [outW]⟩
  obtain ⟨ht_eval, ht_len⟩ := htree outW Finset.Subset.rfl (by omega) hout_S
  let T := buildTree N S gateOp in0 in1 outW
  have hT_eval : ∀ y : Fin 8 → Bool, T.eval y = pm3_0 y := fun y => (ht_eval y).trans (heval_out y)
  have hT_all : ∀ i : Fin 8, i ∈ T.vars := by
    intro i
    obtain ⟨y, z, hyz, hne⟩ := pm3_0_essential i
    by_contra hni
    have heq := T.eval_eq_of_agree y z (fun k hk => hyz k (fun heq => hni (heq ▸ hk)))
    rw [hT_eval y, hT_eval z] at heq
    exact hne heq
  have hT_nodup : T.vars.Nodup := by
    apply nodup_of_toFinset_card_eq
    have hle1 : 8 ≤ T.vars.toFinset.card := by
      have hsub : (Finset.univ : Finset (Fin 8)) ⊆ T.vars.toFinset :=
        fun i _ => List.mem_toFinset.mpr (hT_all i)
      simpa using Finset.card_le_card hsub
    have hle2 : T.vars.toFinset.card ≤ T.vars.length := List.toFinset_card_le T.vars
    have hle3 : T.vars.length ≤ 8 := by
      dsimp only [T]
      change (buildTree N S gateOp in0 in1 outW).vars.length ≤ 1 + R.card at ht_len
      omega
    omega
  exact no_read_once_pm3_0 T hT_nodup hT_eval

end PEqualNP.Outside.L_meta_27136_aux

theorem PEqualNP.Outside.L_meta_27136 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩)) := by
  rintro ⟨C, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact PEqualNP.Outside.L_meta_27136_aux.main_aux C h1 h2 h3 h4 h5 h6 h7 h8 h9
