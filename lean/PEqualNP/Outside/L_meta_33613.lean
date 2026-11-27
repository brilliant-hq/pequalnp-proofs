import Mathlib
import PEqualNP.Defs

-- Credit: the namespaces Helpers, RepReads, RepPath and RepInduced below are copied from
-- PEqualNP.MetaComplexity.Helpers (Shannon, RepReads, RepPath, RepInduced; the first three as
-- inlined in PEqualNP.Outside.L_meta_22890), inlined because those modules are not built here.

namespace PEqualNP.Outside.L_meta_33613

namespace Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
end Helpers

namespace RepReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_33613.Helpers
open PEqualNP.Represents

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro N; exact ⟨N, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 : g.inputs.length ≤ 2 := hg g (by simp)
    by_cases hm : n + gs.length ∈ N
    · obtain ⟨N', hc, hN⟩ := ih hgs (N.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · have h1 := Finset.card_union_le (N.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, hm⟩
        rw [List.length_append, List.length_singleton]
        omega
      · have H := hN x y hx hy h
        rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        split_ifs with hk
        · congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hk, hi⟩))
    · obtain ⟨N', hc, hN⟩ := ih hgs N
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        have hk : i ≠ n + gs.length := fun h => hm (h ▸ hi)
        rw [if_neg hk, if_neg hk]
        exact hN x y hx hy h i hi

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

theorem reads_le {n m s : ℕ} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨S, hcard, hS⟩ := needed (n + m) C.gates (fun g hg => (hC g hg).2) {C.output}
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
    fun g hg => (hC g hg).1
  have hev : ∀ P, C.eval (inp (n + m) P) =
      (wiresFrom C.gates (inp (n + m) P)).getD C.output false := fun P => rfl

  have hoff : ∀ P w, w ∉ S → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hev, hev]
    refine hS _ _ (by simp [inp]) (by simp [inp]) (fun i hi => ?_) _ (Finset.mem_singleton_self _)
    rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
    have : i ≠ w := fun e => hw (e ▸ hi)
    tauto
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    rw [hev, hev]
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v
    rw [← oneEach_eq]; exact hR u v
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ S := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ S := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ S := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  rw [Finset.card_singleton] at hcard
  have : C.gates.length ≤ s := hs
  omega

end RepReads

namespace RepPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_33613.Helpers
open PEqualNP.Represents

def on (a c : ℕ) : ℕ → Bool := fun i => decide (i = a) || decide (i = c)

theorem on_iff (a c i : ℕ) : on a c i = true ↔ i = a ∨ i = c := by simp [on]

def Dep (F : (ℕ → Bool) → Bool) (N : Finset ℕ) : Prop :=
  ∀ x y : ℕ → Bool, (∀ i ∈ N, x i = y i) → F x = F y

def Free (F : (ℕ → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem free_or {F : (ℕ → Bool) → Bool} {N : Finset ℕ} (hd : Dep F N) (hf : Free F) {t p q : ℕ}
    (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    Free fun x => F (Function.update x t (x p || x q)) := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset N
  let r : ℕ → ℕ := fun a => if a = p ∨ a = q then t else if a ∈ N.erase t then a else z
  have key : ∀ a c, F (Function.update (on a c) t (on a c p || on a c q)) = F (on (r a) (r c)) := by
    intro a c
    refine hd _ _ fun i hi => bool_ext ?_
    have hr : ∀ a, (i = t → (i = r a ↔ a = p ∨ a = q)) ∧ (i ≠ t → (i = r a ↔ i = a)) := by
      intro a
      have hiz : i ≠ z := fun h => hz (h ▸ hi)
      constructor
      · intro hit
        simp only [r]
        split_ifs with h1 h2
        · simp [hit, h1]
        · have := Finset.ne_of_mem_erase h2
          simp only [h1, iff_false]; rw [hit]; exact fun h => this h.symm
        · simp [h1, hiz]
      · intro hit
        have hiN : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
        simp only [r]
        split_ifs with h1 h2
        · simp only [hit, false_iff]
          rintro rfl
          rcases h1 with rfl | rfl
          · exact hp hiN
          · exact hq hiN
        · rfl
        · simp only [hiz, false_iff]
          rintro rfl; exact h2 hiN
    rw [on_iff]
    by_cases hit : i = t
    · rw [(hr a).1 hit, (hr c).1 hit, hit, Function.update_self, Bool.or_eq_true, on_iff, on_iff]
      constructor
      · rintro ((h | h) | (h | h)) <;> simp [h]
      · rintro ((h | h) | (h | h)) <;> simp [h]
    · rw [(hr a).2 hit, (hr c).2 hit, Function.update_of_ne hit, on_iff]
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false || false)) = false
    rw [show Function.update (fun _ : ℕ => false) t (false || false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
  · intro a b c d
    simp only [key]
    exact hf.2 _ _ _ _

theorem free_and {F : (ℕ → Bool) → Bool} {N : Finset ℕ} (hd : Dep F N) (hf : Free F) {t p q : ℕ}
    (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    Free fun x => F (Function.update x t (x p && x q)) := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset N
  let r : ℕ → ℕ := fun a => if a ∈ N.erase t then a else z
  have rp : r p = z := if_neg hp
  have rq : r q = z := if_neg hq
  have hzz : ∀ x, F (on x z) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hzz' : ∀ x, F (on z x) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hz0 : F (on z z) = false := by
    rw [← hf.1]
    exact hd _ _ fun i hi => by
      have : i ≠ z := fun h => hz (h ▸ hi)
      simp [on, this]
  have key : ∀ a c, ¬ (a = p ∧ c = q) → ¬ (a = q ∧ c = p) →
      F (Function.update (on a c) t (on a c p && on a c q)) = F (on (r a) (r c)) := by
    intro a c h1 h2
    refine hd _ _ fun i hi => bool_ext ?_
    have hiz : i ≠ z := fun h => hz (h ▸ hi)
    have hr : ∀ a, i = r a ↔ i ≠ t ∧ i = a := by
      intro a
      simp only [r]
      split_ifs with h
      · constructor
        · intro e; exact ⟨e ▸ Finset.ne_of_mem_erase h, e⟩
        · exact fun e => e.2
      · simp only [hiz, false_iff]
        rintro ⟨e1, rfl⟩
        exact h (Finset.mem_erase.2 ⟨e1, hi⟩)
    rw [on_iff, hr, hr]
    by_cases hit : i = t
    · rw [hit, Function.update_self, Bool.and_eq_true, on_iff, on_iff]
      constructor
      · rintro ⟨e1 | e1, e2 | e2⟩
        · exact absurd (e1.trans e2.symm) hpq
        · exact absurd ⟨e1.symm, e2.symm⟩ h1
        · exact absurd ⟨e2.symm, e1.symm⟩ h2
        · exact absurd (e1.trans e2.symm) hpq
      · rintro (⟨e, _⟩ | ⟨e, _⟩) <;> exact absurd rfl e
    · rw [Function.update_of_ne hit, on_iff]
      simp [hit]
  have kk : ∀ a, F (Function.update (on a a) t (on a a p && on a a q)) = F (on (r a) (r a)) :=
    fun a => key a a (fun h => hpq (h.1.symm.trans h.2)) (fun h => hpq (h.2.symm.trans h.1))
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    rw [show Function.update (fun _ : ℕ => false) t (false && false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
  · intro a b c d ha hb hc hd' hac had hbc
    beta_reduce at ha hb hc hd' hac had hbc

    have nb : ∀ e f, (e = p ∨ e = q) →
        F (Function.update (on f f) t (on f f p && on f f q)) = false →
        (F (Function.update (on e f) t (on e f p && on e f q)) = true →
          (e = p ∧ f = q) ∨ (e = q ∧ f = p)) ∧
        (F (Function.update (on f e) t (on f e p && on f e q)) = true →
          (f = p ∧ e = q) ∨ (f = q ∧ e = p)) := by
      intro e f he hf0
      have re : r e = z := by rcases he with rfl | rfl <;> assumption
      rw [kk] at hf0
      constructor
      · intro h
        by_contra hn
        rw [key e f (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz', hf0] at h
        exact Bool.noConfusion h
      · intro h
        by_contra hn
        rw [key f e (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz, hf0] at h
        exact Bool.noConfusion h
    by_cases hA : a = p ∨ a = q
    · have e1 := (nb a c hA hc).1 hac
      have e2 := (nb a d hA hd').1 had
      have : c = d := by
        rcases e1 with ⟨x, y⟩ | ⟨x, y⟩ <;> rcases e2 with ⟨x', y'⟩ | ⟨x', y'⟩
        · rw [y, y']
        · exact absurd (x.symm.trans x') hpq
        · exact absurd (x'.symm.trans x) hpq
        · rw [y, y']
      rw [← this]; exact hbc
    · by_cases hB : b = p ∨ b = q
      · have e1 := (nb b c hB hc).1 hbc
        have hC : c = p ∨ c = q := by
          rcases e1 with ⟨_, y⟩ | ⟨_, y⟩
          · exact Or.inr y
          · exact Or.inl y
        have e2 := (nb c a hC ha).2 hac
        exact absurd (by rcases e2 with ⟨x, _⟩ | ⟨x, _⟩ <;> simp [x]) hA
      · have n1 : ∀ e, ¬ (a = p ∧ e = q) ∧ ¬ (a = q ∧ e = p) := fun e =>
          ⟨fun h => hA (Or.inl h.1), fun h => hA (Or.inr h.1)⟩
        have n2 : ∀ e, ¬ (b = p ∧ e = q) ∧ ¬ (b = q ∧ e = p) := fun e =>
          ⟨fun h => hB (Or.inl h.1), fun h => hB (Or.inr h.1)⟩
        rw [kk] at ha hb hc hd'
        rw [key _ _ (n1 c).1 (n1 c).2] at hac
        rw [key _ _ (n1 d).1 (n1 d).2] at had
        rw [key _ _ (n2 c).1 (n2 c).2] at hbc
        show F (Function.update (on b d) t (on b d p && on b d q)) = true
        rw [key _ _ (n2 d).1 (n2 d).2]
        exact hf.2 _ _ _ _ ha hb hc hd' hac had hbc

def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [RepReads.getD_snoc, Function.update_apply]

theorem back (o : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ t, ∃ N : Finset ℕ, N.card ≤ 1 + gs.length ∧ Dep (fun x => run gs t x o) N ∧
      (N.card = 1 + gs.length → Free fun x => run gs t x o) := by
  induction gs with
  | nil =>
    intro t
    refine ⟨{o}, by simp, fun x y h => h o (by simp), fun _ => ⟨rfl, ?_⟩⟩
    intro a b c d ha hb hc hd hac had hbc
    simp only [run, on, Bool.or_self, decide_eq_false_iff_not, Bool.or_eq_true,
      decide_eq_true_eq] at *
    tauto
  | cons g gs ih =>
    intro t
    have hgs := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    have hg0 := hg g (by simp)
    obtain ⟨N, hc, hd, hf⟩ := ih hgs (t + 1)
    by_cases ht : t ∈ N
    · refine ⟨N.erase t ∪ g.inputs.toFinset, ?_, ?_, ?_⟩
      · have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have := hg0.2
        rw [List.length_cons]; omega
      · intro x y h
        refine hd _ _ fun i hi => ?_
        by_cases hit : i = t
        · subst hit
          simp only [Function.update_self]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · simp only [Function.update_of_ne hit]
          exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
      · intro heq
        rw [List.length_cons] at heq
        have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        have hN : N.card = 1 + gs.length := by omega
        have hI : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
        have hT : g.inputs.toFinset.card = 2 := by omega
        have hL : g.inputs.length = 2 := by omega
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hL
        rw [hpq] at hT hI
        have hne : p ≠ q := by rintro rfl; simp at hT
        have hI' := Finset.card_eq_zero.1 hI
        have hp : p ∉ N.erase t := fun h => by
          have : p ∈ N.erase t ∩ [p, q].toFinset := Finset.mem_inter.2 ⟨h, by simp⟩
          rw [hI'] at this; simp at this
        have hq : q ∉ N.erase t := fun h => by
          have : q ∈ N.erase t ∩ [p, q].toFinset := Finset.mem_inter.2 ⟨h, by simp⟩
          rw [hI'] at this; simp at this
        have hop := hg0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · have := free_and hd (hf hN) hne hp hq
          have e : (fun x => run (g :: gs) t x o) = fun x =>
              (fun x => run gs (t + 1) x o) (Function.update x t (x p && x q)) := by
            funext x; simp [run, hop, hpq, GateOp.eval]
          rw [e]; exact this
        · have := free_or hd (hf hN) hp hq
          have e : (fun x => run (g :: gs) t x o) = fun x =>
              (fun x => run gs (t + 1) x o) (Function.update x t (x p || x q)) := by
            funext x; simp [run, hop, hpq, GateOp.eval]
          rw [e]; exact this
    · refine ⟨N, by rw [List.length_cons]; omega, ?_, ?_⟩
      · intro x y h
        refine hd _ _ fun i hi => ?_
        have hit : i ≠ t := fun e => ht (e ▸ hi)
        simp only [Function.update_of_ne hit]
        exact h i hi
      · intro heq; rw [List.length_cons] at heq; omega

open RepReads in
theorem path : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u x : Fin n) (v w : Fin m), A u v = true → A u w = true → A x v = true → A x w = false → (∃ w' : Fin m, A u w' = false) → (∃ u' : Fin n, A u' v = false) → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card ≤ s := by
  intro n m s A u x v w huv huw hxv hxw ⟨w', huw'⟩ ⟨u', hu'v⟩ h
  by_contra hlt
  have hlt' : s + 1 ≤ (forcedL A).card + (forcedR A).card := by
    unfold forcedL forcedR; omega
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨N, hc, hd, hf⟩ := back C.output C.gates hC (n + m)
  have hsz : C.gates.length ≤ s := hs
  let F : (ℕ → Bool) → Bool := fun x => run C.gates (n + m) x C.output
  have hF : ∀ P : Finset ℕ, C.eval (inp (n + m) P) = F fun i => decide (i < n + m ∧ i ∈ P) := by
    intro P
    show (wiresFrom C.gates (inp (n + m) P)).getD C.output false = _
    rw [run_eq]
    have hl : (inp (n + m) P).length = n + m := by simp [inp]
    rw [hl]
    show run C.gates (n + m) (fun j => (inp (n + m) P).getD j false) C.output = _
    simp only [inp_getD]; rfl
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hR u v
  have hon : ∀ a c, a < n + m → c < n + m → F (on a c) = C.eval (inp (n + m) {a, c}) := by
    intro a c ha hc
    rw [hF]
    congr 1
    funext i
    apply bool_ext
    rw [on_iff, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [*]
    · exact fun h => h.2

  have hoff : ∀ P w, w ∉ N → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hF, hF]
    refine hd _ _ fun i hi => ?_
    have : i ≠ w := fun e => hw (e ▸ hi)
    rw [decide_eq_decide, Finset.mem_erase]
    tauto
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ N := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ N := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ N := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  have hfree := hf (by omega)
  have bu := u.2
  have bx := x.2
  have bv := v.2
  have bw := w.2

  have hrow : ∀ (a : Fin n) (b : Fin m), A a b = false → F (on a a) = false := by
    intro a b hab
    have ba := a.2
    rw [hon _ _ (by omega) (by omega)]
    by_contra hne
    have := hmono {(a : ℕ), (a : ℕ)} {(a : ℕ), n + (b : ℕ)} (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto) (by simpa using hne)
    rw [hA, hab] at this
    exact Bool.noConfusion this
  have hcol : ∀ (a : Fin n) (b : Fin m), A a b = false → F (on (n + b) (n + b)) = false := by
    intro a b hab
    have bb := b.2
    rw [hon _ _ (by omega) (by omega)]
    by_contra hne
    have := hmono {n + (b : ℕ), n + (b : ℕ)} {(a : ℕ), n + (b : ℕ)} (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto) (by simpa using hne)
    rw [hA, hab] at this
    exact Bool.noConfusion this
  have hcell : ∀ (a : Fin n) (b : Fin m), F (on a (n + b)) = A a b := by
    intro a b
    have ba := a.2
    have bb := b.2
    rw [hon _ _ (by omega) (by omega), hA]
  have := hfree.2 u x (n + v) (n + w) (hrow u w' huw') (hrow x w hxw) (hcol u' v hu'v)
    (hcol x w hxw) ((hcell u v).trans huv) ((hcell u w).trans huw) ((hcell x v).trans hxv)
  have e := hcell x w
  rw [hxw] at e
  exact Bool.noConfusion (this.symm.trans e)

end RepPath

namespace RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_33613.Helpers
open PEqualNP.Represents PEqualNP.Outside.L_meta_33613.RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

/-- The new gates and the new names of the old wires (`none`: the wire is off). -/
noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

/-- Gate `j` reads an off wire. -/
def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

/-- An operand off at the end is off when read. -/
theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in
/-- The new wires carry the old values with `Z` off. -/
theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]
          -- the OR of its wires that are not off
          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia
            -- the gate reads exactly `i` and `i'`
            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

/-- Wires the output `o` depends on by reading. -/
def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in
/-- At least as many gates disappear as there are live inputs off. -/
theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          · -- the gate is not off, so one of its wires is not off
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in
/-- Switching off inputs: the circuit that is left. -/
theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

/-- The excess of an induced subgraph without full lines is at most that of the graph. -/
theorem induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
  -- the value with `Z` off
  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      · -- column off: the row alone
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    · -- row off: at most the column alone
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_33613.Helpers PEqualNP.Outside.L_meta_33613.RepReads

/-- A gate with its inputs renamed by `r`. -/
def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem snoc_last (gs : List Gate) (g : Gate) (W : List Bool) (k : ℕ)
    (hk : k = W.length + gs.length) :
    (wiresFrom (gs ++ [g]) W).getD k false =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs W).getD i false) := by
  rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, if_pos hk]

theorem snoc_lt (gs : List Gate) (g : Gate) (W : List Bool) (i : ℕ)
    (hi : i < W.length + gs.length) :
    (wiresFrom (gs ++ [g]) W).getD i false = (wiresFrom gs W).getD i false := by
  rw [wiresFrom_snoc, getD_snoc, length_wiresFrom, if_neg (by omega)]

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

/-- Renaming wires: the copied gates read the renamed wires and agree with the old ones. -/
theorem ren (x y : List Bool) (d : ℕ) (r : ℕ → ℕ) (hy : y.length = x.length + d)
    (hr : ∀ w, x.length ≤ w → r w = w + d) (hlt : ∀ w, w < x.length → r w < y.length)
    (hv : ∀ w, w < x.length → y.getD (r w) false = x.getD w false) (gs : List Gate) :
    ∀ w, (wiresFrom (gs.map (rg r)) y).getD (r w) false = (wiresFrom gs x).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    by_cases h : w < x.length
    · exact hv w h
    · have := hr w (by omega)
      simp only [List.map_nil]
      show y.getD (r w) false = x.getD w false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, wiresFrom_snoc, wiresFrom_snoc, getD_snoc,
      getD_snoc, length_wiresFrom, length_wiresFrom, List.length_map]
    by_cases hw : w = x.length + gs.length
    · have := hr w (by omega)
      rw [if_pos (by omega), if_pos hw]
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact ih a
    · have : r w ≠ y.length + gs.length := by
        by_cases h : w < x.length
        · have := hlt w h; omega
        · have := hr w (by omega); omega
      rw [if_neg this, if_neg hw]
      exact ih w

/-! ### OR chains -/

theorem any_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ c ∈ l, f c = g c) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.any_cons]
    rw [h c (by simp), ih (fun d hd => h d (by simp [hd]))]

/-- OR gates folding the wires `a :: t`, the first gate becoming wire `B`. -/
def orc : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | a, B, b :: t => ⟨GateOp.or, [a, b]⟩ :: orc B (B + 1) t

/-- The wire holding the OR of `a :: t`. -/
def orf : ℕ → ℕ → List ℕ → ℕ
  | a, _, [] => a
  | _, B, _ :: t => orf B (B + 1) t

theorem orc_length : ∀ (t : List ℕ) (a B : ℕ), (orc a B t).length = t.length := by
  intro t
  induction t with
  | nil => intro a B; rfl
  | cons b t ih => intro a B; simp [orc, ih]

theorem orc_ok : ∀ (t : List ℕ) (a B : ℕ), ∀ g ∈ orc a B t,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro t
  induction t with
  | nil => intro a B g hg; simp [orc] at hg
  | cons b t ih =>
    intro a B g hg
    simp only [orc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ih _ _ g hg

theorem orf_lt : ∀ (t : List ℕ) (a B : ℕ), a < B → orf a B t < B + t.length := by
  intro t
  induction t with
  | nil => intro a B h; simpa [orf] using h
  | cons b t ih =>
    intro a B _
    have := ih B (B + 1) (by omega)
    simp only [orf, List.length_cons]; omega

theorem orc_val : ∀ (t : List ℕ) (a B : ℕ) (x : List Bool), x.length = B → a < B →
    (∀ b ∈ t, b < B) →
    (wiresFrom (orc a B t) x).getD (orf a B t) false =
      (x.getD a false || t.any fun b => x.getD b false) := by
  intro t
  induction t with
  | nil => intro a B x _ _ _; simp [orc, orf, wiresFrom]
  | cons b t ih =>
    intro a B x hx ha ht
    have hb := ht b (by simp)
    have e : wiresFrom (orc a B (b :: t)) x = wiresFrom (orc B (B + 1) t)
        (x ++ [GateOp.or.eval ([a, b].map fun i => x.getD i false)]) := rfl
    have e2 : orf a B (b :: t) = orf B (B + 1) t := rfl
    rw [e, e2, ih B (B + 1) _ (by simp [hx]) (by omega)
      (fun c hc => by have := ht c (by simp [hc]); omega)]
    have hl : ∀ c, c < B → (x ++ [GateOp.or.eval ([a, b].map fun i => x.getD i false)]).getD c false
        = x.getD c false := fun c hc => List.getD_append _ _ _ _ (by omega)
    rw [any_congr' (l := t) (fun c hc => hl c (ht c (by simp [hc])))]
    rw [show B = x.length from hx.symm, List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil, eval_or2,
      List.any_cons]
    cases x.getD a false <;> cases x.getD b false <;> simp

/-- The same with the values read off an earlier wire list `X`. -/
theorem orc_val' (a : ℕ) (t : List ℕ) (X x : List Bool) (B : ℕ) (hx : x.length = B)
    (hXB : X.length ≤ B) (hpre : ∀ i < X.length, x.getD i false = X.getD i false)
    (hl : ∀ b ∈ a :: t, b < X.length) :
    (wiresFrom (orc a B t) x).getD (orf a B t) false = (a :: t).any fun b => X.getD b false := by
  have ha := hl a (by simp)
  rw [orc_val t a B x hx (by omega) (fun b hb => by have := hl b (by simp [hb]); omega),
    List.any_cons, hpre a ha, any_congr' (l := t) (fun c hc => hpre c (hl c (by simp [hc])))]


/-! ### Copying a circuit into the padded table -/

/-- Old input wires go to their place in the padded input; gate wires move up by `k`. -/
def rr (n m p k w : ℕ) : ℕ := if w < n then w else if w < n + m then w + p else w + k

/-- The old inputs that are on at the padded input `(u, v)`. -/
def Pset (n m p u v : ℕ) : Finset ℕ :=
  (Finset.range (n + m)).filter fun w => (w < n ∧ w = u) ∨ (n ≤ w ∧ w + p = n + p + v)

theorem X_getD {n m p q : ℕ} (u : Fin (n + p)) (v : Fin (m + q)) (w : ℕ) :
    (oneEach u v).getD w false =
      decide (w < n + p + (m + q) ∧ (w = u.val ∨ w = n + p + v.val)) := by
  rw [oneEach_eq, inp_getD]; simp

theorem X_length {n m p q : ℕ} (u : Fin (n + p)) (v : Fin (m + q)) :
    (oneEach u v).length = n + p + (m + q) := by simp [oneEach]

theorem copy_val (n m p q : ℕ) (D : Circuit) (pre : List Gate) (G : ℕ) (hG : pre.length = G)
    (u : Fin (n + p)) (v : Fin (m + q)) :
    (wiresFrom (D.gates.map (rg (rr n m p (p + q + G)))) (wiresFrom pre (oneEach u v))).getD
      (rr n m p (p + q + G) D.output) false = D.eval (inp (n + m) (Pset n m p u v)) := by
  have hu := u.2
  have hv := v.2
  have hXl := X_length u v
  have hxl : (inp (n + m) (Pset n m p u v)).length = n + m := by simp [inp]
  have hYl : (wiresFrom pre (oneEach u v)).length = n + m + (p + q + G) := by
    rw [length_wiresFrom, hXl, hG]; omega
  refine ren _ _ (p + q + G) (rr n m p (p + q + G)) (by rw [hYl, hxl])
    (fun w hw => by rw [hxl] at hw; simp only [rr]; rw [if_neg (by omega), if_neg (by omega)])
    (fun w hw => by rw [hxl] at hw; rw [hYl]; simp only [rr]; split_ifs <;> omega)
    (fun w hw => ?_) D.gates D.output
  rw [hxl] at hw
  have hrw : rr n m p (p + q + G) w < n + p + (m + q) := by simp only [rr]; split_ifs <;> omega
  rw [getD_wiresFrom _ _ _ (by rw [hXl]; exact hrw), X_getD, inp_getD]
  simp only [Pset, Finset.mem_filter, Finset.mem_range, decide_eq_decide]
  simp only [rr]
  split_ifs <;> omega

theorem evmono (D : Circuit) (hD : Monotone2 D) (N : ℕ) (P Q : Finset ℕ) (h : P ⊆ Q)
    (hP : D.eval (inp N P) = true) : D.eval (inp N Q) = true :=
  mono D.gates (fun g hg => (hD g hg).1) _ _ (by simp [inp]) (fun i => by
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, h b⟩) _ hP

theorem cval_old {n m p q : ℕ} (D : Circuit) (B : Fin n → Fin m → Bool) (hR : Represents B D)
    (u : Fin (n + p)) (v : Fin (m + q)) (hu : u.val < n) (hv : v.val < m) :
    D.eval (inp (n + m) (Pset n m p u v)) = B ⟨u.val, hu⟩ ⟨v.val, hv⟩ := by
  rw [← hR, oneEach_eq]
  have : Pset n m p u v = {u.val, n + v.val} := by
    ext w
    simp only [Pset, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [this]

theorem cval_le {n m p q : ℕ} (D : Circuit) (hD : Monotone2 D) (B : Fin n → Fin m → Bool)
    (hR : Represents B D) (u : Fin (n + p)) (v : Fin (m + q)) (u' : Fin n) (v' : Fin m)
    (h1 : u.val < n → u'.val = u.val) (h2 : v.val < m → v'.val = v.val)
    (h : D.eval (inp (n + m) (Pset n m p u v)) = true) : B u' v' = true := by
  rw [← hR u' v', oneEach_eq]
  refine evmono D hD _ _ _ (fun w hw => ?_) h
  simp only [Pset, Finset.mem_filter, Finset.mem_range] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hw with ⟨_, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
  · left; have := h1 (by omega); omega
  · right; have := h2 (by omega); omega

/-! ### Row and column lists -/

def rowsL (n : ℕ) (S : Fin n → Bool) : List ℕ := ((List.finRange n).filter S).map Fin.val

def colsL (n p m : ℕ) (S : Fin m → Bool) : List ℕ :=
  ((List.finRange m).filter S).map fun j => n + p + j.val

theorem rows_lt {n : ℕ} (S : Fin n → Bool) : ∀ b ∈ rowsL n S, b < n := by
  intro b hb
  simp only [rowsL, List.mem_map] at hb
  obtain ⟨i, _, rfl⟩ := hb
  exact i.2

theorem cols_lt {n p m : ℕ} (S : Fin m → Bool) : ∀ b ∈ colsL n p m S, n + p ≤ b ∧ b < n + p + m := by
  intro b hb
  simp only [colsL, List.mem_map] at hb
  obtain ⟨j, _, rfl⟩ := hb
  have := j.2
  omega

theorem rows_any {n m p q : ℕ} (S : Fin n → Bool) (u : Fin (n + p)) (v : Fin (m + q)) :
    (rowsL n S).any (fun b => (oneEach u v).getD b false) =
      decide (∃ i : Fin n, S i = true ∧ i.val = u.val) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp only [rowsL, List.mem_map, List.mem_filter, List.mem_finRange, true_and, X_getD,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    have := i.2
    exact ⟨i, hi, by omega⟩
  · rintro ⟨i, hi, he⟩
    have := i.2
    have := u.2
    exact ⟨i, ⟨i, hi, rfl⟩, by omega⟩

theorem cols_any {n m p q : ℕ} (S : Fin m → Bool) (u : Fin (n + p)) (v : Fin (m + q)) :
    (colsL n p m S).any (fun b => (oneEach u v).getD b false) =
      decide (∃ j : Fin m, S j = true ∧ j.val = v.val) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp only [colsL, List.mem_map, List.mem_filter, List.mem_finRange, true_and, X_getD,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, h⟩
    have := j.2
    have := u.2
    exact ⟨j, hj, by omega⟩
  · rintro ⟨j, hj, he⟩
    have := j.2
    have := v.2
    exact ⟨_, ⟨j, hj, rfl⟩, by omega⟩

theorem rows_len {n : ℕ} (S : Fin n → Bool) :
    (rowsL n S).length + (rowsL n fun i => !S i).length = n := by
  simp only [rowsL, List.length_map]
  have := List.length_eq_length_filter_add (l := List.finRange n) S
  simp only [List.length_finRange] at this
  omega

theorem cols_len {n p m : ℕ} (S : Fin m → Bool) :
    (colsL n p m S).length + (colsL n p m fun i => !S i).length = m := by
  simp only [colsL, List.length_map]
  have := List.length_eq_length_filter_add (l := List.finRange m) S
  simp only [List.length_finRange] at this
  omega

theorem rows_cons {n : ℕ} (S : Fin n → Bool) (h : ∃ i, S i = true) :
    ∃ a t, rowsL n S = a :: t := by
  obtain ⟨i, hi⟩ := h
  apply List.exists_cons_of_ne_nil
  intro e
  have : i.val ∈ rowsL n S := by simp only [rowsL, List.mem_map, List.mem_filter, List.mem_finRange, true_and]; exact ⟨i, hi, rfl⟩
  rw [e] at this
  simp at this

theorem cols_cons {n p m : ℕ} (S : Fin m → Bool) (h : ∃ i, S i = true) :
    ∃ a t, colsL n p m S = a :: t := by
  obtain ⟨i, hi⟩ := h
  apply List.exists_cons_of_ne_nil
  intro e
  have : n + p + i.val ∈ colsL n p m S := by simp [colsL]; exact ⟨i, hi, rfl⟩
  rw [e] at this
  simp at this

/-! ### A guarded copy: one OR chain, the copy, one AND -/

def guardC (n m p q : ℕ) (D : Circuit) (a : ℕ) (t : List ℕ) : Circuit :=
  ⟨orc a (n + p + (m + q)) t ++ D.gates.map (rg (rr n m p (p + q + t.length))) ++
    [⟨GateOp.and, [rr n m p (p + q + t.length) D.output, orf a (n + p + (m + q)) t]⟩],
   n + p + (m + q) + t.length + D.gates.length⟩

theorem guard_ok (n m p q : ℕ) (D : Circuit) (hD : Monotone2 D) (a : ℕ) (t : List ℕ) :
    Monotone2 (guardC n m p q D a t) := by
  intro g hg
  simp only [guardC, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact orc_ok t a _ g hg
  · exact ⟨(hD g' hg').1, by simp only [rg, List.length_map]; exact (hD g' hg').2⟩
  · exact ⟨by simp, by simp⟩

theorem guard_size (n m p q : ℕ) (D : Circuit) (a : ℕ) (t : List ℕ) :
    (guardC n m p q D a t).size = t.length + D.size + 1 := by
  simp [guardC, Circuit.size, orc_length]
  omega

theorem guard_val (n m p q : ℕ) (D : Circuit) (a : ℕ) (t : List ℕ)
    (hl : ∀ b ∈ a :: t, b < n + p + (m + q)) (u : Fin (n + p)) (v : Fin (m + q)) :
    (guardC n m p q D a t).eval (oneEach u v) = (D.eval (inp (n + m) (Pset n m p u v)) &&
      (a :: t).any fun b => (oneEach u v).getD b false) := by
  have hXl := X_length u v
  have ha := hl a (by simp)
  show (wiresFrom (orc a (n + p + (m + q)) t ++ D.gates.map (rg (rr n m p (p + q + t.length))) ++
    [⟨GateOp.and, [rr n m p (p + q + t.length) D.output, orf a (n + p + (m + q)) t]⟩])
      (oneEach u v)).getD (n + p + (m + q) + t.length + D.gates.length) false = _
  rw [snoc_last _ _ _ _ (by rw [List.length_append, orc_length, List.length_map, hXl]; omega)]
  simp only [List.map_cons, List.map_nil, eval_and2]
  rw [wiresFrom_append, copy_val n m p q D _ t.length (orc_length t a _),
    getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, orc_length, hXl]; exact orf_lt t a _ (by omega)),
    orc_val' a t (oneEach u v) (oneEach u v) _ hXl (by omega) (fun _ _ => rfl)
      (fun b hb => by rw [hXl]; exact hl b hb)]

/-- The OR of the row wires `a :: t` as a circuit on the old inputs. -/
def rowC (n m a : ℕ) (t : List ℕ) : Circuit := ⟨orc a (n + m) t, orf a (n + m) t⟩

theorem rowC_eval (n m a : ℕ) (t : List ℕ) (hl : ∀ b ∈ a :: t, b < n + m) (P : Finset ℕ) :
    (rowC n m a t).eval (inp (n + m) P) = (a :: t).any fun b => decide (b ∈ P) := by
  have hxl : (inp (n + m) P).length = n + m := by simp [inp]
  show (wiresFrom (orc a (n + m) t) (inp (n + m) P)).getD (orf a (n + m) t) false = _
  rw [orc_val' a t (inp (n + m) P) (inp (n + m) P) _ hxl (by omega) (fun _ _ => rfl)
    (fun b hb => by rw [hxl]; exact hl b hb)]
  apply any_congr'
  intro b hb
  rw [inp_getD]
  have := hl b hb
  simp [this]

theorem rowC_ok (n m a : ℕ) (t : List ℕ) : Monotone2 (rowC n m a t) :=
  fun g hg => orc_ok t a _ g hg


/-! ### Full rows and full columns: four OR chains and four gates -/

/-- Four nonempty wire lists `aF :: tF`, `aN :: tN`, `cF :: sF`, `cN :: sN`. -/
abbrev L4s := ℕ × List ℕ × ℕ × List ℕ × ℕ × List ℕ × ℕ × List ℕ

def L4s.aF (L : L4s) : ℕ := L.1
def L4s.tF (L : L4s) : List ℕ := L.2.1
def L4s.aN (L : L4s) : ℕ := L.2.2.1
def L4s.tN (L : L4s) : List ℕ := L.2.2.2.1
def L4s.cF (L : L4s) : ℕ := L.2.2.2.2.1
def L4s.sF (L : L4s) : List ℕ := L.2.2.2.2.2.1
def L4s.cN (L : L4s) : ℕ := L.2.2.2.2.2.2.1
def L4s.sN (L : L4s) : List ℕ := L.2.2.2.2.2.2.2

def B2 (N : ℕ) (L : L4s) : ℕ := N + L.tF.length
def B3 (N : ℕ) (L : L4s) : ℕ := B2 N L + L.tN.length
def B4 (N : ℕ) (L : L4s) : ℕ := B3 N L + L.sF.length
def MM (N : ℕ) (L : L4s) : ℕ := B4 N L + L.sN.length

def chains (N : ℕ) (L : L4s) : List Gate :=
  ((orc L.aF N L.tF ++ orc L.aN (B2 N L) L.tN) ++ orc L.cF (B3 N L) L.sF) ++
    orc L.cN (B4 N L) L.sN

def pre4 (N : ℕ) (L : L4s) : List Gate :=
  (((chains N L ++ [⟨GateOp.or, [orf L.cF (B3 N L) L.sF, orf L.cN (B4 N L) L.sN]⟩]) ++
    [⟨GateOp.and, [orf L.aN (B2 N L) L.tN, orf L.cF (B3 N L) L.sF]⟩]) ++
    [⟨GateOp.or, [orf L.aF N L.tF, MM N L + 1]⟩]) ++ [⟨GateOp.and, [MM N L + 2, MM N L]⟩]

theorem chains_len (N : ℕ) (L : L4s) : (chains N L).length = MM N L - N := by
  simp only [chains, List.length_append, orc_length, MM, B4, B3, B2]; omega

theorem pre4_len (N : ℕ) (L : L4s) : (pre4 N L).length = MM N L - N + 4 := by
  simp only [pre4, List.length_append, chains_len, List.length_singleton]

theorem chains_ok (N : ℕ) (L : L4s) : ∀ g ∈ chains N L,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [chains, List.mem_append] at hg
  rcases hg with ((h | h) | h) | h <;> exact orc_ok _ _ _ g h

theorem pre4_ok (N : ℕ) (L : L4s) : ∀ g ∈ pre4 N L,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [pre4, List.mem_append, List.mem_singleton] at hg
  rcases hg with (((h | rfl) | rfl) | rfl) | rfl
  · exact chains_ok N L g h
  all_goals exact ⟨by simp, by simp⟩

/-- All wires of the four lists are inputs. -/
def L4s.ok (N : ℕ) (L : L4s) : Prop :=
  (∀ b ∈ L.aF :: L.tF, b < N) ∧ (∀ b ∈ L.aN :: L.tN, b < N) ∧
    (∀ b ∈ L.cF :: L.sF, b < N) ∧ (∀ b ∈ L.cN :: L.sN, b < N)

theorem chains_val (N : ℕ) (L : L4s) (hL : L.ok N) (X : List Bool) (hX : X.length = N) :
    (wiresFrom (chains N L) X).getD (orf L.aF N L.tF) false =
      (L.aF :: L.tF).any (fun b => X.getD b false) ∧
    (wiresFrom (chains N L) X).getD (orf L.aN (B2 N L) L.tN) false =
      (L.aN :: L.tN).any (fun b => X.getD b false) ∧
    (wiresFrom (chains N L) X).getD (orf L.cF (B3 N L) L.sF) false =
      (L.cF :: L.sF).any (fun b => X.getD b false) ∧
    (wiresFrom (chains N L) X).getD (orf L.cN (B4 N L) L.sN) false =
      (L.cN :: L.sN).any (fun b => X.getD b false) := by
  obtain ⟨h1, h2, h3, h4⟩ := hL
  have a1 := h1 _ (List.mem_cons_self ..)
  have a2 := h2 _ (List.mem_cons_self ..)
  have a3 := h3 _ (List.mem_cons_self ..)
  have a4 := h4 _ (List.mem_cons_self ..)
  have o1 := orf_lt L.tF L.aF N (by omega)
  have o2 := orf_lt L.tN L.aN (B2 N L) (by simp only [B2]; omega)
  have o3 := orf_lt L.sF L.cF (B3 N L) (by simp only [B3, B2]; omega)
  have e : wiresFrom (chains N L) X = wiresFrom (orc L.cN (B4 N L) L.sN)
      (wiresFrom (orc L.cF (B3 N L) L.sF) (wiresFrom (orc L.aN (B2 N L) L.tN)
        (wiresFrom (orc L.aF N L.tF) X))) := by
    simp only [chains, wiresFrom_append]
  have l1 : (wiresFrom (orc L.aF N L.tF) X).length = B2 N L := by
    rw [length_wiresFrom, orc_length, hX]; rfl
  have l2 : (wiresFrom (orc L.aN (B2 N L) L.tN) (wiresFrom (orc L.aF N L.tF) X)).length =
      B3 N L := by rw [length_wiresFrom, orc_length, l1]; rfl
  have l3 : (wiresFrom (orc L.cF (B3 N L) L.sF) (wiresFrom (orc L.aN (B2 N L) L.tN)
      (wiresFrom (orc L.aF N L.tF) X))).length = B4 N L := by
    rw [length_wiresFrom, orc_length, l2]; rfl
  have hB2 : N ≤ B2 N L := by simp only [B2]; omega
  have hB3 : B2 N L ≤ B3 N L := by simp only [B3]; omega
  have hB4 : B3 N L ≤ B4 N L := by simp only [B4]; omega
  have p1 : ∀ i < X.length, (wiresFrom (orc L.aF N L.tF) X).getD i false = X.getD i false :=
    fun i hi => getD_wiresFrom _ _ _ hi
  have p2 : ∀ i < X.length, (wiresFrom (orc L.aN (B2 N L) L.tN)
      (wiresFrom (orc L.aF N L.tF) X)).getD i false = X.getD i false := fun i hi => by
    rw [getD_wiresFrom _ _ _ (by omega), p1 i hi]
  have p3 : ∀ i < X.length, (wiresFrom (orc L.cF (B3 N L) L.sF) (wiresFrom (orc L.aN (B2 N L) L.tN)
      (wiresFrom (orc L.aF N L.tF) X))).getD i false = X.getD i false := fun i hi => by
    rw [getD_wiresFrom _ _ _ (by omega), p2 i hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, getD_wiresFrom _ _ _ (by rw [l3]; simp only [B4, B3, B2] at *; omega),
      getD_wiresFrom _ _ _ (by rw [l2]; simp only [B3, B2] at *; omega),
      getD_wiresFrom _ _ _ (by rw [l1]; simp only [B2] at *; omega),
      orc_val' _ _ X X N hX (by omega) (fun _ _ => rfl) (fun b hb => by rw [hX]; exact h1 b hb)]
  · rw [e, getD_wiresFrom _ _ _ (by rw [l3]; simp only [B4, B3] at *; omega),
      getD_wiresFrom _ _ _ (by rw [l2]; simp only [B3] at *; omega),
      orc_val' _ _ X _ (B2 N L) l1 (by omega) p1 (fun b hb => by rw [hX]; exact h2 b hb)]
  · rw [e, getD_wiresFrom _ _ _ (by rw [l3]; simp only [B4] at *; omega),
      orc_val' _ _ X _ (B3 N L) l2 (by omega) p2 (fun b hb => by rw [hX]; exact h3 b hb)]
  · rw [e, orc_val' _ _ X _ (B4 N L) l3 (by omega) p3 (fun b hb => by rw [hX]; exact h4 b hb)]

theorem pre4_val (N : ℕ) (L : L4s) (hL : L.ok N) (X : List Bool) (hX : X.length = N) :
    (wiresFrom (pre4 N L) X).getD (MM N L + 3) false =
      ((((L.aF :: L.tF).any fun b => X.getD b false) ||
        (((L.aN :: L.tN).any fun b => X.getD b false) &&
          ((L.cF :: L.sF).any fun b => X.getD b false))) &&
        (((L.cF :: L.sF).any fun b => X.getD b false) ||
          ((L.cN :: L.sN).any fun b => X.getD b false))) := by
  obtain ⟨v1, v2, v3, v4⟩ := chains_val N L hL X hX
  obtain ⟨h1, h2, h3, h4⟩ := hL
  have a1 := h1 _ (List.mem_cons_self ..)
  have a2 := h2 _ (List.mem_cons_self ..)
  have a3 := h3 _ (List.mem_cons_self ..)
  have a4 := h4 _ (List.mem_cons_self ..)
  have o1 := orf_lt L.tF L.aF N (by omega)
  have o2 := orf_lt L.tN L.aN (B2 N L) (by simp only [B2]; omega)
  have o3 := orf_lt L.sF L.cF (B3 N L) (by simp only [B3, B2]; omega)
  have o4 := orf_lt L.sN L.cN (B4 N L) (by simp only [B4, B3, B2]; omega)
  have hc : (chains N L).length = L.tF.length + L.tN.length + L.sF.length + L.sN.length := by
    simp only [chains, List.length_append, orc_length]
  simp only [pre4]
  rw [snoc_last _ _ _ (MM N L + 3) ?_]
  · simp only [List.map_cons, List.map_nil, eval_and2]
    rw [snoc_last _ _ _ (MM N L + 2) ?_, snoc_lt _ _ _ (MM N L) ?_]
    · simp only [List.map_cons, List.map_nil, eval_or2]
      rw [snoc_last _ _ _ (MM N L + 1) ?_, snoc_lt _ _ _ (orf L.aF N L.tF) ?_,
        snoc_lt _ _ _ (MM N L) ?_]
      · simp only [List.map_cons, List.map_nil, eval_and2]
        rw [snoc_last _ _ _ (MM N L) ?_, snoc_lt _ _ _ (orf L.aF N L.tF) ?_,
          snoc_lt _ _ _ (orf L.aN (B2 N L) L.tN) ?_, snoc_lt _ _ _ (orf L.cF (B3 N L) L.sF) ?_]
        · simp only [List.map_cons, List.map_nil, eval_or2]
          rw [v1, v2, v3, v4]
        all_goals simp only [List.length_append, List.length_singleton, hc, hX, MM, B4, B3,
          B2] at *
        all_goals omega
      all_goals simp only [List.length_append, List.length_singleton, hc, hX, MM, B4, B3,
        B2] at *
      all_goals omega
    all_goals simp only [List.length_append, List.length_singleton, hc, hX, MM, B4, B3,
      B2] at *
    all_goals omega
  all_goals simp only [List.length_append, List.length_singleton, hc, hX, MM, B4, B3, B2] at *
  all_goals omega


theorem MM_ge (N : ℕ) (L : L4s) : N ≤ MM N L := by simp only [MM, B4, B3, B2]; omega

def fourC (n m p q : ℕ) (D : Circuit) (L : L4s) : Circuit :=
  ⟨pre4 (n + p + (m + q)) L ++
    D.gates.map (rg (rr n m p (p + q + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4)))) ++
    [⟨GateOp.or, [MM (n + p + (m + q)) L + 3,
      rr n m p (p + q + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4)) D.output]⟩],
   n + p + (m + q) + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4) + D.gates.length⟩

theorem four_ok (n m p q : ℕ) (D : Circuit) (hD : Monotone2 D) (L : L4s) :
    Monotone2 (fourC n m p q D L) := by
  intro g hg
  simp only [fourC, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact pre4_ok _ L g hg
  · exact ⟨(hD g' hg').1, by simp only [rg, List.length_map]; exact (hD g' hg').2⟩
  · exact ⟨by simp, by simp⟩

theorem four_size (n m p q : ℕ) (D : Circuit) (L : L4s) :
    (fourC n m p q D L).size = L.tF.length + L.tN.length + L.sF.length + L.sN.length + 4 +
      D.size + 1 := by
  simp only [fourC, Circuit.size, List.length_append, pre4_len, List.length_map,
    List.length_singleton, MM, B4, B3, B2]
  omega

theorem four_val (n m p q : ℕ) (D : Circuit) (L : L4s) (hL : L.ok (n + p + (m + q)))
    (u : Fin (n + p)) (v : Fin (m + q)) :
    (fourC n m p q D L).eval (oneEach u v) =
      (((((L.aF :: L.tF).any fun b => (oneEach u v).getD b false) ||
        (((L.aN :: L.tN).any fun b => (oneEach u v).getD b false) &&
          ((L.cF :: L.sF).any fun b => (oneEach u v).getD b false))) &&
        (((L.cF :: L.sF).any fun b => (oneEach u v).getD b false) ||
          ((L.cN :: L.sN).any fun b => (oneEach u v).getD b false))) ||
        D.eval (inp (n + m) (Pset n m p u v))) := by
  have hXl := X_length u v
  have hge := MM_ge (n + p + (m + q)) L
  show (wiresFrom (pre4 (n + p + (m + q)) L ++
    D.gates.map (rg (rr n m p (p + q + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4)))) ++
    [⟨GateOp.or, [MM (n + p + (m + q)) L + 3,
      rr n m p (p + q + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4)) D.output]⟩])
      (oneEach u v)).getD
      (n + p + (m + q) + (MM (n + p + (m + q)) L - (n + p + (m + q)) + 4) + D.gates.length)
        false = _
  rw [snoc_last _ _ _ _ (by rw [List.length_append, pre4_len, List.length_map, hXl]; omega)]
  simp only [List.map_cons, List.map_nil, eval_or2]
  rw [wiresFrom_append, copy_val n m p q D _ _ (pre4_len _ L),
    getD_wiresFrom _ _ _ (by rw [length_wiresFrom, pre4_len, hXl]; omega),
    pre4_val _ L hL _ hXl]

theorem T_ok (N : ℕ) (L : L4s) : Monotone2 ⟨pre4 N L, MM N L + 3⟩ := fun g hg => pre4_ok N L g hg

theorem exfin {n : ℕ} (S : Fin n → Bool) (k : ℕ) :
    decide (∃ i : Fin n, S i = true ∧ i.val = k) = if h : k < n then S ⟨k, h⟩ else false := by
  by_cases h : k < n
  · rw [dif_pos h]
    rcases hS : S ⟨k, h⟩ with _ | _
    · rw [decide_eq_false_iff_not]
      rintro ⟨i, hi, rfl⟩
      rw [show i = ⟨i.val, h⟩ from Fin.ext rfl, hS] at hi
      exact Bool.noConfusion hi
    · rw [decide_eq_true_iff]; exact ⟨⟨k, h⟩, hS, rfl⟩
  · rw [dif_neg h, decide_eq_false_iff_not]
    rintro ⟨i, _, rfl⟩
    exact h i.2

theorem rows_anyP {n : ℕ} (S : Fin n → Bool) (P : Finset ℕ) :
    (rowsL n S).any (fun b => decide (b ∈ P)) = decide (∃ i : Fin n, S i = true ∧ i.val ∈ P) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp only [rowsL, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨i, hi, rfl⟩, h⟩


open PEqualNP.Outside.L_meta_33613.RepInduced in
theorem part1 (n m p q : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Fin n → Fin m → Bool) (s : ℕ)
    (hA : RepSizeAtMost A s) :
    RepSizeAtMost (fun (i : Fin (n + p)) (j : Fin (m + q)) =>
      if hi : i.val < n then if hj : j.val < m then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else false
      else false) (s + (n + m - 1)) := by
  have hA0 := hA
  obtain ⟨C, hC, hs, hR⟩ := hA
  have hs' : C.gates.length ≤ s := hs
  obtain ⟨a, t, ht⟩ := cols_cons (n := n) (p := p) (fun _ : Fin m => true) ⟨⟨0, hm⟩, rfl⟩
  have hlen : t.length + 1 = m := by
    have : (colsL n p m fun _ : Fin m => true).length = m := by simp [colsL]
    rw [ht] at this; simpa using this
  have hl : ∀ b ∈ a :: t, b < n + p + (m + q) := by
    rw [← ht]; intro b hb; have := cols_lt _ b hb; omega
  obtain ⟨a0, t0, ht0⟩ := rows_cons (fun _ : Fin n => true) ⟨⟨0, hn⟩, rfl⟩
  have hlen0 : t0.length + 1 = n := by
    have : (rowsL n fun _ : Fin n => true).length = n := by simp [rowsL]
    rw [ht0] at this; simpa using this
  by_cases hcol : ∀ v : Fin m, ∃ u, A u v = false
  · -- guard the columns
    refine ⟨guardC n m p q C a t, guard_ok n m p q C hC a t, ?_, fun u v => ?_⟩
    · rw [guard_size]; show t.length + C.gates.length + 1 ≤ _; omega
    · beta_reduce
      rw [guard_val n m p q C a t hl u v, ← ht, cols_any, exfin]
      by_cases hv : v.val < m
      · rw [dif_pos hv, Bool.and_true]
        by_cases hu : u.val < n
        · rw [cval_old C A hR u v hu hv, dif_pos hu, dif_pos hv]
        · rw [dif_neg hu]
          by_contra hne
          rw [Bool.not_eq_false] at hne
          obtain ⟨u', hu'⟩ := hcol ⟨v.val, hv⟩
          have := cval_le C hC A hR u v u' ⟨v.val, hv⟩ (fun h => absurd h hu) (fun _ => rfl) hne
          rw [hu'] at this; exact Bool.noConfusion this
      · rw [dif_neg hv, Bool.and_false]
        by_cases hu : u.val < n
        · rw [dif_pos hu, dif_neg hv]
        · rw [dif_neg hu]
  by_cases hrow : ∀ u : Fin n, ∃ v, A u v = false
  · -- guard the rows
    have hl0 : ∀ b ∈ a0 :: t0, b < n + p + (m + q) := by
      rw [← ht0]; intro b hb; have := rows_lt _ b hb; omega
    refine ⟨guardC n m p q C a0 t0, guard_ok n m p q C hC a0 t0, ?_, fun u v => ?_⟩
    · rw [guard_size]; show t0.length + C.gates.length + 1 ≤ _; omega
    · beta_reduce
      rw [guard_val n m p q C a0 t0 hl0 u v, ← ht0, rows_any, exfin]
      by_cases hu : u.val < n
      · rw [dif_pos hu, Bool.and_true, dif_pos hu]
        by_cases hv : v.val < m
        · rw [cval_old C A hR u v hu hv, dif_pos hv]
        · rw [dif_neg hv]
          by_contra hne
          rw [Bool.not_eq_false] at hne
          obtain ⟨v', hv'⟩ := hrow ⟨u.val, hu⟩
          have := cval_le C hC A hR u v ⟨u.val, hu⟩ v' (fun _ => rfl) (fun h => absurd h hv) hne
          rw [hv'] at this; exact Bool.noConfusion this
      · rw [dif_neg hu, Bool.and_false, dif_neg hu]
  push_neg at hcol hrow
  obtain ⟨v0, hv0⟩ := hcol
  obtain ⟨u0, hu0⟩ := hrow
  have hl0 : ∀ b ∈ a0 :: t0, b < n + m := by
    rw [← ht0]; intro b hb; have := rows_lt _ b hb; omega
  by_cases hall : ∀ u v, A u v = true
  · -- all true: the OR of the rows, guarded by the columns
    have hDR : Represents A (rowC n m a0 t0) := by
      intro u' v'
      rw [oneEach_eq, rowC_eval n m a0 t0 hl0, ← ht0, rows_anyP, hall u' v', decide_eq_true_iff]
      exact ⟨u', rfl, by simp⟩
    refine ⟨guardC n m p q (rowC n m a0 t0) a t, guard_ok n m p q _ (rowC_ok n m a0 t0) a t, ?_,
      fun u v => ?_⟩
    · rw [guard_size]
      have : (rowC n m a0 t0).size = t0.length := orc_length t0 a0 _
      omega
    · beta_reduce
      rw [guard_val n m p q _ a t hl u v, ← ht, cols_any, exfin, rowC_eval n m a0 t0 hl0, ← ht0,
        rows_anyP]
      by_cases hu : u.val < n
      · have h1 : decide (∃ i : Fin n, (fun _ : Fin n => true) i = true ∧
            i.val ∈ Pset n m p u v) = true := by
          rw [decide_eq_true_iff]
          exact ⟨⟨u.val, hu⟩, rfl, by simp [Pset]; omega⟩
        rw [h1, Bool.true_and, dif_pos hu]
        by_cases hv : v.val < m
        · rw [dif_pos hv, dif_pos hv, hall]
        · rw [dif_neg hv, dif_neg hv]
      · have h1 : decide (∃ i : Fin n, (fun _ : Fin n => true) i = true ∧
            i.val ∈ Pset n m p u v) = false := by
          rw [decide_eq_false_iff_not]
          rintro ⟨i, _, hi⟩
          simp only [Pset, Finset.mem_filter, Finset.mem_range] at hi
          have := i.2
          omega
        rw [h1, Bool.false_and, dif_neg hu]
  push_neg at hall
  obtain ⟨u1, v1, h11⟩ := hall
  simp only [ne_eq, Bool.not_eq_false, Bool.not_eq_true] at hu0 hv0 h11
  -- full rows and full columns, not all true
  let fr : Fin n → Bool := fun i => decide (∀ v, A i v = true)
  let fc : Fin m → Bool := fun j => decide (∀ u, A u j = true)
  have fr_t : ∀ i, fr i = true ↔ ∀ v, A i v = true := fun i => decide_eq_true_iff
  have fc_t : ∀ j, fc j = true ↔ ∀ u, A u j = true := fun j => decide_eq_true_iff
  have fru0 : fr u0 = true := (fr_t u0).2 hu0
  have fcv0 : fc v0 = true := (fc_t v0).2 hv0
  have fru1 : fr u1 = false := by
    rcases h : fr u1 with _ | _
    · rfl
    · rw [(fr_t u1).1 h v1] at h11; exact absurd h11 (by simp)
  have fcv1 : fc v1 = false := by
    rcases h : fc v1 with _ | _
    · rfl
    · rw [(fc_t v1).1 h u1] at h11; exact absurd h11 (by simp)
  obtain ⟨aF, tF, hF⟩ := rows_cons fr ⟨u0, fru0⟩
  obtain ⟨aN, tN, hN⟩ := rows_cons (fun i => !fr i) ⟨u1, by simp [fru1]⟩
  obtain ⟨cF, sF, hcF⟩ := cols_cons (n := n) (p := p) fc ⟨v0, fcv0⟩
  obtain ⟨cN, sN, hcN⟩ := cols_cons (n := n) (p := p) (fun j => !fc j) ⟨v1, by simp [fcv1]⟩
  let L : L4s := ⟨aF, tF, aN, tN, cF, sF, cN, sN⟩
  have hLok : L.ok (n + p + (m + q)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ∀ b ∈ aF :: tF, _
      rw [← hF]; intro b hb; have := rows_lt _ b hb; omega
    · show ∀ b ∈ aN :: tN, _
      rw [← hN]; intro b hb; have := rows_lt _ b hb; omega
    · show ∀ b ∈ cF :: sF, _
      rw [← hcF]; intro b hb; have := cols_lt _ b hb; omega
    · show ∀ b ∈ cN :: sN, _
      rw [← hcN]; intro b hb; have := cols_lt _ b hb; omega
  have hG : tF.length + tN.length + sF.length + sN.length + 4 = n + m := by
    have h1 := rows_len fr
    have h2 := cols_len (n := n) (p := p) fc
    rw [hF, hN] at h1
    rw [hcF, hcN] at h2
    simp only [List.length_cons] at h1 h2
    omega
  -- the value of the four lists at the padded input
  have hT : ∀ (u : Fin (n + p)) (v : Fin (m + q)),
      ((((L.aF :: L.tF).any fun b => (oneEach u v).getD b false) ||
        (((L.aN :: L.tN).any fun b => (oneEach u v).getD b false) &&
          ((L.cF :: L.sF).any fun b => (oneEach u v).getD b false))) &&
        (((L.cF :: L.sF).any fun b => (oneEach u v).getD b false) ||
          ((L.cN :: L.sN).any fun b => (oneEach u v).getD b false))) =
        if hu : u.val < n then if hv : v.val < m then
          (fr ⟨u.val, hu⟩ || fc ⟨v.val, hv⟩) else false else false := by
    intro u v
    show ((((aF :: tF).any fun b => (oneEach u v).getD b false) ||
        (((aN :: tN).any fun b => (oneEach u v).getD b false) &&
          ((cF :: sF).any fun b => (oneEach u v).getD b false))) &&
        (((cF :: sF).any fun b => (oneEach u v).getD b false) ||
          ((cN :: sN).any fun b => (oneEach u v).getD b false))) = _
    rw [← hF, ← hN, ← hcF, ← hcN, rows_any, rows_any, cols_any, cols_any, exfin, exfin, exfin,
      exfin]
    by_cases hu : u.val < n
    · by_cases hv : v.val < m
      · simp only [dif_pos hu, dif_pos hv]
        cases fr ⟨u.val, hu⟩ <;> cases fc ⟨v.val, hv⟩ <;> rfl
      · simp only [dif_pos hu, dif_neg hv]
        cases fr ⟨u.val, hu⟩ <;> rfl
    · simp only [dif_neg hu, Bool.false_or, Bool.false_and]
  by_cases hcore : ∃ u v, A u v = true ∧ fr u = false ∧ fc v = false
  · -- the induced core circuit
    let R : Finset (Fin n) := Finset.univ.filter fun i => fr i = false
    let K : Finset (Fin m) := Finset.univ.filter fun j => fc j = false
    have hRK : ∀ u ∈ R, ∃ v ∈ K, A u v = false := by
      intro u hu
      have : fr u = false := (Finset.mem_filter.1 hu).2
      have : ¬ ∀ v, A u v = true := fun h => by rw [(fr_t u).2 h] at this; exact absurd this (by simp)
      push_neg at this
      obtain ⟨v, hv⟩ := this
      refine ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simpa using hv⟩
      rcases h : fc v with _ | _
      · rfl
      · have := (fc_t v).1 h u; rw [this] at hv; exact absurd hv (by simp)
    have hKR : ∀ v ∈ K, ∃ u ∈ R, A u v = false := by
      intro v hv
      have : fc v = false := (Finset.mem_filter.1 hv).2
      have : ¬ ∀ u, A u v = true := fun h => by rw [(fc_t v).2 h] at this; exact absurd this (by simp)
      push_neg at this
      obtain ⟨u, hu⟩ := this
      refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simpa using hu⟩
      rcases h : fr u with _ | _
      · rfl
      · have := (fr_t u).1 h v; rw [this] at hu; exact absurd hu (by simp)
    obtain ⟨uc, vc, hc1, hc2, hc3⟩ := hcore
    obtain ⟨s', ⟨D, hD, hDs, hDR⟩, hs'⟩ := induced n m s A R K hRK hKR
      ⟨uc, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc2⟩, vc,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hc3⟩, hc1⟩ hA0
    -- the induced circuit saves a gate on each side
    have hBL : ((R.filter fun a => ∃ b ∈ K, A a b = true)).card + 1 ≤
        (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
          ∃ a' : Fin n, A a' b = false)).card := by
      have hnot : u0 ∉ R.filter fun a => ∃ b ∈ K, A a b = true := by
        intro h
        have := (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).2
        rw [fru0] at this; exact absurd this (by simp)
      rw [← Finset.card_insert_of_notMem hnot]
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_insert] at ha
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases ha with rfl | ha
      · exact ⟨v1, hu0 v1, u1, h11⟩
      · obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
        obtain ⟨a', _, ha'⟩ := hKR b hb
        exact ⟨b, hab, a', ha'⟩
    have hBR : ((K.filter fun b => ∃ a ∈ R, A a b = true)).card + 1 ≤
        (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
          ∃ b' : Fin m, A a b' = false)).card := by
      have hnot : v0 ∉ K.filter fun b => ∃ a ∈ R, A a b = true := by
        intro h
        have := (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).2
        rw [fcv0] at this; exact absurd this (by simp)
      rw [← Finset.card_insert_of_notMem hnot]
      apply Finset.card_le_card
      intro b hb
      rw [Finset.mem_insert] at hb
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases hb with rfl | hb
      · exact ⟨u1, hv0 u1, v1, h11⟩
      · obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
        obtain ⟨b', _, hb'⟩ := hRK a ha
        exact ⟨a, hab, b', hb'⟩
    refine ⟨fourC n m p q D L, four_ok n m p q D hD L, ?_, fun u v => ?_⟩
    · rw [four_size]
      have : D.size ≤ s' := hDs
      show tF.length + tN.length + sF.length + sN.length + 4 + D.size + 1 ≤ _
      omega
    · beta_reduce
      rw [four_val n m p q D L hLok u v, hT]
      by_cases hu : u.val < n
      · by_cases hv : v.val < m
        · rw [dif_pos hu, dif_pos hv, dif_pos hu, dif_pos hv,
            cval_old D _ hDR u v hu hv]
          simp only [R, K, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases h1 : fr ⟨u.val, hu⟩ with _ | _ <;> rcases h2 : fc ⟨v.val, hv⟩ with _ | _
          · simp
          · simp [(fc_t _).1 h2]
          · simp [(fr_t _).1 h1]
          · simp [(fr_t _).1 h1]
        · rw [dif_pos hu, dif_neg hv, dif_pos hu, dif_neg hv, Bool.false_or]
          by_contra hne
          rw [Bool.not_eq_false] at hne
          have := cval_le D hD _ hDR u v ⟨u.val, hu⟩ v0 (fun _ => rfl) (fun h => absurd h hv) hne
          simp [K, fcv0] at this
      · rw [dif_neg hu, dif_neg hu, Bool.false_or]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        by_cases hv : v.val < m
        · have := cval_le D hD _ hDR u v u0 ⟨v.val, hv⟩ (fun h => absurd h hu) (fun _ => rfl) hne
          simp [R, fru0] at this
        · have := cval_le D hD _ hDR u v u0 v0 (fun h => absurd h hu) (fun h => absurd h hv) hne
          simp [R, fru0] at this
  · -- no core: the four gates alone
    push_neg at hcore
    have h2 := reads_le A hA0
    have hL1 : 1 ≤ (forcedL A).card :=
      Finset.card_pos.2 ⟨u0, Finset.mem_filter.2 ⟨Finset.mem_univ _, v1, hu0 v1, u1, h11⟩⟩
    have hR1 : 1 ≤ (forcedR A).card :=
      Finset.card_pos.2 ⟨v0, Finset.mem_filter.2 ⟨Finset.mem_univ _, u1, hv0 u1, v1, h11⟩⟩
    refine ⟨⟨pre4 (n + p + (m + q)) L, MM (n + p + (m + q)) L + 3⟩, T_ok _ L, ?_, fun u v => ?_⟩
    · show (pre4 _ L).length ≤ _
      rw [pre4_len]
      simp only [MM, B4, B3, B2]
      show n + p + (m + q) + tF.length + tN.length + sF.length + sN.length -
        (n + p + (m + q)) + 4 ≤ _
      omega
    · beta_reduce
      show (wiresFrom (pre4 _ L) (oneEach u v)).getD _ false = _
      rw [pre4_val _ L hLok _ (X_length u v), hT]
      by_cases hu : u.val < n
      · by_cases hv : v.val < m
        · rw [dif_pos hu, dif_pos hv, dif_pos hu, dif_pos hv]
          rcases h1 : fr ⟨u.val, hu⟩ with _ | _ <;> rcases h2 : fc ⟨v.val, hv⟩ with _ | _
          · rw [Bool.or_false]
            rcases h3 : A ⟨u.val, hu⟩ ⟨v.val, hv⟩ with _ | _
            · rfl
            · exact absurd (hcore _ _ h3 h1) (by simp [h2])
          · rw [(fc_t _).1 h2]; rfl
          · rw [(fr_t _).1 h1]; rfl
          · rw [(fr_t _).1 h1]; rfl
        · rw [dif_pos hu, dif_neg hv, dif_pos hu, dif_neg hv]
      · rw [dif_neg hu, dif_neg hu]


theorem weaken {n m : ℕ} (A : Fin n → Fin m → Bool) (s s' : ℕ) (h : RepSizeAtMost A s)
    (hs : s ≤ s') : RepSizeAtMost A s' := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hs, h3⟩

theorem cross_rep (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    RepSizeAtMost (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0))
      (if n = 1 ∨ m = 1 then 0 else 1) := by
  by_cases h1 : n = 1
  · rw [if_pos (Or.inl h1)]
    refine ⟨⟨[], 0⟩, fun g hg => by simp at hg, le_refl _, fun u v => ?_⟩
    show (oneEach u v).getD 0 false = _
    rw [oneEach_eq, inp_getD]
    have := u.2
    simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
    omega
  by_cases h2 : m = 1
  · rw [if_pos (Or.inr h2)]
    refine ⟨⟨[], n⟩, fun g hg => by simp at hg, le_refl _, fun u v => ?_⟩
    show (oneEach u v).getD n false = _
    rw [oneEach_eq, inp_getD]
    have := u.2
    have := v.2
    simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
    omega
  rw [if_neg (by tauto)]
  refine ⟨⟨[⟨GateOp.or, [0, n]⟩], n + m⟩, fun g hg => ?_, le_refl _, fun u v => ?_⟩
  · simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨by simp, by simp⟩
  · show (wiresFrom ([] ++ [⟨GateOp.or, [0, n]⟩]) (oneEach u v)).getD (n + m) false = _
    rw [snoc_last _ _ _ _ (by simp [oneEach])]
    simp only [List.map_cons, List.map_nil, eval_or2]
    show ((oneEach u v).getD 0 false || (oneEach u v).getD n false) = _
    rw [oneEach_eq, inp_getD, inp_getD]
    have := u.2
    have := v.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hu : u.val = 0 <;> by_cases hv : v.val = 0 <;> simp [hu, hv] <;> omega

theorem cross_low (n m s : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : RepSizeAtMost (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)) s) :
    1 ≤ s := by
  have H := reads_le _ h
  have hL : 1 ≤ (forcedL (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0))).card :=
    Finset.card_pos.2 ⟨⟨0, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨1, by omega⟩,
      by simp, ⟨1, by omega⟩, by simp⟩⟩
  have hR : 1 ≤ (forcedR (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0))).card :=
    Finset.card_pos.2 ⟨⟨0, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨1, by omega⟩,
      by simp, ⟨1, by omega⟩, by simp⟩⟩
  omega

/-- In the padded cross every old row and every old column must be read. -/
theorem ext_forced (n m p q : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) :
    let E := fun (i : Fin (n + p)) (j : Fin (m + q)) =>
      if hi : i.val < n then if hj : j.val < m then
        (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)) ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else false else false
    n ≤ (Finset.univ.filter (fun a : Fin (n + p) => ∃ b : Fin (m + q), E a b = true ∧
      ∃ a' : Fin (n + p), E a' b = false)).card ∧
    m ≤ (Finset.univ.filter (fun b : Fin (m + q) => ∃ a : Fin (n + p), E a b = true ∧
      ∃ b' : Fin (m + q), E a b' = false)).card := by
  intro E
  constructor
  · have hsub : (Finset.univ : Finset (Fin n)).map (Fin.castAddEmb p) ⊆
        Finset.univ.filter (fun a : Fin (n + p) => ∃ b : Fin (m + q), E a b = true ∧
          ∃ a' : Fin (n + p), E a' b = false) := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 ha
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨0, by omega⟩, ?_, ⟨n, by omega⟩, ?_⟩
      · simp [E, hm]
      · simp [E]
    have := Finset.card_le_card hsub
    simpa using this
  · have hsub : (Finset.univ : Finset (Fin m)).map (Fin.castAddEmb q) ⊆
        Finset.univ.filter (fun b : Fin (m + q) => ∃ a : Fin (n + p), E a b = true ∧
          ∃ b' : Fin (m + q), E a b' = false) := by
      intro b hb
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hb
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨0, by omega⟩, ?_, ⟨m, by omega⟩, ?_⟩
      · simp [E, hn]
      · simp [E]
    have := Finset.card_le_card hsub
    simpa using this

open PEqualNP.Outside.L_meta_33613.RepPath in
theorem ext_low (n m p q : ℕ) (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) (s : ℕ)
    (h : RepSizeAtMost (fun (i : Fin (n + p)) (j : Fin (m + q)) =>
      if hi : i.val < n then if hj : j.val < m then
        (fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)) ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else false else false) s) :
    (if n = 1 ∨ m = 1 then 0 else 1) + (n + m - 1) ≤ s := by
  obtain ⟨h1, h2⟩ := ext_forced n m p q hn hm hp hq
  by_cases hb : n = 1 ∨ m = 1
  · rw [if_pos hb]
    have H := reads_le _ h
    unfold forcedL forcedR at H
    omega
  · rw [if_neg hb]
    have hn2 : 2 ≤ n := by omega
    have hm2 : 2 ≤ m := by omega
    have H := path (n + p) (m + q) s _ ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩
      (by simp [hn, hm]) (by simp [hn]; omega) (by simp [hm]; omega) (by simp)
      ⟨⟨m, by omega⟩, by simp⟩ ⟨⟨n, by omega⟩, by simp⟩ h
    have := le_trans (add_le_add h1 h2) H
    omega

end PEqualNP.Outside.L_meta_33613

open PEqualNP.Outside.L_meta_33613 in
theorem PEqualNP.Outside.L_meta_33613 : ∀ (n m p q : Nat), 0 < n → 0 < m → 0 < p → 0 < q →
  let extend := fun (A : Fin n → Fin m → Bool) (i : Fin (n+p)) (j : Fin (m+q)) =>
    if hi : i.val < n then if hj : j.val < m then A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else false else false
  let cross := fun (i : Fin n) (j : Fin m) => decide (i.val = 0 ∨ j.val = 0)
  let base := if n = 1 ∨ m = 1 then 0 else 1
  (∀ (A : Fin n → Fin m → Bool) (s : Nat), PEqualNP.Represents.RepSizeAtMost A s →
    PEqualNP.Represents.RepSizeAtMost (extend A) (s+(n+m-1))) ∧
  (∀ s : Nat, PEqualNP.Represents.RepSizeAtMost cross s ↔ base ≤ s) ∧
  (∀ s : Nat, PEqualNP.Represents.RepSizeAtMost (extend cross) s ↔ base+(n+m-1) ≤ s) := by
  intro n m p q hn hm hp hq extend cross base
  refine ⟨fun A s h => part1 n m p q hn hm A s h, fun s => ⟨fun h => ?_, fun h => ?_⟩,
    fun s => ⟨fun h => ext_low n m p q hn hm hp hq s h, fun h => ?_⟩⟩
  · show (if n = 1 ∨ m = 1 then 0 else 1) ≤ s
    by_cases hb : n = 1 ∨ m = 1
    · rw [if_pos hb]; omega
    · rw [if_neg hb]; exact cross_low n m s (by omega) (by omega) h
  · exact weaken _ _ _ (cross_rep n m hn hm) h
  · exact weaken _ _ _ (part1 n m p q hn hm _ _ (cross_rep n m hn hm)) h
