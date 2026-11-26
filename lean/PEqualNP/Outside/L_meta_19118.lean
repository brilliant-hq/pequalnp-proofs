import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19118

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def live (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private theorem live_eval (g : Gate) (a : ℕ → Bool) :
    g.op.eval ((live g).map a) = g.op.eval (g.inputs.map a) := by
  obtain ⟨op, js⟩ := g
  cases op <;> try rfl
  cases js <;> rfl

private def fire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl fire w

private theorem push_lookup {α : Type} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i = l.length then v else l.getD i d := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [ite_eq_right (ne_of_lt h), List.getD_append _ _ _ _ h]
  · subst i
    simp
  · rw [ite_eq_right (ne_of_gt h)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (fire w g)).length = _
    rw [ih]
    simp [fire]; omega

private theorem primary (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (fire w g)).getD i false = _
    rw [ih _ (by simp [fire]; omega)]
    unfold fire
    exact List.getD_append _ _ _ _ hi

private theorem unread (p : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, p ∉ live g)
    (a b : List Bool) (hlen : a.length = b.length)
    (hval : ∀ i, i ≠ p → a.getD i false = b.getD i false) :
    ∀ i, i ≠ p → (run gs a).getD i false = (run gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact hval
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      rw [← live_eval g, ← live_eval g]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hval i (fun e => h g (by simp) (e ▸ hi))
    change ∀ i, i ≠ p → (run gs (fire a g)).getD i false = (run gs (fire b g)).getD i false
    apply ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    · simp [fire, hlen]
    · intro i hi
      simp only [fire, push_lookup, hlen, hv]
      rw [hval i hi]

private abbrev Ref := Bool ⊕ ℕ

private def load (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr i => w.getD i false

private def bounded (m : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr i => i < m

private abbrev Plan := Ref × List Gate

private def rule (m : ℕ) (value : List Bool → Bool) (P : Plan) : Prop :=
  bounded (m + P.2.length) P.1 ∧ (∀ g ∈ P.2, legal g) ∧ P.2.length ≤ 1 ∧
    ∀ w, w.length = m → load (run P.2 w) P.1 = value w

private theorem pass_rule (m : ℕ) (r : Ref) (h : bounded m r)
    (f : List Bool → Bool) (hf : ∀ w, load w r = f w) : rule m f (r, []) := by
  refine ⟨by simpa using h, by simp, by simp, ?_⟩
  intro w _
  exact hf w

private theorem gate_rule (m : ℕ) (g : Gate) (hg : legal g) :
    rule m (fun w => g.op.eval (g.inputs.map fun i => w.getD i false)) (.inr m, [g]) := by
  refine ⟨by simp [bounded], by simpa, by simp, ?_⟩
  intro w hw
  change (fire w g).getD m false = _
  simp [fire, hw]

private def binOp (e : Bool) : GateOp := if e then .and else .or

private theorem bin_comm (e a b : Bool) :
    (binOp e).eval [a, b] = (binOp e).eval [b, a] := by
  cases e <;> cases a <;> cases b <;> rfl

private def cofactor (e c : Bool) (a : Ref) : Ref := if c = e then a else .inl c

private theorem cofactor_bound {m : ℕ} {a : Ref} (e c : Bool) (ha : bounded m a) :
    bounded m (cofactor e c a) := by
  by_cases h : c = e
  · simpa only [cofactor, ite_eq_left h] using ha
  · rw [cofactor, ite_eq_right h]
    exact trivial

private theorem cofactor_value (e c : Bool) (a : Ref) (w : List Bool) :
    load w (cofactor e c a) = (binOp e).eval [c, load w a] := by
  cases e <;> cases c <;> simp [cofactor, binOp, load, GateOp.eval]

private theorem binary (m : ℕ) (e : Bool) (rs : List Ref) (hlen : rs.length ≤ 2)
    (hr : ∀ r ∈ rs, bounded m r) :
    ∃ P : Plan, rule m (fun w => (binOp e).eval (rs.map (load w))) P ∧
      ((∃ c, Sum.inl c ∈ rs) → P.2.length = 0) := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨d, ds⟩⟩⟩
  · refine ⟨(.inl e, []), pass_rule m (.inl e) trivial _ ?_, fun _ => rfl⟩
    intro w
    cases e <;> rfl
  · refine ⟨(a, []), pass_rule m a (hr a (by simp)) _ ?_, fun _ => rfl⟩
    intro w
    cases e <;> simp [binOp, GateOp.eval]
  · have ha := hr a (by simp)
    have hb := hr b (by simp)
    rcases a with c | i
    · refine ⟨(cofactor e c b, []), pass_rule m _ (cofactor_bound e c hb) _ ?_, fun _ => rfl⟩
      intro w
      exact cofactor_value e c b w
    · rcases b with c | j
      · refine ⟨(cofactor e c (.inr i), []), pass_rule m _ (cofactor_bound e c ha) _ ?_, fun _ => rfl⟩
        intro w
        exact (cofactor_value e c (.inr i) w).trans (bin_comm e c (load w (.inr i)))
      · refine ⟨(.inr m, [⟨binOp e, [i, j]⟩]), gate_rule m _ ?_, by simp⟩
        cases e <;> simp [legal, binOp]
  · simp at hlen

private theorem plan_gate (m : ℕ) (g : Gate) (hg : legal g) (R : ℕ → Ref)
    (hr : ∀ i, bounded m (R i)) :
    ∃ P : Plan, rule m (fun w => g.op.eval ((live g).map fun i => load w (R i))) P ∧
      ((∃ i ∈ live g, ∃ c, R i = Sum.inl c) → P.2.length = 0) := by
  obtain ⟨op, js⟩ := g
  obtain ⟨ho, hlen⟩ := hg
  have bspec (e : Bool) : ∃ P : Plan,
      rule m (fun w => (binOp e).eval (js.map fun i => load w (R i))) P ∧
        ((∃ i ∈ js, ∃ c, R i = Sum.inl c) → P.2.length = 0) := by
    obtain ⟨P, hp, hc⟩ := binary m e (js.map R) (by simpa using hlen) (by
      intro r h
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      exact hr i)
    refine ⟨P, by simpa [List.map_map, Function.comp_def] using hp, ?_⟩
    rintro ⟨i, hi, c, he⟩
    exact hc ⟨c, List.mem_map.mpr ⟨i, hi, he⟩⟩
  have hb : op = .and ∨ op = .or ∨ op = .not := by simpa using ho
  rcases hb with rfl | rfl | rfl
  · exact bspec true
  · exact bspec false
  · cases js with
    | nil => exact ⟨(.inl true, []), pass_rule m (.inl true) trivial _ (fun _ => rfl), fun _ => rfl⟩
    | cons i js =>
      simp only [live, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.mem_singleton, exists_eq_left]
      cases hv : R i with
      | inl c =>
        exact ⟨(.inl (!c), []), pass_rule m (.inl (!c)) trivial _ (fun _ => rfl), fun _ => rfl⟩
      | inr j =>
        refine ⟨(.inr m, [⟨.not, [j]⟩]), ?_, by simp⟩
        exact gate_rule m ⟨.not, [j]⟩ (by simp [legal])

private def tag (A : List Ref) (i : ℕ) : Ref := A.getD i (.inl false)

private def reflects (A : List Ref) (w old : List Bool) : Prop :=
  A.length = old.length ∧ ∀ i, bounded w.length (tag A i) ∧ load w (tag A i) = old.getD i false

private theorem load_run {r : Ref} {w : List Bool} (gs : List Gate) (h : bounded w.length r) :
    bounded (run gs w).length r ∧ load (run gs w) r = load w r := by
  cases r with
  | inl b => exact ⟨trivial, rfl⟩
  | inr i =>
    change i < w.length at h
    exact ⟨by simp [bounded, run_length]; omega, primary gs w i h⟩

private theorem plan_step {A : List Ref} {w old : List Bool} {g : Gate} {P : Plan}
    (ha : reflects A w old)
    (hr : rule w.length (fun v => g.op.eval ((live g).map fun i => load v (tag A i))) P) :
    reflects (A ++ [P.1]) (run P.2 w) (fire old g) := by
  refine ⟨by simp [ha.1, fire], ?_⟩
  have eq : (live g).map (fun i => load w (tag A i)) = (live g).map (fun i => old.getD i false) :=
    List.map_congr_left fun i _ => (ha.2 i).2
  have hv : load (run P.2 w) P.1 = g.op.eval ((live g).map fun i => load w (tag A i)) :=
    hr.2.2.2 w rfl
  rw [eq, live_eval] at hv
  intro i
  simp only [tag, fire, push_lookup, ← ha.1]
  split_ifs with hi
  · exact ⟨by simpa [run_length] using hr.1, hv⟩
  · have h := load_run P.2 (ha.2 i).1
    exact ⟨h.1, h.2.trans (ha.2 i).2⟩

private theorem compile (p : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, legal g)
    (m : ℕ) (A : List Ref) (hp : p < A.length) (hpin : tag A p = .inl false)
    (ha : ∀ i, bounded m (tag A i)) :
    ∃ (B : List Ref) (ds : List Gate), (∀ g ∈ ds, legal g) ∧ ds.length ≤ gs.length ∧
      ((∃ g ∈ gs, p ∈ live g) → ds.length + 1 ≤ gs.length) ∧
      ∀ w old, w.length = m → reflects A w old → reflects B (run ds w) (run gs old) := by
  induction gs generalizing m A with
  | nil => exact ⟨A, [], by simp, by simp, by simp, fun _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨P, hr, hs⟩ := plan_gate m g (ok g (by simp)) (tag A) ha
    let A' := A ++ [P.1]
    have hp' : p < A'.length := by simp [A']; omega
    have hpin' : tag A' p = .inl false := by
      change (A ++ [P.1]).getD p (.inl false) = .inl false
      rw [push_lookup, ite_eq_right (ne_of_lt hp)]
      exact hpin
    have ha' (i : ℕ) : bounded (m + P.2.length) (tag A' i) := by
      simp only [A', tag, push_lookup]
      split_ifs
      · exact hr.1
      · change bounded (m + P.2.length) (tag A i)
        have h := ha i
        cases he : tag A i with
        | inl b => exact trivial
        | inr j =>
          have hj : j < m := by simpa only [he, bounded] using h
          change j < m + P.2.length
          omega
    obtain ⟨B, ds, hleg, hsz, hsave, heval⟩ := ih
      (fun k hk => ok k (List.mem_cons_of_mem _ hk)) (m + P.2.length) A' hp' hpin' ha'
    refine ⟨B, P.2 ++ ds, ?_, ?_, ?_, ?_⟩
    · intro h hh
      rcases List.mem_append.mp hh with hP | hd
      · exact hr.2.1 h hP
      · exact hleg h hd
    · have := hr.2.2.1
      simp only [List.length_append, List.length_cons]
      omega
    · rintro ⟨k, hk, hkp⟩
      simp only [List.length_append, List.length_cons]
      rcases List.mem_cons.mp hk with rfl | hk
      · have := hs ⟨p, hkp, false, hpin⟩
        omega
      · have := hsave ⟨k, hk, hkp⟩
        have := hr.2.2.1
        omega
    · intro w old hw hwold
      have hr' := hr
      rw [← hw] at hr'
      have q := plan_step hwold hr'
      simpa only [run, List.foldl_append, List.foldl_cons] using
        heval (run P.2 w) (fire old g) (by rw [run_length, hw]) q

private theorem input_read {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private def initial {n : ℕ} (p : Fin n) : List Ref :=
  List.ofFn (fun j : Fin n => if j = p then .inl false else .inr j.val)

private theorem tag_initial {n : ℕ} (p : Fin n) (i : ℕ) : tag (initial p) i =
    if h : i < n then (if (⟨i, h⟩ : Fin n) = p then .inl false else .inr i) else .inl false := by
  unfold tag initial
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rename_i h
    rw [List.getD_eq_default _ _ (by simp; omega)]

private theorem init_reflects {n : ℕ} (p : Fin n) (x : Fin n → Bool) :
    reflects (initial p) (List.ofFn x) (List.ofFn (Function.update x p false)) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  rw [tag_initial]
  by_cases hi : i < n
  · rw [dite_eq_left hi, input_read _ i hi]
    by_cases hp : (⟨i, hi⟩ : Fin n) = p
    · simp [hp, bounded, load]
    · simp [hp, hi, bounded, load, Function.update_of_ne]
  · rw [dite_eq_right hi, List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private theorem once {n s : ℕ} {f : (Fin n → Bool) → Bool} (p : Fin n)
    (hf : HasCircuitSize n f s)
    (hdep : ∃ x, f (Function.update x p false) ≠ f (Function.update x p true))
    (hnc : ∃ a b, f (Function.update a p false) ≠ f (Function.update b p false)) :
    ∃ t : ℕ, t + 1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p false)) t := by
  obtain ⟨C, hok, hsz, hC⟩ := hf
  have ho : C.output ≠ p.val := by
    intro he
    obtain ⟨a, b, hab⟩ := hnc
    have pinned (x : Fin n → Bool) : f (Function.update x p false) = false := by
      rw [← hC]
      change (run C.gates (List.ofFn (Function.update x p false))).getD C.output false = false
      rw [he, primary _ _ _ (by simp), input_read _ _ p.isLt]
      simp
    exact hab ((pinned a).trans (pinned b).symm)
  have hread : ∃ g ∈ C.gates, p.val ∈ live g := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := hdep
    apply hx
    rw [← hC, ← hC]
    apply unread p.val C.gates h _ _ (by simp) _ C.output ho
    intro i hi
    by_cases hlt : i < n
    · have hne : (⟨i, hlt⟩ : Fin n) ≠ p := fun e => hi (congrArg Fin.val e)
      rw [input_read _ i hlt, input_read _ i hlt, Function.update_of_ne hne, Function.update_of_ne hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hi := init_reflects p (fun _ => false)
  obtain ⟨B, ds, hd, _, hc, hr⟩ := compile p.val C.gates hok n (initial p)
    (by simp [initial]) (by simp [tag_initial, p.isLt]) (fun i => by simpa using (hi.2 i).1)
  have bound := hc hread
  have hs : C.gates.length ≤ s := hsz
  have ev (x : Fin n → Bool) : load (run ds (List.ofFn x)) (tag B C.output) =
      f (Function.update x p false) := by
    rw [← hC]
    exact (hr _ _ (by simp) (init_reflects p x)).2 C.output |>.2
  cases e : tag B C.output with
  | inl c =>
    obtain ⟨a, b, hab⟩ := hnc
    have ea : f (Function.update a p false) = c := by simpa only [e, load] using (ev a).symm
    have eb : c = f (Function.update b p false) := by simpa only [e, load] using ev b
    exact (hab (ea.trans eb)).elim
  | inr j =>
    refine ⟨ds.length, by omega, ⟨⟨ds, j⟩, hd, le_rfl, fun x => ?_⟩⟩
    change (run ds (List.ofFn x)).getD j false = f (Function.update x p false)
    simpa only [e, load] using ev x

private theorem strip_or {n s : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n)
    (h0 : ∃ x, f x = false) (h1 : ∃ x, f x = true)
    (hind : ∀ x b, f (Function.update x p b) = f x)
    (hc : HasCircuitSize n (fun x => f x || x p) s) :
    ∃ t, t + 1 ≤ s ∧ HasCircuitSize n f t := by
  obtain ⟨z, hz⟩ := h0
  obtain ⟨a, ha⟩ := h1
  have fixed (x : Fin n → Bool) : (f (Function.update x p false) || Function.update x p false p) = f x := by
    simp [hind]
  have hdep : (f (Function.update z p false) || Function.update z p false p) ≠
      (f (Function.update z p true) || Function.update z p true p) := by
    simp [hind, hz]
  have hnc : (f (Function.update z p false) || Function.update z p false p) ≠
      (f (Function.update a p false) || Function.update a p false p) := by
    rw [fixed, fixed, hz, ha]
    decide
  obtain ⟨t, ht, D, hD, hsize, he⟩ := once p hc ⟨z, hdep⟩ ⟨z, a, hnc⟩
  exact ⟨t, ht, D, hD, hsize, fun x => (he x).trans (fixed x)⟩

end PEqualNP.Outside.L_meta_19118

theorem PEqualNP.Outside.L_meta_19118 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (u w : Fin n) (s : ℕ), u ≠ w → (∃ x : Fin n → Bool, f x = false) → (∃ x : Fin n → Bool, f x = true) → (∀ x : Fin n → Bool, ∀ b : Bool, f (Function.update x u b) = f x) → (∀ x : Fin n → Bool, ∀ b : Bool, f (Function.update x w b) = f x) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f x || x u || x w) s → ∃ t : ℕ, t + 2 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  intro n f u w s huw h0 h1 hu hw hc
  let g : (Fin n → Bool) → Bool := fun x => f x || x w
  have hg0 : ∃ x, g x = false := by
    obtain ⟨x, h⟩ := h0
    exact ⟨Function.update x w false, by simp [g, hw, h]⟩
  have hg1 : ∃ x, g x = true := by
    obtain ⟨x, h⟩ := h1
    exact ⟨x, by simp [g, h]⟩
  have hgu (x : Fin n → Bool) (b : Bool) : g (Function.update x u b) = g x := by
    simp [g, hu, Function.update_of_ne (Ne.symm huw)]
  have hg : HasCircuitSize n (fun x => g x || x u) s := by
    convert hc using 1
    funext x
    unfold g
    cases f x <;> cases x u <;> cases x w <;> rfl
  obtain ⟨s', hs', h'⟩ := PEqualNP.Outside.L_meta_19118.strip_or g u hg0 hg1 hgu hg
  obtain ⟨t, ht, h⟩ := PEqualNP.Outside.L_meta_19118.strip_or f w h0 h1 hw h'
  exact ⟨t, by omega, h⟩
