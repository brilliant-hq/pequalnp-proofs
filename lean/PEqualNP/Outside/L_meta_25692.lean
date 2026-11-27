import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_376
import PEqualNP.Outside.L_meta_5506

namespace PEqualNP.Outside.L_meta_25692.Local.Restriction

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_25692.Local.Restriction

namespace PEqualNP.Outside.L_meta_25692.Local.WireEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

end PEqualNP.Outside.L_meta_25692.Local.WireEval

namespace PEqualNP.Outside.L_meta_25692.Local.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_25692.Local.Restriction PEqualNP.Outside.L_meta_25692.Local.WireEval

def pull {n m : ℕ} (source : Fin n → Option (Fin m)) (y : Fin m → Bool) (i : Fin n) : Bool :=
  ((source i).map y).getD false

def code {n m : ℕ} (source : Fin n → Option (Fin m)) (i : Fin n) : Stat :=
  match source i with
  | none => Sum.inl false
  | some j => Sum.inr j.val

theorem deleteInput {n m : ℕ} (C : Circuit) (mono : Monotone2 C) (source : Fin n → Option (Fin m))
    (p : Fin n) (removed : source p = none) (reader : ∃ g ∈ C.gates, p.val ∈ g.inputs)
    (rejects : ∃ y, circuitFun n C (pull source y) = false) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun m D = (fun y => circuitFun n C (pull source y)) ∧
      D.size < C.size := by
  let start : List Stat × List Gate := (List.ofFn (code source),[])
  let finish := elim m C.gates start
  have seed (y : Fin m → Bool) : Inv m (List.ofFn y) (List.ofFn (pull source y)) start := by
    refine ⟨by simp [start],?_⟩
    intro i
    by_cases inside : i < n
    · let t : Fin n := ⟨i,inside⟩
      change ((List.ofFn (code source)).getD t.val _).Valid (m+0) ∧
        ((List.ofFn (code source)).getD t.val _).val (List.ofFn y) = (List.ofFn (pull source y)).getD t.val _
      rw [getD_ofFn',getD_ofFn']
      cases h : source t with
      | none => simp [code,h,pull,Stat.Valid,Stat.val]
      | some u => simp [code,h,pull,Stat.Valid,Stat.val,u.isLt]
    · have a : start.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [start]; omega)
      have b : (List.ofFn (pull source y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [a,b]; exact ⟨trivial,rfl⟩
  have known : start.1.getD p.val (Sum.inl false) = Sum.inl false := by
    change (List.ofFn (code source)).getD p.val _ = _
    rw [getD_ofFn']; simp [code,removed]
  have limit := elim_count m p.val C.gates start mono (by simp [start]) ⟨false,known⟩
  have cost : finish.2.length + C.gates.countP (fun g => decide (p.val ∈ g.inputs)) ≤ C.size := by
    simpa [start,finish,Circuit.size] using limit
  obtain ⟨g,hg,read⟩ := reader
  have charge : 0 < C.gates.countP (fun h => decide (p.val ∈ h.inputs)) := by
    by_contra! zero
    exact (List.countP_eq_zero.mp (Nat.le_zero.mp zero) g hg) (decide_eq_true read)
  have short : finish.2.length < C.size := by omega
  let out := finish.1.getD C.output (Sum.inl false)
  have eval (y : Fin m → Bool) :
      out.val (wiresFrom finish.2 (List.ofFn y)) = circuitFun n C (pull source y) :=
    ((inv_elim m (List.ofFn y) (by simp) C.gates _ start mono (seed y)).2 C.output).2
  have legal : ∀ h ∈ finish.2, Ok h := elim_ok m C.gates start (by simp [start])
  cases result : out with
  | inr i =>
    refine ⟨⟨finish.2,i⟩,legal,?_,short⟩
    funext y
    have h := eval y
    rw [result] at h
    exact h
  | inl b =>
    have const (y : Fin m → Bool) : b = circuitFun n C (pull source y) := by
      have h := eval y
      rw [result] at h
      exact h
    obtain ⟨y,hy⟩ := rejects
    have off : b = false := (const y).trans hy
    refine ⟨⟨[],m⟩,by intro h mem; simp at mem,?_,by change 0 < C.size; omega⟩
    funext z
    change (List.ofFn z).getD m false = _
    rw [List.getD_eq_default _ _ (by simp)]
    exact off.symm.trans (const z)

theorem read_of_separation {n : ℕ} (C : Circuit) (mono : Monotone2 C) (p : Fin n)
    (out : C.output ≠ p.val) (x y : Fin n → Bool)
    (ordered : ∀ t, t ≠ p → x t = true → y t = true)
    (on : circuitFun n C x = true) (off : circuitFun n C y = false) :
    ∃ g ∈ C.gates, p.val ∈ g.inputs := by
  by_contra! unread
  have wires (w : ℕ) : w ≠ p.val → val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ne
      by_cases raw : w < n
      · let t : Fin n := ⟨w,raw⟩
        rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
        simpa [t,raw] using ordered t (fun eq => ne (congrArg Fin.val eq))
      by_cases past : n+C.gates.length ≤ w
      · rw [val_ge List.length_ofFn past]; simp
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have valid : k < C.gates.length := by omega
      rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn valid]
      apply opMono_imp _ (mono_ops mono k valid)
      intro i hi
      by_cases earlier : i < n+k
      · simp only [earlier,ite_true]
        exact ih i earlier (fun eq => unread _ (gateAt_mem valid) (eq ▸ hi))
      · simp [earlier]
  have contradiction := wires C.output out on
  change circuitFun n C y = true at contradiction
  simp [off] at contradiction
end PEqualNP.Outside.L_meta_25692.Local.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25692.Local

def mask {n m : ℕ} (t : ℕ) (u : Fin n) (v : Fin m) : Bool :=
  t.testBit (m * u.val + v.val)

def cell {n m : ℕ} (u : Fin n) (v : Fin m) (w : Fin (n + m)) : Bool :=
  (oneEach u v).getD w.val false

theorem cell_toList {n m : ℕ} (u : Fin n) (v : Fin m) :
    List.ofFn (cell u v) = oneEach u v := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro i hi hj
    simp [cell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

def dropWire {n m : ℕ} (p : ℕ) (i : Fin n) : Option (Fin m) :=
  let j := if i.val < p then i.val else i.val - 1
  if i.val = p then none else if h : j < m then some ⟨j, h⟩ else none

theorem smaller {n m n' m' : ℕ} (t t' : ℕ)
    (row : Fin n' → Fin n) (col : Fin m' → Fin m) (p : Fin (n + m))
    (a b c : Fin n × Fin m)
    (cert : mask t a.1 a.2 = true ∧ mask t b.1 b.2 = false ∧
      mask t c.1 c.2 = false ∧ cell c.1 c.2 p = true ∧
      (∀ i, i ≠ p → cell a.1 a.2 i = true → cell b.1 b.2 i = true) ∧
      (∀ u v, List.ofFn (DeleteInput.pull (dropWire (n := n+m) (m := n'+m') p.val) (cell u v)) =
        oneEach (row u) (col v)) ∧
      (∀ u v, mask t (row u) (col v) = mask t' u v) ∧
      (∃ (u : Fin n') (v : Fin m'), mask t' u v = false)) {k : ℕ} :
    RepSizeAtMost (@mask n m t) (k + 1) → RepSizeAtMost (@mask n' m' t') k := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨ha, hb, hc, cp, ordered, embed, table, u0, v0, off⟩ := cert
  have evalCell (u : Fin n) (v : Fin m) : circuitFun (n+m) C (cell u v) = mask t u v := by
    change C.eval (List.ofFn _) = _
    rw [cell_toList]
    exact hr u v
  have out : C.output ≠ p.val := by
    intro eq
    have h := (hr c.1 c.2).trans hc
    change WireEval.val C (oneEach c.1 c.2) C.output = false at h
    rw [eq, WireEval.val_input (n := n+m) (by simp [oneEach]) p.isLt] at h
    exact Bool.noConfusion (cp.symm.trans h)
  have reads := DeleteInput.read_of_separation C hm p out (cell a.1 a.2) (cell b.1 b.2)
    ordered ((evalCell _ _).trans ha) ((evalCell _ _).trans hb)
  let src := dropWire (n := n+m) (m := n'+m') p.val
  have compute (u : Fin n') (v : Fin m') :
      circuitFun (n+m) C (DeleteInput.pull src (cell u v)) = mask t' u v := by
    change C.eval (List.ofFn (DeleteInput.pull _ _)) = _
    rw [embed u v]
    exact (hr _ _).trans (table u v)
  obtain ⟨D, legal, eqv, size⟩ := DeleteInput.deleteInput C hm src p
    (by simp [src, dropWire]) reads ⟨cell u0 v0, (compute u0 v0).trans off⟩
  refine ⟨D, legal, by omega, ?_⟩
  intro u v
  rw [← cell_toList u v]
  change circuitFun (n'+m') D (cell u v) = _
  rw [eqv]
  exact compute u v

end PEqualNP.Outside.L_meta_25692.Local

namespace PEqualNP.Outside.L_meta_25692.Reindex

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem run (φ : ℕ → ℕ) :
    ∀ (gs : List Gate) (W W' : List Bool),
      (∀ k, k < gs.length → ∀ i, (φ i = W'.length + k ↔ i = W.length + k)) →
      (∀ i, W.getD i false = W'.getD (φ i) false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD i false
        = ((gs.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate)).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD (φ i) false := by
  intro gs
  induction gs with
  | nil => intro W W' _ h; simpa using h
  | cons g gs ih =>
    intro W W' hφ h
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · intro k hk i
      have := hφ (k + 1) (by simp; omega) i
      simp only [List.length_append, List.length_singleton]
      constructor
      · intro hi; exact by have := this.1 (by omega); omega
      · intro hi; exact by have := this.2 (by omega); omega
    · intro i
      rw [getD_snoc, getD_snoc]
      have hb : g.op.eval (g.inputs.map fun i => W.getD i false)
          = g.op.eval ((g.inputs.map φ).map fun i => W'.getD i false) := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro j _; exact h j
      have h0 := hφ 0 (by simp) i
      simp only [Nat.add_zero] at h0
      by_cases hi : i = W.length
      · rw [if_pos hi, if_pos (h0.2 hi)]; exact hb
      · rw [if_neg hi, if_neg (fun h' => hi (h0.1 h'))]; exact h i

theorem main (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (he : Function.Injective e) (hf : Function.Injective f) (hA : RepSizeAtMost A s) :
    RepSizeAtMost (fun u v => A (e u) (f v)) s := by
  classical
  obtain ⟨C, hmono, hsize, hrep⟩ := hA
  set L := C.gates.length with hL
  set BIG := m + m' + L with hBIG
  let φ : ℕ → ℕ := fun i =>
    if h1 : i < n then
      (if h : ∃ u : Fin m, (e u : ℕ) = i then ((Classical.choose h : Fin m) : ℕ) else BIG)
    else if h2 : i < n + n' then
      (if h : ∃ v : Fin m', (f v : ℕ) = i - n then m + ((Classical.choose h : Fin m') : ℕ) else BIG)
    else m + m' + (i - (n + n'))
  refine ⟨⟨C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate), φ C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hmono g0 hg0
    simpa using this
  · simpa [Circuit.size] using hsize
  · intro u v
    have key := run φ C.gates (oneEach (e u) (f v)) (oneEach u v) ?_ ?_ C.output
    · have h1 := hrep (e u) (f v)
      simp only [Circuit.eval, Circuit.wires] at h1 ⊢
      rw [← h1, key]
    · intro k hk i
      simp only [oneEach, List.length_append, List.length_ofFn]
      simp only [φ]
      constructor
      · intro hi
        split_ifs at hi with h1 h3 h2 h4
        · have := (Classical.choose h3).isLt; omega
        · omega
        · have := (Classical.choose h4).isLt; omega
        · omega
        · omega
      · intro hi
        rw [dif_neg (by omega), dif_neg (by omega)]; omega
    · intro i
      simp only [φ]
      by_cases h1 : i < n
      · rw [dif_pos h1]
        have hx : (oneEach (e u) (f v)).getD i false = decide (i = (e u : ℕ)) := by
          simp only [oneEach]
          rw [List.getD_append _ _ _ _ (by simpa using h1)]
          simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
        rw [hx]
        split_ifs with h3
        · have hc := Classical.choose_spec h3
          have hlt := (Classical.choose h3).isLt
          have hy : (oneEach u v).getD ((Classical.choose h3 : Fin _) : ℕ) false
              = decide (((Classical.choose h3 : Fin _) : ℕ) = (u : ℕ)) := by
            simp only [oneEach]
            rw [List.getD_append _ _ _ _ (by simpa using hlt)]
            simp [List.getD_eq_getElem?_getD, hlt, Fin.ext_iff]
          rw [hy]
          apply decide_eq_decide.2
          constructor
          · intro h; exact congrArg Fin.val (he (Fin.ext (hc.trans h)))
          · intro h; rw [← hc, show Classical.choose h3 = u from Fin.ext h]
        · rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]
          simp only [decide_eq_false_iff_not]
          intro h; exact h3 ⟨u, h.symm⟩
      · rw [dif_neg h1]
        by_cases h2 : i < n + n'
        · rw [dif_pos h2]
          have hx : (oneEach (e u) (f v)).getD i false = decide (i - n = (f v : ℕ)) := by
            simp only [oneEach]
            rw [List.getD_append_right _ _ _ _ (by simp; omega)]
            simp only [List.length_ofFn]
            simp [List.getD_eq_getElem?_getD, show i - n < n' by omega, Fin.ext_iff]
          rw [hx]
          split_ifs with h3
          · have hc := Classical.choose_spec h3
            have hlt := (Classical.choose h3).isLt
            have hy : (oneEach u v).getD (m + ((Classical.choose h3 : Fin _) : ℕ)) false
                = decide (((Classical.choose h3 : Fin _) : ℕ) = (v : ℕ)) := by
              simp only [oneEach]
              rw [List.getD_append_right _ _ _ _ (by simp)]
              simp only [List.length_ofFn, Nat.add_sub_cancel_left]
              simp [List.getD_eq_getElem?_getD, hlt, Fin.ext_iff]
            rw [hy]
            apply decide_eq_decide.2
            constructor
            · intro h; exact congrArg Fin.val (hf (Fin.ext (hc.trans h)))
            · intro h; rw [← hc, show Classical.choose h3 = v from Fin.ext h]
          · rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]
            simp only [decide_eq_false_iff_not]
            intro h; exact h3 ⟨v, h.symm⟩
        · rw [dif_neg h2]
          rw [List.getD_eq_default _ _ (by simp [oneEach] <;> omega),
            List.getD_eq_default _ _ (by simp [oneEach] <;> omega)]

theorem Reindex :
    ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s :=
  PEqualNP.Outside.L_meta_25692.Reindex.main
end PEqualNP.Outside.L_meta_25692.Reindex

namespace PEqualNP.Outside.L_meta_25692.Local2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_5506

abbrev W := BitVec 96

def bit3 (k : Fin 96) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 96) :
    (w.map (bit3 k)).getD i false = bit3 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit3]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 96 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

def step3 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step3 (w.map (bit3 k)) g = (w ++ [z]).map (bit3 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
      rcases hop with rfl | rfl
      · exact ⟨BitVec.allOnes 96, by simp [possible], by simp [step3, GateOp.eval, bit3]; decide⟩
      · exact ⟨0, by simp [possible], by simp [step3, GateOp.eval, bit3]⟩
  | cons i tail =>
      cases tail with
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, atom (mem i),
            by simp only [step3, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
        · exact ⟨_, atom (mem i),
            by simp only [step3, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      | cons j tail =>
        cases tail with
        | cons => simp at hlen
        | nil =>
          rcases hop with rfl | rfl
          · exact ⟨_, (pair (mem i) (mem j)).1,
              by simp only [step3, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit3]⟩
          · exact ⟨_, (pair (mem i) (mem j)).2,
              by simp only [step3, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit3]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 96 ∨ u ∈ available

private theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 96 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 96 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 96 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step3 (w.map (bit3 k))).getD out false = bit3 k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
      have hval : w.getD out 0 = goal := by
        apply BitVec.eq_of_getElem_eq
        intro i hi
        simpa only [List.foldl_nil, read_bit, bit3] using he ⟨i, hi⟩
      have hr := read_wire w out
      rw [hval] at hr
      rcases hr with hz | hm
      · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
      · rcases hw _ hm with h | h | h
        · exact False.elim ((by decide : goal ≠ (0 : W)) h)
        · exact False.elim ((by decide : goal ≠ BitVec.allOnes 96) h)
        · exact h
  | cons g gs ih =>
      obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
      have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
      have he' : ∀ k, (gs.foldl step3 ((w ++ [z]).map (bit3 k))).getD out false = bit3 k goal := by
        intro k; simpa only [List.foldl_cons, hstep] using he k
      have appendOK (h : z = 0 ∨ z = BitVec.allOnes 96 ∨ z ∈ av) : represents av (w ++ [z]) := by
        intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · exact hw _ old
        · have eq : u = z := List.mem_singleton.mp fresh
          exact eq ▸ h
      rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
      · exact Or.inl (fn av (appendOK (.inl h)) he')
      · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
      · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
      · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
        · simp_all
end PEqualNP.Outside.L_meta_25692.Local2

open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25692.Local
open PEqualNP.Outside.L_meta_25692.Local.DeleteInput
open PEqualNP.Outside.L_meta_5506

theorem PEqualNP.Outside.L_meta_25692 : (¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (268222 : ℕ).testBit (6 * u.val + v.val)) 9)) := by
  intro h9
  have h1 : RepSizeAtMost (fun u : Fin 4 => fun v : Fin 5 => (34270 : ℕ).testBit (5 * u.val + v.val)) 8 := by
    exact smaller (n := 4) (m := 6) (n' := 4) (m' := 5) (t := 268222) (t' := 34270)
      (row := fun i => i) (col := (2 : Fin 6).succAbove) (p := ⟨6, by decide⟩)
      (a := (⟨1, by decide⟩, ⟨2, by decide⟩))
      (b := (⟨1, by decide⟩, ⟨5, by decide⟩))
      (c := (⟨2, by decide⟩, ⟨2, by decide⟩))
      (by decide +kernel) h9
  have h2 : RepSizeAtMost (fun u : Fin 4 => fun v : Fin 4 => (4462 : ℕ).testBit (4 * u.val + v.val)) 7 := by
    exact smaller (n := 4) (m := 5) (n' := 4) (m' := 4) (t := 34270) (t' := 4462)
      (row := fun i => i) (col := (2 : Fin 5).succAbove) (p := ⟨6, by decide⟩)
      (a := (⟨0, by decide⟩, ⟨2, by decide⟩))
      (b := (⟨0, by decide⟩, ⟨0, by decide⟩))
      (c := (⟨2, by decide⟩, ⟨2, by decide⟩))
      (by decide +kernel) h1
  have h3 : RepSizeAtMost (fun u : Fin 4 => fun v : Fin 3 => (598 : ℕ).testBit (3 * u.val + v.val)) 6 := by
    exact smaller (n := 4) (m := 4) (n' := 4) (m' := 3) (t := 4462) (t' := 598)
      (row := fun i => i) (col := (2 : Fin 4).succAbove) (p := ⟨6, by decide⟩)
      (a := (⟨0, by decide⟩, ⟨2, by decide⟩))
      (b := (⟨0, by decide⟩, ⟨0, by decide⟩))
      (c := (⟨2, by decide⟩, ⟨2, by decide⟩))
      (by decide +kernel) h2
  have h4 : RepSizeAtMost (fun u : Fin 3 => fun v : Fin 3 => (86 : ℕ).testBit (3 * u.val + v.val)) 5 := by
    exact smaller (n := 4) (m := 3) (n' := 3) (m' := 3) (t := 598) (t' := 86)
      (row := (3 : Fin 4).succAbove) (col := fun i => i) (p := ⟨3, by decide⟩)
      (a := (⟨3, by decide⟩, ⟨0, by decide⟩))
      (b := (⟨0, by decide⟩, ⟨0, by decide⟩))
      (c := (⟨3, by decide⟩, ⟨1, by decide⟩))
      (by decide +kernel) h3
  have h5 : RepSizeAtMost (fun u : Fin 3 => fun v : Fin 3 => (85 : ℕ).testBit (3 * u.val + v.val)) 5 := by
    have hh := PEqualNP.Outside.L_meta_25692.Reindex.Reindex 3 3 3 3 5
      (fun u : Fin 3 => fun v : Fin 3 => (86 : ℕ).testBit (3 * u.val + v.val))
      (fun i : Fin 3 => ![0, 2, 1] i) (fun i : Fin 3 => ![1, 0, 2] i)
      (by decide) (by decide) h4
    convert hh using 1
    ext u v
    fin_cases u <;> fin_cases v <;> decide

  let A3 : Fin 3 → Fin 3 → Bool := fun u v => (85 : ℕ).testBit (3 * u.val + v.val)
  let negL3 : List (Fin 3 × Fin 3) := [(0,1), (1,0), (1,2), (2,1), (2,2)]
  let posL3 : List (Fin 3 × Fin 3) := [(0,0), (0,2), (1,1), (2,0)]
  let samp3 (k : Fin 96) : Fin 3 × Fin 3 :=
    if k.val < 10 then (0,1) else if k.val < 20 then (1,0)
    else if k.val < 30 then (1,2) else if k.val < 39 then (2,1)
    else if k.val < 48 then (2,2) else posL3.getD ((k.val - 48) / 12) (0,0)
  let rawInputs3 : List W :=
    [0xffffff0000000003ff, 0xfff00000000003ffffc00, 0xfff000000000ffffc0000000,
     0xfff000000fff0000000ffc00, 0xfff000000007fc00003ff, 0xfff000ff803ff00000]
  let goal3 : W := goal
  have input_rows3 : ∀ k : Fin 96, rawInputs3.map (PEqualNP.Outside.L_meta_25692.Local2.bit3 k) = oneEach (samp3 k).1 (samp3 k).2 := by
    decide +kernel
  have goal_rows3 : ∀ k : Fin 96, PEqualNP.Outside.L_meta_25692.Local2.bit3 k goal3 = A3 (samp3 k).1 (samp3 k).2 := by
    decide +kernel
  have rows_eval3 (C : Circuit) (hr : Represents A3 C) (k : Fin 96) :
      (C.gates.foldl PEqualNP.Outside.L_meta_25692.Local2.step3 (rawInputs3.map (PEqualNP.Outside.L_meta_25692.Local2.bit3 k))).getD C.output false =
        PEqualNP.Outside.L_meta_25692.Local2.bit3 k goal3 := by
    rw [input_rows3 k, goal_rows3 k]
    exact hr (samp3 k).1 (samp3 k).2
  have initial_rep3 : PEqualNP.Outside.L_meta_5506.represents rawInputs3.toFinset rawInputs3 := by
    intro u hu
    exact .inr (.inr (List.mem_toFinset.mpr hu))
  have inputs3_nodup : rawInputs3.Nodup := by decide +kernel
  have all_front3 : rawInputs3.sublists.all
      (fun l => decide (6 < l.length) || !(optimized 5 (6 - l.length) l)) = true := by
    decide +kernel
  have no_small3 (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 5) (hr : Represents A3 C) : False := by
    have hlegal : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_25692.Local2.legal g := by
      intro g hg
      simpa [PEqualNP.Outside.L_meta_25692.Local2.legal] using hm g hg
    obtain ⟨S, hsub, hl⟩ := compress (PEqualNP.Outside.L_meta_25692.Local2.compile C.gates C.output hlegal
      rawInputs3 rawInputs3.toFinset initial_rep3 (rows_eval3 C hr))
    have hl5 : PEqualNP.Outside.L_meta_5506.live PEqualNP.Outside.L_meta_5506.basicOps PEqualNP.Outside.L_meta_5506.goal 5 S := extend_live hs hl
    let l := rawInputs3.filter (fun w => decide (w ∈ S))
    have hlS : l.toFinset = S := by
      ext v
      simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
    have hnd : l.Nodup := inputs3_nodup.filter _
    have hcard := PEqualNP.Outside.L_meta_5506.live_card hl5
    rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
    have hsearch := PEqualNP.Outside.L_meta_5506.optimized_complete 5 l (6 - l.length) hnd (by omega) (hlS ▸ hl5)
    have hmem : l ∈ rawInputs3.sublists := List.mem_sublists.mpr List.filter_sublist
    have hrow := List.all_eq_true.mp all_front3 l hmem
    have h4 : decide (6 < l.length) = false := by simp; omega
    rw [h4, hsearch] at hrow
    exact Bool.noConfusion hrow
  rcases h5 with ⟨C, hm, hs, hr⟩
  exact no_small3 C hm hs (by simpa [A3] using hr)
