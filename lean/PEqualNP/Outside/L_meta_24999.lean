import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24999_aux

namespace MonoReduction24999

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
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
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

private theorem drops_emptyOR (N : ℕ) (gs : List Gate)
    (present : (⟨.or,[]⟩ : Gate) ∈ gs) : (elim N gs (idStats N, [])).2.length < gs.length := by
  obtain ⟨p,atPos⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨pre,post,rfl,plen⟩ := split_at gs p _ atPos
  let init := elim N pre (idStats N, [])
  have lePre : init.2.length ≤ pre.length := by simpa [init] using elim_len N pre (idStats N,[])
  have lePost := elim_len N post (elimStep N init ⟨.or,[]⟩)
  have noEmit : (elimStep N init ⟨.or,[]⟩).2.length = init.2.length := by
    simp [elimStep,simplify,simpOr]
  rw [elim_append,elim_cons]
  change (elim N post (elimStep N init ⟨.or,[]⟩)).2.length < (pre ++ ⟨.or,[]⟩ :: post).length
  simp only [List.length_append,List.length_cons]
  omega

private theorem gateAt_some {C : Circuit} {j : ℕ} {g : Gate}
    (h : C.gates[j]? = some g) : gateAt C j = g := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ (List.getElem?_eq_some_iff.mp h).1]
  exact (List.getElem?_eq_some_iff.mp h).2

private theorem atGate {C : Circuit} {j : ℕ} (hj : j < C.size) :
    C.gates[j]? = some (gateAt C j) := by
  have lt : j < C.gates.length := hj
  have get : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem lt
  rw [gateAt_some get]
  exact get

private theorem eval_gate {N : ℕ} {C : Circuit} (back : ReadsBack N C)
    (x : List Bool) (len : x.length = N) {j : ℕ} (lt : j < C.size) :
    let V := fun w => (C.wires x).getD w false
    V (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map V) := by
  dsimp only
  let g := gateAt C j
  obtain ⟨pre,post,eq,plen⟩ := split_at C.gates j g (atGate lt)
  let W := wiresFrom pre x
  let b := g.op.eval (g.inputs.map fun w => W.getD w false)
  have wlen : W.length = N+j := by rw [length_wiresFrom, len, plen]
  have expand : C.wires x = wiresFrom post (W ++ [b]) := by
    rw [wires_eq,eq,wiresFrom_append]
    rfl
  have advance : (C.wires x).getD (N+j) false = b := by
    rw [expand,getD_wiresFrom _ _ _ (by simp [wlen]),getD_snoc_len _ _ _ _ wlen]
  rw [advance]
  change g.op.eval (g.inputs.map (fun w => W.getD w false)) =
    g.op.eval (g.inputs.map (fun w => (C.wires x).getD w false))
  congr 1
  apply List.map_congr_left
  intro w hw
  have early := back j lt w hw
  have beforeW : w < W.length := by rw [wlen]; exact early
  have beforePost : w < (W ++ [b]).length := by simpa [wlen] using Nat.lt_succ_of_lt early
  rw [expand, getD_wiresFrom post (W ++ [b]) w beforePost, List.getD_append _ _ _ _ beforeW]

private theorem read_count_le (C : Circuit) {j w : ℕ} (jlt : j < C.size) :
    (gateAt C j).inputs.count w ≤ readsIn C (Finset.range C.size) w := by
  unfold readsIn
  exact Finset.single_le_sum (f := fun a => (gateAt C a).inputs.count w)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr jlt)

private theorem changed_operand {N : ℕ} {C : Circuit} (back : ReadsBack N C)
    {V U : ℕ → Bool} {j : ℕ} (lt : j < C.size)
    (orig : V (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map V))
    (new : U (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map U))
    (diff : V (N+j) ≠ U (N+j)) :
      ∃ w ∈ (gateAt C j).inputs, w < N+j ∧ V w ≠ U w := by
  by_contra no
  apply diff
  rw [orig,new]
  congr 1
  apply List.map_congr_left
  intro w hw
  by_contra diff
  exact no ⟨w,hw,back j lt w hw,diff⟩

private def emptyOR : Gate := ⟨.or,[]⟩
private def forced (C : Circuit) (src : ℕ) : Circuit := ⟨C.gates.set src emptyOR,C.output⟩

private theorem forced_size (C : Circuit) (src : ℕ) : (forced C src).size = C.size := by
  simp [forced,Circuit.size]

private theorem forced_here {C : Circuit} {src : ℕ} (lt : src < C.size) :
    gateAt (forced C src) src = emptyOR :=
  gateAt_some (List.getElem?_set_self (l := C.gates) (a := emptyOR) lt)

private theorem forced_else {C : Circuit} {src j : ℕ} (lt : j < C.size) (different : j ≠ src) :
    gateAt (forced C src) j = gateAt C j := by
  apply gateAt_some
  change (C.gates.set src emptyOR)[j]? = _
  rw [List.getElem?_set_ne (Ne.symm different)]
  exact atGate lt

private theorem forced_back {N : ℕ} {C : Circuit} {src : ℕ}
    (back : ReadsBack N C) : ReadsBack N (forced C src) := by
  intro j hlt w reads
  have sizeEq := forced_size C src
  have lt : j < C.size := by change j < (forced C src).size at hlt; simpa [sizeEq] using hlt
  by_cases same : j = src
  · subst j
    simp [forced_here lt,emptyOR] at reads
  · exact back j lt w (by rwa [forced_else lt same] at reads)

private theorem forced_mono {C : Circuit} {src : ℕ} (fan : Monotone2 C) : Monotone2 (forced C src) := by
  intro g hg
  obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp hg
  have lt : j < C.size := by
    have fromGet := (List.getElem?_eq_some_iff.mp get).1
    change j < (forced C src).size at fromGet
    rwa [forced_size] at fromGet
  rw [← gateAt_some get]
  by_cases same : j = src
  · subst j
    simp [forced_here lt,emptyOR]
  · rw [forced_else lt same]
    exact fan _ (List.mem_iff_getElem?.mpr ⟨j,atGate lt⟩)

private theorem clean_back {N : ℕ} {C : Circuit} (h : CleanL N C.gates) : ReadsBack N C := by
  intro p hp w used
  exact (h p _ (atGate hp)).lt _ used

private theorem no_reader_iff {C : Circuit} {w : ℕ} :
    readsIn C (Finset.range C.size) w = 0 ↔ ∀ g ∈ C.gates, w ∉ g.inputs := by
  constructor
  · intro zero g hm hi
    obtain ⟨p,get⟩ := List.mem_iff_getElem?.mp hm
    have lt := (List.getElem?_eq_some_iff.mp get).1
    have bound := read_count_le C (w := w) lt
    rw [gateAt_some get,zero] at bound
    have pos := List.count_pos_iff.mpr hi
    omega
  · intro absent
    unfold readsIn
    apply Finset.sum_eq_zero
    intro p hp
    apply List.count_eq_zero_of_not_mem
    exact absent _ (List.mem_iff_getElem?.mpr ⟨p,atGate (Finset.mem_range.mp hp)⟩)

private theorem forced_correct_dead {N : ℕ} {C : Circuit} {p : ℕ}
    (back : ReadsBack N C) (out : C.output ≠ N+p)
    (absent : ∀ g ∈ C.gates, N+p ∉ g.inputs) (y : Fin N → Bool) :
    (forced C p).eval (List.ofFn y) = C.eval (List.ofFn y) := by
  let x := List.ofFn y
  let D := forced C p
  let V := fun w => (C.wires x).getD w false
  let U := fun w => (D.wires x).getD w false
  have len : x.length = N := by simp [x]
  have sizeEq : D.size = C.size := forced_size C p
  have sameNear (w : ℕ) (lt : w < N) : V w = U w := by
    simp only [V,U,wires_eq]
    rw [getD_wiresFrom C.gates _ _ (by omega),getD_wiresFrom D.gates _ _ (by omega)]
  have sameFar (w : ℕ) (lt : N+C.size ≤ w) : V w = U w := by
    have lc : (wiresFrom C.gates x).length ≤ w := by rw [length_wiresFrom,len]; exact lt
    have ld : (wiresFrom D.gates x).length ≤ w := by
      rw [length_wiresFrom,len]
      change N+D.size ≤ w
      rwa [sizeEq]
    simp only [V,U,wires_eq,List.getD_eq_default _ _ lc,List.getD_eq_default _ _ ld]
  have eq (w : ℕ) (except : w ≠ N+p) : V w = U w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases small : w < N
      · exact sameNear w small
      · by_cases big : N+C.size ≤ w
        · exact sameFar w big
        · obtain ⟨j,rfl⟩ : ∃ j, w = N+j := ⟨w-N,by omega⟩
          have lt : j < C.size := by omega
          have other : j ≠ p := by omega
          have old : V (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map V) :=
            eval_gate back x len lt
          have new : U (N+j) = (gateAt D j).op.eval ((gateAt D j).inputs.map U) :=
            eval_gate (forced_back back) x len (by rwa [sizeEq])
          rw [show gateAt D j = gateAt C j from forced_else lt other] at new
          by_contra diff
          obtain ⟨w,read,earlier,difference⟩ := changed_operand back lt old new diff
          have hmem := List.mem_iff_getElem?.mpr ⟨j,atGate lt⟩
          have wNe : w ≠ N+p := fun same => absent _ hmem (same ▸ read)
          exact difference (ih w earlier wNe)
  exact (eq C.output out).symm

theorem simplifies_sameOp (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = .and ∨ op = .or) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  rcases hop with rfl | rfl
  · intro g hg
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpAnd] at hg
    subst hg
    rfl
  · intro g hg
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify,simpOr] at hg
    subst hg
    rfl

theorem elim_positive (n : ℕ) (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ acc.2, g.op = .and ∨ g.op = .or) →
      ∀ g ∈ (elim n gs acc).2, g.op = .and ∨ g.op = .or := by
  induction gs with
  | nil => intro acc known; exact known
  | cons g gs ih =>
    intro acc known
    rw [elim_cons]
    apply ih (fun g' hg => ops g' (List.mem_cons_of_mem _ hg))
    intro h hh
    rcases List.mem_append.mp hh with old | new
    · exact known h old
    · have hop := ops g List.mem_cons_self
      exact (simplifies_sameOp _ _ _ hop h (by simpa using new)) ▸ hop

def Candidate (N : ℕ) (C D : Circuit) : Prop :=
  Monotone2 D ∧ CleanL N D.gates ∧ D.output < N+D.size ∧
    ∀ y : Fin N → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn y)

theorem normalized_mono (N : ℕ) (C : Circuit) (fan : Monotone2 C)
    (varies : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D, Candidate N C D ∧ D.size ≤ C.size ∧
      ((⟨.or,[]⟩ : Gate) ∈ C.gates → D.size < C.size) := by
  let acc := elim N C.gates (idStats N,[])
  have positive (g : Gate) (mem : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by
    simpa using (fan g mem).1
  have good (g : Gate) (mem : g ∈ C.gates) : Ok g := by
    have cap := (fan g mem).2
    rcases positive g mem with a | b
    · simp [Ok, a, cap]
    · simp [Ok, b, cap]
  have inv (y : Fin N → Bool) : Inv N (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    inv_elim N _ (by simp) _ _ _ good (inv_id N y)
  have ev (y : Fin N → Bool) :
      (acc.1.getD C.output (.const false)).val (wiresFrom acc.2 (List.ofFn y)) = C.eval (List.ofFn y) :=
    ((inv y).2 C.output).2
  have clean : CleanL N acc.2 :=
    clean_elim N _ (by simp) _ _ _ good (inv_id N (fun _ => false)) (by intro j g hv; simp at hv)
  have cap : acc.2.length ≤ C.size := by simpa [acc,Circuit.size] using elim_len N C.gates (idStats N,[])
  cases status : acc.1.getD C.output (.const false) with
  | const c =>
    obtain ⟨x,y,diff⟩ := varies
    have ex := ev x
    have ey := ev y
    rw [status] at ex ey
    exact (diff (ex.symm.trans ey)).elim
  | wire output =>
    let D : Circuit := ⟨acc.2,output⟩
    refine ⟨D,⟨?_,clean,?_,?_⟩,cap,?_⟩
    · intro g hg
      have ops := elim_positive N C.gates positive (idStats N,[]) (by simp) g hg
      have well := elim_ok N C.gates (idStats N,[]) (by simp) g hg
      exact ⟨by simpa using ops,well.2⟩
    · have valid := ((inv (fun _ => false)).2 C.output).1
      rw [status] at valid
      exact valid
    · intro y
      have eq := ev y
      rw [status] at eq
      exact eq
    · intro empty
      exact drops_emptyOR N C.gates empty

def Reduced (N : ℕ) (D : Circuit) : Prop :=
  (D.size = 0 ∧ D.output < N) ∨
  (0 < D.size ∧ D.output + 1 = N+D.size ∧
    ∀ j < D.size, readsIn D (Finset.range D.size) (N+j) = 0 ↔ j+1=D.size)

theorem reduced_mono (N : ℕ) (C : Circuit) (fan : Monotone2 C)
    (varies : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D, Candidate N C D ∧ D.size ≤ C.size ∧ Reduced N D := by
  classical
  obtain ⟨B, bGood, bSize, _⟩ := normalized_mono N C fan varies
  let P : ℕ → Prop := fun k => ∃ E, Candidate N C E ∧ E.size = k
  have possible : ∃ k, P k := ⟨B.size,B,bGood,rfl⟩
  obtain ⟨D, dGood, eq⟩ := Nat.find_spec possible
  have least (E : Circuit) (valid : Candidate N C E) : D.size ≤ E.size := by
    rw [eq]
    exact Nat.find_min' possible ⟨E,valid,rfl⟩
  refine ⟨D,dGood,(least B bGood).trans bSize,?_⟩
  rcases dGood with ⟨dMono,clean,valid,eval⟩
  have output (j : ℕ) (inside : j < D.size) (zero : readsIn D (Finset.range D.size) (N+j) = 0) :
      D.output = N+j := by
    by_contra different
    let F := forced D j
    have same (y : Fin N → Bool) : F.eval (List.ofFn y) = C.eval (List.ofFn y) :=
      (forced_correct_dead (clean_back clean) different (no_reader_iff.mp zero) y).trans (eval y)
    have diff : ∃ x y : Fin N → Bool, F.eval (List.ofFn x) ≠ F.eval (List.ofFn y) := by
      obtain ⟨x,y,ne⟩ := varies
      exact ⟨x,y,by rwa [same x,same y]⟩
    obtain ⟨E,good,_,short⟩ := normalized_mono N F (forced_mono dMono) diff
    have empty : (⟨.or,[]⟩ : Gate) ∈ F.gates :=
      List.mem_iff_getElem?.mpr ⟨j,List.getElem?_set_self (a := emptyOR) inside⟩
    have earlier : E.size < D.size := by simpa [F,forced_size] using short empty
    have proposed : Candidate N C E :=
      ⟨good.1, good.2.1, good.2.2.1, fun y => (good.2.2.2 y).trans (same y)⟩
    exact (Nat.not_le_of_lt earlier) (least E proposed)
  by_cases empty : D.size = 0
  · exact Or.inl ⟨empty,by omega⟩
  · let last := D.size-1
    have inside : last < D.size := by dsimp [last]; omega
    have zero : readsIn D (Finset.range D.size) (N+last) = 0 := by
      apply no_reader_iff.mpr
      intro g mem read
      obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp mem
      have before := (clean j g get).lt _ read
      have jlt : j < D.size := (List.getElem?_eq_some_iff.mp get).1
      dsimp [last] at before
      omega
    have isLast := output last inside zero
    have lastEq : last+1 = D.size := by dsimp [last]; omega
    refine Or.inr ⟨by omega,by omega,?_⟩
    intro j jlt
    constructor
    · intro zj
      have eq := output j jlt zj
      omega
    · intro jeq
      have eq : j = last := by omega
      rwa [eq]

end MonoReduction24999
namespace FormulaSplit

private theorem and_mono {a b c d : Bool} (ab : a ≤ b) (cd : c ≤ d) :
    (a && c) ≤ (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Bool.le_iff_imp]

private theorem or_mono {a b c d : Bool} (ab : a ≤ b) (cd : c ≤ d) :
    (a || c) ≤ (b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Bool.le_iff_imp]

inductive Tree (V : Type) where
  | input (v : V)
  | meet (branch sibling : Tree V)
  | join (branch sibling : Tree V)

namespace Tree

variable {V : Type} [DecidableEq V]

def support : Tree V → Finset V
  | .input v => {v}
  | .meet f g => f.support ∪ g.support
  | .join f g => f.support ∪ g.support

def eval : Tree V → Finset V → Bool
  | .input v, s => decide (v ∈ s)
  | .meet f g, s => f.eval s && g.eval s
  | .join f g, s => f.eval s || g.eval s

def readOnce : Tree V → Prop
  | .input _ => True
  | .meet f g | .join f g =>
      f.readOnce ∧ g.readOnce ∧ Disjoint f.support g.support

theorem support_nonempty (t : Tree V) : t.support.Nonempty := by
  induction t with
  | input i => exact ⟨i, Finset.mem_singleton_self _⟩
  | meet f g hf _ | join f g hf _ =>
    obtain ⟨i, hi⟩ := hf
    exact ⟨i,Finset.mem_union_left _ hi⟩

theorem empty_false (t : Tree V) : t.eval ∅ = false := by
  induction t <;> simp_all [eval]

theorem evaluate_congr (t : Tree V) {s q : Finset V}
    (same : ∀ i ∈ t.support, i ∈ s ↔ i ∈ q) : t.eval s = t.eval q := by
  induction t with
  | input v => simpa [eval] using same v (Finset.mem_singleton_self _)
  | meet f g fh gh | join f g fh gh =>
    have l := fh (fun i hi => same i (Finset.mem_union_left _ hi))
    have r := gh (fun i hi => same i (Finset.mem_union_right _ hi))
    simp only [eval, l, r]

theorem eval_mono (t : Tree V) {s q : Finset V} (h : s ⊆ q) :
    t.eval s ≤ t.eval q := by
  induction t with
  | input v =>
    apply Bool.le_iff_imp.mpr
    simpa only [eval, decide_eq_true_eq] using fun hs : v ∈ s => h hs
  | meet f g ihf ihg =>
    change (f.eval s && g.eval s) ≤ (f.eval q && g.eval q)
    exact and_mono ihf ihg
  | join f g ihf ihg =>
    change (f.eval s || g.eval s) ≤ (f.eval q || g.eval q)
    exact or_mono ihf ihg

end Tree

end FormulaSplit

namespace Graph24999

open FormulaSplit

abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n

def edge {n : ℕ} (u v : Fin n) : Bool :=
  decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val ≤ 1))

def pair {n : ℕ} (u v : Fin n) : Finset (Vertex n) := {Sum.inl u, Sum.inr v}

def z {n : ℕ} (h : 3 ≤ n) : Fin n := ⟨0, by omega⟩
def o {n : ℕ} (h : 3 ≤ n) : Fin n := ⟨1, by omega⟩
def t {n : ℕ} (h : 3 ≤ n) : Fin n := ⟨2, by omega⟩

theorem rowZero {n : ℕ} (h : 3 ≤ n) {v : Fin n} (nz : v.val ≠ 0) :
    edge (z h) v = true := by simp [edge,z,nz]

theorem colZero {n : ℕ} (h : 3 ≤ n) {u : Fin n} (nz : u.val ≠ 0) :
    edge u (z h) = true := by
  simp [edge,z,nz]
  omega

theorem bridge {n : ℕ} (h : 3 ≤ n) : edge (t h) (o h) = true := by simp [edge,t,o]

theorem row_not_universal {n : ℕ} (h : 3≤n) (u : Fin n) :
    ∃ v, edge u v = false := by
  by_cases zero : u.val = 0
  · exact ⟨z h, by simp [edge,z,zero]⟩
  · exact ⟨t h, by simp [edge,t,zero]⟩

theorem col_not_universal {n : ℕ} (h : 3≤n) (v : Fin n) :
    ∃ u, edge u v = false := by
  by_cases zero : v.val = 0
  · exact ⟨z h, by simp [edge,z,zero]⟩
  · exact ⟨o h, by simp [edge,o,zero]⟩

theorem constant_on_edges {n : ℕ} (h : 3≤n) (p : Vertex n → Bool)
    (same : ∀ u v, edge u v = true → p (.inl u) = p (.inr v)) :
    ∀ w, p w = p (.inl (z h)) := by
  have b1 := same (z h) (o h) (rowZero h (by simp [o]))
  have b2 := same (t h) (o h) (bridge h)
  have b3 := same (t h) (z h) (colZero h (by simp [t]))
  have firstCol : p (.inr (z h)) = p (.inl (z h)) := b3.symm.trans (b2.trans b1.symm)
  intro w
  cases w with
  | inl u =>
    by_cases hu : u.val = 0
    · have eq : u = z h := Fin.ext hu
      simp [eq]
    · exact (same u (z h) (colZero h hu)).trans firstCol
  | inr v =>
    by_cases hv : v.val = 0
    · have eq : v = z h := Fin.ext hv
      simpa [eq] using firstCol
    · exact (same (z h) v (rowZero h hv)).symm

theorem no_singleton {n : ℕ} (h : 3≤n) {T : FormulaSplit.Tree (Vertex n)}
    (correct : ∀ u v, T.eval (pair u v) = edge u v) (w : Vertex n) :
    T.eval {w} = false := by
  cases w with
  | inl u =>
    obtain ⟨v,hv⟩ := row_not_universal h u
    have sub : ({Sum.inl u} : Finset (Vertex n)) ⊆ pair u v := by simp [pair]
    have le := T.eval_mono sub
    rw [correct,hv] at le
    exact Bool.eq_false_of_le_false le
  | inr v =>
    obtain ⟨u,hu⟩ := col_not_universal h v
    have sub : ({Sum.inr v} : Finset (Vertex n)) ⊆ pair u v := by simp [pair]
    have le := T.eval_mono sub
    rw [correct,hu] at le
    exact Bool.eq_false_of_le_false le

theorem remove_left {n : ℕ} (f : FormulaSplit.Tree (Vertex n)) (u v : Fin n)
    (off : Sum.inl u ∉ f.support) : f.eval (pair u v) = f.eval {Sum.inr v} := by
  apply f.evaluate_congr
  intro q hq
  simp only [pair, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun h => h.elim (fun eq => (off (eq ▸ hq)).elim) id, Or.inr⟩

theorem remove_right {n : ℕ} (f : FormulaSplit.Tree (Vertex n)) (u v : Fin n)
    (off : Sum.inr v ∉ f.support) : f.eval (pair u v) = f.eval {Sum.inl u} := by
  apply f.evaluate_congr
  intro q hq
  simp only [pair, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun h => h.elim id (fun eq => (off (eq ▸ hq)).elim), Or.inl⟩

theorem remove_both {n : ℕ} (f : FormulaSplit.Tree (Vertex n)) (u v : Fin n)
    (a : Sum.inl u ∉ f.support) (b : Sum.inr v ∉ f.support) :
    f.eval (pair u v) = false := by
  rw [remove_left f u v a, ← f.empty_false]
  apply f.evaluate_congr
  intro q hq
  simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
  exact fun eq => b (eq ▸ hq)

theorem root_impossible {n : ℕ} (h : 3≤n) (T : FormulaSplit.Tree (Vertex n))
    (once : T.readOnce) (correct : ∀ u v, T.eval (pair u v) = edge u v) : False := by
  have singles := no_singleton h correct
  cases T with
  | input w => simpa [FormulaSplit.Tree.eval] using singles w
  | join f g =>
    have separate : Disjoint f.support g.support := once.2.2
    have left (w : Vertex n) : f.eval {w} = false := (Bool.or_eq_false_iff.mp (singles w)).1
    have right (w : Vertex n) : g.eval {w} = false := (Bool.or_eq_false_iff.mp (singles w)).2
    let color (w : Vertex n) : Bool := decide (w ∈ f.support)
    have oneColor : ∀ u v, edge u v = true → color (.inl u) = color (.inr v) := by
      intro u v e
      have ev := correct u v
      change (f.eval (pair u v) || g.eval (pair u v)) = _ at ev
      by_cases row : Sum.inl u ∈ f.support <;> by_cases col : Sum.inr v ∈ f.support
      · simp [color,row,col]
      · have off := (Finset.disjoint_left.mp separate) row
        rw [remove_right f u v col,remove_left g u v off,left,right,e] at ev
        contradiction
      · have off := (Finset.disjoint_left.mp separate) col
        rw [remove_left f u v row,remove_right g u v off,left,right,e] at ev
        contradiction
      · simp [color,row,col]
    have same := constant_on_edges h color oneColor
    obtain ⟨a,ha⟩ := f.support_nonempty
    obtain ⟨b,hb⟩ := g.support_nonempty
    have hb' : b ∉ f.support := fun hb' => (Finset.disjoint_left.mp separate) hb' hb
    have eq := (same a).trans (same b).symm
    simp [color,ha,hb'] at eq
  | meet f g =>
    have separate : Disjoint f.support g.support := once.2.2
    let color (w : Vertex n) : Bool := decide (w ∈ f.support)
    have different : ∀ u v, edge u v = true → color (.inl u) ≠ color (.inr v) := by
      intro u v e
      have ev := correct u v
      change (f.eval (pair u v) && g.eval (pair u v)) = _ at ev
      by_cases row : Sum.inl u ∈ f.support <;> by_cases col : Sum.inr v ∈ f.support
      · have a := (Finset.disjoint_left.mp separate) row
        have b := (Finset.disjoint_left.mp separate) col
        rw [remove_both g u v a b,e] at ev
        simp at ev
      · simp [color,row,col]
      · simp [color,row,col]
      · rw [remove_both f u v row col,e] at ev
        simp at ev
    let flipped (w : Vertex n) : Bool := w.elim (fun u => color (.inl u)) (fun v => !color (.inr v))
    have aligned : ∀ u v, edge u v = true → flipped (.inl u) = flipped (.inr v) := by
      intro u v e
      have diff := different u v e
      change color (.inl u) = !color (.inr v)
      exact Bool.eq_not_of_ne diff
    have same := constant_on_edges h flipped aligned
    have col o1 : color (.inr o1) = !color (.inl (z h)) := by
      have eq := same (.inr o1)
      change (!color (.inr o1)) = color (.inl (z h)) at eq
      simpa using congrArg Bool.not eq
    have row u : color (.inl u) = color (.inl (z h)) := same (.inl u)
    have pos1 := correct (z h) (o h)
    have pos2 := correct (o h) (z h)
    have neg := correct (z h) (z h)
    change (f.eval (pair (z h) (o h)) && g.eval (pair (z h) (o h))) = _ at pos1
    change (f.eval (pair (o h) (z h)) && g.eval (pair (o h) (z h))) = _ at pos2
    change (f.eval (pair (z h) (z h)) && g.eval (pair (z h) (z h))) = _ at neg
    rw [rowZero h (by simp [o])] at pos1
    rw [colZero h (by simp [o])] at pos2
    have e0 : edge (z h) (z h) = false := by simp [edge,z]
    rw [e0] at neg
    by_cases side : Sum.inl (z h) ∈ f.support
    · have cOff v : Sum.inr v ∉ f.support := by simpa [color,side] using col v
      have rOn u : Sum.inl u ∈ f.support := by simpa [color,side] using row u
      have rOff u : Sum.inl u ∉ g.support := (Finset.disjoint_left.mp separate) (rOn u)
      rw [remove_right f _ _ (cOff _),remove_left g _ _ (rOff _)] at pos1 pos2 neg
      rw [(Bool.and_eq_true_iff.mp pos1).1,(Bool.and_eq_true_iff.mp pos2).2] at neg
      contradiction
    · have cOn v : Sum.inr v ∈ f.support := by simpa [color,side] using col v
      have rOff u : Sum.inl u ∉ f.support := by simpa [color,side] using row u
      have cOff v : Sum.inr v ∉ g.support := (Finset.disjoint_left.mp separate) (cOn v)
      rw [remove_left f _ _ (rOff _),remove_right g _ _ (cOff _)] at pos1 pos2 neg
      rw [(Bool.and_eq_true_iff.mp pos2).1,(Bool.and_eq_true_iff.mp pos1).2] at neg
      contradiction

end Graph24999

namespace Graph24999

open PEqualNP.CircuitLowerBounds

theorem vertex_sensitive {n : ℕ} (h : 3 ≤ n) (F : Finset (Vertex n) → Bool)
    (mono : ∀ ⦃s t⦄, s ⊆ t → F s ≤ F t)
    (correct : ∀ u v, F (pair u v) = edge u v) :
    ∀ w, ∃ q : Vertex n, q ≠ w ∧ F {q} = false ∧ F {w,q} = true := by
  intro w
  cases w with
  | inl u =>
    have incident : ∃ v : Fin n, edge u v = true := by
      by_cases uZero : u.val = 0
      · have eq : u = z h := Fin.ext uZero
        exact ⟨o h, eq.symm ▸ rowZero h (by simp [o])⟩
      · exact ⟨z h, colZero h uZero⟩
    obtain ⟨v, positive⟩ := incident
    obtain ⟨u', negative⟩ := col_not_universal h v
    have inclusion : ({Sum.inr v} : Finset (Vertex n)) ⊆ pair u' v := by simp [pair]
    have le := mono inclusion
    rw [correct, negative] at le
    exact ⟨Sum.inr v, by simp, Bool.eq_false_of_le_false le, (correct u v).trans positive⟩
  | inr v =>
    have incident : ∃ u : Fin n, edge u v = true := by
      by_cases colZero' : v.val = 0
      · have eq : v = z h := Fin.ext colZero'
        exact ⟨o h, eq.symm ▸ colZero h (by simp [o])⟩
      · exact ⟨z h, rowZero h colZero'⟩
    obtain ⟨u, positive⟩ := incident
    obtain ⟨v', negative⟩ := row_not_universal h u
    have inclusion : ({Sum.inl u} : Finset (Vertex n)) ⊆ pair u v' := by simp [pair]
    have le := mono inclusion
    rw [correct, negative] at le
    have swap : ({Sum.inr v, Sum.inl u} : Finset (Vertex n)) = pair u v := by
      ext q
      simp [pair,or_comm]
    exact ⟨Sum.inl u, by simp, Bool.eq_false_of_le_false le,
      (congrArg F swap).trans ((correct u v).trans positive)⟩

theorem slots_length (gs : List Gate) (reads : ∀ g ∈ gs, g.inputs.length = 2) :
    (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    have ha := reads a List.mem_cons_self
    have hg := ih (fun g hg => reads g (List.mem_cons_of_mem _ hg))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ha, hg]
    omega

theorem saturated_slots (N : ℕ) (gs : List Gate)
    (positive : 0 < gs.length) (budget : gs.length + 1 ≤ N)
    (binary : ∀ g ∈ gs, g.inputs.length = 2)
    (every : Finset.range (N + gs.length - 1) ⊆ (gs.flatMap Gate.inputs).toFinset) :
    gs.length + 1 = N ∧ (gs.flatMap Gate.inputs).Nodup := by
  let slots := gs.flatMap Gate.inputs
  have low := Finset.card_le_card every
  rw [Finset.card_range] at low
  have high := List.toFinset_card_le slots
  have len : slots.length = 2 * gs.length := slots_length gs binary
  change N + gs.length - 1 ≤ slots.toFinset.card at low
  have tight : slots.toFinset.card = slots.length := by omega
  refine ⟨by omega, ?_⟩
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (slots : Multiset ℕ))).mp tight

end Graph24999

namespace MonoForest24999

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open FormulaSplit
variable {V : Type} [Fintype V] [DecidableEq V]

def onSet {n : Nat} (labels : V ≃ Fin n) (x : List Bool) : Finset V :=
  Finset.univ.filter fun v => x.getD (labels v).val false

def slots (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

def Binary (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def Earlier (n : Nat) (gs : List Gate) : Prop := ReadsBack n ⟨gs,0⟩

def Available (n : Nat) (gs : List Gate) (w : Nat) : Prop :=
  w < n + gs.length ∧ w ∉ slots gs

def vals (gs : List Gate) (x : List Bool) : List Bool := (Circuit.mk gs 0).wires x

private theorem at_prefix (gs : List Gate) (g : Gate) (j : Nat) (hj : j < gs.length) :
    gateAt ⟨gs ++ [g],0⟩ j = gateAt ⟨gs,0⟩ j := by
  simp only [gateAt]
  rw [List.getD_append _ _ _ _ hj]

private theorem at_last (gs : List Gate) (g : Gate) :
    gateAt ⟨gs ++ [g],0⟩ gs.length = g := by
  simp [gateAt,List.getD_eq_getElem?_getD]

private theorem earlier_prefix {n : Nat} {gs : List Gate} {g : Gate}
    (back : Earlier n (gs ++ [g])) : Earlier n gs := by
  intro j hj w hw
  have hlen : j < gs.length := hj
  apply back j (by change j < (gs ++ [g]).length; simpa using Nat.lt_succ_of_lt hlen) w
  rwa [at_prefix gs g j hlen]

private theorem earlier_last {n : Nat} {gs : List Gate} {g : Gate}
    (back : Earlier n (gs ++ [g])) : ∀ w ∈ g.inputs, w < n + gs.length := by
  intro w hw
  apply back gs.length (by change gs.length < (gs ++ [g]).length; simp) w
  rwa [at_last]

private theorem slots_count (gs : List Gate) (w : Nat) :
    (slots gs).count w = readsIn ⟨gs,0⟩ (Finset.range gs.length) w := by
  induction gs using List.reverseRecOn with
  | nil => simp [slots,readsIn]
  | append_singleton gs g ih =>
    simp only [slots,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.count_append] at ih ⊢
    rw [ih,show (gs ++ [g]).length = gs.length+1 by simp]
    simp only [readsIn,Finset.sum_range_succ,at_last]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [at_prefix gs g j (Finset.mem_range.mp hj)]

theorem reads_eq_count (C : Circuit) (w : Nat) :
    (slots C.gates).count w = readsIn C (Finset.range C.size) w := by
  obtain ⟨gs,out⟩ := C
  exact slots_count gs w

private theorem slot_bound {n : Nat} {gs : List Gate} (back : Earlier n gs) {w : Nat}
    (used : w ∈ slots gs) : w + 1 < n + gs.length := by
  obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp used
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
  have valid : j < gs.length := List.getElem?_eq_some_iff.mp hj |>.choose
  have atGate : gateAt ⟨gs,0⟩ j = g := by
    simp [gateAt,List.getD_eq_getElem?_getD,hj]
  have before := back j valid w (by simpa [atGate] using hr)
  omega

private theorem vals_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    vals (gs ++ [g]) x = vals gs x ++ [g.op.eval (g.inputs.map fun i => (vals gs x).getD i false)] := by
  simp [vals,Circuit.wires,List.foldl_append]

private theorem vals_length (gs : List Gate) (x : List Bool) :
    (vals gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [vals,Circuit.wires]
  | append_singleton gs g ih => simp [vals_snoc,ih,Nat.add_assoc]

private structure Forest {n : Nat} (labels : V ≃ Fin n) (gs : List Gate) (trees : Nat → FormulaSplit.Tree V) : Prop where
  once : ∀ w, Available n gs w → (trees w).readOnce
  apart : ∀ u v, Available n gs u → Available n gs v → u ≠ v →
    Disjoint (trees u).support (trees v).support
  eval : ∀ w, Available n gs w → ∀ x : List Bool, x.length = n →
    (trees w).eval (onSet labels x) = (vals gs x).getD w false

theorem forest_exists (n : Nat) (nonzero : 0 < n) (labels : V ≃ Fin n) (gs : List Gate) (back : Earlier n gs)
    (good : ∀ g ∈ gs, Binary g) (once : (slots gs).Nodup) :
    ∃ trees : Nat → FormulaSplit.Tree V, Forest labels gs trees := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    let base (w : Nat) : FormulaSplit.Tree V :=
      .input (labels.symm (if h : w < n then ⟨w,h⟩ else ⟨0,nonzero⟩))
    refine ⟨base, ⟨fun _ _ => trivial, ?_, ?_⟩⟩
    · intro u v av bv ne
      have hu : u < n := by simpa using av.1
      have hv : v < n := by simpa using bv.1
      have distinct : labels.symm ⟨u,hu⟩ ≠ labels.symm ⟨v,hv⟩ :=
        fun eq => ne (congrArg Fin.val (labels.symm.injective eq))
      simpa [base,hu,hv,FormulaSplit.Tree.support] using distinct
    · intro w valid x _
      have hw : w < n := by simpa using valid.1
      simp [base,hw,FormulaSplit.Tree.eval, onSet, vals,Circuit.wires]
  | append_singleton gs g ih =>
    have gBin := good g (by simp)
    have both := earlier_last back
    have goodPre (h : Gate) (mem : h ∈ gs) := good h (by simp [mem])
    have sEq : slots (gs ++ [g]) = slots gs ++ g.inputs := by simp [slots]
    rw [sEq,List.nodup_append'] at once
    obtain ⟨P,fp⟩ := ih (earlier_prefix back) goodPre once.1
    obtain ⟨a,b,args⟩ : ∃ a b, g.inputs = [a,b] := by
      have length := gBin.2
      rcases ls : g.inputs with _ | ⟨a,_ | ⟨b,tail⟩⟩
      · simp [ls] at length
      · simp [ls] at length
      · have h : tail = [] := by simpa [ls] using length
        exact ⟨a,b,by simp [h]⟩
    have ha : a ∈ g.inputs := by simp [args]
    have hb : b ∈ g.inputs := by simp [args]
    have av : Available n gs a := ⟨both a ha,fun hall => (once.2.2 hall ha)⟩
    have bv : Available n gs b := ⟨both b hb,fun hall => (once.2.2 hall hb)⟩
    have ne : a ≠ b := by simpa [args] using once.2.1
    let k := n + gs.length
    let root := if g.op = .and then FormulaSplit.Tree.meet (P a) (P b)
      else FormulaSplit.Tree.join (P a) (P b)
    let T := fun w => if w = k then root else P w
    have earlier {w} (valid : Available n (gs ++ [g]) w) (notLast : w ≠ k) :
        Available n gs w := by
      refine ⟨?_,fun hh => valid.2 (by rw [sEq]; exact List.mem_append_left _ hh)⟩
      have size := valid.1
      simp [k] at notLast
      simp at size
      omega
    have not_a {w} (valid : Available n (gs ++ [g]) w) : a ≠ w := by
      rintro rfl
      exact valid.2 (by rw [sEq]; exact List.mem_append_right _ ha)
    have not_b {w} (valid : Available n (gs ++ [g]) w) : b ≠ w := by
      rintro rfl
      exact valid.2 (by rw [sEq]; exact List.mem_append_right _ hb)
    have rootOnce : root.readOnce := by
      have h : (P a).readOnce ∧ (P b).readOnce ∧ Disjoint (P a).support (P b).support :=
        ⟨fp.once a av,fp.once b bv,fp.apart a b av bv ne⟩
      dsimp [root]
      split <;> exact h
    have rootSupport : root.support = (P a).support ∪ (P b).support := by
      dsimp [root]
      split <;> rfl
    have rootApart {w} (valid : Available n (gs ++ [g]) w) (notLast : w ≠ k) :
        Disjoint root.support (P w).support := by
      rw [rootSupport,Finset.disjoint_union_left]
      exact ⟨fp.apart a w av (earlier valid notLast) (not_a valid),
             fp.apart b w bv (earlier valid notLast) (not_b valid)⟩
    refine ⟨T,⟨?_,?_,?_⟩⟩
    · intro w valid
      by_cases eq : w = k
      · simpa [T,eq] using rootOnce
      · simp [T,eq,fp.once w (earlier valid eq)]
    · intro u v hu hv notEq
      by_cases eu : u = k
      · have ev : v ≠ k := fun e => notEq (eu.trans e.symm)
        simpa [T,eu,ev] using rootApart hv ev
      · by_cases ev : v = k
        · simpa [T,eu,ev] using (rootApart hu eu).symm
        · simpa [T,eu,ev] using fp.apart u v (earlier hu eu) (earlier hv ev) notEq
    · intro w valid x hx
      by_cases eq : w = k
      · subst w
        rw [show T k = root by simp [T],vals_snoc,← show (vals gs x).length = k by simp [vals_length,hx,k]]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right le_rfl, Nat.sub_self,
          List.getElem?_cons_zero,Option.getD_some]
        have ea := fp.eval a av x hx
        have eb := fp.eval b bv x hx
        rcases gBin.1 with andOp | orOp
        · simp [root,andOp,args,FormulaSplit.Tree.eval,GateOp.eval,ea,eb,List.getD_eq_getElem?_getD]
        · simp [root,orOp,args,FormulaSplit.Tree.eval,GateOp.eval,ea,eb,List.getD_eq_getElem?_getD]
      · rw [show T w = P w by simp [T,eq],vals_snoc,List.getD_append]
        · exact fp.eval w (earlier valid eq) x hx
        · rw [vals_length,hx]
          exact (earlier valid eq).1

theorem output_tree {n : Nat} (nonzero : 0 < n) (labels : V ≃ Fin n) (C : Circuit) (back : ReadsBack n C)
    (good : ∀ g ∈ C.gates, Binary g)
    (once : (slots C.gates).Nodup)
    (out : C.output + 1 = n + C.size ∨ (C.size = 0 ∧ C.output < n)) :
    ∃ t : FormulaSplit.Tree V, t.readOnce ∧ ∀ x : List Bool, x.length = n →
      t.eval (onSet labels x) = C.eval x := by
  obtain ⟨T,f⟩ := forest_exists n nonzero labels C.gates back good once
  have avail : Available n C.gates C.output := by
    rcases out with last | ⟨nil,raw⟩
    · have e : C.size = C.gates.length := rfl
      refine ⟨by omega,fun h => ?_⟩
      have smaller := slot_bound (gs := C.gates) back h
      omega
    · have noGate : C.gates = [] := List.length_eq_zero_iff.mp nil
      exact ⟨by simpa [noGate] using raw,by simp [slots,noGate]⟩
  exact ⟨T C.output,f.once _ avail,f.eval _ avail⟩

end MonoForest24999
namespace MonoBridge24999

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents
open Graph24999 MonoReduction24999

def labels (n : ℕ) : Vertex n ≃ Fin (n+n) := finSumFinEquiv

def words {n : ℕ} (s : Finset (Vertex n)) : List Bool :=
  List.ofFn fun k : Fin (n+n) => decide ((labels n).symm k ∈ s)

theorem words_len {n : ℕ} (s : Finset (Vertex n)) : (words s).length = n+n :=
  List.length_ofFn

theorem words_get {n i : ℕ} (s : Finset (Vertex n)) (h : i<n+n) :
    (words s).getD i false = decide ((labels n).symm ⟨i,h⟩ ∈ s) := by
  unfold words
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h), List.getElem_ofFn]

theorem words_pair {n : ℕ} (u v : Fin n) : words (pair u v) = oneEach u v := by
  apply List.ext_getElem (by simp [words_len,oneEach])
  intro i hi hj
  have limit : i < n+n := by rwa [words_len] at hi
  rw [← List.getD_eq_getElem _ false hi, ← List.getD_eq_getElem _ false hj, words_get _ limit]
  by_cases left : i<n
  · let a : Fin n := ⟨i,left⟩
    have cast : (⟨i,limit⟩ : Fin (n+n)) = a.castAdd n := Fin.ext rfl
    rw [cast]
    change decide (finSumFinEquiv.symm (a.castAdd n) ∈ pair u v) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    unfold oneEach
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using left)]
    have len : i < (List.ofFn fun j : Fin n => decide (j = u)).length := by
      simpa only [List.length_ofFn] using left
    rw [List.getD_eq_getElem _ _ len,List.getElem_ofFn]
    simp [pair,a]
  · let b : Fin n := ⟨i-n,by omega⟩
    have cast : (⟨i,limit⟩ : Fin (n+n)) = b.natAdd n :=
      Fin.ext (by change i = n+(i-n); omega)
    rw [cast]
    change decide (finSumFinEquiv.symm (b.natAdd n) ∈ pair u v) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    unfold oneEach
    rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt left),
      List.length_ofFn]
    have len : i-n < (List.ofFn fun j : Fin n => decide (j = v)).length := by
      rw [List.length_ofFn]; omega
    rw [List.getD_eq_getElem _ _ len,List.getElem_ofFn]
    simp [pair,b]

theorem on_words {n : ℕ} (s : Finset (Vertex n)) :
    MonoForest24999.onSet (labels n) (words s) = s := by
  ext v
  simp only [MonoForest24999.onSet,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [words_get s (labels n v).isLt]
  simp

theorem gate_increasing (g : Gate) (ops : g.op = .and ∨ g.op = .or)
    (x y : List Bool) (order : ∀ i, x.getD i false ≤ y.getD i false) :
    g.op.eval (g.inputs.map fun i => x.getD i false) ≤
      g.op.eval (g.inputs.map fun i => y.getD i false) := by
  apply Bool.le_iff_imp.mpr
  rcases ops with op | op
  · simp only [op,GateOp.eval,List.all_eq_true,List.mem_map, id_eq]
    intro all b hb
    obtain ⟨i,hi,rfl⟩ := hb
    exact (Bool.le_iff_imp.mp (order i)) (all _ ⟨i,hi,rfl⟩)
  · simp only [op,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨_,⟨i,hi,rfl⟩,yes⟩
    exact ⟨_,⟨i,hi,rfl⟩,(Bool.le_iff_imp.mp (order i)) yes⟩

theorem wires_increasing (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {x y : List Bool} (same : x.length = y.length)
    (order : ∀ i, x.getD i false ≤ y.getD i false) :
    ∀ i, (wiresFrom gs x).getD i false ≤ (wiresFrom gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact order
  | cons g gs ih =>
    change ∀ i, (wiresFrom gs (x++[_])).getD i false ≤ (wiresFrom gs (y++[_])).getD i false
    apply ih (fun h hm => ops h (List.mem_cons_of_mem _ hm)) (by simp [same])
    intro i
    by_cases last : i = x.length
    · rw [last,getD_snoc_eq,getD_snoc_len _ _ _ _ same.symm]
      exact gate_increasing g (ops g List.mem_cons_self) x y order
    · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega)]
      exact order i

theorem monotone_words {n : ℕ} (D : Circuit) (mono : Monotone2 D)
    {s t : Finset (Vertex n)} (inc : s ⊆ t) : D.eval (words s) ≤ D.eval (words t) := by
  apply wires_increasing D.gates (fun g hg => by simpa using (mono g hg).1)
    (by rw [words_len,words_len]) _ D.output
  intro i
  by_cases raw : i<n+n
  · rw [words_get _ raw,words_get _ raw]
    exact Bool.le_iff_imp.mpr (by simpa only [decide_eq_true_eq] using @inc ((labels n).symm ⟨i,raw⟩))
  · rw [List.getD_eq_default _ _ (by rw [words_len]; omega),
        List.getD_eq_default _ _ (by rw [words_len]; omega)]

theorem unreferenced (p : ℕ) (gs : List Gate)
    (absent : ∀ g ∈ gs, p ∉ g.inputs) {x y : List Bool} (len : x.length = y.length)
    (agree : ∀ i, i ≠ p → x.getD i false = y.getD i false) :
    ∀ i, i ≠ p → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact agree
  | cons g gs ih =>
    have eq : g.inputs.map (fun i => x.getD i false) = g.inputs.map (fun i => y.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact agree i (fun h => absent g List.mem_cons_self (h ▸ hi))
    simp only [show ∀ z : List Bool, wiresFrom (g::gs) z =
      wiresFrom gs (z++[g.op.eval (g.inputs.map (fun i => z.getD i false))]) from fun _ => rfl, eq]
    apply ih (fun h hh => absent h (List.mem_cons_of_mem _ hh)) (by simp [len])
    intro i hi
    by_cases last : i = x.length
    · rw [last, getD_snoc_eq]
      exact (getD_snoc_len y _ _ x.length len.symm).symm
    · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega)]
      exact agree i hi

theorem required {n : ℕ} (h : 3≤n) (D : Circuit) (mono : Monotone2 D)
    (rep : Represents (fun u v : Fin n => edge u v) D) :
    ∀ i < n+n, i ∈ MonoForest24999.slots D.gates ∨ D.output = i := by
  intro i raw
  let w : Vertex n := (labels n).symm ⟨i,raw⟩
  let F : Finset (Vertex n) → Bool := fun s => D.eval (words s)
  have yes (u v : Fin n) : F (pair u v) = edge u v := by
    dsimp [F]
    rw [words_pair]
    exact rep u v
  obtain ⟨q,_,lo,hi⟩ := vertex_sensitive h F (fun _ _ inc => monotone_words D mono inc) yes w
  by_contra! missing
  have empty : ∀ g ∈ D.gates, i ∉ g.inputs := fun g hg used =>
    missing.1 (List.mem_flatMap.mpr ⟨g,hg,used⟩)
  have equal : F {q} = F {w,q} := by
    apply unreferenced i D.gates empty (by rw [words_len,words_len]) _ D.output missing.2
    intro j different
    by_cases bound : j<n+n
    · rw [words_get _ bound,words_get _ bound]
      have notW : (labels n).symm ⟨j,bound⟩ ≠ w :=
        fun b => different (congrArg Fin.val ((labels n).symm.injective b))
      simp [notW]
    · rw [List.getD_eq_default _ _ (by rw [words_len]; omega),
          List.getD_eq_default _ _ (by rw [words_len]; omega)]
  rw [lo,hi] at equal
  contradiction

theorem lower : ∀ n : ℕ, 3≤n → ¬ RepSizeAtMost (fun u v : Fin n => edge u v) (2*n-1) := by
  intro n h existsC
  obtain ⟨C,mono,size,rep⟩ := existsC
  have nonconstant : ∃ x y : Fin (n+n) → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    refine ⟨fun k : Fin (n+n) => decide ((labels n).symm k ∈ pair (z h) (z h)),
      fun k : Fin (n+n) => decide ((labels n).symm k ∈ pair (z h) (o h)),?_⟩
    change C.eval (words (pair (z h) (z h))) ≠ C.eval (words (pair (z h) (o h)))
    rw [words_pair,words_pair,rep,rep]
    change edge (z h) (z h) ≠ edge (z h) (o h)
    have no : edge (z h) (z h) = false := by simp [edge,z]
    rw [no,rowZero h (by simp [o])]
    decide
  obtain ⟨D,good,bound,reduced⟩ := reduced_mono (n+n) C mono nonconstant
  obtain ⟨dMono,clean,_,eval⟩ := good
  have dRep : Represents (fun u v : Fin n => edge u v) D := by
    intro u v
    have agree := eval (fun k : Fin (n+n) => decide ((labels n).symm k ∈ pair u v))
    change D.eval (words (pair u v)) = C.eval (words (pair u v)) at agree
    rw [words_pair] at agree
    exact agree.trans (rep u v)
  have everyRaw := required h D dMono dRep
  rcases reduced with ⟨zero,rawOut⟩ | ⟨positive,last,used⟩
  · let other : ℕ := if D.output = 0 then 1 else 0
    have otherLt : other<n+n := by dsimp [other]; split <;> omega
    have otherNe : D.output ≠ other := by
      dsimp [other]
      split <;> omega
    have first := (everyRaw other otherLt).resolve_right otherNe
    have noGates : D.gates = [] := List.length_eq_zero_iff.mp zero
    simp [MonoForest24999.slots,noGates] at first
  · have nD : D.size = D.gates.length := rfl
    have dg : D.gates.length + 1 ≤ n+n := by omega
    have binary (g : Gate) (hg : g ∈ D.gates) : MonoForest24999.Binary g := by
      obtain ⟨j,atGate⟩ := List.mem_iff_getElem?.mp hg
      rcases clean j g atGate with ⟨isNot,_⟩ | ⟨ops,a,b,ha,hb,args⟩
      · have opp := (dMono g hg).1
        simp [isNot] at opp
      · exact ⟨ops,by simp [args]⟩
    have back : ReadsBack (n+n) D := by
      intro g hg i mem
      have glt : g < D.gates.length := hg
      have read : D.gates[g]? = some (gateAt D g) := by
        simp [gateAt,glt]
      exact (clean g _ read).lt _ mem
    have slots : Finset.range (n+n+D.gates.length-1) ⊆ (D.gates.flatMap Gate.inputs).toFinset := by
      intro i hi
      have iLt := Finset.mem_range.mp hi
      apply List.mem_toFinset.mpr
      change i ∈ MonoForest24999.slots D.gates
      by_cases raw : i<n+n
      · exact (everyRaw i raw).resolve_right (by omega)
      · let j := i-(n+n)
        have jlt : j<D.size := by dsimp [j]; omega
        have earlier : j+1 ≠ D.size := by dsimp [j]; omega
        have reads : readsIn D (Finset.range D.size) (n+n+j) ≠ 0 := fun k => earlier ((used j jlt).mp k)
        have pos : 0<(MonoForest24999.slots D.gates).count (n+n+j) := by
          rw [MonoForest24999.reads_eq_count]
          omega
        have written : i=n+n+j := by dsimp [j]; omega
        rw [written]
        exact List.count_pos_iff.mp pos
    have tight := saturated_slots (n+n) D.gates (by omega) dg (fun g hg => (binary g hg).2) slots
    obtain ⟨T,once,tree⟩ := MonoForest24999.output_tree (by omega : 0<n+n)
      (labels n) D back binary tight.2 (.inl last)
    apply root_impossible h T once
    intro u v
    have eq := tree (words (pair u v)) (words_len _)
    rw [on_words,words_pair] at eq
    exact eq.trans (dRep u v)

end MonoBridge24999

end PEqualNP.Outside.L_meta_24999_aux

open PEqualNP.Outside.L_meta_24999_aux in
theorem PEqualNP.Outside.L_meta_24999 : (∀ n : ℕ, 3 ≤ n → ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val ≤ 1))) (2 * n - 1)) := by
  exact MonoBridge24999.lower
