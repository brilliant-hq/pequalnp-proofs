import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.L_meta_27804

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
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
end RepReads

namespace RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
open PEqualNP.Represents RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

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
          · 
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
      · 
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
    · 
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

namespace RestrictAux

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

end RestrictAux

theorem restrictSize :
    ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s :=
  RestrictAux.main

namespace Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def core (n m : ℕ) : Circuit :=
  let b := n + m
  ⟨[⟨.or, [0,n]⟩, ⟨.or, [1,n+1]⟩, ⟨.or, [b,b+1]⟩, ⟨.and, [b,b+1]⟩,
    ⟨.or, [n+2,b+3]⟩, ⟨.or, [2,b+4]⟩, ⟨.and, [b+2,b+5]⟩], b+6⟩

private def result (u v : ℕ) : Bool :=
  let x := decide (u = 0 ∨ v = 0)
  let y := decide (u = 1 ∨ v = 1)
  (x || y) && (decide (u = 2) || (decide (v = 2) || (x && y)))

private theorem core_mono (n m : ℕ) : Monotone2 (core n m) := by
  intro g hg
  simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem getL {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (u.val = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Fin.ext_iff, eq_comm]

private theorem getR {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < m) :
    (oneEach u v).getD (n+i) false = decide (v.val = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, hi, Fin.ext_iff, eq_comm]

private theorem core_eval {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) (u : Fin n) (v : Fin m) :
    (core n m).eval (oneEach u v) = result u.val v.val := by
  have h0 := getL u v 0 (by omega)
  have h1 := getL u v 1 (by omega)
  have h2 := getL u v 2 (by omega)
  have h3 := getR u v 0 (by omega)
  have h4 := getR u v 1 (by omega)
  have h5 := getR u v 2 (by omega)
  simp only [Nat.add_zero] at h3
  have hl : (oneEach u v).length = n + m := by simp [oneEach]
  generalize oneEach u v = l at hl h0 h1 h2 h3 h4 h5 ⊢
  have i1 : 1 < l.length := by omega
  have i2 : 2 < l.length := by omega
  have i4 : n + 1 < l.length := by omega
  have i5 : n + 2 < l.length := by omega
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3 h4 h5
  unfold core
  rw [← hl]
  simp only [Circuit.eval, Circuit.wires, List.foldl, List.map, List.getD_eq_getElem?_getD,
    List.append_assoc, List.cons_append, List.nil_append,
    List.getElem?_append_left i1, List.getElem?_append_left i2,
    List.getElem?_append_left i4, List.getElem?_append_left i5, h0, h1, h2, h3, h4, h5,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, GateOp.eval]
  simp [result]

private def push (N : ℕ) (C : Circuit) (i : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output,i]⟩], N + C.size⟩

private theorem push_mono {N i : ℕ} {C : Circuit} (h : Monotone2 C) :
    Monotone2 (push N C i) := by
  intro g hg
  change g ∈ C.gates ++ [_] at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with h' | rfl
  · exact h _ h'
  · simp

private theorem push_eval {N i : ℕ} (C : Circuit) (w : List Bool) (hw : w.length = N)
    (hi : i < N) : (push N C i).eval w = (C.eval w || w.getD i false) := by
  have hprefix : ∀ gs : List Gate, ∀ w : List Bool, ∃ t,
      (Circuit.mk gs 0).wires w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [Circuit.wires]⟩
    | cons g gs ih =>
      intro w
      let a := g.op.eval (g.inputs.map fun j => w.getD j false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [a])
      exact ⟨a :: t, by simpa [Circuit.wires, a] using ht, by simp [hl]⟩
  obtain ⟨t, ht, hl⟩ := hprefix C.gates w
  change C.wires w = w ++ t at ht
  have hlen : (C.wires w).length = N + C.size := by simp [ht, hw, hl, Circuit.size]
  have hget : (C.wires w).getD i false = w.getD i false := by
    rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < w.length by omega)]
  change (((C.gates ++ [_]).foldl _ w).getD (N + C.size) false) = _
  rw [List.foldl_append]
  change ((C.wires w ++ [GateOp.or.eval [(C.wires w).getD C.output false, (C.wires w).getD i false]]).getD (N + C.size) false) = _
  rw [← hlen, hget]
  simp [Circuit.eval, GateOp.eval]

private theorem extend (N : ℕ) (is : List ℕ) (his : ∀ i ∈ is, i < N) (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + is.length ∧
      ∀ w : List Bool, w.length = N → D.eval w = (C.eval w || is.any (fun i => w.getD i false)) := by
  induction is generalizing C with
  | nil => exact ⟨C, hC, by simp, by simp⟩
  | cons i is ih =>
    obtain ⟨D, hD, hs, he⟩ := ih (fun j hj => his j (by simp [hj])) (push N C i) (push_mono hC)
    refine ⟨D, hD, ?_, ?_⟩
    · simpa [push, Circuit.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    · intro w hw
      rw [he w hw, push_eval C w hw (his i (by simp)), List.any_cons, Bool.or_assoc]

private def extras (n m : ℕ) :=
  ((List.range (n-3)).map (3+·)) ++ ((List.range (m-3)).map (fun j => n+(3+j)))

private theorem mem_extras {n m i : ℕ} : i ∈ extras n m ↔
    (3 ≤ i ∧ i < n) ∨ (n+3 ≤ i ∧ i < n+m) := by
  simp only [extras, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩) <;> omega
  · rintro (⟨h,h'⟩ | ⟨h,h'⟩)
    · exact Or.inl ⟨i-3, by omega, by omega⟩
    · exact Or.inr ⟨i-n-3, by omega, by omega⟩

private theorem extras_eval {n m : ℕ} (u : Fin n) (v : Fin m) :
    (extras n m).any (fun i => (oneEach u v).getD i false) = decide (3 ≤ u.val ∨ 3 ≤ v.val) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,h⟩
    rcases mem_extras.mp hi with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [getL u v i h2, decide_eq_true_eq] at h; omega
    · have eq : i = n + (i-n) := by omega
      rw [eq, getR u v (i-n) (by omega), decide_eq_true_eq] at h; omega
  · rintro (h | h)
    · exact ⟨u.val, mem_extras.mpr (Or.inl ⟨h,u.isLt⟩), by rw [getL u v _ u.isLt]; simp⟩
    · exact ⟨n+v.val, mem_extras.mpr (Or.inr ⟨by omega, by have := v.isLt; omega⟩), by rw [getR u v _ v.isLt]; simp⟩

private theorem mask (u v : ℕ) : (result u v || decide (3 ≤ u ∨ 3 ≤ v)) =
    (64478 : ℕ).testBit (4 * min u 3 + min v 3) := by
  have h : ∀ i : Fin 4, ∀ j : Fin 4, (result i.val j.val || decide (3 ≤ i.val ∨ 3 ≤ j.val)) =
      (64478 : ℕ).testBit (4*i.val+j.val) := by decide
  rw [← h ⟨min u 3, by omega⟩ ⟨min v 3, by omega⟩]
  apply Bool.eq_iff_iff.mpr
  simp only [result, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem upper {n m : Nat} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    RepSizeAtMost (fun (u : Fin n) (v : Fin m) => (64478 : Nat).testBit (4*min u.val 3 + min v.val 3)) (n+m+1) := by
  obtain ⟨D, hD, hs, he⟩ := extend (n+m) (extras n m) (fun i hi => by have := mem_extras.mp hi; omega)
    (core n m) (core_mono n m)
  refine ⟨D, hD, ?_, ?_⟩
  · rw [hs]; simp only [core, Circuit.size, List.length_cons, List.length_nil, extras,
      List.length_append, List.length_map, List.length_range]; omega
  · intro u v
    rw [he _ (by simp [oneEach]), core_eval hn hm u v, extras_eval, mask]

end Upper

namespace Lower

open PEqualNP.Represents

private def clip {n : Nat} (u : Fin n) : Fin 4 := ⟨min u.val 3, by omega⟩
private def emb {n : Nat} (h : 4 ≤ n) : Fin 4 ↪ Fin n where
  toFun x := ⟨x.val, by omega⟩
  inj' _ _ e := Fin.ext (congrArg (fun x : Fin n => x.val) e)

private theorem clip_emb {n : Nat} (h : 4 ≤ n) (i : Fin 4) : clip (emb h i) = i := by
  apply Fin.ext
  change min i.val 3 = i.val
  exact Nat.min_eq_left (by omega)

private def base (u v : Fin 4) := (64478 : Nat).testBit (4 * u.val + v.val)
private def mat {n m : Nat} (u : Fin n) (v : Fin m) := base (clip u) (clip v)
private def small : Finset (Fin 4) := Finset.univ.filter fun x => x.val < 3

private theorem rowWitness : ∀ i : Fin 4, ∃ j ∈ small, base i j = true ∧ base j j = false := by decide
private theorem colWitness : ∀ j : Fin 4, ∃ i ∈ small, base i j = true ∧ base i i = false := by decide
private theorem zeroDiag : ∀ i ∈ small, base i i = false := by decide
private theorem table : ∀ u v : Fin 4, (base u v && decide (u ∈ small) && decide (v ∈ small)) =
    (854 : Nat).testBit (4 * u.val + v.val) := by decide

set_option maxHeartbeats 1000000 in
theorem lower {n m : Nat} (hn : 4 ≤ n) (hm : 4 ≤ m) : ¬ RepSizeAtMost
    (fun (u : Fin n) (v : Fin m) => (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)) (n + m) := by
  change ¬ RepSizeAtMost (mat (n := n) (m := m)) (n + m)
  intro h
  classical
  let R := small.map (emb hn)
  let K := small.map (emb hm)
  have rzero : ∀ u ∈ R, ∃ v ∈ K, mat u v = false := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
    exact ⟨emb hm i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, by simpa [mat, clip_emb] using zeroDiag i hi⟩
  have kzero : ∀ v ∈ K, ∃ u ∈ R, mat u v = false := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨emb hn i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, by simpa [mat, clip_emb] using zeroDiag i hi⟩
  have one : ∃ u ∈ R, ∃ v ∈ K, mat u v = true := by
    refine ⟨emb hn 0, Finset.mem_map.mpr ⟨0, by decide, rfl⟩, emb hm 1, Finset.mem_map.mpr ⟨1, by decide, rfl⟩, ?_⟩
    simp only [mat, clip_emb]
    decide
  obtain ⟨s, hs, hk⟩ := RepInduced.induced n m (n+m) mat R K rzero kzero one h
  have allR : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, mat a b = true ∧ ∃ a' : Fin n, mat a' b = false)) = Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    obtain ⟨j, _, hj, hz⟩ := rowWitness (clip a)
    exact ⟨emb hm j, by simpa [mat, clip_emb] using hj, emb hn j, by simpa [mat, clip_emb] using hz⟩
  have allK : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, mat a b = true ∧ ∃ b' : Fin m, mat a b' = false)) = Finset.univ := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    obtain ⟨i, _, hi, hz⟩ := colWitness (clip b)
    exact ⟨emb hn i, by simpa [mat, clip_emb] using hi, emb hm i, by simpa [mat, clip_emb] using hz⟩
  rw [allR, allK] at hk
  simp only [Finset.card_univ, Fintype.card_fin] at hk
  have hr := Finset.card_filter_le R (fun a => ∃ b ∈ K, mat a b = true)
  have hc := Finset.card_filter_le K (fun b => ∃ a ∈ R, mat a b = true)
  have hsmall : small.card = 3 := by decide
  have rcard : R.card = 3 := (Finset.card_map _).trans hsmall
  have kcard : K.card = 3 := (Finset.card_map _).trans hsmall
  rw [rcard] at hr
  rw [kcard] at hc
  have hs6 : s ≤ 6 := by omega
  have ha := restrictSize n m 4 4 s _ (emb hn) (emb hm) (emb hn).injective (emb hm).injective hs
  have heq : (fun (u v : Fin 4) => mat (emb hn u) (emb hm v) && decide (emb hn u ∈ R) && decide (emb hm v ∈ K)) =
      (fun (u v : Fin 4) => (854 : Nat).testBit (4 * u.val + v.val)) := by
    funext u v
    simpa [mat, R, K, clip_emb] using table u v
  change RepSizeAtMost (fun (u v : Fin 4) => mat (emb hn u) (emb hm v) && decide (emb hn u ∈ R) && decide (emb hm v ∈ K)) s at ha
  rw [heq] at ha
  obtain ⟨C, hC, hsize, hrep⟩ := ha
  exact PEqualNP.Outside.L_meta_6158.2 ⟨C, hC, hsize.trans hs6, hrep⟩

end Lower
end PEqualNP.Outside.L_meta_27804

theorem PEqualNP.Outside.L_meta_27804 : (∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  exact ⟨PEqualNP.Outside.L_meta_27804.Upper.upper hn hm, PEqualNP.Outside.L_meta_27804.Lower.lower hn hm⟩
