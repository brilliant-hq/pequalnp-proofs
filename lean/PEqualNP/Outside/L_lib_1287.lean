import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1287_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def maj3 (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

private lemma maj3_of_eq_left {a b c : Bool} (h : a = b) : maj3 a b c = a := by
  subst h; cases a <;> cases c <;> rfl

private lemma maj3_of_eq_mid {a b c : Bool} (h : a = c) : maj3 a b c = a := by
  subst h; cases a <;> cases b <;> rfl

private lemma maj3_of_eq_right {a b c : Bool} (h : b = c) : maj3 a b c = b := by
  subst h; cases a <;> cases b <;> rfl

private lemma ok_of_pairs {t : ℕ} (ok : (Fin t → Bool) → Prop)
    (hne : ∃ z, ok z)
    (hmaj : ∀ a b c, ok a → ok b → ok c →
      ok (fun k => (a k && b k) || (a k && c k) || (b k && c k)))
    (w : Fin t → Bool)
    (hpairs : ∀ k l : Fin t, ∃ z, ok z ∧ z k = w k ∧ z l = w l) :
    ok w := by
  have hS : ∀ (n : ℕ) (S : Finset (Fin t)), S.card = n → ∃ z, ok z ∧ ∀ k ∈ S, z k = w k := by
    intro n
    induction n with
    | zero =>
      intro S hcard
      have hS0 : S = ∅ := Finset.card_eq_zero.mp hcard
      rcases hne with ⟨z, hz⟩
      exact ⟨z, hz, fun k hk => by rw [hS0] at hk; exact absurd hk (Finset.notMem_empty k)⟩
    | succ n ih =>
      intro S hcard
      cases n with
      | zero =>
        rcases Finset.card_eq_one.mp hcard with ⟨k, rfl⟩
        rcases hpairs k k with ⟨z, hz, hzk, _⟩
        exact ⟨z, hz, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hzk⟩
      | succ n =>
        cases n with
        | zero =>
          rcases Finset.card_eq_two.mp hcard with ⟨k, l, _, rfl⟩
          rcases hpairs k l with ⟨z, hz, hzk, hzl⟩
          exact ⟨z, hz, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hzk
            · rw [Finset.mem_singleton.mp hx']; exact hzl⟩
        | succ n =>
          have hpos1 : 0 < S.card := by omega
          rcases Finset.card_pos.mp hpos1 with ⟨k1, hk1⟩
          have hpos2 : 0 < (S.erase k1).card := by
            rw [Finset.card_erase_of_mem hk1]; omega
          rcases Finset.card_pos.mp hpos2 with ⟨k2, hk2⟩
          have hk2S : k2 ∈ S := Finset.mem_of_mem_erase hk2
          have hne12 : k2 ≠ k1 := (Finset.mem_erase.mp hk2).1
          have hpos3 : 0 < ((S.erase k1).erase k2).card := by
            rw [Finset.card_erase_of_mem hk2, Finset.card_erase_of_mem hk1]; omega
          rcases Finset.card_pos.mp hpos3 with ⟨k3, hk3⟩
          have hk3S : k3 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk3)
          have hne32 : k3 ≠ k2 := (Finset.mem_erase.mp hk3).1
          have hne31 : k3 ≠ k1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk3)).1
          rcases ih (S.erase k1) (by rw [Finset.card_erase_of_mem hk1]; omega) with ⟨z1, hz1, hz1S⟩
          rcases ih (S.erase k2) (by rw [Finset.card_erase_of_mem hk2S]; omega) with ⟨z2, hz2, hz2S⟩
          rcases ih (S.erase k3) (by rw [Finset.card_erase_of_mem hk3S]; omega) with ⟨z3, hz3, hz3S⟩
          refine ⟨fun k => (z1 k && z2 k) || (z1 k && z3 k) || (z2 k && z3 k),
            hmaj z1 z2 z3 hz1 hz2 hz3, ?_⟩
          intro k hk
          by_cases h1 : k = k1
          · subst h1
            have ha : z2 k = w k := hz2S k (Finset.mem_erase.mpr ⟨hne12.symm, hk⟩)
            have hb : z3 k = w k := hz3S k (Finset.mem_erase.mpr ⟨hne31.symm, hk⟩)
            change maj3 (z1 k) (z2 k) (z3 k) = w k
            rw [maj3_of_eq_right (ha.trans hb.symm), ha]
          · by_cases h2 : k = k2
            · subst h2
              have ha : z1 k = w k := hz1S k (Finset.mem_erase.mpr ⟨h1, hk⟩)
              have hb : z3 k = w k := hz3S k (Finset.mem_erase.mpr ⟨hne32.symm, hk⟩)
              change maj3 (z1 k) (z2 k) (z3 k) = w k
              rw [maj3_of_eq_mid (ha.trans hb.symm), ha]
            · have ha : z1 k = w k := hz1S k (Finset.mem_erase.mpr ⟨h1, hk⟩)
              have hb : z2 k = w k := hz2S k (Finset.mem_erase.mpr ⟨h2, hk⟩)
              change maj3 (z1 k) (z2 k) (z3 k) = w k
              rw [maj3_of_eq_left (ha.trans hb.symm), ha]
  rcases hS (Finset.univ : Finset (Fin t)).card Finset.univ rfl with ⟨z, hz, hzw⟩
  have heq : z = w := funext fun k => hzw k (Finset.mem_univ k)
  exact heq ▸ hz

private lemma reach_add_arc {α : Type*} (R : α → α → Prop) (a b : α) :
    ∀ x y : α,
      Relation.ReflTransGen (fun p q => R p q ∨ (p = a ∧ q = b)) x y →
      Relation.ReflTransGen R x y ∨ (Relation.ReflTransGen R x a ∧ Relation.ReflTransGen R b y) := by
  intro x y h
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with hr | ⟨rfl, rfl⟩
    · rcases ih with h1 | ⟨h1, h2⟩
      · exact Or.inl (h1.tail hr)
      · exact Or.inr ⟨h1, h2.tail hr⟩
    · rcases ih with h1 | ⟨h1, _⟩
      · exact Or.inr ⟨h1, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨h1, Relation.ReflTransGen.refl⟩

private lemma twosat_add_force {α : Type*} (R : (α × Bool) → (α × Bool) → Prop)
    (hclean : ∀ u : α, ¬ (Relation.ReflTransGen R (u, false) (u, true) ∧
      Relation.ReflTransGen R (u, true) (u, false)))
    (u0 : α) (v0 : Bool)
    (hnot : ¬ Relation.ReflTransGen R (u0, v0) (u0, !v0)) :
    let R' := fun p q => R p q ∨ (p = (u0, !v0) ∧ q = (u0, v0))
    ∀ u : α, ¬ (Relation.ReflTransGen R' (u, false) (u, true) ∧
      Relation.ReflTransGen R' (u, true) (u, false)) := by
  intro R' u ⟨hFT, hTF⟩
  rcases reach_add_arc R (u0, !v0) (u0, v0) _ _ hFT with hFT0 | ⟨hFT1, hFT2⟩
  · rcases reach_add_arc R (u0, !v0) (u0, v0) _ _ hTF with hTF0 | ⟨hTF1, hTF2⟩
    · exact hclean u ⟨hFT0, hTF0⟩
    · exact hnot ((hTF2.trans hFT0).trans hTF1)
  · rcases reach_add_arc R (u0, !v0) (u0, v0) _ _ hTF with hTF0 | ⟨hTF1, hTF2⟩
    · exact hnot ((hFT2.trans hTF0).trans hFT1)
    · exact hnot (hFT2.trans hTF1)

open scoped Classical in
private lemma twosat_solve {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (k : ℕ) (R : (α × Bool) → (α × Bool) → Prop),
      (∀ u a v b, R (u, a) (v, b) → R (v, !b) (u, !a)) →
      (∀ u : α, ¬ (Relation.ReflTransGen R (u, false) (u, true) ∧
        Relation.ReflTransGen R (u, true) (u, false))) →
      ((Finset.univ : Finset α).filter (fun u =>
        ¬ Relation.ReflTransGen R (u, false) (u, true) ∧
        ¬ Relation.ReflTransGen R (u, true) (u, false))).card ≤ k →
      ∃ val : α → Bool, ∀ u a v b, R (u, a) (v, b) → val u = a → val v = b := by
  intro k
  induction k with
  | zero =>
    intro R hsym hclean hcard
    have hforced : ∀ u : α, Relation.ReflTransGen R (u, false) (u, true) ∨
        Relation.ReflTransGen R (u, true) (u, false) := by
      intro u
      by_contra h
      push Not at h
      have hmem : u ∈ (Finset.univ : Finset α).filter (fun u =>
          ¬ Relation.ReflTransGen R (u, false) (u, true) ∧
          ¬ Relation.ReflTransGen R (u, true) (u, false)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩
      have hpos : 0 < ((Finset.univ : Finset α).filter (fun u =>
          ¬ Relation.ReflTransGen R (u, false) (u, true) ∧
          ¬ Relation.ReflTransGen R (u, true) (u, false))).card :=
        Finset.card_pos.mpr ⟨u, hmem⟩
      omega
    let val : α → Bool := fun u => decide (Relation.ReflTransGen R (u, false) (u, true))
    have hval_iff : ∀ (u : α) (b : Bool), val u = b ↔ Relation.ReflTransGen R (u, !b) (u, b) := by
      intro u b
      cases b
      · simp only [val, Bool.not_false, decide_eq_false_iff_not]
        constructor
        · intro hn
          rcases hforced u with h1 | h2
          · exact absurd h1 hn
          · exact h2
        · intro h2 h1
          exact hclean u ⟨h1, h2⟩
      · simp only [val, Bool.not_true, decide_eq_true_eq]
    refine ⟨val, fun u a v b hr hua => ?_⟩
    rw [hval_iff] at hua ⊢
    have hrev : R (v, !b) (u, !a) := hsym u a v b hr
    exact (Relation.ReflTransGen.head hrev hua).tail hr
  | succ k ih =>
    intro R hsym hclean hcard
    let U := (Finset.univ : Finset α).filter (fun u =>
      ¬ Relation.ReflTransGen R (u, false) (u, true) ∧
      ¬ Relation.ReflTransGen R (u, true) (u, false))
    by_cases hU : U.Nonempty
    · rcases hU with ⟨u0, hu0⟩
      have hu0p := (Finset.mem_filter.mp hu0).2
      let R' : (α × Bool) → (α × Bool) → Prop :=
        fun p q => R p q ∨ (p = (u0, false) ∧ q = (u0, true))
      have hsym' : ∀ u a v b, R' (u, a) (v, b) → R' (v, !b) (u, !a) := by
        intro u a v b hr
        rcases hr with h | ⟨h1, h2⟩
        · exact Or.inl (hsym u a v b h)
        · rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
          rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
          exact Or.inr ⟨rfl, rfl⟩
      have hclean' : ∀ u : α, ¬ (Relation.ReflTransGen R' (u, false) (u, true) ∧
          Relation.ReflTransGen R' (u, true) (u, false)) :=
        twosat_add_force R hclean u0 true hu0p.2
      let U' := (Finset.univ : Finset α).filter (fun u =>
        ¬ Relation.ReflTransGen R' (u, false) (u, true) ∧
        ¬ Relation.ReflTransGen R' (u, true) (u, false))
      have hsub : U' ⊆ U.erase u0 := by
        intro u hu
        have hup := (Finset.mem_filter.mp hu).2
        have hmono : ∀ x y, Relation.ReflTransGen R x y → Relation.ReflTransGen R' x y := by
          intro x y h
          induction h with
          | refl => exact .refl
          | tail _ hr ih => exact ih.tail (Or.inl hr)
        have hne : u ≠ u0 := by
          rintro rfl
          exact hup.1 (Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl⟩))
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ u,
          fun h => hup.1 (hmono _ _ h), fun h => hup.2 (hmono _ _ h)⟩⟩
      have hUcard : U.card ≤ k + 1 := hcard
      have hcard' : U'.card ≤ k := by
        have h1 : U'.card ≤ (U.erase u0).card := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hu0] at h1
        omega
      rcases ih R' hsym' hclean' hcard' with ⟨val, hval⟩
      exact ⟨val, fun u a v b hr => hval u a v b (Or.inl hr)⟩
    · have hU0 : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
      exact ih R hsym hclean (by change U.card ≤ k; omega)

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepWire w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hlt : k < (stepWire w g).length := by simp [stepWire]; omega
    rw [List.foldl_cons, ih (stepWire w g) hlt]
    simp only [stepWire, List.getD_append _ _ _ _ hk]

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWire w g)]
    simp [stepWire]; omega

private lemma gate_eval_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : List Bool) (hle : ∀ k, u.getD k false = true → v.getD k false = true) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = true →
    g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with h | h
  · rw [h]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id_eq]
    intro hall i hi
    exact hle i (hall i hi)
  · rw [h]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
    rintro ⟨i, hi, hui⟩
    exact ⟨i, hi, hle i hui⟩

private lemma circuit_mono (C : Circuit) (hmono : Monotone2 C) (u v : List Bool)
    (hlen : u.length = v.length)
    (hle : ∀ k, u.getD k false = true → v.getD k false = true) :
    ∀ k, (C.wires u).getD k false = true → (C.wires v).getD k false = true := by
  unfold Circuit.wires
  suffices ∀ (gs : List Gate) (u v : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      u.length = v.length →
      (∀ k, u.getD k false = true → v.getD k false = true) →
      ∀ k, (gs.foldl stepWire u).getD k false = true → (gs.foldl stepWire v).getD k false = true by
    exact this C.gates u v (fun g hg => (hmono g hg).1) hlen hle
  intro gs
  induction gs with
  | nil => intro u v _ _ hle; exact hle
  | cons g gs ih =>
    intro u v hg hlen hle
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stepWire u g) (stepWire v g) (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
      (by simp [stepWire, hlen])
    intro k hk
    by_cases hlt : k < u.length
    · have hltv : k < v.length := hlen ▸ hlt
      simp only [stepWire, List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hltv] at hk ⊢
      exact hle k hk
    · have hge : u.length ≤ k := by omega
      have hgev : v.length ≤ k := hlen ▸ hge
      simp only [stepWire, List.getD_append_right _ _ _ _ hge,
        List.getD_append_right _ _ _ _ hgev, hlen] at hk ⊢
      cases hdiff : k - v.length with
      | zero =>
        rw [hdiff] at hk
        simp only [List.getD_cons_zero] at hk ⊢
        exact gate_eval_mono g (hg g (List.mem_cons_self ..)) u v hle hk
      | succ d =>
        rw [hdiff] at hk
        simp at hk

private def buildAndLoop (n : ℕ) (s : Finset (Fin n)) :
    ℕ → List (Fin n) → List Gate × ℕ → List Gate × ℕ
  | _, [], acc => acc
  | base, j :: rest, (gs, cur) =>
    if j ∈ s then
      let g : Gate := ⟨GateOp.and, [cur, j.val]⟩
      buildAndLoop n s base rest (gs ++ [g], base + gs.length)
    else
      buildAndLoop n s base rest (gs, cur)

private lemma buildAndLoop_spec (n : ℕ) (s : Finset (Fin n)) (base : ℕ) :
    ∀ (js : List (Fin n)) (gs : List Gate) (cur : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ idx < gs.length, ∀ w ∈ (gs.getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx) →
      cur < base + gs.length →
      n + 2 ≤ base →
      let res := buildAndLoop n s base js (gs, cur)
      gs.length ≤ res.1.length ∧
      res.1.length ≤ gs.length + js.length ∧
      res.2 < base + res.1.length ∧
      (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ idx < res.1.length, ∀ w ∈ (res.1.getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx) ∧
      (∀ (w0 : List Bool), w0.length = base →
        (∀ j : Fin n, w0.getD j.val false = decide (j ∈ s) → True) →
        ∀ (xr : Finset (Fin n)),
          (∀ j : Fin n, w0.getD j.val false = decide (j ∈ xr)) →
          (res.1.foldl stepWire w0).getD res.2 false =
            ((gs.foldl stepWire w0).getD cur false && decide (∀ j ∈ js, j ∈ s → j ∈ xr))) := by
  intro js
  induction js with
  | nil =>
    intro gs cur hmono hrb hcur hbase
    refine ⟨le_refl _, by simp [buildAndLoop], hcur, hmono, hrb, fun w0 _ _ xr _ => ?_⟩
    simp [buildAndLoop]
  | cons j rest ih =>
    intro gs cur hmono hrb hcur hbase
    dsimp only [buildAndLoop]
    by_cases hj : j ∈ s
    · simp only [hj, ↓reduceIte]
      let g : Gate := ⟨GateOp.and, [cur, j.val]⟩
      have hmono' : ∀ g' ∈ gs ++ [g], g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        rcases List.mem_append.mp hg' with h1 | h2
        · exact hmono g' h1
        · rw [List.mem_singleton.mp h2]; simp [g]
      have hrb' : ∀ idx < (gs ++ [g]).length, ∀ w ∈ ((gs ++ [g]).getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx := by
        intro idx hidx w hw
        by_cases hlt : idx < gs.length
        · rw [List.getD_append _ _ _ _ hlt] at hw
          exact hrb idx hlt w hw
        · have heq : idx = gs.length := by simp at hidx; omega
          subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hw
          simp only [Nat.sub_self, List.getD_cons_zero, g, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hcur
          · have := j.isLt; omega
      have hcur' : base + gs.length < base + (gs ++ [g]).length := by simp
      rcases ih (gs ++ [g]) (base + gs.length) hmono' hrb' hcur' hbase with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      dsimp only [g] at hge hle hres_lt hres_mono hres_rb hres_ev
      refine ⟨by simp at hge; omega, by simp at hle ⊢; omega, hres_lt, hres_mono, hres_rb, ?_⟩
      intro w0 hw0 _ xr hxr
      rw [hres_ev w0 hw0 (fun _ _ => trivial) xr hxr]
      have hstep : ((gs ++ [g]).foldl stepWire w0).getD (base + gs.length) false =
          ((gs.foldl stepWire w0).getD cur false && decide (j ∈ xr)) := by
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl stepWire w0).length = base + gs.length := by
          rw [foldl_length, hw0]
        simp only [stepWire, List.getD_append_right _ _ _ _ (le_of_eq hlen), hlen, Nat.sub_self,
          List.getD_cons_zero, g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true]
        have hjlt : j.val < w0.length := by rw [hw0]; have := j.isLt; omega
        rw [foldl_getD_lt gs w0 j.val hjlt, hxr j]
      rw [hstep]
      by_cases h2 : j ∈ xr <;>
        by_cases h3 : ∀ j' ∈ rest, j' ∈ s → j' ∈ xr <;>
        simp [hj, h2, h3]
    · simp only [hj, ↓reduceIte]
      rcases ih gs cur hmono hrb hcur hbase with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      refine ⟨hge, by simp at hle ⊢; omega, hres_lt, hres_mono, hres_rb, ?_⟩
      intro w0 hw0 _ xr hxr
      rw [hres_ev w0 hw0 (fun _ _ => trivial) xr hxr]
      simp [hj]

private def buildOrLoop (base : ℕ) (ind : Fin m → ℕ) (sel : Fin m → Bool) :
    List (Fin m) → List Gate × ℕ → List Gate × ℕ
  | [], acc => acc
  | i :: rest, (gs, cur) =>
    if sel i = true then
      let g : Gate := ⟨GateOp.or, [cur, ind i]⟩
      buildOrLoop base ind sel rest (gs ++ [g], base + gs.length)
    else
      buildOrLoop base ind sel rest (gs, cur)

private lemma buildOrLoop_spec {m : ℕ} (base : ℕ) (ind : Fin m → ℕ) (sel : Fin m → Bool) :
    ∀ (is : List (Fin m)) (gs : List Gate) (cur : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ idx < gs.length, ∀ w ∈ (gs.getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx) →
      cur < base + gs.length →
      (∀ i : Fin m, ind i < base + gs.length) →
      let res := buildOrLoop base ind sel is (gs, cur)
      gs.length ≤ res.1.length ∧
      res.1.length ≤ gs.length + is.length ∧
      res.2 < base + res.1.length ∧
      (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ idx < res.1.length, ∀ w ∈ (res.1.getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx) ∧
      (∀ (w0 : List Bool), w0.length = base →
        (res.1.foldl stepWire w0).getD res.2 false =
          ((gs.foldl stepWire w0).getD cur false ||
            decide (∃ i ∈ is, sel i = true ∧ (gs.foldl stepWire w0).getD (ind i) false = true))) := by
  intro is
  induction is with
  | nil =>
    intro gs cur hmono hrb hcur _
    refine ⟨le_refl _, by simp [buildOrLoop], hcur, hmono, hrb, fun w0 _ => by simp [buildOrLoop]⟩
  | cons i rest ih =>
    intro gs cur hmono hrb hcur hind
    dsimp only [buildOrLoop]
    by_cases hi : sel i = true
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      let g : Gate := ⟨GateOp.or, [cur, ind i]⟩
      have hmono' : ∀ g' ∈ gs ++ [g], g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        rcases List.mem_append.mp hg' with h1 | h2
        · exact hmono g' h1
        · rw [List.mem_singleton.mp h2]; simp [g]
      have hrb' : ∀ idx < (gs ++ [g]).length, ∀ w ∈ ((gs ++ [g]).getD idx ⟨GateOp.or, []⟩).inputs, w < base + idx := by
        intro idx hidx w hw
        by_cases hlt : idx < gs.length
        · rw [List.getD_append _ _ _ _ hlt] at hw
          exact hrb idx hlt w hw
        · have heq : idx = gs.length := by simp at hidx; omega
          subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hw
          simp only [Nat.sub_self, List.getD_cons_zero, g, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hcur
          · exact hind i
      have hcur' : base + gs.length < base + (gs ++ [g]).length := by simp
      have hind' : ∀ i' : Fin m, ind i' < base + (gs ++ [g]).length := fun i' => by
        have := hind i'; simp; omega
      rcases ih (gs ++ [g]) (base + gs.length) hmono' hrb' hcur' hind' with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      dsimp only [g] at hge hle hres_lt hres_mono hres_rb hres_ev
      refine ⟨by simp at hge; omega, by simp at hle ⊢; omega, hres_lt, hres_mono, hres_rb, ?_⟩
      intro w0 hw0
      rw [hres_ev w0 hw0]
      have hlen : (gs.foldl stepWire w0).length = base + gs.length := by rw [foldl_length, hw0]
      have hstep : ((gs ++ [g]).foldl stepWire w0).getD (base + gs.length) false =
          ((gs.foldl stepWire w0).getD cur false || (gs.foldl stepWire w0).getD (ind i) false) := by
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [stepWire, List.getD_append_right _ _ _ _ (le_of_eq hlen), hlen, Nat.sub_self,
          List.getD_cons_zero, g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
      have hpres : ∀ i' : Fin m, ((gs ++ [g]).foldl stepWire w0).getD (ind i') false =
          (gs.foldl stepWire w0).getD (ind i') false := by
        intro i'
        rw [List.foldl_append]
        exact foldl_getD_lt [g] (gs.foldl stepWire w0) (ind i') (by rw [hlen]; exact hind i')
      dsimp only [g] at hstep hpres
      rw [hstep]
      simp_rw [hpres]
      simp [hi, Bool.or_assoc]
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      rcases ih gs cur hmono hrb hcur hind with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      refine ⟨hge, by simp at hle ⊢; omega, hres_lt, hres_mono, hres_rb, ?_⟩
      intro w0 hw0
      rw [hres_ev w0 hw0]
      simp [hi]

private lemma build_monotone_circuit {n m t : ℕ} (x : Fin m → Finset (Fin n))
    (val : Fin m → Fin t → Bool)
    (hmono : ∀ i j k, x i ⊆ x j → val i k = true → val j k = true) :
    ∃ (C : Circuit) (p : Fin t → ℕ),
      Monotone2 C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      (∀ k, p k < n + 2 + C.size) ∧ C.size ≤ (n + t) * m ∧
      ∀ (i : Fin m) (k : Fin t),
        (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false, true])).getD (p k) false =
        val i k := by
  have hphase1 : ∀ (q : ℕ) (hq : q ≤ m),
      ∃ (gs : List Gate) (ind : Fin q → ℕ),
        gs.length ≤ n * q ∧
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ idx < gs.length, ∀ w ∈ (gs.getD idx ⟨GateOp.or, []⟩).inputs, w < n + 2 + idx) ∧
        (∀ i : Fin q, ind i < n + 2 + gs.length) ∧
        (∀ (r : Fin m) (i : Fin q),
          let w0 := List.ofFn (fun j : Fin n => decide (j ∈ x r)) ++ [false, true]
          (gs.foldl stepWire w0).getD (ind i) false = decide (x ⟨i.val, by omega⟩ ⊆ x r)) := by
    intro q
    induction q with
    | zero =>
      intro _
      exact ⟨[], Fin.elim0, by simp, (fun _ h => by cases h), (fun _ h => by simp at h),
        fun i => Fin.elim0 i, fun _ i => Fin.elim0 i⟩
    | succ q ih =>
      intro hq
      rcases ih (Nat.le_of_succ_le hq) with ⟨gs, ind, hlen, hgm, hrb, hind, hev⟩
      let i0 : Fin m := ⟨q, hq⟩
      let res := buildAndLoop n (x i0) (n + 2) (List.finRange n) (gs, n + 1)
      have hcur_lt : n + 1 < n + 2 + gs.length := by omega
      rcases buildAndLoop_spec n (x i0) (n + 2) (List.finRange n) gs (n + 1) hgm hrb hcur_lt (le_refl _) with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      have hprefix : ∃ tail : List Gate, res.1 = gs ++ tail := by
        suffices ∀ (js : List (Fin n)) (gs0 : List Gate) (cur0 : ℕ),
            ∃ tail : List Gate, (buildAndLoop n (x i0) (n + 2) js (gs0, cur0)).1 = gs0 ++ tail from
          this (List.finRange n) gs (n + 1)
        intro js
        induction js with
        | nil => intro gs0 _; exact ⟨[], by simp [buildAndLoop]⟩
        | cons j rest ihr =>
          intro gs0 cur0
          dsimp only [buildAndLoop]
          split_ifs
          · rcases ihr (gs0 ++ [⟨GateOp.and, [cur0, j.val]⟩]) (n + 2 + gs0.length) with ⟨t1, ht1⟩
            exact ⟨⟨GateOp.and, [cur0, j.val]⟩ :: t1, by rw [ht1, List.append_assoc]; rfl⟩
          · exact ihr gs0 cur0
      rcases hprefix with ⟨tail, htail⟩
      let ind' : Fin (q + 1) → ℕ := Fin.snoc ind res.2
      refine ⟨res.1, ind', ?_, hres_mono, hres_rb, ?_, ?_⟩
      · have hfr : (List.finRange n).length = n := List.length_finRange
        rw [hfr] at hle
        calc res.1.length ≤ gs.length + n := hle
          _ ≤ n * q + n := Nat.add_le_add_right hlen n
          _ = n * (q + 1) := by ring
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [ind', Fin.snoc_last]; exact hres_lt
        · simp only [ind', Fin.snoc_castSucc]; have h1 := hind i'; have h2 : gs.length ≤ res.1.length := hge; omega
      · intro r i
        let w0 := List.ofFn (fun j : Fin n => decide (j ∈ x r)) ++ [false, true]
        have hw0_len : w0.length = n + 2 := by simp [w0]
        have hw0_j : ∀ j : Fin n, w0.getD j.val false = decide (j ∈ x r) := by
          intro j
          have hlt : j.val < (List.ofFn (fun j : Fin n => decide (j ∈ x r))).length := by simp
          simp only [w0, List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        have hw0_true : (gs.foldl stepWire w0).getD (n + 1) false = true := by
          have hlt : n + 1 < w0.length := by omega
          rw [foldl_getD_lt gs w0 (n + 1) hlt]
          have hge_n : (List.ofFn (fun j : Fin n => decide (j ∈ x r))).length ≤ n + 1 := by simp
          simp only [w0, List.getD_append_right _ _ _ _ hge_n, List.length_ofFn]
          have hsub : n + 1 - n = 1 := by omega
          rw [hsub]; rfl
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [ind', Fin.snoc_last]
          rw [hres_ev w0 hw0_len (fun _ _ => trivial) (x r) hw0_j, hw0_true, Bool.true_and]
          exact decide_eq_decide.mpr (by simp [Finset.subset_iff, i0])
        · simp only [ind', Fin.snoc_castSucc]
          rw [htail, List.foldl_append]
          have hlen_gs : (gs.foldl stepWire w0).length = n + 2 + gs.length := by
            rw [foldl_length, hw0_len]
          rw [foldl_getD_lt tail (gs.foldl stepWire w0) (ind i') (by rw [hlen_gs]; exact hind i')]
          exact hev r i'
  rcases hphase1 m (le_refl m) with ⟨gs1, ind, hlen1, hgm1, hrb1, hind1, hev1⟩
  have hphase2 : ∀ (q : ℕ) (hq : q ≤ t),
      ∃ (gs : List Gate) (p : Fin q → ℕ),
        gs.length ≤ gs1.length + q * m ∧
        (∃ tail : List Gate, gs = gs1 ++ tail) ∧
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ idx < gs.length, ∀ w ∈ (gs.getD idx ⟨GateOp.or, []⟩).inputs, w < n + 2 + idx) ∧
        (∀ k : Fin q, p k < n + 2 + gs.length) ∧
        (∀ (r : Fin m) (k : Fin q),
          let w0 := List.ofFn (fun j : Fin n => decide (j ∈ x r)) ++ [false, true]
          (gs.foldl stepWire w0).getD (p k) false = val r ⟨k.val, by omega⟩) := by
    intro q
    induction q with
    | zero =>
      intro _
      exact ⟨gs1, Fin.elim0, by simp, ⟨[], by simp⟩, hgm1, hrb1,
        fun k => Fin.elim0 k, fun _ k => Fin.elim0 k⟩
    | succ q ih =>
      intro hq
      rcases ih (Nat.le_of_succ_le hq) with ⟨gs, p, hlen, ⟨tail0, hgs_eq⟩, hgm, hrb, hp, hev⟩
      let k0 : Fin t := ⟨q, hq⟩
      let sel : Fin m → Bool := fun i => val i k0
      let res := buildOrLoop (n + 2) ind sel (List.finRange m) (gs, n)
      have hcur_lt : n < n + 2 + gs.length := by omega
      have hind_gs : ∀ i : Fin m, ind i < n + 2 + gs.length := fun i => by
        have := hind1 i; rw [hgs_eq, List.length_append]; omega
      rcases buildOrLoop_spec (n + 2) ind sel (List.finRange m) gs n hgm hrb hcur_lt hind_gs with
        ⟨hge, hle, hres_lt, hres_mono, hres_rb, hres_ev⟩
      have hprefix : ∃ tail : List Gate, res.1 = gs ++ tail := by
        suffices ∀ (is : List (Fin m)) (gs0 : List Gate) (cur0 : ℕ),
            ∃ tail : List Gate, (buildOrLoop (n + 2) ind sel is (gs0, cur0)).1 = gs0 ++ tail from
          this (List.finRange m) gs n
        intro is
        induction is with
        | nil => intro gs0 _; exact ⟨[], by simp [buildOrLoop]⟩
        | cons i rest ihr =>
          intro gs0 cur0
          dsimp only [buildOrLoop]
          split_ifs
          · rcases ihr (gs0 ++ [⟨GateOp.or, [cur0, ind i]⟩]) (n + 2 + gs0.length) with ⟨t1, ht1⟩
            exact ⟨⟨GateOp.or, [cur0, ind i]⟩ :: t1, by rw [ht1, List.append_assoc]; rfl⟩
          · exact ihr gs0 cur0
      rcases hprefix with ⟨tail, htail⟩
      let p' : Fin (q + 1) → ℕ := Fin.snoc p res.2
      refine ⟨res.1, p', ?_, ⟨tail0 ++ tail, by rw [htail, hgs_eq, List.append_assoc]⟩,
        hres_mono, hres_rb, ?_, ?_⟩
      · have hfr : (List.finRange m).length = m := List.length_finRange
        rw [hfr] at hle
        calc res.1.length ≤ gs.length + m := hle
          _ ≤ gs1.length + q * m + m := Nat.add_le_add_right hlen m
          _ = gs1.length + (q + 1) * m := by ring
      · intro k
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · simp only [p', Fin.snoc_last]; exact hres_lt
        · simp only [p', Fin.snoc_castSucc]; have h1 := hp k'; have h2 : gs.length ≤ res.1.length := hge; omega
      · intro r k
        let w0 := List.ofFn (fun j : Fin n => decide (j ∈ x r)) ++ [false, true]
        have hw0_len : w0.length = n + 2 := by simp [w0]
        have hw0_false : (gs.foldl stepWire w0).getD n false = false := by
          have hlt : n < w0.length := by omega
          rw [foldl_getD_lt gs w0 n hlt]
          have hge_n : (List.ofFn (fun j : Fin n => decide (j ∈ x r))).length ≤ n := by simp
          simp only [w0, List.getD_append_right _ _ _ _ hge_n, List.length_ofFn, Nat.sub_self]
          rfl
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · simp only [p', Fin.snoc_last]
          rw [hres_ev w0 hw0_len, hw0_false, Bool.false_or]
          have hind_ev : ∀ i : Fin m, (gs.foldl stepWire w0).getD (ind i) false = decide (x i ⊆ x r) := by
            intro i
            rw [hgs_eq, List.foldl_append]
            have hlen_gs1 : (gs1.foldl stepWire w0).length = n + 2 + gs1.length := by
              rw [foldl_length, hw0_len]
            rw [foldl_getD_lt tail0 (gs1.foldl stepWire w0) (ind i) (by rw [hlen_gs1]; exact hind1 i)]
            exact hev1 r i
          simp_rw [hind_ev]
          change _ = val r k0
          cases hvr : val r k0
          · rw [decide_eq_false_iff_not]
            rintro ⟨i, _, hvi, hsub⟩
            have h1 := hmono i r k0 (of_decide_eq_true hsub) hvi
            rw [hvr] at h1
            exact Bool.noConfusion h1
          · rw [decide_eq_true_eq]
            exact ⟨r, List.mem_finRange r, hvr, decide_eq_true (Finset.Subset.refl _)⟩
        · simp only [p', Fin.snoc_castSucc]
          rw [htail, List.foldl_append]
          have hlen_gs : (gs.foldl stepWire w0).length = n + 2 + gs.length := by
            rw [foldl_length, hw0_len]
          rw [foldl_getD_lt tail (gs.foldl stepWire w0) (p k') (by rw [hlen_gs]; exact hp k')]
          exact hev r k'
  rcases hphase2 t (le_refl t) with ⟨gs, p, hlen2, _, hgm, hrb, hp, hev⟩
  let C : Circuit := ⟨gs, 0⟩
  have hCsize : C.size ≤ (n + t) * m := by
    change gs.length ≤ (n + t) * m
    calc gs.length ≤ gs1.length + t * m := hlen2
      _ ≤ n * m + t * m := Nat.add_le_add_right hlen1 _
      _ = (n + t) * m := by ring
  refine ⟨C, p, hgm, hrb, by simp [C], hp, hCsize, ?_⟩
  intro i k
  exact hev i k

open scoped Classical in
private lemma main_proof (n m t : ℕ) (x : Fin m → Finset (Fin n)) (ok : Fin m → (Fin t → Bool) → Prop)
    (hne : ∀ i, ∃ z, ok i z)
    (hmaj : ∀ i a b c, ok i a → ok i b → ok i c →
      ok i (fun k => (a k && b k) || (a k && c k) || (b k && c k))) :
    let arc := fun (p q : Fin m × Fin t × Bool) =>
      (∃ (i j : Fin m) (k : Fin t), x i ⊆ x j ∧
        ((p = (i,k,true) ∧ q = (j,k,true)) ∨ (p = (j,k,false) ∧ q = (i,k,false)))) ∨
      (∃ (i : Fin m) (k l : Fin t) (a b : Bool),
        (¬ ∃ z, ok i z ∧ z k = a ∧ z l = b) ∧ p = (i,k,a) ∧ q = (i,l,!b))
    let reach := Relation.ReflTransGen arc
    let clean := ∀ (i : Fin m) (k : Fin t),
      ¬ (reach (i,k,false) (i,k,true) ∧ reach (i,k,true) (i,k,false))
    let wire := fun (C : Circuit) (i : Fin m) (k : ℕ) =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD k false
    let fits := fun (C : Circuit) (p : Fin t → ℕ) =>
      Monotone2 C ∧ ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ k, p k < n+2+C.size) ∧
      ∀ i, ok i (fun k => wire C i (p k))
    (clean ↔ ∃ C p, fits C p) ∧ (clean → ∃ C p, fits C p ∧ C.size ≤ (n+t)*m) ∧
    (clean → ∀ (i : Fin m) (k : Fin t) (v : Bool), ¬ reach (i,k,v) (i,k,!v) ↔
      ∃ C p, fits C p ∧ C.size ≤ (n+t)*m ∧ wire C i (p k) = v) := by
  intro arc reach clean wire fits
  let R : ((Fin m × Fin t) × Bool) → ((Fin m × Fin t) × Bool) → Prop :=
    fun p q => arc (p.1.1, p.1.2, p.2) (q.1.1, q.1.2, q.2)
  have hR_sym : ∀ u a v b, R (u, a) (v, b) → R (v, !b) (u, !a) := by
    intro ⟨i, k⟩ a ⟨j, l⟩ b hr
    rcases hr with ⟨i', j', k', hsub, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨i', k', l', a', b', hno, h1, h2⟩
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      exact Or.inl ⟨i, j, l, hsub, Or.inr ⟨rfl, rfl⟩⟩
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      exact Or.inl ⟨j, i, l, hsub, Or.inl ⟨rfl, rfl⟩⟩
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      refine Or.inr ⟨j, l, k, b', a, ?_, by simp, rfl⟩
      rintro ⟨z, hz, h1, h2⟩
      exact hno ⟨z, hz, h2, h1⟩
  have hR_reach_iff : ∀ i k a j l b,
      Relation.ReflTransGen R ((i, k), a) ((j, l), b) ↔ reach (i, k, a) (j, l, b) := by
    intro i k a j l b
    constructor
    · intro h
      suffices ∀ x y, Relation.ReflTransGen R x y → reach (x.1.1, x.1.2, x.2) (y.1.1, y.1.2, y.2) from
        this ((i, k), a) ((j, l), b) h
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | tail _ hr ih => exact ih.tail hr
    · intro h
      suffices ∀ x y, reach x y → Relation.ReflTransGen R ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2) from
        this (i, k, a) (j, l, b) h
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | tail _ hr ih => exact ih.tail hr
  have hval_from_fits : ∀ C p, fits C p →
      ∀ (i j : Fin m) (k l : Fin t) (a b : Bool),
        arc (i, k, a) (j, l, b) → wire C i (p k) = a → wire C j (p l) = b := by
    intro C p ⟨hmono, _, _, _, hok⟩ i j k l a b harc ha
    have hwire_mono : ∀ i' j' : Fin m, x i' ⊆ x j' → ∀ w : ℕ, wire C i' w = true → wire C j' w = true := by
      intro i' j' hsub w hw
      let u := List.ofFn (fun r : Fin n => decide (r ∈ x i')) ++ [false, true]
      let v := List.ofFn (fun r : Fin n => decide (r ∈ x j')) ++ [false, true]
      apply circuit_mono C hmono u v (by simp [u, v]) _ w hw
      intro idx hidx
      by_cases hlt : idx < n
      · have hltu : idx < (List.ofFn (fun r : Fin n => decide (r ∈ x i'))).length := by simp [hlt]
        have hltv : idx < (List.ofFn (fun r : Fin n => decide (r ∈ x j'))).length := by simp [hlt]
        simp only [u, v, List.getD_append _ _ _ _ hltu, List.getD_append _ _ _ _ hltv,
          List.getD_eq_getElem _ _ hltu, List.getD_eq_getElem _ _ hltv, List.getElem_ofFn,
          decide_eq_true_eq] at hidx ⊢
        exact hsub hidx
      · have hgeu : (List.ofFn (fun r : Fin n => decide (r ∈ x i'))).length ≤ idx := by simp; omega
        have hgev : (List.ofFn (fun r : Fin n => decide (r ∈ x j'))).length ≤ idx := by simp; omega
        simp only [u, v, List.getD_append_right _ _ _ _ hgeu, List.getD_append_right _ _ _ _ hgev,
          List.length_ofFn] at hidx ⊢
        exact hidx
    rcases harc with ⟨i', j', k', hsub, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨i', k', l', a', b', hno, h1, h2⟩
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      exact hwire_mono i j hsub (p l) ha
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      cases hjl : wire C j (p l)
      · rfl
      · have h1 := hwire_mono j i hsub (p l) hjl
        rw [ha] at h1; exact Bool.noConfusion h1
    · rcases Prod.mk.inj h1 with ⟨rfl, h1'⟩
      rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
      rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
      cases hbl : wire C j (p l)
      · cases b'
        · exfalso; exact hno ⟨fun r => wire C j (p r), hok j, ha, hbl⟩
        · rfl
      · cases b'
        · rfl
        · exfalso; exact hno ⟨fun r => wire C j (p r), hok j, ha, hbl⟩
  have hreach_from_fits : ∀ C p, fits C p →
      ∀ (i j : Fin m) (k l : Fin t) (a b : Bool),
        reach (i, k, a) (j, l, b) → wire C i (p k) = a → wire C j (p l) = b := by
    intro C p hfits i j k l a b hr
    suffices ∀ p1 p2 : Fin m × Fin t × Bool, reach p1 p2 →
        wire C p1.1 (p p1.2.1) = p1.2.2 → wire C p2.1 (p p2.2.1) = p2.2.2 from
      this (i, k, a) (j, l, b) hr
    intro p1 p2 hr
    induction hr with
    | refl => exact id
    | tail _ harc ih =>
      intro h1
      exact hval_from_fits C p hfits _ _ _ _ _ _ harc (ih h1)
  have hclean_of_fits : (∃ C p, fits C p) → clean := by
    rintro ⟨C, p, hfits⟩ i k ⟨hFT, hTF⟩
    cases hv : wire C i (p k)
    · have h1 := hreach_from_fits C p hfits i i k k false true hFT hv
      rw [hv] at h1; exact Bool.noConfusion h1
    · have h1 := hreach_from_fits C p hfits i i k k true false hTF hv
      rw [hv] at h1; exact Bool.noConfusion h1
  have hcircuit_of_val : ∀ val : (Fin m × Fin t) → Bool,
      (∀ u a v b, R (u, a) (v, b) → val u = a → val v = b) →
      ∃ C p, fits C p ∧ C.size ≤ (n + t) * m ∧ ∀ i k, wire C i (p k) = val (i, k) := by
    intro val hval
    have hmono_val : ∀ i j k, x i ⊆ x j → val (i, k) = true → val (j, k) = true :=
      fun i j k hsub hi => hval (i, k) true (j, k) true (Or.inl ⟨i, j, k, hsub, Or.inl ⟨rfl, rfl⟩⟩) hi
    have hok_val : ∀ i : Fin m, ok i (fun k => val (i, k)) := by
      intro i
      apply ok_of_pairs (ok i) (hne i) (hmaj i) (fun k => val (i, k))
      intro k l
      by_contra hno
      have hr : R ((i, k), val (i, k)) ((i, l), !(val (i, l))) :=
        Or.inr ⟨i, k, l, val (i, k), val (i, l), hno, rfl, rfl⟩
      have hbad := hval (i, k) (val (i, k)) (i, l) (!(val (i, l))) hr rfl
      cases h : val (i, l) <;> simp [h] at hbad
    rcases build_monotone_circuit x (fun i k => val (i, k)) hmono_val with
      ⟨C, p, hCm, hCrb, hCout, hCp, hCsize, hCev⟩
    refine ⟨C, p, ⟨hCm, hCrb, hCout, hCp, fun i => ?_⟩, hCsize, hCev⟩
    have heq : (fun k => wire C i (p k)) = (fun k => val (i, k)) := funext fun k => hCev i k
    rw [heq]
    exact hok_val i
  have hclean_to_circ : clean → ∃ C p, fits C p ∧ C.size ≤ (n + t) * m := by
    intro hcl
    have hclR : ∀ u : Fin m × Fin t, ¬ (Relation.ReflTransGen R (u, false) (u, true) ∧
        Relation.ReflTransGen R (u, true) (u, false)) := by
      intro ⟨i, k⟩ ⟨h1, h2⟩
      exact hcl i k ⟨(hR_reach_iff i k false i k true).mp h1, (hR_reach_iff i k true i k false).mp h2⟩
    rcases twosat_solve (Fintype.card (Fin m × Fin t)) R hR_sym hclR (Finset.card_filter_le _ _) with
      ⟨val, hval⟩
    rcases hcircuit_of_val val hval with ⟨C, p, hfits, hsz, _⟩
    exact ⟨C, p, hfits, hsz⟩
  refine ⟨⟨fun hcl => by rcases hclean_to_circ hcl with ⟨C, p, hfits, _⟩; exact ⟨C, p, hfits⟩,
    hclean_of_fits⟩, hclean_to_circ, ?_⟩
  intro hcl i k v
  constructor
  · intro hnot
    have hclR : ∀ u : Fin m × Fin t, ¬ (Relation.ReflTransGen R (u, false) (u, true) ∧
        Relation.ReflTransGen R (u, true) (u, false)) := by
      intro ⟨i', k'⟩ ⟨h1, h2⟩
      exact hcl i' k' ⟨(hR_reach_iff i' k' false i' k' true).mp h1, (hR_reach_iff i' k' true i' k' false).mp h2⟩
    have hnotR : ¬ Relation.ReflTransGen R ((i, k), v) ((i, k), !v) := fun h =>
      hnot ((hR_reach_iff i k v i k (!v)).mp h)
    let R' : ((Fin m × Fin t) × Bool) → ((Fin m × Fin t) × Bool) → Prop :=
      fun p q => R p q ∨ (p = ((i, k), !v) ∧ q = ((i, k), v))
    have hsym' : ∀ u a w b, R' (u, a) (w, b) → R' (w, !b) (u, !a) := by
      intro u a w b hr
      rcases hr with h | ⟨h1, h2⟩
      · exact Or.inl (hR_sym u a w b h)
      · rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
        rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact Or.inr ⟨rfl, by simp⟩
    have hclR' := twosat_add_force R hclR (i, k) v hnotR
    rcases twosat_solve (Fintype.card (Fin m × Fin t)) R' hsym' hclR' (Finset.card_filter_le _ _) with
      ⟨val, hval⟩
    have hval_ik : val (i, k) = v := by
      cases hv : val (i, k)
      · cases v
        · rfl
        · have h1 := hval (i, k) false (i, k) true (Or.inr ⟨rfl, rfl⟩) hv
          rw [hv] at h1; exact Bool.noConfusion h1
      · cases v
        · have h1 := hval (i, k) true (i, k) false (Or.inr ⟨rfl, rfl⟩) hv
          rw [hv] at h1; exact Bool.noConfusion h1
        · rfl
    rcases hcircuit_of_val val (fun u a w b hr => hval u a w b (Or.inl hr)) with ⟨C, p, hfits, hsz, hev⟩
    exact ⟨C, p, hfits, hsz, (hev i k).trans hval_ik⟩
  · rintro ⟨C, p, hfits, _, hv⟩ hr
    have hbad := hreach_from_fits C p hfits i i k k v (!v) hr hv
    rw [hv] at hbad
    cases v <;> exact Bool.noConfusion hbad

end PEqualNP.Outside.L_lib_1287_aux

theorem PEqualNP.Outside.L_lib_1287 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t : Nat) (x : Fin m → Finset (Fin n)) (ok : Fin m → (Fin t → Bool) → Prop),
  (∀ i, ∃ z, ok i z) →
  (∀ i a b c, ok i a → ok i b → ok i c →
    ok i (fun k => (a k && b k) || (a k && c k) || (b k && c k))) →
  let arc := fun (p q : Fin m × Fin t × Bool) =>
    (∃ (i j : Fin m) (k : Fin t), x i ⊆ x j ∧
      ((p = (i,k,true) ∧ q = (j,k,true)) ∨ (p = (j,k,false) ∧ q = (i,k,false)))) ∨
    (∃ (i : Fin m) (k l : Fin t) (a b : Bool),
      (¬ ∃ z, ok i z ∧ z k = a ∧ z l = b) ∧ p = (i,k,a) ∧ q = (i,l,!b))
  let reach := Relation.ReflTransGen arc
  let clean := ∀ (i : Fin m) (k : Fin t),
    ¬ (reach (i,k,false) (i,k,true) ∧ reach (i,k,true) (i,k,false))
  let wire := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin m) (k : Nat) =>
    (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD k false
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Nat) =>
    PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ k, p k < n+2+C.size) ∧
    ∀ i, ok i (fun k => wire C i (p k))
  (clean ↔ ∃ C p, fits C p) ∧ (clean → ∃ C p, fits C p ∧ C.size ≤ (n+t)*m) ∧
  (clean → ∀ (i : Fin m) (k : Fin t) (v : Bool), ¬ reach (i,k,v) (i,k,!v) ↔
    ∃ C p, fits C p ∧ C.size ≤ (n+t)*m ∧ wire C i (p k) = v)) := by
  intro n m t x ok hne hmaj arc reach clean wire fits
  have hdec : ∀ (i : Fin m) (j : Fin n),
      @decide (j ∈ x i) (Classical.propDecidable _) = @decide (j ∈ x i) (Finset.decidableMem j (x i)) :=
    fun i j => by by_cases h : j ∈ x i <;> simp [h]
  have hm := PEqualNP.Outside.L_lib_1287_aux.main_proof n m t x ok hne hmaj
  have hwire_eq : ∀ C i k, wire C i k =
      (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Finset.decidableMem j (x i))) ++ [false, true])).getD k false :=
    fun C i k => by simp only [wire, hdec]
  have hfits_eq : ∀ C p, fits C p ↔
      (PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
        C.output < n + 2 + C.size ∧ (∀ k, p k < n + 2 + C.size) ∧
        ∀ i, ok i (fun k => (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ x i) (Finset.decidableMem j (x i))) ++ [false, true])).getD (p k) false)) :=
    fun C p => by simp only [fits, hwire_eq]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hfits_eq] using hm.1
  · simpa only [hfits_eq] using hm.2.1
  · intro hcl i k v
    simpa only [hfits_eq, hwire_eq] using hm.2.2 hcl i k v
