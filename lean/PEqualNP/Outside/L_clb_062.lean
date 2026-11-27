import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_062_aux

open PEqualNP.CircuitLowerBounds

def evalGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def notCountList (gs : List Gate) : ℕ :=
  (gs.filter fun g => match g.op with | GateOp.not => true | _ => false).length

theorem evalGates_nil (x : List Bool) : evalGates [] x = x := rfl

theorem evalGates_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    evalGates (gs ++ [g]) x =
      evalGates gs x ++ [g.op.eval (g.inputs.map fun i => (evalGates gs x).getD i false)] := by
  simp [evalGates, List.foldl_append]

theorem evalGates_length (gs : List Gate) (x : List Bool) :
    (evalGates gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [evalGates]
  | append_singleton gs g ih =>
    rw [evalGates_append_singleton, List.length_append, List.length_singleton,
      List.length_append, List.length_singleton, ih]
    omega

theorem getD_append_left {α : Type} (l₁ l₂ : List α) (d : α) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

theorem getD_append_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_eq_default_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

theorem notCountList_append_singleton (gs : List Gate) (g : Gate) :
    notCountList (gs ++ [g]) =
      notCountList gs + match g.op with | GateOp.not => 1 | _ => 0 := by
  unfold notCountList
  rw [List.filter_append, List.length_append]
  rcases g with ⟨op, ins⟩
  cases op <;> simp

theorem exists_drop_between_aux {L : ℕ} (v : Fin (L + 1) → Bool) :
    ∀ (d a : ℕ) (hb : a + d ≤ L),
      v ⟨a, by omega⟩ = true → v ⟨a + d, by omega⟩ = false →
      ∃ s : Fin L, a ≤ s.val ∧ s.val < a + d ∧ v s.castSucc = true ∧ v s.succ = false
  | 0, a, hb, ha, hbf => by
    simp only [Nat.add_zero] at hbf
    rw [ha] at hbf
    cases hbf
  | d + 1, a, hb, ha, hbf => by
    by_cases hnext : v ⟨a + 1, by omega⟩ = false
    · refine ⟨⟨a, by omega⟩, le_refl _, by simp, ha, ?_⟩
      simpa [Fin.succ] using hnext
    · have ht : v ⟨a + 1, by omega⟩ = true := by
        cases h : v ⟨a + 1, by omega⟩
        · exact absurd h hnext
        · rfl
      have hbf' : v ⟨a + 1 + d, by omega⟩ = false := by
        have heq : (⟨a + 1 + d, by omega⟩ : Fin (L + 1)) = ⟨a + (d + 1), by omega⟩ := by
          ext; simp; omega
        rw [heq]; exact hbf
      obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_drop_between_aux v d (a + 1) (by omega) ht hbf'
      exact ⟨s, by omega, by omega, hs3, hs4⟩

theorem exists_drop_between {L : ℕ} (v : Fin (L + 1) → Bool)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ L)
    (ha : v ⟨a, by omega⟩ = true) (hbf : v ⟨b, by omega⟩ = false) :
    ∃ s : Fin L, a ≤ s.val ∧ s.val < b ∧ v s.castSucc = true ∧ v s.succ = false := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact exists_drop_between_aux v d a hb ha hbf

theorem card_le_succ_of_between {L : ℕ} :
    ∀ (m : ℕ) (S T : Finset (Fin L)), T.card = m →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ < t₂ → ∃ s ∈ S, t₁ < s ∧ s < t₂) →
      T.card ≤ S.card + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro S T hcard hbet
    by_cases hTe : T = ∅
    · subst hTe; simp
    · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTe
      let mx := T.max' hTne
      have hmx_mem : mx ∈ T := Finset.max'_mem T hTne
      let T' := T.erase mx
      have hT'_card : T'.card + 1 = T.card := by
        have h1 : T'.card = T.card - 1 := Finset.card_erase_of_mem hmx_mem
        have hpos : 0 < T.card := Finset.card_pos.mpr hTne
        omega
      by_cases hT'e : T' = ∅
      · have : T'.card = 0 := by simp [hT'e]
        omega
      · have hT'ne : T'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT'e
        let mx' := T'.max' hT'ne
        have hmx'_mem' : mx' ∈ T' := Finset.max'_mem T' hT'ne
        have hmx'_ne : mx' ≠ mx := (Finset.mem_erase.mp hmx'_mem').1
        have hmx'_mem : mx' ∈ T := (Finset.mem_erase.mp hmx'_mem').2
        have hmx'_lt : mx' < mx := lt_of_le_of_ne (Finset.le_max' T mx' hmx'_mem) hmx'_ne
        obtain ⟨s, hsS, hmx'_s, hs_mx⟩ := hbet mx' hmx'_mem mx hmx_mem hmx'_lt
        let S' := S.filter (· < s)
        have hS'_sub : S' ⊂ S := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro heq
          have : s ∈ S' := heq ▸ hsS
          exact lt_irrefl s (Finset.mem_filter.mp this).2
        have hS'_lt : S'.card < S.card := Finset.card_lt_card hS'_sub
        have hbet' : ∀ t₁ ∈ T', ∀ t₂ ∈ T', t₁ < t₂ → ∃ u ∈ S', t₁ < u ∧ u < t₂ := by
          intro t₁ ht₁ t₂ ht₂ h12
          obtain ⟨u, huS, h1u, hu2⟩ :=
            hbet t₁ (Finset.mem_of_mem_erase ht₁) t₂ (Finset.mem_of_mem_erase ht₂) h12
          have ht₂_le : t₂ ≤ mx' := Finset.le_max' T' t₂ ht₂
          have hu_s : u < s := lt_trans (lt_of_lt_of_le hu2 ht₂_le) hmx'_s
          exact ⟨u, Finset.mem_filter.mpr ⟨huS, hu_s⟩, h1u, hu2⟩
        have hih := ih T'.card (by omega) S' T' rfl hbet'
        omega

def Covers {L : ℕ} (I : ℕ) (X : Fin (L + 1) → List Bool) (gs : List Gate) (S : Finset (Fin L)) : Prop :=
  ∀ t : Fin L, t ∉ S → ∀ wire < I + gs.length,
    (evalGates gs (X t.castSucc)).getD wire false = true →
    (evalGates gs (X t.succ)).getD wire false = true

theorem markov_bound {L : ℕ} (I : ℕ) (X : Fin (L + 1) → List Bool)
    (hXlen : ∀ t, (X t).length = I)
    (hXmono : ∀ t : Fin L, ∀ a < I,
      (X t.castSucc).getD a false = true → (X t.succ).getD a false = true)
    (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∃ S : Finset (Fin L), Covers I X gs S ∧ S.card + 1 ≤ 2 ^ notCountList gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨∅, ?_, by simp [notCountList]⟩
    intro t _ wire hwire htrue
    simpa [evalGates] using hXmono t wire (by simpa using hwire) htrue
  | append_singleton gs g ih =>
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg_op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      hgs g (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨S, hCov, hScard⟩ := ih hgs'
    have hlen_w : ∀ t, (evalGates gs (X t)).length = I + gs.length := fun t => by
      rw [evalGates_length, hXlen t]
    have hwire_lt : ∀ t wire, wire < I + gs.length →
        (evalGates (gs ++ [g]) (X t)).getD wire false = (evalGates gs (X t)).getD wire false := by
      intro t wire hwire
      rw [evalGates_append_singleton, getD_append_left _ _ _ _ (by rw [hlen_w t]; exact hwire)]
    have hwire_eq : ∀ t,
        (evalGates (gs ++ [g]) (X t)).getD (I + gs.length) false =
          g.op.eval (g.inputs.map fun i => (evalGates gs (X t)).getD i false) := by
      intro t
      rw [evalGates_append_singleton]
      have hl : (evalGates gs (X t)).length = I + gs.length := hlen_w t
      rw [← hl, getD_append_eq]
    have hwire_mono_old : ∀ t : Fin L, t ∉ S → ∀ wire,
        (evalGates gs (X t.castSucc)).getD wire false = true →
        (evalGates gs (X t.succ)).getD wire false = true := by
      intro t ht wire htrue
      by_cases hw : wire < I + gs.length
      · exact hCov t ht wire hw htrue
      · have hge : (evalGates gs (X t.castSucc)).length ≤ wire := by rw [hlen_w]; omega
        rw [getD_eq_default_of_ge _ _ _ hge] at htrue
        cases htrue
    rcases hg_op with hop | hop | hop
    · refine ⟨S, ?_, ?_⟩
      · intro t ht wire hwire htrue
        have hwire' : wire < I + gs.length + 1 := by
          rw [List.length_append, List.length_singleton] at hwire; omega
        by_cases hlt : wire < I + gs.length
        · rw [hwire_lt _ _ hlt] at htrue ⊢
          exact hCov t ht wire hlt htrue
        · have heq : wire = I + gs.length := by omega
          subst heq
          rw [hwire_eq] at htrue ⊢
          rw [hop] at htrue ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at htrue ⊢
          intro i hi
          exact hwire_mono_old t ht i (htrue i hi)
      · rw [notCountList_append_singleton, hop]
        simpa using hScard
    · refine ⟨S, ?_, ?_⟩
      · intro t ht wire hwire htrue
        have hwire' : wire < I + gs.length + 1 := by
          rw [List.length_append, List.length_singleton] at hwire; omega
        by_cases hlt : wire < I + gs.length
        · rw [hwire_lt _ _ hlt] at htrue ⊢
          exact hCov t ht wire hlt htrue
        · have heq : wire = I + gs.length := by omega
          subst heq
          rw [hwire_eq] at htrue ⊢
          rw [hop] at htrue ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, hti⟩ := htrue
          exact ⟨_, ⟨i, hi, rfl⟩, hwire_mono_old t ht i hti⟩
      · rw [notCountList_append_singleton, hop]
        simpa using hScard
    · have hop' : g.op = GateOp.not := by simpa [Set.mem_singleton_iff] using hop
      let f : Fin (L + 1) → Bool := fun t =>
        (evalGates (gs ++ [g]) (X t)).getD (I + gs.length) false
      let T : Finset (Fin L) := Finset.univ.filter (fun t => f t.castSucc = true ∧ f t.succ = false)
      refine ⟨S ∪ T, ?_, ?_⟩
      · intro t ht wire hwire htrue
        have hwire' : wire < I + gs.length + 1 := by
          rw [List.length_append, List.length_singleton] at hwire; omega
        have htS : t ∉ S := fun h => ht (Finset.mem_union_left _ h)
        have htT : t ∉ T := fun h => ht (Finset.mem_union_right _ h)
        by_cases hlt : wire < I + gs.length
        · rw [hwire_lt _ _ hlt] at htrue ⊢
          exact hCov t htS wire hlt htrue
        · have heq : wire = I + gs.length := by omega
          subst heq
          change f t.castSucc = true at htrue
          change f t.succ = true
          cases hsucc : f t.succ
          · exfalso
            exact htT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrue, hsucc⟩)
          · rfl
      · have hTcard : T.card ≤ S.card + 1 := by
          apply card_le_succ_of_between T.card S T rfl
          intro t₁ ht₁ t₂ ht₂ h12
          have h1 := (Finset.mem_filter.mp ht₁).2
          have h2 := (Finset.mem_filter.mp ht₂).2
          cases hin : g.inputs with
          | nil =>
            have hconst : ∀ t, f t = true := fun t => by
              dsimp only [f]
              rw [hwire_eq, hop', hin]
              rfl
            have hf2 : f t₁.succ = false := h1.2
            rw [hconst] at hf2
            cases hf2
          | cons i₀ rest =>
            let v : Fin (L + 1) → Bool := fun t => (evalGates gs (X t)).getD i₀ false
            have hfv : ∀ t, f t = !(v t) := fun t => by
              dsimp only [f, v]
              rw [hwire_eq, hop', hin]
              rfl
            have hv1 : v t₁.succ = true := by
              have := h1.2
              rw [hfv] at this
              cases hv : v t₁.succ <;> simp [hv] at this ⊢
            have hv2 : v t₂.castSucc = false := by
              have := h2.1
              rw [hfv] at this
              cases hv : v t₂.castSucc <;> simp [hv] at this ⊢
            have hle : t₁.val + 1 ≤ t₂.val := by
              have : t₁.val < t₂.val := h12
              omega
            obtain ⟨s, hs1, hs2, hvs1, hvs2⟩ :=
              exists_drop_between v (t₁.val + 1) t₂.val hle (by omega)
                ((congrArg v (Fin.ext (by simp))).trans hv1)
                ((congrArg v (Fin.ext (by simp))).trans hv2)
            refine ⟨s, ?_, ?_, ?_⟩
            · by_contra hsnot
              have htrue_succ : v s.succ = true := hwire_mono_old s hsnot i₀ hvs1
              rw [hvs2] at htrue_succ
              cases htrue_succ
            · change t₁.val < s.val; omega
            · change s.val < t₂.val; omega
        rw [notCountList_append_singleton, hop', pow_succ]
        have hu := Finset.card_union_le S T
        omega

def midWords (k : ℕ) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun u : Fin k → Bool =>
    (Finset.univ.filter (fun j : Fin k => u j = true)).card = k / 2)

theorem card_midWords (k : ℕ) : (midWords k).card = Nat.choose k (k / 2) := by
  have hbij : (midWords k).card =
      (Finset.powersetCard (k / 2) (Finset.univ : Finset (Fin k))).card := by
    refine Finset.card_bij
      (fun u _ => Finset.univ.filter (fun j : Fin k => u j = true))
      (fun u hu => ?_)
      (fun u₁ _ u₂ _ heq => ?_)
      (fun s hs => ?_)
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hu).2⟩
    · funext j
      have hj : (j ∈ Finset.univ.filter (fun i : Fin k => u₁ i = true)) ↔
          (j ∈ Finset.univ.filter (fun i : Fin k => u₂ i = true)) := by rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      cases h1 : u₁ j <;> cases h2 : u₂ j <;> simp_all
    · rw [Finset.mem_powersetCard] at hs
      refine ⟨fun j => decide (j ∈ s), ?_, ?_⟩
      · rw [midWords, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hf : Finset.univ.filter (fun j : Fin k => decide (j ∈ s) = true) = s := by
          ext j; simp
        rw [hf, hs.2]
      · ext j; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_fin]

theorem midWords_nonempty (k : ℕ) : (midWords k).Nonempty := by
  rw [← Finset.card_pos, card_midWords]
  exact Nat.choose_pos (Nat.div_le_self k 2)

theorem midWords_incomparable {k : ℕ} {u v : Fin k → Bool}
    (hu : u ∈ midWords k) (hv : v ∈ midWords k) (hne : u ≠ v) :
    ∃ j : Fin k, v j = true ∧ u j = false := by
  let Su := Finset.univ.filter (fun j : Fin k => u j = true)
  let Sv := Finset.univ.filter (fun j : Fin k => v j = true)
  have hcu : Su.card = k / 2 := (Finset.mem_filter.mp hu).2
  have hcv : Sv.card = k / 2 := (Finset.mem_filter.mp hv).2
  by_contra hall
  push_neg at hall
  have hsub : Sv ⊆ Su := by
    intro j hj
    have hvj : v j = true := (Finset.mem_filter.mp hj).2
    have huj : u j ≠ false := hall j hvj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    cases h : u j
    · exact absurd h huj
    · rfl
  have heq : Sv = Su := Finset.eq_of_subset_of_card_le hsub (by omega)
  apply hne
  funext j
  have hj : j ∈ Sv ↔ j ∈ Su := by rw [heq]
  simp only [Sv, Su, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  cases h1 : u j <;> cases h2 : v j <;> simp_all

def blockTable (n w k : ℕ) (hk : 0 < k) (hkw : k ≤ w + 1)
    (A : Fin (n / k) → Finset (Fin k → Bool)) :
    Fin n → (Fin (w + 1) → Bool) → Bool :=
  fun i win =>
    if h : i.val < (n / k) * k ∧ i.val % k = 0 then
      decide ((fun j : Fin k => win ⟨j.val, by omega⟩) ∈
        A ⟨i.val / k, (Nat.div_lt_iff_lt_mul hk).mpr h.1⟩)
    else
      true

theorem blockTable_mono (n w k : ℕ) (hk : 0 < k) (hkw : k ≤ w + 1)
    (A₁ A₂ : Fin (n / k) → Finset (Fin k → Bool))
    (hsub : ∀ b, A₁ b ⊆ A₂ b) :
    ∀ i win, blockTable n w k hk hkw A₁ i win = true →
      blockTable n w k hk hkw A₂ i win = true := by
  intro i win h
  unfold blockTable at h ⊢
  split_ifs at h ⊢ with hc
  · rw [decide_eq_true_eq] at h ⊢
    exact hsub _ h
  · rfl

theorem blockTable_sat (n w k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkw : k ≤ w + 1)
    (A : Fin (n / k) → Finset (Fin k → Bool))
    (hne : ∀ b, (A b).Nonempty) :
    ∃ word : Fin n → Bool, ∀ i : Fin n,
      blockTable n w k hk hkw A i
        (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
  classical
  let pick : Fin (n / k) → (Fin k → Bool) := fun b => (hne b).choose
  have hpick : ∀ b, pick b ∈ A b := fun b => (hne b).choose_spec
  let word : Fin n → Bool := fun pos =>
    if h : pos.val < (n / k) * k then
      pick ⟨pos.val / k, (Nat.div_lt_iff_lt_mul hk).mpr h⟩ ⟨pos.val % k, Nat.mod_lt _ hk⟩
    else
      false
  refine ⟨word, fun i => ?_⟩
  unfold blockTable
  split_ifs with hc
  · rw [decide_eq_true_eq]
    have hbk_le : (n / k) * k ≤ n := Nat.div_mul_le_self n k
    have hi_eq : i.val = (i.val / k) * k := by
      have := Nat.div_add_mod i.val k
      rw [hc.2, Nat.add_zero, Nat.mul_comm] at this
      exact this.symm
    have hfun : (fun j : Fin k => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) =
        pick ⟨i.val / k, (Nat.div_lt_iff_lt_mul hk).mpr hc.1⟩ := by
      funext j
      have hsum_lt_bk : i.val + j.val < (n / k) * k := by
        have hdiv_lt : i.val / k < n / k := (Nat.div_lt_iff_lt_mul hk).mpr hc.1
        have h1 : (i.val / k + 1) * k ≤ (n / k) * k := Nat.mul_le_mul_right k hdiv_lt
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      have hmod_n : (i.val + j.val) % n = i.val + j.val := Nat.mod_eq_of_lt (by omega)
      dsimp only [word]
      rw [dif_pos (by omega)]
      let q : ℕ := i.val / k
      have hi_q : i.val = k * q := by
        dsimp only [q]
        rw [Nat.mul_comm]
        exact hi_eq
      have hdiv_eq : (i.val + j.val) / k = q := by
        rw [hi_q, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      have hmod_eq : (i.val + j.val) % k = j.val := by
        rw [hi_q, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      congr 1 <;> ext <;> simp [q, hmod_n, hdiv_eq, hmod_eq]
    rw [hfun]
    exact hpick _
  · rfl

theorem blockTable_extract (n w k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkw : k ≤ w + 1)
    (A : Fin (n / k) → Finset (Fin k → Bool))
    (word : Fin n → Bool)
    (hvalid : ∀ i : Fin n,
      blockTable n w k hk hkw A i
        (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true)
    (b : Fin (n / k)) :
    (fun j : Fin k => word ⟨b.val * k + j.val, by
      have h1 : (b.val + 1) * k ≤ (n / k) * k := Nat.mul_le_mul_right k b.isLt
      have h2 : (n / k) * k ≤ n := Nat.div_mul_le_self n k
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩) ∈ A b := by
  have hbk_le : (n / k) * k ≤ n := Nat.div_mul_le_self n k
  have hbi_lt : b.val * k < (n / k) * k := by
    have h1 : (b.val + 1) * k ≤ (n / k) * k := Nat.mul_le_mul_right k b.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  let i : Fin n := ⟨b.val * k, by omega⟩
  have hv := hvalid i
  unfold blockTable at hv
  have hcond : i.val < (n / k) * k ∧ i.val % k = 0 := ⟨hbi_lt, Nat.mul_mod_left b.val k⟩
  rw [dif_pos hcond, decide_eq_true_eq] at hv
  have hb_eq : (⟨i.val / k, (Nat.div_lt_iff_lt_mul hk).mpr hcond.1⟩ : Fin (n / k)) = b := by
    ext
    exact Nat.mul_div_cancel b.val hk
  rw [hb_eq] at hv
  convert hv using 1
  funext j
  congr 1
  ext
  have hsum_lt : b.val * k + j.val < n := by
    have h1 : (b.val + 1) * k ≤ (n / k) * k := Nat.mul_le_mul_right k b.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  exact (Nat.mod_eq_of_lt hsum_lt).symm

def pot {B k : ℕ} (A : Fin B → Finset (Fin k → Bool)) : ℕ :=
  ∑ b : Fin B, ((A b).card - 1)

theorem exists_shrink_block {B k : ℕ} (A : Fin B → Finset (Fin k → Bool))
    (hpos : 0 < pot A) : ∃ b : Fin B, 2 ≤ (A b).card := by
  by_contra hall
  push_neg at hall
  have hz : ∀ b : Fin B, (A b).card - 1 = 0 := fun b => by have := hall b; omega
  have : pot A = 0 := Finset.sum_eq_zero (fun b _ => hz b)
  omega

theorem pot_erase {B k : ℕ} (A : Fin B → Finset (Fin k → Bool))
    (b₀ : Fin B) (u : Fin k → Bool) (hu : u ∈ A b₀) (hge : 2 ≤ (A b₀).card) :
    pot (fun b => if b = b₀ then (A b₀).erase u else A b) + 1 = pot A := by
  unfold pot
  have hsub : ∀ b : Fin B,
      ((if b = b₀ then (A b₀).erase u else A b).card - 1) + (if b = b₀ then 1 else 0) =
      (A b).card - 1 := by
    intro b
    split_ifs with h
    · subst h
      rw [Finset.card_erase_of_mem hu]
      omega
    · omega
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun b _ => hsub b)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  exact hsum

end PEqualNP.Outside.L_clb_062_aux

theorem PEqualNP.Outside.L_clb_062 : (∀ (n w k : ℕ) (hn : 0 < n), 0 < k → k ≤ n → k ≤ w + 1 →
  let stride := 2 ^ (w + 1)
  let I := n * stride
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C →
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun addr : Fin I =>
        table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
      let valid := fun (word : Fin n → Bool) => ∀ i : Fin n,
        table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true
      (∃ word, valid word) →
        valid (fun pos => (C.wires inputs).getD (outBit pos).val false)) →
    1 + (n / k) * (Nat.choose k (k / 2) - 1) ≤ 2 ^ PEqualNP.NotBracket.notCount C) := by
  classical
  intro n w k hn hk hkn hkw stride I C outBit hfan _ hcorr
  let B : ℕ := n / k
  let L : ℕ := B * (Nat.choose k (k / 2) - 1)
  let inputsOf : (Fin n → (Fin (w + 1) → Bool) → Bool) → List Bool := fun table =>
    List.ofFn (fun addr : Fin I =>
      table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
  let State := Fin B → Finset (Fin k → Bool)
  let Good : State → Prop := fun A =>
    ∀ b : Fin B, A b ⊆ PEqualNP.Outside.L_clb_062_aux.midWords k ∧ (A b).Nonempty
  let outWord : State → (Fin n → Bool) := fun A pos =>
    (C.wires (inputsOf (PEqualNP.Outside.L_clb_062_aux.blockTable n w k hk hkw A))).getD
      (outBit pos).val false
  have hout_block : ∀ (A : State), Good A → ∀ b : Fin B,
      (fun j : Fin k => outWord A ⟨b.val * k + j.val, by
        have h1 : (b.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k b.isLt
        have h2 : B * k ≤ n := Nat.div_mul_le_self n k
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega⟩) ∈ A b := by
    intro A hA b
    have hsat := PEqualNP.Outside.L_clb_062_aux.blockTable_sat n w k hn hk hkw A (fun b' => (hA b').2)
    have hval := hcorr (PEqualNP.Outside.L_clb_062_aux.blockTable n w k hk hkw A) hsat
    exact PEqualNP.Outside.L_clb_062_aux.blockTable_extract n w k hn hk hkw A (outWord A) hval b
  have hstep : ∀ (A : State), Good A → 0 < PEqualNP.Outside.L_clb_062_aux.pot A →
      ∃ A' : State, Good A' ∧
        PEqualNP.Outside.L_clb_062_aux.pot A' + 1 = PEqualNP.Outside.L_clb_062_aux.pot A ∧
        (∀ b, A' b ⊆ A b) ∧
        ∃ pos : Fin n, outWord A' pos = true ∧ outWord A pos = false := by
    intro A hA hpos
    obtain ⟨b₀, hb₀⟩ := PEqualNP.Outside.L_clb_062_aux.exists_shrink_block A hpos
    let u : Fin k → Bool := fun j => outWord A ⟨b₀.val * k + j.val, by
      have h1 : (b₀.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k b₀.isLt
      have h2 : B * k ≤ n := Nat.div_mul_le_self n k
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩
    have hu_mem : u ∈ A b₀ := hout_block A hA b₀
    let A' : State := fun b => if b = b₀ then (A b₀).erase u else A b
    have hA'_sub : ∀ b, A' b ⊆ A b := by
      intro b
      dsimp only [A']
      split_ifs with h
      · subst h; exact Finset.erase_subset _ _
      · exact Finset.Subset.refl _
    have hA'_good : Good A' := by
      intro b
      refine ⟨(hA'_sub b).trans (hA b).1, ?_⟩
      dsimp only [A']
      split_ifs with h
      · subst h
        rw [← Finset.card_pos, Finset.card_erase_of_mem hu_mem]
        omega
      · exact (hA b).2
    have hpot' : PEqualNP.Outside.L_clb_062_aux.pot A' + 1 =
        PEqualNP.Outside.L_clb_062_aux.pot A :=
      PEqualNP.Outside.L_clb_062_aux.pot_erase A b₀ u hu_mem hb₀
    let v : Fin k → Bool := fun j => outWord A' ⟨b₀.val * k + j.val, by
      have h1 : (b₀.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k b₀.isLt
      have h2 : B * k ≤ n := Nat.div_mul_le_self n k
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩
    have hv_mem' : v ∈ A' b₀ := hout_block A' hA'_good b₀
    have hv_erase : v ∈ (A b₀).erase u := by simpa [A'] using hv_mem'
    have hvu_ne : u ≠ v := (Finset.mem_erase.mp hv_erase).1.symm
    have hu_mid : u ∈ PEqualNP.Outside.L_clb_062_aux.midWords k := (hA b₀).1 hu_mem
    have hv_mid : v ∈ PEqualNP.Outside.L_clb_062_aux.midWords k := (hA'_good b₀).1 hv_mem'
    obtain ⟨j, hvj, huj⟩ := PEqualNP.Outside.L_clb_062_aux.midWords_incomparable hu_mid hv_mid hvu_ne
    refine ⟨A', hA'_good, hpot', hA'_sub, ⟨b₀.val * k + j.val, ?_⟩, hvj, huj⟩
    have h1 : (b₀.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k b₀.isLt
    have h2 : B * k ≤ n := Nat.div_mul_le_self n k
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  let A₀ : State := fun _ => PEqualNP.Outside.L_clb_062_aux.midWords k
  have hA₀_good : Good A₀ := fun _ =>
    ⟨Finset.Subset.refl _, PEqualNP.Outside.L_clb_062_aux.midWords_nonempty k⟩
  have hA₀_pot : PEqualNP.Outside.L_clb_062_aux.pot A₀ = L := by
    simp only [PEqualNP.Outside.L_clb_062_aux.pot, A₀,
      PEqualNP.Outside.L_clb_062_aux.card_midWords, Finset.sum_const, Finset.card_fin, smul_eq_mul, L]
  have hchain : ∀ r ≤ L, ∃ seq : Fin (r + 1) → State,
      Good (seq ⟨r, Nat.lt_succ_self r⟩) ∧
      PEqualNP.Outside.L_clb_062_aux.pot (seq ⟨r, Nat.lt_succ_self r⟩) = L - r ∧
      (∀ t : Fin r, (∀ b, seq t.succ b ⊆ seq t.castSucc b) ∧
        ∃ pos : Fin n, outWord (seq t.succ) pos = true ∧ outWord (seq t.castSucc) pos = false) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun _ => A₀, hA₀_good, by simpa using hA₀_pot, fun t => Fin.elim0 t⟩
    | succ r ih =>
      intro hr
      obtain ⟨seq, hgood, hpot, htr⟩ := ih (by omega)
      have hpos : 0 < PEqualNP.Outside.L_clb_062_aux.pot (seq ⟨r, Nat.lt_succ_self r⟩) := by omega
      obtain ⟨A', hA'_good, hA'_pot, hA'_sub, pos, hpos_t, hpos_f⟩ :=
        hstep (seq ⟨r, Nat.lt_succ_self r⟩) hgood hpos
      let seq' : Fin (r + 2) → State := fun i =>
        if hi : i.val ≤ r then seq ⟨i.val, by omega⟩ else A'
      refine ⟨seq', ?_, ?_, ?_⟩
      · simpa [seq'] using hA'_good
      · have : seq' ⟨r + 1, Nat.lt_succ_self (r + 1)⟩ = A' := by simp [seq']
        rw [this]; omega
      · intro t
        by_cases ht : t.val < r
        · have hc : seq' t.castSucc = seq ⟨t.val, by omega⟩ := by
            dsimp only [seq']
            have hle : t.castSucc.val ≤ r := by simp; omega
            rw [dif_pos hle]
            exact congrArg seq (Fin.ext (by simp))
          have hs : seq' t.succ = seq ⟨t.val + 1, by omega⟩ := by
            dsimp only [seq']
            have hle : t.succ.val ≤ r := by simp; omega
            rw [dif_pos hle]
            exact congrArg seq (Fin.ext (by simp))
          rw [hc, hs]
          exact htr ⟨t.val, ht⟩
        · have ht_eq : t.val = r := by omega
          have hc : seq' t.castSucc = seq ⟨r, Nat.lt_succ_self r⟩ := by
            dsimp only [seq']
            have hle : t.castSucc.val ≤ r := by simp; omega
            rw [dif_pos hle]
            congr 1; ext; simp [ht_eq]
          have hs : seq' t.succ = A' := by
            dsimp only [seq']
            have hnle : ¬ t.succ.val ≤ r := by simp; omega
            rw [dif_neg hnle]
          rw [hc, hs]
          exact ⟨hA'_sub, pos, hpos_t, hpos_f⟩
  obtain ⟨seq, _, _, htr⟩ := hchain L (le_refl L)
  let X : Fin (L + 1) → List Bool := fun t =>
    inputsOf (PEqualNP.Outside.L_clb_062_aux.blockTable n w k hk hkw (seq ⟨L - t.val, by omega⟩))
  have hXlen : ∀ t, (X t).length = I := fun t => by simp [X, inputsOf]
  have hXmono : ∀ t : Fin L, ∀ a < I,
      (X t.castSucc).getD a false = true → (X t.succ).getD a false = true := by
    intro t a ha htrue
    let r : Fin L := ⟨L - 1 - t.val, by omega⟩
    have hidx1 : (⟨L - t.castSucc.val, by omega⟩ : Fin (L + 1)) = r.succ := by
      ext; simp [r]; omega
    have hidx2 : (⟨L - t.succ.val, by omega⟩ : Fin (L + 1)) = r.castSucc := by
      ext; simp [r]; omega
    have hsub := (htr r).1
    have hseq1 : seq ⟨L - t.castSucc.val, by omega⟩ = seq r.succ := congrArg seq hidx1
    have hseq2 : seq ⟨L - t.succ.val, by omega⟩ = seq r.castSucc := congrArg seq hidx2
    have hsub' : ∀ b, seq ⟨L - t.castSucc.val, by omega⟩ b ⊆ seq ⟨L - t.succ.val, by omega⟩ b := by
      intro b
      rw [hseq1, hseq2]
      exact hsub b
    dsimp only [X, inputsOf] at htrue ⊢
    rw [List.getD_eq_getElem _ _ (by simp; exact ha), List.getElem_ofFn] at htrue ⊢
    exact PEqualNP.Outside.L_clb_062_aux.blockTable_mono n w k hk hkw _ _ hsub' _ _ htrue
  have hgs : ∀ g ∈ C.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
      Set PEqualNP.CircuitLowerBounds.GateOp) := fun g hg => (hfan g hg).1
  obtain ⟨S, hCov, hScard⟩ := PEqualNP.Outside.L_clb_062_aux.markov_bound I X hXlen hXmono C.gates hgs
  have hallS : ∀ t : Fin L, t ∈ S := by
    intro t
    by_contra htS
    let r : Fin L := ⟨L - 1 - t.val, by omega⟩
    have hidx1 : (⟨L - t.castSucc.val, by omega⟩ : Fin (L + 1)) = r.succ := by
      ext; simp [r]; omega
    have hidx2 : (⟨L - t.succ.val, by omega⟩ : Fin (L + 1)) = r.castSucc := by
      ext; simp [r]; omega
    obtain ⟨pos, hpos_t, hpos_f⟩ := (htr r).2
    have htrue : (PEqualNP.Outside.L_clb_062_aux.evalGates C.gates (X t.castSucc)).getD
        (outBit pos).val false = true := by
      change outWord (seq ⟨L - t.castSucc.val, by omega⟩) pos = true
      rw [hidx1]
      exact hpos_t
    have hfalse : (PEqualNP.Outside.L_clb_062_aux.evalGates C.gates (X t.succ)).getD
        (outBit pos).val false = false := by
      change outWord (seq ⟨L - t.succ.val, by omega⟩) pos = false
      rw [hidx2]
      exact hpos_f
    have hmono_out := hCov t htS (outBit pos).val (outBit pos).isLt htrue
    rw [hfalse] at hmono_out
    cases hmono_out
  have hS_univ : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hallS
  rw [hS_univ, Finset.card_fin] at hScard
  have hnc : PEqualNP.Outside.L_clb_062_aux.notCountList C.gates =
      PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.Outside.L_clb_062_aux.notCountList PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases g.op <;> simp
  rw [hnc] at hScard
  dsimp only [L, B] at hScard
  omega
