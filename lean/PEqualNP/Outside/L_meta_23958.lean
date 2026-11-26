import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23958_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def backStep (t : ℕ) (g : Gate) (R : Finset ℕ) : Finset ℕ :=
  if t ∈ R then R.erase t ∪ g.inputs.toFinset else R

def backConeRec (N : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], R => R
  | g :: gs, R => backStep N g (backConeRec (N + 1) gs R)

theorem backConeRec_append_singleton (N : ℕ) (gs : List Gate) (g : Gate) (R : Finset ℕ) :
    backConeRec N (gs ++ [g]) R = backConeRec N gs (backStep (N + gs.length) g R) := by
  induction gs generalizing N with
  | nil => simp [backConeRec]
  | cons g0 gs ih =>
    simp only [List.cons_append, backConeRec, List.length_cons]
    rw [ih (N + 1), show N + 1 + gs.length = N + (gs.length + 1) by omega]

theorem backConeRec_card_le (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    (backConeRec N gs R).card ≤ R.card + gs.length := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => simp [backConeRec]
  | append_singleton gs g ih =>
    rw [backConeRec_append_singleton]
    have hg' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    have h1 := ih hg' (backStep (N + gs.length) g R)
    have hstep : (backStep (N + gs.length) g R).card ≤ R.card + 1 := by
      unfold backStep
      split_ifs with ht
      · have := Finset.card_union_le (R.erase (N + gs.length)) g.inputs.toFinset
        have := Finset.card_erase_of_mem ht
        have := List.toFinset_card_le g.inputs
        have : 0 < R.card := Finset.card_pos.2 ⟨N + gs.length, ht⟩
        omega
      · omega
    simp only [List.length_append, List.length_singleton]
    omega

theorem backConeRec_mem_ge (N : ℕ) (gs : List Gate) (R : Finset ℕ) (w : ℕ)
    (hwR : w ∈ R) (hw : N + gs.length ≤ w) : w ∈ backConeRec N gs R := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => simpa [backConeRec] using hwR
  | append_singleton gs g ih =>
    rw [backConeRec_append_singleton]
    apply ih
    · unfold backStep
      split_ifs with ht
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp at hw; omega, hwR⟩)
      · exact hwR
    · simp at hw; omega

theorem backConeRec_dep (N : ℕ) (gs : List Gate) (R : Finset ℕ) :
    ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ backConeRec N gs R, x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => intro x y _ _ h w hw; simpa [backConeRec] using h w hw
  | append_singleton gs g ih =>
    intro x y hx hy hxy w hw
    rw [backConeRec_append_singleton] at hxy
    have e := ih (backStep (N + gs.length) g R) x y hx hy hxy
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hx, hy]
    split_ifs with h1 h3
    · exact e w (by unfold backStep; split_ifs <;> simp_all; omega)
    · have ht : N + gs.length ∈ R := by rw [← h3]; exact hw
      congr 1
      refine List.map_congr_left fun i hi => e i ?_
      simp [backStep, ht, hi]
    · rfl

inductive Formula where
  | leaf : ℕ → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

def Formula.leaves : Formula → Finset ℕ
  | .leaf w => {w}
  | .and a b => a.leaves ∪ b.leaves
  | .or a b => a.leaves ∪ b.leaves

def Formula.eval (x : List Bool) : Formula → Bool
  | .leaf w => x.getD w false
  | .and a b => a.eval x && b.eval x
  | .or a b => a.eval x || b.eval x

def Formula.ReadOnce : Formula → Prop
  | .leaf _ => True
  | .and a b => a.ReadOnce ∧ b.ReadOnce ∧ Disjoint a.leaves b.leaves
  | .or a b => a.ReadOnce ∧ b.ReadOnce ∧ Disjoint a.leaves b.leaves

def Formula.subst : Formula → ℕ → Formula → Formula
  | .leaf w, t, sub => if w = t then sub else .leaf w
  | .and a b, t, sub => .and (a.subst t sub) (b.subst t sub)
  | .or a b, t, sub => .or (a.subst t sub) (b.subst t sub)

theorem Formula.subst_of_not_mem {F sub : Formula} {t : ℕ} (ht : t ∉ F.leaves) :
    F.subst t sub = F := by
  induction F with
  | leaf w =>
    simp only [Formula.leaves, Finset.mem_singleton] at ht
    simp [Formula.subst, Ne.symm ht]
  | and a b iha ihb =>
    simp only [Formula.leaves, Finset.mem_union, not_or] at ht
    simp [Formula.subst, iha ht.1, ihb ht.2]
  | or a b iha ihb =>
    simp only [Formula.leaves, Finset.mem_union, not_or] at ht
    simp [Formula.subst, iha ht.1, ihb ht.2]

theorem erase_union_left {A B S : Finset ℕ} {t : ℕ} (htB : t ∉ B) :
    (A.erase t ∪ S) ∪ B = (A ∪ B).erase t ∪ S := by
  ext w
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ((⟨hne, hA⟩ | hS) | hB)
    · exact Or.inl ⟨hne, Or.inl hA⟩
    · exact Or.inr hS
    · exact Or.inl ⟨fun e => htB (e ▸ hB), Or.inr hB⟩
  · rintro (⟨hne, hA | hB⟩ | hS)
    · exact Or.inl (Or.inl ⟨hne, hA⟩)
    · exact Or.inr hB
    · exact Or.inl (Or.inr hS)

theorem erase_union_right {A B S : Finset ℕ} {t : ℕ} (htA : t ∉ A) :
    A ∪ (B.erase t ∪ S) = (A ∪ B).erase t ∪ S := by
  ext w
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (hA | (⟨hne, hB⟩ | hS))
    · exact Or.inl ⟨fun e => htA (e ▸ hA), Or.inl hA⟩
    · exact Or.inl ⟨hne, Or.inr hB⟩
    · exact Or.inr hS
  · rintro (⟨hne, hA | hB⟩ | hS)
    · exact Or.inl hA
    · exact Or.inr (Or.inl ⟨hne, hB⟩)
    · exact Or.inr (Or.inr hS)

theorem Formula.subst_leaves {F sub : Formula} {t : ℕ} (hro : F.ReadOnce) (ht : t ∈ F.leaves) :
    (F.subst t sub).leaves = F.leaves.erase t ∪ sub.leaves := by
  induction F with
  | leaf w =>
    simp only [Formula.leaves, Finset.mem_singleton] at ht
    subst ht
    simp [Formula.subst, Formula.leaves]
  | and a b iha ihb =>
    rcases hro with ⟨ha, hb, hdisj⟩
    simp only [Formula.leaves, Finset.mem_union] at ht
    rcases ht with hta | htb
    · have hntb : t ∉ b.leaves := Finset.disjoint_left.mp hdisj hta
      rw [Formula.subst, Formula.subst_of_not_mem hntb, Formula.leaves, iha ha hta, Formula.leaves]
      exact erase_union_left hntb
    · have hnta : t ∉ a.leaves := Finset.disjoint_right.mp hdisj htb
      rw [Formula.subst, Formula.subst_of_not_mem hnta, Formula.leaves, ihb hb htb, Formula.leaves]
      exact erase_union_right hnta
  | or a b iha ihb =>
    rcases hro with ⟨ha, hb, hdisj⟩
    simp only [Formula.leaves, Finset.mem_union] at ht
    rcases ht with hta | htb
    · have hntb : t ∉ b.leaves := Finset.disjoint_left.mp hdisj hta
      rw [Formula.subst, Formula.subst_of_not_mem hntb, Formula.leaves, iha ha hta, Formula.leaves]
      exact erase_union_left hntb
    · have hnta : t ∉ a.leaves := Finset.disjoint_right.mp hdisj htb
      rw [Formula.subst, Formula.subst_of_not_mem hnta, Formula.leaves, ihb hb htb, Formula.leaves]
      exact erase_union_right hnta

theorem Formula.subst_readOnce {F sub : Formula} {t : ℕ}
    (hro : F.ReadOnce) (hsub : sub.ReadOnce) (ht : t ∈ F.leaves)
    (hdisjS : Disjoint (F.leaves.erase t) sub.leaves) :
    (F.subst t sub).ReadOnce := by
  induction F with
  | leaf w =>
    simp only [Formula.leaves, Finset.mem_singleton] at ht
    subst ht
    simpa [Formula.subst] using hsub
  | and a b iha ihb =>
    rcases hro with ⟨ha, hb, hdisj⟩
    simp only [Formula.leaves, Finset.mem_union] at ht
    rcases ht with hta | htb
    · have hntb : t ∉ b.leaves := Finset.disjoint_left.mp hdisj hta
      have hdb : Disjoint b.leaves sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwb
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨fun e => hntb (e ▸ hwb), Finset.mem_union_right _ hwb⟩)
      have hda : Disjoint (a.leaves.erase t) sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwa
        have hwa' := Finset.mem_erase.mp hwa
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨hwa'.1, Finset.mem_union_left _ hwa'.2⟩)
      rw [Formula.subst, Formula.subst_of_not_mem hntb]
      refine ⟨iha ha hta hda, hb, ?_⟩
      rw [Formula.subst_leaves ha hta]
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj, hdb.symm⟩
    · have hnta : t ∉ a.leaves := Finset.disjoint_right.mp hdisj htb
      have hda : Disjoint a.leaves sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwa
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨fun e => hnta (e ▸ hwa), Finset.mem_union_left _ hwa⟩)
      have hdb : Disjoint (b.leaves.erase t) sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwb
        have hwb' := Finset.mem_erase.mp hwb
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨hwb'.1, Finset.mem_union_right _ hwb'.2⟩)
      rw [Formula.subst, Formula.subst_of_not_mem hnta]
      refine ⟨ha, ihb hb htb hdb, ?_⟩
      rw [Formula.subst_leaves hb htb]
      rw [Finset.disjoint_union_right]
      exact ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj, hda⟩
  | or a b iha ihb =>
    rcases hro with ⟨ha, hb, hdisj⟩
    simp only [Formula.leaves, Finset.mem_union] at ht
    rcases ht with hta | htb
    · have hntb : t ∉ b.leaves := Finset.disjoint_left.mp hdisj hta
      have hdb : Disjoint b.leaves sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwb
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨fun e => hntb (e ▸ hwb), Finset.mem_union_right _ hwb⟩)
      have hda : Disjoint (a.leaves.erase t) sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwa
        have hwa' := Finset.mem_erase.mp hwa
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨hwa'.1, Finset.mem_union_left _ hwa'.2⟩)
      rw [Formula.subst, Formula.subst_of_not_mem hntb]
      refine ⟨iha ha hta hda, hb, ?_⟩
      rw [Formula.subst_leaves ha hta]
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj, hdb.symm⟩
    · have hnta : t ∉ a.leaves := Finset.disjoint_right.mp hdisj htb
      have hda : Disjoint a.leaves sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwa
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨fun e => hnta (e ▸ hwa), Finset.mem_union_left _ hwa⟩)
      have hdb : Disjoint (b.leaves.erase t) sub.leaves := by
        rw [Finset.disjoint_left]
        intro w hwb
        have hwb' := Finset.mem_erase.mp hwb
        exact Finset.disjoint_left.mp hdisjS
          (Finset.mem_erase.mpr ⟨hwb'.1, Finset.mem_union_right _ hwb'.2⟩)
      rw [Formula.subst, Formula.subst_of_not_mem hnta]
      refine ⟨ha, ihb hb htb hdb, ?_⟩
      rw [Formula.subst_leaves hb htb]
      rw [Finset.disjoint_union_right]
      exact ⟨Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj, hda⟩

theorem Formula.subst_eval {F sub : Formula} {t : ℕ} {x y : List Bool}
    (ht : sub.eval x = y.getD t false)
    (hother : ∀ w ∈ F.leaves, w ≠ t → x.getD w false = y.getD w false) :
    (F.subst t sub).eval x = F.eval y := by
  induction F with
  | leaf w =>
    simp only [Formula.subst]
    by_cases hw : w = t
    · subst hw; simpa [Formula.eval] using ht
    · simp only [hw, ↓reduceIte, Formula.eval]
      exact hother w (by simp [Formula.leaves]) hw
  | and a b iha ihb =>
    simp only [Formula.subst, Formula.eval]
    rw [iha (fun w hw => hother w (Finset.mem_union_left _ hw)),
        ihb (fun w hw => hother w (Finset.mem_union_right _ hw))]
  | or a b iha ihb =>
    simp only [Formula.subst, Formula.eval]
    rw [iha (fun w hw => hother w (Finset.mem_union_left _ hw)),
        ihb (fun w hw => hother w (Finset.mem_union_right _ hw))]

theorem Formula.eval_false_of_all_false (F : Formula) (x : List Bool)
    (h : ∀ w ∈ F.leaves, x.getD w false = false) : F.eval x = false := by
  induction F with
  | leaf w => exact h w (by simp [Formula.leaves])
  | and a b iha ihb =>
    simp [Formula.eval, iha (fun w hw => h w (Finset.mem_union_left _ hw)),
          ihb (fun w hw => h w (Finset.mem_union_right _ hw))]
  | or a b iha ihb =>
    simp [Formula.eval, iha (fun w hw => h w (Finset.mem_union_left _ hw)),
          ihb (fun w hw => h w (Finset.mem_union_right _ hw))]

theorem Formula.eval_mono (F : Formula) (x y : List Bool)
    (h : ∀ w ∈ F.leaves, x.getD w false = true → y.getD w false = true) :
    F.eval x = true → F.eval y = true := by
  induction F with
  | leaf w => exact h w (by simp [Formula.leaves])
  | and a b iha ihb =>
    simp only [Formula.eval, Bool.and_eq_true]
    exact fun ⟨ha, hb⟩ => ⟨iha (fun w hw => h w (Finset.mem_union_left _ hw)) ha,
                           ihb (fun w hw => h w (Finset.mem_union_right _ hw)) hb⟩
  | or a b iha ihb =>
    simp only [Formula.eval, Bool.or_eq_true]
    intro hor
    rcases hor with ha | hb
    · exact Or.inl (iha (fun w hw => h w (Finset.mem_union_left _ hw)) ha)
    · exact Or.inr (ihb (fun w hw => h w (Finset.mem_union_right _ hw)) hb)

theorem list_len2_of_toFinset_card2 {l : List ℕ} (h1 : l.length ≤ 2) (h2 : l.toFinset.card = 2) :
    ∃ a b : ℕ, l = [a, b] ∧ a ≠ b := by
  match l with
  | [] => simp at h2
  | [a] => simp at h2
  | [a, b] =>
    refine ⟨a, b, rfl, ?_⟩
    intro heq
    subst heq
    simp at h2
  | _ :: _ :: _ :: _ => simp at h1

theorem tight_backCone_to_formula (N : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (F : Formula) (hro : F.ReadOnce)
    (htight : (backConeRec N gs F.leaves).card = F.leaves.card + gs.length)
    (hbound : ∀ w ∈ backConeRec N gs F.leaves, w < N) :
    ∃ F' : Formula, F'.ReadOnce ∧ F'.leaves = backConeRec N gs F.leaves ∧
      ∀ x : List Bool, x.length = N → F'.eval x = F.eval (gs.foldl stp x) := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, hro, rfl, fun _ _ => rfl⟩
  | append_singleton gs g ih =>
    rw [backConeRec_append_singleton] at htight hbound
    have hg' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hg g' (by simp [h])
    have hg0 := hg g (by simp)
    set t := N + gs.length
    have hle1 := backConeRec_card_le N gs (fun g' h => (hg' g' h).2) (backStep t g F.leaves)
    have hle2 : (backStep t g F.leaves).card ≤ F.leaves.card + 1 := by
      unfold backStep
      split_ifs with ht
      · have := Finset.card_union_le (F.leaves.erase t) g.inputs.toFinset
        have := Finset.card_erase_of_mem ht
        have := List.toFinset_card_le g.inputs
        have : 0 < F.leaves.card := Finset.card_pos.2 ⟨t, ht⟩
        omega
      · omega
    simp only [List.length_append, List.length_singleton] at htight
    have hstepEq : (backStep t g F.leaves).card = F.leaves.card + 1 := by omega
    have hrecEq : (backConeRec N gs (backStep t g F.leaves)).card =
        (backStep t g F.leaves).card + gs.length := by omega
    have htMem : t ∈ F.leaves := by
      by_contra hnt
      simp [backStep, hnt] at hstepEq
    have hcard_un : (F.leaves.erase t ∪ g.inputs.toFinset).card = F.leaves.card + 1 := by
      simpa [backStep, htMem] using hstepEq
    have hcard_er : (F.leaves.erase t).card = F.leaves.card - 1 := Finset.card_erase_of_mem htMem
    have hpos : 0 < F.leaves.card := Finset.card_pos.2 ⟨t, htMem⟩
    have hcard_in_le : g.inputs.toFinset.card ≤ 2 :=
      le_trans (List.toFinset_card_le g.inputs) hg0.2
    have hcard_u_le := Finset.card_union_le (F.leaves.erase t) g.inputs.toFinset
    have hcard_in : g.inputs.toFinset.card = 2 := by omega
    have hdisj : Disjoint (F.leaves.erase t) g.inputs.toFinset := by
      have hi := Finset.card_union_add_card_inter (F.leaves.erase t) g.inputs.toFinset
      have h0 : (F.leaves.erase t ∩ g.inputs.toFinset).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    obtain ⟨a, b, hgab, hab⟩ := list_len2_of_toFinset_card2 hg0.2 hcard_in
    have hlt_all : ∀ w ∈ backStep t g F.leaves, w < t := by
      intro w hw
      by_contra hge
      have hw' := backConeRec_mem_ge N gs (backStep t g F.leaves) w hw (by omega)
      have hltN := hbound w hw'
      omega
    have hltF : ∀ w ∈ F.leaves, w ≠ t → w < t := fun w hw hne =>
      hlt_all w (by simp [backStep, htMem, hw, hne])
    let sub : Formula := match g.op with
      | .and => .and (.leaf a) (.leaf b)
      | _ => .or (.leaf a) (.leaf b)
    have hsub_leaves : sub.leaves = g.inputs.toFinset := by
      rcases hg0.1 with hop | hop <;> simp [sub, hop, Formula.leaves, hgab]
    have hsub_ro : sub.ReadOnce := by
      rcases hg0.1 with hop | hop <;>
        simpa [sub, hop, Formula.ReadOnce, Formula.leaves] using hab
    let F1 := F.subst t sub
    have hF1_leaves : F1.leaves = backStep t g F.leaves := by
      rw [Formula.subst_leaves hro htMem, hsub_leaves]
      simp [backStep, htMem]
    have hF1_ro : F1.ReadOnce :=
      Formula.subst_readOnce hro hsub_ro htMem (hsub_leaves ▸ hdisj)
    obtain ⟨F', hF'ro, hF'l, hF'ev⟩ := ih hg' F1 hF1_ro (by rw [hF1_leaves]; exact hrecEq)
      (by rw [hF1_leaves]; exact hbound)
    refine ⟨F', hF'ro, ?_, ?_⟩
    · rw [backConeRec_append_singleton, ← hF1_leaves]; exact hF'l
    · intro x hx
      rw [hF'ev x hx]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      apply Formula.subst_eval
      · rw [getD_snoc, len, hx]
        have hlt_f : ¬ t < t := Nat.lt_irrefl t
        simp only [t, hlt_f, ↓reduceIte]
        rcases hg0.1 with hop | hop <;>
          simp [sub, hop, hgab, GateOp.eval, Formula.eval]
      · intro w hw hne
        rw [getD_snoc, len, hx]
        have hwt := hltF w hw hne
        simp [t, hwt]

def targetA (n : ℕ) (u v : Fin n) : Bool :=
  decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0))

theorem targetA_essential (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k ∈ Finset.range (n + n)) :
    ∃ (u v u' v' : Fin n), targetA n u v = true ∧ targetA n u' v' = false ∧
      (u.val = k ∨ u = u') ∧ (n + v.val = k ∨ v = v') := by
  simp only [Finset.mem_range] at hk
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, by omega⟩
  let r2 : Fin n := ⟨2, by omega⟩
  by_cases hkn : k < n
  · let u : Fin n := ⟨k, hkn⟩
    by_cases hk0 : k = 0
    · refine ⟨u, r1, r2, r1, ?_, ?_, Or.inl rfl, Or.inr rfl⟩
      · simp [targetA, u, r1, hk0]
      · simp [targetA, r2, r1]
    · by_cases hk1 : k = 1
      · refine ⟨u, r0, r0, r0, ?_, ?_, Or.inl rfl, Or.inr rfl⟩
        · simp [targetA, u, r0, hk1]
        · simp [targetA, r0]
      · refine ⟨u, r0, r0, r0, ?_, ?_, Or.inl rfl, Or.inr rfl⟩
        · simp [targetA, u, r0]; omega
        · simp [targetA, r0]
  · let v : Fin n := ⟨k - n, by omega⟩
    by_cases hkv : k - n = 0
    · refine ⟨r2, v, r2, r1, ?_, ?_, Or.inr rfl, Or.inl (by simp [v]; omega)⟩
      · simp [targetA, r2, v, hkv]
      · simp [targetA, r2, r1]
    · refine ⟨r0, v, r0, r0, ?_, ?_, Or.inr rfl, Or.inl (by simp [v]; omega)⟩
      · simp [targetA, r0, v, hkv]
      · simp [targetA, r0]

theorem no_readOnce_targetA (n : ℕ) (hn : 3 ≤ n) (F : Formula) :
    F.ReadOnce →
    (∀ u v : Fin n, u.val < 3 → v.val < 3 → F.eval (oneEach u v) = targetA n u v) →
    False := by
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, by omega⟩
  let r2 : Fin n := ⟨2, by omega⟩
  have hr0 : r0.val < 3 := by show 0 < 3; omega
  have hr1 : r1.val < 3 := by show 1 < 3; omega
  have hr2 : r2.val < 3 := by show 2 < 3; omega
  induction F with
  | leaf w =>
    intro _ heval
    have h01 : (Formula.leaf w).eval (oneEach r0 r1) = true := by rw [heval r0 r1 hr0 hr1]; simp [targetA, r0, r1]
    have h20 : (Formula.leaf w).eval (oneEach r2 r0) = true := by rw [heval r2 r0 hr2 hr0]; simp [targetA, r2, r0]
    simp only [Formula.eval, oe] at h01 h20
    rcases h01 with rfl | rfl <;> rcases h20 with h | h <;> simp [r0, r1, r2] at h <;> omega
  | and L R _ _ =>
    intro hro heval
    have h00 : (Formula.and L R).eval (oneEach r0 r0) = false := by rw [heval r0 r0 hr0 hr0]; simp [targetA, r0]
    have h01 : (Formula.and L R).eval (oneEach r0 r1) = true  := by rw [heval r0 r1 hr0 hr1]; simp [targetA, r0, r1]
    have h10 : (Formula.and L R).eval (oneEach r1 r0) = true  := by rw [heval r1 r0 hr1 hr0]; simp [targetA, r1, r0]
    have h11 : (Formula.and L R).eval (oneEach r1 r1) = true  := by rw [heval r1 r1 hr1 hr1]; simp [targetA, r1, r1]
    rcases hro with ⟨_, _, hdisj⟩
    have meet : ∀ (G : Formula) (u v : Fin n), G.eval (oneEach u v) = true →
        u.val ∈ G.leaves ∨ n + v.val ∈ G.leaves := by
      intro G u v hG
      by_contra hno
      push Not at hno
      have hf := Formula.eval_false_of_all_false G (oneEach u v) (fun w hw => by
        by_contra ht
        have ht' : (oneEach u v).getD w false = true := by cases h' : (oneEach u v).getD w false <;> simp_all
        rw [oe] at ht'
        rcases ht' with rfl | rfl
        · exact hno.1 hw
        · exact hno.2 hw)
      simp [hG] at hf
    have split_edge : ∀ (u v : Fin n), (Formula.and L R).eval (oneEach u v) = true →
        (u.val ∈ L.leaves ∧ n + v.val ∈ R.leaves) ∨ (u.val ∈ R.leaves ∧ n + v.val ∈ L.leaves) := by
      intro u v huv
      simp only [Formula.eval, Bool.and_eq_true] at huv
      have mL := meet L u v huv.1
      have mR := meet R u v huv.2
      rcases mL with huL | hvL <;> rcases mR with huR | hvR
      · exact absurd huR (Finset.disjoint_left.mp hdisj huL)
      · exact Or.inl ⟨huL, hvR⟩
      · exact Or.inr ⟨huR, hvL⟩
      · exact absurd hvR (Finset.disjoint_left.mp hdisj hvL)
    have e01 := split_edge r0 r1 h01
    have e11 := split_edge r1 r1 h11
    have e10 := split_edge r1 r0 h10
    have contra_side : ∀ (A B : Formula), Disjoint A.leaves B.leaves →
        A.eval (oneEach r0 r1) = true → B.eval (oneEach r1 r0) = true →
        (r0.val ∈ A.leaves ∧ n + r1.val ∈ B.leaves) →
        (r1.val ∈ A.leaves ∧ n + r0.val ∈ B.leaves) →
        A.eval (oneEach r0 r0) = true ∧ B.eval (oneEach r0 r0) = true := by
      intro A B hd hA01 hB10 hA hB
      constructor
      · apply Formula.eval_mono A (oneEach r0 r1) (oneEach r0 r0) _ hA01
        intro w hw hwt
        rw [oe] at hwt ⊢
        rcases hwt with rfl | rfl
        · exact Or.inl rfl
        · exact absurd hw (Finset.disjoint_right.mp hd hA.2)
      · apply Formula.eval_mono B (oneEach r1 r0) (oneEach r0 r0) _ hB10
        intro w hw hwt
        rw [oe] at hwt ⊢
        rcases hwt with rfl | rfl
        · exact absurd hw (Finset.disjoint_left.mp hd hB.1)
        · exact Or.inr rfl
    simp only [Formula.eval, Bool.and_eq_true] at h01 h10
    rcases e01 with ⟨h0L, hv1R⟩ | ⟨h0R, hv1L⟩
    · have h1L : r1.val ∈ L.leaves := by
        rcases e11 with ⟨h1L, _⟩ | ⟨_, hv1L⟩
        · exact h1L
        · exact absurd hv1R (Finset.disjoint_left.mp hdisj hv1L)
      have hv0R : n + r0.val ∈ R.leaves := by
        rcases e10 with ⟨_, hv0R⟩ | ⟨h1R, _⟩
        · exact hv0R
        · exact absurd h1R (Finset.disjoint_left.mp hdisj h1L)
      have ⟨hL00, hR00⟩ := contra_side L R hdisj h01.1 h10.2 ⟨h0L, hv1R⟩ ⟨h1L, hv0R⟩
      simp [Formula.eval, hL00, hR00] at h00
    · have h1R : r1.val ∈ R.leaves := by
        rcases e11 with ⟨_, hv1R⟩ | ⟨h1R, _⟩
        · exact absurd hv1R (Finset.disjoint_left.mp hdisj hv1L)
        · exact h1R
      have hv0L : n + r0.val ∈ L.leaves := by
        rcases e10 with ⟨h1L, _⟩ | ⟨_, hv0L⟩
        · exact absurd h1R (Finset.disjoint_left.mp hdisj h1L)
        · exact hv0L
      have ⟨hR00, hL00⟩ := contra_side R L hdisj.symm h01.2 h10.1 ⟨h0R, hv1L⟩ ⟨h1R, hv0L⟩
      simp [Formula.eval, hL00, hR00] at h00
  | or L R ihL ihR =>
    intro hro heval
    have h00 : (Formula.or L R).eval (oneEach r0 r0) = false := by rw [heval r0 r0 hr0 hr0]; simp [targetA, r0]
    have h01 : (Formula.or L R).eval (oneEach r0 r1) = true  := by rw [heval r0 r1 hr0 hr1]; simp [targetA, r0, r1]
    have h02 : (Formula.or L R).eval (oneEach r0 r2) = true  := by rw [heval r0 r2 hr0 hr2]; simp [targetA, r0, r2]
    have h10 : (Formula.or L R).eval (oneEach r1 r0) = true  := by rw [heval r1 r0 hr1 hr0]; simp [targetA, r1, r0]
    have h11 : (Formula.or L R).eval (oneEach r1 r1) = true  := by rw [heval r1 r1 hr1 hr1]; simp [targetA, r1, r1]
    have h12 : (Formula.or L R).eval (oneEach r1 r2) = false := by rw [heval r1 r2 hr1 hr2]; simp [targetA, r1, r2]
    have h20 : (Formula.or L R).eval (oneEach r2 r0) = true  := by rw [heval r2 r0 hr2 hr0]; simp [targetA, r2, r0]
    have h21 : (Formula.or L R).eval (oneEach r2 r1) = false := by rw [heval r2 r1 hr2 hr1]; simp [targetA, r2, r1]
    rcases hro with ⟨hroL, hroR, hdisj⟩
    have both_in : ∀ (G : Formula), (∀ u v : Fin n, G.eval (oneEach u v) = true → (Formula.or L R).eval (oneEach u v) = true) →
        ∀ u v : Fin n, u.val < 3 → v.val < 3 → G.eval (oneEach u v) = true →
        u.val ∈ G.leaves ∧ n + v.val ∈ G.leaves := by
      intro G hGimp u v hu hv hG
      constructor
      · by_contra hnu
        have hfalse : ∃ u' : Fin n, u'.val < 3 ∧ (Formula.or L R).eval (oneEach u' v) = false := by
          have hv3 : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
          rcases hv3 with hv0 | hv1 | hv2
          · refine ⟨r0, hr0, ?_⟩
            have : v = r0 := Fin.ext hv0; subst this; exact h00
          · refine ⟨r2, hr2, ?_⟩
            have : v = r1 := Fin.ext hv1; subst this; exact h21
          · refine ⟨r1, hr1, ?_⟩
            have : v = r2 := Fin.ext hv2; subst this; exact h12
        obtain ⟨u', _, hu'f⟩ := hfalse
        have hGu' : G.eval (oneEach u' v) = true := by
          apply Formula.eval_mono G (oneEach u v) (oneEach u' v) _ hG
          intro w hw hwt
          rw [oe] at hwt ⊢
          rcases hwt with rfl | rfl
          · exact absurd hw hnu
          · exact Or.inr rfl
        have := hGimp u' v hGu'
        simp [hu'f] at this
      · by_contra hnv
        have hfalse : ∃ v' : Fin n, v'.val < 3 ∧ (Formula.or L R).eval (oneEach u v') = false := by
          have hu3 : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by omega
          rcases hu3 with hu0 | hu1 | hu2
          · refine ⟨r0, hr0, ?_⟩
            have : u = r0 := Fin.ext hu0; subst this; exact h00
          · refine ⟨r2, hr2, ?_⟩
            have : u = r1 := Fin.ext hu1; subst this; exact h12
          · refine ⟨r1, hr1, ?_⟩
            have : u = r2 := Fin.ext hu2; subst this; exact h21
        obtain ⟨v', _, hv'f⟩ := hfalse
        have hGv' : G.eval (oneEach u v') = true := by
          apply Formula.eval_mono G (oneEach u v) (oneEach u v') _ hG
          intro w hw hwt
          rw [oe] at hwt ⊢
          rcases hwt with rfl | rfl
          · exact Or.inl rfl
          · exact absurd hw hnv
        have := hGimp u v' hGv'
        simp [hv'f] at this
    have impL : ∀ u v : Fin n, L.eval (oneEach u v) = true → (Formula.or L R).eval (oneEach u v) = true :=
      fun u v h => by simp [Formula.eval, h]
    have impR : ∀ u v : Fin n, R.eval (oneEach u v) = true → (Formula.or L R).eval (oneEach u v) = true :=
      fun u v h => by simp [Formula.eval, h]
    have edge_same : ∀ u v : Fin n, u.val < 3 → v.val < 3 →
        (Formula.or L R).eval (oneEach u v) = true →
        (u.val ∈ L.leaves ∧ n + v.val ∈ L.leaves) ∨ (u.val ∈ R.leaves ∧ n + v.val ∈ R.leaves) := by
      intro u v hu hv huv
      simp only [Formula.eval, Bool.or_eq_true] at huv
      rcases huv with hL | hR
      · exact Or.inl (both_in L impL u v hu hv hL)
      · exact Or.inr (both_in R impR u v hu hv hR)
    have e01 := edge_same r0 r1 hr0 hr1 h01
    have e02 := edge_same r0 r2 hr0 hr2 h02
    have e11 := edge_same r1 r1 hr1 hr1 h11
    have e10 := edge_same r1 r0 hr1 hr0 h10
    have e20 := edge_same r2 r0 hr2 hr0 h20
    have all_in_one : (r0.val ∈ L.leaves ∧ r1.val ∈ L.leaves ∧ r2.val ∈ L.leaves ∧
        n + r0.val ∈ L.leaves ∧ n + r1.val ∈ L.leaves ∧ n + r2.val ∈ L.leaves) ∨
        (r0.val ∈ R.leaves ∧ r1.val ∈ R.leaves ∧ r2.val ∈ R.leaves ∧
        n + r0.val ∈ R.leaves ∧ n + r1.val ∈ R.leaves ∧ n + r2.val ∈ R.leaves) := by
      rcases e01 with ⟨h0L, hv1L⟩ | ⟨h0R, hv1R⟩
      · left
        have hv2L : n + r2.val ∈ L.leaves := by
          rcases e02 with ⟨_, h⟩ | ⟨h0R, _⟩
          · exact h
          · exact absurd h0R (Finset.disjoint_left.mp hdisj h0L)
        have h1L : r1.val ∈ L.leaves := by
          rcases e11 with ⟨h, _⟩ | ⟨_, hv1R⟩
          · exact h
          · exact absurd hv1R (Finset.disjoint_left.mp hdisj hv1L)
        have hv0L : n + r0.val ∈ L.leaves := by
          rcases e10 with ⟨_, h⟩ | ⟨h1R, _⟩
          · exact h
          · exact absurd h1R (Finset.disjoint_left.mp hdisj h1L)
        have h2L : r2.val ∈ L.leaves := by
          rcases e20 with ⟨h, _⟩ | ⟨_, hv0R⟩
          · exact h
          · exact absurd hv0R (Finset.disjoint_left.mp hdisj hv0L)
        exact ⟨h0L, h1L, h2L, hv0L, hv1L, hv2L⟩
      · right
        have hv2R : n + r2.val ∈ R.leaves := by
          rcases e02 with ⟨h0L, _⟩ | ⟨_, h⟩
          · exact absurd h0R (Finset.disjoint_left.mp hdisj h0L)
          · exact h
        have h1R : r1.val ∈ R.leaves := by
          rcases e11 with ⟨_, hv1L⟩ | ⟨h, _⟩
          · exact absurd hv1R (Finset.disjoint_left.mp hdisj hv1L)
          · exact h
        have hv0R : n + r0.val ∈ R.leaves := by
          rcases e10 with ⟨h1L, _⟩ | ⟨_, h⟩
          · exact absurd h1R (Finset.disjoint_left.mp hdisj h1L)
          · exact h
        have h2R : r2.val ∈ R.leaves := by
          rcases e20 with ⟨_, hv0L⟩ | ⟨h, _⟩
          · exact absurd hv0R (Finset.disjoint_left.mp hdisj hv0L)
          · exact h
        exact ⟨h0R, h1R, h2R, hv0R, hv1R, hv2R⟩
    rcases all_in_one with ⟨h0L, h1L, h2L, hv0L, hv1L, hv2L⟩ | ⟨h0R, h1R, h2R, hv0R, hv1R, hv2R⟩
    · apply ihL hroL
      intro u v hu hv
      have hRf : R.eval (oneEach u v) = false := by
        apply Formula.eval_false_of_all_false
        intro w hw
        by_contra ht
        have ht' : (oneEach u v).getD w false = true := by cases h' : (oneEach u v).getD w false <;> simp_all
        rw [oe] at ht'
        rcases ht' with rfl | rfl
        · have hu3 : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by omega
          rcases hu3 with h | h | h
          · exact Finset.disjoint_left.mp hdisj (h.symm ▸ h0L) hw
          · exact Finset.disjoint_left.mp hdisj (h.symm ▸ h1L) hw
          · exact Finset.disjoint_left.mp hdisj (h.symm ▸ h2L) hw
        · have hv3 : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
          rcases hv3 with h | h | h
          · exact Finset.disjoint_left.mp hdisj (by simpa [r0, h] using hv0L) hw
          · exact Finset.disjoint_left.mp hdisj (by simpa [r1, h] using hv1L) hw
          · exact Finset.disjoint_left.mp hdisj (by simpa [r2, h] using hv2L) hw
      have := heval u v hu hv
      simp only [Formula.eval, hRf, Bool.or_false] at this
      exact this
    · apply ihR hroR
      intro u v hu hv
      have hLf : L.eval (oneEach u v) = false := by
        apply Formula.eval_false_of_all_false
        intro w hw
        by_contra ht
        have ht' : (oneEach u v).getD w false = true := by cases h' : (oneEach u v).getD w false <;> simp_all
        rw [oe] at ht'
        rcases ht' with rfl | rfl
        · have hu3 : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by omega
          rcases hu3 with h | h | h
          · exact Finset.disjoint_right.mp hdisj (h.symm ▸ h0R) hw
          · exact Finset.disjoint_right.mp hdisj (h.symm ▸ h1R) hw
          · exact Finset.disjoint_right.mp hdisj (h.symm ▸ h2R) hw
        · have hv3 : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
          rcases hv3 with h | h | h
          · exact Finset.disjoint_right.mp hdisj (by simpa [r0, h] using hv0R) hw
          · exact Finset.disjoint_right.mp hdisj (by simpa [r1, h] using hv1R) hw
          · exact Finset.disjoint_right.mp hdisj (by simpa [r2, h] using hv2R) hw
      have := heval u v hu hv
      simp only [Formula.eval, hLf, Bool.false_or] at this
      exact this

theorem main_lb (n : ℕ) (hn : 3 ≤ n) : ¬ RepSizeAtMost (targetA n) (2 * n - 1) := by
  rintro ⟨C, hM, hs, hR⟩
  set N := n + n
  set K := Finset.range N
  set R' := backConeRec N C.gates {C.output}
  have hsub : K ⊆ R' := by
    intro k hk
    by_contra hk'
    obtain ⟨u, v, u', v', h1, h2, h3, h4⟩ := targetA_essential n hn k hk
    have e1 := hR u v
    have e2 := hR u' v'
    have hx : (oneEach u v).length = N := by simp [oneEach, N]
    have hyD : ∀ i, ((oneEach u v).set k false).getD i false =
        if i = k then false else (oneEach u v).getD i false := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
      by_cases h : k = i
      · subst h; simp only [ite_true]; split_ifs <;> rfl
      · simp [h, Ne.symm h]
    have eq := backConeRec_dep N C.gates {C.output} (oneEach u v) ((oneEach u v).set k false) hx
      (by simp [hx]) (fun i hi => by
        rw [hyD]; split_ifs with h
        · exact absurd (h ▸ hi) hk'
        · rfl) C.output (Finset.mem_singleton_self _)
    have hmo := mono C.gates (fun g hg => by simpa using (hM g hg).1) ((oneEach u v).set k false)
      (oneEach u' v') (by simp [oneEach]) (fun i hi => by
        rw [hyD] at hi
        split_ifs at hi with h
        rw [oe] at hi ⊢
        rcases hi with rfl | rfl
        · rcases h3 with h3 | rfl
          · exact absurd h3 h
          · exact Or.inl rfl
        · rcases h4 with h4 | rfl
          · exact absurd h4 h
          · exact Or.inr rfl) C.output
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [e1, h1] at eq
    rw [e2, h2] at hmo
    exact absurd (hmo eq.symm) (by simp)
  have hcard_le : R'.card ≤ ({C.output} : Finset ℕ).card + C.gates.length :=
    backConeRec_card_le N C.gates (fun g hg => (hM g hg).2) {C.output}
  have hcard_K : K.card ≤ R'.card := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard_K
  rw [Finset.card_singleton] at hcard_le
  simp only [Circuit.size] at hs
  have hR'card : R'.card = 1 + C.gates.length := by omega
  have hR'eq : K = R' := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)
  have hbound : ∀ w ∈ R', w < N := fun w hw => by
    rw [← hR'eq] at hw; exact Finset.mem_range.mp hw
  obtain ⟨F', hF'ro, _, hF'ev⟩ := tight_backCone_to_formula N C.gates
    (fun g hg => ⟨by simpa using (hM g hg).1, (hM g hg).2⟩)
    (Formula.leaf C.output) trivial
    (by simpa [Formula.leaves, R'] using hR'card)
    (by simpa [Formula.leaves, R'] using hbound)
  apply no_readOnce_targetA n hn F' hF'ro
  intro u v _ _
  have h1 := hF'ev (oneEach u v) (by simp [oneEach, N])
  have h2 := hR u v
  simp only [Formula.eval] at h1
  simp only [Circuit.eval, Circuit.wires] at h2
  change (C.gates.foldl stp (oneEach u v)).getD C.output false = targetA n u v at h2
  rw [h1, h2]

end PEqualNP.Outside.L_meta_23958_aux

theorem PEqualNP.Outside.L_meta_23958 : (∀ n : ℕ, 3 ≤ n → ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) (2 * n - 1)) :=
  PEqualNP.Outside.L_meta_23958_aux.main_lb
