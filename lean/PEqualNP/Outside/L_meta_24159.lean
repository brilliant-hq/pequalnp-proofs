import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24159_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

inductive BTree where
  | var (i : ℕ)
  | and (l r : BTree)
  | or (l r : BTree)
  | not (t : BTree)

def BTree.eval : BTree → (ℕ → Bool) → Bool
  | .var i, f => f i
  | .and l r, f => l.eval f && r.eval f
  | .or l r, f => l.eval f || r.eval f
  | .not t, f => !(t.eval f)

def BTree.vars : BTree → List ℕ
  | .var i => [i]
  | .and l r => l.vars ++ r.vars
  | .or l r => l.vars ++ r.vars
  | .not t => t.vars

def BTree.notCount : BTree → ℕ
  | .var _ => 0
  | .and l r => l.notCount + r.notCount
  | .or l r => l.notCount + r.notCount
  | .not t => t.notCount + 1

inductive MTree where
  | const (b : Bool)
  | var (i : ℕ)
  | and (l r : MTree)
  | or (l r : MTree)

def MTree.eval : MTree → (ℕ → Bool) → Bool
  | .const b, _ => b
  | .var i, f => f i
  | .and l r, f => l.eval f && r.eval f
  | .or l r, f => l.eval f || r.eval f

def MTree.vars : MTree → List ℕ
  | .const _ => []
  | .var i => [i]
  | .and l r => l.vars ++ r.vars
  | .or l r => l.vars ++ r.vars

def MTree.Clean : MTree → Prop
  | .const _ => False
  | .var _ => True
  | .and l r => l.Clean ∧ r.Clean
  | .or l r => l.Clean ∧ r.Clean

def MTree.Good (t : MTree) : Prop :=
  (∃ b, t = .const b) ∨ t.Clean

def mkAnd : MTree → MTree → MTree
  | .const false, _ => .const false
  | _, .const false => .const false
  | .const true, r => r
  | l, .const true => l
  | l, r => .and l r

def mkOr : MTree → MTree → MTree
  | .const true, _ => .const true
  | _, .const true => .const true
  | .const false, r => r
  | l, .const false => l
  | l, r => .or l r

lemma mkAnd_eval (l r : MTree) (f : ℕ → Bool) :
    (mkAnd l r).eval f = (l.eval f && r.eval f) := by
  cases l with
  | const b =>
    cases b <;> cases r with
    | const b2 => cases b2 <;> simp [mkAnd, MTree.eval]
    | _ => simp [mkAnd, MTree.eval]
  | var i =>
    cases r with
    | const b => cases b <;> simp [mkAnd, MTree.eval]
    | _ => simp [mkAnd, MTree.eval]
  | and _ _ =>
    cases r with
    | const b => cases b <;> simp [mkAnd, MTree.eval]
    | _ => simp [mkAnd, MTree.eval]
  | or _ _ =>
    cases r with
    | const b => cases b <;> simp [mkAnd, MTree.eval]
    | _ => simp [mkAnd, MTree.eval]

lemma mkOr_eval (l r : MTree) (f : ℕ → Bool) :
    (mkOr l r).eval f = (l.eval f || r.eval f) := by
  cases l with
  | const b =>
    cases b <;> cases r with
    | const b2 => cases b2 <;> simp [mkOr, MTree.eval]
    | _ => simp [mkOr, MTree.eval]
  | var i =>
    cases r with
    | const b => cases b <;> simp [mkOr, MTree.eval]
    | _ => simp [mkOr, MTree.eval]
  | and _ _ =>
    cases r with
    | const b => cases b <;> simp [mkOr, MTree.eval]
    | _ => simp [mkOr, MTree.eval]
  | or _ _ =>
    cases r with
    | const b => cases b <;> simp [mkOr, MTree.eval]
    | _ => simp [mkOr, MTree.eval]

lemma mkAnd_good {l r : MTree} (hl : l.Good) (hr : r.Good) : (mkAnd l r).Good := by
  rcases hl with ⟨b, rfl⟩ | hl
  · cases b
    · left; exact ⟨false, rfl⟩
    · rcases hr with ⟨b2, rfl⟩ | hr
      · cases b2 <;> left <;> exact ⟨_, rfl⟩
      · cases r <;> simp [mkAnd, MTree.Good, MTree.Clean] at hr ⊢
        · exact hr
        · exact hr
  · rcases hr with ⟨b2, rfl⟩ | hr
    · cases b2
      · cases l <;> simp [mkAnd, MTree.Good, MTree.Clean] at hl ⊢
      · cases l <;> simp [mkAnd, MTree.Good, MTree.Clean] at hl ⊢
        · exact hl
        · exact hl
    · cases l <;> cases r <;> simp [MTree.Clean] at hl hr <;>
        exact Or.inr ⟨hl, hr⟩

lemma mkOr_good {l r : MTree} (hl : l.Good) (hr : r.Good) : (mkOr l r).Good := by
  rcases hl with ⟨b, rfl⟩ | hl
  · cases b
    · rcases hr with ⟨b2, rfl⟩ | hr
      · cases b2 <;> left <;> exact ⟨_, rfl⟩
      · cases r <;> simp [mkOr, MTree.Good, MTree.Clean] at hr ⊢
        · exact hr
        · exact hr
    · left; exact ⟨true, rfl⟩
  · rcases hr with ⟨b2, rfl⟩ | hr
    · cases b2
      · cases l <;> simp [mkOr, MTree.Good, MTree.Clean] at hl ⊢
        · exact hl
        · exact hl
      · cases l <;> simp [mkOr, MTree.Good, MTree.Clean] at hl ⊢
    · cases l <;> cases r <;> simp [MTree.Clean] at hl hr <;>
        exact Or.inr ⟨hl, hr⟩

lemma mkAnd_vars_sublist (l r : MTree) : (mkAnd l r).vars.Sublist (l.vars ++ r.vars) := by
  cases l with
  | const b =>
    cases b
    · simp [mkAnd, MTree.vars]
    · cases r with
      | const b2 => cases b2 <;> simp [mkAnd, MTree.vars]
      | _ => simp [mkAnd, MTree.vars]
  | var _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkAnd, MTree.vars]
    | _ => simp [mkAnd, MTree.vars]
  | and _ _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkAnd, MTree.vars]
    | _ => simp [mkAnd, MTree.vars]
  | or _ _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkAnd, MTree.vars]
    | _ => simp [mkAnd, MTree.vars]

lemma mkOr_vars_sublist (l r : MTree) : (mkOr l r).vars.Sublist (l.vars ++ r.vars) := by
  cases l with
  | const b =>
    cases b
    · cases r with
      | const b2 => cases b2 <;> simp [mkOr, MTree.vars]
      | _ => simp [mkOr, MTree.vars]
    · simp [mkOr, MTree.vars]
  | var _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkOr, MTree.vars]
    | _ => simp [mkOr, MTree.vars]
  | and _ _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkOr, MTree.vars]
    | _ => simp [mkOr, MTree.vars]
  | or _ _ =>
    cases r with
    | const b2 => cases b2 <;> simp [mkOr, MTree.vars]
    | _ => simp [mkOr, MTree.vars]

lemma MTree.eval_mono (t : MTree) {f g : ℕ → Bool}
    (hfg : ∀ i, f i = true → g i = true) :
    t.eval f = true → t.eval g = true := by
  induction t with
  | const b => intro h; exact h
  | var i => exact hfg i
  | and l r ihl ihr =>
    simp [MTree.eval]
    intro hl hr
    exact ⟨ihl hl, ihr hr⟩
  | or l r ihl ihr =>
    simp [MTree.eval]
    rintro (hl | hr)
    · exact Or.inl (ihl hl)
    · exact Or.inr (ihr hr)

lemma MTree.eval_congr (t : MTree) {f g : ℕ → Bool}
    (h : ∀ i ∈ t.vars, f i = g i) : t.eval f = t.eval g := by
  induction t with
  | const _ => rfl
  | var i => exact h i (by simp [MTree.vars])
  | and l r ihl ihr =>
    simp only [MTree.eval]
    rw [ihl (fun i hi => h i (by simp [MTree.vars, hi])),
        ihr (fun i hi => h i (by simp [MTree.vars, hi]))]
  | or l r ihl ihr =>
    simp only [MTree.eval]
    rw [ihl (fun i hi => h i (by simp [MTree.vars, hi])),
        ihr (fun i hi => h i (by simp [MTree.vars, hi]))]

lemma MTree.clean_eval_false {t : MTree} (hc : t.Clean) :
    t.eval (fun _ => false) = false := by
  induction t with
  | const _ => cases hc
  | var _ => rfl
  | and l r ihl ihr =>
    simp [MTree.eval, ihl hc.1]
  | or l r ihl ihr =>
    simp [MTree.eval, ihl hc.1, ihr hc.2]

lemma MTree.clean_vars_nonempty {t : MTree} (hc : t.Clean) :
    t.vars ≠ [] := by
  induction t with
  | const _ => cases hc
  | var _ => simp [MTree.vars]
  | and l r ihl _ =>
    simp [MTree.vars, ihl hc.1]
  | or l r ihl _ =>
    simp [MTree.vars, ihl hc.1]

def BTree.toMTree : BTree → MTree
  | .var i => .var i
  | .and l r => .and l.toMTree r.toMTree
  | .or l r => .or l.toMTree r.toMTree
  | .not _ => .const false

lemma BTree.toMTree_clean {t : BTree} (h0 : t.notCount = 0) : t.toMTree.Clean := by
  induction t with
  | var _ => trivial
  | and l r ihl ihr =>
    simp [BTree.notCount] at h0
    exact ⟨ihl h0.1, ihr h0.2⟩
  | or l r ihl ihr =>
    simp [BTree.notCount] at h0
    exact ⟨ihl h0.1, ihr h0.2⟩
  | not _ => simp [BTree.notCount] at h0

lemma BTree.toMTree_vars {t : BTree} (h0 : t.notCount = 0) : t.toMTree.vars = t.vars := by
  induction t with
  | var _ => rfl
  | and l r ihl ihr =>
    simp [BTree.notCount] at h0
    simp [BTree.toMTree, MTree.vars, BTree.vars, ihl h0.1, ihr h0.2]
  | or l r ihl ihr =>
    simp [BTree.notCount] at h0
    simp [BTree.toMTree, MTree.vars, BTree.vars, ihl h0.1, ihr h0.2]
  | not _ => simp [BTree.notCount] at h0

lemma BTree.toMTree_eval {t : BTree} (h0 : t.notCount = 0) (f : ℕ → Bool) :
    t.toMTree.eval f = t.eval f := by
  induction t with
  | var _ => rfl
  | and l r ihl ihr =>
    simp [BTree.notCount] at h0
    simp [BTree.toMTree, MTree.eval, BTree.eval, ihl h0.1, ihr h0.2]
  | or l r ihl ihr =>
    simp [BTree.notCount] at h0
    simp [BTree.toMTree, MTree.eval, BTree.eval, ihl h0.1, ihr h0.2]
  | not _ => simp [BTree.notCount] at h0

def BTree.splitOne : BTree → MTree × MTree × MTree
  | .var _ => (.const false, .const false, .const false)
  | .not s => (s.toMTree, .const true, .const false)
  | .and l r =>
    if l.notCount = 1 then
      let p := l.splitOne
      let tr := r.toMTree
      (p.1, mkAnd p.2.1 tr, mkAnd p.2.2 tr)
    else
      let p := r.splitOne
      let tl := l.toMTree
      (p.1, mkAnd tl p.2.1, mkAnd tl p.2.2)
  | .or l r =>
    if l.notCount = 1 then
      let p := l.splitOne
      let tr := r.toMTree
      (p.1, mkOr p.2.1 tr, mkOr p.2.2 tr)
    else
      let p := r.splitOne
      let tl := l.toMTree
      (p.1, mkOr tl p.2.1, mkOr tl p.2.2)

lemma bool_and_split (b h a r : Bool) :
    ((b || (!h && a)) && r) = ((b && r) || (!h && (a && r))) := by
  cases b <;> cases h <;> cases a <;> cases r <;> rfl

lemma bool_and_split_left (b h a l : Bool) :
    (l && (b || (!h && a))) = ((l && b) || (!h && (l && a))) := by
  cases b <;> cases h <;> cases a <;> cases l <;> rfl

lemma bool_or_split (b h a r : Bool) :
    ((b || (!h && a)) || r) = ((b || r) || (!h && (a || r))) := by
  cases b <;> cases h <;> cases a <;> cases r <;> rfl

lemma bool_or_split_left (b h a l : Bool) :
    (l || (b || (!h && a))) = ((l || b) || (!h && (l || a))) := by
  cases b <;> cases h <;> cases a <;> cases l <;> rfl

lemma sublist_nodup {α : Type*} {l₁ l₂ : List α} (hs : l₁.Sublist l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist hs

lemma BTree.splitOne_spec (t : BTree) (h1 : t.notCount = 1) (hnd : t.vars.Nodup) :
    let p := t.splitOne
    p.1.Clean ∧ p.2.1.Good ∧ p.2.2.Good ∧
    p.1.vars.Sublist t.vars ∧
    p.2.1.vars.Sublist t.vars ∧
    p.2.2.vars.Sublist t.vars ∧
    (∀ i ∈ p.2.1.vars, i ∉ p.1.vars) ∧
    (∀ i ∈ p.2.2.vars, i ∉ p.1.vars) ∧
    (∀ f, p.2.2.eval f = true → p.2.1.eval f = true) ∧
    (∀ f, t.eval f = (p.2.2.eval f || (!(p.1.eval f) && p.2.1.eval f))) := by
  induction t with
  | var _ => simp [BTree.notCount] at h1
  | not s =>
    have hs0 : s.notCount = 0 := by simp [BTree.notCount] at h1; omega
    refine ⟨s.toMTree_clean hs0, Or.inl ⟨true, rfl⟩, Or.inl ⟨false, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [BTree.splitOne, BTree.vars, s.toMTree_vars hs0]
    · simp [BTree.splitOne, MTree.vars]
    · simp [BTree.splitOne, MTree.vars]
    · simp [BTree.splitOne, MTree.vars]
    · simp [BTree.splitOne, MTree.vars]
    · intro f hf; simp [BTree.splitOne, MTree.eval] at hf
    · intro f; simp [BTree.splitOne, BTree.eval, MTree.eval, s.toMTree_eval hs0]
  | and l r ihl ihr =>
    simp only [BTree.notCount, BTree.vars] at h1 hnd
    have hndl : l.vars.Nodup := (List.nodup_append.mp hnd).1
    have hndr : r.vars.Nodup := (List.nodup_append.mp hnd).2.1
    have hdisj : ∀ x ∈ l.vars, x ∉ r.vars :=
      fun x hx hxr => (List.nodup_append.mp hnd).2.2 x hx x hxr rfl
    by_cases hl1 : l.notCount = 1
    · have hr0 : r.notCount = 0 := by omega
      rcases ihl hl1 hndl with ⟨hcH, hgA, hgB, hsH, hsA, hsB, hdA, hdB, hba, hev⟩
      have hcr : r.toMTree.Clean := r.toMTree_clean hr0
      have hvr : r.toMTree.vars = r.vars := r.toMTree_vars hr0
      simp only [BTree.splitOne, hl1, ↓reduceIte]
      refine ⟨hcH, mkAnd_good hgA (Or.inr hcr), mkAnd_good hgB (Or.inr hcr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hsH.trans (List.sublist_append_left l.vars r.vars)
      · exact (mkAnd_vars_sublist _ _).trans (by rw [hvr]; exact hsA.append (List.Sublist.refl _))
      · exact (mkAnd_vars_sublist _ _).trans (by rw [hvr]; exact hsB.append (List.Sublist.refl _))
      · intro i hi hiH
        have hm := (mkAnd_vars_sublist _ _).subset hi
        rw [List.mem_append, hvr] at hm
        rcases hm with hmA | hmr
        · exact hdA i hmA hiH
        · exact hdisj i (hsH.subset hiH) hmr
      · intro i hi hiH
        have hm := (mkAnd_vars_sublist _ _).subset hi
        rw [List.mem_append, hvr] at hm
        rcases hm with hmB | hmr
        · exact hdB i hmB hiH
        · exact hdisj i (hsH.subset hiH) hmr
      · intro f hf
        rw [mkAnd_eval] at hf ⊢
        simp only [Bool.and_eq_true] at hf ⊢
        exact ⟨hba f hf.1, hf.2⟩
      · intro f
        simp only [BTree.eval, mkAnd_eval, hev f, r.toMTree_eval hr0]
        exact bool_and_split _ _ _ _
    · have hr1 : r.notCount = 1 := by omega
      have hl0 : l.notCount = 0 := by omega
      rcases ihr hr1 hndr with ⟨hcH, hgA, hgB, hsH, hsA, hsB, hdA, hdB, hba, hev⟩
      have hcl : l.toMTree.Clean := l.toMTree_clean hl0
      have hvl : l.toMTree.vars = l.vars := l.toMTree_vars hl0
      simp only [BTree.splitOne, hl1, ↓reduceIte]
      refine ⟨hcH, mkAnd_good (Or.inr hcl) hgA, mkAnd_good (Or.inr hcl) hgB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hsH.trans (List.sublist_append_right l.vars r.vars)
      · exact (mkAnd_vars_sublist _ _).trans (by rw [hvl]; exact (List.Sublist.refl _).append hsA)
      · exact (mkAnd_vars_sublist _ _).trans (by rw [hvl]; exact (List.Sublist.refl _).append hsB)
      · intro i hi hiH
        have hm := (mkAnd_vars_sublist _ _).subset hi
        rw [List.mem_append, hvl] at hm
        rcases hm with hml | hmA
        · exact hdisj i hml (hsH.subset hiH)
        · exact hdA i hmA hiH
      · intro i hi hiH
        have hm := (mkAnd_vars_sublist _ _).subset hi
        rw [List.mem_append, hvl] at hm
        rcases hm with hml | hmB
        · exact hdisj i hml (hsH.subset hiH)
        · exact hdB i hmB hiH
      · intro f hf
        rw [mkAnd_eval] at hf ⊢
        simp only [Bool.and_eq_true] at hf ⊢
        exact ⟨hf.1, hba f hf.2⟩
      · intro f
        simp only [BTree.eval, mkAnd_eval, hev f, l.toMTree_eval hl0]
        exact bool_and_split_left _ _ _ _
  | or l r ihl ihr =>
    simp only [BTree.notCount, BTree.vars] at h1 hnd
    have hndl : l.vars.Nodup := (List.nodup_append.mp hnd).1
    have hndr : r.vars.Nodup := (List.nodup_append.mp hnd).2.1
    have hdisj : ∀ x ∈ l.vars, x ∉ r.vars :=
      fun x hx hxr => (List.nodup_append.mp hnd).2.2 x hx x hxr rfl
    by_cases hl1 : l.notCount = 1
    · have hr0 : r.notCount = 0 := by omega
      rcases ihl hl1 hndl with ⟨hcH, hgA, hgB, hsH, hsA, hsB, hdA, hdB, hba, hev⟩
      have hcr : r.toMTree.Clean := r.toMTree_clean hr0
      have hvr : r.toMTree.vars = r.vars := r.toMTree_vars hr0
      simp only [BTree.splitOne, hl1, ↓reduceIte]
      refine ⟨hcH, mkOr_good hgA (Or.inr hcr), mkOr_good hgB (Or.inr hcr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hsH.trans (List.sublist_append_left l.vars r.vars)
      · exact (mkOr_vars_sublist _ _).trans (by rw [hvr]; exact hsA.append (List.Sublist.refl _))
      · exact (mkOr_vars_sublist _ _).trans (by rw [hvr]; exact hsB.append (List.Sublist.refl _))
      · intro i hi hiH
        have hm := (mkOr_vars_sublist _ _).subset hi
        rw [List.mem_append, hvr] at hm
        rcases hm with hmA | hmr
        · exact hdA i hmA hiH
        · exact hdisj i (hsH.subset hiH) hmr
      · intro i hi hiH
        have hm := (mkOr_vars_sublist _ _).subset hi
        rw [List.mem_append, hvr] at hm
        rcases hm with hmB | hmr
        · exact hdB i hmB hiH
        · exact hdisj i (hsH.subset hiH) hmr
      · intro f hf
        rw [mkOr_eval] at hf ⊢
        simp only [Bool.or_eq_true] at hf ⊢
        rcases hf with hb | hr
        · exact Or.inl (hba f hb)
        · exact Or.inr hr
      · intro f
        simp only [BTree.eval, mkOr_eval, hev f, r.toMTree_eval hr0]
        exact bool_or_split _ _ _ _
    · have hr1 : r.notCount = 1 := by omega
      have hl0 : l.notCount = 0 := by omega
      rcases ihr hr1 hndr with ⟨hcH, hgA, hgB, hsH, hsA, hsB, hdA, hdB, hba, hev⟩
      have hcl : l.toMTree.Clean := l.toMTree_clean hl0
      have hvl : l.toMTree.vars = l.vars := l.toMTree_vars hl0
      simp only [BTree.splitOne, hl1, ↓reduceIte]
      refine ⟨hcH, mkOr_good (Or.inr hcl) hgA, mkOr_good (Or.inr hcl) hgB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hsH.trans (List.sublist_append_right l.vars r.vars)
      · exact (mkOr_vars_sublist _ _).trans (by rw [hvl]; exact (List.Sublist.refl _).append hsA)
      · exact (mkOr_vars_sublist _ _).trans (by rw [hvl]; exact (List.Sublist.refl _).append hsB)
      · intro i hi hiH
        have hm := (mkOr_vars_sublist _ _).subset hi
        rw [List.mem_append, hvl] at hm
        rcases hm with hml | hmA
        · exact hdisj i hml (hsH.subset hiH)
        · exact hdA i hmA hiH
      · intro i hi hiH
        have hm := (mkOr_vars_sublist _ _).subset hi
        rw [List.mem_append, hvl] at hm
        rcases hm with hml | hmB
        · exact hdisj i hml (hsH.subset hiH)
        · exact hdB i hmB hiH
      · intro f hf
        rw [mkOr_eval] at hf ⊢
        simp only [Bool.or_eq_true] at hf ⊢
        rcases hf with hl | hb
        · exact Or.inl hl
        · exact Or.inr (hba f hb)
      · intro f
        simp only [BTree.eval, mkOr_eval, hev f, l.toMTree_eval hl0]
        exact bool_or_split_left _ _ _ _

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl, stepWire, ih]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl]
    have hlen : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlen]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma circuit_wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_stepWire_len C.gates x

lemma circuit_wires_getD_input (C : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_stepWire_getD_lt C.gates x hi

lemma list_split_at_getD {α : Type*} (l : List α) {j : ℕ} (hj : j < l.length) (d : α) :
    l = l.take j ++ (l.getD j d) :: l.drop (j + 1) := by
  have h1 : l.take j ++ l.drop j = l := List.take_append_drop j l
  have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
  have h3 : l.getD j d = l[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [h3, ← h2, h1]

lemma stepWire_getD_last (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma circuit_wires_getD_gate (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x : List Bool)
    (hx : x.length = N) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) :=
    list_split_at_getD C.gates hj ⟨GateOp.or, []⟩
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hwires : C.wires x = C.gates.foldl stepWire x := rfl
  rw [hwires]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set w0 := (C.gates.take j).foldl stepWire x
  have hw0_len : w0.length = N + j := by
    rw [foldl_stepWire_len, hx, htake_len]
  have hstep_len : N + j < (stepWire w0 (gateAt C j)).length := by
    simp [stepWire, hw0_len]
  rw [foldl_stepWire_getD_lt _ _ hstep_len]
  have hget : (stepWire w0 (gateAt C j)).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w0.getD i false) := by
    rw [← hw0_len]
    exact stepWire_getD_last w0 (gateAt C j)
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < N + j := hRB j hj i hi
  have hpre : ((gateAt C j :: C.gates.drop (j + 1)).foldl stepWire w0).getD i false =
      w0.getD i false := foldl_stepWire_getD_lt _ _ (by omega)
  have hfull : (C.gates.foldl stepWire x).getD i false = w0.getD i false := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    exact hpre
  exact hfull.symm

def wireTree (N : ℕ) (D : Circuit) (w : ℕ) : BTree :=
  if _hw : w < N then .var w
  else
    let j := w - N
    if _hj : j < D.gates.length then
      let g := gateAt D j
      match g.op, g.inputs with
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireTree N D a) (wireTree N D b)
          else .var 0
        else .var 0
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireTree N D a) (wireTree N D b)
          else .var 0
        else .var 0
      | .not, [a] =>
        if _ha : a < w then .not (wireTree N D a)
        else .var 0
      | _, _ => .var 0
    else .var 0
termination_by w

lemma gateAt_mem {D : Circuit} {j : ℕ} (hj : j < D.gates.length) :
    gateAt D j ∈ D.gates := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

lemma gateAt_eq_getD_any {D : Circuit} {j : ℕ} (hj : j < D.gates.length) (d : Gate) :
    D.gates.getD j d = gateAt D j := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wireTree_eval (N : ℕ) (D : Circuit)
    (hGates : ∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hRB : ReadsBack N D) (x : List Bool) (hx : x.length = N) :
    ∀ w < N + D.gates.length,
      (D.wires x).getD w false = (wireTree N D w).eval (fun i => x.getD i false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < N
    · rw [wireTree]
      simp only [hlt, ↓reduceDIte, BTree.eval]
      exact circuit_wires_getD_input D x (by omega)
    · have hj : w - N < D.gates.length := by omega
      have hw_eq : w = N + (w - N) := by omega
      have hgm : gateAt D (w - N) ∈ D.gates := gateAt_mem hj
      have hgw := circuit_wires_getD_gate N D hRB x hx hj
      rw [← hw_eq] at hgw
      rw [hgw]
      rw [wireTree]
      simp only [hlt, ↓reduceDIte, hj]
      rcases hGates (gateAt D (w - N)) hgm with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
      · rcases List.length_eq_two.mp hlen with ⟨a, b, hinp⟩
        have ha : a < w := by
          have := hRB (w - N) hj a (by rw [hinp]; simp)
          omega
        have hb : b < w := by
          have := hRB (w - N) hj b (by rw [hinp]; simp)
          omega
        rcases hop with hand | hor
        · simp only [hand, hinp, ha, hb, ↓reduceDIte, List.map_cons, List.map_nil, GateOp.eval,
            BTree.eval]
          rw [ih a ha (by omega), ih b hb (by omega)]
          simp
        · simp only [hor, hinp, ha, hb, ↓reduceDIte, List.map_cons, List.map_nil, GateOp.eval,
            BTree.eval]
          rw [ih a ha (by omega), ih b hb (by omega)]
          simp
      · rcases List.length_eq_one_iff.mp hlen with ⟨a, hinp⟩
        have ha : a < w := by
          have := hRB (w - N) hj a (by rw [hinp]; simp)
          omega
        simp only [hop, hinp, ha, ↓reduceDIte, List.map_cons, List.map_nil, GateOp.eval, BTree.eval]
        rw [ih a ha (by omega)]
        simp

def countWire (N : ℕ) (D : Circuit) (u : ℕ) (w : ℕ) : ℕ :=
  if _hw : w < N then
    if w = u then 1 else 0
  else
    let j := w - N
    if _hj : j < D.gates.length then
      (if w = u then 1 else 0) +
        ((gateAt D j).inputs.map (fun c => if _hc : c < w then countWire N D u c else 0)).sum
    else 0
termination_by w

lemma countWire_gate (N : ℕ) (D : Circuit) (hRB : ReadsBack N D) (u : ℕ)
    {j : ℕ} (hj : j < D.gates.length) :
    countWire N D u (N + j) =
      (if N + j = u then 1 else 0) + ((gateAt D j).inputs.map (countWire N D u)).sum := by
  rw [countWire]
  have hnotlt : ¬ (N + j < N) := by omega
  have hsub : N + j - N = j := by omega
  simp only [hnotlt, ↓reduceDIte, hsub, hj]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  have hlt : c < N + j := hRB j hj c hc
  simp [hlt]

lemma countWire_input (N : ℕ) (D : Circuit) (u : ℕ) {i : ℕ} (hi : i < N) :
    countWire N D u i = if i = u then 1 else 0 := by
  rw [countWire]
  simp [hi]

lemma list_map_sum_eq_sum_count {l : List ℕ} {M : ℕ} (hl : ∀ c ∈ l, c < M) (f : ℕ → ℕ) :
    (l.map f).sum = ∑ w ∈ Finset.range M, l.count w * f w := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a < M := hl a (by simp)
    have ht : ∀ c ∈ t, c < M := fun c hc => hl c (by simp [hc])
    rw [List.map_cons, List.sum_cons, ih ht]
    have hcnt : ∀ w, (a :: t).count w = (if w = a then 1 else 0) + t.count w := by
      intro w
      rw [List.count_cons]
      by_cases h : w = a
      · subst h; simp [Nat.add_comm]
      · have hne : (a == w) = false := beq_false_of_ne (Ne.symm h)
        simp [h, hne]
    simp_rw [hcnt, Nat.add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [hba]
    · intro ha'; exact False.elim (ha' (Finset.mem_range.mpr ha))

lemma countWire_output_eq (N : ℕ) (D : Circuit) (hRB : ReadsBack N D)
    (hPos : 0 < D.gates.length)
    (hGateRead : ∀ j < D.gates.length,
      readsIn D (Finset.range D.gates.length) (N + j) = if j + 1 = D.gates.length then 0 else 1)
    (u : ℕ) :
    countWire N D u (N + (D.gates.length - 1)) =
      (∑ j ∈ Finset.range D.gates.length, if N + j = u then 1 else 0) +
      (∑ i ∈ Finset.range N, readsIn D (Finset.range D.gates.length) i * (if i = u then 1 else 0)) := by
  set S := D.gates.length
  have h1 : ∑ j ∈ Finset.range S, countWire N D u (N + j) =
      (∑ j ∈ Finset.range S, if N + j = u then 1 else 0) +
      ∑ j ∈ Finset.range S, ((gateAt D j).inputs.map (countWire N D u)).sum := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact countWire_gate N D hRB u (Finset.mem_range.mp hj)
  have h2 : ∑ j ∈ Finset.range S, ((gateAt D j).inputs.map (countWire N D u)).sum =
      ∑ w ∈ Finset.range (N + S), readsIn D (Finset.range S) w * countWire N D u w := by
    have hinner : ∀ j ∈ Finset.range S,
        ((gateAt D j).inputs.map (countWire N D u)).sum =
        ∑ w ∈ Finset.range (N + S), (gateAt D j).inputs.count w * countWire N D u w := by
      intro j hj
      have hjlt : j < S := Finset.mem_range.mp hj
      apply list_map_sum_eq_sum_count
      intro c hc
      have := hRB j hjlt c hc
      omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    simp only [readsIn, Finset.sum_mul]
  rw [h2, Finset.sum_range_add] at h1
  have hIn : ∑ i ∈ Finset.range N, readsIn D (Finset.range S) i * countWire N D u i =
      ∑ i ∈ Finset.range N, readsIn D (Finset.range S) i * (if i = u then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [countWire_input N D u (Finset.mem_range.mp hi)]
  have hsplit_sum : ∀ f : ℕ → ℕ, ∑ j ∈ Finset.range S, f j =
      (∑ j ∈ Finset.range (S - 1), f j) + f (S - 1) := by
    intro f
    have hS : S = (S - 1) + 1 := by omega
    conv_lhs => rw [hS]
    rw [Finset.sum_range_succ]
  have hGt : ∑ j ∈ Finset.range S, readsIn D (Finset.range S) (N + j) * countWire N D u (N + j) =
      ∑ j ∈ Finset.range (S - 1), countWire N D u (N + j) := by
    rw [hsplit_sum]
    have hlast : readsIn D (Finset.range S) (N + (S - 1)) = 0 := by
      rw [hGateRead (S - 1) (by omega)]
      simp [show S - 1 + 1 = S by omega]
    rw [hlast, Nat.zero_mul, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < S - 1 := Finset.mem_range.mp hj
    rw [hGateRead j (by omega)]
    have hne : j + 1 ≠ S := by omega
    simp [hne]
  have hLHS : ∑ j ∈ Finset.range S, countWire N D u (N + j) =
      (∑ j ∈ Finset.range (S - 1), countWire N D u (N + j)) + countWire N D u (N + (S - 1)) :=
    hsplit_sum (fun j => countWire N D u (N + j))
  rw [hIn, hGt, hLHS] at h1
  omega

lemma wireTree_vars_count_eq (N : ℕ) (D : Circuit)
    (hGates : ∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hRB : ReadsBack N D) (u : ℕ) (hu : u < N) :
    ∀ w < N + D.gates.length, (wireTree N D w).vars.count u = countWire N D u w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < N
    · rw [wireTree, countWire_input N D u hlt]
      simp only [hlt, ↓reduceDIte, BTree.vars]
      by_cases hwu : w = u
      · subst hwu; simp
      · simp [hwu]
    · have hj : w - N < D.gates.length := by omega
      have hw_eq : w = N + (w - N) := by omega
      have hgm : gateAt D (w - N) ∈ D.gates := gateAt_mem hj
      have hcw := countWire_gate N D hRB u hj
      rw [← hw_eq] at hcw
      have hne : w ≠ u := by omega
      rw [hcw]
      simp only [hne, ↓reduceIte, Nat.zero_add]
      rw [wireTree]
      simp only [hlt, ↓reduceDIte, hj]
      rcases hGates (gateAt D (w - N)) hgm with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
      · rcases List.length_eq_two.mp hlen with ⟨a, b, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        have hb : b < w := by have := hRB (w - N) hj b (by rw [hinp]; simp); omega
        rcases hop with hand | hor
        · simp [hand, hinp, ha, hb, BTree.vars, ih a ha (by omega), ih b hb (by omega)]
        · simp [hor, hinp, ha, hb, BTree.vars, ih a ha (by omega), ih b hb (by omega)]
      · rcases List.length_eq_one_iff.mp hlen with ⟨a, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        simp [hop, hinp, ha, BTree.vars, ih a ha (by omega)]

lemma wireTree_vars_lt (N : ℕ) (D : Circuit)
    (hGates : ∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hRB : ReadsBack N D) :
    ∀ w < N + D.gates.length, ∀ i ∈ (wireTree N D w).vars, i < N := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw i hi
    by_cases hlt : w < N
    · rw [wireTree] at hi
      simp only [hlt, ↓reduceDIte, BTree.vars, List.mem_singleton] at hi
      omega
    · have hj : w - N < D.gates.length := by omega
      have hgm : gateAt D (w - N) ∈ D.gates := gateAt_mem hj
      rw [wireTree] at hi
      simp only [hlt, ↓reduceDIte, hj] at hi
      rcases hGates (gateAt D (w - N)) hgm with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
      · rcases List.length_eq_two.mp hlen with ⟨a, b, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        have hb : b < w := by have := hRB (w - N) hj b (by rw [hinp]; simp); omega
        rcases hop with hand | hor
        · simp only [hand, hinp, ha, hb, ↓reduceDIte, BTree.vars, List.mem_append] at hi
          rcases hi with hia | hib
          · exact ih a ha (by omega) i hia
          · exact ih b hb (by omega) i hib
        · simp only [hor, hinp, ha, hb, ↓reduceDIte, BTree.vars, List.mem_append] at hi
          rcases hi with hia | hib
          · exact ih a ha (by omega) i hia
          · exact ih b hb (by omega) i hib
      · rcases List.length_eq_one_iff.mp hlen with ⟨a, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        simp only [hop, hinp, ha, ↓reduceDIte, BTree.vars] at hi
        exact ih a ha (by omega) i hi

lemma wireTree_notCount_eq (N : ℕ) (D : Circuit)
    (hGates : ∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hRB : ReadsBack N D) (j0 : ℕ)
    (hNot : ∀ j < D.gates.length, (D.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.not ↔ j = j0) :
    ∀ w < N + D.gates.length, (wireTree N D w).notCount = countWire N D (N + j0) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < N
    · rw [wireTree, countWire_input N D (N + j0) hlt]
      have hne : w ≠ N + j0 := by omega
      simp [hlt, hne, BTree.notCount]
    · have hj : w - N < D.gates.length := by omega
      have hw_eq : w = N + (w - N) := by omega
      have hgm : gateAt D (w - N) ∈ D.gates := gateAt_mem hj
      have hcw := countWire_gate N D hRB (N + j0) hj
      rw [← hw_eq] at hcw
      rw [hcw]
      rw [wireTree]
      simp only [hlt, ↓reduceDIte, hj]
      have hnot_iff : (gateAt D (w - N)).op = GateOp.not ↔ w - N = j0 := by
        rw [← gateAt_eq_getD_any hj ⟨GateOp.and, []⟩]
        exact hNot (w - N) hj
      rcases hGates (gateAt D (w - N)) hgm with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
      · rcases List.length_eq_two.mp hlen with ⟨a, b, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        have hb : b < w := by have := hRB (w - N) hj b (by rw [hinp]; simp); omega
        have hne : w ≠ N + j0 := by
          intro heq
          have hj0 : w - N = j0 := by omega
          have := hnot_iff.mpr hj0
          rcases hop with h | h <;> rw [h] at this <;> cases this
        rcases hop with hand | hor
        · simp [hand, hinp, ha, hb, hne, BTree.notCount, ih a ha (by omega), ih b hb (by omega)]
        · simp [hor, hinp, ha, hb, hne, BTree.notCount, ih a ha (by omega), ih b hb (by omega)]
      · rcases List.length_eq_one_iff.mp hlen with ⟨a, hinp⟩
        have ha : a < w := by have := hRB (w - N) hj a (by rw [hinp]; simp); omega
        have heq : w = N + j0 := by
          have := hnot_iff.mp hop
          omega
        simp only [hop, hinp, ha, ↓reduceDIte, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero, BTree.notCount]
        simp only [heq, ↓reduceIte]
        rw [ih a ha (by omega)]
        omega

def compileGates (base : ℕ) : MTree → List Gate × ℕ
  | .const _ => ([], 0)
  | .var i => ([], i)
  | .and l r =>
    let pl := compileGates base l
    let pr := compileGates (base + pl.1.length) r
    (pl.1 ++ pr.1 ++ [⟨GateOp.and, [pl.2, pr.2]⟩], base + pl.1.length + pr.1.length)
  | .or l r =>
    let pl := compileGates base l
    let pr := compileGates (base + pl.1.length) r
    (pl.1 ++ pr.1 ++ [⟨GateOp.or, [pl.2, pr.2]⟩], base + pl.1.length + pr.1.length)

def listReads (gs : List Gate) (u : ℕ) : ℕ :=
  (gs.map (fun g => g.inputs.count u)).sum

lemma listReads_append (g1 g2 : List Gate) (u : ℕ) :
    listReads (g1 ++ g2) u = listReads g1 u + listReads g2 u := by
  simp [listReads]

lemma readsIn_range_eq_listReads (C : Circuit) (u : ℕ) :
    readsIn C (Finset.range C.size) u = listReads C.gates u := by
  rcases C with ⟨gs, out⟩
  unfold readsIn Circuit.size listReads
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
        List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    have hpre : ∀ j ∈ Finset.range gs.length,
        (gateAt ⟨gs ++ [g], out⟩ j).inputs.count u =
        (gateAt ⟨gs, out⟩ j).inputs.count u := by
      intro j hj
      have hjlt : j < gs.length := Finset.mem_range.mp hj
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
    rw [Finset.sum_congr rfl hpre, ih]
    simp [gateAt, List.getD_eq_getElem?_getD]

lemma listReads_bin_gate (op : GateOp) (a b u : ℕ) :
    listReads [⟨op, [a, b]⟩] u = (if u = a then 1 else 0) + (if u = b then 1 else 0) := by
  simp only [listReads, List.map_singleton, List.sum_singleton, List.count_cons,
    List.count_nil, Nat.zero_add, beq_iff_eq]
  split_ifs <;> omega

lemma compileGates_spec (N : ℕ) (t : MTree) (hc : t.Clean) (hlt : ∀ i ∈ t.vars, i < N) :
    ∀ base, N ≤ base →
      let p := compileGates base t
      (∀ g ∈ p.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ((p.1.length = 0 ∧ p.2 < N) ∨ (0 < p.1.length ∧ p.2 + 1 = base + p.1.length)) ∧
      (∀ j < p.1.length, ∀ i ∈ (p.1.getD j ⟨GateOp.or, []⟩).inputs, i < base + j) ∧
      (∀ u, listReads p.1 u + (if u = p.2 then 1 else 0) =
        t.vars.count u + (if base ≤ u ∧ u < base + p.1.length then 1 else 0)) ∧
      (∀ (pref : List Bool) (f : ℕ → Bool), pref.length = base →
        (∀ i ∈ t.vars, pref.getD i false = f i) →
        (p.1.foldl stepWire pref).getD p.2 false = t.eval f) := by
  induction t with
  | const _ => cases hc
  | var i =>
    intro base hbase
    have hi : i < N := hlt i (by simp [MTree.vars])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp [compileGates] at hg
    · left; exact ⟨rfl, hi⟩
    · intro j hj; simp [compileGates] at hj
    · intro u
      simp only [compileGates, listReads, List.map_nil, List.sum_nil, List.length_nil,
        Nat.add_zero, Nat.zero_add, MTree.vars]
      have hnot : ¬ (base ≤ u ∧ u < base) := by omega
      simp only [hnot, ↓reduceIte, Nat.add_zero]
      by_cases hui : u = i
      · subst hui; simp
      · simp [hui, Ne.symm hui]
    · intro pref f _ hpf
      simp only [compileGates, List.foldl_nil, MTree.eval]
      exact hpf i (by simp [MTree.vars])
  | and l r ihl ihr =>
    intro base hbase
    have hltl : ∀ i ∈ l.vars, i < N := fun i hi => hlt i (by simp [MTree.vars, hi])
    have hltr : ∀ i ∈ r.vars, i < N := fun i hi => hlt i (by simp [MTree.vars, hi])
    dsimp only [compileGates]
    rcases ihl hc.1 hltl base hbase with ⟨hgl, houtl, hrbl, hrl, hevl⟩
    set pl := compileGates base l
    rcases ihr hc.2 hltr (base + pl.1.length) (by omega) with ⟨hgr, houtr, hrbr, hrr, hevr⟩
    set pr := compileGates (base + pl.1.length) r
    have hwl_lt : pl.2 < base + pl.1.length := by rcases houtl with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hwr_lt : pr.2 < base + pl.1.length + pr.1.length := by rcases houtr with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact hgl g hg
      · exact hgr g hg
      · exact ⟨Or.inl rfl, rfl⟩
    · right
      simp only [List.length_append, List.length_singleton]
      constructor <;> omega
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hj1 : j < pl.1.length
      · have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.and, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
            pl.1.getD j ⟨GateOp.or, []⟩ := by
          rw [List.append_assoc]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
        rw [hgd] at hi
        exact hrbl j hj1 i hi
      · by_cases hj2 : j < pl.1.length + pr.1.length
        · have hj2' : j - pl.1.length < pr.1.length := by omega
          have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.and, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
              pr.1.getD (j - pl.1.length) ⟨GateOp.or, []⟩ := by
            have hlt12 : j < (pl.1 ++ pr.1).length := by simp; omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt12]
            rw [List.getElem?_append_right (by omega)]
          rw [hgd] at hi
          have := hrbr (j - pl.1.length) hj2' i hi
          omega
        · have hjeq : j = (pl.1 ++ pr.1).length := by simp; omega
          have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.and, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
              (⟨GateOp.and, [pl.2, pr.2]⟩ : Gate) := by
            simp [List.getD_eq_getElem?_getD, hjeq]
          rw [hgd] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · intro u
      simp only [listReads_append, MTree.vars, List.count_append,
        List.length_append, List.length_singleton, listReads_bin_gate]
      have hl_eq := hrl u
      have hr_eq := hrr u
      have hint : (if base ≤ u ∧ u < base + pl.1.length then 1 else 0) +
          (if base + pl.1.length ≤ u ∧ u < base + pl.1.length + pr.1.length then 1 else 0) +
          (if u = base + pl.1.length + pr.1.length then 1 else 0) =
          (if base ≤ u ∧ u < base + (pl.1.length + pr.1.length + 1) then 1 else 0) := by
        split_ifs <;> omega
      omega
    · intro pref f hpref hpf
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set w1 := pl.1.foldl stepWire pref
      have hw1_len : w1.length = base + pl.1.length := by
        rw [foldl_stepWire_len, hpref]
      have hw1_r : ∀ i ∈ r.vars, w1.getD i false = f i := by
        intro i hi
        have hilt : i < pref.length := by have := hltr i hi; omega
        rw [foldl_stepWire_getD_lt pl.1 pref hilt]
        exact hpf i (by simp [MTree.vars, hi])
      set w2 := pr.1.foldl stepWire w1
      have hw2_len : w2.length = base + pl.1.length + pr.1.length := by
        rw [foldl_stepWire_len, hw1_len]
      have hw2_wl : w2.getD pl.2 false = l.eval f := by
        rw [foldl_stepWire_getD_lt pr.1 w1 (by omega)]
        exact hevl pref f hpref (fun i hi => hpf i (by simp [MTree.vars, hi]))
      have hw2_wr : w2.getD pr.2 false = r.eval f := hevr w1 f hw1_len hw1_r
      rw [← hw2_len, stepWire_getD_last]
      simp only [List.map_cons, List.map_nil, GateOp.eval, MTree.eval]
      rw [hw2_wl, hw2_wr]
      simp
  | or l r ihl ihr =>
    intro base hbase
    have hltl : ∀ i ∈ l.vars, i < N := fun i hi => hlt i (by simp [MTree.vars, hi])
    have hltr : ∀ i ∈ r.vars, i < N := fun i hi => hlt i (by simp [MTree.vars, hi])
    dsimp only [compileGates]
    rcases ihl hc.1 hltl base hbase with ⟨hgl, houtl, hrbl, hrl, hevl⟩
    set pl := compileGates base l
    rcases ihr hc.2 hltr (base + pl.1.length) (by omega) with ⟨hgr, houtr, hrbr, hrr, hevr⟩
    set pr := compileGates (base + pl.1.length) r
    have hwl_lt : pl.2 < base + pl.1.length := by rcases houtl with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hwr_lt : pr.2 < base + pl.1.length + pr.1.length := by rcases houtr with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact hgl g hg
      · exact hgr g hg
      · exact ⟨Or.inr rfl, rfl⟩
    · right
      simp only [List.length_append, List.length_singleton]
      constructor <;> omega
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hj1 : j < pl.1.length
      · have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.or, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
            pl.1.getD j ⟨GateOp.or, []⟩ := by
          rw [List.append_assoc]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
        rw [hgd] at hi
        exact hrbl j hj1 i hi
      · by_cases hj2 : j < pl.1.length + pr.1.length
        · have hj2' : j - pl.1.length < pr.1.length := by omega
          have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.or, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
              pr.1.getD (j - pl.1.length) ⟨GateOp.or, []⟩ := by
            have hlt12 : j < (pl.1 ++ pr.1).length := by simp; omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt12]
            rw [List.getElem?_append_right (by omega)]
          rw [hgd] at hi
          have := hrbr (j - pl.1.length) hj2' i hi
          omega
        · have hjeq : j = (pl.1 ++ pr.1).length := by simp; omega
          have hgd : (pl.1 ++ pr.1 ++ [(⟨GateOp.or, [pl.2, pr.2]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩ =
              (⟨GateOp.or, [pl.2, pr.2]⟩ : Gate) := by
            simp [List.getD_eq_getElem?_getD, hjeq]
          rw [hgd] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · intro u
      simp only [listReads_append, MTree.vars, List.count_append,
        List.length_append, List.length_singleton, listReads_bin_gate]
      have hl_eq := hrl u
      have hr_eq := hrr u
      have hint : (if base ≤ u ∧ u < base + pl.1.length then 1 else 0) +
          (if base + pl.1.length ≤ u ∧ u < base + pl.1.length + pr.1.length then 1 else 0) +
          (if u = base + pl.1.length + pr.1.length then 1 else 0) =
          (if base ≤ u ∧ u < base + (pl.1.length + pr.1.length + 1) then 1 else 0) := by
        split_ifs <;> omega
      omega
    · intro pref f hpref hpf
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set w1 := pl.1.foldl stepWire pref
      have hw1_len : w1.length = base + pl.1.length := by
        rw [foldl_stepWire_len, hpref]
      have hw1_r : ∀ i ∈ r.vars, w1.getD i false = f i := by
        intro i hi
        have hilt : i < pref.length := by have := hltr i hi; omega
        rw [foldl_stepWire_getD_lt pl.1 pref hilt]
        exact hpf i (by simp [MTree.vars, hi])
      set w2 := pr.1.foldl stepWire w1
      have hw2_len : w2.length = base + pl.1.length + pr.1.length := by
        rw [foldl_stepWire_len, hw1_len]
      have hw2_wl : w2.getD pl.2 false = l.eval f := by
        rw [foldl_stepWire_getD_lt pr.1 w1 (by omega)]
        exact hevl pref f hpref (fun i hi => hpf i (by simp [MTree.vars, hi]))
      have hw2_wr : w2.getD pr.2 false = r.eval f := hevr w1 f hw1_len hw1_r
      rw [← hw2_len, stepWire_getD_last]
      simp only [List.map_cons, List.map_nil, GateOp.eval, MTree.eval]
      rw [hw2_wl, hw2_wr]
      simp

def setFn {N : ℕ} (S : Finset (Fin N)) (k : ℕ) : Bool :=
  if h : k < N then decide (⟨k, h⟩ ∈ S) else false

lemma getD_ofFn_setFn {N : ℕ} (S : Finset (Fin N)) {k : ℕ} (hk : k < N) :
    (List.ofFn fun i : Fin N => decide (i ∈ S)).getD k false = setFn S k := by
  simp [List.getD_eq_getElem?_getD, hk, setFn]

lemma compile_circuit_spec (N : ℕ) (t : MTree) (hc : t.Clean)
    (hnd : t.vars.Nodup) (hlt : ∀ i ∈ t.vars, i < N) :
    let F : Circuit := ⟨(compileGates N t).1, (compileGates N t).2⟩
    ((∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
     ReadsBack N F ∧
     (F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N)) ∧
     (∀ i < N, readsIn F (Finset.range F.size) i ≤ 1) ∧
     (∀ j < F.size, readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)) ∧
    (∀ i : Fin N, readsIn F (Finset.range F.size) i.val = 1 → i.val ∈ t.vars) ∧
    (∀ S : Finset (Fin N), t.eval (setFn S) = F.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) := by
  rcases compileGates_spec N t hc hlt N le_rfl with ⟨hg, hout, hrb, hr, hev⟩
  set F : Circuit := ⟨(compileGates N t).1, (compileGates N t).2⟩
  have hFg : F.gates = (compileGates N t).1 := rfl
  have hFo : F.output = (compileGates N t).2 := rfl
  rw [← hFg] at hg hout hrb hr hev
  rw [← hFo] at hout hr hev
  refine ⟨⟨hg, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj i hi
    exact hrb j hj i hi
  · rcases hout with ⟨h0, hlt0⟩ | ⟨_, heq⟩
    · exact Or.inr ⟨h0, hlt0⟩
    · exact Or.inl heq
  · intro i hi
    rw [readsIn_range_eq_listReads]
    have hri := hr i
    have hnot : ¬ (N ≤ i ∧ i < N + F.gates.length) := by omega
    simp only [hnot, ↓reduceIte, Nat.add_zero] at hri
    have hcnt : t.vars.count i ≤ 1 := List.nodup_iff_count_le_one.mp hnd i
    omega
  · intro j hj
    rw [readsIn_range_eq_listReads]
    have hrj := hr (N + j)
    have hcnt0 : t.vars.count (N + j) = 0 := by
      rw [List.count_eq_zero]
      intro hm
      have := hlt (N + j) hm
      omega
    have hin : N ≤ N + j ∧ N + j < N + F.gates.length := by
      simp only [Circuit.size] at hj
      omega
    simp only [hcnt0, hin.1, hin.2, and_self, ↓reduceIte, Nat.zero_add] at hrj
    have hout_eq : F.output + 1 = N + F.gates.length := by
      rcases hout with ⟨h0, _⟩ | ⟨_, heq⟩
      · simp only [Circuit.size] at hj; omega
      · exact heq
    have hiff : N + j = F.output ↔ j + 1 = F.size := by
      simp only [Circuit.size]
      omega
    by_cases hlast : j + 1 = F.size
    · have h1 : N + j = F.output := hiff.mpr hlast
      rw [if_pos h1] at hrj
      rw [if_pos hlast]
      omega
    · have h1 : N + j ≠ F.output := fun he => hlast (hiff.mp he)
      simp only [h1, ↓reduceIte, Nat.add_zero] at hrj
      simp only [hlast, ↓reduceIte]
      exact hrj
  · intro i hi
    rw [readsIn_range_eq_listReads] at hi
    have hri := hr i.val
    have hnot : ¬ (N ≤ i.val ∧ i.val < N + F.gates.length) := by omega
    simp only [hnot, ↓reduceIte, Nat.add_zero] at hri
    have hpos : 0 < t.vars.count i.val := by omega
    exact List.count_pos_iff.mp hpos
  · intro S
    unfold Circuit.eval Circuit.wires
    have hlen : (List.ofFn fun k : Fin N => decide (k ∈ S)).length = N := by simp
    exact (hev (List.ofFn fun k : Fin N => decide (k ∈ S)) (setFn S) hlen
      (fun k hk => getD_ofFn_setFn S (hlt k hk))).symm

lemma main_proof :
    ∀ (N : ℕ) (D : Circuit),
      (∀ g ∈ D.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
        (g.op = GateOp.not ∧ g.inputs.length = 1)) →
      ReadsBack N D →
      0 < D.size →
      D.output + 1 = N + D.size →
      (∃ j0 < D.size, ∀ j < D.size, (D.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.not ↔ j = j0) →
      (∀ i < N, readsIn D (Finset.range D.size) i ≤ 1) →
      (∀ j < D.size, readsIn D (Finset.range D.size) (N + j) = if j + 1 = D.size then 0 else 1) →
      ∃ (Nset : Finset (Fin N)) (H α β : Finset (Fin N) → Bool),
        Nset.Nonempty ∧
        H ∅ = false ∧
        (∀ S T : Finset (Fin N), S ⊆ T → H S = true → H T = true) ∧
        (∀ S T : Finset (Fin N), S ⊆ T → α S = true → α T = true) ∧
        (∀ S T : Finset (Fin N), S ⊆ T → β S = true → β T = true) ∧
        (∀ S : Finset (Fin N), β S = true → α S = true) ∧
        (∀ x : Fin N → Bool,
          D.eval (List.ofFn x) =
            (β ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset) ||
              (!H ((Finset.univ.filter (fun i : Fin N => x i = true)) ∩ Nset) &&
                α ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset)))) ∧
        (∃ FH : Circuit,
          ((∀ g ∈ FH.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
            ReadsBack N FH ∧
            (FH.output + 1 = N + FH.size ∨ (FH.size = 0 ∧ FH.output < N)) ∧
            (∀ i < N, readsIn FH (Finset.range FH.size) i ≤ 1) ∧
            (∀ j < FH.size, readsIn FH (Finset.range FH.size) (N + j) = if j + 1 = FH.size then 0 else 1)) ∧
          (∀ i : Fin N, readsIn FH (Finset.range FH.size) i.val = 1 → i ∈ Nset) ∧
          ∀ S : Finset (Fin N), H S = FH.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) ∧
        ((∃ c : Bool, ∀ S : Finset (Fin N), α S = c) ∨
          ∃ Fα : Circuit,
            ((∀ g ∈ Fα.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
              ReadsBack N Fα ∧
              (Fα.output + 1 = N + Fα.size ∨ (Fα.size = 0 ∧ Fα.output < N)) ∧
              (∀ i < N, readsIn Fα (Finset.range Fα.size) i ≤ 1) ∧
              (∀ j < Fα.size, readsIn Fα (Finset.range Fα.size) (N + j) = if j + 1 = Fα.size then 0 else 1)) ∧
            (∀ i : Fin N, readsIn Fα (Finset.range Fα.size) i.val = 1 → i ∉ Nset) ∧
            ∀ S : Finset (Fin N), α S = Fα.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) := by
  intro N D hGates hRB hPos hOut hNot hInRead hGateRead
  rcases hNot with ⟨j0, hj0, hNot⟩
  have hOut_eq : D.output = N + (D.gates.length - 1) := by
    simp only [Circuit.size] at hOut hPos
    omega
  have hOut_lt : D.output < N + D.gates.length := by
    simp only [Circuit.size] at hPos
    omega
  set T := wireTree N D D.output
  have hT_vars_lt : ∀ i ∈ T.vars, i < N := wireTree_vars_lt N D hGates hRB D.output hOut_lt
  have hT_nodup : T.vars.Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro u
    by_cases hu : u < N
    · rw [wireTree_vars_count_eq N D hGates hRB u hu D.output hOut_lt, hOut_eq]
      rw [countWire_output_eq N D hRB hPos hGateRead u]
      have h1 : (∑ j ∈ Finset.range D.gates.length, if N + j = u then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have : N + j ≠ u := by omega
        simp [this]
      have h2 : (∑ i ∈ Finset.range N, readsIn D (Finset.range D.gates.length) i *
          (if i = u then 1 else 0)) = readsIn D (Finset.range D.gates.length) u := by
        rw [Finset.sum_eq_single u]
        · simp
        · intro b _ hbu; simp [hbu]
        · intro hu'; exact False.elim (hu' (Finset.mem_range.mpr hu))
      rw [h1, h2, Nat.zero_add]
      exact hInRead u hu
    · have h0 : T.vars.count u = 0 := by
        rw [List.count_eq_zero]
        intro hm
        exact hu (hT_vars_lt u hm)
      omega
  have hT_not1 : T.notCount = 1 := by
    rw [wireTree_notCount_eq N D hGates hRB j0 hNot D.output hOut_lt, hOut_eq]
    rw [countWire_output_eq N D hRB hPos hGateRead (N + j0)]
    have h1 : (∑ j ∈ Finset.range D.gates.length, if N + j = N + j0 then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hbj; simp [hbj]
      · intro hj0'; exact False.elim (hj0' (Finset.mem_range.mpr hj0))
    have h2 : (∑ i ∈ Finset.range N, readsIn D (Finset.range D.gates.length) i *
        (if i = N + j0 then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : i ≠ N + j0 := by have := Finset.mem_range.mp hi; omega
      simp [hne]
    rw [h1, h2]
  rcases T.splitOne_spec hT_not1 hT_nodup with
    ⟨hcH, hgA, hgB, hsH, hsA, hsB, hdA, hdB, hba, hev⟩
  set tH := T.splitOne.1
  set tα := T.splitOne.2.1
  set tβ := T.splitOne.2.2
  set Nset : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.val ∈ tH.vars)
  set H : Finset (Fin N) → Bool := fun S => tH.eval (setFn S)
  set α : Finset (Fin N) → Bool := fun S => tα.eval (setFn S)
  set β : Finset (Fin N) → Bool := fun S => tβ.eval (setFn S)
  have hltH : ∀ i ∈ tH.vars, i < N := fun i hi => hT_vars_lt i (hsH.subset hi)
  have hltA : ∀ i ∈ tα.vars, i < N := fun i hi => hT_vars_lt i (hsA.subset hi)
  have hltB : ∀ i ∈ tβ.vars, i < N := fun i hi => hT_vars_lt i (hsB.subset hi)
  have hndH : tH.vars.Nodup := sublist_nodup hsH hT_nodup
  have hndA : tα.vars.Nodup := sublist_nodup hsA hT_nodup
  have hsetMono : ∀ {S T : Finset (Fin N)}, S ⊆ T → ∀ k, setFn S k = true → setFn T k = true := by
    intro S T hST k hk
    unfold setFn at hk ⊢
    by_cases h : k < N
    · simp only [h, ↓reduceDIte, decide_eq_true_eq] at hk ⊢
      exact hST hk
    · simp only [h, ↓reduceDIte] at hk
      cases hk
  refine ⟨Nset, H, α, β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hne : tH.vars ≠ [] := MTree.clean_vars_nonempty hcH
    match hv : tH.vars with
    | [] => exact absurd hv hne
    | k :: _ =>
      have hk : k ∈ tH.vars := by rw [hv]; simp
      exact ⟨⟨k, hltH k hk⟩, by simp [Nset, hk]⟩
  · have hfn : setFn (∅ : Finset (Fin N)) = fun _ => false := by
      funext k
      unfold setFn
      split_ifs <;> simp
    simp only [H, hfn]
    exact MTree.clean_eval_false hcH
  · intro S T hST
    exact MTree.eval_mono tH (hsetMono hST)
  · intro S T hST
    exact MTree.eval_mono tα (hsetMono hST)
  · intro S T hST
    exact MTree.eval_mono tβ (hsetMono hST)
  · intro S
    exact hba (setFn S)
  · intro x
    unfold Circuit.eval
    rw [wireTree_eval N D hGates hRB (List.ofFn x) (by simp) D.output hOut_lt]
    rw [hev]
    set supp := Finset.univ.filter (fun i : Fin N => x i = true)
    have hcongrH : tH.eval (fun i => (List.ofFn x).getD i false) = H (supp ∩ Nset) := by
      apply MTree.eval_congr
      intro i hi
      have hilt : i < N := hltH i hi
      simp [List.getD_eq_getElem?_getD, hilt, setFn, supp, Nset, hi]
    have hcongrA : tα.eval (fun i => (List.ofFn x).getD i false) = α (supp \ Nset) := by
      apply MTree.eval_congr
      intro i hi
      have hilt : i < N := hltA i hi
      have hni : i ∉ tH.vars := hdA i hi
      simp [List.getD_eq_getElem?_getD, hilt, setFn, supp, Nset, hni]
    have hcongrB : tβ.eval (fun i => (List.ofFn x).getD i false) = β (supp \ Nset) := by
      apply MTree.eval_congr
      intro i hi
      have hilt : i < N := hltB i hi
      have hni : i ∉ tH.vars := hdB i hi
      simp [List.getD_eq_getElem?_getD, hilt, setFn, supp, Nset, hni]
    rw [hcongrH, hcongrA, hcongrB]
  · rcases compile_circuit_spec N tH hcH hndH hltH with ⟨hFH1, hFH2, hFH3⟩
    refine ⟨⟨(compileGates N tH).1, (compileGates N tH).2⟩, hFH1, ?_, hFH3⟩
    intro i hi
    simp only [Nset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hFH2 i hi
  · rcases hgA with ⟨c, hc⟩ | hcA
    · left
      refine ⟨c, fun S => ?_⟩
      simp [α, hc, MTree.eval]
    · right
      rcases compile_circuit_spec N tα hcA hndA hltA with ⟨hFA1, hFA2, hFA3⟩
      refine ⟨⟨(compileGates N tα).1, (compileGates N tα).2⟩, hFA1, ?_, hFA3⟩
      intro i hi
      simp only [Nset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdA i.val (hFA2 i hi)

end PEqualNP.Outside.L_meta_24159_aux

theorem PEqualNP.Outside.L_meta_24159 : (∀ (N : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack N D → 0 < D.size → D.output + 1 = N + D.size → (∃ j0 < D.size, ∀ j < D.size, (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = j0) → (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) → (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N + j) = if j + 1 = D.size then 0 else 1) → ∃ (Nset : Finset (Fin N)) (H α β : Finset (Fin N) → Bool), Nset.Nonempty ∧ H ∅ = false ∧ (∀ S T : Finset (Fin N), S ⊆ T → H S = true → H T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → α S = true → α T = true) ∧ (∀ S T : Finset (Fin N), S ⊆ T → β S = true → β T = true) ∧ (∀ S : Finset (Fin N), β S = true → α S = true) ∧ (∀ x : Fin N → Bool, D.eval (List.ofFn x) = (β ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset) || (!H ((Finset.univ.filter (fun i : Fin N => x i = true)) ∩ Nset) && α ((Finset.univ.filter (fun i : Fin N => x i = true)) \ Nset)))) ∧ (∃ FH : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ FH.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N FH ∧ (FH.output + 1 = N + FH.size ∨ (FH.size = 0 ∧ FH.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i ≤ 1) ∧ (∀ j < FH.size, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) (N + j) = if j + 1 = FH.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn FH (Finset.range FH.size) i.val = 1 → i ∈ Nset) ∧ ∀ S : Finset (Fin N), H S = FH.eval (List.ofFn fun k : Fin N => decide (k ∈ S))) ∧ ((∃ c : Bool, ∀ S : Finset (Fin N), α S = c) ∨ ∃ Fα : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g ∈ Fα.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N Fα ∧ (Fα.output + 1 = N + Fα.size ∨ (Fα.size = 0 ∧ Fα.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i ≤ 1) ∧ (∀ j < Fα.size, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) (N + j) = if j + 1 = Fα.size then 0 else 1)) ∧ (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn Fα (Finset.range Fα.size) i.val = 1 → i ∉ Nset) ∧ ∀ S : Finset (Fin N), α S = Fα.eval (List.ofFn fun k : Fin N => decide (k ∈ S)))) :=
  PEqualNP.Outside.L_meta_24159_aux.main_proof
