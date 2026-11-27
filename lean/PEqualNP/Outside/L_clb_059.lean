import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_059

open PEqualNP.CircuitLowerBounds

abbrev WMat (w : ℕ) := Fin (2 ^ w) → Fin (2 ^ w) → ℕ
abbrev BMat (w : ℕ) := Fin (2 ^ w) → Fin (2 ^ w) → Bool

def wires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def depths (I : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
    (List.replicate I 0)

def Valid (I : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < I + j)

lemma wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wires]
  | cons g gs ih =>
    simp only [wires, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x =
      wires gs x ++ [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires, List.foldl_append]

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma getD_append_right_zero {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

lemma wires_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs₁.length) :
    (wires (gs₁ ++ gs₂) x).getD i false = (wires gs₁ x).getD i false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc, wires_snoc]
    have hlen : i < (wires (gs₁ ++ gs₂) x).length := by
      rw [wires_length, List.length_append]; omega
    rw [getD_append_left _ _ _ _ hlen, ih]

lemma wires_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wires gs x).getD i false = x.getD i false := by
  have h := wires_prefix [] gs x i (by simpa using hi)
  simpa [wires] using h

lemma wires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wires_snoc, ← wires_length gs x, getD_append_right_zero]

lemma depths_snoc (I : ℕ) (gs : List Gate) (g : Gate) :
    depths I (gs ++ [g]) =
      depths I gs ++ [(g.inputs.map fun i => (depths I gs).getD i 0).foldr max 0 + 1] := by
  simp [depths, List.foldl_append]

lemma depths_length (I : ℕ) (gs : List Gate) :
    (depths I gs).length = I + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depths]
  | append_singleton gs g ih =>
    rw [depths_snoc, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

lemma depths_prefix (I : ℕ) (gs₁ gs₂ : List Gate) (i : ℕ) (hi : i < I + gs₁.length) :
    (depths I (gs₁ ++ gs₂)).getD i 0 = (depths I gs₁).getD i 0 := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc, depths_snoc]
    have hlen : i < (depths I (gs₁ ++ gs₂)).length := by
      rw [depths_length, List.length_append]; omega
    rw [getD_append_left _ _ _ _ hlen, ih]

lemma depths_input (I : ℕ) (gs : List Gate) (i : ℕ) (hi : i < I) :
    (depths I gs).getD i 0 = 0 := by
  have h := depths_prefix I [] gs i (by simpa using hi)
  rw [List.nil_append] at h
  rw [h]
  simp [depths, List.getD, hi]

lemma depths_snoc_last (I : ℕ) (gs : List Gate) (g : Gate) :
    (depths I (gs ++ [g])).getD (I + gs.length) 0 =
      (g.inputs.map fun i => (depths I gs).getD i 0).foldr max 0 + 1 := by
  rw [depths_snoc, ← depths_length I gs, getD_append_right_zero]

lemma valid_nil (I : ℕ) : Valid I [] := by
  refine ⟨by simp, by simp⟩

lemma valid_snoc (I : ℕ) (gs : List Gate) (g : Gate) (hv : Valid I gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < I + gs.length) :
    Valid I (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hv.1 g' hg'
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hv.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right_zero] at hi
      exact hrb i hi

def pushOr0 (I : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, []⟩], I + gs.length)

def pushOr2 (I : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], I + gs.length)

def pushAnd2 (I : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], I + gs.length)

lemma wires_pushOr0 (I : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = I) :
    (wires (pushOr0 I gs).1 x).getD (pushOr0 I gs).2 false = false := by
  unfold pushOr0
  rw [← hx, wires_snoc_last]
  rfl

lemma depths_pushOr0 (I : ℕ) (gs : List Gate) :
    (depths I (pushOr0 I gs).1).getD (pushOr0 I gs).2 0 = 1 := by
  unfold pushOr0
  rw [depths_snoc_last]
  rfl

lemma wires_pushOr2 (I : ℕ) (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = I) :
    (wires (pushOr2 I gs a b).1 x).getD (pushOr2 I gs a b).2 false =
      ((wires gs x).getD a false || (wires gs x).getD b false) := by
  unfold pushOr2
  rw [← hx, wires_snoc_last]
  simp [GateOp.eval]

lemma depths_pushOr2 (I : ℕ) (gs : List Gate) (a b : ℕ) :
    (depths I (pushOr2 I gs a b).1).getD (pushOr2 I gs a b).2 0 =
      max ((depths I gs).getD a 0) ((depths I gs).getD b 0) + 1 := by
  unfold pushOr2
  rw [depths_snoc_last]
  simp

lemma wires_pushAnd2 (I : ℕ) (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = I) :
    (wires (pushAnd2 I gs a b).1 x).getD (pushAnd2 I gs a b).2 false =
      ((wires gs x).getD a false && (wires gs x).getD b false) := by
  unfold pushAnd2
  rw [← hx, wires_snoc_last]
  simp [GateOp.eval]

lemma depths_pushAnd2 (I : ℕ) (gs : List Gate) (a b : ℕ) :
    (depths I (pushAnd2 I gs a b).1).getD (pushAnd2 I gs a b).2 0 =
      max ((depths I gs).getD a 0) ((depths I gs).getD b 0) + 1 := by
  unfold pushAnd2
  rw [depths_snoc_last]
  simp

def orTree (I : ℕ) (gs : List Gate) : (k : ℕ) → (Fin (2 ^ k) → ℕ) → List Gate × ℕ
  | 0, f => (gs, f ⟨0, by simp⟩)
  | k + 1, f =>
    let r1 := orTree I gs k (fun i => f ⟨i.val, by
      have := i.isLt; rw [Nat.pow_succ]; omega⟩)
    let r2 := orTree I r1.1 k (fun i => f ⟨i.val + 2 ^ k, by
      have := i.isLt; rw [Nat.pow_succ]; omega⟩)
    pushOr2 I r2.1 r1.2 r2.2

lemma orTree_prefix (I : ℕ) (k : ℕ) (gs : List Gate) (f : Fin (2 ^ k) → ℕ) :
    ∃ ext, (orTree I gs k f).1 = gs ++ ext ∧ ext.length = 2 ^ k - 1 := by
  induction k generalizing gs with
  | zero =>
    exact ⟨[], by simp [orTree]⟩
  | succ k ih =>
    simp only [orTree]
    set f1 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set f2 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set r1 := orTree I gs k f1
    set r2 := orTree I r1.1 k f2
    obtain ⟨ext1, h1, hl1⟩ := ih gs f1
    obtain ⟨ext2, h2, hl2⟩ := ih r1.1 f2
    refine ⟨ext1 ++ ext2 ++ [⟨GateOp.or, [r1.2, r2.2]⟩], ?_, ?_⟩
    · dsimp only [pushOr2, r2]
      rw [h2]
      dsimp only [r1]
      rw [h1]
      simp [List.append_assoc]
    · simp only [List.length_append, List.length_singleton, hl1, hl2, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

lemma orTree_out_lt (I : ℕ) (k : ℕ) (gs : List Gate) (f : Fin (2 ^ k) → ℕ)
    (hf : ∀ i, f i < I + gs.length) :
    (orTree I gs k f).2 < I + (orTree I gs k f).1.length := by
  cases k with
  | zero => exact hf ⟨0, by simp⟩
  | succ k =>
    simp only [orTree, pushOr2, List.length_append, List.length_singleton]
    omega

lemma orTree_valid (I : ℕ) (k : ℕ) (gs : List Gate) (f : Fin (2 ^ k) → ℕ)
    (hv : Valid I gs) (hf : ∀ i, f i < I + gs.length) :
    Valid I (orTree I gs k f).1 ∧ (orTree I gs k f).2 < I + (orTree I gs k f).1.length := by
  induction k generalizing gs with
  | zero =>
    exact ⟨hv, hf ⟨0, by simp⟩⟩
  | succ k ih =>
    simp only [orTree]
    set f1 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set f2 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set r1 := orTree I gs k f1
    set r2 := orTree I r1.1 k f2
    obtain ⟨hv1, hw1⟩ := ih gs f1 hv (fun i => hf _)
    obtain ⟨ext1, hext1, _⟩ := orTree_prefix I k gs f1
    have hf2 : ∀ i : Fin (2 ^ k), f2 i < I + r1.1.length := by
      intro i
      have h : f2 i < I + gs.length := hf ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      dsimp only [r1]; rw [hext1, List.length_append]; omega
    obtain ⟨hv2, hw2⟩ := ih r1.1 f2 hv1 hf2
    obtain ⟨ext2, hext2, _⟩ := orTree_prefix I k r1.1 f2
    have hw1' : r1.2 < I + r2.1.length := by
      dsimp only [r2]; rw [hext2, List.length_append]; dsimp only [r1]; omega
    refine ⟨valid_snoc I _ _ hv2 (by simp) (by simp) ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hw1'
      · exact hw2
    · simp only [pushOr2, List.length_append, List.length_singleton]; omega

lemma orTree_depth (I : ℕ) (k : ℕ) (gs : List Gate) (f : Fin (2 ^ k) → ℕ) (D : ℕ)
    (hf : ∀ i, f i < I + gs.length)
    (hd : ∀ i, (depths I gs).getD (f i) 0 ≤ D) :
    (depths I (orTree I gs k f).1).getD (orTree I gs k f).2 0 ≤ D + k := by
  induction k generalizing gs with
  | zero =>
    simpa [orTree] using hd ⟨0, by simp⟩
  | succ k ih =>
    simp only [orTree]
    set f1 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set f2 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set r1 := orTree I gs k f1
    set r2 := orTree I r1.1 k f2
    have hd1 : (depths I r1.1).getD r1.2 0 ≤ D + k := ih gs f1 (fun i => hf _) (fun i => hd _)
    obtain ⟨ext1, hext1, _⟩ := orTree_prefix I k gs f1
    have hf2 : ∀ i, f2 i < I + r1.1.length := by
      intro i
      have h : f2 i < I + gs.length := hf ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      dsimp only [r1]; rw [hext1, List.length_append]; omega
    have hd2_in : ∀ i, (depths I r1.1).getD (f2 i) 0 ≤ D := by
      intro i
      dsimp only [r1]
      rw [hext1, depths_prefix I gs ext1 (f2 i) (hf _)]
      exact hd _
    have hd2 : (depths I r2.1).getD r2.2 0 ≤ D + k := ih r1.1 f2 hf2 hd2_in
    obtain ⟨ext2, hext2, _⟩ := orTree_prefix I k r1.1 f2
    have hvalid1 : r1.2 < I + r1.1.length := orTree_out_lt I k gs f1 (fun i => hf _)
    have hd1' : (depths I r2.1).getD r1.2 0 ≤ D + k := by
      rw [hext2, depths_prefix I r1.1 ext2 r1.2 hvalid1]
      exact hd1
    rw [depths_pushOr2]
    omega

lemma orTree_eval (I : ℕ) (k : ℕ) (gs : List Gate) (f : Fin (2 ^ k) → ℕ)
    (x : List Bool) (hx : x.length = I) (hf : ∀ i, f i < I + gs.length) :
    (wires (orTree I gs k f).1 x).getD (orTree I gs k f).2 false = true ↔
      ∃ i : Fin (2 ^ k), (wires gs x).getD (f i) false = true := by
  induction k generalizing gs with
  | zero =>
    simp only [orTree]
    constructor
    · intro h; exact ⟨⟨0, by simp⟩, h⟩
    · rintro ⟨i, hi⟩
      have : i = ⟨0, by simp⟩ := Fin.ext (by omega)
      rwa [this] at hi
  | succ k ih =>
    simp only [orTree]
    set f1 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set f2 : Fin (2 ^ k) → ℕ := fun i => f ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set r1 := orTree I gs k f1
    set r2 := orTree I r1.1 k f2
    obtain ⟨ext1, hext1, _⟩ := orTree_prefix I k gs f1
    obtain ⟨ext2, hext2, _⟩ := orTree_prefix I k r1.1 f2
    have hvalid1 : r1.2 < I + r1.1.length := orTree_out_lt I k gs f1 (fun i => hf _)
    have hf2 : ∀ i, f2 i < I + r1.1.length := by
      intro i
      have h : f2 i < I + gs.length := hf ⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      dsimp only [r1]; rw [hext1, List.length_append]; omega
    rw [wires_pushOr2 I r2.1 r1.2 r2.2 x hx, Bool.or_eq_true]
    rw [hext2, wires_prefix r1.1 ext2 x r1.2 (by rw [hx]; exact hvalid1)]
    have hev1 : (wires r1.1 x).getD r1.2 false = true ↔
        ∃ i : Fin (2 ^ k), (wires gs x).getD (f1 i) false = true :=
      ih gs f1 (fun i => hf _)
    have hev2 : (wires r2.1 x).getD r2.2 false = true ↔
        ∃ i : Fin (2 ^ k), (wires r1.1 x).getD (f2 i) false = true :=
      ih r1.1 f2 hf2
    rw [hev1, ← hext2, hev2]
    have hpref2 : ∀ i : Fin (2 ^ k), (wires r1.1 x).getD (f2 i) false = (wires gs x).getD (f2 i) false := by
      intro i
      dsimp only [r1]
      rw [hext1, wires_prefix gs ext1 x (f2 i) (by rw [hx]; exact hf _)]
    simp only [hpref2]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩, hi⟩
      · exact ⟨⟨i.val + 2 ^ k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩, hi⟩
    · rintro ⟨i, hi⟩
      by_cases hlt : i.val < 2 ^ k
      · left; exact ⟨⟨i.val, hlt⟩, hi⟩
      · right
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
        have hi_lt : i.val < 2 ^ (k + 1) := i.isLt
        have hlt2 : i.val - 2 ^ k < 2 ^ k := by omega
        refine ⟨⟨i.val - 2 ^ k, hlt2⟩, ?_⟩
        have heq : (⟨i.val - 2 ^ k + 2 ^ k, by omega⟩ : Fin (2 ^ (k + 1))) = i :=
          Fin.ext (by dsimp; omega)
        simpa [f2, heq] using hi

def buildFnAux (step : List Gate → ℕ → List Gate × ℕ) : ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, fun _ => 0)
  | m + 1, gs =>
    let r := buildFnAux step m gs
    let r' := step r.1 m
    (r'.1, fun i => if i = m then r'.2 else r.2 i)

lemma buildFnAux_spec (I : ℕ) (step : List Gate → ℕ → List Gate × ℕ) (m : ℕ) (c D : ℕ)
    (P : ℕ → List Bool → Bool) (gs : List Gate) (x : List Bool) (hx : x.length = I)
    (hv : Valid I gs)
    (hstep : ∀ k < m, ∀ gs0, Valid I gs0 → (∃ ext, gs0 = gs ++ ext) →
      (∃ ext, (step gs0 k).1 = gs0 ++ ext ∧ ext.length ≤ c) ∧
      Valid I (step gs0 k).1 ∧
      (step gs0 k).2 < I + (step gs0 k).1.length ∧
      (depths I (step gs0 k).1).getD (step gs0 k).2 0 ≤ D ∧
      (wires (step gs0 k).1 x).getD (step gs0 k).2 false = P k x) :
    (∃ ext, (buildFnAux step m gs).1 = gs ++ ext ∧ ext.length ≤ m * c) ∧
    Valid I (buildFnAux step m gs).1 ∧
    ∀ i < m,
      (buildFnAux step m gs).2 i < I + (buildFnAux step m gs).1.length ∧
      (depths I (buildFnAux step m gs).1).getD ((buildFnAux step m gs).2 i) 0 ≤ D ∧
      (wires (buildFnAux step m gs).1 x).getD ((buildFnAux step m gs).2 i) false = P i x := by
  induction m with
  | zero =>
    exact ⟨⟨[], by simp [buildFnAux]⟩, hv, by intro i hi; omega⟩
  | succ m ih =>
    have hstep' : ∀ k < m, ∀ gs0, Valid I gs0 → (∃ ext, gs0 = gs ++ ext) →
        (∃ ext, (step gs0 k).1 = gs0 ++ ext ∧ ext.length ≤ c) ∧
        Valid I (step gs0 k).1 ∧
        (step gs0 k).2 < I + (step gs0 k).1.length ∧
        (depths I (step gs0 k).1).getD (step gs0 k).2 0 ≤ D ∧
        (wires (step gs0 k).1 x).getD (step gs0 k).2 false = P k x :=
      fun k hk => hstep k (by omega)
    obtain ⟨⟨ext1, hext1, hlen1⟩, hv1, hall1⟩ := ih hstep'
    set r := buildFnAux step m gs
    obtain ⟨⟨ext2, hext2, hlen2⟩, hv2, hw2, hd2, hev2⟩ := hstep m (by omega) r.1 hv1 ⟨ext1, hext1⟩
    simp only [buildFnAux]
    refine ⟨⟨ext1 ++ ext2, ?_, ?_⟩, hv2, ?_⟩
    · rw [hext2, hext1, List.append_assoc]
    · rw [List.length_append, Nat.succ_mul]
      exact Nat.add_le_add hlen1 hlen2
    · intro i hi
      by_cases him : i = m
      · subst him
        simp only [ite_true]
        exact ⟨hw2, hd2, hev2⟩
      · simp only [him, ite_false]
        obtain ⟨hwi, hdi, hevi⟩ := hall1 i (by omega)
        refine ⟨?_, ?_, ?_⟩
        · change r.2 i < I + (step r.1 m).1.length
          rw [hext2, List.length_append]; omega
        · rw [hext2, depths_prefix I r.1 ext2 (r.2 i) hwi]; exact hdi
        · rw [hext2, wires_prefix r.1 ext2 x (r.2 i) (by rw [hx]; exact hwi)]; exact hevi

def matMulEntry (I w : ℕ) (gs : List Gate) (A B : WMat w) (u v : Fin (2 ^ w)) : List Gate × ℕ :=
  let r := buildFnAux (fun gs0 k =>
    if hk : k < 2 ^ w then pushAnd2 I gs0 (A u ⟨k, hk⟩) (B ⟨k, hk⟩ v) else (gs0, 0)) (2 ^ w) gs
  orTree I r.1 w (fun k => r.2 k.val)

def matMul (I w : ℕ) (gs : List Gate) (A B : WMat w) : List Gate × WMat w :=
  let r := buildFnAux (fun gs0 idx =>
    if hidx : idx < 2 ^ w * 2 ^ w then
      have hu : idx / 2 ^ w < 2 ^ w := Nat.div_lt_of_lt_mul hidx
      have hv : idx % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
      matMulEntry I w gs0 A B ⟨idx / 2 ^ w, hu⟩ ⟨idx % 2 ^ w, hv⟩
    else (gs0, 0)) (2 ^ w * 2 ^ w) gs
  (r.1, fun u v => r.2 (u.val * 2 ^ w + v.val))

def bMul {w : ℕ} (A B : BMat w) : BMat w :=
  fun u v => decide (∃ k : Fin (2 ^ w), A u k = true ∧ B k v = true)

lemma matMulEntry_spec (I w : ℕ) (gs : List Gate) (A B : WMat w) (u v : Fin (2 ^ w))
    (D : ℕ) (x : List Bool) (hx : x.length = I) (hv : Valid I gs)
    (hA : ∀ a b, A a b < I + gs.length ∧ (depths I gs).getD (A a b) 0 ≤ D)
    (hB : ∀ a b, B a b < I + gs.length ∧ (depths I gs).getD (B a b) 0 ≤ D) :
    (∃ ext, (matMulEntry I w gs A B u v).1 = gs ++ ext ∧ ext.length ≤ 2 * 2 ^ w - 1) ∧
    Valid I (matMulEntry I w gs A B u v).1 ∧
    (matMulEntry I w gs A B u v).2 < I + (matMulEntry I w gs A B u v).1.length ∧
    (depths I (matMulEntry I w gs A B u v).1).getD (matMulEntry I w gs A B u v).2 0 ≤ D + (w + 1) ∧
    ((wires (matMulEntry I w gs A B u v).1 x).getD (matMulEntry I w gs A B u v).2 false = true ↔
      ∃ k : Fin (2 ^ w),
        (wires gs x).getD (A u k) false = true ∧ (wires gs x).getD (B k v) false = true) := by
  unfold matMulEntry
  set step : List Gate → ℕ → List Gate × ℕ := fun gs0 k =>
    if hk : k < 2 ^ w then pushAnd2 I gs0 (A u ⟨k, hk⟩) (B ⟨k, hk⟩ v) else (gs0, 0)
  set P : ℕ → List Bool → Bool := fun k y =>
    if hk : k < 2 ^ w then
      (wires gs y).getD (A u ⟨k, hk⟩) false && (wires gs y).getD (B ⟨k, hk⟩ v) false
    else false
  obtain ⟨⟨ext1, hext1, hlen1⟩, hv1, hall1⟩ :=
    buildFnAux_spec I step (2 ^ w) 1 (D + 1) P gs x hx hv (by
      intro k hk gs0 hv0 ⟨ext0, hext0⟩
      simp only [step, P, dif_pos hk]
      have hAu : A u ⟨k, hk⟩ < I + gs0.length := by
        rw [hext0, List.length_append]; have := (hA u ⟨k, hk⟩).1; omega
      have hBv : B ⟨k, hk⟩ v < I + gs0.length := by
        rw [hext0, List.length_append]; have := (hB ⟨k, hk⟩ v).1; omega
      refine ⟨⟨[⟨GateOp.and, [A u ⟨k, hk⟩, B ⟨k, hk⟩ v]⟩], rfl, by simp⟩, ?_, ?_, ?_, ?_⟩
      · exact valid_snoc I gs0 _ hv0 (by simp) (by simp) (by
          intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> assumption)
      · simp only [pushAnd2, List.length_append, List.length_singleton]; omega
      · rw [depths_pushAnd2, hext0,
          depths_prefix I gs ext0 (A u ⟨k, hk⟩) (hA u ⟨k, hk⟩).1,
          depths_prefix I gs ext0 (B ⟨k, hk⟩ v) (hB ⟨k, hk⟩ v).1]
        have := (hA u ⟨k, hk⟩).2; have := (hB ⟨k, hk⟩ v).2; omega
      · rw [wires_pushAnd2 I gs0 _ _ x hx, hext0,
          wires_prefix gs ext0 x (A u ⟨k, hk⟩) (by rw [hx]; exact (hA u ⟨k, hk⟩).1),
          wires_prefix gs ext0 x (B ⟨k, hk⟩ v) (by rw [hx]; exact (hB ⟨k, hk⟩ v).1)])
  set r := buildFnAux step (2 ^ w) gs
  obtain ⟨ext2, hext2, hlen2⟩ := orTree_prefix I w r.1 (fun k => r.2 k.val)
  obtain ⟨hv2, hw2⟩ := orTree_valid I w r.1 (fun k => r.2 k.val) hv1 (fun k => (hall1 k.val k.isLt).1)
  have hd2 := orTree_depth I w r.1 (fun k => r.2 k.val) (D + 1)
    (fun k => (hall1 k.val k.isLt).1) (fun k => (hall1 k.val k.isLt).2.1)
  have hev2 := orTree_eval I w r.1 (fun k => r.2 k.val) x hx (fun k => (hall1 k.val k.isLt).1)
  refine ⟨⟨ext1 ++ ext2, ?_, ?_⟩, hv2, hw2, ?_, ?_⟩
  · rw [hext2, hext1, List.append_assoc]
  · rw [List.length_append, hlen2]
    simp only [mul_one] at hlen1
    have hp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega
  · dsimp only
    omega
  · rw [hev2]
    refine exists_congr (fun k => ?_)
    rw [(hall1 k.val k.isLt).2.2]
    simp [P, k.isLt]

lemma matMul_spec (I w : ℕ) (gs : List Gate) (A B : WMat w) (D : ℕ)
    (x : List Bool) (hx : x.length = I) (hv : Valid I gs)
    (hA : ∀ a b, A a b < I + gs.length ∧ (depths I gs).getD (A a b) 0 ≤ D)
    (hB : ∀ a b, B a b < I + gs.length ∧ (depths I gs).getD (B a b) 0 ≤ D) :
    (∃ ext, (matMul I w gs A B).1 = gs ++ ext ∧ ext.length ≤ 2 * 8 ^ w) ∧
    Valid I (matMul I w gs A B).1 ∧
    (∀ u v, (matMul I w gs A B).2 u v < I + (matMul I w gs A B).1.length ∧
      (depths I (matMul I w gs A B).1).getD ((matMul I w gs A B).2 u v) 0 ≤ D + (w + 1)) ∧
    (∀ u v, (wires (matMul I w gs A B).1 x).getD ((matMul I w gs A B).2 u v) false =
      bMul (fun a b => (wires gs x).getD (A a b) false)
           (fun a b => (wires gs x).getD (B a b) false) u v) := by
  unfold matMul
  set step : List Gate → ℕ → List Gate × ℕ := fun gs0 idx =>
    if hidx : idx < 2 ^ w * 2 ^ w then
      have hu : idx / 2 ^ w < 2 ^ w := Nat.div_lt_of_lt_mul hidx
      have hv' : idx % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
      matMulEntry I w gs0 A B ⟨idx / 2 ^ w, hu⟩ ⟨idx % 2 ^ w, hv'⟩
    else (gs0, 0)
  set P : ℕ → List Bool → Bool := fun idx y =>
    if hidx : idx < 2 ^ w * 2 ^ w then
      have hu : idx / 2 ^ w < 2 ^ w := Nat.div_lt_of_lt_mul hidx
      have hv' : idx % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
      bMul (fun a b => (wires gs y).getD (A a b) false)
           (fun a b => (wires gs y).getD (B a b) false) ⟨idx / 2 ^ w, hu⟩ ⟨idx % 2 ^ w, hv'⟩
    else false
  obtain ⟨⟨ext, hext, hlen⟩, hv1, hall1⟩ :=
    buildFnAux_spec I step (2 ^ w * 2 ^ w) (2 * 2 ^ w - 1) (D + (w + 1)) P gs x hx hv (by
      intro idx hidx gs0 hv0 ⟨ext0, hext0⟩
      simp only [step, P, dif_pos hidx]
      have hA0 : ∀ a b, A a b < I + gs0.length ∧ (depths I gs0).getD (A a b) 0 ≤ D := by
        intro a b
        refine ⟨by rw [hext0, List.length_append]; have := (hA a b).1; omega, ?_⟩
        rw [hext0, depths_prefix I gs ext0 (A a b) (hA a b).1]
        exact (hA a b).2
      have hB0 : ∀ a b, B a b < I + gs0.length ∧ (depths I gs0).getD (B a b) 0 ≤ D := by
        intro a b
        refine ⟨by rw [hext0, List.length_append]; have := (hB a b).1; omega, ?_⟩
        rw [hext0, depths_prefix I gs ext0 (B a b) (hB a b).1]
        exact (hB a b).2
      obtain ⟨h1, h2, h3, h4, h5⟩ := matMulEntry_spec I w gs0 A B
        ⟨idx / 2 ^ w, Nat.div_lt_of_lt_mul hidx⟩
        ⟨idx % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩ D x hx hv0 hA0 hB0
      refine ⟨h1, h2, h3, h4, ?_⟩
      apply Bool.eq_iff_iff.mpr
      rw [h5]
      simp only [bMul, decide_eq_true_eq]
      refine exists_congr (fun k => ?_)
      rw [hext0,
        wires_prefix gs ext0 x (A _ k) (by rw [hx]; exact (hA _ k).1),
        wires_prefix gs ext0 x (B k _) (by rw [hx]; exact (hB k _).1)])
  refine ⟨⟨ext, hext, ?_⟩, hv1, ?_, ?_⟩
  · have h8 : 2 ^ w * 2 ^ w * (2 * 2 ^ w) = 2 * 8 ^ w := by
      have : (8 : ℕ) ^ w = 2 ^ w * 2 ^ w * 2 ^ w := by
        rw [show (8 : ℕ) = 2 * 2 * 2 by rfl, mul_pow, mul_pow]
      linarith
    calc ext.length ≤ 2 ^ w * 2 ^ w * (2 * 2 ^ w - 1) := hlen
      _ ≤ 2 ^ w * 2 ^ w * (2 * 2 ^ w) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * 8 ^ w := h8
  · intro u v
    have hidx : u.val * 2 ^ w + v.val < 2 ^ w * 2 ^ w := by
      have hu := u.isLt; have hv' := v.isLt
      nlinarith
    exact ⟨(hall1 _ hidx).1, (hall1 _ hidx).2.1⟩
  · intro u v
    have hidx : u.val * 2 ^ w + v.val < 2 ^ w * 2 ^ w := by
      have hu := u.isLt; have hv' := v.isLt
      nlinarith
    rw [(hall1 _ hidx).2.2]
    simp only [P, dif_pos hidx]
    have hdiv : (u.val * 2 ^ w + v.val) / 2 ^ w = u.val := by
      rw [Nat.mul_comm u.val (2 ^ w), Nat.mul_add_div (Nat.two_pow_pos w),
        Nat.div_eq_of_lt v.isLt, Nat.add_zero]
    have hmod : (u.val * 2 ^ w + v.val) % 2 ^ w = v.val := by
      rw [Nat.mul_comm u.val (2 ^ w), Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt]
    congr 1 <;> apply Fin.ext <;> simp [hdiv, hmod]

def bId (w : ℕ) : BMat w := fun u v => decide (u = v)

def bProd {w : ℕ} : List (BMat w) → BMat w
  | [] => bId w
  | A :: L => bMul A (bProd L)

lemma bMul_assoc {w : ℕ} (A B C : BMat w) : bMul (bMul A B) C = bMul A (bMul B C) := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  simp only [bMul, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨j, huj, hjk⟩, hkv⟩
    exact ⟨j, huj, k, hjk, hkv⟩
  · rintro ⟨j, huj, k, hjk, hkv⟩
    exact ⟨k, ⟨j, huj, hjk⟩, hkv⟩

lemma bMul_bId_right {w : ℕ} (A : BMat w) : bMul A (bId w) = A := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  simp only [bMul, bId, decide_eq_true_eq]
  constructor
  · rintro ⟨k, huk, rfl⟩; exact huk
  · intro huv; exact ⟨v, huv, rfl⟩

lemma bProd_append {w : ℕ} (L₁ L₂ : List (BMat w)) :
    bProd (L₁ ++ L₂) = bMul (bProd L₁) (bProd L₂) := by
  induction L₁ with
  | nil =>
    funext u v
    apply Bool.eq_iff_iff.mpr
    simp only [List.nil_append, bProd, bMul, bId, decide_eq_true_eq]
    constructor
    · intro h; exact ⟨u, rfl, h⟩
    · rintro ⟨k, rfl, h⟩; exact h
  | cons A L₁ ih =>
    simp only [List.cons_append, bProd, ih, bMul_assoc]

def mulTree (I w : ℕ) : ℕ → List Gate → List (WMat w) → List Gate × WMat w
  | _, gs, [] => (gs, fun _ _ => 0)
  | 0, gs, A :: _ => (gs, A)
  | h + 1, gs, L =>
    if L.length ≤ 1 then
      (gs, L.headD (fun _ _ => 0))
    else
      let mid := L.length / 2
      let r1 := mulTree I w h gs (L.take mid)
      let r2 := mulTree I w h r1.1 (L.drop mid)
      matMul I w r2.1 r1.2 r2.2

lemma mulTree_spec (I w : ℕ) (h : ℕ) :
    ∀ (gs : List Gate) (L : List (WMat w)) (D : ℕ) (x : List Bool),
      x.length = I → Valid I gs → 1 ≤ L.length → L.length ≤ 2 ^ h →
      (∀ M ∈ L, ∀ u v, M u v < I + gs.length ∧ (depths I gs).getD (M u v) 0 ≤ D) →
      (∃ ext, (mulTree I w h gs L).1 = gs ++ ext ∧ ext.length ≤ (L.length - 1) * (2 * 8 ^ w)) ∧
      Valid I (mulTree I w h gs L).1 ∧
      (∀ u v, (mulTree I w h gs L).2 u v < I + (mulTree I w h gs L).1.length ∧
        (depths I (mulTree I w h gs L).1).getD ((mulTree I w h gs L).2 u v) 0 ≤ D + h * (w + 1)) ∧
      (fun u v => (wires (mulTree I w h gs L).1 x).getD ((mulTree I w h gs L).2 u v) false) =
        bProd (L.map fun M u v => (wires gs x).getD (M u v) false) := by
  induction h with
  | zero =>
    intro gs L D x hx hv hL1 hL2 hM
    cases L with
    | nil => simp at hL1
    | cons A L' =>
      have hL' : L' = [] := by
        simp only [List.length_cons, pow_zero] at hL2
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hL'
      simp only [mulTree, List.length_singleton, Nat.sub_self, zero_mul, Nat.add_zero]
      refine ⟨⟨[], by simp⟩, hv, hM A (by simp), ?_⟩
      change (fun u v => (wires gs x).getD (A u v) false) =
        bMul (fun u v => (wires gs x).getD (A u v) false) (bId w)
      exact (bMul_bId_right _).symm
  | succ h ih =>
    intro gs L D x hx hv hL1 hL2 hM
    have hmul : mulTree I w (h + 1) gs L =
        if L.length ≤ 1 then (gs, L.headD (fun _ _ => 0))
        else
          let mid := L.length / 2
          let r1 := mulTree I w h gs (L.take mid)
          let r2 := mulTree I w h r1.1 (L.drop mid)
          matMul I w r2.1 r1.2 r2.2 := by
      cases L with
      | nil => simp at hL1
      | cons _ _ => rfl
    rw [hmul]
    by_cases hle1 : L.length ≤ 1
    · rw [if_pos hle1]
      cases L with
      | nil => simp at hL1
      | cons A L' =>
        have hL' : L' = [] := by
          simp only [List.length_cons] at hle1
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hL'
        simp only [List.headD_cons, List.length_singleton, Nat.sub_self, zero_mul]
        refine ⟨⟨[], by simp⟩, hv, ?_, ?_⟩
        · intro u v
          exact ⟨(hM A (by simp) u v).1, le_trans (hM A (by simp) u v).2 (Nat.le_add_right _ _)⟩
        · change (fun u v => (wires gs x).getD (A u v) false) =
            bMul (fun u v => (wires gs x).getD (A u v) false) (bId w)
          exact (bMul_bId_right _).symm
    · rw [if_neg hle1]
      set mid := L.length / 2
      set L1 := L.take mid
      set L2 := L.drop mid
      have hL1_len : L1.length = mid := by
        simp only [L1, List.length_take]; omega
      have hL2_len : L2.length = L.length - mid := by
        simp only [L2, List.length_drop]
      have h1_ge : 1 ≤ L1.length := by omega
      have h2_ge : 1 ≤ L2.length := by omega
      have h1_le : L1.length ≤ 2 ^ h := by rw [Nat.pow_succ] at hL2; omega
      have h2_le : L2.length ≤ 2 ^ h := by rw [Nat.pow_succ] at hL2; omega
      have hM1 : ∀ M ∈ L1, ∀ u v, M u v < I + gs.length ∧ (depths I gs).getD (M u v) 0 ≤ D :=
        fun M hmem => hM M (List.mem_of_mem_take hmem)
      obtain ⟨⟨ext1, hext1, hlen1⟩, hv1, hwd1, hev1⟩ :=
        ih gs L1 D x hx hv h1_ge h1_le hM1
      set r1 := mulTree I w h gs L1
      have hM2 : ∀ M ∈ L2, ∀ u v, M u v < I + r1.1.length ∧ (depths I r1.1).getD (M u v) 0 ≤ D := by
        intro M hmem u v
        have hMm := hM M (List.mem_of_mem_drop hmem) u v
        refine ⟨by rw [hext1, List.length_append]; omega, ?_⟩
        rw [hext1, depths_prefix I gs ext1 (M u v) hMm.1]
        exact hMm.2
      obtain ⟨⟨ext2, hext2, hlen2⟩, hv2, hwd2, hev2⟩ :=
        ih r1.1 L2 D x hx hv1 h2_ge h2_le hM2
      set r2 := mulTree I w h r1.1 L2
      have hA : ∀ u v, r1.2 u v < I + r2.1.length ∧ (depths I r2.1).getD (r1.2 u v) 0 ≤ D + h * (w + 1) := by
        intro u v
        refine ⟨by rw [hext2, List.length_append]; have := (hwd1 u v).1; omega, ?_⟩
        rw [hext2, depths_prefix I r1.1 ext2 (r1.2 u v) (hwd1 u v).1]
        exact (hwd1 u v).2
      obtain ⟨⟨ext3, hext3, hlen3⟩, hv3, hwd3, hev3⟩ :=
        matMul_spec I w r2.1 r1.2 r2.2 (D + h * (w + 1)) x hx hv2 hA hwd2
      refine ⟨⟨ext1 ++ ext2 ++ ext3, ?_, ?_⟩, hv3, ?_, ?_⟩
      · dsimp only
        rw [hext3, hext2, hext1]
        simp [List.append_assoc]
      · simp only [List.length_append]
        have hsum : (L1.length - 1) + (L2.length - 1) + 1 = L.length - 1 := by omega
        calc ext1.length + ext2.length + ext3.length
            ≤ (L1.length - 1) * (2 * 8 ^ w) + (L2.length - 1) * (2 * 8 ^ w) + 2 * 8 ^ w := by omega
          _ = ((L1.length - 1) + (L2.length - 1) + 1) * (2 * 8 ^ w) := by ring
          _ = (L.length - 1) * (2 * 8 ^ w) := by rw [hsum]
      · intro u v
        refine ⟨(hwd3 u v).1, ?_⟩
        calc (depths I (matMul I w r2.1 r1.2 r2.2).1).getD ((matMul I w r2.1 r1.2 r2.2).2 u v) 0
            ≤ D + h * (w + 1) + (w + 1) := (hwd3 u v).2
          _ = D + (h + 1) * (w + 1) := by ring
      · funext u v
        rw [hev3 u v]
        have hAev : (fun a b => (wires r2.1 x).getD (r1.2 a b) false) =
            bProd (L1.map fun M a b => (wires gs x).getD (M a b) false) := by
          funext a b
          rw [hext2, wires_prefix r1.1 ext2 x (r1.2 a b) (by rw [hx]; exact (hwd1 a b).1)]
          exact congrFun (congrFun hev1 a) b
        have hBev : (fun a b => (wires r2.1 x).getD (r2.2 a b) false) =
            bProd (L2.map fun M a b => (wires gs x).getD (M a b) false) := by
          rw [hev2]
          congr 1
          apply List.map_congr_left
          intro M hmem
          funext a b
          rw [hext1, wires_prefix gs ext1 x (M a b) (by rw [hx]; exact (hM M (List.mem_of_mem_drop hmem) a b).1)]
        rw [hAev, hBev, ← bProd_append, ← List.map_append, List.take_append_drop]

lemma testBit_add_two_pow_lt (x w k : ℕ) (hk : k < w) :
    (x + 2 ^ w).testBit k = x.testBit k := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.add_div_of_dvd_left hdvd]
  have hdiv : 2 ^ w / 2 ^ k = 2 * 2 ^ (w - k - 1) := by
    have hwk : w - k = (w - k - 1) + 1 := by omega
    rw [Nat.pow_div (by omega) (by norm_num), hwk, Nat.pow_succ, Nat.mul_comm]
    simp
  rw [hdiv, Nat.add_mul_mod_self_left]

lemma testBit_add_two_pow_eq (x w : ℕ) (hx : x < 2 ^ w) :
    (x + 2 ^ w).testBit w = true := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.add_div_right _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx]
  simp

def toBits (w : ℕ) (u : Fin (2 ^ w)) : Fin w → Bool :=
  fun j => u.val.testBit j.val

def ofBits : (w : ℕ) → (Fin w → Bool) → Fin (2 ^ w)
  | 0, _ => ⟨0, by simp⟩
  | w + 1, f =>
    let lo := ofBits w (fun j => f ⟨j.val, by omega⟩)
    ⟨lo.val + if f ⟨w, by omega⟩ then 2 ^ w else 0, by
      have := lo.isLt; rw [Nat.pow_succ]; split_ifs <;> omega⟩

lemma testBit_ofBits (w : ℕ) (f : Fin w → Bool) (j : Fin w) :
    (ofBits w f).val.testBit j.val = f j := by
  induction w with
  | zero => exact Fin.elim0 j
  | succ w ih =>
    simp only [ofBits]
    set lo := ofBits w (fun k => f ⟨k.val, by omega⟩)
    have hlo : lo.val < 2 ^ w := lo.isLt
    by_cases hj : j.val < w
    · cases hb : f ⟨w, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact ih (fun k => f ⟨k.val, by omega⟩) ⟨j.val, hj⟩
      · simp only [↓reduceIte]
        rw [testBit_add_two_pow_lt lo.val w j.val hj]
        exact ih (fun k => f ⟨k.val, by omega⟩) ⟨j.val, hj⟩
    · have hjeq : j.val = w := by omega
      have hfj : f j = f ⟨w, by omega⟩ := congrArg f (Fin.ext hjeq)
      rw [hjeq, hfj]
      cases hb : f ⟨w, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlo
      · simp only [↓reduceIte]
        exact testBit_add_two_pow_eq lo.val w hlo

lemma toBits_ofBits (w : ℕ) (f : Fin w → Bool) : toBits w (ofBits w f) = f := by
  funext j
  exact testBit_ofBits w f j

lemma ofBits_toBits (w : ℕ) (u : Fin (2 ^ w)) : ofBits w (toBits w u) = u := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < w
  · exact testBit_ofBits w (toBits w u) ⟨k, hk⟩
  · have h1 : (ofBits w (toBits w u)).val < 2 ^ k :=
      lt_of_lt_of_le (ofBits w (toBits w u)).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : u.val < 2 ^ k :=
      lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

lemma toBits_inj (w : ℕ) {u v : Fin (2 ^ w)} (h : toBits w u = toBits w v) : u = v := by
  have := congrArg (ofBits w) h
  rwa [ofBits_toBits, ofBits_toBits] at this

lemma flatten_ofFn_length {α : Type*} (n m : ℕ) (f : Fin n → Fin m → α) :
    ((List.ofFn fun a : Fin n => List.ofFn fun b : Fin m => f a b).flatten).length = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      ih (fun a => f a.succ)]
    ring

lemma flatten_ofFn_getD {α : Type*} (n m : ℕ) (f : Fin n → Fin m → α) (d : α)
    (i : Fin n) (p : Fin m) :
    ((List.ofFn fun a : Fin n => List.ofFn fun b : Fin m => f a b).flatten).getD
      (i.val * m + p.val) d = f i p := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [getD_append_left _ _ _ _ (by rw [List.length_ofFn]; exact p.isLt)]
      simp [List.getD, p.isLt]
    · intro i'
      simp only [Fin.val_succ]
      have hge : (List.ofFn fun b : Fin m => f 0 b).length ≤ (i'.val + 1) * m + p.val := by
        rw [List.length_ofFn]; nlinarith
      rw [getD_append_right _ _ _ _ hge, List.length_ofFn]
      have hsub : (i'.val + 1) * m + p.val - m = i'.val * m + p.val := by
        rw [Nat.add_mul, one_mul]; omega
      rw [hsub]
      exact ih (fun a => f a.succ) i'

def buildBase (n w : ℕ) : List Gate × List (WMat w) :=
  let I := n * 2 ^ (w + 1)
  let r0 := pushOr0 I []
  match w with
  | 0 =>
    let r := buildFnAux (fun gs0 i => pushOr2 I gs0 (i * 2) (i * 2 + 1)) n r0.1
    (r.1, List.ofFn fun i : Fin n => fun _ _ => r.2 i.val)
  | w' + 1 =>
    (r0.1, List.ofFn fun i : Fin n => fun u v =>
      let b := v.val.testBit w'
      let p := u.val + if b then 2 ^ (w' + 1) else 0
      if p / 2 = v.val then i.val * 2 ^ (w' + 2) + p else r0.2)

def mkTest {n w : ℕ} (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    Fin n → (Fin w → Bool) → Bool → Bool :=
  fun i p b => table i (fun j => if h : j.val < w then p ⟨j.val, h⟩ else b)

lemma testBit_pack (w : ℕ) (u : Fin (2 ^ w)) (b : Bool) (j : Fin (w + 1)) :
    (u.val + if b then 2 ^ w else 0).testBit j.val =
      if h : j.val < w then u.val.testBit j.val else b := by
  by_cases hj : j.val < w
  · rw [dif_pos hj]
    cases b
    · simp
    · simp only [↓reduceIte]
      exact testBit_add_two_pow_lt u.val w j.val hj
  · rw [dif_neg hj]
    have hjeq : j.val = w := by omega
    rw [hjeq]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact Nat.testBit_lt_two_pow u.isLt
    · simp only [↓reduceIte]
      exact testBit_add_two_pow_eq u.val w u.isLt

lemma nx_iff_div2 (w' : ℕ) (u v : Fin (2 ^ (w' + 1))) (bit : Bool) :
    PEqualNP.Outside.L_lib_377.nx (toBits (w' + 1) u) bit = toBits (w' + 1) v ↔
      bit = v.val.testBit w' ∧ (u.val + if bit then 2 ^ (w' + 1) else 0) / 2 = v.val := by
  set p := u.val + if bit then 2 ^ (w' + 1) else 0
  have hp_lt : p < 2 ^ (w' + 2) := by
    have := u.isLt; rw [Nat.pow_succ]; cases bit <;> simp [p] <;> omega
  have hdiv_lt : p / 2 < 2 ^ (w' + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [Nat.pow_succ] at hp_lt
    exact hp_lt
  have hdiv_bit : ∀ j : Fin (w' + 1),
      (p / 2).testBit j.val = PEqualNP.Outside.L_lib_377.nx (toBits (w' + 1) u) bit j := by
    intro j
    rw [Nat.testBit_div_two]
    have h1 := testBit_pack (w' + 1) u bit ⟨j.val + 1, by omega⟩
    dsimp only at h1
    rw [h1]
    simp only [PEqualNP.Outside.L_lib_377.nx, toBits]
  constructor
  · intro hnx
    have hlast := congrFun hnx ⟨w', by omega⟩
    simp only [PEqualNP.Outside.L_lib_377.nx, toBits, lt_self_iff_false, ↓reduceDIte] at hlast
    refine ⟨hlast, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < w' + 1
    · rw [hdiv_bit ⟨k, hk⟩, hnx]
      rfl
    · have h1 : p / 2 < 2 ^ k :=
        lt_of_lt_of_le hdiv_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : v.val < 2 ^ k :=
        lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  · rintro ⟨_, hdiv⟩
    funext j
    rw [← hdiv_bit j, hdiv]
    rfl

lemma buildBase_spec (n w : ℕ) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    let I := n * 2 ^ (w + 1)
    let x := (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
      table i (fun j => p.val.testBit j.val)))).flatten
    let res := buildBase n w
    res.1.length ≤ n + 1 ∧
    res.2.length = n ∧
    Valid I res.1 ∧
    (∀ M ∈ res.2, ∀ u v, M u v < I + res.1.length ∧ (depths I res.1).getD (M u v) 0 ≤ 1) ∧
    (∀ i : Fin n, ∀ u v : Fin (2 ^ w),
      (wires res.1 x).getD ((res.2.getD i.val (fun _ _ => 0)) u v) false = true ↔
        ∃ bit : Bool, mkTest table i (toBits w u) bit = true ∧
          PEqualNP.Outside.L_lib_377.nx (toBits w u) bit = toBits w v) := by
  intro I x res
  have hx : x.length = I := flatten_ofFn_length n (2 ^ (w + 1)) _
  cases w with
  | zero =>
    dsimp only [res, buildBase]
    set r0 := pushOr0 I []
    have hv0 : Valid I r0.1 := valid_snoc I [] _ (valid_nil I) (by simp) (by simp) (by simp)
    set step : List Gate → ℕ → List Gate × ℕ := fun gs0 i => pushOr2 I gs0 (i * 2) (i * 2 + 1)
    set P : ℕ → List Bool → Bool := fun i y => y.getD (i * 2) false || y.getD (i * 2 + 1) false
    obtain ⟨⟨ext, hext, hlen⟩, hv1, hall1⟩ :=
      buildFnAux_spec I step n 1 1 P r0.1 x hx hv0 (by
        intro k hk gs0 hv_gs0 _
        have hk0 : k * 2 < I := by dsimp only [I]; omega
        have hk1 : k * 2 + 1 < I := by dsimp only [I]; omega
        refine ⟨⟨[⟨GateOp.or, [k * 2, k * 2 + 1]⟩], rfl, by simp⟩, ?_, ?_, ?_, ?_⟩
        · exact valid_snoc I gs0 _ hv_gs0 (by simp) (by simp) (by
            intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> omega)
        · simp only [step, pushOr2, List.length_append, List.length_singleton]; omega
        · simp only [step]
          rw [depths_pushOr2, depths_input I gs0 (k * 2) hk0, depths_input I gs0 (k * 2 + 1) hk1]
          simp
        · simp only [step, P]
          rw [wires_pushOr2 I gs0 _ _ x hx, wires_input gs0 x (k * 2) (by omega),
            wires_input gs0 x (k * 2 + 1) (by omega)])
    set r := buildFnAux step n r0.1
    refine ⟨?_, by simp, hv1, ?_, ?_⟩
    · rw [hext, List.length_append]
      simp only [r0, pushOr0, List.length_append, List.length_nil, List.length_singleton]
      omega
    · intro M hM u v
      simp only [List.mem_ofFn] at hM
      obtain ⟨i, rfl⟩ := hM
      exact ⟨(hall1 i.val i.isLt).1, (hall1 i.val i.isLt).2.1⟩
    · intro i u v
      have hget : (List.ofFn fun a : Fin n => (fun (_ _ : Fin (2 ^ 0)) => r.2 a.val)).getD
          i.val (fun _ _ => 0) = fun _ _ => r.2 i.val := by
        simp [List.getD, i.isLt]
      rw [hget, (hall1 i.val i.isLt).2.2]
      simp only [P, Bool.or_eq_true]
      have hx0 := flatten_ofFn_getD n (2 ^ 1) (fun a p => table a (fun j => p.val.testBit j.val))
        false i ⟨0, by norm_num⟩
      have hx1 := flatten_ofFn_getD n (2 ^ 1) (fun a p => table a (fun j => p.val.testBit j.val))
        false i ⟨1, by norm_num⟩
      change x.getD (i.val * 2 + 0) false = true ∨ x.getD (i.val * 2 + 1) false = true ↔ _
      rw [show (2 : ℕ) = 2 ^ 1 by rfl, hx0, hx1]
      have hnx0 : ∀ bit : Bool, PEqualNP.Outside.L_lib_377.nx (toBits 0 u) bit = toBits 0 v := by
        intro bit; funext j; exact Fin.elim0 j
      constructor
      · rintro (h0 | h1)
        · refine ⟨false, ?_, hnx0 false⟩
          simpa [mkTest] using h0
        · refine ⟨true, ?_, hnx0 true⟩
          simpa [mkTest] using h1
      · rintro ⟨bit, hbit, _⟩
        cases bit
        · left; simpa [mkTest] using hbit
        · right; simpa [mkTest] using hbit
  | succ w' =>
    dsimp only [res, buildBase]
    set r0 := pushOr0 I []
    have hv0 : Valid I r0.1 := valid_snoc I [] _ (valid_nil I) (by simp) (by simp) (by simp)
    refine ⟨by simp [r0, pushOr0], by simp, hv0, ?_, ?_⟩
    · intro M hM u v
      simp only [List.mem_ofFn] at hM
      obtain ⟨i, rfl⟩ := hM
      dsimp only
      set b := v.val.testBit w'
      set p := u.val + if b = true then 2 ^ (w' + 1) else 0
      by_cases hdiv : p / 2 = v.val
      · rw [if_pos hdiv]
        have hu := u.isLt
        have hpow : 2 ^ (w' + 2) = 2 ^ (w' + 1) * 2 := Nat.pow_succ 2 (w' + 1)
        have hite : (if b = true then 2 ^ (w' + 1) else 0) ≤ 2 ^ (w' + 1) := by
          cases b <;> simp
        have hp_lt : p < 2 ^ (w' + 2) := by omega
        have hw_lt : i.val * 2 ^ (w' + 2) + p < I := by
          change i.val * 2 ^ (w' + 2) + p < n * 2 ^ (w' + 2)
          have hi := i.isLt
          nlinarith
        refine ⟨by omega, ?_⟩
        rw [depths_input I r0.1 _ hw_lt]
        omega
      · rw [if_neg hdiv]
        refine ⟨by simp [r0, pushOr0], ?_⟩
        rw [depths_pushOr0]
    · intro i u v
      have hget : (List.ofFn fun a : Fin n => fun (u' v' : Fin (2 ^ (w' + 1))) =>
          if (u'.val + if v'.val.testBit w' = true then 2 ^ (w' + 1) else 0) / 2 = v'.val then
            a.val * 2 ^ (w' + 2) + (u'.val + if v'.val.testBit w' = true then 2 ^ (w' + 1) else 0)
          else r0.2).getD i.val (fun _ _ => 0) = fun u' v' =>
          if (u'.val + if v'.val.testBit w' = true then 2 ^ (w' + 1) else 0) / 2 = v'.val then
            i.val * 2 ^ (w' + 2) + (u'.val + if v'.val.testBit w' = true then 2 ^ (w' + 1) else 0)
          else r0.2 := by
        simp [List.getD, i.isLt]
      rw [hget]
      dsimp only
      set b := v.val.testBit w'
      set p := u.val + if b = true then 2 ^ (w' + 1) else 0
      have hp_lt : p < 2 ^ (w' + 2) := by
        have hu := u.isLt
        have hpow : 2 ^ (w' + 2) = 2 ^ (w' + 1) * 2 := Nat.pow_succ 2 (w' + 1)
        have hite : (if b = true then 2 ^ (w' + 1) else 0) ≤ 2 ^ (w' + 1) := by
          cases b <;> simp
        omega
      by_cases hdiv : p / 2 = v.val
      · rw [if_pos hdiv]
        have hw_lt : i.val * 2 ^ (w' + 2) + p < x.length := by
          rw [hx]; change i.val * 2 ^ (w' + 2) + p < n * 2 ^ (w' + 2)
          have hi := i.isLt; nlinarith
        rw [wires_input r0.1 x _ hw_lt]
        have hxp := flatten_ofFn_getD n (2 ^ (w' + 2))
          (fun a q => table a (fun j => q.val.testBit j.val)) false i ⟨p, hp_lt⟩
        rw [hxp]
        have htb : table i (fun j => p.testBit j.val) = mkTest table i (toBits (w' + 1) u) b := by
          congr 1; funext j
          exact testBit_pack (w' + 1) u b j
        rw [htb]
        constructor
        · intro ht
          exact ⟨b, ht, (nx_iff_div2 w' u v b).2 ⟨rfl, hdiv⟩⟩
        · rintro ⟨bit, ht, hnx⟩
          obtain ⟨rfl, _⟩ := (nx_iff_div2 w' u v bit).1 hnx
          exact ht
      · rw [if_neg hdiv, wires_pushOr0 I [] x hx]
        simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro bit _ hnx
        obtain ⟨rfl, hdiv'⟩ := (nx_iff_div2 w' u v bit).1 hnx
        exact hdiv hdiv'

lemma natProd_bProd_rel {w : ℕ} (L_nat : List (Matrix (Fin w → Bool) (Fin w → Bool) ℕ))
    (L_bool : List (BMat w))
    (hrel : List.Forall₂ (fun M B => ∀ u v, B u v = true ↔ 0 < M (toBits w u) (toBits w v))
      L_nat L_bool) :
    ∀ u v, bProd L_bool u v = true ↔ 0 < L_nat.prod (toBits w u) (toBits w v) := by
  induction hrel with
  | nil =>
    intro u v
    simp only [bProd, bId, decide_eq_true_eq, List.prod_nil, Matrix.one_apply]
    constructor
    · rintro rfl; simp
    · intro h
      by_cases heq : toBits w u = toBits w v
      · exact toBits_inj w heq
      · simp [heq] at h
  | @cons M B L_nat L_bool hhead _ ih =>
    intro u v
    simp only [bProd, bMul, decide_eq_true_eq, List.prod_cons, Matrix.mul_apply]
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · rintro ⟨k, h1, h2⟩
      refine ⟨toBits w k, Finset.mem_univ _, ?_⟩
      exact Nat.mul_pos ((hhead u k).1 h1) ((ih k v).1 h2)
    · rintro ⟨p, _, hp⟩
      have hpos := Nat.pos_of_mul_pos_right hp
      have hpos' := Nat.pos_of_mul_pos_left hp
      refine ⟨ofBits w p, ?_, ?_⟩
      · rw [hhead u (ofBits w p), toBits_ofBits]; exact hpos
      · rw [ih (ofBits w p) v, toBits_ofBits]; exact hpos'

lemma forall₂_ofFn {α β : Type*} (R : α → β → Prop) :
    ∀ (m : ℕ) (f : Fin m → α) (g : Fin m → β),
      (∀ i : Fin m, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => List.Forall₂.nil
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0)
      (forall₂_ofFn R m (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

lemma list_eq_ofFn_getD {α : Type*} (l : List α) (d : α) :
    l = List.ofFn (fun i : Fin l.length => l.getD i.val d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD, h1]

def buildCircuit (n w : ℕ) : Circuit :=
  let I := n * 2 ^ (w + 1)
  let b := buildBase n w
  let p := mulTree I w (Nat.log2 n + 1) b.1 b.2
  let r := orTree I p.1 w (fun u => p.2 u u)
  ⟨r.1, r.2⟩

end PEqualNP.Outside.L_clb_059

open PEqualNP.Outside.L_clb_059 in
theorem PEqualNP.Outside.L_clb_059 : (∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 6 * n * 8 ^ w + 3 ∧
    C.depth I ≤ 1 + (Nat.log2 n + 1) * (w + 1) + w ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let x := (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
        table i (fun j => p.val.testBit j.val)))).flatten
      C.eval x = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true) := by
  intro n w hn I
  refine ⟨buildCircuit n w, ?_⟩
  set dummyTable : Fin n → (Fin (w + 1) → Bool) → Bool := fun _ _ => false
  set dummyX := (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
    dummyTable i (fun j => p.val.testBit j.val)))).flatten
  have hdx : dummyX.length = I := flatten_ofFn_length n (2 ^ (w + 1)) _
  set b := buildBase n w
  set p := mulTree I w (Nat.log2 n + 1) b.1 b.2
  set r := orTree I p.1 w (fun u => p.2 u u)
  have hlog : n ≤ 2 ^ (Nat.log2 n + 1) := by
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [← Nat.log2_eq_log_two] at hlt
    omega
  obtain ⟨hb_len, hb_mats, hb_val, hb_wd, _⟩ := buildBase_spec n w dummyTable
  have hb_len' : b.1.length ≤ n + 1 := hb_len
  have hb_mats' : b.2.length = n := hb_mats
  obtain ⟨⟨ext_p, hext_p, hlen_p⟩, hp_val, hp_wd, _⟩ :=
    mulTree_spec I w (Nat.log2 n + 1) b.1 b.2 1 dummyX hdx hb_val
      (by omega) (by omega) hb_wd
  obtain ⟨ext_r, hext_r, hlen_r⟩ := orTree_prefix I w p.1 (fun u => p.2 u u)
  obtain ⟨hr_val, hr_out⟩ := orTree_valid I w p.1 (fun u => p.2 u u) hp_val (fun u => (hp_wd u u).1)
  have hr_dep := orTree_depth I w p.1 (fun u => p.2 u u) (1 + (Nat.log2 n + 1) * (w + 1))
    (fun u => (hp_wd u u).1) (fun u => (hp_wd u u).2)
  refine ⟨hr_val.1, hr_val.2, hr_out, ?_, hr_dep, ?_⟩
  · show r.1.length ≤ 6 * n * 8 ^ w + 3
    dsimp only [r]
    rw [hext_r, List.length_append]
    dsimp only [p]
    rw [hext_p, List.length_append, hlen_r]
    rw [hb_mats'] at hlen_p
    have h2le8 : 2 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
    have h8pos : 1 ≤ 8 ^ w := Nat.one_le_pow w 8 (by norm_num)
    have h1 : (n - 1) * (2 * 8 ^ w) ≤ 2 * n * 8 ^ w := by
      calc (n - 1) * (2 * 8 ^ w) ≤ n * (2 * 8 ^ w) := Nat.mul_le_mul_right _ (Nat.sub_le n 1)
        _ = 2 * n * 8 ^ w := by ring
    have hsub : 2 ^ w - 1 ≤ 8 ^ w := le_trans (Nat.sub_le _ _) h2le8
    have h1' : ext_p.length ≤ 2 * n * 8 ^ w := le_trans hlen_p h1
    nlinarith
  · intro table x
    have hx : x.length = I := flatten_ofFn_length n (2 ^ (w + 1)) _
    obtain ⟨_, _, _, _, hb_ev⟩ := buildBase_spec n w table
    obtain ⟨_, _, _, hp_ev⟩ :=
      mulTree_spec I w (Nat.log2 n + 1) b.1 b.2 1 x hx hb_val
        (by omega) (by omega) hb_wd
    have hr_ev := orTree_eval I w p.1 (fun u => p.2 u u) x hx (fun u => (hp_wd u u).1)
    change (wires r.1 x).getD r.2 false = true ↔ _
    rw [hr_ev]
    have hp_ev' : ∀ u, (wires p.1 x).getD (p.2 u u) false =
        bProd (b.2.map fun M a c => (wires b.1 x).getD (M a c) false) u u :=
      fun u => congrFun (congrFun hp_ev u) u
    simp only [hp_ev']
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    set test := mkTest table
    set step : Fin (t + 1) → Matrix (Fin w → Bool) (Fin w → Bool) ℕ := fun i =>
      Matrix.of fun q1 q2 =>
        (Finset.univ.filter fun bit : Bool =>
          test i q1 bit = true ∧ PEqualNP.Outside.L_lib_377.nx q1 bit = q2).card
    have hmap_eq : (b.2.map fun M a c => (wires b.1 x).getD (M a c) false) =
        List.ofFn (fun i : Fin (t + 1) => fun a c =>
          (wires b.1 x).getD (b.2.getD i.val (fun _ _ => 0) a c) false) := by
      apply List.ext_getElem
      · simp [hb_mats']
      · intro idx h1 h2
        simp only [List.getElem_map, List.getElem_ofFn]
        have hlt : idx < b.2.length := by simpa using h1
        have hget : b.2[idx] = b.2.getD idx (fun _ _ => 0) := by
          simp [List.getD, hlt]
        rw [hget]
    have hrel : List.Forall₂ (fun M B => ∀ u v, B u v = true ↔ 0 < M (toBits w u) (toBits w v))
        (List.ofFn step) (b.2.map fun M a c => (wires b.1 x).getD (M a c) false) := by
      rw [hmap_eq]
      apply forall₂_ofFn
      intro i u v
      rw [hb_ev i u v]
      simp only [step, Matrix.of_apply, Finset.card_pos, Finset.Nonempty, Finset.mem_filter,
        Finset.mem_univ, true_and]
    have hprod := natProd_bProd_rel (List.ofFn step) _ hrel
    simp only [hprod]
    have hdiag : (∃ u : Fin (2 ^ w), 0 < (List.ofFn step).prod (toBits w u) (toBits w u)) ↔
        0 < Matrix.trace (List.ofFn step).prod := by
      show _ ↔ 0 < ∑ q : Fin w → Bool, (List.ofFn step).prod q q
      rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
      constructor
      · rintro ⟨u, hu⟩; exact ⟨toBits w u, Finset.mem_univ _, hu⟩
      · rintro ⟨q, _, hq⟩; refine ⟨ofBits w q, ?_⟩; rwa [toBits_ofBits]
    rw [hdiag]
    have hlib := PEqualNP.Outside.L_lib_377 t w test
    dsimp only at hlib
    have hstep_eq : (List.ofFn step) =
        List.ofFn (fun i : Fin (t + 1) =>
          (Matrix.of (fun q1 q2 : Fin w → Bool =>
            (Finset.univ.filter (fun bit : Bool =>
              test i q1 bit = true ∧
                (fun (state : Fin w → Bool) (bit : Bool) (j : Fin w) =>
                  if h : j.val + 1 < w then state ⟨j.val + 1, h⟩ else bit) q1 bit = q2)).card) :
            Matrix (Fin w → Bool) (Fin w → Bool) ℕ)) := rfl
    rw [hstep_eq, hlib]
    simp only [Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]
    refine exists_congr (fun word => forall_congr' (fun i => ?_))
    have heq : test i (fun pos : Fin w => word (Fin.ofNat (t + 1) (i.val + pos.val)))
        (word (Fin.ofNat (t + 1) (i.val + w))) =
        table i (fun j => word ⟨(i.val + j.val) % (t + 1), Nat.mod_lt _ hn⟩) := by
      dsimp only [test, mkTest]
      congr 1
      funext j
      by_cases hj : j.val < w
      · rw [dif_pos hj]
        rfl
      · rw [dif_neg hj]
        have hjeq : j.val = w := by omega
        rw [hjeq]
        rfl
    rw [heq]
