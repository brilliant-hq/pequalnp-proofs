import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20592

open PEqualNP.CircuitLowerBounds

private def A : Fin 5 → Fin 5 → Bool :=
  fun u v => (32735232 : ℕ).testBit (5 * u.val + v.val)

private def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [4, 12]⟩], 13⟩

private theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

private theorem upper : PEqualNP.Represents.RepSizeAtMost A 4 :=
  ⟨witness, witness_mono, by decide, by decide +kernel⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wv (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

private theorem wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = step (wv gs x) g := by
  simp [wv, List.foldl_append]

private theorem wv_len (gs : List Gate) (x : List Bool) :
    (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp [step, ih]
    omega

private theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold step
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi]; simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    rw [hk]; simp [h1, h2]

private theorem gate_cases (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

private theorem op_mono_bin (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {a1 a2 b1 b2 : Bool} (ha : a1 = true → a2 = true) (hb : b1 = true → b2 = true) :
    op.eval [a1, b1] = true → op.eval [a2, b2] = true := by
  rcases hop with rfl | rfl <;> cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp_all [GateOp.eval]

private theorem op_mono_un (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {a1 a2 : Bool} (ha : a1 = true → a2 = true) :
    op.eval [a1] = true → op.eval [a2] = true := by
  rcases hop with rfl | rfl <;> simpa [GateOp.eval] using ha

private theorem image_merge {ι : Type} [DecidableEq ι] (X : Finset ι) (a b : ι) :
    X.card ≤ (X.image (fun x => if x = a then b else x)).card + 1 := by
  have h1 : X.erase a ⊆ X.image (fun x => if x = a then b else x) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact Finset.mem_image.mpr ⟨x, hx.2, by simp [hx.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := X) (a := a)
  omega

private theorem ofFn_getD (f : Fin 10 → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < 10 then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

private theorem gate_key (S : Finset (Fin 10)) (W : (Fin 10 → Bool) → ℕ → Bool) (c : Fin 10 → Fin 10)
    (hc : ∀ i, ∃ k, ∀ x y : Fin 10 → Bool, (∀ j, c j = c k → x j = true → y j = true) → W x i = true → W y i = true)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ c' : Fin 10 → Fin 10,
      (S.image c).card ≤ (S.image c').card + 1 ∧
      (∀ v v', c v = c v' → c' v = c' v') ∧
      ∃ k, ∀ x y : Fin 10 → Bool, (∀ j, c' j = c' k → x j = true → y j = true) →
        g.op.eval (g.inputs.map (W x)) = true → g.op.eval (g.inputs.map (W y)) = true := by
  rcases gate_cases g.inputs hg.2 with hi | ⟨a, hi⟩ | ⟨a, b, hi⟩
  · obtain ⟨k, _⟩ := hc 0
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y _ h; rw [hi] at h ⊢; exact h
  · obtain ⟨k, hk⟩ := hc a
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y h
    rw [hi, List.map_singleton, List.map_singleton]
    exact op_mono_un g.op hg.1 (hk x y h)
  · obtain ⟨ka, hka⟩ := hc a
    obtain ⟨kb, hkb⟩ := hc b
    refine ⟨fun v => if c v = c ka then c kb else c v, ?_, ?_, kb, ?_⟩
    · have e : S.image (fun v => if c v = c ka then c kb else c v) =
          (S.image c).image (fun x => if x = c ka then c kb else x) := by
        rw [Finset.image_image]; rfl
      rw [e]
      exact image_merge (S.image c) (c ka) (c kb)
    · intro v v' h; simp only [h]
    · intro x y h
      have e : (if c kb = c ka then c kb else c kb) = c kb := by split <;> rfl
      simp only [e] at h
      have h1 : W x a = true → W y a = true :=
        hka x y fun j hj => h j (by simp [hj])
      have h2 : W x b = true → W y b = true :=
        hkb x y fun j hj => h j (by simp [hj])
      rw [hi, List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil]
      exact op_mono_bin g.op hg.1 h1 h2

private theorem core (S : Finset (Fin 10)) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ c : Fin 10 → Fin 10,
      S.card ≤ (S.image c).card + gs.length ∧
      ∀ i, ∃ k, ∀ x y : Fin 10 → Bool, (∀ j, c j = c k → x j = true → y j = true) →
        (wv gs (List.ofFn x)).getD i false = true → (wv gs (List.ofFn y)).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, by simp, fun i => ?_⟩
    by_cases hi : i < 10
    · refine ⟨⟨i, hi⟩, fun x y h hx => ?_⟩
      simp only [wv, List.foldl_nil, ofFn_getD, hi, dite_true] at hx ⊢
      exact h ⟨i, hi⟩ rfl hx
    · refine ⟨0, fun x y _ hx => ?_⟩
      simp only [wv, List.foldl_nil, ofFn_getD, hi, dite_false] at hx
      exact absurd hx (by decide)
  | append_singleton gs g ih =>
    have hm1 : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hm g' (List.mem_append_left _ hg')
    have hmg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hm g (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨c, hcard, hc⟩ := ih hm1
    obtain ⟨c', hmerge, hpres, kg, hkg⟩ :=
      gate_key S (fun x i => (wv gs (List.ofFn x)).getD i false) c hc g hmg
    refine ⟨c', by simp only [List.length_append, List.length_singleton]; omega, fun i => ?_⟩
    by_cases hlt : i < 10 + gs.length
    · obtain ⟨k, hk⟩ := hc i
      refine ⟨k, fun x y h hx => ?_⟩
      rw [wv_snoc, step_getD] at hx ⊢
      have hlx : (wv gs (List.ofFn x)).length = 10 + gs.length := by rw [wv_len]; simp
      have hly : (wv gs (List.ofFn y)).length = 10 + gs.length := by rw [wv_len]; simp
      rw [hlx] at hx; rw [hly]
      simp only [hlt, ite_true] at hx ⊢
      exact hk x y (fun j hj => h j (hpres j k hj)) hx
    · by_cases heq : i = 10 + gs.length
      · refine ⟨kg, fun x y h hx => ?_⟩
        rw [wv_snoc, step_getD] at hx ⊢
        have hlx : (wv gs (List.ofFn x)).length = 10 + gs.length := by rw [wv_len]; simp
        have hly : (wv gs (List.ofFn y)).length = 10 + gs.length := by rw [wv_len]; simp
        rw [hlx] at hx; rw [hly]
        subst heq
        simp only [lt_irrefl, ite_false, ite_true] at hx ⊢
        exact hkg x y h hx
      · refine ⟨0, fun x y _ hx => ?_⟩
        rw [wv_snoc, step_getD] at hx
        have hlx : (wv gs (List.ofFn x)).length = 10 + gs.length := by rw [wv_len]; simp
        rw [hlx] at hx
        simp only [hlt, heq, ite_false] at hx
        exact absurd hx (by decide)

private def oneEachFun (u v : Fin 5) : Fin 10 → Bool :=
  fun i => if i.val < 5 then decide (i.val = u.val) else decide (i.val - 5 = v.val)

private theorem oneEach_eq_ofFn (u v : Fin 5) :
    PEqualNP.Represents.oneEach u v = List.ofFn (oneEachFun u v) := by
  revert u v
  decide

private theorem eval_eq_wv (C : Circuit) (u v : Fin 5) :
    C.eval (PEqualNP.Represents.oneEach u v) =
      (wv C.gates (List.ofFn (oneEachFun u v))).getD C.output false := by
  rw [oneEach_eq_ofFn]
  rfl

private def ess : Finset (Fin 10) := {3, 4, 5, 6, 7}

private theorem ess_card : ess.card = 5 := by decide

private theorem lower : ¬ PEqualNP.Represents.RepSizeAtMost A 3 := by
  rintro ⟨C, hmono, hsize, hrep⟩
  obtain ⟨c, hcard, hc⟩ := core ess C.gates hmono
  obtain ⟨k, hk⟩ := hc C.output
  have hgt : 1 < (ess.image c).card := by
    have : ess.card = 5 := ess_card
    have : C.gates.length ≤ 3 := hsize
    omega
  have hne : ∃ j ∈ ess, c j ≠ c k := by
    by_contra hall
    have hsub : ess.image c ⊆ {c k} := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      exact Finset.mem_singleton.mpr (Classical.byContradiction fun h => hall ⟨j, hj, h⟩)
    have hle := Finset.card_le_card hsub
    simp at hle
    omega
  obtain ⟨j, hj, hjk⟩ := hne
  have step_contra : ∀ (u1 v1 u2 v2 : Fin 5),
      A u1 v1 = true → A u2 v2 = false →
      (∀ m : Fin 10, m ≠ j → oneEachFun u1 v1 m = true → oneEachFun u2 v2 m = true) →
      False := by
    intro u1 v1 u2 v2 h1 h2 hle
    have hx : (wv C.gates (List.ofFn (oneEachFun u1 v1))).getD C.output false = true := by
      rw [← eval_eq_wv, hrep u1 v1, h1]
    have hy : (wv C.gates (List.ofFn (oneEachFun u2 v2))).getD C.output false = true :=
      hk (oneEachFun u1 v1) (oneEachFun u2 v2) (fun m hm => hle m (fun hmj => hjk (hmj ▸ hm))) hx
    rw [← eval_eq_wv, hrep u2 v2, h2] at hy
    exact Bool.false_ne_true hy
  simp only [ess, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact step_contra 3 0 0 0 (by decide) (by decide) (by decide)
  · exact step_contra 4 3 3 3 (by decide) (by decide) (by decide)
  · exact step_contra 3 0 3 3 (by decide) (by decide) (by decide)
  · exact step_contra 3 1 3 3 (by decide) (by decide) (by decide)
  · exact step_contra 3 2 3 3 (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_20592

theorem PEqualNP.Outside.L_meta_20592 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32735232 : ℕ).testBit (5 * u.val + v.val)) 4 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32735232 : ℕ).testBit (5 * u.val + v.val)) 3) :=
  ⟨PEqualNP.Outside.L_meta_20592.upper, PEqualNP.Outside.L_meta_20592.lower⟩
