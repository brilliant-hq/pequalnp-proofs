import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19155

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The dependency bound and monotonicity lemmas are adapted from L_meta_5470.
theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [ite_eq_left c1] at hw; exact h w hw
      · rw [ite_eq_right c1, ite_eq_left c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

-- the dependency set of the output wire
def depS (n : ℕ) (C : Circuit) : Finset ℕ :=
  (C.gates.foldl dstep ((List.range n).map fun j => ({j} : Finset ℕ))).getD C.output ∅

theorem depS_card (n : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (depS n C).card ≤ C.size + 1 := by
  have hc := cardb C.gates ((List.range n).map fun j => ({j} : Finset ℕ)) 0 hfan (base_card n)
    {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  unfold depS PEqualNP.CircuitLowerBounds.Circuit.size
  omega

theorem dep (C : Circuit) (n i : ℕ) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ j, j ≠ i → x.getD j false = y.getD j false) (hi : i ∉ depS n C) :
    C.eval x = C.eval y := by
  have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y
    ((List.range n).map fun j => ({j} : Finset ℕ)) (by simp [hx]) (by simp [hy]) ?_ C.output ?_
  · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [wires_eq, wires_eq]; exact key
  · intro w hw
    by_cases hwn : w < n
    · apply hw w
      simp [List.getD_eq_getElem?_getD, hwn]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro j hj
    have hji : j ≠ i := fun e => hi (by unfold depS; exact e ▸ hj)
    exact hxy j hji

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id]
    exact fun ⟨h1, h2⟩ => ⟨h a h1, ih h2⟩

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id]
    rintro (h1 | h2)
    · exact Or.inl (h a h1)
    · exact Or.inr (ih h2)

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → W1.length = W2.length →
    (∀ w, W1.getD w false = true → W2.getD w false = true) →
    ∀ w, (gs.foldl wstep W1).getD w false = true → (gs.foldl wstep W2).getD w false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 hop hl h
    simp only [List.foldl_cons]
    apply ih
    · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
    · simp [wstep, hl]
    · intro w hw
      simp only [wstep] at hw ⊢
      rw [getD_snoc] at hw
      rw [getD_snoc, ← hl]
      by_cases c1 : w < W1.length
      · rw [ite_eq_left c1] at hw ⊢; exact h w hw
      · rw [ite_eq_right c1] at hw ⊢
        by_cases c2 : w = W1.length
        · rw [ite_eq_left c2] at hw ⊢
          rcases hop g List.mem_cons_self with e | e
          · rw [e] at hw ⊢
            exact all_mono _ _ _ h hw
          · rw [e] at hw ⊢
            exact any_mono _ _ _ h hw
        · rw [ite_eq_right c2] at hw; exact absurd hw (by decide)

theorem evmono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ w, x.getD w false = true → y.getD w false = true) :
    C.eval x = true → C.eval y = true := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval
  rw [wires_eq, wires_eq]
  exact mono C.gates x y hop hl h C.output


-- The binary OR chain and its evaluation are adapted from L_meta_18822.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_step_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
      omega

theorem foldl_step_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (step xs g) i (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem chain_getD_snoc (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

def orChainAux : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | base, acc, x :: xs => ⟨.or, [acc, x]⟩ :: orChainAux (base + 1) base xs

def orChain (base : ℕ) : List ℕ → List Gate
  | [] => []
  | x :: xs => orChainAux base x xs

def orChainOut (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | _ :: xs => base + xs.length - 1

theorem orChainAux_len (base acc : ℕ) (xs : List ℕ) :
    (orChainAux base acc xs).length = xs.length := by
  induction xs generalizing base acc with
  | nil => rfl
  | cons x xs ih => simp [orChainAux, ih]

theorem orChain_len (base : ℕ) (ws : List ℕ) :
    (orChain base ws).length = ws.length - 1 := by
  cases ws with
  | nil => rfl
  | cons x xs => simp [orChain, orChainAux_len]

theorem foldl_orChainAux (base acc : ℕ) (xs : List ℕ) :
    ∀ (w : List Bool), w.length = base →
      (∀ x ∈ xs, x < base) → acc < base →
      ((orChainAux base acc xs).foldl step w).getD (if xs.isEmpty then acc else base + xs.length - 1) false =
        xs.foldl (fun b x => b || w.getD x false) (w.getD acc false) := by
  induction xs generalizing base acc with
  | nil => intro w _ _ _; simp [orChainAux]
  | cons x xs ih =>
      intro w hlen hxs hacc
      simp only [orChainAux, List.foldl_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hx : x < base := hxs x List.mem_cons_self
      let w' := step w ⟨.or, [acc, x]⟩
      have hw'_len : w'.length = base + 1 := by simp [w', step, hlen]
      have hw'_acc : w'.getD base false = (w.getD acc false || w.getD x false) := by
        simp only [w', step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, chain_getD_snoc w _ base hlen]
      have hxs' : ∀ y ∈ xs, y < base + 1 := fun y hy => by
        have := hxs y (List.mem_cons_of_mem _ hy); omega
      have hsub := ih (base + 1) base w' hw'_len hxs' (by omega)
      have hfold_eq : xs.foldl (fun b y => b || w'.getD y false) (w'.getD base false) =
          xs.foldl (fun b y => b || w.getD y false) (w.getD acc false || w.getD x false) := by
        rw [hw'_acc]
        have hcong : ∀ (l : List ℕ) (b0 : Bool), (∀ y ∈ l, y < base) →
            l.foldl (fun b y => b || w'.getD y false) b0 =
            l.foldl (fun b y => b || w.getD y false) b0 := by
          intro l
          induction l with
          | nil => intro b0 _; rfl
          | cons y ys ihl =>
              intro b0 hyl
              simp only [List.foldl_cons]
              have hy : y < base := hyl y List.mem_cons_self
              have hget : w'.getD y false = w.getD y false := by
                simpa [w', step] using List.getD_append w _ false y (by omega)
              rw [hget]
              exact ihl _ (fun z hz => hyl z (List.mem_cons_of_mem _ hz))
        exact hcong xs _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      cases xs with
      | nil =>
          simp only [List.isEmpty_nil, ↓reduceIte, List.length_nil] at hsub ⊢
          have hidx : base + 1 - 1 = base := by omega
          rw [hidx, hsub, hfold_eq]
      | cons y ys =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsub ⊢
          have hidx : base + (ys.length + 1 + 1) - 1 = base + 1 + (ys.length + 1) - 1 := by omega
          rw [hidx, hsub, hfold_eq]

theorem foldl_orChain (base : ℕ) (ws : List ℕ) (w : List Bool)
    (hlen : w.length = base) (hne : ws ≠ []) (hlt : ∀ x ∈ ws, x < base) :
    ((orChain base ws).foldl step w).getD (orChainOut base ws) false =
      ws.any (fun x => w.getD x false) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons x xs =>
      have h1 := foldl_orChainAux base x xs w hlen
        (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (hlt x List.mem_cons_self)
      have hout : orChainOut base (x :: xs) = if xs.isEmpty then x else base + xs.length - 1 := by
        cases xs <;> simp [orChainOut]
      rw [orChain, hout, h1]
      have hany : ∀ (l : List ℕ) (b : Bool),
          l.foldl (fun acc y => acc || w.getD y false) b = (b || l.any (fun y => w.getD y false)) := by
        intro l
        induction l with
        | nil => intro b; simp
        | cons y ys ihl =>
            intro b
            simp only [List.foldl_cons, List.any_cons, ihl, Bool.or_assoc]
      rw [hany, List.any_cons]


private theorem oneEach_left {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD k false = decide (k = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (by simpa using hk : k < (List.ofFn (fun a : Fin n => decide (a = u))).length),
    List.getElem?_ofFn, dite_eq_left hk, Option.getD_some]
  simp [Fin.ext_iff]

private theorem oneEach_right {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (k = v.val) := by
  have hl : (List.ofFn (fun a : Fin n => decide (a = u))).length = n := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by omega : (List.ofFn (fun a : Fin n => decide (a = u))).length ≤ n+k),
    hl, Nat.add_sub_cancel_left, List.getElem?_ofFn, dite_eq_left hk, Option.getD_some]
  simp [Fin.ext_iff]

private theorem oneEach_on {n : ℕ} (u v : Fin n) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  by_cases h : w < n
  · rw [oneEach_left u v w h]
    simp only [decide_eq_true_eq]
    omega
  · by_cases b : w < n+n
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ w)
      rw [oneEach_right u v k (by omega)]
      simp only [decide_eq_true_eq]
      have := u.isLt
      omega
    · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      have := u.isLt
      have := v.isLt
      have ha : w ≠ u.val := by omega
      have hb : w ≠ n + v.val := by omega
      simp [ha, hb]

-- Removing an essential wire leaves a single common input, which is below a rejected pair.
private theorem mustDepend {m a b : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x z : List Bool) (hx : x.length = m) (hz : z.length = m) (hb : b < m)
    (hxv : ∀ w, x.getD w false = true ↔ w = a ∨ w = b)
    (hzb : z.getD b false = true) (ex : C.eval x = true) (ez : C.eval z = false) :
    a ∈ depS m C := by
  by_contra ha
  let y := List.ofFn (fun k : Fin m => decide (k.val = b))
  have hy : y.length = m := by simp [y]
  have hyv (w : ℕ) : y.getD w false = true ↔ w = b := by
    by_cases hw : w < m
    · simp [y, List.getD_eq_getElem?_getD, hw]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [show w ≠ b by omega]
  have e := dep C m a x y hx hy (by
    intro w hw
    apply Bool.eq_iff_iff.mpr
    rw [hxv, hyv]
    simp [hw]) ha
  have ey : C.eval y = true := e ▸ ex
  have := evmono C hm y z (hy.trans hz.symm) (by
    intro w hw
    exact (hyv w |>.mp hw) ▸ hzb) ey
  simp [ez] at this

private theorem floorBound {n : ℕ} (i j : Fin n) (hn : 2 ≤ n) (C : Circuit)
    (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) C) :
    2 * n - 3 ≤ C.size := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨u₀, hu₀⟩ := exists_ne i
  obtain ⟨v₀, hv₀⟩ := exists_ne j
  let inputs := ((Finset.range (n+n)).erase i.val).erase (n+j.val)
  have sub : inputs ⊆ depS (n+n) C := by
    intro k hk
    simp only [inputs, Finset.mem_erase, Finset.mem_range] at hk
    by_cases hl : k < n
    · let u : Fin n := ⟨k, hl⟩
      have hui : u ≠ i := fun e => hk.2.1 (congrArg Fin.val e)
      apply mustDepend (a := k) (b := n+v₀.val) C hm (oneEach u v₀) (oneEach i v₀)
        (by simp [oneEach]) (by simp [oneEach]) (by have := v₀.isLt; omega)
      · exact oneEach_on u v₀
      · exact (oneEach_on i v₀ _).2 (Or.inr rfl)
      · simp [hr u v₀, hui, hv₀]
      · simp [hr i v₀]
    · let v : Fin n := ⟨k-n, by omega⟩
      have hv : n + v.val = k := by dsimp [v]; omega
      have hvj : v ≠ j := fun e => hk.1 (hv ▸ congrArg (fun w : Fin n => n+w.val) e)
      apply mustDepend (a := k) (b := u₀.val) C hm (oneEach u₀ v) (oneEach u₀ j)
        (by simp [oneEach]) (by simp [oneEach]) (by have := u₀.isLt; omega)
      · intro w
        rw [oneEach_on, hv, or_comm]
      · exact (oneEach_on u₀ j _).2 (Or.inl rfl)
      · simp [hr u₀ v, hu₀, hvj]
      · simp [hr u₀ j]
  have h1 : i.val ∈ Finset.range (n+n) := by simp; have := i.isLt; omega
  have h2 : n+j.val ∈ (Finset.range (n+n)).erase i.val := by
    simp only [Finset.mem_erase, Finset.mem_range]
    have := i.isLt; have := j.isLt; omega
  have hc : inputs.card = n+n-1-1 := by
    simp only [inputs, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1, Finset.card_range]
  have hsub := Finset.card_le_card sub
  have hdep := depS_card (n+n) C (fun g hg => (hm g hg).2)
  omega

private theorem chainMono (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ orChain base ws, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  have aux (acc : ℕ) (xs : List ℕ) :
      ∀ g ∈ orChainAux base acc xs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g.inputs.length ≤ 2 := by
    induction xs generalizing base acc with
    | nil => simp [orChainAux]
    | cons k ks ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | h
      · exact ⟨by simp, Nat.le_refl 2⟩
      · exact ih _ _ g h
  cases ws with
  | nil => simp [orChain]
  | cons a xs => exact aux a xs

private theorem chainOut_lt {m : ℕ} {ws : List ℕ} (hne : ws ≠ [])
    (h : ∀ k ∈ ws, k < m) : orChainOut m ws < m + (orChain m ws).length := by
  rw [orChain_len]
  cases ws with
  | nil => exact (hne rfl).elim
  | cons a as =>
    cases as with
    | nil => simpa [orChainOut] using h a List.mem_cons_self
    | cons b bs => simp [orChainOut]

-- Form each selected union by a chain, then take their intersection.
private def rectangle (m : ℕ) (as bs : List ℕ) : Circuit :=
  let ag := orChain m as
  let next := m + ag.length
  let bg := orChain next bs
  ⟨ag ++ bg ++ [⟨.and, [orChainOut m as, orChainOut next bs]⟩], next + bg.length⟩

private theorem rectangle_mono (m : ℕ) (as bs : List ℕ) : Monotone2 (rectangle m as bs) := by
  intro g hg
  simp only [rectangle, List.mem_append, List.mem_singleton] at hg
  rcases hg with (ha | hb) | rfl
  · exact chainMono _ _ _ ha
  · exact chainMono _ _ _ hb
  · exact ⟨by simp, Nat.le_refl 2⟩

private theorem rectangle_size (m : ℕ) (as bs : List ℕ) :
    (rectangle m as bs).size = (as.length - 1) + (bs.length - 1) + 1 := by
  simp [Circuit.size, rectangle, orChain_len, Nat.add_assoc]

private theorem rectangle_eval (m : ℕ) (as bs : List ℕ) (w : List Bool)
    (hw : w.length = m) (ha : as ≠ []) (hb : bs ≠ [])
    (hla : ∀ k ∈ as, k < m) (hlb : ∀ k ∈ bs, k < m) :
    (rectangle m as bs).eval w =
      (as.any (fun k => w.getD k false) && bs.any (fun k => w.getD k false)) := by
  let ag := orChain m as
  let next := m + ag.length
  let bg := orChain next bs
  let wa := ag.foldl step w
  let wb := bg.foldl step wa
  let a := orChainOut m as
  let b := orChainOut next bs
  have hwa : wa.length = next := by simp [wa, next, foldl_step_len, hw]
  have hwb : wb.length = next + bg.length := by simp [wb, foldl_step_len, hwa]
  have ha' : a < wa.length := by rw [hwa]; exact chainOut_lt ha hla
  have aw : wb.getD a false = as.any (fun k => w.getD k false) := by
    rw [show wb.getD a false = wa.getD a false from foldl_step_getD_lt bg wa a ha']
    exact foldl_orChain m as w hw ha hla
  have hbw := foldl_orChain next bs wa hwa hb (fun k hk => by
    dsimp [next]; have := hlb k hk; omega)
  have bw : wb.getD b false = bs.any (fun k => w.getD k false) := by
    refine hbw.trans ?_
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    have hget (k) (hk : k ∈ bs) : wa.getD k false = w.getD k false :=
      foldl_step_getD_lt ag w k (hw ▸ hlb k hk)
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, (hget k hk) ▸ h⟩,
      fun ⟨k, hk, h⟩ => ⟨k, hk, (hget k hk).symm ▸ h⟩⟩
  change ((ag ++ bg ++ [({ op := GateOp.and, inputs := [a,b] } : Gate)]).foldl step w).getD _ false = _
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (wb ++ [GateOp.and.eval ([a,b].map (fun k => wb.getD k false))]).getD
    (next + bg.length) false = _
  rw [chain_getD_snoc _ _ _ hwb]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, aw, bw]

private def exceptWire (n index : ℕ) : List ℕ := (List.range n).erase index

private theorem except_mem {n t x : ℕ} : x ∈ exceptWire n t ↔ x ≠ t ∧ x < n := by
  simp [exceptWire, (List.nodup_range (n := n)).mem_erase_iff]

private theorem except_len {n : ℕ} (i : Fin n) : (exceptWire n i.val).length = n - 1 := by
  simp [exceptWire, List.length_erase_of_mem (List.mem_range.mpr i.isLt)]

private theorem upperBound {n : ℕ} (i j : Fin n) (hn : 2 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2*n-3) := by
  let as := exceptWire n i.val
  let bs := (exceptWire n j.val).map (n+·)
  have al : as.length = n-1 := except_len i
  have bl : bs.length = n-1 := by simp [bs, except_len j]
  have hla (k) (hk : k ∈ as) : k < n+n := by have := (except_mem.mp hk).2; omega
  have hlb (k) (hk : k ∈ bs) : k < n+n := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    have := (except_mem.mp hr).2
    omega
  refine ⟨rectangle (n+n) as bs, rectangle_mono _ _ _, ?_, ?_⟩
  · rw [rectangle_size, al, bl]; omega
  · intro u v
    have ha : as ≠ [] := fun h => by rw [h] at al; simp at al; omega
    have hb : bs ≠ [] := fun h => by rw [h] at bl; simp at bl; omega
    rw [rectangle_eval (n+n) as bs _ (by simp [oneEach]) ha hb hla hlb]
    have left : as.any (fun k => (oneEach u v).getD k false) = decide (u ≠ i) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨k, hk, h⟩
        obtain ⟨hki, hkn⟩ := except_mem.mp hk
        rw [oneEach_left u v k hkn, decide_eq_true_eq] at h
        exact fun e => hki (h.trans (congrArg Fin.val e))
      · intro h
        exact ⟨u.val, except_mem.mpr ⟨fun e => h (Fin.ext e), u.isLt⟩, (oneEach_on u v _).2 (Or.inl rfl)⟩
    have right : bs.any (fun k => (oneEach u v).getD k false) = decide (v ≠ j) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨k, hk, h⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
        obtain ⟨hrj, hrn⟩ := except_mem.mp hr
        rw [oneEach_right u v r hrn, decide_eq_true_eq] at h
        exact fun e => hrj (h.trans (congrArg Fin.val e))
      · intro h
        refine ⟨n+v.val, List.mem_map.mpr ⟨v.val, except_mem.mpr ⟨fun e => h (Fin.ext e), v.isLt⟩, rfl⟩, ?_⟩
        exact (oneEach_on u v _).2 (Or.inr rfl)
    rw [left, right]

end PEqualNP.Outside.L_meta_19155

open PEqualNP.Outside.L_meta_19155 in
theorem PEqualNP.Outside.L_meta_19155 :
    ∀ (n : ℕ) (i j : Fin n), 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 3) ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) (2 * n - 4) := by
  intro n i j hn
  refine ⟨upperBound i j hn, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  have h := floorBound i j hn C hm hr
  omega
