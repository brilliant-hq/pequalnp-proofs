import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19395_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Copied from Legoshi, `L_lib_370.lean`. -/
theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  . subst h; simp
  . rcases Nat.lt_or_gt_of_ne h with h1 | h1
    . rw [List.getD_append _ _ _ _ h1]
    . rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- Running a list of gates on two wire lists, the second read through `φ`.
Copied from Legoshi, `L_lib_370.lean`. -/
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
    . intro k hk i
      have := hφ (k + 1) (by simp; omega) i
      simp only [List.length_append, List.length_singleton]
      constructor
      . intro hi; exact by have := this.1 (by omega); omega
      . intro hi; exact by have := this.2 (by omega); omega
    . intro i
      rw [getD_snoc, getD_snoc]
      have hb : g.op.eval (g.inputs.map fun i => W.getD i false)
          = g.op.eval ((g.inputs.map φ).map fun i => W'.getD i false) := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro j _; exact h j
      have h0 := hφ 0 (by simp) i
      simp only [Nat.add_zero] at h0
      by_cases hi : i = W.length
      . rw [if_pos hi, if_pos (h0.2 hi)]; exact hb
      . rw [if_neg hi, if_neg (fun h' => hi (h0.1 h'))]; exact h i

/-- A chain of OR gates: the first reads `a` and `x0`, each later one the previous gate and the
next wire of the list. -/
def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | a, p, x :: xs => ({ op := GateOp.or, inputs := [a, x] } : Gate) :: chain p (p + 1) xs

/-- The wire holding the OR of the chain. -/
def chainOut : ℕ → ℕ → List ℕ → ℕ
  | a, _, [] => a
  | _, p, _ :: xs => chainOut p (p + 1) xs

theorem chain_length : ∀ (L : List ℕ) (a p : ℕ), (chain a p L).length = L.length := by
  intro L
  induction L with
  | nil => intro a p; rfl
  | cons x xs ih => intro a p; simp [chain, ih]

theorem chain_mono : ∀ (L : List ℕ) (a p : ℕ), ∀ g ∈ chain a p L,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro L
  induction L with
  | nil => intro a p g hg; simp [chain] at hg
  | cons x xs ih =>
    intro a p g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    . simp
    . exact ih p (p + 1) g hg

theorem chain_run : ∀ (L : List ℕ) (a p : ℕ) (w : List Bool), w.length = p → a < p →
    (∀ x ∈ L, x < p) →
    ((chain a p L).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = p + L.length ∧
    (∀ i < p, ((chain a p L).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false) ∧
    chainOut a p L < p + L.length ∧
    (((chain a p L).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        (chainOut a p L) false = true ↔ (w.getD a false = true ∨ ∃ x ∈ L, w.getD x false = true)) := by
  intro L
  induction L with
  | nil =>
    intro a p w hw ha _
    simp only [chain, chainOut, List.foldl_nil, List.length_nil, Nat.add_zero]
    refine ⟨hw, ?_, ha, ?_⟩ <;> simp
  | cons x xs ih =>
    intro a p w hw ha hx
    simp only [chain, chainOut, List.foldl_cons]
    have hxp : x < p := hx x (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih p (p + 1)
      (w ++ [GateOp.eval GateOp.or ([a, x].map fun i => w.getD i false)])
      (by simp [hw]) (by omega) (fun y hy => by have := hx y (by simp [hy]); omega)
    refine ⟨by rw [h1]; simp; omega, ?_, by simp; omega, ?_⟩
    . intro i hi
      rw [h2 i (by omega), List.getD_append _ _ _ _ (by omega)]
    . rw [h4, getD_snoc, if_pos hw.symm]
      have hex : (∃ y ∈ xs, (w ++ [GateOp.eval GateOp.or ([a, x].map fun i => w.getD i false)]).getD
          y false = true) ↔ (∃ y ∈ xs, w.getD y false = true) := by
        constructor
        . rintro ⟨y, hy, h⟩
          refine ⟨y, hy, ?_⟩
          rw [List.getD_append _ _ _ _ (by have := hx y (by simp [hy]); omega)] at h
          exact h
        . rintro ⟨y, hy, h⟩
          refine ⟨y, hy, ?_⟩
          rw [List.getD_append _ _ _ _ (by have := hx y (by simp [hy]); omega)]
          exact h
      rw [hex]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
      tauto

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) :
    ((oneEach u v).getD j false = true) ↔ (j = u.val ∨ j = n + v.val) := by
  by_cases h1 : j < n
  . simp only [oneEach]
    rw [List.getD_append _ _ _ _ (by simpa using h1)]
    simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
    omega
  . by_cases h2 : j < n + m
    . simp only [oneEach]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      simp [List.getD_eq_getElem?_getD, show j - n < m by omega, Fin.ext_iff]
      omega
    . rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp only [Bool.false_eq_true, false_iff]
      omega

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem main (n m s : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m))
    (u0 : Fin n) (v0 : Fin m) (hu0 : u0 ∈ U) (hv0 : v0 ∈ W)
    (hU : ∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) (hW : ∀ v ∈ W, ∀ u : Fin n, A u v = A u v0)
    (hC : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin n) (v : Fin m),
      (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (oneEach u v) = A u v) :
    RepSizeAtMost A (s + (U.card - 1) + (W.card - 1)) := by
  classical
  obtain ⟨C, hmono, hsize, hrep⟩ := hC
  set LU : List ℕ := (U.erase u0).toList.map (fun u => u.val) with hLU
  set LW : List ℕ := (W.erase v0).toList.map (fun v => n + v.val) with hLW
  have hLUlen : LU.length = U.card - 1 := by
    simp [hLU, Finset.card_erase_of_mem hu0]
  have hLWlen : LW.length = W.card - 1 := by
    simp [hLW, Finset.card_erase_of_mem hv0]
  set P := LU.length + LW.length with hP
  set g1 := chain u0.val (n + m) LU with hg1
  set orU := chainOut u0.val (n + m) LU with horU
  set g2 := chain (n + v0.val) (n + m + LU.length) LW with hg2
  set orW := chainOut (n + v0.val) (n + m + LU.length) LW with horW
  set BIG := n + m + P + C.gates.length with hBIG
  let σ : ℕ → ℕ := fun i =>
    if h1 : i < n then
      (if (⟨i, h1⟩ : Fin n) ∈ U then (if i = u0.val then orU else BIG) else i)
    else if h2 : i < n + m then
      (if (⟨i - n, by omega⟩ : Fin m) ∈ W then (if i = n + v0.val then orW else BIG) else i)
    else i + P
  refine ⟨⟨g1 ++ g2 ++ C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map σ } : Gate),
    σ C.output⟩, ?_, ?_, ?_⟩
  . intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with (hg | hg) | ⟨g0, hg0, rfl⟩
    . exact chain_mono _ _ _ g hg
    . exact chain_mono _ _ _ g hg
    . have := hmono g0 hg0
      simpa using this
  . simp only [Circuit.size, List.length_append, List.length_map, hg1, hg2, chain_length]
    simp only [Circuit.size] at hsize
    omega
  . intro u v
    set u' : Fin n := if u ∈ U then u0 else u with hu'
    set v' : Fin m := if v ∈ W then v0 else v with hv'
    have hA : C.eval (oneEach u' v') = A u v := by
      rw [hrep u' v' (by by_cases h : u ∈ U <;> simp [hu', h])
        (by by_cases h : v ∈ W <;> simp [hv', h])]
      have e1 : A u' v' = A u' v := by
        by_cases h : v ∈ W
        . simp only [hv', if_pos h]; exact (hW v h u').symm
        . simp only [hv', if_neg h]
      have e2 : A u' v = A u v := by
        by_cases h : u ∈ U
        . simp only [hu', if_pos h]; exact (hU u h v).symm
        . simp only [hu', if_neg h]
      rw [e1, e2]
    set x := oneEach u v with hx
    have hxlen : x.length = n + m := oneEach_length u v
    -- the first chain
    obtain ⟨a1, a2, a3, a4⟩ := chain_run LU u0.val (n + m) x hxlen (by omega)
      (fun y hy => by
        simp only [hLU, List.mem_map] at hy
        obtain ⟨z, _, rfl⟩ := hy
        omega)
    set w1 := g1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      with hw1
    obtain ⟨b1, b2, b3, b4⟩ := chain_run LW (n + v0.val) (n + m + LU.length) w1 a1 (by omega)
      (fun y hy => by
        simp only [hLW, List.mem_map] at hy
        obtain ⟨z, _, rfl⟩ := hy
        omega)
    set pre := g2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1
      with hpre
    have hprelen : pre.length = n + m + P := by rw [b1]; omega
    have hpreIn : ∀ j < n + m, pre.getD j false = x.getD j false := by
      intro j hj
      rw [b2 j (by omega), a2 j hj]
    have hpreBig : ∀ j, n + m + P ≤ j → pre.getD j false = false := by
      intro j hj
      exact List.getD_eq_default _ _ (by omega)
    have hpreU : pre.getD orU false = true ↔ u ∈ U := by
      rw [b2 orU (by omega), a4, oneEach_getD]
      constructor
      . rintro (h | ⟨y, hy, h⟩)
        . have : u0 = u := Fin.ext (by omega)
          rw [← this]; exact hu0
        . simp only [hLU, List.mem_map, Finset.mem_toList] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          rw [oneEach_getD] at h
          have : z = u := Fin.ext (by omega)
          rw [← this]; exact Finset.mem_of_mem_erase hz
      . intro h
        by_cases h0 : u = u0
        . left; left; rw [h0]
        . right
          refine ⟨u.val, ?_, ?_⟩
          . simp only [hLU, List.mem_map, Finset.mem_toList]
            exact ⟨u, Finset.mem_erase.2 ⟨h0, h⟩, rfl⟩
          . rw [oneEach_getD]; left; rfl
    have hpreW : pre.getD orW false = true ↔ v ∈ W := by
      rw [b4]
      have hw1x : ∀ j < n + m, w1.getD j false = x.getD j false := a2
      rw [hw1x _ (by omega)]
      have hex : (∃ y ∈ LW, w1.getD y false = true) ↔ (∃ y ∈ LW, x.getD y false = true) := by
        constructor
        . rintro ⟨y, hy, h⟩
          refine ⟨y, hy, ?_⟩
          rw [hw1x y (by
            simp only [hLW, List.mem_map] at hy
            obtain ⟨z, _, rfl⟩ := hy
            omega)] at h
          exact h
        . rintro ⟨y, hy, h⟩
          refine ⟨y, hy, ?_⟩
          rw [hw1x y (by
            simp only [hLW, List.mem_map] at hy
            obtain ⟨z, _, rfl⟩ := hy
            omega)]
          exact h
      rw [hex, oneEach_getD]
      constructor
      . rintro (h | ⟨y, hy, h⟩)
        . have : v0 = v := Fin.ext (by omega)
          rw [← this]; exact hv0
        . simp only [hLW, List.mem_map, Finset.mem_toList] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          rw [oneEach_getD] at h
          have : z = v := Fin.ext (by omega)
          rw [← this]; exact Finset.mem_of_mem_erase hz
      . intro h
        by_cases h0 : v = v0
        . left; right; rw [h0]
        . right
          refine ⟨n + v.val, ?_, ?_⟩
          . simp only [hLW, List.mem_map, Finset.mem_toList]
            exact ⟨v, Finset.mem_erase.2 ⟨h0, h⟩, rfl⟩
          . rw [oneEach_getD]; right; rfl
    have horUlt : orU < n + m + P := by omega
    have horWlt : orW < n + m + P := by omega
    have key := run σ C.gates (oneEach u' v') pre ?_ ?_ C.output
    . rw [← hA]
      simp only [Circuit.eval, Circuit.wires, List.foldl_append]
      rw [key]
    . intro k hk i
      rw [hprelen, oneEach_length]
      simp only [σ]
      constructor
      . intro hi
        split_ifs at hi <;> omega
      . intro hi
        rw [dif_neg (by omega), dif_neg (by omega)]; omega
    . intro i
      simp only [σ]
      apply Bool.eq_iff_iff.2
      rw [oneEach_getD]
      by_cases h1 : i < n
      . rw [dif_pos h1]
        by_cases hiU : (⟨i, h1⟩ : Fin n) ∈ U
        . rw [if_pos hiU]
          by_cases hi0 : i = u0.val
          . rw [if_pos hi0, hpreU]
            constructor
            . rintro (h | h)
              . by_contra hn
                simp only [hu', if_neg hn] at h
                exact hn (by rw [show u = u0 from Fin.ext (by omega)]; exact hu0)
              . omega
            . intro h; left; simp only [hu', if_pos h]; exact hi0
          . rw [if_neg hi0, hpreBig _ (by omega)]
            simp only [Bool.false_eq_true, iff_false]
            rintro (h | h)
            . by_cases hu : u ∈ U
              . simp only [hu', if_pos hu] at h; exact hi0 h
              . simp only [hu', if_neg hu] at h
                exact hu (by rw [show u = ⟨i, h1⟩ from Fin.ext h.symm]; exact hiU)
            . omega
        . rw [if_neg hiU, hpreIn i (by omega), oneEach_getD]
          have : i = u'.val ↔ i = u.val := by
            by_cases hu : u ∈ U
            . simp only [hu', if_pos hu]
              constructor
              . intro h; exact absurd (by rw [show (⟨i, h1⟩ : Fin n) = u0 from Fin.ext h]; exact hu0) hiU
              . intro h; exact absurd (by rw [show (⟨i, h1⟩ : Fin n) = u from Fin.ext h]; exact hu) hiU
            . simp only [hu', if_neg hu]
          rw [this]
          constructor <;> rintro (h | h) <;> first | (left; exact h) | omega
      . rw [dif_neg h1]
        by_cases h2 : i < n + m
        . rw [dif_pos h2]
          by_cases hiW : (⟨i - n, by omega⟩ : Fin m) ∈ W
          . rw [if_pos hiW]
            by_cases hi0 : i = n + v0.val
            . rw [if_pos hi0, hpreW]
              constructor
              . rintro (h | h)
                . omega
                . by_contra hn
                  simp only [hv', if_neg hn] at h
                  exact hn (by rw [show v = v0 from Fin.ext (by omega)]; exact hv0)
              . intro h; right; simp only [hv', if_pos h]; exact hi0
            . rw [if_neg hi0, hpreBig _ (by omega)]
              simp only [Bool.false_eq_true, iff_false]
              rintro (h | h)
              . omega
              . by_cases hv : v ∈ W
                . simp only [hv', if_pos hv] at h; exact hi0 h
                . simp only [hv', if_neg hv] at h
                  exact hv (by rw [show v = ⟨i - n, by omega⟩ from Fin.ext (by simp; omega)]; exact hiW)
          . rw [if_neg hiW, hpreIn i (by omega), oneEach_getD]
            have : i = n + v'.val ↔ i = n + v.val := by
              by_cases hv : v ∈ W
              . simp only [hv', if_pos hv]
                constructor
                . intro h
                  exact absurd (by rw [show (⟨i - n, by omega⟩ : Fin m) = v0 from Fin.ext (by simp; omega)]; exact hv0) hiW
                . intro h
                  exact absurd (by rw [show (⟨i - n, by omega⟩ : Fin m) = v from Fin.ext (by simp; omega)]; exact hv) hiW
              . simp only [hv', if_neg hv]
            rw [this]
            constructor <;> rintro (h | h) <;> first | (right; exact h) | omega
        . rw [dif_neg h2, hpreBig _ (by omega)]
          simp only [Bool.false_eq_true, iff_false]
          omega

end PEqualNP.Outside.L_meta_19395_aux

theorem PEqualNP.Outside.L_meta_19395 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → PEqualNP.Represents.RepSizeAtMost A (s + (U.card - 1) + (W.card - 1)) :=
  PEqualNP.Outside.L_meta_19395_aux.main
