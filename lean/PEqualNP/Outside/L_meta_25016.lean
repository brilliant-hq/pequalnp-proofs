import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25016_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def operands (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem operands_eval (x : List Bool) (g : Gate) :
    g.op.eval ((operands g).map fun i => x.getD i false) =
      g.op.eval (g.inputs.map fun i => x.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> rfl

theorem operands_le (g : Gate) (hg : g.inputs.length ≤ 2) :
    (operands g).length ≤ 2 ∧ (g.op = .not → (operands g).length ≤ 1) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [operands] at hg ⊢ <;> omega

def ANDOR (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem trace (N : ℕ) (gs : List Gate) (hF : FanInTwo ⟨gs, 0⟩) (R : Finset ℕ) :
    ∃ (R' : Finset ℕ) (K : List Gate) (saved : ℕ),
      R'.card + saved ≤ R.card + gs.length ∧ K.length = gs.length ∧
      (saved = 0 → ANDOR K) ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ i ∈ R', x.getD i false = y.getD i false) →
        ∀ w ∈ R, (gs.foldl stp x).getD w false = (K.foldl stp y).getD w false := by
  classical
  induction gs using List.reverseRecOn generalizing R with
  | nil =>
    exact ⟨R, [], 0, by simp, rfl, by simp [ANDOR], fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hfit : FanInTwo ⟨gs, 0⟩ := fun a ha => hF a (List.mem_append_left _ ha)
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := hF g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ (operands g).toFinset else R
    let tailGate : Gate := if t ∈ R then ⟨g.op, operands g⟩ else ⟨.or, []⟩
    obtain ⟨R', K, debt, hR', hK, hANDOR, heval⟩ := ih hfit R0
    let saved := if t ∈ R ∧ g.op = .not then 1 else debt
    have hlen := operands_le g hg.2
    have hend : R0.card ≤ R.card + 1 := by
      by_cases ht : t ∈ R
      · have hcard := Finset.card_union_le (R.erase t) (operands g).toFinset
        have herase := Finset.card_erase_of_mem ht
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨t, ht⟩
        have hf := List.toFinset_card_le (operands g)
        simp only [R0, ite_eq_left ht]
        omega
      · simp [R0, ht]
    refine ⟨R', K ++ [tailGate], saved, ?_, by simp [hK], ?_, ?_⟩
    · by_cases hnot : t ∈ R ∧ g.op = .not
      · have hcard := Finset.card_union_le (R.erase t) (operands g).toFinset
        have herase := Finset.card_erase_of_mem hnot.1
        have hpos : 0 < R.card := Finset.card_pos.mpr ⟨t, hnot.1⟩
        have hf := List.toFinset_card_le (operands g)
        have hu := hlen.2 hnot.2
        simp only [R0, ite_eq_left hnot.1] at hR'
        simp only [saved, ite_eq_left hnot, List.length_append, List.length_singleton]
        omega
      · simp only [saved, ite_eq_right hnot, List.length_append, List.length_singleton]
        omega
    · intro hz a ha
      have hnot : ¬(t ∈ R ∧ g.op = .not) := by
        intro h
        simp [saved, h] at hz
      have hzero : debt = 0 := by simpa [saved, hnot] using hz
      rcases List.mem_append.mp ha with ha | ha
      · exact hANDOR hzero a ha
      · have ha' := List.mem_singleton.mp ha
        subst a
        by_cases ht : t ∈ R
        · have hn : g.op ≠ .not := fun h => hnot ⟨ht, h⟩
          have hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
            rcases hg.1 with he | he | he
            · exact Or.inl he
            · exact Or.inr he
            · exact (hn he).elim
          simpa [tailGate, ht] using And.intro hop hlen.1
        · simp [tailGate, ht]
    · intro x y hx hy hxy w hw
      have ev := heval x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [snoc, snoc, len, len, hK, hx, hy]
      split_ifs with hlt he
      · apply ev w
        by_cases ht : t ∈ R
        · have hne : w ≠ t := by dsimp [t]; omega
          rw [show R0 = R.erase t ∪ (operands g).toFinset by simp [R0, ht]]
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
        · simpa only [R0, ite_eq_right ht] using hw
      · have ht : t ∈ R := by change w = t at he; exact he ▸ hw
        rw [show tailGate = ⟨g.op, operands g⟩ by simp [tailGate, ht]]
        change g.op.eval (g.inputs.map fun i => (gs.foldl stp x).getD i false) =
          g.op.eval ((operands g).map fun i => (K.foldl stp y).getD i false)
        rw [← operands_eval (gs.foldl stp x) g]
        congr 1
        apply List.map_congr_left
        intro i hi
        apply ev i
        simp [R0, ht, hi]
      · rfl

theorem oneEach_true {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem input_count {n m : ℕ} (A : Fin n → Fin m → Bool) (R : Finset ℕ)
    (hr : ∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u')
    (hc : ∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v')
    (he : ∀ u u' v v', (∀ i ∈ R, (oneEach u v).getD i false =
      (oneEach u' v').getD i false) → A u v = A u' v') :
    n + m ≤ R.card + 2 := by
  let missRows := Finset.univ.filter (fun u : Fin n => u.val ∉ R)
  let missCols := Finset.univ.filter (fun v : Fin m => n + v.val ∉ R)
  have hmRows : missRows.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro u u' hu hu'
    simp only [missRows, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    apply hr
    intro v
    apply he
    intro i hi
    have hu1 : i ≠ u.val := fun e => hu (e ▸ hi)
    have hu2 : i ≠ u'.val := fun e => hu' (e ▸ hi)
    exact Bool.eq_iff_iff.2 (by simp only [oneEach_true, hu1, hu2, false_or])
  have hmCols : missCols.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro v v' hv hv'
    simp only [missCols, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    apply hc
    intro u
    apply he
    intro i hi
    have hv1 : i ≠ n + v.val := fun e => hv (e ▸ hi)
    have hv2 : i ≠ n + v'.val := fun e => hv' (e ▸ hi)
    exact Bool.eq_iff_iff.2 (by simp only [oneEach_true, hv1, hv2, or_false])
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => u.val ∈ R)
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun v : Fin m => n + v.val ∈ R)
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  change _ + missRows.card = n at h1
  change _ + missCols.card = m at h2
  have h3 : (Finset.univ.filter (fun u : Fin n => u.val ∈ R)).card ≤ (R.filter (· < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, a.isLt⟩
  have h4 : (Finset.univ.filter (fun v : Fin m => n + v.val ∈ R)).card ≤
      (R.filter (¬ · < n)).card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h) :
      Function.Injective (fun v : Fin m => n + v.val))]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, by omega⟩
  have h5 := Finset.card_filter_add_card_filter_not (s := R) (· < n)
  omega

end PEqualNP.Outside.L_meta_25016_aux

open PEqualNP.Outside.L_meta_25016_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in

theorem PEqualNP.Outside.L_meta_25016 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u') → (∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v') → ¬ PEqualNP.Represents.RepSizeAtMost A (n + m - 3) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → n + m - 2 ≤ C.size := by
  intro n m A hn hm hr hc hmono C hFit hRep
  obtain ⟨R, K, saved, hBudget, hK, hANDOR, hEval⟩ :=
    trace (n + m) C.gates (show PEqualNP.MetaComplexity.FanInTwo ⟨C.gates, 0⟩ from hFit) {C.output}
  simp only [Finset.card_singleton] at hBudget
  let D : Circuit := ⟨K, C.output⟩
  have hDSize : D.size = C.size := hK
  have transfer (u u' : Fin n) (v v' : Fin m)
      (h : ∀ i ∈ R, (oneEach u v).getD i false = (oneEach u' v').getD i false) :
      A u v = D.eval (oneEach u' v') := by
    have eq := hEval (oneEach u v) (oneEach u' v') (by simp [oneEach]) (by simp [oneEach])
      h C.output (Finset.mem_singleton_self _)
    exact (hRep u v).symm.trans eq
  by_cases h : saved = 0
  · by_contra he
    apply hmono
    exact ⟨D, hANDOR h, by omega, fun u v => (transfer u u v v (fun _ _ => rfl)).symm⟩
  · have hc' := input_count A R hr hc
      (fun u u' v v' e => (transfer u u' v v' e).trans
        (transfer u' u' v' v' (fun _ _ => rfl)).symm)
    change R.card + saved ≤ 1 + C.size at hBudget
    omega
