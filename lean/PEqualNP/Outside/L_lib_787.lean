import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_787

open Finset PEqualNP.CircuitLowerBounds

section Abstract

variable {n : ℕ} (col : ℕ → Fin n → Bool)

def cnt (L : List ℕ) (i : Fin n) : ℕ := L.countP (fun w => col w i)

def rowOf (L : List ℕ) (i : Fin n) : List Bool := L.map (fun w => col w i)

def movedOf (L : List ℕ) : ℕ := (univ.filter fun i => 0 < cnt col L i).card

def wideOf (L : List ℕ) : ℕ :=
  ((univ.filter fun i => 2 ≤ cnt col L i).image (rowOf col L)).card

def portsOf (L : List ℕ) : ℕ := L.countP (fun w => decide (∃ i, col w i = true))

theorem countP_split (p : ℕ → Bool) (g : ℕ) (L : List ℕ) :
    L.countP p = (L.filter (fun w => w ≠ g)).countP p + (if p g then L.count g else 0) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : a = g
    · subst ha
      by_cases hp : p a <;> simp [List.countP_cons, List.filter_cons, List.count_cons, hp, ih] <;>
        omega
    · have hb : (a == g) = false := by simpa using ha
      by_cases hp : p a <;> by_cases hq : p g <;>
        simp [List.countP_cons, List.filter_cons, List.count_cons, hp, hq, ha, hb, ih] <;> omega

theorem sum_cnt_le (L : List ℕ)
    (hL : ∀ w ∈ L, ∀ i j : Fin n, col w i = true → col w j = true → i = j) :
    ∑ i, cnt col L i ≤ portsOf col L := by
  induction L with
  | nil => simp [cnt, portsOf]
  | cons a L ih =>
    have h1 := ih (fun w hw => hL w (List.mem_cons_of_mem a hw))
    have h2 : ∑ i : Fin n, (if col a i = true then 1 else 0) ≤
        (if (decide (∃ i, col a i = true)) = true then 1 else 0) := by
      by_cases h : ∃ i, col a i = true
      · rw [if_pos (by simpa using h), ← Finset.card_filter]
        apply Finset.card_le_one.mpr
        intro i hi j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        exact hL a (by simp) i j hi hj
      · push_neg at h
        simp [h]
    have h3 : ∑ i, cnt col (a :: L) i = ∑ i, cnt col L i + ∑ i : Fin n, (if col a i = true then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [cnt, List.countP_cons]
    have h4 : portsOf col (a :: L) = portsOf col L +
        (if (decide (∃ i, col a i = true)) = true then 1 else 0) := by
      simp only [portsOf, List.countP_cons]
    rw [h3, h4]
    omega

theorem base (L : List ℕ)
    (hL : ∀ w ∈ L, ∀ i j : Fin n, col w i = true → col w j = true → i = j) :
    movedOf col L + wideOf col L ≤ portsOf col L := by
  have hw : wideOf col L ≤ (univ.filter fun i => 2 ≤ cnt col L i).card := Finset.card_image_le
  have hs := sum_cnt_le col L hL
  have h5 : (univ.filter fun i => 0 < cnt col L i).card +
      (univ.filter fun i => 2 ≤ cnt col L i).card ≤ ∑ i, cnt col L i := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  unfold movedOf
  omega

theorem replace (g : ℕ) (U L : List ℕ) (hg : g ∈ L)
    (h1 : ∀ i i', (∀ u ∈ U, col u i = col u i') → col g i = col g i')
    (h2 : ∀ i, col g i = true → ∃ u ∈ U, col u i = true)
    (h3 : (∃ i, col g i = true) ∨ U = []) :
    movedOf col L + wideOf col L + portsOf col (L.filter (fun w => w ≠ g) ++ U) ≤
      movedOf col (L.filter (fun w => w ≠ g) ++ U) + wideOf col (L.filter (fun w => w ≠ g) ++ U) +
        portsOf col L + (U.length - 1) := by
  classical
  set R := L.filter (fun w => w ≠ g) with hR
  set L' := R ++ U with hL'
  have hcnt : ∀ i, cnt col L i = R.countP (fun w => col w i) +
      (if col g i then L.count g else 0) := fun i => countP_split (fun w => col w i) g L
  have hcnt' : ∀ i, cnt col L' i = R.countP (fun w => col w i) + U.countP (fun w => col w i) :=
    fun i => List.countP_append
  have hμ : 0 < L.count g := List.count_pos_iff.mpr hg
  have hm : movedOf col L ≤ movedOf col L' := by
    apply Finset.card_le_card
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hi
    rw [hcnt']
    rw [hcnt] at hi
    by_cases hgi : col g i = true
    · obtain ⟨u, hu, hcu⟩ := h2 i hgi
      have : 0 < U.countP (fun w => col w i) := List.countP_pos_iff.mpr ⟨u, hu, hcu⟩
      omega
    · rw [if_neg hgi] at hi
      omega
  have hdet : ∀ i i', rowOf col L' i = rowOf col L' i' → rowOf col L i = rowOf col L i' := by
    intro i i' h
    unfold rowOf at h ⊢
    rw [List.map_inj_left] at h ⊢
    intro w hw
    by_cases hwg : w = g
    · subst hwg
      exact h1 i i' (fun u hu => h u (List.mem_append_right _ hu))
    · exact h w (List.mem_append_left _ (List.mem_filter.mpr ⟨hw, by simpa using hwg⟩))
  let ψ : List Bool → List Bool := fun r =>
    if h : ∃ i, rowOf col L' i = r then rowOf col L h.choose else r
  have hψ : ∀ i, ψ (rowOf col L' i) = rowOf col L i := by
    intro i
    have h : ∃ j, rowOf col L' j = rowOf col L' i := ⟨i, rfl⟩
    simp only [ψ, dif_pos h]
    exact hdet _ _ h.choose_spec
  have hcol : ∀ i, 2 ≤ cnt col L i → ¬ 2 ≤ cnt col L' i →
      col g i = true ∧ R.countP (fun w => col w i) = 0 ∧ 2 ≤ L.count g := by
    intro i hi hi'
    rw [hcnt] at hi
    rw [hcnt'] at hi'
    by_cases hgi : col g i = true
    · obtain ⟨u, hu, hcu⟩ := h2 i hgi
      have : 0 < U.countP (fun w => col w i) := List.countP_pos_iff.mpr ⟨u, hu, hcu⟩
      rw [if_pos hgi] at hi
      exact ⟨hgi, by omega, by omega⟩
    · rw [if_neg hgi] at hi
      omega
  have hrow : ∀ i, 2 ≤ cnt col L i → ¬ 2 ≤ cnt col L' i →
      rowOf col L i = L.map (fun w => decide (w = g)) := by
    intro i hi hi'
    obtain ⟨hgi, hR0, _⟩ := hcol i hi hi'
    unfold rowOf
    rw [List.map_inj_left]
    intro w hw
    by_cases hwg : w = g
    · subst hwg
      simp [hgi]
    · have hwR : w ∈ R := List.mem_filter.mpr ⟨hw, by simpa using hwg⟩
      have := (List.countP_eq_zero.mp hR0) w hwR
      simp [hwg] at this ⊢
      exact this
  have hwide0 : (∀ i, 2 ≤ cnt col L i → 2 ≤ cnt col L' i) → wideOf col L ≤ wideOf col L' := by
    intro hall
    unfold wideOf
    calc ((univ.filter fun i => 2 ≤ cnt col L i).image (rowOf col L)).card
        ≤ (((univ.filter fun i => 2 ≤ cnt col L' i).image (rowOf col L')).image ψ).card := by
          apply Finset.card_le_card
          intro r hr
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          obtain ⟨i, hi, rfl⟩ := hr
          exact ⟨rowOf col L' i, ⟨i, hall i hi, rfl⟩, hψ i⟩
      _ ≤ _ := Finset.card_image_le
  have hwide1 : wideOf col L ≤ wideOf col L' + 1 := by
    unfold wideOf
    calc ((univ.filter fun i => 2 ≤ cnt col L i).image (rowOf col L)).card
        ≤ (insert (L.map (fun w => decide (w = g)))
            (((univ.filter fun i => 2 ≤ cnt col L' i).image (rowOf col L')).image ψ)).card := by
          apply Finset.card_le_card
          intro r hr
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert] at hr ⊢
          obtain ⟨i, hi, rfl⟩ := hr
          by_cases hi' : 2 ≤ cnt col L' i
          · exact Or.inr ⟨rowOf col L' i, ⟨i, hi', rfl⟩, hψ i⟩
          · exact Or.inl (hrow i hi hi')
      _ ≤ _ := Finset.card_insert_le _ _
      _ ≤ _ := by
          have := (Finset.card_image_le (s := ((univ.filter fun i => 2 ≤ cnt col L' i).image
            (rowOf col L'))) (f := ψ))
          omega
  have hports : portsOf col L = R.countP (fun w => decide (∃ i, col w i = true)) +
      (if (decide (∃ i, col g i = true)) = true then L.count g else 0) :=
    countP_split _ g L
  have hports' : portsOf col L' = R.countP (fun w => decide (∃ i, col w i = true)) +
      U.countP (fun w => decide (∃ i, col w i = true)) := List.countP_append
  have hUl : U.countP (fun w => decide (∃ i, col w i = true)) ≤ U.length := List.countP_le_length
  by_cases hz : ∃ i, col g i = true
  · rw [if_pos (by simpa using hz)] at hports
    obtain ⟨i0, hi0⟩ := hz
    obtain ⟨u, hu, _⟩ := h2 i0 hi0
    have hUpos : 0 < U.length := List.length_pos_of_mem hu
    by_cases hC : ∀ i, 2 ≤ cnt col L i → 2 ≤ cnt col L' i
    · have := hwide0 hC
      omega
    · push_neg at hC
      obtain ⟨i, hi, hi'⟩ := hC
      obtain ⟨_, _, h2g⟩ := hcol i hi (by omega)
      have := hwide1
      omega
  · have hU : U = [] := h3.resolve_left hz
    have hC : ∀ i, 2 ≤ cnt col L i → 2 ≤ cnt col L' i := by
      intro i hi
      by_contra hi'
      exact hz ⟨i, (hcol i hi hi').1⟩
    have := hwide0 hC
    rw [if_neg (by simpa using hz)] at hports
    subst hU
    simp at hports'
    omega

end Abstract

def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepf x := rfl

theorem stepf_len (w : List Bool) (g : Gate) : (stepf w g).length = w.length + 1 := by
  simp [stepf]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepf w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, stepf_len, List.length_cons]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepf w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepf w g) (by rw [stepf_len]; omega), stepf,
      List.getD_append _ _ _ _ hi]

theorem fold_gate2 (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepf w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepf w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      rw [List.foldl_cons, fold_pre gs (stepf w g) _ (by rw [stepf_len]; omega)]
      simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [stepf, List.getD_append_right _ _ _ _ le_rfl]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [fold_pre gs _ i (by simp; omega), List.getD_append _ _ _ _ h]
      · exact List.getD_eq_default _ _ (by omega)
    | succ j =>
      have hl : (stepf w g).length = w.length + 1 := stepf_len w g
      rw [List.foldl_cons, show w.length + (j + 1) = (stepf w g).length + j by omega]
      simp only [List.getElem_cons_succ]
      exact ih (stepf w g) j (by simpa using hj)

def WW (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem WW_in {N : ℕ} (C : Circuit) (w : ℕ) (hw : w < N) (x : Fin N → Bool) :
    WW N C w x = x ⟨w, hw⟩ := by
  unfold WW
  rw [wires_eq, fold_pre _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw),
    List.getElem_ofFn]

theorem WW_out {N : ℕ} (C : Circuit) (w : ℕ) (hw : N + C.gates.length ≤ w) (x : Fin N → Bool) :
    WW N C w x = false := by
  unfold WW
  rw [wires_eq]
  apply List.getD_eq_default
  rw [fold_len]; simpa using hw

theorem WW_gate2 {N : ℕ} (C : Circuit) (p : ℕ) (hp : p < C.gates.length) (x : Fin N → Bool) :
    WW N C (N + p) x = C.gates[p].op.eval (C.gates[p].inputs.map fun i =>
      if i < N + p then WW N C i x else false) := by
  unfold WW
  rw [wires_eq]
  have := fold_gate2 C.gates (List.ofFn x) p hp
  rw [List.length_ofFn] at this
  exact this

noncomputable def usedOf (N : ℕ) (C : Circuit) (p : Fin C.gates.length) : Finset ℕ :=
  (@ite (List ℕ) ((C.gates.get p).op = GateOp.not) (Classical.propDecidable _)
    ((C.gates.get p).inputs.take 1) (C.gates.get p).inputs).toFinset.filter (fun h => h < N + p.val)

noncomputable def costOf (N : ℕ) (C : Circuit) (p : Fin C.gates.length) : ℕ := (usedOf N C p).card - 1

theorem local_eq {N : ℕ} (C : Circuit) (p : Fin C.gates.length) (x y : Fin N → Bool)
    (h : ∀ u ∈ usedOf N C p, WW N C u x = WW N C u y) :
    WW N C (N + p.val) x = WW N C (N + p.val) y := by
  rw [WW_gate2 C p.val p.isLt, WW_gate2 C p.val p.isLt]
  have hg : C.gates[p.val] = C.gates.get p := by simp
  rw [hg]
  unfold usedOf at h
  by_cases hop : (C.gates.get p).op = GateOp.not
  · rw [if_pos hop] at h
    rw [hop]
    simp only [GateOp.eval]
    cases hin : (C.gates.get p).inputs with
    | nil => simp
    | cons i rest =>
      rw [hin] at h
      simp only [List.map_cons, List.headD_cons]
      split_ifs with hi
      · rw [h i (by simp [hi])]
      · rfl
  · rw [if_neg hop] at h
    congr 1
    apply List.map_congr_left
    intro i hi
    split_ifs with hlt
    · exact h i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (by simpa using hi), hlt⟩)
    · rfl

def flipv {N : ℕ} (a : Fin N → Bool) (i : Fin N) : Fin N → Bool :=
  fun h => if h = i then !(a h) else a h

def colOf (N : ℕ) (C : Circuit) (a : Fin N → Bool) (w : ℕ) (i : Fin N) : Bool :=
  decide (WW N C w (flipv a i) ≠ WW N C w a)

theorem bool3 (x y c : Bool) (h : decide (x ≠ c) = decide (y ≠ c)) : x = y := by
  cases x <;> cases y <;> cases c <;> simp_all

theorem induct (n : ℕ) (C : Circuit) (a : Fin n → Bool) (N : ℕ) (hN : N ≤ C.gates.length) :
    ∀ L : List ℕ, (∀ w ∈ L, w < n + N ∨ n + C.gates.length ≤ w) →
      movedOf (colOf n C a) L + wideOf (colOf n C a) L ≤ portsOf (colOf n C a) L +
        ∑ p : Fin C.gates.length, (if p.val < N then costOf n C p else 0) := by
  induction N with
  | zero =>
    intro L hL
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero, add_zero]
    apply base
    intro w hw i j hi hj
    rcases hL w hw with h | h
    · have hwn : w < n := by omega
      unfold colOf at hi hj
      rw [WW_in C w hwn, WW_in C w hwn] at hi hj
      unfold flipv at hi hj
      have e1 : (⟨w, hwn⟩ : Fin n) = i := by
        by_contra hne
        simp [hne] at hi
      have e2 : (⟨w, hwn⟩ : Fin n) = j := by
        by_contra hne
        simp [hne] at hj
      rw [← e1, ← e2]
    · unfold colOf at hi
      rw [WW_out C w h, WW_out C w h] at hi
      simp at hi
  | succ N ih =>
    intro L hL
    have hNl : N < C.gates.length := by omega
    have ih' := ih (by omega)
    have hsum : (∑ p : Fin C.gates.length, (if p.val < N + 1 then costOf n C p else 0)) =
        (∑ p : Fin C.gates.length, (if p.val < N then costOf n C p else 0)) +
          costOf n C ⟨N, hNl⟩ := by
      have hpt : ∀ p : Fin C.gates.length, (if p.val < N + 1 then costOf n C p else 0) =
          (if p.val < N then costOf n C p else 0) +
            (if p = ⟨N, hNl⟩ then costOf n C p else 0) := by
        intro p
        by_cases h1 : p.val < N
        · have hne : p ≠ ⟨N, hNl⟩ := fun h => by subst h; simp at h1
          simp [h1, hne, show p.val < N + 1 by omega]
        · by_cases h2 : p = ⟨N, hNl⟩
          · subst h2; simp
          · have hn1 : ¬ p.val < N + 1 := fun h => h2 (Fin.ext (by simp; omega))
            simp [h1, h2, hn1]
      rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib]
      simp
    rw [hsum]
    by_cases hg : n + N ∈ L
    · set col := colOf n C a with hcol
      set p : Fin C.gates.length := ⟨N, hNl⟩ with hp
      have hloc : ∀ x y : Fin n → Bool, (∀ u ∈ usedOf n C p, WW n C u x = WW n C u y) →
          WW n C (n + N) x = WW n C (n + N) y := fun x y h => local_eq C p x y h
      have hR : ∀ w ∈ L.filter (fun w => w ≠ n + N), w < n + N ∨ n + C.gates.length ≤ w := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := List.mem_filter.mp hw
        have hw2' : w ≠ n + N := by simpa using hw2
        rcases hL w hw1 with h | h
        · left; omega
        · right; exact h
      by_cases hz : ∃ i, col (n + N) i = true
      · have key := replace col (n + N) (usedOf n C p).toList L hg
          (by
            intro i i' h
            have : WW n C (n + N) (flipv a i) = WW n C (n + N) (flipv a i') :=
              hloc _ _ (fun u hu => bool3 _ _ _ (h u (Finset.mem_toList.mpr hu)))
            simp only [hcol, colOf, this])
          (by
            intro i hi
            by_contra hne
            push_neg at hne
            have : WW n C (n + N) (flipv a i) = WW n C (n + N) a := by
              apply hloc
              intro u hu
              have := hne u (Finset.mem_toList.mpr hu)
              simp only [hcol, colOf] at this
              simpa using this
            simp only [hcol, colOf, this] at hi
            simp at hi)
          (Or.inl hz)
        have hL' : ∀ w ∈ L.filter (fun w => w ≠ n + N) ++ (usedOf n C p).toList,
            w < n + N ∨ n + C.gates.length ≤ w := by
          intro w hw
          rcases List.mem_append.mp hw with h | h
          · exact hR w h
          · left
            have := (Finset.mem_filter.mp (Finset.mem_toList.mp h)).2
            simpa [hp] using this
        have := ih' _ hL'
        have hU : (usedOf n C p).toList.length - 1 ≤ costOf n C p := by
          simp [costOf, Finset.length_toList]
        omega
      · push_neg at hz
        have key := replace col (n + N) [] L hg
          (by
            intro i i' _
            have e1 := hz i
            have e2 := hz i'
            simp only [Bool.not_eq_true] at e1 e2
            rw [e1, e2])
          (by
            intro i hi
            exact absurd hi (hz i))
          (Or.inr rfl)
        have hL' : ∀ w ∈ L.filter (fun w => w ≠ n + N) ++ [],
            w < n + N ∨ n + C.gates.length ≤ w := by
          intro w hw
          rw [List.append_nil] at hw
          exact hR w hw
        have := ih' _ hL'
        simp only [List.length_nil] at key
        omega
    · have := ih' L (by
        intro w hw
        have hne : w ≠ n + N := fun h => hg (h ▸ hw)
        rcases hL w hw with h | h
        · left; omega
        · right; exact h)
      omega

theorem countP_ofFn {m : ℕ} (f : Fin m → ℕ) (q : ℕ → Bool) :
    (List.ofFn f).countP q = (univ.filter fun j => q (f j) = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    exact add_comm _ _

end PEqualNP.Outside.L_lib_787

open PEqualNP.Outside.L_lib_787 in
theorem PEqualNP.Outside.L_lib_787 : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (a : Fin n → Bool) (out : Fin m → ℕ),
  let value := fun (v : Fin n → Bool) (j : Fin m) =>
    (C.wires (List.ofFn v)).getD (out j) false
  let delta := fun i : Fin n => Finset.univ.filter (fun j : Fin m =>
    value (fun h => if h = i then !(a h) else a h) j ≠ value a j)
  let moved := Finset.univ.filter (fun i : Fin n => (delta i).Nonempty)
  let wide := (Finset.univ.image delta).filter (fun s => 2 ≤ s.card)
  let ports := Finset.univ.filter (fun j : Fin m => ∃ i : Fin n, j ∈ delta i)
  let cost := fun p : Fin C.gates.length =>
    let g := C.gates.get p
    let used := @ite (List ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
      (Classical.propDecidable _) (g.inputs.take 1) g.inputs
    ((used.toFinset.filter (fun h => h < n + p.val)).card - 1)
  moved.card + wide.card ≤ ports.card + ∑ p, cost p := by
  intro n m C a out value delta moved wide ports cost
  have main := induct n C a C.gates.length le_rfl (List.ofFn out) (fun w _ => by omega)
  have hs : (∑ p : Fin C.gates.length,
      (if p.val < C.gates.length then costOf n C p else 0)) = ∑ p, cost p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [if_pos p.isLt]
    rfl
  have hdelta : ∀ i, delta i = Finset.univ.filter fun j => colOf n C a (out j) i = true := by
    intro i
    ext j
    simp [delta, value, colOf, WW]
    exact Iff.rfl
  have hcd : ∀ i, cnt (colOf n C a) (List.ofFn out) i = (delta i).card := by
    intro i
    rw [hdelta, cnt, countP_ofFn]
  have hmoved : moved.card = movedOf (colOf n C a) (List.ofFn out) := by
    show (Finset.univ.filter fun i => (delta i).Nonempty).card = _
    unfold movedOf
    congr 1
    ext i
    simp [hcd, Finset.card_pos]
  have hports : ports.card = portsOf (colOf n C a) (List.ofFn out) := by
    show (Finset.univ.filter fun j => ∃ i : Fin n, j ∈ delta i).card = _
    unfold portsOf
    rw [countP_ofFn]
    congr 1
    ext j
    simp [hdelta]
  have hwide : wide.card ≤ wideOf (colOf n C a) (List.ofFn out) := by
    unfold wideOf
    calc wide.card ≤ (((Finset.univ.filter fun i => 2 ≤ cnt (colOf n C a) (List.ofFn out) i).image
          (rowOf (colOf n C a) (List.ofFn out))).image
          (fun r : List Bool => Finset.univ.filter fun j : Fin m => r.getD j.val false = true)).card := by
          apply Finset.card_le_card
          intro s hs
          simp only [wide, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hs
          obtain ⟨⟨i, rfl⟩, hs2⟩ := hs
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨rowOf (colOf n C a) (List.ofFn out) i, ⟨i, by rw [hcd]; exact hs2, rfl⟩, ?_⟩
          rw [hdelta]
          ext j
          simp [rowOf, List.map_ofFn]
      _ ≤ _ := Finset.card_image_le
  rw [hs] at main
  omega
