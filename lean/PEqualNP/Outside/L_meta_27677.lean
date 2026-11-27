import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27677

open PEqualNP.CircuitLowerBounds

def perm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def extTrue (y : Fin 8 → Bool) : Fin 9 → Bool :=
  fun i => if h : i.val = 0 then true else y ⟨i.val - 1, by omega⟩

def f1 (y : Fin 8 → Bool) : Bool := perm3 (extTrue y)

def setVec (S : Finset (Fin 8)) : Fin 8 → Bool := fun i => decide (i ∈ S)

lemma f1_essential (i : Fin 8) :
    ∃ y : Fin 8 → Bool, f1 (Function.update y i false) ≠ f1 (Function.update y i true) := by
  fin_cases i
  · refine ⟨setVec {2, 7}, by decide⟩
  · refine ⟨setVec {2, 6}, by decide⟩
  · refine ⟨setVec {0, 7}, by decide⟩
  · refine ⟨setVec {7}, by decide⟩
  · refine ⟨setVec {6}, by decide⟩
  · refine ⟨setVec {0, 4}, by decide⟩
  · refine ⟨setVec {4}, by decide⟩
  · refine ⟨setVec {3}, by decide⟩

lemma f1_nonconst : f1 (fun _ => false) = false ∧ f1 (fun _ => true) = true := by
  constructor <;> decide

lemma no_mono_and_split (A : Finset (Fin 8)) (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (g1 g2 : (Fin 8 → Bool) → Bool)
    (hm1 : ∀ y1 y2, (∀ i, y1 i = true → y2 i = true) → g1 y1 = true → g1 y2 = true)
    (hm2 : ∀ y1 y2, (∀ i, y1 i = true → y2 i = true) → g2 y1 = true → g2 y2 = true)
    (hd1 : ∀ y1 y2, (∀ i ∈ A, y1 i = y2 i) → g1 y1 = g1 y2)
    (hd2 : ∀ y1 y2, (∀ i ∈ Aᶜ, y1 i = y2 i) → g2 y1 = g2 y2)
    (heq : ∀ y, f1 y = (g1 y && g2 y)) : False := by
  have hg1_false : g1 (fun _ => false) = false := by
    by_contra h1
    have h1t : g1 (fun _ => false) = true := by cases h : g1 (fun _ => false) <;> simp_all
    have hg1_all : ∀ y, g1 y = true := fun y => hm1 _ y (fun _ h => by cases h) h1t
    rcases hAne with ⟨a, ha⟩
    rcases f1_essential a with ⟨y, hy⟩
    have hagree : ∀ i ∈ Aᶜ, Function.update y a false i = Function.update y a true i := by
      intro i hi
      have hne : i ≠ a := by
        intro h; subst h; simp at hi; exact hi ha
      simp [hne]
    have h2 := hd2 _ _ hagree
    rw [heq, heq, hg1_all, hg1_all, h2] at hy
    exact hy rfl
  have hg2_false : g2 (fun _ => false) = false := by
    by_contra h2
    have h2t : g2 (fun _ => false) = true := by cases h : g2 (fun _ => false) <;> simp_all
    have hg2_all : ∀ y, g2 y = true := fun y => hm2 _ y (fun _ h => by cases h) h2t
    rcases hBne with ⟨b, hb⟩
    rcases f1_essential b with ⟨y, hy⟩
    have hagree : ∀ i ∈ A, Function.update y b false i = Function.update y b true i := by
      intro i hi
      have hne : i ≠ b := by
        intro h; subst h; simp at hb; exact hb hi
      simp [hne]
    have h1 := hd1 _ _ hagree
    rw [heq, heq, hg2_all, hg2_all, h1] at hy
    exact hy rfl
  have hcross : ∀ S : Finset (Fin 8), f1 (setVec S) = true →
      (∃ p ∈ S, p ∈ A) ∧ (∃ q ∈ S, q ∈ Aᶜ) := by
    intro S hS
    rw [heq, Bool.and_eq_true] at hS
    constructor
    · by_contra hno
      have hagree : ∀ i ∈ A, setVec S i = false := by
        intro i hi
        unfold setVec
        simp only [decide_eq_false_iff_not]
        intro hiS; exact hno ⟨i, hiS, hi⟩
      have := hd1 (setVec S) (fun _ => false) hagree
      rw [hg1_false, hS.1] at this; cases this
    · by_contra hno
      have hagree : ∀ i ∈ Aᶜ, setVec S i = false := by
        intro i hi
        unfold setVec
        simp only [decide_eq_false_iff_not]
        intro hiS; exact hno ⟨i, hiS, hi⟩
      have := hd2 (setVec S) (fun _ => false) hagree
      rw [hg2_false, hS.2] at this; cases this
  have hS1 : f1 (setVec {3, 7}) = true := by decide
  have hS2 : f1 (setVec {4, 6}) = true := by decide
  rcases hcross {3, 7} hS1 with ⟨⟨p, hpS, hpA⟩, ⟨q, hqS, hqB⟩⟩
  rcases hcross {4, 6} hS2 with ⟨⟨r, hrS, hrA⟩, ⟨s, hsS, hsB⟩⟩
  have hS1_g1 : g1 (setVec {3, 7}) = true := by
    rw [heq, Bool.and_eq_true] at hS1; exact hS1.1
  have hS2_g2 : g2 (setVec {4, 6}) = true := by
    rw [heq, Bool.and_eq_true] at hS2; exact hS2.2
  have hp_ne_q : p ≠ q := by intro h; subst h; simp at hqB; exact hqB hpA
  have hr_ne_s : r ≠ s := by intro h; subst h; simp at hsB; exact hsB hrA
  have hagree1 : ∀ i ∈ A, setVec {p, s} i = setVec {3, 7} i := by
    intro i hi
    unfold setVec
    have hi_ne_s : i ≠ s := by intro h; subst h; simp at hsB; exact hsB hi
    have hi_ne_q : i ≠ q := by intro h; subst h; simp at hqB; exact hqB hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpS hqS ⊢
    rcases hpS with rfl | rfl <;> rcases hqS with rfl | rfl
    · exact (hp_ne_q rfl).elim
    · simp [hi_ne_s, hi_ne_q]
    · simp [hi_ne_s, hi_ne_q]
    · exact (hp_ne_q rfl).elim
  have hagree2 : ∀ i ∈ Aᶜ, setVec {p, s} i = setVec {4, 6} i := by
    intro i hi
    unfold setVec
    have hi_ne_p : i ≠ p := by intro h; subst h; simp at hi; exact hi hpA
    have hi_ne_r : i ≠ r := by intro h; subst h; simp at hi; exact hi hrA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrS hsS ⊢
    rcases hrS with rfl | rfl <;> rcases hsS with rfl | rfl
    · exact (hr_ne_s rfl).elim
    · simp [hi_ne_p, hi_ne_r]
    · simp [hi_ne_p, hi_ne_r]
    · exact (hr_ne_s rfl).elim
  have hps : f1 (setVec {p, s}) = true := by
    rw [heq, hd1 _ _ hagree1, hd2 _ _ hagree2, hS1_g1, hS2_g2]
    rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpS hsS
  rcases hpS with rfl | rfl <;> rcases hsS with rfl | rfl <;> revert hps <;> decide

lemma extTrue_mono (y1 y2 : Fin 8 → Bool) (hle : ∀ i, y1 i = true → y2 i = true)
    (j : Fin 9) (h : extTrue y1 j = true) : extTrue y2 j = true := by
  unfold extTrue at h ⊢
  split_ifs at h ⊢ with hj
  · rfl
  · exact hle _ h

lemma f1_mono (y1 y2 : Fin 8 → Bool) (hle : ∀ i, y1 i = true → y2 i = true)
    (h1 : f1 y1 = true) : f1 y2 = true := by
  have hm := extTrue_mono y1 y2 hle
  unfold f1 perm3 at h1 ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 ⊢
  rcases h1 with (((((⟨⟨a, b⟩, c⟩ | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩)
  · left; left; left; left; left; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩
  · left; left; left; left; right; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩
  · left; left; left; right; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩
  · left; left; right; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩
  · left; right; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩
  · right; exact ⟨⟨hm _ a, hm _ b⟩, hm _ c⟩

lemma no_mono_or_split (A : Finset (Fin 8)) (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (g1 g2 : (Fin 8 → Bool) → Bool)
    (hd1 : ∀ y1 y2, (∀ i ∈ A, y1 i = y2 i) → g1 y1 = g1 y2)
    (hd2 : ∀ y1 y2, (∀ i ∈ Aᶜ, y1 i = y2 i) → g2 y1 = g2 y2)
    (heq : ∀ y, f1 y = (g1 y || g2 y)) : False := by
  have hmin : ∀ M : Finset (Fin 8), f1 (setVec M) = true →
      (∀ x ∈ M, f1 (setVec (M.erase x)) = false) →
      M ⊆ A ∨ M ⊆ Aᶜ := by
    intro M hM hprop
    rw [heq, Bool.or_eq_true] at hM
    rcases hM with h1 | h2
    · left
      intro i hi
      by_contra hni
      have hagree : ∀ j ∈ A, setVec (M ∩ A) j = setVec M j := by
        intro j hj; simp [setVec, hj]
      have hval : f1 (setVec (M ∩ A)) = true := by
        rw [heq, hd1 _ _ hagree, h1]; rfl
      have hsub : ∀ j, setVec (M ∩ A) j = true → setVec (M.erase i) j = true := by
        intro j hj
        unfold setVec at hj ⊢
        simp only [decide_eq_true_eq, Finset.mem_inter, Finset.mem_erase] at hj ⊢
        exact ⟨fun h => hni (h ▸ hj.2), hj.1⟩
      have hval2 := f1_mono _ _ hsub hval
      rw [hprop i hi] at hval2; cases hval2
    · right
      intro i hi
      by_contra hni
      have hagree : ∀ j ∈ Aᶜ, setVec (M ∩ Aᶜ) j = setVec M j := by
        intro j hj; simp [setVec, hj]
      have hval : f1 (setVec (M ∩ Aᶜ)) = true := by
        rw [heq, hd2 _ _ hagree, h2]; simp
      have hsub : ∀ j, setVec (M ∩ Aᶜ) j = true → setVec (M.erase i) j = true := by
        intro j hj
        unfold setVec at hj ⊢
        simp only [decide_eq_true_eq, Finset.mem_inter, Finset.mem_erase] at hj ⊢
        exact ⟨fun h => hni (h ▸ hj.2), hj.1⟩
      have hval2 := f1_mono _ _ hsub hval
      rw [hprop i hi] at hval2; cases hval2
  have hsame : ∀ M : Finset (Fin 8), f1 (setVec M) = true →
      (∀ x ∈ M, f1 (setVec (M.erase x)) = false) →
      ∀ a ∈ M, ∀ b ∈ M, (a ∈ A ↔ b ∈ A) := by
    intro M hM hprop a ha b hb
    rcases hmin M hM hprop with hA | hB
    · exact ⟨fun _ => hA hb, fun _ => hA ha⟩
    · have hna : a ∉ A := by simpa using hB ha
      have hnb : b ∉ A := by simpa using hB hb
      exact ⟨fun h => (hna h).elim, fun h => (hnb h).elim⟩
  have hM1 : ∀ a ∈ ({3, 7} : Finset (Fin 8)), ∀ b ∈ ({3, 7} : Finset (Fin 8)), (a ∈ A ↔ b ∈ A) :=
    hsame {3, 7} (by decide) (by decide)
  have hM2 : ∀ a ∈ ({4, 6} : Finset (Fin 8)), ∀ b ∈ ({4, 6} : Finset (Fin 8)), (a ∈ A ↔ b ∈ A) :=
    hsame {4, 6} (by decide) (by decide)
  have hM3 : ∀ a ∈ ({0, 2, 7} : Finset (Fin 8)), ∀ b ∈ ({0, 2, 7} : Finset (Fin 8)), (a ∈ A ↔ b ∈ A) :=
    hsame {0, 2, 7} (by decide) (by decide)
  have hM4 : ∀ a ∈ ({0, 4, 5} : Finset (Fin 8)), ∀ b ∈ ({0, 4, 5} : Finset (Fin 8)), (a ∈ A ↔ b ∈ A) :=
    hsame {0, 4, 5} (by decide) (by decide)
  have hM5 : ∀ a ∈ ({1, 2, 6} : Finset (Fin 8)), ∀ b ∈ ({1, 2, 6} : Finset (Fin 8)), (a ∈ A ↔ b ∈ A) :=
    hsame {1, 2, 6} (by decide) (by decide)
  have hall : ∀ i : Fin 8, i ∈ A ↔ (0 : Fin 8) ∈ A := by
    have e02 : (2 : Fin 8) ∈ A ↔ (0 : Fin 8) ∈ A := hM3 2 (by decide) 0 (by decide)
    have e07 : (7 : Fin 8) ∈ A ↔ (0 : Fin 8) ∈ A := hM3 7 (by decide) 0 (by decide)
    have e37 : (3 : Fin 8) ∈ A ↔ (7 : Fin 8) ∈ A := hM1 3 (by decide) 7 (by decide)
    have e04 : (4 : Fin 8) ∈ A ↔ (0 : Fin 8) ∈ A := hM4 4 (by decide) 0 (by decide)
    have e05 : (5 : Fin 8) ∈ A ↔ (0 : Fin 8) ∈ A := hM4 5 (by decide) 0 (by decide)
    have e46 : (6 : Fin 8) ∈ A ↔ (4 : Fin 8) ∈ A := hM2 6 (by decide) 4 (by decide)
    have e12 : (1 : Fin 8) ∈ A ↔ (2 : Fin 8) ∈ A := hM5 1 (by decide) 2 (by decide)
    intro i
    fin_cases i
    · rfl
    · exact e12.trans e02
    · exact e02
    · exact e37.trans e07
    · exact e04
    · exact e05
    · exact e46.trans e04
    · exact e07
  rcases hAne with ⟨a, ha⟩
  rcases hBne with ⟨b, hb⟩
  simp only [Finset.mem_compl] at hb
  exact hb ((hall b).mpr ((hall a).mp ha))

def evalGateWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma evalGateWires_length (gs : List Gate) (x : List Bool) :
    (evalGateWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalGateWires]
  | cons g tl ih =>
    simp only [evalGateWires, List.foldl_cons]
    have h := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    unfold evalGateWires at h
    rw [h, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalGateWires_prefix (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (evalGateWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g tl ih =>
    simp only [evalGateWires, List.foldl_cons]
    have h := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (by rw [List.length_append, List.length_singleton]; omega)
    unfold evalGateWires at h
    rw [h, List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
      List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

lemma evalGateWires_at (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]'hj).inputs, i < x.length + j) :
    (evalGateWires gs x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (evalGateWires gs x).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]'hj] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j]'hj :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  have hpre_len : (evalGateWires (gs.take j) x).length = x.length + j := by
    rw [evalGateWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have happ : ∀ gs1 gs2 x, evalGateWires (gs1 ++ gs2) x = evalGateWires gs2 (evalGateWires gs1 x) := by
    intro gs1 gs2 x; unfold evalGateWires; rw [List.foldl_append]
  have hstep : (evalGateWires (gs.take j ++ [gs[j]'hj]) x).getD (x.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (evalGateWires (gs.take j) x).getD i false) := by
    rw [happ]
    set w := evalGateWires (gs.take j) x
    unfold evalGateWires
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hpre_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
    simp
  have hfull : (evalGateWires gs x).getD (x.length + j) false =
      (evalGateWires (gs.take j ++ [gs[j]'hj]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    rw [happ]
    exact evalGateWires_prefix (gs.drop (j + 1)) _ (by rw [evalGateWires_length, List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), List.length_singleton]; omega)
  rw [hfull, hstep]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hrb i hi
  conv_rhs => rw [hsplit]
  rw [happ, happ]
  rw [evalGateWires_prefix (gs.drop (j + 1)) _ (by rw [evalGateWires_length, hpre_len, List.length_singleton]; omega),
    evalGateWires_prefix [gs[j]'hj] _ (by rw [hpre_len]; exact hlt)]

def stepCollapse (m : List (Bool ⊕ ℕ)) (g : Gate) : Bool ⊕ ℕ :=
  let w := m.length
  match g.op, g.inputs with
  | .not, [a] =>
    match m.getD a (Sum.inl false) with
    | Sum.inl b => Sum.inl (!b)
    | Sum.inr _ => Sum.inr w
  | .and, [a, b] =>
    match m.getD a (Sum.inl false), m.getD b (Sum.inl false) with
    | Sum.inl false, _ => Sum.inl false
    | _, Sum.inl false => Sum.inl false
    | Sum.inl true, v => v
    | u, Sum.inl true => u
    | Sum.inr _, Sum.inr _ => Sum.inr w
  | .or, [a, b] =>
    match m.getD a (Sum.inl false), m.getD b (Sum.inl false) with
    | Sum.inl true, _ => Sum.inl true
    | _, Sum.inl true => Sum.inl true
    | Sum.inl false, v => v
    | u, Sum.inl false => u
    | Sum.inr _, Sum.inr _ => Sum.inr w
  | _, _ => Sum.inl false

def initCollapse : List (Bool ⊕ ℕ) :=
  Sum.inl true :: (List.range 8).map (fun i => Sum.inr (i + 1))

def runCollapse (gs : List Gate) : List (Bool ⊕ ℕ) :=
  gs.foldl (fun m g => m ++ [stepCollapse m g]) initCollapse

lemma runCollapse_length (gs : List Gate) : (runCollapse gs).length = 9 + gs.length := by
  have h : ∀ (l : List Gate) (acc : List (Bool ⊕ ℕ)),
      (l.foldl (fun m g => m ++ [stepCollapse m g]) acc).length = acc.length + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons g tl ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  unfold runCollapse
  rw [h]
  rfl

lemma runCollapse_prefix (gs : List Gate) (acc : List (Bool ⊕ ℕ)) {i : ℕ} (hi : i < acc.length) :
    (gs.foldl (fun m g => m ++ [stepCollapse m g]) acc).getD i (Sum.inl false) =
      acc.getD i (Sum.inl false) := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ [stepCollapse acc g]) (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
      List.getElem_append_left hi]

lemma runCollapse_init_getD (gs : List Gate) :
    (runCollapse gs).getD 0 (Sum.inl false) = Sum.inl true ∧
    ∀ i < 8, (runCollapse gs).getD (i + 1) (Sum.inl false) = Sum.inr (i + 1) := by
  have h0 : (runCollapse gs).getD 0 (Sum.inl false) = initCollapse.getD 0 (Sum.inl false) :=
    runCollapse_prefix gs initCollapse (by decide)
  refine ⟨by rw [h0]; rfl, ?_⟩
  intro i hi
  have h1 : (runCollapse gs).getD (i + 1) (Sum.inl false) =
      initCollapse.getD (i + 1) (Sum.inl false) :=
    runCollapse_prefix gs initCollapse (i := i + 1) (by simp [initCollapse]; omega)
  rw [h1]
  unfold initCollapse
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [hi]

lemma runCollapse_at (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]'hj).inputs, i < 9 + j) :
    (runCollapse gs).getD (9 + j) (Sum.inl false) =
      match (gs[j]'hj).op, (gs[j]'hj).inputs with
      | .not, [a] =>
        match (runCollapse gs).getD a (Sum.inl false) with
        | Sum.inl b => Sum.inl (!b)
        | Sum.inr _ => Sum.inr (9 + j)
      | .and, [a, b] =>
        match (runCollapse gs).getD a (Sum.inl false), (runCollapse gs).getD b (Sum.inl false) with
        | Sum.inl false, _ => Sum.inl false
        | _, Sum.inl false => Sum.inl false
        | Sum.inl true, v => v
        | u, Sum.inl true => u
        | Sum.inr _, Sum.inr _ => Sum.inr (9 + j)
      | .or, [a, b] =>
        match (runCollapse gs).getD a (Sum.inl false), (runCollapse gs).getD b (Sum.inl false) with
        | Sum.inl true, _ => Sum.inl true
        | _, Sum.inl true => Sum.inl true
        | Sum.inl false, v => v
        | u, Sum.inl false => u
        | Sum.inr _, Sum.inr _ => Sum.inr (9 + j)
      | _, _ => Sum.inl false := by
  have hsplit : gs = gs.take j ++ [gs[j]'hj] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j]'hj :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  set mPre := runCollapse (gs.take j)
  have hmPre_len : mPre.length = 9 + j := by
    rw [runCollapse_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hm_eq : runCollapse gs = (gs.drop (j + 1)).foldl (fun m g => m ++ [stepCollapse m g])
      (mPre ++ [stepCollapse mPre (gs[j]'hj)]) := by
    unfold runCollapse
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append]
    rfl
  have hm_at : (runCollapse gs).getD (9 + j) (Sum.inl false) = stepCollapse mPre (gs[j]'hj) := by
    rw [hm_eq, runCollapse_prefix (gs.drop (j + 1)) _ (by simp [hmPre_len])]
    rw [← hmPre_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
    simp
  have hm_pre : ∀ i < 9 + j, (runCollapse gs).getD i (Sum.inl false) = mPre.getD i (Sum.inl false) := by
    intro i hi
    rw [hm_eq, runCollapse_prefix (gs.drop (j + 1)) _ (by simp [hmPre_len]; omega)]
    rw [List.getD_eq_getElem _ _ (by simp [hmPre_len]; omega),
      List.getD_eq_getElem _ _ (by rw [hmPre_len]; exact hi),
      List.getElem_append_left (by rw [hmPre_len]; exact hi)]
  rw [hm_at]
  unfold stepCollapse
  rw [hmPre_len]
  cases hop : (gs[j]'hj).op <;> cases hins : (gs[j]'hj).inputs with
  | nil => rfl
  | cons a tl =>
    cases tl with
    | nil =>
      have ha : a < 9 + j := hrb a (by rw [hins]; exact List.mem_cons_self)
      dsimp only
      try rw [hm_pre a ha]
      try rfl
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        have ha : a < 9 + j := hrb a (by rw [hins]; exact List.mem_cons_self)
        have hb : b < 9 + j := hrb b (by rw [hins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        dsimp only
        try rw [hm_pre a ha]
        try rw [hm_pre b hb]
        try rfl
      | cons _ _ => rfl

lemma getElem_zero_of_head? {α : Type*} {l : List α} {x : α} (h : l.head? = some x)
    (hlt : 0 < l.length) : l[0]'hlt = x := by
  cases l with
  | nil => simp at h
  | cons a tl => simp at h; exact h

lemma getElem_one_of_tail_head? {α : Type*} {l : List α} {x : α} (h : l.tail.head? = some x)
    (hlt : 1 < l.length) : l[1]'hlt = x := by
  cases l with
  | nil => simp at h
  | cons a tl =>
    cases tl with
    | nil => simp at h
    | cons b tl2 => simp at h; exact h

def effIn (gs : List Gate) (M : List (Bool ⊕ ℕ)) (w : ℕ) : List ℕ :=
  if h : 9 ≤ w ∧ w < 9 + gs.length then
    let j := w - 9
    let g := gs[j]'(by omega)
    match g.op, g.inputs with
    | .not, [a] =>
      match M.getD a (Sum.inl false) with
      | Sum.inr u => [u]
      | _ => []
    | .and, [a, b] =>
      match M.getD a (Sum.inl false), M.getD b (Sum.inl false) with
      | Sum.inr u, Sum.inr v => [u, v]
      | _, _ => []
    | .or, [a, b] =>
      match M.getD a (Sum.inl false), M.getD b (Sum.inl false) with
      | Sum.inr u, Sum.inr v => [u, v]
      | _, _ => []
    | _, _ => []
  else []

def reach (gs : List Gate) (M : List (Bool ⊕ ℕ)) (w : ℕ) : Finset (Fin gs.length) :=
  if h : 9 ≤ w ∧ w < 9 + gs.length then
    insert ⟨w - 9, by omega⟩ ((effIn gs M w).foldr (fun u acc =>
      if _ : u < w then reach gs M u ∪ acc else acc) ∅)
  else ∅

def deps (gs : List Gate) (M : List (Bool ⊕ ℕ)) (w : ℕ) : Finset (Fin 8) :=
  if h1 : 1 ≤ w ∧ w < 9 then {⟨w - 1, by omega⟩}
  else if h2 : 9 ≤ w ∧ w < 9 + gs.length then
    (effIn gs M w).foldr (fun u acc => if _ : u < w then deps gs M u ∪ acc else acc) ∅
  else ∅

end PEqualNP.Outside.L_meta_27677

theorem PEqualNP.Outside.L_meta_27677 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩)) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_27677 in
  rintro ⟨C, hfan, hsize, heval, hout, hnf, hdist, hused, hg0, hg1⟩
  set gs := C.gates
  set m := gs.length
  have hm_le : m ≤ 11 := hsize
  have hout' : C.output + 1 = 9 + m := hout
  have hrb : ∀ j (hj : j < m), ∀ i ∈ (gs[j]'hj).inputs, i < 9 + j := by
    intro j hj i hi
    rcases hnf ⟨j, hj⟩ with ⟨_, a, ha, hins⟩ | ⟨_, a, b, hab, hb, hins⟩
    · simp only [List.get_eq_getElem] at hins
      rw [hins] at hi; simp at hi; subst hi; exact ha
    · simp only [List.get_eq_getElem] at hins
      dsimp only at hb
      rw [hins] at hi; simp at hi
      rcases hi with rfl | rfl <;> omega
  let M := runCollapse gs
  have hM_init : M.getD 0 (Sum.inl false) = Sum.inl true ∧
      ∀ i < 8, M.getD (i + 1) (Sum.inl false) = Sum.inr (i + 1) :=
    runCollapse_init_getD gs
  have hM_at : ∀ (j : ℕ) (hj : j < m),
      M.getD (9 + j) (Sum.inl false) =
        match (gs[j]'hj).op, (gs[j]'hj).inputs with
        | .not, [a] =>
          match M.getD a (Sum.inl false) with
          | Sum.inl b => Sum.inl (!b)
          | Sum.inr _ => Sum.inr (9 + j)
        | .and, [a, b] =>
          match M.getD a (Sum.inl false), M.getD b (Sum.inl false) with
          | Sum.inl false, _ => Sum.inl false
          | _, Sum.inl false => Sum.inl false
          | Sum.inl true, v => v
          | u, Sum.inl true => u
          | Sum.inr _, Sum.inr _ => Sum.inr (9 + j)
        | .or, [a, b] =>
          match M.getD a (Sum.inl false), M.getD b (Sum.inl false) with
          | Sum.inl true, _ => Sum.inl true
          | _, Sum.inl true => Sum.inl true
          | Sum.inl false, v => v
          | u, Sum.inl false => u
          | Sum.inr _, Sum.inr _ => Sum.inr (9 + j)
        | _, _ => Sum.inl false := fun j hj => runCollapse_at gs j hj (hrb j hj)
  let F : ℕ → (Fin 8 → Bool) → Bool := fun w y =>
    (evalGateWires gs (List.ofFn (extTrue y))).getD w false
  have hF_in0 : ∀ y, F 0 y = true := by
    intro y
    dsimp only [F]
    rw [evalGateWires_prefix gs _ (by simp)]
    simp [extTrue]
  have hF_in : ∀ i (hi : i < 8) (y : Fin 8 → Bool), F (i + 1) y = y ⟨i, hi⟩ := by
    intro i hi y
    dsimp only [F]
    rw [evalGateWires_prefix gs _ (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    simp [extTrue]
  have hM_sound : ∀ w < 9 + m,
      (∀ b, M.getD w (Sum.inl false) = Sum.inl b → ∀ y, F w y = b) ∧
      (∀ u, M.getD w (Sum.inl false) = Sum.inr u →
        1 ≤ u ∧ u ≤ w ∧ M.getD u (Sum.inl false) = Sum.inr u ∧ ∀ y, F w y = F u y) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hw0 : w = 0
      · subst hw0
        rw [hM_init.1]
        exact ⟨fun b hb y => by cases hb; exact hF_in0 y, fun u hu => by cases hu⟩
      · by_cases hw9 : w < 9
        · have h1 := hM_init.2 (w - 1) (by omega)
          have hsub : w - 1 + 1 = w := by omega
          rw [hsub] at h1
          rw [h1]
          refine ⟨(fun b hb => by cases hb), fun u hu => ?_⟩
          cases hu
          exact ⟨by omega, le_refl _, h1, fun _ => rfl⟩
        · set j := w - 9
          have hj : j < m := by omega
          have hwj : w = 9 + j := by omega
          have hMat := hM_at j hj
          have hFat : ∀ y, F (9 + j) y =
              (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => F i y) := by
            intro y
            have h := evalGateWires_at gs (List.ofFn (extTrue y)) j hj
              (by rw [List.length_ofFn]; exact hrb j hj)
            rw [List.length_ofFn] at h
            exact h
          rw [hwj]
          rcases hnf ⟨j, hj⟩ with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
          · simp only [List.get_eq_getElem] at hop hins
            dsimp only at ha
            have iha := ih a (by omega) (by omega)
            rw [hop, hins] at hMat; dsimp only at hMat
            cases hMa : M.getD a (Sum.inl false) with
            | inl bv =>
              rw [hMa] at hMat
              rw [hMat]
              refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
              cases hb'
              rw [hFat y, hop, hins]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
              rw [iha.1 bv hMa y]
            | inr ua =>
              rw [hMa] at hMat
              rw [hMat]
              refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
              cases hu
              exact ⟨by omega, le_refl _, hMat, fun _ => rfl⟩
          · simp only [List.get_eq_getElem] at hop hins
            dsimp only at hb
            have iha := ih a (by omega) (by omega)
            have ihb := ih b (by omega) (by omega)
            rcases hop with hop | hop
            · rw [hop, hins] at hMat; dsimp only at hMat
              cases hMa : M.getD a (Sum.inl false) with
              | inl ba =>
                cases ba
                · rw [hMa] at hMat; rw [hMat]
                  refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                  cases hb'; rw [hFat y, hop, hins]
                  simp [GateOp.eval, iha.1 false hMa y]
                · cases hMb : M.getD b (Sum.inl false) with
                  | inl bb =>
                    rw [hMa, hMb] at hMat; rw [hMat]
                    cases bb
                    · refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                      cases hb'; rw [hFat y, hop, hins]
                      simp [GateOp.eval, ihb.1 false hMb y]
                    · refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                      cases hb'; rw [hFat y, hop, hins]
                      simp [GateOp.eval, iha.1 true hMa y, ihb.1 true hMb y]
                  | inr ub =>
                    rw [hMa, hMb] at hMat; rw [hMat]
                    have hbu := ihb.2 ub hMb
                    refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                    cases hu
                    refine ⟨hbu.1, by omega, hbu.2.2.1, fun y => ?_⟩
                    rw [hFat y, hop, hins]
                    simp [GateOp.eval, iha.1 true hMa y, hbu.2.2.2 y]
              | inr ua =>
                cases hMb : M.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · rw [hMa, hMb] at hMat; rw [hMat]
                    refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                    cases hb'; rw [hFat y, hop, hins]
                    simp [GateOp.eval, ihb.1 false hMb y]
                  · rw [hMa, hMb] at hMat; rw [hMat]
                    have hau := iha.2 ua hMa
                    refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                    cases hu
                    refine ⟨hau.1, by omega, hau.2.2.1, fun y => ?_⟩
                    rw [hFat y, hop, hins]
                    simp [GateOp.eval, ihb.1 true hMb y, hau.2.2.2 y]
                | inr ub =>
                  rw [hMa, hMb] at hMat; rw [hMat]
                  refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                  cases hu
                  exact ⟨by omega, le_refl _, hMat, fun _ => rfl⟩
            · rw [hop, hins] at hMat; dsimp only at hMat
              cases hMa : M.getD a (Sum.inl false) with
              | inl ba =>
                cases ba
                · cases hMb : M.getD b (Sum.inl false) with
                  | inl bb =>
                    rw [hMa, hMb] at hMat; rw [hMat]
                    cases bb
                    · refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                      cases hb'; rw [hFat y, hop, hins]
                      simp [GateOp.eval, iha.1 false hMa y, ihb.1 false hMb y]
                    · refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                      cases hb'; rw [hFat y, hop, hins]
                      simp [GateOp.eval, ihb.1 true hMb y]
                  | inr ub =>
                    rw [hMa, hMb] at hMat; rw [hMat]
                    have hbu := ihb.2 ub hMb
                    refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                    cases hu
                    refine ⟨hbu.1, by omega, hbu.2.2.1, fun y => ?_⟩
                    rw [hFat y, hop, hins]
                    simp [GateOp.eval, iha.1 false hMa y, hbu.2.2.2 y]
                · rw [hMa] at hMat; rw [hMat]
                  refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                  cases hb'; rw [hFat y, hop, hins]
                  simp [GateOp.eval, iha.1 true hMa y]
              | inr ua =>
                cases hMb : M.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb
                  · rw [hMa, hMb] at hMat; rw [hMat]
                    have hau := iha.2 ua hMa
                    refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                    cases hu
                    refine ⟨hau.1, by omega, hau.2.2.1, fun y => ?_⟩
                    rw [hFat y, hop, hins]
                    simp [GateOp.eval, ihb.1 false hMb y, hau.2.2.2 y]
                  · rw [hMa, hMb] at hMat; rw [hMat]
                    refine ⟨fun b' hb' y => ?_, (fun u hu => by cases hu)⟩
                    cases hb'; rw [hFat y, hop, hins]
                    simp [GateOp.eval, ihb.1 true hMb y]
                | inr ub =>
                  rw [hMa, hMb] at hMat; rw [hMat]
                  refine ⟨(fun b' hb' => by cases hb'), fun u hu => ?_⟩
                  cases hu
                  exact ⟨by omega, le_refl _, hMat, fun _ => rfl⟩
  have hF_out : ∀ y, F C.output y = f1 y := by
    intro y
    exact heval (extTrue y)
  have hm_ge2 : 2 ≤ m := by
    cases hgs : C.gates with
    | nil => simp [gs, hgs] at hg0
    | cons g0 tl =>
      cases tl with
      | nil => simp [gs, hgs] at hg1
      | cons g1 tl2 => simp [m, gs, hgs]
  have hgs0 : gs[0]'(by omega) = ⟨GateOp.or, [0, 1]⟩ :=
    getElem_zero_of_head? hg0 (by omega)
  have hgs1 : gs[1]'(by omega) = ⟨GateOp.or, [0, 4]⟩ :=
    getElem_one_of_tail_head? hg1 (by omega)
  have hM9 : M.getD 9 (Sum.inl false) = Sum.inl true := by
    have h := hM_at 0 (by omega)
    rw [hgs0] at h; dsimp only at h; rw [hM_init.1] at h
    exact h
  have hM10 : M.getD 10 (Sum.inl false) = Sum.inl true := by
    have h := hM_at 1 (by omega)
    rw [hgs1] at h; dsimp only at h; rw [hM_init.1] at h
    exact h
  have hnot_const_out : ∀ b, M.getD C.output (Sum.inl false) ≠ Sum.inl b := by
    intro b hb
    have hlt : C.output < 9 + m := by omega
    have h0 := (hM_sound C.output hlt).1 b hb (fun _ => false)
    have h1 := (hM_sound C.output hlt).1 b hb (fun _ => true)
    rw [hF_out, f1_nonconst.1] at h0
    rw [hF_out, f1_nonconst.2] at h1
    rw [← h0] at h1; cases h1
  have hcol_if_const_in : ∀ (k : Fin m) (a : ℕ), a ∈ (gs[k.val]'k.isLt).inputs →
      (∃ b, M.getD a (Sum.inl false) = Sum.inl b) →
      M.getD (9 + k.val) (Sum.inl false) ≠ Sum.inr (9 + k.val) := by
    intro k a ha ⟨bv, hbv⟩ hkept
    have hMat := hM_at k.val k.isLt
    rcases hnf k with ⟨hop, x, hx, hins⟩ | ⟨hop, x, y, hxy, hy, hins⟩
    · simp only [List.get_eq_getElem] at hop hins
      rw [hins] at ha; simp at ha; subst ha
      rw [hop, hins] at hMat; dsimp only at hMat; rw [hbv] at hMat
      rw [hMat] at hkept; cases hkept
    · simp only [List.get_eq_getElem] at hop hins
      rw [hins] at ha; simp at ha
      rcases hop with hop | hop
      · rw [hop, hins] at hMat; dsimp only at hMat
        rcases ha with rfl | rfl
        · rw [hbv] at hMat
          cases bv
          · rw [hMat] at hkept; cases hkept
          · cases hMy : M.getD y (Sum.inl false) with
            | inl byv => cases byv <;> (rw [hMy] at hMat; rw [hMat] at hkept; cases hkept)
            | inr uy =>
              rw [hMy] at hMat; rw [hMat] at hkept
              have hle := (hM_sound y (by omega)).2 uy hMy
              cases hkept; omega
        · rw [hbv] at hMat
          cases bv
          · cases hMx : M.getD x (Sum.inl false) with
            | inl bxv => cases bxv <;> (rw [hMx] at hMat; rw [hMat] at hkept; cases hkept)
            | inr ux => rw [hMx] at hMat; rw [hMat] at hkept; cases hkept
          · cases hMx : M.getD x (Sum.inl false) with
            | inl bxv => cases bxv <;> (rw [hMx] at hMat; rw [hMat] at hkept; cases hkept)
            | inr ux =>
              rw [hMx] at hMat; rw [hMat] at hkept
              have hle := (hM_sound x (by omega)).2 ux hMx
              cases hkept; omega
      · rw [hop, hins] at hMat; dsimp only at hMat
        rcases ha with rfl | rfl
        · rw [hbv] at hMat
          cases bv
          · cases hMy : M.getD y (Sum.inl false) with
            | inl byv => cases byv <;> (rw [hMy] at hMat; rw [hMat] at hkept; cases hkept)
            | inr uy =>
              rw [hMy] at hMat; rw [hMat] at hkept
              have hle := (hM_sound y (by omega)).2 uy hMy
              cases hkept; omega
          · rw [hMat] at hkept; cases hkept
        · rw [hbv] at hMat
          cases bv
          · cases hMx : M.getD x (Sum.inl false) with
            | inl bxv => cases bxv <;> (rw [hMx] at hMat; rw [hMat] at hkept; cases hkept)
            | inr ux =>
              rw [hMx] at hMat; rw [hMat] at hkept
              have hle := (hM_sound x (by omega)).2 ux hMx
              cases hkept; omega
          · cases hMx : M.getD x (Sum.inl false) with
            | inl bxv => cases bxv <;> (rw [hMx] at hMat; rw [hMat] at hkept; cases hkept)
            | inr ux => rw [hMx] at hMat; rw [hMat] at hkept; cases hkept
  let KEPT : Finset (Fin m) :=
    Finset.univ.filter (fun j : Fin m => M.getD (9 + j.val) (Sum.inl false) = Sum.inr (9 + j.val))
  have hm_ge3 : 3 ≤ m := by
    by_contra hlt
    have hm2 : m = 2 := by omega
    have hout10 : C.output = 10 := by omega
    rw [hout10] at hnot_const_out
    exact hnot_const_out true hM10
  have hkept_le7 : KEPT.card ≤ 7 := by
    have hnot0 : (⟨0, by omega⟩ : Fin m) ∉ KEPT := by
      simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and, Nat.add_zero]
      rw [hM9]; intro h; cases h
    have hnot1 : (⟨1, by omega⟩ : Fin m) ∉ KEPT := by
      simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hM10]; intro h; cases h
    rcases hused ⟨0, by omega⟩ (by dsimp; omega) with ⟨k0, hk0_gt, hk0_in⟩
    rcases hused ⟨1, by omega⟩ (by dsimp; omega) with ⟨k1, hk1_gt, hk1_in⟩
    dsimp only at hk0_gt hk1_gt
    have hk0_ge2 : 2 ≤ k0.val := by
      by_contra hlt
      have hk0_1 : k0.val = 1 := by omega
      simp only [List.get_eq_getElem] at hk0_in
      have h1 : gs[k0.val]'k0.isLt = ⟨GateOp.or, [0, 4]⟩ := by
        simpa [hk0_1] using hgs1
      rw [h1] at hk0_in
      simp at hk0_in
    have hnot_k0 : k0 ∉ KEPT := by
      simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcol_if_const_in k0 9 (by simpa [List.get_eq_getElem] using hk0_in) ⟨true, hM9⟩
    have hnot_k1 : k1 ∉ KEPT := by
      simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcol_if_const_in k1 10 (by simpa [List.get_eq_getElem] using hk1_in) ⟨true, hM10⟩
    have hcard_compl : 4 ≤ KEPTᶜ.card := by
      by_cases hne : k0 ≠ k1
      · have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩, k0, k1} : Finset (Fin m)) ⊆ KEPTᶜ := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_compl]
          rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({⟨0, by omega⟩, ⟨1, by omega⟩, k0, k1} : Finset (Fin m)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hne]
          · simp [Fin.ext_iff]; exact ⟨by omega, by omega⟩
          · simp [Fin.ext_iff]; exact ⟨by omega, by omega⟩
        exact h4 ▸ Finset.card_le_card hsub
      · push Not at hne
        subst hne
        have hMk0_const : ∃ b, M.getD (9 + k0.val) (Sum.inl false) = Sum.inl b := by
          have hMat := hM_at k0.val k0.isLt
          rcases hnf k0 with ⟨hop, a, _, hins⟩ | ⟨hop, a, b, hab, _, hins⟩
          · simp only [List.get_eq_getElem] at hins hk0_in hk1_in
            rw [hins] at hk0_in hk1_in
            simp at hk0_in hk1_in; omega
          · simp only [List.get_eq_getElem] at hop hins hk0_in hk1_in
            rw [hins] at hk0_in hk1_in
            simp at hk0_in hk1_in
            have ha9 : a = 9 := by omega
            have hb10 : b = 10 := by omega
            subst ha9 hb10
            rcases hop with hop | hop
            · rw [hop, hins] at hMat; dsimp only at hMat; rw [hM9, hM10] at hMat; exact ⟨true, hMat⟩
            · rw [hop, hins] at hMat; dsimp only at hMat; rw [hM9, hM10] at hMat; exact ⟨true, hMat⟩
        rcases hMk0_const with ⟨b0, hb0⟩
        have hk0_lt : k0.val + 1 < m := by
          by_contra hge
          have hlast : 9 + k0.val = C.output := by omega
          rw [hlast] at hb0
          exact hnot_const_out b0 hb0
        rcases hused k0 hk0_lt with ⟨k2, hk2_gt, hk2_in⟩
        have hnot_k2 : k2 ∉ KEPT := by
          simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcol_if_const_in k2 (9 + k0.val)
            (by simpa [List.get_eq_getElem] using hk2_in) ⟨b0, hb0⟩
        have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩, k0, k2} : Finset (Fin m)) ⊆ KEPTᶜ := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_compl]
          rcases hx with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({⟨0, by omega⟩, ⟨1, by omega⟩, k0, k2} : Finset (Fin m)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [Fin.ext_iff]; omega
          · simp [Fin.ext_iff]; exact ⟨by omega, by omega⟩
          · simp [Fin.ext_iff]; exact ⟨by omega, by omega⟩
        exact h4 ▸ Finset.card_le_card hsub
    have hsum := Finset.card_add_card_compl KEPT
    rw [Fintype.card_fin] at hsum
    omega
  let eff := effIn gs M
  have heff_kept : ∀ j : Fin m, j ∈ KEPT →
      ((gs[j.val]'j.isLt).op = .not ∧ ∃ u, eff (9 + j.val) = [u] ∧ 1 ≤ u ∧ u < 9 + j.val ∧
        M.getD u (Sum.inl false) = Sum.inr u ∧ ∀ y, F (9 + j.val) y = !(F u y)) ∨
      (((gs[j.val]'j.isLt).op = .and ∨ (gs[j.val]'j.isLt).op = .or) ∧
        ∃ u v, eff (9 + j.val) = [u, v] ∧ 1 ≤ u ∧ u < 9 + j.val ∧ 1 ≤ v ∧ v < 9 + j.val ∧
        M.getD u (Sum.inl false) = Sum.inr u ∧ M.getD v (Sum.inl false) = Sum.inr v ∧
        ∀ y, F (9 + j.val) y = (gs[j.val]'j.isLt).op.eval [F u y, F v y]) := by
    intro j hj
    simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hMat := hM_at j.val j.isLt
    have hFat : ∀ y, F (9 + j.val) y =
        (gs[j.val]'j.isLt).op.eval ((gs[j.val]'j.isLt).inputs.map fun i => F i y) := by
      intro y
      have h := evalGateWires_at gs (List.ofFn (extTrue y)) j.val j.isLt
        (by rw [List.length_ofFn]; exact hrb j.val j.isLt)
      rw [List.length_ofFn] at h; exact h
    rcases hnf j with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
    · simp only [List.get_eq_getElem] at hop hins
      left
      cases hMa : M.getD a (Sum.inl false) with
      | inl bv =>
        rw [hop, hins] at hMat; dsimp only at hMat; rw [hMa] at hMat; rw [hMat] at hj; cases hj
      | inr u =>
        have hu := (hM_sound a (by omega)).2 u hMa
        refine ⟨hop, u, ?_, hu.1, by omega, hu.2.2.1, fun y => ?_⟩
        · dsimp only [eff, effIn]
          split_ifs
          · simp only [Nat.add_sub_cancel_left, hop, hins, hMa]
          · omega
        · rw [hFat y, hop, hins]; simp [GateOp.eval, hu.2.2.2 y]
    · simp only [List.get_eq_getElem] at hop hins
      right
      cases hMa : M.getD a (Sum.inl false) with
      | inl ba =>
        exfalso
        exact hcol_if_const_in j a (by rw [hins]; exact List.mem_cons_self) ⟨ba, hMa⟩ hj
      | inr u =>
        cases hMb : M.getD b (Sum.inl false) with
        | inl bb =>
          exfalso
          exact hcol_if_const_in j b (by rw [hins]; exact List.mem_cons_of_mem _ List.mem_cons_self) ⟨bb, hMb⟩ hj
        | inr v =>
          have hu := (hM_sound a (by omega)).2 u hMa
          have hv := (hM_sound b (by omega)).2 v hMb
          refine ⟨hop, u, v, ?_, hu.1, by omega, hv.1, by omega, hu.2.2.1, hv.2.2.1, fun y => ?_⟩
          · dsimp only [eff, effIn]
            split_ifs
            · rcases hop with hop | hop <;>
                simp only [Nat.add_sub_cancel_left, hop, hins, hMa, hMb]
            · omega
          · rw [hFat y, hins]; simp [hu.2.2.2 y, hv.2.2.2 y]
  have heff_lt : ∀ w, ∀ u ∈ eff w, u < w := by
    intro w u hu
    dsimp only [eff, effIn] at hu
    split_ifs at hu with hcond
    · have hj : w - 9 < m := by omega
      rcases hnf ⟨w - 9, hj⟩ with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
      · simp only [List.get_eq_getElem] at hop hins
        dsimp only at ha
        simp only [hop, hins] at hu
        cases hMa : M.getD a (Sum.inl false) with
        | inl _ => rw [hMa] at hu; cases hu
        | inr u' =>
          rw [hMa] at hu
          simp only [List.mem_singleton] at hu
          subst hu
          have := (hM_sound a (by omega)).2 u hMa
          omega
      · simp only [List.get_eq_getElem] at hop hins
        dsimp only at hb
        rcases hop with hop | hop <;>
        · simp only [hop, hins] at hu
          cases hMa : M.getD a (Sum.inl false) with
          | inl _ => rw [hMa] at hu; cases hu
          | inr u' =>
            cases hMb : M.getD b (Sum.inl false) with
            | inl _ => rw [hMa, hMb] at hu; cases hu
            | inr v' =>
              rw [hMa, hMb] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · have := (hM_sound a (by omega)).2 u hMa; omega
              · have := (hM_sound b (by omega)).2 u hMb; omega
    · cases hu
  have hreach_unfold : ∀ j : Fin m,
      reach gs M (9 + j.val) = insert j ((eff (9 + j.val)).foldr (fun u acc => reach gs M u ∪ acc) ∅) := by
    intro j
    rw [reach]
    split_ifs
    · have hj_eq : (⟨9 + j.val - 9, by omega⟩ : Fin gs.length) = j := by ext; simp
      rw [hj_eq]
      congr 1
      have hfold : ∀ l : List ℕ, (∀ u ∈ l, u < 9 + j.val) →
          l.foldr (fun u acc => if _ : u < 9 + j.val then reach gs M u ∪ acc else acc) ∅ =
          l.foldr (fun u acc => reach gs M u ∪ acc) ∅ := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a tl ih =>
          simp only [List.foldr_cons, hl a List.mem_cons_self, ↓reduceDIte]
          rw [ih (fun u hu => hl u (List.mem_cons_of_mem a hu))]
      exact hfold (eff (9 + j.val)) (heff_lt (9 + j.val))
    · omega
  have hreach_in : ∀ w < 9, reach gs M w = ∅ := by
    intro w hw
    rw [reach]
    split_ifs
    · omega
    · rfl
  have hdeps_in : ∀ w, (h1 : 1 ≤ w) → (h2 : w < 9) → deps gs M w = {⟨w - 1, by omega⟩} := by
    intro w h1 h2
    rw [deps]
    split_ifs
    · rfl
    · omega
    · omega
  have hdeps_gate : ∀ j : Fin m,
      deps gs M (9 + j.val) = (eff (9 + j.val)).foldr (fun u acc => deps gs M u ∪ acc) ∅ := by
    intro j
    rw [deps]
    split_ifs
    · omega
    · have hfold : ∀ l : List ℕ, (∀ u ∈ l, u < 9 + j.val) →
          l.foldr (fun u acc => if _ : u < 9 + j.val then deps gs M u ∪ acc else acc) ∅ =
          l.foldr (fun u acc => deps gs M u ∪ acc) ∅ := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a tl ih =>
          simp only [List.foldr_cons, hl a List.mem_cons_self, ↓reduceDIte]
          rw [ih (fun u hu => hl u (List.mem_cons_of_mem a hu))]
      exact hfold (eff (9 + j.val)) (heff_lt (9 + j.val))
    · omega
  have hwire_props : ∀ w, 1 ≤ w → w < 9 + m → M.getD w (Sum.inl false) = Sum.inr w →
      (reach gs M w ⊆ KEPT) ∧
      (∀ j ∈ reach gs M w, 9 + j.val ≤ w) ∧
      (deps gs M w).Nonempty ∧
      (∀ y1 y2, (∀ i ∈ deps gs M w, y1 i = y2 i) → F w y1 = F w y2) ∧
      (∀ j ∈ reach gs M w, 9 + j.val ≠ w → ∃ k ∈ reach gs M w, 9 + j.val ∈ eff (9 + k.val)) ∧
      (∀ i ∈ deps gs M w, w = i.val + 1 ∨ ∃ k ∈ reach gs M w, i.val + 1 ∈ eff (9 + k.val)) ∧
      ((∀ j ∈ reach gs M w, (gs[j.val]'j.isLt).op ≠ .not) →
        ∀ y1 y2, (∀ i, y1 i = true → y2 i = true) → F w y1 = true → F w y2 = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw1 hwm hMw
      by_cases hw9 : w < 9
      · rw [hreach_in w hw9, hdeps_in w hw1 hw9]
        refine ⟨Finset.empty_subset _, fun j hj => by simp at hj,
          ⟨⟨w - 1, by omega⟩, by simp⟩, ?_, fun j hj => by simp at hj, ?_, ?_⟩
        · intro y1 y2 hy
          have hsub : w - 1 + 1 = w := by omega
          rw [← hsub, hF_in (w - 1) (by omega), hF_in (w - 1) (by omega)]
          exact hy ⟨w - 1, by omega⟩ (by simp)
        · intro i hi
          simp only [Finset.mem_singleton] at hi
          subst hi
          left; dsimp; omega
        · intro _ y1 y2 hle hy1
          have hsub : w - 1 + 1 = w := by omega
          rw [← hsub, hF_in (w - 1) (by omega)] at hy1 ⊢
          exact hle ⟨w - 1, by omega⟩ hy1
      · set j : Fin m := ⟨w - 9, by omega⟩
        have hwj : w = 9 + j.val := by simp [j]; omega
        have hjK : j ∈ KEPT := by
          simp only [KEPT, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hwj]; exact hMw
        rw [hwj]
        rcases heff_kept j hjK with ⟨hop, u, heff, hu1, hult, hMu, hFu⟩ |
            ⟨hop, u, v, heff, hu1, hult, hv1, hvlt, hMu, hMv, hFuv⟩
        · have ihu := ih u (by omega) hu1 (by omega) hMu
          rw [hreach_unfold j, hdeps_gate j, heff]
          simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
          refine ⟨Finset.insert_subset hjK ihu.1, ?_, ihu.2.2.1, ?_, ?_, ?_, ?_⟩
          · intro j' hj'
            rcases Finset.mem_insert.mp hj' with rfl | hj'
            · exact le_refl _
            · exact Nat.le_trans (ihu.2.1 j' hj') (Nat.le_of_lt hult)
          · intro y1 y2 hy
            rw [hFu y1, hFu y2, ihu.2.2.2.1 y1 y2 hy]
          · intro j' hj' hne
            rcases Finset.mem_insert.mp hj' with rfl | hj'
            · exact (hne rfl).elim
            · by_cases hju : 9 + j'.val = u
              · exact ⟨j, Finset.mem_insert_self j _, by rw [heff, hju]; exact List.mem_cons_self⟩
              · rcases ihu.2.2.2.2.1 j' hj' hju with ⟨k, hk, hkin⟩
                exact ⟨k, Finset.mem_insert_of_mem hk, hkin⟩
          · intro i hi
            right
            rcases ihu.2.2.2.2.2.1 i hi with heq | ⟨k, hk, hkin⟩
            · exact ⟨j, Finset.mem_insert_self j _, by rw [heff, ← heq]; exact List.mem_cons_self⟩
            · exact ⟨k, Finset.mem_insert_of_mem hk, hkin⟩
          · intro hnoNot
            exfalso
            exact hnoNot j (Finset.mem_insert_self j _) hop
        · have ihu := ih u (by omega) hu1 (by omega) hMu
          have ihv := ih v (by omega) hv1 (by omega) hMv
          rw [hreach_unfold j, hdeps_gate j, heff]
          simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
          refine ⟨Finset.insert_subset hjK (Finset.union_subset ihu.1 ihv.1), ?_,
            ihu.2.2.1.mono Finset.subset_union_left, ?_, ?_, ?_, ?_⟩
          · intro j' hj'
            rcases Finset.mem_insert.mp hj' with rfl | hj'
            · exact le_refl _
            · rcases Finset.mem_union.mp hj' with hj' | hj'
              · exact Nat.le_trans (ihu.2.1 j' hj') (Nat.le_of_lt hult)
              · exact Nat.le_trans (ihv.2.1 j' hj') (Nat.le_of_lt hvlt)
          · intro y1 y2 hy
            rw [hFuv y1, hFuv y2,
              ihu.2.2.2.1 y1 y2 (fun i hi => hy i (Finset.mem_union_left _ hi)),
              ihv.2.2.2.1 y1 y2 (fun i hi => hy i (Finset.mem_union_right _ hi))]
          · intro j' hj' hne
            rcases Finset.mem_insert.mp hj' with rfl | hj'
            · exact (hne rfl).elim
            · rcases Finset.mem_union.mp hj' with hj' | hj'
              · by_cases hju : 9 + j'.val = u
                · exact ⟨j, Finset.mem_insert_self j _, by rw [heff, hju]; exact List.mem_cons_self⟩
                · rcases ihu.2.2.2.2.1 j' hj' hju with ⟨k, hk, hkin⟩
                  exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · by_cases hjv : 9 + j'.val = v
                · exact ⟨j, Finset.mem_insert_self j _,
                    by rw [heff, hjv]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
                · rcases ihv.2.2.2.2.1 j' hj' hjv with ⟨k, hk, hkin⟩
                  exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
          · intro i hi
            right
            rcases Finset.mem_union.mp hi with hi | hi
            · rcases ihu.2.2.2.2.2.1 i hi with heq | ⟨k, hk, hkin⟩
              · exact ⟨j, Finset.mem_insert_self j _, by rw [heff, ← heq]; exact List.mem_cons_self⟩
              · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
            · rcases ihv.2.2.2.2.2.1 i hi with heq | ⟨k, hk, hkin⟩
              · exact ⟨j, Finset.mem_insert_self j _,
                  by rw [heff, ← heq]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
              · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
          · intro hnoNot y1 y2 hle hy1
            have hmu := ihu.2.2.2.2.2.2 (fun k hk => hnoNot k (Finset.mem_insert_of_mem (Finset.mem_union_left _ hk))) y1 y2 hle
            have hmv := ihv.2.2.2.2.2.2 (fun k hk => hnoNot k (Finset.mem_insert_of_mem (Finset.mem_union_right _ hk))) y1 y2 hle
            rw [hFuv y1] at hy1
            rw [hFuv y2]
            rcases hop with hop | hop
            · rw [hop] at hy1 ⊢
              simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
                Bool.and_eq_true] at hy1 ⊢
              exact ⟨hmu hy1.1, hmv hy1.2⟩
            · rw [hop] at hy1 ⊢
              simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                Bool.or_eq_true] at hy1 ⊢
              rcases hy1 with h1 | h2
              · exact Or.inl (hmu h1)
              · exact Or.inr (hmv h2)
  have hMout_sum : ∃ r, M.getD C.output (Sum.inl false) = Sum.inr r := by
    cases h : M.getD C.output (Sum.inl false) with
    | inl b => exact (hnot_const_out b h).elim
    | inr r => exact ⟨r, rfl⟩
  rcases hMout_sum with ⟨r, hr⟩
  have hlt_out : C.output < 9 + m := by omega
  have hr_sound := (hM_sound C.output hlt_out).2 r hr
  have hFr : ∀ y, F r y = f1 y := fun y => by rw [← hr_sound.2.2.2 y, hF_out y]
  have hr_props := hwire_props r hr_sound.1 (by omega) hr_sound.2.2.1
  have hr_deps : deps gs M r = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hni
    rcases f1_essential i with ⟨y, hy⟩
    have hagree : ∀ j ∈ deps gs M r, Function.update y i false j = Function.update y i true j := by
      intro j hj
      have hne : j ≠ i := fun h => hni (h ▸ hj)
      simp [hne]
    have hEq := hr_props.2.2.2.1 _ _ hagree
    rw [hFr, hFr] at hEq
    exact hy hEq
  have hr_ge9 : 9 ≤ r := by
    by_contra hlt
    have hcard : (deps gs M r).card = 1 := by rw [hdeps_in r hr_sound.1 (by omega)]; simp
    rw [hr_deps, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  set jtop : Fin m := ⟨r - 9, by omega⟩
  have hr_eq : r = 9 + jtop.val := by simp [jtop]; omega
  have hjtop_mem : jtop ∈ reach gs M r := by
    rw [hr_eq, hreach_unfold jtop]; exact Finset.mem_insert_self _ _
  have hlist_count_sum : ∀ (l : List ℕ) (T : Finset ℕ), (∑ x ∈ T, l.count x) ≤ l.length := by
    intro l T
    induction l with
    | nil => simp
    | cons a tl ih =>
      simp only [List.count_cons, List.length_cons, beq_iff_eq, Finset.sum_add_distrib]
      have h1' : (∑ x ∈ T, if a = x then 1 else 0) ≤ 1 := by
        by_cases ha : a ∈ T
        · rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hba; simp [hba.symm]
          · intro h; exact (h ha).elim
        · rw [Finset.sum_eq_zero]
          · exact Nat.zero_le 1
          · intro b hb; have : a ≠ b := fun h => ha (h ▸ hb); simp [this]
      omega
  have hcount_bound : ∀ (w : ℕ), 1 ≤ w → w < 9 + m → M.getD w (Sum.inl false) = Sum.inr w →
      ∀ (S : Finset ℕ), (∀ x ∈ S, ∃ k ∈ reach gs M w, x ∈ eff (9 + k.val)) →
      S.card ≤ ∑ k ∈ reach gs M w, (eff (9 + k.val)).length := by
    intro w hw1 hwm hMw S hS
    have h1 : S.card ≤ ∑ x ∈ S, ∑ k ∈ reach gs M w, (eff (9 + k.val)).count x := by
      calc S.card = ∑ _x ∈ S, 1 := by simp
        _ ≤ ∑ x ∈ S, ∑ k ∈ reach gs M w, (eff (9 + k.val)).count x := by
            apply Finset.sum_le_sum
            intro x hx
            rcases hS x hx with ⟨k, hk, hkin⟩
            have hpos : 1 ≤ (eff (9 + k.val)).count x := by
              rw [Nat.succ_le_iff]; exact List.count_pos_iff.mpr hkin
            exact Nat.le_trans hpos
              (Finset.single_le_sum (f := fun k' => (eff (9 + k'.val)).count x)
                (fun _ _ => Nat.zero_le _) hk)
    have h2 : (∑ x ∈ S, ∑ k ∈ reach gs M w, (eff (9 + k.val)).count x) =
        ∑ k ∈ reach gs M w, ∑ x ∈ S, (eff (9 + k.val)).count x := Finset.sum_comm
    have h3 : (∑ k ∈ reach gs M w, ∑ x ∈ S, (eff (9 + k.val)).count x) ≤
        ∑ k ∈ reach gs M w, (eff (9 + k.val)).length :=
      Finset.sum_le_sum (fun k _ => hlist_count_sum (eff (9 + k.val)) S)
    omega
  set R := reach gs M r
  have hR_sub : R ⊆ KEPT := hr_props.1
  have hR_le7 : R.card ≤ 7 := Nat.le_trans (Finset.card_le_card hR_sub) hkept_le7
  set W_in : Finset ℕ := (Finset.univ : Finset (Fin 8)).image (fun i => i.val + 1)
  set W_g : Finset ℕ := (R.erase jtop).image (fun j => 9 + j.val)
  have hW_disj : Disjoint W_in W_g := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨j, _, hj⟩
    omega
  have hWin_card : W_in.card = 8 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by ext; omega), Finset.card_univ, Fintype.card_fin]
  have hWg_card : W_g.card = R.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by ext; omega), Finset.card_erase_of_mem hjtop_mem]
  have hW_read : ∀ x ∈ W_in ∪ W_g, ∃ k ∈ R, x ∈ eff (9 + k.val) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      have hi : i ∈ deps gs M r := by rw [hr_deps]; exact Finset.mem_univ i
      rcases hr_props.2.2.2.2.2.1 i hi with heq | ⟨k, hk, hkin⟩
      · omega
      · exact ⟨k, hk, hkin⟩
    · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      have hne : 9 + j.val ≠ r := by
        have := (Finset.mem_erase.mp hj).1
        intro h; apply this; ext; omega
      exact hr_props.2.2.2.2.1 j (Finset.mem_erase.mp hj).2 hne
  have hR_len_le : ∀ k ∈ R, (eff (9 + k.val)).length ≤ 2 := by
    intro k hk
    rcases heff_kept k (hR_sub hk) with ⟨_, u, heff, _⟩ | ⟨_, u, v, heff, _⟩ <;> rw [heff] <;> simp
  have hsum_le : (∑ k ∈ R, (eff (9 + k.val)).length) ≤ 2 * R.card := by
    calc (∑ k ∈ R, (eff (9 + k.val)).length) ≤ ∑ _k ∈ R, 2 := Finset.sum_le_sum hR_len_le
      _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hW_card : (W_in ∪ W_g).card = 8 + (R.card - 1) := by
    rw [Finset.card_union_of_disjoint hW_disj, hWin_card, hWg_card]
  have hcnt : (W_in ∪ W_g).card ≤ ∑ k ∈ R, (eff (9 + k.val)).length :=
    hcount_bound r hr_sound.1 (by omega) hr_sound.2.2.1 (W_in ∪ W_g) hW_read
  have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨jtop, hjtop_mem⟩
  have hR_eq7 : R.card = 7 := by omega
  have hsum_eq14 : (∑ k ∈ R, (eff (9 + k.val)).length) = 14 := by omega
  have hnoNot : ∀ k ∈ R, (gs[k.val]'k.isLt).op ≠ .not := by
    intro k hk hnot
    have hk_len1 : (eff (9 + k.val)).length = 1 := by
      rcases heff_kept k (hR_sub hk) with ⟨_, u, heff, _⟩ | ⟨hop, _⟩
      · rw [heff]; rfl
      · rcases hop with h | h <;> rw [h] at hnot <;> cases hnot
    have hlt_sum : (∑ k' ∈ R, (eff (9 + k'.val)).length) < 2 * R.card := by
      rw [← Finset.add_sum_erase _ _ hk]
      have hrest : (∑ k' ∈ R.erase k, (eff (9 + k'.val)).length) ≤ 2 * (R.erase k).card := by
        calc (∑ k' ∈ R.erase k, (eff (9 + k'.val)).length)
            ≤ ∑ _k' ∈ R.erase k, 2 := Finset.sum_le_sum (fun k' hk' => hR_len_le k' (Finset.mem_erase.mp hk').2)
          _ = 2 * (R.erase k).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      rw [Finset.card_erase_of_mem hk] at hrest
      omega
    omega
  have hread_eq1 : ∀ x ∈ W_in ∪ W_g, (∑ k ∈ R, (eff (9 + k.val)).count x) = 1 := by
    have hge1 : ∀ x ∈ W_in ∪ W_g, 1 ≤ ∑ k ∈ R, (eff (9 + k.val)).count x := by
      intro x hx
      rcases hW_read x hx with ⟨k, hk, hkin⟩
      have hpos : 1 ≤ (eff (9 + k.val)).count x := by
        rw [Nat.succ_le_iff]; exact List.count_pos_iff.mpr hkin
      exact Nat.le_trans hpos
        (Finset.single_le_sum (f := fun k' => (eff (9 + k'.val)).count x)
          (fun _ _ => Nat.zero_le _) hk)
    have htot_le : (∑ x ∈ W_in ∪ W_g, ∑ k ∈ R, (eff (9 + k.val)).count x) ≤ 14 := by
      rw [Finset.sum_comm]
      have h3 : (∑ k ∈ R, ∑ x ∈ W_in ∪ W_g, (eff (9 + k.val)).count x) ≤
          ∑ k ∈ R, (eff (9 + k.val)).length :=
        Finset.sum_le_sum (fun k _ => hlist_count_sum (eff (9 + k.val)) (W_in ∪ W_g))
      omega
    intro x hx
    by_contra hne1
    have hge2 : 2 ≤ ∑ k ∈ R, (eff (9 + k.val)).count x := by
      have := hge1 x hx; omega
    have hsum_ge15 : 15 ≤ ∑ y ∈ W_in ∪ W_g, ∑ k ∈ R, (eff (9 + k.val)).count y := by
      rw [← Finset.add_sum_erase _ _ hx]
      have hrest : (W_in ∪ W_g).card - 1 ≤
          ∑ y ∈ (W_in ∪ W_g).erase x, ∑ k ∈ R, (eff (9 + k.val)).count y := by
        calc (W_in ∪ W_g).card - 1 = ((W_in ∪ W_g).erase x).card := (Finset.card_erase_of_mem hx).symm
          _ = ∑ _y ∈ (W_in ∪ W_g).erase x, 1 := by simp
          _ ≤ ∑ y ∈ (W_in ∪ W_g).erase x, ∑ k ∈ R, (eff (9 + k.val)).count y :=
              Finset.sum_le_sum (fun y hy => hge1 y (Finset.mem_erase.mp hy).2)
      omega
    omega
  rcases heff_kept jtop (hR_sub hjtop_mem) with ⟨hop_not, _⟩ |
      ⟨hop, u, v, heff_top, hu1, hult, hv1, hvlt, hMu, hMv, hFuv⟩
  · exact hnoNot jtop hjtop_mem hop_not
  have ihu := hwire_props u hu1 (by omega) hMu
  have ihv := hwire_props v hv1 (by omega) hMv
  have hR_split : R = insert jtop (reach gs M u ∪ reach gs M v) := by
    dsimp only [R]; rw [hr_eq, hreach_unfold jtop, heff_top]
    simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
  have hdeps_split : deps gs M r = deps gs M u ∪ deps gs M v := by
    rw [hr_eq, hdeps_gate jtop, heff_top]
    simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
  have hu_ne_v : u ≠ v := by
    intro heq; subst heq
    by_cases hu9 : u < 9
    · have hu_mem : u ∈ W_in ∪ W_g := by
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨⟨u - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
      have h1 := hread_eq1 u hu_mem
      have h2 : 2 ≤ ∑ k ∈ R, (eff (9 + k.val)).count u := by
        have htop : (eff (9 + jtop.val)).count u = 2 := by rw [heff_top]; simp
        exact htop ▸ Finset.single_le_sum (f := fun k => (eff (9 + k.val)).count u)
          (fun _ _ => Nat.zero_le _) hjtop_mem
      omega
    · set ju : Fin m := ⟨u - 9, by omega⟩
      have hju_eq : 9 + ju.val = u := by simp [ju]; omega
      have hju_mem : ju ∈ R.erase jtop := by
        rw [Finset.mem_erase]
        refine ⟨by intro h; rw [h] at hju_eq; omega, ?_⟩
        rw [hR_split]; apply Finset.mem_insert_of_mem; apply Finset.mem_union_left
        rw [← hju_eq, hreach_unfold ju]; exact Finset.mem_insert_self _ _
      have hu_mem : u ∈ W_in ∪ W_g := by
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨ju, hju_mem, hju_eq⟩
      have h1 := hread_eq1 u hu_mem
      have h2 : 2 ≤ ∑ k ∈ R, (eff (9 + k.val)).count u := by
        have htop : (eff (9 + jtop.val)).count u = 2 := by rw [heff_top]; simp
        exact htop ▸ Finset.single_le_sum (f := fun k => (eff (9 + k.val)).count u)
          (fun _ _ => Nat.zero_le _) hjtop_mem
      omega
  have hreach_disj : Disjoint (reach gs M u) (reach gs M v) := by
    rw [Finset.disjoint_iff_ne]
    intro j1 hj1 j2 hj2 heq
    subst heq
    set I := reach gs M u ∩ reach gs M v
    have hIne : I.Nonempty := ⟨j1, Finset.mem_inter.mpr ⟨hj1, hj2⟩⟩
    obtain ⟨jmax, hjmax_mem, hjmax_max⟩ := Finset.exists_max_image I Fin.val hIne
    have hjmax_u : jmax ∈ reach gs M u := (Finset.mem_inter.mp hjmax_mem).1
    have hjmax_v : jmax ∈ reach gs M v := (Finset.mem_inter.mp hjmax_mem).2
    have hjmax_ne_top : jmax ≠ jtop := by
      have hle := ihu.2.1 jmax hjmax_u
      intro h; subst h; omega
    have hjmax_in_W : 9 + jmax.val ∈ W_in ∪ W_g := by
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨jmax, Finset.mem_erase.mpr ⟨hjmax_ne_top, ?_⟩, rfl⟩
      rw [hR_split]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hjmax_u)
    have hread1 := hread_eq1 (9 + jmax.val) hjmax_in_W
    have hk1 : ∃ k1 : Fin m, 9 + jmax.val ∈ eff (9 + k1.val) ∧
        ((k1 = jtop ∧ 9 + jmax.val = u) ∨ k1 ∈ reach gs M u) := by
      by_cases hju : 9 + jmax.val = u
      · exact ⟨jtop, by rw [heff_top, hju]; exact List.mem_cons_self, Or.inl ⟨rfl, hju⟩⟩
      · rcases ihu.2.2.2.2.1 jmax hjmax_u hju with ⟨k1, hk1_u, hk1_in⟩
        exact ⟨k1, hk1_in, Or.inr hk1_u⟩
    have hk2 : ∃ k2 : Fin m, 9 + jmax.val ∈ eff (9 + k2.val) ∧
        ((k2 = jtop ∧ 9 + jmax.val = v) ∨ k2 ∈ reach gs M v) := by
      by_cases hjv : 9 + jmax.val = v
      · exact ⟨jtop, by rw [heff_top, hjv]; exact List.mem_cons_of_mem _ List.mem_cons_self,
          Or.inl ⟨rfl, hjv⟩⟩
      · rcases ihv.2.2.2.2.1 jmax hjmax_v hjv with ⟨k2, hk2_v, hk2_in⟩
        exact ⟨k2, hk2_in, Or.inr hk2_v⟩
    rcases hk1 with ⟨k1, hk1_in, hk1_or⟩
    rcases hk2 with ⟨k2, hk2_in, hk2_or⟩
    have hk1_R : k1 ∈ R := by
      rw [hR_split]
      rcases hk1_or with ⟨rfl, _⟩ | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
    have hk2_R : k2 ∈ R := by
      rw [hR_split]
      rcases hk2_or with ⟨rfl, _⟩ | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
    have hk1_ne_k2 : k1 ≠ k2 := by
      intro h; subst h
      rcases hk1_or with ⟨rfl, hju⟩ | h1
      · rcases hk2_or with ⟨_, hjv⟩ | h2
        · exact hu_ne_v (hju.symm.trans hjv)
        · have := ihv.2.1 jtop h2; omega
      · rcases hk2_or with ⟨rfl, _⟩ | h2
        · have := ihu.2.1 jtop h1; omega
        · have hk_I : k1 ∈ I := Finset.mem_inter.mpr ⟨h1, h2⟩
          have hle := hjmax_max k1 hk_I
          have hlt := heff_lt (9 + k1.val) (9 + jmax.val) hk1_in
          omega
    have hge2 : 2 ≤ ∑ k ∈ R, (eff (9 + k.val)).count (9 + jmax.val) := by
      have hsub : ({k1, k2} : Finset (Fin m)) ⊆ R := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      calc 2 = ({k1, k2} : Finset (Fin m)).card := by rw [Finset.card_pair hk1_ne_k2]
        _ = ∑ _k ∈ ({k1, k2} : Finset (Fin m)), 1 := by simp
        _ ≤ ∑ k ∈ ({k1, k2} : Finset (Fin m)), (eff (9 + k.val)).count (9 + jmax.val) := by
            apply Finset.sum_le_sum
            intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rw [Nat.succ_le_iff, List.count_pos_iff]
            rcases hk with rfl | rfl <;> assumption
        _ ≤ ∑ k ∈ R, (eff (9 + k.val)).count (9 + jmax.val) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    omega
  have hdeps_disj : Disjoint (deps gs M u) (deps gs M v) := by
    rw [Finset.disjoint_left]
    intro i hiu hiv
    have hi_W : i.val + 1 ∈ W_in ∪ W_g :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hread1 := hread_eq1 (i.val + 1) hi_W
    have hk1 : ∃ k1 : Fin m, i.val + 1 ∈ eff (9 + k1.val) ∧
        ((k1 = jtop ∧ u = i.val + 1) ∨ k1 ∈ reach gs M u) := by
      rcases ihu.2.2.2.2.2.1 i hiu with heq | ⟨k1, hk1_u, hk1_in⟩
      · exact ⟨jtop, by rw [heff_top, ← heq]; exact List.mem_cons_self, Or.inl ⟨rfl, heq⟩⟩
      · exact ⟨k1, hk1_in, Or.inr hk1_u⟩
    have hk2 : ∃ k2 : Fin m, i.val + 1 ∈ eff (9 + k2.val) ∧
        ((k2 = jtop ∧ v = i.val + 1) ∨ k2 ∈ reach gs M v) := by
      rcases ihv.2.2.2.2.2.1 i hiv with heq | ⟨k2, hk2_v, hk2_in⟩
      · exact ⟨jtop, by rw [heff_top, ← heq]; exact List.mem_cons_of_mem _ List.mem_cons_self,
          Or.inl ⟨rfl, heq⟩⟩
      · exact ⟨k2, hk2_in, Or.inr hk2_v⟩
    rcases hk1 with ⟨k1, hk1_in, hk1_or⟩
    rcases hk2 with ⟨k2, hk2_in, hk2_or⟩
    have hk1_R : k1 ∈ R := by
      rw [hR_split]
      rcases hk1_or with ⟨rfl, _⟩ | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
    have hk2_R : k2 ∈ R := by
      rw [hR_split]
      rcases hk2_or with ⟨rfl, _⟩ | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
    have hk1_ne_k2 : k1 ≠ k2 := by
      intro h; subst h
      rcases hk1_or with ⟨rfl, hui⟩ | h1
      · rcases hk2_or with ⟨_, hvi⟩ | h2
        · exact hu_ne_v (hui.trans hvi.symm)
        · have := ihv.2.1 jtop h2; omega
      · rcases hk2_or with ⟨rfl, _⟩ | h2
        · have := ihu.2.1 jtop h1; omega
        · exact Finset.disjoint_left.mp hreach_disj h1 h2
    have hge2 : 2 ≤ ∑ k ∈ R, (eff (9 + k.val)).count (i.val + 1) := by
      have hsub : ({k1, k2} : Finset (Fin m)) ⊆ R := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      calc 2 = ({k1, k2} : Finset (Fin m)).card := by rw [Finset.card_pair hk1_ne_k2]
        _ = ∑ _k ∈ ({k1, k2} : Finset (Fin m)), 1 := by simp
        _ ≤ ∑ k ∈ ({k1, k2} : Finset (Fin m)), (eff (9 + k.val)).count (i.val + 1) := by
            apply Finset.sum_le_sum; intro k hk; simp at hk
            rw [Nat.succ_le_iff, List.count_pos_iff]
            rcases hk with rfl | rfl <;> assumption
        _ ≤ ∑ k ∈ R, (eff (9 + k.val)).count (i.val + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    omega
  have hB_eq : deps gs M v = (deps gs M u)ᶜ := by
    ext i
    simp only [Finset.mem_compl]
    constructor
    · intro hiv hiu; exact Finset.disjoint_left.mp hdeps_disj hiu hiv
    · intro hniu
      have hi : i ∈ deps gs M u ∪ deps gs M v := by rw [← hdeps_split, hr_deps]; exact Finset.mem_univ i
      rcases Finset.mem_union.mp hi with h | h
      · exact (hniu h).elim
      · exact h
  have hAne : (deps gs M u).Nonempty := ihu.2.2.1
  have hBne : (deps gs M u)ᶜ.Nonempty := hB_eq ▸ ihv.2.2.1
  have hmono_u : ∀ y1 y2, (∀ i, y1 i = true → y2 i = true) → F u y1 = true → F u y2 = true :=
    ihu.2.2.2.2.2.2 (fun k hk => hnoNot k (by rw [hR_split]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hk)))
  have hmono_v : ∀ y1 y2, (∀ i, y1 i = true → y2 i = true) → F v y1 = true → F v y2 = true :=
    ihv.2.2.2.2.2.2 (fun k hk => hnoNot k (by rw [hR_split]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hk)))
  have hd_u : ∀ y1 y2, (∀ i ∈ deps gs M u, y1 i = y2 i) → F u y1 = F u y2 := ihu.2.2.2.1
  have hd_v : ∀ y1 y2, (∀ i ∈ (deps gs M u)ᶜ, y1 i = y2 i) → F v y1 = F v y2 := by
    rw [← hB_eq]; exact ihv.2.2.2.1
  rcases hop with hop | hop
  · apply no_mono_and_split (deps gs M u) hAne hBne (F u) (F v) hmono_u hmono_v hd_u hd_v
    intro y
    rw [← hFr y, hr_eq, hFuv y, hop]
    simp [GateOp.eval]
  · apply no_mono_or_split (deps gs M u) hAne hBne (F u) (F v) hd_u hd_v
    intro y
    rw [← hFr y, hr_eq, hFuv y, hop]
    simp [GateOp.eval]
