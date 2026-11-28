import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1180_aux
open Classical

variable {n t d : ℕ}

abbrev A (d : ℕ) := Fin (d + 2)

def a0 (d : ℕ) : A d := ⟨0, by omega⟩

def Pass (scope : Fin t → Finset (Fin n)) (s : Fin t → Fin n → A d) (x : Fin n → A d) : Prop :=
  ∀ j, ∃ v ∈ scope j, x v ≠ s j v

noncomputable def Cov {k : ℕ} (scope : Fin t → Finset (Fin n))
    (f : Fin k → Fin t → Fin n → A d) : Finset (Fin n → A d) :=
  Finset.univ.filter (fun x => ∃ i, Pass scope (f i) x)

theorem mem_Cov {k : ℕ} (scope : Fin t → Finset (Fin n)) (f : Fin k → Fin t → Fin n → A d)
    (x : Fin n → A d) : x ∈ Cov scope f ↔ ∃ i, Pass scope (f i) x := by
  simp [Cov]

def Live (scope : Fin t → Finset (Fin n)) (v : Fin n) (s : Fin t → Fin n → A d)
    (y : Fin n → A d) : Prop :=
  ∀ j, v ∉ scope j → ∃ w ∈ scope j, y w ≠ s j w

noncomputable def Ex (scope : Fin t → Finset (Fin n)) (v : Fin n) (s : Fin t → Fin n → A d)
    (y : Fin n → A d) : Finset (A d) :=
  ((Finset.univ : Finset (Fin t)).filter (fun j =>
    v ∈ scope j ∧ ∀ w ∈ scope j, w ≠ v → y w = s j w)).image (fun j => s j v)

theorem pass_update (scope : Fin t → Finset (Fin n)) (v : Fin n) (s : Fin t → Fin n → A d)
    (y : Fin n → A d) (a : A d) :
    Pass scope s (Function.update y v a) ↔ Live scope v s y ∧ a ∉ Ex scope v s y := by
  unfold Pass Live Ex
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun ha => ?_⟩
    · obtain ⟨w, hw, hne⟩ := h j
      have hwv : w ≠ v := fun e => hj (e ▸ hw)
      exact ⟨w, hw, by simpa [Function.update_of_ne hwv] using hne⟩
    · obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp ha
      obtain ⟨hjv, hmatch⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨w, hw, hne⟩ := h j
      by_cases hwv : w = v
      · subst hwv
        simp at hne
        exact hne hjs.symm
      · rw [Function.update_of_ne hwv] at hne
        exact hne (hmatch w hw hwv)
  · rintro ⟨hl, ha⟩ j
    by_cases hj : v ∈ scope j
    · by_contra hcon
      push_neg at hcon
      apply ha
      refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, ?_⟩, ?_⟩
      · intro w hw hwv
        have := hcon w hw
        rwa [Function.update_of_ne hwv] at this
      · have := hcon v hj
        simpa using this.symm
    · obtain ⟨w, hw, hne⟩ := hl j hj
      have hwv : w ≠ v := fun e => hj (e ▸ hw)
      exact ⟨w, hw, by simpa [Function.update_of_ne hwv] using hne⟩

theorem count_lemma {k : ℕ} (c : Fin k → A d) (hc : Function.Injective c) (live : Fin k → Prop)
    (E E' : Fin k → Finset (A d))
    (hE : ∀ i, E' i = if (E i).Nonempty then {c i} else ∅) :
    (Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E i)).card ≤
      (Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E' i)).card := by
  by_cases h1 : ∃ i, live i ∧ E i = ∅
  · obtain ⟨i, hi, hE0⟩ := h1
    have : Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E' i) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro a
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, ?_⟩
      rw [hE i, hE0]; simp
    rw [this]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · push_neg at h1
    have hne : ∀ i, live i → (E i).Nonempty := h1
    by_cases h2 : ∃ i1 i2, i1 ≠ i2 ∧ live i1 ∧ live i2
    · obtain ⟨i1, i2, hne12, hl1, hl2⟩ := h2
      have : Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E' i) = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro a
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        by_cases ha : a = c i1
        · refine ⟨i2, hl2, ?_⟩
          rw [hE i2, if_pos (hne i2 hl2)]
          simp
          intro h
          exact hne12 (hc (ha.symm.trans h))
        · refine ⟨i1, hl1, ?_⟩
          rw [hE i1, if_pos (hne i1 hl1)]
          simpa using ha
      rw [this]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    · push_neg at h2
      by_cases h3 : ∃ i0, live i0
      · obtain ⟨i0, hl0⟩ := h3
        have hsingle : ∀ i, live i → i = i0 := fun i hi =>
          by_contra fun hne' => h2 i i0 hne' hi hl0
        have hold : Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E i) =
            Finset.univ.filter (fun a : A d => a ∉ E i0) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, ha⟩
            rw [hsingle i hi] at ha; exact ha
          · intro ha; exact ⟨i0, hl0, ha⟩
        have hnew : Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E' i) =
            Finset.univ.filter (fun a : A d => a ≠ c i0) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, ha⟩
            rw [hsingle i hi, hE i0, if_pos (hne i0 hl0)] at ha
            simpa using ha
          · intro ha
            refine ⟨i0, hl0, ?_⟩
            rw [hE i0, if_pos (hne i0 hl0)]
            simpa using ha
        rw [hold, hnew]
        have e1 : Finset.univ.filter (fun a : A d => a ∉ E i0) = Finset.univ \ E i0 := by
          ext a; simp
        have e2 : Finset.univ.filter (fun a : A d => a ≠ c i0) = Finset.univ \ {c i0} := by
          ext a; simp
        rw [e1, e2, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        have := Finset.card_pos.mpr (hne i0 hl0)
        have h5 : (E i0).card ≤ Fintype.card (A d) := by
          simpa using Finset.card_le_univ (E i0)
        simp only [Finset.card_univ, Finset.card_singleton]
        omega
      · push_neg at h3
        have : Finset.univ.filter (fun a : A d => ∃ i, live i ∧ a ∉ E i) = ∅ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨i, hi, _⟩
          exact h3 i hi
        rw [this]
        exact Nat.zero_le _

end PEqualNP.Outside.L_lib_1180_aux

namespace PEqualNP.Outside.L_lib_1180_aux
open Classical

variable {n t d : ℕ}

theorem card_fiberwise (v : Fin n) (S : Finset (Fin n → A d)) :
    S.card = ∑ y ∈ Finset.univ.filter (fun y : Fin n → A d => y v = a0 d),
      (Finset.univ.filter (fun a : A d => Function.update y v a ∈ S)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Function.update x v (a0 d))
    (t := Finset.univ.filter (fun y : Fin n → A d => y v = a0 d)) (by intro x _; simp)]
  apply Finset.sum_congr rfl
  intro y hy
  have hy' : y v = a0 d := (Finset.mem_filter.mp hy).2
  apply Finset.card_bij (fun x _ => x v)
  · intro x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    have : Function.update y v (x v) = x := by
      rw [← hxy]; simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; exact hxS
  · intro x1 hx1 x2 hx2 h
    have e1 := (Finset.mem_filter.mp hx1).2
    have e2 := (Finset.mem_filter.mp hx2).2
    have h1 : x1 = Function.update y v (x1 v) := by rw [← e1]; simp
    have h2 : x2 = Function.update y v (x2 v) := by rw [← e2]; simp
    have h' : x1 v = x2 v := h
    rw [h1, h2, h']
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨Function.update y v a, Finset.mem_filter.mpr ⟨ha, ?_⟩, by simp⟩
    simp [hy']

noncomputable def reset (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (v : Fin n) (f : Fin k → Fin t → Fin n → A d) : Fin k → Fin t → Fin n → A d :=
  fun i j w => if w = v ∧ v ∈ scope j then color i else f i j w

theorem live_reset (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (v : Fin n) (f : Fin k → Fin t → Fin n → A d) (i : Fin k) (y : Fin n → A d) :
    Live scope v (reset scope color v f i) y ↔ Live scope v (f i) y := by
  unfold Live
  apply forall_congr'
  intro j
  by_cases hj : v ∈ scope j
  · simp [hj]
  · have : ∀ w, reset scope color v f i j w = f i j w := by
      intro w; simp [reset, hj]
    simp only [this]

theorem ex_reset (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (v : Fin n) (f : Fin k → Fin t → Fin n → A d) (i : Fin k) (y : Fin n → A d) :
    Ex scope v (reset scope color v f i) y =
      if (Ex scope v (f i) y).Nonempty then {color i} else ∅ := by
  have hF : (Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
      ∀ w ∈ scope j, w ≠ v → y w = reset scope color v f i j w)) =
      Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
      ∀ w ∈ scope j, w ≠ v → y w = f i j w) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, h⟩
      refine ⟨hj, fun w hw hwv => ?_⟩
      have := h w hw hwv
      simpa [reset, hwv] using this
    · rintro ⟨hj, h⟩
      refine ⟨hj, fun w hw hwv => ?_⟩
      have := h w hw hwv
      simpa [reset, hwv] using this
  have hE : Ex scope v (reset scope color v f i) y =
      (Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
        ∀ w ∈ scope j, w ≠ v → y w = f i j w)).image (fun _ => color i) := by
    unfold Ex
    rw [hF]
    apply Finset.image_congr
    intro j hj
    have hjv := (Finset.mem_filter.mp hj).2.1
    simp [reset, hjv]
  have hne : (Ex scope v (f i) y).Nonempty ↔ (Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
        ∀ w ∈ scope j, w ≠ v → y w = f i j w)).Nonempty := by
    unfold Ex
    exact Finset.image_nonempty
  rw [hE]
  by_cases h : (Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
        ∀ w ∈ scope j, w ≠ v → y w = f i j w)).Nonempty
  · rw [if_pos (hne.mpr h), Finset.image_const h]
  · rw [if_neg (fun h' => h (hne.mp h'))]
    have : (Finset.univ.filter (fun j : Fin t => v ∈ scope j ∧
        ∀ w ∈ scope j, w ≠ v → y w = f i j w)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [this]; simp

theorem step (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (hc : Function.Injective color) (v : Fin n) (f : Fin k → Fin t → Fin n → A d) :
    (Cov scope f).card ≤ (Cov scope (reset scope color v f)).card := by
  rw [card_fiberwise v (Cov scope f), card_fiberwise v (Cov scope (reset scope color v f))]
  apply Finset.sum_le_sum
  intro y _
  have h1 : ∀ a, Function.update y v a ∈ Cov scope f ↔
      ∃ i, Live scope v (f i) y ∧ a ∉ Ex scope v (f i) y := by
    intro a
    rw [mem_Cov]
    exact exists_congr (fun i => pass_update scope v (f i) y a)
  have h2 : ∀ a, Function.update y v a ∈ Cov scope (reset scope color v f) ↔
      ∃ i, Live scope v (f i) y ∧ a ∉ Ex scope v (reset scope color v f i) y := by
    intro a
    rw [mem_Cov]
    exact exists_congr (fun i => by
      rw [pass_update scope v _ y a, live_reset])
  have e1 : Finset.univ.filter (fun a : A d => Function.update y v a ∈ Cov scope f) =
      Finset.univ.filter (fun a : A d => ∃ i, Live scope v (f i) y ∧ a ∉ Ex scope v (f i) y) :=
    Finset.filter_congr (fun a _ => h1 a)
  have e2 : Finset.univ.filter (fun a : A d => Function.update y v a ∈
        Cov scope (reset scope color v f)) =
      Finset.univ.filter (fun a : A d => ∃ i, Live scope v (f i) y ∧
        a ∉ Ex scope v (reset scope color v f i) y) :=
    Finset.filter_congr (fun a _ => h2 a)
  rw [e1, e2]
  exact count_lemma color hc (fun i => Live scope v (f i) y) (fun i => Ex scope v (f i) y)
    (fun i => Ex scope v (reset scope color v f i) y) (fun i => ex_reset scope color v f i y)

theorem reset_all (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (hc : Function.Injective color) (f : Fin k → Fin t → Fin n → A d) (S : Finset (Fin n)) :
    ∃ g : Fin k → Fin t → Fin n → A d, (Cov scope f).card ≤ (Cov scope g).card ∧
      ∀ i j w, w ∈ S → w ∈ scope j → g i j w = color i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨f, le_refl _, by simp⟩
  | insert v S hv ih =>
    obtain ⟨g, hg1, hg2⟩ := ih
    refine ⟨reset scope color v g, hg1.trans (step scope color hc v g), ?_⟩
    intro i j w hw hws
    by_cases hwv : w = v
    · subst hwv; simp [reset, hws]
    · have hwS : w ∈ S := by
        rcases Finset.mem_insert.mp hw with h | h
        · exact absurd h hwv
        · exact h
      simp [reset, hwv, hg2 i j w hwS hws]

theorem cov_eq_const (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (g : Fin k → Fin t → Fin n → A d)
    (hg : ∀ i j w, w ∈ scope j → g i j w = color i) :
    Cov scope g = Cov scope (fun i _ _ => color i) := by
  ext x
  rw [mem_Cov, mem_Cov]
  apply exists_congr
  intro i
  unfold Pass
  apply forall_congr'
  intro j
  apply exists_congr
  intro w
  constructor
  · rintro ⟨hw, hne⟩; exact ⟨hw, by rwa [hg i j w hw] at hne⟩
  · rintro ⟨hw, hne⟩; exact ⟨hw, by rwa [hg i j w hw]⟩

theorem part1 (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (hc : Function.Injective color) (f : Fin k → Fin t → Fin n → A d) :
    (Cov scope f).card ≤ (Cov scope (fun i _ _ => color i)).card := by
  obtain ⟨g, hg1, hg2⟩ := reset_all scope color hc f Finset.univ
  rw [← cov_eq_const scope color g (fun i j w hw => hg2 i j w (Finset.mem_univ _) hw)]
  exact hg1

theorem part2 (scope : Fin t → Finset (Fin n)) {k : ℕ} (color : Fin k → A d)
    (hc : Function.Injective color) :
    Cov scope (fun i _ _ => color i) = Finset.univ ↔
      ¬ ∃ edge : Fin k → Fin t, ∀ i j : Fin k, i ≠ j → scope (edge i) ∩ scope (edge j) = ∅ := by
  constructor
  · intro hcov ⟨edge, hedge⟩

    let x : Fin n → A d := fun v =>
      if h : ∃ i, v ∈ scope (edge i) then color (Classical.choose h) else a0 d
    have hx : ∀ i, ∀ v ∈ scope (edge i), x v = color i := by
      intro i v hv
      have h : ∃ i, v ∈ scope (edge i) := ⟨i, hv⟩
      simp only [x, dif_pos h]
      have hs := Classical.choose_spec h
      by_cases hii : Classical.choose h = i
      · rw [hii]
      · exfalso
        have := hedge _ _ hii
        have hmem : v ∈ scope (edge (Classical.choose h)) ∩ scope (edge i) :=
          Finset.mem_inter.mpr ⟨hs, hv⟩
        rw [this] at hmem
        simp at hmem
    have hxm : x ∈ Cov scope (fun i _ _ => color i) := by rw [hcov]; exact Finset.mem_univ _
    rw [mem_Cov] at hxm
    obtain ⟨i, hi⟩ := hxm
    obtain ⟨v, hv, hne⟩ := hi (edge i)
    exact hne (hx i v hv)
  · intro hno
    apply Finset.eq_univ_of_forall
    intro x
    rw [mem_Cov]
    by_contra hcon
    have : ∀ i, ∃ j, ∀ v ∈ scope j, x v = color i := by
      intro i
      have hnp : ¬ Pass scope (fun _ _ => color i) x := fun hp => hcon ⟨i, hp⟩
      unfold Pass at hnp
      simpa [not_forall, not_exists] using hnp
    choose edge hedge using this
    apply hno
    refine ⟨edge, fun i j hij => ?_⟩
    ext v
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨h1, h2⟩
    have := (hedge i v h1).symm.trans (hedge j v h2)
    exact hij (hc this)

end PEqualNP.Outside.L_lib_1180_aux

theorem PEqualNP.Outside.L_lib_1180 : (∀ (n t d : Nat) (scope : Fin t → Finset (Fin n)),
  let Word := Fin n → Fin (d + 2)
  let Signing := Fin t → Word
  let labels := (Finset.univ : Finset (Fin t))
  let cube := (Finset.univ : Finset Word)
  let pass := fun (s : Signing) (x : Word) => labels.toList.all (fun j =>
    (scope j).toList.any (fun v => x v != s j v))
  let covered := fun {k : Nat} (f : Fin k → Signing) =>
    cube.filter (fun x => (List.finRange k).any (fun i => pass (f i) x))
  ∀ (k : Nat) (color : Fin k → Fin (d + 2)), Function.Injective color →
    let constant : Fin k → Signing := fun i _ _ => color i
    (∀ f : Fin k → Signing, (covered f).card ≤ (covered constant).card) ∧
    (covered constant = cube ↔ ¬ ∃ edge : Fin k → Fin t,
      ∀ i j : Fin k, i ≠ j → scope (edge i) ∩ scope (edge j) = ∅)) := by
  intro n t d scope Word Signing labels cube pass covered k color hc constant
  have hcov : ∀ {k : Nat} (f : Fin k → Signing),
      covered f = PEqualNP.Outside.L_lib_1180_aux.Cov scope f := by
    intro k f
    ext x
    rw [PEqualNP.Outside.L_lib_1180_aux.mem_Cov]
    simp [covered, cube, pass, labels, PEqualNP.Outside.L_lib_1180_aux.Pass,
      List.any_eq_true, List.all_eq_true]
  refine ⟨fun f => ?_, ?_⟩
  · rw [hcov f, hcov constant]
    exact PEqualNP.Outside.L_lib_1180_aux.part1 scope color hc f
  · rw [hcov constant]
    exact PEqualNP.Outside.L_lib_1180_aux.part2 scope color hc
