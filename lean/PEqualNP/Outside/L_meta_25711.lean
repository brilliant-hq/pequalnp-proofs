import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25711.Helpers

open Classical

abbrev I (n : Nat) := Fin n
abbrev P (q : Nat) := Fin q

def pools {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (x y : I n) (j : P q) : Bool := decide (x ∈ R j) || decide (π y ∈ C j)

def color {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (x : I n) (j : P q) : Fin 3 :=
  if x ∈ R j then 1 else if π x ∈ C j then 2 else 0

def rowPins {n q : Nat} (f : I n → P q → Fin 3) : Nat :=
  ∑ j : P q, ((Finset.univ : Finset (I n)).filter (fun x => f x j = 1)).card

def colPins {n q : Nat} (f : I n → P q → Fin 3) : Nat :=
  ∑ j : P q, ((Finset.univ : Finset (I n)).filter (fun x => f x j = 2)).card

def colorPool {n q : Nat} (f : I n → P q → Fin 3)
    (x y : I n) (j : P q) : Bool := decide (f x j = 1 ∨ f y j = 2)

lemma color_one_iff {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (x : I n) (j : P q) : color R C π x j = 1 ↔ x ∈ R j := by
  by_cases hx : x ∈ R j
  · simp [color, hx]
  · by_cases hc : π x ∈ C j <;> simp [color, hx, hc]

lemma color_two_iff {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (x : I n) (j : P q) : color R C π x j = 2 ↔ x ∉ R j ∧ π x ∈ C j := by
  by_cases hx : x ∈ R j
  · simp [color, hx]
  · simp [color, hx]

lemma colors_equal_imply_pool_equal {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    {x y : I n} {j : P q} (h : color R C π x j = color R C π y j) :
    pools R C π x y j = pools R C π y x j := by
  by_cases hxR : x ∈ R j <;> by_cases hyR : y ∈ R j <;>
  by_cases hxC : π x ∈ C j <;> by_cases hyC : π y ∈ C j <;>
    simp [color, pools, hxR, hyR, hxC, hyC] at h ⊢ <;> simp_all

lemma colors_equal_imply_pool_vector_equal {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    {x y : I n} (h : color R C π x = color R C π y) :
    pools R C π x y = pools R C π y x := by
  funext j
  exact colors_equal_imply_pool_equal R C π (congrFun h j)

lemma color_one_card_le {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (j : P q) :
    ((Finset.univ : Finset (I n)).filter (fun x => color R C π x j = 1)).card ≤ (R j).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact (color_one_iff R C π x j).mp hx

lemma color_two_card_le {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (j : P q) :
    ((Finset.univ : Finset (I n)).filter (fun x => color R C π x j = 2)).card ≤ (C j).card := by
  let S := (Finset.univ : Finset (I n)).filter (fun x => π x ∈ C j)
  have hS : S.image π ⊆ C j := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  have hcard : S.card = (S.image π).card := by
    symm
    exact Finset.card_image_of_injective S π.injective
  calc
    ((Finset.univ : Finset (I n)).filter (fun x => color R C π x j = 2)).card
        ≤ S.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (color_two_iff R C π x j).mp hx |>.2⟩
    _ = (S.image π).card := hcard
    _ ≤ (C j).card := Finset.card_le_card hS

lemma rowPins_le {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n)) :
    rowPins (color R C π) ≤ ∑ j : P q, (R j).card := by
  unfold rowPins
  exact Finset.sum_le_sum fun j hj => color_one_card_le R C π j

lemma colPins_le {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n)) :
    colPins (color R C π) ≤ ∑ j : P q, (C j).card := by
  unfold colPins
  exact Finset.sum_le_sum fun j hj => color_two_card_le R C π j

lemma distinct_colors_separate {n q : Nat} (f : I n → P q → Fin 3)
    {x y : I n} {j : P q} (h : f x j ≠ f y j) :
    colorPool f x y j ≠ colorPool f y x j := by
  let a := f x j
  let b := f y j
  have hab : a ≠ b := h
  generalize ha : f x j = a at *
  generalize hb : f y j = b at *
  fin_cases a <;> fin_cases b <;> simp_all [colorPool]

lemma equal_colors_same_pool {n q : Nat} (f : I n → P q → Fin 3)
    {x y : I n} {j : P q} (h : f x j = f y j) :
    colorPool f x y j = colorPool f y x j := by
  simp [colorPool, h]

def errTest {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool)
    (z : I n × I n) : Prop :=
  out {z.1, z.2} (pools R C π z.1 z.2) ≠ G z.1 (π z.2)

noncomputable def errSet {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool) :
    Finset (I n × I n) :=
  Finset.univ.filter (fun z =>
    out {z.1, z.2} (pools R C π z.1 z.2) ≠ G z.1 (π z.2))

def badTest {n q : Nat} (f : I n → P q → Fin 3) (G : I n → I n → Bool)
    (π : Equiv.Perm (I n)) (z : I n × I n) : Prop :=
  z.1 < z.2 ∧ f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1)

noncomputable def badSet {n q : Nat} (f : I n → P q → Fin 3) (G : I n → I n → Bool)
    (π : Equiv.Perm (I n)) : Finset (I n × I n) :=
  Finset.univ.filter (fun z =>
    z.1 < z.2 ∧ f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))

def canon {n : Nat} (z : I n × I n) : I n × I n :=
  if z.1 < z.2 then z else (z.2, z.1)

noncomputable def badToErr {n q : Nat} (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool)
    (z : I n × I n) : I n × I n :=
  if errTest R C π G out z then z else (z.2, z.1)

lemma one_orientation_errors {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool)
    {x y : I n} (hcolor : color R C π x = color R C π y)
    (hG : G x (π y) ≠ G y (π x)) :
    errTest R C π G out (x, y) ∨ errTest R C π G out (y, x) := by
  have haddr := colors_equal_imply_pool_vector_equal R C π hcolor
  have hkey : ({x, y} : Finset (I n)) = {y, x} := by ext z; simp [or_comm]
  have hout : out {x, y} (pools R C π x y) = out {y, x} (pools R C π y x) := by
    rw [hkey, haddr]
  by_cases he : errTest R C π G out (x, y)
  · exact Or.inl he
  · right
    have hval : out {x, y} (pools R C π x y) = G x (π y) := by
      unfold errTest at he
      exact not_ne_iff.mp he
    unfold errTest
    intro hrev
    apply hG
    calc
      G x (π y) = out {x, y} (pools R C π x y) := hval.symm
      _ = out {y, x} (pools R C π y x) := hout
      _ = G y (π x) := hrev

lemma badToErr_mem {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool)
    {z : I n × I n} (hz : badTest (color R C π) G π z) :
    badToErr R C π G out z ∈ errSet R C π G out := by
  rcases hz with ⟨hlt, hcolor, hG⟩
  have hor := one_orientation_errors R C π G out hcolor hG
  unfold errSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change errTest R C π G out (badToErr R C π G out z)
  by_cases he : errTest R C π G out z
  · simpa [badToErr, he] using he
  · have hs : errTest R C π G out (z.2, z.1) := by
      rcases hor with h | h
      · exact (he h).elim
      · simpa [Prod.swap] using h
    simpa [badToErr, he] using hs

lemma canon_badToErr {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool)
    {z : I n × I n} (hlt : z.1 < z.2) :
    canon (badToErr R C π G out z) = z := by
  by_cases he : errTest R C π G out z
  · simp [badToErr, canon, he, hlt]
  · have hnot : ¬ z.2 < z.1 := not_lt_of_gt hlt
    simp [badToErr, canon, he, hlt, hnot]

theorem bad_card_le_err_card {n q : Nat}
    (R C : P q → Finset (I n)) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) (out : Finset (I n) → (P q → Bool) → Bool) :
    (badSet (color R C π) G π).card ≤ (errSet R C π G out).card := by
  apply Finset.card_le_card_of_injOn
    (badToErr R C π G out)
  · intro z hz
    change z ∈ badSet (color R C π) G π at hz
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact badToErr_mem R C π G out hz
  · intro z hz z' hz' heq
    have hcanon := congrArg (canon (n := n)) heq
    change z ∈ badSet (color R C π) G π at hz
    change z' ∈ badSet (color R C π) G π at hz'
    unfold badSet at hz hz'
    rcases Finset.mem_filter.mp hz with ⟨_, hzpred⟩
    rcases Finset.mem_filter.mp hz' with ⟨_, hz'pred⟩
    rcases hzpred with ⟨hzlt, _, _⟩
    rcases hz'pred with ⟨hz'lt, _, _⟩
    rw [canon_badToErr R C π G out hzlt,
      canon_badToErr R C π G out hz'lt] at hcanon
    exact hcanon

def rowFromColor {n q : Nat} (f : I n → P q → Fin 3) (j : P q) : Finset (I n) :=
  Finset.univ.filter (fun x => f x j = 1)

noncomputable def colFromColor {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (j : P q) : Finset (I n) :=
  ((Finset.univ : Finset (I n)).filter (fun x => f x j = 2)).image π

lemma rowFromColor_mem {n q : Nat} (f : I n → P q → Fin 3) (j : P q) (x : I n) :
    x ∈ rowFromColor f j ↔ f x j = 1 := by
  simp [rowFromColor]

lemma colFromColor_mem {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (j : P q) (y : I n) :
    π y ∈ colFromColor f π j ↔ f y j = 2 := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨x, hx, hxy⟩
    have hxy' : x = y := π.injective hxy
    subst y
    exact (Finset.mem_filter.mp hx).2
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

lemma poolsFromColor_eq {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (x y : I n) (j : P q) :
    pools (rowFromColor f) (colFromColor f π) π x y j = colorPool f x y j := by
  simp [pools, colorPool, rowFromColor_mem, colFromColor_mem]

noncomputable def orDecoder {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (G : I n → I n → Bool)
    (U : Finset (I n)) (a : P q → Bool) : Bool :=
  decide (∃ x y, ({x, y} : Finset (I n)) = U ∧
    pools (rowFromColor f) (colFromColor f π) π x y = a ∧ G x (π y) = true)

lemma pair_eq_pair_cases {α : Type} [DecidableEq α] [LinearOrder α]
    {a b x y : α} (h : ({a, b} : Finset α) = {x, y}) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  by_cases hxy : x = y
  · subst y
    have ha : a = x := by
      have hm : a ∈ ({x, x} : Finset α) := by rw [← h]; simp
      simpa using hm
    have hb : b = x := by
      have hm : b ∈ ({x, x} : Finset α) := by rw [← h]; simp
      simpa using hm
    exact Or.inl ⟨ha, hb⟩
  · have ha : a = x ∨ a = y := by
      have hm : a ∈ ({x, y} : Finset α) := by rw [← h]; simp
      simpa using hm
    have hb : b = x ∨ b = y := by
      have hm : b ∈ ({x, y} : Finset α) := by rw [← h]; simp
      simpa using hm
    rcases ha with hax | hay
    · rcases hb with hbx | hby
      · have hyx : y = x := by
          have hm : y ∈ ({a, b} : Finset α) := by rw [h]; simp
          simpa [hax, hbx] using hm
        exact Or.inl ⟨hax, hbx.trans hyx.symm⟩
      · exact Or.inl ⟨hax, hby⟩
    · rcases hb with hbx | hby
      · exact Or.inr ⟨hay, hbx⟩
      · have hxy' : x = y := by
          have hm : x ∈ ({a, b} : Finset α) := by rw [h]; simp
          simpa [hay, hby] using hm
        exact Or.inr ⟨hay, hby.trans hxy'.symm⟩

lemma colorPool_vectors_eq_iff {n q : Nat} (f : I n → P q → Fin 3)
    {x y : I n} :
    colorPool f x y = colorPool f y x ↔ f x = f y := by
  constructor
  · intro hp
    funext j
    by_contra hne
    exact (distinct_colors_separate f hne) (congrFun hp j)
  · intro h
    funext j
    exact equal_colors_same_pool f (congrFun h j)

lemma orDecoder_error_target_false {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (G : I n → I n → Bool) {z : I n × I n}
    (he : errTest (rowFromColor f) (colFromColor f π) π G
      (orDecoder f π G) z) : G z.1 (π z.2) = false := by
  by_contra hfalse
  have htrue : G z.1 (π z.2) = true := by cases h : G z.1 (π z.2) <;> simp_all
  have hself : orDecoder f π G {z.1, z.2}
      (pools (rowFromColor f) (colFromColor f π) π z.1 z.2) = true := by
    exact decide_eq_true_eq.mpr ⟨z.1, z.2, rfl, rfl, htrue⟩
  unfold errTest at he
  simp [hself, htrue] at he

lemma orDecoder_error_bad {n q : Nat} (f : I n → P q → Fin 3)
    (π : Equiv.Perm (I n)) (G : I n → I n → Bool) {z : I n × I n}
    (he : errTest (rowFromColor f) (colFromColor f π) π G
      (orDecoder f π G) z) :
    badTest f G π (canon z) := by
  rcases z with ⟨x, y⟩
  have htarget := orDecoder_error_target_false f π G he
  have hout : orDecoder f π G {x, y}
      (pools (rowFromColor f) (colFromColor f π) π x y) = true := by
    unfold errTest at he
    cases hv : orDecoder f π G {x, y}
        (pools (rowFromColor f) (colFromColor f π) π x y) <;>
      simp [hv, htarget] at he ⊢
  have hwitness := (decide_eq_true_eq.mp hout)
  rcases hwitness with ⟨a, b, hab, haddr, htrue⟩
  rcases pair_eq_pair_cases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst a
    subst b
    simp [htarget] at htrue
  · subst a
    subst b
    have hpool : pools (rowFromColor f) (colFromColor f π) π y x =
        pools (rowFromColor f) (colFromColor f π) π x y := haddr
    have hcolors : f x = f y := by
      apply (colorPool_vectors_eq_iff f).mp
      funext j
      have hj := congrFun hpool j
      simpa [poolsFromColor_eq] using hj.symm
    have hdiff : G x (π y) ≠ G y (π x) := by
      simp [htarget, htrue]
    have hneq : x ≠ y := by
      intro hxy
      subst y
      simp [htarget] at htrue
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simp [badTest, canon, hlt, hcolors, hdiff]
    · have hnot : ¬ x < y := not_lt_of_gt hgt
      simp only [canon, if_neg hnot, badTest]
      exact ⟨hgt, hcolors.symm, hdiff.symm⟩

lemma canon_pair_eq {n : Nat} {x y x' y' : I n}
    (h : canon (x, y) = canon (x', y')) :
    ({x, y} : Finset (I n)) = {x', y'} := by
  by_cases hxy : x < y <;> by_cases hx'y' : x' < y'
  · simp [canon, hxy, hx'y'] at h
    rcases h with ⟨rfl, rfl⟩
    ext t
    simp [or_comm]
  · simp [canon, hxy, hx'y'] at h
    rcases h with ⟨rfl, rfl⟩
    ext t
    simp [or_comm]
  · simp [canon, hxy, hx'y'] at h
    rcases h with ⟨rfl, rfl⟩
    ext t
    simp [or_comm]
  · simp [canon, hxy, hx'y'] at h
    rcases h with ⟨rfl, rfl⟩
    ext t
    simp [or_comm]

lemma canon_bad_implies_asym {n q : Nat} (f : I n → P q → Fin 3)
    (G : I n → I n → Bool) (π : Equiv.Perm (I n)) (x y : I n)
    (h : badTest f G π (canon (x, y))) :
    G x (π y) ≠ G y (π x) := by
  by_cases hlt : x < y
  · simpa [badTest, canon, hlt] using h.2.2
  · simpa [badTest, canon, hlt] using h.2.2.symm

theorem orDecoder_err_card_le_bad_card {n q : Nat}
    (f : I n → P q → Fin 3) (π : Equiv.Perm (I n))
    (G : I n → I n → Bool) :
    (errSet (rowFromColor f) (colFromColor f π) π G
      (orDecoder f π G)).card ≤ (badSet f G π).card := by
  apply Finset.card_le_card_of_injOn (fun z => canon (n := n) z)
  · intro z hz
    change z ∈ errSet (rowFromColor f) (colFromColor f π) π G
      (orDecoder f π G) at hz
    unfold errSet at hz
    have hzbad : badTest f G π (canon z) :=
      orDecoder_error_bad f π G (Finset.mem_filter.mp hz).2
    simpa [badSet, badTest] using hzbad
  · intro z hz z' hz' hcanon
    have hzerr : errTest (rowFromColor f) (colFromColor f π) π G
        (orDecoder f π G) z := by
      change z ∈ errSet (rowFromColor f) (colFromColor f π) π G
        (orDecoder f π G) at hz
      simpa [errSet, errTest] using hz
    have hz'err : errTest (rowFromColor f) (colFromColor f π) π G
        (orDecoder f π G) z' := by
      change z' ∈ errSet (rowFromColor f) (colFromColor f π) π G
        (orDecoder f π G) at hz'
      simpa [errSet, errTest] using hz'
    rcases z with ⟨x, y⟩
    rcases z' with ⟨x', y'⟩
    have hset : ({x, y} : Finset (I n)) = {x', y'} := canon_pair_eq hcanon
    rcases pair_eq_pair_cases hset with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
    · subst x'
      subst y'
      rfl
    · subst x'
      subst y'
      have hxfalse := orDecoder_error_target_false f π G hzerr
      have hyfalse := orDecoder_error_target_false f π G hz'err
      have hdiff := canon_bad_implies_asym f G π x y
        (orDecoder_error_bad f π G hzerr)
      simp [hxfalse, hyfalse] at hdiff

theorem characterization {n q r c e : Nat} (G : I n → I n → Bool)
    (π : Equiv.Perm (I n)) :
    (∃ (R C : P q → Finset (I n)) (out : Finset (I n) → (P q → Bool) → Bool),
      (∑ j : P q, (R j).card) ≤ r ∧
      (∑ j : P q, (C j).card) ≤ c ∧
      (errSet R C π G out).card ≤ e) ↔
    ∃ f : I n → P q → Fin 3,
      rowPins f ≤ r ∧ colPins f ≤ c ∧ (badSet f G π).card ≤ e := by
  constructor
  · rintro ⟨R, C, out, hr, hc, he⟩
    refine ⟨color R C π, ?_, ?_, ?_⟩
    · exact (rowPins_le R C π).trans hr
    · exact (colPins_le R C π).trans hc
    · exact (bad_card_le_err_card R C π G out).trans he
  · rintro ⟨f, hr, hc, he⟩
    refine ⟨rowFromColor f, colFromColor f π, orDecoder f π G, ?_, ?_, ?_⟩
    · change rowPins f ≤ r
      exact hr
    · have hcol : (∑ j : P q, (colFromColor f π j).card) = colPins f := by
        unfold colFromColor colPins
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.card_image_of_injective
          ((Finset.univ : Finset (I n)).filter (fun x => f x j = 2)) π.injective
      rw [hcol]
      exact hc
    · exact (orDecoder_err_card_le_bad_card f π G).trans he

theorem exactTarget : (∀ (n q : ℕ) (G : Fin n → Fin n → Bool)
    (π : Equiv.Perm (Fin n)),
  let I := Fin n
  let P := Fin q
  let pools := fun (R C : P → Finset I) (x y : I) (j : P) =>
    decide (x ∈ R j ∨ π y ∈ C j)
  let loss := fun (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (pools R C z.1 z.2) ≠ G z.1 (π z.2))).card
  ∀ (r c e : ℕ),
    (∃ (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool),
      (∑ j, (R j).card) ≤ r ∧ (∑ j, (C j).card) ≤ c ∧ loss R C out ≤ e) ↔
    ∃ f : I → P → Fin 3,
      (∑ j : P, ((Finset.univ : Finset I).filter (fun v => f v j = 1)).card) ≤ r ∧
      (∑ j : P, ((Finset.univ : Finset I).filter (fun w => f w j = 2)).card) ≤ c ∧
      ((Finset.univ : Finset (I × I)).filter (fun z => z.1 < z.2 ∧
        f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))).card ≤ e) := by
  intro n q G π
  dsimp
  intro r c e
  have h := characterization (n := n) (q := q) (r := r) (c := c) (e := e) G π
  exact h

end PEqualNP.Outside.L_meta_25711.Helpers


theorem PEqualNP.Outside.L_meta_25711 : (∀ (n q : ℕ) (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)),
  let I := Fin n
  let P := Fin q
  let pools := fun (R C : P → Finset I) (x y : I) (j : P) => decide (x ∈ R j ∨ π y ∈ C j)
  let loss := fun (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (pools R C z.1 z.2) ≠ G z.1 (π z.2))).card
  ∀ (r c e : ℕ),
    (∃ (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool),
      (∑ j, (R j).card) ≤ r ∧ (∑ j, (C j).card) ≤ c ∧ loss R C out ≤ e) ↔
    ∃ f : I → P → Fin 3,
      (∑ j : P, ((Finset.univ : Finset I).filter (fun v => f v j = 1)).card) ≤ r ∧
      (∑ j : P, ((Finset.univ : Finset I).filter (fun w => f w j = 2)).card) ≤ c ∧
      ((Finset.univ : Finset (I × I)).filter (fun z => z.1 < z.2 ∧
        f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))).card ≤ e) := by
  exact PEqualNP.Outside.L_meta_25711.Helpers.exactTarget
