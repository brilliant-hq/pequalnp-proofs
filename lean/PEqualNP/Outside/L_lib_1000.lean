import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1000_aux

open Finset
open scoped BigOperators

variable {m q : ℕ}

def differences (x y : Fin m → Fin q) : Finset (Fin m) :=
  univ.filter (fun i => x i ≠ y i)

theorem mem_differences (x y : Fin m → Fin q) (i : Fin m) :
    i ∈ differences x y ↔ x i ≠ y i := by
  simp [differences]

noncomputable def axis (c x : Fin m → Fin q) (hx : hammingDist c x = 1) : Fin m :=
  Classical.choose (card_eq_one.mp hx : ∃ i, differences c x = {i})

theorem differences_axis (c x : Fin m → Fin q) (hx : hammingDist c x = 1) :
    differences c x = {axis c x hx} :=
  Classical.choose_spec (card_eq_one.mp hx : ∃ i, differences c x = {i})

theorem axis_ne (c x : Fin m → Fin q) (hx : hammingDist c x = 1) :
    c (axis c x hx) ≠ x (axis c x hx) := by
  rw [← mem_differences, differences_axis c x hx]
  simp

theorem axis_other (c x : Fin m → Fin q) (hx : hammingDist c x = 1)
    (i : Fin m) (hi : i ≠ axis c x hx) : c i = x i := by
  by_contra hn
  have h := (mem_differences c x i).2 hn
  rw [differences_axis c x hx, mem_singleton] at h
  exact hi h

theorem axis_inj (c x z : Fin m → Fin q)
    (hx : hammingDist c x = 1) (hz : hammingDist c z = 1)
    (h : axis c x hx = axis c z hz)
    (hv : x (axis c x hx) = z (axis c z hz)) : x = z := by
  funext i
  by_cases hi : i = axis c x hx
  · simpa [hi, ← h] using hv
  · rw [← axis_other c x hx i hi, ← axis_other c z hz i (h ▸ hi)]

theorem same_axis (c x z : Fin m → Fin q)
    (hx : hammingDist c x = 1) (hz : hammingDist c z = 1)
    (h : hammingDist x z = 1) : axis c x hx = axis c z hz := by
  by_contra hne
  have hxz : axis c x hx ∈ differences x z := by
    apply (mem_differences _ _ _).2
    rw [← axis_other c z hz _ hne]
    exact (axis_ne c x hx).symm
  have hzx : axis c z hz ∈ differences x z := by
    apply (mem_differences _ _ _).2
    rw [← axis_other c x hx _ (fun h => hne h.symm)]
    exact axis_ne c z hz
  rw [differences_axis x z h, mem_singleton] at hxz hzx
  exact hne (hxz.trans hzx.symm)

theorem near_axis (c x y : Fin m → Fin q) (hx : hammingDist c x = 1)
    (hy : 2 ≤ hammingDist c y) (h : hammingDist x y ≤ 2) :
    axis c x hx ∈ differences c y := by
  by_contra hn
  have hev : c (axis c x hx) = y (axis c x hx) := by
    simpa [mem_differences] using hn
  have hsub : insert (axis c x hx) (differences c y) ⊆ differences x y := by
    intro i hi
    rcases mem_insert.1 hi with rfl | hi
    · apply (mem_differences _ _ _).2
      rw [← hev]
      exact (axis_ne c x hx).symm
    · apply (mem_differences _ _ _).2
      have hi' : i ≠ axis c x hx := fun e => hn (e ▸ hi)
      rw [← axis_other c x hx i hi']
      exact (mem_differences _ _ _).1 hi
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hn] at hc
  change hammingDist c y + 1 ≤ hammingDist x y at hc
  omega

theorem adjacent_value (c x y : Fin m → Fin q) (hx : hammingDist c x = 1)
    (hy : 2 ≤ hammingDist c y) (h : hammingDist x y = 1) :
    x (axis c x hx) = y (axis c x hx) := by
  by_contra hne
  have ha := (mem_differences x y _).2 hne
  rw [differences_axis x y h, mem_singleton] at ha
  have hsub : differences c y ⊆ {axis c x hx} := by
    intro i hi
    by_contra hn
    have hi' : i ≠ axis c x hx := by simpa using hn
    have hv := (mem_differences c y i).1 hi
    rw [axis_other c x hx i hi'] at hv
    have hm := (mem_differences x y i).2 hv
    rw [differences_axis x y h, mem_singleton, ← ha] at hm
    exact hi' hm
  have hc := card_le_card hsub
  simp only [card_singleton] at hc
  change hammingDist c y ≤ 1 at hc
  omega

theorem adjacent_neighbors (c y : Fin m → Fin q) (N : Finset (Fin m → Fin q))
    (hN : ∀ x ∈ N, hammingDist c x = 1) (hy : 2 ≤ hammingDist c y) :
    (N.filter (fun x => hammingDist x y = 1)).card ≤ 2 := by
  let A := N.filter (fun x => hammingDist x y = 1)
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx⟩ := hA
    have hx' := mem_filter.mp hx
    have hd := hammingDist_triangle c x y
    rw [hN x hx'.1, hx'.2] at hd
    refine le_trans (card_le_card_of_injective (f := fun z : A =>
      (⟨axis c z (hN z (mem_filter.mp z.property).1),
        near_axis c z y (hN z (mem_filter.mp z.property).1) hy
          (by have h := (mem_filter.mp z.property).2; omega)⟩ : differences c y)) ?_) hd
    intro a b hab
    apply Subtype.ext
    have ha := hN a (mem_filter.mp a.property).1
    have hb := hN b (mem_filter.mp b.property).1
    have he : axis c a ha = axis c b hb := congrArg Subtype.val hab
    apply axis_inj c a b ha hb he
    rw [adjacent_value c a y ha hy (mem_filter.mp a.property).2,
      adjacent_value c b y hb hy (mem_filter.mp b.property).2, he]
  · have he := not_nonempty_iff_eq_empty.mp hA
    simp [← show A = N.filter (fun x => hammingDist x y = 1) from rfl, he]

theorem near_neighbors (c y : Fin m → Fin q) (N : Finset (Fin m → Fin q))
    (hN : ∀ x ∈ N, hammingDist c x = 1) (hy : 2 ≤ hammingDist c y) :
    (N.filter (fun x => hammingDist x y ≤ 2)).card ≤ 3*q := by
  let A := N.filter (fun x => hammingDist x y ≤ 2)
  by_cases hA : A.Nonempty
  · obtain ⟨x, hx⟩ := hA
    have hx' := mem_filter.mp hx
    have hd := hammingDist_triangle c x y
    rw [hN x hx'.1] at hd
    have hd' : (differences c y).card ≤ 3 := le_trans hd (by omega)
    let P := (differences c y).product (univ : Finset (Fin q))
    calc
      A.card ≤ P.card := by
        refine card_le_card_of_injective (f := fun z : A =>
          let j := axis c z (hN z (mem_filter.mp z.property).1)
          (⟨(j, z.val j), mem_product.2
            ⟨near_axis c z y (hN z (mem_filter.mp z.property).1) hy
              (mem_filter.mp z.property).2, mem_univ _⟩⟩ : P)) ?_
        intro a b hab
        apply Subtype.ext
        have he := congrArg Subtype.val hab
        exact axis_inj c a b _ _ (congrArg Prod.fst he) (congrArg Prod.snd he)
      _ ≤ 3*q := by simpa [P] using Nat.mul_le_mul_right q hd'
  · have he := not_nonempty_iff_eq_empty.mp hA
    simp [← show A = N.filter (fun x => hammingDist x y ≤ 2) from rfl, he]

theorem internal_neighbors (c x : Fin m → Fin q) (N : Finset (Fin m → Fin q))
    (hN : ∀ z ∈ N, hammingDist c z = 1) (hx : hammingDist c x = 1) :
    (N.filter (fun z => hammingDist x z = 1)).card ≤ q := by
  let A := N.filter (fun z => hammingDist x z = 1)
  calc
    A.card ≤ (univ : Finset (Fin q)).card := by
      refine card_le_card_of_injOn (fun z => z (axis c x hx)) (fun _ _ => mem_univ _) ?_
      intro a ha b hb hv
      have ha' := hN a (mem_filter.mp ha).1
      have hb' := hN b (mem_filter.mp hb).1
      have hxa := same_axis c x a hx ha' (mem_filter.mp ha).2
      have hxb := same_axis c x b hx hb' (mem_filter.mp hb).2
      exact axis_inj c a b ha' hb' (hxa.symm.trans hxb) (by simpa [← hxa, ← hxb] using hv)
    _ = q := by simp

end PEqualNP.Outside.L_lib_1000_aux

namespace PEqualNP.Outside.L_lib_1000_aux

open Finset
open scoped BigOperators

def countPairs {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (S T : Finset α) : ℕ :=
  ((S.product T).filter (fun p => r p.1 p.2)).card

theorem count_eq_sum {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (S T : Finset α) :
    countPairs r S T = ∑ x ∈ S, (T.filter (r x)).card := by
  have hc := Finset.natCast_card_filter (R := ℕ) (fun p => r p.1 p.2) (S.product T)
  simp only [Nat.cast_id] at hc
  rw [countPairs, hc]
  refine (Finset.sum_product' S T (fun x y => if r x y then (1 : ℕ) else 0)).trans ?_
  apply sum_congr rfl
  intro x _
  simpa only [Nat.cast_id] using Finset.sum_boole (R := ℕ) (r x) T

theorem count_swap {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (hr : ∀ x y, r x y ↔ r y x) (S T : Finset α) :
    countPairs r S T = countPairs r T S := by
  have expand (U V : Finset α) :
      countPairs r U V = ∑ x ∈ U, ∑ y ∈ V, if r x y then 1 else 0 := by
    rw [count_eq_sum]
    apply sum_congr rfl
    intro x _
    simpa only [Nat.cast_id] using Finset.natCast_card_filter (R := ℕ) (r x) V
  rw [expand, expand, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
    if_congr (hr x y) rfl rfl

theorem count_split {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (hr : ∀ x y, r x y ↔ r y x) (B T : Finset α) (hd : Disjoint B T) :
    countPairs r (B ∪ T) (B ∪ T) =
      countPairs r B B + countPairs r T T + 2 * countPairs r T B := by
  have count_union_left (S : Finset α) :
      countPairs r (B ∪ T) S = countPairs r B S + countPairs r T S := by
    simp only [count_eq_sum, sum_union hd]
  rw [count_union_left, count_swap r hr B (B ∪ T), count_swap r hr T (B ∪ T),
    count_union_left, count_union_left, count_swap r hr B T]
  omega

theorem split_neighbors {m q : ℕ} (S : Finset (Fin m → Fin q)) (c : Fin m → Fin q)
    (hc : c ∈ S) (hq : 2 ≤ q) (k : ℕ)
    (hD : 3*q+2*k < (S.filter (fun x => hammingDist c x = 1)).card) :
    let N := S.filter (fun x => hammingDist c x = 1)
    let B := insert c N
    let T := S \ B
    let E := fun x y => hammingDist x y = 1
    let F := fun x y => 3 ≤ hammingDist x y
    countPairs E B B ≤ (3*q+2*k) * B.card ∧
      k * countPairs E T B ≤ countPairs F T B := by
  intro N B T E F
  have hN : ∀ x ∈ N, hammingDist c x = 1 := fun _ hx => (mem_filter.mp hx).2
  have hnc : c ∉ N := by simp [N]
  have inside : ∀ x ∈ N, (B.filter (E x)).card ≤ q+1 := by
    intro x hx
    have hsub : B.filter (E x) ⊆ insert c (N.filter (E x)) := by
      intro z hz
      obtain ⟨hz, hadj⟩ := mem_filter.mp hz
      rcases mem_insert.mp hz with rfl | hz
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hz,hadj⟩)
    exact (card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (internal_neighbors c x N hN (hN x hx)) 1))
  have hb : B.card = N.card+1 := card_insert_of_notMem hnc
  constructor
  · rw [count_eq_sum]
    calc
      ∑ x ∈ B, (B.filter (E x)).card
          = (B.filter (E c)).card + ∑ x ∈ N, (B.filter (E x)).card :=
        sum_insert hnc
      _ ≤ B.card + N.card * (q+1) := by
        apply Nat.add_le_add (card_filter_le _ _)
        calc
          ∑ x ∈ N, (B.filter (E x)).card ≤ ∑ _x ∈ N, (q+1) := sum_le_sum inside
          _ = N.card * (q+1) := by simp
      _ ≤ (3*q+2*k) * B.card := by
        have hh : N.card * (q+1) ≤ B.card * (q+1) :=
          Nat.mul_le_mul_right _ (by omega)
        calc
          B.card + N.card * (q+1) ≤ (q+2) * B.card := by
            rw [show (q+2) * B.card = B.card + B.card * (q+1) by ring]
            omega
          _ ≤ (3*q+2*k) * B.card := Nat.mul_le_mul_right _ (by omega)
  · rw [count_eq_sum, count_eq_sum, Finset.mul_sum]
    apply sum_le_sum
    intro y hy
    have hy' : 2 ≤ hammingDist c y := by
      obtain ⟨hsy,hby⟩ := mem_sdiff.mp hy
      have hn : hammingDist c y ≠ 1 := fun h => hby (mem_insert_of_mem (mem_filter.mpr ⟨hsy,h⟩))
      have hz : hammingDist c y ≠ 0 := fun h =>
        hby (by
          have he := hammingDist_eq_zero.mp h
          rw [← he]
          exact mem_insert_self c N)
      omega
    have hedges : (B.filter (E y)).card ≤ 2 := by
      have he : B.filter (E y) = N.filter (fun x => hammingDist x y = 1) := by
        ext x
        simp only [mem_filter, B, mem_insert, E]
        rw [hammingDist_comm y x]
        constructor
        · rintro ⟨rfl | hx,ha⟩
          · omega
          · exact ⟨hx,ha⟩
        · rintro ⟨hx,ha⟩
          exact ⟨Or.inr hx,ha⟩
      rw [he]
      exact adjacent_neighbors c y N hN hy'
    have hfar : 2*k ≤ (B.filter (F y)).card := by
      have hnear := near_neighbors c y N hN hy'
      have hpartition := card_filter_add_card_filter_not (s := N)
        (p := fun x => hammingDist x y ≤ 2)
      have hs :
          (N.filter (fun x => ¬ hammingDist x y ≤ 2)) ⊆ B.filter (F y) := by
        intro x hx
        obtain ⟨hx,hfar⟩ := mem_filter.mp hx
        apply mem_filter.mpr
        refine ⟨mem_insert_of_mem hx, ?_⟩
        change 3 ≤ hammingDist y x
        rw [hammingDist_comm y x]
        omega
      have hh := card_le_card hs
      change 3*q+2*k < N.card at hD
      omega
    exact (Nat.mul_le_mul_left k hedges).trans (by simpa [Nat.mul_comm] using hfar)

theorem total {m q : ℕ} (hq : 2 ≤ q) (k : ℕ) (S : Finset (Fin m → Fin q)) :
    k * countPairs (fun x y => hammingDist x y = 1) S S ≤
      k * (3*q + 2*k) * S.card + countPairs (fun x y => 3 ≤ hammingDist x y) S S := by
  let E := fun x y : Fin m → Fin q => hammingDist x y = 1
  let F := fun x y : Fin m → Fin q => 3 ≤ hammingDist x y
  change k * countPairs E S S ≤ k * (3*q + 2*k) * S.card + countPairs F S S
  have hE : ∀ x y, E x y ↔ E y x := fun x y => by simp only [E, hammingDist_comm x y]
  have hF : ∀ x y, F x y ↔ F y x := fun x y => by simp only [F, hammingDist_comm x y]
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hex : ∃ c ∈ S, 3*q+2*k < (S.filter (E c)).card
    · obtain ⟨c,hc,hD⟩ := hex
      let N := S.filter (E c)
      let B := insert c N
      let T := S \ B
      have hBS : B ⊆ S := insert_subset hc (filter_subset _ _)
      have hT : T ⊂ S := sdiff_ssubset hBS ⟨c, mem_insert_self c N⟩
      have hd : Disjoint B T := disjoint_sdiff
      have hu : B ∪ T = S := union_sdiff_of_subset hBS
      have hcard : S.card = B.card + T.card := by rw [← card_union_of_disjoint hd, hu]
      have hsmall := ih T hT
      obtain ⟨hB,hcross⟩ := split_neighbors S c hc hq k hD
      change countPairs E B B ≤ (3*q+2*k)*B.card at hB
      change k * countPairs E T B ≤ countPairs F T B at hcross
      have h1 := Nat.mul_le_mul_left k hB
      rw [← Nat.mul_assoc] at h1
      rw [← hu, count_split E hE B T hd, count_split F hF B T hd,
        hu, hcard, Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc,
        Nat.mul_comm k 2, Nat.mul_assoc]
      omega
    · have hbound : countPairs E S S ≤ (3*q+2*k) * S.card := by
        rw [count_eq_sum, Nat.mul_comm]
        calc
          ∑ x ∈ S, (S.filter (E x)).card ≤ ∑ _x ∈ S, (3*q+2*k) :=
            sum_le_sum fun x hx => Nat.le_of_not_gt fun h => hex ⟨x,hx,h⟩
          _ = S.card * (3*q+2*k) := by simp
      exact (Nat.mul_le_mul_left k hbound).trans (by rw [← Nat.mul_assoc]; omega)

end PEqualNP.Outside.L_lib_1000_aux

theorem PEqualNP.Outside.L_lib_1000 : (∀ (q m k : Nat), 2 ≤ q → 0 < k →
  let W := Fin m → Fin q
  let dist := fun (x y : W) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)).card
  ∀ S : Finset W,
    let pairs := S.product S
    let edges := (pairs.filter (fun p => dist p.1 p.2 = 1)).card
    let far := (pairs.filter (fun p => 3 ≤ dist p.1 p.2)).card
    k * edges ≤ k * (3*q + 2*k) * S.card + far) := by
  intro q m k hq _ W dist S pairs edges far
  exact PEqualNP.Outside.L_lib_1000_aux.total hq k S
