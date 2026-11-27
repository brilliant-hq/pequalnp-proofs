import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_759

open Module Submodule

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem plane_mem {n : ℕ} {x y z : Fin n → ZMod 2} (h : z ∈ span (ZMod 2) {x, y}) (hz : z ≠ 0) :
    z = x ∨ z = y ∨ z = x + y := by
  obtain ⟨a, b, rfl⟩ := mem_span_pair.1 h
  rcases z2 a with rfl | rfl <;> rcases z2 b with rfl | rfl <;> simp_all

theorem range2 {n : ℕ} (x y : Fin n → ZMod 2) : Set.range ![x, y] = {x, y} := by
  rw [Matrix.range_cons_cons_empty]

theorem finrank2 {n : ℕ} {x y : Fin n → ZMod 2} (h : LinearIndependent (ZMod 2) ![x, y]) :
    finrank (ZMod 2) (span (ZMod 2) ({x, y} : Set (Fin n → ZMod 2))) = 2 := by
  rw [← range2, finrank_span_eq_card h]; simp

theorem indep_facts {n : ℕ} {x y : Fin n → ZMod 2} (h : LinearIndependent (ZMod 2) ![x, y]) :
    x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 := by
  rw [LinearIndependent.pair_iff] at h
  refine ⟨fun hx => ?_, fun hy => ?_, fun hxy => ?_⟩
  · have := h 1 0 (by simp [hx]); exact absurd this.1 (by decide)
  · have := h 0 1 (by simp [hy]); exact absurd this.2 (by decide)
  · have := h 1 1 (by simpa using hxy); exact absurd this.1 (by decide)

theorem extend2 {n : ℕ} {x y : Fin n → ZMod 2} (h : LinearIndependent (ZMod 2) ![x, y])
    (α β : ZMod 2) : ∃ m : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, m x = α ∧ m y = β := by
  let b := Basis.span h
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.constr (ZMod 2) ![α, β])
  have e : ∀ i, g (![x, y] i) = ![α, β] i := by
    intro i
    have := congrArg (fun f => f (b i)) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Basis.constr_basis] at this
    rw [Basis.span_apply] at this
    exact this
  exact ⟨g, e 0, e 1⟩

theorem combine {n : ℕ} (U T : Submodule (ZMod 2) (Fin n → ZMod 2)) (hd : Disjoint U T)
    (m1 m2 : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ m : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ x ∈ U, m x = m1 x) ∧ (∀ x ∈ T, m x = m2 x) := by
  let f1 : (Fin n → ZMod 2) →ₗ.[ZMod 2] ZMod 2 := ⟨U, m1.comp U.subtype⟩
  let f2 : (Fin n → ZMod 2) →ₗ.[ZMod 2] ZMod 2 := ⟨T, m2.comp T.subtype⟩
  have H : ∀ (x : f1.domain) (y : f2.domain), (x : Fin n → ZMod 2) = y → f1 x = f2 y := by
    intro x y hxy
    have hx0 : (x : Fin n → ZMod 2) = 0 :=
      Submodule.disjoint_def.1 hd x x.2 (hxy ▸ y.2)
    have hy0 : (y : Fin n → ZMod 2) = 0 := hxy ▸ hx0
    show m1 x = m2 y
    rw [hx0, hy0, map_zero, map_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (f1.sup f2 H).toFun
  refine ⟨g, fun x hx => ?_, fun x hx => ?_⟩
  · have hz : x ∈ f1.domain ⊔ f2.domain := Submodule.mem_sup_left hx
    have e1 : g x = (f1.sup f2 H) ⟨x, hz⟩ := congrArg (fun f => f ⟨x, hz⟩) hg
    have e2 := LinearPMap.sup_apply H ⟨x, hx⟩ (0 : f2.domain) ⟨x, hz⟩ (by simp)
    exact e1.trans (e2.trans (by rw [LinearPMap.map_zero, add_zero]; rfl))
  · have hz : x ∈ f1.domain ⊔ f2.domain := Submodule.mem_sup_right hx
    have e1 : g x = (f1.sup f2 H) ⟨x, hz⟩ := congrArg (fun f => f ⟨x, hz⟩) hg
    have e2 := LinearPMap.sup_apply H (0 : f1.domain) ⟨x, hx⟩ ⟨x, hz⟩ (by simp)
    exact e1.trans (e2.trans (by rw [LinearPMap.map_zero, zero_add]; rfl))

def good {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (P : Submodule (ZMod 2) (Fin n → ZMod 2)) (c : ZMod 2) : Prop :=
  ∃ m : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ x ∈ P, x ≠ 0 → m x + c ∈ av x

theorem arith1 : ∀ a c : ZMod 2, a + c + c = a := by decide
theorem arith2 : ∀ a b d c : ZMod 2, a + b + d = c → a + c + (b + c) + c = d := by decide

theorem good_of_pair {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    {x y : Fin n → ZMod 2} (h : LinearIndependent (ZMod 2) ![x, y]) (f : (Fin n → ZMod 2) → ZMod 2)
    (c : ZMod 2) (hsum : f x + f y + f (x + y) = c) (hx : f x ∈ av x) (hy : f y ∈ av y)
    (hxy : f (x + y) ∈ av (x + y)) : good av (span (ZMod 2) {x, y}) c := by
  obtain ⟨m, mx, my⟩ := extend2 h (f x + c) (f y + c)
  refine ⟨m, fun z hz hz0 => ?_⟩
  rcases plane_mem hz hz0 with rfl | rfl | rfl
  · rw [mx, arith1]; exact hx
  · rw [my, arith1]; exact hy
  · rw [map_add, mx, my, arith2 _ _ _ _ hsum]; exact hxy

noncomputable def sel {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (hne : ∀ x : Fin n → ZMod 2, x ≠ 0 → (av x).Nonempty) (z : Fin n → ZMod 2) : ZMod 2 :=
  if h : z ≠ 0 then (hne z h).choose else 0

theorem sel_mem {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (hne : ∀ x : Fin n → ZMod 2, x ≠ 0 → (av x).Nonempty) {z : Fin n → ZMod 2} (hz : z ≠ 0) :
    sel av hne z ∈ av z := by
  unfold sel; rw [dif_pos hz]; exact (hne z hz).choose_spec

theorem good_any {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (hne : ∀ x : Fin n → ZMod 2, x ≠ 0 → (av x).Nonempty)
    {x y : Fin n → ZMod 2} (h : LinearIndependent (ZMod 2) ![x, y]) :
    ∃ c, good av (span (ZMod 2) {x, y}) c := by
  obtain ⟨hx, hy, hxy⟩ := indep_facts h
  exact ⟨_, good_of_pair av h (sel av hne) _ rfl (sel_mem av hne hx) (sel_mem av hne hy)
    (sel_mem av hne hxy)⟩

theorem self_add {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a; revert a; decide

theorem indep_of {n : ℕ} {x y : Fin n → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent (ZMod 2) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases z2 s with rfl | rfl <;> rcases z2 t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp at hst; exact absurd hst hy
  · simp at hst; exact absurd hst hx
  · simp at hst
    apply absurd _ hxy
    have := congrArg (· + y) hst
    simpa [add_assoc, self_add] using this

theorem other_vec {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ZMod 2} (hx : x ≠ 0) :
    ∃ y, LinearIndependent (ZMod 2) ![x, y] := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  refine ⟨Pi.single j 1, ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hi' := congrFun hst i
  simp [Ne.symm hj] at hi'
  rcases hi' with rfl | hi'
  · refine ⟨rfl, ?_⟩
    have hj' := congrFun hst j
    simpa using hj'
  · exact absurd hi' hi

theorem arith3 : ∀ a b d c : ZMod 2, a + b + d ≠ c → a + b + d = c + 1 := by decide
theorem arith4 : ∀ a b d c : ZMod 2, a + b + d = c + 1 →
    a + (c + 1) + (b + (c + 1)) = d + (c + 1) := by decide
theorem arith5 : ∀ a b d c e : ZMod 2, a + b + d = c + 1 → e ≠ a → e + b + d = c := by decide
theorem arith6 : ∀ a c : ZMod 2, a = a + (c + 1) + (c + 1) := by decide

theorem affine_of_bad {n : ℕ} (hn : 2 ≤ n) (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (hne : ∀ x : Fin n → ZMod 2, x ≠ 0 → (av x).Nonempty) (c : ZMod 2)
    (hbad : ∀ x y : Fin n → ZMod 2, LinearIndependent (ZMod 2) ![x, y] →
      ¬ good av (span (ZMod 2) {x, y}) c) :
    ∃ (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (o : ZMod 2),
      ∀ x : Fin n → ZMod 2, x ≠ 0 → ∀ b ∈ av x, b = l x + o := by
  set f := sel av hne
  have hsum : ∀ x y : Fin n → ZMod 2, LinearIndependent (ZMod 2) ![x, y] →
      f x + f y + f (x + y) = c + 1 := by
    intro x y h
    obtain ⟨hx, hy, hxy⟩ := indep_facts h
    by_contra hc
    apply hbad x y h
    by_contra hc2
    exact hc (arith3 _ _ _ _ (fun e => hc2 (good_of_pair av h f _ e (sel_mem av hne hx)
      (sel_mem av hne hy) (sel_mem av hne hxy)))) |>.elim
  let l0 : (Fin n → ZMod 2) → ZMod 2 := fun z => if z = 0 then 0 else f z + (c + 1)
  have hadd : ∀ x y, l0 (x + y) = l0 x + l0 y := by
    intro x y
    by_cases hx : x = 0
    · subst hx; simp [l0]
    by_cases hy : y = 0
    · subst hy; simp [l0]
    by_cases hxy : x = y
    · subst hxy; simp only [l0, self_add, if_true, if_neg hx]
      generalize f x + (c + 1) = a; revert a; decide
    have hi := indep_of hx hy hxy
    have hs := hsum x y hi
    have hxy0 := (indep_facts hi).2.2
    simp only [l0, if_neg hx, if_neg hy, if_neg hxy0]
    exact (arith4 _ _ _ _ hs).symm
  let l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (AddMonoidHom.mk' l0 hadd).toZModLinearMap 2
  refine ⟨l, c + 1, fun x hx b hb => ?_⟩
  have hlx : l x = f x + (c + 1) := by
    show l0 x = _; simp only [l0, if_neg hx]
  rw [hlx, ← arith6]
  by_contra hbx
  obtain ⟨y, hi⟩ := other_vec hn hx
  obtain ⟨_, hy, hxy⟩ := indep_facts hi
  have hyx : y ≠ x := fun e => by
    rw [LinearIndependent.pair_iff] at hi
    have := hi 1 1 (by rw [e, one_smul, self_add]); exact absurd this.1 (by decide)
  have hxyx : x + y ≠ x := fun e => hy (by simpa using e)
  apply hbad x y hi
  refine good_of_pair av hi (Function.update f x b) c ?_ ?_ ?_ ?_
  · rw [Function.update_self, Function.update_of_ne hyx, Function.update_of_ne hxyx]
    exact arith5 _ _ _ _ _ (hsum x y hi) hbx
  · rw [Function.update_self]; exact hb
  · rw [Function.update_of_ne hyx]; exact sel_mem av hne hy
  · rw [Function.update_of_ne hxyx]; exact sel_mem av hne hxy


theorem proper3 {n : ℕ} (hn : 4 ≤ n) (a b r : Fin n → ZMod 2) :
    span (ZMod 2) ({a, b, r} : Set (Fin n → ZMod 2)) ≠ ⊤ := by
  intro h
  have h1 := finrank_span_finset_le_card (R := ZMod 2) ({a, b, r} : Finset (Fin n → ZMod 2))
  have h2 : (({a, b, r} : Finset (Fin n → ZMod 2)) : Set (Fin n → ZMod 2)) = {a, b, r} := by
    simp
  unfold Set.finrank at h1
  rw [h2, h, finrank_top, Module.finrank_fin_fun] at h1
  have := Finset.card_le_three (a := a) (b := b) (c := r)
  omega

theorem avoid {n : ℕ} {A B : Submodule (ZMod 2) (Fin n → ZMod 2)} (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    ∃ x, x ∉ A ∧ x ∉ B := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ A := by
    by_contra hc; push_neg at hc; exact hA (eq_top_iff.2 fun x _ => hc x)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ B := by
    by_contra hc; push_neg at hc; exact hB (eq_top_iff.2 fun x _ => hc x)
  by_cases haB : a ∈ B
  · by_cases hbA : b ∈ A
    · refine ⟨a + b, fun h => ?_, fun h => ?_⟩
      · exact ha (by have := A.sub_mem h hbA; simpa using this)
      · exact hb (by have := B.sub_mem h haB; simpa using this)
    · exact ⟨b, hbA, hb⟩
  · exact ⟨a, ha, haB⟩

theorem le3 {n : ℕ} (a b r : Fin n → ZMod 2) :
    span (ZMod 2) ({a, b} : Set (Fin n → ZMod 2)) ≤ span (ZMod 2) {a, b, r} :=
  span_mono (by intro w hw; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢; tauto)

theorem disj {n : ℕ} {r s a b : Fin n → ZMod 2} (hr : r ∉ span (ZMod 2) ({a, b} : Set _))
    (hs : s ∉ span (ZMod 2) ({a, b, r} : Set _)) :
    Disjoint (span (ZMod 2) ({r, s} : Set (Fin n → ZMod 2))) (span (ZMod 2) {a, b}) := by
  rw [Submodule.disjoint_def]
  intro z hz hzP
  obtain ⟨α, β, rfl⟩ := mem_span_pair.1 hz
  have hrm : r ∈ span (ZMod 2) ({a, b, r} : Set (Fin n → ZMod 2)) := subset_span (by simp)
  rcases z2 α with rfl | rfl <;> rcases z2 β with rfl | rfl
  · simp
  · simp only [zero_smul, one_smul, zero_add] at hzP; exact absurd (le3 a b r hzP) hs
  · simp only [zero_smul, one_smul, add_zero] at hzP; exact absurd hzP hr
  · simp only [one_smul] at hzP
    exact absurd (by have := sub_mem (le3 a b r hzP) hrm; simpa using this) hs

theorem common {n : ℕ} (hn : 4 ≤ n) (a b c d : Fin n → ZMod 2) :
    ∃ r s : Fin n → ZMod 2, LinearIndependent (ZMod 2) ![r, s] ∧
      Disjoint (span (ZMod 2) ({r, s} : Set _)) (span (ZMod 2) {a, b}) ∧
      Disjoint (span (ZMod 2) ({r, s} : Set _)) (span (ZMod 2) {c, d}) := by
  obtain ⟨r, hr1, hr2⟩ := avoid (ne_top_of_le_ne_top (proper3 hn a b a) (le3 a b a))
    (ne_top_of_le_ne_top (proper3 hn c d c) (le3 c d c))
  obtain ⟨s, hs1, hs2⟩ := avoid (proper3 hn a b r) (proper3 hn c d r)
  have hrm : r ∈ span (ZMod 2) ({a, b, r} : Set (Fin n → ZMod 2)) := subset_span (by simp)
  refine ⟨r, s, ?_, disj hr1 hs1, disj hr2 hs2⟩
  rw [LinearIndependent.pair_iff]
  intro α β h
  rcases z2 α with rfl | rfl <;> rcases z2 β with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact absurd (h ▸ zero_mem _) hs1
  · simp only [zero_smul, one_smul, add_zero] at h
    exact absurd (h ▸ zero_mem _) hr1
  · simp only [one_smul] at h
    have e : s = (r + s) - r := by abel
    exact absurd (by rw [e, h]; exact sub_mem (zero_mem _) hrm) hs1

theorem three_points {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hU : finrank (ZMod 2) U = 2) :
    ∃ x y, x ∈ U ∧ y ∈ U ∧ x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 := by
  let bU := Module.finBasisOfFinrankEq (ZMod 2) U hU
  refine ⟨bU 0, bU 1, (bU 0).2, (bU 1).2, ?_, ?_, ?_⟩
  · intro h; exact bU.ne_zero 0 (Subtype.ext h)
  · intro h; exact bU.ne_zero 1 (Subtype.ext h)
  · intro h
    have hli := bU.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun _ => 1) (by
      rw [Fin.sum_univ_two]; simp only [one_smul]; exact Subtype.ext (by simpa using h))
    exact absurd (this 0) (by decide)

theorem arith7 : ∀ mx my lx ly o : ZMod 2, 1 + mx = lx + o → 1 + my = ly + o →
    1 + (mx + my) = (lx + ly) + o → o = 1 := by decide
theorem arith8 : ∀ mx my lx ly o : ZMod 2, mx = lx + o → my = ly + o →
    mx + my = (lx + ly) + o → o = 0 := by decide

theorem assemble {n : ℕ} (av : (Fin n → ZMod 2) → Finset (ZMod 2))
    (U T : Submodule (ZMod 2) (Fin n → ZMod 2)) (hd : Disjoint U T)
    (hU : finrank (ZMod 2) U = 2) (hT : finrank (ZMod 2) T = 2) (gU : good av U 1)
    (gT : good av T 0) :
    ∃ (U T : Submodule (ZMod 2) (Fin n → ZMod 2)) (mask : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      Disjoint U T ∧ Module.finrank (ZMod 2) U = 2 ∧ Module.finrank (ZMod 2) T = 2 ∧
      (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ av x) ∧
      (∀ x ∈ T, x ≠ 0 → mask x ∈ av x) := by
  obtain ⟨m1, hm1⟩ := gU
  obtain ⟨m2, hm2⟩ := gT
  obtain ⟨m, e1, e2⟩ := combine U T hd m1 m2
  refine ⟨U, T, m, hd, hU, hT, fun x hx hx0 => ?_, fun x hx hx0 => ?_⟩
  · rw [e1 x hx, add_comm]; exact hm1 x hx hx0
  · rw [e2 x hx]; simpa using hm2 x hx hx0

end PEqualNP.Outside.L_lib_759

open PEqualNP.Outside.L_lib_759 in
theorem PEqualNP.Outside.L_lib_759 : ∀ (n : Nat), 4 ≤ n →
  let F := ZMod 2
  let V := Fin n → F
  ∀ (available : V → Finset F), (∀ x : V, x ≠ 0 → (available x).Nonempty) →
    Iff (∃ (U T : Submodule F V) (mask : V →ₗ[F] F),
      Disjoint U T ∧ Module.finrank F U = 2 ∧ Module.finrank F T = 2 ∧
      (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ available x) ∧
      (∀ x ∈ T, x ≠ 0 → mask x ∈ available x))
    (¬(∃ (linear : V →ₗ[F] F) (offset : F), ∀ x : V, x ≠ 0 →
        ∀ b ∈ available x, b = linear x + offset)) := by
  intro n hn
  dsimp only
  intro av hne
  constructor
  · rintro ⟨U, T, mask, hd, hU, hT, h1, h0⟩ ⟨l, o, hl⟩
    obtain ⟨x, y, hx, hy, hx0, hy0, hxy0⟩ := three_points U hU
    have e1 := hl x hx0 _ (h1 x hx hx0)
    have e2 := hl y hy0 _ (h1 y hy hy0)
    have e3 := hl (x + y) hxy0 _ (h1 (x + y) (U.add_mem hx hy) hxy0)
    rw [map_add, map_add] at e3
    have ho1 := arith7 _ _ _ _ _ e1 e2 e3
    obtain ⟨u, v, hu, hv, hu0, hv0, huv0⟩ := three_points T hT
    have f1 := hl u hu0 _ (h0 u hu hu0)
    have f2 := hl v hv0 _ (h0 v hv hv0)
    have f3 := hl (u + v) huv0 _ (h0 (u + v) (T.add_mem hu hv) huv0)
    rw [map_add, map_add] at f3
    have ho0 := arith8 _ _ _ _ _ f1 f2 f3
    rw [ho1] at ho0
    exact absurd ho0 (by decide)
  · intro hna
    have hex : ∀ c : ZMod 2, ∃ x y : Fin n → ZMod 2, LinearIndependent (ZMod 2) ![x, y] ∧
        good av (Submodule.span (ZMod 2) {x, y}) c := by
      intro c
      by_contra hc
      push_neg at hc
      exact hna (affine_of_bad (by omega) av hne c hc)
    obtain ⟨x1, y1, hi1, g1⟩ := hex 1
    obtain ⟨x0, y0, hi0, g0⟩ := hex 0
    obtain ⟨r, s, hrs, hd1, hd0⟩ := common hn x1 y1 x0 y0
    obtain ⟨c, gc⟩ := good_any av hne hrs
    rcases z2 c with rfl | rfl
    · exact assemble av _ _ hd1.symm (finrank2 hi1) (finrank2 hrs) g1 gc
    · exact assemble av _ _ hd0 (finrank2 hrs) (finrank2 hi0) gc g0
