import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_810

open Finset

abbrev V (k : ℕ) := Fin k → ZMod 2

theorem two_zero {k : ℕ} : (2 : V k) = 0 := by
  funext i
  show (2 : ZMod 2) = 0
  decide

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

def Sp {k : ℕ} (K R : Finset (V k)) : Prop :=
  ∀ s ∈ K, ∀ x ∈ R, x - s ∈ Submodule.span (ZMod 2) (↑(K.image (· - s)) : Set (V k))

theorem gen_mem {k : ℕ} (K : Finset (V k)) (s x : V k) (hx : x ∈ K) :
    x - s ∈ Submodule.span (ZMod 2) (↑(K.image (· - s)) : Set (V k)) :=
  Submodule.subset_span (by
    simp only [coe_image, Set.mem_image, mem_coe]
    exact ⟨x, hx, rfl⟩)

theorem span_le_of {k : ℕ} (S : Finset (V k)) (s s1 : V k) (hs : s ∈ S)
    (M : Submodule (ZMod 2) (V k)) (h : ∀ x ∈ S, x - s1 ∈ M) :
    Submodule.span (ZMod 2) (↑(S.image (· - s)) : Set (V k)) ≤ M := by
  rw [Submodule.span_le]
  intro y hy
  simp only [coe_image, Set.mem_image, mem_coe] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := M.sub_mem (h x hx) (h s hs)
  simpa using this

theorem rebase {k : ℕ} (S T R : Finset (V k)) (s0 : V k) (hs0 : s0 ∈ S)
    (hR : ∀ y ∈ R, y - s0 ∈ Submodule.span (ZMod 2) (↑(S.image (· - s0)) : Set (V k)))
    (hT : Sp T S) : Sp T R := by
  intro s1 hs1 y hy
  have hle := span_le_of S s0 s1 hs0 _ (fun x hx => hT s1 hs1 x hx)
  have := Submodule.add_mem _ (hle (hR y hy)) (hT s1 hs1 s0 hs0)
  simpa using this

theorem select {k : ℕ} (S : Finset (V k)) (hS : S.Nonempty) :
    ∃ T ⊆ S, T.Nonempty ∧ T.card ≤ k + 1 ∧ Sp T S := by
  classical
  obtain ⟨s0, hs0⟩ := hS
  set D := S.image (· - s0) with hD
  obtain ⟨B, hBD, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (↑D : Set (V k))
  set Bf := D.filter (· ∈ B) with hBf
  have hBfc : (↑Bf : Set (V k)) = B := by
    ext x
    simp only [hBf, coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨hBD h, h⟩
  rw [← hBfc] at hli hspan
  have hcard : Bf.card ≤ k := by
    have := hli.finset_card_le_finrank
    simpa using this
  set T := insert s0 (Bf.image (· + s0)) with hTdef
  have hTS : T ⊆ S := by
    intro x hx
    rw [hTdef, mem_insert, mem_image] at hx
    rcases hx with rfl | ⟨β, hβ, rfl⟩
    · exact hs0
    · have : β ∈ D := (mem_filter.1 hβ).1
      rw [hD, mem_image] at this
      obtain ⟨x, hx, rfl⟩ := this
      simpa using hx
  refine ⟨T, hTS, ⟨s0, mem_insert_self _ _⟩, ?_, ?_⟩
  · calc T.card ≤ (Bf.image (fun x : V k => x + s0)).card + 1 := card_insert_le _ _
      _ ≤ Bf.card + 1 := by
        have := card_image_le (s := Bf) (f := fun x : V k => x + s0)
        omega
      _ ≤ k + 1 := by omega
  · have base : ∀ x ∈ S,
        x - s0 ∈ Submodule.span (ZMod 2) (↑(T.image (· - s0)) : Set (V k)) := by
      intro x hx
      have h1 : x - s0 ∈ Submodule.span (ZMod 2) (↑D : Set (V k)) :=
        Submodule.subset_span (by
          simp only [hD, coe_image, Set.mem_image, mem_coe]
          exact ⟨x, hx, rfl⟩)
      rw [← hspan] at h1
      refine Submodule.span_mono ?_ h1
      intro β hβ
      simp only [coe_image, Set.mem_image, mem_coe, hTdef, mem_insert, mem_image]
      exact ⟨β + s0, Or.inr ⟨β, hβ, rfl⟩, by simp⟩
    intro s1 hs1 y hy
    have hle := span_le_of T s0 s1 (mem_insert_self _ _) _ (fun x hx => gen_mem T s1 x hx)
    have := Submodule.sub_mem _ (hle (base y hy)) (hle (base s1 (hTS hs1)))
    simpa using this

def dotL {k : ℕ} (a : V k) : V k →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, sum_add_distrib]
  map_smul' c x := by simp [mul_sum, mul_left_comm]

theorem eqn {k : ℕ} (K R : Finset (V k)) (hKR : K ⊆ R) (hK : K.Nonempty) (hsp : Sp K R)
    (a : V k) (b : ZMod 2) :
    (∀ x ∈ K, ∑ i, a i * x i = b) ↔ (∀ x ∈ R, ∑ i, a i * x i = b) := by
  constructor
  · intro h x hx
    obtain ⟨s, hs⟩ := hK
    have hle : Submodule.span (ZMod 2) (↑(K.image (· - s)) : Set (V k)) ≤
        LinearMap.ker (dotL a) := by
      rw [Submodule.span_le]
      intro y hy
      simp only [coe_image, Set.mem_image, mem_coe] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      show dotL a (t - s) = 0
      rw [map_sub]
      show (∑ i, a i * t i) - (∑ i, a i * s i) = 0
      rw [h t ht, h s hs, sub_self]
    have h1 := hle (hsp s hs x hx)
    rw [LinearMap.mem_ker, map_sub] at h1
    have h2 : dotL a x = dotL a s := sub_eq_zero.1 h1
    show dotL a x = b
    rw [h2]
    exact h s hs
  · intro h x hx
    exact h x (hKR hx)

def pol {k : ℕ} (Q : V k → V k) (u v : V k) : V k := Q (u + v) + Q u + Q v + Q 0

def stepF {k : ℕ} (Q : V k → V k) (κ : V k) (D X : Finset (V k)) : Finset (V k) :=
  (D.product X).image (fun p => Q (p.2 + p.1) + Q p.2 + κ)

def baseF (k : ℕ) : Finset (V k) :=
  insert (0 : V k) (Finset.univ.image (fun (pivot i : Fin k) => if i = pivot then (1 : ZMod 2) else 0))

theorem pol_symm {k : ℕ} (Q : V k → V k) (u v : V k) : pol Q u v = pol Q v u := by
  unfold pol
  rw [add_comm u v]
  abel

theorem pol_zero {k : ℕ} (Q : V k → V k) (w : V k) : pol Q 0 w = 0 := by
  unfold pol
  rw [zero_add]
  linear_combination (Q w + Q 0) * (two_zero (k := k))

def PL {k : ℕ} (Q : V k → V k)
    (hpol : ∀ u v w : V k, pol Q (u + v) w = pol Q u w + pol Q v w) (w : V k) :
    V k →ₗ[ZMod 2] V k where
  toFun u := pol Q u w
  map_add' u v := hpol u v w
  map_smul' c u := by
    rcases zmod2_cases c with rfl | rfl
    · simp [pol_zero]
    · simp

theorem stepSpan {k : ℕ} (Q : V k → V k) (κ : V k)
    (hpol : ∀ u v w : V k, pol Q (u + v) w = pol Q u w + pol Q v w)
    (K R : Finset (V k)) (hK : K.Nonempty) (hsp : Sp K R) :
    ∃ s0 ∈ stepF Q κ K (baseF k), ∀ y ∈ stepF Q κ R univ,
      y - s0 ∈ Submodule.span (ZMod 2) (↑((stepF Q κ K (baseF k)).image (· - s0)) : Set (V k)) := by
  classical
  have h2 := two_zero (k := k)
  obtain ⟨d0, hd0⟩ := hK
  set S' := stepF Q κ K (baseF k) with hS'
  set s0 := Q (0 + d0) + Q 0 + κ with hs0
  have memS : ∀ t ∈ K, ∀ x ∈ baseF k, Q (x + t) + Q x + κ ∈ S' := by
    intro t ht x hx
    rw [hS', stepF, mem_image]
    exact ⟨(t, x), mem_product.2 ⟨ht, hx⟩, rfl⟩
  have hs0S : s0 ∈ S' := memS d0 hd0 0 (mem_insert_self _ _)
  set W' := Submodule.span (ZMod 2) (↑(S'.image (· - s0)) : Set (V k)) with hW'
  have m1 : ∀ t ∈ K, Q t - Q d0 ∈ W' := by
    intro t ht
    have := gen_mem S' s0 _ (memS t ht 0 (mem_insert_self _ _))
    have e : Q (0 + t) + Q 0 + κ - s0 = Q t - Q d0 := by
      rw [hs0, zero_add, zero_add]
      abel
    rwa [e] at this
  have m2 : ∀ t ∈ K, ∀ p : Fin k,
      pol Q (fun i => if i = p then (1 : ZMod 2) else 0) t ∈ W' := by
    intro t ht p
    have hp : (fun i => if i = p then (1 : ZMod 2) else 0) ∈ baseF k := by
      rw [baseF]
      exact mem_insert_of_mem (mem_image.2 ⟨p, mem_univ _, rfl⟩)
    have a1 := gen_mem S' s0 _ (memS t ht _ hp)
    have a0 := gen_mem S' s0 _ (memS t ht 0 (mem_insert_self _ _))
    have := W'.sub_mem a1 a0
    convert this using 1
    unfold pol
    rw [zero_add]
    linear_combination (Q t + Q 0) * h2
  have m3 : ∀ t ∈ K, ∀ x, pol Q x t ∈ W' := by
    intro t ht x
    have hx : x = ∑ p : Fin k, x p • (fun i => if i = p then (1 : ZMod 2) else 0) := by
      funext i
      simp [Finset.sum_apply]
    have : PL Q hpol t x ∈ W' := by
      rw [hx, map_sum]
      refine Submodule.sum_mem _ (fun p _ => ?_)
      rw [map_smul]
      exact W'.smul_mem _ (m2 t ht p)
    exact this
  set U := Submodule.span (ZMod 2) (↑(K.image (· - d0)) : Set (V k)) with hU
  have m4 : ∀ v ∈ U, ∀ x, pol Q x v ∈ W' := by
    intro v hv x
    have hle : U ≤ W'.comap (PL Q hpol x) := by
      rw [hU, Submodule.span_le]
      intro y hy
      simp only [coe_image, Set.mem_image, mem_coe] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      show PL Q hpol x (t - d0) ∈ W'
      rw [map_sub]
      show pol Q t x - pol Q d0 x ∈ W'
      rw [pol_symm Q t x, pol_symm Q d0 x]
      exact W'.sub_mem (m3 t ht x) (m3 d0 hd0 x)
    have := hle hv
    show pol Q x v ∈ W'
    rw [pol_symm]
    exact this
  have m5 : ∀ v ∈ U, Q (d0 + v) - Q d0 ∈ W' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      simp only [coe_image, Set.mem_image, mem_coe] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      rw [add_sub_cancel]
      exact m1 t ht
    | zero => simp
    | add v w hv hw ihv ihw =>
      have e : Q (d0 + (v + w)) - Q d0 =
          (Q (d0 + v) - Q d0) + pol Q (d0 + v) w + pol Q d0 w + (Q (d0 + w) - Q d0) := by
        unfold pol
        rw [← add_assoc]
        linear_combination (-(Q (d0 + v) + Q w + Q 0 + Q (d0 + w))) * h2
      rw [e]
      exact W'.add_mem (W'.add_mem (W'.add_mem ihv (m4 w hw _)) (m4 w hw _)) ihw
    | smul c v hv ih =>
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using ih
  refine ⟨s0, hs0S, fun y hy => ?_⟩
  rw [stepF, mem_image] at hy
  obtain ⟨⟨d, x⟩, hp, rfl⟩ := hy
  have hd : d ∈ R := (mem_product.1 hp).1
  set v := d - d0 with hv
  have hvU : v ∈ U := hsp d0 hd0 d hd
  have hdv : d = d0 + v := by rw [hv]; abel
  have hpd : pol Q x d = pol Q x d0 + pol Q x v := by
    rw [pol_symm, hdv, hpol, pol_symm Q d0, pol_symm Q v]
  have e : Q (x + d) + Q x + κ - s0 = pol Q x d + (Q d - Q d0) := by
    rw [hs0, zero_add]
    unfold pol
    linear_combination (-(Q 0 + Q d)) * h2
  show Q (x + d) + Q x + κ - s0 ∈ W'
  rw [e, hpd]
  have m5' := m5 v hvU
  rw [← hdv] at m5'
  exact W'.add_mem (W'.add_mem (m3 d0 hd0 x) (m4 v hvU x)) m5'

noncomputable def sel {k : ℕ} (S : Finset (V k)) : Finset (V k) :=
  if h : S.Nonempty then Classical.choose (select S h) else ∅

theorem sel_sub {k : ℕ} (S : Finset (V k)) : sel S ⊆ S := by
  unfold sel
  split_ifs with h
  · exact (Classical.choose_spec (select S h)).1
  · exact empty_subset _

theorem sel_spec {k : ℕ} (S : Finset (V k)) (h : S.Nonempty) :
    (sel S).Nonempty ∧ (sel S).card ≤ k + 1 ∧ Sp (sel S) S := by
  unfold sel
  rw [dif_pos h]
  exact (Classical.choose_spec (select S h)).2

theorem step_mono {k : ℕ} (Q : V k → V k) (κ : V k) (K R : Finset (V k)) (h : K ⊆ R) :
    stepF Q κ K (baseF k) ⊆ stepF Q κ R univ := by
  unfold stepF
  exact image_subset_image (product_subset_product h (subset_univ _))

end PEqualNP.Outside.L_lib_810

open PEqualNP.Outside.L_lib_810 in
theorem PEqualNP.Outside.L_lib_810 : ∀ (k r : ℕ),
  let W := Fin k → ZMod 2
  ∀ (Q : Fin r → W → W) (kick : Fin r → W) (initial : W),
    let polar := fun (j : Fin r) (u v : W) => Q j (u+v) + Q j u + Q j v + Q j 0
    (∀ (j : Fin r) (u v w : W), polar j (u+v) w = polar j u w + polar j v w) →
    let unit := fun (pivot i : Fin k) => if i=pivot then (1 : ZMod 2) else 0
    let base : Finset W := insert (0 : W) (Finset.univ.image unit)
    let step := fun (j : Fin r) (D X : Finset W) => (D.product X).image
      (fun p => Q j (p.2+p.1) + Q j p.2 + kick j)
    let reached := fun n : ℕ => ((List.finRange r).take n).foldl
      (fun S j => step j S Finset.univ) {initial}
    let dot := fun (a x : W) => ∑ i : Fin k, a i * x i
    ∃ keep : ℕ → Finset W, keep 0 = {initial} ∧
      (∀ j : Fin r, keep (j.val+1) ⊆ step j (keep j.val) base) ∧
      ∀ n ≤ r, (keep n).card ≤ k+1 ∧ keep n ⊆ reached n ∧
        ∀ (a : W) (b : ZMod 2),
          (∀ x ∈ keep n, dot a x = b) ↔ (∀ x ∈ reached n, dot a x = b) := by
  intro k r W Q kick initial polar hpol unit base step reached dot
  have hpol' : ∀ j : Fin r, ∀ u v w : V k, pol (Q j) (u + v) w = pol (Q j) u w + pol (Q j) v w :=
    fun j u v w => hpol j u v w
  have hstep : ∀ j D X, step j D X = stepF (Q j) (kick j) D X := fun _ _ _ => rfl
  have hbase : base = baseF k := rfl
  have hr0 : reached 0 = {initial} := rfl
  have hrs : ∀ m (h : m < r), reached (m + 1) = step ⟨m, h⟩ (reached m) Finset.univ := by
    intro m h
    show ((List.finRange r).take (m + 1)).foldl _ _ = _
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h), List.foldl_append]
    simp
    rfl
  have hdot : ∀ a x, dot a x = ∑ i : Fin k, a i * x i := fun _ _ => rfl
  clear_value dot reached step base polar unit
  obtain ⟨keep, hk0, hks⟩ : ∃ keep : ℕ → Finset W, keep 0 = {initial} ∧
      ∀ m (h : m < r), keep (m + 1) = sel (step ⟨m, h⟩ (keep m) base) :=
    ⟨fun n => Nat.rec (motive := fun _ => Finset W) {initial}
      (fun m K => if h : m < r then sel (step ⟨m, h⟩ K base) else ∅) n, rfl,
      fun m h => dif_pos h⟩
  have inv : ∀ n ≤ r, keep n ⊆ reached n ∧ (keep n).Nonempty ∧ (keep n).card ≤ k + 1 ∧
      Sp (keep n) (reached n) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [hk0, hr0]
      refine ⟨subset_refl _, Finset.singleton_nonempty _, by simp, ?_⟩
      intro s hs x hx
      rw [Finset.mem_singleton] at hs hx
      subst hs hx
      simp
    | succ m ih =>
      intro hm
      have hmr : m < r := by omega
      obtain ⟨hKR, hKne, -, hsp⟩ := ih (by omega)
      obtain ⟨s0, hs0, hspan⟩ := stepSpan (Q ⟨m, hmr⟩) (kick ⟨m, hmr⟩) (hpol' _)
        (keep m) (reached m) hKne hsp
      have hne : (stepF (Q ⟨m, hmr⟩) (kick ⟨m, hmr⟩) (keep m) (baseF k)).Nonempty := ⟨s0, hs0⟩
      obtain ⟨hTne, hTc, hTsp⟩ := sel_spec _ hne
      rw [hks m hmr, hrs m hmr, hstep, hstep, hbase]
      refine ⟨(sel_sub _).trans (step_mono _ _ _ _ hKR), hTne, hTc, ?_⟩
      exact rebase _ _ _ s0 hs0 hspan hTsp
  refine ⟨keep, hk0, ?_, ?_⟩
  · intro j
    rw [hks j.val j.isLt]
    exact sel_sub _
  · intro n hn
    obtain ⟨hKR, hKne, hc, hsp⟩ := inv n hn
    refine ⟨hc, hKR, fun a b => ?_⟩
    simp only [hdot]
    exact eqn _ _ hKR hKne hsp a b
