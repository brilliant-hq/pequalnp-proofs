import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_579

open Finset
open Fin.NatCast Fin.CommRing

theorem card_le_of_dual {K : Type} [Field K] {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → (Fin d → K)) (g : ι → (Fin d → K) →ₗ[K] K)
    (h : ∀ σ τ, g τ (f σ) = if σ = τ then 1 else 0) : Fintype.card ι ≤ d := by
  have hli : LinearIndependent K f := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have hc := congrArg (g i) hs
    simp only [map_sum, map_smul, smul_eq_mul, h, map_zero, mul_ite, mul_one, mul_zero] at hc
    rw [Finset.sum_eq_single i] at hc
    · simpa using hc
    · intro j _ hji; simp [hji]
    · intro hni; exact absurd hi hni
  have := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using this

theorem foldl_lin {K : Type} [Field K] {d : ℕ} {α : Type}
    (F : α → (Fin d → K) →ₗ[K] (Fin d → K)) (l : List α)
    (M : (Fin d → K) →ₗ[K] (Fin d → K)) (v : Fin d → K) :
    l.foldl (fun v j => F j v) (M v) = (l.foldl (fun M j => (F j).comp M) M) v := by
  induction l generalizing M with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih ((F x).comp M)

theorem foldl_congr' {β α : Type} (f f' : β → α → β) (l : List α) (b : β)
    (h : ∀ x ∈ l, ∀ b, f b x = f' b x) : l.foldl f b = l.foldl f' b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih _ (fun y hy b => h y (by simp [hy]) b)

theorem lt_of_mem_take {N k : ℕ} {j : Fin N} (hj : j ∈ (List.finRange N).take k) :
    j.val < k := by
  obtain ⟨m, hm, he⟩ := List.getElem_of_mem hj
  simp only [List.getElem_take, List.getElem_finRange] at he
  subst he
  simp only [List.length_take, List.length_finRange] at hm
  simp only [Fin.val_cast]
  omega

theorem le_of_mem_drop {N k : ℕ} {j : Fin N} (hj : j ∈ (List.finRange N).drop k) :
    k ≤ j.val := by
  obtain ⟨m, hm, he⟩ := List.getElem_of_mem hj
  simp only [List.getElem_drop, List.getElem_finRange] at he
  subst he
  simp only [Fin.val_cast]
  omega

theorem exists_pred_not_mem {N : ℕ} [NeZero N] (B : Finset (Fin N)) (hne : B.Nonempty)
    (hnu : B ≠ univ) : ∃ u ∈ B, u - 1 ∉ B := by
  by_contra hc
  push_neg at hc
  obtain ⟨b, hb⟩ := hne
  have key : ∀ m : ℕ, b - (m : Fin N) ∈ B := by
    intro m
    induction m with
    | zero => simpa using hb
    | succ m ih =>
      have := hc _ ih
      simpa [sub_sub, Nat.cast_succ] using this
  apply hnu
  ext u
  simp only [mem_univ, iff_true]
  have := key ((b - u).val)
  simpa using this

theorem card_A_le {N : ℕ} [NeZero N] (X : Finset (Fin N)) (hX : X ≠ univ) (w : ℕ) :
    (univ.filter (fun t : Fin N => ∀ j ≤ w, t - (j : Fin N) ∈ X)).card + min X.card w
      ≤ X.card := by
  set A := univ.filter (fun t : Fin N => ∀ j ≤ w, t - (j : Fin N) ∈ X) with hA
  rcases A.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  let B : ℕ → Finset (Fin N) := fun m => univ.filter (fun u => ∃ j ≤ m, u + (j : Fin N) ∈ A)
  have hAB : ∀ m, A ⊆ B m := by
    intro m u hu
    simp only [B, mem_filter, mem_univ, true_and]
    exact ⟨0, Nat.zero_le _, by simpa using hu⟩
  have hBX : ∀ m ≤ w, B m ⊆ X := by
    intro m hm u hu
    simp only [B, mem_filter, mem_univ, true_and] at hu
    obtain ⟨j, hj, hjA⟩ := hu
    simp only [hA, mem_filter, mem_univ, true_and] at hjA
    have := hjA j (le_trans hj hm)
    simpa using this
  have hcard : ∀ m ≤ w, A.card + m ≤ (B m).card := by
    intro m
    induction m with
    | zero => intro _; simpa using card_le_card (hAB 0)
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hsub : B m ⊆ B (m + 1) := by
        intro u hu
        simp only [B, mem_filter, mem_univ, true_and] at hu ⊢
        obtain ⟨j, hj, hjA⟩ := hu
        exact ⟨j, by omega, hjA⟩
      have hne' : (B m).Nonempty := hne.mono (hAB m)
      have hnu' : B m ≠ univ := by
        intro heq
        apply hX
        apply eq_univ_of_forall
        intro x
        exact hBX m (by omega) (heq ▸ mem_univ x)
      obtain ⟨u, hu, hu1⟩ := exists_pred_not_mem (B m) hne' hnu'
      have hu1' : u - 1 ∈ B (m + 1) := by
        simp only [B, mem_filter, mem_univ, true_and] at hu ⊢
        obtain ⟨j, hj, hjA⟩ := hu
        refine ⟨j + 1, by omega, ?_⟩
        have : u - 1 + ((j + 1 : ℕ) : Fin N) = u + (j : Fin N) := by
          push_cast; ring
        rw [this]; exact hjA
      have hss : B m ⊂ B (m + 1) := (Finset.ssubset_iff_of_subset hsub).2 ⟨u - 1, hu1', hu1⟩
      have := Finset.card_lt_card hss
      omega
  have h1 := hcard w le_rfl
  have h2 := card_le_card (hBX w le_rfl)
  have h3 : min X.card w ≤ w := min_le_right _ _
  omega

theorem ofNat_add (a : ℕ) (i : Fin (a + 2)) (j : ℕ) :
    Fin.ofNat (a + 2) (i.val + j) = i + (j : Fin (a + 2)) := by
  ext
  simp [Fin.val_add, Fin.val_natCast, Nat.add_mod]

def extA {N : ℕ} (Sh : Finset (Fin N)) (σ : Sh → Bool) (t : Fin N) : Bool :=
  if h : t ∈ Sh then σ ⟨t, h⟩ else false

def Tp (a w : ℕ) (Sh : Finset (Fin (a + 2))) (σ : Sh → Bool) (i : Fin (a + 2))
    (y : Fin (w + 1) → Bool) : Bool :=
  decide (∀ j : Fin (w + 1), y j = extA Sh σ (Fin.ofNat (a + 2) (i.val + j.val)))

theorem ofNat_self (a w : ℕ) (t : Fin (a + 2)) :
    Fin.ofNat (a + 2) (t.val + (0 : Fin (w + 1)).val) = t := by
  ext
  simp

theorem fool_count (a w : ℕ) (Sh : Finset (Fin (a + 2))) (pref : Fin (a + 2) → Prop)
    [DecidablePred pref]
    (hSh : ∀ t ∈ Sh, (∃ i, pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t) ∧
      (∃ i, ¬ pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t))
    (σ τ : Sh → Bool) :
    (univ.filter (fun x : Fin (a + 2) → Bool => ∀ i : Fin (a + 2),
      (if pref i then Tp a w Sh σ i else Tp a w Sh τ i)
        (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card
      = if σ = τ then 1 else 0 := by
  split_ifs with hst
  · subst hst
    rw [Finset.card_eq_one]
    refine ⟨extA Sh σ, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton, ite_self, Tp, decide_eq_true_eq]
    constructor
    · intro hx
      funext t
      have := hx t 0
      rwa [ofNat_self] at this
    · rintro rfl i j
      rfl
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply hst
    funext s
    obtain ⟨⟨i, hi, j, hj⟩, ⟨i', hi', j', hj'⟩⟩ := hSh s.val s.property
    have h1 := hx i
    have h2 := hx i'
    simp only [hi, hi', ↓reduceIte, Tp, decide_eq_true_eq] at h1 h2
    have e1 := h1 j
    have e2 := h2 j'
    rw [hj] at e1
    rw [hj'] at e2
    simp only [extA, s.property, ↓reduceDIte] at e1 e2
    rw [← e1, ← e2]

theorem card_lt_filter (N k : ℕ) (hk : k ≤ N) :
    (univ.filter (fun j : Fin N => j.val < k)).card = k := by
  have : (univ.filter (fun j : Fin N => j.val < k)).map Fin.valEmbedding = range k := by
    ext m
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  calc (univ.filter (fun j : Fin N => j.val < k)).card
      = ((univ.filter (fun j : Fin N => j.val < k)).map Fin.valEmbedding).card := (card_map _).symm
    _ = (range k).card := by rw [this]
    _ = k := card_range k

theorem lower {K : Type} [Field K] (a w d : ℕ)
    (order : Equiv.Perm (Fin (a + 2))) (s : Fin d → K)
    (step : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool) → (Fin d → K) →ₗ[K] (Fin d → K))
    (out : (Fin d → K) →ₗ[K] K)
    (h : ∀ T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool),
      out ((List.finRange (a + 2)).foldl (fun v j => step j (T (order j)) v) s) =
        (((Finset.univ : Finset (Fin (a + 2) → Bool)).filter (fun x =>
          ∀ i : Fin (a + 2), T i (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card
          : K)) :
    2 ^ min (a + 2) (2 * w) ≤ d := by
  classical
  set k := (a + 2) / 2 with hk
  let pref : Fin (a + 2) → Prop := fun i => (order.symm i).val < k
  let Sh : Finset (Fin (a + 2)) := univ.filter (fun t =>
    (∃ i, pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t) ∧
    (∃ i, ¬ pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t))
  have hSh : ∀ t ∈ Sh, (∃ i, pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t) ∧
      (∃ i, ¬ pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t) :=
    fun t ht => (mem_filter.1 ht).2
  let f : (Sh → Bool) → (Fin d → K) := fun σ =>
    ((List.finRange (a + 2)).take k).foldl (fun v j => step j (Tp a w Sh σ (order j)) v) s
  let g : (Sh → Bool) → (Fin d → K) →ₗ[K] K := fun τ =>
    out.comp (((List.finRange (a + 2)).drop k).foldl
      (fun M j => (step j (Tp a w Sh τ (order j))).comp M) LinearMap.id)
  have hfg : ∀ σ τ, g τ (f σ) = if σ = τ then 1 else 0 := by
    intro σ τ
    have hT := h (fun i => if pref i then Tp a w Sh σ i else Tp a w Sh τ i)
    rw [fool_count a w Sh pref hSh σ τ] at hT
    rw [← List.take_append_drop k (List.finRange (a + 2)), List.foldl_append] at hT
    have e1 : ((List.finRange (a + 2)).take k).foldl
        (fun v j => step j ((fun i => if pref i then Tp a w Sh σ i else Tp a w Sh τ i) (order j)) v)
        s = f σ := by
      apply foldl_congr'
      intro x hx b
      simp [pref, lt_of_mem_take hx]
    have e2 : ∀ v, ((List.finRange (a + 2)).drop k).foldl
        (fun v j => step j ((fun i => if pref i then Tp a w Sh σ i else Tp a w Sh τ i) (order j)) v)
        v = ((List.finRange (a + 2)).drop k).foldl (fun v j => step j (Tp a w Sh τ (order j)) v) v := by
      intro v
      apply foldl_congr'
      intro x hx b
      simp [pref, Nat.not_lt.2 (le_of_mem_drop hx)]
    rw [e1, e2] at hT
    have hl := foldl_lin (fun j => step j (Tp a w Sh τ (order j)))
      ((List.finRange (a + 2)).drop k) LinearMap.id (f σ)
    simp only [LinearMap.id_apply] at hl
    simp only [g, LinearMap.comp_apply]
    rw [← hl, hT]
    split_ifs <;> simp
  have hcard := card_le_of_dual f g hfg
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hcard
  let P : Finset (Fin (a + 2)) := univ.filter pref
  let Q : Finset (Fin (a + 2)) := univ.filter (fun i => ¬ pref i)
  have hPc : P.card = k := by
    have : P = (univ.filter (fun j : Fin (a + 2) => j.val < k)).map order.toEmbedding := by
      ext i
      simp only [P, pref, mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
      constructor
      · intro hi; exact ⟨order.symm i, hi, by simp⟩
      · rintro ⟨j, hj, rfl⟩; simpa using hj
    rw [this, card_map, card_lt_filter (a + 2) k (by omega)]
  have hQc : Q.card = a + 2 - k := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (a + 2)))) pref
    simp only [card_univ, Fintype.card_fin] at this
    simp only [P] at hPc
    simp only [Q]
    omega
  have hPu : P ≠ univ := by
    intro he
    have := congrArg Finset.card he
    simp only [card_univ, Fintype.card_fin] at this
    omega
  have hQu : Q ≠ univ := by
    intro he
    have := congrArg Finset.card he
    simp only [card_univ, Fintype.card_fin] at this
    omega
  have hAP := card_A_le P hPu w
  have hAQ := card_A_le Q hQu w
  have hcover : (univ : Finset (Fin (a + 2))) ⊆ Sh ∪
      (univ.filter (fun t : Fin (a + 2) => ∀ j ≤ w, t - (j : Fin (a + 2)) ∈ P)) ∪
      (univ.filter (fun t : Fin (a + 2) => ∀ j ≤ w, t - (j : Fin (a + 2)) ∈ Q)) := by
    intro t _
    have rd : ∀ j ≤ w, ∃ jj : Fin (w + 1), Fin.ofNat (a + 2) ((t - (j : Fin (a + 2))).val + jj.val) = t := by
      intro j hj
      refine ⟨⟨j, by omega⟩, ?_⟩
      rw [ofNat_add]
      ring
    by_cases h1 : ∃ i, pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t
    · by_cases h2 : ∃ i, ¬ pref i ∧ ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t
      · simp only [mem_union]
        left; left
        exact mem_filter.2 ⟨mem_univ _, h1, h2⟩
      · simp only [mem_union, mem_filter, mem_univ, true_and]
        left; right
        intro j hj
        simp only [P, mem_filter, mem_univ, true_and]
        by_contra hc
        exact h2 ⟨_, hc, rd j hj⟩
    · simp only [mem_union, mem_filter, mem_univ, true_and]
      right
      intro j hj
      simp only [Q, mem_filter, mem_univ, true_and]
      intro hc
      exact h1 ⟨_, hc, rd j hj⟩
  have hc1 := card_le_card hcover
  have hc2 := card_union_le (Sh ∪ (univ.filter (fun t : Fin (a + 2) => ∀ j ≤ w, t - (j : Fin (a + 2)) ∈ P)))
    (univ.filter (fun t : Fin (a + 2) => ∀ j ≤ w, t - (j : Fin (a + 2)) ∈ Q))
  have hc3 := card_union_le Sh (univ.filter (fun t : Fin (a + 2) => ∀ j ≤ w, t - (j : Fin (a + 2)) ∈ P))
  simp only [card_univ, Fintype.card_fin] at hc1
  rw [hPc] at hAP
  rw [hQc] at hAQ
  have hsh : min (a + 2) (2 * w) ≤ Sh.card := by omega
  calc 2 ^ min (a + 2) (2 * w) ≤ 2 ^ Sh.card := Nat.pow_le_pow_right (by norm_num) hsh
    _ ≤ d := hcard


theorem ofNat_self' (a w : ℕ) (t : Fin (a + 2)) :
    Fin.ofNat (a + 2) (t.val + (0 : Fin (w + 1)).val) = t := by
  ext
  simp

abbrev rd (a w : ℕ) (i t : Fin (a + 2)) : Prop :=
  ∃ j : Fin (w + 1), Fin.ofNat (a + 2) (i.val + j.val) = t

def Dn (a w k : ℕ) : Finset (Fin (a + 2)) :=
  univ.filter (fun t => ∀ i, rd a w i t → i.val < k)

def Fr (a w k : ℕ) : Finset (Fin (a + 2)) :=
  univ.filter (fun t => (∃ i, i.val < k ∧ rd a w i t) ∧ (∃ i, k ≤ i.val ∧ rd a w i t))

def win (a w : ℕ) (i : Fin (a + 2)) (y : Fin (a + 2) → Bool) : Fin (w + 1) → Bool :=
  fun j => y (Fin.ofNat (a + 2) (i.val + j.val))

def Sx (a w k : ℕ) (x : Fin (a + 2) → Bool) : Finset (Fin (a + 2) → Bool) :=
  univ.filter (fun y => ∀ t, t ∉ Dn a w k → y t = x t)

def Sp (a w k : ℕ) (x : Fin (a + 2) → Bool) : Finset (Fin (a + 2) → Bool) :=
  univ.filter (fun y => (∀ t, t ∉ Dn a w (k + 1) → y t = x t) ∧ (∀ t ∈ Dn a w k, y t = x t))

def V {K : Type} [Field K] (a w k : ℕ) (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool))
    (x : Fin (a + 2) → Bool) : K :=
  ∑ y ∈ Sx a w k x, if (∀ i : Fin (a + 2), i.val < k → T i (win a w i y) = true) then 1 else 0

theorem rd_self (a w : ℕ) (t : Fin (a + 2)) : rd a w t t := ⟨0, ofNat_self' a w t⟩

theorem V_zero {K : Type} [Field K] (a w : ℕ) (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool))
    (x : Fin (a + 2) → Bool) : V (K := K) a w 0 T x = 1 := by
  have hS : Sx a w 0 x = {x} := by
    ext y
    simp only [Sx, Dn, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hy
      funext t
      apply hy t
      intro h
      exact absurd (h t (rd_self a w t)) (Nat.not_lt_zero _)
    · rintro rfl t _; rfl
  simp [V, hS]

theorem V_last {K : Type} [Field K] (a w : ℕ) (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool))
    (x : Fin (a + 2) → Bool) : V (K := K) a w (a + 2) T x =
      (((Finset.univ : Finset (Fin (a + 2) → Bool)).filter (fun x =>
        ∀ i : Fin (a + 2), T i (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card : K) := by
  have hS : Sx a w (a + 2) x = univ := by
    ext y
    simp only [Sx, Dn, mem_filter, mem_univ, true_and, iff_true]
    intro t ht
    exact absurd (fun i _ => i.isLt) ht
  simp only [V, hS, win]
  rw [Finset.sum_boole]
  congr 2
  ext y
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h i => h i i.isLt, fun h i _ => h i⟩

theorem win_eq (a w k : ℕ) (hk : k < a + 2) (y y' : Fin (a + 2) → Bool)
    (hy : ∀ t, t ∉ Dn a w k → y t = y' t) :
    win a w ⟨k, hk⟩ y = win a w ⟨k, hk⟩ y' := by
  funext j
  simp only [win]
  apply hy
  simp only [Dn, mem_filter, mem_univ, true_and, not_forall]
  exact ⟨⟨k, hk⟩, ⟨j, rfl⟩, by simp⟩

theorem V_succ {K : Type} [Field K] (a w k : ℕ) (hk : k < a + 2)
    (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool)) (x : Fin (a + 2) → Bool) :
    V (K := K) a w (k + 1) T x = ∑ y' ∈ Sp a w k x,
      (if T ⟨k, hk⟩ (win a w ⟨k, hk⟩ y') = true then (1 : K) else 0) * V a w k T y' := by
  have hmono : Dn a w k ⊆ Dn a w (k + 1) := by
    intro t ht
    simp only [Dn, mem_filter, mem_univ, true_and] at ht ⊢
    intro i hi; have := ht i hi; omega
  let π : (Fin (a + 2) → Bool) → (Fin (a + 2) → Bool) := fun y t => if t ∈ Dn a w k then x t else y t
  have hmaps : ∀ y ∈ Sx a w (k + 1) x, π y ∈ Sp a w k x := by
    intro y hy
    simp only [Sx, Sp, mem_filter, mem_univ, true_and, π] at hy ⊢
    refine ⟨fun t ht => ?_, fun t ht => by simp [ht]⟩
    split_ifs
    · rfl
    · exact hy t ht
  have hfib : ∀ y' ∈ Sp a w k x,
      (Sx a w (k + 1) x).filter (fun y => π y = y') = Sx a w k y' := by
    intro y' hy'
    simp only [Sp, mem_filter, mem_univ, true_and] at hy'
    ext y
    simp only [Sx, mem_filter, mem_univ, true_and, π]
    constructor
    · rintro ⟨_, rfl⟩ t ht
      simp [ht]
    · intro hy
      refine ⟨fun t ht => ?_, ?_⟩
      · have ht' : t ∉ Dn a w k := fun h => ht (hmono h)
        rw [hy t ht', hy'.1 t ht]
      · funext t
        split_ifs with ht
        · exact (hy'.2 t ht).symm
        · exact hy t ht
  have hind : ∀ y' ∈ Sp a w k x, ∀ y ∈ Sx a w k y',
      (if (∀ i : Fin (a + 2), i.val < k + 1 → T i (win a w i y) = true) then (1 : K) else 0) =
      (if T ⟨k, hk⟩ (win a w ⟨k, hk⟩ y') = true then (1 : K) else 0) *
      (if (∀ i : Fin (a + 2), i.val < k → T i (win a w i y) = true) then (1 : K) else 0) := by
    intro y' _ y hy
    simp only [Sx, mem_filter, mem_univ, true_and] at hy
    rw [← win_eq a w k hk y y' hy]
    have hsplit : (∀ i : Fin (a + 2), i.val < k + 1 → T i (win a w i y) = true) ↔
        (T ⟨k, hk⟩ (win a w ⟨k, hk⟩ y) = true ∧
          ∀ i : Fin (a + 2), i.val < k → T i (win a w i y) = true) := by
      constructor
      · intro h; exact ⟨h ⟨k, hk⟩ (by simp), fun i hi => h i (by omega)⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact h2 i h
        · have : i = ⟨k, hk⟩ := Fin.ext h
          subst this; exact h1
    rw [if_congr hsplit rfl rfl, ite_and]
    split_ifs <;> simp
  simp only [V]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro y' hy'
  rw [hfib y' hy', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact hind y' hy' y hy

theorem V_congr {K : Type} [Field K] (a w k : ℕ)
    (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool)) (x z : Fin (a + 2) → Bool)
    (hxz : ∀ t ∈ Fr a w k, x t = z t) : V (K := K) a w k T x = V a w k T z := by
  simp only [V]
  refine Finset.sum_nbij' (fun y t => if t ∈ Dn a w k then y t else z t)
    (fun y t => if t ∈ Dn a w k then y t else x t) ?_ ?_ ?_ ?_ ?_
  · intro y _
    simp only [Sx, mem_filter, mem_univ, true_and]
    intro t ht; simp [ht]
  · intro y _
    simp only [Sx, mem_filter, mem_univ, true_and]
    intro t ht; simp [ht]
  · intro y hy
    simp only [Sx, mem_filter, mem_univ, true_and] at hy
    funext t
    by_cases ht : t ∈ Dn a w k
    · simp [ht]
    · simp [ht, hy t ht]
  · intro y hy
    simp only [Sx, mem_filter, mem_univ, true_and] at hy
    funext t
    by_cases ht : t ∈ Dn a w k
    · simp [ht]
    · simp [ht, hy t ht]
  · intro y hy
    simp only [Sx, mem_filter, mem_univ, true_and] at hy
    congr 1
    apply propext
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro hi
    have : win a w i y = win a w i (fun t => if t ∈ Dn a w k then y t else z t) := by
      funext j
      simp only [win]
      by_cases ht : Fin.ofNat (a + 2) (i.val + j.val) ∈ Dn a w k
      · simp only [ht, ↓reduceIte]
      · simp only [ht, ↓reduceIte]
        rw [hy _ ht]
        apply hxz
        simp only [Dn, mem_filter, mem_univ, true_and, not_forall] at ht
        obtain ⟨i', hr, hlt⟩ := ht
        simp only [Fr, mem_filter, mem_univ, true_and]
        exact ⟨⟨i, hi, j, rfl⟩, ⟨i', by omega, hr⟩⟩
    rw [this]

theorem card_val_le {N m : ℕ} (s : Finset (Fin N)) (u : Finset ℕ) (hu : u.card ≤ m)
    (hs : ∀ t ∈ s, t.val ∈ u) : s.card ≤ m := by
  have : s.map Fin.valEmbedding ⊆ u := by
    intro x hx
    simp only [mem_map, Fin.valEmbedding_apply] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact hs t ht
  have := card_le_card this
  rw [card_map] at this
  omega

theorem Fr_card (a w k : ℕ) : (Fr a w k).card ≤ min (a + 2) (2 * w) := by
  rcases le_or_gt (a + 2) (2 * w) with h | h
  · have := card_le_univ (Fr a w k)
    simp only [Fintype.card_fin] at this
    omega
  · have hsub : Fr a w k ⊆ univ.filter (fun t : Fin (a + 2) => t.val < w) ∪
        univ.filter (fun t : Fin (a + 2) => k ≤ t.val ∧ t.val < k + w) := by
      intro t ht
      have ht' := (mem_filter.1 ht).2
      obtain ⟨⟨i, hi, j, hj⟩, ⟨i', hi', j', hj'⟩⟩ := ht'
      have e1 : t.val = (i.val + j.val) % (a + 2) := by rw [← hj, Fin.val_ofNat]
      have e2 : t.val = (i'.val + j'.val) % (a + 2) := by rw [← hj', Fin.val_ofNat]
      have hj1 := j.isLt
      have hj2 := j'.isLt
      have hi2 := i'.isLt
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases Nat.lt_or_ge (i'.val + j'.val) (a + 2) with c2 | c2
      · rw [Nat.mod_eq_of_lt c2] at e2
        rcases Nat.lt_or_ge (i.val + j.val) (a + 2) with c1 | c1
        · rw [Nat.mod_eq_of_lt c1] at e1
          right; omega
        · have : (i.val + j.val) % (a + 2) = i.val + j.val - (a + 2) := by
            rw [Nat.mod_eq_sub_mod c1, Nat.mod_eq_of_lt (by omega)]
          left; omega
      · have : (i'.val + j'.val) % (a + 2) = i'.val + j'.val - (a + 2) := by
          rw [Nat.mod_eq_sub_mod c2, Nat.mod_eq_of_lt (by omega)]
        left; omega
    have c1 : (univ.filter (fun t : Fin (a + 2) => t.val < w)).card ≤ w :=
      card_val_le _ (range w) (by simp) (by intro t ht; simp only [mem_filter] at ht; simpa using ht.2)
    have c2 : (univ.filter (fun t : Fin (a + 2) => k ≤ t.val ∧ t.val < k + w)).card ≤ w :=
      card_val_le _ (Ico k (k + w)) (by simp)
        (by intro t ht; simp only [mem_filter] at ht; simp only [mem_Ico]; exact ht.2)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega


noncomputable def code {d : ℕ} (a w : ℕ) (e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d) (k : ℕ)
    (x : Fin (a + 2) → Bool) : Fin d :=
  e k (fun t => x t.val)

noncomputable def rep {d : ℕ} (a w : ℕ) (e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d) (k : ℕ)
    (r : Fin d) : Fin (a + 2) → Bool :=
  fun t => if h : t ∈ Fr a w k then Function.invFun (e k) r ⟨t, h⟩ else false

theorem rep_code {d : ℕ} (a w : ℕ) (e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d) (k : ℕ)
    (x : Fin (a + 2) → Bool) : ∀ t ∈ Fr a w k, rep a w e k (code a w e k x) t = x t := by
  intro t ht
  simp only [rep, code, ht, ↓reduceDIte]
  rw [Function.leftInverse_invFun (e k).injective]

noncomputable def stepMap {K : Type} [Field K] {d : ℕ} (a w : ℕ)
    (e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d)
    (jj : Fin (a + 2)) (tab : (Fin (w + 1) → Bool) → Bool) : (Fin d → K) →ₗ[K] (Fin d → K) where
  toFun u := fun r => ∑ y ∈ Sp a w jj.val (rep a w e (jj.val + 1) r),
      (if tab (win a w jj y) = true then (1 : K) else 0) * u (code a w e jj.val y)
  map_add' u v := by
    funext r
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem scan_inv {K : Type} [Field K] {d : ℕ} (a w : ℕ) (e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d)
    (T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool)) :
    ∀ k ≤ a + 2, ((List.finRange (a + 2)).take k).foldl
      (fun v j => stepMap (K := K) a w e j (T j) v) (fun _ => 1) =
      fun r => V a w k T (rep a w e k r) := by
  intro k
  induction k with
  | zero =>
    intro _
    funext r
    simp [V_zero]
  | succ k ih =>
    intro hk
    rw [List.take_succ, List.foldl_append, ih (by omega)]
    have hget : (List.finRange (a + 2))[k]? = some ⟨k, by omega⟩ := by
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
    funext r
    simp only [stepMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [V_succ a w k (by omega)]
    apply Finset.sum_congr rfl
    intro y _
    rw [V_congr a w k T _ _ (rep_code a w e k y)]

theorem upper {K : Type} [Field K] (a w d : ℕ) (hd : 2 ^ min (a + 2) (2 * w) ≤ d) :
    ∃ (order : Equiv.Perm (Fin (a + 2))) (s : Fin d → K)
      (step : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool) → (Fin d → K) →ₗ[K] (Fin d → K))
      (out : (Fin d → K) →ₗ[K] K),
      ∀ T : Fin (a + 2) → ((Fin (w + 1) → Bool) → Bool),
        out ((List.finRange (a + 2)).foldl (fun v j => step j (T (order j)) v) s) =
          (((Finset.univ : Finset (Fin (a + 2) → Bool)).filter (fun x =>
            ∀ i : Fin (a + 2), T i (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card
            : K) := by
  have hemb : ∀ k : ℕ, Nonempty ((Fr a w k → Bool) ↪ Fin d) := by
    intro k
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]
    exact (Nat.pow_le_pow_right (by norm_num) (Fr_card a w k)).trans hd
  let e : ∀ k : ℕ, (Fr a w k → Bool) ↪ Fin d := fun k => Classical.choice (hemb k)
  refine ⟨Equiv.refl _, fun _ => 1, stepMap a w e,
    LinearMap.proj (code a w e (a + 2) (fun _ => false)), ?_⟩
  intro T
  have hs := scan_inv (K := K) a w e T (a + 2) le_rfl
  rw [List.take_of_length_le (by simp)] at hs
  simp only [Equiv.refl_apply]
  rw [hs, LinearMap.proj_apply]
  exact V_last a w T _

end PEqualNP.Outside.L_lib_579

theorem PEqualNP.Outside.L_lib_579 : (∀ (K : Type) [Field K] (a w d : ℕ),
  let n := a + 2
  let Table := (Fin (w + 1) → Bool) → Bool
  let count := fun (T : Fin n → Table) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, T i (fun j => x (Fin.ofNat (a + 2) (i.val + j.val))) = true)).card
  (∃ (order : Equiv.Perm (Fin n)) (s : Fin d → K)
      (step : Fin n → Table → (Fin d → K) →ₗ[K] (Fin d → K))
      (out : (Fin d → K) →ₗ[K] K),
    ∀ T : Fin n → Table,
      out ((List.finRange n).foldl (fun v j => step j (T (order j)) v) s) =
        (count T : K)) ↔
    2 ^ min n (2 * w) ≤ d) := by
  intro K _ a w d n Table count
  refine ⟨fun h => ?_, fun hd => ?_⟩
  · obtain ⟨order, s, step, out, h⟩ := h
    exact PEqualNP.Outside.L_lib_579.lower a w d order s step out h
  · exact PEqualNP.Outside.L_lib_579.upper a w d hd
