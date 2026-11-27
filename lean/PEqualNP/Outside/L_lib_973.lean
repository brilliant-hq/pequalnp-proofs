import Mathlib

open scoped BigOperators Matrix

namespace PEqualNP.Outside.L_lib_973_aux

private theorem l973_lower
    (n k b r : ℕ) (hn : 2 ≤ n) (hk : 2^(k-1) < n) (_ : n ≤ 2^k) (_ : n-k ≤ b) :
    let m := 2^k * b
    (∃ (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
      (∀ i j : Fin n, i ≠ j →
        2 * (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card = m) ∧
      let E := fun i j => ((T i j).toNat : ZMod 2)
      let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => E i j + E i v + E u j + E u v
      Matrix.rank A = r) → k ≤ r ∧ r < n := by
  classical
  dsimp only
  rintro ⟨T, u, v, hd, hr⟩
  let m := 2^k * b
  let E := fun (i : Fin n) (j : Fin m) => ((T i j).toNat : ZMod 2)
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => E i j + E i v + E u j + E u v
  change A.rank = r at hr
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) v.isLt
  have hbool (p q s t : Bool)
      (h : (p.toNat : ZMod 2) + (s.toNat : ZMod 2) =
        (q.toNat : ZMod 2) + (t.toNat : ZMod 2)) : (p ≠ q) ↔ (s ≠ t) := by
    revert h
    cases p <;> cases q <;> cases s <;> cases t <;> decide
  have hinj : Function.Injective A.row := by
    intro i j h
    by_contra hij
    have hpred (c : Fin m) : (T i c ≠ T j c) ↔ (T i v ≠ T j v) := by
      apply hbool
      have hc := congrFun h c
      change E i c + E i v + E u c + E u v = E j c + E j v + E u c + E u v at hc
      exact add_right_cancel (add_right_cancel hc)
    have hfilter : (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)) =
        (Finset.univ.filter (fun _ : Fin m => T i v ≠ T j v)) := by
      ext c
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hpred c
    have hh := hd i j hij
    change 2 * (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card = m at hh
    rw [hfilter] at hh
    by_cases hv : T i v ≠ T j v <;> simp [hv] at hh <;> omega
  let S := Submodule.span (ZMod 2) (Set.range A.row)
  have hs : Module.finrank (ZMod 2) S = r := A.rank_eq_finrank_span_row.symm.trans hr
  let B := Module.finBasisOfFinrankEq (ZMod 2) S hs
  let f : Fin n → Fin r → ZMod 2 := fun i => B.equivFun ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val (B.equivFun.injective hij))
  have hcard := Fintype.card_le_of_injective f hf
  simp [ZMod.card] at hcard
  refine ⟨?_, ?_⟩
  · by_contra! hkr
    exact (not_lt_of_ge (hcard.trans (pow_right_mono₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)))) hk
  · have hu : A.row u = 0 := by
      funext c
      change E u c + E u v + E u c + E u v = 0
      calc
        _ = (E u c + E u c) + (E u v + E u v) := by ac_rfl
        _ = 0 := by simp [← two_mul, show (2 : ZMod 2) = 0 by decide]
    let s := (Finset.univ.erase u).image A.row
    have hspan : S = Submodule.span (ZMod 2) (s : Set (Fin m → ZMod 2)) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        by_cases hi : i = u
        · subst i
          rw [hu]
          exact Submodule.zero_mem _
        · exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩)
      · apply Submodule.span_mono
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨i, rfl⟩
    have hdim := finrank_span_finset_le_card (R := ZMod 2) s
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (s : Set (Fin m → ZMod 2))) ≤ s.card at hdim
    rw [← hspan, hs] at hdim
    have hsize : s.card ≤ n - 1 := by
      refine Finset.card_image_le.trans ?_
      simp [Finset.card_erase_of_mem]
    omega

private theorem l973_labels {n k : ℕ} (hn : k + 1 ≤ n) (hk : n ≤ 2^k) :
    ∃ l : Fin n → (Fin k → ZMod 2), Function.Injective l ∧
      l ⟨0, by omega⟩ = 0 ∧
      ∀ j : Fin k, l ⟨j.val+1, by omega⟩ = Pi.single j 1 := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin n ↪ (Fin k → ZMod 2)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hk)
  let g : Fin (k + 1) → (Fin k → ZMod 2) :=
    Fin.cases 0 (fun j => Pi.single j 1)
  have hg : Function.Injective g := by
    intro a b h
    induction a using Fin.cases <;> induction b using Fin.cases
    · rfl
    · rename_i j
      have hj := congrFun h j
      simp [g] at hj
    · rename_i i
      have hi := congrFun h i
      simp [g] at hi
    · rename_i i j
      by_contra hne
      have hij : i ≠ j := fun e => hne (congrArg Fin.succ e)
      have hi := congrFun h i
      simp [g, Pi.single_eq_of_ne hij] at hi
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (e ∘ Fin.castLEEmb hn) g (e.injective.comp (Fin.castLEEmb hn).injective) hg
  refine ⟨σ ∘ e, σ.injective.comp e.injective, ?_, ?_⟩
  · exact hσ 0
  · intro j
    exact hσ j.succ

private theorem l973_balance {k : ℕ} (x y : Fin k → ZMod 2) (h : x ≠ y) (a b : ZMod 2) :
    2 * (Finset.univ.filter (fun f : Fin k → ZMod 2 =>
      (∑ j, x j * f j) + a ≠ (∑ j, y j * f j) + b)).card = 2^k := by
  classical
  have hex : ∃ j, x j ≠ y j := by
    by_contra! hn
    exact h (funext hn)
  obtain ⟨j, hj⟩ := hex
  let t : (Fin k → ZMod 2) → Fin k → ZMod 2 := fun f => f + Pi.single j 1
  have ht : ∀ f, t (t f) = f := by
    intro f
    ext i
    by_cases hi : i = j
    · subst i
      simp [t, add_assoc, show (1 : ZMod 2) + 1 = 0 by decide]
    · simp [t, Pi.single_eq_of_ne hi]
  let P : (Fin k → ZMod 2) → Prop := fun f => (∑ i, x i * f i) + a = (∑ i, y i * f i) + b
  have hs (w f : Fin k → ZMod 2) : (∑ i, w i * t f i) = (∑ i, w i * f i) + w j := by
    simp [t, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite]
  have hp (f) : P (t f) ↔ ¬ P f := by
    dsimp [P]
    rw [hs, hs]
    have aux (u v s z : ZMod 2) (hne : s ≠ z) : u + s = v + z ↔ u ≠ v := by
      revert u v s z
      decide
    rw [add_right_comm _ (x j) a, add_right_comm _ (y j) b]
    exact aux _ _ _ _ hj
  have hc : (Finset.univ.filter (fun f => ¬ P f)).card = (Finset.univ.filter P).card := by
    apply Finset.card_bij (fun f _ => t f)
    · intro f hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hp f).mpr (Finset.mem_filter.mp hf).2⟩
    · intro f _ g _ hfg
      simpa only [ht] using congrArg t hfg
    · intro f hf
      refine ⟨t f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ht f⟩
      intro hh
      exact (hp f).mp hh (Finset.mem_filter.mp hf).2
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → ZMod 2))) P
  rw [← hc] at hsum
  change 2 * (Finset.univ.filter (fun f => ¬ P f)).card = 2^k
  rw [two_mul, hsum]
  simp

private abbrev F := ZMod 2

private def l973_shift {n k s b : ℕ} (i : Fin n) (t : Fin b) : F :=
  if i.val = k + t.val ∧ 0 < t.val ∧ t.val ≤ s then 1 else 0

private def l973_entry {n k s b : ℕ} (l : Fin n → Fin k → F)
    (i : Fin n) (c : Fin b × (Fin k → F)) : F :=
  (∑ j, l i j * c.2 j) + l973_shift (k := k) (s := s) i c.1

private theorem l973_rank {n k s b m : ℕ} (hr : k+s < n) (hb : s < b)
    (l : Fin n → Fin k → F)
    (hl : ∀ j : Fin k, l ⟨j.val+1, by omega⟩ = Pi.single j 1)
    (e : Fin m ≃ Fin b × (Fin k → F)) :
    Matrix.rank (fun i c => l973_entry (s := s) l i (e c) : Matrix (Fin n) (Fin m) F) = k+s := by
  classical
  let A : Matrix (Fin n) (Fin m) F := fun i c => l973_entry (s := s) l i (e c)
  let G : Matrix (Fin n) (Fin (k+s)) F := fun i =>
    Fin.addCases (l i) (fun j : Fin s => if i.val = k+j.val+1 then 1 else 0)
  let H : Matrix (Fin (k+s)) (Fin m) F := fun j c =>
    Fin.addCases (e c).2 (fun a : Fin s => if (e c).1.val = a.val+1 then 1 else 0) j
  have hA : A = G * H := by
    ext i c
    change l973_entry (s := s) l i (e c) = _
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp only [G, H, Fin.addCases_left, Fin.addCases_right, l973_entry]
    congr 1
    unfold l973_shift
    by_cases ht : 0 < (e c).1.val ∧ (e c).1.val ≤ s
    · let a : Fin s := ⟨(e c).1.val - 1, by omega⟩
      have ha : (e c).1.val = a.val+1 := by change _ = (e c).1.val - 1 + 1; omega
      rw [Finset.sum_eq_single a]
      · simp only [ht.1, ht.2, and_true]
        rw [ite_eq_left ha, mul_one, show k + (e c).1.val = k + a.val + 1 by omega]
      · intro j _ hj
        have hne : (e c).1.val ≠ j.val+1 := by
          intro he
          apply hj
          apply Fin.ext
          omega
        simp [hne]
      · simp
    · have hz : ∀ a : Fin s, (e c).1.val ≠ a.val+1 := by
        intro a ha
        have := a.isLt
        omega
      simp [ht, hz]
  let row (i : Fin (k+s)) : Fin n := ⟨i.val+1, by omega⟩
  let pick : Fin (k+s) → Fin m := Fin.addCases
    (fun j => e.symm (⟨0, by omega⟩, Pi.single j 1))
    (fun j => e.symm (⟨j.val+1, by omega⟩, 0))
  have hminor : A.submatrix row pick = G.submatrix row id := by
    ext i j
    change l973_entry (s := s) l (row i) (e (pick j)) = G (row i) j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simp [pick, l973_entry, l973_shift, G, Pi.single_apply, mul_ite]
    · have ha := a.isLt
      simp [pick, l973_entry, l973_shift, G, show a.val+1 ≤ s by omega, Nat.add_assoc]
  let M := G.submatrix row id
  have htri : M.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    change G (row i) j = 0
    revert hij
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · intro hij
      have hv : i.val < a.val := hij
      let x : Fin k := ⟨i.val, by omega⟩
      have hx : x ≠ a := by intro h; have := congrArg Fin.val h; change i.val = a.val at this; omega
      dsimp only [G]
      rw [Fin.addCases_left]
      change l ⟨x.val+1, by omega⟩ a = 0
      rw [hl x]
      simp [Ne.symm hx]
    · intro hij
      have hv : i.val < k+a.val := hij
      have hne : i.val ≠ k+a.val := by omega
      simp [G, row, hne]
  have hdiag : ∀ i, M.diag i = 1 := by
    intro i
    change G (row i) i = 1
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp [G, row, hl]
    · simp [G, row]
  have hM : M.rank = k+s := by
    have hd : M.det ≠ 0 := by
      rw [Matrix.det_of_isLowerTriangular M htri]
      change (∏ i, M.diag i) ≠ 0
      have hp : (∏ i, M.diag i) = 1 := by simp only [hdiag, Finset.prod_const_one]
      rw [hp]
      exact one_ne_zero
    simpa using Matrix.rank_of_det_ne_zero hd
  change A.rank = k+s
  apply le_antisymm
  · rw [hA]
    exact (Matrix.rank_mul_le_left G H).trans (Matrix.rank_le_width G)
  · have hh := Matrix.rank_submatrix_le A row pick
    rw [hminor] at hh
    exact hM ▸ hh

private theorem l973_bool (z : F) : ((decide (z = 1)).toNat : F) = z := by
  fin_cases z <;> rfl

private theorem l973_upper {n k b r : ℕ} (hk : n ≤ 2^k) (hb : n-k ≤ b)
    (hkr : k ≤ r) (hr : r < n) :
    let m := 2^k * b
    ∃ (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
      (∀ i j : Fin n, i ≠ j →
        2 * (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card = m) ∧
      let E := fun i j => ((T i j).toNat : ZMod 2)
      let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => E i j + E i v + E u j + E u v
      Matrix.rank A = r := by
  classical
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hkr
  have hsb : s < b := by omega
  have hkn : k + 1 ≤ n := by omega
  obtain ⟨l, hli, hl0, hlu⟩ := l973_labels hkn hk
  let m := 2^k * b
  let e : Fin m ≃ Fin b × (Fin k → F) := Fintype.equivOfCardEq (by
    simp [m, Fintype.card_prod, ZMod.card, Nat.mul_comm])
  let D (i : Fin n) (c : Fin m) : F := l973_entry (s := s) l i (e c)
  let T (i : Fin n) (c : Fin m) : Bool := decide (D i c = 1)
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin m := e.symm (⟨0, by omega⟩, 0)
  have hT (i c) : ((T i c).toNat : F) = D i c := l973_bool _
  refine ⟨T, u, v, ?_, ?_⟩
  · intro i j hij
    let p (c : Fin b × (Fin k → F)) : Prop :=
      l973_entry (s := s) l i c ≠ l973_entry (s := s) l j c
    have hp (c : Fin m) : T i c ≠ T j c ↔ p (e c) := by
      constructor
      · intro ht hd
        exact ht (by change decide (D i c = 1) = decide (D j c = 1); rw [show D i c = D j c from hd])
      · intro hd ht
        apply hd
        change D i c = D j c
        rw [← hT, ← hT, ht]
    have hc : (Finset.univ.filter (fun c => T i c ≠ T j c)).card =
        ∑ t : Fin b, (Finset.univ.filter (fun f : Fin k → F => p (t, f))).card := by
      rw [Finset.card_filter]
      simp_rw [hp]
      rw [e.sum_comp (fun c => if p c then 1 else 0), Fintype.sum_prod_type]
      simp_rw [Finset.card_filter]
    rw [hc, Finset.mul_sum]
    have hbal (t : Fin b) : 2 * (Finset.univ.filter (fun f : Fin k → F => p (t, f))).card = 2^k := by
      change 2 * (Finset.univ.filter (fun f : Fin k → F =>
        (∑ a, l i a * f a) + l973_shift (k := k) (s := s) i t ≠
        (∑ a, l j a * f a) + l973_shift (k := k) (s := s) j t)).card = 2^k
      exact l973_balance (l i) (l j) (fun h => hij (hli h))
        (l973_shift (k := k) (s := s) i t) (l973_shift (k := k) (s := s) j t)
    simp_rw [hbal]
    simp [Nat.mul_comm]
  · have hu (c) : D u c = 0 := by
      simp [D, l973_entry, l973_shift, u, hl0]
      omega
    have hv (i) : D i v = 0 := by
      simp [D, l973_entry, l973_shift, v]
    dsimp only
    simp only [hT, hu, hv, add_zero]
    exact l973_rank hr hsb l hlu e

end PEqualNP.Outside.L_lib_973_aux

theorem PEqualNP.Outside.L_lib_973 :
    ∀ (n k b r : ℕ) (_ : 2 ≤ n) (_ : 2^(k-1) < n) (_ : n ≤ 2^k) (_ : n-k ≤ b),
      let m := 2^k * b
      (∃ (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
        (∀ i j : Fin n, i ≠ j →
          2 * (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card = m) ∧
        let E := fun i j => ((T i j).toNat : ZMod 2)
        let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => E i j + E i v + E u j + E u v
        Matrix.rank A = r) ↔ k ≤ r ∧ r < n := by
  intro n k b r hn hk hkn hb
  constructor
  · exact PEqualNP.Outside.L_lib_973_aux.l973_lower n k b r hn hk hkn hb
  · rintro ⟨hkr, hr⟩
    exact PEqualNP.Outside.L_lib_973_aux.l973_upper hkn hb hkr hr
