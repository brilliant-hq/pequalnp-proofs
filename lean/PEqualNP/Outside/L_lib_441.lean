import PEqualNP.Defs
import PEqualNP.Outside.L_lib_416

namespace PEqualNP.Outside.L_lib_441_aux

open PEqualNP.Outside.L_lib_416_aux

private lemma finset_compl_union_self {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    sᶜ ∪ s = Finset.univ := by
  ext i; by_cases hi : i ∈ s <;> simp

private lemma finset_union_compl_self {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    s ∪ sᶜ = Finset.univ := by
  ext i; by_cases hi : i ∈ s <;> simp

private lemma sum_prod_subtype_bool {α : Type} [Fintype α] [DecidableEq α] (P : Finset α)
    (F : P → Bool → ℤ) :
    (∑ x : P → Bool, ∏ p : P, F p (x p)) = ∏ p : P, (F p false + F p true) := by
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [add_comm]

private lemma sum_tilted_all {m : ℕ} (P : Finset (Fin m)) :
    (∑ x : P → Bool, ∏ p : P, (if x p then (1 : ℤ) else 2)) = (3 : ℤ) ^ P.card := by
  rw [sum_prod_subtype_bool P (fun _ b => if b then (1 : ℤ) else 2)]
  simp

private lemma sum_tilted_parity {m : ℕ} (P : Finset (Fin m)) (mask : Fin m → Bool)
    (hmask : ∃ p₀ ∈ P, mask p₀ = true) :
    (∑ x : P → Bool, sgn (par (∑ p : P, (mask p.1 && x p).toNat)) *
      ∏ p : P, (if x p then (1 : ℤ) else 2)) ≤ (3 : ℤ) ^ (P.card - 1) := by
  have h1 : ∀ x : P → Bool,
      sgn (par (∑ p : P, (mask p.1 && x p).toNat)) *
        ∏ p : P, (if x p then (1 : ℤ) else 2) =
      ∏ p : P, (sgn (mask p.1 && x p) * (if x p then (1 : ℤ) else 2)) := fun x => by
    rw [sgn_par_sum, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [sum_prod_subtype_bool P (fun p b => sgn (mask p.1 && b) * (if b then (1 : ℤ) else 2))]
  have hprod_eq : (∏ p : P,
      (sgn (mask p.1 && false) * (if false then (1 : ℤ) else 2) +
       sgn (mask p.1 && true) * (if true then (1 : ℤ) else 2))) =
      ∏ p : P, (if mask p.1 then (1 : ℤ) else 3) :=
    Finset.prod_congr rfl fun p _ => by cases mask p.1 <;> decide
  rw [hprod_eq]
  obtain ⟨p₀, hp₀, hm₀⟩ := hmask
  let q₀ : P := ⟨p₀, hp₀⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun p : P => if mask p.1 then (1 : ℤ) else 3)
    (Finset.mem_univ q₀)]
  have hq0 : (if mask q₀.1 then (1 : ℤ) else 3) = 1 := by
    dsimp only [q₀]; rw [hm₀]; rfl
  rw [hq0, one_mul]
  have hle : (∏ p ∈ (Finset.univ : Finset P).erase q₀,
      (if mask p.1 then (1 : ℤ) else 3)) ≤
      ∏ _p ∈ (Finset.univ : Finset P).erase q₀, (3 : ℤ) := by
    refine prod_le_prod_nonneg _ _ _ (fun p _ => by cases mask p.1 <;> decide)
      (fun p _ => by cases mask p.1 <;> decide)
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_coe] at hle
  exact hle

private lemma two_pow_sub_wt_eq_prod {m : ℕ} (h : Fin m → Bool) :
    ((2 ^ (m - wt h) : ℕ) : ℤ) = ∏ i : Fin m, (if h i then (1 : ℤ) else 2) := by
  have hprod : (∏ i : Fin m, (if h i then (1 : ℤ) else 2)) =
      ∏ i : Fin m, (if h i = false then (2 : ℤ) else 1) := by
    refine Finset.prod_congr rfl fun i _ => by cases h i <;> rfl
  rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hcard : (Finset.univ.filter (fun i : Fin m => h i = false)).card = m - wt h := by
    have hcomp : Finset.univ.filter (fun i : Fin m => h i = false) =
        (Finset.univ.filter (fun i : Fin m => h i = true))ᶜ := by
      ext i; cases h i <;> simp
    rw [hcomp, Finset.card_compl, Fintype.card_fin]
    rfl
  rw [hcard]
  push_cast
  rfl

private lemma subgroup_pivot_exists : ∀ (m : ℕ) (H : Finset (Fin m → Bool)), IsSubgroup H →
    ∃ P : Finset (Fin m), H.card = 2 ^ P.card ∧
      ∀ x : P → Bool, ∃! h : Fin m → Bool, h ∈ H ∧ ∀ p : P, h p.1 = x p := by
  intro m
  induction m with
  | zero =>
    intro H hH
    have hHeq : H = {fun _ => false} := by
      ext h
      simp only [Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · rintro rfl; exact hH.1
    refine ⟨∅, by simp [hHeq], fun x => ?_⟩
    refine ⟨fun _ => false, ⟨hH.1, fun p => Fin.elim0 p.1⟩, fun g ⟨_, _⟩ => ?_⟩
    funext i; exact Fin.elim0 i
  | succ m ih =>
    intro H hH
    let H0 : Finset (Fin m → Bool) :=
      Finset.univ.filter (fun h' => consBool false h' ∈ H)
    let H1 : Finset (Fin m → Bool) :=
      Finset.univ.filter (fun h' => consBool true h' ∈ H)
    have hH0_sub : IsSubgroup H0 := by
      refine ⟨?_, ?_⟩
      · simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
        have : consBool false (fun _ : Fin m => false) = fun _ => false := by
          funext i; cases i using Fin.cases <;> rfl
        rw [this]; exact hH.1
      · intro a ha b hb
        simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
        have : consBool false (fun i => xor (a i) (b i)) =
            (fun i => xor (consBool false a i) (consBool false b i)) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [this]; exact hH.2 _ ha _ hb
    obtain ⟨P0, hH0card, huniq0⟩ := ih H0 hH0_sub
    let emb0 : (Fin m → Bool) ↪ (Fin (m + 1) → Bool) := ⟨consBool false, consBool_inj false⟩
    let emb1 : (Fin m → Bool) ↪ (Fin (m + 1) → Bool) := ⟨consBool true, consBool_inj true⟩
    have hsplitH : H = H0.map emb0 ∪ H1.map emb1 := by
      ext h
      simp only [Finset.mem_union, Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk,
        H0, H1, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hh
        have heq : consBool (h 0) (Fin.tail h) = h := Fin.cons_self_tail h
        cases h0 : h 0
        · left; refine ⟨Fin.tail h, ?_, ?_⟩
          · rw [← h0, heq]; exact hh
          · rw [← h0, heq]
        · right; refine ⟨Fin.tail h, ?_, ?_⟩
          · rw [← h0, heq]; exact hh
          · rw [← h0, heq]
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> exact hu
    have hdisj : Disjoint (H0.map emb0) (H1.map emb1) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨a, _, rfl⟩ := hx1
      obtain ⟨b, _, hab⟩ := hx2
      have := congrFun hab 0
      simp [consBool_zero] at this
    by_cases hH1e : H1 = ∅
    · refine ⟨P0.map (Fin.succEmb m), ?_, ?_⟩
      · rw [Finset.card_map, hsplitH, Finset.card_union_of_disjoint hdisj, Finset.card_map,
          Finset.card_map, hH1e, Finset.card_empty, Nat.add_zero, hH0card]
      · intro x
        let x0 : P0 → Bool := fun p => x ⟨p.1.succ, Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
        obtain ⟨h', ⟨hh'H0, hh'eq⟩, h'uniq⟩ := huniq0 x0
        refine ⟨consBool false h', ⟨(Finset.mem_filter.mp hh'H0).2, ?_⟩, ?_⟩
        · intro p
          obtain ⟨j, hj, hjp⟩ := Finset.mem_map.mp p.2
          have hp : p = ⟨j.succ, Finset.mem_map.mpr ⟨j, hj, rfl⟩⟩ := Subtype.ext hjp.symm
          rw [hp]
          simpa [consBool_succ, x0] using hh'eq ⟨j, hj⟩
        · intro g ⟨hgH, hgeq⟩
          have hg0 : g 0 = false := by
            cases h0 : g 0
            · rfl
            · exfalso
              have hmem1 : Fin.tail g ∈ H1 := by
                simp only [H1, Finset.mem_filter, Finset.mem_univ, true_and]
                have heq : consBool true (Fin.tail g) = g := by
                  rw [← h0]; exact Fin.cons_self_tail g
                rwa [heq]
              rw [hH1e] at hmem1
              exact Finset.notMem_empty _ hmem1
          have hgH0 : Fin.tail g ∈ H0 := by
            simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
            have heq : consBool false (Fin.tail g) = g := by
              rw [← hg0]; exact Fin.cons_self_tail g
            rwa [heq]
          have htail : Fin.tail g = h' := by
            refine h'uniq (Fin.tail g) ⟨hgH0, fun p => ?_⟩
            simpa [Fin.tail, x0] using hgeq ⟨p.1.succ, Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
          rw [← htail, ← hg0]
          exact (Fin.cons_self_tail g).symm
    · obtain ⟨hstar, hhstar⟩ := Finset.nonempty_iff_ne_empty.mpr hH1e
      have hhstarH : consBool true hstar ∈ H := (Finset.mem_filter.mp hhstar).2
      have hH1_eq : H1 = H0.map (xorEmb hstar) := by
        ext u
        simp only [H1, H0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          xorEmb_apply]
        constructor
        · intro hu
          refine ⟨fun j => xor (hstar j) (u j), ?_, ?_⟩
          · have : consBool false (fun j => xor (hstar j) (u j)) =
                (fun i => xor (consBool true hstar i) (consBool true u i)) := by
              funext i; cases i using Fin.cases <;> simp [consBool_zero, consBool_succ]
            rw [this]; exact hH.2 _ hhstarH _ hu
          · funext j; dsimp only; cases hstar j <;> cases u j <;> rfl
        · rintro ⟨v, hv, rfl⟩
          have : consBool true (fun j => xor (hstar j) (v j)) =
              (fun i => xor (consBool true hstar i) (consBool false v i)) := by
            funext i; cases i using Fin.cases <;> simp [consBool_zero, consBool_succ]
          rw [this]; exact hH.2 _ hhstarH _ hv
      let P : Finset (Fin (m + 1)) := insert 0 (P0.map (Fin.succEmb m))
      have h0not : (0 : Fin (m + 1)) ∉ P0.map (Fin.succEmb m) := by
        simp only [Finset.mem_map, not_exists, not_and]
        intro j _ h
        exact Fin.succ_ne_zero j h
      refine ⟨P, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem h0not, Finset.card_map, hsplitH,
          Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
          hH1_eq, Finset.card_map, hH0card, pow_succ]
        ring
      · intro x
        let b0 : Bool := x ⟨0, Finset.mem_insert_self 0 _⟩
        let x0 : P0 → Bool := fun p =>
          xor (b0 && hstar p.1)
            (x ⟨p.1.succ, Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩)⟩)
        obtain ⟨h', ⟨hh'H0, hh'eq⟩, h'uniq⟩ := huniq0 x0
        let h : Fin (m + 1) → Bool := consBool b0 (fun j => xor (b0 && hstar j) (h' j))
        have hhH : h ∈ H := by
          cases hb0 : b0
          · have : h = consBool false h' := by
              funext i; cases i using Fin.cases <;> simp [h, hb0, consBool_zero, consBool_succ]
            rw [this]; exact (Finset.mem_filter.mp hh'H0).2
          · have : h = fun i => xor (consBool true hstar i) (consBool false h' i) := by
              funext i; cases i using Fin.cases <;> simp [h, hb0, consBool_zero, consBool_succ]
            rw [this]; exact hH.2 _ hhstarH _ (Finset.mem_filter.mp hh'H0).2
        refine ⟨h, ⟨hhH, ?_⟩, ?_⟩
        · intro p
          rcases Finset.mem_insert.mp p.2 with hp0 | hpS
          · have hp : p = ⟨0, Finset.mem_insert_self 0 _⟩ := Subtype.ext hp0
            rw [hp]; rfl
          · obtain ⟨j, hj, hjp⟩ := Finset.mem_map.mp hpS
            have hp : p = ⟨j.succ, Finset.mem_insert_of_mem
                (Finset.mem_map.mpr ⟨j, hj, rfl⟩)⟩ := Subtype.ext hjp.symm
            rw [hp]
            dsimp only [h]
            rw [consBool_succ, hh'eq ⟨j, hj⟩]
            dsimp only [x0]
            cases b0 && hstar j <;> cases x ⟨j.succ, _⟩ <;> rfl
        · intro g ⟨hgH, hgeq⟩
          have hg0 : g 0 = b0 := hgeq ⟨0, Finset.mem_insert_self 0 _⟩
          let g' : Fin m → Bool := fun j => xor (b0 && hstar j) (Fin.tail g j)
          have hg'H0 : g' ∈ H0 := by
            simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
            cases hb0 : b0
            · have : consBool false g' = g := by
                funext i
                cases i using Fin.cases with
                | zero => simp [consBool_zero, hg0, hb0]
                | succ j => simp [g', hb0, consBool_succ, Fin.tail]
              rwa [this]
            · have : consBool false g' = fun i => xor (consBool true hstar i) (g i) := by
                funext i
                cases i using Fin.cases with
                | zero => simp [consBool_zero, hg0, hb0]
                | succ j => simp [g', hb0, consBool_succ, Fin.tail]
              rw [this]; exact hH.2 _ hhstarH _ hgH
          have hg'eq : g' = h' := by
            refine h'uniq g' ⟨hg'H0, fun p => ?_⟩
            dsimp only [g', x0, Fin.tail]
            rw [hgeq ⟨p.1.succ, Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩)⟩]
          funext i
          cases i using Fin.cases with
          | zero => simp [h, consBool_zero, hg0]
          | succ j =>
            have hpt := congrFun hg'eq j
            dsimp only [g', Fin.tail] at hpt
            dsimp only [h]
            rw [consBool_succ, ← hpt]
            cases b0 && hstar j <;> cases g j.succ <;> rfl

private lemma additive_bool_eq_par {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool)
    (hadd : ∀ x y, f (fun i => xor (x i) (y i)) = xor (f x) (f y)) :
    ∀ x, f x = par (∑ i : α, (f (fun j => decide (j = i)) && x i).toNat) := by
  have hzero : f (fun _ => false) = false := by
    have h := hadd (fun _ => false) (fun _ => false)
    have hz : (fun _ : α => xor false false) = fun _ => false := rfl
    rw [hz] at h
    cases hf : f (fun _ => false)
    · rfl
    · simp [hf] at h
  have hind : ∀ (s : Finset α) (x : α → Bool),
      f (fun j => if j ∈ s then x j else false) =
        par (∑ i ∈ s, (f (fun j => decide (j = i)) && x i).toNat) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x; simp [hzero, par]
    | insert a s ha ih =>
      intro x
      have hsplit : (fun j => if j ∈ insert a s then x j else false) =
          fun j => xor (if j = a then x a else false) (if j ∈ s then x j else false) := by
        funext j
        by_cases hja : j = a
        · subst hja; simp [ha]
        · simp [hja]
      rw [hsplit, hadd, ih x, Finset.sum_insert ha, par_add, par_toNat]
      congr 1
      cases hxa : x a
      · simp [hzero]
      · simp only [Bool.and_true]
        congr 1
        funext j
        by_cases hja : j = a <;> simp [hja]
  intro x
  have hx := hind Finset.univ x
  simpa using hx

private lemma subgroup_coord_or_bound {m k : ℕ} (H : Finset (Fin m → Bool))
    (hH : IsSubgroup H) (hcard : H.card = 2 ^ k) :
    (∃ P : Finset (Fin m), P.card = k ∧
      H = Finset.univ.filter (fun h => ∀ i, i ∉ P → h i = false)) ∨
    (6 * ∑ h ∈ H, (2 ^ (m - wt h) : ℤ) ≤ 5 * (3 : ℤ) ^ k * (2 : ℤ) ^ (m - k)) := by
  obtain ⟨P, hPcard_pow, huniq⟩ := subgroup_pivot_exists m H hH
  have hPcard : P.card = k := by
    have hpow : 2 ^ P.card = 2 ^ k := hPcard_pow.symm.trans hcard
    exact Nat.pow_right_injective (by omega) hpow
  let invP : (P → Bool) → (Fin m → Bool) := fun x => Classical.choose (huniq x)
  have hinv_spec : ∀ x : P → Bool, invP x ∈ H ∧ ∀ p : P, invP x p.1 = x p :=
    fun x => (Classical.choose_spec (huniq x)).1
  have hinv_uniq : ∀ (x : P → Bool) (h : Fin m → Bool),
      h ∈ H → (∀ p : P, h p.1 = x p) → h = invP x :=
    fun x h hh hEq => (Classical.choose_spec (huniq x)).2 h ⟨hh, hEq⟩
  have hinv_add : ∀ x y : P → Bool,
      invP (fun p => xor (x p) (y p)) = fun i => xor (invP x i) (invP y i) := by
    intro x y
    symm
    refine hinv_uniq (fun p => xor (x p) (y p)) (fun i => xor (invP x i) (invP y i))
      (hH.2 _ (hinv_spec x).1 _ (hinv_spec y).1) ?_
    intro p
    rw [(hinv_spec x).2 p, (hinv_spec y).2 p]
  by_cases hcoord : ∀ h ∈ H, ∀ i, i ∉ P → h i = false
  · left
    refine ⟨P, hPcard, ?_⟩
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hcoord h
    · intro hout
      let h' := invP (fun p => h p.1)
      have hh' : h = h' := by
        funext i
        by_cases hi : i ∈ P
        · exact ((hinv_spec (fun p => h p.1)).2 ⟨i, hi⟩).symm
        · rw [hout i hi, hcoord h' (hinv_spec _).1 i hi]
      rw [hh']
      exact (hinv_spec _).1
  · right
    push Not at hcoord
    obtain ⟨h₀, hh₀H, a₀, ha₀not, ha₀true⟩ := hcoord
    have ha₀eq : h₀ a₀ = true := by
      cases h : h₀ a₀
      · exact absurd h ha₀true
      · rfl
    have hfa_add : ∀ x y : P → Bool,
        invP (fun p => xor (x p) (y p)) a₀ = xor (invP x a₀) (invP y a₀) := fun x y => by
      rw [hinv_add]
    have hfa_par := additive_bool_eq_par (fun x : P → Bool => invP x a₀) hfa_add
    let mask : Fin m → Bool := fun i =>
      if hi : i ∈ P then invP (fun p => decide (p.1 = i)) a₀ else false
    have hmask_eq : ∀ x : P → Bool,
        invP x a₀ = par (∑ p : P, (mask p.1 && x p).toNat) := by
      intro x
      rw [hfa_par x]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [mask, p.2, ↓reduceDIte]
      have heq : (fun j : P => decide (j = p)) = (fun j : P => decide (j.1 = p.1)) := by
        funext j
        by_cases hjp : j = p
        · subst hjp; simp
        · have hne : j.1 ≠ p.1 := fun h => hjp (Subtype.ext h)
          simp [hjp, hne]
      rw [heq]
    have hmask_ne : ∃ p₀ ∈ P, mask p₀ = true := by
      by_contra hall
      push Not at hall
      have h0 : invP (fun p => h₀ p.1) a₀ = false := by
        rw [hmask_eq]
        have hsum0 : (∑ p : P, (mask p.1 && h₀ p.1).toNat) = 0 := by
          refine Finset.sum_eq_zero fun p _ => ?_
          have hm : mask p.1 = false := by
            cases h : mask p.1
            · rfl
            · exact absurd h (hall p.1 p.2)
          simp [hm]
        rw [hsum0]; rfl
      have hh₀inv : h₀ = invP (fun p => h₀ p.1) := hinv_uniq _ h₀ hh₀H (fun _ => rfl)
      rw [← hh₀inv, ha₀eq] at h0
      exact Bool.noConfusion h0
    have hk_pos : 1 ≤ k := by
      obtain ⟨p₀, hp₀, _⟩ := hmask_ne
      have : 0 < P.card := Finset.card_pos.mpr ⟨p₀, hp₀⟩
      omega
    have hk_lt : k < m := by
      have : P.card < (Finset.univ : Finset (Fin m)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ P, ?_⟩
        intro heq
        exact ha₀not (heq ▸ Finset.mem_univ a₀)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hsum_bij : (∑ h ∈ H, (2 ^ (m - wt h) : ℤ)) =
        ∑ x : P → Bool, ∏ i : Fin m, (if invP x i then (1 : ℤ) else 2) := by
      have h1 : (∑ h ∈ H, (2 ^ (m - wt h) : ℤ)) =
          ∑ h ∈ H, ∏ i : Fin m, (if h i then (1 : ℤ) else 2) :=
        Finset.sum_congr rfl fun h _ => two_pow_sub_wt_eq_prod h
      rw [h1]
      symm
      refine Finset.sum_bij (fun x _ => invP x) (fun x _ => (hinv_spec x).1) ?_ ?_ (fun _ _ => rfl)
      · intro x₁ _ x₂ _ hEq
        funext p
        rw [← (hinv_spec x₁).2 p, ← (hinv_spec x₂).2 p, hEq]
      · intro h hh
        refine ⟨fun p => h p.1, Finset.mem_univ _, (hinv_uniq _ h hh (fun _ => rfl)).symm⟩
    have hterm_le : ∀ x : P → Bool,
        (∏ i : Fin m, (if invP x i then (1 : ℤ) else 2)) ≤
          (2 : ℤ) ^ (m - k - 1) * (if invP x a₀ then (1 : ℤ) else 2) *
          ∏ p : P, (if x p then (1 : ℤ) else 2) := by
      intro x
      let Q : Finset (Fin m) := insert a₀ P
      have hcompl : (∏ i : Fin m, (if invP x i then (1 : ℤ) else 2)) =
          (∏ i ∈ Qᶜ, (if invP x i then (1 : ℤ) else 2)) *
          (∏ i ∈ Q, (if invP x i then (1 : ℤ) else 2)) := by
        rw [← Finset.prod_union disjoint_compl_left, finset_compl_union_self]
      have hQprod : (∏ i ∈ Q, (if invP x i then (1 : ℤ) else 2)) =
          (if invP x a₀ then (1 : ℤ) else 2) * ∏ p : P, (if x p then (1 : ℤ) else 2) := by
        rw [Finset.prod_insert ha₀not]
        congr 1
        rw [← Finset.prod_coe_sort P]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [(hinv_spec x).2 p]
      have hC_le : (∏ i ∈ Qᶜ, (if invP x i then (1 : ℤ) else 2)) ≤ (2 : ℤ) ^ (m - k - 1) := by
        have hle : (∏ i ∈ Qᶜ, (if invP x i then (1 : ℤ) else 2)) ≤ ∏ _i ∈ Qᶜ, (2 : ℤ) :=
          prod_le_prod_nonneg _ _ _ (fun i _ => by cases invP x i <;> decide)
            (fun i _ => by cases invP x i <;> decide)
        rw [Finset.prod_const, Finset.card_compl, Fintype.card_fin,
          Finset.card_insert_of_notMem ha₀not, hPcard] at hle
        have hexp : m - (k + 1) = m - k - 1 := by omega
        rwa [hexp] at hle
      rw [hcompl, hQprod, mul_assoc]
      refine mul_le_mul_of_nonneg_right hC_le ?_
      have h1 : (0 : ℤ) ≤ if invP x a₀ then 1 else 2 := by cases invP x a₀ <;> decide
      have h2 : (0 : ℤ) ≤ ∏ p : P, (if x p then (1 : ℤ) else 2) :=
        Finset.prod_nonneg fun p _ => by cases x p <;> decide
      exact mul_nonneg h1 h2
    have h2sum : 2 * (∑ x : P → Bool, (if invP x a₀ then (1 : ℤ) else 2) *
          ∏ p : P, (if x p then (1 : ℤ) else 2)) ≤
        3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1) := by
      have hpt : ∀ x : P → Bool,
          2 * ((if invP x a₀ then (1 : ℤ) else 2) * ∏ p : P, (if x p then (1 : ℤ) else 2)) =
          3 * (∏ p : P, (if x p then (1 : ℤ) else 2)) +
          sgn (par (∑ p : P, (mask p.1 && x p).toNat)) *
            ∏ p : P, (if x p then (1 : ℤ) else 2) := fun x => by
        rw [hmask_eq x]
        cases par (∑ p : P, (mask p.1 && x p).toNat) <;> simp [sgn] <;> ring
      rw [Finset.mul_sum]
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_tilted_all P, hPcard]
      have hp := sum_tilted_parity P mask hmask_ne
      rw [hPcard] at hp
      linarith
    have h6sum : 6 * ∑ h ∈ H, (2 ^ (m - wt h) : ℤ) ≤
        3 * (2 : ℤ) ^ (m - k - 1) * (3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1)) := by
      rw [hsum_bij]
      have hsum_le : (∑ x : P → Bool, ∏ i : Fin m, (if invP x i then (1 : ℤ) else 2)) ≤
          (2 : ℤ) ^ (m - k - 1) * ∑ x : P → Bool, (if invP x a₀ then (1 : ℤ) else 2) *
            ∏ p : P, (if x p then (1 : ℤ) else 2) := by
        calc _ ≤ ∑ x : P → Bool, (2 : ℤ) ^ (m - k - 1) * (if invP x a₀ then (1 : ℤ) else 2) *
              ∏ p : P, (if x p then (1 : ℤ) else 2) := Finset.sum_le_sum fun x _ => hterm_le x
          _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      calc 6 * ∑ x : P → Bool, ∏ i : Fin m, (if invP x i then (1 : ℤ) else 2)
          ≤ 6 * ((2 : ℤ) ^ (m - k - 1) * ∑ x : P → Bool, (if invP x a₀ then (1 : ℤ) else 2) *
              ∏ p : P, (if x p then (1 : ℤ) else 2)) := by linarith
        _ = 3 * (2 : ℤ) ^ (m - k - 1) * (2 * ∑ x : P → Bool, (if invP x a₀ then (1 : ℤ) else 2) *
              ∏ p : P, (if x p then (1 : ℤ) else 2)) := by ring
        _ ≤ 3 * (2 : ℤ) ^ (m - k - 1) * (3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1)) :=
              mul_le_mul_of_nonneg_left h2sum (by positivity)
    have h3eq : 3 * (3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1)) = 10 * (3 : ℤ) ^ k := by
      have h3k : 3 * (3 : ℤ) ^ (k - 1) = (3 : ℤ) ^ k := by
        rw [← pow_succ']
        congr 1; omega
      linarith
    have h2eq : 2 * (2 : ℤ) ^ (m - k - 1) = (2 : ℤ) ^ (m - k) := by
      rw [← pow_succ']
      congr 1; omega
    calc 6 * ∑ h ∈ H, (2 ^ (m - wt h) : ℤ)
        ≤ 3 * (2 : ℤ) ^ (m - k - 1) * (3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1)) := h6sum
      _ = (2 : ℤ) ^ (m - k - 1) * (3 * (3 * (3 : ℤ) ^ k + (3 : ℤ) ^ (k - 1))) := by ring
      _ = (2 : ℤ) ^ (m - k - 1) * (10 * (3 : ℤ) ^ k) := by rw [h3eq]
      _ = 5 * (3 : ℤ) ^ k * (2 * (2 : ℤ) ^ (m - k - 1)) := by ring
      _ = 5 * (3 : ℤ) ^ k * (2 : ℤ) ^ (m - k) := by rw [h2eq]

private lemma two_bit_lin_zero_of_nz (d0 d1 : Bool) (h : d0 = true ∨ d1 = true) :
    (∑ x : Fin 2 → Bool, sgn (xor (d0 && x 0) (d1 && x 1))) = 0 := by
  cases d0 <;> cases d1
  · simp at h
  · decide
  · decide
  · decide

private lemma lane_u_sum_zero_of_active_d {m : ℕ} (lane : Fin m → Fin 3)
    (Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool) (h : Fin m → Bool)
    (a₀ : Fin m) (ha₀ : h a₀ = false)
    (b₀ : Fin 2)
    (hd : par (∑ i : Fin m, (Bcoeff (a₀, otherIdx (lane a₀) b₀) (i, lane i) && h i).toNat) = true) :
    let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
      fun u p => mergeLane lane u (fun _ => false) p.1 p.2
    let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
      par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
    (∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) = 0 := by
  intro uVec ν
  let d0 : Fin m → Bool := fun j =>
    par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat)
  let d1 : Fin m → Bool := fun j =>
    par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat)
  have hlin_u : ∀ u : Fin m → Fin 2 → Bool,
      linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h =
      par (∑ j : Fin m,
        (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1))).toNat) := by
    intro u
    have h1 : linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h =
        xor (par (∑ j : Fin m, (h j && (u j 0 && u j 1)).toNat)) (linGen (ν u) h) := by
      unfold linGen
      have hpt : ∀ i, (xor (u i 0 && u i 1) (ν u i) && h i) =
          xor (h i && (u i 0 && u i 1)) (ν u i && h i) := fun i => by
        cases u i 0 <;> cases u i 1 <;> cases ν u i <;> cases h i <;> rfl
      simp_rw [hpt]
      exact par_sum_xor Finset.univ _ _
    have h2 : linGen (ν u) h = par (∑ j : Fin m, (xor (d0 j && u j 0) (d1 j && u j 1)).toNat) := by
      unfold linGen ν
      have hmod1 : par (∑ i : Fin m,
          (par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) && h i).toNat) =
          par (∑ i : Fin m, ∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p && h i).toNat) := by
        refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
        cases h i
        · simp
        · simp only [Bool.and_true, par]
          have hm : (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) % 2 = 0 ∨
              (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      rw [hmod1, Finset.sum_comm, Fintype.sum_prod_type]
      have htriple : ∀ j : Fin m,
          (∑ l : Fin 3, ∑ i : Fin m, (Bcoeff (j, l) (i, lane i) && uVec u (j, l) && h i).toNat) =
          (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i && u j 0).toNat) +
          (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i && u j 1).toNat) := by
        intro j
        rw [Fin.sum_univ_three]
        have hlane_cases : ∀ (lj : Fin 3),
            (∑ i : Fin m, (Bcoeff (j, 0) (i, lane i) &&
              (if (0 : Fin 3) = lj then false else if (0 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) +
            (∑ i : Fin m, (Bcoeff (j, 1) (i, lane i) &&
              (if (1 : Fin 3) = lj then false else if (1 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) +
            (∑ i : Fin m, (Bcoeff (j, 2) (i, lane i) &&
              (if (2 : Fin 3) = lj then false else if (2 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) =
            (∑ i : Fin m, (Bcoeff (j, otherIdx lj 0) (i, lane i) && h i && u j 0).toNat) +
            (∑ i : Fin m, (Bcoeff (j, otherIdx lj 1) (i, lane i) && h i && u j 1).toNat) := by
          intro lj
          fin_cases lj <;> simp [otherIdx, Bool.and_right_comm]
        simpa only [uVec, mergeLane] using hlane_cases (lane j)
      simp_rw [htriple]
      refine par_sum_congr_mod Finset.univ _ _ fun j _ => ?_
      have ha : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i && u j 0).toNat) % 2 =
          (d0 j && u j 0).toNat % 2 := by
        cases u j 0
        · simp
        · simp only [Bool.and_true, d0, par]
          have hm : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat) % 2 = 0 ∨
              (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      have hb : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i && u j 1).toNat) % 2 =
          (d1 j && u j 1).toNat % 2 := by
        cases u j 1
        · simp
        · simp only [Bool.and_true, d1, par]
          have hm : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat) % 2 = 0 ∨
              (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      rw [Nat.add_mod, ha, hb]
      cases d0 j && u j 0 <;> cases d1 j && u j 1 <;> rfl
    rw [h1, h2, ← par_sum_xor]
  have hprod : (∑ u : Fin m → Fin 2 → Bool,
      sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) =
      ∏ j : Fin m, ∑ x : Fin 2 → Bool,
        sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1))) := by
    have hcongr : (∑ u : Fin m → Fin 2 → Bool,
        sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) =
        ∑ u : Fin m → Fin 2 → Bool,
          ∏ j : Fin m, sgn (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1))) :=
      Finset.sum_congr rfl fun u _ => by rw [hlin_u u, sgn_par_sum]
    rw [hcongr]
    exact sum_prod_fin_fun (fun (j : Fin m) (x : Fin 2 → Bool) =>
      sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1))))
  rw [hprod]
  refine Finset.prod_eq_zero (Finset.mem_univ a₀) ?_
  rw [ha₀]
  simp only [Bool.false_and, Bool.false_xor]
  apply two_bit_lin_zero_of_nz
  fin_cases b₀
  · exact Or.inl hd
  · exact Or.inr hd

private abbrev T4 := Fin 2 × Fin 2

private lemma par_sum_indep_T4 (F : (T4 → Bool) → Bool) (p₀ : T4)
    (hind : ∀ x : T4 → Bool, F (fun p => xor (x p) (decide (p = p₀))) = F x) :
    par (∑ x : T4 → Bool, (F x).toNat) = false := by
  let fl : (T4 → Bool) → (T4 → Bool) := fun x p => xor (x p) (decide (p = p₀))
  let S0 : Finset (T4 → Bool) := Finset.univ.filter (fun x => x p₀ = false)
  let S1 : Finset (T4 → Bool) := Finset.univ.filter (fun x => x p₀ = true)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    rw [h0] at h1; exact Bool.noConfusion h1
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext x; simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    cases x p₀ <;> simp
  have hbij : (∑ x ∈ S1, (F x).toNat) = ∑ x ∈ S0, (F x).toNat := by
    refine Finset.sum_bij (fun x _ => fl x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simp [fl, hx]
    · intro a _ b _ hab
      funext p
      have := congrFun hab p
      dsimp only [fl] at this
      revert this; cases a p <;> cases b p <;> cases decide (p = p₀) <;> simp
    · intro x hx
      refine ⟨fl x, ?_, ?_⟩
      · simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        simp [fl, hx]
      · funext p; dsimp only [fl]; cases x p <;> cases decide (p = p₀) <;> rfl
    · intro x _; exact (hind x).symm ▸ rfl
  rw [← hunion, Finset.sum_union hdisj, hbij, par_add]
  cases par (∑ x ∈ S0, (F x).toNat) <;> rfl

private lemma par_sum_monom3_T4 (c : Bool) (p₁ p₂ p₃ : T4) :
    par (∑ x : T4 → Bool, (c && x p₁ && x p₂ && x p₃).toNat) = false := by
  have hex : ∃ p₀ : T4, p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₀ ≠ p₃ := by
    have hcard : ({p₁, p₂, p₃} : Finset T4).card ≤ 3 := by
      calc ({p₁, p₂, p₃} : Finset T4).card
          ≤ ({p₂, p₃} : Finset T4).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({p₃} : Finset T4).card + 1 + 1 := by
            have := Finset.card_insert_le p₂ ({p₃} : Finset T4); omega
        _ = 3 := by simp
    have hlt : ({p₁, p₂, p₃} : Finset T4).card < (Finset.univ : Finset T4).card := by
      have : (Finset.univ : Finset T4).card = 4 := by decide
      omega
    obtain ⟨p₀, _, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact ⟨p₀, hnot.1, hnot.2.1, hnot.2.2⟩
  obtain ⟨p₀, h1, h2, h3⟩ := hex
  refine par_sum_indep_T4 _ p₀ fun x => ?_
  have e1 : decide (p₁ = p₀) = false := by simp [h1.symm]
  have e2 : decide (p₂ = p₀) = false := by simp [h2.symm]
  have e3 : decide (p₃ = p₀) = false := by simp [h3.symm]
  simp [e1, e2, e3]

private lemma par_sum_const_T4 (c : Bool) :
    par (∑ _x : T4 → Bool, c.toNat) = false :=
  par_sum_indep_T4 (fun _ => c) (0, 0) (fun _ => rfl)

private lemma par_sum_monom1_T4 (c : Bool) (p₁ : T4) :
    par (∑ x : T4 → Bool, (c && x p₁).toNat) = false := by
  have h : (∑ x : T4 → Bool, (c && x p₁).toNat) =
      ∑ x : T4 → Bool, (c && x p₁ && x p₁ && x p₁).toNat :=
    Finset.sum_congr rfl fun x _ => congrArg Bool.toNat (by cases c <;> cases x p₁ <;> rfl)
  rw [h]
  exact par_sum_monom3_T4 c p₁ p₁ p₁

private lemma par_sum_monom2_T4 (c : Bool) (p₁ p₂ : T4) :
    par (∑ x : T4 → Bool, (c && x p₁ && x p₂).toNat) = false := by
  have h : (∑ x : T4 → Bool, (c && x p₁ && x p₂).toNat) =
      ∑ x : T4 → Bool, (c && x p₁ && x p₂ && x p₂).toNat :=
    Finset.sum_congr rfl fun x _ =>
      congrArg Bool.toNat (by cases c <;> cases x p₁ <;> cases x p₂ <;> rfl)
  rw [h]
  exact par_sum_monom3_T4 c p₁ p₂ p₂

private lemma par_sum_isQuadGen_T4 {f : (T4 → Bool) → Bool} (hf : IsQuadGen f) :
    par (∑ x : T4 → Bool, (f x).toNat) = false := by
  obtain ⟨b, l, a, hfeq⟩ := hf
  simp_rw [hfeq, quadFormGen]
  rw [par_sum_xor, par_sum_xor, par_sum_const_T4]
  have hlin : par (∑ x : T4 → Bool, (linGen l x).toNat) = false := by
    unfold linGen
    rw [par_sum_par_comm (fun (x : T4 → Bool) (j : T4) => l j && x j)]
    have h0 : ∀ j : T4, par (∑ x : T4 → Bool, (l j && x j).toNat) = false :=
      fun j => par_sum_monom1_T4 (l j) j
    simp_rw [h0]; simp [par]
  have hquad : par (∑ x : T4 → Bool,
      (par (∑ i : T4, ∑ j : T4, (a i j && x i && x j).toNat)).toNat) = false := by
    have hprod : ∀ x : T4 → Bool,
        (∑ i : T4, ∑ j : T4, (a i j && x i && x j).toNat) =
        ∑ p : T4 × T4, (a p.1 p.2 && x p.1 && x p.2).toNat := fun x =>
      (Fintype.sum_prod_type (fun p : T4 × T4 => (a p.1 p.2 && x p.1 && x p.2).toNat)).symm
    simp_rw [hprod]
    rw [par_sum_par_comm (fun (x : T4 → Bool) (p : T4 × T4) => a p.1 p.2 && x p.1 && x p.2)]
    have h0 : ∀ p : T4 × T4, par (∑ x : T4 → Bool, (a p.1 p.2 && x p.1 && x p.2).toNat) = false :=
      fun p => par_sum_monom2_T4 (a p.1 p.2) p.1 p.2
    simp_rw [h0]; simp [par]
  rw [hlin, hquad]
  rfl

private lemma par_sum_pair_and_affine_T4 (p₁ p₂ : T4) (c : Bool) (m : T4 → Bool) :
    par (∑ x : T4 → Bool, ((x p₁ && x p₂) && xor c (linGen m x)).toNat) = false := by
  have h1 : ∀ x : T4 → Bool,
      ((x p₁ && x p₂) && xor c (linGen m x)) =
      xor (c && x p₁ && x p₂) ((x p₁ && x p₂) && linGen m x) := fun x => by
    cases x p₁ <;> cases x p₂ <;> cases c <;> cases linGen m x <;> rfl
  simp_rw [h1]
  rw [par_sum_xor, par_sum_monom2_T4, Bool.false_xor]
  have h2 : ∀ x : T4 → Bool,
      ((x p₁ && x p₂) && linGen m x) =
      par (∑ q : T4, (m q && x p₁ && x p₂ && x q).toNat) := fun x => by
    unfold linGen
    cases h12 : x p₁ && x p₂
    · have : ∀ q : T4, (m q && x p₁ && x p₂ && x q) = false := fun q => by
        cases h1 : x p₁ <;> cases h2 : x p₂ <;> simp [h1, h2] at h12 ⊢
      simp [this, par]
    · have : ∀ q : T4, (m q && x p₁ && x p₂ && x q) = (m q && x q) := fun q => by
        cases h1 : x p₁ <;> cases h2 : x p₂ <;> simp [h1, h2] at h12 ⊢
      simp [this]
  simp_rw [h2]
  rw [par_sum_par_comm (fun (x : T4 → Bool) (q : T4) => m q && x p₁ && x p₂ && x q)]
  have h0 : ∀ q : T4, par (∑ x : T4 → Bool, (m q && x p₁ && x p₂ && x q).toNat) = false :=
    fun q => par_sum_monom3_T4 (m q) p₁ p₂ q
  simp_rw [h0]; simp [par]

private lemma par_sum_deg4_T4 :
    par (∑ x : T4 → Bool, (x (0, 0) && x (0, 1) && x (1, 0) && x (1, 1)).toNat) = true := by
  have h1 : (∑ x : T4 → Bool, (x (0, 0) && x (0, 1) && x (1, 0) && x (1, 1)).toNat) = 1 := by
    rw [Finset.sum_eq_single (fun _ => true)]
    · rfl
    · intro x _ hne
      have hex : ∃ p : T4, x p = false := by
        by_contra hall
        push Not at hall
        apply hne
        funext p
        cases h : x p
        · exact absurd h (hall p)
        · rfl
      obtain ⟨⟨i, k⟩, hik⟩ := hex
      fin_cases i <;> fin_cases k <;> simp at hik <;> simp [hik]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]; rfl

private lemma abs_sum_sgn_le_14 (G : (T4 → Bool) → Bool)
    (hodd : par (∑ x : T4 → Bool, (G x).toNat) = true) :
    |∑ x : T4 → Bool, sgn (G x)| ≤ 14 := by
  have hpt : ∀ x : T4 → Bool, sgn (G x) = 1 - 2 * ((G x).toNat : ℤ) := fun x => by
    cases G x <;> decide
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  have hcard : Fintype.card (T4 → Bool) = 16 := by decide
  rw [hcard]
  have hle : (∑ x : T4 → Bool, (G x).toNat) ≤ 16 := by
    calc (∑ x : T4 → Bool, (G x).toNat)
        ≤ ∑ _x : T4 → Bool, 1 := Finset.sum_le_sum fun x _ => by cases G x <;> decide
      _ = 16 := by simp [hcard]
  have hmod : (∑ x : T4 → Bool, (G x).toNat) % 2 = 1 := by
    simpa [par] using hodd
  have hcast : (∑ x : T4 → Bool, ((G x).toNat : ℤ)) = ((∑ x : T4 → Bool, (G x).toNat : ℕ) : ℤ) := by
    push_cast; rfl
  rw [hcast]
  change |(16 : ℤ) - 2 * ((∑ x : T4 → Bool, (G x).toNat : ℕ) : ℤ)| ≤ 14
  rw [abs_le]
  constructor <;> omega

private lemma nondeg_quad_bent {α : Type} [Fintype α] [DecidableEq α] {s : ℕ}
    (hcard : Fintype.card α = 2 * s) (hs_pos : 0 < s)
    (RA : (α → Bool) → Bool) (hRA_quad : IsQuadGen RA) (hRA_zero : RA (fun _ => false) = false)
    (hnondeg : ∀ x : α → Bool, (∀ y : α → Bool, polar RA x y = false) → x = fun _ => false) :
    ∃ (invB : (α → Bool) → (α → Bool)) (a₁ a₂ : α),
      a₁ ≠ a₂ ∧
      (∀ β y, polar RA (invB β) y = linGen β y) ∧
      (∀ β₁ β₂, invB (fun a => xor (β₁ a) (β₂ a)) = fun a => xor (invB β₁ a) (invB β₂ a)) ∧
      (invB (fun _ => false) = fun _ => false) ∧
      polar RA (invB (fun a => decide (a = a₁))) (invB (fun a => decide (a = a₂))) = true ∧
      (∀ β, (∑ z : α → Bool, sgn (xor (RA z) (linGen β z))) =
        sgn (RA (invB β)) * (∑ z : α → Bool, sgn (RA z))) ∧
      |∑ z : α → Bool, sgn (RA z)| = (2 : ℤ) ^ s := by
  let ΦB : (α → Bool) → (α → Bool) := fun x a => polar RA x (fun b => decide (b = a))
  have hΦB_lin : ∀ x y : α → Bool, linGen (ΦB x) y = polar RA x y := fun x y =>
    (additive_bool_eq_par (polar RA x) (fun u v => polar_xor_right hRA_quad x u v) y).symm
  have hΦB_add : ∀ x₁ x₂ : α → Bool,
      ΦB (fun a => xor (x₁ a) (x₂ a)) = fun a => xor (ΦB x₁ a) (ΦB x₂ a) := fun x₁ x₂ => by
    funext a; exact polar_xor_left hRA_quad x₁ x₂ _
  have hΦB_zero : ΦB (fun _ => false) = fun _ => false := by
    funext a
    dsimp only [ΦB, polar]
    have hz : (fun b : α => xor false (decide (b = a))) = fun b => decide (b = a) := by
      funext b; simp
    rw [hz, hRA_zero]
    cases RA (fun b => decide (b = a)) <;> rfl
  have hΦB_inj : Function.Injective ΦB := by
    intro x₁ x₂ hEq
    have hzero : (fun a => xor (x₁ a) (x₂ a)) = fun _ => false := by
      apply hnondeg
      intro y
      rw [← hΦB_lin, hΦB_add, hEq]
      have h0 : (fun a => xor (ΦB x₂ a) (ΦB x₂ a)) = fun _ => false := by
        funext a; cases ΦB x₂ a <;> rfl
      rw [h0]; simp [linGen, par]
    funext a
    have ha := congrFun hzero a
    cases h1 : x₁ a <;> cases h2 : x₂ a <;> simp [h1, h2] at ha ⊢
  let eB : (α → Bool) ≃ (α → Bool) :=
    Equiv.ofBijective ΦB (Finite.injective_iff_bijective.mp hΦB_inj)
  let invB : (α → Bool) → (α → Bool) := eB.symm
  have hΦB_invB : ∀ β, ΦB (invB β) = β := fun β => eB.apply_symm_apply β
  have hBA_invB : ∀ β y : α → Bool, polar RA (invB β) y = linGen β y := fun β y => by
    rw [← hΦB_lin, hΦB_invB]
  have hinvB_add : ∀ β₁ β₂ : α → Bool,
      invB (fun a => xor (β₁ a) (β₂ a)) = fun a => xor (invB β₁ a) (invB β₂ a) := fun β₁ β₂ => by
    apply hΦB_inj
    rw [hΦB_invB, hΦB_add, hΦB_invB, hΦB_invB]
  have hinvB_zero : invB (fun _ => false) = fun _ => false := by
    apply hΦB_inj
    rw [hΦB_invB, hΦB_zero]
  have hWRA_bent : ∀ β : α → Bool,
      (∑ z : α → Bool, sgn (xor (RA z) (linGen β z))) =
      sgn (RA (invB β)) * (∑ z : α → Bool, sgn (RA z)) := by
    intro β
    let sh : (α → Bool) ≃ (α → Bool) :=
      { toFun := fun z a => xor (z a) (invB β a)
        invFun := fun z a => xor (z a) (invB β a)
        left_inv := fun z => by funext a; dsimp only; cases z a <;> cases invB β a <;> rfl
        right_inv := fun z => by funext a; dsimp only; cases z a <;> cases invB β a <;> rfl }
    rw [← Fintype.sum_equiv sh (fun z => sgn (xor (RA (sh z)) (linGen β (sh z))))
      (fun z => sgn (xor (RA z) (linGen β z))) (fun _ => rfl)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← sgn_xor]
    congr 1
    have hsh : sh z = fun a => xor (z a) (invB β a) := rfl
    have h1 : RA (fun a => xor (z a) (invB β a)) =
        xor (xor (RA z) (RA (invB β))) (linGen β z) := by
      rw [quad_add_expand RA z (invB β), hRA_zero, Bool.xor_false, polar_symm, hBA_invB]
    have h2 : linGen β (fun a => xor (z a) (invB β a)) = linGen β z := by
      rw [linGen_xor]
      have hself : linGen β (invB β) = false := by
        rw [← hBA_invB]
        exact polar_self hRA_quad (invB β)
      rw [hself, Bool.xor_false]
    rw [hsh, h1, h2]
    cases RA z <;> cases RA (invB β) <;> cases linGen β z <;> rfl
  have hWRA0_abs : |∑ z : α → Bool, sgn (RA z)| = (2 : ℤ) ^ s := by
    have hsq : (∑ z : α → Bool, sgn (RA z)) * (∑ z : α → Bool, sgn (RA z)) =
        ((2 : ℤ) ^ s) * ((2 : ℤ) ^ s) := by
      rw [Finset.sum_mul]
      have h2 : (∑ z1 : α → Bool, sgn (RA z1) * ∑ z2 : α → Bool, sgn (RA z2)) =
          ∑ h : α → Bool, sgn (RA h) * ∑ z : α → Bool, sgn (polar RA h z) := by
        trans (∑ z2 : α → Bool, ∑ h : α → Bool,
            sgn (xor (RA (fun a => xor (h a) (z2 a))) (RA z2)))
        · simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z2 _ => ?_
          let sh : (α → Bool) ≃ (α → Bool) :=
            { toFun := fun h a => xor (h a) (z2 a)
              invFun := fun z1 a => xor (z1 a) (z2 a)
              left_inv := fun h => by funext a; dsimp only; cases h a <;> cases z2 a <;> rfl
              right_inv := fun z1 => by funext a; dsimp only; cases z1 a <;> cases z2 a <;> rfl }
          exact (Fintype.sum_equiv sh (fun h => sgn (xor (RA (sh h)) (RA z2)))
            (fun z1 => sgn (RA z1) * sgn (RA z2)) (fun h => by rw [sgn_xor])).symm
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← sgn_xor]
          congr 1
          rw [quad_add_expand RA h z, hRA_zero, Bool.xor_false]
          cases RA h <;> cases RA z <;> cases polar RA h z <;> rfl
      rw [h2, Finset.sum_eq_single (fun _ => false)]
      · have h0 : ∀ z : α → Bool, polar RA (fun _ => false) z = false := fun z => by
          rw [← hΦB_lin, hΦB_zero]; simp [linGen, par]
        simp_rw [h0, hRA_zero]
        simp only [sgn, Bool.false_eq_true, ↓reduceIte, one_mul, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]
        have hc : Fintype.card (α → Bool) = 2 ^ (2 * s) := by
          simp [Fintype.card_pi, hcard]
        rw [hc]
        push_cast
        rw [← pow_add]
        congr 1; omega
      · intro h _ hne
        have hΦne : ΦB h ≠ fun _ => false := by
          intro h0
          exact hne (hΦB_inj (h0.trans hΦB_zero.symm))
        have hsum0 : (∑ z : α → Bool, sgn (polar RA h z)) = 0 := by
          simp_rw [← hΦB_lin h]
          rw [sum_sgn_linGen (ΦB h)]
          simp [hΦne]
        rw [hsum0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have habs_sq : |∑ z : α → Bool, sgn (RA z)| * |∑ z : α → Bool, sgn (RA z)| =
        ((2 : ℤ) ^ s) * ((2 : ℤ) ^ s) := by
      rw [← abs_mul, hsq, abs_of_nonneg (by positivity)]
    have hpos : (0 : ℤ) ≤ 2 ^ s := by positivity
    have ha : (0 : ℤ) ≤ |∑ z : α → Bool, sgn (RA z)| := abs_nonneg _
    nlinarith
  have hnonempty : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a₂⟩ := hnonempty
  let e2 : α → Bool := fun a => decide (a = a₂)
  have he2_ne : e2 ≠ fun _ => false := by
    intro h0; have := congrFun h0 a₂; simp [e2] at this
  have hinv_e2_ne : invB e2 ≠ fun _ => false := by
    intro h0
    apply he2_ne
    have h := congrArg ΦB h0
    rw [hΦB_invB, hΦB_zero] at h
    exact h
  have hex_a1 : ∃ a₁ : α, invB e2 a₁ = true := by
    by_contra hall
    push Not at hall
    apply hinv_e2_ne
    funext a
    cases h : invB e2 a
    · rfl
    · exact absurd h (hall a)
  obtain ⟨a₁, ha₁_true⟩ := hex_a1
  have ha12_ne : a₁ ≠ a₂ := by
    intro heq
    have ha2_true : invB e2 a₂ = true := heq ▸ ha₁_true
    have hself : linGen e2 (invB e2) = false := by
      rw [← hBA_invB]
      exact polar_self hRA_quad (invB e2)
    have hl : linGen e2 (invB e2) = invB e2 a₂ := by
      unfold linGen
      have : (∑ a : α, (e2 a && invB e2 a).toNat) = (invB e2 a₂).toNat := by
        rw [Finset.sum_eq_single a₂]
        · simp [e2]
        · intro a _ hne; simp [e2, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [this, par_toNat]
    rw [hl, ha2_true] at hself
    exact Bool.noConfusion hself
  have hBA_e12 : polar RA (invB (fun a => decide (a = a₁))) (invB (fun a => decide (a = a₂))) = true := by
    rw [hBA_invB]
    unfold linGen
    have : (∑ a : α, (decide (a = a₁) && invB e2 a).toNat) = (invB e2 a₁).toNat := by
      rw [Finset.sum_eq_single a₁]
      · simp
      · intro a _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    exact (by simpa [e2, this, par_toNat] using ha₁_true)
  exact ⟨invB, a₁, a₂, ha12_ne, hBA_invB, hinvB_add, hinvB_zero, hBA_e12, hWRA_bent, hWRA0_abs⟩

private lemma quartic_section_le_14 {α : Type} [Fintype α] [DecidableEq α]
    (RA : (α → Bool) → Bool) (hRA_quad : IsQuadGen RA) (hRA_zero : RA (fun _ => false) = false)
    (invB : (α → Bool) → (α → Bool))
    (hBA_invB : ∀ β y, polar RA (invB β) y = linGen β y)
    (hinvB_add : ∀ β₁ β₂, invB (fun a => xor (β₁ a) (β₂ a)) = fun a => xor (invB β₁ a) (invB β₂ a))
    (hinvB_zero : invB (fun _ => false) = fun _ => false)
    (a₁ a₂ : α)
    (hBA_e12 : polar RA (invB (fun a => decide (a = a₁))) (invB (fun a => decide (a = a₂))) = true)
    (q0 : (T4 → Bool) → Bool) (hq0 : IsQuadGen q0)
    (Lx : (T4 → Bool) → (α → Bool))
    (hLx : ∀ a : α, ∃ (c : Bool) (m : T4 → Bool), ∀ x, Lx x a = xor c (linGen m x)) :
    |∑ x : T4 → Bool, sgn (xor (q0 x)
      (RA (invB (fun a =>
        xor (xor ((x (0, 0) && x (0, 1)) && decide (a = a₁))
                 ((x (1, 0) && x (1, 1)) && decide (a = a₂)))
            (Lx x a)))))| ≤ 14 := by
  apply abs_sum_sgn_le_14
  let e1 : α → Bool := fun a => decide (a = a₁)
  let e2 : α → Bool := fun a => decide (a = a₂)
  have hinvB_sc : ∀ (b : Bool) (v : α → Bool),
      invB (fun a => b && v a) = fun a => b && invB v a := fun b v => by
    cases b
    · simpa using hinvB_zero
    · simp
  have hRA_sc : ∀ (b : Bool) (v : α → Bool),
      RA (fun a => b && v a) = (b && RA v) := fun b v => by
    cases b
    · simpa only [Bool.false_and] using hRA_zero
    · simp only [Bool.true_and]
  have hBA_sc_l : ∀ (b : Bool) (v w : α → Bool),
      polar RA (fun a => b && v a) w = (b && polar RA v w) := fun b v w => by
    cases b
    · simp only [Bool.false_and]
      dsimp only [polar]
      have hz : (fun a => xor false (w a)) = w := by funext a; simp
      rw [hz, hRA_zero]; cases RA w <;> rfl
    · simp only [Bool.true_and]
  have hBA_sc_r : ∀ (b : Bool) (v w : α → Bool),
      polar RA v (fun a => b && w a) = (b && polar RA v w) := fun b v w => by
    rw [polar_symm, hBA_sc_l, polar_symm]
  have hinvBL_aff : ∀ a : α,
      ∃ (c : Bool) (m : T4 → Bool), ∀ x, invB (Lx x) a = xor c (linGen m x) := by
    intro a
    have hlin := additive_bool_eq_par (fun β : α → Bool => invB β a)
      (fun β₁ β₂ => by rw [hinvB_add])
    obtain ⟨c, mk, hmk⟩ := lin_comp_affine (fun b : α => invB (fun d => decide (d = b)) a) Lx hLx
    refine ⟨c, mk, fun x => ?_⟩
    rw [hlin (Lx x)]
    exact hmk x
  have hRA_exp : ∀ x : T4 → Bool,
      RA (invB (fun a => xor (xor ((x (0, 0) && x (0, 1)) && e1 a)
                                  ((x (1, 0) && x (1, 1)) && e2 a)) (Lx x a))) =
      xor (xor (xor ((x (0, 0) && x (0, 1)) && RA (invB e1))
                    ((x (1, 0) && x (1, 1)) && RA (invB e2)))
               (RA (invB (Lx x))))
          (xor (xor ((x (0, 0) && x (0, 1)) && linGen e1 (invB (Lx x)))
                    ((x (1, 0) && x (1, 1)) && linGen e2 (invB (Lx x))))
               (x (0, 0) && x (0, 1) && x (1, 0) && x (1, 1))) := by
    intro x
    rw [hinvB_add, hinvB_add, hinvB_sc, hinvB_sc]
    let v1 : α → Bool := fun a => (x (0, 0) && x (0, 1)) && invB e1 a
    let v2 : α → Bool := fun a => (x (1, 0) && x (1, 1)) && invB e2 a
    let v3 : α → Bool := invB (Lx x)
    change RA (fun a => xor (xor (v1 a) (v2 a)) (v3 a)) = _
    rw [quad_add_expand RA (fun a => xor (v1 a) (v2 a)) v3, hRA_zero, Bool.xor_false,
      quad_add_expand RA v1 v2, hRA_zero, Bool.xor_false,
      polar_xor_left hRA_quad v1 v2 v3]
    have hv1 : RA v1 = ((x (0, 0) && x (0, 1)) && RA (invB e1)) := hRA_sc _ _
    have hv2 : RA v2 = ((x (1, 0) && x (1, 1)) && RA (invB e2)) := hRA_sc _ _
    have hb12 : polar RA v1 v2 = (x (0, 0) && x (0, 1) && x (1, 0) && x (1, 1)) := by
      dsimp only [v1, v2]
      rw [hBA_sc_l, hBA_sc_r, hBA_e12, Bool.and_true]
      cases x (0, 0) <;> cases x (0, 1) <;> cases x (1, 0) <;> cases x (1, 1) <;> rfl
    have hb13 : polar RA v1 v3 = ((x (0, 0) && x (0, 1)) && linGen e1 (invB (Lx x))) := by
      dsimp only [v1, v3]
      rw [hBA_sc_l, hBA_invB]
    have hb23 : polar RA v2 v3 = ((x (1, 0) && x (1, 1)) && linGen e2 (invB (Lx x))) := by
      dsimp only [v2, v3]
      rw [hBA_sc_l, hBA_invB]
    rw [hv1, hv2, hb12, hb13, hb23]
    cases (x (0, 0) && x (0, 1)) && RA (invB e1) <;>
      cases (x (1, 0) && x (1, 1)) && RA (invB e2) <;>
      cases RA (invB (Lx x)) <;>
      cases (x (0, 0) && x (0, 1)) && linGen e1 (invB (Lx x)) <;>
      cases (x (1, 0) && x (1, 1)) && linGen e2 (invB (Lx x)) <;>
      cases x (0, 0) && x (0, 1) && x (1, 0) && x (1, 1) <;> rfl
  change par (∑ x : T4 → Bool, (xor (q0 x) (RA (invB (fun a =>
    xor (xor ((x (0, 0) && x (0, 1)) && e1 a) ((x (1, 0) && x (1, 1)) && e2 a)) (Lx x a))))).toNat) = true
  simp_rw [hRA_exp]
  rw [par_sum_xor, par_sum_isQuadGen_T4 hq0, Bool.false_xor]
  rw [par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor]
  have ht1 : par (∑ x : T4 → Bool, ((x (0, 0) && x (0, 1)) && RA (invB e1)).toNat) = false := by
    have h : (∑ x : T4 → Bool, ((x (0, 0) && x (0, 1)) && RA (invB e1)).toNat) =
        ∑ x : T4 → Bool, (RA (invB e1) && x (0, 0) && x (0, 1)).toNat :=
      Finset.sum_congr rfl fun x _ => congrArg Bool.toNat
        (by cases x (0, 0) <;> cases x (0, 1) <;> cases RA (invB e1) <;> rfl)
    rw [h]
    exact par_sum_monom2_T4 _ _ _
  have ht2 : par (∑ x : T4 → Bool, ((x (1, 0) && x (1, 1)) && RA (invB e2)).toNat) = false := by
    have h : (∑ x : T4 → Bool, ((x (1, 0) && x (1, 1)) && RA (invB e2)).toNat) =
        ∑ x : T4 → Bool, (RA (invB e2) && x (1, 0) && x (1, 1)).toNat :=
      Finset.sum_congr rfl fun x _ => congrArg Bool.toNat
        (by cases x (1, 0) <;> cases x (1, 1) <;> cases RA (invB e2) <;> rfl)
    rw [h]
    exact par_sum_monom2_T4 _ _ _
  have ht3 : par (∑ x : T4 → Bool, (RA (invB (Lx x))).toNat) = false :=
    par_sum_isQuadGen_T4 (isQuadGen_comp_affine hRA_quad (fun x => invB (Lx x)) hinvBL_aff)
  obtain ⟨c1, m1, hm1⟩ := lin_comp_affine e1 (fun x => invB (Lx x)) hinvBL_aff
  obtain ⟨c2, m2, hm2⟩ := lin_comp_affine e2 (fun x => invB (Lx x)) hinvBL_aff
  have ht4 : par (∑ x : T4 → Bool, ((x (0, 0) && x (0, 1)) && linGen e1 (invB (Lx x))).toNat) = false := by
    simp_rw [hm1]
    exact par_sum_pair_and_affine_T4 (0, 0) (0, 1) c1 m1
  have ht5 : par (∑ x : T4 → Bool, ((x (1, 0) && x (1, 1)) && linGen e2 (invB (Lx x))).toNat) = false := by
    simp_rw [hm2]
    exact par_sum_pair_and_affine_T4 (1, 0) (1, 1) c2 m2
  rw [ht1, ht2, ht3, ht4, ht5, par_sum_deg4_T4]
  rfl

private lemma coord_no_active_bound_78 (m s : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3) (hs_pos : 0 < s) (hs : 2 * s ≤ m)
    (P : Finset (Fin m)) (hPcard : P.card = m - 2 * s)
    (hRad_eq : (Finset.univ.filter (fun h : Fin m → Bool =>
      ∀ t : Fin m → Bool, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)) =
      Finset.univ.filter (fun h => ∀ i, i ∉ P → h i = false))
    (hno_act : ∀ a ∈ Pᶜ, ∀ b : Fin 2, ∀ p ∈ P,
      xor (a0 (a, otherIdx (lane a) b) (p, lane p)) (a0 (p, lane p) (a, otherIdx (lane a) b)) = false) :
    8 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    7 * 8 ^ s * 6 ^ m := by
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)) :=
    ⟨b0, l0, a0, hqeq⟩
  have hRquad : IsQuadGen R := restrict_isQuadGen q hq lane
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
    fun u p => mergeLane lane u (fun _ => false) p.1 p.2
  let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
    par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
  have hsum_split := sum_split_lane m q b0 l0 a0 hqeq lane
  dsimp only at hsum_split
  let A : Finset (Fin m) := Pᶜ
  have hAcard : A.card = 2 * s := by
    rw [Finset.card_compl, Fintype.card_fin, hPcard]; omega
  let comb : ∀ {α : Type}, (P → α) → (A → α) → (Fin m → α) := fun fP fA i =>
    if hi : i ∈ P then fP ⟨i, hi⟩ else fA ⟨i, Finset.mem_compl.mpr hi⟩
  let splitEquiv : ∀ {α : Type}, (Fin m → α) ≃ ((P → α) × (A → α)) :=
    { toFun := fun f => (fun p => f p.1, fun a => f a.1)
      invFun := fun pair => comb pair.1 pair.2
      left_inv := fun f => by
        funext i; dsimp only [comb]; by_cases hi : i ∈ P <;> simp [hi]
      right_inv := fun ⟨fP, fA⟩ => by
        apply Prod.ext
        · funext p; simp [comb, p.2]
        · funext a; have ha : a.1 ∉ P := Finset.mem_compl.mp a.2; simp [comb, ha] }
  have hcomb_xor : ∀ (zP1 zP2 : P → Bool) (zA1 zA2 : A → Bool),
      comb (fun p => xor (zP1 p) (zP2 p)) (fun a => xor (zA1 a) (zA2 a)) =
      fun i => xor (comb zP1 zA1 i) (comb zP2 zA2 i) := fun zP1 zP2 zA1 zA2 => by
    funext i; dsimp only [comb]; by_cases hi : i ∈ P <;> simp [hi]
  have hcombP_mem_Rad : ∀ zP : P → Bool, comb zP (fun _ => false) ∈ Rad := fun zP => by
    change comb zP (fun _ => false) ∈ Finset.univ.filter _
    rw [hRad_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi; simp [comb, hi]
  let rP : P → Bool := fun p => xor (R (fun i => decide (i = p.1))) (R (fun _ => false))
  let RA : (A → Bool) → Bool := fun zA => xor (R (comb (fun _ => false) zA)) (R (fun _ => false))
  have hR_P_add : ∀ zP1 zP2 : P → Bool,
      xor (R (comb (fun p => xor (zP1 p) (zP2 p)) (fun _ => false))) (R (fun _ => false)) =
      xor (xor (R (comb zP1 (fun _ => false))) (R (fun _ => false)))
          (xor (R (comb zP2 (fun _ => false))) (R (fun _ => false))) := by
    intro zP1 zP2
    have hpol := (Finset.mem_filter.mp (hcombP_mem_Rad zP1)).2 (comb zP2 (fun _ => false))
    have hx : comb (fun p => xor (zP1 p) (zP2 p)) (fun _ => false) =
        fun i => xor (comb zP1 (fun _ => false) i) (comb zP2 (fun _ => false) i) := by
      simpa using hcomb_xor zP1 zP2 (fun _ => false) (fun _ => false)
    rw [hx, quad_add_expand R (comb zP1 (fun _ => false)) (comb zP2 (fun _ => false)), hpol]
    cases R (comb zP1 (fun _ => false)) <;> cases R (comb zP2 (fun _ => false)) <;>
      cases R (fun _ => false) <;> rfl
  have hR_P_par : ∀ zP : P → Bool,
      xor (R (comb zP (fun _ => false))) (R (fun _ => false)) =
      par (∑ p : P, (rP p && zP p).toNat) := by
    have h := additive_bool_eq_par
      (fun zP : P → Bool => xor (R (comb zP (fun _ => false))) (R (fun _ => false))) hR_P_add
    intro zP
    rw [h zP]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    have heq : comb (fun j : P => decide (j = p)) (fun _ => false) = fun i => decide (i = p.1) := by
      funext i; dsimp only [comb]
      by_cases hi : i ∈ P
      · by_cases hEq : i = p.1
        · subst hEq; simp [hi]
        · have hne : (⟨i, hi⟩ : P) ≠ p := fun h => hEq (congrArg Subtype.val h)
          simp [hi, hEq, hne]
      · have hne : i ≠ p.1 := fun h => hi (h ▸ p.2)
        simp [hi, hne]
    rw [heq]
  have hR_decomp : ∀ (zP : P → Bool) (zA : A → Bool),
      R (comb zP zA) = xor (R (fun _ => false))
        (xor (par (∑ p : P, (rP p && zP p).toNat)) (RA zA)) := by
    intro zP zA
    have hx : comb zP zA = fun i => xor (comb zP (fun _ => false) i) (comb (fun _ => false) zA i) := by
      simpa using hcomb_xor zP (fun _ => false) (fun _ => false) zA
    have hpol := (Finset.mem_filter.mp (hcombP_mem_Rad zP)).2 (comb (fun _ => false) zA)
    rw [hx, quad_add_expand R _ _, hpol]
    have hp := hR_P_par zP
    dsimp only [RA]
    rw [← hp]
    cases R (comb zP (fun _ => false)) <;> cases R (comb (fun _ => false) zA) <;>
      cases R (fun _ => false) <;> rfl
  have hnu_P_indep : ∀ (uP : P → Fin 2 → Bool) (uA : A → Fin 2 → Bool) (p : P),
      ν (comb uP uA) p.1 = ν (comb uP (fun _ _ => false)) p.1 := by
    intro uP uA p
    unfold ν
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hqP : q.1 ∈ P
    · have hu : uVec (comb uP uA) q = uVec (comb uP (fun _ _ => false)) q := by
        dsimp only [uVec, mergeLane, comb]; simp [hqP]
      rw [hu]
    · have hqA : q.1 ∈ A := Finset.mem_compl.mpr hqP
      by_cases hql : q.2 = lane q.1
      · simp [uVec, mergeLane, hql]
      · have hq01 : q.2 = otherIdx (lane q.1) 0 ∨ q.2 = otherIdx (lane q.1) 1 := by
          generalize hl : lane q.1 = l1 at hql ⊢
          generalize hq2 : q.2 = l2 at hql ⊢
          fin_cases l1 <;> fin_cases l2 <;> simp [otherIdx] at hql ⊢
        rcases hq01 with hq0 | hq1
        · have hB : Bcoeff q (p.1, lane p.1) = false := by
            have := hno_act q.1 hqA 0 p.1 p.2
            change Bcoeff (q.1, otherIdx (lane q.1) 0) (p.1, lane p.1) = false at this
            rwa [← hq0] at this
          simp [hB]
        · have hB : Bcoeff q (p.1, lane p.1) = false := by
            have := hno_act q.1 hqA 1 p.1 p.2
            change Bcoeff (q.1, otherIdx (lane q.1) 1) (p.1, lane p.1) = false at this
            rwa [← hq1] at this
          simp [hB]
  let αP : (P → Fin 2 → Bool) → P → Bool := fun uP p =>
    xor (uP p 0 && uP p 1) (ν (comb uP (fun _ _ => false)) p.1)
  let αA : (P → Fin 2 → Bool) → (A → Fin 2 → Bool) → A → Bool := fun uP uA a =>
    xor (uA a 0 && uA a 1) (ν (comb uP uA) a.1)
  let SurvP : Finset (P → Fin 2 → Bool) := Finset.univ.filter (fun uP => ∀ p : P, αP uP p = rP p)
  have hSurvP_le : (SurvP.card : ℤ) ≤ (3 : ℤ) ^ (m - 2 * s) := by
    have hstep1 : (2 ^ P.card : ℤ) * (SurvP.card : ℤ) =
        ∑ hP : P → Bool, sgn (par (∑ p : P, (hP p && rP p).toNat)) *
          ∑ uP : P → Fin 2 → Bool, sgn (par (∑ p : P, (hP p && αP uP p).toNat)) := by
      have h1 : (2 ^ P.card : ℤ) * (SurvP.card : ℤ) =
          ∑ uP : P → Fin 2 → Bool, ∑ hP : P → Bool,
            sgn (linGen (fun p : P => xor (αP uP p) (rP p)) hP) := by
        have hinner : ∀ uP : P → Fin 2 → Bool,
            (∑ hP : P → Bool, sgn (linGen (fun p : P => xor (αP uP p) (rP p)) hP)) =
            if ∀ p : P, αP uP p = rP p then (2 ^ P.card : ℤ) else 0 := by
          intro uP
          have hsgn := sum_sgn_linGen (fun p : P => xor (αP uP p) (rP p))
          have hcardP : Fintype.card (P → Bool) = 2 ^ P.card := by simp [Fintype.card_pi]
          rw [hcardP] at hsgn
          have hiff : (fun p : P => xor (αP uP p) (rP p)) = (fun _ => false) ↔
              ∀ p : P, αP uP p = rP p := by
            constructor
            · intro h p
              have hp := congrFun h p
              cases h1 : αP uP p <;> cases h2 : rP p <;> simp [h1, h2] at hp ⊢
            · intro h; funext p; rw [h p]; cases rP p <;> rfl
          rw [hsgn]
          by_cases hc : ∀ p : P, αP uP p = rP p
          · have h1 := hiff.mpr hc
            rw [ite_eq_left_iff.mpr (fun h => absurd h1 h),
              ite_eq_left_iff.mpr (fun h => absurd hc h)]
            push_cast; rfl
          · have h1 := mt hiff.mp hc
            rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
              ite_eq_right_iff.mpr (fun h => absurd h hc)]
        simp_rw [hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        rfl
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun hP _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun uP _ => ?_
      rw [← sgn_xor]
      congr 1
      unfold linGen
      rw [← par_sum_xor]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only
      cases αP uP p <;> cases rP p <;> cases hP p <;> rfl
    have hstep2 : ∀ hP : P → Bool,
        |∑ uP : P → Fin 2 → Bool, sgn (par (∑ p : P, (hP p && αP uP p).toNat))| ≤
        (2 ^ P.card : ℤ) * ∏ p : P, (if hP p then (1 : ℤ) else 2) := by
      intro hP
      let h : Fin m → Bool := comb hP (fun _ => false)
      have hu_eq : (∑ u : Fin m → Fin 2 → Bool,
          sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) =
          (2 : ℤ) ^ (4 * s) * ∑ uP : P → Fin 2 → Bool,
            sgn (par (∑ p : P, (hP p && αP uP p).toNat)) := by
        trans (∑ pair : (P → Fin 2 → Bool) × (A → Fin 2 → Bool),
            sgn (par (∑ p : P, (hP p && αP pair.1 p).toNat)))
        · refine Fintype.sum_equiv splitEquiv _ _ fun u => ?_
          congr 1
          have hu_comb : u = comb (splitEquiv u).1 (splitEquiv u).2 :=
            (splitEquiv.left_inv u).symm
          unfold linGen
          congr 1
          trans (∑ i ∈ P, (xor (u i 0 && u i 1) (ν u i) && h i).toNat)
          · symm
            refine Finset.sum_subset (Finset.subset_univ P) fun i _ hi => ?_
            simp [h, comb, hi]
          · rw [← Finset.sum_coe_sort P (fun i => (xor (u i 0 && u i 1) (ν u i) && h i).toNat)]
            refine Finset.sum_congr rfl fun p _ => ?_
            have hhp : h p.1 = hP p := by simp [h, comb, p.2]
            have hnu : ν u p.1 = ν (comb (splitEquiv u).1 (fun _ _ => false)) p.1 := by
              conv_lhs => rw [hu_comb]
              exact hnu_P_indep (splitEquiv u).1 (splitEquiv u).2 p
            have hsp : (splitEquiv u).1 p = u p.1 := rfl
            rw [hhp, hnu]
            dsimp only [αP]
            rw [hsp, Bool.and_comm]
        · rw [Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          congr 1
          have hcardA : Fintype.card (A → Fin 2 → Bool) = 2 ^ (4 * s) := by
            rw [Fintype.card_pi]
            simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin, Fintype.card_coe, hAcard]
            rw [← pow_mul]; congr 1; omega
          rw [hcardA]; push_cast; rfl
      have hb := lane_u_factor_bound m lane Bcoeff h
      dsimp only at hb
      rw [hu_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ (4 * s))] at hb
      have hwth : ((2 ^ (m - wt h) : ℕ) : ℤ) =
          (2 : ℤ) ^ (2 * s) * ∏ p : P, (if hP p then (1 : ℤ) else 2) := by
        rw [two_pow_sub_wt_eq_prod h]
        have hsplit : (∏ i : Fin m, (if h i then (1 : ℤ) else 2)) =
            (∏ i ∈ Pᶜ, (if h i then (1 : ℤ) else 2)) *
            (∏ i ∈ P, (if h i then (1 : ℤ) else 2)) := by
          rw [← Finset.prod_union disjoint_compl_left, finset_compl_union_self]
        rw [hsplit]
        congr 1
        · have h2s : (∏ i ∈ Pᶜ, (if h i then (1 : ℤ) else 2)) = ∏ _i ∈ Pᶜ, (2 : ℤ) :=
            Finset.prod_congr rfl fun i hi => by simp [h, comb, Finset.mem_compl.mp hi]
          rw [h2s, Finset.prod_const, Finset.card_compl, Fintype.card_fin, hPcard]
          congr 1; omega
        · rw [← Finset.prod_coe_sort P]
          refine Finset.prod_congr rfl fun p _ => by simp [h, comb, p.2]
      have hpow_eq : (2 ^ m : ℤ) * ((2 ^ (m - wt h) : ℕ) : ℤ) =
          (2 : ℤ) ^ (4 * s) * ((2 ^ P.card : ℤ) * ∏ p : P, (if hP p then (1 : ℤ) else 2)) := by
        rw [hwth]
        have h2 : (2 : ℤ) ^ m * (2 : ℤ) ^ (2 * s) = (2 : ℤ) ^ (4 * s) * (2 : ℤ) ^ P.card := by
          rw [← pow_add, ← pow_add, hPcard]; congr 1; omega
        calc (2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * ∏ p : P, (if hP p then (1 : ℤ) else 2))
            = ((2 : ℤ) ^ m * (2 : ℤ) ^ (2 * s)) * ∏ p : P, (if hP p then (1 : ℤ) else 2) := by ring
          _ = ((2 : ℤ) ^ (4 * s) * (2 : ℤ) ^ P.card) * ∏ p : P, (if hP p then (1 : ℤ) else 2) := by rw [h2]
          _ = _ := by ring
      rw [show (2 ^ (m - wt h) : ℤ) = ((2 ^ (m - wt h) : ℕ) : ℤ) by push_cast; rfl,
        hpow_eq] at hb
      exact le_of_mul_le_mul_left hb (by positivity)
    have htotal : (2 ^ P.card : ℤ) * (SurvP.card : ℤ) ≤ (2 ^ P.card : ℤ) * (3 : ℤ) ^ P.card := by
      rw [hstep1]
      calc _ ≤ ∑ hP : P → Bool, |sgn (par (∑ p : P, (hP p && rP p).toNat)) *
            ∑ uP : P → Fin 2 → Bool, sgn (par (∑ p : P, (hP p && αP uP p).toNat))| :=
            Finset.sum_le_sum fun hP _ => le_abs_self _
        _ = ∑ hP : P → Bool,
            |∑ uP : P → Fin 2 → Bool, sgn (par (∑ p : P, (hP p && αP uP p).toNat))| := by
            refine Finset.sum_congr rfl fun hP _ => by rw [abs_mul, sgn_abs, one_mul]
        _ ≤ ∑ hP : P → Bool, (2 ^ P.card : ℤ) * ∏ p : P, (if hP p then (1 : ℤ) else 2) :=
            Finset.sum_le_sum fun hP _ => hstep2 hP
        _ = (2 ^ P.card : ℤ) * ∑ hP : P → Bool, ∏ p : P, (if hP p then (1 : ℤ) else 2) :=
            (Finset.mul_sum ..).symm
        _ = (2 ^ P.card : ℤ) * (3 : ℤ) ^ P.card := by rw [sum_tilted_all P]
    have hle := le_of_mul_le_mul_left htotal (by positivity)
    rwa [hPcard] at hle
  have hRA_quad : IsQuadGen RA := by
    let Φ : (A → Bool) → (Fin m → Bool) := fun zA => comb (fun _ => false) zA
    have hΦ : ∀ i : Fin m, ∃ (c : Bool) (mask : A → Bool), ∀ zA, Φ zA i = xor c (linGen mask zA) := by
      intro i
      by_cases hi : i ∈ P
      · refine ⟨false, fun _ => false, fun zA => by simp [Φ, comb, hi, linGen, par]⟩
      · have hiA : i ∈ A := Finset.mem_compl.mpr hi
        refine ⟨false, fun a => decide (a = ⟨i, hiA⟩), fun zA => ?_⟩
        simp only [Φ, comb, hi, ↓reduceDIte, Bool.false_xor, linGen]
        have : (∑ a : A, (decide (a = ⟨i, hiA⟩) && zA a).toNat) = (zA ⟨i, hiA⟩).toNat := by
          rw [Finset.sum_eq_single ⟨i, hiA⟩]
          · simp
          · intro a _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [this, par_toNat]
    exact isQuadGen_xor (isQuadGen_comp_affine hRquad Φ hΦ) (isQuadGen_const _)
  have hRA_zero : RA (fun _ => false) = false := by
    dsimp only [RA]
    have h0 : comb (fun _ : P => false) (fun _ : A => false) = fun _ => false := by
      funext i; dsimp only [comb]; by_cases hi : i ∈ P <;> simp [hi]
    rw [h0]; cases R (fun _ => false) <;> rfl
  have hRA_nondeg : ∀ x : A → Bool, (∀ y : A → Bool, polar RA x y = false) → x = fun _ => false := by
    intro x hx
    have hmem : comb (fun _ => false) x ∈ Rad := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun t => ?_⟩
      have ht : t = comb (splitEquiv t).1 (splitEquiv t).2 := (splitEquiv.left_inv t).symm
      rw [ht]
      have hsplit : comb (splitEquiv t).1 (splitEquiv t).2 =
          fun i => xor (comb (splitEquiv t).1 (fun _ => false) i)
                       (comb (fun _ => false) (splitEquiv t).2 i) := by
        simpa using hcomb_xor (splitEquiv t).1 (fun _ => false) (fun _ => false) (splitEquiv t).2
      rw [hsplit, polar_xor_right hRquad]
      have h1 : polar R (comb (fun _ => false) x) (comb (splitEquiv t).1 (fun _ => false)) = false := by
        rw [polar_symm]
        exact (Finset.mem_filter.mp (hcombP_mem_Rad (splitEquiv t).1)).2 _
      have h2 : polar R (comb (fun _ => false) x) (comb (fun _ => false) (splitEquiv t).2) =
          polar RA x (splitEquiv t).2 := by
        dsimp only [polar, RA]
        have h0 : comb (fun _ : P => false) (fun _ : A => false) = fun _ => false := by
          funext i; dsimp only [comb]; by_cases hi : i ∈ P <;> simp [hi]
        have hadd : (fun i => xor (comb (fun _ => false) x i)
            (comb (fun _ => false) (splitEquiv t).2 i)) =
            comb (fun _ => false) (fun a => xor (x a) ((splitEquiv t).2 a)) := by
          simpa using (hcomb_xor (fun _ => false) (fun _ => false) x (splitEquiv t).2).symm
        rw [hadd, h0]
        cases R (comb (fun _ => false) (fun a => xor (x a) ((splitEquiv t).2 a))) <;>
          cases R (comb (fun _ => false) x) <;>
          cases R (comb (fun _ => false) (splitEquiv t).2) <;>
          cases R (fun _ => false) <;> rfl
      rw [h1, h2, hx]
      rfl
    change comb (fun _ => false) x ∈ Finset.univ.filter _ at hmem
    rw [hRad_eq] at hmem
    have hout := (Finset.mem_filter.mp hmem).2
    funext a
    have ha : a.1 ∉ P := Finset.mem_compl.mp a.2
    simpa [comb, ha] using hout a.1 ha
  obtain ⟨invB, a₁, a₂, ha12_ne, hBA_invB, hinvB_add, hinvB_zero, hBA_e12, hWRA_bent, hWRA0_abs⟩ :=
    nondeg_quad_bent (by simpa [Fintype.card_coe] using hAcard) hs_pos RA hRA_quad hRA_zero hRA_nondeg
  let W0 : ℤ := ∑ z : A → Bool, sgn (RA z)
  have hS_factor : (∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
      sgn (R (fun _ => false)) * (2 : ℤ) ^ P.card * W0 *
        ∑ uP ∈ SurvP, ∑ uA : A → Fin 2 → Bool,
          sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
            (RA (invB (αA uP uA)))) := by
    rw [hsum_split]
    have hstep_u : (∑ u : Fin m → Fin 2 → Bool,
        sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
          ∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))) =
        ∑ uP : P → Fin 2 → Bool, ∑ uA : A → Fin 2 → Bool,
          sgn (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false))) *
            ∑ z : Fin m → Bool, sgn (xor (R z)
              (linGen (fun i => xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i)) z)) := by
      trans (∑ pair : (P → Fin 2 → Bool) × (A → Fin 2 → Bool),
          sgn (xor (q (mergeLane lane (comb pair.1 pair.2) (fun _ => false))) (q (fun _ _ => false))) *
            ∑ z : Fin m → Bool, sgn (xor (R z)
              (linGen (fun i => xor (comb pair.1 pair.2 i 0 && comb pair.1 pair.2 i 1)
                (ν (comb pair.1 pair.2) i)) z)))
      · refine Fintype.sum_equiv splitEquiv _ _ fun u => ?_
        have hu : comb (splitEquiv u).1 (splitEquiv u).2 = u := splitEquiv.left_inv u
        rw [hu]
      · exact Fintype.sum_prod_type _
    rw [hstep_u]
    have hinner_z : ∀ (uP : P → Fin 2 → Bool) (uA : A → Fin 2 → Bool),
        (∑ z : Fin m → Bool, sgn (xor (R z)
          (linGen (fun i => xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i)) z))) =
        if uP ∈ SurvP then
          sgn (R (fun _ => false)) * (2 : ℤ) ^ P.card *
            (sgn (RA (invB (αA uP uA))) * W0)
        else 0 := by
      intro uP uA
      have hsplit_z : (∑ z : Fin m → Bool, sgn (xor (R z)
          (linGen (fun i => xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i)) z))) =
          sgn (R (fun _ => false)) *
            (∑ zP : P → Bool, sgn (linGen (fun p : P => xor (rP p) (αP uP p)) zP)) *
            (∑ zA : A → Bool, sgn (xor (RA zA) (linGen (αA uP uA) zA))) := by
        trans (∑ pair : (P → Bool) × (A → Bool),
            sgn (R (fun _ => false)) *
              sgn (linGen (fun p : P => xor (rP p) (αP uP p)) pair.1) *
              sgn (xor (RA pair.2) (linGen (αA uP uA) pair.2)))
        · refine Fintype.sum_equiv splitEquiv _ _ fun z => ?_
          have hz : comb (splitEquiv z).1 (splitEquiv z).2 = z := splitEquiv.left_inv z
          conv_lhs => rw [← hz]
          rw [hR_decomp, ← sgn_xor, ← sgn_xor]
          congr 1
          have hlin_split : linGen (fun i => xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i))
              (comb (splitEquiv z).1 (splitEquiv z).2) =
              xor (par (∑ p : P, (αP uP p && (splitEquiv z).1 p).toNat))
                  (linGen (αA uP uA) (splitEquiv z).2) := by
            unfold linGen
            rw [← par_add]
            congr 1
            have hPA : (∑ i : Fin m, (xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i) &&
                comb (splitEquiv z).1 (splitEquiv z).2 i).toNat) =
                (∑ i ∈ P, (xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i) &&
                  comb (splitEquiv z).1 (splitEquiv z).2 i).toNat) +
                (∑ i ∈ A, (xor (comb uP uA i 0 && comb uP uA i 1) (ν (comb uP uA) i) &&
                  comb (splitEquiv z).1 (splitEquiv z).2 i).toNat) := by
              rw [← Finset.sum_union disjoint_compl_right, finset_union_compl_self]
            rw [hPA]
            congr 1
            · rw [← Finset.sum_coe_sort P]
              refine Finset.sum_congr rfl fun p _ => ?_
              simp only [comb, p.2, ↓reduceDIte, αP]
              rw [hnu_P_indep uP uA p]
            · rw [← Finset.sum_coe_sort A]
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha : a.1 ∉ P := Finset.mem_compl.mp a.2
              simp only [comb, ha, ↓reduceDIte, αA]
          rw [hlin_split]
          have hP_xor : linGen (fun p : P => xor (rP p) (αP uP p)) (splitEquiv z).1 =
              xor (par (∑ p : P, (rP p && (splitEquiv z).1 p).toNat))
                  (par (∑ p : P, (αP uP p && (splitEquiv z).1 p).toNat)) := by
            unfold linGen
            rw [← par_sum_xor]
            congr 1
            refine Finset.sum_congr rfl fun p _ => by
              dsimp only
              cases rP p <;> cases αP uP p <;> cases (splitEquiv z).1 p <;> rfl
          rw [hP_xor]
          cases R (fun _ => false) <;>
            cases par (∑ p : P, (rP p && (splitEquiv z).1 p).toNat) <;>
            cases par (∑ p : P, (αP uP p && (splitEquiv z).1 p).toNat) <;>
            cases RA (splitEquiv z).2 <;> cases linGen (αA uP uA) (splitEquiv z).2 <;> rfl
        · rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
          rw [← Finset.mul_sum]
          ring
      rw [hsplit_z, hWRA_bent (αA uP uA)]
      have hsumP := sum_sgn_linGen (fun p : P => xor (rP p) (αP uP p))
      have hcardP : Fintype.card (P → Bool) = 2 ^ P.card := by simp [Fintype.card_pi]
      rw [hcardP] at hsumP
      have hiff : (fun p : P => xor (rP p) (αP uP p)) = (fun _ => false) ↔ uP ∈ SurvP := by
        simp only [SurvP, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h p
          have hp := congrFun h p
          cases h1 : rP p <;> cases h2 : αP uP p <;> simp [h1, h2] at hp ⊢
        · intro h; funext p; rw [h p]; cases rP p <;> rfl
      rw [hsumP]
      by_cases huP : uP ∈ SurvP
      · simp only [hiff.mpr huP, huP, ↓reduceIte]; push_cast; rfl
      · simp [mt hiff.mp huP, huP]
    simp_rw [hinner_z]
    have hstep_filt : (∑ uP : P → Fin 2 → Bool, ∑ uA : A → Fin 2 → Bool,
        sgn (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false))) *
          if uP ∈ SurvP then sgn (R (fun _ => false)) * (2 : ℤ) ^ P.card *
            (sgn (RA (invB (αA uP uA))) * W0) else 0) =
        ∑ uP ∈ SurvP, ∑ uA : A → Fin 2 → Bool,
          sgn (R (fun _ => false)) * (2 : ℤ) ^ P.card * W0 *
            sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
              (RA (invB (αA uP uA)))) := by
      have hsf : (Finset.univ : Finset (P → Fin 2 → Bool)).filter (fun uP => uP ∈ SurvP) = SurvP := by
        ext uP; simp
      conv_rhs => rw [← hsf, Finset.sum_filter]
      refine Finset.sum_congr rfl fun uP _ => ?_
      by_cases huP : uP ∈ SurvP
      · simp only [huP, ↓reduceIte]
        refine Finset.sum_congr rfl fun uA _ => ?_
        simp only [sgn_xor]; ring
      · simp [huP]
    rw [hstep_filt]
    symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun uP _ => Finset.mul_sum ..
  let Arest : Finset A := (Finset.univ.erase a₁).erase a₂
  have hArest_card : Arest.card = 2 * s - 2 := by
    have ha2_in : a₂ ∈ (Finset.univ : Finset A).erase a₁ :=
      Finset.mem_erase.mpr ⟨ha12_ne.symm, Finset.mem_univ a₂⟩
    rw [Finset.card_erase_of_mem ha2_in, Finset.card_erase_of_mem (Finset.mem_univ a₁),
      Finset.card_univ, Fintype.card_coe, hAcard]
    omega
  have h4_bound : ∀ (uP : P → Fin 2 → Bool),
      |∑ uA : A → Fin 2 → Bool,
        sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
          (RA (invB (αA uP uA))))| ≤ (2 : ℤ) ^ (4 * s - 4) * 14 := by
    intro uP
    let mkUA (uR : Arest → Fin 2 → Bool) (x : T4 → Bool) (a : A) : Fin 2 → Bool :=
      if h1 : a = a₁ then fun k => x (0, k)
      else if h2 : a = a₂ then fun k => x (1, k)
      else uR ⟨a, Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ a⟩⟩⟩
    let splitA : (A → Fin 2 → Bool) ≃ ((Arest → Fin 2 → Bool) × (T4 → Bool)) :=
      { toFun := fun uA =>
          (fun r => uA r.1,
           fun t => if t.1 = 0 then uA a₁ t.2 else uA a₂ t.2)
        invFun := fun pair => mkUA pair.1 pair.2
        left_inv := fun uA => by
          funext a k
          dsimp only [mkUA]
          by_cases h1 : a = a₁
          · subst h1; simp
          · by_cases h2 : a = a₂
            · subst h2; simp [h1]
            · simp [h1, h2]
        right_inv := fun ⟨uR, x⟩ => by
          apply Prod.ext
          · funext ⟨a, ha⟩ k
            have h2 : a ≠ a₂ := (Finset.mem_erase.mp ha).1
            have h1 : a ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
            simp [mkUA, h1, h2]
          · funext ⟨i, k⟩
            fin_cases i
            · simp [mkUA]
            · simp [mkUA, ha12_ne.symm] }
    rw [← Fintype.sum_equiv splitA.symm
      (fun pair => sgn (xor (xor (q (mergeLane lane (comb uP (mkUA pair.1 pair.2)) (fun _ => false)))
        (q (fun _ _ => false))) (RA (invB (αA uP (mkUA pair.1 pair.2))))))
      (fun uA => sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false)))
        (q (fun _ _ => false))) (RA (invB (αA uP uA)))))
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    calc |∑ uR : Arest → Fin 2 → Bool, ∑ x : T4 → Bool,
            sgn (xor (xor (q (mergeLane lane (comb uP (mkUA uR x)) (fun _ => false)))
              (q (fun _ _ => false))) (RA (invB (αA uP (mkUA uR x)))))|
        ≤ ∑ uR : Arest → Fin 2 → Bool, |∑ x : T4 → Bool,
            sgn (xor (xor (q (mergeLane lane (comb uP (mkUA uR x)) (fun _ => false)))
              (q (fun _ _ => false))) (RA (invB (αA uP (mkUA uR x)))))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _uR : Arest → Fin 2 → Bool, (14 : ℤ) := by
          refine Finset.sum_le_sum fun uR _ => ?_
          let uA_of : (T4 → Bool) → (A → Fin 2 → Bool) := mkUA uR
          have huA_a1 : ∀ x k, uA_of x a₁ k = x (0, k) := fun x k => by simp [uA_of, mkUA]
          have huA_a2 : ∀ x k, uA_of x a₂ k = x (1, k) := fun x k => by
            simp [uA_of, mkUA, ha12_ne.symm]
          have huA_aff : ∀ (a : A) (k : Fin 2),
              ∃ (c : Bool) (m : T4 → Bool), ∀ x, uA_of x a k = xor c (linGen m x) := by
            intro a k
            by_cases h1 : a = a₁
            · subst h1
              refine ⟨false, fun t => decide (t = (0, k)), fun x => ?_⟩
              rw [huA_a1, Bool.false_xor]
              unfold linGen
              have : (∑ t : T4, (decide (t = (0, k)) && x t).toNat) = (x (0, k)).toNat := by
                rw [Finset.sum_eq_single (0, k)]
                · simp
                · intro t _ hne; simp [hne]
                · intro h; exact absurd (Finset.mem_univ _) h
              rw [this, par_toNat]
            · by_cases h2 : a = a₂
              · subst h2
                refine ⟨false, fun t => decide (t = (1, k)), fun x => ?_⟩
                rw [huA_a2, Bool.false_xor]
                unfold linGen
                have : (∑ t : T4, (decide (t = (1, k)) && x t).toNat) = (x (1, k)).toNat := by
                  rw [Finset.sum_eq_single (1, k)]
                  · simp
                  · intro t _ hne; simp [hne]
                  · intro h; exact absurd (Finset.mem_univ _) h
                rw [this, par_toNat]
              · refine ⟨uR ⟨a, Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ a⟩⟩⟩ k,
                  fun _ => false, fun x => by simp [uA_of, mkUA, h1, h2, linGen, par]⟩
          have huVec_aff : ∀ p : Fin m × Fin 3,
              ∃ (c : Bool) (m : T4 → Bool), ∀ x, uVec (comb uP (uA_of x)) p = xor c (linGen m x) := by
            intro ⟨i, l⟩
            dsimp only [uVec, mergeLane]
            by_cases hl : l = lane i
            · refine ⟨false, fun _ => false, fun x => by simp [hl, linGen, par]⟩
            · by_cases hi : i ∈ P
              · refine ⟨if l = otherIdx (lane i) 0 then uP ⟨i, hi⟩ 0 else uP ⟨i, hi⟩ 1,
                  fun _ => false, fun x => by simp [hl, comb, hi, linGen, par]⟩
              · have hiA : i ∈ A := Finset.mem_compl.mpr hi
                by_cases h0 : l = otherIdx (lane i) 0
                · obtain ⟨c, mk, hmk⟩ := huA_aff ⟨i, hiA⟩ 0
                  refine ⟨c, mk, fun x => ?_⟩
                  rw [ite_eq_right_iff.mpr (fun h => absurd h hl),
                    ite_eq_left_iff.mpr (fun h => absurd h0 h)]
                  simp only [comb, hi, ↓reduceDIte, hmk]
                · obtain ⟨c, mk, hmk⟩ := huA_aff ⟨i, hiA⟩ 1
                  refine ⟨c, mk, fun x => ?_⟩
                  rw [ite_eq_right_iff.mpr (fun h => absurd h hl),
                    ite_eq_right_iff.mpr (fun h => absurd h h0)]
                  simp only [comb, hi, ↓reduceDIte, hmk]
          have hq0_quad : IsQuadGen (fun x : T4 → Bool =>
              xor (q (mergeLane lane (comb uP (uA_of x)) (fun _ => false))) (q (fun _ _ => false))) := by
            have hQv : IsQuadGen (fun v : (Fin m × Fin 3) → Bool => q (fun i l => v (i, l))) :=
              quad_to_gen q hq
            exact isQuadGen_xor (isQuadGen_comp_affine hQv (fun x => uVec (comb uP (uA_of x))) huVec_aff)
              (isQuadGen_const _)
          let Lx : (T4 → Bool) → (A → Bool) := fun x a =>
            xor (if a = a₁ ∨ a = a₂ then false else uA_of x a 0 && uA_of x a 1)
                (ν (comb uP (uA_of x)) a.1)
          have hLx_aff : ∀ a : A, ∃ (c : Bool) (m : T4 → Bool), ∀ x, Lx x a = xor c (linGen m x) := by
            intro a
            have hnu_aff : ∃ (c : Bool) (m : T4 → Bool),
                ∀ x, ν (comb uP (uA_of x)) a.1 = xor c (linGen m x) := by
              have := lin_comp_affine (fun p : Fin m × Fin 3 => Bcoeff p (a.1, lane a.1))
                (fun x => uVec (comb uP (uA_of x))) huVec_aff
              simpa only [ν, linGen] using this
            obtain ⟨cν, mν, hν⟩ := hnu_aff
            by_cases ha12 : a = a₁ ∨ a = a₂
            · refine ⟨cν, mν, fun x => by simp only [Lx, ha12, ↓reduceIte, Bool.false_xor, hν]⟩
            · have h1 : a ≠ a₁ := fun h => ha12 (Or.inl h)
              have h2 : a ≠ a₂ := fun h => ha12 (Or.inr h)
              let haR : a ∈ Arest :=
                Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ a⟩⟩
              refine ⟨xor (uR ⟨a, haR⟩ 0 && uR ⟨a, haR⟩ 1) cν, mν, fun x => ?_⟩
              have hconst : (uA_of x a 0 && uA_of x a 1) = (uR ⟨a, haR⟩ 0 && uR ⟨a, haR⟩ 1) := by
                simp only [uA_of, mkUA, h1, h2, ↓reduceDIte]
              simp only [Lx, ha12, ↓reduceIte, hconst, hν, Bool.xor_assoc]
          have hαA_decomp : ∀ x : T4 → Bool,
              αA uP (uA_of x) = fun a =>
                xor (xor ((x (0, 0) && x (0, 1)) && decide (a = a₁))
                         ((x (1, 0) && x (1, 1)) && decide (a = a₂))) (Lx x a) := by
            intro x; funext a
            dsimp only [αA, Lx]
            by_cases h1 : a = a₁
            · subst h1; simp [ha12_ne, huA_a1]
            · by_cases h2 : a = a₂
              · subst h2; simp [ha12_ne.symm, huA_a2]
              · simp [h1, h2]
          have hcongr : (∑ x : T4 → Bool,
              sgn (xor (xor (q (mergeLane lane (comb uP (uA_of x)) (fun _ => false))) (q (fun _ _ => false)))
                (RA (invB (αA uP (uA_of x)))))) =
              ∑ x : T4 → Bool,
                sgn (xor (xor (q (mergeLane lane (comb uP (uA_of x)) (fun _ => false))) (q (fun _ _ => false)))
                  (RA (invB (fun a =>
                    xor (xor ((x (0, 0) && x (0, 1)) && decide (a = a₁))
                             ((x (1, 0) && x (1, 1)) && decide (a = a₂))) (Lx x a))))) :=
            Finset.sum_congr rfl fun x _ => by rw [hαA_decomp x]
          change |∑ x : T4 → Bool,
              sgn (xor (xor (q (mergeLane lane (comb uP (uA_of x)) (fun _ => false))) (q (fun _ _ => false)))
                (RA (invB (αA uP (uA_of x)))))| ≤ 14
          rw [hcongr]
          exact quartic_section_le_14 RA hRA_quad hRA_zero invB hBA_invB hinvB_add hinvB_zero
            a₁ a₂ hBA_e12 _ hq0_quad Lx hLx_aff
      _ = (2 : ℤ) ^ (4 * s - 4) * 14 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          congr 1
          have hc : Fintype.card (Arest → Fin 2 → Bool) = 2 ^ (4 * s - 4) := by
            rw [Fintype.card_pi]
            simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin, Fintype.card_coe, hArest_card]
            rw [← pow_mul]; congr 1; omega
          rw [hc]; push_cast; rfl
  have hS_le : |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (4 * s - 4) * 14 := by
    rw [hS_factor, abs_mul, abs_mul, abs_mul, sgn_abs, one_mul,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ P.card), hWRA0_abs, hPcard]
    have hsum_le : |∑ uP ∈ SurvP, ∑ uA : A → Fin 2 → Bool,
        sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
          (RA (invB (αA uP uA))))| ≤ (3 : ℤ) ^ (m - 2 * s) * ((2 : ℤ) ^ (4 * s - 4) * 14) := by
      calc _ ≤ ∑ uP ∈ SurvP, |∑ uA : A → Fin 2 → Bool,
            sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
              (RA (invB (αA uP uA))))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _uP ∈ SurvP, ((2 : ℤ) ^ (4 * s - 4) * 14) :=
            Finset.sum_le_sum fun uP _ => h4_bound uP
        _ = (SurvP.card : ℤ) * ((2 : ℤ) ^ (4 * s - 4) * 14) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (3 : ℤ) ^ (m - 2 * s) * ((2 : ℤ) ^ (4 * s - 4) * 14) :=
            mul_le_mul_of_nonneg_right hSurvP_le (by positivity)
    calc (2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s *
          |∑ uP ∈ SurvP, ∑ uA : A → Fin 2 → Bool,
            sgn (xor (xor (q (mergeLane lane (comb uP uA) (fun _ => false))) (q (fun _ _ => false)))
              (RA (invB (αA uP uA))))|
        ≤ (2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * ((3 : ℤ) ^ (m - 2 * s) * ((2 : ℤ) ^ (4 * s - 4) * 14)) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = _ := by ring
  have hrhs_eq : 8 * (9 : ℤ) ^ s * ((2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (3 : ℤ) ^ (m - 2 * s) *
      (2 : ℤ) ^ (4 * s - 4) * 14) = 7 * (8 : ℤ) ^ s * (6 : ℤ) ^ m := by
    have h9 : (9 ^ s : ℤ) = 3 ^ (2 * s) := by rw [pow_mul]; norm_num
    have h8 : (8 ^ s : ℤ) = 2 ^ (3 * s) := by rw [pow_mul]; norm_num
    have h6 : (6 ^ m : ℤ) = 2 ^ m * 3 ^ m := by rw [← mul_pow]; norm_num
    rw [h9, h8, h6]
    have h3exp : (3 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s) = (3 : ℤ) ^ m := by
      rw [← pow_add]; congr 1; omega
    have h2exp : (2 : ℤ) ^ 4 * (2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (2 : ℤ) ^ (4 * s - 4) =
        (2 : ℤ) ^ (3 * s) * (2 : ℤ) ^ m := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1; omega
    calc 8 * (3 : ℤ) ^ (2 * s) * ((2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (3 : ℤ) ^ (m - 2 * s) *
          (2 : ℤ) ^ (4 * s - 4) * 14)
        = 7 * ((2 : ℤ) ^ 4 * (2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (2 : ℤ) ^ (4 * s - 4)) *
          ((3 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s)) := by ring
      _ = 7 * ((2 : ℤ) ^ (3 * s) * (2 : ℤ) ^ m) * (3 : ℤ) ^ m := by rw [h2exp, h3exp]
      _ = 7 * (2 : ℤ) ^ (3 * s) * ((2 : ℤ) ^ m * (3 : ℤ) ^ m) := by ring
  calc 8 * (9 : ℤ) ^ s * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|
      ≤ 8 * (9 : ℤ) ^ s * ((2 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ s * (3 : ℤ) ^ (m - 2 * s) *
          (2 : ℤ) ^ (4 * s - 4) * 14) := mul_le_mul_of_nonneg_left hS_le (by positivity)
    _ = 7 * (8 : ℤ) ^ s * (6 : ℤ) ^ m := hrhs_eq

private lemma lane_rank_bound_78 (m s : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3) (hs_pos : 0 < s) (hs : 2 * s ≤ m)
    (hrad : ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t : Fin m → Bool,
      xor (xor (q (fun i j => (j == lane i) && xor (h i) (t i)))
               (q (fun i j => (j == lane i) && h i)))
          (xor (q (fun i j => (j == lane i) && t i))
               (q (fun i j => (j == lane i) && false))) = false)).card = 2 ^ (m - 2 * s)) :
    8 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    7 * 8 ^ s * 6 ^ m := by
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hRquad : IsQuadGen R := restrict_isQuadGen q hq lane
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  have hRad_card : Rad.card = 2 ^ (m - 2 * s) := hrad
  obtain ⟨b0, l0, a0, hqeq⟩ := hq
  let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
    fun u p => mergeLane lane u (fun _ => false) p.1 p.2
  let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
    par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
  have hsum_split := sum_split_lane m q b0 l0 a0 hqeq lane
  dsimp only at hsum_split
  have hRad_sub : IsSubgroup Rad := by
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      unfold polar
      have : (fun i => xor false (t i)) = t := by funext i; simp
      rw [this]
      cases R t <;> cases R (fun _ => false) <;> rfl
    · intro a ha b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      rw [polar_xor_left hRquad, (Finset.mem_filter.mp ha).2 t, (Finset.mem_filter.mp hb).2 t]
      rfl
  have hmul_rad : (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
        |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
    have htri : |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
        ∑ u : Fin m → Fin 2 → Bool,
          |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := by
      rw [hsum_split]
      calc |∑ u : Fin m → Fin 2 → Bool,
              sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
                ∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))|
          ≤ ∑ u : Fin m → Fin 2 → Bool,
              |sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
                ∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ u : Fin m → Fin 2 → Bool,
              |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := by
            refine Finset.sum_congr rfl fun u _ => by rw [abs_mul, sgn_abs, one_mul]
    have h1 : (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
        (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
          |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| :=
      mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg _)
    have h2 : (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
        |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| =
        (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
          sgn (xor (R h) (R (fun _ => false))) *
            ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := by
      rw [Finset.mul_sum]
      have hterm : ∀ u : Fin m → Fin 2 → Bool,
          (Rad.card : ℤ) *
            |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| =
          (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            sgn (xor (R h) (R (fun _ => false))) *
              sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := fun u => by
        have hw := walsh_abs_eq_rad_sum R hRquad hs hRad_card (fun i => xor (u i 0 && u i 1) (ν u i))
        dsimp only at hw
        rw [hw]
        congr 1
        refine Finset.sum_congr rfl fun h _ => sgn_xor _ _
      simp_rw [hterm, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => (Finset.mul_sum ..).symm
    have h3 : ∑ h ∈ Rad,
        sgn (xor (R h) (R (fun _ => false))) *
          ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) ≤
        ∑ h ∈ Rad,
          |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
      refine Finset.sum_le_sum fun h _ => ?_
      calc sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)
          ≤ |sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| :=
            le_abs_self _
        _ = |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
            rw [abs_mul, sgn_abs, one_mul]
    calc (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|
        ≤ (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
            |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := h1
      _ = (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := h2
      _ ≤ (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hmul_rhs_id : (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
      ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) =
      (2 ^ (m - 2 * s) : ℤ) * (8 ^ s * 6 ^ m) := by
    have h9 : (9 ^ s : ℤ) = 3 ^ (2 * s) := by rw [pow_mul]; norm_num
    have h8 : (8 ^ s : ℤ) = 2 ^ (3 * s) := by rw [pow_mul]; norm_num
    have h6 : (6 ^ m : ℤ) = 2 ^ m * 3 ^ m := by rw [← mul_pow]; norm_num
    rw [h9, h8, h6]
    have h2exp : (2 ^ (m - s) : ℤ) * 2 ^ m * 2 ^ (2 * s) = 2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1; omega
    have h3exp : (3 ^ (2 * s) : ℤ) * 3 ^ (m - 2 * s) = 3 ^ m := by
      rw [← pow_add]; congr 1; omega
    calc (3 ^ (2 * s) : ℤ) * (2 ^ (m - s) * 2 ^ m * (3 ^ (m - 2 * s) * 2 ^ (2 * s)))
        = (3 ^ (2 * s) * 3 ^ (m - 2 * s)) * (2 ^ (m - s) * 2 ^ m * 2 ^ (2 * s)) := by ring
      _ = 3 ^ m * (2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m) := by rw [h3exp, h2exp]
      _ = 2 ^ (m - 2 * s) * (2 ^ (3 * s) * (2 ^ m * 3 ^ m)) := by ring
  rcases subgroup_coord_or_bound Rad hRad_sub hRad_card with ⟨P, hPcard, hRad_eq⟩ | hnoncoord
  · by_cases hactive : ∃ a₀ : Fin m, a₀ ∉ P ∧ ∃ b₀ : Fin 2, ∃ p₀ ∈ P,
        Bcoeff (a₀, otherIdx (lane a₀) b₀) (p₀, lane p₀) = true
    · obtain ⟨a₀, ha₀not, b₀, p₀, hp₀P, hBtrue⟩ := hactive
      let mask : Fin m → Bool := fun i => Bcoeff (a₀, otherIdx (lane a₀) b₀) (i, lane i)
      let Rad0 : Finset (Fin m → Bool) := Rad.filter (fun h => linGen mask h = false)
      have hsum_Rad : (∑ h ∈ Rad,
          |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) ≤
          (2 ^ m : ℤ) * ∑ h ∈ Rad0, (2 ^ (m - wt h) : ℤ) := by
        have hzero : ∀ h ∈ Rad, linGen mask h = true →
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| = 0 := by
          intro h hh hlin
          have hha0 : h a₀ = false := by
            rw [hRad_eq] at hh
            exact (Finset.mem_filter.mp hh).2 a₀ ha₀not
          have hz := lane_u_sum_zero_of_active_d lane Bcoeff h a₀ hha0 b₀ hlin
          dsimp only at hz
          rw [hz, abs_zero]
        have hfilt : (∑ h ∈ Rad,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) =
            ∑ h ∈ Rad0,
              |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun h hh hnot => ?_
          have htrue : linGen mask h = true := by
            cases hm : linGen mask h
            · exact absurd (Finset.mem_filter.mpr ⟨hh, hm⟩) hnot
            · rfl
          exact hzero h hh htrue
        rw [hfilt, Finset.mul_sum]
        refine Finset.sum_le_sum fun h _ => lane_u_factor_bound m lane Bcoeff h
      have hRad0_bound : 3 * ∑ h ∈ Rad0, (2 ^ (m - wt h) : ℤ) ≤
          2 * ((3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (2 * s)) := by
        let extP : (P → Bool) → (Fin m → Bool) := fun x i =>
          if hi : i ∈ P then x ⟨i, hi⟩ else false
        have hbij : (∑ h ∈ Rad0, (2 ^ (m - wt h) : ℤ)) =
            (2 : ℤ) ^ (2 * s) * ∑ x : P → Bool,
              if par (∑ p : P, (mask p.1 && x p).toNat) = false then
                ∏ p : P, (if x p then (1 : ℤ) else 2)
              else 0 := by
          rw [← Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_bij (fun h _ => fun p : P => h p.1) ?_ ?_ ?_ ?_
          · intro h hh
            simp only [Rad0, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
            rw [hRad_eq] at hh
            have hout := (Finset.mem_filter.mp hh.1).2
            have hlin_eq : linGen mask h = par (∑ p : P, (mask p.1 && h p.1).toNat) := by
              unfold linGen
              congr 1
              trans (∑ i ∈ P, (mask i && h i).toNat)
              · symm
                refine Finset.sum_subset (Finset.subset_univ P) fun i _ hi => ?_
                simp [hout i hi]
              · exact (Finset.sum_coe_sort P (fun i => (mask i && h i).toNat)).symm
            rw [← hlin_eq]
            exact hh.2
          · intro h₁ hh₁ h₂ hh₂ hEq
            have h1 := (Finset.mem_filter.mp (hRad_eq ▸ (Finset.mem_filter.mp hh₁).1)).2
            have h2 := (Finset.mem_filter.mp (hRad_eq ▸ (Finset.mem_filter.mp hh₂).1)).2
            funext i
            by_cases hi : i ∈ P
            · exact congrFun hEq ⟨i, hi⟩
            · rw [h1 i hi, h2 i hi]
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            refine ⟨extP x, ?_, funext fun p => by simp [extP, p.2]⟩
            simp only [Rad0, Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [hRad_eq]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              intro i hi; simp [extP, hi]
            · unfold linGen
              have hsum_eq : (∑ i : Fin m, (mask i && extP x i).toNat) =
                  ∑ p : P, (mask p.1 && x p).toNat := by
                trans (∑ i ∈ P, (mask i && extP x i).toNat)
                · symm
                  refine Finset.sum_subset (Finset.subset_univ P) fun i _ hi => ?_
                  simp [extP, hi]
                · rw [← Finset.sum_coe_sort P (fun i => (mask i && extP x i).toNat)]
                  refine Finset.sum_congr rfl fun p _ => by simp [extP, p.2]
              rw [hsum_eq]; exact hx
          · intro h hh
            rw [show (2 ^ (m - wt h) : ℤ) = ((2 ^ (m - wt h) : ℕ) : ℤ) by push_cast; rfl,
              two_pow_sub_wt_eq_prod h]
            have hout := (Finset.mem_filter.mp (hRad_eq ▸ (Finset.mem_filter.mp hh).1)).2
            have hsplit : (∏ i : Fin m, (if h i then (1 : ℤ) else 2)) =
                (∏ i ∈ Pᶜ, (if h i then (1 : ℤ) else 2)) *
                (∏ i ∈ P, (if h i then (1 : ℤ) else 2)) := by
              rw [← Finset.prod_union disjoint_compl_left, finset_compl_union_self]
            rw [hsplit]
            congr 1
            · have h2s : (∏ i ∈ Pᶜ, (if h i then (1 : ℤ) else 2)) = ∏ _i ∈ Pᶜ, (2 : ℤ) :=
                Finset.prod_congr rfl fun i hi => by simp [hout i (Finset.mem_compl.mp hi)]
              rw [h2s, Finset.prod_const, Finset.card_compl, Fintype.card_fin, hPcard]
              congr 1; omega
            · rw [← Finset.prod_coe_sort P]
        rw [hbij]
        have h2sum : 2 * (∑ x : P → Bool,
            if par (∑ p : P, (mask p.1 && x p).toNat) = false then
              ∏ p : P, (if x p then (1 : ℤ) else 2)
            else 0) ≤
            (3 : ℤ) ^ (m - 2 * s) + (3 : ℤ) ^ (m - 2 * s - 1) := by
          have hpt : ∀ x : P → Bool,
              2 * (if par (∑ p : P, (mask p.1 && x p).toNat) = false then
                ∏ p : P, (if x p then (1 : ℤ) else 2)
              else 0) =
              (∏ p : P, (if x p then (1 : ℤ) else 2)) +
              sgn (par (∑ p : P, (mask p.1 && x p).toNat)) *
                ∏ p : P, (if x p then (1 : ℤ) else 2) := fun x => by
            cases par (∑ p : P, (mask p.1 && x p).toNat)
            · simp [sgn]; ring
            · simp [sgn]
          rw [Finset.mul_sum]
          simp_rw [hpt, Finset.sum_add_distrib]
          rw [sum_tilted_all P, hPcard]
          have hp := sum_tilted_parity P mask ⟨p₀, hp₀P, hBtrue⟩
          rw [hPcard] at hp
          linarith
        have hPpos : 1 ≤ m - 2 * s := by
          have : 0 < P.card := Finset.card_pos.mpr ⟨p₀, hp₀P⟩
          omega
        have h3eq : 3 * ((3 : ℤ) ^ (m - 2 * s) + (3 : ℤ) ^ (m - 2 * s - 1)) =
            4 * (3 : ℤ) ^ (m - 2 * s) := by
          have h3k : 3 * (3 : ℤ) ^ (m - 2 * s - 1) = (3 : ℤ) ^ (m - 2 * s) := by
            rw [← pow_succ']; congr 1; omega
          linarith
        have h6le : 2 * (3 * ((2 : ℤ) ^ (2 * s) * ∑ x : P → Bool,
            if par (∑ p : P, (mask p.1 && x p).toNat) = false then
              ∏ p : P, (if x p then (1 : ℤ) else 2)
            else 0)) ≤ 2 * (2 * ((3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (2 * s))) := by
          calc 2 * (3 * ((2 : ℤ) ^ (2 * s) * ∑ x : P → Bool,
                  if par (∑ p : P, (mask p.1 && x p).toNat) = false then
                    ∏ p : P, (if x p then (1 : ℤ) else 2)
                  else 0))
              = 3 * (2 : ℤ) ^ (2 * s) * (2 * ∑ x : P → Bool,
                  if par (∑ p : P, (mask p.1 && x p).toNat) = false then
                    ∏ p : P, (if x p then (1 : ℤ) else 2)
                  else 0) := by ring
            _ ≤ 3 * (2 : ℤ) ^ (2 * s) * ((3 : ℤ) ^ (m - 2 * s) + (3 : ℤ) ^ (m - 2 * s - 1)) :=
                  mul_le_mul_of_nonneg_left h2sum (by positivity)
            _ = (2 : ℤ) ^ (2 * s) * (3 * ((3 : ℤ) ^ (m - 2 * s) + (3 : ℤ) ^ (m - 2 * s - 1))) := by ring
            _ = (2 : ℤ) ^ (2 * s) * (4 * (3 : ℤ) ^ (m - 2 * s)) := by rw [h3eq]
            _ = 2 * (2 * ((3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (2 * s))) := by ring
        linarith
      have h3main : (2 ^ (m - 2 * s) : ℤ) * (3 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) ≤
          (2 ^ (m - 2 * s) : ℤ) * (2 * 8 ^ s * 6 ^ m) := by
        calc (2 ^ (m - 2 * s) : ℤ) * (3 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)
            = 3 * (9 ^ s : ℤ) * ((Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by
              rw [hRad_card]; push_cast; ring
          _ ≤ 3 * (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
                |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) :=
              mul_le_mul_of_nonneg_left hmul_rad (by positivity)
          _ ≤ 3 * (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * ((2 ^ m : ℤ) * ∑ h ∈ Rad0, (2 ^ (m - wt h) : ℤ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_Rad (by positivity)) (by positivity)
          _ = (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (3 * ∑ h ∈ Rad0, (2 ^ (m - wt h) : ℤ))) := by ring
          _ ≤ (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (2 * ((3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (2 * s)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRad0_bound (by positivity)) (by positivity)
          _ = 2 * ((9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) := by ring
          _ = (2 ^ (m - 2 * s) : ℤ) * (2 * 8 ^ s * 6 ^ m) := by rw [hmul_rhs_id]; ring
      have h3bound := le_of_mul_le_mul_left h3main (by positivity : (0 : ℤ) < 2 ^ (m - 2 * s))
      have hpos : (0 : ℤ) ≤ 8 ^ s * 6 ^ m := by positivity
      linarith
    · push Not at hactive
      have hno_act : ∀ a ∈ Pᶜ, ∀ b : Fin 2, ∀ p ∈ P,
          xor (a0 (a, otherIdx (lane a) b) (p, lane p)) (a0 (p, lane p) (a, otherIdx (lane a) b)) = false := by
        intro a ha b p hp
        cases h : Bcoeff (a, otherIdx (lane a) b) (p, lane p)
        · exact h
        · exact absurd h (hactive a (Finset.mem_compl.mp ha) b p hp)
      exact coord_no_active_bound_78 m s q b0 l0 a0 hqeq lane hs_pos hs P hPcard hRad_eq hno_act
  · have h6main : (2 ^ (m - 2 * s) : ℤ) * (6 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) ≤
        (2 ^ (m - 2 * s) : ℤ) * (5 * 8 ^ s * 6 ^ m) := by
      have hsub : m - (m - 2 * s) = 2 * s := by omega
      rw [hsub] at hnoncoord
      calc (2 ^ (m - 2 * s) : ℤ) * (6 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)
          = 6 * (9 ^ s : ℤ) * ((Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by
            rw [hRad_card]; push_cast; ring
        _ ≤ 6 * (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
              |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) :=
            mul_le_mul_of_nonneg_left hmul_rad (by positivity)
        _ ≤ 6 * (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad, (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun h _ => lane_u_factor_bound m lane Bcoeff h) (by positivity)) (by positivity)
        _ = (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (6 * ∑ h ∈ Rad, (2 ^ (m - wt h) : ℤ))) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (5 * (3 : ℤ) ^ (m - 2 * s) * (2 : ℤ) ^ (2 * s))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnoncoord (by positivity)) (by positivity)
        _ = 5 * ((9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) := by ring
        _ = (2 ^ (m - 2 * s) : ℤ) * (5 * 8 ^ s * 6 ^ m) := by rw [hmul_rhs_id]; ring
    have h6bound := le_of_mul_le_mul_left h6main (by positivity : (0 : ℤ) < 2 ^ (m - 2 * s))
    have hpos : (0 : ℤ) ≤ 8 ^ s * 6 ^ m := by positivity
    linarith

private lemma cross_gap_bound_28 (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (i j : Fin m × Fin 3) (hij : i.1 ≠ j.1) (hcross : xor (a0 i j) (a0 j i) = true) :
    |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))| ≤
    28 * 6 ^ (m - 2) := by
  have hm2 : 2 ≤ m := by
    have h1 := i.1.isLt; have h2 := j.1.isLt
    have hne : i.1.val ≠ j.1.val := fun h => hij (Fin.ext h)
    omega
  let lane : Fin m → Fin 3 := fun k => if k = i.1 then i.2 else if k = j.1 then j.2 else 0
  have hlane_i : lane i.1 = i.2 := by simp [lane]
  have hlane_j : lane j.1 = j.2 := by simp [lane, hij.symm]
  let R : (Fin m → Bool) → Bool := fun z => q (fun k l => (l == lane k) && z k)
  have hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)) :=
    ⟨b0, l0, a0, hqeq⟩
  obtain ⟨s, hs, hrad⟩ := symplectic_rad_card R (restrict_isQuadGen q hq lane)
  have hpol_true : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = true := by
    let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun h l => v (h, l))
    let ei : (Fin m × Fin 3) → Bool := fun p => decide (p = i)
    let ej : (Fin m × Fin 3) → Bool := fun p => decide (p = j)
    have hR1 : ∀ z : Fin m → Bool, R z = Qv (fun p => (p.2 == lane p.1) && z p.1) := fun _ => rfl
    have he1 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && decide (p.1 = i.1)) = ei := by
      funext ⟨k, l⟩; rcases i with ⟨i1, i2⟩
      by_cases hk : k = i1
      · subst hk; by_cases hl : l = i2
        · subst hl; simp [ei, hlane_i]
        · simp [ei, hlane_i, hl, beq_false_of_ne hl]
      · simp [ei, hk]
    have he2 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && decide (p.1 = j.1)) = ej := by
      funext ⟨k, l⟩; rcases j with ⟨j1, j2⟩
      by_cases hk : k = j1
      · subst hk; by_cases hl : l = j2
        · subst hl; simp [ej, hlane_j]
        · simp [ej, hlane_j, hl, beq_false_of_ne hl]
      · simp [ej, hk]
    have he12 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && xor (decide (p.1 = i.1)) (decide (p.1 = j.1))) =
        fun p => xor (ei p) (ej p) := by
      funext p
      have h1 := congrFun he1 p; have h2 := congrFun he2 p
      rw [← h1, ← h2]
      cases (p.2 == lane p.1) <;> cases decide (p.1 = i.1) <;> cases decide (p.1 = j.1) <;> rfl
    have he0 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && false) = fun _ => false := by
      funext p; simp
    have hpeq : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = polar Qv ei ej := by
      unfold polar; rw [hR1, hR1, hR1, hR1, he1, he2, he12, he0]
    rw [hpeq]
    have hpeq2 : polar Qv ei ej = polar (quadFormGen b0 l0 a0) ei ej := by
      unfold polar Qv; simp only [hqeq]; rfl
    rw [hpeq2, polar_quadFormGen]
    have hsum : (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
        (xor (a0 p₁ p₂) (a0 p₂ p₁) && ei p₁ && ej p₂).toNat) = (xor (a0 i j) (a0 j i)).toNat := by
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp [ei, ej]
        · intro p₂ _ hne; simp [ej, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p₁ _ hne
        refine Finset.sum_eq_zero fun p₂ _ => by simp [ei, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, par_toNat, hcross]
  have hs_pos : 0 < s := by
    by_contra hs0
    have hse : s = 0 := by omega
    subst hse
    simp only [Nat.mul_zero, Nat.sub_zero] at hrad
    have hall : (Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hrad, Finset.card_univ, Fintype.card_pi]
      simp
    have hmem : (fun k : Fin m => decide (k = i.1)) ∈
        Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false) := by
      rw [hall]; exact Finset.mem_univ _
    have hfalse := (Finset.mem_filter.mp hmem).2 (fun k => decide (k = j.1))
    rw [hpol_true] at hfalse
    exact Bool.noConfusion hfalse
  have hb := lane_rank_bound_78 m s q hq lane hs_pos hs hrad
  have h89 : 9 * (8 : ℤ) ^ s ≤ 8 * (9 : ℤ) ^ s := by
    have hpow : (8 : ℤ) ^ (s - 1) ≤ (9 : ℤ) ^ (s - 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) (s - 1)
    have h8s : (8 : ℤ) ^ s = 8 * (8 : ℤ) ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    have h9s : (9 : ℤ) ^ s = 9 * (9 : ℤ) ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h8s, h9s]
    linarith
  have h6eq : 7 * (6 : ℤ) ^ m = 9 * (28 * (6 : ℤ) ^ (m - 2)) := by
    have h6m : (6 : ℤ) ^ m = 36 * (6 : ℤ) ^ (m - 2) := by
      have : (36 : ℤ) = 6 ^ 2 := by norm_num
      rw [this, ← pow_add]; congr 1; omega
    rw [h6m]; ring
  have hmul : (8 * (9 : ℤ) ^ s) * (9 * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|) ≤
      (8 * (9 : ℤ) ^ s) * (9 * (28 * (6 : ℤ) ^ (m - 2))) := by
    calc (8 * (9 : ℤ) ^ s) * (9 * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|)
        = 9 * (8 * (9 : ℤ) ^ s * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|) := by ring
      _ ≤ 9 * (7 * (8 : ℤ) ^ s * (6 : ℤ) ^ m) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 7 * (9 * (8 : ℤ) ^ s) * (6 : ℤ) ^ m := by ring
      _ ≤ 7 * (8 * (9 : ℤ) ^ s) * (6 : ℤ) ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h89 (by norm_num)) (by positivity)
      _ = (8 * (9 : ℤ) ^ s) * (7 * (6 : ℤ) ^ m) := by ring
      _ = (8 * (9 : ℤ) ^ s) * (9 * (28 * (6 : ℤ) ^ (m - 2))) := by rw [h6eq]
  have h9le := le_of_mul_le_mul_left hmul (by positivity : (0 : ℤ) < 8 * (9 : ℤ) ^ s)
  linarith

private lemma no_cross_lt_six_pow_le_28 (m : ℕ) (hm : 2 ≤ m) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (hno_cross : ∀ p₁ p₂ : Fin m × Fin 3, p₁.1 ≠ p₂.1 → a0 p₁ p₂ = a0 p₂ p₁)
    (hlt : |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| < 6 ^ m) :
    |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤ 28 * 6 ^ (m - 2) := by
  let qi : Fin m → (Fin 3 → Bool) → Bool := fun i x =>
    quadFormGen false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂)) x
  have hq_split : ∀ w : Fin m → Fin 3 → Bool,
      q w = xor b0 (par (∑ i : Fin m, (qi i (w i)).toNat)) := by
    intro w
    rw [hqeq w]
    have hlin_split : par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat) =
        par (∑ i : Fin m, (linGen (fun k => l0 (i, k)) (w i)).toNat) := by
      rw [Fintype.sum_prod_type]
      refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
      unfold linGen par
      have hm2 : (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 0 ∨
          (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 1 := by omega
      rcases hm2 with hm2 | hm2 <;> simp [hm2]
    have hquad_split : par (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
        (a0 p₁ p₂ && w p₁.1 p₁.2 && w p₂.1 p₂.2).toNat) =
        par (∑ i : Fin m, (par (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
          (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat)).toNat) := by
      have hpair : (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
          (a0 p₁ p₂ && w p₁.1 p₁.2 && w p₂.1 p₂.2).toNat) =
          ∑ p : (Fin m × Fin 3) × (Fin m × Fin 3),
            (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat :=
        (Fintype.sum_prod_type (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) =>
          (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat)).symm
      rw [hpair]
      let F : (Fin m × Fin 3) × (Fin m × Fin 3) → ℕ :=
        fun p => (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat
      have hpart : ∑ p : (Fin m × Fin 3) × (Fin m × Fin 3), F p =
          (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 = p.2.1), F p) +
          (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 < p.2.1), F p) +
          (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.2.1 < p.1.1), F p) := by
        rw [← Finset.sum_union, ← Finset.sum_union]
        · congr 1
          ext p
          simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
          rcases lt_trichotomy p.1.1 p.2.1 with h | h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          rcases hp1 with h | h <;> omega
        · rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          omega
      have hlt_gt : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.2.1 < p.1.1), F p) =
          ∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 < p.2.1), F p := by
        refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
        · intro p₁ _ p₂ _ h; exact Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
        · intro p hp
          refine ⟨(p.2, p.1), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
        · intro p hp
          have hne : p.1.1 ≠ p.2.1 := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; omega
          dsimp only [F]
          rw [hno_cross p.1 p.2 hne]
          congr 1
          cases a0 p.2 p.1 <;> cases w p.1.1 p.1.2 <;> cases w p.2.1 p.2.2 <;> rfl
      have hdiag : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 = p.2.1), F p) =
          ∑ i : Fin m, ∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat := by
        rw [Finset.sum_filter]
        trans (∑ i : Fin m, ∑ k₁ : Fin 3, ∑ p₂ : Fin m × Fin 3,
            if i = p₂.1 then F ((i, k₁), p₂) else 0)
        · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k₁ _ => ?_
          rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
          · simp [F]
          · intro j _ hne
            refine Finset.sum_eq_zero fun k₂ _ => by simp [hne.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
      rw [hpart, hlt_gt, hdiag]
      have heven : ∀ a b : ℕ, par (a + b + b) = par a := fun a b => by
        have : (a + b + b) % 2 = a % 2 := by omega
        simp [par, this]
      rw [heven]
      refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
      unfold par
      have hm2 : (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 0 ∨
          (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 1 := by omega
      rcases hm2 with hm2 | hm2 <;> simp [hm2]
    rw [hlin_split, hquad_split, Bool.xor_assoc, ← par_sum_xor]
    congr 2
    refine Finset.sum_congr rfl fun i _ => by simp [qi, quadFormGen]
  have hprod : |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| =
      ∏ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| := by
    have h1 : ∀ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w)) =
        sgn b0 * ∏ i : Fin m, sgn (xor (w i 0 && w i 1 && w i 2) (qi i (w i))) := fun w => by
      rw [hq_split w, ← sgn_par_sum, ← sgn_xor, par_sum_xor]
      congr 1
      cases par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) <;>
        cases b0 <;> cases par (∑ i : Fin m, (qi i (w i)).toNat) <;> rfl
    simp_rw [h1, ← Finset.mul_sum, abs_mul, sgn_abs, one_mul]
    rw [sum_prod_fin_fun (fun i x => sgn (xor (x 0 && x 1 && x 2) (qi i x))), abs_prod_eq_prod_abs]
  have hle6 : ∀ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| ≤ 6 :=
    fun i => (single_triple_quad_bound false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂))).1
  have heven : ∀ i : Fin m,
      2 ∣ |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| := by
    intro i
    have hpt : ∀ x : Fin 3 → Bool,
        sgn (xor (x 0 && x 1 && x 2) (qi i x)) = 1 - 2 * ((xor (x 0 && x 1 && x 2) (qi i x)).toNat : ℤ) :=
      fun x => by cases xor (x 0 && x 1 && x 2) (qi i x) <;> decide
    have hsum : (∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))) =
        2 * (4 - ∑ x : Fin 3 → Bool, ((xor (x 0 && x 1 && x 2) (qi i x)).toNat : ℤ)) := by
      simp_rw [hpt]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
      have hc : Fintype.card (Fin 3 → Bool) = 8 := by decide
      rw [hc]; ring
    rw [hsum, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    exact dvd_mul_right 2 _
  have hex : ∃ i₀ : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| < 6 := by
    by_contra hall
    push Not at hall
    have heq6 : ∀ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| = 6 :=
      fun i => le_antisymm (hle6 i) (hall i)
    rw [hprod] at hlt
    simp_rw [heq6] at hlt
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨i₀, hi₀_lt⟩ := hex
  have hi₀_le4 : |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| ≤ 4 := by
    obtain ⟨t, ht⟩ := heven i₀
    omega
  rw [hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hrest_le : (∏ i ∈ (Finset.univ : Finset (Fin m)).erase i₀,
      |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))|) ≤ 6 ^ (m - 1) := by
    calc _ ≤ ∏ _i ∈ (Finset.univ : Finset (Fin m)).erase i₀, (6 : ℤ) :=
          prod_le_prod_nonneg _ _ _ (fun _ _ => abs_nonneg _) (fun i _ => hle6 i)
      _ = 6 ^ (m - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
            Finset.card_univ, Fintype.card_fin]
  have h6eq : 4 * (6 : ℤ) ^ (m - 1) = 24 * (6 : ℤ) ^ (m - 2) := by
    have h1 : (6 : ℤ) ^ (m - 1) = 6 * (6 : ℤ) ^ (m - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [h1]; ring
  calc |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| *
        ∏ i ∈ (Finset.univ : Finset (Fin m)).erase i₀,
          |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))|
      ≤ 4 * (6 : ℤ) ^ (m - 1) :=
        mul_le_mul hi₀_le4 hrest_le (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)
    _ = 24 * (6 : ℤ) ^ (m - 2) := h6eq
    _ ≤ 28 * (6 : ℤ) ^ (m - 2) := by
        have : (0 : ℤ) ≤ 6 ^ (m - 2) := by positivity
        linarith

end PEqualNP.Outside.L_lib_441_aux

theorem PEqualNP.Outside.L_lib_441 : (∀ m : Nat,
  let W := Fin m → Fin 3 → Bool
  let J := Fin m × Fin 3
  let get := fun (w : W) (j : J) => w j.1 j.2
  let par := fun (n : Nat) => n % 2 == 1
  let lin := fun (mask : J → Bool) (w : W) =>
    par (∑ j : J, (mask j && get w j).toNat)
  let quad := fun (q : W → Bool) => ∃ (b : Bool) (l : J → Bool) (a : J → J → Bool),
    ∀ w, q w = xor (xor b (lin l w))
      (par (∑ i : J, ∑ j : J, (a i j && get w i && get w j).toNat))
  let f := fun (w : W) => par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)
  let gap := fun (S : Finset W) (q : W → Bool) =>
    ((2 : Int) * ((S.filter (fun w => f w == q w)).card : Int) - (S.card : Int)).natAbs
  let flip := fun (w : W) (i : J) (h : Fin m) (l : Fin 3) =>
    xor (w h l) (decide ((h,l) = i))
  let cross := fun (q : W → Bool) => ∃ (i j : J) (w : W), i.1 ≠ j.1 ∧
    xor (xor (q w) (q (flip w i))) (xor (q (flip w j)) (q (flip (flip w i) j))) = true
  let radicalSize := fun (q : W → Bool) (lane : Fin m → Fin 3) =>
    let restrict := fun (z : Fin m → Bool) => q (fun i j => (j == lane i) && z i)
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t : Fin m → Bool,
      xor (xor (restrict (fun i => xor (h i) (t i))) (restrict h))
        (xor (restrict t) (restrict (fun _ => false))) = false)).card
  (∀ q : W → Bool, quad q →
    (∀ (lane : Fin m → Fin 3) (s : Nat), 0 < s → 2*s ≤ m →
      radicalSize q lane = 2^(m-2*s) → 8 * 9^s * gap Finset.univ q ≤ 7 * 8^s * 6^m) ∧
    (2 ≤ m → (gap Finset.univ q < 6^m ↔ gap Finset.univ q ≤ 28*6^(m-2))) ∧
    (cross q → gap Finset.univ q ≤ 28*6^(m-2))) ∧
  (2 ≤ m → ∃ q : W → Bool, quad q ∧ cross q ∧ gap Finset.univ q = 28*6^(m-2))) := by
  intro m W J get par lin quad f gap flip cross radicalSize
  constructor
  · intro q hq
    have hgap_int : (gap Finset.univ q : ℤ) =
        |∑ w : Fin m → Fin 3 → Bool,
          PEqualNP.Outside.L_lib_416_aux.sgn
            (xor (PEqualNP.Outside.L_lib_416_aux.par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| := by
      dsimp only [gap]
      rw [← Int.abs_eq_natAbs, PEqualNP.Outside.L_lib_416_aux.gap_eq_natAbs_sum]
      rfl
    have hcross_bound : cross q → gap Finset.univ q ≤ 28 * 6 ^ (m - 2) := by
      intro hcr
      obtain ⟨b0, l0, a0, hqeq⟩ := hq
      obtain ⟨i, j, w, hij, hdiff⟩ := hcr
      have hxt : xor (a0 i j) (a0 j i) = true := by
        have := PEqualNP.Outside.L_lib_416_aux.flip_second_diff q b0 l0 a0 hqeq i j w
        dsimp only at this
        rw [← this]; exact hdiff
      have h := PEqualNP.Outside.L_lib_441_aux.cross_gap_bound_28 m q b0 l0 a0 hqeq i j hij hxt
      rw [← hgap_int] at h
      exact_mod_cast h
    refine ⟨?_, ?_, hcross_bound⟩
    · intro lane s hs_pos hs hrad
      have h := PEqualNP.Outside.L_lib_441_aux.lane_rank_bound_78 m s q hq lane hs_pos hs hrad
      rw [← hgap_int] at h
      exact_mod_cast h
    · intro hm
      constructor
      · intro hlt
        by_cases hcr : cross q
        · exact hcross_bound hcr
        · obtain ⟨b0, l0, a0, hqeq⟩ := hq
          have hno_cross : ∀ p₁ p₂ : Fin m × Fin 3, p₁.1 ≠ p₂.1 → a0 p₁ p₂ = a0 p₂ p₁ := by
            intro p₁ p₂ hne
            by_contra hdiff
            have hxt : xor (a0 p₁ p₂) (a0 p₂ p₁) = true := by
              cases h1 : a0 p₁ p₂ <;> cases h2 : a0 p₂ p₁ <;> simp_all
            apply hcr
            refine ⟨p₁, p₂, fun _ _ => false, hne, ?_⟩
            have := PEqualNP.Outside.L_lib_416_aux.flip_second_diff q b0 l0 a0 hqeq p₁ p₂ (fun _ _ => false)
            dsimp only at this
            rw [this]; exact hxt
          have hlt_int : |∑ w : Fin m → Fin 3 → Bool,
              PEqualNP.Outside.L_lib_416_aux.sgn
                (xor (PEqualNP.Outside.L_lib_416_aux.par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| <
              6 ^ m := by
            rw [← hgap_int]; exact_mod_cast hlt
          have h := PEqualNP.Outside.L_lib_441_aux.no_cross_lt_six_pow_le_28 m hm q b0 l0 a0 hqeq hno_cross hlt_int
          rw [← hgap_int] at h
          exact_mod_cast h
      · intro hle
        have h6 : 6 ^ m = 36 * 6 ^ (m - 2) := by
          have : 36 = 6 ^ 2 := by norm_num
          rw [this, ← pow_add]; congr 1; omega
        have hpos : 0 < 6 ^ (m - 2) := by positivity
        omega
  · intro hm
    exact (PEqualNP.Outside.L_lib_416 m).2 hm
