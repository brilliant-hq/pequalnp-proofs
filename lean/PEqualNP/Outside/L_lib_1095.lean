import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1095

-- Character orthogonality is adapted from the pinned L_lib_1029.
section ProofBody

private abbrev V (q : ℕ) : Type := Fin q → ZMod 2

private def dot {q : ℕ} (a x : V q) : ZMod 2 := ∑ i, a i * x i

private def chi {q : ℕ} (a x : V q) : ℚ := if dot a x = 0 then 1 else -1

private lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

private lemma v_add_self {q : ℕ} (a : V q) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (a i) with h | h <;> rw [h] <;> decide

private lemma v_add_eq_zero_iff {q : ℕ} (a b : V q) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    have hi : a i + b i = 0 := congrFun h i
    rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
      simp [ha, hb] at hi ⊢
  · rintro rfl; exact v_add_self a

private lemma dot_zero_left {q : ℕ} (x : V q) : dot (0 : V q) x = 0 := by
  simp [dot]

private lemma dot_add_left {q : ℕ} (a b x : V q) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {q : ℕ} (a x y : V q) : dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma chi_zero {q : ℕ} (x : V q) : chi (0 : V q) x = 1 := by
  simp [chi, dot_zero_left]

private lemma chi_mul_left {q : ℕ} (a b x : V q) : chi a x * chi b x = chi (a + b) x := by
  unfold chi
  rw [dot_add_left]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with ha | ha <;> rcases zmod2_cases (dot b x) with hb | hb <;>
    simp [ha, hb, h11]

private lemma chi_mul_right {q : ℕ} (a x y : V q) : chi a (x + y) = chi a x * chi a y := by
  unfold chi
  rw [dot_add_right]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with hx | hx <;> rcases zmod2_cases (dot a y) with hy | hy <;>
    simp [hx, hy, h11]

private lemma chi_sq {q : ℕ} (a x : V q) : chi a x * chi a x = 1 := by
  rw [chi_mul_left, v_add_self, chi_zero]

private lemma one_sub_chi {q : ℕ} (a x : V q) :
    1 - chi a x = if dot a x = 0 then 0 else 2 := by
  unfold chi
  split_ifs <;> norm_num

private lemma card_V (q : ℕ) : (Fintype.card (V q) : ℚ) = (2 : ℚ) ^ q := by
  have h : Fintype.card (V q) = 2 ^ q := by
    simp [V, ZMod.card]
  exact_mod_cast h

private lemma sum_chi {q : ℕ} (a : V q) :
    ∑ x : V q, chi a x = if a = 0 then (2 : ℚ) ^ q else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ↓reduceIte]
    exact card_V q
  · simp only [ha, ↓reduceIte]
    have hex : ∃ i : Fin q, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    have hai : a i = 1 := by
      rcases zmod2_cases (a i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    let e : V q := Pi.single i (1 : ZMod 2)
    have hdot_e : dot a e = 1 := by
      unfold dot
      rw [Finset.sum_eq_single i]
      · simp [e, hai]
      · intro j _ hji
        simp [e, Pi.single_eq_of_ne hji]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have hchi_e : chi a e = -1 := by
      unfold chi
      rw [hdot_e]
      norm_num
    let eqv : V q ≃ V q :=
      { toFun := fun x => x + e
        invFun := fun x => x + e
        left_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero]
        right_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero] }
    have hsum : ∑ x : V q, chi a x = ∑ x : V q, chi a (x + e) :=
      (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : V q, chi a (x + e) = -(∑ x : V q, chi a x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_mul_right, hchi_e]
      ring
    linarith

private lemma sum_chi_mul {q : ℕ} (a b : V q) :
    ∑ x : V q, chi a x * chi b x = if a = b then (2 : ℚ) ^ q else 0 := by
  have h1 : ∑ x : V q, chi a x * chi b x = ∑ x : V q, chi (a + b) x :=
    Finset.sum_congr rfl fun x _ => chi_mul_left a b x
  rw [h1, sum_chi]
  simp only [v_add_eq_zero_iff]


private abbrev F := ZMod 2

private def local' {n} (D : Fin n → Finset (Fin n)) (T : Fin n → V n → F) :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

private def fill {n} (U : Finset (Fin n)) (b : V n) (z : U → F) (i : Fin n) : F :=
  if h : i∈U then z ⟨i,h⟩ else b i

private def obs {n m} (Q : Fin n → V m) (U : Finset (Fin n)) (T : Fin n → V n → F)
    (b : V n) (z : U → F) (r : Fin m) : F :=
  ∑ i, (fill U b z i + T i (fill U b z))*Q i r

private def uniform' {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) :=
  ∀ T, local' D T → ∀ b v, 2^m * Nat.card {z : U → F // obs Q U T b z = v}=2^U.card

private def pivot {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (a : V m) (j : Fin n) :=
  dot a (Q j)=1 ∧ ∀ i, j∈D i → dot a (Q i)=0

private def cond {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) :=
  ∀ a : V m, a≠0 → ∃ j∈U, pivot D Q a j

private lemma dot_swap {m} (a b : V m) : dot a b=dot b a := by simp [dot,mul_comm]

private lemma chi_swap {m} (a b : V m) : chi a b=chi b a := by simp [chi,dot_swap a b]

private lemma dot_obs {n m} (a : V m) (Q : Fin n → V m) (U : Finset (Fin n))
    (T : Fin n → V n → F) (b : V n) (z : U → F) :
    dot a (obs Q U T b z)=∑ i, (fill U b z i + T i (fill U b z))*dot a (Q i) := by
  simp only [dot,obs,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def unit {m : Nat} (r : Fin m) : V m := Pi.single r 1

private lemma dot_unit {m} (a : V m) (r) : dot a (unit r)=a r := by
  unfold dot
  rw [Finset.sum_eq_single r]
  · simp [unit]
  · intro i _ hi
    simp [unit,Pi.single_eq_of_ne hi]
  · simp

private lemma zero_or_one (x : F) : x=0 ∨ x=1 := zmod2_cases x
private lemma twice (x : F) : x+x=0 := by revert x; decide

private lemma fiberCount {A : Type} [Fintype A] {m : Nat} (f : A → V m)
    (hz : ∀ a : V m, a≠0 → ∑ x, chi a (f x)=0) (v : V m) :
    2^m*Nat.card {x : A // f x=v}=Fintype.card A := by
  classical
  have total : (∑ x, ∑ a, chi (f x) a * chi v a) = (Fintype.card A : ℚ) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single (0 : V m)]
    · simp [fun (x : V m) => (chi_swap x 0).trans (chi_zero x)]
    · intro a _ ha
      rw [← Finset.sum_mul]
      have hh : (∑ x, chi (f x) a)=0 := by
        simpa only [chi_swap a] using hz a ha
      simp [hh]
    · simp
  have sumh : (∑ x : A, if f x=v then (2:ℚ)^m else 0) = (Fintype.card A : ℚ) := by
    simpa only [sum_chi_mul] using total
  rw [← Finset.sum_filter] at sumh
  simp only [Finset.sum_const,nsmul_eq_mul] at sumh
  have cnt : Nat.card {x : A // f x=v} = (Finset.univ.filter (fun x => f x=v)).card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [cnt,mul_comm]
  exact_mod_cast sumh

private lemma cond_suffices {n m} {D : Fin n → Finset (Fin n)} {Q : Fin n → V m}
    {U : Finset (Fin n)} (h : cond D Q U) : uniform' D Q U := by
  classical
  intro T loc b v
  have balance (a : V m) (ha : a≠0) : (∑ z : U → F, chi a (obs Q U T b z))=0 := by
    obtain ⟨j,hj,own,quiet⟩ := h a ha
    let t : U := ⟨j,hj⟩
    let change : (U → F) → (U → F) := fun z i => if i=t then z i+1 else z i
    have cancel (c : F) : c+1+1=c := by revert c; decide
    let e : (U → F) ≃ (U → F) := ⟨change,change,
      fun z => by funext i; by_cases hi : i=t <;> simp [change,hi,cancel],
      fun z => by funext i; by_cases hi : i=t <;> simp [change,hi,cancel]⟩
    have raw (z : U → F) (i : Fin n) :
        fill U b (change z) i=fill U b z i+(if i=j then 1 else 0) := by
      by_cases eq : i=j
      · subst i; simp [fill,change,hj,t]
      · by_cases mem : i∈U
        · have dif : (⟨i,mem⟩ : U)≠t := fun hh => eq (congrArg Subtype.val hh)
          simp [fill,change,mem,eq,dif]
        · simp [fill,mem,eq]
    have moved (z : U → F) : dot a (obs Q U T b (change z))=dot a (obs Q U T b z)+1 := by
      rw [dot_obs,dot_obs]
      have term (i : Fin n) :
          (fill U b (change z) i+T i (fill U b (change z)))*dot a (Q i)=
          (fill U b z i+T i (fill U b z))*dot a (Q i)+(if i=j then 1 else 0) := by
        by_cases zero : dot a (Q i)=0
        · have ne : i≠j := fun e => by subst i; rw [own] at zero; exact one_ne_zero zero
          simp [zero,ne]
        · have same : T i (fill U b (change z))=T i (fill U b z) := by
            apply loc
            intro k hk
            have ne : k≠j := fun ee => by subst k; exact zero (quiet i hk)
            simp [raw,ne]
          rw [same,raw]
          by_cases eq : i=j
          · subst i; simp [own]; ring
          · simp [eq]
      simp_rw [term]
      rw [Finset.sum_add_distrib]
      simp
    have alt (z : U → F) : chi a (obs Q U T b (e z)) = -chi a (obs Q U T b z) := by
      change chi a (obs Q U T b (change z))=_
      unfold chi
      rw [moved]
      rcases zero_or_one (dot a (obs Q U T b z)) with hz | hz <;> simp [hz, twice]
    have total := e.sum_comp (fun z => chi a (obs Q U T b z))
    simp only [alt, Finset.sum_neg_distrib] at total
    linarith
  simpa [Fintype.card_fun,ZMod.card,F] using fiberCount (obs Q U T b) balance v

private lemma uniform_needs {n m} {D : Fin n → Finset (Fin n)} {Q : Fin n → V m}
    {U : Finset (Fin n)} (h : uniform' D Q U) : cond D Q U := by
  classical
  intro a ha
  by_contra lack
  let K := U.filter fun j => dot a (Q j)=1
  have get (j : Fin n) (hj : j∈K) : ∃ i, j∈D i ∧ dot a (Q i)=1 := by
    by_contra! bad
    obtain ⟨mem,one⟩ := Finset.mem_filter.mp hj
    apply lack
    refine ⟨j,mem,one,?_⟩
    intro i hi
    exact (zero_or_one _).resolve_right (bad i hi)
  let owner (j : Fin n) := if hj : j∈K then Classical.choose (get j hj) else j
  have ow (j : Fin n) (hj : j∈K) : j∈D (owner j) ∧ dot a (Q (owner j))=1 := by
    simpa [owner,hj] using Classical.choose_spec (get j hj)
  let T (i : Fin n) (x : V n) : F := ∑ j∈K, if owner j=i then x j else 0
  have loc : local' D T := by
    intro i x y eq
    apply Finset.sum_congr rfl
    intro j mem
    by_cases e : owner j=i
    · subst i; simp [eq j (ow j mem).1]
    · simp [e]
  have cancel (z : U → F) : dot a (obs Q U T 0 z)=0 := by
    rw [dot_obs]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    let x := fill U (0 : V n) z
    have raw : (∑ i, x i * dot a (Q i))=∑ i∈K, x i := by
      rw [show K=Finset.univ.filter (fun j => j∈U ∧ dot a (Q j)=1) by ext j; simp [K]]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈U
      · rcases zero_or_one (dot a (Q i)) with eq | eq <;> simp [eq,hi]
      · simp [x,fill,hi]
    have rules : (∑ i, T i x*dot a (Q i))=∑ i∈K,x i := by
      unfold T
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp [ite_mul,(ow j hj).2]
    change (∑ i,x i*dot a (Q i))+(∑ i,T i x*dot a (Q i))=0
    rw [raw,rules,twice]
  obtain ⟨r,hr⟩ : ∃ r,a r≠0 := by
    by_contra! allzero
    exact ha (funext allzero)
  let v := unit r
  have hcnt := h T loc 0 v
  have empty : IsEmpty {z : U → F // obs Q U T 0 z=v} := ⟨by
    rintro ⟨z,hz⟩
    have eq := cancel z
    rw [hz,dot_unit] at eq
    exact hr eq⟩
  have no : Nat.card {z : U → F // obs Q U T 0 z=v}=0 := by
    letI := empty
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero
  rw [no,Nat.mul_zero] at hcnt
  exact (Nat.ne_of_gt (Nat.two_pow_pos U.card)) hcnt.symm

private lemma pivotEquiv {n m} {D : Fin n → Finset (Fin n)} {Q : Fin n → V m}
    (U : Finset (Fin n)) : uniform' D Q U ↔ cond D Q U := ⟨uniform_needs,cond_suffices⟩

private abbrev NZ (m : Nat) := {a : V m // a≠0}

private lemma nzCard (m : Nat) : Fintype.card (NZ m) = 2^m-1 := by
  classical
  change Fintype.card {a : V m // ¬ a=0}=_
  rw [Fintype.card_subtype_compl]
  simp [V,ZMod.card]

private def readSet {n} (D : Fin n → Finset (Fin n)) (j : Fin n) :=
  Finset.univ.filter fun i => j∈D i

private lemma totalReads {n} (D : Fin n → Finset (Fin n)) :
    (∑ j,(readSet D j).card)=∑ i,(D i).card := by
  classical
  simp_rw [readSet,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp

private lemma countLower {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m)
    (W : Finset (Fin n)) (card : W.card=2^m-1) (all : cond D Q Finset.univ)
    (minimal : ∀ j∈W, ¬cond D Q (Finset.univ.erase j)) :
    2^m-1 ≤ n ∧ (∀ j∈W,m-1 ≤ (readSet D j).card) ∧
      (2^m-1)*(m-1) ≤ ∑ i,(D i).card := by
  classical
  have privateMask (j : W) : ∃ a : NZ m, pivot D Q a j ∧ ∀ i, pivot D Q a i → i=j := by
    have bad := minimal j j.property
    unfold cond at bad
    push_neg at bad
    obtain ⟨a,non,miss⟩ := bad
    obtain ⟨i,_,hp⟩ := all a non
    have only (k : Fin n) (ok : pivot D Q a k) : k=j := by
      by_contra diff
      exact miss k (Finset.mem_erase.mpr ⟨diff,Finset.mem_univ _⟩) ok
    exact ⟨⟨a,non⟩,only i hp ▸ hp,only⟩
  choose f existsPivot uniquePivot using privateMask
  have inj : Function.Injective f := by
    intro j k eq
    apply Subtype.ext
    exact uniquePivot k j (eq ▸ existsPivot j)
  have onto : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simpa [nzCard] using card⟩).2
  have oneAt (j : W) (a : V m) (hp : pivot D Q a j) : a=(f j).val := by
    have non : a≠0 := by
      intro zero
      have := hp.1
      rw [zero,dot_zero_left] at this
      exact zero_ne_one this
    obtain ⟨k,hk⟩ := onto ⟨a,non⟩
    have eq : (f k).val=a := congrArg Subtype.val hk
    have jk : j=k := Subtype.ext (uniquePivot k j (eq ▸ hp))
    simpa [jk] using eq.symm
  have quantity (j : W) : m-1 ≤ (readSet D j.val).card := by
    let R := readSet D j.val
    let code (w : V m) : F × (R → F) := (dot w (Q j), fun i => dot w (Q i.val))
    have mono : Function.Injective code := by
      intro a b same
      have o : dot a (Q j)=dot b (Q j) := congrArg Prod.fst same
      have eq (i : R) : dot a (Q i)=dot b (Q i) := congrFun (congrArg Prod.snd same) i
      have hp := existsPivot j
      have fixed : pivot D Q ((f j).val+(a+b)) j := by
        constructor
        · rw [dot_add_left,dot_add_left,o,twice,hp.1,add_zero]
        · intro i hi
          have mem : i∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
          rw [dot_add_left,dot_add_left,eq ⟨i,mem⟩,twice,hp.2 i hi,add_zero]
      have hsame := oneAt j _ fixed
      have vanish : a+b=0 := add_left_cancel (show (f j).val+(a+b)=(f j).val+0 by simpa using hsame)
      exact (v_add_eq_zero_iff a b).mp vanish
    have hcap := Fintype.card_le_of_injective code mono
    have pp : 2^m ≤ 2^(R.card+1) := by simpa [V,F,ZMod.card,pow_succ,mul_comm] using hcap
    by_contra! low
    have e : R.card+1 < m := by change m-1 > R.card at low; omega
    exact (Nat.not_lt_of_ge pp) (Nat.pow_lt_pow_right (by decide : 1 < 2) e)
  refine ⟨?_,fun j hj => quantity ⟨j,hj⟩,?_⟩
  · have sz := Finset.card_le_card (Finset.subset_univ W)
    simpa [card] using sz
  · rw [← totalReads,←card]
    calc
      W.card*(m-1) = ∑ _j∈W,(m-1) := by simp
      _ ≤ ∑ j∈W,(readSet D j).card := Finset.sum_le_sum (fun j mem => quantity ⟨j,mem⟩)
      _ ≤ ∑ j,(readSet D j).card := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

private def ones {m : Nat} (a : V m) := Finset.univ.filter fun r => a r=1

private lemma onesNon {m} (a : NZ m) : (ones a.val).Nonempty := by
  classical
  by_contra empty
  apply a.property
  funext r
  exact (zero_or_one (a.val r)).resolve_right (fun h => empty ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

private noncomputable def low {m} (a : NZ m) := (ones a.val).min' (onesNon a)
private noncomputable def high {m} (a : NZ m) := (ones a.val).max' (onesNon a)

private noncomputable def col {m} (a : NZ m) : V m :=
  if h : (high a).val+1 < m then unit (low a)+unit ⟨(high a).val+1,h⟩ else unit (low a)

private lemma oddCol {m} (a : NZ m) : dot a.val (col a)=1 := by
  classical
  have hl : a.val (low a)=1 :=
    (Finset.mem_filter.mp (Finset.min'_mem (ones a.val) (onesNon a))).2
  unfold col
  split_ifs with h
  · let s : Fin m := ⟨(high a).val+1,h⟩
    have hs : a.val s=0 := by
      apply (zero_or_one _).resolve_right
      intro one
      have mem : s∈ones a.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,one⟩
      have hle : s ≤ high a := Finset.le_max' _ _ mem
      change (high a).val+1 ≤ (high a).val at hle
      omega
    change dot a.val (unit (low a)+unit s)=1
    rw [dot_add_right,dot_unit,dot_unit,hl,hs,add_zero]
  · rw [dot_unit,hl]

private lemma supportTwo {m} (a : NZ m) : (Finset.univ.filter (fun r => col a r≠0)).card ≤ 2 := by
  classical
  unfold col
  split_ifs with h
  · let s : Fin m := ⟨(high a).val+1,h⟩
    have bound : ({low a,s} : Finset (Fin m)).card ≤ 2 := by
      simpa using (Finset.card_insert_le (low a) ({s} : Finset (Fin m)))
    apply (Finset.card_le_card (t:=({low a,s} : Finset (Fin m))) ?_).trans bound
    intro r hr
    by_contra bad
    simp only [Finset.mem_insert,Finset.mem_singleton] at bad
    have l : r≠low a := fun q => bad (.inl q)
    have u : r≠s := fun q => bad (.inr q)
    exact (Finset.mem_filter.mp hr).2 (by change unit (low a) r+unit s r=0; simp [unit,Pi.single_eq_of_ne l,Pi.single_eq_of_ne u])
  · have sub : Finset.univ.filter (fun r => unit (low a) r ≠ 0) ⊆ {low a} := by
      intro r hr
      by_contra e
      have ne : r≠low a := fun q => e (Finset.mem_singleton.mpr q)
      exact (Finset.mem_filter.mp hr).2 (by simp [unit,Pi.single_eq_of_ne ne])
    exact (Finset.card_le_card sub).trans (by simp)

private noncomputable def intervalSite {m} (l r : Fin m) (le : l ≤ r) : NZ m :=
  ⟨fun i => if l ≤ i ∧ i ≤ r then 1 else 0,by
    intro eq
    have h := congrFun eq l
    simpa [le] using h⟩

private lemma intervalMem {m} (l r : Fin m) (le : l ≤ r) (x : Fin m) :
    x∈ones (intervalSite l r le).val ↔ l ≤ x ∧ x ≤ r := by
  simp [ones,intervalSite]

private lemma loInterval {m} (l r : Fin m) (le : l ≤ r) : low (intervalSite l r le)=l := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((intervalMem l r le l).mpr ⟨le_rfl,le⟩)
  · exact ((intervalMem l r le _).mp (Finset.min'_mem _ _)).1

private lemma hiInterval {m} (l r : Fin m) (le : l ≤ r) : high (intervalSite l r le)=r := by
  apply le_antisymm
  · exact ((intervalMem l r le _).mp (Finset.max'_mem _ _)).2
  · exact Finset.le_max' _ _ ((intervalMem l r le r).mpr ⟨le,le_rfl⟩)

private lemma stockOne {m} (i : Fin m) : ∃ a : NZ m,col a=unit i := by
  let z : Fin m := ⟨m-1,by have := i.isLt; omega⟩
  have le : i ≤ z := by change i.val ≤ m-1; have := i.isLt; omega
  refine ⟨intervalSite i z le,?_⟩
  have last : ¬ z.val+1 < m := by dsimp [z]; have := i.isLt; omega
  simp [col,loInterval,hiInterval,last]

private lemma stockPairLt {m} (i j : Fin m) (ij : i < j) : ∃ a : NZ m,col a=unit i+unit j := by
  let z : Fin m := ⟨j.val-1,by have := j.isLt; omega⟩
  have le : i ≤ z := by change i.val ≤ j.val-1; change i.val < j.val at ij; omega
  refine ⟨intervalSite i z le,?_⟩
  have next : z.val+1=j.val := by change j.val-1+1=j.val; change i.val < j.val at ij; omega
  simp [col,loInterval,hiInterval,next]

private lemma stockPair {m} (i j : Fin m) (ij : i≠j) : ∃ a : NZ m,col a=unit i+unit j := by
  rcases lt_or_gt_of_ne ij with lt | gt
  · exact stockPairLt i j lt
  · simpa only [add_comm (unit i) (unit j)] using stockPairLt j i gt

private def basisCol {m} (a : V m) (p r : Fin m) : V m :=
  if a r=0 then unit r else unit r+unit p

private lemma basisDot {m} (a z : V m) (p r : Fin m) :
    dot z (basisCol a p r)=if a r=0 then z r else z r+z p := by
  unfold basisCol
  split_ifs <;> simp only [dot_add_right,dot_unit]

private lemma basisVal {m} (a : V m) (p r s : Fin m) (hs : s≠p) :
    basisCol a p r s=if s=r then 1 else 0 := by
  unfold basisCol
  by_cases eq : s=r
  · subst s
    by_cases h : a r=0 <;> simp [h,unit,Pi.single_eq_of_ne hs]
  · by_cases h : a r=0 <;> simp [h,eq,unit,Pi.single_eq_of_ne eq,Pi.single_eq_of_ne hs]

private lemma design (m : Nat) :
    let N := 2^m-1
    ∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → V m),
      (∀ i,i∉D i) ∧ (∀ i,(Finset.univ.filter (fun r => Q i r≠0)).card ≤ 2) ∧
      (∀ j,(readSet D j).card=m-1) ∧ (∑ i,(D i).card)=N*(m-1) ∧
      (∀ U,cond D Q U ↔ U=Finset.univ) := by
  classical
  dsimp only
  let I := Fin (2^m-1)
  let e : I ≃ NZ m := (Fintype.equivFinOfCardEq (nzCard m)).symm
  let A (j : I) : V m := (e j).val
  let Q (j : I) := col (e j)
  let p (j : I) := low (e j)
  let R (j : I) := {r : Fin m // r≠p j}
  have one (j : I) : A j (p j)=1 :=
    (Finset.mem_filter.mp (Finset.min'_mem (ones (A j)) (onesNon (e j)))).2
  have findReader (j : I) (r : R j) : ∃ i : I, Q i=basisCol (A j) (p j) r := by
    have pick : ∃ a : NZ m,col a=basisCol (A j) (p j) r := by
      by_cases h : A j r=0
      · simpa only [basisCol,h,if_true] using stockOne r.val
      · simpa only [basisCol,h,if_false] using stockPair r.val (p j) r.property
    obtain ⟨v,hv⟩ := pick
    exact ⟨e.symm v,by simpa [Q] using hv⟩
  choose idx spec using findReader
  have inject (j : I) : Function.Injective (idx j) := by
    intro r s eq
    apply Subtype.ext
    by_contra ne
    have he : basisCol (A j) (p j) r=basisCol (A j) (p j) s :=
      (spec j r).symm.trans ((congrArg Q eq).trans (spec j s))
    have bad := congrFun he r.val
    rw [basisVal _ _ _ _ r.property,basisVal _ _ _ _ r.property,if_pos rfl,if_neg ne] at bad
    exact one_ne_zero bad
  let D (i : I) : Finset I := Finset.univ.filter fun j => ∃ r : R j,idx j r=i
  have wire {i j : I} : j∈D i ↔ ∃ r : R j,idx j r=i := by simp [D]
  have own (j : I) : dot (A j) (Q j)=1 := oddCol (e j)
  have quiet (j : I) (r : R j) : dot (A j) (Q (idx j r))=0 := by
    rw [spec,basisDot,one]
    rcases zero_or_one (A j r) with h | h <;> simp [h,twice]
  have yes (j : I) : pivot D Q (A j) j := by
    refine ⟨own j,?_⟩
    intro i hi
    obtain ⟨r,rfl⟩ := wire.mp hi
    exact quiet j r
  have unique (z : V m) (j : I) (hp : pivot D Q z j) : z=A j := by
    have scalar (r : Fin m) : z r=z (p j)*A j r := by
      by_cases hr : r=p j
      · subst r; simp [one]
      · let u : R j := ⟨r,hr⟩
        have val := hp.2 (idx j u) (wire.mpr ⟨u,rfl⟩)
        rw [spec,basisDot] at val
        have bit : ∀ s c b : F, (if s=0 then c else c+b)=0 → c=b*s := by decide
        exact bit _ _ _ val
    have zp : z (p j)=1 := by
      apply (zero_or_one _).resolve_left
      intro h
      have zv : z=0 := funext (fun i => by simpa [h] using scalar i)
      have must := hp.1
      rw [zv,dot_zero_left] at must
      exact zero_ne_one must
    exact funext (fun i => by simpa [zp] using scalar i)
  have rcount (j : I) : (readSet D j).card=m-1 := by
    have eq : readSet D j=Finset.univ.image (idx j) := by
      ext i
      simp only [readSet,Finset.mem_filter,Finset.mem_univ,true_and,wire,Finset.mem_image]
    rw [eq,Finset.card_image_of_injective _ (inject j),Finset.card_univ]
    change Fintype.card {r : Fin m // ¬r=p j}=m-1
    rw [Fintype.card_subtype_compl]
    simp
  refine ⟨D,Q,?_,fun i => supportTwo (e i),rcount,?_,?_⟩
  · intro i hi
    obtain ⟨r,eq⟩ := wire.mp hi
    have bad := quiet i r
    rw [eq,own] at bad
    exact one_ne_zero bad
  · rw [← totalReads]
    simp [rcount,I]
  · intro U
    constructor
    · intro hf
      apply Finset.eq_univ_of_forall
      intro j
      obtain ⟨k,mem,ok⟩ := hf (A j) (e j).property
      have eq := unique (A j) k ok
      have jk : j=k := e.injective (Subtype.ext eq)
      simpa only [jk] using mem
    · rintro rfl a nzero
      let k := e.symm ⟨a,nzero⟩
      have eq : A k=a := congrArg Subtype.val (e.apply_symm_apply ⟨a,nzero⟩)
      exact ⟨k,Finset.mem_univ _,eq ▸ yes k⟩

end ProofBody
end PEqualNP.Outside.L_lib_1095

open PEqualNP.Outside.L_lib_1095 in
theorem PEqualNP.Outside.L_lib_1095 : let Word := fun k : Nat => Fin k → ZMod 2
let localRule := fun (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) =>
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
let observed := fun (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) =>
  let x := fun i : Fin n => if h : i ∈ U then z ⟨i,h⟩ else b i
  ∑ i, (x i + T i x) * Q i r
let uniform := fun (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) =>
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card
let readers := fun (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) =>
  (Finset.univ.filter (fun i => j ∈ D i)).card
let wires := fun (n : Nat) (D : Fin n → Finset (Fin n)) => ∑ i, (D i).card
∀ m : Nat, 1 ≤ m →
  let N := 2^m - 1
  (∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → Word m),
    (∀ i, i ∉ D i) ∧
    (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, readers N D j = m-1) ∧ wires N D = N*(m-1) ∧
    (∀ U, uniform N m D Q U ↔ U = Finset.univ)) ∧
  (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (W : Finset (Fin n)),
    W.card = N → uniform n m D Q Finset.univ →
    (∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) →
    N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D) := by
  change ∀ m : Nat, 1 ≤ m →
    (∃ (D : Fin (2^m-1) → Finset (Fin (2^m-1))) (Q : Fin (2^m-1) → V m),
      (∀ i,i∉D i) ∧ (∀ i,(Finset.univ.filter (fun r => Q i r≠0)).card≤2) ∧
      (∀ j,(readSet D j).card=m-1) ∧ (∑ i,(D i).card)=(2^m-1)*(m-1) ∧
      (∀ U,uniform' D Q U ↔ U=Finset.univ)) ∧
    (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (W : Finset (Fin n)),
      W.card=2^m-1 → uniform' D Q Finset.univ →
      (∀ j∈W,¬uniform' D Q (Finset.univ.erase j)) →
      2^m-1≤n ∧ (∀ j∈W,m-1≤(readSet D j).card) ∧ (2^m-1)*(m-1)≤∑ i,(D i).card)
  intro m _
  constructor
  · obtain ⟨D,Q,a,b,c,d,h⟩ := design m
    exact ⟨D,Q,a,b,c,d,fun U => (pivotEquiv U).trans (h U)⟩
  · intro n D Q W card all minimal
    exact countLower D Q W card (uniform_needs all)
      (fun j hj ok => minimal j hj (cond_suffices ok))
