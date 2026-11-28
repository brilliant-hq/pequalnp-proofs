import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1165

abbrev Mask (r : Nat) := Finset (Fin r)
abbrev Fam (r : Nat) := Finset (Mask r)

def push {r : Nat} (t : Bool) (S : Mask r) : Mask (r+1) :=
  if t then insert 0 (S.map (Fin.succEmb r)) else S.map (Fin.succEmb r)

lemma mZero {r} (t : Bool) (S : Mask r) : 0 ∈ push t S ↔ t = true := by
  cases t <;> simp [push, Finset.mem_map, Fin.succEmb]

lemma mSucc {r} (t : Bool) (S : Mask r) (j : Fin r) : j.succ ∈ push t S ↔ j ∈ S := by
  cases t <;> simp [push, Finset.mem_map, Fin.succEmb]

lemma push_inj {r} (t : Bool) : Function.Injective (@push r t) := by
  intro A B h
  ext j
  simpa only [mSucc] using (show j.succ ∈ push t A ↔ j.succ ∈ push t B by rw [h])

lemma push_ne {r} (A B : Mask r) : push false A ≠ push true B := by
  intro h; have h0 := (mZero true B).2 rfl; rw [← h, mZero] at h0; cases h0

lemma push_surj {r} (A : Mask (r+1)) : ∃ t S, push t S = A := by
  refine ⟨decide (0 ∈ A), Finset.univ.filter (fun j : Fin r => j.succ ∈ A), ?_⟩
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [mZero]
  · simp [mSucc]

def join {r} (L U : Fam r) : Fam (r+1) := L.image (push false) ∪ U.image (push true)

def sec {r} (t : Bool) (M : Fam (r+1)) : Fam r := Finset.univ.filter (fun S => push t S ∈ M)

lemma joinDisj {r} (L U : Fam r) : Disjoint (L.image (push false)) (U.image (push true)) := by
  rw [Finset.disjoint_left]; intro z hz h'z
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨B, _, hB⟩ := Finset.mem_image.mp h'z
  exact push_ne A B hB.symm

lemma memJoin {r} (L U : Fam r) (t : Bool) (S : Mask r) :
    push t S ∈ join L U ↔ S ∈ (if t then U else L) := by
  cases t <;> simp [join, Finset.mem_image, (push_inj _).eq_iff, push_ne, Ne.symm (push_ne _ _)]

lemma joinSec {r} (M : Fam (r+1)) : join (sec false M) (sec true M) = M := by
  ext A; obtain ⟨t,S,rfl⟩ := push_surj A
  cases t <;> simp [memJoin, sec]

lemma cardJoin {r} (L U : Fam r) : (join L U).card = L.card + U.card := by
  simp [join, Finset.card_union_of_disjoint (joinDisj L U), Finset.card_image_of_injective, push_inj]

def idx {r} (S : Mask r) := S.sum (fun j => 2^j.val)

lemma idxPush {r} (t : Bool) (S : Mask r) : idx (push t S) = 2*idx S + (if t then 1 else 0) := by
  have h0 : (0 : Fin (r+1)) ∉ S.map (Fin.succEmb r) := by simp [Finset.mem_map, Fin.succEmb]
  cases t <;> simp [idx, push, h0, Finset.sum_map, Fin.succEmb, pow_succ, Finset.sum_mul, Finset.mul_sum, Nat.mul_comm, Nat.add_comm]

lemma idx_lt {r} (S : Mask r) : idx S < 2^r := by
  induction r with
  | zero => have h : S = ∅ := by ext j; exact j.elim0
            simp [h, idx]
  | succ r ih => obtain ⟨t,S,rfl⟩ := push_surj S; specialize ih S
                 cases t <;> simp [idxPush, pow_succ] <;> omega

lemma idx_inj {r} : Function.Injective (@idx r) := by
  induction r with
  | zero => intro A B h; ext j; exact j.elim0
  | succ r ih =>
    intro A B h; obtain ⟨t,S,rfl⟩ := push_surj A; obtain ⟨u,T,rfl⟩ := push_surj B
    cases t <;> cases u <;> simp [idxPush] at h <;> first | exact congrArg _ (ih (by omega)) | omega

def weight (a d : Nat) {r} (S : Mask r) := a ^ S.card * d ^ (r-S.card)
def cost (a d : Nat) {r} (M : Fam r) := M.sum (weight a d)

lemma weightPush (a d : Nat) {r} (t : Bool) (S : Mask r) :
    weight a d (push t S) = (if t then a else d) * weight a d S := by
  have hs : S.card ≤ r := by simpa using S.card_le_univ
  have h0 : (0 : Fin (r+1)) ∉ S.map (Fin.succEmb r) := by simp [Finset.mem_map, Fin.succEmb]
  cases t <;> simp [weight, push, h0, show r+1-S.card=r-S.card+1 by omega, pow_succ] <;> ring

lemma costJoin (a d : Nat) {r} (L U : Fam r) :
    cost a d (join L U) = d*cost a d L + a*cost a d U := by
  simp [cost, join, Finset.sum_union (joinDisj L U), Finset.sum_image (push_inj _).injOn, weightPush, Finset.mul_sum]

lemma swapCost {A D X Y : Nat} (h : A ≤ D) (h' : X ≤ Y) :
    D * X + A * Y ≤ D * Y + A * X := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
  nlinarith

def W (a d : Nat) : Nat → Nat → Nat
  | 0, k => k
  | r+1, k => d * W a d r ((k+1)/2) + a * W a d r (k/2)

lemma W_mono (a d r : Nat) : Monotone (W a d r) := by
  induction r with
  | zero => exact fun _ _ h => h
  | succ r ih =>
    intro x y h
    simp only [W]
    exact Nat.add_le_add (Nat.mul_le_mul_left d (ih (by omega))) (Nat.mul_le_mul_left a (ih (by omega)))

lemma W_even (a d r i : Nat) : W a d (r+1) (2*i) = (d+a) * W a d r i := by
  rw [W, show (2*i+1)/2=i by omega, show 2*i/2=i by omega, Nat.add_mul]

lemma W_odd (a d r i : Nat) : W a d (r+1) (2*i+1) = d * W a d r (i+1) + a * W a d r i := by
  rw [W, show (2*i+1+1)/2=i+1 by omega, show (2*i+1)/2=i by omega]

lemma W_split (a d : Nat) (had : a ≤ d) (r u v : Nat) (hvu : v ≤ u) :
    W a d (r+1) (u+v) ≤ d * W a d r u + a * W a d r v := by
  induction r generalizing u v with
  | zero =>
    simp only [W]
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show (u+v+1)/2 ≤ u by omega)
    have he : (u+v)/2 = v+t := by omega
    calc
      _ = d * ((u+v+1)/2) + a*v + a*t := by rw [he]; ring
      _ ≤ d * ((u+v+1)/2) + a*v + d*t := by gcongr
      _ = d * (((u+v+1)/2)+t) + a*v := by ring
      _ = d * u + a*v := by rw [←ht]
  | succ r ih =>
    by_cases huv : u = v
    · subst v; rw [show u+u=2*u by omega, W_even, Nat.add_mul]
    let i := u/2
    let j := v/2
    have hij : j ≤ i := by dsimp [i,j]; omega
    rcases (show u = 2*i ∨ u = 2*i+1 by dsimp [i]; omega) with hu|hu <;>
      rcases (show v = 2*j ∨ v = 2*j+1 by dsimp [j]; omega) with hv|hv
    · rw [show u+v=2*(i+j) by omega, hu, hv, W_even, W_even, W_even]
      calc
        _ ≤ (d+a)*(d * W a d r i + a * W a d r j) := Nat.mul_le_mul_left _ (ih i j hij)
        _ = _ := by ring
    · have hji : j+1 ≤ i := by omega
      rw [show u+v=2*(i+j)+1 by omega, hu, hv, W_odd, W_even, W_odd]
      calc
        _ ≤ d * (d * W a d r i + a * W a d r (j+1)) + a * (d * W a d r i + a * W a d r j) := by
          apply Nat.add_le_add _ (Nat.mul_le_mul_left _ (ih i j hij))
          exact Nat.mul_le_mul_left _ (by simpa only [Nat.add_assoc] using ih i (j+1) hji)
        _ = _ := by ring
    · rw [show u+v=2*(i+j)+1 by omega, hu, hv, W_odd, W_odd, W_even]
      calc
        _ ≤ d * (d * W a d r (i+1) + a * W a d r j) + a * (d * W a d r i + a * W a d r j) := by
          apply Nat.add_le_add _ (Nat.mul_le_mul_left _ (ih i j hij))
          exact Nat.mul_le_mul_left _ (by simpa only [Nat.add_right_comm] using ih (i+1) j (by omega))
        _ = _ := by ring
    · have hji : j+1 ≤ i := by omega
      rw [show u+v=2*(i+j+1) by omega, hu, hv, W_even, W_odd, W_odd, Nat.add_mul]
      calc
        _ ≤ d * (d * W a d r (i+1) + a * W a d r j) + a * (d * W a d r i + a * W a d r (j+1)) := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ (by simpa only [Nat.add_right_comm] using ih (i+1) j (by omega))
          · exact Nat.mul_le_mul_left _ (by simpa only [Nat.add_assoc] using ih i (j+1) hji)
        _ = d*d*W a d r (i+1) + a*d*W a d r i + a*(d*W a d r j+a*W a d r (j+1)) := by ring
        _ ≤ d*d*W a d r (i+1) + a*d*W a d r i + a*(d*W a d r (j+1)+a*W a d r j) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left a (swapCost had (W_mono a d r (Nat.le_succ j)))) _
        _ = _ := by ring

open scoped Classical

def cell (a b q : Nat) (z : Prop) : Prop := if q<a then z else if q<a+b then ¬z else True

def hit (a b : Nat) {r n} (M : Fam r) (x : Fin r → Fin n) : Prop :=
  ∃ S ∈ M, ∀ j, cell a b (x j).val (j ∈ S)

noncomputable def see (a b c : Nat) {r} (M : Fam r) : Nat :=
  ∑ x : Fin r → Fin (a+b+c), if hit a b M x then 1 else 0

lemma hitJoin (a b : Nat) {r n} (L U : Fam r) (q : Fin n) (x : Fin r → Fin n) :
    hit a b (join L U) (Fin.cons q x) ↔
      if q.val<a then hit a b U x else if q.val<a+b then hit a b L x else hit a b (L∪U) x := by
  have h : hit a b (join L U) (Fin.cons q x) ↔
      ∃ t : Bool, ∃ S ∈ (if t then U else L), cell a b q.val (t=true) ∧ ∀ j, cell a b (x j).val (j∈S) := by
    constructor
    · rintro ⟨A,hA,h⟩; obtain ⟨t,S,rfl⟩ := push_surj A
      exact ⟨t,S,(memJoin L U t S).mp hA, by simpa only [Fin.cons_zero,mZero] using h 0,
        fun j => by simpa only [Fin.cons_succ,mSucc] using h j.succ⟩
    · rintro ⟨t,S,hS,h0,hs⟩
      refine ⟨push t S, (memJoin L U t S).mpr hS, ?_⟩
      rw [Fin.forall_fin_succ]; simpa only [Fin.cons_zero,Fin.cons_succ,mZero,mSucc] using And.intro h0 hs
  rw [h]; by_cases h1 : q.val < a
  · simp [h1, cell, hit, Bool.exists_bool]
  · by_cases h2 : q.val < a+b
    · simp [h1, h2, cell, hit, Bool.exists_bool]
    · simp [h1,h2,cell,hit,Bool.exists_bool,Finset.mem_union,or_and_right,exists_or]

lemma sumHead (a b c A B C : Nat) :
    (∑ q : Fin (a+b+c), if q.val<a then A else if q.val<a+b then B else C) = a*A+b*B+c*C := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add (a:=a) (b:=b)]
  calc
    _ = ((∑ _ : Fin a, A) + ∑ _ : Fin b, B) + ∑ _ : Fin c, C := by
      apply congrArg₂ (·+·)
      · apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro i hi
        · simp [Fin.val_castAdd, i.isLt]
        · simp [Fin.val_castAdd, Fin.val_natAdd, i.isLt]
      · apply Finset.sum_congr rfl; intro i hi
        simp [Fin.val_natAdd, show ¬a+b+i.val<a by omega]
    _ = _ := by simp

lemma seeJoin (a b c : Nat) {r} (L U : Fam r) :
    see a b c (join L U) = a * see a b c U + b * see a b c L + c * see a b c (L∪U) := by
  unfold see
  rw [← (Fin.consEquiv (fun _ : Fin (r+1) => Fin (a+b+c))).sum_comp, Fintype.sum_prod_type]
  refine Eq.trans ?_ (sumHead a b c _ _ _)
  apply Finset.sum_congr rfl; intro q hq
  change (∑ x : Fin r → Fin (a+b+c), if hit a b (join L U) (Fin.cons q x) then 1 else 0) = _
  by_cases ha : q.val<a <;> by_cases hb : q.val<a+b <;> simp only [hitJoin, ha, hb, ite_true, ite_false]

lemma seeZero (a b c : Nat) (M : Fam 0) : see a b c M = M.card := by
  have h : ∀ x : Fin 0 → Fin (a+b+c), hit a b M x ↔ M.Nonempty := by simp [hit,Finset.Nonempty]
  by_cases hm : M.Nonempty
  · have hl := M.card_le_univ; have hp := Finset.card_pos.mpr hm
    have he : M.card=1 := by simp [Fam,Mask] at hl; omega
    simp [see,h,hm,he]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hm
    simp [he,see,hit]

lemma costZero (a d : Nat) (M : Fam 0) : cost a d M = M.card := by
  have h (S : Mask 0) : S.card=0 := by simpa using S.card_le_univ
  change (∑ S ∈ M, weight a d S) = M.card
  simp [weight,h]

def Down {r} (M : Fam r) := ∀ S ∈ M, ∀ T ⊆ S, T ∈ M

lemma sec_down {r} {M : Fam (r+1)} (hm : Down M) (t : Bool) : Down (sec t M) := by
  intro S hs T hT; simp only [sec,Finset.mem_filter,Finset.mem_univ,true_and] at hs ⊢
  apply hm _ hs; cases t <;> simp only [push,Bool.false_eq_true,ite_false,ite_true]
  · exact Finset.map_subset_map.mpr hT
  · exact Finset.insert_subset_insert _ (Finset.map_subset_map.mpr hT)

lemma seeDown (a b c : Nat) {r} {M : Fam r} (hm : Down M) : see a b c M = cost a (b+c) M := by
  induction r with
  | zero => rw [seeZero, costZero]
  | succ r ih =>
    let L := sec false M; let U := sec true M
    have hUL : U ⊆ L := by
      intro S hS; simp only [U,L,sec,Finset.mem_filter,Finset.mem_univ,true_and] at hS ⊢
      apply hm _ hS; exact Finset.subset_insert _ _
    have he : join L U = M := joinSec M
    rw [←he,seeJoin,costJoin,Finset.union_eq_left.mpr hUL,
      ih (sec_down hm true), ih (sec_down hm false)]; ring

lemma cap {r} (M : Fam r) : M.card ≤ 2^r := by simpa [Mask] using M.card_le_univ

def key {r} (S : Mask r) : Nat := S.card * 2^r + idx S

def predKey {r} (A B : Mask r) : Prop := A.card < B.card ∨ (A.card = B.card ∧ idx A < idx B)

lemma key_lt {r} (A B : Mask r) : key A < key B ↔ predKey A B := by
  have ha := idx_lt A; have hb := idx_lt B
  have hp : 0 < 2^r := Nat.two_pow_pos r
  unfold key predKey
  rcases lt_trichotomy A.card B.card with h|h|h
  · have hh := Nat.mul_le_mul_right (2^r) (show A.card+1≤B.card by omega); rw [Nat.add_mul,one_mul] at hh
    omega
  · rw [h]; omega
  · have hh := Nat.mul_le_mul_right (2^r) (show B.card+1≤A.card by omega); rw [Nat.add_mul,one_mul] at hh
    omega

lemma key_inj {r} : Function.Injective (@key r) := by
  intro A B he
  have ha : ¬predKey A B := fun h => ((key_lt A B).mpr h).ne he
  have hb : ¬predKey B A := fun h => ((key_lt B A).mpr h).ne he.symm
  unfold predKey at ha hb; apply idx_inj; omega

def rank {r} (S : Mask r) := (Finset.univ.filter (fun T : Mask r => T.card < S.card ∨ (T.card = S.card ∧ idx T < idx S))).card

lemma rank_eq {r} (S : Mask r) : rank S = (Finset.univ.filter (fun T : Mask r => key T < key S)).card := by
  simp only [rank,key_lt,predKey]

lemma rank_mono {r} {A B : Mask r} (h : key A < key B) : rank A < rank B := by
  rw [rank_eq,rank_eq]; apply Finset.card_lt_card
  have hsub : (Finset.univ.filter fun T : Mask r => key T < key A) ⊆ (Finset.univ.filter fun T : Mask r => key T < key B) := by
    intro T ht; simpa using (lt_trans (by simpa using ht) h : key T < key B)
  exact (Finset.ssubset_iff_of_subset hsub).mpr ⟨A,by simpa,by simp⟩

lemma rank_lt {r} (S : Mask r) : rank S < 2^r := by
  rw [rank_eq]; have h := Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset (fun T : Mask r => key T < key S) Finset.univ)).mpr ⟨S,Finset.mem_univ _,by simp⟩)
  simpa [Mask] using h

lemma rank_inj {r} : Function.Injective (@rank r) := by
  intro A B h; rcases lt_trichotomy (key A) (key B) with hl|he|hg
  · exact False.elim ((rank_mono hl).ne h)
  · exact key_inj he
  · exact False.elim ((rank_mono hg).ne h.symm)

lemma prefixCard {r k} (f : Mask r → Nat) (hi : Function.Injective f) (hb : ∀ S, f S < 2^r) (hk : k≤2^r) :
    (Finset.univ.filter (fun S => f S<k)).card=k := by
  have all : Finset.univ.image f = Finset.range (2^r) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hz; simpa using hb S
    · simp [Finset.card_image_of_injective _ hi,Mask]
  have he : (Finset.univ.filter (fun S => f S<k)).image f = Finset.range k := by
    ext z; simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_range]
    constructor
    · rintro ⟨S,hS,rfl⟩; exact hS
    · intro hz
      have hm : z ∈ Finset.univ.image f := by rw [all]; exact Finset.mem_range.mpr (lt_of_lt_of_le hz hk)
      obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hm; exact ⟨S,hz,rfl⟩
  simpa [Finset.card_image_of_injective _ hi] using congrArg Finset.card he

def pref (a d r k : Nat) : Fam r := Finset.univ.filter fun S => (if a≤d then idx S else rank S)<k

lemma prefCard {a d r k} (hk : k≤2^r) : (pref a d r k).card=k := by
  by_cases h : a≤d
  · simpa only [pref,h,ite_true] using prefixCard idx idx_inj idx_lt hk
  · simpa only [pref,h,ite_false] using prefixCard rank rank_inj rank_lt hk

lemma prefSubset {a d r u v} (h : u≤v) : pref a d r u ⊆ pref a d r v := by
  intro S hS; simp only [pref,Finset.mem_filter,Finset.mem_univ,true_and] at hS ⊢; omega

lemma weight_le {a d r} (h : d≤a) {S T : Mask r} (hST : S.card ≤ T.card) : weight a d S ≤ weight a d T := by
  have ht : T.card ≤ r := by simpa using T.card_le_univ
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hST
  have he : r-S.card = j+(r-T.card) := by omega
  unfold weight
  nth_rw 1 [he]; rw [pow_add]; conv_rhs => rw [hj,pow_add]
  calc
    _ = a^S.card * d^j * d^(r-T.card) := by ring
    _ ≤ a^S.card * a^j * d^(r-T.card) := by gcongr
    _ = _ := by rw [←hj]

lemma cheapest {a d r k} (h : ¬ a≤d) {M : Fam r} (hM : M.card=k) : cost a d (pref a d r k) ≤ cost a d M := by
  let B := pref a d r k
  have hk := prefCard (a:=a) (d:=d) (hM ▸ cap M)
  change cost a d B ≤ cost a d M
  have hcard : B.card=M.card := hk.trans hM.symm
  have hcross : ∀ S ∈ B\M, ∀ T ∈ M\B, weight a d S ≤ weight a d T := by
    intro S hS T hT
    have hs := (Finset.mem_sdiff.mp hS).1; have ht := (Finset.mem_sdiff.mp hT).2
    simp only [B,pref,h,ite_false,Finset.mem_filter,Finset.mem_univ,true_and] at hs ht
    apply weight_le (by omega)
    by_contra! hgt
    have hl := rank_mono ((key_lt T S).mpr (Or.inl hgt)); omega
  have ex := Finset.equivOfCardEq (Finset.card_sdiff_comm hcard)
  have hsum : (B\M).sum (weight a d) ≤ (M\B).sum (weight a d) := by
    rw [←Finset.sum_attach, ←Finset.sum_attach (s:=M\B)]
    exact (Finset.sum_le_sum (fun (i : ↥(B\M)) _ => hcross i i.2 (ex i) (ex i).2)).trans_eq
      (by simpa using ex.sum_comp (fun j => weight a d j.val))
  have h1 := Finset.sum_sdiff (f:=weight a d) (Finset.inter_subset_left (s₁:=B) (s₂:=M))
  have h2 := Finset.sum_sdiff (f:=weight a d) (Finset.inter_subset_right (s₁:=B) (s₂:=M))
  simp only [Finset.sdiff_inter_self_right,Finset.sdiff_inter_self_left] at h1 h2
  change (∑ x ∈ B\M, weight a d x) ≤ (∑ x ∈ M\B, weight a d x) at hsum
  change (∑ x ∈ B, weight a d x) ≤ ∑ x ∈ M, weight a d x
  omega

lemma prefDown (a d r k : Nat) : Down (pref a d r k) := by
  intro S hs T hTS
  have hi : idx T ≤ idx S := Finset.sum_le_sum_of_subset hTS
  have hc := Finset.card_le_card hTS
  by_cases had : a≤d
  · simp [pref,had] at hs ⊢; omega
  · simp [pref,had] at hs ⊢
    rcases lt_or_eq_of_le hc with hl | he
    · exact lt_trans (rank_mono ((key_lt T S).mpr (Or.inl hl))) hs
    · have hT : T=S := Finset.eq_of_subset_of_card_le hTS he.ge
      simpa only [hT] using hs

lemma prefCost {a d} (had : a≤d) (r k : Nat) (hk : k≤2^r) : cost a d (pref a d r k) = W a d r k := by
  induction r generalizing k with
  | zero => rw [costZero,prefCard hk,W]
  | succ r ih =>
    have he : join (pref a d r ((k+1)/2)) (pref a d r (k/2)) = pref a d (r+1) k := by
      ext A; obtain ⟨t,S,rfl⟩ := push_surj A
      cases t <;> simp [memJoin, pref, had, idxPush] <;> omega
    rw [←he,costJoin,ih _ (by rw [pow_succ] at hk; omega),ih _ (by rw [pow_succ] at hk; omega),W]

def bestCost (a d r k : Nat) := cost a d (pref a d r k)

lemma bestMono (a d r : Nat) : Monotone (bestCost a d r) := by
  intro u v huv
  exact Finset.sum_le_sum_of_subset (f := @weight a d r) (prefSubset (a:=a) (d:=d) (r:=r) huv)

lemma bestSplit (a d r u v : Nat) (hu : u≤2^r) (hv : v≤u) :
    bestCost a d (r+1) (u+v) ≤ d * bestCost a d r u + a * bestCost a d r v := by
  unfold bestCost; by_cases h : a≤d
  · rw [prefCost h _ _ (by rw [pow_succ]; omega),prefCost h _ _ hu,prefCost h _ _ (hv.trans hu)]
    exact W_split a d h r u v hv
  · rw [←costJoin]; apply cheapest h; rw [cardJoin,prefCard hu,prefCard (hv.trans hu)]

lemma bestLe (a b c : Nat) (hba : b≤a) {r} (M : Fam r) : bestCost a (b+c) r M.card ≤ see a b c M := by
  induction r with
  | zero => rw [seeZero,bestCost,costZero,prefCard (cap M)]
  | succ r ih =>
    let L := sec false M; let U := sec true M
    have he : join L U = M := joinSec M
    rw [←he,cardJoin,seeJoin]
    let F := bestCost a (b+c) r
    have H (X : Fam r) : F X.card ≤ see a b c X := ih X
    have mono : Monotone F := bestMono _ _ _
    by_cases hUL : U.card ≤ L.card
    · refine (bestSplit a (b+c) r _ _ (cap L) hUL).trans ?_
      have hLu := (mono (Finset.card_le_card (Finset.subset_union_left (s₂:=U) (s₁:=L)))).trans (H (L∪U))
      change (b+c)*F L.card + a*F U.card ≤ _
      calc
        _ = a*F U.card+b*F L.card+c*F L.card := by ring
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (H U)) (Nat.mul_le_mul_left _ (H L))) (Nat.mul_le_mul_left _ hLu)
    · have hLU : L.card ≤ U.card := by omega
      rw [Nat.add_comm L.card U.card]; refine (bestSplit a (b+c) r _ _ (cap U) hLU).trans ?_
      have hUu := (mono (Finset.card_le_card (Finset.subset_union_right (s₂:=U) (s₁:=L)))).trans (H (L∪U))
      change (b+c)*F U.card + a*F L.card ≤ _
      calc
        _ = (a*F L.card + b*F U.card) + c*F U.card := by ring
        _ ≤ (a*F U.card + b*F L.card) + c*F U.card := Nat.add_le_add_right (swapCost hba (mono hLU)) _
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (H U)) (Nat.mul_le_mul_left _ (H L))) (Nat.mul_le_mul_left _ hUu)

lemma rawSee (a b c : Nat) {r} (M : Fam r) :
    ((Finset.univ : Finset (Fin r → Fin (a+b+c))).filter (fun x => M.toList.any (fun S =>
      (Finset.univ : Finset (Fin r)).toList.all (fun j => if (x j).val < a then decide (j∈S) else
        if (x j).val < a+b then decide (j∉S) else true)))).card = see a b c M := by
  classical
  rw [Finset.card_filter, see]; apply Finset.sum_congr rfl; intro x hx
  congr 1; apply propext; simp only [List.any_eq_true,List.all_eq_true,Finset.mem_toList,Finset.mem_univ,true_implies,hit]
  apply exists_congr; intro S; apply and_congr_right; intro hS
  apply forall_congr'; intro j; by_cases h : (x j).val<a <;> by_cases h' : (x j).val<a+b <;> simp [cell,h,h']

end PEqualNP.Outside.L_lib_1165

theorem PEqualNP.Outside.L_lib_1165 : (∀ (r k a b c : Nat), b ≤ a → k ≤ 2 ^ r →
  let Kind := Finset (Fin r)
  let kinds := (Finset.univ : Finset Kind)
  let positions := (Finset.univ : Finset (Fin r))
  let omega := (Finset.univ : Finset (Fin r → Fin (a + b + c)))
  let sees := fun (M : Finset Kind) => (omega.filter (fun x =>
    M.toList.any (fun S => positions.toList.all (fun j =>
      if (x j).val < a then decide (j ∈ S) else
      if (x j).val < a + b then decide (j ∉ S) else true)))).card
  let index := fun (S : Kind) => S.sum (fun j => 2 ^ j.val)
  let weightOrder := fun (S : Kind) => (kinds.filter (fun V =>
    V.card < S.card ∨ (V.card = S.card ∧ index V < index S))).card
  let best := kinds.filter (fun S => (if a ≤ b + c then index S else weightOrder S) < k)
  best.card = k ∧ sees best =
    best.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) ∧
    ∀ M : Finset Kind, M.card = k → sees best ≤ sees M) := by
  intro r k a b c hba hk
  let B := PEqualNP.Outside.L_lib_1165.pref a (b+c) r k
  have hw := (PEqualNP.Outside.L_lib_1165.rawSee a b c B).trans
    (PEqualNP.Outside.L_lib_1165.seeDown a b c (PEqualNP.Outside.L_lib_1165.prefDown a (b+c) r k))
  refine ⟨PEqualNP.Outside.L_lib_1165.prefCard hk, hw, ?_⟩
  intro M hm
  have hl : PEqualNP.Outside.L_lib_1165.cost a (b+c) B ≤ PEqualNP.Outside.L_lib_1165.see a b c M := by
    simpa only [B,PEqualNP.Outside.L_lib_1165.bestCost,hm] using PEqualNP.Outside.L_lib_1165.bestLe a b c hba M
  exact hw.le.trans (hl.trans (PEqualNP.Outside.L_lib_1165.rawSee a b c M).symm.le)
