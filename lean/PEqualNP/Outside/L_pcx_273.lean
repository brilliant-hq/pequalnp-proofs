import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_273

private theorem fridayAffine (f d : ℕ → ℕ) (hf : ∀ i, f (i+1) = f i + d i)
    (hd : Monotone d) (b x : ℕ) : f b + x * d b ≤ f x + b * d b := by
  by_cases h : b ≤ x
  · induction x, h using Nat.le_induction with
    | base => omega
    | succ i hi ih =>
      rw [Nat.succ_mul, hf i]
      have hdi := hd hi
      omega
  · have hx : x ≤ b := by omega
    have aux : ∀ k : ℕ, x + k ≤ b → f (x+k) + x*d b ≤ f x + (x+k)*d b := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have hk' : x+k ≤ b := by omega
        have hii := ih hk'
        have hdi := hd hk'
        rw [Nat.add_succ, Nat.succ_mul, hf (x+k)]
        omega
    have eq : x + (b-x) = b := by omega
    simpa [eq] using aux (b-x) (by omega)

private theorem fridayConvexSum {ι : Type*} (K : Finset ι) (u : ι → ℕ)
    (m t : ℕ) (ht : 0 < t) (hk : K.card ≤ t) (hs : m ≤ ∑ c ∈ K, u c)
    (f d : ℕ → ℕ) (hf : ∀ i, f (i+1) = f i + d i) (hd : Monotone d)
    (hz : f (m/t) ≤ (m/t)*d (m/t)) :
    (t - m%t) * f (m/t) + (m%t)*f (m/t+1) ≤ ∑ c ∈ K, f (u c) := by
  let b := m / t
  let s := m % t
  let q := b*d b - f b
  have hq : b*d b = f b + q := by dsimp [q,b] at *; omega
  have hs0 : s ≤ t := Nat.le_of_lt (Nat.mod_lt m ht)
  have val : s + t*b = m := Nat.mod_add_div m t
  have hx : ∀ i, i*d b ≤ f i + q := by
    intro i
    have hi := fridayAffine f d hf hd b i
    omega
  have sums := Finset.sum_le_sum (s:=K) (fun c _ => hx (u c))
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul] at sums
  have upper : m * d b ≤ (∑ c ∈ K, f (u c)) + t*q := by
    exact (Nat.mul_le_mul_right (d b) hs).trans (sums.trans (Nat.add_le_add_left (Nat.mul_le_mul_right q hk) _))
  have parts : (t-s)+s=t := by omega
  have total : (t-s)*f b + s*f (b+1) + t*q = m*d b := by
    rw [hf b, Nat.mul_add]
    calc
      (t-s)*f b + (s * f b + s * d b) + t*q =
          ((t-s)+s)*f b + s*d b + t*q := by ring
      _ = t*f b + s*d b + t*q := by rw [parts]
      _ = s*d b + t*(f b+q) := by ring
      _ = (s+t*b)*d b := by rw [← hq]; ring
      _ = m*d b := by rw [val]
  change (t-s)*f b + s*f (b+1) ≤ _
  omega

theorem fridayBalance {ι : Type*} (K : Finset ι) (u : ι → ℕ) (n m t : ℕ)
    (hn : 2 ≤ n) (hm : 0 < m) (ht : 0 < t) (htm : t ≤ m)
    (hk : K.card ≤ t) (hs : m ≤ ∑ c ∈ K, u c) :
    (t - m%t) * n^(m/t) + (m%t)*n^(m/t+1) ≤ ∑ c ∈ K, n^(u c) ∧
    (t - m%t) * (m/t)*n^(m/t) + (m%t)*(m/t+1)*n^(m/t+1) ≤ ∑ c ∈ K, u c*n^(u c) ∧
    ∃ c ∈ K, (m+t-1)/t ≤ u c := by
  let d := n-1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hn' : d+1=n := by dsimp [d]; omega
  have hb : 1 ≤ m/t := (Nat.le_div_iff_mul_le ht).2 (by simpa using htm)
  have hpow : Monotone (fun i : ℕ => n^i) := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  constructor
  · apply fridayConvexSum K u m t ht hk hs (fun i => n^i) (fun i => d*n^i)
    · intro i
      change n^(i+1) = n^i + d*n^i
      rw [pow_succ]
      calc n^i*n = n^i*(d+1) := by rw [hn']
           _ = _ := by ring
    · intro i j hij
      exact Nat.mul_le_mul_left _ (hpow hij)
    · let b := m/t
      change n^b ≤ b*(d*n^b)
      calc n^b = 1*(1*n^b) := by simp
           _ ≤ b*(d*n^b) := Nat.mul_le_mul hb (Nat.mul_le_mul_right _ hd)
  constructor
  · simp only [Nat.mul_assoc]
    apply fridayConvexSum K u m t ht hk hs (fun i => i*n^i) (fun i => n^i*((i+1)*d+1))
    · intro i
      change (i+1)*n^(i+1) = i*n^i+n^i*((i+1)*d+1)
      rw [pow_succ]
      calc (i+1)*(n^i*n) = (i+1)*(n^i*(d+1)) := by rw [hn']
           _ = _ := by ring
    · intro i j hij
      apply Nat.mul_le_mul (hpow hij)
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega : i+1 ≤ j+1)) 1
    · apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_right _ (by omega)
  · by_contra! h
    have hw : m + t - 1 = (m-1) + t := by omega
    have hceil : (m+t-1)/t = (m-1)/t + 1 := by rw [hw, Nat.add_div_right _ ht]
    have small : ∀ c ∈ K, u c ≤ (m-1)/t := by
      intro c hc
      have hcu := h c hc
      omega
    have hc := Finset.sum_le_sum small
    simp only [Finset.sum_const, nsmul_eq_mul] at hc
    have cardlim := Nat.mul_le_mul_right ((m-1)/t) hk
    have last : t*((m-1)/t) ≤ m-1 := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (m-1) t
    have habs : m ≤ m-1 := hs.trans (hc.trans (cardlim.trans last))
    omega


open PEqualNP.ProofComplexity
private abbrev Vv (m n a : ℕ) := Sum (Fin m × Fin n) (Fin a)
private abbrev Cc (m n a : ℕ) := Clause (Vv m n a)
private abbrev Word (m n : ℕ) := Fin m → Fin n
private def misses {m n : ℕ} (f : Word m n) (e : Fin m × Fin n) : Bool :=
  decide (e.2 ≠ f e.1)
private def patch {m n : ℕ} (f : Word m n) (j : Fin m) (e : Fin m × Fin n) : Bool :=
  if e.1 = j then true else misses f e

private abbrev goodEnc {m n a : ℕ} (G : Finset (Cc m n a)) :=
  ∀ x : (Fin m × Fin n) → Bool, (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
  ∃ z : Fin a → Bool, Satisfies (Sum.elim x z) (↑G : Set _)

private def lbRawLits {m n a : ℕ} (D : Cc m n a) := D.filter (fun l =>
  l.2 = true ∧ ∃ e : Fin m × Fin n, l.1 = Sum.inl e)

private def raws {m n a : ℕ} (D : Cc m n a) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun e => (Sum.inl e, true) ∈ D

private theorem numRaws {m n a : ℕ} (D : Cc m n a) : (raws D).card = (lbRawLits D).card := by
  classical
  let g : Fin m × Fin n → (Vv m n a × Bool) := fun e => (Sum.inl e,true)
  have hj : Function.Injective g := fun x y h => Sum.inl.inj (congrArg Prod.fst h)
  have hh : (raws D).image g = lbRawLits D := by
    ext l
    simp only [Finset.mem_image,raws,lbRawLits,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases l with ⟨e,o⟩
    cases e <;> cases o <;> simp [g]
  rw [← hh, Finset.card_image_of_injective _ hj]

private def rowsHit {m n a : ℕ} (D : Cc m n a) := (raws D).image Prod.fst

private lemma selected {m n a : ℕ} (G : Finset (Cc m n a)) (hg : goodEnc G)
    (f : Word m n) : ∃ K : Finset (Cc m n a), K ⊆ G ∧ K.card ≤ min m (2^a) ∧
      (∀ j : Fin m, ∃ D ∈ K, (j,f j) ∈ raws D) ∧
      (∀ D ∈ K, (raws D).Nonempty ∧ ∀ e ∈ raws D, e.2 = f e.1) := by
  classical
  have hn : ¬ ∃ z : Fin a → Bool, Satisfies (Sum.elim (misses f) z) (↑G : Set _) := by
    rintro ⟨z,hz⟩
    obtain ⟨j,hj⟩ := (hg _).2 ⟨z,hz⟩
    simpa [misses] using hj (f j)
  have reject (z : Fin a → Bool) : ∃ D ∈ G, ¬ ClauseSat (Sum.elim (misses f) z) D := by
    by_contra! h
    exact hn ⟨z,h⟩
  choose bad hG hbad using reject
  have satisfy (j : Fin m) : ∃ z : Fin a → Bool, Satisfies (Sum.elim (patch f j) z) (↑G : Set _) :=
    (hg _).1 ⟨j, fun i => by simp [patch]⟩
  choose wit hw using satisfy
  have fixed (z : Fin a → Bool) (e : Fin m × Fin n) (he : e ∈ raws (bad z)) : e.2 = f e.1 := by
    by_contra h
    exact hbad z ⟨(Sum.inl e,true),(Finset.mem_filter.mp he).2,by simpa [misses] using h⟩
  have touches (j : Fin m) : (j,f j) ∈ raws (bad (wit j)) := by
    obtain ⟨⟨v,t⟩,hl,ht⟩ := hw j _ (hG (wit j))
    have nu : Sum.elim (misses f) (wit j) v ≠ t := fun hh => hbad (wit j) ⟨(v,t),hl,hh⟩
    cases v with
    | inr h => exact (nu ht).elim
    | inl e =>
      rcases e with ⟨row,col⟩
      by_cases he : row = j
      · subst row
        have ht' : true = t := by simpa [patch] using ht
        subst t
        by_cases hc : col = f j
        · simpa [raws,hc] using hl
        · exact (nu (by simpa [misses] using hc)).elim
      · exact (nu (by simpa [patch,he] using ht)).elim
  let K := Finset.univ.image fun j => bad (wit j)
  refine ⟨K,?_,le_min ?_ ?_,?_,?_⟩
  · intro D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hG _
  · simpa [K] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun j => bad (wit j)))
  · have sub : K ⊆ Finset.univ.image bad := by
      intro D hD
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
      exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
    exact (Finset.card_le_card sub).trans (by simpa using (Finset.card_image_le (s := Finset.univ) (f := bad)))
  · intro j
    exact ⟨_,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,touches j⟩
  · intro D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact ⟨⟨_,touches j⟩,fixed _⟩

private lemma rowCover {m n a : ℕ} (K : Finset (Cc m n a)) (f : Word m n)
    (h : ∀ j, ∃ D ∈ K, (j,f j) ∈ raws D) :
    m ≤ ∑ D ∈ K, (lbRawLits D).card := by
  classical
  have hU : Finset.univ ⊆ K.biUnion rowsHit := by
    intro i _
    obtain ⟨D,hD,hi⟩ := h i
    exact Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨_,hi,rfl⟩⟩
  calc
    m = (Finset.univ : Finset (Fin m)).card := by simp
    _ ≤ _ := Finset.card_le_card hU
    _ ≤ ∑ D ∈ K, (rowsHit D).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun D _ => (Finset.card_image_le (s := raws D) (f := Prod.fst)).trans_eq (numRaws D))

private lemma rowCard {m n a : ℕ} {D : Cc m n a} (f : Word m n)
    (fixed : ∀ e ∈ raws D, e.2 = f e.1) :
    (rowsHit D).card = (lbRawLits D).card := by
  classical
  rw [rowsHit,Finset.card_image_of_injOn, numRaws]
  intro e he v hv hh
  exact Prod.ext hh (by rw [fixed _ he, fixed _ hv, hh])

private lemma countFiber {m n a : ℕ} (K : Word m n → Finset (Cc m n a))
    (fixed : ∀ f, ∀ D ∈ K f, ∀ e ∈ raws D, e.2 = f e.1) (D : Cc m n a) :
    ((Finset.univ : Finset (Word m n)).filter (fun f => D ∈ K f)).card * n^(lbRawLits D).card ≤ n^m := by
  classical
  let S := (Finset.univ : Finset (Word m n)).filter (fun f => D ∈ K f)
  change S.card * _ ≤ _
  by_cases hz : S.Nonempty
  · obtain ⟨f0,hf0⟩ := hz
    have h0 : D ∈ K f0 := (Finset.mem_filter.mp hf0).2
    let A := (rowsHit D)ᶜ
    let restr : (↥S) → (↥A → Fin n) := fun f i => f.val i.val
    have inj : Function.Injective restr := by
      intro f g hfg
      apply Subtype.ext
      funext i
      by_cases hmem : i ∈ rowsHit D
      · obtain ⟨e,he,hee⟩ := Finset.mem_image.mp hmem
        change e.1 = i at hee
        subst i
        exact (fixed f.val D (Finset.mem_filter.mp f.property).2 e he).symm.trans
          (fixed g.val D (Finset.mem_filter.mp g.property).2 e he)
      · exact congrFun hfg ⟨i,Finset.mem_compl.mpr hmem⟩
    have hbound := Fintype.card_le_of_injective restr inj
    have hr := rowCard f0 (fixed f0 D h0)
    have hm : (lbRawLits D).card ≤ m := by simpa [←hr] using (Finset.card_le_univ (rowsHit D))
    have hb : S.card ≤ n^(m-(lbRawLits D).card) := by
      simpa [A,Fintype.card_fun,Finset.card_compl,hr] using hbound
    calc
      _ ≤ n^(m-(lbRawLits D).card) * n^(lbRawLits D).card := Nat.mul_le_mul_right _ hb
      _ = _ := by rw [←pow_add,Nat.sub_add_cancel hm]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hz]

private lemma sumCharges {m n a : ℕ} (G : Finset (Cc m n a)) (K : Word m n → Finset (Cc m n a))
    (hKG : ∀ f, K f ⊆ G)
    (fixed : ∀ f, ∀ D ∈ K f, ∀ e ∈ raws D, e.2 = f e.1) (v : Cc m n a → ℕ) :
    (∑ f : Word m n, ∑ D ∈ K f, n^(lbRawLits D).card * v D) ≤ n^m * ∑ D ∈ G, v D := by
  classical
  let amount := fun D : Cc m n a => n^(lbRawLits D).card * v D
  have eqsum (f : Word m n) :
      (∑ D ∈ K f, amount D) = ∑ D ∈ G, if D ∈ K f then amount D else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext D
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hKG f h,h⟩,And.right⟩
  change (∑ f : Word m n, ∑ D ∈ K f, amount D) ≤ _
  simp_rw [eqsum]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
  simpa [amount,←Nat.mul_assoc] using (Nat.mul_le_mul_right (v D) (countFiber K fixed D))


theorem fridayLower (n m a : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (G : Finset (Cc m n a)) (hG : goodEnc G) :
    let t := min m (2^a)
    let b := m/t
    let s := m%t
    (t-s)*n^b + s*n^(b+1) ≤ G.card ∧
      (t-s)*b*n^b + s*(b+1)*n^(b+1) ≤ ∑ D ∈ G, (lbRawLits D).card ∧
      ∃ D ∈ G, (m+t-1)/t ≤ (lbRawLits D).card := by
  classical
  let t := min m (2^a)
  let u := fun D : Cc m n a => (lbRawLits D).card
  have ht : 0 < t := lt_min hm (pow_pos (by decide) a)
  choose K sub cards cov fix using selected G hG
  have strength (f : Word m n) :=
    fridayBalance (K f) u n m t hn hm ht (Nat.min_le_left ..) (cards f) (rowCover (K f) f (cov f))
  have hc (v : Cc m n a → ℕ) (Q : ℕ) (hQ : ∀ f, Q ≤ ∑ D ∈ K f, n^u D * v D) :
      Q ≤ ∑ D ∈ G, v D := by
    have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Word m n))) (fun f _ => hQ f)
    have total := sumCharges G K sub (fun f D hD => (fix f D hD).2) v
    have hle' : n^m * Q ≤ n^m * ∑ D ∈ G, v D := by
      simpa [Word,Fintype.card_fun] using hle.trans total
    exact Nat.le_of_mul_le_mul_left hle' (pow_pos (by omega) _)
  refine ⟨?_,?_,?_⟩
  · simpa using hc (fun _ => 1) _ (fun f => by simpa using (strength f).1)
  · apply hc u
    intro f
    simpa only [Nat.mul_comm] using (strength f).2.1
  · let f : Word m n := fun _ => ⟨0, by omega⟩
    obtain ⟨D,hD,hwidth⟩ := (strength f).2.2
    exact ⟨D,sub f hD,hwidth⟩

theorem fridayLayout (n m a : ℕ) (_hn : 2 ≤ n) (hm : 0 < m) :
    let t := min m (2^a)
    let b := m/t
    let s := m%t
    ∃ w : Fin t → ℕ, (∀ j, 0 < w j) ∧ (∑ j, w j) = m ∧
      (∑ j, n^(w j)) = (t-s)*n^b+s*n^(b+1) ∧
      (∑ j, (w j)*n^(w j)) = (t-s)*b*n^b+s*(b+1)*n^(b+1) ∧
      ∀ j, w j ≤ (m+t-1)/t := by
  dsimp only
  let t := min m (2^a)
  let b := m/t
  let s := m%t
  have ht : 0 < t := lt_min hm (by positivity)
  have htm : t ≤ m := min_le_left _ _
  have hp : 0 < b := Nat.div_pos htm ht
  have hs : s ≤ t := Nat.le_of_lt (Nat.mod_lt m ht)
  have he : (t-s)+s = t := by omega
  let e : (Fin (t-s) ⊕ Fin s) ≃ Fin t := finSumFinEquiv.trans (finCongr he)
  let g : Fin (t-s) ⊕ Fin s → ℕ := Sum.elim (fun _ => b) (fun _ => b+1)
  let w : Fin t → ℕ := fun j => g (e.symm j)
  have hsum (f : ℕ → ℕ) : (∑ j, f (w j)) = (t-s)*f b+s*f (b+1) := by
    calc
      (∑ j, f (w j)) = ∑ j, f (g j) := Equiv.sum_comp e.symm (fun j => f (g j))
      _ = _ := by simp [Fintype.sum_sum_type,g,nsmul_eq_mul]
  have hbs : s + t*b = m := Nat.mod_add_div m t
  refine ⟨w, ?_, ?_, hsum (fun x => n^x), ?_, ?_⟩
  · intro j
    cases q : e.symm j <;> simp [w,q,g,hp]
  · calc
      (∑ j, w j) = (t-s)*b+s*(b+1) := hsum id
      _ = s + ((t-s)+s)*b := by ring
      _ = m := by rw [he,hbs]
  · simpa only [Nat.mul_assoc] using hsum (fun x => x*n^x)
  · intro j
    apply (Nat.le_div_iff_mul_le ht).2
    have hs' : s+b*t=m := by simpa [Nat.mul_comm] using hbs
    cases q : e.symm j with
    | inl i =>
      change g (e.symm j) * t ≤ m+t-1
      rw [q]
      change b*t ≤ m+t-1
      omega
    | inr i =>
      have hi := i.isLt
      change g (e.symm j) * t ≤ m+t-1
      rw [q]
      change (b+1)*t ≤ m+t-1
      rw [Nat.succ_mul]
      omega

def Matches {a : ℕ} (p : Fin a → Option Bool) (z : Fin a → Bool) : Prop :=
  ∀ i c, p i = some c → z i = c

theorem matchPoint {a : ℕ} (p : Fin a → Option Bool) :
    Matches p (fun i => (p i).getD false) := by
  intro i c h
  simp [h]

theorem matchesCons {a : ℕ} (b : Bool) (p : Fin a → Option Bool) (z : Fin (a+1) → Bool) :
    Matches (Fin.cons (some b) p) z ↔ z 0 = b ∧ Matches p (fun i => z i.succ) := by
  constructor
  · intro h
    exact ⟨h 0 b (by simp), fun i c hc => h i.succ c (by simpa using hc)⟩
  · rintro ⟨h0,h⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro c hc
      simpa using h0.trans (by simpa using hc : b = c)
    · intro c hc
      exact h j c (by simpa using hc)

theorem maskPartition (a t : ℕ) (hp : 0 < t) (hc : t ≤ 2^a) :
    ∃ p : Fin t → Fin a → Option Bool, ∀ z, ∃! j, Matches (p j) z := by
  induction a generalizing t with
  | zero =>
    simp at hc
    have ht : t = 1 := by omega
    subst t
    exact ⟨fun _ _ => none, fun z => ⟨0, by simp [Matches], fun i _ => Subsingleton.elim _ _⟩⟩
  | succ a ih =>
    by_cases h : t ≤ 2^a
    · obtain ⟨p,H⟩ := ih t hp h
      refine ⟨fun j => Fin.cons none (p j), fun z => ?_⟩
      have e (j : Fin t) : Matches (Fin.cons none (p j)) z ↔ Matches (p j) (fun i => z i.succ) := by
        constructor
        · intro M i c hc
          exact M i.succ c (by simpa using hc)
        · intro M i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp
          · intro c hz
            exact M j c (by simpa using hz)
      obtain ⟨q,hq,hu⟩ := H (fun i => z i.succ)
      exact ⟨q,(e q).2 hq,fun j hj => hu j ((e j).1 hj)⟩
    · let k := 2^a
      let l := t-k
      have hpos : 0 < k := by simp [k]
      have hl : 0 < l := by dsimp [k,l] at *; omega
      have hl' : l ≤ k := by dsimp [k,l] at *; rw [pow_succ] at hc; omega
      obtain ⟨p,Hp⟩ := ih k hpos (by rfl)
      obtain ⟨q,Hq⟩ := ih l hl hl'
      have hsum : k+l=t := by dsimp [l,k] at *; omega
      let e : Fin k ⊕ Fin l ≃ Fin t := finSumFinEquiv.trans (finCongr hsum)
      let pat : Fin k ⊕ Fin l → Fin (a+1) → Option Bool := Sum.elim
        (fun i => Fin.cons (some false) (p i)) (fun i => Fin.cons (some true) (q i))
      refine ⟨fun j => pat (e.symm j), fun z => ?_⟩
      cases hz : z 0 with
      | false =>
        obtain ⟨i,hi,hu⟩ := Hp (fun j => z j.succ)
        refine ⟨e (.inl i), ?_, ?_⟩
        · simpa [pat, matchesCons, hz] using hi
        · intro j hj
          apply e.symm.injective
          rw [e.symm_apply_apply]
          cases hh : e.symm j with
          | inl i' =>
            have hm : Matches (p i') (fun j => z j.succ) := by simpa [hh,pat,matchesCons,hz] using hj
            exact congrArg Sum.inl (hu i' hm)
          | inr i' => simpa [hh,pat,matchesCons,hz] using hj
      | true =>
        obtain ⟨i,hi,hu⟩ := Hq (fun j => z j.succ)
        refine ⟨e (.inr i), ?_, ?_⟩
        · simpa [pat,matchesCons,hz] using hi
        · intro j hj
          apply e.symm.injective
          rw [e.symm_apply_apply]
          cases hh : e.symm j with
          | inl i' => simpa [hh,pat,matchesCons,hz] using hj
          | inr i' =>
            have hm : Matches (q i') (fun j => z j.succ) := by simpa [hh,pat,matchesCons,hz] using hj
            exact congrArg Sum.inr (hu i' hm)
open PEqualNP.ProofComplexity

abbrev Raw (m n : ℕ) := Fin m × Fin n
abbrev Var (m n a : ℕ) := Sum (Raw m n) (Fin a)
abbrev Layout (m t : ℕ) (w : Fin t → ℕ) := (Σ j, Fin (w j)) ≃ Fin m

def posSet {m n a : ℕ} (C : Clause (Var m n a)) := C.filter fun l =>
  l.2 = true ∧ ∃ e : Raw m n, l.1 = Sum.inl e

def rawLits {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w) (j : Fin t)
    (f : Fin (w j) → Fin n) : Clause (Var m n a) :=
  Finset.univ.image fun i => (Sum.inl (r ⟨j,i⟩, f i),true)

def guardLits {n m a : ℕ} (p : Fin a → Option Bool) : Clause (Var m n a) :=
  Finset.univ.filter fun l => (match l.1 with
    | .inr i => decide (p i = some (!l.2))
    | .inl _ => false) = true

def buildClause {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w)
    (p : Fin t → Fin a → Option Bool) (c : Σ j, Fin (w j) → Fin n) :
    Clause (Var m n a) := rawLits r c.1 c.2 ∪ guardLits (p c.1)

theorem posBuilt {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w)
    (p : Fin t → Fin a → Option Bool) (c : Σ j, Fin (w j) → Fin n) :
    posSet (buildClause r p c) = rawLits r c.1 c.2 := by
  classical
  ext l
  rcases l with ⟨u,b⟩
  rcases u with ⟨u,v⟩ | i <;> cases b <;>
    simp [posSet,buildClause,rawLits,guardLits]

theorem builtWidth {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w)
    (p : Fin t → Fin a → Option Bool) (c : Σ j, Fin (w j) → Fin n) :
    (posSet (buildClause r p c)).card = w c.1 := by
  classical
  rw [posBuilt,rawLits,Finset.card_image_of_injective]
  · simp
  · intro i k h
    have H : (⟨c.1,i⟩ : Σ j, Fin (w j)) = ⟨c.1,k⟩ :=
      r.injective (congrArg Prod.fst (Sum.inl.inj (congrArg Prod.fst h)))
    simpa using H

theorem buildClause_sat {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w)
    (p : Fin t → Fin a → Option Bool) (c : Σ j, Fin (w j) → Fin n)
    (x : Raw m n → Bool) (z : Fin a → Bool) :
    ClauseSat (Sum.elim x z) (buildClause r p c) ↔
      (∃ i, x (r ⟨c.1,i⟩,c.2 i) = true) ∨ ¬ Matches (p c.1) z := by
  classical
  constructor
  · rintro ⟨⟨q,b⟩,hq,hv⟩
    rcases Finset.mem_union.mp hq with ha | ha
    · obtain ⟨i,_,hh⟩ := Finset.mem_image.mp ha
      cases hh
      exact Or.inl ⟨i,hv⟩
    · right
      intro hm
      rcases q with u | i
      · simpa [guardLits] using ha
      · have hp : p c.1 i = some (!b) := by simpa [guardLits] using ha
        have h1 := hm i (!b) hp
        have h2 : z i = b := hv
        cases b <;> simp_all
  · rintro (⟨i,hi⟩|h)
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),hi⟩
    · unfold Matches at h
      push_neg at h
      obtain ⟨i,b,hp,hn⟩ := h
      refine ⟨(Sum.inr i,!b), Finset.mem_union_right _ ?_, ?_⟩
      · simpa [guardLits] using hp
      · change z i = !b
        cases b <;> cases hzi : z i <;> simp_all

theorem buildEnc {n m t a : ℕ} {w : Fin t → ℕ} (r : Layout m t w)
    (p : Fin t → Fin a → Option Bool) (hp : ∀ z, ∃! j, Matches (p j) z)
    (x : Raw m n → Bool) :
    (∃ j, ∀ i, x (j,i) = true) ↔ ∃ z, Satisfies (Sum.elim x z)
      (↑(Finset.univ.image (buildClause (n:=n) r p)) : Set (Clause (Var m n a))) := by
  classical
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨⟨j,i⟩,rfl⟩ := r.surjective b
    let z := fun q => (p j q).getD false
    have hmatch : Matches (p j) z := matchPoint _
    obtain ⟨j0,_,huniq⟩ := hp z
    refine ⟨z,?_⟩
    intro C hC
    obtain ⟨⟨k,f⟩,_,rfl⟩ := Finset.mem_image.mp hC
    apply (buildClause_sat r p _ x z).2
    by_cases hk : Matches (p k) z
    · have he : k=j := (huniq _ hk).trans (huniq _ hmatch).symm
      subst k
      exact Or.inl ⟨i,hb _⟩
    · exact Or.inr hk
  · rintro ⟨z,hz⟩
    obtain ⟨j,hj,_⟩ := hp z
    by_contra! h
    have hn (i : Fin (w j)) := h (r ⟨j,i⟩)
    choose f hf using hn
    let c : Σ j, Fin (w j) → Fin n := ⟨j,f⟩
    have hs := hz (buildClause r p c) (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩)
    rcases (buildClause_sat r p c x z).1 hs with ⟨i,hi⟩ | hn
    · simpa [c, hf i] using hi
    · exact hn hj

theorem buildClause_injective {n m t a : ℕ} {w : Fin t → ℕ} (hw : ∀ j, 0 < w j)
    (r : Layout m t w) (p : Fin t → Fin a → Option Bool) :
    Function.Injective (buildClause (n:=n) r p) := by
  classical
  rintro ⟨j,f⟩ ⟨k,g⟩ h
  have hr := congrArg posSet h
  rw [posBuilt,posBuilt] at hr
  change rawLits (a:=a) r j f = rawLits r k g at hr
  have matchAt (i : Fin (w j)) : ∃ l : Fin (w k),
      (⟨k,l⟩ : Σ s, Fin (w s)) = ⟨j,i⟩ ∧ g l = f i := by
    have mem : (Sum.inl (r ⟨j,i⟩,f i),true) ∈ rawLits (a:=a) r k g := by
      rw [← hr]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp mem
    change (Sum.inl (r ⟨k,l⟩,g l),true) = (Sum.inl (r ⟨j,i⟩,f i),true) at he
    have hh := Sum.inl.inj (congrArg Prod.fst he)
    exact ⟨l,r.injective (congrArg Prod.fst hh),congrArg Prod.snd hh⟩
  obtain ⟨l,h1,_⟩ := matchAt ⟨0,hw j⟩
  have hk : k = j := congrArg Sigma.fst h1
  subst k
  have hfun : f = g := by
    funext i
    obtain ⟨l,hl,hh⟩ := matchAt i
    have hs : l = i := by simpa using hl
    simpa [hs] using hh.symm
  subst g
  rfl

theorem buildCounts (n m t a : ℕ) (w : Fin t → ℕ) (hw : ∀ j, 0 < w j)
    (r : Layout m t w) (p : Fin t → Fin a → Option Bool) :
    let F := Finset.univ.image (buildClause (n:=n) r p)
    F.card = ∑ j, n^(w j) ∧
    (∑ C ∈ F, (posSet C).card) = ∑ j, w j * n^(w j) ∧
    ∀ C ∈ F, ∀ e : Raw m n, (Sum.inl e,false) ∉ C := by
  classical
  dsimp only
  have hinj := buildClause_injective (n:=n) hw r p
  constructor
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_sigma]
    simp
  constructor
  · rw [Finset.sum_image hinj.injOn]
    simp_rw [builtWidth]
    rw [Fintype.sum_sigma]
    simp [Nat.mul_comm]
  · intro C hC e
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hC
    simp [buildClause,rawLits,guardLits]

end PEqualNP.Outside.L_pcx_273

open PEqualNP.Outside.L_pcx_273 in
theorem PEqualNP.Outside.L_pcx_273 : (∀ (n m a : ℕ), 2 ≤ n → 0 < m →
  let Raw := Fin m × Fin n
  let Var := Sum Raw (Fin a)
  let Cl := PEqualNP.ProofComplexity.Clause Var
  let enc := fun F : Finset Cl => ∀ x : Raw → Bool,
    (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
      ∃ z : Fin a → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x z) (↑F : Set _)
  let pos := fun C : Cl => (C.filter (fun l =>
    l.2 = true ∧ ∃ e : Raw, l.1 = Sum.inl e)).card
  let t := min m (2^a)
  let b := m / t
  let s := m % t
  let count := (t-s) * n^b + s * n^(b+1)
  let lits := (t-s) * b * n^b + s * (b+1) * n^(b+1)
  let width := (m+t-1) / t
  (∃ F : Finset Cl, enc F ∧ F.card = count ∧ (∑ C ∈ F, pos C) = lits ∧
    (∀ C ∈ F, pos C ≤ width) ∧
    ∀ C ∈ F, ∀ e : Raw, (Sum.inl e, false) ∉ C) ∧
  ∀ G : Finset Cl, enc G → count ≤ G.card ∧
    lits ≤ (∑ D ∈ G, pos D) ∧ ∃ D ∈ G, width ≤ pos D) := by
  classical
  intro n m a hn hm
  dsimp only
  constructor
  · let t := min m (2^a)
    obtain ⟨w,hw,hsum,hcard,hlits,hwidth⟩ := fridayLayout n m a hn hm
    have ht : 0 < t := lt_min hm (pow_pos (by decide) a)
    obtain ⟨p,hp⟩ := maskPartition a t ht (min_le_right ..)
    let r : Layout m t w := Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using hsum)
    let F := Finset.univ.image (buildClause (n:=n) r p)
    obtain ⟨hc,hl,hnraw⟩ := buildCounts n m t a w hw r p
    refine ⟨F,buildEnc r p hp,hc.trans hcard,hl.trans hlits,?_,hnraw⟩
    intro C hC
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hC
    exact (builtWidth r p c).le.trans (hwidth c.1)
  · exact fun G hG => fridayLower n m a hn hm G hG
