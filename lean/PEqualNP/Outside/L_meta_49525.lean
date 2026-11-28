import Mathlib.Tactic

/- Integer telescoping helpers adapted from accepted L-meta-48520. -/

namespace PEqualNP.Outside.L_meta_49525_aux

def step {n : ℕ} (u v : Finset (Fin n)) : Prop :=
  ∃ i : Fin n, i ∉ u ∧ v = insert i u

def adj {n : ℕ} (u v : Finset (Fin n)) : Prop :=
  step u v ∨ step v u

def wcost {n : ℕ} (r : Finset (Fin n) → ℕ) {l : ℕ} (p : Fin (l + 1) → Finset (Fin n)) : ℕ :=
  Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc))

lemma sum_telescope_int {l : ℕ} (g : Fin (l + 1) → ℤ) :
    Finset.univ.sum (fun i : Fin l => g i.castSucc - g i.succ) = g 0 - g (Fin.last l) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun k => g k.castSucc)
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.castSucc - g i.castSucc.succ)) = g 0 - g (Fin.last l).castSucc := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1, Fin.succ_last]
    ring

lemma sum_telescope_nat_mono {l : ℕ} (g : Fin (l + 1) → ℕ)
    (hmono : ∀ i : Fin l, g i.castSucc ≤ g i.succ) :
    Finset.univ.sum (fun i : Fin l => g i.succ - g i.castSucc) = g (Fin.last l) - g 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hmono' : ∀ i : Fin l, g i.castSucc.castSucc ≤ g i.succ.castSucc := fun i => by
      rw [← Fin.succ_castSucc]
      exact hmono i.castSucc
    have hih := ih (fun k => g k.castSucc) hmono'
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.succ - g i.castSucc.castSucc)) = g (Fin.last l).castSucc - g 0 := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1]
    have h0_le : g 0 ≤ g (Fin.last l).castSucc := by
      have hgen : ∀ k : Fin (l + 1), g 0 ≤ g k.castSucc := by
        intro k
        induction k using Fin.induction with
        | zero => simp
        | succ k ihk => exact ihk.trans (hmono k.castSucc)
      exact hgen (Fin.last l)
    have hlast_le : g (Fin.last l).castSucc ≤ g (Fin.last l.succ) := by
      have := hmono (Fin.last l)
      rwa [Fin.succ_last] at this
    rw [Fin.succ_last]
    change g (Fin.last l).castSucc - g 0 + (g (Fin.last l.succ) - g (Fin.last l).castSucc) = g (Fin.last l.succ) - g 0
    omega


end PEqualNP.Outside.L_meta_49525_aux

namespace PEqualNP.Outside.L_meta_49525_aux
open scoped Classical

noncomputable def centers {n : Nat} (g : Fin n → Fin n → Prop) (x : Finset (Fin n)) :
    Finset (Fin n) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  exact Finset.univ.filter (fun c => ∀ u∈x, g u c)
def Fits {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop)
    (f : Finset (Fin n) → Fin n → Nat) : Prop :=
  (∀ x j, f x j≤D) ∧ (∀ x j, j∈centers g x → f x j=D) ∧
  (∀ x j, j∈x → f x j=0) ∧ (∀ x y, x⊆y → ∀ j, f y j≤f x j)
def Bounds {n : Nat} (f : Finset (Fin n) → Fin n → Nat) (B : Nat) : Prop :=
  ∀ (l : Nat) (p : Fin (l+1) → Finset (Fin n)) (a : Fin l → Fin n),
    (∀ i : Fin l, p i.castSucc⊆p i.succ) →
    (∑ i : Fin l, (f (p i.castSucc) (a i)-f (p i.succ) (a i))) ≤ B
def Tests {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop) (B : Nat) : Prop :=
  (0<n → D≤B) ∧ ((∃ i j, g i j) → 2*D≤B) ∧
  ∀ (r : Nat) (p : Fin (r+1) → Fin n), g (p 0) (p (Fin.last r)) →
    (∀ i : Fin r, ∃ c, g (p i.castSucc) c ∧ g (p i.succ) c) →
    D≤r*(B-2*D)

lemma mem_centers {n : Nat} (g : Fin n → Fin n → Prop) (x : Finset (Fin n)) (c : Fin n) :
    c∈centers g x ↔ ∀ u∈x, g u c := by simp [centers]

lemma centers_anti {n : Nat} (g : Fin n → Fin n → Prop)
    {x y : Finset (Fin n)} (hxy : x⊆y) : centers g y⊆centers g x := by
  intro c hc
  exact (mem_centers g x c).mpr (fun u hu => (mem_centers g y c).mp hc u (hxy hu))

lemma fits_empty {n D : Nat} {g : Fin n → Fin n → Prop}
    {f : Finset (Fin n) → Fin n → Nat} (hf : Fits D g f) (j : Fin n) : f ∅ j=D :=
  hf.2.1 ∅ j (by simp [centers])
lemma fits_self {n D : Nat} {g : Fin n → Fin n → Prop}
    {f : Finset (Fin n) → Fin n → Nat} (hf : Fits D g f) (j : Fin n) : f {j} j=0 :=
  hf.2.2.1 {j} j (by simp)

lemma necessary_one {n D B : Nat} {g : Fin n → Fin n → Prop}
    {f : Finset (Fin n) → Fin n → Nat} (hf : Fits D g f) (hb : Bounds f B) :
    0<n → D≤B := by
  intro hn
  let j : Fin n := ⟨0,hn⟩
  have hc : ∀ i : Fin 1, (![∅,{j}] : Fin 2 → Finset (Fin n)) i.castSucc⊆![∅,{j}] i.succ := by
    intro i; fin_cases i; simp
  have h := hb 1 ![∅,{j}] ![j] hc
  simpa [Fin.sum_univ_succ,fits_empty hf,fits_self hf] using h

lemma necessary_two {n D B : Nat} {g : Fin n → Fin n → Prop}
    {f : Finset (Fin n) → Fin n → Nat} (hf : Fits D g f) (hb : Bounds f B) :
    (∃ u v, g u v) → 2*D≤B := by
  rintro ⟨u,v,huv⟩
  have hcv : v∈centers g {u} := by simp [centers,huv]
  have hs : f {u} v=D := hf.2.1 _ _ hcv
  have hz : f {u,v} v=0 := hf.2.2.1 _ _ (by simp)
  have hc : ∀ i : Fin 2, (![∅,{u},{u,v}] : Fin 3 → Finset (Fin n)) i.castSucc⊆![∅,{u},{u,v}] i.succ := by
    intro i; fin_cases i <;> simp
  have h := hb 2 ![∅,{u},{u,v}] ![u,v] hc
  simp [Fin.sum_univ_succ,fits_empty hf,fits_self hf,hs,hz] at h
  omega

lemma singleton_comparison {n D B : Nat} {g : Fin n → Fin n → Prop}
    {f : Finset (Fin n) → Fin n → Nat} (hf : Fits D g f) (hb : Bounds f B)
    (u v c j : Fin n) (hu : g u c) (hv : g v c) :
    f {u} j ≤ f {v} j+(B-2*D) := by
  have hcc : c∈centers g {u,v} := by simp [centers,hu,hv]
  have hs : f {u,v} c=D := hf.2.1 _ _ hcc
  have hz : f (insert c {u,v}) c=0 := hf.2.2.1 _ _ (by simp)
  have hc : ∀ i : Fin 3, (![∅,{u},{u,v},insert c {u,v}] : Fin 4 → Finset (Fin n)) i.castSucc
      ⊆![∅,{u},{u,v},insert c {u,v}] i.succ := by
    intro i; fin_cases i <;> simp
  have h := hb 3 ![∅,{u},{u,v},insert c {u,v}] ![u,j,c] hc
  have h1 : f {u,v} j≤f {u} j := hf.2.2.2 _ _ (by simp) _
  have h2 : f {u,v} j≤f {v} j := hf.2.2.2 _ _ (by simp) _
  simp [Fin.sum_univ_succ,fits_empty hf,fits_self hf,hs,hz] at h
  omega

lemma rate_bound {r e : Nat} (v : Fin (r+1) → Nat) (h0 : v 0=0)
    (hs : ∀ i : Fin r, v i.succ≤v i.castSucc+e) : v (Fin.last r)≤r*e := by
  have all (k : Fin (r+1)) : v k≤k.val*e := by
    refine Fin.induction ?_ (fun i ih => ?_) k
    · simpa [h0]
    · have h := hs i
      simp only [Fin.val_castSucc] at ih
      simp only [Fin.val_succ,Nat.add_mul,Nat.one_mul]
      omega
  exact all (Fin.last r)

lemma necessary {n D B : Nat} (g : Fin n → Fin n → Prop) (sym : Symmetric g)
    (f : Finset (Fin n) → Fin n → Nat) (hf : Fits D g f) (hb : Bounds f B) :
    Tests D g B := by
  refine ⟨necessary_one hf hb,necessary_two hf hb,fun r p hadj hpath => ?_⟩
  have h0 : f {p 0} (p 0)=0 := fits_self hf _
  have hc : p 0∈centers g {p (Fin.last r)} := by simp [centers,sym hadj]
  have hend : f {p (Fin.last r)} (p 0)=D := hf.2.1 _ _ hc
  have hs : ∀ i : Fin r, f {p i.succ} (p 0)≤f {p i.castSucc} (p 0)+(B-2*D) := by
    intro i
    obtain ⟨c,ha,hb'⟩ := hpath i
    exact singleton_comparison hf hb _ _ c _ hb' ha
  have h := rate_bound (fun k => f {p k} (p 0)) h0 hs
  simpa [hend] using h

end PEqualNP.Outside.L_meta_49525_aux


namespace PEqualNP.Outside.L_meta_49525_aux
open scoped Classical

def Walk {n : Nat} (g : Fin n → Fin n → Prop) {r : Nat} (p : Fin (r+1) → Fin n) : Prop :=
  ∀ i : Fin r, ∃ c, g (p i.castSucc) c ∧ g (p i.succ) c
def Costs {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop) (u j : Fin n) : Set Nat :=
  {v | v=D ∨ ∃ (r : Nat) (p : Fin (r+1) → Fin n), p 0=u ∧ p (Fin.last r)=j ∧ Walk g p ∧ v=r*e}
noncomputable def shortest {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop) (u j : Fin n) : Nat :=
  sInf (Costs D e g u j)

lemma shortest_mem {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop) (u j : Fin n) :
    shortest D e g u j ∈ Costs D e g u j :=
  Nat.sInf_mem ⟨D,Or.inl rfl⟩

lemma shortest_le {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop) (u j : Fin n) :
    shortest D e g u j≤D := Nat.sInf_le (Or.inl rfl)

lemma shortest_self {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop) (u : Fin n) :
    shortest D e g u u=0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact Or.inr ⟨0,fun _ => u,rfl,rfl,fun i => Fin.elim0 i,by simp⟩

lemma shortest_edge {n D B : Nat} (g : Fin n → Fin n → Prop) (ht : Tests D g B)
    (u j : Fin n) (huj : g u j) : shortest D (B-2*D) g u j=D := by
  apply le_antisymm (shortest_le _ _ _ _ _)
  rcases shortest_mem D (B-2*D) g u j with eq | ⟨r,p,h0,hl,hw,eq⟩
  · exact eq.ge
  · rw [eq]
    exact ht.2.2 r p (by simpa [h0,hl] using huj) hw

lemma shortest_lip {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop)
    (u v c j : Fin n) (hu : g u c) (hv : g v c) :
    shortest D e g u j≤shortest D e g v j+e := by
  rcases shortest_mem D e g v j with eq | ⟨r,p,h0,hl,hw,eq⟩
  · rw [eq]; exact (shortest_le _ _ _ _ _).trans (Nat.le_add_right _ _)
  · let q : Fin (r+2) → Fin n := Fin.cons u p
    have hq : Walk g q := by
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [q,Fin.castSucc_zero,Fin.succ_zero_eq_one,Fin.cons_zero,Fin.cons_one,h0]
        exact ⟨c,hu,hv⟩
      · simpa only [q,Fin.castSucc_succ,Fin.cons_succ] using hw k
    have hlast : q (Fin.last (r+1))=j := by simpa [q] using hl
    apply Nat.sInf_le
    refine Or.inr ⟨r+1,q,rfl,hlast,hq,?_⟩
    rw [eq,Nat.add_mul,Nat.one_mul]

def ValidA {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop)
    (A : Fin n → Fin n → Nat) : Prop :=
  (∀ u j, A u j≤D) ∧ (∀ u, A u u=0) ∧ (∀ u j, g u j → A u j=D) ∧
  ∀ u v c j, g u c → g v c → A u j≤A v j+e

lemma shortest_valid {n D B : Nat} (g : Fin n → Fin n → Prop) (ht : Tests D g B) :
    ValidA D (B-2*D) g (shortest D (B-2*D) g) :=
  ⟨shortest_le _ _ _,shortest_self _ _ _,shortest_edge g ht,shortest_lip _ _ _⟩

noncomputable def neighbors {n : Nat} (g : Fin n → Fin n → Prop) (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => g u c)
noncomputable def centerMatrix {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop)
    (A : Fin n → Fin n → Nat) (c j : Fin n) : Nat :=
  D-(neighbors g c).sup (fun u => D-A u j)

def ValidW {n : Nat} (D e : Nat) (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) : Prop :=
  (∀ c j, W c j≤D) ∧ (∀ c, W c c=D) ∧
  (∀ u c j, g u c → W c j≤A u j) ∧
  ∀ u c j, g u c → A u j≤W c j+e

lemma centerMatrix_valid {n D e : Nat} (g : Fin n → Fin n → Prop)
    (A : Fin n → Fin n → Nat) (ha : ValidA D e g A) :
    ValidW D e g A (centerMatrix D g A) := by
  have sup_le (c j : Fin n) : (neighbors g c).sup (fun u => D-A u j)≤D :=
    Finset.sup_le (fun _ _ => Nat.sub_le _ _)
  refine ⟨fun _ _ => Nat.sub_le _ _,fun c => ?_,fun u c j hu => ?_,fun u c j hu => ?_⟩
  · have hzero : (neighbors g c).sup (fun u => D-A u c)=0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro u hu
      have gu : g u c := by simpa [neighbors] using hu
      simp [ha.2.2.1 u c gu]
    simp [centerMatrix,hzero]
  · have hu' : u∈neighbors g c := by simp [neighbors,hu]
    have hle := Finset.le_sup (f := fun v => D-A v j) hu'
    have hb := ha.1 u j
    have hs := sup_le c j
    unfold centerMatrix
    omega
  · have hs := sup_le c j
    have hb := ha.1 u j
    have hle : (neighbors g c).sup (fun v => D-A v j)≤D+e-A u j := by
      apply Finset.sup_le
      intro v hv
      have gv : g v c := by simpa [neighbors] using hv
      have hl := ha.2.2.2 u v c j hu gv
      have hvb := ha.1 v j
      omega
    unfold centerMatrix
    omega

end PEqualNP.Outside.L_meta_49525_aux


namespace PEqualNP.Outside.L_meta_49525_aux
open scoped Classical

noncomputable def extension {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (x : Finset (Fin n)) (j : Fin n) : Nat := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  exact if x=∅ then D else if x.card=1 then x.sup (fun u => A u j)
    else (centers g x).sup (fun c => W c j)

lemma extension_singleton {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (u j : Fin n) :
    extension D g A W {u} j=A u j := by simp [extension]

lemma extension_many {n : Nat} (D : Nat) (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (x : Finset (Fin n)) (h2 : 2≤x.card) (j : Fin n) :
    extension D g A W x j=(centers g x).sup (fun c => W c j) := by
  have hx : x≠∅ := by intro eq; subst x; simp at h2
  have hc : x.card≠1 := by omega
  simp [extension,hx,hc]

lemma extension_le {n D e : Nat} (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W)
    (x : Finset (Fin n)) (j : Fin n) : extension D g A W x j≤D := by
  unfold extension
  split
  · exact le_rfl
  · split
    · exact Finset.sup_le (fun u _ => ha.1 u j)
    · exact Finset.sup_le (fun c _ => hw.1 c j)

lemma extension_fit {n D e : Nat} (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W) :
    Fits D g (extension D g A W) := by
  refine ⟨extension_le g A W ha hw,?_,?_,?_⟩
  · intro x j hj
    by_cases hx : x=∅
    · simp [extension,hx]
    by_cases hc : x.card=1
    · obtain ⟨u,eqx⟩ := Finset.card_eq_one.mp hc
      subst x
      have guj : g u j := (mem_centers g {u} j).mp hj u (by simp)
      rw [extension_singleton]
      exact ha.2.2.1 u j guj
    · have h : D≤(centers g x).sup (fun c => W c j) := by
        have h' := Finset.le_sup (f := fun c => W c j) hj
        simpa [hw.2.1 j] using h'
      have hb := extension_le g A W ha hw x j
      simp only [extension,if_neg hx,if_neg hc] at hb ⊢
      omega
  · intro x j hj
    by_cases hx : x=∅
    · subst x; simp at hj
    by_cases hc : x.card=1
    · obtain ⟨u,eqx⟩ := Finset.card_eq_one.mp hc
      subst x
      have eqj : j=u := Finset.mem_singleton.mp hj
      subst j
      rw [extension_singleton]
      exact ha.2.1 u
    · simp only [extension,if_neg hx,if_neg hc]
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro c hcx
      have guc := (mem_centers g x c).mp hcx j hj
      have h := hw.2.2.1 j c j guc
      simpa [ha.2.1 j] using h
  · intro x y hxy j
    by_cases hx : x=∅
    · subst x
      simpa [extension] using extension_le g A W ha hw y j
    by_cases hc : x.card=1
    · obtain ⟨u,eqx⟩ := Finset.card_eq_one.mp hc
      subst x
      rw [extension_singleton]
      have hu : u∈y := hxy (by simp)
      by_cases hy1 : y.card=1
      · obtain ⟨v,eqy⟩ := Finset.card_eq_one.mp hy1
        subst y
        have eq : u=v := Finset.mem_singleton.mp hu
        subst u
        rw [extension_singleton]
      · have hyne : y≠∅ := by intro eq; subst y; simp at hu
        simp only [extension,if_neg hyne,if_neg hy1]
        apply Finset.sup_le
        intro c hcy
        exact hw.2.2.1 u c j ((mem_centers g y c).mp hcy u hu)
    · have h2x : 2≤x.card := by
        have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hx)
        omega
      have h2y : 2≤y.card := h2x.trans (Finset.card_le_card hxy)
      rw [extension_many D g A W x h2x,extension_many D g A W y h2y]
      exact Finset.sup_mono (centers_anti g hxy)

lemma centers_card_le {n L : Nat} (g : Fin n → Fin n → Prop)
    (bound : ∀ u v : Fin n, u≠v → (centers g {u,v}).card≤L)
    (x : Finset (Fin n)) (h2 : 2≤x.card) : (centers g x).card≤L := by
  obtain ⟨u,hu,v,hv,hne⟩ := Finset.one_lt_card.mp (by omega : 1<x.card)
  have hsub : {u,v}⊆x := by simp [Finset.insert_subset_iff,hu,hv]
  exact (Finset.card_le_card (centers_anti g hsub)).trans (bound u v hne)

lemma extension_le_A {n D e : Nat} (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W)
    (x : Finset (Fin n)) (u : Fin n) (hu : u∈x) (j : Fin n) :
    extension D g A W x j≤A u j := by
  have h := (extension_fit g A W ha hw).2.2.2 {u} x (by simpa using hu) j
  simpa only [extension_singleton] using h

lemma extension_small_drop {n D e : Nat} (g : Fin n → Fin n → Prop)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W)
    (x y : Finset (Fin n)) (hne : x.Nonempty) (hxy : x⊆y) (h2y : 2≤y.card)
    (hyc : (centers g y).Nonempty) (j : Fin n) :
    extension D g A W x j≤extension D g A W y j+e := by
  obtain ⟨u,hu⟩ := hne
  obtain ⟨c,hc⟩ := hyc
  have h1 := extension_le_A g A W ha hw x u hu j
  have h2 : W c j≤extension D g A W y j := by
    rw [extension_many D g A W y h2y]
    exact Finset.le_sup (f := fun c => W c j) hc
  have h3 := hw.2.2.2 u c j ((mem_centers g y c).mp hc u (hxy hu))
  omega

end PEqualNP.Outside.L_meta_49525_aux


namespace PEqualNP.Outside.L_meta_49525_aux
open scoped Classical

lemma bounds_of_potential {n H : Nat} (f : Finset (Fin n) → Fin n → Nat)
    (anti : ∀ x y, x⊆y → ∀ j, f y j≤f x j)
    (R : Finset (Fin n) → Int)
    (rb : ∀ x, 0≤R x ∧ R x≤(H : Int))
    (drop : ∀ x y, x⊆y → ∀ j, (f x j : Int)-(f y j : Int)≤R y-R x) :
    Bounds f H := by
  intro l p a hp
  have hz : (((∑ i : Fin l, (f (p i.castSucc) (a i)-f (p i.succ) (a i) : Nat)) : Nat) : Int)≤(H : Int) := by
    rw [Nat.cast_sum]
    calc
      (∑ i : Fin l, ((f (p i.castSucc) (a i)-f (p i.succ) (a i) : Nat) : Int)) =
          ∑ i : Fin l, ((f (p i.castSucc) (a i) : Int)-(f (p i.succ) (a i) : Int)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.cast_sub (anti _ _ (hp i) _)
      _ ≤ ∑ i : Fin l, (R (p i.succ)-R (p i.castSucc)) :=
        Finset.sum_le_sum (fun i _ => drop _ _ (hp i) _)
      _ = R (p (Fin.last l))-R (p 0) := by
        simpa only [neg_sub_neg] using sum_telescope_int (fun k => -R (p k))
      _ ≤ (H : Int) := by have := (rb (p (Fin.last l))).2; have := (rb (p 0)).1; omega
  exact_mod_cast hz

noncomputable def potential {n : Nat} (D L e : Nat) (g : Fin n → Fin n → Prop)
    (x : Finset (Fin n)) : Int :=
  if x=∅ then 0 else if x.card=1 then D
  else if centers g x=∅ then 2*(D : Int)+(L : Int)*(e : Int)
  else (D : Int)+((L : Int)+1-((centers g x).card : Int))*(e : Int)

lemma card_two {n : Nat} (x : Finset (Fin n)) (hne : x≠∅) (h1 : x.card≠1) : 2≤x.card := by
  have h := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  omega

lemma potential_bounds {n D L e : Nat} (g : Fin n → Fin n → Prop)
    (bound : ∀ u v : Fin n, u≠v → (centers g {u,v}).card≤L) (x : Finset (Fin n)) :
    (if x=∅ then (0 : Int) else (D : Int))≤potential D L e g x ∧
      potential D L e g x≤((2*D+L*e : Nat) : Int) := by
  have hK : ((2*D+L*e : Nat) : Int)=2*(D : Int)+(L : Int)*(e : Int) := by push_cast; ring
  rw [hK]
  have hmul : 0≤(L : Int)*(e : Int) := mul_nonneg (Int.ofNat_nonneg L) (Int.ofNat_nonneg e)
  by_cases hx : x=∅
  · simp only [potential,if_pos hx]
    constructor <;> nlinarith [Int.ofNat_nonneg D]
  by_cases h1 : x.card=1
  · simp only [potential,if_neg hx,if_pos h1]
    constructor <;> nlinarith [Int.ofNat_nonneg D]
  by_cases hc : centers g x=∅
  · simp only [potential,if_neg hx,if_neg h1,if_pos hc]
    constructor <;> nlinarith [Int.ofNat_nonneg D]
  · have h2 := card_two x hx h1
    have hcl : ((centers g x).card : Int)≤(L : Int) := by
      exact_mod_cast centers_card_le g bound x h2
    have hcp : (1 : Int)≤((centers g x).card : Int) := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hc)
      exact_mod_cast this
    have ha : 0≤((L : Int)+1-((centers g x).card : Int))*(e : Int) :=
      mul_nonneg (by omega) (Int.ofNat_nonneg e)
    have hb : 0≤(((centers g x).card : Int)-1)*(e : Int) :=
      mul_nonneg (by omega) (Int.ofNat_nonneg e)
    simp only [potential,if_neg hx,if_neg h1,if_neg hc]
    constructor <;> nlinarith [Int.ofNat_nonneg D]

lemma potential_drop {n D L e : Nat} (g : Fin n → Fin n → Prop)
    (bound : ∀ u v : Fin n, u≠v → (centers g {u,v}).card≤L)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W)
    (x y : Finset (Fin n)) (hxy : x⊆y) (j : Fin n) :
    (extension D g A W x j : Int)-(extension D g A W y j : Int)≤
      potential D L e g y-potential D L e g x := by
  have hD := Int.ofNat_nonneg D
  have he := Int.ofNat_nonneg e
  have hmul : 0≤(L : Int)*(e : Int) := mul_nonneg (Int.ofNat_nonneg L) he
  have fbound (z : Finset (Fin n)) : (extension D g A W z j : Int)≤(D : Int) := by
    exact_mod_cast extension_le g A W ha hw z j
  by_cases hx : x=∅
  · subst x
    by_cases hy : y=∅
    · subst y; simp
    have hR := (potential_bounds (D := D) (e := e) g bound y).1
    rw [if_neg hy] at hR
    have hz := Int.ofNat_nonneg (extension D g A W y j)
    have hRx : potential D L e g ∅=0 := rfl
    have hfx : extension D g A W ∅ j=D := by simp [extension]
    rw [hRx,hfx]
    nlinarith
  have hy : y≠∅ := by
    intro eq; subst y
    exact hx (Finset.subset_empty.mp hxy)
  by_cases h1x : x.card=1
  · have hRx : potential D L e g x=(D : Int) := by simp [potential,hx,h1x]
    by_cases h1y : y.card=1
    · have eq : x=y := Finset.eq_of_subset_of_card_le hxy (by omega)
      subst y; simp
    have h2y := card_two y hy h1y
    by_cases hc : centers g y=∅
    · have fy : extension D g A W y j=0 := by rw [extension_many D g A W y h2y,hc]; simp
      have hRy : potential D L e g y=2*(D : Int)+(L : Int)*(e : Int) := by simp [potential,hy,h1y,hc]
      rw [fy,hRx,hRy]
      have := fbound x
      nlinarith
    · have hd : (extension D g A W x j : Int)≤(extension D g A W y j : Int)+(e : Int) := by
        exact_mod_cast extension_small_drop g A W ha hw x y
          (Finset.nonempty_iff_ne_empty.mpr hx) hxy h2y (Finset.nonempty_iff_ne_empty.mpr hc) j
      have hcl : ((centers g y).card : Int)≤(L : Int) := by
        exact_mod_cast centers_card_le g bound y h2y
      have hm : 0≤((L : Int)-((centers g y).card : Int))*(e : Int) :=
        mul_nonneg (by omega) he
      rw [hRx]
      simp only [potential,if_neg hy,if_neg h1y,if_neg hc]
      nlinarith
  have h2x := card_two x hx h1x
  have h2y := h2x.trans (Finset.card_le_card hxy)
  have h1y : y.card≠1 := by omega
  have csub := centers_anti g hxy
  by_cases hcx : centers g x=∅
  · have hcy : centers g y=∅ := Finset.subset_empty.mp (hcx ▸ csub)
    have fx : extension D g A W x j=0 := by rw [extension_many D g A W x h2x,hcx]; simp
    have fy : extension D g A W y j=0 := by rw [extension_many D g A W y h2y,hcy]; simp
    simp [fx,fy,potential,hx,hy,h1x,h1y,hcx,hcy]
  by_cases hcy : centers g y=∅
  · have fy : extension D g A W y j=0 := by rw [extension_many D g A W y h2y,hcy]; simp
    have hcp : (1 : Int)≤((centers g x).card : Int) := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hcx)
      exact_mod_cast this
    have hm : 0≤(((centers g x).card : Int)-1)*(e : Int) :=
      mul_nonneg (by omega) he
    have hf := fbound x
    rw [fy]
    simp only [potential,if_neg hx,if_neg hy,if_neg h1x,if_neg h1y,if_neg hcx,if_pos hcy]
    nlinarith
  by_cases ceq : centers g x=centers g y
  · have feq : extension D g A W x j=extension D g A W y j := by
      rw [extension_many D g A W x h2x,extension_many D g A W y h2y,ceq]
    simp [feq,potential,hx,hy,h1x,h1y,hcx,hcy,ceq]
  · have hcard : (centers g y).card<(centers g x).card := by
      have hle := Finset.card_le_card csub
      have hne : (centers g y).card≠(centers g x).card := by
        intro eq
        exact ceq (Finset.eq_of_subset_of_card_le csub (by omega)).symm
      omega
    have hcardZ : ((centers g y).card : Int)<((centers g x).card : Int) := by exact_mod_cast hcard
    have hm : 0≤(((centers g x).card : Int)-((centers g y).card : Int)-1)*(e : Int) :=
      mul_nonneg (by omega) he
    have hd : (extension D g A W x j : Int)≤(extension D g A W y j : Int)+(e : Int) := by
      exact_mod_cast extension_small_drop g A W ha hw x y
        (Finset.nonempty_iff_ne_empty.mpr hx) hxy h2y (Finset.nonempty_iff_ne_empty.mpr hcy) j
    simp only [potential,if_neg hx,if_neg hy,if_neg h1x,if_neg h1y,if_neg hcx,if_neg hcy]
    nlinarith

lemma extension_budget {n D L e : Nat} (g : Fin n → Fin n → Prop)
    (bound : ∀ u v : Fin n, u≠v → (centers g {u,v}).card≤L)
    (A W : Fin n → Fin n → Nat) (ha : ValidA D e g A) (hw : ValidW D e g A W) :
    Bounds (extension D g A W) (2*D+L*e) := by
  apply bounds_of_potential (extension D g A W) (extension_fit g A W ha hw).2.2.2
    (potential D L e g)
  · intro x
    have h := potential_bounds (D := D) (e := e) g bound x
    refine ⟨?_,h.2⟩
    by_cases hx : x=∅
    · simpa only [if_pos hx] using h.1
    · have hD := Int.ofNat_nonneg D
      rw [if_neg hx] at h
      omega
  · exact potential_drop g bound A W ha hw

end PEqualNP.Outside.L_meta_49525_aux


namespace PEqualNP.Outside.L_meta_49525_aux
open scoped Classical

lemma bounds_mono {n H H' : Nat} {f : Finset (Fin n) → Fin n → Nat}
    (hb : Bounds f H) (hh : H≤H') : Bounds f H' :=
  fun l p a hp => (hb l p a hp).trans hh

lemma edgeless {n D : Nat} (g : Fin n → Fin n → Prop) (noedge : ∀ u v, ¬g u v) :
    ∃ A W : Fin n → Fin n → Nat,
      Fits D g (extension D g A W) ∧ Bounds (extension D g A W) D := by
  let A : Fin n → Fin n → Nat := fun _ _ => 0
  let W : Fin n → Fin n → Nat := fun _ _ => D
  have ha : ValidA D 0 g A := by
    refine ⟨fun _ _ => Nat.zero_le _,fun _ => rfl,?_,?_⟩
    · intro u v h; exact (noedge u v h).elim
    · intro u v c j h; exact (noedge u c h).elim
  have hw : ValidW D 0 g A W := by
    refine ⟨fun _ _ => le_rfl,fun _ => rfl,?_,?_⟩
    · intro u c j h; exact (noedge u c h).elim
    · intro u c j h; exact (noedge u c h).elim
  have hf := extension_fit g A W ha hw
  have zero (x : Finset (Fin n)) (hx : x≠∅) (j : Fin n) :
      extension D g A W x j=0 := by
    have hc : centers g x=∅ := by
      ext c
      constructor
      · intro hc
        obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr hx
        exact (noedge u c ((mem_centers g x c).mp hc u hu)).elim
      · intro hc
        simp at hc
    simp [extension,hx,hc,A]
  let R : Finset (Fin n) → Int := fun x => if x=∅ then 0 else D
  refine ⟨A,W,hf,bounds_of_potential (extension D g A W) hf.2.2.2 R ?_ ?_⟩
  · intro x
    by_cases hx : x=∅ <;> simp [R,hx]
  · intro x y hxy j
    by_cases hx : x=∅
    · subst x
      by_cases hy : y=∅
      · subst y; simp
      · rw [zero y hy j]
        simp [extension,R,hy]
    · have hy : y≠∅ := by
        intro eq; subst y
        exact hx (Finset.subset_empty.mp hxy)
      rw [zero x hx j,zero y hy j]
      simp [R,hx,hy]

lemma budget_compare (D L B : Nat) (hB : 2*D≤B) :
    2*D+L*(B-2*D)≤B+(L-1)*(B-2*D) := by
  have eqB : B=2*D+(B-2*D) := by omega
  cases L with
  | zero => simpa using hB
  | succ L =>
    simp only [Nat.add_sub_cancel,Nat.succ_sub_one,Nat.succ_mul]
    omega

lemma upper {n D L B : Nat} (g : Fin n → Fin n → Prop)
    (bound : ∀ u v : Fin n, u≠v → (centers g {u,v}).card≤L) (ht : Tests D g B) :
    ∃ A W : Fin n → Fin n → Nat,
      Fits D g (extension D g A W) ∧ Bounds (extension D g A W) (B+(L-1)*(B-2*D)) := by
  by_cases hn : n=0
  · subst n
    refine ⟨fun _ _ => 0,fun _ _ => 0,?_,?_⟩
    · exact ⟨fun _ j => Fin.elim0 j,fun _ j => Fin.elim0 j,
        fun _ j => Fin.elim0 j,fun _ _ _ j => Fin.elim0 j⟩
    · intro l p a hp
      cases l with
      | zero => simp
      | succ k => exact Fin.elim0 (a 0)
  by_cases hedge : ∃ u v, g u v
  · let A := shortest D (B-2*D) g
    let W := centerMatrix D g A
    have ha : ValidA D (B-2*D) g A := shortest_valid g ht
    have hw : ValidW D (B-2*D) g A W := centerMatrix_valid g A ha
    exact ⟨A,W,extension_fit g A W ha hw,
      bounds_mono (extension_budget g bound A W ha hw) (budget_compare D L B (ht.2.1 hedge))⟩
  · obtain ⟨A,W,hf,hb⟩ := edgeless (D := D) g (fun u v h => hedge ⟨u,v,h⟩)
    exact ⟨A,W,hf,bounds_mono hb ((ht.1 (Nat.pos_of_ne_zero hn)).trans (Nat.le_add_right _ _))⟩

end PEqualNP.Outside.L_meta_49525_aux


theorem PEqualNP.Outside.L_meta_49525 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n D L : Nat) (g : Fin n → Fin n → Prop),
  Symmetric g → (∀ i, ¬g i i) →
  let X := Finset (Fin n)
  let centers := fun (x : X) => (Finset.univ : X).filter (fun c => ∀ u ∈ x, g u c)
  (∀ u v : Fin n, u ≠ v → (centers {u,v}).card ≤ L) →
  let fit := fun (f : X → Fin n → Nat) =>
    (∀ x j, f x j ≤ D) ∧ (∀ x j, j ∈ centers x → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
  let bounds := fun (f : X → Fin n → Nat) (H : Nat) =>
    ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → Fin n),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
      Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ H
  let tests := fun (B : Nat) =>
    (0 < n → D ≤ B) ∧ ((∃ i j, g i j) → 2*D ≤ B) ∧
    ∀ (r : Nat) (p : Fin (r+1) → Fin n), g (p 0) (p (Fin.last r)) →
      (∀ i : Fin r, ∃ c, g (p i.castSucc) c ∧ g (p i.succ) c) →
      D ≤ r*(B-2*D)
  ∀ B : Nat,
    ((∃ f, fit f ∧ bounds f B) → tests B) ∧
    (tests B → ∃ A W : Fin n → Fin n → Nat,
      let f := fun (x : X) (j : Fin n) => if x = ∅ then D
        else if x.card = 1 then x.sup (fun u => A u j)
        else (centers x).sup (fun c => W c j)
      fit f ∧ bounds f (B+(L-1)*(B-2*D))) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n D L g sym irref
  dsimp only
  intro bound B
  constructor
  · rintro ⟨f,hf,hb⟩
    exact PEqualNP.Outside.L_meta_49525_aux.necessary g sym f hf hb
  · intro ht
    refine PEqualNP.Outside.L_meta_49525_aux.upper g ?_ ht
    intro u v hne
    convert bound u v hne using 1
    congr 1 <;> ext c <;> simp [PEqualNP.Outside.L_meta_49525_aux.centers]
