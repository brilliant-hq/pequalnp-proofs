import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1209

namespace Worker1209Path

abbrev V (L : Nat) := Fin (3*L+1)
abbrev T (L : Nat) := Fin (2*L+1)

def p {L : Nat} (k : Fin L) : V L := ⟨3*k.val, by have := k.isLt; omega⟩
def b {L : Nat} (k : Fin L) : V L := ⟨3*k.val+1, by have := k.isLt; omega⟩
def u {L : Nat} (k : Fin L) : V L := ⟨3*k.val+2, by have := k.isLt; omega⟩
def q {L : Nat} (k : Fin L) : V L := ⟨3*k.val+3, by have := k.isLt; omega⟩
def last (L : Nat) : V L := ⟨3*L, by omega⟩
def first (L : Nat) : V L := ⟨0, by omega⟩

def arc {L : Nat} (k : Fin L) : Finset (V L × V L) := {(p k,q k),(q k,b k),(b k,p k),(u k,p k)}
def D (L : Nat) : Finset (V L × V L) := Finset.univ.biUnion arc

theorem mem_arc {L} (k : Fin L) (e : V L × V L) :
    e ∈ arc k ↔ e = (p k,q k) ∨ e = (q k,b k) ∨ e = (b k,p k) ∨ e = (u k,p k) := by
  simp [arc]

theorem mem_D_arc {L} (e : V L × V L) :
    e ∈ D L ↔ ∃ k : Fin L, e ∈ arc k := by simp [D]

theorem mem_D {L} (i j : V L) :
    (i,j) ∈ D L ↔ ∃ k : Fin L,
      (i=p k ∧ j=q k) ∨ (i=q k ∧ j=b k) ∨ (i=b k ∧ j=p k) ∨ (i=u k ∧ j=p k) := by
  simp [D,arc]

theorem D_card (L : Nat) : (D L).card ≤ 4*L := by
  rw [D]
  calc
    _ ≤ ∑ k : Fin L, (arc k).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin L, (4 : Nat) := Finset.sum_le_sum fun _ _ => Finset.card_le_four
    _ = 4*L := by simp [Nat.mul_comm]

theorem D_loopless {L} (i : V L) : (i,i) ∉ D L := by
  intro h
  obtain ⟨k,h1|h2|h3|h4⟩ := (mem_D i i).mp h
  all_goals
    obtain ⟨h,h'⟩ := ‹_ ∧ _›
    have d := congrArg Fin.val (h.symm.trans h')
    simp [p,q,b,u] at d

def zeroTime (L : Nat) : T L := ⟨0, by omega⟩
def oddTime {L : Nat} (k : Fin L) : T L := ⟨2*k.val+1, by have := k.isLt; omega⟩
def evenTime {L : Nat} (k : Fin L) : T L := ⟨2*k.val+2, by have := k.isLt; omega⟩
def lastTime (L : Nat) : T L := ⟨2*L, by omega⟩

def bag {L : Nat} (t : T L) : Finset (V L) :=
  if h : t.val = 0 then {first L} else
    if h' : t.val % 2 = 1 then
      let k : Fin L := ⟨t.val / 2, by have := t.isLt; omega⟩
      {p k,u k}
    else
      let k : Fin L := ⟨t.val / 2 - 1, by have := t.isLt; omega⟩
      {p k,q k,b k}

theorem bag_zero (L : Nat) : bag (zeroTime L) = {first L} := by simp [bag,zeroTime]
theorem bag_odd {L} (k : Fin L) : bag (oddTime k) = {p k,u k} := by
  have hk : (2*k.val+1)/2 = k.val := by omega
  simp [bag,oddTime,hk]
theorem bag_even {L} (k : Fin L) : bag (evenTime k) = {p k,q k,b k} := by
  simp [bag,evenTime]

theorem times {L} (t : T L) :
    t=zeroTime L ∨ (∃ k : Fin L, t=oddTime k) ∨ (∃ k : Fin L, t=evenTime k) := by
  have ht := t.isLt
  by_cases h : t.val=0
  · left; apply Fin.ext; exact h
  · right
    by_cases hh : t.val % 2=1
    · exact Or.inl ⟨⟨t.val/2, by omega⟩,Fin.ext (by simp [oddTime]; omega)⟩
    · exact Or.inr ⟨⟨t.val/2-1, by omega⟩,Fin.ext (by simp [evenTime]; omega)⟩

theorem bag_card {L} (t : T L) : (bag t).card ≤ 3 := by
  obtain h|⟨k,h⟩|⟨k,h⟩ := times t
  · rw [h,bag_zero]; simp
  · rw [h,bag_odd]; exact Finset.card_le_two.trans (by decide)
  · rw [h,bag_even]; exact Finset.card_le_three

def arrival {L : Nat} (i : V L) : Nat := 2*(i.val/3) + if i.val % 3 = 0 then 0 else 3-i.val % 3
def departure {L : Nat} (i : V L) : Nat := 2*(i.val/3) + if i.val % 3 = 0 then 2 else 3-i.val % 3

theorem mem_bag_interval {L} (t : T L) (i : V L) :
    i ∈ bag t ↔ arrival i ≤ t.val ∧ t.val ≤ departure i := by
  obtain ht|⟨k,ht⟩|⟨k,ht⟩ := times t
  · rw [ht,bag_zero]
    simp only [Finset.mem_singleton,Fin.ext_iff,first,zeroTime,arrival,departure]
    split <;> omega
  · rw [ht,bag_odd]
    simp only [Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,p,u,oddTime,arrival,departure]
    split <;> omega
  · rw [ht,bag_even]
    simp only [Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,p,q,b,evenTime,arrival,departure]
    split <;> omega

theorem bag_has_vertex {L} (i : V L) : ∃ t : T L, i ∈ bag t := by
  have h := i.isLt
  refine ⟨⟨arrival i, by unfold arrival; split <;> omega⟩,?_⟩
  apply (mem_bag_interval _ _).mpr
  simp only [le_refl,true_and,arrival,departure]
  split <;> omega

theorem bag_has_edge {L} (i j : V L) (edge : (i,j) ∈ D L) :
    ∃ t : T L, i ∈ bag t ∧ j ∈ bag t := by
  obtain ⟨k,h1|h2|h3|h4⟩ := (mem_D i j).mp edge
  · obtain ⟨rfl,rfl⟩ := h1; exact ⟨evenTime k, by simp [bag_even]⟩
  · obtain ⟨rfl,rfl⟩ := h2; exact ⟨evenTime k, by simp [bag_even]⟩
  · obtain ⟨rfl,rfl⟩ := h3; exact ⟨evenTime k, by simp [bag_even]⟩
  · obtain ⟨rfl,rfl⟩ := h4; exact ⟨oddTime k, by simp [bag_odd]⟩

theorem bag_convex {L} (i : V L) (s t r : T L)
    (st : s ≤ t) (tr : t ≤ r) (hs : i ∈ bag s) (hr : i ∈ bag r) : i ∈ bag t := by
  change s.val ≤ t.val at st
  change t.val ≤ r.val at tr
  have hs' := (mem_bag_interval s i).mp hs
  have hr' := (mem_bag_interval r i).mp hr
  exact (mem_bag_interval t i).mpr ⟨hs'.1.trans st, tr.trans hr'.2⟩

theorem bag_terminal (L : Nat) :
    ∃ t : T L, last L ∈ bag t ∧ ∀ s : T L, s ≤ t := by
  refine ⟨lastTime L, (mem_bag_interval _ _).mpr ?_, ?_⟩
  · simp [arrival,departure,last,lastTime]
  · intro s
    have h := s.isLt
    change s.val ≤ 2*L
    omega

theorem path_cert (L : Nat) :
    ∃ (l : Nat) (path : Fin l → Finset (V L)),
      l ≤ 2*(3*L+1)+1 ∧ (∀ t, (path t).card ≤ 3) ∧ (∀ i, ∃ t, i ∈ path t) ∧
      (∀ i j, (i,j) ∈ D L → ∃ t, i ∈ path t ∧ j ∈ path t) ∧
      (∀ i s t r, s ≤ t → t ≤ r → i ∈ path s → i ∈ path r → i ∈ path t) ∧
      (∃ t, last L ∈ path t ∧ ∀ r, r ≤ t) :=
  ⟨2*L+1,bag,by omega,bag_card,bag_has_vertex,bag_has_edge,bag_convex,bag_terminal L⟩

end Worker1209Path

namespace Worker1209LocalCount


def step (d old new tag free : Bool) : Prop :=
  (d = true → tag = false) ∧
  (old = true → new = true) ∧
  (d = false → new = true → tag = true) ∧
  (d = false → tag = true → old = true) ∧
  (free = true → old = true)


theorem cold : ∀ d old tag free : Bool,
    step d old false tag free ↔ old=false ∧ tag=false ∧ free=false := by
  unfold step
  decide +kernel

theorem hotHot : ∀ d tag free : Bool,
    step d true true tag free ↔ tag = !d := by
  unfold step
  decide +kernel

theorem hotCold : ∀ d tag free : Bool,
    step d false true tag free ↔ d=true ∧ tag=false ∧ free=false := by
  unfold step
  decide +kernel

theorem hot : ∀ d old tag free : Bool,
    step d old true tag free ↔
      (old=true ∧ tag= !d) ∨
      (old=false ∧ d=true ∧ tag=false ∧ free=false) := by
  unfold step
  decide +kernel

noncomputable def count {α : Type*} [Fintype α] (P : α → Prop)  : Nat := by
  classical
  exact ((Finset.univ : Finset α).filter P).card

def coldAux : Finset (Bool × Bool) := {(false,false)}
def hotAux (d : Bool) : Finset (Bool × Bool) :=
  Finset.univ.filter (fun w => w.1 = !d)

theorem hotAuxCard (d : Bool) : (hotAux d).card = 2 := by
  cases d <;> decide +kernel

theorem countCold {α : Type*} [Fintype α] (P : α → Prop) 
    (s : α → Bool) (d : Bool) :
    count (fun w : α × (Bool × Bool) => P w.1 ∧ step d (s w.1) false w.2.1 w.2.2) =
    count (fun x => P x ∧ s x = false) := by
  classical
  let A : Finset α := Finset.univ.filter (fun x => P x ∧ s x = false)
  have eq : (Finset.univ.filter (fun w : α × (Bool × Bool) =>
    P w.1 ∧ step d (s w.1) false w.2.1 w.2.2)) = A ×ˢ coldAux := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product,A,coldAux,Finset.mem_singleton,cold]
    simp only [Prod.ext_iff]
    exact and_assoc.symm
  have a : count (fun w : α × (Bool × Bool) =>
      P w.1 ∧ step d (s w.1) false w.2.1 w.2.2) = (A ×ˢ coldAux).card := by
    unfold count
    apply congrArg Finset.card
    ext w
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
      (show w ∈ (Finset.univ.filter (fun w : α × (Bool × Bool) =>
          P w.1 ∧ step d (s w.1) false w.2.1 w.2.2)) ↔ w∈A ×ˢ coldAux from by rw [eq])
  rw [a,Finset.card_product]
  have c : coldAux.card=1 := by simp [coldAux]
  have ca : A.card=count (fun x=>P x ∧ s x=false) := by
    unfold count
    apply congrArg Finset.card
    ext x
    simp [A]
  rw [c,ca,Nat.mul_one]

theorem countHot {α : Type*} [Fintype α] (P : α → Prop) 
    (s : α → Bool) (d : Bool) :
    count (fun w : α × (Bool × Bool) => P w.1 ∧ step d (s w.1) true w.2.1 w.2.2) =
    2 * count (fun x => P x ∧ s x = true) +
      if d then count (fun x => P x ∧ s x = false) else 0 := by
  classical
  let A : Finset α := Finset.univ.filter (fun x => P x ∧ s x = true)
  let B : Finset α := Finset.univ.filter (fun x => P x ∧ s x = false)
  let C : Finset (Bool × Bool) := if d then coldAux else ∅
  have eq : (Finset.univ.filter (fun w : α × (Bool × Bool) =>
    P w.1 ∧ step d (s w.1) true w.2.1 w.2.2)) = (A ×ˢ hotAux d) ∪ (B ×ˢ C) := by
    ext w
    cases hh : d <;>
      simp [A,B,C,hot,hh,hotAux,coldAux,Prod.ext_iff] <;> tauto
  have dis : Disjoint (A ×ˢ hotAux d) (B ×ˢ C) := by
    rw [Finset.disjoint_left]
    intro w a b
    have ha := (Finset.mem_filter.mp (Finset.mem_product.mp a).1).2.2
    have hb := (Finset.mem_filter.mp (Finset.mem_product.mp b).1).2.2
    simp [ha] at hb
  have ea : count (fun w : α × (Bool × Bool) =>
      P w.1 ∧ step d (s w.1) true w.2.1 w.2.2) = ((A ×ˢ hotAux d) ∪ (B ×ˢ C)).card := by
    unfold count
    apply congrArg Finset.card
    ext w
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
      (show w ∈ (Finset.univ.filter (fun w : α × (Bool × Bool) =>
          P w.1 ∧ step d (s w.1) true w.2.1 w.2.2)) ↔ w∈(A ×ˢ hotAux d) ∪ (B ×ˢ C)
          from by rw [eq])
  have ca : A.card=count (fun x=>P x ∧ s x=true) := by
    unfold count
    apply congrArg Finset.card
    ext x
    simp [A]
  have cb : B.card=count (fun x=>P x ∧ s x=false) := by
    unfold count
    apply congrArg Finset.card
    ext x
    simp [B]
  rw [ea,Finset.card_union_of_disjoint dis,Finset.card_product,Finset.card_product,hotAuxCard,ca,cb]
  cases d <;> simp [C,coldAux,Nat.mul_comm]

theorem countStep {α : Type*} [Fintype α] (P : α → Prop) 
    (s : α → Bool) (d pin : Bool) :
    count (fun w : α × (Bool × Bool) => P w.1 ∧ step d (s w.1) pin w.2.1 w.2.2) =
    if pin then (2 * count (fun x => P x ∧ s x = true) +
      if d then count (fun x => P x ∧ s x = false) else 0)
    else count (fun x => P x ∧ s x = false) := by
  cases pin
  · simpa using countCold P s d
  · simpa using countHot P s d

end Worker1209LocalCount

namespace Worker1209Fiber
open Worker1209LocalCount

abbrev Timeline (n : ℕ) := Fin (3*n+1) → Bool

def atVal {n : ℕ} (y : Timeline n) (i : ℕ) : Bool :=
  if h : i < 3*n+1 then y ⟨i,h⟩ else false

@[local simp] theorem atVal_coord {n : ℕ} (y : Timeline n) (i : Fin (3*n+1)) :
    atVal y i.val = y i := by simp [atVal,i.isLt]

def Valid {n : ℕ} (d : Fin n → Bool) (y : Timeline n) : Prop :=
  ∀ k : Fin n, step (d k) (atVal y (3*k.val)) (atVal y (3*k.val+3))
    (atVal y (3*k.val+1)) (atVal y (3*k.val+2))

abbrev Fiber {n : ℕ} (d : Fin n → Bool) (pin : Bool) :=
  { y : Timeline n // Valid d y ∧ atVal y (3*n)=pin }

noncomputable def counter (n : ℕ) (d : Fin n → Bool) (pin : Bool) : ℕ := by
  classical
  exact count (fun y : Timeline n => Valid d y ∧ atVal y (3*n)=pin)

def pre {n : ℕ} (y : Timeline (n+1)) : Timeline n :=
  fun i => y ⟨i.val, by omega⟩
def post {n : ℕ} (y : Timeline (n+1)) : Fin 3 → Bool :=
  fun i => y ⟨3*n+1+i.val, by omega⟩
def pack {n : ℕ} (x : Timeline n) (z : Fin 3 → Bool) : Timeline (n+1) :=
  fun i => if h : i.val < 3*n+1 then x ⟨i.val,h⟩
    else z ⟨i.val-(3*n+1),by omega⟩

@[local simp] theorem pre_pack {n : ℕ} (x : Timeline n) (z : Fin 3→Bool) :
    pre (pack x z)=x := by
  funext i
  simp [pre,pack,i.isLt]

@[local simp] theorem post_pack {n : ℕ} (x : Timeline n) (z : Fin 3→Bool) :
    post (pack x z)=z := by
  funext i
  have ng : ¬ (3*n+1+i.val < 3*n+1) := by omega
  have eq : 3*n+1+i.val-(3*n+1)=i.val := by omega
  simp only [post,pack,dif_neg ng]
  congr 1
  exact Fin.ext eq

@[local simp] theorem pack_parts {n : ℕ} (y : Timeline (n+1)) :
    pack (pre y) (post y)=y := by
  funext i
  by_cases h : i.val<3*n+1
  · simp [pack,pre,h]
  · simp only [pack,dif_neg h,post]
    congr 1
    apply Fin.ext
    change 3*n+1+(i.val-(3*n+1))=i.val
    omega

theorem pre_at {n : ℕ} (y : Timeline (n+1)) (i : ℕ) (hi : i<3*n+1) :
    atVal (pre y) i=atVal y i := by
  have hj : i<3*(n+1)+1 := by omega
  simp [atVal,pre,hi,hj]

theorem post_at {n : ℕ} (y : Timeline (n+1)) (i : Fin 3) :
    atVal y (3*n+1+i.val)=post y i := by
  have hh : 3*n+1+i.val <3*(n+1)+1 := by omega
  simp [atVal,post,hh]

def tailPin (tag free pin : Bool) (i : Fin 3) : Bool :=
  if i.val=0 then tag else if i.val=1 then free else pin
@[local simp] theorem tailPin0 (a b c : Bool) : tailPin a b c 0=a := by simp [tailPin]
@[local simp] theorem tailPin1 (a b c : Bool) : tailPin a b c 1=b := by simp [tailPin]
@[local simp] theorem tailPin2 (a b c : Bool) : tailPin a b c 2=c := by simp [tailPin]

theorem pinVal {n : ℕ} (y : Timeline (n+1)) : atVal y (3*(n+1))=post y 2 := by
  have e : 3*(n+1) = 3*n+1+(2 : Fin 3).val := by omega
  rw [e,post_at]

theorem lastStage {n : ℕ} (d : Fin (n+1)→Bool) (y : Timeline (n+1)) :
    step (d (Fin.last n)) (atVal y (3*(Fin.last n).val))
      (atVal y (3*(Fin.last n).val+3))
      (atVal y (3*(Fin.last n).val+1))
      (atVal y (3*(Fin.last n).val+2))
    ↔ step (d (Fin.last n)) (atVal (pre y) (3*n)) (post y 2) (post y 0) (post y 1) := by
  have a : atVal y (3*n)=atVal (pre y) (3*n) := (pre_at y _ (by omega)).symm
  have b : atVal y (3*n+3)=post y 2 := by
    simpa [Nat.mul_add] using pinVal y
  have c : atVal y (3*n+1)=post y 0 := by simpa using post_at y 0
  have e : atVal y (3*n+2)=post y 1 := by
    simpa [Nat.add_assoc] using post_at y 1
  simp only [Fin.val_last,a,b,c,e]

theorem validParts {n : ℕ} (d : Fin (n+1)→Bool) (y : Timeline (n+1)) :
    Valid d y ↔ Valid (fun i : Fin n => d i.castSucc) (pre y) ∧
      step (d (Fin.last n)) (atVal (pre y) (3*n)) (post y 2) (post y 0) (post y 1) := by
  unfold Valid
  rw [Fin.forall_fin_succ']
  constructor
  · rintro ⟨h,z⟩
    refine ⟨?_,(lastStage d y).1 z⟩
    intro k
    simp only [Fin.val_castSucc] at h
    rw [pre_at y _ (by omega),pre_at y _ (by omega),pre_at y _ (by omega),pre_at y _ (by omega)]
    exact h k
  · rintro ⟨h,z⟩
    refine ⟨?_,(lastStage d y).2 z⟩
    intro k
    specialize h k
    rw [pre_at y _ (by omega),pre_at y _ (by omega),pre_at y _ (by omega),pre_at y _ (by omega)] at h
    exact h

abbrev Grown {n : ℕ} (d : Fin (n+1)→Bool) (pin : Bool) :=
  { w : Timeline n × (Bool × Bool) //
    Valid (fun i : Fin n => d i.castSucc) w.1 ∧
      step (d (Fin.last n)) (atVal w.1 (3*n)) pin w.2.1 w.2.2 }

def fiberEquiv {n : ℕ} (d : Fin (n+1)→Bool) (pin : Bool) :
    Fiber d pin ≃ Grown d pin where
  toFun y := ⟨(pre y.val, post y.val 0, post y.val 1), by
    obtain ⟨hd,hl⟩ := y.property
    obtain ⟨hv,hs⟩ := (validParts d y.val).1 hd
    have hp : post y.val 2=pin := (pinVal y.val).symm.trans hl
    rw [hp] at hs
    exact ⟨hv,hs⟩⟩
  invFun w := ⟨pack w.val.1 (tailPin w.val.2.1 w.val.2.2 pin), by
    constructor
    · apply (validParts d _).2
      simpa only [pre_pack,post_pack,tailPin0,tailPin1,tailPin2] using w.property
    · rw [pinVal,post_pack,tailPin2]⟩
  left_inv y := by
    apply Subtype.ext
    change pack (pre y.val) (tailPin (post y.val 0) (post y.val 1) pin) = y.val
    have e : tailPin (post y.val 0) (post y.val 1) pin = post y.val := by
      funext i
      fin_cases i
      · simp
      · simp
      · exact y.property.2.symm.trans (pinVal y.val)
    rw [e,pack_parts]
  right_inv w := by
    apply Subtype.ext
    simp only [pre_pack,post_pack,tailPin0,tailPin1,Prod.mk.eta]

theorem counter_step (n : ℕ) (d : Fin (n+1)→Bool) (pin : Bool) :
    counter (n+1) d pin =
      if pin then 2*counter n (fun i => d i.castSucc) true +
        (if d (Fin.last n) then counter n (fun i => d i.castSucc) false else 0)
      else counter n (fun i => d i.castSucc) false := by
  classical
  have hL : Fintype.card (Fiber d pin) = counter (n+1) d pin := by
    unfold counter count
    apply Fintype.card_of_subtype
    intro y
    simp [Fiber]
  have hR : Fintype.card (Grown d pin) =
      count (fun w : Timeline n × (Bool × Bool) =>
        Valid (fun i : Fin n => d i.castSucc) w.1 ∧
          step (d (Fin.last n)) (atVal w.1 (3*n)) pin w.2.1 w.2.2) := by
    unfold count
    apply Fintype.card_of_subtype
    intro x
    simp [Grown]
  rw [← hL, Fintype.card_congr (fiberEquiv d pin),hR]
  exact countStep (fun y : Timeline n => Valid (fun i : Fin n => d i.castSucc) y)
    (fun y : Timeline n => atVal y (3*n)) (d (Fin.last n)) pin


theorem counter_zero (d : Fin 0→Bool) (pin : Bool) : counter 0 d pin = 1 := by
  classical
  unfold counter count
  have e : ((Finset.univ : Finset (Timeline 0)).filter
      (fun y => Valid d y ∧ atVal y (3*0)=pin)) = {fun _ => pin} := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    have nv : Valid d y := by intro k; exact Fin.elim0 k
    constructor
    · intro h
      funext i
      have ei : i = (0 : Fin (3*0+1)) := by
        apply Fin.ext
        change i.val = 0
        have h := i.isLt
        change i.val < 1 at h
        omega
      subst i
      simpa [atVal] using h.2
    · intro h
      subst y
      exact ⟨by intro k; exact Fin.elim0 k, by simp [atVal]⟩
  have f : ((Finset.univ : Finset (Timeline 0)).filter
      (fun y => Valid d y ∧ atVal y (3*0)=pin)).card=1 := by rw [e,Finset.card_singleton]
  refine Eq.trans ?_ f
  apply congrArg Finset.card
  ext y
  simp

end Worker1209Fiber

namespace Local1209Weights

def bit (b : Bool) : ℕ := if b then 1 else 0

def weight {n : ℕ} (d : Fin n→Bool) : ℕ :=
  ∑ i : Fin n, if d i then 2^(i.rev.val) else 0

def value {n : ℕ} (d : Fin n→Bool) : ℕ := 2^n+weight d

theorem weight_step {n : ℕ} (d : Fin (n+1)→Bool) :
    weight d=2*weight (fun i : Fin n=>d i.castSucc)+bit (d (Fin.last n)) := by
  unfold weight
  rw [Fin.sum_univ_castSucc]
  have fLast : (Fin.last n).rev.val=0 := by simp [Fin.val_rev]
  rw [fLast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have e : i.castSucc.rev.val=i.rev.val+1 := by simp only [Fin.val_rev,Fin.val_castSucc];omega
  rw [e,pow_succ]
  cases h : d i.castSucc <;> simp [h,Nat.mul_comm]
  
theorem value_step {n : ℕ} (d : Fin (n+1)→Bool) :
    value d=2*value (fun i : Fin n=>d i.castSucc)+bit (d (Fin.last n)) := by
  simp only [value,weight_step,pow_succ,Nat.mul_add]
  omega

theorem value_zero (d : Fin 0→Bool) : value d=1 := by simp [value,weight]

theorem reorder {n : ℕ} (d : Fin n→Bool) :
    weight (fun i=>d i.rev)=∑ i : Fin n,if d i then 2^i.val else 0 := by
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun i=>if d i then 2^i.val else 0)

theorem count_induct (c : ∀ n : ℕ,(Fin n→Bool)→Bool→ℕ)
    (zero : ∀ d : Fin 0→Bool,∀ pin,c 0 d pin=1)
    (hot : ∀ n (d : Fin (n+1)→Bool), c (n+1) d true=
      2*c n (fun i=>d i.castSucc) true+
        if d (Fin.last n) then c n (fun i=>d i.castSucc) false else 0)
    (cold : ∀ n (d : Fin (n+1)→Bool), c (n+1) d false=c n (fun i=>d i.castSucc) false) :
    ∀ n (d : Fin n→Bool) pin,c n d pin=if pin then value d else 1 := by
  intro n
  induction n with
  | zero =>
    intro d pin
    rw [zero,value_zero]
    cases pin <;> rfl
  | succ n ih =>
    intro d pin
    have H := ih (fun i=>d i.castSucc) true
    have C := ih (fun i=>d i.castSucc) false
    cases pin with
    | false =>
      rw [cold]
      exact C
    | true =>
      rw [hot,H,C,value_step]
      simp [bit]

end Local1209Weights

namespace Local1209Graph
open Worker1209Path Worker1209LocalCount

def tag {L : ℕ} (i : V L) : Option (Fin L) :=
  if h : i.val % 3=1 ∧ i.val/3<L then
    some ((⟨i.val/3,h.2⟩ : Fin L).rev)
  else none

theorem tag_b {L} (k : Fin L) : tag (b k)=some k.rev := by
  have hv : (3*k.val+1)/3=k.val := by omega
  have hm : (3*k.val+1)%3=1 := by omega
  simp [tag,b,hv,hm,k.isLt]

theorem tag_p {L} (k : Fin L) : tag (p k)=none := by simp [tag,p]
theorem tag_q {L} (k : Fin L) : tag (q k)=none := by simp [tag,q,Nat.add_mod]
theorem tag_u {L} (k : Fin L) : tag (u k)=none := by simp [tag,u,Nat.add_mod]
theorem tag_last (L : ℕ) : tag (last L)=none := by simp [tag,last]

theorem tag_of_some {L} (i : V L) (j : Fin L) (e : tag i=some j) :
    ∃ k : Fin L,i=b k ∧ j=k.rev := by
  unfold tag at e
  split at e
  next h =>
    let k : Fin L := ⟨i.val/3,h.2⟩
    have er : k.rev=j := Option.some.inj e
    exact ⟨k,Fin.ext (by simp [b,k];omega),er.symm⟩
  next h => simp at e

def active {L} (digit : Fin L→Bool) (i : V L) : Bool :=
  (tag i).elim true (fun j=>!(digit j))

def graphValid {L} (digit : Fin L→Bool) (y : V L→Bool) : Prop :=
  (∀ i, active digit i=false → y i=false) ∧
  ∀ i j,(i,j)∈D L → active digit i=true → active digit j=true → y i=true → y j=true

def stageValid {L} (digit : Fin L→Bool) (y : V L→Bool) : Prop :=
  ∀ k : Fin L, step (digit k.rev) (y (p k)) (y (q k)) (y (b k)) (y (u k))

theorem graph_iff_stages {L} (digit : Fin L→Bool) (y : V L→Bool) :
    graphValid digit y ↔ stageValid digit y := by
  have pb (k : Fin L) : active digit (b k)=(!(digit k.rev)) := by simp [active,tag_b]
  have pp (k : Fin L) : active digit (p k)=true := by simp [active,tag_p]
  have pq (k : Fin L) : active digit (q k)=true := by simp [active,tag_q]
  have pu (k : Fin L) : active digit (u k)=true := by simp [active,tag_u]
  constructor
  · rintro ⟨d,ar⟩ k
    have run (a c : V L) (R :
      (a=p k ∧ c=q k) ∨ (a=q k ∧ c=b k) ∨ (a=b k ∧ c=p k) ∨ (a=u k ∧ c=p k)) :=
      ar a c ((mem_D a c).mpr ⟨k,R⟩)
    refine ⟨?_,run _ _ (Or.inl ⟨rfl,rfl⟩) (pp k) (pq k),?_,?_,
      run _ _ (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))) (pu k) (pp k)⟩
    · intro yes
      exact d _ (by simp [pb,yes])
    · intro no
      exact run _ _ (Or.inr (Or.inl ⟨rfl,rfl⟩)) (pq k) (by simp [pb,no])
    · intro no
      exact run _ _ (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))) (by simp [pb,no]) (pp k)
  · intro h
    constructor
    · intro i off
      cases e : tag i with
      | none => simp [active,e] at off
      | some j =>
        obtain ⟨k,rfl,_⟩ := tag_of_some i j e
        exact (h k).1 (by simpa [pb] using off)
    · intro i j ed ai aj vi
      obtain ⟨k,a|a|a|a⟩ := (mem_D i j).mp ed
      · obtain ⟨rfl,rfl⟩ := a
        exact (h k).2.1 vi
      · obtain ⟨rfl,rfl⟩ := a
        exact (h k).2.2.1 (by simpa [pb] using aj) vi
      · obtain ⟨rfl,rfl⟩ := a
        exact (h k).2.2.2.1 (by simpa [pb] using ai) vi
      · obtain ⟨rfl,rfl⟩ := a
        exact (h k).2.2.2.2 vi

end Local1209Graph

namespace Local1209Main
open Worker1209Path Worker1209Fiber Local1209Graph Local1209Weights

theorem graph_to_valid {L} (digit : Fin L→Bool) (y : V L→Bool) :
    graphValid digit y ↔ Valid (fun i => digit i.rev) y := by
  rw [graph_iff_stages]
  unfold stageValid Valid
  have P (k : Fin L) : atVal y (3*k.val)=y (p k) := atVal_coord y (p k)
  have Q (k : Fin L) : atVal y (3*k.val+3)=y (q k) := atVal_coord y (q k)
  have B (k : Fin L) : atVal y (3*k.val+1)=y (b k) := atVal_coord y (b k)
  have U (k : Fin L) : atVal y (3*k.val+2)=y (u k) := atVal_coord y (u k)
  simp only [P,Q,B,U]

theorem count_value (L : ℕ) (digits : Fin L→Bool) (pin : Bool) :
    counter L digits pin=if pin then value digits else 1 := by
  apply count_induct counter counter_zero
  · intro n d
    simpa using counter_step n d true
  · intro n d
    simpa using counter_step n d false

theorem graph_count (L : ℕ) (digit : Fin L→Bool) (pin : Bool) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ((Finset.univ : Finset (V L→Bool)).filter
        (fun y=>graphValid digit y ∧ y (last L)=pin)).card =
      if pin then 2^L+∑ i : Fin L, (if digit i then 2^i.val else 0) else 1 := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let A : Finset (V L→Bool) := Finset.univ.filter
    (fun y=>graphValid digit y ∧ y (last L)=pin)
  change A.card=_
  have e : A.card=counter L (fun i=>digit i.rev) pin := by
    unfold counter Worker1209LocalCount.count
    apply congrArg Finset.card
    ext y
    simp only [A,Finset.mem_filter,graph_to_valid,Finset.mem_univ,true_and]
    have z := atVal_coord y (last L)
    change atVal y (3*L)=y (last L) at z
    rw [z]
  rw [e,count_value,value,reorder]
  cases pin <;> simp
  apply Finset.sum_congr rfl
  intro i _
  cases digit i <;> simp

end Local1209Main

end PEqualNP.Outside.L_lib_1209

open PEqualNP.Outside.L_lib_1209

theorem PEqualNP.Outside.L_lib_1209 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ L : Nat,
  ∃ (m : Nat) (D : Finset (Fin m × Fin m)) (tag : Fin m → Option (Fin L))
    (last : Fin m),
    m = 3*L+1 ∧ D.card ≤ 4*L ∧ (∀ i, (i,i) ∉ D) ∧ tag last = none ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
      l ≤ 2*m+1 ∧ (∀ t, (bag t).card ≤ 3) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
      (∀ i j, (i,j) ∈ D → ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
      (∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
      (∃ t, last ∈ bag t ∧ ∀ u, u ≤ t)) ∧
    ∀ (digit : Fin L → Bool) (pin : Bool),
      let active := fun i => (tag i).elim true (fun j => !(digit j))
      let valid := fun (y : Fin m → Bool) =>
        (∀ i, active i = false → y i = false) ∧
        ∀ i j, (i,j) ∈ D → active i = true → active j = true → y i = true → y j = true
      ((Finset.univ : Finset (Fin m → Bool)).filter
        (fun y => valid y ∧ y last = pin)).card =
          if pin then 2^L + ∑ i : Fin L, (if digit i then 2^i.val else 0) else 1 := by
  intro L
  refine ⟨3*L+1, Worker1209Path.D L, Local1209Graph.tag, Worker1209Path.last L, rfl,
    Worker1209Path.D_card L, Worker1209Path.D_loopless, Local1209Graph.tag_last L,
    Worker1209Path.path_cert L, ?_⟩
  intro digit pin
  exact Local1209Main.graph_count L digit pin
