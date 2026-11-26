import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17511

namespace Numeric
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def aN (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def bG (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def dN (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem cZ {u d} (h : bG u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem gz {u d} (h : bG u d) (a b : Sig) : bin d a b = bin (dN d) b a := by
  rcases cZ h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,dN,BitVec.and_comm,BitVec.or_comm]
theorem mw {u d} (h : bG u d) : bG u (dN d) ∧ dN (dN d)=d := by
  rcases cZ h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [dN,bG]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ aN target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), bG u d ∧ S=insert a (insert b U) ∧
      aN a ∧ aN b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : aN target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : bG u d)
    (ha : aN a) (hb : aN b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : aN target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : bG u d)
      (ha : aN a) (hb : aN b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma jG {u target k S} (h : Live u target k S) : ∀ a ∈ S, aN a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma g3 {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma cf (i) : bit i zero = false := by simp [bit,zero]
private lemma cH (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma dZ (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma dH (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem co {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem sf (a : Sig) : nrm false a = a := rfl
theorem se (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,dZ]
theorem g8 {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem sb (a : Sig) : neg (neg a) = a := by simp [neg]
theorem jZ (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,dZ,sb]
theorem sR {a : Sig} (h : aN (neg a)) : aN a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem sS {u} {a : Sig} (h : aN (nrm u a)) : aN a := by
  unfold nrm at h
  split at h
  · exact sR h
  · exact h
def ct (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem ex (i) (d : Bool) (a b : Sig) : bit i (ct d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [ct,bit]
theorem si (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (ct d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply co
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,ex,ha,hb,dH,dZ,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,dZ,ex]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (ct false) one
  | .or => xs.foldr (ct true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def d3 (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def dp (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬aN v
def bV (u : Bool) (w : List Sig) (v : Sig) : Prop := dp w (nrm u v)

private lemma ic (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply co <;> intro i <;>
    simp [dH,cf,cH]

private lemma sa : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma j2 {w : List Sig} {a : Sig} (h : dp w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ aN a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def eM (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, bG u d ∧ a ∈ w ∧ b ∈ w ∧ aN a ∧ aN b ∧ a ≠ b ∧ z = bin d a b

private lemma ie {u w a b} (d : Nat) (hd : bG u d) (ha : dp w a) (hb : dp w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    dp w (bin d a b) ∨ eM u w (bin d a b) := by
  have rz : dp w zero := Or.inr (fun h => h.1 rfl)
  have ro : dp w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := ic a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := ic b
  by_cases he : a=b
  · subst b
    left
    rcases cZ hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases j2 ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases cZ hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases cZ hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases j2 hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases cZ hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases cZ hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem jX (a : Sig) : nrm true a ≠ one := by
  intro h
  have := se a
  rw [h,cH] at this
  exact Bool.noConfusion this
theorem kk {u w a b} (d : Bool) (ha : bV u w a) (hb : bV u w b) :
    bV u w (ct d a b) ∨ eM u w (nrm u (ct d a b)) := by
  cases u
  · have e : ct d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := ie (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold bV
    simp only [sf] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := si d a b
    unfold bV
    rw [eq]
    exact ie e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨jX a,jX b⟩)
theorem fk {u w} {v : Sig} (h : v=zero ∨ v=one) : bV u w v := by
  refine Or.inr fun hp => ?_
  have := sS hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma eW {u} (w : List Sig) (i : Nat) : bV u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact fk (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem sX {w a} (h : bV true w a) : bV true w (neg a) := by
  unfold bV
  rwa [jZ]

def cD (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma n8 (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → cD g=false) :
    bV u (w.map (nrm u)) (gv w g) ∨ (cD g=false ∧ eM u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : bV u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (ct d) (if d then zero else one)) ∨
      eM u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (ct d) (if d then zero else one))) := by
    have unit (v : Sig) : ct d v (if d then zero else one) = v := by
      apply co
      intro i
      cases d <;> simp [ex,cf,cH]
    cases l with
    | nil => exact Or.inl (fk (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (eW w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact kk d (eW w i) (eW w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [cD])
    left
    cases l with
    | nil => exact fk (Or.inr (by simp [gv,sa]))
    | cons i l => exact sX (eW w i)

private lemma kl {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : dp w z ∨ (c=1 ∧ eM u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := jG h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma mj {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, cD g=false)
    (hp : aN target) (hout : target ∈ (d3 gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !cD g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [d3] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := n8 u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : dp (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if cD g then 0 else 1)=1 ∧ eM u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := kl ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : cD g <;> simp [hn] at hl ⊢ <;> omega

private lemma h5 (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (cf _).symm
  | some a => rfl

private lemma s3 (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [h5]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact cH _
    | cons a l ih =>
      change bit i (ct false _ _) = (_ && _)
      rw [ex]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact cf _
    | cons a l ih =>
      change bit i (ct true _ _) = (_ || _)
      rw [ex]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [dZ,cf]
    | cons a l => exact dZ _ _

private lemma mg (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (d3 gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (d3 gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,s3 i g w (hg g (by simp))]

abbrev aq (R : Type) := R → Bool

def inv {R} (a : aq R) : aq R := fun r => !(a r)

def bM {R} (isOr : Bool) (a b : aq R) : aq R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def cJ {R} (d : Nat) (a b : aq R) : aq R :=
  if d=0 then bM false a b else if d=1 then bM true a b else
    if d=2 then bM false a (inv b) else bM false (inv a) b

def a0 {R} (a : aq R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def bx {R} (a : aq R) : Nat := by
  classical exact if a0 a then 1 else 0

noncomputable def bR {R} (xs : List (aq R)) : Nat := (xs.map bx).sum

def aL {R} (u : Bool) (pool : List (aq R)) (v : aq R) : Prop :=
  v ∈ pool ∨ a0 v ∨ (u=true ∧ inv v ∈ pool)

def ek {R} (u : Bool) (pool xs : List (aq R)) := ∀ a ∈ xs, aL u pool a

def Reach {R} (u : Bool) (roots : List (aq R)) : Nat → List (aq R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (aq R)) (a b : aq R), Reach u roots p bank ∧ aL u bank a ∧
      aL u bank b ∧ c=bM op a b :: bank
theorem Reach.start {R u} {roots : List (aq R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (aq R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : aL u bank a) (hb : aL u bank b) : Reach u roots (p+1) (bM op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (aq R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : aL u bank a)
      (hb : aL u bank b), motive p bank h →
      motive (p+1) (bM op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def aP {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : aq R) : Nat → List (aq R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : aq R) (rest : List (aq R)), bG u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (cJ op a b :: aP ka a (aP kb b rest))
theorem Run.stop {R u} {goal : aq R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : aq R} {s : Nat} {xs zs : List (aq R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : aq R} {s : Nat} {a b : aq R} {rest : List (aq R)} (op : Nat) (hd : bG u op) (ka kb : Bool)
    (h : Run u goal s (cJ op a b :: aP ka a (aP kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : aq R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : bG u op) (ka kb : Bool) (h : Run u goal s (cJ op a b :: aP ka a (aP kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem eG {R} (a : aq R) (xs) : bR (a::xs)=bx a + bR xs := by
  simp [bR]

theorem jQ {R} (a : aq R) (xs) (k : Bool) : bR xs ≤ bR (aP k a xs) := by
  cases k <;> simp [aP,eG]

theorem gU {R} {a : aq R} (h : a0 a) : a0 (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem iR {R} (a : aq R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem im {R} (a : aq R) : bx (inv a)=bx a := by
  have : a0 (inv a) ↔ a0 a := ⟨fun h => iR a ▸ gU h,gU⟩
  by_cases h : a0 a
  · simp only [bx,if_pos h,if_pos (this.mpr h)]
  · simp only [bx,if_neg h,if_neg (fun x => h (this.mp x))]
theorem gw {R u} {bank : List (aq R)} {a} (hu : u=true) (h : aL u bank a) : aL u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(iR a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (gU h))
  · exact Or.inl h
theorem lD {R} {a b : aq R} (op) (h : a0 a) (g : a0 b) :
    a0 (bM op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem mC {R u} (op) {a b : aq R} {bank}
    (h : a0 a ∨ a0 b) (ha : aL u bank a) (hb : aL u bank b) :
    aL u bank (bM op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [bM]⟩)
    · simpa [bM] using hb
    · simpa [bM] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [bM]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [bM]⟩)
    · simpa [bM] using ha
    · simpa [bM] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [bM]⟩)

theorem hZ {R u} {bank v} (w : aq R) (h : aL u bank v) :
    aL u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem mi {R u} (roots : List (aq R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : aL u bank a) (hb : aL u bank b) :
    ∃ q next, Reach u roots q next ∧ aL u next (bM op a b) ∧
        (∀ v, aL u bank v → aL u next v) ∧
        q+bx a+bx b ≤ p+1+bx (bM op a b) := by
  classical
  by_cases c : a0 a ∨ a0 b
  · refine ⟨p,bank,hp,mC op c ha hb,fun _ h => h,?_⟩
    by_cases ca : a0 a <;> by_cases cb : a0 b
    · simp [bx,ca,cb,lD op ca cb]
    · simp [bx,ca,cb]
    · simp [bx,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬a0 a := fun h => c (Or.inl h)
    have cb : ¬a0 b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => hZ _ h,
      by simp [bx,ca,cb]⟩
theorem ik {R u} {bank : List (aq R)} {d a b} (hd : bG u d) (ha : aL u bank a) (hb : aL u bank b) :
    ∃ op x y, cJ d a b=bM op x y ∧ aL u bank x ∧ aL u bank y ∧ bx x=bx a ∧ bx y=bx b := by
  rcases cZ hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,gw hu hb,rfl,im b⟩
  · exact ⟨false,inv a,b,rfl,gw hu ha,hb,im a,rfl⟩
theorem mh {R u} (roots : List (aq R)) {p bank a b} (d) (hd : bG u d) (hp : Reach u roots p bank)
    (ha : aL u bank a) (hb : aL u bank b) :
    ∃ q next, Reach u roots q next ∧ aL u next (cJ d a b) ∧
        (∀ v, aL u bank v → aL u next v) ∧
        q+bx a+bx b ≤ p+1+bx (cJ d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := ik hd ha hb
  rw [e,←cx,←cy]
  exact mi roots op hp hx hy

theorem jS {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ aP k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [aP]

theorem lL {R u} {goal : aq R} (nc : ¬a0 goal) {s ws}
    (h : Run u goal s ws) (roots : List (aq R)) {p bank}
    (hp : Reach u roots p bank) (hs : ek u bank ws) :
    ∃ q next, Reach u roots q next ∧ aL u next goal ∧ q+bR ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [bR,bx,nc]⟩
  | perm eq _ ih =>
    have hsub : ek u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [bR,←(eq.map bx).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := mh roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : ek u T (cJ op a b :: aP ka a (aP kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases jS hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (jS hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := jQ a (aP kb b rest) ka
    have hlen' := jQ b rest kb
    rw [eG] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [eG,eG]
    omega

def aS {R S : Type} (rows : S → R) (a : aq R) : aq S :=
  fun r => a (rows r)

theorem sY {R S : Type} (rows : S → R) (k : Bool) (a : aq R) (ws) :
    (aP k a ws).map (aS rows) =
    aP k (aS rows a) (ws.map (aS rows)) := by
  cases k <;> simp [aP]

theorem kp {R S : Type} (rows : S → R) (d) (a b : aq R) :
    aS rows (cJ d a b) = cJ d (aS rows a) (aS rows b) := by
  unfold cJ
  split_ifs <;> rfl
theorem sZ {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (aS rows goal) s (ws.map (aS rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,sY,kp] at ih ⊢
    exact Run.two op hd ka kb ih

theorem hE {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬a0 (aS rows goal)) {roots : List (aq S)} {p bank L}
    (hp : Reach u roots p bank) (hs : ek u bank (ws.map (aS rows)))
    (hl : ∀ q bs, Reach u roots q bs → aL u bs (aS rows goal) → L ≤ q) :
    L + bR (ws.map (aS rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := lL nc (sZ rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def ay (a : Sig) : aq Row := fun r => bit r a
def ce (f : aq Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem dJ (f : aq Row) (r : Row) : bit r (ce f) = f r := by
  simp only [bit,ce,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem hO (v : Sig) : ce (ay v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact dJ (ay v) ⟨j,hj⟩

theorem sj (f : aq Row) : ay (ce f) = f := by
  funext r
  exact dJ f r

theorem j1 (a : Sig) : ay (neg a) = inv (ay a) := by
  funext r
  exact dZ _ _

theorem j0 (d : Nat) (a b : Sig) :
    ay (bin d a b) = cJ d (ay a) (ay b) := by
  funext r
  simp only [ay,dH,cJ]
  split_ifs <;> rfl

theorem jM {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (aP d a l).map f = aP d (f a) (l.map f) := by cases d <;> rfl

theorem fL {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (aP k a l).Nodup := by cases k <;> simp [aP,hn,ha]

theorem fK (k : Bool) (a : Sig) (l : List Sig) :
    (aP k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [aP]

theorem g2 {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (ay T) k (v.map ay) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := aP kb b rest
    let tail := aP ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := fL kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,aP,h,hab,ar]
    have nd := fL ka a mid bm am
    have ht : tail.toFinset = U := by
      change (aP ka a (aP kb b rest)).toFinset = U
      rw [fK,fK,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::aP ka a (aP kb b rest)).map ay) at progress
    rw [List.map_cons,jM,jM,j0] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem uA (f : aq Row) : ce (inv f) = neg (ce f) := by
  rw [←hO (neg (ce f)),j1,sj]

theorem uB (d : Bool) (f g : aq Row) :
    ce (bM d f g) = ct d (ce f) (ce g) := by
  apply co
  intro r
  rw [dJ,ex,dJ,dJ]
  cases d <;> rfl

theorem gx {u} {bank : List (aq Row)} {a} (h : aL u bank a) :
    bV u ((bank.map ce).map (nrm u)) (ce a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply fk
    cases b
    · exact Or.inl (co fun i => (dJ _ i).trans (cf i).symm)
    · exact Or.inr (co fun i => (dJ _ i).trans (cH i).symm)
  · have := uA a
    refine Or.inl ?_
    rw [←jZ,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem sU {u} {roots : List (aq Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map ce).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map ce).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,uB] at sub
    have rep := kk d (gx ha) (gx hb)
    obtain ⟨k',S',hk,run',sub'⟩ := kl (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def bT (a : Sig) : Bool := !(bit 0 a)
theorem jY {u} {w : List Sig} (h : w.all bT=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact g8 (by simpa [bT] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem f7 {u} {roots : List Sig} {p bank T} (hp : aN T) (nT : bT T=true) (nR : roots.all bT=true)
    (h : Reach u (roots.map ay) p bank) (hit : aL u bank (ay T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := gx hit
  rw [hO] at hm
  unfold bV at hm
  rw [g8 (by simpa [bT] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := sU h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map ay).map ce = roots := by simp [List.map_map,Function.comp_def,hO]
  rw [e,jY nR] at hs
  exact hs

theorem jH {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [dH,dH,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem fj {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := jH h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def cC : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def f9 (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def gH (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem md : ∀ r : Row, bit r cC = gH (f9 r) := by decide +kernel
theorem iP : aN cC := by unfold aN; decide +kernel
theorem gT : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem s4 (r : Row) : List.ofFn (f9 r) = inputs.map (bit r) := by
  rw [←gT]
  rw [List.map_ofFn]
  rfl

theorem uz (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((d3 C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (f9 r))).getD i false := by
  rw [←h5,mg _ _ _ (fun g hg => (h g hg).1),s4]
  rfl

def bK (f : Row → Row) (a : Sig) := ce fun r => bit (f r) a
theorem dI (f : Row → Row) (a : Sig) (r : Row) :
    bit r (bK f a) = bit (f r) a := dJ _ _
theorem e9 (f : Row → Row) (a : Sig) :
    ay (bK f a) = aS f (ay a) := by funext r; exact dI f a r
theorem km (f : Row → Row) (d : Nat) (a b : Sig) :
    bK f (bin d a b) = bin d (bK f a) (bK f b) := by
  apply co
  intro r
  simp only [dI,dH]

theorem sW (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (bK f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [dI,dI,hr] at he
  exact he
theorem kn (f : Row → Row) : bK f zero = zero ∧ bK f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (dI f zero ⟨j,hj⟩).trans ((cf _).trans (cf ⟨j,hj⟩).symm)
  · exact (dI f one ⟨j,hj⟩).trans ((cH _).trans (cH ⟨j,hj⟩).symm)
theorem qt {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (bK f T) k (S.image (bK f)) := by
  have inj := sW f onto
  obtain ⟨fz,fo⟩ := kn f
  have pp (v) (p : aN v) : aN (bK f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : bK f (bin d a b) ∉ (insert a (insert b U)).image (bK f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,km] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem r9 {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [dH] at hp hn
      subst none
      rcases cZ hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def ac (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map ay) p bank → aL u bank (ay T) → L ≤ p
theorem sV {R u} {roots : List (aq R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (aq R)} {a} (h : aL false bank a) : aL u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem rA {u roots T L} (h : ac true roots T L) : ac u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (sV hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def aH (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def fw (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem jJ {u roots T L} (hp : aN T) (nT : bT T=true) (nR : roots.all bT=true)
    (essential : ∀ a ∈ roots, fw T roots a)
    (noRun : aH u T L roots.toFinset) : ac u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := f7 hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact fj run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem g9 {v : Sig} (hv : aN v) : ¬a0 (ay v) := by
  rintro ⟨b,h⟩
  have hr : bV false [] v := by
    apply fk
    cases b
    · exact Or.inl (co fun i => (congrFun h i).trans (cf i).symm)
    · exact Or.inr (co fun i => (congrFun h i).trans (cH i).symm)
  have hr' : dp [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem rG {R} (a b : List (aq R)) : bR (a++b) = bR a + bR b := by
  simp [bR]
theorem rH {R} (xs : List (aq R)) (hc : ∀ x ∈ xs, a0 x) :
    bR xs = xs.length := by
  induction xs with
  | nil => simp [bR]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [eG,List.length_cons,bx,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem jK {u} {roots other : List Sig} {T G : Sig} (pT : aN T) (nT : bT T=true) (nR : roots.all bT=true) (pG : aN G)
    (r : Row → Row) (eq : bK r T = G)
    (cB : ∀ a ∈ roots, aL u (other.map ay) (ay (bK r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, fw T roots a)
    (constant : ∀ a ∈ singles, a0 (ay (bK r a)))
    (L : Nat) (prior : ac u other G L) : ac u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := f7 pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact fj run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := g2 run front nd fe
  have gc : aS r (ay T) = ay G := (e9 _ _).symm.trans (congrArg ay eq)
  have supp : ek u (other.map ay) ((front.map ay).map (aS r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←e9]
    exact cB a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := hE r run' (gc ▸ g9 pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ bR ((front.map ay).map (aS r)) := by
    simp only [front,List.map_append,rG]
    let xs := (singles.toList.map ay).map (aS r)
    have only : ∀ v ∈ xs, a0 v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←e9]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := rH xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ bR xs + _
    rw [sz]
    omega
  omega

def cT (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: aP ka a (aP kb b ((ws.erase a).erase b))

theorem iv {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem me {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, bG u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      aN (bin d a b) → (cT ws a b d ka kb).length ≤ cap →
      aH u T (cap-1) (cT ws a b d ka kb).toFinset) :
    aH u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := jG tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,iv (hn.erase _) b,
        iv hn a]
    have ke : (aP ka a (aP kb b rest)).toFinset = U := by
      rw [fK,fK,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := fL kb b rest rn br
    have ax : a ∉ aP kb b rest := by cases kb <;> simp [aP,ar,hab]
    have nd : (cT ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,fL ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (cT ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::aP ka a (aP kb b rest)).toFinset = _
      simp [ke]
    have sc := g3 tail
    have len : (cT ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def aW {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def cB {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => aW oriented (sig a) ||| cB oriented sig ws

theorem l3 {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (cB oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (aW oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [cB]
  | cons a ws ih =>
    simp only [cB,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem lZ {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    cB oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (l3 (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := jH h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [aW,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := r9 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [aW,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem lY {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    cB (!u) sig ws = BitVec.allOnes n := by
  apply lZ h rfl correct
  simp

def dF (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, aL u (roots.map ay) (aS f (ay a))) ∧
    ¬a0 (aS f (ay T)) ∧
    ∀ p bank, Reach u (roots.map ay) p bank → aL u bank (aS f (ay T)) → L ≤ p

def aZ (d a : Sig) := a &&& d
def bf (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := aZ d a
  m == zero || m == d || (pool.map (aZ d)).any (fun v => v==m) ||
    (u && (let c := aZ d (neg a); (pool.map (aZ d)).any (fun v => v==c)))

theorem jN {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : aZ d a = aZ d b) :
    aS f (ay a) = aS f (ay b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,aZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem jP {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : aZ d a = zero) : aS f (ay a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [cf] at he
  simpa only [bit,aZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem jO {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : aZ d a = d) : aS f (ay a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,aZ,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def eg (u : Bool) (f : Row → Row) (bank : List (aq Row)) (pool : List Sig) :=
  ∀ a ∈ pool, aL u bank (aS f (ay a))

theorem eu {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : eg u f bank pool)
    (check : bf u d pool a = true) : aL u bank (aS f (ay a)) := by
  simp only [bf,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,jP dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,jO dom ho⟩)
  · exact jN dom he ▸ supplyB v hv
  · have h := gw hu (jN dom he ▸ supplyB v hv)
    rw [j1] at h
    have e : inv (aS f (inv (ay a))) = aS f (ay a) := by
      funext r
      simp [inv,aS]
    rwa [e] at h

abbrev cv := Nat × Sig × Sig
def bH (c : cv) := bin c.1 c.2.1 c.2.2
def et (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem lm {u d} (h : et u d=true) : bG u d := by
  simpa [et,bG] using h
def d1 (u : Bool) (d : Sig) (pool : List Sig) (c : cv) :=
  et u c.1 && (bf u d pool c.2.1 && bf u d pool c.2.2)

theorem kg {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : eg u f bank pool)
    (c : cv) (valid : d1 u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ eg u f next (bH c :: pool) := by
  simp only [d1,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := ik (lm valid.1) (eu dom hs valid.2.1)
    (eu dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [bH,j0,kp,e]
    exact Or.inl (by simp)
  · exact hZ _ (hs _ hm)

def eb (u : Bool) (d : Sig) (pool : List Sig) : List cv → Option (List Sig)
  | [] => some pool
  | c::cs => if d1 u d pool c then eb u d (bH c::pool) cs else none

theorem jL {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : eg u f bank pool)
    (cs : List cv) {result} (ok : eb u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ eg u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [eb] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := kg dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def bg (d a : Sig) := aZ d a == zero || aZ d a == d
theorem io {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (bg d) ≤ bR ((ws.map ay).map (aS f)) := by
  classical
  induction ws with
  | nil => simp [bR]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,eG]
    cases h : bg d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : a0 (aS f (ay a)) := by
        have hh : aZ d a = zero ∨ aZ d a = d := by simpa only [bg,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,jP dom hz⟩
        · exact ⟨true,jO dom ho⟩
      simpa [bx,hc,Nat.add_comm] using Nat.succ_le_succ ih

def f5 (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (bg d)) && ws.all (bf u d pool)

theorem kj {u raw T d L} (slice : dF u raw T d L) (cs : List cv)
    {pool ws cap} (built : eb u d raw cs = some pool)
    (nd : ws.Nodup) (cut : f5 u d L cap cs.length pool ws = true) :
    aH u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := jL dom (Reach.start (roots:=roots.map ay)) base cs built
  simp only [f5,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : ek u bank ((ws.map ay).map (aS f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact eu dom hs (List.all_eq_true.mp all a ha)
  have b := hE f (g2 h ws nd rfl) nc hr coveredS lo
  have massLo := io dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev cl := Sig × Sig × Row
def ga (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def h6 (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def hI (m : cl) (r : Row) : Row :=
  if bit r m.1 then ga m.2.2 r else if bit r m.2.1 then ga (h6 m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def fq (m : cl) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (h6 m.2.2).val) a)

theorem lA (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (ga d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [ga,h,r.isLt]

theorem lC (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem lz (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact lC _ _ _

theorem ly (r : Row) (m : cl) (a : Sig) : bit r (fq m a) = bit (hI m r) a := by
  simp only [fq,lz,lA,hI]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def cj (ms : List cl) (r : Row) := ms.foldl (fun j m => hI m j) r
def bd (ms : List cl) (a : Sig) := ms.foldr fq a
theorem eP (ms : List cl) (a : Sig) (r : Row) :
    bit r (bd ms a) = bit (cj ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (ly r m _).trans (ih _)
theorem ec (ms : List cl) (a : Sig) : bd ms a = bK (cj ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (eP ms a ⟨j,hj⟩).trans (dI _ _ ⟨j,hj⟩).symm

def gO (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem mB {u roots w} (ok : gO roots w = true) :
    aL u (roots.map ay) (ay w) := by
  simp only [gO,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext cf⟩)
  · exact Or.inr (Or.inl ⟨true,funext cH⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def dL (ms : List cl) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  bd ms T == G && raw.all (fun a => gO base (bd ms a))

theorem g4 {u ms raw T base G} (ok : dL ms raw T base G = true) :
    bK (cj ms) T = G ∧
    ∀ a ∈ raw, aL u (base.map ay) (ay (bK (cj ms) a)) := by
  simp only [dL,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,ec] at ok
  exact ⟨ok.1,fun a ha => mB (ok.2 a ha)⟩

theorem rB {u ms raw T base G L} (ok : dL ms raw T base G = true)
    (pT : aN T) (nT : bT T=true) (nR : raw.all bT=true) (pG : aN G)
    (hL : ac u base G L) : ac u raw T L := by
  obtain ⟨eq,supp⟩ := g4 ok
  simpa using jK pT nT nR pG (cj ms) eq supp ∅ (by simp) (by simp) L hL

theorem ut {u ms raw T base G L d} (ok : dL ms raw T base G = true)
    (all : bd ms d = one) (properG : aN G) (hL : ac u base G L) :
    dF u raw T d L := by
  obtain ⟨eq,supp⟩ := g4 ok
  have obs : aS (cj ms) (ay T) = ay G :=
    (e9 _ _).symm.trans (congrArg ay eq)
  refine ⟨cj ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←eP,all,cH]
  · intro a ha
    rw [←e9]
    exact supp a ha
  · rw [obs]
    exact g9 properG
  · rw [obs]
    exact hL

def hR (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem vL {T roots a rs} (ok : hR T roots a rs = true) : fw T roots a := by
  simp only [hR,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def db (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  bT T && raw.all bT && xs.all (fun a => hR T raw a.1 a.2)
theorem eU {T raw xs} (ok : db T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, fw T raw a := by
  simp only [db,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact vL (List.all_eq_true.mp ok.2 _ hm)

theorem dc {T raw xs} (ok : db T raw xs = true) :
    bT T=true ∧ raw.all bT=true := by
  simp only [db,Bool.and_eq_true] at ok
  exact ok.1
theorem ry {u raw T} (properT : aN T) (xs : List (Sig × Row × Row))
    (ok : db T raw xs = true) :
    ac u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := f7 properT (dc ok).1 (dc ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := eU ok a ha
    exact fj run raw a sub r s hd iso
  have bound := g3 run
  omega

def gB (ms : List cl) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  dL ms raw T base G && db T raw xs &&
    xs.all (fun a => bd ms a.1 == zero || bd ms a.1 == one)

theorem qp {u ms T raw base G xs L} (ok : gB ms T raw base G xs = true)
    (properT : aN T) (properG : aN G) (low : ac u base G L) :
    ac u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [gB,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := g4 ok.1.1
  apply jK properT (dc ok.1.2).1 (dc ok.1.2).2 properG _ eq supp _ (eU ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,ec] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext cf⟩
  · rw [h]
    exact ⟨true,funext cH⟩

def dt (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def aF (m : Nat) := (dt m).map Prod.snd
def gg (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def ad (m : Nat) : List Sig := if m<512 then aF m else aF m ++ [gg (m/512-1)]
def fp (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def K (m : Nat) : Sig :=
  let x := fp m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def l4 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def l5 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def l6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def ej (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((l4 (fixed &&& 7)*l5 ((fixed >>> 3) &&& 7)*l6 ((fixed >>> 6) &&& 7)) <<< o)
def gL (z o : Nat) : List cl :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def cY (v : Nat) : cl :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def ks (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (dt mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def gQ (m hints : Nat) : List (Sig × Row × Row) :=
  (dt m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def cd (T : Sig) := T != zero && T != one
theorem dm (T : Sig) (h : cd T = true) : aN T := by
  simpa only [cd,aN,Bool.and_eq_true,bne_iff_ne] using h
abbrev bw := Nat × Nat × Nat × Nat × Nat
def gC (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def dK (m : Nat) : Sig := K m
def eh (m : Nat) (c : bw) : Nat := m % 512+512*(c.1/512)
def eR (m : Nat) (c : bw) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := gL z o
  let raw := eh m c
  let free := gC raw (z % 512) o
  let G := bd ms (dK m)
  let xs := ks (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  cd G && dL ms (ad raw) (dK m) (ad free) G &&
    (bd ms (ej z o)==one) &&
    (if q=0 then db G (ad free) xs && decide (L ≤ count-1)
     else cd (K q) &&
       gB (gL (gC free q 0) 0) G (ad free) (ad q) (K q) xs &&
       decide (L ≤ prior q+count))

theorem eS {u} {m : Nat} (c : bw) (prior : Nat → Nat)
    (valid : ∀ q, ac u (ad q) (K q) (prior q))
    (ok : eR m c prior = true) : dF u (ad (eh m c)) (dK m) (ej c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := gL z o
  let raw := eh m (z,o,q,s,L)
  let free := gC raw (z % 512) o
  let G := bd ms (dK m)
  let xs := ks (z/512+80) s
  change (((cd G && dL ms (ad raw) (dK m) (ad free) G) &&
    (bd ms (ej z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply ut ok.1.1.2 ok.1.2 (dm _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [eR,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ry (dm _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [eR,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (qp hh.1.2 (dm _ ok.1.1.1) (dm _ hh.1.1) (valid q) p bank hr ha)

def fC (old rep : Nat) (swaps : List Nat) :=
  (cd (K old) && bT (K old) && (ad old).all bT) && cd (K rep) &&
    dL (swaps.map cY) (ad old) (K old) (ad rep) (K rep)
theorem ig {u old rep L swaps} (ok : fC old rep swaps = true)
    (h : ac u (ad rep) (K rep) L) : ac u (ad old) (K old) L := by
  simp only [fC,Bool.and_eq_true] at ok
  exact rB ok.2 (dm _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (dm _ ok.1.2) h

def aD (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem ag {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, ac u (ad e.1) (K e.1) e.2) (q : Nat) :
    ac u (ad q) (K q) (aD entries q) := by
  unfold aD
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def dG (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (aq Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬a0 (aS f (ay T)) ∧
    (∀ q ws, Reach u (roots.map ay) q ws → aL u ws (aS f (ay T)) → c.bound ≤ q) ∧
    Reach u (roots.map ay) c.paid bank ∧ eg u f bank c.wires ∧ True

theorem lG {u raw T d lb} (h : dF u raw T d lb) (cs : List cv) {ws}
    (build : eb u d raw cs = some ws) : dG u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := jL dom (Reach.start (roots:=roots.map ay)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem vG {u raw T c} (valid : dG u raw T c) (k : Nat) (rest : List Sig)
    (choice : cv) (paid : Bool)
    (known : ∀ a ∈ rest, bf u c.domain c.wires a = true)
    (buy : if paid then d1 u c.domain c.wires choice = true
       else bf u c.domain c.wires (bH choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(bH choice :: rest).countP (bg c.domain))
    (nd : (bH choice :: rest).Nodup) :
    aH u T k (bH choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := bH choice::rest
  have done (n : Nat) (out : List (aq Row)) (reach : Reach u (roots.map ay) n out)
      (zs : eg u f out (bH choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have cB : ek u out ((ws.map ay).map (aS f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := hE f (g2 run ws nd rfl) nc reach cB lo
    have cm := io dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (bg c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact eu dom hs buy
    · exact eu dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := kg dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, aL u out (aS f (ay v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact eu dom point (known _ hm)

def dU (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : cv) :=
  let z := bH op
  let extra := !(bf u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (bg c.domain)) &&
    rest.all (bf u c.domain c.wires)) && (!extra || d1 u c.domain c.wires op)

theorem s5 {u raw T c} (valid : dG u raw T c) {k rest op}
    (nd : (bH op::rest).Nodup) (cut : dU u c k rest op = true) :
    aH u T k (bH op::rest).toFinset := by
  let extra := !(bf u c.domain c.wires (bH op))
  apply vG valid k rest op extra _ _ _ nd
  · simp only [dU,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [dU,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : bf u c.domain c.wires (bH op) <;> simp_all [extra]
  · simp only [dU,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def g5 (u : Bool) (raw : List Sig) (cs : List cv) (d : Sig) (lb : Nat) : Option BoundPool :=
  (eb u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem rI {u raw T d L cs c} (slice : dF u raw T d L)
    (h : g5 u raw cs d L = some c) : dG u raw T c := by
  unfold g5 at h
  cases he : eb u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact lG slice cs he

abbrev ae := BitVec 152
abbrev fx := ae × ae
abbrev Y := Sig × fx

def cW {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem dA {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (cW r v).getLsbD i.val = bit (r i) v := by
  simp only [cW,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def dj (r s : Fin 152 → Row) (a : Sig) : fx := (cW r a,cW s a)
def fh (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem so {T r s} (h : fh T r s) : Sep T 152 r s (dj r s) := by
  exact ⟨h,fun a i => ⟨dA _ _ _,dA _ _ _⟩⟩
def cp (r s : Fin 152 → Row) (x : Y) := x.2 = dj r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bO (d : Nat) (x y : Y) : Y := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem sk {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    cW r (bin d a b) = bv d (cW r a) (cW r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := dA r (bin d a b) ⟨j,hj⟩
  rw [dH,←dA r a ⟨j,hj⟩,←dA r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem iz {r s x y} (d) (hx : cp r s x) (hy : cp r s y) :
    cp r s (bO d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [cp,bO,dj,sk,hx,hy]

def bW : Y := (zero,0,0)
theorem mn (r s) : cp r s bW := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : ae).getLsbD j = (cW r zero).getLsbD j
    rw [show (cW r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from dA _ _ ⟨j,hj⟩,cf]
    simp
  · change (0 : ae).getLsbD j = (cW s zero).getLsbD j
    rw [show (cW s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from dA _ _ ⟨j,hj⟩,cf]
    simp
theorem iA {r s ws} (all : ∀ v ∈ ws, cp r s v) (i : Nat) :
    cp r s (List.getD ws i bW) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact mn _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def eT (n : Nat) (bits : Nat) (ws : List Y) : List Y :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) bW
    let b := ws.getD ((bits >>> 4) &&& 15) bW
    eT k (bits >>> 10) (ws++[bO ((bits >>> 8) &&& 3) a b])
theorem ma (n bits) (ws) (r s) (base : ∀ v ∈ ws, cp r s v) :
    ∀ v ∈ eT n bits ws, cp r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact iz _ (iA base _) (iA base _)

def cA (cols : Nat → ae) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem lM : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem lN : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem lO : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem lP : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem lQ : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem lR : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem lS : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem lT : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem lU : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem gS : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact lM r
  · exact lN r
  · exact lO r
  · exact lP r
  · exact lQ r
  · exact lR r
  · exact lS r
  · exact lT r
  · exact lU r
theorem gu (cols : Nat → ae) (i : Fin 152) (j : Fin 9) :
    bit (cA cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [gS]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def f6 (m : Nat) (p q : Nat → ae) : List Y :=
  (dt m).map (fun (j,a) => (a,p j,q j))
theorem kq {m j a} (h : (j,a) ∈ dt m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem sT (m) (p q : Nat → ae) :
    ∀ a ∈ f6 m p q, cp (cA p) (cA q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := kq hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (gu p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (dA _ _ ⟨i,hi⟩).symm
  · exact (gu q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (dA _ _ ⟨i,hi⟩).symm

def g0 (m : Nat) (v : Nat → ae) : ae :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem lB (m : Nat) (v : Nat → ae) (i : Fin 152) (j : Fin 9) :
    bit (cA v i) (fp m j.val) =
    ((if m.testBit j.val then v j.val else 0) : ae).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [fp,hh] using gu v i j
  · simp [fp,hh,cf]
theorem lx (m : Nat) (v : Nat → ae) (i : Fin 152) :
    bit (cA v i) (K m) = (g0 m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (fp m j).getLsbD (cA v i).val = ((if m.testBit j then v j else 0) : ae).getLsbD i.val := lB m v i ⟨j,hj⟩
  simp only [bit,K,g0,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := ae × ae × ae

def cz (z : ae) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def bI (d : Bool) (v : List Y) : Cov :=
  v.foldr (fun a c => cz (aW d a.2) c) (0,0,0)

def dC (c : Cov) (a : ae) : ae := c.1 &&& ~~~(c.2.1 &&& a)
def eL (c : Cov) (a b : ae) : ae :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem lV (c : Cov) (a : ae) : dC (cz a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [dC,cz,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem lW (c : Cov) (a b : ae) : eL (cz a (cz b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [eL,cz,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem kW (c : Cov) (a b : ae) : cz a (cz b c)=cz b (cz a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [cz,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [cz,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem ip (d : Bool) {l r : List Y} (h : l.Perm r) : bI d l=bI d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (cz (aW d a.2)) ih
  | swap a b t => exact kW _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem lX (d : Bool) (v : List Y) {r s} (good : ∀ a ∈ v, cp r s a) :
    (bI d v).1 = cB d (dj r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (aW d a.2 ||| (bI d v).1) = aW d (dj r s a.1) ||| _
    rw [show a.2=dj r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def cK (ws : List Y) (a : Y) (keep : Bool) :=
  if keep then ws else ws.erase a
def bA (ws : List Y) (a b : Y) (ka kb : Bool) :=
  cK (cK ws a ka) b kb

theorem gF {ws : List Y} (a : Y) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem iq {ws : List Y} (d : Bool) (a : Y) (ha : a ∈ ws) (keep : Bool) :
    (bI d (cK ws a keep)).1 =
      (if keep then (bI d ws).1 else dC (bI d ws) (aW d a.2)) := by
  cases keep
  · change (bI d (ws.erase a)).1 = dC (bI d ws) _
    rw [ip d (gF a ha)]
    exact (lV _ _).symm
  · rfl
theorem mb {ws : List Y} (a b : Y) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (gF a ha).trans (List.Perm.cons _ (gF b hm))

theorem l0 {ws : List Y} (d : Bool) (a b : Y) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (bI d (bA ws a b ka kb)).1 =
      (if ka then (if kb then (bI d ws).1 else dC (bI d ws) (aW d b.2))
       else if kb then dC (bI d ws) (aW d a.2)
       else eL (bI d ws) (aW d a.2) (aW d b.2)) := by
  cases ka <;> cases kb
  · change (bI d ((ws.erase a).erase b)).1 = eL (bI d ws) _ _
    rw [ip d (mb a b ha hb ne)]
    exact (lW _ _ _).symm
  · exact iq d a ha false
  · exact iq d b hb false
  · rfl

def eJ (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem hK {xs ys} (h : eJ xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [eJ,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def cU (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def eX (xs : List Sig) := xs.foldl (fun v x => v+cU x) 0

def ey (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : cv) :=
  let ws := bH op::rest
  (links (eX ws)).any (eJ ws) || pools.any (fun p => dU u p k rest op)

theorem lK {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, dG u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → aH u T k (List.toFinset xs))
    (nd : (bH op :: rest).Nodup)
    (h : ey u pools links k rest op = true) :
    aH u T k (bH op :: rest).toFinset := by
  simp only [ey,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [hK ok]
    exact lValid _ _ hx
  · exact s5 (pValid _ hp) nd ok

abbrev hU := Cov × Bool
def ff (u : Bool) (ws : List Y) : hU := (bI (!u) ws,u)
def ei (v : Cov) (a b : ae) (ka kb : Bool) :=
  if ka then (if kb then v.1 else dC v b) else if kb then dC v a else eL v a b

theorem gG (ws : List Y) (a : Y) (k : Bool) : (cK ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem pX (ws : List Y) (a b : Y) (ka kb : Bool) :
    (bA ws a b ka kb).Sublist ws := (gG _ _ _).trans (gG _ _ _)
theorem qo (ws : List Y) (a b : Y) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (bA ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [bA,cK,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def cN (op : Nat) (a b : Y) : cv := (op,a.1,b.1)

abbrev bL := Nat × Nat × List Y × hU × List BoundPool × (Nat → List (List Sig))
def dM (c : bL) (op : Nat) (a b z : Y) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := ei cov.1 (aW d a.2) (aW d b.2) ka kb
    if (rs ||| aW d z.2) != BitVec.allOnes 152 then true else
    if !cd z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (bA ws a b ka kb).map Prod.fst
      ey cov.2 pools links (cap-1) rest (cN op a b)

def g7 (ws : List Y) (op : Nat) (a b : Y) (ka kb : Bool) :=
  (bO op a b).1 :: (bA ws a b ka kb).map Prod.fst
theorem mf {u raw T r s ws pools links cap a b op ka kb}
    (pairs : fh T r s) (faith : ∀ w ∈ ws, cp r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, dG u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → aH u T (cap-1) (List.toFinset xs))
    (pro : aN (bO op a b).1) (fresh : (bO op a b).1 ∉ ws.map Prod.fst)
    (test : dM (cap,ws.length,ws,ff u ws,pools,links) op a b (bO op a b) ka kb = true) :
    aH u T (cap-1) (g7 ws op a b ka kb).toFinset := by
  let z := bO op a b
  let rest := bA ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := pX _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : cd z.1 = true := by simpa [cd,aN] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,qo _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := g3 h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold dM at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := lY h (so pairs)
  let d := !u
  have g : (bI d rest).1 = cB d (dj r s) (rest.map Prod.fst) :=
    lX _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (bI d rest).1 = ei (bI d ws) (aW d a.2) (aW d b.2) ka kb :=
    l0 d a b ha hb ne ka kb
  have hf := iz op (faith _ ha) (faith _ hb)
  change aW d (dj r s z.1) ||| cB d (dj r s) (rest.map Prod.fst) = _ at sep
  change z.2 = dj r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((ei (bI (!u) ws) (aW (!u) a.2) (aW (!u) b.2) ka kb ||| aW (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (ei (bI (!u) ws) (aW (!u) a.2) (aW (!u) b.2) ka kb ||| aW (!u) z.2) != BitVec.allOnes 152 then true else if !cd z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact lK (op:=cN op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def el (ctx : bL) (a b : Y) (op : Nat) :=
  let z := bO op a b
  let attempt := dM ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def ed (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem j3 {u d} (h : bG u d) : d ∈ ed u := by
  rcases cZ h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [ed]
  · cases u <;> simp [ed]
  · simp [ed]
  · simp [ed]
def hP (ctx : bL) (a : Y) (bs : List Y) :=
    bs.all (fun b => (ed ctx.2.2.2.1.2).all (el ctx a b))
def dD (ctx : bL) : List Y → Bool
  | [] => true
  | a::bs => hP ctx a bs && dD ctx bs

theorem kY {ctx ws} (h : dD ctx ws=true) {a b : Y} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, bG ctx.2.2.2.1.2 d → el ctx a b d=true) ∨
      (∀ d, bG ctx.2.2.2.1.2 d → el ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [dD,Bool.and_eq_true,hP,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (j3 hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (j3 hd)
      · exact ih h.2 haTail hbTail

theorem uN {ctx a b d} (h : el ctx a b d = true) (ka kb : Bool) :
    dM ctx d a b (bO d a b) ka kb = true := by
  simp only [el,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem iS {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ aP k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [aP]
theorem jR {v : List Y} (nd : v.Nodup) (a w : Y) (k : Bool) :
    w ∈ cK v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [cK,nd.mem_erase_iff,and_comm]

theorem kA {ws : List Y} (nd : (ws.map Prod.fst).Nodup) {a b : Y}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem iT {ws : List Y} (nd : (ws.map Prod.fst).Nodup) {a b : Y}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (bA ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (gG ws a ka)
  simp only [bA,List.mem_map,jR wn,jR dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (kA nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (kA nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem lu {ws : List Y} (nd : (ws.map Prod.fst).Nodup) {a b : Y}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (g7 ws d a b ka kb).toFinset =
      (cT (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [g7,cT,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    iT nd ha hb,iS,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bO]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem lJ {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : bG u d) (ka kb : Bool) :
    (cT v a b d ka kb).toFinset = (cT v b a (dN d) kb ka).toFinset := by
  ext x
  simp only [cT,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    iS,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,gz hd a b]
  tauto

theorem sd {u raw T r s ws pools links cap}
    (pairs : fh T r s) (faith : ∀ w ∈ ws, cp r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, dG u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → aH u T (cap-1) (List.toFinset xs))
    (checks : dD (cap,ws.length,ws,ff u ws,pools,links) ws = true) :
    aH u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply me nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Y) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : aN (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : el (cap,ws.length,ws,ff u ws,pools,links) a b d = true) :
      aH u T (cap-1) (cT (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←lu nd aa bb ne']
    exact mf pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (uN test ka kb)
  rcases kY checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [lJ _ nd _ _ d hd]
    exact one b a (dN d) hbW haW (Ne.symm ne) kb ka (gz hd a.1 b.1 ▸ pro)
      (gz hd a.1 b.1 ▸ fresh) (hh _ (mw hd).1)

theorem kX (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← gT]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (gS i r).symm.trans ((h _ hm).trans (gS i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def gE (p q : List cl) := inputs.all (fun a => bd p (bd q a) == a)
theorem il {p q} (h : gE p q = true) (r : Row) :
    cj q (cj p r) = r := by
  apply kX
  intro a ha
  rw [←eP,←eP]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def eO (T : Sig) (p : List cl) :=
  (bd p T == T) && gE p p.reverse && gE p.reverse p
theorem s0 {u T n} {ws : List Sig} (hi : aH u T n ws.toFinset)
    (p : List cl) (ok : eO T p = true) : aH u T n (ws.map (bd p.reverse)).toFinset := by
  simp only [eO,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (cj p) := fun r => ⟨cj p.reverse r,il ok.2 r⟩
  intro k hk h
  have run := qt h (cj p) onto
  have goal : bK (cj p) T = T := (ec p T).symm.trans ok.1.1
  have inv (x : Sig) : bK (cj p) (bd p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [dI,eP,il ok.1.2]
  have back : (ws.map (bd p.reverse)).toFinset.image (bK (cj p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev af := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def bS : af := (0,0,0,0,0,0,0,fun _ => 0)
def bo (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def aR (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := bo data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := bo data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def cM (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := bo data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := bo data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → ae × ae) × List bw × List (List Nat) ×
  (Nat → af) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → ae × ae := g.2.2.1
def Forest.cols (g : Forest) : List bw := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → af := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def dY (g : Forest) :=
  let ws := f6 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem vJ (g : Forest) : ∀ a ∈ dY g,
    cp (cA fun j => (g.samples j).1) (cA fun j => (g.samples j).2) a := by
  exact sT g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def aY (g : Forest) := dK g.mask
def eQ (m : Nat) (v : Nat → ae) :=
  g0 m v
theorem lI (m : Nat) (v : Nat → ae) (i : Fin 152) :
    bit (cA v i) (dK m) = (eQ m v).getLsbD i.val := by
  exact lx m v i
theorem fD {m : Nat} {p q : Nat → ae}
    (hp : eQ m p = BitVec.allOnes 152) (hq : eQ m q = 0) :
    fh (dK m) (cA p) (cA q) := by
  intro i
  simp only [lI,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def dr {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::dr (bits >>> 1) ws else dr (bits >>> 1) ws
theorem s7 {α : Type} (bits : Nat) (ws : List α) : (dr bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold dr
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def fg (d : Nat) := 10*(d-1)
def iu (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def it (d raw dict : Nat) :=
  (dict % 65536)*fg d + (dict/65536)*(raw+d)

def iE (tab : af) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then bo word (i*width) width else
    let off := it d raw dict+i*iu d flags
    let pre := bo word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := bo word (off+flags % 16) lastBits
    let mask := bo word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*fg d
    bo word (pre*fg d) (fg d) |||
      (last <<< fg d) ||| (bo word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def kr (_g : Forest) (depth : Nat) := depth
def f8 (g : Forest) (k i : Nat) : Nat × List Y × List Y :=
  let raw := dY g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*kr g depth
  let width := len+raw.length+depth
  let recp := iE (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := eT depth ops raw
  (ops,bank,dr (recp >>> len) bank)

def iN (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def ii (bank : List Y) (ops paid : Nat) : Nat → List cv
  | 0 => []
  | n+1 =>
    let more := ii bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (iN ops 8 2,(bank.getD (ops &&& 15) bW).1,
        (bank.getD (iN ops 4 4) bW).1) :: more

def fB (g : Forest) (ops d : Nat) (bank : List Y) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    g5 g.mode (ad (eh g.mask ci)) (ii bank ops paid d) (ej ci.1 ci.2.1) ci.2.2.2.2

theorem lF (g : Forest)
    (cols : ∀ ci ∈ g.cols, dF g.mode (ad (eh g.mask ci)) (aY g) (ej ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : fB g ops depth bank i paid = some c) :
    dG g.mode (aF g.mask) (aY g) c := by
  unfold fB at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply rI _ h
    exact cols ci (List.mem_of_getElem? e)

def iO (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := bo data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: iO data w v n (pos+w+v)

def eB {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def hF (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    eB st fun pos => eB first fun base =>
    eB (bo data pos 32) fun head =>
    eB (Nat.log2 (head ^^^ (head+1))) fun ones =>
    eB (base+(ones <<< gapBits)+bo data (pos+ones+1) gapBits) fun key =>
    eB (bo data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        hF data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def sQ {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def iD (tab : af) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+bo data (start+i*ow) ow
    iO data cw d (bo data pos 5) (pos+5+marker)
  else
    let off := it d raw dict + num*iu d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+bo data (off+i*ow) ow
    let n := bo data pos 5
    let gap := bo data (pos+5) 3
    if !priority || decide (n≤1) then hF data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := bo data (pos+8) width
      let b := if n=2 then 1-a else bo data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := hF data pairs cw d gap n (pos+8+extra) 0
      sQ a b xs

def bP (g : Forest) (k i : Nat) := (f8 g k i).2.2.map Prod.fst
def ea (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (bP g k pair.1).map (bd (perm.map cY).reverse)

theorem qr (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, eO (aY g) (x.map cY) = true)
    (earlier : ∀ i < (g.levels k).1, aH g.mode (aY g) k (bP g k i).toFinset)
    {pair out} (h : ea g k pair = some out) :
    aH g.mode (aY g) k out.toFinset := by
  unfold ea at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact s0 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def dR (g : Forest) (k i : Nat) :=
  let raw := dY g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := f8 g k i
  let values := ws.map Prod.fst
  let rules := (iD (g.levels k) raw.length i).filterMap (fun (a,b) => fB g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (ea g (k-1))).toList
  decide values.Nodup && !(values.contains (aY g)) &&
    (if k=0 then true else dD (k,ws.length,ws,ff g.mode ws,rules,ls) ws)

theorem f1 (g : Forest) (k i : Nat)
    (samples : fh (aY g) (cA fun j => (g.samples j).1) (cA fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, dF g.mode (ad (eh g.mask ci)) (aY g) (ej ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, eO (aY g) (x.map cY) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, aH g.mode (aY g) (k-1) (bP g (k-1) j).toFinset)
    (checked : dR g k i = true) : aH g.mode (aY g) k (bP g k i).toFinset := by
  simp only [dR,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : aY g ∉ bP g k i := by simpa [bP] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (bP g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply sd (raw:=aF g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply ma _ _ _ _ _ (vJ g) v
    exact (s7 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact lF g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (ea g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact qr g _ names (prior (by omega)) h

def Q (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => dR g k (start+n) && Q g k start n
theorem gA {g k start n} (h : Q g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    dR g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [Q,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem ba {g k start a b} (h : Q g k start a=true)
    (h' : Q g k (start+a) b=true) : Q g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [Q,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,Q,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def cI (g : Forest) (top : Nat) :=
  ∀ k ≤ top, Q g k 0 (g.levels k).1 = true
def aJ (g : Forest) (prior : Nat → Nat) :=
  (eQ g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (eQ g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => eR g.mask c prior) &&
  g.autos.all (fun p => eO (aY g) (p.map cY))

theorem mz (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, ac g.mode (ad q) (K q) (prior q))
    (geometry : aJ g prior = true) (rows : cI g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, aH g.mode (aY g) k (bP g k i).toFinset := by
  simp only [aJ,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply f1 g 0 i (fD geometry.1.1.1 geometry.1.1.2)
      (fun x hx => eS _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact gA (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply f1 g _ i (fD geometry.1.1.1 geometry.1.1.2)
      (fun x hx => eS _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact gA (rows _ hk) i (by omega) (by omega)

def d7 (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && eJ (bP g k i) ws
theorem hG {g top prior k i ws} (low : ∀ q, ac g.mode (ad q) (K q) (prior q))
    (geom : aJ g prior = true) (blocks : cI g top) (le : k ≤ top)
    (idx : d7 g k i ws = true) : aH g.mode (aY g) k ws.toFinset := by
  simp only [d7,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←hK idx.2]
  exact mz g top prior low geom blocks _ le i idx.1

theorem zC {g prior i hints} (low : ∀ q, ac g.mode (ad q) (K q) (prior q))
    (geom : aJ g prior = true) (blocks : cI g g.cap)
    (idx : d7 g g.cap i (aF g.mask) = true) (hp : cd (aY g) = true)
    (ess : db (aY g) (aF g.mask) (gQ g.mask hints) = true)
    (all : (gQ g.mask hints).map Prod.fst = aF g.mask) :
    ac g.mode (aF g.mask) (aY g) (g.cap+1) := by
  apply jJ (dm _ hp) (dc ess).1 (dc ess).2 _ (hG low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply eU ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def ai (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, ac u (ad e.1) (K e.1) e.2
def au (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem aw {u old L m carries} (previous : ai u old)
    (main : ac u (ad m) (K m) L)
    (ok : carries.all (fun v => fC v.1 m v.2) = true) :
    ai u (au old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact ig (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem h7 : ai true [] := by simp [ai]
theorem p0 {u es} (h : ai true es) : ai u es := fun e he => rA (h e he)
def bY (v : Nat) (upper : Nat) := 2^153*upper+v
def bc {α : Type} (f : α → ae) : List α → Nat
  | [] => 0
  | x::xs => bY (f x).toNat (bc f xs)
def em : Nat → Nat
  | 0 => 0
  | n+1 => bY 1 (em n)
theorem gY (x : ae) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem sN (a b : ae) (u v : Nat) :
    bY a.toNat u &&& bY b.toNat v = bY (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bY,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (gY _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem sO (a b : ae) (u v : Nat) :
    bY a.toNat u ||| bY b.toNat v = bY (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bY,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (gY _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem sP (a b : ae) (u v : Nat) :
    bY a.toNat u ^^^ bY b.toNat v = bY (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bY,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (gY _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem e7 {α} (f g : α → ae) (xs) :
    bc f xs &&& bc g xs = bc (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [bc]
  | cons a xs ih => simp only [bc,sN,ih]
theorem gZ {α} (f g : α → ae) (xs) :
    bc f xs ||| bc g xs = bc (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [bc]
  | cons a xs ih => simp only [bc,sO,ih]
theorem fY {α} (f g : α → ae) (xs) :
    bc f xs ^^^ bc g xs = bc (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [bc]
  | cons a xs ih => simp only [bc,sP,ih]
def fI (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem uQ (n i : Nat) (hi : i<n) : (em n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [em,bY,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem oo (a : ae) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem rD {α} (f : α → ae) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fI (em xs.length) (bc f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fI,Nat.testBit_and,Nat.testBit_shiftRight,uQ _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [bc,List.length_cons,em,bY]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using oo (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev eN := Nat × Nat
abbrev gr := Nat × Nat × Nat

def cX {α} (s : α → fx) (xs : List α) : eN :=
  (bc (fun x => (s x).1) xs,bc (fun x => (s x).2) xs)
def f2 {α} (c : α → Cov) (xs : List α) : gr :=
  (bc (fun x => (c x).1) xs,bc (fun x => (c x).2.1) xs,
   bc (fun x => (c x).2.2) xs)
def dS (d : Bool) (a : eN) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem gq (a b : ae) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem hA {α} (s : α → fx) (xs : List α) (d : Bool) :
    dS d (cX s xs) = bc (fun x => aW d (s x)) xs := by
  cases d <;> simp only [dS,cX,aW,Bool.false_eq_true,ite_false,ite_true,e7,fY,gq]

def ee (op : Nat) (a b : eN) : eN :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem sn {α} (a b : α → Y) (xs : List α) (op : Nat) :
    ee op (cX (fun x => (a x).2) xs) (cX (fun x => (b x).2) xs) =
    cX (fun x => (bO op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [ee,h0,ite_true,cX,e7,bO,bv]
  by_cases h1 : op=1
  · simp [ee,h1,cX,gZ,bO,bv]
  by_cases h2 : op=2
  · simp [ee,h2,cX,e7,fY,gq,bO,bv]
  · have e (x y : ae) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [ee,h0,h1,h2,ite_false,cX,e7,fY,gq,bO,bv,e]

def gf (c : gr) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem uM {α} (c : α → Cov) (a b : α → ae) (xs : List α) (ka kb : Bool) :
    gf (f2 c xs) (bc a xs) (bc b xs) ka kb =
    bc (fun x => ei (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [gf,f2,e7,gZ,fY,gq,ei,dC,eL,
      Bool.false_eq_true,ite_false,ite_true]

def aI (c : bL) (i : Nat) := c.2.2.1.getD i bW
def d0 (c : bL) (i j op : Nat) (ka kb : Bool) :=
  let a := aI c i
  let b := aI c j
  dM c op a b (bO op a b) ka kb
def gD (c : bL) (d ka kb : Bool) (op i j : Nat) :=
  let a := aI c i
  let b := aI c j
  ei c.2.2.2.1.1 (aW d a.2) (aW d b.2) ka kb |||
    aW d (bO op a b).2

def fc {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && fc f (mask >>> 153) xs
theorem rE {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : fc f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [fc,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev ep := Nat × Nat × Nat × List eN × gr
def dg (k n : Nat) (xs : List bL) : ep :=
  (k,n,em xs.length,(List.range n).map (fun i => cX (fun c => (aI c i).2) xs),
    f2 (fun c => c.2.2.2.1.1) xs)
def eF (b : ep) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem jE (k n) (xs) {i : Nat} (h : i<n) :
    eF (dg k n xs) i = cX (fun c => (aI c i).2) xs := by
  simp [eF,dg,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem rF (d x : Sig) : aZ d (neg x) = d ^^^ aZ d x := by
  apply co
  intro r
  simp only [aZ,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def cg (p : Y → Bool) (a : Y) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem jI (p : Y → Bool) (ws : List Y) (a : Y) (keep : Bool) :
    ws.countP p ≤ (cK ws a keep).countP p + cg p a keep := by
  cases keep
  · simp only [cK,Bool.false_eq_true,ite_false,cg,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [cK,cg]

theorem pY (p : Y → Bool) (ws : List Y) (a b : Y) (ka kb : Bool) :
    ws.countP p - cg p a ka - cg p b kb ≤
    (bA ws a b ka kb).countP p := by
  have h1 := jI p ws a ka
  have h2 := jI p (cK ws a ka) b kb
  simp only [bA]
  omega

noncomputable def bJ {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem dy {β : Type} (n : Nat) (f : Nat → β) : bJ n f = f n := by cases n <;> rfl
noncomputable def d5 {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => bJ (f a) fun x => ih fun xs => k (x::xs)) l
theorem gN {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : d5 f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change bJ (f a) (fun x => d5 f l fun xs => k (x::xs)) = _
    rw [dy,ih]
    rfl
def aK (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def da (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def dQ (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def cO (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (dQ d m) (da m pm)) (and u (da (Nat.xor d m) pm))
theorem e8 (d a : Sig) : aK d.toNat a = (aZ d a).toNat := (BitVec.toNat_and _ _).symm
theorem gy (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem f0 (d a : Sig) : dQ d.toNat (aK d.toNat a) = bg d a := by
  rw [e8]
  have e : Nat.beq (aZ d a).toNat 0 = (aZ d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←gy,z0]
  rw [dQ,e,gy]
  rfl
theorem hY (x d : Sig) (pool : List Sig) : da x.toNat (pool.map (aK d.toNat)) = (pool.map (aZ d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (aK d.toNat a)) (da x.toNat (l.map (aK d.toNat))) = _
    rw [ih,e8,gy,List.map_cons,List.any_cons,Bool.beq_comm]
theorem fZ (u : Bool) (d a : Sig) (pool : List Sig) :
    cO u d.toNat (pool.map (aK d.toNat)) (aK d.toNat a) = bf u d pool a := by
  have x : Nat.xor d.toNat (aZ d a).toNat = (aZ d (neg a)).toNat := by
    rw [rF]
    exact (BitVec.toNat_xor _ _).symm
  rw [cO,f0,e8,x,hY,hY]
  simp only [bf,bg]
def dV (u : Bool) (p : BoundPool) (w : Y) : Nat := cond (bf u p.domain p.wires w.1) 0 1
def gb (u : Bool) (p : BoundPool) (ws : List Y) (k : Nat) (a b : Y) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Y => bg p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - cg const a ka - cg const b kb + (bg p.domain z).toNat
  (((ws.map (dV u p)).sum == cond ka 0 (dV u p a) + cond kb 0 (dV u p b)) &&
    decide (k+p.paid+(!bf u p.domain p.wires z).toNat < p.bound+cm)) &&
    (bf u p.domain p.wires z || (bf u p.domain p.wires a.1 && bf u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem kU (op : Nat) (d a b : Sig) : zN op (aK d.toNat a) (aK d.toNat b) = aK d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [e8]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply co
    intro r
    simp only [aZ,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply co
    intro r
    simp only [aZ,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply co
    intro r
    simp only [aZ,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply co
  intro r
  simp only [aZ,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def dh (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (dQ d x) 1 0)
theorem jW (d : Sig) (a : Y) (keep : Bool) :
    dh d.toNat (aK d.toNat a.1) keep = cg (fun w : Y => bg d w.1) a keep := by
  rw [dh,f0,cg]
  cases keep
  · cases bg d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def fi (u : Bool) (k : Nat) (ws : List Y) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Y => aK d w.1)
  (d,ms.countP (dQ d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (cO u d (p.wires.map (aK d)) m) 0 1).sum,ms,p.wires.map (aK d),u)
noncomputable def iB {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def fG {β : Type} (u : Bool) (k : Nat) (ws : List Y) (p : BoundPool) (f : QS → β) : β :=
  bJ p.domain.toNat fun d => d5 (aK d) p.wires fun pm => d5 (fun w : Y => aK d w.1) ws fun ms =>
  bJ (ms.countP (dQ d)) fun c => bJ p.bound fun l => bJ (Nat.add k p.paid) fun t =>
  bJ (ms.map fun m => cond (cO u d pm m) 0 1).sum fun v => iB u fun u => f (d,c,l,t,v,ms,pm,u)
theorem mx {β : Type} (u k ws p) (f : QS → β) : fG u k ws p f = f (fi u k ws p) := by
  have e (b : Bool) (f : Bool → β) : iB b f = f b := by cases b <;> rfl
  simp only [fG,dy,gN,e]
  rfl
noncomputable def fH {β : Type} (u : Bool) (k : Nat) (ws : List Y) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => fG u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem my {β : Type} (u k ws ps) (f : List QS → β) : fH u k ws ps f = f (ps.map (fi u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change fG u k ws p (fun q => fH u k ws ps fun qs => f (q::qs)) = _
    rw [mx,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev dw := bL × Nat × Nat × List QS × List Nat × Nat
noncomputable def df (c : bL) : dw :=
  let ws := c.2.2.1.map (fun w : Y => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (fi c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def gM {β : Type} (cs : List bL) : (List dw → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => bJ c.2.2.1.length fun n => bJ (cond c.2.2.2.1.2 4 2) fun l =>
    d5 (fun w : Y => w.1.toNat) c.2.2.1 fun ws => bJ (ws.map kwN).sum fun t =>
    fH c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem iC {β : Type} (cs) (f : List dw → β) : gM cs f = f (cs.map df) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change bJ c.2.2.1.length (fun n => bJ (cond c.2.2.2.1.2 4 2) fun l =>
      d5 (fun w : Y => w.1.toNat) c.2.2.1 fun ws => bJ (ws.map kwN).sum fun t =>
      fH c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => gM cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [dy,dy,gN,dy,my,ih]
    rfl
noncomputable def gJ (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  bJ (s.2.2.2.2.2.1.getD i 0) fun x => bJ (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := cO s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (dh s.1 x ka)) (dh s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (bJ (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (dQ s.1 (zN op x y)) false))
theorem uv {d : Nat} (ws : List Y) (i : Nat) (hd : aK d zero=0) :
    (ws.map (fun w : Y => aK d w.1)).getD i 0 = aK d (ws.getD i bW).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem mu {u k p ws i j op ka kb} (h : gJ (fi u k ws p) i j op ka kb=true) :
    gb u p ws k (ws.getD i bW) (ws.getD j bW) op ka kb=true := by
  have z0 : aK p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [aK,this]
  have su : (((ws.map (fun w : Y => aK p.domain.toNat w.1)).map fun m => cond (cO u p.domain.toNat (p.wires.map (aK p.domain.toNat)) m) 0 1).sum) =
      (ws.map (dV u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (cO u p.domain.toNat (p.wires.map (aK p.domain.toNat)) (aK p.domain.toNat w.1)) 0 1 = _
    rw [fZ]
    rfl
  simp only [gJ,fi,dy,uv _ _ z0,su,List.countP_map,Function.comp_def,f0] at h
  generalize ws.getD i bW=a at h ⊢
  generalize ws.getD j bW=b at h ⊢
  replace h : and (Nat.beq (ws.map (dV u p)).sum (Nat.add (cond ka 0 (cond ((cO u p.domain.toNat (p.wires.map (aK p.domain.toNat))) (aK p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((cO u p.domain.toNat (p.wires.map (aK p.domain.toNat))) (aK p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Y => bg p.domain w.1)) (dh p.domain.toNat (aK p.domain.toNat a.1) ka)) (dh p.domain.toNat (aK p.domain.toNat b.1) kb))))
    (or ((cO u p.domain.toNat (p.wires.map (aK p.domain.toNat))) (zN op (aK p.domain.toNat a.1) (aK p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Y => bg p.domain w.1)) (dh p.domain.toNat (aK p.domain.toNat a.1) ka)) (dh p.domain.toNat (aK p.domain.toNat b.1) kb)))) (and ((cO u p.domain.toNat (p.wires.map (aK p.domain.toNat))) (aK p.domain.toNat a.1)) ((cO u p.domain.toNat (p.wires.map (aK p.domain.toNat))) (aK p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Y => bg p.domain w.1)) (dh p.domain.toNat (aK p.domain.toNat a.1) ka)) (dh p.domain.toNat (aK p.domain.toNat b.1) kb)))) (dQ p.domain.toNat (zN op (aK p.domain.toNat a.1) (aK p.domain.toNat b.1))) false)) = true := h
  rw [kU,f0,fZ,fZ,fZ,jW,jW] at h
  have ca : bg p.domain (bin op a.1 b.1)=true → bf u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [bf,bg,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [gb,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => bg p.domain w.1) - cg (fun w : Y => bg p.domain w.1) a ka -
      cg (fun w : Y => bg p.domain w.1) b kb = c at h ⊢
    generalize bg p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize bf u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem lp (m : Nat) (l : List Nat) : da m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [da]
  | cons a l ih =>
    change or (Nat.beq m a) (da m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def g1 (fl : Nat → Option (List Nat)) (l : dw) (i j op : Nat) (ka kb : Bool) : Bool :=
  bJ (l.2.2.2.2.1.getD i 0) fun x => bJ (l.2.2.2.2.1.getD j 0) fun y => bJ (zN op x y) fun z =>
  Option.rec false (fun ys => d5 (fun v => v) ys fun ys =>
    and (da z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (da v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (da v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem pZ (xs : List Sig) : eX xs = (xs.map cU).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+cU x) a = a+(xs.map cU).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem ir (f : Y → Nat) {ws : List Y} {a b : Y} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((bA ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Y} {x : Y} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [bA,cK,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem mr {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : et u op=true)
    (h : gb u p ws k a b op ka kb=true) :
    dU u p k ((bA ws a b ka kb).map Prod.fst) (cN op a b)=true := by
  let const := fun w : Y => bg p.domain w.1
  let z := bin op a.1 b.1
  let rest := bA ws a b ka kb
  have ck := pY const ws a b ka kb
  change ws.countP const - cg const a ka - cg const b kb ≤ rest.countP const at ck
  simp only [gb,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := ir (dV u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((bA ws a b ka kb).map (dV u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (bf u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : bf u p.domain p.wires w.1
    · simp [dV,e] at v
    · rfl
  have opOK : (!(!bf u p.domain p.wires z) || d1 u p.domain p.wires (cN op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [d1,cN,x,y,al]
  change k+p.paid+(!bf u p.domain p.wires z).toNat < p.bound+(ws.countP const - cg const a ka -
        cg const b kb+(bg p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : bH (cN op a b)=z := rfl
  simp only [dU,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!bf u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if bg p.domain z then 1 else 0)
  cases hc' : bg p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem kV (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : aK one.toNat v = v.toNat := by
    rw [e8]
    congr 1
    exact BitVec.and_allOnes
  have := kU op one a b
  rwa [e,e,e] at this
theorem on (ws : List Y) (i : Nat) :
    (ws.map (fun w : Y => w.1.toNat)).getD i 0 = (ws.getD i bW).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem kO {c : bL} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (aI c i).1 ≠ (aI c j).1 := by
  have gi : aI c i = c.2.2.1[i] := by simp [aI,List.getD_eq_getElem?_getD,hi]
  have gj : aI c j = c.2.2.1[j] := by simp [aI,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem qq {c : bL} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : g1 fl (df c) i j op ka kb=true) :
    (c.2.2.2.2.2 (eX (bH (cN op (aI c i) (aI c j)) ::
      (bA c.2.2.1 (aI c i) (aI c j) ka kb).map Prod.fst))).any (eJ
      (bH (cN op (aI c i) (aI c j)) ::
      (bA c.2.2.1 (aI c i) (aI c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : aI c t ∈ c.2.2.1 := by
    simp [aI,List.getD_eq_getElem?_getD,ht]
  have hne := kO nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : aI c i ≠ aI c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := iT nd ha hb ka kb v
  have sum := ir (fun w : Y => cU w.1) ha hb hab ka kb
  have wi : aI c i = c.2.2.1.getD i bW := rfl
  have wj : aI c j = c.2.2.1.getD j bW := rfl
  simp only [g1,df,dy,on,←wi,←wj,kV] at h
  generalize aI c i=a at *
  generalize aI c j=b at *
  change Option.rec false _ (fl (cU (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Y => w.1.toNat)).map kwN).sum -
    (cond ka 0 (cU a.1)) - (cond kb 0 (cU b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Y => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Y => cU w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : eX (bH (cN op a b) :: (bA c.2.2.1 a b ka kb).map Prod.fst) =
      cU (bin op a.1 b.1)+((bA c.2.2.1 a b ka kb).map (fun w : Y => cU w.1)).sum := by
    rw [pZ,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize eX (bH (cN op a b) :: (bA c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [gN,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,lp,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [eJ,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def gI (fl : Nat → Option (List Nat)) (l : dw) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => gJ s i j op ka kb) (g1 fl l i j op ka kb))) (d0 l.1 i j op ka kb)
theorem mq {c : bL} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : gI fl (df c) i j op ka kb=true) :
    d0 c i j op ka kb=true := by
  simp only [gI,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : et c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [et] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : aI c t ∈ c.2.2.1 := by
      simp [aI,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := kO nd hi hj (fun e => by simp [e] at hn)
    have closed := mr (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (mu ok)
    have cut : c.2.2.2.2.1.any (fun p => dU c.2.2.2.1.2 p (c.1-1)
        ((bA c.2.2.1 (aI c i) (aI c j) ka kb).map Prod.fst)
        (cN op (aI c i) (aI c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [d0,dM,ey,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := qq nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [d0,dM,ey,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def fm (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def eo (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem ux : ∀ v : Fin 144, eo v.val=true → ∀ t : Fin 9, fm v.val t.val<9 ∧
    fq (cY v.val) (inputs.getD t.val zero) = inputs.getD (fm v.val t.val) zero := by decide +kernel
theorem uw {v t : Nat} (hv : eo v=true) (ht : t<9) : fm v t<9 ∧
    fq (cY v) (inputs.getD t zero) = inputs.getD (fm v t) zero := by
  have lt : v<144 := by
    simp only [eo,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact ux ⟨v,lt⟩ hv ⟨t,ht⟩
def gR (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => fm v t) t
theorem pV {perm : List Nat} (ok : perm.all eo=true) {t : Nat} (ht : t<9) :
    bd (perm.map cY).reverse (inputs.getD t zero) = inputs.getD (gR perm t) zero := by
  rw [bd,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := uw ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def fE : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => bJ (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => fE n (bits >>> 10) (ws++[z])
theorem l9 (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Y) :
    (eT n bits ds).map (fun w => F w.1) = fE n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Y) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i bW).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [fE,dy,eT,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem s6 {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (dr bits ws).map f = dr bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,dr,dr]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def gK (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (dt g.mask).map fun e => (inputs.getD (gR perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  bJ (iE (g.levels k) (dt g.mask).length i) fun rec =>
  dr (rec >>> len) (fE depth (rec &&& ((1 <<< len)-1)) raw)
theorem mt (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all eo=true) :
    gK g k i perm = ((bP g k i).map (bd (perm.map cY).reverse)).map BitVec.toNat := by
  let ms := (perm.map cY).reverse
  let F (a : Sig) : Nat := (bd ms a).toNat
  have F0 : F zero=0 := by
    change (bd ms zero).toNat=0
    rw [ec,(kn _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (bd ms (bin op a b)).toNat = zN op (bd ms a).toNat (bd ms b).toNat
    rw [kV,ec,km,ec,ec]
  have raw : (dY g).map (fun w => F w.1) = (dt g.mask).map fun e => (inputs.getD (gR perm e.1) zero).toNat := by
    simp only [dY,f6,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := kq hm
    exact congrArg BitVec.toNat (pV ok hj)
  have len : (dY g).length = (dt g.mask).length := by simp [dY,f6]
  unfold gK bP f8
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [dy,kr,len]
  rw [List.map_map,List.map_map,s6,←raw,←l9 F F0 Fb]
  rfl
noncomputable def jF (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all eo) (some (gK g k pair.1 perm)) none
noncomputable def d4 (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (jF g (k-1))
noncomputable def h8 (fl : Nat → Option (List Nat)) (u : Bool) (b : ep) (xs : List dw) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := eF b i
    let b' := eF b j
    let z := ee op a b'
    let mask := fI r (gf cov (dS (!u) a) (dS (!u) b') ka kb ||| dS (!u) z)
    fc (fun c => gI fl c i j op ka kb) mask xs

theorem lq {fl u} (k n) (xs : List bL) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : h8 fl u (dg k n xs) (xs.map df) i j op ka kb=true) :
    d0 xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : d0 xs[q] i j op ka kb =
      if len>k then true else if gD xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !cd (bO op (aI xs[q] i) (aI xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(bO op (aI xs[q] i) (aI xs[q] j)).1)
      then true else ey u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((bA xs[q].2.2.1 (aI xs[q] i) (aI xs[q] j) ka kb).map Prod.fst)
        (cN op (aI xs[q] i) (aI xs[q] j)) := by
    simp only [d0,dM,budget,arity,mode,len,gD] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := em xs.length
    let a := eF (dg k n xs) i
    let b := eF (dg k n xs) j
    let cov := f2 (fun c : bL => c.2.2.2.1.1) xs
    change (if len>k then true else fc _ (fI r
       (gf cov (dS (!u) a) (dS (!u) b) ka kb |||
        dS (!u) (ee op a b))) (xs.map df)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := jE k n xs hi
    have cb : b = _ := jE k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,sn,hA,hA,hA,uM,gZ] at pass
    by_cases hit : gD xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply mq nd hfl
      have m := rE _ _ _ q (by simpa using hq) (by
        rw [rD _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def h9 (fl : Nat → Option (List Nat)) (u : Bool) (b : ep) (xs : List dw) (i j op : Nat) :=
  let f := h8 fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def fA (fl : Nat → Option (List Nat)) (u : Bool) (b : ep) (xs : List dw) (i : Nat) (js : List Nat) :=
    js.all (fun j => (ed u).all (h9 fl u b xs i j))
noncomputable def ew (fl : Nat → Option (List Nat)) (u : Bool) (b : ep) (xs : List dw) : List Nat → Bool
  | [] => true
  | i::js => fA fl u b xs i js && ew fl u b xs js

theorem lr {fl u} (k n) (xs : List bL) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : ew fl u (dg k n xs) (xs.map df) js=true) :
    dD xs[q] (js.map (aI xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [ew,Bool.and_eq_true,fA,List.all_eq_true] at allRows
    simp only [List.map_cons,dD,hP,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @lq fl u k n xs i j op
    simp only [h9,Bool.and_eq_true] at pass
    simp only [el,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def hJ (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List bL) :=
    ew fl u (dg k n xs) (xs.map df) (List.range n)
theorem s2 {fl u k n} {xs : List bL} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : hJ fl u k n xs=true) : dD xs[q] xs[q].2.2.1=true := by
  have all := lr k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (aI xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [aI,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def eA (g : Forest) (k i : Nat) : bL :=
  let raw := dY g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := f8 g k i
  let rules := (iD (g.levels k) raw.length i).filterMap (fun (a,b) => fB g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (ea g (k-1))).toList
  (k,ws.length,ws,ff g.mode ws,rules,ls)

theorem mv (g : Forest) (k i tag : Nat) (ys) (h : d4 g k tag=some ys) :
    ∃ xs ∈ (eA g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (ea g (k-1))).toList, _
  unfold d4 at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,jF] at h
    simp only [Option.bind_some,ea]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all eo with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(bP g (k-1) pair.1).map (bd (perm.map cY).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (mt g _ _ hv)

def hC (T : Sig) (c : bL) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem mD (g : Forest) (k i : Nat) :
    dR g k i = (hC (aY g) (eA g k i) &&
      (if k=0 then true else dD (eA g k i) (eA g k i).2.2.1)) := rfl

theorem rC {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → dR g k i = true) :
    Q g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Q,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def d2 (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (eA g k)
def iQ (g : Forest) (k start n ar : Nat) :=
  (d2 g k start n).all (fun c => c.2.1==ar && hC (aY g) c)
noncomputable def dq (g : Forest) (k start n ar lo len : Nat) :=
  let xs := d2 g k start n
  let b := dg k ar xs
  gM xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    fA (d4 g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem hH {g k start n ar lo len} (h : dq g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    fA (d4 g k) g.mode (dg k ar (d2 g k start n)) ((d2 g k start n).map df)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [dq,iC] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem s1 {g k start n ar lo a b}
    (h : dq g k start n ar lo a=true) (t : dq g k start n ar (lo+a) b=true) :
    dq g k start n ar lo (a+b)=true := by
  simp only [dq,iC]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact hH h (lo+j) (by omega) (by omega)
  · exact hH t (lo+j) (by omega) (by omega)

theorem l8 {g k start n ar} (h : dq g k start n ar 0 ar=true) :
    hJ (d4 g k) g.mode k ar (d2 g k start n)=true := by
  let xs := d2 g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      ew (d4 g k) g.mode (dg k ar xs) (xs.map df) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,ew,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := hH h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold hJ
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem l7 {g k start n ar} (hd : iQ g k start n ar=true)
    (h : dq g k start n ar 0 ar=true) : Q g k start n=true := by
  apply rC
  intro i lo hi
  let xs := d2 g k start n
  have hm : eA g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [hC,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, d4 g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => mv g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [mD,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ s2 hq hb ha hm nd hfl hn (l8 h)

def aC (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => dq g k start n ar lo num=true
  | d+1 => aC g k start n ar lo (num/2) d ∧ aC g k start n ar (lo+num/2) (num-num/2) d
theorem lE {g k start n ar lo num d} (h : aC g k start n ar lo num d) :
    dq g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := s1 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def J (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => iQ g k start n ar=true ∧ aC g k start n ar 0 ar rows
  | d+1 => J g k start (n/2) ar rows d ∧ J g k (start+n/2) (n-n/2) ar rows d
theorem aE {g k start n ar rows d} (h : J g k start n ar rows d) :
    Q g k start n=true := by
  induction d generalizing start n with
  | zero => exact l7 h.1 (lE h.2)
  | succ d ih =>
    have v := ba (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def bB {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => bB f (xs.take (xs.length/2)) d ∧ bB f (xs.drop (xs.length/2)) d
theorem aQ {α f xs d} (h : @bB α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem uu {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : aN T) (h : ac u raw T L) :
    dF u raw T one L := by
  refine ⟨id,raw,fun r => cH r,fun a ha => ?_,g9 pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem dB {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, ac u (ad q) (K q) (prior q))
    (e : (K q == K m && (ad q == aF m) && (prior q == cap+1) && cd (K m) &&
      decide (aF m).Nodup && f5 u one (cap+1) cap 0 (aF m) (aF m)) = true) :
    aH u (K m) cap (aF m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact kj (uu (dm _ e4) h) [] rfl e5 e6

theorem bk {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, ac u (ad q) (K q) (prior q)) (ci : bw)
    (ok : eR m ci prior = true)
    (cut : (decide ws.Nodup && f5 u (ej ci.1 ci.2.1) ci.2.2.2.2 cap 0 (ad (eh m ci)) ws)=true) :
    aH u (K m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact kj (eS ci prior low ok) [] rfl cut.1 cut.2

theorem d6 {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, ac u (ad q) (K q) (prior q))
    (geom : aJ g prior = true) (blocks : cI g cap)
    (idx : d7 g cap i ws = true) : aH u (K m) cap ws.toFinset := by
  subst hm
  subst hu
  exact hG low geom blocks (Nat.le_refl _) idx

def ix (m hints : Nat) : Bool :=
  let xs := gQ m hints
  cd (K m) && db (K m) (aF m) xs && (xs.map Prod.fst == aF m)
theorem cF {u} {m hints cap : Nat} (ok : ix m hints = true)
    (a : aH u (K m) cap (aF m).toFinset) : ac u (aF m) (K m) (cap+1) := by
  simp only [ix,Bool.and_eq_true,beq_iff_eq] at ok
  apply jJ (dm _ ok.1.1) (dc ok.1.2).1 (dc ok.1.2).2 _ a
  intro v hv
  apply eU ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def vK (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((dt m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fJ (m : Nat) (rs : List Nat) : Bool :=
  let xs := vK m rs
  db (K m) (ad m) xs && (xs.map Prod.fst == aF m) &&
    cd (K m) && decide (ad m = aF m ++ [gg (m/512-1)])
theorem mE {u} {m : Nat} {rs : List Nat} (ok : fJ m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (K m) k S) (sub : ∀ v ∈ S, v ∈ ad m) :
    S=(aF m).toFinset ∨ S=(ad m).toFinset := by
  simp only [fJ,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ aF m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := eU ess v (List.mem_toFinset.mpr hv)
    exact fj h (ad m) v sub r s hd hi
  have mem : ∀ v, v ∈ ad m ↔ v ∈ aF m ∨ v=gg (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : gg (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem aG {u} {m q cap : Nat} {rs : List Nat} (ok : fJ m rs = true)
    (e : K m = K q) (ev : aF m = aF q)
    (a : aH u (K q) cap (aF q).toFinset)
    (b : aH u (K q) cap (ad m).toFinset) :
    ac u (ad m) (K m) (cap+1) := by
  have ok' := ok
  simp only [fJ,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := f7 (dm _ ok'.1.2) (dc ok'.1.1.1).1 (dc ok'.1.1.1).2 hr ha
  by_contra! small
  rcases mE ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
structure cS (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def gV (T : Sig) : cS {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def jC {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : cS (insert (bin d a b) U) T) : cS (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem gX {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem gW {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (cS S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨gV T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := gX tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨jC d01 ha hb fresh H⟩

def bn (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem dO {S T v p n} (H : cS S T) (one : bn S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem qm {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : bn S T a p na) (B : bn S T b p nb)
    (C : bn S T a pa n) (D : bn S T b pb n) : aH false T k S := by
  intro j hj run
  have lb := gX run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := gW run tight
  exact different (H.unique (H.rect (dO H A) (dO H C)) (H.rect (dO H B) (dO H D)))
structure dv (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure cn (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : cS inner pivot
  outside : dv outer T pivot

def mA {S T} (D : cS S T) (h : Sig) : dv S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect

def iG {S T h} (D : dv S T h) : dv (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩

def mm {S T} (D : cS S T) : cn S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }

def iF {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : dv (insert (bin d a b) U) T h) : dv (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kt {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB

def mk {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : cn (insert (bin d a b) U) T) :
    cn (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := kt F.cover F.apart inn freshA freshB freshZ
    have old : cS (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,jC hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := kt ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : dv (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      iF hd ha hb (by simp [z]) old⟩

def iy {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : cS (insert (bin d a b) U) T) :
    cn (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : dv (insert z (U.erase a)) T a := set0 ▸ iG (mA H a)
  have H1 := iF hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : dv (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,gV a,iG H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp

theorem sl {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (cn S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨mm (gV T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := gX tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := gW tail (by change (insert z U).card=k+1; omega)
        exact ⟨iy hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := gW tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : cS (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := iy hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨mk hd01 fa fb zU F⟩
theorem ml {S : Finset Sig} {T : Sig} (F : cn S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)

theorem fF {S : Finset Sig} {T : Sig} (F : cn S T) {a p n} (ao : a∈F.outer)
    (one : bn S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw

theorem sm {S : Finset Sig} {T : Sig} (F : cn S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : bn S T a p na) (B : bn S T b p nb)
    (C : bn S T a pa n) (D : bn S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (fF F aout A) (fF F aout C))
    (F.outside.rect (fF F bout B) (fF F bout D)))

theorem pW {S : Finset Sig} {T : Sig} (F : cn S T) {a b p n pa pb na nb}
    (different : a≠b) (A : bn F.inner F.pivot a p na) (B : bn F.inner F.pivot b p nb)
    (C : bn F.inner F.pivot a pa n) (D : bn F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (dO F.inside A) (dO F.inside C))
    (F.inside.rect (dO F.inside B) (dO F.inside D)))
theorem eD {S : Finset Sig} {T : Sig} (F : cn S T) {v p n}
    (hv : v∈F.inner) (only : bn S T v p n) : bn F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply ml F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn

theorem bl {S : Finset Sig} {T : Sig} (F : cn S T) {a b c p n pa na}
    (ar : bn S T a p na) (br : bn S T b pa n) (cr : bn S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := eD F ia ar
  have bh := eD F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi

theorem cc {S : Finset Sig} {T : Sig} (F : cn S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : bn S T a p na) (h2 : bn S T b p nb)
    (h3 : bn S T a pa n) (h4 : bn S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact pW F ne (eD F ia h1) (eD F ib h2)
      (eD F ia h3) (eD F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact sm F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def d9 (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem eY {ws T v p n} (h : d9 ws T v p n=true) :
    bn ws.toFinset T v p n := by
  simp only [d9,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def dP (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def eZ (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := dP pos (field 2)
  let n := dP neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    d9 ws T a p (dP neg (field 4)) && d9 ws T b p (dP neg (field 5)) &&
    d9 ws T a (dP pos (field 6)) n && d9 ws T b (dP pos (field 7)) n
theorem jD {pos neg T ws k v} (h : eZ pos neg T ws k v=true) : aH false T k ws.toFinset := by
  simp only [eZ,Bool.and_eq_true,decide_eq_true_eq] at h
  exact qm h.1.1.1.1.1 h.1.1.1.1.2 (eY h.1.1.1.2)
    (eY h.1.1.2) (eY h.1.2) (eY h.2)

def Z (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → dR g k j=true ∨ aH g.mode (aY g) k (bP g k j).toFinset
theorem az (g : Forest) (k a : Nat) : Z g k a 0 := by
  intro j lo hi
  omega
theorem aM {g k a n} (h : Q g k a n=true) : Z g k a n :=
  fun j lo hi => Or.inl (gA h j lo hi)
theorem X {g k a x y} (first : Z g k a x) (last : Z g k (a+x) y) :
    Z g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def qn (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => eZ pos neg (aY g) (bP g k (a+j)) k (bo data (32*j) 32))
theorem bZ {pos neg g k a n data} (mode : g.mode=false) (h : qn pos neg g k a n data=true) :
    Z g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change eZ pos neg _ (bP g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact jD hh

def cE (g : Forest) (top : Nat) := ∀ k ≤ top, Z g k 0 (g.levels k).1
theorem rJ (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, ac g.mode (ad q) (K q) (prior q))
    (geometry : aJ g prior=true) (rows : cE g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, aH g.mode (aY g) k (bP g k i).toFinset := by
  simp only [aJ,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact f1 g 0 i (fD geometry.1.1.1 geometry.1.1.2)
        (fun x hx => eS _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact f1 g _ i (fD geometry.1.1.1 geometry.1.1.2)
        (fun x hx => eS _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem jT {g top prior k i ws} (lower : ∀ q, ac g.mode (ad q) (K q) (prior q))
    (geom : aJ g prior=true) (blocks : cE g top) (le : k≤top)
    (idx : d7 g k i ws=true) : aH g.mode (aY g) k ws.toFinset := by
  simp only [d7,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←hK idx.2]
  exact rJ g top prior lower geom blocks _ le i idx.1
abbrev dx := Nat × Nat × Nat
def dT (arity : Nat) (tags : List dx) : Prop :=
  ∀ {S T}, (F : cn S T) → (w : Nat → Sig) → (p n : Nat → Row) →
    (∀ i<arity, w i∈S) → (∀ i<arity, ∀ j<arity, i≠j → w i≠w j) →
    (∀ t∈tags, bn S T (w t.1) (p t.2.1) (n t.2.2)) → False
structure hV where
  arity : Nat
  tags : List dx
  closed : dT arity tags
def j4 : List dx := [(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
theorem sq (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A2 → A1) → (A0 → A3 → A1) → (A2 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u1 : A1
  · by_cases u0 : A0
    · exact r0 (Or.inl ⟨u0,u1⟩)
    · by_cases u3 : A3
      · exact u0 (r2 u1 u3)
      · by_cases u2 : A2
        · exact u3 (r5 u2 u1)
        · exact r1 (Or.inr ⟨u2,u3⟩)
  · by_cases u0 : A0
    · by_cases u3 : A3
      · exact u1 (r4 u0 u3)
      · by_cases u2 : A2
        · exact u1 (r3 u0 u2)
        · exact r1 (Or.inr ⟨u2,u3⟩)
    · exact r0 (Or.inr ⟨u0,u1⟩)
theorem sp : dT 4 j4 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,2) (by decide)
  have c1 := J (1,1,2) (by decide)
  have c2 := J (2,2,3) (by decide)
  have c3 := J (3,3,3) (by decide)
  have c4 := J (0,4,1) (by decide)
  have c5 := J (1,4,3) (by decide)
  have c6 := J (2,5,0) (by decide)
  have c7 := J (3,5,1) (by decide)
  have c8 := J (3,5,2) (by decide)
  have r0 := cc F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := cc F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := bl F c5 c7 c4
  have r3 := bl F c4 c2 c5
  have r4 := bl F c4 c3 c5
  have r5 := bl F c6 c1 c8
  exact sq (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def j5 : List dx := [(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
theorem ss (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A3 → A1) → (A2 → A0 → A3) → (A3 → A1 → A2) → (A0 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u3 : A3
  · by_cases u0 : A0
    · exact r1 (Or.inl ⟨u0,u3⟩)
    · by_cases u1 : A1
      · by_cases u2 : A2
        · exact r0 (Or.inl ⟨u1,u2⟩)
        · exact u2 (r4 u3 u1)
      · by_cases u2 : A2
        · exact u1 (r2 u2 u3)
        · exact r0 (Or.inr ⟨u1,u2⟩)
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact u3 (r5 u0 u1)
      · by_cases u2 : A2
        · exact u3 (r3 u2 u0)
        · exact r0 (Or.inr ⟨u1,u2⟩)
    · exact r1 (Or.inr ⟨u0,u3⟩)
theorem sr : dT 4 j5 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,1) (by decide)
  have c1 := J (1,1,3) (by decide)
  have c2 := J (2,2,0) (by decide)
  have c3 := J (1,2,2) (by decide)
  have c4 := J (3,3,1) (by decide)
  have c5 := J (2,3,3) (by decide)
  have c6 := J (3,4,2) (by decide)
  have c7 := J (0,4,3) (by decide)
  have r0 := cc F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := cc F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4
  have r2 := bl F c2 c6 c3
  have r3 := bl F c5 c0 c4
  have r4 := bl F c4 c1 c5
  have r5 := bl F c7 c3 c6
  exact ss (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def j6 : List dx := [(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
theorem sx (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A2) → (A2 → A0 → A1) → False := by
  intro r0 r1 r2 r3 r4
  by_cases u2 : A2
  · by_cases u1 : A1
    · exact r0 (Or.inl ⟨u1,u2⟩)
    · by_cases u3 : A3
      · exact r2 (Or.inl ⟨u2,u3⟩)
      · by_cases u0 : A0
        · exact u1 (r4 u2 u0)
        · exact r1 (Or.inr ⟨u0,u3⟩)
  · by_cases u1 : A1
    · by_cases u3 : A3
      · exact u2 (r3 u1 u3)
      · exact r2 (Or.inr ⟨u2,u3⟩)
    · exact r0 (Or.inr ⟨u1,u2⟩)
theorem sv : dT 4 j6 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,2) (by decide)
  have c1 := J (1,1,1) (by decide)
  have c2 := J (2,2,0) (by decide)
  have c3 := J (1,2,2) (by decide)
  have c4 := J (3,3,0) (by decide)
  have c5 := J (0,3,1) (by decide)
  have c6 := J (2,4,1) (by decide)
  have c7 := J (3,4,2) (by decide)
  have r0 := cc F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6
  have r1 := cc F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7
  have r2 := cc F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4
  have r3 := bl F c3 c4 c2
  have r4 := bl F c2 c0 c3
  exact sx (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def j7 : List dx := [(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
theorem sA (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (A3 → A1 → A2) → (A2 → A1 → A3) → (A0 → A2 → A1) → (A0 → A3 → A1) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u1 : A1
  · by_cases u0 : A0
    · exact r1 (Or.inl ⟨u0,u1⟩)
    · by_cases u2 : A2
      · by_cases u3 : A3
        · exact r0 (Or.inl ⟨u2,u3⟩)
        · exact u3 (r3 u2 u1)
      · by_cases u3 : A3
        · exact u2 (r2 u3 u1)
        · exact r0 (Or.inr ⟨u2,u3⟩)
  · by_cases u0 : A0
    · by_cases u2 : A2
      · exact u1 (r4 u0 u2)
      · by_cases u3 : A3
        · exact u1 (r5 u0 u3)
        · exact r0 (Or.inr ⟨u2,u3⟩)
    · exact r1 (Or.inr ⟨u0,u1⟩)
theorem sy : dT 4 j7 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,0) (by decide)
  have c1 := J (1,1,0) (by decide)
  have c2 := J (2,2,3) (by decide)
  have c3 := J (3,3,3) (by decide)
  have c4 := J (2,4,1) (by decide)
  have c5 := J (3,4,2) (by decide)
  have c6 := J (1,5,1) (by decide)
  have c7 := J (1,5,2) (by decide)
  have c8 := J (0,5,3) (by decide)
  have r0 := cc F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3
  have r1 := cc F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1
  have r2 := bl F c5 c6 c4
  have r3 := bl F c4 c7 c5
  have r4 := bl F c8 c4 c6
  have r5 := bl F c8 c5 c7
  exact sA (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def j8 : List dx := [(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
theorem sC (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A3 → A1) → (A2 → A0 → A3) → (A2 → A1 → A3) → False := by
  intro r0 r1 r2 r3 r4 r5
  by_cases u3 : A3
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact r0 (Or.inl ⟨u0,u1⟩)
      · exact u1 (r3 u0 u3)
    · by_cases u1 : A1
      · exact u0 (r2 u1 u3)
      · exact r0 (Or.inr ⟨u0,u1⟩)
  · by_cases u0 : A0
    · by_cases u1 : A1
      · exact r0 (Or.inl ⟨u0,u1⟩)
      · by_cases u2 : A2
        · exact u3 (r4 u2 u0)
        · exact r1 (Or.inr ⟨u2,u3⟩)
    · by_cases u1 : A1
      · by_cases u2 : A2
        · exact u3 (r5 u2 u1)
        · exact r1 (Or.inr ⟨u2,u3⟩)
      · exact r0 (Or.inr ⟨u0,u1⟩)
theorem sB : dT 4 j8 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,3) (by decide)
  have c1 := J (1,1,3) (by decide)
  have c2 := J (2,2,3) (by decide)
  have c3 := J (3,3,3) (by decide)
  have c4 := J (0,4,1) (by decide)
  have c5 := J (1,4,2) (by decide)
  have c6 := J (2,5,0) (by decide)
  have c7 := J (3,5,1) (by decide)
  have c8 := J (3,5,2) (by decide)
  have r0 := cc F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := cc F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := bl F c5 c7 c4
  have r3 := bl F c4 c8 c5
  have r4 := bl F c6 c4 c7
  have r5 := bl F c6 c5 c8
  exact sC (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def j9 : List dx := [(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
theorem sE (A0 A1 A2 A3 A4 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A0 → A1) → (A3 → A1 → A2) → (A0 → A1 → A2) → (A2 → A4 → A1) → (A3 → A2 → A4) → False := by
  intro r0 r1 r2 r3 r4 r5 r6
  by_cases u2 : A2
  · by_cases u1 : A1
    · exact r0 (Or.inl ⟨u1,u2⟩)
    · by_cases u0 : A0
      · exact u1 (r2 u2 u0)
      · by_cases u3 : A3
        · by_cases u4 : A4
          · exact u1 (r5 u2 u4)
          · exact u4 (r6 u3 u2)
        · exact r1 (Or.inr ⟨u0,u3⟩)
  · by_cases u1 : A1
    · by_cases u0 : A0
      · exact u2 (r4 u0 u1)
      · by_cases u3 : A3
        · exact u2 (r3 u3 u1)
        · exact r1 (Or.inr ⟨u0,u3⟩)
    · exact r0 (Or.inr ⟨u1,u2⟩)
theorem sD : dT 5 j9 := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,2) (by decide)
  have c1 := J (1,1,3) (by decide)
  have c2 := J (2,2,0) (by decide)
  have c3 := J (1,2,4) (by decide)
  have c4 := J (3,3,1) (by decide)
  have c5 := J (2,3,3) (by decide)
  have c6 := J (0,3,4) (by decide)
  have c7 := J (3,4,2) (by decide)
  have c8 := J (4,4,3) (by decide)
  have c9 := J (4,4,4) (by decide)
  have r0 := cc F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := cc F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7
  have r2 := bl F c2 c6 c3
  have r3 := bl F c4 c1 c5
  have r4 := bl F c6 c1 c5
  have r5 := bl F c2 c9 c3
  have r6 := bl F c7 c5 c8
  exact sE (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def kc : List dx := [(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
theorem sG (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A1 ∧ A3) ∨ (¬A1 ∧ ¬A3)) → False) → (A2 → A1 → A3) → (A0 → A3 → A1) → False := by
  intro r0 r1 r2 r3 r4
  by_cases u1 : A1
  · by_cases u3 : A3
    · exact r2 (Or.inl ⟨u1,u3⟩)
    · by_cases u0 : A0
      · exact r1 (Or.inl ⟨u0,u1⟩)
      · by_cases u2 : A2
        · exact u3 (r3 u2 u1)
        · exact r0 (Or.inr ⟨u2,u3⟩)
  · by_cases u3 : A3
    · by_cases u0 : A0
      · exact u1 (r4 u0 u3)
      · exact r1 (Or.inr ⟨u0,u1⟩)
    · exact r2 (Or.inr ⟨u1,u3⟩)
theorem sF : dT 4 kc := by
  intro S T F w p n mem diff J
  have c0 := J (0,0,0) (by decide)
  have c1 := J (1,1,0) (by decide)
  have c2 := J (2,2,3) (by decide)
  have c3 := J (2,3,1) (by decide)
  have c4 := J (3,3,2) (by decide)
  have c5 := J (1,4,2) (by decide)
  have c6 := J (0,4,3) (by decide)
  have c7 := J (1,5,1) (by decide)
  have c8 := J (3,5,3) (by decide)
  have r0 := cc F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8
  have r1 := cc F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1
  have r2 := cc F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4
  have r3 := bl F c3 c5 c4
  have r4 := bl F c6 c4 c5
  exact sG (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def sH : Nat → hV
  | 0 => ⟨4,j4,sp⟩
  | 1 => ⟨4,j5,sr⟩
  | 2 => ⟨4,j6,sv⟩
  | 3 => ⟨4,j7,sy⟩
  | 4 => ⟨4,j8,sB⟩
  | 5 => ⟨5,j9,sD⟩
  | _ => ⟨4,kc,sF⟩
def sL (arity : Nat) (ws : List Sig) (w : Nat→Sig) :=
  (List.range arity).all (fun i => decide (w i∈ws) &&
    (List.range arity).all (fun j => (i==j) || decide (w i≠w j)))
def kd (pc : hV) (ws : List Sig) (T : Sig) (w : Nat→Sig) (p n : Nat→Row) :=
  sL pc.arity ws w &&
    pc.tags.all (fun t => d9 ws T (w t.1) (p t.2.1) (n t.2.2))
theorem f3 {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
theorem sI {pc ws T w p n} (F : cn (List.toFinset ws) T)
    (h : kd pc ws T w p n=true) : False := by
  have ij := (f3 h).1
  have hrow (i : Nat) (hi : i<pc.arity) := f3
    (List.all_eq_true.mp ij i (List.mem_range.mpr hi))
  apply pc.closed F w p n
  · intro i hi
    exact List.mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
  · intro i hi j hj ne
    have one := List.all_eq_true.mp (hrow i hi).2 j (List.mem_range.mpr hj)
    have diff : (i==j)=false := beq_eq_false_iff_ne.mpr ne
    simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
  · intro t ht
    exact eY (List.all_eq_true.mp (f3 h).2 t ht)

def f4 (pos neg : Nat) (ws : List Sig) (T : Sig) (k rec : Nat) :=
  let field := fun i => (rec >>> (4*i)) &&& 15
  decide (k≤ws.toFinset.card) && kd (sH (field 0)) ws T
    (fun i => ws.getD (field (1+i)) zero)
    (fun i => dP pos (field (6+i))) (fun i => dP neg (field (12+i)))
theorem kf {pos neg ws T k rec} (ok : f4 pos neg ws T k rec=true) :
    aH false T k ws.toFinset := by
  obtain ⟨bound,check⟩ := f3 ok
  intro j hj live
  obtain ⟨F⟩ := sl live (hj.trans (of_decide_eq_true bound))
  exact sI F check
def aU : Nat := 0x9050141084210842110c0300c03
def aT : Nat := 0xc9606290568325147434114642a
def sK (pos neg : Nat) (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun i => f4 pos neg (bP g k (start+i)) (aY g) k (bo data (68*i) 68))
theorem bi {pos neg g k start n data} (mode : g.mode=false)
    (ok : sK pos neg g k start n data=true) : Z g k start n := by
  intro j lo hi
  right
  rw [mode]
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  change f4 pos neg (bP g k (start+(j-start))) (aY g) k _=true at h
  rw [e] at h
  exact kf h
def hB (pos neg : Nat) (g : Forest) (k i : Nat) (kw panels : Nat→Nat) (tag : Nat) :=
  if tag=0 then dR g k i else if tag<128 then
    eZ pos neg (aY g) (bP g k i) k (bo kw (32*(tag-1)) 32)
  else f4 pos neg (bP g k i) (aY g) k (bo panels (68*(tag-128)) 68)
def sJ (pos neg : Nat) (g : Forest) (k start n : Nat) (kw panels : Nat→Nat) (data : Nat) :=
  (List.range n).all fun j => hB pos neg g k (start+j) kw panels ((data >>> (8*j)) &&& 255)
theorem aB {pos neg g k start n kw panels data} (mode : g.mode=false)
    (h : sJ pos neg g k start n kw panels data=true) : Z g k start n := by
  intro j lo hi
  have one := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have eq : start+(j-start)=j := by omega
  change hB pos neg g k (start+(j-start)) kw panels _=true at one
  rw [eq] at one
  unfold hB at one
  split at one
  · exact Or.inl one
  · right
    rw [mode]
    split at one
    · exact jD one
    · exact kf one
theorem aX {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, ac u (ad q) (K q) (prior q))
    (geom : aJ g prior=true) (blocks : cE g cap)
    (idx : d7 g cap i ws=true) : aH u (K m) cap ws.toFinset := by
  subst hm
  subst hu
  exact jT low geom blocks (Nat.le_refl _) idx
def mR (i : Nat) : Nat := 0xf
def mT : af := (1,0,1,0,0,0,0,mR)
def mV : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mQ : List bw := []
def mP : List (List Nat) := [[],[48,33]]
def mU : Nat → af
  | 3 => mT
  | _ => bS
def mS : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => mV[j]?.getD (0,0),mQ,mP,mU,mS⟩
set_option maxHeartbeats 0 in
theorem oc : aJ g15 (aD []) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ta : Q g15 3 0 1=true := by decide +kernel
theorem k1 : Q g15 3 0 1=true := ta
theorem uD : cI g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q g15 0 0 0 = true)
  · exact (rfl : Q g15 1 0 0 = true)
  · exact (rfl : Q g15 2 0 0 = true)
  · exact k1
set_option maxHeartbeats 0 in
theorem qB : ac true (aF 15) (K 15) 4 := cF (hints:=8449) (by decide +kernel) (d6 (g:=g15) (i:=0) rfl rfl (ag [] h7) oc uD (by decide +kernel))
def fO := au [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxHeartbeats 0 in
theorem kD : ai true fO := aw (m:=15) h7 qB (by decide +kernel)
def nC (i : Nat) : Nat := 0x11a20bf
def nI : af := (1,0,3,0,0,0,0,nC)
def nE (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def nB (i : Nat) : Nat := 0x40828fd20fd10
def nH : af := (2,1,3,0,0,3,0,nB)
def nD (i : Nat) : Nat := 0x300
def nz (i : Nat) : Nat := 0x5dd4520
def nG : af := (1,2,3,0,0,0,0,nz)
def nK : Array (ae × ae) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def ny : List bw := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def iI : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def nJ : Nat → af
  | 6 => nI
  | 5 => nH
  | 4 => nG
  | _ => bS
def nF : Nat → Nat → Option (Nat × Nat)
  | 6 => aR 5 15 3 9 1 4 nE
  | 5 => aR 1 3 1 9 1 4 nD
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => nK[j]?.getD (0,0),ny,iI,nJ,nF⟩
set_option maxHeartbeats 0 in
theorem og : aJ g31 (aD fO) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=1) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tu : Q g31 6 0 1=true := by decide +kernel
theorem ld : Q g31 6 0 1=true := tu
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tt : Q g31 5 0 2=true := by decide +kernel
theorem lc : Q g31 5 0 2=true := tt
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ts : Q g31 4 0 1=true := by decide +kernel
theorem la : Q g31 4 0 1=true := ts
theorem uG : cI g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q g31 0 0 0 = true)
  · exact (rfl : Q g31 1 0 0 = true)
  · exact (rfl : Q g31 2 0 0 = true)
  · exact (rfl : Q g31 3 0 0 = true)
  · exact la
  · exact lc
  · exact ld
set_option maxHeartbeats 0 in
theorem qW : ac true (aF 31) (K 31) 7 := cF (hints:=8449) (by decide +kernel) (d6 (g:=g31) (i:=0) rfl rfl (ag fO kD) og uG (by decide +kernel))
def fT := au fO 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxHeartbeats 0 in
theorem kI : ai true fT := aw (m:=31) kD qW (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rd : ac true (aF 47) (K 47) 5 := cF (hints:=8449) (by decide +kernel) (bk (prior:=aD fT) (ag fT kI) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def fV := au fT 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxHeartbeats 0 in
theorem kL : ai true fV := aw (m:=47) kI rd (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rl : ac true (aF 55) (K 55) 5 := cF (hints:=257) (by decide +kernel) (bk (prior:=aD fV) (ag fV kL) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def fW := au fV 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxHeartbeats 0 in
theorem kM : ai true fW := aw (m:=55) kL rl (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rt : ac true (aF 63) (K 63) 8 := cF (hints:=8449) (by decide +kernel) (bk (prior:=aD fW) (ag fW kM) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def fX := au fW 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxHeartbeats 0 in
theorem kN : ai true fX := aw (m:=63) kM rt (by decide +kernel)
def mI (i : Nat) : Nat := 0x7213f
def mM : af := (1,0,2,0,0,0,0,mI)
def mJ (i : Nat) : Nat := 0x8000
def mH (i : Nat) : Nat := 0x17e51
def mL : af := (1,1,2,0,0,0,0,mH)
def mO : Array (ae × ae) := #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def mG : List bw := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def mF : List (List Nat) := [[],[32,83]]
def mN : Nat → af
  | 6 => mM
  | 5 => mL
  | _ => bS
def mK : Nat → Nat → Option (Nat × Nat)
  | 6 => aR 1 3 1 6 1 1 mJ
  | _ => fun _ => none
def cL : Forest := ⟨111,6,fun j => mO[j]?.getD (0,0),mG,mF,mN,mK⟩
set_option maxHeartbeats 0 in
theorem n9 : aJ cL (aD fX) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s9 : Q cL 6 0 1=true := by decide +kernel
theorem k0 : Q cL 6 0 1=true := s9
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s8 : Q cL 5 0 1=true := by decide +kernel
theorem kZ : Q cL 5 0 1=true := s8
theorem uC : cI cL 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q cL 0 0 0 = true)
  · exact (rfl : Q cL 1 0 0 = true)
  · exact (rfl : Q cL 2 0 0 = true)
  · exact (rfl : Q cL 3 0 0 = true)
  · exact (rfl : Q cL 4 0 0 = true)
  · exact kZ
  · exact k0
set_option maxHeartbeats 0 in
theorem qv : ac true (aF 111) (K 111) 7 := cF (hints:=16785665) (by decide +kernel) (d6 (g:=cL) (i:=0) rfl rfl (ag fX kN) n9 uC (by decide +kernel))
def fM := au fX 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxHeartbeats 0 in
theorem kB : ai true fM := aw (m:=111) kN qv (by decide +kernel)
def mZ (i : Nat) : Nat := 0x163441bf
def m5 : af := (1,0,3,0,0,0,0,mZ)
def m1 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def mY (i : Nat) : Nat := 0x420a3fa41fd10
def m4 : af := (2,1,3,0,0,3,0,mY)
def m0 (i : Nat) : Nat := 0x18000
def mX (i : Nat) : Nat := 0xb7d8d20
def m3 : af := (1,2,3,0,0,0,0,mX)
def m7 : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def mW : List bw := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def iH : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def m6 : Nat → af
  | 7 => m5
  | 6 => m4
  | 5 => m3
  | _ => bS
def m2 : Nat → Nat → Option (Nat × Nat)
  | 7 => aR 9 13 2 9 1 4 m1
  | 6 => aR 1 3 1 9 1 4 m0
  | _ => fun _ => none
def cq : Forest := ⟨189,7,fun j => m7[j]?.getD (0,0),mW,iH,m6,m2⟩
set_option maxHeartbeats 0 in
theorem od : aJ cq (aD fM) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=1) ?_⟩,aQ (d:=2) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem td : Q cq 7 0 1=true := by decide +kernel
theorem k4 : Q cq 7 0 1=true := td
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tc : Q cq 6 0 2=true := by decide +kernel
theorem k3 : Q cq 6 0 2=true := tc
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tb : Q cq 5 0 1=true := by decide +kernel
theorem k2 : Q cq 5 0 1=true := tb
theorem uE : cI cq 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q cq 0 0 0 = true)
  · exact (rfl : Q cq 1 0 0 = true)
  · exact (rfl : Q cq 2 0 0 = true)
  · exact (rfl : Q cq 3 0 0 = true)
  · exact (rfl : Q cq 4 0 0 = true)
  · exact k2
  · exact k3
  · exact k4
set_option maxHeartbeats 0 in
theorem qK : ac true (aF 189) (K 189) 8 := cF (hints:=536879876) (by decide +kernel) (d6 (g:=cq) (i:=0) rfl rfl (ag fM kB) od uE (by decide +kernel))
def fP := au fM 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxHeartbeats 0 in
theorem kE : ai true fP := aw (m:=189) kB qK (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qy : ac true (aF 127) (K 127) 9 := cF (hints:=16785665) (by decide +kernel) (bk (prior:=aD fP) (ag fP kE) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def fN := au fP 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxHeartbeats 0 in
theorem kC : ai true fN := aw (m:=127) kE qy (by decide +kernel)
def m9 (i : Nat) : Nat := 0x8201ff
def nq : af := (1,0,5,0,0,0,0,m9)
def nj (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def ni (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def nv : af := (12,1,5,0,0,10,0,ni)
def nn (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def nh (j : Nat) : Nat := 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def nu : af := (113,2,5,589836,68,12,1057,nh)
def nm (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def ng (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def nt : af := (116,3,5,0,0,11,0,ng)
def nl (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def nf (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def nr : af := (12,4,5,0,0,6,0,nf)
def nx : Array (ae × ae) := #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]
def m8 : List bw := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def gP : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def nw : Nat → af
  | 10 => nq
  | 9 => nv
  | 8 => nu
  | 7 => nt
  | 6 => nr
  | _ => bS
def np : Nat → Nat → Option (Nat × Nat)
  | 10 => aR 16 41 5 10 4 2 nj
  | 9 => aR 67 277 6 13 7 2 nn
  | 8 => aR 100 251 6 13 7 2 nm
  | 7 => aR 4 19 2 10 4 2 nl
  | _ => fun _ => none
def aV : Forest := ⟨191,10,fun j => nx[j]?.getD (0,0),m8,gP,nw,np⟩
set_option maxHeartbeats 0 in
theorem oe : aJ aV (aD fN) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=3) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem te : Q aV 10 0 1=true := by decide +kernel
theorem k5 : Q aV 10 0 1=true := te
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tr : Q aV 9 0 12=true := by
  apply aE (ar:=8) (rows:=0) (d:=2)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem k9 : Q aV 9 0 12=true := tr
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tk : Q aV 8 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tm : Q aV 8 3 36=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tp : Q aV 8 39 31=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tq : Q aV 8 70 36=true := by
  apply aE (ar:=9) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tl : Q aV 8 106 7=true := by
  apply aE (ar:=9) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem k8 : Q aV 8 0 113=true := (@ba aV 8 0 106 7 (@ba aV 8 0 70 36 (@ba aV 8 0 39 31 (@ba aV 8 0 3 36 tk tm) tp) tq) tl)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tg : Q aV 7 0 13=true := by
  apply aE (ar:=7) (rows:=0) (d:=2)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem th : Q aV 7 13 36=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ti : Q aV 7 49 36=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tj : Q aV 7 85 31=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem k7 : Q aV 7 0 116=true := (@ba aV 7 0 85 31 (@ba aV 7 0 49 36 (@ba aV 7 0 13 36 tg th) ti) tj)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tf : Q aV 6 0 12=true := by
  apply aE (ar:=7) (rows:=0) (d:=2)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem k6 : Q aV 6 0 12=true := tf
theorem uF : cI aV 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q aV 0 0 0 = true)
  · exact (rfl : Q aV 1 0 0 = true)
  · exact (rfl : Q aV 2 0 0 = true)
  · exact (rfl : Q aV 3 0 0 = true)
  · exact (rfl : Q aV 4 0 0 = true)
  · exact (rfl : Q aV 5 0 0 = true)
  · exact k6
  · exact k7
  · exact k8
  · exact k9
  · exact k5
set_option maxHeartbeats 0 in
theorem qL : ac true (aF 191) (K 191) 11 := cF (hints:=536879361) (by decide +kernel) (d6 (g:=aV) (i:=0) rfl rfl (ag fN kC) oe uF (by decide +kernel))
def fQ := au fN 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxHeartbeats 0 in
theorem kF : ai true fQ := aw (m:=191) kC qL (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qR : ac true (aF 251) (K 251) 8 := cF (hints:=1358970881) (by decide +kernel) (bk (prior:=aD fQ) (ag fQ kF) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def fR := au fQ 8 [(251,[])]
set_option maxHeartbeats 0 in
theorem kG : ai true fR := aw (m:=251) kF qR (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qS : ac true (aF 255) (K 255) 12 := cF (hints:=553656577) (by decide +kernel) (bk (prior:=aD fR) (ag fR kG) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def fS := au fR 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxHeartbeats 0 in
theorem kH : ai true fS := aw (m:=255) kG qS (by decide +kernel)
def nO (i : Nat) : Nat := 0x1840804ff
def n2 : af := (1,0,6,0,0,0,0,nO)
def nW (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def nN (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def n1 : af := (6,1,6,0,0,9,0,nN)
def nV (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def nM (j : Nat) : Nat := 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def n0 : af := (47,2,6,524294,51,11,1060,nM)
def nU (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def nS (j : Nat) : Nat := (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def n5 : af := (136,3,6,1638440,86,12,1083,nS)
def nY (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def nQ (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def n4 : af := (53,4,6,0,0,9,0,nQ)
def nX (i : Nat) : Nat := 0x834601a000
def nP (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def n3 : af := (2,5,6,0,0,3,0,nP)
def n7 : Array (ae × ae) := #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]
def nL : List bw := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def iJ : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def n6 : Nat → af
  | 12 => n2
  | 11 => n1
  | 10 => n0
  | 9 => n5
  | 8 => n4
  | 7 => n3
  | _ => bS
def nZ : Nat → Nat → Option (Nat × Nat)
  | 12 => aR 8 37 4 10 3 3 nW
  | 11 => aR 48 123 4 13 6 3 nV
  | 10 => aR 79 299 8 15 8 3 nU
  | 9 => aR 39 99 5 13 6 3 nY
  | 8 => aR 1 5 1 8 1 3 nX
  | _ => fun _ => none
def aO : Forest := ⟨383,12,fun j => n7[j]?.getD (0,0),nL,iJ,n6,nZ⟩
set_option maxHeartbeats 0 in
theorem oh : aJ aO (aD fS) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=3) ?_⟩,aQ (d:=1) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tA : Q aO 12 0 1=true := by decide +kernel
theorem lh : Q aO 12 0 1=true := tA
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tz : Q aO 11 0 6=true := by
  apply aE (ar:=9) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lg : Q aO 11 0 6=true := tz
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tv : Q aO 10 0 6=true := by
  apply aE (ar:=8) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem ty : Q aO 10 6 13=true := by
  apply aE (ar:=9) (rows:=0) (d:=2)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tw : Q aO 10 19 28=true := by
  apply aE (ar:=10) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lf : Q aO 10 0 47=true := (@ba aO 10 0 19 28 (@ba aO 10 0 6 13 tv ty) tw)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tF : Q aO 9 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tI : Q aO 9 3 36=true := by
  apply aE (ar:=9) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tJ : Q aO 9 39 36=true := by
  apply aE (ar:=9) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tK : Q aO 9 75 36=true := by
  apply aE (ar:=9) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tG : Q aO 9 111 8=true := by
  apply aE (ar:=9) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tH : Q aO 9 119 17=true := by
  apply aE (ar:=10) (rows:=0) (d:=2)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ll : Q aO 9 0 136=true := (@ba aO 9 0 119 17 (@ba aO 9 0 111 8 (@ba aO 9 0 75 36 (@ba aO 9 0 39 36 (@ba aO 9 0 3 36 tF tI) tJ) tK) tG) tH)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tC : Q aO 8 0 36=true := by
  apply aE (ar:=8) (rows:=0) (d:=3)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tD : Q aO 8 36 8=true := by
  apply aE (ar:=8) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tE : Q aO 8 44 9=true := by
  apply aE (ar:=9) (rows:=0) (d:=1)
  simp only [J,aC,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lk : Q aO 8 0 53=true := (@ba aO 8 0 44 9 (@ba aO 8 0 36 8 tC tD) tE)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tB : Q aO 7 0 2=true := by decide +kernel
theorem lj : Q aO 7 0 2=true := tB
theorem uH : cI aO 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q aO 0 0 0 = true)
  · exact (rfl : Q aO 1 0 0 = true)
  · exact (rfl : Q aO 2 0 0 = true)
  · exact (rfl : Q aO 3 0 0 = true)
  · exact (rfl : Q aO 4 0 0 = true)
  · exact (rfl : Q aO 5 0 0 = true)
  · exact (rfl : Q aO 6 0 0 = true)
  · exact lj
  · exact lk
  · exact ll
  · exact lf
  · exact lg
  · exact lh
set_option maxHeartbeats 0 in
theorem qX : ac true (aF 383) (K 383) 13 := cF (hints:=12901687553) (by decide +kernel) (d6 (g:=aO) (i:=0) rfl rfl (ag fS kH) oh uH (by decide +kernel))
def dz := au fS 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxHeartbeats 0 in
theorem kJ : ai true dz := aw (m:=383) kH qX (by decide +kernel)
theorem gk : ai false dz := p0 kJ
def xl (i : Nat) : Nat := 0x1a230180fd10fc20
def xp : af := (2,1,2,0,0,4,0,xl)
def xm (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def xk (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def xo : af := (5,2,2,0,0,5,0,xk)
def xr : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffffffc47,0xa86),(0xfffffffffffffffffffffffffffffffffff09b,0xfffffffffffffffffffffffffffffffffff531),(0x29c,0x8cc),(0xfffffffffffffffffffffffffffffffffff327,0xfffffffffffffffffffffffffffffffffff303),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def xj : List bw := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def xi : List (List Nat) := iI
def xq : Nat → af
  | 6 => xp
  | 5 => xo
  | _ => bS
def xn : Nat → Nat → Option (Nat × Nat)
  | 6 => aR 8 11 1 11 3 4 xm
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => xr[j]?.getD (0,0),xj,xi,xq,xn⟩
set_option maxHeartbeats 0 in
theorem iL : aJ x31 (aD dz) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=1) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def xh : Nat := 0x110c0300c03
def xg : Nat := 0x14090281205
set_option maxHeartbeats 0 in
theorem ql : Z x31 6 0 2 := by
  exact aM (by decide +kernel)
theorem qk : Z x31 6 0 2 := ql
set_option maxHeartbeats 0 in
theorem qj : Z x31 5 0 5 := by
  apply bZ (pos:=xh) (neg:=xg) (data:=fun _ => 0x4224033220301121141340101413401031423232) rfl
  decide +kernel
theorem qi : Z x31 5 0 5 := qj
theorem kx : cE x31 6 := by
  intro k hk
  interval_cases k
  · exact az x31 0 0
  · exact az x31 1 0
  · exact az x31 2 0
  · exact az x31 3 0
  · exact az x31 4 0
  · exact qi
  · exact qk
set_option maxHeartbeats 0 in
theorem ki : aH false (K 1055) 6 (aF 1055).toFinset := dB (q:=31) (prior:=aD dz) (ag dz gk) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qC : ac false (ad 1567) (K 1567) 7 :=
  aG (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ki
    (aX (g:=x31) (i:=0) rfl rfl (ag dz gk) iL kx (by decide +kernel))
def iZ := au dz 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxHeartbeats 0 in
theorem uW : ai false iZ := aw (m:=1567) gk qC (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qY : ac false (ad 42527) (K 42527) 7 :=
  aG (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ki
    (aX (g:=x31) (i:=1) rfl rfl (ag dz gk) iL kx (by decide +kernel))
def d8 := au iZ 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxHeartbeats 0 in
theorem gh : ai false d8 := aw (m:=42527) uW qY (by decide +kernel)
def vP (i : Nat) : Nat := 0x1040a3fa21fd51
def vT : af := (2,1,1,0,0,3,0,vP)
def vQ (i : Nat) : Nat := 0x40000
def vO (i : Nat) : Nat := 0x102de54110
def vS : af := (1,2,1,0,0,0,0,vO)
def vW : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffffff9b5,0xe94),(0xfffffffffffffffffffffffffffffffffff0db,0xfffffffffffffffffffffffffffffffffff10b),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def vN : List bw := [(96,0,15,0,4),(1,32,78,0,4)]
def vM : List (List Nat) := [[],[32,83]]
def vV : Nat → af
  | 6 => vT
  | 5 => vS
  | _ => bS
def vR : Nat → Nat → Option (Nat × Nat)
  | 6 => aR 1 3 1 6 1 1 vQ
  | _ => fun _ => none
def cG : Forest := ⟨1135,6,fun j => vW[j]?.getD (0,0),vN,vM,vV,vR⟩
set_option maxHeartbeats 0 in
theorem iK : aJ cG (aD d8) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def kQ : Nat := 0x42108300c03
def kP : Nat := 0x68321248a2a
set_option maxHeartbeats 0 in
theorem p4 : Z cG 6 0 2 := by
  apply bZ (pos:=kQ) (neg:=kP) (data:=fun _ => 0x2401212143203010) rfl
  decide +kernel
theorem p3 : Z cG 6 0 2 := p4
set_option maxHeartbeats 0 in
theorem p2 : Z cG 5 0 1 := by
  apply bZ (pos:=kQ) (neg:=kP) (data:=fun _ => 0x24012110) rfl
  decide +kernel
theorem p1 : Z cG 5 0 1 := p2
theorem ku : cE cG 6 := by
  intro k hk
  interval_cases k
  · exact az cG 0 0
  · exact az cG 1 0
  · exact az cG 2 0
  · exact az cG 3 0
  · exact az cG 4 0
  · exact p1
  · exact p3
set_option maxHeartbeats 0 in
theorem kh : aH false (K 1135) 6 (aF 1135).toFinset := dB (q:=111) (prior:=aD d8) (ag d8 gh) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rg : ac false (ad 49775) (K 49775) 7 :=
  aG (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) kh
    (aX (g:=cG) (i:=0) rfl rfl (ag d8 gh) iK ku (by decide +kernel))
def jq := au d8 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxHeartbeats 0 in
theorem vt : ai false jq := aw (m:=49775) gh rg (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q0 : ac false (ad 42607) (K 42607) 7 :=
  aG (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) kh
    (aX (g:=cG) (i:=1) rfl rfl (ag d8 gh) iK ku (by decide +kernel))
def bU := au jq 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxHeartbeats 0 in
theorem dE : ai false bU := aw (m:=42607) vt q0 (by decide +kernel)
def x0 (i : Nat) : Nat := 0x344640ac3f865fc10
def x8 : af := (2,1,2,0,0,4,0,x0)
def x3 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def xZ (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x7 : af := (12,2,2,0,0,7,0,xZ)
def x2 (i : Nat) : Nat := 0x24f9400060ba8030352
def xY (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x6 : af := (6,3,2,0,0,6,0,xY)
def x1 (i : Nat) : Nat := 0x20034000
def xX (i : Nat) : Nat := 0x3b04813058432
def x5 : af := (1,4,2,0,0,0,0,xX)
def ya : Array (ae × ae) := #[(0xffffffffffffffffffffffffffffffffff209f,0xd8096),(0xfffffffffffffffffffffffffffffffff19c61,0xfffffffffffffffffffffffffffffffff03861),(0x97be,0x2c69c),(0xfffffffffffffffffffffffffffffffff04b47,0xfffffffffffffffffffffffffffffffffd3903),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def xW : List bw := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def xV : List (List Nat) := [[],[65,50]]
def x9 : Nat → af
  | 7 => x8
  | 6 => x7
  | 5 => x6
  | 4 => x5
  | _ => bS
def x4 : Nat → Nat → Option (Nat × Nat)
  | 7 => aR 7 21 2 9 4 1 x3
  | 6 => aR 2 9 1 8 3 1 x2
  | 5 => aR 1 5 1 6 1 1 x1
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => ya[j]?.getD (0,0),xW,xV,x9,x4⟩
set_option maxHeartbeats 0 in
theorem iM : aJ x63 (aD bU) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def gl (j : Nat) : Nat := 0x3514243035142420351320403142355431423232203411211512401013243543
def gp (j : Nat) : Nat := 0x3120043210043201024300234510350210243002345103402102430023451023051024300234010340210210341352003510002103413520030210
def gn : Nat := 0x42110c0300c03
def gm : Nat := 0x34190a81205
set_option maxHeartbeats 0 in
theorem zv : Z x63 4 0 1 := by
  apply aB (pos:=gn) (neg:=gm) (kw:=gl) (panels:=gp) (data:=0x1) rfl
  decide +kernel
theorem zu : Z x63 4 0 1 := zv
set_option maxHeartbeats 0 in
theorem zx : Z x63 5 0 6 := by
  apply aB (pos:=gn) (neg:=gm) (kw:=gl) (panels:=gp) (data:=0x50008000607) rfl
  decide +kernel
theorem zw : Z x63 5 0 6 := zx
set_option maxHeartbeats 0 in
theorem zz : Z x63 6 0 12 := by
  apply aB (pos:=gn) (neg:=gm) (kw:=gl) (panels:=gp) (data:=0x803020482818600838580) rfl
  decide +kernel
theorem zy : Z x63 6 0 12 := zz
set_option maxHeartbeats 0 in
theorem zB : Z x63 7 0 2 := by
  apply aB (pos:=gn) (neg:=gm) (kw:=gl) (panels:=gp) (data:=0x84) rfl
  decide +kernel
theorem zA : Z x63 7 0 2 := zB
theorem ky : cE x63 7 := by
  intro k hk
  interval_cases k
  · exact az x63 0 0
  · exact az x63 1 0
  · exact az x63 2 0
  · exact az x63 3 0
  · exact zu
  · exact zw
  · exact zy
  · exact zA
set_option maxHeartbeats 0 in
theorem ef : aH false (K 1087) 7 (aF 1087).toFinset := dB (q:=63) (prior:=aD bU) (ag bU dE) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem ru : ac false (ad 6719) (K 6719) 8 :=
  aG (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (bk (prior:=aD bU) (ag bU dE) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def jz := au bU 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxHeartbeats 0 in
theorem vD : ai false jz := aw (m:=6719) dE ru (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qu : ac false (ad 1087) (K 1087) 8 :=
  aG (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (aX (g:=x63) (i:=0) rfl rfl (ag bU dE) iM ky (by decide +kernel))
def iU := au jz 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxHeartbeats 0 in
theorem uR : ai false iU := aw (m:=1087) vD qu (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qw : ac false (ad 11327) (K 11327) 8 :=
  aG (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (aX (g:=x63) (i:=1) rfl rfl (ag bU dE) iM ky (by decide +kernel))
def iV := au iU 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxHeartbeats 0 in
theorem uS : ai false iV := aw (m:=11327) uR qw (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qD : ac false (ad 1599) (K 1599) 8 :=
  aG (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (bk (prior:=aD bU) (ag bU dE) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def i0 := au iV 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxHeartbeats 0 in
theorem uX : ai false i0 := aw (m:=1599) uS qD (by decide +kernel)
set_option maxHeartbeats 0 in
theorem re : ac false (ad 47679) (K 47679) 8 :=
  aG (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (bk (prior:=aD bU) (ag bU dE) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def jp := au i0 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxHeartbeats 0 in
theorem vs : ai false jp := aw (m:=47679) uX re (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qZ : ac false (ad 42559) (K 42559) 8 :=
  aG (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (bk (prior:=aD bU) (ag bU dE) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def jh := au jp 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxHeartbeats 0 in
theorem vk : ai false jh := aw (m:=42559) vs qZ (by decide +kernel)
set_option maxHeartbeats 0 in
theorem ri : ac false (ad 52799) (K 52799) 8 :=
  aG (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ef
    (bk (prior:=aD bU) (ag bU dE) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def de := au jh 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxHeartbeats 0 in
theorem en : ai false de := aw (m:=52799) vk ri (by decide +kernel)
def wd (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def wm : af := (5,1,3,0,0,7,0,wd)
def wg (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def wc (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def wl : af := (10,2,3,0,0,7,0,wc)
def wf (i : Nat) : Nat := 0x700009040000000000ddd0800002
def wb (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def wk : af := (3,3,3,0,0,5,0,wb)
def wr : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffff1880f,0xfffffffffffffffffffffffffffffffffe600d),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff2619f,0x2a10e),(0xfffffffffffffffffffffffffffffffff60271,0xfffffffffffffffffffffffffffffffffc5851),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def wa : List bw := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def v9 : List (List Nat) := iH
def wq : Nat → af
  | 7 => wm
  | 6 => wl
  | 5 => wk
  | _ => bS
def wh : Nat → Nat → Option (Nat × Nat)
  | 7 => aR 23 29 4 12 4 4 wg
  | 6 => aR 2 11 1 10 2 4 wf
  | _ => fun _ => none
def bQ : Forest := ⟨1213,7,fun j => wr[j]?.getD (0,0),wa,v9,wq,wh⟩
set_option maxHeartbeats 0 in
theorem eV : aJ bQ (aD de) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=1) ?_⟩,aQ (d:=2) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def kS : Nat := 0x1408410844300c
def kR : Nat := 0x90448d05005
set_option maxHeartbeats 0 in
theorem qf : Z bQ 7 0 5 := by
  apply aM
  apply aE (ar:=7) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qe : Z bQ 7 0 5 := qf
set_option maxHeartbeats 0 in
theorem qc : Z bQ 6 0 3 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qd : Z bQ 6 3 7 := by
  apply bZ (pos:=kS) (neg:=kR) (data:=fun _ => 0x25234363203201322034013214234010432405431423402114234021) rfl
  decide +kernel
theorem qb : Z bQ 6 0 10 := (@X bQ 6 0 3 7 qc qd)
set_option maxHeartbeats 0 in
theorem qa : Z bQ 5 0 3 := by
  apply bZ (pos:=kS) (neg:=kR) (data:=fun _ => 0x242340404324053241324040) rfl
  decide +kernel
theorem p9 : Z bQ 5 0 3 := qa
theorem fn : cE bQ 7 := by
  intro k hk
  interval_cases k
  · exact az bQ 0 0
  · exact az bQ 1 0
  · exact az bQ 2 0
  · exact az bQ 3 0
  · exact az bQ 4 0
  · exact p9
  · exact qb
  · exact qe
set_option maxHeartbeats 0 in
theorem fd : aH false (K 1213) 7 (aF 1213).toFinset := dB (q:=189) (prior:=aD de) (ag de en) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qN : ac false (ad 2237) (K 2237) 8 :=
  aG (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) fd
    (aX (g:=bQ) (i:=0) rfl rfl (ag de en) eV fn (by decide +kernel))
def i8 := au de 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxHeartbeats 0 in
theorem vc : ai false i8 := aw (m:=2237) en qN (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qG : ac false (ad 1725) (K 1725) 8 :=
  aG (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) fd
    (aX (g:=bQ) (i:=1) rfl rfl (ag de en) eV fn (by decide +kernel))
def i3 := au i8 8 [(1725,[]),(17085,[82,48])]
set_option maxHeartbeats 0 in
theorem u5 : ai false i3 := aw (m:=1725) vc qG (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qT : ac false (ad 2749) (K 2749) 8 :=
  aG (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) fd
    (aX (g:=bQ) (i:=2) rfl rfl (ag de en) eV fn (by decide +kernel))
def je := au i3 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxHeartbeats 0 in
theorem vh : ai false je := aw (m:=2749) u5 qT (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q5 : ac false (ad 43197) (K 43197) 8 :=
  aG (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) fd
    (aX (g:=bQ) (i:=3) rfl rfl (ag de en) eV fn (by decide +kernel))
def jj := au je 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxHeartbeats 0 in
theorem vm : ai false jj := aw (m:=43197) vh q5 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q9 : ac false (ad 44221) (K 44221) 8 :=
  aG (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) fd
    (aX (g:=bQ) (i:=4) rfl rfl (ag de en) eV fn (by decide +kernel))
def eE := au jj 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxHeartbeats 0 in
theorem hQ : ai false eE := aw (m:=44221) vm q9 (by decide +kernel)
def wT (i : Nat) : Nat := 0x60bfd31
def wW : af := (1,1,1,0,0,0,0,wT)
def wY : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffffffffc91,0xfffffffffffffffffffffffffffffffffffc01),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),(0xffffffffffffffffffffffffffffffffffff8d,0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def wS : List bw := [(88,0,163,0,4),(8,0,243,0,7)]
def wR : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def wX : Nat → af
  | 7 => wW
  | _ => bS
def wV : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def cR : Forest := ⟨1275,7,fun j => wY[j]?.getD (0,0),wS,wR,wX,wV⟩
set_option maxHeartbeats 0 in
theorem oj : aJ cR (aD eE) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=0) ?_⟩,aQ (d:=1) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def wQ : Nat := 0x14042108443003
def wP : Nat := 0x68325248a381a0642a
set_option maxHeartbeats 0 in
theorem qh : Z cR 7 0 1 := by
  apply bZ (pos:=wQ) (neg:=wP) (data:=fun _ => 0x50634340) rfl
  decide +kernel
theorem qg : Z cR 7 0 1 := qh
theorem uJ : cE cR 7 := by
  intro k hk
  interval_cases k
  · exact az cR 0 0
  · exact az cR 1 0
  · exact az cR 2 0
  · exact az cR 3 0
  · exact az cR 4 0
  · exact az cR 5 0
  · exact az cR 6 0
  · exact qg
set_option maxHeartbeats 0 in
theorem sM : aH false (K 1275) 7 (aF 1275).toFinset := dB (q:=251) (prior:=aD eE) (ag eE hQ) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rf : ac false (ad 48891) (K 48891) 8 :=
  aG (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) sM
    (aX (g:=cR) (i:=0) rfl rfl (ag eE hQ) oj uJ (by decide +kernel))
def bX := au eE 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxHeartbeats 0 in
theorem dX : ai false bX := aw (m:=48891) hQ rf (by decide +kernel)
def v2 (i : Nat) : Nat := 0x1948817fd30
def v6 : af := (1,1,3,0,0,0,0,v2)
def v3 (i : Nat) : Nat := 0x8e80
def v1 (i : Nat) : Nat := 0x24c269243a037eb0261df54530
def v5 : af := (2,2,3,0,0,5,0,v1)
def v8 : Array (ae × ae) := #[(0xffffffffffffffffffffffffffffffffff22a7,0xffffffffffffffffffffffffffffffffffa027),(0xffffffffffffffffffffffffffffffffff4759,0x4258),(0x942e,0x8424),(0xffffffffffffffffffffffffffffffffff99d3,0xffffffffffffffffffffffffffffffffff3bd3),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def v0 : List bw := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def vZ : List (List Nat) := [[],[16,66,101]]
def v7 : Nat → af
  | 8 => v6
  | 7 => v5
  | _ => bS
def v4 : Nat → Nat → Option (Nat × Nat)
  | 8 => aR 1 3 1 6 1 1 v3
  | _ => fun _ => none
def cu : Forest := ⟨1151,8,fun j => v8[j]?.getD (0,0),v0,vZ,v7,v4⟩
set_option maxHeartbeats 0 in
theorem oi : aJ cu (aD bX) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=1) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def vY : Nat := 0x10842110c0300c03
def vX : Nat := 0xe86824914642a
set_option maxHeartbeats 0 in
theorem p8 : Z cu 8 0 1 := by
  exact aM (by decide +kernel)
theorem p7 : Z cu 8 0 1 := p8
set_option maxHeartbeats 0 in
theorem p6 : Z cu 7 0 2 := by
  apply bZ (pos:=vY) (neg:=vX) (data:=fun _ => 0x2615312126154121) rfl
  decide +kernel
theorem p5 : Z cu 7 0 2 := p6
theorem uI : cE cu 8 := by
  intro k hk
  interval_cases k
  · exact az cu 0 0
  · exact az cu 1 0
  · exact az cu 2 0
  · exact az cu 3 0
  · exact az cu 4 0
  · exact az cu 5 0
  · exact az cu 6 0
  · exact p5
  · exact p7
set_option maxHeartbeats 0 in
theorem eH : aH false (K 1151) 8 (aF 1151).toFinset := dB (q:=127) (prior:=aD bX) (ag bX dX) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qM : ac false (ad 2175) (K 2175) 9 :=
  aG (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (bk (prior:=aD bX) (ag bX dX) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def i7 := au bX 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxHeartbeats 0 in
theorem u9 : ai false i7 := aw (m:=2175) dX qM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qx : ac false (ad 1151) (K 1151) 9 :=
  aG (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (bk (prior:=aD bX) (ag bX dX) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def iW := au i7 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxHeartbeats 0 in
theorem uT : ai false iW := aw (m:=1151) u9 qx (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rj : ac false (ad 52863) (K 52863) 9 :=
  aG (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (bk (prior:=aD bX) (ag bX dX) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def jt := au iW 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxHeartbeats 0 in
theorem vv : ai false jt := aw (m:=52863) uT rj (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q8 : ac false (ad 44159) (K 44159) 9 :=
  aG (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (bk (prior:=aD bX) (ag bX dX) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def jm := au jt 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxHeartbeats 0 in
theorem vp : ai false jm := aw (m:=44159) vv q8 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q6 : ac false (ad 43647) (K 43647) 9 :=
  aG (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (aX (g:=cu) (i:=0) rfl rfl (ag bX dX) oi uI (by decide +kernel))
def jk := au jm 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxHeartbeats 0 in
theorem vn : ai false jk := aw (m:=43647) vp q6 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q1 : ac false (ad 42623) (K 42623) 9 :=
  aG (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eH
    (bk (prior:=aD bX) (ag bX dX) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def ch := au jk 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxHeartbeats 0 in
theorem cP : ai false ch := aw (m:=42623) vn q1 (by decide +kernel)
def wv (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def wH : af := (10,1,7,0,0,9,0,wv)
def wB (i : Nat) : Nat := 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def wA (j : Nat) : Nat := (if j<1 then 0x4670b12533d10c75e8c8b58478714c78518d7ffe317a00012a9ac91478d191b210c32553e54c93f89481224ccae8c8db6fde254791fe4e848fbc887bfd7bf91489036fde2547dcf8012e849566e24b9fb14c8811a0e059e352b5153447cbd4232d7f49221033d272641407a231b409789c248c37effc18880013340f091678851c118ebe79ab9993d531d8dc499a05bd0c116be4b20866cfc8181973f508195bdbb50994f7c60a504f0c8428b9e9121c0ac4fc46a1120e04a60f4453fb885004944e5f860055bc6ff42c4127799d428024a1e7ce7ac1704adc7e20451ffc4244651f5f0228486f4f0a1954c1e8977ea4a053be12443c9c3c6580589afe03afe94c94489efffa830090fdb8d0417f449000ce5f928a32dffc2d0614d27f807b0a67cf1f4d91f647d4208fbfe3700101096bf0781268499f1f02000903ffe01040482fca44652ffe289a4fc122aff8d4941804bdf23604101297c7e2140124af7ee811a7f861011d78f7002c80953e381127d8e0211e7f299142fbf18650920df8cb8019cf270f30e0547938798702a5ebf9031120250f9f5818890128f270f30e05400fe351d6404a258208d1b924507a3c1d8e86f1d841349848218d86b128212494478f110820c0a8e62006815047c230948a42161f9088a0318c9c0a1707c9404221c0c881288b0503b15130a240108fc04381b1a0844030838cc0801088b84e07148944900150b4582b1787c010b2846416a08101e7fcbfa1f92fab7c5bddde64f0b778bb55d82e9e73db929c58e0c6f43739b5ad886b9b591a7ed1d68533b5996cb263d319988cc2b606af8d78aba05bcad9566ab10570ab25534a8d52fa8ed41e9ef4eba72935296e4a92505254906477a3591928ae444219908c8224009f80f6c78e3c09da0e727113711ad0d0066031e1840bdc5d52d89660ad254f29413e49b64b1247919c87c4161f88ef472036519c0c605f42df15609f849e22e105076437c19a0bf054424c0f9066025c0c4035000524114a83d264f4b885240f4b93d2a234983d2a4f4bb3d2e6f4b24d2813498352c034b1852c6d4902d242d4b93524094884d284d4aa3d26334a0bd2a614b0bd2c13498852eaf490352c734b1bd2a274b13d0e4f4b01d24134a13d2403499352e334b09d2407498b522014a8c52e2f4b08d2c114a84d26134ba4d2e8d4aa3528334b9b52e61498052c054384d0e4d4a0352a434a9152a474b84d282d4a8bd2c0f498bd24014a002ae4cab8c32846eb1caae10ab883282eab84aae22a393ca40cabb0c282cab91aae4aa3932ae0aab8caae2aab982aea4abb128e132983aaea6ab913a610ab8a3a612aba32ae6cabb1aae26abac2ae4eab822ae42caa3aaea2ababaae048b8a1ae462ba9a2e260bb192e660bb0ffffdfdfbfbeff7dbdddebf3f54d435011018c53100310c020 else 0x2a514f996be52268663fe3f325000b13ca8643f53090a16b2b1c08e6b231fc5008b7c382938e31a32317b310ffc6068f40910413efe1f6c01485ee44d9b654c87a249bf13a091bbf9e4f32ae0e4e3d3a92ab09fe26af3c9e651e04e8247ae7089a62f4408edf4ca44663e5120b04991818324)
def wM : af := (122,2,7,720906,68,13,1115,wA)
def wF (i : Nat) : Nat := (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def wz (j : Nat) : Nat := (if j<1 then 0x6525d9a24904d89415292e2f4660a546a02949804e92e6012580e3841401982aa92a4d525c84a4901d496028e285512442340a129793064f2c6e9261e3aea93e49204ef2a521754a9a4b94249760e92407125d43a4bb2b5160ad12a2b066119c4a8b94954511aa4e1c508d249035714182e282f524812a4b9398d2068910f412482ca4b09d49727c92a44de58dc44409749204d1ac0e125825c4b0d4714236e2a8d866008a4c28e79317092e42925d820cc2b55d52a91ac2e1e4c2a24ba8349730292e8cd25d4224a8b6496366330539261d244a8ad8d845292e6cd248118cc2b4198224a2c03125ca7c6900b49406692e4f622063a4b954498244330ce125465bc982c4971871a60a52614a24a0598d2071110341e4c27a4b0351983511102dc6619a3cb1d44976583306a525c8424b88279537092407dc551724b0cb19855e92e42dc502a46c1a98d2034f2615d2614e82c1220487860b0e18161e182c33629523e090efd5551e8243be05821e0b06a0e5cc30243d75952a27ac274e480f36aa380580b20b0ec98212890b09039730a230754e20e282c14d05836682c270d50a6b4a0c20581408a4094160a314a94d05870a4302408585002c22821602c0b0ad8e4c260ac0b105802ceaa6e1048119ec01d05823e53047ca54878243b94572707b0a74858081c985904879e7ac0741604f9ca89e3d72328ae6a5b505c02c3ba40818a52c27ce548f02c14e21524042c0801605b20a0a861429052a538121e81aa12005849c130d38121d91aa11c4d63aaaaa50016013bea12935423eeac6e1654ab34a0ae21514082a2d0a480fba98504171307ae429a505c9cb1d805859882c0701606702c3835954ac52a23c848081cb09e05818c6ae500e580f20b8830487a6824070e4c268243ad41863882a471358ebb4a12f5554a70a82a41604810c0a005822a0b0ef0d5c9db2a117418538090ec0854483a904804878452a27c360600243b121204042a441d4c5c20b88929813e72e60ca580f9ea89d29522a8a40881604796a11e1d4240030d389508f98a11cffbfdff3fbfebf7fdbeffbbedfafe7f7fd7f3fbfedf7fdfb7ddef77dbf6dd9f5fd3f3fcbeffbf6f7bbebf9fe3f5c5535c1535915358d535815350553501534c5534c15348153441531c1535d5435c5435c14358143545434c143481435d5405c94058d405894058540581405514054940545405414050940505404c9404c5404c140481401c9405d1105cd105c91058d10551105091050510501104c9104c5104c11048510481101c9105c8635c4635c063480635c4535c053480535d8405d4405cc405c8405c44058440580405484054440480405d8315d4315c8315c03158031548315d8305d4305c8305c43058430580305483054430480305cc2058c2054c20500204c4204c0204802044020 else (if j<2 then 0x91681d011002a0fd070f4380c4270111f8940107c110cc0787d000a6000b8000b02b0bc2deb07517a69d25e8cf4179efcdae64f2cf94fc90e4271bb8b3c3fe1870a3833c0bdfe6fc77c5bd4ddceeb7743b8ddc2ede76c1b4bd966c7761faf6d6ceb0f569a9fd4aea174f7a6ad2de93b47ba2fd10e8273fb9e3ce566b3333987cbc65b32bb94cc9c64b72258fac6fe34f1898b1c4f625b101868c27e10b06d81fc065fdefc77d5be45ecaf3178dbbcddaeebb73eb925c2edf36ecb70db42d836b3b53da62cff673b2ed93ac8962fb0ad80ebe75dbae756d2b41595abed5d6adb553a9dd482a0b4eea6552be94f491a3cd19a883430a12503e8013f39f44f627953ac9cace1a6f135a99fccce63b30d97a4b9a5a52c29554a7650f27d934c97a49923a912c8624051e38e3c6ba34518e8c2c5b22b514289d448220b0f486b43261830ae84b421e0e506282b410e06701d807400dff6fee7f03f55f8efb77d5be7df2af827b83d89e9af367943c55e14efc7773b51d8ceb97513a4dcfce7272f3941c8ae39711b855c12df26f5377dba2dc56dd3689b18d776b5b579aa4d4769a34a1a2cd0a67933999a4cb6655b27190ec6c62f312186cc186052ffd7cebd25e12ec5740b8d5b62d3566ab28586ac0d5e8ae456a2af5556a9a53ca98d480a26503a7cd3cc9da4e026c534c98c4bf25b92b894749ea4892068ee46a231d1688a744821d90cc85341c20910207f43ef1f1cf5e79b3bd1d80e8c7383901c34df46db3659ad0d3869033f19acc94637311981cbe85d42dc16b8b445922be1574aa654229a9450a024ee26992dc94e494242117c87c42e2098fe07c43cf1d20e507043611a38ce864e31c1830bb05a42bd1508a0c4e425e12788fc456212101079c3a21b20d206342f81680aa84d424a10b079839016c08e03080cc00033031d25c9fc4b0bb71429292e21a3481924c3a1198262a2c111261e824b88549208c92ead525c6ba4904c71425e92403d2618e38a1188d20aa9304963481aa490228d2062f26142254578cc336198086910518660670cc32c71422ef2415925c8c0cc10c492096f24121248104440a45161831a413d2486324bb038d4253110284660d9a4b881498366330269c549dc4a8d249765a92e22925cd48cc22971418712a2ac6605224b09f493066baa501e4c24a4b94171423292c07466050a4b013893154e284c62204438a0c449529692e4dd25d5a0cc2b689525ee240edc551ca4bb2e1980191a4129754a4a4ba8289515d1a41046608da4b88b4920b092e22125ca224a9b35d529f12a20e25059bc9932198074930c4de4c5d46a8b849709e3305246601946902d49765e92e4312548a28b09a79609033012525cd50cc2ba89516a92e46521ca324c30d49202092c13125d8138904081207e3303112549a44408189516892e2 else 0x340a25a5322c508f112816314116c3de54064dca108c686c049ec18d808de0829e121cf18c88708802c913c053686908722a6065d5041b011814e2218030127c898cde1045fae0190e111e05df2863ef912326700c746877788680cc210053a42a3435615f2106c359147a03199093c85065f40630ff70992f091d6cc53108c84e116c50b5450d0144be0640f4a63c9700c86421c8b2da1d9923005f190e3e018ddc2106b41602dfc0867848d7a886ba887591588b5e282f71020d80ad4a19e0559147cba06417d1a0f6f8489bc215585808f90aad09a45a83b90a7f0488c046f0415a234057a887dfd531a78c4bc06dec8c6e021b3e9127810e9087b431800047f00c7de40c60f0020f47e8220fd0436fdb422651f810880159731d7a031d65625ffab00233cc0d8084f486748b682409780cb036fe60190bc0319c22c6073a780648790506c05730922f2153c2a0cb619e0431942af60636810f5886012d7219028958b78421d6a1d5867f443cfe000c8bfd44885f4a63302cf06200c7ca18cf2238fe26300e70020d7d79221ec0f3a78064581005af232f2863a703ba14336236020e0c4c7433e221eb8140400d02388980dc450684604c040147262de108b61677416403630d86eb91d21ac8ab222fc898de02581278463a3433d243d41da143b88a90981133c492c0a8147286300a43ec0a81521cf6663e2e18d7c486a05b415026026708d80bb262602ef806360213a43af362642048e06e1848ef10a0ee22a4c495ba625fd0811550340590e2c735843be223b11e6989f6022fe810118edf1613b79231b00efcc312a023810f888f88a78e219c84766235fd020232f848796c3d05967c0844edb498cb6e848c034039f021107021024fc218de029a42be08e62a86016d509453b7c584f35843ce68191c057109120798c18cbf80639a424ecc590e8190cb090cb0923c10193b3263ce48c75e24c72c904bfa04046ce68192fc402678083e018ee2121fa230fe404c97845b65511bc218cc0b78424ecc49dbe08655bc09b50863c8508bd0d8b035c91977fa0910023023e03ada98cedf16138047e0370147d309195f6021f023c8740c85fa44c97c44fb010b8133ca8100ccbfa0404698428f448c990e81917c2434ecc45fb1482819e690ad5245fd0202367340c96223e446808af9249f021127c08449ac21d72923227ca48c8bc4232c24ac467c0679c46be80443e039f5a089b2b221f790c26780b3a1319b810cb092f91187e1d0321f01b7ec0c7b59288708829e5ff3e22a9c6fd08248df7fcca0824053cbfe7c454be30c6f1a092a21088340e91013c2805841913414844b4961d8042140842076168d1128a002041230830042241c581bc54308404e071228552789d4186d154a02409604480450c))
def wL : af := (387,3,7,2359386,103,13,1105,wz)
def wE (i : Nat) : Nat := 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def wy (j : Nat) : Nat := (if j<1 then 0xcf10e13bf579aec5c2b756a2cd588b015e2b6560ab1536a0d39a634a690d19a21422804f49c9362684c39772ce52c8d8f91d23645c8a911e1d42e84d06608c057f4fc9f53da7a4f1ddfbb775ee8dcab8d6f6dadb1b4f684cdd9331961ac05792e65acb0d5baaf538a293f2744d09812aa464768bd13a0d40a7d4ef1cf38e6fcd91a933863cc39772de570aa1422684908e10b1f43c86f8d71922d85309b1242183e8710d0170268420660940d00f0001330942649c6ca0b0c541874ac3246645536a94785422c1330a026430ea90069c914e9a40da95064209034752033292241b508ce49842a9637a7930252481b8cc8a5119128790335f508906c899c930be52a544f206b8ccc250991c3ba413cf245206c91ad9417cfa844e250869e40a6d94158510f54e21ec0ccba19d601211318dc244b7098566d423052a54195806b2b08b85421213235e250829e48a9199501128433450821443dd6d4238c92274264a284c9533c984a1324d21480f4e48a38d510312e219f5088c4a0b128878cb28475b508dbea1145161327ae22275457b6ba8715911d324039c545ccc903919921b12c3136505704c95c6d422e2b243cf545598a11b7d730faa40d46644588c915454195192245b508b70984189710e2b303d9244164a0bfe52066bac251858471e40a230876ab2847cf206cc89857b154787b0eea2508518aa408942123930b784c26489014b952a942c983348192aa11dbd209c01300c1261290a952b520b6013080921f134a116348396f284470505d9643daad30bd028427fc7f4fe5fb3f57e9fd1f9bf2fe4fc5f6be97cef8dedbd6f87ef9debbcf76eebdb7b5f69ecfd8faf75de9fd2f9ef3be6fcbf95f1fdf9beb76e7ecfb9df3ae6fccf97f1be1fbf95f6bdd77abf1fe3ec3f4817154d635915321d6454d5458d535014154d54501535494054c87501535493054c844c15361d2054d304815321d2054c81481535491054d204415321d1054d861c1536107054d811c1535493050d424c14361d2050c8148143205725018158d405056250161581405c954501525454021d5150172505404c532501544c54054531500874c54058d30501614c14058130501524c1404c5305008148140549734408758d106095444181551105095444087551105494144142505105d94044184481105cd20441424811050520441404811060c72441541c9106017218d205c4634817018d87480634817114d825c0534817014d87480532052014d525d84054576101425d84048176101825d44060575101615d44058175101525d44054575101205d44058573101605cc4054973101515cc4048173101805c84058572101605c84061971101855c44058171101525c4404817110182584405096110142580405c5511008148040549760c1205d8305cd31081714c420 else 0x2a743e6105ac2095c0d7b8c6c040101078c50c0aaf41113c18a9815e610c03b2626c097a420000b213210020464200000000000100005023e22502001a0800026c21860c6f60300003e2200701380b50401682016424080000f88801808000004a0c3020152b14d2100078314584812e909c056432837488c866108be314a080073625f90ac8501b2100205748980990802c7a4880134853f090ee910000548802e02701004e210003762005e9093613e2200dd2168d08034c218058442710cec0e90804c8402c04016023244c04c91260748690992206610100a2784ed04271200030d019507a0004620e00c830008f90124ec020b004a828120fd1662d4548002c43e0b80002905e0ad0002dd73ac74e689ced99f28e46c7d8)
def wK : af := (137,4,7,3801188,103,11,1064,wy)
def wD (i : Nat) : Nat := 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def wx (i : Nat) : Nat := 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def wJ : af := (19,5,7,0,0,8,0,wx)
def wC (i : Nat) : Nat := 0x81900
def ww (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def wI : af := (2,6,7,0,0,3,0,ww)
def wO : Array (ae × ae) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),(0xffffffffffffffffffffffffffff4ca8886101,0xffffffffffffffffffffffffffff8c0d9a00c9),(0xdc001a04a,0x12b065ab12),(0xffffffffffffffffffffffffffff815101844f,0xffffffffffffffffffffffffffffe94a0254e5),(0x2200761284,0xca4842b0f4),(0x0,0x0),(0xffffffffffffffffffffffffffff2220844287,0x31b2254f02),(0x0,0x0)]
def wu : List bw := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def wt : List (List Nat) := gP
def wN : Nat → af
  | 10 => wH
  | 9 => wM
  | 8 => wL
  | 7 => wK
  | 6 => wJ
  | 5 => wI
  | _ => bS
def wG : Nat → Nat → Option (Nat × Nat)
  | 10 => aR 177 223 4 13 7 2 wB
  | 9 => aR 185 697 7 15 9 2 wF
  | 8 => aR 39 199 6 14 8 2 wE
  | 7 => aR 11 35 3 11 5 2 wD
  | 6 => aR 1 3 1 7 1 2 wC
  | _ => fun _ => none
def ak : Forest := ⟨1215,10,fun j => wO[j]?.getD (0,0),wu,wt,wN,wG⟩
set_option maxHeartbeats 0 in
theorem dd : aJ ak (aD ch) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=4) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def bp (j : Nat) : Nat := 0x764260437506145074436550744365407443653074436254734362657236165272361651723616317236163071362652713626427136264170435540704355307042554070415550704155407003547070035450672465416714653065360765653607546536074360634121606341106060416160604121605341216050412160134121566307635663075453641483531322715313227053132261531022715310225051643070516430505135227147145542463462604606417142560343425603324256032142530343425303324246037342460371424603434246033242430376374316743743167337431663374316623743164337401475374014633734657337346572363562323635622136356210363462323634622135461480354614403546143035461420313522823135225231352232313522213134223231342221313122723131223231312221310522323101223231012221304656652434038317632675154630701546306015463050154630101545307015453010154230101541307015063460150630601506301014463010135322521313228213132275072455740724555207145574071455640606418106064161060541810605417103645676036456650364566403645483
def bu (j : Nat) : Nat := 0x6453043210043201064500432100432010641306357005416106410043210043201064025174200502100640251742004610006402517420040210064025174200401700640251732003610006401517420050210064015174200301500640103457203042106324067501054021063200675010540210630120364103201006042537420030270052345207130072600523452071300523005234520713004270052344207130052400523052071300623005230520713005230052305207130042600523052071300412005046010432010421040351306420124300403113064201632004031130642012430040311306420123500315406417200162003120021053021061031200210530210310312002105301602103120021043021031030420315240103600304203152401034003041031524010340030410315240102300254064170302604002460057610056201024600576100341010241004321004320102036001674012501020340016740126010203400167400146101450057630012561014500576200451010145005761005620101450057610045201014500576100342010145005761003415101450057610012031014064135200402100140641352003021001402413520040210014024135200302100140241352003017001324023401034021013200234010630210132002340103402101304607241072010013046072410620100062435247003640000624352470034500006243524700273000062007561005620200620075610034102005123542700435000051235427003240000461735642056434004517156020561200045171460207412000412314602037120003247065140651000032470641202506000264362471037520002643624710365200026436247103462000214726531065320002147264310473200014236427104362000142364271043520001423642710325600014236427103251000134746530065400001257465300654000012474653006540000124746530054360001247465300543000012473654206543400124736542054324
def bt : Nat := 0x5021042110c0300c03
def bq : Nat := 0x24914891a0c85405
set_option maxHeartbeats 0 in
theorem yk : Z ak 5 0 2 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x7570) rfl
  decide +kernel
theorem yj : Z ak 5 0 2 := yk
set_option maxHeartbeats 0 in
theorem ym : Z ak 6 0 19 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x6f311660000238033954395f3a36481e4dbfb1) rfl
  decide +kernel
theorem yl : Z ak 6 0 19 := ym
set_option maxHeartbeats 0 in
theorem yo : Z ak 7 0 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0xf456a7442354b2f19185c5c34004fc7ad00d8a4cf9f00a4be00d000a7a99000) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yq : Z ak 7 32 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x6900281b446259441f4e1a250b186118056a663a0718715c536b661845495029) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yr : Z ak 7 64 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x5b4500305300182327273c18131712683b18185d1118451800442b005c472337) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yt : Z ak 7 96 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x1604440027000044006c5a5d511a583269584a182f1a180d1418491866454010) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yp : Z ak 7 128 9 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x1818403d3232183c18) rfl
  decide +kernel
theorem yn : Z ak 7 0 137 := (@X ak 7 0 64 73 (@X ak 7 0 32 32 yo yq) (@X ak 7 64 32 41 yr (@X ak 7 96 32 9 yt yp)))
set_option maxHeartbeats 0 in
theorem yv : Z ak 8 0 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x930097c585d69c0000848a00a4008f0000b6a88700820088b6808a0000000000) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yC : Z ak 8 32 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0xb0d2a0cbd7a2000000b5b2a3bd008a84ca8981c4848e00829d00aa84c3bac898) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yG : Z ak 8 64 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0xd5b5bfaaa4c00000b583a884d3c6bc84bbd984ac009fb400cc9e84cd92b8c100) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yH : Z ak 8 96 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x8484a997a3a5d48484c3ce9ac58084a18497c5d1bfa4aa00a6a88080b6b9b6d1) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yw : Z ak 8 128 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x2d5646645b00582828462842005b188684a4d6a4b9848b8a8484a3bf009600ae) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yx : Z ak 8 160 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x181846063e5846581828564518155d28555b2863180a18185d00585b563e582a) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yy : Z ak 8 192 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x282846734500004626235b5d465a5b27671815186e18185823092a2d5e181828) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yz : Z ak 8 224 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x16582818181846464667581c5818462346241826185e18585b2c586d334c0046) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yA : Z ak 8 256 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x58115842284618285b18211808181828465b5b410e732045082358005d15183e) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yB : Z ak 8 288 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x2c6a4572183f581822416e585801235b083e182843461818232c0856575b1d6d) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yD : Z ak 8 320 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x465d00452852112d0c4558461858232c56234658330818285b182a5b1846185b) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yE : Z ak 8 352 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x2e2d5246235b43283f18185e6546286a01574546000027181818282d5d004618) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yF : Z ak 8 384 3 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x181827) rfl
  decide +kernel
theorem yu : Z ak 8 0 387 := (@X ak 8 0 192 195 (@X ak 8 0 96 96 (@X ak 8 0 32 64 yv (@X ak 8 32 32 32 yC yG)) (@X ak 8 96 32 64 yH (@X ak 8 128 32 32 yw yx))) (@X ak 8 192 96 99 (@X ak 8 192 32 64 yy (@X ak 8 224 32 32 yz yA)) (@X ak 8 288 64 35 (@X ak 8 288 32 32 yB yD) (@X ak 8 352 32 3 yE yF))))
set_option maxHeartbeats 0 in
theorem yJ : Z ak 9 0 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x0) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yK : Z ak 9 32 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x8494bf9d84d6b6b6bba48c8dbfb381d600000000000000000000000000000000) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yL : Z ak 9 64 32 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0xa49bc284d681a4d600d6d60000918184bdc5008484b4d697daa4ab9d8400c984) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yM : Z ak 9 96 26 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x8cbf8495d68a94b7d6d6c9af94bfa4a481848481a499ccb48c) rfl
  decide +kernel
theorem yI : Z ak 9 0 122 := (@X ak 9 0 64 58 (@X ak 9 0 32 32 yJ yK) (@X ak 9 64 32 26 yL yM))
set_option maxHeartbeats 0 in
theorem yi : Z ak 10 0 10 := by
  apply aB (pos:=bt) (neg:=bq) (kw:=bp) (panels:=bu) (data:=0x0) rfl
  decide +kernel
theorem yh : Z ak 10 0 10 := yi
theorem du : cE ak 10 := by
  intro k hk
  interval_cases k
  · exact az ak 0 0
  · exact az ak 1 0
  · exact az ak 2 0
  · exact az ak 3 0
  · exact az ak 4 0
  · exact yj
  · exact yl
  · exact yn
  · exact yu
  · exact yI
  · exact yh
set_option maxHeartbeats 0 in
theorem dk : aH false (K 1215) 10 (aF 1215).toFinset := dB (q:=191) (prior:=aD ch) (ag ch cP) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rv : ac false (ad 6847) (K 6847) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=0) rfl rfl (ag ch cP) dd du (by decide +kernel))
def jA := au ch 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxHeartbeats 0 in
theorem vE : ai false jA := aw (m:=6847) cP rv (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qJ : ac false (ad 18111) (K 18111) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=1) rfl rfl (ag ch cP) dd du (by decide +kernel))
def i6 := au jA 11 [(14143,[135,50,65])]
set_option maxHeartbeats 0 in
theorem u8 : ai false i6 := aw (m:=18111) vE qJ (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qE : ac false (ad 17087) (K 17087) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=2) rfl rfl (ag ch cP) dd du (by decide +kernel))
def i1 := au i6 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxHeartbeats 0 in
theorem uY : ai false i1 := aw (m:=17087) u8 qE (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qO : ac false (ad 2239) (K 2239) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=3) rfl rfl (ag ch cP) dd du (by decide +kernel))
def i9 := au i1 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxHeartbeats 0 in
theorem vd : ai false i9 := aw (m:=2239) uY qO (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qU : ac false (ad 2751) (K 2751) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=4) rfl rfl (ag ch cP) dd du (by decide +kernel))
def jf := au i9 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxHeartbeats 0 in
theorem vi : ai false jf := aw (m:=2751) vd qU (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qH : ac false (ad 1727) (K 1727) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=5) rfl rfl (ag ch cP) dd du (by decide +kernel))
def i4 := au jf 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxHeartbeats 0 in
theorem u6 : ai false i4 := aw (m:=1727) vi qH (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q2 : ac false (ad 42687) (K 42687) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=6) rfl rfl (ag ch cP) dd du (by decide +kernel))
def ji := au i4 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxHeartbeats 0 in
theorem vl : ai false ji := aw (m:=42687) u6 q2 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rq : ac false (ad 58559) (K 58559) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=7) rfl rfl (ag ch cP) dd du (by decide +kernel))
def jx := au ji 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxHeartbeats 0 in
theorem vB : ai false jx := aw (m:=58559) vl rq (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rm : ac false (ad 58047) (K 58047) 11 :=
  aG (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=8) rfl rfl (ag ch cP) dd du (by decide +kernel))
def jv := au jx 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxHeartbeats 0 in
theorem vy : ai false jv := aw (m:=58047) vB rm (by decide +kernel)
set_option maxHeartbeats 0 in
theorem ra : ac false (ad 44223) (K 44223) 11 :=
  aG (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dk
    (aX (g:=ak) (i:=9) rfl rfl (ag ch cP) dd du (by decide +kernel))
def bz := au jv 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxHeartbeats 0 in
theorem cQ : ai false bz := aw (m:=44223) vy ra (by decide +kernel)
def w2 (i : Nat) : Nat := 0x4c88f1a284060808057fc10
def xa : af := (1,1,6,0,0,0,0,w2)
def w6 (i : Nat) : Nat := 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def w1 (i : Nat) : Nat := 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def w9 : af := (11,2,6,0,0,10,0,w1)
def w5 (i : Nat) : Nat := 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def w4 (j : Nat) : Nat := 0x5e531855aca28df80d3485b10aff144a303b08ac2279015e40503fc243f74904e6f88cfe84131fd4095e405a6492532492f60487f42099e4055ba01ef5025bee9209cfec0916e8073ee9209c7a808879e449669080ff091d4057d0116e807bd81208116988c51b8c1680a003e0241874390b410783414020482f090886c0001070642100bd2d8b0ab2a8e8a9f66f9864f8f625819f3761bf6b59860d6e54d414ad153dcdf324ab2487719c4f0f42b054002c92cc12c983ca94cb84cc11eb80cca3ca134aa60cad8a94ab9b89846b856a15aaa38cbc0cbc4a168b846cad4986aa134b9e6c95a9836b9d0c958b9c8a146a956aa58aa46985aca3ffdbff7def7ddfafeffcff618106101060c10608105cc10550104c010
def xc : af := (36,3,6,524295,51,10,1055,w4)
def w7 (i : Nat) : Nat := 0x4200118060050390014553e041769a0
def w3 (i : Nat) : Nat := 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def xb : af := (8,4,6,0,0,8,0,w3)
def xf : Array (ae × ae) := #[(0xffffffffffffffffffffffffffffffa8c12191,0x7c002100),(0x100d1cae,0x38d1cac),(0xffffffffffffffffffffffffffffffc4146207,0xffffffffffffffffffffffffffffffec000203),(0x5308cf8,0x139088f0),(0xffffffffffffffffffffffffffffffa160574f,0xffffffffffffffffffffffffffffff806f560f),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def w0 : List bw := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def wZ : List (List Nat) := gP
def xe : Nat → af
  | 11 => xa
  | 10 => w9
  | 9 => xc
  | 8 => xb
  | _ => bS
def w8 : Nat → Nat → Option (Nat × Nat)
  | 11 => aR 5 23 3 10 4 2 w6
  | 10 => aR 27 69 6 12 6 2 w5
  | 9 => aR 2 13 4 9 3 2 w7
  | _ => fun _ => none
def bN : Forest := ⟨1279,11,fun j => xf[j]?.getD (0,0),w0,wZ,xe,w8⟩
set_option maxHeartbeats 0 in
theorem ol : aJ bN (aD bz) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=3) ?_⟩,aQ (d:=0) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def fs (j : Nat) : Nat := 0x847465507548287565753010647580103578044026643171266431212664311026523060
def fv (j : Nat) : Nat := 0x760215268407140007602152684021500076021526800214000756214263002130007502157680021400075021526800214000724013674201273007012142630021400070121426300213000641207854107502106412078541065021064120785410640710641207854106402106412078501064021041620746810017200405707468100162002305817562075120023058175620651200230581756206417002305817562064120007214135200402100041202345103702100412023401073021
def fu : Nat := 0xa04210842110c0300c03
def ft : Nat := 0xd064a49147434114642a
set_option maxHeartbeats 0 in
theorem yS : Z bN 8 0 8 := by
  apply aB (pos:=fu) (neg:=ft) (kw:=fs) (panels:=fv) (data:=0x304020102040392) rfl
  decide +kernel
theorem yR : Z bN 8 0 8 := yS
set_option maxHeartbeats 0 in
theorem yU : Z bN 9 0 32 := by
  apply aB (pos:=fu) (neg:=ft) (kw:=fs) (panels:=fv) (data:=0x60002090900008096919089008e8f8c9300858b82898494888e8a810087838b) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yV : Z bN 9 32 4 := by
  apply aB (pos:=fu) (neg:=ft) (kw:=fs) (panels:=fv) (data:=0x3050807) rfl
  decide +kernel
theorem yT : Z bN 9 0 36 := (@X bN 9 0 32 4 yU yV)
set_option maxHeartbeats 0 in
theorem yO : Z bN 10 0 11 := by
  apply aB (pos:=fu) (neg:=ft) (kw:=fs) (panels:=fv) (data:=0x9586008d00000000000000) rfl
  decide +kernel
theorem yN : Z bN 10 0 11 := yO
set_option maxHeartbeats 0 in
theorem yQ : Z bN 11 0 1 := by
  apply aB (pos:=fu) (neg:=ft) (kw:=fs) (panels:=fv) (data:=0x0) rfl
  decide +kernel
theorem yP : Z bN 11 0 1 := yQ
theorem uK : cE bN 11 := by
  intro k hk
  interval_cases k
  · exact az bN 0 0
  · exact az bN 1 0
  · exact az bN 2 0
  · exact az bN 3 0
  · exact az bN 4 0
  · exact az bN 5 0
  · exact az bN 6 0
  · exact az bN 7 0
  · exact yR
  · exact yT
  · exact yN
  · exact yP
set_option maxHeartbeats 0 in
theorem dl : aH false (K 1279) 11 (aF 1279).toFinset := dB (q:=255) (prior:=aD bz) (ag bz cQ) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qP : ac false (ad 2303) (K 2303) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def jc := au bz 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxHeartbeats 0 in
theorem vf : ai false jc := aw (m:=2303) cQ qP (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qF : ac false (ad 17151) (K 17151) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def i2 := au jc 12 [(17151,[])]
set_option maxHeartbeats 0 in
theorem uZ : ai false i2 := aw (m:=17151) vf qF (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qV : ac false (ad 2815) (K 2815) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def jg := au i2 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxHeartbeats 0 in
theorem vj : ai false jg := aw (m:=2815) uZ qV (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rx : ac false (ad 6911) (K 6911) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def jB := au jg 12 [(17403,[118,130,81])]
set_option maxHeartbeats 0 in
theorem vF : ai false jB := aw (m:=6911) vj rx (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qI : ac false (ad 1791) (K 1791) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def i5 := au jB 12 [(17405,[82,129,48])]
set_option maxHeartbeats 0 in
theorem u7 : ai false i5 := aw (m:=1791) vF qI (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qz : ac false (ad 1279) (K 1279) 12 :=
  aG (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (aX (g:=bN) (i:=0) rfl rfl (ag bz cQ) ol uK (by decide +kernel))
def iX := au i5 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxHeartbeats 0 in
theorem uU : ai false iX := aw (m:=1279) u7 qz (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rr : ac false (ad 58623) (K 58623) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def jy := au iX 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxHeartbeats 0 in
theorem vC : ai false jy := aw (m:=58623) uU rr (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rp : ac false (ad 58111) (K 58111) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def jw := au jy 12 [(68863,[116,83,32])]
set_option maxHeartbeats 0 in
theorem vA : ai false jw := aw (m:=58111) vC rp (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rb : ac false (ad 44287) (K 44287) 12 :=
  aG (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def jn := au jw 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxHeartbeats 0 in
theorem vq : ai false jn := aw (m:=44287) vA rb (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q3 : ac false (ad 42751) (K 42751) 12 :=
  aG (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) dl
    (bk (prior:=aD bz) (ag bz cQ) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def cV := au jn 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxHeartbeats 0 in
theorem dW : ai false cV := aw (m:=42751) vq q3 (by decide +kernel)
def xx (i : Nat) : Nat := 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def xN : af := (6,1,8,0,0,9,0,xx)
def xF (i : Nat) : Nat := 0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def xw (j : Nat) : Nat := 0x6ffff64904012a7fcc020224b7f64e130f024d2bfafe40a032481e0294604de32d22ffc68564541281bff0144081a63d8b819409fff785350254fffe02f017139c88000001547ebf703c5804a327e1f3e4c0082f1cf1be89c1b0004ec7062909778125ffe0ca5ec0085e09fb70ef058a20000dc5fff81aae0670005ffd7000400fcfea2002aaffec8001025157aa85702d1ae1e9c8400000003ff3fc7f8990414d7fe7f00184005c15620000af597d0ca8a688f6fe300022685f554114bff14d63033dff85f00ccb9c800caef024afe865044340378275f91338fb400f3f404a0073c6fbb0870004c004ff0178007139c9224a93c6a8dbca09400dffea8819f3f0e0085a338ff5f0360058d98227afe40ec8c00004fe7ff61784cbbc09000001f000000138ffe14e3f504e40cc185538033003cfc0464a86819c66172268a04d84e148820c8404551112469184211b10d424450f4fc3981c641855454d52428511404f1394b0a82900c2809c090941f0c00486a170520e0086017c5e16e06490464743a41c6518c6289d565552c42c2487612872188442d0320f8340b1303c1762a1695855d3d4084844d304b51c082018260882e2d96540436024cd324c51488e038120a0bd2b11e2c86d204404a88a210da2550438caf100d43b0f8371270f0b8348900001c0697a94f9158e38c58a386e83a81a7e378274c7106d06b169b6616155e45835535255044aa44941c3e83ca39b3563403132e32b02a526c2151e51b618713f11d0dc0c607204902300090414ae2e57352b8391cd48e6253032c3c90c14ae12560729829619cae3248352c189609ca632570329859605cae2647132a8b9589cb06a48172c0994c04a40d98306c1a32059b060c8126c3c36199b0251862641a8481c2e0d5418ec107482830c498202c18ffffefeff7fbfbfbfefbbdebf549404c1100c010
def xM : af := (48,2,8,655366,67,12,1166,xw)
def xE (i : Nat) : Nat := (if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def xv (j : Nat) : Nat := (if j<1 then 0x53d58f2b3c28eb83a90e78393ce293768dc436c0d91359cd2233fccd432b8c9b31e8c563090c122ff0be22e5cb622d3cb392c18ada2a50a812994a3427f09d626f4992261496024dc8fa233c89b218c82b20607d21e947751d3c7121bb86c21a9467a198461f17d85bc162455014a050a13844ce128c480117842b0fd83d40e4037d0d102f70b4c29309a022507f01d106b417a053c118039c0da031c0b40284066016404600cc020003400095304255c6295717a5661894973e525d195317a5661095313e55c9595714e564629597725641695724a561d695654e55c4f94875a52618959072564df95718254c5595987e554d394918a55c5c95935255cd195515a55c9495315e565d4959872560569531825589795985a5641f95716a5662295656a55c0e9487565641894874652610949772558d394937da61d9688739a5cd169970da26102d9034b6622716559f4c5d698305a4c602d983645897698724b65d12d974a45c0f69516e45c012d9179a6055698744b261691604cb64cb68970cb641c91874e154d568972634c21716356164d490985da24e0688746364e17d9775a661669814da261f2d977235c9391206da649b699181a65d169811a154da91935da609490815da5c112d976a4605791725cb65cc7d7174b659391706da6608912060b655291315e45c1a698750b2614689744b65ce68816da65c969875a45c132d926da21d985313db5c5e689862324992d9649a605a7d4179a615369534a465d32d9169a61da698159a262269916da481b688169a6622689871a6155699381a4c112d987244857697180b646068874a154d3698121a604769706e421d3698569a24602d9189f64dd69816da21da8d718646593698704b644f69826e35c962d916cb64927d4181a6095698559a245b69874e35c9a90814e365e191514da66182d9131a61c769985245953716555a61c391814c465d11198004261035870c4660421932d765c21098604660d259784465c519954a04c571197384660f3d861cf604a81534c464d23d8618464e015963196053618120f644a59900d665c3119548a640d89724ca640051877595c1b5d8205625c3259235760805d820c42614119039764c23d8621d54611d9411e4c5d49850c465d2893085461017553844649b119820f244a59700d26141119180466223d86049648b019715061434d8408c61c305954816545458508264d2398609560830d9217ffffeff7febfbff6fdffb7edfbfeffbff7f6fddf7bdf79eefdd7b7f6ded7d7faef3fe77bff7fafddf7bdf77edfcff9f73de6fc7f4c1524815261d405c5405c140505404c5406193060930605305c5305c130589305813054530481302053060d105cd104c11020d101cd100c1100411061830604305c4305c0304c030204301c43060c10608104c0101cc10 else (if j<2 then 0x294b87d9e18125a4c0d94ff1102129ffd080042d275fc88cc7d08e32d5a4ca1d3e240ca037fc0042243d78c55d1318fe00895fff0e105d3009081b01d1fd4e20010e7b410dc82500e01ff0000d08c5060b310c019f4978ffef011359ed040b978a3df8cc2818025730485f341944407c3d214551e90632fde35400ce503bbfd64a14479ebd08198bf837d44a8044d40dfc218819dbe3fb489689a11fd4cfa8410a203b8c33a15081a8f482827f7a6d123c1044da94fef4220672ff8fda88267aebe1881981af92c46490191206189cd483f27d448490174c4a3c749363910d1e90630ef8780361ff911abdb383b610b5f13eba1b0203547ec9e824206907fb855000c14449c5d78852e1c8ad47cc58b8f0853da088ff1343221a0f764452011fdd10858604791431a4bbe9cd63940d22e1078c2057cbebd8aa49a3359ed0427c0af2080034400017c0bbe142f9501b60af51a91d3e015c308f48d5aaf7fb0e401527fcb0c8f4880466b0029f743c2871a470e26782bd46a479fea3fe0240932f282e30219bffe705d071346fc66140c0128a067b410f6821ed040efce05fa1e10d25033da087b410f6821ed04281c0e41a23c2e3080f21c82d0944b4cc4ab92ce2024c969130ec472814036174444546487c211c18800fa1ed3c6140189d9240742621c03786b6b0562abd2aa65822014464402444813026719d05a6686b1984442810b1861861dc22c9108c4700420840a0a125175b8d0fa8491844c10c39881a022281e0f2a006d41e96524896817824458500ca4084731d22819a8e88710c116154208188740800f0dc18d0622c43623134400c041dc3ab410e64af12e2d12b4c795a0211a4c89017184ac703384681383b00e220c8188a0d08a490d1a151cc378b28a70f0bc1ea0a42d09180e0385108e88686e0fc0813f0686165689024b11a661a3108784014819060ac461ff0584347c17695a070700e43604a0d216e0307c8499649f2066215043f30f06e0d2881070d40f81d83606a0bc2683ac4801c0004c00c0ba6cd9a72682994e633984a5e997565c39642569950a523942e4f4936a4c0925246e917643e908e4048f223ad8e4e3788d5a32f8c462db8aca27f895e23f88aa204874a1ba866e175854e13484520f9833a0b682ba09281f205780ae00f7fc9fd57ecdf9e7e21f357c11ef47b11ea87959e2c7871dfa7741da57601d607501d0e73d1ccf728dc83718dc4870b9c0b6f8db9f6dfdb596ccdb046b9dac76aa1a8a69c1a3267699c26695979652991363e18c86259878611981b5fd17d85eb57775d2d7275c216be5a8567e598962858455e256a558f559d51e53ad4d2529d49851f1456510541650013d74ead37c4d3d3384c4d2ee4b052a149c5249489120c47b91ce46bd18e455112744210ea430108b413901e402cfe43efcf8 else 0x2f02307bc14abdfc307b7cc69f38145081a23fe881901ef881084fe013a08547682bc08c9d1ec34420438ffa252847172f00810a97f7d114b9618fbd23190f884c4f4813469ff92003369f84009499a625fde088bd9571903cb803233ffc88b000204443891835f70913be00324f1dc2c8dded86c01980f500a327ffc4d185021e1eaea8810aefea20a20021c3a7c2c0199718110f88498f25040429bfca5410010e5d2cc70e2c3a137e3d9104747e100211bfe003255f98051aff1044a87d89218cffb7184019ca08c87321269f5983a927e8501b41251f09a0f6b1888a174c4a3578cfd210bcc0c3ed2197fffc5a3080e0854206d53f4482041535911d8fe7e60441647c503243e1da8c958204200811a1fe7da913334029feb118511ff95848330f73e7400488bfa10023cf83f022cfaa80230379971f140d0bd62a22ffcc0411b7fe140a09234f15091b7a4be1159fe903cc780896fed48a13dfa9b0021400d7b0dd44fa02228de1002133aacb806633f2003a90193ffd31033c7db499213760a107c56322af8e408a3437a247fe881e00c000d411ff87d00ad07f708804df7f90499f420643be040300a502e0cffc28cfdb7f8547a889a4efe012ede01555805373f061200010e3fa8822a3a7aa090010e1ff850001986fd2c68238d7c222ebfff2a428517fc9ba8410a1f71f44c041257e97c411b32a943297ffffd6190000804d75e700646fe1268cb5ff104ccfcff9208000445cd025064fff4c40ce5fc1be9a60a06959f41125d9df21a1483f1fded08000440da5ff84202501a17fb00de7c02061295c0253e904197a409b4cc798240ffe02840cc6e4128bfc82002175fe9da0021adfcfcc2a1437bfa24010219fec02de721f20a0b1e1050cc027924e7086cfd42065dbea0a2100a657b3a1c08577de82042d61ab1a8fe008b97fa808bb9e8091a5dd54108077c7d86cc024403fc56420a194fc88518f58c28b9e184a8033f3ff4214410a1e9ff6e9016358512bd7c54440093b110c3e3680033698595029012ff94541840888b876c06054c5fe564c819b9f40090801ff67a58611f58220371f4120e0af50952483fd0610217de28040850fffc0150dba624048da7c412d9a924df302a3bbec500))
def xL : af := (259,3,8,2490403,102,14,1251,xv)
def xD (i : Nat) : Nat := (if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def xC (j : Nat) : Nat := (if j<1 then 0x5a2c6b4e344b82353242352c282e4709b5145eb04a292e47c9b4afc2152e1f2e2a66aa76942a4e8cb494622e2e0cb491c9950529240a0c34b454330e5eae4cc9b511e6aa4717ae4989b4ed1a346149b4f20f341467a633e32a2c54130ed41512c234ebe2ae0e9632a5c9b4748215244f344d8f34cd8f152ddeae490e342ca7a831e12e485eae50cab46ad634460f34e654130a02352b89b517142604941317e12e300e344409b4375432ea54b2e5cf150dd62ca9cf34a69a302c4f34c68234c9dc30f354130d669536692e474f34268e344a89b4751b2a2d1c30f30234e9d41517d41312c9b42fdeb4e0e5aa7709b4af57b245cf150e423525e3ac079eae48dda635692e48272a27c13524c13449c1344e811503c135255ba63384b4d544b4e341353110b4662626160e942981352d013475d394318894318d34665332e1c19526c134380db44686349516a832933440863483049522d594060bb4a644b4e390b2b112350290b2a588344547b470972616d0aa69c8344f4834021ca630982e01a1ae2e0834424bb4ad90aa38252a271e241764aa47013509891511552a69c5b4b04b34761ba8320134c9d534661d263145b4a259ae01592e238db4464a34ed81352cc135314134e9cd342705b4af90aca9daae0105b4b0a0ae289e2a48de2e48c934154115359032a0202e2e001522c0b4408fb0c292b040642a470734024334a346b44243b4834534a244344342b4e351328011b0807ff3febfdbfcffb7f7bf6ff6bf5ff5bf4ff4befbe7fdfbdf7df3defdebdd3bfbbf7befbebbdfbdbbd7bbfbb7b7fb7baffafbaf79ff9fb7ef7eb7b777f77b75f5ff3ff3f73ef3eb3bf3bb3af37f36f2beffaff2feefeafdafbef7ef7af6eefedfabfebfabf6beebdebdabcebbeb7eb5eafeaeeabea7e8fe7fe7fa3fe3ee2fd984c15264530549714c15226130548914c15265d20549714815254d205495148152645875013161d4024d875009161d4064d71500985c54024d71501715c1405057050187505405c541501315054065d31501904c5405c531500984c54025d3150192619305c1864c15161930481864c09161930205864c1726093021d824c0816093021d814c1985c530641714c0985c530589704c1315c130485704c0815c13061d624c18558930605624c17258930595624c15158930261624c08758930615604c18258130595604c08758130609514c17254530261514c1964813061d204c18548130605204c172481305c5204c17048130595204c16348130581204c15348130545204c08748130205204c195205305c8814c1532053021c814c17360d105c183440985cd105c530440974c11065c834419161830245860c09760430619710c1941c43025d83041976081064d82041874c01061930041854c01060930041981cc1064073041821cc10 else 0x36285bf610c3eb16a0f78313259a16018b360a9f1020ef08ac84e1493586087710ef811806dc08f490f0c6a2601ae5091c1046648f7d2431b843c342afe64645d2134087bd144b9847522ee8c4dc189c047018f390d40b2e8594b1081edd0b3e0241dec472b4246af906806788830d068cb760514584df0120f2e850c1058f0f0212ae845fa09e01cca15e22d910c023488b22f7a20b6b88720e689161514304a0dbca8c60e8e20d8076910fd81107a90d80738421704153cc4838e04c75c018cfa233c22ea4d147229c443187434d85e01bbdd050c0a029f98a7213bd9053f810ce11201bc030704135d0af090ef113809617a19e1120378896350dbae58d7e021a7f93416538447e035025020fac5622cfe9244cb3f121cd550c7b8864c89013b01d795318f350dd01ba037a03b66826fc0477920b7f311117f8218f421cb2d5070ea9419d9157940032cf021d52c5bc14368113221798506e80d0127f446265d68920dec0680a3e0631c422051e818c991172c18eb8031da118bc40835e821bf00c4f086ce0733429aa12fec110fc119028f818f734260200e30411f80c9b234047fc04859147c0c63a843c721a0e384719239fc10ce05bef922003ffe3641203e90c6650ff58992bf5c4c93f1c110003813ff024e7f081932f1432f4d18f39aa643fe2240373ed140dcfb45df7c91013c18dcad880270dc441c26b480c20266c458909250d2e0e8874ac26092b88420217891a0d54742281b6482c81d0747281a198119450c3dc381a4a5e26c27825823e0d20001d02301746741d4c4443144021780780c17119a25e1755c6c3c25749010c0d501824c2079640e40f813e19f0901b344081825016c0035060181340e81fc01801f8901f81f01a81300bc0bbe2fdd3d87d57ce7cabc77c23bb3b73b43af3aa3a53a079e39a79538fb8c788382f7e378b73b6fb68b6476135ab55f52b4df49345f4273d33a335f3172e72a72371ef1ab13f10f0d304eff6fc2f52f0eebee42e02db2d76d36cfacb2c8ac52c1abc2b6eb0eab6a529ee98294e9168b286282e7ea79672a6ce67262a5ea59655a50a4ba4824463ee3b638e3423062ae2522161e61aa1561160c2086051ff5fb5f8df51f01ea1e45db9d7dd39d09cd9c8dc59bcdb75b21acda91a65a259c59719358f98b98698197c17516f56a563d5d55955154c547d4293f53b934d3112e52591f11ad1811290e90bd061024fc0f64f24eb8e64e20dccd8cd48d04ca0c54c28bd0b88b58b34ae4aa0a58a2c9cc99493c8e888083c7f87a076c7046505c85504dc4703b43402e82802181b81400c80600002353797ae57d433049fb027d634c6141314d634e609b4cf68ae2729ae26deae4b142e3814130f1eae4d18ae0ea2263428952709b4efa924178c34b714152d49b4cfdeae4949b4355b14ad)
def xS : af := (203,4,8,5505121,119,12,1118,xC)
def xJ (i : Nat) : Nat := 0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def xB (i : Nat) : Nat := 0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def xR : af := (28,5,8,0,0,10,0,xB)
def xI (i : Nat) : Nat := 0x2022120a00481835bb4200000707b100030
def xA (i : Nat) : Nat := 0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def xQ : af := (7,6,8,0,0,6,0,xA)
def xH (i : Nat) : Nat := 0x78001b2d178400008
def xz (i : Nat) : Nat := 0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def xP : af := (3,7,8,0,0,5,0,xz)
def xG (i : Nat) : Nat := 0x1e0
def xy (i : Nat) : Nat := 0xd41d1505c4da54cb94817254530
def xO : af := (1,8,8,0,0,0,0,xy)
def xU : Array (ae × ae) := #[(0x840a108bec0006,0xd3584ac0e0a004),(0xffffffffffffffffffffffff24640550c50029,0xffffffffffffffffffffffff2c85b1021f1821),(0xffffffffffffffffffffffff61200154008957,0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),(0xffffffffffffffffffffffff000b70212005e1,0xffffffffffffffffffffffff28a2b4371545e1),(0xffffffffffffffffffffffff8880028a0a427f,0xffffffffffffffffffffffff04a7252e0a5a3b),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def xu : List bw := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def xt : List (List Nat) := iJ
def xT : Nat → af
  | 12 => xN
  | 11 => xM
  | 10 => xL
  | 9 => xS
  | 8 => xR
  | 7 => xQ
  | 6 => xP
  | 5 => xO
  | _ => bS
def xK : Nat → Nat → Option (Nat × Nat)
  | 12 => aR 35 135 6 13 6 3 xF
  | 11 => aR 470 589 6 16 9 3 xE
  | 10 => aR 338 423 6 15 8 3 xD
  | 9 => aR 9 55 5 12 5 3 xJ
  | 8 => aR 3 13 3 10 3 3 xI
  | 7 => aR 4 7 1 9 2 3 xH
  | 6 => aR 1 3 1 8 1 3 xG
  | _ => fun _ => none
def aA : Forest := ⟨1407,12,fun j => xU[j]?.getD (0,0),xu,xt,xT,xK⟩
set_option maxHeartbeats 0 in
theorem eC : aJ aA (aD cV) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=4) ?_⟩,aQ (d:=1) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def bC (j : Nat) : Nat := 0x965808769465755094657540946575309461755092462752855829948558298485582975855829648558295485582153824627738246275382462752823627738206276281756661817566518175664181756640817566206567401065614010656040106557417565574153655141856537501065374070653740106530401056854187568541655685314356784170567640705675419056754180567541705675316056752150560640805606407056064060560640405603408049568574495685734847668442482343424823324247233242452343424523324176809041768070318412323154128526783191267831212678311026763191267631212675412126184171261841612618412126083191260541812453237314678090146780101461801014608070146080501460801013451272
def bF (j : Nat) : Nat := 0x82306318240152300810252493100532008015021683021531076255694810653000762326318002751007620569180038400076202691800762000750208924604653107361519420050210070352810670142300703228196702845006783004321004311067136584900463000670365849004830006350690857005460063406918570054600634069185700485006340691857004350063200786120761310632007861206502106320078612057021063200786120541810632007861205402106320078612043021063200786020850210632007860207502106320078602065191063200786020650210630531470204312006012648130040260054077183620671200540771836205217005267091485008530042654735820407300426007658201073004260076582010630042600765820096200426007658200862004260076582007510041730756930017300370208612004017103407907562037050031569275130642300307214263002140003016947530075400030121426300214000301214263001830002765068950056411027600689500564010276006895004530102713352490039400027133524900384000271335249003450002710352490034500025800543290032410240691856207512002406918562065120024069185620641800240671856204716002106928531075320021069285310642800210692853105726002106928531053260020569485300754000205694853006840002056948530064380020569485300643000205694853005320002036012780029611020360127800236110201694853007540002016948530068400020169485300674000201694853006540002016948530064800020169485300643000201694853005730002016948530053260016720598600576010167205986004650101620263180032610015360168920045110132681962007621001326819620068210013268196200651000123683962005428000765826713056230007628269170451200067283674206743000621463581040610006214635800305100054601687200346100346006875004571003284135200402100032681962007621000326817620076210003268176200659100032681762006521000321413520040210002674730820407300025683764207643000256837642065320
def bE : Nat := 0x241408410842110c0300c03
def bD : Nat := 0x11489414e86824914642a
set_option maxHeartbeats 0 in
theorem ze : Z aA 5 0 1 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x43) rfl
  decide +kernel
theorem zd : Z aA 5 0 1 := ze
set_option maxHeartbeats 0 in
theorem zg : Z aA 6 0 3 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x2c1125) rfl
  decide +kernel
theorem zf : Z aA 6 0 3 := zg
set_option maxHeartbeats 0 in
theorem zi : Z aA 7 0 7 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x342d2111268edc) rfl
  decide +kernel
theorem zh : Z aA 7 0 7 := zi
set_option maxHeartbeats 0 in
theorem zk : Z aA 8 0 28 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xc392711360349312e3522002836140833a799cededfcfa894bde2bc) rfl
  decide +kernel
theorem zj : Z aA 8 0 28 := zk
set_option maxHeartbeats 0 in
theorem zm : Z aA 9 0 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xb7bfcd9fa6b889a5b8cfa50098c8918700000000000000000000000000000000) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zq : Z aA 9 32 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xcfd59c9d84b89aa3c5b89ae1a2cc009acf9e00e0aba6a4dba5c6d89fd0009ed1) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zr : Z aA 9 64 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x36441a4c3a409f9f9f9f9fd992839fb88a009f9fa3a3d48b009fb4b290a99bb0) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zt : Z aA 9 96 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x363638481036363624122438242f15383b2b1f1332194c3638301c3c0b383624) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zn : Z aA 9 128 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x638384d0d45381230171d41023836003c060f242016183e4b4718120b241c36) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zo : Z aA 9 160 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x5363715073a361e0b38361b1538123606363b060923361204013606004c3829) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem zp : Z aA 9 192 11 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x3838382a1238123800000a) rfl
  decide +kernel
theorem zl : Z aA 9 0 203 := (@X aA 9 0 96 107 (@X aA 9 0 32 64 zm (@X aA 9 32 32 32 zq zr)) (@X aA 9 96 64 43 (@X aA 9 96 32 32 zt zn) (@X aA 9 160 32 11 zo zp)))
set_option maxHeartbeats 0 in
theorem yX : Z aA 10 0 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x0) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y3 : Z aA 10 32 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x0) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y4 : Z aA 10 64 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xa6af00009fa60086c3b3c49fa68db6d6e500b09f9581c0a08cc0000000000000) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y5 : Z aA 10 96 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x86e381b8d786889fc3a681a686beaa93868600b1869fcbb000c9b5a6b19fbb86) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yY : Z aA 10 128 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x84ca81d29586ca00b8b200cab000d300ca82d39fb8a6b9c3ca869f00dae485ae) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem yZ : Z aA 10 160 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xca81d286aa9f86009f9f86c0a19facadc7ca939f808fa68db0ddb6c1a6939f00) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y0 : Z aA 10 192 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x364d3f36060036360f12000f0f4d4606ba9fb8b8b8879fc29686979f00b09f00) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y1 : Z aA 10 224 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xf0f000f4e4600364d423d36420036004a060646063d0b4d0e0f4200000e4d) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y2 : Z aA 10 256 3 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0xf0006) rfl
  decide +kernel
theorem yW : Z aA 10 0 259 := (@X aA 10 0 128 131 (@X aA 10 0 64 64 (@X aA 10 0 32 32 yX y3) (@X aA 10 64 32 32 y4 y5)) (@X aA 10 128 64 67 (@X aA 10 128 32 32 yY yZ) (@X aA 10 192 32 35 y0 (@X aA 10 224 32 3 y1 y2))))
set_option maxHeartbeats 0 in
theorem y7 : Z aA 11 0 32 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x0) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem y8 : Z aA 11 32 16 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x0) rfl
  decide +kernel
theorem y6 : Z aA 11 0 48 := (@X aA 11 0 32 16 y7 y8)
set_option maxHeartbeats 0 in
theorem zb : Z aA 12 0 6 := by
  apply aB (pos:=bE) (neg:=bD) (kw:=bC) (panels:=bF) (data:=0x0) rfl
  decide +kernel
theorem y9 : Z aA 12 0 6 := zb
theorem eK : cE aA 12 := by
  intro k hk
  interval_cases k
  · exact az aA 0 0
  · exact az aA 1 0
  · exact az aA 2 0
  · exact az aA 3 0
  · exact az aA 4 0
  · exact zd
  · exact zf
  · exact zh
  · exact zj
  · exact zl
  · exact yW
  · exact y6
  · exact y9
set_option maxHeartbeats 0 in
theorem eI : aH false (K 1407) 12 (aF 1407).toFinset := dB (q:=383) (prior:=aD cV) (ag cV dW) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qQ : ac false (ad 2431) (K 2431) 13 :=
  aG (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=0) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def jd := au cV 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxHeartbeats 0 in
theorem vg : ai false jd := aw (m:=2431) dW qQ (by decide +kernel)
set_option maxHeartbeats 0 in
theorem qA : ac false (ad 1407) (K 1407) 13 :=
  aG (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=1) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def iY := au jd 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxHeartbeats 0 in
theorem uV : ai false iY := aw (m:=1407) vg qA (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rk : ac false (ad 54143) (K 54143) 13 :=
  aG (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=2) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def ju := au iY 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxHeartbeats 0 in
theorem vx : ai false ju := aw (m:=54143) uV rk (by decide +kernel)
set_option maxHeartbeats 0 in
theorem rc : ac false (ad 44415) (K 44415) 13 :=
  aG (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=3) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def jo := au ju 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxHeartbeats 0 in
theorem vr : ai false jo := aw (m:=44415) vx rc (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q7 : ac false (ad 43903) (K 43903) 13 :=
  aG (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=4) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def jl := au jo 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxHeartbeats 0 in
theorem vo : ai false jl := aw (m:=43903) vr q7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem q4 : ac false (ad 42879) (K 42879) 13 :=
  aG (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) eI
    (aX (g:=aA) (i:=5) rfl rfl (ag cV dW) eC eK (by decide +kernel))
def fU := au jl 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxHeartbeats 0 in
theorem kK : ai false fU := aw (m:=42879) vo q4 (by decide +kernel)
def yc (i : Nat) : Nat := 0x16ad2728c1ee6b16a4a0e629062082fff
def ye : af := (1,0,5,0,0,0,0,yc)
def yg : Array (ae × ae) := #[(0xfffffffffffffffffffffffffffffff8278ca9,0xfffffffffffffffffffffffffffffffe078829),(0x8c5796,0x1884792),(0xfffffffffffffffffffffffffffffff819b865,0x31b824),(0xfffffffffffffffffffffffffffffffe1200db,0xfffffffffffffffffffffffffffffffec400d9),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def yb : List bw := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(42624,0,42879,0,13),(43648,0,43903,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(60032,0,60287,0,13),(69248,0,69503,0,13),(49168,0,49647,0,13),(55312,0,55791,0,13),(43072,0,43455,0,13),(58432,0,58815,0,13)]
def kT : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def yf : Nat → af
  | 14 => ye
  | _ => bS
def yd : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => yg[j]?.getD (0,0),yb,kT,yf,yd⟩
set_option maxHeartbeats 0 in
theorem om : aJ xd (aD fU) = true := by
  simp only [aJ,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=3) ?_⟩,aQ (d:=2) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem uy : Q xd 14 0 1=true := by decide +kernel
theorem ln : Q xd 14 0 1=true := uy
theorem uL : cI xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q xd 0 0 0 = true)
  · exact (rfl : Q xd 1 0 0 = true)
  · exact (rfl : Q xd 2 0 0 = true)
  · exact (rfl : Q xd 3 0 0 = true)
  · exact (rfl : Q xd 4 0 0 = true)
  · exact (rfl : Q xd 5 0 0 = true)
  · exact (rfl : Q xd 6 0 0 = true)
  · exact (rfl : Q xd 7 0 0 = true)
  · exact (rfl : Q xd 8 0 0 = true)
  · exact (rfl : Q xd 9 0 0 = true)
  · exact (rfl : Q xd 10 0 0 = true)
  · exact (rfl : Q xd 11 0 0 = true)
  · exact (rfl : Q xd 12 0 0 = true)
  · exact (rfl : Q xd 13 0 0 = true)
  · exact ln
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lH : aH false (K 511) 14 (aF 511).toFinset := by
  have h : aH false (K 1535) 14 (aF 1535).toFinset :=
    d6 (g:=xd) (i:=0) rfl rfl (ag fU kK) om uL (by decide +kernel)
  have e1 : K 1535=K 511 := by decide +kernel
  have e2 : aF 1535=aF 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
set_option maxHeartbeats 0 in
theorem rh : ac false (aF 511) (K 511) 15 := cF (hints:=13438558465) (by decide +kernel) lH
def jr := au fU 15 [(511,[])]
set_option maxHeartbeats 0 in
theorem vu : ai false jr := aw (m:=511) kK rh (by decide +kernel)

def jV (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def gt (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< jV i)
def hD (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< jV i))

set_option maxHeartbeats 1000000 in
theorem ko :
    (∀ i : Fin 9, bit (gt i) cC ≠ bit (hD i) cC) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (gt i) (inputs.getD j.val zero) =
      bit (hD i) (inputs.getD j.val zero)) := by decide +kernel

theorem uP (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = gH) (small : C.size ≤ 15) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 14 else 15) ∧ Live u cC k inputs.toFinset := by
  have goalEq : (d3 C.gates inputs).getD C.output zero = cC := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (uz C legal C.output r).trans ((congrFun computes (f9 r)).trans (md r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, cD g=false) ∧ C.gates.countP (fun g => !cD g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, cD g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !cD g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !cD g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !cD g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := eW (u:=u) (d3 C.gates inputs) C.output
  rw [goalEq] at out
  unfold bV at out
  have pg : bit 0 cC = false := by decide +kernel
  rw [g8 pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := mj C.gates inputs legal mono iP
    (out.resolve_right (fun h => h iP))
  have ns : inputs.all bT = true := by decide +kernel
  rw [jY ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←gT] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply fj run inputs (inputs.getD i.val zero) sub (gt i) (hD i)
        (ko.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply ko.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem mc
    (m : ∀ k, k ≤ 15 → ¬Live false cC k inputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Live true cC k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 gH 15 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := uP C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

abbrev fy := Nat × Nat × Nat × List Nat
def g6 (rows : List fy) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def kz (base : List (Nat × Nat)) (e : fy) :=
  (aD base e.2.2.1 == e.2.1) && fC e.1 e.2.2.1 e.2.2.2
theorem jU {u base rows} (h : ai u base)
    (cert : rows.all (kz base) = true) : ai u (g6 rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [kz,Bool.and_eq_true,beq_iff_eq] at hh
    exact ig hh.2 (hh.1 ▸ ag base h r.2.2.1)
  · exact h e hb
def uO : List fy := [(151,5,94,[48,33,133,118]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(223,9,478,[80,16,33,50,116,131,100]),(239,9,127,[32,83,116]),(247,9,478,[48,33,133,118]),(254,8,251,[32,83,116]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(350,8,95,[128,49,100]),(369,5,94,[16,82,131,100]),(371,8,95,[16,82,131,100]),(375,9,127,[16,82,131,100]),(381,9,127,[48,129,82]),(440,5,94,[81,130,118]),(444,8,95,[32,49,128,81,116,100]),(446,9,127,[32,49,128,81,116,100]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(463,9,127,[16,32,48,128,100,80,116]),(471,8,251,[16,82,131,100]),(477,8,251,[48,33,133,118]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116]),(491,9,127,[128,81,32,49,100,116]),(493,9,127,[80,129,50,116]),(499,9,478,[32,83,116]),(501,8,251,[80,16,33,50,116,131,100]),(505,9,478,[16,82,131,100]),(506,8,251,[128,49,100]),(510,12,255,[32,49,128,81,116,100]),(1279,12,3579,[81,130,118]),(1407,13,28143,[32,49,128,81,116,100]),(1503,12,18911,[128,49,100]),(1527,12,3579,[16,32,48,128,100,80,116]),(1531,12,18911,[48,129,82]),(1791,12,17405,[48,129,82]),(1967,11,4927,[32,49,128,81,116,100]),(1983,13,17343,[48,129,82]),(2015,12,17403,[48,129,82]),(2039,12,17403,[80,129,50,116]),(2045,12,17151,[48,129,82]),(2431,13,9599,[16,82,131,100]),(2493,11,2239,[48,129,82]),(2495,13,9599,[32,49,128,81,116,100]),(3263,11,1375,[80,16,33,50,116,131,100]),(3391,11,1343,[81,130,118]),(3519,13,28143,[16,32,48,128,100,80,116]),(3571,9,11742,[32,83,116]),(4955,8,1725,[81,130,118]),(4991,13,17343,[16,32,48,128,100,80,116]),(5053,11,6847,[48,129,82]),(5111,12,17403,[16,32,48,128,100,80,116]),(5115,12,17405,[16,32,48,128,100,80,116]),(5117,12,17403,[48,33,133,118]),(6511,11,1343,[16,32,48,128,100,80,116]),(6606,8,1119,[16,32,48,128,100,80,116]),(6639,13,28143,[81,130,118]),(6654,12,18911,[80,129,50,116]),(7039,13,17343,[81,130,118]),(7150,11,6847,[128,49,100]),(7166,12,17403,[128,81,32,49,100,116]),(8167,11,1727,[16,82,131,100]),(8175,13,17343,[32,49,128,81,116,100]),(8183,12,17405,[32,49,128,81,116,100]),(8190,12,17151,[32,49,128,81,116,100]),(8679,11,2751,[16,82,131,100]),(9702,8,2237,[16,82,131,100]),(9710,11,2239,[128,49,100]),(11710,9,18814,[81,130,118]),(11711,13,28143,[16,82,131,100]),(11773,12,18911,[81,130,118]),(12716,7,2079,[32,49,128,81,116,100]),(12719,11,2367,[32,83,116]),(12733,11,2239,[80,129,50,116]),(12735,13,9599,[81,130,118]),(12781,9,2429,[32,83,116]),(12783,13,9599,[16,32,48,128,100,80,116]),(13310,12,27127,[48,129,82]),(13806,11,2751,[32,49,128,81,116,100]),(14191,11,4927,[128,81,32,49,100,116]),(14269,11,6847,[80,129,50,116]),(14303,12,17403,[16,82,131,100]),(14310,8,1725,[32,49,128,81,116,100]),(14319,13,17343,[16,82,131,100]),(14333,12,17403,[80,16,33,50,116,131,100]),(14334,12,17405,[16,82,131,100]),(17342,9,7038,[81,130,118]),(17406,12,17403,[32,83,116]),(18429,12,27127,[128,81,32,49,100,116]),(18779,8,11453,[81,130,118]),(18815,13,28143,[32,83,116]),(18939,12,18911,[16,82,131,100]),(18940,9,11742,[81,130,118]),(27623,11,2751,[80,16,33,50,116,131,100]),(28079,11,1343,[80,129,50,116]),(28134,8,11453,[16,82,131,100]),(28155,12,3579,[128,49,100]),(28157,12,3579,[80,16,33,50,116,131,100]),(28158,12,18911,[16,32,48,128,100,80,116]),(32750,11,2751,[128,49,100]),(37374,12,27127,[48,33,133,118]),(42719,9,48094,[80,16,33,50,116,131,100]),(42727,8,42679,[16,82,131,100]),(42867,8,42591,[16,82,131,100]),(42943,13,44927,[81,130,118]),(42951,7,42683,[16,82,131,100]),(42995,9,48094,[32,83,116]),(43003,12,44799,[81,130,118]),(43447,9,46455,[81,130,118]),(44287,12,58335,[48,33,133,118]),(44415,13,58239,[48,129,82]),(44479,13,58239,[48,33,133,118]),(44511,12,68863,[16,32,48,128,100,80,116]),(44539,12,58335,[48,129,82]),(44541,12,68863,[80,129,50,116]),(44791,9,48094,[128,81,32,49,100,116]),(44915,8,42679,[81,130,118]),(45039,13,44927,[80,129,50,116]),(45041,7,42711,[81,130,118]),(45047,12,42751,[80,16,33,50,116,131,100]),(45051,12,42751,[81,130,118]),(48063,13,44927,[32,49,128,81,116,100]),(48079,9,42623,[16,32,48,128,100,80,116]),(48095,12,42751,[16,32,48,128,100,80,116]),(48111,13,42879,[16,32,48,128,100,80,116]),(48126,12,44799,[32,49,128,81,116,100]),(48635,12,58623,[81,130,118]),(49403,8,43479,[16,82,131,100]),(49643,9,46455,[80,129,50,116]),(49662,12,58623,[32,49,128,81,116,100]),(50047,13,58239,[128,49,100]),(50143,12,58335,[128,49,100]),(50158,11,58047,[128,49,100]),(50159,13,58239,[128,81,32,49,100,116]),(50167,12,58335,[128,81,32,49,100,116]),(50174,12,68863,[32,49,128,81,116,100]),(51135,13,54143,[81,130,118]),(51151,9,43647,[16,32,48,128,100,80,116]),(53086,8,42679,[48,33,133,118]),(53183,13,42879,[32,49,128,81,116,100]),(53198,8,42679,[32,49,128,81,116,100]),(53215,12,42751,[48,33,133,118]),(53229,9,44925,[32,83,116]),(53231,13,44927,[32,83,116]),(53244,9,48094,[16,32,48,128,100,80,116]),(53245,12,44799,[48,129,82]),(53246,12,42751,[32,49,128,81,116,100]),(54206,9,43647,[32,49,128,81,116,100]),(54253,9,43647,[80,129,50,116]),(55039,12,58335,[80,16,33,50,116,131,100]),(55231,13,58239,[80,16,33,50,116,131,100]),(55279,13,58239,[80,129,50,116]),(55287,12,68863,[16,82,131,100]),(55294,12,58335,[80,129,50,116]),(55789,9,46455,[128,81,32,49,100,116]),(55799,12,58623,[16,82,131,100]),(58111,12,68863,[32,83,116]),(58301,11,44223,[48,129,82]),(58363,12,68863,[128,81,32,49,100,116]),(58814,9,46455,[48,33,133,118]),(60251,8,44733,[48,33,133,118]),(60380,7,42711,[128,49,100]),(60382,9,48094,[80,129,50,116]),(60396,8,42679,[128,49,100]),(60409,9,48094,[32,49,128,81,116,100]),(60411,12,44799,[128,81,32,49,100,116]),(60414,12,42751,[128,49,100]),(63871,13,64447,[81,130,118]),(69053,11,44223,[80,129,50,116]),(69055,13,58239,[32,49,128,81,116,100]),(69094,8,44221,[80,16,33,50,116,131,100]),(69111,12,58335,[32,83,116]),(69118,12,68863,[128,49,100]),(69561,8,42679,[80,129,50,116]),(69617,7,42711,[128,81,32,49,100,116]),(69619,9,48094,[48,129,82]),(69627,12,42751,[128,81,32,49,100,116]),(69628,9,48094,[81,130,118]),(69630,12,44799,[128,49,100]),(73703,11,64191,[16,82,131,100]),(73710,11,64191,[32,49,128,81,116,100]),(74214,8,44221,[128,49,100]),(74218,7,44155,[128,81,32,49,100,116]),(74222,11,44223,[128,49,100]),(74223,13,58239,[16,32,48,128,100,80,116]),(74238,12,58335,[16,32,48,128,100,80,116])]
def pri := g6 uO jr
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vH : ai false pri := by
  apply jU vu
  apply aQ (d:=6)
  simp only [bB]
  repeat' apply And.intro
  all_goals decide +kernel
def us : List fy := [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def hM := g6 us dz
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vI : ai true hM := by
  apply jU kJ
  apply aQ (d:=6)
  simp only [bB]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (ae × ae) := #[(0xffffffffffffffff0247102040c820c0830811,0x3f03f81ff800001f8000),(0xffffffffffffffff04c1040881096109041223,0xffffffffffffffffffc000000007e000007fff),(0x888245902104218288206,0xfff800001ff81f8000),(0x111008902432803260844c,0xffffffffffffffff000000001fffe007e001ff),(0x302182060608060410c08,0xffc0fc07e0001ff8007e00),(0xa004820208841484826190,0xffffffffffffffff0000000000001fffe07fff),(0x4420410491010901141020,0x7fff81fffff8000),(0x280820430a040604082080,0xffff0007ffffe000000000),(0xd030c38414021802104140,0xfffffff800000000000000)]
def moC : List bw := [(43072,0,43455,0,13),(43010,0,43517,0,12),(42512,0,42991,0,13),(42624,0,42879,0,13),(42560,0,42943,0,13),(59905,0,60414,0,12),(43648,0,43903,0,13),(256,0,255,0,12),(42504,0,42999,0,12),(2,0,509,0,12),(42752,0,42751,0,12),(43536,0,44015,0,13),(69121,0,69630,0,12),(42500,0,43003,0,12),(49153,0,49662,0,12),(32,0,479,0,12),(42528,0,42975,0,12),(17,0,494,0,11),(53776,0,54255,0,13),(1152,0,1407,0,13),(50704,0,51183,0,13),(66,0,445,0,11),(52737,0,53246,0,12),(1056,0,1503,0,12),(4,0,507,0,12),(48256,0,48511,0,13),(8,0,503,0,12),(16,0,495,0,13),(1032,0,1527,0,12),(1,0,510,0,12),(1028,0,1531,0,12),(53824,0,54207,0,13),(128,0,383,0,13),(1600,0,1983,0,13),(132,0,379,0,11),(2180,0,2427,0,11),(0,1,460,50,8),(24,0,487,0,11),(69136,0,69615,0,13),(47617,0,48126,0,12),(48132,0,48635,0,12),(50816,0,51071,0,13),(55305,16,55782,0,8),(11265,0,11774,0,12),(9,16,486,0,8),(49168,0,49647,0,13),(55312,0,55791,0,13),(1280,0,1279,0,12),(12305,0,12782,0,11),(43584,0,43967,0,13),(58624,0,58623,0,12),(59920,0,60399,0,13),(34,1,460,16,6),(47633,0,48110,0,11),(68624,0,69103,0,13),(7,0,504,0,7),(36,128,347,0,8),(40,256,151,64,6),(58432,0,58815,0,13),(13825,0,14334,0,12),(13841,0,14318,0,11),(160,0,351,0,11),(260,8,227,16,6),(1538,0,2045,0,12),(18433,0,18942,0,12),(1544,0,2039,0,12),(1568,0,2015,0,12),(32,1,460,18,7),(10,4,369,128,6),(46208,0,46463,0,13),(60032,0,60287,0,13),(6145,0,6654,0,12),(27649,0,28158,0,12),(5,2,440,64,6),(27664,0,28143,0,13),(2112,0,2495,0,13),(1792,0,1791,0,12),(52753,0,53230,0,11),(44676,0,44923,0,11),(18560,0,18815,0,13),(47744,0,47999,0,13),(55304,0,55799,0,12),(43266,64,43197,0,8),(57984,0,58239,0,13),(16897,0,17406,0,12),(0,4,369,138,8),(0,8,227,276,8),(58373,0,58874,0,8),(12297,16,12774,0,8),(49161,16,49638,0,8),(54800,0,55279,0,13),(44608,0,44991,0,13),(2208,0,2399,0,11),(46084,128,46427,32,9),(0,2,440,69,8),(52800,0,53183,0,13),(42628,0,42875,0,11),(3,0,508,0,9),(44096,0,44479,0,13),(57920,0,58303,0,13),(2176,0,2431,0,13),(6657,0,7166,0,12),(44164,0,44411,0,11),(12304,0,12783,0,13),(0,64,189,258,10),(5,0,506,0,8),(2,4,369,136,7),(47632,0,48111,0,13),(69184,0,69567,0,13),(73233,0,73710,0,11),(4740,0,4987,0,11),(55297,16,55782,8,9),(258,64,189,0,8),(1,32,94,384,7),(47680,0,48063,0,13),(69128,0,69623,0,12),(2084,128,2395,0,8),(42532,128,42843,0,8),(40,0,471,0,8),(43048,0,43479,0,8),(8,4,369,130,7),(257,32,94,128,6),(52752,0,53231,0,13),(3136,0,3519,0,13),(54848,0,55231,0,13),(59968,0,60351,0,13),(53888,0,54143,0,13),(32273,0,32750,0,11),(54801,0,55278,0,11),(0,128,347,36,10),(1,16,486,8,9),(4,128,347,32,9),(46116,128,46427,0,8),(13840,0,14319,0,13),(50752,0,51135,0,13),(4736,0,4991,0,13),(6784,0,7039,0,13),(69248,0,69503,0,13),(7681,0,8190,0,12),(47624,0,48119,0,12),(73745,0,74222,0,11),(320,0,191,0,11),(2,64,189,256,9),(32,128,347,4,9),(264,0,247,0,9),(6153,16,6630,0,8),(15,16,480,0,4),(9232,0,9711,0,13),(54785,0,55294,0,12),(13826,0,14333,0,12),(69122,0,69629,0,12),(27656,0,28151,0,12),(8,16,486,1,9),(47625,16,48102,0,8),(48164,128,48475,0,8),(296,0,215,0,7),(64064,0,64447,0,13),(63616,0,63871,0,13),(44546,0,45053,0,12),(3076,0,3579,0,12),(44548,0,45051,0,12),(57888,0,58335,0,12),(47872,0,47871,0,12),(2114,0,2493,0,11),(68674,0,69053,0,11),(1216,0,1343,0,11),(1,2,440,68,7),(4,8,227,272,7),(11328,0,11711,0,13),(68672,0,69055,0,13),(73729,0,74238,0,12),(27650,0,28157,0,12),(52738,0,53245,0,12),(44552,0,45047,0,12),(46112,0,46559,0,12),(58112,0,58111,0,12),(6161,0,6638,0,11),(12354,0,12733,0,11),(2240,0,2367,0,11),(2368,0,2239,0,11),(0,16,486,9,10),(12,0,499,0,9),(18,0,493,0,9),(33,0,478,0,9),(256,64,189,2,9),(0,256,151,104,8),(13833,16,14310,0,8),(69129,16,69606,0,8),(7696,0,8175,0,13),(49680,0,50159,0,13),(12352,0,12735,0,13),(16960,0,17343,0,13),(9344,0,9599,0,13),(59906,0,60413,0,12),(44036,0,44539,0,12),(68616,0,69111,0,12),(13329,0,13806,0,11),(69144,0,69607,0,11),(64066,0,64445,0,11),(69123,0,69628,0,9),(27657,16,28134,0,8),(46090,0,46581,0,8),(59923,0,60396,0,8),(1060,128,1371,0,8),(69127,0,69624,0,7),(256,8,227,20,7),(130,1,332,48,6),(49792,0,50047,0,13),(68609,0,69118,0,12),(69124,0,69627,0,12),(47648,0,48095,0,12),(17152,0,17151,0,12),(9233,0,9710,0,11),(27160,0,27623,0,11),(144,0,367,0,11),(60064,0,60255,0,11),(4800,0,4927,0,11),(42688,0,42815,0,11),(64320,0,64191,0,11),(58368,64,58557,258,10),(58370,64,58557,256,9),(59910,0,60409,0,9),(49160,16,49638,1,9),(10,0,501,0,8),(59940,128,60251,0,8),(52897,0,53086,0,8),(257,0,254,0,8),(58626,64,58557,0,8),(260,0,251,0,8),(2,1,460,48,7),(8,256,151,96,7),(18,1,460,32,6),(136,4,369,2,6),(39,128,344,0,4),(0,0,511,0,15),(6160,0,6639,0,13),(44560,0,45039,0,13),(64,0,447,0,13),(44160,0,44415,0,13),(44672,0,44927,0,13),(11266,0,11773,0,12),(16898,0,17405,0,12),(44034,0,44541,0,12),(4612,0,5115,0,12),(27652,0,28155,0,12),(57860,0,58363,0,12),(4616,0,5111,0,12),(44064,0,44511,0,12),(59936,0,60383,0,12),(44288,0,44287,0,12),(6673,0,7150,0,11),(7704,0,8167,0,11),(68632,0,69095,0,11),(73240,0,73703,0,11),(80,0,431,0,11),(1616,0,1967,0,11),(1156,0,1403,0,11),(1168,0,1391,0,11),(58016,0,58207,0,11),(44544,64,44733,258,10),(47617,16,48102,8,9),(52739,0,53244,0,9),(42508,0,42995,0,9),(52754,0,53229,0,9),(48160,128,48475,4,9),(11297,0,11742,0,9),(48,0,463,0,9),(65,0,446,0,9),(50817,0,51070,0,9),(288,0,223,0,9),(0,32,94,385,8),(54793,16,55270,0,8),(69190,0,69561,0,8),(258,0,189,0,8),(17154,64,17085,0,8),(44802,64,44733,0,8),(49412,0,49403,0,8),(59911,0,60408,0,7),(69134,0,69617,0,7),(35,0,476,0,7),(42552,0,42951,0,7),(44700,0,44899,0,7),(256,32,94,129,7),(44812,0,44787,0,7),(53025,0,52958,0,7),(24,4,353,130,6),(160,1,332,18,6),(13,16,482,0,5),(152,4,353,2,5),(141,16,354,0,4),(73744,0,74223,0,13),(52864,0,53119,0,13),(12801,0,13310,0,12),(36865,0,37374,0,12),(49665,0,50174,0,12),(17922,0,18429,0,12),(18434,0,18941,0,12),(18436,0,18939,0,12),(26632,0,27127,0,12),(13856,0,14303,0,12),(18464,0,18911,0,12),(68864,0,68863,0,12),(49681,0,50158,0,11),(68625,0,69102,0,11),(8216,0,8679,0,11),(9240,0,9703,0,11),(42520,0,42983,0,11),(4674,0,5053,0,11),(13890,0,14269,0,11),(57922,0,58301,0,11),(12368,0,12719,0,11),(27728,0,28079,0,11),(4752,0,4975,0,11),(42640,0,42863,0,11),(18592,0,18783,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(3264,0,3391,0,11),(18624,0,18751,0,11),(44736,0,44863,0,11),(1856,0,1727,0,11),(3392,0,3263,0,11),(55104,0,54975,0,11),(52736,64,52925,258,10),(44546,64,44733,256,9),(18435,0,18940,0,9),(6,0,505,0,9),(3084,0,3571,0,9),(69132,0,69619,0,9),(12306,0,12781,0,9),(53778,0,54253,0,9),(55314,0,55789,0,9),(20,0,491,0,9),(59937,0,60382,0,9),(50736,0,51151,0,9),(11329,0,11710,0,9),(16961,0,17342,0,9),(53825,0,54206,0,9),(58433,0,58814,0,9),(43080,0,43447,0,9),(129,0,382,0,9),(130,0,381,0,9),(58624,64,58557,2,9),(272,0,239,0,9),(42784,0,42719,0,9),(9,0,486,0,8),(47625,0,48102,0,8),(55305,0,55782,0,8),(68617,16,69094,0,8),(36,0,347,0,8),(4644,128,4955,0,8),(18468,128,18779,0,8),(44068,128,44379,0,8),(57892,128,58203,0,8),(67,0,444,0,8),(134,0,377,0,8),(140,0,371,0,8),(4748,0,4979,0,8),(42636,0,42867,0,8),(44684,0,44915,0,8),(161,0,350,0,8),(52994,64,52925,0,8),(58114,64,58045,0,8),(42776,0,42727,0,8),(47944,0,47799,0,8),(14,0,497,0,7),(44558,0,45041,0,7),(21,0,490,0,7),(73749,0,74218,0,7),(47672,0,48071,0,7),(74,0,437,0,7),(12371,0,12716,0,7),(168,0,343,0,7),(268,0,243,0,7),(18,4,353,136,6),(48,1,460,2,6),(272,8,227,4,6),(272,32,78,129,6),(384,8,99,20,6),(21,2,424,64,5),(41,16,454,0,5),(50,1,460,0,5),(133,2,312,64,5),(138,4,369,0,5),(266,64,181,0,5),(321,32,30,128,5),(270,64,177,0,4)]
def moA : List (List Nat) := kT
def rQ (j : Nat) : Nat := 0x30a206102004e8a0e8c6c0b2eb28da986d9ada8efa1d3d389edfd2bf251de8cb5cd425c1206ddb62a531480c954d524c120661814c53048152605314c120
def rK (j : Nat) : Nat := (if j<1 then 0xad8b0aad8b06ad8aa6adc30aaacb30a6cb2aa6cb0aa6c96aa6c94aa5d302a1ab0299c3029603028ebb926ebb906ebb306eb9946eb9926ed306683b8534438b3212cb300b8b291b012502a524d34f20d34320bb4f1cbb4b1d4aa51cb35114bb4b101b83051309050aa7057260fcbb52f8bb40f94260f80b90f4e302f40b90f0ea60f00b90e8b350e4b340e53b02e53260e4bb70e0bb6ae0bb40e14260e00b90dcc30adceb62d87b82d5e994d26186d26b30caa2a6c92b02c48b8cc2a392bea382bc9382bea360bea342be8330bea322bea300bea220bea192bea174bea152bc2196b98172b02390ad538cad6b88ad7386ad72a6ad7330a97192a9bb6aa69330a6c2a4a52342a1b262a0fb429d53309d92629d134299a262983382951b4295733095db0291f2a28cbb708a0aa2880b8a840b8a800b8080daa480c2a67c0b8a78d2a6780b90740b8472a3066dcb666ab34a6ab39266b38666b36666b34666b32666b30666b17464bb6a600b8a5c5b8a58e35054a36a500b8a4e4b02480b8244a30244c39640c3663c738639636638cb70340b903223502c4b96284b9026430424539020db461c53861a2aa619e3461652a615fb461272a6121b460c73860a2b460a3346067aa606439402838a00299700ab6ee25b30a4119498038247ff8ffd3ff0ff6bfd8ff4ffd2fbf3ef4f7f3dd3f72fd5bf3ebcf6f3d3cdbe7d79f3e7bf9ebe76f9d7e6ef9afe67f97fe5ef95fe3fb8fbe1ff7fadfe37f6dfd37f2dfbb7e6defb7b6d7fb5fcd7df5f6d7bb5dbd6ff5bed6ef5b7d5f7577d3fb3facfdb3eecf7b3d7cefb1ffc7fb1fdc7ef1f7c7bf1dfc6ff17fc4ff0ffbfdafd3bedadfdb7daddbaffa9ffa7f69fba7de9efa6fe7f69dea5fe8ffa3ee87fe1fd2a563505602a542505606c8a9505606c8a9605306cda5245302cda4661206d8a3661206e99564d206dc93645206d893645206c553605206cca9605202e9545c1205cd425c1202e5a154d206d8a954d206c4a954d202e5a54c5202e1a54c5202e9944c5206dca94c5206d8a94c5206d4a94c5202e9984c1202cd984c120661814c12054d814c120549814c1206e5804c1202e5534c12054d524c120661514c120609514c120605514c1202e5514c1206d5314c120605314c1206c8a54c1206d8954c1206d0954c1206cc954c120661a724d2069d9524d206999524d206c8a960d102e993609106d4a9609106cca9609106e9954c9106e5a54c11054d52481106c951481105495148110659a2604306e9926043068991604306c55364420661a3604206e9936042064da154c202e99854c20655a3608106e995608106c99560810651a3548106e993548106d593548106a1935481068d935481068d92548106e582548106a58254810661825481065d825481065982548106558254810651825481064d8254810 else 0x3be9190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2305002fffec004058000000000000000000000007ffcb004a5200000000000000000000000000c0081c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff619148001ffc827bf200584e0ffbc0c200ffc80600f84dbc8c807710e102c029d632d006e32506181d0177035c0f361415300380572c00037f091a14989ae8940cc114815b81a749f0d3815ae10b841d133c21d08b411015c03900d3c0101e40490113a0be81bc00d8dafb5b696d1da1b3f676cdd99b2f656c9d91b1f636c5d89b0f616c1d81aff5f6bdd79aef5d6b9d71adf5b6b5d69acf596b1d61abf576add59aaf556a9d51a9f536a5d49a8f516a1d41a7f4f69dd39a6f4d699d31a5f4b695d29a4f49691d21a3f4768dd19a2f45689d11a1f43685d09a083d97a2f25e0bb9762ea5d0b99722e25c0b51692d059cb31652c858cb11612c057caf15d2b49652c2574ac9552a2534a49452824f49c9352624b4949252424748c915222434849052023f47c8f51e23b4748e51c23746c8d51a2334648c51822f45c8b51622b4548a51422744c895122234448851021f43c8750e21b4348650c217422c3204103c0023b0f30f30f2cf3031881930cf2a508f350fd7b06fd5b22f99a20f86392ec6b80ecf172ecf306ddc364cdd366c9d172c89b82c2ab02bd8972b6d364b29b04b2d2a4b28972b18b90)
def rR (j : Nat) : Nat := 0x6000005c000000000000000080000041000000000000428000000000000000000000000021ff0042000000002c0000080000000000007a03000000001
def rL (j : Nat) : Nat := (if j<3 then (if j<1 then 0x13747209b53804dc9bb864ca24aa65151b2272ecb91186588813743e71a21f3ad28f1d6887813743829b11c2ccc0d026e860db262a09ba142cd40a022e85043702425b31112dc081c6a040b3301c5d970e30cb071965438d3281c65ba0a62d9051b6e8201374106da30838d1839765c14c32c0a69940536dd01026e809836a046da80236d1811c6a004e3460225b90038d4802966001632e00b9960062ca803365001ab2600fd748002db3d016d9b22aa6c1215227025d10002e813ffdffdffe7fefff5ff8ffbffdbfebff4ff9ffbffddfeafef7f6ffb5fd8febff4ffa5fbffd7fdffefdf7afb57cffdfddffeff77f7bf7dfaefbf7dbbe7defef5f77fbb7dd7edff6efaffd7be7ff3fb9f7bffdff6ff77f7bf7defeeff6ffaffcffe7fb3fb9fbcfbe7bf3bf9bfcbfe3fefff7febfddfeafef7f6bf75efef7d5ffaff57f6bf75f7adfd5fe7ff3fe9fbc7fe37f17f69573581655c56058d71581715c16058d70581655096058d4158142505602a5415819864530655914c192645306a5814c152605302a5814c1a824530694914c1a224530660914c19524530648914c1a46612068598480a366120661944819864d2065d934819564d2026193481986452064d9148153645202619148093645206a58448195611206a581481986052054d81480a9605206898048131601206a174481985d12065d73481935cd2061d73481985c12064d70481845c1205cd70481715c12055170481535c12054570481425c12050570481a954d2068553481a054d2065153480a954d20695434819550d2061143481a75052066141481955052065141481845052054d41481a94c52069531481a04c52065131480a94c5206a130481a54c12068930481a14c12066130481954c12064530481824c12060530481804c12054d30481524c12054530481314c1202a530480a84c12029530480984c12025530481a32612068498481a824d2069c93481a624d2069493481a124d20660934819524d2025493481a564d10689934419864d1068d9244198649106559244193649106a583440a960d106a582441956091064d82440a96091064d8044131601106a552441935491060952440a9549106a532441a54c91065532440a94c91069530441984c11060130441534c1104c530441a84811069520441a34811066120441954811064d20441854811060d20441804811054d2044152481105452044150481104c120441a8644306a5810c1a26043065d810c19660430649810c191604306859808153644206a581081a3604206618108193604206a553081a854c20685530819854c2064d53081a564c106a192041a5648106a582041a36081066182041976081065982041956081065182041936081064982041a95481068d520419754810651520419354810649520418254810 else (if j<2 then 0xaa4bd48b95e6e5caf522d57a914abd48955e28dc2e946d570a364b851b15c28dc2d946c96ca362b651b55a28d9ad146c5693b42b451b85928d9ac946c5653b42b2ed98594898ac056cd5d3262ae81815642cc2aa1655550b02aa85515544cc2a226555112a2a87d985346a8a9856e1482b6aa47d98523ecaa9266054932a2a47da85118dc281f6a140fb4aa07da84e3ed4269f69534fb50967da54b18dc241f6c91cfaa48c7db3453ed2a29f68d14fb408a7d95453ec9a29f6e9106374887dba4318dd218c6d50cf9748631b5423ed2a11f68508fb40847d534218d9209f68cfcfb407e7d933f3edd1f0c6e8f863707c7cba3e72dc9eb96a4f5cb267b29533d725c9e9f6d4ecfb50767da53b3edc9d056e4e8fb30747cb93a3edd1c8c6e8e46370727da8393edc9b856e0dc2b626e7cb93718da9b0c6c8d9eb026b495335a4989ab76e4d1bb30691d52346e5c9a116d4cdbb306615b3320adc18a76a0c4fb30629da83018da97bb660b9db705a31b82d76da96bb6a0b4fb505aeda52d3ed296bb660b5db2a5aed852d28dd16146e4b0a3745651b92b76c99555548a8a3745215ba2928dc948c6e4a4a370532d8529a4c194d56e4a1cb725155b828aad994556a0a12b505155a328aacc1439660a2ab2650e59328aac1944a54ca2bb744f5db327aed193d764c9ebb064f5cba274ed4133b66099db264c51b5254ed412bb6609692a64b55522518d9121f6c88cfb44467db9220ada912d6e8856b4442bd52203edd0f8c6e87c636a3e7da51f72d10fba69479d3443ce9521e18d98e9f6e87063743831b81c74d88e1f6cc6cfb46367d531b3edc8d056d4695b4632ad53193edd0c0c6e860636a307da5186ea98c1f6e05cfb622e7da8173ed08b9f6e458fb722a7d98154cc08a9f6e850637428ada8146ed409b76844dbb7024ddb21272da88b96cc45cb7020e5b31072d4081f6a040fb6a1e7db30f3ed2879f68c3cfb721c7d950e56d286ab68c356b4a18b5a30c5aa9862f6942d7b4616c9ba0a3edd050c6e829936614e5b20a64d2853268c29917414d1a50968d184b454c25bb741031ba086eda840c6d421bb4a10dda3086ea984396d41dcb4a0ee5a30772a9839f6cc18fb460c7db9050adc02b46a00da34606ddba023edd010c6e809936a04dda8023ed4013768c09cb7002e5a80172d180b96e401cb520095a30072c9804a54c00c1536268a9b004d9d7826cabc13755809b2a906d9d3882ce883b6d4009ba9c0cdbcb076da5813672008b98d085d41c05ce026284fe61b67a0edb3d026c5e81172f208b976045cb7822e9b4336ed861b66c0edb36026d5b0f174ced8b36754cc318b6e58a32a6c02cb95f20daaf50605789364b635b6591eda2c906cd64bb30aa6198542ed3a8186994013749e61a64f04d923022e91011748609b54204d9a1026ccf else 0xc34db2612ad930d36c5869b04c34d8161acdc30566cd82b362c1598160aca9b0564c582b170c165b85fb2d9afd96c97ecb04bf64985f50caac28545614362aca1985650caab286055942a2aca1985350c0a9bc60541e2a498f1534a78c1a4bc61521e2a48ea1534578a822bc4c115e37488f1b34478d1a23c2e911e34a86f1a14378d021bc54905434480f1833f50c19fbc4c0fde3747cf1b83e78d41f3c684f9e3407d59b93dacd99ed66c4f6b3607b59a93dacd19ed6684f6b3407b59933dac989ed64c0f6b1727af1853b50dc9d286e0e9433074f1ba3978dc1cbc6a0e543046ea1813778a91b59548d69b70694db234a6d89a53608d29b02694d8233a6a919d9614c2cb0a5b65ba2cb2dc96596ccb2cb745765b92bb2da95d9694aecb2a5765532ab2dd14a86e8a6cb7252f1b929b2dc14956e0a6cb605365a82950d414d9660a5e3305364ba29b25c94d66e0a2b36650f1522378da8fbc6e871e37038f1a81c78da8c3c69461e3022ef1ba0a78d9853c68c282b616e7d98b77cb2da3e58ed0736366f973b31cd8d943596c0fae75e7da2ab3e51559f2a6a923674e7d98a746a953856d698fb314c7d95a63ed4529f6a290fb4b487da8a33ed2d19f68a8cfb4f447da4a13ed1d09f28e846363407da7a018d8cf8c6e274fb513a7da19d18dacd8c6c66cfb4b3631b99818d9cb8c6e258636b2c7d87953edd4a0c6c650f975287da3933ec9c99f24e4d5b2724ac9392185cc8856ce40fb27207d30900ad9c7856c63c29751c30b98e18d8c62d64e2c637114b5878a18d9c4146c62063631051b88728d8c3bb6621e0aeb0e51b98682c9c2c1612160b27090584849ac241946e608a361052d548228dc40d566202aaa70051b37f9ac23fc15cdfda168fc7da97d185cbe9f2a5f46372f87da97c3e54be1f6a5ec736cf431b17a3ed4bd1f6e9e06370f031b17868cabb8c6ddd4f974ea7dba7418dc3a1f2e9d1a32ae6d1957218dcb89f6a1c1a168e07ca8703e52b81f6e5bc2b72de7da96f3ecc379f2e5bc6172de7ca96f4ed43727695ba9326dc9ca96e4e543727295b8fb50da31b86c3edab60c6d5b0fb50d87da06c3ec2b61f541b0f90ad8ecb96b4e54b5a76a1a9d972d4ed98694ed43427695a1db30d1495368aaa9343b2e5a13950d09ca56876d9b3bb6c59d3974ceecb567a459b3bb661993974cced9865a4a9b2d5549953b42c8ed986428dd31946e58deb30c6f58263a4a9b1d55498ca172c651b2627ac0b1524c58a9372c231b961a4d930d26c5869360c31d5261a45cb0b72e5869152c355ba604add30556cd809b62c155b060aad4305566181cb30c13d536094a9b0552e982a952c154a860aa4c30146e97ca372bf49b35faad92fbb6617e5b2abf5d815fa4a9afbb2e57ca172bf49b95ea4daaf116d57a934abcdd985ea4caaf516057a7)) else (if j<5 then (if j<4 then 0xd65ad969659d965658d961657d95d656d959655d955654d951653d94d652d949651d945650d94164fd93d64ed93964dd93564cd93164bd92d64ad929649d925648d921647d91d646d919645d915644d911643d90d642d909641d905640d90163fd8fd63ed8f963dd8f563cd8f163bd8ed63ad8e9639d8e5638d8e1637d8dd636d8d9635d8d5634d8d1633d8cd632d8c9631d8c5630d8c162fd8bd62ed8b962dd8b562cd8b162bd8ad62ad8a9629d8a5628d8a1627d89d626d899625d895624d891623d88d622d889621d885620d88161fd87d61ed87961dd87561cd87161bd86d61ad869619d865618d861617d85d616d859615d855614d851613d84d612d849611d845610d84160fd83d60ed83960dd83560cd83160bd82d60ad829609d825608d821607d81d606d819605d815604d811603d80d602d809601d805600d8015ffd7fd5fed7f95fdd7f55fcd7f15fbd7ed5fad7e95f9d7e55f8d7e15f7d7dd5f6d7d95f5d7d55f4d7d15f3d7cd5f2d7c95f1d7c55f0d7c15efd7bd5eed7b95edd7b55ecd7b15ebd7ad5ead7a95e9d7a55e8d7a15e7d79d5e6d7995e5d7955e4d7915e3d78d5e2d7895e1d7855e0d7815dfd77d5ded7795ddd7755dcd7715dbd76d5dad7695d9d7655d8d7615d7d75d5d6d7595d5d7555d4d7515d3d74d5d2d7495d1d7455d0d7415cfd73d5ced7395cdd7355ccd7315c7f7081bbe6d49afa6aa1a5567819a2658993764318ba61d98165f197625cc16f25abd66458cd5e9567556954994e3525544c503d3c44de932c4b792a1497922047791a5455d12643bd0b141b90404034fc43e1cf453c28ecd3a58e50384cdcc35e4d3d33d4cab31d4c342fa4baa2d90b252ba8aa32964a1f278c9ac25dc93d24188d4226486720f87ff1f007871d1c6fb1b08690195c61217705a615c452d13e44b311b443f10103b00dec3380bb02b60a1023407f81b7055c118037c0b201cc03e000143056f1142b688aa5ac450ad622e7653987b078c0d73c54ab9e2435cf181ad7890d6bc616b1e30358f150ab78d4d52854aa143654ea152a750dad32854a99e2a54af152a478c3cf3c61679e3073cf1819e78c1ce3c60671e15138f1519b78c1cd3c61665e30732a1ba9878dccc3c66261e32730f0b99850c3cabc4c651430726f15093789849bc6e646c36322a1a99178dcc7156e238ab6b1d65b08e78a8c54264e26130913094189b2cc43596e60acb6105659382b2c2415954dfe7168fca1a97d785cbe956c9f1434ef8a1a27c50d0be3c6a5ecab62f539957778c3babc2e1d2732ae539877278dcb8bc655c5e30ae0f1507078cc37a864dbd4170dea0a86fb2c2b73c6059ec970cd64a866b24c33596e98ecb72c765b563b2d9b1d96c98ecb50c765a563b2d131d96618ecb2ac7658263b254b1d92958ec92ac7658262b2c0b1594c58a9b7 else 0x180081d40d58634b5a67040841c19b03581e04120b211506f04200e00c957b18c985045203482640b149f369029d0a4a2504c70400c2024a4f302014cc5ca0d5197044c18e2170ff085841a115130190e076060439839454a2450bc23403c3137ba81b610305c38cb8c8077d1b70c780c03806603700b3428307839a44a05204260ac137c1dc056022847a09d03e0ff453c4cc02d05d85e0e060770228a3440b0a01e7830078c11801f8b9c4ba20d03a82206805cb0ad82360782c01d686002ac06d0400ed815037c1d305109180700dc0bd415a0e01c685740502bd004092043022511d82b801d0cf02b843811e0bf0be813e2001f685345cc0503500e4068c09016015a819817e0e786f804055e02700f803a0bc0f687f425a06e09f0035f9d7c75e9d7875d9d7475c9d7075b9d6c75a9d687599d647589d607579d5c7569d587559d547549d507539d4c7529d487519d447509d4074f9d3c74e9d3874d9d3474c9d3074b9d2c74a9d287475d1b7465d177423d06f413d02f403cfef3f3cfaf3e3cf6f3d3cf2f3c3ceef3b3ceaf3a3ce6f393ce2f383cdef373cdaf363cd6f353cd2f343ccef333ccaf2f6cbbb2e6cb7b2d6cb3b2c6cafb2b6cabb2a6ca7b296ca3b286c9fb276c9bb266c97b256c93b246c8fb236c8bb226c87b216c83b206c7fb1f6c7bb1e6c77b1d6c73b1c6c6fb192c62b182c5eb172c5ab162c56b152c52b142c4eb132c4ab122c46b112c42b102c3eb0f2c3ab0e2c36b0d2c32b0c2c2eb0b2c2ab0a2c26b092c22b082c1eb072c1ab062c16b052c12b042c0eb032c0ab022c06b012c02b002bfeaff2bfaafe2bf6afd2bf2afc2beeafb2beaafa2be6af92be2af82bdeaf72bdaaf62bd6af52bd2af42bceaf32bcaaf22bc6af12bc2af02bbeaef2bbaaee2bb6aed2bb2aec2baeaeb2baaaea2ba6ae92ba2ae82b9eae72b9aae62b96ae52b92add0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562d50b522d40b4e2d30b4a2d20b462d10b422d00b3e2cf0b3a2ce0b362cd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22bc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2adbab4eacbab0eabbaacea79a9c6a69a986a59a946a49a906a39a8c6a29a886a19a846a09a8069f9a7c69e9a7869d9a7469c9a7069b9a6c69a9a686999a646989a606979a5c6969a586959a546949a506939a4c6929a486919a446909a4068f9a3c68e9a3868d9a3468c9a3068b9a2c68a9a286899a246889a206879a1c6869a186859a0aa7d99dfe7779dbe7679d7e7579d3e7479cfe7379cbe6f49bb26e49b726d49b326c49af26b49ab26a49a726949a3268499f267499b26649972654985a60e96) else (if j<6 then 0x99f821d9fa046c0068900008fcdf90b0602589153f02bb02c8617f96ae0f011c7b104702ad1020a18d6a29ffb4c883c046c0478a0fe1c136f683104a3543c2067c18404e219ffc9901060c2041c4a3f060df84b40800913effa61909c80c200bc50016ffdf823830806f1415fc2b51620536917e6fcfa24c202710005fae490101653835f3039ffa623d10027a64e8100587f7c0001bf97a610096280803ffe046cd27801594688e9800bc12344c025a70035f00baa097bb115e627be14b30baac6501e086f7c9c0c978000809c48bf87db188105a1c00d7fe3d42041588279c33ac4082f10017370d02041688020fe16008094c01ff690ee3200813563fc9c2888105a1c1cfffb96304081244821f37c5010488810958beffe6851900456837fdd6038708100389000000005f053fcca241eff66f38548608f82619e61e9b34d3f468e00a16d14428ae783ca0cd2d09d11cf073140cb30f3444fbf988157c0e7088e78382af81cd10fcf06300a616c8462279f8c02ab44321e128a073f1b3ef01aa1c801bf837e43a9a00006b885fad43c181c54bbeae9adfc18bbae09a8742ffec130946ce11fb0d0251b387c2bf61a049c6813d6aabf2d1200dbb91b3491fd32d517589d5a71fe4cac2f185e4457f2cb5dd6299a113fe8099798819a400f921e6244eb08162b7f8bac85e4ce9257f7733b3414eff17590bc99d279f8f2694e4404ad12cfeaf2d00c2c36f1cae8d240c933f75d86220849afff812050022106a3ee5f330a102ab7fc5a0718020822275f8f1715000420889b87e3c2820a73e1882501103b4817ffff0ae06c501103b66ffec2284941273d3fb3025011483513fd3808604002144c503ffba2003190d3f1c485a4324025eae9c044400213ac58dff1301c4b0922ff7602184e2096224000000003fc3bfb7970009bc00f100de0ef0b440057f0e847175a21f80c20150a6fcda028881042200017fa6db970c2fcdf310000c3c448c81c409a69484f414b8aac4a603a432c6c61d31c986324511e929346509a8162060870607c0d606116c88191348da45d25a909492816c1520a8053c2d401ae1d689b46614b0a5052791a0e8007aa58c30af0e0582ec28c0a2084c80652a14d94b58dacb562db35da16c2461a0671b0e89d84d36a9bf42260b500b04481c7a9396b589609b633d278c282c205d011da4c6020b0d22ea1cc6c84ed1ee80c2e0156d57ca874a760fb13592a9840df0b9051014082ab5720b099615908f886817472b37c0248e58e0f41185794e66ed074e3042ea114e04846f0200ca06380630cb00d83a917884690c951120d8778a366ab2282d943be11b08f019442623d06287ec220aff079880c6d08e12df05e0dd07090b022d01ed07c32d8ca8b740b90a806a0c4522a80d50e614316a8f409c14304740061670a30a8855 else 0x8df904283c4000000abf939119a6629800000000000000000000000000000000000000000000000000000000000000cffd08b59234a000000000000000000000000000000000000000000000000000000000000000000000000000001dbcb1665b880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe4d7eff252488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029fff80d9e40694eb01163000000000001e0f0a08946a87000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057fe4c20470a01d7e3fc33449620026c0031ffabfc400746100822c00000000000000000003b8ff24eac40ab400000000000000000000000000000000000000003bfec8060c202710000013fffebe900c1840028b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005be029164d068632a00000000013ff57fb60290460000f7fc0005393f0060c531a00000000010ff829f9e6940c91e00000affd3830a8b668d160013ffa603601cfa2b4500000055f9008296054aa000000001efffc852172c4b0093c8a5fdcf09c154574e009e17c019806b4f6396bc0371057195306620000023ffd96277022b14071f281c06400675000000047f01bcdb72b010f1a000bf829f1b7930049140000000025ff07be19040c31cf7d48d568e52cbff6a6a23bc650e0033db84bab0022240067e0fd7882c022c4c7edc0c302d9)))
def rS (j : Nat) : Nat := (if j<1 then 0x1caa00019150000000000000000000000000000000084ae2cf80b68a0000000000060accd2000100f800000000000000000000241400060be000609e00000000000000000000000000000000000000214a00044940000000000607603580000000000000641200040660000000000615c00000000000000000000123d000041b80010210000000000000061060000000000000000000000000000000000000001680578000000000083f0000000000120260500000000000000000000000000000000000000000000000097022a4a602d000000040b80448000000214000020e40000001841000000000000000001834800001680000000000000000101e000000000018068001b2ea15a0000001056000022e00000000000000000000000008178000000200400000000120eb782f26a2000000000000008388000000000000000000520001a398000150813800000a800040f60000000000000000000000000000000000000000000000000d508034000000000000010c1800000000010250eb8000000000062cc0000000000494000000000000000000000000000000000000000000094fc12200000900000001a3be03c000000000020298330000000000100940018230000000000000000000004162000000000000000000000000000080380004ad80000000000000000000060f2000000180892b40000000000204a00020d80000000000407400280000000000000000000000001038000848000025581660002143009a0a000000003ac8000000000000000000000000000000000032b800000000000000000000085900d00000c0800c00da0000000cd68001846c01c81c800200000000000000000000000000000004f5c00000000000000000000000000000000000000000000000000000000000013181b800103eeebc8238000000000000060ae0000000000000000000ea00000b7019000000048b600000000000000000000000000000000000000000000000000000000000614400041460000000000000000000000000000000207e000000000060700000000000000000000000000000000000104300000000000000000000060bb829331aa56800000000000000000000000000000000003094000000000000000000001843800023c00000000000000000000000000000000000000000040aa00000000000000000000000060438110000000011c0004010000095e00000f800000000000000000000080a80000000000000000085860a20000000000402e000000000000000000000000000101a00008058000baa60ee000000000000000000000822000000000000000000000006c000626200000000000000000000002c8000a46a06284f80008498000000000000000440182400c12288180091c125021a08803120000b00a200 else 0x401f853000084d8000000604c0000000000000000000f0000000000000018268434000000008160060000001840000000000000000000000205400000000000000000000000000000000000000245200060400000056811800131200000050000000094e0000000000000104b603600000000000000000000004c80000004f49847c108000000000000000000008000000000000000000000031204e000000000000000002058000000000041020000000000000084b800000000000000c6e030c1560000000000000000ec0de00028a800000018b080000538001bd40000000000000000000000000000000000000000000000000000000000000000000000213400040e600000000000000000000000000008458000916000000000000000000000000000000fe0000000000000000e00000000000000000000000000000000000000000000000000000224000080c8000000000102c00000000000000000000061100000001998800000000012520000398800000000000000000000000081e800010e84320000000000000000020c000022f800000000000000000000000000000000000000000000000000000000000209c0000000000000000020dc0000000115800083b0000000000110a80000000000000000000000000000000814800000060c6000000000000015ad000000000ce000607c0000000000205c00000000000000000000000000000000000000024d84a015400000000000000000000115020e800041520000001a30206a0000000000409800000000004018000000015100c800040d4000000000000000002f5a832a11584f0020144e2c890dce95042a0800b2e124020a69f004ec040000000000000185ae0920000000000000100300009be800000064380000f4a000000000000008298000854000104ee0e0000000022200f400000000000000000000000000000000000021800000000000006061046000)
def rM (j : Nat) : Nat := (if j<3 then (if j<1 then 0xd308fe9547f4cc3da54ded352ee9a1774d03ba651dd2e8ee8a9774cc39a655cd330de9956f4c3b7a5cdbd2a6de9a96b4d2b5a681ad32ad69946b4aa35a2a5ad14ad68956b4d2b3a6859d330ce995674c133a6059d2a6ce95267498b3a6617d32abe9a85b4d2ada6896d330b69a8574d2aba68d5d330ae995574c9aba60d5d352a69a94f4d2a7a68d3d3429e9a04f4caa7a64d3d2a69e8a94f4d125a64d2d2a6969524b498a5a6a51d3468e9a0474c9a3a60d1d34486993434c121a6a4fd34a7e9953f4c29fa694ed330769823b4c09da548ed3506e9a5374cc1ba64cdd2a66e9a22b4a915a68c6d2a6369a8174d08ba6941d3460e953074d180369706b317c187be4b2df258ef82e374963ba4b2d9258eb9a855b598a9acad4d64aa6b5348da8a06d2d0368a86b3143595a1ac950d69276b433b4a39dacc4cd66256b2f2b59595a4c4ad66246b272349891a49c836a636b2b1b5a9886d4c4e6622195310da2846d440d66201b52fc1977dac9bf061df82e8fe59879acc3d964decb08f41737a0b8bd9551ecaa6f65517b2a0bcd6a5d6952e8da571acc38d655c9b08e0da76dacc36d655b9b28dcd846dad4b43695acb40d359469a54b596a19cb4ace5a2672d0b3966196b30ce595672c8b396099cb02ce58066aa9b375499caa2cd53167254b392a19c94ace4986724ab2368d81b42c0da85c6d2ae368576b30bb5955da4aaed6a166b4ab35a259acc2cd6a156b46ab59855acaaad64d56b52a35a94c6d4a6d65536b269b4a94dac9a4d6a511b528b59346ec122d6a4f1b4a7b5953c6d29cd660ecb00755533aa989d96a0d1b506e5a5346d29b968cdcb306b598372ca9b964cd6b266e585372c19b9600dcaa66dd52372a81b94c0d6b505b5a9286d114d648a6b424b5a521ad40ed54c76b5230da319ac98cd6a451b5028da115acc0ad69436b50135a509ad482368c16b2a0b59305ad480368c06b2605d82000d4e0565ef8b09681a9b22b25602a6b0153481a98c054c406a610352f95977debabcf5d1e7ae6f3d717aca13c02a5d4328d80a9698cc33454d9b2a4cd131642d3ae269970352a00a9500d4a602a530152881a93c0549ec64cdb2a46e15134cd11806a4a2b2e51996296c89406a462330301a9152c98a568c44b4a1a9a8094d28406a4123300959704ccb027654143280a593054c90206a402b2e02194012c980a6480fffffeffcffbffaff7ff6feffbffaff7ff7eeffdffdfedfddfbdf7defddfdbfd7fcffbffbbfb7f9ff5cd605c5605c160591605096050560645306053024530661206512064d20645206112060520601205d1205cd205c12054d2050d20505204c5204c1202612024d2064d106491060d10609106011054910541104c9104c110481106583064430604306602064c20644206042054c2065c1064c10648106081054810 else (if j<2 then 0x1d02328b823c5cc4281508341160905ea25246a45614632208c4b43008f817409c09a2d21924f069c18a1f049044a2605882b80aa07a09a2ec0b83b21a059c31c2f039c06c0dc1703e40a05d80841541604340842802c40180c034e2003881e40e037c1d410c2182780ee1bc1ca2980581640ca12a19811a14c08a0b60f405c13c0a60702ac10a0680d024801c02c01c03c04c00ad375a4eb45d683acf759ceb35d663acb7594eb25d643ac7758ceb15d623ac37584eadf55b6ab5d569aacf5596ab1d561aabf5576aadd559aaaf5556aa9d551aa9f5536aa5d549aa8f5516aa1d5316a5ed4b5a95b5296a4ed495a91b50eea19d42ba847506e9c65384a6f94dd29b65364a6b94bbe941522aa35d44ca862508da10b41f683ad06da0cb41767e5cfc39f013de27b84f689ec13d627a84f489e813ce27984f289e413c62750ce999d233a26740ce799ce339a6730ce599ca33926720ce399c6338a6710ce199c233826700cdf99be337a66f0cdd99ba337266e0cdb99a7734ce695cd239a37344e685cd0399f733ce675cce399b7334e665ccc3997732ce655cca39937324e60ecc15981b30165fecbf597db2f965eecbd5979b2cfe5684a2d93692472433c7b08e011aa230cc5bd8ac313c624c444e87f50ec21b3c3148571090e0f0c18a82670322026bffa7f6afda9f91bee67d50f8c9ee4bd7f7a78f40de62bc627814ef15dab3af57516e89dcee397c7258e309c15b7af6ea6db1db2db5e96a96d37da47b4326794cda198332a86478c7158b7b10f6172c1b98132fb35eb8bc2d762ae6f5c56b7616bc2d2d59beb1e560f2baf56baabe1557aa6253eaa6dd4b6291c518ca17d40e27b24e909be136326764c7897f92dea5724a6893fd266249948da90ed1f8a3a746d28c5115f22744468879d0cea14041f482a50269feb3f387ce4f641e633bd076d4ebf9d533a0e7354e511c63386e7014dde1b65361c6a88d389a1f3370659cc8c98d1311460c8bee97962e965bb0b5696582bee56d0ab8952f29ae5224a2513fe27904de898d92e3252e49248f511942288442084e104820183e4c7a20ed71d0438dc6ec8d8e1a5433446378c1316fa2c405670a84148a28004df899b1266239444d086310641fec3e1077a0e7a1c4036786a80cd418882e4059a0aa4143c2660491089c106c1e9038e06a60c74173829304ba08240e7019b029804400678094007800034d4e1a6970d3097e942bf4c3d9a5cebd351569a5ab4d155a662ad32b56992ab45455a296ad145569a9a74d053a64a9d2a54e8a9a744953a6927d3473e9a19f451cfa6626d3512e9a7974d2cba6865d3312e997974cacba61e5d1512e8a59744c4ba6a24d34726998934c9c9a54e4d3311e9878f4d4c5a68e2d341169988b4c9c5a54e2d127169a2874d0c3a60a1d2630e998834cc3fa64df else 0x27f317c0c4100a442dfdd0d2280dffe2d584088135eea4016470197f03001883e0a6f524fffd90cf1020080a279f64531004b43eff3ea88241239fce441004b4381fef4880021698dffbb4208820080a249ffab1104012d0f3fc4820a24817ffd21801004fc45f99988227038005ed9d96b29c1eab0e002db6650e280007be0e717b2cf593518b440cf5932e141eab0e000e36650e2b3f9dbe68466caa3567f3b7cd08cd9456a260d10536fcd30e0d1053eece77212279e0b5bbac5431bff5a3f700656986241ffe1c220195a3a22bf1f1c81aab8b42c42c7b42eac92b10b1ed0bab2493f07bff76804a16e3a452c42c7b42eac926ff1fffc04a067034ad159f0050b705619a442f4744983a4bdff48802418e01a45a9133ef1a3217404a03aff302b8639553b4332d85a150869b7fffc0ce6940c301a3a8b133ae7a3217044a87027043823842cc0f16d17c16fc20a201768b04f04ac14517433cacfc8606810b33a181c7c1554b348c5420d845b0a42ef2872644a446c4a948647242147d4a813eaef0b28c488c49c47b1370ffa8513686daeb90b22e25a28508c06d07fc7b218c1a0adab1a96aab65a66b6850b917717f68964667e62963d61946011c6d367369715717941a11fad621b1671662c344d16533820330a6bc160a4f17e33b0cb30169333917a1784201718f520b2af17d8828fa3320df3314c217b0de18011616e2514526ae03b6a26f86d210d20a2d32900a000da7311446111b87510690590686504808a00852885455856bc48c5114844284c182c2b4b715dc05c0e93485b80087b82126b8042eba9d08d69dc8d16911311272d27e62e04e1091470200111642d51532fd4d045c10c8b316344843b4404658cb6202fc8a4c7247c4624310c644bc6c2452228aa41f8944686180c8a9511e46e8801202da61b0e81212812c03020e111911811daaf2a1aa1abc2360b041b0cd64a2fb0c9a1b81a82c4f44f30e941d8091174f18400400650542a283f11143f0e244c0dd110c15c47c63c62c7d22d0b8a7aa6b0e3aae01b10f4806c31000800c40918c10ca8514948a3c1e42f82f46d0b70a7a88c5f45f46343ac5b2962ab2012952b181d84d0ce60243c4352882d78660b4a930e703040760b8184d149f86e83c49e0278480e502b0b5441c220790e405506a267a670b6a4a06606e25324a4660188ac0c7075081841a22c1f0a5400209a8909aa7e2c50822ad4a00ba22540da188610a6c3a0bb23d060a8709b22600700f01a09081087f08e427c2342241c20661a84ea3244ec0701600c00500e830c1107605607120209923282262663604d625074098a1a297061423c64c41842417077a0f084860a0206f40f078847212a33a5a62d03c035273052070451c4cc3fa5083541805720f092207a36a46229250a53633612a3da030098280)) else (if j<4 then 0x7219fe1f007f080bb477f7fde5f082840286acbd5dce06080e38068a9006ff8ec55d8e204021aa81efe4f03bea90c0cd1e4049c685f80139fd76148a7a7fff240b56da0601f752017238dfd5ff86e9594189335c80bc8e43fc1ab202c9804071a9ead39ed40d59e2f47c49415555401cea5193f01ac183187dff14f3f1208092b7be9789ea9044e96efe1f0d210420080a2b7fc53cfc482024abff7ef01110155f9fe6022022adff500104a0937e660444a527fff30111294abfe3f6b788100405129ffff56bcf410103356feff3ea090440954f87bffa935220802108b47fdffd328c88820089e2c001ee87f43080085a8dec79627c482a24c164fee37c4384010b4507ffeff3100440442d4f71bcaf3069881020022aabf51fd20f30200822248fd6dbea084040045153efff37fbfe7510410054317afe9e847ffc10941040115c617ffefc7483a2202026bc7ffffe410a046882100405180f7ecf378048fba414310802248ff7fff1f1ee43848b384011446821f829e087ae9fb024041220084991dff50010446927fe7ef01111955f99811099497ffa364400010109b61fffcc0444653bfea00208152771f15d4004110265f9981112949fffcc0444a535ffb2742000202526b4bffbc134904004004475487ff292b8208008008e6a814f07800057fc42000020088e3ef8ff9c4446525fffff42364601010bb6025e2f0005fe4a00000802378e00affff3a100010111b673a3c13cd4c370633115deb0f5805b76e686d4025fc8b72f56e49aa1deafeb30e01465b66522309ffb43533e404641b2117e7f0a0449742b0caa15f97b435738a06b3c4c3f97a3f550879f0520d608ccfe7e6f346264ad277382cafdd484832427aa77eef02bfc9dc6410c6e2dc67054414dbb9dc83893391e8905567e695087245d4d45df99d401de8fa8749bb59cee42c613fa93ad1f209128b11404dff010629a369dde8f93f88806568622660858f617754963e4d64b5d27aa68dea5dff2d5fc7f012819c0d43460f10b1f449b02483fe0671172180d20454bff35e2570dd3b41314affff1f03058d2b4c0685a3002ffe7eff12ada1da688a01116fcdf9099c6d458a5bd8f7d6292e9a6000000000037e6fc7cd93cb508e37bb4626830e7f08d678b33e17a1ce6948a637e4f050dc70030c1aa759011a26c8d27afcbd020113e9266b6ffaf00f6c32f66afd20ca005b800009d0dee164e4c901ea89fe6fa7a84184001c4811fe36d9e51b89009016b1baffe546200af20212240aff5f013a6036d2e32024a37dfc0e8093652d81900e518015ebfe014b403b43da001b7eb8018fe14c42e342901946857ff847ff0f000cc00b0000e877f6c20026ee0023ffc44007bcc5e835520328f0be078358f2008a9f9f003f4e3671001889b7ece800904007100ff2cce0620802489 else (if j<5 then 0xe20022f3725ec44a491013ff8000020df1000ae2013e6d025ec44e59500006ffe00005aa749ad2c1e1495ce0858006db409c4e00000000000016ffc0001be28725d2f07a5c0aeb42519c000000000cffe9c10821e9a6a002ad9cae43c426539bdbe77b330a506c67aa42aa0000000008fffeead9ed349b273335010729cffa33ca2e6212ca07cc519cffa73c1c86212ca46cc7198ffffc5f0fb218842098c9acf51d27ff8189810c10140136aa00000b7d5fb29d102264fe00000017e62950c2a4000025f77eca744089dbf4f499e7314a9e54025f669c3fa8c4a74248a034fcbf36fb94308a5484ab000024fe47c2a90e9951060805157d9e241f0a5a3594760e00135937f97b380a534304024aab1fca4dccb24221840594628df013fcb2e529015338808c8f000000015ff27d5f67e836971013120afabdb420d64ce2026a2dcfa0ccafbd880274fd849b39ff1daa01d5ac936efc563b5404bb59adb6578a0000718024fb44580019c687e9fa452105b8c804de270807964414fffe53766eecef60e100711ba7fe909d46191012d4161fc553d9180046a6fc2bc7230173449ff0675d992274d0f9199be9e008340c4202523a5ffba91488c9c9a29a8a2d0f014fe8e7183334e0fffe68fc550aded0120120316381fcf1db20852d2d81901a51c000000c7fad825319100804c56957ce7f00a5a01da1ef2002380006ffcdb100c80328906bf0f164b89ef744280a88d0fd3a7ff00122440596b57f8b92782b95f8420ce2027a3d9ff0ffc410000c800280000781ef641000acb33fd5fc7c35654b0354b31462401248e3ff7370e551c6c189009c68008ffc6bedeb103120009013ee090008ca2be0b6001bd802837712a4004478000b7fff8035053055f8d500b71e003bff1e4c78f0201320012005196cdb3812acc0016fe087bf2eec13f1e6403cc771e4f38d02c647c02bd483dfc1e00640d5c582015e331fc80fffa45b3b590582025e340017c1cdea8b67707080658d03ae376c62ba11115c4019eb3adfd376c934e0bb7d80b36ed7f07dd77d00ab36bea2100d28e05bffc001228ecddd9c0e49201d1214f039a593189f3680414602da3a7a59333e6954800a4683de0fa1936dcfe20009179fa53a36be41600d9adeffd6f22e9c2007aa0000029fc1af03be4f30b2cd05d4780065d085f690cc98007aa97ffcc2ceca818e01a450bf0b3b2a8238069131ffffccefcd58327022b6774c74dd8327023b5cbff91aa80c012080378b87ff77f1120181812080038d2ffbf8cadd709c068d55fdffead81832703cb5e3fdbc12ffdf6e954241006d1b9763e34be80b8030e00eaac02ff87901e00001ff7088401247175cb8e0a0c19d0806edce07fff571047180c720809d8e67ffa044aa08e0324487e5f28640018f82a5ac14f03b013dfd43c954241000 else 0x61ffafe309544aa400000000000000000000000000000000000000000003ba27dcbf2c2100ecd4000000000000006fff79d6f98b308010458000000000dfffc9278bff8248110248018d0500699300000000000047f18006f655b6d759388e07d483aef17f42580a3c86041d200823c1e0e02a76ec09254829233dffffb7aaca4b0328e0d39c42001e411ffffc50979cea0c08e1ccc4202d643de2843078e0a644021196406f9093b6c96570590e00000000000000005ffe0355a7e307eab1f1a1004200134a001bffedab106a0068800000000000000000000000000effff3e39c0fcee1378089150112e400000000000000000000000000000000000000000000000000000000000023fff8386267fe8f101204a0105c80000000000000000000000000000000000000000001bffb75fe32842460c00004010912200000000000000000000000000001dffc5efed5880efde6f800a5c98000147fcc0c2040c696a2e8a3ae013ff814007a582d35a583c217b36001c69040d30000010f880c)))
def rT (j : Nat) : Nat := (if j<2 then (if j<1 then 0x4cc2da88830172831e002d02b281d3822485b0ad35c11a443bc1bfc2fa80de2ec2c2c98298826ceabb815c024ccc4e88e80d2582b9083602635225c116851d01b41c4d0577c05ec2a199d0014381e95c4fddfa8176a608831c82f8057841ff805a0122429d08f00160c2c0400bc4e390f742ef8016c1860729c19dc01ac0ce801800a0c266810c8333914e99fac03e42b61da642e1c86a992e402ec11fd1af413ec2c6c86f00f4031f412f429300000000821d001c826f0000d9e881ac10ee8d94c934a9030000000000008076000042c39e690000c09842614180d1ff0000000049940000ae81df0601e600004232000081a9c2010950821300ae424e919741bc1170000081ad902bc274c30142f409f00000c147020e2532813a0000010e91a48316000059dd403b81a1c1dd40f01804d1f0ae9592160d93c107018a81c8009dc03100004abb0090504ec50b4008c59b9db9812e0b25086c1a1a00051a5d5048000000ebc17321e8850140ed9f2b8525c0d1c899904a4d0981a6806841460000c26742f240d400008086051511710841915300000000c1a59c3300000325000000110000c2dfea0caaea66c142f642530000000042ee84fc893b00b3408ec1330000c896428801528ebbd0ea000000006e1300005172cd372226401400001038494825f800000000492504e1000042e0000000004538461b0300c0f71918031500b601de02cd52e4414e5f0f00c341054132c1b2d0605cd784d3c280d9300230803801c91e4a00000000015400c8000002dba305921f017f0a00405282d5d0500000ae8c9100c11182e2000002fd0037c2fe480dc135000000d808fd130b0000c81ecde3c007d02d826800008089804f00004637427d00a7c318c16781af000000000000c0e0019a863a42dec0bbc144c24f405b00004907526d52c3823c2e0609002302010a881c054a2502014110031026012e0b453e277704033e0011803e0700020910004f1c273a16170f6b0100090104001d1b0b0c122305130020012e1b0812000a1001035c4d0d070e0013043b032e1e200739100200000800051a3147000e0b2501000101020105000803112300100a02052202100217241a0f00090918000102004600001808186a056e353a250c1522074300030014031412190200280005101708000f080220001e43090a1e0e1a090a0f1006013f0601000b10390e3f00091e06190102061303002307000507002a0f09000b03010a1d0b0d60090004090520300e1e170c670409030b141707030b01261c000d2a061103310507020504101a0d0f040300380b010d02061318130103040505050e18050300170a00190806130d0829041a4e01010009063e0219220038001e0b03002d010515022001010500010400240302110500010c000702021d13000a051503021606 else 0x2cc126000002144071016c400ec00681484271102c125f828a82e68e054206c01580e3a250c312c27a8211088c00000000d83ac191dd0292ca4187e6c69985c32cc292972599389ef19c5c61e2000080f8c2a9846642eb0000a8fb023610f4486e827fc222000081f7d1bc1e7f8681ca020000c2c1427840b881c69980818b85ac41b3c1fb0f311e494219010d91914083810411b18294d042000000001839822100f5032640652d3c55041f26404a0de49223d98742ca000000c60000000092604ac20000a9441da76e4d00009986126c88975e6d000080e8000081ee00000000000000009efcc2814209480c411900006437426bef30000000000000c2d482570000000010f5d220000024ec1e7b42cba1e581cf0000c171c1f16e940000c192c25c8225c18d00000000c269584c0054830b000001490000830449b0c2834d284072405602d96d45e1d92d4d002741258323d5050073418f01c3c311c1fe80e202628168e10ba662000082e55a8140ee0000c03dca0102318d3bc1b8dd8dd2c200e982169ecb923901d622c28151000042aa4075294c02f0c60a0000c19f01f90725c2d682aec0db9f0e82b8c25b01c7813dd30f41e50000c1ed91a9c02a0000091395b08123c6094a9f0000000000000010000010cdc1cc00008cfc000005ae113b5928c0ecc1415ac2815390f626f300da48fc919d0000000080cc018907050000016f10c0ed339e7dc20a000000000000920901c00000000009270000429bca26401385c081ca50c700000000000082b700000000404100000000000051eb00002ac282ac0303000082720000c0340000c23400008ae3c04702730242000000d38917011852c8acf39ec6dec98170523a51b4030640fc83070000c1b041900000000042d7c85f0000429c998800000000000080b0424b0000024dda7a00000000809fc0ddc30800004a9c4202031452c481f0028b80b7e2a00000c0794208006cd16e9b05c1360000809201d5000029455e62e6c200006d2f41b6531712810000dd7b0000df1200001db0402200008d1c1ec8c10f1f08419c80e4000080590000009a40330000000000005ef60000814fdd7a813f82ea832702f30a855ef00000954bc30dc4e2407e828541a351a882e48036c06100000000000002ecc1280000e669c17b9da10000c09b021fc91bc032c1888243083c030c02a300008195416ad2c5c1fcd6a0a665032e49100000401f6dfa099201da00002f2e410900000000c2569d1a422d82b1c12d41210000021b00004181c30e00004094491a0137c1abc082d22251a00a4a0254c0b4027b021744d640f6c91ce85000b24d92dda98028c060c302d0bec28caebbc11d624a82a02d34008b00000320029e81650159c15f42a81b27c2b4c1d7844b41124062eaa5c24783175c35018c28ed6affc1) else (if j<3 then 0x40d2024985a1e2a148ea000081010023000041d8000001ce010000000000c3210000a6810000431d000082be020f5063a470000051991e08c26e0a6a40f342a681e340b5005f0265dcff41a7454b41e4c25f02288070881002ed4296c8148e48010643316d9bc14b4332889080fa80660134411c0244c8ecc27c44e002e7de7e80f282b3da7958cec83bc00a4cf7c0b152bb415bdacc00000000c087d97f803a11ae000000000000000059e2000066f0c2dd000011f9000002d80045000000fd80dfc01d80e700009ec2dc315d22d4fbe9b5c1b7000080cb99e50000014a0000088542904919d9dc02ff40bf0237022680968003ddc681db01a400000124403f0000402540bc0329400900000000018380350000c0c180fb00000000000010c80000c17e0000644fc0c081e8992fc06d00008019c1ef000081a201970000c0cd4812d50681df81bd513c829a817901b5401b486d00001d1800009d1c8115008000000000c83700000dfa822e82c7d19bd1a501c200005315000086e581f2819e000049b5e95100004309000c00005eca00000000c5c780cae94d11760000812a80a5820b832b8002c2230000c026c92919d81e6300e61d7cc1f8c8792117008101ecc88942339114ed2d01a80461c21e423e8064c20500001dcc8313402f000042c512f089440088800d0000a902022bc21cdae5821000004284000099a102158299000000000000000000e10000000081aa00000000000040f9cd3c00000030c2f5cd8bc039416b00002e911afe009e190b5de300914e81017c82c242cf00008c3b02480097c451521d431a82708204116bc16411be8220422c804349909ef95236c1eb828704e4425980c545ca0000422ac00f1e6500000000c255ddf8451f84679d88ca81464f807a02cc853702dc5681c32ac2f11dc300ea0000402b00000000000041a000005f0700001231423d91b3e1dd80c4420c000082290000e138c1829196c2ce4663c2bc000001c400006e8dd319d2265036c218030f8aa68108c1408156d3098142a66dd2bf01e2c0a882b58166c1174150c1ae1d51c139051b1dfe424a457902951d1b00000000413180d980d749e400f1828fc5c2c10a4103893cc94a815e4085521e01d98d29806f00004816432d80c745ccc8844069c264c10202bb41d0104dc238000002fb1ec1c90848e90000031b026d990c808a425a614500004638c68300460000c1750000019900008162e18600004004487c000042910000000040530c02c1f6e6cb40a90d8f11b90000c80ac5099f11472a817dc07712c60260c02980b940930057c80f4a4bc11e01fa5989c5864938e663c80b4130c15a422f00cfc08c0000c03cc196518cc04c827e40abc02442768a5596c2c2770000029f1aa046c240bdc12700000000420351c002a240fe8811c08f89 else 0x11a100afc23a000082ab9a1be29f0169621b4145428602d200000000821200a4d856c0ba12630000000000be426ac32f0000917481f401cb42af806a00000000000042fc0000e03901dc22e212e902ad40dc561b105f86e0ee930000c1140000881d025d41e181fd01bb81f3000040ad59d7829740c2d2f110ec46cd8ec205f30000c528000000001efa65fa428901130000020d516c91ba5e0700004310d1f8d8540809523880d00000c15d00000000e666ee909cd240a60048000059834178006302a48058c04dc2c8d18311925224000048399325ddc94319c1579da3de814044018ed30ac049023b407dde7c0000992742d0c30a0000c06bd2bd417a92c00000425e00000000408d81850000823f00005cd48240e990c07fc1b9c0ac81e0df1005fa000040d541c541bed97e00008817c2ba891d0406009c8818e1e6819840504055880e80a3819ba2814227016d0000aa2611fa00004279aa4a416e0000000024ff000080e5c252000090f38db045ad624906cc41d20158000002c4419300008095000010370000001ec20029b685c8d19e823542bfa1845262493a00000000c12bed4cdef28250c2821d25404b5ef348f7025841775ec7051742a7451e813b813802468239c11b1233e04c10f082a5092b866ee51a6e8f10495cdbc1b1d22dc021d98450f225a141948275c2f982e900748110c12990c30000c06702e381554120c099000049490084c91f421a41e7c12cdde940c94d8d82e84078d84d402083229e66024151c541741e2ec0ff82d1d9d5006e00002a810012818483300000926aed2ec52095ad014de6fcd2fc4c610f25807c00a29230000081c182b00a6340d681cd40a141f541ba0000d1ab0000c20700001234eec7c245000002d30000ae8800008328d86082f71eef000000000000c07b00000000c28d000042bdc1d1864800005da8000080aac02c9cdcdee4800101d4c10bc1ea000000004947805c000086a012f7000081612dbe83248042887300ef80400000428e904f192c004e005dc1634251000000008702c0515c34413c455a8305001700))
def rN (j : Nat) : Nat := (if j<1 then 0x99ff8fe7880a0e00018eec0cbbe6603945800007e0761dd4180851602fac46c0a44f8e2d41b00a483df013c0af006010662c3e1f5a5adc83308350ff9f0b1f8d1000804bea0ce0e7e965500318662b3feffe92f8480004004badc007bff2b4900108c51165e1ffe7881054a5d7ff1cdf102095cb80000392ada6fa910000bc82e3a85d04e2400f00b0c2007190c4805fa49a23320605120073c12905ef828ac56787c001b824009295d200ea1b900000000000bfc00001bfcf3d7bc035b9ffffe000000005e1557d71a0060baa96800000000005fe00000dfe79ebde01ad80000000000007dbfb7fc09be1bbc06a3301887aff5a413aa80182181f5bc0004e06d602c2e6fc00d5377af1541e980d4400beb11b02913e38b506c02933e38b11b1a91045f04f5b40b10536d91f0ca7cc0aa980a51b1be194f981553014a36027f3506f64d602936cefff8f4800562012a358f5fe00e16604a8960001f002f846b5b40b104d538817c33f00fde620122b6463d241140243691ff98016604a894bfc01c2cc09512a54cbf97d2a0a094017036840b2314912c998a52d0588978ff26a4b8b987052c80555a9503aac41505255cb5841a874c884d01aaf5423d549abc16101c86a0a5a6a8939a8b410a5c608ca0ea2785a8ac20b17211c5186110a20c2881810817c1685e05d0f93f1fc0981982e0241e81680b9f33de610f29dc3e8078180384c09312425449c92acf9391ec6348d05886104c1a580a21190610202cc6c06c1522703e01f0be218390be0fa1885f8a80962345a01a14613020c4c07e144550d41a02523e08e8c696a05c0610103c1b890015016070d98fb21a392bd50a99d4e85b0620e8318000081ec10a894fc940370230c10621f82203c11e3241c105026360b24f49ae312460cc1381407f83d05e2fa2282a2303442282294d0d4080ca22a2da3640507c1e22949f86e0ec0d01108436a2e40e1341aa4540c82c0683b05704e18a0fc409291e801874866080300901500a81142489919a2d81410013a1444b00e0100e02d00602005019002b9f587a75d14a771327944c7ee36f15b88843861230628143f19eecf1974f3891b34d6167d31dd858bf65d2ad4d64aaf155029654069b84ada42d19688c425a010f7a7773969b04c845bc29e937094444c1f90ed470e3531918b5c5182410fb06a42ce10105881d80760009663cb2fe584f2b9f95c7cae1e542f2a0f9646cb036491b2cc496524b27259192c2496064b01257492b9c95c24aa7254392a0c94c64a6124989249c964dcb24e58372c139601caa4e5507299394c1ca40e58152c09954ccb0425520acbf6597b2c9d963eea0e56622b29217090984564dab24e1206ac8a5660ab2655912ac9856480b2c819704ca0364c23243ffffefdfefeffdfbbef7bedfd7f581404c1204403008010 else 0x25fe2067259934a6b1ccffb7406a1e14a4f13bfffff9ff85c09f851030b02684d0060b0726ba37ffffc2fbf9c6df106850640b0b901f81125d004fffffa81fe04c2cc7da27100b9c86f8d6574003ff64f4a800270048252a141005d05e4f43ffffc4ffc2e04fe0a2068989a1340182c13f2f8077fc0be9f0048400a0926e000600822cf2003b043cd207231120f800066015b0d520722f1a00000001bf819fcca2425f35fe1423eef53135440180e0b7a8c5e16bfc03472f5cb20b170cda37fcfc21a1242880301c00f54b7cbb71810137a401a8b4ffffff60cd040010000436a7fff1f6d01241398a00018218014750ffff800006401a50028151b60039d0002bfc33e70094ab048205212602008d79c7c02c541810438037ffffe4411300060860c27000efff6f4e041204c02680006008018eeeff1c8da185c800822)
def rU (j : Nat) : Nat := (if j<2 then (if j<1 then 0x8ae000001c40000000516800000000000000000000000000d8ea0001041a14ad94ba2f9110b467000184ac0000000d05054a506a80fa000180fc000204c49b7085c00042fcc1fe00030ae80000000000000054eba9e1317f16b00000001833e0a08000012a0000000000000000000000771488e40000000207400000000000000002fc047800070e6000001380000000000182480000000000000000000a5e00011186b3380000000000000000000000000000000000000000307e80000001525c0000000000000000000000000184b400000008150000000009538c4e232000000000000d55126300000000000000000000000000344600000000857d039c2b444c4000000060e4000131bc05680000000028000000008163817000000000000000103d40140001022400061240000000000000001166000000000000000000000000000000000070a800081fc232757300000000000000000002dfe000145e0000000000000006099c0cda2c874b80000001335400000000000000000000000000000095730720000000000000000001b4bf1868000e9f59a520148000401c04040000000000182060108000511c000000000000000810000000000000000000100001a660000000000000000001498c046d26600000006f70000000000000000109c000242d4f40c80400030a00000ca3600000000000985f051c0000000000000000000000000104c80000000000103300000000c1105be8000692a00000000000000082ac0000000408a00000000000000000000000000494e000000000000000000000000000000000000000000000000104f00000000000082d4000000000010600000606c000000020218148000005f000000000000b28400000000000000000000000000000004b00000000a19c00060d2000000000b00000000015f00000000c1be000000000000000000000000000001830800060390000000005a010ac15e000000000006e0e0000000011984da808c04d00000001005400000000000000000000000000000000000004091844c45680000001056c0000000000002c120d914b01900419a3d00008006025f21f4f714d68000005480000000000328880000000000000026310000bcdc00000000000bbb80000409124f8b0a00900000000000027c410000019c0d0550000000012c713a8959000034c745d80000000000000000000000392815b80000000000107a207708da908400040900460000303b00000000bd100000000d1a112a800000002d2880f4000600d34004122460351060000227330202013212740045132070000005072a301113130020210b81043010000000c000016100010064028024520010120056011014402310003150401010300103010012031250001300100100201006000220001001100210 else 0x200030ac0000516a5be3699000000008a3c00000000000000002a000000000002022c2e30000048400060a1000024a007c00009174000000000009d48000000000000000000000000000000000000008990000000000000000000b9744310000c2c2000000000004d48000233766b2000094140840000d9d1896646880f60000000341480005eb000024798000000000030a8e0dd0000000006c80000001807b419600c000083012a9e09b000000000000000ad3000000000000000000000000b0a0000256c00000000000000000060cd00000000000000000000000000208542d000016b80000c8dc000000000d60001102c000217b000082939a00000000084dc00000000000b3fc000000000000000000202f822a29d70b50000000000023498000022c000365e40056ae20d2c0000000000000024330000000003a66b68000000084da22d800002ed004c0000000c296000000000ea000000000000000106c09ac0000000e1e4000000041140000a26000001460000000000060172682000000000000000000300fc07d00000000000217ac8de00200000939407c000000060500001821d03cc11f000184cc000000002a000000000000009382ac00000000000000130d00005864000000e0000000120b805fe92300000001b15c14d00ac000000000004254000000016ec0001b1b800028970000000000051350000000102ee6f8c9e60000000609800000000000493a00012ce40006267000000030aba1281ca80000007800000000000000000000000002495800000000000000000000000000000000000000000000000000000000000685b00000000000000000000000000415381f7225400000000001bab80006b560001017800000000000829c0000000c29200000000000000139b000000000001db85002000042c6000000040a20000000119300000001cd10000245dd2ae000207be03000012b08759800000000000171000000012c340000000c25e840a0988e7b81580515a8c0000594483c800020e0000110fc00061674246000000000bd000000000000000594680a800000000000000000002b6000000000000000000081840000000004800010a78000000184b80000000d26f88b4000000000000000000000048c44baa086e03400000000062000000000001235000000000002697000000000000000000000000000000000040e4000000028bf000139aa00304790221a51055e0000407501fc0002084821c00000000000a8f0a88518500000000000001b000002980000000000000000000897e13000010412048cf420000d1b00006107822e45fa02b800000018298000610f0000000000000000000000218180000000011c06e2d350000000046580000001142eb397671000000000000000aa2925a000000000000000344e) else (if j<3 then 0x41d00000184b66e000000000000000000000000000000829c839e169800042da000201ac0b6000182380000000c61732da469349800000000000007c81ae00000000000ddda00000000000000000020b880000000000000000000000000000000000000000000020c700000000000000092c684600000000c1dc02c900500000000a04400000000000000323c0000000000000000000000000000004c700001ad2c0004152416e80880000000add200020380000c05c00000000000ccca000000000db00000000000000000000000000296c0000000102f800000000001221e0ce000181a811944fe00018129a89a064de30000041d00000000000000000650000000000000008a0e0000000000080d200036390000000000000948000000182e00000000000000020000000000180760ba0000000000000002ac1017c81f843f800000000000000286881f8000000060820000000000000180000000103a800000000001068e0bba1ca05700000000ae2a000000000000000000000022f800000000000211a00000000000000008003a8000000000000000000060d381dea5240000000000000000000000000000020b340372a8e0000000703c000000000000000d93d8183049b2b300000001052800088bc000229c800000013bca0310000614a000123649240001022c00000005d200327abf8000028400000004cfe20ea00030bbe89400000000000667400000002779804180b6000000020f1d28301e0a94095d5277c1df09a80b3000000000000000000083980000000000000000002f0b88ca000201d80000000000376be22ed10c000001980000001806d02a800000000000000294581c70278000000044d8000323180008948000000000000001d2990aa0051c0b00000000000098a9cbcc000000000000003634f6b90000814c0006962000183b220400000000000244deeaf00010059089530f86040000000000000000000031e03841b40000000000002bc000000000002ae00000000000000003ac20c0a08f00010564000600b0000000000000008146000000060eb82d680ad0b60000d5520000000606b000000010aaa0d000000003046000000000000000000000000000000044000000003a5ce493013a13d485ac06700000000000000094ce0000000000000000000000000000000000000000000000001972a746000002e6b1900000000a3da0008000020a000104300000000000160e004b4238048802200000000000374aa26eddf200000000000444e00024b58000000000020618000000005cc494c16e000000024b4f45d00000002649202540a424f0000029f81b050a59708000004f04e2418800000000000000000000000000000295480da00000002960c0b2000228528330000db7c000000042c800000000000827 else 0x544a7a0967a00d00000000000048b4049aa4dc81b266f832a755e4975a6891a603de0f30000000205d0000007800000006b0984ca937c08d8000c23a000172dc12082c485110bc0000d135004146a00009caa0ad712e422f02180000000000000b400000006020000090400000000000000018bf800000000001b8900000000000270c800000000000000000000008064000000000000003037a17f009a000202100000001842c00010e40000c96c0000032c11a000109d250600000000000000000000000b1f42724ae000020848000000083d449700000a5013ec1a6f63a000000000000080000103b40000000c27a0000000000000009029a3b80000000000309a000000000000000000000005ca4000000000000000000016f455284440000000000000033830000000005c80000000000000034268000c94c0001777ad7c000000010960672815c5bac00000009a96000000020c10000a07a443d02e0001a501018895100004a54770000042fa00030780000413800000000000000185c00000000418a0000000413f000000000000000024fa24c07c8000119b23c7274a8a98528000000000000000000067c402880dc00b40000000c85785e4000166f82cb849400000001dc48cb400000000000000104a440c0001c38f200a56d48e2809811e00000000a2e40000000000000000000ee4000085680004f6d000132500000000000000000000000409e000000000000000000000000000000827f003800041c5a33c0000000000000000000000000000000000000000180b000000002ada000000000000000000000040094ae391f800036770001a0c00000000c1ca00020658223000000000000000000105a4000000000012b4c00008f700000000000000041a92d3400005180000000106300004034000000000000000000079400000001838769c00000000000000000000000000209f6cbb000000010ba800009c000000000000d1e0000339300000000253f49e8103c28600014468000000083780000000000000000000000c022000105e0d80000184ec00))
def rO (j : Nat) : Nat := 0x7ffffe000017e010944e400000002fff97991d6494e800fff0000bf2a0c06404fe000b950499fc055100a38000fe26242400007ff2f09a1617fe00190c05617fe060020549117a2510a3384a4e9fc361524e0fa3e03e2f90c3917e5f1502d8f646c410d9f27b984791dc0c01203002050200401a01860138764508e288c86a0501f82c0f0261d0c613066170243d028168d6760620381e0d03a02096070421100a200a83101600004060900a823d1bacb1eeca4d18860005916050130481100c020043ff
def rV (j : Nat) : Nat := 0xd07800000000010b16ef035b8d00060d400000041c0000000000000000000100a00000000000000000000000000000247b7329af1074e2801b30d892800173a92a812c0b102511f000a24021bab101200006500000000001016000000002201800088e6a840008155ca08d000081c24b80024100000000002054000447800000000000000000000000000000000c3d456800107600000060f4000000000000204200048c2287204000000289800010be8a000000000000000000000000000e38000000000000300c2320000000000000c02800000000000060d20238200000000000000013800000000000480000000000000000000a1c0cb9688000000c19c4741080008018000a3000040200000000020000248000a2900060fc00000001f0000000000000401c000000e990cac65c000811808800000040c80000019054908003750000000000145c00000020c00000000000000536000516e8a80000000098003078000c8d000203a0000000002456000000000063b836000000000000000000000000000001058000000914000000000000000000000000000000000000c5cc274000bb9000000000000000020c5114000000000000000000000000000004830000000000000000000002600000000000005080ce400000069160ca1363b7017000102f039000645346000001480006151a0650000016e1010000001050000000206c0000144076040b30037c07c0022620000000000001bab88000af05a0000002cdc000000000000000012200042a315e000105800208308e0000000000000000406000000002060e80000000004c380000006c860bc24800008d8003534000000103503d10cc0b000000000091a80000000000000000000000000000000000000062e000088d000244800181f00c600880508000114000100510020081c0084222500080020
def rP (j : Nat) : Nat := 0x403103b437ff
def rW (j : Nat) : Nat := 0x3040022200000000000004200000000000006700107c08000000000000000000020500000000008cc000000000000951970000095f06002310000000000000005c40000000000000d000000000000000145000000000084c00000000000061c0000000000000000000000000000000000127000000000000000001140000000000000000037300000000004dc0000000894000000000000000000000000000000000000000090000000000000110000000000000000000000000000000000000000000000c44000000000024000000000000000edc000000085c0000000000000000000293000000000054000000000000000000d1c000000000318000005dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000e980000000000000000000000000000000000000003a70000000000000000000000000000000000000000000001c03000000000000024600000000000000000000c0c000000000000000000000000000000000000000000000000017400000000000012100253000000000000000001860000000000000000035100000000000000000000c04000000000000003080000000000000000000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000366000000000000000400
def rY : Nat → af
  | 9 => (7,6,9,393221,51,6,4096,rQ)
  | 10 => (182,5,9,5963854,119,11,4144,rK)
  | 11 => (820,4,9,5898424,120,14,4465,rL)
  | 12 => (386,3,9,1769521,86,15,4664,rM)
  | 13 => (66,2,9,655368,67,13,4360,rN)
  | 14 => (9,1,9,65537,0,9,4180,rO)
  | 15 => (1,0,9,65537,0,0,4099,rP)
  | _ => bS
def rX : Nat → Nat → Option (Nat × Nat)
  | 10 => cM 3 61 1 8 3 3 rR
  | 11 => cM 65 977 3 14 8 4 rS
  | 12 => cM 353 1741 8 16 10 4 rT
  | 13 => cM 199 1993 4 15 9 4 rU
  | 14 => cM 40 409 5 13 7 4 rV
  | 15 => cM 12 431 1 10 4 4 rW
  | _ => fun _ => none
def mo : Forest := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,rY,rX⟩
def sgY : Array (ae × ae) := #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]
def sgC : List bw := [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def sgA := moA
def tX (j : Nat) : Nat := 0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910
def tY (j : Nat) : Nat := 0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110
def t4 (j : Nat) : Nat := 0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000
def tS (j : Nat) : Nat := (if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))
def tZ (j : Nat) : Nat := 0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916
def tT (j : Nat) : Nat := (if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))
def t0 (j : Nat) : Nat := (if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)
def tU (j : Nat) : Nat := 0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def t1 (j : Nat) : Nat := 0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c
def tV (j : Nat) : Nat := 0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff
def t2 (j : Nat) : Nat := 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def tW (j : Nat) : Nat := 0x10090e08185081808013ff
def t3 (j : Nat) : Nat := 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def t6 : Nat → af
  | 8 => (6,6,7,327686,51,6,4097,tX)
  | 9 => (69,5,7,2818098,102,10,4151,tY)
  | 10 => (373,4,7,4849791,119,14,4299,tS)
  | 11 => (216,3,7,1769495,85,14,4244,tT)
  | 12 => (30,2,7,327683,50,11,4144,tU)
  | 13 => (3,1,7,65537,0,6,4109,tV)
  | 14 => (1,0,7,65537,0,0,4105,tW)
  | _ => bS
def t5 : Nat → Nat → Option (Nat × Nat)
  | 9 => cM 1 113 0 8 3 3 t4
  | 10 => cM 26 127 7 13 7 4 tZ
  | 11 => cM 159 691 9 15 9 4 t0
  | 12 => cM 102 467 8 14 8 4 t1
  | 13 => cM 16 163 4 11 5 4 t2
  | 14 => cM 3 59 0 8 2 4 t3
  | _ => fun _ => none
def sg : Forest := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,t6,t5⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r7 : aJ mo (aD pri) = true := by
  simp only [aJ, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=6) ?_⟩,aQ (d:=3) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uq : aJ sg (aD hM) = true := by
  simp only [aJ, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aQ (d:=6) ?_⟩,aQ (d:=3) ?_⟩
  all_goals simp only [bB]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pS : Z mo 9 0 6 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x7b44819a306751009a5093b784047230032800865a200437000b64002b510562020ba8451937002508043b60092163274655) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pU : Z mo 9 6 1 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x31401265) rfl
  decide +kernel
theorem hb9 : Z mo 9 0 7 := (@X mo 9 0 6 1 pS pU)
set_option maxHeartbeats 0 in
theorem os : Z mo 10 0 5 := by
  apply aM
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem oy : Z mo 10 5 67 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x20159475300532700250885a2900592600801264a1300803700b6245194200471000253885a2900593600801264a130040870080359a7b6804235006308b089650630700801264a1300402700628b1807a20016800ba84519470050210020169475300894000201694753006540002016947530059400020159475300754000201a9475300754000b8262631a003261002018b4a5300743000201a94753006940002015947530075400060b214263002130002015947530075400020159475300754000801264a1300201600801264a13003917002018b4a13004716002018b4a13004716002018b4a1300471600601bb48230048160032844b36a001547002018b4a1300471600801264a1300271600801264ab32027160020159475300654000201594753007540002015947530064300060141426300193000601414263002140002015947530075400060141426300192000201594753007540002015947530075400020159475300684000201a947530069400060121426300713000801264a13004130006b02152690021400020159475300754000201a947530058300020159475300643000201594753006430006012142630091200008257691a0068510008257691a0068510060121426300813000801264a130041300008257691a0067510008214635a0030410065121426300713000851264a130041300006214135200307100801264a1300413000601214263007130002051374291082570008214635a1080310060121426300712000801264a130031200) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oz : Z mo 10 72 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oA : Z mo 10 73 13 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x32800865a20054800832008a602042081035a27a2986016750009457592140509700850265a190050490035a27a2986015690035a27a298601564000748a2867406417000748a286740641700064b0218a00176020630bb0896506309063b4003506917682506a84b25670028070) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oB : Z mo 10 86 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oC : Z mo 10 87 11 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xba84519470047100032800865a2006580032800865a200548000638006a820024510430b81a362057160032800865a2005480032800865a20054800628b1805a20175800862008a6020420810862008a6020420810862008a602042081) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oD : Z mo 10 98 2 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem ot : Z mo 10 100 39 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x8045947b350654000810368a13b051370002844865a208063002015947530075400065021526900103900230881a5620681200b62451942004021006502152690021400065b2142630021400060121426300214000b4262037410290100201594753008540002015947530065400085709ab76804657007b8106ab90046301095b264a19004087000638006a85004681060121426300214000201594753006540000628a1862006821006014142630021400060141426300193000b68451942005021006308b089650740800b68051942005021002570945730058400025b09457300584000257094573004830000268a9867506584009a5093b78405634008351374892043620002814835a204073000268a9867506854006014142630021400060141426300214000601214263001038006a84b25a780361900ba845194700491000ba84519370036100) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem ou : Z mo 10 139 39 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x65a530108746a23284b6838365ab401003ba0473656b4010a36b4872374672326561301009365573565a30707868a29109065573314312767b4b8964654b3196891b5ba3654131968786a2108786a2218786a2218786a221929b0761565630708786a280656030966565309665653096656530967868a2918786a2218786a29114a1901053341271533412715334127113ba04725334127126b43076) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem ov : Z mo 10 178 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem ox : Z mo 10 179 3 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x76b97121426b234314a59010) rfl
  decide +kernel
theorem oq : Z mo 10 0 182 := (@X mo 10 0 87 95 (@X mo 10 0 72 15 (@X mo 10 0 5 67 os oy) (@X mo 10 72 1 14 oz (@X mo 10 73 13 1 oA oB))) (@X mo 10 87 52 43 (@X mo 10 87 11 41 oC (@X mo 10 98 2 39 oD ot)) (@X mo 10 139 39 4 ou (@X mo 10 178 1 3 ov ox))))
set_option maxHeartbeats 0 in
theorem oF : Z mo 11 0 7 := by
  apply aM
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem o1 : Z mo 11 7 96 := by
  apply aM
  apply aE (ar:=10) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem oG : Z mo 11 103 9 := by
  apply aM
  apply aE (ar:=10) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem oH : Z mo 11 112 96 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x201594753006430009102524b3100421006012142630021400060121426300214000201594753007540006018b485300854000601414263001830002015947530075400020159475300754000801264a13006140002015947530075400060141426300214000201594753007540000a814135700402100201594753007540002015947530075400020159475300754000801364a13006140000a81413570030210020159475300754000201594753007540006012142630021400060141426300214000601214263002140006014142630021400060141426300214000601414263001a30006012142630021400060121426300214000601214263002140006012142630021300060141426300213000601214263002130006012142630021300008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0040610008214635a0040610008214635a0040610008214635a0040610008214635a004061002015947530075400060b2142630021400008214635a0040610008214635a00406100851264a1300614000851264a1300614000851264a130061400008214635a1040910008214635a10409100801264a1300514000801264a1300614000801264a1300614000801264a1300514000801264a1300513000801264a1300514000801264a1300514000801264a13005140002b1035249003940002b40352490039400008214635a10905100801264a1300513000801264a1300614000801264a1300513000801264a1300614000801264a1300513000801264a1300513000801264a130051300008214635a0030510008214635a0030510008214635a0030510008214635a003051002018b4a53008540002018b4a530085400020159475300754000205137429104372002108b2a53107432002108b2a53107432002018b4a5300743000201594753007540002018b4a53008540002018b4a53007a40002018b4a5300743000201a94753007540002018b4a530074300008214635a0030510008214635a0030510008214635a0030510008214635a00305100801264a130051300020513742910326900801264a130051300008214635a1030410) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oI : Z mo 11 208 96 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x2015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000250885a2900835000250885a2900835000a502257890012490065021526900103900a50225789001a39006502152690021400065021526900214000862008a602064191065021526900214000205887a29107a6200250885a290079400060b214263002140002016947530075400020169475300643a002016947530075400025043542900324a000248a386420864300801264a1300503800801264a13005038000892a368420684300801264a130050380068b4b358420473200b8262631a003261002016947530064380020169475300754000801264a1300503800801264a1300503800801264a130050380020169475300643900801264a130050390080b264a1300503900801264a1300503900a230690a570054600082b4631a002840002015947530064390020159475300754000801264a13005039000248a386420864300801264a1300503900801264a1300403800801264a13004028002018b4a530063280018202631a002851002018b4a53006328002018b4a53006328004986852a4b016730018202631a002a51000248a3864206421002018b4a530063280018202631a002851002018b4a530063280018202631a00285100801264a130040280008200a6b50046a120801264a1300492800436b84a26306172000248a386420642100801264a1300492800801264a13004928000248a38642064210020169475300643a00201694753006438002016947530064380020159475300643900850265a1900504a00250885a2900724800862008a6020640a10862008a6020640110201594753007540002015947530075400020159475300754000201594753007540002015947530075400080159475300954000201594753009540009102524b310053200801264a13006140002015947530075400020169475300754000801364a1300614000201594753006430008015947530064300) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oJ : Z mo 11 304 94 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xa6020a827606a141035a27a2986016750080359a7b680645700250885a2900693700630bb089650630700a6020a827607a2510250885a29006937006a84b25a7804729000268a98675064530026a00279500153910a6020a8276069a4100268a9867506453000268a986750756400250885a29006937006308b08965063070080359a7b680534600a230690a57005460032800865a20087200850265a1900504800250885a2900724800850265a1900504800250885a290072480080359a7b68064570032800865a20087200850265a1900504800250885a2900724800801264a130050380086a002795801642106308b08965074080080359a7b6806457006018b489300743800628b1807a200172000892a368420573a000892a3684206843000268a9867507564005890b3984205943009a5093b78405934009a6093b78405934009a5093b78405934000892a36b4806743009230631a2401934000248a3864207943000248a386420794300648b1807a201283000892a36b4805743000896a3684206843000892a36b4806843008b403584900345000201694753007540009a5093b78404623000892a36b480573200b6245194200502100201694753007540006012142630021400060121426300214000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002018b4a530085400020159475300754000201a947530075400020159475300754000b6245194200502100201594753007540002015947530075400020159475300754000801264a130061400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a1300614000201a947530075400020159475300754000b6245194200502100801264a130061400008257691a00726100201594753007540002016947530075400020159475300754000201594753007540002018b4a53008540002018b4a530085400020159475300754000801264a1300513000801264a1300513000801264a1300513000801264a1300413000801264a13005130002015947530075400) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oK : Z mo 11 398 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oL : Z mo 11 399 1 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x268a98675064590) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oM : Z mo 11 400 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oN : Z mo 11 401 20 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x628a186200752100832008a602064091032800865a2007610018202631a0028510032800865a2007610008257691a0068510032800865a2007610032800865a20076100862008a6020640110628b1807a20197200832008a6020641a102308b1a56206a170032800865a20076100832008a60206401102308b0a562063070032800865a20076100250885a2900724800250885a2900724800a6020a827606a1410205887a290061570) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oO : Z mo 11 421 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oP : Z mo 11 422 10 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x268a986750756400a230690a57005460026a0027958016421026a00279580153a1032800865a20076900250885a290083500032800865a200769000638006a85004671032800865a20076900832008a602064191) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oQ : Z mo 11 432 3 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oR : Z mo 11 435 68 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x601414263002140006012142630021400020169475300754000601214263002140006012142630021400060121426300219000b9452637a10326100b9262637a1032610020169475300754000206887a2910837200206887a29108372006890b35842047830021069275310643200a5022578900235000201594753007540002015947530064a0002015947530075400020159475300754000601414263002140000248a38642086430060141426300214000064b0218a00238120b6040a8276083261080359a7b6807568001328a4b6530860400801364a1300503800601bb485300743800250885a29006837001328a4b6530758300801264a1300503800801264a1300503800b68151942005021008015947b3507540001328a4b65308604001328a4b65308604001368a4b65308604001328a4b6530860400801a947b3507540001328a4b65308604000268a986750867500250885a2900724a000892a368420573200250885a2900724800250885a2900724a00850265a1900504a0080b264a130050380020159475300643800850265a1900504a0032800865a20076a0032800865a20076100250885a2900724a00801264a1300503800801264a1300503800850265a1900504900850265a19005049006894b358420473200628b1807a20017200b8245693a003840008306907b650640a000248a386420753200850265a1900504a00862008a6020640a10862008a6020640110801264a1300503800850265a1900504a00250885a2900724800250885a29007248006a84b25a78049120) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oS : Z mo 11 503 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oT : Z mo 11 504 5 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x601414263002140006012142630021400020159475300754000601214263002140001628a1b620086210) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oU : Z mo 11 509 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oV : Z mo 11 510 83 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x2048b3a5420654340062ba1862007821005a80b198700562100026ba9867507865007412079541054021020b71ba576085213020159475300754000201594753007540002018b4a5300854000205887a29107a620060b214263002140002308b1a5620791200250885a290083500080b264a13006140002015947530075400060b214263002140002015947530075400060121426300214000204594753007540002054374291043720020459475300754000b62451942005021001628a1b620086210020459475300754000601214263002140004b8609b837058371065b214263002140001628a1b62008621005628a18620086210025b4945730057400025b49457300574000804a9475300754000204594753007540002015947530075400020159475300754000201594753007540006012142630021400060121426300214000b62151942005021002016947530075400065021526900215000801264a13006140002015947530075400020459475300754000201594753007540005890b398420594300ba8451947005021008015947b3007540000892a36842068430008244635a0040610008257692a007261000248a3864208643000248a3864208643000248a3b64208643009a5093b7840573400651214263002140005628a1862007621002048b4a53008540006502152690021500065b2142630021400085b264a130050380065b2142630021400085b264a130050380085b264a13005038006894b35842047320008244639a003850006891b35842047320008244639a003850007b8106ab9005640100a644639a00385000a9462587b402148007b8106ab9004630100248a3864207532000248a3864207532007b8006ab90046901085b364a1300503800a9462587b401938005278006a84004671095036ba1980504700a9462587b4021380090359a4b6808456006012142630021a0006014142630021400) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oW : Z mo 11 593 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem oX : Z mo 11 594 2 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x1a80813b700382100ba635694a0050610) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oY : Z mo 11 596 96 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x8796a2328746a2328746a23214a190103183123214ab901065ab401076b8612165ab301076b8612165a1401070b9a12165ab301065ab301065ab301065ab301065ab301070b8a12170b8a12126183121754b297565ab301076b8612165a5301065ab301065ab301065ab3010658b301065a1301070b8a19170b8a19170b8a19170b8a19170b8a191133912a2133912a2133912a270b8a19135ab043070b8a19170b8a19165ab301076586121765861217658612165ab301065ab301065ab301070b8a12170b8a121a1b68661a1b6865076b86121765861213146129270b8a12170b8a12190a055403bb618978796a2218786a2218796a2218796a2218796a2218796a2218796a2218796a2218796a2218796a221a1b68650531a04937658612153ba0493a1b6866153ba04938796a232531a0493a1b6865076b8612153ba0493a1b6866103ba049353ba0493133912921339129214ab901014ab901031461232314612323146123214ab901014ab901014ab9010426b234335ab0440426b2343) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem oZ : Z mo 11 692 7 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x8786a2218796a2328796a2328796a2328796a2328796a2328796a232) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem o0 : Z mo 11 699 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem o2 : Z mo 11 700 39 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0xb67b0a8656b6308070b9a121560a3080560a3080560a30808786a2218786a2218786a2218786a221093a55848786a2218786a2218786a2218786a2218786a221093a55848786a2218786a2218786a221a1b786508786a221754b29648786a2a2a1b78651a1b78661b67b0a75a1b786518786a2a22619318126193181261931817868a2a226193181b67b0a75261931818786a221b67b0a75a26a2872) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem o3 : Z mo 11 739 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem o4 : Z mo 11 740 31 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x754b296426543121b4a49550b4a49550b4a495508796a221a1b78650a1b78650a1b7865046ba7080a1b79650a1b78651b67b0a86b67b0a86a1b786618746a23242642343b67b0a8665a14010b67b0a86b4a495408796a232319612328796a2328796a2323146123231461232656b301065613010b464b550b67b0a86) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem o5 : Z mo 11 771 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem o6 : Z mo 11 772 3 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0xa1b68661929b07728796a232) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem o7 : Z mo 11 775 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem o8 : Z mo 11 776 44 := by
  apply bZ (pos:=aU) (neg:=aT) (data:=fun _ => 0x70b9a121946475503746723294a4755076b9712176b9712170b8a12165ab30108785b23270b8a1213185123265a530107058a12170b9a12114ab901065a530102659312126193121658530106585301026193121261931218796a2328796a2328796a2328796a23265a0301014a0901065a030102654312165ab401065a5401065a54010a1b6866165a5401065ab401065a5401065ab40108796a232656130108796a23270b9a12170b9a12114a59010) rfl
  decide +kernel
theorem oE : Z mo 11 0 820 := (@X mo 11 0 504 316 (@X mo 11 0 399 105 (@X mo 11 0 112 287 (@X mo 11 0 7 105 oF (@X mo 11 7 96 9 o1 oG)) (@X mo 11 112 192 95 (@X mo 11 112 96 96 oH oI) (@X mo 11 304 94 1 oJ oK))) (@X mo 11 399 23 82 (@X mo 11 399 2 21 (@X mo 11 399 1 1 oL oM) (@X mo 11 401 20 1 oN oO)) (@X mo 11 422 13 69 (@X mo 11 422 10 3 oP oQ) (@X mo 11 435 68 1 oR oS)))) (@X mo 11 504 195 121 (@X mo 11 504 89 106 (@X mo 11 504 5 84 oT (@X mo 11 509 1 83 oU oV)) (@X mo 11 593 3 103 (@X mo 11 593 1 2 oW oX) (@X mo 11 596 96 7 oY oZ))) (@X mo 11 699 72 49 (@X mo 11 699 40 32 (@X mo 11 699 1 39 o0 o2) (@X mo 11 739 1 31 o3 o4)) (@X mo 11 771 4 45 (@X mo 11 771 1 3 o5 o6) (@X mo 11 775 1 44 o7 o8)))))
set_option maxHeartbeats 0 in
theorem pd : Z mo 12 0 62 := by
  apply aM
  apply aE (ar:=10) (rows:=0) (d:=3)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pJ : Z mo 12 62 96 := by
  apply aM
  apply aE (ar:=11) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pe : Z mo 12 158 75 := by
  apply aM
  apply aE (ar:=11) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pf : Z mo 12 233 10 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x201594753007540009102524b310053200201594753007540000a814135700402100601214263002140006014142630021400008214635a1040610008214635a1040610008214635a104061002108b2a531085320) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem ph : Z mo 12 243 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pi : Z mo 12 244 21 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x2018b4a53008540002018b4a53008540002018b4a53008540002018b4a5300854000801264a1300614000201694753007540002016947530075400020169475300754000201594753007540002015947530075400020159475300754000801264a1300614000250885a2900835000250885a2900835000850265a1900615000a5022578900235000862008a60208613106894b3584205843000248a3864208643000892a36842068430008b2a36842068430) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pj : Z mo 12 265 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pk : Z mo 12 266 29 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x832008a60208613100268a9867508675009a5093b78405734009a6093b7840573400201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a13006140009a5093b7840573400801264a1300614000801264a1300614000801264a1300614000801264a1300614000b8262631a0032610008257691a0072610008257691a0072610018202631a0032610) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pl : Z mo 12 295 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pn : Z mo 12 296 13 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x268a9867508675000268a9867508675000268a98675086750090379a7b6807568000268a9867508675000268a98675086750080359a7b6807568000268a9867508675000268a986750867500a230690a5701657000268a986750867500a230690a57016570026a0027958027531) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem po : Z mo 12 309 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pq : Z mo 12 310 1 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x268a98675086750) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pt : Z mo 12 311 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pu : Z mo 12 312 6 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xa230690a5701657000268a986750867500a9462587b40325000a9462587b40325000a9462587b4032500095046ba198061580) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem px : Z mo 12 318 7 := by
  apply aM
  apply aE (ar:=12) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem py : Z mo 12 325 6 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xa9462587b4032500086406b0a58016580085026ba09806158007b8106ab9006851107b8006a83006831106894b35842058430) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pz : Z mo 12 331 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pB : Z mo 12 332 4 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x9a5093b78405734009230631a2401634009260631a2401634009230631a24016340) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pC : Z mo 12 336 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pD : Z mo 12 337 7 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xa9462587b40325000a9462587b403250005890b3984205843005890b3984205843005890b398420584300a9462587b403250005890b39842058430) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pE : Z mo 12 344 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pF : Z mo 12 345 22 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0xa50225789002350005a80b1987005821006894b3584205843006894b3584205843006894b358420584300a230690a5701657006894b3584205843000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a3864208643000248a3864208643005896a3684206843000248a3b64208643000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a38642086430) rfl
  decide +kernel
set_option maxHeartbeats 0 in
theorem pH : Z mo 12 367 1 := by
  exact aM (by decide +kernel)
set_option maxHeartbeats 0 in
theorem pI : Z mo 12 368 18 := by
  apply bi (pos:=aU) (neg:=aT) (data:=fun _ => 0x5a80b198700582100634ab489350854000a43752874903205304687b58294083506076835894a3050834059471b98670581230250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000650215269002150000628a186200862100250885a2900835000a5022578900235000a5022578900235000a502257890023500) rfl
  decide +kernel
theorem o9 : Z mo 12 0 386 := (@X mo 12 0 311 75 (@X mo 12 0 265 46 (@X mo 12 0 233 32 (@X mo 12 0 62 171 pd (@X mo 12 62 96 75 pJ pe)) (@X mo 12 233 10 22 pf (@X mo 12 243 1 21 ph pi))) (@X mo 12 265 31 15 (@X mo 12 265 1 30 pj (@X mo 12 266 29 1 pk pl)) (@X mo 12 296 13 2 pn (@X mo 12 309 1 1 po pq)))) (@X mo 12 311 25 50 (@X mo 12 311 14 11 (@X mo 12 311 1 13 pt (@X mo 12 312 6 7 pu px)) (@X mo 12 325 6 5 py (@X mo 12 331 1 4 pz pB))) (@X mo 12 336 9 41 (@X mo 12 336 1 8 pC (@X mo 12 337 7 1 pD pE)) (@X mo 12 345 22 19 pF (@X mo 12 367 1 18 pH pI)))))
set_option maxHeartbeats 0 in
theorem pL : Z mo 13 0 5 := by
  apply aM
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pN : Z mo 13 5 18 := by
  apply aM
  apply aE (ar:=10) (rows:=0) (d:=1)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem pM : Z mo 13 23 43 := by
  apply aM
  apply aE (ar:=11) (rows:=0) (d:=3)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem pK : Z mo 13 0 66 := (@X mo 13 0 5 61 pL (@X mo 13 5 18 43 pN pM))
set_option maxHeartbeats 0 in
theorem pP : Z mo 14 0 9 := by
  apply aM
  apply aE (ar:=10) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem pO : Z mo 14 0 9 := pP
set_option maxHeartbeats 0 in
theorem pR : Z mo 15 0 1 := by
  exact aM (by decide +kernel)
theorem pQ : Z mo 15 0 1 := pR
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rZ : cE mo 15 := by
  intro k hk
  interval_cases k
  · exact az mo 0 0
  · exact az mo 1 0
  · exact az mo 2 0
  · exact az mo 3 0
  · exact az mo 4 0
  · exact az mo 5 0
  · exact az mo 6 0
  · exact az mo 7 0
  · exact az mo 8 0
  · exact hb9
  · exact oq
  · exact oE
  · exact o9
  · exact pK
  · exact pO
  · exact pQ
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ul : Q sg 8 0 6 = true := by
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tQ : Q sg 8 0 6 = true := ul
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem um : Q sg 9 0 21 = true := by
  apply aE (ar:=9) (rows:=0) (d:=2)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem un : Q sg 9 21 48 = true := by
  apply aE (ar:=10) (rows:=0) (d:=3)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tR : Q sg 9 0 69 = true := (@ba sg 9 0 21 48 um un)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t7 : Q sg 10 0 3 = true := by
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ua : Q sg 10 3 128 = true := by
  apply aE (ar:=10) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t8 : Q sg 10 131 111 = true := by
  apply aE (ar:=10) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t9 : Q sg 10 242 128 = true := by
  apply aE (ar:=11) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ub : Q sg 10 370 3 = true := by
  apply aE (ar:=11) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tL : Q sg 10 0 373 = true := (@ba sg 10 0 131 242 (@ba sg 10 0 3 128 t7 ua) (@ba sg 10 131 111 131 t8 (@ba sg 10 242 128 3 t9 ub)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uc : Q sg 11 0 2 = true := by
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ue : Q sg 11 2 62 = true := by
  apply aE (ar:=10) (rows:=0) (d:=3)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uf : Q sg 11 64 123 = true := by
  apply aE (ar:=11) (rows:=0) (d:=4)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ud : Q sg 11 187 29 = true := by
  apply aE (ar:=12) (rows:=0) (d:=2)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tM : Q sg 11 0 216 = true := (@ba sg 11 0 64 152 (@ba sg 11 0 2 62 uc ue) (@ba sg 11 64 123 29 uf ud))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ug : Q sg 12 0 1 = true := by
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uh : Q sg 12 1 12 = true := by
  apply aE (ar:=10) (rows:=0) (d:=1)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ui : Q sg 12 13 17 = true := by
  apply aE (ar:=11) (rows:=0) (d:=1)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tN : Q sg 12 0 30 = true := (@ba sg 12 0 1 29 ug (@ba sg 12 1 12 17 uh ui))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uj : Q sg 13 0 3 = true := by
  apply aE (ar:=10) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tO : Q sg 13 0 3 = true := uj
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uk : Q sg 14 0 1 = true := by
  apply aE (ar:=9) (rows:=0) (d:=0)
  simp only [J,aC]
  repeat' apply And.intro
  all_goals decide +kernel
theorem tP : Q sg 14 0 1 = true := uk
set_option maxHeartbeats 0 in
theorem uo : cI sg 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : Q sg 0 0 0 = true)
  · exact (rfl : Q sg 1 0 0 = true)
  · exact (rfl : Q sg 2 0 0 = true)
  · exact (rfl : Q sg 3 0 0 = true)
  · exact (rfl : Q sg 4 0 0 = true)
  · exact (rfl : Q sg 5 0 0 = true)
  · exact (rfl : Q sg 6 0 0 = true)
  · exact (rfl : Q sg 7 0 0 = true)
  · exact tQ
  · exact tR
  · exact tL
  · exact tM
  · exact tN
  · exact tO
  · exact tP
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r8 : aH false cC 15 inputs.toFinset := by
  rw [show cC = aY mo by decide +kernel]
  exact jT (g:=mo) (top:=15) (i:=0) (ag pri vH) r7 rZ (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ur : aH true cC 14 inputs.toFinset := by
  rw [show cC = aY sg by decide +kernel]
  exact hG (g:=sg) (top:=14) (i:=0) (ag hM vI) uq uo (by decide) (by decide +kernel)
end Numeric
namespace Peter17
def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
end Peter17

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Reader7354
def pins (g : Gate) := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
def touch (g : Gate) : Bool := (pins g).any (fun i => i == 0 || i == 10)
def spec (C : Circuit) := ∀ x : Fin 10 → Bool,
  C.eval (List.ofFn x ++ [x 0 && x 2]) = Peter17.target x
end Reader7354

namespace Reader7354.Copy
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def name {n m} (f : Fin n → Fin m) (base i : ℕ) :=
  if hi : i<n then (f ⟨i,hi⟩).val else base+(i-n)
def renameG {n m} (f : Fin n → Fin m) (base : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (name f base)⟩
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem old (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k<w.length) : (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem lookup {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m ≤ W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (z : List Bool) (i : Nat) :
    (W++z).getD (name f W.length i) false = (List.ofFn x++z).getD i false := by
  unfold name
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (by have := (f ⟨i,hi⟩).isLt; omega),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD,hi] using ag ⟨i,hi⟩
  next hi =>
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : W.length ≤ W.length+(i-n)),
      List.getElem?_append_right (by simp;omega : (List.ofFn x).length ≤ i),List.length_ofFn,Nat.add_sub_cancel_left]

theorem sim {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (gs : List Gate) (z : List Bool) :
    ∃ endBits, run gs (List.ofFn x ++ z) = List.ofFn x ++ endBits ∧
      run (gs.map (renameG f W.length)) (W++z) = W++endBits := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x ++ z).getD i false)
    obtain ⟨t,h1,h2⟩ := ih (z++[bit])
    refine ⟨t,?_,?_⟩
    · simpa [run,step,bit,List.append_assoc] using h1
    · have hstep : step (W++z) (renameG f W.length g) = W++(z++[bit]) := by
        simp only [step,renameG,List.map_map,Function.comp_def,lookup f W hw x ag,List.append_assoc,bit]
      change run _ (step (W++z) (renameG f W.length g)) = _
      rw [hstep];exact h2

theorem copy_val {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (C : Circuit) :
    (run (C.gates.map (renameG f W.length)) W).getD (name f W.length C.output) false = circuitFun n C x := by
  obtain ⟨z,h1,h2⟩ := sim f W hw x ag C.gates []
  simp only [List.append_nil] at h1 h2
  change _ = (run C.gates (List.ofFn x)).getD C.output false
  rw [h1,h2,lookup _ _ hw x ag]

end Reader7354.Copy
namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def rawShrink (i : Fin 11) : Fin 10 := if h : i.val<10 then ⟨i.val,h⟩ else 0
def collapse := Copy.name rawShrink 10
def down (g : Gate) : Gate := ⟨g.op,g.inputs.map collapse⟩
def squeeze (C : Circuit) : Circuit := ⟨C.gates.map down, collapse C.output⟩
theorem squeeze_size (C : Circuit) : (squeeze C).size=C.size := by simp [squeeze,Circuit.size]
theorem squeeze_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (squeeze C) := by
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [down] using h v hv
theorem squeeze_eval (C : Circuit) (x : Fin 10→Bool) :
    (squeeze C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0]) := by
  have ag (p : Fin 11) : (List.ofFn x).getD (rawShrink p).val false = (x ∘ rawShrink) p := by
    fin_cases p <;> rfl
  have hl : List.ofFn (x ∘ rawShrink) = List.ofFn x ++ [x 0] := rfl
  have h := Copy.copy_val rawShrink (List.ofFn x) (by simp) (x ∘ rawShrink) ag C
  simp only [List.length_ofFn] at h
  rw [←hl]
  exact h
end Reader7354

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Reader7354
def fixG (g : Gate) : Gate :=
  if 0 ∈ pins g ∧ 10 ∈ pins g then
    match g.op with | .and => ⟨.and,[10]⟩ | _ => ⟨.or,[0]⟩
  else ⟨g.op,pins g⟩
def fixed (C : Circuit) : Circuit := ⟨C.gates.map fixG,C.output⟩
def gval (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
theorem pair {l : List ℕ} (n : l.length≤2) (h : 0∈l ∧ 10∈l) :
    l=[0,10] ∨ l=[10,0] := by
  rcases l with _|⟨a, l⟩
  · simp at h
  rcases l with _|⟨b,l⟩
  · simp_all <;> omega
  rcases l with _|⟨c,l⟩
  · simp at h
    grind
  · simp at n
theorem sep (g : Gate) : ¬ (0∈(fixG g).inputs ∧ 10∈(fixG g).inputs) := by
  unfold fixG
  split
  · rcases g with ⟨op,l⟩; cases op <;> simp
  · assumption
theorem touch_of_fix (g : Gate) (h : 0∈(fixG g).inputs ∨ 10∈(fixG g).inputs) : touch g = true := by
  rw [touch,List.any_eq_true]
  have one : 0∈pins g ∨ 10∈pins g := by
    unfold fixG at h
    split at h
    next both => exact Or.inl both.1
    next => exact h
  rcases one with h|h
  · exact ⟨0,h,rfl⟩
  · exact ⟨10,h,rfl⟩
theorem pins_len (g : Gate) : (pins g).length ≤ g.inputs.length := by
  rcases g with ⟨op,l⟩; cases op <;> simp [pins,List.length_take]
theorem fix_fan (C : Circuit) (fan : FanInTwo C) : FanInTwo (fixed C) := by
  intro g hg
  obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hg
  have hx := fan h hm
  unfold fixG
  split
  · cases h with | mk op l => cases op <;> simp
  · exact ⟨hx.1,(pins_len h).trans hx.2⟩
theorem fix_size (C : Circuit) : (fixed C).size = C.size := by simp [fixed,Circuit.size]

theorem evalPins (g : Gate) (w : List Bool) : gval ⟨g.op,pins g⟩ w = gval g w := by
  rcases g with ⟨op,l⟩
  cases op <;> first | rfl | (cases l <;> rfl)

theorem fix_val (g : Gate) (fan : g.op∈({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (w : List Bool) (a b : Bool) (h0 : w.getD 0 false=a) (h10 : w.getD 10 false = (a && b)) :
    gval (fixG g) w = gval g w := by
  rw [←evalPins g w]
  unfold fixG
  split
  next hb =>
    have hp := pair ((pins_len g).trans fan.2) hb
    rcases hp with hp|hp
    all_goals
      rw [hp]
      rcases g with ⟨op,l⟩
      cases op <;> simp_all [gval,GateOp.eval,pins,Set.mem_insert_iff]
    all_goals first | (cases a <;> cases b <;> simp_all) |
      (have := congrArg List.length hp; simp [List.length_take] at this; omega)
    all_goals have q := congrArg List.length hp; simp only [List.length_take,List.length_cons,List.length_nil] at q; omega
  next => rfl

theorem fixed_eval (C : Circuit) (fan : FanInTwo C) (x : Fin 10→Bool) :
    (fixed C).eval (List.ofFn x ++ [x 0 && x 2]) = C.eval (List.ofFn x ++ [x 0 && x 2]) := by
  have fk (gs : List Gate) (legal : ∀g∈gs,g.op∈({.and,.or,.not}:Set GateOp) ∧ g.inputs.length≤2) :
      ∀ (w : List Bool), 10<w.length → w.getD 0 false=x 0 → w.getD 10 false=(x 0 && x 2) →
      Copy.run (gs.map fixG) w = Copy.run gs w := by
    induction gs with
    | nil => intros; rfl
    | cons g gs ih =>
      intro w len h0 hz
      have h := fix_val g (legal g List.mem_cons_self) w (x 0) (x 2) h0 hz
      change Copy.run (gs.map fixG) (w++[gval (fixG g) w]) = Copy.run gs (w++[gval g w])
      rw [h]
      apply ih (fun j hj => legal j (List.mem_cons_of_mem _ hj))
      · simp; omega
      · rwa [List.getD_append _ _ _ _ (by omega)]
      · rwa [List.getD_append _ _ _ _ len]
  exact congrArg (fun w : List Bool => w.getD C.output false) (fk C.gates fan _ (by simp) rfl rfl)

theorem ignore (gs : List Gate) (idx : ℕ) (no : ∀g∈gs, idx∉g.inputs) :
    ∀ w v : List Bool, w.length=v.length → (∀i,i≠idx → w.getD i false = v.getD i false) →
    ∀i,i≠idx → (Copy.run gs w).getD i false=(Copy.run gs v).getD i false := by
  induction gs with
  | nil => exact fun w v _ h => h
  | cons g gs ih =>
    intro w v len eq
    have same : gval g w = gval g v := congrArg g.op.eval
      (List.map_congr_left (fun i hi => eq i (fun e => no g List.mem_cons_self (e ▸ hi))))
    change ∀i, i≠idx → (Copy.run gs (w++[gval g w])).getD i false = (Copy.run gs (v++[gval g v])).getD i false
    rw [same]
    apply ih (fun g hg => no g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
    intro i hi
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ (by omega)]
      exact eq i hi
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : w.length ≤ i),
        List.getElem?_append_right (by omega : v.length ≤ i),len]
end Reader7354

namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem no_pins (C : Circuit) (few : C.gates.countP touch ≤ 1) :
    (∀g∈(fixed C).gates, 0∉g.inputs) ∨ (∀g∈(fixed C).gates, 10∉g.inputs) := by
  by_contra! bad
  rcases bad with ⟨⟨g,hg,h0⟩,⟨h,hh,h10⟩⟩
  obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
  obtain ⟨h₀,hh₀,rfl⟩ := List.mem_map.mp hh
  let pool := C.gates.filter touch
  have gmem : g₀ ∈ pool := List.mem_filter.mpr ⟨hg₀,touch_of_fix g₀ (Or.inl h0)⟩
  have hmem : h₀ ∈ pool := List.mem_filter.mpr ⟨hh₀,touch_of_fix h₀ (Or.inr h10)⟩
  have hp : pool.length ≤ 1 := by simpa only [pool,List.countP_eq_length_filter] using few
  have unique (l : List Gate) (hl : l.length ≤ 1) (g h : Gate) (g₁ : g∈l) (h₁ : h∈l) : g=h := by
    cases l with
    | nil => simp at g₁
    | cons v t =>
      cases t with
      | nil => simp_all
      | cons y r => simp at hl
  have geq := unique pool hp g₀ h₀ gmem hmem
  subst h₀
  exact sep g₀ ⟨h0,h10⟩

theorem out_ne (C : Circuit) (ok : spec C) : C.output ≠ 0 ∧ C.output ≠ 10 := by
  let x : Fin 10 → Bool := fun i => decide (i.val=3 ∨ i.val=4)
  let w := List.ofFn x ++ [x 0 && x 2]
  have h := ok x
  change (Copy.run C.gates w).getD C.output false = Peter17.target x at h
  have ht : Peter17.target x=true := rfl
  rw [ht] at h
  constructor
  · rintro e
    rw [e,Copy.old _ _ _ (by simp [w])] at h
    exact Bool.noConfusion h
  · rintro e
    rw [e,Copy.old _ _ _ (by simp [w])] at h
    exact Bool.noConfusion h

theorem no0_absurd (C : Circuit) (ok : spec C) (no : ∀g∈C.gates,0∉g.inputs) : False := by
  let a : Fin 10 → Bool := fun i => decide (i.val=1)
  let b : Fin 10 → Bool := fun i => decide (i.val≤1)
  let w := List.ofFn a ++ [a 0 && a 2]
  let v := List.ofFn b ++ [b 0 && b 2]
  have neq : C.output ≠ 0 := (out_ne C ok).1
  have src (i : ℕ) (hn : i≠0) : w.getD i false=v.getD i false := by
    by_cases h : i<11
    · interval_cases i <;> first | contradiction | rfl
    · rw [List.getD_eq_default _ _ (by simp [w];omega),List.getD_eq_default _ _ (by simp [v];omega)]
  have agree := ignore C.gates 0 no w v (by simp [w,v]) src C.output neq
  have h1 := ok a
  have h2 := ok b
  change (Copy.run C.gates w).getD C.output false = Peter17.target a at h1
  change (Copy.run C.gates v).getD C.output false = Peter17.target b at h2
  rw [h1,h2] at agree
  exact Bool.noConfusion agree

def ordinary17 := ∀ C : Circuit, FanInTwo C → C.size≤17 →
  ∃ x : Fin 10→Bool, C.eval (List.ofFn x) ≠ Peter17.target x

theorem noz_absurd (floor : ordinary17) (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 17)
    (ok : spec C) (no : ∀g∈C.gates,10∉g.inputs) : False := by
  obtain ⟨x,hx⟩ := floor (squeeze C) (squeeze_fan C fan) (by rwa [squeeze_size])
  apply hx
  rw [squeeze_eval]
  let a := List.ofFn x ++ [x 0]
  let b := List.ofFn x ++ [x 0 && x 2]
  have agree (i : ℕ) (hi : i≠10) : a.getD i false=b.getD i false := by
    by_cases small : i<10
    · exact (List.getD_append _ _ _ _ (by simpa using small)).trans
        (List.getD_append _ _ _ _ (by simpa using small)).symm
    · rw [List.getD_eq_default _ _ (by simp [a];omega),List.getD_eq_default _ _ (by simp [b];omega)]
  exact (ignore C.gates 10 no a b (by simp [a,b]) agree C.output (out_ne C ok).2).trans (ok x)

theorem few (floor : ordinary17) (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 17)
    (hf : C.gates.countP touch ≤ 1) (ok : spec C) : False := by
  have ok' : spec (fixed C) := fun x => (fixed_eval C fan x).trans (ok x)
  rcases no_pins C hf with hh|hh
  · exact no0_absurd _ ok' hh
  · exact noz_absurd floor _ (fix_fan C fan) (by rwa [fix_size]) ok' hh
end Reader7354

namespace MonoPin7354.Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
abbrev Stat := Bool ⊕ ℕ
def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
end MonoPin7354.Pin
namespace MonoPin7354
open PEqualNP.CircuitLowerBounds
def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]
def edgeFunction (x : Fin 10 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)
def minorGraph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonoPin7354.Pin
def touched (mark : ℕ → Bool) : List Gate → ℕ
  | [] => 0
  | g :: tail => (if g.inputs.any mark then 1 else 0) + touched mark tail
def fixedSlot {m : ℕ} (slot : Fin m → Stat) (i : ℕ) : Bool :=
  if h : i < m then match slot ⟨i,h⟩ with
    | .inl _ => true
    | .inr _ => false
  else false
private lemma elim_cost (n : ℕ) (mark : ℕ → Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ i, mark i = true → i < acc.1.length ∧ ∃ b, acc.1.getD i (.inl false) = .inl b) →
      (∀ g ∈ gs, NOk g) →
      (elim n gs acc).2.length + touched mark gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim,touched]
  | cons g gs ih =>
    intro acc fixed valid
    let next := elimStep n acc g
    have persist (i : ℕ) (hi : mark i = true) :
        i < next.1.length ∧ ∃ b, next.1.getD i (.inl false) = .inl b := by
      obtain ⟨bound,b,eq⟩ := fixed i hi
      refine ⟨by simp [next,elimStep]; omega, b, ?_⟩
      simp only [next,elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact eq
    have rest := ih next persist (fun h hh => valid _ (List.mem_cons_of_mem _ hh))
    change (elim n gs next).2.length + touched mark (g::gs) ≤ _
    rw [touched,List.length_cons]
    by_cases hits : g.inputs.any mark = true
    · obtain ⟨i,inside,yes⟩ := List.any_eq_true.mp hits
      obtain ⟨_,b,eq⟩ := fixed i yes
      have legal := valid g List.mem_cons_self
      have gone := simplify_count g.op (n+acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))
        legal.1.1 (by simpa using legal.1.2) (fun h => by simpa using legal.2 h)
        ⟨b, List.mem_map.mpr ⟨i,inside,eq⟩⟩
      have same : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n+acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList).length = _
        rw [gone]; simp
      simp only [hits,ite_true]
      omega
    · have grow : next.2.length ≤ acc.2.length+1 := by
        simp only [next,elimStep,List.length_append]
        have := toList_length_le (simplify g.op (n+acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1
        omega
      have zero : (if g.inputs.any mark then 1 else 0 : ℕ) = 0 := if_neg hits
      rw [zero]
      omega
theorem marked_restriction {m n : ℕ} (C : Circuit) (legal : FanInTwo C)
    (slot : Fin m → Stat) (valid : ∀ i, Stat.Valid n (slot i)) (f : (Fin n → Bool) → Bool)
    (correct : ∀ y, C.eval (List.ofFn fun i => Stat.val (List.ofFn y) (slot i)) = f y)
    (different : ∃ y z, f y ≠ f z) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + touched (fixedSlot slot) (C.gates.map normGate) ≤ C.size ∧
      ∀ y, D.eval (List.ofFn y) = f y := by
  let gs := C.gates.map normGate
  let start := (List.ofFn slot, ([] : List Gate))
  let acc := elim n gs start
  have normalized (g : Gate) (hg : g ∈ gs) : NOk g := by
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok old (legal _ ho)
  have fixed (i : ℕ) (hi : fixedSlot slot i = true) :
      i < start.1.length ∧ ∃ b, start.1.getD i (.inl false) = .inl b := by
    by_cases earlier : i < m
    · refine ⟨by simpa [start] using earlier,?_⟩
      cases eq : slot ⟨i,earlier⟩ with
      | inl b => exact ⟨b,by simpa [start,earlier] using eq⟩
      | inr => simp [fixedSlot,earlier,eq] at hi
    · simp [fixedSlot,earlier] at hi
  have size : acc.2.length + touched (fixedSlot slot) gs ≤ C.size := by
    simpa [gs,start,Circuit.size,acc] using elim_cost n (fixedSlot slot) gs start fixed normalized
  have semantics (y : Fin n → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    let wire0 := List.ofFn fun i => Stat.val (List.ofFn y) (slot i)
    have initial : Inv n (List.ofFn y) wire0 start := by
      refine ⟨by simp [start,wire0],?_⟩
      intro i
      by_cases lt : i < m
      · simpa [start,wire0,lt,wiresFrom] using And.intro (valid ⟨i,lt⟩)
          (rfl : Stat.val (List.ofFn y) (slot ⟨i,lt⟩) = _)
      · have high : m ≤ i := Nat.le_of_not_gt lt
        change Stat.Valid _ ((List.ofFn slot).getD i (.inl false)) ∧ _
        rw [List.getD_eq_default _ _ (by simpa using high)]
        simp [wire0,lt,Stat.val,Stat.Valid]
    have finished := inv_elim n (List.ofFn y) (by simp) gs wire0 start
      (fun g h => (normalized g h).1) initial
    have eq := (finished.2 C.output).2
    rw [show wiresFrom gs wire0 = wiresFrom C.gates wire0 from wiresFrom_norm _ _] at eq
    exact eq.trans (correct y)
  cases which : acc.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨y,z,ne⟩ := different
    exact False.elim (ne (by rw [← semantics y,← semantics z,which]; rfl))
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs start (by simp [start]),size,?_⟩
    intro y
    have eq := semantics y
    rw [which] at eq
    exact eq
theorem touched_positive (mark : ℕ → Bool) {gs : List Gate} (k : ℕ) (hk : mark k = true)
    (reads : ∃ g ∈ gs, k ∈ g.inputs) : 0 < touched mark gs := by
  induction gs with
  | nil => simp at reads
  | cons g gs ih =>
    obtain ⟨h,hh,mem⟩ := reads
    rcases List.mem_cons.mp hh with rfl | later
    · have yes := List.any_eq_true.mpr ⟨k,mem,hk⟩
      simp [touched,yes]
    · have lower := ih ⟨h,later,mem⟩
      simp only [touched]
      omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonoPin7354.Pin
private lemma ignore_marked (mark : ℕ → Bool) (gs : List Gate)
    (none : ∀ g ∈ gs, ∀ i ∈ g.inputs, mark i = false) :
    ∀ x y : List Bool, x.length = y.length → (∀ i, mark i = false → x.getD i false = y.getD i false) →
    ∀ i, mark i = false → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs with
  | nil => exact fun x y _ eq => eq
  | cons g gs ih =>
    intro x y len eq
    let act (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
    have same : act x = act y := congrArg g.op.eval (List.map_congr_left
      (fun i hi => eq i (none g List.mem_cons_self i hi)))
    apply ih (fun h hh => none h (List.mem_cons_of_mem _ hh)) (x++[act x]) (y++[act y]) (by simp [len])
    intro i k
    by_cases last : i=x.length
    · subst i; rw [getD_snoc_eq,len,getD_snoc_eq,same]
    · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (fun e => last (e.trans len.symm))]
      exact eq i k
theorem witness_saves_gate {m n : ℕ} (C : Circuit) (legal : FanInTwo C) (slot : Fin m → Stat)
    (valid : ∀ i, Stat.Valid n (slot i)) (f : (Fin n → Bool) → Bool)
    (correct : ∀ y, C.eval (List.ofFn fun i => Stat.val (List.ofFn y) (slot i)) = f y)
    (different : ∃ y z, f y ≠ f z)
    (a b : Fin m → Bool) (separates : C.eval (List.ofFn a) ≠ C.eval (List.ofFn b))
    (agrees : ∀ i : Fin m, fixedSlot slot i.val = false → a i = b i) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧ ∀ y, D.eval (List.ofFn y) = f y := by
  obtain ⟨D,hD,size,hf⟩ := marked_restriction C legal slot valid f correct different
  refine ⟨D,hD,?_,hf⟩
  suffices pos : 0 < touched (fixedSlot slot) (C.gates.map normGate) by omega
  by_contra! empty
  have noRead : ∀ g ∈ C.gates.map normGate, ∀ i ∈ g.inputs, fixedSlot slot i = false := by
    intro g hg i hi
    apply Bool.eq_false_iff.mpr
    intro marked
    have pos := touched_positive (fixedSlot slot) i marked ⟨g,hg,hi⟩
    omega
  have outFree : fixedSlot slot C.output = false := by
    by_cases bound : C.output < m
    · cases eq : slot ⟨C.output,bound⟩ with
      | inr j => simp [fixedSlot,bound,eq]
      | inl constant =>
        exfalso
        have independent (y : Fin n → Bool) : f y = constant := by
          let w := List.ofFn (fun i => Stat.val (List.ofFn y) (slot i))
          have h : (wiresFrom C.gates w).getD C.output false = f y := correct y
          obtain ⟨tail,append,_⟩ := wiresFrom_prefix C.gates w
          rw [append,List.getD_append _ _ _ _ (by simpa [w] using bound)] at h
          have input {k : ℕ} (x : Fin k → Bool) (i : Fin k) : (List.ofFn x).getD i.val false = x i := by
            simp [List.getD_eq_getElem?_getD,i.isLt]
          have hw := input (fun i => Stat.val (List.ofFn y) (slot i)) ⟨C.output,bound⟩
          rw [eq] at hw
          exact h.symm.trans hw
        obtain ⟨y,z,ne⟩ := different
        exact ne ((independent y).trans (independent z).symm)
    · simp [fixedSlot,bound]
  have agreeAt (i : ℕ) (free : fixedSlot slot i = false) :
      (List.ofFn a).getD i false = (List.ofFn b).getD i false := by
    by_cases before : i < m
    · simpa [List.getD_eq_getElem?_getD,before] using agrees ⟨i,before⟩ free
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  have eq := ignore_marked (fixedSlot slot) _ noRead (List.ofFn a) (List.ofFn b)
    (by simp) agreeAt C.output outFree
  rw [wiresFrom_norm,wiresFrom_norm] at eq
  exact separates eq
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonoPin7354.Pin (Stat ofFn_snoc)
def pinName (i : ℕ) : Fin 11 := if h : i<10 then ⟨i,by omega⟩ else 10
def atom (a : Fin 11) (x : Fin 10 → Bool) := (List.ofFn x).getD a.val false
def gateForm (op : Fin 3) (a b : Fin 11) (x : Fin 10 → Bool) : Bool :=
  if op=2 then !(atom a x) else if op=0 then atom a x && atom b x else atom a x || atom b x
private lemma readPin (i : ℕ) (x : Fin 10 → Bool) :
    (List.ofFn x).getD i false = atom (pinName i) x := by
  by_cases h : i<10
  · simp [atom,pinName,h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [atom,pinName,h,List.getD_eq_getElem?_getD]
theorem gate_shape (g : Gate) (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) :
    ∃ (op : Fin 3) (a b : Fin 11), ∀ x : Fin 10 → Bool,
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = gateForm op a b x := by
  obtain ⟨kind,len⟩ := legal
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at kind
  cases hs : g.inputs with
  | nil =>
    rcases kind with h | h | h
    · exact ⟨2,10,10,fun x => by simp [hs,h,GateOp.eval,gateForm,atom,List.getD_eq_getElem?_getD]⟩
    · exact ⟨1,10,10,fun x => by simp [hs,h,GateOp.eval,gateForm,atom,List.getD_eq_getElem?_getD]⟩
    · exact ⟨2,10,10,fun x => by simp [hs,h,GateOp.eval,gateForm,atom,List.getD_eq_getElem?_getD]⟩
  | cons i rest =>
    cases rest with
    | nil =>
      rcases kind with h | h | h
      · exact ⟨0,pinName i,pinName i,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
      · exact ⟨1,pinName i,pinName i,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
      · exact ⟨2,pinName i,pinName i,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
    | cons j tail =>
      have empty : tail = [] := by rw [hs] at len; simp at len; simpa using len
      subst tail
      rcases kind with h | h | h
      · exact ⟨0,pinName i,pinName j,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
      · exact ⟨1,pinName i,pinName j,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
      · exact ⟨2,pinName i,pinName i,fun x => by simp [hs,h,GateOp.eval,gateForm,← readPin]⟩
def chosen (a b : Fin 11) : Fin 10 :=
  if h : a.val<10 then ⟨a.val,h⟩ else if h : b.val<10 then ⟨b.val,h⟩ else 0
def replacement (op : Fin 3) (a b : Fin 11) : Fin 12 :=
  if op=2 then 11 else if op=0 then 10 else
    if b.val<10 ∧ b.val ≠ (chosen a b).val then b.castSucc else 10
def literal (r : Fin 12) (x : Fin 10 → Bool) := if h : r.val<10 then x ⟨r.val,h⟩ else decide (r.val=11)
set_option maxHeartbeats 4000000 in
theorem replacement_correct : ∀ (op : Fin 3) (a b : Fin 11) (x : Fin 10 → Bool),
    x (chosen a b) = false → gateForm op a b x = literal (replacement op a b) x := by
  decide +kernel
def low (w u : Fin 10) (i : Fin 10) := decide (i=w ∨ i=u)
set_option maxHeartbeats 4000000 in
theorem sensitivity_tests : ∀ (op : Fin 3) (a b : Fin 11), ∃ w u : Fin 10,
    let x := low w u
    let y := Function.update x (chosen a b) true
    edgeFunction x ≠ edgeFunction y ∧
      ((replacement op a b).val < 10 → gateForm op a b x = gateForm op a b y) := by
  decide +kernel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonoPin7354.Pin (Stat ofFn_snoc)
def toMinor : Fin 10 → Fin 10 → Fin 10 := ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7], ![6, 1, 0, 5, 8, 9, 2, 4, 7, 3], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
def extendNine (v : Fin 10) (y : Fin 9 → Bool) (i : Fin 10) :=
  (List.ofFn y).getD (toMinor v i).val false
def originalSlot (v i : Fin 10) : Stat :=
  if (toMinor v i).val < 9 then .inr (toMinor v i).val else .inl false
def finalSlot (v : Fin 10) (r : Fin 12) : Stat :=
  if h : r.val<10 then originalSlot v ⟨r.val,h⟩ else .inl (decide (r.val=11))
def slot (v : Fin 10) (r : Fin 12) (i : Fin 11) : Stat :=
  if h : i.val<10 then originalSlot v ⟨i.val,h⟩ else finalSlot v r
private def lifted (op : Fin 3) (a b : Fin 11) (x : Fin 10 → Bool) : Fin 11 → Bool :=
  Fin.snoc x (gateForm op a b x)
private lemma evaluate_original (v i : Fin 10) (y : Fin 9 → Bool) :
    Stat.val (List.ofFn y) (originalSlot v i) = extendNine v y i := by
  by_cases h : (toMinor v i).val < 9
  · simp [originalSlot,h,Stat.val,extendNine]
  · simp only [originalSlot,ite_eq_right h,Stat.val,extendNine]
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
private lemma evaluate_final (v : Fin 10) (r : Fin 12) (y : Fin 9 → Bool) :
    Stat.val (List.ofFn y) (finalSlot v r) = literal r (extendNine v y) := by
  by_cases h : r.val<10
  · simpa only [finalSlot,literal,dite_eq_left h] using evaluate_original v ⟨r.val,h⟩ y
  · simp [finalSlot,literal,h,Stat.val]
private theorem tail_restriction (T : Circuit) (fan : FanInTwo T) (op : Fin 3) (a b : Fin 11)
    (full : ∀ x, T.eval (List.ofFn (lifted op a b x)) = edgeFunction x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size+1 ≤ T.size ∧ ∀ y, D.eval (List.ofFn y) = minorGraph y := by
  let v := chosen a b
  let r := replacement op a b
  have rawValid (v i : Fin 10) : Stat.Valid 9 (originalSlot v i) := by
    unfold originalSlot
    split <;> simp_all [Stat.Valid]
  have valid (v : Fin 10) (r : Fin 12) (i : Fin 11) : Stat.Valid 9 (slot v r i) := by
    unfold slot
    split
    · exact rawValid _ _
    · unfold finalSlot
      split
      · exact rawValid _ _
      · trivial
  have off : ∀ v : Fin 10, ∀ y : Fin 9 → Bool, extendNine v y v=false := by decide +kernel
  have graph : ∀ v : Fin 10, ∀ y : Fin 9 → Bool, edgeFunction (extendNine v y)=minorGraph y := by decide +kernel
  have projected (y : Fin 9 → Bool) :
      (List.ofFn fun i => Stat.val (List.ofFn y) (slot v r i)) = List.ofFn (lifted op a b (extendNine v y)) := by
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Stat.val (List.ofFn y) (finalSlot v r) = lifted op a b (extendNine v y) (Fin.last 10)
      simp only [lifted,Fin.snoc_last,evaluate_final]
      exact (replacement_correct op a b _ (off v y)).symm
    · change Stat.val (List.ofFn y) (slot v r j.castSucc) = lifted op a b (extendNine v y) j.castSucc
      simpa only [slot,Fin.val_castSucc,dite_eq_left j.isLt,lifted,Fin.snoc_castSucc] using evaluate_original v j y
  obtain ⟨w,u,diff,same⟩ := sensitivity_tests op a b
  let x := low w u
  let y := Function.update x v true
  have changed : T.eval (List.ofFn (lifted op a b x)) ≠ T.eval (List.ofFn (lifted op a b y)) := by
    rw [full,full]; exact diff
  have marked : ∀ v r, fixedSlot (slot v r) (Fin.val v) = true := by decide +kernel
  have lastRaw : ∀ v r, fixedSlot (slot v r) 10 = false → r.val < 10 := by decide +kernel
  apply witness_saves_gate T fan (slot v r) (valid v r) minorGraph
    (fun yy => (congrArg T.eval (projected yy)).trans ((full _).trans (graph v yy)))
    ⟨fun _ => false,fun _ => true,by decide⟩ (lifted op a b x) (lifted op a b y) changed
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro free
    simpa only [lifted,Fin.snoc_last] using same (lastRaw v r free)
  · intro free
    have ne : j ≠ v := by
      intro eq
      subst j
      change fixedSlot (slot v r) v.val=false at free
      exact Bool.noConfusion ((marked v r).symm.trans free)
    simp only [lifted,Fin.snoc_castSucc,y,Function.update_of_ne ne]
theorem ordinary_lower (base : ¬HasCircuitSize 9 minorGraph 15) (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeFunction x) : 18 ≤ C.size := by
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    by_cases short : out < 10
    · let x : Fin 10 → Bool := fun i => decide (i.val = out)
      have h := correct x
      change (List.ofFn x).getD out false = edgeFunction x at h
      have no : ∀ v : Fin 10, edgeFunction (fun i => decide (i.val=v.val))=false := by decide +kernel
      rw [show edgeFunction x = false from no ⟨out,short⟩] at h
      have read {n : ℕ} (f : Fin n → Bool) (i : Fin n) : (List.ofFn f).getD i.val false = f i := by
        simp [List.getD_eq_getElem?_getD,i.isLt]
      have atOut : (List.ofFn x).getD out false = true := (read x ⟨out,short⟩).trans (by simp [x])
      exact False.elim (Bool.noConfusion (atOut.symm.trans h))
    · have h := correct (fun _ => true)
      change (List.ofFn (fun _ : Fin 10 => true)).getD out false = edgeFunction (fun _ => true) at h
      rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt short)] at h
      exact False.elim (Bool.noConfusion (h.trans (by decide : edgeFunction (fun _ => true) = true)))
  | cons g gs =>
    obtain ⟨op,a,b,shape⟩ := gate_shape g (legal g List.mem_cons_self)
    let T : Circuit := ⟨gs,out⟩
    have ok : FanInTwo T := fun h hmem => legal h (List.mem_cons_of_mem _ hmem)
    have full (x : Fin 10 → Bool) : T.eval (List.ofFn (lifted op a b x)) = edgeFunction x := by
      unfold lifted
      rw [ofFn_snoc,← shape x]
      exact correct x
    obtain ⟨D,fan,size,real⟩ := tail_restriction T ok op a b full
    have lower : 16 ≤ D.size := by
      by_contra small
      exact base ⟨D,fan,by omega,real⟩
    change D.size+1 ≤ gs.length at size
    change 18 ≤ (g::gs).length
    simp only [List.length_cons]; omega
end MonoPin7354

namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonoPin7354 MonoPin7354.Pin

theorem sameGraph (x : Fin 10→Bool) : edgeFunction x = Peter17.target x := by
  simp only [edgeFunction, edges, List.any_cons, List.any_nil, Bool.or_false, Peter17.target, Bool.or_assoc]

theorem marks (i : Nat) : fixedSlot (slot 0 10) i = (i == 0 || i == 10) := by
  by_cases hi : i<11
  · interval_cases i <;> rfl
  · have a : i≠0 := by omega
    have b : i≠10 := by omega
    simp [fixedSlot,hi,a,b]

theorem touched_eq (gs : List Gate) :
    touched (fixedSlot (slot 0 10)) (gs.map normGate) = gs.countP touch := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hp : (normGate g).inputs = pins g := by cases g with | mk op l => cases op <;> rfl
    have hf : fixedSlot (slot 0 10) = (fun i => i == 0 || i == 10) := funext marks
    simp only [List.map_cons, touched,List.countP_cons,ih,hp]
    simp only [touch,hf]
    exact Nat.add_comm _ _

theorem cheaperMany (base : ¬HasCircuitSize 9 minorGraph 15) (C : Circuit) (fan:FanInTwo C)
    (size:C.size≤17) (hm:2≤C.gates.countP touch) (ok:spec C) : False := by
  have valid : ∀ i, Stat.Valid 9 (slot 0 10 i) := by intro i; fin_cases i <;> dsimp [slot, originalSlot, finalSlot, toMinor, Stat.Valid] <;> decide
  have graph : ∀ y : Fin 9 → Bool, Peter17.target (extendNine 0 y)=minorGraph y := by decide +kernel
  have project (y : Fin 9→Bool) :
      List.ofFn (fun i => Stat.val (List.ofFn y) (slot 0 10 i)) =
      List.ofFn (extendNine 0 y) ++ [extendNine 0 y 0 && extendNine 0 y 2] := rfl
  have real (y : Fin 9→Bool) : C.eval (List.ofFn (fun i => Stat.val (List.ofFn y) (slot 0 10 i))) = minorGraph y := by
    rw [project,ok,graph]
  obtain ⟨D,hD,hd,agree⟩ := marked_restriction C fan (slot 0 10) valid minorGraph real
    ⟨fun _ => false,fun _ => true,by decide⟩
  rw [touched_eq] at hd
  exact base ⟨D,hD,by omega,agree⟩

theorem whole (base : ¬HasCircuitSize 9 minorGraph 15) (C : Circuit) (fan:FanInTwo C)
    (size:C.size≤17) : ∃ x : Fin 10→Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) ≠ Peter17.target x := by
  by_contra! ok
  by_cases h : 2 ≤ C.gates.countP touch
  · exact cheaperMany base C fan size h ok
  · have floor : ordinary17 := by
      intro D legal hs
      by_contra! correct
      have hh := ordinary_lower base D legal (fun x => (correct x).trans (sameGraph x).symm)
      omega
    exact few floor C fan size (by omega) ok
end Reader7354

theorem numericLower : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 MonoPin7354.minorGraph 15 :=
  Numeric.mc Numeric.r8 Numeric.ur

namespace ConstGate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Ref := Bool ⊕ Nat

def evalRef (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr j => w.getD j false

def isFalseRef : Ref → Bool
  | .inl b => !b
  | .inr _ => false

def isTrueRef : Ref → Bool
  | .inl b => b
  | .inr _ => false

def liveRef : Ref → Option Nat
  | .inl _ => none
  | .inr i => some i

def shrink (op : GateOp) (xs : List Ref) : Gate :=
  match op with
  | .not => match xs.headD (.inl false) with
    | .inl b => ⟨if b then .or else .and, []⟩
    | .inr i => ⟨.not,[i]⟩
  | .or => if xs.any isTrueRef then ⟨.and, []⟩ else ⟨.or,xs.filterMap liveRef⟩
  | .and => if xs.any isFalseRef then ⟨.or, []⟩ else ⟨.and,xs.filterMap liveRef⟩
  | _ => ⟨.or,[]⟩

lemma wireAll (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).all id =
       (!xs.any isFalseRef && ((xs.filterMap liveRef).map fun j => w.getD j false).all id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isFalseRef,liveRef,ih]
    · simp [evalRef,isFalseRef,liveRef,ih,Bool.and_comm,Bool.and_left_comm]

lemma wireAny (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).any id =
       (xs.any isTrueRef || ((xs.filterMap liveRef).map fun j => w.getD j false).any id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isTrueRef,liveRef,ih]
    · simp [evalRef,isTrueRef,liveRef,ih,Bool.or_comm,Bool.or_left_comm]

lemma shrink_eval (w : List Bool) (o : GateOp) (xs : List Ref)
    (ho : o = .and ∨ o = .or ∨ o = .not) :
    (shrink o xs).op.eval ((shrink o xs).inputs.map fun j => w.getD j false) =
       o.eval (xs.map (evalRef w)) := by
  rcases ho with rfl|rfl|rfl
  · rw [show GateOp.and.eval _ = (xs.map (evalRef w)).all id by rfl, wireAll]
    cases hh : xs.any isFalseRef <;> simp [shrink,GateOp.eval,hh]
  · rw [show GateOp.or.eval _ = (xs.map (evalRef w)).any id by rfl, wireAny]
    cases hh : xs.any isTrueRef <;> simp [shrink,GateOp.eval,hh]
  · cases xs with
    | nil => rfl
    | cons x xs =>
      cases x with
      | inl b => cases b <;> rfl
      | inr i => rfl

lemma shrink_mono (o : GateOp) (xs : List Ref) (h : xs.length ≤ 2) :
    (shrink o xs).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      (shrink o xs).inputs.length ≤ 2 := by
  have h' : (xs.filterMap liveRef).length ≤ 2 := (List.length_filterMap_le liveRef xs).trans h
  cases o with
  | and => by_cases h : xs.any isFalseRef <;> simp [shrink,h,h']
  | or => by_cases h : xs.any isTrueRef <;> simp [shrink,h,h']
  | not =>
    cases xs with
    | nil => simp [shrink]
    | cons r xs =>
      cases r with
      | inl b => cases b <;> simp [shrink]
      | inr i => simp [shrink]
  | mod i => simp [shrink]
  | maj => simp [shrink]
end ConstGate

namespace FlexPins

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ConstGate (Ref evalRef shrink shrink_eval shrink_mono)

def source {n : ℕ} (r : Fin n → Ref) (m i : ℕ) : Ref :=
  if h : i<n then r ⟨i,h⟩ else .inr (m+(i-n))

def convert {n : ℕ} (r : Fin n → Ref) (m : ℕ) (g : Gate) : Gate :=
  shrink g.op (g.inputs.map (source r m))

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w

theorem value {n : ℕ} (r : Fin n → Ref) (old new : List Bool) (size : old.length=n)
    (good : ∀ i j, r i = .inr j → j < new.length)
    (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
    (bits : List Bool) (i : ℕ) :
    evalRef (new++bits) (source r new.length i) = (old++bits).getD i false := by
  unfold source
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (by omega)]
    have z := agree ⟨i,hi⟩
    cases q : r ⟨i,hi⟩ with
    | inl b => simpa [q,evalRef] using z
    | inr j =>
      change (new++bits).getD j false = _
      rw [List.getD_append _ _ _ _ (good _ _ q)]
      simpa [q, evalRef] using z
  next hi =>
    change (new++bits).getD (new.length+(i-n)) false = _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : new.length ≤ new.length+(i-n)),
      List.getElem?_append_right (by omega : old.length ≤ i),size,Nat.add_sub_cancel_left]

theorem replay {n : ℕ} (r : Fin n → Ref) (old new : List Bool) (size : old.length=n)
    (good : ∀ i j, r i = .inr j → j < new.length)
    (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
    (gs : List Gate) (ok : ∀ g ∈ gs, g.op=.and ∨ g.op=.or ∨ g.op=.not) (bits : List Bool) :
    ∃ z, run gs (old++bits) = old++z ∧ run (gs.map (convert r new.length)) (new++bits) = new++z := by
  induction gs generalizing bits with
  | nil => exact ⟨bits,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (old++bits).getD i false)
    obtain ⟨z,h1,h2⟩ := ih (fun a h => ok a (List.mem_cons_of_mem _ h)) (bits++[bit])
    refine ⟨z,?_,?_⟩
    · simpa [run,step,bit,List.append_assoc] using h1
    · have next : step (new++bits) (convert r new.length g) = new++(bits++[bit]) := by
        simp only [step,convert,shrink_eval _ _ _ (ok g List.mem_cons_self),List.map_map,Function.comp_def,
          value r old new size good agree bits,bit,List.append_assoc]
      change run (gs.map _) (step _ _) = _
      rw [next]
      exact h2

theorem output {n : ℕ} (r : Fin n → Ref) (old new : List Bool) (size : old.length=n)
    (good : ∀ i j, r i = .inr j → j < new.length)
    (agree : ∀ i : Fin n, evalRef new (r i) = old.getD i.val false)
    (C : Circuit) (fan : FanInTwo C) :
    evalRef (run (C.gates.map (convert r new.length)) new) (source r new.length C.output) =
      C.eval old := by
  obtain ⟨z,h1,h2⟩ := replay r old new size good agree C.gates
    (fun g h => by simpa using (fan _ h).1) []
  simp only [List.append_nil] at h1 h2
  change _ = (run C.gates old).getD C.output false
  rw [h1,h2,value r old new size good agree]

theorem fan {n : ℕ} (r : Fin n → Ref) (m o : ℕ) (C : Circuit) (hf : FanInTwo C) :
    FanInTwo ⟨C.gates.map (convert r m),o⟩ := by
  intro g hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  apply shrink_mono
  simpa using (hf _ hq).2

end FlexPins

namespace Adapter17511
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ConstGate (Ref evalRef)

def z (x : Fin 10 → Bool) := x 0 && x 2
def src (f : Fin 10 → Fin 10) (i : Fin 12) : Ref :=
  if hi : i.val < 10 then .inr (f ⟨i.val,hi⟩).val else if i.val=10 then .inr 10 else .inl true
def old (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) := List.ofFn (x ∘ f) ++ [z x,true]
def new (x : Fin 10 → Bool) := List.ofFn x ++ [z x]
def graph (x : Fin 10 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
    (4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any fun e => x e.1 && x e.2

theorem same (x : Fin 10 → Bool) : graph x = Peter17.target x := by
  simp [graph,Peter17.target,Bool.or_assoc]

theorem valid (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) (i : Fin 12) (j : ℕ) (h : src f i = .inr j) :
    j < (new x).length := by
  unfold src at h
  split at h
  next hi => cases h; have := (f ⟨i.val,hi⟩).isLt; simp [new]; omega
  next => split at h <;> cases h <;> simp [new]

theorem agree (f : Fin 10 → Fin 10) (x : Fin 10 → Bool) (i : Fin 12) :
    evalRef (new x) (src f i) = (old f x).getD i.val false := by
  unfold src
  split
  next hi =>
    change (List.ofFn x++[z x]).getD (f ⟨i.val,hi⟩).val false =
      (List.ofFn (x ∘ f)++[z x,true]).getD i.val false
    rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,hi,↓reduceDIte,Option.getD_some,
      Function.comp_apply]
  next hi =>
    have both : i=10 ∨ i=11 := by omega
    rcases both with rfl | rfl <;> simp [evalRef,old,new,List.getD_eq_getElem?_getD,
      List.getElem?_append_right]

theorem exclude (C : Circuit) (f : Fin 10 → Fin 10) (hf : FanInTwo C) (size : C.size ≤ 17) :
    ∃ x : Fin 10 → Bool, C.eval (old f x) ≠ graph x := by
  by_contra! perfect
  let gs := C.gates.map (FlexPins.convert (src f) 11)
  have ev (x : Fin 10 → Bool) :
      evalRef (FlexPins.run gs (new x)) (FlexPins.source (src f) 11 C.output) = C.eval (old f x) := by
    have h := FlexPins.output (src f) (old f x) (new x) (by simp [old]) (valid f x) (agree f x) C hf
    simpa only [new,List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using h
  cases ht : FlexPins.source (src f) 11 C.output with
  | inl b =>
    have cst (x : Fin 10 → Bool) : b = graph x := by
      have h := ev x
      rw [ht] at h
      exact h.trans (perfect x)
    have off := cst (fun _ => false)
    have on := cst (fun j => decide (j.val ≤ 1))
    have h0 : b = false := off
    have h1 : b = true := on
    exact Bool.noConfusion (h0.symm.trans h1)
  | inr i =>
    let D : Circuit := ⟨gs,i⟩
    have fd : FanInTwo D := FlexPins.fan (src f) 11 i C hf
    have bd : D.size ≤ 17 := by simpa [D,gs,Circuit.size] using size
    obtain ⟨x,bad⟩ := Reader7354.whole numericLower D fd bd
    apply bad
    have h := ev x
    rw [ht] at h
    exact (h.trans (perfect x)).trans (same x)

end Adapter17511
end PEqualNP.Outside.L_meta_17511
open PEqualNP.Outside.L_meta_17511
theorem PEqualNP.Outside.L_meta_17511 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)), Bool.true]) ≠ [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))].any fun (x6 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x5 x6.1 && x5 x6.2 := by
  intro C f fan size
  exact Adapter17511.exclude C f fan size
