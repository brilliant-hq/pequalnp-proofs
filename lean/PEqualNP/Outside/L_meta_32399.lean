import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32399.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
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

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 256
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
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
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
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
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d ||
    if u then
      let c := d ^^^ m
      pool.any (fun v => v == m || v == c)
    else
      pool.any (fun v => v == m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem masked_idem (d a : Sig) : masked d (masked d a) = masked d a := by
  apply bit_ext; intro i; simp [bit, masked]

theorem masked_xor_neg (d a : Sig) : d ^^^ masked d a = masked d (neg a) := by
  apply bit_ext; intro i
  simp only [bit, masked, neg, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
  cases d.getLsbD i.val <;> cases a.getLsbD i.val <;> rfl

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  unfold availableB at check
  dsimp only at check
  simp only [Bool.or_eq_true, beq_iff_eq] at check
  rcases check with (hz | ho) | hrest
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · cases u with
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.any_eq_true, beq_iff_eq] at hrest
      obtain ⟨v, hv, rfl⟩ := hrest
      exact masked_eq dom (masked_idem d a) ▸ supplyB _ hv
    | true =>
      simp only [ite_true, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at hrest
      obtain ⟨v, hv, rfl | rfl⟩ := hrest
      · exact masked_eq dom (masked_idem d a) ▸ supplyB _ hv
      · have h := avail_inv rfl (masked_eq dom ((congrArg (masked d) (masked_xor_neg d a)).trans (masked_idem d (neg a))) ▸ supplyB _ hv)
        rw [obs_neg] at h
        have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
          funext r; simp [inv, restrictRows]
        rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def fixRows (z o : Nat) : List Move :=
  (List.range 8).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 256 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 256 d)

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let rhs := c.bound + (z :: rest).countP (isMaskedConstant c.domain)
  if k + c.paid < rhs then
    let extra := !(availableB u c.domain c.wires z)
    ((k + c.paid + extra.toNat < rhs) &&
      rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
  else false

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  unfold scalarPoolCut at cut
  dsimp only at cut
  split at cut
  · let extra := !(availableB u c.domain c.wires (choiceVal op))
    apply valid_exclude valid k rest op extra _ _ _ nd
    · simp only [Bool.and_eq_true, List.all_eq_true] at cut
      exact cut.1.2
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at cut
      cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at cut
      exact cut.1.1
  · contradiction

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 8 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem input_coords : ∀ (j : Fin 8) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 8) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 8 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<8 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 1000000000000000003
  ((n*n % 1000000000000000003)*(n+7)+971*n) % 1000000000000000003
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  pools.any (fun p => scalarPoolCut u p k rest op) ||
    let ws := choiceVal op :: rest
    (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨p, hp, ok⟩ | ⟨xs, hx, ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<8
  · let i : Fin 8 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 256 ≤ 2^j := by
      change 2^8 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

end PEqualNP.Outside.L_meta_32399.Model

namespace PEqualNP.Outside.L_meta_32399
open PEqualNP.Outside.L_meta_32399.Model
open PEqualNP.CircuitLowerBounds

def decodeSigs (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) zero
    let b := ws.getD ((bits >>> 5) &&& 31) zero
    decodeSigs k (bits >>> 12) (ws ++ [bin ((bits >>> 10) &&& 3) a b])

theorem decodeSigs_eq (n bits : Nat) (ws : List Decor) :
    decodeSigs n bits (ws.map Prod.fst) = (decodeBank n bits ws).map Prod.fst := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs, decodeBank]
    have hget (j : Nat) : (ws.map Prod.fst).getD j zero = (ws.getD j defaultDecor).1 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ws[j]? <;> rfl
    rw [hget, hget]
    have h := ih (bits >>> 12) (ws ++ [dbin ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) defaultDecor) (ws.getD ((bits >>> 5) &&& 31) defaultDecor)])
    rw [List.map_append, List.map_singleton] at h
    exact h

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons a ws ih =>
    unfold selectLive
    split <;> simp [ih]

def decodeBankChoices (n : Nat) (bits : Nat) (ws : List Decor) : List Decor × List Choice :=
  match n with
  | 0 => (ws, [])
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    let op := (bits >>> 10) &&& 3
    let res := decodeBankChoices k (bits >>> 12) (ws ++ [dbin op a b])
    (res.1, (op, a.1, b.1) :: res.2)

theorem decodeBankChoices_fst (n bits : Nat) (ws : List Decor) :
    (decodeBankChoices n bits ws).1 = decodeBank n bits ws := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeBankChoices, decodeBank]
    exact ih _ _

theorem poolSupply_masked {u} {f : Row → Row} {d : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (hs : poolSupply u f bank pool) :
    poolSupply u f bank (pool.map (masked d)) := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
  exact masked_eq dom (masked_idem d v).symm ▸ hs v hv

def autoPoolStep (u : Bool) (d : Sig) (budget : Nat) (paid : Nat) (mpool : List Sig) : List Choice → Nat × List Sig
  | [] => (paid, mpool)
  | c :: cs =>
    if paid < budget then
      if availableB u d mpool (choiceVal c) then autoPoolStep u d budget paid mpool cs
      else if choiceOK u d mpool c then autoPoolStep u d budget (paid + 1) (masked d (choiceVal c) :: mpool) cs
      else (paid, mpool)
    else (paid, mpool)

theorem autoPoolStep_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank budget paid mpool} (hp : Reach u roots paid bank) (hs : poolSupply u f bank mpool)
    (cs : List Choice) :
    ∃ next, Reach u roots (autoPoolStep u d budget paid mpool cs).1 next ∧
      poolSupply u f next (autoPoolStep u d budget paid mpool cs).2 := by
  induction cs generalizing bank paid mpool with
  | nil => exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [autoPoolStep]
    split
    · split
      · exact ih hp hs
      · split
        next hok =>
          obtain ⟨next, hr, hs'⟩ := pay_choice dom hp hs c hok
          have hs'' : poolSupply u f next (masked d (choiceVal c) :: mpool) := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | hm
            · exact masked_eq dom (masked_idem d (choiceVal c)).symm ▸ hs' _ (by simp)
            · exact hs' _ (List.mem_cons_of_mem _ hm)
          exact ih hr hs''
        next => exact ⟨bank, hp, hs⟩
    · exact ⟨bank, hp, hs⟩

def autoBoundPool (u : Bool) (raw : List Sig) (cs : List Choice) (budget : Nat) (spec : Sig × Nat) : BoundPool :=
  let res := autoPoolStep u spec.1 budget 0 (raw.map (masked spec.1)) cs
  ⟨spec.1, spec.2, res.1, res.2⟩

theorem autoBoundPool_valid {u raw T cs budget spec} (slice : Slice u raw T spec.1 spec.2) :
    ValidPool u raw T (autoBoundPool u raw cs budget spec) := by
  obtain ⟨f, roots, dom, base, nc, lo⟩ := slice
  obtain ⟨bank, hr, hs⟩ := autoPoolStep_sound dom (Reach.start (roots := roots.map observe)) (poolSupply_masked dom base) cs
  exact ⟨f, roots, bank, dom, nc, lo, hr, hs, trivial⟩

def activePools (u : Bool) (raw : List Sig) (cs : List Choice) (k : Nat) (vs : List Sig)
    (specs : List (Sig × Nat)) : List BoundPool :=
  specs.filterMap fun sp =>
    if k < sp.2 + vs.length + 2 then
      let lim := sp.2 + vs.countP (isMaskedConstant sp.1) + 2
      if k < lim then
        let bp := autoBoundPool u raw cs (lim - k) sp
        if k + bp.paid < lim then some bp else none
      else none
    else none

theorem activePools_valid {u raw T cs k vs specs}
    (h : ∀ sp ∈ specs, Slice u raw T sp.1 sp.2) :
    ∀ p ∈ activePools u raw cs k vs specs, ValidPool u raw T p := by
  intro p hp
  obtain ⟨sp, hsp, hsome⟩ := List.mem_filterMap.mp hp
  simp only at hsome
  split at hsome
  · split at hsome
    · split at hsome
      · cases hsome
        exact autoBoundPool_valid (h sp hsp)
      · contradiction
    · contradiction
  · contradiction

abbrev Atlas := Nat × List Decor × Sig × List (Sig × Nat) × List Move ×
  (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def slices (g : Atlas) := g.2.2.2.1
def mirror (g : Atlas) := g.2.2.2.2.1
def count (g : Atlas) := g.2.2.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.2

def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g - k
  let v := record g k i
  selectLive (v >>> (12 * d)) (decodeBank d v (first g))
def roots (g : Atlas) := (first g).map Prod.fst
def vals (g : Atlas) (k i : Nat) : List Sig :=
  let d := top g - k
  let v := record g k i
  selectLive (v >>> (12 * d)) (decodeSigs d v (roots g))

theorem vals_eq (g : Atlas) (k i : Nat) : vals g k i = (items g k i).map Prod.fst := by
  simp only [vals, items, roots, decodeSigs_eq, selectLive_map]

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) (mirror g) then ws.map (movedWord (mirror g).reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let d := top g - k
  let v := record g k i
  let dc := decodeBankChoices d v (first g)
  let ws := selectLive (v >>> (12 * d)) dc.1
  let vs := ws.map Prod.fst
  let pools := activePools true (roots g) dc.2 k vs (slices g)
  decide vs.Nodup && !vs.contains (target g) &&
    testAll (k, ws.length, ws, preCov true ws, pools, links g (k - 1)) ws

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ sp ∈ slices g, Slice true (roots g) (target g) sp.1 sp.2

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    rw [vals_eq]
    have h := good k (by omega) i hi
    simp only [checkRow, decodeBankChoices_fst, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    by_cases hk : k = 0
    · subst k
      intro n cap run
      have : n = 0 := by omega
      subst n
      have hm : target g ∈ ((items g 0 i).map Prod.fst).toFinset := run.1 ▸ Finset.mem_singleton_self _
      exact h.1.2 (List.mem_toFinset.mp hm)
    apply node_sound (raw := roots g) ready.1 _ h.1.1 h.1.2 (activePools_valid ready.2.2) _ h.2
    · intro a ha
      exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
    · intro tag xs hx
      simp only [links] at hx
      split at hx
      next le =>
        obtain rfl := List.mem_singleton.mp hx
        exact variant_ok (ih (k - 1) (by omega) (fun l hl => good l (by omega)) _ le) _
      next => simp at hx

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start + n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n = true) (i : Nat)
    (lo : start ≤ i) (hi : i < start + n) : test i = true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment, Bool.and_eq_true] at h
    by_cases eq : i = start + n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n = true) (i : Nat)
    (lo : a ≤ i) (hi : i < a + n) : checkRow g k i = true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start + n → checkRow g k i = true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a + m) n) :
    Interval g k a (m + n) := by
  intro i lo hi
  by_cases mid : i < a + m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true

theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs = true) (names : xs.map Prod.fst = roots g) :
    Lower true (roots g) (target g) (top g + 1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

end PEqualNP.Outside.L_meta_32399

namespace PEqualNP.Outside.L_meta_32399
open PEqualNP.Outside.L_meta_32399.Model
open PEqualNP.CircuitLowerBounds

def u0T : Sig := 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
def u1T : Sig := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def u2T : Sig := 0xffffffffffff0000ffffffffffff0000ffff000000000000ffff000000000000
def u3T : Sig := 0xffffffffffff0000ffffffffffff0000ffff000000000000ffff000000000000
def u4T : Sig := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def u5T : Sig := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def u6T : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def u7T : Sig := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def u8T : Sig := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def u9T : Sig := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def u10T : Sig := 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000
def u11T : Sig := 0xffffffffffffffffffffffffffff0000ffffffffffffffffffff000000000000
def u12T : Sig := 0xffffffffffffffffffffffffffff0000ffff000000000000ffff000000000000
def u13T : Sig := 0xffffffffffffffffffffffffff00ff00ff00ff00ff00ff000000000000000000
def u14T : Sig := 0xffffffffffffffffffffffff00000000f0f0f0f0f0f0f0f00000000000000000
def u15T : Sig := 0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccc00000000
def u16T : Sig := 0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccc00000000
def u17T : Sig := 0xffffffffffffffffffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def u18T : Sig := 0xffffffffffffffffffffff00ffffff00ff00ff00ff00ff000000000000000000
def u19T : Sig := 0xffffffffffffffffffff0000ffff0000f0f0f0f0f0f0f0f00000000000000000
def u20T : Sig := 0xffffffffffffffffff00ff00ff00ff00fff0fff0fff0fff00000000000000000
def u21T : Sig := 0xffffffffffffffffffccffccffccffccffccffccffccffcc0000000000000000
def u22T : Sig := 0xffffffffffffffffffaaffaaffaaffaaff00ff00ff00ff00aa00aa00aa00aa00
def u23T : Sig := 0xffffffffffffffffccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def u24T : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaf0f0f0f0f0f0f0f00000000000000000
def u25T : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeeecccccccccccccccc0000000000000000
def u26T : Sig := 0xffffffffffffff00ffffffffffffff00ffff000000000000ffff000000000000
def u27T : Sig := 0xffffffffffffccccffffffffffffccccffffcccccccc0000ffffcccccccc0000
def u28T : Sig := 0xffffffffffffccccffffffffffffccccffffcccccccc0000ffffcccccccc0000
def u29T : Sig := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000ffffaaaaaaaa0000
def u30T : Sig := 0xffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000ffffaaaaaaaa0000
def u31T : Sig := 0xffffffffffccffccffffffffffccffcccccccccc00000000cccccccc00000000
def u32T : Sig := 0xffffffffffccffccffffffffffccffcccccccccc00000000cccccccc00000000
def u33T : Sig := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def u34T : Sig := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def u35T : Sig := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def u36T : Sig := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def u37T : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def u38T : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def u39T : Sig := 0xffffffffffffffffffffcccccccc0000ffffffffffffffffffffcccccccc0000
def u40T : Sig := 0xffffccccccccccccffffcccccccc0000ffffccccccccccccffffcccccccc0000
def u41T : Sig := 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000
def u42T : Sig := 0xffccffccffccffcccccccccc00000000ffccffccffccffcccccccccc00000000
def u43T : Sig := 0xffaaffaaff00ff00aaaaaaaaaa00aa00ffaaffaaff00ff00aaaaaaaaaa00aa00
def u44T : Sig := 0xfcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000
def u45T : Sig := 0xeeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000
def u46T : Sig := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000
def u47T : Sig := 0xffaaff00ffaaff00aaaaaa00aaaaaa00ffaaff00ffaaff00aaaaaa00aaaaaa00
def u48T : Sig := 0xfcfcfcfcfcfcfcfccccc0000cccc0000fcfcfcfcfcfcfcfccccc0000cccc0000
def u49T : Sig := 0xeeeecccceeeecccceeee0000eeee0000eeeecccceeeecccceeee0000eeee0000
def u50T : Sig := 0xffccffccffccffccaa00aa00aa00aa00ffccffccffccffccaa00aa00aa00aa00
def u51T : Sig := 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000
def u52T : Sig := 0xffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00
def u53T : Sig := 0xffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00
def u54T : Sig := 0xffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeecccc
def u55T : Sig := 0xffffeeeeeeeeaaaaffffeeeeeeeeaaaaffffeeeeeeeeaaaaffffeeeeeeeeaaaa
def u56T : Sig := 0xffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000
def u57T : Sig := 0xeeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00eeeeeeeeaa00aa00
def u58T : Sig := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u59T : Sig := 0xffffffffffffffffffffffffffffff00ffffffffffffffffffff000000000000
def u60T : Sig := 0xffffffffffffffffffffffffffffff00ffffff00ff00ff00ffff000000000000
def u61T : Sig := 0xffffffffffffffffffffffffffff0000fffff0f0f0f0f0f0ffff000000000000
def u62T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc0000
def u63T : Sig := 0xffffffffffffffffffffffffffffccccffffffffffffffffffffcccccccc0000
def u64T : Sig := 0xffffffffffffffffffffffffffffccccffffccccccccccccffffcccccccc0000
def u65T : Sig := 0xffffffffffffffffffffffffffffaaaaffffffffffffffffffffaaaaaaaa0000
def u66T : Sig := 0xffffffffffffffffffffffffffffaaaaffffaaaaaaaa0000ffffaaaaaaaa0000
def u67T : Sig := 0xffffffffffffffffffffffffff00ff00fff0fff0fff0fff00000000000000000
def u68T : Sig := 0xffffffffffffffffffffffffffccffccffffffffffffffffcccccccc00000000
def u69T : Sig := 0xffffffffffffffffffffffffffccffccffccffccffccffcccccccccc00000000
def u70T : Sig := 0xffffffffffffffffffffffffffaaffaaffffffffffffffffaaaaaaaaaa00aa00
def u71T : Sig := 0xffffffffffffffffffffffffffaaffaaffaaffaaff00ff00aaaaaaaaaa00aa00
def u72T : Sig := 0xffffffffffffffffffffffffccccccccfcfcfcfcfcfcfcfccccccccc00000000
def u73T : Sig := 0xffffffffffffffffffffffffaaaaaaaafafafafaf0f0f0f0aaaaaaaa00000000
def u74T : Sig := 0xffffffffffffffffffffffffeeeeeeeeeeeeeeeecccccccceeeeeeee00000000
def u75T : Sig := 0xffffffffffffffffffffff00ffffff00fff0fff0fff0fff00000000000000000
def u76T : Sig := 0xffffffffffffffffffffffccffffffccffccffccffccffcccccc0000cccc0000
def u77T : Sig := 0xffffffffffffffffffffffaaffffffaaffaaff00ffaaff00aaaaaa00aaaaaa00
def u78T : Sig := 0xffffffffffffffffffffccccffffccccfcfcfcfcfcfcfcfccccc0000cccc0000
def u79T : Sig := 0xffffffffffffffffffffaaaaffffaaaafafaf0f0fafaf0f0aaaa0000aaaa0000
def u80T : Sig := 0xffffffffffffffffffffeeeeffffeeeeeeeecccceeeecccceeee0000eeee0000
def u81T : Sig := 0xffffffffffffffffffccffccffccffccfffcfffcfffcfffc0000000000000000
def u82T : Sig := 0xffffffffffffffffffaaffaaffaaffaafff0fff0fff0fff0aa00aa00aa00aa00
def u83T : Sig := 0xffffffffffffffffffeeffeeffeeffeeffccffccffccffccaa00aa00aa00aa00
def u84T : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeeefcfcfcfcfcfcfcfc0000000000000000
def u85T : Sig := 0xffffffffffffff00ffffffffffffff00ffff000000000000ffff000000000000
def u86T : Sig := 0xffffffffffffffccffffffffffffffccffffcccccccc0000ffffcccccccc0000
def u87T : Sig := 0xffffffffffffffffffffffffffffffffffffffaaffaaff00ffffffaaffaaff00
def u88T : Sig := 0xffffffffffffffaaffffffffffffffaaffffaaaaaaaaaa00ffffaaaaaaaaaa00
def u89T : Sig := 0xffffffffffffccccffffffffffffccccffffcccccccc0000ffffcccccccc0000
def u90T : Sig := 0xfffffffffffffffffffffffffffffffffffffafafafaf0f0fffffafafafaf0f0
def u91T : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeeeeeccccffffeeeeeeeecccc
def u92T : Sig := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeeeee0000ffffeeeeeeee0000
def u93T : Sig := 0xffffffffffffeeeeffffffffffffeeeeffffeeeeeeee0000ffffeeeeeeee0000
def u94T : Sig := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def u95T : Sig := 0xffffffffffeeffeeffffffffffeeffeeeeeeeeeeaa00aa00eeeeeeeeaa00aa00
def u96T : Sig := 0xffffffffffeeffeeffffffffffeeffeeeeeeeeeeaa00aa00eeeeeeeeaa00aa00
def u97T : Sig := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def u98T : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000eeee0000eeee0000
def u99T : Sig := 0xffffffccffccffccffffcccccccc0000ffffffccffccffccffffcccccccc0000
def u100T : Sig := 0xffffffffffffffffffffaaaaaaaaaa00ffffffffffffffffffffaaaaaaaaaa00
def u101T : Sig := 0xffffffaaffaaff00ffffaaaaaaaaaa00ffffffaaffaaff00ffffaaaaaaaaaa00
def u102T : Sig := 0xfffffcfcfcfcfcfcffffcccccccc0000fffffcfcfcfcfcfcffffcccccccc0000
def u103T : Sig := 0xfffffafafafaf0f0ffffaaaaaaaa0000fffffafafafaf0f0ffffaaaaaaaa0000
def u104T : Sig := 0xffffffffffffffffffffeeeeeeeeaaaaffffffffffffffffffffeeeeeeeeaaaa
def u105T : Sig := 0xffffffffffffffffffffeeeeeeee0000ffffffffffffffffffffeeeeeeee0000
def u106T : Sig := 0xffffeeeeeeeeccccffffeeeeeeee0000ffffeeeeeeeeccccffffeeeeeeee0000
def u107T : Sig := 0xfffcfffcfffcfffccccccccc00000000fffcfffcfffcfffccccccccc00000000
def u108T : Sig := 0xfffafffafff0fff0aaaaaaaaaa00aa00fffafffafff0fff0aaaaaaaaaa00aa00
def u109T : Sig := 0xffeeffeeffccffcceeeeeeeeaa00aa00ffeeffeeffccffcceeeeeeeeaa00aa00
def u110T : Sig := 0xfefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000
def u111T : Sig := 0xfffafff0fffafff0aaaaaa00aaaaaa00fffafff0fffafff0aaaaaa00aaaaaa00
def u112T : Sig := 0xffeeffccffeeffcceeeeaa00eeeeaa00ffeeffccffeeffcceeeeaa00eeeeaa00
def u113T : Sig := 0xfefefcfcfefefcfceeee0000eeee0000fefefcfcfefefcfceeee0000eeee0000
def u114T : Sig := 0xfffffffafffafff0fffffffafffafff0fffffffafffafff0fffffffafffafff0
def u115T : Sig := 0xffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00ffffaaaaaaaaaa00
def u116T : Sig := 0xffffffeeffeeffccffffffeeffeeffccffffffeeffeeffccffffffeeffeeffcc
def u117T : Sig := 0xffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00
def u118T : Sig := 0xffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00
def u119T : Sig := 0xfffffefefefefcfcfffffefefefefcfcfffffefefefefcfcfffffefefefefcfc
def u120T : Sig := 0xffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000ffffeeeeeeee0000
def u121T : Sig := 0xffffffffffffffffffffffffffffff00fffffff0fff0fff0ffff000000000000
def u122T : Sig := 0xffffffffffffffffffffffffffffffccffffffffffffffffffffcccccccc0000
def u123T : Sig := 0xffffffffffffffffffffffffffffffccffffffccffccffccffffcccccccc0000
def u124T : Sig := 0xffffffffffffffffffffffffffffffaaffffffffffffffffffffaaaaaaaaaa00
def u125T : Sig := 0xffffffffffffffffffffffffffffffaaffffffaaffaaff00ffffaaaaaaaaaa00
def u126T : Sig := 0xffffffffffffffffffffffffffffccccfffffcfcfcfcfcfcffffcccccccc0000
def u127T : Sig := 0xffffffffffffffffffffffffffffaaaafffffafafafaf0f0ffffaaaaaaaa0000
def u128T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeaaaa
def u129T : Sig := 0xffffffffffffffffffffffffffffeeeeffffffffffffffffffffeeeeeeee0000
def u130T : Sig := 0xffffffffffffffffffffffffffffeeeeffffeeeeeeeeccccffffeeeeeeee0000
def u131T : Sig := 0xffffffffffffffffffffffffffccffccfffcfffcfffcfffccccccccc00000000
def u132T : Sig := 0xffffffffffffffffffffffffffaaffaafffafffafff0fff0aaaaaaaaaa00aa00
def u133T : Sig := 0xffffffffffffffffffffffffffeeffeeffffffffffffffffeeeeeeeeaa00aa00
def u134T : Sig := 0xffffffffffffffffffffffffffeeffeeffeeffeeffccffcceeeeeeeeaa00aa00
def u135T : Sig := 0xffffffffffffffffffffffffeeeeeeeefefefefefcfcfcfceeeeeeee00000000
def u136T : Sig := 0xffffffffffffffffffffffccffffffccfffcfffcfffcfffccccc0000cccc0000
def u137T : Sig := 0xffffffffffffffffffffffaaffffffaafffafff0fffafff0aaaaaa00aaaaaa00
def u138T : Sig := 0xffffffffffffffffffffffeeffffffeeffffffffffffffffeeeeaa00eeeeaa00
def u139T : Sig := 0xffffffffffffffffffffffeeffffffeeffeeffccffeeffcceeeeaa00eeeeaa00
def u140T : Sig := 0xffffffffffffffffffffeeeeffffeeeefefefcfcfefefcfceeee0000eeee0000
def u141T : Sig := 0xffffffffffffffffffeeffeeffeeffeefffcfffcfffcfffcaa00aa00aa00aa00
def u142T : Sig := 0xffffffffffffffccffffffffffffffccffffcccccccc0000ffffcccccccc0000
def u143T : Sig := 0xfffffffffffffffffffffffffffffffffffffffafffafff0fffffffafffafff0
def u144T : Sig := 0xffffffffffffffffffffffffffffffffffffffeeffeeffccffffffeeffeeffcc
def u145T : Sig := 0xffffffffffffffeeffffffffffffffeeffffeeeeeeeeaa00ffffeeeeeeeeaa00
def u146T : Sig := 0xffffffffffffffeeffffffffffffffeeffffeeeeeeeeaa00ffffeeeeeeeeaa00
def u147T : Sig := 0xfffffffffffffffffffffffffffffffffffffefefefefcfcfffffefefefefcfc
def u148T : Sig := 0xffffffffffeeffeeffffffffffeeffeeeeeeeeeeaa00aa00eeeeeeeeaa00aa00
def u149T : Sig := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u150T : Sig := 0xfffffffcfffcfffcffffcccccccc0000fffffffcfffcfffcffffcccccccc0000
def u151T : Sig := 0xfffffffafffafff0ffffaaaaaaaaaa00fffffffafffafff0ffffaaaaaaaaaa00
def u152T : Sig := 0xffffffffffffffffffffeeeeeeeeaa00ffffffffffffffffffffeeeeeeeeaa00
def u153T : Sig := 0xffffffeeffeeffccffffeeeeeeeeaa00ffffffeeffeeffccffffeeeeeeeeaa00
def u154T : Sig := 0xfffffefefefefcfcffffeeeeeeee0000fffffefefefefcfcffffeeeeeeee0000
def u155T : Sig := 0xfffefffefffcfffceeeeeeeeaa00aa00fffefffefffcfffceeeeeeeeaa00aa00
def u156T : Sig := 0xfffefffcfffefffceeeeaa00eeeeaa00fffefffcfffefffceeeeaa00eeeeaa00
def u157T : Sig := 0xfffffffefffefffcfffffffefffefffcfffffffefffefffcfffffffefffefffc
def u158T : Sig := 0xffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00ffffeeeeeeeeaa00
def u159T : Sig := 0xffffffffffffffffffffffffffffffccfffffffcfffcfffcffffcccccccc0000
def u160T : Sig := 0xffffffffffffffffffffffffffffffaafffffffafffafff0ffffaaaaaaaaaa00
def u161T : Sig := 0xffffffffffffffffffffffffffffffeeffffffffffffffffffffeeeeeeeeaa00
def u162T : Sig := 0xffffffffffffffffffffffffffffffeeffffffeeffeeffccffffeeeeeeeeaa00
def u163T : Sig := 0xffffffffffffffffffffffffffffeeeefffffefefefefcfcffffeeeeeeee0000
def u164T : Sig := 0xffffffffffffffffffffffffffeeffeefffefffefffcfffceeeeeeeeaa00aa00
def u165T : Sig := 0xffffffffffffffffffffffeeffffffeefffefffcfffefffceeeeaa00eeeeaa00
def u166T : Sig := 0xfffffffffffffffffffffffffffffffffffffffefffefffcfffffffefffefffc
def u167T : Sig := 0xfffffffefffefffcffffeeeeeeeeaa00fffffffefffefffcffffeeeeeeeeaa00
def u168T : Sig := 0xffffffffffffffffffffffffffffffeefffffffefffefffcffffeeeeeeeeaa00

def u0K3 : Nat → Nat
  | 0 => 0x287
  | _ => 0
def u0N : Nat → Nat
  | 3 => 1
  | _ => 0
def u0R : Nat → Nat → Nat
  | 3, i => packedAt u0K3 (i * 3) 3
  | _, _ => 0
def u0I : Nat → Nat → Nat
  | 3, h => packedAt u0K3 (4 + ((h / 1 + packedAt u0K3 (3 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u0Pos : Nat → Bits
  | 3 => 0xfffffffffffffffffffffffffffffffffffecf
  | 6 => 0xffffffffffffffffffffffffffffffffffff73
  | 7 => 0x1bc
  | _ => 0
def u0Neg : Nat → Bits
  | 3 => 0xffffffffffffffffffffffffffffffffffff05
  | 6 => 0x92
  | 7 => 0x68
  | _ => 0
def u0Slices : List (Sig × Nat) := []
def u0Atlas : Atlas := ⟨3, rawDecor 200 u0Pos u0Neg, u0T, u0Slices, [swapRows 118], u0N, u0R, u0I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u0_3_0 : Interval u0Atlas 3 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u0_3 : Interval u0Atlas 3 0 1 := blk_u0_3_0
theorem cert_u0 : Complete u0Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u0_3 i (by omega) hi
theorem b_u0 : Lower true (vars 200) u0T 4 := by
  have ready : Ready u0Atlas (asRow u0Pos) (asRow u0Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u0Atlas, u0Slices, List.not_mem_nil] at hsp
  exact frozen ready cert_u0 (by decide +kernel) (by decide) [(inputs.getD 3 zero,64,72),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u1 : Lower true (vars 194) u1T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u2 : Lower true (vars 176) u2T 4 :=
  lower_map (ms := [swapRows 67,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u3 : Lower true (vars 176) u3T 4 :=
  lower_map (ms := [swapRows 67,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u4 : Lower true (vars 162) u4T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u5 : Lower true (vars 162) u5T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u6 : Lower true (vars 161) u6T 4 :=
  lower_map (ms := [swapRows 48,swapRows 49,swapRows 50,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u7 : Lower true (vars 146) u7T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u8 : Lower true (vars 50) u8T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u9 : Lower true (vars 50) u9T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u10 : Lower true (vars 49) u10T 4 :=
  lower_map (ms := [swapRows 48,swapRows 49,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u11 : Lower true (vars 240) u11T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 240) (T := u11T) (xs := [(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u2
  have hc : (([(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u12 : Lower true (vars 240) u12T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 240) (T := u12T) (xs := [(inputs.getD 6 zero,128,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u3
  have hc : (([(inputs.getD 6 zero,128,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u13 : Lower true (vars 232) u13T 5 :=
  lower_map (ms := [swapRows 67,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
def u14K3 : Nat → Nat
  | 0 => 0x44f
  | _ => 0
def u14N : Nat → Nat
  | 3 => 1
  | _ => 0
def u14R : Nat → Nat → Nat
  | 3, i => packedAt u14K3 (i * 4) 4
  | _, _ => 0
def u14I : Nat → Nat → Nat
  | 3, h => packedAt u14K3 (5 + ((h / 1 + packedAt u14K3 (4 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u14Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffe074cf
  | 5 => 0x388fc
  | 6 => 0xfffffffffffffffffffffffffffffffffc7f0f
  | 7 => 0x1f8ff0
  | _ => 0
def u14Neg : Nat → Bits
  | 2 => 0xfffffffffffffffffffffffffffffffffad4c5
  | 5 => 0x15b85c
  | 6 => 0x5290a
  | 7 => 0xa46a0
  | _ => 0
def u14Slices : List (Sig × Nat) := []
def u14Atlas : Atlas := ⟨3, rawDecor 228 u14Pos u14Neg, u14T, u14Slices, [swapRows 82,swapRows 118], u14N, u14R, u14I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u14_3_0 : Interval u14Atlas 3 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u14_3 : Interval u14Atlas 3 0 1 := blk_u14_3_0
theorem cert_u14 : Complete u14Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u14_3 i (by omega) hi
theorem b_u14 : Lower true (vars 228) u14T 4 := by
  have ready : Ready u14Atlas (asRow u14Pos) (asRow u14Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u14Atlas, u14Slices, List.not_mem_nil] at hsp
  exact frozen ready cert_u14 (by decide +kernel) (by decide) [(inputs.getD 2 zero,64,68),(inputs.getD 5 zero,128,160),(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,32,160)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u15 : Lower true (vars 226) u15T 5 :=
  lower_map (ms := [swapRows 65,swapRows 66,swapRows 67]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u16 : Lower true (vars 226) u16T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 32 0) (raw := vars 226) (T := u16T) (xs := [(inputs.getD 5 zero,2,34)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u1
  have hc : (([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u17 : Lower true (vars 225) u17T 5 :=
  lower_map (ms := [swapRows 64,swapRows 65,swapRows 66,swapRows 67]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u18 : Lower true (vars 216) u18T 5 :=
  lower_map (ms := [swapRows 67,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u19 : Lower true (vars 212) u19T 4 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u20 : Lower true (vars 204) u20T 5 :=
  lower_map (ms := [swapRows 98,swapRows 67,swapRows 100,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u21 : Lower true (vars 202) u21T 5 :=
  lower_map (ms := [swapRows 81,swapRows 99,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u22 : Lower true (vars 201) u22T 5 :=
  lower_map (ms := [swapRows 80,swapRows 81,swapRows 83,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u23 : Lower true (vars 198) u23T 5 :=
  lower_map (ms := [swapRows 65,swapRows 98,swapRows 67,swapRows 100,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u24 : Lower true (vars 197) u24T 4 :=
  lower_map (ms := [swapRows 32,swapRows 33,swapRows 82,swapRows 83,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u25 : Lower true (vars 195) u25T 5 :=
  lower_map (ms := [swapRows 96,swapRows 65,swapRows 98,swapRows 67,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u26 : Lower true (vars 184) u26T 5 :=
  lower_map (ms := [swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
def u27K3 : Nat → Nat
  | 0 => 0x8051423919909491290a4e93878f14624614419d00a8c88833801519110792312302204d8254644409a04a8c8881e11051010823c32a2221047065444420
  | _ => 0
def u27K4 : Nat → Nat
  | 0 => 0x5416a28a28a28a28227a28911a288a8a28a28a28a288c3561505226121228878a27622628a28a28a239c2198a28a28a28a28a28a28a24c30808a2d464af824462be01118bb462441f5185106f864441bd191106f804441ed189103b441440f9181102f864440bd191102f824440f5105083e440420be111082f444420
  | _ => 0
def u27K5 : Nat → Nat
  | 0 => 0xc81a215204fa317d107e881f420
  | _ => 0
def u27K6 : Nat → Nat
  | 0 => 0x50f
  | _ => 0
def u27N : Nat → Nat
  | 3 => 9
  | 4 => 17
  | 5 => 4
  | 6 => 1
  | _ => 0
def u27R : Nat → Nat → Nat
  | 3, i => packedAt u27K3 (i * 43) 43
  | 4, i => packedAt u27K4 (i * 30) 30
  | 5, i => packedAt u27K5 (i * 17) 17
  | 6, i => packedAt u27K6 (i * 4) 4
  | _, _ => 0
def u27I : Nat → Nat → Nat
  | 3, h => packedAt u27K3 (403 + ((h / 4 + packedAt u27K3 (387 + (h % 4) * 4) 4) % 19) * 5) 5
  | 4, h => packedAt u27K4 (528 + ((h / 9 + packedAt u27K4 (510 + (h % 9) * 2) 2) % 78) * 6) 6
  | 5, h => packedAt u27K5 (74 + ((h / 2 + packedAt u27K5 (68 + (h % 2) * 3) 3) % 9) * 4) 4
  | 6, h => packedAt u27K6 (5 + ((h / 1 + packedAt u27K6 (4 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u27Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffff0cf0cf
  | 4 => 0xffffffffffffffffffffffffffffffff333333
  | 5 => 0xc3cc3c
  | 7 => 0xfc0fc0
  | _ => 0
def u27Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffff510045
  | 4 => 0x844112
  | 5 => 0x281428
  | 7 => 0x2aa80
  | _ => 0
def u27Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,4),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,4),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,4),(0x3333333333333333333333333333333333333333333333333333333333333333,4)]
def u27Atlas : Atlas := ⟨6, rawDecor 178 u27Pos u27Neg, u27T, u27Slices, [swapRows 117], u27N, u27R, u27I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u27_3_0 : Interval u27Atlas 3 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u27_3 : Interval u27Atlas 3 0 9 := blk_u27_3_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u27_4_0 : Interval u27Atlas 4 0 17 := block_range (n := 17) (by decide +kernel)
theorem all_u27_4 : Interval u27Atlas 4 0 17 := blk_u27_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u27_5_0 : Interval u27Atlas 5 0 4 := block_range (n := 4) (by decide +kernel)
theorem all_u27_5 : Interval u27Atlas 5 0 4 := blk_u27_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u27_6_0 : Interval u27Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u27_6 : Interval u27Atlas 6 0 1 := blk_u27_6_0
theorem cert_u27 : Complete u27Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u27_3 i (by omega) hi
  · exact all_u27_4 i (by omega) hi
  · exact all_u27_5 i (by omega) hi
  · exact all_u27_6 i (by omega) hi
theorem b_u27 : Lower true (vars 178) u27T 7 := by
  have ready : Ready u27Atlas (asRow u27Pos) (asRow u27Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u27Atlas, u27Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u9
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u7
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u4
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u2
  exact frozen ready cert_u27 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,2,18),(inputs.getD 5 zero,2,34),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u28 : Lower true (vars 178) u28T 7 :=
  lower_map (ms := []) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
theorem b_u29 : Lower true (vars 177) u29T 7 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
theorem b_u30 : Lower true (vars 177) u30T 7 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
theorem b_u31 : Lower true (vars 170) u31T 5 :=
  lower_map (ms := [swapRows 65,swapRows 66,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u32 : Lower true (vars 170) u32T 5 :=
  lower_map (ms := [swapRows 65,swapRows 66,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u33 : Lower true (vars 169) u33T 5 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u34 : Lower true (vars 169) u34T 5 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u35 : Lower true (vars 162) u35T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u36 : Lower true (vars 163) u36T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u37 : Lower true (vars 147) u37T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 100]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u38 : Lower true (vars 139) u38T 5 :=
  lower_map (ms := [swapRows 64,swapRows 97,swapRows 66,swapRows 83,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u39 : Lower true (vars 114) u39T 5 :=
  lower_map (ms := [swapRows 65,swapRows 66,swapRows 67,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u40 : Lower true (vars 114) u40T 5 :=
  lower_map (ms := [swapRows 113,swapRows 114,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u41 : Lower true (vars 49) u41T 4 :=
  lower_map (ms := [swapRows 48,swapRows 49,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u42 : Lower true (vars 106) u42T 4 :=
  lower_map (ms := [swapRows 113,swapRows 114,swapRows 115,swapRows 116]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u43 : Lower true (vars 105) u43T 4 :=
  lower_map (ms := [swapRows 96,swapRows 97,swapRows 98,swapRows 115,swapRows 116,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u44 : Lower true (vars 102) u44T 4 :=
  lower_map (ms := [swapRows 113,swapRows 115,swapRows 116]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u45 : Lower true (vars 99) u45T 4 :=
  lower_map (ms := [swapRows 32,swapRows 113,swapRows 115,swapRows 116,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u46 : Lower true (vars 90) u46T 4 :=
  lower_map (ms := [swapRows 113,swapRows 114,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u47 : Lower true (vars 89) u47T 4 :=
  lower_map (ms := [swapRows 96,swapRows 97,swapRows 98,swapRows 115,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u48 : Lower true (vars 86) u48T 4 :=
  lower_map (ms := [swapRows 113,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u49 : Lower true (vars 83) u49T 4 :=
  lower_map (ms := [swapRows 32,swapRows 113,swapRows 115,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u50 : Lower true (vars 75) u50T 4 :=
  lower_map (ms := [swapRows 32,swapRows 81,swapRows 99,swapRows 84,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u51 : Lower true (vars 50) u51T 4 :=
  lower_map (ms := [swapRows 49,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u52 : Lower true (vars 57) u52T 5 :=
  lower_map (ms := [swapRows 64,swapRows 65,swapRows 66,swapRows 99,swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u53 : Lower true (vars 57) u53T 5 :=
  lower_map (ms := [swapRows 112,swapRows 113,swapRows 114,swapRows 99,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u54 : Lower true (vars 51) u54T 5 :=
  lower_map (ms := [swapRows 64,swapRows 97,swapRows 66,swapRows 99,swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u55 : Lower true (vars 51) u55T 5 :=
  lower_map (ms := [swapRows 96,swapRows 65,swapRows 98,swapRows 67,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u56 : Lower true (vars 51) u56T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u57 : Lower true (vars 43) u57T 4 :=
  lower_map (ms := [swapRows 112,swapRows 33,swapRows 114,swapRows 83,swapRows 116,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u58 : Lower true (vars 27) u58T 4 :=
  lower_map (ms := [swapRows 112,swapRows 33,swapRows 114,swapRows 83,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
theorem b_u59 : Lower true (vars 248) u59T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 72 0) (raw := vars 248) (T := u59T) (xs := [(inputs.getD 3 zero,128,136),(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u2
  have hc : (([(inputs.getD 3 zero,128,136),(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
def u60K4 : Nat → Nat
  | 0 => 0x7a18d54d7428b184dc833624138310b631874715059020109b846425c839e806465c8197866405c819b8464854619e8064854619b4460854619e4060854619b846425c80978664854209b846485420974660854209b446085420
  | _ => 0
def u60K5 : Nat → Nat
  | 0 => 0x6887faeac9bae96eabe81e8567ae86e9010ceb5ebae89920d8ee98eba502aba9529d5ebacb41e9c0f6fae9dea1eba780ea2bafb4b2a3e170e87390000a901d5000070100605f425c83ef0ca9077e09520ff402a41de805483be8cb9037d017206fc32a40fb845481b708a903f6095206fc02a40f7483461fa9028c37f215186fc42a30df485461be10a8c37d097203bc32a4057865480bf04a901fa015203ea40a107e480420bf90a8417e215082fa42a105f085420
  | _ => 0
def u60K6 : Nat → Nat
  | 0 => 0x2085aa0184190391c2341302ff20ff483ff207f481fd187fc80fd203f420
  | _ => 0
def u60K7 : Nat → Nat
  | 0 => 0x29f
  | _ => 0
def u60N : Nat → Nat
  | 4 => 12
  | 5 => 29
  | 6 => 8
  | 7 => 1
  | _ => 0
def u60R : Nat → Nat → Nat
  | 4, i => packedAt u60K4 (i * 44) 44
  | 5, i => packedAt u60K5 (i * 31) 31
  | 6, i => packedAt u60K6 (i * 18) 18
  | 7, i => packedAt u60K7 (i * 5) 5
  | _, _ => 0
def u60I : Nat → Nat → Nat
  | 4, h => packedAt u60K4 (560 + ((h / 8 + packedAt u60K4 (528 + (h % 8) * 4) 4) % 32) * 5) 5
  | 5, h => packedAt u60K5 (984 + ((h / 17 + packedAt u60K5 (899 + (h % 17) * 5) 5) % 78) * 6) 6
  | 6, h => packedAt u60K6 (148 + ((h / 4 + packedAt u60K6 (144 + (h % 4) * 1) 1) % 19) * 5) 5
  | 7, h => packedAt u60K7 (6 + ((h / 1 + packedAt u60K7 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u60Pos : Nat → Bits
  | 3 => 0xc603f00933fc
  | 4 => 0xffffffffffffffffffffffffc3090c0f41cccf
  | 5 => 0xffffffffffffffffffffffffcc11300f8e0f0f
  | 6 => 0x3022c0f0f00ff0
  | 7 => 0x3ffcff00fff000
  | _ => 0
def u60Neg : Nat → Bits
  | 3 => 0x3520173309115c
  | 4 => 0xffffffffffffffffffffffffdc504d554144c5
  | 5 => 0x2388b2aa8a0b0a
  | 6 => 0xac4e8ccd00ea0
  | 7 => 0x3000024a000
  | _ => 0
def u60Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,5),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,5),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,4),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,4)]
def u60Atlas : Atlas := ⟨7, rawDecor 248 u60Pos u60Neg, u60T, u60Slices, [swapRows 84], u60N, u60R, u60I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u60_4_0 : Interval u60Atlas 4 0 12 := block_range (n := 12) (by decide +kernel)
theorem all_u60_4 : Interval u60Atlas 4 0 12 := blk_u60_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u60_5_0 : Interval u60Atlas 5 0 29 := block_range (n := 29) (by decide +kernel)
theorem all_u60_5 : Interval u60Atlas 5 0 29 := blk_u60_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u60_6_0 : Interval u60Atlas 6 0 8 := block_range (n := 8) (by decide +kernel)
theorem all_u60_6 : Interval u60Atlas 6 0 8 := blk_u60_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u60_7_0 : Interval u60Atlas 7 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u60_7 : Interval u60Atlas 7 0 1 := blk_u60_7_0
theorem cert_u60 : Complete u60Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u60_4 i (by omega) hi
  · exact all_u60_5 i (by omega) hi
  · exact all_u60_6 i (by omega) hi
  · exact all_u60_7 i (by omega) hi
theorem b_u60 : Lower true (vars 248) u60T 8 := by
  have ready : Ready u60Atlas (asRow u60Pos) (asRow u60Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u60Atlas, u60Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u26
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u18
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
    · exact slice_correct (ms := fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u3
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
  exact frozen ready cert_u60 (by decide +kernel) (by decide) [(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,32,48),(inputs.getD 5 zero,16,48),(inputs.getD 6 zero,8,72),(inputs.getD 7 zero,8,136)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u61K4 : Nat → Nat
  | 0 => 0x2492390c112dc22a40db045481
  | _ => 0
def u61K5 : Nat → Nat
  | 0 => 0x6b83ca3fc81fd207f441
  | _ => 0
def u61K6 : Nat → Nat
  | 0 => 0x89f
  | _ => 0
def u61N : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 1
  | _ => 0
def u61R : Nat → Nat → Nat
  | 4, i => packedAt u61K4 (i * 31) 31
  | 5, i => packedAt u61K5 (i * 18) 18
  | 6, i => packedAt u61K6 (i * 5) 5
  | _, _ => 0
def u61I : Nat → Nat → Nat
  | 4, h => packedAt u61K4 (63 + ((h / 1 + packedAt u61K4 (62 + (h % 1) * 1) 1) % 13) * 3) 3
  | 5, h => packedAt u61K5 (55 + ((h / 1 + packedAt u61K5 (54 + (h % 1) * 1) 1) % 8) * 3) 3
  | 6, h => packedAt u61K6 (6 + ((h / 1 + packedAt u61K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u61Pos : Nat → Bits
  | 2 => 0x15003e04cc3fc
  | 4 => 0xffffffffffffffffffffffff0e781c1e80fccf
  | 5 => 0xffffffffffffffffffffffff3398e01f0f0f0f
  | 6 => 0xc00703e1f00ff0
  | 7 => 0xfde7fc01fff000
  | _ => 0
def u61Neg : Nat → Bits
  | 2 => 0xd754b6664cc15c
  | 4 => 0xffffffffffffffffffffffff71810caa8054c5
  | 5 => 0x8c626155050b0a
  | 6 => 0x28034999900ea0
  | 7 => 0x21c92006aa000
  | _ => 0
def u61Slices : List (Sig × Nat) := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,4),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,4),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,4)]
def u61Atlas : Atlas := ⟨6, rawDecor 244 u61Pos u61Neg, u61T, u61Slices, [swapRows 84], u61N, u61R, u61I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u61_4_0 : Interval u61Atlas 4 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u61_4 : Interval u61Atlas 4 0 2 := blk_u61_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u61_5_0 : Interval u61Atlas 5 0 3 := block_range (n := 3) (by decide +kernel)
theorem all_u61_5 : Interval u61Atlas 5 0 3 := blk_u61_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u61_6_0 : Interval u61Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u61_6 : Interval u61Atlas 6 0 1 := blk_u61_6_0
theorem cert_u61 : Complete u61Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u61_4 i (by omega) hi
  · exact all_u61_5 i (by omega) hi
  · exact all_u61_6 i (by omega) hi
theorem b_u61 : Lower true (vars 244) u61T 7 := by
  have ready : Ready u61Atlas (asRow u61Pos) (asRow u61Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u61Atlas, u61Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u3
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u19
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
  exact frozen ready cert_u61 (by decide +kernel) (by decide) [(inputs.getD 2 zero,64,68),(inputs.getD 4 zero,32,48),(inputs.getD 5 zero,16,48),(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,16,144)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u62 : Lower true (vars 242) u62T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 192 0) (raw := vars 242) (T := u62T) (xs := [(inputs.getD 6 zero,0,64),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u8
  have hc : (([(inputs.getD 6 zero,0,64),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u63 : Lower true (vars 242) u63T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 242) (T := u63T) (xs := [(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u27
  have hc : (([(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u64 : Lower true (vars 242) u64T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 242) (T := u64T) (xs := [(inputs.getD 6 zero,2,66)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u28
  have hc : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u65 : Lower true (vars 241) u65T 8 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u66 : Lower true (vars 241) u66T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 241) (T := u66T) (xs := [(inputs.getD 6 zero,128,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u30
  have hc : (([(inputs.getD 6 zero,128,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u67 : Lower true (vars 236) u67T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 36 0) (raw := vars 236) (T := u67T) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 5 zero,128,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u0
  have hc : (([(inputs.getD 2 zero,64,68),(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u68 : Lower true (vars 234) u68T 6 :=
  lower_map (ms := [swapRows 65,swapRows 66]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u59
def u69K6 : Nat → Nat
  | 0 => 0xa1f
  | _ => 0
def u69N : Nat → Nat
  | 6 => 1
  | _ => 0
def u69R : Nat → Nat → Nat
  | 6, i => packedAt u69K6 (i * 5) 5
  | _, _ => 0
def u69I : Nat → Nat → Nat
  | 6, h => packedAt u69K6 (6 + ((h / 1 + packedAt u69K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u69Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffe1c3608f81333f
  | 3 => 0x204837009cdcc
  | 5 => 0xffffffffffffffffffffffffe4082c03ce0e0f
  | 6 => 0x1870d07c700ff0
  | 7 => 0x1fbf1f807ff000
  | _ => 0
def u69Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffec180194811115
  | 3 => 0x1ce007b589454c
  | 5 => 0x13c11e6b4a0e0a
  | 6 => 0x306184a500aa0
  | 7 => 0xe00024a000
  | _ => 0
def u69Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,5),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,5),(0x3333333333333333333333333333333333333333333333333333333333333333,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5)]
def u69Atlas : Atlas := ⟨6, rawDecor 234 u69Pos u69Neg, u69T, u69Slices, [swapRows 97,swapRows 83], u69N, u69R, u69I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u69_6_0 : Interval u69Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u69_6 : Interval u69Atlas 6 0 1 := blk_u69_6_0
theorem cert_u69 : Complete u69Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u69_6 i (by omega) hi
theorem b_u69 : Lower true (vars 234) u69T 7 := by
  have ready : Ready u69Atlas (asRow u69Pos) (asRow u69Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u69Atlas, u69Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u32
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
  exact frozen ready cert_u69 (by decide +kernel) (by decide) [(inputs.getD 1 zero,32,34),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u70 : Lower true (vars 233) u70T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 72 0) (raw := vars 233) (T := u70T) (xs := [(inputs.getD 3 zero,1,9),(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u6
  have hc : (([(inputs.getD 3 zero,1,9),(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u71 : Lower true (vars 233) u71T 7 :=
  lower_map (ms := [swapRows 96,swapRows 97,swapRows 99,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
def u72K4 : Nat → Nat
  | 0 => 0xa5b845480
  | _ => 0
def u72K5 : Nat → Nat
  | 0 => 0x113f480
  | _ => 0
def u72K6 : Nat → Nat
  | 0 => 0x29f
  | _ => 0
def u72N : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0
def u72R : Nat → Nat → Nat
  | 4, i => packedAt u72K4 (i * 31) 31
  | 5, i => packedAt u72K5 (i * 18) 18
  | 6, i => packedAt u72K6 (i * 5) 5
  | _, _ => 0
def u72I : Nat → Nat → Nat
  | 4, h => packedAt u72K4 (32 + ((h / 1 + packedAt u72K4 (31 + (h % 1) * 1) 1) % 3) * 2) 2
  | 5, h => packedAt u72K5 (19 + ((h / 1 + packedAt u72K5 (18 + (h % 1) * 1) 1) % 3) * 2) 2
  | 6, h => packedAt u72K6 (6 + ((h / 1 + packedAt u72K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u72Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffe3e3f061f00f33f
  | 2 => 0xa201e04ccdcc
  | 5 => 0xfffffffffffffffffffffffe42c338078f0e0f
  | 6 => 0x18d04c1f8f00ff0
  | 7 => 0x1f1f8fe00fff000
  | _ => 0
def u72Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffec1c00229005115
  | 2 => 0x1dea2af6b4cc54c
  | 5 => 0x1342858d6850e0a
  | 6 => 0x20105094900aa0
  | 7 => 0xa07a5006aa000
  | _ => 0
def u72Slices : List (Sig × Nat) := [(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,5),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,4),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,4),(0x3333333333333333333333333333333333333333333333333333333333333333,4)]
def u72Atlas : Atlas := ⟨6, rawDecor 230 u72Pos u72Neg, u72T, u72Slices, [swapRows 113], u72N, u72R, u72I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u72_4_0 : Interval u72Atlas 4 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u72_4 : Interval u72Atlas 4 0 1 := blk_u72_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u72_5_0 : Interval u72Atlas 5 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u72_5 : Interval u72Atlas 5 0 1 := blk_u72_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u72_6_0 : Interval u72Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u72_6 : Interval u72Atlas 6 0 1 := blk_u72_6_0
theorem cert_u72 : Complete u72Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u72_4 i (by omega) hi
  · exact all_u72_5 i (by omega) hi
  · exact all_u72_6 i (by omega) hi
theorem b_u72 : Lower true (vars 230) u72T 7 := by
  have ready : Ready u72Atlas (asRow u72Pos) (asRow u72Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u72Atlas, u72Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u23
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u15
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u5
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u44
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
  exact frozen ready cert_u72 (by decide +kernel) (by decide) [(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,64,68),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u73 : Lower true (vars 229) u73T 7 :=
  lower_map (ms := [swapRows 64,swapRows 65,swapRows 67]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u74 : Lower true (vars 227) u74T 7 :=
  lower_map (ms := [swapRows 48,swapRows 50,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u75 : Lower true (vars 220) u75T 6 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
theorem b_u76 : Lower true (vars 218) u76T 7 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u77 : Lower true (vars 217) u77T 7 :=
  lower_map (ms := [swapRows 96,swapRows 97,swapRows 99,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u78 : Lower true (vars 214) u78T 7 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u79 : Lower true (vars 213) u79T 7 :=
  lower_map (ms := [swapRows 64,swapRows 65,swapRows 67,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u80 : Lower true (vars 211) u80T 7 :=
  lower_map (ms := [swapRows 48,swapRows 50,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u81 : Lower true (vars 206) u81T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 6 0) (raw := vars 206) (T := u81T) (xs := [(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u0
  have hc : (([(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u82 : Lower true (vars 205) u82T 7 :=
  lower_map (ms := [swapRows 80,swapRows 81,swapRows 83,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u83 : Lower true (vars 203) u83T 7 :=
  lower_map (ms := [swapRows 48,swapRows 81,swapRows 50,swapRows 99,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u84 : Lower true (vars 199) u84T 6 :=
  lower_map (ms := [swapRows 32,swapRows 49,swapRows 82,swapRows 83,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
theorem b_u85 : Lower true (vars 184) u85T 5 :=
  lower_map (ms := [swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u86 : Lower true (vars 186) u86T 8 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
theorem b_u87 : Lower true (vars 185) u87T 6 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u88 : Lower true (vars 185) u88T 8 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
theorem b_u89 : Lower true (vars 178) u89T 7 :=
  lower_map (ms := []) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
theorem b_u90 : Lower true (vars 181) u90T 6 :=
  lower_map (ms := [swapRows 16,swapRows 98,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u91 : Lower true (vars 179) u91T 6 :=
  lower_map (ms := [swapRows 16,swapRows 97,swapRows 98,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u92 : Lower true (vars 179) u92T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := vars 179) (T := u92T) (xs := [(inputs.getD 0 zero,16,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u27
  have hc : (([(inputs.getD 0 zero,16,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u93 : Lower true (vars 179) u93T 8 :=
  lower_map (ms := []) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u92
theorem b_u94 : Lower true (vars 169) u94T 5 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u95 : Lower true (vars 171) u95T 7 :=
  lower_map (ms := [swapRows 16,swapRows 49,swapRows 50,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u96 : Lower true (vars 171) u96T 7 :=
  lower_map (ms := [swapRows 16,swapRows 49,swapRows 50,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u97 : Lower true (vars 163) u97T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u98 : Lower true (vars 147) u98T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 100]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u99 : Lower true (vars 122) u99T 7 :=
  lower_map (ms := [swapRows 113,swapRows 114,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u100 : Lower true (vars 121) u100T 6 :=
  lower_map (ms := [swapRows 112,swapRows 113,swapRows 114]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u59
theorem b_u101 : Lower true (vars 121) u101T 7 :=
  lower_map (ms := [swapRows 112,swapRows 113,swapRows 114,swapRows 99,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u102 : Lower true (vars 118) u102T 7 :=
  lower_map (ms := [swapRows 113,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u103 : Lower true (vars 117) u103T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 4 64) (raw := vars 117) (T := u103T) (xs := [(inputs.getD 2 zero,64,68),(inputs.getD 6 zero,4,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u10
  have hc : (([(inputs.getD 2 zero,64,68),(inputs.getD 6 zero,4,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u104 : Lower true (vars 115) u104T 6 :=
  lower_map (ms := [swapRows 96,swapRows 98,swapRows 99,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u105 : Lower true (vars 115) u105T 6 :=
  lower_map (ms := [swapRows 48,swapRows 81,swapRows 82,swapRows 83,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u70
theorem b_u106 : Lower true (vars 115) u106T 7 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u107 : Lower true (vars 110) u107T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 110) (T := u107T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u42
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u108 : Lower true (vars 109) u108T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 109) (T := u108T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u43
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u109K4 : Nat → Nat
  | 0 => 0x73ccccc68c1c205cc4cca22f402a315e0054629f10a8833c215106bc32a1057065420
  | _ => 0
def u109K5 : Nat → Nat
  | 0 => 0x7158af98c8058300fd18bf481fd187f441fd103f420
  | _ => 0
def u109K6 : Nat → Nat
  | 0 => 0x89f
  | _ => 0
def u109N : Nat → Nat
  | 4 => 6
  | 5 => 6
  | 6 => 1
  | _ => 0
def u109R : Nat → Nat → Nat
  | 4, i => packedAt u109K4 (i * 31) 31
  | 5, i => packedAt u109K5 (i * 18) 18
  | 6, i => packedAt u109K6 (i * 5) 5
  | _, _ => 0
def u109I : Nat → Nat → Nat
  | 4, h => packedAt u109K4 (192 + ((h / 3 + packedAt u109K4 (186 + (h % 3) * 2) 2) % 21) * 4) 4
  | 5, h => packedAt u109K5 (117 + ((h / 3 + packedAt u109K5 (108 + (h % 3) * 3) 3) % 14) * 4) 4
  | 6, h => packedAt u109K6 (6 + ((h / 1 + packedAt u109K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u109Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffc6001fe34c33f
  | 1 => 0x181fe0048fdcc
  | 3 => 0xfffffffffffffffffffffffffe3e001f8f0e0f
  | 5 => 0xc01fe1f00ff0
  | 6 => 0x31fe001fff000
  | _ => 0
def u109Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffe88a2b214c115
  | 1 => 0x242662608554c
  | 3 => 0x1464c4c890e0a
  | 5 => 0x1351949e00aa0
  | 6 => 0xb9919176a000
  | _ => 0
def u109Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,4),(0x3333333333333333333333333333333333333333333333333333333333333333,4),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,4),(0x5555555555555555555555555555555555555555555555555555555555555555,4),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,4)]
def u109Atlas : Atlas := ⟨6, rawDecor 107 u109Pos u109Neg, u109T, u109Slices, [swapRows 97,swapRows 83], u109N, u109R, u109I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u109_4_0 : Interval u109Atlas 4 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u109_4 : Interval u109Atlas 4 0 6 := blk_u109_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u109_5_0 : Interval u109Atlas 5 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u109_5 : Interval u109Atlas 5 0 6 := blk_u109_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u109_6_0 : Interval u109Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u109_6 : Interval u109Atlas 6 0 1 := blk_u109_6_0
theorem cert_u109 : Complete u109Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u109_4 i (by omega) hi
  · exact all_u109_5 i (by omega) hi
  · exact all_u109_6 i (by omega) hi
theorem b_u109 : Lower true (vars 107) u109T 7 := by
  have ready : Ready u109Atlas (asRow u109Pos) (asRow u109Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u109Atlas, u109Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u57
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u43
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u50
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u45
  exact frozen ready cert_u109 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,32,34),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u110 : Lower true (vars 103) u110T 5 :=
  lower_map (ms := [swapRows 32,swapRows 49,swapRows 82,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
theorem b_u111 : Lower true (vars 93) u111T 5 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
theorem b_u112 : Lower true (vars 91) u112T 7 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
theorem b_u113 : Lower true (vars 87) u113T 5 :=
  lower_map (ms := [swapRows 32,swapRows 49,swapRows 82,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
theorem b_u114 : Lower true (vars 61) u114T 6 :=
  lower_map (ms := [swapRows 16,swapRows 98,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u115 : Lower true (vars 57) u115T 5 :=
  lower_map (ms := [swapRows 112,swapRows 113,swapRows 114,swapRows 99,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
theorem b_u116 : Lower true (vars 59) u116T 6 :=
  lower_map (ms := [swapRows 16,swapRows 97,swapRows 98,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u117 : Lower true (vars 59) u117T 7 :=
  lower_map (ms := [swapRows 96,swapRows 81,swapRows 98,swapRows 99,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u118 : Lower true (vars 59) u118T 7 :=
  lower_map (ms := [swapRows 96,swapRows 81,swapRows 98,swapRows 99,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u119 : Lower true (vars 55) u119T 6 :=
  lower_map (ms := [swapRows 16,swapRows 97,swapRows 114,swapRows 99,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
theorem b_u120 : Lower true (vars 51) u120T 5 :=
  lower_map (ms := [swapRows 80,swapRows 97,swapRows 82,swapRows 83,swapRows 100,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
theorem b_u121 : Lower true (vars 252) u121T 9 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 252) (T := u121T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u60
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u122 : Lower true (vars 250) u122T 9 := by
  have h := lift_ok (u := true) (ms := fixRows 72 0) (raw := vars 250) (T := u122T) (xs := [(inputs.getD 3 zero,128,136),(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u27
  have hc : (([(inputs.getD 3 zero,128,136),(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
def u123K6 : Nat → Nat
  | 0 => 0x29d34a34a2462
  | _ => 0
def u123K7 : Nat → Nat
  | 0 => 0x1c92a8eaaa1a814df4a34a2bf8664a2ff4664a2fb4a2462bf4a6462
  | _ => 0
def u123K8 : Nat → Nat
  | 0 => 0x10723fa517f462
  | _ => 0
def u123K9 : Nat → Nat
  | 0 => 0x143f
  | _ => 0
def u123N : Nat → Nat
  | 6 => 1
  | 7 => 5
  | 8 => 2
  | 9 => 1
  | _ => 0
def u123R : Nat → Nat → Nat
  | 6, i => packedAt u123K6 (i * 45) 45
  | 7, i => packedAt u123K7 (i * 32) 32
  | 8, i => packedAt u123K8 (i * 19) 19
  | 9, i => packedAt u123K9 (i * 6) 6
  | _, _ => 0
def u123I : Nat → Nat → Nat
  | 6, h => packedAt u123K6 (46 + ((h / 1 + packedAt u123K6 (45 + (h % 1) * 1) 1) % 3) * 2) 2
  | 7, h => packedAt u123K7 (162 + ((h / 2 + packedAt u123K7 (160 + (h % 2) * 1) 1) % 14) * 4) 4
  | 8, h => packedAt u123K8 (39 + ((h / 1 + packedAt u123K8 (38 + (h % 1) * 1) 1) % 5) * 3) 3
  | 9, h => packedAt u123K9 (7 + ((h / 1 + packedAt u123K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u123Pos : Nat → Bits
  | 1 => 0xffffffffffc007ef03a3f0041c3f00261330ff
  | 3 => 0x18000452403be00009386dcccc
  | 4 => 0xffffffffffc0e013181c70c003c741c18e0f0f
  | 5 => 0x7001c601f830003f88e01f00ff0
  | 6 => 0x38006080600c03fc00f001fff000
  | 7 => 0x3fff80ff800ffc0000fffe000000
  | _ => 0
def u123Neg : Nat → Bits
  | 1 => 0xffffffffffc92010a814000c24090022011055
  | 3 => 0x3b61f50012417ce4db0928254ccc
  | 4 => 0x160aac408284d1494641408e050a
  | 5 => 0x20d54311005b2292b08a01700aa0
  | 6 => 0x49e0a06000e831b24d001daa000
  | 7 => 0x69200000002494000000
  | _ => 0
def u123Slices : List (Sig × Nat) := [(0x3333333333333333333333333333333333333333333333333333333333333333,8),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,8),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,8),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,5),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,4),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,4)]
def u123Atlas : Atlas := ⟨9, rawDecor 250 u123Pos u123Neg, u123T, u123Slices, [swapRows 84], u123N, u123R, u123I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u123_6_0 : Interval u123Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u123_6 : Interval u123Atlas 6 0 1 := blk_u123_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u123_7_0 : Interval u123Atlas 7 0 5 := block_range (n := 5) (by decide +kernel)
theorem all_u123_7 : Interval u123Atlas 7 0 5 := blk_u123_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u123_8_0 : Interval u123Atlas 8 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u123_8 : Interval u123Atlas 8 0 2 := blk_u123_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u123_9_0 : Interval u123Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u123_9 : Interval u123Atlas 9 0 1 := blk_u123_9_0
theorem cert_u123 : Complete u123Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u123_6 i (by omega) hi
  · exact all_u123_7 i (by omega) hi
  · exact all_u123_8 i (by omega) hi
  · exact all_u123_9 i (by omega) hi
theorem b_u123 : Lower true (vars 250) u123T 10 := by
  have ready : Ready u123Atlas (asRow u123Pos) (asRow u123Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u123Atlas, u123Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u60
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u86
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u99
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u76
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u46
  exact frozen ready cert_u123 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,64,72),(inputs.getD 4 zero,2,18),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u124 : Lower true (vars 249) u124T 9 := by
  have h := lift_ok (u := true) (ms := fixRows 72 0) (raw := vars 249) (T := u124T) (xs := [(inputs.getD 3 zero,1,9),(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u29
  have hc : (([(inputs.getD 3 zero,1,9),(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u125 : Lower true (vars 249) u125T 10 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u123
def u126K4 : Nat → Nat
  | 0 => 0x8e085247244864251a502205920c94a34624a0440
  | _ => 0
def u126K5 : Nat → Nat
  | 0 => 0x212106447669660cd99b3821811e67183143cb9a69a698a79a5d14895a68807e382408240590c00a00003534a38074a24628bd22031d28d102b30c84a3462440a7832128d281102da8684a24a0440f4928d189281102da4a84624a0440d6928a19d281103d24a34a2460440bc92a1189181103b24624608a6440e4d28d189299103964a34604a6440ec9189181299103330678474a6440e69289282199103934a34a2466440e692892811991023b8484a7466440
  | _ => 0
def u126K6 : Nat → Nat
  | 0 => 0xf07d586c021db0d6856f246c36f5bb2cb476643f731ddd91cc6c382e9ec1f40b6c11b0ab397b10ec2ef94ecd87516c27b08c9d9b2a26d91766cd85294a80e36246002f2a739ac8d622b62309b226c9d8ab6c58eb66c6882bbb0cdb5a76a66d679b0c8465eba0897fa46609909292503c680060038508d0287000140500004000200c01111dd002e0820002067e80f0cc9459f4a38064a29fa33c032515de19d01928aee0ce80c9457b8474064a2e9a51a512315ee01d28918a7f00e94c8c55f8674a24a0eda5123125057d29d189283b694508c9419f4a38464a09fc33c232504fd19e119282ef0ce88c941770674464a09fe63a51a204fe31d28d1027e18e946881db4a34a2440bdc33a512207cd28d189102f694e8c4881de4a34a0440ed2512502207e9189281102fd0ce940881fa8474a0440fd2512302207c9189181103768c514c881be4608a64409fa33c532205de19d299102ee0ce94c8817b8474a6440cfa51a532206ed1892991037c8c094c8813f8674a6440dbc33a532204de19d2991036e0ce94c881370674a6440ddc23a532206ed28a1991037c9410cc8813f4a7866440dda512332206f92811991027f14e8cc8813f4a7466440
  | _ => 0
def u126K7 : Nat → Nat
  | 0 => 0x4a0965c9173a2d5d75c30f72f1191b173e85d71ef332d35dc04175d23842d51d4064942b6aa774c1046628814028065df4a34a2bf8664a2ff4664a2bf8064a2ff4064a2fb4a2462bf4a6462df4a24a0ff4624a0ff8464a0bf8464a0ff4464a0ff4a3440fb4a2440fb462440fe4a0440fe460440bf8a6440ff4a6440bf4a6440bf866440ff466440bf466440
  | _ => 0
def u126K8 : Nat → Nat
  | 0 => 0x841e219228fe945fd18bfa507f440
  | _ => 0
def u126K9 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u126N : Nat → Nat
  | 4 => 2
  | 5 => 19
  | 6 => 54
  | 7 => 23
  | 8 => 4
  | 9 => 1
  | _ => 0
def u126R : Nat → Nat → Nat
  | 4, i => packedAt u126K4 (i * 71) 71
  | 5, i => packedAt u126K5 (i * 58) 58
  | 6, i => packedAt u126K6 (i * 45) 45
  | 7, i => packedAt u126K7 (i * 32) 32
  | 8, i => packedAt u126K8 (i * 19) 19
  | 9, i => packedAt u126K9 (i * 6) 6
  | _, _ => 0
def u126I : Nat → Nat → Nat
  | 4, h => packedAt u126K4 (143 + ((h / 1 + packedAt u126K4 (142 + (h % 1) * 1) 1) % 7) * 3) 3
  | 5, h => packedAt u126K5 (1168 + ((h / 11 + packedAt u126K5 (1102 + (h % 11) * 6) 6) % 45) * 6) 6
  | 6, h => packedAt u126K6 (2661 + ((h / 33 + packedAt u126K6 (2430 + (h % 33) * 7) 7) % 127) * 7) 7
  | 7, h => packedAt u126K7 (801 + ((h / 13 + packedAt u126K7 (736 + (h % 13) * 5) 5) % 53) * 6) 6
  | 8, h => packedAt u126K8 (82 + ((h / 2 + packedAt u126K8 (76 + (h % 2) * 3) 3) % 9) * 4) 4
  | 9, h => packedAt u126K9 (7 + ((h / 1 + packedAt u126K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u126Pos : Nat → Bits
  | 1 => 0xfffffff803f9f803f0ff006070fc001e1330ff
  | 2 => 0x3330ccc001f800099986dcccc
  | 4 => 0xfffffff81c06383c0f0f03800f1d01e18e0f0f
  | 5 => 0xe007c3c00ff01c000fe21e01f00ff0
  | 6 => 0x7003804001000e01ff003e001fff000
  | 7 => 0x7ffc007ffe000ffe00003fffe000000
  | _ => 0
def u126Neg : Nat → Bits
  | 1 => 0xfffffff924020554050000209024000a011055
  | 2 => 0x76cff6b330ccc96f3936c9998254ccc
  | 4 => 0x2c148c28120502185251900a08e050a
  | 5 => 0x41a90182a40054c0a4ac20a01700aa0
  | 6 => 0x930090008000690c6c932001daa000
  | 7 => 0x2520001aaa92500000d554000000
  | _ => 0
def u126Slices : List (Sig × Nat) := [(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,7),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,7),(0x3333333333333333333333333333333333333333333333333333333333333333,7),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,5),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,4),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,4),(0x0000333300003333000033330000333300003333000033330000333300003333,4),(0x0000000033333333000000003333333300000000333333330000000033333333,4)]
def u126Atlas : Atlas := ⟨9, rawDecor 246 u126Pos u126Neg, u126T, u126Slices, [swapRows 84], u126N, u126R, u126I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_4_0 : Interval u126Atlas 4 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u126_4 : Interval u126Atlas 4 0 2 := blk_u126_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_5_0 : Interval u126Atlas 5 0 19 := block_range (n := 19) (by decide +kernel)
theorem all_u126_5 : Interval u126Atlas 5 0 19 := blk_u126_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_6_0 : Interval u126Atlas 6 0 54 := block_range (n := 54) (by decide +kernel)
theorem all_u126_6 : Interval u126Atlas 6 0 54 := blk_u126_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_7_0 : Interval u126Atlas 7 0 23 := block_range (n := 23) (by decide +kernel)
theorem all_u126_7 : Interval u126Atlas 7 0 23 := blk_u126_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_8_0 : Interval u126Atlas 8 0 4 := block_range (n := 4) (by decide +kernel)
theorem all_u126_8 : Interval u126Atlas 8 0 4 := blk_u126_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u126_9_0 : Interval u126Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u126_9 : Interval u126Atlas 9 0 1 := blk_u126_9_0
theorem cert_u126 : Complete u126Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u126_4 i (by omega) hi
  · exact all_u126_5 i (by omega) hi
  · exact all_u126_6 i (by omega) hi
  · exact all_u126_7 i (by omega) hi
  · exact all_u126_8 i (by omega) hi
  · exact all_u126_9 i (by omega) hi
theorem b_u126 : Lower true (vars 246) u126T 10 := by
  have ready : Ready u126Atlas (asRow u126Pos) (asRow u126Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u126Atlas, u126Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u28
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u102
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u78
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u23
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u48
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u44
    · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u19
  exact frozen ready cert_u126 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,64,68),(inputs.getD 4 zero,2,18),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u127K4 : Nat → Nat
  | 0 => 0xd763b0db3ca1a4928e02118911b282c9204e51a51433220592449ca34a0866440
  | _ => 0
def u127K5 : Nat → Nat
  | 0 => 0x58b162c2fb162c58b0f6c580562c58ad06c58b162358b1619443282c58b002c587762c58b162c36b162c58b162c582f62c3eb162c0eb1010d8b06ac58a04ac58b161ad8b162c58b0f26d8b162a58b162c4eb161394b162c58b162c58b162c58b162c58128ac58b162c58b02d6497332c2a676293fb162c583762c584b62c1fb032c58b162c161e741d8610ec58b162c081471258b11ec58b122c066962c2e4ce2c37b162c582a8d4a8b15ec18b10ac582362c10b162893b162558b162c58b162c587562c580962c58b162c58b162c58b07ac0800002000400412001d4d28e01d28918a3e0084a78a6462cce19e11d29918b3a8470074a6462e4d28d28a01918b5a4a2807462ca09792a201d18b283934a3462446ca0aea02118911b2822f4880c74624a08bd22031d28d102da408ca34a2440acc32128d189102da448ca34a0440b6a1a1289281103d24a34624a0440b692a11892811027a0e84624a0440d6928a19d281103d24a34a24604409e83a1289181102f28a8462460440bc92a1189181103b24624608a64408dc1a129e299103934a34624a6440e5928d181299103b24624604a6440ccc19e11d299103360678074a6440cea11e01d299102b3448ca3866440ad902328e19910393ca34a2866440e5b28d2821991039a4a24a0866440c5f28d29e199103934a34a2466440e692892811991023b8484a74664408fa02129d1991022f4880a74664408ed12029d1991023e4080a7466440
  | _ => 0
def u127K6 : Nat → Nat
  | 0 => 0x7c3a91ab6f7c7c5b7c11087c7c7c387c037a7c7c7c7c7c7c7c7c477c107c7c7c4bfc15fc7c66a7fc427c08f20b7c7c7c7c4e18758b9c7c7c4a7c7c16f905c07c40fc29a3d81e7c7825cfdf7c07f0e20eac954b7c3e9b7c42ea3e027c7c7c684132fc7c491ce512bdecfc7c7c7c7c63b8fb0d1a8ff46ab1de431f667c7c20a0257c7c567c55fc062aaefc7c7c577c7c247c44bb56aa7c3a357c7c3237717c7c5a537c7c7c09f8d17c7c06fc7c7c2e7c7c0e617c7c7c7c7c7c7c24abcc5c4abbf1fc22636ffc7c4da2dd7c590cada3697c7c7c6b7c43fc7c4cee7c7517147c7bfc50d47c1ee01328f636c57c70731fb7b97c190f7afc7c79fc7c7c7c6c3593c60c7c7c00527c7c7c33312c3c7c73fc7c19cd6b97fc277c7c33fc4580c02112668001088022042000c20004200000214401100a001063104c2114a30080000044010c000041100859fc03a336514fe19d01b28abe80f946945d74a38664a29fa03c332515ee11d19928afd00e8cc9457e0074664a2cfe51c0325167d28e01928a7e8cf00c945778674064a2bb833a032517cd28d28918ba69469448c5f38674a2462bdc03a512315ed11f29918a7e80f94c8c53f4a78a64629fa03c532315ee11d29918afd00e94c8c57e0074a6462ddc23a532314fe01d29918b7d00e94c8c53e8074a6462df003a532314f801d29918a5e90e14c8c53ec070a64629fa038532314f901c29918b7694500c8c53fca78064629fa53c0323157e19d28b283b69448c59415f4a7462ca0bf403a316504fe31d18b2833e94688d941bb462446ca09fc33a236504fd19d11b282be8cf9449415f8674a24a0ef403a5125076d289189282bf94e8c49415f4a74624a09fc63a312504fc31d189283b694508c9419fca38464a0cfa51c232506ed28a1192827f0cf08c9413f4678464a0bbc33a232505dc19d119282fd00e88c9417b447ca3440bf203e51a204ff31f28d1027e98f9468813fcc74a34409fc63a51a204fc31d28d103b7946944881db4a34a2440bdc33a512207ea01d289103e69468c48817b8a7462440bda53a3122077b28d281103bc946940881fa4a24a0440ed2512502207e9189281102fd0ce940881fa8474a0440fd2512302207c9189181102f688f94c8817e407ca6440cfa51e532204fd19f299103768c514c881be4608a64409fa53c532204fd19e299102ef0ce94c881770674a6440bdc23a532205fa01d2991033f94694c8819f4a34a6440dda312532206f91812991027f0ce94c881b78674a64409bc33a532206dc19d2991026e0ce94c881bb8474a6440df403a532204bd21c2991026f8ce14c8813f4670a64409ba338532206df28e199103769450cc881be4a08664409fe53c332204fd29e199103769448cc881be4a04664409fe53a332204fe29d1991027e94e8cc8813f0a7466440
  | 1 => 0x7c7c481d7c7c7c7c51fc7c057c367c7c297c7c7c7c677c1a7c777c070d8474fc34fc440a267c7c30ed7c3f287c39b40afc4f21d9d03cbff298fc7c302ff79dad213d76817c14fc7c097c122f7c7c7c55641bfc1096
  | _ => 0
def u127K7 : Nat → Nat
  | 0 => 0x385abb54ad5a1222d5a0f22d4cb44880c14a6d198ef14032cfa55ab56ad4d012ed5a376915ab56812eb56ad5ab56ad55b56acc60b68d303901011630c35a64607aab56ad2cb569c56b56ad5ab56ad5a896a2ce1b6ad5a476215a2f42a34b4124ad496ad1f2ad8f3ab53ced7b5690da4c9ca5a2b20050300200202410001112bf466ca2bf406ca2dfca34a2ff4a34a2df4a34a2ff8664a2bf8664a2ff4664a2ff8064a2bf8064a2ff4064a2fb4a2462ffca6462bfca6462bf8a6462ff4a6462bf4a6462bf0a6462bf806462ff406462df4a2ca0ff462ca0bf446ca0dfca24a0ff4a24a0df4a24a0ff4624a0ff8464a0bf8464a0ff4464a0ffca3440ff4a3440fb4a2440fb462440fe4a0440fe460440ffca6440bfca6440bf8a6440ff4a6440bf4a6440bf0a6440bf866440ff466440bf466440
  | _ => 0
def u127K8 : Nat → Nat
  | 0 => 0x16624064d5b60d03fe517f4a2fe8c5ff283fa507f440
  | _ => 0
def u127K9 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u127N : Nat → Nat
  | 4 => 3
  | 5 => 44
  | 6 => 124
  | 7 => 45
  | 8 => 6
  | 9 => 1
  | _ => 0
def u127R : Nat → Nat → Nat
  | 4, i => packedAt u127K4 (i * 71) 71
  | 5, i => packedAt u127K5 (i * 58) 58
  | 6, i => packedAt u127K6 (i * 45) 45
  | 7, i => packedAt u127K7 (i * 32) 32
  | 8, i => packedAt u127K8 (i * 19) 19
  | 9, i => packedAt u127K9 (i * 6) 6
  | _, _ => 0
def u127I : Nat → Nat → Nat
  | 4, h => packedAt u127K4 (215 + ((h / 2 + packedAt u127K4 (213 + (h % 2) * 1) 1) % 15) * 3) 3
  | 5, h => packedAt u127K5 (2627 + ((h / 25 + packedAt u127K5 (2552 + (h % 25) * 3) 3) % 240) * 7) 7
  | 6, h => packedAt u127K6 (5935 + ((h / 71 + packedAt u127K6 (5580 + (h % 71) * 5) 5) % 367) * 8) 8
  | 7, h => packedAt u127K7 (1540 + ((h / 25 + packedAt u127K7 (1440 + (h % 25) * 4) 4) % 131) * 7) 7
  | 8, h => packedAt u127K8 (123 + ((h / 3 + packedAt u127K8 (114 + (h % 3) * 3) 3) % 13) * 4) 4
  | 9, h => packedAt u127K9 (7 + ((h / 1 + packedAt u127K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u127Pos : Nat → Bits
  | 0 => 0xffffff800f1f807b0ff003800ff1003c33c0ff
  | 2 => 0x6660ccc0007f00023330ccfccc
  | 4 => 0xffffff80f0e38785f0f01c00f0f403c30f0f0f
  | 5 => 0xf00fc7806ff00e000ff083c03f00ff0
  | 6 => 0x7000000007000f007f000fc003fff000
  | 7 => 0x7fff007ff8000fff80000ffffc000000
  | _ => 0
def u127Neg : Nat → Bits
  | 0 => 0xffffff9550602a84500101890551001411c055
  | 2 => 0x7333b6e660ccc8b6c733323330445ccc
  | 4 => 0x2a050c502a05020c1250a401410e050a
  | 5 => 0x40aa01855100546024aa081402e00aa0
  | 6 => 0xccc49000700074938cccd4003bba000
  | 7 => 0x920000aaa892400002aaa8000000
  | _ => 0
def u127Slices : List (Sig × Nat) := [(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,7),(0x5555555555555555555555555555555555555555555555555555555555555555,7),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,6),(0x0000555500005555000055550000555500005555000055550000555500005555,4),(0x0000000055555555000000005555555500000000555555550000000055555555,4),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,4)]
def u127Atlas : Atlas := ⟨9, rawDecor 245 u127Pos u127Neg, u127T, u127Slices, [swapRows 84], u127N, u127R, u127I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_4_0 : Interval u127Atlas 4 0 3 := block_range (n := 3) (by decide +kernel)
theorem all_u127_4 : Interval u127Atlas 4 0 3 := blk_u127_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_5_0 : Interval u127Atlas 5 0 44 := block_range (n := 44) (by decide +kernel)
theorem all_u127_5 : Interval u127Atlas 5 0 44 := blk_u127_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_0 : Interval u127Atlas 6 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_64 : Interval u127Atlas 6 64 60 := block_range (n := 60) (by decide +kernel)
theorem all_u127_6 : Interval u127Atlas 6 0 124 := (concat blk_u127_6_0 blk_u127_6_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_0 : Interval u127Atlas 7 0 45 := block_range (n := 45) (by decide +kernel)
theorem all_u127_7 : Interval u127Atlas 7 0 45 := blk_u127_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_8_0 : Interval u127Atlas 8 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u127_8 : Interval u127Atlas 8 0 6 := blk_u127_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_9_0 : Interval u127Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u127_9 : Interval u127Atlas 9 0 1 := blk_u127_9_0
theorem cert_u127 : Complete u127Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u127_4 i (by omega) hi
  · exact all_u127_5 i (by omega) hi
  · exact all_u127_6 i (by omega) hi
  · exact all_u127_7 i (by omega) hi
  · exact all_u127_8 i (by omega) hi
  · exact all_u127_9 i (by omega) hi
theorem b_u127 : Lower true (vars 245) u127T 10 := by
  have ready : Ready u127Atlas (asRow u127Pos) (asRow u127Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u127Atlas, u127Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u65
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u30
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u79
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u73
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
    · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u19
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u24
  exact frozen ready cert_u127 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 2 zero,64,68),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u128 : Lower true (vars 243) u128T 7 := by
  have h := lift_ok (u := true) (ms := fixRows 193 0) (raw := vars 243) (T := u128T) (xs := [(inputs.getD 0 zero,0,1),(inputs.getD 6 zero,0,64),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u8
  have hc : (([(inputs.getD 0 zero,0,1),(inputs.getD 6 zero,0,64),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by decide +kernel
  rwa [hc] at h
theorem b_u129 : Lower true (vars 243) u129T 9 := by
  have h := lift_ok (u := true) (ms := fixRows 65 0) (raw := vars 243) (T := u129T) (xs := [(inputs.getD 0 zero,16,17),(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u27
  have hc : (([(inputs.getD 0 zero,16,17),(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
def u130K5 : Nat → Nat
  | 0 => 0x244e08baa02119d28920b834a34a2486462
  | _ => 0
def u130K6 : Nat → Nat
  | 0 => 0x420802e061261084210841c1842108421084150841b08320f81210800bf403a3325172d28d28920bd68ce944905ab4a2866482e9a51a512316fa01d29918a7d00e94c8c5ab4a2486462
  | _ => 0
def u130K7 : Nat → Nat
  | 0 => 0x2247949f050a4694a4992dcc216526c804df4a34a2bf8664a2ff4664a2ef4a3482eb4a2482af866482fb4a2462bf4a6462af486462
  | _ => 0
def u130K8 : Nat → Nat
  | 0 => 0xd057b2d9fd28b7a417f462
  | _ => 0
def u130K9 : Nat → Nat
  | 0 => 0x113f
  | _ => 0
def u130N : Nat → Nat
  | 5 => 2
  | 6 => 8
  | 7 => 9
  | 8 => 3
  | 9 => 1
  | _ => 0
def u130R : Nat → Nat → Nat
  | 5, i => packedAt u130K5 (i * 58) 58
  | 6, i => packedAt u130K6 (i * 45) 45
  | 7, i => packedAt u130K7 (i * 32) 32
  | 8, i => packedAt u130K8 (i * 19) 19
  | 9, i => packedAt u130K9 (i * 6) 6
  | _, _ => 0
def u130I : Nat → Nat → Nat
  | 5, h => packedAt u130K5 (117 + ((h / 1 + packedAt u130K5 (116 + (h % 1) * 1) 1) % 7) * 3) 3
  | 6, h => packedAt u130K6 (372 + ((h / 4 + packedAt u130K6 (360 + (h % 4) * 3) 3) % 43) * 5) 5
  | 7, h => packedAt u130K7 (293 + ((h / 5 + packedAt u130K7 (288 + (h % 5) * 1) 1) % 26) * 5) 5
  | 8, h => packedAt u130K8 (58 + ((h / 1 + packedAt u130K8 (57 + (h % 1) * 1) 1) % 10) * 3) 3
  | 9, h => packedAt u130K9 (7 + ((h / 1 + packedAt u130K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u130Pos : Nat → Bits
  | 0 => 0xfffffffffff00309006c0cc0c039c8131bc273
  | 1 => 0x1c36018233013cc6001c24f39c
  | 4 => 0xfffffffffff0e0c70e15c3c20307d060c70c1f
  | 5 => 0x700f87019fc0403f82180f80fe0
  | 6 => 0x80000801e00383c003e00fff000
  | 7 => 0xfff00ffe0003fc0003fff000000
  | _ => 0
def u130Neg : Nat → Bits
  | 0 => 0xfffffffffffb64d212104009cc5ac81109c231
  | 1 => 0x92040a4008001444a4014005294
  | 4 => 0x4092840a814121105102046040a
  | 5 => 0x92050944016422a02080b00940
  | 6 => 0x6dfbf001c003ebbb5ba00ffa000
  | 7 => 0x32a800000054a000000
  | _ => 0
def u130Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,8),(0x3333333333333333333333333333333333333333333333333333333333333333,8),(0x5555555555555555555555555555555555555555555555555555555555555555,8),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,7),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,6),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,5),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,5),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,5),(0x00000000000000000000000000000000ffffffffffffffff0000000000000000,5),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,4),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,4)]
def u130Atlas : Atlas := ⟨9, rawDecor 243 u130Pos u130Neg, u130T, u130Slices, [swapRows 84], u130N, u130R, u130I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_5_0 : Interval u130Atlas 5 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u130_5 : Interval u130Atlas 5 0 2 := blk_u130_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_6_0 : Interval u130Atlas 6 0 8 := block_range (n := 8) (by decide +kernel)
theorem all_u130_6 : Interval u130Atlas 6 0 8 := blk_u130_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_7_0 : Interval u130Atlas 7 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u130_7 : Interval u130Atlas 7 0 9 := blk_u130_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_8_0 : Interval u130Atlas 8 0 3 := block_range (n := 3) (by decide +kernel)
theorem all_u130_8 : Interval u130Atlas 8 0 3 := blk_u130_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_9_0 : Interval u130Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u130_9 : Interval u130Atlas 9 0 1 := blk_u130_9_0
theorem cert_u130 : Complete u130Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u130_5 i (by omega) hi
  · exact all_u130_6 i (by omega) hi
  · exact all_u130_7 i (by omega) hi
  · exact all_u130_8 i (by omega) hi
  · exact all_u130_9 i (by omega) hi
theorem b_u130 : Lower true (vars 243) u130T 10 := by
  have ready : Ready u130Atlas (asRow u130Pos) (asRow u130Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u130Atlas, u130Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u93
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u106
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u80
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u74
    · exact slice_correct (ms := fixRows 0 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u91
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u37
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u36
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u25
    · exact slice_correct (ms := fixRows 128 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u54
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u49
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u45
  exact frozen ready cert_u130 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u131K4 : Nat → Nat
  | 0 => 0x20a1c20aa28a28a28a127a8a28a00a28a181280a4a0ca10a16a22a285281a8a0ea289a8a1a600d0d29111c29920f464a44070a64838e612131f28f206394088474a6c818e612131f207282398484c7c814a08d53a3206199282398c84a7c814409e22a101f2051029a0c84a44a0440f0929120d281102720e84834a0440b612a3205281102784e8c814a0440d8920e29d201103624834a74804409a422109d299102788084274a6440d6128229d09910319ca68a7426440
  | _ => 0
def u131K5 : Nat → Nat
  | 0 => 0xa0100264a0a01aa05e2470a078a0161c3226a0a06c663628303c08069e0e489c7c845468886a7280a038426e829a4c467e4a522e92142a987458a00a8a5ca02ca0a040a0223e8c608e4e2000943486a01296a03a62a050a0045a7aa0900ca0561876441ea0a0040000e8317d0570c02460800014c0a800231419bc33a036524ed01e1192927708e90d94797ca38a64839dc23a53241cfa01d29920e7688e14c9073e4070a6483f1c23a52241d9e01d29120ece90f94c907c74a48a6483cbe53453241d9e21d29920ee708e94c907768074a6483bb003a53241f1d29029920ece90e14c907734470a6483bb603853241dd901c29920e7a98f947903b98474a6c819cc23a53640cf601d29b2067b14e80d903c74a4483ca0aea53e40e504f531f2072834e90690d9413b847486ca0e3a52241a504dc31d20d282ba94f9029417c407c814a09ea63e40a506d52861992836b9030cc941378878664a09ba43c332506d509e1992836b0cc84c941e6807483480e725225024079920d2812034e90714c901a74834a64809bc33a532404ee11d2992026e8ce14c9013b4470a6480bd203e522204ee31d2911027618e948881e34a4483440f9403a41a205e631d285102f294f90288178407c81440bca63e40a2076b291281103b4948940881f24834a0440fc250a502207e3205281102f510e940881f28674a0440fc213a502207a9291201103c49069008817a8a7480440bd253a402205e509f299102f480f94c881738674a6440bca13a532207e12810991037394c84c881798a7426440
  | _ => 0
def u131K6 : Nat → Nat
  | 0 => 0x1f3210f973a223d20b7cddf2360f9da8085d39e1849f1d7ce1f2f0cf82ad26f84831cb1a1400e4e256cacb3e7cf0c1502a550a7cf933e7c1c13e7cf9f1a7cf9f207cf9f217af883e1af913e7cf9f337c6df3e7cf9f3e32f98be3ed5f3e7ca000f013100331021010bf466ca4bf406ca4bf8664a4fb8464a4bb8464a4bf8064a4bf486ca3bd426ca3bf8864a3ef4a4483f7ca3483f74a3483bfca6483bf8a6483bf4a6483bf0a6483e74a4483f7ca6483f78a6483f74a6483f70a6483f7806483f7406483fd4a34a1bd8064a1fdca3c81fd4a3c81bd4a6c81bd406c81df4a4ca0f7483ca0fdc81ca0bf486ca0bd426ca0dfca44a0df4a44a0f74834a0fd4a14a0fdc814a0bf8864a0f78664a0b78664a0fd4264a0bd4264a0ef4a4480e7483480fe4a0480bfca6480bf8a6480bf4a6480bf0a6480fbca4440fb4a4440f3483440f94a1440f9c81440fa4a0440fa480440fbca6440fb4a6440fb486440f9426440
  | _ => 0
def u131K7 : Nat → Nat
  | 0 => 0x70c075b8257398e725c87384e711466850bfe527f4a4ff947fd28fbc41ff483ee907f5287ee40ffca0fe941fd203da207d420
  | _ => 0
def u131K8 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u131N : Nat → Nat
  | 4 => 20
  | 5 => 80
  | 6 => 62
  | 7 => 14
  | 8 => 1
  | _ => 0
def u131R : Nat → Nat → Nat
  | 4, i => packedAt u131K4 (i * 58) 58
  | 5, i => packedAt u131K5 (i * 45) 45
  | 6, i => packedAt u131K6 (i * 32) 32
  | 7, i => packedAt u131K7 (i * 19) 19
  | 8, i => packedAt u131K8 (i * 6) 6
  | _, _ => 0
def u131I : Nat → Nat → Nat
  | 4, h => packedAt u131K4 (1172 + ((h / 6 + packedAt u131K4 (1160 + (h % 6) * 2) 2) % 49) * 6) 6
  | 5, h => packedAt u131K5 (3756 + ((h / 26 + packedAt u131K5 (3600 + (h % 26) * 6) 6) % 102) * 8) 8
  | 6, h => packedAt u131K6 (2064 + ((h / 20 + packedAt u131K6 (1984 + (h % 20) * 4) 4) % 107) * 7) 7
  | 7, h => packedAt u131K7 (278 + ((h / 4 + packedAt u131K7 (266 + (h % 4) * 3) 3) % 25) * 5) 5
  | 8, h => packedAt u131K8 (7 + ((h / 1 + packedAt u131K8 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u131Pos : Nat → Bits
  | 1 => 0xffffc600f780e0fc00878420fff0024f0693ff
  | 2 => 0x8802083204304383f0604b38c9b1ccc
  | 3 => 0x108071c0083f85fc01800c3f0e3e0f0
  | 5 => 0xffffc80e00b8003cfc0060001ff8fc00fc00ff
  | 6 => 0x33f00f401fc300007fffe00f0000ffff00
  | 7 => 0x3dfff07fe003ffff8000000fffff000000
  | _ => 0
def u131Neg : Nat → Bits
  | 1 => 0xffffd83e00692544018d8c616a300245029155
  | 2 => 0x3eda9db3af6ee7d6fcb73e54b38c8b14cc
  | 3 => 0x3f6ca2132f4ccbbd7de25ea0c2d0a3a0f0
  | 5 => 0x2781f3128a09de20730c95c8d400fc00aa
  | 6 => 0x1400440011000020881090000544a00
  | 7 => 0xc8010b2204200100006292a000000
  | _ => 0
def u131Slices : List (Sig × Nat) := [(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x3333333333333333333333333333333333333333333333333333333333333333,6),(0x0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,5),(0x0303030303030303030303030303030303030303030303030303030303030303,5),(0x000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f,5),(0x00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,5),(0x000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f,5),(0x0000000033333333000000003333333300000000333333330000000033333333,5),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,5),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,4),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4),(0x0033003300330033003300330033003300330033003300330033003300330033,4),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,4)]
def u131Atlas : Atlas := ⟨8, rawDecor 238 u131Pos u131Neg, u131T, u131Slices, [], u131N, u131R, u131I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_4_0 : Interval u131Atlas 4 0 20 := block_range (n := 20) (by decide +kernel)
theorem all_u131_4 : Interval u131Atlas 4 0 20 := blk_u131_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_5_0 : Interval u131Atlas 5 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_5_64 : Interval u131Atlas 5 64 16 := block_range (n := 16) (by decide +kernel)
theorem all_u131_5 : Interval u131Atlas 5 0 80 := (concat blk_u131_5_0 blk_u131_5_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_6_0 : Interval u131Atlas 6 0 62 := block_range (n := 62) (by decide +kernel)
theorem all_u131_6 : Interval u131Atlas 6 0 62 := blk_u131_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_7_0 : Interval u131Atlas 7 0 14 := block_range (n := 14) (by decide +kernel)
theorem all_u131_7 : Interval u131Atlas 7 0 14 := blk_u131_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u131_8_0 : Interval u131Atlas 8 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u131_8 : Interval u131Atlas 8 0 1 := blk_u131_8_0
theorem cert_u131 : Complete u131Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u131_4 i (by omega) hi
  · exact all_u131_5 i (by omega) hi
  · exact all_u131_6 i (by omega) hi
  · exact all_u131_7 i (by omega) hi
  · exact all_u131_8 i (by omega) hi
theorem b_u131 : Lower true (vars 238) u131T 9 := by
  have ready : Ready u131Atlas (asRow u131Pos) (asRow u131Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u131Atlas, u131Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u81
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u68
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
    · exact slice_correct (ms := fixRows 64 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u31
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
    · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u15
    · exact slice_correct (ms := fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
    · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u20
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u107
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u44
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 76 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u35
  exact frozen ready cert_u131 (by decide +kernel) (by decide) [(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,64,72),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u132K4 : Nat → Nat
  | 0 => 0x1028c5928119c2992031a4a04470a6480
  | _ => 0
def u132K5 : Nat → Nat
  | 0 => 0x3252948927091282806937867406ca49ea63e40e506d52861992836b9030cc941378674a64809dc23a532406792802992026e8ce14c9013b4470a6480
  | _ => 0
def u132K6 : Nat → Nat
  | 0 => 0x4423d121144d45144b0d114439144030a1874504414491004bf406ca4bf8064a4bd4a6c81fdc81ca0bf486ca0bd426ca0fd4a14a0fdc814a0bf8864a0f78664a0b78664a0ef4a4480fe4a0480bfca6480bf8a6480bf4a6480bf0a6480
  | _ => 0
def u132K7 : Nat → Nat
  | 0 => 0x5c1cdc951dd9dd1ff293fa527d4a1fb903ff283fa507f480
  | _ => 0
def u132K8 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u132N : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 17
  | 7 => 7
  | 8 => 1
  | _ => 0
def u132R : Nat → Nat → Nat
  | 4, i => packedAt u132K4 (i * 58) 58
  | 5, i => packedAt u132K5 (i * 45) 45
  | 6, i => packedAt u132K6 (i * 32) 32
  | 7, i => packedAt u132K7 (i * 19) 19
  | 8, i => packedAt u132K8 (i * 6) 6
  | _, _ => 0
def u132I : Nat → Nat → Nat
  | 4, h => packedAt u132K4 (117 + ((h / 1 + packedAt u132K4 (116 + (h % 1) * 1) 1) % 4) * 3) 3
  | 5, h => packedAt u132K5 (408 + ((h / 3 + packedAt u132K5 (405 + (h % 3) * 1) 1) % 15) * 5) 5
  | 6, h => packedAt u132K6 (559 + ((h / 5 + packedAt u132K6 (544 + (h % 5) * 3) 3) % 30) * 6) 6
  | 7, h => packedAt u132K7 (137 + ((h / 2 + packedAt u132K7 (133 + (h % 2) * 2) 2) % 14) * 4) 4
  | 8, h => packedAt u132K8 (7 + ((h / 1 + packedAt u132K8 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u132Pos : Nat → Bits
  | 0 => 0xffffffd007ce01c7e000e000fff2001e0d33ff
  | 2 => 0x400918c81080c3f41045999323ecc
  | 3 => 0xffffffc038361e30e20f17c081f061e1c3c30f
  | 5 => 0xc008e00703f01800fe087e01fc03f0
  | 6 => 0x2f003100381c001fff000f8001fffc00
  | 7 => 0x3fffc1ffc01fffe000000ffffe000000
  | _ => 0
def u132Neg : Nat → Bits
  | 0 => 0xffffffc1d810b200040061091292000a053055
  | 2 => 0x374cfcd59db39dbc67c73459991216cc
  | 3 => 0x3a054144d9232b1cc2c96060a142430a
  | 5 => 0x3c278245192b7a1e94ed486a01f803a0
  | 6 => 0xb20208000c404318308a8000ada800
  | 7 => 0x2c0026d084802000051554000000
  | _ => 0
def u132Slices : List (Sig × Nat) := [(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x5555555555555555555555555555555555555555555555555555555555555555,6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,5),(0x0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,5),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,5)]
def u132Atlas : Atlas := ⟨8, rawDecor 237 u132Pos u132Neg, u132T, u132Slices, [], u132N, u132R, u132I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u132_4_0 : Interval u132Atlas 4 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u132_4 : Interval u132Atlas 4 0 2 := blk_u132_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u132_5_0 : Interval u132Atlas 5 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u132_5 : Interval u132Atlas 5 0 9 := blk_u132_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u132_6_0 : Interval u132Atlas 6 0 17 := block_range (n := 17) (by decide +kernel)
theorem all_u132_6 : Interval u132Atlas 6 0 17 := blk_u132_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u132_7_0 : Interval u132Atlas 7 0 7 := block_range (n := 7) (by decide +kernel)
theorem all_u132_7 : Interval u132Atlas 7 0 7 := blk_u132_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u132_8_0 : Interval u132Atlas 8 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u132_8 : Interval u132Atlas 8 0 1 := blk_u132_8_0
theorem cert_u132 : Complete u132Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u132_4 i (by omega) hi
  · exact all_u132_5 i (by omega) hi
  · exact all_u132_6 i (by omega) hi
  · exact all_u132_7 i (by omega) hi
  · exact all_u132_8 i (by omega) hi
theorem b_u132 : Lower true (vars 237) u132T 9 := by
  have ready : Ready u132Atlas (asRow u132Pos) (asRow u132Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u132Atlas, u132Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u82
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u73
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u71
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u70
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u34
    · exact slice_correct (ms := fixRows 64 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u33
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
  exact frozen ready cert_u132 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u133 : Lower true (vars 235) u133T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 235) (T := u133T) (xs := [(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u95
  have hc : (([(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u134K5 : Nat → Nat
  | 0 => 0x15cb935410795f92a4604a3cb4724f5a7f28991d72d4ca872e45a92c11358c5300ecc33c0ab921fb89bfe1bc73b72def72e5c8022d2db909cccc2b02f50a72e5cb972b7b2672e5cb919161ee65347469091cb972e58d25d36e08aa392b9718f38fe7e50b92bc52f972b5c90f247cb97269cb946e5c9e58e5cb9284dcb972e582aeb80fb9725d8433d5e076f2e5c80102801084a710000700013c4a0000e250c01181a60a63e8084678864a28f802119e21928a2f8884278064a28bc22109e01928a378684078864a18dc1a101e2192862f8884478664a18bc22111e1992874d4a48474a1481b5622128d285187554a38074a14619e802129d189107c94a44824a1441f4528d189285107c94a44a2481441f8520d1892051078b4a44824a6441e352912052991072b4620874a6441e2d2912892191078d4a44a14864418be22129d219107954a34a14664418be22129d1991062f0884a74664418fa02129d1991063e0084a74664418de1a109e119282370684278464a0b6a1a1289281103d24a34624a0440b692a11892811035a4a28874a0440e692892811991023e8084a74664409b422129d105083d44a34614a0420f61289105281083cc4a44a1480420fa1209105201083d44a34a1460420fc1189105181083954a34614a6420e5928d181299083354410674a6420cd920019d2990838d4a44a14864208ee12129d2190823b0484a7486420e5528d285199083964a34a04664208de1a129d1990839a4a24a04464208be22129d1190822f0884a74464208de1a129d119082370684a7446420
  | _ => 0
def u134K6 : Nat → Nat
  | 0 => 0x67e90f08c9433f4678464a19fa03c23250dbe21d119286de10e88c9439f4a38064a19fa43c03250cfd19e0192867e88f00c943778674064a1bb833a03250cfe31d2892079a948942903dd4a34a1481bec23a50a40cfe11d2992067f00e94c9033f8c74a4461bbc43a51a30cfe31d289187ba9489428c3d54a34a1461bec03a50a30cfe21d2991867f08e94c8c33f8074a64619fc63a52220df609d28d1067f18e946883db4a44a2441bdc43a51220dee19d289107d69489048837b4a7482441f9a51a31220fcd20d189106f694e8c4883dd4a44a1441eea51a50a20fe5209285107f28c49428837d8874a1441bec03a50a20fb5291205107da906902883f94a2481441fca31240a20df529d2051073e94894c883bb4824a6441dda31253220ef52052991067f10e94c883af8874a644197c43a53220ebc21d2991065e10e94c8833f8674a64419fc03a53220ebd2912191077694490c883bd4a14864419fc53a43220cfd29d2191067f0ce90c8833f807486441dba51a33220edd20d199107769448cc883bd4a14664419fc53a33220cfd29d1991067f10e8cc8833f4874664419fc03a33220d7e19d289283b69448c49415f4a74624a09fe63a312504ff31d205283ae9468c29413fcc74614a0eda51220a504ff31d1052837688308c9413f4878464a09fa33c232504fd09e1192833e94704c9413f4878264a09fa33c132504fd11e099282ef0ce84c941770674264a09fc63a522204fe31d28d103b69489448817b8674a2440f9a51a312207cd20d189102f694e8c48813f8c74a1440ef251a50220769289281103f48c49408817e8874a0440dda312532204fe21d2991027f0ce94c8813f8274a6440dda512332206f92811991027f14e8cc8813f4a74664409fc13a332205f609d2910827f18e9488413f8c74a3420bf403a512104fe31d289083ba948942841dd4a34a1420bec33a50a105f611d285083ea9468c2841f5483461420bea53a30a107e5289105083f2904882841f9462441420bea53a20a105f519d105083bc946940841de4a24a0420fe230a502107f1105281082fd10e9408417e8674a0420fe250a402107f1185201083f8882900841f64a3460420fb2312302107f1285181083f88828c08417e4a7460420cfa51a532106f51852990837a88294c841be4804a6420df2302532104fe21d2990827f0ce94c841b78674a64209bc33a532106dc19d2990826e0ce94c8413f8474a6420dea50a432106f51052190837c94090c8413f8a74864209fa53a432104fe11d2190836e9468cc841bd4a1466420df2502332104fe29d1990827e94e8cc8413f8874664209fc23a332106ed289119083768c488c841bd4a1446420df2502232106f92011190827f14e88c8413f4a74464209fc43a232104fd21d1190827f0ce88c8413f467446420
  | 1 => 0x6ca6b67d94b76594936cb65b28f6cb65b22eec9e1b2d907ce27f1dec8c8eab2ec9504bd96cb41b26aec955b2d96cb65b2d96ab65b22cbb3642ebd6c9907552ecb64c73008b65b29a4f765b2d96cb64b20db921db231ecb65b2d9279f58f99cab65ad906ca07917e47c597e75e195bb2d96cb65731d6a764389d27d6fb2346cb650bbc011b781d92ac8483beec801b2d92e765b2a0ecb646a4aeb270edd9543652e209ef65b2d93d451b29bebef2866a6bb4b74a16cb64b5206cb6524d96caed5ca191b659dbe25031b2c115a8837d95bf34782c4ec88c0d93c87cf422ec99d180b6c8901dd90c4b43c17c5b644c4eda00a87d953b64a377ec84a1e290ce12df583f6e5b2881ba62e3b61974f2b094feb12cd1b112ce88a00ced30b0129e6a21a4090bb2085ed2f5a6b3df647ad91bdb1b257c1665b2d94fa5f29d96ca2b7703a3c5b219e1d34c7dc915365b2d91b365b22adaf64e1d939de369d86cb6443396cb6450d911f65b2866cb65b2d96ca25956b99eb249aee35f06b151391c5748e624688d92f01997d96cb65b2d96ca99a406ab36507d90fe02c2490c2ae4f0bc5ce706d92f505b2b26c9a15f5030df740124458c84532d02bb2d902a1002d96cb11b26e14eaccaba8d8271dd96ca33b2d943dc014c76794e0bb097365b2d96c80298d92edf3b2d16c903b2c5068229cd96cab76dd9666ffb25f1b701b2d96cb3fb2d959b6570d96cb648c382cf6522348f765b2d918983a80cec8b6ba5fecb642630ec97184d90e6345e54ecaa551d96c4fc21aa88dfeb1d9266e2ded9374ee32c9b14bf0d73368f9b21ada95d6e07d8d42d3a6c72c4fec8240407993c6c1d4549b9601b2cb2900ce94db27374926bda73b277410a30aa3ecb65aba54a3648ac651b65b2d938aa9b2d96cabdb2d9269a5b2d952365b2d96cb6408d96c90136333316d4fce07013b2d932f4270008638008000600c08600a9021c800618a58209830a38010008031490028001409019008200010408018018028410000210003605a0a008209450210000602658080638000a38a50009eb8609010028028008210218240838020208018018010028ad1c3040013f4678864a29fa13c432514fd01e21928a7e90f0cc9453f4278664a29fa03c332515fa01d19928afc00e8cc9453f4878264a29fa33c132514fd01e09928adf10e84c9456f0874264a29fa43c032514fd19e01928a7e84f00c9457b8274a2462bdc03a512314fe09d29918a7f00e94c8c5be8074a64629f403a532316f801d29918a7c00e94c8c55f8874a34a1eba51a31250cff31d1892867e8cf10c9433f4478864a19fa03c43250edd18a1992867e90f0cc9433f4478664a19fa03c33250e7d29211928
  | _ => 0
def u134K7 : Nat → Nat
  | 0 => 0x7a028573184a794e493000579c348c822b9c0775582c51367e7611231984815e16783f5a0e7f9c8d74839c889c1f7b9c9c9c26482f9c106a71525f5c46253c5509248631372e9a1c4c8b65046968928f80509c535b919c7d9c9c22547c1a9b0f0d208a6044136c29011e4f6d66777294285615124d93083e2d47276e339c8e384b613b9c9c1b039c9c409c96429c5d3d9c9c069c3a9817399c0c0a67419c149c9c909c9c9c9c9c9c1d9c9c9c9c9c3597702a959962326410f1027471120881810010003400052420801b908b00b00508c00521928000701200f60ebf8864a2ff4864a2bf8664a2ff4664a2bf8264a2ff4264a2bf8064a2ff4064a2fb4a2462bf4a6462df4a44a1df4a34a1ff4624a1bf8864a1ff4864a1bf8664a1ff4664a1bf8464a1ff4464a1bf8064a1ff4064a1ff4a2481ff462481fd4a1481bf4a6481ff4a4461f74a3461ff4a2461ff482461fd4a1461bf4a6461ff4a4441ff4a3441ff483441fb4a2441fb482441fb462441fd4a1441fd481441bf4a6441bf486441bf466441df4a24a0ff4624a0ff4814a0ff4614a0ff4414a0bf8464a0ff4464a0bf8264a0ff4264a0ff4a4440ff4a3440ff483440fb4a2440fb462440ff4a1440ff481440ff461440fe4a0440bf4a6440bf466440ff4a4420ff4a3420ff483420ff4a2420ff482420ff462420fd4a1420fd461420fd441420fe4a0420fe480420fe460420bf4a6420bf486420bf466420bf446420
  | _ => 0
def u134K8 : Nat → Nat
  | 0 => 0x249949a36408a91a28088f293a5204a5207f4a2fe8c5fd287fa40ff461fe883fd283fa207f420
  | _ => 0
def u134K9 : Nat → Nat
  | 0 => 0x113f
  | _ => 0
def u134N : Nat → Nat
  | 5 => 57
  | 6 => 217
  | 7 => 78
  | 8 => 9
  | 9 => 1
  | _ => 0
def u134R : Nat → Nat → Nat
  | 5, i => packedAt u134K5 (i * 58) 58
  | 6, i => packedAt u134K6 (i * 45) 45
  | 7, i => packedAt u134K7 (i * 32) 32
  | 8, i => packedAt u134K8 (i * 19) 19
  | 9, i => packedAt u134K9 (i * 6) 6
  | _, _ => 0
def u134I : Nat → Nat → Nat
  | 5, h => packedAt u134K5 (3486 + ((h / 36 + packedAt u134K5 (3306 + (h % 36) * 5) 5) % 162) * 7) 7
  | 6, h => packedAt u134K6 (10593 + ((h / 138 + packedAt u134K6 (9765 + (h % 138) * 6) 6) % 606) * 9) 9
  | 7, h => packedAt u134K7 (2784 + ((h / 48 + packedAt u134K7 (2496 + (h % 48) * 6) 6) % 183) * 8) 8
  | 8, h => packedAt u134K8 (176 + ((h / 5 + packedAt u134K8 (171 + (h % 5) * 1) 1) % 26) * 5) 5
  | 9, h => packedAt u134K9 (7 + ((h / 1 + packedAt u134K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u134Pos : Nat → Bits
  | 0 => 0xfffffffffffe001c6018c03000ff402634c33f
  | 1 => 0xe1806300c0ff00013848fdcc
  | 3 => 0xfffffffffffe07022184430f000f09c18f0e0f
  | 5 => 0x3800c6018c000ff08e01f00ff0
  | 6 => 0x1c0031806300ff000f001fff000
  | 7 => 0x1fffc1ff83ff00000fffe000000
  | _ => 0
def u134Neg : Nat → Bits
  | 0 => 0xfffffffffffe6b42828010745159402214c115
  | 1 => 0xd9064c0001d13313012808554c
  | 3 => 0x1902d5008078326260940890e0a
  | 5 => 0x104b920302e0a8ca48a01e00aa0
  | 6 => 0x26d0a140382cc8c8d00176a000
  | 7 => 0x7c00000002494000000
  | _ => 0
def u134Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,7),(0x5555555555555555555555555555555555555555555555555555555555555555,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x3333333333333333333333333333333333333333333333333333333333333333,7),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff,5),(0x0000000000000000555555555555555500000000000000005555555555555555,5),(0x0000000033333333000000003333333300000000333333330000000033333333,5),(0x0000000055555555000000005555555500000000555555550000000055555555,5),(0x0000000000000000333333333333333300000000000000003333333333333333,5),(0x0033003300330033003300330033003300330033003300330033003300330033,5),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,5),(0x0055005500550055005500550055005500550055005500550055005500550055,5),(0x1111111111111111111111111111111111111111111111111111111111111111,5),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,5),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,4),(0x0000000000000000000000000000000033333333333333333333333333333333,4),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,4),(0x0000000000000000000000000000000055555555555555555555555555555555,4),(0x000000000000000000000000000000000000000000000000ffffffffffffffff,4)]
def u134Atlas : Atlas := ⟨9, rawDecor 235 u134Pos u134Neg, u134T, u134Slices, [swapRows 97,swapRows 83], u134N, u134R, u134I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_5_0 : Interval u134Atlas 5 0 57 := block_range (n := 57) (by decide +kernel)
theorem all_u134_5 : Interval u134Atlas 5 0 57 := blk_u134_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_6_0 : Interval u134Atlas 6 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_6_64 : Interval u134Atlas 6 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_6_128 : Interval u134Atlas 6 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_6_192 : Interval u134Atlas 6 192 25 := block_range (n := 25) (by decide +kernel)
theorem all_u134_6 : Interval u134Atlas 6 0 217 := (concat (concat blk_u134_6_0 blk_u134_6_64) (concat blk_u134_6_128 blk_u134_6_192))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_7_0 : Interval u134Atlas 7 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_7_64 : Interval u134Atlas 7 64 14 := block_range (n := 14) (by decide +kernel)
theorem all_u134_7 : Interval u134Atlas 7 0 78 := (concat blk_u134_7_0 blk_u134_7_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_8_0 : Interval u134Atlas 8 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u134_8 : Interval u134Atlas 8 0 9 := blk_u134_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u134_9_0 : Interval u134Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u134_9 : Interval u134Atlas 9 0 1 := blk_u134_9_0
theorem cert_u134 : Complete u134Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u134_5 i (by omega) hi
  · exact all_u134_6 i (by omega) hi
  · exact all_u134_7 i (by omega) hi
  · exact all_u134_8 i (by omega) hi
  · exact all_u134_9 i (by omega) hi
theorem b_u134 : Lower true (vars 235) u134T 10 := by
  have ready : Ready u134Atlas (asRow u134Pos) (asRow u134Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u134Atlas, u134Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u96
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u83
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u71
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u74
    · exact slice_correct (ms := fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u25
    · exact slice_correct (ms := fixRows 65 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u32
    · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u22
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 66 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u34
    · exact slice_correct (ms := fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
    · exact slice_correct (ms := fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u36
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
    · exact slice_correct (ms := fixRows 3 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u38
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u45
    · exact slice_correct (ms := fixRows 130 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u43
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u50
    · exact slice_correct (ms := fixRows 129 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 192 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u57
  exact frozen ready cert_u134 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,32,34),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u135 : Lower true (vars 231) u135T 9 :=
  lower_map (ms := [swapRows 80,swapRows 49]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u132
theorem b_u136 : Lower true (vars 222) u136T 9 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u131
theorem b_u137 : Lower true (vars 221) u137T 9 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u132
theorem b_u138 : Lower true (vars 219) u138T 8 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u133
theorem b_u139 : Lower true (vars 219) u139T 10 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u134
theorem b_u140 : Lower true (vars 215) u140T 9 :=
  lower_map (ms := [swapRows 80,swapRows 49,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u132
theorem b_u141 : Lower true (vars 207) u141T 9 :=
  lower_map (ms := [swapRows 80,swapRows 49,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u131
theorem b_u142 : Lower true (vars 186) u142T 8 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
theorem b_u143 : Lower true (vars 189) u143T 7 :=
  lower_map (ms := [swapRows 16,swapRows 33,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u128
theorem b_u144 : Lower true (vars 187) u144T 7 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u128
theorem b_u145 : Lower true (vars 187) u145T 10 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u130
theorem b_u146 : Lower true (vars 187) u146T 10 :=
  lower_map (ms := [swapRows 16,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u130
theorem b_u147 : Lower true (vars 183) u147T 7 :=
  lower_map (ms := [swapRows 16,swapRows 98,swapRows 99]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u128
theorem b_u148 : Lower true (vars 171) u148T 7 :=
  lower_map (ms := [swapRows 16,swapRows 49,swapRows 50,swapRows 83,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u149 : Lower true (vars 155) u149T 7 :=
  lower_map (ms := [swapRows 16,swapRows 49,swapRows 50,swapRows 83,swapRows 100]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
theorem b_u150 : Lower true (vars 126) u150T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 126) (T := u150T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u99
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u151 : Lower true (vars 125) u151T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 125) (T := u151T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u101
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u152 : Lower true (vars 123) u152T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 123) (T := u152T) (xs := [(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u117
  have hc : (([(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u153K5 : Nat → Nat
  | 0 => 0x27f3cf3cf32f14f1fc3cf18f3cf3cb85f061fc83c0bc4bcf0cf3c27c8bcf3c3bcf3c0fcf3cf2af3cf342bccfcf3cf3cf01f1de3c01e59093c708f366a1f31f3ce84b28f3cf26f3cf3c4fc831721000301108fa02111e09920e3e0084478264838f60a129e01920e3d0284a780648387e2a111e2191861f0a844788646187e2a111d2191861f0a84474864618fa02111d2191863e008447486461e9520d2060191869d8284830a6441aea02120c119283274830c74814608ee12129e2191823b0484a78864608ee12129d2191823b0484a74864608f60a129d2191823d0284a7486460e9920d2020991821fca80c748342087d2a031d20d0823bc480c74834208ed12031d20d083e4483481460420e9520d205199083a64834804664208bf3a021d19908327087867466420
  | _ => 0
def u153K6 : Nat → Nat
  | 0 => 0x157b5b5b58d2e21175c411d25b5b581b5b41bb5b47b14c4caa6ddb4bc5e45b56c0029b50ca534abb492c8628c57b4c69591b4ae3b9c1658be4d0bb422fc043e473959207cda9e71b48519b443b4aca104d87e76c1281fb37d3d2a309d06a8d1110e902f3e0ba854481218cc3c72baf89b54b0391a6c142bb4645c6033b5ae0d2d754fb5b5b50025b5b5b5b544a207b5b522348388c378f5b4b95a267953b595a0b549275141b599b5b1b469b44f02e5b512f14ce0ce02eb702c98886e96ed6531b451b5ad61474281a4741169b409851f08e9b453b4d5b5b41cb3b408239205a10210448210400270060600070001220260a82c60218e106196b8207050a0802843080061821113f4078864a39fa43c03251cef11e29920e7688f14c9073f4078a6483bec13a53241df409d29920e7b04e94c9073d0274a64839fc03a53241c7f29e11920e3e94f08c9073f427846483bf403a23241df801d11920e7f04e88c9073e8074464839f003a23241cfd11e09920e7e80f04c9073f4a78064839fa13c03241cfd09e21918a7e90f04c8c53f8c74824619f863a41230f9520d2051875e90510c8c33f4478864619fa03c43230cfe11d2191867e88e90c8c33f8074864619fa43c23230d7e29d119186be14e88c8c31f8a74464618f853a23230cfe21d1191876e90700c8c3bd4818064619fa43c03230dbe21d019186de10e80c8c377867406461bec13a41a20cff31d20d1067e18e9068839f4838a6441cfa41853220cfd21e199106fd00e9069413fcc74834a09f863a41a504fd21e1992837690708c941bb4830464a09fc63a522304fc31d291183ce9069028c13fcc74814609fc63a40a304fc31d205183cc9069008c13f4878a6460bdc23a532305ec11d2991827f10e94c8c13b8474a64609d823a532306bd2922191827e94f10c8c13f4278864609fc53a432304fd29d2191827f04e90c8c1b7483826460df2404132304fd21e099182df10e84c8c16f087426460bbc33a132304fe31d20d0827e18e906841f5483461420bec43a30a105f521d185083ec9068c0841fc481460420bf443a302105f921d181083ea8c30cc841f6460866420dea40c332106f92021990827f10f0cc8413f487866420b7c43a332105bc21d1990836e9068cc841bd481466420df2402332104fe21d1990835f10e8cc8412f8874664209fa43a332106bc21d1990825e10e8cc841b7867466420
  | _ => 0
def u153K7 : Nat → Nat
  | 0 => 0x19392be4d41f2e5cb97296a61f271cb572e55378759c8b24e5c3921e433972e521a3daa1b3098381d4fe46ee017c3c57233c845ee41794008c1fa705c8c7239339724b41472e5c9313e5cb96ec46b972e5cad72e5cb971e539700d0da972e5ca2c23a3b972e5b39203dc9156a3cb9156513972e527910942f972e5cb92ab05094663c8fbcafcb972000c2000000020a04012030c014f11bf8864a3bf8064a3bf8a6483ff4a6483bf4a6483bf846483ff446483bf446483bf826483ff426483bf806483ff406483ff4834a2bf886462bf826462ff4834a1f7483461ff482461fd481461bf886461ff486461bf486461bf846461ff446461bf446461bf806461ff406461ff4834419f8a64419f0a6441bf866441ff4834a0bf8664a0bb8464a0bb0464a0ff4a4460f7483460ff4a1460ff481460fe480460bf8a6460ff4a6460bf4a6460bf886460ff486460bf486460bf826460ff426460ff483440ff461440ff483420fd461420fe460420ff866420bf866420ff466420bf466420
  | _ => 0
def u153K8 : Nat → Nat
  | 0 => 0x85ad6716c0b0976b2916b5996b5692b3cd6b101fd28ffa41ff4a2fe8c5fd287fa30ff441fe941fd183fa207f420
  | _ => 0
def u153K9 : Nat → Nat
  | 0 => 0x113f
  | _ => 0
def u153N : Nat → Nat
  | 5 => 30
  | 6 => 109
  | 7 => 57
  | 8 => 11
  | 9 => 1
  | _ => 0
def u153R : Nat → Nat → Nat
  | 5, i => packedAt u153K5 (i * 58) 58
  | 6, i => packedAt u153K6 (i * 45) 45
  | 7, i => packedAt u153K7 (i * 32) 32
  | 8, i => packedAt u153K8 (i * 19) 19
  | 9, i => packedAt u153K9 (i * 6) 6
  | _, _ => 0
def u153I : Nat → Nat → Nat
  | 5, h => packedAt u153K5 (1796 + ((h / 14 + packedAt u153K5 (1740 + (h % 14) * 4) 4) % 99) * 6) 6
  | 6, h => packedAt u153K6 (5253 + ((h / 58 + packedAt u153K6 (4905 + (h % 58) * 6) 6) % 219) * 8) 8
  | 7, h => packedAt u153K7 (1944 + ((h / 30 + packedAt u153K7 (1824 + (h % 30) * 4) 4) % 155) * 7) 7
  | 8, h => packedAt u153K8 (214 + ((h / 5 + packedAt u153K8 (209 + (h % 5) * 1) 1) % 30) * 5) 5
  | 9, h => packedAt u153K9 (7 + ((h / 1 + packedAt u153K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u153Pos : Nat → Bits
  | 0 => 0xffffffffff0071f60900001e1ff0634c03333f
  | 1 => 0x638e003603e1e1e000848f0dcdcc
  | 3 => 0xffffffffff80003124fc000001f318f0ce0e0f
  | 4 => 0x1c0fcbc7001e01fe0c1f00f00ff0
  | 5 => 0x1ff00df8001ffe000fe000fff000
  | 6 => 0xe0000e00ffe000000fffff000000
  | _ => 0
def u153Neg : Nat → Bits
  | 0 => 0xffffffffff9504084020a02a2b10214c011115
  | 1 => 0x8c1041800460626230008505454c
  | 3 => 0x68b2c1241c46c4c4e10890ce0e0a
  | 4 => 0x22e01438490a0194441e00500aa0
  | 5 => 0x400ba207921594008bc000aaa000
  | 6 => 0x134d3e00e39919190ef76a000000
  | _ => 0
def u153Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x5555555555555555555555555555555555555555555555555555555555555555,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,7),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x3333333333333333333333333333333333333333333333333333333333333333,7),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,6),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,6),(0x0000000000000000333333333333333300000000000000003333333333333333,5),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,5),(0x0000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00,5),(0x0055005500550055005500550055005500550055005500550055005500550055,5),(0x3333333333333333000000000000000033333333333333330000000000000000,5),(0x5500550055005500550055005500550055005500550055005500550055005500,5),(0x0000000000000000555555555555555500000000000000005555555555555555,4),(0x0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff,4),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,4),(0x0000000033333333000000003333333300000000333333330000000033333333,4),(0x0000000055555555000000005555555500000000555555550000000055555555,4),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,4),(0x000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,4),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,4),(0x0000333300003333000033330000333300003333000033330000333300003333,4),(0x0000555500005555000055550000555500005555000055550000555500005555,4),(0x0033003300330033003300330033003300330033003300330033003300330033,4)]
def u153Atlas : Atlas := ⟨9, rawDecor 123 u153Pos u153Neg, u153T, u153Slices, [swapRows 84], u153N, u153R, u153I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_5_0 : Interval u153Atlas 5 0 30 := block_range (n := 30) (by decide +kernel)
theorem all_u153_5 : Interval u153Atlas 5 0 30 := blk_u153_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_6_0 : Interval u153Atlas 6 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_6_64 : Interval u153Atlas 6 64 45 := block_range (n := 45) (by decide +kernel)
theorem all_u153_6 : Interval u153Atlas 6 0 109 := (concat blk_u153_6_0 blk_u153_6_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_7_0 : Interval u153Atlas 7 0 57 := block_range (n := 57) (by decide +kernel)
theorem all_u153_7 : Interval u153Atlas 7 0 57 := blk_u153_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_8_0 : Interval u153Atlas 8 0 11 := block_range (n := 11) (by decide +kernel)
theorem all_u153_8 : Interval u153Atlas 8 0 11 := blk_u153_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u153_9_0 : Interval u153Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u153_9 : Interval u153Atlas 9 0 1 := blk_u153_9_0
theorem cert_u153 : Complete u153Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u153_5 i (by omega) hi
  · exact all_u153_6 i (by omega) hi
  · exact all_u153_7 i (by omega) hi
  · exact all_u153_8 i (by omega) hi
  · exact all_u153_9 i (by omega) hi
theorem b_u153 : Lower true (vars 123) u153T 10 := by
  have ready : Ready u153Atlas (asRow u153Pos) (asRow u153Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u153Atlas, u153Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u118
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u112
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u99
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u106
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u101
    · exact slice_correct (ms := fixRows 0 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u116
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u104
    · exact slice_correct (ms := fixRows 66 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u53
    · exact slice_correct (ms := fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u56
    · exact slice_correct (ms := fixRows 64 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u55
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u40
    · exact slice_correct (ms := fixRows 2 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u52
    · exact slice_correct (ms := fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u39
    · exact slice_correct (ms := fixRows 73 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u51
    · exact slice_correct (ms := fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u49
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u50
    · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u47
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u46
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u57
    · exact slice_correct (ms := fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u45
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u58
    · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u43
    · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 74 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u41
  exact frozen ready cert_u153 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u154 : Lower true (vars 119) u154T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := vars 119) (T := u154T) (xs := [(inputs.getD 0 zero,16,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u102
  have hc : (([(inputs.getD 0 zero,16,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u155 : Lower true (vars 111) u155T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 111) (T := u155T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u109
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u156 : Lower true (vars 95) u156T 8 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u155
theorem b_u157 : Lower true (vars 63) u157T 7 :=
  lower_map (ms := [swapRows 16,swapRows 98,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u128
theorem b_u158 : Lower true (vars 59) u158T 7 :=
  lower_map (ms := [swapRows 96,swapRows 81,swapRows 98,swapRows 99,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
theorem b_u159 : Lower true (vars 254) u159T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 254) (T := u159T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u123
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u160K5 : Nat → Nat
  | 0 => 0x1103dc019b6874869f44b836db60f6db6db6db61d4dafdb6db69454f65f6db6c76a8c85bd46a58c2c9b6b8a374db6da7db64b6d9e8d6db6cb60b6db6db3576dab3b68a4d8939000600211c02219c006649931102a1a529219d30324c9890148d31110ce98122e88b46a9094c00c74a0a1b495a45260234063a5050d84ad2293011a031d282c4d116a549808d018e94162608b52a4c04680c74a0b13645895260234063a50589922c4a93011a031d282c648962549808d018e94162a88b46a4c04480c74a0b15045a35260224063a50589a1ad31130122219d28262c9561d49889869808c133244b0ea4c44c34c0460a93075a62444a61a602304c712ac3a93113053011826708961d49889829808c17240eb4c44834c14c0460b13075a62261c44260230619a1a742a02622131d182e4881798898794310e8c172446bcc4ca14c0887460c1b260235064a54443a3060e93011283252a221d18306c9808d419295090e8c183a4c044a0c94a8487460
  | _ => 0
def u160K6 : Nat → Nat
  | 0 => 0xc10888684c7460e65ca10888684c7460d274c48898684c7460d664808898684c7460f264c44838084c7460e668888688084c7460e660888688084c7460e364c48688084c7460e74ca18688084c7460a7952aca14480c7460c794894294480c7460e3690a4c34c08a7460e364c39094c08a7460e274c44c34888a7460e2e4c44c04888a7460e364c34c04888a746086f08a4e9cc84a7460cb64c08698c84a7460cb64c38098c84a7460ca74c34890c84a7460cae4c04890c84a7460c2f4c74890c84a7460cb64c04690c84a7460cba4c04490c84a7460cb64c34090c84a7460ce64808698884a7460ce64838098884a7460a3e10a4c44c04a7460e3610a4c34c04a7460e364c31094c04a7460c3e92a4c00c84a7460c3e4c04890c84a7460c2e4c04890c84a7460c364c04690c84a7460c3a4c04490c84a7460e364c34c08884a746096746acc94a488746096e40acc94a488746096746a0c94a488746096b44a0c94a488746096e40a0c94a488746086f50a0c94a4887460b2640acc44c3887460b6546acc4ca1887460b6c40acc4ca188746096d52acc4ca1887460f25cc44c3ca1887460b2646acc44c0887460f264a44c34c0887460f2688a4c34c0887460e3690a4c34c0887460f344c34c14c0887460f2ccc4ca14c0887460f344c3ca14c0887460f264c38894c0887460e364c39094c088746087d52aca1cc8887460a2fd2acc44c8887460e2dcc4ca14c8887460a4f88a4c54a8887460e364c34c04a888746087b84a4c94a8887460c3e4c00c94a888746087746a0c94a888746087b44a0c94a888746087e40a0c94a8887460d274c4469cc7487460d2e4c4409cc7487460cb64c04690c8487460cba4c04490c848746087786a509cc5487460e274c41094c3487460f254c44c34c1487460f254c44c3ca1487460f264c44c34c0487460e3610a4c34c0487460f344c34c14c0487460f344c3ca14c048746087d52aca1cc848746087786a4c98c8487460c378c98694c8487460c678898694c8487460c754c18694c8487460c75ca18694c8487460c3e8c98094c8487460c768698094c8487460a3786a4c80c848746083f92a4c80c8487460d274c44690c8487460d364c04690c8487460d3a4c04490c848746087d52aca10c8487460c5dca14a90c8487460c5d82a4a90c8487460c75ca14690c8487460c79ca14490c8487460c7942a4490c8487460e274c44c38a8487460e364c34c08a848746087746a0c98a848746087b44a0c98a8487460e274c44c34a8487460e364c34c04a848746087786a4c94a848746087b84a4c94a8487460c3e4c00c94a848746085f4aa0c94a848746087746a0c94a848746087b44a0c94a848746087e40a0c94a8487460c578a98694a8487460c678898694a8487460c5e8a98094a8487460c768698094a8487460
  | 1 => 0x9488cc5460c670898694e8cc546085f4aa0e98884c5460c764694098e84c5460c764694098e84c446087792a4680e84c446087e92a4080e84c4460c5d82a4a90e84c4460c7942a4490e84c446096b44a0e94c44a446086f92a4c48e84a4460c764694098e84a44609574aa0e94c44c346097344a0e94c44c3460d364090e94c44c3460b174aa0e94c44c3460b3344a0e94c44c3460a670ea4c48884c34609670ea489cc5483460d664090e94c448346095d4aa0e94c44c146097944a0e94c44c1460b650ea4c44834c146095d4aa0e94c4ca146097944a0e94c4ca146087d50a0e94c4ca1460bb440acc44c3ca1460b650ea4c4483ca146095e4aa0e94c44c046097a44a0e94c44c0460d364690e94c44c0460b1e4aa0e94c44c0460b3a44a0e94c44c0460b360ea4c54c34c0460b360ea4c44c34c0460da64c48894c34c0460b660ea4c44834c0460f268ea4c44834c0460f260ea4c44834c0460da688a4c94834c0460d368ea4c94834c0460b3c0ea4c44c14c0460bb488a4c34c14c0460fa44c44834c14c0460bb44ca4834c14c0460bb446acc4ca14c0460bb488a4c3ca14c0460fa44c4483ca14c0460bb44ca483ca14c0460db44c34c9ca14c0460db24c38494a84c0460d364c38e94a84c0460ba688a4c38884c0460a6e0ea4c48884c0460ea64c44c38884c0460ae688a4c38884c0460ea688a4c38884c0460eb44c34c18884c0460eb44c3ca18884c0460d364c38e94884c0460ea64c48888684c0460da64c48898684c0460ce68884898684c0460ea64c49094c3480460ea64c41094c3480460ce64891094c3480460ae6d0acc5483480460ae650acc54834804609e652acc5483480460ce690a4c9483480460fa44c44c34c1480460be44ca4834c1480460fa44c44c3ca1480460be44ca483ca1480460de44834c9ca1480460ea64c4480468cc7460ce6480489468cc7460ee4483480428cc7460ea64c4483408cc7460ce6483489408cc7460f644834c14808c7460f64483ca14808c7460e274c44834c88c7460e2e4c44804c88c7460e664834804c88c7460c6dca10894c88c7460c670898694c88c7460ce64838098884c7460ce68698098884c7460ea64c44808684c7460ce64808898684c7460ea64c44838084c7460f254c44834c14c7460f254c4483ca14c7460f2c4c44c14804c7460f644834c14804c7460f2c4c4ca14804c7460f64483ca14804c7460d2e4c48098884c7460d664838098884c746087b84a4a98884c7460a6b84a4a88884c746086f92a4a88884c7460a2fd0a0c98884c7460d668698098884c7460a6ed0a8098884c7460a6d4caca18884c7460a6b84a4a98884c7460a6786a4a80884c7460a6b84a4a80884c746086f92a4a80884c7460a6d4caca10884c7460a37d0acc48684c7460f264c44808684c7460e654
  | 2 => 0x4c49c5f021b5285d650c7681e4c2464c9305b9324c931ae9305d931450fdd70616c5fc4652db18155884e350cdc65d96032e2a5510b5be4c7da4c7657c31c459324c20c224124c10dbc9324c0182635512802199324c078049324c4d9e922d21930365d0bb6f9532699a7723d86204930eb9324c65a4c378ed26e4c27ce65b6289310e06a4c4a8b763de19324c78a4c041d03887965cbf7a1a955e4c6144a93028679939314777d426914c930617a8d10dcf54891a364492e402589c08d86533cb203001039d81a55c05a4b7209e2a1107989021081931245f42c93085408329322752956611ef3917b384d38096e541599324c6b48f9316a294b56d0c66ed704156b221de36e1e051ab930fa9303c8820a9324c92575930a09324c9324c28a4c66c3a3010c818500203570104600339c1811a40002800001860000040c41091021ca38b00000920421b1031a00c80890410010c300500614e08810e20000010e0803cc0100041460f600010160e10024500808540e082346080bcd8c000054539f0000020cbb5804168074631a00224100004340300008318d02418600421604b800281080f46083145ca74c48694a88874c3ca74c48694088874c387b84a4a94088874c3a6786a4094880c74a3a7686a4894080c74a3e274c44c34888074a3c674894698e84c54839a78ca8894a84c3483d274c48e94a84c3483e274c41094c34a7483e274c44c38084a7483da54c48094c34834c1da54c48094c3483ca1ce58898694c8483ca1f254c44c34834c7ca1f254c4483ca1467cc09b686a4a98084c34c09b686a4898084c34c0cb64c34098884a34c0ca78898694c84834c0cba8c98098484a74c0cb34c38494a88674c0cb64c38094a88674c0cb64c38094888674c0d274c48694a48674c097640a8694a48674c097680a4698a88674c0d274c44698888674c097680a4698888674c0e274c44c38888674c087b84a4a98888674c087b84a4a94888674c0a6746a8894888674c0a6b84a4a78884674c0a6ecea8098884674c0a6b84a4a70884674c0ea64c44838084674c093e48a0e94c34c04a093ed0a0e94c34c04a093e0ea4c94834c04a0b2e88a4694c00c74a0b2e08a4694c00c74a0a3e90a4694c00c74a0a3e46a9094c00c74a0e364834c04680c74a0e3686a4c04680c74a0c3e92a4c04680c74a0c3e4c08894680c74a0c3e4c04894680c74a0e3688a4c04680c74a0e3648a4c04680c74a0e3692a4c04680c74a0e3652a4c04680c74a0e3612a4c04680c74a0e364c08894680c74a0e364c04894680c74a0e3a4834c04480c74a0e3a86a4c04480c74a0e3a46a4c04480c74a0e3a92a4c04480c74a0e3a4c04694480c74a0b3686a4c44c08674a0a3e10a4c44c08674a0a6786a4c44888674a0e2e4c44c04888674a085f4aa0e9488cc546087b44a0e
  | 3 => 0x24c8ae4c931fb9324c348506fc743cc343f0404f64c4ac626824c9324c9324c7de4c61a4c0b925361fc93233931892b56559d4d4f2459324c921285124c0f4fe9324c6020d7b05421cf654971321f0586467ea4c8e24c841079307c3c88a9324c4fa4c9324c9319f9303063130931e49310a3b8609324c930cc579c32a9c9634975e190401aa931a743df3298df68d4e9324c5264c931cb71e4c931a6480272e1796864a86d98445489324c1ca0c8b0f94324c1655a1220e851b7818e00e070002472d1ee0aa4c4c8ff8d23c5195b930c19314148df54e0779324c930961c40a744f7275ac2f8e59300d1cd2e2bcea68a228e4937b60904a30930670714f1ec4c930b690c662ea4c311da696293724435c805989c7164c9324c57cb332a4c139085a24c9319493163170fd404cd8695d780393d0566cc5e3bc586f489191c43159161e086e98a1e97a930c230d3a891557e4a41fc077051e07c684501d1f4ec6e203804f867131475d27304d6061236a4c1b19239cd63c21f7d24c5f9f2674bc5dc4b775cd3a4154715116a421ad881ba26261d35a50360cac87086301f888540664781a9068b4e83c5151f8ab7fcce859174b1b273ce31d5e78548c7f8c98e8ae2363e250928b9e5904204992d62db9900dd05d8e459b0875c20c4bd93055265ca85e4c930a95ccd078d0d4264c7c5729324c93134590d44664c930fb6a06d0f91b110576da329324c931af9324c28d952098247e4c14a4c23a4c738a7461292c1d49324c93042930631bc95092
  | _ => 0
def u160K7 : Nat → Nat
  | 0 => 0xd31529221d182b7e64a52443a3056f0c94a4887460e4f98898710e8c1d9d29130e21d183b3c44a61c43a306779094c3887460eea98698310e8c1db731328621d183baa61e50c43a3057d4c9ca1887460e5d98898110e8c1db929130221d183bb261a60443a307364c34c0887460ef898298110e8c1df328530221d183b7444a60443a3067e9094c0887460cfb94399110e8c11fd2a732221d1823ea14e64443a3062fcc44c8887460cde94899110e8c19f530532221d1833ee50a64443a3047f8a94c8887460cdf11299110e8c197d3152a221d1833ba61a54443a3067e4c04a88874608ff99295110e8c11fe3252a221d1823fa64a54443a3047f0c94a8887460f4e98898690e8c1eb931130121d183db261a60243a3072f4c4cc7487460aee8d398e90e8c15f50a731d21d182bf204e63a43a3072f4c44c74874609ee8d399090e8c13f50a732121d1827f204e64243a3047f4e9cc8487460d6e98719090e8c1af930232121d1831fe63c64243a3063f4c78c84874609df11299090e8c13de1a532121d1827f404a64243a3047f8e94c8487460d6e98619090e8c1af930032121d1831fa63864243a304dfca90c84874609be95219090e8c13dd1a432121d1827da24864243a304fd4290c8487460cbe94f15090e8c13de1a52a121d1827f404a54243a3047f8e94a8487460aee8d398a90e8c15f902731521d1823fe84e62a43a3047f509cc54874608ff21298a90e8c11fc42531521d183b3a62261a43a307274c44c3487460cee21298690e8c1dd530d30521d183baa61e50a43a3057d4c9ca1487460eec98698090e8c1cd930d30121d183be260a60243a3077cca14c0487460aee8d399090e8c15f50a732121d182bf204e64243a3067dca1cc84874608fe95399090e8c11f50a732121d1839ba61c64243a3073e4c08c8487460c7f99119090e8c19f530632121d1833ee50c64243a3047f4c98c84874608fe95319090e8c15de1a532121d182bf404a64243a3067d4c14c8487460cfb94299090e8c18fe32532121d1823fc54a64243a306778694c84874608ef0d299090e8c19fa02532121d1839ba61864243a3073e4c00c8487460c7e99019090e8c157f2a432121d182afa54864243a305774690c8487460af689219090e8c15f50a432121d1823fe84864243a3067dca10c84874608bf95219090e8c11fd2a432121d1822fa54864243a304774690c84874608f689219090e8c11f50a432121d1833ba61c54243a3067e4c08a84874608ff99315090e8c11fe3262a121d1823fa64c54243a3047f0c98a8487460aef0d295090e8c15fa0252a121d1832fa62a54243a306774c34a8487460cfc98095090e8c11ff3252a121d1823fc64a54243a3047f4c94a84874608fe19295090e8c197e2a52a121d1833bc34a54243a3067e8094a8487460
  | 1 => 0x4444263a3072f0c98884c7460ecf0d311098e8c1dba02622131d18337a62c44263a3066d4c18884c7460cdb94311098e8c19be2a622131d18337a54c44263a305778694884c7460afd01291098e8c1db530422131d183b6e50844263a3066f8a80884c7460cde95011098e8c15bf42422131d18337a62844263a3066d4c10884c7460cdb94211098e8c1cdf3121a131d1839ba62434263a307754c18684c7460eeb9430d098e8c1dd92021a131d183b3c44434263a307670888684c7460cce1110d098e8c15de2261a131d182bba44c34263a3073e4c48084c7460eec90701098e8c1df328602131d183b7444404263a3076e0888084c7460eed0d101098e8c19da1a202131d182bf244c04263a3047d509ca10c7460cbb94295018e8c11fe2252a031d1832fc44a54063a3065d8294a80c7460cdb94391018e8c19f728522031d18336e50a44063a30679ca14480c7460cf691289018e8c19e50a512031d1823fc84a62453a307374c44c38a7460cef21298714e8c1cf931130229d1839b261a60453a3067e9094c08a7460c7e98999114e8c11fd22732229d1831fa62264453a3066f4c44888a7460cee98691114e8c19f930122229d1823fc64a44453a3047f4c94888a7460f6c98698094e8c1f9920d20129d182b7c44a63a53a3056f0894c74a74609ee8d399094e8c13f902732129d1823fa74e64253a306b74c38c84a7460d7c98119094e8c18fd31e32129d1827bc34c64253a304fe8098c84a74609df11299094e8c13bc22532129d1827bc34a64253a304fb8494c84a74609fd01299094e8c11fe3a532129d1835ba61864253a306be4c00c84a7460c7e98e19094e8c13bf22432129d18277a44864253a304f74690c84a74609f689219094e8c13f902432129d18373a41c44253a306ee4808884a74609ef0d311094e8c13fa02622129d1836ba62c34253a306d74a48684a7460dec9810d094e8c1bd92021a129d1827ba64c34253a304f74898684a7460ded0d101094e8c1b7931602129d1836f252404253a306f64c38084a7460dec90701094e8c13f932602129d1827f244c04253a3055f8894c54a74608fe21298894e8c1cdd31130d29d1833b884a61a53a3073e4c44c04a7460e6c98698094e8c19f842530129d1823fa44e64253a3047f8894c84a74608df11299094e8c11bc22532129d1823dc24a64253a3063e4c00c84a74608be95219094e8c11bf22432129d1823fa44864253a3046f4890c84a74608ee8d219094e8c11ed12432129d1823f204864253a3065f4c58884a7460cee98711094e8c19f930222129d1823fc64c44253a3047f4c98884a7460ced0d101094e8c15dd1a731621d182bf204e62c43a3047f509cc5887460adf11298b10e8c11fe42531621d182b7a54e62443a30567469cc4887460adc81398910e8c1d3
  | 2 => 0x884c0460fcc9069109808c17da1a5221301182bf474a442602307b6cc48684c0460f6c9890d09808c1fd13061a1301183fa650c342602306f68888684c0460dec9110d09808c17da2261a1301182fb244c342602305f6469cc54804609fda1398a9008c13f9427315201183f3262261a402307a64c44c3480460fcc9129869008c1bda42530d2011837b084a61a402307e6cc5483480460fcc98a9069008c179932520d201183fa261a60a402307e44834c1480460fe89879429008c1f9120f285201182fe264e50a402307a74c4483cc74609faa1394398e8c1eb931120331d183f3241a40663a306e7483488cc7460ddc90091198e8c1add3111a331d1837ae50a34663a306f6480468cc74609ef1128d198e8c13dd2251a331d1837aa41a14663a306fc480428cc7460d7c98881198e8c1bd920d02331d1837e650a04663a304fe889408cc74609fc91281198e8c18fe42531331d1839ea62650e63a3047d509ca1cc74608ff11295198e8c19f728522331d1823fc84a52463a307674c44838c7460eea90698318e8c1dd520f28631d182bea64e50c63a3076e4c44808c7460ecc90690118e8c1df130520231d183be650a40463a3063f4c44c88c7460cee90699118e8c19f728532231d1833f240264463a3047f8894c88c7460cde11299118e8c11bc22532231d1833bc34a64463a3047f8894a88c7460cde98891118e8c19f530522231d1833ee50a44463a3047f8a94888c74608fe95291118e8c1e9d31120d31d183d7262240263a307e64834804c7460dce90711098e8c1bb920222131d1827f404c44263a306ed4c18884c7460ddb94311098e8c1b9e1a622131d18377404c44263a3066f4e98884c7460dda98211098e8c1bb728422131d18373c44434263a306e70888684c7460d6f9890d098e8c1add3121a131d1837aa60c34263a306f5ca18684c7460dec9010d098e8c13de2261a131d1827ba44c34263a306ee8888084c7460ddc11101098e8c1bda1a202131d1835f262404263a306f64838084c7460df994301098e8c13f922602131d1829fe84e62263a3072f4c44a44c74608ff21294898e8c11fc42529131d183b3a62241a63a307274c44834c7460e7a98898298e8c1dd520d30531d1839ee62650a63a3073d4c4ca14c7460eea90794298e8c15f532728531d183b7262240263a3072e4c44804c7460ecc90690098e8c1df130520131d183be650a40263a3047f4898a84c7460adf11295098e8c15bc2252a131d182bbc34a54263a3057b8494a84c7460afd01295098e8c1cbd31222131d183b3a41c44263a3076e4808884c7460afd01311098e8c19bd31222131d18337a52444263a3067d4c18884c7460cfb94311098e8c11fe2a622131d1823fa54c44263a3076d4c18884c7460edb94311098e8c19be2a222131d18337a5
  | 3 => 0x9888c13dd1a63a13111827f204c7426223047f8a98e84c44608fe9531d09888c19dd1a63a13111833f204c7426223053f8c94e84c4460aef0d29d09888c19dd1a03a13111833f20407426223053fcc90e84c4460abf9521d09888c157d2a43a1311182bda2487426223057d4290e84c44608bf9521d09888c11fd2a43a13111822fa5487426223047b4490e84c44608fa8521d09888c157e3a5315291182b7e74a6225223056f0e94c44a44609ee8d39909488c13f90273212911823fe74e6425223047f4e9cc84a44608fe1d31909488c11fe3a53212911823f874a642522304f74690c84a44609f68921909488c13f90243212911823fe7486425223047f4e90c84a44609ee8d31d09488c13f90263a12911832fa62c7425223066f4c48e84a44608fe9931d09488c19dd1a63a12911833f204c7425223047f4c90e84a4460aee1d298a9868c16d902731130d182bb874a62261a307b64094c44c3460e6f1d29889868c1cdc3a531130d183d3a62252261a305b78c94a84c3460bed0129509868c15de3a52a130d183d3a62444261a306e74c48884c3460bed0129109868c15de3a522130d183db262404261a306f64888084c3460bec9130109868c179d22731520d182fb204e62a41a30577ce9cc5483460aee9d398a9068c13dd42731520d183f3204a62241a307678e94c4483460ece1d29889068c159c3a531120d18373c44a64241a306f68094c8483460cef1d29909068c15f73a5311305182bec74a62260a3057d0e94c44c1460f6a9889869828c17d622530d305183f2a62241a60a305f54c94834c1460bea8d39899428c17f1027313285182bee74e62650a3057d4e9cc4ca14609faa139899428c15f73a5313285182bec74a62650a3057d0e94c4ca1460f6b9889879428c1ed531130f285182fac44a61e50a307f48094c3ca1460fca9889079428c17d532520f2851837aa61a64650a306f54834c8ca1460afc1d298a9808c16d91a7311301182bf074a622602307b64694c44c0460e7d1d29889808c1cf83a5311301183d72622522602307b64c54c34c0460f6c9889869808c17da22530d301183db252261a602307b68a94c34c0460f6c9529869808c1eda22530d301182db444a61a602307b64894c34c0460fcc9889069808c1e9931120d301182fb264a41a602305b64c94834c0460f789889829808c1ed130d305301183fa241a60a602307bccc4ca14c0460f789899429808c1fd130f285301183da261e50a602307f4483ca14c0460bf89939429808c1ed930e2a1301183db261a542602305be8c94a84c0460bed0d29509808c17ea1252a1301182bf474a542602307ae4c48884c0460f6c9871109808c1bb93122213011837b261c442602306b64c38884c0460df89831109808c1bf32862213011837b434c442602307b64c34
  | 4 => 0xd3033ba61c44433a6067d4c18888674c0cfb9431110ce9811fe2a622219d3023fa54c44433a606774c34888674c0cfa9829110ce9819f728522219d3023fc54a44433a6047f4a94888674c0cdf1129110ce9812ff42731119d303d3a62241a33a6047fd098a74674c0af709294e8ce981cbd31221d19d303b3a41a43a33a604bf8c94a84674c09df1129508ce9813bc2252a119d3027dc24a54233a604fe8094a84674c08ff1d29508ce981abd31222119d30376a60c44233a606edca18884674c0cdf14f1108ce9819bd29e22119d30357864c44233a606ee8098884674c097f1929108ce9813fa02522119d30277e84844233a606ed4c10884674c0ddb9421108ce9819be29c22119d30337a53844233a606e70888684674c0ddd1110108ce981bb822202119d3035f262404233a606f64838084674c0df99430108ce981bda19e02119d3027f254c04233a604fe4898084674c09be9130d098a9411ff3a622130d2829fa64e74261a5047f4890e84c34a09bf21298a906941e9d31130d20d2827f404a64241a5047f0e94c84834a0b7d112986980941cf83a530d3012829f074a61a602507b64c34834c04a0b7c992906980941ed930e1a1301282bf074c342602505ee8894684c04a0bdc1128d09809419dd20d1a331d2823fc44a34663a5047f489468cc74a08ff1130d098e9411fd2261a131d2833da41c24263a5073e4834c00c74a0e7d0d298018e941cf91a530031d2831f484a60063a506774834680c74a0c7c9808d018e9411fe2251a031d2823fa44a34063a506364c04680c74a0cef1128d018e9419dd2251a031d2833da41a24063a5063a4c04480c74a0cf68d289018e94157e22531619d282bbc34a62433a5047fd094c48674a08ff2129890ce9411fc42531219d2839f262260433a5067e9094c08674a08fe9131910ce9411fe22532219d2832fa62c44433a5067e4c08888674a08fe9931110ce94197d31522219d28337a62244433a5067e4c04888674a08ff1929110ce9411fd32522219d2823fe74a44662a3047f8e9488cc54608fe1d291198a8c13de2251a33151827f444a04662a306f6869408cc54608fe9139d198a8c13be2253a331518277844a74662a304f78694e8cc54608ff1129d198a8c19be2253a331518237c44a74662a3066f0894e8cc54608de1129d198a8c19de1a53a33151823fe74c44262a3047f4e98884c54608fe1d311098a8c11fd2273a13151827ba34c74262a304fe4098e84c54608fe9131d098a8c19dd1a63a13151833f204c74262a3047f4890e84c54608ff1d29519888c11fc3a52a33111837b434a046622304f78694e8cc4460cef0d29d19888c13dd1a62a13111827f204c5426223047fce98a84c44608fe9d31509888c1bd91a10213111829fa64e7426223047f4c9ce84c44608fe9539d0
  | 5 => 0x1c7b4490c84a74838fd81219094e9071fd02432129d20e3f204864253a41e678888684a7483cbe98b01094e9079dd30e02129d20e3fa64c04253a41cfd4098884c34c1d7a9890109869833f522602130d306f6c44a04261a60ded0894084c34c1beb0d2810986983e9531130d20d306fac04a61a41a60cfd8094c84834c19fb0129119879433f622502330f286dea04e62261e50fad4c48884c3ca19fa8131109879437d61a522130f2875ee62404261e50ebd4c48084c3ca19fa9130109879437b622502130f286f6844a04261e50fe54c44c3483ca1f4a988986907943f9622530d20f286fac04a61a41e50cfd409cc8483ca18fa9d3990907943bd61a532120f2867ec04a64241e50f3d4c44c34c7ca1afb11298698f9435f602530d31f287baa61a41a63e50d7d4c94834c7ca1a7f1d29109879818fe3a532120f302dec44a61e50e607b54c3483ca1cc0b7a9929079439819f520d3a32873023fe84a41a53e6047f4898684a7cc0e4e9889068cf981cf531328519f303baa41e50a33e6067dca1888467cc0cfb9429108cf9816de1a52a130d302df404a54261a6053f8e94a84c34c0b6f0d29109869816fa02522130d3035f244404261a605be4a98084c34c0b7c913010986981eda02530d28d3035ba61c44251a604fe4098884a34c08ff9d31109469811fd3a622128d3025fa64c74251a6063f4c98e84a34c08fe9131d0946981add30c3a128d3023fa44874251a607a74c44c34834c0f4f112986906981eda02530d20d3025fe74e64241a606b78694c84834c0d7d012990906981add30d2a120d3023fc74a54241a6047f0e94a84834c0b7b112986982981ed530d20d305302dea64a41a60a605bd489cc3ca14c0b7b112987942981ef202530f285303daa61a41e50a605bdcc9483ca14c0b7a992907942981af530d3232853027f404a34453a606774834688a74c08ff1128d114e9811fd2251a229d3035ba61c34253a604bf8c98684a74c0d7698709094e981aee32612129d3037d404c24253a606be4c38084a74c09fc8d301094e9816dd1a731219d302dbc34a62433a607b68094c38674c0f6a9869830ce981ed530f28619d302bdc24a53c33a6047f9094a78674c0e6e98710f0ce981add30e2a219d3023fe74c54433a606b74c34a88674c097f1929510ce9813ee1252a219d3027f404a54433a606b74c38888674c0d6e9869110ce9813fa02522219d3023fc84a62c33a605778694c48674c0e6f0d29890ce981cbd31129219d302bbc34a52433a6047f9094a48674c08fe2129490ce981cdd31130e19d3039ea62260c33a6073dcc4ca18674c0e7a9899430ce981dd530f28619d302bea64e50c33a605774698a88674c08fe9131510ce9815ee1252a219d3023fc44a54433a6047b8494a88674c0e5e9891110ce9815dd1a622219
  | 6 => 0xff1928d100e98b1fe2251a201d3163fa04c44253e61c7f4898084a7cc3adf11281090f9875de1a502121f30ebbc34a44203e61eb7869408cc44c39ef0d291114e9873de1a502229d30e3fc04a44453a61c7f8894088a74c3d5e98911094e9872fe32622129d30f5ba62434253a61cf74898684a74c39ee8130d094e987e9e1a531221d30e3fc84a53c43a61eaf4c44a88874c397f19295110e9873de1a52a221d30f57a62204443a61cf78694088874c38ff21298b10e9871fd0262a221d30e3fc04a54443a61c7f8a94088874c38fe95281110e9871ff42629d21d30e5fc64a54243a61cf78694a84874c38ff1d295090e9873dd2a61a121d30e7ba04c34243a61c7f9094a78074c397f19295100e9873de1a52a201d30e7bc34a44403a61c7f9094c58074c38fe91315100e9871fe2252a201d30e3fc54a44403a61c7f4a94888074c3d6f0d198880e9872ff42731101d30e3fe84c53a03a61f2f4c48874074c397f19295080e9873be2252a101d30e77844a54203a61cf78694a84074c39f709295080e9871fe3a52a101d30f57a62444203a61e6f8a78884074c3cde94f11080e987abc32622101d30f73c34c44203a61e6f8a70884074c3cde94e11080e987b9e2221a101d30f73844434203a61cdf4098884c54a39be91301098a9471ff3a602131128e9fa64e74262251c7f4090e84c44a3b6f012988986947cdc3a531130d28fd3a62444261a51de78894084c34a3bce1128109869471fe02522331d28e3fc44a04663a51c7f4098884c74a38fe91301098e9471fe02522031d28f37c04a44063a51e6f4094880c74a3cf691289018e9479ed02512031d28e3fc44a04063a51e7e8894080c74a3cfc91281018e94757e02531621d28f3bc84a61c43a51c7f4098c88874a38ff01299110e94797d31502221d28f3ba61a04443a51c7f8c94088874a3abf11298b00e9471fe42531201d28e3f884a62403a51f374c44c38074a3cef21298700e9471fe22532201d28f2fa62a44403a51e6f4c44888074a3cee98691100e9471fe32522201d28e3fa64a44403a51cf7809468cc54838ff1d281198a9071fe0253a331520e3fa74c04262a41e774698e84c54838fe8131d098a907e9d31531130d20fd3a62454261a41fa74c44a84c3483b6f19295098690779e2252a130d20ebbc74a54261a41de74098884c3483f4e989010986907b9d31202130d20f53a62404261a41fa74c44084c3483dcf11081098690779e22502130d20e3fc04a54663a41c7f4098a84c7483a7f19295098e9075de1a52a131d20fb3c44434263a41e678888684c7483aee8130d098e9071fe2a602131d20e3fa54c04263a41d3f8c94084c7483aef0d281098e90757e02531529d20f93a62261a53a41e771094c34a74838fe81399094e9071fe02532129d20e3ba34864253a4
  | 7 => 0xf6158bd87b0808fc9c5b99f61ec0f91e73ddec17d1dc8d4a1e92f13af794c2b600f600abd87b05b1b30daa6bb860692ed7cf61ec3a96a4010d9359f507e3b5d61bf0161ade37c8884c703a17a8d18e7a06cde3ea8cec62172d2500a38957146515a553b8ca92d67306b536bd87b04c1513b17b096dec1877b0f6114b0d683817ec3d82d52a5a3fd87b067bec02a1fdd31d5b8b91555ba1bd85bf866e23d84cf90001252fb020e9abd86b6de0ab18806fb85e2e66fb0f608ac227b0b16344d4f25f61ec3047b09f0d172fe24aa4defd80302e66cbb2c14f61ec06b71fcc4ca7d87b01aa84bd87b0f606811e862f61ec3d87b0658f4effa86769c28a682c069333d8158f61ec3a1f5af61ec3d855957025e61eab9ecc0fcf9aea6c419e47b0c1f605987b03174f541f51b0bec3d8628e6fb06e45f8d08dc8bec7589898c3019e7aa289375000200000f00072b04050012201e03050a090e030418020000080d00000903020702050203011409000700070b0802000b01060105010c05130008000403030b01001802070e0226061b0207050e010700020611000210001e020001000505000306020b00126500013804000305000003081400070007000a1f0107020400130001000c04031202080e0408020000010b1100000709001c0a0502010101060000001000000003000c060c002d01021200010a06030208000d0503050400150600000502000700161903030a0c05000703150b0200060504000400000308210205000014192c0500030002010d020d01020401020202010007001c0101000401360001000802000706080d2102010105071202010b00120100011e05000802000300022a030201050e000100000a08040002040501030101010300021d0200260302000c000e01020b00000c1207020c01012006193e01000102000139190000000b1611010b000800490201030e091900111602070507060f4b00000208001902000000042100002c000701000b07060000000a080001020801040502080b00000b0505020c00010708040008151502000504063d01090001000006010b01050f2604000105000e000900040202010b02000403320136030300021e0003010e22220c11000f0300000900060c05000102001b04070800091900061100050011000517030e0d00000607061a0d05000f010a0a130c0025000001020000000201310d0000062d0126100e0004000500010b0f0000000a0d08a90300000d26040008012300050001001e040200020101030d041e030200010607080009002e020000000b8fe8131108cf98b1fd22602119f316b7c44a04233e62d6f089408467cc5aef0d28108cf98b1fd2261a101f316b7c44a34203e62d6f089468407cc58ff1929110ce98b1fe02522219d3163fc64a04433a62c7f8894088674c58
  | 8 => 0x486f61ec3d87b0bbace7d8642eeeb80572f6f607e677fb0451ec3d87b0938b1ec6fb0f6011bd821df619c1766df5a4a59b7aa176e95ad7d2a14a579ae1432cdec23e7b0f61763d862b2050153bbcb4e3d10ccfb02f22b7822c09e54a0939a5283d2811c7e086ef76838dac980ef43f63675d316502ba5ec0e9fb09f72795da31ee7254f25df82de02df513d3838d8eb04e5057fd82bcf60e8bd87b0dcce7c8d0f4ef27b698efaf608127006c04968f919c7acdd512e05896b98fd842d9ccea129a1639fd866ffb0dc0864959e2f61ec323211961ec39a38eebce6142735a52b3651592f6044fd87b0f61aefd81ba688947a6bcd830adbd0fb00f7ec3d87b07d737613b61b9d9027839df6046344ed9585ebf532bd52ecccb71d6121583d829b525ec3d86e8970d8fd8049583dfe0940cca0b7f6c74bef84440118f11163c637abddde1eea2755dd980e1cce4b19b1c0aff75a5b1ba44bf6150639e013efbcd83a9c498cbc60240a2352248c49d58df5ff9e1b3a857a00c544a5ea008c93aa7d99f4763601db57c2fb2c32a04b3246be5b86de4aac9404517ca1772b7a0d01703ab457b0f61ec3d83fc5cdec3d809cbd8eb3d82a0b976dfd87b0f61207d82a9346d5958e55cbd06cba1b674a48d1094ce8bec3d846392fec28fa98a740187655df18a2f6da477ae724ec3e4ded7b6bac82471be00028a06c335f450df61ec2aa7b0315690f1f97eb29960ae968f5315cd8474695af25281c456c4da6333f83f50448b13c8caf8671f5b665ea0c38077e7afe0a7ce5b59d850e71735e8a01f601aacdf6859849bd80df674cf0a5fb06998355140f82063bd3c0e91b0e3d816ff61ec0c40166f858a1d9ebb4fec151fb093fac152c1df60fa4cc540b8fec1a8471e3c8e86d89fd758dea3fb0859ec0707b0975bcbd821c53bec0643c738ddb25a7b086183ba32095fd8bbc6f78f61ec39651dd1c86b54fb06d4ee12a7b0f6100bac72d5cbec3289975d2a6bd868239a8e74f391ed6b50cdad1483a5d1fef570b1ac0e1cb9a929c0c227b834cbc7453dbbc03c35a54ff10c463a63b74c356c19d4086cc6124ee5128b5e75029ec177fb0a9dec3bd92d022f32c4a4fc6bc2d70c8f98c4f9d3fb023742a27f14f61ec29bc6eb81ec3d87b0e7362a597164bdec1eb7b0ac2cda42ca89f9df6c07b0f407a4e40392fd3a3d8257a32efb22d716d01b9eefb0f60fdfd87b0f616d2276eaf61ec2cbeaa7fbec3d872bf60f049928eeedec1747b0b0dec3d851563e1d1586722e568bd8120a4893bd82794e9e685576ad01ec0e264cf5dec014576f60ecbd81008f1be772f55d9e880774591e5e429657f627440f66e27203ffd827df616d7d81b9b0575a2b05af61623d81711c4ad7d836ef61ec1d7fb050b7cfd8261e4e547d87b0357e50f7f2ee63c9b02fb0f602ae6bfb
  | 9 => 0xdb0cc6e72613d527f3b8aa54a8fa4779a612abc87b58a303a9c81fb35602f606a27a1c1258453a4ddef61144b47b07c7e0fd810df604eb9ea95f604205d810b5360d05864e79ec1769b8cb1ec0bda99f60391084420b9ec1017b0f60f973a457cb8d61f56d24ce3c465c40f6098b1d101ede8171c41addb43f0ae4e4fdb19ff170d4e47c51d45ef5df936fb0b39ec3d87b0f61bacc21bbe0a39bd8122a39ec109d78125ec223587f60c4bd800e97f99bd84ae6d301a60594db4bdf68f9970f2ecfc195eb7d4dacea5f60b75dd0c2e3bec1c7fb096ee58bb89639d6d97ea6611dea47cfb053db73d87b0e5f6bbae8e786c0fbd832bf60b5fd87b017d84bb1fb043f0f67ee3c127ec1edfb0a71af962fb0006a2494a4df61e27d8420a69ec0ac964e03ec3d8729f61ec2cfa36f61ec3d812ff6156bd870272a8318d27044497da393926be4e79c32f60643a789d5bc3e3d87b0f604abd87b0caf01f927b0f612a980cdcf60a210a206f147fca7d428cea9bd846698eb2bd86b2c6813bce7b0bfa17abbfb0f61ec07815bf60ab8137b027fbf25ec87213b86502bac08459c13480f16a8ab4316f4bd4d50f36aed505c8800a4dd48e95d857b27d8192b266923dd1bf61da52cfb0f619679f3262b9ec0c0f1bd8968592985301c43d87b0ada43e44d556c0e71297b040e2448f7b09b3ec366938f61ec1ee512c40a013da37f61249d0121f61ec3d87b03e88b3909550ebe6db8f15214d57c7fb084a37220b06a3c3be95fb0f60aa226bf302e838540ac868c5ae613b1ee3066c770b1dec22de14f606df35fb0c183aee2606f607eacf7b0f61782b81f15b6b3fd8694153ec3d833ff60514ce7b0f61ec3b7636f61267d8273f60ec3d87b0f61ec3d87b0f609f27d0b695ae869f383e0c35d1e0e9bdc898578ddf61ec09e54354e4c2ea9e0359b2bd87b05a06f1d4fb02c3ec3d8514131275957b07482fce17b0f61ec3241d1053a88b3989dd94f3d8764e9d2879967edabc2459991f61ec1b6293a09ec1187b066e3490f0b4f60c3fd820ddef9b6bf7b0f617a4cffb06fc265797b087e1a1f01044e5e8b3b3b36ca90e304905661f1b31d7811826e4cf1abdc83d810bd797416c9fb5f692787012875767544ca822a33d861bf600327ce6916b7d72a6e9d20b4c6a1426a7dc78cd794b4dd9d72f81d0d342404af61ec1557b0f60f60d37b06b618f497b0f61ec27ab020e46c7d87b0f60803d830547c028aa2f1b72d07d87b0f602992313d713ec3c2937a43ec3d83189ddec1e72b2f60b394841ef60ba98f7b06a308e2fb43e25ec2c803c8d3ec1e37b0454fbfd81289ffec1bc707f60f8aca9bdcf93b148ed38abb528bd20c52f08a879257f7da9d936207b2eff7b07a4779866187bf84dfd8a4f61ea916fb0f60890cd5b291929b843c384981e86667edaed683
  | 10 => 0x65d6f2874ea935ec308342f4dd2242134f47174d0aeb1cbca8d3b949da525de1753cb94acd0f65c9ec3d87a41c22c9ddc35780742221f3b611d2b47603e104fd87b08905abd87b0f604c7d87b0f60282ee45a5c51b3d846148a4330e66441fbfe5e1da7dbec05bf67f61ec31308487cf3e68b461eac90436fe9581f73d7b0c339373c79ef08ee62e49424bec17e36b344bc3d82c4d70c8a1761d327c3021255bb4089c9fb0611610abdfb3d0b9f60386142addb6963d9d543d80fc66be973755137d341fc9767a1c68e643c850c72b64457ddec3d87b0f61ec3d87b0f60f16ac7b0697ec3d8479f61ec0ad7b0ae55b934fb064e92dfa4648fef6a5cbd991c5117cf3b8733882073a6c5ec0ea1caf617e81022e668ae6abfb0f614cfd834f32dec24dfb0f61ec3d82c6f60c6fd845eb57d73278550f5ec3d82afe7fec37ee5b290582a370f789ec3d83f88433485e4374edb92affb077fbc6fbd4f0cce3275c54c2c29fd8621ab88ef25f4c03d357aba6820b8bfb37b0bdfec2d0282a2dec1f6248dbde6223bb1bd44cf089ad3bbec23e9df5e9ec1fa9fe801ec3d83793b3ec3d82420e1526a56b517b163d87b0cd1323c47b011fec0197b0f6135ad47b0f605948bfb0bf90a8dfa8db228a7d87b0593197d814ef61ec2dd0fbd34d4bcafb08e5ec171fb0f6092b99b144f1ec241fb0844ca3d87b0a114bb64518f6046488370735ec214db330eeabd87b0f61ec3c0fb08a11c3d87b07cc80f1f7b07bcd74a57b0f61ec3d87b0c886378c417f607a94fc6da72eaebed7372ed7cceb38ad54d63b8ded6374e4b07fddf3960fac84463eabd02ecdf7d2520da6bd4272ecfe430b5bd67916ceb73196e7d110294a11cd696b5fd7b07c395b1eeb9a4d6e0c36e3f6148858b77615c0e0e65ae39311a51c58d1533a3f74b3060f0589a708c25903a33ccd3b0f0d82fe20b7daf3d856992df368c43b58022fbe522a558cebaef29c92be2f0311c063021c74b4ea644d88281c71165a4b8d7a44f60dff91340f60b2d6d0d31b231ef154d1fc2e82651aab6d270f912947d04a998297c26f573c9bcacc6b787719f24e9fa6f129e09
  | _ => 0
def u160K8 : Nat → Nat
  | 0 => 0xff5311305183f54c34c1460fd520d305183fdcc4ca1460ff5313285183f54c3ca1460fd520f285182fd4c8ca1460ff9315301183becc44c0460ff9311301183be4c44c0460ff9291301183f64c34c0460ed930d301183f64834c0460ff1305301183fcca14c0460ffa2a1301183fe4a84c0460ffa221301182fe8884c0460ff9221301183f68684c0460ffb315201183fe4c5480460fd930d201183e6483480460ff1305201183fcca1480460efd31331d183f7483cc7460ff728731d183fe480cc7460bfd2a331d182ff488cc7460bdd1a331d182fd428cc7460bf902331d1833f4c4cc7460df728731d1827f4a8cc74609fd22331d1827d428cc7460dfd31631d1837f4c48c7460dfd29231d183774838c7460df530631d1837dca18c7460df920231d1827f4c88c74609fd2a231d1827f4888c7460eff31131d183bf4c44c7460fdd20d31d183fd4c14c7460ff728531d183fe4804c7460bfe2a131d182ff8884c7460fbe22131d182ef8884c7460fbc22131d182ef0884c7460fde1a131d182f78684c7460ffa02131d182fe8084c7460dfd31531d1833fcc44c7460dfd31131d1833f4c44c7460dfd29131d183774834c7460df530531d1837dca14c7460df920131d1837f8a84c74609fe2a131d1837f4a84c7460dfe22131d1827f8884c7460dbe22131d1826f8884c7460dfd22131d1836f0884c74609bc22131d183778684c7460dfa02131d1837dca10c746097f2a031d1827f4a80c746097d2a031d1826fc880c74609fd22031d1826f4880c74609ed12031d1827d4280c7460dfd31229d183774c38a7460df930229d1827fcc88a74609fd32229d1827f4888a7460f7d31529d183df4a44a7460fdd30d29d183f74834a7460ff930129d183fe4804a7460dfd31d29d182ffcc84a7460bfe32129d182ff4c84a7460bfc32129d182ff8884a7460fde1a129d182f78684a7460ffa02129d182fe8084a7460d7d31529d1837f4c44a7460d7d29129d183774c34a7460df930129d1827fcc84a74609fe32129d1827f4c84a74609fc32129d1837f8884a74609fe22129d183778684a7460dfa02129d1837fcc5887460dfd31621d1836fcc4887460dbd29221d183774c3887460df530621d1837dca1887460df930221d1827fcc88874609fd32221d1827f4a8887460fbd31121d183f74c3487460ff530521d183fdca1487460ff930121d1837fcc7487460dfd31d21d1837f4a7487460bff32121d182ff8c8487460bfd32121d182ff0c8487460bfe2a121d182ff4a8487460dff31521d1837f4c5487460ddd30d21d1837d4c1487460df728521d1837e4c0487460dff32121d1827fcc8487460dfe32121d1827f8c8487460dfd32121d1827f4c8487460dfc32121d1827f0c8487460dfe2a121d1827f8a8487460dfd2a121d1827f4a8487460
  | 1 => 0xc0afe22130d303bf4884c34c0efa02130d303bf4c44a34c0edd30d28d302ff8884a34c0bfe3a128d3027f8e84a34c0bfc3a128d3027f0e84a34c0fdd30d20d303b74c34834c0aff32120d302ff4c84834c0afd32120d302ff4a84834c0ef530d305303fd4834c14c0ef730f285303fd4c3ca14c0ef530f285303fd483ca14c0bf5323285303bf4c38a74c0bfd1a229d3037f4838a74c09fd1a229d303bf4c34a74c0afe32129d302ff8684a74c0bee12129d302fe8084a74c0eff31219d303bf4c48674c0fdd30e19d303b74c38674c0ff530619d303fdca18674c0dfe29e19d3037f4a78674c0dfe21e19d302ff8a88674c0bfd2a219d302ff8888674c0bfd22219d3037f4c58674c0cff31219d3037f4c48674c0cfd31219d3037f4a48674c0ddd30e19d3037d4c18674c0df728619d3037f8a88674c09fe2a219d3037f4a88674c09fd2a219d3037f8888674c09fe22219d3037f4888674c09fd22219d303bfcc44674c0efd31119d303f74834674c0ff530519d303fdca14674c0dfe29d19d3037f4a74674c0dfe21d19d3037f4874674c0bfe2a119d302ff4a84674c0bfe22119d303ef8884674c0bbe22119d302ff4884674c0fbc22119d302ef0884674c0fde1a119d303fe8084674c0bfa02119d302df8684c54a0efd31130d282ff8884c34a0dff3a130d2837f0e84c34a09fc3a130d282df8884a34a0f7d31520d283f74c34834a0bfd32120d282df4a84834a0bff3a120d283be4c34c04a0ff920d301283fe8684c04a0ff91a13012837f483cc74a09fd1a331d2837f4838c74a0dfd20d31d2827f8684c74a09ee12131d2837f4830c74a0cf930031d28277c680c74a09fd1a031d282774680c74a09ed12031d282ff4888674a0d7d31619d2837f4c48674a0d7d29219d2837e4c08674a09fe32219d2837f4c88674a09fd32219d2827f8888674a0dfd22219d2827f4888674a0bfd223315182f7468cc5460bf90233151827fce8cc5460bfd3a33151827f4e8cc5460bfe2213151827fce84c5460bfe3a13151837f8e84c54609fe3a13151837f0e84c54609fc3a1315182ff4a8cc4460bdd1a3311182fd428cc4460bf90233111827fce8cc4460bfd3a33111827f4e8cc4460bfe2a1311183f74684c4460ff90213111837fce84c44609ff3a1311182ff8e84c4460dfe3a13111827f8e84c4460dfd3a13111837f0e84c44609fc3a1311183df4c54a4460fbd311291182ffcc84a4460bfe321291182ff4c84a4460bfc3212911827fce84a4460bfe3a12911837f8e84a44609fe3a12911837f0e84a44609fc3a1291183f74c54c3460edf31130d183f74c44c3460edd31130d183f74a44c3460fde2a130d183f74a84c3460fde22130d182f78884c3460fdd22130d183f68084c3460fdf31520d183f74c5483460f9d31120d182f74c848346
  | 2 => 0x4c3efd31531130fbf4c48a74c3bfd22229d30eff4088a74c39fd22229d30e7f4088a74c3efd31129d30ebf8c84a74c3bfe22129d30ef78684a74c3bfe02129d30faf4c48874c3dfd29e21d30eff4a88874c3bfd02221d30f7f4c58874c39fe2a221d30f7f4a88874c39fd2a221d30f7f4088874c39fd02221d30f7f8a74874c3dfd29d21d30eff8a84874c3bfd2a121d30ff78684874c3bde1a121d30eff8084874c3efd31201d30f7f4a78074c3dfd21e01d30eff4a88074c3bfd22201d30f7f4c58074c3cff31201d30f7f4c48074c3cfd31201d30e7f8a88074c3dfd2a201d30e7f4a88074c3dfd22201d30e7f4888074c3eff31101d30fbf4c44074c3dfe29d01d30f7f4a74074c3dfe21d01d30f7f4874074c3bfe2a101d30eff4a84074c3bfe22101d30fef8884074c3bbe22101d30fef0884074c3bbc22101d30ff78684074c3b7e22131528edf8084c54a3bfe02131128f7fce84c44a3dfc3a131128e7f0e84c44a3edd31130d28ff78884c34a3fdd22130d28ff78084c34a3fdd02130d28e7f488cc74a39fd02331d28e7f8884c74a39fe02131d28e6fc880c74a39fd22031d28e6f4880c74a39ed12031d28e7ec080c74a39fd02031d28e7e4080c74a3bfd02221d28f5f4c58874a3ddd30e21d28e7f8c88874a3dfd32221d28e7f4c88874a3dfd02221d28e7f4088874a3bfd22201d28f5f4c58074a3dfd31201d28f5f4a48074a3ddd30e01d28f7f4c88074a39fd32201d28f7f4888074a39fd22201d28ef7468cc5483bfd02331520e7f4e8cc5483bfe02131520f7f8e84c54839fe3a131520ff74c54c3483f9d31130d20fa74c44c3483fde2a130d20ff74a84c3483f9e22130d20ff78084c3483bde02130d20ff74084c34839fd2a331d20e7d428cc74839fd02331d20f7f4c54c7483dfe2a131d20e7f8a84c7483dfd2a131d20f778684c7483dfe02131d20e7f8084c7483dfd02131d20f5f4c54a7483ddd30d29d20e7fcc84a74839fe32129d20e7f4c84a74839fc32129d20f778684a7483dfe02129d20e7f8084a7483ef531130d306fd8884c34c1ff522130d306fd8084c34c1ff502130d307f54c34834c1bf532120d306fd488cc3ca1bf502330f2867d4e8cc3ca1ef731130f287fd4c44c3ca1ef531130f287fd8884c3ca1bf622130f287fd4884c3ca1ff602130f286fd8084c3ca1ff502130f287f54c3483ca1bf732120f286fd4c8483ca1df530d31f2877d4834c7ca1afe22130f303bf4884c3cc0edd30d20f302bf4c8483cc0ef530f287303fd483ca1cc09f53a32873037f4834a7cc09fe1a129f3033f4c4467cc0ddd20d19f3037dca1467cc09fe22119f3037f488467cc09fd22119f3037d483427cc0bfe1a1315302bf488cc34c0efd31530d303bf4c44c34c0bfe22130d303bf8a84c34c0efd2a130d303bf8884c34
  | 3 => 0x2391807c0243b07c53722f8af16838c608c0b5526b868c11823009b24c182303c8694279c79cf898476303fe8c04ca022a02849d23021a8c0e7084b531181310e32673c19d3541b8c091a3031382cb807a9b86e1181bf9588c118114c608c1182304602911804b9aa8c0b614bbf38c04a184a598c118230460509182304600b6bea3038e143182304602f0406304608c1182304600b31805ec6079277dcb2c543a4dc4846080698e2c379811182304608c02523046030e73230460041182304607be369adc608c11807285a746854468765868ac709b18c1181954608c0ae52da6f8c0c862a080780792060a224044d5f8f24faaddb019e4fccb87b2cf0142d1c89a68c11808b25877318049c6046cb4d793ba319165f206678a81977ad66e3181bb80e5eccb2304605040ec41c608c0d08f9853764d31f83c11b31807d9188c0f5e3028111679c9dc606d9180112cb8c1182304608c11823015162004076c608c1181d603f33918040b828a489056c600301f2302cc48ae1630435425004e289c6a4ff48fad76a8f980d200205065e60ac09ee49c21de75ab42304608c06520ac608c01f4e84608c0764fb23b21ae9e2b0dd44ab28cb2e4614c012ea088c0154bd4608c00a603b0c6244161dac23405500a4608c1182304608c1182300fe8c08e8ebc607b854ce1ba558c2fd5d29f80a11c15a9912c125bd19756029c1a3bd7d8a46161f4590d70e73fa123050b8b306c8359764604ac99e300e726b182303187bd182304608c0d843c4608c1182304608c1181380e32d1180e04602c11800246086f1807bc608c0c8e304608c1182304608624a979c605a91807146041cd6487c602b7180e694f8c11805486a5104004000c00010034f0c100200238000104114318000928524040201c0003d62032c90811580043010064033a22c010008304408104100008404210000400104200500108008030414128205008708300014004140c0020820002830480c40cd0872810805c100310c08000f00318314000700004f0140910814c364004100238500100101b0400410c100000328e2c00c11400006850c02c21401011820041951885424c104344004010a00804010114005d00004704144204014124e20c3c914600060444b4c10004c21002000040000030001850c004a01b6440830060800030460022c50850010410ce4240833840010000c80c41c41410810002819fe22119f3177f488467cc59fe02119f3177f408467cc5dfe1a101f3167f868407cc5dfd1a101f316ff4888674c5bfd02219d3177f4888674c59fd22219d3177f4088674c59fd02219d316ff4688074c5dfd1a201d3167f4688074c59fe22129f30e7f8084a7cc39fe02121f30f7f408487cc3dfe22101f30e7f888407cc3dfd22101f30eff8884c54c3bfe02131530ebf408cc4
  | 4 => 0x601c01fe3029a2591823039a83b1821a3b67f318222460124af63031581681c77429726e2c2ea371a0f50eb222019180ee4601530894199f2c61d23046084d182304602ba2e2301b28902ee301da8c0f0a303a88c1181774608c11808221947e7ca303cd5a4ec05aabb34adb6300d58c09d4bfb948c11801288a148c7e3012118909ce09628c09392d4608c11023022e15663906b9b8c050ccd08485b0f4bb26d8c05f2304602dec79a246054832a0bb0457d1805799944ca4d8303a7f807dba4600f6dfa26c608c0c75db8508c00c4b697466d18079c5d4cc60a302a18c1182300408c1182304608c05781e16c37f18167460565181fbc606aad7a3046081a31a30460715181714604d26ae304605301bdca8d77b680e300de8bc5c23017e8c0a78608b12e47197b98109a139519858c104e24afb8c07a2304608c118230460521182303af7a3181e3c60320c5c142b51f21708f24f32a981609122ea518294608c1182301844bed5a079b778ccf85e06c2fa6d47eb1a4f63d05b8f18c05493c8351a6b75bd82a150988c6c43084829911ee7cf182154606cc952304608c1180c7c601c845630460273182302854e40c2304603d4179f7c608c041e3046071ac2e304608c11820fc602bebfa3046070f182301a88c118064ac78c1182304608c1182301493c1181a70544867d4ac86e75caa2302410af0c028bb807ccdcb38a3090ab9460f010ef86303578c057061b5a8c0f8a30460469171f94608c0acd259e98c0af0dda80082da0a004614a554c4b58824fd031a104a2fa5f0079184e80f61660ee269ee812794ae1708c01fe8b19e33427d0e5c80ec1d2c3a0d2b60c51160e4601544f2282448c1029013f187010ca518b8c1180c34608c11810c4608c07954b4608c0e22304608c0744d14608c0c82304606e7045198568c06bc221b38c1180914603cd181f29c88c1181291a179e78e3013a0008b4d1c608c03a09191421d1823044a8c0058b9c600d5104c89fa7f6e5cf84606811806e1bc8c10863010a559182304605cf182304608c07896f8828c11823021e7f0b9a3046060a3342faa68c1181139887321e8fc1646291813e4602dc726304605800b6301938c0a89e94608c1182304608c1182304608c0019c48d28c02223008e1124d9b73b5269182304608c1180e50397aa0dde82618c0d06303a28c11554a46018b1823043e4546f4a6a393fc2b819460840465101d3848a38febab0b11823036a3ab1823046022f17df5c3c5b90c8662e34aa0be300ea4aeba0c0183702ce2303ce1a885217a876a1180803d60c8c96303768c05309832d8c11823007e8c1180501c719708cb0acd7867b63036f8c0830c510b4609297a9068b67518ca68372fd9c639d8c0811191a777e1b5baa35296430b29a98c01c9cf82735a4963040083118025460
  | 5 => 0x42d180fe460515181b10b60663f081ba66f9182300868c0362304608c036e301e161a3449703d8c11823004589c2e88d9be8c114532c60850f10bdb03283182304607b056a1b3288c05392482c592fa93637d164f69d20758c0b7a303d98c0ef95a4608c0ea63013f8c10b8b50c827aa71e5a9206c0e18141e11e27d214604811823027f8c0d2180c3f172748a244670033ca3c4f12a37d46c0219cb951444b81c3e9cc06b2ac6c1f6c608c1024db2f08a7181ffbf58c0542302f42f2ac4599a462d180b482e8c09ce304605f01a1241388c0298e59ba4990ea3033a8c118230460884a223019b3311823023e755182304603d718123c608c11823046033b18038460768de17501c8c049df746038887d2f4604b911e03069820940b5924743182304608c11813d4608c0196300264f0f8dd8c608c031ced99203cc9077bd3638ece12a214c82651e2fc4122148d3087764bc5f2386e46b88880213b182301b42ee1cd838b05b5182303bc866a9e301ac385182300eb6a212c30c608c11814346068caa87321b8c0cc9f415728b181624607071813b4608c1182300988c0440840084d7182304
  | _ => 0
def u160K9 : Nat → Nat
  | 0 => 0x14c45779595955194553606f9941194019498f1314ed569954348d67e56a8b11cdc4b4a6c27944cb380b8d1616a0d94473e52d86891946588810ea44f94188394bb7d9594899451959415959595903595959584fc4195959595959578fe755d95959437959595670d939513003d7aae42ed95759564ee09596f4021397279148a3f948c939595959471941d94c42d95559431956d35953d2a63705f9595950994178b32487c2995959595959595959595871195959594e8cd953b1b958d942485959594a194592394239413941f959517940f95940a8f5395945b9595946195959595955a5d94c195951e9d959595942ee30a2aace5443995955746e19518c995959595949525279595043b94f52cb4bd94b7299594c60594e61b95959595219401200600a00000038a40218008019c28298200400c2402000003a0084000080d000801844020002ac0017f467cc5bfa03e62ffe19d316ff0ce98bff8074c5bfc03a62dfd29f30efe90f9877d427cc3bfa03e61ffd31530f7f988987ff4c44c3dfa62261ffe29d30eff14e987ff4a74c3ffc43a61dfe21d30ffe90e987ff8074c3bfc03a61ffd01d30fbe98a947ff4c44a3efa52251fdd30d28eff98e9477f8c74a3bfa63a51dfc31d28fff10e9477f8874a3ffc03a51dfe01d28fff98a907ff4c5483fba61a41dff31d20efe98e9077f4a7483fea61a60ff520d307fb987943fd4c3ca1fea41e50df531f2877e987981ff483cc0fee50e605fd29f302fe8cf9817d427cc0ffa62a606ff30d303fe986981bf4c34c0ffa51a607fd20d303fa982981fdca14c0ffc53a605fe29d303fe94e981ff8674c0bfc33a607fd19d303be98a941ff4c34a0efa51a507fd20d283fc9809417fcc74a0bfc63a505fd31d282fe18e941ff8674a0bfc33a507ff315183fe98a8c1ffcc4460ffa622307fd291183ee9868c1f7483460fea60a307f7285183fc9808c1fe480460ffe63a305ff31d182ff18e8c1ff4c7460bfa63a305fc31d182ff14e8c1ff4a7460bfa53a305fe21d183fe90e8c17f487460
  | _ => 0
def u160K10 : Nat → Nat
  | 0 => 0x1f899881c2852c610cc6311a0318c6318b631876200ffcc5ff4c5ffcc3ff4c3ff4a3ff483fd4c1fdca1ffcc0ff4c0ff4a0ff460
  | _ => 0
def u160K11 : Nat → Nat
  | 0 => 0xa7f
  | _ => 0
def u160N : Nat → Nat
  | 5 => 27
  | 6 => 294
  | 7 => 984
  | 8 => 560
  | 9 => 101
  | 10 => 12
  | 11 => 1
  | _ => 0
def u160R : Nat → Nat → Nat
  | 5, i => packedAt u160K5 (i * 85) 85
  | 6, i => packedAt u160K6 (i * 72) 72
  | 7, i => packedAt u160K7 (i * 59) 59
  | 8, i => packedAt u160K8 (i * 46) 46
  | 9, i => packedAt u160K9 (i * 33) 33
  | 10, i => packedAt u160K10 (i * 20) 20
  | 11, i => packedAt u160K11 (i * 7) 7
  | _, _ => 0
def u160I : Nat → Nat → Nat
  | 5, h => packedAt u160K5 (2380 + ((h / 17 + packedAt u160K5 (2295 + (h % 17) * 5) 5) % 92) * 6) 6
  | 6, h => packedAt u160K6 (22248 + ((h / 180 + packedAt u160K6 (21168 + (h % 180) * 6) 6) % 679) * 10) 10
  | 7, h => packedAt u160K7 (62936 + ((h / 610 + packedAt u160K7 (58056 + (h % 610) * 8) 8) % 2292) * 11) 11
  | 8, h => packedAt u160K8 (27818 + ((h / 343 + packedAt u160K8 (25760 + (h % 343) * 6) 6) % 1502) * 11) 11
  | 9, h => packedAt u160K9 (3669 + ((h / 56 + packedAt u160K9 (3333 + (h % 56) * 6) 6) % 288) * 8) 8
  | 10, h => packedAt u160K10 (245 + ((h / 5 + packedAt u160K10 (240 + (h % 5) * 1) 1) % 33) * 5) 5
  | 11, h => packedAt u160K11 (8 + ((h / 1 + packedAt u160K11 (7 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u160Pos : Nat → Bits
  | 0 => 0xc00000e00000007ffffc40000f01834c00ffff
  | 2 => 0x104300b81fe602041808b2ccc264c8fccb2cc
  | 3 => 0xc2083f15fe01804081fc0c30f03870f0f0c30f
  | 4 => 0xfc0060001ff80fe01003f00c07f00ff03f0
  | 5 => 0x3f000180001ffff00020fc000ff8000fffc00
  | 6 => 0x3c00001ffffe00000003f00000ffffff000000
  | 7 => 0x3fffffe0000000000003ffffff000000000000
  | _ => 0
def u160Neg : Nat → Bits
  | 0 => 0x400006010220009124440000500814c001455
  | 2 => 0xe39e79bf831fe2e3c78c8b2ccc224485ccb2cc
  | 3 => 0xc32cb71f8e05e564c9b80c3050285090f0c30a
  | 4 => 0x480dd206a448a980ec91003500407e005503a0
  | 5 => 0x937024194891567601220d4000bf0000aae800
  | 6 => 0x1c41004070e018183043500000d5ab6a000000
  | 7 => 0x20820880010000000000a28aaa000000000000
  | _ => 0
def u160Slices : List (Sig × Nat) := [(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,10),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10),(0x5555555555555555555555555555555555555555555555555555555555555555,9),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,9),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,9),(0x0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,8),(0x000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f,8),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,8),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,7),(0x000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f,7),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,7),(0x00000000000000000000000000000000ffffffffffffffff0000000000000000,6),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,6),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x00ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,6),(0x0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,6),(0x0000000055555555000000005555555500000000555555550000000055555555,6),(0x0000555500005555000055550000555500005555000055550000555500005555,6),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,5),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,5),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,5),(0x000000000000000000000000000000000000000000000000ffffffffffffffff,5),(0x0000000000000000555555555555555500000000000000005555555555555555,5)]
def u160Atlas : Atlas := ⟨11, rawDecor 253 u160Pos u160Neg, u160T, u160Slices, [swapRows 84], u160N, u160R, u160I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_5_0 : Interval u160Atlas 5 0 27 := block_range (n := 27) (by decide +kernel)
theorem all_u160_5 : Interval u160Atlas 5 0 27 := blk_u160_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_6_0 : Interval u160Atlas 6 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_6_64 : Interval u160Atlas 6 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_6_128 : Interval u160Atlas 6 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_6_192 : Interval u160Atlas 6 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_6_256 : Interval u160Atlas 6 256 38 := block_range (n := 38) (by decide +kernel)
theorem all_u160_6 : Interval u160Atlas 6 0 294 := (concat (concat blk_u160_6_0 blk_u160_6_64) (concat blk_u160_6_128 (concat blk_u160_6_192 blk_u160_6_256)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_0 : Interval u160Atlas 7 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_64 : Interval u160Atlas 7 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_128 : Interval u160Atlas 7 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_192 : Interval u160Atlas 7 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_256 : Interval u160Atlas 7 256 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_320 : Interval u160Atlas 7 320 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_384 : Interval u160Atlas 7 384 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_448 : Interval u160Atlas 7 448 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_512 : Interval u160Atlas 7 512 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_576 : Interval u160Atlas 7 576 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_640 : Interval u160Atlas 7 640 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_704 : Interval u160Atlas 7 704 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_768 : Interval u160Atlas 7 768 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_832 : Interval u160Atlas 7 832 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_896 : Interval u160Atlas 7 896 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_7_960 : Interval u160Atlas 7 960 24 := block_range (n := 24) (by decide +kernel)
theorem all_u160_7 : Interval u160Atlas 7 0 984 := (concat (concat (concat (concat blk_u160_7_0 blk_u160_7_64) (concat blk_u160_7_128 blk_u160_7_192)) (concat (concat blk_u160_7_256 blk_u160_7_320) (concat blk_u160_7_384 blk_u160_7_448))) (concat (concat (concat blk_u160_7_512 blk_u160_7_576) (concat blk_u160_7_640 blk_u160_7_704)) (concat (concat blk_u160_7_768 blk_u160_7_832) (concat blk_u160_7_896 blk_u160_7_960))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_0 : Interval u160Atlas 8 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_64 : Interval u160Atlas 8 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_128 : Interval u160Atlas 8 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_192 : Interval u160Atlas 8 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_256 : Interval u160Atlas 8 256 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_320 : Interval u160Atlas 8 320 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_384 : Interval u160Atlas 8 384 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_448 : Interval u160Atlas 8 448 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_8_512 : Interval u160Atlas 8 512 48 := block_range (n := 48) (by decide +kernel)
theorem all_u160_8 : Interval u160Atlas 8 0 560 := (concat (concat (concat blk_u160_8_0 blk_u160_8_64) (concat blk_u160_8_128 blk_u160_8_192)) (concat (concat blk_u160_8_256 blk_u160_8_320) (concat blk_u160_8_384 (concat blk_u160_8_448 blk_u160_8_512))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_9_0 : Interval u160Atlas 9 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_9_64 : Interval u160Atlas 9 64 37 := block_range (n := 37) (by decide +kernel)
theorem all_u160_9 : Interval u160Atlas 9 0 101 := (concat blk_u160_9_0 blk_u160_9_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_10_0 : Interval u160Atlas 10 0 12 := block_range (n := 12) (by decide +kernel)
theorem all_u160_10 : Interval u160Atlas 10 0 12 := blk_u160_10_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u160_11_0 : Interval u160Atlas 11 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u160_11 : Interval u160Atlas 11 0 1 := blk_u160_11_0
theorem cert_u160 : Complete u160Atlas := by
  intro k hk i hi
  change k ≤ 11 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u160_5 i (by omega) hi
  · exact all_u160_6 i (by omega) hi
  · exact all_u160_7 i (by omega) hi
  · exact all_u160_8 i (by omega) hi
  · exact all_u160_9 i (by omega) hi
  · exact all_u160_10 i (by omega) hi
  · exact all_u160_11 i (by omega) hi
theorem b_u160 : Lower true (vars 253) u160T 12 := by
  have ready : Ready u160Atlas (asRow u160Pos) (asRow u160Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u160Atlas, u160Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u127
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u125
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u121
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u137
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u124
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u132
    · exact slice_correct (ms := fixRows 64 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u88
    · exact slice_correct (ms := fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u151
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u101
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u82
    · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u77
    · exact slice_correct (ms := fixRows 0 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u143
    · exact slice_correct (ms := fixRows 128 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u114
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u100
    · exact slice_correct (ms := fixRows 8 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u90
    · exact slice_correct (ms := fixRows 4 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u87
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u75
    · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
    · exact slice_correct (ms := fixRows 84 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u94
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u111
    · exact slice_correct (ms := fixRows 196 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u115
    · exact slice_correct (ms := fixRows 69 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u85
  exact frozen ready cert_u160 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u161 : Lower true (vars 251) u161T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 251) (T := u161T) (xs := [(inputs.getD 6 zero,0,64)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u145
  have hc : (([(inputs.getD 6 zero,0,64)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u162K11 : Nat → Nat
  | 0 => 0x227f
  | _ => 0
def u162N : Nat → Nat
  | 11 => 1
  | _ => 0
def u162R : Nat → Nat → Nat
  | 11, i => packedAt u162K11 (i * 7) 7
  | _, _ => 0
def u162I : Nat → Nat → Nat
  | 11, h => packedAt u162K11 (8 + ((h / 1 + packedAt u162K11 (7 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u162Pos : Nat → Bits
  | 0 => 0x3e006c018e00180000f0ff900130634c03333f
  | 1 => 0xc001810e7000601f0f0f000009c0848f0dcdcc
  | 3 => 0x6020288420387e000000f824e0318f0ce0e0f
  | 4 => 0xf81c14f07c0c0000f00ff020700c1f00f00ff0
  | 5 => 0xe018ff80300000fff00043800fe000fff000
  | 6 => 0x1001f0001c007ff0000007c000fffff000000
  | 7 => 0x1ffe00001fff8000000007ffff00000000000
  | _ => 0
def u162Neg : Nat → Bits
  | 0 => 0x8026101000403905015158900110214c011115
  | 1 => 0x94800a00000e823031311800940008505454c
  | 3 => 0x580000884017c0e2362627024a010890ce0e0a
  | 4 => 0x280a80a808d0248500ca22050041e00500aa0
  | 5 => 0x7411440055320490aca00442800bc000aaa000
  | 6 => 0xa6001c0001e8171cc8c8c874000ef76a000000
  | 7 => 0x3452a0000000000000924a00000000000
  | _ => 0
def u162Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,10),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,10),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,10),(0x5555555555555555555555555555555555555555555555555555555555555555,10),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,10),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,10)]
def u162Atlas : Atlas := ⟨11, rawDecor 251 u162Pos u162Neg, u162T, u162Slices, [swapRows 84], u162N, u162R, u162I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u162_11_0 : Interval u162Atlas 11 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u162_11 : Interval u162Atlas 11 0 1 := blk_u162_11_0
theorem cert_u162 : Complete u162Atlas := by
  intro k hk i hi
  change k ≤ 11 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u162_11 i (by omega) hi
theorem b_u162 : Lower true (vars 251) u162T 12 := by
  have ready : Ready u162Atlas (asRow u162Pos) (asRow u162Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u162Atlas, u162Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u153
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u146
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u139
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u123
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u134
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u130
  exact frozen ready cert_u162 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u163K5 : Nat → Nat
  | 0 => 0x19cb170c723270292e140a46d01691521298618e94762680b52a4c34880c74a3b1a405a45261a14063a51f0d130d2250250a031d28e86d25691498681018e947c344c340a4290c84a7483
  | _ => 0
def u163K6 : Nat → Nat
  | 0 => 0xa54a9529f32920a5269522809ed2094a952a54a952a54a852a494ad2a54a952a54a94d864e952a4e1d52800294aa54a9471b06952a4c950e2e90611614a952454a952206a908914a92ca54a152967a952a4a14d2a548b464d4833ca54a72ea4da93e8b48c52474a8d2a54a952a549a527f4a952a548ed2a548cd2894851c254908218201042140044ca74c48694a88874c3937d0a0e94c44c34a3b3680a4894c30c74a3a3790a4894c30c74a3a3748a9094c30c74a3e2752a4c34880c74a3e3548a4c34280c74a3e354c34894280c74a3e344c34094280c74a3c7c4894094280c74a3e3648a4c34080c74a3c674894698e84c5483b270ea4c54c44c3483d274c48e94a84c3483ce68898698084c7483a7c82a4a88084c7483e668888688084c7483d668898698084c7483a7c82a4a98084c7483c784494094280c7483e274c49094c38a748387e80a4e9cc84a7483ca74c48698c84a7483ca74c44690c84a7483cb54c34290c84a7483c3d4c74290c84a7483cb64c34090c84a7483c3e4c74090c84a74838e792a4c48684a7483e274c41094c34a7483c3792a4c30c84a7483c274c44690c84a7483c354c34290c84a7483c7c40a4290c84a7483c364c34090c84a74838fa80a4c98c8483ca2ce38898694c8483ca2cf840a4290c8483ca2c794ea4290c8483ca2f234c44c34834c7ca297a80a4c94834c7ca2
  | _ => 0
def u163K7 : Nat → Nat
  | 0 => 0x18f8e783419acc055000b4e68341a0c10800a080623000a0c432000a408c040880028c40480e15016a0800360402dcc000848101c212310020015fa02522119f3163fc64a44433a62cf78694888a74c3d5e98911094e9872fe32622129d30f5ba62434253a61cf74898684a74c3f4f0d298910e9871fe42529e21d30f57a62254443a61cbf8c94a88874c39ef0d295110e9871fe42531621d30e3fe84c53a43a61cbf8c94a84874c39ef0d295090e9873f60a52a121d30e7f404a54243a61c7f8e94a84874c39ee9530d090e987bda1a202121d30f3f453c04243a61e7e4a78084874c3ded0d301090e9874fd3273a131128f9b874a62261a51d370e94c44c34a3f4e9891109869477da02522130d28f9ba44a61863a51e379094c30c74a3c6e98691018e94789d30d22031d28f1aa61a14063a51e7d4894280c74a3cf881285018e9478d930d02031d28f3bc84a61c43a51cfe8094e8cc5483cfd0129d198a9071fa0253a331520e7ba34c74262a41e774698e84c5483aee1d298a986907e9d31531130d20fd3a62454261a41fa74c44a84c3483b6f19295098690779e2252a130d20ebbc74a54261a41e7e8094c88c74838fd01299118e907b9e2221a131d20f7b434404263a41ef68698084c7483aef0d295098e9075f60a52a131d20ebf404a54263a41f678888684c7483ccf1110d098e9079fa2a202131d20f3f254404263a41f768688084c7483eed0d301098e9079f931602131d20f3f454c04263a41e7e4a98084c7483cb709295018e9079e51250a031d20f3e204a14063a41f274c44c38a7483cef21298714e907e9d31130d29d20ebf404a63a53a41cf7469cc84a74838fe9d399094e907add30e32129d20f1fa63c64253a41cf78698c84a74839ef0d299094e9073f60a532129d20e7f404a64253a41c7f8e94c84a7483d6e98619094e9078fd31c32129d20e7ba34864253a41cfd4290c84a74839fc81219094e907b9e2221a129d20f6ba62c34253a41ee74c48684a74839ee9930d094e907c9d31130d29d20f3b884a61a53a41c7d8294c84a74838fd01299094e9078dd30c32129d20e2fa54864253a41c774690c84a74838fa85219094e9071f902432129d20f33c44434253a41dfa8094884c34c2f469889869069857ea02532120d30b7d404a64241a614fa8094c84834c2f569891109879457ce1a522130f28afd404a44261e517e34c44c3483ca2f46988986907945f8e22530d20f28af9a34e64241e5157b4e9cc8483ca28f69d39909079453ed32632120f28af9c34a64241e515fa8094c8483ca2de70d2990907945bea02532120f28a7d404a64241e514db4a90c8483ca29f28521909079453e902432120f28a3da74864241e5173b4c44c34c7ca2af711298698f945dcd30d20d31f28abdc64a41a63e5157b4c94834c7ca2
  | 1 => 0x831e98f061e32591046dc1a0c6d833e9e02057a508a3a15a61ba723316da2eb8106e0cff6a40d60ea172f20ce1834194a6c830c976f522419c7064f0496d065729d9f068341a02ba1b3920d068341a0cc159b3849066b940e2056a918107e460e1d2d97ca21945c421615106473820106141920d068341a0d05831492f068341971063bc189706200b556f2669e20c048341984347eafd1482834183d06831d028b244b720c06831060ca08341a0d06830304d06833c60d068308a0d068326a0cbe4941a0c6883419a7066d0082c568341a0ca64841a0c547c17dca107d8a90e2333b15530663179fd0635108a6df61ab01d06831c20c51830f872484d8299860713b0304f03ad10ccb83418589631131e81783419bca30e291a506273b860fc8341a0cb134c1a0cc4743cc350683129b1064e0bd7af6511d9a080373b532ef12c
  | _ => 0
def u163K8 : Nat → Nat
  | 0 => 0xf34a0b0e7c8d1a6e56230a1cc108369f61a053cdb6bf87439ea887a4041d0e0010498c30b27828f7212c56a3b8707e0f0377be094763721a1cfa1f3191b0e10315c10e84139170e8743a1c5817071287e4b3c21c21012c8e88268abcaa0c18a3848295839e1d0e67c3a1c5201b01d09a194261cbc2d0548d0e872cde4df8124194d8420f148660bc3a1d0e660e96ca087428f0bb28099c4f68732dacea2043952aa112fa1d0e1543890ab87335dc988742c56b72e2e06c2872399d2e32a200d90e871dd104034224218200000008000018f1400090004810c10830810e120120a24c28524a0d10800c30420270c50450430000c10810080a7f888467cc5dfd22119f316ff4888674c5dfd22219d3167f4888674c59fe22129f30eff8884c54c3efd31531130fbf4c48a74c3bfd22229d30e7f4888a74c3efd31129d30ebf8c84a74c3bfe22129d30ef78684a74c3ebd31221d30f7f4a78874c3bfd2a221d30f7f4c58874c39fe2a221d30f7f4a88874c39fd2a221d30f7f8a74874c3dfd29d21d30eff8a84874c3bfd2a121d30ff78684874c3bde1a121d30ffe8084874c3bfa02121d30edf8884c54a3dff3a131128f7f0e84c44a39fc3a131128fb74c44c34a3fde22130d28ff74884c34a39fd22331d28e7f8884c74a3cdd30c31d28e6fc880c74a39fd22031d28e6f4880c74a39f50a031d28e7e4080c74a3d7d31621d28f774c38874a39fe32221d28f7f4c88874a39fd32221d28ef7468cc54839ff3a331520eff4e8cc54839fd3a331520e7fce84c5483bfe3a131520f7f8e84c54839fe3a131520f7f0e84c54839fc3a131520ff74c54c3483f9d31130d20fa74c44c3483fde2a130d20ff74a84c3483f9e22130d20eff4a8cc7483bdd1a331d20efb448cc74839fd2a331d20e7b448cc7483dfd31631d20e7f4c88c74839fd2a231d20eff8a84c7483fde1a131d20ef78684c7483ffa02131d20efe8084c7483dfd31531d20f7f8a84c74839fe2a131d20f7f4a84c7483dde1a131d20f7e8084c74839fa02131d20e5fca80c74839fd2a031d20e5f4a80c74839ed12031d20e7d4280c74839f902031d20f774c38a74839ff32229d20e7f4c88a7483f7d31529d20ff74c34a7483dfd31d29d20effcc84a7483bfe32129d20eff4c84a7483bfc32129d20ff78684a7483bde1a129d20f5f4c54a7483ddd30d29d20e7fcc84a74839fe32129d20e7f4c84a74839fc32129d20f778684a7483eed31130d30afb8884c34c2fed22130d30bf34c34834c2bee32120d30bfb4c84834c2bed32120d30afb488cc3ca29ed3a330f28bbbcc44c3ca2fed31130f28bbb4c44c3ca2fee22130f28afb8884c3ca2fed22130f28bf34c3483ca2fef32120f28afbcc8483ca2bee32120f28bfb4c8483ca2bed32120f28afb0c8483ca2ded30d31f28b7b4834c7ca2
  | 1 => 0x172a2638617a757e8b11eeb4e0c0d4a687370e4a85d04558ae87438bc088737590701fc3a1c87874399d0d1c43a1c4487439bd0e874395a673e43a18ed82249a0602b0121d0e7f32518e145364f42d09400c8d75a3540cd483135e2950e988d0fc09bb21d0e0
  | _ => 0
def u163K9 : Nat → Nat
  | 0 => 0x3a087dfd66e416d37a96c55b15d658921ec58b0ece125615f589962c58b16132e4562358b112458b1612344162158b128c364ea8400354978a1d5274bb161e40a27ac312d62c58b161c0b86a6c580d6278c9aca8357305828b16011426319203020517352102a29bfa33e62ffe19d316ff0ce98b7f4a7cc3bfa43e61ded11f30ffe98a987bfcc44c3ffa62261efd31130fff14e9877f8a74c3ffa53a61ffe21d30eff10e987ff4874c3efa62a51ffd31128fbe948947f74c34a3bfe63a51dfe31d28efe98e9477f0c74a3ffc43a51dfe21d28fff98a907ff4c5483fba61a41fff31d20eff98e9077f8c7483ffa63a41dfd31d20efe18e9077f8a7483ffa53a41dfd29d20ff6986985fb4834c2fde61e517ed30f28bf69079457b4c7ca2
  | _ => 0
def u163K10 : Nat → Nat
  | 0 => 0x420882d2e81e10508043420c008ffcc5ff4c5ffcc3ff4c3ff4a3ff483fb4c2fbca2
  | _ => 0
def u163K11 : Nat → Nat
  | 0 => 0x287f
  | _ => 0
def u163N : Nat → Nat
  | 5 => 6
  | 6 => 41
  | 7 => 131
  | 8 => 135
  | 9 => 44
  | 10 => 8
  | 11 => 1
  | _ => 0
def u163R : Nat → Nat → Nat
  | 5, i => packedAt u163K5 (i * 85) 85
  | 6, i => packedAt u163K6 (i * 72) 72
  | 7, i => packedAt u163K7 (i * 59) 59
  | 8, i => packedAt u163K8 (i * 46) 46
  | 9, i => packedAt u163K9 (i * 33) 33
  | 10, i => packedAt u163K10 (i * 20) 20
  | 11, i => packedAt u163K11 (i * 7) 7
  | _, _ => 0
def u163I : Nat → Nat → Nat
  | 5, h => packedAt u163K5 (526 + ((h / 4 + packedAt u163K5 (510 + (h % 4) * 4) 4) % 17) * 4) 4
  | 6, h => packedAt u163K6 (3015 + ((h / 21 + packedAt u163K6 (2952 + (h % 21) * 3) 3) % 147) * 7) 7
  | 7, h => packedAt u163K7 (8069 + ((h / 68 + packedAt u163K7 (7729 + (h % 68) * 5) 5) % 299) * 9) 9
  | 8, h => packedAt u163K8 (6630 + ((h / 70 + packedAt u163K8 (6210 + (h % 70) * 6) 6) % 264) * 9) 9
  | 9, h => packedAt u163K9 (1544 + ((h / 23 + packedAt u163K9 (1452 + (h % 23) * 4) 4) % 105) * 7) 7
  | 10, h => packedAt u163K10 (172 + ((h / 3 + packedAt u163K10 (160 + (h % 3) * 4) 4) % 19) * 5) 5
  | 11, h => packedAt u163K11 (8 + ((h / 1 + packedAt u163K11 (7 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u163Pos : Nat → Bits
  | 0 => 0xc731c0063d0080187d87c4009cc18ecc09ce73
  | 1 => 0x38ce000bc200fc2f82f80000e702130f0e739c
  | 2 => 0xc0f0000c03ff0030030008ccf80c63f0cf83e0
  | 4 => 0xffc070000003c003ffd00f00307c00f003ff
  | 5 => 0xff000380000003fffc0020f0003f8000fffc00
  | 6 => 0x3c0003fffc0000003f00003fffff000000
  | 7 => 0x3ffffc00000000003fffffc00000000000
  | _ => 0
def u163Neg : Nat → Bits
  | 0 => 0x902440e5f119438af8ac4008c4086cc08c631
  | 1 => 0x902400ec7028c3987984000a50003050a5294
  | 2 => 0xc9f262dfab8f88fb1bb188ccf8042350cf83e0
  | 4 => 0x5200083000242140006510050010780050014a
  | 5 => 0x5491800048428650002050002f0000a52800
  | 6 => 0x1d201070730460463500003bdcaa000000
  | 7 => 0xa4a922412080000000000aaa52800000000000
  | _ => 0
def u163Slices : List (Sig × Nat) := [(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10),(0x3333333333333333333333333333333333333333333333333333333333333333,10),(0x5555555555555555555555555555555555555555555555555555555555555555,10),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,9),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,9),(0x0303030303030303030303030303030303030303030303030303030303030303,8),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,8),(0x0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,8),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,8),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x0000000000000000555555555555555500000000000000005555555555555555,7),(0x0000000000000000000000000000000055555555555555555555555555555555,7),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,7),(0x0000000000000000000000000000000033333333333333333333333333333333,6),(0x0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,6),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x00000000000000000000000000000000ffffffffffffffff0000000000000000,6),(0x3333333333333333000000000000000033333333333333330000000000000000,6),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,6),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,5),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,5),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,5),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,5),(0x000000000000000000000000000000000000000000000000ffffffffffffffff,5)]
def u163Atlas : Atlas := ⟨11, rawDecor 247 u163Pos u163Neg, u163T, u163Slices, [swapRows 84], u163N, u163R, u163I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_5_0 : Interval u163Atlas 5 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u163_5 : Interval u163Atlas 5 0 6 := blk_u163_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_6_0 : Interval u163Atlas 6 0 41 := block_range (n := 41) (by decide +kernel)
theorem all_u163_6 : Interval u163Atlas 6 0 41 := blk_u163_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_7_0 : Interval u163Atlas 7 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_7_64 : Interval u163Atlas 7 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_7_128 : Interval u163Atlas 7 128 3 := block_range (n := 3) (by decide +kernel)
theorem all_u163_7 : Interval u163Atlas 7 0 131 := (concat blk_u163_7_0 (concat blk_u163_7_64 blk_u163_7_128))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_8_0 : Interval u163Atlas 8 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_8_64 : Interval u163Atlas 8 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_8_128 : Interval u163Atlas 8 128 7 := block_range (n := 7) (by decide +kernel)
theorem all_u163_8 : Interval u163Atlas 8 0 135 := (concat blk_u163_8_0 (concat blk_u163_8_64 blk_u163_8_128))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_9_0 : Interval u163Atlas 9 0 44 := block_range (n := 44) (by decide +kernel)
theorem all_u163_9 : Interval u163Atlas 9 0 44 := blk_u163_9_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_10_0 : Interval u163Atlas 10 0 8 := block_range (n := 8) (by decide +kernel)
theorem all_u163_10 : Interval u163Atlas 10 0 8 := blk_u163_10_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u163_11_0 : Interval u163Atlas 11 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u163_11 : Interval u163Atlas 11 0 1 := blk_u163_11_0
theorem cert_u163 : Complete u163Atlas := by
  intro k hk i hi
  change k ≤ 11 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u163_5 i (by omega) hi
  · exact all_u163_6 i (by omega) hi
  · exact all_u163_7 i (by omega) hi
  · exact all_u163_8 i (by omega) hi
  · exact all_u163_9 i (by omega) hi
  · exact all_u163_10 i (by omega) hi
  · exact all_u163_11 i (by omega) hi
theorem b_u163 : Lower true (vars 247) u163T 12 := by
  have ready : Ready u163Atlas (asRow u163Pos) (asRow u163Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u163Atlas, u163Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u130
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u127
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u126
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u140
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u135
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u129
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u93
    · exact slice_correct (ms := fixRows 64 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u92
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u154
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u106
    · exact slice_correct (ms := fixRows 69 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u89
    · exact slice_correct (ms := fixRows 129 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u102
    · exact slice_correct (ms := fixRows 0 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u147
    · exact slice_correct (ms := fixRows 130 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
    · exact slice_correct (ms := fixRows 4 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u91
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u105
    · exact slice_correct (ms := fixRows 128 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u119
    · exact slice_correct (ms := fixRows 2 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u90
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u84
    · exact slice_correct (ms := fixRows 84 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u97
    · exact slice_correct (ms := fixRows 100 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u98
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u110
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u113
    · exact slice_correct (ms := fixRows 196 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u120
  exact frozen ready cert_u163 (by decide +kernel) (by decide) [(inputs.getD 0 zero,16,17),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,64,68),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u164 : Lower true (vars 239) u164T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 239) (T := u164T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u134
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u165 : Lower true (vars 223) u165T 11 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u164
theorem b_u166 : Lower true (vars 191) u166T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 142 0) (raw := vars 191) (T := u166T) (xs := [(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,0,8),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u10
  have hc : (([(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,0,8),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 4 := by decide +kernel
  rwa [hc] at h
theorem b_u167 : Lower true (vars 127) u167T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 127) (T := u167T) (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u153
  have hc : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u168K6 : Nat → Nat
  | 0 => 0x35ef7bc2f733eb1498f7bc0ec7dea7bdeacbdef6d237cfde818fe7799e52d0d1900081193a2350322ad329396021392236a16e86495a65272252270516696d4e488a80a8694c84e082ec8db2989d69490129909c1453a2353962ad22a025321382327406a46455a65272c44270492ed2d94c4cb4e44a44e04c084dc91ba191d69549129c0981113d2374b23ad42939531520222f206e96475a85272a62a40520f96d4e54c590a4c94e448084ec8db2d89cb2149929c0901487a5b5395316429325381203c07272a70465445264a54240780e4e54e48ca80a4c94a8480
  | _ => 0
def u168K7 : Nat → Nat
  | 0 => 0x3a12030ee48b40b92a4c54e8480b13e4b132d3952913a1202c5e92c4cb4e54a04e8480d07d3944ad3153253a12020bfd4c12b4c54c94e8480e9392912823a93253a120324f4a48eb8aa4c94e8480c9792823ae2a93253a1203a0f4e54c588a4c94e8480e9393952822293253a120324f4e58ab88a4c94e8480cb392822ae2293253a1203a474e54a486a4c94e8480e9593952821a93253a1203ac64a44a086a4c94e8480e8793953160293253a1203a4e4e54a480a4c94e8480c9793962ae0293253a12032ce4a48ab80a4c94e8480837d5324ad3162a53a120309f4c594b4c98a94e8480c17d3974ae32a2a53a120303f8c98eb4ca8a94e8480c93d39622d32a2a53a12030af8c988b4ca8a94e8480c95d3961ad32a2a53a120325e4e580b4ca8a94e8480c2fa32602d32a2a53a120289f4ac8cb4ca8a94e8480b83e2b132d395391321202c0f12c4e54c54e44c8480b87a2b132d395381321202c1e12c4e54c54e04c8480b1b84b12ad39138132120346e4e412b4aa4e04c848083de1b14ae4a93992a12020fd82c52b92a4e64a8480c33d2ad22e4a93992a12030ee48b40b92a4e64a848091bf4b23ad3293912a120344f4e592b4ca4e44a8480a1ed3b34ad3ab3092a120287b8ec52b4eacc24a8480a3ce1b14ad3ab3092a12028f982c52b4eacc24a8480d9993921ad3293812a120346e4e492b4ca4e04a8480e1af30a3aa2293a52a12028cf8ac4ca88a4e94a8480a3ba03132a2293a52a120384f8ea8aa88a4e94a8480e32f30a2aa2293a52a120387acc28ea80a4e94a8480a3ba23132a0293a52a120386e8ea88a80a4e94a8480e33a2aa22a0293a52a12038eacc288a80a4e94a848092be23132e3aa3252a12024be80c4cb8ea8c94a8480a0fd3323ad3aa3252a12020bfd4c12b4e64c94a8480c1bd39352e3a53252a120307e4e0d4b8e94c94a8480a1be2313a63a93252a120287e80c4e98ea4c94a8480e9393953822293252a120324f4e58eb88a4c94a8480c9b93823ae2293252a1203a4e4e54e480a4c94a8480c9b93923ae0293252a120303f8eb8cb4ea4c94a8480c1be3ae22d3a93252a12030af8cb88b4ea4c94a8480c33e2ae22d3a93252a12030f586b82b4ea4c94a8480c1fa3ae02d3a93252a12030be8cb80b4ea4c94a8480c3ba22e02d3a93252a1203c0f4e54e48ca4c94a8480f0b93913823293252a1203c4e4e54e088a4c94a8480e23d39632a2293252a12038ae4e08ca88a4c94a8480e23e32a2aa2293252a120388f4e68aa88a4c94a8480e3393822aa2293252a120344f4e58eb88a4c94a8480d1b93823ae2293252a1203c4e4e54e480a4c94a8480e2b939232a0293252a12038ae8ca88a80a4c94a8480e33a2aa22a0293252a12038ae4e688a80a4c94a8480e33939622a0293252a120346e4e48eb80a4c94a8480
  | 1 => 0x8a8094c84e0e47939531522a02532138315e4e58ab48a8094c84e0993d2322ad3293962213824cf48c8ab4ca4a98884e0c27e32e2ad3292a622138341f4e512b4c54c84884e0e91d3952921a93212213831768eb80b86a4c94884e0e47939531602932522138309f4c594b4c88a94884e0c55d3961ad32a2a522138315e4e580b4ca8a94884e087f20b132e0292a522138318f4ab48b92a4e64a44c09c3e3b22ad32939129130350f4e592b4ca4e44a44c0993d3b12af42939129130264f8ec8ab50a4e44a44c0d91d3961ad42939129130344f4e592b50a4e44a44c083f95b202b4293a52913020bf96c4ca10a4e94a44c09cb92b222d32939138130272e88c4cb4aa4e44e04c0c8f932842d2a9391381302e2e10c4ab4e44c44e04c0e4b92b13904a9311381302f0e8ac4cb4e44a44e04c0acba53132d391291381302b2e88c4cb4ea4a44e04c0c8f932c42d3a929138130312e4e412b4ca4a44e04c099b923042d39522538130227ed4c10b4e54894e04c0b87843139531522538130331e4e514b4c54894e04c0cc7939632e2a922538130227ed0c8eb4aa4894e04c092be33122e2aa2253a13028cf48c8ab4aa8894e84c0b87a2b132d39538222130305f8eb8ab4ea4a98884c0c3ba22e02d42a2a53992030ee88b80b50a8c94e54808b5e1b132e2a94253952032ae48b40b90a4e64c5480917f4b23ad4293953152030ee48b40b90a4e94c5480a33e53139522a4253152038ae4e648a40a9094c5480e33939522902a42531520236e80c4ab8ea4c94e4480ec3939531602932539120236e8ec4ab80a4c94e448089be5b1396429325391203a0f4e54c590a4c94e4480d1ce3b21ad4293a730920236e54c92b4c54e44e048095b94b252d31539138120352e4c592b4ca4e44e048095b92b24ad32939138120276c82c4cb4aa4e44e048095ba4b132d2a9391381202e4e90c4cb4e54a44e0480ad3a2b132d3a9291381202b6c82c4cb4ea4a44e0480a9ba43132d3a929138120296e92c4cb4ea4a44e04808dbb5322ad391325381203b0e4e54c588a4c94e0480cd393962ae22932538120236e8ec4ab88a4c94e0480ad9a2b13921a9325381202b6616c4e486a4c94e0480ed193952921a9325381202b664ec4a486a4c94e0480e99939242e1a9325381203a664e486a90a4c94e048089fa5b1396429325381203a1e4e54c590a4c94e0480e8b931539242932538120326e4e44ab90a4c94e0480a5ba53132d3922a53812035664e486b4c94a94e0480d7192921ad3252a538120236e8ec88b4ca4a94e0480cd993921ad3292a538120326e4e490b4ca4a94e0480d5393964ad329391281202b4e8ec4cb4ea4a44a0480af320b132d3a92912812029ce92c4cb4ea4a44a0480917f4b22ad3293953a120306f4eb48b92a4c54e8480c1f93ad02e4a9315
  | 2 => 0x82544f37b359426335ebe8791885ea319dbbb04a9ddef7ea7d3cf8850fe647d06c04b66fd1e84fd5bd1e8cf7a223e8b0395429175ec3a653a977576719ee3ba5e8acc31f5e831fa3d07ecefa3d0d6ee03b58ba6776d9411f461fd04358e47d0a6d5a5fd144485ad6ebebb0624246cff9c0c8e93b2372a4bb9bd7bc1a37a2a0f1d97a2f436f47a3d039111922a3fc49c1031c8007489e8977a09c19f477f712cf433f781c167a185e8f41455d5c7e969267cf26bb6f40f472342e3013a2cde51248b0403db15bd0e6f4353d086d17a13b62f40ecc1e8f4590bfe8b8fa21c3a6ce5bd1e8f42538514739d98be8d31e9fde8f475f7d97f46a3d066693dbd1e8e07a349e83938411e244a6a8e986e985c492f47a20c8b022e57902c536e9f2af42fd568595d97686e8561701e802f87d1dabe0785cea04c0efd706c766355b9d05acf986bb4f2014aa6492be625da908af79f4755cd14424068004868844a2400031c25810031440003002840820c41020c21010420c21830011c2a9003720108d0d90000010050800411152c40b32038010c70011800830001830012403490401c40852c050d1110810006803800c0d2800104400001f09c1d00950c81c23c1048501c53d3962ad02a2253213930be8ca80b4ca4098a84e493792b202d3290262a139265e40c8ab4ca4e58084e4c27e32a2ad3292a60213924de40c8ab4ca4a98084e4c27d31652d3222a502139314f4e588b4ca8a94084e4c55d3961ad32a2a502139325d8eb8ab82a5094e54c49c3d0322ad32939539131270f8ac4cb40a4e54e44c4c8bd32842d02939539131266e40c10b4e54094e44c489bf53042d395025391312e0f10c4e54c54094e44c4cc3d39452d31502539131330f4e58cb8aa4094e44c492fa33102e2aa0253a1312e0f8ac4cb4e54e48084c4c17e3ae2ad3a92a60213130cf8ab88b50a8094e64a48d3e2b102e3a932539129234f40c8eb8aa4c94e44a48d3e3b102e2a932539129324f4e540b90a4c94e44a4a53e53132d39602539129326d8eb88b82a4c94e84a4cb362ae22e0a93253a129303f8c98eb4ca8094e84a4c2be32622d32a0253a12928be40c8cb4ca8094e84a4d13d3944ad029391321292c8f80c4e68a98894c84a4c9e63b20ad4a92913a330aa738ec48b86a4094e8cc28dba23132e0292a539138237c82c4cb80a4a94e44e09cba33202d2a939131138307e8eb80b50a8a94c44e0a1be5312ad39042531138384f4ac4e44aa1094c44e091bf4324ad32939129138256e88c4cb80a4e94a44e095f20b132e0293a52913830cf8ab88b4aa4898c84e0c5b939202d2aa22532138257696c4e480a8694c84e0e59939222a02a1a53213829768ec48a80a8694c84e0d4b93922ad31202532138217e94c4eb4a48094c84e0d4b939132d29202532138296e88c4e54
  | 3 => 0xd583ee9dadf0514237e8918987cb284ce0a51d0fc9aaeb3f41e104a9f41fc608c74b811f68ea842416c8236aff17e5e72b14eb6dd3d0cb5c6ef26d005a94360c565288108eb068f3374044950c6507128be826bed15e8f41785474d8b73d038f478fd0f843df7d028ea272d2a29ce239e342e7a0fa235acdae5d0f403fd1e85845b8ba0f47a3d06816fa3d142f412265e892fa2ea37f44cfd0fc887a395e8e72b707e8e3b12f2d1a67a3d06c4ddcfd1e8a47a3d11980cd7d1e87ce57872f003d2530be4e1af0888c41683def4237d0992ecc38de8f46ce9b43af7a3d1e8f452cb06a552d29328f47a249e81e39308122db321b1319633c15f783bbd001f47a2dfe8f430fd15a9a62c41e8763fcf73cccfa23cf777ad9
  | _ => 0
def u168K8 : Nat → Nat
  | 0 => 0x8480a7f495a6527025424079ad39330a3a52a1203cf59849c11d29509012ef88b4ca8e94a848097f405a65474a542406b3e2aa2293a52a12035d79851149d2950901a6f8e988a4e94a8480d77445405274a542406beb30a0293a52a12034fd1d30149d2950901c7bcc28ea4e94a8480a77c45a65274a5424053de1ad3293a52a12029fb0569949d29509014fe80b4ca4e94a8480e75e61445274a5424071be3aa2293a52a12030df1d51149d29509018ef8ca88a4e94a8480c77a65445274a54240733e2aa2293a52a120319f1551149d2950901cfacc280a4e94a8480e3f475405274a5424061fa3aa0293a52a12031fd1950149d29509018fe4ca80a4e94a8480e77445405274a5424063ba22a0293a52a1203c9e9ca9c9192950901e6e4e44e08c94a8480e37a72474c64a5424071f93823a63252a12029df1169d31929509014fe80b4e98c94a848087fca5a74c64a5424043ff4ae3aa3252a12030ff1d29d5192950901c4f4e54e48c94a8480e37272270464a5424052fd32e3aa3252a120317e9971d519295090187f8eb4ea8c94a8480a5f895a73264a54240793d3953913252a1203cdc9c89c0992950901c6f4e48e94c94a8480e3f270474a64a5424043ff52e3a53252a12029df1169d29929509014fe80b4e94c94a8480d37a72475264a5424069f93823a93252a12030fe9d31d49929509012ef88b4ea4c94a848097bc35a75264a542404bf60ad3a93252a12025fd0169d49929509010ff92b4ea4c94a8480d67c55445264a542406abd39a2293252a120359e9cb114992950901aee4e088a4c94a8480d57c64c45264a542404bbe3ae2293252a12025de9d7114992950901aee88a80a4c94a8480d5f273405264a542406bb93920293252a120357d1930149929509012fe8eb80a4c94a848097f275c05264a54240713d3953913252a12038dc9c89c0992950901c3f4e68ea4c94a8480e37a72475264a5424071f93823a93252a120297f1969d49929509014ef88b4ea4c94a8480a7bc35a75264a5424053f60ad3a93252a12029fd0169d499295090187f8eb4ea4c94a8480c5fc65a75264a5424063be22d3a93252a12031ef0d69d49929509010f786b4ea4c94a8480c7ec15a75264a5424043f60ad3a93252a12031fd0169d4992950901caf4e48ca4c94a8480e5f270465264a5424052fe3ae3293252a120297e9d7194992950901caf4e688a4c94a8480e67a72c45264a5424073b93822293252a120395f1951149929509018af8ca88a4c94a8480e67c55445264a54240633e2aa2293252a12029df1d71149929509014ef4eb88a4c94a8480e5f273405264a5424073b93920293252a120397d1950149929509018be8ca80a4c94a8480e77445405264a5424063ba22a0293252a12029fd1d70149929509014fe4eb80a4c94a8480
  | 1 => 0xa94e8480d2fa72c65454a7424062fd32632a2a53a12021ffa571951529d0901a5f4e54ca8a94e8480c5fc64a65454a7424049fe3ad32a2a53a12025df1169951529d09012f786b4ca8a94e848097f405a65454a74240537d2ae32a2a53a12031be9571951529d0901c9f4c54ca8a94e8480a7bc35a65454a7424062fe32d32a2a53a12031ef0d69951529d09010f786b4ca8a94e848087fea5c64a54a7424053de1ad3252a53a12034f79851d49529d09018bf4c98ca4a94e848093fc75a65254a742404bbe22d3292a53a12025ef0d69949529d09012fd82b4ca4a94e848097f405a65254a7424043fe4ad3292a53a12034bf1d51549529d0901a6f8ea88a4a94e8480d75e61445254a7424063be3262292a53a12031de9931149529d0901acf8a988a4a94e8480d3f475405254a742406bba22a0292a53a12035f59850149529d09018fe8c980a4a94e8480c7f264c05254a742406b7a2a60292a53a120257fa571549cc99090163f8eb4ca4e54c8480b4fc55a65272a6424051fd3af4a93953212028ff1d6a549ca9909014df8ab52a4e54c8480a7bc35a95272a6424053f60ad4a93953212021ffa562549ca99090149f12b4e54c54c8480f17a65a72a7226424059bc4ad3953913212028de2569ca9c8990901e0f4e54c54e44c8480b77405a5527226424053bc4ad2a9391321203c7c9969ca9c099090167e12b4e54e04c8480a3f095a72a702642407879395315381321203c5c98a9c89c0990901e6e4ab4e44e04c8480f372722552702642405bba22d2a93813212029fc2569549c0990901e6e4e4d2a4e04c8480b3f275e9527026424069b939202a3a532120257e9571949d299090183f8ea8ca4e94c8480a5fa55c65274a6424061be3aa2293a532120315f1951149d29909018f78aa86a4e94c8480c7bc55c35274a6424061fa3aa0293a532120317d1950149d29909018ee88a80a4e94c8480f37272270454a6424070fd39a3a62a53212038de9c91d3152990901c7e4e08e98a94c8480a7bc35a74c54a6424069bd3923aa2a53212034fc9c11d515299090187f8e94ea8a94c8480e37272270454a6424071bd3923aa2a53212038fc9c11d515299090187f8eb4ea8a94c8480b5f455a73404a6424079b93953920253212028fe9d7a549cc9509014bf4cbd2a4e64a8480977a45c952732542404bf902e4a93992a12021fea572549cc9509018ef48b92a4e64a8480c7f205c9527325424051fe3ad4a93992a120297f196a549cc9509014f786b52a4e64a8480a7ec15a9527325424043ff4ac4a93992a1203c9e9ca9949c895090166f8eb4ca4e44a8480a77c95a65272254240792d3953933092a12031f7a569d59849509018fb52b4eacc24a8480f37265a7227025424079a93933093812a1203cdc9c89949c09509016f686b4ca4e04a
  | 2 => 0x4a4cc24e0480f8f272a62a64a702407cb9315391325381202edd1569c89929c0901f4e4e54a44c94e0480bb7275a52264a702406d793962a93253812036dc9c91549929c0901b6e4e588a4c94e0480dd7262c45264a702404fba2ae2293253812027dc9571149929c0901f664e486a4c94e0480df3445435264a702406dd93961a93253812036cc9c90d49929c0901be64a486a4c94e0480df3445c35264a702406bda42e1a9325381203cdc9c92149929c0901af686a90a4c94e0480d3f272c85264a702406af93164293253812034dc9c92149929c09012fe4ab90a4c94e0480eb7265a72454a7024075a939330a2a5381203ed49c99849529c0901fca4a4cc24a94e0480eb7272264a54a7024077392913252a5381202bdd1169929529c09015f686b4c94a94e0480db7272465254a702406db93913292a53812026fd1d69949529c09013ee88b4ca4a94e04809fb435a65254a702404bfa42d3292a53812037d59851149529c0901f4e4e54ca4e44a0480bb7475a6527225024057ba4ad32939128120379c9949549c8940901bce8cb4ea4a44a0480de7265a752522502407d29395393309281203f949569c99849409017ca4eb4a4cc24a0480de5252275661250240597e2ad3293953a12028ff2569949ca9d090127f4eb92a4c54e8480977a45c95262a742404bf902e4a93153a12038be9cb25498a9d090187f4eb92a4c54e8480c77a45c95262a7424063f902e4a93153a12034be9ca25498a9d0901c5f4e512a4c54e8480c2fa72895262a74240793d32d3952913a1203c969ca9499849d0901e5e4cb4e54a04e8480f2d272e612502742407b292933092813a1203c9e9ca9491929d0901e5e4e54a08c94e8480f67252250464a74240787d3953153253a120297e25698a9929d0901e4f4e54a44c94e8480f2f272a50264a742407b392912813253a120347e98b1d49929d0901a6f4a48ea4c94e8480d3f250475264a7424049fd2ae3a93253a120347f1d51949929d0901a5f4e58aa4c94e8480d67a52455264a742406b792822a93253a12024ff1d71549929d0901a6f8ea88a4c94e8480d37a72c45264a742406abd3162293253a12035dc9411149929d0901aaf8c988a4c94e8480977c55c45264a742404bbd2ae2293253a12034ef1d50d49929d0901ae788a86a4c94e8480d3ba72c35264a742406b9d2921a93253a12035ec9410d49929d0901ae788b86a4c94e8480d3f475405264a742406bba22a0293253a12035ed0d50149929d0901a7e4e580a4c94e8480d5f262c05264a742406bb92920293253a120357d1930149929d09012fe8ab80a4c94e848097f255c05264a74240537e4ad3162a53a1203cb69cb9851529d0901ecb4a4cc28a94e8480f6d661250454a74240727d3153262a53a12029ef0d69931529d09010ff94b4c98
  | 3 => 0xf94b4a99094e6480c77245205484a7324043ff52e2a542539920257e957194a129cc9018f78a986a5094e6480cf7405a45464a72a4067ba22d02a3253952031bf156a151929ca9018ef88b50a8c94e5480c7f405a85464a72a4049fd42e3a93253952025bea171549929ca9018bf4c98ca5094e5480d2fc75455284a72a40637d3262a94253952025be997154a129ca901a6f8ea88a5094e5480d67c55445284a72a4069fa3aa0294253952035bd155014a129ca901aee88a80a5094e5480b4fa55c85273262a406a7d2ae42939931520355e9172149cc98a901abe40b90a4e64c548095fe95c85273262a406f39229029395315202cbf1d6a149ca98a90169f8cb50a4e54c5480a6fc95a85272a62a40657e3aa2a93a53152031de9172149d298a9018fe40b90a4e94c548096fca5a72c84a62a4043fe52d3a642531520317f2969cd21298a9014df94b4e59094c5480e57a73245484a62a40733d39522a4253152031de9d491521298a901cbe4e640a9094c5480e6f272a05484a62a4063f93a902a4253152031dc91481521298a90174f8ab4ca4e54e4480b37c85a65272a722406db9329029395391203e9c8169ca98a9c890136f4eb92a4c54e44809f7205c95262a722407c3d39531532539120365e98b1d49929c890136f4ab8ea4c94e4480da7a72c55264a722404dbe3ae2a93253912036dd1d50149929c8901b6e4e580a4c94e4480dd7262c05264a722406dba3ae0293253912027dc9570149929c8901a6f8ea90a4c94e4480d37a72c85264a722406abd3164293253912025de9572149929c89015ee80b4c94a94e44809b7c75a65254a722404fb60ad3292a53912027dd0169949529c89012ef90b4ca4a94e4480ba7c75a65272a522405b3e42d32939529120379c9948149ca94890156f8eb4ca4e94a4480ae7c55a65274a5224057b60ad3293a5291202bdd0169949d29489014ef90b4ca4e94a4480df5245205272e6124059ee3ad429397309202db7156a149cb984901f6a40b4e54e4cc2480bf5405a552726612407f2902d3952933092037d50169d49499849014fb90b4aa4e9cc2480a3dc75a85274e6124053ee2ad4293a73092029e70d6a149d398490175e8ab4ca4e54e0480b3f485a65272a702406db9329229395381203e9c9169ca98a9c090137e4eb92a4c54e04809f7245c95262a702405dba4ad315391381202edd29698a9c89c0901f2e4c54ca4e44e0480bb7455a6527227024079ba42d329391381202edd2569949c89c0901d6e92b4ca4e44e0480ab7495a652722702406db93292a9391381202edd1969549c89c090176e4cb4aa4e44e0480fa7265a72a522702406dba32d3a92913812036dc9969d49489c0901f6a48b4e5cc24e0480bb5455a726612702407da92ad393309381203e949ca9499849c090176a4eb
  | 4 => 0x810f786b50a8a94e44c099fc75a65254a722604ebe22d3292a539130237f2569949529c89819be4c980a4a94e44c093fa75e85254a722604bbd22f4292a53913021fea57a149529c89818bf4c910a4a94e44c0a7f405a54e84a7226049fe2ad3ab4253913034be9ca955a129c898127f4eb4aad094e44c0d2fa72c55284a7226049fe3ae2a94253913034de9cb114a129c89812ef4ab88a5094e44c0d3ba72c35284a7226063dd2a61a94253913035cf1170d4a129c898163f4ebd0a4e54c44c0a9fa75e95272a6226078bf42d395391311302f5d0169549c89889816af10b4aa4e44c44c0adf205c9527325226066bd22e4a939929130337c8172549cc948981f0f4e54ca4e44a44c0b97c75a652722522605e3e2ad329391291302b5f2569949c8948981e4f4e5d0a4e44a44c0b37a75e852722522605b3d2af429391291303c9e9caa149c894898166f8eb50a4e44a44c0b67c55a852722522605b9e1ad4293912913029df256a149c894898153f8eb4ca4e94a44c0ad7c45a65274a5226066f932a0293a529130337c9970149d29489818fe80ad0a4e94a44c0a3fa75e85274a5226053bd22f4293a52913028ff1d6a149d29489814ef88b50a4e94a44c0a7bc35a85274a5226053f60ad4293a529130317e9942149d2948981d0f4e54e44c94a44c0cc7c55445264a5226062fe52d39b425291302e7d1569949c89c098172e88b4ca4e44e04c0d9f2652552722702605cf932d2a9391381302cfd2169549c89c098167e10b4aa4e44e04c093f2558852722702606cfb52d395311381303e5c9569c89889c098162e10b4e44c44e04c0d9727245526227026064b93904a9311381303e5c9969c89489c0981b3e4cb4ea4a44e04c0d3f485a7525227026069f842d3a92913813024fc2169d49489c0981b2e4e44ca4a44e04c08df095a6525227026059f842d395225381303e3c9ca98a9129c09813be14b4c54894e04c0fa7272a52244a7026077392912a522538130367c9cb1949129c09813be4ab8ca4894e04c0daf272c55244a702606e793162a922538130277d1971549129c09812fe10b8aa4894e04c09bf475a55244a702604efa32d2a92253813025fd2169549129c09814ef48b8aa8894e84c0c6fc55a55444a7426053de2ae2261a53a13029ee9571130d29d09818f78aa88a8694e84c0a7bc55c45434a7426053dd2ae22a1a53a1302c7f1d69949cb11098169f8ab4ca4e58884c0a3fc75a95272c44260537e2ad4a9396221303c7c9969ca9c1110981e1e4e54c54e08884c0a7f495a5527044426051fe3ad2a93a62213038bc9ca9c0953110981c5f4e58ea4a98884c0e3f270475254c44260537e2ad3a92a62213030ff1d69d49531109818df8ab4ea4a98884c095fc65a85454a7324063be22d42a2a53992031fd016a151529cc9010f
  | 5 => 0x9909c157714b4e48694c84e0eb3a72252434a6427055dd3ad2921a5321383ace9c91150d29909c15778eb48a8694c84e0afb405a45434a6427053de42d22a1a5321383aec9c90150d29909c19f688a80a8694c84e0cfb245405434a6427057d922e02a1a5321383adc9c91130129909c1d764e48698094c84e0cf7444a45404a6427067da1a522a025321382afd1569c90129909c1d3e4e54c48094c84e0e97272262404a6427056fa2ad312025321383adc9c89490129909c157e4eb4a48094c84e0adf265a52404a6427065f939522a02532138337c98a9150129909c11fe8ab48a8094c84e08ff255a45404a64270597e2ad3293962213828ff2569949cb1109c1c5f4e592a4c58884e0c7bc55435264c4427063de2ae1a93262213831ee9570d49931109c14df8ab4ca4a98884e0a7bc35a65254c4427062fe32d3292a62213831bf1569949531109c18f786b4ca4a98884e087bc35a65254c4427045fd3ae4a93152213823fc81725498a9109c10ff50b92a4c54884e0cafa72895262a442707d2d395293309221383c3e9ca98a9909109c14bf12b4c54c84884e0f27a72a52264244270697d3962a93212213835cf1150d49909109c1a774e586a4c84884e0d73a524352642442706b9e22e1a9321221383d969499849509109c10ff94b4a88c94884e0c5fa64255464a4427047fa02d2aa325221383a3e9ca98a9929109c193f4c58ea4c94884e08bfa55c75264a4427064fe3aa3293252213832be9cb1549929109c117f8eb8aa4c94884e0cb7c75445264a4427066be32a2293252213832ef1d50d49929109c19774e586a4c94884e0c7ba54435264a4427065de3ae1a93252213833ed0170d49929109c18f790b86a4c94884e0cbf475405264a4427066fa32a0293252213833dd1150149929109c19f686a80a4c94884e0cbf272c05264a4427066f93160293252213823fc9570149929109c18bf8ca90a4c94884e0c77c45485264a4427063de1aa42932522138317e98b2149929109c10ff4ab90a4c94884e0a6fc85a62c54a44270756d39730a2a522138393e98a9911529109c14f786b4c88a94884e087fca5a64454a44270657d39632a2a522138317e9911951529109c195f4e54ca8a94884e08bfc75a65454a4427047de1ad32a2a52213823fd0169951529109c10ff90b4ca8a94884e0a7bc35a64254a4427065ef30a3a92a522138317e9911949529109c117f8eb4ca4a94884e08fbc35a65254a4427047f60ad3292a52213823fd0169949529109c10ff90b4ca4a94884e0cb7c75445254a44270673e2aa2292a52213832fd1d50149529109c19ee88a80a4a94884e0cfd661405254a4427063f93220292a52213823fc9970149529109c1b1f4e58aa4c94e44c099fc75c55264a722606cbd39622932539130275e9571149929c89
  | 6 => 0x49d29909494bf40b8ca4e94c84a4c37c75445274a6425262be32a2293a532129319f1551149d29909498fd80b82a4e94c84a4c7ec15405274a642525abe02d39a22532129391e9cd153112990949e4f4e54e48094c84a4e1fa73474c04a6425271bd3923a60253212929fb0569d3012990949ccf8a98898094c84a4c3fc74a75404a64252713d3953920253212938de9c91d5012990949b5b4e58aa4094e4cc2da5a72c052722526617d2d39502939129330af971568149c894998557b8eb40a4e94a4cc2af5c45a05274a5266149ee3ad4a92913a330a5f3056a549489d19852fb80b52a4a44e8cc297da05c55244a746614bed2ae0292253a330a5f71571148129d19852fb4ab88a4094e8cc2d79a52435204a746616bce22e1a90253a330b5e69170d48129d198536f4ab88a4c94e44e0db7445405264a722704df92ae0293253913836dd1170149929c89c1a6f88a90a4c94e44e093fa55c85264a7227055fa02d3252a53913826fc9970149529c89c171f8ab4ca4e54c44e0b9f405a65272a6227058fe42d329395311382afc817a549ca9889c147f50bd2a4e54c44e0aafc55a95272a6227055f60ad4a9395311382afd016a549ca9889c147f90b52a4e54c44e0b97c65a552722622705dba02d2a93913113836dc9c88151529889c12ef48bd0a8a94c44e0eb7272205454a6227065b939102a2a53113832fd1d68151529889c14bf4cbd0a8a94c44e0a77a45e85454a6227045fe3ad42a2a53113823fd016a151529889c187f8eb50a8a94c44e0c7f405a85454a6227061bd39042a2a5311383a3e9ca98b2129889c193f4c54ea9094c44e08bfc55a75484a62270657d3952aa4253113822fe9d69552129889c1a6f4e44aa9094c44e0e1fa62a75484a6227069bd3912a84253113825df1169542129889c1c6f4ab4e41094c44e0c37a72255084a622705d3e2ad329391291382edd0169949c89489c166f90b4ca4e44a44e0ab7c95a6527225227055be22d3293a5291382afb0569949d29489c157e80b4ca4e94a44e0a3fc85a65274a5227055f932e0293a5291383a9e9cb1149929489c19cf8aa88a4c94a44e08bfa75c85264a5227071bd3924293252913830fe9d72149929489c1c6f4e410a4c94a44e0c37a72085264a5227063de1ad32b4252913821ef0d6995a129489c177a80b4aa4e4cc24e0dbd405a75252661270733d2922a92263213829df1169549131909c14fe80b4aa4898c84e0c77c45a55244c6427063fa02d2a92263213822ffa571549c89909c1b2f4e48aa4c44c84e0d97a72265252264270747d395316225321383a5e98a9c91129909c196f4e48aa8894c84e0cb7a72255444a6427045fe3ad2aa2253213823fd0169551129909c10ff90b4aa8894c84e0eb7272405444a64270759d3922261a5321382aef1569c90d2
  | 7 => 0x17a149ca9c898936f40b10a4e54e44c4937a05885272a72262583c42d39531539131275e8171949529c89893af8cb80a4a94e44c4977885c05254a7226259bc42d395025391313e1e9ca98a8129c89893af14b4c54094e44c4d97a72c65204a722624ebd2ae32902539131369e9cb1548129c8989b8f4c58aa4094e44c49d7c65c55204a722624bbc42e2a90253913131bf1529550129d09894fe40b8aa8094e84c4a7f405a74204c5426265bd3923a90262a13129df2568149c9150989a6f4e48ea4098a84c4c3fa74c75204c5426271bd3923a90262a13129fd0169d48131509891ef48b92a4e58084c4ea7a72a72254c04262537e2ad3a12a60213132de9c91d495301098963f8eb4ca4e58084c4b4fc55a65272c0426251fd3af4a93960213129be957a549cb0109892bf4cb92a4e58084c4977a45c95272c0426243fd4ae4a93960213128ff1d6a549cb0109894df8ab52a4e58084c4f17a65a72a7240426251bc4ad395392021313c1e9ca98a9c90109894ef92b4aa4e48084c4f27a72a72254c0426269bd3923a92a60213130fe9d31d4953010989c4f4e54e44a98084c4e2fa72c75254c0426271bd3923a92a60213129bf1569d495301098987f8eb4ea4a98084c4c6fc55a75254c042624afe32d42a0253992931df116a150129cc9494f786b4099094e64a487fca5a04c84a73252633d2a922a4253992921ffa97012a129cc9492bf40b8ca5094e64a4c7ec04c15284a732526d3f52d3953253912926de8171d49929c8949b4f8ea8aa4c94e44a4ba7c75c55264a722526d3e3ae2a932539129269f1d71549929c89493cf40b8aa4c94e44a4da7a72c05264a72252793d3964293253912934df1d52149929c8949a4f4e590a4c94e44a4977a05c85264a72252753d32d396025391293a9e9ca9928129c89495cf8ab4c94094e44a4da7a72c65204a7225249fd02e3a93253a129347f1d51949929d0949a6f8ea88a4c94e84a4d67c55445264a742526abe3262293253a12925de8171149929d0949a7d8ea82a4c94e84a4d76c45415264a7425269f63ae0a93253a12935db1170549929d09498bf8ca4c98094e84a4a7ec15a64c04a7425262fe32532a0253a12924ff1d69950129d09492ef88b4ca8094e84a497ec15a65404a7425253f902e32a0253a12929fb0569950129d09498bf8cb4ca8094e84a4c7ec15a65404a7425243f60ad32a0253a12929fb0569928129d09498bf4c98ca4094e84a4d37c75445204a742526b3e2aa2290253a12931df1931148129d09498ef4c988a4094e84a4d3f475405204a742526bba22a0290253a129257fa570149cc990949e4f4e540a4e44c84a4b67c55a0527226425253bc4ad029391321293c9e9cba549c899094966f4ebd2a4e44c84a4d27a72c45474a642524afd02e3293a532129307f1d519
  | 8 => 0x690008309831210200080758401100080002520803006c1004000104001082004802002c00442080200140d10001395000002000ca40040200004024612300900121130000010100400018641840200c0100c410804031c211000008000105c020000000570000900c42194411000630021304610800001821004200000000140180091082b1800001ce300c4198062008e610082400402a4711002120c0338004000202010050040280045bde100467008010b80269c001800662800080a410420002a420c20400080084408c0d114881046300800400000144709861100c1200a408418df4a98aa4098884e6a7f405a55204c4427353f902e2a202522139a9df1169509130109cd4ef88b4aa4898084e6a77a45c54444a0427353dd2ae2221a502139a9bf1568149531909c94ef88b40a4a98c84e4a77c45a55204c6427253fa02d2a90263213922ff0169551d29909c917f8ab40a8e94c84e48bfa05c75454a64272753d39622a2a53213932df1d51151529909c995f4e540a8a94c84e48bfc75a05454a6427247be22d02a2a5321393a9e9cb1531129909c956f8eb8a98894c84e4cb7c74a55444a64272673e2a52aa2253213932df1d28151129909c91ef80b4aa8894c84e4cb7a72a05444a6427247be2ad02a2253213922ff1d69550129909c91ef88b4aa8094c84e487fc85a55404a6427265be3aa22a025321392bdc8171150129909c98bf8ca4ca4098a84e4a7bc35a65204c5427253fa02d3290262a13934df1d51149909509c98bf4c840a8c94a84e48f7c45a05464a5427264fe3263a93252a139333f1931549929509c99af8c988a4c94a84e4c5fc64c85264a5427262fe3293220252a13922ff1d69950129509c91ef88b4ca8094a84e48fec15a65404a5427243fe42d32a0252a1392cbf1569949cb0109c947f92b4ca4e58084e4c5fc65265254c04272537e2ad3292a60213929fb0569949530109c9a5f4e58aa4c84084e4d37c7544526420427243fe52d2a232502139317e9909551928109c91ef88b4aa8c94084e4c9fc64c75264a0427266be32622932502139337d1930149928109c98bf8ca4c88a94084e487fca5a64454a04272657d39532a2a50213922ff1d69951528109c91ef88b4ca8a94084e48fbc35a65454a042724e7d02e2a93253953121fb056a150129ca98933f8eb4ca4094e54c49cfc55a65204a72a6266bd32622902539531317e9922148129ca9894ef88b409d094e54c493fc05a75684a72a624b7d02e2a94253953131fa813054a129ca989a7d8eb82a5094e54c4d6ec55c15284a72a6263f64ae0a94253953121fe817a142129ca98970f8ab4ca4e54e44c4b97c05a65272a722624dbf42e02939539131365e9948149ca9c898972f4cb40a4e54e44c4b37c85a05272a7226259bc42d0293953913126de8
  | 9 => 0x87b28c27f225d0352f85331648d8b2bd0bdbef65cdfd91b3f65ec913c1af6422830c8a8c5eca4e20f573ec8d577a6a1ec85671d2bbecbd96af24206b5a2e00f4ed0a9688f659dbd97b2f6542bd97b2f65ecbd977bea1ecbd948ff64893d905df64f858bfb26df641e86265ab19fd9777f64ce4bf7b2f65ec9947b243fd1dde7b2f64c8fd97b2f65ecbd91d0777bd602313f64983d97b2f64bd5637b2f65eca0c102f65ec9394f7f3e48d56835ad5ecbb79d31fda0fd97b2f65153d97b28bb4eb611f2399ec97352ff65ecbd97b2f645e301d267f08be4c1cdd7089bc5b94f65ec80c4cd5d7e5926efbf6594a80d96737086c12efa265ee5629346becbd9195f65ecbd9546f65ecbd97b2533bada6fb2f65ecbd97b263b715ef3777ec8ab8f75a2708d22d7b2659ecbd9083be9affc27b2f6443e8f9e23abecb257b2f65ecbd97b2f65be5b00aa4f9ecbd90c8f641d3d9674f65ec9117b2f659ffd97b2f49ecbd97b24d1ec9a7267405ecbd97b23bbeca22a9af65eca1297d5805b3d93f2f65ecbd90baf6476fd97b2f65ecbd9021864e8bcc6a97d3ec9f315698fecac3d43c6d627d97b240841c7e7b2f65ecb553149976e261fb217a97d03bc66801df4a13d952c6d7baccca0e81ae988024b67d97b2a3141bd97b07a4da7d97b2a01ecbd9735f64c73d92d3643ecbd9468f65d607d552b61ecbd9239f65ecb157b22e5c5bb87a5f65a6fd97b2f65ecbd90d1f65ecb4f5cf2c6caf92c2eb7f903d97b2c1bdb15f984e89890347b2d76eafd962d460b425f179e5f53bd9685ac4029ab7b2f64537d97b2f65ecbd97b2f65ecb46fb2f65ecaaafb2f64f0fd97b2bfdecae47b2de906e052845119dd10ebda5dc46079a19fdecb82fb2f65ec919c86d82190aafb26c7ecbd94a6f6529de8f0f227ec8207b2735ec9b22c2170aa07b53400c7d652f00f65ecb6382af65ecbd95a02b3d1bd94dc090971b8f9dda9cfbd97b2f65ecbd97b279c25960fb2f64607d9778db532ae5569f65ec8fffb2cc0e73d92a0e67ecbd94e5f654a9efd16f6518e8d3344cbbf71f21231f6bc8afb2949ecafe008e57ec9beb15f65bf2d0bcde37ec9b3fb2b1759148cf14ebecbd97b226decbd97b2f64bcbd97b2f65ec8987b2f65ecbd91ae571a07d9721395c93d97b25a52d7d9437a3a67ddf3d4f65ecbd97b2f656a488183ce5ecbd97b2d5becbd97b2b80013d97b25c5ecb737b27254b35273f7d072d260001084c020001084a108801010640002008125014b200880018840002010480104201ac00118a21880320602080c60004030003080060080030182280000800001c0403402000011000660400000111807b0080001022080000040000082000050ac0100023031240142004404004070006201800104031a8801804120080104213202018da11140020062184e0000
  | 10 => 0xbd90440a9ecb197b271fecbd95ad58aee3d935b168b9fd9669f658c3d97b2f65ec8437b2d39ec8c5eacf65c09cc7b2f64ea09f25269f874314c6181ecbd97b2f641ee92fb283ddf367d4873dd7bd9740a6bca6f977d1a892e6bd3ccf6cb4fdfb11348665b2d765fec91efb2f65ec823a709bbecbd97b2f64e064f9cedc693c357b2f650f7d94c5dd2f8bd97b2383ecbd97b2f6556a891489419cfd97b2f65ec8d37b2f6412d837b2f65eca617b2f65ecbd97b29d1ecbd97b27fdecb509a3f64b93d97b2671368741b9a6469dd67b2f65ecbd97b2e9fecbd97b2f6535bd92449d7eca90167727ecbd97b28b1ec92cf86f65eca16fb2f65ecbd97b2f65ecbd943af65ecb457b2f65ecbd97b2f6565d4956592decbd96f7f64b77d962cf65ecbd97b23626eb387b2f6490e06298774083d97b2f650c3d95d8cdd6e7d97b2d87b47a67b2143ec9b37b2f65ec8391c69de66bd921121c661db3a6f64b7cf9b1ff65511202f3f651cafeedf7951b3d971aa7decbd97b23c7ecbd90e2b3895776d10f65ecbd97b2177438ecde6f65ecbd97b2388db728da7bbba191e7b2f64db3d97b2f65ec911af1ccbecbd97b2eebecbd9034f65ec9357b29bee76eb7b2590e37d9757d6048b6698a54fbfe706dd36b1a7b1143f65ecbd97b2f65ec938fb2f65ecbd97b2f65dcd7cb512aed0fd9779f65ecbd94e3f6586af564478fecbd97b2f65c51bb7b2f6467bd916fde725e774f2a19ecab02be883ec9a9ce9f65ecbd97a7f65ecbd9257f65ecbd97b2f65ecbd97b2f65ecbd9055f65ecbd97b260728ac8fb2f6461f0b7b2f5430bd94ab81dec8787b2d75ecbd97b2bca80e9dcccb67ec93b309655ec93d7b2f65ec831a79f65ecbd97b2f1b0efd97b2bf1ecbd97b262c6ed47f718b8e0bd97b2f641b3d92e52bdecb547527c733bd97b2f642e737d2d9d9ec967d21f65ecbc7b52cf9ecbd97b2f65ecb017b2f65ecbd96d5f651dbd97b2f642991c7b2e7163fd92100a0ccd287b2c50cd47532ed99e814afb2f65beb14fb26d0827d97b24bdecbd94c9f641e3d94bdf65ecbd97b2c7fec9938cebc450559a42e164e89a319e7a209aa2ee5b7ecbd91f9357ecb967b261041aedf5f6c2f0a132cb21454c9600eb968071751ed7366ed11ebe72a537c170f65b71256f1b51eca18facf65db7d97b2eb7710fc7b29c5eca4893386c822f42fb33beca6f666a29ecbd964eb9bec9a0e3af64c2a84b2457a8b8421ded96480b77b2237ecbd9586f65ec8b0f91f64e29f9985001a80622255934fd9e2465d3d583b48db1d6b38a999f65ecbd97b2f6438caf85af65eca0ad0df65ecbd97b2f65ec9e67b2f65c48f57b2f65ec8a8d45f65423d93a1f3dec986e96f64d5fc2b20f641ba2670451af13d97b2b4becaf69bd23b757d95def65ecbd97b2f64d73d97b24adecbd960cf65ecaf
  | 11 => 0xecb341dc1cd4916a2f4973ec9ee9d4684d67d93db4646030743ec38560117b2f65ecbd930b7b1eca94fb2763ecb5398951cd22b611fac7807d94201ca44bd944a31ce7cdc7b2345ecbd97b23d0c63d93ecf65ecbd92a52c1ec8f27b2af8b47d97741372e3d97b2f65ec8df7b2f64d8ad8a8ac0c3c8ed4164ff7a780fb2f53ecbd97b2f6574ae36e7f651fa73499f65ec950842507143d9346889ec8847b2879ecbd97b2cb9cc09de98f65ec89355bf65eca09fb2f65ecbd9269f65ecbd9116bedc0e1a7b211ec8bd940577e5ab8cb297195bbd929e2b8fe94ffb2f64f695e2e366decbbb7a329368c8e20c75e035107b2f65ecab87b2b31ec8ad104bd88ea29fb23dbecbd976e3aeb6bd97b2563ec880d27b6b48bd977ef65ecbd97b2dec98bd97b2f6407f0c706f65c3bd96ea5bdec81e7b2a6c433d97b29a2e18d7b4c6cb8f39b71cb1becaf1fb2b79ecbd92c3f65ecabc196f65ecbd9428f65b3a8245ff65ec9379e1f64d7c9e07e621733d9638cc9ecbd94c1b3d2abd933df65ecbd97b2dc36572d002977ecb7221b369ecbd9423f65ecbd97b2e68a8c2fdb725decada7b2f650b38bf97828630a164cf6471d40fb2265d82ccfb2f65ecb47720f65c1ea0fb2a97ec8b27b2f655323069f839b27d914c102bf7d936e518d1c95273f65ecbd9304384a1fd97b2623eca859f0cbfec8d03008b3e0ecfa1ef641981675454c7c7d97b252decbd97b2f65387d97b2a51abbd959d1515efd97b2f65123d97b2947ec8e97b2e8becbd95856b0aa5f86b618fe33d9118f03c21ee7b23786c242391ed1a95298b0a6011bc99909ffbbe7db892e6cee78713f43ecb487b2f65ecbd97b2f640425d594f21ec936fb2e9b6dba090df10c071079c4290085204aa8eb35c27b2f65ecbd90cc07de9838917f65ec8a87b2bafd71c2ce43cbecaee2ac2345ad5bfb2f65ecb4961f56c35af0fb2f6453bd97b2f64ec16c302f65eca3bf72f64aac5397c3d3ecbcd7ae5648aca2f67f644b40ef32a9f73a76ec86f1963d97b22ffecbd97b2ade16fd904c5d598d14fb2f65ecbd9533521ecbd920af24a77d944df65ecbd90cf74becab8fb2f65043d9098f6404cb3094bb5ecb637b2f65ecbd97b2f64b297d7b2141ecbd97b2e55ecbd945eb19ecbd97b2b24cebd93f4f65eca7e7b2f65eca50fb2e79ecbd9751f65ec932030f65ecbd97b2f65ecadef99f652fdd57b2f642dbd949bf658efd97b283fce9fe538f65ecb6519cb93ecbd95d1f6487176fb255fcbbd94ad5c3ecba42281444bfd90bef04648b2a74f65ecbd97b2f65ecbd97b21188dfd9646f65ec99f9e09e9ecb3efb2f65ecbd97b2f65ecb849cfe19ca3717b2c141803e6f0917eca277b2f65ec928fa21a5eca7efb22dac95c3fb2f657efacc4362486b1a7b2f648dbd97b2d001661ff61dd8bffd9710f64da
  | 12 => 0x13ec9d97b2f65ecbd97b2f65ecbd97b2f65584dfe152966b3d97b226becbd92a4f64e9229553eab7beb30aef65ec86c856f656cbd97b2cf5320e8ceac01eca88c4f9ebecbd949e77a8b00da5df65ecb5afb2f65ecbd97b2950513d924ead0c9814282a040bbd97b2e1432bd95fff656ebd97b2aad003d97b2391e010c7b2569ecae17b2f65ecbd9331c566dfd95d9f64138d27b2eca4dc93fb2f5fecbd97b2f645a7d97b2f65ecbd97b2f65ec931aae322058c17b2f65813d95f723dec955627afcdfbd969a47d39fd97b2f6546fd9466c45ecbd968c66096d585a6716e0f98e10e4fecbd97b25d1707d96d37dea6d994b2f64a2f6c33e1b5ecbd97b2f65eca95bd66f38bd7c7b28e9503777b2f65a0bd9019f65ecbd95d4f65ecbd97b2c10c31f0215ab05d6f23ea881457d97b2f65eca3d248dbd243d91713dc179e0fb2083ecad574bf65ecbd97b2f65ec9a2fb2f64d2bd97b28afecbd97b2d4deca4a7b2bdc9bbd94b03fbe1f45b0ff6453c6e9c36e6053d9551f643cf1cd74179ced761dff65ecbd97b2f65ec84e7b2f65ecbd97b2f65ecbd9200791ecbd9011e45ec86f7b28a3ecbd92fcf65eca5e49d545ecb2b177f640cbd93967cb3d895fb21a0fc76bbc0f64f2efd168f64637d97b2f6451bd97b2f65b4116b881e856f2f531249ecbd96c0f65ecbd97b2f65ecbd97b2f65ecb6de87f65ec84ffb2f65ecaefcd450a64fd938e42decb707b26f933c77fb2f65ecbd92cef64393d97b204decac23aef659e078d8af6560088fb2d62383d97b2692dd4aa54a8c9ecbd97b2f65849ad7b2cd5203d95c7f645ebd97b2f65ec909f2d512ee7d5dc33ec9f7d91296e10a7d96d2cebeca6c390f65d93747b2b57ecbd97b20398c7d948e7dbec8ec0a51d8400440650535db5f374f65ec88a0d8c3d9fa097b2f65ecaabfb2f65254477b228164c92c8861decbd9344ba6a709ffb241601fd9642f64f93427b2f65ecbd97b2f649502e00c9aa5d0fbfb23cdecb627b2f65ecbd97b239348fd97b2381ec80f7b2f648c5c04c404879dbdebc88d5651dfb2ed6cddd1fb2f65c61e4fb2d669fbd97b280dec93c7b290509fd97b2a0bec8484b4f65ecbd97b2f65eca2afb21cfec9cbdd0f647fbd97239f515b6b48cf649afd95720746dbd97b20a51f3d97b2f65ecbd978aed326aaf9faf649dfd40c6f65ec8d97b2abd693d9742803ecad720e8d5eca49fb216fc998d4229a59c402b7a2c5ecbd97b2f64f9fd97b2f65ecbd97b258fecb7f7b2f6424bd92b5f65108d68705acd7baefb2aea6185fcd34f616133417f64bc3d9766f654e786f951011c3d914a336bfbd9307f65ec8941472633e3d97b2f64dcbd97b2f65ecbca7b2f65ec8597b2f65ecbd92bbf6434fd97b2bc1d8fd97b25746a1f72064c3ecb1aa58f646a6bd439811343d97b2f652dfd97b272b
  | 13 => 0x3d9424f65a8fd97adf65573c4cf36ffec982c6ef65ecbd9438ea7ec9a5ed9a0e37219f7ff652268e3ebf64652a87b2de5ecbd97b2f65ecbd97b2f65ec89ce5b2ed127d97b283a0e2c44aef65e6d367b2f65ecbd97b2f65ecbd94d9f65ecbd97b2f65da902d42f65ec906fb28cb16cfa4b35ecb1140537cd8b71431ef1f1aae0c9c56ab3e75159af64e67d97b2f1c65fd947106d300eb74963decb597b28f12c7d97b2a93ecbd955413c467a55bbca9c7fd96e53d924ba1d4d43adae157b2f65eca1afb21ddecbd97b234b11fd925ad6fecbd97b2f65ecba77b2d
  | _ => 0
def u168K9 : Nat → Nat
  | 0 => 0xa94e8480afe80a4a94e8480ebf8aa4e64c8480abf8aa4e64c8480ebf4ca4e54c8480cffd2a4e54c84808ff92a4e54c8480cff52a4e54c8480aff12a4e54c84808ff12a4e54c8480e9f4e54c54c8480abf8ea4c54c8480abf4ea4c54c8480e6f4e54e44c8480eaf4c54e44c8480eef4aa4e44c8480e7e4e54e04c8480ebe4c54e04c8480e6e4e44e04c8480efe4aa4e04c8480efed2a4e04c8480e3f4e68e94c8480e6f4e48e94c8480e7e4e08e94c8480afe80a8e94c8480cbf4c58e94c8480cff8aa8e94c84808ff4aa8e94c8480abf8ca4e94c8480aff8aa4e94c8480aef88a4e94c8480af786a4e94c8480afe80a4e94c8480cbf4c54e94c8480c7f8ea4e94c8480cbf8ca4e94c8480cff8aa4e94c84808ff8aa4e94c8480cef88a4e94c8480cf786a4e94c84808f786a4e94c8480cfe80a4e94c8480ebf4e68a94c8480e9f4c58a94c8480eef4e48a94c8480efe4e08a94c8480cff8e98a94c8480cff4e98a94c8480aff8ea8a94c8480aff4ea8a94c8480cbf4e68a94c8480cef4e48a94c8480cfe4e08a94c8480cff8ea8a94c84808ff8ea8a94c8480cff4ea8a94c84808ff4ea8a94c8480abf8ca4a94c8480aef88a4a94c8480afe80a4a94c8480ebe4e68094c8480efe4e58094c8480ebe4c58094c8480eee4e48094c8480efe8a98094c8480afe4ea8094c8480cffd2a4e64a8480aff92a4e64a8480cff92a4e64a84808ff92a4e64a8480cff52a4e64a8480aff12a4e64a8480cff12a4e64a84808ff12a4e64a8480e4f4e54e44a8480eef4ca4e44a8480eeb4e4cc24a8480afb4eacc24a8480e6e4e44e04a8480efacc24e04a8480efe4ca4e04a8480e6f4e48e94a8480efbcc28e94a8480e7e4e08e94a8480aff4ca8e94a8480cfbcc28e94a8480cff8ca8e94a8480cff4ca8e94a84808ff4ca8e94a8480efbcc24e94a8480e7f8ea4e94a8480aff8ca4e94a8480eef88a4e94a8480aef88a4e94a8480efe80a4e94a8480afe80a4e94a8480cfbcc24e94a8480c7f8ea4e94a8480cff8ca4e94a84808ff8ca4e94a8480cff4ca4e94a8480cef88a4e94a8480cfe80a4e94a8480eef4e48c94a8480efe4e08c94a8480cff8e98c94a8480cff4e98c94a8480aff8ea8c94a8480aff4ea8c94a8480cef4e48c94a8480cfe4e08c94a8480cff8ea8c94a84808ff8ea8c94a8480cff4ea8c94a84808ff4ea8c94a8480ebf4e64c94a8480eef4e44c94a8480efe4e04c94a8480cff8e94c94a8480cff4e94c94a8480aff8ea4c94a8480aff4ea4c94a8480ebf8ca4c94a8480eef88a4c94a8480aef88a4c94a8480efe80a4c94a8480afe80a4c94a8480cbf4e64c94a8480cef4e44c94a8480cfe4e04c94a8480cff8ea4c94a84808ff8ea4c94a8480cff4ea4c94a84808ff4ea4c94a8480cbf8ca4c94a8480cef88a4c94a8480cfe80a4c94a8480
  | 1 => 0xf6e40a4e54e4480f4f4e54c54e4480bef92a4c54e4480f6f4e54c94e4480faf4c54c94e4480f6f8ea4c94e4480b6f8ea4c94e4480bef8aa4c94e4480fee80a4c94e4480bee80a4c94e4480eef90a4c94e4480aef90a4c94e4480def4c94a94e4480bef8ca4a94e4480bef4ca4a94e4480fee80a4a94e4480bee80a4a94e4480fcf4ca4e54a4480fce40a4e54a4480def8ca4e94a4480def4ca4e94a4480dee80a4e94a4480feb48a4e5cc2480ffa40a4e5cc2480afb90a4e5cc2480efb50a4e5cc2480f6b4e54e4cc2480beb8aa4e4cc2480feb4aa4e4cc2480fcb4e54a4cc2480beb4ea4a4cc2480deb4a44e9cc2480dfb4aa4e9cc2480cfb50a4e9cc2480f7e4ca4e54e0480f6e48a4e54e0480f5e4e54c54e0480bfe92a4c54e0480f6e4c54e44e0480f6e4ca4e44e0480b6e8aa4e44e0480f6e4aa4e44e0480f4e4e54a44e0480b6e4ea4a44e0480f7a4e5cc24e0480f6a4e4cc24e0480fea4a4cc24e0480f7e4e54c94e0480fbe4c54c94e0480f6e4e44c94e0480fee4a44c94e0480bfe8aa4c94e0480fee88a4c94e0480bee88a4c94e0480ff686a4c94e0480bf686a4c94e0480efe90a4c94e0480afe90a4c94e0480d6e4e48a94e0480dfacc28a94e0480f6e4e44a94e0480fce4a44a94e0480ffacc24a94e0480dfe4c94a94e0480bfe8ca4a94e0480bfe4ca4a94e0480fee88a4a94e0480bee88a4a94e0480f4e4e54e44a0480fee4ca4e44a0480fce4aa4e44a0480fce4e64a44a0480bce4ea4a44a0480fca4a44e24a0480fea4e4cc24a0480fca4a4cc24a0480bfa4eacc24a0480e7f4ca4e54e8480e5f4e54c54e8480aff92a4c54e8480cff92a4c54e84808ff92a4c54e8480aff12a4c54e8480cff12a4c54e84808ff12a4c54e8480e4f4e54a44e8480e7b4e5cc24e8480eeb4a4cc24e8480e5e4e54a04e8480ece4a44a04e8480efacc24a04e8480e7f4e58c94e8480eef4a48c94e8480efe4a08c94e8480aff4aa8c94e8480cff4aa8c94e84808ff4aa8c94e8480e7f4e54c94e8480ebf4c54c94e8480eef4a44c94e8480efe4a04c94e8480e7f8ea4c94e8480a7f8ea4c94e8480ebf8ca4c94e8480aff8aa4c94e8480eef88a4c94e8480aef88a4c94e8480ef786a4c94e8480af786a4c94e8480efe80a4c94e8480afe80a4c94e8480e5f4e58a94e8480edf4c58a94e8480ecf4a48a94e8480efbcc28a94e8480ede4a08a94e8480cff8c98a94e8480cff4c98a94e8480aff8ca8a94e8480aff4ca8a94e8480cdf4c58a94e8480cfbcc28a94e8480cff8ca8a94e84808ff8ca8a94e8480cff4ca8a94e84808ff4ca8a94e8480efbcc24a94e8480cff8c94a94e8480cff4c94a94e8480e7f8ea4a94e8480a7f8ea4a94e8480aff8ca4a94e8480aff4ca4a94e8480edf8aa4a94e8480eef88a4a94e8480aef88a4a94e8480efe80a4
  | 2 => 0x4c94a44c09bf4ea4c94a44c0daf88a4c94a44c0dbe80a4c94a44c0cbf4e6d094a44c08ff4ead094a44c09bf8ca5094a44c09fe80a5094a44c0f3e4ca4e44e04c0b7e8aa4e44e04c0f7e4aa4e44e04c0a7e10a4e44e04c0f3e4e54c44e04c0f2e4e44c44e04c0bbe8aa4c44e04c09be12a4c44e04c0f6e4e44a44e04c0b7e4ea4a44e04c0bbe4ca4a44e04c0afed0a4a44e04c0f7e4e54894e04c0fbe4c54894e04c0fee4a44894e04c0dfe4a94894e04c0fbe8ca4894e04c0bbe8ca4894e04c0bfe8aa4894e04c0bfe4aa4894e04c0abf8aa4c48e84c0abf4ca4a48e84c08ff52a4a48e84c08ff8aa4898e84c09ff8aa8894e84c09ff4aa8894e84c0df74a48694e84c0dfe4a48094e84c0abf8aa4c44e84c0abf4ca4a44e84c0cff8a98894e84c0aff8aa8894e84c0aff4aa8894e84c0cbf4c58894e84c0cff8aa8894e84c08ff8aa8894e84c0cff4aa8894e84c08ff4aa8894e84c0ef74a48694e84c0cf78898694e84c0cf74a48694e84c0cf788a8694e84c0efe4a48094e84c0ebf8aa4e68884c0abf8aa4e68884c0ebf4ca4e58884c08ff92a4e58884c0cff52a4e58884c0e9f4e54c58884c0abf8ea4c58884c0abf4ea4c58884c0e7e4e54e08884c0ebe4c54e08884c0efe4aa4e08884c0cbf4c54e98884c0cff8aa4e98884c08ff8aa4e98884c0cff4aa4e98884c0cbf4e64a98884c0cdf4e54a98884c0cfe4e04a98884c0cff8ea4a98884c08ff8ea4a98884c0cff4ea4a98884c08ff4ea4a98884c0aff50a8a94e6480cff50a8a94e64808ff50a8a94e6480b7f8ea4a94e6480aff90a4a94e6480cff4a99094e6480aff4aa9094e6480cff4aa9094e64808ff4aa9094e6480cef48a9094e6480cfe40a9094e6480cff8a95094e6480a7f8ea5094e6480abf8ca5094e6480aff8aa5094e6480af786a5094e64809ef48a8c94e54809fe40a8c94e54808ff50a8c94e5480b7f8ea4c94e5480bdf8aa4c94e5480aff90a4c94e5480def4c94894e5480fee80a4894e5480dfe4c94094e5480dee4894094e5480fee88a4094e54808ff4ca9094e5480cff4c95094e5480e7f8ea5094e5480a7f8ea5094e5480aff8ca5094e5480edf8aa5094e5480adf8aa5094e5480eef88a5094e5480efe80a5094e5480f9f8aa4e64c5480ebf90a4e64c5480abf90a4e64c5480fcf48a4e54c5480fde40a4e54c5480edf50a4e54c5480f3f4e68e94c5480f5f4e58e94c54808ff50a8e94c5480bdf8aa4e94c5480aff90a4e94c5480d7f8ea4e94c5480ddf8aa4e94c5480cff90a4e94c54808ff90a4e94c5480ebf4e69094c5480edf4e59094c5480cff4e99094c5480aff4ea9094c5480cbf4e69094c5480cdf4e59094c5480cff4ea9094c54808ff4ea9094c5480cef48a9094c5480cfe40a9094c5480abf8ca5094c5480adf8aa5094c5480f6f4ca4e54e448
  | 3 => 0xe09fe48a8094c84e0e7f4ca4e58884e0e5f4e54c58884e0cff92a4c58884e08ff92a4c58884e0e7b4e5cc28884e0cbf4c54c98884e0cff8aa4c98884e08ff8aa4c98884e0cf786a4c98884e08f786a4c98884e0cfbcc24a98884e0cff8ca4a98884e08ff8ca4a98884e0cff4ca4a98884e08ff4ca4a98884e0f5f4e54c54884e0aff90a4c54884e09ff92a4c54884e09ff12a4c54884e0f4f4e54a44884e0f7b4e5cc24884e0feb4a4cc24884e0e7f4e54c84884e0ebf4c54c84884e0eef4a44c84884e0aff8aa4c84884e0eef88a4c84884e0ef786a4c84884e0af786a4c84884e0efe80a4c84884e0ecf4a44a84884e0efbcc24a84884e0ebf4c88c94884e0d7f4e58c94884e0cbf4c88c94884e0cff4a88c94884e09ff4aa8c94884e0b7f8ea4c94884e0bef88a4c94884e0bf786a4c94884e0bfe80a4c94884e0aff90a4c94884e0d7f4e54c94884e0dbf4c54c94884e0cff4a84c94884e0d7f8ea4c94884e097f8ea4c94884e0dbf8ca4c94884e09ff8aa4c94884e0def88a4c94884e0df786a4c94884e09f786a4c94884e0dfe80a4c94884e09fe80a4c94884e0cff90a4c94884e08ff90a4c94884e0f5f4e58a94884e0fcf4a48a94884e0edf4a88a94884e0d5f4e58a94884e0ddf4c58a94884e0dfbcc28a94884e0cff4c88a94884e09ff8ca8a94884e09ff4ca8a94884e0b7f8ea4a94884e0bef88a4a94884e0bfe80a4a94884e0dfbcc24a94884e0cff4c84a94884e0d7f8ea4a94884e097f8ea4a94884e09ff8ca4a94884e09ff4ca4a94884e0def88a4a94884e0dfe80a4a94884e09fe80a4a94884e0bbf4aa8894e64c0dbf4aa8894e64c09bf4aa8894e64c0f3f4e54c94e44c0b3f8ea4c94e44c0bbf8aa4c94e44c0baf88a4c94e44c09bf4ca8a94e44c08ffd0a8a94e44c08ff50a8a94e44c0dbf4c94a94e44c0bbf4ca4a94e44c0bfe80a4a94e44c0affd0a4a94e44c0aff90a4a94e44c0aff10a4a94e44c0e7f4e5d094e44c0cff4a9d094e44c0a7f4ead094e44c0aff4aad094e44c08ff4aad094e44c08ff4aa9094e44c0e7f4e55094e44c0cff4a95094e44c0a7f8ea5094e44c0aff8aa5094e44c0aef88a5094e44c0af786a5094e44c08ff4aa1094e44c0ebfd0a4e54c44c0abfd0a4e54c44c0dbfd2a4e54c44c0f2f4e54e44c44c0faf4aa4e44c44c0aaf10a4e44c44c09bf8aa4e94c44c0daf4e48a94c44c09bf8ea8a94c44c0dbf4ea8a94c44c09bf4ea8a94c44c0fbe80a4e64a44c0dbf92a4e64a44c09bf92a4e64a44c0f4f4e54e44a44c0faf4ca4e44a44c0eefd0a4e44a44c0eef50a4e44a44c0dbf4ca4e94a44c0dfe80a4e94a44c09fe80a4e94a44c0cffd0a4e94a44c08ffd0a4e94a44c0cff90a4e94a44c08ff90a4e94a44c0cff50a4e94a44c0cff10a4e94a44c08ff10a4e94a44c0daf4e44c94a44c09bf8ea
  | 4 => 0x68894c84a4ecf4e58894c84a4ecf8a98894c84a4ccf8a98894c84a4aef4ea8894c84a4ebf4e68094c84a4eef4e48094c84a4cff8e98094c84a4cff4e98094c84a4eef8898094c84a4aff4ea8094c84a4cbf4e68094c84a4cef4e48094c84a4cff8ea8094c84a4cff4ea8094c84a48ff4ea8094c84a4abf8ca4094c84a4aef88a4094c84a49fb40a8a94e4cc2bfb80a4a94e4cc2d7b4e58094e4cc29fb4aa8094e4cc2f7b4e54094e4cc2dfb4a94094e4cc2bfb8aa4094e4cc2f4b4e54e44a4cc2beb80a4e44a4cc2feb40a4e44a4cc2dfb80a4e94a4cc29fb80a4e94a4cc2dfb40a4e94a4cc2afb52a4a44e8cc2afb8aa4894e8cc2afb80a4894e8cc2efb4a44094e8cc2afb88a4094e8cc2af386a4094e8cc2b7f8aa4c94e44e0f6f88a4c94e44e0b6f88a4c94e44e0f7e80a4c94e44e0b7e80a4c94e44e0b7f90a4c94e44e0e7f90a4c94e44e0a7f90a4c94e44e0d7f4c94a94e44e0b7f8ca4a94e44e0f7e80a4a94e44e0b7e80a4a94e44e0f3f4ca4e54c44e0d7fd2a4e54c44e0d7f52a4e54c44e0f2f4c54e44c44e0f6f4aa4e44c44e0f6f4e48a94c44e0bfe40a8a94c44e0affd0a8a94c44e0aff50a8a94c44e0d6f4e48a94c44e0dfe40a8a94c44e09fe40a8a94c44e0cffd0a8a94c44e08ffd0a8a94c44e09ff50a8a94c44e0cff50a8a94c44e08ff50a8a94c44e08ff10a8a94c44e08ff4aad094c44e0f6f4e49094c44e0b7f4ea9094c44e0d7f4e59094c44e0dbf4c59094c44e0d7f4ea9094c44e097f4ea9094c44e09ff4aa9094c44e0e6f4e49094c44e0aff4aa9094c44e0cbf4c59094c44e0c7f4ea9094c44e0cff4aa9094c44e08ff4aa9094c44e0e6f4e41094c44e0aff4aa1094c44e0c6f4e41094c44e08ff4aa1094c44e0f6f4ca4e44a44e0d7f8ca4e94a44e0d7f4ca4e94a44e0d7e80a4e94a44e0d6f4e44c94a44e0def88a4c94a44e08ffd0a4c94a44e09ff90a4c94a44e0cff90a4c94a44e08ff90a4c94a44e0cff10a4c94a44e08ff10a4c94a44e08ff4cad094a44e0b7b8aa4e4cc24e0f7b4aa4e4cc24e0f6b4e44a4cc24e0b7b4ea4a4cc24e0afbd0a4a4cc24e0cef4a44898c84e0cff8aa4898c84e08ff8aa4898c84e0cff4aa4898c84e08ff4aa4898c84e0b7f8aa4e44c84e0f3f4e54c44c84e0f2f4e44c44c84e0bbf8aa4c44c84e0f6f4e44a44c84e0b7f4ea4a44c84e0bbf4ca4a44c84e0f6f4e48894c84e0d7f4e58894c84e0dbf4c58894c84e0d6f4e48894c84e09ff8aa8894c84e09ff4aa8894c84e0dfe80a8894c84e0f774e48694c84e0df78898694c84e0ff680a8694c84e0d774e48694c84e0df74a48694c84e0df788a8694c84e0df748a8694c84e0df680a8694c84e0f7e4e48094c84e0dfe8898094c84e0df68698094c84e0bfe48a8094c84e0d7e4e48094c84e0dbe4c48094c84e0dfe4a48094c84
  | 5 => 0x4c4ebf80a4e68a84c4abf80a4e68a84c4eef40a4e48a84c48ff40a8e98a84c4aff80a4e98a84c4cff80a4e98a84c48ff80a4e98a84c4cff40a4e98a84c4ebf4e64098a84c4eef4e44098a84c4cff4e94098a84c4aff8ea4098a84c4cbf4e64098a84c4cef4e44098a84c4cff8ea4098a84c48ff8ea4098a84c4cff4ea4098a84c4bbf8aa4e68084c49ff92a4e58084c4f6f4e54e48084c4aff8aa4e88084c49ff8aa4e98084c4dbf4e64a98084c4ddf4e54a98084c4def4e44a98084c4cff4e84a98084c49ff8ea4a98084c49ff4ea4a98084c4ebf8aa4e68084c4abf8aa4e68084c4ebf4ca4e58084c4cffd2a4e58084c4aff92a4e58084c48ff92a4e58084c4cff52a4e58084c48ff12a4e58084c4e9f4e54c58084c4abf8ea4c58084c4abf4ea4c58084c4e6f4e54e48084c4eaf4c54e48084c4eef4aa4e48084c4ebf4c54e98084c4aff8aa4e98084c4cbf4c54e98084c4cff8aa4e98084c48ff8aa4e98084c4cff4aa4e98084c4ebf4e64a98084c4edf4e54a98084c4eef4e44a98084c4cff4e94a98084c4aff8ea4a98084c4aff4ea4a98084c4cbf4e64a98084c4cdf4e54a98084c4cef4e44a98084c4cff8ea4a98084c48ff8ea4a98084c4cff4ea4a98084c48ff4ea4a98084c4aff50a8094e64a4cff50a8094e64a48ff50a8094e64a4bf786a4094e64a4aff90a4094e64a4cff4099094e64a4aff40a9094e64a4cef48a9094e64a4cff40a9094e64a48ff40a9094e64a4cff8095094e64a4a7f8ea5094e64a4abf8ca5094e64a4afd82a5094e64a4aff80a5094e64a4f4f4e54c94e44a4f6f8ea4c94e44a4b6f8ea4c94e44a4fcf8aa4c94e44a4bcf8aa4c94e44a4bef80a4c94e44a4eef90a4c94e44a4aef90a4c94e44a4d4f4e58094e44a4f4f4e54094e44a4def4c94094e44a4bef8ca4094e44a4fcf8aa4094e44a4bcf8aa4094e44a4aff40a8c94e84a4cff40a8c94e84a48ff40a8c94e84a4e7f8ea4c94e84a4a7f8ea4c94e84a4ebf8ca4c94e84a4eef88a4c94e84a4aef88a4c94e84a4efd82a4c94e84a4afd82a4c94e84a4aff80a4c94e84a4cff8c98094e84a4cff4c98094e84a4aff4ca8094e84a4cff8ca8094e84a4cff4ca8094e84a48ff4ca8094e84a4cff8c94094e84a4cff4c94094e84a4e7f8ea4094e84a4a7f8ea4094e84a4aff8ca4094e84a4eef88a4094e84a4aef88a4094e84a4efe80a4094e84a4ebf80a4e64c84a4abf80a4e64c84a4e4f4e54e44c84a4eef40a4e44c84a4eefd2a4e44c84a4e3f4e68e94c84a4e6f4e48e94c84a4aef88a8e94c84a4cff80a8e94c84a48ff40a8e94c84a4abf8ca4e94c84a4aef88a4e94c84a4afd82a4e94c84a4aff80a4e94c84a4c7f8ea4e94c84a4cbf8ca4e94c84a4cef88a4e94c84a4cfd82a4e94c84a48fd82a4e94c84a4cff80a4e94c84a48ff80a4e94c84a4eaf4e
  | 6 => 0xaa8894c84e49ef40a8894c84e4d7f8e98094c84e4def8898094c84e4d7f4e58094c84e4d7f8ea8094c84e49ff4aa8094c84e4def88a8094c84e4cff80a4c98a84e48ff80a4c98a84e4cff8ca4098a84e48ff8ca4098a84e4cff4ca4098a84e4e7f8ea4c84a84e4edf8aa4c84a84e4eef88a4c84a84e4aff80a4c84a84e4ebf4c88c94a84e4cbf4c88c94a84e49ff40a8c94a84e4dbf8c94c94a84e4b7f8ea4c94a84e4bdf8aa4c94a84e4bef88a4c94a84e4bfd82a4c94a84e4aff90a4c94a84e4cff4c88094a84e49ff4ca8094a84e4b7f8ea4094a84e4bdf8aa4094a84e4bef88a4094a84e4e7f4ca4e58084e4cff8aa4c98084e48ff8aa4c98084e4cff8ca4a98084e48ff8ca4a98084e4cff4ca4a98084e4e7f4e54c84084e4e7f8ea4c84084e4aff8aa4c84084e4eef88a4c84084e4efe80a4c84084e4aff8ca4a84084e4efe80a4a84084e4ebf4c88c94084e4d7f4e58c94084e4cbf4c88c94084e4cff4a88c94084e49ff4aa8c94084e4dbf8c94c94084e4b7f8ea4c94084e4bef88a4c94084e4bf786a4c94084e4bfe80a4c94084e4f5f4e58a94084e4edf4a88a94084e4d5f4e58a94084e4cff4c88a94084e49ff4ca8a94084e4b7f8ea4a94084e4bef88a4a94084e4bfe80a4a94084e4bbf40a8a94e64c4dbf40a8a94e64c49bf40a8a94e64c4bbf4aa8094e64c4dbf4aa8094e64c49bf4aa8094e64c4b3f8ea4c94e54c4b9f8aa4c94e54c4bbf80a4c94e54c49bf4ca8094e54c49ffd0a8094e54c48ffd0a8094e54c48ff50a8094e54c4dbf4c94094e54c4bbf4ca4094e54c4bef88a4094e54c4aff90a4094e54c4aff10a4094e54c4b7f4ead094e54c49ff40ad094e54c4cff409d094e54c4e7f4ead094e54c4a7f4ead094e54c4aff40ad094e54c48ff40a9094e54c4cff4095094e54c4a7f8ea5094e54c4adf8aa5094e54c4afd82a5094e54c4aff80a5094e54c49ff40a1094e54c48ffd0a1094e54c4c9f4c51094e54c48ff40a1094e54c4f2f4ca4e54e44c4b6f80a4e54e44c4f6f40a4e54e44c4f6fd0a4e54e44c4b6fd0a4e54e44c4b6f10a4e54e44c4a6f10a4e54e44c4f0f4e54c54e44c4faf8ca4a94e44c4baf8ca4a94e44c4bef80a4a94e44c4f6f4e54094e44c4faf4c54094e44c4def4a94094e44c4faf8ca4094e44c4baf8ca4094e44c4bef8aa4094e44c4f6f4aa4e48e84c4f6f40a4e48e84c48ff80a4a98e84c48ff8aa4098e84c49ff40a8a94e84c49ff4aa8094e84c4aff40a8a94e84c4cff80a8a94e84c4cff40a8a94e84c48ff40a8a94e84c4c6f8e98894e84c4cff8a98094e84c4aff4aa8094e84c4cbf4c58094e84c4cff8aa8094e84c4cff4aa8094e84c48ff4aa8094e84c4bbf80a4e68a84c4aff80a4e88a84c49ff80a4e98a84c4dbf4e64098a84c4def4e44098a84c4cff4e84098a84c49ff8ea4098a8
  | 7 => 0x33d6b927dcfb9d4500024717f72847dcfb95a85f066209d54f10d29e1f0fee7dcfb8173a87dcce07d02b8bc15ee2a26306fb9f729903a4187a1f0b7bf49a4fee3d1c63543ee70deb879b5c39a00d9b82151a61724bee06e2cc957ee7dc5d8b988fdf22f0f7fee7dcfb9f70d9ab4e9ef0a677dc541e403d913fb9f73ee7dce66b042c19cfb9f725d77de9ce0a51fdc46df73ee1cda0ef2fee7dc98101ce0cbeed65fbee7a3849f73ee7dce6cd7bee53a697f73ee04ebeeb141e7dc8ddb09e7e2039419041c50012041c10024c008b1c40410010000cb1c14862430c40020820820911405c60000050010000420010000022401040422422020014c06c01011000c01000c500200200108100408102120001000130004004400900100000608f0400c000008108018124608b08000000604054b0810000020402c400004010a04408110d1401040c42400023803000041001800400020000c12413410020451820082c008724200100600d10f00024200218c28d04180a1810480450421021c008b04020000038900000218118111050014700400438024200504020600328004004410900518008114d0400000400812492821000402431000c25c30002c30040007421870460020020831000cb2820802433800001800c119000228109c0810020811021405400000001810035030420020230050820000440080401422480c41c000304c0000ca2473c014900a9840090000140834001610c20000411206020800010000440400051c200500314014004010c0800010c300408001900814108004068224408108000010000200108a1830c10021c12c00c20031010841400c26031cf0091882d20810420410cb2c14040800011010002051c03000420405070442c01455000c09ff80a4a98884e69ff8aa4098884e6aff80a4a98884e6cff80a4a98884e68ff80a4a98884e6cff40a4a98884e6cff4a94098884e6aff8aa4098884e6cff8aa4098884e68ff8aa4098884e6cff4aa4098884e6aff40a8a84884e69ff40a8a94884e6cff8a88094884e69ff4aa8094884e6aff8aa4888084e6cff4a84898084e69ff8aa4898084e6cff4a94898084e6aff8aa4898084e6cff8aa4898084e68ff8aa4898084e6cff4aa4898084e6aff4aa8884084e6cff8a88894084e69ff4aa8894084e6cf78888694084e6cff80a4a98c84e48ff80a4a98c84e4cff40a4a98c84e4cff8aa4098c84e48ff8aa4098c84e4cff4aa4098c84e4d7fd2a4e54c84e497f4aa8e94c84e497f40a8e94c84e4f5f4e58a94c84e4d7f8e98a94c84e4b7f8ea8a94c84e4d5f4e58a94c84e4d7f8ea8a94c84e497f8ea8a94c84e4def88a8a94c84e49ff40a8a94c84e4f6f4e58894c84e4d6f8e98894c84e4def8a98894c84e4bef4aa8894c84e4bef40a8894c84e4d6f4e58894c84e49ef4
  | 8 => 0xe6e4f43ee616969f7335577fb9c276c7dcfb835e99df1918b6fa9fdcfb9f73ee503fb9f72567dc4354289fb87fb9a7bee0ddfb852ded64877fa019aaebb31f7014957fb866dcd876fb9f7344358fb9f71e9fdcfb960bee7dc388b4bee7ca1db8ec3ce8a7c9f73ee5c6fb88bfee7dc89df72e77dcbb5f73097dc765f73ee4a1187f73ee425a9a337ee773cc1a1bee7dc6ff152f4515d9a3d2c363a834d363dfdc49dcc872f91fb9f73cf116d3ff73ee7dcfb9f71a37dcfb86eee5711a57d0bee43efb9f73ee78afb9f73d468eeec9f72f7dcfb9f73ee7dcfa9f73ee25afb9f73ee622381ae44dad934aaa3544f1fb9f7008fdc6ce853e5fdc4b7f72ff7dcfb9eb1b1068fb890398395fb8dcfee4f3d61f73ee7dcfb9f73ee697fb893fee7dcfb84d2eefdc2d0c5fee432761007ee12cc73f70407dcd92d97ee07cfb9f7126fdcfb8a2fee710fb8f122055cfb9f71b34c2fb89fa817dceeecbd9376cfb9f73ee7dc467f70beb5cfb89e787fdcfb8ff7ee7dcce3b7389e1d743adbee3f2bf1e75f466bfb93a3ee162f39082f70d0150f06ab6728c7ca8ce9f8b82d903157e4739367e480c615c55c86038efacd6be22f2fd9bbb717862204165af07c10cb7dc2138d211fdcfb8bd04cfdc7013d4c0bbefb9f734c7dcfb9f71177dc5d5f73ee7dc0a9f73ee2d8f4e6c38c4f43fff71a7fdcfb9f73ee7dcfb9a9ce45495882b7ee3f978091878e8f56734647fdcfb9f73dca08cbfc54487dc05de48d3f8d70ab6a46fdcfb8c0e4e6e691d1aa90111fb9f73ee7dcfb999d41fdc779f73ee08ac7ed2944fdcbacbfbee7dc425f703f7dcee9f711f7dcfb9f73ee7dcfb8537ee7dcfb99fe988aeef06bd808bd471cba418fbd4dd2fee044080c8bee4f9eda1abee7dcfb889bee7dcfb928bee4e5e91f72e2a19fb8c77ee7dc455f73287dc11df73ee57487ff73ee734fb88ca3edded5df70b57dcf83460810fcfb95f3ee7dcfb829fee28d9f18f0a0a6885fb8f70086a5e5318b10342b343ee7dc99f16e117dc487f737fba5fb8f7ae67dcdb34bbee44bfb9f71407dcc1f16a42ac2438a5b627dc293f701a645bf550f65955fb98523d772fb835498e27fb9f70a3fdc9287689b67cd349990c427f9bec721a5e97af8265a7a21021109d521f26cb82a5782073933f621c2ee3d5b7e398962c7244393589720c1a0ae5e177dc2a6a07ee7dcb0abba0afdc17ff71c9808fb9e10ea7dc15483ad2d963e1ca7ee7dcfb8fa4367dcfb8ab1926158f8b23ee7dcfb897111fdcfb9f73ee7dcfb8a8bee48afb9f73ee6d0f0b02fac9a2cd232d30c6bb713070288c38b4a94d0a103cf1d47e4244ae4469efafb8b24887dcfb9763ee7dca59f0bee1878938da08fdc3527b1957dc721f707f7dc6f53f5a67dcfb9f72924b81612e5d6eec890bc7ee7dcfb9f7342da2fb9f7149abd2
  | 9 => 0x2ff0b5f73ee2bcfb9f73ee176320502cf204fb8a85b77dcfb800ab94d6f9325aa376674c933ee1fddfc7eab82299b7a513c7dcc13f73ddef17dace3be68bf126f1800917e2a7fee7dcfb98f7ee11bfb8d41872cef8fd51d216cfb9f73ee018fb9f73ee7dcfb8482874579556f8133d7fb81c81c761fb93b6e6a1633dd757dd58fb9aefe2fdcfb9d3640fdcfb858dbefdcfb9f723484afb8e5a00369325f73ee7dcfb9783ee6e7fb9f73a67dcfb8d13a27dc9404cfee7dc1c7f73ee7dcfb9acfee121a09f612ce35039f73ee15dfb825b77135d7c62bee442fb9f72188c95c5f73ee7dc291f73ee4cdfb9f7337fcc43ff73757dcfb849fee00e8adf73ee6d72757e58df1e448f70160cf9e58a8f754ebed3f90d92bcb87473d203e4cdd065154870b0c7aaf22ca37b5069d238a77ee7dcfb8616aa9efa2c389f327326fe1dd17dcfb9f703a603fb97ab25e2f52867e866b1d5beb929b60126f3790926e5b03555997009869825dcfb86c7ee68cfb9f70b0fdc563f73ee625fb9f73ee7dcfb8f554232e4ed39d70525604f5a4c1bff0d9cc517dc9c75a7ee0ab8689c07b3fafb9f732c50b2245bb127dcfb9f7210fdc171f71b7fc0a2705bee248ef5f733cb94fb90f3ee7dc4c1f7110fdcfb9f72dcc0cfb9f73ee7c8df1f73a0c6146b066599c24bba1fc111afb98b459fdcfb9183ee7dcfb9a95ddf407a5f73ee7dcc8f35fee5ef5302e53bef2f31ae8797dcfb91d70bb756bad097d05efb87acd2100f41f72d47dce16fff061b7fb939bee7dcc09eabee230fa1ed19a46d369e55d4573fb9c1cc27dc9c5f73ee7dc0506828860d82ff703c0c4651cfe15db69b254b6dbce4d871920ea4bcca654812552b84fee7dcfb9b3bee73e8bedf0c77dc375f73ee5bffb9f73ee6c590dde7ee7dccf7f7142fdcd68a7adacdafb9f7063530ee1f73ee6f3fb95b091928fb9f73ee022fb9f7099466fb4140f0bca8732c4fb8ee4a227f9ef807d5f70d5859df7f73ee7dcfb9f713e210fb80589e9868a38ced9f3a020cb317651730123eb7dcd5ff70d44b5fb9143903f08f2fe3d9da45520337c9aa987f7104fdcc56e07ee097fb8aebee321fb9f708aae12e04e34e46c1c82991e6669b04bfee2a6dd04e60dc82fb9f73d0fdc386a19f753ec89b32297dccf1f7156d42bc995348fdcfb9f70107dcfb88a3ee7dc08e3a03abc8c03062b3727b20814a89a6147ba7affdcfb9987ee44ff1e6d58d4e9abf1e25323dfb9eb7ee7dc5610d548c5efb8eebee2a70011cbee14ffb9f73ee1fbfb9f732afdcfb8538eeb15f10aab641bd1d631e0ff96fb9f73567c6fb9f73db26ffb9f73ee7dcfb850dad5fbb24e0fee368f35f7218098c99f4a63d38f53d63eb8c5fb8028d67dcfb841495540029f737bfdc2a1b06a47dc64187ec44fa3e31c1f7f1c87bb009df45249f73bf4a
  | 10 => 0x807dcfb8a8fee7dc25a9160ecabfb84a73aed5fb9f7079fdc69d47e3b20bfab7b3ee4045363b3b5254ab5a8d5c7dca95a43959a3fb81bc478438c9f708a42866df73af7dcccb603ee7dc033f71354bf39ff72da66cfb9d4bee070176345897dcfb909bee5b7a44b43c67dc5ebf73ee7dcfb876f72fdc184579c6fdcfb924616b5b245f709e646fb9f725963efb9efb635f5978e335170613ddbbe9f7588efd7ee7dcd8f7f46623afb9f7258271217af76fd361b31569e1aea99f73d17dcfb9f732cfdcfb9f7110652fb9f73a4f9706ff7052baafb9f71a94fffb9513ee7dc1adf738674afb9f7367fbafb9f73ee7168c52db037dcfb9f73557dce77f72ddbf43b3f71b55e2fb9d6cf6d68fb9a6eea618fb9f73ee7dc0a5cf3ee5ed1bf6a900fdc73ff73ee172709ad50f4889483bcdcd14876a4b6a728311928ba89d163aacfe1df56d4a0c6ab5dba5afee092fb8b7dcefdcf03adcf1fdc3d3a6487fdcfb9375fbe63fb99d9f9f94fb9552699a1921d5fb26497927d4ebe92219bf3137dcee3f73ee6404a53ecb3fdcfb85b7ee7dcfb90ebee7dcfb9f7284acdfb9f73bfd27fb82a74b7dcfb9f733a7dc8243a7ee3dbe625a657f3863910dd02227ca5cd393d9175c64a513ec05f71572ccfb9e9bee22b86c9098a664fb932a772025abf73ee62920c8efee7dcfb98233415616be7c507dce1472e77fdc40fb4c6dac686ecebee0b7fb9f731c7dc7c7c04ac4a8fb9f73ee7dc681f72bc6e15b9f72fffdcfb9f7215370331f73ee7affb9f73ee1fefb833a8e1be2f7ef16f689e47f73ee7378b9f73ee501ed1f71bb6e2169313ee31fe87f3bee26498adb7657dcb47a5664ab22e2510b07dc2f4c4e8331e96f025994ecfb9f7132fdc7b0657ee7dc73dd82c18dab18edabcf563292b54158a2efd1ce85641b1bd2dd20ac36e9c85413300b1d373083ac1e908b5975dd1bee60ba5b5dbee2cb4638dce960a7a90714453d4964c04d799307380ba6d1f70a28707b22dfd8d34e10af5f72cd25ffb9905de9f3fb9f73ee5cbe4a9fd6523fbe131a0f7dc5a83eac26814c4438f2b61abde2f3128ee6bf73ee7d92ff332fa7dcfb9f73ee7dc78b104eabb4f1d485c7fdc4c7f73ee0fdfb96bbee653691f73ee2d6fb9f72236f5e3ee3b46d26f9ff73ee6a1977387ee7dcfb99f5602bbfb9f73ee7dcfb9f71fe7dcfb8835b1b193edf706e7dcc33f7243ae8fb9c0c4afdc468323727dc43a5099f70eb61f70ae250dbc29123f1b619f73ee3ac4da06bee237db5f72342fcfb9f70f526b3bcc27ee6b223bbafee632cadc5060712fb89d1c97dc747f73806f0da5bbf8d5a62c82b124856a1e0ca4f3ec1e06d8f07dcfb835214f2278d5bae977b16df71b5b9cfb9c5d8c7dcfb993fee7dce11ec316310fb9d959183efb8b8fee7dcfb9f73816bcb7bf73ee47efb91d204
  | 11 => 0x19758382a935f701860efb91de0a0f8d0445f7b389334a3361fdcfb916289206c479dd4bfdc81ebc2a9fdc06df71c47dc1fff73b4c843f3f73ee1b8fb9f73ee7dcbe656ae27a512889fee7d11ceafb5fbddfb98460161c9bd6f1f3b5ff7e11bee7dce5fb5ae17dcd07f726a7dce73f73ee5b2fb902bee7dc57f743ee256fb9723ee7dcfb9f73965a0fb851bee793548cc3e222d56ff70097dc098fef2da87fb9f705912e8cb3561998c9be8b3ee7dcfb9e6f76c0e4ea2729a7673b0bd883fb570c407ee7dcfb93ac0dfdcfb857ece7dc53839bee6283ce463ee7dc6d9f726e20f21bf72d635654acf3b7fdcfb8be0be7dbfb9f73ee2af3a734bee7dcb8ede3ee6073c8f333f51e8dee667be21614567ee4e4bf987bee600a5260bee7dcfb9f70a2b54cdb113ee4f6fb9f71257dc4f63dfee2d1859f737efdc9d5653ee15bcaf725ff68423d582257dc3b87cae07dc80df73ee7bd9903abee7dcfb9f73ee7dcfb970d0bfdcfb9c77ee37900793a
  | _ => 0
def u168K10 : Nat → Nat
  | 0 => 0x13827fc84a622706ff1094c44e09fe2129889c1dbd391291382bfa74a522705ff4c94a44e09ffa129489c1ded393309383fda526612706ff4a48c84e09fe9131909c1dfd391321383dfa622642707ff4a44c84e0fff1129909c17fe225321383fbc34a642705f78694c84e0ffd0129909c17fa0253213833fa72c442706ff4c58884e0df79851109c13fd3262213827fa54c4427077f4e54884e0ffe98a9109c1fbd291221383fde612442706ff4c84884e0dfe9509109c1ffe325221382ffc64a442707ff4c94884e0bfe9929109c1ffe2a5221382ffc54a442707ff4a94884e0bfe9529109c1efe225399302dfc44a732607be8094e64c0efe9ca9c8981efd325391302ffc54a722607ff4a94e44c0dffa129c89813ff4253913027fc84a722606ff5094e44c09fe2129c8981efd395311303d7a722622605bf8e94c44c0b7e9d2988981efe2a5311302dfc54a622607be8094c44c0f7e9cc948981fbd391291302ffa74a522605bf4c94a44c09ffa129489817fd425291303bf2722702607be4c44e04c0ffc9489c0981ff92253813035fa624742606ff4a48e84c09fe9131d0981ffd2913a1302ffc44a742605f78694e84c0bfd0129d0981afd3113a13037fa522742606ff8894e84c09ff1129d0981bde1a53a13027bc34a742606fe8094e84c0d7e9cd110981bfd3962213035fa62c442606fe4e08884c09fe9d31109813fd2a6221302ffc54a442605fe8094884c0fff1529cc9017fe2a5399203ffa54a732406ff9094e64809ff2129cc901bfd425399202ffc64a72a407ff4c94e5480fde9129ca901ff90253952027fc84a72a406ff5094e5480f7e9cc98a901f7d395315203ffc74a62a405ff8e94c5480ffe9d298a9017fd3a53152037fc84a62a404ff9094c5480dfea1298a901dbd395391203f7a62a722407ef4c94e4480bdf1529c8901fbd2a5391203f7a732522407cf4e54a4480bde9d2948901fad291389203fda72e612407eb4e4cc2480fd69499849017ed3a7309203bf272a702407fe4c54e0480edc9c89c0901fb9291381203fd6612702407fe4c94e0480bfd1529c0901ff92a5381203ff2732502407ee4e44a0480f9c948940901fe9389281203fd66125024067f4e54e8480dfe98a9d0901bbd2913a12037de612742406fe4a04e8480dff1929d09013fe3253a12037fa64a742406ff8a94e84809ff1529d0901bfd2a53a12035fa732642406ff4e54c8480d7e98a990901bbd3913212037f2702642406ff8e94c84809ff1d2990901bfd3a53212027fa74a642406ff8a94c84809ff152990901bfd2a53212037f404a642406ff4e64a8480dde9c8950901bed3892a12037de612542406fe4e04a8480dff1d29509013fe3a52a12037fa74a542404ff4e94a8480dff1929509013fe3252a12037fa64a542404ff4c94a8480
  | 1 => 0x201880d080123904010c01010442042260c860940308401080e9a0c620046218400081e2300802a4000040002080004201804008026010001840020881282ffa54c442735ff4098884e6dfe9531109cd3fd2a622139b7fa04c442734ff4098884e6dff1509109cd5fe3a522139affc54a442735ff8094884e6dfe9110109cd7fd22602139b7fa44c042734ff4898084e6dff1108109cd7fe22502139afbc34a042734ff4a98c84e49fe8131909c9dfd395321393bfc74a6427257f8e94c84e4fff1529909c97fe2a5321393f7c44a642725ef8894c84e4fff0129909c97fe0253213927fa64c542724ff4098a84e4dfe9909509c9ffe3252a1392ffc64a542727ff4c94a84e4fff0129509c97fe0252a1393ffa04a5427267f4e58084e49fe9930109c93fd2a6021393bfa72a042726ff4c84084e4dfe9508109c9ffe325021392ffc64a042727ff4c94084e4fff1528109c97fe2a5021393ffa54a042727bf8a94e64c4b7f1529cc989ebe225399313dfc04a732625bf8094e64c4f7e9929ca9897fe025395313ffa04a72a627ffd094e54c4bffa129ca989bff4253953127fc84a72a626ff5094e54c4bfe2129ca9893fc425395313b7a72a722627af4c54e44c4fde9529c8989fbd0253913139fa7347426276f4e48e84c4d7e98b1d09893fd2a63a13127fa04c742625ff8a94e84c4bdf1129d09897fe0253a13135fa62a7426267f8e94e84c4dff1529d09893fe2a53a131377c44a742626ff8094e84c49ff0129d0989efd39a2a1313cfa62c542627ef4e48a84c4dfe9d11509897fd3a62a1312ffa04c542626bf4e68a84c4dde9c91509893fe3a62a13137fa74c542624ff4e98a84c4dfe8131509893fd0262a1312f7c44a542625ff8094a84c4f7e9cd010989ffd396021313dfa62c042627ef4e48084c4dfe9d1010989bfd2a2021312ffa74c042625ff4a98084c4d7e9cd010989bfd3960213135fa62c042626ef4e48084c4dfe9d30109893fd3a60213137fa54c042624ff4a98084c4dff1508109897fe2a5021313ffc04a732525ff8094e64a4ffe8129cc949bfe4253992927fc84a732526ff5094e64a4e9e9ca9c8949fbd325391292f7c04a722527ef4094e44a4dff1929d09493fe3253a12937fa64a742526ff8094e84a49ff0129d0949bfd0253a12935fa732642526ef4e44c84a4dff1d29909493fe3a53212937fa74a642524ff4e94c84a4ddf112990949bfe0253212927fc04a642526ff4094c84a4ef69ca9c99857ee2a539330bfda54a726615fb8094e4cc2ff68129c9985fad39129330afda74a526616fb4a44e8cc2df69129d1985bed0253a330bbfa64a7227057f8a94e44e0efe9529c89c1dfd395311383dfa62a6227076f4e44c44e0fff1529889c17fe2a53113827fe84a622707ff9094c44e0bff2129889c1bfe42531
  | 2 => 0xad48a9275335495254952549524be355483a40552483523a31f956fd549524a23212152548f433931b544ad48d34d91382d40ad5358ee3e8243c1754130c3fb302cd48c2d4867ba7520ea8cd48a3548c1d495254899a0d04a06b1d495210640548bc54952549520ab524fe80d49525495203d159e15229a11aa9523584ebf64331f4aa9c165491cc76dd371525495244352549524fd5213e50beb025255254952548382dd52549521dea846f523bf52513474e5521255251b5218352549525495254952549525482c5487f887524b462190c80a93235cd82e45c548f0549525495254843d495254952548c75495254895085525483604cf3d48ccd480b9112bc5f3bd49525485554952548062cf52549525495254952533525486c5426927152549525495254952549525495254952549521663d302605344dc18aad493ac453a2b256549525495254952549523901226152549525487d96a0a54952548ef5495222efc9f8843295254952009525495254952549525495246b522b4ab0f914d480ed49525495212d522bb5240724d495254822d49524de993e2cf2fd525495250e9fd49525495246152462b60755254891d495254952548a154905b7c9b54952549524db525492c54952549523e942bd4b697e91549520b75238d525483f549524015254952257525481fd48f854952549525495254846549525495208ed5d495254952549522ed52549525484a1fd52549525484d5493e3789f548b8d481cd4952549522171187cb7a1b5254875d4818548bbd495205d0f815525495254952548672e94f549085492e5495217d2dd4942549522bd32d48edd3724548290b444ad3524233dc6810892e22c265d4945088929854a18b5249eeeb6cf0d4952549521d534d49525495218d524dd5223013bee2ed495215d5238552439525487cb83274364e044f21b5524f35215352549521b352548c2549433689e9a6d91ad525486844b523aa1aca082d49520055223adec988131028268e2cb35209552549521bc93d48651e459068f987b06c0c5a2fe15b95520aee63b10d451525495234552548735488ad4830998d4238ecd4952259525480d0794ecf151d4952038425495242c514d4772b0ae3ace03d3525495227819d495206f1f54952548855492039f5225a86549525495228847d49521f094a8752548925495254952548a05487bd492accf525495254952549523181289d5254831d495254952548a4548a3d495254952549525495222cf7549522c552517523db3b549213f92b548b28a35254857d49521054bd49524c1525495222352549525492a352f60ad5254952549525492508040148009c010906000002190050202048842100230004230801000000824048c02100002850408420004c0200420000102400081a2080000804410400000
  | 3 => 0x8d525492ed4939a08d0549525483c8bc88010abd49520d752549520b9525488dd481c3491b549525495254952548b20ed38d48f7c7a265488d0e752549521f437d4952226b00bebd548241175254947c9b52449523a552549522b67b549521c51954952549524786dd49525487654952548f1549523af525480854916d49520d1525495248f38548455495254952549523cd523e55254952549525489754878d49525495254919d494fc555254952548005492f54952548348e3522f833c8cf59facd54848d4815549524c4b810329b015225f525490c35b52549091c94c1495214cee548931e8ed549505484bd49525495230529549525495254952548a2c70874d1042291d54819201039eb52549525481b3a074d490ea995254817d495254846d48fed4952548e5d495248694295525485440a18d4949d48103a842abf5217952549521b9520374b4335239ac5549521c0c924251c1f52549525495254952549524c3259635214f524290994b523f1520c1525495213090549525488f161520e4372fa1dc1d5201d5254952549525495248b009275254952548729e66ac5c0fbed5216e2042f444f4ff521463c64f0cb40140471db3ebfef28c5221a8145225b053521d152548e7549525495254816d483dd495254836d4952392b315a0c5495200d523875232d52548dfd49522e71043d4e5495254489549525495244c4c8cd522635254820d4952549525495254952549525495238f52459052d10
  | _ => 0
def u168K11 : Nat → Nat
  | 0 => 0x5064b4bad47104d904245cfa4e9ed2ff0504c4dcfce4484d0504b90408bd04825b0504e1050426790504c10504f828450505046876ce9304e881046c2303050500582b0474d1050494a67c2c145504d6cc2f0485041817045e1b048810f0a4b6910421050505043c381e9d05050504a105050504af05041c1304c904ac30049aaadec2b240988cf4005272a8603236beca06e6e20cec34dab104a20b04408082286c0000020ae4010001004200082012483107ff8884e6bfe22139bff4884e6ffe02139aff8084e6ffd02139b7f4e54e4bfe321393ff4c84e4bfe2a1393ff4a84e4bfe021393ff4084e4efd399313ff4e54c4efd315313ef4e44c4ffe3a1312ff8e84c4ffd3a1312ff4e84c4ffe2a1312ff8a84c4ffd2a1313ff8084c4bfe021313ff4084c4ffd399293ef4e44a4bfd3a1292ff4c84a4fed29138bfb4e4cc2fed29330afb4e8cc2dfd391383ff4c44e0ffd291383fbcc24e0bfe321383ff4c84e0bfe221383ff4884e0efd399303ff4e44c0efd311303ff4a44c0ff9381302ff8e84c0ffd3a1302ff4e84c0bfe221303ff4884c0ffd399203ff4e5480ffd315203ef4e4480fbd291203fb4e2480fef309203fe4e0480ff9281202ff4e8480bfd321202ff4a8480
  | _ => 0
def u168K12 : Nat → Nat
  | 0 => 0x49ca94a520c24d3304f412407ff4e6ffa727fd313fe949fb4e2fde617fd383fe981ff480
  | _ => 0
def u168K13 : Nat → Nat
  | 0 => 0x50ff
  | _ => 0
def u168N : Nat → Nat
  | 6 => 15
  | 7 => 244
  | 8 => 985
  | 9 => 1006
  | 10 => 338
  | 11 => 65
  | 12 => 9
  | 13 => 1
  | _ => 0
def u168R : Nat → Nat → Nat
  | 6, i => packedAt u168K6 (i * 99) 99
  | 7, i => packedAt u168K7 (i * 86) 86
  | 8, i => packedAt u168K8 (i * 73) 73
  | 9, i => packedAt u168K9 (i * 60) 60
  | 10, i => packedAt u168K10 (i * 47) 47
  | 11, i => packedAt u168K11 (i * 34) 34
  | 12, i => packedAt u168K12 (i * 21) 21
  | 13, i => packedAt u168K13 (i * 8) 8
  | _, _ => 0
def u168I : Nat → Nat → Nat
  | 6, h => packedAt u168K6 (1512 + ((h / 9 + packedAt u168K6 (1485 + (h % 9) * 3) 3) % 50) * 5) 5
  | 7, h => packedAt u168K7 (21860 + ((h / 146 + packedAt u168K7 (20984 + (h % 146) * 6) 6) % 549) * 9) 9
  | 8, h => packedAt u168K8 (74875 + ((h / 594 + packedAt u168K8 (71905 + (h % 594) * 5) 5) % 3033) * 11) 11
  | 9, h => packedAt u168K9 (63978 + ((h / 603 + packedAt u168K9 (60360 + (h % 603) * 6) 6) % 2641) * 11) 11
  | 10, h => packedAt u168K10 (16891 + ((h / 201 + packedAt u168K10 (15886 + (h % 201) * 5) 5) % 1202) * 10) 10
  | 11, h => packedAt u168K11 (2385 + ((h / 35 + packedAt u168K11 (2210 + (h % 35) * 5) 5) % 157) * 8) 8
  | 12, h => packedAt u168K12 (197 + ((h / 4 + packedAt u168K12 (189 + (h % 4) * 2) 2) % 19) * 5) 5
  | 13, h => packedAt u168K13 (9 + ((h / 1 + packedAt u168K13 (8 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u168Pos : Nat → Bits
  | 0 => 0xe4703ffff1000009cc030312cc0026732673ff
  | 1 => 0x1b9fc00c0000024e700404a30f00db9cdb9ccc
  | 2 => 0x3e000f0022cb38f809898c3f0cce3e0e3e0f0
  | 3 => 0x1c0000fff030c3f000e0e0fc00f0fc00fc00ff
  | 4 => 0x1fffff000400fc000300ff0000ff0000ffff00
  | 5 => 0xe0000000083f000003ff000000ffffff000000
  | 6 => 0xfc0000003ffffffff000000000000
  | 7 => 0xffffffffc00000000000000000000
  | _ => 0
def u168Neg : Nat → Bits
  | 0 => 0x60b0531631000008c4010112cc000231023155
  | 1 => 0x29b1c13c5000024a500000a305004a944a94cc
  | 2 => 0xdff286fc222cb38f808888c350cce3e0e3e0f0
  | 3 => 0x1f4508e9c030c2d000a0a0e400f0fc00fc00aa
  | 4 => 0x164e2c408400d4000100fe0000550000b54a00
  | 5 => 0x800000810835000002fe000000aab54a000000
  | 6 => 0x830020d40000003575718aa000000000000
  | 7 => 0x28a29252800000000000000000000
  | _ => 0
def u168Slices : List (Sig × Nat) := [(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,12),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,12),(0x3333333333333333333333333333333333333333333333333333333333333333,12),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,11),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,11),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,11),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,11),(0x5555555555555555555555555555555555555555555555555555555555555555,11),(0x0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,10),(0x0000000055555555000000005555555500000000555555550000000055555555,9),(0x000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,9),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,9),(0x0000555500005555000055550000555500005555000055550000555500005555,9),(0x5050505050505050505050505050505050505050505050505050505050505050,9),(0x00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,8),(0x0000000000000000555555555555555500000000000000005555555555555555,8),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,8),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,8),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8),(0x0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,8),(0x0000000000000000000000000000000055555555555555555555555555555555,8),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,8),(0x00ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,7),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,7),(0x00000000000000000000000000000000ffffffffffffffff0000000000000000,7),(0x0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,7),(0x000000000000000000000000000000000000000000000000ffffffffffffffff,7),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,7),(0x3333333333333333000000000000000033333333333333330000000000000000,7)]
def u168Atlas : Atlas := ⟨13, rawDecor 255 u168Pos u168Neg, u168T, u168Slices, [swapRows 84], u168N, u168R, u168I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_6_0 : Interval u168Atlas 6 0 15 := block_range (n := 15) (by decide +kernel)
theorem all_u168_6 : Interval u168Atlas 6 0 15 := blk_u168_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_7_0 : Interval u168Atlas 7 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_7_64 : Interval u168Atlas 7 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_7_128 : Interval u168Atlas 7 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_7_192 : Interval u168Atlas 7 192 52 := block_range (n := 52) (by decide +kernel)
theorem all_u168_7 : Interval u168Atlas 7 0 244 := (concat (concat blk_u168_7_0 blk_u168_7_64) (concat blk_u168_7_128 blk_u168_7_192))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_0 : Interval u168Atlas 8 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_64 : Interval u168Atlas 8 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_128 : Interval u168Atlas 8 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_192 : Interval u168Atlas 8 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_256 : Interval u168Atlas 8 256 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_320 : Interval u168Atlas 8 320 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_384 : Interval u168Atlas 8 384 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_448 : Interval u168Atlas 8 448 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_512 : Interval u168Atlas 8 512 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_576 : Interval u168Atlas 8 576 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_640 : Interval u168Atlas 8 640 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_704 : Interval u168Atlas 8 704 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_768 : Interval u168Atlas 8 768 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_832 : Interval u168Atlas 8 832 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_896 : Interval u168Atlas 8 896 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_8_960 : Interval u168Atlas 8 960 25 := block_range (n := 25) (by decide +kernel)
theorem all_u168_8 : Interval u168Atlas 8 0 985 := (concat (concat (concat (concat blk_u168_8_0 blk_u168_8_64) (concat blk_u168_8_128 blk_u168_8_192)) (concat (concat blk_u168_8_256 blk_u168_8_320) (concat blk_u168_8_384 blk_u168_8_448))) (concat (concat (concat blk_u168_8_512 blk_u168_8_576) (concat blk_u168_8_640 blk_u168_8_704)) (concat (concat blk_u168_8_768 blk_u168_8_832) (concat blk_u168_8_896 blk_u168_8_960))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_0 : Interval u168Atlas 9 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_64 : Interval u168Atlas 9 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_128 : Interval u168Atlas 9 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_192 : Interval u168Atlas 9 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_256 : Interval u168Atlas 9 256 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_320 : Interval u168Atlas 9 320 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_384 : Interval u168Atlas 9 384 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_448 : Interval u168Atlas 9 448 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_512 : Interval u168Atlas 9 512 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_576 : Interval u168Atlas 9 576 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_640 : Interval u168Atlas 9 640 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_704 : Interval u168Atlas 9 704 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_768 : Interval u168Atlas 9 768 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_832 : Interval u168Atlas 9 832 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_896 : Interval u168Atlas 9 896 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_9_960 : Interval u168Atlas 9 960 46 := block_range (n := 46) (by decide +kernel)
theorem all_u168_9 : Interval u168Atlas 9 0 1006 := (concat (concat (concat (concat blk_u168_9_0 blk_u168_9_64) (concat blk_u168_9_128 blk_u168_9_192)) (concat (concat blk_u168_9_256 blk_u168_9_320) (concat blk_u168_9_384 blk_u168_9_448))) (concat (concat (concat blk_u168_9_512 blk_u168_9_576) (concat blk_u168_9_640 blk_u168_9_704)) (concat (concat blk_u168_9_768 blk_u168_9_832) (concat blk_u168_9_896 blk_u168_9_960))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_0 : Interval u168Atlas 10 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_64 : Interval u168Atlas 10 64 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_128 : Interval u168Atlas 10 128 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_192 : Interval u168Atlas 10 192 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_256 : Interval u168Atlas 10 256 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_10_320 : Interval u168Atlas 10 320 18 := block_range (n := 18) (by decide +kernel)
theorem all_u168_10 : Interval u168Atlas 10 0 338 := (concat (concat blk_u168_10_0 (concat blk_u168_10_64 blk_u168_10_128)) (concat blk_u168_10_192 (concat blk_u168_10_256 blk_u168_10_320)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_11_0 : Interval u168Atlas 11 0 64 := block_range (n := 64) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_11_64 : Interval u168Atlas 11 64 1 := block_range (n := 1) (by decide +kernel)
theorem all_u168_11 : Interval u168Atlas 11 0 65 := (concat blk_u168_11_0 blk_u168_11_64)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_12_0 : Interval u168Atlas 12 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u168_12 : Interval u168Atlas 12 0 9 := blk_u168_12_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u168_13_0 : Interval u168Atlas 13 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u168_13 : Interval u168Atlas 13 0 1 := blk_u168_13_0
theorem cert_u168 : Complete u168Atlas := by
  intro k hk i hi
  change k ≤ 13 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u168_6 i (by omega) hi
  · exact all_u168_7 i (by omega) hi
  · exact all_u168_8 i (by omega) hi
  · exact all_u168_9 i (by omega) hi
  · exact all_u168_10 i (by omega) hi
  · exact all_u168_11 i (by omega) hi
  · exact all_u168_12 i (by omega) hi
  · exact all_u168_13 i (by omega) hi
theorem b_u168 : Lower true (vars 255) u168T 14 := by
  have ready : Ready u168Atlas (asRow u168Pos) (asRow u168Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u168Atlas, u168Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u163
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u162
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u160
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u167
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u165
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u164
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u161
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u159
    · exact slice_correct (ms := fixRows 64 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u145
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u136
    · exact slice_correct (ms := fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u135
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u141
    · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u131
    · exact slice_correct (ms := fixRows 1 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u122
    · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u138
    · exact slice_correct (ms := fixRows 69 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u142
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u156
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u155
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u152
    · exact slice_correct (ms := fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u133
    · exact slice_correct (ms := fixRows 129 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u150
    · exact slice_correct (ms := fixRows 0 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u166
    · exact slice_correct (ms := fixRows 8 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u147
    · exact slice_correct (ms := fixRows 84 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u148
    · exact slice_correct (ms := fixRows 128 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u157
    · exact slice_correct (ms := fixRows 4 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u144
    · exact slice_correct (ms := fixRows 196 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u158
    · exact slice_correct (ms := fixRows 100 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u149
    · exact slice_correct (ms := fixRows 2 64) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u143
  exact frozen ready cert_u168 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,64,68),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def fullRoots : List Sig := vars 255
def fullWord : Sig := u168T
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample8 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table8 : ∀ r, posted (sample8 r) = bit r fullWord := by decide +kernel
theorem raw8 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval8 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero = fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample8 r) = fullRoots.map (bit r) := by rw [←raw8, List.map_ofFn]; rfl
  rw [←bRead, exeBits gs r fullRoots (fun g hg => (legal g hg).1), ←e]
  exact (h (sample8 r)).trans (table8 r)
theorem binaryLower (low : Lower true fullRoots fullWord 14)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : 14 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u := true) (execute gs fullRoots) o
  rw [eval8 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_32399.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord = false)] at out
  obtain ⟨k, S, hk, run, sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord = true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, B, hr, hit, hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega
def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[8,4]⟩,⟨.or,[9,5]⟩,⟨.or,[10,3]⟩,⟨.or,[10,7]⟩,⟨.or,[8,4]⟩,⟨.and,[13,12]⟩,⟨.or,[0,7]⟩,⟨.and,[15,11]⟩,⟨.or,[16,14]⟩,⟨.or,[1,2]⟩,⟨.or,[3,7]⟩,⟨.or,[18,19]⟩,⟨.and,[6,20]⟩,⟨.or,[17,21]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 22⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 14) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs, o, ?_, Nat.le_refl _, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))), len⟩
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    exact ⟨mono, 22, monoShape, by change 15 ≤ gs.length; omega, monoEval⟩
end PEqualNP.Outside.L_meta_32399

open PEqualNP.Outside.L_meta_32399 in
theorem PEqualNP.Outside.L_meta_32399 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  solve b_u168
