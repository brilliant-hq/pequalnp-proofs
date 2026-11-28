import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34310_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace ForestCore
def pn (a b : Nat) : Nat := a * 1000000000000000000 + b

open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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
  simp only [b_read]
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

abbrev Row := Fin 512
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

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450)])),(BitVec.ofNat 512 (word80 [0xcccccccc,(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940)])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400)])),(BitVec.ofNat 512 (word80 [0xff00ff00,(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400)])),(BitVec.ofNat 512 (word80 [0xffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,(pn 1208925 819333154198061055),(pn 1208907 372870559760121855),0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819333154197995520),0xffffffffffffffff,0xffff,(pn 1208925 819614624879738880),0xffffffffffff,(pn 1208907 372870555465154560)])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819614629174706175),(pn 1208907 372870555465154560),0xffff,(pn 1208925 819614629174706175),(pn 1208925 819333154197995520),0])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819614629174706175),(pn 1208925 819614629174706175),(pn 1208925 819614629174640640),0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819333154197995519),(pn 1208612 224965371817361402),(pn 1204184 933466900696989695),(pn 1208925 819614624879738879),(pn 1208925 814829554570559487),(pn 1208833 513554078929431040)]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
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
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

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
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
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
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

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
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
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
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
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

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
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

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
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
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
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

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[3,4]⟩,⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[8,10]⟩,⟨.or,[0,7]⟩,⟨.or,[1,2]⟩,⟨.or,[7,13]⟩,⟨.or,[4,7]⟩,⟨.and,[14,5]⟩,⟨.and,[6,11]⟩,⟨.and,[15,9]⟩,⟨.and,[12,8]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 1, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low19 : Lower true (varsX 19) (graphGoal 19) 2 := by
  have q := @lower_count true (vars 19) (graphGoal 19) (proper_of _ (by decide +kernel)) (graphPairs 19 68) (by decide +kernel)
  exact q
def K19 := extendKnown [] 2 [(88,[48,65,32,33,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V19 : Known true K19 := extend_ok (m:=19) baseKnown low19 (by decide +kernel)
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,(pn 1162882 43834387862124095)])),(BitVec.ofNat 152 (word80 [0x492049204920492049,(pn 152464 666195390404042825)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,(pn 1189003 32017409375992775)])),(BitVec.ofNat 152 (word80 [0x924092409240924092,(pn 304929 332390780808085650)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,(pn 1199351 813352631882546680)])),(BitVec.ofNat 152 (word80 [0x248124812481248124,(pn 609858 664781561616171300)]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g73L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g73D3)
  | _ => emptyPacking
def g73I (_ _ : Nat) : Option (Nat × Nat) := none
def g73 : Forest := ⟨73,3,fun i => g73Y[i]?.getD (0,0),g73C,g73A,g73L,g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3_0 : block g73 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g73B3 : block g73 3 0 1=true := g73P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore K19) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound K19 V19) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown K19 4 [(73,[]),(81,[67]),(137,[118]),(145,[67,118]),(146,[16,67,118]),(162,[16,83,67,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) V19 low73 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,(pn 1049545 879886024386469439)])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,(pn 341357 731007050283370569)]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,(pn 1103871 610997741933160896)])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,(pn 1099632 45411241334728923)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,(pn 1086291 865003813055030791)])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,(pn 792005 210639894179260342)]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,(pn 292657 594729400964431352)])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,(pn 99847 650583316231951652)]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[64,49]]
def g27D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K73 V73) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K73 4 [(27,[]),(51,[16,83]),(54,[16,32,67,83]),(86,[96,32,50,83]),(90,[96,32,82]),(101,[32,16,83,100]),(102,[32,99,84,67]),(108,[32,49,81,100]),(114,[64,81,32,99,33]),(116,[32,65,83,97,49]),(165,[80,16,33,50,116,100]),(172,[112,33,16,84,65,100]),(195,[99,116,83,84]),(204,[48,33,16,113,100,81]),(212,[64,33,16,115,97,81,83]),(225,[81,33,99,116]),(228,[80,97,32,115,66,65,67]),(232,[48,81,32,98,116]),(240,[64,81,32,99,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V73 low27 (by decide +kernel)
def g77Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,(pn 1058400 317033753488113727)])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,(pn 609859 314374012705374793)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,(pn 381930 611549317130527168)])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,(pn 393979 520990958612817627)]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,(pn 524256 466573726212611591)])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,(pn 501920 936703110033233042)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,(pn 755514 73654884983980024)])),(BitVec.ofNat 152 (word80 [0x249204100400400,(pn 21587 338844555465197860)]))),(0x0,0x0),(0x0,0x0)]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77A : List (List Nat) := [[],[48]]
def g77D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g77L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g77D4)
  | _ => emptyPacking
def g77I (_ _ : Nat) : Option (Nat × Nat) := none
def g77 : Forest := ⟨77,4,fun i => g77Y[i]?.getD (0,0),g77C,g77A,g77L,g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4_0 : block g77 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g77B4 : block g77 4 0 1=true := g77P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K27 V27) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K27 5 [(77,[]),(83,[33,99,67]),(85,[67]),(139,[33,118]),(154,[16,50,66,118]),(163,[16,32,83,67,118]),(166,[16,115,67,84,101]),(169,[82,66,118]),(170,[16,50,82,66,118]),(177,[82,67,50,118]),(210,[16,98,115,66,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V27 low77 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe701fffc1f9f9ffe,(pn 529495 324433687572316671)])),(BitVec.ofNat 152 (word80 [0x40012490841010040,(pn 5396 862735422549135945)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3e7d0e07ffe01fe3e7,(pn 986393 521920675527069191)])),(BitVec.ofNat 152 (word80 [0x891d2492508a4a0891,(pn 993046 242283794911274130)]))),((BitVec.ofNat 152 (word80 [0x3f8bf038ffffe003f8,(pn 902037 714751666868973624)])),(BitVec.ofNat 152 (word80 [0x104ba492610c0c5104,(pn 879709 521035260490130578)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,(pn 679948 139478437607309248)])),(BitVec.ofNat 152 (word80 [0x200049248210100200,(pn 21587 888002785186171172)]))),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(8,0,81,0,4)]
def g89A : List (List Nat) := [[],[67],[96],[96,67]]
def g89D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g89L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g89D4)
  | _ => emptyPacking
def g89I (_ _ : Nat) : Option (Nat × Nat) := none
def g89 : Forest := ⟨89,4,fun i => g89Y[i]?.getD (0,0),g89C,g89A,g89L,g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4_0 : block g89 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B4 : block g89 4 0 1=true := g89P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact (rfl : block g89 3 0 0 = true)
  · exact g89B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=3) (before_sound K77 V77) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K77 5 [(89,[]),(147,[64,33,49,16,118]),(153,[118]),(178,[16,67,83,118]),(201,[99,116,84]),(209,[99,116,83,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V77 low89 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,(pn 302231 419156143424012303)])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,(pn 690981 100112529940698453)]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,(pn 906841 938383889087598576)])),(BitVec.ofNat 152 (word80 [0x80981b160644809813,(pn 15941 599977161605255441)]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,(pn 1208778 245662311163228160)])),(BitVec.ofNat 152 (word80 [0x2e05c18178702e01c,(pn 16541 845403685938344755)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,(pn 1208925 819612869302812927)])),(BitVec.ofNat 152 (word80 [0x130160205808130120,(pn 170092 815418087668230826)]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,(pn 264581 668404956932132044)]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[32,84]]
def g55D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1049924) (before_sound K89 V89) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K89 5 [(55,[]),(59,[48,65,82,32,16]),(103,[33,100]),(110,[16,32,48,84,100]),(122,[48,65,82,97,33]),(199,[16,116,101,84]),(206,[16,48,116,101,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V89 low55 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ff80fffffff0,(pn 18889 456994599510278599)])),(BitVec.ofNat 152 (word80 [0x2a1a8251a148a02a1,(pn 794723 368333296315470409)]))),((BitVec.ofNat 152 (word80 [0x7ffffc0000ffc07fff,(pn 1190054 800357305912524856)])),(BitVec.ofNat 152 (word80 [0x44c132362c191344c9,(pn 238120 699149986591824749)]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,(pn 1208907 372870623917149696)])),(BitVec.ofNat 152 (word80 [0x1705c0b8305e1c1701,(pn 908763 790725641921279707)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,(pn 1208925 819614189736259647)])),(BitVec.ofNat 152 (word80 [0x180600c04060201802,0x80300000190c082492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080300008000600c,(pn 14180 939045595327252772)]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(2,0,85,0,5)]
def g87A : List (List Nat) := [[],[33,100]]
def g87D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g87L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g87D5)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,5,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P5_0 : block g87 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B5 : block g87 5 0 1=true := g87P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact g87B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K55 V55) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K55 6 [(87,[]),(167,[16,116,84,101]),(174,[16,32,48,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V55 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,(pn 1208649 118441798321107199)])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,(pn 302858 653367718168826129)]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,(pn 151098 429148429568446208)])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,(pn 685926 632540694940203963)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,(pn 1057811 244850887185596431)])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,(pn 26051 594509983722923622)]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,(pn 1208924 666714341587816432)])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,(pn 28334 416199508339999812)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,(pn 113494 459931333812062344)]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,2,73,16,5),(2,0,89,0,5),(8,0,83,0,5),(1,0,90,0,4),(16,2,73,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[96]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd40
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b2a0bf
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (1,1,3,0,0,0,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 2 0 4 0 0 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[]),(182,[16,32,67,83,118]),(203,[99,116,84]),(205,[33,115,100,84,83]),(213,[33,115,100,83]),(233,[81,33,99,116]),(241,[81,33,99,116,67]),(242,[16,96,32,83,50,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff801ffc07fe03fff,(pn 1208925 819614590239244799)])),(BitVec.ofNat 152 (word80 [0x805014028100408001,(pn 303707 770907968931926601)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffe00007fffc07f,(pn 1057957 382379889640607232)])),(BitVec.ofNat 152 (word80 [0x156298ab162a8a1515,(pn 667667 338150611823474395)]))),((BitVec.ofNat 152 (word80 [0x3fffffffff8000007f,(pn 1208778 250165562192982023)])),(BitVec.ofNat 152 (word80 [0x198320cc2433132626,(pn 44924 939271120878904466)]))),((BitVec.ofNat 152 (word80 [0xc0000000000000007f,(pn 1208925 815111046603964472)])),(BitVec.ofNat 152 (word80 [0x1e03c0f0383c1c3838,(pn 66177 912655989482792082)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x200401000040000040,(pn 75631 652954008975460644)]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(4,0,89,0,5)]
def g93A : List (List Nat) := [[],[67]]
def g93D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g93L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g93D5)
  | _ => emptyPacking
def g93I (_ _ : Nat) : Option (Nat × Nat) := none
def g93 : Forest := ⟨93,5,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B5 : block g93 5 0 1=true := g93P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact g93B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 6 := lower_forest (g:=g93) (i:=0) (hints:=1539) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 6 [(93,[]),(185,[82,118]),(186,[16,50,66,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,(pn 1208925 819614570218778631)])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,(pn 25098 311408250631977837)]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,(pn 1208335 667884281443369016)])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,(pn 196104 475483696833087195)]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,(pn 1208925 675499496466141632)])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,(pn 368434 544797595573016283)]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,(pn 1208925 819614569849269767)])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,(pn 529034 204828317107651730)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,(pn 604905 739769085423651108)]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,4)]
def g94A : List (List Nat) := [[],[50]]
def g94D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g94L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g94D4)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,4,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B4 : block g94 4 0 1=true := g94P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact g94B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 5 := lower_forest (g:=g94) (i:=0) (hints:=33646144) (before_sound K93 V93) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K93 5 [(94,[]),(124,[81,50,66]),(188,[33,49,65,81,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V93 low94 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,(pn 1208649 118148109799780415)])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,(pn 605090 712193548703519045)]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,(pn 302231 436899901662826432)])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,(pn 81465 507835005109089491)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,(pn 906712 810742461308338239)])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,(pn 26048 100041094978904714)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,(pn 1208907 373194464517427136)])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,(pn 179461 172161201235479340)]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,(pn 264616 247056932670737456)]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,73,32,5)]
def g107A : List (List Nat) := [[],[99],[81],[81,99],[48],[48,96],[48,81],[48,81,96],[96,48],[96],[96,81,48],[96,81]]
def g107D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=1048659) (before_sound K94 V94) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K94 6 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V94 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,(pn 1208787 469003790995192863)])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,(pn 755892 845066537344865445)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,(pn 75557 845767985541645280)])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,(pn 909645 918109925482007651)]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,(pn 1133377 178363348856602655)])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,(pn 13024 698501994769623370)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffff,(pn 1208916 596327460471047136)])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,(pn 51952 665198646203937692)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,(pn 56749 111614967047012880)]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,32,73,4,5),(32,0,77,0,5),(1,0,108,0,4),(4,32,73,0,4),(8,0,101,0,4)]
def g109A : List (List Nat) := [[],[48]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2012,(pn 10640 402918663730036000)])
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44000000,(pn 101530 886701146397736960)])
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (3,1,3,0,0,5,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 19 0 7 2 1 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 3=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=2098435) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(115,[33,99,67]),(117,[67]),(173,[82,118]),(181,[82,67,118]),(214,[16,98,115,67,82,84]),(227,[16,32,83,67,100,116]),(230,[16,115,67,101]),(234,[16,50,82,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,(pn 1206712 209433514605544447)])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,(pn 609482 766155251386197289)]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,(pn 1208787 451955721440066560)])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,(pn 47242 186518030200179811)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,(pn 208412 35304608648861894)]))),((BitVec.ofNat 152 (word80 [0x7fffffff,(pn 1208916 596327460471078880)])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,(pn 226679 72072932537291412)]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,(pn 907956 823074292147970840)]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(2,0,116,0,4),(4,0,114,0,4),(16,0,102,0,4),(32,0,86,0,4),(64,0,54,0,4)]
def g118A : List (List Nat) := [[],[98,84],[33,100],[33,65,81,97],[65,101],[65,82,97,33],[81,66],[81,98,65,66],[97,33,66,84],[97,82]]
def g118D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g118D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g118H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g118D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g118H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 628078 117388108550934528),0xc33600000000610000,0x6a000000005b0200])
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (2,1,3,0,0,4,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g118H5
  | 6 => lookupWord 2 37 0 8 1 3 g118H6
  | _ => fun _ => none
def g118 : Forest := ⟨118,6,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : block g118 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B4 : block g118 4 0 1=true := g118P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 2=true := g118P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : block g118 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B6 : block g118 6 0 1=true := g118P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=34669888) (before_sound K109 V109) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K109 7 [(118,[]),(229,[16,82,100,114,66]),(236,[33,49,84,100,116]),(244,[33,65,49,83,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V109 low118 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,(pn 604454 839313597785501951)])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,(pn 23632 587332985302356241)]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,(pn 606823 83163942432739072)])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,(pn 104076 823124529999196979)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,(pn 1206564 780369771284660239)])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,(pn 114153 685532969491916390)]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,(pn 1208925 675512518183751664)])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,(pn 152001 225776126551671876)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,(pn 303412 118581968886073480)]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[64,49]]
def g155D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g155L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 1=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K118 V118) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K118 7 [(155,[]),(179,[16,83]),(211,[99,116,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V118 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,(pn 1208909 678382502157253663)])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,(pn 47265 476900912396145829)]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,(pn 208153 98712227001764963)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,(pn 1204205 758105008907223071)])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,(pn 228306 776732229628668234)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,(pn 1208923 513876730662093792)])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,(pn 304003 355727768339231116)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,(pn 606825 245970254570996240)]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5),(9,0,162,0,4),(34,0,137,0,4)]
def g171A : List (List Nat) := [[],[81],[16,83],[16,48,80],[48],[48,81],[80,16,49],[80,49]]
def g171D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x31825f635474,(pn 45997 628584972743954704)])
def g171D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc110204810001,(pn 642860 393083663582828395),(pn 965963 861894045253646855),(pn 893878 543212922761643266),(pn 1202589 966390085481570849),(pn 587127 888071362789329216)])
def g171H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf100,0x1900008880a20000])
def g171D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3140cc503,(pn 396863 504484021018098960)])
def g171H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [2,(pn 111648 378076389133254683),(pn 1002640 492324354789475365),(pn 907584 421530913809997000)])
def g171D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g171H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x212002a001a,(pn 316731 748667097614270490),(pn 798670 231514286456315904),0x30000000000000001])
def g171L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g171D4)
  | 5 => (10,2,3,0,0,7,0,g171D5)
  | 6 => (3,1,3,0,0,6,0,g171D6)
  | 7 => (1,0,3,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g171H5
  | 6 => lookupWord 4 23 3 10 4 2 g171H6
  | 7 => lookupWord 3 31 1 9 2 3 g171H7
  | _ => fun _ => none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 3=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_1 : block g171 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 10=true := (@block_merge g171 5 0 1 9 g171P5_0 g171P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 3=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
  · exact g171B5
  · exact g171B6
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=1048659) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 8 [(171,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fff80ff1fe3ffc07,(pn 1175853 113329631925338623)])),(BitVec.ofNat 152 (word80 [0x81010202004000810,(pn 75594 759465861558604361)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc07fff001ffc3fff8,0xffe1fc3c655d1c0e07])),(BitVec.ofNat 152 (word80 [0x50a0a0414428085020,(pn 765392 597981500893897874)]))),((BitVec.ofNat 152 (word80 [0x7fffffe0003ffff,(pn 1204203 597180693722984504)])),(BitVec.ofNat 152 (word80 [0x60c0c0818030906040,(pn 907142 283734445019702418)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80000000003ffff,(pn 1208925 675499972198432704)])),(BitVec.ofNat 152 (word80 [0x8105050a0941228285,0xa001411013a8924924]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x206060c0180030306,(pn 22441 725772806491359524)]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(8,0,209,0,5)]
def g217A : List (List Nat) := [[],[118],[67],[67,118],[99,116],[99,116,67],[115,100,67],[115,100]]
def g217D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g217L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g217D5)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,5,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P5_0 : block g217 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B5 : block g217 5 0 1=true := g217P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : checkedTables g217 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g217 0 0 0 = true)
  · exact (rfl : block g217 1 0 0 = true)
  · exact (rfl : block g217 2 0 0 = true)
  · exact (rfl : block g217 3 0 0 = true)
  · exact (rfl : block g217 4 0 0 = true)
  · exact g217B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 6 := lower_forest (g:=g217) (i:=0) (hints:=3) (before_sound K171 V171) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K171 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V171 low217 (by decide +kernel)
def g218Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc01f,(pn 1138073 28522754252533775)])),(BitVec.ofNat 152 (word80 [0x8a2511444220228940,(pn 765062 722828016345765205)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffe0,0xfffff00c76790f00f0])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0182,(pn 925952 784110301962515251)]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,(pn 1204204 605828642294992655)])),(BitVec.ofNat 152 (word80 [0x3008060018440c0203,0x184080303024222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,(pn 1208924 666714341572087792)])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02c14,0xa00b040349c8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03018,(pn 41330 797117593319147656)]))),(0x0,0x0)]
def g218C : List ColumnInfo := [(8,0,210,0,5)]
def g218A : List (List Nat) := [[],[99,116]]
def g218D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g218L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g218D5)
  | _ => emptyPacking
def g218I (_ _ : Nat) : Option (Nat × Nat) := none
def g218 : Forest := ⟨218,5,fun i => g218Y[i]?.getD (0,0),g218C,g218A,g218L,g218I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218P5_0 : block g218 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g218B5 : block g218 5 0 1=true := g218P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g218 0 0 0 = true)
  · exact (rfl : block g218 1 0 0 = true)
  · exact (rfl : block g218 2 0 0 = true)
  · exact (rfl : block g218 3 0 0 = true)
  · exact (rfl : block g218 4 0 0 = true)
  · exact g218B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : graphValid g218 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=318857280) (before_sound K217 V217) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K217 6 [(218,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V218 : Known true K218 := extend_ok (m:=218) V217 low218 (by decide +kernel)
def g220Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe003ff01ff80ffe003,(pn 1206583 74180388515938311)])),(BitVec.ofNat 152 (word80 [0x49a84a3429164549a9,(pn 175212 527047990122591963)]))),((BitVec.ofNat 152 (word80 [0xfffc0001fffffffffc,0xffffc068dbb00e38])),(BitVec.ofNat 152 (word80 [0x81306c583224098130,(pn 255820 350088607833264713)]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,(pn 1208907 372870623917175232)])),(BitVec.ofNat 152 (word80 [0x1c070603c380e01c0,(pn 265339 51591640325329481)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,(pn 1208925 819614189736231423)])),(BitVec.ofNat 152 (word80 [0x120280814040901202,(pn 302241 831197271910795556)]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0x6754f2fe00])),(BitVec.ofNat 152 (word80 [0x1c0300018000e01c03,(pn 605659 646868030892436918)]))),(0x0,0x0)]
def g220C : List ColumnInfo := [(8,0,212,0,4)]
def g220A : List (List Nat) := [[],[67]]
def g220D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g220L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g220D4)
  | _ => emptyPacking
def g220I (_ _ : Nat) : Option (Nat × Nat) := none
def g220 : Forest := ⟨220,4,fun i => g220Y[i]?.getD (0,0),g220C,g220A,g220L,g220I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220P4_0 : block g220 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g220B4 : block g220 4 0 1=true := g220P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220T : checkedTables g220 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g220 0 0 0 = true)
  · exact (rfl : block g220 1 0 0 = true)
  · exact (rfl : block g220 2 0 0 = true)
  · exact (rfl : block g220 3 0 0 = true)
  · exact g220B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g220G : graphValid g220 (boundsBefore K218) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low220 : Lower true (varsX 220) (graphGoal 220) 5 := lower_forest (g:=g220) (i:=0) (hints:=839280128) (before_sound K218 V218) g220G g220T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K220 := extendKnown K218 5 [(220,[]),(248,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V220 : Known true K220 := extend_ok (m:=220) V218 low220 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,(pn 1178569 279235049704653823)])),(BitVec.ofNat 152 (word80 [0x5040150804a100a400,(pn 763000 158491694419191081)]))),((BitVec.ofNat 152 (word80 [0x3ffff80000ffffe00,(pn 27993 96611289036225536)])),(BitVec.ofNat 152 (word80 [0x9800a60036c004c803,(pn 253329 298836940639013987)]))),((BitVec.ofNat 152 (word80 [0x3fffffffff0000000,(pn 11573 306515451523629056)])),(BitVec.ofNat 152 (word80 [0xe0153802a70056f015,(pn 917972 406227378837363943)]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,(pn 1183055 280498601394962463)])),(BitVec.ofNat 152 (word80 [0x299c053380a6700a6,(pn 9547 64264335733512918)]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,(pn 10726 302879353885720544)])),(BitVec.ofNat 152 (word80 [0x31e0063c00c780138,(pn 10628 284232486370300564)]))),((34138 * 1000000000000000000 + 417981799316553728),(BitVec.ofNat 152 (word80 [0x3e0007c000f8001c0,0x1885b88053038c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,4,27,32,5),(0,8,54,1,5),(4,0,59,0,5),(8,0,55,0,5)]
def g63A : List (List Nat) := [[],[80,65,50]]
def g63D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe413f
def g63L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g63D6)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,6,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 1=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact g63B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K220) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 7 := lower_forest (g:=g63) (i:=0) (hints:=1049923) (before_sound K220 V220) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K220 7 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V220 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,(pn 1206762 517230291410546943)])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,(pn 394366 610621094899552529)]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,(pn 9242 589033195586457344)])),(BitVec.ofNat 152 (word80 [0x9029a05320db209901,(pn 725861 702782271870450619)]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738dada715000f0000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,(pn 1059351 380639082524145527)]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,(pn 1192491 469653974461710351)])),(BitVec.ofNat 152 (word80 [0x1700ce00ce00ce013,0x5179013b116666666]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442992504444444]))),(0x0,0x0),((15242 * 1000000000000000000 + 620261404986306560),(BitVec.ofNat 152 (word80 [0x20030003000300020,0x284001004268888888]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[]]
def g95D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 1=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=1603) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(190,[16,32,48,64,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffff6,(pn 529984 968234490205569087)])),(BitVec.ofNat 152 (word80 [0x5820a821282148142,(pn 454426 958651698105831749)]))),((BitVec.ofNat 152 (word80 [0xffffffc0003fffc00b,(pn 617980 245788667456524224)])),(BitVec.ofNat 152 (word80 [0x29105310db1099066b,(pn 617979 950732543844496595)]))),((BitVec.ofNat 152 (word80 [0x3fffffffc0000009,(pn 968614 987087710460833792)])),(BitVec.ofNat 152 (word80 [0x4e009c009c00de0b89,(pn 926113 598667556859424963)]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffa,(pn 104728 656800526303756351)])),(BitVec.ofNat 152 (word80 [0x7004e004e004e00c08,(pn 103985 598749188330922634)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc000000000000009,(pn 103348 306394496712835008)])),(BitVec.ofNat 152 (word80 [0x2700270027001000,(pn 80907 806185786367462188)]))),((BitVec.ofNat 152 (word80 [4,(pn 1107827 368516099187146752)])),(BitVec.ofNat 152 (word80 [0x803800380038002004,(pn 40144 800220659635653680)]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[48]]
def g111D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=1049939) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff57,(pn 152213 732673908859994175)])),(BitVec.ofNat 152 (word80 [0x504d41250452161417,(pn 151881 601204539488489797)]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0029,(pn 597445 236073143109681088)])),(BitVec.ofNat 152 (word80 [0x620988362064242629,(pn 103957 789995664255816785)]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,(pn 671921 42074015108956160)])),(BitVec.ofNat 152 (word80 [0x800e0038017838381d,(pn 57862 943044751806181571)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,(pn 348376 403185517339873279)])),(BitVec.ofNat 152 (word80 [0x9002400980000080,(pn 343552 254045616129745546)]))),((BitVec.ofNat 152 (word80 [0x91,(pn 553554 389419298218045440)])),(BitVec.ofNat 152 (word80 [0x4e013804e00404080,(pn 459105 905928678667373356)]))),((BitVec.ofNat 152 (word80 [0x4e,(pn 696371 522245685707538432)])),(BitVec.ofNat 152 (word80 [0x7001c007000808040,(pn 694596 11842156678548528)]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,32,81,6,6),(32,0,87,0,6),(16,0,103,0,5),(64,0,55,0,5)]
def g119A : List (List Nat) := [[],[33,100]]
def g119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fb7059653
def g119D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1002628,(pn 302601 764560807482622143),(pn 422158 344607034061940027),(pn 1121586 520501744575021139)])
def g119H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10
def g119D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x190e,(pn 500948 156045823103265377),(pn 337806 579555005207411795)])
def g119H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x69000000610000,0x220000000000,0x6300000000e5d000,0x34])
def g119D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def g119H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1980000007900
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 37 0 8 3 1 g119H7
  | 8 => lookupWord 1 11 0 7 2 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 1=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_4 : block g119 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 6=true := (@block_merge g119 6 0 4 2 g119P6_0 g119P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 3=true := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1049924) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[]),(231,[16,116,101]),(238,[16,32,48,84,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc03fffffff72,(pn 41533 763557241816879103)])),(BitVec.ofNat 152 (word80 [0x214040808000820032,(pn 37798 243764701307883845)]))),((BitVec.ofNat 152 (word80 [0x1fffffc03fff00ad,(pn 513301 48146794140135424)])),(BitVec.ofNat 152 (word80 [0x5880500009004022c,(pn 59657 996185614938879187)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe00000003fffffbd,(pn 706230 286826262874816575)])),(BitVec.ofNat 152 (word80 [0x4602960b0b05282885,(pn 101767 372480794744889994)]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000080,(pn 354282 972995685640830912)])),(BitVec.ofNat 152 (word80 [0x880318121206304c80,(pn 316484 69898817873412616)]))),((BitVec.ofNat 152 (word80 [0x91,(pn 554733 684144060434743296)])),(BitVec.ofNat 152 (word80 [0xf013e01c1c27c07091,(pn 535253 921560869853121324)]))),((BitVec.ofNat 152 (word80 [0x4e,(pn 696371 522245685707538432)])),(BitVec.ofNat 152 (word80 [0x1c00202038008048,(pn 606565 854415259250658352)]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(8,0,115,0,7)]
def g123A : List (List Nat) := [[],[96]]
def g123D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g123L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g123D7)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,7,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 1=true := g123P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact g123B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 8 := lower_forest (g:=g123) (i:=0) (hints:=1048643) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 8 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,(pn 939045 599695546098877439)])),(BitVec.ofNat 152 (word80 [0x502050202000101000,(pn 322458 490494292354831525)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf80007fff003fff801,(pn 530107 952631108428921856)])),(BitVec.ofNat 152 (word80 [0x600d6009406805202c,(pn 528923 612748866942766179)]))),((BitVec.ofNat 152 (word80 [0xfffff8000003ffffff,(pn 574710 117599214596784159)])),(BitVec.ofNat 152 (word80 [0x8149814d82b0a64149,(pn 234699 730794951911745866)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc000001,(pn 12360 132512857574081504)])),(BitVec.ofNat 152 (word80 [0x18e018e04c0c78271,(pn 12212 413794146735958346)]))),((BitVec.ofNat 152 (word80 [1,(pn 164894 327456943059270656)])),(BitVec.ofNat 152 (word80 [0x5f005f00702f80381,(pn 13778 588741198576251804)]))),((742129 * 1000000000000000000 + 573845209073025024),(BitVec.ofNat 152 (word80 [0x60006000803000400,(pn 642249 47552838578225680)]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(8,0,117,0,7)]
def g125A : List (List Nat) := [[],[67]]
def g125D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g125L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g125D7)
  | _ => emptyPacking
def g125I (_ _ : Nat) : Option (Nat × Nat) := none
def g125 : Forest := ⟨125,7,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 1=true := g125P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact (rfl : block g125 6 0 0 = true)
  · exact g125B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 8 := lower_forest (g:=g125) (i:=0) (hints:=2098435) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 8 [(125,[]),(189,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,(pn 1025449 475008929483195391)])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,(pn 118745 303630259806315817)]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,(pn 296773 689920639860734976)])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,(pn 879985 950361475561393251)]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,(pn 34055 274991122184667136)])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,(pn 29332 872478356218813671)]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,(pn 946113 141726850976841759)])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,(pn 20505 436140397198868448)])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,(pn 18936 165012877527896724)]))),((243983 * 1000000000000000000 + 393810807020027904),(BitVec.ofNat 152 (word80 [0x1c000e0007000200,(pn 7085 603529566907556632)]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(8,0,118,0,7)]
def g126A : List (List Nat) := [[],[81,66]]
def g126D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g126L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g126D7)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,7,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : block g126 7 0 1=true := g126P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact (rfl : block g126 6 0 0 = true)
  · exact g126B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=34694464) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,(pn 977697 249293364974551071)])),(BitVec.ofNat 152 (word80 [0x481610542128429028,(pn 325992 227622980336915621)]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,(pn 529296 295957148711519200)])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,(pn 529222 147426249581104227)]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,(pn 272807 894751702434216960)])),(BitVec.ofNat 152 (word80 [0xe13884e109c21bc171,(pn 271627 298626856698891891)]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,(pn 314257 150020502396338207)])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,(pn 11872 788339081831852362)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000001,(pn 165173 406518685240164320)])),(BitVec.ofNat 152 (word80 [0x38007000e00200,(pn 11400 183680345129234828)]))),(0x0,0x0),((742129 * 1000000000000000000 + 573845209073025024),(BitVec.ofNat 152 (word80 [0x200c0018003000400,(pn 642321 105076507761984016)]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(4,0,171,0,8)]
def g175A : List (List Nat) := [[],[48]]
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g175L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact (rfl : block g175 7 0 0 = true)
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1049939) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,(pn 577914 747931349851570207)])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,(pn 275683 281205920844125349)]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,(pn 712640 761516851078397920)])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,(pn 681797 787407946091627553)]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,(pn 1023644 459590750592532480)])),(BitVec.ofNat 152 (word80 [0x17083841c217838381,(pn 1023635 200190590612000371)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,(pn 23593 978658918894666751)])),(BitVec.ofNat 152 (word80 [0x980240120098000008,(pn 21730 852819478044289354)]))),((BitVec.ofNat 152 (word80 [9,(pn 108921 360528938755947520)])),(BitVec.ofNat 152 (word80 [0xe003801c00e0040408,(pn 33361 117402047785087372)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,(pn 1100744 762900167011598336)])),(BitVec.ofNat 152 (word80 [0xc00600300080804,(pn 302326 12487498612621840)]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,4,147,32,6),(16,0,167,0,6),(32,0,147,0,5),(32,4,147,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3,(pn 11763 847092003883014484),(pn 273728 979754544646935380),(pn 790622 165920981855850306)])
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 4729 430486671684288780),(pn 306963 486819215432421395),(pn 28666 372656550154128058),(pn 805745 671669955435372560),0xbf58f54bfd8d54bf59,(pn 251392 52969957290753021),(pn 704882 325944879228732407),(pn 400594 84965090604676143),(pn 856210 435700266624194370)])
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1d40000000,0x70000000,0xa4042000000000,0xc00000000016000000,0])
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8512ec33a544b0c,(pn 786593 586869992069851473),(pn 208735 737167874049071177),(pn 265210 716141940992092831),(pn 1158158 839680681392860994)])
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6c0,(pn 279800 223398937814368256),0,0x201c4000000c,(pn 988155 186540473260965888),0xe0000000000,0x2282400000,(pn 102711 471002415613870098)])
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x681117f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (140158 * 1000000000000000000 + 402567410378875227)
def g183L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g183D5)
  | 6 => (14,2,3,0,0,8,0,g183D6)
  | 7 => (7,1,3,0,0,8,0,g183D7)
  | 8 => (1,0,3,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 53 0 7 3 0 g183H6
  | 7 => lookupWord 3 71 2 8 4 0 g183H7
  | 8 => lookupWord 1 11 0 7 3 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 6=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_2 : block g183 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 14=true := (@block_merge g183 6 0 2 12 g183P6_0 g183P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : block g183 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 7=true := (@block_merge g183 7 0 2 5 g183P7_0 g183P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1049924) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[]),(215,[16,116,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffff80ffffffc,(pn 919827 601398019912631295)])),(BitVec.ofNat 152 (word80 [0x11410a081020010400,(pn 917460 345902587377259685)]))),((BitVec.ofNat 152 (word80 [0xffe000fffff01ffe03,(pn 663370 399031344365566976)])),(BitVec.ofNat 152 (word80 [0x1802c00a000400809,(pn 661599 429905560156343395)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000001ffffe,(pn 1004395 134251260373368863)])),(BitVec.ofNat 152 (word80 [0xa20a3052c2c58a50a2,(pn 97700 769516420631701834)]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00002,(pn 83429 71352537836191712)])),(BitVec.ofNat 152 (word80 [0xc40c406304890c6132,(pn 83233 38675972339278088)]))),((BitVec.ofNat 152 (word80 [2,(pn 497408 604137143669850112)])),(BitVec.ofNat 152 (word80 [0xf80f807c070e0f81c2,(pn 459334 524207804562420108)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,(pn 259823 117644723225886720)])),(BitVec.ofNat 152 (word80 [0x1000800000100000,0x108421084210]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(16,0,171,0,8),(8,0,179,0,7),(32,0,155,0,7),(1,0,186,0,6),(2,0,185,0,6),(9,0,178,0,5),(10,0,177,0,5),(17,0,170,0,5),(33,0,154,0,5),(34,0,153,0,5),(40,0,147,0,5),(128,0,59,0,5),(25,0,162,0,4),(41,0,146,0,4),(42,0,145,0,4),(136,0,51,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[16,83]]
def g187D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 72648 768104222802676811),(pn 50194 525558870308836616),(pn 376787 491663909270732307),(pn 617981 370512035394884326),(pn 239108 264379320049680656)])
def g187D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc1820,0x1a25004000000000,0,0,0,0x6040030,(pn 151115 727451830930147868),(pn 631045 256305177560336876),(pn 574321 454039492573193633),(pn 485690 538990808656633201),(pn 428966 746868128108846401),(pn 372242 954745447561059601),(pn 315519 162622767013272801),(pn 258795 370500086465486001),(pn 202071 578377405917699201),(pn 145347 786254725369903176),(pn 67352 572086039616705551),0x26be1171d49528bf84,(pn 436634 813525857654900560),(pn 1089541 219832177598796145),(pn 1001824 925198791660356397),(pn 681627 770840435604703074),(pn 397476 465911399784835456),(pn 134405 662082019461269840),(pn 670432 341789017961270370),(pn 1021600 47623831637279539),(pn 1043461 228929180517894497),(pn 397614 799304935523143043),(pn 116105 339325249464141136),(pn 677520 484339418146900817),(pn 700479 126788695745970798),(pn 1062958 841814027909566801),(pn 95378 732997816842235764),(pn 418318 59262170410336336),(pn 976191 160578904028451698),(pn 396772 83774004639384250),(pn 764251 291208148693910864),(pn 95367 205209954566453124),(pn 440768 305090649174410816),(pn 818596 305898484794787957),(pn 417413 679117977310004028),(pn 417174 73749949387755857),(pn 680959 94400481986798450),(pn 417136 872885926184699200),(pn 660988 761466830099190129),(pn 1004130 697276316056060471),(pn 1061783 439694759809635617),(pn 642887 338507641432095076),(pn 435437 141871616072173072),(pn 1107806 373702293117602160),(pn 724017 181249359825879859),(pn 154495 342628036953360741),(pn 322066 158687179491815284),(pn 134999 344885152451237136),(pn 967349 982888546841533797),(pn 119554 239321462032056879),(pn 1062964 608602990867503954),(pn 321890 358406862439507810),(pn 436618 598477542103795984),(pn 660988 766793671823461750),(pn 399354 380280690251154138),(pn 455825 189271208951925072),(pn 321990 659498578774223714),(pn 1003890 566494252349866256),(pn 1048497 784536132906519926),(pn 396993 23086913441251991),(pn 457005 780891755918497104),(pn 322040 778650357384999815),(pn 398523 766282286542422288)])
def g187H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x5005d0,0xc2000000003d03])
def g187D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x37738ec4,(pn 795402 211666681333168914),(pn 763766 412795105336912970),(pn 628027 605460049744998698),(pn 130853 375858324237894824),(pn 448170 675508449847710369),(pn 1038193 503538640707013255),(pn 525701 407401218784930323),(pn 1160731 490641547641399406),(pn 935868 273478068278567355),(pn 1023094 852020376657626559),(pn 549423 953692981268715453),(pn 950991 65686291924938438),(pn 177186 803901245815897432),(pn 330957 896975815373418338),(pn 700479 216665319173905734),(pn 384064 655606807064933925),(pn 327332 820818201505618101),(pn 24847 528085637263483604),(pn 99353 797989578520760913),(pn 95460 395431566022945092),(pn 381896 903944084639290641),(pn 315803 226370235988988997),(pn 64836 173518282575925524),(pn 263782 864842232607096912),(pn 1053902 445044214220085506),(pn 603147 188250387773154317),(pn 1118807 766532635544883255),(pn 772895 743526243154673823),(pn 825723 282809011874366204),(pn 870874 392006313422096890),(pn 1117591 960951952006723499),(pn 50232 825622938041499502),(pn 200783 711505253474139832),(pn 966499 195233150037778148),(pn 843681 727479674808298422),(pn 767981 467119813334117018),(pn 654075 309832430560459562),(pn 198445 421745172186310824),(pn 793928 108010674368193184),(pn 757916 124038460062182018),(pn 610354 79273248720759985),(pn 23601 553337485376727364),(pn 130853 659642206916355344),(pn 597804 592810447484947521),(pn 299237 684943584880111876),(pn 1206386 249365877477131286),(pn 1198619 964675347227807855),(pn 406515 952399814595723707),(pn 421805 16511727589722091),(pn 539901 759965655782923237),(pn 629560 299393582269222871),(pn 120810 95249709519159260),(pn 407682 447188117716069746),(pn 1002655 188381002173251033),(pn 383843 164106518303782693),(pn 307562 359672049569323381),(pn 114579 551074952083501268),(pn 458309 125324434566387025),(pn 624200 611456416409339206),(pn 79089 121148163350959368),(pn 320931 349145334481869137),(pn 47129 211574894076519748),(pn 259649 76714766105679120),(pn 1048038 733982323854169154),(pn 603137 962204355735671052),(pn 1203220 200828293276320815),(pn 583558 896030175643111631),(pn 815256 890176457806201590),(pn 873871 303368946763237886),(pn 1108301 288458962988181491),(pn 862505 788216540490948076),(pn 427708 621279663193521336),(pn 501908 595984652154043116),(pn 798709 121556472398863234),(pn 776984 351662210526654010),(pn 614525 508957344137788106),(pn 40286 703212939212549288),(pn 161112 535673518023715488),(pn 644007 488390297214028418),(pn 159349 394350236925241864),(pn 641807 358040872759633954),(pn 131738 93913765101871240),(pn 564712 860774008349164065),(pn 1190558 988613345000163463),(pn 1139590 566275502077125145),(pn 1197513 68837875178571870),(pn 1167111 739256671838544254),(pn 441025 64541654365013753),(pn 479616 575366861884102629),(pn 1007049 568110445731540886),(pn 401420 820353157404159573),(pn 94526 14483722158784372),(pn 417729 509632201956386267),(pn 380522 781687599288268645),(pn 303722 699349456261109973),(pn 5966 706883977804865876),(pn 23867 979894732026136933),(pn 378737 825869231516224842),(pn 155495 264876829819573844),(pn 621962 612754457158767649),(pn 46022 803247211871823172),(pn 183795 920968479521477904)]) else (word80 [0x810107041000,(pn 53182 540768751198011656),0x20400304003042c162,(pn 19112 29391974152802328),(pn 610993 345440206438337552),(pn 379122 168509475493793992),(pn 313447 369178705356177675),(pn 618777 596790243542175744),0x21041a8a803a2a008,0x101c107041a204,0x18304083040c10b042,(pn 911619 933661945182335088),(pn 19517 125884871601881088),(pn 152296 393404068669184002),(pn 321176 552693232293839368),(pn 38226 283667992078188560),(pn 37926 798549801840680976),(pn 152296 536406481204003332),(pn 38076 408200620778999872),(pn 609259 63337947460804608),(pn 17156 48450402806350088),(pn 94891 222874385684893696),(pn 14241 179158893528886288),(pn 304020 843721253665661185),(pn 37852 732429494892367872),(pn 4722 906950756634460164),0x10000000b040000000,(pn 302268 350643819980570881),(pn 18963 829404467099403012),(pn 642575 54290056359712784),0x462098810b0484106,(pn 21325 616171755176722433),(pn 190119 251397483908300848),0x400000104040020488,(pn 76776 537787299265790024),(pn 612761 642034507200627649),(pn 619866 230992938456850512),(pn 531293 323547603067437102),0x4178020fe0083c1780,(pn 292791 547548505126995982),0x4403c2e00b0b23b203,(pn 135504 240762505464443659),(pn 832963 66439216230759087),(pn 542844 948759192099335746),(pn 1061018 878659106817528531),(pn 816430 603388113719049387),(pn 692779 796289540717783522),(pn 739817 234173675948274317),(pn 796946 228834065969215655),(pn 540520 100423178165790306),(pn 465853 92390433976562255),(pn 778052 150055192555041955),(pn 85844 428158227357999682),(pn 154100 790867498580873735),(pn 756205 727392651077087903),(pn 84700 432713297447460321),(pn 1032380 234720219907281353),(pn 738492 528570467300259483),(pn 234672 191752791212399201),(pn 758418 399342937136255375),(pn 720779 329748274929301655),(pn 535796 571727861922895457),(pn 465557 871283889285435725),(pn 701885 395154984111258771),(pn 836884 58214784140153441),(pn 163254 918917548487577879),(pn 686533 956175759312750736),(pn 80235 239517401838882464),(pn 1088767 249844690762944723),(pn 665277 973438738840206475),(pn 683369 659417451655957024),(pn 729779 754841237745094795),(pn 644612 574777663371114119),(pn 228730 880636248072357152),(pn 361342 911807090002702381),(pn 616271 168396560686911104),(pn 831237 959027141100868863),(pn 530536 802541351006262269),(pn 932092 410142713581231831),(pn 62743 330263349758095325),(pn 104284 812179809897000276),(pn 399411 928795805390667217),(pn 461984 141708246960305957),(pn 639008 468396947221142565),(pn 119308 728829916837671380),(pn 174947 976068600852727632),(pn 699646 636208253243434385),(pn 381772 413219974433027621),(pn 318588 703346695897143445),(pn 65424 382086135994081876)]))
def g187H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x28588d91d74700,0x24ff180000000,0xa8200063a13bc9d806,(pn 307544 117196888606548832),(pn 73715 558212857131578544),0x622035000d39,(pn 569045 161185793620513792),0x62e0003018979114,(pn 188026 676182525090467138),(pn 541718 125927154775049491),(pn 151132 201620166974391583),(pn 126325 609491035089536791),0x624f4409ad9800000,0x2410,0x72aa4900058b,(pn 469896 880532665543950484),(pn 477835 604408684922191935),(pn 36658 745994925862850355),(pn 991424 629912952419716130),(pn 458958 536886800384827612),(pn 54345 991587541742177040),(pn 152591 503805912887328913),(pn 680020 773533238599617030),(pn 53238 673837056378079317)])
def g187D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x21610186,(pn 624242 508019577597772097),(pn 104262 186669609200922912),(pn 618783 944631360276271656),(pn 226767 420325084958755928),(pn 684771 102884536233691272),(pn 38683 220339285339226889),(pn 39405 776799361444962561),(pn 633610 19855289045099560),(pn 9501 809916719504302129),(pn 492381 72945213558425624),(pn 850634 819874034932648711),(pn 606538 367342605807761415),(pn 42723 668646190209071233),(pn 37190 518816739361833080),(pn 1114538 810672570010066976),(pn 246754 603609659000529295),(pn 907657 63317504833138818),(pn 226767 275158355259168512),(pn 835902 685830166408840326),(pn 141689 983562298879903366),(pn 297524 130726212295238657),(pn 1058365 818625475248136369),(pn 113383 645486863645705600),(pn 192164 507605580595593865),(pn 85317 56388317707809032),(pn 22435 7074161115815425),(pn 762745 449604488594752032),(pn 303267 68385699460964365),(pn 152037 497351564014232260),(pn 142021 541460419062316035),(pn 316548 650410130797592616),(pn 617486 941649641115246602),(pn 189487 333553601494770050),(pn 16531 885641231216179426),(pn 922634 234289743043498072),(pn 661154 781538421290043072),(pn 95782 588414459370012996),(pn 75908 374668872814707762),(pn 226787 461880267236447288),(pn 617530 124991015036291116),(pn 330577 345718903813222405),(pn 66713 514990942323402302),(pn 344195 354997198782614992),(pn 1037992 9001411306929362),(pn 666237 569050821738351036),(pn 608113 945024601989700546),(pn 880639 759464269096886447),(pn 1109104 442110875653022954),(pn 276877 123108955135506805),(pn 704687 641987982237936008),(pn 39522 421674837092367287),(pn 691661 195528626557118164),(pn 508071 639464805201740125),(pn 1160343 528397830469079236),(pn 1106453 338398348955382828),(pn 305255 8547574399592244),(pn 392476 327915198845560274),(pn 279238 880979664783319400),(pn 96239 262568849742013192),(pn 77310 579169877663516498),(pn 1205830 599162058397144341),(pn 226480 284014641077549447),(pn 382499 612386795646418836),(pn 477253 987405160670105597),(pn 384005 823273349140795647),(pn 418317 967517203408655631),(pn 1197217 973678956812272976),(pn 1204652 304385620586763349),(pn 75359 944314376623749444),(pn 382499 310645620611546964),(pn 472531 599512600529080317),(pn 331174 348049432399126783),(pn 398192 569729212875038991),(pn 1197508 509899200069473552),(pn 1204670 462899609128622225),(pn 75507 788482396266954049),(pn 80267 841100833415675736),(pn 553327 779565663176437693),(pn 346259 210156231922635455),(pn 724074 765983275162047531),(pn 1159697 278148676614441808),(pn 1054650 297972829617871205),(pn 56475 162125411264757137),(pn 381328 253145040590797592),(pn 703890 664828420383640573),(pn 629568 844072281449975999),(pn 416842 221226010529588235),(pn 1159751 465459045275877952),(pn 904800 406275525115335956),(pn 75064 503604600636175766),(pn 155761 182036361157344072),(pn 463085 136284721305750517),(pn 704241 12018534374514879),(pn 724312 267814107929403663),(pn 1082640 616608180859409680),(pn 903619 598477626735319185),(pn 56475 360283519655863617),(pn 80253 717816728855035801),(pn 307174 431358722817461181),(pn 648452 582814814497951931),(pn 418022 521313418821518603),(pn 1027230 55470565820830224)]) else (word80 [2,(pn 987086 164933669811395602),(pn 17766 414604605292030992),(pn 644704 926752720375133218),(pn 15386 243078821116977184),(pn 833059 798693906791669268)]))
def g187H7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xb6ec6ce7,0x53f0001,(pn 119239 753700759988731918),(pn 521821 496364534679470120),(pn 595018 176841575297976674),(pn 154491 481617317494784714),(pn 369027 115194559580078080),0,0,0xc6b00000000000,0,0,0,0,0,(pn 623802 951874312468430848),0,0,(pn 7816 807951399566203219),(pn 151115 727504026491682816),0,0,0x30a26640000000000b,(pn 420290 616975398424018960),(pn 528905 46257871880192000),0,(pn 134329 190344752954867712),0,0,0x1ec000000c1680000,0x13a643800000000000,0,0,0xf880000000000,0,0,0,(pn 5981 356765900322111488),0,0x3cae000,(pn 96956 98530429913530368),0,0,0,0,0xc250000001438000,(pn 92086 146415958081667072),(pn 541312 463054805980434432),0,0xb15800000000015180,0x1ad7000000000000,(pn 61943 119512677163991226),(pn 302231 457834405537513472),0x5da4,0xb4d00000000000000,0x24cba5f00000000,0x74680000000006b,(pn 566683 977944357425643520),0,0x8d80000000,0,0x11,(pn 136948 628003221862875136),0,(pn 27347 298089274410270720),0,0xc070000000,(pn 468104 577614453704884224),0,(pn 8713 780731818549889024),(pn 23192 169319548481942528),0x6568000000c8b,(pn 604462 909807314587353452),0x48340000000000,0x1b3300000000000,0x1e0600000,0,0,0x12a9,0x42b0,0x41ebd500000000,0,0x118e00050,(pn 566683 977944357425643520),0x5044000000000,0xc24,0x421e20c000000aa2c,(pn 157018 685555415703355392),0x1ca600000000,0,0,0,0x34340000000000,0,0x39f00004aeb7180000,0x40b7b038f200000,0x575c00,0x208c000000,0,0x10102000000000000,(pn 377790 471553275247263760),(pn 226968 748144014852620801),(pn 80280 230772902421594368)]) else (if j<2 then (word80 [0xf23800,(pn 126987 386301822844010496),0,0,0x546a98cee400000000,0x400800000000000,(pn 29371 828251364033560576),0,0x16350000000000,0x4cb800120b0000,0x34d80000000003cb20,0x3324000000b5c00,(pn 12340 871785311690031104),0x7ba80000000004d8,(pn 302255 328485281984676681),0,0x10770,0x394000000000000000,0x4d8000000002600000,0x241d41f000000312,(pn 567440 294451379517259776),0xf9280038e0,(pn 969544 763645760532054016),0x1a,(pn 363622 219180962681454635),(pn 18889 465931478580854953),(pn 528905 46081400263933952),0xdab80004ea000,(pn 254122 347874549806137344),0,0xe3c00000,0,0xf01000000,0x413,(pn 620179 535758115125329920),0,0xa4400002100000008,(pn 401401 151043919843164160),0x918babc00186,(pn 459471 501387957511651328),0,0x7a10,0x2832cb0000c,(pn 743772 889444373938307072),0,0x16780021b,(pn 453347 182355485940514816),0x39240000000000000,0x22380000000,0x51600000000,0x83d000000000000038,(pn 982252 228436886206086656),0x71000,0xa218c0000b62000,0x82e0000,0xc1e00000002d60,0x7e0c00000000000000,0xa8f0000000000a3000,0,0,0x10960000000000000,0x4690000,0x54c00000000000018,(pn 774468 103190621815046144),0x2cd530e00,0x187,(pn 604462 911849107680133120),0,0x44000000000000,0xb000043440,0,0x978000000000000,0x1bac000000000,0x133c91b1a40000,0,0x43474080000,0x682000000000000,(pn 10983 275751389689544704),0,0x1e240000000000000,(pn 4869 940435459321626624),0x38bc0000000,0x330800085400000,0x577800000000,0,0xe450001cb6000843,0xa36000b4b0921d1c,0,0x3aa60,0x208a00000000,0x8ba800000000,(pn 54505 108350127124668416),(pn 215347 291535854317764608),0x122e0000000,0x4b939880000006280,0x93a00000,0,0x70c800,0,0x10b40000000000,0x1270db40000000006,(pn 1063713 78765728976338958),(pn 661131 307601750329917506)]) else (word80 [1,(pn 768565 145089403433242552),(pn 886139 503666088709718016),0x59bc00063,(pn 549334 815143033601136640),0xcc500024bc000000,0x200600000078a8,0x65a0,0x41858,(pn 925583 830642450461884416),0,0x9130000000000000,0x18980006ae7d3982a,0xa6860140000000000,0x3534000d5580000000,0x58400000000,0,0xf4ebaf,(pn 658265 266746406461243392),0x21a80000000000000,0x31960000,0x32ca00000000000,0xaa50000000000000d6,(pn 680020 773533228910772224),0x11180005bc000000,0x44961f46bc000,0,0,0,0,0x6c84000000bc4800,0xe170000000000000,0xd440000,0x49cc9c00000000000,8,(pn 243902 850142598102589184),0xa3a000000000,(pn 77660 792550317212303360),0,0x4f694ba00016c8,0x21d0000000000c,(pn 533627 412564269909147648),0x10e,(pn 377789 318629571617095680),0,0x69e0000000000,0,0x24ec00000041029,(pn 853863 632777813998698496),0xaa6000000,(pn 129325 974885520858154707),0xd2b0001102,0x8a800026e22630000,0x21b80000])))
def g187D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [5,(pn 17122 348100401154570755),(pn 317584 36939701604602113),(pn 85062 841379376014116644),(pn 188988 88755202230853697),(pn 756541 363907575727548429),(pn 77939 805268344131106957),(pn 297980 265342481167290112),(pn 301832 532012321797391356),(pn 764973 866139356860753951),(pn 1067548 317952351978781712)])
def g187H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 254232 676882900146783856),(pn 989842 243968330129168597),(pn 135050 186258262908795497),(pn 414056 53362455806461013),(pn 609202 92731443078937784),0x2d590c51c40014575a,(pn 1099573 535406930008071729),(pn 1000035 541709651342638648),(pn 847451 785438151636250306),(pn 1168667 675915372666814483),(pn 273019 890503851217791013),(pn 718980 484619981081804836),(pn 456138 17837956630730924),(pn 850030 126839121757538138),(pn 1016005 227377019065482568),(pn 1160998 377095450077429810),(pn 1190037 219655036216289502),(pn 258794 330721417316567352),(pn 649104 32976331887840768),(pn 6083 203872500754927664),0x3058001b2400800188,(pn 40951 771843635204587520),0x3b2e58d124a37,(pn 930696 806013752053557830),(pn 1116578 383387909400577501),(pn 231872 765012278987165054),(pn 943292 816623409300091458),(pn 191991 181296178788439360),(pn 17014 775684601626378336),(pn 14544 719680438071264256),0x1980614980000802a2,(pn 759232 134681460199195137)])
def g187D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8200ff
def g187H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x19df2f1c0000f,(pn 793357 675432230510216984),0x1d23600000,0x2980000000000000,0x35000520000000,(pn 1038920 626240219431365888),(pn 127748 314404153653734303),0xfae41010])
def g187L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g187D4)
  | 5 => (83,4,5,0,0,10,0,g187D5)
  | 6 => (238,3,5,0,0,12,0,g187D6)
  | 7 => (121,2,5,0,0,12,0,g187D7)
  | 8 => (14,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g187H5
  | 6 => lookupWord 24 149 5 12 7 1 g187H6
  | 7 => lookupWord 77 1571 4 13 8 1 g187H7
  | 8 => lookupWord 38 191 7 12 7 1 g187H8
  | 9 => lookupWord 6 67 4 9 4 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P4_0 : block g187 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B4 : block g187 4 0 6=true := g187P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 83=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 83=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_21 : block g187 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_117 : block g187 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_213 : block g187 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 238=true := (@block_merge g187 6 0 117 121 (@block_merge g187 6 0 21 96 g187P6_0 g187P6_21) (@block_merge g187 6 117 96 25 g187P6_117 g187P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_10 : block g187 7 10 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_73 : block g187 7 73 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 121=true := (@block_merge g187 7 0 10 111 g187P7_0 (@block_merge g187 7 10 63 48 g187P7_10 g187P7_73))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 14=true := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact g187B4
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=1048643) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,(pn 326234 679128851003474943)])),(BitVec.ofNat 152 (word80 [0x481400540128029029,(pn 302602 20653621555790881)]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,(pn 1171836 64217836780781568)])),(BitVec.ofNat 152 (word80 [0x90a612982db05320cc,(pn 1096278 200456676084260071)]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,(pn 272805 642882619516419072)])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,(pn 120509 323792493464366443)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,(pn 314254 844247894173646879)])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x894809498884210842]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,(pn 165175 712361661168877536)])),(BitVec.ofNat 152 (word80 [0x98013002600200,(pn 162370 620556830845850260)]))),((BitVec.ofNat 152 (word80 [1,(pn 742129 573845209072009216)])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,(pn 99218 136910863864193816)]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33,118],[48],[48,33,118]]
def g207D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 1=true := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=1651) (before_sound K187 V187) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K187 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V187 low207 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffe88,(pn 367194 299890940685288447)])),(BitVec.ofNat 152 (word80 [0x501402801080010280,(pn 341209 430797224462287905)]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff8195,(pn 1139405 844090002893470720)])),(BitVec.ofNat 152 (word80 [0x61184b08a004420994,(pn 1139367 795826998772084075)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,(pn 628965 321200760874074143)])),(BitVec.ofNat 152 (word80 [0x80200c02c108140051,(pn 628374 952390739441686726)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,(pn 218934 759791173415501792)])),(BitVec.ofNat 152 (word80 [0x4010030000181021,(pn 19188 793322389540835460)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x44,(pn 683554 23081287606042624)])),(BitVec.ofNat 152 (word80 [0x581602c0211602004,(pn 78776 938532031395816216)]))),((BitVec.ofNat 152 (word80 [0x33a,(pn 389779 939842362095697920)])),(BitVec.ofNat 152 (word80 [0x6018030042180400a,(pn 11990 458538414689501712)]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,2,73,144,6),(1,0,218,0,6),(2,0,217,0,6)]
def g219A : List (List Nat) := [[],[99,116]]
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4a8b9,(pn 100694 66782898237863184)])
def g219D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x344191bf
def g219H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x28f
def g219L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g219D7)
  | 8 => (1,0,3,0,0,0,0,g219D8)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g219H8
  | _ => fun _ => none
def g219 : Forest := ⟨219,8,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 2=true := g219P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact g219B7
  · exact g219B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=67) (before_sound K207 V207) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K207 9 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V207 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,(pn 1173566 300158732531666943)])),(BitVec.ofNat 152 (word80 [0x50028008000080,(pn 40177 14367728809611537)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffc03ffc0,(pn 116836 209819771664920576)])),(BitVec.ofNat 152 (word80 [0x2a45626b1250692905,(pn 721151 536667329390147447)]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,(pn 964279 319937728199458831)])),(BitVec.ofNat 152 (word80 [0x4c09804c0360b03209,0x11ad4a201222222222]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,(pn 15704 538775792852664560)])),(BitVec.ofNat 152 (word80 [0x700e00700380c03c0e,(pn 5036 555952872931598882)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000000000000000,(pn 20591 626311420549791488)])),(BitVec.ofNat 152 (word80 [0x9004802401024010,(pn 20222 396314465027524744)]))),((243881 * 1000000000000000000 + 224984588776898560),(BitVec.ofNat 152 (word80 [0x80e007003802038020,(pn 236788 360689997675547852)]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(8,0,213,0,7)]
def g221A : List (List Nat) := [[],[67]]
def g221D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g221L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g221D7)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,7,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 1=true := g221P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact (rfl : block g221 5 0 0 = true)
  · exact (rfl : block g221 6 0 0 = true)
  · exact g221B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 8 := lower_forest (g:=g221) (i:=0) (hints:=1539) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 8 [(221,[]),(249,[82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00ffffffffffffff,(pn 930992 347280045895581727)])),(BitVec.ofNat 152 (word80 [0x481610542128429029,(pn 911494 138503766259963045)]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff800,(pn 1171540 711399972854039520)])),(BitVec.ofNat 152 (word80 [0x90a442988db11320cc,(pn 1171540 620202092591951211)]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,(pn 272805 913097498687208448)])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,(pn 196067 417200880405023843)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,(pn 314254 844247894173646879)])),(BitVec.ofNat 152 (word80 [0x1c007000e001c0180,0x89c801c88884210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,(pn 165175 712361661168877536)])),(BitVec.ofNat 152 (word80 [0x98013002600200,(pn 11254 917698878289105556)]))),((BitVec.ofNat 152 (word80 [1,(pn 742129 573845209072009216)])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,(pn 95074 573053203386753816)]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(8,0,214,0,7)]
def g222A : List (List Nat) := [[]]
def g222D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g222L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g222D7)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,7,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 1=true := g222P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact (rfl : block g222 6 0 0 = true)
  · exact g222B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 8 := lower_forest (g:=g222) (i:=0) (hints:=302081600) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 8 [(222,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60acd,(pn 22115 916762154935500927)])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021d28,(pn 84298 666059860782628736)])),(BitVec.ofNat 152 (word80 [0x304b04500208221d28,(pn 8434 856565567704582547)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0ca,(pn 619239 545002442528653439)])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,(pn 5331 330883910476399882)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f6,(pn 496340 993793612031475584)])),(BitVec.ofNat 152 (word80 [0x8090098004e04820c6,(pn 453692 74965387193292332)]))),((BitVec.ofNat 152 (word80 [0x93711,(pn 767522 39355741982146560)])),(BitVec.ofNat 152 (word80 [0x2e02e011700803711,(pn 767422 951653200109516912)]))),((BitVec.ofNat 152 (word80 [0x4c917,(pn 596199 200807856667361280)])),(BitVec.ofNat 152 (word80 [0x30030021801008011,(pn 141671 319028953842196544)]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(64,0,171,0,8),(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(0,2,73,160,6),(0,32,73,130,6),(0,64,162,9,6),(128,0,107,0,6),(1,64,162,8,5),(2,32,73,128,5),(8,64,162,1,5),(34,0,201,0,5),(128,2,73,32,5),(128,32,73,2,5),(9,0,162,0,4),(9,64,162,0,4),(130,0,73,0,4),(130,32,73,0,4)]
def g235A : List (List Nat) := [[],[81],[48],[48,81]]
def g235D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x308bd87,(pn 1025732 682287536212886816)])
def g235D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x201100780402070,0x81e8820306901c1c00,(pn 795738 353194047181451377),(pn 837078 692200949659737677),(pn 935964 827230821740725313),(pn 831182 597909011073036372),(pn 703853 309536914377654629),(pn 340746 794727274972597573),(pn 154642 377689597038105876),(pn 618329 793157422475660370),(pn 74799 576933773592842312),(pn 179075 139198695541915936)])
def g235H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcb
def g235D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 613928 404391529673855509),(pn 94890 630102996991746373),(pn 325954 22004455805965832),(pn 311807 347468409349607168),(pn 456317 184739454296813603),(pn 123830 810992313724063872),(pn 831433 537125544480086822),(pn 38429 581981046165096135),(pn 624348 617787631903810562),(pn 945562 866508709204081681),(pn 534143 264623652237615745),(pn 1052035 217935728882014762),(pn 642566 412166036929218896),(pn 1205837 507683577512318034),(pn 75359 930802994649232771),(pn 386041 405262212702978008),(pn 703890 664828420383640565),(pn 704241 228050562227441839),(pn 421270 275306098116867340),(pn 1158516 691027573050544416)])
def g235H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x19c0000000d2800,(pn 630436 503049749846890313),0x34b0004022000,(pn 456889 727333174454779904),0x60000000000cae6a,(pn 606824 612088606464409600),0x207f3000912580001a])
def g235D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8e,(pn 88037 95669702878134561),(pn 769931 936966036274152261),(pn 690508 757708874348315010),(pn 342669 37419388210060864),(pn 161608 756156295776306305),(pn 492675 712682568353556031),(pn 1157273 389209143126113620)])
def g235H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9040,(pn 9534 741907891917160914),(pn 871600 154713418176981023),(pn 8643 322197149303199840),(pn 80340 183836770281349472),(pn 1079517 514424320356515992),(pn 226968 856222958583054414)])
def g235D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41882017f
def g235H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc100001e,(pn 608800 200507645545676826),(pn 74636 129441983296512001),(pn 264895 244908917744406688)])
def g235L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g235D5)
  | 6 => (14,3,5,0,0,9,0,g235D6)
  | 7 => (21,2,5,0,0,10,0,g235D7)
  | 8 => (8,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g235H6
  | 7 => lookupWord 5 53 2 10 4 2 g235H7
  | 8 => lookupWord 7 43 5 11 5 2 g235H8
  | 9 => lookupWord 3 29 4 9 3 2 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 2=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 14=true := (@block_merge g235 6 0 2 12 g235P6_0 g235P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_6 : block g235 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_15 : block g235 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 21=true := (@block_merge g235 7 0 6 15 g235P7_0 (@block_merge g235 7 6 9 6 g235P7_6 g235P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 8=true := (@block_merge g235 8 0 1 7 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=1048659) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff722c9,(pn 58709 645322705853988991)])),(BitVec.ofNat 152 (word80 [0x280280084044032080,(pn 56901 867236031780176517)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d52c,(pn 27610 596537889265303424)])),(BitVec.ofNat 152 (word80 [0x310b1050080823d12c,(pn 24944 629532065798869411)]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ca,(pn 694798 489592301245956223)])),(BitVec.ofNat 152 (word80 [0x400c0160809000504a,(pn 685334 738536976246539530)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,(pn 496341 65851206069403520)])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c2,(pn 189239 614904159015734812)]))),((BitVec.ofNat 152 (word80 [0x91711,(pn 767522 39355776073449472)])),(BitVec.ofNat 152 (word80 [0x26026011300880611,(pn 162977 317512210457831504)]))),((BitVec.ofNat 152 (word80 [0x4e917,(pn 596199 200807822576058368)])),(BitVec.ofNat 152 (word80 [0x38038021c01048915,(pn 312857 122189222648229984)]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(0,4,137,96,6),(0,32,73,132,6),(4,32,73,128,5),(36,0,201,0,5),(64,4,137,32,5),(68,0,169,0,5),(128,32,73,4,5),(160,0,77,0,5),(5,0,232,0,4),(9,0,228,0,4),(12,0,225,0,4),(33,0,204,0,4),(65,0,172,0,4),(72,0,165,0,4),(96,0,137,0,4),(129,0,108,0,4),(132,0,73,0,4),(132,32,73,0,4),(136,0,101,0,4)]
def g237A : List (List Nat) := [[],[82,118],[48],[48,82,118]]
def g237D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8185b54f033a,(pn 135602 417984566645348692),(pn 341129 103804030253902709),(pn 380519 761973027807756576)])
def g237D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x188100000081,0x5448200481c0040650,(pn 421489 655375648845205505),(pn 310496 68005327169159426),(pn 18910 236532977465131280),(pn 755665 708355248839797353),(pn 219890 134750708193937622),(pn 492059 371355185974113844),(pn 106447 252493262748254287),(pn 1016148 216582650745497919),(pn 437821 149444298970367727),(pn 539997 596005250349145069),(pn 913285 630318003525541815),(pn 26365 60739274436112092),(pn 100442 701267907666951508),(pn 1022762 321754460545285525),(pn 313155 812641145999054685),(pn 685344 960163117361257877),(pn 323528 129504155552015445),(pn 85214 655629726651880785),(pn 340877 66975995992954113),(pn 154642 418072461151376388),(pn 623143 203812217168517457),(pn 47129 967757410154140228),(pn 186451 819796105603121440)])
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 23611 945848764582857792),0x4810e8803020011801])
def g237D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14220,(pn 59788 511887056006435082),(pn 80651 257629688887548193),(pn 1098027 473312014663698472),(pn 380446 192530792358350988),(pn 670583 156888314458931779),(pn 28785 14008866423641172),(pn 19019 499515945886886472),(pn 266309 952066077677738211),(pn 911796 474962649091904785),(pn 159556 415683478302164230),(pn 694352 868989894329914496),(pn 909392 812500993643908116),(pn 610430 795765875516564160),(pn 142420 492864343675683278),(pn 262807 74186267463330489),(pn 347830 978298031976688132),(pn 738903 551002614008643839),(pn 1020424 303578891618440207),(pn 1159585 462772863390288192),(pn 1205763 648649997068490002),(pn 75364 542489047436621061),(pn 155825 146666265722535896),(pn 100571 474528044473126645),(pn 383706 100695006848827583),(pn 1025086 429930514386260491),(pn 1197508 491954345595473233)])
def g237H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x145245b468c,(pn 170005 194475913983655936),(pn 914228 778955601508040962),(pn 1040226 57633710068465664),0x2400000816062644,0x2c37030000c3c00000,(pn 20757 747116285785587820),(pn 151116 315171580074628393),(pn 461611 323700507822410694),(pn 906718 800190754787164160),0x1f1983a00fb08002,(pn 340010 386766614458826436),(pn 1196051 199523744441958400)])
def g237D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1628212a330,(pn 311741 472778667132226689),(pn 656965 228331597522553187),(pn 651982 453375091448799496),(pn 11308 296071383013920710),(pn 465758 972324676724828735),(pn 1001730 373374379720572176)])
def g237H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 12011 594687362597126144),0x6352ea124caae305e,(pn 628074 742382252508839936),0x12f0c2c80004640010,(pn 784733 788333946223746048),(pn 517304 647537056971542586),(pn 607239 145038744072606240),(pn 283349 652772226736327090),(pn 477180 413139976967578242)])
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g237H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x24400000000021,0x600000000000000,(pn 79099 638588066575817728),0x7340000340000,0x14800000030c0,2,(pn 453391 281726256698097666)])
def g237L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g237D5)
  | 6 => (33,3,5,0,0,9,0,g237D6)
  | 7 => (26,2,5,0,0,11,0,g237D7)
  | 8 => (7,1,5,0,0,9,0,g237D8)
  | 9 => (1,0,5,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 1 9 3 2 g237H6
  | 7 => lookupWord 11 79 6 12 6 2 g237H7
  | 8 => lookupWord 11 59 6 11 5 2 g237H8
  | 9 => lookupWord 3 59 1 9 3 2 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 5=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 33=true := (@block_merge g237 6 0 2 31 g237P6_0 g237P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_1 : block g237 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_12 : block g237 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 26=true := (@block_merge g237 7 0 1 25 g237P7_0 (@block_merge g237 7 1 11 14 g237P7_1 g237P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 7=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 1=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=2098435) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 10 [(237,[]),(245,[67]),(246,[16,115,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff83ffc1f432e,(pn 455288 287838145814986815)])),(BitVec.ofNat 152 (word80 [0x94028010808840030e,(pn 453369 232837090046914755)]))),((BitVec.ofNat 152 (word80 [0xfe003fffffffe0205a,(pn 784631 430517233669111744)])),(BitVec.ofNat 152 (word80 [0x18230420041002200a,(pn 19571 133344562880483913)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48c,(pn 688732 428843101328510975)])),(BitVec.ofNat 152 (word80 [0x200401410120001080,(pn 610808 626941239026008324)]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,(pn 497447 132186764730691584)])),(BitVec.ofNat 152 (word80 [0xc048098009c0848944,(pn 497361 732495648589702550)]))),((BitVec.ofNat 152 (word80 [0x9171,(pn 116617 739975006002872320)])),(BitVec.ofNat 152 (word80 [0x1702e022e01088071,(pn 116303 8417045935263288)]))),((BitVec.ofNat 152 (word80 [0x4e93,(pn 375428 531704902929350656)])),(BitVec.ofNat 152 (word80 [0x18030043002104411,(pn 11806 15429337331927072)]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,32,81,130,6),(0,64,162,17,6),(1,64,162,16,5),(2,32,81,128,5),(16,64,162,1,5),(33,0,210,0,5),(34,0,209,0,5),(80,0,163,0,5),(96,0,147,0,5),(128,32,81,2,5),(160,0,83,0,5),(3,0,240,0,4),(17,0,162,0,4),(17,64,162,0,4),(18,0,225,0,4),(81,0,162,0,4),(97,0,146,0,4),(98,0,145,0,4),(129,0,114,0,4),(130,0,81,0,4),(130,32,81,0,4),(162,0,81,0,4)]
def g243A : List (List Nat) := [[],[16,116,101]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20,(pn 305597 434943352184111442),(pn 361649 327121625142035290),(pn 400056 70268062062168400),(pn 322255 776467957448599909),(pn 399372 316522869173813520)])
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 113560 548027035103396616),(pn 359200 783253800096796292),(pn 302232 973469957848367360),0x180c2070408007060,(pn 303135 687990965162479920),(pn 380270 485104355349365808),(pn 152305 619868938597572652),(pn 585603 492438469257794319),(pn 130093 378201086191102562),(pn 616769 619892015831541826),(pn 49531 734729191778445057),(pn 804667 217256685847667841),(pn 86165 742283042211848640),(pn 425289 783701308806269591),(pn 979601 991557335032079955),(pn 1160657 775714464877029495),(pn 864290 582983447728005535),(pn 400037 624225217295058797),(pn 388568 344877635622673389),(pn 913285 55686356929380023),(pn 24960 803472700235438932),(pn 704011 7309870050704241),(pn 397011 545100613502369237),(pn 464049 175011043845330789),(pn 345043 874378633317375125),(pn 20134 454850958852186708),(pn 80555 968910333776790864),(pn 322002 593419890697589889),(pn 79674 705760105243382276),(pn 320985 498729617961405589),(pn 44768 784799673885478984),(pn 272912 850342707720440114)])
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe20000000000,0xe100000000000000,(pn 422173 626022797556842496),(pn 1156979 788531763425313019)])
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x526118484c31,(pn 763898 578521516685140541),(pn 123105 290122148882678535),(pn 80751 937871574983672968),(pn 643579 835018018739728432),(pn 173644 435232303432009992),(pn 359820 101927018765044807),(pn 369488 437355927273812109),(pn 637667 684571452612674729),(pn 234405 453799731074009172),(pn 228156 592912316444492097),(pn 704338 280427949483209476),(pn 387385 386425402918142540),(pn 551055 732414747779892611),(pn 154127 309507457344172771),(pn 920865 797085370539405634),(pn 76736 709903109261257580),(pn 951643 141284309076432965),(pn 37205 829585509341055269),(pn 144677 260259393325646208),0xffd8152ff58152ff54,(pn 1002026 384101497864785908),(pn 629568 880308903274160383),(pn 360413 635688123178717451),(pn 1197144 328636135982858546),(pn 905967 235458405087300757),(pn 72989 825860930607248789),(pn 155751 954165052844589016),(pn 684963 746892176937783156),(pn 949509 137253521674014951),(pn 704576 738692413321974575),(pn 251635 697148042936160544)])
def g243H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 10910 242648646584112900),(pn 888488 941539523193089840),(pn 337434 760393603596421120),0xc3781800882d23c8f9,(pn 714223 820889089592801984),(pn 777332 433990222274894970),(pn 24008 20628031768293616),(pn 113345 188378830357135553),(pn 28710 103388291574145031)])
def g243D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x38a2481218233,(pn 1077443 230909669720500512),(pn 57301 287946539612294944),(pn 389106 730937822516686065),(pn 704080 616022182635919524),(pn 161487 419626203503838732),(pn 798670 925454664096092688),(pn 1106807 241454332069351418),(pn 783862 323388762717923359),(pn 996712 820704908251880754)])
def g243H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1d00000000036b,0xca440f23800813248,0xe0323c000000012,(pn 358903 987004004815601664),(pn 28987 76728006134203586),0xd32001c31,(pn 727244 438361925423464506),(pn 226675 423144435390611911),0x5170000000059ff90,0x1c86c00000,0x410000000000000,0xc174a,(pn 41911 21253554052530176),(pn 27173 499113104692215823),(pn 453347 182356681015164944),(pn 604523 618339671751319198),0x1734c8000682000000,0xbb6e30000000040605])
def g243D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g243H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44,(pn 966314 242266191641968640),0,(pn 19774 967630861845004294),(pn 755578 637259144089829546),(pn 642258 198744118359052288),0xf10000000000000000,0,0x65c01c40000001e8d4])
def g243L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g243D5)
  | 6 => (38,3,5,0,0,10,0,g243D6)
  | 7 => (34,2,5,0,0,11,0,g243D7)
  | 8 => (11,1,5,0,0,9,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 37 0 8 3 1 g243H6
  | 7 => lookupWord 11 59 6 11 6 1 g243H7
  | 8 => lookupWord 13 131 3 11 6 1 g243H8
  | 9 => lookupWord 4 71 2 9 4 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 7=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_1 : block g243 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_5 : block g243 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 38=true := (@block_merge g243 6 0 1 37 g243P6_0 (@block_merge g243 6 1 4 33 g243P6_1 g243P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_6 : block g243 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_23 : block g243 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 34=true := (@block_merge g243 7 0 6 28 g243P7_0 (@block_merge g243 7 6 17 11 g243P7_6 g243P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : block g243 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 11=true := (@block_merge g243 8 0 2 9 g243P8_0 g243P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 1=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=1048644) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff7,(pn 245139 952236538031506431)])),(BitVec.ofNat 152 (word80 [0x40a102840400202003,(pn 161170 359561653090161829)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00a,(pn 615284 37014340493147136)])),(BitVec.ofNat 152 (word80 [0xac06b0128340a416a,(pn 605839 285464761034181731)]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffb,(pn 967172 204404603305820191)])),(BitVec.ofNat 152 (word80 [0x13004c01b0580c8248,(pn 664940 569330610287478850)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,(pn 98992 730484808479671264)])),(BitVec.ofNat 152 (word80 [0x9c027009c0604f0388,(pn 98102 672549266732689738)]))),((BitVec.ofNat 152 (word80 [9,(pn 108939 807271947313609728)])),(BitVec.ofNat 152 (word80 [0xe00b802e0081700401,(pn 90041 44680377923171228)]))),((BitVec.ofNat 152 (word80 [4,(pn 1100744 762900167011598336)])),(BitVec.ofNat 152 (word80 [0xc00300101800804,(pn 307253 743112276840825360)]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,7),(16,0,234,0,7),(0,64,162,24,6),(32,0,218,0,6),(64,0,186,0,6),(2,0,248,0,5),(96,0,154,0,5),(128,0,122,0,5),(18,0,232,0,4),(160,0,90,0,4)]
def g250A : List (List Nat) := [[]]
def g250D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x183b,(pn 1073686 952416607484595597),(pn 381693 875078012897887797),(pn 317259 996821359862797539),(pn 69482 447107046083749196),(pn 236029 164297490175181104)])
def g250D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x608e,(pn 41920 304759832014062080),(pn 455819 622522218939955235),(pn 613914 599213943551998094),(pn 117542 958956108582045764),(pn 46871 190380219407377081),(pn 380783 105641165028962496),(pn 340564 438240542144549823),(pn 422154 817110936386872587),(pn 1159605 58005489979576656),(pn 905971 847575724130506965),(pn 66063 361726248406218134),(pn 231088 497775507819003476),(pn 165504 13649909908705013),(pn 383414 950929670024016126),(pn 397030 276229657102177547),(pn 555105 240006739958793296)])
def g250H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc508a,(pn 20020 596135970249703464)])
def g250D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa2844c718a68,(pn 326481 177877664787607874),(pn 175253 443447577694605392),(pn 653000 626599382671828500),(pn 337728 478439059553375341),(pn 1127729 205692190617502718),(pn 793308 281631569377995295),(pn 930600 302434831194242388)])
def g250H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7480001f0668e309,(pn 524185 114181198565081237),(pn 184173 949738453402389635),(pn 97201 950502494102237312),(pn 33646 861190446223852816)])
def g250D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3420117f
def g250H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x20c000003140000,0x1d9624001,(pn 37779 68096845889667804),0x3c790000002])
def g250L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g250D5)
  | 6 => (27,2,4,0,0,9,0,g250D6)
  | 7 => (10,1,4,0,0,9,0,g250D7)
  | 8 => (1,0,4,0,0,0,0,g250D8)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 3 8 4 0 g250H6
  | 7 => lookupWord 6 41 4 9 5 0 g250H7
  | 8 => lookupWord 2 37 1 8 4 0 g250H8
  | _ => fun _ => none
def g250 : Forest := ⟨250,8,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P5_0 : block g250 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B5 : block g250 5 0 9=true := g250P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_0 : block g250 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_5 : block g250 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B6 : block g250 6 0 27=true := (@block_merge g250 6 0 5 22 g250P6_0 g250P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : block g250 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_2 : block g250 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B7 : block g250 7 0 10=true := (@block_merge g250 7 0 2 8 g250P7_0 g250P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_0 : block g250 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B8 : block g250 8 0 1=true := g250P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact g250B5
  · exact g250B6
  · exact g250B7
  · exact g250B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 9 := lower_forest (g:=g250) (i:=0) (hints:=319905856) (before_sound K243 V243) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K243 9 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V243 low250 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,(pn 950325 171204939862508543)])),(BitVec.ofNat 152 (word80 [0x581440548129029028,(pn 949568 782350028278900009)]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff801,(pn 1161800 166111769764330496)])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cd,(pn 1142910 696767341663980643)]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,(pn 272805 931230644453474304)])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,(pn 232665 762080860201389155)]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,(pn 314254 844265486358675487)])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,(pn 11985 774734352360609990)]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,(pn 165175 712361661168877536)])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa014c3205294a5294]))),((BitVec.ofNat 152 (word80 [1,(pn 742129 573845209072009216)])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,(pn 57298 523475316044489496)]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(8,0,244,0,7)]
def g252A : List (List Nat) := [[],[67],[82,118],[82,67,118]]
def g252D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g252L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g252D7)
  | _ => emptyPacking
def g252I (_ _ : Nat) : Option (Nat × Nat) := none
def g252 : Forest := ⟨252,7,fun i => g252Y[i]?.getD (0,0),g252C,g252A,g252L,g252I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P7_0 : block g252 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B7 : block g252 7 0 1=true := g252P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252T : checkedTables g252 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g252 0 0 0 = true)
  · exact (rfl : block g252 1 0 0 = true)
  · exact (rfl : block g252 2 0 0 = true)
  · exact (rfl : block g252 3 0 0 = true)
  · exact (rfl : block g252 4 0 0 = true)
  · exact (rfl : block g252 5 0 0 = true)
  · exact (rfl : block g252 6 0 0 = true)
  · exact g252B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 8 := lower_forest (g:=g252) (i:=0) (hints:=841377024) (before_sound K250 V250) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K250 8 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V250 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfee452b8e041c6843b,(pn 1086743 810246777646366719)])),(BitVec.ofNat 152 (word80 [0x282052284040468019,(pn 765623 543032068098376841)]))),((BitVec.ofNat 152 (word80 [0xb85b250ba3110715,(pn 130335 470252795105361920)])),(BitVec.ofNat 152 (word80 [0xccb81b2409a1010415,(pn 92116 358406252031168931)]))),((BitVec.ofNat 152 (word80 [0x172b56edcfa0714a1,0x480001fc07f0000000])),(BitVec.ofNat 152 (word80 [0x7072352eccca0304a1,0x48070e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xff5b28f8af85484d98,(pn 21767 229501621355413631)])),(BitVec.ofNat 152 (word80 [0x815a28d0ae81084d80,(pn 21768 755756463970159382)]))),((BitVec.ofNat 152 (word80 [0x10096918e422928e6,(pn 1099638 12292342900326272)])),(BitVec.ofNat 152 (word80 [0x100849186022808a2,(pn 341672 46232781677988372)]))),((BitVec.ofNat 152 (word80 [0x122c951708cbc338a,(pn 686892 185700720076390400)])),(BitVec.ofNat 152 (word80 [0x100c0513004bc330a,(pn 605428 531497094281047128)]))),((BitVec.ofNat 152 (word80 [0x9d24061534aaea41,(pn 14895 745839486103191552)])),(BitVec.ofNat 152 (word80 [0x8500001134802240,(pn 4747 785224703496958048)]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(8,0,119,0,9),(1,0,126,0,8),(2,0,125,0,8),(4,0,123,0,8),(16,0,111,0,8),(32,0,95,0,8),(0,2,77,48,7),(0,32,89,6,7),(9,0,118,0,7),(10,0,117,0,7),(12,0,115,0,7),(18,0,109,0,7),(36,0,91,0,7),(64,0,63,0,7),(0,4,27,96,6),(0,8,54,65,6),(2,32,89,4,6),(4,2,73,48,6),(4,32,89,2,6),(16,2,77,32,6),(16,32,73,6,6),(20,0,107,0,6),(34,0,93,0,6),(40,0,87,0,6),(1,8,54,64,5),(3,0,124,0,5),(5,0,122,0,5),(6,0,89,0,5),(6,32,89,0,5),(17,0,110,0,5),(24,0,103,0,5),(33,0,94,0,5),(48,0,77,0,5),(48,2,77,0,5),(64,4,27,32,5),(64,8,54,1,5),(68,0,59,0,5),(25,0,102,0,4),(65,0,54,0,4),(65,8,54,0,4),(96,4,27,0,4)]
def g127A : List (List Nat) := [[]]
def g127D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x30927ea5761d9,(pn 398172 149335735646114115)])
def g127D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd081d081,(pn 15385 107542439007092736),0xb081b08100007740,(pn 38314 284954414117356544),(pn 469949 883444699152254849),(pn 832688 915325215257986175),(pn 293345 800822616454356269),(pn 91064 910631422983144834),0xb4f4c0ecb2287c9f7,(pn 499857 499784225094314634),(pn 147119 523454600760552592),(pn 1117617 352417894890554638),(pn 281914 391485600333974912),(pn 1022726 323673980710076764),(pn 1176562 696928535605586542),(pn 505392 933803892437724796),(pn 693813 870458536447251509),(pn 619585 847227086518252061),(pn 398169 948018204782332609),(pn 708214 157573135692931259),(pn 190850 439464602984857844),(pn 959360 300970629976613079),(pn 474643 593459748001839717),(pn 685985 418013138274403250),(pn 640131 375509450666095392),(pn 279441 231310880092029248)])
def g127H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3e4
def g127D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x88e45612,0x4615048e45104e083c,0x1000000018507020b0,(pn 831763 994417690348445808),(pn 4782 327795357503809601),(pn 453372 740497095317718086),(pn 52095 197335303481292312),(pn 415885 322590229146654808),(pn 80319 159667150717214856),(pn 609240 886747261842392072),(pn 113374 848784710692257794),(pn 531268 573940203458270087),(pn 566712 80703458769929240),(pn 151249 685476831761006852),(pn 368492 164234655922511872),(pn 613317 383008001005258248),0x404106821a11050d06,(pn 123006 854928291124350094),(pn 19498 641996478660313347),(pn 133038 355192459084570376),(pn 727928 85996002066239236),(pn 90066 536191312198365513),(pn 464876 537257432214419979),(pn 10091 538685008843900803),(pn 919690 737817266856026352),(pn 615699 145499048929659421),(pn 19609 936079874962810922),0xc1e0c0546112138101,(pn 95851 447402141497672099),(pn 1105912 470679519941795833),(pn 1093741 580915244398557437),(pn 674871 144581724078889861),(pn 417035 97735194846593527),(pn 1159321 936935501438711671),(pn 559735 352712694689371248),(pn 410503 274565121200252614),(pn 441041 348402678348195322),(pn 447256 540350102821506647),(pn 1159051 986031811233402900),(pn 1059231 984763298453738621),(pn 334777 727512521921010240),(pn 850122 808927897826966435),(pn 808579 840066091807097555),(pn 203699 407551506373809694),(pn 914997 237444991457234976),(pn 1147766 832255762765508608),(pn 754841 760932154739900772),(pn 896514 777498192900905283),(pn 896514 201037698295501123),(pn 1179856 457974054834770243),(pn 1179854 152131045610574147),(pn 1180137 752806779848577347),(pn 1179547 456996163462220099),(pn 1047616 953618999920150851),(pn 1179804 13556393522348355),(pn 755431 483094182497472866),(pn 1179821 833207917484818786),(pn 1047558 152404164036385090),(pn 901824 823198941994387745),(pn 904187 144195471386677088),(pn 1047557 578756095622894944),(pn 901827 132452846193447264),(pn 905366 600346004468617568),(pn 904187 143632401226124640),(pn 1047597 355111087122271584),(pn 1047596 202189582465092960),(pn 1047630 789834720717688160),(pn 1047615 801855023392869728),(pn 1047614 648933724910898528),(pn 1179803 386461644752013664),(pn 1048203 214235858632018272),(pn 1113708 701319910328174944),(pn 887662 352357969104323936),(pn 1048203 195095430306563424),(pn 1048203 177080998516262240),(pn 1048203 123037699374176576),(pn 887072 350372171266775360),(pn 1048221 665448355126696256),(pn 897105 937996389040904512),(pn 1188708 589283127123578176),(pn 1179783 839678177688258880),(pn 887072 616084549281876288),(pn 1179783 821664173204799808),(pn 1198156 776509394611722528),(pn 754848 680638352829254944),(pn 1047616 324202469087579424),(pn 1198153 285058732264622368),(pn 1052926 715555598187202848),(pn 1056468 488165893733712160),(pn 1198156 776474612287766816),(pn 745990 204391754518092099),(pn 877627 617409706355972419),(pn 895921 887614516999608643),(pn 891791 834554569339296067),(pn 1104875 55000374399570243),(pn 878212 993037609044610914),(pn 745990 204389606495162208),(pn 1104263 970042745501633888),(pn 745699 616939542838578528),(pn 1104263 969479796083513664),(pn 1029317 154116396164386112),(pn 1179263 819162629685215552),(pn 1178603 227791253896026400)]) else (word80 [0x1e000846080000c,(pn 227902 641838456024837140),0x84722d0a0025088e45,(pn 68562 18104899605162060),(pn 179606 763704744205866032)]))
def g127H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe78000000a2,(pn 664502 453671418272995840),(pn 125733 36919384300348201),(pn 590554 195246497461698565),(pn 680150 371871843040624640),(pn 10505 764797296756660837)])
def g127D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x43220890385430d0,(pn 321430 608418268015436324),(pn 61575 556008294709551201),(pn 47534 973883588418961415),(pn 189227 22434682054115538),(pn 533934 116708051686031642),(pn 907415 304880557559920641),(pn 387844 28213488236430976),(pn 314057 45655352075898980),(pn 415599 532855397592416295),(pn 137251 285753360865677536),(pn 344797 540382291750565634),(pn 228156 275302649062056195),(pn 647022 290240833105167106),(pn 164106 931439103954193964),(pn 266534 730909115010522120),(pn 313753 754893793026786627),(pn 917569 15363904208705813),(pn 61501 663747287001862145),(pn 322674 255326879073546387),(pn 43774 854267636268075520),(pn 569567 155547354872004675),(pn 535415 599103870079798300),(pn 113632 742603762908033120),(pn 378381 76986392071348640),(pn 531428 873173029133550594),(pn 310498 199360153533810432),(pn 397721 76391308151587589),(pn 342445 862809995844458552),(pn 132596 134306142807943260),(pn 41114 460302367755681984),(pn 831294 525859567734128909),(pn 321676 492227771541819532),(pn 661147 610847363475788032),(pn 1134263 328113034390831552),(pn 321363 78320689305161836),(pn 435864 3705853047857569),(pn 457487 364303155584501252),(pn 13000 722075776411371264),(pn 388126 476013830354775041),(pn 991879 143059301299478784),(pn 909941 792675505958360092),(pn 113743 779977375787307556),(pn 510049 192838239753765658),(pn 33167 607402446660308520),(pn 246136 563830471202970716),(pn 22175 404817996616585955),(pn 34347 963579377290588244),(pn 643502 569222021801149248),(pn 386941 265975530915955585),(pn 31885 998832615083231452),(pn 80889 837808045086814243),(pn 25974 514240821540881693),(pn 229114 384674156039987440),(pn 310655 862125738838510465),(pn 94458 139513864872294567),(pn 324702 61921693172637957),(pn 22580 201857084606413811),(pn 1011147 103048256618352718),(pn 512122 222786043254860598),(pn 612400 581951667928880324),(pn 330550 558133270160585396),(pn 100731 239696688169372028),(pn 348020 602098642851405984),(pn 1200802 639585304406944579),(pn 260189 73155024684665865),(pn 1002483 852362245707381787),(pn 230437 155984753346322502),(pn 311603 387291382913876095),(pn 15349 150354361192300539),(pn 693191 702805231672799871),(pn 1015411 691694213586834272),(pn 1207343 653271343661574954),(pn 916127 358498902260088789),(pn 328278 165541933571203327),(pn 794741 650668579828992705),(pn 1205759 181084327380248421),(pn 18866 58507555826630636),(pn 349602 505184944484139391),(pn 435460 469586748075617682),(pn 1202883 112560371441856011),(pn 188294 442354770631456605),(pn 700085 709544860821032942),(pn 874384 855805145381734941),(pn 1196914 160656546197888054),(pn 207763 999079355032207288),(pn 209406 707244917878036461),(pn 464280 331220872381339167),(pn 1051991 360334697496228460),(pn 148552 738121846924640116),(pn 416600 917655863109750718),(pn 1089399 984947777836231703),(pn 1198767 482261810249037392),(pn 292401 826721424741495488),(pn 757348 904463401253869565),(pn 987578 702857888617154623),(pn 505630 9542798690894480),(pn 602507 880038803694933447),(pn 480462 620268310333570283),(pn 163067 440119358058901719),(pn 1167983 770965263382809920)])
def g127H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x60985ae828600,0xa951b0007ac79e,(pn 1108575 531853755919672811),(pn 131958 872359615057625088),0x4ee5c00032a,(pn 604462 909807314589326136),(pn 151115 727451828690878470),(pn 411677 785744243941083136),(pn 9783 68236379648006578),(pn 982737 657616904389736068),(pn 1038920 627300047249327232),(pn 22634 162049643563712512),(pn 96808 512898827731210240),(pn 782732 244753896752307596),(pn 680021 506321445443862528),(pn 39439 138829592855297525),(pn 684234 557526828475236353),(pn 437530 716501679705953216),0x672b34f9a4b3b00,(pn 76824 988112172476393472),(pn 382373 199803877505474198),(pn 306953 821386527109589952),(pn 23105 938217160396692449),(pn 738279 772347324915499174),0x6d8e6946a974e0004,(pn 278084 667557684327743516),(pn 1021556 547515912723388453),(pn 100350 522001044552032292)])
def g127D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4046c028,(pn 229051 158725901011699850),(pn 309776 202698668531462656),(pn 838243 185419594051928471),0x68c1920e1a460cb803,(pn 39037 204949272070329356),(pn 387296 312490446321436736),(pn 105155 97596077001958465),(pn 455828 282065559096564012),(pn 56698 665658602813493971),(pn 680980 869482481905363264),(pn 241431 787181145417894784),(pn 229065 995625244553437194),(pn 309760 923803532966177802),(pn 994743 401242799176684813),(pn 24594 833527402947147359),(pn 1159783 649772929350455293),(pn 661083 100878649377682823),(pn 1196271 301529363513967613),(pn 382499 20939780084194627)])
def g127H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x456737,(pn 68953 103470226816630799),(pn 283341 989926761847935488),(pn 127344 323507938834513920),(pn 382034 794999583917216326),(pn 812330 46417121484742709),(pn 990682 986261617283265061),0x1af620a00b1aeda6,(pn 1079657 18947932231008256),(pn 9179 982106245096538208),(pn 425908 81053023768412160),0x3468000008f0,0x20c20800000000e,(pn 518796 231239403962469153),(pn 1057862 161092842325977628),(pn 479921 508359710061002766),(pn 245712 937300998693609758),(pn 453352 234020302998709077),(pn 158972 888527187791106192),(pn 321130 365477325149127683)])
def g127D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9858027f
def g127H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 10625 324587034375151620),(pn 340010 386842480757704309),(pn 831136 500985057557610496),(pn 611003 973943838046701568),0xab,(pn 797950 815811663597162498)])
def g127L : Nat → Packing
  | 5 => (2,5,6,0,0,3,0,g127D5)
  | 6 => (28,4,6,0,0,9,0,g127D6)
  | 7 => (114,3,6,0,0,12,0,g127D7)
  | 8 => (86,2,6,0,0,13,0,g127D8)
  | 9 => (19,1,6,0,0,10,0,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 1 0 g127H6
  | 7 => lookupWord 7 47 3 9 5 0 g127H7
  | 8 => lookupWord 28 191 4 11 7 0 g127H8
  | 9 => lookupWord 21 127 7 11 7 0 g127H9
  | 10 => lookupWord 4 53 2 9 5 0 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 2=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_4 : block g127 6 4 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 28=true := (@block_merge g127 6 0 4 24 g127P6_0 g127P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_26 : block g127 7 26 88=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 114=true := (@block_merge g127 7 0 26 88 g127P7_0 g127P7_26)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_9 : block g127 8 9 52=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_61 : block g127 8 61 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 86=true := (@block_merge g127 8 0 9 77 g127P8_0 (@block_merge g127 8 9 52 25 g127P8_9 g127P8_61))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_1 : block g127 9 1 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 19=true := (@block_merge g127 9 0 1 18 g127P9_0 g127P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1049923) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff9914845dc0c3208,(pn 415442 582048594278223871)])),(BitVec.ofNat 152 (word80 [0xa081484148081200,(pn 93879 104058693815407177)]))),((BitVec.ofNat 152 (word80 [0x2e1698323522625,(pn 1181786 47400513340698624)])),(BitVec.ofNat 152 (word80 [0x330e0680303102205,(pn 1181772 267239152743624899)]))),((BitVec.ofNat 152 (word80 [0x5cac5a9599d85d5,(pn 364803 963723185756569600)])),(BitVec.ofNat 152 (word80 [0x15c1c8c1a9599d8595,(pn 364803 524514992468425191)]))),((BitVec.ofNat 152 (word80 [0xfffd6ca45bd5527d10,(pn 378310 439426730842128447)])),(BitVec.ofNat 152 (word80 [0xa60568241a95526d10,(pn 302752 978031249133757846)]))),((BitVec.ofNat 152 (word80 [0x402593eb1ca049b,(pn 624360 46866743085498304)])),(BitVec.ofNat 152 (word80 [0x380402111cb0c2049a,(pn 19267 990191816485979412)]))),((BitVec.ofNat 152 (word80 [0x48b2640ac338afe,(pn 153559 903027197726425088)])),(BitVec.ofNat 152 (word80 [0xc004030640a402086a,0x847618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x27492b802a4c902,(pn 55618 86303737831227392)])),(BitVec.ofNat 152 (word80 [0x21480a000248000,0x20820820820820820]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[]]
def g191D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact (rfl : block g191 6 0 0 = true)
  · exact (rfl : block g191 7 0 0 = true)
  · exact (rfl : block g191 8 0 0 = true)
  · exact (rfl : block g191 9 0 0 = true)
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1049923) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe647a826c1076899,(pn 86330 762542037648281599)])),(BitVec.ofNat 152 (word80 [0x28242a00641036088,(pn 75559 34947760273231937)]))),((BitVec.ofNat 152 (word80 [0x1a1675100a05e7f6,(pn 401991 464587202081845248)])),(BitVec.ofNat 152 (word80 [0xcca167010080563f6,(pn 401414 34484225291104971)]))),((BitVec.ofNat 152 (word80 [0xf7a344bcdb08551,(pn 378305 827463636541505536)])),(BitVec.ofNat 152 (word80 [0x570f7a344bcdb08551,(pn 75732 375780960845526487)]))),((BitVec.ofNat 152 (word80 [0xffe43932daaacf8214,(pn 656410 76026054427803711)])),(BitVec.ofNat 152 (word80 [0x98043912588a4c8214,(pn 47230 692159772151013766)]))),((BitVec.ofNat 152 (word80 [0x18b84719f40b063,(pn 191918 772425698895462336)])),(BitVec.ofNat 152 (word80 [0xe00089046186408001,(pn 189489 640012528313450756)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x22c1b017070590e,(pn 1081790 859463020991217664)])),(BitVec.ofNat 152 (word80 [0x4090030001802,(pn 930721 980880632290642472)]))),((BitVec.ofNat 152 (word80 [0x19d049cc14980680,(pn 740526 94090598193561600)])),(BitVec.ofNat 152 (word80 [0x1100098010900400,(pn 608282 264246956926897200)]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,9),(8,0,215,0,9),(0,4,155,64,8),(1,0,222,0,8),(2,0,221,0,8),(16,0,207,0,8),(128,0,95,0,8),(0,2,77,144,7),(9,0,214,0,7),(12,0,211,0,7),(18,0,205,0,7),(20,0,203,0,7),(64,0,155,0,7),(64,4,155,0,7),(1,4,154,64,6),(5,0,218,0,6),(8,4,147,64,6),(16,2,77,128,6),(16,4,139,64,6),(128,2,77,16,6),(130,0,93,0,6),(136,0,87,0,6),(9,4,146,64,5),(13,0,210,0,5),(17,0,206,0,5),(24,0,199,0,5),(65,0,154,0,5),(65,4,154,0,5),(66,4,153,0,5),(72,0,147,0,5),(72,4,147,0,5),(80,0,139,0,5),(80,4,139,0,5),(129,0,94,0,5),(140,0,83,0,5),(144,0,77,0,5),(144,2,77,0,5),(28,0,195,0,4),(73,0,146,0,4),(137,0,86,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[]]
def g223D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa008500,(pn 304609 473415262089818678),(pn 753334 553304910714766945),(pn 320319 931543867881754450),(pn 378592 448053695990022350),(pn 181286 553093422670690822),(pn 459320 797730359297195337),(pn 303489 833146087102546192)])
def g223D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x81290129,(pn 114526 610581677560311872),(pn 1133386 476168959450152961),(pn 306954 38685638812041992),0x2c4040174133411401,(pn 8272 446571317991427345),(pn 908820 497067137046984752),(pn 605223 275204988594097679),(pn 530422 318591512498585776),(pn 690663 898263894795442794),(pn 1120707 198952890389062436),(pn 473054 180166079984146394),(pn 1149258 358139552901673173),(pn 1032876 294142359632166567),(pn 97445 812930252395472102),(pn 731138 601962336417850292),(pn 484265 180279436470977567),(pn 849370 733450126265116905),(pn 136718 362346719288608280),(pn 914220 850878181043153829),(pn 399751 609298631286927141),(pn 626019 124153539216552195),(pn 151188 684234317645858552),(pn 992174 500696917697244229),(pn 343073 924956333632702998),(pn 12548 976017296146302071),(pn 1080685 50502917657136818),(pn 795490 443613898755963762),(pn 57752 910129185410799956),(pn 280073 91375447692400909),(pn 1026604 32576637824174623),(pn 639241 243424437359641290),(pn 841327 435250329679367907),(pn 1145979 955808561564185941),(pn 95545 976152769646027223),(pn 479713 655254669111503498),(pn 145864 834285651480607794),(pn 947870 414865480879113487),(pn 471953 796018704039662932),(pn 434830 949510496963954494),(pn 420549 260061731792667560),(pn 578885 591102479381228668),(pn 240409 636009229959369789),(pn 357455 308237406243274265),(pn 473730 53999113179635365),(pn 740682 747660490623347136),(pn 191156 3208086810481388),(pn 508300 78526192623376663),(pn 62778 427760825168655925),(pn 685985 716137422496492422),(pn 779743 382817981686561577),(pn 319505 319040270793510240),(pn 1081341 997120522481931861),(pn 95434 501715587808800871),(pn 274441 601825161165811786),(pn 126354 259020957351427378),(pn 948017 983865238957866313),(pn 457855 907791342996151700),(pn 1061783 438598909434431144),(pn 540523 712838043484205740),(pn 652177 823300269140825146),(pn 278262 948774947747616773),(pn 62884 431123691961192927),(pn 695992 651410729423614598),(pn 757173 584663991231893450),(pn 825419 920263760156377936),(pn 204153 411794994293368215),(pn 401645 619076879496620060),(pn 743594 690439289192229674),(pn 635757 107961549766790854),(pn 883973 315734829179732291),(pn 378807 568361376083994213),(pn 566777 166670616495956392),(pn 139558 144468261350240778),(pn 126998 935603724279911437),(pn 938794 616204021026288911),(pn 388714 51223685375330147),(pn 441914 617162148259989417),(pn 189404 927391447417837424),(pn 808165 738063212399843348),(pn 71364 880332436223400293),(pn 63167 431857547059661319),(pn 785560 664277110317945478),(pn 831876 580155446958294001),(pn 190879 35558926174343768),(pn 94730 133875813985155220),(pn 289417 907878223183751690),(pn 35682 440447418206637234),(pn 796459 512093318604719363),(pn 543972 152374503456265539),(pn 397048 839909368108581244),(pn 873750 300173419737428520),(pn 495989 416794749973610140),(pn 618826 123602432833688628),(pn 318625 64798885943135821),(pn 629699 285123244795494945),(pn 1176336 551461714179328673),(pn 793514 796652869781098684),(pn 436874 573630338415153397),(pn 174791 53984299143425558),(pn 81531 479102850855365122),(pn 160414 342826679388291881),(pn 798818 420074430897389840)]) else (word80 [0x4404000,(pn 321194 707868005213149456),(pn 5018 670810675401560192),(pn 533658 613784019279290384),(pn 4727 50328050656284715),(pn 75853 83759056643690497),(pn 455048 913777596982951936),(pn 680326 302255617119751184),(pn 472579 71198780729999715),(pn 511454 442570463139530795),(pn 38240 677800832179143684),(pn 9739 955220312531976265),(pn 10045 568906772110312448),0x291c4090f040040104]))
def g223H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x930,0xd25660007f00022162])
def g223D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x4f89bc47,(pn 1066204 155680569980203052),(pn 607488 112744319662145317),(pn 1162579 562887712991409047),(pn 725995 382508195571016604),(pn 1118709 72008154354421872),(pn 54161 621861501100219819),(pn 1120518 176012463491565141),(pn 840683 559191614073477156),(pn 897062 475221689941908066),(pn 947239 203929337245813546),(pn 223440 402913467536038822),(pn 761265 533565467771452052),(pn 1079561 451859807020898852),(pn 381598 887669247734368122),(pn 276291 247360292669233548),(pn 940452 351907139486242274),(pn 685107 216996228166911047),(pn 973900 592580523785913110),(pn 607548 480762850052621364),(pn 1064839 65094193798721608),(pn 7526 730949922013434213),(pn 754846 370367472865231205),(pn 830989 329370847824435540),(pn 868768 261216341118015811),(pn 896512 759885559842068803),(pn 897102 479235165708997955),(pn 896512 758759659936273731),(pn 897102 478109266339534147),(pn 896520 234735246976062787),(pn 1160952 5188915739071811),(pn 897102 460095125509214531),(pn 1179841 469994494935257411),(pn 1179842 604901613380684099),(pn 896519 670659324928966979),(pn 896518 517737820321071427),(pn 1179822 460300467232424259),(pn 897109 390008931867541827),(pn 1047616 374906190675951939),(pn 1048205 517795181660062019),(pn 1179821 883839714928476483),(pn 1194023 570933474985886019),(pn 1194618 428343798959771474),(pn 1194611 510814771312398162),(pn 1052317 989381423779105121),(pn 754846 375991474841310560),(pn 830993 941052467674206560),(pn 981484 225476752387182944),(pn 830405 931945128969458016),(pn 1047931 71843475278597472),(pn 1123192 634742706160340320),(pn 1123154 588333173855554912),(pn 1179803 386462044181302624),(pn 1197562 989318741766785376),(pn 1052927 274072260630890848),(pn 1193951 479593926813669712),(pn 1048221 665465776591967568),(pn 981503 230649690230198608),(pn 904187 161629044341297488),(pn 1019282 144498205968371024),(pn 1047616 324255228500446544),(pn 1160933 520178538814442832),(pn 1197562 989301016437840192),(pn 755437 249353172002919744),(pn 755438 401148776703432000),(pn 981503 231757929248298304),(pn 1113709 892486680849764672),(pn 1151488 806335506326818112),(pn 1179861 32502077254077760),(pn 1180450 175390931368611136),(pn 1179841 432836498919853376),(pn 1052338 743637823021500736),(pn 901243 156283408272673088),(pn 1052339 284069778306451776),(pn 905372 360414827776409920),(pn 1188067 560422986486219072),(pn 1202822 649838674351833408),(pn 1169197 676142674812682560),(pn 1194618 427725873424960800),(pn 1196978 458028213601111312),(pn 1204652 336213981589209360),(pn 752480 576565008975368515),(pn 1104265 159524231504286019),(pn 1142652 815927463055282499),(pn 1175099 519608383686953283),(pn 899464 795711482587582290),(pn 1175099 467270667531305810),(pn 1104263 969479796083513680),(pn 1142024 454581345033981248),(pn 1028726 858306037994556736),(pn 1028725 705384666008456512),(pn 1179263 819162686558947648),(pn 750127 428831424484821312),(pn 1175062 13627395390392640),(pn 1112528 143441124348232000),(pn 1150288 610545609290891584),(pn 899464 795093557321207072),(pn 1175099 466652864420842768),(pn 1191662 336970200846256400),(pn 1191590 296264870867599632),(pn 1200461 466544718469202192),(pn 1199926 474937797292917008),(pn 1024002 186563033926795536)]) else (word80 [0x100400181c08,(pn 9445 421418365216624132),(pn 4722 692573953784842242),(pn 9456 559981866114418816),(pn 152675 505309540405182792),(pn 613944 582460483050678337),(pn 992158 742530337948114056),(pn 317008 451247334400037123),(pn 929531 462093315684966368),(pn 47318 280957263005458833),(pn 17492 558315660863177920),(pn 59178 670644389248062000),(pn 709296 932003648723161088),(pn 1100542 281074681696126272),(pn 59200 402576621627852868),(pn 4876 898709106554592257),(pn 39921 107381287884966429),(pn 49589 899025629118988546),(pn 648889 690864854646156388),(pn 99247 133641981202956818),(pn 40436 636625050944962578),0xc20100400189380100,(pn 170033 161905567950720647),(pn 311789 465398733397069825),(pn 647997 816007277714367040),(pn 1172664 296943279424152864),(pn 199526 72953760492044289),(pn 1073162 106935847275241635),(pn 493930 86898925708521633),(pn 757063 944722032512729188),(pn 231138 647339476103400841),(pn 604792 880675319080648832),(pn 4731 590138307786311426),0x8020014480c4270040,(pn 236120 711160686586103312),(pn 694263 31726586513069410),(pn 42803 509611130049825798),(pn 492974 313538710540402200),(pn 1058755 781146843543574666),(pn 304618 741151747513024544),(pn 682571 77701003470963712),(pn 295370 712907382180810816),(pn 169281 746970484161581318),(pn 155939 608743477717775172),(pn 62282 552668630595037280),(pn 595222 175197722501452294),(pn 321356 312742751797112844),(pn 205446 942264534136932770),(pn 314097 35115905425630485),(pn 365135 575552794749456712),(pn 1190553 229283680052660748),(pn 615286 976280371832917080),(pn 531886 358679479370350989),(pn 57618 972576664183470082),(pn 305782 564628351573561868),(pn 119284 724845589188150304),(pn 35445 663777102899605612),(pn 988614 643211938358111618),(pn 654758 391558713741746434),(pn 343006 183215843689989030),(pn 38053 368611347526851601),(pn 153506 471507029573144512),(pn 77628 754653303070917740),(pn 444143 916512807610238673),(pn 386691 663041613315906097),(pn 35445 640003374970624434),(pn 307131 90978366542450328),(pn 774768 133244857790677240),(pn 211494 270576632479113236),(pn 149964 117412817401294025),(pn 154001 352698439620899009),(pn 1090571 834697681691071150),(pn 138837 912066878210323100),(pn 400084 835881217213811200),(pn 979272 337154273805329913),(pn 213268 881857339550175452),(pn 619289 848553091658559281)]))
def g223H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1f5dc,(pn 780579 772596690817646592),0x426000002b43a5000,(pn 67293 722416889974489098),(pn 415569 936574812512059461),(pn 248994 162109539335940096),0x1e7eb7793764002,(pn 14368 832007318272063118),(pn 146916 427987774762647552),0x240d8ccc20020723d,0xd8feb02b8c4000003,(pn 731967 656413642791514531),(pn 716848 696645598213808365),(pn 917398 831405279196744062),(pn 727114 479108394702331407),(pn 991697 669488311300784153),(pn 963989 958576908459563381),(pn 347684 238116890545300175),(pn 1048378 879803085094395325),(pn 546945 961785488205414476),(pn 755578 657856964575238434),(pn 354802 470861028281047718),(pn 40585 557729492331767345),(pn 268099 411918157098532885),(pn 161076 969958484948032064),(pn 302454 78120417233469441)])
def g223D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1189c6a20,(pn 1177160 590550594232850435),(pn 94752 646866618282029192),(pn 340621 505533944478779536),(pn 20985 667011401008515650),(pn 229210 38799125476409960),(pn 776981 695004354893939040),(pn 1058494 66801494460825735),(pn 615388 85277479693525189),(pn 18307 337425645604180998),(pn 932093 230541665184548484),(pn 16533 484981801297947734),(pn 5329 436055834416751395),(pn 664140 545143140023997698),(pn 238617 901392031911653904),(pn 66814 258126738275535080),(pn 985657 382387309814531634),(pn 54355 138780675800836134),(pn 28526 234888934920815224),(pn 228622 318546270045637187),(pn 611602 252421820011781633),(pn 154967 687899360929612737),(pn 1060882 774427810936032266),(pn 44881 440477637820300838),(pn 10441 494705199797985804),(pn 924460 941077911310275096),(pn 26015 205430079414081636),(pn 406381 853291054993774633),(pn 769811 420877101664993857),(pn 1059592 983430165766228008),(pn 935034 763966467779641713),(pn 416336 313446491694114314),(pn 312581 127113024398494280),(pn 917283 231577456719222832),(pn 536749 758714394867731085),(pn 611602 309966054771525784),(pn 653620 607268618756071462),(pn 1061380 847702880779642644),(pn 728205 833706643666876528),(pn 911273 197149889990418912),(pn 85224 210259199242809544),(pn 369342 750652674347254168),(pn 194855 327495926573665684),(pn 120459 267886322736824404),(pn 117914 13661465239830982),(pn 779402 825260282843917828),(pn 118662 182856124052725953),(pn 786606 655837587940460592),(pn 907255 697310417681502812),(pn 877306 112319242825095841),(pn 776124 388604799545231731),(pn 1014153 878846473015214419),(pn 874630 672234442697330993),(pn 53429 335423727310878940),(pn 969280 441759875014372426),(pn 494018 317049483139139520),(pn 558548 416838407779862605),(pn 927654 496708492358854722),(pn 189443 558057439436128257),(pn 1205920 612613649122449237),(pn 623328 897383174271729580),(pn 654195 143052959679676927),(pn 440730 760864513507411350),(pn 1207600 877481302389927626),(pn 790948 347460066048735069),(pn 700086 141327474561454062),(pn 843689 473666492687845919),(pn 1121060 860953904227016022),(pn 66017 55574839966006962),(pn 208364 408816870194087917),(pn 313302 954397830640915726),(pn 1183702 814815290191231784),(pn 113149 536127397195545973),(pn 378931 513265680945516506),(pn 1079660 185404989764544543),(pn 1082625 646030831953469768),(pn 300666 805874518947523274),(pn 644590 722277090617597885),(pn 345041 659136024261185788),(pn 1108031 925806844117445033),(pn 589488 570233118940624141),(pn 305735 77811619413638970),(pn 708981 391843282448058494),(pn 397347 765205959115604240)])
def g223H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 1075931 242168265097609216),(pn 43219 857569675000938496),0x8cb5a000f97f2d,(pn 348570 182915984298320384),(pn 62405 337554314402004992),0x895052a77519670d25,(pn 321883 331275406562561671),(pn 302231 454904501254750210),(pn 608651 125615161773389203),(pn 569065 382708234464213664),(pn 250287 238092506976757081),(pn 46096 495055650854375522),(pn 231586 231843635790348528),(pn 1007297 237540886673425572),(pn 760092 325094129789092360),0x75e10a57d33328343,(pn 610903 779400649483616265),(pn 51946 339536836082929818),(pn 348283 10723365193340416),(pn 14388 460511045379024703),(pn 478886 628233354982530089),(pn 609850 959791398184812577),(pn 906697 386399822451374000),0x17a79f85100088e000,(pn 1134548 593650665355477143),(pn 950400 930329536598774607),(pn 368457 360236351972182923),(pn 720591 455867302365364278),(pn 226686 298687133727086878),(pn 711965 922708357192641818),(pn 235755 91522823763426887),(pn 161825 302375621371085058),(pn 973250 951442279270711572),(pn 340774 827772896311283856),(pn 75631 650728803867853187)])
def g223D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa0340864e5411a44d,(pn 99428 816518417068726440),(pn 189034 958894151194250762),(pn 19208 18494733386150560),(pn 16569 819864547593448560),(pn 331280 899456220262695811),0x513180cd8d0e00a1a3,(pn 319147 434666531155620952),(pn 990022 993181940088079232),(pn 190676 166378371467120275),(pn 713710 857378297173788898),(pn 218567 508218020915208181),(pn 698861 23943810669868419),(pn 1196252 856966561951715311),(pn 391870 2676546176021776)])
def g223H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe840000000000,0x1c1c00000000,0,0x188e2a0000000000,(pn 58181 30808479925796864),0,(pn 968085 128988277268807680),0,0x35c00000000,0,0,(pn 19424 421509616157851648),1,(pn 910236 139573124115070990),(pn 302231 454903657293676544),(pn 30326 447257178502856704),0,0x1048000000000,(pn 7683 68906700028248064),0x80a00000000,0x3d1f,(pn 47223 664828696452136993),(pn 928976 203090564306960384),0xc4000000,0,0x14818,(pn 1078581 125989797482987520),0x167000000000000,0,(pn 6428 690309687778738176),0,0x87c003160,0x6800000000,(pn 12525 339226048786026496),0,0,0x8760000000,0x7c0f2c00000,0,0,0,0x5280000000000000,0x186800000000000,0x3260000,0xd88002de00000000,(pn 28186 667799193399066624),0x14ac0000b0,(pn 7686 32275254838034432),0,0x20d800000000,0x695000000000000000,(pn 9656 870522587177287680),(pn 66777 213546830830002176),0,0xac0000000000000,0,0,0x1888000000,0xd780,0x1e0400,0,0x668000000000000,0,0x2c300061800000,0,0,0x414f6400,0x2260000014f000000,2,(pn 292786 721937918003249152),0x15e80000000000,0x41e003,(pn 1043642 992714191592226816),0,0xb5a00000000,0,0x24c0000012811])
def g223D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x68c19408037f
def g223H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3d40b66b,(pn 681104 749220034112201792),0x398011fa0ab4ce])
def g223L : Nat → Packing
  | 5 => (8,5,6,0,0,7,0,g223D5)
  | 6 => (121,4,6,0,0,11,0,g223D6)
  | 7 => (163,3,6,0,0,13,0,g223D7)
  | 8 => (69,2,6,0,0,12,0,g223D8)
  | 9 => (15,1,6,0,0,10,0,g223D9)
  | 10 => (1,0,6,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 2 7 3 0 g223H6
  | 7 => lookupWord 30 167 6 11 7 0 g223H7
  | 8 => lookupWord 40 211 7 12 8 0 g223H8
  | 9 => lookupWord 17 577 1 11 7 0 g223H9
  | 10 => lookupWord 3 23 2 8 4 0 g223H10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P5_0 : block g223 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B5 : block g223 5 0 8=true := g223P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_8 : block g223 6 8 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_104 : block g223 6 104 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 121=true := (@block_merge g223 6 0 8 113 g223P6_0 (@block_merge g223 6 8 96 17 g223P6_8 g223P6_104))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_2 : block g223 7 2 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_44 : block g223 7 44 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_140 : block g223 7 140 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 163=true := (@block_merge g223 7 0 44 119 (@block_merge g223 7 0 2 42 g223P7_0 g223P7_2) (@block_merge g223 7 44 96 23 g223P7_44 g223P7_140))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_16 : block g223 8 16 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_59 : block g223 8 59 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 69=true := (@block_merge g223 8 0 16 53 g223P8_0 (@block_merge g223 8 16 43 10 g223P8_16 g223P8_59))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_6 : block g223 9 6 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 15=true := (@block_merge g223 9 0 6 9 g223P9_0 g223P9_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 1=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact g223B5
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=1603) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x53129020bd67c6988,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x531010202c2586908,(pn 23704 427835580964209925)]))),((BitVec.ofNat 152 (word80 [0x655714c93b408f3648,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0x255704891b408f3040,(pn 90076 825775207663997715)]))),((BitVec.ofNat 152 (word80 [0x991b81245628f75424,0xff00ff0000])),(BitVec.ofNat 152 (word80 [0x911b81041208e75424,(pn 317639 332996784920412995)]))),((BitVec.ofNat 152 (word80 [0xb0984f5581e08781d1,0xff0000ff00000000ff])),(BitVec.ofNat 152 (word80 [0x10084e5501208700d0,(pn 47408 855671161928419850)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xb429ac7602d1ac91a,(pn 1204203 453131759546269440)])),(BitVec.ofNat 152 (word80 [0xa001a42602410891a,(pn 208598 964953112485047340)]))),((BitVec.ofNat 152 (word80 [0x2c8d22b02c17c09a67,0xffffff000000])),(BitVec.ofNat 152 (word80 [0x288420a02c15008203,(pn 834395 859812449940189360)]))),((BitVec.ofNat 152 (word80 [0xd224e40a9601212633,(pn 1208925 819333154197995520)])),(BitVec.ofNat 152 (word80 [0xc000a0008401200621,(pn 910250 28886309025661120)]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,10),(4,0,235,0,10),(1,0,238,0,9),(8,0,231,0,9),(64,0,175,0,9),(32,0,207,0,8),(128,0,111,0,8),(0,2,77,160,7),(0,4,139,96,7),(0,32,73,134,7),(0,64,162,13,7),(9,0,230,0,7),(34,0,205,0,7),(36,0,203,0,7),(1,64,162,12,6),(2,32,73,132,6),(4,32,73,130,6),(4,64,162,9,6),(8,64,162,5,6),(32,4,139,64,6),(65,0,174,0,6),(72,0,167,0,6),(128,2,77,32,6),(128,32,73,6,6),(9,64,162,4,5),(33,0,206,0,5),(40,0,199,0,5),(73,0,166,0,5),(96,0,139,0,5),(96,4,139,0,5),(129,0,110,0,5),(136,0,103,0,5),(160,0,77,0,5),(160,2,77,0,5),(137,0,102,0,4)]
def g239A : List (List Nat) := [[],[48]]
def g239D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6081000,(pn 76591 465740551919698179),(pn 606856 393111706748413923),(pn 765574 4329813207433257),(pn 1018322 348258220126174817),(pn 478675 85937233685240705),(pn 420678 923639152823788628),(pn 197594 704409953358093158),(pn 786354 207683246370199057),(pn 469138 967672002753957216),(pn 360045 524701516090388669),(pn 370805 232263153958886001),(pn 686280 277973138516886861),(pn 379194 680862695541260592)])
def g239D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xa04000000,(pn 920935 251139449135238166),(pn 38077 565624623319744512),(pn 529126 410387985040240706),0x70207020409181d001,(pn 7139 286840641209778592),(pn 302231 816327440175992832),(pn 14222 731297822424696860),(pn 38148 447708852003045895),(pn 28422 542658720818790404),0x4090400241e081000,0x504000c1064106,(pn 303130 170850649772132386),(pn 57259 153014839592747525),(pn 917953 807102624149017218),(pn 910268 475701230095647017),(pn 14444 18756137597083681),(pn 190223 408114965014709504),(pn 869095 392190617599541280),(pn 579744 705945387725235700),(pn 896505 56507043064688133),(pn 881728 323197602243632683),(pn 327663 432081258142382405),(pn 795811 30578400903039349),(pn 201379 976335802030835336),(pn 836193 364515495150226240),(pn 491144 461782051757963743),(pn 278162 841409398317665713),(pn 822665 300115075627769739),(pn 837983 514211796064056405),(pn 956893 443293858235597384),(pn 335441 425865839304674129),(pn 425751 173124192225472389),(pn 152739 599491019558505861),(pn 435459 244299226951633247),(pn 571509 490749013079016110),(pn 14858 736797329872179148),(pn 222075 167303615245244161),(pn 692932 515888645987104355),(pn 555414 605660788989600449),(pn 962594 759848224498853562),(pn 824256 333219008043114703),(pn 810753 45301636544979031),(pn 328245 972087251577886590),(pn 365782 584116063174034338),(pn 914358 364819828203973323),(pn 909877 222243015766953312),(pn 829892 123116641548343453),(pn 260717 255227476896297047),(pn 1049646 569350089723891339),(pn 126349 665582228277046719),(pn 182884 221405029809472909),(pn 456736 522412866126739345),(pn 461136 699112578314717352),(pn 413175 755509681656413040),(pn 203700 594185192320816182),(pn 1108792 329662521432987697),(pn 686233 790040096922803037),(pn 705417 780278242556254408),(pn 794832 33425722899849138),(pn 361770 240319658663310164),(pn 206587 875293996349514838),(pn 367409 615560383084997141),(pn 1121895 898054402960925478),(pn 1089249 677885129492859387),(pn 947731 99954026508046179),(pn 397794 725093949625982436),(pn 407401 914026689464674730),(pn 110783 153573954275193347),(pn 163634 749242893839946763),(pn 447652 942198397440955865),(pn 393436 153644673883834094),(pn 421324 16676258044381872),(pn 189461 420757245216675666),(pn 656902 436694561290147860),(pn 49562 604945169945958666),(pn 82462 434207670324873605),(pn 594508 28736363292295944),(pn 883784 947349879173464983),(pn 825143 959697054397858137),(pn 89964 391120330974928599),(pn 406278 318687965241445513),(pn 635128 124585586439212213),(pn 41028 303721656034395330),(pn 1055205 364035427385625988),(pn 415919 601571393450434943),(pn 269572 746605678855500204),(pn 45004 750605384296756947),(pn 164225 608610681259087364),(pn 920772 867978409449024914),(pn 473787 547254307871687265),(pn 451455 351126179913606706),(pn 198515 67116467557314751),(pn 663654 523644294621058261),(pn 22503 536104945810439525),(pn 686280 277977372442651266),(pn 458585 590934631204122926),(pn 843754 796326973736343856)])
def g239H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1100167a1,(pn 227855 385541035880461440),(pn 215206 81665408450965704)])
def g239D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xae956c6a,(pn 1111308 715894220086619300),(pn 779682 232145806944606839),(pn 696892 306183433330121069),(pn 959568 971407227732632457),(pn 107887 891558705607901780),(pn 6487 992328296912774191),0x75dba69c86e196f336,(pn 971332 717015458431691459),(pn 28060 835301369751020210),(pn 99956 350303016930257221),(pn 344035 961237131273379916),(pn 1184864 4204878081583939),(pn 283804 653408833873992138),(pn 492561 668284777238867483),0xc485882a312f08f43f,(pn 8357 280385407136985173),(pn 613317 806330818571125604),(pn 906547 193378374563501412),(pn 1057078 401449453451858272),(pn 1132599 952928649753776480),(pn 1057060 247716501154025824),(pn 905960 661165668836954464),(pn 1057059 959486125002051936),(pn 906550 668745650853761376),(pn 1132599 88237521298624864),(pn 1132599 646683875092304224),(pn 1132599 358453360983888224),(pn 906555 244402872547134816),(pn 1057077 828643478049770848),(pn 1057040 935155330647444832),(pn 1057059 381899404356472160),(pn 1057058 805438720772509024),(pn 1132616 651150236569668960),(pn 1132598 204405956466282832),(pn 905964 101898191963263312),(pn 1057061 382606049425068368),(pn 905960 643133678142460240),(pn 1057061 94375673273094480),(pn 906550 650713795999404368),(pn 905960 66672925820702032),(pn 1057336 83042917529013584),(pn 1056745 787232421417946448),(pn 906551 802509368456727888),(pn 1170672 266142342770412880),(pn 1170081 970331881021230912),(pn 1057080 693460726662401856),(pn 1057061 75780749802950464),(pn 1057080 134451302927535424),(pn 1189598 643558672570338624),(pn 1057061 75217800117964096),(pn 1189266 584151083669881152),(pn 1207013 519508195652239680),(pn 1207011 213665185851343168),(pn 1057372 403412828026165552),(pn 1057060 517879496114278704),(pn 1057061 382570761990541616),(pn 1057061 94340385838567728),(pn 1206418 616497689043505456),(pn 1207307 514474277676351792),(pn 1207270 620986130223694128),(pn 1207565 750876911335457072),(pn 1206975 455066552092934448),(pn 754841 763184925216195428),(pn 755434 937076093439296868),(pn 754845 217445013703999588),(pn 1055897 809828735517835364),(pn 1055895 503985452499976292),(pn 897105 936905673506133344),(pn 754845 221944009664614752),(pn 1038759 924673602365280608),(pn 904187 179661189636542816),(pn 904187 161646533717872992),(pn 754849 509370922560737632),(pn 901827 113312547777121632),(pn 905366 599220173264752976),(pn 904187 161629070107709776),(pn 901236 547268411474940240),(pn 904776 16287686014635344),(pn 755439 536618833290055488),(pn 1038150 893290590754410304),(pn 754849 238556940501880640),(pn 755434 943510162789225792),(pn 754554 92340465534079296),(pn 887074 617934447289158976),(pn 1038446 617093829582245184),(pn 755144 385898903365848384),(pn 905366 581170383723760960),(pn 1038762 463542896348695872),(pn 1131418 762294115925590336),(pn 1188362 708328033232978240),(pn 1131416 456451107449045312),(pn 1056482 348010996666044720),(pn 904776 880943690211234096),(pn 904187 161593756890796336),(pn 901236 547233227102851376),(pn 904776 16252638024007984),(pn 1197529 587193698382594352),(pn 753071 454746772385420900),(pn 750711 424127777153341780),(pn 753071 452772045208017232),(pn 753071 454425714990110016),(pn 1121971 723467749682659632)]) else (if j<2 then (word80 [0xa0834105,(pn 916402 11076495495670272),(pn 624551 429902158572570744),(pn 151908 954364187913817140),(pn 24814 329863086001948289),(pn 171591 649491216151628544),(pn 657646 39124919877438597),(pn 1059212 195811828920493568),(pn 435677 529915939836149764),(pn 643533 438369897717506129),(pn 11817 603620245651592221),0x12050d07400481440a,(pn 11968 767513914293364786),0x80121e130483050505,(pn 47308 459030200290640513),(pn 155103 394882119761144326),(pn 302315 191462943991152769),(pn 312866 111282804199282689),(pn 380743 707288646633678881),0x7c3485102a0a089408,(pn 473086 377350010350118952),(pn 154217 734827540392577540),(pn 614590 678503556479861144),(pn 662095 876295310919008899),(pn 52057 117751582581760224),(pn 920872 281955694941324312),(pn 510386 102691139525559812),(pn 610422 37160184185397638),(pn 912966 278129503256449573),(pn 30696 106523447579951888),(pn 227566 65470114695819318),0x80441850950312060b,(pn 9556 784072666633117795),(pn 531118 759164695517268997),(pn 929723 990839832115681815),0x2e34260ec36103d0c8,(pn 444106 557116503445082251),(pn 25427 717563443099482159),(pn 9698 475355133298401500),0xc8cc461c1783c0110c,(pn 47268 653673548683181111),(pn 35419 482669302902293509),(pn 5759 432324509196168067),(pn 614212 754294311034553922),(pn 1065233 230273398282786335),(pn 605090 929537420459270392),(pn 245996 808399665483482628),(pn 75880 122175777865074967),(pn 604907 81833010994283142),(pn 14093 389176310075951553),(pn 764729 394488092324138752),(pn 668253 772656119115806798),(pn 66269 988338639019446704),(pn 318823 176578025855665857),(pn 75793 172848771085502604),(pn 304131 921557295156453872),(pn 434468 459846716333627432),(pn 46075 429393457525333020),(pn 77998 621654147248709763),(pn 1074952 17781412042358977),(pn 76049 184001033220178092),(pn 108913 18289271582548152),(pn 283528 782643134051784723),(pn 615288 869901081853297008),(pn 909084 393528928313077800),(pn 472853 487188419613167115),(pn 604888 631706839525360017),(pn 610371 492625559242608001),(pn 1057875 422084097195644672),(pn 218154 83211107262047010),(pn 758534 446240701878075927),(pn 1058714 199643708710584456),(pn 382346 204873073637286279),(pn 619146 570094829072515095),(pn 101643 784888251250227356),(pn 79228 784981394988860545),(pn 305110 459497594906743744),(pn 914101 219514619975827739),(pn 104927 245684588165594140),(pn 420320 649273534864093296),(pn 434498 158977660532049376),(pn 83552 510567089249523586),(pn 334210 45927196685245953),(pn 118469 893594822835422432),(pn 633830 441722473473928254),(pn 184458 507710278330990914),(pn 304850 908413302756458503),(pn 47556 62077728385965104),(pn 340582 650589641781112952),(pn 5339 799911794737288728),(pn 92123 359662163779411008),(pn 939889 283798641724682243),(pn 467429 241667632046246972),(pn 235549 857270448737060330),(pn 374353 174515659274594190),(pn 284667 915976610320047578),(pn 520925 395797561185367463),(pn 808359 53142490217238422),(pn 549921 622876647498654264),(pn 1052016 528518172157679712),(pn 297448 538294374313673588),(pn 734454 509640989155843491),(pn 212089 592146966222042611)]) else (word80 [0x530d8818381,(pn 228594 364122359847813124),(pn 652203 466443727465636128),(pn 618058 166666521171738946),(pn 1096222 54564152620410112),(pn 152594 171178344413270176),(pn 793443 38613952923449395),(pn 57301 358606507116791307)])))
def g239H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4a8,0x239163fbe94d75c58,(pn 982269 793060793087935811),(pn 802665 260881055206150280),(pn 482274 286177770798824738),(pn 175617 695944693943264189),(pn 5030 260309924407682657),(pn 5003 806215916223926193),(pn 813017 593944833639565517),(pn 217721 155699217111451992),(pn 398672 546130486431318016),(pn 34215 982211704054713040),(pn 178591 522354623204810059),(pn 767279 593921508399462153),(pn 194461 594013073596966398),(pn 338694 76809306548048962),(pn 481681 382676928877386595),(pn 676378 886344907038130190),(pn 252383 330339968404967170),(pn 836449 231272086590129570),(pn 1133367 955899710073039668),(pn 913794 858003100948041000),0xf20026a34f1ed3355,(pn 1027557 521208029481009698),(pn 396679 957542178255799314),(pn 303433 252295210061267201)])
def g239D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x1b006060,(pn 359416 470024552313856432),(pn 529016 232712697980980760),(pn 198709 202848351582093448),(pn 755805 491489527924113745),(pn 22144 164330786244576066),(pn 914960 172979483656080132),(pn 266519 444526293041938882),(pn 836759 348782086624645825),(pn 906954 360626995113166592),(pn 96966 484556307423658352),(pn 529016 93800417656326919),0x5c38589060485c012c,(pn 79726 847524606327391936),(pn 113872 626014395579434752),(pn 342450 833480313440632880),(pn 918212 88900685511268226),(pn 911861 839999085978519051),0x48814c017c12118181,(pn 685636 655876562531631490),(pn 907120 667592913828515587),(pn 20670 760057026831454736),(pn 840609 530367355193918984),(pn 47390 65729609230209060),(pn 94689 13931718657273924),(pn 510238 679787053894715076),(pn 914959 952292051366904940),(pn 380967 650798451355070468),(pn 638774 917975062198950656),(pn 455490 580618757261503505),(pn 614244 489842399621678535),(pn 50853 314702758658185254),(pn 104095 194186305992659313),(pn 157922 679862116961601294),(pn 929194 889655425608717407),(pn 14247 831024027974074694),(pn 382237 339410837929509912),(pn 108720 623997431334899211),(pn 33063 226239585905024001),(pn 537210 785119020491211464),(pn 50797 729110471780009728),(pn 455052 457446588224904192),(pn 840664 311976297330315539),(pn 31877 710762406667884295),0x70786c4c3c2850fc12,(pn 7110 98450729662661126),(pn 906936 123303533674508396),(pn 359791 930334636465537541),(pn 926469 708892500701265281),(pn 660787 607206848865097115),(pn 209211 300998695356912880),(pn 780759 679102024366246738),(pn 376945 997385325257496456),(pn 799342 535752386763552542),(pn 1194519 454397614831593585),(pn 696384 998206020359786900),(pn 965435 846814108445410745),(pn 212826 988928034779239532),(pn 753306 888101263758083666),(pn 146696 326845847531742407),0x36d1ab0cec65030d17,(pn 1136721 43482982914559048),(pn 614591 347880463521485001),(pn 27377 994972918143959496),(pn 59330 854430339555983824),(pn 36598 412280640384562265),(pn 604078 755573133839695594),(pn 833494 753935639788134397),(pn 988763 915174023273928767),(pn 1074979 543211438828603568),(pn 603969 856844541833772493),(pn 458063 670242251858526203),(pn 163548 803988744659576959),(pn 936306 288779539552505168),(pn 1207389 698073858601380510),(pn 613905 144418730409754615),(pn 250359 116459124049395967),(pn 1117015 493275452336448097),(pn 1204665 994199995368068877),(pn 713072 307468933246861230),(pn 883783 324162639736916351),(pn 441067 125738298876056979),(pn 1188720 624797746573848227),(pn 179402 663656921449987932),(pn 176129 434916013839045566),(pn 843728 691020915935152805),(pn 1196932 569402666215497014),(pn 56574 412279328043925426),(pn 812762 793300257413989887),(pn 544699 492855806321808907),(pn 1203846 650903036426105514),(pn 113296 538122833130650963),(pn 397562 766437943249997690),(pn 952156 65231504179587095),(pn 1198766 329269936898143568),(pn 226298 495916894258690760),(pn 757864 107395272459950077),(pn 969283 584253498117804095),(pn 958686 620790524475009688),(pn 452595 820930312370644289),(pn 230172 589494659117035451),(pn 655401 241920724705489503),(pn 411170 70201700089448788)]) else (word80 [0x512c1c0,(pn 108874 423056304224896096),(pn 473198 494475103065211296),(pn 79405 248431906797077828),(pn 914960 674570400449712665),(pn 89854 117567708984795508),(pn 359416 470255721142841349),(pn 946965 772718484505149729),(pn 153333 409986012808413276),(pn 684159 868778908968165889),(pn 760907 490116251469496452),(pn 621041 999611485723036420),(pn 625130 316330373565481361),(pn 330289 398619350000736069),(pn 320028 30273014869031445),(pn 96274 736987879528597700),(pn 232587 515727121276750868),(pn 466643 34174354455818272),(pn 686110 541867537572382277),(pn 626922 18928568535099670),(pn 89854 237058583879766065),(pn 340822 913933286764015728),(pn 21375 598379222959160849),(pn 80557 366073375993895936),(pn 1097096 853402563511745),(pn 907120 374572966173870172),(pn 462503 127699627680304129),(pn 540722 609002312131593998),(pn 44941 205148396476074792),(pn 269655 734924338683516460),(pn 794688 104787350363855900),(pn 41078 674421343115571234),(pn 989502 501727401187499780)]))
def g239H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x80000000,0x32a3c9b000559d0b96,(pn 28334 198897217871282201),(pn 726384 358919488655065088),0,0,0x44e51a0000000000,0,0x71700000,0xa0,(pn 491126 114218443102224714),(pn 1057810 92162800527867904),0,0x52400000000000000,0,0x107200000,0x46,(pn 768943 303340545804337931),0xe3b,0x52800000000000000,0xc8d0420,0x181c00000000000,0xb0a000000000000,(pn 16750 958107069517484032),(pn 133093 258492082450296832),0x93e00020bc,0x50615400000000006,(pn 9444 732975757301645312),0xd14e0fc00000065100,0xc7a000000000018,(pn 604467 563312439200055296),0x2eaa000,0x8b40000000000000,0x126a2080000000,0,0x94f0000003c09a8300,(pn 33139 575728419209478886),(pn 302232 767702948672179598),0,0,0x1c11000494c001b,(pn 637519 475227267991096192),0x70e42800000000,0x20be000000000,(pn 192711 263573978780794880),(pn 1135729 152879418293616640),0x29c5,(pn 212506 491729134034616320),0x1b0940f14,(pn 751270 965402465227243852),(pn 302231 454903657293676544),(pn 136210 758240271329132544),0x4bc0,1,(pn 561961 611515303721503872),0xe6a000f52800000109,(pn 377797 391340287454871552),0x5c000632,0x1140000,(pn 518279 721494943562257952),0x62600000,0x54,(pn 264453 626422665880272896),(pn 86353 527961319456636928),(pn 216048 275373085733765120),0x147fb138,0x30d20000000003c160,0xb4f005611471600000,0x33,(pn 831144 720054377521513608),(pn 906694 364710971923734528),(pn 383101 980924833903411202),(pn 938570 338476483789455360),0x606800000000000000,0x4a8c00000000,0xd2,(pn 151115 727451828670127274),0,0xb548000000000ac18,0x48ac0000,0,0x98b000000000000,0x3b1969a84b000,0x61c7826000,0x5992c800000000002,(pn 981333 566176575113658368),0,(pn 5914 487318649501646851),(pn 566683 978128869220679680),0x18fbcd6000d36,(pn 604521 294472883933770836),0xab400000000000000,0x72740000,0x7c000,0x7e0400000,0,0x7328000000000,0,0xa3c000c,(pn 8489 249275994731184128),0x450000a3c00000001,(pn 18908 25274345711468546),0x18244010001408240]) else (word80 [0x15300,(pn 16804 984045764188569736),(pn 1112643 38921985569587200),0,0xe208000,0xe0f00038ec0000,0x1a2e00000000000,0x1e000000000000,0,(pn 10809 792027386687320064),0,(pn 47518 812733875804962820),(pn 161741 171944572432941056),0x3bfd154001c1f00000,0xa71c80000488800000,0x2a9000145b000000,0x1d970000000000000,0x1c869150000001,(pn 788526 107444738177196640),0,(pn 5911 28589715993395200),0xc36000000000309,(pn 906694 364710971887872852),0,0x59300008c6000a4a0,0x610007c280000,0xcaaf0480,0x1e37000000109600,0x329ed30000000000,0x1888,0x1a000005a64,(pn 791586 681691024278970463),(pn 802081 243628981580726272),(pn 5904 111106048747634688),0x4e681c000000146]))
def g239D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1418242,(pn 435122 386370847093301441),(pn 152318 242754622547723008),(pn 231426 96740004730618629),(pn 647223 658293812628822056),(pn 684171 760168776929215042),(pn 85224 174155111309791365),(pn 1059012 609650825479029258),0x624286890e08280386,(pn 47456 575239515005006360),(pn 684162 247744305032741678),(pn 47445 170722710357284866),(pn 948355 235975781303736065),(pn 582281 849295153318072317),(pn 717751 714995950305932691),(pn 1191899 444786958153122813),(pn 458057 172933453967260976)])
def g239H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd100023930a0,0xa65000,0xb5000,0xe5c0000000,0x51c000000000000000,0xd5200000000000,0,0x7a5004000112000,0x71500000044d00,0xb,(pn 410846 967969794446327808),(pn 327023 924133048879153152),(pn 38498 354881831834222592),0x1d2000000,(pn 988155 186540476564063488),0x2553580,0xb33f0d2af000000000,5,(pn 680020 773533229049315456),0x8d40004da3ad000000,(pn 239069 803204686062288896),0x410000007250000000,0,(pn 180643 776567066909016429),(pn 377789 318629571653337088),0x9200000065b0dc000,0xa2,(pn 147426 378637086796670224),0xf1122c000000,0x59700085e00000,0,0xc94000,0,(pn 58199 478847778332868608),0xf22000abe000,0xea100000000011,(pn 23962 320551748707566528),0x6bb000000000000,0x93b000516e2b00000,0x2d90,0x507a9b,0xc370000000d300000,0x52e0000000,0x33a000000,0,(pn 38332 334185168692641792),0xa23000000000a354a9,(pn 22136 120420224998572032),0x80c000f1f0,0x720000,0x24300000000,0,0x5cf0009c2000,(pn 28629 346802398862283676),(pn 1057810 92205407663030272),0x240000000c600002b6,(pn 379560 206063078685540352),0x15f0000000000000,0xd00000000000000,(pn 329680 278466164261126144),0xb81000000000c,(pn 127503 895037480420769792),0xfcd00006700000,0x3e00000033d7630001,(pn 231395 957660647229525296),0xfcb202e4800022,(pn 1017190 361712492095265600),0x3c9000000000000000,(pn 384817 888413748314719232),0,0xa89000,(pn 1119294 891607236080041984),0x74f0,0x54a000,0x9c82e1a4,(pn 453347 185788161242431488),0x4181a8e34656,(pn 702452 14326860277088310),(pn 151130 292093023649267712),0x84735a000000000000,0,0x8490410,(pn 37797 564116632709891072)])
def g239D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81840802ff
def g239H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x21e62000,0x3d000635840123002,(pn 806757 759597363664519169),(pn 179462 932806617893175296),0x6000abe4b2802e800,0x2c8000048])
def g239L : Nat → Packing
  | 6 => (13,5,6,0,0,8,0,g239D6)
  | 7 => (101,4,6,0,0,11,0,g239D7)
  | 8 => (171,3,6,0,0,13,0,g239D8)
  | 9 => (104,2,6,0,0,13,0,g239D9)
  | 10 => (14,1,6,0,0,10,0,g239D10)
  | 11 => (1,0,6,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 23 2 9 4 1 g239H7
  | 8 => lookupWord 32 149 7 12 7 1 g239H8
  | 9 => lookupWord 56 829 3 13 8 1 g239H9
  | 10 => lookupWord 36 547 3 12 7 1 g239H10
  | 11 => lookupWord 4 53 2 9 4 1 g239H11
  | _ => fun _ => none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : block g239 6 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B6 : block g239 6 0 13=true := g239P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_3 : block g239 7 3 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_99 : block g239 7 99 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 101=true := (@block_merge g239 7 0 3 98 g239P7_0 (@block_merge g239 7 3 96 2 g239P7_3 g239P7_99))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_10 : block g239 8 10 70=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_80 : block g239 8 80 91=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 171=true := (@block_merge g239 8 0 10 161 g239P8_0 (@block_merge g239 8 10 70 91 g239P8_10 g239P8_80))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_8 : block g239 9 8 60=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_68 : block g239 9 68 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 104=true := (@block_merge g239 9 0 8 96 g239P9_0 (@block_merge g239 9 8 60 36 g239P9_8 g239P9_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 14=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P11_0 : block g239 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B11 : block g239 11 0 1=true := g239P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
  · exact g239B10
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=1049939) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8366c3359803cd000,0xff0000ff000000ff])),(BitVec.ofNat 152 (word80 [0x816683159000c1005,(pn 23704 427835580964209925)]))),((BitVec.ofNat 152 (word80 [0x4f4a6867855b401000,0xff0000000000ffff00])),(BitVec.ofNat 152 (word80 [0x454a68270503001011,(pn 80595 54640975278313745)]))),((BitVec.ofNat 152 (word80 [0x1727e208320d8a7200,0xff00ff000000])),(BitVec.ofNat 152 (word80 [0x1727e00822090a5043,(pn 317639 332996784920412995)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf2a04dd88e21110600,(pn 1204203 524907878590775295)])),(BitVec.ofNat 152 (word80 [0x12a005c0820011020a,(pn 47408 855671161928419850)]))),((BitVec.ofNat 152 (word80 [0x899534d41346622bff,0xffff0000])),(BitVec.ofNat 152 (word80 [0x889014d0104460232c,(pn 208598 964953112485047340)]))),((BitVec.ofNat 152 (word80 [0xc41a93a66070a8ac00,0xffffff00000000])),(BitVec.ofNat 152 (word80 [0xc00812060070a0acb0,(pn 834395 859812449940189360)]))),((BitVec.ofNat 152 (word80 [0x30c990090098855dff,(pn 1208925 747557035136778240)])),(BitVec.ofNat 152 (word80 [0x200180080098804cc0,(pn 910250 28886309025661120)]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(0,4,147,96,7),(0,32,81,134,7),(0,64,162,21,7),(2,32,81,132,6),(4,32,81,130,6),(16,64,162,5,6),(80,0,167,0,6),(128,32,81,6,6),(160,0,87,0,6),(96,0,147,0,5),(96,4,147,0,5),(130,32,81,4,5),(144,0,103,0,5)]
def g247A : List (List Nat) := [[],[16,116,101]]
def g247D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x29f3a05d7815d163
def g247D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x380,(pn 142263 684300562164150513),(pn 36733 387446741208411042),(pn 942690 257874105593214752),(pn 919319 583985767208553795)])
def g247H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10a108242285809690,(pn 457493 131275981349021024),(pn 343627 436643981488315996),(pn 293635 353584977662519664),(pn 1172185 148950113142562981),(pn 144466 505741481567614556),(pn 369194 149448262578403512),(pn 11910 94608192227056216),(pn 645207 712467687766784224),(pn 191371 195506238212657507),(pn 1057059 959489217950994787),(pn 1199339 677354522683215171),(pn 830996 263787409849045347),(pn 901827 113315503258326339),(pn 754554 92343978248998211),(pn 753071 454429013524993347)])
def g247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x16001000,0xd4c000000000401])
def g247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x665498,(pn 831408 756110243888581003),(pn 28661 958250803953255175),(pn 123454 296719045909907201),(pn 460142 700478233475899676),(pn 228374 728565400934291526),(pn 52393 966324093580091521),(pn 5079 970734742472508355),(pn 644321 874972372114137540),(pn 629496 228585038808945182),(pn 132678 535115034592839436),(pn 236672 611898593936018488),(pn 637742 574040205647486008),(pn 835742 550116413862756133),(pn 821121 559775430187219920),(pn 1039809 103711020064680060),0x7ff7458ffeba2c7ff5,(pn 384356 336028333964087551),(pn 1110540 650490788315063466),(pn 453186 173883437200965073),(pn 395496 952794559848443899),(pn 805301 790122037746377211),(pn 1007138 34242612537182548)])
def g247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x680030eb8860050,(pn 419934 364230474908303360),0x71464000000001300,(pn 43214 380296426968055808),(pn 26858 459535113979955257)])
def g247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe,(pn 67907 946388238965999118),(pn 189505 478704365884768802),(pn 333311 968137053638652470),0xff553fd63ff54ffd43])
def g247H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3d100,(pn 132857 975778398527718306),(pn 302231 637054526062985496),(pn 1114757 743168995839731432),(pn 604463 76682668463820419),(pn 302231 649230242943074336)])
def g247D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3148310023ff
def g247H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x280099ec0000,0x164000c514000])
def g247L : Nat → Packing
  | 6 => (1,5,5,0,0,0,0,g247D6)
  | 7 => (4,4,5,0,0,7,0,g247D7)
  | 8 => (13,3,5,0,0,10,0,g247D8)
  | 9 => (19,2,5,0,0,10,0,g247D9)
  | 10 => (4,1,5,0,0,8,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g247H7
  | 8 => lookupWord 1 17 0 7 2 1 g247H8
  | 9 => lookupWord 4 41 3 9 4 1 g247H9
  | 10 => lookupWord 7 41 4 10 5 1 g247H10
  | 11 => lookupWord 1 23 0 7 2 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 1=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1 : block g247 7 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 4=true := (@block_merge g247 7 0 1 3 g247P7_0 g247P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : block g247 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_8 : block g247 8 8 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 13=true := (@block_merge g247 8 0 2 11 g247P8_0 (@block_merge g247 8 2 6 5 g247P8_2 g247P8_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_1 : block g247 9 1 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_13 : block g247 9 13 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 19=true := (@block_merge g247 9 0 1 18 g247P9_0 (@block_merge g247 9 1 12 6 g247P9_1 g247P9_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 4=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : block g247 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : block g247 11 0 1=true := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1049924) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x821209d867fcc18010,0xfe0007f0003fff])),(BitVec.ofNat 152 (word80 [0x2120850662c400000,(pn 761528 75347797905326725)]))),((BitVec.ofNat 152 (word80 [0x22af700644067ca210,0x7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x2077006440620a012,(pn 475955 47092373690829203)]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x18c58a81005dacbd80,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0x188182810050acad01,(pn 314130 331080966635947274)]))),((BitVec.ofNat 152 (word80 [0xd022269a3800be4c60,(pn 149935 136389663144542080)])),(BitVec.ofNat 152 (word80 [0xd020028800009e4c21,(pn 9519 100941847473816584)]))),((BitVec.ofNat 152 (word80 [0x15b99b69ac12c842af,(pn 1057810 92162800794206208)])),(BitVec.ofNat 152 (word80 [0x11b88b49a810c842a5,(pn 656817 964987475693344300)]))),((BitVec.ofNat 152 (word80 [0x6154172748a10167d0,0x1fffff0000000])),(BitVec.ofNat 152 (word80 [0x2144152608810102de,(pn 133267 413185864633432176)]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,(pn 1208925 819051679221284864)])),(BitVec.ofNat 152 (word80 [0x240000201181001048,(pn 76152 807534779790532672)]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(1,0,250,0,9),(32,0,219,0,9),(2,0,249,0,8),(128,0,123,0,8),(0,2,73,176,7),(0,32,89,130,7),(0,64,162,25,7),(10,0,241,0,7),(18,0,233,0,7),(96,0,155,0,7),(160,0,91,0,7),(1,64,162,24,6),(2,32,89,128,6),(8,64,162,17,6),(32,2,73,144,6),(33,0,218,0,6),(34,0,217,0,6),(65,0,186,0,6),(66,0,185,0,6),(128,2,73,48,6),(128,32,89,2,6),(3,0,248,0,5),(48,2,73,128,5),(97,0,154,0,5),(129,0,122,0,5),(130,0,89,0,5),(130,32,89,0,5),(160,2,73,16,5),(162,0,89,0,5),(192,0,59,0,5)]
def g251A : List (List Nat) := [[]]
def g251D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x6c204000002df0,(pn 314463 230054570605457662),(pn 725184 849723506864825921),(pn 481037 338670606244512101),(pn 379753 437759243429437681),(pn 975194 465311490253765125),(pn 715518 962652552516492817),(pn 459696 354744387555673440)])
def g251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x87070607842142c1,(pn 870107 282069389500746628),(pn 31935 962309800110243859),(pn 28468 253257110426521659),(pn 38480 777656026282594916),(pn 154694 422933729309103391),(pn 323786 714664989211038023),(pn 48573 883540958688066577),(pn 1081294 491830406556707106),(pn 337088 608676753665683585),(pn 524260 580476676922606681),(pn 161874 905826302385735430),(pn 1022374 150388847386670627),(pn 18595 224973588495106300),0x5a85f046f0bc1f000f,(pn 26075 937062640031402250),(pn 759489 381429620451632872),(pn 1025239 133713611791674501),(pn 343009 275770469251852816),(pn 611770 18709705955521280),(pn 844348 364314169486968527),(pn 1146576 25813090688401497),(pn 406688 433350632548848601),(pn 26405 674342089391877298),(pn 71423 322835146384866227),0xb2a8376f9260165507,(pn 979633 596615647451562341),(pn 439586 865982637137904103),(pn 873740 945651643875111630),(pn 203202 335272621033182204),(pn 919869 423652078670661397),(pn 622456 702990341163839041),(pn 478588 529491462472207041),(pn 1094279 707496112997998656),(pn 815401 940954483968532689),(pn 1110623 748887172160707655),(pn 101596 500394572287863029),(pn 715518 674421821553289986),(pn 612866 83348048598852298),(pn 305404 908620070344262976)])
def g251H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x9803,(pn 610365 867975563987198919)])
def g251D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x832158616a10b0661b,0x2c85141c878321708c,(pn 274209 728172026260570765),(pn 625156 739033385129231899),(pn 5359 362947376547680500),(pn 158260 412453715660981134),(pn 109270 547277736786031169),(pn 92087 794878037013578177),(pn 986995 667877050183665295),(pn 910836 933452492011474440),(pn 265525 923792078867806241),(pn 455431 786238880235397488),(pn 265269 976266062663221774),(pn 635403 36007461278505076),(pn 539789 599003565925573585),(pn 153110 348927514438373403),(pn 66435 391738221196099692),(pn 223411 161233560327619459),(pn 326666 455859195883032752),(pn 1066628 141407573795817921),(pn 987423 946338977570113286),(pn 344168 990433033814601779),(pn 54473 497285516521015480),(pn 293211 249840447738218224),(pn 265417 568148259655614913),(pn 52080 284761883652140811),(pn 611617 982117324671949840),(pn 871137 843873699969664387),(pn 1075824 556063258428555654),(pn 688301 92797270393956484),(pn 184228 191804132706873528),(pn 39513 527162326177530080),(pn 621118 45460361305922576),(pn 794396 67990427091890241),(pn 923268 195700235049921807),(pn 614204 341333646171580526),(pn 33140 591008901143692736),(pn 1060494 247253596061958427),(pn 614923 42437369445024769),(pn 1173437 600640973240240064),(pn 1060849 590552215377807484),(pn 455417 217381934366507504),(pn 869433 684787824197077440),(pn 1060236 406866704176558256),(pn 283988 454170833207943536),(pn 265068 273408247086942656),(pn 1060273 373096350997907925),(pn 515232 400382652719873771),(pn 801473 795278189441161748),(pn 741291 747470913322898047),(pn 867558 833546042157327253),(pn 1153935 310292200920335464),(pn 320605 870309342288487471),(pn 768697 204798757690939969),(pn 533983 732876177981104128),(pn 1170999 716416016141882977),(pn 1170999 716134541165172065),(pn 1170999 716380831769794113),(pn 1170999 716099356793083201),(pn 868178 558773899241047397),(pn 868177 690705071608021349),(pn 887068 6933078569489760),(pn 1095443 5328962950108512),(pn 1169819 124512655494992224),(pn 1094820 444604974094992736),(pn 830406 252826602419897696),(pn 1055284 745221432582456672),(pn 1094820 441227085964756320),(pn 1094820 152996861727327584),(pn 1094820 711443252016153952),(pn 887662 334343612993176928),(pn 1094820 387184009893221696),(pn 1019892 59606996577785104),(pn 1204352 576622409074460005),(pn 1017505 813363938619147621),(pn 849883 420500277592441189),(pn 864048 212980165815161185),(pn 877625 885808711739216449),(pn 884707 976613163352557121),(pn 736546 630501460645090625),(pn 1111347 552947193288955744),(pn 736546 625469132300457312),(pn 1036395 225211812974002496),(pn 736546 630447720385839376)])
def g251H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [1,(pn 123067 453091361783412323),(pn 44862 484937233041195189),(pn 491438 141617041458713643),(pn 914739 623858408357858722),(pn 12691 839103591524614680)])
def g251D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x44c2c0c11b1d1848,(pn 259933 288169331622685697),(pn 510341 984972504524927047),(pn 335791 19379689498132758),(pn 171704 48340960977552132),(pn 513118 965859090856763857),(pn 155555 641753315815228354),(pn 910256 252118073397150468),(pn 417864 303873435035095427),(pn 227563 900827631364148928),(pn 911824 794197943757427788),(pn 56988 973451510656544839),(pn 330991 533677640715125006),(pn 171708 713167630371062820),(pn 682311 340451326593139075),(pn 933565 519818462591173312),(pn 911658 272786788443780196),(pn 208823 772455010826334384),(pn 16238 90437767981088961),(pn 104427 610156730826388592),(pn 661943 26284255303037104),(pn 227983 744536998542316563),(pn 52001 678980846086523921),(pn 80013 973088935598163394),(pn 910255 529551952366296152),(pn 321936 143312655010017328),(pn 459573 320108366139299609),(pn 71038 628858874240438625),(pn 232612 339440653550357955),(pn 107447 753357582177862404),(pn 587367 113904793448448449),(pn 229923 697102224393158849),(pn 146874 60278326950650913),(pn 988897 383155257511522371),(pn 320046 547104777085786883),(pn 20226 11626222631579984),(pn 621598 795719454276763917),(pn 71259 920698709951392772),(pn 416676 312064427037831239),(pn 332996 210703300653758991),(pn 14249 273336908095762801),(pn 685350 779241704940903874),(pn 622185 697457038406912771),(pn 20152 212464934705695761),(pn 463108 978006367387681730),(pn 907962 656643640506122767),(pn 20521 159527209832812897),(pn 910267 342605569401129028),(pn 910255 819481439993862914),(pn 89806 854470847926374609),(pn 1136614 686502442936746885),(pn 83836 38604275342050356),(pn 435269 399077440162104130),(pn 929176 408937511959331588),(pn 247072 330605327383843271),(pn 328271 407613767462568462),(pn 929135 99407266784905060),(pn 206027 145115444920838671),(pn 87195 717870908690860599),(pn 574690 820313193570181317),(pn 784174 520474676147888831),(pn 706596 309231285257177562),(pn 363075 415318921982386873),(pn 66264 902104947381794339),(pn 689979 193835124877790604),(pn 77285 143388631402351142),(pn 761030 280709585733851246),(pn 15091 139201541280637186),(pn 34683 482127544313151952),(pn 54901 978206869397557600),(pn 1207423 204857343377404810),(pn 916127 304455698577915878),(pn 101604 571971653357363455),(pn 794151 319395677894320843),(pn 1057152 233065932652009237),(pn 716586 304135180929331118),(pn 52794 397411646829414783),(pn 435455 856788565449398662),(pn 1202917 673175085678046379),(pn 66103 67605327394631453),(pn 104445 377319694886078207),(pn 869731 121927825380004367),(pn 592169 343264198118692964),(pn 132131 803268019242073787),(pn 190037 606826124920885238),(pn 459554 487822476086350875),(pn 1184791 747489879033887276),(pn 113295 677935305905012086),(pn 378894 622029333407206398),(pn 1070215 231463801570207767),(pn 1161020 845639138031793348),(pn 300664 499892972342213356),(pn 644452 448257731452868597),(pn 987288 102919280487646271),(pn 958679 738993966862494642),(pn 414818 673476873341042129),(pn 461310 312968145908297451),(pn 721405 709617778554581207),(pn 1017033 798208823351416160)])
def g251H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [3,(pn 11418 534581629999906816),0x730004840000000001,0x20000000000000000,0x571ca0036710f,(pn 826414 134502187912396800),0x25ec3c9f00231000,0x9040000000000daa8a,(pn 481304 488514438729564160),0xcb611d9000134,0x3f7d2c0095000743,(pn 784392 453122174627520515),(pn 936342 895829884737778252),0x3d5003e000375ecc,0x3c500000000008d2,(pn 538349 779049991416754176),0,0xe8fb9b6c,0x9e0,0xb490059200e13])
def g251D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [2,(pn 924454 220059940854472222),(pn 104411 458342141968529488),(pn 153718 770936384409635384),(pn 306389 1741079139205635),(pn 52130 791947582199956496),(pn 610497 741234200457134722),(pn 341494 206103298434506977),(pn 304633 17596509990225129),(pn 7226 802193861907318283),(pn 85006 654521848182134800),(pn 329272 839736674957915681),(pn 317667 791050569402028029),(pn 698862 177006053050283399),(pn 1191844 103217725784818685),(pn 458056 884699779268050277)])
def g251H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x111da3,(pn 157018 753039067810627586),(pn 729494 941138940237787604),(pn 513649 232949035677515816),(pn 447001 502409986874086814),(pn 115698 69871793232936965),(pn 288064 355455048358035456),0x8340035f000f240e,(pn 275706 118961652922889318),(pn 807525 143333920360027287),(pn 508281 587981604832356051),(pn 970757 781179942962200719),(pn 604726 914687751985169080),0x5b9a53a74000020002,(pn 867178 889868942337808777),(pn 1086499 576181332773984273),0x565b41958,(pn 780452 801627445646176258),(pn 188898 226165692626927686),(pn 216048 277960340686572612)])
def g251D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81801022ff
def g251H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [(pn 547794 537064156016672768),6,(pn 887804 917356841763078144),0,0x40,0x7ac300000000000000,0x31fb000000000000,0x35000000000097,0xe80000000000,0,0])
def g251L : Nat → Packing
  | 6 => (8,5,6,0,0,7,0,g251D6)
  | 7 => (32,4,6,0,0,11,0,g251D7)
  | 8 => (58,3,6,0,0,12,0,g251D8)
  | 9 => (81,2,6,0,0,13,0,g251D9)
  | 10 => (14,1,6,0,0,10,0,g251D10)
  | 11 => (1,0,6,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 13 3 7 3 0 g251H7
  | 8 => lookupWord 8 41 4 9 5 0 g251H8
  | 9 => lookupWord 14 149 3 10 6 0 g251H9
  | 10 => lookupWord 20 131 5 11 7 0 g251H10
  | 11 => lookupWord 4 127 0 8 4 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_1 : block g251 6 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 8=true := (@block_merge g251 6 0 1 7 g251P6_0 g251P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_1 : block g251 7 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_10 : block g251 7 10 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 32=true := (@block_merge g251 7 0 1 31 g251P7_0 (@block_merge g251 7 1 9 22 g251P7_1 g251P7_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_21 : block g251 8 21 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_50 : block g251 8 50 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 58=true := (@block_merge g251 8 0 21 37 g251P8_0 (@block_merge g251 8 21 29 8 g251P8_21 g251P8_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_12 : block g251 9 12 59=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_71 : block g251 9 71 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 81=true := (@block_merge g251 9 0 12 69 g251P9_0 (@block_merge g251 9 12 59 10 g251P9_12 g251P9_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_1 : block g251 10 1 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 14=true := (@block_merge g251 10 0 1 13 g251P10_0 g251P10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=1048643) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end ForestCore

open ForestCore
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def coding : Fin 8 → Nat := ![7, 2, 6, 1, 0, 5, 3, 4]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := ((((((((13407807929 * 1000000000000000000 + 942597087217766685) * 1000000000000000000 + 180528987471026981) * 1000000000000000000 + 148436152594090240) * 1000000000000000000 + 113389819240481381) * 1000000000000000000 + 541891457692645541) * 1000000000000000000 + 939666959725568266) * 1000000000000000000 + 218191220749062497) * 1000000000000000000 + 954235114602822336)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u:=true) (ms:=fixRows 4 0) (raw:=roots) (T:=codedGraph)
    (xs := [(inputs.getD 2 zero, 2, 6)]) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) low251
  have hcard : (([(inputs.getD 2 zero, 2, 6)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rw [hcard] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    13 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def witness8 : Circuit := ⟨[⟨.or,[0, 1]⟩, ⟨.or,[2, 4]⟩, ⟨.or,[6, 7]⟩, ⟨.or,[0, 2]⟩, ⟨.or,[3, 8]⟩, ⟨.or,[5, 7]⟩, ⟨.or,[3, 6]⟩, ⟨.and,[9, 10]⟩, ⟨.and,[11, 4]⟩, ⟨.and,[12, 13]⟩, ⟨.and,[8, 14]⟩, ⟨.or,[15, 16]⟩, ⟨.or,[19, 17]⟩, ⟨.or,[20, 18]⟩], 21⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, witness8.eval (List.ofFn x) = graph x := by decide +kernel
end PEqualNP.Outside.L_meta_34310_aux
open PEqualNP.Outside.L_meta_34310_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_34310 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hg,eq⟩ := neg
    have fan : FanInTwo ⟨gs,o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryLower ⟨gs,o⟩ fan computes
    change 13 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g,hg,by simp [eq,signedNot]⟩
    exact ⟨witness8.gates,witness8.output,by simp [witness8],by change 14 ≤ gs.length; omega,witnessCorrect⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨op,cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g,hg,eq⟩)),cap⟩
