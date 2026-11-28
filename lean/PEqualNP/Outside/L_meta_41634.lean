import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41634.Model
open PEqualNP.CircuitLowerBounds
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

def inputChunks (xs : List Nat) : Nat := xs.foldr (fun w r => w ||| (r <<< 60)) 0
def inputs : List Sig := [(BitVec.ofNat 512 (inputChunks [0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaa])),(BitVec.ofNat 512 (inputChunks [0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xcccccccc])),(BitVec.ofNat 512 (inputChunks [0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0])),(BitVec.ofNat 512 (inputChunks [0xf00ff00ff00ff00, 0xff00ff00ff00f, 0xff00ff00ff00ff, 0xff00ff00ff00ff0, 0xf00ff00ff00ff00, 0xff00ff00ff00f, 0xff00ff00ff00ff, 0xff00ff00ff00ff0, 0xff00ff00])),(BitVec.ofNat 512 (inputChunks [0xfff0000ffff0000, 0xff0000ffff0000f, 0xf0000ffff0000ff, 0xffff0000fff, 0xffff0000ffff, 0xffff0000ffff0, 0xffff0000ffff00, 0xffff0000ffff000, 0xffff0000])),(BitVec.ofNat 512 (inputChunks [0xfffffff00000000, 0xffffff00000000f, 0xfffff00000000ff, 0xffff00000000fff, 0xfff00000000ffff, 0xff00000000fffff, 0xf00000000ffffff, 0xfffffff, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0xffffffffffffff0, 0xff, 0xffffffffffff000, 0xffff, 0xffffffffff00000, 0xffffff, 0xffffffff0000000, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0x0, 0xfffffffffffff00, 0xfffffffffffffff, 0xffff, 0x0, 0xfffffffff000000, 0xfffffffffffffff, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0x0, 0x0, 0x0, 0xfffffffffff0000, 0xfffffffffffffff, 0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff]))]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  let n := v.toNat % 2305843009213693951
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d || anyEq (masked d a) d pool ||
    (u && anyEq (masked d (neg a)) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  simp only [availF,availableB,eqF_eq,anyEq_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWords (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (fun op => quickPair ctx a b op || testPair ctx a b op))
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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

end PEqualNP.Outside.L_meta_41634.Model

namespace PEqualNP.Outside.L_meta_41634
open PEqualNP.Outside.L_meta_41634.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

abbrev Catalog := List (Sig × Nat)
abbrev Hints := Nat → Nat → List Nat

def purchases : Nat → Nat → List Sig → List Choice
  | 0, _, _ => []
  | n+1, code, bank =>
    let a := bank.getD (code &&& 15) zero
    let b := bank.getD ((code >>> 4) &&& 15) zero
    let x := if code.testBit 10 then neg a else a
    let y := if code.testBit 11 then neg b else b
    let v : Choice := ((code >>> 8) &&& 3, x, y)
    v :: purchases n (code >>> 12) (bank ++ [choiceVal v])

def fromHint (raw : List Sig) (ds : Catalog) (q : Nat) : Option BoundPool := do
  let desc ← ds[q &&& 255]?
  let cs := purchases ((q >>> 8) &&& 7) (q >>> 11) raw
  let ws ← makePool true desc.1 raw cs
  return ⟨desc.1,desc.2, cs.length,ws⟩

def SafeCatalog (g : Atlas) (ds : Catalog) : Prop :=
  ∀ p ∈ ds, Slice true (roots g) (target g) p.1 p.2

theorem safeNil (g : Atlas) : SafeCatalog g [] := by
  intro p hp
  simp at hp

theorem safeCons {g ds p} (one : Slice true (roots g) (target g) p.1 p.2) (tail : SafeCatalog g ds) :
    SafeCatalog g (p::ds) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | h
  · exact one
  · exact tail v h

def pools (g : Atlas) (ds : Catalog) (hs : Hints) (k i : Nat) :=
  (hs k i).filterMap (fromHint (roots g) ds)

theorem pools_valid {g ds} (safe : SafeCatalog g ds) (hs : Hints) (k i : Nat) :
    ∀ p ∈ pools g ds hs k i, ValidPool true (roots g) (target g) p := by
  intro p hp
  obtain ⟨q, _, hq⟩ := List.mem_filterMap.mp hp
  cases hd : ds[q &&& 255]? with
  | none => simp [fromHint, hd] at hq
  | some v =>
    let cs := purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g)
    cases hm : makePool true v.1 (roots g) cs with
    | none => simp [fromHint, hd, ←show purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g) = cs from rfl, cs] at hm; simp [fromHint, hd, hm] at hq
    | some bank =>
      have eq : (⟨v.1,v.2,cs.length,bank⟩ : BoundPool) = p := by
        simpa [fromHint, hd, ←show purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g) = cs from rfl, hm, cs] using hq
      rw [←eq]
      exact build_valid (safe v (List.mem_of_getElem? hd)) cs hm

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let i := locate g k tag
  if i < count g k then [vals g k i] else []

noncomputable def checkRow (g : Atlas) (ds : Catalog) (hs : Hints) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  decide vs.Nodup && !vs.contains (target g) &&
    testAll (k,ws.length,ws,preCov true ws,pools g ds hs k i,links g (k-1)) ws

def Ready (g : Atlas) (ds : Catalog) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧ SafeCatalog g ds

theorem checked {g ds hs r s} (ready : Ready g ds r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g ds hs l i=true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hk : k=0
    · subst k
      intro n cap run
      have : n=0 := by omega
      subst n
      have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
      exact h.1.2 (List.mem_toFinset.mp hm)
    apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 (pools_valid ready.2.2 hs k i) _ h.2
    · intro a ha
      exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
    · intro tag xs hx
      simp only [links] at hx
      split at hx
      next le =>
        obtain rfl := List.mem_singleton.mp hx
        exact ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le
      next => simp at hx

def Complete (g : Atlas) (ds : Catalog) (hs : Hints) :=
  ∀ k ≤ top g, ∀ i < count g k, checkRow g ds hs k i=true

theorem frozen {g ds hs p n} (ready : Ready g ds p n) (complete : Complete g ds hs)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem lowerNeg {roots T k} (low : Lower true roots T k) : Lower true roots (neg T) k := by
  intro p bank hr hav
  rw [obs_neg] at hav
  have h := avail_inv (u:=true) rfl hav
  rw [inv_inv'] at h
  exact low p bank hr h

def identifyRows (i j : Nat) (sign : Bool) : List Move :=
  let a := inputs.getD i zero
  let b := if sign then neg (inputs.getD j zero) else inputs.getD j zero
  [(neg a &&& b, a &&& neg b, Fin.ofNat 512 (1 <<< i))]

def freeSigned (base : List Sig) (w : Sig) :=
  freeWord base w || freeWord base (neg w)

theorem signedFree {base w} (h : freeSigned base w=true) :
    Available true (base.map observe) (observe w) := by
  simp only [freeSigned,Bool.or_eq_true] at h
  rcases h with h | h
  · exact freeWord_ok h
  · have hx := avail_inv (u:=true) rfl (freeWord_ok (u:=true) h)
    simpa only [obs_neg,inv_inv'] using hx

def signedMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeSigned base (movedWord ms a))

theorem signedMapCorrect {ms raw T base G} (ok : signedMap ms raw T base G=true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available true (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [signedMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => signedFree (ok.2 a ha)⟩

theorem signedSlice {ms raw T base G L d} (ok : signedMap ms raw T base G=true)
    (all : movedWord ms d=one) (pg : proper G) (low : Lower true base G L) :
    Slice true raw T d L := by
  obtain ⟨eq,supp⟩ := signedMapCorrect ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper pg
  · rw [obs]
    exact low

def flipInput (j : Nat) : Move :=
  let a := inputs.getD j zero
  (neg a,a,Fin.ofNat 512 (1 <<< j))

def field (ws : Nat → Nat) (pos width : Nat) : Nat :=
  let r := pos % 60
  let low := (ws (pos / 60)) >>> r
  let value := if r+width ≤ 60 then low else low ||| ((ws (pos/60+1)) <<< (60-r))
  value &&& ((1 <<< width)-1)

def hashRow (n b spec tag : Nat) : Nat :=
  if n<2 then 0 else if spec % 2 = 1 then spec / 2 else
   (tag / b % n + (spec / 2) * (1+(tag/(b*n) % (n-1)))) % n

def repeatWord (v : Nat) : Sig := BitVec.ofNat 512 (v * ((2 ^ 512 - 1) / (2 ^ 64 - 1)))

def big (v : List Nat) : Nat := v.foldr (fun w rest => w ||| (rest <<< 60)) 0

def hintsAt (words : Nat → Nat) (rowBase rowWidth listBase listWidth dictBase dictWidth i : Nat) : List Nat :=
  let start := field words (rowBase + i*rowWidth) rowWidth
  let stop := field words (rowBase + (i+1)*rowWidth) rowWidth
  (List.range (stop-start)).map fun j =>
    let h := field words (listBase + (start+j)*listWidth) listWidth
    field words (dictBase + h*dictWidth) dictWidth

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def page0 : List Nat := [0x90109b8a868107, 0x43c042100211f35, 0x18860084bc94340, 0x8041c4320c421e8, 0xce9403408790641, 0x910c84400123040, 0x864105f8a041128, 0x1d842105f20063d, 0x417868085f8a06, 0x92061f060085e1a, 0xfa10821f060105f, 0x87c10021e86210, 0x62185e120217e48, 0x7e4818fa18821b8, 0x657c8010f619043, 0xa0437c82195f200, 0xf9a043b86418de1, 0x85f9a0417e68085, 0x5bb6000001b8641, 0x18f8005601600, 0xa0e2a46980e8000, 0x6290821001c87c, 0xf7ad671841cc521, 0xb59339ad6b58bde]
def page1 : List Nat := [0x65f08224dc4e7a3, 0x61f043e18fc21f8, 0x62080e4b00004f8, 0xe7246e4a76c6290, 0xf4fa7d3fc90727c, 0x4c3f887f21fa409, 0xcc7f087c32f861f, 0x4cbf18fe21f841f, 0xa248a88005b801f, 0x163447c4a6b6c91, 0x1424fe9e9f63446, 0x42502fea4a05fd4, 0xa808bcbf22a41bd, 0xd42fc31fd40fd20, 0xba9876543210c4f, 0x70ca6204f272ce0, 0xa6043ee553350e9, 0x144688fe90e2c2e, 0x8d1]
def storagePage (p : Nat) : List Nat := (if p < 1 then page0 else page1)
def storageWord (i : Nat) := (storagePage (i / 24)).getD (i % 24) 0
def a0Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbf67bf67bf67bf6, 0xf67bf67bf67bf67, 0xf67bf67b])
  | 4 => BitVec.ofNat 152 (big [0x7ddb7ddb7ddb7dd, 0xddb7ddb7ddb7ddb, 0xddb7ddb7])
  | 5 => BitVec.ofNat 152 (big [0x94209420942094, 0x942094209420942, 0x94209420])
  | _ => 0

def a0Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x206820682068206, 0x68206820682068, 0x6820682])
  | 4 => BitVec.ofNat 152 (big [0x118411841184118, 0x184118411841184, 0x18411841])
  | 5 => BitVec.ofNat 152 (big [0xf9edf9edf9edf9e, 0x9edf9edf9edf9ed, 0x9edf9edf])
  | _ => 0

def a0Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a0Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (0+i*3) 3
  | _ => 0

def a0Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a0Hints : Hints := fun _ _ => []
def a0 : Atlas := ⟨3,rawDecor 49 a0Pos a0Neg,repeatWord 12297641736783506090,a0Count,a0Rec,(fun _ _ => 0),a0Loc⟩
def a0Domains : Catalog := []
def a1Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x4f4ff7efbfbefe9, 0xfa7a7fbf7dfdf7f, 0xdfbefefb])
  | 1 => BitVec.ofNat 152 (big [0xffb7af7edffde5f, 0x97fdbd7bf6ffef2, 0xbdfb7ff7])
  | 3 => BitVec.ofNat 152 (big [0xbefcddfff4ff5f7, 0x7df7e6efffa7faf, 0x77ffd3fd])
  | 4 => BitVec.ofNat 152 (big [0xf3fffeb1ff5fbbe, 0xef9ffff58ffafdd, 0xfac7fd7e])
  | _ => 0

def a1Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x48b0165025982e9, 0xba4580b2812cc17, 0x59409660])
  | 1 => BitVec.ofNat 152 (big [0xd06250aa9211c5a, 0x1683128554908e2, 0x42aa4847])
  | 3 => BitVec.ofNat 152 (big [0xa913c300106e535, 0x4d489e180083729, 0xc0041b9])
  | 4 => BitVec.ofNat 152 (big [0x340501d9cc04b86, 0xe1a0280ece6025c, 0x7673012])
  | _ => 0

def a1Count (k : Nat) : Nat :=
  match k with
  | 3 => 8
  | 4 => 28
  | 5 => 6
  | 6 => 1
  | _ => 0

def a1Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (3+i*37) 37
  | 4 => field storageWord (373+i*26) 26
  | 5 => field storageWord (1478+i*15) 15
  | 6 => field storageWord (1683+i*4) 4
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 8 4 (field storageWord (299+(tag % 4)*4) 4) tag
  | 4 => hashRow 28 28 (field storageWord (1101+(tag % 28)*6) 6) tag
  | 5 => hashRow 6 6 (field storageWord (1568+(tag % 6)*4) 4) tag
  | 6 => 0
  | _ => 0

def a1Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 321 4 357 2 315 2 i
  | 4 => hintsAt storageWord 1277 5 1422 2 1269 2 i
  | 5 => hintsAt storageWord 1600 5 1635 2 1592 2 i
  | 6 => hintsAt storageWord 1695 3 1701 2 1687 2 i
  | _ => []

def a1 : Atlas := ⟨6,rawDecor 27 a1Pos a1Neg,repeatWord 17188137515442800640,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := [(repeatWord 12297829382473034410, 4), (repeatWord 14757395258967641292, 4), (repeatWord 18374966859414961920, 4), (repeatWord 18446462603027742720, 4)]
def a2Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | 2 => BitVec.ofNat 152 (big [0xfeef997cdd09afd, 0x4bbdf55bf0f0b5d, 0xb2496de3])
  | 3 => BitVec.ofNat 152 (big [0x3d9c7f92ff7330e, 0xfdd6a3dddd33ef4, 0xd9fa9556])
  | 4 => BitVec.ofNat 152 (big [0xb353b8d73ab7ca5, 0x3d7b5bedd34ffaf, 0x649d7afe])
  | 5 => BitVec.ofNat 152 (big [0xdee167afa0dd772, 0xf6906dfebfad937, 0xafefc3af])
  | _ => 0

def a2Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xc21694031ae19b, 0x4110f00302341, 0x3084412])
  | 2 => BitVec.ofNat 152 (big [0x72ce118c8c01a7d, 0x81e4642db8d039e, 0xd5a51a87])
  | 3 => BitVec.ofNat 152 (big [0x35980e964f53206, 0x86007f0469f9894, 0x6c19960])
  | 4 => BitVec.ofNat 152 (big [0xe309b49612b1ca4, 0x19126d4a104ccbe, 0xf4c2ba65])
  | 5 => BitVec.ofNat 152 (big [0xf94004a5a05d760, 0x633706069cb983b, 0x846f3c74])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (1709+i*5) 5
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a2Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 1715 1 1717 1 1714 1 i
  | _ => []

def a2 : Atlas := ⟨7,rawDecor 62 a2Pos a2Neg,repeatWord 14757395207427244032,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := [(repeatWord 14757395258967641292, 7)]
def a3Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb55c3beda8b889c, 0xf1882b7ee9e455, 0x37dffdc7])
  | 2 => BitVec.ofNat 152 (big [0xd06be747f02056f, 0xbaf1aef3d02fa2b, 0x7fe4bcad])
  | 3 => BitVec.ofNat 152 (big [0x7db9c23c058f051, 0xf77cdcc5274c9fc, 0xafff7b5f])
  | 4 => BitVec.ofNat 152 (big [0x4a6519ba7a55ba0, 0xf40ad1febcf9797, 0xefcb8db9])
  | 5 => BitVec.ofNat 152 (big [0x8f868cb7f7c2e0a, 0xb2dfa17f25c3968, 0xfcf26636])
  | _ => 0

def a3Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x21003e24a6a8888, 0x4012a420a045a05, 0x42600301])
  | 2 => BitVec.ofNat 152 (big [0xc04800020000505, 0x830410080010020, 0xa0110c00])
  | 3 => BitVec.ofNat 152 (big [0x100100000003050, 0x180101851000558, 0x14000000])
  | 4 => BitVec.ofNat 152 (big [0x82401081014220, 0x20880a100308000, 0x4000])
  | 5 => BitVec.ofNat 152 (big [0x2400b4b567c080a, 0x20c042cc65800, 0x28c8144])
  | _ => 0

def a3Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a3Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (1718+i*5) 5
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 1724 1 1726 1 1723 1 i
  | _ => []

def a3 : Atlas := ⟨7,rawDecor 61 a3Pos a3Neg,repeatWord 18446744009284713120,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 6148914691236517205, 7)]
def a4Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbf7f6bac7d479fc, 0x59ffdded7fd03bf, 0xf3b7cdf6])
  | 1 => BitVec.ofNat 152 (big [0x6afbfedf8fb8e9f, 0xbe45ffd3c9afc6f, 0x6effb769])
  | 3 => BitVec.ofNat 152 (big [0xd6eef57d4eb77ea, 0xfaf37bfd85f36fe, 0xeff979d7])
  | 4 => BitVec.ofNat 152 (big [0xafdb0bf3f35cf35, 0xf59f8e77fa7f9d7, 0x7927f7b9])
  | 5 => BitVec.ofNat 152 (big [0x712df4f3b0ebae3, 0x776cbdaeff4dfdb, 0x9e6c5b1e])
  | _ => 0

def a4Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1a1ea10854468dc, 0xe6804c0169c8199, 0xd00a2290])
  | 1 => BitVec.ofNat 152 (big [0x484fc8958998c9a, 0xa4002180898e104, 0xd19d1496])
  | 3 => BitVec.ofNat 152 (big [0x82e054504e33322, 0x114110741411a3a, 0x2940656d])
  | 4 => BitVec.ofNat 152 (big [0xa50012e2b304725, 0x10263071d4208c6, 0x20708020])
  | 5 => BitVec.ofNat 152 (big [0xa82db02120e9ae1, 0x23a2d89e16c9d43, 0x62a2835b])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (1727+i*5) 5
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a4Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 1733 1 1735 1 1732 1 i
  | _ => []

def a4 : Atlas := ⟨7,rawDecor 59 a4Pos a4Neg,repeatWord 17216960113253320704,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := [(repeatWord 4294967295, 7)]
def a5Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbc7fff7aff6e253, 0x46fdfffbde5f0be, 0x7be9fbfe])
  | 1 => BitVec.ofNat 152 (big [0x6bbd47bf42b9fbf, 0xfb4f67753ba2f79, 0xcf9ffead])
  | 2 => BitVec.ofNat 152 (big [0xf5c75ee869d74dc, 0x7de09f9ef5be7ff, 0xd5e4ffc7])
  | 3 => BitVec.ofNat 152 (big [0xcbedf157bcabd26, 0xcaba37bb29c1f9b, 0xab5edf59])
  | 4 => BitVec.ofNat 152 (big [0xefd8bdef9ed0be9, 0xbdd7477d46e1d60, 0x343bf7ba])
  | _ => 0

def a5Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1068d128570a043, 0xe6130301d208088, 0x44c1001])
  | 1 => BitVec.ofNat 152 (big [0x298546194230f1e, 0x83cc165a004100, 0x4608291])
  | 2 => BitVec.ofNat 152 (big [0x2683084028c5498, 0x60449800a7677, 0x52b3a940])
  | 3 => BitVec.ofNat 152 (big [0xce4c2002b8ab124, 0x5473a9a0989b5c, 0x13864200])
  | 4 => BitVec.ofNat 152 (big [0xd71215e68cd0ae1, 0xa3c834b00441660, 0x40115458])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (1736+i*5) 5
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a5Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 1742 1 1744 1 1741 1 i
  | _ => []

def a5 : Atlas := ⟨7,rawDecor 31 a5Pos a5Neg,repeatWord 17215265353524373664,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := [(repeatWord 14757395258967641292, 7)]
def a6Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x69abdefe4aa7fa4, 0x9abdefe4aa7fa4d, 0xaa7fa4d6])
  | 2 => BitVec.ofNat 152 (big [0xffff7fbbfffeedb, 0xfff7fbbfffeedbe, 0xffeedbef])
  | 4 => BitVec.ofNat 152 (big [0xbc7be575c5cf57c, 0xc7be575c5cf57c5, 0x5cf57c5b])
  | 5 => BitVec.ofNat 152 (big [0xaf75d8c7f995937, 0xf75d8c7f995937b, 0x995937ba])
  | _ => 0

def a6Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9447280a5427f04, 0x447280a5427f042, 0x427f0429])
  | 2 => BitVec.ofNat 152 (big [0x40900100089, 0x409001000891, 0x10008910])
  | 4 => BitVec.ofNat 152 (big [0x43680a24e4e0570, 0x3680a24e4e0570a, 0x4e0570a4])
  | 5 => BitVec.ofNat 152 (big [0x5d8a014938c4836, 0xd8a014938c48364, 0x8c483645])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (1745+i*15) 15
  | 5 => field storageWord (2015+i*4) 4
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 6 (field storageWord (1925+(tag % 6)*5) 5) tag
  | 5 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 1964 3 2003 2 1955 3 i
  | 5 => hintsAt storageWord 2037 3 2043 3 2019 3 i
  | _ => []

def a6 : Atlas := ⟨5,rawDecor 53 a6Pos a6Neg,repeatWord 18085032171284766880,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 6510615555426900570, 4), (repeatWord 12297735558912431445, 4), (repeatWord 12297829381041378645, 4), (repeatWord 1085350949055099120, 4), (repeatWord 1085102596360827120, 4), (repeatWord 18446462598732906495, 4)]
def a7Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | 2 => BitVec.ofNat 152 (big [0x9ebbbef6fdf99eb, 0xdf99ebbbef6fdf9, 0xebbbef6f])
  | 4 => BitVec.ofNat 152 (big [0x75edf96fb7fe75e, 0x7fe75edf96fb7fe, 0x5edf96fb])
  | 5 => BitVec.ofNat 152 (big [0xfb57e7bdef97fb5, 0xf97fb57e7bdef97, 0xb57e7bde])
  | _ => 0

def a7Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xaf8015208708af8, 0x708af8015208708, 0xf8015208])
  | 2 => BitVec.ofNat 152 (big [0x12b4498c74a512b, 0x4a512b4498c74a5, 0x2b4498c7])
  | 4 => BitVec.ofNat 152 (big [0x746226c801f5746, 0x1f5746226c801f5, 0x46226c80])
  | 5 => BitVec.ofNat 152 (big [0x1958da40a837195, 0x8371958da40a837, 0x958da40a])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2061+i*4) 4
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a7Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2066 1 2068 1 2065 1 i
  | _ => []

def a7 : Atlas := ⟨4,rawDecor 54 a7Pos a7Neg,repeatWord 14757382013086334976,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := [(repeatWord 14757395258967641292, 4)]
def a8Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdffeefbffe7dd7e, 0xdffeefbffe7dd7e, 0xffe7dd7e])
  | 1 => BitVec.ofNat 152 (big [0x79ddd3f17bc7fc5, 0x79ddd3f17bc7fc5, 0x17bc7fc5])
  | 2 => BitVec.ofNat 152 (big [0xbeeffeffddbfbbb, 0xbeeffeffddbfbbb, 0xfddbfbbb])
  | 4 => BitVec.ofNat 152 (big [0xf3f9796b63d76f5, 0xf3f9796b63d76f5, 0xb63d76f5])
  | _ => 0

def a8Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x22451005a811c26, 0x22451005a811c26, 0x5a811c26])
  | 1 => BitVec.ofNat 152 (big [0x8639a420904f9c5, 0x8639a420904f9c5, 0x904f9c5])
  | 2 => BitVec.ofNat 152 (big [0x409021b84508398, 0x409021b84508398, 0x84508398])
  | 4 => BitVec.ofNat 152 (big [0xc26d1874684671, 0xc26d1874684671, 0x74684671])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2069+i*4) 4
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2074 1 2076 1 2073 1 i
  | _ => []

def a8 : Atlas := ⟨4,rawDecor 23 a8Pos a8Neg,repeatWord 16782840624358924448,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 14757395258967641292, 4)]
def a9Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xe5efe5efe5efe5e, 0x5efe5efe5efe5ef, 0x5efe5efe])
  | 2 => BitVec.ofNat 152 (big [0xa5c9a5c9a5c9a5c, 0x5c9a5c9a5c9a5c9, 0x5c9a5c9a])
  | 4 => BitVec.ofNat 152 (big [0x7ebe7ebe7ebe7eb, 0xebe7ebe7ebe7ebe, 0xebe7ebe7])
  | _ => 0

def a9Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xc600c600c600c6, 0xc600c600c600c60, 0xc600c600])
  | 2 => BitVec.ofNat 152 (big [0xb386b386b386b38, 0x386b386b386b386, 0x386b386b])
  | 4 => BitVec.ofNat 152 (big [0x828282828282828, 0x282828282828282, 0x28282828])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (2077+i*3) 3
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a9Hints : Hints := fun _ _ => []
def a9 : Atlas := ⟨2,rawDecor 22 a9Pos a9Neg,repeatWord 14974399220382941376,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := []
def a10Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xf77f7fef7ef7ff2, 0xf77f7fef7ef7ff2, 0xf7ef7ff2])
  | 2 => BitVec.ofNat 152 (big [0x96512f0e6e336d2, 0x96512f0e6e336d2, 0xe6e336d2])
  | 4 => BitVec.ofNat 152 (big [0xefeff7fbfdfc9ef, 0xefeff7fbfdfc9ef, 0xbfdfc9ef])
  | 5 => BitVec.ofNat 152 (big [0xbaf6bc579b3f75d, 0xbaf6bc579b3f75d, 0x79b3f75d])
  | _ => 0

def a10Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xa2081220c4ef02, 0xa2081220c4ef02, 0x20c4ef02])
  | 2 => BitVec.ofNat 152 (big [0x69bf049b23712d6, 0x69bf049b23712d6, 0xb23712d6])
  | 4 => BitVec.ofNat 152 (big [0x1114208951210ec, 0x1114208951210ec, 0x951210ec])
  | 5 => BitVec.ofNat 152 (big [0x4543417d0819555, 0x4543417d0819555, 0xd0819555])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2080+i*4) 4
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2085 1 2087 1 2084 1 i
  | _ => []

def a10 : Atlas := ⟨4,rawDecor 54 a10Pos a10Neg,repeatWord 14974399220332363776,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 18446744069414584320, 3)]
def a11Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe9fa2f7bfc0dedb, 0xd3cfd7fed476fed, 0xf9e767fb])
  | 1 => BitVec.ofNat 152 (big [0xf627db878bff527, 0xaef8f83dffcdb56, 0xded8bf07])
  | 2 => BitVec.ofNat 152 (big [0x7d59eefce7b37c9, 0xe0a7fd67e7f797f, 0x3dbeee3b])
  | 4 => BitVec.ofNat 152 (big [0xf6e7552f1bcea7e, 0xffff9af89f9b7ea, 0xcec91dfe])
  | 5 => BitVec.ofNat 152 (big [0x9ec6b8a7f275974, 0xfd7ab6f779b95b4, 0x8791f8cf])
  | _ => 0

def a11Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x810231384c05c1a, 0xf948a80d474315, 0x20902228])
  | 1 => BitVec.ofNat 152 (big [0xd021394708df505, 0x905388580c8955, 0x20c20d81])
  | 2 => BitVec.ofNat 152 (big [0x6cd486c4a3a03c1, 0x102a01260203022, 0x18401056])
  | 4 => BitVec.ofNat 152 (big [0x3696c032130a27e, 0xf449a07a0702468, 0x41280004])
  | 5 => BitVec.ofNat 152 (big [0x1c4b901f275860, 0x821815f27bd3190, 0xf51c13f2])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 5 => 4
  | 6 => 4
  | 7 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (2088+i*27) 27
  | 6 => field storageWord (2220+i*16) 16
  | 7 => field storageWord (2437+i*5) 5
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 4 2 (field storageWord (2196+(tag % 2)*3) 3) tag
  | 6 => hashRow 4 4 (field storageWord (2284+(tag % 4)*2) 2) tag
  | 7 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 2208 2 2218 1 2202 3 i
  | 6 => hintsAt storageWord 2340 5 2365 4 2292 4 i
  | 7 => hintsAt storageWord 2466 3 2472 3 2442 4 i
  | _ => []

def a11 : Atlas := ⟨7,rawDecor 55 a11Pos a11Neg,repeatWord 17216945682068840608,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 12297735558912431445, 6), (repeatWord 14106333703424951235, 6), (repeatWord 6148914691236517205, 5), (repeatWord 14757395258967641292, 5), (repeatWord 1085102592571150095, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 6510615555426900570, 5), (repeatWord 4919131752989213764, 4), (repeatWord 3435973836, 4), (repeatWord 1085086035472220160, 4), (repeatWord 4294901760, 4)]
def a12Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfd3274ebd3f14db, 0xbeff78f2da9ae61, 0xcbf7bd8d])
  | 1 => BitVec.ofNat 152 (big [0x42ef8f553c9ff64, 0x5d5ba70f756759e, 0xff48f6fa])
  | 2 => BitVec.ofNat 152 (big [0xe19fe0ce7e0a23a, 0xcef22383cfd33db, 0x77ae0237])
  | 3 => BitVec.ofNat 152 (big [0x5d8fd30a4e55b4, 0x940a4f7f21fd86e, 0x9a175dca])
  | 4 => BitVec.ofNat 152 (big [0xfba813b50b38bdd, 0xff3ddeb611644d7, 0x95daeb30])
  | 5 => BitVec.ofNat 152 (big [0x3ec75a98814f873, 0xf3f49d7f6678da8, 0x707b966a])
  | _ => 0

def a12Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x28120461c271443, 0x303200200892820, 0x814030c4])
  | 1 => BitVec.ofNat 152 (big [0x26785451c85940, 0x195a21041000432, 0x6b486069])
  | 2 => BitVec.ofNat 152 (big [0xc189608a3c0a238, 0xcec09213c7001cb, 0x14a70211])
  | 3 => BitVec.ofNat 152 (big [0x8598f81020e45b4, 0x60c0f5b0155044, 0x12370f06])
  | 4 => BitVec.ofNat 152 (big [0xf9a813b40318a9c, 0x8605d4db8b645c1, 0x84128320])
  | 5 => BitVec.ofNat 152 (big [0x6c65a98810b073, 0xd234987f636c169, 0x542db74a])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 9 => field storageWord (2490+i*6) 6
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 9 => 0
  | _ => 0

def a12Hints (k i : Nat) : List Nat :=
  match k with
  | 9 => hintsAt storageWord 2511 3 2517 3 2496 3 i
  | _ => []

def a12 : Atlas := ⟨9,rawDecor 63 a12Pos a12Neg,repeatWord 17216961075332311200,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := [(repeatWord 6148914691236517205, 8), (repeatWord 14757395258967641292, 8), (repeatWord 1085102592571150095, 8), (repeatWord 4294967295, 8), (repeatWord 71777214294589695, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0S3P0 : segment (checkRow a0 a0Domains a0Hints 3) 0 1 = true := by decide +kernel
theorem a0S3 (j : Nat) (hj : j < 1) : (checkRow a0 a0Domains a0Hints 3) j = true := by
  exact segmentRange a0S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Complete : Complete a0 a0Domains a0Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a0S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S3P0 : segment (checkRow a1 a1Domains a1Hints 3) 0 8 = true := by decide +kernel
theorem a1S3 (j : Nat) (hj : j < 8) : (checkRow a1 a1Domains a1Hints 3) j = true := by
  exact segmentRange a1S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P0 : segment (checkRow a1 a1Domains a1Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P1 : segment (checkRow a1 a1Domains a1Hints 4) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P2 : segment (checkRow a1 a1Domains a1Hints 4) 20 8 = true := by decide +kernel
theorem a1S4 (j : Nat) (hj : j < 28) : (checkRow a1 a1Domains a1Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a1S4P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 20
    ·
      exact segmentRange a1S4P1 j (by omega) (by omega)
    ·
      exact segmentRange a1S4P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S5P0 : segment (checkRow a1 a1Domains a1Hints 5) 0 6 = true := by decide +kernel
theorem a1S5 (j : Nat) (hj : j < 6) : (checkRow a1 a1Domains a1Hints 5) j = true := by
  exact segmentRange a1S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S6P0 : segment (checkRow a1 a1Domains a1Hints 6) 0 1 = true := by decide +kernel
theorem a1S6 (j : Nat) (hj : j < 1) : (checkRow a1 a1Domains a1Hints 6) j = true := by
  exact segmentRange a1S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Complete : Complete a1 a1Domains a1Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a1S3 j hj
  · exact a1S4 j hj
  · exact a1S5 j hj
  · exact a1S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2S7P0 : segment (checkRow a2 a2Domains a2Hints 7) 0 1 = true := by decide +kernel
theorem a2S7 (j : Nat) (hj : j < 1) : (checkRow a2 a2Domains a2Hints 7) j = true := by
  exact segmentRange a2S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Complete : Complete a2 a2Domains a2Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a2S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S7P0 : segment (checkRow a3 a3Domains a3Hints 7) 0 1 = true := by decide +kernel
theorem a3S7 (j : Nat) (hj : j < 1) : (checkRow a3 a3Domains a3Hints 7) j = true := by
  exact segmentRange a3S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Complete : Complete a3 a3Domains a3Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a3S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S7P0 : segment (checkRow a4 a4Domains a4Hints 7) 0 1 = true := by decide +kernel
theorem a4S7 (j : Nat) (hj : j < 1) : (checkRow a4 a4Domains a4Hints 7) j = true := by
  exact segmentRange a4S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Complete : Complete a4 a4Domains a4Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a4S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S7P0 : segment (checkRow a5 a5Domains a5Hints 7) 0 1 = true := by decide +kernel
theorem a5S7 (j : Nat) (hj : j < 1) : (checkRow a5 a5Domains a5Hints 7) j = true := by
  exact segmentRange a5S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Complete : Complete a5 a5Domains a5Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a5S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P0 : segment (checkRow a6 a6Domains a6Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P1 : segment (checkRow a6 a6Domains a6Hints 4) 10 2 = true := by decide +kernel
theorem a6S4 (j : Nat) (hj : j < 12) : (checkRow a6 a6Domains a6Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a6S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a6S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P0 : segment (checkRow a6 a6Domains a6Hints 5) 0 1 = true := by decide +kernel
theorem a6S5 (j : Nat) (hj : j < 1) : (checkRow a6 a6Domains a6Hints 5) j = true := by
  exact segmentRange a6S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Complete : Complete a6 a6Domains a6Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a6S4 j hj
  · exact a6S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S4P0 : segment (checkRow a7 a7Domains a7Hints 4) 0 1 = true := by decide +kernel
theorem a7S4 (j : Nat) (hj : j < 1) : (checkRow a7 a7Domains a7Hints 4) j = true := by
  exact segmentRange a7S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Complete : Complete a7 a7Domains a7Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a7S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P0 : segment (checkRow a8 a8Domains a8Hints 4) 0 1 = true := by decide +kernel
theorem a8S4 (j : Nat) (hj : j < 1) : (checkRow a8 a8Domains a8Hints 4) j = true := by
  exact segmentRange a8S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Complete : Complete a8 a8Domains a8Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a8S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P0 : segment (checkRow a9 a9Domains a9Hints 2) 0 1 = true := by decide +kernel
theorem a9S2 (j : Nat) (hj : j < 1) : (checkRow a9 a9Domains a9Hints 2) j = true := by
  exact segmentRange a9S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Complete : Complete a9 a9Domains a9Hints := by
  intro k hk j hj
  change k ≤ 2 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S2 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S4P0 : segment (checkRow a10 a10Domains a10Hints 4) 0 1 = true := by decide +kernel
theorem a10S4 (j : Nat) (hj : j < 1) : (checkRow a10 a10Domains a10Hints 4) j = true := by
  exact segmentRange a10S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Complete : Complete a10 a10Domains a10Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a10S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S5P0 : segment (checkRow a11 a11Domains a11Hints 5) 0 4 = true := by decide +kernel
theorem a11S5 (j : Nat) (hj : j < 4) : (checkRow a11 a11Domains a11Hints 5) j = true := by
  exact segmentRange a11S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S6P0 : segment (checkRow a11 a11Domains a11Hints 6) 0 4 = true := by decide +kernel
theorem a11S6 (j : Nat) (hj : j < 4) : (checkRow a11 a11Domains a11Hints 6) j = true := by
  exact segmentRange a11S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S7P0 : segment (checkRow a11 a11Domains a11Hints 7) 0 1 = true := by decide +kernel
theorem a11S7 (j : Nat) (hj : j < 1) : (checkRow a11 a11Domains a11Hints 7) j = true := by
  exact segmentRange a11S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Complete : Complete a11 a11Domains a11Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a11S5 j hj
  · exact a11S6 j hj
  · exact a11S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S9P0 : segment (checkRow a12 a12Domains a12Hints 9) 0 1 = true := by decide +kernel
theorem a12S9 (j : Nat) (hj : j < 1) : (checkRow a12 a12Domains a12Hints 9) j = true := by
  exact segmentRange a12S9P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Complete : Complete a12 a12Domains a12Hints := by
  intro k hk j hj
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a12S9 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Bound : Lower true (roots a0) (target a0) 4 := by
  have ready : Ready a0 a0Domains (asRow a0Pos) (asRow a0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a0
  exact frozen ready a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D0 : Slice true (roots a1) (target a1) (repeatWord 12297829382473034410) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 67, swapRows 84, flipInput 1, flipInput 3] ++ fixRows 0 1)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D1 : Slice true (roots a1) (target a1) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 0 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D2 : Slice true (roots a1) (target a1) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D3 : Slice true (roots a1) (target a1) (repeatWord 18446462603027742720) 4 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 83, flipInput 0, flipInput 1] ++ fixRows 0 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 7 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a1D0 (safeCons a1D1 (safeCons a1D2 (safeCons a1D3 (safeNil a1))))
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D0 : Slice true (roots a2) (target a2) (repeatWord 14757395258967641292) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 2)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 8 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a2D0 (safeNil a2)
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14), (inputs.getD 2 zero, 10, 14), (inputs.getD 3 zero, 6, 14), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 6148914691236517205) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 8 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeNil a3)
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4D0 : Slice true (roots a4) (target a4) (repeatWord 4294967295) 7 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 8 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a4D0 (safeNil a4)
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D0 : Slice true (roots a5) (target a5) (repeatWord 14757395258967641292) 7 :=
  signedSlice (ms := ([swapRows 33, flipInput 0, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 2)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 8 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a5D0 (safeNil a5)
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 9, 11), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 6510615555426900570) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D1 : Slice true (roots a6) (target a6) (repeatWord 12297735558912431445) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D2 : Slice true (roots a6) (target a6) (repeatWord 12297829381041378645) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D3 : Slice true (roots a6) (target a6) (repeatWord 1085350949055099120) 4 :=
  signedSlice (ms := ([flipInput 0] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D4 : Slice true (roots a6) (target a6) (repeatWord 1085102596360827120) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 5 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D5 : Slice true (roots a6) (target a6) (repeatWord 18446462598732906495) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, flipInput 0, flipInput 2] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 6 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeCons a6D1 (safeCons a6D2 (safeCons a6D3 (safeCons a6D4 (safeCons a6D5 (safeNil a6))))))
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D0 : Slice true (roots a7) (target a7) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 0 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 5 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a7D0 (safeNil a7)
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22), (inputs.getD 2 zero, 18, 22), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 0 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 5 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeNil a8)
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 17, 19), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 3 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a9
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 18446744069414584320) 3 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 5 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeNil a10)
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18), (inputs.getD 2 zero, 34, 38), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 12297735558912431445) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 66] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D1 : Slice true (roots a11) (target a11) (repeatWord 14106333703424951235) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 false)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D2 : Slice true (roots a11) (target a11) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D3 : Slice true (roots a11) (target a11) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 83, swapRows 84, flipInput 0, flipInput 2, flipInput 4, flipInput 5] ++ fixRows 0 2)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D4 : Slice true (roots a11) (target a11) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 65] ++ fixRows 4 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D5 : Slice true (roots a11) (target a11) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 84, flipInput 0, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 0 16)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D6 : Slice true (roots a11) (target a11) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D7 : Slice true (roots a11) (target a11) (repeatWord 6510615555426900570) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D8 : Slice true (roots a11) (target a11) (repeatWord 4919131752989213764) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 1 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D9 : Slice true (roots a11) (target a11) (repeatWord 3435973836) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 32 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D10 : Slice true (roots a11) (target a11) (repeatWord 1085086035472220160) 4 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, flipInput 0, flipInput 1] ++ fixRows 4 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D11 : Slice true (roots a11) (target a11) (repeatWord 4294901760) 4 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 32 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 8 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeCons a11D1 (safeCons a11D2 (safeCons a11D3 (safeCons a11D4 (safeCons a11D5 (safeCons a11D6 (safeCons a11D7 (safeCons a11D8 (safeCons a11D9 (safeCons a11D10 (safeCons a11D11 (safeNil a11))))))))))))
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 17, 19), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D0 : Slice true (roots a12) (target a12) (repeatWord 6148914691236517205) 8 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D1 : Slice true (roots a12) (target a12) (repeatWord 14757395258967641292) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 2)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D2 : Slice true (roots a12) (target a12) (repeatWord 1085102592571150095) 8 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D3 : Slice true (roots a12) (target a12) (repeatWord 4294967295) 8 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D4 : Slice true (roots a12) (target a12) (repeatWord 71777214294589695) 8 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 10 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a12D0 (safeCons a12D1 (safeCons a12D2 (safeCons a12D3 (safeCons a12D4 (safeNil a12)))))
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 9, 11), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a12
def fullWord := target a12
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008636128 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_41634.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[3,4]⟩, ⟨.or,[6,5]⟩, ⟨.and,[1,7]⟩, ⟨.or,[0,8]⟩, ⟨.and,[0,1]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,11]⟩, ⟨.or,[5,12]⟩, ⟨.and,[6,13]⟩, ⟨.or,[2,14]⟩, ⟨.and,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636128 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636128 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_41634
open PEqualNP.Outside.L_meta_41634 in
theorem PEqualNP.Outside.L_meta_41634 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636128 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636128 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a12Bound
