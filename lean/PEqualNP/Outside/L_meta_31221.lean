import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31221

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

theorem restoreInput {α : Type} [DecidableEq α] (U : Finset α) (a : α) :
    (if a ∈ U then insert a (U.erase a) else U.erase a) = U := by
  by_cases ha : a ∈ U
  · rw [if_pos ha, Finset.insert_erase ha]
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]

theorem restoreInputs {α : Type} [DecidableEq α] (U : Finset α) (a b : α) (hab : a ≠ b) :
    let s := (U.erase a).erase b
    let t := if b ∈ U then insert b s else s
    (if a ∈ U then insert a t else t) = U := by
  have member : b ∈ U.erase a ↔ b ∈ U := by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨Ne.symm hab, h⟩⟩
  have inner : (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U.erase a := by
    by_cases hb : b ∈ U
    · rw [if_pos hb, Finset.insert_erase (member.mpr hb)]
    · rw [if_neg hb, Finset.erase_eq_of_notMem (fun h => hb (member.mp h))]
  dsimp only
  rw [inner]
  exact restoreInput U a

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
      rw [kept_fin, kept_fin, er]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]

def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8

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
      rw [kept_fin, kept_fin, er, he, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne (Ne.symm hab), Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 7) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7)

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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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

def graphCutPairs (G : Sig) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let p := (1 : Nat) <<< i
    let witness := (List.range 9).find? fun j =>
      !G.getLsbD (1 <<< j) && G.getLsbD ((1 <<< j) ||| p)
    let r := if G.getLsbD p then 0 else (witness.map fun j => (1 : Nat) <<< j).getD 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| p))

def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := graphCutPairs (movedWord ms (chartGoal m)) s
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
  let xs := graphCutPairs (movedWord ms (chartGoal m)) s
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

abbrev Bits := BitVec 256

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1

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

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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

theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 7) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]

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
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 256) (hq : chartSamples m q = 0) :
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

def initialSegmentWidth (d : Nat) := 10*(d-1)

def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16

def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*initialSegmentWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*initialSegmentWidth d
    packedAt word (pre*initialSegmentWidth d) (initialSegmentWidth d) |||
      (last <<< initialSegmentWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
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

def K0 : List (Nat × Nat) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V0 : Known true K0 := baseKnown

def g49Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbde7,0x4062), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0xd7fc,0x208c), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7edb,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8411), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g49C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g49D3 (_ : Nat) : Nat := 0x7
def g49L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g49D3)
  | _ => emptyPacking
def g49I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g49 : Forest := ⟨49,3,fun i => g49Y[i]?.getD (0,0),g49C,[[]],g49L,g49I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49P3_0 : block g49 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49B3 : block g49 3 0 1 = true := g49P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49T : checkedTables g49 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g49B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound K0 V0) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown K0 4 [(49,[]),(50,[16]),(73,[67, 101]),(81,[101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) V0 low49 (by decide +kernel)

def g27Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffdfafafebc7ff6c7b,0xffffffffffffffffffffffffffffffffffffffffffffffff22502011c2012823), (0xadfa79bfb8e0bbb4,0x521302fd024158b4), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffe73d37abe33cda5d,0x18a2c30e142cc25c), (0x7edefbdf7dcbb7e6,0x80a8040235840740), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g27C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g27D3 (_ : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g27D3)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,[[]],g27L,g27I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27B3 : block g27 3 0 1 = true := g27P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g27B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K49 V49) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K49 4 [(27,[]),(43,[84]),(86,[32, 50, 83, 101]),(90,[32, 82, 101]),(99,[83, 100, 101]),(101,[33, 83, 100]),(116,[32, 81, 82, 99, 84, 101]),(120,[32, 81, 98, 83, 100]),(165,[33, 83, 100, 118]),(166,[32, 33, 83, 100, 118]),(170,[32, 33, 82, 83, 100, 118]),(195,[83, 100, 117, 118]),(198,[32, 83, 100, 117, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V49 low27 (by decide +kernel)

def g57Y : Array (Bits × Bits) := #[ (0x6fbeff7ff7b6367e,0x1000028004102068), (0x0,0x0), (0x0,0x0), (0x5cb3e6117ea4f5b4,0x23549d0c22ad9594), (0xffffffffffffffffffffffffffffffffffffffffffffffff9f53fbe7af79c99b,0xffffffffffffffffffffffffffffffffffffffffffffffffe0082c1720085093), (0xfffffffffffffffffffffffffffffffffffffffffffffffffa7f2fcab8fbefc1,0x582812898250f00), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g57C : List ColumnInfo := [(8,0,49,0,4)]
set_option maxRecDepth 100000 in
def g57D4 (_ : Nat) : Nat := 0x2f
def g57L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g57D4)
  | _ => emptyPacking
def g57I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g57 : Forest := ⟨57,4,fun i => g57Y[i]?.getD (0,0),g57C,[[]],g57L,g57I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g57P4_0 : block g57 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g57B4 : block g57 4 0 1 = true := g57P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g57B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=3) (before_sound K27 V27) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K27 5 [(57,[]),(77,[64, 50, 83, 84, 101]),(83,[64, 49, 50, 101]),(85,[64, 50, 84, 101]),(105,[67, 100, 101]),(114,[16, 65, 99]),(139,[64, 49, 50, 83, 84, 101, 118]),(169,[67, 100, 101, 118]),(210,[16, 65, 99, 117])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V27 low57 (by decide +kernel)

def g51Y : Array (Bits × Bits) := #[ (0xfffffffffffffffffffffffffffffffffffffffffffffffffeba2f7247fd914f,0xfffffffffffffffffffffffffffffffffffffffffffffffff1450a8429e88145), (0x6de7c8dfaaf44f4,0x92086446a48c4c4), (0x0,0x0), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffffdcbffd78b3bfe2d,0x208002900011228), (0xf7def2df5dc7bd2,0x80301080140812), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g51C : List ColumnInfo := [(2,0,49,0,4)]
set_option maxRecDepth 100000 in
def g51D4 (_ : Nat) : Nat := 0x2f
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g51D4)
  | _ => emptyPacking
def g51I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,[[]],g51L,g51I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : block g51 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51B4 : block g51 4 0 1 = true := g51P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g51B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K57 V57) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K57 5 [(51,[]),(89,[64, 33, 50, 67, 101]),(113,[64, 33, 50, 99, 84]),(178,[32, 65, 50, 99, 84, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V57 low51 (by decide +kernel)

def g103Y : Array (Bits × Bits) := #[ (0xffbfaddffb37357f09be9bf62c8aff7df3afac76ee6df4ba4a25b96ade39647d,0xffc0530800504a88f0208cb2c7780072521018043e4d22100825d88802292071), (0x5b9278ede92f7ed77fc68b72749c5765d5cec9338737f539f0625f1f983bd2,0x246f04103290a36d204cb04b0daca7aa388011788e23f0a900ec4819982352), (0x23f021bbbcffb97fe83439d16732ef5c6fbf64b55a4b54ec6a2fb17f47a2e6,0x5c0f9a45010013b00142de45eab4100a59b84991782a40887139b8174320e6), (0x0,0x0), (0x0,0x0), (0xffeefbaccf7ff66fffa7cbd15ebf5e7bb9dddfaba5f5b36379d6fb47e68759df,0x110043688004100245324830001300008424200020180252d80303e406588c), (0x7dd7fff5d4cdfb7a79fcffef47f38d7fe6f9545a5edcfeff6f05bd39feb628,0x22000aa2a00040c4c110138010809012400a04080d424628a040588949608), (0x0,0x0), (0x0,0x0) ]
def g103C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g103D4 (_ : Nat) : Nat := 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g103D4)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,[[]],g103L,g103I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103B4 : block g103 4 0 1 = true := g103P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g103B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1621) (before_sound K51 V51) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K51 5 [(230,[48, 81, 98, 67, 116]),(234,[48, 81, 66, 99, 116, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V51 low103 (by decide +kernel)

def g167Y : Array (Bits × Bits) := #[ (0xffffdb7c5fefdd8e05e5bbff21ceee759df9343c14d5677f94dc507f5b26acb5,0xffff248300b402515e180c20104252383cda8d4204c5010c60d0c0d95720a835), (0xffffbb9a9d94fff6ba5cc4b2fe177fe6e955f1dbce81b813477bffc8af59f843,0xffff4461606200c455b90aa0144020543398db20064c801b4101d2d82740f841), (0xffff0fff3adaada1d6361c1fccb5cbceabba0f64f9fa92853c4692ddb2c4931f,0xfffff011c4755a4c28b0352213562ad006e6d86983c8928134c7d1b941c49117), (0x0,0x0), (0x0,0x0), (0xeecff2f6f9df9d7aeeb3c7cee7e3f7b6e41e1de79f62552b77afda8df4ae,0x1110190911202000905aabb004028000008c38024ec0062a0124888d048a), (0x0,0x0), (0xfffffdf9affd3fff779fd1ff7f311aff1efb5ff5ef3aebfdabd68c5d2df30f59,0x20c1800000080440019e888040040000010683064200220040408130608), (0x0,0x0) ]
def g167C : List ColumnInfo := [(2,0,165,0,4)]
set_option maxRecDepth 100000 in
def g167D4 (_ : Nat) : Nat := 0x5f
def g167L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g167D4)
  | _ => emptyPacking
def g167I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g167 : Forest := ⟨167,4,fun i => g167Y[i]?.getD (0,0),g167C,[[]],g167L,g167I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167P4_0 : block g167 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167B4 : block g167 4 0 1 = true := g167P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g167B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 5 := lower_forest (g:=g167) (i:=0) (hints:=1877) (before_sound K103 V103) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K103 5 [(167,[]),(199,[33, 101]),(206,[48, 33, 50, 101]),(227,[112, 81, 50, 67, 100, 117]),(248,[48, 65, 98, 83, 116, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V103 low167 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x3be76756739b8efbbda9f71a39f3fd785655dc6c6b1bef99bebce315cf77660,0xc418c8a90427221450580e23058f1c046c9108582810ca5d1229c055d736620), (0xf0f7e9e4d02efdc3b75eabde0cd07d6f0af5437893c8be065e2d2ff2dbb29437,0xff081467be91023461447fa5421c42a7f6227300438a7602e7412f3247a29433), (0x9ecbb30eb5a3e766881b82867f8df3ed3bff86550b56b9b7d1346ce6e4b97d0,0x61394cc54bd030991a6d36c8e45ec01c4226ad2583c6e006903ec5e0e4a9750), (0xff1ee2ff5f177ff1dbae7f1b7bfdbdeb44a47feeff257f18dffb67b08867b7a,0xe11502c2c8040284a460c8284022c1820a852482651500c4d235002841952), (0x0,0x0), (0xff7fbffffefeeff9efedfebeff72f4ed7bbffbf93b6ff9ee76b77dcef779ad9f,0x80680001001000040000100100100000cc04250040808c10b010810011208c), (0x0,0x0), (0x0,0x0) ]
def g94C : List ColumnInfo := [(8,0,86,0,4)]
set_option maxRecDepth 100000 in
def g94D4 (_ : Nat) : Nat := 0x5f
def g94L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g94D4)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g94 : Forest := ⟨94,4,fun i => g94Y[i]?.getD (0,0),g94C,[[]],g94L,g94I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94B4 : block g94 4 0 1 = true := g94P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g94B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 5 := lower_forest (g:=g94) (i:=0) (hints:=33646144) (before_sound K167 V167) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K167 5 [(124,[81]),(174,[65, 84, 118]),(188,[81, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V167 low94 (by decide +kernel)

def g171Y : Array (Bits × Bits) := #[ (0xd7f3fdc3f5ebf58f73bf7bfecdd0d9b96f492eddbf3ad31c83d8d68,0x280d0020081443a04008a00402c4020019400e500012c0010090560), (0xfffffffff9ed6d7f9bf12eb5ff7768435a26f03f7d5d4baf7584d2d736c751a3,0xfffffffff61212166004c128148cea210480505085d000c3c1804a8b30474121), (0x0,0x0), (0xfffffffff3ddfceef04d5ffbf6e2067d8bdcfec68e6a65959ed90edbc514e277,0xfffffffffc2022110726a8006826308802c08158e4204502989c02396414e203), (0x0,0x0), (0x6f6fa37dddc37144d6cfbd3f9f8f44b5f9daf0b4aa573764df9701a,0x909098800222ac0491204980a132a0e1a2b0b08020e01704bb0301a), (0x0,0x0), (0xffffffffffb7b1f766f7feaf7fd5c88c675fbf77a41b75f8277af78973223f95,0x490c00884800400250011010000c87180a2808066290000a201894), (0x0,0x0) ]
def g171C : List ColumnInfo := [(32,0,139,0,5)]
set_option maxRecDepth 100000 in
def g171D5 (_ : Nat) : Nat := 0x5f
def g171L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g171D5)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g171 : Forest := ⟨171,5,fun i => g171Y[i]?.getD (0,0),g171C,[[]],g171L,g171I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171B5 : block g171 5 0 1 = true := g171P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g171B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 6 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K94 V94) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K94 6 [(171,[]),(218,[32, 49, 66, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V94 low171 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[ (0xffffef4faff027bf5b51afa789c373d337d079fffec72fd1c5664dfa2c363c33,0xffff10b854074440a41e0b00e4c93822a8a82a0634c68f00c434609030303413), (0x7d817c6adedf1d07607af7abb30f3b24863deaf8161bfadfad11b00b769c,0x827e4b920082a2fb19167443d491419a2a41e7c0140112fefc90d802769c), (0xa5e3685c1d766e7e91dbe06dee14f7b9952b53a4e1ed5a1de9d566d512da,0x5a1885a3e0952782866092fa545997282a8c0272c58c449c6be1645510da), (0x0,0x0), (0xffffbefdff7fd78fe6f76fb8be7df5ebdf469f77f4991f7e6f8ebfe9970dc57f,0x4101002028301000a0e800000048100140200010405029000321060d0160), (0x0,0x0), (0xdfbbfebfadfcbfbbbacfddf79efef5bfe19a6b67e9a7b37d5617eff2bbc4,0x204420101202400040100000028040508110c90130230201140008828a04), (0x0,0x0), (0x0,0x0) ]
def g87C : List ColumnInfo := [(4,0,83,0,5)]
set_option maxRecDepth 100000 in
def g87D5 (_ : Nat) : Nat := 0x5f
def g87L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g87D5)
  | _ => emptyPacking
def g87I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g87 : Forest := ⟨87,5,fun i => g87Y[i]?.getD (0,0),g87C,[[]],g87L,g87I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P5_0 : block g87 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87B5 : block g87 5 0 1 = true := g87P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g87B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K171 V171) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K171 6 [(109,[96, 49, 50, 99, 84, 101]),(173,[96, 49, 50, 99, 84, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V171 low87 (by decide +kernel)

def g179Y : Array (Bits × Bits) := #[ (0xffffffffffffffff3ffeb35d9b2f9bb296cb57ebd457186681ccb77b9bc4c72d,0xffffffffffffffffc09048a204104d006020485150c00a41802c042b11040329), (0xffffffffffffffffaf7fce75e0be3f5b6998a87e8ef3d389deb325d3755c29c3,0xffffffffffffffff50a051020c421404c0064a0d40401ac114240443004421c1), (0x0,0x0), (0x0,0x0), (0xdff763fbfdf15bff63f57e0cf37c65d42e784c9dbae7b830,0x200884000220228314000000000085040800001008209800), (0xfffffffffffffffff5b5df9f03fba5c71322ad7ffd565d3d379a9d26c732405f,0xa42201170050008094904828618602263900900c6124016), (0x0,0x0), (0xf6bf5ca5bf66dec1cd8d54c53effa6aafa05e36f2e8b5782,0x906205840890060009981020316600a4300a904628b4402), (0x0,0x0) ]
def g179C : List ColumnInfo := [(128,0,51,0,5)]
set_option maxRecDepth 100000 in
def g179D5 (_ : Nat) : Nat := 0x5f
def g179L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g179D5)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g179 : Forest := ⟨179,5,fun i => g179Y[i]?.getD (0,0),g179C,[[]],g179L,g179I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g179B5 : block g179 5 0 1 = true := g179P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g179B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 6 := lower_forest (g:=g179) (i:=0) (hints:=68) (before_sound K87 V87) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K87 6 [(179,[]),(217,[64, 33, 50, 67, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V87 low179 (by decide +kernel)

def g143Y : Array (Bits × Bits) := #[ (0xffdbd4aed36ed74beffa94fcba3ff3cf9fc3c6fc402ffaf75786f87abb90fed3,0xffa42b19a01129121008744864c01180261a009e00072ba610c60102ab003e51), (0x7a329226c4fdf2a9d97d664a72ea609b3e7d90747431ae8fe0764775aa6e8c,0x5cec9db0b20455e34aa0579204b872c5a4cede0ca398e8a497e461fa26e8c), (0x7d82cd3f761c2a5589424bd1b5c3fd716b6a1afb02feaa496f6df124079cb4,0x27d329086bbc59a346dc7719bdc872f8072801a43b828517dff2221069cb4), (0xffef2f8e98597ffef6a797eedf8a9fdb8d73c3d57cb9fec5239cbeeea6c2c7bb,0x10d06046a60000c8e40b911203c04248652c4056a8d04881189ac00482c1aa), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x3ffffdfffffbf7d9ff7bdb7ff5fcbcfabf7fefffd6b57ffc7f4795ddff396c,0x40000000400008200100000000000890008000001004010400001100590000), (0x0,0x0) ]
def g143C : List ColumnInfo := [(4,0,139,0,5)]
set_option maxRecDepth 100000 in
def g143D5 (_ : Nat) : Nat := 0x5f
def g143L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g143D5)
  | _ => emptyPacking
def g143I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g143 : Forest := ⟨143,5,fun i => g143Y[i]?.getD (0,0),g143C,[[]],g143L,g143I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g143P5_0 : block g143 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g143B5 : block g143 5 0 1 = true := g143P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g143T : checkedTables g143 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g143B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1907) (before_sound K179 V179) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K179 6 [(143,[]),(158,[64, 65, 66, 67])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V179 low143 (by decide +kernel)

def g93Y : Array (Bits × Bits) := #[ (0x777ccff7bdffca68f5d74cd3effff9d736b4cd3353fe9b4e7e75e87de2,0x882000a42800094300d2082004202000008083000081a1c0015087060), (0x0,0x0), (0xd7de5c1ba8da1d1c47c3276117b5c76e5cd24ec5ce5911af19ffb40d4,0x728213de04665e8b3720e8ce0034b05bb61f2cb861ef4190b313fb40c4), (0x6daafba75f882ecabe116727abceeaffe70247c2aaabfb233fd366c724,0x12518650201ed12900b2c060b11069190fd673496a82c1033702628704), (0xffffffaeb45a9b6ddfb99660e5cfaf6c79cd2b3cddd9affde226c72125d8ac8d,0x5149e174a420042b4c10d000881899b293f2938ffb220182a002d08c8c), (0x0,0x0), (0xfffffffbf7fffbf6fc77bf5b2ff7fefb333f7edd6bb3fcac156cfdf5da97925f,0xffffff84000001010100400000060004810004000000000400204040c0040013), (0x0,0x0), (0x0,0x0) ]
def g93C : List ColumnInfo := [(16,0,77,0,5)]
set_option maxRecDepth 100000 in
def g93D5 (_ : Nat) : Nat := 0x5f
def g93L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g93D5)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g93 : Forest := ⟨93,5,fun i => g93Y[i]?.getD (0,0),g93C,[[]],g93L,g93I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g93B5 : block g93 5 0 1 = true := g93P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g93B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 6 := lower_forest (g:=g93) (i:=0) (hints:=1539) (before_sound K143 V143) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K143 6 [(93,[]),(151,[48, 65, 67, 118]),(157,[118]),(233,[96, 82, 99, 116]),(242,[16, 82, 115, 100, 117, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V143 low93 (by decide +kernel)

def g59Y : Array (Bits × Bits) := #[ (0xffffffffffeb7fa978fd9dbf7373c6dd872d6f7f7ae4b9cbf85878f6ed257a59,0x144040810462008084022988080086104485021820083440053048), (0x3efecf795ea1bacd5e4fd52f87a70bcf78f151d97bf9f66126e01ee,0xc101280aa942449412422850880c986c084850ac62c0a5012660168), (0x0,0x0), (0x8bffb51a5a4d1df775f3ecd8832843d1dc0cb05e75aafaae5f21ad4,0x741028e5a1b19241f220dc43500b270ec180a45e25b05839ef20a94), (0xef7c3faeaee7efa3bf87b3e2bcedaf6bf1d6bbe3bac578b6a9bc70c,0x1080405040981820442041060030211200800100140518b28184604), (0xffffffffff3e5f96d7ddf7e6ef0fe0bbf69bf3fec5765ef58e87e9dd14d4aca3,0xfffffffff0c3a028000200302000484000443468091058c50081a00080808883), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g59C : List ColumnInfo := [(2,0,57,0,5), (8,0,51,0,5), (0,8,50,1,5), (9,0,50,0,4), (32,0,27,0,4), (16,0,43,0,4)]
set_option maxRecDepth 100000 in
def g59D4 (_ : Nat) : Nat := 0x5d85534
set_option maxRecDepth 100000 in
def g59H4 (_ : Nat) : Nat := 0xa00
set_option maxRecDepth 100000 in
def g59D5 (_ : Nat) : Nat := 0x210808fd34
set_option maxRecDepth 100000 in
def g59H5 (_ : Nat) : Nat := 0x50
set_option maxRecDepth 100000 in
def g59D6 (_ : Nat) : Nat := 0x2c68819f
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,1,0,g59D4)
  | 5 => (1,1,3,0,0,1,0,g59D5)
  | 6 => (1,0,3,0,0,1,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 2 1 5 1 0 g59H4 h
  | 6, h => lookupWord 2 2 1 5 1 0 g59H5 h
  | _, _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,[[]],g59L,g59I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B4 : block g59 4 0 1 = true := g59P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B5 : block g59 5 0 1 = true := g59P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B6 : block g59 6 0 1 = true := g59P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=67) (before_sound K93 V93) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K93 7 [(59,[]),(91,[64, 49, 101]),(117,[64, 33, 50, 99, 84, 101]),(181,[64, 33, 50, 99, 84, 101, 118]),(182,[32, 65, 50, 99, 84, 118]),(186,[32, 65, 98, 84, 118]),(203,[64, 49, 83, 100, 117, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V93 low59 (by decide +kernel)

def g107Y : Array (Bits × Bits) := #[ (0xfffffff7ea7effef15f7ff01fef9e7fee2bf5de1fb3c03df0c71f4bffa14dd5d,0xffffff88158000100a00c21050060000403080094400020a0c408022c8041115), (0x6ec1c53fd3ddae8bd6160eca779cfbbe36add374c6f738b16a54eb9592,0x11323a8155221062304b2a0aaa570a91418513b6c81805712a40ea9510), (0x0,0x0), (0x7d9cb7d7f8af2ee7eeb1eb1b5e7b97bbab491fea3185ae7bf4ed5b7624,0x26010020750d500240030245b0c0d04b089225811c02458d0011b6400), (0x0,0x0), (0x5d77ff0f79f193cfb7cb969f3bd4726cf6fdee7c5ef25a07ab0ead69e2,0x2288047400106c154a24100151a8040c02386c0104e09a0890060168e2), (0xffffffaf7d1f3b377f4df7ffff39f0979d6f838952cb89a599cfbbcfd1c2aa3b,0x508242d4c8810001c0ad40892400025106208885042189230d12c08a2a), (0x0,0x0), (0x0,0x0) ]
def g107C : List ColumnInfo := [(2,0,105,0,5), (0,2,73,32,5), (34,0,73,0,4), (64,0,43,0,4), (8,0,99,0,4)]
set_option maxRecDepth 100000 in
def g107D4 (_ : Nat) : Nat := 0xc2dc4a824f91502
set_option maxRecDepth 100000 in
def g107H4 (_ : Nat) : Nat := 0xe064
set_option maxRecDepth 100000 in
def g107D5 (_ : Nat) : Nat := 0x3044024044023070898280fd24ff04fd04ff02fd02
set_option maxRecDepth 100000 in
def g107H5 (_ : Nat) : Nat := 0x800317976022000
set_option maxRecDepth 100000 in
def g107D6 (_ : Nat) : Nat := 0x468815f
def g107L : Nat → Packing
  | 4 => (2,2,3,0,0,3,0,g107D4)
  | 5 => (5,1,3,0,0,6,0,g107D5)
  | 6 => (1,0,3,0,0,1,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 3 1 5 1 0 g107H4 h
  | 6, h => lookupWord 4 8 1 7 3 0 g107H5 h
  | _, _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,[[]],g107L,g107I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B4 : block g107 4 0 2 = true := g107P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B5 : block g107 5 0 5 = true := g107P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B6 : block g107 6 0 1 = true := g107P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 7 [(107,[]),(122,[32, 49, 66, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)

def g115Y : Array (Bits × Bits) := #[ (0xfffffffffffff6e557fb76f9ae6c3daeff67fdad602fa7ed99af4c80f50457d5,0x91a2004210500018640a0241208021e018089000020f4804790), (0xffffffffffffbcd6ccddfa1cb9b2f6c305eeb7e50fe7dd136fa8fa380ce3c139,0xffffffffffffc318236200d340648040a79350170a0d448463280a226c81c139), (0x0,0x0), (0x0,0x0), (0x7bfbefdebdbbe7af9554cdba76fafdf9997ae75d075736b82d6a,0x400140102001000582400002000004088100041040000200842), (0x7f1f1ff939775dd15bd7bde5989f3ee66c0ab5f7f3e9c84bf086,0xe0c090c4002682000a484001808520200a1484d045014a3004), (0xffffffffffffdd953dace797b240a5bf2e1e7d0bcffc76d7685c7c87975c8a1d,0xffffffffffffa260815a08686ef8018014c0454611a01447321ce0c6095c800d), (0x0,0x0), (0x0,0x0) ]
def g115C : List ColumnInfo := [(32,0,83,0,5), (1,0,114,0,5), (64,0,51,0,5), (2,0,113,0,5)]
set_option maxRecDepth 100000 in
def g115D6 (_ : Nat) : Nat := 0xe411f
def g115L : Nat → Packing
  | 6 => (1,0,2,0,0,1,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,[[]],g115L,g115I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115B6 : block g115 6 0 1 = true := g115P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g115B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K107 V107) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K107 7 [(115,[]),(121,[64, 33, 50, 101]),(155,[99, 84, 101, 118]),(185,[64, 33, 50, 101, 118]),(211,[117])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V107 low115 (by decide +kernel)

def g175Y : Array (Bits × Bits) := #[ (0x79aeef2bb5bda8b6dc1f35c010d9d66a9d51f27acd27495fd996b3f2ac19e602,0x104090e083838010c4082100300142409410c570846740408090a300a0192602), (0xd5b4f5c92ac3d95b3fa258bea8ee8a9af5b29e47fe4d94a402984ec1c26c1773,0x813010202286d942d42208a0b0e98818f0b486ca9646940000308ec1c02c0703), (0xcbe84bd5b6805ef4ffb272dd66a08925f6478539b111724ffc28aa88193ef5a8,0x13d1e2e173003034dfbaf6c1efa0c958c6d6052db501814d4c38aa88183ef5a0), (0x4feb770be7e4ec262eefe2a21b72abba02fa42b88ab53b0d1b67fdec0aa888a7,0x69a22b0500047c072ac48ac24f70a03a48c200880a00170c1a2e5ce80aa088a1), (0x0,0x0), (0xfd1e68bbfd5361617ae0d74fc87e9071de213c65fb2e6e7a6b5b06306eb253fc,0x42086a084448202d2884d44c4a1620250a09300549002a3a070900300e8250fc), (0x0,0x0), (0x83f3925c5608979a85d1abb967b77d85a3cee9c357d0b2caa7e5481f91c72c9d,0x80c08008800010018000210840108080040102032214000160140001c), (0x0,0x0) ]
def g175C : List ColumnInfo := [(4,0,171,0,6), (2,0,173,0,6), (32,0,143,0,6), (6,0,169,0,5), (8,0,167,0,5), (1,0,174,0,5), (0,4,43,128,5), (132,0,43,0,4), (9,0,166,0,4), (128,4,43,0,4)]
set_option maxRecDepth 100000 in
def g175D4 (_ : Nat) : Nat := 0x930c099c6e8344b2d19d454079882a8a80de10789501
set_option maxRecDepth 100000 in
def g175H4 (_ : Nat) : Nat := 0x18ee214
set_option maxRecDepth 100000 in
def g175D5 (_ : Nat) : Nat := 0x90400f20940400274884f182a3030300ed85945bb4da25bb41a25b78d905cf51505ed91901f949901fc54101ed51501f989501
set_option maxRecDepth 100000 in
def g175H5 (_ : Nat) : Nat := 0x20661949f8c000393d801c3482602
set_option maxRecDepth 100000 in
def g175D6 (_ : Nat) : Nat := 0x938a301526006734a20152620044a0e6a9251012941cc59440420b49060369df4fc2a912006f517fa6bee25fe82fb48fda05f501
set_option maxRecDepth 100000 in
def g175H6 (_ : Nat) : Nat := 0x202c7180090001a9
set_option maxRecDepth 100000 in
def g175D7 (_ : Nat) : Nat := 0x10ea84203bf
def g175L : Nat → Packing
  | 4 => (4,3,4,0,0,5,0,g175D4)
  | 5 => (10,2,4,0,0,7,0,g175D5)
  | 6 => (7,1,4,0,0,8,0,g175D6)
  | 7 => (1,0,4,0,0,1,0,g175D7)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 5 1 6 2 0 g175H4 h
  | 6, h => lookupWord 5 13 2 8 4 0 g175H5 h
  | 7, h => lookupWord 3 9 1 7 3 0 g175H6 h
  | _, _ => none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,[[]],g175L,g175I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B4 : block g175 4 0 4 = true := g175P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B5 : block g175 5 0 10 = true := g175P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B6 : block g175 6 0 7 = true := g175P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B7 : block g175 7 0 1 = true := g175P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1875) (before_sound K115 V115) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K115 8 [(175,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V115 low175 (by decide +kernel)

def g215Y : Array (Bits × Bits) := #[ (0x92f95d51f837f2fafe13d6ffa6550e05f8163db83b0138bc4f33808b1d1949aa,0x2079289149200d8b5000d7f820200c41a8024c1011041cbc0b70800a1d1100aa), (0xaded9fad665920a10bd565cd19a6a539a3cd64215b867c94188d7e969ee00279,0xf82a93608121673ad1471011ab8409000566205396549c2a259a969e400078), (0x3ef532cb5fadb7d48b0cf342e558fcc9a364cb4bcd56c2d186735b586440d6ba,0x640d3857890c856d4b08834205181441af424c0828d493810b775e482440c6ba), (0x0,0x0), (0x68cbd755fb71da5457e38aa23316102726aa0cddff2e07cf740c742ea4766e04,0x45005400004e020001000000001400040620008da84083000408240020226e00), (0x0,0x0), (0xd2bc6b4b58de768ef56e6c1dd0018f1ad5a5ebbe063382e5bb5b1bb56b0e8023,0x9082032830103000240628059083c21000843302062b0040b08001b5420c0001), (0x5f675ea31d70ed2b289ab5649df8f7f74ad1b04494e87b32c0b0a961128135dd,0x8a00800810104000000228048040612240809042040920004080012100801105), (0x0,0x0) ]
def g215C : List ColumnInfo := [(4,0,211,0,7)]
set_option maxRecDepth 100000 in
def g215D7 (_ : Nat) : Nat := 0xbf
def g215L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,g215D7)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g215 : Forest := ⟨215,7,fun i => g215Y[i]?.getD (0,0),g215C,[[]],g215L,g215I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g215B7 : block g215 7 0 1 = true := g215P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g215B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 8 := lower_forest (g:=g215) (i:=0) (hints:=1604) (before_sound K175 V175) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K175 8 [(215,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V175 low215 (by decide +kernel)

def g190Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x9edc1fa2ef61ac553ab2caf2f3287fd35e5fcdfdd1e1f248500e1cce46bd0ca1,0x40061200201281028a2c030002807424413048388611028000a1c8202390420), (0x8bfd2eee2ef175eadc5da503543375a15aa8f182ea88f31fc88fce909e61554,0x3c95c88e724f024f09098a72149b2452d5aa8d013ca99bb4d8cd7ce901e61544), (0x423f6cd298d35263592ad32455f6c7b07f62b352d0defc360d03a9b300dc6f0b,0x71595069af318eb4b0ac77c45f2c31079e084d27490d46c440be9b300dc0f0b), (0xf5c708efbbfba9f6804bace90fcff24fb650b124f49c4cc79a7ef276b3468c0e,0x33008c82f1a0804401000d4805c1d00882408120340c0d470054227421040806), (0xe9e917cabdde14efcec99612dee5a9f5c87f583862fb209b4a33e59875d2a179,0xf810510000148b86491207d20428a501001818419020906b81c10854c2a159), (0x0,0x0), (0xbbb7e17f7395f70afd377b0dee33c42e21a1fec70f36bf34a5d10b21d82973d6,0x8042004004000500900010012a000800000072040302200023000000d8006090), (0x0,0x0) ]
def g190C : List ColumnInfo := [(8,0,182,0,7)]
set_option maxRecDepth 100000 in
def g190D7 (_ : Nat) : Nat := 0xbf
def g190L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,g190D7)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g190 : Forest := ⟨190,7,fun i => g190Y[i]?.getD (0,0),g190C,[[]],g190L,g190I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g190B7 : block g190 7 0 1 = true := g190P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g190B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := lower_forest (g:=g190) (i:=0) (hints:=269580096) (before_sound K215 V215) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K215 8 [(190,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V215 low190 (by decide +kernel)

def g235Y : Array (Bits × Bits) := #[ (0x79c7139a2bd7e9f013d4a25fbd4324c8bcddb0cf9b74259b8a1cb41f54d55902,0x60040100010840200000800c880000c85090000b184000008908040440904900), (0x467d7845fe7eba82e0296f75e72c39c0512f4fadf50b564e3dcb09f0729803f5,0xc0003d002180660200286ec085082cc94044002394421402b1c84190509003f1), (0x0,0x0), (0xfec2d7ea4ea237ef6cca9e89109de7371fa6a211d7ec8c6164a8e698a926a729,0x840098400080040a80260481100165120c040200c50c00601000c0982804a209), (0x0,0x0), (0x72b478b43b6c7da8d2855c1fd3bfdab8e23a6304fe33f15e5212886d6762805b,0x1f01c0c74a3101d0da95013142e592122a2a231402b1e178420088692762800a), (0xc3f789e6d447f1b7614371402a6b42f782dfa670269ee78eeea85a4311523eec,0xc922837446b3906141710060ea1825a24bac502280ad1e04e40a43114214e4), (0xbce8f61fc9d1179e0e3be5b2cc92a3740523ddfb0a20fa7d07c591e388abc486,0x8e002835c7190941910013240b202200323c89002214b1d06241063802b0406), (0x0,0x0) ]
def g235C : List ColumnInfo := [(32,0,203,0,7), (128,0,107,0,7), (64,0,171,0,6), (2,0,233,0,6), (0,2,73,160,6), (66,0,169,0,5), (1,0,234,0,5), (8,0,227,0,5), (32,2,73,128,5), (136,0,99,0,4), (65,0,170,0,4)]
set_option maxRecDepth 100000 in
def g235D5 (_ : Nat) : Nat := 0x48f309183012fd9c4640a9eab88c817ab0490902f5208a12056d91d20806db23a4080df20749101
set_option maxRecDepth 100000 in
def g235H5 (_ : Nat) : Nat := 0x125ace4802533830
set_option maxRecDepth 100000 in
def g235D6 (_ : Nat) : Nat := (0xb24d208a42204fc7b3a9b0d26630168a84e1f8c04e240f06c2a120481800bf41b24bf81924bf49b04efc9304ef49104bf41a02bf51a02fb50a02bf91902ef91902af91902bf51902ef11902fe90102fe50102fb90902fb509029f55802af51802b74d802fdc8201fd48201fd91901fd89901fdc8101fd48101fdc9101fd49101 + (0x181081000002071c020000810810810812471b01071b1c041b1080481030040192080181994 <<< 1024))
set_option maxRecDepth 100000 in
def g235H6 (_ : Nat) : Nat := 0x4778c000008dc3e792142dc0179320024e000d9071a8c03553de001c000000b6105bebead2c6953e010a40001a7c3
set_option maxRecDepth 100000 in
def g235D7 (_ : Nat) : Nat := 0xe6290628860028e6290628860028e6290628860029473148314430016a39883144300147310628860024e620c510c004a8e620c510c00518a41ca301d48310728c08ed68ad52d7ab091e5717003fe49fd24ff827f413fe05fe02fe817f00bec03f501
set_option maxRecDepth 100000 in
def g235H7 (_ : Nat) : Nat := 0x31b200960064b5f9135718a00830
set_option maxRecDepth 100000 in
def g235D8 (_ : Nat) : Nat := 0x864202bf
def g235L : Nat → Packing
  | 5 => (7,3,4,0,0,6,0,g235D5)
  | 6 => (28,2,4,0,0,9,0,g235D6)
  | 7 => (10,1,4,0,0,9,0,g235D7)
  | 8 => (1,0,4,0,0,1,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 3 9 4 7 3 0 g235H5 h
  | 7, h => lookupWord 12 36 4 9 5 0 g235H6 h
  | 8, h => lookupWord 4 12 4 8 4 0 g235H7 h
  | _, _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,[[]],g235L,g235I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235B5 : block g235 5 0 7 = true := g235P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235P6_16 : block g235 6 16 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235B6 : block g235 6 0 28 = true := (@block_merge g235 6 0 16 12 g235P6_0 g235P6_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235B7 : block g235 7 0 10 = true := g235P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235B8 : block g235 8 0 1 = true := g235P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K190 V190) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K190 9 [(235,[]),(246,[32, 49, 50, 67, 101]),(250,[32, 49, 66, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V190 low235 (by decide +kernel)

def g187Y : Array (Bits × Bits) := #[ (0xbc2ff494354fdf3ba71d3aa6411173fb0ba42f40fc5996a63199b911cf81d8a0,0x10020040260048832400608240110b4201042b005a00000018000810c8015080), (0x5a7a156553b5f2eeb9cc89d4ee9f1886f4c9c3d53a5428603a32e71a38b2658c,0x5090242800018a3a403208240861882e4c42a043b5000400810541228a2408c), (0x0,0x0), (0x716173a73908402b83a4bdd594447763d27a65d6b1b8474de11c12db01c4306f,0x41a1388f01ca8720496089058cc4b011566a00c0218a0f04659416cb01c4202e), (0x84986dfaef966ee66cfe7e2ae46ba46ac17a10f80c66e836cff44ce64c0a2632,0x4000d008c060008041001802000200028005004222c268684008404082422), (0xa9d3bce87cfa94603542df9cd9768e1574a15e8be004d3d2c7272968136981d6,0xca703c305043a01400600e140a0084101a01548b8084d2014161216813408150), (0x0,0x0), (0xf30e3e1bd44519d7faa1866113ac1580395ec22fdfaf331d504ec3a4b054ca49,0x285084101021004400900260130804000811500080040011004b812010108a41), (0x0,0x0) ]
def g187C : List ColumnInfo := [(128,0,59,0,7), (1,0,186,0,7), (32,0,155,0,7), (2,0,185,0,7), (16,0,171,0,6), (8,0,179,0,6), (0,8,50,129,6)]
set_option maxRecDepth 100000 in
def g187D7 (_ : Nat) : Nat := 0x54ba981952ea606f03de47ed23
set_option maxRecDepth 100000 in
def g187H7 (_ : Nat) : Nat := 0xfa2
set_option maxRecDepth 100000 in
def g187D8 (_ : Nat) : Nat := 0x358d103bf
def g187L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g187D7)
  | 8 => (1,0,3,0,0,1,0,g187D8)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 8, h => lookupWord 2 3 1 5 1 0 g187H7 h
  | _, _ => none
def g187 : Forest := ⟨187,8,fun i => g187Y[i]?.getD (0,0),g187C,[[]],g187L,g187I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B7 : block g187 7 0 2 = true := g187P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B8 : block g187 8 0 1 = true := g187P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g187B7
  · exact g187B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 9 := lower_forest (g:=g187) (i:=0) (hints:=67) (before_sound K235 V235) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K235 9 [(187,[]),(219,[64, 49, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V235 low187 (by decide +kernel)

def g125Y : Array (Bits × Bits) := #[ (0xff651feb67ed5d377320d8af3b89e884d40e2b3e42e9af5d13eafe2374321743,0x208001a00010000008003a08000400060808002d804c00008e0300100041), (0x0,0x0), (0x4b7f8d379ba0fc7fa8de2747bfb75cb2e0f043280266c8fa05b16c45f317ca84,0x1101083909a9eb2bb8c6ef01ee9b48506ab4c3281a66d01505a07c45f2174a84), (0x1f994a853cf3dbdfe14be62b48f42379ad024faed640d207f2dca90ce80a5df8,0xbb490010e40071af6b8ae61344c42a61ac006102774212037418200ce80a5da8), (0xa2ab3f9af53b438ebfaeb1d03a066e937bcd9dc739195412bd8522f820dc6ba4,0x2200466058091904bb889311800468937a0004044900100048852078204043a4), (0x44d43300e1c4472b694d3d2643a30635645ab2d9bd3a75f3be0751cd5fcc4c03,0x5dc08104a042e22b44450026416194280068f28132026493b60a11845f8c0c02), (0x279fc4f73fbae0c9c4f70758e57df56f3bb9549084f7aaa86a30a5168fa1a0bc,0x4014000600460040042000480120940801080091801008200202010005a0a010), (0x0,0x0), (0x0,0x0) ]
def g125C : List ColumnInfo := [(8,0,117,0,7), (4,0,121,0,7), (16,0,109,0,6), (32,0,93,0,6), (0,4,57,64,6), (68,0,57,0,5), (48,0,77,0,5), (20,0,105,0,5), (36,0,89,0,5), (12,0,113,0,5), (1,0,124,0,5), (8,4,49,64,5), (64,4,57,0,5), (76,0,49,0,4), (24,0,101,0,4), (9,0,116,0,4), (5,0,120,0,4)]
set_option maxRecDepth 100000 in
def g125D4 (_ : Nat) : Nat := (0x14182000000001cb666c16aa4e91099a43c6090c0c02394e22741a15b193801d45416ca4a007515058e62859e15c12c382135515239c6084de1548e399a107855238e62859e15c0ef08211748d03c8c6748d4540f835952351503f090548d4540e398a167855038b57891a1540f3159d2385503dc10748e1540f8c415458d901 + (0x20c <<< 1024))
set_option maxRecDepth 100000 in
def g125H4 (_ : Nat) : Nat := 0x788002800a3c000003411068e869002007356b15600a4b978232
set_option maxRecDepth 100000 in
def g125D5 (_ : Nat) : Nat := (0x40f5a8bc8c81eb64645903eb20aa9a07f145d2340f672b24681ecd5648d03f1c8c91a07f14592340fe52824681fc95048d0397ecea2a072f19d4540f1eb2a8a81f390551503e3a6aa2a07e348d4540e7ab3c2a81df10785503baa6f0aa07ad91a1540fe291c2a81ef1508d901d6a8b1b2036d91d3040773b3a4680fc50348d01 + ((0x553049eacf0ae09378dd564127713aac8263f6555104bcc0e8b247734df0648f728b60c91dae4741923b9c0ea9a47e38dd4548f869aa8a91de56785523b8a6f0aa477941e1548ee69be0a91cee6741523e9a6a82a47cb5150548e7713aad81e3d6551703e720aa2e073d59e15c0ef883c2b81cbe47559039dc4eab2072f55e46 + ((0x16e5a15a5514e521424f1364a11a3d0e6340c22b0a626092210761a05a1504e120420f02e0a0220700e002cf1ba0ca2dae2741945b3a6e0328b6b49c065178f1ba8a9ae3e06515359ec0e9b42b3d8dd068577313a0d0ace62741a1597c8e9b60b3b4de264179d03a8a82f380751505c7c6ca2a0bcb899454167713aad8263d65 + ((0x4001901640408c040000000002484223048410002304b08d0b8440b04941008c100b012c0400310100000000008071010e09c380110c14300090c107860800e04003040c1c407101000000030c1000002c16306deb62d2b32beae2b2ab2a6a6292a327e9c26a972569424a9123e8e22285206801fa7b1c66e1aa69196641825d + (0x1901000000850 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g125H5 (_ : Nat) : Nat := (0x4868050018afcad44a50000006bca4c00082000501c6d9abb182000321794a0c86509797b3a00000101f0562bd8187f6f4b48580041ca0e0f72137600251718001a2222f34559680ded2ab6683fcb2b6183c468f9a567010117ab257f8325219307ca6a5d50900007351d27000eba54bc3200c0181a090823100204880199c4f + (0x16e <<< 1024))
set_option maxRecDepth 100000 in
def g125D6 (_ : Nat) : Nat := (0x1505df4d505bf55b04ef55304fd85704bf95904bf55904ef55104fd85504fb55923f945923fbc1923fb41923f354d23eb51523f985523fbc1523fb41523bf55b03fe54303ef51703fd85703bf95903bf55903ef91903af91903fd45903fe94103fe54103f754d03f348d03ef51503fd85503bd8d901fd50101fd4c101f948d01 + ((0xa90cff9f337a6c4bd94521e39c4a86d051fcbec7a2ebdd139c6f4cb98d2f8574a292d23841e7d0f39cc37e690c116e2a64c4921101f83305889d0cc1801f000bf81945ef8d945ef4d945efc1945ef81945ef41945ef01945bf81935cf51535bd4da15bd41a15bf51b05bf4db05bf91905bf8d905fb89905bb89905df51505cf5 + ((0x356244220e5826325498e121805244210f488d088396064a8c1610042c4a8e16180325498e1218032c4809088396240484508040071010b12086101080c0861018100203c2142c3803201e30112203101041620438343058400c162410c243088260b11101c0380411c10224c4d16263450501196b1c616c05782df58eaf552 + (0x284021a40689088192224222442105480d0889112140205480d121403040210c0a0e161c030508880e014284038040020302180100800e661001cc8b843180c218141e1c028c041040604008162410c202101810c202020040a08 <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g125H6 (_ : Nat) : Nat := 0x5396f5b45f0029812176002a10031206b441d1720d6f0001ccf0b0d2408700000b66d5e94179a823c4c0083c0079c664cc00a25961738ad9311d7ba961a05c04eca03e010eabca3cbab80006d1400331b74a275e4272e20134062800130020
set_option maxRecDepth 100000 in
def g125D7 (_ : Nat) : Nat := (0x106000b98512388180730a1440c284180028c2851030a106000a2861440e20a106000b2861430a10600093869630a10073071851230818092861440c284180028a1851030a106000a40c2a61448e20602b2ab72b29aa3a7e1b65b932408c6210420037e8bfd45dea2ff4d7ec2bff05fe82ffc13fa09ed23fa89ffc0ffa07f501 + (0x3061438a180730a18510388284180030c1438a180630a1851030a <<< 1024))
set_option maxRecDepth 100000 in
def g125H7 (_ : Nat) : Nat := 0xba00d4ede028b573e9003c001b00d612a771178020
set_option maxRecDepth 100000 in
def g125D8 (_ : Nat) : Nat := 0x18a3104033f
def g125L : Nat → Packing
  | 4 => (17,4,5,0,0,7,0,g125D4)
  | 5 => (70,3,5,0,0,10,0,g125D5)
  | 6 => (55,2,5,0,0,11,0,g125D6)
  | 7 => (14,1,5,0,0,10,0,g125D7)
  | 8 => (1,0,5,0,0,1,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 6 21 3 9 5 0 g125H4 h
  | 6, h => lookupWord 24 83 5 11 7 0 g125H5 h
  | 7, h => lookupWord 20 66 5 10 6 0 g125H6 h
  | 8, h => lookupWord 8 20 3 8 4 0 g125H7 h
  | _, _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,[[]],g125L,g125I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P4_0 : block g125 4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P4_16 : block g125 4 16 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B4 : block g125 4 0 17 = true := (@block_merge g125 4 0 16 1 g125P4_0 g125P4_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_16 : block g125 5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_32 : block g125 5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_48 : block g125 5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_64 : block g125 5 64 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B5 : block g125 5 0 70 = true := (@block_merge g125 5 0 64 6 (@block_merge g125 5 0 32 32 (@block_merge g125 5 0 16 16 g125P5_0 g125P5_16) (@block_merge g125 5 32 16 16 g125P5_32 g125P5_48)) g125P5_64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_16 : block g125 6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_32 : block g125 6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_48 : block g125 6 48 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B6 : block g125 6 0 55 = true := (@block_merge g125 6 0 32 23 (@block_merge g125 6 0 16 16 g125P6_0 g125P6_16) (@block_merge g125 6 32 16 7 g125P6_32 g125P6_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B7 : block g125 7 0 14 = true := g125P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B8 : block g125 8 0 1 = true := g125P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g125B4
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=1539) (before_sound K187 V187) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K187 9 [(189,[118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V187 low125 (by decide +kernel)

def g123Y : Array (Bits × Bits) := #[ (0xffd4ffed2088854e5d76b224debf8ff80e60048d29c262dcaa735a0c3a310e9a,0x181cb0188005002c4400820058a100000700000500d06000204050003801028a), (0x73e6297eef79d0bbf283c59f085612f73175b75748f0bda100e8db27288ae1ac,0x8104982112c1a6a5448a039c081000a22764b6130952e803012072252808e1a8), (0x0,0x0), (0x38f38c4d5d51a191fa790706f374f95ae888463b9a2a9b264beb57f1a2944073,0x5424561130248112a8950468604c95218068a281a2a1a2640a807e182904051), (0xcfd15da56ae1af9e4d61cca99872108953bfad866ed8e7054b4b5a0c561311d,0xa001c0000000000a1014008206200890020808702400304000818085200014), (0x867ff8a3e06be45f3bed40f305e07fb760155b8ece5560bdf40b4403c4de8ec1,0x44404200611800501044406305489310009141a08200008c140f000240d60c41), (0xdb0766c41bf4aa35d53ca994e8195486eaeb6121b32dbd8e671ea8dc590e7460,0xc201000420b0b1c0902400a90018148460a94000010185811316281c400e3420), (0x0,0x0), (0x0,0x0) ]
def g123C : List ColumnInfo := [(64,0,59,0,7), (32,0,91,0,7), (16,0,107,0,7), (1,0,122,0,7), (8,0,115,0,7), (2,0,121,0,7), (0,2,73,48,6), (0,8,50,65,6), (66,0,57,0,5), (40,0,83,0,5), (18,0,105,0,5), (9,0,114,0,5), (72,0,51,0,5), (34,0,89,0,5), (10,0,113,0,5), (1,8,50,64,5), (16,2,73,32,5), (32,2,73,16,5), (64,8,50,1,5), (74,0,49,0,4), (73,0,50,0,4), (50,0,73,0,4), (42,0,81,0,4), (96,0,27,0,4), (80,0,43,0,4), (33,0,90,0,4), (24,0,99,0,4), (3,0,120,0,4), (48,2,73,0,4), (65,8,50,0,4)]
set_option maxRecDepth 100000 in
def g123D5 (_ : Nat) : Nat := 0x4080c10b82000057a32e2bf608490c0c033989e1641534d5a474155340ee69610450d03f8b645012340f664dd0451503d99074d14540f564dd0551503f19344154540f5641d3551503f19044d54540fd4961034d501
set_option maxRecDepth 100000 in
def g123H5 (_ : Nat) : Nat := 0x5014238c81e9860001ea00e400002ff350488
set_option maxRecDepth 100000 in
def g123D6 (_ : Nat) : Nat := (0x40e7fb3a8a81cfd6751503bf20ea2a07774dd4540f5eb228a81fb90451503f3a68a2a079f5954540fbc82a8a81f5d3551503bec2e9a2053f51e564067e9bcac80ef93095901dea632b2037d51e56406fa9bcac80ef53695901fe2aea0203fc95940407f92ba6080ff1574c101fe4ac98203ec41145407e881a6a80fc10348d01 + ((0x91923bda0f23247bb41a4648fe6a3aa691fce4654d23e9a6aa2a477b89d0544e7ea3cac81e7e57559039fc8eab2073f55e4640f5f23a8c81cfe5751903ef6caa82077e95d4040fddb228081dde4754d03ebecaa9a07d64155340feca02a681f9f6450d03f3208a1a07f65414340fe723a4681fce4648d03f9a8c91a07f250123 + ((0x8dd45416bf23a6a82cfe07559349ea0f0b2696f81d544d37b0b24a9a5ee2741534cfaca82a69cf515054d37b0b20a9a5ee27415149fa6f2b2093f8dd564127eabc6c825be474d904b7c6eaa209af8d9544135f2b268826bd564d104b7a8e9aa099f595354139ea2a6a824fd57919239fa0f23247bb40a4648f6e81c8c91ded57 + ((0xa8c7cc60c54c48c1cc00bf4bd8b8cb50a74a68a3ca009f49c898c98095493891c9008e484883c81077476872c6f06946085fc5b058455851c5004d449846c45044442841c3f03e43b83ac3903443082cc2702341680dc0013f41e365167e9bc0ca2cfd07919359fa8f0326b5f95d064d6bf03a8a9ae7e06515359da6f1320b5f + ((0x388a0018e82382e10ea200863a2e10e020000200ed004030900403082281ec8c020dd090863a06c018e8a07b2300a3a364418e0d8c8a08d3e322f20190d0183836214f8c06454040e8e596887d3e362d2219170f01b03900d000fd4fa8f8cf70f34f18f0cee0ea4e88e7ce60e44e18dfcdf0de4db8d8cd60d44d28d1cd00cd4c + ((0x808e0200102380610e81043a3810082000394213002030022a20cac220d5010063a3834302a258f4dca880542406800c0a10e8a00060038204382a001803a0610e820608e020408a63d3b301c10110001200e01042b4f8ccc070404420248038348618e013086382a20cac228e8d07d3b321813090003830282083a0410e0184 + (0x382040c0a1000c0a10e80043a08e820f86c41818200302840cc7841810206282060e2d2054808000382040e0810e00043 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g123H6 (_ : Nat) : Nat := (0x4e501772ac47e5a4180051ca704c4c608acede980063d500e5a3c720d2800000927f53163bfc9f687ceb2964e405864c91912e15e8b1e7395b5a847d7d50c84e8ff84e4b85ed2f6c4a2d2891000000001508648b400608c2e2080041bd9bebec27b0d6fe34001c4a69e88089510a00108e0850031a70140002863c010602d242 + (0xa998984380022a13b55800001882c300000147d28c0aa332168013ac83893d9a5533 <<< 1024))
set_option maxRecDepth 100000 in
def g123D7 (_ : Nat) : Nat := (0xd504fb51723fb41323bf91923fb91923f354d23fb51523fb41123ff41513ff95903bf95903ff55903bf55903ff91903bf91903ff51903bf51903fe54103fe50103f754d03f750d03f348d03ff51503ff4d102ff44d02fd51601fd4d601f9c8e01f948e01bf95901fd95901fc50101fc4c101fd51501fd4d501f9c8d01f948d01 + ((0x39e9b70d4a64b2ff96e8aea52926792608ec45b1fd0e806d231d15709343d819208e02b40c2000bf8d945ff4d945bf81945ff41945bf91935ff51935bf81935ff41935df51535bb89905df51505df4d505bf55934bd85934ef55134ff49534ff41534ff41514bf95904ff55904bf55904bf8d904ff4d904ef55104ef4d104ff4 + ((0x407890e034e51203e3450b901a2c380c386ca119e9e3068b9124306890a040e9c36427a78c1a2a4860d1214079c2946345490d161c051d38ca88f4f1a2a4868b0e03659729491647d631b15687ac2fa0ad0267df3d91e06ed3735b941c40e056ceb599a0aca4636b015756b7b58d2b014a29f04c7a44914688142c1fdcf80766 + ((0x80014647c64c0e1024204930423a7860c1200049c2a413c6860c1210251d64407a7ca90243058701874e1706080801c5874a104141c306549cf4f142e4490c1a24280d3a567a78a1524306890a0309c5490d161c039d2ac93c5490d161c051d364e7878d14243060b0814000f3a6ca4f4f1a2a4868b0a14069c324680f8d142e + ((0x848702034e9824427c7cb10263058501a74e1a2a4a8470e9b2a5888e102428113a70d501f1c3a64b111c2048501e283054821d060900014ecf0e182e4090e102028001a74c141e910001ce98293c3860a121c20280c380c1210229ca01c3650a121c2048408034e192a412a10239c32568070c14243848401874a0f8e981c204 + ((0x4819d32527870c1424305040a0007192e507a4400073a64b949e1c305090c1414069c32c03860a121a2050408034e192a452a20439d325ca118e9e2e4860c0a00071c32548b04f1a183440809874e19300400c509d04d952c4088e1024280d38528264b1022384090a030e1a2b423860b101c204840e00079c34568474c96223 + ((0x92230639c30568070c1420384840c0007182e54825420473a617870c1422384080c00069d3050924460c73860b95251936589081210200e0f961e2c30063a5ca129e9e365890c1a10200e3a60a129e9e343068810030e182e568070c14203850501a1b263850700c70b9523423a68b92102028001c303c50ca948a9008018686 + (0x70b95601c305080d141030001c60b9522951021ce9728bc3860a11182820600038c97284 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g123H7 (_ : Nat) : Nat := 0x25892fe4b1000a0ed48cc00bf2d1000008d000000b7b5edd37aee1735b0034a48fe85a5cfc8b82fe000ccbccd4ec18f64d37def0ee486e7e5001357428949e8021aec35800bc7aad49ba267b6f9b0e001704552056800486c7c1400bb4000006b2d4a823820448c0000ad00041004a2
set_option maxRecDepth 100000 in
def g123D8 (_ : Nat) : Nat := (0x9459040c284180039140f3871851230e20a10600105922c71a51440e20a106000f54f1640e286021b4503c71859040e20a106001071140f1859038a180bccd81ad35409b51d2073a8690c49562644086a8a20e415c120007f517fa6bfd25fe8aff417fa69fd24fe8a7f413de47fd23f691ff44ffa07fd12fe817d807fa03f501 + ((0x69451230e20a10403d24502071859048c388284101075448f1c69459040e20a104041c5514071a51641230c20600104913c91c69451230e20818004164d03471859048c38820600106513c71a516410388206000f5109448c286021a4903c71a51448c30a106001075240f1e51230a180b4d12871859048c30a106000f40f1c6 + (0x174911c69459048c38820403d84901c69459048c30a10403d33cc1c <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g123H8 (_ : Nat) : Nat := 0xe88348b99eb90f810a32000c0000ab7f27497191fb88e8d00180259
set_option maxRecDepth 100000 in
def g123D9 (_ : Nat) : Nat := 0x1483104033f
def g123L : Nat → Packing
  | 5 => (11,4,5,0,0,7,0,g123D5)
  | 6 => (87,3,5,0,0,12,0,g123D6)
  | 7 => (62,2,5,0,0,13,0,g123D7)
  | 8 => (19,1,5,0,0,11,0,g123D8)
  | 9 => (1,0,5,0,0,1,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 7 16 3 8 4 0 g123H5 h
  | 7, h => lookupWord 29 103 6 11 7 0 g123H6 h
  | 8, h => lookupWord 24 77 5 10 6 0 g123H7 h
  | 9, h => lookupWord 8 24 4 9 5 0 g123H8 h
  | _, _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,[[]],g123L,g123I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123B5 : block g123 5 0 11 = true := g123P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_16 : block g123 6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_32 : block g123 6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_48 : block g123 6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_64 : block g123 6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P6_80 : block g123 6 80 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123B6 : block g123 6 0 87 = true := (@block_merge g123 6 0 64 23 (@block_merge g123 6 0 32 32 (@block_merge g123 6 0 16 16 g123P6_0 g123P6_16) (@block_merge g123 6 32 16 16 g123P6_32 g123P6_48)) (@block_merge g123 6 64 16 7 g123P6_64 g123P6_80))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P7_16 : block g123 7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P7_32 : block g123 7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P7_48 : block g123 7 48 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123B7 : block g123 7 0 62 = true := (@block_merge g123 7 0 32 30 (@block_merge g123 7 0 16 16 g123P7_0 g123P7_16) (@block_merge g123 7 32 16 14 g123P7_32 g123P7_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P8_16 : block g123 8 16 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123B8 : block g123 8 0 19 = true := (@block_merge g123 8 0 16 3 g123P8_0 g123P8_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123B9 : block g123 9 0 1 = true := g123P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K125 V125) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K125 10 [(123,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V125 low123 (by decide +kernel)

def g255Y : Array (Bits × Bits) := #[ (0xd1c45e412489c60498860c40f1897172660b0450a41b220988aa140bc60280da,0x81800c00000904020010284010015002200b005024080209080a100a84008000), (0xeba09124304180e4458e56105c09ed8e65c157a0ca28cf13f46d82494604010,0x2000802224c18020018e4410500909ae658155204a20ca10e06d82484404010), (0x380304cc9ab75c32218630a23d6ed0e5628a9a094439012d780db91d314e5bb1,0x203304440097f812290621263d509061228a9a090439002d780db91d304613b0), (0xa2293c317af961812f2d55267a10a249eb80ee871f21e2a856232a3118c22416,0x202910273ab02108292e0524041080494bc0ce010b21e0a056212a3110c20416), (0x6252b4a00130d04a2523835d061ad19f126158090a4558464a1860c0b2d101a2,0x5010800122c048252203040018000000004009084140444010204032800182), (0x9466e1008e950aa469895ab8c8b13f210824ebc102d4b08131c08b0b69340c69,0x142320018c9003b44ac510b8c8842f210024aa800214b00031c0030149340c69), (0x4f845a904dd402e5b2e8ee56104626b4a59a0282d1a60810c58003d40db9f141,0x4e044010c44002a412c0401800062a9414100082d08608108180008009396041), (0x790da36ed0223fd411f010b90ba1ae0d1d90a034700855368055342049350e44,0x5c04a300c400002440c0100882a02e0410002024500011128040040049310840), (0x0,0x0) ]
def g255C : List ColumnInfo := [(4,0,123,128,11), (128,0,123,4,11), (1,0,250,4,10), (2,0,189,64,10), (8,0,246,1,10), (16,0,235,4,10), (32,0,219,4,10), (64,0,189,2,10), (20,0,235,0,9), (9,0,246,0,9), (5,0,250,0,9), (68,0,187,0,9), (36,0,219,0,9), (66,0,189,0,9), (0,4,59,192,9), (80,0,175,0,8), (40,0,215,0,8), (65,0,190,0,8), (0,2,77,176,8), (6,0,185,64,8), (10,0,181,64,8), (12,0,211,32,8), (48,0,203,4,8), (64,4,59,128,8), (72,0,182,1,8), (96,0,155,4,8), (100,0,155,0,7), (44,0,211,0,7), (0,8,50,193,7), (0,12,50,193,7), (2,4,57,192,7), (4,2,73,176,7), (16,2,77,160,7), (18,0,233,4,7), (32,2,77,144,7), (33,0,218,4,7), (34,0,217,4,7), (84,0,171,0,6), (37,0,218,0,6), (82,0,173,0,6), (76,0,179,0,6), (112,0,143,0,6), (97,0,158,0,6), (104,0,151,0,6), (98,0,157,0,6), (13,0,242,0,6), (1,8,50,192,6), (3,0,248,4,6), (16,4,43,192,6), (17,0,234,4,6), (24,0,230,1,6), (64,8,50,129,6), (1,12,50,192,6), (10,4,49,192,6), (48,2,77,128,6), (64,12,50,129,6), (178,0,77,0,5), (170,0,85,0,5), (45,0,210,0,5), (77,0,178,0,5), (25,0,230,0,5), (21,0,234,0,5), (88,0,167,0,5), (56,0,199,0,5), (49,0,206,0,5), (28,0,227,0,5), (7,0,248,0,5), (81,0,174,0,5), (67,0,188,0,5), (89,0,166,0,4), (60,0,195,0,4), (57,0,198,0,4)]
set_option maxRecDepth 100000 in
def g255D5 (_ : Nat) : Nat := 0x1a38389ab129412684d101
set_option maxRecDepth 100000 in
def g255H5 (_ : Nat) : Nat := 0x18
set_option maxRecDepth 100000 in
def g255D6 (_ : Nat) : Nat := (0xe8b96929461344133c282e5a4a5184d104fa0968415284d156413aa28326a929894d102c5657b4a8599a54840778856d2b4115651901de216b4ad04595454075e0e26ab4a5044d101b7838c96529411344070f1e26ab4a6684d101af82ac4a5049a134407f80415464a5564d101de115b5ad04559344077a05ad2b411564d101 + (0x2c00201618103462b95a84a88f9c323e64300cb0 <<< 1024))
set_option maxRecDepth 100000 in
def g255H6 (_ : Nat) : Nat := 0x3510828d8049f3da0ca8005e000eb12453050a
set_option maxRecDepth 100000 in
def g255D7 : Nat → Nat
  | 0 => (0xd101ff0254824d09a203fe04a5049a134407fc094ac8a826880ef538a415564d101fc220aa32ac9a203fd04152955934407f42a3252ab26880ef91ab411564d101fe22b6822ac9a203fa45ad0455934407fc095a08ab26880ef938a411564d101ff0252822ac9a2033e992d5a9a1244077b1c520aab24880fe21055195649101 + ((0x5294d101af8f172ca529a203be45a95a411344077c1352548226880ef816a4a9044d101bf27172ca089a203fe0aad2941134406fc155a528226880ff825b4a5044d101ef011294a089a203de09a52941134407bc12ca528226880f686694a5644d1019f2c96ad4d09a2033f1aad299a134407fc095a093426880ef915a412684 + ((0x2ae250451901fc62b6822aca3203fa84ad04559464077d0b52548228a80f7a12a5a50451501fc62d6822caa2a03fc84ad045954540759aad2913428a80e7e12a4266851501de62b4824d0a2a03be84a9049a145407798a520b3428a80ef612a4166851501f6629082cd0a2a033e552f8a965344077c24549494a6880f7864a22 + ((0xf7a2694a78450101ef42d294f08a02033ec92d5a9a1404067d125a553428080ebb15a9226850101cfc2552ccd0a0203ee8921299a140406bb8a5f1282aac80f37148e250555901dce2b4b5280ab2039f86692a501564077b0ad254a02ac80eee16a4a94055901dd44d495208a3203be85692a41146406bd8adf128228c80f7a1 + ((0xb080e7b3a45026956101ee62a8a04d2ac203cece11409a5584073cbd226934ab080f791044d26956101cf4f48924d2ac2039d94aa599a548406ababd8b334a9080e7652a1666952101cee74aa84d2a42035d94ae6a965484073b2954b33429080d9757b16668521019ee4b6a54d0a82033f892d2a9a150406fd095cd3c228080 + ((0xc9a2ac827e19056193455904f51a54c3268ab209fa24a9064d156413f0cc2a0c9a2ac827a8d684a13455904ef121294268ab209fc2415284d156413f44832509a2ac825f8a0b4a93445504d71415253129a205aa39aa4a6253440b5c70d494c4a68816b8e4a625154d102bf155694a089a203ce2225294113440799aaa29134a + ((0x2d2528c268827a8a684a1604d104f712d0942a09a209e9a5a1054a156413b94a4a0a942ac827a2d685152855904ee5212a2a50ab209e9a561064a156413b54a4a0c942ac827e29454192855904f45ab0a3250ab209daa425464a156413f1482a8c942ac825f8a0b4a93455904ef125484a68ab209fc24a9054d156413d0eac30 + (0x3547054d0942c89a6e8e0a5192855934e51d30a3250ab2699e382a494a1154d33c6954930422a9a768d964a16441534fc1aac942c882a69eaa561064a164413d94b420a942a8824f890ba29294d104cf141534a529a2099e282a594a5344137872d2508c268826f1a5a825184d104b71d1694a309a2097e282d2946134413787 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0x11cf9ce1c69c51c39bf1bd9bc1b79b61b49b31a299e19c99819098c18a98918498318198017b97a17597417297116f96e16c96814e9351309261038f90d68b709487e07c87506d86c06785a05285104683f03783602e82a02581e01080f00d8002b4735a1324a509a578d0b926194a134cf1a1524c32942695e242e4a825284d + ((0x258607618158e580080f08b92736184000709a88703f811388b8737fb6634fb4532eb2a328b2131cb18313afd2e3aca2c2ac12b9aac2a4a97295a9128fa8b286a82280a7f27aa76274a67262a5e256a4f24aa4323ba3a238a37235a34223a1c21aa1920e9ef1ed9ec1ea9e91e79e61e49e31de9dd1db9da1d89d71d59d41d29d + ((0x25023800c0f00eca6fe1f217c0f40940be06e00e00b82eb803800c1140f10d90c4c7ca73027217c0f40be04b03c03b2b382e51138bc09787d02f81281140f10da0b948ca6ce33025e1b40be04b04703c0b318bf03f02f811c011e1800829740c201600103c22e49c58e1011d0b8201c0fe07e00389c09b080f28b820166561c + ((0xb9c0be07c005f02f81080000f3c0ce00303c43603243131ff0dc85f03d02f8128000000000003600100000000000000003827e0420000a504000a181000001000c4a2f427e04504004000a0526521c2031040012181000002141002181000000000386040c5a60e2e42b025e1f40be04803139790ac09787684f8138020e181d + ((0x7580040a2e4aa0a870128704a18103b09b609e05702f81d801c1180f10b8c45826e1cc0be04804503c42e323609b86302f812282381420361b210202ed86c84d8313817c08218b90ac09f8110028604028604814128704000a1c120504003c12e02ee86104b8149c04a1ca182299286094b8112e49c08a64a1c2000000000ed0 + (0x2e0be04200481608203b42e21b509b05582f81e80201180f20ce25c22de0be04703c52e5800c0f00c826a25ea37a1be04 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g255H7 (_ : Nat) : Nat := (0x68003915cb58dd59c002414000000001d4dcdbd5180545f43652c56c8fd4eedc98e748b9fce01c67daa51c0038f1dcc0028eb881db8002d5c000002cc2d390d0105db254a608001112d78204042084001c731eb1ece15c380051cf008a0e357840424503022410200100808220001000c1804e1c005021820102300801a08680 + ((0x8191d3590003dac6134a6dbc000002527c605c092a945850d7fd669de0d78980000039e0cbe98400003207fd56821d8b0451db9d644c5f789d00f83d013d1a123ca14cad3cc6d194ccd5014af18c86a8904bac1f0fac48003c0990c002599108002db4458d36170002c7402a0b0000df800000282f9a1940d629e6c54002cc71 + (0x188c577132d5a424496879cab9a6581cf40025c48e05f0e0d <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255D8 : Nat → Nat
  | 0 => (0x59644d101fe14a5644d101bf556a684d101ff14aa684d101ff14a6684d101fe4412684d101ff04a5504d101fe4591504d101ff49a1504d101bf5e29564d101fd4415564d101fa5519564d101ff14a5564d101fe4411564d101bf956a6849101fe85915049101ff89a15049101bf9e295649101fd84155649101fa95195649101 + ((0x51501dfc4266851501fec4126851501fdc4166851501bf5e2a594d101fe1929294d101be1929294d101ff1969294d101df1225294d101df19a5294d101df1965294d101fe49a9044d101fe45a9044d101fe4969044d101fe4569044d101fe04a9044d101fe4225044d101fe49a5044d101fe4965044d101fe04a5044d101fa5e + ((0x1fec5690451901fe84a90451901dece250451901fac4115651901f9c5955051901dfce255051901ddc9690951501dfc5a90951501fcc9690451501fec5a90451501fe84a90451501dec5a50451501ddc5a50551501ddc4256551501fcc41165515019fd66a6851501bed52a6851501bdd56a6851501bf94aa6851501eed52268 + ((0x5652950101fec9a78450101fec5a78450101fe84a78450101bfc56a6850101ff84aa6850101bf84aa6850101eec9226850101dfc9666850101ff84a668501019fd52b8955901cfd5238955901ddce250555901dfc6694055901fdc5694055901fbc5a94055901ff84a94055901dfce2540559019fd56b8951901fac9a9045190 + ((0x952101bf94aa6852101ddd9666852101afd56a6852101ef94aa6852101edd9666852101edd1666852101bdc9694954101bfc52a6854101ff84aa6854101bf84aa6854101efc9226854101efc5226854101bf84aa6950101bf84aa5950101df84aa5950101dfc5a55950101df89a52950101df85a52950101df89652950101df8 + ((0x19fd52a6956101ddd5166956101cfd9226956101cfd5226956101dfc5026956101df54d26956101df94926956101bf94aa6856101afd56a6892101ddc9660952101dece120952101bf94aa6952101ddd9666952101ddd16669521019fd96a69521019fd56a6952101df94aa6952101dfc5426952101ddc82a5952101ddd9aa5 + ((0x3625154d102fc94555445102fe1929294d201be1929294d201ff1969294d201df1965294d201fe3929294d101be3929294d101cf3225294d101fe24a9044d101ee6225044d101fe24a5044d1019fd929599a1019fd969499a101df94a9499a101df9565299a101df9525299a1019f9929299a101ddce1609561019fd92a69561 + (0x8450d23ee38678450d23ee34678450d239f3a6943559239f39693951923fa34d15651923f935955351923dd39693951523fc94555445123dd3e555345123dba6596051502f9a5596051502ee3929894d102ae3929894d102ef3969894d102cf3626594d102fa2519604d102fa3519564d102fb2419564d102be3929154d102ef <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0x904fba4192855904fab5192855904fe68293455904fe34a93455904de76253455904de64253455904fc76153455904fc64153455904fa76193455904ea76193455904fa64193455904fe34a13455904fcb5152845504fe68293445504fe34a93445504fe34a13445504ed39694854d239f35aa5950d23ee39a78450d23ee35a7 + ((0xe65a1504d104fe24a1504d104dce5250555904dce4254555904e9f5618655904f9e4158655904f8f5158655904dae5250655904f9e6150655904f8e5150655904dae4254655904f8f6154655904f8e4154655904cfb6612855904edb5612855904ebb5a12855904dfa4252855904deb5252855904fda4152855904fcb5152855 + ((0x9684d104ee7569684d104ee34a5684d104ee75a1584d104ee39a1284d104ee35a1284d104bc7969184d104fe34a1184d104fe6825184d104fe34a5184d104be6e69604d104fa6e19604d104fe24a5604d104fe6561604d104fe24a1604d104be6e69504d104be6269504d104be69a9504d104fc6e15504d104fe24a5504d104f + ((0x9104eeb5612859104faa4192859104fea4a15059104bce9a90555104fce4156855104eeb5a12855104fca4152855104fea4a16055104de6826694d104de6826594d104fe3a29294d104be3a29294d104be2829294d104fe3969294d104fe3869294d104de39a5294d104de3965294d104ee34aa684d104ee34a6684d104ea79a + ((0xde39252845534bf34aa0845534de79260845534de79250845534cf32612841534df35a52841534fd35952841534da76596441534f875596441534fe34a16441534dab6596441524f8b5596441524deb9252846104ddb9652846104cdb9652846104eba9a12858104efa5612858104efa5a12854104fae4195859104eab9a1285 + ((0xaa584a134cf3826584a134ed3969584a134ed3e55584a134de39292982134cf34a65882134fe39692859134be38292859134ea39a12859134ee39612859134ea79a20859134da7e254655934bf38292855934cf3a612855934fa35192855934fa751a0855934da7e254641934fa35192841934fb35592841934bf38292845534 + ((0x50000ed34a38554d34de3929299a134be35aa494a134be342a494a134de39a6494a134de35a6494a134de3466494a134de3826494a134de3426494a134bf35aa594a134bf342a594a134df3426594a134de3926194a134de392a094a134ee3926684a134cf3826684a134af3969684a134ee3925684a134ef3965684a134af35 + (0x7c1adc35ac69e0d339a1f34066744ccf9999326063ccc2417ea2ed65bb0b5d16462c545680abc94e428ca4f989b392dd25ae4b1895a929925264a08928121e240445e087710bc207a3e747840e471af632bc5f70aeb1412252043e07b00e4c1a1833a86640c4e15c426e043c082a0fe41b782da053a07f40f601570260045004 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 2 => (0x5e32b5255d2aa0152729cf5324a39d42ea7914dcc991932026244c1098092eda5934a8094e929a252e4a509489288a50049de937926c247a48649059202a3f447b08f491e0a39a46628c29171a2d245988b1916022ba446088250f12163428e850505ba0173f307df0f791e5d3ba67524e861ce538f871ace1c9bba36a26d00d + ((0x6264c42987ef0d0616c424383730516052c05d7f64fcf9f653eae7d0ef981ef63dc57aa2f375e5b3c4d788ef0d9e12bc0977daef71de03b9976ceecd5d713ad174a4e8adcdbb96f71f6e1c5c2538237024df55bcc37246d76d86dac8b50768facff99d0330064ecc8358c1b125618ec14d7ceaef25d80b8ad6b52cca5854af89 + ((0x82f90dea2bc317666eae5ca6b7b56cead68da73b4576686c6ad88db0495dbab8dd6f4ad015992b1ed616ab4555c2a99d4b4a881500e9c7d31ba5e94b0a937d1e5a39346e28bdd0fca1c1407e801cf8f9ea53d06750ce7a9c2336766b04cc098412f365c84ac4941d26ee4a3c8e9918520e2408c77c8db919fa320c5f98b4d14f + ((0x5c2704dd86141e0364680c51049db3344ac3d86f03607c05803842820d89522051f42544387b0ca1681d02f02a00d51ca20c306238440448f10199613a22c3986d0ac0c81781d006036a2423f84a8811061ec3085e07c0bc099a8c74c8e8f1d0779deb36d663acb1f9367253e454c85b8e8f18ce279c3b3856b062e0a9c0557e + ((0x84909c0f81781700708504c0020f01da2e13863850788d01a22093a23e86d87b0ca1781d03f03607c05804023c3605d48d4e09bb0da1742503a05e05c01a11c1b43425488147b87b0ca1542503a05e07c01c0d0c33800cc71800891e2093a666c3986d0ba1181902f03e00c0780db1a199a2423cc3d8610bc0f81781f00683c4 + ((0x340620b94eb12812e1dc3485d09c0d81d02f02e07c0380501e2b78680d159b12223025c3b86d08a1281781703e01c0221141e0368680d091c20625025c3b86d08a1281781703e01c02411c2283c86cacc17420538e5dc7787f0d21742703a05e05c02411c1e0b7166c48c3885e07c0bc0f8070060451668ba1019712b61e42e + ((0x6b8770d21442f03a0440bc0b81f00e01108a10c1891111ec3604b8770d2154270360740bc0b81f00e0120860f01c0360680c54838770d21442e84a0440bc0b81f00e01208e10018a9d625025c3b8690ba1142303a05e05c0f8070088430800f41e2b786c0d018c2053ae5dc710a812223c3f8690ba1381d02f02e01708a0f01b + (0x8850742e02080b00082f12d21ac0080bc4b485b00218610a103b85c8804d895f0fe1b81f02f03600c0180f01dc2e44026c4af87f0dc0f81781b00642e137600c0081141e23623e27342a84e07c09817812c2383c0762ce1718b70fa1742284e07c0981781382283c46d0b84d98c70da1542703e04c0bc09a1001e034062a618 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 3 => (0x500204306208c4b509d0bc0fc0f807005043054104306c0c44b50950d21442d02f03e01c01810c08a860c2003d86c0c61049601542743485805e05c01a0bc54c2012c23e84b87d0c00bc0f802c178a9c402644b50970fa1401781f00584006208f10309b0f21b42a03f03e00b06c0c51049912d44984d8790c217c0f8030010c + ((0x84426684e87005e07c0100a8106208d4ce8750fe006022a18206242b434851017a8e10aa0040020031a12a1c42d02f03e01c01210011a8770d00850860c61029791e02a84e8790be1381d02805e05c01e0be1008fa13a1c01781f0040360632668908f61321ec3085f03e00b0462670928fa12a1c43685a07e07c0160bd47086 + ((0x8c0ac12e1f42b8460780bc09803421a3846c0c4c640ac12e1b42b84405e04c0800f418a23815825c3685708c0fc09803242885804009c00a23cc3b030e1b420c1222242c02f02e00c01221410840bf42980102103405e44cc7609b0fa1701e02f02582f44023e86e09b0e217c0f8026c00229686a0a90bc0e818c2384004002f + ((0x3105409011e0950d61781802f03e00c018638431800c17e8630018420680be1518ec1361f43603c05e04b05e6142002003406282805609b0fa1781e02f02600c86c0d0cba0a015826c3685f09c0f01781700600e0870e21b031c1361b42f84c05e05c01610cc30410018b0d31702b04b87d0ae1301202f02604306265d0 + ((0x814e38ee1be1fc348580bc0e81781700700238400410840040042b00200391dc25c2f03e05e04646c0bd1150950de07c00e000000008504428221418580808da84e85a0740bc0f80b00402f44142542f81f003427d0a158006c0022384004008006470869001a27844c26c3685606c0bc0f802513b877001c27d0da143b00080 + ((0xbe1fc3703e05e06c0130b84dd80300242e137c34c6386d0aa1381f02605e04b0828820e50ee0628324410704d89502bc37c3f07f0dc1b81f02f03c04f0828d81911fe1ba1502703e04c0bc0d80321b034840a778690a81222004787f0d21602e84e0740bc0b80481b0340640c41729d625c3642e84e0740881781f007c3605d0 + ((0x3081041d1264380718bb0eb0da1642702a05e04d08b8748b91111e6368540941061fc3285d09e0e81781e00883cc3a6648b88f31bc28c3d8610be0f81781e00761d83a6648b911614428c3d86d0ba13c1902f02758de1421381781e00303a90a128de1221a4288550620f81781e00509be1be1fc3703e05e06c0180244d895e1 + (0xf8728da12a1c43685f02643306404106509d0be0780300244b28de1221a42885e08a0c41f82f03c00c02ba3684e85009a0ec1781204c88f01542743685005e048132044c6d0aa1221d43685d07e04a0760ea1741ca2f43b04f87f0da1142783e05e0780300401e03b0750cc16c1cf1b827c3f86d09e0f81781e00783a838429c <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 4 => (0xc00906506dc6e0970ee1842e04408e0dc1781703c00e06506dc6e0970ee19c1b82f02e0780300305041b71b825c3b8610a811c1b82f02e04c14106dc6e0970ee19c1b82f02e0780300301921a02b42743e86b0a01041781e005c1c01942743b86d0a20bc0900c98e49942a23f8748d61321ec3085f07e07801c2650bc15020a3 + ((0xa03245488d08e8dd0fa1802f81f005a9902ca1c306288e4ea99d1ba1d43202f03e00a062a6407e8650de0060874d01880f50fa1bc1f02f03e00a2680c64ea99422a3543e86f0680bc0f803084686c04183144042035240e2484045781602161c031840423010a2da8bc15a1d82543585409e0580140c80660970f61b42882f03 + ((0x8710c1099022218313203c43060640b00f91b42743502005e07c01408c4c8870c1889903205a0881191b427c0f80281181902323584e86a0a017c0f80284c81610e18310462640cc0f01ec27c0f8024050e0a8604852050884202088502a6484040c4856860c18a99211a1842680c817686101e12e13845743702c043829049 + ((0x1903105c4a891a9d32561a81102f03e00d08e1021a03224603dc6b87b0c40bc0f80302183c06c0c4c3605205e07c038028238410780c817523840a704dd8680b40bc0b80382180f70f618c3405182003d0780d018c2053a42a04808b0d01681781700781902c03f46d09d0f40801781f00502303204746b09d0f41402f81f005 + ((0x6e05d0960f81781f00442141161b02d831417192b0d212c19831a1089cb0d81642583e04383f0780c888d8db0e017c0f80242003c06261f02d02205e07c038028228410780ec1902e539446c6d8780b40bc0b80382001630ee1840780c54e997a236348540901161f02c05d0940bc0b80401f03c06448cc958600be07c0120d0 + ((0xa41142083c46c0ca17323137054c660970d81781302f028031930c2ac3f02f02e0070780ed1702883065ec3f02f02e00a0800f01880fe05e07c0380202002970c18450788b80ad1181f826c3c04e05e05c018100c39860c20434062a61c698ba1582604387c0bc0bc09b0d01899741ee3685609810e1f02a84e05e04c01d086c + ((0x480bc0d803820686804183f0780c888a09b0e40bc0f80241f03c06448d10209b0c40bc0f802818605e04c08c00a0f01d89b12b023c3f86c0be0f81302f03600c01c11c228410780bbc6f87f0d81742783605e06c01c10617415e04c0ac01801c20a2082bc09810a11c2083c0762cc1942e82ac45c698bc12e1f02e04e04c0bc0 + (0x268da15c2684705e05e0470800c50888b01702b04f05c0480bc0980302028709430208c0b087b0c80850800c507a8d117c2604605e05e04c016101438410d08a0f51a0298480850fe1b02a05f09e0d81202f036011081014208008c07b8da12e1e43502f03e00a02203c432054042a86042023644085805309010a1b02a0560 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 5 => (0xba1902683f05e06c0144570284810025800c04d82b001841554a8e0de86e0a81341282f02542e5540720d890708e01b50ea085c680c85509912263743005d05e07c0178744c80f31a21d43683d05e07c01411d174aa43921c5132244c6e89a1002343005d05e04a13203cc6e89a1021d43683d05e04a210c14400742a84705b0 + ((0xe03213323743005f03e0080784b817115d0c60060780ca0d89a92fa3743e86e0a8114178130208330654714c89722a83ec728d50fa1902f04f07e0bc0d804a9a03213225e43580181f83212323402e82505e07c0121142083285d4704ba9141f63946a8740bc1341781b00842e23846c4ba86d04a08722b814c006a9110015d1 + ((0x7c0e80500584123725c8ac8ef0fe1bc1e82505e06c0188748da9711961b82d04d0520bc0b802c20c3350f600c00a1142083c25d25e0ae0fd1ba1f02f04c08e0bc0d8030080470820cc1909741f6394688b810a1fc3605e09e0fc1781b0090458660ca4bc15c1fa34c668770d81582382f02703f06425c07d0910f60bc0f80241 + ((0x61e82304b05e0740280382303c0770cd1749711761f82f04a08e08c17813822c1c43725ec688cb0ee1b82982f025c3385c86e4ba15b1b61cc3d82f03a024028036400800822832836a5dc688c70f61b82982f0258450820f11741b11961b82d0470460bc0990cc1942e83806c8808ce0be07402802c9b43385d0700d91030dc1 + ((0x4106e0aa9351ce35c3b8670660dc1781702703b45c4820dc1570ee19c1b82305e05c0e80900a00f45c4820da9782aa3984b8770ce0dc1182f02e07404804119c1b11661840828ba0d88a30ce08c10e0e90e6800c9021b42b636c3d86b0760bc0d81d01200c0820ee1721b42be1fc3783b0460bc0e80301dc3343725d0ad8d917 + (0x8cc1921582023304f05809e05401802e1a0302364564768dd0fe1982b04f07e0bc0d80381d83005006d4b81571aa2dc3d0520be0bc0e80381d83045c0b40d815613e1fc350520be0dc1182f03a0100768ce0da9782ae35c3b86a0a415c1f82705e05c0e805008a2e836a5e0aa8e71aa2dc398770ce0dc1781702722e2 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g255H8 (_ : Nat) : Nat := (0x45052499bfa5bc92daa54ae43101e2c1c001ae962e39680004b9818503c001c8ad307afc0960e692070698dc500345807ee00001210808000cb010a4c79a00302003a440050200c80100018f26006840210584004031042183001e00880201c4012404a9d06000042e0418000009080000d00102c0040200c800400009 + ((0x2280f81b61cc452e76bb48447c9335dfc229a904ea2580014c4000f2300038ea29a5376264000ef257ca468001d03a7dc29f90c89ce69c84f0197115247010833626d5e039d93ece5e284c1309e45f4740402049cd0b4053a800000046369f2c1329b0000bfae3c000370c0505214fad0098e312a28dd48b81e16a26b40e1a88 + ((0xb32f8811123161b27413d84021600008c2a7a2588000d08000c5529e4a2f506c322c58ce600040f0003e26e5dd1380024728d965d3af4000ee0000405fd1e637f2a1c0bde60003149374000000768c1a809a000223f360000a5e357f0a09aa726f3dac8a8b3ee286b5145c86d1f426319d5b948c785d9de99185553f29c99ed0 + ((0xa000233704400042d25b32cd85e000a408476d8aa830319048c1750ae7200aedf84c900019050fa10ce5800009e9affc4a2a20001ea307ba238000036c8a0000241e4a000232800182163a2a2e248000d42d0ca4762970003427454a0336d59a35482cfe53616259dec7d78e8e857070f4003bd60a6ac10005b115f08ae40 + ((0x296756e472d64889d90a869232210c7ea808c5c0ab70dcc1684ac56c6f41b2143a180004adc47e0004614a1ccde000000445400021d1380aa05c7f12032803b40d033f761126504518a3f800000140dd52d0d016890d41e843b47c000f22735c9b7476375bc04000c4200028d4d58098e8d8bb88e3ccc022a336197c78000330 + (0x42a000b885880000000c348000001cef30553c0000 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255D9 : Nat → Nat
  | 0 => (0xf710555901ff8a02ac80dfde2546407f6208a3203ef55651901ff8a828c80dfc42545406fead2a2a03fb10451501fb882a8a80fdd59545407fecd0a2a03fd4894d101feb34a6880ff596534407f8a529a203f91044d101fcab226880ff59a134407fa2a09a203fd5564d101fd2b224880ff99a124407fc2a092203fe55649101 + ((0xfecd2ac2037f66956101ffb342b080efd9a248407fe412a42037f20952101ffb34a9080dfd9a548406eecb2a4203ff66852101dfb3429080dfc92550407fe292a8203f738554101ff9342a080ffc9a540407fe2d2a0203ff25950101bf92ca8080ffc56540407fc252a0203fb38450101ff93428080dfde2556407eef0aab203 + ((0xf38653440bf1ac89a205fc9604d102fe6ab268817f34553440afdcb28a2057ed5945102ff2a8a28817eb5511440bfacb29a403fc5294d2019bf2ca9080ffa4a5404077b9129a203fcd294d101fcc8226880ffd56668406feab334203ff5499a101bfaa4cd080ff94a668406fca5334203ef7865a101ff904ab080dfc82558407 + ((0xe6a9a8c91df34e54548efdad2a2a47f6d6551523fe6b1a8a91fdb5151548f7da908aa47fcd4345523bf72ca2891dfb5651448ffcaa28a247fad5445123fe6a9a2891efb9654840bdd20cab205ee90651902f76ab28c815fb5a54540bedacaa2a05fe96051502bf724a2a817db5151540b7da908aa05bcd894d102fe72ca68817 + ((0x790555904f9ea2aac827bf619564135fb0cab209ef90655904f5ea32ac827fb4a156413f3a68ab209f3d4545504ff69422a827e74d1154137dcb2a4247bce4858d23de6a42a691df39a54348ff9cb2a1a477ce5950d23fe70ca8691ee3e114348ef9a72ab247f4d3555923fe6a1aac91df34e54648ff1a68a3247eed5651923f + ((0x5a50aa209fb96055104fcd04a68827e79a534413f3cb29a209f8d294d104fcf0ca68827e79a13441373cd09a209f9d684d104dceb4268827e796134413f3ab09a209f8d284d104fcf0c268827e746134413f32c09a209f99504d1049ffc4aac825ff625564127fb12ab2097f90955904bdea4aac827df615564136fb0aab209f + ((0xb9a1284137dad094209bee584a104df6ac250825fb4a6184137da510c2097be4946104bbf2ca30827fb4a1184137da508c209efb8658104ffcac2c0827fa4a160412ff4d2a8209f7b8554104ffcb42a0827fa4a150413d7f0cb2209eb90659104fdeac2c8827eb4a164413f72a0b2209f3f8555104f9c82aa8827ef5a154413f + (0x69420a9a7e7591054d3d5a8cab249ead4641924f76ab20c925fb9a505492fdad282a49f6d6541524fd6b220a927cd455544536ff0a9aa29f3d4541514bf694cd0824ff566684137da5334209afe695a1049ff2cad0826ff56568412fda532c2093fd6996104df694cb0826ff5a1584136fcb2ac2093fe6956104dfeb4ab0826f <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0xe6882134def2c4109a5f7965084d37bcb084269e9f8659134fcf2c2c89a7e34a1644d3f3c10b22697df8955934f4ea32ac9a7f34a1564d3fbc10ab2697df8941934f4ea320c9a7b7559064d3f9a508326979e4945534fe69422a9a7f7821154d3fba108aa697df8941534bee44a0a9a5f79a5054d2fbad282a69f5d6541534fe + ((0xa510c269f5f8554d349ffc4aac9a7af519564d3fda508aa697cd299a134bef2cad09a5f75a6584d3f9a532c2697cd2996134bee84cb09a7d7e15584d3f1c9294269fce594a134fe70ca509a5f3825284d379cd094269bcd684a134fe72c2509a6f3961284d379ab0942697cd2986134bee84c309a7f34a2184d2f9a5304269bd + ((0x98362833b830d02eb02ba0295826c0242822f81fc01c88195016b814e812a00fe00d700a600818055802e800035fb0c8328be7d5641945f3eab28c9acff52668416efcb2a420b77e5946105dbf3428a82edf5a145416efab2a320bafd8651905f3eab28c82cff965684d27fad32c269bed2996134dbf2cab09a6fb961284d37d + ((0x20d188cec8cc58c998c750c490c1d0bfd8bd18ba80b748b438b1a0af30abf8a938a678a3b8a1c09fc89ce09ac0994096a8934890108da08cc08a2888d0861083f081d07f887d187a58797876e07650748071c06f006dd06b3869686810661863f860e85e785b9058f85638532850b84da84a984878459042f840b03df03b3038 + ((0xc97f817ce97a51767972f16fe16c816949672963f161815e495b3957b154a151e14f994cd94a19496146c944a9428941313ee93ca13a59390136b93421318930092d212a8929312649231120791db91ad11721141110d90f310c2108e904e90228ff18fc58f8d0f610f2d8f018ece0eac0e7b0e428e140de58dc38da18d708d4 + ((0x8218da161a138210ea0d620b6a0882077a064a038a0029fd19fa09f799f439f129ee69ebd1e961e6a1e3e1e199ded9dbf1d9f9d761d451d1b9cf99cdc9cb09ca01c6f1c431c211c0e1bec1bc29bb21b839b529b1f1aeb9abd1a911a6f1a4f9a3a1a0e19f119de19b219901970995d9936991718eb18da98ae98851860982d181 + ((0xf0da2066512c26882218761a8521584c0f0240b81606804aa302a0929dfa9b62991a96d2950292e290c28ea28c32899a870284ba82c27eea7bb2794276aa737271ca6f326c72698a674264aa619a5f525c9259aa569a5452516a4eaa4b2247c244da421a3f0a3bfa393a371a34fa31ea2f522cba2982269a231220521e321a + (0x2e0780383c8d0348809d61d86a1485a1303c0902e0581e018044470d8344a9238838761a85a130340d02e07803c3c0da348809d6651261d86a1485a1303c0902e0581e01804c360808fc248861f8621784c0f02e0680200e8809723b09a208861d86a148561303c0902e0581a0110d92a48e2042688e1d86a1784c0d0340b81a <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 2 => (0x71143c0d8340b89d4498761a852168421303c0902e0581e018050470f0b78d0342cd1261d86a1485a1084c0f0240b816078060141143c0da340d2204498761a852168421303c0902e0581e0180503c8d8b30ba202719763b87e1a85a1303c0b8160100d83408387e1885a130340b81e00b114368d02023d87e1885a1084c0f0 + ((0x84a8f4268761886a168440d02e0681e0280484008e2025909e1e86a1784c0c03e0780342f2a620264960488fc2587a1a8521303c0802e0481e00804c400d82025909e1e8621784c0d0200b81e00e0d82a08c22880964278721a85e130340802e0780403608a202649644b0961c8721a8521703c0b81e0100bc9621a852160260 + ((0x100d82226612c268721c86a170340f02e078038360a8230889983509a1c86e1784c0d0340802e078044360c520a661242687a19852168440d02e0681e0280442f8808f23b09a1c86a1484c0f0200b8120780201010c360808f83509a1f8621784c0d0200b81e00f0d8998491223f0921d8621a8521703c0b81e00f0d82a08e20 + ((0xc380d831092208278761a85e120200b81e00f100360c42344a09e1d8761a85e1184c0d0380b8160780601310c400f6360c62065d8e02a0922387e1a85e130380b8160130d82f08209e1f862178480802e0780600d0be2023d0d8258761a8521584c0e0340e02e0581e0180482f8889923b09a1e8621484c0f0200b812078020 + ((0x9e1d87a1985e1184c0d0380b816078060130d82f0a82308a09e1c86e178480802e0780600f0bc2a888994360961e86219856120340e02e0581e018048400c50d8258761a8521584c0e0200b8160780601010c310448f4360961d86a1584c0d0380b8160780601110c380d8318278761d86a1485e1184c0e0200b816078060131 + ((0xa178440d02e078060080443809e220861242787e1a85e130300d0200b81e008044278498721e85215801e1223b0961c8721a8521484c0f0200b8120780201008a12c278761a85e1303c0b81e00b0bc278488fa1a85c0d80202f09e1223f0961c87a1485c0b81e00c0a8230852082787a1985e120200b81e00d100360a82344a0 + ((0x1f86e1784c0f02e0580342f88a208480dc2487c0f02e0780a0180200e0b2228821242787a1b85e110340b81e0180200f0e02c0922084909e1e86e1784c0c0340802e078020111102c8498721c511212c258721e862188521303c0802e0481e0080402c049800c2f8830961c87a1485c0f02e07802c3809e220862084909e1f86 + (0x2e8809c0718e43b0de1f07e1b06a1605a1303c0b81c058050360d32208312c3787e188501684c0d02e07803c2f4898621b80142f48b09a1c876188621484c0f0200b812078020100bd2025c8761485e0180202f4808ec268721c866148521303c0802e0481e008044420bc97c2687e1b85e1303c0b816008034420d02f23b09a <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 3 => (0x61886a148520f02e070030a125a8dc258621885a0c83c0b81c00c0f2340d30d61d86a1485a1084c0d03c0902e0581e0180483c0b89c63b0de1f86a1684c0f02e0580370dc2787a1784c0f02e078026368830d02a0922008e1f86a1605e130380b8160100d8320b89d4490ec350741a85016840130340f0240b814078040158d8 + ((0x87e1885a1084e0f02e07004045875174458d42987e1a85a138340b81c01003c3c8741d665176370a4298761a8521684e0d83c0902e0581c0142e0a00758dc290a61d86a1485a1183c0902e0581c0112868dc280ac248761a8521484a0c83c0802e0481c011284a024a8dc280ac248761a8521283c0802e0481c011284a023709 + ((0x128320f0200b812070044a025a8dc248661485a0c83c0b81c00c2810e03a8d42b0942287a198521684a0f0280b81a0510f02e4781c45d0ee350ae1f86a1684e0f02e070040450f0b62821d43b0a4298761a852168421183c0902e0581c0140f0b62821d4398dc290a61d86a168421183c0902e0581c013114378751723d8dc29 + ((0x921e86e1784e0d0200b81c01005c1123c8d4280a4260821f86a1784e0d0200b81c0112641723c8dc2b0921d8621a8521783c0b81c00f2649623d8dc280ac2587a1a8521083c0802e0481c011264966370ac258721c86a1485a0f02e07003a96444116350a0290961c87a1a85a128340b81a050044a0a370a02b0921e86614852 + ((0xa85217040128320f8220b812070048a1280152480ea370921d86a170401283e0882e0481c012284a02370961886a1485c1083e0b81c00d28496a37096188621704a0c83e0b81c00da8515055100420ea3509a1d8621a8541283a0982e068140132d8a085e0e82b098218761a8521584e0d83c0902e0581489905c112350a0290 + ((0xc0140cc9925b158398dc258721c86a1485c1283e0b81c0110711806296454158398d4258721e86a1504a0e8260b81a050050a025a8dc248661485c128320f82e070034a04550e03a8dc2508a1e8661485c1204a0f82a0b81a07004c390c8a00701b4541583a8d42687a198521504a0e8260b81a070040162841503a8dc248761 + ((0x3e0882e070000110f833471150548fc3a8d82d09a1f862150401383e0b81c013264178548fc388dc248761886a1485c1383e0b81c011072174541544010a3f0e83a8d4268761886a1504a0e8260b81a050058b60cc1c45410c3b8d42787a1a85e0f8220b81c000044a9070992581523c0e6370961e86a170401083e0882e0481 + (0x8d8258761a852160401183e0982e0581c01406c15e3609e1f86e0f82e0700282b0701b0621745410c3a8d42687a1b85e0f8220b81c00004c3306c9985d1505410c3a8d82d09a1c86e150401383e0b81c0140cc324701c06e9945415c3a0ea3509a1e866148541383a0e8260b81a070040190f833070184570ea3509a1f86a178 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 4 => (0x1b8601523e8d82687e198581383e0a82e07008010479170561043b8d8250802387a198581383e0a82e0510cc328570e6350b02e0961f86a160401383e0882e0700483e2d8322821c06e1543209e1d8761a85216040138360f8260b81607005c3e2d8328570ee350c03209e1d86a160401383e0882e07004cb60c8a08721544d + ((0x921c07a190501783c0b81e0100c69942908a1e868160240090f1340c49da668da1e8641504e0e83c0a02e0681e028048310902005a9284a8dc24860190501683c0b81e0108e0318810a422838090020380c6240809da4a8da1e8641504a0f0280b81a0780a0122d8a085e1583b098200861d86a1485c110460f8260b81607005 + ((0xb81e00d0c42326416a1c8701b8020400c42305a8dc268701c86c1503c0b81e00e0c42326419a3509a1c8601b0540802e078038312641905a8dc26872180641405c0b81e00e0c4990440f01e8621b8020430c41103c8dc2487a1806c1783c0b81e00e0c499064170448d4248701e86c178340802e078040312641905c0f2370 + ((0x8460f02e0581e0180444510c344458d61f8681405a138340b81e00e11c400d8344a9230838de1d8681405a138340b81e0110c40ea3709a1e86c14050138300f0200b810078000110a8290678010431002a0a68dc2687a1b0501003c0b810078000100a82306411a3509a1e86c140540b81e00d0a4190580fa3709a1e8641702 + ((0x360961f86a1004e0f02e07803c430f0360d0310809061d8681405a138360f0240b8160780601411c400d8310809d05a0961d868168421183c0b8160780601310c400f43c2dc340c49d65d8ee350a82408e1f8681684e0f02e0580583c0d8340c4202518d61d8681405a1183c0902e0581e01804c36084202758d8258761a05a1 + ((0x58471143c2cc2e271970558ee3787e1a05a1204e0f02e05804c3c0d8340c831081926360961d868160421183c0902e0581e018054400f0340c49863587e198681405a138360f0240b816078060141003c8d0312601863587e1b83c0b81e00d114430c51103d8d82587e1986816842138360f02e0581e0180504510e344440f6 + ((0x78050430440fa188680861003d8d8318580ac2408a1a05c0a02e0580384310216059110458d42587a1a050150200b81e01011c450f0340c82e0838de1f86a138340b81e018040470f0b78d0342cc324458d8258761a05a12042100460f0240b816078060181143c0da340d03248c208258761a05a120421183c0902e0581e018 + (0x3c8dc248781405c0b81e0180304305c1103c8d4248701f8681405e138340802e0780444008c1621d86808610c3125e0fa340ac2408a1f8681784e0f0280b81601110c400a82383c0fa3509a1d868140540802e078040430d83108016c248601a0501702e0780600e100360a8230882005b8d427872180681405e138340802e0 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 5 => (0x350ac2508a1e86c1684a0f02e06816008044400c41182487c160200b81e01802c4008c16a1c8761a051c430c4978468d02a0902287e1b0581784e0e02e0580444008c0f6360961e86c140580802e078034430d83108e0921b0580802e0780600c10c1103d87a188681471003d8d83188e2002a0902286c160580b81600f10031 + ((0x84e0d83c0902e058150400f5360c5234811682b098218761b0561183c0b816068020140d8340c420a370942008e1f86c1784a0f02e0580200004a368809304e8d42b0942287a1b05a1283c0a02e068144360bc20a370941683c0802e07802000034368868dc278761b05e1283c0b81e00c8862042908a1b05a0d80223688620a + ((0xe1383c0b816000034431008701e86218061c430d83108c16c2705e0f02e07806000034406370961e8601b050140400f0200b8100780001010c400a82961c0718400c58d22c0b82b098218761b054158460f0240b81605210c3125d1143d8d82b098218761b0561183c0b8160680201310d360c5202300c82b098218761b05415 + ((0x40400f0200b8100780001010031a3709a1f86c1784e0f02e0580000d100310440fc2705c0b81e0180000b10e8dc268761806c14050138300f0200b8100780001110c400a829618061a360d03125d0a02b0942008e1e86c1784e0f02e0580200004c316370961e8601b0501404e0c03c0802e0401e000044438d831c2787a1b05 + ((0x61c8721b05a0e8220b81c00e2a90f03d8da25080218721e8641684a0e82e068140110e024084164490de27872180681405e110300f82e0780492184b0da2486c168401303a0b81e00c08c2208416c4a12c36892180641405c0e82e078040400d031a350a02b0942008a1f86c1784e0f02e0580200004c31a3709a1d8601b0501 + ((0x8d61c87a190541283a0b81a0780a0130dc9905c0f237894200821e8641405e1383e0b81c01105c9103c8da250802087e190501784e0e82e0700409905c9123689c208761886c1783a0882e07003ca363689c200861e8621b050148420e8220b812070044a32649163689c200861e86c140521083a0b812070044a32658da2708 + ((0x8a34749223887a1886c1405c100420e8220b8120780201511e340c8a30718d61e8621b050170420e8220b812078020138d0322a8a3070992458d61e86c1405c1083a0b8120780201328e1d474996358721c86c1704a0e8220b81e00f11c418d8320baa38811c0701b23a87a1b0581704a0e82e0681601511c3e8d0aa8750f03d + (0xd264912348761886c1704e0e8220b81e010114410ec320b91c07097a458e23a8da1e86c1605c1283a0b81a058058a40828de1e864170401283e0b81e00c8e0328801c06c8ea3687a1b0581704a0f82a0b81a058048a424a054118260062901c249098158260070f83228c9223887a1b050170401083a0b812078020110c82e2a <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 6 => (0x83c0c89923a8da1e86c1405c100420c82e0481e008044372640f23487a190501704e0f82e078034410cc324701c06e9925d8e23a8da1e86c1605c1383a0f82a0b81a05805d340c82e26497a188641182600a0fc322448ea368721b050170401083a0b81207802011114378d09103c8d82487e190501704e0e82e078040378d11 + ((0x20e8220b812078020131143c0c8a38821d0760961886c1504a0882e078040470dc330c80f23487e1a0501704e0f82e078060101143e8dc3225e0f03e8da1c8761a058110460d82e0581e0180503e0cd2e470970560f63a8da1f868170481383e0b8160120f9340c92e25c0fa3509a1c8761a05c12044100460d82e0581e01805 + ((0x4a0f82e058020110f0360c8202488ea348721b05c128320d8220b812078020131043c8d8328811c24e8da1e86c170481283e0a82e06816013104322781d25c1523b8de1f86c1704e0e82e058020110fc3225d8721f05c12044128220b81e00d0f8328818621b05c12044128220b81e00d1143c874922388761886c1405c1383 + ((0xd87e1b05c1104e0f8260b81a0120f8330b81c46097a398d61f86c1783e0982e068020110f83c4d8324821c06c8ce1d8761b05417044138360f8260b816068058451043e0f1360c81ba5e8ee348ce1d86c170441383e0982e068055360cc2e0701ba5d10a3b8de1d86c1783e0982e068020120d8340c82027c1d23a8de1f86c17 + ((0x170420d8220b812078020138de340ca1d8701021b05c1381e02806008038410ee338ba1c06e970568ee3787e1b83e0b81a008044414d9208701ba398761b054170460f8260b81606802012105364809e8728e6378761d86c170460f8260b816068020131043c0b815e3787e1b05c138360b81a00803847104330c897a398d22 + ((0x200711542205c1204400a104340c81d0548ea3687e1b05c1383e0b816008040450fa1da368721d8621b050170420c82e0481e008044450f9370c98d61c87a1886c1405c108320b812078020120f83c8d83247787a1b05c1383e0b816008038340c89e0749723b8de1e86c1704e0f82e058020101143c4d0322488e21e8621b05 + ((0x303e4d8324821c8548c033098238761d86c1505c1104e0d83e0982e0581a0188da204711524c13a370942287a1b05c1204a0f82a0b81a058052370ca1d8701082486c160401381e0280600803c3203a8dc2687a1b05017040100300b810078000100dc330cb1d2641905c0f2370921c07a190501704e0f82e078052390ca + (0x8034290641603e8dc268741a85c0802e0780342a08c190448dc2487c1a8501702e078034230648f03c8dc248701d0601a85c0f02e07803e1da3709a1d8601b05017040100300b810078000100c98dc2587a1806c1405c100400c02e0401e0000403e8d83247709e1e86c1704e0f82e0580000e8dc328741604309c1704e07806 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 7 => (0x3419058910448da248701d0601b05c0e82e07803c370641023c0f2370921c0741806a1704c0f81e01008e8dc2687c18066140501003c0802e0401e000040360c42a08f0941a85e0f0200b81e0080000e0d82f08a8dc2506e1683c0802e078020000382303d8dc258781a8501702e07802c2a08c190458dc258781a8501702e07 + (0x290641603c8da2487c1b05a0802e0780 <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g255H9 (_ : Nat) : Nat := (0x7c49a2b8001e6854848ef5df035e7d20659ceac7348b158001ed1c2020d81dbafc8695a96882095727d33c1a9c4484a6b181000e040045801e0102101801c4720112000020818902002ce050a0818d0a00f0000280050a400240af80a000002821418a911200e0036140000000e0c000800002340193c18300000c8800a04208 + ((0x1cc5e0552381c4176ec0a55227186000052f614647a0002213280c2f82ec17ebcb4a440340e1baa195c7e037d8a799a00012f9b14dcbadfd6efac24e7c96444026204c60cf81bac981f2ecf5b1a118e5a8515213d00f528ac157bd44bb497211b27b8980a2e0fd9b78b9cceb1d088451b645d364ac4000000a65da87c736a + ((0xcfa2d95d441aa0b258a4119810eb092c34e357c6367bc57b9db0fe6eb93818cadbc00043083ec00087d70a00039d20000000001c03c1e8727327136abfa71ac0b16e80b00000000006fe443e9d21aca16f0d227c000838f26a3f4008e0e24663cc959ab9169ab418f32eec29a0088b6280808c2a047e0000002968487a6a67c + ((0x8110c78b0412000678d35f5c20661433bc2d782dae64706c051207c7bd840001cdc4533404000d042377a270660000001b88000812c5c32d0000cbe9280002c2600000063a1c1a000000030ad4600056c71244f908b061eaf484967712b800302a63400062d40012223325ab40004e000000000940000000003552b0081bc167 + (0x1d0887342ad0a9e08325fa0c001f0900060fbd32a65a473307a0e29d0007956c0c0000003acc83b4f9710311b490ad904d48af8152cc931fa3e00147857ff36f04ee6bd270896c780000007bda5880 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255D10 : Nat → Nat
  | 0 => (0x3bed4840bfa58102fed5640bfb51902fed4540bfb45502fcd3440bfb45102ff545807f54d201fe524806ff96101bfd58406ff92101bfd48407fe54101ff940407fd54501ff541407f74d101fed24407fd9a101ff568407fd96101ff558407fd92101ff548407fc54101ff140407fd55901ff546407fd51501fd534407f949101 + ((0x14ffe68412ff9a104ffd68412ff5a104ffe58412ff96104ffd58412ff56104fed28413ff86104bfe18413ff46104ff960413fe54104fbd64413ef55104f9d34413ff55904ffd15412fb92123bed4848ff358d23fcd5348ff350d23fed5648ffb51923fed4548ffb45523fed1448eff56113bfd4844ff754d13fdd4344ffb4911 + ((0x134fdd634d3f754d34fbd644d3ff55934ffd154d3f79a134fdd684d3f796134fdd584d3f34a134fde184d3f746134fde084d3f742134f9d644d3f755934fdd064d3f745534fdd054d3eb59124fed56493fb4d924fed06493fb4d524fed15493fb41524bfe58452ff56114bfe38452ff82114ff551453ef55114ffd35453ff415 + ((0xdb00e40003bf55946efd5641bbf51906bfd68517df59545ffd36517ff41945bfd684d7df59535ffd464d6ff92115bfe38456ff82115f7d45456ff9a105bfd68416ff92105ffd48416ff86105ffd18417df59505f7d45417ff51905fdd56cd3f745734bfe684d2ff5a134ffe584d2ff96134bfd584d3fb4a134ffe184d2ff86 + ((0xd2e9b5b44b2c95fc2b3e5508a77148ca84d4f149b4130fa55349328f7d1a922aa443a861d08f20373e8e7b30f1f9da93a2671f4dd89aee3468657cc4e17e22e625a6cae3150c28fe4fec9a5129923e24500867101d1f0e3c9c75f0e041aa632645f40b49156627c049688730f601c6833905c10a4411c41e9034e05b808d00c6 + ((0xc32170903816050065d48b9897102dc35af0b41364aec3457d2adc5587eab2d4b4a82b4db695e51f9a26d42167e14f2c9d1b36be68ccc8397812bf6514495c910f1f36377c6358ac1120a1ed42bd8341039a011bf577d04f7f9ea23c6f777cebc9d4039e17260e1fdbde372f6cd8d6c9a80b44766f6cae18ff31446114bf6579 + ((0xa1f0c8642e1109038160503804022361508c4409c3a1b0b848180c0581c01c36100270f8642e120603016070060d84499094250e86c2a17088481c08058140e010090d8401247c250f8643217088481c08058140e010090d844204b04a138743a190b844240e0402c0a0700804c6c341061f0c854240e0581c01636104251187 + (0x9440230f07c34190a05c24120702c0c0500a8be1287c321b0a85c22120702016050380402022100481b0943e190d8542e1109038160503804024361788a138743a1b0a85c221206038100b0281c02013110802509c3a1d0d8542e11090381605038040223617882138743e190c85c221206038100b0281c02013110802509c3 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0x190b840240e058100e000098d846229044a1a09c3a180d85c240c0602c0e0111b4884112868270f864281709030180b0380404822100481b09c3a1d0c06c2a17088401c08058140e0100a888422009036138743e190c8502e1108038100b0281c020151b0d244200ec4a1b8783e1a0c8502a120702c0c070100506d221044a1b + ((0x58140c01386c270e874321708848180e0402c0a07008040690dc3e190a8481c0b03802a1b094461f0c85c240e05814016361788a1b09c381d0d8502e10090301c08058100e0000a090442009436138703a1b0a05c20120702c080700004c6c2f10436138703e180c85c201206038100b0201c0001411084401286c270e07c30 + ((0x3617098301606000039321746c28150943a1b0a85c221306838100b028180261747a36140a84a1f0c8642e11098341c08058140c0134b636140a84e1d0e8642e11098341c08058140c012502491b0a054270e87436150b844220e0402c0a060098dc3b8d8561f0c854260e05818018a149236140a84e1d0f8643217088441c08 + ((0xd8502c1207820160403800028220e850250d84e1c0f86032160903c100b0201c000130e8522410868270e8603614090301e0b0380406c200e8702912868270f07c34190a050240c0782816060380802e1d8a44a1b09440230f07c34190a058240f0502c0c0500a0782e0ec682a1208c3e190b84c1c0b03003c2e11468281287c + ((0x1c8d84a1d0d8542c10098341e09058140c0160bc542a8f870391b0943e190c85820130683c120b0281802a968a8561c0ec6c270e87432160804c1a0f0482c0a0600a0e5401b8a855250e07236138743a1b0a858201107824160503005d43150aa4a1c0e46c270e87c32190b040220f0482c0a0600a8803a14090421b09c381d0 + ((0x8064703112081241246c260e874301a0a058221106038100b030140e020080683615c6c270f8642c130782c0c000068782e15076361208c3e190b04c1e0b03003c30170ac391a0943e1b0a04c1e0905818000100d854210ec68270e86c2813078241606000040661c0ac3b1a09c3e190a04c1e0905818000100da642f150ac38 + ((0x1a0b844220c0702c0a07008050861708a34128703e1a0a05c260c0581c01e401b0a846221063413874301a0a05c260c0581c024430b83d1b094381f0c05c260e0402c0e00f200d84416c6c270e860301709838100b038040698dc3e180a840260e0581c016314c8642e8d84a1c0e86034140b044260e06838100b030140e0200 + (0xd862231005a138743a180d05c22130683816050380402a401b08c2c12c6c270e07434170804c180e058100e0000a10c803d18a5d1d8d054241187c341709838160500004c6c31100491b09c3a1f0c868281708844180e0402c0a07008058441207236138703e180d05c201106038100b0201c000141b084401246c270e87c32 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 2 => (0x8341c08058140e0100a100620e46c250f86034140b840260c0702016040380002843188441e8d84a1c0f86434170884c1a0e058140e0100a10c220f46c250f86034170804c180e058100e0000910c6c31104270e874301a0a05c221306838100b0281c02015218d8621207636138703a1a0a05c201306038100b0201c0001620 + ((0xd05c201206034100b0201c000131c09042200903713874301a0a05c200f0581c02238110842d1286e270e8603017090301e0b03804642210ec48249008435130743a180d0502a10090301c09058180a07010040363811888431209435130743a180d0502c11090301a08058180a07010040344018a36128703e190d0502e1109 + ((0x70a410075248dc4c20118743a1a0a05c22110782416050300586caa518831a89840230e87434140b844260d0682c0a0600a888421d86e270e07434140b840240c0782016040380002838108803a1286e270e0743417080481e08058100e0000a0e03a1c86a270e07c301a0a840240c078201604038000283810c35138703e180 + ((0xee370e87434140b04c1a0d058140e0100a8dc2e0f46e241087c30170983c160600003c6e1d4c85d1b89840210e86828170884c1a0f0482c0a0600a875301746a26100843e190d0502a130683c120b028180281748a3513080421f0c86828170884c1a0d058140c0131b875218d44c20118743a1a0a054260d078241605030050 + ((0xb8743e190d0582013068341605038040263c1b8d066200e8731a09c3a1f0c8682c130683416050380402c3707a350f8602c100983c16070060dc3a9946a1d0d0502c130683c120b0281c02011228dc681d48a350f86434140b04c1a0d058140e010098e148200ea491b8743a1a0a058220f0482c0a0700804c8e361a2a946200 + ((0xa070080548a3e1e0d86420c6e1d0e86828160804c1a0f0482c0a070080586e361a0cc5c200e870218dc3a1d0d058260d0782416050380402e33170712e8ec6e1f0d058260f0581401c3c1b0c8409246e1d0f8643416080441e09058140e0100a0d8682e510803a1c0a2491b8743e190d058220f0482c0a0700805c6832170831 + ((0x6128703e180b040260f0581c02437198ca3a1d0e264321746c250e074301a0a0582013070341e0a0482c0c05038080201f1c8c9482410074389209236138783a1d0c068281608044180f0502416060281c040100f91c6e33192350f86434140b040260d078241605038040283e1b8d05c1d0e0611a87c321a0b04c1a0f0482c0 + (0x3b1b090461f0d058260f05814000141b0c8411d0e8491b09c3a1f0c868281608044180f0482c0a07008060441207236138703e180d05820110603c100b0201c000141f0dc3a1c0c05d1a094381f0c8682814098341e09058140e0100b8dc6c33110743810c68270e874301a0a050260d078241605038040303e1b8ce3a1707a3 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 3 => (0xe180d0502c10098301e08058100e0000a8f86e1d0e0601e8d84a1f0c0682c130603c100b0201c000151f0d864208e876138743a180d0502c10098341e09058140e0100b8f86c320903b1b09c381d0d0502c10098301e08058100e0000b0dc6c330e8702c1208636138703a1a0b04c180f0402c080700005c8235198c838970aa + ((0x8743c1b0a85c22110603816050380402a2a118651b094381c0d85c260e0702016070080d854231005b1b09c38190a05c260e0402c0e0111508d1e0f46c250e07830190a058221206838100b030140e020080611b0943a1a0a05820130683c120b0281c0201046c270e87434140b040220f0482c0a070080406e33190391b0943 + ((0xc0782c0e01111a3612878301b0a05c201306038100b0201c000121508c321146c250f06c28170804c180e058100e000098d8542309636138703c190a05c201306038100b0201c00015200d854231105a138743c190a05c22130683816050380402a2009236138703c1b0a05c201106038100b0201c000131b09046220923613 + ((0xc250e07036160804c1c0f0581c020370ec40208f07a36128703c180c8502c10090341c09058180a070100403439120803b0dc4e1c0f064281708048180f0402c0807000054701d0e435138703c1b0a05420120603c100b0201c000141c0921a89c381e0d8502e10090301a08058100e000098e048200b44a1b89c38190a05c24 + ((0x70a43a190b03d1b8943c1a0b840260c07820160403800028370c8591b894381c0d0502e130703c160700807530188b0591a894381e0c0682815080481a0e0482c0c0503808020198b059221146a250e078301a0a058221206834100b030140e02008060561d0e064301046c250f06c2816098301e08058100e0000a8dc321046 + (0x641e0dc481d0c06828170983c1607007064220d8481d0c06c2e130702016070070441e0d8481f0c8502e1307020160700 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g255H10 (_ : Nat) : Nat := (0x3e0390c18e97c0f9d2087a5971770c9d04041cc00028bf44545a5c00020d055b0f7593dcc001024dbf4ae6180021b29a58c49e6d53a0e900002d781495c48649a1e075b850b56fdf30edc6c851c1dd3e9fac8fd27117cf318394c00241a1a90a99d1e2068602a1a40e5849d0240a9e003408084c1aa0a12a4416880c0cca0 + ((0x1ac0019ec0000038870330e25b70550744354d546800149000800245c18794000008099f1138e893843cdd80006159451e80024b19ded6695c000001098003c4c000003128001810000003028557cba87e1f411c1359634fc16882e4204e45d68ce610d33d2e001ca79e1dfe09ccb703b1704890708dc84b89506380e20800 + (0x18a0804002d1998a99a9cb8d8c140 <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255D11 (_ : Nat) : Nat := (0x987868584830281002c34261e1a16100c0a0600a362220120d09870786068505840403028101800050261e1a16100c0a060099628d48467b87226945f656050a4744263c83322ac2461a814a0f404e000ffaadff51bfe9b7fd06ffa8bff4d7fe8affd05fbe69ff4d3ee9a7ed24ffa29ff413f691ffd13fda05fd807fe80ff501 + ((0xc0a0406000128d09878605048382818028dc7634261c1e181814120c0e080a0406000128d8786050483828180263624221e1816120e0a0400b21120d8987078606058404038202810180004a34261c1e18181610120c0c0a040600010150e8d09878685048382810030d8504834261c1e181a1414100e080a0406000138d0a0 + ((0x20281018000443c36241e18181610120c0e080a040600011180d090786068505048303820281018000444434241e181a141610120c0c0a04060001136168d898707060584048303820281018000484234261c1c1a1414120c0e080a0406000112420120d8987070685058404038202810180004ca88e34261c1c1a141610120c + (0x190d8907068505840483038 <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255H11 (_ : Nat) : Nat := 0x51e443e87c6752b8c20096d4000e4000015852d079e9345b5b080053e0808b
set_option maxRecDepth 100000 in
def g255D12 (_ : Nat) : Nat := 0x344870c142030404014ff
def g255L : Nat → Packing
  | 5 => (1,7,7,0,0,1,0,g255D5)
  | 6 => (14,6,7,0,0,7,0,g255D6)
  | 7 => (134,5,7,0,0,12,0,g255D7)
  | 8 => (295,4,7,0,0,15,0,g255D8)
  | 9 => (266,3,7,0,0,16,0,g255D9)
  | 10 => (135,2,7,0,0,15,0,g255D10)
  | 11 => (20,1,7,0,0,12,0,g255D11)
  | 12 => (1,0,7,0,0,1,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 2 2 1 5 1 0 g255H5 h
  | 7, h => lookupWord 5 17 3 8 4 0 g255H6 h
  | 8, h => lookupWord 46 160 7 12 8 0 g255H7 h
  | 9, h => lookupWord 102 352 7 13 9 0 g255H8 h
  | 10, h => lookupWord 90 315 7 13 9 0 g255H9 h
  | 11, h => lookupWord 46 161 5 12 8 0 g255H10 h
  | 12, h => lookupWord 8 25 3 9 5 0 g255H11 h
  | _, _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,[[]],g255L,g255I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P5_0 : block g255 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B5 : block g255 5 0 1 = true := g255P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B6 : block g255 6 0 14 = true := g255P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_16 : block g255 7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_32 : block g255 7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_48 : block g255 7 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_64 : block g255 7 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_80 : block g255 7 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_96 : block g255 7 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_112 : block g255 7 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P7_128 : block g255 7 128 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B7 : block g255 7 0 134 = true := (@block_merge g255 7 0 128 6 (@block_merge g255 7 0 64 64 (@block_merge g255 7 0 32 32 (@block_merge g255 7 0 16 16 g255P7_0 g255P7_16) (@block_merge g255 7 32 16 16 g255P7_32 g255P7_48)) (@block_merge g255 7 64 32 32 (@block_merge g255 7 64 16 16 g255P7_64 g255P7_80) (@block_merge g255 7 96 16 16 g255P7_96 g255P7_112))) g255P7_128)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_16 : block g255 8 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_32 : block g255 8 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_48 : block g255 8 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_64 : block g255 8 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_80 : block g255 8 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_96 : block g255 8 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_112 : block g255 8 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_128 : block g255 8 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_144 : block g255 8 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_160 : block g255 8 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_176 : block g255 8 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_192 : block g255 8 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_208 : block g255 8 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_224 : block g255 8 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_240 : block g255 8 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_256 : block g255 8 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_272 : block g255 8 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_288 : block g255 8 288 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B8 : block g255 8 0 295 = true := (@block_merge g255 8 0 256 39 (@block_merge g255 8 0 128 128 (@block_merge g255 8 0 64 64 (@block_merge g255 8 0 32 32 (@block_merge g255 8 0 16 16 g255P8_0 g255P8_16) (@block_merge g255 8 32 16 16 g255P8_32 g255P8_48)) (@block_merge g255 8 64 32 32 (@block_merge g255 8 64 16 16 g255P8_64 g255P8_80) (@block_merge g255 8 96 16 16 g255P8_96 g255P8_112))) (@block_merge g255 8 128 64 64 (@block_merge g255 8 128 32 32 (@block_merge g255 8 128 16 16 g255P8_128 g255P8_144) (@block_merge g255 8 160 16 16 g255P8_160 g255P8_176)) (@block_merge g255 8 192 32 32 (@block_merge g255 8 192 16 16 g255P8_192 g255P8_208) (@block_merge g255 8 224 16 16 g255P8_224 g255P8_240)))) (@block_merge g255 8 256 32 7 (@block_merge g255 8 256 16 16 g255P8_256 g255P8_272) g255P8_288))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_16 : block g255 9 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_32 : block g255 9 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_48 : block g255 9 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_64 : block g255 9 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_80 : block g255 9 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_96 : block g255 9 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_112 : block g255 9 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_128 : block g255 9 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_144 : block g255 9 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_160 : block g255 9 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_176 : block g255 9 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_192 : block g255 9 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_208 : block g255 9 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_224 : block g255 9 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_240 : block g255 9 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_256 : block g255 9 256 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B9 : block g255 9 0 266 = true := (@block_merge g255 9 0 256 10 (@block_merge g255 9 0 128 128 (@block_merge g255 9 0 64 64 (@block_merge g255 9 0 32 32 (@block_merge g255 9 0 16 16 g255P9_0 g255P9_16) (@block_merge g255 9 32 16 16 g255P9_32 g255P9_48)) (@block_merge g255 9 64 32 32 (@block_merge g255 9 64 16 16 g255P9_64 g255P9_80) (@block_merge g255 9 96 16 16 g255P9_96 g255P9_112))) (@block_merge g255 9 128 64 64 (@block_merge g255 9 128 32 32 (@block_merge g255 9 128 16 16 g255P9_128 g255P9_144) (@block_merge g255 9 160 16 16 g255P9_160 g255P9_176)) (@block_merge g255 9 192 32 32 (@block_merge g255 9 192 16 16 g255P9_192 g255P9_208) (@block_merge g255 9 224 16 16 g255P9_224 g255P9_240)))) g255P9_256)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_16 : block g255 10 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_32 : block g255 10 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_48 : block g255 10 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_64 : block g255 10 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_80 : block g255 10 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_96 : block g255 10 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_112 : block g255 10 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_128 : block g255 10 128 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B10 : block g255 10 0 135 = true := (@block_merge g255 10 0 128 7 (@block_merge g255 10 0 64 64 (@block_merge g255 10 0 32 32 (@block_merge g255 10 0 16 16 g255P10_0 g255P10_16) (@block_merge g255 10 32 16 16 g255P10_32 g255P10_48)) (@block_merge g255 10 64 32 32 (@block_merge g255 10 64 16 16 g255P10_64 g255P10_80) (@block_merge g255 10 96 16 16 g255P10_96 g255P10_112))) g255P10_128)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P11_16 : block g255 11 16 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B11 : block g255 11 0 20 = true := (@block_merge g255 11 0 16 4 g255P11_0 g255P11_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B12 : block g255 12 0 1 = true := g255P12_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g255B5
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 13 := lower_forest (g:=g255) (i:=0) (hints:=1603) (before_sound K123 V123) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffefffffffefffffffefffffffefffffffefffffffaffffeeeeeeeeaa00fffffffefffffffefffffffefffffffefffffffefffffffaffffeeeeeeeeaa00
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [14, 8]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [20, 18]⟩], 21⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

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

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r postedGraph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([8, 16, 64, 1, 1, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([8, 16, 64, 1, 1, 1, 1, 1] : List Nat).getD i.val 0) ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) postedGraph ≠ bit (highRow i) postedGraph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true postedGraph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = postedGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 postedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) postedGraphProper
    (out.resolve_right (fun h => h postedGraphProper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true postedGraph 12 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by rw [witnessSize]; omega),witnessCorrect⟩
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

def coreMoves : List Move := ([].map swapRows) ++ fixRows 0 0
def removed : List (Sig × Row × Row) := []

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem restricted : Lower true eightInputs postedGraph 13 := by
  have h := lift_ok (u:=true) (ms:=coreMoves) (T:=postedGraph) (raw:=eightInputs)
    (base:=varsX 255) (G:=graphGoal 255) (xs:=removed)
    (by decide +kernel) postedGraphProper (proper_of _ (by decide +kernel)) low255
  exact h

theorem excluded : Impossible true postedGraph 12 eightInputs.toFinset := by
  intro k small run
  have steps := list_run run eightInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper postedGraphProper)
    steps (eightInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_31221

theorem PEqualNP.Outside.L_meta_31221 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_31221.replaceShort PEqualNP.Outside.L_meta_31221.excluded gates o fit correct
