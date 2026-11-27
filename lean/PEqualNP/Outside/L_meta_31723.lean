import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31723_aux


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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

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

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input


def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)


def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2




def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower209 : Claim 209 5 :=
  fromLift 5 64 4 lower145 (by decide +kernel)

def cuts148 : Cuts (goalAt 148) := []

def state148_0 : List Sig := roots 148
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude148_0 : Impossible true (goalAt 148) 3 state148_0.toFinset :=
  node_ok cuts148 [] 0x240401404240408404242009080240409080242008404050101404210101410050409010212008480210108480212009010050401410050108480212009080050409080050101410050409080212008480 (by decide +kernel)

theorem lower148 : Claim 148 4 :=
  fromSearch 537003008 (by decide +kernel) exclude148_0

def cuts197 : Cuts (goalAt 197) := []

def state197_0 : List Sig := roots 197
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude197_0 : Impossible true (goalAt 197) 3 state197_0.toFinset :=
  node_ok cuts197 [] 0x31110850521110844431110c4c031300810521200c4c03130084c011510c1c030700454420600c1c03070081c030700c4c011510c1c0 (by decide +kernel)

theorem lower197 : Claim 197 4 :=
  fromSearch 1798 (by decide +kernel) exclude197_0

theorem lower149 : Claim 149 5 :=
  fromLift 5 1 1028 lower148 (by decide +kernel)

def cuts85 : Cuts (goalAt 85) := []

def state85_0 : List Sig := roots 85
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude85_0 : Impossible true (goalAt 85) 3 state85_0.toFinset :=
  node_ok cuts85 [] 0x54145444151101444050405450151401450151105450151401105044405150145401150115105150145404544145405450115105150 (by decide +kernel)

theorem lower85 : Claim 85 4 :=
  fromSearch 1028 (by decide +kernel) exclude85_0

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower148 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower149 none (by decide +kernel)

def rule213_4 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower85 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3,rule213_4]

def state213_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 4 state213_0.toFinset :=
  node_ok cuts213 [] 0x31300d0c015140c4c015140c4c031300545011414c4c031300410530700c4c011510c1c030700d0c014540c1c014540c1c030700515011414c1c030701000124140d0c0343005444054148505 (by decide +kernel)

def state213_1 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_1 : Impossible true (goalAt 213) 4 state213_1.toFinset :=
  node_ok cuts213 [] 0xc4c034300545031300545031300c4c015140c1c031300454430700c1c034300515030700515030700c1c014540544434300d0c0151105450313005450313005150307005150307005444343005444343009050 (by decide +kernel)

def state213_2 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_2 : Impossible true (goalAt 213) 5 state213_2.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_1,exclude213_1⟩] 0xc44415140545024140c4c031300c44431300c4c024140545015140544431300c4c034300545034300544415140545034300c4c031300450521200848010404c4c031300450531300c4c010404848021300850514540515024140c1c030700850530700c1c024140515014541000130700c1c031300454431301000111510454431300c1c030701000230700c1c034300515034301000114540515034300c1c030700450520600818040004c1c030700450530700c1c040004818020700905015110905031110d0c034300905034300d0c03111054441511100034000c9080241404505241408505800048505241420000241408505114148444 (by decide +kernel)

def state213_3 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_3 : Impossible true (goalAt 213) 4 state213_3.toFinset :=
  node_ok cuts213 [] 0x545031300c4c015140c4c015140545031300c1c031300454430700515030700c1c014540c1c014540515030700905021110905021110c4c015140c4c015140c1c014540c1c014540844424140844424140d0c0 (by decide +kernel)

def state213_4 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_4 : Impossible true (goalAt 213) 5 state213_4.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_3,exclude213_3⟩] 0x905015110905021110d0c034300905034300d0c021110544415112000105414150511414d0c034302000034300d0c011414150505110544431300c4c034300545034300544415140545034300c4c031300844415140545024140c4c031300844431300c4c024140545015140450505040141010404c4c031300450531300c4c010404141005140150530700c1c034300515034300150514540515034300c1c030701000130700c1c031300454431301000111510454431300c1c030701000114540515024140c1c030701000130700c1c024140515014540450504440111040004c1c030700450530700c1c04000411100454100034000c9010 (by decide +kernel)

def state213_5 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,input 0,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_5 : Impossible true (goalAt 213) 4 state213_5.toFinset :=
  node_ok cuts213 [] 0x34140901024140905020600c1c03070081c014540c1c030700515030700d0c014540c1c024200d0c03430090c034140d0c034300544421300c4c031300848030700454430700c4c015140c4c031300545031300545034300c4c0 (by decide +kernel)

def state213_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_6 : Impossible true (goalAt 213) 5 state213_6.toFinset :=
  node_ok cuts213 [⟨state213_0,exclude213_0⟩,⟨state213_5,exclude213_5⟩] 0xd0502404090502414045054000e000011414848031300c4c021300545031300c4c015140c4c034300545031302000131300c4c040000818030700c1c020700c1c031300454430700515030700c1c014540c1c034300515030700454430700c1c011510c44424200d0c03430090c034140d0c0400085444 (by decide +kernel)

def state213_7 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_7 : Impossible true (goalAt 213) 6 state213_7.toFinset :=
  node_ok cuts213 [⟨state213_2,exclude213_2⟩,⟨state213_4,exclude213_4⟩,⟨state213_6,exclude213_6⟩] 0x4000cd05011414d0504000c90104000c90104000cd0508000490504000c901011414905040010d05015110d05040008c44434300d0c080008d05034300d0c040008c4441511054444000d00032420090804000c450534300d0c04000e000034300d0c04000c45052420090c040000c44415140545040000d05031300c4c040000c44431300c4c040000d05015140545040000450521200848040000410131300c4c040000450531300c4c04000041012120084c040000544431300c4c040000d0c015140d0c040000544415140545040000d0c031300c4c040004850514540515040004d05030700c1c040004850530700c1c040004d0501454051504000c45052060081804000d000130700c1c04000c450530700c1c04000d00032060081c040008150530700c1c040004d0c014540d0c040004150514540515040008d0c030700c1c040001000030700c1c040000c4c011510c4c040001000111510454440000c4c030700c1c0 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 1028 (by decide +kernel) exclude213_7

def cuts210 : Cuts (goalAt 210) := []

def state210_0 : List Sig := roots 210
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude210_0 : Impossible true (goalAt 210) 3 state210_0.toFinset :=
  node_ok cuts210 [] 0x34140c28230a08905034140d0c034300128224a08d0c03430090c014940c2c030b00525030a08c2c030b00125030b00d0c024208c2c0 (by decide +kernel)

theorem lower210 : Claim 210 4 :=
  fromSearch 1090584640 (by decide +kernel) exclude210_0

theorem lower150 : Claim 150 5 :=
  fromLift 5 2 536937536 lower148 (by decide +kernel)

def cuts86 : Cuts (goalAt 86) := []

def state86_0 : List Sig := roots 86
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude86_0 : Impossible true (goalAt 86) 3 state86_0.toFinset :=
  node_ok cuts86 [] 0x58185444151101444050405450151401450151105450151401206048405250149401250119105250149404644149405450119105250 (by decide +kernel)

theorem lower86 : Claim 86 4 :=
  fromSearch 16843840 (by decide +kernel) exclude86_0

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower148 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower150 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower86 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3]

def state214_0 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 4 state214_0.toFinset :=
  node_ok cuts214 [] 0x15140c4c031300545031300d0c015140c4c021208c4c031300848224140d0c034300544424a08905030a08c28210a00525030b00c2c014940c2c021208c4c030b00c2c014940d0c030b010001 (by decide +kernel)

def state214_1 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_1 : Impossible true (goalAt 214) 5 state214_1.toFinset :=
  node_ok cuts214 [⟨state214_0,exclude214_0⟩] 0xc44415140545024140c4c031300c44431300c4c024140545015140544431300c4c034300545034300544415140545034300c4c031300460621a08868230a08c4c031300460631300c4c030a08868221300860614940525024140c2c030b00860630b00c2c024140525014940868230b00c2c031300464431300868211910848231300c2c030b01000130b00c2c034300525034301000114940525034300c2c030b00c28280000c28240004c2c030b00c28230b00c2c040005000140004905015110905031110d0c034300905034300d0c031110544415111000240008928224140460624140860630a08c28224140c28230a088606118188444 (by decide +kernel)

def state214_2 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_2 : Impossible true (goalAt 214) 4 state214_2.toFinset :=
  node_ok cuts214 [] 0x30a08c2c030b00125030b00d0c024208c2c030b00c4c021208c2c024a08d0c03430090c021a08c4c03130084c031300d0c015140c4c024140c28234140c28214940c2c014940c2c015110d0c034140d0c015140c4c015140c4c0 (by decide +kernel)

def state214_3 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_3 : Impossible true (goalAt 214) 5 state214_3.toFinset :=
  node_ok cuts214 [⟨state214_2,exclude214_2⟩] 0xd05030a08c28224140525030b00c2c014940c28230b00c2c004940c2c014940525030b00c2c015140464430b00c2c014940525030b00d05031110d05015110160630a08544430a08d0c015140d05031110545005040c28215140c28215110545004818c4c034142000034141000311818c28211818c282 (by decide +kernel)

def state214_4 : List Sig := [0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 2,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_4 : Impossible true (goalAt 214) 4 state214_4.toFinset :=
  node_ok cuts214 [] 0x14940c2c030b00525030b00d0c014940c2c030b00c4c021208c2c030a08c2c030b01000124140d0c034300544424a08d0c034300c28215140c4c031300545031300d0c015140c4c021a08c4c03130084c024140c28230a088444 (by decide +kernel)

def state214_5 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_5 : Impossible true (goalAt 214) 5 state214_5.toFinset :=
  node_ok cuts214 [⟨state214_4,exclude214_4⟩] 0xd05030a08c28224140525030b00c2c014940c28230b00c2c004940c2c014940525030b00c2c031300848230b00d05031110d05015110160630a08544430a08c44431300c4c034140868231300c4c021300d4c015110c4c034140c44434140c44440008c28280000c28214940c2c014940c2c0343005450 (by decide +kernel)

def state214_6 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_6 : Impossible true (goalAt 214) 5 state214_6.toFinset :=
  node_ok cuts214 [] 0xc44430a08c28221110420230a08c28210808928234300d0c024300544434300d0c015110120234300d0c004808c28230b00c2c004940c2c034300908230b00525030b00c2c014940c2c031300848230b00525030b00c2c014940d05021a08c4c03130084c031300d0c015110c4c031110c4c0400005450 (by decide +kernel)

def state214_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_7 : Impossible true (goalAt 214) 4 state214_7.toFinset :=
  node_ok cuts214 [] 0x34140c28230a08905030a08c2c030b00125014940c2c030b00525030b00d0c024208c2c024a08d0c03430090c034140d0c034300544421300c4c031300868230b00848230b00c4c015140c4c031300545031300545034300c4c0 (by decide +kernel)

def state214_8 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_8 : Impossible true (goalAt 214) 5 state214_8.toFinset :=
  node_ok cuts214 [⟨state214_7,exclude214_7⟩] 0xd05030a08c28224140460630a08c28211818868231300c4c021300545031300c4c015140c4c034300545031302000031300c4c040000c28230b00c2c004940c2c031300848230b00525030b00c2c014940c2c034300908230b00464430b00c2c011910c44424a08d0c03430090c034140d0c004a085444 (by decide +kernel)

def state214_9 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_9 : Impossible true (goalAt 214) 4 state214_9.toFinset :=
  node_ok cuts214 [] 0x15140c4c031300545031300d0c015140c4c021a08c4c03130084c030b00c4c021208c2c014940c2c030b00525030b00d0c024208c2c030a08c2c030b01000134140d0c034300544424a08d0c03430090c034140c28230a089050 (by decide +kernel)

def state214_10 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_10 : Impossible true (goalAt 214) 5 state214_10.toFinset :=
  node_ok cuts214 [⟨state214_9,exclude214_9⟩] 0xc44430a08c28221110868231300c4c021300545031300c4c015140c4c034300545031300c28230b00c2c004940c2c031300848230b00525030b00c2c014940c2c034300908230b00928234300d0c024300d44434300c44440008c28280000c28215140c4c015140c4c014940c2c014940c2c0341405444 (by decide +kernel)

def state214_11 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_11 : Impossible true (goalAt 214) 6 state214_11.toFinset :=
  node_ok cuts214 [⟨state214_1,exclude214_1⟩,⟨state214_3,exclude214_3⟩,⟨state214_5,exclude214_5⟩,⟨state214_6,exclude214_6⟩,⟨state214_8,exclude214_8⟩,⟨state214_10,exclude214_10⟩] 0x40008d05011818d05040008901030a08c28240008d05030a08c2824000890101181890504000cd05015110d05080014c44434300d0c080010d05034300d0c04000cc44415110544440009000224a08928240008c28234300d0c04000a000034300d0c040008c28224a0890c04000cc44415140545040000d05031300c4c08000cc44431300c4c040000d05015140545040008460621a08868240008c28231300c4c040008460631300c4c040008c28221a0884c080008544431300c4c040000d0c015140d0c080004544415140545040000d0c031300c4c040004860614940525040004d05030b00c2c040004860630b00c2c040004d05014940525040008c28204840c28240009000130b00c2c040008c28230b00c2c040009000204840125040004928230b00c2c040004d0c014940d0c040004928214940908240004d0c030b00c2c040000868230b00c2c040004c4c011910c4c040004868211910848240000c4c030b00c2c0 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 553714752 (by decide +kernel) exclude214_11

theorem lower211 : Claim 211 6 :=
  fromLift 6 2 68 lower209 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

theorem lower151 : Claim 151 6 :=
  fromLift 6 1 1092 lower150 (by decide +kernel)

theorem lower199 : Claim 199 5 :=
  fromLift 5 2 1894 lower197 (by decide +kernel)

def cuts195 : Cuts (goalAt 195) := []

def state195_0 : List Sig := roots 195
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude195_0 : Impossible true (goalAt 195) 3 state195_0.toFinset :=
  node_ok cuts195 [] 0x10c0cc28230a08428210900c2c030b0042c030a08c2c030b00410310500c1c03070041c020e08c1c030700838230700c2c020e08c1c0 (by decide +kernel)

theorem lower195 : Claim 195 4 :=
  fromSearch 102 (by decide +kernel) exclude195_0

theorem lower87 : Claim 87 5 :=
  fromLift 5 1 1092 lower86 (by decide +kernel)

def rule215_0 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 none (by decide +kernel)

def rule215_1 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 none (by decide +kernel)

def rule215_2 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 none (by decide +kernel)

def rule215_3 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower147 none (by decide +kernel)

def rule215_4 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 none (by decide +kernel)

def rule215_5 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower199 none (by decide +kernel)

def rule215_6 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower150 none (by decide +kernel)

def rule215_7 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 4,input 6)) (by decide +kernel)

def rule215_8 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower148 none (by decide +kernel)

def rule215_9 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (1,input 4,input 6)) (by decide +kernel)

def rule215_10 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower149 none (by decide +kernel)

def rule215_11 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower197 none (by decide +kernel)

def rule215_12 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower145 none (by decide +kernel)

def rule215_13 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower195 none (by decide +kernel)

def rule215_14 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower87 none (by decide +kernel)

def rule215_15 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 2,input 4)) (by decide +kernel)

def rule215_16 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower209 none (by decide +kernel)

def rule215_17 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (3,input 2,input 4)) (by decide +kernel)

def rule215_18 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 2,input 7)) (by decide +kernel)

def rule215_19 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower86 none (by decide +kernel)

def rule215_20 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower85 none (by decide +kernel)

def rule215_21 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (1,input 4,input 7)) (by decide +kernel)

def rule215_22 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 (some (1,input 4,input 7)) (by decide +kernel)

def rule215_23 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 (some (2,input 4,input 7)) (by decide +kernel)

def cuts215 : Cuts (goalAt 215) := [rule215_0,rule215_1,rule215_2,rule215_3,rule215_4,rule215_5,rule215_6,rule215_7,rule215_8,rule215_9,rule215_10,rule215_11,rule215_12,rule215_13,rule215_14,rule215_15,rule215_16,rule215_17,rule215_18,rule215_19,rule215_20,rule215_21,rule215_22,rule215_23]

def state215_0 : List Sig := [0xbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaabbbbbbbbbbbbbbbbbbbbaaaabbbbaaaa,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_0 : Impossible true (goalAt 215) 5 state215_0.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545031300d0c015140c4c021208c4c031300848224140d0c034300544424a08905030a08c28210a00515030700c1c014540c1c031300454430700c1c034300515030700450730700c1c020f00838214940c2c030b00525030b00848231300c2c030b00525034300c2c01141cc2c030b00c282 (by decide +kernel)

def state215_1 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0x1111111111111111111100001111000011111111111111111111000011110000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_1 : Impossible true (goalAt 215) 4 state215_1.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140848231300c4c021208c4c034300545031300905030a08c28210a00515030b00c2c014540c2c021208c4c030b00140730b00838230700c1c024140d0c034300544420e08d0c0343008382 (by decide +kernel)

def state215_2 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0x1111111111111111111100001111000011111111111111111111000011110000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_2 : Impossible true (goalAt 215) 4 state215_2.toFinset :=
  node_ok cuts215 [] 0x24140d0c034300544424a08905030a08c28210a00525030b00c2c014940c2c014940d0c030b01000830b00838230700c1c015140c4c031300545031300d0c015140c4c020e08c4c0313008382 (by decide +kernel)

def state215_3 : List Sig := [0x1111111111111111111100001111000011111111111111111111000011110000,input 0,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_3 : Impossible true (goalAt 215) 5 state215_3.toFinset :=
  node_ok cuts215 [⟨state215_1,exclude215_1⟩,⟨state215_2,exclude215_2⟩] 0x545031300c4c015140c4c034300545031300848231300c4c021208905034300d0c015110928224140c28230a0842802141c838220e08905020e08c4c080004c4c020e08d0c080000d0c020e08c1821141c838214940c2c030b00525030b00848231300c2c030b00525034300c2c040020c1c0 (by decide +kernel)

def state215_4 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_4 : Impossible true (goalAt 215) 4 state215_4.toFinset :=
  node_ok cuts215 [] 0x905030a08c28210a00525030b00c2c014940110730b00525034300c2c030b00848231300c2c024140d0c034300454424a08d0c034300c28214540c4c031300515021208c4c031300848230700c1c014540c4c0 (by decide +kernel)

def state215_5 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_5 : Impossible true (goalAt 215) 5 state215_5.toFinset :=
  node_ok cuts215 [⟨state215_1,exclude215_1⟩,⟨state215_4,exclude215_4⟩] 0x15140c4c031300545021208c4c031300848231300d0c015140c4c024140c28230a08428014940c2c030b00525030b00848231300c2c00541cc2c080000515030b00c2c014940d0c030b00515024140850714540515031302000131300170730a08515030a08c1c024140d0c034300544424a08d0c034300c282 (by decide +kernel)

def state215_6 : List Sig := [0x5555000055550000555500005555000055550000555500005555000055550000,input 0,0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_6 : Impossible true (goalAt 215) 5 state215_6.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140848231300c4c021208905030a08c28210a00525030b00c2c014940c2c021208c4c030b00150730700838230700c2c030b00525034300c2c011510c1c03070051c030700c4c011510c1c020e08c1c030700838224140d0c034300544434300c4c015140c4c024a085150 (by decide +kernel)

def state215_7 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_7 : Impossible true (goalAt 215) 5 state215_7.toFinset :=
  node_ok cuts215 [⟨state215_4,exclude215_4⟩,⟨state215_2,exclude215_2⟩] 0x905034300d0c015110928224140c28230a08428014940c2c030b00525030b00525034300c2c01041cc2c080004454430b00c2c021208c4c030b00454424140810724140454434302000034300430730a08454430a08c1c015140c4c031300545031300d0c015140c4c021208c4c0313008482 (by decide +kernel)

def state215_8 : List Sig := [0x5050505050505050505050505050505050505050505050505050505050505050,input 0,0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_8 : Impossible true (goalAt 215) 5 state215_8.toFinset :=
  node_ok cuts215 [] 0x905034300d0c015110928224140c28230a08428014940c2c030b00525030b00525034300c2c01041cc1c020e08c1c030b00c2c021208c4c030b00515030700c1c014540c1c034300515030700838230700c1c020e08545031300c4c015140c4c034300545031300848231300c4c0212084544 (by decide +kernel)

def state215_9 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_9 : Impossible true (goalAt 215) 6 state215_9.toFinset :=
  node_ok cuts215 [⟨state215_0,exclude215_0⟩,⟨state215_3,exclude215_3⟩,⟨state215_5,exclude215_5⟩,⟨state215_6,exclude215_6⟩,⟨state215_7,exclude215_7⟩,⟨state215_8,exclude215_8⟩] 0x31110545015140905031300c4c031110c4c031300905015140545015110c4c031300d0c015140d0c015110545015140d0c031300c4c011c1c848221208c28231300c4c011c1cc4c031300c2822120884822141c515014540905030700c1c02141cc1c030700905014540515080014c1c030700c4c011510c4c080010454411510c4c030700c1c08000cc1c030700d0c014540d0c080008515014540d0c030700c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838224140544424140c44434300d0c024140d0c034300c44415110544440029000a24a08905011c1c90502141cc28230a08905030a08c2822141c470710a0090501494052502141cc2c030b00905030b00c2c02141c525014940c4c030b00c2c021208464421208c4c011910c4c021208c2c030b00c1c030b00c1c020e0a000120e08c1c080000c1c020e08c2c030b00d0c030b00c2c040028525014940d0c014940d0c040024c2c030b01000a400284507 (by decide +kernel)

def state215_10 : List Sig := [0xffffffffffffffffffff0000ffff000000000000000000000000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_10 : Impossible true (goalAt 215) 6 state215_10.toFinset :=
  node_ok cuts215 [] 0x31300d0c015140c4c015140c4c031300545021a08c4c031300868221a08c4c031300868230b00c4c021208c2c030b00d0c014940c2c014940c2c030b00525011c1cc2c030b00450714940c2c030b00525030700c4c011510c1c030700c2c020e08c1c030700d0c014540c1c014540c1c030700515020e08c1c030700838220e08c1c030700838215110d0c034300544405c1c544434300d0c015110470721c1c844424140c282 (by decide +kernel)

def state215_11 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_11 : Impossible true (goalAt 215) 5 state215_11.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545021a08c4c03130084c030b00c4c021208c2c014940c2c030b00525030a08c2c030b00150730700c4c011510c1c030700c2c020e08c1c014540c1c030700515020e08c1c030700838224140c28230a08844431300545031300d0c030b00525030b00d0c030700515030700d0c015110d0c034300905030a08d0c0343009282 (by decide +kernel)

def state215_12 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_12 : Impossible true (goalAt 215) 5 state215_12.toFinset :=
  node_ok cuts215 [] 0xc4c034300545031300545031300c4c015140868231300c4c021300c2c031300848230b00c2c034300525030b00525030b00c2c014940c28230b00c2c01141c905034300d0c015110928224140c28230a08844430700454431300c1c030700838230b00c1c030700515034300c1c014540c1c030700515020e08c1c0307008382 (by decide +kernel)

def state215_13 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_13 : Impossible true (goalAt 215) 5 state215_13.toFinset :=
  node_ok cuts215 [] 0xc4c034300545031300545031300c4c015140868231300c4c021300c1c031300454430700c1c034300515030700515030700c1c014540838230700c1c020e08905034300d0c015110928224140c28230a08844430b00848231300c2c030700838230700c2c030b00525034300c2c014940c2c030b0052501141cc2c030b00c282 (by decide +kernel)

def state215_14 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_14 : Impossible true (goalAt 215) 4 state215_14.toFinset :=
  node_ok cuts215 [] 0x31300d0c015140c4c015140c4c03130054501141cc4c031300410724140d0c03430054440541c850730700c4c011510c1c030700d0c014540c1c014540c1c03070051501141cc1c0307010008 (by decide +kernel)

def state215_15 : List Sig := [0xcccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_15 : Impossible true (goalAt 215) 5 state215_15.toFinset :=
  node_ok cuts215 [⟨state215_14,exclude215_14⟩] 0xc4c034300545031300545031300c4c015140450731300c4c01041cc1c031300454430700c1c034300515030700515030700c1c014540450730700c1c040020c1c030b02000030700905034300d0c01511015072141cc2c031300464430b00c2c034300525030b00525030b00c2c0149404707 (by decide +kernel)

def state215_16 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_16 : Impossible true (goalAt 215) 5 state215_16.toFinset :=
  node_ok cuts215 [] 0xc2c034300525030b00525030b00c2c014940c28230b00c2c01141cc1c030b00838230700c1c034300515030700515030700c1c014540838230700c1c020e08905034300d0c015110928224140c28230a08844430b00848230b00c4c030700454430700c4c031300545034300c4c015140c4c031300545021300c4c0313008682 (by decide +kernel)

def state215_17 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_17 : Impossible true (goalAt 215) 6 state215_17.toFinset :=
  node_ok cuts215 [⟨state215_11,exclude215_11⟩,⟨state215_12,exclude215_12⟩,⟨state215_13,exclude215_13⟩,⟨state215_15,exclude215_15⟩,⟨state215_16,exclude215_16⟩] 0xc4c034300545031300545031300c4c015140868231300c4c021302000431300c4c04000cc2c031300848230b00c2c034300525030b00525030b00c2c014940c28230b00c2c08000e000230b00c2c040028c1c031300454430700c1c030b00838230700c1c034300515030700515030700c1c014540838230700c1c020e0a000130700c1c040018905034300d0c015110928280000870724140c282211104707 (by decide +kernel)

def state215_18 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaa,0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_18 : Impossible true (goalAt 215) 4 state215_18.toFinset :=
  node_ok cuts215 [] 0xc4c034300545031300545031300c4c015140544434300d0c015110545031300545031300544434300544434300905014540c1c014540c1c030700c4c011510c1c030700d0c014540c1c014540c1c0307005150 (by decide +kernel)

def state215_19 : List Sig := [0xcccccccccccccccccccc0000cccc0000cccccccccccccccccccc0000cccc0000,0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_19 : Impossible true (goalAt 215) 5 state215_19.toFinset :=
  node_ok cuts215 [⟨state215_18,exclude215_18⟩] 0xc4c034300545031300545031300c4c015140c1c031300454430700c1c034300515030700515030700c1c014540c1c030b02000030700544434300d0c015110545031300545031300515030700515030700544434300544434300905014940c2c014940c2c030b00c4c011910c2c030b00d0c014940c2c014940c2c030b005250 (by decide +kernel)

def state215_20 : List Sig := [0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_20 : Impossible true (goalAt 215) 6 state215_20.toFinset :=
  node_ok cuts215 [⟨state215_19,exclude215_19⟩] 0x31300d0c015140c4c015140c4c031300545021a08c4c03130084c030b00c4c021208c2c030b00d0c014940c2c014940c2c030b00525030a08c2c030b02000030700c4c011510c1c030700c2c020e08c1c030700d0c014540c1c014540c1c030700515020e08c1c030700838215110d0c034300544424a08c70730a08870715140c4c015140c4c014940c2c014940c2c014540c1c014540c1c015110d0c015110d0c0241404707 (by decide +kernel)

def state215_21 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_21 : Impossible true (goalAt 215) 5 state215_21.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545021a08c4c031300868231300d0c021a08c4c030b00c4c021208c2c014940c2c030b00525024a08c2c030b00908230b00d0c014940c2c030700c4c011510c1c030700c2c020e08c1c014540c1c030700515020e08c1c030700838230700d0c020e08c1c024140928224a08528224140d0c034300544424a08d0c034300c282 (by decide +kernel)

def state215_22 : List Sig := [0xccccccccccccccccccccffffccccffffcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_22 : Impossible true (goalAt 215) 5 state215_22.toFinset :=
  node_ok cuts215 [] 0xc4c034300545031300545031300c4c015140848231300c4c021208c1c031300454430700c1c034300515030700515030700c1c014540838230700c1c020e08c1c030b00838230700905034300d0c015110928224140c28230a08428030b00c4c021208c2c030b00d0c014940c2c014940c2c030b00525030a08c2c030b004507 (by decide +kernel)

def state215_23 : List Sig := [0xffff0000ffff00000000000000000000000000000000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 7,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_23 : Impossible true (goalAt 215) 6 state215_23.toFinset :=
  node_ok cuts215 [⟨state215_21,exclude215_21⟩,⟨state215_22,exclude215_22⟩] 0xc4c034300545031300545031300c4c015140868231300c4c021a08c2c031300848230b00c2c034300525030b00525030b00c2c014940470730b00c2c01141cc1c031300454430700c1c030b00838230700c1c034300515030700515030700c1c014540838230700c1c020e08905034300d0c015110170731c1c905011c1c868231300868231301000a30b02000130b00838230700838230702000021c1cc282 (by decide +kernel)

def state215_24 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_24 : Impossible true (goalAt 215) 5 state215_24.toFinset :=
  node_ok cuts215 [] 0xc28230b00c2c01041c525030b00c2c014940c2c034300525030b00c1c030b00838230700838230700c1c020e08515030700c1c014540c1c034300515030700905030a08c28221110928224140d0c034300544430b00848230b00c4c030700454430700c4c021300c4c031300868215140c4c031300545031300545034300c4c0 (by decide +kernel)

def state215_25 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_25 : Impossible true (goalAt 215) 6 state215_25.toFinset :=
  node_ok cuts215 [⟨state215_24,exclude215_24⟩] 0x21a08c4c03130084c015140c4c031300545031300d0c015140c4c080000c4c031301000330b00c4c021208c2c030a08c2c030b00450714940c2c030b00525030b00d0c014940c2c011910c2c030b00464430700c4c011510c1c030700c2c020e08c1c020e08c1c030700838214540c1c030700515030700d0c014540c1c011510c1c030700454424140c28230a08470711c1cc28230a08470731110928224140d0c0400145444 (by decide +kernel)

def state215_26 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_26 : Impossible true (goalAt 215) 6 state215_26.toFinset :=
  node_ok cuts215 [] 0x21a08c4c03130084c015140c4c031300545031300545015140c4c030b00c4c021208c2c030a08c2c030b00450714940c2c030b00525030b00525014940c2c030700c4c011510c1c030700c2c020e08c1c020e08c1c030700838214540c1c030700515030700515014540c1c024140c28230a08470705c1c944424140544431300545031300545030b00525030b00525030700515030700515030a08470730a08470731110d0c0 (by decide +kernel)

def state215_27 : List Sig := [0x3333333333333333333330303333303033333333333333333333303033333030,input 2,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_27 : Impossible true (goalAt 215) 5 state215_27.toFinset :=
  node_ok cuts215 [] 0x515030700c1c014540c1c034300515030700838230700c1c020e08c1c031300454430700905034300d0c015110928224140c28230a08844415140c4c031300545031300d0c015140c4c021a08c4c03130084c014940c2c030b00525030700838230700c2c030b00525034300c2c01141cc2c030b00c28230b00848231300c2c0 (by decide +kernel)

def state215_28 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff0f0,input 2,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_28 : Impossible true (goalAt 215) 6 state215_28.toFinset :=
  node_ok cuts215 [⟨state215_27,exclude215_27⟩] 0x525030b00c2c014940c2c034300525030b00470730b00c2c01141cc2c031300464430b02000030b00c2c040028515030700c1c014540c1c030b00838230700c1c034300515030700838230700c1c020e08c1c031300454430700838230700c1c020e08905034300d0c01511017074000c905021c1c905021110c28215140c4c031300545031300d0c015140c4c011c1cc4c0213008682241408303241408303 (by decide +kernel)

def state215_29 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,input 2,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_29 : Impossible true (goalAt 215) 6 state215_29.toFinset :=
  node_ok cuts215 [] 0x14940c2c030b00525030b00d0c014940c2c011c1cc2c030b00450730b00848021208c2c014540c1c030700515030700c2c020e08c1c030700d0c014540c1c020e08c1c030700838230700868211510c1c024140d0c034300544405c1c905021c1c905021110c44421a08868224140868234300544434300c68211c1c868224140c44424140c44430b00464430b00464430700838230700838234300544434300544430a08c4c0 (by decide +kernel)

def state215_30 : List Sig := [0xffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0,input 2,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_30 : Impossible true (goalAt 215) 5 state215_30.toFinset :=
  node_ok cuts215 [] 0x30a08c2c030b00450714940c2c030b00525030b00c4c021208c2c030700c2c020e08c1c020e08c1c030700838214540c1c030700515030700c4c011510c1c024140c28230a08844421a08c4c03130084c015140c4c031300545030b00525030b00d0c030700515030700d0c030a08d0c034300928215110d0c034300905031300545031300d0c0 (by decide +kernel)

def state215_31 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_31 : Impossible true (goalAt 215) 6 state215_31.toFinset :=
  node_ok cuts215 [⟨state215_30,exclude215_30⟩] 0x30b00d0c014940c2c030a08c2c030b00450714940c2c030b00525030b00c4c021208c2c014940c2c030b00525030700c2c020e08c1c030700d0c014540c1c020e08c1c030700838214540c1c030700515030700c4c011510c1c014540c1c030700515024a08544434300d0c015112000034300d0c040014c44430a08c28221110430330a08c28210c0c905031300d0c015110c4c021a08c4c03130084c031110c4c020c1c5450 (by decide +kernel)

def state215_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_32 : Impossible true (goalAt 215) 6 state215_32.toFinset :=
  node_ok cuts215 [] 0x30b00d0c014940c2c030a08c2c030b00450714940c2c030b00525030b00545011910c2c030700c2c020e08c1c030700d0c014540c1c020e08c1c030700838214540c1c030700515030700545011510c1c024a08544434300d0c015110c44430a08c28221110544434300545034300470730a08545030a08945031110545030b00525030b00525030700515030700515034300544434300544430a08470730a08470724140c4c0 (by decide +kernel)

def state215_33 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_33 : Impossible true (goalAt 215) 7 state215_33.toFinset :=
  node_ok cuts215 [⟨state215_9,exclude215_9⟩,⟨state215_10,exclude215_10⟩,⟨state215_17,exclude215_17⟩,⟨state215_20,exclude215_20⟩,⟨state215_23,exclude215_23⟩,⟨state215_25,exclude215_25⟩,⟨state215_26,exclude215_26⟩,⟨state215_28,exclude215_28⟩,⟨state215_29,exclude215_29⟩,⟨state215_31,exclude215_31⟩,⟨state215_32,exclude215_32⟩] 0x80028c4441514054504000c905031300c4c080024c44431300c4c04000c905015140545040014544431300c4c04000cd0c015140d0c040034544415140545040014d0c031300c4c080020470721a0886824000cc28231300c4c08001c470731300c4c04000cc28221a0884c040024870714940525040028905030b00c2c040024870730b00c2c04002890501494052504000c868230b00c2c040028c4c011910c4c040030868211910848240028c4c030b00c2c040015000930b00c2c040028d0c014940d0c04002d000914940525040014d0c030b00c2c040024c28280000c28240028450530b00c2c040024c28230b00c2c04002845054002445074001c870714540515040018905030700c1c04001c870730700c1c04001890501454051504000d000730700c1c040018c4c011510c4c04001d000711510454440018c4c030700c1c040029000930700c1c040018c2c020e08c2c040021000720e08838240018c2c030700c1c040015000730700c1c040018d0c014540d0c04001d000714540515040014d0c030700c1c04001c470720e08838240018c28230700c1c04001c470730700c1c040018c28220e08838280018905015110905040014c44434300d0c080014905034300d0c040014c44415110544440011000440010928280010905011c1c90508000c870730a08c28280008905030a08c28280004870711c1c8444 (by decide +kernel)

def state215_34 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_34 : Impossible true (goalAt 215) 5 state215_34.toFinset :=
  node_ok cuts215 [] 0x525030b00c2c014940c2c024200908230b00c1c030b00838230700515030700c1c014540c1c024a08515030700c2c030a08c2c014940c1c020e08c1c020e08c44430a08c28224140d0c03130084c031300868224140928224a08528230b00848230b00c4c030700454430700c4c015140c4c031300545031300545024a08c4c0 (by decide +kernel)

def state215_35 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_35 : Impossible true (goalAt 215) 6 state215_35.toFinset :=
  node_ok cuts215 [⟨state215_34,exclude215_34⟩] 0x15140c4c031300545031300928215140c4c080000c4c031301000330b00c4c021208c2c014940c2c030b00525030b00908024208c2c011910c2c030b00464430700c4c011510c1c030700c2c020e08c1c014540c1c030700515030700928214540c1c011510c1c03070045443130086823130084c030b00c28230b00525030700838230700838211c1cc28230a08905034300470730a08c28211c1cc44424140928214a081707 (by decide +kernel)

def state215_36 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_36 : Impossible true (goalAt 215) 6 state215_36.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545031300545015140c4c030b00c4c021208c2c014940c2c030b00525030b00525014940c2c030700c4c011510c1c030700c2c020e08c1c014540c1c030700515030700515014540c1c03130086823130084c030b00c28230b00525030700838230700838211c1cc28230a08905015110470730a08c28211c1c970724140170731300545031300545030b00525030b005250307005150307005150311109282 (by decide +kernel)

def state215_37 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_37 : Impossible true (goalAt 215) 7 state215_37.toFinset :=
  node_ok cuts215 [⟨state215_35,exclude215_35⟩,⟨state215_36,exclude215_36⟩] 0x4000cc4441514054504000c905031300c4c04000cc44431300c4c04000c905015140545040014170731300c4c04000c92821514092824000c170715140545040014928231300c4c040028870714940525040028905030b00c2c040028870730b00c2c040028905014940525040028868230b00c2c040028c4c011910c4c040028868211910848240028c4c030b00c2c040014928230b00c2c040028908014940908040028928214940908240014908030b00c2c040018870714540515040018905030700c1c040018870730700c1c040018905014540515040019000630700c1c040018c4c011510c4c040019000611510454440018c4c030700c1c040019000630700c1c040018c2c020e08c2c040019000620e08838240018c2c030700c1c040014170730700c1c040018928214540928240018170714540515040014928230700c1c080004905005c1c905040014c44424a08928280000905024a08928240014c44405c1c528240010c44411c1cc44440010905030a08c28240010c44430a08c28240010905011c1c905040010c4c030a08c4c040010868211c1c868240010c4c011c1cc4c040010868230a0884c040010c2c011414c2c040010525030a08c28240010c2c030a08c2c040010525011414525040010c1c030a08c1c040010838211c1c838240010c1c011c1cc1c040010838230a08838240011000440024d0c0 (by decide +kernel)

def state215_38 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 7,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_38 : Impossible true (goalAt 215) 5 state215_38.toFinset :=
  node_ok cuts215 [] 0x34140c28230a08905030a08c2c030b00125030b00d0c024208c2c014940c2c030b00525020e08c1c030700838230700c2c020e08c1c030700d0c014540c1c014540c1c030700515024a08d0c03430090c034140d0c034300544421300c4c031300868230b00848230b00c4c030700454430700c4c031300545034300c4c015140c4c0313005450 (by decide +kernel)

def state215_39 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 7,input 2,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_39 : Impossible true (goalAt 215) 6 state215_39.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩] 0xd05030a08c28224140430330a08c28210c0cc28230b00c2c004940c2c034300908230b00c2c031300848230b00525030b00c2c014940424030b00c2c010900838230700c1c020e08c1c030b00838230700c1c034300515030700c1c031300454430700515030700c1c014540414030700c1c010500928234300d0c024300d05034300d0c015110130321a08c4c03130084c031300d0c015140c4c015140c4c0313005450800008303 (by decide +kernel)

def state215_40 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_40 : Impossible true (goalAt 215) 5 state215_40.toFinset :=
  node_ok cuts215 [] 0x15140c28230a08845015110c28230a08844430a08c2c030b00125030b00c4c021208c2c014940c2c030b00525011910c2c030b00464420e08c1c030700838230700c2c020e08c1c030700c4c014540c1c014540c1c030700515011510c1c030700454421a08c4c03130094c015140c4c031300128215110c4c0313008307151105450151401307 (by decide +kernel)

def state215_41 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_41 : Impossible true (goalAt 215) 6 state215_41.toFinset :=
  node_ok cuts215 [⟨state215_40,exclude215_40⟩] 0x31110c28230a08844415140c28230a08145030a08c2c030b00125030b00525014940c2c030b00c4c021208c2c014940c2c030b00525014940c2c030b00525020e08c1c030700838230700c2c020e08c1c030700515014540c1c030700c4c014540c1c014540c1c030700515014540c1c030700515005c1cc28215110c28234300544431112000015110545015110545004c1c868231300c4c021300c44431300c4c020c1c545031300c4c040014d050 (by decide +kernel)

def state215_42 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_42 : Impossible true (goalAt 215) 6 state215_42.toFinset :=
  node_ok cuts215 [⟨state215_40,exclude215_40⟩] 0x34140c28230a08905015110c28230a08144430a08c2c030b00125030b00545011910c2c030b00d0c024208c2c014940c2c030b00525011910c2c030b00464420e08c1c030700838230700c2c020e08c1c030700545011510c1c030700d0c014540c1c014540c1c030700515011510c1c030700454405040c28215140c28231300545031142000015140544415140545004c1c928234300d0c024300d05034300d0c004a08544434300d0c040008c444 (by decide +kernel)

def state215_43 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_43 : Impossible true (goalAt 215) 7 state215_43.toFinset :=
  node_ok cuts215 [⟨state215_39,exclude215_39⟩,⟨state215_41,exclude215_41⟩,⟨state215_42,exclude215_42⟩] 0xd05011c1cd05024040c28230a08d05030a08c28224040470724140870714940525034140c2c030b00870730b00c2c034140525014940c28204840c28211414c2c030b00c28230b00c2c011414121004940170730b00c2c015110525014940170714940525015110c2c030b01000230b00c2c015140464415141001011910464415140c2c030b01001030b00c2c040000525014941001014940525040000c2c030b00870714540515034140c1c030700870730700c1c034140515014540470720e08838230a08c1c030700470730700c1c030a08838220e09001030700c1c030b00838230b01000f20e08838230b00c1c030700170730700c1c015110515014540170714540515015110c1c030701000230700c1c015140454415141000f11510454415140c1c030701000d30700c1c040004515014541000f14540515040004c1c030700d05015110d05031111000d31110d05080008d05031110544415111000305c1c170730a08544430a09000d15110544430a08170730a09000240008d0c031110545015140d05040008d05031112000131110d05015140545011c1c141005040c28215140c28211c1c545015140c28205040c28215111000515111000215140545040009000204c1d000240014c4c034141000e34140830340034830334142000034140830340038830311c1d000411c1cc2824000cc28211c1d000311c1cc28240010c282 (by decide +kernel)

def state215_44 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_44 : Impossible true (goalAt 215) 4 state215_44.toFinset :=
  node_ok cuts215 [] 0x24140d0c034300544424a08d0c034300c28224140c28230a08844415140c4c031300545031300d0c015140c4c020e08c4c03130084c014940c2c030b00525030b00d0c014940c2c030a08c2c030b01000830700c1c020e08c2c0 (by decide +kernel)

def state215_45 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 4,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_45 : Impossible true (goalAt 215) 5 state215_45.toFinset :=
  node_ok cuts215 [⟨state215_44,exclude215_44⟩] 0x525030b00c2c014940c2c034300525030b00c28230b00c2c01041cc2c031300848230b00905034300d0c015110928234300d0c030a08905030a08c28221110454424140830724140454430b02000030b00454434300160734300430730a08454430a08c1c015140c4c031300545031300d0c015140c4c021a08c4c03130084c0 (by decide +kernel)

def state215_46 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_46 : Impossible true (goalAt 215) 5 state215_46.toFinset :=
  node_ok cuts215 [⟨state215_44,exclude215_44⟩] 0x905034300d0c015110928234300d0c030a08545031300c4c015140c4c034300545031300868231300c4c021300905030a08c28221110850720e08838224140838234300150734300838231302000031300838230608450720e08c1c014940c2c030b00525030b00d0c014940c2c030b00c4c021208c2c030a08c2c030b010008 (by decide +kernel)

def state215_47 : List Sig := [0x3333333333333333030300000303000033333333333333330303000003030000,0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 2,input 4,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_47 : Impossible true (goalAt 215) 5 state215_47.toFinset :=
  node_ok cuts215 [] 0x515030700c1c014540c1c034300515030700c1c031300454430700838230700c1c020e08905034300d0c015110928234300d0c030a08545031300c4c015140c4c034300545031300848231300c4c021208905030a08c28210a00525030b00c2c014940c1c020e08c1c030b00c2c014940d0c030b00c2c021208c4c030b004507 (by decide +kernel)

def state215_48 : List Sig := [0xffffffffffffffff0f0f00000f0f0000ffffffffffffffff0f0f00000f0f0000,input 2,input 4,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_48 : Impossible true (goalAt 215) 6 state215_48.toFinset :=
  node_ok cuts215 [⟨state215_45,exclude215_45⟩,⟨state215_46,exclude215_46⟩,⟨state215_47,exclude215_47⟩] 0x21c1c525014940905030b00c2c021c1cc2c030b00905014940525005c1cc2c030b00d0c014940d0c005c1c525014940d0c030b00c2c021a08c2c030b00c4c011910c4c021a08464421208c4c030b00c2c030a0a000230a08450530b00c2c030a08c2c030b00450540030450721c1c515014540905030700c1c021c1cc1c030700905014540515040030c1c030700c2c020e08c2c080004838220e08c2c030700c1c005c1cc1c030700d0c014540d0c005c1c515014540d0c030700c1c04000cc1c030700c4c011510c4c080000454411510c4c030700c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838224140544424140c44434300d0c024140d0c034300c44415110544440010170724a08c28234300d0c040010d0c034300c28205c1cc28231110545015140905031300c4c031110c4c031300905015140545015110c4c031300d0c015140d0c015110545015140d0c031300c4c011c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c024140470724140870730a08c28224140c28230a08870711c1c8444 (by decide +kernel)

def state215_49 : List Sig := [0xffffffffffffffffffffffffffffffff0f0f00000f0f00000f0f00000f0f0000,input 7,input 2,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_49 : Impossible true (goalAt 215) 6 state215_49.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩] 0xd05030a08c28224140470730a08c28211c1cc28230b00c2c004940c2c034300908230b00c2c031300848230b00525030b00c2c014940464430b00c2c011910838230700c1c020e08c1c030b00838230700c1c034300515030700c1c031300454430700515030700c1c014540454430700c1c011510928234300d0c024300d05034300d0c015110544434300d0c015110868231300c4c021300c4c034300544431300d45031300c4c034142000031300c4c015140c444 (by decide +kernel)

def state215_50 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_50 : Impossible true (goalAt 215) 5 state215_50.toFinset :=
  node_ok cuts215 [] 0x15110c28230a08844430a08c2c030b00125011910c2c030b00464420e08c1c030700838230700c2c020e08c1c011510c1c030700454424a08d0c03430090c034300c2c024208c2c034300c1c014540c1c015140c4c034300c4c004c1c94c031300c4c021a08c2c021208c2c031300c1c014540c1c0313008307 (by decide +kernel)

def state215_51 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 7,0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 4,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_51 : Impossible true (goalAt 215) 6 state215_51.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩,⟨state215_50,exclude215_50⟩] 0x31110c28230a08844430a08c2c030b00125030b00525014940c2c014940c2c030b00525020e08c1c030700838230700c2c020e08c1c030700515014540c1c014540c1c030700515005c1cc28215110c28215110c44480004544405140c28215140c28214940c2c014940c2c014540c1c014540c1c034300545031110d4501514054503130200003130084c031300c4c021a08c2c021208c2c031300c1c014540c1c031300c4c015110d4c031300d050 (by decide +kernel)

def state215_52 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 2,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_52 : Impossible true (goalAt 215) 6 state215_52.toFinset :=
  node_ok cuts215 [⟨state215_50,exclude215_50⟩] 0xd05030a08c28224140544430a08c28205110c28230b00c2c004940c2c031300848230b00525030b00c2c014940464430b00c2c011910838230700c1c020e08c1c030b00838230700c1c031300454430700515030700c1c014540454430700c1c011510868231300c4c025302000031300c4c015300544431300c4c040008928234300d0c024300d0c030b00908230b00d0c030700515030700545034140d0c034300128204c0cc444 (by decide +kernel)

def state215_53 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_53 : Impossible true (goalAt 215) 7 state215_53.toFinset :=
  node_ok cuts215 [⟨state215_48,exclude215_48⟩,⟨state215_49,exclude215_49⟩,⟨state215_51,exclude215_51⟩,⟨state215_52,exclude215_52⟩] 0xd05011c1cd05024040c28230a08d05030a08c28224040470724140870714940525034140c2c030b00870730b00c2c034140525014940c28204840c28211414c2c030b00c28230b00c2c011414121004940170730b00c2c015110525014940170714940525015110c2c030b00868230b00c2c031300464431300868211910848231300c2c030b00870714540515034140c1c030700870730700c1c034140515014540470720e08838230a08c1c030700470730700c1c030a08838220e09001030700c1c030b00838230b01001120e08838230b00c1c030700170730700c1c015110515014540170714540515015110c1c030701000230700c1c031300454431301001111510454431300c1c030700d05015110d05031111000531110d0508000cd05031110544415111000505c1c170730a08544430a09000515110544430a08170730a08c44480008c44434140c4c031300c44431300c4c034141000234140470721a08868230a08c4c031300470731300c4c030a08868221301000240008d4c015111000515111000231300c4c034141000e34140c44440014c44434142000134140c44440014c44440015000440010c28240014c28240015000380000c28240010c28214941000014940c2c040040c2c014941001014940c2c040000c2c014541000114540c1c040014c1c014541001114540c1c040004c1c0400090002343010005400085450 (by decide +kernel)

def state215_54 : List Sig := [0xffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0,input 4,input 2,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_54 : Impossible true (goalAt 215) 6 state215_54.toFinset :=
  node_ok cuts215 [⟨state215_30,exclude215_30⟩] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c031300848230b00c2c014940525030b00838230700c1c020e08c1c030b00838230700515030700c1c014540c1c031300454430700c1c014540515030700868231300c4c021300545031300c4c015140c4c015140545031300130330a0a000030a08d05031110d05031110c28210c0cc28210c0cc2c014940c2c014940c1c014540c1c014540c44434140c44434140c4c015140c4c015140d0c0 (by decide +kernel)

def state215_55 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_55 : Impossible true (goalAt 215) 6 state215_55.toFinset :=
  node_ok cuts215 [⟨state215_40,exclude215_40⟩] 0x34140c28230a08905031110c28230a08844430a08c2c030b00125030b00c4c021208c2c014940c2c030b00525030b00d0c024208c2c011910c2c030b00464420e08c1c030700838230700c2c020e08c1c030700c4c011510c1c014540c1c030700515030700d0c014540c1c011510c1c030700454421a08c4c03130084c015140c4c034302000031300c44431300c4c020c1cc44434140d05040008928234300d0c024300d05034300d0c004a085444 (by decide +kernel)

def state215_56 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_56 : Impossible true (goalAt 215) 6 state215_56.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140c28230b00c2c004940c2c031300848230b00525030b00c2c014940c2c014940525030b00838230700c1c020e08c1c030b00838230700c1c031300454430700515030700c1c014540c1c014540515030700868231300c4c021300545031300130315110c4c005c1cc28215110c28234140544434140130330a08c44430a08844430b00525030b00525030700515030700515031300c44431300830720c0cd0c0 (by decide +kernel)

def state215_57 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_57 : Impossible true (goalAt 215) 7 state215_57.toFinset :=
  node_ok cuts215 [⟨state215_41,exclude215_41⟩,⟨state215_39,exclude215_39⟩,⟨state215_31,exclude215_31⟩,⟨state215_54,exclude215_54⟩,⟨state215_55,exclude215_55⟩,⟨state215_56,exclude215_56⟩] 0xc44411c1cc44421c1cc28230a08c44430a08c28221c1c470721111000310c0c430340010c28230a09000330a08c28240010430310c0d000324a08928230a08d0c034302000234300d0c030a08928224302000515110544431110d0c034302000434300d0c031110544415112000304c0c130340014d0c034302000134300d0c040014130304c0cc28204840c28211414c2c030b00c28230b00c2c011414121004940928230b00c2c034300525034300928214940908234300c2c030b00870714940525031110c2c030b00870730b00c2c031110525014940868230b00c2c031300464431300868211910848231300c2c030b01001014940525040000c2c030b01001030b00c2c040000525014940470720e08838230a08c1c030700470730700c1c030a08838220e08170730700c1c034300515034300170714540515034300c1c030701001030700c1c030b00838230b01001220e08838230b00c1c030700870714540515031110c1c030700870730700c1c031110515014541000230700c1c031300454431301001211510454431300c1c030701001214540515040004c1c030701001230700c1c040004515014541000240008d05011c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c015110c4c031300d0c040008d0c015112000015110d0c031300c4c031111000e31111000231300c4c040009000220c1d0002400385450 (by decide +kernel)

def state215_58 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000ffff0000ffff0000,input 4,input 2,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_58 : Impossible true (goalAt 215) 6 state215_58.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c015140464430b00c2c034300908230b00464430b00c2c011910838230700c1c020e08c1c030b00838230700515030700c1c014540c1c015140454430700c1c034300515030700454430700c1c011510141030a08545030a08545034140c44415140d4c034300545034302000015140c4c031300928234300d0c024300d05034300d0c031110544430a08470730a08470734140c44434140c444 (by decide +kernel)

def state215_59 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_59 : Impossible true (goalAt 215) 6 state215_59.toFinset :=
  node_ok cuts215 [⟨state215_50,exclude215_50⟩] 0xc44430a08c28221110c28230b00c2c004940c2c015140464430b00c2c034300908230b00464430b00c2c011910838230700c1c020e08c1c030b00838230700c1c015140454430700c1c034300515030700454430700c1c011510141030a08545030a0a000034300545034300c44415140545040008c28234140c28224140c2c014940c2c014940c1c014540c1c014540c4c034300d05034300128220c0c928234300d0c0243005444 (by decide +kernel)

def state215_60 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 0,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_60 : Impossible true (goalAt 215) 7 state215_60.toFinset :=
  node_ok cuts215 [⟨state215_51,exclude215_51⟩,⟨state215_32,exclude215_32⟩,⟨state215_58,exclude215_58⟩,⟨state215_59,exclude215_59⟩] 0xc44411c1cc44421c1cc28230a08c44430a08c28221c1c470721111000324a08928230a08d0c034302000134300d0c030a08928224301000e15110544431110d0c034302000334300d0c031110544415110c28204840c28211414c2c030b00c28230b00c2c011414121004940928230b00c2c034300525034300928214940908234300c2c030b00870714940525031110c2c030b00870730b00c2c031110525014941000230b00c2c015140464415141001011910464415140c2c030b00470720e08838230a08c1c030700470730700c1c030a08838220e08170730700c1c034300515034300170714540515034300c1c030701001030700c1c030b00838230b01001320e08838230b00c1c030700870714540515031110c1c030700870730700c1c031110515014541000230700c1c015140454415141001311510454415140c1c030700470705040141030a08545030a08470715140545030a08141030a08544480000544434300545034300544415140545034301000234301000240008d45031111000e31111000215140545030a09000430a08470740038470730a09000330a08470740010470734301000534300544440038544434302000234300544440014544430b01000030b00525040040525030b01001030b00525040000525030701000130700515040038515030701001330700515040004515040009000234141000e40008c4c0 (by decide +kernel)

def state215_61 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,input 4,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_61 : Impossible true (goalAt 215) 6 state215_61.toFinset :=
  node_ok cuts215 [] 0x31110545015140d05031300c4c031110c4c031300d05015140545011c1c848221208c28231300c4c011c1cc4c031300c28221208848215110c4c031300d0c015140d0c015110545015140d0c031300c4c02141c515014540d05030700c1c02141cc1c030700d05014540515040020c1c030700c4c011510c4c040020454411510c4c030700c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838205c1cc1c030700d0c014540d0c005c1c515014540d0c030700c1c034140470734140901030a08c28234140c28230a08901011c1c905034140544434140c44434300d0c034140d0c034300c44415110544440028928224a08c28234300d0c040024d0c034300c28224a0890c034140525014940850730b00c2c034140c2c030b00850714940525031300c2c030b00848211910848231300464431300848230b00c2c030700c2c030700838240020838230701000830700838230b00c2c040028121004940c28230b00c2c040024c2c030b00c28204840c28234300c2c030b00928214940908234300525034300928230b00c2c0 (by decide +kernel)

def state215_62 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_62 : Impossible true (goalAt 215) 5 state215_62.toFinset :=
  node_ok cuts215 [] 0x21a08c4c03130084c031300d0c015140c4c015140c4c031300545030b00c4c021208c2c030a08c2c030b00125030b00d0c024208c2c014940c2c030b00525034140c28230a08905024a08d0c03430090c034140d0c034300544430700454431300c1c030700838230b00c1c020e08c1c030700838230700515034300c1c014540c1c0307005150 (by decide +kernel)

def state215_63 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_63 : Impossible true (goalAt 215) 5 state215_63.toFinset :=
  node_ok cuts215 [] 0x21a08c4c03130084c031300d0c015140c4c015140c4c031300545030700c4c011510c1c020e08c1c030700838230700d0c014540c1c014540c1c030700515034140c28230a08905024a08d0c03430090c034140d0c034300544430b00848231300c2c030700838230700c2c004940c2c030b00c28230b00908234300c2c014940c2c030b005250 (by decide +kernel)

def state215_64 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_64 : Impossible true (goalAt 215) 5 state215_64.toFinset :=
  node_ok cuts215 [] 0x30a08c2c030b00125030b00d0c024208c2c014940c2c030b00525030700c2c020e08c1c020e08c1c030700838230700d0c014540c1c014540c1c030700515034140c28230a08905024a08d0c03430090c034140d0c034300544430b00848230b00c4c030700454430700c4c021300c4c031300868231300545034300c4c015140c4c0313005450 (by decide +kernel)

def state215_65 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_65 : Impossible true (goalAt 215) 6 state215_65.toFinset :=
  node_ok cuts215 [⟨state215_62,exclude215_62⟩,⟨state215_63,exclude215_63⟩,⟨state215_64,exclude215_64⟩] 0x868231300c4c021300c4c034300545031300545031300c4c015142000231300c4c040008c2c031300848230b00c28230b00c2c004940c2c034300908230b00525030b00c2c014942000130b00c2c040000c1c031300454430700c1c030b00838230700838230700c1c020e08c1c034300515030700515030700c1c014542000030700c1c040004d05030a08c28224140470724a08d0c03430090c034140d0c034300544405c1c8707 (by decide +kernel)

def state215_66 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_66 : Impossible true (goalAt 215) 6 state215_66.toFinset :=
  node_ok cuts215 [] 0x868231300c4c021300c4c034300545031300545031300c4c015140c2c031300848230b00c28230b00c2c004940c2c034300908230b00525030b00c2c014940c1c031300454430700c1c030b00838230700838230700c1c020e08c1c034300515030700515030700c1c014540c70730a08c28221c1c928234300d0c024300544434300d0c015110545031300545031300525030b00525030b00515030700515030700470730a09000530a08544434300544434300d050 (by decide +kernel)

def state215_67 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_67 : Impossible true (goalAt 215) 6 state215_67.toFinset :=
  node_ok cuts215 [⟨state215_11,exclude215_11⟩] 0x31300d0c015140c4c021a08c4c03130084c015140c4c031300545005040c4c031300145030b00c4c021208c2c030b00d0c014940c2c030a08c2c030b01000a14940c2c030b00525004840c2c030b00125030700c4c011510c1c030700c2c020e08c1c030700d0c014540c1c020e08c1c030700838214540c1c030700515004440c1c030700115024a08905034300d0c015112000034300d0c005110905030a08c28221110470730a08c282400149010 (by decide +kernel)

def state215_68 : List Sig := [0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_68 : Impossible true (goalAt 215) 5 state215_68.toFinset :=
  node_ok cuts215 [] 0xc4c034300545031300848231300c4c021208545031300c4c015140c1c031300454430700c1c034300515030700838230700c1c020e08515030700c1c014540c1c030b00838230700908234140d0c034300544434140c28230a08428030b00c4c021208c2c030b00d0c014940c2c030a08c2c030b00450714940c2c030b005250 (by decide +kernel)

def state215_69 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_69 : Impossible true (goalAt 215) 6 state215_69.toFinset :=
  node_ok cuts215 [⟨state215_21,exclude215_21⟩,⟨state215_68,exclude215_68⟩] 0x31300d0c015140c4c021a08c4c031300868215140c4c031300545030b00c4c021208c2c030b00d0c014940c2c011c1cc2c030b00450714940c2c030b00525030700c4c011510c1c030700c2c020e08c1c030700d0c014540c1c020e08c1c030700838214540c1c030700515024a08d05034300d0c015110d05031c1cd05011c1c868231300868231301000a30b02000130b0083823070083823070090c034302000034301000511c1cc28230a089050 (by decide +kernel)

def state215_70 : List Sig := [0x3333333333333333333300003333000033333333333333333333000033330000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_70 : Impossible true (goalAt 215) 6 state215_70.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545021208c4c031300848231300d0c015140c4c021208c4c031300848214540c1c030700515030700c4c011510c1c020e08c1c030700838230700d0c014540c1c020e08c1c030700838234140901024140905030a08d05034300d0c015111000a3430090c024a08d0502141cd0502141c525030b00c2c014940c2c021208c4c030b00c1c020e08c1c030b00125030b00c2c004840c2c014940d0c030b010000 (by decide +kernel)

def state215_71 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_71 : Impossible true (goalAt 215) 7 state215_71.toFinset :=
  node_ok cuts215 [⟨state215_61,exclude215_61⟩,⟨state215_65,exclude215_65⟩,⟨state215_66,exclude215_66⟩,⟨state215_67,exclude215_67⟩,⟨state215_69,exclude215_69⟩,⟨state215_70,exclude215_70⟩] 0xc44415140545034140c4c031300c44431300c4c034140545015141000421a0886824000cc4c031301000331300c4c040010868221a08544431300c4c034300545034300544415140545034300c4c031301000321a08868240008c4c031301000331300c4c040008868221a08870714940525034140c2c030b00870730b00c2c034140525014940868230b00c2c031300464431300868211910848231300c2c030b01000404840121040028c2c030b01000a30b00c2c040010121004941000a30b00c2c034300525034301000a14940525034300c2c030b01000a80016000040000c2c030b01000a30b00c2c040001000a40000870714540515034140c1c030700870730700c1c034140515014541000630700c1c031300454431301000611510454431300c1c030701000630700c1c030b00838230b01000620e08838230b00c1c030701000420e08838240018c1c030701000630700c1c040010838220e09000630700c1c034300515034301000614540515034300c1c030701000620e08838240004c1c030701000630700c1c040004838220e08d05080010d05024041000424040d0508000c905024041000424141000440014c28234140544434140c44434300d0c034140d0c034300c44415110544440011000440011000534300d0c040011000424301000440010928234141000e341408707800088707341420001341408707400388707 (by decide +kernel)

def state215_72 : List Sig := [0xffffffffffffffffffffffffffffffff0000000000000000ffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_72 : Impossible true (goalAt 215) 6 state215_72.toFinset :=
  node_ok cuts215 [] 0x868231300c4c021300c4c034300545031300545031300c4c015140545031300c4c015140c2c031300848230b00c28230b00c2c004840c2c034300908230b00525030b00c2c014940525030b00c2c014940c1c031300454430700c1c030b00838230700838230700c1c020e08c1c034300515030700515030700c1c014540515030700c1c014540d01030a08c28224040470730a08c28211c1c928234300d0c024300544434300d0c015110544434300d0c015110d050 (by decide +kernel)

def state215_73 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_73 : Impossible true (goalAt 215) 7 state215_73.toFinset :=
  node_ok cuts215 [⟨state215_72,exclude215_72⟩] 0xc44415140545034140c4c031300c44431300c4c034140545015140470721a08868230a08c4c031300470731300c4c030a08868221300544431300c4c034300545034300544415140545034300c4c031300870714940525034140c2c030b00870730b00c2c034140525014940868230b00c2c031300464431300868211910848231300c2c030b00c28204840c28211414c2c030b00c28230b00c2c011414121004841000530b00c2c034300525034301000a14940525034300c2c030b00870714540515034140c1c030700870730700c1c034140515014541000630700c1c031300454431301000611510454431300c1c030701000630700c1c030b00838230b01000620e08838230b00c1c030700470720e08838230a08c1c030700470730700c1c030a08838220e09000530700c1c034300515034301000614540515034300c1c030700d05011c1cd05024040c28230a08d05030a08c28224040470721110d05015110d05031110d0c034300d05034300d0c031110544415111000440010d28240014d0c034300c28240010c28224041000e24040d05040014d05024042000024040d05040014d05005041000205040c4c040014c4c005041000305040c4c040008c4c004841000004840c2c040014c2c004841000a04840c2c040000c2c004441000104440c1c040014c1c004441000604440c1c040004c1c0400150004400250004400109282 (by decide +kernel)

def state215_74 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffff0000000000000000,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_74 : Impossible true (goalAt 215) 6 state215_74.toFinset :=
  node_ok cuts215 [] 0x31110545015140905031300c4c031110c4c031300905015140545015110c4c031300d0c015140d0c015110545015140d0c031300c4c011c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c021a08c2c030b00c4c011910c4c021a08464421208c4c030b00c2c021c1c525014940905030b00c2c021c1cc2c030b00905014940525005c1cc2c030b00d0c014940d0c005c1c525014940d0c030b00c2c030a08121030a08450530b00c2c030a08c2c030b0045050484012504004cc1c030700c4c011510c4c04004c454411510c4c030700c1c040050c1c030700c2c020e08c2c04004c838220e08c2c030700c1c021c1c515014540905030700c1c021c1cc1c030700905014540515005c1cc1c030700d0c014540d0c005c1c515014540d0c030700c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838224140544424140c44434300d0c024140d0c034300c44415110544440010170724a08c28234300d0c040010d0c034300c28205c1cc28224140470724140870730a08c28224140c28230a08870711c1c8444 (by decide +kernel)

def state215_75 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 4,input 7,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_75 : Impossible true (goalAt 215) 6 state215_75.toFinset :=
  node_ok cuts215 [] 0x31110470731110870730a08c28231110c28230a08870711c1c844411c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c031110545015140830331300c4c031110c4c031300830315140545015110c4c031300130315140545015110545015140130331300c4c011510c4c031300c1c04004cc1c011511001311510c1c031300c1c030a08121030a08450530b00c2c030a08c2c030b00450504840125021a08c2c030b00c4c011910c4c021a08464421208c4c030b00c2c021c1c525014940c44430b00c2c021c1cc2c030b00c44414940525005c1cc2c030b00544414940525005c1c525014940544430b00c2c020e08c2c030b00c1c040050c1c020e09001320e08c1c030b00c1c040014170705c1cc28215110c28240014544415110c28205c1cc28240014544415110c44440014c44440015000e04a08c44415110544414540544434300c1c005c1cc1c014540170714540c1c015110c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838221c1c515014540c44430700c1c021c1cc1c030700c444145405150 (by decide +kernel)

def state215_76 : List Sig := [0xffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccccccc,input 4,input 7,input 0,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_76 : Impossible true (goalAt 215) 6 state215_76.toFinset :=
  node_ok cuts215 [] 0x31110470731110870730a08c28231110c28230a08870711c1c844411c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c031110545015140830331300c4c031110c4c031300830315140545015110c4c031300908215140908215110545015140908231300c4c011910c4c031300c2c021a08c2c011910868221208c2c031300c2c011c1c838220e08c28230700c1c011c1cc1c030700c28220e0883824004cc1c030700c4c011510c4c04004c454411510c4c030700c1c021c1c515014540c44430700c1c021c1cc1c030700c44414540515005c1cc1c030700908214540908205c1c515014540908230700c1c040050c1c030700c2c020e08c2c04004c838220e08c2c030700c1c040014908224208c28215110c28240014544415110c28224208908240014544415110c44424208908240014908224208c44415110544414940544434300c2c024208c2c014940908224208c2c015110c2c030a08121030a08450530b00c2c030a08c2c030b00450504840125021c1c525014940c44430b00c2c021c1cc2c030b00c444149405250 (by decide +kernel)

def state215_77 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_77 : Impossible true (goalAt 215) 6 state215_77.toFinset :=
  node_ok cuts215 [] 0x31110470731110870730a08c28231110c28230a08870711c1c844430a08121030a08450530b00c2c030a08c2c030b00450504840125021c1c525014940c44430b00c2c021c1cc2c030b00c44414940525005c1cc2c030b00544414940525005c1c525014940544430b00c2c021a08c2c030b00c4c011910c4c021a08464421208c4c030b00c2c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838240050c1c030700c2c020e08c2c04004c838220e08c2c030700c1c021c1c515014540c44430700c1c021c1cc1c030700c44414540515005c1cc1c030700544414540515005c1c515014540544430700c1c04004cc1c030700c4c011510c4c04004c454411510c4c030700c1c040014170705c1cc28215110c28240014544415110c28205c1cc28240014544415110c44440014c44440015000e04a08c44415110544415140130334300c4c015110c4c015140544415140c4c004c0cc4c011c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c031110545015140830331300c4c031110c4c0313008303151405450 (by decide +kernel)

def state215_78 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffff0000000000000000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_78 : Impossible true (goalAt 215) 6 state215_78.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140c4c034300545031300868231300c4c021a08868231300c4c021a08c2c031300848230b00525030b00c2c014940c2c034300525030b00121030b00c2c004840121030b00c2c004840c1c031300454430700c1c030b00838230700515030700c1c014540c1c034300515030700838230700c1c020e08838230700c1c020e08d05034300d0c015110170734300d0c024300928234300d0c005c1cd05021c1c905024140c282341409010341408707 (by decide +kernel)

def state215_79 : List Sig := [0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_79 : Impossible true (goalAt 215) 7 state215_79.toFinset :=
  node_ok cuts215 [⟨state215_74,exclude215_74⟩,⟨state215_75,exclude215_75⟩,⟨state215_76,exclude215_76⟩,⟨state215_77,exclude215_77⟩,⟨state215_78,exclude215_78⟩] 0xc44411c1cc44421c1cc28230a08c44430a08c28221c1c470721110470721a08868230a08c4c031300470731300c4c030a08868221300c44415140545020c0cc4c031300c44431300c4c020c0c545015140544431300c4c004c0c545015140544415140545004c0cc4c031301000531300c4c040009000540009000d40016000340008c4c031300c28204840c28211414c2c030b00c28230b00c2c011414121004940868230b00c2c031300464431300868211910848231300c2c030b00870714940525031110c2c030b00870730b00c2c031110525014940170730b00c2c015110525014940170714940525015110c2c030b01000530b00c2c040001000540001001440016000240000c2c030b00470720e08838230a08c1c030700470730700c1c030a08838220e09001330700c1c031300454431301001311510454431300c1c030701001430700c1c030b00838230b01001320e08838230b00c1c030700870714540515031110c1c030700870730700c1c031110515014540170730700c1c015110515014540170714540515015110c1c030701000530700c1c040005000540005001340016000140004c1c030701000505c1c170730a08544430a09000515110544430a08170730a09000515110544431111000531111000540038128240015000440010c28240014c28240016000480000c28240010c28240015000e34141000540014d0c0 (by decide +kernel)

def state215_80 : List Sig := [0xafafafafafafafafafafafafafafafafafafaaaaafafaaaaafafaaaaafafaaaa,input 0,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_80 : Impossible true (goalAt 215) 5 state215_80.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c034300908230b00928234300d0c024300d05034300d0c015110838230700c1c021700c1c030b00838230700515030700c1c014540c1c034300515030700454421300c4c031300868230b00848230b00c4c015140c4c031300545031300545034300c4c0 (by decide +kernel)

def state215_81 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x505050505050505050505050505050505050000050500000505000005050000,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_81 : Impossible true (goalAt 215) 4 state215_81.toFinset :=
  node_ok cuts215 [] 0x34140c28230a08905024a08d0c03430090c034140d0c034300544421300c4c031300838215140c4c031300545031300545034300c4c030b00838230700c1c030a08c2c030b00125014940c2c030b00525030b00d0c024208c2c0 (by decide +kernel)

def state215_82 : List Sig := [0x505050505050505050505050505050505050000050500000505000005050000,input 0,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_82 : Impossible true (goalAt 215) 5 state215_82.toFinset :=
  node_ok cuts215 [⟨state215_81,exclude215_81⟩] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c034300908230b00928234300d0c024300d05034300d0c015110430730a08454430a08454430b02000030b0045443414083073414045443430013073430084c031300c4c021a08c2c021208c2c031300545031300c4c015140c4c015140d0c031300c1c0 (by decide +kernel)

def state215_83 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_83 : Impossible true (goalAt 215) 5 state215_83.toFinset :=
  node_ok cuts215 [⟨state215_81,exclude215_81⟩] 0xd05030a08c28224140928234300d0c024300d05034300d0c01511084c031300c4c021a08545031300c4c015140c4c015140d0c031300c4c080000838231300c2c021208c2c031300838230608410720e08850720e08838234140838234300150734300c1c030a08c2c030b00125014940c2c030b00525030b00d0c024208c2c0 (by decide +kernel)

def state215_84 : List Sig := [0x4444444444444444444444444444444444444444444444444444444444444444,input 0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_84 : Impossible true (goalAt 215) 5 state215_84.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140928234300d0c024300d05034300d0c01511084c031300c4c021a08545031300c4c015140c4c015140d0c031300c1c011510c1c031300c2c021208c2c031300818030700c1c020f00515030700c1c014540c1c034300515030700c28230b00c2c004940525030b00c2c014940c2c034300908230b008382 (by decide +kernel)

def state215_85 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_85 : Impossible true (goalAt 215) 6 state215_85.toFinset :=
  node_ok cuts215 [⟨state215_24,exclude215_24⟩,⟨state215_34,exclude215_34⟩,⟨state215_80,exclude215_80⟩,⟨state215_82,exclude215_82⟩,⟨state215_83,exclude215_83⟩,⟨state215_84,exclude215_84⟩] 0x34140430734140901030a08c28234140c28230a08901010c1c905030a08121030a08410530b00c2c030a08c2c030b00410504840125021c1c525014940d05030b00c2c021c1cc2c030b00d05014940525024a08c2c030b00d0c014940d0c024a08525024208d0c030b00c2c010c1c838220e08c28230700c1c010c1cc1c030700c28220e08838280014c1c030700c2c020e08c2c080010838220e08c2c030700c1c021c1c515014540d05030700c1c021c1cc1c030700d05014540515005c1cc1c030700d0c014540d0c005c1c515014540d0c030700c1c080004928224a08c28234300d0c080000d0c034300c28224a0890c034140544434140c44434300d0c034140d0c034300c44415110544430a08868221300430731300c4c030a08c4c031300430721a08868230b00c4c030b00464421a08848230b00868230b00464431300c4c030700c4c03070045448000c454430702000230700454431300c4c034140545015140c44431300c4c034140c4c031300c44415140545034300c4c031300544415140545034300545034300544431300c4c0 (by decide +kernel)

def state215_86 : List Sig := [0xfafafafafafafafafafafafafafafafafafaaaaafafaaaaafafaaaaafafaaaaa,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_86 : Impossible true (goalAt 215) 5 state215_86.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140430730a08c28210c1cc28230b00c2c004940525030b00c2c014940c2c034300908230b00464430b00c2c011910c2c030700838230700830724a08d0c03430090c034140d0c004a08130720e08c1c03070085c014540c1c030700515030700d0c014540c1c011510c1c0307004544 (by decide +kernel)

def state215_87 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f00000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_87 : Impossible true (goalAt 215) 6 state215_87.toFinset :=
  node_ok cuts215 [⟨state215_38,exclude215_38⟩,⟨state215_86,exclude215_86⟩] 0x34140c28230a08905010c1cc28230a08430730a08c2c030b00125014940c2c030b00525030b00d0c024208c2c011910c2c030b00464430b00c4c021208c2c020e08c1c030700838230700c2c020e08c1c014540c1c030700515030700d0c014540c1c011510c1c030700454430700c4c080004c1c020c1c928234300d0c024300d05034300128204c1c868231300c4c021300545031300c4c015140c4c0343005450313020000 (by decide +kernel)

def state215_88 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_88 : Impossible true (goalAt 215) 6 state215_88.toFinset :=
  node_ok cuts215 [] 0x34140c28230a08905010c1cc28230a08430730a08c2c030b00125014940c2c030b00525030b00d0c024208c2c011910c2c030b00464420e08c1c030700838230700c2c020e08c1c014540c1c030700515030700d0c014540c1c011510c1c030700454431110928234300d0c024300d0503430012821511084c031300c4c021a08c2c021208c2c031300c1c011510c1c031300545031300c4c015140c4c015140d0c0313010002 (by decide +kernel)

def state215_89 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_89 : Impossible true (goalAt 215) 6 state215_89.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c034300908230b00c2c011910464430b00838230700c1c020e08c1c030b00838230700515030700c1c014540c1c034300515030700c1c011510454430700928234300d0c024300d05034300d0c015110470730a08430730a08c44434140c44434140544434300544434300c28211c1cc28211c1cc2c011910c2c011910c1c011510c1c011510d05031110d05031110d0c015110d0c015110c4c0 (by decide +kernel)

def state215_90 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_90 : Impossible true (goalAt 215) 6 state215_90.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140c4c034300545031300868231300c4c021a08c2c031300848230b00525030b00c2c014940c2c034300908230b00121030b00c2c004840c1c031300454430700c1c030b00838230700515030700c1c014540c1c034300515030700838230700c1c020e08d05034300d0c015110928234300d0c024a08d05024040d05024040868231300868231300121030b00121030b00838230700838230700901034140901034140928234300928234300c282 (by decide +kernel)

def state215_91 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_91 : Impossible true (goalAt 215) 7 state215_91.toFinset :=
  node_ok cuts215 [⟨state215_25,exclude215_25⟩,⟨state215_35,exclude215_35⟩,⟨state215_39,exclude215_39⟩,⟨state215_42,exclude215_42⟩,⟨state215_52,exclude215_52⟩,⟨state215_55,exclude215_55⟩,⟨state215_59,exclude215_59⟩,⟨state215_65,exclude215_65⟩,⟨state215_85,exclude215_85⟩,⟨state215_87,exclude215_87⟩,⟨state215_88,exclude215_88⟩,⟨state215_89,exclude215_89⟩,⟨state215_90,exclude215_90⟩] 0xd05011c1cd05024040c28230a08d05030a08c28224040470724142000c11c1c470740010c28230a0a000730a08c28240010470711c1c470721a08868230a08c4c031300470731300c4c030a08868221302000615140545034140c4c031302000531300c4c034140545015142000431300c4c034300545034302000315140545034300c4c031302000b8002a000840008c4c031302000231300c4c04000a000940008c28204840c28211414c2c030b00c28230b00c2c011414121004940868230b00c2c031300464431300868211910848231300c2c030b01001614940525034140c2c030b01001630b00c2c034140525014940928230b00c2c034300525034300928214940908234300c2c030b01001611910464440000c2c030b01001630b00c2c040000464411910470720e08838230a08c1c030700470730700c1c030a08838220e09001530700c1c031300454431301001511510454431300c1c030701001630700c1c030b00838230b01001520e08838230b00c1c030701001514540515034140c1c030701001530700c1c034140515014541001530700c1c034300515034301001514540515034300c1c030701001511510454440004c1c030701001530700c1c040004454411511000540014c44480004928224a08c28234300d0c080000d0c034300c28224a0890c034141000e34141000534300d0c040015000e04a09000e400385444 (by decide +kernel)

def state215_92 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_92 : Impossible true (goalAt 215) 4 state215_92.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545021a08c4c03130084c031300d0c015140c4c034140c28230a08905034140d0c034300544420e08d0c03430090c030b00c4c021208c2c014540c2c030b00515030a08c2c030b00140730700c1c020e08c2c0 (by decide +kernel)

def state215_93 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_93 : Impossible true (goalAt 215) 4 state215_93.toFinset :=
  node_ok cuts215 [] 0x14940c2c030b00525030a08c2c030b00110730b00d0c024208c2c030b00c4c021208c2c034140c28230a08905034140d0c034300454424a08d0c03430090c014540c4c031300515021a08c4c03130084c030700c1c014540c4c0 (by decide +kernel)

def state215_94 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 7,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_94 : Impossible true (goalAt 215) 5 state215_94.toFinset :=
  node_ok cuts215 [⟨state215_92,exclude215_92⟩,⟨state215_93,exclude215_93⟩] 0x545031300c4c015140868231300c4c021300c4c034300545031300c2c031300848230b00525030b00c2c014940c28230b00c2c00541cc2c034300908230b00d05030a08c28224140515031302000131300515030b02000030b00515030540870714540170730a08515030a08c1c034140d0c034300544424a08d0c03430090c0 (by decide +kernel)

def state215_95 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_95 : Impossible true (goalAt 215) 4 state215_95.toFinset :=
  node_ok cuts215 [] 0x34140d0c034300544424a08d0c03430090c034140c28230a08905014940c2c030b00525030b00d0c024208c2c030a08c2c030b01000830700c1c020e08c2c015140c4c031300545031300d0c015140c4c020e08c4c03130084c0 (by decide +kernel)

def state215_96 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_96 : Impossible true (goalAt 215) 5 state215_96.toFinset :=
  node_ok cuts215 [⟨state215_92,exclude215_92⟩,⟨state215_95,exclude215_95⟩] 0x545031300c4c015140c4c034300545031300868231300c4c021300d05034300d0c015110928234300d0c024300d05030a08c28224140838231302000131300850720e08838234140838234302000034300838230608450720e08c1c030b00c4c021208c2c014940c2c030b00525030b00d0c024208c2c030a08c2c030b010008 (by decide +kernel)

def state215_97 : List Sig := [0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,input 0,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_97 : Impossible true (goalAt 215) 5 state215_97.toFinset :=
  node_ok cuts215 [⟨state215_93,exclude215_93⟩,⟨state215_95,exclude215_95⟩] 0x525030b00c2c014940c2c034300908230b00c28230b00c2c01041cc2c031300848230b00d05034300d0c015110928234300d0c024300d05030a08c28224140454430b02000130b00454434140830734140454434302000034300430730a08454430a08c1c015140c4c031300545031300d0c015140c4c021a08c4c03130084c0 (by decide +kernel)

def state215_98 : List Sig := [0x3333333333333333000000000000000033333333333333333333000033330000,0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_98 : Impossible true (goalAt 215) 5 state215_98.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140c4c034300545031300848231300c4c021208c1c031300454430700515030700c1c014540c1c034300515030700838230700c1c020e08d05034300d0c015110908234300d0c024208d05030a08c28210a00c2c021208c4c030b00c1c020e08c1c030b00525030b00c2c014940c2c024208d0c030b004507 (by decide +kernel)

def state215_99 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_99 : Impossible true (goalAt 215) 6 state215_99.toFinset :=
  node_ok cuts215 [⟨state215_94,exclude215_94⟩,⟨state215_96,exclude215_96⟩,⟨state215_97,exclude215_97⟩,⟨state215_98,exclude215_98⟩] 0x31110545015140d05031300c4c031110c4c031300d05015140545015110c4c031300d0c015140d0c015110545015140d0c031300c4c011c1c868221a08c28231300c4c011c1cc4c031300c28221a0884c021a08c2c030b00c4c011910c4c021a08464421208c4c030b00c2c021c1c525014940d05030b00c2c021c1cc2c030b00d05014940525024a08c2c030b00d0c014940d0c024a08525024208d0c030b00c2c030a0a000330a08450530b00c2c030a08c2c030b0045054002c450740034c1c030700c4c011510c4c080008454411510c4c030700c1c04002cc1c030700c2c020e08c2c080004838220e08c2c030700c1c021c1c515014540d05030700c1c021c1cc1c030700d05014540515040014c1c030700d0c014540d0c080000515014540d0c030700c1c011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838234140544434140c44434300d0c034140d0c034300c44415110544440010928224a08c28234300d0c040010d0c034300c28224a0890c034140470734140870730a08c28234140c28230a08870711c1c9050 (by decide +kernel)

def state215_100 : List Sig := [0x3333333333333333000000000000000033333333333333333333000033330000,input 6,input 4,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_100 : Impossible true (goalAt 215) 5 state215_100.toFinset :=
  node_ok cuts215 [] 0x15140c4c031300545031300d0c015140c4c021208c4c031300848230700c4c011510c1c014540c1c030700515030700d0c014540c1c020e08c1c030700838234140d0c034300544424208d0c034300908234140c28230a08428030b00848231300c2c030700838230700c2c014940c2c030b00525030b00908234300c2c004940c2c030b00c282 (by decide +kernel)

def state215_101 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_101 : Impossible true (goalAt 215) 6 state215_101.toFinset :=
  node_ok cuts215 [⟨state215_100,exclude215_100⟩] 0x545031300c4c015140c4c034300545031300868231300c4c021a08868231300c4c021a08c2c031300848230b00525030b00c2c014940c2c034300908230b00121030b00c2c004942000030b00c2c040000c1c031300454430700c1c030b00838230700515030700c1c014540c1c034300515030700838230700c1c020e08838230700c1c020e08d05034300d0c015110928234300d0c024a08928234300d0c024a08d05034040d05021c1cc282341408707341409010 (by decide +kernel)

def state215_102 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_102 : Impossible true (goalAt 215) 7 state215_102.toFinset :=
  node_ok cuts215 [⟨state215_99,exclude215_99⟩,⟨state215_101,exclude215_101⟩] 0xc44411c1cc44421c1cc28230a08c44430a08c28221c1c470721110470721a08868230a08c4c031300470731300c4c030a08868221300c44415140545020c0cc4c031300c44431300c4c020c0c545015141000531300c4c034300545034301000d15140545034300c4c031300c28204840c28211414c2c030b00c28230b00c2c011414121004940868230b00c2c031300464431300868211910848231300c2c030b00870714940525031110c2c030b00870730b00c2c031110525014940928230b00c2c034300525034300928214940908234300c2c030b00470720e08838230a08c1c030700470730700c1c030a08838220e09000d30700c1c031300454431301001711510454431300c1c030701000b30700c1c030b00838230b01001720e08838230b00c1c030700870714540515031110c1c030700870730700c1c031110515014541000530700c1c034300515034301001714540515034300c1c030701000524a08928230a08d0c034301000534300d0c030a08928224301000540038d44440014d0c034300c44440014c44440015000440010c28240014c28240016000180000c28240010c28215141000215140c4c040014c4c015141000d15140c4c040008c4c014941000014940c2c040014c2c014941000b14940c2c040000c2c014541000114540c1c040014c1c014541001714540c1c040004c1c0400150016341410005400145444 (by decide +kernel)

def state215_103 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 4,input 7,input 0,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_103 : Impossible true (goalAt 215) 6 state215_103.toFinset :=
  node_ok cuts215 [] 0xd05030a08c28224140c28230b00c2c004940525030b00c2c014940c2c014940525030b00c2c031300848230b00525030b00c2c014940838230700c1c020e08c1c030b00838230700515030700c1c014540c1c014540515030700c1c031300454430700515030700c1c014540170730a08544430a08d05031110d05015110868231300c4c021300c44431300c4c034140c4c035300544431300545030a08430330a08430331110d05031110d05015110130334300d0c0 (by decide +kernel)

def state215_104 : List Sig := [0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_104 : Impossible true (goalAt 215) 6 state215_104.toFinset :=
  node_ok cuts215 [] 0x545031300c4c015140c4c034300545031300868231300c4c021300141031300c4c005040c2c031300848230b00525030b00c2c014940c2c034300525030b00c28230b00c2c004840121030b00c2c004840c1c031300454430700c1c030b00838230700515030700c1c014540c1c034300515030700838230700c1c020e08111030700c1c004440d05034300d0c015110d28234300d0c030a08170734300d0c024a08d05030a08c282211104707341409010341409010 (by decide +kernel)

def state215_105 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_105 : Impossible true (goalAt 215) 7 state215_105.toFinset :=
  node_ok cuts215 [⟨state215_26,exclude215_26⟩,⟨state215_36,exclude215_36⟩,⟨state215_56,exclude215_56⟩,⟨state215_103,exclude215_103⟩,⟨state215_104,exclude215_104⟩] 0xd05011c1cd05024040c28230a08d05030a08c28224040470724140470721a08868230a08c4c031300470731300c4c030a08868221301000e15140545034140c4c031302000231300c4c034140545015140544431300c4c004c0c545015140544415140545004c0cc4c031300c28204840c28211414c2c030b00c28230b00c2c011414121004940868230b00c2c031300464431300868211910848231300c2c030b01000e14940525034140c2c030b01001430b00c2c034140525014940170730b00c2c015110525014940170714940525015110c2c030b00470720e08838230a08c1c030700470730700c1c030a08838220e09001330700c1c031300454431301001311510454431300c1c030701001430700c1c030b00838230b01001320e08838230b00c1c030701000e14540515034140c1c030701001330700c1c034140515014540170730700c1c015110515014540170714540515015110c1c030702000105c1c170730a08544430a0a000015110544430a08170730a09000540038d44434141000e34141000515110544430a09000430a08470740038470730a0a000430a08470740010470731301000231300545040038545031302000331300545040008545030b01000030b00525040038525030b01001430b00525040000525030701000130700515040038515030701001330700515040004515040015000531111000e40058d0c0 (by decide +kernel)

def state215_106 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_106 : Impossible true (goalAt 215) 6 state215_106.toFinset :=
  node_ok cuts215 [⟨state215_11,exclude215_11⟩] 0x545031300c4c015140868231300c4c021300c4c015140545031300c2c031300848230b00525030b00c2c014940c28230b00c2c004940c2c014940525030b00c1c031300454430700c1c030b00838230700515030700c1c014540838230700c1c020e08c1c014540515030700d05030a08c28224140d05031110d05031110170730a0a000030a08c4c015140c4c015140c2c014940c2c014940c1c014540c1c014540c44434140c44434140c28211c1cc28240010d0c0 (by decide +kernel)

def state215_107 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_107 : Impossible true (goalAt 215) 7 state215_107.toFinset :=
  node_ok cuts215 [⟨state215_65,exclude215_65⟩,⟨state215_67,exclude215_67⟩,⟨state215_106,exclude215_106⟩] 0xd05015110d05031110d0c034300d05034300d0c031110544415111000424a08928230a08d0c034302000134300d0c030a08928224302000205c1c170740014d0c034302000034300d0c040014170705c1c544431300c4c034300545034300544415140545034300c4c031300c44415140545034140c4c031300c44431300c4c034140545015141000421a08868230a08c4c031301000331300c4c030a08868221301000305040141040008c4c031301000331300c4c040008141005040928230b00c2c034300525034300928214940908234300c2c030b00868230b00c2c031300464431300868211910848231300c2c030b01000a14940525034140c2c030b01000a30b00c2c034140525014940c28204840c28240028c2c030b00c28230b00c2c040010121004841000a04840121040000c2c030b01000a30b00c2c040000121004840170730700c1c034300515034300170714540515034300c1c030701000630700c1c031300454431301000611510454431300c1c030701000630700c1c030b00838230b01000620e08838230b00c1c030701000614540515034140c1c030701000630700c1c034140515014541000420e08838230a08c1c030701000630700c1c030a08838220e09000604440111040004c1c030701000630700c1c040004111004441000440010901034141000e34141000430a08c282400110004241410004400384707 (by decide +kernel)

def state215_108 : List Sig := [0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc,input 6,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_108 : Impossible true (goalAt 215) 6 state215_108.toFinset :=
  node_ok cuts215 [⟨state215_68,exclude215_68⟩] 0x34140544434140c44434300d0c034140d0c034300c44415110544440028908224208c28234300d0c080000d0c034300c28224208908215110c4c031300d0c015140d0c015110545015140d0c031300c4c031110545015140d05031300c4c031110c4c031300d05015140545011c1c848221208c28231300c4c011c1cc4c031300c28221208848205c1cc1c030700d0c014540d0c005c1c515014540d0c030700c1c040020c1c030700c4c011510c4c040020454411510c4c030700c1c02141c515014540d05030700c1c02141cc1c030700d05014540515011c1c838220e08c28230700c1c011c1cc1c030700c28220e08838240020c1c030700c2c020e08c2c040020838220e08c2c030700c1c034140470734140850730a08c28234140c28230a08850711c1c428024208c2c030b00d0c014940d0c024208525024208d0c030b00c2c021208c2c030b00c4c011910c4c021208464421208c4c030b00c2c02141c525014940d05030b00c2c02141cc2c030b00d05014940525030a08121030a08450530b00c2c030a08c2c030b004505048401250 (by decide +kernel)

def state215_109 : List Sig := [0xffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_109 : Impossible true (goalAt 215) 6 state215_109.toFinset :=
  node_ok cuts215 [⟨state215_21,exclude215_21⟩] 0x545031300c4c015140868231300c4c021a08c4c024a08545031300c4c021a08868231300c2c031300848230b00525030b00c2c014940121030b00c2c004940c2c024200908230b00c2c014940525030b00c1c031300454430700c1c030b00838230700515030700c1c014540838230700c1c020e08c1c024a08515030700c1c020e08838230700d05024040905024140d05024a08928231110928234a0a000024a08d0c034140c44434140c44440010470730a08c282 (by decide +kernel)

def state215_110 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_110 : Impossible true (goalAt 215) 7 state215_110.toFinset :=
  node_ok cuts215 [⟨state215_69,exclude215_69⟩,⟨state215_108,exclude215_108⟩,⟨state215_109,exclude215_109⟩] 0xd05015110d05031110d0c034300d05034300d0c031110544415111000424a08928211c1cd0c034302000034300d0c011c1c928224a08544431300c4c034300545034300544415140545034300c4c031300c44415140545034140c4c031300c44431300c4c034140545015140470721a08868210c0cc4c031300470731300c4c010c0c868221a08928230b00c2c034300525034300928214940908234300c2c030b00868230b00c2c031300464431300868211910848231300c2c030b01000e14940525034140c2c030b01000a30b00c2c034140525014940470704840121011414c2c030b00470730b00c2c011414121004940170730700c1c034300515034300170714540515034300c1c030701000630700c1c031300454431301000611510454431300c1c030701000630700c1c030b00838230b01000620e08838230b00c1c030701000e14540515034140c1c030701000630700c1c034140515014540470720e08838211818c1c030700470730700c1c011818838220e09000440010d01034141000e34141000411c1c470724a09000524a08d0c040038d0c024a0a000224a08d0c040014d0c021a09000221a08c4c040038c4c021a09000321a08c4c040008c4c040039000040000c2c040038c2c040039000a80004c2c040000c2c020e09000120e08c1c040038c1c020e09000620e08c1c040004c1c040011000424041000e40010c282 (by decide +kernel)

def state215_111 : List Sig := roots 215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_111 : Impossible true (goalAt 215) 8 state215_111.toFinset :=
  node_ok cuts215 [⟨state215_33,exclude215_33⟩,⟨state215_37,exclude215_37⟩,⟨state215_43,exclude215_43⟩,⟨state215_53,exclude215_53⟩,⟨state215_57,exclude215_57⟩,⟨state215_60,exclude215_60⟩,⟨state215_71,exclude215_71⟩,⟨state215_73,exclude215_73⟩,⟨state215_79,exclude215_79⟩,⟨state215_91,exclude215_91⟩,⟨state215_102,exclude215_102⟩,⟨state215_105,exclude215_105⟩,⟨state215_107,exclude215_107⟩,⟨state215_110,exclude215_110⟩] 0x80034d05011c1cd05040010901030a08c28280030d05030a08c28240010901011c1c90508002cd05015110d05080028c44434300d0c080024d05034300d0c080020c44415110544440012000124a0892828001cc28234300d0c08001a000034300d0c040010c28224a0890c080014c44415140545040008d05031300c4c080010c44431300c4c040008d05015140545040010470721a08868240008c28231300c4c04000c470731300c4c040008c28221a0884c08000c544431300c4c040008d0c015140d0c080008544415140545040008d0c031300c4c040000870714940525040000d05030b00c2c040000870730b00c2c040000d05014940525040000c28204840c28240000450530b00c2c040000c28230b00c2c040000450504840125040000928230b00c2c040000d0c014940d0c040000928214940908240000d0c030b00c2c040000868230b00c2c040000c4c011910c4c040000868211910848240000c4c030b00c2c040004870714540515040004d05030700c1c040004870730700c1c040004d05014540515040004470720e08838240004c28230700c1c040004470730700c1c040004c28220e08838240004170730700c1c040004d0c014540d0c040004170714540515040004d0c030700c1c040005000130700c1c040004c4c011510c4c040005000111510454440004c4c030700c1c040001000030700c1c040000c2c020e08c2c040001000120e08838240000c2c030700c1c0 (by decide +kernel)

theorem lower215 : Claim 215 9 :=
  fromSearch 1092 (by decide +kernel) exclude215_111


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [14, 6]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

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


def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 4, 4, 6, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 4, 4, 6, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
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
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates, smallCircuit.output, witnessMonotone, (by simpa only [witnessSize] using big), witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates, o, noNotReuse fit mono, Nat.le_refl _, correct⟩
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fit g hg
  obtain ⟨k, hk, run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower215 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31723_aux

open PEqualNP.Outside.L_meta_31723_aux in
theorem PEqualNP.Outside.L_meta_31723 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
