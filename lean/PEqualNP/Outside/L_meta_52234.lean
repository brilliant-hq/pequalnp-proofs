import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_52234
open PEqualNP.CircuitLowerBounds

private def chunk (xs : Array Nat) (i : Nat) : Nat := xs[i]?.getD 0
private def B (n : Nat) : BitVec 256 := BitVec.ofNat 256 n

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

abbrev Row := Fin 256
def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
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

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h; exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by funext r; simp [inv]
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
  obtain ⟨v,rfl⟩ := h; obtain ⟨w,rfl⟩ := g; cases op <;> exact ⟨_,rfl⟩
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

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by cases k <;> simp [kept]
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl
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

def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f) = f := by funext r; exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by funext r; exact bit_neg _ _
theorem obs_bin (d : Nat) (a b : Sig) : observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r; simp only [observe,bit_bin,comb]; split_ifs <;> rfl
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by cases k <;> simp [kept]

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
  apply bit_ext; intro r; rw [bit_table,bit_prime,bit_table,bit_table]; cases d <;> rfl
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
def inputs : List Sig := [BitVec.ofNat 256 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,BitVec.ofNat 256 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,BitVec.ofNat 256 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,BitVec.ofNat 256 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,BitVec.ofNat 256 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,BitVec.ofNat 256 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,BitVec.ofNat 256 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,BitVec.ofNat 256 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def graph : Sig := BitVec.ofNat 256 0xfffffffffffffffefffffffffffefffaffffffeeffffffeefffeffeefefeaa00
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) : bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) : observe (rename f a) = restrictRows f (observe a) := by
  funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext; intro r; simp only [bit_rename,bit_bin]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) : Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he; exact he
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
      intro hm; obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

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
    ext a; rw [List.mem_toFinset]
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

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) : mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]; omega

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
    intro a hs; obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he; subst b
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
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]; exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _; rw [sz]; omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

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
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
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
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (s : BitVec n × BitVec n) : BitVec n := s.1 ^^^ s.2
def covered {n} (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column (sig a) ||| covered sig ws
theorem covered_bit {n : Nat} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) : covered sig ws = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  let i : Fin n := ⟨j,hj⟩
  have yes := (correct.1 i).1; have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
  refine ⟨a,List.mem_toFinset.mp ha,?_⟩
  simp only [column,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
  cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all

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
    (eq : masked d a = masked d b) : restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,Bool.and_true] using he

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
      funext r; simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by simpa [allowedB,allowed] using h
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
  · rw [choiceVal,obs_bin,restrict_comb,e]; exact Or.inl (by simp)
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
theorem bit_mux (r : Row) (m a b : Sig) : bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) : bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
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
  · intro r; rw [←bit_moved,all,bit_one]
  · intro a ha; rw [←observe_rename]; exact supp a ha
  · rw [obs]; exact observe_proper properG
  · rw [obs]; exact hL

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
  simp only [checkEssential,Bool.and_eq_true] at ok; exact ok.1
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
  · rw [h]; exact ⟨false,funext bit_zero⟩
  · rw [h]; exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) |||
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) |||
  (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) |||
  (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7)

def subcube (z o : Nat) : Sig :=
  (List.range 8).foldl (fun acc j =>
    let x := inputs.getD j zero
    if z.testBit j then acc &&& ~~~x
    else if o.testBit j then acc &&& x
    else acc) one
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 256 0,Fin.ofNat 256 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (vars m) (graphGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
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
  (properB (graphGoal old) && plainWord (graphGoal old) && (vars old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (vars rep) (graphGoal rep) L) : Lower u (vars old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (vars q) (graphGoal q) (boundsBefore entries q) := by
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
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs⟩

theorem validPoolCut_sound {u raw T c cap ws} (valid : ValidPool u raw T c)
    (nd : ws.Nodup) (cut : poolCut u c.domain c.bound cap c.paid c.wires ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs⟩ := valid
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hp coveredS lo
  have massLo := count_constants dom ws
  omega

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
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs⟩ := valid
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
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut; exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut; exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c; exact build_valid slice cs he

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
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]; unfold bv; split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx; change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]; simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]; simp
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
    apply ih; intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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
theorem input_coords : ∀ (j : Fin 8) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r; fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 8) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 8 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) : j<8 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next => cases hh; exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) : ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) |||
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) |||
  (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) |||
  (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 8) :
    bit (asRow v i) (vertex m j.val) = ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<8) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]

abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z), (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (column a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [addCov,BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm {l r : List Decor} (h : l.Perm r) : coverage l=coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage v).1 = covered (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column a.2 ||| (coverage v).1) = column (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) := if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) := delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) : ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage (delOne ws a keep)).1 = (if keep then (coverage ws).1 else takeOne (coverage ws) (column a.2)) := by
  cases keep
  · change (coverage (ws.erase a)).1 = takeOne (coverage ws) _
    rw [cov_perm (delOne_perm a ha)]; exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage ws).1 else takeOne (coverage ws) (column b.2))
       else if kb then takeOne (coverage ws) (column a.2)
       else takeTwo (coverage ws) (column a.2) (column b.2)) := by
  cases ka <;> cases kb
  · change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm (delTwo_perm a b ha hb ne)]; exact (cov_two _ _ _).symm
  · exact cover_one a ha false
  · exact cover_one b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut true p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool true raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible true T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible true T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev NodeContext := Nat × Nat × List Decor × Cov × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let rs := restCov cov (column a.2) (column b.2) ka kb
    if (rs ||| column z.2) != BitVec.allOnes 256 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool true raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible true T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,coverage ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible true T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
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
  have g : (coverage rest).1 = covered (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage rest).1 = restCov (coverage ws) (column a.2) (column b.2) ka kb :=
    cover_two a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column (pairSig r s z.1) ||| covered (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage ws) (column a.2) (column b.2) ka kb ||| column z.2) != BitVec.allOnes 256) = false := by
    simpa using sep
  change (if (restCov (coverage ws) (column a.2) (column b.2) ka kb ||| column z.2) != BitVec.allOnes 256 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  if !properB z.1 || ctx.2.2.1.any (fun v => v.1==z.1) then true else
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def ops4 : List Nat := [0,1,2,3]
theorem ops4_mem {d} (h : allowed true d) : d ∈ ops4 := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [ops4]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => ops4.all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed true d → testPair ctx a b d=true) ∨
      (∀ d, allowed true d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (ops4_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (ops4_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true)
    (pro : proper (dbin d a b).1) (fresh : (dbin d a b).1 ∉ ctx.2.2.1.map Prod.fst) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  have pp : properB (dbin d a b).1 = true := by simpa [properB,proper] using pro
  have fr : ctx.2.2.1.any (fun v => v.1==(dbin d a b).1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  simp only [testPair,pp,fr,Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
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
    (moveFront ws d a b ka kb).toFinset = (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed true d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]; tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool true raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible true T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,coverage ws,pools,links) ws = true) :
    Impossible true T cap (ws.map Prod.fst).toFinset := by
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
      (test : testPair (cap,ws.length,ws,coverage ws,pools,links) a b d = true) :
      Impossible true T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test pr fr ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j<8
  · let i : Fin 8 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by rw [← input_list]; exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 256 ≤ 2^j := by change 2^8 ≤ 2^j; exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) : movedRow q (movedRow p r) = r := by
  apply agree_inputs; intro a ha; rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha); rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible true T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible true T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a; simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run; exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,1,1,fun _ => 0)
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
  if (word >>> (iw+pw)) == h/(nb*slots) % 15 + 1 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : liftGoal m p = BitVec.allOnes 256) (hq : liftGoal m q = 0) :
    properPairs (graphGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [bit_liftGoal,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]; simp

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive; split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,data) := g.levels k
  let len := 10*depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let ops := recp &&& ((1 <<< len)-1)
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
    materialize true (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice true (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool true (vars g.mask) (graphGoal g.mask) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    exact materialize_sound (cols ci (List.mem_of_getElem? e)) h

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,ow,data) := tab
  let start := num*(10*d+raw+d)
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  getPairs data cw d (packedAt data pos 6) (pos+6)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (graphGoal g.mask) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible true (graphGoal g.mask) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible true (graphGoal g.mask) k out.toFinset := by
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

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (_,depth,_,_,_) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,coverage ws,rules,ls)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

def nodeVerified (g : Forest) (k i : Nat) :=
  let c := contextOf g k i
  prelim (graphGoal g.mask) c &&
    (if k=0 then true else
      c.2.2.2.2.1.any (fun p => poolCut true p.domain p.bound k p.paid p.wires (c.2.2.1.map Prod.fst)) ||
      testAll c c.2.2.1)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (graphGoal g.mask) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice true (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (graphGoal g.mask) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible true (graphGoal g.mask) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible true (graphGoal g.mask) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,contextOf,prelim,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : graphGoal g.mask ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k; intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have h2 := checked.2
  simp only [h0,ite_false,Bool.or_eq_true,List.any_eq_true] at h2
  have pValid : ∀ p ∈ (forestHints (g.levels k) (wiresOf g).length i).filterMap
      (fun (a,b) => buildRule g (readNode g k i).1 (g.levels k).2.1 (readNode g k i).2.1 a b),
      ValidPool true (vars g.mask) (graphGoal g.mask) p := by
    intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  rcases h2 with ⟨p,hp,hcut⟩ | htest
  · exact validPoolCut_sound (pValid p hp) hN hcut
  · apply node_sound (raw:=vars g.mask) samples _ hN hT pValid _ htest
    · intro v hv
      apply decode_faithful _ _ _ _ _ (wires_faithful g) v
      exact (selectLive_sub _ _).subset hv
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
    simp only [block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def lanePlace (v : Nat) (upper : Nat) := 2^257*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^257 := lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with | nil => simp [combineLanes] | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 256) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (257*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^257)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 257*(i+1)-257=257*i := by omega
      have ge : ¬257*(i+1)<257 := by omega
      simp only [ge,ite_false,di]; exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 256 = (a==BitVec.allOnes 256) := by
  by_cases h : a=BitVec.allOnes 256
  · subst a; decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^256-1 := by
      intro eq; apply h; apply BitVec.eq_of_toNat_eq; simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^256 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]; exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (257*i) = (f xs[i]==BitVec.allOnes 256) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^257*u+x+(2^257*v+1)=2^257*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^257 from by have := (f a).isLt; omega)]
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬256+257*(i+1)<257 := by omega
      have di : 256+257*(i+1)-257=256+257*i := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]; exact ih i (Nat.lt_of_succ_lt_succ hi)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,combineLanes (fun x => (c x).2.2) xs)
def packedColumn (a : PackedSig) := a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) :
    packedColumn (packedSig s xs) = combineLanes (fun x => column (s x)) xs := by
  simp only [packedColumn,packedSig,column,lanes_xor]
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
  if ka then (if kb then c.1 else without1 b) else if kb then without1 a else without2
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
def combField (c : NodeContext) (ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1 (column a.2) (column b.2) ka kb ||| column (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 257) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (257*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 257) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext; intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) := if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤ (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]; omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]; rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (anyEq (Nat.xor d m) pm)
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]; exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]; rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (d a : Sig) (pool : List Sig) :
    navail d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB true d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]; exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant,Bool.true_and]
def unav (p : BoundPool) (w : Decor) : Nat := cond (availableB true p.domain p.wires w.1) 0 1
def slowCost (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav p)).sum == cond ka 0 (unav p a) + cond kb 0 (unav p b)) &&
    decide (k+p.paid+(!availableB true p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB true p.domain p.wires z || (availableB true p.domain p.wires a.1 && availableB true p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]; unfold zN
  by_cases h0 : op=0
  · subst h0; change Nat.land _ _ = _; rw [tn]; congr 1; apply bit_ext; intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1; change Nat.lor _ _ = _; rw [tor]; congr 1; apply bit_ext; intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2; change Nat.xor _ (Nat.land _ _) = _; rw [tn,tx]; congr 1; apply bit_ext; intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]; change Nat.xor _ (Nat.land _ _) = _; rw [tn,tx]; congr 1; apply bit_ext; intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]; cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat
noncomputable def quickSpec (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d))
noncomputable def forcePool {β : Type} (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail d pm m) 0 1).sum fun v => f (d,c,l,t,v,ms,pm)
theorem forcePool_eq {β : Type} (k ws p) (f : QS → β) : forcePool k ws p f = f (quickSpec k ws p) := by
  simp only [forcePool,force_eq,forceMap_eq]; rfl
noncomputable def forcePools {β : Type} (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (k ws ps) (f : List QS → β) : forcePools k ws ps f = f (ps.map (quickSpec k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool k ws p (fun q => forcePools k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]; rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,c.2.2.2.2.1.map (quickSpec (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,qs,ws,t)::ys)) = _
    rw [force_eq,forceMap_eq,force_eq,forcePools_eq,ih]; rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.1 s.2.2.2.2.2.2
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with | none => exact hd.symm | some v => rfl
theorem fast_slow {k p ws i j op ka kb} (h : fastCost (quickSpec k ws p) i j op ka kb=true) :
    slowCost p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by simp [nmask,zero]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav p)).sum := by
    rw [List.map_map]; refine congrArg List.sum (List.map_congr_left ?_); intro w _
    change cond (navail p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]; rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav p)).sum (Nat.add (cond ka 0 (cond ((navail p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB true p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc; simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢; exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB true p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2; simp only [h2,Bool.cond_true,Bool.cond_false] at h
        subst h; rw [ca rfl]; simp <;> omega
    · rw [h1] at h; have l1 := Nat.ble_eq.mp h1
      simp only [Bool.cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first | (have : (!q).toNat ≤ 1 := Bool.toNat_le _; omega) | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih => change or (Nat.beq m a) (anyEq m l)=true ↔ _; rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.1.getD i 0) fun x => force (l.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq; rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha; have e2 := er hb; have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,Bool.cond_true,Bool.cond_false] <;> omega
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB true op=true)
    (h : slowCost p ws k a b op ka kb=true) :
    scalarPoolCut true p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB true p.domain p.wires)=true := by
    apply List.all_eq_true.mpr; intro _ hm; obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB true p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB true p.domain p.wires z) || choiceOK true p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB true p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB true p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by rw [nmask_eq]; congr 1; exact BitVec.and_allOnes
  have := zN_eq op one a b; rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => simp [zero,defaultDecor]
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]; intro e; apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi; have hb := mem j hj
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
    rw [List.map_map]; rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]; rfl
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
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv; exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr; refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv; obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
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
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m; exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_; subst e; simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_; subst e; simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) 4) (not (Nat.beq i j)))))
    (or (l.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) : checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi; have hj := Nat.ble_eq.mp hj; have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi; change Nat.succ j ≤ c.2.2.1.length at hj
    have al : allowedB true op=true := by simp [allowedB]; omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut true p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true := List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]; split_ifs <;> rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]; split_ifs <;> rfl
  · exact h

def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 8)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 128, validSwap v.val=true → ∀ t : Fin 8, swapIdx v.val t.val<8 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<8) : swapIdx v t<8 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<128 := by simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv; omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<8) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]; rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with | none => exact F0.symm | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih => rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]; rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]; split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,data) := g.levels k
  let len := 10*depth
  let width := len+(selected g.mask).length+depth
  force (packedAt data (i*width) width) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by change (movedWord ms zero).toNat=0; rw [moved_eq_rename,(rename_constants _).1]; simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]; apply List.map_congr_left
    rintro ⟨j,a⟩ hm; obtain ⟨hj,rfl⟩ := selected_entry hm; exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,data⟩
  simp only [force_eq,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]; rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))

noncomputable def batchMove (fl : Nat → Option (List Nat)) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn a) (packedColumn b') ka kb ||| packedColumn z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] ka kb op i j != BitVec.allOnes 256 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,combField]; rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn a) (packedColumn b) ka kb |||
        packedColumn (packedOp op a b))) (xs.map laneOf)) = true at pass
    simp only [small,ite_false] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] ka kb op i j = BitVec.allOnes 256
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by rw [mark_at _ _ _ hq]; exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval]; simp only [small,ite_false,bne_iff_ne.mpr hit,ite_true]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => ops4.all (batchPair fl b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl b xs i js && batchRows fl b xs js

theorem batchRows_at {fl} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl (makeBatch k n xs) (xs.map laneOf) js=true) :
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
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    unfold testPair; dsimp only
    split
    · rfl
    · simp only [Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity nd hfl pass.1.1.1,check hi hj' hq budget arity nd hfl pass.1.1.2⟩,
        check hi hj' hq budget arity nd hfl pass.1.2⟩,check hi hj' hq budget arity nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2; simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

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
          simp only [hv,Bool.cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [block,Bool.and_eq_true]; exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) := ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (graphGoal g.mask) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr; intro j hj; have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch; rw [List.range_eq_range']; exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock; intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr; exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2; simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p; rw [e]; exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]; exact fun tag ys h => flOf_ok g k i tag ys h
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  unfold nodeVerified; rw [Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · have ht : testAll (contextOf g k i) (contextOf g k i).2.2.1 = true := by
      simpa only [e] using runBatch_at hq hb ha nd hfl hn (cutsRun h)
    rw [ht,Bool.or_true]
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih => have v := rowCut_merge (ih h.1) (ih h.2); simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih => have v := block_merge (ih h.1) (ih h.2); simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def checkedTables (g : Forest) (top : Nat) := ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (liftGoal g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
  (liftGoal g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (graphGoal g.mask) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower true (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible true (graphGoal g.mask) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower true (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible true (graphGoal g.mask) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower true (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (graphGoal g.mask) = true)
    (ess : checkEssential (graphGoal g.mask) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower true (vars g.mask) (graphGoal g.mask) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_self {m cap hints : Nat} {prior : Nat → Nat} (c : ColumnInfo)
    (low : ∀ q, Lower true (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true)
    (hp : properB (graphGoal m) = true)
    (ess : checkEssential (graphGoal m) (vars m) (graphPairs m hints) = true)
    (all : (graphPairs m hints).map Prod.fst = vars m)
    (nd : (vars m).Nodup)
    (cut : poolCut true (subcube c.1 c.2.1) c.2.2.2.2 cap 0 (vars m) (vars m) = true) :
    Lower true (vars m) (graphGoal m) (cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2
  · intro a ha; apply essential_ok ess a; rw [all]; exact List.mem_toFinset.mpr ha
  · exact validPoolCut_sound (build_valid (col_sound c prior low ok) [] rfl) nd cut

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower true (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {old L m carries} (previous : Known old)
    (main : Lower true (vars m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]

def g41Y : Array (Bits × Bits) := #[(B 0xfcf,B 0x124a),(0,0),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1f3,B 0x24a1),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3c,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc914),(0,0),(0,0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[80,48],[48,80],[80]]
def g41D3 : Nat → Nat := chunk #[0x7]
def g41L : Nat → Packing
  | 3 => (1,0,1,3,g41D3)
  | _ => emptyPacking
def g41I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def g41 : Forest := ⟨41,3,fun i => (g41Y[i]?).getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41P3_0
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low41 : Lower true (vars 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(81,[101,67]),(82,[101,67,16]),(137,[117,101]),(161,[117,83,99,67]),(168,[117,83,99,48,64,32,16])]
set_option maxHeartbeats 0 in
theorem V41 : Known K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(B 0x3f33f,B 0x4912a),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0dcc,B 0xdb98c),(0,0),(B 0x7e0f,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6e05),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8ff0,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24650),(0,0),(0,0),(0,0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[49,64]]
def g27D3 : Nat → Nat := chunk #[0xf]
def g27L : Nat → Packing
  | 3 => (1,0,1,3,g27D3)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def g27 : Forest := ⟨27,3,fun i => (g27Y[i]?).getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27P3_0
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low27 : Lower true (vars 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(29,[33]),(53,[83,33]),(54,[83,16,32]),(58,[67,49,81,16,32]),(92,[96,16,81,32]),(120,[67,65,48,96,81,32]),(147,[115,99,83]),(150,[115,99,83,32]),(156,[116,100,67,49,81,32]),(166,[112,64,100,80,48,32]),(178,[113,65,67,99,81,16,32]),(180,[116,67,99,81,32]),(195,[115,100,83]),(197,[67,115,100,83,33]),(202,[115,100,48,80,32]),(204,[67,115,100,48,16,81,32]),(212,[49,113,99,81,32]),(216,[67,116,65,48,96,81,32])]
set_option maxHeartbeats 0 in
theorem V27 : Known K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low43 : Lower true (vars 43) (graphGoal 43) 5 := lower_self (m:=43) (cap:=4) (hints:=83) (2,0,41,0,4) (before_sound K27 V27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K27 5 [(43,[]),(57,[48,65,33,80]),(75,[101]),(85,[99,83,67,33]),(86,[99,83,67,16,32]),(90,[101,49,65,16,32]),(113,[16,99,65,33,80]),(114,[99,64,81,32]),(141,[117,101,33]),(153,[115,99,48,65,33,80]),(163,[115,99,67]),(165,[117,83,99,67,33]),(177,[115,99,65,33,80]),(209,[113,16,99,65,33,80]),(225,[49,113,99,65,33,80]),(232,[49,48,113,83,96,65,32])]
set_option maxHeartbeats 0 in
theorem V43 : Known K43 := extend_ok (m:=43) V27 low43 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low83 : Lower true (vars 83) (graphGoal 83) 5 := lower_self (m:=83) (cap:=4) (hints:=68) (1,0,82,0,4) (before_sound K43 V43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K43 5 [(83,[]),(89,[16,49,33,64]),(105,[80,97,49,33,64]),(201,[16,112,80,97,49,33,64])]
set_option maxHeartbeats 0 in
theorem V83 : Known K83 := extend_ok (m:=83) V43 low83 (by decide +kernel)
def g169Y : Array (Bits × Bits) := #[(B 0xf0ff0cf,B 0x11111108a),(0,0),(0,0),(B 0xf0f0f333,B 0x222222221),(0,0),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff0c3c,B 0x444444814),(0,0),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000fc0,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff888888540)]
def g169C : List ColumnInfo := [(1,0,168,0,4),(8,0,161,0,4),(128,0,41,0,4),(32,0,137,0,4)]
def g169A : List (List Nat) := [[],[117],[83],[115,83],[83,115],[115],[48],[117,48],[80,48],[112,80,48],[80,112,48],[112,48],[48,80],[115,48,80],[80],[112,80],[115,80],[48,115,80],[83,48,112],[48,112],[80,112],[112],[48,83,112],[83,112]]
def g169D3 : Nat → Nat := chunk #[0x20080303c242902211e3549110]
def g169D4 : Nat → Nat := chunk #[0x188401030503e48110be24442f49110]
def g169H4 : Nat → Nat := chunk #[0xa0700000000008]
def g169D5 : Nat → Nat := chunk #[0x1a20407d10]
def g169H5 : Nat → Nat := chunk #[0x405c020000030633ce08006840000010071a32400]
def g169D6 : Nat → Nat := chunk #[0x2d040f]
def g169H6 : Nat → Nat := chunk #[0xe68003000000320519d8002c41000]
def g169L : Nat → Packing
  | 3 => (2,3,2,5,g169D3)
  | 4 => (3,2,2,5,g169D4)
  | 5 => (1,1,2,5,g169D5)
  | 6 => (1,0,2,4,g169D6)
  | _ => emptyPacking
def g169I : Nat → Nat → Option (Nat × Nat)
  | 4,h => lookupWord 2 5 3 10 1 5 g169H4 h
  | 5,h => lookupWord 5 13 4 11 2 5 g169H5 h
  | 6,h => lookupWord 4 11 4 10 1 5 g169H6 h
  | _,_ => none
def g169 : Forest := ⟨169,6,fun i => (g169Y[i]?).getD (0,0),g169C,g169A,g169L,g169I⟩
set_option maxHeartbeats 0 in
theorem g169P3_0 : block g169 3 0 2 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g169P4_0 : block g169 4 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g169P5_0 : block g169 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g169P6_0 : block g169 6 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g169T : checkedTables g169 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g169 0 0 0 = true)
  · exact (rfl : block g169 1 0 0 = true)
  · exact (rfl : block g169 2 0 0 = true)
  · exact g169P3_0
  · exact g169P4_0
  · exact g169P5_0
  · exact g169P6_0
set_option maxHeartbeats 0 in
theorem g169G : graphValid g169 (boundsBefore K83) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low169 : Lower true (vars 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K83 V83) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K83 7 [(169,[])]
set_option maxHeartbeats 0 in
theorem V169 : Known K169 := extend_ok (m:=169) V83 low169 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 5 := lower_self (m:=31) (cap:=4) (hints:=1091) (2,0,29,0,4) (before_sound K169 V169) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K169 5 [(31,[])]
set_option maxHeartbeats 0 in
theorem V31 : Known K31 := extend_ok (m:=31) V169 low31 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := lower_self (m:=55) (cap:=4) (hints:=1092) (1,0,54,0,4) (before_sound K31 V31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K31 5 [(55,[]),(151,[117,101,33])]
set_option maxHeartbeats 0 in
theorem V55 : Known K55 := extend_ok (m:=55) V31 low55 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low59 : Lower true (vars 59) (graphGoal 59) 6 := lower_self (m:=59) (cap:=5) (hints:=67) (2,0,57,0,5) (before_sound K55 V55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 6 [(59,[]),(122,[84,67,49,97,16,32]),(157,[117,101,33]),(179,[115,99]),(181,[117,83,99,33]),(213,[116,84,99,33]),(227,[67,116,99]),(234,[67,116,48,96,32])]
set_option maxHeartbeats 0 in
theorem V59 : Known K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[(B 0x1f07fe10f33f,B 0x21084200a12a),(0,0),(B 0xf8006ccdcc,B 0x16b5ad64cc98c),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffe0003f8f0e0f,B 0xc6318d0a0e05),(B 0xffc1f00ff0,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffe94a529b00650),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff0001fff000,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffff18c630f55000),(0,0),(0,0)]
def g61C : List ColumnInfo := [(32,0,29,0,4),(0,4,41,16,5),(4,0,57,0,5),(8,0,53,0,4),(16,4,41,0,4)]
def g61A : List (List Nat) := [[],[83]]
def g61D4 : Nat → Nat := chunk #[0x4f91520]
def g61D5 : Nat → Nat := chunk #[0x304c843005c280fd42fe20fd20]
def g61H5 : Nat → Nat := chunk #[0xa0000000]
def g61D6 : Nat → Nat := chunk #[0x41c101f]
def g61H6 : Nat → Nat := chunk #[0x2280c43000001200690000]
def g61L : Nat → Packing
  | 4 => (1,2,3,3,g61D4)
  | 5 => (3,1,3,6,g61D5)
  | 6 => (1,0,3,5,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 1 5 3 6 1 1 g61H5 h
  | 6,h => lookupWord 4 11 4 7 2 1 g61H6 h
  | _,_ => none
def g61 : Forest := ⟨61,6,fun i => (g61Y[i]?).getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61P4_0
  · exact g61P5_0
  · exact g61P6_0
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low61 : Lower true (vars 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[]),(155,[117,101,33]),(186,[117,80,32,98,64,16]),(188,[112,66,96,16]),(214,[82,117,32,96,66,48,16]),(218,[32,112,80,64,98,48,16]),(242,[82,84,67,115,98,16]),(248,[84,83,66,48,114,96,16])]
set_option maxHeartbeats 0 in
theorem V61 : Known K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low62 : Lower true (vars 62) (graphGoal 62) 5 := lower_self (m:=62) (cap:=4) (hints:=1135680) (4,0,58,0,4) (before_sound K61 V61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 5 [(62,[]),(124,[83,97]),(158,[117,101,33]),(199,[117,100,48,32,16]),(206,[117,100,49,33]),(244,[83,115,33,97])]
set_option maxHeartbeats 0 in
theorem V62 : Known K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low87 : Lower true (vars 87) (graphGoal 87) 6 := lower_self (m:=87) (cap:=5) (hints:=1092) (1,0,86,0,5) (before_sound K62 V62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K62 6 [(87,[])]
set_option maxHeartbeats 0 in
theorem V87 : Known K87 := extend_ok (m:=87) V62 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[(B 0x787f81333f,B 0x88888881212a),(B 0x7878009cdcc,B 0x199999989898c),(0,0),(B 0x780007ce0e0f,B 0x33333334c0e05),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffff8007f8700ff0,B 0x2222222600650),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff8007ff000,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffc444444125000),(0,0)]
def g91C : List ColumnInfo := [(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,5),(16,0,75,0,5)]
def g91A : List (List Nat) := [[],[49,64]]
def g91D6 : Nat → Nat := chunk #[0x4e081f]
def g91L : Nat → Packing
  | 6 => (1,0,2,4,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def g91 : Forest := ⟨91,6,fun i => (g91Y[i]?).getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact (rfl : block g91 5 0 0 = true)
  · exact g91P6_0
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low91 : Lower true (vars 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[]),(121,[67,65,48,81,33,96]),(217,[67,116,65,48,81,33,96])]
set_option maxHeartbeats 0 in
theorem V91 : Known K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[(B 0xf0ff00f33f,B 0x11111100a12a),(0,0),(B 0xf004ccdcc,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffbbbbbb4cc98c),(B 0xf000f8f0e0f,B 0x6666668a0e05),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00ff0f00ff0,B 0x444444a00650),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff000fff000,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffff888888555000),(0,0)]
def g93C : List ColumnInfo := [(0,4,73,16,5),(4,0,89,0,5),(8,0,85,0,5),(1,0,92,0,4),(16,4,73,0,4),(64,0,29,0,4)]
def g93A : List (List Nat) := [[],[96]]
def g93D4 : Nat → Nat := chunk #[0x5b89540]
def g93D5 : Nat → Nat := chunk #[0x1908080fd40]
def g93H5 : Nat → Nat := chunk #[0x2000000]
def g93D6 : Nat → Nat := chunk #[0x5654141f]
def g93H6 : Nat → Nat := chunk #[0x4000000]
def g93L : Nat → Packing
  | 4 => (1,2,3,3,g93D4)
  | 5 => (1,1,3,5,g93D5)
  | 6 => (1,0,3,5,g93D6)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 1 5 3 6 1 1 g93H5 h
  | 6,h => lookupWord 1 5 3 6 1 1 g93H6 h
  | _,_ => none
def g93 : Forest := ⟨93,6,fun i => (g93Y[i]?).getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxHeartbeats 0 in
theorem g93P4_0 : block g93 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact g93P4_0
  · exact g93P5_0
  · exact g93P6_0
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low93 : Lower true (vars 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=1027) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 7 [(93,[]),(203,[67,116,84,99,33]),(205,[116,84,99]),(211,[114,82,33,49,64])]
set_option maxHeartbeats 0 in
theorem V93 : Known K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low94 : Lower true (vars 94) (graphGoal 94) 6 := lower_self (m:=94) (cap:=5) (hints:=16868416) (4,0,90,0,5) (before_sound K93 V93) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K93 6 [(94,[]),(117,[97,82,50,16,64]),(118,[97,82,50,65]),(167,[118,84,48,32,16]),(174,[118,84,49,33]),(229,[98,33,113,82,50,16,64]),(236,[116,99,81])]
set_option maxHeartbeats 0 in
theorem V94 : Known K94 := extend_ok (m:=94) V93 low94 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low107 : Lower true (vars 107) (graphGoal 107) 6 := lower_self (m:=107) (cap:=5) (hints:=83) (2,0,105,0,5) (before_sound K94 V94) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K94 6 [(107,[]),(115,[49,48,67,97,80])]
set_option maxHeartbeats 0 in
theorem V107 : Known K107 := extend_ok (m:=107) V94 low107 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low171 : Lower true (vars 171) (graphGoal 171) 8 := lower_self (m:=171) (cap:=7) (hints:=83) (2,0,169,0,7) (before_sound K107 V107) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K107 8 [(171,[]),(173,[117,33]),(185,[48,65,33,80])]
set_option maxHeartbeats 0 in
theorem V171 : Known K171 := extend_ok (m:=171) V107 low171 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0,0),(B 0xf83e23c3f3,B 0x1294a5222c152),(B 0x1f07c044fd9c,B 0x6318c640a998),(0,0),(B 0x7ff870e1f,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffe94a529850605),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffe0f801f80fe0,B 0xc6318d500ea0),(0,0),(B 0xffffffffffffffffffffffffffffffffffffffffffffffffffffff0001fff000,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffff18c630af5000)]
def g182C : List ColumnInfo := [(16,0,166,0,4),(2,0,180,0,4),(4,0,178,0,4),(32,0,150,0,4),(128,0,54,0,4)]
def g182A : List (List Nat) := [[],[84,114],[117,33],[65,116,81,33],[82,65],[81,33,114,65],[116,81],[114,33,66,81],[66,84,33,113],[66,113]]
def g182D4 : Nat → Nat := chunk #[0x5b89510]
def g182D5 : Nat → Nat := chunk #[0x540fd20fd10]
def g182H5 : Nat → Nat := chunk #[0x40000]
def g182D6 : Nat → Nat := chunk #[0x4611141f]
def g182H6 : Nat → Nat := chunk #[0x638013100003d12500788002300001d9810000241c70000000000]
def g182L : Nat → Packing
  | 4 => (1,2,3,3,g182D4)
  | 5 => (2,1,3,5,g182D5)
  | 6 => (1,0,3,5,g182D6)
  | _ => emptyPacking
def g182I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 1 5 3 9 1 4 g182H5 h
  | 6,h => lookupWord 8 19 5 9 1 4 g182H6 h
  | _,_ => none
def g182 : Forest := ⟨182,6,fun i => (g182Y[i]?).getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxHeartbeats 0 in
theorem g182P4_0 : block g182 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g182P5_0 : block g182 5 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g182P6_0 : block g182 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g182T : checkedTables g182 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g182 0 0 0 = true)
  · exact (rfl : block g182 1 0 0 = true)
  · exact (rfl : block g182 2 0 0 = true)
  · exact (rfl : block g182 3 0 0 = true)
  · exact g182P4_0
  · exact g182P5_0
  · exact g182P6_0
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K171) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low182 : Lower true (vars 182) (graphGoal 182) 7 := lower_forest (g:=g182) (i:=0) (hints:=537986112) (before_sound K171 V171) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K171 7 [(182,[]),(220,[116,100,84,33,49])]
set_option maxHeartbeats 0 in
theorem V182 : Known K182 := extend_ok (m:=182) V171 low182 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low233 : Lower true (vars 233) (graphGoal 233) 8 := lower_self (m:=233) (cap:=7) (hints:=3) (64,0,169,0,7) (before_sound K182 V182) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K182 8 [(233,[])]
set_option maxHeartbeats 0 in
theorem V233 : Known K233 := extend_ok (m:=233) V182 low233 (by decide +kernel)
def g241Y : Array (Bits × Bits) := #[(B 0x1f07fff08727f,B 0x210842100204a),(0,0),(0,0),(0,0),(B 0xf801f364d93,B 0x14a5294a264911),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e0c78e1c,B 0xc6318c6850e14),(B 0xffc00f80fe0,B 0xffffffffffffffffffffffffffffffffffffffffffffffffffe94a5294d806a0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000fff000,B 0xfffffffffffffffffffffffffffffffffffffffffffffffffff18c63187ad000)]
def g241C : List ColumnInfo := [(80,0,161,0,4),(64,0,177,0,5),(128,0,113,0,5),(32,0,209,0,5),(16,0,225,0,5),(160,0,81,0,4)]
def g241A : List (List Nat) := [[],[117],[118,84],[116,100,84],[100],[117,100],[101,84,116],[101,116]]
def g241D4 : Nat → Nat := chunk #[0x25d36015218f919258425e3649510]
def g241D5 : Nat → Nat := chunk #[0x4188220811c4208220840040011c03c58840110c02fc0a90df01521bf12c217d25843ea4288778d510bf12a217d25443ec2a88578d510]
def g241H5 : Nat → Nat := chunk #[0xc8c02a80000000018242000]
def g241D6 : Nat → Nat := chunk #[0x14023200d2000fd21fe10fd10]
def g241H6 : Nat → Nat := chunk #[0x105c006935120010a80070e0000000000000000000608000c341214b00502d0000000000000001021cb603000e0800000000000000004001001000]
def g241D7 : Nat → Nat := chunk #[0x14041f]
def g241H7 : Nat → Nat := chunk #[0x1ecd1a8331c20000002400014801852800648002696800000000]
def g241L : Nat → Packing
  | 4 => (3,3,3,3,g241D4)
  | 5 => (10,2,3,7,g241D5)
  | 6 => (3,1,3,6,g241D6)
  | 7 => (1,0,3,4,g241D7)
  | _ => emptyPacking
def g241I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 3 9 4 9 2 3 g241H5 h
  | 6,h => lookupWord 14 35 6 11 4 3 g241H6 h
  | 7,h => lookupWord 7 19 5 9 2 3 g241H7 h
  | _,_ => none
def g241 : Forest := ⟨241,7,fun i => (g241Y[i]?).getD (0,0),g241C,g241A,g241L,g241I⟩
set_option maxHeartbeats 0 in
theorem g241P4_0 : block g241 4 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g241P5_0 : block g241 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g241P5_1 : block g241 5 1 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g241B5 : block g241 5 0 10 = true := (@block_merge g241 5 0 1 9 g241P5_0 g241P5_1)
set_option maxHeartbeats 0 in
theorem g241P6_0 : block g241 6 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g241P7_0 : block g241 7 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g241T : checkedTables g241 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g241 0 0 0 = true)
  · exact (rfl : block g241 1 0 0 = true)
  · exact (rfl : block g241 2 0 0 = true)
  · exact (rfl : block g241 3 0 0 = true)
  · exact g241P4_0
  · exact g241B5
  · exact g241P6_0
  · exact g241P7_0
set_option maxHeartbeats 0 in
theorem g241G : graphValid g241 (boundsBefore K233) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low241 : Lower true (vars 241) (graphGoal 241) 8 := lower_forest (g:=g241) (i:=0) (hints:=4) (before_sound K233 V233) g241G g241T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K241 := extendKnown K233 8 [(241,[])]
set_option maxHeartbeats 0 in
theorem V241 : Known K241 := extend_ok (m:=241) V233 low241 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := lower_self (m:=63) (cap:=7) (hints:=1091) (2,0,61,0,7) (before_sound K241 V241) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K241 8 [(63,[]),(159,[117,101,33])]
set_option maxHeartbeats 0 in
theorem V63 : Known K63 := extend_ok (m:=63) V241 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[(B 0xf00ff002730693ff,B 0x11111111002520292aa),(B 0xf00f000939c9b1ccc,B 0x33333333093189318cc),(B 0xf0004e3e0e3e0f0,B 0xfffffffffffffffffffffffffffffffffffffffffffffbbbbbbbb4e3e0c3c0f0),(B 0xf00000f8fc00fc00ff,B 0x666666668d800fc0055),(B 0xffffffffffffffffffffffffffffffffffffffffffffff000fff0f0000ffff00,B 0x44444444a00002c2500),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffffffffff0000fffff000000,B 0xfffffffffffffffffffffffffffffffffffffffffffff88888888524a5000000),(0,0)]
def g95C : List ColumnInfo := [(8,0,87,0,6),(6,0,89,0,5),(4,0,91,0,7),(3,0,92,0,4),(2,0,93,0,7),(16,4,75,0,5),(5,0,90,0,5),(9,0,86,0,5),(2,4,73,16,5),(0,4,75,16,6),(1,0,94,0,6),(12,0,83,0,5),(18,0,73,0,4),(66,0,29,0,4),(64,0,31,0,5),(68,0,27,0,4)]
def g95A : List (List Nat) := [[]]
def g95D4 : Nat → Nat := chunk #[0x10040000000000000000018000180085e785585650f455511715943d195441c5650f1655907159438e61859f53d0a394221755b428e61859f42d423986167d09508cd78d0a36542661e143541408e66855f424427896107d0910f115450d50442741e14354110b6158d0950442785e34254110d914395d404436450d5750110d615095d2644319d5a5749910]
def g95D5 : Nat → Nat := chunk #[0x1a41160b9045590ac8200110083068031c30410804401001b002192040831412a0902bc83351a8d46a351a8506a35364d46a351a9b26a351a8d46a351aa286a351a8d514661a8d46a351a8d46a3541df4e66c9a9986a351c0d41b382fcd4bf352c8d4a5529c0e0910d9a8fa703513c84351406c01378dd06d527a83c2caa4f61751b53cbea72b2873d85d5650e7d03aaca1f961755143b3c0eaa2876751f5650f8eaa4aca1e5f5695943b3c8eab2877585d5650eed03aaca1f1d5415943cbaac2b2877545c5650eec838aca1ced67d4f42dcc2eab6853b81d56d0a772ba0da171d5450f50adaafa16a13b59f42d434ea1a8da84f61751b50e3aa8a1aa13719d43542b6abe84a85e907d09509dacfa12a1b354a3654367a146ca84de478d9509ba8f1b2a1b349e36543671b24ca879a0750d40e72a8a8281e650d505034ea1caca069d43559409bc6eab2813d85d56502f883ea8884f66755110f2aa8a1a21f481d43442f333aa4885e557d0910bcacfa1221dcd5150443b8aa2a0887d14354110fc2a4a8221f8d0950442f923aa0887d23754110fc24ea8221ec55140442f92ba80885f15750110be20fab221758dd56443f0a824c886e75649910bccae932213985d56d0af083e84887914350110]
def g95H5 : Nat → Nat := chunk #[0x447d82469c8400e6d41b4e400110030b0981b9c00b065800004a000029e6e9000000004028000]
def g95D6 : Nat → Nat := chunk #[0x26528628012428410a114488108ca412400a1b4ca8908d2890028aca403423290e1928040520d44844881065521525055442867c09064c01121001d590019f38c19428470a11210448810021492a1a4a861b21a419ac8692029892a1e5284065a0a235a1e289a0a135a0a1e95641e80642d42c886552a2c896152a2c9854a881e43861e43aa203386a88ca93b32a870bd0f927684d051114027c8f49dd39c6f0d69a132a660ca98f2b8618bd1712d0570a81472764bc9191a2224207c8ed1c2354618b715c27c480870f61bc2e84b0720a80f00f000bf4db54bf41b54bf8d954fd85954bf81954bf51b53bf91953ef55143f7d4d43f754d43bf95943bf55943f7d5943f795943f755943f715943f781943f741943fb54d52fbd4f42fb54f42df55350f750f50fbd0b50bf51b50dfd5150df55150f750d50fb54950fbd0950bf91950f78d950fb49950ef55140fe54140bf95940bf55940fdd5110fd55110fdd5910fd55910fd51910bd85954e755143bb81952bb55b42bb41b42b78d950e750d40f550d10f954910f9d0910fc54110fc50110f949910]
def g95H6 : Nat → Nat := chunk #[0x1ae0002c51060021b894f7ae70007bc000002848005818e54b53a24104e962b65116b88298e00000151c9720524096800156aec00604f66c780051ab7c86f00a31d4a0000059f41544b8880070e2be5fcb2918e3dda598d1790663000f335089aa27000000a278d52b10c000aa145085d230624c00394429d3b2c000200020c080041010004040001e040030600082020010100000000400401060c400]
def g95D7 : Nat → Nat := chunk #[0x50254714672812a1462d24e38ae2ca8715d2a14e296923b857169238ae950e5165429c404b5428a275e8516f42866a1ca2107591c5c2582832281b918aa6461b49c390f803fea9fd54ffa9ff54ffa87ff50fea87f503bc87dd43f6a97bd0bda41f510]
def g95H7 : Nat → Nat := chunk #[0x20c43e24c6450a75eaab800000014694d8d80000000370000000072800006e00025800722003674ec04000000000000080d0e49c9b31af69e5100000000000000000000409f5800001a000683a1f3836ee4750004b1947a1ed6aed20033e007e393e0a000900000000000004b40015eb061744f29cc9460800000001010208180000000004042810004000041c0000008000]
def g95D8 : Nat → Nat := chunk #[0xae84203f]
def g95H8 : Nat → Nat := chunk #[0x11066ae37da01409274ea0001e2a40000d8e80000006c01880000000]
def g95L : Nat → Packing
  | 4 => (20,4,4,5,g95D4)
  | 5 => (71,3,4,9,g95D5)
  | 6 => (55,2,4,11,g95D6)
  | 7 => (14,1,4,9,g95D7)
  | 8 => (1,0,4,5,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 11 29 5 9 5 0 g95H5 h
  | 6,h => lookupWord 36 91 7 11 7 0 g95H6 h
  | 7,h => lookupWord 31 97 7 10 6 0 g95H7 h
  | 8,h => lookupWord 9 23 5 8 4 0 g95H8 h
  | _,_ => none
def g95 : Forest := ⟨95,8,fun i => (g95Y[i]?).getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 20 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g95P5_3 : block g95 5 3 68 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 71 = true := (@block_merge g95 5 0 3 68 g95P5_0 g95P5_3)
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 42 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 55 = true := (@block_merge g95 6 0 13 42 g95P6_0 g95P6_13)
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g95P7_6 : block g95 7 6 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 14 = true := (@block_merge g95 7 0 6 8 g95P7_0 g95P7_6)
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95P4_0
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95P8_0
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low95 : Lower true (vars 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=1091) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[])]
set_option maxHeartbeats 0 in
theorem V95 : Known K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low119 : Lower true (vars 119) (graphGoal 119) 7 := lower_self (m:=119) (cap:=6) (hints:=1092) (1,0,118,0,6) (before_sound K95 V95) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 7 [(119,[])]
set_option maxHeartbeats 0 in
theorem V119 : Known K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(B 0x7c00f83ff081311333f,B 0x210842108421001201212a),(B 0xf801f07c00109c29cdcc,B 0x6318c6318c63009809898c),(0,0),(B 0x1f003e00001f24e0ce0e0f,B 0xc6318c6318c604c08c0e05),(B 0xffffffffffffffffffffffffffffffffffffffffffe00000007fe0c700f00ff0,B 0x18c6318c6318c8600f00650),(B 0x3fff8000f800fff000,B 0xffffffffffffffffffffffffffffffffffffffffff18c6318c6318f800725000),(B 0xffffffffffffffffffffffffffffffffffffffffffffffc0000000ffff000000,B 0xfffffffffffffffffffffffffffffffffffffffffe1084210842107925000000),(0,0)]
def g123C : List ColumnInfo := [(16,0,107,0,6),(66,0,57,0,5),(18,0,105,0,5),(32,0,91,0,7),(9,0,114,0,5),(80,0,43,0,5),(3,0,120,0,4),(2,0,121,0,7)]
def g123A : List (List Nat) := [[],[67,81,96]]
def g123D5 : Nat → Nat := chunk #[0x680803001cd55156442eb1baac887315454110]
def g123D6 : Nat → Nat := chunk #[0x280840dd6da086d91a23f6868000fd55910fd4d910ed55110fc54110fc4c110]
def g123H6 : Nat → Nat := chunk #[0x4a40000030de001]
def g123D7 : Nat → Nat := chunk #[0x3ed504fb4511db6d0560c0d00fe997f543fa61f510]
def g123H7 : Nat → Nat := chunk #[0x32000000000000a061630014c9000000]
def g123D8 : Nat → Nat := chunk #[0x163e203f]
def g123H8 : Nat → Nat := chunk #[0x1e530000000b4628ad3010]
def g123L : Nat → Packing
  | 5 => (3,3,3,5,g123D5)
  | 6 => (5,2,3,7,g123D6)
  | 7 => (4,1,3,7,g123D7)
  | 8 => (1,0,3,5,g123D8)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 3 9 4 7 2 1 g123H6 h
  | 7,h => lookupWord 6 13 4 8 3 1 g123H7 h
  | 8,h => lookupWord 4 11 4 7 2 1 g123H8 h
  | _,_ => none
def g123 : Forest := ⟨123,8,fun i => (g123Y[i]?).getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g123P5_1 : block g123 5 1 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 3 = true := (@block_merge g123 5 0 1 2 g123P5_0 g123P5_1)
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g123P6_3 : block g123 6 3 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 5 = true := (@block_merge g123 6 0 3 2 g123P6_0 g123P6_3)
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g123P7_1 : block g123 7 1 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 4 = true := (@block_merge g123 7 0 1 3 g123P7_0 g123P7_1)
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123P8_0
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low123 : Lower true (vars 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 9 [(123,[])]
set_option maxHeartbeats 0 in
theorem V123 : Known K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[(B 0x3e0f83ff0601e10f33f,B 0x8421084210001400a12a),(0,0),(B 0x7c00949986ccdcc,B 0xfffffffffffffffffffffffffffffffffffffffffff9ce739ce73949984cc98c),(B 0x7c1f0001f191e18f0e0f,B 0x318c6318c6011410a0e05),(B 0xffffffffffffffffffffffffffffffffffffffffffff800007fe0e1e01f00ff0,B 0x6318c6318c41401b00650),(B 0x1ff8000fe001fff000,B 0xfffffffffffffffffffffffffffffffffffffffffffc6318c6318fe000f55000),(B 0xffffffffffffffffffffffffffffffffffffffffffffffe000000ffffe000000,B 0xfffffffffffffffffffffffffffffffffffffffffff8421084210beaaa000000),(0,0)]
def g125C : List ColumnInfo := [(32,0,93,0,7),(8,0,117,0,6),(4,0,121,0,7),(64,0,61,0,7),(0,4,105,16,6),(1,0,124,0,5),(16,4,105,0,5),(16,0,105,0,5)]
def g125A : List (List Nat) := [[]]
def g125D5 : Nat → Nat := chunk #[0x25f23a4d184f567cc620d6e63232411f95d364825f23a6c905b64748110]
def g125D6 : Nat → Nat := chunk #[0x34821804885a814380200482088310044a023ec2d6c24a5a9b95854a70655a4a30201000bf81932bf49a30f74c930bf89930fdcc620bf4da20fb4c920fdcc520ef91920bf8d920bf4d920fd48110bd41b31af91920]
def g125H6 : Nat → Nat := chunk #[0xa75d400000e06d0800010]
def g125D7 : Nat → Nat := chunk #[0x10c5b28ca3516c33a0c55a8eeb431634c5b88a5316c33a493a291a0f007f4cbfc61fd30ff107f483ee63f510]
def g125H7 : Nat → Nat := chunk #[0x48148936f2c3bd21000000cb00f04ad557bc00000140100040]
def g125D8 : Nat → Nat := chunk #[0xc426283f]
def g125H8 : Nat → Nat := chunk #[0x268035f003b01607790101]
def g125L : Nat → Packing
  | 5 => (6,3,3,3,g125D5)
  | 6 => (14,2,3,8,g125D6)
  | 7 => (7,1,3,8,g125D7)
  | 8 => (1,0,3,5,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 4 11 4 7 3 0 g125H6 h
  | 7,h => lookupWord 8 21 5 8 4 0 g125H7 h
  | 8,h => lookupWord 4 11 4 7 3 0 g125H8 h
  | _,_ => none
def g125 : Forest := ⟨125,8,fun i => (g125Y[i]?).getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g125P6_2 : block g125 6 2 12 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 14 = true := (@block_merge g125 6 0 2 12 g125P6_0 g125P6_2)
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g125P7_2 : block g125 7 2 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 7 = true := (@block_merge g125 7 0 2 5 g125P7_0 g125P7_2)
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g125T : checkedTables g125 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125P5_0
  · exact g125B6
  · exact g125B7
  · exact g125P8_0
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low125 : Lower true (vars 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=1027) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 9 [(125,[])]
set_option maxHeartbeats 0 in
theorem V125 : Known K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low126 : Lower true (vars 126) (graphGoal 126) 7 := lower_self (m:=126) (cap:=6) (hints:=17912896) (4,0,122,0,6) (before_sound K125 V125) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 7 [(126,[]),(231,[101,116,48,16]),(238,[101,116,49])]
set_option maxHeartbeats 0 in
theorem V126 : Known K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low175 : Lower true (vars 175) (graphGoal 175) 9 := lower_self (m:=175) (cap:=8) (hints:=1875) (2,0,173,0,8) (before_sound K126 V126) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 9 [(175,[])]
set_option maxHeartbeats 0 in
theorem V175 : Known K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[(B 0x3e0f801f0064f19ce93,B 0x8421084210024a094a92),(B 0x1f003e011b8c2e731c,B 0x4a5294a5291138c0c6318),(B 0x7c0007c00223f0cf83e0,B 0x18c6318c63203608f83c0),(0,0),(B 0x7fffc3c00f003ff,B 0xfffffffffffffffffffffffffffffffffffffffffffa5294a5294c2c00700025),(B 0xffffffffffffffffffffffffffffffffffffffffffff801ff8000fc000fffc00,B 0x318c6318c6a8000f29400),(0,0),(B 0xffffffffffffffffffffffffffffffffffffffffffffffe000000fffff000000,B 0xfffffffffffffffffffffffffffffffffffffffffffc6318c631857c95000000)]
def g183C : List ColumnInfo := [(32,0,151,0,5),(2,0,181,0,6),(1,0,182,0,7),(4,0,179,0,6),(16,0,167,0,6),(128,0,55,0,5),(33,0,150,0,4),(6,0,177,0,5),(18,0,165,0,5),(130,0,53,0,4),(20,0,163,0,5),(36,0,147,0,4)]
def g183A : List (List Nat) := [[],[117,33]]
def g183D4 : Nat → Nat := chunk #[0xb15181515350ec64205454d43]
def g183D5 : Nat → Nat := chunk #[0x9ec2e9b4a96b49c5450eda8b8a8a1db90715143e38a8a9a878fd525650e7b0baaca1cfa0755943]
def g183H5 : Nat → Nat := chunk #[0x66b200000000]
def g183D6 : Nat → Nat := chunk #[0x4e10031010c20430410010050320c5182c81364836363636366c6c6c786c5448363648363c36361e001e0c000000bf55a54bf4da54bf45a54bf8d954bf85954bf4d854efd5343bf55b43efd5143ef15143f754d43bf95943bf55943fd85943df55351bf51b51df55151bf55b41fd54541bf95941bf55941cfd5254b74d854bd45854be41854bb49b43bd85943b74db51]
def g183H6 : Nat → Nat := chunk #[0x1540051a400029c038c03b982b1451848004000000]
def g183D7 : Nat → Nat := chunk #[0x148192c520c2504861848992c62a24a00a502a481407920a280e8924529e4040a501e481604de5d26cf85d1f07c01fe54feaa7f153fe87fd43ffa8ff547fe83fd41]
def g183H7 : Nat → Nat := chunk #[0xbb40055fd600115d0acfc04802cdf7d344676a6724400f0c007cb0500258dd61216d8c00000000009900000000002ca00000003cefac0000000000d4f1c000004400000002d0001c90000012d13f65880002000018000000008100040060c000000a00000]
def g183D8 : Nat → Nat := chunk #[0x150e4203f]
def g183H8 : Nat → Nat := chunk #[0x88386a563c8980d1250031f4c00c980000009ac8be964007e00000000c000802100000]
def g183L : Nat → Packing
  | 4 => (2,4,4,3,g183D4)
  | 5 => (8,3,4,3,g183D5)
  | 6 => (28,2,4,8,g183D6)
  | 7 => (9,1,4,9,g183D7)
  | 8 => (1,0,4,5,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 2 7 3 6 1 1 g183H5 h
  | 6,h => lookupWord 6 17 5 8 3 1 g183H6 h
  | 7,h => lookupWord 22 65 7 10 5 1 g183H7 h
  | 8,h => lookupWord 11 27 5 9 4 1 g183H8 h
  | _,_ => none
def g183 : Forest := ⟨183,8,fun i => (g183Y[i]?).getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxHeartbeats 0 in
theorem g183P4_0 : block g183 4 0 2 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 8 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 7 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g183P6_7 : block g183 6 7 21 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 28 = true := (@block_merge g183 6 0 7 21 g183P6_0 g183P6_7)
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact g183P4_0
  · exact g183P5_0
  · exact g183B6
  · exact g183P7_0
  · exact g183P8_0
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low183 : Lower true (vars 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1092) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[])]
set_option maxHeartbeats 0 in
theorem V183 : Known K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low187 : Lower true (vars 187) (graphGoal 187) 9 := lower_self (m:=187) (cap:=8) (hints:=67) (2,0,185,0,8) (before_sound K183 V183) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 9 [(187,[]),(189,[117,33])]
set_option maxHeartbeats 0 in
theorem V187 : Known K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0,0),(B 0xfc0fc41d98193e73,B 0x4514514514441598092a52),(B 0xfc003f008261e6e339c,B 0x14514514514806144e3318),(B 0x3f03f000000c7e18fc3e0,B 0xc30c30c30c087410d83e0),(B 0x3fff0f801f003ff,B 0xffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaab0e801b000a5),(B 0xfffffffffffffffffffffffffffffffffffffffffffc003ffc003f0001fffc00,B 0x30c30c30c32a0000f25400),(0,0),(B 0xffffffffffffffffffffffffffffffffffffffffffffffc000003ffffe000000,B 0xffffffffffffffffffffffffffffffffffffffffffc30c30c30c1578aa000000)]
def g190C : List ColumnInfo := [(32,0,158,0,5),(128,0,62,0,5),(8,0,182,0,7),(2,0,188,0,7),(4,0,186,0,7),(0,16,168,6,6),(16,0,174,0,6)]
def g190A : List (List Nat) := [[],[117,33]]
def g190D5 : Nat → Nat := chunk #[0x4ee2755a54]
def g190D6 : Nat → Nat := chunk #[0x102004010018612db2c0bf55a54fb89954cfd5254bb89954bb49854be41854]
def g190H6 : Nat → Nat := chunk #[0x4000000]
def g190D7 : Nat → Nat := chunk #[0x1946f28076510cba1d9472e807888807f953faa9fc54]
def g190H7 : Nat → Nat := chunk #[0xe1940000f57362303800001110]
def g190D8 : Nat → Nat := chunk #[0xd546283f]
def g190H8 : Nat → Nat := chunk #[0x4600849300000000100]
def g190L : Nat → Packing
  | 5 => (1,3,3,3,g190D5)
  | 6 => (6,2,3,6,g190D6)
  | 7 => (3,1,3,7,g190D7)
  | 8 => (1,0,3,5,g190D8)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 1 5 3 6 1 1 g190H6 h
  | 7,h => lookupWord 4 11 4 8 3 1 g190H7 h
  | 8,h => lookupWord 3 9 4 7 2 1 g190H8 h
  | _,_ => none
def g190 : Forest := ⟨190,8,fun i => (g190Y[i]?).getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxHeartbeats 0 in
theorem g190P5_0 : block g190 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g190P6_0 : block g190 6 0 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g190P6_4 : block g190 6 4 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g190B6 : block g190 6 0 6 = true := (@block_merge g190 6 0 4 2 g190P6_0 g190P6_4)
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g190P8_0 : block g190 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g190T : checkedTables g190 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact g190P5_0
  · exact g190B6
  · exact g190P7_0
  · exact g190P8_0
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K187) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low190 : Lower true (vars 190) (graphGoal 190) 9 := lower_forest (g:=g190) (i:=0) (hints:=538006592) (before_sound K187 V187) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K187 9 [(190,[]),(222,[116,100,84,33,49]),(246,[116,99,81]),(252,[83,115,33,97])]
set_option maxHeartbeats 0 in
theorem V190 : Known K190 := extend_ok (m:=190) V187 low190 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low207 : Lower true (vars 207) (graphGoal 207) 8 := lower_self (m:=207) (cap:=7) (hints:=1891) (2,0,205,0,7) (before_sound K190 V190) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 8 [(207,[])]
set_option maxHeartbeats 0 in
theorem V207 : Known K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[(B 0x7c00f801f0232789ce93,B 0x84210842100125094a92),(B 0x1f003e00cdc60e731c,B 0x294a5294a5089c60c6318),(B 0xffffffffffffffffffffffffffffffffffffffffffff800007c00311f84f83e0,B 0x18c6318c63201b04f83c0),(0,0),(B 0x3e007fffc1e007003ff,B 0x421084210881600200025),(0,0),(B 0x3fff8000fe0007ffc00,B 0xfffffffffffffffffffffffffffffffffffffffffff94a5294a5276000529400),(B 0xfffffffffffffffffffffffffffffffffffffffffffffc0000000fffff800000,B 0xfffffffffffffffffffffffffffffffffffffffffffe739ce739cdfe4a800000)]
def g215C : List ColumnInfo := [(2,0,213,0,6),(16,0,199,0,5),(64,0,151,0,5),(65,0,150,0,4),(1,0,214,0,7),(4,0,211,0,7),(0,128,82,5,6),(128,0,87,0,6),(18,0,197,0,4),(130,0,85,0,5)]
def g215A : List (List Nat) := [[]]
def g215D5 : Nat → Nat := chunk #[0x40000000000606775385943ceaa70b2877c41c1650f2ea9c6ca0f9543d0731baa6fa0e63add0546cc7caa1a8298cf61751931]
def g215D6 : Nat → Nat := chunk #[0x1060041802001081080081d03d01d01082d010c10c2a2a26078968460786096786084787860786060786660483c2a1200dfd4f43df54f43bf45b43bf51a43dfd4d43df54d43bf85943fd85943fd05943df54f41ef50f41bf4db41df54d41efd0d41ef50d41bf8d941f750f31fdd0731bf51b31f750d31fd50531bf51931e7d0e43bd85943bb49843bd45843be41843]
def g215H6 : Nat → Nat := chunk #[0xd1b4001200b528000000b6400033b700001]
def g215D7 : Nat → Nat := chunk #[0x730415a08711cd5a206398020d68380e6156881c35a24428835a24511cd5050239cc2056881cc1ad1229d06ad05a2481eece57a40ce3e0f803fe87fe43fea1ff10ffe83fd41ff98ff4c6fea77d53]
def g215H7 : Nat → Nat := chunk #[0x4ac01f2903badf02321a16c7781fb0b4f939e36aa65c38000000003e2e991000018c6920801549000000114c0400001c0000]
def g215D8 : Nat → Nat := chunk #[0xeca8283f]
def g215H8 : Nat → Nat := chunk #[0xc7d00000c600e85375a442001100e9103050]
def g215L : Nat → Packing
  | 5 => (9,3,4,5,g215D5)
  | 6 => (27,2,4,8,g215D6)
  | 7 => (10,1,4,9,g215D7)
  | 8 => (1,0,4,5,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 5 15 4 8 4 0 g215H6 h
  | 7,h => lookupWord 14 37 6 9 5 0 g215H7 h
  | 8,h => lookupWord 6 15 4 8 4 0 g215H8 h
  | _,_ => none
def g215 : Forest := ⟨215,8,fun i => (g215Y[i]?).getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 5 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g215P6_5 : block g215 6 5 22 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 27 = true := (@block_merge g215 6 0 5 22 g215P6_0 g215P6_5)
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g215P7_2 : block g215 7 2 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 10 = true := (@block_merge g215 7 0 2 8 g215P7_0 g215P7_2)
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g215T : checkedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact g215P5_0
  · exact g215B6
  · exact g215B7
  · exact g215P8_0
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low215 : Lower true (vars 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=1092) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[])]
set_option maxHeartbeats 0 in
theorem V215 : Known K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(B 0x3f00003f03ffc108781333f,B 0x4104104104104000501212a),(B 0xfc0fc000636609cdcc,B 0x2cb2cb2cb2cb2c426609898c),(0,0),(B 0xfffffffffffffffffffffffffffffffffffffffffc003f000000fc8c784e0e0f,B 0x1861861861861808504c0e05),(B 0xfc0000fff030f80700ff0,B 0x514514514514520d80600650),(0,0),(B 0xffffff00003f0007ff000,B 0xffffffffffffffffffffffffffffffffffffffff82082082082081b000125000),(B 0xfffffffffffffffffffffffffffffffffffffffffff00000000003ffff800000,B 0xffffffffffffffffffffffffffffffffffffffffe38e38e38e38e3f7aa800000)]
def g219C : List ColumnInfo := [(17,0,202,0,4),(80,0,137,0,4),(2,0,217,0,7),(0,128,82,9,6),(128,0,91,0,7),(8,0,211,0,7),(64,0,155,0,7),(0,2,137,80,6),(9,0,82,0,4),(1,128,82,8,5),(16,0,203,0,7),(16,2,137,64,5),(1,0,218,0,7),(64,2,137,16,5),(3,0,216,0,4),(72,0,147,0,4),(24,0,195,0,4),(10,0,209,0,5),(18,0,201,0,5),(66,0,153,0,5),(8,128,82,1,5),(129,0,90,0,5)]
def g219A : List (List Nat) := [[],[67,113,96]]
def g219D4 : Nat → Nat := chunk #[0x1f0154509324c110]
def g219D5 : Nat → Nat := chunk #[0x100e1c103020106ca0990c6118c100000c081008002363636369f9081363636723c36363636363663364b3c36363636363636271800f89424c9404c2ea8e14250120f89434c9404829d8614395920c6c5789d46483aa509408d920e994350136483aa509404d9208f66851d32c427c4222750d10bd23841d43442ec8a14350110bb23850940443cc5513250110f91434c940443e85093250110bb1484c940443e450e3750110f315489d40443e850a2750110f315449d40442f48a1434c110f315450930443d4d51324c110f51544c930443f0509324c110bd2484c930442f4521324c110dd13291d30442f48e1474c110dd13251d30443748e1474c110]
def g219H5 : Nat → Nat := chunk #[0x80000000]
def g219D6 : Nat → Nat := chunk #[0x7020b11882100430162061010a8409241020803083c202870418104040c10403081c100c08424230908982020430908c30001080498200381c22605aa302658c08a814742000c2421959048cc7a36306081b300c20c2601634b14318d943444ba60a31919a2c48c6463668b14058c01982c5e46300650b14019a2c300aa01660217ab94342444605301874a5a1d29652ca594b40852cd194b29652d0920429682d021fd29652cfb1a33d6780ea94b39470ce194b3786f0de1b535c68cc818529652cbd11c2965ccb215929652ca594e23852ca013925c434918fa2384347d0df1a82f45509f1181d42f047070084070070009fa8f032653f8de265027e9bc4ca07cd424c930bbc8e99261ee509404c3ec99280987da3750130dba65232613f49e464c37ca044c984fd4789930bdc6ea1241f350d32482f723a64907b94350120fd264a0241fa89d404833ea1cac9067d4195920cfa632b241bb4ca464827e9bc8c906ed3251920cfcaea32419f15d464827f1ba8c906ee2751920dda851b241be502364827ea3c6c906dd434d920dda849b241be501364833f2ba6c9067c574d9209fc8e9b2413f51d36482fb13a87885f63750b10eeea899621f550d32c43f2a1265885f6474cb10bea8e996217d89d43443f883a86885f63750910eeea899221dd55132443eaa1a64887e5424c910bec8e992217d51d32443f899280887f23750110fe26ea0221fc89d40443f893a80887f1424c110fe28e98221fc49d30443d4a12809047d4795920f6286a0221ec50940442f91ba8088773544c110ee2a898221f450d30443e899260885f2474c110be28e98221cc5514044376a144ca06ed2089940]
def g219H6 : Nat → Nat := chunk #[0xb7121cc43ee538a0051f206d43c1afbb5e8007236c9d0d3f8c001739340872001860de8933acb1435819da180184800002260000043de275d37c5c5bbf705d632a001914d5296f1e7c6b0200001ce0019000000000000850810005000c1010800204000000002000000004081]
def g219D7 : Nat → Nat := chunk #[0x284042400b06261c186483830c6062018c0c9431e244244a28f0010b44040261480910900251a22202204884c387109070c4a41e20420252001028e12908881438608094ac203a5141c149c93231043200868e10b4b309011d389949860a10182969800e1c325080a4801c7c7105134c188628e22214553088e204c54c28a0e101824c2071f2440a0f1414c080d316a8304061c1081c80806015070d141049924c4a91181549a64221524929614c4c3a6939154c84947080e60b843464a911814d3058ea92494b3068c9a4e44b3058c95249173068d9b5628a0e60dab2a44d0a60dab2a498345d59468913565c82468a03365c82458ddffa4f64e93cbb89eeadadab73ee5bc8189701ddab635ea9e4f798f2422cc297d6f09c5b38602a9d34a323f672cca1642684106a0a40f616418000ff41932ff54931ff50550ff4c550ff4c940ff89940ff49940ff50930ff51930ff49930ff50d20ff50520ff4c520ff51920ff4d920ff45920bf81932bf89940f74c930fe50130bf91930bf89930fb50920fb4c920fe50120bf91920bf51920bf8d920bf4d920fd50f10fd50b10fd4cb10bf89910fd50d10fd50910fd4c910fd899109f95920ddd5310ddd5110dd55110fc50110fc4c110]
def g219H7 : Nat → Nat := chunk #[0x6392380009aaab4a1f38968888ab0d000408000e0600099e00020a000000000596aa1000e17b4500000060900033fe420000000004ab91c6bf7c4a187acc49c41ba4000000000000d0c32700000000074300099bda279792583e104e3b000895386e1951541be81b46f3500082f000740c0742b98712d834d167b9f26736398000000305c93b8da0f000b00000c203442a591132ed8bd9f72982c132f0294ae2a49c000724000a137c56c7821628c1e783b0e40393169951df3a64761233c99419d83db14bbb390c1aabd50b223fa0c22f1063394b248a379300001000401081a0000200002010210190400000005010e000200010000030400000c0105000000070000030900060303000500020004010100]
def g219D8 : Nat → Nat := chunk #[0x2054d648a4458a49aa1648924b62468aa4961689a34d544aa82d52c46c848c61001534b1484966124883902c93551286164c928461668e4c935528460e11324a69660eed378cc2dca52286c12030060007f4cbfaa3fd31fe90ff543fa81fd30fe907f443ee21f510]
def g219H8 : Nat → Nat := chunk #[0x3b2b8e79ba36a1e9200000000000000002b264870c0038f3273310444dd1c00000069524a33e33609499b3d3b2fccb541b5091800000000c29a232980cc0ad0c5516bc3da900075fc780000125400000520003c500048e00000000d4c000002d8a1200000580108e093541d000000000000007324ba0b0000020b61f45000169800000e4c0069ac10000528006420c00202000000208000020008000080010004382060c10300000810200100]
def g219D9 : Nat → Nat := chunk #[0x21945130603f]
def g219H9 : Nat → Nat := chunk #[0x5d841c834cc30c00000e30e00a2608017789800002a3a0cacb61002c401430018a20000000400]
def g219L : Nat → Packing
  | 4 => (1,5,5,3,g219D4)
  | 5 => (32,4,5,8,g219D5)
  | 6 => (76,3,5,11,g219D6)
  | 7 => (43,2,5,11,g219D7)
  | 8 => (11,1,5,10,g219D8)
  | 9 => (1,0,5,6,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 1 5 3 6 1 1 g219H5 h
  | 6,h => lookupWord 27 69 7 10 5 1 g219H6 h
  | 7,h => lookupWord 57 145 8 12 7 1 g219H7 h
  | 8,h => lookupWord 35 103 7 11 6 1 g219H8 h
  | 9,h => lookupWord 11 29 5 9 4 1 g219H9 h
  | _,_ => none
def g219 : Forest := ⟨219,9,fun i => (g219Y[i]?).getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxHeartbeats 0 in
theorem g219P4_0 : block g219 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 32 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 2 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g219P6_2 : block g219 6 2 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P6_3 : block g219 6 3 11 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P6_14 : block g219 6 14 62 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 76 = true := (@block_merge g219 6 0 3 73 (@block_merge g219 6 0 2 1 g219P6_0 g219P6_2) (@block_merge g219 6 3 11 62 g219P6_3 g219P6_14))
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P7_6 : block g219 7 6 21 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P7_27 : block g219 7 27 16 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 43 = true := (@block_merge g219 7 0 6 37 g219P7_0 (@block_merge g219 7 6 21 16 g219P7_6 g219P7_27))
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g219P8_2 : block g219 8 2 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 11 = true := (@block_merge g219 8 0 2 9 g219P8_0 g219P8_2)
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact g219P4_0
  · exact g219P5_0
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219P9_0
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low219 : Lower true (vars 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=67) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[])]
set_option maxHeartbeats 0 in
theorem V219 : Known K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[(B 0xfc003f03ffc111300f33f,B 0x4104104104104001200a12a),(0,0),(B 0x3f000000fc000629c4ccdcc,B 0x2cb2cb2cb2cb2c40984cc98c),(B 0xfffffffffffffffffffffffffffffffffffffffffc0000fc0000fc8ce08f0e0f,B 0x1861861861861808c08a0e05),(B 0x3f000fff030f00f00ff0,B 0x514514514514520f00a00650),(0,0),(B 0x3ffff00003f000fff000,B 0xffffffffffffffffffffffffffffffffffffffffa28a28a28a28a1f000555000),(B 0xffffffffffffffffffffffffffffffffffffffffffffc000000003ffff000000,B 0xffffffffffffffffffffffffffffffffffffffffc30c30c30c30c3b725000000)]
def g221C : List ColumnInfo := [(4,0,217,0,7),(1,0,220,0,7),(5,0,216,0,4),(128,0,93,0,7),(16,0,205,0,7),(24,0,197,0,4),(68,0,153,0,5),(80,0,141,0,5),(9,0,212,0,4),(17,0,204,0,4),(0,4,73,144,6),(65,0,156,0,4),(129,0,92,0,4),(144,0,73,0,4),(16,4,73,128,5),(8,0,213,0,6),(136,0,85,0,5),(12,0,209,0,5),(64,0,157,0,6),(128,4,73,16,5),(20,0,201,0,5),(132,0,89,0,5),(192,0,29,0,4)]
def g221A : List (List Nat) := [[],[116,99]]
def g221D4 : Nat → Nat := chunk #[0x17422954e524c110]
def g221D5 : Nat → Nat := chunk #[0x2096002868304480b8c1010201060008064043c3dbc3c3c3c3c3c3c3c3c3c3d80903c3c3c3c3c3c903c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3d443d443c3c3c3c3d08cc3c903c543c3c031754d67d0e52cf11081d4690bc35515350932aae28552464ca3e8215751932b4e2854e524c22f9216794930a9d3890a464c3a39093291930cae4249e464c2ea4225450920f295450950482da5614254120f49534c950482da5613254120d695291d50482ea5225250120ba94890940482ea8e14250120ba9488c940483e250d3250120ba9484c9404822f9213795920ea94250236483a650d404d920ea942501364822f921574d9208f66855d32c427c4222754d10b662854e524427c82147949109f13881d42442f8821428c9109f20851e32442f8821424c9109f20851d32443d4551534c110bd24854d30442f48a1534c110bd15850d30443d454e524c110bd13894930442f44e2424c1109f27850930443f0909324c110fc1424c930442f4961324c110bd1584c930442f4921324c110bd1484c930443744ca574c110dd13255d30442f44e3274c110bb24849d304422f9213791920]
def g221H5 : Nat → Nat := chunk #[0x1800000]
def g221D6 : Nat → Nat := chunk #[0xaf683c84997ad5450932f9aa6a1265f38dd424caf703a84994fd47959329fa0f2b2659f551564ca7f23aac996f61755932de82eab2653f81d564cb5eaa48c994fd57919329fa0f23265778dd464ca7f2ba8c994fd5751932dbc6ea32653f81d464cb6ea9c0c996dd4381932dda85032653f55e064ca7ea3c0c995be47419329fc0ea3643d7551534c2ef23aa6985de2754d30bbaaea1a61d754e524c2ee9bca4984fd6794930bba6f212613f59e424c27f33a84987ce424c930f9a84992617795d324c2eeaba64985de474c930bba8e99261b74ca564c27ea3cac984fd2795930dba64ab2613f89d564c37b0baac986f41755930d7aa923261af90a464c36e9948c984fd57919309fa4f23261774df264c36ea9c4c986dd43899309faaf132613f51e264c2df23a4c985ed27d0f209facfa1e417b8dd42c83e6a1a65905ed474cb20dda64a36413f8dd46c836ea1a6d906ed424db209fa8e9b6417b49e54482fa8bca8905f907951209facf2a2417d85d53482f693e86905f907d0d209facfa1a41db54e52482f6a3ca4905ed3794920edaa8a92417b4de42483d72a284907ad5450920bdcaea12417b55d42482f71ba84907ea0750920bda8f19241f354d32483e6a1a64905ee574c920bdaae992417b91d32482f6a3a649057d57d0520bda4fa0a417e41f414827eb3e82907795454120ef2a6a8241fa50950483f4992a0905fa4754120fd4a4a0241fa54940483f521280907b94250120fd464a0241fa4c9404833ea9cac904fd47959209fa6f2b2419f551564827f23aac904fe3755920bf20fa3241bb4ca464835fa0c8c906bd41919209faaf232413f4de46482fd03a8c906ee3251920dda64a32413f8dd464837d03a8c906ed428d920df2811b2413f55e364827ea3c6c905be474d920b788e9b241b754d364836ea1a6c906ee424d920dda849b241be501364827f2ba6c904fd574d9209fc8e9b241af91d364827ea3a6c906bc474d920afcae8b2417d89d53c42fb1ba85887d5534cb10faa8699621f950932c42fb2ba65885f5574cb10bec8e996217d51d32c42fd03a84884fd4789910bec4ea9a21fc41d53443baa9ca4885f54794910bea6f292217d4de42442fb1ba84887f20750910fca85192217d51e32443eaa9a64887d5434c910fcc8499221f950932442fb2ba64885f5574c910bec8e992217d51d32443f8aa260887f2524c110fe2a498221fc90930443f8a1260887f1574c110fe28e98221fcc9d30443f893a60885f54789910bea8e132213d41e1654eb713aa7296f11741842ed2a4a8241ea509404825f23a6c907a74290910be40ea1221754dc42442f883884884f767109109eecf19221f454d30443e8a1a60887d1324c110be4ae982217c55d304437c9820d194fd0781932dda0ca1641af50146c827eb3a84906f50650b10,0x14a801432006101420423600c4a002610428040030507094810f8009380020d0a08280024360080c10f0414104600990108042c2020406480c2120a000c4815105018c224010830243430d2408358c22f058c10a0208041a404918c224049c109043128250040b270928250030908270c0060108281510d0982421c3ca81100c483e043c10400130c0270f00c09c33027c0c1112a9304c040d09630e1038249c3e3090e0c258e3830c090da4630019101210504143086240218430fa90c2184311390c218431172403ea4308610c2184316010c5724315729f218430fa90c5284305a0fa4808b92028d4404313f2732184308610c4804308610c4d8430fa9723ea5c8ea1722184308610c3085c85d97244e7d48626121895925a2e2184312010c2e48b88610c2184308610c2184308610c21889c8610c2e44311390c2185c91390c218430b910c2e44308610c2e44311390c46a430b91721765c8861721f42d08622e2188808610c21889d1390c440854861d43a84308617241c4305a10c41c81c861f52187f08610c3ea4308610c3d4750ea1d43a8430ed90c3a84308610c39a430e118b2b26105a10c2182d0861b7350674b910c2185c8b910c2e4648c590c2b2610bc90c2e45acb01592a452c9c12d23c43c861011f43bc700d11842ec4b0b414a258418700ba1381f83002a038038000000000027ea3c4ca9cfd07899539fa4f032a7d754f4394a7eb3e872967d5351a529fc6ea34a53f81d4694b3ea9a0d2957d57d0d529facfa1aa53f81d4690afb0baa6a16dd538d9429fcaf1b2853f55e3650a7e83c6ca14fd3781942bdc0ea14653f81d468cb76a120d1975d5454d32bbc8ea9a657781d534c]
def g221H6 : Nat → Nat := chunk #[0x24bf1656ca930e5280008300018e00045180a13e4bd9c00092000000001cbb9fb5ba18abf5b37e0e98800127800609000baa990009c20034d80084400000503654002139b464c000000004520012f195c209a1690007c89b39762ff3302fae9a063e5a441285f47e855630dfa860375a07a6a35cc89639310cdc55624638c1b3000c0cb4507f9a9080000000040801200c8708000810410b8b000090e080cf001c0c00000041020008186]
def g221D7 : Nat → Nat := chunk #[0x2304444802810648504020080d1c90f140108d1818d49444080619110901864428a48504010c40c048110e201201c88514504020080818503020038a4878a080c0211c510221c40a443900c0910e4042428010882060a8e90d403880e8318e0a1c52044385102e01ea91871890101391851a70d0b109011400812281800f8428c14503020038c48503008428c3c0930c385240471310289a434723823091d04388271c00a3a08c487a3013848d3868c12487c446280412c78a06003891890a060048a2e0900e560210428a2820082405242b01082146948c4062254120212202031e484411252420204101700f950d24120608940480a3c5880c90a088f00818608242824100408140c0641028b142020301047249018a00206101450906009248248da3191a4830076492041602a4461a09115963490488a48713042325e351c11c332490579315924270580ac852405020b01e00a488c1325f048488c1401505827219411cc0464bf1c11c2b22638108c89c11cbc58f0f08aa1106264871110807221c7c31099116340c24c78e180894f8c70b0ff86b42d2133085838c175eef049817404dff0fd67da3e2deeef4e681bccde30f04774bb55d4ae8a737b935c56e10695b7f1bc2dc66d93679af8d616a6b4ada2ed03674336d98eca5641b1a1862c015efaef5728b645a12c655d2ac0544a98148aa234f9a6f13269714a0a44519889c43620f10267ea3dd1e60ed07383729ad4d18671324187cbde5d42d9165caea55328a93b09a24a123190e88063d31c70d5c65c30516e0ae851426111c08043861850b184e82300ef05f820810409d0410164052000ff49953ff41953ffd0e52ffd0d52ff50d52ff54d42ff8d942ff4d942ff85942ff45942ff81942ff41942ff55132ff50932ff55932ff51932ff41932ff50931ff55130ff94930ff54930ff90930ff50930ff55930ff51930ffc9930ff49930ffd0f20ff50f20ff95120ff55120ff54d20ffd0d20ff50d20ffd0920ff50920ff4c920ff54520ffd0520ff50520ff4c520ff55920ffd1920ff51920ff4d920ff45920ff50910bf89953bf81953df54e52bf51a52bf4da52bf41a52bf51a42bf4da42bf41a42bf8d942bf81942bf41842fb50a32bf51a32bf41a32f754d32f750d32fb90932fb50932bf95932bf55932bf91932bf51932bf81932bf51b21bf41b21f754d30f750d30f74c930bf95930bf55930bf91930bf89930fb50b20fb4cb20bf51b20bf4db20fb94920fb54920fb90920fb50920fb8c920fb4c920fe54120fe50120bf95920bf55920bf91920bf51920bf8d920bf4d920fd54f10fd54b10fd50b10fd4cb10bf89910fd54d10fd94910fd54910fd90910fd50910fd10910fd8c910fd4c910fd89910fd09910bd85953ebd0a42b74d842bd45842be41842bd45a32b74db21fc4c110,0x382a0203451c310091a292490c788492100c8070900d089240852008506221921e8431621087111960a2121f10288386a00a4050a1c2122038542289885831e8c48640484247870c7890870d1825023185890e18e402430e1448810924823c4821c786584048040d0c924101880e141101121f04409042880ca8a091a024204141822828218208062011620212202a4105]
def g221H7 : Nat → Nat := chunk #[0x3a86548e7e30095fffb12e1214b9c4da5b6fb36628d3b8224a541ce24e69314a22a6cb5be6dbadd89f85d170843f5bb0c58ad549b624001d69ae9a0e690200023709f0000000b330000000000801b98400183e74af08988600030ed22ba664308936aac000e1a6c508d0000472f0021700004d4f29f8c8000817b621900000ec0837800000168541e09800012230000000cce0008048000000a7b00000025b400040f80005955c500000004f20000000000000000c96fde1e046381e53346911458e2b08da01d183d09296e05a00015900000002e8c5f000067c00000032b953153ac13000000000000058820958bb30800000000000003f5c0000000000000001637c2680008908680000002520000b61c84400105e0000002dbe00000000021040006be80034c82c64462a81082f63ec38a7688c000a52d1d4000000e9ef8c6e140000003b8ec84000a6450f69178e0364a54b582567507c0112ca428e1d5b94000000d4a734c8264bca4d725916d55410c153cd2581bc22c139107db534e492e613f7abca5374607c2192fd27d11c21c3c2b35f8ee4d6d2ad2261850b14359c89cd46514b536da51b015dd1b18e4feabfb3d49a521de7d6151ace62683b843191c572459e8ea74a5b920a7f00c86c888aae2bfa02010f2b6f3e1499714653949d5759ff889bdd39f168bb37ef8001175e3500000020f04cb3628003c587465c2000279a32886d88309b125416f38bd933891dbe0002cb46070000000000000b3a181840b619774a2dd02d36229218975582afa51625e09264fa7259d879ecd03672ac0c3dc9ec1facd967860b354ee1aac8f6b6b658ccd8f168e381131f4535ee0a383454e3666b68ad7109aa62733b658570d5a2812f759b25d766654d28268f9711cec0a00008101601018040000038688c000200000050382c02110080800000080c0c04000084e030400402050800800170100008010000002000a8d06600040000005000200000000001213000000200000000005000082201000340000008180c00008b00005000240003000100207000240a220300800000180008020082c2a010000402010083404010980c00020100800000601400000001c02000101400000c00002050007c1800008100200108000202]
def g221D8 : Nat → Nat := chunk #[0x1c01a38704282621494908688a9490c09a034280e8883150a03a23081800a03a23803c280888d18a3c301c80840c8c2a2628830109e99c38d0a689c29e4891c039c09094880288a91444882208e32200299c30c8c720008c02670225353b49917408ea354ba2a0901f863144390900f001fd53ff297f54bfc85fd42fe217f8cbfa65fd31ff90ff487fa61ff20fe907f443ee21f510]
def g221H8 : Nat → Nat := chunk #[0xd4f7f5810d67d69c1b446d8528ea1e6508560004802356b900000060048858bb5b000000000000715a278da00000056f3489d9000000f6cad622900000061cc66ff200042185760cfd1718890c16cd37c01b5e585d810d28fbbaca1c6e39ea3bb134b7755000000144b6164343f000000d64000000000b6823a906e3dbe765179b6ae720c1a453f7785ed2d371ddc000e2f00040b000000a3363e78a000438000fe6dd5f28832e4a000501a5d0005ebb6d83045ca25a08d5a463295e8900049244d403baf95f66a319731000e65b23778d75a0211490430994b94541d1db774a52c42749e70812a346a880f0000006d2d47000000eddec773970500000072667242e5f173781794c3bd6f8b2b000541d40f1fcb3f3c000000000a6bc0a62c5e2d36107222762354b73d4e72ad110004595d7793000e0ee76000000c247604c901060001000003010005000200010103010d04000103000000010002010106061101060301141403020000010200080200020201020002070701010000010305070701000001000000070006000600000200010005]
def g221D9 : Nat → Nat := chunk #[0x32002203f]
def g221H9 : Nat → Nat := chunk #[0x190a5533c4000a700000fb800003cbdb66964128e8d4190eef82a08f2580b9a8e00000fab82e3c00a1f8d00105002460000040003404109080140001]
def g221L : Nat → Packing
  | 4 => (1,5,5,3,g221D4)
  | 5 => (55,4,5,8,g221D5)
  | 6 => (234,3,5,11,g221D6)
  | 7 => (121,2,5,13,g221D7)
  | 8 => (17,1,5,10,g221D8)
  | 9 => (1,0,5,5,g221D9)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 5,h => lookupWord 1 5 3 6 1 1 g221H5 h
  | 6,h => lookupWord 39 99 7 11 6 1 g221H6 h
  | 7,h => lookupWord 158 397 9 13 8 1 g221H7 h
  | 8,h => lookupWord 85 213 8 12 7 1 g221H8 h
  | 9,h => lookupWord 15 39 6 10 5 1 g221H9 h
  | _,_ => none
def g221 : Forest := ⟨221,9,fun i => (g221Y[i]?).getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxHeartbeats 0 in
theorem g221P4_0 : block g221 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 1 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g221P5_1 : block g221 5 1 54 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 55 = true := (@block_merge g221 5 0 1 54 g221P5_0 g221P5_1)
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 6 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g221P6_6 : block g221 6 6 17 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g221P6_23 : block g221 6 23 211 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 234 = true := (@block_merge g221 6 0 6 228 g221P6_0 (@block_merge g221 6 6 17 211 g221P6_6 g221P6_23))
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 8 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g221P7_8 : block g221 7 8 66 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g221P7_74 : block g221 7 74 47 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 121 = true := (@block_merge g221 7 0 8 113 g221P7_0 (@block_merge g221 7 8 66 47 g221P7_8 g221P7_74))
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g221P8_2 : block g221 8 2 15 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 17 = true := (@block_merge g221 8 0 2 15 g221P8_0 g221P8_2)
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g221T : checkedTables g221 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact g221P4_0
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
  · exact g221P9_0
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low221 : Lower true (vars 221) (graphGoal 221) 10 := lower_forest (g:=g221) (i:=0) (hints:=1027) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 10 [(221,[])]
set_option maxHeartbeats 0 in
theorem V221 : Known K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low235 : Lower true (vars 235) (graphGoal 235) 9 := lower_self (m:=235) (cap:=8) (hints:=83) (2,0,233,0,8) (before_sound K221 V221) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K221 9 [(235,[])]
set_option maxHeartbeats 0 in
theorem V235 : Known K235 := extend_ok (m:=235) V221 low235 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low237 : Lower true (vars 237) (graphGoal 237) 9 := lower_self (m:=237) (cap:=8) (hints:=1795) (4,0,233,0,8) (before_sound K235 V235) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 9 [(237,[])]
set_option maxHeartbeats 0 in
theorem V237 : Known K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low243 : Lower true (vars 243) (graphGoal 243) 9 := lower_self (m:=243) (cap:=8) (hints:=68) (2,0,241,0,8) (before_sound K237 V237) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 9 [(243,[])]
set_option maxHeartbeats 0 in
theorem V243 : Known K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low245 : Lower true (vars 245) (graphGoal 245) 9 := lower_self (m:=245) (cap:=8) (hints:=1028) (4,0,241,0,8) (before_sound K243 V243) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 9 [(245,[])]
set_option maxHeartbeats 0 in
theorem V245 : Known K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[(B 0xfc003f03ffff040988327f,B 0x41041041041041000100204a),(0,0),(0,0),(B 0x3f000fc0fc003f083614cd93,B 0x820820820820820024048911),(B 0x3f000000fc03338670e1c,B 0x5965965965965962338460e14),(B 0xffffffffffffffffffffffffffffffffffffffffc0000000fff000c3c0780fe0,B 0x30c30c30c30c30c82807806a0),(B 0x3ffff000000fc007ff000,B 0xfffffffffffffffffffffffffffffffffffffffa28a28a28a28a28dc00395000),(B 0xfffffffffffffffffffffffffffffffffffffffffffc0000000000ffff800000,B 0xfffffffffffffffffffffffffffffffffffffffc30c30c30c30c307d5a800000)]
def g249C : List ColumnInfo := [(8,0,241,0,8),(16,0,233,0,8),(64,0,185,0,8),(1,0,248,0,7),(32,0,217,0,7),(128,0,121,0,7),(160,0,89,0,5),(33,0,216,0,4),(129,0,120,0,4)]
def g249A : List (List Nat) := [[],[117]]
def g249D6 : Nat → Nat := chunk #[0x1cb885090f80c07595354130]
def g249D7 : Nat → Nat := chunk #[0x81c60c7cb18f01862070f2c55c24215c72c071481c6cb1c06ae844e2a00ff55930f754d30fe54130bf95930bf55930]
def g249H7 : Nat → Nat := chunk #[0x6000]
def g249D8 : Nat → Nat := chunk #[0x41ca3030c7a90728c075203faa7fd30]
def g249H8 : Nat → Nat := chunk #[0xa29be30000c100000024d004000]
def g249D9 : Nat → Nat := chunk #[0xa86420303f]
def g249H9 : Nat → Nat := chunk #[0xb80030029000]
def g249L : Nat → Packing
  | 6 => (1,3,4,6,g249D6)
  | 7 => (5,2,4,8,g249D7)
  | 8 => (2,1,4,7,g249D8)
  | 9 => (1,0,4,5,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 1 5 3 6 1 1 g249H7 h
  | 8,h => lookupWord 5 11 4 8 3 1 g249H8 h
  | 9,h => lookupWord 4 7 3 6 1 1 g249H9 h
  | _,_ => none
def g249 : Forest := ⟨249,9,fun i => (g249Y[i]?).getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g249P7_4 : block g249 7 4 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 5 = true := (@block_merge g249 7 0 4 1 g249P7_0 g249P7_4)
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g249P9_0 : block g249 9 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g249T : checkedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact g249P6_0
  · exact g249B7
  · exact g249P8_0
  · exact g249P9_0
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K245) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low249 : Lower true (vars 249) (graphGoal 249) 10 := lower_forest (g:=g249) (i:=0) (hints:=3) (before_sound K245 V245) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K245 10 [(249,[])]
set_option maxHeartbeats 0 in
theorem V249 : Known K249 := extend_ok (m:=249) V245 low249 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0,0),(B 0xfe03fff0643c11333f,B 0x224489122448910442c01212a),(0,0),(B 0x1fc07f01fc000080cf29cdcc,B 0x60c183060c1830008a09898c),(B 0x3f80000007f318f0ce0e0f,B 0x4c993264c99326218d08c0e05),(B 0xffffffffffffffffffffffffffffffffffffffffe0000001fff80c1f00f00ff0,B 0x183060c183060c81200f00650),(B 0x3ffffe00000fe000fff000,B 0xfffffffffffffffffffffffffffffffffffffff91224489122448da000725000),(B 0xffffffffffffffffffffffffffffffffffffffffffc0000000000fffff000000,B 0xfffffffffffffffffffffffffffffffffffffffe1c3870e1c38707ed75000000)]
def g250C : List ColumnInfo := [(2,0,248,0,7),(8,0,242,0,7),(32,0,218,0,7),(64,0,186,0,7),(0,16,168,66,6),(16,0,234,0,6)]
def g250A : List (List Nat) := [[],[101,116,49],[116,99,81],[83,97]]
def g250D8 : Nat → Nat := chunk #[0x58d10303f]
def g250L : Nat → Packing
  | 8 => (1,0,3,5,g250D8)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def g250 : Forest := ⟨250,8,fun i => (g250Y[i]?).getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxHeartbeats 0 in
theorem g250P8_0 : block g250 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g250T : checkedTables g250 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact (rfl : block g250 5 0 0 = true)
  · exact (rfl : block g250 6 0 0 = true)
  · exact (rfl : block g250 7 0 0 = true)
  · exact g250P8_0
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K249) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low250 : Lower true (vars 250) (graphGoal 250) 9 := lower_forest (g:=g250) (i:=0) (hints:=823218240) (before_sound K249 V249) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K249 9 [(250,[])]
set_option maxHeartbeats 0 in
theorem V250 : Known K250 := extend_ok (m:=250) V249 low250 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 10 := lower_self (m:=127) (cap:=9) (hints:=1091) (2,0,125,0,9) (before_sound K250 V250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 10 [(127,[])]
set_option maxHeartbeats 0 in
theorem V127 : Known K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(B 0x3f8001fc000fffc004093c102730693ff,B 0x10204081020408102040000928002520292aa),(B 0xfe0007f000041ace302939c9b1ccc,B 0x23468d1a3468d1a3468c412ce30093189318cc),(B 0x1fc0000003f8000008230fc0ce3e0e3e0f0,B 0xb162c58b162c58b162c8030d808e3e0c3c0f0),(B 0xfe0007f000000001fc0c3f0030fc00fc00ff,B 0x60c183060c183060c18083a0020d800fc0055),(B 0x3ffffe030fc0003f0000ffff00,B 0xffffffffffffffffffffffffffd4a952a54a952a54a9530ec0003700002c2500),(B 0xffffffffffffffffffffffffffff000007ffffc0000003f000003fffff000000,B 0x183060c183060c183062a000001f24a5000000),(0,0),(B 0xfffffffffffffffffffffffffffffffff8000000000003ffffffc00000000000,B 0xffffffffffffffffffffffffffe0c183060c183060c18157c525400000000000)]
def g191C : List ColumnInfo := [(1,0,190,0,9),(2,0,189,0,9),(4,0,187,0,9),(8,0,183,0,9),(16,0,175,0,9),(32,0,159,0,8),(128,0,63,0,8)]
def g191A : List (List Nat) := [[],[117,33]]
def g191D9 : Nat → Nat := chunk #[0x1972a6e0703fd65]
def g191D10 : Nat → Nat := chunk #[0x6b1a20707f]
def g191H10 : Nat → Nat := chunk #[0x1800]
def g191L : Nat → Packing
  | 9 => (1,1,3,6,g191D9)
  | 10 => (1,0,3,5,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 10,h => lookupWord 1 5 3 6 1 1 g191H10 h
  | _,_ => none
def g191 : Forest := ⟨191,10,fun i => (g191Y[i]?).getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
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
  · exact g191P9_0
  · exact g191P10_0
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1091) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxHeartbeats 0 in
theorem V191 : Known K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(B 0x1fc00001fc000fffc041024f002730693ff,B 0x1020408102040810204000024a002520292aa),(B 0xfe0007f0000186b38c0939c9b1ccc,B 0x13264c993264c993264c104b38c093189318cc),(B 0xfe000000003f800000608c3f04e3e0e3e0f0,B 0xb162c58b162c58b162c400c3604e3e0c3c0f0),(B 0xffffffffffffffffffffffffffff000007f000000001fc830fc008fc00fc00ff,B 0x60c183060c183060c18020e8008d800fc0055),(B 0x3f800003ffffe0303f0000f0000ffff00,B 0x2448912244891224489203b0000a00002c2500),(0,0),(B 0x3ffffffc0000003fc00000fffff000000,B 0xffffffffffffffffffffffffffc8912244891224489121ec00000524a5000000),(B 0xfffffffffffffffffffffffffffffffc00000000000003fffffff00000000000,B 0xfffffffffffffffffffffffffff0e1c3870e1c3870e1c3bdf149500000000000)]
def g223C : List ColumnInfo := [(2,0,221,0,10),(17,0,206,0,5),(80,2,141,0,5),(8,0,215,0,9),(16,0,207,0,8),(65,0,158,0,5),(0,2,141,80,7),(4,0,219,0,10),(1,0,222,0,9),(16,2,141,64,6),(9,128,82,4,5),(5,0,218,0,7),(130,0,93,0,7),(64,0,159,0,8),(9,0,214,0,7),(18,0,205,0,7),(128,0,95,0,9),(16,4,75,128,6),(136,0,87,0,6),(0,128,82,13,7),(3,0,220,0,7),(66,0,157,0,6),(73,0,150,0,4),(129,0,94,0,6),(1,128,82,12,6),(64,2,141,16,6),(4,128,82,9,6),(144,4,75,0,5),(20,0,203,0,7),(72,0,151,0,5),(128,4,75,16,6),(0,4,75,144,7),(8,128,82,5,6),(13,0,82,0,4),(10,0,213,0,6),(24,0,199,0,5),(11,0,212,0,4),(144,0,75,0,5),(192,0,31,0,5),(131,0,92,0,4),(82,0,141,0,5),(68,0,155,0,7),(138,0,85,0,5),(137,0,86,0,5),(21,0,202,0,4),(76,0,147,0,4),(12,0,211,0,7),(132,0,91,0,7),(133,0,90,0,5)]
def g223A : List (List Nat) := [[]]
def g223D5 : Nat → Nat := chunk #[0x41f20b66a18de15458f984a9a9294a102ba87c4a55d494a50815d438e5556ac8b2a1a8090632964a695816140483990aa2d08c8b0a024194c9687a5654350110]
def g223D6 : Nat → Nat := chunk #[0x20de29520954d43483789548255350d209f282939d61434833e2198255850d20cf886a095614348236e9a5605850d20dc95511916143483729544245850d20dd254d0916143483369584245850d20baa92969551604836e1698655458120db859619551604836e16a8655458120bb88695458d604827e21a52753581209f88695950d604837a1698655450120de84e61955140482f295ad255350120be24eb4954d40482f2a5a52553501209ea52a8954d40482fa21a5514350120dcad525950d40483729549654350120be24eb5950d40483f09539654350120dcad665950d40482fa21a5654350120dca9695950d404837a21a5654350120fc254c5950d40483729591654350120be84685950d40482bab8a1654350120dca552595a140482b6a5a5a35850120de250d39d61404827a94a4e75850120fc88695496140483b2964d625850120eca50f5896140482f893a99158501209eae6a6456140482ea96ad0d5850120de250e39561404837a2498655850120de859219561404837a1438655850120cf89a219561404833e16886558501209eaa694316140483b29545a05850120eca591581614048336a9a5605850120de250d3916140483789644e45850120cf25a139161404837894a4e45850120de859119161404837a1434645850120cf85a11916140483b89435623850120de250d598e140483b29549613850120dca552594e140482bca0a54e3855d20af2829534e3474823ea0a56538d1d20af48e96942354442bd20a5a53815110eccd5254821634429f27a5520858d10af44e85482163442be12a1520858d10a7c5e85482163443176591e55850d10d5c1e95950d504427715aa254354110dd8551299a1504427739ad516854110dcc552495a150443753548e56854110dd4552395a150442bd23a5a24854110af48e96992150443f115350d4854110af84aa6852150442bd23a5a14854110dcc50e59521504427713a9654854110dd454e3952150443751535263854110fc4551434e150443b914352138541109dc969494e150442f325a52553501109ec52a8954d40443f11539654350110dcc9695950d404435b07a56543501109ece6a545a140443731549656850110de8552295a140442be22a5a25850110af88a96996140442be22a5a15850110de450e3956140442b725a5a55850110aec9296956140442bd23a5a55850110af88a96956140443b31439655850110ecc9664956140443b91438e55850110ee450d588e140443791435663850110ecc552584e140443731549653850110cdc562594e140442bd23a5a508d5d108daa695816140483721544645850120ccc96649561404427399a5514354140cce8e554423435427599a5514354130e4e4e154542375023e94a8255850d209ea6695450d404827aa5a4e65450120,0x5d54a798a968422175529e62a5910885d54a758e969422175529e62a5a50885d54a7c82969422175529f20a4e50885d54e4d85e58921075529f20a5e6185516387d66a18de15458f1f2188257855163cb65a5394205458f1f119de50815163c4f5968951c4754e9e62a59e1855d43a798a9688615750e9f20a5a21855d43e4d962488615750e9f10a8660855d43c4f5928955c5750f9355459d1815d43a798a9674605750fb196454d0815d43e4e551674205750e9ea2a59d0815d43e4e591574205750fb19535250815d43e4e55d494205750fb19544e50815d43e5655d394205750fb29544a50815d43ed254d294205750f969574a50815d43cea525294205750f52d544a45741d43d4d5511915d0750e9d63a5e6185516087d66a18de1545831d6188e57855160cb65a5094e0545825d61a527538dd60ace52b58421435429d61a5523859d50ec654d43423475429e52a99e1851d50a758e9678614754313d65a254711d50e47551674e0475421de9a59d3811d50e47595474e0475429ce3a59d2811d50e4d55167460475429d63a59d1811d50ec6551438213754233e9a5605850d40dc654d0916143503339584245850d40bca8a96455150502f2a2a5a55454140dcc5a61955150503731398655454140bc64eb4954d50502f193ad654354140dcc8695950d50503729544a66854140dc6552395a150503719654e44854140dca551291e150503b29545422859d40a798a967861575029d63a5a21855d40a798a96886157503936589221855d40c4f5928955c57503b19435413815d40ec6591504e0575029ce2a59d3815d40ec6541494e0575039355459d1815d40a798a96746057503d321a551508dd40f46551435423750235e9a5605850d30dc355129161434c3715544645850d30dc655109161434c3359584245850d30f86d525458d604c2ed21a5516358130bb24a85458d604c2ed11a1516358130b365e85458d604c3751398655454130bd48695454d504c2b598ad255354130bd48694954d504c2f195a9514354130fc48695450d504c2f194ad654354130dd48695950d504c37194356748541309d656939d21504c3559535e74854130dc650e59521504c3751538654854130b564eb54541474c3d321a5515051d30f4695153541474c3d195454d5051d30c5796639561474c317a598255851d30c768e609561474c217e9a5605851d30d5654139161474c352d544a45851d30d4d55119161474c3539544245851d30d5654d09161474c3d19545423851d30e6655238821474c2be20a4e21855120af88293986154482b695ad220854d208fa66b4882153482be21a5220854d20af24ea54821534823e99a9520854d20af88695482153482b695ad260854d20af24eb4982153482be21a5260854d20cf88694982153482f890a9515350d,0x60c1b8fe0c2f060e08070703034101a084c616130b042103c2010140849d8012440402842f801b0805c383218100a08c41861002074003e001005e0020020b800402fc008418490037003014402a0c1686098805618270c119866198661991a198661986619866198661991a198661986619866198661986619a83a5066ac29419a834691a198661986619866198661986619866198661986619866468661991a198661986646866198661997a5e866199f0198661997a19866198664691a1982219866198661986619866198661986619866198665ea72199f019a61199f0198661986619866940668fc66198661986619866198661986619866198661986619866198661986619866198661986619866198661986688c6684866198661997a198661986619866804661986619a017c1df198661986619866198661986670c6670c6619866198665a4666c86662d7a199695e8665e96919866198661986619866198661986619866198661986619866198661986651d094246619866561474ac66198661991a19866198661986642466198663e0f8198dc1986632c66198ba198931b0660445511033088110025e50a8a56785d54d4d966494de175529e62a59d0885d54a7c82967422175529f20a4dd0885d54ccd96649422175525e50a8a56485d5497942a295a2175529e62a5a1388]
def g223H6 : Nat → Nat := chunk #[0x34580010405201223242100]
def g223D7 : Nat → Nat := chunk #[0xe0855d10bf904ac7a3a21bf163423474437e2d28468e886fc4e508d1d10bf904ac6a3a211f50986157952bcc52b3c2eaa5798a56485d54af314ad10baa99e52846107153bc2508c20e2a47d4261851f538df44a8e23aa755c795955350e73f13322a6a1e4f9624855d438fa84c30aba8717e8955c5750f4baa6b40aea1ecb5512815d43d9aaa2302ba87b39544205750f6b2a6840aea1e5e55d0815d43d9caa211a1aa11be8951c4754363aa89c08ea866751d3811d50d9aaa23023aa17394999550502af0f2b2aa0a05ce5666454140bcc9ccc8a82817395995150502e7472aa2a0a07cc8655454140b9ca4ea6a82816b969d0d50502e72b3a1aa0a07c654d4354140b9caca86a82816b96912150502f3272242a0a064f9624855d408bf44aae2ba81a79505a0575036b2a09c0aea06cb5512815d40d9aaa2302ba81d395454237502eb273aa2a0985d69255354130f8caa286a82617595950d504c27b112a1aa0986768e20855d30e9caa2a0a3a61d5953541474c33b4710428e984fa82538d51209f30cab12a241be119420544827cc32a46a6904fa5260854d20dd4aa211a1a417a90995143482f9412a9a86904f98655850d209f504ab0a1a416ea4959560482fc432aa2c0906ba5964858120bd4a4ccaa02417a95999140482f52b32a280905ea4e65450120bd5c4ca8a02417e21955140482f5472aa280907e88655450120bd4a4ea6a02413ea8954d404827d112a9a80905ea5674350120fc4a9a86a02417aa5950d40482f52b2a1a80905ea5275850120f94aa4b0a0241b6b5896140482f5492ac280905f88655850120f94aa0b0a0241b695816140482dd2d22c280905f24e45850120bf08c8b0a0241f89438e1404827cc32ac68e906f84a50815110bd884ca8a1a217724959550442fc452b22a0885dc4e75454110bb9c4ea8a82217724954d50443e62a8a1aa0887d454d4354110bb8aca86a82217e1299a150442fa472b42a0887cc5524854110bb92ca90a8221f51538e150442fc452b2280885ec9656450110bd89cca8a02217b38995140443f22a6a1a80885ec9654350110bd8aca86a02217e2295a140443e62a92c280886ec50e5850110bd924ab0a0221bb143561404436e4b2ac280886ec9255850110fc8a1c70a02217893999140482d52d3a1a80905e44e66450110b58b4e86a02219dd484213715367a70aa686a86cf50d48d4d509bec4aa8a1aa197d505620750e3fab3042aea1e6f5014881d538fea4c10aba879bd435e35350277b12aa286a04ef9653895140cdea02909bea15bd7955143502b7a73a1caea066f8e15441f438feacc70aba815bd0950d47d427bb12aa286984f79653895130cde9c2a91ba811fd89551474c23fcb2bc4a8986eb4e154d0d20dd6a1a91a9a413ed89551434827dcb29c4a8905fa6255450120,0x907ea5515350120fd5a4aa6a02417ea4954d40483f5292a9a80905faa255350120fd5aa286a0241fa95450d40483f92a6a1a80905fa9654350120bf4aca86a0241fab5950d40483f54b2a1a80907ea5654350120fd42ca86a0241fa9549a140482fd2b334280907ea5516850120bf52cad0a0241fa964d6140483f5287ac280906fa9a35850120df4b46b0a02417e939d6140483f52c92c280907ea5525850120fd4a1cb0a0241be96896140482fd2732c280907ea9915850120fd4b22b0a0241faa5456140483f5686ac280907ea50d5850120df5342b0a0241be96856140482fd492ac280907ea9255850120bf51cab0a0241fe21956140483f52c82c280907ea50c5850120df4b40b0a02417e93916140483f52a91c280906fa5623850120bf4acc70a0241faa544e140483f52a89c280907f254d3850120df52c270a0241be9584e140482fd4b29c280905fa5653850120bf504aa6aba41bcd538e157482fd412a9e8e906f354d38d1d209f72ca71a3a413ed594e3474837d2a68468e906fa56508d1d20df49ca11a3a417ea0954d474827da732c28e904fb5663851d20df8b4a11aa221bf169422544437e272844a8886f55a53815110df8b4a102a2217f109d5163443e6ea92a2c6885fc4265458d10afb3caa8b1a217d53915163442fca522a2c6885fc4245458d10afabc8a8b1a21bf354821634437e4a9042c6886fc5520858d10df82a410b1a217765952153443e6aa92c286887d554e5850d10dbb2cab0a1a219f47956143442fe512b22a0887dcd516354110fb8aa2c6a8221f714954d50443ee2b2a1aa0885fca254354110fb8aa4d0a82217f1499a150443ee6a8b42a0887dc5516854110bf924ad0a8221f7165921504437e2d1242a0886fc58e4854110df8b4c90a8221f716552150443ee2a6a42a0887ec50d4854110df934290a8221bf16852150443ee4b2a42a0885fc8e54854110fb8aa470a8221bf1488e150442fe2931c2a0887dc5513854110fe8a1a70a8221bf1484e150442fe2929c2a0885fca256550110fd92a2c6a0221fb15458d40443f6292a9a80885fca255350110fd92ca86a0221fb15950d40443f62a934280885fc5666850110fd92a2d0a0221fb1545a140442fe4b2b4280887ec5925850110fd8a1cb0a0221bf16896140442fe2732c280886fc58e5850110df8b4cb0a0221bf13996140443f62c8ac280887ec50d5850110df9342b0a0221bf16856140443f6492ac280885fc8e55850110df8b1ab0a0221bf269561404437e2d2ac280886fc8e55850110df89cab0a0221fb1548e1404437e2b11c280885fc5663850110fd92a270a0221fb1544e140443fa2a69c280886fc9613850110df8ac270a02217f2594e140442fe2b29c280885fc82563d5d10df8b1a11aba21bf16942357442fe412b1aae886fc58,0xb2732a2a0985fc8655454130fac9caa8a8261f7219551504c3eb6a8b1aa0987d65516354130fad2a2a6a8261f595454d504c3eb692a9aa0987d65255354130fadaa286a8261f9a5450d504c3f32a8a1aa0987d65514354130fadaca86a82617da5950d504c2fb2b2a1aa0987d65654354130faca9e90a8261f9943d21504c2ef2b3a42a0985f64e74854130afcbce90a8261f5953521504c3f3286a42a0985de9654854130bed1ca90a82617f219521504c3eb2a91c2a0985f65263854130e9faa4a8b3a615f619551674c2bba722a2ce9857b4a45459d30afa8c8a8b3a615f909151674c2bba732a2ae9857d8655455d30ecf2a286aba61d9d5450d574c2afab3a42ae985774e74855d30afc84e90aba6157e59521574c2bbc72a42ae9857d8654855d30afd04a90aba615dd498e1574c3bb287042ae985774e75451d30afc84ea8a3a615f619551474c3b6c32aa28e987679515351d30eceaa2a6a3a61d7b54541474c3b74a8a828e9876e5515051d30ebcaa2a0a3a61dd953541474c2b7a93ac28e985774e75851d30afc84eb0a3a61d3d54961474c3abaa72c28e9875e5425851d30cbfac4b0a3a6197f54961474c32faa92c28e985778e55851d30afb0cab0a3a615fa09561474c32fcb2ac28e986778e55851d30cfb0cab0a3a619fa09561474c3a7aa82c28e9875754c5851d30ebca80b0a3a6197d58161474c2bba722c28e9857b4a45851d30afa8c8b0a3a615f909161474c3b3aa91c28e987765423851d30aeeacc70a3a61db954821474c3bb2a70428e987768e20851d30afcacc10a3a61be959422544837d272844a8905eb9256855120bf504a70aa241be568861544837ca710c2a8906f95961855120df2b4c30aa241be53986154482fcc32aa2c6905fa4265454d20bf30caa8a9a4176d59d2153482f9a73a42a6905fa4274854d20bb72ca90a9a417e61952153482fd412a42a6906fad220854d20df4a4410a9a417e949821534837d4a9042a6906fa5520854d20df5a4c10a9a41be949821534837d410bc2a6906fa56508d0d20bf30caa8a1a41fa61955143483f1ca8a9a86907e35515350d20fe504aa6a1a417cd39d6143483e5aa92c286907d354e5850d20db7ac4b0a1a41b6f54961434836daa92c286905f98655850d20bf504ab0a1a41b6e59561434837cc32ac286906fa8255850d20f96aa0b0a1a41f4d53161434836dab02c286905f94645850d20bf4848b0a1a417e939d5160483dd2caaa2c0907ba5a55458120bf51caa8b0241fe21955160483dd6a8b1ac0907ba5516358120bf4a4ea6b02417ea4954d60483f52a8a1ac0907f254d4358120bf52ca86b02417e95950d60482fd31332a80905faa256550120bf49cea8a0241fa96555140483f52d2aa280907ea4e55450120fd4aa2c6a02417e989d4d40483f54a8a9a8,0x4257502bdc52b3caea074f5935795d40e9ea1eaf2ba81b79504e257502bdc52b24aea074f5935495d40e9faa2872ba81d3d5450e57503b3aa6a1caea057b8a56895d40ceea9a712ba8179d399915750277f13322aea05af5a74355d40af714aceaba81b9d438e15750376c910c2aea06ed5921855d40ddaa1c30aba819f667861575033eacf0c2aea057b8a56455d40ecea9a86aba8157e595a157502b7c92b42aea05778e56855d40af714ad0aba815fa095a157503a7a872c2aea074f9624855d40ecea1c70aba819dd538e1575033ba871c2aea057e8253855d40edaa1c30aba819f668861575033ead10c2aea075d9621855d40edb24430aba819f638861575033ea710c2aea067d58e1855d409df44a862ba81f396454057503e7286a80aea06dea255015d40e9eaa2ce2ba815ee2959c575023fd12b38aea074f5915715d40cbf44aae2ba81b9d434e0575036f2a09c0aea06e75913815d40ceeb3a702ba81b9d494e05750375a86940aea06ed5911815d40ddaa1a302ba819f56746057503f3412a1c6ea07ce551508dd40fcca1aa11ba815bd49d5e375023fb13abc6ea076750d578dd40afb0caaf1ba81b9d4356237502bf213aa46ea047f627548dd40afb0caa91ba81db61955237503b3aa8a1c6ea075ed51508dd40edd2a2a11ba81db95454237503af2a8a846ea077650d508dd40adea4eb11ba815f909d62375033ba86ac46ea07ce551504dd40faca9aa09ba81d3d5495d37503af2a12ba6ea057d865574dd40ebca80ae9ba815ed2915d37502bea322ba6ea047fe24574dd40d9eaa4b09ba81b7950961375032feaf2c26ea065f55e584dd409fd04ab09ba81bb954821375037b2a70426ea04fe566084dd409fb0cab12a261bd538861544c37aa730c2a89867d5e61855130cfb0c2f0aa2617d909d51634c3e3ea92a2c6985f58655458d30be6948a8b1a617d519151634c2fb2122a2c6985775e45458d30beb0caa8a9a6175d59d21534c2fb213a42a6985775e74854d30baf2ca90a9a617d619521534c2fb412a42a6986f65220854d30bec84ea8a1a6179d59951434c2fac32aa286987e58655450d30bcea4eb0a1a617d909d61434c2bbaf3ac286987c75525850d30dafac4b0a1a61b5f54961434c36baa92c286985f58655850d30bed04ab0a1a61b5e59561434c37ac32ac286986f68255850d30f8eaa0b0a1a61b5d58161434c2f9a522c286985f54645850d30bec848b0a1a61f9954821434c37b2b104286985f65660850d30bec9cea8b0261f3b54951604c2fb2732a2c0985fc8655458130bec9c8a8b02617e929151604c2fe2322a2c09857e5e45458130f6daa2c6b0261eda5458d604c3db2a8b1ac0987b61516358130bed24aa6b0261f9a5450d604c3f32a8a1ac0985f69654358130becaca86b026177959951504c2f,0xa1f1d5350f475423fb1333e8ea856f92567d1d50aef1cacfa3aa1b3d43563475436baa69c68ea84df56538d1d50dbcb2a11a3aa1b795342347543772868468ea84fe8e508d1d50f9b0caa923aa15de3959e47543a7acba3c8ea857b8a56491d50e9eb2ca923aa15de395a2475433ba869c48ea84dfe266551d509bfc4ea6a3aa1f1d5350d47542bda5333a8ea85778e56751d50d9ea1cb0a3aa137d39961475436baa71c28ea86dd9621851d50dbab2c30a3aa1b7553861475433eccf0c28ea867d59e1851d509bf44aca23aa1d3d5459c47542bbc72b388ea847fa256711d50e9eb2a8e23aa19be8951c475436baca9c08ea867759d3811d50db6b2a5023aa19ed674a0475436eaca8c08ea867d59d1811d508fec4e8f1baa15f61951e375436baa6a446ea847f626548dd50afb0caa91baa11fd4992237542bec32a446ea867754d488dd50cfb0ca911baa1f1d5450d37543b3a87a3a6ea876750d474dd50afb0ca8e9baa137e59521375427f412a426ea86de552084dd50deca1c109baa13f949821375433eac70c2afa04fe4267859540bd714ac8aa281bb56486154502f5c52b42a8a05ee8256855140bdd04a70aa281bb5688615450376a710c2a8a05cf5674854d40bce9ce90a9a8173e5952153502afab3bc2a6a04fe4267854d40abf2caf0a9a817b6195514350367ea92c286a06cf5525850d40bce9ceb0a1a817b909d6143503e3aa72c286a06cfd625850d40bdb0cab0a1a817ba095614350367cb2ac286a06ed8655850d40ddd04ab0a1a81f1d531614350367ab02c286a05eb4a45850d40bda8c8b0a1a817b90916143502b7ef22c286a07e654e0850d40ddcac410a1a817b95982143502ef492b2aa0a05fa8a56454140bdd2cac8a8281f3964d5150502ef273aa2a0a07ce5965454140bdc9cca8a8281f396555150503e72c8aa2a0a07ce5a55454140f9c9caa8a8281f395458d50503e74a8a9aa0a07ce5515354140f9da4aa6a828177a4954d50503e7292a9aa0a07ced514354140f9caa286a8281f595350d50502ef2b2a1aa0a07e654d4354140f9daca86a82817ba5950d50502f72b2a1aa0a07ce5654354140f9caa4d0a82817e9299a150503e72a8b42a0a05ee9256854140bed1cad0a8281f395492150503e72cb242a0a07ce5944854140bddbc890a8281f39548e150503eb2a71c2a0a07ce5513854140fcca1a70a8281f39541e150502fd2523c2a0a07ce5515099d408fec4ea933a815f6195526750277f132a2cea07ce5515059d40d9eaa4b0b3a81b79509616750375aa9142cea06fa5422859d40afb0caa8b3a8197f54961675032faa92c2cea047f62667d5d40abf2cacfaba815ee2959f5750373a869c6aea06ee59108d5d40ddca1a11aba81f361955257503e72a8a84aea07ce5915095d40f9ca1aa12ba81f3a495,0xaa2112ba873bf899915750ebdc52b3aaea1eed9221855d43ddab2430aba879f6678615750f3eacf0c2aea1cfd4261855d43aef1cacaaba875ee295915750eafcb2b42aea1d6f9256855d43aef1cad0aba875ee295a15750ebf412b42aea1d5f4265855d43e9f2c490aba879f6688615750f3ead10c2aea1f5d9621855d43edb24430aba875f5098615750f3ec31042aea1e7d8660855d43cfb0c210aba875de394215750fe3ac8a98aea1ed7a255315d43e9eaa2ce2ba875ee2959c5750e3fd12b38aea1f4f5915715d43cbf44aae2ba87bb5644605750f3eace8c0aea1ecf5510815d43daea9a102ba8797d574205750f772c8840aea1e7e59d0815d43ddca4a102ba87bd9394205750f7d252840aea1d6f5275781d438fec4eaf03a875f61955e0750ebba73aa40ea1c7f6275481d43adeacca903a875f6195520750fb6c32aa40ea1f679515381d43eceaa2a703a875bd49d620750ebba73ac40ea1d7d8655881d43cfb0cab103a875bd49d5d0750fa7aa92ba0ea1f5754e5741d43afb0caae83a87d3d5415d0750fabaa62ba0ea1d7b4a45741d43afa8c8ae83a871ff8915d0750f67aa92c20ea1ed754e5841d43cbfabcb083a8797d579610750ed7c92b2ca8b04fd8655895160b5f24ad0aa2c1af568861545835eacb0c2a8b06bd5921855160d7ab4c30aa2c19f779861545833eaf30c2a8b067d8637855160cfb0c2f0aa2c15de395e1545835bad29c0a8b06f64253815160cefbca702a2c19dd794e0545827f472840a8b06fc4650815160f1faa4a8b1ac16f61955163582dba722a2c6b05bb4a45458d60b7a8c8a8b1ac16f909151635827ec32a46a6b04fd8655850d60afb0caa92bac19be545225758337aa8a44aeb057d8655491d60cbfaa2b123ac197d5456247583a7ea92a46eb05774e6548dd60aef1caa91bac15f61955237582bba722a46eb057b4a4548dd60afa8c8a91bac15f90915237582bba93a9c6eb0767951438dd60eceaa2871bac157e7952153d432fcf2ac287a867d58e1851f509fc84cf0b22a176e2959354542e7c92b2ca8a86dd5961855150bb714ac8aa2a173e495a154542edc52b42a8a85de8256855150bbd04a70aa2a1b7568861545436ea710c2a8a85dd8655454d50bae9ce90a9aa177909d2153542afaf3a42a6a85dd8654854d50bbd04a90a9aa1b794882153542ef293042a6a87cd8655450d50f8f2a2a6a1aa1f1d5454d43543eb412a9a86a85d74e75850d50dbb0cab0a1aa1b7a0956143543e72a884286a87d654d0850d50dbdac210a1aa1b795842143542b7a93bc286a84fe4267850d50db6aa25133aa11fd8995267542bec32aa4cea84dfe275459d50d9eaa490b3aa1b5f548e1675436baa91c2cea86de5520859d50afb0caa8b3aa19be549216754337aa9242cea86779523859d50ceeaa470b3a,0x85d54cfab3a110baa99f537422175536ecb28442eaa6ed9250885d54afb1cacb0baa95f60959617552bec72b442eaa7798a56885d54afb04ad10baa99f5684e217552becd29c42eaa57d8253885d54cfab42110baa99f53842217552becd28442eaa57d8e50885d54cfab2a110baa99f564422175533ecd28442eaa67d5a50885d54cfb2ca110baa99f649422175533ec728442eaa67d4e50885d54af714ace83aa99f6179a107553aec2f2c20eaa76d85e4841d54d9f2c49083aa99f6178e107552bbc12b426e2a6775a2084dc54aeeb4c109b8a99dd68421371533ead08c20e2a57e8e56841c54cfcb4470838a95f9698e1071533f2d09c20e2a77c5a11841c549fb0cab12a2c7af5658615458e7ea130c2a8b1e7dde61855163cfabcc30aa2c79f618de15458f3ec30bc2a8b1d7e82578551639ef04a702a2c7af9694205458f7b272840a8b1efc4650815163cfdbca102a2c79f9794205458ebec32aa4aeb1e6f9514895d63cdeaa2912bac75f6195524758f2fea8ac48eb1e5f5515891d63e9faa4a903ac75f6195520758ebf412aa40eb1d774e45481d63af6948a903ac75f5191520758ebf2122a40eb1cf74e67859153b9f24acb2a2a7b75658615454e7ea130c2a8a9c7f6265499d53afb0caa933aa75f6195516754f37ca9242cea9e6f5524859d538fec4ccfa3aa75be4959f4754f6baca9c68ea9cf782538d1d53e9eb2e8f23aa75de395964754ebdc52b248ea9f4f5965491d53aef1cad123aa737f899954754e6fa132c28ea9edd9621851d53dbab2c30a3aa79f6678614754f3eacf0c28ea9cfd4261851d538ff44ace23aa7d3d6551c4754f37d12a388ea9d5f5674781d538fec4e8f03aa75f61951e0754ebba732a40ea9c7f6265481d53afb0caa903aa757d59d220754ebba73a440ea9d7d8654881d53cfb0ca9103aa757d59d1d0754ebec32a3a0ea9cf74e67859543bcf1cacb2a2877ae295915450f76ac90c2a8a1cfd4261855143bcf1cacaaa28779e395a15450ef5c52b42a8a1eed5a21855143bda84c30aa287bb6184215450ef3c72842a8a1df38a56454d43bcf2cac8a9a87f1d659515350ef3a132a2a6a1fc75955454d43bcf24ad0a9a87f1d659215350fe3aca242a6a1de7de44854d43dcf2a410a9a87b9d548215350e7bd12a9ccea1c7f6275499d43afb0caa933a873bf899516750f67aa92c2cea1ed754e5859d43dd6aa450b3a87bcd538a16750ebec32aa2cea1e5fd525859d43cbeaa4b0b3a871fd8999f5750eafcb2b3eaea1d7b8a567d5d43dceb2271aba873de094e35750fe6c32aa4aea1fc75515395d43f8eb22a72ba87f1e4954e5750ebdc52b3caea1f4f5935795d43d9eaa2112ba87b5d534225750f2feae844aea1d778e56595d43af714ac92ba87d3d64d525750ebdc52b44aea1e5fd510895d43cbe,0x1615f25161431572d5e0572d5d3572d5cb570d5b1569159255c543155915644aa52a936153de526954d5514d883620dbf54b9517540145851614b253cd45852a94aa53994d95160d8536154a253094b2416505952e94b24164d85361547d3614d8551f54aa361547d51f546851a146836fcdbf3614dbf36153de52a94a2361549a521548552154855235485521546851a146851614582e8cd8551f546051a0d8551a147036fd46836fcd851c107045180d853614d853614d852e8cd85516144b4f78d8550e4b1f50c5424504940536153f34f98d854f78eff4db936e4f38dbf4f593ce4e753bc3cd8f364ebd39d4e4137e41653664d98f504dd8f364db8d853614d854d9935e3614f364d453444cc932a1c10d85361531d4aa530b4be52784bb12da4b212b64aa52974a152784998d903640020362124f48e0d884899219481d1fa3bfd1ed3614008476d0593a551c436151b7468118445dd165453914144d112736151152c7d10343d90594390f9143490c042a5097421507d4185059411cfb840e901e3ff4fd73f14bee3cd8fb82f08bb02e8cfab3e78f913dfcf6d3d94f583d40d853cf8f363c90b1f3c70d853614b602c9cb1f00e0f142ce4eff2ce4eff3c1ceff2ce4eff3bc8ef23b80ec936fcd8536149783b04d903620d883abc9783614e9d3530e953a0ce763410e692ce4b6032bce4d3900e333870e0a37f4df0378cdc736fcdb23694d983640d883620d7d3614d7d35c0d633530d3f34b4d1b3410cf733a8cd82ce4ccb2c7ccaf3260c9031e4c673168c4d3100c243048bfb2fb8be12f3cbc22ec0ba30020b912dfcb6d2d04b392d80b532ce4b412ce4b272c7cb172980b0a2bf4af02b50ab82a98a992a1ca7a29b4a6026cca4928b4a1127d49d426cc99c26149782614978257094a24b884b245c90023b88d722ec89a220c862212c834209c80b1fd07d81f187b41e4c7771d947441c8c70c1c106e31b1c6ba1a8c69619e8663193063a186460c17e85de17445c416b459615fc568151c535148c50713d44de13304b51264473115c436107c4080fd83df0f343bb0ea43970e003690d3433b0c7c30307a42f10b7c2c80ad82950a0c271096824d08ec224084820007a41c806d819a060c171057c14d04c411a03e40ec03680be028808101bc05801400100040010010004801000480040010002003800e0008010000800e003000a001000800180040010004000800013ed098a164d52bdc52b226faa57b8a56441f54aef1cad083ea93bd399216595277a13242cb2a5778e5654de549f684c50b22a93bd399216755277a13242ceaa6eb9222859d549f684c50b3aa95ee2959d3755367cb12426eaa76d9256785d54afb1cacf0baa9de62959e17552bec12b3c2eaa57d9a53785d54ebb2ca6f0baa9db6494de17552bec129bc2eaa67da2537,0xe44361400870d0d85759cd853615e323615e1b5da8d857839bf64164d853614d8551f5468361547d51a0d8536157723614d85361547d7625e06759cd853614d85361547d51a15c35dc80283614d853614d85759cd853614d85757dd673614d853614d853615df43615c493614d857124d853614d85361546852a8d8577b0d85572d4ba52e8d8536154ba759cd7d777cd856611dd27714d7d76cddab7679d9e572cd853615d913615d8952e8d853615d675ffdb1e51f54683614d853615d813614d8575bd7d85160d8552e94585160d853614d85759cd8551f4d8552897ae757d4ba755d681361577275297725dc97725da976a36157503615d3835f4d7d74ad46051a1d2351a1d167439cfc73456c752e9cbf52e9c68728dc8c71d54ba71a1c5b516149a3615c493614d857124d853614d8536154853614d85361546852a94585160d8536147043614d8552a8d853614d8551817046100d8570f003870d0ec13615c223615c0b5da9bfe6fd8d853615bee6101bd43bfdbd46f85bd46f1d5cb3614d8551f5468610147d51a0d8551f5772361547d3614d853614d853615bbf6979bad36154685f41ba06a697d06e4d7d06e19b796895a256db0d7d3615af46d7cd7d6979b4535f4d7d6d49a5e35f59f16d154586ce14856cad46851a00383615b1e3615b1636140386c595cb51f54686c3946035f4d853614d8535f4d7d6bd18143614d853614d7d36156a85f416a8361546835f4d7d6c057ae5eb8d853614d7d35f5a9a6a696812c7daf46bb1ac66ae4d7d6a9da250021a252c7da9a2c7da883614d7d6a20d8569ecd8569cd46852c947d6998d8551a16556978d855954d8551a1a446945a4468c99996895a2535f4d7d361546851a1468684da066790d7d361545835f59b867f99e467c59e4675cd7d67159b86698d7d5161458666598c6610d883620d8565dcd8565a995864dd91b3620d85642470436158fc36158ea3bfd4aa3614d8536154aa63758c662898aa60518a26254d883620eff620d4b261c4db261694b26120d856101704609181c60518075ffd7f251f54683614d853614d7d3614d8535f57e05f610594164d8535f4d7d2e8d7d05aa17c335f4d7d36154685ed8d7d5ed97ae3614d7d5e8579436156815e1d77a5dc97725da976a5d74d7d5d40d8551a14685d2173b361572935f4d7d36157213614d7d5c507045c317045b656c735f56b55aa0ba35aa16815aa16965a256895a0403859d10593614d853614d854164d853614d853614d853614d8552153663614d853614d855974ba3361505936147043614d8552894584f78d8551816555160d855954d85592163b361563350c4eff3bfceff3bfd626570ceff3614d8552a960c4f5945841653de36156195514d8552a94aa5160d853614d854f594aa58313d657fcd8536153d64f580385,0x1000d00618ae180a138f400462387401a0200bc00041802e1856180a130002840a10c02803618a0b020700a13000b0443100103009a608001028a00415a084040c00a00da020a363840bd8e66860bda02206699a001210200400846838e101c223861ba0e38484500699a0010a0480b403862500099ae3d00680800f00010602b8614002904e870013a084b8ee1f00280bc0386182c84b87c009618021610c0040280361860b586101d6199a181c008466b0061860708961860b10c4006e838612280a848a0a62906290228ba0e386e182078248c041123048448c0c141fe1e1ba42362b8fe1d8186a36280d86b9018040b040eda005061181417800b0403390178fe003a050834f8011836010a147a1e3846010be8781e3846010a0efa1e078e01046303be8707e078e010c4c78fa18042003e071001080b004102e06f8fe0014280b68014182fe3809e001429a78478e0108e18046981c2611e380419a607586010869f8f61f80008a69f8e02587e001c30460e80a00881183be01a601610378fe00020509e3f800082c2781c405e380be0710010be3f800281427a1e3f80028022f100d8041f8e00804183b446864c00be00c00f806981a870a69f800b06010468c00be041c30460102c69f81840c118a60700a20140847c193007780068c11803e001a050a0081410a72680f61890df10170fe1b8126c362893c3c9bc409e00ba298162130088841fa000f8069823a18c2e8141093c3f1018bac47802980e28c00d8584436141748aa0300968016888142780088020508698238408427a1e01a600822e18c698380b07843810d866981c05b86210b08e16210669d860588420a6038ba18a62e816008869f8161802088a2233e2eba1e0002050e00f8069817618a2ee11e01a62101631a600816210866889e000226166680219a6008160b0984093858622002210602f80210666e160506e199b85802278666e16008968089e0014008b2243d8586e3f87c049a2d8be878e00e86010a6d01501066980a01060b1a60a80221a60102c1a31e878e02d86010c0502c01066982c010685e280500a20158a05e382c01066980a0a002209a0500a1b8e0540418020a5a00509e878e69802e180431a60782c1ba00578e00804280269d860108698100106288158a0600f8e0107e878e00b86010a698020a02c27a1e380bc0386010dc000417000b0041da1e3888050022803e0022210142803e003008885070de38040506e878f07004220809900a900b100a0609060a1c091c0a8609860a100fcc0d855f40d8551f547d7ca1f203614d855dc976a7c4de4c7c18d857be5ee23614d7d35f5ec335f5ed07b0cd7d35f4d853614d857ad9ea47a5cd850121e8579e00480120d855a04d857999a7369ccd852c7de593614d7d35f5e4c3614d853614d850121c343615,0x10105e000414220a22c430e185508d1143880db0615200847e000418a0080541852800611a6118469a061307680269a0610402805a8020902069084186c1826002e80304e001018e438e1b9060040a02a99061506083763f06183e09ca1a428f82607a0100ef80010608f8fe0046010be3805e0046278fc1f800108e3f06130601040400c00060631012360a22c3b06184f08d0f41880db10132008be083d84040de10103c840421820e805e00748004104c010413092103a24840ce101033c40402804103a010407046111a440508e0e104c0b1a0804028404004121a08272861b8468ea1e803820018400f8001060cb10100c01800180c0005030222086103a08128d8408c04104a088121804c40404e0784078180410120805c404118041014010408f10010604f10102204b1018460484698101408080269846984c138e6984a184c12b8e84780010c1183a84780010b618040e860103a100411d86180411856821b63a10204c0ba1b619082e1a0909840561a1a84060e81c42068458f6000426a0421101c36084a0be8e4209a284a082e0822c404c20383c36101a425101aa60c040d100105a000416800812c40404b86160101040180410260f80091209840178011120804e1840638ee1861102442a615100836083e09ca18428f82687a0100f820038602f800106c40041038c4004181ec404e383a1910104626e860708230211310100cc404120229a10140984041182c104604041180a102e29a0618a68185818208020b82429862982410a609380182e0901ce3b80298ca9c06102c01780870987020b506e0004202ce8015840811b800102c204741840b04612100b0401003601062706080a081008060c1a0f060684068202020b78010000b800846084607042480ae00629822ef8012222631618c4c40488ba0c586c4386101c0f10091008ba00b8018bae0042eba00506e00ba15a005042189a08800e860884082c2105c408010ba047801822081c268466d80a80685f800d87a81801036298a418a62938018a628180182e2984a9ea061866222e3006298a011800b8a61a160df8021082ea11e008420920298018ba0085618ba2106050ba10842e8561b8021062e89204180208861842ea102138023a085b80088142da000840283000860899b4382e20880b84699a01210618429b0e6806699a084068419a10a66830e189200d801d80699a0199a24d8002880b093600602d80618760022999ac3d80680a008202803e00621180141761d80698362da105a1022580050c299a10430f22587600e0738600860298610ba618466986101c2204249800b072680f21860f82858ba108808102308018ba089200b80183808b608a1840584020c0a410304a0a41928e3830290803020b22801076858e840761820bd8662060b98811a0e1840ca,0x60809a00f000c05a0044d80414986384488186418e2018e3990184464056818e11226418e19a061846838e64066199013a0e3b861e8]
def g223H7 : Nat → Nat := chunk #[0x87961822780035a9cacb331bdd184cf2d456088c848f8472f1a71434e456eb900cb6edeb4b728ce1fe0a0002aa359166c408398f5c32555648a651fd835a3260bada4000f534022908437d0138cd59986e13bda83d54cdcc7d80035220000007b04a0d47100071aac29a61739d2d4001eef000206800080bc380002451c7800060a40012ea0003b0000146b7266924001ad752f0989c9c510d4f40715dda8b53f69d40018d10000000000cec96b79d3456e2613e139c00100f000384d4a80000007acb4ce000d2e401400120e72c4081534000544426247d05f92873a6953c113712a3400080464780019a10d3f5d98eac7baf4921c1135e1ced75a18858f76f6d414a6c60e29fe842921d0f068341c9650b40000003b38864e34000440c83fcc6000738111d47f322d01a1d14ab225f80717d100f1299b7d25eda0007a56dc6ebd36c50e613800030b53e7095909e4a00035f8aeb24042bc001a9d85880028a2d01f3d0b1c8ca000162fa1615a6035510002846000f2e9c2c921d0a45bcb6c837adf60cd0bc9f5a526520a9c0012bc6126408000000d86c14dc7ec300000000001027b30224edfee7d0000001cf30e663b5027188e1200058c4001cd90000000c3a0000000002c0000037e8000000000e821c38000000767ab0c000e4667a800045400000000000008f3443000350244712680028192cdf1d9afd01b42c35d000080fe38e390003e0a415e5cea304af256b57132cd2f83688672c25948b826ac879cdfea565b58b61e3a8990b8ace482050080400000000000000000c0004068000805000141204000100400030000007030000000000000208000000a030080404160100c020b0000400010900000000100400060000000000281c000d038100812000000e09000100802000000615030000008008100200000081200000000001008001a0200000000000008200402000181009800081f038040804018100007028180001000040006]
def g223D8 : Nat → Nat := chunk #[0xe3855d30dfa0855d30dbe5451d30dbd5451d30ddd5351d30df95051d309fe5851d309fd5851d30dde3851d30dfa0851d30bed4899520bee4859520bed5899120bed38d5120bed5895120bed3895120bee3855120fe61855120bed3815120bed48d4d20bee4854d20fea0854d20fad54d0d20bed58d0d20fae5450d20fad5450d20fcd5350d20bee5850d20bed5850d20feb5458120fe95458120feb5358120fe95358120fe94358120fea6550120fe96550120feb5450120fe95450120fe96350120feb5350120fe95350120fe94350120fea6850120fe96850120feb5850120fea5850120fe95850120fe85850120fea3850120fe93850120bed38d5d20bee3855d20bed58d1d20bed38d1d20bee5851d20bee3851d20bee584dd20bf64859510bf65859110bf538d5110bf53895110bf53815110bf64854d10fb65450d10fb55450d10fd55350d10bf65850d10bf55850d10ff16554110ff16454110ff16354110ff15354110ff14354110ff26854110ff16854110ff24854110ff14854110ff23854110ff13854110ff16550110ff16450110ff16350110ff15350110ff14350110ff26850110ff16850110ff25850110ff15850110ff23850110ff13850110bf538d5d10bf63855d10bf538d1d10bf63851d109ed0889d649ee2859e549f61855e549ee2859d549f61859d549f50885d54de92841c54df11841c549f61851f539ee2859d439f61855d439f61851f509ed2899d509de3859d509ee2859f409f61855f40b9d3899140abd68d0d40f3954541409ee2859d409f61855d40ed96358130f5953541309ed7899520bcd3899120be908991209ee7859120f2f5495120be90895120be61855120aed6815120bcd3815120be51815120be908151209ed7815120bea0854d20aed68d0d20be908d0d20ee96558120ee96458120ee96358120bea4858120faa6450120fa96450120faa5450120fa95450120fab4350120fa94350120bea6850120be96850120aed68d5d20be908d5d20be908d1d20aee684dd20be52899510bf10899510bd53899110bf10899110be62859110bf108d5110f375495110bf108951109f67855110af56815110bd53815110be52815110bf108151109f57815110bf20858d10bf108d4d10af568d0d10bf108d0d10f726554110f716554110f735454110f715454110f735354110f715354110bf24854110fb26450110fb16450110fb25450110fb15450110fb34350110fb14350110bf25850110bf15850110bf108d5d10bf20855d10bf108d1d10bf2084dd10bfd7855153bfd7855143dfd4391d53bfd7855150bfd7855140dfd4091d509fe4859f54dbd3755343dbd4351f539fd7855143dbd4391d539fe484df549fe584de54d7d0755350dbd0755340dbd4051f509fd7855140dbd4091d509fe4841f549fe5841e54,0x855d43df61855d439fe0855d43f3d5415d43f5d5315d43d7d5715d43afd6815d43bed2815d43bf51815d43bf90815d43dbe5481d43dbd5481d43ddd5381d439fd5881d43afe4859560afe5859160f3f5495160bf61855160bdd3815160bed2815160bf51815160bf90815160cfd6495d609fd4895d60cfd6591d609fd5891d60ddf538dd60ddd438dd60b7e4859750bee2859350b7e4854f50f3d5450f50f5d5350f50b7d5850f509fe7850f509fe4859f50dbd4351f50ddd434df509fe484df509fd484df50b7d4899550b7e4859550b7d5899150bdd3899150bf908991509ff78991509fd7899150bee2859150b7d38d5150b7f78d5150bf61855150b7e3855150f761855150b7d48d4d50b7e4854d50f7a0854d50f3d54d0d50afd68d0d50b7d58d0d50bf908d0d509ff78d0d509fd78d0d50f3d5450d50f5d5350d50b7d5850d509fe7850d509fc7850d50bed2899d509fd4899d50bde3859d50bfa0859d509fe4859d50b7d58d1d50bf908d1d50f3d5491d50dbf4791d50dbe5491d50dbd5491d509fd3891d50b7e5851d50bf61851d50f3d5411d50dbd4711d50afd6811d50bdd3811d50bed2811d50bf51811d50f5d538dd50ddd538dd509fe488dd509fd488dd50bfa084dd509fe78597409fe7854f40f9d5350f40bbe5850f40bbd5850f40dbd4355f40dbd544df40ddd534df409fe584df409fd584df40bbd4899540bed2899540bf908995409ff78995409fd78995409fe78595409fc7859540bbd5899140bee2859140bbe5859140bbd3895140bbf7895140bf61855140bbe3855140fb61855140bbd48d4d40bf908d4d409ff78d4d409fd78d4d409fe7854d409fc7854d40bbd58d0d40f9d5350d40bbe5850d40bbd5850d40fba0850d40f7a6554140f796554140fba6454140fb96454140f7b5454140fba5454140fb95454140f795454140f7b5354140f795354140fbb4354140fb94354140fba4854140fb848541409fd5899d40bee2859d409fe5859d40bf908d5d40f3d5495d40f795095d40d7f5795d40d7f5495d40d7d5495d40dbf4395d40dbd4395d409fd3895d40bf61855d40dbf4355d40dbd4355d40d7e5855d40dbe4855d409fe3855d40df61855d40f3d5415d40f795015d40d7d5715d40afd6815d40bdd3815d40bed2815d40bf51815d40f9d438dd40dbe548dd40dbd548dd40ddd438dd40df9508dd409fe588dd409fd588dd40bfa084dd40bdd38d5130bf908d51309fd78d5130f3f5495130bdd38951309fd7895130bf61855130bdd3815130bed2815130bf51815130bf908151309fd7815130bde4854d30fda0854d30f9e5450d30f9d5450d30bde5850d30bdd5850d30fda0850d30fd95358130fd94358130f7b5454130f795454130fd96354130fd95354130fd94354130fda3854130ddd4355d309fe4855d30dd,0x5d40dfd3855d40fbd6415d40fbd4315d40dfd6715d40bfd3815d40fbd548dd40ff9508dd40dff578dd40dfd578dd40bfd588dd40dff548dd40dfd548dd40dff588dd40dfd588dd40fbe544dd40fbd544dd40fdd534dd40ff9504dd40dff574dd40dfe574dd40dfd574dd40dfc574dd40bfe584dd40bfd584dd40ffa084dd40bfd5895130fdd3855130ff61855130dfd7855130fdf5458d30fde5458d30fdd5458d30fdc5458d30fde5454d30fdd5454d30fdf4854d30fdd4854d30fdf5450d30fdd5450d30fdf5850d30fde5850d30fdd5850d30fdc5850d30ffb5458130ffa5458130ff95458130ff85458130ffa5454130ff95454130ffb4854130ff94854130dff5459d30dfe5459d30dfd5459d30dfc5459d30dfe5455d30dfd5455d30dff4855d30dfd4855d30dff5451d30dfd5451d30dff5851d30dfe5851d30dfd5851d30dfc5851d30fed6555120fed6855120fed3855120fef5458d20fed5458d20fee5454d20fed5454d20fef4854d20fed4854d20fed7854d20fef5450d20fed5450d20fef5850d20fee5850d20fed5850d20fec5850d20fed5355d20fed53d1d20fef5351d20fed5351d20ff75458d10ff65458d10ff55458d10ff45458d10ff54854d10ff65850d10ff55850d10ff563d5d10ff56355d10ff563d1d10ff56351d109fd3891d659fd0891d65ddd584de649fd3895d649fd0895d64bee28593549fe084df549fe3841f54bbe48596549fe084de549fe3841e54bee2859154bbe4859d54bee2859d549fd088dd54df56785d54df53785d54bf50885d54df56585d54df56485d54df56885d54df53885d54df50885d549fd3881d54df61741d549fe084dc54dde684dc54ddd684dc54dde084dc54ddd084dc549fe3841c54ded2841c54df51841c54dfa6841c54df96841c54dfa3841c54df93841c54f3f5495163bf61855163bdd3815163bed2815163bf51815163bf908151639fd4895d63cfd6591d639fd5891d63bee28593539fe4859f539fe4841f53bdd38991539ff78991539fd7899153bee2859153bf618551539fd4899d53bde3859d539fe4859d53afd68d1d53b7d58d1d53bdd38d1d53dbf4791d53dbe5491d53dbd5491d539fd0891d53b7e5851d53bf61851d53dbd4711d539fd4881d539fe7859743dbd5441f439fe5841f43bbd4899543bdd3899543bed28995439ff78995439fd7899543bde38595439fe78595439fc7859543bbd5899143bee2859143bbe5859143bbd0895143bbf7895143bf61855143fb61855143bbe0855143f5e6554d43f5d6554d43f9e6454d43f9d6454d43f9e5454d43f9d5454d43f9e4854d43f9c4854d43bde0854d439fd5899d43bee2859d439fe5859d43bdd38d5d43f3d5495d43f5d5395d43d7f5795d43d7f5495d43d7d5495d439fd0895d43bf61855d43d7e5855d43dbe4,0x60efe5458d60efd5458d60efc5458d60bfd48d4d60bfe4854d60fbd54d0d60bfd58d0d60fbe5450d60fbd5450d60fdd5350d60bfe5850d60bfd5850d60dfe5495d60dfd5495d60dff5491d60dfd5491d60dff548dd60dfe548dd60dfd548dd60dfc548dd60f7d5458f50f7d4854f50f7d5850f50dfd7850f50dfd6351f50dfd484df50bfe4859550bfd7899150bfe5859150bfe7859150f7d64d5150f7d6595150bfd3895150f7d6555150f7d6455150f7d6855150f7d3855150f7f5458d50f7d5458d50f7e5454d50f7d5454d50f7f4854d50f7d4854d50bfd78d0d50f7f5450d50fbe5450d50fbd5450d50f7d5450d50fdd5350d50f7f5850d50bfe5850d50bfd5850d50f7d5850d50ff90850d50dff7850d50bfe7850d50dfd7850d50f7d5499d50bfd4899d50dfe5499d50dfd5499d50f7f5459d50f7d5459d50bfe4859d50dfe5459d50dfd5459d50f7d65d1d50f7d53d1d50fbd43d1d50dfe67d1d50dfd67d1d50bfd38d1d50f7d6591d50f7d5491d50dfd6791d50dfd6591d50dfd6491d50dfd6391d50dfd4391d50dfd6891d50f7e6551d50f7d6551d50f7f5451d50f7f5351d50f7d5351d50fbf4351d50fbd4351d50dfe6751d50dfd6751d50bfe5851d50f7e5851d50bfe3851d50ff61851d50f7d6511d50dfd6711d50f7d548dd50dff478dd50dfd478dd50bfd488dd50dfe548dd50dfd548dd50dff488dd50dfd488dd50f7d544dd50fdd434dd50dff474dd50dfd474dd50bfd484dd50fbd5458f40fbd4854f40dfd7854f40fbd5850f40dfd6355f40dfd584df40bfd7899540bfe4859540bfe7859540fbd64d5140bfd38d5140fbd6595140fbd6455140fbd6555140fbd6855140fbd3855140fbe5458d40fbd5458d40bfd78d4d40fbe5454d40fbd5454d40fbf4854d40bfe4854d40fbd4854d40dff7854d40bfe7854d40dfd7854d40fbf5450d40fbd5450d40fdd5350d40bfe5850d40bfd5850d40fbf5850d40fbe5850d40fbd5850d40fbc5850d40ff96554140ff96454140ff96354140ff95354140ff94354140ffa6854140ff96854140ffa4854140ffa3854140ff93854140ff87854140fbd5499d40ff95099d40bfd5899d40dff5499d40dfd5499d40fbe5459d40fbd5459d40ff95059d40bfe5859d40dff5459d40dfd5459d40fbd64d5d40fbd43d5d40dfe67d5d40dfd67d5d40bfd38d5d40fbd6495d40fbd5495d40fbd4395d40ff95095d40dfd6795d40bfd3895d40dfd6595d40dfd6495d40dfd6395d40dfd5395d40dfd4395d40dfd6895d40dfd3895d40fbe6455d40fbd6455d40fbe5455d40fbf4355d40fbd4355d40ff95055d40dfe6755d40dfd6755d40fbe4855d40bfe3855d40ff61855d40dfd6555d40dfd6455d40dfd6355d40dfd5355d40dfd4355d40dfe6855d40dfd6855d40dfe5855d40dfe4855d40dfe385,0xb8028e025b021f01ec01b9017d014a011700e400b10075004b002d002d002d000f000f000f003c002d002d002d002d001e001e000f000f000f000f000f00000000dfd3891d65dfd0891d65dfd644df54dfd684df54dfd484df54dfd6441f54dfd6841f54dfd4841f54bfe3859654bfe0859654dfd654de54dfd684de54dfd584de54dfd084de54dfd6541e54dfd6841e54dfd5841e54dfd3841e54bfe3859554bfe0859554fbe4859d54bfe3859d54fee2859d54bfe0859d54dfd674dd54bfe684dd54f7e584dd54fbe484dd54bfe084dd54dfd6741d54dfd3741d54bfe6841d54f7e5841d54fbe4841d54bfe3841d54dfd684dc54dfd6841c54bfd08d5163efd6595163bfd5895163bfd0895163efd6555163ff61855163bfe0855163dff7855163dfd7855163bfd0815163dfe5495d63dfd5495d63dff5491d63dfd5491d63dff5481d63dfe5481d63dfd5481d63dfc5481d63dfd4841f53bfe4859553bfd7899153bfe5859153bfe7859153f7d6595153bfd0895153f7d6555153bfd4899d53dfe5499d53dfd5499d53bfe4859d53dfe5459d53dfd5459d53f7d65d1d53dfe67d1d53dfd67d1d53bfd08d1d53f7d6591d53dfd6791d53dfd6591d53dfd6491d53dfd6891d53f7e6551d53f7d6551d53dfe6751d53dfd6751d53bfe5851d53f7e5851d53ff61851d53bfe0851d53f7d6511d53dfd6711d53dff4781d53dfd4781d53bfd4881d53dfe5481d53dfd5481d53dff4881d53dfd4881d53dff4741d53dfd4741d53dfd5841f43bfd7899543bfe4859543bfe7859543fbd64d5143bfd08d5143fbd6595143fbd6455143fbd6555143fbd6855143fbd0855143fdd6554d43fdd6454d43fde6854d43fdd6854d43fde4854d43fde0854d43fdd0854d43fdc7854d43fbd5499d43fdd5399d43bfd5899d43dff5499d43dfd5499d43fbe5459d43fbd5459d43fdd5359d43bfe5859d43dff5459d43dfd5459d43fbd64d5d43dfe67d5d43dfd67d5d43bfd08d5d43fbd6495d43fbd5495d43fdd5395d43dfd6795d43bfd0895d43dfd6595d43dfd6495d43dfd6895d43dfd0895d43fbe6455d43fbd6455d43fbe5455d43fdd5355d43dfe6755d43dfd6755d43fbe4855d43ff61855d43bfe0855d43dfd6555d43dfd6455d43dfe6855d43dfd6855d43dfe5855d43dfe4855d43dfe0855d43dfd0855d43fbd6415d43dfd6715d43bfd0815d43fbd5481d43fdd5381d43dff5781d43dfd5781d43bfd5881d43dff5481d43dfd5481d43dff5881d43dfd5881d43fbe5441d43fbd5441d43fdd5341d43dff5741d43dfe5741d43dfd5741d43dfc5741d43bfe5841d43fde3841d43efd64d5160bfd38d5160efd6595160bfd5895160bfd3895160efd6555160efd6455160efd6855160bfe3855160ff61855160dff7855160dfd7855160bfd3815160eff5458d,0xf65ee65bb65916567652b650a64d764c864a7647d6441641763f663cc63ab6381634e632462f162b862d962b86297626d6243621061d461a1616e613b080760f660b1606c60395ff45faf5f735f495f0d5ed15e8c5e505e1d5dea5db75d7b5d3f5d035cc75c8b5c465c135bd75b9b5a005b445b1a5af05abd5a815a335a0059c4597f5943590758cb588f47bb585347bb582957ed57b156a0577e182d5742570f56d33fae4f2656a0566456285607560755e655aa556e553b551154ba182d5487544b182d541853ee53c4182d539139b4398a5367532252ef52a152655232520851c35187514b510f50dc5097505b501f4fe34f9e4f620ad14f264eea4eb74e844e514e274dfd4daf4d7c4d522f824d164cbf4c8c4c474c0b4bd84b9c4b604b244af14aac4a794a2249ef49c54992494d491a48de48a24866482a47bb47ee47bb47914767473d471346e93ae646ad467a463545f945bd456f453344ee44c44488182d182d4455182d182d441943dd43aa437743443150431128923d5042d542ab38134278423c41f741a04164411f40e34068402c3ff03fc63fae32103f7b3f513f273f0f3f0f3eee3eb23e7f3e4c3e2b3e01182d3dd73dad3d7a3d503d143cd83c813c4e182d3c093bc43b9a3b5e3b223ae63aaa3a6e3a29182d3a0839de182d182d39b4398a396039361daf38e838b5388238463150381337ce37923744370836ba367e362735e235a6357334fb353734fb34bf347a343533f933f933c6338a334e32f732c43288324c0ad1321031e631bc3192317131713150312630d8308a305730122fc42fa32f822f342ef82ece2e892e56182d2e232df92dab2d782d452d002cc42c912c552c072bd42ba12b6e2b202ae42aa82a632a2729d92994294f291328b32892287a282c27e727b4277827602748271e26fd26ca26b22676264c263425ef25bc25922571252324d524a2246f242123d323b22391235e08070ad122fe22cb22a1225322050a1d21ae21692136210c20e220af206120131fbc1f651f201edb1e961e511e271dd91daf1d731d371d161cc81c681c231bd51b991b541b061aaf1a4f1a0119b319801944191118d518ab1881184e182d182d17fa17c71782174f170a16ce169216561611135915de132f15a21566152114d314a01452140413b613831359132f12f312b71272122d11f111a31155110710cb108f105310170fed0fba0f750f390efd0eaf0e7c0e400e040dda0d9e0d620bd00d2f0cfc0cc00c8d0c510bfa0bd00b940b6a0b250af20ad10ad10ad10a1d0a950a4706900a1d09f309c0098d09510600090c08d908b8088508640828080707d407860741070506e406ba06900666062a060005d605a605be05a6057302b80537014a04fb04d104950459041d03d803ae035a038d035a028e025b032701ec01b902e202,0x16e380840bf1c040a1228d00171c14286003d0e1f1c043063a1c3e38085e802b8e0e010bd0054538e02618c01e870f8e021701d0e1f1c042f409bc70b0245e870f8e15048a01e870f8e440c8dc70c8881221401418243051009201a3fba3daa3b9a398a36ea344a31aa2f0a2d8a2c0a296a263a239a218a1eea1cda1a3a182a161a137a10da0eca0c2a07da0389f6c9f549f54a0059fc09f8d9f6c9f549f549f339f099ed673fe9eac9e8b9e6a9e3771e29e0d8b3b9dd19d8c9d629ae09d389d0e9cf69cd59cb49c8a9c699c3f9c279c069bee69ab7c5091da9bc49b9a9b679b349b0a9ae09abf9aa79a8692e298fd9a779a449a239a02736b99cf99a5997b995a910871e2993098fd98ee982e98c4989a9882984f982e980d97e397b9855697a19789977a97597c50972f96fc96d29696966c964b962a960995d695be959d77c19573955b9531950794dd94aa9480944d940893d59399935d933c932d92fa92e292b89297927f748b925e923d9213739b91fb91da91a7917d91539132723c910871e290de90ab907870ef903c901b8ffa8fc78f9d8f618f1c8ed78eb68e958df68e6b8e386a658e058df68dd58db48d938d698d518d308d0f6d178cdc8cc48ca389228c798c4f8c258bf28bc88b9e8b7d8b5c8b3b8aff8acc8aa28a788a4e8a0989df892289c789a68985895b893a8922890188d788ad88838850882f881787f687cc7d70878a7d4f87ab7164878a87607ccb873f7c92871586e27c5086b8868e865b86287d707b3c860785d485a1856e85568535851484ea84c08496847579b6844b842184096ee56ee583e883c77722839d83588340831f82fe82cb828f826582448223820b81e173e681ae74ee81848148811e73fe73e680fd736b80ca80a0736b806d804c802b800a7fd77fbf72127f9e71e27f477ef97ed87e2a7eb77e847e6c7e397e2a7e097dfa7de27dca7da07d7f7d707d4f7d2e7d0471647ce37ccb7ca17c927c687c507c267bf37bd27b967b6c7b547b3c7b1b7ac17afa7ad979b67ac16ee56ee57aa07a767a4c7a2279f879ce79b67995796b7926790578db78c378a27878784e781277fa77d977c17785776d774c7722770176ce76b6768c7650761d75ea75ae758475636ee5753973e6750674ee74cd74b5748b746a7449741673fe73e673bc739b7383736b7338730e72e472ba7287726f723c721271fa71e271b871857164713a711070ef70b370927071705070266fd86f936f4e6f246f0c6eeb6ee56ec46ea36e826e4f6e406e286e076de66dce6da46d8c6d6b6d4a6d176ce46cc36cab6c8a6c606c3f6c1e6bf46bd36ba96b6d6b556b2b6b016ae06abf6a8c6a7d6a656a3b69ff69d569ab6978693c692468fa68e268c168a968886867683d682567fb67da67b96798676e675f672c671466d866a5667b6651663066,0x842b0f81880d881f29940178761e208447431787e1902238821101f2994017872050f1042243e532861c17c00b0fd045f00145d16861bc41084a1f03101b128616e0620362f430e98e00448588a191874fb4380440b02b10461c881f2994017c0a1e209c387c2c532802c85c0c412178430ca7c06686c78405d9ac329f00363a7c16c4e00ad9a601d3ecd05b13802b300ecde006cc02445a00b00846160a211001e006c14230c0308e033436300581c38406c84306c302b0d3ed02200616c30510882227cbad066807810b61828a00b37a0c3e0028223b419b872242f800105101766a1f801b050c9f0c34003c38590870c3419ac322702160122109f0c34186cd00c2f80486386d085b0d9a0b227000253419a44e002a16c300909f6833403c0858281c407b804dc4044505b0c23c0c40786219003d0b210ac326f0089880f0c43e0078582137801e16081ee050f1011178e020506532871f100214a7d0e3e20042b0ca7d0e393710091ca650e38082c2a602dd0e3d0f10021d31d0e3d0f1002182cd0e382b10021a86532871f1002182c14299438f88010ed002f1c040a140bd061f1c1402180ac3e871c140219a04d624538e05050e866230c2ed0e3c50144063a1c7010585840600b80e870f8e02209ac4e802b8f146181488a34188c3e3e00141621a001e3808142b438e0a0109c78a0605623418601e382804300587d00571c0433419a448a71c020a1d9a860bb4229c7050e18e870f8e02008d080c00701d0e1f1c0443419a44e382a28c30090d066a1803c78a0281c414ca1c726e2012314fa009e3e2032314fa1c72262032314ca1c70ce20123613801a0509041007f801817a1c3e44340d04e38f8dc20803fc00c0d8dc20800dc70c0c06c6e1281d0e1b238e44358fc00b06c5607421bc70b0246e8723070de38246c1f00221813a1c80ce0f8e091ba1c3e3c3710091b1bc7e062040287e09c0c40805e870f8f04c4064600f038e02050a01e00638e02870c0d02063a1c3847038e02278188100444e870c33c7c4024629f038e2b101a16e802b8fc0070e4da8703101117801105074d00a2387c00d8d872330317c3a6e223647009b880d884f26e203621370fc00b06c526f0089880f0b43e822c15c02e8c4200f4287c005044766c2f801b300bc00d98038594f801b158bc01586c30b90803c0088286e006c1418059bc3e006c50c423a1c3e00461642208401e803b800a088e1185f4015c0618dc03006c303f003660109bc0088604e00782c111003c3e0110841e1a87c008860434d43100210040a0814020b005f2d408142f4387c726e2012374387c70ce2012371c9a090c09d026e238e16048dd0e1827104d2e0d80e81378e16048dd0e181b11c72691070c2538e52138e180107d0a1f1c14021431d00b71c042f4187140571c04161fa0,0xdc7a18600420078e0aa18085098438f430101460084c2188e3d0c043f4380234c01687c7c400894688f800a0b620611d0f80162980b10384c21c7e062046307fa00d0401006130801801c711814d08a2d8fc005014600d438fc0c40806c6f1f800a104c0a08a605e3e2004281511c70109c7e00082c20082c171c2c020c261001f1f801618a68d02f00022f4387c7c400850685804180780160109d0e38082c27418e020b09d0e38648816141a0ae005840ef01a00ae3814609d0f81d0e38146030042605e86238fc0a19205e002b8e1d1426104271f81880e8e230eb4015c70700872980b1023104616e014c05881a27d011f1f1002184698e871f10021846d0e382b1002182610e380b1023184613087038f88010e11010283e00449a0a138fc0050984e3f004c0a138e01010284c6f00220a13a02329f1f800161e20829f1f80040b0b90c1e238e0214a60ee3b0f100218a7c7a1e20042f1c0a04a1f00144d1c2610c471e86021b10050984381c7a180880984381c7c40746098401a08e071c3a0120a7c7a180710021a08040eb438e01e002b104f1c022329f0287881c3bc7e014c05881ba00ae3f004628041bc7e034014305c0a01e38081430178e04e034014306003c7847009a841c3005e3c23804d420e18e870e11c7010c05008281c02149a01e00282cc3180a010571c1c021ba0840201447c7e0029864f1d0818e005850c0238fc000858602d438fc0c408060b8138fc0c4080600a238e021381c7010044268638001138e020087c7c4008389b0c04011047d0e3c4c03c061e208098401c01e3f01878823a1c3c471c04285803c089e2186021fa1c702f022602c430c8e0008021f0004160c0a0109f4311c0e3b0c8c474386c0e380860271c02021031d04471f8005008fc702f03100217a0c3e3808022f0c36020089d00791b86c0e393402454015c7e000454c03687c0008b434c71d081de0620711c438fc005004600f000b43050a130850f8fc0008c050984003c7e062286471c03c00508c50ef00a64d470a05e014c9a8e143a05098409bc7e02388c871f804426e386c871f805311a3861184c2001e3f011c3e421a068271f1c308f2053e3913804d47101f0e643804d226387c803c0dc7221371c394f21c7e01102c308c02130860f8fc02213710514f80160c3a0a0846980b6438fc0224388c800931c7227021c388ca7c0076205818082c53e06206118282100ac2e3a0c402b1031c00b06180105b810e14302b0ba1c7057001a16184605e002840282828871f8016050101c384c21c7e00585e871c1416138e0a0b06234c0048983e005b1042601dc72260c1bc0c41001e00281a0e1447c0050341c284c200e0271f07c0c41006c18582610c471f804028020e0c142307060bc3a44144214bb870f94ca00b26f018788288640c406c,0x164a00838a14ca4194ca5140308532945088214ca50f8a0185c809825c7e002860b89b8fc0050acde3c13800a142425e071c14286a2188c1f0023021c261001f038ec80e8e130430f81d0e381470df038e26010a130800f8fc06408c70984010c3e3f00023e230611e05420437038e260109c8e18478150810c130850f8ec8010c9b6813190c3e380871130da0c8e38086e870f8ec8010ac861b438e021591c7e1809362b2186d00cf1c12334190c30cf1c12374191c30cf1c12304c21c0e3d20043152a148a1f1c04304c21c7e043590231f81c7823402c2f1c46c8e04343633438fc086b2046304c201f0381800c38680490e700361613a1c707858463825801b0b0bc761807810d0d8cd0088258ec061c340243438fc0820585e3e2307c02686c686e200d04c871f063f1c4788e0134363623064de01703c371f11832793436371c0383e01343632401bc0e3e0c30307c350205098386f1f81500c0c130871f0602028d8de3f00880a143e1ac6c13800a1b2188c1f1c04288f07c7e05403036378e44e002850e94f81c7c180860ef03a083e38086e01102c1f1c04160c26100471f8016183a5346f1f80231ba1c8c1f1c04288f80020b08230360c3a130871f814824b1c7c1d2004284c21c7c180802371c09c026828508f00d20a109bc7e002842871f8004050a23e38081422b8bf8da8413800a1f8e2511f00142f40a7c700f004783641053e871f80040b0d88e860f8e0217a1c7c1808429f401dc7c1b2004388c25c7e007414308c1bc7e034014308c3a12e3808143077801b680285100778150e3c0c043883815081f1c043083a1c7427002c3083a1c7e008c2c3074a1c0e388c14c81c3b83e3f02a018182404e3f0306181847c02820f8e021ba002e3f004628809bc7e008c5e87038e02118bc0e38084627038e230108130803847c7e060d904723a183e38085e3f0046021307d0e43038e0218461d0304f07d0e3f01904f4381c711808510077a1c0e3808463877a183e071c0436138fc0268285e400b801b3488c604f23a1c71408c664703a1c70108c62c0378148118a58e38144783e0520711f003a0aa40a1d0308c2610c1f1f8148278010e3883102f0310200d8983e0137101b161a068260f8f90c40e23e0137101b1707c026e20881e181e06c1937101b1b8f8300f009a1b192004e071f102019200de071c4188182604e3f00562f0310206688cde00822e271f810d05081f2d02a04214c05880e88230ef00148d070c1de014c058814261046f1f8188118f0dc471f8020a80d13e871d8788010c1d8871c09c0056221a404c21c7016203a30742610e071f10021f8e05010284a80044dc7e0028606f1f8044050a1fc6c10b5c0050c1d29f000ac3c40c5306f000216172183e3e2004294c1cc3c40085298168788010a9802f1e8788010,0x8285c268d81b00083008a650440888010583028084618458e10118613280853280361088144a132830c41284c20880142066380826101026c3680602a014ca088140340c40084440080340218a05008083618080a18958f400c26c3a0111a0281404100802c30ca65006d1e8602a042110484ca10d8451e86c3a0100da1814311b000a180480050150c584014211d0d8108028a050408c0028616041c050a86160809436005841186480194c11187404188d00020c461660008411b0004186004106c0453c408180404538406c40123820d8084c5311a0c7a006c042b404c020c4c1b63a238002183a88e000840d94c24414c202900041d0c3a020c14020e86020e841900a003840091043118143c40084c400c04011004430088c40e900058810058808084311861d0130310234310c702009800a1da0260c06d0638943024103012103a4d0c9a23842104684358e18104c180bc3586841a108409870802860e0b04c7028058008010d500085504206030c014035012101b4407506006c0508168e1b08364da385c4128602f4742134612d401a040b8a178384c1a1b142e1383b00360d191002299404440088618358e132808532842008881710020a1004008688268426099418e208c1c010c0413080613638084b081426120804c308042384004409b1da01805861500041220054029940502d031002102c01a000840280a80c311100500d0004289a80104d8f4026b4050280803c0100ac30880020a001301340463c002602680b0009848300c0004c3100b000130c409f01a0184d8ec30134380301780020c03c0010605e030c30b00987c010a688a3d0c05408406c8a82228e040150014384e114763d0e801b1c1c02618044a18042a1a20021801dc4300302806861c2108880c3a84a1b03102804106804211858021936860e0c1c0108468407134406d0c20ee20021b009b430da0c76021014288c1a04a18385049002c18041c1100040e0c2c02e023842000b1c18242dc00e10882984842984a10194c250860090863b00a612070d080b04166040c042059a00ac408c0010583224201c1c2088c0818085c40303118416013031023418ec0c411014340d06172988532840d06214ca10341b00563c0d80172983860713426060c044d102d830906c001062b09842b098103600ac261b1d80131588040b050e023002c234014160c08c00b0644068383223021c0d101a088c1a44008385600582680358e44600286299368044680a8b217003622202dc021081b2994836014ca41c2286160c2d086050c842b4015880b0988601082c20b4421f6802916313489430f10446050c84293412691086185910c02108d026a2d8011050c1f1482d86211216160e38c31607c48e07c581c2110532908532942110441610942994848431d2853290a430104,0xc09826810c2612104a1308b1da028758002a1882300b2030d80826171026c70d86056052004208c02c30f0020130648c00604c206f8fc00109c01330c32386f8102104c110491c4bc0640e1363d0180500150c70e82447c0640a1363d018050015207a03008602a40bc009b403e00082e00158618942743680813a471f801b14261226a0c42004c24186c26120c261226d01062a208013090812088251087e00d834471f801b098487098489a0410881309034409849800d1030120830120206c009060363b003012100ac0010623099404c208004144027830ea02008415011874428236061310a10301300262898260401d405098491a041026126001044194ca0184ca0101026500c4a0894261081a0c56384c20184d06d00d0602a014ca028942650a00813a0111a02074468d0c4640013204299401b03418b0d0402c00ed20411900041d12061d0a110300b003a2b40141d0c08c00e86d0055202c252008c00b0802100453c1842004a7030d862368098a623418f400106c56820ca626104c1b63a0f8002180a83e0008413081a01b1c40250e1ad010062609435a0841606840806c80e86230ea1206208ea01542088410082310076a022120750418903013010750144a11a3e0c40d9368f83090a2510048a14742134712d401a04090a1183a102612068c13090460ec0068c532860c368020d63e0c26501404c808a6500260c40260c9a1a0c9a10041c230d06130806136389606208d90120e80020c05402994306287681830108230ed0004209a80d00c461d0170040e90004c81032838004da028258f0009b40509b218e026870060ef0004188f80020c461d0170190285804c8e00853a451e801bc18c13a451d8f40c186c70883b8fc06400846381290230c07481186056008e902074802301520502c0d8148118a23041ac01186160088c326d201c1a10020e26880da4040511e0c36013690183690040083851183820b84c36186c2e1326881b2005c26220c361709881709d01204d142f400986c44470036021106170987902000830982780185c220943a0f80362036830985c50b84a10131036130942040984a10c010370863b002e13090f032005c26206d26106c2e130e061b4987908190d2621112e200c2e1308801709864d0b84c08205c26c00208170986c1a206c2e136003451005d9a185c4013002e200d8ec01005c40ea0004187580020c04011354040114f101b1c042529880229942108815a1404400846831c4a02104ac74470004288c2c88e00085840082c185a86c08400850b3401402c40a23013002d881402020a10021186020288c3c40168602128623c40084c400c0a021310021186232000b10205b100211880e118409400583a851c0a1a351107088811a82360ec00142071350c22250c2e18982e440d1b030b84c,0x1130980c4c209a26c80d8e1309062609b40311b000543118e020985c41304d86d01002c0a40084100982]
def g223H8 : Nat → Nat := chunk #[0x68dcc00033cc0001ca5c000381c37be00000000000e7af8cd00000000000000031de3bf2a15ccaf6d89f81e500e000193bcac2c7d445ec00038ba00008efb624caf5562181926169915914e0001046a88ee1c8eea7d59fc1000016a1ccbb4b9000000000cdc91c0c48e443a5968000000000021084a610000000000020bb3443ea38000582400002fd9958907357df715c0000000c4b400034b4000000010c2c0007218f33b06f741bf0cc0000ed5261e0000f25d83140007406567d83f4415f06a0000000381df2026184e5206304866c115a77a0b68000800800014c2800000010272447c8546709a4c007800000000000030000180800400001c000060000280000300e0000000300000000809002014008000000000201100400c0000a0020000380000001005807002000000080040000480000006c0000000e01001000000014000020000040080300a010058000120a80080602401c0000600a01800000004008030000020000180e000004040020020000d80200e00009001054000000000080300400200a01c00006004000010180240000000600e00000805012000010000000000300000201407008010008000000000a80900b0000000000300000800002008004000000060000800100201403009002000030000060000200000a008008040000080000301e00413000008000028000260200100500a0080180700a008010000000040000000200c000040000180100300a000018100040000080000200000002000024008060180040080003e058018010060000180001000400001004064060000060140000a04e0080001000200c0080000a0000380100a0100080000a008020000000000080100200c0002900001000803008000020000020400000500200c00005000008000000160000000000a004000000060080000400000000808006008000010360080300400403401018002000018030020000000000000000002008004010000000000000000602804800000004018000060000000f00a0040000303e00c000040000040780000000c0280101000000008000000000190000000000000000c008010000080000201801c01803000000000250000000b00000800400000000000000050000000280200a058048030040000080200008400803000000008020140040b80801200802002000018010030040040300000a000010170040000a00001a0000000300a024110140000040200100000c0080002e0000080101801c05805028004020000080680000301e0000180000c01c008000000180000400c0000000600e00c000030020040680001806000000000000000020060400000000000c040030000240580100e0000000d0000280300000002401803002004008000000040180800c000000000000000300800000800000,0x77818b5ca6f1b1b7bc5ae0ad6f5b13633512123e3dd55341f086d1265596e00000000000000013060001f0600007a92f5228ad4000196ba3860001c82542815af0c03c59c2345809c02ec5fac430000000143839be94c80002decd2d4d45660c7105086e000000010b068f227c0849e207800000000000000135200015118000000054cb306f55cba95c77b28be41fbaa8e74400010f2a245c76f491a04c7372b371c9d8000540a8383e8974669463f50ae57110a7beb000186380000000a65d65080007b9bf3c3e0e3017934b466b50d8e2cd43891b3661f574cc70000103c71e98000e14bc8d80002235000000019e3e320f0c66a285f2e9af51cea6d99dd5462b3d0cfb5d9cb90cd5c7c88f634919be4538738000085cd423a7e4cbaa429f12ee164880502096ee4f3c622aa1d40d8232800060920001a005e354a26a4458463499908810aec088c28eb607635a0096183371000081dd9a0e16e45ab6c324a1a0acb31be55c000341d861cc64c00008410000eaf94a5992143330e70433e290c2270db14a53c3748326734000000000018fd4000000000000000000000025ec00000000000b0de0000000706100018c1000061a3b69cd0d3219b94783cc00035df92aa00018a7cc736a380000413a90b99bc755be0c0954f1df127f503b0e348eff58ec90800000000000000387400002670000187ce46f347c0002c1a800047f2869e926f0c9261063d0000489ff2e8000000071a8000000000000000165200015c69c22d5a6cd6dc9ed2a7c7936f52d3819a587ce835b8dd79faa3b54e16469681a31b6486d07b5375c83cc5cf0b61a3794ff4816960781626a0a78b93e1c05c3960001140800000000003d2dcb7037560000000688000004e800001ad1d81648fe6256102d1bf299c00000000000b17961f2a08b4be2d8442428cb540980b0845c8d527e223fdd41616328a061e99e17060973b063093c3b5a43da25249e4598064924eef9eea80cc4cd8da8d4198b9103f23821f45c67d5ac69a562b1b6df099e3abdc9a26ec7610e655e6e95a3275909f4d5592348a46b655e0f2cfe1a6ae3f97519c9e029e6108a833b4a655a7c6610c83e601522b48b7d1b7666d2e310342c680001074f0220000e465a9b557cc9ff3834000060a127d0000000312928e90000000088a000000006b1163c9b53512ccec94da5c0325960002a1268eb517890248ca7b819612a7d9d87faff281a9150cd4c40c62bc00009a4698224500000000000000004cfc50969f2000130ac83ea156651a66eee35b181e3b7e156008734f607448b1903c0f855fb0ff7c415a5591dd2a8f5704240c02e263ee26c32bf658865e963401114aea2d8de842b6f838a806c5bb89e680146afc39613bb0eda479dca1177571767bd60f98e132a6ad89a3691d072ba847fcf3d951520,0x966693618eb660001633b9eddada978186b74f668aba4bcabf25acfb44519e2b328acaa3154e800005223b80000000000000000936271134311a71f496c4485a059fce080b097937c47700010465d81934d512000011d2f369000150ea57f7ac3509b0671c76c04ff6662503c9158a300010d9746f099aa15f6b0645f6b79b6754ffe617f965c0dac72bcb8482132aa31cdd06f32394a0ac08ce65260a5d8449893dd87fa74766830c5317938477008000000023b8000000000002164402580ca19111a1c0c880429c2d02a0003cb5317f00018a5250b000000006a609bdd0fc3320000000028d8d71400000000000a16a87deddae8a8000000024f1c9e40000000000033e268b864700000000514400018878000000067d185c0000c18800000004b1842be204e1f649d90001cddbc507bf743ddceb949880005417c48389b5bf876292cc85185b5528d9ef0d8c47b7aa8eaaaed4aa1b19c8abed1ecbd7aeed8bb704655d3bf4b8b08226dc13b42b755445e86e627ea8f5e76117248c816bdebcd1d208035500661b002a101a0858252812f109a64ea974998dadf81836776a04113c60f00000d0c8884308e0003cb0f3de389c24bfd0a80003590a505d86800080d60000000085b0001478399ea0e5a72a914400000007299c9709354081a41800000000000440ce98aa09889b42e2c20cd927b3ba10fe31ca39514e00000002982f8c6000042a7188800060f9ca1104d4afa00012b880000000826b04d2d5c0000a2212ab80000000d8960001156422e664b82c40004bc40000280d9be8000d02424a2cea000072a58ac963a0000d890c754000000000000000d738833000000029f1b82600000003d1d8000b78a8add842f000608d81d25f7288cc65e4e0fa20e253a72525f58f4d35f172f610e54ed3d5662d059dcd090d7e7f7b0aace2c962d0e2a62dd9859b5214ce293a326028b72daaf10d9baf00001226597a3b74f5ef809ed83800000000001564fab4a21ae1ef84a92f25095e6c0d49c17c0001cba0000512ab448e9594249b49853768e586a1296773d6dfc9c3414fa0a4ad0e9f0f33c325b8ed8d8bf2734072ae22d47da79a3314fc28ff123378dd0ffb483c1387168a75ec07f2e1c483d0c8ccb5bb3601ae38d416a95883e72490985743d189ef04958ff91b107a8e3b54d3476d7430f2856d8a89e7d2ef6a90f000031b5e6b89910aa1545a26fecd923b9826f6c86a2ddc66c4a2c83f049fc01a64cea22cfea0f085de659b86ef9ebc079a06f5d43c26453850b9415000000018ebe124425852b60002c8b328b0000000180ed1d6b8f1e3b3429b27284542e1f555b21361a200000001378e59d20180006ba756fc287c0000b1b82c9cd8d8e41b580000000351ee227a3ea0000000707500000001d071b6ef8a6a62788470faa3d4000092,0xc1780001a8c00004c040002132000000038a680000001e73c000000037cc50d6194608677b1046a5690c1500008bb5c82b058b4a8705c0002aa20000671c0000000d13b2d300000000c858000361059d231606ec64556a8693f167455e948a1e5b1a1e494c9357f54908819682906000060d00000aaf634c44475a569ac517b719587d8000863b451a9345a1c000000004c18000606d88e8000419ec62b05e3411a312d24a000000063ade0538feaa213b91000143cddb3baca5771e5fa17d9ac5e82d4b99822e23c20b460b89251c4c709624adc9662a093f62a7855fcb9fb6b9f17e2204ba6d498000113af1a224c6667c0005aa545d6000182ea90ad1c56d1bdfe139a00000003cb919c40001af38000000000000001c60510bd7c80001521b43bd32425a7223e0f530ca70fec2fe87e00008eb157c7929b434eb7a461a34570a0cf73d66e145923b44e6daeeaf1a56109ea5be18fe00000001d04bb1c00000001a38800086ac00032039c61c7136fce1cc326b34b2acdf49f6c39a6c8af440007869463c2daf5278000f5ba00021000000000000004072944f7]
def g223D9 : Nat → Nat := chunk #[0xd3e33e0cca30a0c943198c283008bc42e18b382be8abc2a58a5028889d4265896024088a421b88201fc87b41df87401c086bc1a38622196062217b05ec16b8558148849e135049e116042a0fb03ae0dc032a0bb02be0a2025208501ce068016a04d00fe032008a015002e0000000ffc8eb2ffc47597feb26a9ff59654ffacaaa7fd64553feb3aa9ff4dd54ffa0eaa7ff5458fff2a2c7ff55163ff8a8b1ffd64d4ffeb2aa7ff99153ffac8a9ffe5454ffeaa2a7ff99d53ffacea9fff4754fff23aa7ff51d53ff88ea9ffe0754ffe83aa7ff59743ffccaa1ffd6550ffeb2287ffd5143ffaa8a1ffe6750ffeb3a87ffd5d43ffcaea1ffd5750ffe2ba87ff81d43ffa0ea1fff54583ff2a2c1ff55160ff8a8b07ff53583fea9ac1ffd0d60ffa86b07fd64d43feb1ea1ff50f50ffacaa87fe64543feb22a1ff95150ffaa8a87fd63543fea9aa1ffd0d50ffa86a87fe67543feb3aa1ffd1d50ffc8ea87fd47543fe23aa1ff8dd50ffa6ea87fd65d03feb1e81ff54f40ffccaa07fd65503feb2281ffd5140ffaa8a07fd63503ffa9a81ff54d40ffa86a07fe67503feb3a81ffd5d40ffcaea07fd57503fe2ba81ff8dd40ffa6ea07ff544c3ff2a261ff55130ff8a8985fd47996fe9bccb7f41e65bfc8eb2dfe37596ff03acb7f55e64bfa6f325fd079937eb2ac97f95d64bfc6eb27ee27592ff03ac97f59f54bfa6faa5fd07d52feb3ca97f55e54bfa6f2a5fd07952ff33aa97f59d54bfc6eaa7f617552ff03aa97f59c54bfa6e2a5fd071537eb2ac77f95d63bfc8eb1dfe0758fbeb2ea77f59f53bfa8fa9dfd07d4fbf32aa7df59553bfccea9dfd6754eff23aa77f81d53f7ac9a1fbd54d0efeb3e877f55f43bfa0fa1fbe6450fdeb2287ef95143f7aa8a1fdd5350eff33a877f59d43bfcaea1dfd5750eff03a87bf59560dfac8b06fd63582ff2bac17f91d60bfc6eb077d65d43beaa6a1df54f50bfacfa85fd47d42fe9bea1df99550efacaa877f54543beaa2a1dfd4d50efaa6a85fe67542feb3aa17f91d50bfc6ea87bd64d03deaa681ef50f40bfacfa05fd57d02fe9be81ef99140f7ac8a07be54503deaa281efd0d40f7a86a07f950502ff33a817f59d40bfcaea05fd57502ff1ba81f758d30fbaa6987dd434c3fcb0261fe54130bface985fd574c2fea3a61fb99520fdaca907ee64483f6b2241fbd5120fdca8907ed54483f62a241fb58d20fdea6907ed53483f7a1a41fb50d20fdace907ef57483f6aba41fbd1d20fda8e907ed37483fb32a21fd59510fecc8887f564443fbaa221fd95110feaa8887f454443fab1a21fdd4d10feaa6887f743443faa1a21fd59d10feeae887f557443fba3a21fd51d10fea6e885ed27996ee9bcc97b89d64e7ea92a5f6175527eb38a9774dc54bda4e2a5f517152fc838a93f59f43fd2c0907e940483f8a8221fc50110,0x4c0c7882018204f031cac513044dc7c02b184c3513031cac6c7c020171143031c342851d0dc0d00ac7020e214010371f02208071d0d43c0d088c70a02245c17000b1c2860d0850c0c70a1863411036231f00588180dd0c3c0c7880220143703402b1c083880d16d043c788c00a21401237031e20807175004038dc7c08820244c0f0342231c08588040543d088c0c70a23006c2832304c0d00ac7020e201f0220806c51300d0c3c788021c8c110f0342231c280891701c002c70a181143031c2851801d0c34d04c7c088246013430f031e2008801c004d00ac7020e2013410e231f002870d0408c0d0c3c70221403613031e2080717500d8488c0c720204c0703430f1e2008813d0c3c088c7021c34050f42231f002880818c0c72b1513402b1f003860320c0c72b145937402b1f0038713c7c02b10105b402b1f003870d44d00ac7c00e1d402e1d122c7b01342894d87508bc01b0a1d4136210f00442870bc01b0a10621e2f0f02206d3484dc3c0881b161c61362f0f006e21089500b434dc0881b1e1e2c63006cac61f8744428bd04388c00a4d2e1c7d35122d0f405a230028b504dc043881b1a1d350e2f422047002892f30c0110a15410d3700782c44729c3c01e0b111935130f01082c7871c4dc311c00b1e1cb941350f00782c4485088c7020a1542210f1c08286148050c7020a1863430f1e200861814d0c3c788021c6053410d430d371e2024a14809418c72b185a010e5342231c08289504388c70a021a010e5342231c082880cc719090a1463430d371c5024718d0c319c714091c63430d131c50647180fd0c309c714192061410f1c64502479011c00a29164013031c082861f1a8490c00a1b430f2034131f0074006d0c3c88d84c72034131f00285d0c8040dc7c01b430f203700706d0c3c80dc70f1b430c371f0010604c0c718831b021c5d402f01806c6c30bc01b13430c531c085ebc3ac2e9f3a16e70397ae4f3906e34387ae0b37cede02e16dceb704db1b668d84b5dcd67b550d42b4c4d1fb438cfea8a6cef3376cd232f2ca9326ec8c31eac673156c3e30b2c1b3016bf42f72bc92ee6bac2e82b8f2e16b782d9ab552d0eb342c7ab0b2bf6ae82b52abb2ab6a9c2a32a7b29a6a54290aa3328a6a1c282a9fb27ae9de27229b5269e99425ea963255694624da92324468fa23aa8d9231e8b6228a8912146885a21687821aa85d214684620ea82d208681820328031fd67e21f3a7c11ec679e1e2a77b1db675e1d427411cce7201c326ff151e53a1bd65251b986d69b0c6b59aa869a9a2c67999a065e993c64598d8622984c60597c85e0973c5bf96b859c963457b95b8560955454794e8530949417b144e50410564f0938c4d593104b2928448f920046c916c449910817b10c242510564020fd23e90f563c40eca3a30e463820dc235f,0xa1c8075430343220f1c089200d03d044c7c01620807743220f031c088200d03d0c744c016203513402b1f01207484844d0c70ac0161c8d40100f1c0828723030d8450c0c70a211e3700286c523204804c088d083c702288c80130323420f1c0894d50c7c0230a193449431f006c2872320c0c8d083c70220813720100f431f008c92023c8d0c083c7022081432120100f03431c088cb4d04d00ac7c04823208d3613402b1f00388431783134490c0c7884d290e0c5c4d3702206c8834317134d440290c7c0882f1e0d0c5c4d3702206c94443c0c74d202b1d35131f0080ac64dc0201b2b16400d3513031c80ac81bc7020a1213031e3460ac6230443d00ac788022021121035431f00288500d880543c7020a2016346d43031c28718500d05439083c788022860150037430f1e200898d84c7c0182b1a11100f40342a231f0058a0d05905088c7430a022434108c163513402b1f010e20c4450c7c0050a19110c5e35431f002881805d0c388c7021c60374112231f0058818d005c3c0c788022063410f014034231c0858a0d44d00ac7c0430521110f431c2b0058750c7020a1237031c6210ac61d905043c70a880221422010071c08287010d8450c0c70a1d411e3700286c618500443019083c788022860050013430f1e200898d84c0c7182b1940100642210f1c28089041d9050014d840ac7c04388308c0635342b40131f010e20b4d50c7c00a0119345d431f006c2871801d0c388c7021c601341370e231f0004918d0c301c088c7022063430f014020110f1c0804b4dd00ac7c043011d361007402b1f0038818905044c7c04d8e20624141371f0112388901850024d44c7c08e2641402b1d13013638804c7c00d0a149b02431c0828610048dc7c00a181236431f0028690c0c70a021643031c082850dc7c0040a141040831c08606c74d0ac01b150f006c28407c0201825141f006c2840d5020c0c718184c221340350f1f00589138403d00d48c7c01624114300831c60613c0d0c3c8c7021c8c4e372340131f010c9138d01d0c304c7c0482636114300831c6078d1b20c0c718184f0343210f1c08700d0c3c8c702184c03430f1d20087045020c7c018184f2037410f1f001058913c30dd01604c7c048244137031e0c606c7c01218114010360f1f0060713d0c0c883c7021c34152343020f1c280891d12c002c70a183543031c285048d50c7c083181c4812360f1f006071308d0c083c702162010760f4123031c28810c01b0a10834303220f1c08783c0181b104f0343220f1c087010448d0c083c70a02248c480f000b1c287040350c0c70a18808f234134131f020c92004c8d0c0c783022034100f2303431c0880d8450c083c7181c494036120f031c6082313d0c8c0c78302204f4323020f1c0870d2383d048c7c00a204137031e20806104,0x2401300831c609871020c70218162123004f1f0c086c8260d88c783c0484313101b02309836220d210f031d4008a508848c7c0c3021b2143230f006f1c087d0c8c043c7021b430f01231c086481288134483c090c74d29231c4c4a21360f006c9884813124d449002c783c02e21231c4c4a0d37006c94403840d50c7c00a2075400f1c082861d8d1b50c0c70a1c80754035230242231e0c08b201d50489088c0c783022911431f007428644128d50c7c0]
def g223H9 : Nat → Nat := chunk #[0xb1f21d426c00008e400073a395b8000dab49e5fbfab76000307e0002642000000000038d5bd809260007fa44e79f2eab500000004b7c46fd8bd1c9d3000004d999f4af570f400000000000000593a0007ed9352cd6a0000c3c000374f7de3e0a00000000000000b3c7ed52c900019280000000658d986a9e769f0fb4c85a59c97aac65e1408191a60c020000000afc2aa626c40440006fcf299b6843598001535420a0004eb127c1fc43af31e372c8000cb2000000079131479eb2000097f296d7e55d649ac000337903180000006f680006cd800000000003c01462eb31dda80009e65e7e202c6ab8ad51ce933ffe098880008087736d27a23ec76800000000004ca7a1b79d7182f407ea4643add836acf85f897e9cbdf721000071c3de2800165db2bc00000004917f8d40a0ec0c9941a0eb5d8de83aebacd9be23396000006fcbe1cf44e3ee000000010000000180200a0000000200a00c0000100000000000000004050010080040e00400400c00801000024000010000000180000001c0080e00c00000000000014028000040000380000a00000001010014000070000000300000000c00000000004000020000080080600c01c0000000000402803000008000000000000180c012000018080080340000300600002000002000020000040000000100000801814002004000010000040100000a000000000000000080100a054000020020080000c006000010000000100000000200c020000060000000100000011001006010058020000100000000a00003804004014008000000080280000200000000004008008030000040000100000800000000008008040060040100000000000800000000000010060300000000201c0b8040000040280001600c0000000000000000014008000050020000000000200c00000008000000000000280080500000403801004018028030020080200000c0180000100000400001000000030000160040080000c0080280000200800001000000020020000080080a01400402801000000000000000040200100001801801000000028000000040100100000000003000000018140040080080100000c0080200201800800012004008020020000000100600c0100000000c0000a0000080000000200002801002004000010000080180200200c0000100c00402800004004008030020000000000000801800014004038010080240080300a0000000000a0140000100c010000110300000280000e0140900000600c080010080000180100e00000000000000098000000040000800000c0200100a000010010000000000100000000000000004010020040000180900a0080080102000c0380000201c0080000e0040000000401000000000000030000000000000100c034000000020000080001601400002,0xab28000000173400000000000000eb9000000000000007ce6000401efb8d9720004ef35720d4ca9724892d0b65e0005770b6100013c58001cf361bc00000000001f9eda580000000001bb3d4e8e8f0e2ce3e116580e668aaedcde50744c489347901e122ed1f589755628ad9b86892ad5768c09994fa8c8824998c4b8f0b73cb3534f93311407492aeace6c80007cfd642d8f3ec195100000000000000135d800000011544aa1c7200011039116af2d6c80014f13315f3b4f010a94989cd6b7740003707277bfc0255b5dfcd8d8ac63bb4dfe6e7fb9827df10833fd945f43346ff2663067fe4cc37cafd730bcc412e03b0fabb0001098800166d00004eeb36db569469a3c3426e3b4d04c56fb2277145889475119bb77c77173dac1420ff1ad9b2d53d6bcfa9ee0ccbdc93cd6d75c2cf72612dba30fce6ab8f2271780df091256e48bf36a43d4a13160006b9a0002826000259e000000000060d30886a478cb5992c9634da00000000005b96b0ddc9afe56db4ea75dfe313b8467e25a07f5e897c00049460007e8723e92be67aefbc0000001075800000056120005e7a67000007bb80007179b27bdb0dd7172c7300006b9cc7b7dd1c52940e7c300015badc28955894200051418f99bf6989afad7e3ded7dcc9fbb116800127a7bc246ce16ff92eea14d2bbab98acf8641e2f5c00041bb729e8076510001aa793ca00000014d4293eeabc2bb059b6c6000391c9b80001efae0cc24548f633a9bfb0e31e55f6f800190abf15746972822b8a2bb4c000077db4a5dede55e00000000003b020007f2be008000441e53e00028720002fae683ae46d49fd8b8efa2f58b0d76274d8000000361e2a1e6c591880000007eb7168b5b000000000000000a7edc78e54800000012d80006be2cd9bd740000ade0007fa200000008b400000005414000000128bc0b433e0000783d628c940000000000000000000001a4026b8d2a5ba6bbd1afdc7580cadf57554c5681900000007200000000000072a35128000000000125e45c3ab6a0d899800014d7f60d6bbd8a880f5e891e80000294dc220002970000000000000000001d2299c7162e530001f97000000000012f56e7d2e38001ad5a74d605ac9d3943805bb48000261d5d5effc034276000000042240000cbfb4b800000000000004ef00002afc0000af6921bd0c00000013a8e0e08d3282d58fcf12f844023a1980013d400000002cf4000179600000009648e9aa1c307b4bfdbfd37880016135a4910b1dfaa490001ed38001ad26336f3800000000000000000128a35a80001205b990f23e22a450bb7bbdc21f7e7264896200003b9887490a648e91351584d73d79f27e71c000055473356aa80008a471dd8c4800098e7bd2a9dbaa1efe0000421800072a00000000b380006ba40003607565b3a69a0000074ea,0x1fe0e0dc8300000b998cba6e8685e6b8be4e506d617a9ba9597ae54e49a30000ef5df19f8120b835fb693b43e03f89ee1c80006bf52b380000003d17e0b80000000eaff5700010bc0001e0975a400020129c96df9418346ccd60000000500c3d0dbe80004c120000000000000021a950a000000133b9ba8d2b80009ddf3b50719f0273880000005e4444f6676000000084445030888f520004add90280007b28001093000000000000000000a23e48e30c694883a12ebf53e212728ea38cb15a9bdc827ddd787fc762fc37276d893000037457078f6fa57ada629d00000000000000326a4ad8001c8300002de8000a7549c4be9ef3ee5acbb20006773f0ebb3f46358a0a690dc6750bf81047acb69680efb0899658acba10c37c6662000100942244fe00000000005ae980ef5bd6412a191bdc6320000001bae80000006ec2f5200000002214f4f0a5ef20000174c8f660000000cd5558628c5f909d250b320c0001c2a80000000d8363150628c754660006898c39e75b88d305800000009c3a318000677f46a00000000001d48000000000000001e40c542b3327800000006c980003fd5fa3972cdc758c200058400004f9b7eff800cee000044e40680003c5534b7c8245b00004e2d9b76a15c466b336084da1d09e7df2c7996f419b328000c06800184cb89126700014468000c6016360000000a57000000000000003dc0c5d673c7a57cab0a5fd650f24d59ce50000000399e00044c40000e6992d50840000001666b7385f7b0ff7097d8f09a00014df8000f01ba024957ef5c7f5994b5147ab07d1fb290d00000000001d1fcb440000000000185a000000102973b07e4fd7c57f7a8a0002136000209a000000198bd360000388ca051a800001b4093221ca0000001cc200000000000000277a00011a600000014cf15ac0002683a5399205f6502a0000000000000000043200000000dd0484f1177e4c3bb6c10bd7c4c6fbf3304cf1ad400000001d14d24b90e6fb10e12c919800b880006bdf05a0001d7b000194e24208dd17c2000000040d9e569a7db642154b5d9f280000000000000609693048b60006fe2a9e00000003bce730cb6a00008d0000000000029ee000463a000000000060bb4e180000006cd22158001585386f5d973ed2db90778ac73ae0004f460000000000574ac36b690845800037480000006237bc115dc00021976c35c320003edb295f928000000000079f8000000000000000007a72d1a800000000019b9800102c456800022e79b3000025ed6b400024dc0000001e8b3843f25933ad2b38934b4e0538ae5e79f1300000000000ccaa99064b686cca3aef886ada98f4d7a604a55b70da99cb8887647b13594428f6659074971cca35f05d92335cc9e77880cbe4c6f3249c593012f3a00042e00004b91705dc1c0000000,0x54fabb950fcc42000000043e167c8000000784a78d0000000000172c247da878001d7bcafa545439356e22880004a838256b1a000289c3c7e01078616a8541800171878f57519d78c03d5e800008e3ec2bbda0000000ff68001aa493c0000398f8581c847229d1823210cb103]
def g223D10 : Nat → Nat := chunk #[0x40406088408e28692202031a420471440d100c110811c50424d8d110c210811c51212843911e00d1c6d087223c00838d09421c8811c11040403a10e40d8f002143440424420038e609080a848071e00d2020da1201c7803901a0a848071e0042468491423c00638d080cb90811d00824202a10e3c01034808368438f0040e34150871e0080840d09421c7802071a105508f0070e1c5d0870040c00a50871c40d2f23f4397e8ef5c33485f8add3ca423fa718c09432183384b860060003fe65ff597fe64ff593ff54ff953fd54ff153fd63ffd4ffd53ffd0ffd43ff583ff50ff543ff40ff503fd30fb483f510]
def g223H10 : Nat → Nat := chunk #[0x8bc000003fc31880000007d1f4084115bf8f598001738d072ef0aada4d61e27d54000902234000002c94003e640000000035500000000000000000014a000000000317c000000000000000000000003c1ad20001d64001e74cc04f400131c0000000022f40008d38b90c4000000000003c32248000002c9f5f8a1f0aec48000003a51658001d5c002602e40000000000000000000b540000000000031b800000245800000303e40041f96ef08000000000000000000000d2c0000000000000000000000000000000000019f33bd8cc00000000133c000000001f180000000000024ee2a12e700c001646f2000197000222926fc71e98002e9c000000000003c100000008eb270000000000000a1685c9aab2bad16b0e840000000034b3c34fa8000000000000000003f8400000223ecb4c54001f8b6ae838002177910000000000003bec0038264c8000000000476396ec2f9c000000003c84001ebc87b06eacf2c55bc0000038f8bcc00125d288cfe86362f8d96b4000000001b816549ffe8000169479b3e80017ad9d3fa4d3d51800000000000000368c0014233729d8000002fa3d79dd4003776f7c6799e636f1279ce5ca352364000e1a5c5083c2a14bacbc06b0210e2da129326fe6908931fd8000001732a6b3e3a3118d9b000089b9a3b4e8f399648b4e660cce00017bb941fb69dfa3be60915d1ed34538000002211dc284c000000003f7ad854d76e988ec65aba0dfed69e00009ec710001c2c0036de4693c40014472ab0a7852f467ddb5cae2f05b36ea7a0700b1ea091991c7e81727e9461b4dac000000000003f90003760003d812fc00394c000000000000e4c002bb319fb2eaf2a9000000000235ba21ef8968bd69f5b68e097c800000000334b70cf1400000000000000c0200000000000000000000000000600008000201000000c030200002000000004010000c0200000000008070000202000000206010080c01020080e050000800000080004010000010020601002060000000010080400020080002000000c0000000040000000180402020080003008040205008080200010100000000000000000000000000040000000080000]
def g223D11 : Nat → Nat := chunk #[0x80640e00a07f]
def g223H11 : Nat → Nat := chunk #[0x2ad6513961880063004814fa6000000101f23d00091768bb92f0945a95e850004010000a00401]
def g223L : Nat → Packing
  | 5 => (7,6,6,3,g223D5)
  | 6 => (273,5,6,10,g223D6)
  | 7 => (1147,4,6,14,g223D7)
  | 8 => (1011,3,6,16,g223D8)
  | 9 => (252,2,6,14,g223D9)
  | 10 => (21,1,6,11,g223D10)
  | 11 => (1,0,6,6,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 4 11 4 7 3 0 g223H6 h
  | 7,h => lookupWord 137 345 9 13 9 0 g223H7 h
  | 8,h => lookupWord 574 1437 11 15 11 0 g223H8 h
  | 9,h => lookupWord 507 1419 11 14 10 0 g223H9 h
  | 10,h => lookupWord 130 431 9 12 8 0 g223H10 h
  | 11,h => lookupWord 11 29 5 9 5 0 g223H11 h
  | _,_ => none
def g223 : Forest := ⟨223,11,fun i => (g223Y[i]?).getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxHeartbeats 0 in
theorem g223P5_0 : block g223 5 0 7 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 7 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g223P6_7 : block g223 6 7 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P6_10 : block g223 6 10 256 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P6_266 : block g223 6 266 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 273 = true := (@block_merge g223 6 0 10 263 (@block_merge g223 6 0 7 3 g223P6_0 g223P6_7) (@block_merge g223 6 10 256 7 g223P6_10 g223P6_266))
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 27 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_27 : block g223 7 27 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_31 : block g223 7 31 124 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_155 : block g223 7 155 256 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_411 : block g223 7 411 256 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_667 : block g223 7 667 256 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P7_923 : block g223 7 923 224 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 1147 = true := (@block_merge g223 7 0 155 992 (@block_merge g223 7 0 27 128 g223P7_0 (@block_merge g223 7 27 4 124 g223P7_27 g223P7_31)) (@block_merge g223 7 155 512 480 (@block_merge g223 7 155 256 256 g223P7_155 g223P7_411) (@block_merge g223 7 667 256 224 g223P7_667 g223P7_923)))
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 20 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g223P8_20 : block g223 8 20 91 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P8_111 : block g223 8 111 256 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P8_367 : block g223 8 367 151 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P8_518 : block g223 8 518 256 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P8_774 : block g223 8 774 237 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 1011 = true := (@block_merge g223 8 0 367 644 (@block_merge g223 8 0 20 347 g223P8_0 (@block_merge g223 8 20 91 256 g223P8_20 g223P8_111)) (@block_merge g223 8 367 151 493 g223P8_367 (@block_merge g223 8 518 256 237 g223P8_518 g223P8_774)))
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 15 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P9_15 : block g223 9 15 144 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P9_159 : block g223 9 159 93 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 252 = true := (@block_merge g223 9 0 15 237 g223P9_0 (@block_merge g223 9 15 144 93 g223P9_15 g223P9_159))
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g223P10_2 : block g223 10 2 19 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 21 = true := (@block_merge g223 10 0 2 19 g223P10_0 g223P10_2)
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g223T : checkedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact g223P5_0
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
  · exact g223B10
  · exact g223P11_0
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low223 : Lower true (vars 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=1091) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxHeartbeats 0 in
theorem V223 : Known K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem low239 : Lower true (vars 239) (graphGoal 239) 10 := lower_self (m:=239) (cap:=9) (hints:=1875) (2,0,237,0,9) (before_sound K223 V223) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 10 [(239,[])]
set_option maxHeartbeats 0 in
theorem V239 : Known K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(B 0xfc003f03f000fc010064f0a27319ce93,B 0x4104104104104104000024a00252094a92),(B 0xfc0fc003f000611b8c1439c2e731c,B 0x24924924924924924041138c003180c6318),(B 0x3f000000000fc00218223f0993e0cf83e0,B 0x145145145145145161020360993e08f83c0),(0,0),(B 0x3f000000ffffc60c3c00e1c00f003ff,B 0x4924924924924924840c2c0040800700025),(B 0xffffffffffffffffffffffffffffffc0000000fff0000380fc000fe000fffc00,B 0x1861861861861861b00a8000fe000f29400),(B 0x3ffff00000003ff00000fffff000000,B 0xfffffffffffffffffffffffffffff92492492492492493bb00000bf4a5000000),(B 0xfffffffffffffffffffffffffffffffffc000000000003fffffff00000000000,B 0xfffffffffffffffffffffffffffffe38e38e38e38e38e0ef57c9500000000000)]
def g247C : List ColumnInfo := [(1,0,246,0,9),(2,0,245,0,9),(4,0,243,0,9),(32,0,215,0,9),(64,0,183,0,9),(0,128,82,37,7),(128,0,119,0,7),(16,0,231,0,7)]
def g247A : List (List Nat) := [[]]
def g247D8 : Nat → Nat := chunk #[0x62eb3bc0c72f359c0d65179bce079aa406df6398edea3cc77b89d63]
def g247D9 : Nat → Nat := chunk #[0x75cba981d726ae1c776c9ba8521b2ea61c76a482200ffd8ffe63ff58ffc63]
def g247H9 : Nat → Nat := chunk #[0x6168190000]
def g247D10 : Nat → Nat := chunk #[0x11a20507f]
def g247H10 : Nat → Nat := chunk #[0x254fc280100]
def g247L : Nat → Packing
  | 8 => (3,2,3,7,g247D8)
  | 9 => (4,1,3,8,g247D9)
  | 10 => (1,0,3,5,g247D10)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 7 3 6 2 0 g247H9 h
  | 10,h => lookupWord 3 9 4 6 2 0 g247H10 h
  | _,_ => none
def g247 : Forest := ⟨247,10,fun i => (g247Y[i]?).getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g247T : checkedTables g247 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact g247P8_0
  · exact g247P9_0
  · exact g247P10_0
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low247 : Lower true (vars 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=1092) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[])]
set_option maxHeartbeats 0 in
theorem V247 : Known K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(B 0x3fc000003fc0003fc03fffc04010f081311333f,B 0x404040404040404040404040400000a001201212a),(B 0x3fc0003fc03fc00001886cc109c29cdcc,B 0x8c8c8c8c8c8c8c8c8c8c8c8c8c1084cc009809898c),(0,0),(B 0x3fc0003fc0003fc00000003fc2018f024e0ce0e0f,B 0x181818181818181818181818180010a004c08c0e05),(B 0x3fc000000000003fffc00c31f00c700f00ff0,B 0x131313131313131313131313130831b008600f00650),(B 0xfffffffffffffffffffffffc000000000003fffffc00000303e000f800fff000,B 0x60606060606060606060606062024000f800725000),(B 0x3fffffffc000000000003fc0000ffff000000,B 0xfffffffffffffffffffffe424242424242424242424242436c00007925000000),(B 0xfffffffffffffffffffffffffffc00000000000000000003ffffff0000000000,B 0xffffffffffffffffffffff83838383838383838383838381fdaf550000000000)]
def g251C : List ColumnInfo := [(18,0,233,0,8),(1,0,250,0,9),(16,0,235,0,9),(66,0,185,0,8),(0,2,137,112,7),(0,128,82,41,7),(136,0,115,0,6),(32,0,219,0,10),(128,0,123,0,9),(80,0,171,0,8),(8,0,243,0,9),(1,16,168,66,6),(0,16,168,67,7),(3,0,248,0,7),(1,128,82,40,6),(16,2,137,96,6),(17,0,234,0,6),(9,128,82,32,5),(10,0,241,0,8),(65,0,186,0,7),(64,2,137,48,6),(2,0,249,0,10),(9,0,242,0,7),(8,128,82,33,6),(24,0,227,0,6),(72,0,179,0,6),(137,0,114,0,5),(19,0,232,0,5),(130,0,121,0,7),(129,0,122,0,6),(192,0,59,0,6),(144,0,107,0,6)]
def g251A : List (List Nat) := [[]]
def g251D6 : Nat → Nat := chunk #[0x2bd20a58a3855d10]
def g251D7 : Nat → Nat := chunk #[0x1a20184c104000bc7817f209589574437aac51c2ae885fc825624dd10]
def g251H7 : Nat → Nat := chunk #[0x34000]
def g251D8 : Nat → Nat := chunk #[0x262583a24104189895060010519a816e769171bd6a0605b9da45c7a916e7930e14991235aaa79e4c38844102c8d6ae7a90e20a0979c1306a4625e9f5e71a1607a3d79c44a464d0ee9e7261635a39ca444513148de81152e7292034b1a39ca44460e0f8d6ae7292c1fa3a8120f9c2c6d0b14b7aa09ca2c799b06094c478f02a8740d800ff56255d10ff5624dd10fe95258120fe93258120fe96254120ff16254110ff1624c110bf62855d10ee96258120f695254120bf20858910f716554110f715254110fd1634c110fd1324c110bd63855d10]
def g251H8 : Nat → Nat := chunk #[0x4da8002801]
def g251D9 : Nat → Nat := chunk #[0x3c19475cf2488e4f411eb2739632475cea4b9a14c0c91d73c1525c80dd5549cf4c70e40675559e48e1fae73c444eb9e49113ae73e444cfd648b3e2f5959d48e16567eaa458ba73f50c38510450c9cfd4c8e22567ea2458d2bae792385512b3f5922c61016567eb2458fd73c1525c502174f5ce686cfd549a134e7ea5ce8aa3a89ce44532ab411cfd449321475ce2488a5c72acfd44c118475cf06497160e7eb24b8aa8411eb9e4901c08ed3d739a1b41983d73915238eeb9cb291630a2fa7ae734311ea4f39652305d3d739a14c93d047ae72ca481016541199faa922a8d50133a9223d51b34769ce687aba2694839c8a922a8e51347aacea459270a671e4451c0f46a1b9c22923400d4133a93638e5048a671a3c7d1a8a0d279d48e407acd1a86e752447345443fc20c053e9bd8bc7bb6ba238daabb79364a82b1cb1cb4933131cb04ae92d4ad4abcaabaaba97282a63a0724f23021ba071eb9d39b81a018817015b93c91d9021020e68c78a509087185603a81f0007fd6754bfe83aa5ff54960ffa64b07fd62543feb12617f89d65bfc0eb2dfe2758eff03ac7bf59562bfcaeb15fe3758aff03ac5df59552bfccea95fd6754aff03aa5f758d32bfcce995fd674caff03a65bf59560dfac6b06fd62582ff2bac17f8dd60bfc4eb077d65543bea92a17f59d50fbac6987dd324c2ff33a617f59d30bfc4e987ed62483f6a9241fb4c920ff2c0907f950482feb3a417f55d20bfa6e907f565443fab1a21fd58910feaa4887f532443fab3a21fd55d10fea6e887f527443f8a8221fc4c110]
def g251H9 : Nat → Nat := chunk #[0xdd00000034000026004800b90031803a6ce2a5bf371e0000a300000000bb000060100000804]
def g251D10 : Nat → Nat := chunk #[0xa0489f54491c6048a7528e9c866884a9f5247601a0b2a7d4921d288a755c19c8a2a9f5253190328a819f5248468a759d6195368aa90671f198cab499e0ba481686000ff597fd63ff58bfd52ff4cbfd60ff543fd30ff483f510]
def g251H10 : Nat → Nat := chunk #[0x54dc4003b00026812de9525250039119e99c1fd69ccdcd3c00000de64aa0c55086bbf57bdccb2a3400054117f2e85d7daea436382c996aec5769b65a13603003c0104001400067786000000012248c5b000ec0011f0034e08048001c003000208200140c000040030006000020224000]
def g251D11 : Nat → Nat := chunk #[0x850527a8c07f]
def g251H11 : Nat → Nat := chunk #[0x200000002cc0804bf10062807239db64000018420]
def g251L : Nat → Packing
  | 6 => (1,5,5,3,g251D6)
  | 7 => (3,4,5,6,g251D7)
  | 8 => (16,3,5,10,g251D8)
  | 9 => (55,2,5,12,g251D9)
  | 10 => (10,1,5,9,g251D10)
  | 11 => (1,0,5,6,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 1 5 3 5 1 0 g251H7 h
  | 8,h => lookupWord 3 7 3 6 2 0 g251H8 h
  | 9,h => lookupWord 12 31 5 8 4 0 g251H9 h
  | 10,h => lookupWord 28 71 7 10 6 0 g251H10 h
  | 11,h => lookupWord 7 17 5 8 4 0 g251H11 h
  | _,_ => none
def g251 : Forest := ⟨251,11,fun i => (g251Y[i]?).getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P8_8 : block g251 8 8 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P8_14 : block g251 8 14 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 16 = true := (@block_merge g251 8 0 8 8 g251P8_0 (@block_merge g251 8 8 6 2 g251P8_8 g251P8_14))
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P9_2 : block g251 9 2 47 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P9_49 : block g251 9 49 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 55 = true := (@block_merge g251 9 0 2 53 g251P9_0 (@block_merge g251 9 2 47 6 g251P9_2 g251P9_49))
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g251P10_1 : block g251 10 1 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 10 = true := (@block_merge g251 10 0 1 9 g251P10_0 g251P10_1)
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251P6_0
  · exact g251P7_0
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251P11_0
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=67) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxHeartbeats 0 in
theorem V251 : Known K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[(B 0x1fc000fe03f80fffc0201130601e10f33f,B 0x810204081020408102040000120001400a12a),(0,0),(B 0xfe00000000007f00020c429c949986ccdcc,B 0x993264c993264c993264e084098949984cc98c),(B 0x7f000007f01fc00001fc100ce0191e18f0e0f,B 0x3060c183060c183060c180008c0011410a0e05),(B 0x3f80000007ffe00618f00e1e01f00ff0,B 0x162c58b162c58b162c58b0418f0041401b00650),(B 0xfffffffffffffffffffffffffff80000000001fff80000381f000fe001fff000,B 0xc183060c183060c183063016000fe000f55000),(B 0x3ffffe000000003fe0000ffffe000000,B 0xfffffffffffffffffffffffffe850a142850a142850a143be0000beaaa000000),(B 0xffffffffffffffffffffffffffffffffc00000000000003ffffff00000000000,B 0xffffffffffffffffffffffffff060c183060c183060c180f6972500000000000)]
def g253C : List ColumnInfo := [(4,0,249,0,10),(32,0,221,0,10),(80,0,173,0,8),(0,16,168,69,7),(5,0,248,0,7),(16,4,105,128,6),(8,0,245,0,9),(24,0,229,0,6),(144,4,105,0,5),(1,0,252,0,9),(128,0,125,0,9),(73,0,180,0,4),(64,0,189,0,9),(9,0,244,0,5),(129,0,124,0,5),(16,0,237,0,9),(65,0,188,0,7),(17,0,236,0,6),(128,4,105,16,6),(1,16,168,68,6),(192,0,61,0,7),(136,0,117,0,6),(0,4,105,144,7),(200,0,53,0,4),(72,0,181,0,6),(48,0,205,0,7),(96,0,157,0,6),(64,4,41,144,6),(12,0,241,0,8),(20,0,233,0,8),(64,16,168,5,6),(4,16,168,65,6),(21,0,232,0,5),(68,0,185,0,8),(132,0,121,0,7)]
def g253A : List (List Nat) := [[]]
def g253D6 : Nat → Nat := chunk #[0x1c0020000000000000000000000000000000000000000000003029b61a4de4841d62cab9a6299210758a33e4a5a65841d52a6d8693792127582ee21a4e56258120db858a194e160483a69629656854120e9a5962854167483b29525424859d20d2b9a6299216748293e5a4e64859d20a6d869399216748313e489653859d20c6d922194e1674838ae689222859d20ccb54a495a257483339509256895d20c5b966295a15748253e4a5a65855d20eb858960462374829b64a59d188dd20e9a589609613748293e4a59e584dd209bc5aa8954960443671654a65858110db858a29561604436e1628a53858110eb8589588a160443a71659612858110d9c596594a1604427b24a5652858110dac9a6494a1604436b1659252858110dac58e494a1604433b2389252858110cec4e2494a1604436b26a9252858110]
def g253D7 : Nat → Nat := chunk #[0x52859d50adf24a50b3aa14fd69de1624c2bda53bc2c49853f9a57858930abf2caf0b12615be495e1624c2bdc52bc2c4985f98653858920bf504a70b1241ee95958960483dd272b12c0907ba5a55258120f3cb2cb0b0241ee96296160483dd2c4ac2c0907da5495858120bf514ab0b0241ee9628e160483dd2c49c2c0905fa8a53858120bf90ca70b0241ee9658a160483dd2c7142c0906fa5622858120bf4acc50b0241f695958950483ed2d2a92a0906de9656854120df514ad0a8241ee93258267483dd452b04ce9055f9653899d20f36b2aa4b3a41e796554167483ed2a4a82ce906fa8a15059d20db6a94b0b3a41b79509616748375aa5242ce906eb4ca4859d20ddca8490b3a41bae299216748375c91142ce9071f5965859d20adf24ab0b3a415ee295616748397acb242ce9072f9a24859d20cdf2c490b3a419bd589216748397cd3242ce9076b8a64859d20cdf2cc90b3a419bd599216748337c73242ce9066f4e64859d20cdf24470b3a419be484e167482afcb29c2ce9056f9253859d20af714a70b3a415f6194e167482bf4129c2ce9073b5962859d20e7734450b3a41dae488a167483dd2c4b04ae907da5496095d20fb4b12a12ba415be4959e574836daa4b44ae906de5416895d209df24ad12ba415be495a25748337c92b44ae9079b5956255d20f3cb2ac0aba41ee962581574838facab3aae9056f9256755d209df24ad0aba4157e595a157482b7c92b42ae9057b8a56855d20cbf2cad0aba419be495a1574833dc52b42ae9055f5a65855d20f74b12c11ba415be4959e374837cac48c46e906fc581188dd20cfab3a311ba41ee96258137482b7c92b3a6e906bb58a684dd20d7cb04d09ba418fd679a1374836dac52c26e906de582584dd20cbf33cb09ba4197d6796137483de2b2b12c0887bc4e56258110f78b4aa4b02217f28954960442fe512992c0887bc58a5858110bf894cb0b0221ef16256160443ee2a4ac2c0885fc8a55858110f78b1470b02217f1298e160443de2c49c2c0885fc8a53858110f78b2c50b0221ef1638a1604437e2b1142c0886fc4e22858110bf8acc50b0221ef1654a160443de2c6942c0886fc9612858110df8ac250b0221bf2384a1604437e270942c0887bc9a52858110bf92ca50b02217f1594a160443f6492942c0887f44e5624c110b752cac4b0241e696554960482dd2d2a92c0906ba58a5858120f34b2ac4a824176a6954950482ed2d2a92a0906ba5896854120db4a92d0a82418ee688a16748237c92b44ae9046f9256855d20b792cac4b0221e716554960442de2d2a92c08879c5965858110f70b1450b02216f2694a160442f6492942c0885f49a5324c110de8994d0982218fd605a20754b3f2c0844cea947f6256741d52cfcb021133a659f9204222758f9da40b2c4eb067b4822859d50,0x20971210100824c485a082e0020a0200020a8280c06e781003986e0212302a0c056621215980a02018200d9ec32121d80088101f0c098608300aa20182a0a2120c080801c1286082a2a042a020a81da089825800a2a08340a2a6084e602e7b98e0060cd9960066083e0820af82142a0e984490c181a082a081c08302a04080a81030080941898250405820b8161002082e05f821e9e436804489a003a60220387a602038208820182c302e0828218604062a8a810260d98070567b8c84866781a09b8c202408d00e30808b8c158c070467d8c61a122086c0040818c101b609981d8d6099e6188018c0d82088760b0063080758de08606998101660856318210102385e0820e102a201a0c01c2a78228300a82961783848de0d840c060a81aa10a888782302006b95217820c0c0a8280c485e0e12302808685e0b0c282807020a1782c30de0f12179fc3781c489c48208009e0b842a8b4b01de08a8610a2a8a961009e08a257820718420946378207080700861f82058b84e09a507028092178221d8c3409e0a0a21a842a920a940a8c0b120aac61d2ac4f04d32ac6154a74a746848a4686472ac6472ac63a6326056056052ac60546060d6326252ac2ac2ac2ac61d2ac2ac6154d30002ac2ac2ac6154db2ac60560d2ac60d60d6052ac6056056052ac2ac60510d3b75f35d25c54605b85a653459e58c57a3af57246056a46053455854153453452c39f2ac51f51750046046846000000039f4db4f82ac4a749f4d34f02ac4e84db4db2ac4d32ac4c12ac4af49f4a73a749f3a746849248a4784704702ac4684603bf2ac40a4534464344272ac2ac41f2ac41f41240a3f82ac3e13d900039f3973c73bf3b73af3a700039f2ac3973783853782ac3703632662d82d82d835133a3233163092f22ac2e52d82c62af2ac2a429c28527326625924c23f22820c1eb1d91b819717615a13912c11510d0f10d50b90a208b06f05d03c0200180100180100080000004fd426184dd62afb0ca6e83ac5a7d659610758b57cd12420eb16af5964841d62cdeabc9083ac59bd379210758b57cd32420eb16eb8a64841d62d773445083ac5bae488a10758b5dacb1420eb155f9650859d52adf24a10b3aa55ee294216754a6fad32c20ea95bd8653858960b7d04a70b12c157d59de152582bda53bc2a4b055f9657854960adf24af0a92c15ee295e1525834faca944aeb06bb58a2855d60d76b14509bac1af562861375839dac4abc4eb057d8653789d60afb0ca7113ac1c7d6595d27582bec329ba4eb069f5965849d609df24ab093ac1abe689212758357acb2424eb06af58e4849d60cdf2bc9093ac19bd579212758337c6f2424eb066f4de4849d60d5f34c9093ac15be495e162542bdc52bc2c4a871f58a5859d50abe94cb0b3aa1ced628a167543adaa5142cea855f96,0xb8]
def g253H7 : Nat → Nat := chunk #[0x287840007624500000f3c00001d900222a540000113a44000039bd1b9a2909e72800e511d5210d0009c00289c8d20d08610000062ec0b5d8131000f4b96e3b0337f0c0810c1000000000040006083002000]
def g253D8 : Nat → Nat := chunk #[0xd0859d52f7d6541d52dfd6741d52efd5858960efd3858960efd6854960dff7854960bfe7854960dfd7854960bfe784c960efd6295d60bfd2895d60dfd2895d60efd6255d60f7d5255d60bfe2855d60efd628dd60bfd288dd60efd624dd60bfe284dd60efd6589d60efd6389d60dfd5789d60dfd3789d60bfd5889d60dfd5889d60dfd3889d60efd6549d60efd6349d60dfe5749d60dfd5749d60dfe3749d60dfd3749d60efe6849d60bfe5849d60bfd5849d60fbe4849d60f7d5858950dfd7858950f7d6854950dfe2859d50dfd2859d50fdd3858930dff7858930dfd7858930bfe7858d20fed5858920fed3858920fed6854920ffa5858120ff95858120ffa3858120ff93858120fed3299d20dfd3899d20efd6559d20fed5259d20fed3259d20ff95059d20bfe5859d20fbe4859d20fee2859d20dfe5859d20dfd5859d20dfe3859d20dfd3859d20fed6295d20ff96095d20dfd6795d20bfd6895d20dfd6895d20f7d6555d20fed6255d20ff96055d20dfd6755d20bfd6855d20dfd6855d20fed628dd20ff9608dd20dfd678dd20bfd688dd20fed624dd20ff9604dd20dfe674dd20dfd674dd20bfe684dd20ff55858910ff53858910ff568549109fd0889d639fd0895d62bf6184dd62cfd6581d629fd5881d62afe6841d62bbe4841d62bee2841d629fd0899d529fe0859d52d7d6581d529fd6881d52b7e5841d529fd0899d32afe2858d60afe5858960e7d6554960afd6854960e7d6595d60cfd6295d609fd2895d609fd288dd60bf6184dd60eed6289d60cfd6589d609fe5889d609fd5889d60afe6849d60bbe4849d60e7d6558950b7e6854950b7d6854950cfd6259d50d7d5259d50d7e5859d509fe2859d50bde2858d30bde684c930ddd3299d309fd2899d309fe2859d30ddd6389d309fd6889d30bf61858d20eed6558920bee5858920f6d6554920bee6854920bed6854920bee684c920ef96558120ef96358120fe95258120fe93258120bfa5858120fea2858120f796554120fe96254120bf96854120eed6299d20ef96099d209fd5899d20bbe4859d20cfd6559d20cfe6859d209fe5859d20dbe4859d20dee2859d20f6d5295d20f795095d209fe6895d209fd6895d20d7d6555d209fe6855d209fd6855d20d7e5855d20bf5188dd209fd688dd20b7e584dd209fe684dd20ef56558910bf65858910f756554910bf66854910bf56854910bf6684c910ff15258110ff13258110ff25858110ff15858110ff23858110ff13858110ff22858110ff12858110ff1624c110bf62859d10bf62855d109f50885d639f61859d329f61859d30ee96258120f6952541209be4859d209f5188dd2097e584dd209f67858d10ef16558110ef16358110ef16258110bf23858110fd1634c110fd1324c110bf2684c110bf1684c110bd63855d10ded2089d60,0x1e020b123703834ac1044501d2b13c1e06098c382b83c001e250437038346c104450b618bf4ae0e2684383585c00af0712541c21c1616242a28348418e0e24a8303684cae0e2430305594170c50b83891c1acaa17038389038e0d84b0b8186e095070682b8186e0b08263a181c0be0d298430380fc0a570584131c300ee0b0a9586190c13e0838406e1b82420815060a82d0d42657062038519410e0d0b0c37002bc105884ae004f820b141b86c4b0b81c1a50f1560f3f99c0c352b1240378015c362782c21c2a0be0874ac362783c0610d89c373f994a8af018240569589e08842e08601a204382420688cae0f02840d141b86c4f03834218318605f0382420832886550b81c1058a17c302f1342e070470686383c0210406e52138342068b86c480f81c1a10d116641f9586e053f83892407c0e0e1b134218ab80097058546c495080b01301c161624aa39630116a370485892a1016026019542e0e24b04160ab800b010a9c1a1624921e01940482d1b8389a112960731a09c1a53087073190b04e0d2984132294c6e0c11840e1a94960731821c182308882718269de0b081c38460812e360295c16104c909b3d9904e0a701c3a5826cf07332950463704908c1486c68270595422037c1a56240a2f07134209081f64e2b8382169586e0e0826285a95c1c4e08509a1a1215e170382382c31cae004382421e9586e170312285b0d89e0d085c362783c00f0a16a562783421425c682704a8c21b8c136170410295426128270b829c1d0b0421f0694c21b824221820402c118dc12110c682c1022cae0d0860041609c16510e843d33821209888906844a06a7f09f3e79c9d2e3169dee7639d2e7219c026df9afa1579a766979a5e67f86ae66798f66259812484978e5c2963e565951252393c24cf929648491b244b90863e58f123a38e2e3588cba3168bd62d48aaa29289c624788761fc87b61ba86ae18a855e13684560f4834e0a081b604c80adff87ef1f9b7de9f597cbdf0e7b91ec37a41e6f7939e2d77c5dd07699d8e75d9d4c74d1d0a7381cb67255c6270e1c056f6dba86e1db3c6d75b3c6c25ad66a8da6768d0d8368059d7666d96864b18f9631988a61398125f117765d0d6fe5b09686594d62957915b155b1530538949d518541c4f5d39b4da132c4be52bd4a0524e48251cd466915544410dd42850654080fdb3e58f513c54ed03a50e6a38b8de936b4d833540d0b32f4c78315cc1b2f34ba32de4b4f2c70ae02a48a5f28689de26ac96f24608dc22388491fec7ad1d586ff1ae866c18c05e2167454614044aa11704290ffc3cc0e643660c842dc0aa4276090c21007501a1057012003d80ba01f8039003c000ff6184dd62bfe084dd62efd6541d62dfd5741d62dfd3741d62efe6841d62bfe5841d62fbe4841d62bfe3841d62fee2841d62df,0x8380c8008100e4004324406d0498151283490b8603a0b009f49162a41a486036785c10a841705b05922060200b0e92170586150a05c30a850301800e40854c07040e06b1a9820398c111828100c281063074f6322430703426c6a78a11045018c202022c60c154607064f0510e8c8914300ec4864f0380d802050200e0c1ccc0806c067861506d059820551346a093c86306313410e824ca30607a08403a0b009f46142a0ea3704406b3020b904161c5483460c30150a24044082c20c0502e1850200e63081705b058c20200e150c060848228c40a0050982180a85c30401d80890a8a150c05c3664241c185021860d9f8609861308a198008149e0621d29122b3006cf0c2a0d2a061507226824c142b4aa093d12431899410a860e0ab3038a9069418541b4ae0880de0b3030b82d99c11007c16786cc01b019fc1140d4c06874c4483430a3041a18541c0d20b2a98303582ca0c30100695040c02c20802c2a6029820b108217082e0b60b284a7b2a8089129e86a004c4043068018381a136553c508d300eca102611a61280e293e980801894c01b04954f140e116506474210c102160aa540f8182e0d18102b278015e0d085e484b83428a8a10e052782c20a8c15e030b8349179fcce05262a2f0293c10a894ac170382c90c0cc9c17078017178014e0a0a92181831c0c1706922f0780820c0345a570305c16481c606b1a85c1c482060870185c1c485460c03a8dc0e090b1214202b46e005e8414e0e2480a7078042070a184570285c16362470762b13c0e0d086c562407c0e0d086e36278342090bc00af041c2053800ea370712c21e8dc1e03081c283b15896170383461c1c8a21f03820b1a2ac1e7f3315c0a362480ad1b8082e08512038419502e0e243030628c170a40b83891c21c00a60b13c1630e140720b8210630c0e417042810169589e060b82c6180702e0e24102f0205c101d1b12331807c]
def g253H8 : Nat → Nat := chunk #[0x11e3aaaab8c420e044858000359948725614c002dee4c1d700036b7300d9f63fc91b0b1d09d800280202c6ef5a069bb1d0955f08f0e8c000ccf8519b80005ebac80031bd0bc002238000b140012a373956800000067c504002ef0ae7e5c003aae6000005a40004ed285a0bd5dcb8eb3985ecf6bc00147ae80001d90000002c7c003d50001adc002db1121adb9440021280024fc0000000000000011cb862ac00000000000014c800116e6464f626800000000394332280d017e74000000d2e0e85540000000000016e80000016940000000019d4000000003045c18001811ed4000c3dcb2e2e66072c002e31c6faf4503a368b40035b400145a33d691c4f4754d0427910000536d0bd77cf8d1a6480000000008540000026d0f2bc888394d9868000000001564000000003dff127b27e1a0a7c22d3b223d7be162060d4000670f0c0035c0002e29afb4a12fdcafde6963dadd3f289c1faa74655faa117065485c6434ac5d97e7898f7107199174c60065aae9fb3589ca430815dc48ea1d50e6e264dcdc00055b988003c2bc99470000b31ce4002e5226e80ae58e640000030a88300000006255300000000035f4b4000397c00351cc5ca0c5cc00040000c000a00000000000004000000000000b010000200118000c00088000000030000200000280402028000202008040202010100e020080000000300002010100004050080000000100c0001000080000000180600000000a010300c0208000081201008000000000000001008100201000140000]
def g253D9 : Nat → Nat := chunk #[0x605453250b03045c80807c9c1c042151f3f312703045461815c91482c1c01720632843020b042c70e1846c08ac1894220381e291b0701084c889c6c0c1420e183b1853010b04407c613c0c1420e1844231a2b0305084c80a13cfccc0c1460e20544c3b3f32262b011b04a154ac082c146901c54440d2a2707011a0890d86c042c189541c3422192b0701084c80613cfc0c14a0b1c544c373f321b02252b04a0906cac0c1420d1c60432b010b042c7ca13c0c1420d18441f2a1b0305084c809c04682c108180306084c205c9158642c1c0141c2707010854586c1c04213140f09270304546c91886c1c002141c252a0b070060618171586c914c1c0822429260b07006060a86c1c0021318252a0b07001c64a86c1c082131b0702084c1c5c68942c1c014182b1b0701084c60a1315c2c046c189203a2b1a270701087068a0389c1c0421c380e291b0b0306248c0c10214101728611b03040840714c610c1c082192b07000a240c646c1c002890318192a0b0700446064a8903c1c0821c291b030608446061315c2c04ac189202c18632b0306250880906cac1c042131c270b012b061860bca10c086c1421e180e270b012b042c81503864a89c2c0c120361b2a270701087180b86ca10c1c042202a1a240f07010870a8689c1c003421d1a02104a27050950804c14213081601544d2a111b084a2704a58801b84ca46c18942252a0210151b05084c822464a1bc104051c85181305084861d42c11220146f0470481451f16c6c98ac1821c4b18130b05286110543cac604c1422230d148889433211d0488013f31f1cf587893b31cece386f536b1accd2866932518acc205ed2e916ecb7659c2c295b8aa653428c93c89ae4bc25092188de45421c90587ee3d81da8e786fe3641a48cb86262f416c8ad852627412c88e842e1f40ea86c83261740a884e821e0e8062829811607402e80f80460007fd5758bfe9bac5ff41d62ffacea97fd0754bfea92c1ff4c960ffcaeb07fd57583ff1bac1ff4dd60ffc4eb07fd27583feb12a1ff58930ffaca907fd63483ff33a41ff59d20ffcae907fd57483ff1ba41ff4dd20bfc4eb1ff61758eff03ac7bf59562bfcaeb15fe3758aff03ac5df59552bfccea95fd6754aff03aa5f758d32bfcce995fd674caff03a65bf59560dfac6b06fd62582ff2bac17f8dd60bfc4eb077d65543bea92a17f59d50fbac6987dd324c2ff33a617f59d30bfc4e987ed62483f6a9241fb4c920ff2c0907f950482ff33a417f59d20bfcae905fd57482ff1ba417f4dd20feaca887f563443fab1221fd54910fea64887f567443faaba21fd4dd10fea4e885f61758ff8b0221fc4c110]
def g253H9 : Nat → Nat := chunk #[0xd26d8e39ce2e88bc0e79a000e4e7a7a067b1647b1b3545a5000000a28856a73000161519b80000c45000944d853317cf8bab5fb555cd000b6b130aa2f920000000000000006c1da861aa68c8846a000000b82327a3ec1ea0f61368a12c000a7e179000ab69ca5840009d5b173c9c69f40e6273b4650004461c7a9f56f7985773b387598157a7c575e32b6b2a1451d0005cb000666a59d377af8c3a6392d3ce2bb2a334c0001ad80c5b4b02e2ae08e3a000000000000000000d4fba400061800000085c0000002aef933a600000034110444af67d49ab5a24e29db7000b514120001c43169910000000000002649a9000842805c6e000000000850e7245aa7661f000460000ad23bd8746c6f15e8c73c209358000b23e35000b0a389c0049dec257d00013f65b2838bce20c012211b8f86e483d0895125e8dda0e7f203f78e322ac97ce53c705b0d4d0009aa000ccc000000cd152f9bf97bf0783333df1c552e90b3666c5c029786d1a12383abd9bd4b40dfbeb10799000000cd3c8f9d6922d7150b911e5765d8b90002d4d342c8696694d3914369eb870080400000180004010080c1e060001c0003000040c0500008020000014000001004020100000080500004080e010080201020280c050000408000000402020081c0408000040001020040401000040c05000040202030100e00008080001000000400000080000000240000000000c01000000807008041c01]
def g253D10 : Nat → Nat := chunk #[0x46930414028308131898a830011056486842a0411cc4a921a0c00438713289868300111184c2150208d2a340820880c441ca8c260c00444a0d0a00982300092a342130477bdb15e943414d5294670dc00ff597fd63ff58bfd52ff4cbfd60ff543fd30ff483f510]
def g253H10 : Nat → Nat := chunk #[0x128ec69c60000000072d44ec119941cb3ac78600aaf4da211840ba700028b000e8f6a000000000c1c9880076e0019d8bc00060082800145b0800000266a9400415357d224f800000a5f902ae0000004a000234000da000000001d4ca426dc434148a9430d79c80000163d41f3f4820000048100000000000000ee8000000014640023e726cb000000e862f400086000b14006185366bdc6089000000888c961db10a5092000800206002010000000020800004000000400006000c080001c10800180020000002]
def g253D11 : Nat → Nat := chunk #[0x1431210200c07f]
def g253H11 : Nat → Nat := chunk #[0x8d813b9002a800079ba2c23000000006c804100001]
def g253L : Nat → Packing
  | 6 => (37,5,6,5,g253D6)
  | 7 => (209,4,6,12,g253D7)
  | 8 => (215,3,6,14,g253D8)
  | 9 => (75,2,6,13,g253D9)
  | 10 => (10,1,6,10,g253D10)
  | 11 => (1,0,6,6,g253D11)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 20 55 6 10 6 0 g253H7 h
  | 8,h => lookupWord 106 295 9 12 8 0 g253H8 h
  | 9,h => lookupWord 108 271 9 12 8 0 g253H9 h
  | 10,h => lookupWord 40 119 7 11 7 0 g253H10 h
  | 11,h => lookupWord 7 17 5 8 4 0 g253H11 h
  | _,_ => none
def g253 : Forest := ⟨253,11,fun i => (g253Y[i]?).getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxHeartbeats 0 in
theorem g253P6_0 : block g253 6 0 37 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 7 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g253P7_7 : block g253 7 7 21 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P7_28 : block g253 7 28 181 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 209 = true := (@block_merge g253 7 0 7 202 g253P7_0 (@block_merge g253 7 7 21 181 g253P7_7 g253P7_28))
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 1 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g253P8_1 : block g253 8 1 18 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P8_19 : block g253 8 19 97 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P8_116 : block g253 8 116 99 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 215 = true := (@block_merge g253 8 0 19 196 (@block_merge g253 8 0 1 18 g253P8_0 g253P8_1) (@block_merge g253 8 19 97 99 g253P8_19 g253P8_116))
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P9_3 : block g253 9 3 49 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P9_52 : block g253 9 52 23 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 75 = true := (@block_merge g253 9 0 3 72 g253P9_0 (@block_merge g253 9 3 49 23 g253P9_3 g253P9_52))
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g253P10_1 : block g253 10 1 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 10 = true := (@block_merge g253 10 0 1 9 g253P10_0 g253P10_1)
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g253T : checkedTables g253 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact g253P6_0
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253P11_0
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low253 : Lower true (vars 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=1027) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxHeartbeats 0 in
theorem V253 : Known K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0,0),(B 0xfe03f80fe01883b301849e193e73,B 0x11224489122448912201082b3000494092a52),(B 0x1fc000000007f0106104c3e527186e339c,B 0x9122448912244891304100c2a527184e3318),(B 0xfe0007f01fc0000008018fc0647e18fc3e0,B 0x3060c183060c1830600010e80046c10d83e0),(B 0x3f80000007ffe3061f00387801f003ff,B 0x264c993264c993264c2061d00105001b000a5),(B 0xfffffffffffffffffffffffffffff000000001fff8001c07e0003f8001fffc00,B 0xc183060c183060c1980540003f8000f25400),(B 0x3ffffe0000001ff800003ffffe000000,B 0xfffffffffffffffffffffffffffc89122448912244891de800002fa92a000000),(B 0xffffffffffffffffffffffffffffffffc000000000001fffffffc00000000000,B 0xffffffffffffffffffffffffffff0e1c3870e1c3870e07baaf15400000000000)]
def g254C : List ColumnInfo := [(2,0,252,0,9),(8,0,246,0,9),(32,0,222,0,9),(64,0,190,0,9),(0,128,82,44,7),(0,16,168,70,7),(4,0,250,0,9),(16,0,238,0,7)]
def g254A : List (List Nat) := [[],[101,116,49],[116,99,81],[83,97]]
def g254D8 : Nat → Nat := chunk #[0x29359f6062937ace0648036fb1cc77d85d63]
def g254D9 : Nat → Nat := chunk #[0x97153ce3adc54f20ea9753d03c44403fe63ff58ffc63]
def g254H9 : Nat → Nat := chunk #[0x180000f200]
def g254D10 : Nat → Nat := chunk #[0xd1c0507f]
def g254H10 : Nat → Nat := chunk #[0xb16620420000000000000]
def g254L : Nat → Packing
  | 8 => (2,2,3,7,g254D8)
  | 9 => (3,1,3,7,g254D9)
  | 10 => (1,0,3,5,g254D10)
  | _ => emptyPacking
def g254I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 5 3 7 1 2 g254H9 h
  | 10,h => lookupWord 3 9 4 8 2 2 g254H10 h
  | _,_ => none
def g254 : Forest := ⟨254,10,fun i => (g254Y[i]?).getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g254P9_0 : block g254 9 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g254P10_0 : block g254 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g254T : checkedTables g254 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact g254P8_0
  · exact g254P9_0
  · exact g254P10_0
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem low254 : Lower true (vars 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=554783808) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxHeartbeats 0 in
theorem V254 : Known K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(B 0x3fc000003fc0003fc0003fffc008008127814009cc102730693ff,B 0x4040404040404040404040404040400000012500000948002520292aa),(B 0x3fc0003fc0003fc00000308359c602824e702939c9b1ccc,B 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c0208259c600024c60093189318cc),(B 0x3fc0000000000000003fc0000020c10461f84b138f80ce3e0e3e0f0,B 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4e0810061b04b138f808e3e0c3c0f0),(B 0x3fc000003fc0003fc0000000003fc100187e000c23f0030fc00fc00ff,B 0x181818181818181818181818181818000107400002360020d800fc0055),(B 0x3fc000000000003fffffc006061f8000703c0003f0000ffff00,B 0x13131313131313131313131313131304061d800020280003700002c2500),(B 0xfffffffc00000000000003fffffc00000003807e000007fc00003fffff000000,B 0x6060606060606060606060606060630054000007fc00001f24a5000000),(B 0x3fffffffc00000000000003ff80000007ffffffc00000000000,B 0xfffffe424242424242424242424242424243bd80000005fd4929400000000000),(B 0xfffffffffffffc0000000000000000000003fffffffff8000000000000000000,B 0xffffff838383838383838383838383838380f7aaf8a4a8000000000000000000)]
def g255C : List ColumnInfo := [(64,0,191,0,11),(16,0,239,0,10),(0,16,168,71,8),(8,0,247,0,11),(32,0,223,0,12),(3,0,252,0,9),(17,0,238,0,7),(80,2,141,32,6),(4,0,251,0,12),(80,0,175,0,9),(0,2,141,112,8),(72,0,183,0,9),(0,128,82,45,8),(192,0,63,0,8),(82,0,173,0,8),(65,0,190,0,9),(8,128,82,37,7),(18,0,237,0,9),(128,0,127,0,10),(1,0,254,0,11),(19,0,236,0,6),(67,0,188,0,7),(66,0,189,0,9),(64,2,141,48,7),(1,128,82,44,7),(137,0,118,0,6),(193,0,62,0,5),(1,16,168,70,7),(130,0,125,0,9),(64,16,168,7,7),(3,16,168,68,6),(9,0,246,0,9),(24,0,231,0,7),(9,128,82,36,6),(4,128,82,41,7),(136,0,119,0,7),(2,0,253,0,12),(5,0,250,0,9),(128,4,107,16,7),(132,0,123,0,9),(16,4,107,128,7),(20,0,235,0,9),(129,0,126,0,7),(16,2,141,96,7),(74,0,181,0,6),(32,2,141,80,7),(10,0,245,0,9),(0,4,107,144,8),(4,2,137,112,7),(2,16,168,69,7),(65,16,168,6,6),(81,0,174,0,6),(4,16,168,67,7),(64,4,43,144,7),(5,16,168,66,6),(200,0,55,0,5),(6,16,168,65,6),(68,16,168,3,6),(13,0,242,0,7),(144,4,107,0,6),(5,128,82,40,6),(80,4,43,128,6),(21,0,234,0,6),(192,4,43,16,6),(68,0,187,0,9),(69,0,186,0,7),(133,0,122,0,6),(12,128,82,33,6),(73,0,182,0,7),(88,0,167,0,6),(12,0,243,0,9),(194,0,61,0,7),(84,0,171,0,8),(144,0,107,0,6),(32,128,82,13,7)]
def g255A : List (List Nat) := [[]]
def g255D7 : Nat → Nat := chunk #[0x3e0c10413a0426400203932e4c86000317a8f2ab5e47950120c5e93caad791e54048317c8f2ab5e47950110c5f13caad791e5404436ac5920b5cd6852110d4f17682d739a5484425bcaf1735826952110]
def g255D8 : Nat → Nat := chunk #[0x7f83f84fa409d1c473e0c07be13e20274689d457a298e888a63a22250e8889d3a22089128744442a1f10e686442da0d109884341a2088e8882b3a220ace8e8224099fbcf7e7fe3f79f98fae7ce3df9ec0f4e79e3c79e00eee76e3af9d40e8e74439a9c68df26de35e9a88d0e66c3229878be25d02dd9698b0a56429b94289c64bc24a91a087641a1f98f6077a39c1c08db069631e17e8b5856a29413c89784622040f1872034e17a0af851025e11407c834816209602a01bc0a802700030ff1dd34bc0f0a061fd3ba69781e140e7b4c91cc12bc261cf659239825784c3ee5322e71cae0907dc9645ce395c120fd52c9b9cd2a0241faa591739a5404833f89da1544aec8857e53ba2a295d110afe31732412b9a21fac593739a540443f58b22e734a808876f3739a96950110ede2e7352d2a02219fc4ed6a427784427f905a75ba2d0886ef164829735a110bf6476ba280b4221fac5937350168443f58b22e6a02d0885fb27b50d405a1109fe4169d6eca4221b7cdda0a5cd484436f8bb414b9a90886fb2648297352110df62c9052e6a42213fc5ae0a5cd484427f905af4b1a90885ef23b5d96052110f9e2edb9ac0a4221fac5937358148442f78b5ee6b0290887cf1765cd6052110fd62c8b9ac0a42213fcaad7358148442f78bdac6b0290887ab564dcd6852110f56ac8b9ad0a42216fc82d735a148443a7abb6e734a908856f56bdce6952110e9eaecb9cd2a42215bd9ad739a548442bf905ae734a908876f3735826952110ede2e6b04d2a42215fc82d735a5484423fad5eed1ca908876f17658239521109d72d73d286b0281b365d90add1634c26ec9dc94bb2e0985cd96bdd1635c1309bb357ba2c6b82613b64ee4a5d9604c366cbb275ba2c09856d99bdd163581309db357ba2c6b02617b28ad7458d604c276cb5cf4a1ac09855d93bdd17958130e9b6e8b1af2b0261b3a5d90add1634826f49dc94bb2e0905ce96bdd1635c1209bd357ba2c6b8241f325d96350d70483a74bb2c724ae09057ab9bdd943501209f5757bb286a0241fa25d96350d404827d4b5cf4a1a809077896350e7950120eb52e8b8472a42411fc82d3a925764432f8bb4149cee88847f16b82939dd1108fe416cd6e8b1a213bc4ee4a5d960443678bb275ba2c0884ef1abdd16358110bdc456ba2c6b02213bc5ae7a50d604427d91da95bb280886db3768e974501109f6556ba2c6a02213eceaf7650d40443f48bb2c6a1a80884fb16b9e94350110df4687152f2a02215eca6d4350378443a78bb2c09cef08866f1605a939de110e9e2ecb1a13bc2219bc58d6a42778442bd84da86a02f08866f1609aa395e110ed62c8b0472a4221cad591688e548442bd84dae8a02708843eaab424895d1208f5556a4892b824196a9ea4a5e5404822f555af23ca809045f2ab5e47950110,0x270109e00178306e0c180f7830a03c101907a00058220506e0d014240507a00054268004044129008d08a402370443c11a0a092001c80011080501b834800ac4d2002c80070441092c110b044e0c200a0484417834900843d230200e04008d48c0840be1001922c400d489a1f00bf841404c043e1142c402a18901f50bf841408e62401be104f8400f88908d1003c037e11224401b39200df84889d031808ce48037e1222784c6fa428cc031a2e13f848891c60be1007c2312245e80f840100d64be100403c28fa4f8408d48914240097e1060962c502a928fa408d189f8458b1c28c234018096627e1162c7928189fa4f8418b090192324a3e93e10624a346326fa4f84482c81b8018c98018097e1120ae0360c7828fa40a0f84090c8218b1c018097e1063162c5c8cf84383228fa409d1a897e10098640488d024f84c891124be2360fe11a2450a3005f8468910093e13224300f005f8408d18217e2003c236429227e12e0c70a308df848890051601f017e1068a22703c6182f84d8300548916648017e136002085780f8488259210017e106402744f88006005482f84d83b801c283e2001f20862fe100847006005f8418c58b1581587fe11a244692f88006f8400717e2206c03e814237e1360c788208df8460513e23e1023401c401af840070ee0fe1006001c4f8488201700513e23e1022f028a268146f88289f8480aa051401be1301401c4128129f84fa41890901be13e902742404e2512612]
def g255H8 : Nat → Nat := chunk #[0x6a016005101191e4fa0000000021]
def g255D9 : Nat → Nat := chunk #[0x73501209fa66b7350120bea5eb4350120fe258d4350120bea9e94350120bea5e94350120bea9a94350120bea5a94350120bea52b7950120f6a5d27950120d7ade67950120d7add27950120d7a5d27950120dead0e7950120dea50e7950120bea9297950120afaa297950120d7add97950120d7a5d97950120dead0d7950120dea50d7950120d7a9e97950120dea9297950120cfaa297950120f6a5d07950120d7a5e47950120faa5926950120fe250e3950120f6a5d140de120dea50149de120d7a5d109de1209fa92909de1209fa52909de120f6a5d1405e120dea502495e120f3a5d9705a120faa591405a1209fa829795a120f6a5d170d2120e6b5d378d2120aeb52b78d2120d7a5c179d2120c7bde179d2120dea5d109d21209fa9e909d21209fa5e909d2120f6a5d17052120d7a5c279521209fa8297952120f725cd704e120fe250d404e1209fa829794e1209fa829694e1209fa829494e1209fc82939dd9109fc42a895d9109fc82939dd1109f98a9799d1109fc42a895d1109f98a979991109f98a979591109f98a949dcd10d7cdda095cd10d7c5da095cd109fc5aa095cd109fc52a095cd109fc42a895cd109fc8297958d10dec5d109d0d10bec42a7450d10bec42a6450d109f98a97950d109fc8297950d109fc42a8950d10bbc9297658110bbc8e97658110f3c5db7458110bbc5ab7458110f3c5d97458110bf88a97458110bbc5e96458110f3c5db7358110bbc5ab7358110f3c5d973581109fca697358110bbc5e96358110fac5914358110fb458d4358110bbc5a94358110bec52b7650110bec5ea7450110bec4ea7450110bece6a7450110bf88a97450110f6cdd97450110f6c5d97450110bec9a97450110bec8e97450110fe88a97450110bec5ea6450110bec4ea6450110bec5e96450110bec52b73501109fca6973501109fc2697350110bec5eb4350110fe458d4350110bec9e94350110bec5e94350110bec9a94350110bec5a94350110bec52b7950110f6c5d27950110d7cde67950110bec9297950110bf88a97950110f6c5d07950110d7c5e47950110fac5926950110dec50e6950110dec50d6950110dbc9a96950110fe450e3950110f3c5d960de110f6c5d140de110dbc58169de110dec50149de110d7c5d909de110d7c5d109de1109fc9a909de1109fc5a909de1109fc92909de1109fc52909de110f3c5d9605e110f6c5d1405e110dbc582695e110dec502495e110fac591405a1109f98a979d2110fac5916052110ead59168521109f98a979521109fc8297952110dbc5826952110fb458d604e110fe450d404e1109dd969794e1109fc829794e110dbc582694e1109fc829694e110dec502494e110cedd22494e1109bd9a9494e1109fc829494e1109fa66974501209fa92909dd1209fa9e9099d1208fb82a295e140,0x9fd269744e110fb55d9634e110fbc5d9604e110fec5d1404e110dfc582794e110dfc502794e1109fd5aa794e1108fd46a494e3768fd46a49423768fb8a9498e1768fb8a949821768fd46a69423748fb42a295e2748fb8a969821748fb8a93982174afa42a29821748fb42a295e2648fb42a295e1648fb8a989993738fb8a969523738fb42a29523738fb8a989991738fd46a69921738efa6948121738fb8a94982173f275d97458d43c6f9e6495e143c779e6395e143ce7926395e1438fb42a295e14387fa69781e1438fb8a9799a1438fb8a9795a1438fb8a979821438fb8a989993708fb8a969523708fb8a9494e3708fb8a989991708fd46a69921708efa6948121708fb8a9498e1708fb8a989dcf408fb8a9794e3408fb8a989dcd40f2e5d97458140bae5e96458140fa658d4358140bae5a94358140c6f9e6495e140c7e9e6095e140cee926095e14087fa69781e1408fb8a9799a1408fb8a9795a140eae591608e140b7642b765cd30b764eb765c130b764eb745c130b769a9735c130b76929735c130f365d9635c130b765e9635c130f665d1435c130b765e9435c1309f6269435c130d765ce695c130f365d97358130bb65e96358130fa65914358130bb65a94358130d765cd7958130db658d7958130cf68e6095e130eae5916052130eb658d60521308fb8a97952130cf68e609521309fa92909dd9209fa42a895d920d7a5d909dd120b7a42b765d1209fa42a695d1209fa42a395d1209fa42a895d120cfa42a895d120cfa424895d1208fba2979991209fa9e909991208fba2979591208fba2949dcd20d7a5d909dcd209fa92909dcd20b7a42b765cd209fa42a895cd20dea5d109d0d209fa9e909d0d20bea42a7450d20bea42a6450d208fba297950d209fa42a8950d20b7a52b765c120b7a4eb765c120b7a929765c120b7a8e9765c120b7a5ab745c120b7a4eb745c120b7ae6b745c120b7a5ea745c120b7a9a9745c120b7a8e9745c120e7aa29745c120e7a229745c120b7a5ea645c1209fae6a645c1209fa66a645c120b7a5e9645c120b7a5ab735c120b7a52b735c120b7a9a9735c120b7a929735c120f3a5d9635c120b7a5e9635c120f6a5d3435c120b7a5eb435c1209fae6b435c1209fa66b435c120f6a5d1435c120b7a5e9435c120f3a5da695c120b7a5eb495c120f6a5d2495c120dead26495c120d7adda495c120d7a5da495c120dea9d2495c120dea5d2495c120b7a9e9495c120afaa29495c120f6a5d0495c120dea524495c120f725ce395c120bea52b76501209fae6b76501209fa66b7650120bea5ea7450120bea4ea7450120beae6a7450120f6add97450120f6a5d97450120bea9a97450120bea8e97450120eeaa297450120eea2297450120bea5ea6450120bea4ea6450120bea5e96450120bea52b73501209fae6b,0x17350120bfa9a97350120fba5d96350120fea5d16350120bfa5e96350120bfa9e94350120feadd94350120fea5d94350120fea9e94350120fea1e94350120bfa4eb7950120fea50e7950120bfa4ea7950120dfa58e7950120dfa50e7950120fead0d7950120bfa8e97950120dfa58d7950120fea50c7950120bfa4e87950120fea5d23950120dfa5e63950120bfa5ea3950120fea9d13950120dfa9e53950120bfa9e93950120fea50d40de120dbb58d69de120dfa50139de120dfa58d09de120dfa50d09de120fea50d405e120dfa502395e120f7a5cd705a120fea50d405a120afb4eb785a120f7a5cd70d2120afb4eb78d2120dfa5c139d2120dfa5cd09d2120f7a5cd70521209fb8e96952120deb5d23952120dfa5c23952120cfb5a239521209fb5aa39521209fd8e949dd9109fd8e989dd9109fd4ea495d9109fd4ea895d910d7d5d939dd110d7ddda395d110df99aa295d110df98ea295d110df9a2a295d110bfc42a64dcd10bfc42a645cd10dfc992095cd10dfc592095cd10f3d5db7458d10bbd5ab7458d109fd66b7458d10bf98a97458d109fda697458d10dfcde909d0d10dfc5e909d0d109fde6b7650d10fb55d96350d109fd5aa7950d10bfc4287950d10bfc4eb7458110bfc8e97458110fbc5937358110fbc5917358110fbcdd16358110fbc5d16358110fbc5d94358110bfc9e94358110bfc4eb7650110bfc8e97650110bfc4eb7450110bfc8e97450110f7c5db7350110fec9937350110fec5937350110bfc5ab7350110f7cdd97350110f7c5d97350110fec9917350110fec5917350110bfc9a97350110fbc5d96350110fec5d16350110bfc5e96350110bfc9e94350110fecdd94350110fec5d94350110fec9e94350110fec1e94350110fecd0f7950110bfc4eb7950110fec50e7950110bfc4ea7950110fecd0d7950110bfc8e97950110fec50c7950110bfc4e87950110dfcdce6950110dfc5ce6950110dfcdcd6950110dfc5cd6950110fec5d23950110dfc5e63950110bfc5ea3950110fec9d13950110dfc9e53950110bfc9e93950110f3d5d963de1109fda6943de110fbc58d60de110fec50d40de110dbd58d69de110d7d5d939de110dfc58139de110dfc50139de1109fd5a939de110dfc58d09de110dfc50d09de110dfc5a909de110dfc52909de1109fd269435e110fbc58d605e110fec50d405e110d7ddda395e110dfc582395e110dfc502395e1109fd9aa395e110bf98a9745a110bfc829735a110fec5d1405a110fec50d405a110bfc82973d2110dfcdcd09d2110dfc5cd09d2110bfc8297352110fbc5d96052110fbc58d6052110dfc58279521109fd5aa7952110dbd5da69521109fd8e96952110ded5923952110dfc5823952110cfd5a239521109fd5aa39521109fde6b764e1109fde6b744e110bf98a9744e11,0x60d3f5d939dd160abf62b7458d609bf66b7458d60bbb8a97458d609bf5aa7950d609fe42a7950d608ff62a7950d60a7f4eb745e160e3fdd1635e160eb758d435e1608ff4ea495e1609ef8e949dd9408ff4eb89dd9408ff8e989dd940d6fdda395d1409efa697458d40aefe2b7650d409efe6b7650d40fa75d96350d409ef5aa7950d40bbe8e97658140bee8e97458140f3e5db7358140fae5937358140bbe5ab7358140f3e5d97358140fae5917358140fae5d16358140bbe5e96358140fae5d94358140bee9e94358140deed0d09de140ee758d439e140cef50d699e140cf758d399e1408ff5a9399e140debd0e295e140c7fdda395e1408ff9aa395e140cfb58e295e140afb8a9788e140aef52b768e1408ff66b768e140afe42b748e140afb8a9748e140e6fdd9748e140aef9a9748e140ebe5d9608e140eee5d1608e140afe42b798e140c7fdd9798e1408ff9a9798e1409f74ea495d9309fe42a495d9308ff62a495d930d775d939dd130d7e5d909dd130c7f5d989dd130b7e42b765d130f375db7458d30bb75ab7458d30bf642b7458d309f766b7458d30bf38a97458d30bf642b7650d309f7e6b7650d309f75aa7950d30bf64287950d30b7e52b765c130b7e929765c130b7e5ab745c130b7e9a9745c130bf64ea645c130f76991735c130f76591735c130f76dd1635c130f765d1635c130f76dd9435c130f765d9435c130fe6991435c130fe6591435c130bf69a9435c130bf65a9435c130d7e5d2695c130df650e695c130bbe9297658130f3e5db7458130bbe5ab7458130bf64eb74581309fe66b7458130bfa8a97458130fb65917358130fb6dd16358130fb65d16358130fb65d94358130bf69e94358130d7edd17958130df650d7958130e3f5db745a130abf5ab745a1308ff66b745a130afb8a9745a130eb75d9435a1308ffe6b7652130eb75d96352130ebe5d960521308ff5aa7952130dfa52909dd9209fb4ea495d920d7b5d939dd120dfa59109dcd20bfa42a645cd20f3b5db7458d20bbb5ab7458d20bfa42b7458d209fb66b7458d20afba297458d20dfa5e909d0d20bfa42b7650d209fbe6b7650d20fb35d96350d209fb5aa7950d20bfa4287950d20bfa4ea645c120f7a593735c120f7a991735c120f7a591735c120f7add1635c120f7a5d1635c120f7add9435c120f7a5d9435c120fea991435c120fea591435c120ff258d435c120bfa9a9435c120bfa5a9435c120f7a5d2695c120bfa52a695c120f7add1695c120bfa929695c120f7a5da495c120dfa5a6495c120bfa5aa495c120dfa5da495c120dfa58e495c120f7add9495c120dfa9a5495c120bfa9a9495c120bfa4eb7650120bfa8e97650120bfa4eb7450120f7a5db7350120fea5937350120bfa5ab7350120f7add97350120f7a5d97350120fea9917350120fea59,0x424c72469241623d9239c235f232222f022b32276223921f121b42177213a20f220b52078203b1ffe1fa01f631f631f261ede1e961e431e061dc91d811d2e1cdb1c931c401bcc1b791afa1aa71a5f1a0c19ae1950190818c01862181a17a6175e172116ce1691165415f615a315501508149f146d141a13bc1353130012a2125a120711bf1182113a10d1109410360fee0f900f3d0eea0ead0e4f0dfc0dbf0d770d240cc60c6809340c0a0bc20b6f0b320af508720ab80a7b0a3309f609b9097c093408f708af08720835080307c60789074c070f06dd068a064d061005bd0580052d04da04920460041803d00367031402cc0284024701ff01b7016f013d010000c3007000330022001100110000cff4293992176cff42989dd163f7e992095cd70f7e592095cd70f77991738e170f77591738e170ef7991738e170ef7591738e170dfe992094e170dfe592094e170faf593739a140faf591739a140fbedcd609a140fbe5cd609a140ebfdce695a140ebf5ce695a140dfb9aa295d130ff6992095cd30ff6592095cd30ff6991735c130ff6591735c130ff6992395c130ff6592395c130ef7992395e130ef7592395e130efe992095e130efe592095e130ffa591735c120ffa992395c120ffa592395c120ffa991395c120ffa591395c120ffadce6950120ffa5ce6950120ffadcd6950120ffa5cd6950120bfd62a64dcd10bfd62a645cd10ffc992095cd10ffc592095cd10ffcdce6950110ffc5ce6950110ffcdcd6950110ffc5cd6950110bfd4eb745a110bfd8e9745a110fbd593735a110fbd591735a110ffc829735a110bfd9e9435a110ffcdcd405a110ffc5cd405a110ffc82973d2110bfd4eb7652110bfd8e97652110f7d5db7352110fed9937352110fed5937352110bfd5ab7352110f7ddd97352110f7d5d97352110fed9917352110fed5917352110bfd9a97352110ffc8297352110fbd5d96352110bfd5e96352110ffcdcd6052110ffc5cd6052110efddcd6852110efd5cd6852110dfddce6952110dfd5ce6952110dfddcd6952110dfd5cd6952110dfddda3952110dfd5da39521108ff42a39523768ff8293992176afb8a9494e374c7f5da094e3748ff5aa094e3748ff8e9099a174a7f42b768e174c7fdd9098e1748ff9a9098e174afb8a9749a173d7bdda2952173cfb9a22952173d3f5d909dd1638ff82989dd1639fb42a295d1638ff42a895d163afe42b79423438ff42b89dd943bb78297658d43eb75d96382143f375d96350f70eb758d435a370cfb58e295237097f8e949dd97097f4ea495d970b3f5ab7458d7097f66b7458d7097fa697458d70f375d96350d70afb8a9749a170a7f8e9749a1708ff8e9499a170e3f5d96392170cbf58d6992170c7f5d939921708ff5a93992170d7bdda2952170cfb9a229521709bf4ea495d9,0x9ec540c4f8c4b0c452c3f4c3c2c36fc31cc2dfc28cc223c1dbc188c14bc103c0bbc05dbfffbfc2bf6fbf1cbed4be97be5abe12bdcabd77bd24bcdcbc94bc41bbf9bbbcbb5ebaf5baa2ba44b9f1b9a9b956b8e2b884b831b7b2b754b701b6aeb65bb608b5aab557b50fb4d2b48ab437b3efb386b328b2cab277b22fb1c6b17eb136b104b0b1b074b021afceaf91af5faf0caec4ae87ae34adf7adafad67ad2aace2ac8fac3cabe9abacab6fab1caac9aa76aa39a9dba95ca8e8a88aa842a7e4a79ca73ea6eba68da645a5fda5b5a56da525a4dda4aba479a431a3e9a38ba317a2daa29da260a218a1baa15ca114a0a0a0589ffa9fa79f549f019eb99e509df29d7e9cf49c8b9c2d9bcf9b669b089aaa9a5799e3996f990698c9985597d6973696b7963895cf953a94dc947e944193ee937a931c91db92be926b922391db9193914090f8908f901b8fc88f808f228ec48e718e1e8d898d2b8ccd8c858bfb8b7c8b1e8acb8a6289f989a6893d88d4888c882387d08788873586d78679860585b2855484e0848d843a83d18373830a82a1825981fb81b38160810d80c58067801f7fed7fa57f5d7f0a7ecd7e7a7e117dbe7d817d5a7d077cca7c8d7c197bd17b5d7b157aac7a597a1c79be795578d6784c77e37785771c76b3763f75c0754174d8747a7411739d733472f772a4724671d2715370ea708c70236fc56f676f096eab6e4d6dfa6d7b6cf16c936c2a6bcc6b426aad6a4f69fc699e693568e26884681b67de678b671766c4667c662965b5656d651a64d2645e63df636b62ec6299623061d26169610060b8606560285fd55f825f3a5ef25eb55e6d5e255df35db65d845d845d315cde5c965c595c1c5bd45b8c5b5a5af15ab45ab45a615a03599a592658bd5854580157c45787573456f7568e565155fe553155c1556e553154e9548b543853e55392534a5302522a52ba5272522a50ee51ed51a55173512b50ee50b1506950214fd94f914f494f014eb94e71485248154e134dc04d834d3b4cf34ca04c584c054bb24b754b2d4ae54a9d4a554a0249ba4972492a48d7488f4852481547c2477a473246ea46a2465a461245ca4577452f44dc449f4457440f43c74374432142ce427b422841e04198414540f240aa4062400f3fd23f8a3f4d3eef37263ea73ea73e6a3e0c3dc43d713d133cc03c783c253be83ba03b583aef3a9c3a2839d5398d393a38f238c0386d381a37dd37953758372636f436ac3664361c35d43597354f350734b4346c342433e733aa3362330432bc327f3242320531c8318b309d313830da309d306030232fdb2f9e2f6c2f242ee72e942e412dee2d852d482cce2d002cce2c912c542bf62b982b452b082ac02a6d2a2529c7297f293728fa28a7286a282d27f0279d273f2702257326ba267d263525d725a525732536250425,0x43fc201821c4882a0ba0fc4380f08060800a06341f88f082746e49e2015a1ff0805c6d1220982e83d01e23c20182015f24f11e1044821198982b60b6485001bd07e23c2089298282bf11e124589d1851683065e100f0a092c908cd07e23c20321f41f88f080c40b8be2046f8481e078503722702c0ff1087fc208d230280741fe2044f8411a380741f817c4089f08234702e83fc4784112084616a062c9783c0b01c1b784c1e4c0ff080840f08a24c9605f1083fc20211c0da89c0a83fc4583f08234806405d44e0541f60fc47840304e89105817c4680f0828c703722702f88b0703fc20182044f84f1083ec181e1844e0500fe2045f840643818f1083ec1f8403c3788325603c201e140291cf11e10448211ac902b00c06302f88f08225c193817c478411206458578140c592f07e12448b42302807f09e20c909d1815806903c91c0788f080848b2406302807f11e104e8e07e40e0513be23c20211c0f09df080845a0a0180282be49e23c240f0424018057817c47847062747b01e13c402103c280532560fc478413a3024b24062c1f88f082747b240140c605b07e23c20332015806c0be220ff84112060800d2070289df1160fc20182002818b07e13c409d180c007c0be23c258313a3818f11e10c581e1402f88f080844e8a07bc278800c274500be23c201913a2d920302d00f78413a378403de20c909d140f784f106484e8be0fc278800c0785c0a01fc47843162746f09e2207b8303c280ff07e200378403c378403de200309d17c408d21fe10038be23c200703c208df1043fc20071649788f080ac4e8a06446f88f0801c5033e23c200703c2f88f080a803880a80d783925e23c20071e49405f11e104e8b24bc402bf08274506407887f8880be10108e207c478400e078540ba480c78821fe10038e06349783f09e201589d1c02f83f09e201581e1b02f849120844f07e13c410f80a06c6f06227c478480b0286b2423041681f060c00bf84c0a4d92119e0fc478402e06c702fe0c87f88f08050680a22fc410ff0801c6103e23c201e00e2e83f1005c1682bc0a3082d07e23c20170303018f1043f41f8400e3788f080ac1609a0fc27880562745d07e23c201b3122d81105a0fc4017f098147d07e23c201b02e2a13048982c4c1d840d819d7e7d7c0d7a4d793d782d771d74ad723d707d6f6d6c4d69dd676d65ad63ed60cd5e5d5b3d581d54fd528d50cd4fbd50cd4fbd4c9d48cd444d3fcd3bfd272d240d377d1d1d345d308d2d6d2afd272d240d1f8d1d1d19fd0edd178d151d11fd0edd0a5d068d041ce3bd00fcfe8cfcccfa5cf7ecf62cf30cf14ceedcebbce94ce62ce3bcde8cda0cd84cd68cd20ccd8cca6cc69cc37cc10cbc8cb80cb2dcadaca92ca3fca0dc9c5c972c92ac8e2c89ac83cc7f4c7acc76fc71cc6c9c68cc639c5e6c5,0xe06c0cfa4f0903c1d8c06c13625f4903fc20191c03090f49e12c00361bd27841200fc404d8940cfa4313e10468e09b12d81037e93c20191c12fa4f08064198a0940dfa4f08624480c243d27840760c85f49e104803b10197841200d84925627d278444a240604a606c07a4f082406251897c27a40542746010606c07a4f08240604a627c209006c2e2504de93c208d120302604be93c2032120301b07f897d220ff08064700de9019784b060d86c4a0ffd218bf082406037e93c218b0782826f49e10c48901412fa4b07e10461891894e92121897c27a4b066248011e92c1f841186246f480cbc209006c283211960fc203617d203cf080a8480a89fd27843122405055e13d209006c2a26c4be0fc27a4524274751a233c1e25077e93c209d20c4f84f480a8480aa4bc27a413a240504be93c20331202d81037e13d20261203092f49e10c489017d27843122404055e03d203cf082406b01e13d20820762926c4a018c97a4f09224724d894c9082f49e12448e09441192f09e90448211ec902800c06312fa4f08225c193897d2784112064500de13d20217000f06f09e904e83b104ef84f480ec108be13d20360422745b2463240f83f09e911289d2012806051c23d278481e08480300a312fa4f08e0c4e8f603c27a40420d8504a64ac1fa4f08274624c49f12e89f49e10480e020c9583f49e104e8c0a003625f49e120f889030462507be13d218b13a300613be93c25830783018b07e101b09d140c03dc4be93c258313a3818f09e90c58361514fa4f080844e8be104efa400c0d8524d897c1f84f480184e8e8a312f8300de13d20825124082f49e1144890171283b13be93c20901812fa4f080644e8b6480c784f480a04e8c49b12a89f07e93c219213a403cf08a244809e93c22891202036f09e904e89017d27841202744e11e93c209013a2926c4a207c1f84f486484e9049b12f83f09e90c909d1fc1f84f480181b0be101b7a400c274506de13d203d0782c92f09e901409d17d27840860d84f09e9212c9213a2f84f492481409d1412f84f480d81e8ba480c784f480a04e8c107d27840780ec5103e13d20360762e80f49e100c0281413190f49e11448361944f84f486481b0be13d2192036a245325e93c24891202f84f486480c4891593918f07e13d208984a0d08f09e921288c9122825f09e901e0321441689f09e90130901ac908cf09e901a81b181b092c7be93c2026078383af09e901b03b1741f84f480a00c0b60341fa4f08098140c0a046683f09e901a81b1f4488260be2340784146381af07e23c202b11a378060ba040df88f0828c715fc905142be0be0e49713f09224a031a4bc1f88f0805c188f0af9270515f64bc18a2e27a0240f842c57d92f0628b4078403c38b415fa0c1978403c309d713417c4380f0828c713ae2682e83f1,0xf8880ae0fc24892408d83105a0308818f1028d02f842a08e83030237c4089f0843c0b920840a692f1043c44f8431605c982203fc4205f08a24108f817c47845120845822e0fc2017828289211802bc47849138147815e23c2289c0a281892504407d83f11e114481427c4784014815448aa244908cf11e12c18141f41f88f09c4c038a2bf17492145e1302c071f41f88f09814038b0b84688bf09814038de200c08d21fa0fc240500e4292519a0fc478403c01c785c03fc4683f08060038f0b803788d07e100c0071c46788f09a0f028071b4180af09e238001b1b89683f09e900dd091a0682fd27e13d25091805612d27e13c45091817f84f48062848a0bf84d83f09e900c0c087c20220642601e01e93c23930443784f48e4c116091640e80f49e10108b84b81d80f09e900d8d84b81f84f48e4c1a0d20740703f49e100c0dc0c05580f09e200d8dc0fc27a4f102240c0c06017d89f09e930f8c083c27a4417e20108c03381f84f49e200d8d00b80f80e07e13d2393044409203bc0fc2788f4806c7e07e93c2609030282fd01c0fc27a4036300c05fc27c27a4c3e302fa25c4f407a4f09204705f84b89f84f492246d060bec4e12f09e93898f2074000c05fe93c27131c05784f100aa448be13d2089f11c4c080c04017d89f09e930f8d24b41f84f49c4e848da0c17f84f49c4f048d24b4182fe13e13d27131c03784f4883fc40211b09902f09e93c40211bc2788f4822d0781d180c78841f60fc27a42043802f09e93c47130203788f49e100801b17c47a403a0400d8a24bc1f84f11e938981d1c0602ff49e1389e09180602ff09e9389e091810f88117e13d203318197a4817e23c2019180dfa481fe23c20191ac081bf49e23c2019180df88f4883fc20191a49006a07e93c27880643f88f4842e0ff84020301bf11e9085c1ff08230702107fc27880642813f48233c27880643010f11e93c241f08a3032f11e9085f840323032f11e9107c1ff08060703707fc47a4f0903c0c0e227c420f83fe13d201b1c0c20ff11e13d241f0363832f11e9207a1ff082307417e23d221ff080406f01e13c47a40540606113e220ff84f4843d010e22485f88f09e908781d1c0602fd13e13d261f180df84f11e900301d1a13525d0124bc27a41043e80f49e10110281692826f48237c2032180cf84f480c81d8b2261eb25d24063d278413a4681037e13d20350443784105e909289016c908c05fa0389fa4f09204804ba03d2481f082406b2423017f13f09e92448f6044102fd07c4fc27a4924409da4a09bd278411a240704ba0fc27a49242746064c941348bf49e100c8fa0fc27a40500885051c23c27a4112084604ba0fd27841192246050c95898a0037a0fc27a4112489064a0a3c27a49162747b2423041681f01a0fc27a405fc4ca05023341f84f480d41a0,0x1b0b5201c292706a0582f8416a0d915920ac9209d00c817c4683f08606c06922c9202b13ba4803205147e20c0e83b01e10c20b093c468303028dc07847024905849a0c0c788147e11c491c9045e83f1001fc2089e262349e49e2003e05d07e1044f1311a48b7e4828c0500511be23c2489e2650afe4828a4960523101e44f84e27a2cbe49a004900a00a207c409013be1389960ac10f24f1001bc2683912e489056e4b92788f0907e44806239221b01401741f88f09c4e4493c905061b11be2044807f0822c1095c9005005119a0fc4784e26a249f1007bc20a0064290ac1fe2302f84912064721460fc4605037e1307821209581b80a817c478441f60d44d92280da05257648c6405f1083fc25835125c0540be2003f8411303e45b922602a0591601fc47840420c8840a23602c1bf1001fc220f042490ac1f816c1f88f08062449042bc4006105817c2580032410af10019c1882c0be10c6906488500543fe23c24891044018214015c1f88f0820a44910afc409d317817c218d1c1580680a8144ef88b0683fc2281b24582b00d01540889f1081441784b06e02c91842bc400610560f02f8431a478885628c0c19213b817c218b2615f8813b815c0784b06060840a0aec900680a2080c78841f60d40f84314082bb2401a0288940a63041788b07e11c01a42bc4006105815c0784032478800e27702f84316084780a817c4007f08086c589d208578800d60c41605b01e100c1242802d83f09e20414891e02a05f1001fc2583724274880ae490281800fe23c258313a481ef11e105009d1410f8803de12c1b9213a382ba4808502f88f08e0d44806b24510a325817c47847062747f11e100f21f00c2746214063c4605f0887c198e0ae9201940a87fc478400ca244114063c478403ce0c4e8c087c401ef08e0ec909d1cc9788067e110f814191589d00d01502f88707e1244b922a02a2b13ae4803205147e21c1f84912583340a8ae12788105e11c1c0f724522b84828dc9205067e204140f707e10b32507fc278803c0184e8ec9051992f11014c1f8400c274921420bc4605f0960c0c0332015d2440a067c478483ea24411349051992f10814c1f8400c2749215e2302f8483e274611760fc478411bc4c038ea4bc4784c0a01c5d2443fc4405f0862c038fa4840b83f11e100f0071c49788107e13028071ac1f8811be13028071987f88f0801c0c8a01841788f0801c0c8c28c46f88f0801f028de23c201900e2788f080640381e17c478400e0644b062490c788f09c4c038ea3087f8880be10c58071d46383f11e100f0071bc4784525c4c038ac3fc478404201c500c20bc478404201c6124243c4784e2601c6c2de1215e151340e8014627446788b07e110a93e23c209d0570545f1160c0c0a340be13448e0c403788707017c2489724403172401851,0x14186c46f08113e93c208b042570805e09741fa4119e1389a8924937a4210280190a67494580055e9046181c4be11c1940aa12a2503623213784f4907e493892c1902a650099128a3925097d208c70160fc2381381522514606e1288c077e93c258371258330544a212a25121e90c4f8452562cb84a894c483bf48243c258b0644a25055096c0a2613a06c487a4f0883ec1a923512c250360efd2784312240825006fd2090f09894c098b23c2583f486241b0a4a3d2625121e10c58321c9799d7000abd208cc4be100dd83289782a119e93c262531606c825e23312fa4f096000d819211283381fe93c208d120392fc4be93c240f12037a43120f3c202a120328dc4be93c2189120312f41f897d2784312064744d0954978451a240625109512a92f49e104809d716483344a27413508f48a4bc21891205508525897d2784312240725f897d2784312240624de9003082c4be12c00192097fa400ce0c41784c4a634804b0a3d2192f09224410e49bd209df0862f1298d1c1452684a0194088944be9041784b06e02c91a49bd2006105e12c1e2531a4126f48063c209dc4a648c591e9241380f0960c1e0c89612d9200c20914018f4883ec1a81f08642500c8944498cf4820ac1b80f080ecb25fe9003082701e131281922147a4c4a277c218b042383b84a8941efa4f08276c58212497fa400c20ac1d80c4be100c12096147a4f0907e448821c1432684a897c27a4b06e484e93095462250300efc27a4b06274983fe101b7a413a2806050c9b12821f49e12c1b9213a4992c4be90937847062747f49e101b21f00c274625f897d2018f0887c198e8a212a25f49e1144890716442544a8a3c27a4120a2441108940c828f494210ff8451201841144bf12818f49e11c189d1d14225811e93c20907162748a4d09512881043e93c2383b24274a325894937a4f0887c198e64a0ff84f480d80309d1e12992903e9184784b060184e924bc417a4c4be12c1818066402844b423d2019f0907d448822614225325423d2583f080184e924bf12fa4f0907c4e8c0f040e92707e13d203607a47a411be11c1e2507a3006b0620bd278407a0f07055097d2784844e2c1e8e0a811784f480f41b0c10a4628c707e13d203607a4006105e93c203d042303cf080ee2088105c1fa4f082741d8d903d2192f09094140c0d8137a4707e134483c1fd2784e2664b448a0a846583f49e12448361c1a39200c463d238384be1244920f9417a4707e101e03f1fd278404d227128be101323c0c15429b07e93c203f07c3fa4f088941328916c1fa4f080fc1f0bc904900a00be2040f84105a03899424b40788f080ae828c2df9200a00a20fc4784104237899422f40788f080ae828dc9051c0af10237c2583e26a249e4906e05784525c4d448f0639278415e2e45457c9149305831e10,0x8403b83c108de23d201df0822d0788d1c03009403e20817a4f0960d07d922bc4006f4840bc258341e2348f1140bd278441f60c0c0f6480320101263081788f49e12c1a0f2cc6301f11e13d240f916074881fe93c2006b070240c0e633c47a4f0883ec181d1c07fa4f0960fc401803a3913925e93c4784004c247c1860fd200bf11e100ef1323d2788f08c041040ca1e3fa403e003c271302037a4f11e100803317d240cf080a184b1f1bc27a4525009c0583e263f88f49e100e810e26302f044a4a067a4613e1389b8b2417c92230e23d2784e26074820204bc4002f49e12c071320c97a4f11e1341f13a123a13025e23c2002a12300c05e89609002f49e130fd0927d2784325e200ef1319c07a4005e108c7131bd27840420cc4f48077c4006f0943c108e64bc4784d060cc5f4864bc2309d06033898ec24067a4f11e1389a8b1c1bf8411b227898a00fc208d0362037019e93c47840372247046a27c478411b47c6f1106fc208da3e2fa4f1008e0d809f0947c7055e23c20320422fa4416227c208dc3e320bf48227c208dc3e360b43fe10c9032141199206fe1244f131bd20a2912043c260bc3e382a041e20c97849120c8703e64bc4784b01c4c100e07fc208ce261145f49e23c20200642fa4f1160015784c3e06c703f84cc4f88f08040468fe93c402a313e130f88d1fc4010f0987c190be2015020118676c078443e403205408e097a4119e21c078483ee04b05408c0dc12119e93c478483ee24a0660a80818983fe114950b2285f8883fe10c48101bc402a02006fc220f83ea488f1060bc241f7000406f100800d81030307fc210b23d228cf11e120fb80036382a33a0804601b701e120f902301541ff08e000d8c0a808788f0987c190c0a80f810f08624190de9207f8411387c468de9107889f082370f8c83fd2089f082370f8d227c260f0322192f09c0c1909e900c78406d83f0f8de90c601bf0883e0f8d07fc4784f4822605c0f724401b724e040ec0bf4903fc478404257a483683fc20211407c1ff092240c0b84cc9784512040504086d0fe80f080406089e9105f88f08224c920f200fa0bf11e9044f8432483c806fe93c4019f080c86c3e4630582f825e901178491383caf49e228df840880846e0680bd2788e27e12c01922006889f49e1085f1303a380d113e93c210fe060747019e93c4784e07c4d448e8d7847a4f080c80c8dc2017825107e93c2082e26234911bc23d2583f0809b89a89201512512102213784d07e9249389288422513ba4846006251e92c0683f08604c117c2341c28f09e9044f1311a4f0885020fc27a4113c4c46910a112908f49e10c9032d1640a3e100bc12fa411be1244f132649035f48243c2489e27a2c8050e4b847a4f0907e44806211290824de93c20190643a1be11a0c12992f4849bc27139125428,0x6e06c206e064190608e0900c70020238240303824e0028240b80061202c48063800e123120181d8340212010609b8303a0184404c040c0703e04b830e04c0f08178b9081188c806e0040462320186e001188c824201b124232090904dc002a020229211806c383ee00283e081b313248460960dc06130542405036626c1e131180a86064605c002a83e23060366241541f118282132503dc18061043111d06248480828f099111180285826e005181812098a30301b83b0184c4e80616c061313a0184042649c1c0f00c208681e0cc410785b4000a02a2216b06814342d44d028628c4668042a2616d000540508275c1981d0082a0a8da004e814415054540a28c46078444808d0142611501028342360c242360d40078444808d0f08c0a0b08a8081460c4a268442a2684540078454000a02821131462303c2260e0a017130880a0281c1180ae0cc002152520078230140a10f415200670720026272002827045c19801242406826c4e08980146230681ce0c490901051b1381c230050a0600a38012424141182343b07e93c26097260ec6f11e13d26097260dc6c240d341fa4f094240d8e037c47a4f08c26c98231fc47a4613e1011d931a0c01db27e23c27a45163d80f080ec1089e93c2380b260401d8cc24087a4f11e12c9a8b1d23703f49e12448181bd2289045e11858181ac4703f49e11448181805fa4413e23c270301b64c8f11e9304f847260dc6f49827c2043727c2c6727e93c250b0762992f49e13c4006e078247727e93c4784925a00100fe9205f8411a0845c36083d201df0842c108fe23d201df0822c8790d1fc47a4f0822d06821181a02ff4984944f84e26e2c8089225c1f84e260ec6f10043c2082517c4c6054227c400df49e1389a8b2011f8800c03644f84517c4c8021e138983b13c4602f49e1045f130203a25711e93c248902183c7f08e0c06489e26280c005e23d2784e26a2c741843405f84f49e2044d83e264fa401fe11c1f1303a37a4625e2004f8480547c7f49e23c201d0322fa4513e101301061e3588f49e13898105123037f48e0c07f8401a20b899003fd2209f11e1006d83e2647a401be134183217d268306e037c2409e26390cf4828bc2409c1783c7f49e104100ce261146f49e1341818c122fa4f11e100c0451449788a13e13898101bd2292213e13898101bd2020a37e1085f13020380c005e93c4784e274247f4800bc2680e260ec6f49e23c2492d000186925e23c27a4d0000b898fe92c1f84701c4c1d8de93c201de260ec5f4880b00820f11e12c071323d2006c03e2101784d076038992c33c47a4f0822f8981d1fd278800d807c208c517c4c800de908178481ee0c468fe93c47]
def g255H9 : Nat → Nat := chunk #[0xae0005594f1ea415c6c2c7d5e38f7cf1948d85954899f0fcc134cd36b1e591d1427400035160ca88007970bed6bba98380000000001875718009bb77c9830f00063000000ab4b4bc2688e254826c40a40fee4003db48e311c819b716ccd0bac26ccb3460614f76003a480034e000000000017655979c86e000000003aa0034cb2200115c00000000e3400000001cfd49e4800078340cce5ce000001e90000014c416ac4001122c52046d652bd35bde8c003065c9ea40034385d53c0000093f22400000001f2800000842cf40071e00000000000900000901000300000000010700000702000d000800020b0000040403010202000100000108050010120000010000030102]
def g255D10 : Nat → Nat := chunk #[0x73ca90905fb5e548482fdcd2a42417ed6952120bf71ca90907f35cd38483f9a869c241fe9704e120ff4a0270906fb5e1384837dad09c241bef484e120bf6bca70905fb5a538482fda929c2417f549dd910bfa9ceec885fd62776442fec92bb2217f6395d910bfb44aec8877d5db74442fead3ba2217f539dd110bfac4ee8885fd5e674442fea733a2217f5899d110efbbb2e88877d5d974442fecd2ba2217f6395d110ff314ae8885fda2574442fea723a2217f5891d110bfabccc8885fd4e664442feb13322217f57959110efabb6e6885fd5a773442fea93b9a217f589dcd10efbbb2e68877d5d973442fecd2b9a217f6495cd10ff904ae6885fda2573443deaecb1a217f57958d10fdaba686885fd5e743442feb13a1a21fb67450d10fdaba286887ed99143443f6ac8a1a21fd56350d10bfb3ca86885fd5e543442fecd2a1a217f56950d10bfb44a86887fcdd160443fe2e8b0221ff37358110ff8b9ac0887fc50d60443fe6eca0221ff17650110ff9ba280887fc5d140443fe6e6a0221ff17350110ff8b1a80887fc50d40443fe6f2a0221ff27950110ff8bca80887fc1e540443fe4d2a0221ff16950110ff91ca80887fc4e540443beaedbc221df574de110ff8b06f0887fc50378442fead3bc2217f549de110bfa9cef08877ddd978443beaecbc221df7745e110efaba2f0887fc58178443fe280bc2217f6695e110bfb24af0885fd8e578443deac8b4221ff1405a110bfabcad0885fd5e748442fea73a4221fb66452110fdab2290887fc581484437ead0a42217f67952110bfabca90885fd9a548442fead2a42217f63952110feab1a70887f550d38443fe2c09c221ff1404e110dfabc270886fd5a1384437ee909c2217f6794e110bfabca70885fd9a538442fead29c2217f6494e110bfaa4a70884fb8a5789d27da13142e93ee295e2649f714af0b24fb8a548dce7dc52bc2873ee29523709f714af1a07ae591605027dc52bc281dd9735c130f6cb1ac0985fa42776482fd213ba241daf749d120bf484ce8904fba2574482fd2123a2417e90999120bf484ee6905fa42743483bd6ecb8241de9765c120ef5ba2e09077a5d170483bd6e6b8241de9735c120bf524ae0907ea9d140483f52e8a0241faa6450120fd4b2280907ead0d40483f5286a02417ea7950120bf4bca80905fa42778482fd213a4241db7749d110bf884ce8885f98a574442fe2123a2217f10999110bf904ae6885fc42743443de2ecb0221ef16458110f78b1ac0887ec9d140443f62e8a0221fb26450110fd8b2280887ecd0d40443f6286a02217f26950110bf8b4a80885fc42778442fe213a4221bbd385d343ddea1a91b9cff6257450f77a87242e73fe494e3749ff3ca713a67f42174dc377a10ba681bbd40523709fec4ae8a06ef502485c27fc92846e93fe7942274,0x24d0a07be5826850377a87342813fe799a1409febccd0a04ff4e66850377a86b42813fe795a1409febcad0a06bf9a5685027fc72b4281f9d438e140ddf3a470a06ef5d23850377cc91c281bbd648e140deea1c70a06fe582385027fcf31c2813fd798e1409ff34c70a04ff5a638502ff4129c2817dd39dd930bfc84eec984ff627764c2fba73ba2617f909dd1309fec4ee89876fdd2744c2fba733a2613fd899d130bf714ae8984ffa25744c2fba723a2617f9091d1309fec48e8985f74e6644c27fb1332261ddf765cd30eeebb2e6985f79a5734c2fbc92b9a61fda095cd30f6ebb2c6985f75e5634c3f3ce8a1a61f9d7450d30fcf32286987e7591434c2fbcf2a1a617dd7950d30bef34a86985f75a5434c3fb412a1a61dfb765c130efcbb2e09877edd1704c3bf2e8b8261fd9735c130fecb1ae0987f650d704c2ff4d2b8261fda395c130f7cbb2c0987be591604c3fb2e6b0261fd94358130bfcbcac09867fdd9784c33faecbc2613fe695e1309ff24af0986f78e5784c37f412bc261afd765a130deea1ad0984ff5e5684c377ce8a4261bbd7452130ddf32290986ef591484c37bac6a4261bf960521309ff3ca90984ff5e5484c27fcd2a42613fd6952130def1ca90986fe825484c2fda93bb2417ed39dd920bf6c4eec905fb92576482fdc72bb2417ee895d920ef6bb6e8905fb5a774482fda73ba2417ed89dd120bf6bcce8905fb4e674482fdb133a241def765d120ef6bb2e8905fb9a574482fdc72ba241fe9095d120bf744ae8906fba25744837d912ba2417ed391d120bf6c48e8905fb5e664482fda73322417ed8999120bf6bcac89077b5db73482fdad3b9a417ed49dcd20bf6c4ee69077bdd973483bdaecb9a417ee695cd20bf724ae6905fba2573483ddaecb1a417ed7958d20fd6ba686905fb5e743482fdb13a1a41fae7450d20fd6ba286907eb99143483f5ac8a1a41fcd6350d20bf73ca86905fb5e543482fdcd2a1a417ed6950d20bf744a86907fa5d970483fd4e8b8241fe9745c120ff5322e0907fa59170483fd2e6b8241fe9635c120ff5a1ae0907fa50d70483fd4d2b8241fe9695c120ff5a4ae0907fa92570483fd292b8241fe8495c120ff51cae0907fa4e570483fd6eca0241fe97650120ff5ba280907fa5d140483fd6e6a0241fe97350120ff4b1a80907fa50d40483fd6f2a0241fea7950120ff4bca80907fa1e540483fd4d2a0241fe96950120ff51ca80907fa4e540483bdae9bc241fe940de120bf6b4ef0905fb52778482fda73bc241def745e120ef6ba2f0907fa50178482fdcd2bc2417ee495e120bf71caf0907bb5d968483ddac8b4241fe9705a120ff4a02d0906fbde168482fdaf2b4241fad74d2120ff4b8690906fbde348482fdaf3a42417ed39d2120fd73a290907eb5d148483fd2e0a4241bed6852120bf,0xd0a1cff8256850f77ce904287bbd7482143ddf32410a1eef5920850f7bac7042873fd79821439feb4c10a1d7f9a574dc2bfc72ba6e1dee295d370cff44ae9b857f5e664dc27fb13326e15fd7959370aff34ae7b857f92573dc39faecb1ee15fd7958f70edeba687b857f5e743dc27fb13a1ee1dbd7450f70afebca87b84ffa2543dc33fae8b46e19fd735a370d7eb1ad1b867f5d948dc377e86a46e1bbd43523709ff34a91b84ff5a548dc27fc72a46e1bee2952370cfebb271b84ff9a538dc27fad29c6e13fe494e3709fea4a71b857f527765c2bfa73bb2e15fe495d970aff1caecb857f5a7745c2bfa73ba2e15ff89dd170bf714ae8b857f9a5745c2bfc72ba2e1dee295d170efd04ae8b857f5e6645c27ff13322e13fd8999170afebcac8b857f5a7735c2bfa93b9ae15fe695cd70aff24ae6b877e825735c39faecb1ae15fd7958d70edeba686b857f5e7435c27ff13a1ae13fd89d0d70edeba286b857f5e5435c27fd12a1ae13fc8950d70e7ebb4d0b86bf5da685c33fee9342e19fd749a170cffb9cd0b867f5ce685c27fa93342e13fd399a170afebce90b85fe427485c3b7ae9242e1bbf4892170cffbb490b867f5da485c377ce9242e1bbd74921709ff34c90b84ff5a6485c27fa73242e15fe7952170bf714a90b85fe825485c3b7ae8242e1bbd4812170eeeb9c70b867fdda385c33faed1c2e1bdd738e1709ff34c70b84ff5a6385c27fc931c2e13fd498e170bfd04a70b85bf92576582dfc72bb2c1cfd76dd160b7eb4ee8b04ff627745839faecba2c17ee295d1609ff44ae8b05bf5e5645839faedb9ac16fd69dcd609fec4ee6b073f5d9735827fd12b9ac16fd7958d60f5eb2286b07b758d43582dfad2a1ac13fe8950d60cffba2f0b067f5d1785833fee6bc2c19fd735e160d7eb1af0b06bf9a5785827fc92bc2c13fe395e160bdf1cae9a07eb8a574d0377d12ba6817bd49dcf409fec4ee7a04ffa2573d02f7cf2a1e817bd7950f40ddea1af1a04ff8e578d037dc52bc681bbd744e3409ff3ca71a04ff5e538d02f7a93bb2813ff89dd9409fec4eeca05ef4e674502f7f133a2817ee295d140edfbb2e8a076f5d974502f7cd2ba2817be395d140fd714ae8a07ee82574502f7af3322817bd3999140bdebcac8a05ef527735027ff13b9a813fd89dcd409ff44ae6a04ff22573502f7af3a1a81f9d6350d40bdf3ca86a05ef5e543502f7cd2a1a817bd6950d40fdd04a86a07be5d960503f72e8b0281ef96358140fdca1ac0a05fe42778503b7ae93c2819ff789e140cffba4f0a067f5d27850377e873c281bbd439e1409feb4cf0a04ff4e678502fdc52bc2817fa095e140cffbb2f0a067f5d97850377e86bc281bbd435e140cff3caf0a04ff9a57850377c92bc2813fe395e140df714af0a06fe82578503b7ae83c2819fd781e140f5eb,0x907fd99373443feac9b9a21ff6645cd10ffab22e6887fddd163443feae8b1a21ff77650d10ffabb286887fd9e543443fe8f2a1a21ff563de110ffaa1ef0887fd58d78443fea86bc221ff7745a110ffaba2d0887fddcd68443feae6b4221ff5435a110ffbb9e90887fd5cf48443feeeca4221ff57652110ffbb9a90887fd5cd48443feac6a4221ff7764e110ffabb270887fddd138443feae89c221ff6794e110ffa3ca70884ff8e548dda7fc12a46ed3fe494e3769ff04a71bb4ff92508dda7fc72846ed3fd39921769fe84c90bb5fb8a5485da7fa931c2ed3fd098e1769fea4c10bb4ff4e6085db3faec9c6e93fe694e3749ff04a71ba67f5d908dd27fcd2846e93fe39423749ff1caf13a6fb8a5789d27fc12bc4e93fe094e2749ff1ca113a57f427765d2bfc12bb2e9cfd769a174d7ebb4d0ba4ff4e6685d27fa13342e97ee295a174cffbb470ba67f5da385d27fad31c2e93fd098e174bf714a70ba77bdda285d3bdaed142e9bee688a174df6b4450ba6fb8e2285d37da71142e97ed098a174df6bb450ba6fb9a6285d37dad3142e9bee398a174df69cc50ba6fb826285d37da13142e9bee2882174cffbb410ba67f5da085d27fad3042e93fd3982174df714c10ba6fb8a1085d2fdc52842e93fe094e0749ff1ca103a4ff8e5789937dc52bc4c93fe095e2649ff3ca71324ff825389927fcf2844c93fe3942264d7f34af0b24ff8e5785937dc52bc2c93fe095e1649fec4cc9b9e7f5d948dce7fcd2a46e73fd6952373df714a91b9cff82548dcf3faec846e73fe69423739ff24a11b9d7f427765cebfc12bb2e77ee295d1739ffc4cc8b9cff626645cf9faed342e7afd769a1739fea4cd0b9cff426685cebfaf3a42e777d59d2173bee9ce90b9eefd22485cf3feed242e79fd7692173ddf3a490b9eef5d2485ce7fcd3242e73fd69921739fe84c90b9d7f9e5485cefbc72a42e77ee2952173ddea4090b9e7fdda085cf3faed042e73fd69821739fea4c10b9dbf8257658f9faedba2c76fd69dd1639fec4ee8b1f3f5d97458efdc52ba2c73fe895d163d7f34af0b1cff9257858e7fc12bc2c7fae295d343bdf04ae9a1eefa2574d0e7fc12bc687bbd74423439ff3ca11a1def5277650e7ff13bb2873fd89dd943bde84ce8a1defe267450efdc52ba287dbf765d143edebb2e8a1def9a57450ff3c72ba287fae295d143bdf04ae8a1def5e66450ef7a13322877bd7959143f6ebb2c6a1fe75d16350efba73bc287dbd749e143cffbc4f0a1e7fdd27850f3fae93c2873fd699e1439fe84cf0a1df78e57850efdc52bc2879ff765e143cfebb2f0a1e7f9e57850e7fcd2bc287bbe495e143def1caf0a1efb8a57850e7fc12bc287dbd741e143cfebc0f0a1faf5926850fdbac7342873fe799a1439febccd0a1cff4266850e7fcf2b42873fd795a143d7f34a,0x7ff992385c3ffac91c2e1ffe644e170ffeb2270b87ffdce68503ffae734281fff735a140ffeb9ad0a06ff52538ddb7fa92846ed7fe494e176bff24a10bb6ff5a538dd37fa929c6e97fd0999373dff32211b9eff59108dceffcd2ba2e77fd0999173bfea4cd0b9eff5d2685cf7fa93342e77fe495a173efebb490b9eff5a2485ceffad3242e7bfd7692173effbb290b9eff9a1485ceffcd2a42e7bfe6482173dfeb2410b9dff4277458ffdc52ba2c77fe095d163dff24af0b1effde508d0f7faf2846877fd09dd943bff04aeca1dff4267850effa123c287bff7682143dfebb410a1fef9d10850f7fcf084287bfc7842143bff3ca10a1dff4e664dc3bfcc8b9ee1dfd645cf70efeba2c7b877f5d943dc3f7cc8a1ee1fbd6450f70feeb1a87b85ff9a543dc2ffad2a1ee1bfd435a370dfeb1a91b86ff99138dc37fac89c6e17fe695d170bfe9ccc8b877f993735c3bfac9b9ae1dfe645cd70efeb22e6b877fdd1635c3bfae8b1ae1dff7650d70efebb286b87ef991435c3f7ac8a1ae1fdd6350d70bff34a86b85ff5a5435c3bfae9342e17fd499a170dfeba4d0b86ff50e685c37fa93342e1dff745a170bff24ad0b877f5da485c37fad1242e17fd6992170dfebb490b86ff58e485c3bfeeca42e1bfe6852170bff34a90b86ff992385c37fac91c2e17fd39dd160bff1cae8b07bf59373583dfac8b9ac1eff7458d60f7eba2c6b07bf5d943582ffcf2a1ac1bfd435e160dff24af0b05ff4e776502ffc72bb2817fd39dd140bff1cae8a077f5db73503f7cc9b9a81fbd64dcd40bfeb4ee6a077fdd973503bfaecb9a81fbe645cd40fdeb22e6a05ff9a573503dfaecb1a81fbd7458d40bfebcac6a05ff9e543503f7eeca1a81fbd7650d40fdf3ca86a07ef1e543503ff6e6b0281ff97358140fdfa1ef0a05ff4e778503f7a873c2817fd399e140dfeb1cf0a06ff50e78503f7e86bc2817fe395e140dfeb1af0a07ef50c78502ffa723c281bff739a140dfeb9cd0a06ffdcd685037fae6b4281fbd748e140dffbc470a06ff5e238502ffaf31c281bff768e140dfebb470a06ffdd2385037fae91c281bff798e140dfebcc70a07ef9d1385037fcf09c281bfc784e140bff3ca70a05ff527764c2ffc92bb261dfd76dd130bfeb4ee89877fdd9744c2ffcd2ba261fde645cd30feeb22e6987f7dd1634c3fbae8b1a61fdf7650d30feebb286987f79e5434c3fb8f2a1a61ffa645c130ffcb22e0987fedd1604c3ff2e8b0261bfe645e130dfeb22f0986ffdd1684c37fae8b4261bff7652130dfebb290986ff9e5484c37f8f2a4261fed64dcd20ff7322e6907fb59173483fdee8b1a41fed7458d20ff7bb286907fb5d943483fdcf2a1a41fec7950d20ff6b1ef0907fb50f78483fdac6bc241fed435e120ff6b9ad0907fb50d68483fdae7a4241fed7352120ff6b1a90,0xe044cf22599124888e24471222591094880843de21de90e5c86e2434b219290bfc85a842a4214410974785a42372108907ac839441ae20c41058882784116207a9033c814840792029900c8800e3fe11fdd8fe547ef23f441f8c8fbb87d9a3eac1f458e9607cd43e441e968f8647be63dd21ed38f6407ad43d491e968f41c79763cd71e5d8f24078d43c4e1e168f03077cc3bc01dcd0ede476b03b321d860ebac758a3a9a1d3a0e96074783a1b1cfa8e750736639971cbb0e52c724038fa1c6c8e2cc7124386c1c230e0946ffe37d91bd48ddf86e9237321b860db986d7636901b328d8d46c1e35ee1aeb8d6c46b2a356f1a9f8d46469d234c81a510d1f0689834261a028cf686772339319b40cd08663832f1196a8cabc651c3268191e8c85c63ec31d518d78c62462bc313818890c3d861aa30a5183a8c13c6052300817f10bef05f2c2f7017a50bc685df22ed8175b8ba1c5ccc2e4a17120b8205bba2dad16be8b5845a622cfc166d8b31059502c8c16380b128585c2c0815f38aef0572c2b6b15960ac2c55d42ac415478a990547c29ff14ef0a6b85324297114a58a49451fe28d414570a1e4509c281413fc09f344f58278613a109c704df626d5135789a244cb2262912ff097384b32255f129c8946049ee24c21249091b0488c242511f808eec47162365119a88bec459622a011420893c443e21ef10e4886a04304216110a28845441fc20dd1060882944108204f101c080343fe21fd00fd787e243ec61f470f9587c283db41ebe0f4e879dc3cac1e350f02877a43b7c1da20ec5875a83a921d280e83873ac399e1c9f0e418719c388c1c250e0206f8c375c1b880db606cdc362c1aeb0d5d86a1834d41a3f0d078677c3368198e0cac864a4321a18e70c5e0625830d6182c0c0305fa82f88178f0bb205cf82dfe16ca0b4a859942c8816230afe8570c2b4415770aa38544829d814b20a4b051ac286c140b09e384e8426ec134b098d84bac25621286092b0487023e211c108c38450c222610e808638424820ce103c080b03fd41f9e0fae07c903dec1eaa0f25078203b8c1d840e85075083a141cc80e3406ff837641b660d9206b6035041a400d04066f032e019240c6206208306c17fe0bd905d702e2016ce0b46058d82b9815800aa4053f02960146e0a0c04f302700132a092804b78252412500902046e022b011020856041081fd80fa007a503ba81d140e3e06ea036201a500cc8063e0309817a00b70058d02ae814c80a1804dc02588120408ac042b020280f7c0772038e01b180ccc062402dd015b80a1c04c2023b0108007a80392019900b4804e4021c00e800610025c00ce004600100006000300018000c000400020000800040002000100008000000001ffe6482173ffeb2410b9fff991085cfffac8842e7ffe645cd70ffeb22e6b8,0xd22d2916488af4455fa2a6514e68a394507227b5138e899244aea2505120488dc4456221b5106687fe43ec21e790edc87394389a1ba10d52867942cfa194d0c5a860c42f5a170105ce859f426ba15f90ab08528427c2135d09ae84a7423e2116d086a840a41ed20ed10726836841a120c2105ce82bc414620999048a821a40fa207110328815f409a203fd0194809f403a20139003c7ff33fe69fe74fef87f513f909fbb0fd8c7ea03f3f9f964fc667e083eec1f6b4fb0e7d613ea01f42cf9a27ca13e339f104f8367bf03de51eea4f7107b5d3d991ec30f5d67abb3d459e96ceca07a303d079e7b8f39a79a73cbb9e508f22478ec3c5e1e258f0cc783b3c081df6cef5677853bb49dcf8ee3076f73b689da98ece276503b101d784eb6275723a9e9d40ce992748f3a321d0a8e80873d939d49cde4e6b0733739839cb5ce558726d39199c7a8e34c717138a09c430e1a470ac38431c194e07e701e37fc1bf34df4e6f6d37949bc0cddba6ead373c1b8f8dbfe6db636be1b558da4c6cfb36659b280d8d66c4536149b00cd7b06bb735c61ad70d6766b1a357a1ab24d5506a7d352b9a8ecd42069f434e99a6c8d32c697034aa1a4ccd22468ec34631a280d0fe685934149a00ccfc4658633e319e6cceea673d33aa19cf4ce2e6700336d19ad0cd266668332399898cc0a65df32e1996885988658632b299510ca4664fd326b992c4c916646a32221908cc7fa63d231d618e04c6b6633f318c98be0a97452cb316b98ac4c516626a312218864c3e661d230d618604c2c0613a308f183f4c1ae386c305b18254c0e86058301e18058bfea5fcf2fd497e0cbeba5f462f9797c24bdd05ec22f4e179c4bc965e2a2f04977a0bb705d972eb617518ba405cff2e6a172ccb9385c802e2d112ccb8685c0e2df416f08b72442882db396d18b6405aff2d6f16accb5245a6c2d2316894b3e059ca2cd2165f8b2c459462c92963fcb1b258b82c46961b0b096582a2c0215f8c789c57bd2bcb95dd8aeaa57342b8995bc8ada23b322b5815a28acc856392b07157a0ab8455a12ac01557caa722cc4291d15474a9f854db2a5d15264a8e654572a1b15040a7e853d329d914e44a6ea5354299714c20a5ce52cb295a14a38a4e45251291d14878a3f051cd28d1145f0a2ac5130288794390a186509d283e14180a06a500f27f493f209e464fa227c093d6c9c9c4f3a279193c089db84eb6274a939bc9c9c4e282701137709b804d9f26bf1354c9a6e4d1625f4133c099944ca9263f0e1b098ba4c3c260d92ffc97d04bbd25ce12dd896aa4b2f258492bc895984ab5254a129cc949a4a2725009276c9360498524ad124d0922648f22466122ac91144869242412060900247db23dd11e508ed24743238c11bc88d9846ab2342919688c54460422ef116e08b2e457122a09145889,0x3204140621ce238401ca87018e0f88e120501c72041887384e202b0c8706e05e238401c21181601783e23840ac1e1c8927414e0f88e102b054811e80e23840ac211a05e138822421141824983e13882241e1c2b04783e2384600141c11e0f84817882241b1e9204405e0d0fe2384224172783e2384c4c0a2246c901ba278881784084706f88e1017084504480e0f88e1017050706092e0f13e23840280e201824b8060f88e10141c2ee208be120501c60b881e238407807182ea4805a0f8843f8401c80ba920501e20405a0f88e10072892a0f8805c05e102b1e83e23840ac15142102a83e2005e11891c1b81683e238401c181e830af88e101706060b81824a83e1388c4c07201824b88c4f8422c2b1c2e04e83e13880ac321c1824880a0f88e101b05c8c4b01e13a40e59310c70bc22c0201e938408470bc22e13a408609182f0d30384b84e90321c2fa4822c0f84e90321c2fa0780e0c34e13a484b13242fa4b8308b84e931382480cd02e0c0fe1388e9009202fa4802c0780e0c22e13a4c4ca04b800648ce9388e101f208903c1fe23a4e100b1c26a252524b84e9280064844e810981949784e90920c890a325c2383c4f84e9092224944c28497a4e102122470bc18a4b80e0e81c4f84e9036282849492e13a4064891d2501a80e0c81e93840ec9d242a49780a0c92e93840ec902406c203ba0fa4e10891c266262524ba403f8406482498989580e93840fc90202606d81e022524ba4e10192492e00250dba4e103b24080aa25e009207fa4e10900ec924825e0183e93840643c20258943be13a4274191c2801a2506192e0fa4e108924132042189784e903b274889406e0c8103fa4e109d0ec90f43320b8389784e90892025c20060efa4e101f22480d881897a4e1183274784e250efa4243840cc70db08277a4e10900ec70a82209783e13a42483d20260d006e0c25e13a422480af24c1783c4c92e238422490ad05e2384084891b2406305a4b80e0e81c4f840d8a0ac9241788e101922470ac0641783a0081e23842749e028341418e238428c70ac0641683e23842247227838141823788e100f238301e0503f88e10891c898140fe238422c60ac068141864b83e23842249078136488181421e238427490ac068178303c81e238427490cc0720b8381784e2089202b01a05e201fe10891c1e20605e238460c9d1c9d01c0681783e2384224803c3301c8281783e2384224901492e238406407183101b8301788e10891d03048305130493064b352562929a4944249892478921b48fd24765237a919c48c024569228691224880a438105ce90bf484ca41a5207c900947f423ea51f108f6747a323c811dfe8e714771a3af51d248e714738a39051c2c8df546e2a367d1af28d534696a18311a188ceb46652329118e88c44460a22f90eca08baa45b,0xc428a41be13a40fc9e13a4c4c89098524b0806e29e13a409821201be13a40d42117a4e103f0f8420f13e13a412026181860f840ffa40f8611892e93840ec3c18460eb84e90360ec6e903fe103a0ec5e903de103a0ec546092c2035e9384a0c250a09e9384098281045e13a4099890e85a0c35e93840a0181ba409b84c4c8b0a06a0f840d7a40981b188324b88e10890786c901b02805a2705e2280e1019288307280e23844142b1c83e13882341e172406c0aa270560f88e1313234a20f880af844148d1b24c1407e1388227132348c908301f05e2089e13132349c900ac1405e028106f88e10192b880738405c1e17242480a01784e20890848c9018c142b60f13e23842249062920478302b88227840509c9089c1407e138824832202bc9017e1388224211f2422418a4b83c1407e23840c8ac900ac1780a041be2384084962032e1021078506292e0f88e10170787c93050af1324b88e1089201102892e2089e10141f240142b20680e23840848c90a00609227705a002be2384c4d833011e0c0ae2280e10141e80e13880841e172462705e2384234211f2406c0a62705a0f88e1313234ac900a01492a0f84e2032202b07283e2313e10171f246243205f05060a324b88e131322cc0cb2405d89c178860384a0c182b2406c0a01589c1580e2384064ac900a01418a4a83e13880c89e010506388e10a31a83e202be110505c6c9089c1788e108b0847c901b02805a2705a0e80e2384060b0af24e2384224211b240142ba0f88e108906080609204683c4f88e100a2249c928306f050af13e138806489289220683e101ee20321f24084a006f05207880af84c4c8b2e83e13882241e17242270501f88e108b0c88c900ac141ba0780a0f88e10182b240280506283e13880c88c90a0060922758006f05e2283e131301cd06092a0d80e2384078706092a0c2be238441417218301e0583f88e11922248648182278381407e13880c890c817a2605e2183e119283c90c81764a890641881583e238483cb6488901e05e2183e1032203327407e0e05e238464889259260c33274078158d06388e10892d838142b64b84e2089208860c1864a050af84e208920890ac062072420a898178860f84648b2042bc9192018828158306289e2384064d648332740781788e108962c964a050ad83e1388224822383e219207b842746015832088106192e2033e1014280606192e0c1ee1388274801481e0f8864833e10142005e0d80e23840509d1c0fe0f84e2033078664805e2033e1183050764b8807b8407c9d1b8823784814071788e1007078401683e229243f8401c70501e0178320788a4b8401c920c8de238481407188124b88e102b0c8606e05e238401c19181c20388e10070846e23840720501c507081e238401c1e181ca481801783e210fe1007241e0178,0x1e80e93840a03c1708c9426e13a4227132348c2083c9426c4f84227a42349c2080c9426a041be93840649e13a409c350d850bc1b24b0809784e90890849c2018c942860f13e13a42408928290bf84e90890f06e13a40ec321384e90212243c1425e13a40ec321425e93840ec2114134209de13a4240361c35e13a4098361425c4c32e13a4084361d08e13a4494320846c23250a313e13a42488920290bc89e13a42483e1f080a02520680e93840848c20a006092a032527428e9384c4d833029a03a4e10260f8609680e13a4084361b08c9426e9384234211c1bc2081c9426e9283e1313234ac2026097a424a83e103223130d683e13a409c281ca3063080c989c949209ba4e131322cc0cba460384a0c3c181bc20810ff2560384e90192784e90320d81914260d784e91250a06c23250ff84e908b084706c81a0283e93840f070a026c23a4e10890847c202809683e9384224182029e1283c4fa4224261c1bc2090c9428c4f84e9019224a2489020784e9032a0c362021c20a006f250a081e13a4c4c8b2e83e13a4224361489c23250f784e908b0c8806e89e9283e103c1825a0c18e93840c8361f0828018249802772506e83e13a4c4c3d341824980a0f84e90361c280d784e912509868949209ba4e108d24070982524ba4e118924070961324ba4e10900ec70aa132488ce0fa4603840ec90a892233830ee25e13a4624989492e03a40ef842301920926043f06490897a4e118b242a09892a4983897a4e1090624a0c8920978006583e93840ec36240b09581e13a4065801087607a40f00fe10901826897a4e11892406094922318106f80e9019e1042282a4218106f80e903ce1090242524a25e9384624191c2560f80e13a4108901c1fe03a4e10190f060a1260cc9de0e25e13a422592298de0c33276250ec18e13a4224a04d838942864b84e9089208909613e13a4224820ec784c0620881e03a460f840ec92040606482a262560c18e93840ecb6483d0cc9d897a4e108962c964a250a183e13a4224822183e13a40ec9d14252088164818e0fa40cf840f8a4200664818e0fa40db84274949825e0c81897a464b840cc909783603a4e103e274703f83e13a40cc36182564ba40cf8460c3e1d92e9036e101f274609784e903d0d850f836e0c8109784e92920f49e93840f43c1225e1092e90280c860f784e90190f05e13a409e250f4509c25e13a40f4361836097832043e89c18e93840f4ae13a40f44213082041889f84e90280c880f784e9021108510041e93840f03b184020784e903b0d861083ce0fa4e10410ec70f89de0fa4e10410ec7e9192e10281045a03a4e1028084509784227a40983618420f092e0c25e9384a24262784e931364a891625e93840988906060609260f84e90890d870a489e13a40983e182909784e90260c860f092e0,0x313040800e9203384e23a40cc7c2788e938447c101b83a4818e13a4077130d08e13a40743b1109e1388e9092c4c1d1fa4e1388c4d090406e2384c4d090405e9003e1388c4c1d040742403a480ce23a4e13130749e1388c4c1007450030100b88e9384c4c102008e9010e13130881d1c1de13880401b178424ba4e23130746e1388e9092c4c1d1809e0f84e23a4008061f8307788e938403c061c10e2384e908bc4c1d1f88e9384c4e090406e9384e231382410181203388e938447c1d1c10e1388e918300a0f1f84e23a4c4e09040600a80e13a4e2313040703c09e0f88e13a400806201203183e1388e90331f84e23a407406140642788e102114020cfa4e1388084608788a0fa4e118001870848be1388e90331b84e23a4424020186e23a4a0f840cc503283e23a4e10331802c2788e9283e131303080480c60283e23a4e1006201203384e23a4a0c331f84e201de902006c606c13e9388a0384064700fa4e2280e1019180200788e9280e10191c13a041be9388e10191c03e93880cb8406460028106f88e93840647c0f88e938424b13224706d03a4b88e9010e13132249c4e9204018e1388e9089202f04018a4b80a07a40db84c7cae93840843b1020e23a4e1092c4c891c06c0f88e9384248891c2001b1324b88e938422480628008388e909de111f201203303e23a4e131307480c81808c92e900be238487c90cba460388e121f060706f88e9180e10191b88e10320644e0023e23a4e101f0607e23a4e100b084506f88e928087f8406070801b04313e23a4e101922490408187f84e23a40c870841b08081e23a402f8487c987f84e23a42241b181ba27a4e238487c181e0304fa406388e10321c1b0602060388e909de121f2418e23a46038487c1b1c20e23a4e101f0c860402a24ba403f88e121f23a46038887f8404060418106fa4e238406472498106fa4e221fe101023800488ce9388e10191f8807fa4043840650b1c20e901fe2010e10320648e23a4603840645e002ae23a4e101f040707f88e938403c211821e200fe13a42261f1c32e201fe9018e101983c803c89e23a4e101f0c87e23a4a021fe1010181de23a411384064607788e9180e100c87c70080160384e23a406470040cc0f84e23a4c4c1d201fe0388e13a40402a1c23e0388e901fe10181f88e9384110211489e23a4e10440c8600801a0303e23a4e131303090800600819e9388e121f224904881e13a4e221f074720788c0fa4e13130747e1388e900287c891889e23a4e110bc4c1d1c89e23a4c0f8443c1d1c02a2788e93840321f1c0cc0f13e13a4e201d1c1203388e13a487c1d1c1203180c0f84e23a4c4c02241fe1388e901d018607f84e23a40801d1825a0384e901b0ec606f082072509ba4a0384064909e80e13a40a0421883e13a423436141b20583e9384c4c3f,0x10c4f84e9388a0c891fa4e1388a0f13030891fa4e138804032141303283e13880c8603388e9384c4c45181204003e1388e93131148e9384e20100a85037a4e13880402a180c22419e13a4e20321c32e23a4a038460c2a1c32e908be2384064603313e1388e90020648923a4e2384c4c89040644fa4e238422410182ae9384e201006c6e9388e10100a85e23a42241911120310de13a4e23130748207a4e13880402a191200ba4e1388c4c101c0260384e23a4064603f13e1388e901907470028100b88e93840647e238404033101ba27a404384c4c221fa4e10100ec4e9081e1388c4c101ba4e138820713040604b80e9384e20100a8707788a0d80e13a40a8707788e908be1313040744b80e23a4e131304070080160283e1388e902a200200580e23a4e1313040804810a0f84e23a4c4c1d200ca0f84e23a4c4c1d1f80e2384e90230606e1388027a40360f181b83f88e93840351f1f84e2009e900d43c6e2384027a40350f180303788e93840c8643fa4e1388024211835a48180db83e13a48270f27a4e103b0c8480013e101be23a4084724b88e13a443c21181be23a4e12830350f1c0d00b09e23a4c4f8404080c90fe9388e1283060700801c0313e1388e9023201be23a4a0f8483c181c09e1283e23a443c1b1c09e2384e900b0c8606388e128343fa406c70480cc0388e9313e102020330a810c4f8403788e91092492007a4e138883c101c92e23a4c0384c4c101c32e9388e11830320f1f88e938442f13040603c0de23a4e10100a8700e9203300e1388e9313008900801e2300e9384c4c10201860f88e9384c4e091c1b623a4e12090846e9384027880845a0f88e93844241b1a83e13a4e210906c606e83e9388e1313824706283e9384e220906c747f84e23a40241b180c60f88e9384c4e091d88e13a4c4e09040604a83e13a4e200906c7a0fa4e1388c4c0c8247a0fa4e1388c4e09030724a80e1388e9313008700c92e9384e2280018700c9200b13e13a4e2209229206006e23a4e1009c4d832784e23a4024191418a4b83c4f84e92090d0801a01603a4e13880847a4818e2384e910f074707e0107788e93840847c4f84e901d0d0211b84e23a407421140600784e23a483c211c1860f84e23a483c1d1c13e1002a03a4e20211c92a0fa4e1388c4c1d1c92e9283e13880cc624ba4a0f84c4f88074706012e1388a0fa4c4c1d201804c12e1388a0fa40cc864806e23a4e100987c7e1388e908bc4c1d18068041de9283e1388060804e83e9384e201d060706388a0f84e910f074706384e23a4c4c0222c7e1388e901d0805034092341803f8807784e9033290164818e1388e920f07480278803c1de13a40cc8b2384e23a460e0f0746e9384e201d2481b1806e13a4e201d0606e13a442788008061802e13a4e2313031091c204041de9388e1,0x402788e900d42c602784e23a40350b183708f03e4c0de1388e9209240be9384e200908460d692e4c43e13a48270b2013e2300c0fa4e103b1c0d02f88e938408c181f03e1388e910906c600801c0303e23a4e10182026623a4e12090846e93848242113a402784e2021140c64f84e23a4c0e091f03e9384e2293032091c92a0384e23a4c0c1b1c1324b84e9388a00201c92c0fa4e1388a001b1c1bc0c2004388e938402593261203034c0f84e920906c80278424ba4e2032182080580e9384e20211c10e238442fa40c86e1388e901d0401b1a1280784e901d0d30306c804388e938447c32182000784e23a482c211c10e1388e920b64c1d1f84e23a40270306c6034090808d04388e13a402c3228104060be1388e90321d0324b84e901de201b1c92c0f84077a4e201b1f88e901d0801b17a4427880801b1703e13a4e210906c604e9203384e23a4114706f09e23a447f840607e1388043a40741b1a9204034e13a40770306c8c0f84e9092e20321ba4c0f84e21090606e9303e101de201b180003388e9303e10321c1dc0f840338806c602303e901de102206c704c0cc0f84e23a40c87c0c92077a4e201b181de23a424b0306c620384e23a40801b1820e23a4e100b0c86e23a4c0f84824181b03e9384e22090606c0f84e23a482418180ca0303e13a4e201b1c0b02788e13a40801b1c1203384e23a4a030306c806c12e938842784a4c20201240703e13a4e20321c21e23a4e1180a4c201f84c0f88e910906c642788e910be1032180ce9303e13880c860480ce1388e910b06c7623a4e1032084504b84e23a4018321881a0388e93840846207a4a0388e1021181ba0384e9388084606f88e9180e131308c7a0f84e22120c8544b88e13a422c21181ba0283e23a4e10181fa4e1388224211788e9283e10890606c4f84e23a4a0c891a83e1112e93880c86a0d12e13880c8544ba4e1388c4c45181200680e9384e20211c32e9280e238447c181e12e23a4e108b0846e9384e200d0845e23842242113a484b84e2183c4c1d1fa4e13130743b140260384e93880846e93840ec211188e938407421141da0fa4e1388034181c0200580e1388e931308c800801a0c0de23a4e10182212e13a4a0f88c4c1d1e12a0fa4e1388c4c1d1c1206788e13a42241b1c1be920fe238406460181022784e23a4c4c0d23a4e23840351f0406c4c89e1388e90190347a041be9388e10191812e23840cc19140284a89e9010e131308888488904388e93840c87a041be9388e111f0407e931304384088321881a03a4e2384c4c101c81e13a4a03880646207a4a0313e13880407e9384e200d87c101b88e10100c8406fa443f88e10191a1201ba4e1388a0c321c12e03a4e1388060231c8be9388e1313040606fa4e2384c4c0c22c7e9384e2313224101ba4e2283e1313030891c,0xaa0211e2183e1205648cc90a320a80600146488c02a1160f88e120538210529264a11e2089e131362c172e2ea0f88e1205648071e2e2341864b88a0f8481407262e01683c4f88e119201c88b89223005a0f88e100707898b992e2017e1313a0c2b222e06005e2283c4c17e11920aca04f8860f00e13a40ec7c0384e901b0ec504b00e1388e928306c700801e2300e13a464c232002e1300e23a406460080160f88c0384e902a2037a0402e4d83e1388e900d2403e1388e900d06c608ba4043840620d1809c0384e9388a0c1b1c0200788e900de1193040800b84e9300e2021180200583e23a4e100d0608a0c0de13a4e20194247e1388e910906450030106f88e13a464c2323a4e1388034321580e138806fa4064660f8884b84e90321b88e938482421140804384e92090881b1fa4e1388824211788e938464e09040660f88e938482418181282419e13a4e20321e12007a4a0388e10211d12203a4e1388040181c0de938804384060660c00043a4e13880c8782403c4818e9384e2193074922010e13a4a002206c7e2283e1180e903b1b84e9388424211400c041be9388e119304082201de13a4a0c2206c7e13a404022424181b84e90490c8410180e1010e902206c7e938412421104660fa4077840881b1d9322384e90220c8211c22e9010e10184346e0f93c48220bf84e9039218008b84e90350d86c0434e13a40d443183908983e13a40d8664f1208b84e90350d87e13a464c3910c5e91880db84084321b88e9384424211580e13a406f88084660fa406384e20321836623a4e10210c86097a404384a4c22074722010e13a4a4c1d0887e23a482612e1193080760f88e920984b84018780700e23a4e1021198804300e9201e10181e01c03a4e23840846c0201e9388e128306070480ce23a4c038464c202300807a4e2384a4c101c1203183e23a4c0384018803409e13a4e201006c7e1388e9209084502300e1010e902206c706f00e13a4e20211a12c0f88e93840c8684980e13a4c0f8806c7623a407703e121206c784b03e9384e2032181de9384e200da4c101c0200580e1388e93030a88c0e12e13a4e229307470cba482f88e10191832e911fe2384034181e1200a89e9022c0f84060800784e9303e20321881c0fa4a0384e20181fa4e138808c18140de9384e2023060603303e23a4e128006c7e9303e2384224181b03e938812889060640fa4e2384224181ba4e238408c181703e938844832151202784e9388c0c321c81e9384e2023060603303e13a444b8806c704980e1388c0fa406c702c01c0f88e93840c8700418c0f88e93840c87e23840604513a4e10180ec400a89c0fa408b840607e9081c0f84e2018181de2180e13a4a4c231c1de23a423f03e10181c0200580e2303e9384060803303e1388e9293074703788e920be10211b8,0x9388c4d0900810203b067a447f84e210900806269206313e1388e91830748e9010e2384c4c1d62c760f84e938808713074724ba4e238447c33181d01810c4f88e1183e9209648a0759201823033a4e2183e1313824b0cc0282788e938460e0f6489824236480c0cc02e9388e118383cb24a1fe13a4e201d0187a0fa408788e1006074708c92e1283e9388074062002e9388e1283060331f88a0fa4e11920cc6037a4e23840cc211821a0fa4e238442592018808e1fe13a4e2109008062021e9388a0f84648331c12e9388e10210cc60821f067a4e238442402018908f1324a83e13a4e201d018904101a0fa4e2384c4d9207490ef8824ba4e1280c7c1b2089e9388e108dc7c6e9388227842371f1b88e9089e108dc7c60efa4e2384248320847040800ec18e23a4e131f0c890c82384ba406388603846061f282306e12233a4e23846261f2788e9089e120b64a1f1c1b64981077a4e238482c212481e23a4e121f648321c182059204388e938487c32241f04081e13a4e20200c8806081e9388e121f64832202a84892e9010e2180e118187ca0aa1224810e9388e121f6249e23a4e108987d9283c7e9388e103208450640ce23a46038487d81201903388e938487d891fa4e23842259291060efa4e1021e22440c8720788c0fa4e13136481d200d6480c22788e9384c0f13074a64ba4e238487c1d180c207a4e2303e13136481d24288952506f0889b84e9283c4e92624c0c8a306283e9180e13130ec9494a3c222506c8c0efa4e1283c4d893225497080f784e9089c4d92a2ca0ee25227080f525e93840ca8b084b0a2254970820526e1283e91920c8b494a0c222586c8d0efa4e1089084b24890a0f840cba42803620284992506192c2081e13a4280322c3ca4ba4e122562c3d1c810f183a4b84e903d0d8810b0889e18e93848958b0f491088cc222760f84e903d0d89903a4e12410ec3c1a40e13a40da410ec60d8a306183e9384a262509890fb0820a2960fa4e103f0f090fa29227a4e122562c3f202bc902181505e228360384c4e92604c0af2406e0541788e1283c4e92624b0cb2428d050ae0506292e228360384c4d813b2428d050ac1b23205a4b88a0f84c4d8937248150501f88e1089c4d92a2cac92054140708784e228b0c89c92054148101f88e1283648322b242810586e0523407e2384224212c92a0f88e101e280321c1820788e101e280321e92e23848158b01c62069260f88e100707878718be238408407188c87183e2384078071e1622583e23846482b854885983e13888542b078707a1602a8160680e2183e1192854b28e16a06800788c0298164b8860f84854d85992e23848542b078707b8860f8481592a24728c1e06192e2183e1205a24905211a0d83e2089e1313648172a11a0c8d60c1864b88e1089c4c172f24209800500,0x84a4d8923a4e238424b0b0c860884907588e93848270b08490efa4e23840870b0c87607a4e2303c03840607087a4e1303824060ec7e23a4e103b87e090187c07a4e2384234211810e13a4e20200c8624b84e9388080321820e23a4e1303648321c200740d86fa4e2384600212406067a4e23844261f00820242a24b03e13a4e22930801d2418407a4e2303e12936481d24202741820680e9388e1183c4f122c23063a4e2212603846061f24230301be938884b8487d89243ba2fa4e23840c8211e810741be9388e128343d0d24200841be23a4e1081c4c8bc48ae1283e23a4c488906c780788e938422f120c870809d0601be2180e9384a0f13c48b06388a0d80e13a4c481b2181e9388e120d08460efa407788e118b084708c18a0fa484b8860384c4d81282306002a0fa484b88e1313624ae938443c100ec5083122042a03280e909de238460f13302a043a46038487c3b1c2a06c0ce938884b8487d8924320a82384ba40338860283e1313604c0a82306e12033a4e2384a0f13624b0cc2a043a4e238422512c4e8b2913a2fa4e2384040321c2aa041b04388e901de1112a0d0f2e810741be9388e1180c4c102420c481b04388e93842071322cac4ba4e2384a0c8906c780712043a4e238422c32201bc48200a80c603a4e209de1283c4cc0ab12033a4e2180e128306c9033a4e2280e101b064744ba4e1313e20890407083a4e2384064321801e9388e1032064603433e920fe23840a81023a422788e10100a8643fa4e2384224191912e9384e23130410d1d1280410e9388e131362c1d243b07433e9089e238443c102713e9388e108904060a810e2283e9180e131360490a810a0f88e13a4c4d8923a4e23848270f06460ef88e93848270f084706f88e13a4a0d09a490f201ba488ce23a4e12834250f2788e13a40260b64a0f1e0be9388e10210c860368107788e938443c2123a4e2209e12830630f1c92008206051be9388c0384c4c102d81e9388e120f0406c040600ba4e2384a0019230101802e938860f84c4c8d2492e9384e22090091f1f84e920947c020ec6c041de9388e108bc4c8d201d01ba4e128343c3b1c0600b88e13a4a0f13a4909270101802e9388e1283c4c8d2423c0418e23a407492e131322cac041de9388e1180a0c1822920180206388e93844068343caa488c01802e23a4e1283c4d092b0101802e9388e118006480370107788e938422c212113a2fa4e2384074211c0600b01e9388a0e80e10182406e1283e9388824020608e2384e9283c4d9207476481804388e13a4a0f130749e13a4e221f074201821e9388e128364b1307480181de23a4e118383d9282496480607418e23a4e120f60e092821e938460d090183b1c92c4f84e938860c1d1d1fe13a4e201d0186a4818e9388e111f0cc7e9109e2384c4d8b040708384e,0x21280d8008c18a4c684a0308c18a4c56021f0640c121f0640c0c23602030ab130303b1c1b2242a80f138480c1e1384980a0c2a04068488906c0ca0c2a1832205800aa1f030606c890aa1f030584d83806800740618188068007406142183c0660d92824021e0983c330084e23a40ef84c0019183be9388e10320646607a4e238482c18180de9388e110906460803be9384e210906c70740604280e9303e11930ec90a810c0fa460293e103b202a0400284b03e9388e1293624a227a4e238442c18181dc480608c0c207a4e2280c0f8464cc117a4e2384a00191b03e9384e20890606607a4e2280e10191981e9388e1303a00181fa422788e101808c6e9388e1089064544ba4c0f84e210d06070743be9089e2045e10182303e9388e1089060608c18e2303e9180e1293604908c18c0f88e93]
def g255H10 : Nat → Nat := chunk #[0xe88d9b979008cad6dc561d61acf3f7ef8948915136d5514c560a3825331180c73d98a0f3fb5f646634b3948f209d14b8d6d748000000252f70d262f157395fc4fec891b6305fb6a40000000000a95e21349d6cb60003469e2928e95ba1115c1f559d000126d9875e50e69d5d400000000002d6900015e4000000000025b411ffe32a3d310e0000d0000036124aae53ec840eddd8aa4815a7866a7437241635659a0000904f1cc000000208f91db5f76883de0730340e000299c00000002724000eae484a1638e7663419314ab1c8b97cec569a48436da0d5d6470a64bf00cd53439523b2608e62c0c4000816f5f8f528000000186a2a700005936c6553b19146370000c6ec89692a1d60d8ad28746f400000025ebe444506c8709a1585329af221902680507249c1588111a966aaf6d5e0000000804ea9bb967534750e1d7c238c3bf0b80008757d12a01a627163f0d4f1c1a6500030010002ab2476a5ef4460d4dd8b0df054f45b000000000001d3c0000000a26613bc6300001591e22d2fc00084c31686985e3187200000003e3f0001c1120d5d5d3af1ee23b3800000000000000000f80080b000360fe5af419c4a2995989000019d3587f60c9ae6a9a66c000299b61ee2dbf28d959000000013b70143416de1f613c0a406c000842c0000003d85f14c00056d7680c929ee331fa6dfd85b68229246cc6aa5c15e39867bb6dbac7a2e2e9fb3a12778afbcaff698ed555c899655dfaae9187a5af94e4236a4cd56000265c0003a6e3b080000040f0080100c040100300c1300802000000000300801000020000000803010040100e000020000b00c01024000100c008020000201416000000080000c0d02408000010001f000070000d00c0200c040280002c00004010040403c04008000080000c11000010000300000020000380000406000030000100c0e00000000000000001012000010280c01c0f000010000002c01004020000000003010000080100800008040782a0000505c01010020000304c00018030000000c1603c0b0001601c00010000500103800038000100000000000050000000c1402005000000040300016004040000100800000070000102c000041e048000080000c0000806010000000100c03000060000b00c02010080100201c02010000000402000054020000200c000000200405000000040100800008000000200400014030000000007008010080a0240000c000101f00801000000040000000000010300f00401000300040100401000010481500c00008030140000001008000100403800000000000101001004030000400002000000340a08c0305800014040000100c120000103c020000400c18000060041801805000020180000018000090041300400038000000300c0004c0a0000d00c05014000000000000,0xe94e224f26f2b0f517470324cf20c000781acde92859ab0001ebb0003a8ca1c4000ab4299200019446a1a8c900029f1c2798f0aa216e7a3e98ad950859358cfed448c3c2d155d1e2838326b19105b123ec8eea5435a8579e17ab945c39dae2aa3e5e74ef572dd1f132227d32169f2b25c000c4b996254a7c867563ded0002d03a1f149a2832eaf1a13ec4805bc3c373c817f3af699bb64926b9c6d51fad997b2022a2500008a7f9fcd9167fc00000008bcc2a6eb089215d8e5029ec82cb06ef834000c36de07000000057e6a260001a790001e9800000007a86eb1000000017440000000589ba3c000000116c35c7c5e00012ca0000000576644c0000000e2d62d165f4000f3670ac000156723f000068d79af246f8f93b928f5f0a9c02407b1acf739c92536b8f195f054530bccb9742b1474b2e8419734000d06b90f4b209488a77c5d8b4b99ea6cb863aad68cb7164ee586b58bd18620c7103d8cf63394abb9a657e3714691f2ead0c864112bba5400000034d100000000002dde0001084b084e56b96c000d0ac933506000022fbee9560614c00000000000000000149bb6e8000b0cb99fa1b0000000000079630d7e62c0003230000000262195c04f757d059746f8a3cd4059ea3817c8a5690000000205cb2718cd9712546e4b2ce33a9cc80c09b90847989526a3b8b488f561f113cc75598f510c6295aad07e0c6b135e529048e4e24ab07aa37400000000008a15541ab7000000030400000ea0881094f280c00041a36b3f2bac78000000065d7ebfc991628986c0000000000c240e3a8198000000281d6a2bddb297c0000002a1e7651642f024000649e8987524ea8b4c800000024b1000000084dc00000000000002e8d547605a28e1e361091ee0e08868b62c106d968102c22df290209c5e5a9e8ddf88e61c1e866c4b6594000747ac3a0000dfa811248d741f49500000000002296d489aaa9183cf80000000000000000035357b840000003a2ee0dd95a0000aad6467672a124874f7d4000b1dc0000000ea400039bf00029c300004d288440008a5ee7c752d429383800065a80008ade4c30001d55000000000039b88b17430880a49d80835ddc3621fdf034e2dd770c8775ffa1a55d8454a473c6470cf810a4ea4e41497851da97eda000304540fe6b40001cccf307842e983e29ba50000b9f8000a85c0000000000fa8b52dd688000572ad16b4e00001b78000c5b4000313b60835e0dd093fdac6768cd8de7b8dccf7f8000c7a2268b3aa8d37601c824143e15215fcfd469495b88dd920591c9996b00c6f558e539cb2524f782e0f2244cca2595300062985e9390dc58127e06b25d2d73218bcc2695568180725242386807000211a591b8aa000000000038a5774f0e21b5d56e3122289e71bebab427e3449774e7f01525ee9cf879d8fa5e3,0x15fcb82a855fb37c040003a67811f266919c8bb9244000ab3c000000000070fb6c1f6f0ad61487ed3f10d6e6e9e0838f5be1c7f6cfc3d437]
def g255D11 : Nat → Nat := chunk #[0xe629c6e382e6f48dc21b3635e26a44d1899ec332a64f8c7818a230965ff4bd3174f2e025b14b44963b2bec56c4ab61515297c51c0a1113d427304d4c98292ae249c47dc8d0115222084320846103e20043ed07bc0f2a1d9439846fc0d981a4c333c6378c1817702d3c5808aaa148227cc4c989451200225c41b87e00eee1c5c35b86450bdc163829b84e008ee10a41e9036906360b1013b023a03b4060c09f00f9016801e001e0000ffd485dbff4e176ffd085dbff5d974ffe685d3ff5a174ffe385d3ff4e174ffe085d3ff42174ffe64dcfff59373ffd765cfff9d173ffd745cfff99173ffd645cfff9a173ffd685cfffd2173ffe485cfff52173ffc485cfff82173ffd085cfffdd163ffd7458fffdd943ffd7650fffdd143ffd7450fffde143ffe7850fff5e143ffc7850fff9a143ffd6850fff82143ffd0850fff99370ffd64dc3ff58f70fff43dc3ff50f70ffd765c3ff9d170ffd745c3ff99170ffd645c3ff5cd70ffd635c3ffd0d70ffd435c3ff9a170ffd685c3ffd2170ffe485c3ff52170ffc485c3ff8e170ffd385c3ffdd160ffd74583ffdcd60ffd73583ff50d60fff73d03ff5cf40fff76503ff5d940fff74503ff5d140fff73503ff5cd40ffd63503ff50d40fff78503ff9e140ffd78503ff1e140ffe68503ff5a140ffe38503ff4e140fff764c3ff5d930fff744c3ff9d130ffd744c3ff1d130ffe644c3ff59130bfd48ddaff4e376bfd08ddaff92176bfe385daff82176dfd76dd2ff5a374bfd38dd2ff42374bfd789d2ff4e274bfd089d37fdd974dfd765d2ff9a174bfe385d3fb8a174bfe085d2ff4e074bfd081d2ff5e264bfd38992ff42264bfd785937f5db73bfd68dceff52373bfd08dcf7fdd973dfd765ceff9a173bfe485ceff82173efd7658eff5e163fbd74d0eff5e343bfd08d0fef9d143fbd7450fef99143fbd6450ff758d43bfe7850eff5e143bfe6850eff5a143bfe0850f7f5db70dfd74dc37f5cf70bfd68dc2ff52370bfd38dc37fdd970dfd765c37fdd170dfd745c37fdcd70dfd735c2ff9a170bfe485c2ff8e170efd76583bf59160efd63582ff5e160fbd74d03ef50f40bfd78d02ff4e340fbe74503ef5d140fbe64503ef59140fbf43503ef50d40ff960502ff9e140bfd78502ff9a140bfd68502ff8e140fdd734c3f758d30fdd434c3fe5c130ff9604c2ff5e130bfd684c2ff52130fef76483fb5d920fef74483fb9d120fed74483fb1d120fee64483fb59120fef73483fb5cd20fed63483fbd0d20fed43483fbde120fed78483fb5a120fef48483fb52120fed38483fddd910ff576443fddd110ff674443fd5d110ff474443fd99110ff564443fddcd10ff573443fd58d10ff743443fd50d10ff778443fd5e110ff568443fdd2110ff548443fd4e110dbf749d2fb8a174fe970483fa50120ff160443fc50110,0x2043b13c26931019240380418a82188d2612264827061806e2309a4079183c26234809078c09c4613480b078c0d01c2711a4c20401e404a2784d262042091c401bc469308090f8e030861349888982471006c2483c262349130492060c60d2513c269310092402920ec4f09a4c408480e81b0601c4613480f206602c1c4f0988d202480362349840487c600e234984418762638cc3b8307e1311a4049003002482113d26131033252403808003b13d2610218828241d0360e2784c46901248486602c18270988d203c9090022788d261106332025800c8634988c207c844e2349840587c640e2349841907c6096003210d2623081f211388d26101e1f1802190660311a4c207c80922711a4c21106092040188d26103a1f22102644c9707844069226922a109292861018344e1349131f97081306e4a81c060f09a489a48b1442031254960f498489a24a8420c4b80492046d8489e90762130510892e0f09a44944d124a4a1125c18ed01a4c244d02524a103d92e0f0913d22249842064b801de91078489a48a840952481c006627a441e10785a4a108992e134913459092840a24ba441e122689246d0849201032589e1348831916814060c7b84d209524442106814009c43a4c20f44a51012481c18ef49842090264960f498412a2471f42124800de0c5384d20fc4a59187e9240a00763dc26907454911305c1e23088089a489922491305c18611a80c4612265c90370540e030784c444d2450ae481882a4b0713c46111254903c83404152481898cb098810982b92417069289e23088926489215c1707884044f08812a489203c170784c444d124c910305c0621078489a489922490305c00610713c4610325c91248982e230913459124490ae0b8841c4f088926481e49201030589e2308831916814060c0f88c201524420d02800e08711840381490b2490089c1e230815212583c46100a891a489208e03061b0a6230805285c9240a010788c201c0a4e0f27840962348091d1183c9c4b0909d20f08496030625d261078460c4a89d2610644e0c0b88c203c69260c0a89c461068f951e163a046e98d49197e30d45d58b0f152e275c49d889f102a1d9c35385f90ade139423683e3068e0b8411981a9021a017bfd87eccfc85f69be8e7c6ef781ec93d4479fef2c56d2bc5a7818eef9dbcbb107584e9f5d1339bd72bae419c5338466f84ddf5b9c36fc6d5cd981b0db5c46afed4c5a68b47a6822cee99bab31e658ec9558ff3195626ac30d831b00c5f8ebdc178caecb5ce8b8996f0ada55aaeb4256592c76582caf695c1ab3555bcaa1d518291c53d6a6994b0a91c519ca1b941027db4f2c9d21381a6b54cbc978d2c1a53549ce926521ca3d947168d19180a2b344a688390dba169422482ed036a01f3fb47e54fa39ef03d447950f079dca3ae6747,0xc461032323a2689d262308800c8e0d44e931184078407d262309134484060606e2689d2623081920541b44e922788c204080984b4988c222432384c258041e1311a4080a89c007f498806610323c0d0784c469012928790920903c3009c1e13498819143280a0711a4c220d250f24243249424321841e931184879712490241f88c269106322711a441e122692848e234906107a4c4612270924661dc1c4f0988d2025244a48660d0ee0e268dc2623481804990341a4b0988d20262602242503418612584d262226090116060080a1388d220f09134914014901805134186213a4c461032624a24330e82711a4c244d1654492483c26234913048089c1a4b0988d244c3a380a26184960f0988d20cc9030612583c269311130e921300e0d2584c469066404c03834061311a40e818904e0c1f84c46900433222692c26234883198e92c2623481f0e8d0140e2349844024a3e4035121fc469308801090210da070188d2611251f263fa4c461112211924010f86d0380d261310212b11a449611131f184312496234880c22063e48862492c461348898f903b09e0c3612c262348092426838484b4984c440032480e129309693098880064984e4d0784c46901a3c270788d2611260d1f0793c202711a4068f83c98270988d2034709a0c2509d261310192033010060d27a4c2620243228260309613498810824809a0f0988d208412380d2784c469042091f06320962309a41d82480684b09a4c408412384f0632c4613483b04901209c271083d2610423b2486361964f07804444a0384d20e4426c480600808c927a4c262042520c2612c262348190490030924f0988d206412404c078400e931100109012104032601c2623481d419412034030601c4693081d49940d0980f09a4c40841242272784c4690160d1d139381e134988068e1300690258481e206440045410c040c25a4c46112652242588c2690320b1c248906e2349844006206484d1303c262348800c9013408020632c26931019240380818604788d2611264827261006e2309a405901306c270988d206016404a0784d262042091c2703c26234818048e120340f0988d224c12408021934940f09a4c40249080052584d2622063220401dc98071184d202c82286e0784c46901239141388c2690640b1c26004906207a4c26208a484c00920640f4984c40c89090803b9381e1311a4049245098481384c4690360b2425800dc0f11a4c2081264a270788d26101e0d1d022189e930988090c88118630012d2623081f211383d26131113068e81018003a1289e9309881094011186300830969311848994890962349840c83c7092241b88d261100108993800da042513d26131019242481086922784c40c881504301a409623081f2025800620f4913c461032480d1313c262348800c900300,0x3709a4c404012181d020dc2623480b0c0e8106e1311a40784070900501a408613100d0c138800a0309a41d8c8706e134809c404036384b1083d261076211c19840ea0f49880d8e1200a4f09a4c40c842461349884987420344d2712c40050103d261076544d278481e234912449101096920784c403430404b4988c240d12181c0401092274984c440c30488c1912c9c0f4880c461102508c1912c9c0f4984c4224901a274988c220032383513a4c461016181e07a4c4611121818180244e9311840c8e230140d13a4c461030469311844486450900f0093c262348230c13800fe901988c2064789a4f0809c4691250b207693490841384d2622164882263281e1311a404a4891044d240d46c0c6584c4690200931258481e2348090d8e0c0961207a4c402436440d2584c46903a1b1c0503490432784c46908a4881241081e1349880e86c9018072692c262348452006014061311a4100c880482f0988d206c8a380c0293c2623482019110341e234880c244e2481260683c2623491389224880a0711a4c244e248b2311a441e122712448e2000a010313c4693088319448b8084b4984c444c1a102025a4c46122689080e020084913a4c262226102454120644b0788d2203091340962a090322583c46930913449412c020e27a4c26201819242512448642188d2612268b2854128920f4988c204226892824011044900818984107a4]
def g255H11 : Nat → Nat := chunk #[0xfcdc6262a028af47100000001a0361770a0b2b91dcd2d191db2c339a46a8001851e2540000001a0f0000000699caf25c2c0005164b580000f369ab20004149c8bad0400029c2000782b1697f940000000df200003d84af4929c62a8696f7b2f6ac43811ecadf5426daeb91b8a0003e79d0a14f5a727b5e425c2ebec5bdeadc00ecc2bde695a5e7fa4800717dcbc2a9657ec40a8052661edec8e22f646557974ebaa00b9f00002b9eff1217a0004e8b367a33686177c2f11d9ae0004d23792f3a565554f370c56245b7a361b4e6adc000000000052bc7cc753e00000000004dcb173e2a12caecb2f4ab879f5a179b4583ed775fd4f157da04f57f1ba625bc32400047b5b9a4c8f7b171b5e250001df3b9d73200000e608001a32800184691ce000000103ef5770ddcc1128778f874cdb1512e93d3c2321a741ecd455446dfe6fe6bd4a198001b8f80018408000000008040060000500000000c008050000080180000000000003004000018000020000880000000000800000048018070000000080000001c00006000000088000000000080003e0000280100c0140080100400400800000004000000080000e8120000000000201000c0000200a0080500000002c0080000001c020070000000300000600000806004004000010040040000000c018020070020000181900400407000000000010000000040280000000000002000008018000060000100000000400004000018038010000040281a004000008000000000100d0000000080000a02c02804000000000050020000000d00e02803001000004000000100080000a0160040100608c04400800000000000080080000000300000008801002000010000020000101a00800000000004020000030160100000a00a000000000020000000300001c01813006004000050120080400200408c088050040040200801400005002002000000010000100200300c000028000100100180100001403006004014000000000100180005002c00018008024000080020000100300000400000000000000000000280000000000400000000044020000000000000200e000020000060100600000e03806802000000008000000000080000a0180000000000c0600600c00000005000008000000500c40000200a00000003000000000000000000000400c00000000006000150050000100000400204c0000000000001009000000000010000040b002000000000000000140000000600401005000000008200020800100000a03c0380b0000600280000400c080000160040303500e01408000004004008070340140e800016014000010000000101500001c0000009a01400003000000000020000080100300000001006000000018000100040080000204000010000018000020040040000600201807000,0x56800017189b684465d2e0004a87c4fee857b2fced89d571833ab1352e21312000000000074850607a580000001e89a55a00028e7eb5ae2d9e1753aa303db4257e824af2eb720004ed4a3a9ca2a2d7d570b7bce4b639688d81af297b9314fc28db2eb0e3e6d3c56611f8d0df000062b70ef2c278622bad76fae90a5c8a47f720c3a00063c5cb18001d430000e1d800198f0000000515000000000000000a9200000000001da0ede96c75a2c942a63800018feba680000002c2eccc3357d3df62824af489c03f11355b7f8115922387ef6a7fc9c39fadc200017eb7b005d6428920bc839cbbc9408fec9638df6799407bcc683c466bd490e33777e06ff19e2e20006eacf530000000000000000005181f700003332765d57580a00007eaaa76e2f90dd28180000005e870797a6cd1451f47c4bdab21f97218396a9bea2ace24224f87cfd0a7268a467e83f7bd707bdb18d1ffbccccf264ce4e715b06f38b1ae3c88237b9ae8fc1b943f033dd5a331d8a685a8862a67b065d0723031726dd47dfae7b05c2922f8c1091486d300000000ec8f906b0514bc2ac00000000001bd56c34478676f88278e9775d56bb135860000000063400005b19bceb7774d8687c58086e38a4b80432d7b0c391623b63a00060907085696bbd6e36334d62e6411f1c00066ebf2542d83d5ba7c0000000000000000076749ec80000003a851df8000c04800000000000001d6600000000007bb80006e9296a7f34000000000000000002e057dddec8000000133f3670c09b44800079d3873670dfd17d4b21c5884f19584a9c2d3e88f448f63c10000774a9b7512a0ef64949ff5f518c60007c023bdd5e6833b352000546fea7fe57946fdb36f93d8d486f26a6c9fa3ee26da0ed80fb513f3674d9743a83ec27e72cc3a748be75a8c655e07ce9013ffb6e34a0fb8da4d2b1276ca2e3f5337625bc30ce2354ec9c133154c3f411752c4ec329cda7db6a970cb0de841098668800062f0f42c0b0000000000000000000000000c910e1d4f7a22a0000001335c61bc66000000019c6c64399b11f4ae12c1777564a4bee794f751d7d634aa36f9876130f1181219cb9a76881ab54ba188100005af80000000ab8000000000000007548001a1580000006e5a0007e6f9305e18d66a8167ce209fa6c6501643b5f2fd8b0a929b8001db4800176572fb3cb53a8db4424a96212a667f0f7d75b93c093427d2b5cf94547cec930a8ac066db0000000620b8eb89de000505e6450000000165e000000000047960000000b41b74a7f2a8d9c888b58d370001dac6f46000573e0003a3637359ace1a294dc2db48ce970abfb30f13c47443abd96195d3001c7b71b4aae0005554532c834000160bb408001d7b35138f1d0500001782ac7ceb6357c716bf46a6065a5cb6f3336a85ae459cde4b67b,0x1a07000187b0000509627a5565b79e945eb5121cd1d5ec17a9df19eb2000000000044df929412d2b0f267bbce4e875f4f2b68008ac4032cd4bba7e766437b5a9bbff73b0f10f49e413be615140f80ec7d9733baadd68e5db4dbe404f71de63106d1b351d7aca0002cfb739c6fa00053860001457ac416e108841be45ac9976480c9c0002cee0003d146bca68f422b39c0000000601f33a0003f26d99742a750dc446e014c4f20b4fef45b546000798d68911317e820331eec2aaefcb364f324b49ee164aa3f0000043780000006ea71ef8000b43f09200015b06fb00016b40b3f0f715b63ed939388e8001b520000cbf65f8842cc18cca000000000000006dc0235fa0ceaa32d2f4f43f0000000000058d4000000000000000004590000000000025829c0d0300004de4000399e000693767a89f821080004320001e95da32fbc0000000234ec19578c0005ed885676e600052a5fd3e06de2ae9a9be39f5bf4df9a1593fb95f83fef9b824c53e98deae000000187a703e00036fcf834c998f817d7f16abb77461f1a984fa1528f00016cd75ac6b31ac1ad374b8f4a5e16af0800000000007789e140003a5f7b029bba706c9b464de200004d71038000000060536276f1e000298e0000000000181042ce2b5a29ae518d8dd78d3e301afda80000000001ac2edae24eae66a4caf8a00036bc0000000665291fa9e248b9244bf65421f3c8df8f0eec6e97e71053478bb0001b1380000000874ced2767ba30000000338200021000000001c44000000015ba0004ececc80000000541cd2a3598000424e0002926000661e5160000290d18b0dd72fef47dd5cf69daf9f90a5275cb800000000004ff3a5b3386c7800025637bf8000b1a70c40000000630800000067240000001fa6143725b6a68dd7d398d9197aeaeedabaa1c945f448d355fa07a53ea5705af1aca136d176a0a76b058cd059e6b1c180987666a499210f27e89862eb6c9e2d785ac8788ccbffe7c291c3b5d41bd9584054d0fb83e240bae5de28eb020b7139178211711e403da19664f9b174cd0c837307f9d458c26ec25c235da45a804ae35c96c0643a2f53b3036fae73a8b3e57a3aad06b3cc8001252e92ed08c584561e9528ce1e7cce5c477e992c737e98000b2780000004a187de200a964d367a08a0d3ba880011c880007d7]
def g255D12 : Nat → Nat := chunk #[0x98393840088a4122048260e4c021222903498393098488a4121c4a0e4e1292202478393120984a4881e0e4c4a122290247128393008884a401204a0e4e122290247018093038488a41220044a024c0e92221081209938488a40b1c4a4c0e122290247129309038488a41c06020e2292104c48801128083a48884132048260e2212903c7128388a48413091c4a0c262292104c712018088a4841f1c2096020e12904c7240580838884131e884c290911a043ca708d19802ba4f88f9001ba2e84d87c0ba0f80f8007ff76ffaedffdd3ff3a7fd74ff8e9ff993feb27ff73ffae7ff58fffa1ffd43ffee1ff5c3feb07ff40ffa81ff4c3f6907f510]
def g255H12 : Nat → Nat := chunk #[0x3b4800432000000405ca08000005ea33141b8000000c08000e21b58000000000005a4f5e8000000004100cbaa200000033b370c5cdb61cf265e379d168bc52d6e8d06f1b57432951f9dcb432f8bda45ebc117c58f5a98d8005d300000040ac594184806898ec0000003c6cd7fcb0000000000000002c8084800156293e895e8710f1118f5269dfb836a72ad9cdf5d2258000001c47be78fdb37e0c81e88596aaec148006d9b557607dc61f0006e4eca7479868000aacd5c29d2a61c6ea9edb9d7629d6a549b8567d0ea051167228e521276e6c90000007c88003df46700025df95aa800023a3244e12c396341758e00059e0000002022a00000000003c174cae8ded64980000000000000066980048743b9c77b06375c1b2c3c29a96dba2319c8ecace7bf78a61a699ce474d45b51ae996c6680fef4b09c5487fcc53d783cb93690efc4ec9b506604215718ca7a3518b1c492c93eaaf6da3e6cb6ca5350bd200000078100071400020280064af088002137ab7b1fcfd2b9f00baf33fa1a543c0438e6bb53942212ee3b28e2d7b9b1fa23a5e50c5210001e18004660003eb13f800211ca67c358cf3c80042e1d870d4f159e82410000401834010000004000a80800010000c0001000040c01000040005058040e02070180000028040001000000000008180e080005002010b000180e018000000018000a030200006050280002010481400080000800010000400000705c080201804240101004080003000000b000040200020001e13040000203000000a05]
def g255D13 : Nat → Nat := chunk #[0x32610424180ff]
def g255H13 : Nat → Nat := chunk #[0x5839c9be95a5211e00c52959c00003c6a6005100001b2b02b000e6005ae82444184211880200000]
def g255L : Nat → Packing
  | 7 => (7,6,7,7,g255D7)
  | 8 => (106,5,7,13,g255D8)
  | 9 => (746,4,7,16,g255D9)
  | 10 => (1005,3,7,17,g255D10)
  | 11 => (228,2,7,15,g255D11)
  | 12 => (21,1,7,11,g255D12)
  | 13 => (1,0,7,6,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8,h => lookupWord 5 13 4 7 3 0 g255H8 h
  | 9,h => lookupWord 55 151 8 11 7 0 g255H9 h
  | 10,h => lookupWord 374 935 10 14 10 0 g255H10 h
  | 11,h => lookupWord 503 1259 11 14 10 0 g255H11 h
  | 12,h => lookupWord 115 289 9 12 8 0 g255H12 h
  | 13,h => lookupWord 11 29 5 9 5 0 g255H13 h
  | _,_ => none
def g255 : Forest := ⟨255,13,fun i => (g255Y[i]?).getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P8_5 : block g255 8 5 51 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P8_56 : block g255 8 56 50 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 106 = true := (@block_merge g255 8 0 5 101 g255P8_0 (@block_merge g255 8 5 51 50 g255P8_5 g255P8_56))
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 4 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g255P9_4 : block g255 9 4 256 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P9_260 : block g255 9 260 48 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P9_308 : block g255 9 308 256 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P9_564 : block g255 9 564 105 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P9_669 : block g255 9 669 77 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 746 = true := (@block_merge g255 9 0 308 438 (@block_merge g255 9 0 4 304 g255P9_0 (@block_merge g255 9 4 256 48 g255P9_4 g255P9_260)) (@block_merge g255 9 308 256 182 g255P9_308 (@block_merge g255 9 564 105 77 g255P9_564 g255P9_669)))
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 13 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_13 : block g255 10 13 58 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_71 : block g255 10 71 256 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_327 : block g255 10 327 256 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_583 : block g255 10 583 184 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_767 : block g255 10 767 224 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P10_991 : block g255 10 991 14 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 1005 = true := (@block_merge g255 10 0 327 678 (@block_merge g255 10 0 13 314 g255P10_0 (@block_merge g255 10 13 58 256 g255P10_13 g255P10_71)) (@block_merge g255 10 327 440 238 (@block_merge g255 10 327 256 184 g255P10_327 g255P10_583) (@block_merge g255 10 767 224 14 g255P10_767 g255P10_991)))
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P11_6 : block g255 11 6 130 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P11_136 : block g255 11 136 92 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 228 = true := (@block_merge g255 11 0 6 222 g255P11_0 (@block_merge g255 11 6 130 92 g255P11_6 g255P11_136))
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
theorem g255P12_2 : block g255 12 2 19 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 21 = true := (@block_merge g255 12 0 2 19 g255P12_0 g255P12_2)
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]; repeat' apply And.intro
  all_goals decide +kernel
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact g255P7_0
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255P13_0
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 inputs.toFinset := by
  rw [show graph = graphGoal 255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def smallCircuit : Circuit := ⟨[
  ⟨.or,[5,6]⟩, ⟨.or,[0,3]⟩, ⟨.or,[5,9]⟩, ⟨.or,[2,10]⟩, ⟨.and,[7,11]⟩,
  ⟨.or,[0,1]⟩, ⟨.or,[3,13]⟩, ⟨.and,[8,14]⟩, ⟨.or,[2,6]⟩, ⟨.or,[13,16]⟩,
  ⟨.and,[4,17]⟩, ⟨.and,[0,3]⟩, ⟨.or,[12,15]⟩, ⟨.or,[18,19]⟩, ⟨.or,[20,21]⟩
], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 12000 in
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

def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD i.val zero)
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = inputs.map (bit r) := by
  rw [←input_list,List.map_ofFn]; rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]; rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (([8, 16, 16, 1, 1, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 (([9, 18, 20, 9, 17, 33, 65, 129] : List Nat).getD i.val 0)

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (inputs.getD j.val zero) =
      bit (highRow i) (inputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates inputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 8, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 13 inputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
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

end PEqualNP.Outside.L_meta_52234

theorem PEqualNP.Outside.L_meta_52234 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_52234.replaceShort PEqualNP.Outside.L_meta_52234.g255R gates o fit correct
