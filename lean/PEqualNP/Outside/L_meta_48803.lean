import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_48803
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 128
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



def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx



def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3


def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[Nat.div i 4]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            cases hg : t.perms[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def v0 : Nat := 0x33333333333333333333333333333333
def v1 : Nat := 0x55555555555555555555555555555555
def v2 : Nat := 0xcccccccccccccccccccccccccccccccc
def v3 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def v4 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def v5 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def v6 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def v7 : Nat := 0x88888888888888888888888888888888
def v8 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def v9 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def v10 : Nat := 0x30303030303030303030303030303030
def v11 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def v12 : Nat := 0x80808080808080808080808080808080
def v13 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
def v14 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def v15 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def v16 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def v17 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def v18 : Nat := 0x11111111111111111111111111111111
def v19 : Nat := 0x22222222222222222222222222222222
def v20 : Nat := 0x44444444444444444444444444444444
def v21 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def v22 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def v23 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def v24 : Nat := 0xffccffccffccffccffccffccffccffcc
def v25 : Nat := 0xfefefefefefefefefefefefefefefefe
def v26 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def v27 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def v28 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def v29 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def v30 : Nat := 0x3030303030303030303030303030303
def v31 : Nat := 0x50505050505050505050505050505050
def v32 : Nat := 0x330033003300330033003300330033
def v33 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def v34 : Nat := 0x55005500550055005500550055005500
def v35 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def v36 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def v37 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def v38 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def v39 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def v40 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def v41 : Nat := 0xffff0000ffff0000ffff0000ffff
def v42 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def v43 : Nat := 0xe880e880e880e880e880e880e880e880
def v44 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def v45 : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def v46 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def v47 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def v48 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def v49 : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def v50 : Nat := 0xfee8eaa8fee8eaa8fee8eaa8fee8eaa8
def v51 : Nat := 0xe8808880e8808880e8808880e8808880
def v52 : Nat := 0xe888e888e888e888e888e888e888e888
def v53 : Nat := 0x550055005500550055005500550055
def v54 : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def v55 : Nat := 0xf000f000f000f000f000f000f000f000
def v56 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def v57 : Nat := 0xff000000ff000000ff000000ff000000
def v58 : Nat := 0x8080808080808080808080808080808
def v59 : Nat := 0x55550000555500005555000055550000
def v60 : Nat := 0xf000f000f000f000f000f000f000f
def v61 : Nat := 0xf0f00000f0f00000f0f00000f0f
def v62 : Nat := 0x880088008800880088008800880088
def v63 : Nat := 0x8888000088880000888800008888
def v64 : Nat := 0x50005000500050005000500050005000
def v65 : Nat := 0x20202020202020202020202020202020
def v66 : Nat := 0x30003000300030003000300030003000
def v67 : Nat := 0x33003300330033003300330033003300
def v68 : Nat := 0x33330000333300003333000033330000
def v69 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def v70 : Nat := 0x44440000444400004444000044440000
def v71 : Nat := 0xa0a00000a0a00000a0a00000a0a
def v72 : Nat := 0xaa000000aa000000aa000000aa
def v73 : Nat := 0xa000a000a000a000a000a000a000a000
def v74 : Nat := 0x40404040404040404040404040404040
def v75 : Nat := 0xf0000000f0000000f0000000f0000
def v76 : Nat := 0x44004400440044004400440044004400
def v77 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def v78 : Nat := 0x22220000222200002222000022220000
def v79 : Nat := 0x55000000550000005500000055000000
def v80 : Nat := 0x22002200220022002200220022002200
def v81 : Nat := 0x50500000505000005050000050500000
def v82 : Nat := 0xf0000000f0000000f0000000f0
def v83 : Nat := 0xcc000000cc000000cc000000cc
def v84 : Nat := 0xc000c000c000c000c000c000c000c
def v85 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def v86 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def v87 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def v88 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def v89 : Nat := 0x70707070707070707070707070707070
def v90 : Nat := 0x2222aaaa2222aaaa2222aaaa2222aaaa
def v91 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def v92 : Nat := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
def v93 : Nat := 0xf0000000f0000000f0000000f0000000
def v94 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def v95 : Nat := 0xa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaa
def v96 : Nat := 0xffff00f0ffff00f0ffff00f0ffff00f0
def v97 : Nat := 0xf000f0f0f000f0f0f000f0f0f000f0f0
def v98 : Nat := 0xffff8080ffff8080ffff8080ffff8080
def v99 : Nat := 0x7070f0f07070f0f07070f0f07070f0f0
def v100 : Nat := 0x88880000888800008888000088880000
def v101 : Nat := 0x80008000800080008000800080008000
def v102 : Nat := 0xf080f080f080f080f080f080f080f080
def v103 : Nat := 0xf8f80000f8f80000f8f80000f8f8
def v104 : Nat := 0x77770000777700007777000077770000
def v105 : Nat := 0x70007000700070007000700070007000
def v106 : Nat := 0x8080f0f08080f0f08080f0f08080f0f0
def v107 : Nat := 0x88808880888088808880888088808880
def v108 : Nat := 0x77707770777077707770777077707770
def v109 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def v110 : Nat := 0x80808888808088888080888880808888
def v111 : Nat := 0x2020a0a02020a0a02020a0a02020a0a0
def v112 : Nat := 0xb030b030b030b030b030b030b030b030
def v113 : Nat := 0x22aaaaaa22aaaaaa22aaaaaa22aaaaaa
def v114 : Nat := 0xa0000000a0000000a0000000a0000000
def v115 : Nat := 0x30f0f0f030f0f0f030f0f0f030f0f0f0
def v116 : Nat := 0x8080aaaa8080aaaa8080aaaa8080aaaa
def v117 : Nat := 0x3000f0003000f0003000f0003000f000
def v118 : Nat := 0xa000f0f0a000f0f0a000f0f0a000f0f0
def v119 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def v120 : Nat := 0xc0c0ccccc0c0ccccc0c0ccccc0c0cccc
def v121 : Nat := 0xf000ff00f000ff00f000ff00f000ff00
def v122 : Nat := 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa
def v123 : Nat := 0x222222aa222222aa222222aa222222aa
def v124 : Nat := 0x2222a2a22222a2a22222a2a22222a2a2
def v125 : Nat := 0x77778888777788887777888877778888
def v126 : Nat := 0xf800f800f800f800f800f800f800f800
def v127 : Nat := 0x70f0f0f070f0f0f070f0f0f070f0f0f0
def v128 : Nat := 0xff88ff00ff88ff00ff88ff00ff88ff00
def v129 : Nat := 0x7700ff007700ff007700ff007700ff00
def v130 : Nat := 0x8888f0f08888f0f08888f0f08888f0f0
def v131 : Nat := 0x7000f0f07000f0f07000f0f07000f0f0
def v132 : Nat := 0x707070f0707070f0707070f0707070f0
def v133 : Nat := 0xf0f000f0f0f000f0f0f000f0f0f000f0
def v134 : Nat := 0x2aaaaaaa2aaaaaaa2aaaaaaa2aaaaaaa
def v135 : Nat := 0xaa000000aa000000aa000000aa00
def v136 : Nat := 0x3333000033330000333300003333
def v137 : Nat := 0xaa000000aa000000aa000000aa0000
def v138 : Nat := 0xa000a000a000a000a000a000a000a
def v139 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def v140 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def v141 : Nat := 0x88008800880088008800880088008800
def v142 : Nat := 0x5f005f005f005f005f005f005f005f00
def v143 : Nat := 0xaf00af00af00af00af00af00af00af00
def v144 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def v145 : Nat := 0x5500ff005500ff005500ff005500ff00
def v146 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def v147 : Nat := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
def v148 : Nat := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
def v149 : Nat := 0x4c4ccccc4c4ccccc4c4ccccc4c4ccccc
def v150 : Nat := 0x5f00ff005f00ff005f00ff005f00ff00
def v151 : Nat := 0x4400ff004400ff004400ff004400ff00
def v152 : Nat := 0x4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c
def v153 : Nat := 0xc888c888c888c888c888c888c888c888
def v154 : Nat := 0xee00aa00ee00aa00ee00aa00ee00aa00
def v155 : Nat := 0xe8888880e8888880e8888880e8888880
def v156 : Nat := 0xe8a8a800e8a8a800e8a8a800e8a8a800
def v157 : Nat := 0xfefefc80fefefc80fefefc80fefefc80
def v158 : Nat := 0xfeeafc80feeafc80feeafc80feeafc80
def v159 : Nat := 0xf000f000f000f000f000f000f000f0
def v160 : Nat := 0xfeeaee80feeaee80feeaee80feeaee80
def v161 : Nat := 0x5050f0f05050f0f05050f0f05050f0f0
def v162 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00
def v163 : Nat := 0x30f030f030f030f030f030f030f030f0
def v164 : Nat := 0x55445544554455445544554455445544
def v165 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0
def v166 : Nat := 0x307030f0307030f0307030f0307030f0
def v167 : Nat := 0xf0e0f0c0f0e0f0c0f0e0f0c0f0e0f0c0
def v168 : Nat := 0xfaeaf0c0faeaf0c0faeaf0c0faeaf0c0
def v169 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0
def v170 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa
def v171 : Nat := 0xfcf0eca0fcf0eca0fcf0eca0fcf0eca0
def v172 : Nat := 0xf3f0a2a0f3f0a2a0f3f0a2a0f3f0a2a
def v173 : Nat := 0xf0c5f4c0f0c5f4c0f0c5f4c0f0c5f4c
def v174 : Nat := 0xccc0cc80ccc0cc80ccc0cc80ccc0cc80
def v175 : Nat := 0x33303320333033203330332033303320
def v176 : Nat := 0x1050f0f01050f0f01050f0f01050f0f0
def v177 : Nat := 0xf0f0e0a0f0f0e0a0f0f0e0a0f0f0e0a0
def v178 : Nat := 0xfaea0000faea0000faea0000faea0000
def v179 : Nat := 0xfaea0000faea0000faea0000faea
def v180 : Nat := 0xff44ff44ff44ff44ff44ff44ff44ff44
def v181 : Nat := 0x44ff444444ff444444ff444444ff4444
def v182 : Nat := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa
def v183 : Nat := 0xffccff00ffccff00ffccff00ffccff00
def v184 : Nat := 0xffeeffaaffeeffaaffeeffaaffeeffaa
def v185 : Nat := 0x3322ffaa3322ffaa3322ffaa3322ffaa
def v186 : Nat := 0xaaffaaaaaaffaaaaaaffaaaaaaffaaaa
def v187 : Nat := 0xcc88cc00cc88cc00cc88cc00cc88cc00
def v188 : Nat := 0xffeeffccffeeffccffeeffccffeeffcc
def v189 : Nat := 0x4400cc004400cc004400cc004400cc
def v190 : Nat := 0x33223300332233003322330033223300
def v191 : Nat := 0xeeaacc00eeaacc00eeaacc00eeaacc00
def v192 : Nat := 0x5544ffcc5544ffcc5544ffcc5544ffcc
def v193 : Nat := 0xbbaa3300bbaa3300bbaa3300bbaa3300
def v194 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def v195 : Nat := 0x33ff22aa33ff22aa33ff22aa33ff22aa
def v196 : Nat := 0xffccaa88ffccaa88ffccaa88ffccaa88
def v197 : Nat := 0xccff88aaccff88aaccff88aaccff88aa
def v198 : Nat := 0xfcfcececfcfcececfcfcececfcfcecec
def v199 : Nat := 0xc0c4c4c0c0c4c4c0c0c4c4c0c0c4c4c
def v200 : Nat := 0xfff0ffa0fff0ffa0fff0ffa0fff0ffa0
def v201 : Nat := 0xf005f000f005f000f005f000f005f00
def v202 : Nat := 0xff000000ff000000ff000000ff0000
def v203 : Nat := 0xcc00eeaacc00eeaacc00eeaacc00eeaa
def v204 : Nat := 0xffcc5544ffcc5544ffcc5544ffcc5544
def v205 : Nat := 0x3300bbaa3300bbaa3300bbaa3300bbaa
def v206 : Nat := 0xeeaa0000eeaa0000eeaa0000eeaa0000
def v207 : Nat := 0xffffeeaaffffeeaaffffeeaaffffeeaa
def v208 : Nat := 0xeeaa0000eeaa0000eeaa0000eeaa
def v209 : Nat := 0x11550000115500001155000011550000
def v210 : Nat := 0xfaeafaeafaeafaeafaeafaeafaeafaea
def v211 : Nat := 0xa2a0a2a0a2a0a2a0a2a0a2a0a2a0a2a
def v212 : Nat := 0xfffff0c0fffff0c0fffff0c0fffff0c0
def v213 : Nat := 0xf3f00000f3f00000f3f00000f3f0000
def v214 : Nat := 0xee00aa00ee00aa00ee00aa00ee00aa
def v215 : Nat := 0x55445500554455005544550055445500
def v216 : Nat := 0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0
def v217 : Nat := 0xeecceecceecceecceecceecceecceecc
def v218 : Nat := 0x50f050f050f050f050f050f050f050f0
def v219 : Nat := 0xffffaa00ffffaa00ffffaa00ffffaa00
def v220 : Nat := 0x55ff000055ff000055ff000055ff0000
def v221 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def v222 : Nat := 0x440044004400440044004400440044
def v223 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000
def v224 : Nat := 0x550000005500000055000000550000
def v225 : Nat := 0xeeeecccceeeecccceeeecccceeeecccc
def v226 : Nat := 0xff00ffaaff00ffaaff00ffaaff00ffaa
def v227 : Nat := 0x22aa22aa22aa22aa22aa22aa22aa22aa
def v228 : Nat := 0xffffcc00ffffcc00ffffcc00ffffcc00
def v229 : Nat := 0x33ff000033ff000033ff000033ff0000
def v230 : Nat := 0xbbaabbaabbaabbaabbaabbaabbaabbaa
def v231 : Nat := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0
def v232 : Nat := 0xff00ffccff00ffccff00ffccff00ffcc
def v233 : Nat := 0xbbbbaaaabbbbaaaabbbbaaaabbbbaaaa
def v234 : Nat := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def v235 : Nat := 0xffffccccffffccccffffccccffffcccc
def v236 : Nat := 0xcccc0000cccc0000cccc0000cccc
def v237 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def v238 : Nat := 0xff000000ff000000ff000000ff00
def v239 : Nat := 0xfee8eee0fee8eee0fee8eee0fee8eee0
def v240 : Nat := 0xfee8eaa8eee08000fee8eaa8eee08000
def v241 : Nat := 0xffffffff00000000ffffffff00000000
def v242 : Nat := 0xffffffff00000000ffffffff
def v243 : Nat := 0xffff000000000000ffff000000000000
def v244 : Nat := 0x55555555000000005555555500000000
def v245 : Nat := 0xffff000000000000ffff00000000
def v246 : Nat := 0xff00ff0000000000ff00ff00
def v247 : Nat := 0xff00ff0000000000ff00ff00000000
def v248 : Nat := 0xff00ff0000000000ff00ff0000000000
def v249 : Nat := 0xf0f0f0f000000000f0f0f0f0
def v250 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def v251 : Nat := 0xf0f0f0f000000000f0f0f0f000000000
def v252 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def v253 : Nat := 0xcccccccc00000000cccccccc
def v254 : Nat := 0x33333333000000003333333300000000
def v255 : Nat := 0xcccccccc00000000cccccccc00000000
def v256 : Nat := 0xaaaaaaaa00000000aaaaaaaa
def v257 : Nat := 0xf000f000f000f000f000f000f000f00
def v258 : Nat := 0xcc000000cc000000cc000000cc00
def v259 : Nat := 0xc0c00000c0c00000c0c00000c0c0
def v260 : Nat := 0x55005500000000005500550000000000
def v261 : Nat := 0x50505050000000005050505000000000
def v262 : Nat := 0x888888880000000088888888
def v263 : Nat := 0xf000f00ff00ff000f000f00ff00ff00
def v264 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def v265 : Nat := 0xf000f0f0f0f0f000f000f0f0f0f0f0
def v266 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def v267 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00
def v268 : Nat := 0xffc0eac0ffc0eac0ffc0eac0ffc0eac0
def v269 : Nat := 0xff30ba30ff30ba30ff30ba30ff30ba30
def v270 : Nat := 0xf3f0b3a0f3f0b3a0f3f0b3a0f3f0b3a0
def v271 : Nat := 0xf050f000f050f000f050f000f050f0
def v272 : Nat := 0xffcceeccffcceeccffcceeccffcceecc
def v273 : Nat := 0xcc44cc00cc44cc00cc44cc00cc44cc
def v274 : Nat := 0xaa00ff00aa00aa00aa00ff00aa00aa00
def v275 : Nat := 0xa0a0f0f0a0a0a0a0a0a0f0f0a0a0a0a0
def v276 : Nat := 0x8f008f008f008f008f008f008f008f00
def v277 : Nat := 0x80f080f080f080f080f080f080f080f0
def v278 : Nat := 0xff000f00ff000f00ff000f00ff000f00
def v279 : Nat := 0x8888ff888888ff888888ff888888ff88
def v280 : Nat := 0xe000e000e000e000e000e000e000e000
def v281 : Nat := 0x1f001f001f001f001f001f001f001f00
def v282 : Nat := 0x10f010f010f010f010f010f010f010f0
def v283 : Nat := 0xeeee0e0eeeee0e0eeeee0e0eeeee0e0e
def v284 : Nat := 0xe0e0e0eeeeeeeee0e0e0e0eeeeeeeee
def v285 : Nat := 0xeeee00eeeeee00eeeeee00eeeeee00ee
def v286 : Nat := 0xee00eeeeeeeeee00ee00eeeeeeeeee
def v287 : Nat := 0xf0f00000f0f0f0f0f0f00000f0f0f0f0
def v288 : Nat := 0xff000000ff00ff00ff000000ff00ff00
def v289 : Nat := 0xd000d000d000d000d000d000d000d000
def v290 : Nat := 0x2f002f002f002f002f002f002f002f00
def v291 : Nat := 0x20f020f020f020f020f020f020f020f0
def v292 : Nat := 0x2222f2f22222f2f22222f2f22222f2f2
def v293 : Nat := 0x2222ff222222ff222222ff222222ff22
def v294 : Nat := 0xb000b000b000b000b000b000b000b000
def v295 : Nat := 0x4f004f004f004f004f004f004f004f00
def v296 : Nat := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
def v297 : Nat := 0x40f040f040f040f040f040f040f040f0
def v298 : Nat := 0xbb00bb00bb00bb00bb00bb00bb00bb00
def v299 : Nat := 0x4444f4f44444f4f44444f4f44444f4f4
def v300 : Nat := 0xf4f4f4f444444444f4f4f4f444444444
def v301 : Nat := 0x4444ff444444ff444444ff444444ff44
def v302 : Nat := 0xff44ff4444444444ff44ff4444444444
def v303 : Nat := 0xeca0eca0eca0eca0eca0eca0eca0eca0
def v304 : Nat := 0xb3a0b3a0b3a0b3a0b3a0b3a0b3a0b3a0
def v305 : Nat := 0x5f5f4c4c5f5f4c4c5f5f4c4c5f5f4c4c
def v306 : Nat := 0xff00cc00ff00cc00ff00cc00ff00cc00
def v307 : Nat := 0xa0a0ececa0a0ececa0a0ececa0a0ecec
def v308 : Nat := 0xff003300ff003300ff003300ff003300
def v309 : Nat := 0xa0a0ffa0a0a0ffa0a0a0ffa0a0a0ffa0
def v310 : Nat := 0xefccefccefccefccefccefccefccefcc
def v311 : Nat := 0x40cc40cc40cc40cc40cc40cc40cc40cc
def v312 : Nat := 0xdc50dc50dc50dc50dc50dc50dc50dc50
def v313 : Nat := 0x73507350735073507350735073507350
def v314 : Nat := 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0
def v315 : Nat := 0xafaf8c8cafaf8c8cafaf8c8cafaf8c8c
def v316 : Nat := 0x5050dcdc5050dcdc5050dcdc5050dcdc
def v317 : Nat := 0xdcdcdcdc50505050dcdcdcdc50505050
def v318 : Nat := 0x30303030f0f0f0f030303030f0f0f0f0
def v319 : Nat := 0x33003300ff00ff0033003300ff00ff00
def v320 : Nat := 0x73737373505050507373737350505050
def v321 : Nat := 0xcc00cc00ff00ff00cc00cc00ff00ff00
def v322 : Nat := 0x5050ff505050ff505050ff505050ff50
def v323 : Nat := 0xff50ff5050505050ff50ff5050505050
def v324 : Nat := 0xba30ba30ba30ba30ba30ba30ba30ba30
def v325 : Nat := 0x55ff44cc55ff44cc55ff44cc55ff44cc
def v326 : Nat := 0xaa00eeccaa00eeccaa00eeccaa00eecc
def v327 : Nat := 0xf0f03030f0f03030f0f03030f0f03030
def v328 : Nat := 0xaa00faf0aa00faf0aa00faf0aa00faf0
def v329 : Nat := 0xa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0
def v330 : Nat := 0xecfcecfcecfcecfcecfcecfcecfcecfc
def v331 : Nat := 0xd5c0d5c0d5c0d5c0d5c0d5c0d5c0d5c0
def v332 : Nat := 0x75307530753075307530753075307530
def v333 : Nat := 0xcf00cf00cf00cf00cf00cf00cf00cf00
def v334 : Nat := 0xaaff88ccaaff88ccaaff88ccaaff88cc
def v335 : Nat := 0x5500ddcc5500ddcc5500ddcc5500ddcc
def v336 : Nat := 0xddccddcc55005500ddccddcc55005500
def v337 : Nat := 0x77337733550055007733773355005500
def v338 : Nat := 0xc0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0
def v339 : Nat := 0x5500f5f05500f5f05500f5f05500f5f0
def v340 : Nat := 0xf5f0f5f055005500f5f0f5f055005500
def v341 : Nat := 0x3f3f2a2a3f3f2a2a3f3f2a2a3f3f2a2a
def v342 : Nat := 0xcfcf8a8acfcf8a8acfcf8a8acfcf8a8a
def v343 : Nat := 0xf000a000f000a000f000a000f000a000
def v344 : Nat := 0xf0f05050f0f05050f0f05050f0f05050
def v345 : Nat := 0xf00af000f00af000f00af000f00af00
def v346 : Nat := 0xff005500ff005500ff005500ff005500
def v347 : Nat := 0xf0a0f000f0a0f000f0a0f000f0a0f0
def v348 : Nat := 0x50005000f000f00050005000f000f000
def v349 : Nat := 0xaf00af000f000f00af00af000f000f00
def v350 : Nat := 0x50505050f0f0f0f050505050f0f0f0f0
def v351 : Nat := 0xa0f0a0f000f000f0a0f0a0f000f000f0
def v352 : Nat := 0x55005500ff00ff0055005500ff00ff00
def v353 : Nat := 0xffffaaaaffff0000ffffaaaaffff0000
def v354 : Nat := 0xeaeaeaeac0c0c0c0eaeaeaeac0c0c0c0
def v355 : Nat := 0x3f003f003f003f003f003f003f003f00
def v356 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000
def v357 : Nat := 0xbabababa30303030babababa30303030
def v358 : Nat := 0xeeaaeeaacc00cc00eeaaeeaacc00cc00
def v359 : Nat := 0xbbaabbaa33003300bbaabbaa33003300
def v360 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea00
def v361 : Nat := 0xaaaaffaaaaaaffaaaaaaffaaaaaaffaa
def v362 : Nat := 0xc0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0
def v363 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa
def v364 : Nat := 0xffc0ffc0c0c0c0c0ffc0ffc0c0c0c0c0
def v365 : Nat := 0xaaaaffffaaaaaaaaaaaaffffaaaaaaaa
def v366 : Nat := 0xba00ba00ba00ba00ba00ba00ba00ba00
def v367 : Nat := 0x3030ff303030ff303030ff303030ff30
def v368 : Nat := 0xff30ff3030303030ff30ff3030303030
def v369 : Nat := 0xe0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0
def v370 : Nat := 0xaaaafafaaaaafafaaaaafafaaaaafafa
def v371 : Nat := 0xcc00fcf0cc00fcf0cc00fcf0cc00fcf0
def v372 : Nat := 0xfafafafaaaaaaaaafafafafaaaaaaaaa
def v373 : Nat := 0xfcf0fcf0cc00cc00fcf0fcf0cc00cc00
def v374 : Nat := 0xb0a0b0a0b0a0b0a0b0a0b0a0b0a0b0a0
def v375 : Nat := 0x3300f3f03300f3f03300f3f03300f3f0
def v376 : Nat := 0xf3f0f3f033003300f3f0f3f033003300
def v377 : Nat := 0xa0a0b0b0a0a0b0b0a0a0b0b0a0a0b0b0
def v378 : Nat := 0xaa00bb00aa00bb00aa00bb00aa00bb00
def v379 : Nat := 0x55554444555544445555444455554444
def v380 : Nat := 0xf000c000f000c000f000c000f000c000
def v381 : Nat := 0xf003f000f003f000f003f000f003f00
def v382 : Nat := 0xf030f000f030f000f030f000f030f0
def v383 : Nat := 0xa0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0
def v384 : Nat := 0xaa00ee00aa00ee00aa00ee00aa00ee00
def v385 : Nat := 0xaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee
def v386 : Nat := 0xf0003000f0003000f0003000f0003000
def v387 : Nat := 0xf00cf000f00cf000f00cf000f00cf00
def v388 : Nat := 0xf0c0f000f0c0f000f0c0f000f0c0f0
def v389 : Nat := 0xe0e0e0e0a0a0a0a0e0e0e0e0a0a0a0a0
def v390 : Nat := 0xee00ee00aa00aa00ee00ee00aa00aa00
def v391 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa
def v392 : Nat := 0x30003000f000f00030003000f000f000
def v393 : Nat := 0xcf00cf000f000f00cf00cf000f000f00
def v394 : Nat := 0xc0f0c0f000f000f0c0f0c0f000f000f0
def v395 : Nat := 0xb0b0b0b0a0a0a0a0b0b0b0b0a0a0a0a0
def v396 : Nat := 0xbb00bb00aa00aa00bb00bb00aa00aa00
def v397 : Nat := 0xbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa
def v398 : Nat := 0xc000c000f000f000c000c000f000f000
def v399 : Nat := 0x3f003f000f000f003f003f000f000f00
def v400 : Nat := 0x30f030f000f000f030f030f000f000f0
def v401 : Nat := 0xaa00fa00aa00fa00aa00fa00aa00fa00
def v402 : Nat := 0xffaaafaaffaaafaaffaaafaaffaaafaa
def v403 : Nat := 0xaaa0aa00aaa0aa00aaa0aa00aaa0aa
def v404 : Nat := 0xfa00fa00aa00aa00fa00fa00aa00aa00
def v405 : Nat := 0xa0a0f0a0a0a0f0a0a0a0f0a0a0a0f0a0
def v406 : Nat := 0xfafaaafafafaaafafafaaafafafaaafa
def v407 : Nat := 0xa0aaa0a0a0aaa0a0a0aaa0a0a0aaa0a
def v408 : Nat := 0xf0a0f0a0a0a0a0a0f0a0f0a0a0a0a0a0
def v409 : Nat := 0xf00ff000f000f000f00ff000f000f00
def v410 : Nat := 0xf0f0f000f000f000f0f0f000f000f0
def v411 : Nat := 0x77007700770077007700770077007700
def v412 : Nat := 0xdd00dd00dd00dd00dd00dd00dd00dd00
def v413 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def v414 : Nat := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
def v415 : Nat := 0xafafafaf00000000afafafaf00000000
def v416 : Nat := 0xddccddccddccddccddccddccddccddcc
def v417 : Nat := 0x88cc88cc88cc88cc88cc88cc88cc88cc
def v418 : Nat := 0xaaffaaff00000000aaffaaff00000000
def v419 : Nat := 0xbabababababababababababababababa
namespace Lib12108
def pw0 : Nat := v0
def pw1 : Nat := v1
def pw2 : Nat := v2
def pw3 : Nat := v3
def pw4 : Nat := v4
def pw5 : Nat := v5
def pw6 : Nat := v6
def pw7 : Nat := v7
def pw8 : Nat := v8
def pw9 : Nat := v9
def pw10 : Nat := v10
def pw11 : Nat := v11
def pw12 : Nat := v12
def pw13 : Nat := v13
def pw14 : Nat := v14
def pw15 : Nat := v15
def pw16 : Nat := v16
def pw17 : Nat := v17
def pw18 : Nat := v18
def pw19 : Nat := v19
def pw20 : Nat := v20
def pw21 : Nat := v21
def pw22 : Nat := v22
def pw23 : Nat := v23
def pw24 : Nat := v24
def pw25 : Nat := v25
def pw26 : Nat := v26
def pw27 : Nat := v27
def pw28 : Nat := v28
def pw29 : Nat := v29
def pw30 : Nat := v30
def pw31 : Nat := v31
def pw32 : Nat := v32
def pw33 : Nat := v33
def pw34 : Nat := v34
def pw35 : Nat := v35
def pw36 : Nat := v36
def pw37 : Nat := v37
def pw38 : Nat := v38
def pw39 : Nat := v39
def pw40 : Nat := v40
def pw41 : Nat := v41
def p1_T : Nat := v7
def p1_R : List Nat := [0, 1]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN true p1_R p1_T 1 := lowCount p1_B (by decide +kernel)
def p2_T : Nat := v22
def p2_R : List Nat := [0, 1]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN true p2_R p2_T 1 := lowCount p2_B (by decide +kernel)
def p3_T : Nat := v42
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw0,1,[0, 2]),(pw1,1,[1, 2]),(pw2,1,[0, 2]),(pw3,1,[1, 2]),(pw4,1,[0, 1]),(pw5,1,[0, 1])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p3_B p2_B p2_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
([pw3,pw2,pw5],[0,4,8,12,1,5,16,20,9,13,17,21],[319,602,3237])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN true p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK true p3_T p3_t 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := levelStep p3_B p3_W p3_I2 (chunks 32 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
theorem p3_L : LowN true p3_R p3_T 4 := lowSearch p3_B p3_I3 (by decide +kernel)
def p4_T : Nat := v12
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN true p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := v43
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw3,4,[1, 2, 3]),(pw2,4,[0, 2, 3]),(pw5,4,[0, 1, 3]),(pw6,4,[0, 1, 2]),(pw1,2,[1, 2, 3]),(pw7,1,[2, 3]),(pw0,2,[0, 2, 3]),(pw4,2,[0, 1, 3]),(pw8,1,[1, 3]),(pw9,1,[1, 2]),(pw10,1,[0, 3]),(pw11,1,[0, 3])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p5_B p1_B p1_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[128]),(3,[128]),(2,[130]),(0,[130]),(0,[131]),(0,[128]),(1,[128]),(6,[]),(7,[]),(2,[256]),(8,[]),(0,[260]),(2,[258]),(9,[]),(3,[258]),(3,[256]),(10,[]),(11,[]),(2,[128,270]),(2,[258,143]),(3,[130,268]),(3,[130,271]),(2,[130,268]),(2,[130,271]),(3,[260,15]),(2,[260,15]),(1,[260,15]),(6,[128]),(3,[256,260]),(4,[128]),(3,[128,260]),(3,[128,256])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(13,12),(14,12),(7,5),(11,10),(14,10),(7,6),(14,6),(11,9),(13,9),(13,5),(7,3),(11,3),(11,2),(13,4),(11,0),(13,0),(14,0)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[2],[1,0,2,1,0],[0],[0,2],[2,1,0]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([pw3,pw2,pw5,pw6],[0,4,8,12,1,5,9,17,13,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131477,263705,530470,1056874,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw7,pw3,pw2,pw5,pw6],[0,4,33,37,16,20,24,28,41,45,3,27,8,12,17,25,23,31,35,39],[3,1,70964,141880,3,17473,34945,262214,524426,780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw12,pw3,pw2,pw5,pw6],[16,44,24,48,12,32,36,40,52,56,43],[32,64,128,1041,3,3,3,14,264,516]),
([pw13,pw3,pw2,pw5,pw6],[16,64,60,68,72,4,76,80],[4,35,13,7,3,9,3,18,192,18]),
([pw7,pw14,pw2,pw5,pw6],[24,48,0,16,28,32,52,56,84,88,92,49,53,3],[33,4,131,2312,67,4,4120,8195,514,1025])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D3 : List StD := [
([pw15,pw2,pw5,pw6],[120,124,128,0,96,100,104,108,112,116],[56,208,776,7,7,7]),
([pw7,pw14,pw16,pw6],[44,8,132,32,40,136,140,144,148,57,61,65],[11,3,548,17,1216,2308])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN true p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK true p5_T p5_t 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := levelStep p5_B p5_W p5_I2 (chunks 32 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK true p5_T p5_t 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := levelStep p5_B p5_W p5_I3 (chunks 32 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK true p5_T p5_t 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I5 : LevelN true p5_T 5 p5_D5 := levelStep p5_B p5_W p5_I4 (chunks 32 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK true p5_T p5_t 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I6 : LevelN true p5_T 6 p5_D6 := levelStep p5_B p5_W p5_I5 (chunks 32 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN true p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)
def p6_T : Nat := v25
def p6_R : List Nat := [0, 1, 2]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN true p6_R p6_T 2 := lowCount p6_B (by decide +kernel)
def p7_T : Nat := v44
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw1,4,[1, 2, 3]),(pw0,4,[0, 2, 3]),(pw4,4,[0, 1, 3]),(pw17,4,[0, 1, 2]),(pw18,1,[2, 3]),(pw19,1,[2, 3]),(pw20,1,[2, 3]),(pw3,2,[1, 2, 3]),(pw2,2,[0, 2, 3]),(pw5,2,[0, 1, 3]),(pw9,1,[1, 2]),(pw6,2,[0, 1, 2]),(pw21,1,[0, 2])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=4) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[129]),(3,[129]),(4,[]),(0,[257]),(1,[257]),(5,[]),(1,[259]),(6,[]),(0,[259]),(2,[261]),(2,[257]),(0,[129]),(1,[129]),(1,[131]),(7,[]),(0,[131]),(8,[]),(0,[130]),(9,[]),(10,[]),(0,[258]),(11,[]),(12,[]),(0,[257,261]),(8,[261]),(0,[129,261]),(0,[129,257]),(0,[261,385]),(3,[263]),(1,[262,13]),(1,[131,270]),(0,[262,13]),(0,[131,270]),(0,[258,141]),(0,[130,270]),(0,[260]),(0,[129,270]),(1,[129,270])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw3,pw2,pw5,pw6],[0,4,8,12,1,9,5,13,17,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131285,262937,527398,1060906,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw3,pw2,pw22,pw5,pw6],[0,4,16,20,13,24,21,41,45,3,43,8,12,29,37,27,31,35,39],[3,2,32789,65609,1,139270,278538,3764,5992,404])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw3,pw2,pw5,pw23,pw24],[28,32,36,44,40,48,52,56,13,29,47],[1027,5,16,7,10,11,32,580,392,3]),
([pw3,pw2,pw5,pw25,pw6],[16,60,64,72,12,68,76,80,84,88,3],[7,7,32,10,7,64,132,256,513,1048]),
([pw26,pw3,pw2,pw5,pw6],[92,24,100,0,4,8,20,28,96,104],[24,24,35,128,257,3,70,514,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D3 : List StD := [
([pw3,pw27,pw24,pw28],[112,4,12,1,108,116,120,124,128,5,49],[1041,41,584,388,7,3]),
([pw29,pw3,pw2,pw5],[132,160,72,0,80,136,140,144,148,152,156,164],[41,193,1793,6,6,2066])]
def p7_D2 : List StD := []
theorem p7_I2 : LevelN true p7_T 2 p7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x0 : levelOK true p7_T p7_t 2 (p7_D2.map Prod.fst) ((p7_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := levelStep p7_B p7_W p7_I2 (chunks 32 p7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
theorem p7_L : LowN true p7_R p7_T 7 := lowSearch p7_B p7_I6 (by decide +kernel)
def p8_T : Nat := v45
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw6,4,[0, 1, 2])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p8_B p3_B p3_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[],[],[])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK true p8_T p8_t 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := levelStep p8_B p8_W p8_I3 (chunks 32 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN true p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := v46
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw1,4,[1, 2, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[],[],[])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN true p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK true p9_T p9_t 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := levelStep p9_B p9_W p9_I3 (chunks 32 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN true p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)
def p10_T : Nat := v47
def p10_R : List Nat := [0, 1, 2]
def p10_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_L : LowN true p10_R p10_T 2 := lowCount p10_B (by decide +kernel)
def p11_T : Nat := v48
def p11_R : List Nat := [0, 1, 2]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_L : LowN true p11_R p11_T 2 := lowCount p11_B (by decide +kernel)
def p12_T : Nat := v49
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw2,2,[0, 2, 3]),(pw3,2,[1, 2, 3]),(pw1,2,[1, 2, 3]),(pw0,2,[0, 2, 3]),(pw19,1,[2, 3]),(pw20,1,[2, 3]),(pw30,1,[0, 3]),(pw31,1,[1, 3]),(pw8,1,[1, 3]),(pw16,1,[0, 3]),(pw17,2,[0, 1, 2]),(pw9,1,[1, 2]),(pw6,2,[0, 1, 2]),(pw4,2,[0, 1, 3]),(pw32,1,[0, 2]),(pw33,1,[0, 2]),(pw34,1,[1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=1) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p1_B p1_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(14,12),(3,2),(3,1),(14,10),(5,1),(14,6),(9,8),(9,1),(5,6),(9,0),(3,0),(11,1),(7,1)],[],[[],[1,2],[1],[2],[2,1],[1,2,1]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw3,pw2,pw5,pw6],[3,1,5,13,17,21,25,33,7,15,9,11,19,29,23],[1295,3634,12483,829,17101,6640])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([pw7,pw3,pw2,pw5,pw6],[8,12,16,20,0,4,24,28,37,3,7,15,23],[16,32,3073,4609,259,5,5,10,10,192]),
([pw3,pw2,pw22,pw5,pw6],[0,4,16,20,8,12,32,36,37,3,11,15,19],[259,32,10,10,16,5,5,3073,4609,192]),
([pw9,pw3,pw2,pw5,pw6],[44,8,48,4,20,28,40,13,41],[64,3,3,8,3,3,262,176,5,5]),
([pw20,pw3,pw2,pw5,pw6],[20,12,4,0,8,32,44,25,45],[8,16,3,3,262,5,5,3,3,224]),
([pw3,pw16,pw2,pw5,pw6],[36,12,52,20,28,32,56,41,3],[3,3,5,224,16,8,3,262,3,5]),
([pw3,pw2,pw5,pw27,pw6],[24,28,0,12,32,36,60,9,3],[7,33,5,194,262,16,5,8,3,3]),
([pw21,pw3,pw2,pw5,pw6],[12,9,64,16,60,0,24,44,56,49,7,15],[3,128,3073,32,3,14,26,17,517,324])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
([pw3,pw2,pw5,pw35],[60,8,12,16,0,28,32],[7,10,11,5,20,97]),
([pw36,pw3,pw5,pw6],[8,12,0,16,28,32,24],[7,50,38,9,9,80]),
([pw3,pw37,pw5,pw6],[32,36,8,24,16,28],[5,26,33,5,10,3]),
([pw26,pw3,pw2,pw5],[32,16,8,64,0,28],[5,6,33,9,10,19]),
([pw3,pw16,pw27,pw6],[24,28,36,16,53],[7,5,10,16,5,3]),
([pw3,pw2,pw5,pw38],[24,28,36,16,60],[7,5,10,26,5,3]),
([pw3,pw39,pw5,pw6],[24,36,16,28,8,60],[19,3,12,44,3,3])]
def p12_D2 : List StD := []
theorem p12_I2 : LevelN true p12_T 2 p12_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK true p12_T p12_t 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I3 : LevelN true p12_T 3 p12_D3 := levelStep p12_B p12_W p12_I2 (chunks 32 p12_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK true p12_T p12_t 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I4 : LevelN true p12_T 4 p12_D4 := levelStep p12_B p12_W p12_I3 (chunks 32 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK true p12_T p12_t 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I5 : LevelN true p12_T 5 p12_D5 := levelStep p12_B p12_W p12_I4 (chunks 32 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
theorem p12_L : LowN true p12_R p12_T 6 := lowSearch p12_B p12_I5 (by decide +kernel)
def p13_T : Nat := v50
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,6,22)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw1,7,[1, 2, 3, 4]),(pw40,7,[0, 1, 2, 3]),(pw0,5,[0, 2, 3, 4]),(pw4,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw17,5,[0, 1, 2, 4]),(pw41,6,[0, 1, 2, 3]),(pw2,5,[0, 2, 3, 4]),(pw5,5,[0, 1, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p13_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel),mkSlice (w:=2) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=4) p13_B p9_B p9_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[]),(1,[]),(0,[128]),(2,[]),(3,[]),(1,[260]),(0,[130]),(0,[131]),(4,[]),(5,[]),(6,[]),(0,[129]),(7,[]),(1,[261]),(8,[]),(0,[258]),(0,[256]),(0,[257]),(1,[390]),(0,[129,128]),(1,[260,261]),(4,[261]),(5,[261]),(6,[261]),(5,[260]),(4,[260])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(3,2),(5,4),(9,8),(3,1),(5,1),(14,12),(14,10),(9,1),(14,6),(28,12),(22,6),(26,10),(7,6),(26,24),(28,24),(22,20),(22,18),(11,1),(28,20),(3,6),(3,0),(7,1)],[],[[],[2],[1,2],[1,2,1],[1],[2,1]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,4,1,37,5,13,17,21,25,29,33,41,3,7,11,9,45,15,19,23],[21,21,32773,7,29152,145056,2058,804672,65546,2058])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D7 : List StD := [
([pw3,pw16,pw2,pw5,pw6,pw40],[12,8,16,20,49,13,17,24,28,32,36,40,9,33,41,45,53,57,3],[19,19,22,4114,26,129,261,9729,2057,262149,65569,41,131140,76,49160]),
([pw3,pw2,pw5,pw27,pw6,pw40],[48,16,44,52,56,5,9,21,25,24,32,36,40,1,29,41,45,61,65,3],[37,8230,69,100,44,524307,3,131201,137,529,262418,282,19457,4105,98312]),
([pw21,pw3,pw2,pw5,pw6,pw40],[12,60,72,1,32,21,29,4,16,40,56,64,68,5,41,45,53,65,69,73],[11,2049,132353,4097,645,11,8202,26,14,65569,262161,37,524368,49156,84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D6 : List StD := [
([pw3,pw16,pw27,pw6,pw40],[12,56,76,80,9,13,84,88,92,96,100,1,29,33,41,45,77,81,85],[65541,131078,2068,28,262147,8385,265,5666,42,49160])]
def p13_D5 : List StD := []
theorem p13_I5 : LevelN true p13_T 5 p13_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK true p13_T p13_t 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I6 : LevelN true p13_T 6 p13_D6 := levelStep p13_B p13_W p13_I5 (chunks 32 p13_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK true p13_T p13_t 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I7 : LevelN true p13_T 7 p13_D7 := levelStep p13_B p13_W p13_I6 (chunks 32 p13_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK true p13_T p13_t 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I8 : LevelN true p13_T 8 p13_D8 := levelStep p13_B p13_W p13_I7 (chunks 32 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
theorem p13_L : LowN true p13_R p13_T 9 := lowSearch p13_B p13_I8 (by decide +kernel)
def p17_T : Nat := v51
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,13,29)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw40,7,[0, 1, 2, 3])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) p17_B p5_B p5_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[],[],[])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p17_D6 : List StD := []
theorem p17_I6 : LevelN true p17_T 6 p17_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C7x0 : levelOK true p17_T p17_t 6 (p17_D6.map Prod.fst) ((p17_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I7 : LevelN true p17_T 7 p17_D7 := levelStep p17_B p17_W p17_I6 (chunks 32 p17_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C7x0
  ))
theorem p17_L : LowN true p17_R p17_T 8 := lowSearch p17_B p17_I7 (by decide +kernel)
def p18_T : Nat := v52
def p18_R : List Nat := [0, 1, 2, 3]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw5,4,[0, 1, 3])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=4) p18_B p3_B p3_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[],[],[])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p18_D3 : List StD := []
theorem p18_I3 : LevelN true p18_T 3 p18_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK true p18_T p18_t 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := levelStep p18_B p18_W p18_I3 (chunks 32 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
theorem p18_L : LowN true p18_R p18_T 5 := lowSearch p18_B p18_I4 (by decide +kernel)

end Lib12108
namespace Lib15811
def pw0 : Nat := v2
def pw1 : Nat := v3
def pw6 : Nat := v30
def pw8 : Nat := v8
def pw10 : Nat := v17
def pw12 : Nat := v6
def pw17 : Nat := v5
def pw29 : Nat := v53
def p1_T : Nat := v47
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN true p1_R p1_T 2 := lowCount p1_B (by decide +kernel)
def p4_T : Nat := v48
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN true p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := v22
def p5_R : List Nat := [0, 1]
def p5_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_L : LowN true p5_R p5_T 1 := lowCount p5_B (by decide +kernel)
def p6_T : Nat := v7
def p6_R : List Nat := [0, 1]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN true p6_R p6_T 1 := lowCount p6_B (by decide +kernel)
def p14_T : Nat := v54
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw6,1,[0, 3]),(pw8,1,[1, 3]),(pw29,1,[1, 2]),(pw17,2,[1, 0, 3]),(pw10,2,[1, 0, 2]),(pw12,2,[0, 1, 2])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p6_B p6_L (by decide +kernel),mkSlice (w:=4) p14_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p14_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p14_B p1_B p1_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[],[],[])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D3 : List StD := [
([pw1,pw0,pw17,pw12],[0,4,12,8,20,16],[11,5,50,6,25,5])]
def p14_D2 : List StD := []
theorem p14_I2 : LevelN true p14_T 2 p14_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C3x0 : levelOK true p14_T p14_t 2 (p14_D2.map Prod.fst) ((p14_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := levelStep p14_B p14_W p14_I2 (chunks 32 p14_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C3x0
  ))
theorem p14_L : LowN true p14_R p14_T 4 := lowSearch p14_B p14_I3 (by decide +kernel)

end Lib15811
namespace Lib12142
def pw0 : Nat := v0
def pw1 : Nat := v1
def pw2 : Nat := v2
def pw3 : Nat := v3
def pw4 : Nat := v4
def pw5 : Nat := v5
def pw6 : Nat := v6
def pw7 : Nat := v7
def pw8 : Nat := v8
def pw9 : Nat := v9
def pw10 : Nat := v10
def pw12 : Nat := v12
def pw14 : Nat := v14
def pw16 : Nat := v16
def pw17 : Nat := v17
def pw19 : Nat := v19
def pw20 : Nat := v20
def pw21 : Nat := v21
def pw22 : Nat := v22
def pw26 : Nat := v26
def pw27 : Nat := v27
def pw28 : Nat := v28
def pw30 : Nat := v30
def pw31 : Nat := v31
def pw32 : Nat := v32
def pw33 : Nat := v33
def pw34 : Nat := v34
def pw35 : Nat := v35
def pw36 : Nat := v36
def pw37 : Nat := v37
def pw38 : Nat := v38
def pw39 : Nat := v39
def pw40 : Nat := v40
def pw42 : Nat := v55
def pw43 : Nat := v56
def pw44 : Nat := v57
def pw45 : Nat := v58
def pw46 : Nat := v59
def pw47 : Nat := v60
def pw48 : Nat := v61
def pw49 : Nat := v62
def pw50 : Nat := v63
def pw51 : Nat := v64
def pw52 : Nat := v65
def pw53 : Nat := v66
def pw54 : Nat := v67
def pw55 : Nat := v68
def pw56 : Nat := v69
def pw57 : Nat := v70
def pw58 : Nat := v71
def pw59 : Nat := v72
def pw60 : Nat := v73
def pw61 : Nat := v74
def pw62 : Nat := v75
def pw63 : Nat := v76
def pw64 : Nat := v77
def pw65 : Nat := v78
def pw66 : Nat := v79
def pw67 : Nat := v80
def pw68 : Nat := v81
def pw69 : Nat := v82
def pw70 : Nat := v83
def pw71 : Nat := v84
def pw72 : Nat := v85
def pw73 : Nat := v86
def pw74 : Nat := v87
def pw75 : Nat := v88
def pw76 : Nat := v89
def pw77 : Nat := v90
def pw78 : Nat := v91
def pw79 : Nat := v92
def pw80 : Nat := v93
def pw81 : Nat := v94
def pw82 : Nat := v95
def pw83 : Nat := v96
def pw84 : Nat := v97
def pw85 : Nat := v98
def pw86 : Nat := v99
def pw87 : Nat := v100
def pw88 : Nat := v101
def pw89 : Nat := v102
def pw90 : Nat := v103
def pw91 : Nat := v104
def pw92 : Nat := v105
def pw93 : Nat := v106
def pw94 : Nat := v107
def pw95 : Nat := v108
def pw96 : Nat := v109
def pw97 : Nat := v110
def pw98 : Nat := v111
def pw99 : Nat := v112
def pw100 : Nat := v113
def pw101 : Nat := v114
def pw102 : Nat := v115
def pw103 : Nat := v116
def pw104 : Nat := v117
def pw105 : Nat := v118
def pw106 : Nat := v119
def pw107 : Nat := v120
def pw108 : Nat := v121
def pw109 : Nat := v122
def pw110 : Nat := v123
def pw111 : Nat := v124
def pw112 : Nat := v125
def pw113 : Nat := v126
def pw114 : Nat := v127
def pw115 : Nat := v128
def pw116 : Nat := v129
def pw117 : Nat := v130
def pw118 : Nat := v131
def pw119 : Nat := v132
def pw120 : Nat := v133
def pw121 : Nat := v134
def pw122 : Nat := v135
def pw123 : Nat := v136
def pw124 : Nat := v137
def pw125 : Nat := v138
def pw126 : Nat := v139
def pw127 : Nat := v140
def pw128 : Nat := v141
def pw129 : Nat := v142
def pw130 : Nat := v143
def pw131 : Nat := v144
def pw132 : Nat := v145
def pw133 : Nat := v146
def pw134 : Nat := v147
def pw135 : Nat := v148
def pw136 : Nat := v149
def pw137 : Nat := v150
def pw138 : Nat := v151
def pw139 : Nat := v152
def pw140 : Nat := v153
def pw141 : Nat := v154
def p1_T : Nat := v7
def p1_R : List Nat := [0, 1]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN true p1_R p1_T 1 := lowCount p1_B (by decide +kernel)
def p2_T : Nat := v22
def p2_R : List Nat := [0, 1]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN true p2_R p2_T 1 := lowCount p2_B (by decide +kernel)
def p3_T : Nat := v42
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw0,1,[0, 2]),(pw1,1,[1, 2]),(pw2,1,[0, 2]),(pw3,1,[1, 2]),(pw4,1,[0, 1]),(pw5,1,[0, 1])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p3_B p2_B p2_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
([pw3,pw2,pw5],[0,4,8,12,1,5,16,20,9,13,17,21],[319,602,3237])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN true p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK true p3_T p3_t 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := levelStep p3_B p3_W p3_I2 (chunks 32 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
theorem p3_L : LowN true p3_R p3_T 4 := lowSearch p3_B p3_I3 (by decide +kernel)
def p4_T : Nat := v12
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN true p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p6_T : Nat := v25
def p6_R : List Nat := [0, 1, 2]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN true p6_R p6_T 2 := lowCount p6_B (by decide +kernel)
def p8_T : Nat := v45
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw6,4,[0, 1, 2])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p8_B p3_B p3_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[],[],[])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK true p8_T p8_t 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := levelStep p8_B p8_W p8_I3 (chunks 32 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN true p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p10_T : Nat := v47
def p10_R : List Nat := [0, 1, 2]
def p10_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_L : LowN true p10_R p10_T 2 := lowCount p10_B (by decide +kernel)
def p11_T : Nat := v48
def p11_R : List Nat := [0, 1, 2]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_L : LowN true p11_R p11_T 2 := lowCount p11_B (by decide +kernel)
def p12_T : Nat := v49
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw2,2,[0, 2, 3]),(pw3,2,[1, 2, 3]),(pw1,2,[1, 2, 3]),(pw0,2,[0, 2, 3]),(pw19,1,[2, 3]),(pw20,1,[2, 3]),(pw30,1,[0, 3]),(pw31,1,[1, 3]),(pw8,1,[1, 3]),(pw16,1,[0, 3]),(pw17,2,[0, 1, 2]),(pw9,1,[1, 2]),(pw6,2,[0, 1, 2]),(pw4,2,[0, 1, 3]),(pw32,1,[0, 2]),(pw33,1,[0, 2]),(pw34,1,[1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=1) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p1_B p1_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(14,12),(3,2),(3,1),(14,10),(5,1),(14,6),(9,8),(9,1),(5,6),(9,0),(3,0),(11,1),(7,1)],[],[[],[1,2],[1],[2],[2,1],[1,2,1]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw3,pw2,pw5,pw6],[3,1,5,13,17,21,25,33,7,15,9,11,19,29,23],[1295,3634,12483,829,17101,6640])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([pw7,pw3,pw2,pw5,pw6],[8,12,16,20,0,4,24,28,37,3,7,15,23],[16,32,3073,4609,259,5,5,10,10,192]),
([pw3,pw2,pw22,pw5,pw6],[0,4,16,20,8,12,32,36,37,3,11,15,19],[259,32,10,10,16,5,5,3073,4609,192]),
([pw9,pw3,pw2,pw5,pw6],[44,8,48,4,20,28,40,13,41],[64,3,3,8,3,3,262,176,5,5]),
([pw20,pw3,pw2,pw5,pw6],[20,12,4,0,8,32,44,25,45],[8,16,3,3,262,5,5,3,3,224]),
([pw3,pw16,pw2,pw5,pw6],[36,12,52,20,28,32,56,41,3],[3,3,5,224,16,8,3,262,3,5]),
([pw3,pw2,pw5,pw27,pw6],[24,28,0,12,32,36,60,9,3],[7,33,5,194,262,16,5,8,3,3]),
([pw21,pw3,pw2,pw5,pw6],[12,9,64,16,60,0,24,44,56,49,7,15],[3,128,3073,32,3,14,26,17,517,324])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
([pw3,pw2,pw5,pw35],[60,8,12,16,0,28,32],[7,10,11,5,20,97]),
([pw36,pw3,pw5,pw6],[8,12,0,16,28,32,24],[7,50,38,9,9,80]),
([pw3,pw37,pw5,pw6],[32,36,8,24,16,28],[5,26,33,5,10,3]),
([pw26,pw3,pw2,pw5],[32,16,8,64,0,28],[5,6,33,9,10,19]),
([pw3,pw16,pw27,pw6],[24,28,36,16,53],[7,5,10,16,5,3]),
([pw3,pw2,pw5,pw38],[24,28,36,16,60],[7,5,10,26,5,3]),
([pw3,pw39,pw5,pw6],[24,36,16,28,8,60],[19,3,12,44,3,3])]
def p12_D2 : List StD := []
theorem p12_I2 : LevelN true p12_T 2 p12_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK true p12_T p12_t 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I3 : LevelN true p12_T 3 p12_D3 := levelStep p12_B p12_W p12_I2 (chunks 32 p12_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK true p12_T p12_t 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I4 : LevelN true p12_T 4 p12_D4 := levelStep p12_B p12_W p12_I3 (chunks 32 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK true p12_T p12_t 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I5 : LevelN true p12_T 5 p12_D5 := levelStep p12_B p12_W p12_I4 (chunks 32 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
theorem p12_L : LowN true p12_R p12_T 6 := lowSearch p12_B p12_I5 (by decide +kernel)
def p14_T : Nat := v52
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw5,4,[0, 1, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=4) p14_B p3_B p3_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[],[],[])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK true p14_T p14_t 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := levelStep p14_B p14_W p14_I3 (chunks 32 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
theorem p14_L : LowN true p14_R p14_T 5 := lowSearch p14_B p14_I4 (by decide +kernel)
def p15_T : Nat := v101
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_L : LowN true p15_R p15_T 3 := lowCount p15_B (by decide +kernel)
def p16_T : Nat := v155
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,6,[1, 2, 3, 4]),(pw2,6,[0, 2, 3, 4]),(pw5,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw42,4,[0, 1, 4]),(pw43,4,[0, 1, 3]),(pw44,4,[0, 1, 2]),(pw1,3,[1, 2, 3, 4]),(pw45,1,[3, 4]),(pw0,3,[0, 2, 3, 4]),(pw31,2,[1, 3, 4]),(pw34,2,[1, 2, 4]),(pw46,2,[1, 2, 3]),(pw47,2,[0, 1, 4]),(pw48,2,[0, 1, 3]),(pw7,2,[2, 3, 4]),(pw10,2,[0, 3, 4]),(pw49,1,[2, 4]),(pw50,1,[2, 3]),(pw51,1,[1, 4]),(pw52,1,[3, 4]),(pw53,1,[0, 4]),(pw54,2,[0, 2, 4]),(pw55,2,[0, 2, 3]),(pw56,2,[0, 2, 3]),(pw57,1,[2, 3]),(pw19,2,[2, 3, 4]),(pw58,1,[1, 3]),(pw59,1,[1, 2]),(pw60,1,[1, 4]),(pw61,1,[3, 4]),(pw62,1,[0, 1]),(pw63,1,[2, 4]),(pw64,2,[1, 2, 3]),(pw65,1,[2, 3]),(pw66,1,[1, 2]),(pw67,1,[2, 4]),(pw68,1,[1, 3]),(pw69,1,[0, 1]),(pw70,1,[0, 2]),(pw71,1,[0, 4]),(pw72,1,[0, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p16_B p12_B p12_L (by decide +kernel),mkSlice (w:=2) p16_B p12_B p12_L (by decide +kernel),mkSlice (w:=4) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=8) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=16) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=12) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=20) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=24) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=12) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=5) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=12) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=18) p16_B p10_B p10_L (by decide +kernel),mkSlice (w:=18) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=13) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=17) p16_B p10_B p10_L (by decide +kernel),mkSlice (w:=17) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=24) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=9) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=20) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=22) p16_B p2_B p2_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(1,[128]),(5,[]),(6,[]),(7,[]),(1,[386]),(0,[260]),(1,[260]),(0,[261]),(1,[261]),(0,[390]),(1,[390]),(0,[130]),(1,[130]),(0,[131]),(8,[]),(0,[128]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(6,[128]),(5,[128]),(5,[130]),(0,[129]),(16,[]),(17,[]),(18,[]),(0,[384]),(1,[384]),(19,[]),(0,[385]),(0,[386]),(7,[128]),(1,[131]),(20,[]),(21,[]),(22,[]),(0,[262]),(0,[263]),(23,[]),(0,[388]),(0,[389]),(24,[]),(25,[]),(26,[]),(6,[130]),(27,[]),(28,[]),(7,[130]),(29,[]),(30,[]),(1,[128,272]),(6,[256]),(1,[388]),(0,[384,147]),(7,[263]),(31,[]),(1,[385]),(0,[256]),(32,[]),(33,[]),(0,[259]),(1,[128,260]),(7,[256]),(34,[]),(35,[]),(1,[392]),(0,[392]),(36,[]),(1,[260,400]),(0,[260,400]),(0,[260,261]),(1,[260,261]),(1,[261,16]),(37,[]),(0,[391]),(1,[391,19]),(0,[262,401]),(1,[262,401]),(0,[395,147]),(1,[395,147]),(0,[128,401]),(1,[128,401]),(0,[128,402]),(0,[390,19]),(1,[128,402]),(1,[390,19]),(1,[384,147]),(0,[129,130]),(0,[128,129]),(1,[131,130]),(0,[131,130]),(0,[131,128]),(1,[386,387]),(1,[386,384]),(1,[260,19]),(0,[260,19]),(0,[256,147]),(0,[128,275]),(0,[128,272]),(0,[260,512]),(6,[131]),(0,[128,403]),(0,[128,525]),(1,[128,525]),(0,[128,400]),(0,[131,400]),(0,[384,145]),(0,[384,518]),(1,[384,518]),(7,[128,271]),(1,[260,130]),(0,[260,130]),(0,[257,144]),(0,[128,274]),(0,[131,272]),(0,[128,260]),(0,[128,263]),(0,[384,388]),(0,[390,386]),(0,[390,384]),(1,[390,384]),(1,[129,128]),(1,[129,130]),(1,[257,144]),(0,[260,17]),(0,[390,17]),(0,[131,402]),(0,[386,145]),(0,[130,402]),(1,[129,402]),(0,[129,402]),(1,[387,384]),(0,[387,384]),(0,[386,387]),(1,[131,128]),(0,[259,147]),(0,[131,275]),(0,[387,147]),(1,[387,147]),(0,[131,261]),(1,[131,261]),(0,[131,262]),(0,[131,389]),(7,[130,268]),(7,[263,15]),(0,[390,129]),(38,[]),(0,[390,131]),(1,[256,516]),(5,[260]),(14,[128]),(7,[256,260]),(7,[128,260]),(7,[128,256]),(39,[]),(40,[]),(0,[130,274]),(0,[261,16]),(0,[261,18]),(1,[261,18]),(1,[130,274]),(41,[]),(1,[390,17]),(0,[130,400]),(0,[391,19]),(0,[387]),(5,[256]),(0,[131,403]),(0,[258,147]),(5,[131]),(0,[388,386]),(0,[388,384]),(0,[129,400]),(0,[384,390]),(1,[390,388]),(42,[]),(1,[390,391]),(1,[256,400]),(0,[392,19]),(0,[256,400]),(0,[256,403]),(1,[392,19]),(6,[258]),(0,[392,147]),(0,[388,275]),(0,[260,403]),(6,[260]),(6,[263]),(1,[392,147]),(0,[260,128]),(1,[130,400]),(1,[394,147]),(1,[260,402]),(0,[262,400]),(5,[259]),(0,[260,129]),(1,[262,402]),(1,[390,260]),(0,[128,273]),(1,[256,145]),(5,[129]),(0,[256,260]),(1,[391,130]),(1,[128,391]),(0,[391,275]),(1,[391,275]),(0,[263,402]),(1,[128,391,279]),(5,[258]),(1,[260,261,20]),(0,[256,402]),(0,[256,401]),(0,[393,16]),(0,[130,401]),(0,[131,128,405]),(0,[130,129,276]),(0,[128,129,276]),(13,[260]),(0,[128,256]),(0,[384,273]),(0,[129,384,277]),(0,[131,384,277]),(0,[384,147,521]),(0,[384,275]),(0,[129,384,279]),(0,[131,384,279]),(0,[384,147,522]),(0,[389,16]),(5,[128,271]),(0,[130,391,279]),(0,[128,391,279]),(0,[129,272]),(0,[130,272]),(0,[261,131,276]),(1,[261,131,276]),(6,[128,271]),(6,[261]),(0,[131,262,405]),(0,[128,520]),(5,[128,256]),(14,[256]),(5,[260,256]),(5,[260,128]),(0,[257]),(6,[256,141]),(0,[131,274]),(0,[260,258]),(0,[260,130,278]),(0,[260,261,20]),(0,[261,260]),(0,[386,394,151]),(0,[384,394,151]),(5,[128,270]),(5,[258,143]),(5,[130,268]),(5,[130,271]),(5,[260,15]),(0,[260,128,277]),(0,[260,259]),(0,[128,273,520]),(0,[392,393,20]),(0,[260,257]),(13,[128]),(5,[128,129])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(29,28),(30,28),(7,5),(11,10),(30,26),(7,6),(30,22),(30,14),(11,9),(29,25),(29,21),(29,13),(7,3),(11,3),(19,3),(19,18),(11,2),(19,16),(19,17),(23,3),(11,1),(29,17),(29,9),(7,1),(29,20),(29,12),(30,24),(15,13),(19,2),(30,18),(30,10),(30,6),(19,1),(15,3),(29,5),(7,2),(29,16),(29,8),(30,16),(30,8)],[],[[],[2,3],[2],[3],[3,2],[0],[0,2,3],[0,2],[0,3],[0,3,2],[2,3,2],[0,2,3,2]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[3,0,4,1,5,9,17,25,29,7,15,13,49,53,57,11,19,23,21,33,37,41,45,27,31,35,39,43],[63,2635,296074,67851,10092564,52428852,71434292,14017,134239553,123776])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40],[0,4,3,37,41,45,1,5,49,53,57,7,11,15,19,8,12,16,17,25,29,23,31,39,43],[3,1,35084,78352,148516,3,262213,528449,1065025,2097290,4194450,8388770,11036,16786732,24112]),
([pw14,pw3,pw2,pw5,pw6,pw40],[3,0,8,20,24,28,33,41,57,9,17,45,53,15,27,61,5,13,65,7,43,47],[6,16969,2,20625,2107680,65547,1030,294930,163874,16973,729,10600,529557,1060132,4529]),
([pw73,pw3,pw2,pw5,pw6,pw40],[28,0,32,49,53,16,36,9,61,4,12,1,21,29,37,41,69,3,39],[4099,262785,41,1045,2,67650,259,262,8195,16393,32788,131265,13,41,21]),
([pw3,pw2,pw42,pw5,pw6,pw40],[24,28,40,44,3,9,21,57,1,5,49,53,23,12,32,13,29,33,45,11,19,31,39],[828,85,32789,524357,1114438,4137,135177,2097193,4457002,8193,3,147,3089,17537,2179]),
([pw3,pw2,pw5,pw6,pw28,pw40],[28,32,48,52,29,9,17,57,3,13,1,5,21,25,37,41,45,49,53,61,73,23],[3372,581,12294,524549,533,16457,32810,3145737,65577,259,131073,209,262147,147,145]),
([pw74,pw3,pw2,pw5,pw6,pw40],[32,28,56,60,21,9,17,53,3,0,4,24,1,5,13,25,37,41,49,57,77,7,15,23,43,47],[16777745,33555489,262147,6291459,2049,12572,16454,32789,277,65610,131113,8388649,131,1572867,131])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw12,pw7,pw3,pw2,pw5,pw6,pw40],[76,80,20,84,88,64,92,3,68,72,96,100,53,7,15,43],[32,256,32,512,24577,32897,4,2,129,9,9,6,3,3,3,22,20,20,72,72,7168]),
([pw12,pw3,pw2,pw5,pw6,pw40],[80,20,88,112,1,3,116,37,53,57,7,15,104,108,73,43,24,28,64,68,72,13,33,45,61,81,85,89,27],[525313,268697600,1048608,68900,166436,23,19,16781329,2105361,139,33574982,4218894,67110312,134253248,8389448]),
([pw7,pw3,pw2,pw5,pw75,pw6,pw40],[92,124,128,120,3,72,84,116,132,4,64,136,11,15,19,23],[8,2,28,32,13,5,3,146,514,3,3,32775,34,260,260,1024,65,65,12292,16404,2176]),
([pw50,pw7,pw3,pw2,pw5,pw6,pw40],[148,88,36,76,112,140,156,160,28,144,152,49,3],[32,512,32,3,3,1024,4,64,3,3,4354,6,9,9,72,3,3,6,2192,129,17]),
([pw76,pw7,pw3,pw2,pw5,pw6,pw40],[84,92,72,124,132,164,4,3,80,128,136,168,7,23],[8,72,72,256,3,3,32,4,4736,3,3,36,148,3,3,8226,17,17,3,3,3072]),
([pw76,pw3,pw2,pw5,pw6,pw40],[72,164,92,84,108,1,41,45,3,53,57,15,32,104,13,33,80,112,136,148,61,93,7,43],[3,3,65792,4199244,8395916,35,16433,1056801,16433,2129942,41026,131218,265036,527756,1728]),
([pw7,pw14,pw2,pw5,pw6,pw40],[20,76,112,3,84,28,172,1,13,41,53,57,15,0,108,116,45,27,96,100,104,61,97,101,105,7,43,47],[37,8193,16683,3146002,16690,131203,8192,4326602,142612678,16777229,33289,69637,33818140,67704912,36356]),
([pw7,pw3,pw2,pw42,pw5,pw6,pw40],[168,40,44,136,3,24,84,116,11,23,176,180,184,31],[4,2,48,56,352,9,6,146,146,386,3,517,517,8197,1028,2048,4096,9,88,65,9]),
([pw7,pw3,pw2,pw5,pw6,pw28,pw40],[96,48,92,57,120,3,52,188,28,116,132,180,184,11,23],[16,2,49,8212,48,265,3,3,6,546,3,196,1089,16449,136,37,4096,12,2048,9,9]),
([pw74,pw7,pw3,pw2,pw5,pw6,pw40],[112,56,60,100,84,3,28,200,43,0,4,24,192,196,53,77,7,15,23,47],[352,769,525313,4096,196609,8192,4,2,104,2072,112,6,11,10,35,133,132,262149,17,32792,16385]),
([pw12,pw14,pw3,pw2,pw5,pw6,pw40],[84,172,80,96,20,72,100,7,24,28,64,92,108,116,27,43],[32,128,1024,32,385,33281,8192,16400,4,3,3,28,12,65,9,2068,3,3,3,3,4168]),
([pw77,pw3,pw56,pw2,pw5,pw6,pw40],[204,140,148,28,216,3,36,208,0,4,108,172,212,220],[1024,256,10,13,5,520,34,35,130,130,35,4096,5,5,64,17,17,80,10240,5,5]),
([pw77,pw3,pw2,pw5,pw6,pw40],[140,212,96,36,148,5,17,3,25,49,53,144,29,61,11,24,28,100,156,220,224,228,9,33,27,35],[2177,262147,33620694,16958736,2053,41,8259,1057025,4227,8912938,6291500,43,1606,4816,17686]),
([pw60,pw14,pw3,pw2,pw5,pw6,pw40],[24,96,232,40,100,108,104,180,20,92,184,27],[128,1,262,128,1024,6,1,6,8,2049,6,6,9,25,6,33,65,48,522,65,49]),
([pw60,pw3,pw2,pw5,pw6,pw40],[24,40,100,57,3,236,9,232,13,45,53,39,4,28,92,180,184,228,240,5,21,25,33,109,113,11,27,35],[3,8394964,134250497,67174401,27288,524338,259,1048579,17039618,4194353,33554529,588,2098179,131085,1037]),
([pw78,pw3,pw56,pw2,pw5,pw6,pw40],[108,28,132,204,244,3,60,140,172,208],[133,2,3,16,5,22,9,12,5,768,3,2,34,9,64,3,12,3,5,44,3]),
([pw78,pw3,pw2,pw5,pw6,pw40],[28,108,132,3,60,13,53,248,33,104,208,21,41,45,0,24,244,252,1,57,27,43],[2115630,1,65545,1085518,17,262332,1191,3168,171,275,4884,279,131147,532481,8771]),
([pw14,pw3,pw16,pw2,pw5,pw6,pw40],[24,80,108,172,104,20,68,28,256,3,7,27],[64,66,2114,2,13,24,1030,546,3,19,134,1,32,261,392,5,25,44,12,17,21]),
([pw14,pw3,pw16,pw2,pw6,pw40],[24,80,20,108,104,172,17,37,53,57,4,256,61,73,3,7,27,28,72,13,33,45,65,81,85,89,117,121,15,23,35,43,47],[3,263170,66694,16859561,4596957872,32838,16390,4198419,528394,1,604014921,3355445856,8396821,1056780,2229017]),
([pw73,pw3,pw56,pw2,pw5,pw6],[28,32,140,200,49,53,36,144,208,61,101,260,9,33,121,125],[133,2049,133,19,35,1100,1100,517,518,1,16657,33058,8217,4138,19]),
([pw14,pw3,pw33,pw2,pw5,pw6,pw40],[104,24,264,172,9,13,272,3,32,68,268,23,276,11,15,27],[512,51328,529,4,8456,265,37,176,6,37,1060,2,2114,4096,65,17,3,1040,200,9,3]),
([pw14,pw3,pw2,pw42,pw6,pw40],[24,40,280,3,33,104,232,5,13,49,57,61,27,28,32,44,108,184,284,9,45,93,23],[3,2134136,3,4611,16992,142,259,2051,2306,4194325,524301,1048724,131073,263177,74753]),
([pw74,pw64,pw3,pw2,pw5,pw6],[32,28,56,208,9,21,196,288,292,57,3,43,60,144,192,5,13,33,53,125,129,23],[65,101,10257,16385,526339,1,3150992,526,649,33828,65542,37,131338,281,262147]),
([pw14,pw3,pw2,pw5,pw44,pw6,pw40],[28,108,304,104,300,9,24,32,284,3,27,296,47],[1,2082,16,1664,1154,4105,36,3,274,280,3,3,6,36,3,517,3,76,1,64,3]),
([pw79,pw3,pw2,pw5,pw6,pw40],[24,64,28,172,41,53,20,92,57,45,80,5,13,37,61],[3,1154,3,185,908,2114,67,16387,4102,8257,57,780,49,261,49]),
([pw3,pw2,pw80,pw5,pw6,pw40],[24,28,104,308,312,1,5,9,32,21,49,3,23,13,33,53,11,19,31,39],[248,2612,10293,66101,131634,4296,20557,262345,524490,257,3,1,1283,1283,32775]),
([pw3,pw2,pw42,pw28,pw40],[24,32,316,320,9,57,3,48,1,5,21,25,29,41,45,61,73,133,23],[860,2181,32837,5126,8217,327689,16410,131073,35,35]),
([pw81,pw3,pw2,pw5,pw6,pw40],[32,48,24,104,232,57,324,73,3,45,61,4,28,172,184,328,5,9,29,39],[3,657816,16390,3,569,65858,1038,1027,262147,32988,8385,545,4357,61,37]),
([pw82,pw3,pw2,pw5,pw6,pw40],[28,332,24,92,172,336,25,53,73,232,9,3,4,192,5,29,49,61,77,23,47],[3,1056520,3,220,8203,18466,131075,70,32771,524577,852,1073,133,327685,133]),
([pw3,pw2,pw5,pw6,pw83],[28,24,340,344,17,9,13,29,53,1,5,21,37,45,57,125,137,3],[132652,85,34822,197,4121,65578,8329,259,16403,259]),
([pw3,pw2,pw84,pw6,pw40],[24,32,348,352,9,17,21,0,40,184,1,5,29,37,45,49,53,57,3,11,31],[265244,165,524357,4166,8233,1048601,16410,801,32771,196611])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw85],[356,84,172,112,224,360,92,28,116,136,3],[16,1,1153,22,22,33,41,65,65,41,6,6,6,6,776]),
([pw86,pw7,pw3,pw2,pw6,pw40],[92,248,380,364,368,72,84,124,136,172,148,160,208,372,376],[184,24584,184,2305,273,4,2,65,65,6,3,3,516,518,5120]),
([pw12,pw3,pw2,pw75,pw6,pw40],[92,136,148,388,20,96,120,172,28,208,384,3,7,15],[64,1024,4096,67,261,9,24,5,3,24,132,130,2081,8705,34]),
([pw76,pw12,pw3,pw2,pw6,pw40],[92,148,136,20,80,172,0,208,392,396,400,3,15],[64,24,24,3,5,256,512,4101,2051,1025,3,5,34,36,130]),
([pw77,pw87,pw2,pw5,pw6,pw40],[92,208,148,140,108,172,61,0,212,224,404,408,69],[128,9,6,5,9,4096,322,577,1024,17,34,2088,17,7,6]),
([pw88,pw3,pw2,pw5,pw6,pw40],[172,92,236,428,108,208,28,84,412,416,420,424,432,19],[256,512,1024,2048,8257,10,44,3,3,14,5,5,4113,129,48]),
([pw12,pw3,pw2,pw5,pw6,pw85],[208,112,108,444,172,440,32,84,212,436,448,3,7],[256,512,2048,4161,32,1034,11,9,38,11,17,6,6,145,5]),
([pw86,pw3,pw2,pw5,pw6,pw40],[108,172,112,372,376,380,0,84,92,248,364,368,452,456],[88,3080,4096,3,8210,548,5,258,7,5,34,5,3,130,5]),
([pw86,pw87,pw3,pw2,pw6,pw40],[108,208,92,148,172,460,464,84,468,61,73,3],[32,35,7,5,10,512,1024,2049,128,68,10,69,18,273,3]),
([pw86,pw3,pw2,pw6,pw40],[108,132,248,380,104,1,32,136,372,472,49,84,92,96,112,364,368,376,9,21,45,53,57,81,129],[131335,102665,1219,3266,46,524340,45,8651290,16777740,7364625]),
([pw12,pw3,pw2,pw42,pw6,pw40],[96,136,84,104,116,428,32,108,188,228,432,476,480,484,488,492,496,500],[2048,4096,57376,1090,580,65537,33,28,3,56,13,386,131072,18,3]),
([pw74,pw87,pw3,pw2,pw5,pw6],[160,172,84,96,108,112,512,516,24,92,104,140,144,224,504,508,3,43],[65536,2057,4099,16384,131084,8192,32768,260,1027,193,112,515,176,7,7]),
([pw7,pw14,pw2,pw75,pw6,pw40],[92,520,172,84,96,124,188,64,72,136,208,524,3,15],[2050,32,256,9,9,67,128,69,5,34,6,6,4113,9217,528]),
([pw7,pw3,pw2,pw89,pw6,pw40],[528,96,484,84,32,64,80,160,532,11,116,136,184,188,492,31],[1,4,16736,537,26,5,6,645,6,97,32771,8193,4354,1160,2050]),
([pw90,pw7,pw3,pw2,pw5,pw6],[136,208,156,536,552,556,140,200,540,32,36,84,96,144,160,192,544,548],[332,9220,332,229384,4097,16,32,3,2562,48,3,34,129,144,16385]),
([pw50,pw91,pw3,pw2,pw5,pw6],[148,160,208,136,36,156,188,200,404,560,564,568,3],[4096,512,1024,3,13,18,34,5,7,2306,5,7,65,131,10]),
([pw76,pw7,pw14,pw2,pw6,pw40],[84,96,72,92,124,136,172,188,572,80,148,200,392],[16,516,20,11,9,4352,4,9,3,386,161,3073,65,65,34]),
([pw92,pw3,pw2,pw5,pw6,pw40],[136,168,108,104,0,4,116,492,32,268,576,580,3],[48,48,1024,2048,259,130,69,200,3,7,10,517,4101,10,3]),
([pw93,pw3,pw2,pw5,pw6,pw40],[200,104,108,588,584,20,32,208,0,64,68,80,112,268,440,452,456,89,7],[1312,2592,65536,262209,49216,25,146,146,5,9,9,8204,4100,131075,7]),
([pw76,pw3,pw2,pw6,pw28,pw40],[104,172,472,32,48,52,96,596,592,600,3,7],[48,48,1034,2048,11,388,7,5,66,7,5,134,512,65,3]),
([pw74,pw76,pw3,pw2,pw6,pw40],[472,108,200,104,620,540,612,56,136,164,248,364,456,604,608,616,624,89,93,141,15],[7200,524321,262657,1048836,8192,16576,32836,19,131081,65553,25,3,13,3,6]),
([pw77,pw7,pw56,pw5,pw6,pw40],[148,208,140,224,4,32,36,108,112,172,188,228],[36,4,259,3,20,12,3,3,140,3,3,64,3584,3,3]),
([pw7,pw60,pw2,pw5,pw6,pw40],[236,116,136,40,108,200,240,84,96,104,176,180,184,284,412,628,101,3,11],[16385,8,81,41472,80,33,2048,4096,65572,131075,262147,1025,268,130,6]),
([pw78,pw7,pw3,pw5,pw6,pw40],[84,172,208,96,364,60,72,104,112,124,220,248,368,452,632,3],[4688,24,8192,11,3,32,16512,3,3,2052,5,33025,3,3,1028]),
([pw7,pw14,pw16,pw5,pw6,pw40],[172,80,84,4,24,104,116,256,28,64,68,72,636],[1034,514,50,48,261,10,2,5,5,2048,193,129,5,5,4160]),
([pw7,pw14,pw16,pw6,pw40],[172,116,84,24,80,53,57,4,104,256,28,72,96,100,108,112,188,200,640,644,648,45,145,149,153,157,3,7,15,23,27,35,43,47],[410,26,269,279557,2192,1145110567,8867414085,687870499,6477062721,2130018]),
([pw7,pw14,pw33,pw5,pw6,pw40],[116,96,172,104,200,272,636,23,0,120,264,276,284,652,3,11],[513,257,9,9,12290,147,1024,32773,22,161,2048,36,16390,65,65]),
([pw7,pw14,pw2,pw42,pw6,pw40],[96,84,24,40,104,116,136,188,20,44,160,176,184,284,656,3,23],[20,8,20,20,8195,641,9,200,17409,65824,32771,2050,4096,34,65]),
([pw74,pw7,pw64,pw2,pw5,pw6],[84,160,200,652,32,256,43,56,96,108,116,144,192,196,292,516],[24,8192,2114,4096,321,24,128,524,24,7,1025,16418,32772,7,35]),
([pw7,pw3,pw2,pw42,pw28,pw40],[96,84,316,116,120,3,188,52,49,57,133,23],[16,4,49,50,3,5,5,44,5,200,2051,66,1024,10,769]),
([pw94,pw3,pw2,pw5,pw6,pw40],[96,256,664,120,104,188,32,72,80,116,200,264,276,324,660,3,19],[8,16384,392,6152,65601,5,5,6,5,8736,1027,34,32771,18,17]),
([pw95,pw3,pw2,pw5,pw6,pw40],[116,104,96,120,668,0,72,80,84,188,256,264,276,672],[9,40,200,6152,6,21,3,3,20,3,3,8704,1284,3,3]),
([pw7,pw81,pw2,pw5,pw6,pw40],[96,324,172,188,48,24,104,160,680,32,676,113,3],[1026,16,97,96,2561,11,17,24,133,10,6,10,4103,388,257]),
([pw96,pw3,pw2,pw5,pw6,pw40],[160,84,200,100,136,148,536,584,652,684,0,64,124,140,224,456],[16385,1025,39040,7,8321,577,72,11,257,516,7,257,19,35,52]),
([pw97,pw3,pw2,pw5,pw6,pw40],[148,200,96,120,100,692,72,80,152,156,188,336,440,452,688,49],[8,16384,200,11,13056,38,5,17,38,3,3,3088,32772,3,3]),
([pw7,pw82,pw2,pw5,pw6,pw40],[116,148,100,96,332,172,4,120,200,284,336,49,113,23],[129,16,11,7,4616,321,17,7,24,8195,35,1060,2056,7,7]),
([pw7,pw3,pw2,pw5,pw6,pw83],[96,200,340,344,84,24,172,100,112,300,3],[8,4,1057,50,17,12,5,132,5,10,10,72,273,82,515]),
([pw7,pw3,pw2,pw84,pw6,pw40],[96,148,348,84,120,116,11,184,188,200,57,31],[16,4,19,82,9,5,5,100,5,514,2051,264,137,42,1027]),
([pw77,pw64,pw2,pw5,pw6,pw40],[148,140,96,100,292,212,696,700,36,108,156,408,69],[66,1026,133,137,66,4354,52,17,2,17,21,2058,548,9,13]),
([pw86,pw64,pw3,pw2,pw6,pw40],[96,108,456,73,256,292,56,196,248,380,704,112,124,364,368],[1220,5,28676,19,1220,2048,521,34,256,521,48,257,9,26,35]),
([pw77,pw64,pw56,pw2,pw5,pw6],[292,108,140,256,28,148,208,4,36,188,212],[132,4,20,18,9,12,772,33,3,1024,73,66,35,9,10]),
([pw98,pw3,pw2,pw5,pw6,pw40],[172,108,96,112,256,212,248,24,72,84,124,452,456],[8,1288,2048,131,4105,68,70,17,7,34,21,19,3,513,38]),
([pw3,pw99,pw2,pw5,pw6,pw40],[108,176,236,256,412,708,0,84,172,184,208,416,488,628,712],[81,38,3,8226,41,2065,4096,529,10,16389,260,7,9,130,1027]),
([pw77,pw3,pw2,pw43,pw5,pw6],[256,720,84,172,24,92,212,108,220,452,456,688,716,724,728,113],[128,4098,11776,20,25,34,3,32834,3,9,288,12,16384,68,5]),
([pw74,pw77,pw3,pw2,pw5,pw6],[256,212,172,56,84,140,512,92,96,112,208,220,504,11],[41,33,5,4096,8450,512,10,18,5,192,1090,5,2050,5,17]),
([pw78,pw3,pw72,pw2,pw6,pw40],[108,28,176,172,84,208,452,220,248,252,732,736,740],[69,64,3,9,20,289,1156,44,3,2,2561,4096,24,3,7]),
([pw100,pw3,pw2,pw5,pw6,pw40],[208,752,96,148,220,92,748,28,172,744,756,760],[512,66,137,67,1026,6,3,3,6,49,7,2320,52,9,9]),
([pw101,pw3,pw2,pw5,pw6,pw40],[220,92,208,104,312,4,96,240,764,768,772,776,23],[256,4129,512,1024,2048,3,20,3,18,3,76,129,3,10,5]),
([pw102,pw3,pw2,pw5,pw6,pw40],[104,176,780,788,108,0,124,172,308,784],[35,69,256,516,3,10,3,3,20,5,137,14,20,3,3]),
([pw60,pw3,pw16,pw2,pw6,pw40],[104,208,108,256,412,792,236,292,428,24,40,268,480,488,500,89,3],[16,8464,400,16384,32897,1027,65632,35,44,4096,12,11,515,2116,7]),
([pw78,pw3,pw56,pw2,pw43,pw6],[28,108,176,84,172,204,4,208,504],[262,1,3,69,18,42,36,3,148,1,13,34,3,24,7]),
([pw103,pw3,pw2,pw5,pw6,pw40],[208,220,112,440,692,796,148,196,256,292,336,452,456,584,688],[32,16432,12432,3,2056,1030,9,3,264,7,513,6,6,65,3]),
([pw104,pw3,pw2,pw5,pw6,pw40],[108,176,804,784,28,104,208,800,0,220,532,632,780],[259,1041,128,4096,146,6,3,578,9,13,2084,7,9,34,67]),
([pw105,pw3,pw2,pw5,pw6,pw40],[240,220,100,652,812,4,104,184,208,312,348,764,776,808],[2049,42,8192,129,4609,6,1029,7,9,3,280,3,3,84,3]),
([pw78,pw64,pw3,pw2,pw5,pw6],[108,172,256,28,104,456,56,60,196,208,248,368,452,516,632,700,704,3],[65888,37,2053,4096,32771,8,131,530,16401,140288,9,6,9,6,5]),
([pw78,pw3,pw2,pw42,pw6,pw40],[104,176,28,824,632,804,24,40,108,136,308,352,816,820],[131,4101,11296,608,3,10,3,3,260,25,25,14,4,3,3]),
([pw3,pw2,pw106,pw5,pw6,pw40],[836,828,832,104,256,328,3,324,676],[70,386,11,7,18,13,7,13,36,5,3,24,112,9,9]),
([pw14,pw3,pw33,pw2,pw42,pw40],[24,136,104,108,432,172,272,280,840,65,93,3,23],[1,4122,1030,3,36,532,2432,5,66,1,25,74,5,34,3]),
([pw14,pw3,pw2,pw80,pw6,pw40],[104,24,312,28,108,136,304,20,148,308,768,93,105],[2,2561,1028,38,265,68,69,3,28,4225,3,56,8,2,3]),
([pw14,pw3,pw107,pw2,pw6,pw40],[256,292,172,844,24,80,148,208,548,692,848,3],[8,296,10,21,7,160,3584,3,5,16,3,5,3,5,66]),
([pw14,pw3,pw2,pw108,pw40],[24,852,28,148,104,172,864,33,3,40,208,232,312,856,860,5,9,13,49,93,27],[3,1583504,16897,262174,33090,1027,131078,65577,228,4109]),
([pw109,pw3,pw2,pw5,pw6,pw40],[100,220,312,256,148,868,0,4,104,228,776],[256,131,69,3,1028,3,5,3,12,50,552,3,10,17,3]),
([pw81,pw3,pw2,pw42,pw40],[24,316,28,872,73,104,172,220,232,3,44,208,5,9,29,49,57,93,39],[3,395056,3,33188,4618,2051,16390,89,8412,65541]),
([pw110,pw3,pw2,pw5,pw6,pw40],[208,292,116,256,100,228,272,884,0,140,172,696,876,880,3],[4,260,7,7,14848,144,3,3,136,3,3,1048,104,33,16449]),
([pw111,pw3,pw2,pw5,pw6,pw40],[208,172,368,376,84,100,256,24,248,272,292,364,452,680,888],[8,2052,4360,131,16394,36,5,5,68,1025,3,98,18,19,8705])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw76,pw3,pw2,pw6,pw85],[208,84,172,356,100,104,116,256,892],[9,9,6,7,272,3,130,5,6,97]),
([pw112,pw3,pw2,pw5,pw6],[256,292,208,129,104,0,24,84,100,140,156],[33,1537,17,84,264,6,3,14,11,129]),
([pw12,pw3,pw2,pw113,pw40],[116,256,904,120,228,428,900,28,104,172,896,908],[8,1024,56,144,69,36,66,2051,518,257]),
([pw114,pw3,pw2,pw6,pw40],[100,104,84,256,292,228,0,48,124,272],[65,274,140,11,33,17,12,22,33,515]),
([pw86,pw3,pw2,pw115,pw40],[100,228,256,292,84,272,912,916,920,924],[65,392,38,3,3,9,516,12,3,17]),
([pw86,pw116,pw3,pw2,pw40],[100,256,84,228,292,928,932,936,940],[6,33,208,11,6,20,5,9,258,11]),
([pw117,pw3,pw2,pw5,pw6],[256,220,100,292,0,104,272,456,548,584,944,948],[17,1281,641,100,6,12,3,2050,9,3]),
([pw12,pw3,pw2,pw108,pw40],[904,104,116,120,228,256,428,956,28,220,952],[8,1024,88,272,129,65,160,38,513,7]),
([pw7,pw14,pw2,pw113,pw40],[116,256,176,264,492,904,960,28,84,112,120,148,172,964],[1025,64,25,386,101,8195,4610,25,6,2081]),
([pw92,pw3,pw2,pw28,pw40],[256,84,176,104,48,28,968,972,976,85],[17,17,512,38,196,14,3,266,5,9]),
([pw118,pw3,pw2,pw6,pw40],[84,176,100,680,220,0,104,256,272,304,364,368,784,980],[36,15360,133,7,26,11,257,577,3,26]),
([pw76,pw3,pw2,pw6,pw83],[84,112,212,272,620,104,116,176,256,340,984],[6,516,25,261,1042,17,11,97,131,42]),
([pw7,pw60,pw16,pw6,pw40],[256,24,84,988,104,112,116,120,240,484,488,492,500,636,792,149],[138,16386,19,261,3592,4096,32801,5,5,8256]),
([pw78,pw7,pw64,pw5,pw6],[84,172,368,72,124,196,364,452,456,636,704,992,996,1000,1004],[92,1316,128,2051,3,12288,3,3,16896,3]),
([pw7,pw106,pw5,pw6,pw40],[256,636,664,104,328,828,836,184,276,484,488,652,660,1008,1012,1016,3],[12548,104,72,18433,33412,1060,3,65553,3,18]),
([pw7,pw14,pw33,pw42,pw40],[84,172,104,176,780,24,40,112,272,840,960,1020,23],[20,2116,36,19,4105,520,3,1027,386,9]),
([pw7,pw14,pw107,pw6,pw40],[116,172,148,256,0,28,108,112,120,548],[257,17,7,98,517,11,14,7,10,133]),
([pw7,pw14,pw2,pw108,pw40],[256,116,28,104,112,148,176,852,24,108,172,860],[12,128,264,517,98,2051,145,1025,65,50]),
([pw94,pw3,pw2,pw42,pw40],[256,112,1028,120,172,28,104,108,116,428,492,904,1024],[8,4096,1544,161,2054,5,7,17,17,322]),
([pw7,pw81,pw2,pw42,pw40],[112,172,84,176,256,1032,24,104,212],[257,32,194,7,13,40,19,18,7,13]),
([pw119,pw3,pw2,pw6,pw40],[116,104,256,100,120,220,172,456,492,580,712],[17,1025,784,134,41,7,68,3,44,3]),
([pw77,pw3,pw2,pw120,pw6],[256,1040,100,104,228,24,84,172,176,304,688,1036],[256,2050,1033,40,6,3,6,129,592,17]),
([pw121,pw2,pw5,pw6,pw40],[104,1060,1044,0,84,100,172,1048,1052,1056],[140,5,5,776,3,3,50,80,3,3]),
([pw3,pw2,pw106,pw42,pw40],[680,1064,836,24,256,220,328,1068,1072,3],[515,11,7,18,140,276,97,10,17,5]),
([pw110,pw3,pw2,pw5,pw44],[172,116,256,100,148,220,1076,120,300,304,328],[2,258,34,37,72,72,5,1168,5,529])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D3 : List StD := [
([pw7,pw106,pw42,pw40],[220,84,256,1028,1072,172,836,904,1024,1068,1080,1084,1088],[1800,81,7,56,133,6146])]
def p16_D2 : List StD := []
theorem p16_I2 : LevelN true p16_T 2 p16_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C3x0 : levelOK true p16_T p16_t 2 (p16_D2.map Prod.fst) ((p16_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := levelStep p16_B p16_W p16_I2 (chunks 32 p16_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK true p16_T p16_t 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := levelStep p16_B p16_W p16_I3 (chunks 32 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x0 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x1 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x2 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (2*32)).take 32) = true := by decide +kernel
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := levelStep p16_B p16_W p16_I4 (chunks 32 p16_D5 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C5x0
  · exact p16_C5x1
  · exact p16_C5x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C6x0 : levelOK true p16_T p16_t 5 (p16_D5.map Prod.fst) ((p16_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I6 : LevelN true p16_T 6 p16_D6 := levelStep p16_B p16_W p16_I5 (chunks 32 p16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C7x0 : levelOK true p16_T p16_t 6 (p16_D6.map Prod.fst) ((p16_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I7 : LevelN true p16_T 7 p16_D7 := levelStep p16_B p16_W p16_I6 (chunks 32 p16_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C8x0 : levelOK true p16_T p16_t 7 (p16_D7.map Prod.fst) ((p16_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I8 : LevelN true p16_T 8 p16_D8 := levelStep p16_B p16_W p16_I7 (chunks 32 p16_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C8x0
  ))
theorem p16_L : LowN true p16_R p16_T 9 := lowSearch p16_B p16_I8 (by decide +kernel)
def p17_T : Nat := v107
def p17_R : List Nat := [0, 1, 2, 3]
def p17_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
theorem p17_L : LowN true p17_R p17_T 3 := lowCount p17_B (by decide +kernel)
def p18_T : Nat := v156
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,10,11),(1,9,11),(2,9,13),(3,3,11),(4,3,19)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw2,5,[0, 3, 4, 2]),(pw5,5,[0, 3, 4, 1]),(pw6,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw16,4,[0, 3, 4]),(pw44,4,[0, 1, 2]),(pw1,3,[1, 2, 3, 4]),(pw45,1,[3, 4]),(pw32,2,[0, 2, 4]),(pw20,2,[2, 3, 4]),(pw0,3,[0, 2, 3, 4]),(pw9,2,[4, 2, 1]),(pw73,2,[3, 2, 1]),(pw122,1,[1, 2]),(pw47,2,[0, 1, 4]),(pw34,2,[1, 2, 4]),(pw19,2,[2, 3, 4]),(pw8,2,[1, 3, 4]),(pw33,2,[0, 2, 4]),(pw63,1,[2, 4]),(pw48,2,[0, 1, 3]),(pw52,1,[3, 4]),(pw123,2,[0, 2, 3]),(pw31,2,[1, 3, 4]),(pw124,1,[1, 2]),(pw46,2,[1, 2, 3]),(pw125,1,[1, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=4) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=6) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=24) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel),mkSlice (w:=3) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=2) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p18_B p17_B p17_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=9) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=10) p18_B p10_B p10_L (by decide +kernel),mkSlice (w:=10) p18_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=5) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=17) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p18_B p1_B p1_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(5,[128]),(3,[128]),(2,[128]),(9,[]),(10,[]),(3,[131]),(11,[]),(2,[131]),(12,[]),(13,[]),(0,[128]),(14,[]),(1,[128]),(15,[]),(0,[131]),(4,[131]),(16,[]),(17,[]),(18,[]),(19,[]),(5,[131]),(5,[256]),(20,[]),(21,[]),(5,[256,143]),(22,[]),(3,[256,147]),(0,[130]),(4,[128]),(0,[129]),(1,[131]),(5,[259]),(5,[257]),(23,[]),(2,[259]),(0,[258]),(0,[256]),(4,[256]),(24,[]),(0,[256,147]),(1,[256,147]),(0,[259]),(0,[257]),(25,[]),(4,[259]),(5,[129]),(5,[258]),(1,[258]),(26,[]),(4,[258]),(5,[131,268]),(5,[131,271]),(0,[389]),(0,[390]),(0,[261]),(0,[262]),(4,[256,143]),(0,[128,274]),(0,[262,19]),(0,[386]),(0,[384]),(5,[260,13]),(4,[129]),(5,[257,140]),(5,[263]),(2,[257,144]),(0,[257,144]),(0,[260,17]),(4,[257,140]),(0,[263])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(13,12),(30,28),(11,9),(11,10),(30,26),(13,9),(19,18),(30,22),(11,3),(30,14),(19,3),(19,17),(13,5),(21,5),(21,17),(21,20),(19,1),(19,16),(11,1),(13,14),(11,8),(13,1),(19,26),(11,14),(11,26)],[],[[],[1],[3],[1,3]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,8,5,4,12,9,17,21,33,41,3,1,29,7,11,16,20,13,25,37,45,49,53,57,15],[3109,139464,267522,543248,32933,3146759,4210741,8397130,16777944,70402])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40],[0,24,16,21,49,3,28,1,53,20,32,36,17,33,61,7,11,40,44,9,37,41,15],[1,524321,32782,41586,6357826,161,4110,17554,16578,13,2097,67841,9228,4108,1442064]),
([pw20,pw3,pw2,pw5,pw6,pw40],[0,48,16,32,21,33,1,17,29,37,3,56,41,8,12,52,60,64,68,5,9,49,65,7,11,15],[1,525313,158,8430882,50352650,1089,150,362,6722,21,2293761,5507073,60,148,808]),
([pw126,pw3,pw2,pw5,pw6,pw40],[8,24,20,72,41,45,57,3,76,61,32,84,9,37,7,11,0,16,80,17,21,25,33,69,15],[1,102570,17973322,4194433,32790,8390434,2359818,641,8214,526688,417,5180,18497,8284,21]),
([pw34,pw3,pw2,pw5,pw6,pw40],[20,88,80,32,9,37,41,5,17,21,3,92,96,49,0,16,100,104,25,29,33,73,7,11,15],[1,8406166,21005066,525313,103,2202,4870,263169,99,412,2172929,89,1191937,549,97]),
([pw3,pw33,pw2,pw5,pw6,pw40],[20,32,0,108,1,16,60,21,3,112,13,25,37,41,100,17,53,57,15],[263450,350,1616,18707,2640,5,32938,4,12299,164,5,65551,131115,161,12289])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw20,pw7,pw3,pw5,pw6,pw40],[32,48,16,100,0,104,116,60,68,88],[16,16,7,10,3,16,37,194,321,14,11,10,37,36,513]),
([pw127,pw14,pw3,pw5,pw6,pw40],[104,16,80,48,120,124,128,0,60,88,100],[128,2,259,20,48,2,1024,65,65,6,13,41,3,3,516]),
([pw127,pw3,pw5,pw6,pw40],[48,100,16,32,9,13,60,132,25,41,49,20,88,136,140,21,33,37,73],[4,87,263251,2067,39,299,291,65676,41604,153096]),
([pw128,pw3,pw2,pw5,pw6,pw40],[60,36,76,88,100,116,15,16,80,92,144,148],[1024,32,193,512,97,7,9,22,9,20,3,22,3,2306,9]),
([pw129,pw3,pw2,pw5,pw6,pw40],[60,88,16,80,120,156,32,92,96,148,152],[1156,7,7,512,3,3,3,24,3,40,3,336,3,56,3]),
([pw7,pw3,pw33,pw5,pw6,pw40],[88,32,16,20,36,0,60,80,112,116,136,65,77],[32,521,133,136,2057,4099,69,18,65,262,32,274,3,1044,3]),
([pw63,pw3,pw2,pw5,pw6,pw40],[32,112,60,36,92,96,116,16,76,80,152],[1024,8,131,256,11,17,38,65,6,3,84,3,3,544,3]),
([pw3,pw130,pw2,pw5,pw6,pw40],[160,32,60,148,80,76,168,72,96,164,172,15],[545,14,28,3,69,164,3,256,2051,82,5,11,3,25,1026]),
([pw131,pw3,pw2,pw5,pw6,pw40],[32,180,112,100,136,36,48,176,184,16,116],[130,32,517,112,131,3,268,73,14,3,18,3,5,1296,5]),
([pw34,pw126,pw3,pw2,pw5,pw40],[20,80,88,72,32,100,0,68,76,92,96,112],[64,1,262,20,7,1,546,1036,131,12,38,37,2066,25,11]),
([pw132,pw64,pw3,pw2,pw5,pw40],[20,136,124,188,88,60,112,180,184],[1,1,130,260,3,1,12,10,32,26,28,3,66,5,3]),
([pw132,pw3,pw2,pw5,pw40],[60,88,20,32,124,192,1,9,49,100,196,21,0,80,13,17,33,81],[4,4867,65811,775,131307,16467,71,36024,172,11268]),
([pw126,pw3,pw33,pw2,pw5,pw40],[80,100,76,20,48,32,112,144,148,16,92,136,85,89],[128,1028,131,4640,2057,8213,36,19,18,8,322,73,7,6,265]),
([pw133,pw3,pw2,pw5,pw6,pw40],[32,200,136,28,208,0,116,212,16,36,100,204,15],[2082,64,4353,76,35,3,1168,25,524,3,6,3,137,20,21]),
([pw3,pw2,pw134,pw5,pw6,pw40],[60,152,216,112,100,16,72,92,77,89,7,11],[259,128,9,532,9,6,18,7,18,1057,6,2053,9,68,9]),
([pw135,pw3,pw2,pw5,pw6,pw40],[88,72,48,184,68,220,20,28,224,228,104],[8,11,11,84,72,3,3,20,161,1284,513,38,385,34,529])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([pw136,pw3,pw5,pw6,pw40],[184,100,48,232,28,236,32,88,136,240],[9,552,38,11,7,6,7,17,17,448]),
([pw137,pw3,pw2,pw5,pw40],[48,28,136,260,72,32,92,100,152,244,248,252,256],[321,129,1538,6148,12,25,3,5,49,10]),
([pw138,pw3,pw2,pw5,pw40],[32,72,192,100,116,264,268,16,48,92,136,152,252],[2656,40,131,4168,7,258,1044,5,5,18]),
([pw139,pw3,pw5,pw6,pw40],[132,72,100,32,136,272,20,48,88,96,276],[1058,34,134,66,517,13,21,9,17,264]),
([pw3,pw140,pw5,pw6,pw40],[284,280,288,32,100,136,0,72,236,292,296,93],[322,2065,13,52,515,3,146,13,37,1032]),
([pw3,pw2,pw141,pw5,pw40],[32,300,80,100,308,216,72,144,304,312,97],[3,385,28,1064,14,3,3,81,545,20])]
def p18_D3 : List StD := []
theorem p18_I3 : LevelN true p18_T 3 p18_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK true p18_T p18_t 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := levelStep p18_B p18_W p18_I3 (chunks 32 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK true p18_T p18_t 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I5 : LevelN true p18_T 5 p18_D5 := levelStep p18_B p18_W p18_I4 (chunks 32 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK true p18_T p18_t 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I6 : LevelN true p18_T 6 p18_D6 := levelStep p18_B p18_W p18_I5 (chunks 32 p18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C7x0 : levelOK true p18_T p18_t 6 (p18_D6.map Prod.fst) ((p18_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I7 : LevelN true p18_T 7 p18_D7 := levelStep p18_B p18_W p18_I6 (chunks 32 p18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C7x0
  ))
theorem p18_L : LowN true p18_R p18_T 8 := lowSearch p18_B p18_I7 (by decide +kernel)

end Lib12142
namespace Aux1
def ptopT : Nat := v157
def ptopR : List Nat := [0,1,2,3,4]
def ptopE : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,2,10),(4,1,17)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(v17,6,[4,0,1,2])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB Lib12108.p12_B Lib12108.p12_L (by decide +kernel), fun _ h => by cases h⟩
def ptopC : List (Nat × List Nat) := [(0,[260]),(0,[261]),(0,[262]),(0,[263]),(0,[388]),(0,[389]),(0,[390]),(0,[391]),(0,[]),(0,[4]),(0,[5]),(0,[6]),(0,[7]),(0,[392]),(0,[393]),(0,[394]),(0,[395]),(0,[8]),(0,[9]),(0,[10]),(0,[11]),(0,[12]),(0,[13]),(0,[14]),(0,[15])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(26,24),(25,24),(7,5),(7,6),(7,4),(28,24),(7,3),(7,2),(14,6),(11,3),(10,3),(22,6),(19,3),(18,3),(13,9),(11,9),(13,5),(21,5),(17,3),(17,5),(25,9),(17,9)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptopD5 : List StD := []
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD6 : List StD := [([v3,v2,v5,v6,v40],[0,1,5,4,9,13,8,17,12,16,21,20,25,24,29,28,32,33,37,41,36,45,40,49,53,44,48,52,57,61,56,60,64,65,68,69,72,73,76,80,84,88,77,92,96,81,85],[511,65060,983076,133169188,8455720976,9127133200,1082340147218,8858701824,34119228593152,105553124982784])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := levelStep ptopB ptopW ptopI5 (chunks 8 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
theorem ptopL : LowN true ptopR ptopT 7 := lowSearch ptopB ptopI6 (by decide +kernel)
end Aux1
namespace Aux3
def ptopT : Nat := v158
def ptopR : List Nat := [0,1,2,3,4]
def ptopE : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,2,10),(4,1,17)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(v41,5,[3,1,2,0]),(v40,5,[0,1,2,3]),(v17,5,[0,4,1,2]),(v5,5,[3,0,1,4]),(v2,5,[3,0,2,4]),(v1,5,[3,1,2,4]),(v3,5,[4,1,2,3]),(v159,4,[0,1,4]),(v21,4,[0,2,4])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=16) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=1) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel), fun _ h => by cases h⟩
def ptopC : List (Nat × List Nat) := [(5,[]),(4,[]),(6,[]),(3,[]),(2,[]),(0,[]),(1,[]),(8,[]),(7,[]),(2,[392])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(22,20),(21,20),(7,5),(7,6),(22,18),(19,18),(7,3),(14,6),(11,3),(25,24),(10,3),(22,6),(19,3),(13,9),(11,9),(13,5),(21,5),(17,3),(17,5),(25,9),(26,18),(17,9),(26,24),(28,24),(11,1),(13,1)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptopD5 : List StD := []
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD6 : List StD := [([v3,v16,v2,v5,v6,v40],[0,21,8,13,89,5,57,93,53,29,33,37,41,45,49,12,9,4,25,16,32,20,24,61,36,97,65,69,101,73,77,81,85],[15,120,394,7688,24586,98304,425984,1574400,6316032,164160,58721344,201343056,293602560,603996544,7516210176])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := levelStep ptopB ptopW ptopI5 (chunks 8 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD7 : List StD := [([v3,v2,v5,v6,v40],[0,1,5,4,9,13,8,17,21,12,25,16,29,33,37,41,20,45,24,49,3,53,57,61,28,65,69,32,73,77,81,85],[127,2017,63585,983328,7341592,29370392,101515282,144715264,302843008,3758956544])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 8 ptopD7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  ))
theorem ptopL : LowN true ptopR ptopT 8 := lowSearch ptopB ptopI7 (by decide +kernel)
end Aux3
namespace Aux4
def ptopT : Nat := v160
def ptopR : List Nat := [0,1,2,3,4]
def ptopE : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,1,9),(4,1,17)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(v5,7,[0,1,3,4]),(v41,5,[3,0,1,2]),(v40,5,[0,1,2,3]),(v17,5,[0,4,1,2]),(v0,5,[0,3,4,2]),(v2,5,[3,0,2,4]),(v1,5,[1,3,2,4]),(v4,4,[0,3,1,4]),(v87,4,[0,1,3]),(v159,4,[0,1,4]),(v21,4,[0,2,4]),(v59,4,[1,2,3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=4) ptopB Lib12108.p7_B Lib12108.p7_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=16) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=0) ptopB Lib15811.p14_B Lib15811.p14_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=16) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel), fun _ h => by cases h⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(4,[]),(5,[]),(0,[128]),(3,[]),(1,[]),(2,[]),(6,[]),(10,[]),(11,[]),(0,[128,273]),(0,[129]),(0,[130]),(4,[387]),(7,[]),(0,[131]),(0,[131,273]),(5,[5]),(0,[131,261]),(2,[131]),(4,[140]),(3,[268]),(0,[256]),(0,[256,145]),(0,[256,147]),(9,[]),(0,[256,401]),(0,[256,403]),(0,[257]),(2,[385]),(0,[258]),(0,[258,273]),(0,[259]),(0,[384]),(2,[129]),(0,[384,145]),(0,[384,147]),(2,[259]),(8,[]),(0,[384,273]),(2,[387]),(0,[384,275]),(0,[260]),(0,[260,513]),(5,[259]),(0,[261]),(0,[262]),(0,[263]),(0,[385]),(6,[392]),(1,[140]),(5,[387]),(0,[385,395]),(0,[385,523]),(0,[386]),(0,[386,273]),(0,[387]),(0,[260,514]),(0,[260,401]),(0,[260,403]),(0,[261,515]),(0,[263,17]),(0,[388]),(0,[388,513]),(0,[388,273]),(0,[389]),(4,[268]),(1,[268]),(0,[390]),(0,[390,273]),(0,[391]),(0,[391,17]),(0,[392]),(0,[392,513]),(0,[393]),(0,[394]),(1,[387]),(0,[395]),(0,[395,17])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(14,12),(13,12),(7,5),(7,6),(22,18),(19,18),(7,3),(14,6),(11,3),(10,3),(22,6),(19,3),(28,24),(26,24),(7,1),(13,5),(9,3),(21,5),(22,20),(17,3),(9,5),(17,5),(28,12),(26,18),(10,18),(17,18),(25,24),(21,20),(28,20),(15,12),(9,1),(13,1),(17,1),(21,1),(11,1),(19,1),(10,6),(22,2),(15,6),(17,24),(10,12),(9,12),(7,12),(17,16),(9,24),(23,20),(17,20),(10,2),(30,6),(23,6),(22,16),(30,20),(13,6),(27,3),(27,18),(22,4),(10,24),(28,8),(9,8),(7,2),(21,18),(21,6),(15,5),(21,24),(21,12),(26,3),(7,4),(19,6),(27,24),(19,2),(10,8),(11,5),(13,4),(14,4),(26,8),(25,8),(15,3),(29,12),(29,5),(28,16),(26,16),(23,18),(23,3),(23,5),(13,8),(14,8)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptopD3 : List StD := []
theorem ptopI3 : LevelN true ptopT 3 ptopD3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD4 : List StD := [([v161,v2,v147,v6,v40],[49,25,57,21,17,81,37,41,45,5,9,1,65,61,89,13,29],[7,26,98,386,3584,13312,17536,106496,33152,24704]),([v2,v147,v5,v162,v40],[5,9,1,49,25,57,65,61,41,89,17,237,13,37,29,177,81,149,45],[7,56,194,770,3088,28672,37120,73744,131344,270848]),([v163,v3,v2,v162,v40],[17,25,237,53,57,81,33,41,149,5,9,73,13,61,109,177,65,89,69],[7,26,98,386,3584,28672,36992,74752,132224,401408]),([v164,v2,v5,v162,v40],[5,1,73,237,17,25,13,29,37,41,177,53,161,49,109,89,145,93,149,97],[7,56,448,1600,14336,16514,33282,196624,262688,524928]),([v3,v2,v165,v162,v40],[5,13,1,17,25,237,37,29,177,41,53,57,121,65,137,89,145,33,149,97,45],[7,56,194,770,3088,28672,33284,196624,262672,1703936]),([v166,v3,v2,v162,v40],[17,25,237,53,57,81,33,41,149,5,9,73,13,61,109,177,65,89,69],[7,26,98,386,3584,28672,36992,74752,132224,401408]),([v3,v2,v167,v162,v40],[5,13,1,17,25,237,37,29,177,41,53,57,121,65,137,89,145,33,149,97,45],[7,56,194,770,3088,28672,33284,196624,262672,1703936]),([v3,v2,v168,v6,v40],[5,13,1,17,25,21,37,29,177,269,53,57,121,65,137,41,89,145,33,45,97],[7,56,194,770,3088,28672,98308,393232,557072,1343488]),([v2,v147,v169,v6,v40],[109,9,73,49,25,57,65,61,77,69,21,17,37,93,233,45,277,81,113],[7,56,194,770,3088,13312,114688,135184,34832,299008]),([v170,v2,v147,v5,v40],[61,9,65,29,21,13,37,25,81,45,41,109,73,49,57,77,69,17],[7,56,448,1600,6146,24704,98306,131216,536,131712]),([v3,v2,v171,v6,v40],[109,9,73,21,25,17,61,113,233,45,277,49,57,65,285,77,69,81,33,85],[7,56,200,1792,6160,24578,98306,393232,524816,704]),([v172,v3,v2,v6,v40],[17,21,237,57,25,53,33,189,45,149,105,101,93,177,121,65,137,129,77,141],[7,56,208,784,3104,4162,8450,114688,917504,4416]),([v173,v3,v2,v6,v40],[17,21,25,57,53,33,121,45,129,105,37,93,233,277,65,281,297,97],[7,28,100,388,530,3074,12416,16432,98432,131232]),([v3,v174,v169,v6,v40],[109,9,73,105,185,49,61,113,233,69,53,57,121,81,125,129,85,133],[7,56,193,769,3074,1090,518,28672,229376,704]),([v175,v3,v169,v6,v40],[73,109,9,57,53,61,121,69,129,105,49,113,233,81,229],[7,28,100,388,1538,2082,4226,9248,16520,2208]),([v176,v2,v147,v6,v40],[49,25,57,21,17,81,37,41,45,5,9,1,65,61,89,13,29],[7,26,98,386,3584,13312,17536,106496,33152,24704]),([v2,v147,v177,v6,v40],[109,9,73,49,25,57,65,61,77,69,21,17,37,93,233,45,277,81,113],[7,56,194,770,3088,13312,114688,135184,34832,299008]),([v3,v2,v165,v178,v6],[5,13,1,233,25,237,45,41,37,29,281,57,129,77,141,121,65,137,145,33,89],[7,56,194,770,3088,28672,229376,208,786448,1572928]),([v179,v3,v2,v165,v6],[41,13,277,129,141,77,45,25,149,33,189,5,1,165,29,281,57,121,65,137],[7,56,448,1600,6146,8322,16898,98432,917504,17024])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC4x0 : levelOK true ptopT ptopt 3 (ptopD3.map Prod.fst) ((ptopD4.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC4x1 : levelOK true ptopT ptopt 3 (ptopD3.map Prod.fst) ((ptopD4.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC4x2 : levelOK true ptopT ptopt 3 (ptopD3.map Prod.fst) ((ptopD4.drop (2*8)).take 8) = true := by decide +kernel
theorem ptopI4 : LevelN true ptopT 4 ptopD4 := levelStep ptopB ptopW ptopI3 (chunks 8 ptopD4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC4x0
  · exact ptopC4x1
  · exact ptopC4x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD5 : List StD := [([v3,v2,v5,v180,v23,v40],[5,9,1,17,25,37,33,153,41,45,53,57,65,61,4,29,77,69,81,85,0],[7,24,97,128,768,3088,12290,49154,196610,262224,24,524816,1081408,832,33536]),([v20,v3,v165,v6,v40],[80,8,13,57,53,17,1,161,121,84,29,129,41,105,5,165,173,169,177,93,49,145,149,89,97],[7,248,1856,6224,57384,214272,292864,3671072,4200488,25695232]),([v181,v3,v2,v5,v6,v40],[13,5,21,9,73,1,25,17,33,29,89,41,45,109,101,185,197,49,201,205,145,93,149,97],[7,56,192,768,7168,24592,32900,772,67588,393344,524816,2072,3145856,4196416,8391168]),([v2,v182,v5,v6,v23,v40],[5,9,1,49,25,57,65,61,101,21,77,69,105,37,33,20,13,45,41,81,17,93,89],[7,56,194,770,3074,4120,24577,98816,393217,540688,1049104,1179664,2097152,4341760,164352]),([v3,v2,v5,v23,v183,v40],[5,9,1,17,25,13,37,33,69,89,53,57,4,93,65,61,77,81,85,129,20,29,97,45],[7,24,32,193,769,3088,12290,49154,65794,24,131216,786448,3145856,4202752,8389248]),([v3,v2,v5,v6,v184,v40],[5,9,1,21,25,17,37,93,13,45,53,57,65,61,24,73,77,69,81,33,56,0,85,29,97,20,41],[7,56,200,256,521,3088,12290,49154,196610,786448,3145744,4194832,8388608,17302016,100663808]),([v185,v3,v2,v5,v6,v40],[21,5,13,73,9,17,25,93,33,29,45,41,69,1,105,49,37,89,57,65,61,77,81,85,129],[7,24,96,896,7168,8210,49216,65794,135170,294976,1572880,2101264,4194624,25165888,135424]),([v186,v2,v5,v6,v23,v40],[5,9,1,105,25,49,37,33,0,21,13,45,41,53,57,65,61,109,73,69,81,17,217,89,20],[7,56,193,1792,6145,24592,98306,393218,786434,1048720,2097680,2099216,4194304,8390784,16779776]),([v161,v3,v33,v2,v6,v40],[21,25,17,152,56,49,57,81,121,85,45,13,3,28,5,9,73,61,113,41,1,29,148,20,65,89],[7,26,98,386,1538,14336,114688,395264,527360,1048576,2097152,13107200,16941056,34111488,34209792]),([v161,v3,v2,v6,v24,v40],[21,25,17,53,49,145,33,56,152,85,45,5,13,1,29,173,41,65,9,89,61,129],[7,26,98,386,1538,14336,22528,36864,70656,155648,262144,598016,1048576,606208,2162688]),([v21,v161,v3,v2,v6,v40],[49,25,5,13,9,29,89,41,21,17,53,81,121,45,61,113,1,249],[3,12,16,32,192,770,1027,6146,8322,12,49160,8328,212992,65728,16576]),([v67,v161,v3,v2,v6,v40],[25,49,13,5,1,61,41,89,105,165,57,229,9,73,177,29,249],[3,12,16,32,192,770,1027,3,2177,12296,12,16520,102400,4288,32960]),([v3,v33,v2,v5,v162,v40],[13,3,28,5,9,73,17,25,237,61,21,177,41,1,156,33,116,20,49,57,65,89,81,121,149,45],[7,56,448,1537,6145,8192,16514,32768,200704,786560,1049104,2101264,12583040,16781440,35652096]),([v3,v2,v5,v162,v24,v40],[5,13,1,17,25,237,37,29,157,3,177,41,53,49,65,33,9,89,145,156,149,20,61,97,45,116],[7,56,194,770,3074,12304,49156,65536,133124,294928,524816,1050640,6324224,25198592,35653632]),([v21,v3,v2,v5,v162,v40],[5,13,9,49,25,33,61,20,89,41,17,237,21,177,53,1,249,81,121,149,45],[3,4,24,224,768,3,3088,4162,8706,16408,98368,33536,393232,524816,1049344]),([v67,v3,v2,v5,v162,v40],[13,5,1,25,49,61,41,89,9,73,105,165,177,57,33,249,229,45],[3,4,24,32,192,770,3088,3,4226,8216,49408,448,24,65672,147584]),([v3,v187,v2,v5,v162,v40],[13,3,28,5,9,73,17,25,237,61,109,177,41,1,156,33,116,20,49,57,65,89,81,121,149,69],[7,56,448,1537,6145,8192,16514,32768,200704,786560,1049104,2101264,12583040,16781440,35652096]),([v3,v2,v5,v162,v188,v40],[5,13,1,17,25,237,37,29,116,3,177,41,53,49,65,33,9,89,145,156,149,61,97,45,20],[7,56,194,770,3074,12304,49156,65536,133124,294928,524816,1050640,2097152,12615680,16779520]),([v189,v3,v2,v5,v162,v40],[5,13,9,49,25,33,89,41,17,237,61,109,177,53,1,249,81,121,149],[3,4,24,32,192,3,784,3074,4226,8216,50176,16576,196624,262288,1216]),([v190,v3,v2,v5,v162,v40],[13,5,1,25,49,61,41,89,9,73,157,165,253,177,257,57,33,249,229,45],[3,4,24,32,192,770,7168,3,24578,32792,196864,448,24,262280,589952]),([v3,v2,v191,v5,v6,v40],[5,9,73,13,16,21,17,25,237,61,113,177,41,20,1,49,57,65,89,0,56,33,24,45,81,121,149],[7,56,448,1544,6152,24578,98432,131586,266242,1572992,2105856,12587008,50331776,67113088,266752]),([v77,v2,v147,v5,v6,v40],[9,68,4,21,25,172,3,37,16,45,5,1,49,57,65,61,41,89,17,237,13,29,177,81,149,261],[7,8,112,448,512,3073,12304,49153,196609,786448,3145856,5308416,8388752,16842768,33685632]),([v163,v77,v3,v2,v6,v40],[25,100,56,17,237,53,57,81,33,41,149,109,9,176,4,61,3,16,69,5,73,13,113,177,65,89],[7,25,97,385,1537,2048,28672,229376,262144,1576960,6324224,10486272,16814080,33559040,33587712]),([v192,v3,v2,v5,v6,v40],[21,13,109,20,1,9,56,25,0,33,61,45,69,41,5,17,237,37,29,177,53,49,65,89,145,149,97],[7,56,448,1544,14336,16402,98432,393218,532482,3145856,4194832,8396816,16777856,33562752,67117568]),([v164,v77,v2,v5,v6,v40],[21,5,1,73,237,17,25,13,29,37,41,177,8,109,185,173,3,45,53,161,49,265,89,145,93,149,97],[1,14,112,896,3200,12292,49184,73984,131072,1835008,2097412,4195332,25165856,33555520,67110144]),([v77,v3,v2,v165,v6,v40],[21,1,8,80,25,3,56,33,84,45,5,13,17,237,37,29,177,41,53,57,121,65,137,89,145,149,97],[1,14,112,416,512,3074,12304,51200,198656,786448,7340032,8519682,16777360,33685520,67240064]),([v3,v193,v2,v5,v6,v40],[13,5,21,9,273,105,165,49,157,177,89,1,20,25,33,61,41,45,57,249,229],[7,26,224,259,1538,6152,8320,53248,197632,270464,540680,66568,24704,1057792,82944]),([v2,v147,v5,v6,v40,v194],[109,9,1,49,25,57,65,61,77,69,4,68,21,17,33,29,177,45,20,13,81,3,172,113,37,41],[7,56,194,770,3074,12304,53248,200704,790528,1064976,139280,6291472,8536064,18890752,33554432]),([v163,v3,v2,v6,v40,v194],[21,25,17,53,57,81,33,85,45,56,100,109,9,73,61,113,177,69,13,65,281,189,41],[7,26,98,386,1538,14336,51200,198656,262144,544768,143360,1052672,180224,2113536,4194304]),([v195,v3,v2,v5,v6,v40],[16,21,13,1,9,56,25,0,33,29,61,20,45,41,109,73,17,113,177,49,57,65,77,69,81,121,85],[7,24,224,1792,14336,49168,65602,132098,266242,1572928,2098192,12582928,50331712,67113024,136192]),([v3,v33,v2,v169,v6,v40],[21,3,196,109,9,73,25,17,61,113,233,45,277,53,56,33,24,200,49,57,65,77,69,81,121,85],[7,56,193,769,7168,8192,16450,32768,198656,786496,1048848,6291472,25165888,33556544,2816]),([v170,v3,v33,v2,v5,v40],[113,21,13,33,61,9,65,121,25,81,45,41,3,29,109,73,17,289,293,145,189,24,49,57,77,69,85],[7,8,112,896,3088,12290,49184,65794,132098,262144,1573120,2106368,12583168,50331680,67110144]),([v3,v2,v165,v6,v40,v194],[1,101,105,21,25,17,29,33,177,45,13,53,57,121,65,137,129,77,141,145,56,3,93,41],[7,56,200,776,1024,6160,57344,458752,2049,524432,560,3145744,4194944,192,8388608]),([v3,v2,v169,v6,v24,v40],[109,21,53,25,17,37,93,233,45,277,49,65,33,9,69,56,3,85,61,97],[7,26,98,3,896,1036,6148,8192,16640,5128,98312,131336,262144,528640,16640]),([v3,v2,v5,v6,v196,v40],[1,21,109,25,17,29,33,13,177,45,53,49,65,293,9,69,145,56,0,85,61,93],[7,26,98,134,770,3080,12352,17409,33280,65608,393224,524808,1048672,2097728,33280]),([v21,v3,v2,v169,v6,v40],[109,21,9,49,25,33,69,45,17,61,113,233,277,53,249,81,121],[3,4,24,32,192,3,274,1538,6272,8216,25088,192,98320,400,1664]),([v21,v170,v3,v2,v5,v40],[61,24,33,109,21,9,189,25,145,69,45,113,13,249,293,121,81,41,17,289,53,49],[7,24,32,448,1536,6160,24577,98432,132097,24,262288,525328,3145856,1536,263296]),([v3,v2,v197,v5,v6,v40],[109,9,73,5,21,13,25,17,33,93,45,1,49,57,249,77,69,61,29,89,41,145,85],[7,56,208,784,1048,2050,12352,16642,98306,4160,393472,1573888,2097472,4195392,1792]),([v67,v3,v2,v169,v6,v40],[21,105,53,25,49,61,45,24,200,9,73,233,177,301,57,33,249,77,69,229,97],[3,4,24,32,448,1538,26,3,14336,16408,98816,393728,24,524312,1081408]),([v3,v2,v169,v198,v6,v40],[109,9,73,21,25,17,105,37,93,233,45,277,56,53,33,61,69,49,121,129,97],[7,56,72,392,3584,4114,8192,49154,66562,131072,49168,66576,278528,525312,1065984]),([v199,v3,v2,v169,v6,v40],[109,21,53,25,61,33,69,45,185,49,37,93,233,277,9,57,81,125,85,133,97],[3,4,8,48,192,3,770,3074,12416,49664,16432,16576,196640,786560,1048736]),([v3,v2,v169,v6,v200,v40],[109,9,73,21,49,61,113,233,45,277,53,3,77,69,81,25,33],[7,25,104,9,896,1026,1058,2050,12290,16432,32768,8448,65536,352,8448]),([v201,v3,v2,v169,v6,v40],[21,105,9,53,49,33,45,24,192,25,17,233,177,301,57,281,225,297,61,305,85,113],[3,12,16,32,448,14,1538,3,14336,16904,12,229376,786944,1049152,2359360]),([v202,v3,v2,v169,v6],[233,200,21,45,277,196,9,69,73,77,25,17,85,24,97,109,101,185,189,33,37,229,281,201,61,65,81],[63,968,7304,24578,98628,166916,1835013,14682368,55050496,86509568]),([v3,v203,v2,v5,v6,v40],[21,16,13,109,9,73,25,17,37,113,33,41,197,1,29,45,20,49,57,65,61,89,81,149,213],[7,56,193,1792,6145,8240,192,17920,100352,393280,1572880,2099216,4195392,8390720,18875392]),([v86,v2,v147,v5,v6,v40],[73,9,13,17,25,37,113,33,45,109,1,49,57,65,61,41,89,21,29,197,81,149],[3,4,24,224,256,1538,6160,24578,98306,131096,393344,688128,1048720,2129936,98432]),([v86,v163,v3,v2,v6,v40],[17,25,13,73,9,113,61,69,21,53,57,81,33,41,149,109,197,65,89],[3,4,24,96,128,259,1538,6146,24578,32792,32864,106496,131152,270352,270400]),([v3,v2,v5,v6,v204,v40],[1,9,109,21,25,17,29,33,13,41,197,53,57,65,61,77,69,81,85,129,97,45],[7,56,200,268,1544,6160,24578,3,98306,131216,48,786448,192,1114240,2163200]),([v86,v3,v2,v165,v6,v40],[13,1,8,80,17,25,29,33,45,101,105,21,41,197,53,57,121,65,137,89,145,149,97],[1,14,48,192,256,1538,2096,192,14336,49184,458752,528386,1048736,2101280,4198528]),([v205,v3,v2,v5,v6,v40],[21,5,13,1,9,73,17,25,29,33,45,41,89,117,105,49,177,57,65,61,81,229,313],[7,56,192,768,7168,8210,49280,770,69634,163968,786448,6160,1049216,2101376,4198912]),([v59,v2,v147,v5,v6,v40],[9,73,13,21,24,25,17,37,113,41,53,49,201,65,237,93,45,197,317],[3,28,96,384,512,1027,6208,8450,3,16480,33152,196612,262464,96,384]),([v163,v59,v3,v2,v6,v40],[25,17,237,53,49,113,93,109,9,73,61,41,5,13,69,197],[3,7,26,98,3,128,768,1056,2048,4864,9248,57344,608,768,1056]),([v164,v59,v2,v5,v6,v40],[13,24,21,5,53,73,237,17,25,93,113,197,45,1,29,41,49,265],[7,56,448,1537,6145,8208,384,16896,32768,65680,131600,8208,66176,384,16896]),([v59,v3,v2,v165,v6,v40],[21,1,53,25,17,33,93,41,13,5,237,37,45,197,49,121,321,129,141],[1,6,24,96,128,772,1048,2368,12544,16404,98368,393220,16464,24,96]),([v2,v206,v147,v5,v6,v40],[9,68,4,5,1,49,25,57,65,61,41,89,21,172,3,37,16,45,17,237,13,29,177,81,149],[7,25,224,769,3073,4096,24640,114688,131072,786496,3178496,5243904,8421440,16778304,35840]),([v2,v147,v5,v6,v40,v207],[109,9,73,49,25,57,65,61,77,69,4,68,21,17,37,93,177,45,13,81,3,172,113,16,41],[7,56,194,770,3074,12304,53248,200704,262144,540688,139280,3145744,4341760,9453568,16777216]),([v208,v2,v147,v5,v6,v40],[73,9,13,17,25,113,37,45,109,49,57,65,61,41,89,21,93,197,81,149],[3,4,24,96,128,259,1552,6146,24578,32792,98368,172032,262224,532496,24640]),([v209,v2,v147,v5,v6,v40],[9,73,21,25,17,37,113,41,5,49,201,65,237,13,45,197,317],[3,4,24,96,128,259,1552,2114,3,4120,8288,57344,65616,24,96]),([v3,v2,v165,v210,v6,v40],[5,13,1,165,25,21,33,29,45,41,53,57,121,65,137,129,77,141,17,93,3,97],[7,26,32,194,770,3088,1028,28672,229376,262144,208,784,524352,1048832,2097472]),([v211,v3,v2,v165,v6,v40],[21,1,8,180,25,29,33,41,45,5,13,17,325,53,161,49,121,65,137,129,77,141,145,149,97],[1,14,16,96,384,1538,7168,1120,1408,57344,458752,3670016,4196416,8388992,16777536]),([v3,v2,v165,v6,v40,v212],[5,13,1,21,17,37,29,41,233,53,49,121,65,137,89,281,33,56,25,93,45],[7,26,98,138,258,1540,14336,16516,32772,65616,131216,262144,589952,65600,1048576]),([v213,v3,v2,v165,v6,v40],[13,21,1,53,17,33,93,45,105,101,25,237,157,57,121,321,145,41,329],[3,12,16,96,128,776,3074,4162,3,9224,49216,12,66624,394240,96]),([v214,v3,v2,v5,v6,v40],[5,21,13,1,9,49,25,33,89,45,41,101,17,29,53,57,113,77,69,145,189,85],[7,24,96,128,1792,2066,4162,8195,515,49216,73744,393232,1572928,2097728,8960]),([v215,v3,v2,v5,v6,v40],[21,9,1,25,17,33,93,29,45,89,41,109,237,13,53,161,49,225,229,97],[1,6,24,224,1792,2054,4120,8288,8960,114688,70,131588,65616,262168,524864])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x1 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x2 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x3 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x4 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x5 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x6 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC5x7 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (7*8)).take 8) = true := by decide +kernel
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := levelStep ptopB ptopW ptopI4 (chunks 8 ptopD5 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  · exact ptopC5x1
  · exact ptopC5x2
  · exact ptopC5x3
  · exact ptopC5x4
  · exact ptopC5x5
  · exact ptopC5x6
  · exact ptopC5x7
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD6 : List StD := [([v3,v2,v5,v6,v35,v40],[1,5,28,4,101,17,105,25,109,37,33,8,16,13,41,45,49,53,73,65,9,69,40,0,85,61,89,36,32,20,24],[31,226,1798,14594,49410,196737,787465,1314825,2392065,4260992,12583072,18907296,33554440,469795840,1612742656]),([v3,v2,v216,v6,v40],[52,1,105,8,13,48,28,117,17,21,25,29,33,37,41,45,49,53,57,121,73,65,137,129,77,141,56,32,145,36,89,93,97],[255,1841,14420,49744,459818,7868427,59801611,469834752,604030208,7650447360]),([v3,v2,v5,v6,v180,v40],[1,5,9,4,17,105,25,29,109,3,32,153,16,13,8,41,45,49,53,57,69,77,93,145,64,0,85,33,89,97,20,24],[15,114,3970,28930,98562,917572,141,4109,3473412,12714176,50331728,68223056,134217736,809566336,3221323776]),([v20,v3,v2,v5,v6,v23,v40],[68,1,25,17,33,3,16,8,4,45,41,5,9,117,157,109,49,57,65,61,69,81,149,29,89],[1,2,12,112,448,1536,14336,12,18448,32768,1536,196616,790528,4480,1053696,2097176,12,4195332,8388608,16778256,1536]),([v20,v3,v5,v6,v24,v40],[4,8,13,25,53,17,1,161,65,16,29,73,69,41,105,5,165,109,169,28,9,93,49,145,72,3,57,45,149,61,89,97,76],[7,248,1856,2051,12368,114728,427264,1736706,176128,14681120,118489122,402661416,536870913,3223331840,4296028160]),([v202,v20,v3,v2,v5,v6,v40],[20,3,4,5,109,9,8,25,17,93,41,21,73,33,29,89,24,181,185,173,49,57,61,32,145,189,193],[7,24,100,384,512,1024,2048,4096,384,24576,98305,131120,786688,24592,24,3145984,4210720,8421408,50331904,384,67158016]),([v3,v217,v5,v6,v40],[8,1,109,9,13,5,92,17,21,25,29,16,65,209,28,41,45,49,53,57,113,61,69,73,77,145,85,89,93,97],[63,976,15440,114960,918088,3151882,29425673,33691200,71369408,939595776]),([v36,v3,v5,v6,v40],[4,5,1,13,9,96,49,53,25,57,16,61,29,65,69,45,73,77,17,21,37,28,41,93,145,89,97],[31,1008,15380,245777,786728,1055786,6848520,25170272,4489504,109089792]),([v218,v3,v2,v6,v40],[28,21,17,88,13,25,56,53,49,100,9,57,16,33,29,81,45,69,85,1,109,105,37,41,113,32,73,89],[63,4064,61736,459364,1573905,6320152,9568273,17323008,109184000,151146496]),([v3,v2,v5,v6,v219],[28,1,109,9,13,104,17,21,25,29,16,177,37,24,41,45,49,53,57,113,69,73,77,93,145,85,89,97,33],[31,496,7729,57488,459048,525834,7381000,25232160,34636128,478192128]),([v220,v3,v2,v5,v6],[20,13,41,21,45,9,69,73,77,108,25,17,85,33,93,89,97,28,109,101,185,16,5,157,49,53,113],[31,497,7760,122897,917672,1314312,14705160,50334336,102776960,83905024]),([v3,v221,v2,v5,v6,v23,v40],[5,16,68,32,73,17,25,37,33,109,41,45,9,61,8,69,49,4,81,85,113,89],[7,25,96,385,512,3072,4096,96,8448,16384,34816,65600,8448,131096,34816,262464,96,526400,1048576,2099456,3072]),([v222,v3,v2,v5,v6,v23,v40],[32,73,25,17,3,8,45,41,5,9,1,37,33,109,53,57,65,61,4,69,81,149,113,89],[1,2,12,16,32,192,1792,12,6400,8192,192,49160,197120,262657,524928,1052680,12,2097284,4194304,8392832,192]),([v3,v69,v2,v5,v6,v23,v40],[5,3,28,9,1,17,25,37,33,21,69,89,73,16,20,45,49,57,65,61,4,8,77,81,85,129,93,24],[7,25,96,385,512,3073,4096,96,8450,16386,32768,196672,786440,3145736,4195336,8388928,96,50331712,67108864,3328,134235136]),([v202,v3,v2,v5,v6,v23,v40],[5,3,28,9,73,25,17,116,20,24,45,37,33,21,177,89,53,201,65,61,81,29,213],[7,24,96,128,768,1024,25,96,6145,8192,49153,196672,786448,24,24,1052736,96,96,2097152,4231168,33536]),([v3,v2,v5,v6,v223,v23,v40],[5,9,1,17,25,37,33,105,13,41,53,57,65,61,73,221,81,49,149,28,116,29,36,24,45,20],[7,24,97,129,256,641,3088,12290,1026,16386,33282,65616,131088,24,262672,1572928,2097152,4194880,8388608,16777216,37749248]),([v224,v3,v2,v5,v6,v23,v40],[3,9,73,25,17,36,24,41,5,37,33,13,45,89,53,201,65,61,81,29,20],[1,6,24,32,64,128,262,24,1792,2048,12544,49168,196612,6,6,263184,24,24,524288,13312,1052704]),([v3,v2,v5,v6,v23,v40],[1,5,9,32,28,17,105,25,16,37,124,33,13,41,45,49,53,57,61,65,4,73,8,69,77,81,0,85,120,29,89,36,20,24],[31,226,3842,4352,24642,229508,788485,7340036,27279364,33851520,67110048,142622880,805307392,3221244160,12884926464]),([v3,v225,v5,v6,v40],[8,1,5,9,13,136,140,17,101,25,241,28,29,33,37,41,20,77,245,49,53,57,61,65,89,73,69,81,93,97],[63,2000,30740,491856,3670600,12591115,117637128,138945088,164544,822288384]),([v144,v3,v5,v6,v40],[76,5,1,4,13,9,144,49,53,25,57,61,33,65,20,69,41,73,77,17,105,237,28,29,37,109,145,129,149,89,93,97],[63,2016,14380,507936,3670608,29364242,33669200,75502272,403243584,3758182400]),([v161,v3,v2,v6,v40],[148,21,17,132,13,25,56,53,49,152,9,57,33,61,81,20,45,41,85,28,1,5,29,3,89,73,113],[63,4064,29536,491564,3671056,6823952,229402,13640704,50496512,84058112]),([v3,v2,v5,v6,v162,v40],[1,5,9,13,17,105,25,237,28,24,16,21,41,177,20,49,53,57,3,4,8,89,73,156,0,149,33,45],[15,248,266,3594,28968,229444,262149,1572869,6295556,8421440,25198656,41947216,67125248,2117632,136335360]),([v3,v2,v5,v162,v40],[28,1,5,9,13,156,17,157,25,237,29,33,37,116,41,20,177,49,53,57,3,61,65,89,73,81,149,93,97,45],[31,1008,15381,114865,917800,7342090,25214984,35784992,67125600,947963904]),([v145,v3,v2,v5,v40],[160,13,29,16,5,33,37,9,61,1,65,164,25,49,81,20,45,89,93,97,28,233,165,21,177,53,161,225,229],[127,1960,31008,1015840,1049234,6305808,25397264,100678144,168002048,268646400]),([v77,v3,v33,v2,v5,v6,v40],[21,20,3,16,9,8,4,25,168,61,45,13,28,5,73,17,237,113,177,41,1,132,33,24,49,57,65,89,81,121,149],[1,14,112,388,524,1024,6148,24592,98432,133632,788480,1048576,2097284,4194304,8912898,50331776,67109392,134742032,805306496,1074266240,134742528]),([v77,v3,v2,v5,v6,v24,v40],[21,1,8,4,25,180,3,33,16,20,45,5,13,17,237,37,29,28,177,41,53,49,65,9,89,145,132,149,61,97,24],[1,14,112,448,580,1024,6146,24592,102400,135232,790528,3145744,4194434,8388608,17301506,33554576,67108944,134742032,268435456,537395328,1074266624]),([v21,v77,v3,v2,v5,v6,v40],[20,32,4,5,13,9,49,25,33,89,41,21,1,8,184,3,61,16,45,17,237,113,177,53,249,81,121,149],[7,24,32,192,256,1536,2048,12292,49280,229376,262144,24,1572992,2162704,4195344,8388800,16846848,5632,100663424,134218880,67072]),([v67,v77,v3,v2,v5,v6,v40],[20,3,16,13,5,1,25,49,61,41,89,105,9,8,4,188,33,45,73,165,233,177,57,249,229],[7,24,32,192,256,1536,2048,28672,32898,65542,131072,266256,1572992,24,2098192,4194496,8458240,5632,192,16778304,67072]),([v3,v33,v2,v5,v6,v40,v194],[21,3,28,109,9,73,25,17,61,113,177,45,13,1,192,33,24,20,16,49,57,65,77,69,4,8,81,121,85,168,41],[7,56,193,769,3073,4096,8192,16450,32768,198656,327682,1572928,2097424,12582928,50331664,201326656,268437568,536870978,2816,262402,1073741824]),([v3,v2,v5,v6,v24,v40,v194],[1,21,109,25,17,29,33,177,45,13,53,49,65,9,69,145,3,192,85,180,61,93,24,8,41],[7,26,98,6,386,512,3080,4161,8192,16640,1025,32840,196616,262408,589832,1048576,2097472,96,16640,12648448,16777216]),([v21,v3,v2,v5,v6,v40,v194],[109,21,9,49,25,33,69,45,4,24,32,1,17,61,113,177,13,53,249,81,121,3,184,16,41],[3,4,24,32,192,1792,2051,4114,24578,32898,65536,131096,272384,192,133120,1572880,4240,6291472,24704,10493952,16777216]),([v67,v3,v2,v5,v6,v40,v194],[21,105,1,25,49,61,45,24,20,16,3,9,73,29,177,5,57,33,249,77,69,4,8,188,93,89],[3,4,24,32,448,1664,6146,26,8195,16450,32768,65560,395264,1574912,6293504,24,24,8389648,16908352,139264,33554432]),([v3,v2,v169,v6,v40],[196,73,109,36,9,21,192,17,25,200,93,33,105,37,233,45,24,277,56,49,53,3,57,61,65,69,77,81,85,97],[63,996,15401,246369,8126736,28313616,100762130,145492224,302088640,539069952]),([v202,v3,v2,v5,v6,v194],[177,20,21,45,28,9,69,73,77,25,17,85,24,93,41,109,101,185,29,33,13,49,53,201,61,1,65,89,204,81,208,3,229,16],[31,488,3656,12290,20482,98468,165380,786437,1048578,14681216,117964928,436211840,556270592,7650415616,8724942848]),([v170,v3,v2,v5,v6,v40],[5,16,21,20,13,1,4,9,8,49,212,25,0,24,33,89,45,41,73,109,17,29,36,53,57,3,293,69,77,189,145,85],[31,480,7680,24576,237576,786564,1574916,6291461,98309,25168512,102760608,402980992,1612712448,2282817536,2203648]),([v3,v2,v5,v6,v226,v40],[1,5,9,21,17,25,28,37,33,20,16,13,41,24,197,49,53,57,61,65,4,73,8,89,81,220,0,149,29,213,45],[15,58,458,3594,28746,229412,786693,7340036,10489860,17072416,100663344,167776304,268443648,545272064,1082143232]),([v86,v3,v33,v2,v5,v6,v40],[13,24,3,16,73,9,17,25,113,61,45,21,28,109,41,197,1,216,33,20,49,57,65,89,81,121,149],[1,14,48,192,768,1024,6148,8240,2240,2816,51200,65536,131204,262144,540674,3145856,4194848,8405024,50331776,67125376,8405504]),([v86,v3,v2,v5,v6,v24,v40],[13,1,8,4,17,25,29,33,24,3,45,21,109,41,197,53,49,65,9,89,145,216,149,61,97,20],[1,14,48,192,772,1024,6146,2096,192,6144,26624,98336,131202,262144,532482,1048736,2097696,4202528,8388608,16785536,33562880]),([v86,v21,v3,v2,v5,v6,v40],[24,32,4,13,1,8,17,25,113,61,45,109,21,9,49,33,89,41,197,53,249,81,121,149],[7,8,52,192,768,1024,6144,8192,16512,32768,196608,6160,4288,4864,397312,540800,1049104,196624,6291584,8519808,197120]),([v86,v67,v3,v2,v5,v6,v40],[24,3,16,5,73,9,49,25,29,33,45,21,105,1,61,41,89,309,57,249,229],[7,8,48,192,768,1024,6144,8192,192,16384,98304,4144,4288,4864,200704,262336,524832,98336,704,1114240,98816]),([v59,v3,v33,v2,v5,v6,v40],[21,20,36,16,9,73,25,17,61,113,41,13,3,28,5,237,45,197,53,224,93,24,49,201,65,317],[1,14,48,192,768,1024,14336,16432,32960,2816,198656,262144,528512,1048576,2162690,12583040,16777760,48,33555072,192,66304]),([v59,v3,v2,v5,v6,v24,v40],[21,1,53,25,17,33,93,20,8,36,41,13,5,237,37,28,3,45,197,49,65,73,69,224,113],[1,6,24,96,896,1024,6148,8216,18496,100352,395264,524308,1048644,2097152,4325380,524368,8454160,24,16777216,96,4325376]),([v21,v59,v3,v2,v5,v6,v40],[20,32,4,5,13,73,49,17,93,69,45,21,1,53,25,61,113,41,237,197,205,317],[7,24,32,192,256,1536,2048,12288,16512,98304,131072,8216,278656,98320,525328,8384,1122304,9728,2162816,16512,99328]),([v67,v59,v3,v2,v5,v6,v40],[20,36,16,13,5,53,17,49,113,45,24,105,9,73,25,33,93,89,165,233,309,201,205],[7,24,32,192,256,1537,2048,12288,16512,98304,131072,12304,786560,65560,1049104,2097344,4268032,12288,192,16512,98304]),([v3,v2,v147,v5,v6,v40],[73,4,9,16,13,17,172,25,113,37,33,41,3,45,1,49,57,61,65,69,77,0,29,20,24,81,85,89],[7,24,224,1800,14336,16391,98500,394252,1581061,2097376,4195592,25176064,33719424,67641504,134227200]),([v2,v147,v5,v6,v40],[4,5,73,13,9,1,172,49,25,57,61,16,37,65,69,45,77,17,21,113,29,3,41,81,89],[63,976,15440,114709,393544,1579018,6586376,8394176,4358464,17340416]),([v227,v2,v5,v6,v40],[4,1,5,9,13,228,17,21,25,16,29,61,37,28,41,45,49,53,57,65,69,73,77,121,81,85,89,93,97],[31,496,7700,57488,459048,527914,7372809,25233696,34636128,469797376]),([v163,v3,v2,v6,v40],[56,21,17,100,13,25,4,53,49,168,9,57,16,33,61,81,45,69,85,73,5,113,3,41,109,65,89],[63,4064,62240,458797,1573968,3166224,29491216,33584768,9045056,69357568]),([v3,v2,v5,v6,v228],[4,73,5,9,13,232,17,21,25,16,97,61,24,41,45,49,225,57,65,69,77,121,81,85,89,33],[31,496,3604,28816,229672,331304,1593354,6326560,8929632,50355200]),([v229,v3,v2,v5,v6],[20,13,41,21,45,9,69,73,77,236,25,17,85,33,113,89,97,4,109,101,185,16,105,157,49,281,201,1,65,317],[31,497,7760,122897,917672,1314312,14704648,117443200,404775552,553675264]),([v164,v3,v2,v5,v6,v40],[8,13,9,4,1,16,25,240,17,0,33,29,45,20,41,24,109,173,32,3,49,53,161,61,89,93,145,149,97],[3,60,960,3112,61440,65557,196928,330752,610304,7340304,8390676,18890768,101714176,134238528,318785536]),([v3,v2,v165,v6,v40],[80,1,5,8,13,3,56,17,21,25,84,29,32,33,37,41,45,180,49,53,57,121,65,137,129,77,141,145,89,93,97],[63,1008,31764,98608,1967618,14820355,118030347,134621697,99040,1879127040]),([v3,v230,v2,v5,v6,v40],[16,13,73,5,9,8,117,49,105,25,29,157,33,89,45,4,1,17,244,0,41,20,24,57,61,65,69,77,81,85,93],[3,124,904,7177,24840,98356,918016,5121,7356416,8651408,50335761,201342996,285217408,603996800,1073770496]),([v3,v2,v182,v5,v6,v40],[1,4,101,9,21,20,13,17,25,252,93,33,3,36,89,45,24,49,281,57,61,65,69,77,0,29,16,41,81,85],[31,96,912,15376,49200,65547,917768,3147785,12615720,16909056,100669440,134266912,269617408,541098368,52224]),([v3,v2,v5,v6,v183,v40],[1,5,9,13,17,21,25,93,3,32,28,89,69,49,53,57,4,24,16,77,20,256,0,129,85,33,97,45],[15,120,906,1320,6184,57412,65669,393221,1658884,2105536,6291536,25170000,34603008,68163712,135272448]),([v3,v2,v231,v6,v40],[264,73,109,8,13,36,56,17,21,25,32,29,33,105,37,268,41,24,45,260,49,53,57,121,65,137,129,281,77,141,145,93,97],[63,1008,31760,491792,7897602,60821515,1007583234,1074798144,983680,6442882048]),([v3,v2,v5,v6,v232,v40],[1,5,32,13,4,17,21,25,237,29,33,37,28,36,89,69,49,53,73,65,20,16,9,24,333,145,276,0,129,85,61,213,45],[31,488,3594,12360,49224,196737,787473,7602177,25460753,33621632,201326752,805339296,1082130432,2155922432,4304453632]),([v3,v233,v2,v5,v6,v40],[20,13,1,109,9,8,181,49,105,25,113,33,41,177,45,4,24,17,284,0,29,16,32,281,57,61,65,69,77,81,85],[3,124,904,3336,28681,98324,918016,7342080,20481,25166480,100665364,402669585,570428032,1207976576,4213761]),([v3,v2,v5,v6,v234,v40],[1,105,9,32,17,25,292,29,16,33,20,13,41,45,49,53,57,61,65,4,8,69,73,77,81,0,85,24,97],[15,114,898,3072,13314,114724,393733,1572869,14688260,16925216,33554544,69214256,134218624,268445440,13312]),([v3,v2,v133,v6,v40],[32,73,109,9,13,56,17,21,100,25,16,93,33,105,37,304,41,24,45,49,53,57,121,65,69,77,300,113,81,85,97],[31,1008,31760,491664,3670824,13636616,50757642,470323712,621150784,1141283840]),([v3,v186,v2,v5,v6,v40],[20,13,73,109,9,21,17,25,29,33,3,36,217,89,45,1,4,8,49,312,0,16,24,41,53,57,61,65,69,77,81,85],[3,60,232,7968,24609,229392,1835136,6292224,8413185,50593936,201359888,805322772,1141113472,2415935680,25089])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x1 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x2 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x3 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x4 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x5 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x6 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC6x7 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (7*8)).take 8) = true := by decide +kernel
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := levelStep ptopB ptopW ptopI5 (chunks 8 ptopD6 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  · exact ptopC6x1
  · exact ptopC6x2
  · exact ptopC6x3
  · exact ptopC6x4
  · exact ptopC6x5
  · exact ptopC6x6
  · exact ptopC6x7
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD7 : List StD := [([v7,v3,v2,v5,v6,v40],[4,8,13,9,12,17,25,0,61,16,33,3,69,20,45,24,28,101,1,5,105,29,109,41,49,53,73,81,85,32,36,89,93,97],[7,9,240,3841,61441,983041,1572976,6882304,13189120,50593872,67372289,67391489,150996304,268456048,16643015680]),([v3,v2,v22,v5,v6,v40],[4,28,101,8,13,9,5,44,17,21,25,29,32,33,37,41,36,45,1,49,57,61,65,69,77,0,113,16,89,20,24,81,85,93,97],[63,65,1936,30738,229906,262152,1574048,6303785,25362473,34079872,201338888,1879179272,2150114432,4303488384,26038382592]),([v19,v3,v2,v5,v6,v40],[4,5,8,9,48,25,0,3,33,16,61,32,45,20,69,24,1,13,28,117,17,21,29,41,49,53,73,121,81,125,129,85,133,89,93,97],[3,12,244,3844,61444,983045,3276848,4590592,10895360,50397232,67175685,67194885,956302384,7517257776,60129561600]),([v20,v3,v2,v5,v6,v40],[4,8,13,1,60,25,17,0,33,16,29,3,45,20,41,24,5,9,28,117,105,109,32,36,49,57,61,69,93,145,149,89,97],[7,9,240,3841,61441,983041,1114224,6622464,10833920,50462800,67243009,142753793,822084688,1073762416,6723488768]),([v139,v3,v2,v5,v6,v40],[16,28,5,9,8,3,4,88,25,0,33,45,20,24,1,109,13,17,21,37,29,41,49,53,57,113,32,69,73,77,93,145,85,89,97],[7,121,929,1025,14369,114698,459136,1638403,2426882,29360520,34619401,1006635016,3226468736,4429318528,26844596225]),([v3,v2,v5,v6,v23,v40],[28,1,5,32,9,3,112,17,105,25,16,37,33,13,41,36,45,49,53,57,61,65,4,73,8,69,77,81,0,85,29,89,20,24],[63,964,7173,9216,114949,918096,3150874,29360184,109150264,135402048,268436160,570491584,1073741825,2147587104,12885016608]),([v9,v3,v2,v5,v6,v40],[16,13,28,1,4,9,8,120,17,25,0,3,33,41,20,45,24,5,32,105,29,153,49,53,57,113,36,69,73,77,93,145,85,89,97],[3,124,1920,6148,122884,393260,656256,3276805,696324,29360800,34865193,1006927904,3226468992,4429218688,26911735809]),([v34,v3,v2,v5,v6,v40],[16,3,5,9,1,8,4,128,25,49,0,29,45,20,89,24,28,109,32,13,21,33,153,36,53,161,61,225,229],[7,121,1920,2049,61441,983064,1573760,6881281,10047488,50332560,69206041,151277584,69206912,268456832,10506241]),([v77,v3,v2,v5,v6,v40],[20,24,21,9,8,3,4,132,25,0,33,16,45,28,1,5,13,17,233,237,29,37,177,41,49,53,57,61,65,89,73,81,149,93,97],[7,121,929,3105,4097,122888,983424,3253248,12656641,117440904,402670632,1619001353,2298480000,4303487360,26315064321]),([v3,v2,v5,v6,v40,v194],[28,1,109,36,9,21,192,17,25,29,33,105,20,177,24,45,13,49,53,57,3,61,65,69,73,77,4,8,81,85,0,93,16,41],[63,484,3625,61473,69632,917840,7341074,58773520,201342994,270665024,545292736,1074807104,2148586496,4296033792,8589950976]),([v86,v3,v2,v5,v6,v40],[20,13,24,1,9,8,4,216,17,25,0,29,33,3,16,45,28,109,21,105,41,197,49,53,57,61,65,89,73,81,149,93,97],[3,124,1920,30724,32772,458776,394112,858112,3473413,29360784,100675608,403701781,574624384,1074791296,6577721349]),([v59,v3,v2,v5,v6,v40],[20,24,21,9,73,8,4,224,25,17,0,33,93,36,16,41,28,5,13,233,237,37,45,197,49,53,3,113,69],[7,121,1920,30721,32769,466968,1835904,2570240,12910593,50332304,234885136,272629785,150999680,272630656,4208641]),([v3,v33,v2,v5,v6,v40],[16,13,3,28,4,73,5,9,168,17,21,25,113,61,41,45,1,0,33,20,24,49,57,65,69,77,121,81,85,89],[15,242,3842,12355,50182,65553,133381,262145,1605637,6293888,8396945,50364592,203434240,285248256,536915969]),([v3,v2,v5,v6,v24,v40],[4,1,5,8,13,3,180,17,21,25,16,29,32,33,37,28,109,41,45,49,53,65,9,69,145,0,85,61,89,93,97,20,24],[63,976,31764,98360,393520,1573442,2106371,4195328,9699339,17312320,33555048,75760320,134217729,1879323648,6451101704]),([v21,v3,v2,v5,v6,v40],[4,5,13,32,28,16,9,184,49,25,0,8,33,69,20,45,24,1,17,21,113,61,3,41,53,249,121,81,89],[31,96,1920,6145,122881,131087,787076,3145774,13139972,16909184,35782689,16949249,203424640,8684160,271613992]),([v67,v3,v2,v5,v6,v40],[16,13,5,3,28,8,1,188,25,49,0,61,45,20,89,24,4,73,9,105,165,29,33,177,57,249,77,229,93],[31,97,1920,2049,61441,458790,1573764,6291463,8933388,17040256,38076417,67588128,6292352,134239104,272650241]),([v3,v69,v2,v5,v6,v40],[20,13,3,21,28,4,1,5,9,248,17,25,32,93,33,37,36,89,69,24,73,0,16,45,49,281,57,61,65,77,81,129,85],[31,488,3594,127116,393227,1572865,2100736,4218885,8388609,117443328,402669920,537133345,1224755712,6442716672,417793]),([v3,v2,v5,v6,v40,v235],[4,73,5,8,13,36,260,17,21,25,32,29,33,37,20,41,24,45,28,49,53,61,77,9,81,3,0,93,97,16,69],[63,976,15380,246032,327732,1573442,3149835,4407299,8404992,19403328,164544,100729408,402871296,539038720,1073807360]),([v236,v3,v2,v5,v6,v40],[24,21,13,36,28,20,9,272,17,25,0,61,33,3,16,45,4,73,5,237,32,29,37,89,69,49,53,333,145,129,85,93],[31,96,1920,30721,32769,458764,525190,7606284,25165863,100795008,67311616,151191585,304091776,1627390848,2172653601]),([v68,v3,v2,v5,v6,v40],[20,13,109,3,28,24,73,280,25,49,0,33,113,32,16,69,4,1,8,9,105,185,157,41,45,281,57,65,333,317],[31,97,1920,30721,32769,983046,3146628,5257220,25165831,101188480,135206912,285802497,536877952,25166720,16791553]),([v3,v2,v5,v57,v6,v40],[32,1,5,9,13,288,17,21,25,20,3,105,28,16,29,33,37,41,45,49,53,57,8,4,61,65,69,73,77,0,81,85,24,93,89,97],[31,496,7696,122900,393872,3670312,13632008,50372618,470024712,537395488,1091076384,2214855008,12884902400,17179869696,34360041984]),([v3,v2,v5,v6,v40,v237],[36,1,5,32,9,13,296,17,21,25,16,93,20,89,24,28,49,53,57,113,73,4,8,0,97,33,45],[63,992,3109,28961,49441,459344,527386,1077272,6307858,592448,8896,8389312,16808960,33558528,67125248]),([v238,v3,v2,v5,v6,v40],[24,13,5,36,28,9,1,8,4,300,25,0,3,20,33,89,32,17,233,165,337,16,93,41,45,21,49,281,161,341,113,69,73,77,85,213],[31,481,7681,24576,32769,65638,1967620,6291470,58728453,1006634560,1080033376,15049171009,1145046528,19344262656,34382815233]),([v202,v3,v2,v5,v6,v40],[20,13,21,3,28,9,73,8,4,308,25,17,0,24,93,45,36,109,32,101,185,16,29,33,5,37,89,49,53,201,61,1,65,81,213],[31,481,7680,24577,32769,983148,1183236,65077260,67108879,939526720,7526940736,67371105,9806285312,67112448,17257463809])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x2 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (2*8)).take 8) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 8 ptopD7 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  · exact ptopC7x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD8 : List StD := [([v3,v2,v5,v6,v40],[3,1,5,9,13,0,17,21,25,29,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93,97],[31,496,3605,12433,114984,394251,3678217,4343072,8921440,117449729])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 8 ptopD8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  ))
theorem ptopL : LowN true ptopR ptopT 9 := lowSearch ptopB ptopI8 (by decide +kernel)
end Aux4
namespace Aux6
def ptopT : Nat := v239
def ptopR : List Nat := [0,1,2,3,4]
def ptopE : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,3,19)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(v40,7,[0,1,2,3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) ptopB Lib12108.p7_B Lib12108.p7_L (by decide +kernel), fun _ h => by cases h⟩
def ptopC : List (Nat × List Nat) := [(0,[128]),(0,[129]),(0,[130]),(0,[131]),(0,[256]),(0,[257]),(0,[258]),(0,[259]),(0,[384]),(0,[385]),(0,[386]),(0,[387]),(0,[]),(0,[260]),(0,[261]),(0,[262]),(0,[263]),(0,[388]),(0,[389]),(0,[390]),(0,[391]),(0,[392]),(0,[393]),(0,[394]),(0,[395])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(14,12),(13,12),(19,17),(19,18),(22,18),(7,3),(6,3),(26,18),(11,3),(10,3),(28,12),(19,3),(19,2),(21,17),(5,3),(25,17),(9,3),(19,1),(28,20),(28,24),(5,17),(9,17)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptopD6 : List StD := []
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD7 : List StD := [([v3,v2,v5,v6,v40],[0,1,5,4,9,13,8,12,16,17,20,21,25,24,28,32,29,36,33,37,40,44,48,41,45,49,52,53,56,57,60,64,68,61,72,65,76,80,69,84,88,73,77,92,96,81,85],[255,32548,4161572,62914596,4227860498,270583201810,274907267090,34634616539136,35184535668736,70377363734528])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 8 ptopD7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  ))
theorem ptopL : LowN true ptopR ptopT 8 := lowSearch ptopB ptopI7 (by decide +kernel)
end Aux6
def ptopT : Nat := v240
def ptopR : List Nat := [0,1,2,3,4,5]
def ptopE : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,5,21),(5,3,35)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(v241,9,[0,1,2,3,4]),(v41,9,[0,5,1,2,3]),(v5,9,[0,1,3,4,5]),(v6,9,[0,1,2,4,5]),(v242,8,[4,0,1,2,3]),(v0,8,[0,2,3,4,5]),(v1,8,[1,4,2,3,5]),(v2,8,[0,2,3,4,5]),(v40,8,[0,1,2,3,5]),(v243,7,[0,1,2,3]),(v55,7,[0,1,4,5]),(v244,7,[1,2,3,4]),(v3,7,[1,2,3,4,5]),(v245,6,[0,1,2,3]),(v86,6,[5,1,2,3]),(v246,5,[4,0,1,2]),(v247,5,[0,1,2,4]),(v248,5,[0,1,2,4]),(v238,5,[0,5,1,2]),(v202,5,[2,0,1,5]),(v249,5,[4,0,1,3]),(v250,5,[0,1,3,4]),(v251,5,[0,1,3,4]),(v87,5,[0,5,1,3]),(v252,5,[3,0,1,5]),(v253,5,[4,2,3,0]),(v254,5,[0,2,3,4]),(v255,5,[0,2,3,4]),(v67,5,[0,4,5,2]),(v33,5,[4,0,2,5]),(v10,5,[0,4,5,3]),(v16,5,[4,0,3,5]),(v256,5,[4,2,3,1]),(v34,5,[1,4,2,5]),(v31,5,[1,4,3,5]),(v20,5,[4,2,3,5]),(v7,5,[5,2,3,4]),(v159,4,[0,4,1,5]),(v257,4,[0,4,1,5]),(v9,4,[2,5,1,4]),(v8,4,[3,5,1,4]),(v258,4,[0,2,5]),(v259,4,[0,3,5]),(v260,4,[1,2,4]),(v261,4,[1,3,4]),(v64,4,[1,4,5]),(v262,4,[2,3,4])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=32) ptopB Lib12108.p13_B Lib12108.p13_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12142.p16_B Lib12142.p16_L (by decide +kernel),mkSlice (w:=4) ptopB Aux4.ptopB Aux4.ptopL (by decide +kernel),mkSlice (w:=8) ptopB Aux4.ptopB Aux4.ptopL (by decide +kernel),mkSlice (w:=0) ptopB Lib12142.p18_B Lib12142.p18_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12142.p18_B Lib12142.p18_L (by decide +kernel),mkSlice (w:=0) ptopB Lib12108.p17_B Lib12108.p17_L (by decide +kernel),mkSlice (w:=2) ptopB Aux3.ptopB Aux3.ptopL (by decide +kernel),mkSlice (w:=16) ptopB Aux6.ptopB Aux6.ptopL (by decide +kernel),mkSlice (w:=48) ptopB Lib12108.p7_B Lib12108.p7_L (by decide +kernel),mkSlice (w:=12) ptopB Lib12108.p7_B Lib12108.p7_L (by decide +kernel),mkSlice (w:=32) ptopB Lib12108.p5_B Lib12108.p5_L (by decide +kernel),mkSlice (w:=1) ptopB Aux1.ptopB Aux1.ptopL (by decide +kernel),mkSlice (w:=32) ptopB Lib12108.p12_B Lib12108.p12_L (by decide +kernel),mkSlice (w:=1) ptopB Lib12108.p12_B Lib12108.p12_L (by decide +kernel),mkSlice (w:=8) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=32) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=40) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=8) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=16) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=32) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=36) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=16) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=32) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=34) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=8) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=10) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=6) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=1) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=8) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=4) ptopB Lib12108.p18_B Lib12108.p18_L (by decide +kernel),mkSlice (w:=2) ptopB Lib12108.p8_B Lib12108.p8_L (by decide +kernel),mkSlice (w:=3) ptopB Lib12108.p9_B Lib12108.p9_L (by decide +kernel),mkSlice (w:=4) ptopB Lib15811.p14_B Lib15811.p14_L (by decide +kernel),mkSlice (w:=8) ptopB Lib15811.p14_B Lib15811.p14_L (by decide +kernel),mkSlice (w:=1) ptopB Lib15811.p14_B Lib15811.p14_L (by decide +kernel),mkSlice (w:=1) ptopB Lib15811.p14_B Lib15811.p14_L (by decide +kernel),mkSlice (w:=10) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=6) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=40) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=36) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=12) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel),mkSlice (w:=3) ptopB Lib12108.p3_B Lib12108.p3_L (by decide +kernel), fun _ h => by cases h⟩
def ptopC : List (Nat × List Nat) := [(2,[]),(3,[]),(1,[]),(0,[]),(5,[]),(6,[]),(2,[128]),(3,[128]),(1,[256]),(8,[]),(4,[]),(0,[128]),(11,[]),(21,[]),(3,[128,279]),(30,[]),(1,[256,407]),(24,[]),(0,[128,279]),(6,[392]),(5,[260]),(2,[128,279]),(16,[]),(1,[256,407,536]),(11,[260]),(0,[128,279,408]),(2,[128,276]),(6,[395]),(5,[263]),(1,[256,407,539]),(11,[263]),(0,[128,279,411]),(28,[]),(1,[256,535]),(19,[]),(0,[128,407]),(3,[128,276]),(6,[271]),(5,[139]),(1,[256,535,411]),(11,[139]),(0,[128,407,283]),(10,[]),(10,[128]),(1,[256,524]),(1,[524]),(8,[392]),(4,[524]),(0,[128,392]),(0,[392]),(8,[128]),(4,[260]),(5,[390]),(6,[138]),(3,[128,394]),(0,[128,522]),(3,[394]),(4,[14]),(0,[522]),(9,[128]),(1,[256,653]),(2,[128,654]),(23,[]),(3,[128,394,665]),(0,[128,522,665]),(5,[390,279]),(6,[138,407]),(2,[128,268]),(2,[268]),(38,[]),(36,[]),(1,[527]),(1,[256,527]),(4,[14,535]),(0,[522,407]),(5,[394]),(6,[142]),(2,[128,394]),(0,[128,526]),(2,[394]),(4,[18]),(0,[526]),(18,[]),(2,[128,394,665]),(1,[256,657]),(3,[128,654]),(0,[128,526,665]),(5,[394,151]),(6,[142,279]),(37,[]),(3,[128,268]),(3,[268]),(1,[403]),(1,[256,403]),(4,[18,407]),(0,[526,279]),(2,[129]),(12,[]),(3,[129]),(1,[257]),(0,[129]),(7,[]),(5,[128]),(6,[256]),(3,[129,276]),(1,[257,404]),(0,[129,276]),(11,[128]),(31,[]),(5,[128,276]),(2,[129,276]),(6,[256,404]),(10,[129]),(1,[257,404,536]),(12,[260]),(0,[129,276,408]),(11,[128,272]),(7,[260]),(2,[129,279]),(12,[263]),(7,[263]),(1,[257,404,539]),(0,[129,276,411]),(5,[128,279]),(6,[256,407]),(11,[128,275]),(5,[128,260]),(6,[256,392]),(1,[257,404,524]),(0,[129,276,392]),(11,[128,260]),(4,[261,404]),(5,[128,516]),(6,[256,520]),(3,[129,276,520]),(1,[257,404,140]),(9,[129,272]),(7,[516]),(11,[128,263]),(0,[129,276,395]),(2,[520]),(2,[129,520]),(5,[520]),(6,[524]),(7,[520]),(17,[]),(1,[144]),(8,[524]),(1,[257,404,144]),(8,[129,276]),(5,[256]),(6,[384]),(1,[257,532]),(0,[129,404]),(11,[256]),(29,[]),(3,[129,279]),(12,[139]),(7,[139]),(1,[257,532,411]),(0,[129,404,283]),(5,[256,151]),(6,[384,279]),(11,[256,147]),(5,[256,260]),(6,[384,392]),(1,[257,532,524]),(0,[129,404,392]),(11,[256,260]),(4,[261,532]),(3,[520]),(3,[129,520]),(5,[516]),(6,[520]),(22,[]),(1,[140]),(8,[520]),(8,[129,404]),(1,[257,532,140]),(5,[256,520]),(6,[384,524]),(2,[129,276,520]),(1,[257,532,144]),(9,[129,400]),(11,[256,262]),(0,[129,404,394]),(1,[257,524]),(0,[129,392]),(8,[129]),(4,[261]),(13,[392]),(13,[129]),(7,[527]),(10,[395]),(2,[527]),(3,[527]),(2,[129,527]),(7,[390]),(3,[129,394]),(42,[]),(0,[129,522]),(12,[390]),(9,[129]),(5,[390,23]),(1,[257,655]),(6,[138,23]),(2,[129,652]),(3,[129,394,667]),(0,[129,522,667]),(1,[257,140]),(5,[516,642]),(6,[520,642]),(0,[129,278]),(2,[129,534]),(3,[129,520,790]),(1,[257,140,790]),(9,[129,274]),(11,[130]),(7,[516,279]),(15,[]),(0,[129,395]),(6,[520,407]),(5,[516,279]),(2,[129,275]),(2,[275]),(1,[140,535]),(8,[520,407]),(0,[395]),(7,[394]),(2,[129,394]),(41,[]),(0,[129,526]),(12,[394]),(5,[394,23]),(1,[257,659]),(6,[142,23]),(2,[129,394,667]),(3,[129,652]),(0,[129,526,667]),(1,[257,144]),(5,[520,642]),(6,[524,642]),(2,[129,520,790]),(0,[129,406]),(3,[129,534]),(1,[257,144,790]),(9,[129,402]),(11,[258]),(11,[262]),(7,[520,646]),(20,[]),(0,[129,394]),(6,[524,650]),(5,[520,646]),(3,[129,522]),(3,[522]),(1,[144,654]),(8,[524,650]),(0,[394]),(13,[]),(3,[129,527]),(5,[527]),(6,[519]),(6,[519,279]),(5,[527,151]),(11,[140]),(7,[527,151]),(3,[527,279]),(1,[257,391]),(1,[391]),(0,[129,272]),(0,[272]),(39,[]),(6,[519,407]),(5,[527,279]),(11,[268]),(2,[527,279]),(7,[527,279]),(1,[257,519]),(1,[519]),(0,[129,400]),(0,[400]),(40,[]),(2,[130]),(3,[130]),(1,[258]),(0,[130]),(5,[131]),(3,[130,279]),(1,[258,407]),(0,[130,279]),(5,[131,276]),(2,[130,279]),(1,[258,407,536]),(0,[130,279,408]),(2,[130,276]),(1,[258,407,539]),(0,[130,279,411]),(5,[131,279]),(5,[259]),(1,[258,535]),(0,[130,407]),(3,[130,276]),(1,[258,535,411]),(0,[130,407,283]),(5,[259,151]),(10,[130]),(1,[258,524]),(0,[130,392]),(8,[130]),(4,[262]),(3,[130,394]),(0,[130,522]),(9,[130]),(5,[390,21]),(1,[258,653]),(2,[130,654]),(3,[130,394,665]),(0,[130,522,665]),(2,[130,394]),(0,[130,526]),(5,[394,21]),(2,[130,394,665]),(1,[258,657]),(3,[130,654]),(0,[130,526,665]),(2,[131]),(3,[131]),(1,[259]),(0,[131]),(7,[128]),(6,[259]),(3,[131,279]),(1,[259,407]),(0,[131,279]),(11,[131]),(6,[259,404]),(10,[131]),(7,[128,276]),(2,[131,279]),(1,[259,407,536]),(0,[131,279,408]),(11,[131,272]),(2,[131,276]),(1,[259,407,539]),(0,[131,279,411]),(6,[259,407]),(11,[131,275]),(2,[131,520]),(4,[263,407]),(8,[131,279]),(7,[256]),(6,[387]),(1,[259,535]),(0,[131,407]),(11,[259]),(3,[131,276]),(1,[259,535,411]),(0,[131,407,283]),(6,[387,279]),(11,[259,147]),(3,[131,520]),(4,[263,535]),(8,[131,407]),(1,[259,524]),(0,[131,392]),(8,[131]),(4,[263]),(13,[131]),(2,[131,527]),(3,[131,394]),(0,[131,522]),(9,[131]),(6,[138,21]),(7,[390,23]),(1,[259,653]),(2,[131,654]),(3,[131,394,665]),(0,[131,522,665]),(7,[390,279]),(2,[131,268]),(35,[]),(1,[259,527]),(1,[259,140]),(0,[131,277]),(2,[131,533]),(7,[516,642]),(6,[520,641]),(3,[131,520,789]),(11,[129]),(1,[259,140,789]),(9,[131,273]),(0,[131,395]),(2,[131,275]),(2,[131,394]),(0,[131,526]),(6,[142,21]),(7,[394,23]),(2,[131,394,665]),(1,[259,657]),(3,[131,654]),(0,[131,526,665]),(7,[394,151]),(3,[131,268]),(1,[259,403]),(1,[259,144]),(0,[131,405]),(6,[524,641]),(2,[131,520,789]),(11,[257]),(3,[131,533]),(7,[520,642]),(1,[259,144,789]),(9,[131,401]),(0,[131,394]),(3,[131,522]),(3,[131,527]),(1,[259,391]),(0,[131,272]),(1,[259,519]),(0,[131,400]),(3,[256]),(1,[384]),(0,[256]),(2,[259]),(33,[]),(1,[384,535]),(0,[256,407]),(2,[259,260]),(1,[384,535,520]),(0,[256,407,388]),(8,[256,407]),(2,[259,394]),(0,[256,407,526]),(9,[256,403]),(2,[260]),(1,[384,520]),(1,[520]),(8,[388]),(4,[520]),(0,[256,388]),(0,[388]),(8,[256]),(4,[388]),(2,[260,641]),(3,[256,149]),(1,[384,520,789]),(0,[256,388,789]),(2,[263]),(1,[384,523]),(0,[256,391]),(1,[523]),(8,[391]),(4,[523]),(0,[391]),(2,[263,21]),(5,[128,649]),(3,[256,646]),(1,[384,523,665]),(0,[256,391,665]),(2,[389]),(6,[129]),(3,[256,389]),(3,[389]),(4,[9]),(0,[256,517]),(0,[517]),(9,[256]),(2,[389,643]),(1,[384,279]),(5,[128,407]),(3,[256,389,791]),(0,[256,517,791]),(5,[128,388]),(6,[129,648]),(3,[256,389,776]),(3,[389,648]),(1,[384,268]),(4,[9,652]),(0,[256,517,776]),(2,[389,648]),(5,[392]),(6,[129,652]),(1,[272]),(1,[384,272]),(4,[9,656]),(0,[517,652]),(6,[130]),(2,[390]),(3,[256,390]),(0,[256,518]),(3,[390]),(4,[10]),(0,[518]),(2,[390,21]),(1,[384,649]),(3,[256,390,665]),(0,[256,518,665]),(2,[390,279]),(6,[130,407]),(7,[268]),(4,[10,535]),(0,[518,407]),(0,[256,526]),(2,[394,21]),(1,[384,657]),(3,[256,654]),(0,[256,526,665]),(3,[259]),(1,[387]),(14,[]),(0,[259]),(7,[131]),(6,[9]),(3,[259,149]),(34,[]),(1,[387,277]),(0,[259,149]),(25,[]),(11,[5]),(45,[]),(8,[259]),(4,[391]),(32,[]),(6,[11]),(3,[259,151]),(1,[387,279]),(0,[259,151]),(11,[7]),(1,[387,532]),(0,[259,404]),(2,[256]),(1,[387,535]),(0,[259,407]),(2,[256,149]),(3,[259,150]),(12,[9]),(7,[131,279]),(1,[387,535,281]),(0,[259,407,153]),(8,[259,407]),(4,[391,535]),(3,[259,148]),(2,[256,151]),(12,[11]),(1,[387,535,283]),(0,[259,407,155]),(2,[256,516]),(2,[516]),(3,[516]),(3,[259,516]),(27,[]),(12,[512]),(1,[136]),(8,[516]),(26,[]),(2,[256,519]),(3,[259,519]),(2,[519]),(3,[519]),(12,[515]),(1,[139]),(8,[519]),(2,[256,520]),(6,[395,524]),(1,[387,535,144]),(9,[259,403]),(2,[512]),(6,[523]),(3,[259,535]),(1,[387,151]),(9,[259]),(1,[387,520]),(14,[388]),(12,[256]),(0,[259,388]),(46,[]),(2,[260,642]),(1,[387,520,789]),(6,[384,649]),(0,[259,388,789]),(11,[256,517]),(1,[387,523]),(0,[259,391]),(14,[391]),(12,[259]),(6,[387,277]),(2,[263,23]),(5,[131,649]),(3,[259,646]),(1,[387,523,665]),(0,[259,391,665]),(11,[259,145]),(44,[]),(5,[131,139]),(3,[259,260]),(1,[387,523,411]),(1,[523,407]),(14,[391,275]),(12,[259,151]),(4,[523,407]),(0,[259,391,283]),(12,[385]),(3,[259,389]),(0,[259,517]),(2,[389,640]),(6,[129,651]),(5,[131,407]),(3,[259,389,791]),(0,[259,517,791]),(14,[140]),(1,[387,272]),(3,[259,390]),(0,[259,518]),(12,[386]),(2,[390,23]),(1,[387,649]),(3,[259,390,665]),(0,[259,518,665]),(6,[130,277]),(6,[512]),(1,[387,136]),(2,[516,642]),(6,[512,649]),(3,[259,516,789]),(1,[387,136,789]),(9,[259,145]),(6,[512,279]),(0,[259,263]),(3,[259,516,283]),(1,[387,136,411]),(9,[259,263]),(12,[512,151]),(2,[516,279]),(6,[512,407]),(1,[136,535]),(8,[516,407]),(1,[387,139]),(6,[515]),(2,[519,23]),(5,[131,657]),(0,[259,646]),(3,[259,519,665]),(1,[387,139,665]),(9,[259,518]),(6,[515,277]),(2,[519,279]),(5,[275]),(6,[515,407]),(1,[139,535]),(8,[519,407]),(0,[259,526]),(6,[142,277]),(2,[394,23]),(1,[387,657]),(3,[259,654]),(0,[259,526,665]),(12,[520]),(1,[387,144]),(6,[524,649]),(11,[261]),(2,[520,642]),(0,[259,405]),(3,[259,533]),(1,[387,144,789]),(9,[259,401]),(17,[259]),(0,[259,394]),(1,[387,144,782]),(9,[259,394]),(12,[520,646]),(3,[259,522]),(3,[259,527]),(12,[527]),(14,[387]),(13,[259]),(1,[387,519]),(0,[259,400]),(1,[512]),(0,[384]),(1,[512,407]),(0,[384,279]),(1,[512,407,392]),(0,[384,279,260]),(8,[384,279]),(3,[259,394]),(0,[384,279,522]),(9,[384,275]),(3,[260]),(1,[512,392]),(1,[392]),(8,[260]),(4,[392]),(0,[384,260]),(0,[260]),(8,[384]),(4,[516]),(3,[260,641]),(1,[512,392,789]),(0,[384,260,789]),(3,[263]),(1,[512,395]),(0,[384,263]),(1,[395]),(8,[263]),(4,[395]),(0,[263]),(3,[263,21]),(5,[256,645]),(2,[256,646]),(1,[512,395,665]),(0,[384,263,665]),(2,[256,389]),(0,[384,517]),(9,[384]),(3,[389,643]),(1,[512,279]),(5,[256,407]),(2,[256,389,791]),(0,[384,517,791]),(5,[388]),(1,[268]),(1,[512,268]),(0,[517,648]),(5,[256,392]),(2,[256,389,776]),(1,[512,272]),(0,[384,517,780]),(2,[256,390]),(0,[384,518]),(3,[390,21]),(1,[512,649]),(2,[256,390,665]),(0,[384,518,665]),(3,[390,279]),(6,[130,279]),(7,[140]),(4,[10,407]),(0,[518,279]),(0,[384,522]),(3,[394,21]),(1,[512,653]),(2,[256,654]),(0,[384,522,665]),(1,[515]),(0,[387]),(7,[259]),(2,[259,149]),(6,[13]),(1,[515,277]),(0,[387,149]),(11,[9]),(8,[387]),(4,[519]),(2,[259,151]),(6,[15]),(1,[515,279]),(0,[387,151]),(11,[11]),(1,[515,407]),(0,[387,279]),(2,[259,150]),(7,[259,151]),(12,[5]),(1,[515,407,281]),(0,[387,279,153]),(8,[387,279]),(4,[519,407]),(2,[259,148]),(3,[256,151]),(12,[7]),(1,[515,407,283]),(0,[387,279,155]),(2,[259,516]),(3,[256,516]),(2,[259,519]),(3,[256,519]),(3,[256,520]),(1,[515,407,140]),(9,[387,275]),(6,[271,520]),(3,[512]),(2,[259,535]),(6,[527]),(1,[515,151]),(9,[387]),(1,[515,392]),(14,[260]),(12,[128]),(0,[387,260]),(3,[260,642]),(1,[515,392,789]),(6,[256,653]),(0,[387,260,789]),(11,[128,521]),(1,[515,395]),(0,[387,263]),(14,[263]),(12,[131]),(6,[259,405]),(3,[263,23]),(5,[259,645]),(2,[259,646]),(1,[515,395,665]),(0,[387,263,665]),(11,[131,273]),(43,[]),(5,[259,263]),(1,[515,395,539]),(1,[395,535]),(14,[263,403]),(12,[131,279]),(4,[395,535]),(0,[387,263,411]),(2,[259,389]),(0,[387,517]),(3,[389,640]),(6,[129,655]),(5,[259,407]),(2,[259,389,791]),(0,[387,517,791]),(14,[136]),(1,[515,268]),(2,[259,390]),(0,[387,518]),(3,[390,23]),(1,[515,649]),(2,[259,390,665]),(0,[387,518,665]),(6,[130,405]),(1,[515,136]),(3,[516,642]),(6,[512,653]),(2,[259,516,789]),(1,[515,136,789]),(9,[387,145]),(3,[516,279]),(1,[136,407]),(8,[516,279]),(0,[387,391]),(2,[259,516,283]),(1,[515,136,539]),(9,[387,391]),(12,[512,279]),(1,[515,139]),(3,[519,23]),(5,[259,657]),(0,[387,646]),(2,[259,519,665]),(1,[515,139,665]),(9,[387,518]),(6,[515,405]),(3,[519,279]),(5,[147]),(6,[515,279]),(1,[139,407]),(8,[519,279]),(0,[387,522]),(6,[138,405]),(3,[394,23]),(1,[515,653]),(2,[259,654]),(0,[387,522,665]),(12,[516]),(1,[515,140]),(6,[520,653]),(11,[137]),(2,[259,533]),(3,[520,642]),(0,[387,277]),(1,[515,140,789]),(9,[387,273]),(0,[387,395]),(2,[259,275]),(1,[515,140,539]),(9,[387,395]),(12,[516,279]),(2,[259,527]),(14,[259]),(13,[387]),(1,[515,391]),(0,[387,272]),(2,[385]),(3,[385]),(0,[513]),(9,[]),(5,[385]),(3,[385,260]),(0,[513,260]),(9,[260]),(4,[5]),(1,[392,23]),(2,[385,647]),(3,[385,260,667]),(0,[513,260,667]),(6,[256,151]),(5,[385,644]),(1,[392,12]),(6,[256,136]),(3,[385,260,648]),(0,[513,260,648]),(4,[5,652]),(5,[385,648]),(6,[140]),(1,[392,16]),(2,[385,648]),(1,[16]),(4,[5,656]),(0,[513,652]),(7,[385]),(3,[385,263]),(0,[513,263]),(9,[263]),(5,[385,647]),(6,[259,151]),(1,[395,23]),(2,[385,644]),(3,[385,263,667]),(0,[513,263,667]),(7,[385,648]),(1,[395,16]),(2,[385,260]),(0,[513,388]),(9,[388]),(1,[520,23]),(3,[385,647]),(2,[385,260,667]),(0,[513,388,667]),(6,[384,151]),(6,[136]),(1,[520,12]),(3,[385,648]),(1,[12]),(0,[513,648]),(6,[384,140]),(2,[385,260,648]),(1,[520,16]),(0,[513,388,652]),(2,[385,263]),(0,[513,391]),(9,[391]),(5,[385,651]),(6,[387,151]),(1,[523,23]),(2,[385,263,667]),(3,[385,644]),(0,[513,391,667]),(7,[385,644]),(1,[523,12]),(10,[257]),(0,[513,392]),(9,[392]),(6,[392,148]),(1,[524,20]),(0,[513,392,664]),(6,[392,136]),(1,[524,12]),(0,[513,392,648]),(6,[392,140]),(1,[524,16]),(0,[513,392,652]),(1,[12,649]),(2,[385,645]),(12,[129]),(8,[261]),(3,[385,648,773]),(9,[261]),(0,[513,648,773]),(8,[395]),(2,[385,646]),(1,[12,650]),(12,[130]),(8,[262]),(3,[385,648,774]),(9,[262]),(0,[513,648,774]),(2,[385,279]),(1,[12,535]),(9,[395]),(0,[513,648,411]),(6,[136,407]),(1,[16,649]),(3,[385,645]),(12,[257]),(2,[385,648,773]),(8,[389]),(9,[389]),(0,[513,652,773]),(8,[394]),(3,[385,646]),(1,[16,650]),(12,[258]),(2,[385,648,774]),(8,[390]),(9,[390]),(0,[513,652,774]),(3,[385,650]),(1,[16,654]),(12,[262]),(9,[394]),(0,[513,652,778]),(6,[140,650]),(2,[386]),(3,[386]),(0,[514]),(3,[386,279]),(0,[514,279]),(5,[386,151]),(2,[386,260]),(4,[6,407]),(7,[386,151]),(2,[386,263]),(2,[386,276]),(0,[514,279,411]),(2,[386,279]),(0,[514,407]),(5,[386,279]),(3,[386,260]),(4,[6,535]),(7,[386,279]),(3,[386,263]),(3,[386,648]),(6,[394]),(1,[515,654]),(0,[514,407,778]),(5,[386]),(0,[514,260]),(4,[6]),(7,[386]),(0,[514,263]),(0,[514,388]),(0,[514,391]),(10,[258]),(0,[514,392]),(1,[128]),(3,[512,279]),(1,[128,407]),(2,[512,279]),(1,[128,407,536]),(9,[259,400]),(2,[512,276]),(1,[128,407,539]),(5,[512,151]),(7,[512,151]),(3,[512,279,263]),(1,[128,407,395]),(2,[512,260]),(8,[512,279]),(2,[512,263]),(1,[128,535]),(3,[512,276]),(1,[128,535,411]),(5,[512,279]),(3,[512,260]),(8,[512,407]),(7,[512,279]),(3,[512,263]),(2,[512,279,263]),(1,[128,535,523]),(2,[512,405]),(3,[512,405]),(5,[512,405]),(3,[512,405,260]),(1,[128,392]),(7,[512,405]),(3,[512,405,263]),(1,[128,395]),(2,[512,405,260]),(1,[128,520]),(2,[512,405,263]),(1,[128,523]),(1,[128,524]),(10,[384,273]),(5,[512]),(8,[512]),(0,[260,641]),(2,[512,149]),(3,[512,260,789]),(1,[128,392,789]),(9,[260,513]),(4,[392,535]),(0,[260,407]),(1,[392,535]),(8,[260,407]),(9,[260,403]),(7,[512]),(0,[263,21]),(5,[512,645]),(2,[512,646]),(3,[512,263,665]),(1,[128,395,665]),(9,[263,17]),(0,[263,407]),(8,[263,407]),(1,[128,395,539]),(0,[388,641]),(2,[512,260,789]),(3,[512,149]),(1,[128,520,789]),(9,[388,513]),(4,[520,407]),(0,[388,279]),(1,[520,407]),(8,[388,279]),(9,[388,275]),(0,[391,21]),(5,[512,649]),(2,[512,263,665]),(3,[512,646]),(1,[128,523,665]),(9,[391,17]),(0,[391,279]),(8,[391,279]),(1,[128,523,411]),(10,[384]),(2,[515]),(3,[515]),(1,[131]),(5,[515]),(3,[515,260]),(1,[131,392]),(8,[515]),(2,[515,263]),(7,[515]),(3,[515,263]),(1,[131,395]),(2,[515,260]),(1,[131,395,539]),(1,[131,520]),(1,[131,523]),(1,[131,523,411]),(10,[387]),(1,[131,524]),(1,[392,641]),(1,[392,641,536]),(0,[260,641,408]),(2,[263,394]),(0,[260,407,526]),(0,[260,526]),(3,[260,14]),(1,[392,17]),(3,[14]),(1,[17]),(4,[18,149]),(0,[526,21]),(2,[394,149]),(3,[260,654]),(1,[392,657]),(0,[260,526,665]),(18,[392]),(3,[260,268]),(1,[392,403]),(0,[260,526,283]),(1,[392,144]),(5,[520,641]),(3,[260,513]),(0,[260,385]),(2,[520,641]),(3,[513]),(1,[144,641]),(8,[524,641]),(0,[385]),(2,[520,645]),(3,[260,533]),(11,[128,273]),(1,[392,144,789]),(9,[260,401]),(0,[260,405]),(3,[260,527]),(5,[527,21]),(1,[392,5]),(0,[260,18]),(2,[527,21]),(3,[527,21]),(1,[5]),(0,[18]),(13,[260]),(1,[392,519]),(0,[260,400]),(5,[5]),(2,[6]),(1,[395,21]),(5,[5,276]),(2,[6,279]),(1,[395,21,536]),(0,[263,21,408]),(5,[263,520]),(2,[260,520]),(1,[395,535,144]),(9,[263,403]),(0,[263,526]),(5,[394,149]),(2,[394,151]),(1,[395,657]),(3,[263,654]),(0,[263,526,665]),(1,[395,144]),(5,[520,645]),(2,[520,646]),(3,[263,533]),(1,[395,144,789]),(9,[263,401]),(0,[263,405]),(3,[263,527]),(13,[263]),(1,[395,519]),(0,[263,400]),(1,[520,641]),(1,[520,641,408]),(6,[384,276]),(0,[388,641,280]),(11,[256,144]),(3,[263,394]),(0,[388,279,522]),(0,[388,522]),(2,[260,14]),(1,[520,13]),(2,[14]),(1,[13]),(4,[14,149]),(0,[522,21]),(2,[260,654]),(3,[394,149]),(1,[520,653]),(0,[388,522,665]),(2,[260,268]),(1,[520,527]),(0,[388,522,411]),(1,[520,140]),(5,[516,641]),(2,[260,513]),(0,[388,257]),(3,[520,641]),(2,[513]),(1,[140,641]),(8,[520,641]),(0,[257]),(2,[260,533]),(11,[256,145]),(3,[520,645]),(1,[520,140,789]),(9,[388,273]),(0,[388,277]),(2,[260,527]),(1,[520,5]),(0,[388,18]),(13,[388]),(1,[520,391]),(0,[388,272]),(5,[9]),(3,[6]),(1,[523,21]),(5,[9,148]),(6,[387,276]),(3,[6,279]),(1,[523,21,408]),(0,[391,21,280]),(11,[259,144]),(5,[139,516]),(3,[260,520]),(1,[523,407,140]),(9,[391,275]),(0,[391,522]),(5,[390,277]),(3,[394,151]),(1,[523,653]),(2,[263,654]),(0,[391,522,665]),(1,[523,140]),(5,[516,649]),(2,[263,533]),(3,[520,646]),(1,[523,140,789]),(9,[391,273]),(0,[391,277]),(2,[263,527]),(13,[391]),(1,[523,391]),(0,[391,272]),(5,[387]),(0,[517,643]),(5,[387,151]),(3,[389,643,283]),(0,[517,643,283]),(6,[129,279]),(5,[387,279]),(2,[389,643,283]),(0,[517,643,411]),(6,[129,407]),(10,[261,515]),(4,[9,647]),(10,[261]),(0,[517,392]),(5,[260,404]),(1,[524,276]),(0,[517,392,664]),(2,[389,279]),(1,[268,535]),(0,[517,648,411]),(5,[388,279]),(3,[389,650]),(7,[262]),(1,[272,654]),(0,[517,652,778]),(5,[392,646]),(1,[9]),(0,[518,21]),(3,[390,21,280]),(1,[9,404]),(0,[518,21,280]),(6,[130,276]),(2,[390,21,280]),(1,[9,532]),(0,[518,21,408]),(6,[130,404]),(10,[262,17]),(1,[9,524]),(4,[10,149]),(1,[395,532]),(0,[518,279,408]),(2,[390,276]),(0,[518,279,411]),(10,[262]),(1,[395,524]),(0,[518,279,392]),(3,[390,648]),(5,[262]),(1,[523,654]),(0,[518,407,778]),(1,[523,524]),(0,[518,407,392]),(0,[518,392]),(2,[516,641]),(3,[516,641]),(1,[136,641]),(6,[512,276]),(3,[516,641,280]),(1,[136,641,408]),(6,[512,404]),(2,[516,641,280]),(1,[136,641,536]),(10,[388,513]),(8,[516,641]),(0,[263,404]),(1,[136,407,536]),(9,[263,400]),(2,[516,276]),(1,[136,407,539]),(3,[516,276]),(1,[136,535,411]),(10,[388]),(1,[136,524]),(5,[17]),(0,[6]),(2,[519,21]),(3,[519,21]),(1,[139,21]),(9,[6]),(5,[17,148]),(6,[515,276]),(0,[6,279]),(3,[519,21,280]),(1,[139,21,408]),(9,[6,275]),(5,[17,276]),(6,[515,404]),(0,[6,407]),(2,[519,21,280]),(1,[139,21,536]),(9,[6,403]),(10,[391,17]),(0,[6,392]),(8,[519,21]),(5,[147,276]),(1,[139,407,536]),(9,[260,400]),(0,[260,404]),(2,[519,276]),(1,[139,407,539]),(5,[147,279]),(3,[519,276]),(1,[139,535,411]),(5,[275,151]),(10,[391]),(1,[139,524]),(10,[395,17]),(1,[524,5]),(0,[392,18]),(7,[527,21]),(2,[14,279]),(1,[13,532]),(0,[522,21,408]),(6,[138,404]),(14,[395]),(3,[394,643]),(1,[527,641]),(2,[268,641]),(8,[385]),(9,[385]),(0,[522,407,769]),(2,[268,642]),(3,[394,640]),(1,[527,642]),(8,[386]),(9,[386]),(0,[522,407,770]),(9,[257]),(6,[520,404]),(2,[513,276]),(0,[257,404]),(1,[140,641,536]),(9,[257,400]),(3,[14,279]),(1,[17,404]),(0,[526,21,280]),(6,[142,276]),(14,[271]),(2,[394,643]),(8,[257]),(1,[403,641]),(0,[526,279,769]),(3,[268,641]),(2,[394,640]),(3,[268,642]),(1,[403,642]),(8,[258]),(9,[258]),(0,[526,279,770]),(6,[524,648]),(4,[140]),(3,[513,648]),(0,[385,648]),(1,[144,641,780]),(9,[385,520]),(3,[527,21,280]),(1,[5,404]),(0,[18,279]),(6,[519,276]),(11,[143]),(2,[527,21,280]),(1,[5,532]),(0,[18,407]),(6,[519,404]),(11,[271]),(11,[140,275]),(2,[527,276]),(1,[391,535]),(0,[272,407]),(11,[268,518]),(3,[527,648]),(1,[519,654]),(0,[400,650])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(30,28),(29,28),(15,13),(15,14),(46,42),(43,42),(15,11),(46,38),(39,38),(15,7),(30,14),(23,7),(51,50),(22,7),(46,14),(39,7),(53,49),(51,49),(15,9),(57,49),(15,5),(29,13),(21,7),(45,13),(37,7),(27,19),(23,19),(27,11),(43,11),(35,7),(35,11),(51,19),(54,38),(35,19),(37,38),(57,56),(53,52),(45,44),(58,56),(54,52),(46,44),(21,28),(60,52),(22,28),(21,5),(21,13),(29,5),(37,5),(37,13),(45,5),(60,28),(22,38),(54,50),(58,50),(60,44),(41,42),(47,42),(58,42),(26,11),(25,24),(43,10),(25,9),(35,33),(25,11),(27,9),(41,9),(26,24),(41,11),(43,9),(26,42),(25,28),(60,56),(26,28),(25,13),(29,9),(41,13),(45,9),(47,38),(21,20),(39,6),(23,5),(22,20),(39,5),(37,33),(23,3),(41,33),(27,3),(37,36),(46,36),(31,11),(35,38),(31,14),(31,13),(15,3),(41,40),(46,40),(31,7),(35,42),(60,40),(60,24),(22,18),(21,17),(15,10),(60,48),(26,18),(15,6),(25,17),(60,36),(60,20),(39,34),(43,34),(55,7),(22,19),(26,19),(21,19),(25,19),(47,11),(47,7),(31,28),(61,56),(31,19),(61,52),(47,44),(41,49),(57,33),(41,44),(61,44),(37,49),(53,33),(37,44),(26,14),(46,10),(22,14),(46,6),(62,56),(62,52),(54,18),(58,18),(22,6),(26,10),(62,14),(62,42),(58,34),(62,44),(46,34),(22,50),(47,14),(29,24),(57,24),(30,10),(58,10),(54,34),(62,38),(54,6),(30,6),(26,50),(29,20),(53,20),(51,17),(35,34),(62,50),(41,56),(57,40),(47,13),(35,50),(60,12),(54,36),(54,20),(22,52),(30,12),(27,10),(57,48),(62,28),(37,52),(61,28),(46,12),(30,20),(51,18),(53,36),(58,40),(58,24),(26,56),(23,6),(53,48),(30,24),(39,3),(43,3),(21,52),(35,49),(51,33),(29,12),(25,56),(35,17),(21,33),(25,33),(45,52),(45,28),(45,56),(55,49),(61,49),(59,49),(23,18),(27,18),(43,40),(45,40),(55,38),(59,42),(45,12),(45,36),(39,33),(61,13),(39,36),(59,11),(43,33),(23,17),(27,17)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptopD6 : List StD := []
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD7 : List StD := [([v263,v3,v2,v264,v6,v40,v241],[33,285,13,552,69,9,404,105,25,52,556,524,536,37,45,420,109,61,113,153,141,209,21,409,29,41,233,241,65,73,413,85,253,261,269,293,301,125,229,277],[15,114,1922,14336,114690,394242,1572900,14680324,16781325,101777412,138677252,805830944,1090519088,6443040800,25770590240,1090519424,36507287936,68988305664,1090600960,17171456,962073001984]),([v265,v3,v2,v266,v5,v40,v241],[21,169,13,736,69,9,404,101,37,88,740,676,724,25,109,608,45,113,61,157,145,213,33,421,17,41,53,317,77,81,413,85,89,189,97,181,193,125,129,205],[15,114,1922,14336,114690,394242,1572900,14680324,16781325,101777412,138677252,805830944,1090519088,6443040800,25770590240,1090519424,36507287936,68988305664,1090600960,17171456,962073001984]),([v3,v2,v5,v267,v6,v268,v40,v241],[5,9,1,49,25,33,13,389,29,53,129,57,61,317,69,73,45,85,93,65,105,109,113,37,16,3608,3532,177,125,133],[7,56,97,416,40,1568,14336,49168,16386,16386,16386,196610,266242,524304,524304,1572880,2162704,4198416,8388608,16777216,2162688,4198400,100663552,2162688,4198400,134283264,268439552,536940544]),([v3,v2,v5,v267,v6,v269,v40,v241],[5,9,1,17,25,33,389,29,53,129,57,61,317,69,73,45,85,93,105,109,117,113,169,404,3532,36,133],[7,24,33,224,33,800,7168,24592,8194,8194,8194,98306,133122,262160,262160,262160,557072,3145744,4194304,8388608,557056,2099200,50331776,557056,2099200,557056,2099200,67143680]),([v3,v2,v169,v5,v171,v6,v40,v241],[5,9,1,21,13,361,17,49,37,53,229,45,57,61,69,81,89,85,97,93,25,16,77,109,113,3584,3528,101,245,125,133],[7,25,104,136,392,3584,12288,16386,16386,16386,49408,196610,786434,1048576,2097152,4194560,8390656,16785408,100663360,4194560,8390656,16785408,138412288,268437504,536879104,8390912,16785664,1073752064]),([v3,v2,v169,v5,v270,v6,v40,v241],[5,9,1,21,361,17,29,37,53,229,45,57,61,69,81,89,85,97,93,285,404,101,109,113,3528,36,121,133],[7,9,56,9,192,1792,6144,8194,8194,8194,24704,98306,393218,524288,1048576,2097280,4195328,8392704,50331680,2097280,4195328,8392704,2097280,4195328,8392704,4195456,67113088,134222848]),([v201,v3,v2,v5,v198,v6,v40,v241],[13,33,21,9,404,3584,25,105,17,16,4,3860,3724,101,45,109,61,113,141,501,233,229,57,241,457,161,157,37,81,245,261,3872,65,521,525,88,277],[7,56,448,7680,8192,49152,196608,262148,524548,262148,6,3145732,12713984,16777480,33554432,469762048,536903680,1073872896,6442451200,384,8589967616,17184194560,34493960192,536903680,1073872896,134266880,134414336,68719640576]),([v199,v201,v3,v2,v5,v6,v40,v241],[3892,3724,4,404,141,21,161,105,17,65,37,88,245,109,261,113,49,9,3788,16,101,45,125,361,233,229,57,241,157,81,521,525,277],[15,48,64,896,3074,12288,49152,65568,917504,768,1048576,2105344,4227072,48,8388896,65568,50331680,201359360,131840,805307392,12288,49152,1792,1073750272,2214625280,2106368,4227072,4295008256]),([v271,v3,v2,v5,v6,v272,v40,v241],[13,21,33,9,404,3608,105,37,101,29,16,0,3936,3620,109,45,113,61,145,517,53,129,57,317,153,25,73,461,161,177,189,52,3952,77,529,533,205],[7,56,64,896,15360,49152,196608,262148,6,524804,262148,3145732,12713984,117440512,134218248,268435456,536903680,1073872896,768,2181046272,33603584,33751040,12884902400,17179902464,34364063744,536903680,1073872896,68719640576]),([v273,v271,v3,v2,v5,v6,v40,v241],[3968,3620,0,404,145,33,161,25,52,101,29,77,177,45,189,61,49,9,3676,16,105,109,125,389,53,129,57,317,153,73,529,533,205],[15,48,64,386,3584,12288,49152,65568,917504,1048576,3072,2105344,4227072,48,65568,8389664,50331680,201359360,805306496,134144,12288,49152,3200,2105472,4227072,1073751040,2214625280,4295008256]),([v274,v3,v16,v2,v5,v6,v40,v241],[33,21,13,16,432,88,69,404,65,0,52,37,45,109,61,113,149,221,813,501,817,825,201,9,25,213,4692,457,169,85,253,257,93,269,273,293,297,301,305,133],[7,56,200,1792,2048,12288,49152,3,458752,1572866,3,2105346,4227074,8388608,16777216,100663328,12288,49152,134218048,301989952,3758096384,30064771072,301990144,103079223296,412316893184,12288,49152,549755854848]),([v275,v3,v33,v2,v5,v6,v40,v241],[21,33,13,16,620,52,69,404,25,77,4,88,109,45,113,61,149,137,845,517,833,821,201,9,209,4688,37,285,461,85,89,321,93,97,329,169,181,185,193,197,133],[7,56,200,256,3584,12288,49152,3,458752,3,1572866,2105346,4227074,8388608,50331680,67108864,12288,49152,150995008,268436032,3758096384,30064771072,34376516096,12288,49152,206158438400,824633753600,1099511668736])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*8)).take 8) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 8 ptopD7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD8 : List StD := [([v105,v3,v2,v5,v6,v40,v241],[76,33,20,13,5,80,69,16,9,1,84,88,17,56,29,92,45,8,85,36,96,61,40,100,93,12,137,209,21,25,213,37,41,149,57,65,73,77,81,161,101,105,109,113,201,217],[31,992,7168,26624,1017856,66060288,67110514,939525136,3221233682,12885196817,25794969617,103616087616,414464352832,554051076640,566960849440,3301219238912,6597606933504,8831014798336,1101659480064,139613708288,52776584642560]),([v276,v3,v2,v5,v6,v40,v241],[104,33,21,0,13,108,20,69,153,9,112,16,105,25,56,88,37,116,45,8,109,36,120,61,40,124,113,12,141,221,209,225,29,229,233,57,237,241,65,1,73,169,245,249,253,257,261,265,269,273,117,125,277],[127,3977,12297,114688,4096000,264241152,805307781,3221233671,4294983718,26039418916,240618831908,1924145357057,2203318239616,65970698847488,1055531263329536,4294979585,1454081,1126174893809665,2203319681024,4408229888,6755408137027584]),([v277,v3,v2,v5,v6,v40,v241],[144,21,33,4,13,148,20,69,157,9,152,16,84,88,25,101,37,0,156,109,8,136,45,36,160,113,40,164,61,12,145,137,17,213,309,129,53,57,313,317,285,77,1,81,177,249,89,321,189,325,97,329,121,125,205],[127,3977,28672,233473,16515072,1056964608,3221230980,4294971430,25769869319,104157413412,962475327524,1103806599552,15393162854657,263882795123968,4222125053314304,4295069697,1103811579904,4747956224,5079041,4505799086899201,27021632547848192]),([v109,v3,v2,v5,v6,v40,v241],[212,5,20,13,21,208,1,16,9,69,240,65,8,25,244,0,248,77,88,252,37,4,245,85,45,236,261,40,256,61,12,161,149,209,141,361,29,33,229,365,57,153,157,81,369,93,97,101,105,109,113,117,121,125,133],[31,992,64512,4128768,29365248,2113929216,6442452264,60129566728,206160003081,824650499082,1237755887625,2199023282432,13194141237536,17592207017280,105556069056800,422212466139136,844424946918400,3377700525860864,703687459603456,5629569094123520,27021873464214528]),([v7,v3,v2,v5,v278,v6,v40,v241],[260,264,13,9,65,268,105,272,16,276,280,88,29,216,37,224,177,284,45,288,93,292,61,296,137,1,5,209,141,20,149,145,129,57,153,161,157,32,25,24,285,373,109,333,357,113,117,200,101,204,44,125,133],[7,9,240,3841,61440,983040,15728640,117440515,469762112,1677721602,2214612992,5436080128,9734979584,17213423696,34393293057,68753055745,34393620480,34398535680,2061584826432,3298534899808,30786325839936,105553120460880,422212465074176,4535486251008,1724034236547072,4398047313920,35184376303616,6755403740479488]),([v279,v3,v2,v5,v6,v40,v241],[304,5,20,13,33,300,1,16,9,69,328,65,52,332,25,0,336,77,8,37,340,4,177,85,45,236,189,40,344,61,12,161,149,17,21,213,145,389,129,365,57,153,73,157,369,93,101,105,109,113,117,121,125,133],[31,992,64512,4128768,29687808,2113929216,6442516776,25769828361,240519741448,824650563594,1117496803337,6597069793568,8796094726400,17592207081792,35187324879136,211106234130432,422212481925120,1688859289083904,351843738255360,2814750574116864,13511074582167552]),([v7,v3,v2,v133,v5,v6,v40,v241],[348,352,33,9,16,356,280,328,17,308,25,316,77,360,101,364,177,368,45,372,189,376,61,380,137,1,5,20,149,141,213,145,129,349,57,161,153,157,200,105,32,37,169,24,109,113,204,44,373,341,385,121,125,133],[7,9,241,3840,61440,983040,15728640,117440515,469762050,603981056,3288350720,12952272896,19398656000,34393292817,68753032705,137472528384,34393620480,137477750784,824633721344,16492674957312,18691698458624,246290608816128,285873023247872,17592186831872,35184376284416,1706442046586880,2286984189988864,13510803181535232]),([v3,v2,v280,v5,v6,v40,v241],[436,157,145,440,9,13,444,20,33,448,16,209,21,105,416,213,101,452,41,456,45,49,53,57,460,61,464,69,468,65,77,85,89,93,97,88,25,37,8,36,40,12,169,285,109,333,337,113,117,341,345,121,125,129,133],[127,2017,14376,114976,8257632,125829472,402654417,671096856,1208041488,6846283793,26222788625,103079215112,171798708224,861142122496,3341534887936,13194139607048,123145303498760,422213052276744,1706442047569920,2392538426195968,31525231802843136]),([v281,v3,v2,v5,v6,v40,v241],[472,13,0,476,21,388,9,480,153,404,1,105,25,285,416,88,101,484,45,8,109,36,61,40,488,113,12,492,141,221,496,281,29,33,37,229,233,201,237,241,500,289,69,81,245,253,257,261,265,269,273,333,217,393,397,277],[63,1989,14341,114688,4096000,130056192,2013266257,2147493907,30064787472,104422572056,2062708375568,2199023266113,13211453636864,123145437708736,2111062509879680,17179879425,15762598696984577,18014535998777345,17181360128,21529378816,36028968869199872]),([v3,v2,v264,v55,v6,v40,v241],[504,153,141,137,384,9,13,508,209,21,105,285,33,448,388,416,213,101,512,41,456,45,49,53,57,516,61,520,65,69,468,404,77,85,89,93,97,4,25,52,109,333,337,113,117,37,420,524,341,345,121,125,129,133],[255,1873,30912,233536,16515264,251662528,805307568,3758098465,4832002080,27382775841,104790491169,415538121728,687194932224,8246339568640,26938403980288,35184372088848,70377336481792,140771948767232,845524444282880,1134700395659264,15763148554633216]),([v3,v2,v264,v251,v6,v40,v241],[528,153,141,137,424,9,33,532,384,401,21,25,524,285,13,428,29,536,37,540,129,544,45,49,53,113,405,69,73,404,77,81,548,85,89,261,269,12,65,52,101,105,109,117,3,420,61,125,121,133],[255,3905,61504,508096,33030336,33574992,469764512,536883232,7650803745,30203707425,103246987312,412316874768,3848291092480,6597076584448,8933565536272,17592186515456,35184377868288,70368744177936,5497565347840,422213572624400,703687480573968]),([v3,v2,v264,v5,v248,v6,v40,v241],[153,141,137,9,13,560,21,564,568,285,428,524,412,417,33,37,421,41,45,49,53,61,424,317,69,572,576,404,408,425,81,85,89,189,97,25,40,52,580,101,416,4,109,584,588,125,12,384,592,77,420,229,596,113,121,129,133],[31,496,1744,7248,122896,1966096,14698512,50331816,83886728,402655241,1627422728,6459490312,25788678152,34426847360,481036339200,3848290729984,30786325839872,105553122557952,140737488358016,1649267475072,285873023484416,35184378380800,562949957615616,7881299348162560,9008298770563072,4947802619904,18015498027433984,108121575431340032]),([v282,v3,v2,v5,v6,v40,v241],[624,13,4,628,33,388,9,632,157,404,1,440,88,105,101,37,169,0,636,109,8,136,45,36,52,113,40,640,61,12,644,145,137,648,17,21,25,165,129,53,201,313,317,652,69,73,173,177,89,321,189,325,97,329,341,217,429,433,205],[63,1989,14336,247809,16515072,1056964608,16106129744,120259086352,137439035411,835375595544,16501667004432,52846351354112,70368744259905,985163496686016,16888500079034752,68719560705,68726556672,86335555584,126100789570895873,144116287990218753,288231750950453248]),([v3,v2,v266,v55,v5,v40,v241],[656,157,145,221,440,9,13,660,392,213,33,101,169,21,448,388,209,105,664,41,456,109,49,233,57,668,113,672,77,69,468,404,65,85,253,93,269,0,37,88,45,341,345,61,121,25,608,676,333,337,117,125,229,133],[255,3905,61632,204880,16515264,251666624,805308832,3758100513,4831969328,27382775841,104790491169,415538092048,687194900496,8246339569664,26938403981312,35184372089104,70377336492032,140771948777472,845524444250128,1134700395626512,15763148554633216]),([v3,v2,v266,v251,v5,v6,v40,v241],[157,145,221,9,13,680,33,684,688,676,616,604,401,21,25,409,169,41,109,49,233,113,612,241,69,692,404,600,405,73,548,85,253,261,269,40,88,696,105,440,0,37,45,700,704,125,12,65,392,608,129,708,61,117,712,229,133],[31,496,3664,61456,66768,1966096,14688784,50331816,201327113,822099976,1090584712,6459490312,25788678152,240518169088,1924145364992,2200096997504,30786325839872,105553122557952,140737492549632,281474976776832,3940649674211840,4504149387378688,824633802752,4672924696576,9007749016862720,18018796556320768,35184378445824,108121575431340032]),([v3,v2,v266,v5,v248,v40,v241],[716,157,145,221,612,9,13,720,392,417,33,37,421,17,21,724,25,616,676,169,728,41,732,109,49,233,61,425,69,81,65,73,576,404,85,253,189,97,88,105,101,12,77,45,121,3,125,117,608,229,113,133],[255,8001,254144,933952,66060480,67387472,939526560,7784726561,8590721056,56112447521,206493974576,1924145448960,6597070555152,9895618283520,19791276673040,35184372981760,9345862565888,211107373449232,844424940355584,1125899906842896,2885118586781712]),([v245,v3,v2,v22,v55,v5,v6,v40,v241],[13,33,9,249,188,468,760,756,448,764,105,333,101,341,129,61,137,149,21,361,437,389,441,53,41,161,89,85,88,768,772,52,776,780,180,45,184,201,125,17,29,784,109,445],[3,12,112,896,3072,12288,16384,32768,65546,131072,3,1835008,6291458,25165826,3,33554432,12,2060,8204,201326600,12,1879048192,6442452992,8858378240,120259084288,412316860416,549755813888,1099511627776,34493956096,412316860416,2199023265792,4432406251520,3072,4432406257664,12288,9105330667520]),([v3,v2,v283,v5,v6,v40,v241],[812,161,149,221,816,69,21,820,20,13,752,16,824,209,105,449,213,49,828,101,453,804,229,109,233,57,832,113,241,808,9,788,65,457,77,461,245,249,253,257,261,269,273,285,8,25,0,248,37,88,4,217,45,61,40,12,357,345,125,121,133],[255,4033,62016,4128960,29491280,1040188096,3221227937,13958664224,54761619489,1030800539696,7700003946529,131941395353616,2111062326116352,6772991635488784,63050395521384448,290271070277632,74309393860018192,9007203751055360,144396663061480464,864691146373988352,1441151880972468240]),([v284,v3,v2,v5,v6,v40,v241],[756,33,40,13,840,16,161,9,844,20,1,848,285,12,65,852,25,0,696,29,88,856,37,4,860,129,8,864,45,36,201,61,113,149,221,401,21,409,213,49,421,868,41,53,241,405,69,73,77,81,548,85,89,261,269,101,105,109,117,125,121,229,133],[63,1989,260096,16515072,1056964608,7516203008,25769806296,240518266888,4123174895880,13744314777864,17666274232328,246290604720256,2040693587443856,7951668377288848,27091970803370112,108086391061184512,216172782399094784,288230381520492544,180143985520541696,1729663736186144768,7493989784507910144]),([v263,v3,v2,v22,v5,v6,v40,v241],[33,20,13,120,69,16,9,404,88,872,876,105,400,25,384,880,756,684,37,45,396,109,752,61,113,884,888,221,5,209,21,409,29,41,49,233,241,1,65,73,169,85,253,261,269,892,3,896,680,217,900,904,40,908,293,301,125,229,277],[15,240,1920,63488,458752,7864320,25202688,234881092,335544320,3758104580,4295098381,60131639300,69810094084,137472507904,824633729104,1103806595152,6597071863888,26388295843920,246290604630528,282578783436800,3940649676046848,13510798898987008,35188667066368,18016597534844928,36029071922044928,1103809216512,4320165888,504403158284369920]),([v3,v2,v285,v5,v6,v40,v241],[932,161,149,137,936,69,33,940,20,13,752,16,209,49,944,105,449,928,948,213,101,453,129,45,53,57,952,61,317,808,9,912,65,457,77,461,177,249,89,321,189,97,329,328,25,0,52,169,8,37,4,217,109,113,40,12,337,125,117,385,133],[255,4033,258240,3932736,29368400,1040188096,3221227937,16106176545,52614660128,1030800539696,7700003946529,131941395382272,2111062326640656,7036874426155024,63050395521384448,158329675759616,72075186232394768,432345569260781568,578712552126545936,9007216637247488,1297036692896612368]),([v286,v3,v2,v5,v6,v40,v241],[756,21,40,13,960,16,161,9,964,20,1,580,17,968,25,0,52,972,169,12,77,976,37,4,980,229,8,984,45,36,201,113,61,149,137,209,49,409,988,417,33,421,41,53,317,65,69,73,576,425,81,85,89,189,97,101,105,109,125,117,121,129,133],[63,1989,129024,16646144,1056964608,7516848128,25769935320,515396100360,3848296988680,13263278440712,18697066512392,527765581357200,1759218610733184,7107243447156880,27091970803499136,108086391063207936,216172782533238784,864726317122338816,180143985386323968,1152921509980143616,7205759408356327424]),([v265,v3,v2,v22,v5,v6,v40,v241],[21,20,13,992,69,16,9,404,580,996,1000,756,564,25,101,400,37,384,1004,109,396,45,752,113,61,1008,1012,137,5,17,213,33,421,41,49,53,317,1,285,77,81,85,89,189,97,560,1016,3,1020,217,1024,1028,40,1032,181,193,125,129,205],[15,240,1920,14336,507904,7864320,25460736,234881092,335544320,536875021,7516258308,60131639300,70884001796,137472507904,275414777936,1649267507280,6597071863888,26388295843920,35459786870784,492581209309696,3940649676046848,13510798899152896,70369281134592,275417399296,562298880,18016597534916608,36029346800009216,504403158284369920]),([v3,v2,v22,v287,v5,v6,v40,v241],[1052,1056,137,13,9,5,20,33,1060,17,21,333,29,37,421,41,45,49,53,201,113,1,16,69,404,77,81,85,89,261,269,1064,1036,764,1000,784,52,776,169,136,1068,1072,1076,36,1080,1084,756,25,101,392,1088,109,400,396,61,465,125,121,229,133,445],[31,34,456,3592,28808,491528,1573000,2097153,29360144,8391184,109060112,411107344,1620049936,32229031936,242665654272,1926292840448,15395310338048,52776559706112,211140592271360,1970333426917376,15780190881906688,22535590324469760,281474976721408,2253998837008384,36046389206583296,2533274790469632,216172782148395008,2089670227101024256]),([v3,v2,v22,v5,v288,v6,v40,v241],[1092,1096,137,13,9,5,17,21,25,409,20,33,1100,29,341,41,45,49,53,201,61,317,1,65,69,73,16,404,85,89,189,97,285,68,1104,1108,1036,764,876,1040,88,780,1112,1116,36,1120,1124,105,384,1128,109,125,117,756,37,400,396,113,469,129,133],[31,34,968,7176,26632,491528,3672072,4194305,58720528,218103824,16801808,822149136,3239051280,64424509696,515530293248,3882650451968,30820685381632,105553117839360,985299857441024,140737488380160,1266637395263744,6755399450493184,27022147520036864,109247475335888896,180179169468481536,1130297953435648,288265560525389824,1731634056725069824]),([v3,v2,v289,v5,v6,v40,v241],[1164,1,145,76,69,13,1168,473,16,33,209,21,105,1152,213,101,1172,41,45,49,53,57,1176,61,468,404,9,65,457,77,461,85,249,89,321,93,97,329,88,25,37,8,36,96,40,12,109,333,337,113,117,341,345,121,125,129,133],[255,809,7264,57888,2031656,14680616,117440787,402657362,1610653714,32229359633,240547528723,824633720896,1374389542912,6871948132352,61572665835520,45120,492581209575488,1688850007068736,6825768185602048,9570149757657088,126109585672306688]),([v290,v3,v2,v5,v6,v40,v241],[1180,13,21,0,108,20,69,9,480,153,404,105,25,1152,88,101,1184,45,8,109,36,120,61,40,1188,113,12,1192,141,221,209,477,29,33,37,229,233,57,237,241,65,1,457,169,81,85,249,253,257,93,265,269,273,481,333,293,297,301,305,125,277],[63,1993,14345,57344,2048000,132120576,939524693,3221227527,30064779268,103348240404,962123005972,7696581396993,26405458944576,527765716140800,8444249485869824,9007216434620417,126135973939054593,432909613742950401,8813273620480,21529370624,1729382291323027456]),([v291,v3,v2,v5,v6,v40,v241],[1208,13,33,4,148,20,69,9,632,157,404,1168,88,105,101,37,0,1212,109,8,136,45,36,160,113,40,1216,61,12,1220,145,137,17,21,25,213,485,129,53,57,313,317,285,73,77,1,461,85,249,89,321,93,325,97,329,481,341,181,185,193,197,125,205],[63,1993,14336,116737,8257536,528482304,3758099028,30064773124,103079231495,413392830484,3848492023828,13211319405120,123145302327809,2111062864429824,33776997943476992,36028814198851585,4415228872704,21692942336,504543895756095489,1731651649111343105,6917529165291978752]),([v292,v3,v2,v5,v6,v40,v241],[212,21,16,13,1256,1,69,788,9,404,1260,105,8,65,1264,0,25,248,101,88,1268,37,4,109,45,85,1252,113,40,1272,61,12,161,149,209,501,29,33,229,49,505,57,153,73,77,157,81,89,93,97,285,245,333,293,297,261,405,177,181,193,125,133],[31,1012,130048,8257536,58725376,4227858432,12884903193,51539632138,206161575945,1924178904072,2338072821769,13194139560192,123145305457040,140737530299680,844430835712400,1143492095008768,33776997238842368,108086392667529216,432363156449264640,576759821147045888,3458764790342616064]),([v293,v3,v2,v5,v6,v40,v241],[304,33,16,13,1284,1,69,912,9,404,328,105,52,1288,25,0,1292,101,8,77,1296,4,37,45,85,109,1252,61,40,1300,113,12,161,149,17,21,213,517,129,49,505,57,65,153,73,157,81,253,93,269,169,245,293,301,177,341,181,185,189,425,125,133],[31,1012,64512,8323072,59047936,4227858432,12884967705,51539632137,206160003082,1924162191368,2234993606665,30786325602704,105553117970688,140737513586976,844430835712400,1130297954951168,6759797504425984,9293073955708928,270215977659596800,864691130067320832,3458764790325903360]),([v3,v294,v2,v5,v6,v40,v241],[1344,20,33,1348,404,5,13,1352,80,157,9,473,1356,17,21,105,1328,29,101,1360,217,149,456,85,201,1364,93,1368,69,16,88,25,37,45,8,36,61,40,12,65,77,89,97,109,333,113,341,125,133],[255,7972,61472,458788,16252961,253755425,805307648,3221229568,5368774656,61212196864,482210742272,550024287232,1099780391936,2207890539776,4467135087872,438272,26388288016384,35734228602880,70377343352832,1168332095488,422213649432576]),([v295,v3,v2,v5,v6,v40,v241],[1372,33,0,13,476,21,388,9,153,112,16,1,105,25,17,1328,88,101,1376,45,8,109,36,61,40,1380,113,12,141,221,449,169,37,41,233,1384,57,237,1388,241,65,537,69,81,245,253,257,261,265,269,273,521,525,125,229,277],[127,3973,28677,229376,8192000,260112384,805307297,1073762339,6442483746,60400336944,1065252552736,3298534900097,13200582017280,123145304671104,2111062425993984,4294987777,2251808405999617,4503668447531009,6445367296,6551535616,63050394886275072]),([v3,v296,v2,v5,v248,v6,v40,v241],[560,21,1392,149,13,576,153,9,489,17,1340,1396,5,1324,417,145,37,217,45,61,1336,69,568,25,40,52,580,101,1328,4,109,584,588,125,12,16,425,81,85,89,189,97,209,1304,401,77,1332,1400,93,181,193,133],[63,458,1550,15368,114696,397320,1579016,6291589,12582916,117442560,939589632,7516454912,25771376640,6292100,34363934912,206160593024,824636080256,3298537504896,13194139533828,4398180794880,4399120515584,17600776503808,35184373137408,211106232928256,281475246194688,563224965873664,1125900176916480,2251808404537344]),([v297,v3,v2,v5,v6,v40,v241],[1424,21,4,13,628,33,388,9,157,152,16,1,1356,88,105,101,37,29,0,1428,109,8,136,45,36,52,113,40,1432,61,12,145,137,285,25,453,41,53,1436,57,313,1440,317,69,73,77,541,177,89,321,189,325,97,329,529,533,125,129,205],[127,3973,28672,495617,33030144,2113929216,6442455968,25769807906,34359902243,483192733744,8522020421664,26414048874752,105553116397953,985162427401088,16888499407946496,17180037121,25779769344,26642223104,18014467238035457,36029347580248065,504403159083909120]),([v3,v298,v2,v251,v5,v6,v40,v241],[680,33,1444,149,13,548,157,9,489,1448,5,1420,1408,401,141,25,29,217,109,113,1416,69,688,40,88,696,105,1356,0,37,45,700,704,125,12,16,405,73,85,253,261,269,65,213,1308,1412,1452,93,293,301,417,133],[63,458,7688,57352,67598,394248,1574408,6291589,58720768,469794816,541065220,7516454912,25771376640,34363933376,206160560256,6357124,824636080256,3298537504896,4398047559680,26388279132164,105553116660224,140737623621632,8796160229376,281749922021376,562950089244672,8797167091712,1125908497367040,2251808404537344]),([v245,v20,v3,v2,v55,v5,v6,v40,v241],[188,760,80,5,149,9,249,1468,1348,1472,209,333,213,341,129,57,33,161,1044,772,88,45,41,125,196,489,349,377,85,17,29,553,201,1476,557,401,417,561],[7,24,96,896,3072,12288,16384,32768,65536,131072,1835008,3072,12288,6291456,25165825,33554512,67108880,134217744,67108880,6291472,8388632,96,3136,12352,272629824,96,536870912,1073741824,2151677952,4303355904,8589944832,17184065536,34359740416,2151686144,68719484928,137451536384]),([v299,v3,v2,v5,v6,v40,v241],[1492,5,20,21,1496,13,404,1464,208,69,16,9,1500,105,8,17,1504,0,25,248,101,88,1508,37,4,109,45,41,1488,113,40,1512,61,12,161,149,141,225,29,33,804,53,57,65,77,81,245,573,93,97,213,209,229,521,401,525,129,529,193,125,205],[255,3840,520192,33030144,234901504,16911433728,51539613984,206158536736,1924157931553,2199191031842,4954513211425,8796093123072,52776570718976,211106366757376,844448552454400,3377699729014784,15762598830051328,54043202507866112,217298682163236864,288512132729798656,1801439857524871168]),([v20,v3,v2,v5,v278,v6,v40,v241],[260,1516,13,1,105,1520,209,272,16,276,1524,88,37,1480,29,224,45,284,129,1528,61,292,57,296,5,9,264,473,141,20,149,388,145,65,69,1088,404,81,177,93,1312,17,1304,285,577,229,333,565,113,401,545,1464,213,41,1468,1316,529,533,553,125,205],[7,9,240,3841,61440,983040,15728640,251658241,285212752,3774873600,4311764992,1090846720,1095761920,25803358272,103112769793,154652401665,292091592704,566973431808,16492674940992,26388279083104,246290604884032,1970324841168960,6755399441063936,9043483139244032,54324670509350912,72092778410819584,144115188081119232,2017612633066438656]),([v3,v2,v5,v300,v6,v40,v241],[688,161,149,9,33,137,1536,1540,17,141,25,225,1468,40,5,13,1544,404,1548,29,1552,37,1556,1560,41,1564,45,145,57,113,585,405,69,73,16,1,77,81,85,89,261,269,12,65,0,101,105,109,117,696,88,4,8,36,61,125,121,129,133],[127,3984,258064,8126484,260309008,1879064656,15032386696,51539619851,210456543241,829004185609,3303366721608,30786325579200,105553118364800,211106308031616,281475782018368,3940649677619200,13510799007940608,18018797361299520,175921972641792,108086460315336768,468374361850511424]),([v263,v20,v3,v2,v5,v6,v40,v241],[888,16,876,88,149,20,5,120,69,9,209,1316,17,25,1304,1568,1468,1444,213,129,1312,41,1464,61,57,113,872,13,1,1572,896,169,29,680,109,900,904,908,40,884,473,141,589,145,377,593,65,73,85,261,269,229,521,597,301,533,125,277,601],[15,240,771,64512,458752,7864320,58755072,201326593,268435457,1610621952,15032516608,120261181441,412350513152,1649267442241,6597069775936,8800388120768,17609368010816,37383428997184,211106232541952,6442451712,281474978808576,1688849893819136,4831847424,15762598697903104,18014398551434240,6445072384,36028801355907072,506654958114832384]),([v301,v3,v2,v5,v6,v40,v241],[1584,5,20,33,1588,13,404,1464,300,69,16,9,328,105,52,1592,25,0,1596,101,8,29,1600,4,37,45,41,109,1488,61,40,1604,113,12,161,149,17,21,928,145,309,233,57,65,73,77,177,573,93,269,213,209,229,521,301,129,529,417,533,125,205],[255,3840,258048,33292288,236191744,16911433728,51539872032,481036435489,1649274257440,2199124181026,4542196351009,26388279167744,35184378382848,211106299906560,844448552454400,3377699726917632,15762598763233280,18295948916654080,109212291033202688,432345571213180928,1765411060439056384]),([v20,v3,v2,v133,v5,v6,v40,v241],[348,1608,33,1,16,356,1524,328,25,1576,17,316,101,1612,213,364,45,368,129,1616,61,376,57,380,5,9,352,473,20,149,388,141,145,349,1128,404,69,73,77,177,189,1464,209,1312,29,169,1304,229,41,1468,1316,577,113,525,341,609,417,549,553,125,205,613],[7,9,241,3840,61440,983040,15728640,251658241,1895825408,2164262144,4311764992,8607039488,4316987392,51573162001,206191986177,343630954496,618509107200,1168268853248,6597069767168,131941395873792,431008558874624,1688849865506816,2286984185800192,140737489142784,13510798886307072,54183933017079808,216172782119043072,4323455642280132608]),([v3,v2,v5,v6,v302,v40,v241],[568,161,149,9,21,1624,1628,17,1632,25,1636,1640,29,145,37,309,1468,40,5,13,1644,404,1648,41,1652,45,57,61,585,65,69,73,425,81,16,1,85,89,189,97,101,105,580,52,0,109,125,117,12,77,4,121,8,36,113,129,133],[63,2004,63504,4128784,63176784,470024240,3758097161,13958662152,51539804171,207269920777,825841680424,3298534902528,30786325578624,37383449871104,211106903622176,1970324836997152,36283921483776,2251800015032352,13510798945026048,18295873687519264,108156759968841760]),([v265,v20,v3,v2,v5,v6,v40,v241],[1012,16,1000,580,149,20,5,992,69,9,1468,1392,209,213,1316,29,37,1304,1656,229,1312,41,1464,113,57,61,996,13,1,285,17,560,1660,1020,45,1024,1028,1032,40,1008,473,141,145,625,349,629,77,81,85,189,97,525,129,529,617,193,125,205,613],[15,240,771,7168,516096,7864320,58998784,201326593,268435457,3758098432,12884975616,120261181441,412350678016,1649267442241,2200096999616,13194139607104,17609368010816,39582452417600,1610613504,211106232599296,281474978808576,1688849893819136,5368784896,1613234176,2251800929632256,31525197393764352,36028797060980736,508906757928517632]),([v20,v3,v2,v287,v5,v6,v40,v241],[1056,1064,13,1,16,1472,1000,1036,333,1476,17,776,37,29,1068,136,45,1076,41,1668,113,1672,1084,1468,40,5,9,1052,473,20,149,1060,141,145,201,69,77,81,85,261,269,209,1308,1088,229,1316,129,1312,57,213,577,525,553,529,617,125,417,277,561],[7,9,241,3840,61441,983040,32505856,503316481,3791650816,4328523008,8623501312,1107623936,25804406784,34426847249,34426848512,240585285632,309305016320,1683695337472,2199031644672,13194139545632,263882793025536,316676531814400,1688849860273408,17592186831872,2251816996701184,32088147345285120,108086391057948672,468391953433886720]),([v20,v3,v2,v5,v288,v6,v40,v241],[1096,1108,13,1,25,17,1104,68,16,1472,876,1036,341,1664,29,780,45,1116,41,1676,61,1680,1124,1468,40,5,9,1092,473,141,20,149,1100,145,201,65,69,73,85,189,97,1304,1128,209,577,557,521,597,125,401,213,129,1316,1312,57,533,205,561],[7,9,241,3841,61440,983040,32505856,503316481,570425392,7549747200,8623509504,2181365760,19361955840,240585277472,68786585857,68786606080,343664754688,1718055075840,6597069767216,26388279087136,255086697906208,844424931180576,1125899915239424,15762598698156032,22518015319867392,2251799814488064,36028814201995264,218706056905490432]),([v142,v3,v33,v2,v5,v40,v241],[1712,33,169,13,1684,21,77,492,37,20,101,69,88,461,105,25,17,1716,45,341,109,616,61,425,1720,113,141,157,281,41,604,233,57,237,241,1,285,245,1724,261,1708,249,325,521,525,201,229,277],[127,1984,14528,114757,1970240,65011776,67109792,201328800,268517411,3826384928,31188844576,34359738384,68719542529,412318040448,1649317773696,68853762049,2336463390848,4947852658816,8865350615041,17596531425281,246290658230272]),([v238,v142,v3,v2,v5,v40,v241],[1704,101,37,8,304,20,141,21,1724,1,492,161,1728,285,17,1684,109,201,1732,113,1708,33,213,13,88,9,77,105,25,169,45,345,1736,93,377,221,501,129,57,237,241,153,381,177,261,269,273,525],[63,244,3844,28676,98305,1966340,14717058,117442562,939544578,3221225739,12952797186,51573164176,68855812225,138512695489,1924146135184,6597069797376,8797166766593,123149631621120,1073770497,141012501286912,138513612801]),([v3,v2,v303,v5,v6,v40,v241],[408,157,141,9,13,1776,0,49,16,33,17,21,25,1780,169,37,1784,41,604,45,57,1788,61,4,69,285,77,81,85,89,93,97,209,105,101,245,8,620,36,616,125,40,12,109,113,229,133],[31,1009,7216,57488,983184,7604240,25174025,50335784,218144808,822673417,3244294153,12884906080,17255407616,515396665344,8246343499776,4362113056,8800388583456,17592192341024,8796160761856,17592259485696,107202390589440]),([v3,v304,v2,v5,v6,v40,v241],[1820,0,21,5,13,1408,1824,157,9,473,285,141,281,1828,29,49,165,37,1832,217,149,45,201,1836,61,69,16,4,17,25,101,109,8,128,36,1420,113,40,12,73,81,85,1320,89,93,97,209,245,261,401,181,193,125,133],[63,1004,7209,253960,3932200,30408744,234889536,805307395,1208098816,32214614016,515421241344,550057805057,1099545321793,15393198702912,57174663364928,70369818051585,140737759151105,844424955298817,1128100006338560,2269392025051136,13510833269899264]),([v305,v3,v2,v5,v6,v40,v241],[1872,149,0,13,1844,21,1876,9,69,8,1880,16,333,25,17,68,37,88,1884,101,4,45,109,1868,61,40,1888,113,12,1,141,449,29,49,453,41,233,57,237,241,285,289,77,461,1320,85,253,201,633,209,521,401,525,129,345,125,121,133],[63,4032,28677,2064384,6292032,528482304,1610614064,2147504227,30065557552,111673344096,962274000944,3299071770881,30786863236352,105553120461248,439805389309184,562954248929281,1688884224213056,6755537081352193,27021602063908928,108090789313904640,189151184555081792]),([v14,v3,v2,v231,v6,v40,v241],[1840,13,1892,69,333,1896,404,17,25,101,1900,37,1904,1908,109,45,113,1912,1916,61,1,141,21,221,52,449,29,49,41,57,237,285,289,9,77,1320,245,249,89,93,209,85,1868,401,193,125,129,133],[3,124,496,7728,57360,983088,15728684,54526112,205524000,406888448,1615593504,15033442441,51540659212,481036378120,584117387276,1099528408704,3298534940800,13743896133760,59904,22557169028096,246290605449216]),([v14,v3,v2,v5,v306,v6,v40,v241],[1920,13,69,1924,1928,404,25,20,620,88,341,1848,1852,109,1932,45,1936,113,1940,61,1944,1,141,21,449,17,49,41,57,237,285,289,1688,1684,9,1320,177,249,89,321,93,97,329,209,0,401,37,85,1772,1692,181,1868,193,197,125,129,133],[3,60,81,912,7696,122880,1966080,14680068,58720273,75497616,75500560,209747968,814219264,3256877060,30066933764,34361838596,1030792183812,7696584015876,26388312621057,8796126577665,8796126617600,35184406298624,70403103918080,140741783429120,844424930787328,1125899906950144,15763698207951872,126100789566930944]),([v307,v3,v2,v5,v6,v40,v241],[1976,49,0,13,408,16,1980,69,8,9,209,25,105,68,101,88,1984,37,4,245,109,45,1868,125,40,1988,61,12,1,141,137,17,21,1948,29,33,217,365,57,285,77,81,85,89,93,97,373,357,113,117,181,121],[63,976,7173,516096,3670336,264241152,1879048728,6442453065,60129738760,206160527434,317928243208,549755816577,3298535080592,13194141631168,52776658797200,70368744328193,140737490979904,844427178280961,1130297955598400,2533292075319296,68830625856]),([v14,v3,v2,v5,v308,v6,v40,v241],[1992,13,69,16,1996,408,2000,25,20,128,88,29,1956,37,1964,245,1804,45,1796,113,2004,61,2008,1,141,21,449,17,49,129,57,237,285,289,1688,9,1684,81,85,249,89,369,93,97,329,0,209,577,401,101,1772,1692,125,133],[3,124,145,1808,30720,491520,7864320,58720260,234881041,50331920,302000128,838991872,3256877056,13027508228,120267735044,137447354404,4123168735236,30786336063492,35188801273857,211106366758913,70368878559232,281475113549824,562949953425440,292058169344,3382097769136128,274878308352,4398048618496,13510799421210624]),([v309,v3,v2,v5,v6,v40,v241],[2016,49,0,13,304,33,328,69,16,9,404,209,25,105,2020,101,8,37,2024,4,129,109,45,1868,125,40,2028,61,12,161,149,17,21,213,517,365,57,285,73,77,81,85,89,93,97,357,113,181,133],[63,1984,14341,1032192,7421952,528482304,1610613272,6442471433,25770197002,34364997642,73215770648,412316865153,1649267835520,6597073977984,26389025653248,169985,35184376305665,70371092992001,142936515985408,70918701711360,281475200073728]),([v3,v143,v2,v310,v5,v6,v40,v241],[2136,33,21,2140,13,153,141,9,2032,145,388,209,25,225,29,2144,229,109,233,57,237,113,241,88,1192,2148,404,16,105,37,45,2152,136,61,2156,69,65,73,169,85,253,93,269,2124,177,2128,2160,189,2164,2132,293,301,125,133],[31,228,1804,14342,49166,458820,7864324,125829248,150994944,268439553,536903688,7524712448,25780289536,34393292800,206158434464,274877923464,1649267572896,6597071863968,8864812503041,274877923592,123145335996416,985162420584448,268455937,1126449931227136,2254067558518784,275951796224,8600436744,13510798884405248]),([v311,v3,v143,v2,v5,v6,v40,v241],[21,2032,33,388,2168,1192,2148,404,69,25,2172,105,2124,169,29,109,2128,45,2160,113,2164,61,2132,153,141,9,209,49,449,2176,41,53,57,237,317,16,88,77,2180,136,2184,65,73,85,93,641,337,125,117,529,533,129,133],[31,224,288,7680,24594,491552,7864320,1045,58720260,469764100,536887317,3355574276,30066868228,103112769568,3584,137975824400,893353361408,1168233725952,6597111711744,33579024,8796135096320,17592230084608,35184372108800,70368744344064,422212534274048,562951027318784,1125972923400208,6896136931639296]),([v3,v143,v255,v2,v5,v6,v40,v241],[2188,33,2192,21,2196,2164,141,120,108,265,9,209,25,225,29,2200,229,109,233,201,237,93,40,88,2204,1,16,1192,105,2208,37,45,2212,2216,189,2132,12,69,2124,169,2032,2128,2160,113,65,73,325,85,253,269,293,261,301],[31,488,1608,14346,49290,458824,3670024,29360160,234882048,268439557,1610645504,15032516608,120261181440,171798691840,274877913089,1649267490816,6597069963296,8830452760608,52776558138880,70918500008960,422212465198592,562984315257888,268455937,1266637663768576,6772991629201408,551903444992,51541721088,2818048]),([v254,v3,v143,v2,v5,v6,v40,v241],[21,2164,141,120,108,40,88,2220,2132,69,25,2224,65,2124,29,2228,169,2032,109,2128,217,2160,93,145,2232,2236,149,265,9,209,477,377,645,649,57,237,113,241,1,16,404,285,2240,77,2244,2248,61,12,73,325,253,653,413,333,509,513,45,429,125],[31,226,768,15360,245760,3932162,4194562,125831172,402653189,1619005444,8486924,15033696260,257698037764,1924413784064,2199040039936,13194139566080,52776559443968,211174952009984,281475379368960,562950221938688,1125900310806528,2251868801597698,4503599627443200,63050394784501760,70437463659520,216172782114914304,70437463720192,288230444872499200]),([v3,v143,v2,v5,v248,v40,v241],[2252,417,33,37,21,2032,421,2256,153,141,120,9,209,25,225,2132,2164,29,237,2260,229,2264,109,233,61,88,69,425,81,105,101,12,77,45,121,65,73,169,85,253,189,97,641,293,125,117,113,133],[127,3984,61461,459792,16253584,17137680,503318536,1610620937,6442680328,9670492168,19344228360,103146334209,137439152384,824707647488,3298618804224,4398046715905,9071512526849,52810934689792,137444917248,70368744210464,158329696452608]),([v3,v2,v312,v5,v6,v40,v241],[1148,1,141,69,13,473,16,49,33,2308,0,17,21,25,2056,29,77,309,2312,41,2296,109,233,2316,57,2320,113,2324,4,9,65,461,85,249,93,105,37,45,8,620,36,61,40,12,117,341,425,125,129,133,920],[63,2001,14864,245904,16515216,260050960,805322763,1073750538,2147598858,12887261193,17280532491,34359748096,68988026880,2061586661376,15943019266048,34359845376,171801059840,19792383713792,35321813483520,72567868178432,2111062428352512]),([v313,v3,v2,v5,v6,v40,v241],[2344,21,20,13,2348,5,0,2352,69,16,9,2356,1,4,25,285,17,37,29,77,2360,45,8,128,85,36,61,40,2364,93,12,2048,141,281,49,485,41,149,2340,57,2368,537,169,157,173,161,101,105,245,293,297,261,301,305,129,533,201,205,2372],[127,16256,114768,927744,66060288,2088763392,2147488163,12884951088,51540002848,481054162977,1787511701537,2199023309072,30786325846032,35255256879232,35737080696960,211106232827920,1970324854849552,15762599501152272,18018796574083072,36028797891774464,522417557598109696]),([v31,v3,v314,v2,v6,v40,v241],[1792,13,2048,25,285,20,404,1436,17,2376,69,157,2380,37,29,2384,45,2388,2392,41,2396,61,2400,2404,57,52,21,225,141,221,49,237,1440,65,1,101,105,169,217,201,77,153,541,249,665,325,669,129,529,533,205],[3,508,3668,28688,2064400,66060304,235929772,872418948,1140879360,1142521984,6536822912,25769810953,240518189065,343631495176,558404468744,7696581416961,26663157533188,106102897248772,422246825381888,562949980712960,1267187210289152]),([v3,v315,v2,v5,v6,v40,v241],[2420,149,0,21,2424,20,13,2428,153,141,2048,69,25,225,2104,213,49,2432,37,2408,229,45,57,237,2436,61,241,2284,1,8,9,16,333,68,341,88,4,41,85,93,40,12,65,77,217,161,89,265,633,101,105,109,113,117,121,125,133],[127,3992,28699,1015832,3227656,264241176,4026550400,4294971397,128849412096,412855844864,3848475246592,4398314952705,8796093418880,123145304426496,422762271214720,1688849860530177,3377699722645504,13515196978958337,2814749769482240,22526794414817280,108086391110385664]),([v31,v3,v2,v5,v306,v6,v40,v241],[1920,13,69,1924,1,404,1928,17,388,2440,620,88,341,2412,1852,45,1932,41,2444,61,1940,57,1944,141,21,25,225,20,49,237,65,157,2036,2032,161,2048,177,249,201,105,0,109,113,29,129,2088,2044,2284,205],[3,60,193,3840,31232,491520,7864320,25165844,117440577,419430656,285225024,285376512,556269568,1107296276,32212516880,36507234320,206158561296,277027487760,1649300996097,549789372417,2748812754944,4399155904512,8830452768768,17596481404928,105553118887936,17592186441728,140737490989056,299342042890240]),([v316,v3,v2,v5,v6,v40,v241],[1148,49,16,2460,13,0,2464,69,8,1,9,105,25,68,101,88,2468,37,4,85,45,41,2284,125,40,2472,61,12,141,489,17,21,2476,29,33,2456,53,57,65,169,157,217,161,201,373,245,565,113,117,129,529,121,205],[63,1985,6184,516096,3670336,264241152,805307025,3221229656,64424706064,68722098258,159018647568,274877911688,1649267638785,6597071864384,13194240197121,17592186198024,105553118369856,422213639475208,1689399618306112,2392545997029376,5075345776574528]),([v31,v3,v2,v5,v308,v6,v40,v241],[1992,13,69,16,1,1148,1996,17,388,2336,128,88,37,2448,29,1964,45,1804,129,2328,61,2004,57,2008,141,21,25,225,20,49,237,65,2036,157,161,2032,217,249,573,201,0,68,52,105,373,245,337,113,169,41,2088,2044,529,533,553,205],[3,60,193,3840,61440,983040,15728640,50331668,234881089,318767360,570445824,570753024,1112539136,2214592532,64425033744,8589959216,481036599312,558349942800,7696648503297,26388346191873,114349276659712,140739707142144,281474976718880,563022968651776,3378249480536064,4503668347650048,9007199260004352,54043745288716288]),([v3,v2,v317,v5,v6,v40,v241],[1148,1,141,9,33,489,2088,40,13,2488,0,17,21,25,361,2068,2492,29,2496,37,389,2076,2500,41,2504,45,49,657,57,237,93,585,12,69,65,265,73,77,157,81,85,89,161,97,2204,88,4,8,36,61,101,105,109,261,301,189,193,201,129,205],[63,2004,64016,4132880,264306704,4026564624,12884934667,120259093000,962073460745,3298572632075,13195481743368,11776,123145303228416,422212527980544,562955590598656,3377699721060864,6755399478813184,27021616017874944,5629499589525504,108086529570144256,1008806317638320128]),([v318,v31,v3,v2,v6,v40,v241],[2088,17,25,40,2508,20,21,1340,1000,409,2512,69,65,161,2192,1,73,52,29,105,2516,169,2520,129,2524,41,113,57,201,13,1148,9,16,2528,37,209,45,93,141,49,237,325,173,217,677,673,553,529,617,189,433,661],[63,1013,130052,4063492,63438852,469767172,536887296,7516225538,60132818946,103133741058,137707389954,278099165248,566938829008,618529816656,1237219017792,6615326556160,26391538073600,35184707668992,492598446784512,1688867310666752,2260733647651840]),([v319,v31,v3,v2,v5,v6,v40,v241],[88,388,876,2092,21,20,141,1420,157,2044,161,1,2032,2332,105,2532,25,0,2088,2200,169,129,2036,41,2084,61,57,201,13,9,16,1148,2536,285,213,29,2196,109,2540,2544,93,1816,409,49,377,233,681,237,65,265,73,217,677,269,261,533,661],[15,240,16128,245760,1835008,31457280,234889728,268468224,3758098432,12884934656,120259608576,962081062912,3298669109248,536873040,4402341576768,8830453285056,123282749653056,141837134200896,1970324837042176,36507748608,6755399986317312,9007199422515456,51539689472,137447424000,18295873620475904,51550093312,36028831546482688,74310493505847296]),([v320,v3,v2,v5,v6,v40,v241],[2088,21,40,13,2556,149,0,2560,9,16,2564,1,12,69,25,65,2220,37,88,2568,77,4,2572,45,8,2576,41,36,61,57,93,2048,137,2580,285,141,501,29,145,517,868,693,237,697,265,537,157,173,217,161,201,109,333,509,513,113,129,341,493,497,533,205],[127,16256,49232,4128768,264241152,1879053312,15032388002,120259118128,2070175809568,2482604343328,13194944840736,52776558184464,211245820545152,844427148920960,1688850397137920,154619904016,33776997276614672,36028797555885056,1080863910675349504,1152921505413334016,2379026503762445312]),([v31,v3,v321,v2,v5,v6,v40,v241],[2584,13,388,88,2092,876,9,2588,1,404,2592,17,77,2228,169,2236,109,2596,41,2600,113,2300,57,1764,20,49,616,21,237,25,225,233,241,157,2044,161,2032,105,0,2088,29,129,2036,2084,61,201,65,69,73,2048,217,677,189,689,341,433,125,205],[3,60,960,3073,61440,983040,15728640,251658240,402653504,1744831489,167792640,2550464512,4702863360,128851116288,412853731329,1649267449856,15393163051008,52793744293888,492581746114816,562958543380736,3377699720790336,13510807476240640,137975844864,137976152064,70369286291456,18016597533016064,36046389211316224,216174981141495808]),([v322,v3,v2,v5,v6,v40,v241],[2608,49,20,33,2612,13,0,328,69,16,9,404,105,25,2616,101,8,29,2620,4,37,45,41,109,2284,61,40,2624,113,12,1,149,928,17,21,309,57,65,73,169,157,217,93,161,269,565,301,129,529,533,201,205],[127,3968,12368,2080768,14761984,1056964608,7516193825,25769828400,34360164386,6307874,86318776353,412316869904,1649267835904,2200101209088,30786745009152,176144,35184376311824,74775783284752,422762225221632,562950390054912,3518437615747072]),([v3,v2,v5,v6,v323,v40,v241],[2636,1,149,2640,9,21,2644,17,25,2648,2652,29,49,37,309,2088,40,13,0,2656,41,2660,45,57,237,61,585,65,69,73,425,81,580,16,404,85,89,189,97,101,105,109,125,117,12,77,4,121,8,36,113,129,133],[63,996,31776,495712,7868449,125829664,939524432,3489670160,30064771090,103354466320,412618850832,1649267450176,262592,3298539602240,13194307306240,123145302322688,2748783797248,140737530309120,844424937996288,1143492134830592,6759797525316096]),([v265,v31,v3,v2,v6,v40,v241],[2088,17,25,40,1008,20,21,992,1000,409,2664,161,65,1,2668,101,105,29,560,37,2672,217,2676,41,113,57,61,13,2680,9,285,52,2684,641,45,525,141,213,49,237,241,77,157,173,705,85,677,189,673,669,129,529,617,193,125,205,613],[63,1013,15620,1032196,15794180,117460996,134479872,4026540034,15032909826,18267242498,34426863619,69256356048,416612352064,292071407696,1649334566977,32989644333056,105553666777088,989560532131840,7881303652859904,9009398362423296,127226689548730368]),([v31,v3,v2,v5,v288,v6,v40,v241],[1104,13,9,1096,1,1108,1092,17,388,1036,2696,2700,876,341,2688,29,780,45,1116,41,2704,61,2708,201,1124,141,21,25,409,20,1100,49,389,237,65,69,73,1148,161,2048,157,85,677,105,0,109,125,2088,169,129,2044,2036,57,533,205,561],[3,60,193,7936,122880,1966080,31457280,100663316,469762113,1711276032,6509600768,2215247872,8667529216,120393302032,962072674320,1099511668752,6871948197904,274888392720,26388413284353,8796227280896,43980599853056,70386066653184,422212465082368,3940649678667776,5629499548893184,562949955026944,9007199269453824,54606145492877312]),([v218,v3,v16,v2,v6,v40,v241],[2380,21,285,13,2124,33,65,644,25,20,105,69,52,457,101,37,29,2728,109,333,45,428,113,405,2732,61,145,153,165,41,412,53,57,313,317,1,169,177,2736,189,2724,249,265,529,533,201,129,205],[127,1984,14528,114773,1970240,65011776,67109792,201328800,268517427,3826384928,31188844576,34359738384,68719542529,412318040448,1649317773696,68853762049,2336463390848,4947852658816,8865350615041,17596531425281,246290658230272]),([v87,v218,v3,v2,v6,v40,v241],[2720,105,25,8,212,20,145,33,2736,1,644,161,2740,169,29,2124,45,201,2744,61,2724,21,209,13,52,9,65,101,37,285,109,337,2748,93,349,137,517,229,57,313,317,157,353,245,189,97,329,533],[63,244,3844,28676,98305,1966340,14717058,117442562,939577346,3221225739,12952797186,51573164176,68855812225,138512695489,1924146135184,6597069797376,8797166766593,123149631621120,1073770497,141012501286912,138513612801]),([v3,v2,v119,v5,v6,v40,v241],[600,153,145,9,13,2788,4,49,16,21,2136,285,25,29,33,37,2792,41,412,45,53,57,2796,61,0,69,65,73,169,85,93,105,213,101,177,8,432,36,428,125,40,12,109,113,129,133],[31,1009,7312,58416,2031760,14958608,50332681,234886152,302022696,571015177,1119879177,2231374848,12884934752,257698627584,4123181187072,4362114048,4398114214912,8796172719104,4402342101024,8796105646112,53601205026816]),([v3,v324,v2,v5,v6,v40,v241],[2828,4,33,5,13,1324,2832,153,9,473,2836,17,49,281,25,169,145,165,2840,217,149,109,201,2844,113,69,16,0,105,29,37,45,8,60,36,1340,61,40,12,73,81,85,1404,253,93,269,213,293,301,177,189,417,125,133],[63,1004,31752,230441,3932200,30408744,234882368,402670592,1610645507,32214614016,515421241344,549789386048,1100082086145,15393198702912,57174663364928,70369012663296,142936782423040,299067187940352,562950492684289,3377699745726465,13510833269899264]),([v325,v3,v2,v5,v6,v40,v241],[2860,149,4,13,1844,33,2864,9,69,8,2868,16,136,25,52,2872,105,0,341,37,29,109,45,2856,113,40,2876,61,12,1,145,17,49,449,453,41,53,57,313,317,65,457,1404,169,173,85,89,201,633,213,229,337,125,117,529,417,533,129,133],[63,4032,258048,1835013,6292032,528482304,1610614064,15032483888,17181180003,107378376800,962274000944,7697118364928,26388816986369,105553120461248,426611249775872,562952102051841,3377701872271424,13511898603552768,18577382827884608,108086528698220545,436849164060459072]),([v139,v3,v2,v231,v5,v6,v40,v241],[1904,13,69,2880,1896,404,20,432,52,333,2848,1840,37,45,2884,109,2888,61,1912,113,2892,1,145,33,49,453,29,41,57,313,2712,2124,9,1404,169,173,245,249,253,257,93,269,273,25,213,4,85,2784,2716,293,2856,301,305,417,125,129,133],[3,60,464,3856,4113,122880,1966080,14680068,25165904,25167376,109051921,159416320,814219264,7518355460,8592033284,51608813572,1030792183812,7696584015876,8804682957824,52776625242113,70369818025984,422212465721344,17592253154817,562949953528320,7882398860051968,17592253194240,9007199322505216,126100789566930944]),([v139,v3,v2,v5,v306,v40,v241],[1852,13,2896,69,341,1928,404,105,2900,25,1920,29,37,2904,45,109,61,1940,2908,113,1,145,33,137,17,49,88,453,41,57,313,65,1404,169,173,9,177,249,253,93,213,2856,301,85,417,125,129,133],[3,124,1968,6256,57360,983088,15728684,54526752,205522976,306225152,1615593504,6443500300,60130600969,481036378120,554052616204,1099578739584,57984,7148973851392,9895604709376,20340965902336,246290605449216]),([v326,v3,v2,v5,v6,v40,v241],[2920,49,4,13,600,16,2924,69,8,9,136,105,2928,25,0,52,213,37,101,177,45,109,2856,125,40,2932,61,12,1,145,221,1948,17,21,29,33,217,365,57,65,73,169,85,253,93,373,293,113,117,385,121],[63,976,64512,458757,3670336,264241152,1879048728,15032397832,51539738697,206160527434,311485792264,1649267454608,2199023387265,13194141631168,17592286708368,35184372299777,74766792796224,422216864903168,562949956239424,1266654675861505,68830625856]),([v139,v3,v2,v327,v5,v6,v40,v241],[2936,13,69,16,2940,600,2944,20,60,52,17,2912,25,1952,37,177,2812,109,2804,61,2948,113,2952,1,145,33,49,453,29,229,57,313,2712,9,2124,73,169,173,85,249,253,369,93,269,273,105,4,2784,2716,213,577,417,125,133],[3,124,912,15360,16401,491520,7864320,58720260,50331792,100668416,436207633,637665280,3256877056,30073421828,34368133156,206435254276,4123168735236,30786336063492,35184372090912,70437732089857,279173267456,426610513674240,1688850128705537,274878304256,4398048613376,562950222020608,2251800084742144,13510799421210624]),([v328,v3,v2,v5,v6,v40,v241],[2960,49,4,13,212,21,136,69,16,9,404,2964,105,8,25,2968,0,213,37,101,229,45,109,2856,125,40,2972,61,12,161,149,209,501,29,33,365,57,65,73,169,81,85,253,93,97,293,113,385,133],[63,1984,129024,917509,7350272,528482304,1610613272,6442500106,25770067977,34364983306,86100672536,412316910208,1649267704449,6597073963648,26389025653248,446464,37383399561216,70506384506880,140737492944897,70377535700993,281475200059392]),([v329,v3,v2,v330,v5,v6,v40,v241],[21,3044,33,1780,13,52,1220,3048,404,9,16,3052,25,101,37,109,3056,45,68,113,61,3060,157,145,1696,141,388,17,213,309,129,53,57,313,317,69,285,77,81,85,89,93,97,245,3036,3064,261,3068,3040,181,193,125,205],[31,992,1088,6146,24586,491552,3670048,12583428,117440518,134219783,805322757,3229745156,30065819652,34359738496,68853694978,412321071616,1649271767552,6597075010048,68870471682,137455747082,61572651286656,492581210292224,134242314,68853858304,135790626,563499709390848,1128236370116608,6755400515977216]),([v152,v329,v3,v2,v5,v6,v40,v241],[1220,3048,404,33,1696,21,388,3072,69,285,17,37,101,3076,45,3036,109,3064,61,3068,113,3040,16,9,52,3080,65,3084,68,3088,157,145,213,49,453,41,233,57,313,241,77,81,85,93,641,521,525,345,125,121,229,133],[7,248,257,1680,14480,245761,3932160,8360,29360129,100663424,14464,419512320,554958848,3229614112,33555624,30064775200,111669215264,962073722912,8390272,3299617017856,4399128707072,8797176201216,17592186059904,35218731894272,70506200958080,140737488443392,844429226151936,3659174698352640]),([v329,v3,v255,v2,v5,v6,v40,v241],[21,2192,33,3092,2196,3068,40,52,2204,1,16,9,1220,2208,25,101,3096,37,109,2212,45,2216,261,3040,93,12,145,160,148,325,17,213,309,129,53,201,313,157,285,1696,1684,3036,3064,61,265,77,81,85,89,97,181,189,193],[31,480,7680,24584,229386,3932160,62914560,469762084,603981828,1207959565,6442582021,25837961220,103095992324,137447342080,825707462664,1101659308032,6605660749856,8796101410848,17868137695232,105553653270528,422213002987520,562949978589216,1073971208,275952959488,1103101952,1266637396410368,6790583830052864,42967498752]),([v254,v329,v3,v2,v5,v6,v40,v241],[40,3068,52,2220,33,145,160,148,3040,157,17,3100,285,1696,37,3104,77,1684,45,3036,217,3064,93,141,2232,2236,149,1,16,9,404,2240,65,169,2244,2248,113,61,12,325,213,485,349,693,713,57,313,317,265,81,89,653,413,109,393,341,493,497,125],[15,242,768,15360,245760,3932162,4194562,125831200,2013265920,6442452992,8606828544,51540918272,481036337408,550292684848,8394848,3298543337504,30786326888480,246428043575328,281475513586688,563500246188032,1126450200838144,2251937789509890,4503599627491328,27021597765276672,206158434560,252201579134124032,206158512128,288230513591975936]),([v329,v3,v2,v251,v6,v40,v241],[1696,21,401,33,25,3108,52,69,405,9,73,3040,17,12,65,3068,101,105,37,3112,109,3116,45,113,117,3120,157,145,160,137,313,213,309,129,53,285,77,81,85,89,261,641,61,181,125,121],[63,2000,63504,458801,7995408,25208848,1040187912,1342214152,6442715178,25944391688,1082165256,34426884608,206225801760,824707645952,1099587127808,2199023554592,42954428416,4398046513153,9070975975456,52845286262784,17600788563968]),([v3,v2,v331,v5,v6,v40,v241],[1196,1,145,69,13,473,16,49,21,3160,4,2988,17,65,225,29,33,37,3164,41,3152,45,53,3168,57,3172,61,3176,0,9,457,77,85,249,93,25,101,109,8,432,36,113,40,12,333,405,121,125,129,133,796],[63,2001,30864,231952,16515216,260112400,805308427,1073756170,2147615242,12887261193,17280532491,34628188160,68719609344,2061586661376,15943019266048,68719622144,17729627367424,37383496017920,206160921088,72570015711744,2111062428352512]),([v332,v3,v2,v5,v6,v40,v241],[3196,33,20,13,3200,5,4,3204,69,16,9,3208,1,0,25,17,65,37,169,29,3212,45,8,60,85,36,61,40,3216,93,12,2984,49,477,145,165,41,149,3192,57,3220,285,153,289,541,161,101,105,229,113,525,177,181,185,189,193,197,201,277,3224],[127,16256,124928,917584,66060288,2088763392,2147488163,12884953120,51540002864,481054162977,1787511701537,15393162827776,17592186442000,35255256879232,35737080696960,211106232829952,283674017826816,1688850665621504,15762598714015760,126100790372073488,1009087792330833920]),([v34,v3,v2,v333,v5,v40,v241],[2800,13,3228,69,169,2984,153,404,37,20,1384,29,1712,25,17,3232,109,3236,3240,41,3244,113,3248,3252,57,88,145,33,137,309,49,313,1388,77,1,65,157,537,217,249,717,201,265,721,105,101,285,229,521,525,277],[3,252,4016,28688,2064400,66060304,469763180,705693472,1207988224,1209631744,6603932672,25769808201,240518189120,1924145905764,15393187954788,123145302331648,35459284107520,2207671910656,439804651687936,562949980712960,1268836477730816]),([v3,v334,v2,v5,v6,v40,v241],[3264,149,4,33,3268,20,13,3272,157,145,2984,69,209,49,3276,25,2408,37,309,3024,129,45,53,57,313,3280,61,317,3140,1,8,9,16,136,333,52,0,341,41,85,93,40,12,65,77,217,161,89,325,633,101,105,109,113,117,121,125,133],[127,3992,127000,917531,7872520,528482328,8053590144,128849068032,137439084549,825710084096,7696950493184,8796093074816,17592723048449,246290607245312,845524542426240,3377699720708097,6755399443709952,27030394226393088,5629499536965632,45053588560543745,216172782218117120]),([v34,v3,v2,v231,v5,v6,v40,v241],[1904,13,69,2880,1,404,388,3284,432,52,333,3256,1840,1896,29,45,2884,41,3288,61,1912,57,2892,145,33,20,49,37,309,53,313,317,153,2976,1696,161,2984,77,245,249,89,201,17,101,4,229,113,3012,2980,3140,277],[3,60,960,7808,24577,491520,7864320,25165844,117440576,83897344,419438593,620920832,3240624128,64424771600,73014447120,137573171220,1924145479696,2203320320016,4466765989888,26388413284353,35192962416640,492581211340800,8796227243009,35184372483072,633318699699200,8796227403776,137575792640,1163283304415232]),([v335,v3,v2,v5,v6,v40,v241],[1196,49,16,3300,13,4,3304,69,8,1,9,136,105,3308,25,0,52,101,37,85,45,41,3140,125,40,3312,61,12,145,489,3316,17,21,2456,29,33,233,57,285,153,77,217,161,201,373,229,521,113,117,177,609,121,277],[63,1985,129024,393256,3670336,264241152,805307025,16106151952,51539869784,68722098258,172977291280,824633745921,1099511890568,6597071864384,13194240197121,17592186466312,105827996287040,422214717431808,1688849862754368,2392554582835208,4547580195242048]),([v34,v3,v2,v327,v5,v6,v40,v241],[2936,13,69,16,1,1196,388,3188,60,52,25,3292,17,1952,2940,29,109,2812,229,3180,61,2948,57,2952,145,33,20,49,37,309,313,317,2976,153,161,1696,77,217,249,573,201,285,4,136,88,41,3012,2980,101,373,521,113,525,177,345,557,277],[3,60,960,15360,49153,983040,15728640,50331668,117440576,167777280,838877185,168099840,3260022784,64425033744,8589940784,68987912212,962072936464,1108105756688,2199023257632,30786594013185,35326106796032,212205748355072,844425198573569,1126037346586624,6755399445255168,27303073009631232,68993155072,108087490572976128]),([v3,v2,v336,v5,v6,v40,v241],[1196,1,145,9,33,489,3012,40,13,3324,4,3328,17,21,3332,25,361,3004,29,37,389,3000,3336,41,3340,45,49,657,57,313,93,585,12,69,65,153,73,77,325,81,85,89,161,97,2204,52,0,8,36,61,101,105,109,261,301,189,193,201,129],[63,2004,260112,3940880,264243216,4028629008,12886999051,120259133449,962073199112,3298572632075,13195483807752,123145302364160,787968,422212527980544,562955592663040,3377699721101824,6755399495630848,27021616019963904,5629499572486656,108086529572208640,432345565336961024]),([v318,v34,v3,v2,v5,v6,v40,v241],[52,388,1000,2092,33,20,145,1340,153,2980,161,1,1696,3184,3012,3092,285,101,3344,37,4,229,2976,41,3008,113,57,201,13,9,16,1196,209,17,2192,2508,169,45,3348,3352,93,2824,49,421,349,53,729,313,77,325,81,217,677,97,525,189,661],[15,240,16128,114688,1966080,31457280,234889728,268697600,3758098432,30064803840,103079477248,962081062912,3298669109248,536873040,4406636478656,8830453547072,123282749653056,141837134200896,10737453312,1970324837500928,6755399986317312,9007199422515456,12885557248,12895387648,18014407267196928,137447997440,36310272130416640,74310493505847296]),([v319,v34,v3,v2,v5,v40,v241],[3012,29,37,40,2536,20,33,1420,876,421,3356,69,77,161,2196,1,81,88,17,101,3360,285,3364,229,3368,41,61,57,201,13,1196,9,16,3372,25,213,109,93,145,49,313,265,289,217,677,725,557,521,597,261,397,661],[63,1013,130052,4063492,63438852,469767172,536887296,7516225538,60132818946,103133741058,137707389954,278099165248,566938829008,618529816656,1237219017792,6615326556160,26391538073600,35184707668992,492598446784512,1688867310666752,2260733647651840]),([v337,v3,v2,v5,v6,v40,v241],[3012,33,40,13,3380,149,4,3384,9,16,3388,1,12,69,2220,25,52,3392,65,0,37,77,3396,45,8,3400,41,36,61,57,93,2984,221,3404,17,141,501,988,169,145,517,693,313,697,153,289,325,541,217,161,201,229,333,509,513,113,525,341,493,497,277],[127,16256,1032192,3145808,264241152,1879053312,15032388002,266288365600,1924147446832,2757482250272,13194944840736,52795885881472,211106235680784,844427148920960,1688850397137920,292060266512,33776997310529536,108086391594058752,1008806316612780048,808453120,1156299204931355648]),([v34,v3,v338,v2,v5,v6,v40,v241],[3408,13,388,52,2092,1000,9,3412,1,404,65,3100,285,2232,3416,29,45,3420,41,3424,61,3156,57,2776,20,49,428,33,313,37,309,53,317,153,2980,161,1696,3012,17,101,4,229,2976,3008,113,201,2984,77,69,81,217,677,261,689,333,397,125,277],[3,60,960,15360,49153,983040,15728640,251658240,402653504,167777280,1744846849,2550464512,4702863360,128851116288,412316862464,1649804312577,15393163051008,52793744293888,70377334118656,985162955358464,3377699720790336,13510807476240640,550292689920,18016597533003776,36046389211303936,550293012480,140738030469120,216174981141495808]),([v339,v3,v2,v5,v6,v40,v241],[3432,49,20,21,3436,13,4,136,69,16,9,404,3440,105,8,17,3444,0,25,101,37,109,45,41,3140,113,40,3448,61,12,1,149,804,225,29,33,57,285,153,77,81,217,93,161,97,229,521,525,609,193,201,277],[127,3968,520192,1572944,14700544,1056964608,7516193825,8590041122,51540660272,10489890,103498645537,412316959744,1649268491536,2200105391104,30786745009152,1679360,105690563645440,140737924669440,281474986676240,567365583503376,3412884503662592]),([v3,v2,v5,v340,v6,v40,v241],[3460,1,149,3464,9,33,137,3468,17,49,25,225,3012,40,13,3472,4,29,37,3476,3480,41,3484,45,53,57,313,113,585,405,69,73,696,16,404,77,81,85,89,261,269,12,65,0,101,105,109,117,8,36,61,125,121,129,133],[127,4000,127520,950308,32506401,503840800,3758097552,30064771090,104153251856,413404233744,1650475925520,15393163314560,52776558396544,105553125704832,140737656653056,491520,844424945860608,1128099098394624,87960939954176,6755433935798272,29273397721038848]),([v263,v34,v3,v2,v5,v40,v241],[3012,29,37,40,884,20,33,120,876,421,88,161,77,1,3488,105,101,17,3492,25,3496,217,3500,41,61,57,113,680,13,3504,9,169,641,109,533,145,209,49,313,317,65,153,289,737,85,677,261,725,721,229,521,597,301,125,277,601],[63,1013,15620,1032196,15794180,117460996,402653184,3758105602,4295754754,10751049730,17246994435,35433488592,206159216704,146042519632,824700846145,16492675211264,52777645514752,494780299632640,3940649684205568,4504699223425024,63613344812122112]),([v34,v3,v2,v287,v5,v6,v40,v241],[1068,13,9,1056,1,1064,388,1036,3512,3516,1000,333,3508,17,776,1052,29,45,1076,41,3520,113,3524,201,1084,145,33,20,1060,49,361,37,421,53,729,313,1196,161,2984,153,77,69,81,85,677,3012,285,101,4,229,2980,2976,57,525,125,277,561],[3,60,1984,30720,98305,1966080,31457280,100663316,503316480,1677731840,6509592577,26374438912,34437332992,481036337168,549755824144,7698728878096,26525718544400,137449439248,105553116270592,422214612549633,3940649678667776,5629499548893184,140739635849216,562949955002368,9007199269429248,140739636494336,18015500176982016,108649341021323264]),([v341,v3,v2,v5,v6,v40,v241],[3564,13,49,8,3544,16,21,3568,161,0,9,69,17,25,65,68,37,88,3572,101,4,45,109,3556,61,40,3576,113,12,153,5,285,281,3580,213,453,3152,41,233,201,709,457,77,461,85,249,253,257,93,265,269,273,169,333,293,297,405,301,305,177,341,345,125,121,129,133],[127,3984,29312,2064384,6291465,528482304,1610614804,7516209284,129923547140,412321054727,1659140833284,2199023278465,13194677192720,263882794862593,4222124851988496,4503601775394944,63067986973442049,504684633443549312,4035225266128683009,13835062453539176448,59951918239761563649]),([v3,v16,v2,v169,v6,v40,v241],[3584,17,21,388,361,153,5,69,221,3588,285,65,281,3528,13,3592,29,49,3596,37,3152,229,53,45,57,3600,61,3556,9,36,404,25,101,136,109,113,3604,52,457,77,85,249,93,265,333,405,121,125,133],[31,485,32324,2064388,14811652,251691076,268443648,3758098435,12885688323,17188258306,103179878403,412316862593,549756600481,3298543272576,13194240196737,141734710272,17609374304768,35218966710272,21483749888,70953095397376,422212576215552]),([v3,v16,v2,v5,v267,v6,v40,v241],[3608,49,388,33,3612,153,5,69,285,65,3616,2760,2752,13,29,3548,389,3152,129,45,53,57,61,317,3620,9,25,16,3,432,88,3532,109,3624,113,3628,3632,457,85,249,93,265,0,333,405,2764,37,2768,2776,3556,125,133],[31,232,778,15432,245832,1835018,14680136,50331648,83886081,2013265921,2147532801,12885427200,120263278592,137455731329,134217889,49313,824634245248,3298539077760,4398063289088,16794368,8800388514304,17609370108416,105553116299264,4295494656,422229649129472,4295508992,562967137533952,3377699725508608]),([v3,v2,v342,v5,v6,v40,v241],[3652,153,141,3636,69,49,3656,3660,5,8,20,13,3664,209,25,213,3668,37,3192,217,149,53,45,57,237,3672,61,709,3648,161,0,16,9,73,77,245,249,261,265,17,65,68,29,88,4,85,93,40,12,101,105,109,113,117,121,125,133],[127,4064,28960,491620,7864480,528482400,8053067793,9126826129,17180065819,103083409552,412417523737,1650341203968,32985349029888,35184376283776,492581578342400,1688849860415488,3377699724738688,13510798982803456,2814749771432064,22518015686017024,108086391162273920]),([v10,v3,v2,v5,v267,v6,v40,v241],[33,3612,5,388,3676,3620,9,3608,65,404,3,60,88,29,3640,3532,45,3624,85,3680,61,3628,93,3632,153,69,17,49,25,145,2812,2800,149,3192,129,349,201,73,16,249,265,105,0,109,113,2816,169,177,189,2820,2824,3648],[31,96,416,7696,61456,983040,15728640,50331653,469762052,8053587972,9126830084,51539869700,69260541956,137740943520,274928239104,50356352,549789696000,1099550425088,6597338202144,2199291699232,10995384975360,17592525783040,105553116282880,140738562883584,1970324841168896,140737489149952,2533274794614784,85903802368]),([v195,v3,v2,v5,v6,v40,v241],[3696,13,49,8,3544,16,33,3700,161,4,9,69,136,25,52,3704,105,0,29,37,77,109,45,3692,113,40,3708,61,12,157,5,3712,209,449,2296,169,165,41,53,201,709,65,457,461,85,249,89,321,93,325,97,329,285,245,333,337,125,117,341,181,185,425,193,197,229,133],[127,3984,258048,1835648,6291465,528482304,1610614804,33286094852,104154005636,412321054727,1652698382340,6597606737936,8796094335361,263882794862593,4222124851988496,4503633988255872,63050394787446785,216174981346852864,2017630225253269505,16141182539674943616,55412289815372103681]),([v3,v33,v2,v169,v5,v6,v40,v241],[3584,49,388,21,3716,157,5,69,3720,1748,1740,13,17,3684,361,2296,169,77,229,109,233,57,113,241,3724,9,16,3,620,52,3528,37,45,3728,61,3604,3732,461,85,249,93,325,1752,25,4,1756,1764,3692,341,425,125,133],[31,232,3912,61512,196618,1835018,14680136,50331648,1006632961,1073754113,2164260865,12885426432,120263278592,67109025,12449,137455861889,824634245248,3298539077760,13194139541504,17592203018240,4295492352,105570300329984,16986112,4295495936,140754672431104,281479272333312,562967137615872,3377699725508608]),([v3,v33,v2,v5,v267,v40,v241],[3608,29,33,388,389,157,5,69,137,3736,17,49,3740,25,2296,3744,169,77,165,3532,13,129,233,109,57,3748,113,3692,9,105,68,36,404,37,45,61,3628,65,88,461,85,249,93,325,117,341,425,125,133],[31,485,32260,2064452,14714884,251658820,268959744,1610625027,15032516611,17188290562,103179878403,137438965921,824633852033,3298543304832,13194240196737,275414986752,17725169664,17764219629568,35201560510464,70403338928128,422212576247808]),([v3,v2,v197,v5,v6,v40,v241],[3764,157,145,3636,69,49,3768,3772,5,8,20,13,209,3776,25,2340,3780,213,37,217,149,53,45,57,313,3784,61,709,3760,161,4,16,9,65,81,177,249,89,321,189,325,97,329,136,17,52,0,29,77,85,93,40,12,101,105,109,113,117,121,125,133],[127,4064,61540,459040,7864480,528482400,8053129233,8589959195,17717067921,515400269968,8246437871641,131941395357696,422213539135488,562949957616256,7881299716997120,27021597764575232,54043195532656768,216172791072841728,45035996278161536,360287970290761728,1729382257015652480]),([v67,v3,v2,v169,v5,v6,v40,v241],[21,3716,5,388,3788,3724,9,404,3,128,52,17,3752,3528,3584,77,45,3728,85,3792,61,3604,93,3732,157,69,141,1804,1792,149,2340,29,49,37,229,377,201,16,81,249,89,321,325,97,329,1808,285,101,4,245,261,1812,1816,3760],[31,96,1936,15376,49184,983040,15728640,50331653,1007157252,1140856836,15032385540,51539869700,68790779908,137489285248,50354176,283501412384,3848324579328,30786364375040,105553116270592,422221055000608,562950088425472,7881299352092672,140746078296096,562949954209792,10133099165784064,140746078617600,10742661120,85903802368]),([v3,v2,v343,v5,v6,v40,v241],[3808,1,5,456,9,33,3812,8,20,13,3620,17,21,105,449,3724,29,101,453,129,45,49,53,57,3816,61,3804,317,88,16,69,404,65,77,85,89,93,97,25,37,40,12,109,333,337,113,117,341,345,121,125,133],[63,997,31776,495648,7864416,260046885,4026531856,5368718352,9663840272,52614398032,207349612560,275146343424,550024282112,17180917952,3367371800576,207936,30786326634560,105557461574656,426610512756800,598142965940224,3377699772432448]),([v3,v2,v55,v169,v6,v40,v241],[3820,1,5,456,9,21,17,3796,388,3824,209,105,449,3528,13,3724,213,49,101,453,229,53,45,57,3828,61,3804,3584,69,52,65,77,85,89,93,97,4,184,36,25,37,3604,136,109,333,337,113,117,341,345,121,125,133],[63,485,32292,1015840,7471648,125829157,402653392,1879050256,2416214032,13157532176,51925483536,1030792185920,1099511635968,4299162176,2216320565312,4466766284800,61572655352320,211107423717376,853221027611136,1196270849130496,6755399496630784]),([v3,v2,v55,v5,v267,v40,v241],[3832,1,5,456,9,33,29,3796,388,3620,209,49,105,449,3836,213,101,453,3532,13,129,45,53,57,3840,61,3804,317,3608,69,65,88,77,85,89,93,97,25,0,184,36,37,3628,109,333,337,113,117,341,345,121,125,133],[63,485,15904,1032228,7358496,260046885,805306576,1610617360,6979387408,26308788240,103733526544,137439216128,4123168670272,8592048192,4432523690048,277025460736,61572653273088,211107356611072,853221025333248,1196273063493632,6755399494549504]),([v3,v2,v169,v5,v198,v6,v40,v241],[1,5,9,21,3844,3848,13,17,361,3852,3528,141,388,29,49,37,229,53,45,57,61,3584,52,404,3788,69,77,157,81,85,89,93,97,3856,25,16,101,3860,3,109,113,3864,3868,36,136,3724,245,3728,261,3604,3732,121,125,133],[15,122,938,7208,57352,475144,1572874,31457284,6291620,50331648,469794820,1610874885,6577717252,25769803808,34361835520,481040564224,549756076048,7696582443008,8796109800608,68723703968,549756076176,3298535932064,52776642052096,211106232795152,1970324838023168,618475585536,2252899393503232,13510798883487744]),([v199,v3,v2,v169,v5,v6,v40,v241],[5,3528,21,388,3876,3584,69,3788,404,17,37,101,3724,136,45,3728,109,3880,61,3604,113,3732,1,9,361,3884,29,49,453,229,233,57,241,16,52,77,157,81,85,93,3888,65,3892,3,3896,3900,577,521,525,345,125,121,133],[31,96,416,562,15392,245760,3932160,12582917,131093,50332181,469764100,1744896004,6443499525,25778192416,8389168,240526559232,274890555392,618484727808,3298534883344,13211319405568,212992,52776559443968,70385991158288,140737488568832,299069311287824,562950020614144,3377699788687360,5629500072198144]),([v201,v3,v2,v169,v5,v6,v40,v241],[49,3528,21,388,3904,9,3584,161,3788,3724,4,3872,36,17,136,101,45,3728,109,3908,61,3604,113,3732,141,221,5,33,501,476,169,37,229,233,57,237,241,52,3,153,381,69,81,245,253,257,261,265,269,273,105,88,3912,3916,521,525,125,277],[31,480,1536,14354,49664,983040,15728640,50331812,201850900,872423444,3221225477,12901941252,120263278596,412316860576,1786706403472,6600290992256,62122407231616,1055531166859392,1125899906844688,2251801961185792,851968,13510798887354368,2147508752,18014398510342144,40532413830406160,3221553152,3226468352,216172786413207552]),([v201,v3,v2,v5,v6,v40,v241],[3904,33,0,13,476,21,388,88,9,16,161,404,105,25,17,3724,101,3908,45,8,109,3912,61,40,3916,113,12,3920,141,221,501,169,37,229,233,57,237,241,65,153,381,69,81,245,253,257,261,265,269,273,521,525,125,277],[127,3968,28677,98432,1966080,132120576,939525424,1073893411,6442483746,26039418912,240704815136,1924145366017,6603512251392,62122408150016,1055531215094784,4294987777,1125899908304896,2251834223775745,6443892736,6497009664,13510807523557376]),([v3,v2,v5,v267,v6,v272,v40,v241],[1,5,9,33,17,49,25,3924,3928,13,29,389,3932,3532,145,388,129,45,53,57,61,317,65,153,73,3608,88,404,3676,69,85,93,105,3936,3,68,3620,109,113,117,3940,37,16,3944,3948,36,177,3624,189,3628,3632,125,133],[15,120,906,7434,57608,458792,3670026,29360196,503316484,100664580,805306368,1073872901,2156920836,30131880000,4362077504,103351844928,141734051904,824638963776,3298534883584,4398080065536,137439084672,26663158022144,35184640533760,137439085696,9070971979008,211106232664192,1970324838023168,6755399442300928]),([v273,v3,v2,v5,v267,v6,v40,v241],[5,3532,33,388,3956,3608,69,25,105,3620,68,3676,404,29,109,3624,45,3960,113,3628,61,3632,1,9,17,49,449,389,3964,129,53,57,317,65,153,73,16,88,85,93,3968,3,577,337,125,117,3972,77,3976,3980,529,533,133],[31,96,1952,6176,8242,245760,3932160,12582917,117440772,131093,402661397,1644232708,6443499525,60137931008,206166818848,8396848,274890555392,566945120256,3435973837184,4535502250256,8796109881600,52776575959296,211106232533008,212992,844424931442688,1125899907063808,2533276938936336,4521192351399936]),([v271,v3,v2,v5,v267,v6,v40,v241],[49,3532,33,388,3984,9,3608,161,3676,88,3620,105,0,3952,36,29,109,3624,45,3988,113,3628,61,3632,145,137,285,25,5,21,517,3992,129,53,57,313,317,69,73,3,157,353,177,89,321,189,325,97,329,101,3996,4000,529,533,125,205],[31,480,3584,5120,58384,983040,15728640,50331812,201326597,805830676,3489693716,12901941252,120263278596,412518187136,549755814560,3298534916752,31885837467776,527765585526912,134219264,134252048,201654272,206569472,562949953429520,851968,3377699725770752,4503599628255232,10133116345679888,54043199827869696]),([v271,v3,v2,v5,v6,v40,v241],[3984,21,4,13,3992,33,388,52,9,16,161,404,3620,88,105,101,37,29,0,3988,109,8,45,3996,113,40,4000,61,12,4004,145,137,285,25,517,129,53,57,313,317,69,73,77,157,353,177,89,321,189,325,97,329,529,533,125,205],[127,3968,28672,495617,7864320,528482304,3758097712,12884906018,17180557347,104157675552,962819260448,3311419790336,30786325709825,255086702363648,4222124860376064,8590102529,12890669056,13103009792,4503599633301504,9007336895184897,54043230094229504]),([v3,v33,v2,v344,v5,v6,v40,v241],[4028,49,604,21,20,157,5,69,1748,13,1740,2288,25,4032,225,169,77,41,109,233,365,57,113,241,4020,9,16,2292,620,2040,333,4008,37,245,2036,61,4036,4024,461,249,93,325,105,4,45,1756,1764,293,117,129,341,497,425,125,229,133],[31,232,3912,28748,98314,1966090,14680136,50331648,1006632961,3221237760,4311744513,25770067968,240522362880,67109025,1073746080,274894749825,558346010752,3298539077760,4398046519300,8796109897728,17592186439936,105553122557952,1073844224,140737488754688,281510414389248,3940649674276864,4503633991368704,63050394787643392]),([v67,v3,v2,v344,v5,v6,v40,v241],[21,20,5,1408,4020,9,404,4040,2336,128,2040,25,4044,4008,52,4028,77,109,2036,245,2328,61,4036,93,4024,157,69,1804,141,149,1792,29,49,37,217,377,505,201,16,333,81,249,325,97,329,285,4,85,1812,1816,101,373,293,261,301,305,129,345],[15,48,1984,30848,98320,1966080,31457280,100663301,2014314500,268441612,15032385540,120259608580,137715777540,274978570304,549856479232,1108168704016,2199091019776,30786403172352,35184372092936,70379481595920,140754804015104,844562377474048,3378258066278400,4503616808814592,63050944547391488,217298690611085312,10747904000,154627735552]),([v345,v3,v2,v5,v6,v40,v241],[4048,33,21,0,13,108,20,88,69,16,9,404,105,25,4020,2040,37,2128,45,8,109,3912,61,40,4052,113,12,153,141,209,225,29,229,233,57,237,241,65,73,169,245,253,93,269,293,301,125,277],[127,3968,12297,114688,1966080,132120576,402654244,1610752007,2147500070,13154516996,120309415972,412451087361,551903315200,3298670281728,13194326180864,2147495937,17592187498496,39719907893249,551904739328,2204123136,211110579011584]),([v3,v16,v2,v5,v346,v6,v40,v241],[4064,49,412,33,20,153,5,69,285,65,2760,13,2752,3144,37,4068,309,41,45,53,365,57,61,317,4056,9,25,16,3148,432,2040,341,4012,177,2976,113,4072,4060,457,249,93,265,0,229,333,513,405,101,109,2768,2776,181,121,125,129,133],[31,232,778,15432,114764,1966090,14680136,50331648,83886081,2013265921,6442500096,25770074112,240522362880,274894684801,134217889,2147500192,558346010752,3298539077760,4398063289088,2147500800,61572651418112,70403108110848,140737488388100,281474977113088,1688849866555392,2251799814103040,4503636138803200,63050394787643392]),([v10,v3,v2,v5,v346,v6,v40,v241],[33,20,5,1324,4056,9,4064,65,404,4076,3188,60,2040,37,4080,4012,88,45,2976,177,3180,61,4072,93,4060,153,69,17,49,25,2812,145,149,2800,217,349,505,201,73,16,341,249,265,0,105,373,229,337,113,169,85,2820,2824,181,189,193,197],[15,48,208,7936,123392,1966080,31457280,100663301,939524100,16107175940,2147508236,120259608580,139594825732,275481886800,549856477440,1099612299264,2199091019776,4398124105728,8796764110864,53876606640128,228698955972608,281475656187904,562949953437704,1125918162026496,6755536888397824,9007216436191232,126101889086398464,154627735552]),([v347,v3,v2,v5,v6,v40,v241],[4084,21,33,4,13,4088,20,52,69,16,9,404,4056,2040,25,101,37,0,4092,109,8,45,3996,113,40,4096,61,12,157,145,17,213,309,129,53,57,313,317,285,77,81,177,89,93,97,181,193,125,205],[127,3968,28672,233473,3932160,264241152,805307428,1073745958,6442778631,26309033988,240618831908,275951654144,1649535943681,6597340562432,26388652360704,1073844225,275954532352,1186992128,35184375070720,79714693742593,422221158023168]),([v348,v3,v2,v5,v6,v40,v241],[2120,33,12,76,13,88,69,16,9,404,4148,876,25,4140,37,4152,45,8,4156,85,36,61,57,93,1,5,209,21,105,213,101,41,65,77,201,161,109,333,113,341,217],[31,992,7168,24608,2064384,14680069,50331928,469763089,1610620946,2181595160,6291475,4563404096,9663684928,2165080320,51543802113,1342186496,206427423744,279445504001,550830186496,9669967873,1116696215553]),([v3,v349,v2,v5,v6,v40,v241],[4160,13,0,21,108,20,153,141,9,221,209,105,225,2132,4140,29,33,37,4164,229,109,233,57,237,113,241,88,16,404,25,101,45,8,2264,36,61,12,65,69,169,81,245,253,257,261,269,273,481,333,337,117,465,125,133],[63,984,15371,245768,3932312,62922760,469762368,536889349,1140867072,32213565440,103096000512,412316862721,1924145496320,15676631941376,123420197003520,140737488504833,844427078928385,3377871536007168,551904755712,34376687616,13510798900469760]),([v10,v350,v3,v2,v6,v40,v241],[2820,25,65,40,4168,16,1324,13,20,5,2268,9,4172,37,4176,169,4140,4180,45,333,85,2512,57,201,21,17,149,69,73,1000,52,101,105,109,2524,113,93,153,313,165,217,761,749,249,265,177,181,185,125,433,661],[63,964,3072,126980,1970180,14680068,119539202,939528243,8053112834,30065950722,103123255298,137573171920,824633778752,3298536063680,4432433512960,137573232656,8796228685840,17592334942208,246307785728000,844424940658688,1126999434199040]),([v350,v3,v33,v2,v5,v6,v40,v241],[21,1764,13,1740,2300,4168,16,1000,52,69,157,1756,4184,25,77,4140,169,4,109,1748,45,1752,113,57,61,5,604,20,65,313,41,53,749,9,2268,37,4144,4188,201,2044,173,85,249,89,321,325,333,341,181,185,125,425,433,129,205],[31,480,1632,14336,245760,3932160,29360146,234881060,33555972,335548421,536952836,3255828484,4307550213,8589967360,17448309024,34359771168,207233220640,824642109456,268441120,1099511727136,32985349882880,35459258385408,268554240,70369013923840,281018384,987361442856960,7881299356352512,27021872651567104]),([v67,v350,v3,v2,v5,v6,v40,v241],[404,4172,1000,52,13,20,5,1408,4140,9,65,4192,2268,4168,169,45,4144,85,4188,57,2332,201,2044,141,1816,149,1792,69,16,157,1812,285,101,37,4,245,1804,1808,261,93,29,313,421,217,377,761,765,81,249,89,321,325,333,125,533,661],[15,240,768,7178,24832,491522,7864320,126877760,939524097,3221227520,30064771328,240518299648,824653643776,671088720,8391872,7705171329088,61572651286592,70643632570432,671091714,140746615169280,1970325374009344,2251800353177600,12884905216,4503633987240960,274881053696,12885065728,27022705867882496,36037867992121344]),([v351,v3,v2,v5,v6,v40,v241],[4200,13,33,4,148,20,876,9,16,157,404,4148,105,101,37,0,4204,109,8,3116,45,36,3040,113,61,12,145,137,17,21,25,213,309,129,53,57,313,317,285,69,73,77,177,89,321,189,325,97,329,481,341,345,121,469,125,205],[63,1984,6208,59393,4128768,62914560,201327252,1879050244,6446653447,25838026772,240539140100,1925219092992,2199023264385,30786327216768,527765602304512,562951027173377,275952896000,1371537408,3377699721781249,13512997934735360,54043204140400640]),([v352,v3,v16,v2,v5,v6,v40,v241],[33,2776,13,2752,3156,4208,16,876,88,69,153,65,4148,285,0,2768,4212,37,45,2760,109,2764,61,57,113,5,412,20,237,77,41,233,765,9,25,3124,4196,4216,201,2980,289,85,249,253,257,265,333,293,297,125,405,397,341,229,277],[31,480,1632,30720,229376,3932160,29360146,234881060,33555972,268445700,604045317,3255828484,4307550213,8589938688,17179873312,34896675104,207233220640,824642109456,1099511641120,536938016,32985349882880,35459258385408,536885248,494780233555968,3940649682345984,4503600165552128,549453840,27021872651567104]),([v10,v352,v3,v2,v5,v6,v40,v241],[404,4220,876,88,13,20,5,1324,4148,9,4208,285,77,4224,3124,109,4196,85,4216,57,3184,201,2980,145,2824,149,2800,69,16,153,105,25,0,2820,169,177,2812,2816,189,93,17,237,409,217,349,761,749,73,249,253,257,265,125,525,341,661],[15,240,768,3328,28682,491522,7864320,126877760,939524097,7516193024,25769811968,240518299648,824653643776,671088720,7698728878144,8401088,61572651286592,70643632570432,140740172711168,671100930,1970325374009344,2251800353177600,3221229824,3221389312,13511900543320064,18014432869355520,274881056768,36037867992121344]),([v67,v352,v3,v2,v5,v40,v241],[1812,37,77,40,4208,16,1408,13,20,5,3124,9,4220,25,4228,285,4148,4232,109,341,85,3356,57,201,33,29,149,69,81,876,88,105,101,45,3368,61,93,157,237,281,217,761,765,249,325,245,293,297,125,397,661],[63,964,3072,126980,1970180,14680068,119539202,939528243,8053112834,30065950722,103123255298,137573171920,824633778752,3298536063680,4432433512960,137573232656,8796228685840,17592334942208,246307785728000,844424940658688,1126999434199040]),([v3,v16,v2,v5,v6,v353,v241],[4244,657,412,13,20,153,5,249,4236,285,333,29,4248,37,421,3552,41,45,53,4252,57,133,9,25,101,4240,136,109,36,2764,3536,457,341,85,201,265,769,405,773,777,129,61],[31,233,1802,30734,1015818,3178506,4194560,8388865,117452801,939655169,1076920320,2147485057,4294979745,9126936705,120261214336,16787200,671220992,412320039936,688009216,554053967872,3298538192896]),([v10,v3,v2,v5,v6,v353,v241],[1324,13,20,5,4236,9,4244,333,4256,37,4260,169,4240,136,45,85,36,2816,3644,133,201,3536,153,249,17,657,25,409,693,165,781,217,149,4264,749,785,73,265,769,101,105,109,177,181,185,433,57,93],[15,48,208,16128,246016,3932160,12582987,251658264,1879051785,15032680458,51809878024,68794974288,12586816,8569152,412327084032,1649334552592,3298602024976,85721088,30786325745152,35184373926400,211108381360128]),([v3,v33,v2,v5,v6,v353,v241],[4244,657,604,13,20,157,5,249,17,4268,25,409,4240,169,341,3688,41,109,233,4272,57,133,9,105,4236,68,37,45,36,1752,3536,333,461,85,201,325,769,773,425,777,229,113],[31,233,3854,28682,1015818,3178506,4198400,58721793,67112961,939655169,1076920320,2147485345,4294987905,9126936705,120261214336,8418816,679609856,139589616640,671240192,824636915712,3298538192896]),([v67,v3,v2,v5,v6,v353,v241],[1408,13,20,5,4240,9,4256,25,4276,285,4236,68,4244,341,45,85,36,1808,3756,133,201,3536,157,249,645,281,789,29,657,37,421,217,149,4280,765,785,81,89,321,325,769,101,105,245,293,297,397,57,93],[15,48,4032,12304,245824,3932160,12587019,117441417,2013265944,15032680458,51558219784,12587968,69264740368,412325433408,1649277665280,6597606638352,61572651320192,70368746013312,2199560175632,672923648,422214613893120]),([v3,v2,v55,v5,v6,v353,v241],[76,1,5,9,13,20,657,4236,209,105,4240,213,101,3800,41,45,53,4284,57,133,4288,4244,249,4256,333,341,184,85,89,201,769,25,37,36,3536,109,337,773,345,777,129,61],[31,113,976,7248,254032,794704,15728648,20972168,37753864,473989128,1615339528,2147484800,4294967424,8791293952,17180663808,5760,103146357376,137456525824,309304792064,549790167040,3298535710720]),([v3,v2,v354,v5,v6,v40,v241],[4292,153,5,137,69,13,4300,12,16,21,4304,285,237,361,65,412,29,33,4308,37,4312,41,45,53,57,61,0,9,2768,40,457,77,85,249,757,201,265,97,405,25,432,101,88,4,109,8,4316,36,113,333,117,129,205],[63,997,31776,1015840,15761444,50462816,1006634002,1073759313,2148270099,30070013969,240551723088,824700847104,16492675203072,263882795909120,281509370003648,2199023799296,580542144726016,1126174818321472,90159959506944,2198339648,6755433838542912]),([v355,v356,v3,v2,v5,v6,v40,v241],[4320,40,88,128,13,20,5,496,69,2268,153,3124,9,4192,65,285,25,4292,4212,77,45,4136,109,4296,57,4324,201,12,21,16,1792,37,2752,4328,4332,136,113,237,281,29,313,421,229,233,681,765,105,157,289,85,249,253,257,265,725,333,293,297,397,4336,533,277,601],[15,240,16128,123392,917504,15728640,251658240,301989888,537003265,1073799168,6442713093,60133736449,68753031169,1360,412316909632,3850438180928,30786329772112,35184472752193,492581209277440,2147878144,8444249305515008,27021597848110080,2147540992,252764529090396160,288300744996593664,576460754456412160,1152922056611069952,6917533425775673344]),([v3,v357,v2,v5,v6,v40,v241],[4344,12,13,5,33,1324,4348,153,69,489,4352,17,237,501,65,169,145,4356,77,165,4360,217,149,85,201,93,2820,40,9,0,25,2072,37,88,4,45,8,4364,36,57,61,4340,249,753,265,653,109,333,513,301,177,341,181,185,189,193,197],[63,1004,31752,1015848,15728680,54525961,1006634368,1610630144,32212647936,515405512704,1649300996099,1073759489,2203318616512,15427531964736,53326347501825,5368988672,492581218698240,562951060734977,16888636051423232,126100793895157761,60817409]),([v356,v3,v2,v333,v5,v6,v40,v241],[4368,21,153,3248,69,404,112,40,88,620,25,4184,65,1740,169,4224,2800,109,3236,4372,136,113,237,13,20,5,1384,17,313,41,233,765,57,2268,3124,9,157,4340,245,249,753,757,201,265,77,45,4136,4296,12,797,333,509,513,4376,433,229,277],[3,124,904,15360,114952,1966088,2097161,12582932,125829120,146804736,343982080,1623326720,6450839561,60129544212,68719481872,137439002644,4123168735248,13198434500624,8589941760,17729625030656,246290604752896,285877318189057,562949953444864,7916483720122368,4294974465,9042383626977280,18014402804498441,108090793398501376]),([v3,v2,v358,v5,v6,v40,v241],[4292,157,5,221,69,13,4380,12,16,33,604,17,21,4384,25,4388,169,313,389,77,4392,41,109,233,57,113,4,9,1756,40,65,461,85,249,757,201,325,269,620,105,52,0,425,37,45,8,4396,36,61,341,121,229,277],[63,997,31776,1015840,15729700,50335840,1006665746,1073766419,2148040785,30070013969,240551723088,4123168628736,13194207199232,263882795909120,281509370003648,549756461056,88510691303424,1124089920,580542145265664,1130297987465280,6755433838542912]),([v163,v356,v3,v2,v5,v6,v40,v241],[4400,40,52,60,13,20,5,648,69,3124,157,2268,9,4184,4292,65,77,4224,169,37,109,4136,45,4296,57,4404,201,12,33,16,25,1740,2800,4408,4412,68,61,17,237,409,313,165,129,53,729,749,101,153,173,85,249,89,321,325,673,4416,525,341,181,185,433,205,613],[15,240,16128,57344,993280,15728640,251658240,301989888,536888577,3221233669,4295426048,60133736449,68753031169,1360,963146416192,3298535211072,30786329772112,35184472752193,1073767680,492581209506816,8444249305515008,27021597848110080,1074208768,36028798097956864,72057732651294720,1009369266488868864,1152991873452081152,6917533425775673344]),([v3,v359,v2,v5,v6,v40,v241],[4420,12,13,5,33,1408,4424,157,69,489,285,141,4428,65,281,4432,29,313,517,77,4436,217,149,85,201,93,1812,40,9,4,2072,25,52,0,37,45,8,4440,36,57,61,4340,249,753,325,653,245,333,293,297,261,301,305,341,497,193],[63,1004,31784,1015816,15728680,54525961,1006666112,16106139648,17717297152,515405512704,1649300996099,2201170751936,17180426497,15427531964736,53326347501825,19327922176,1055668611067904,7881301528944641,27021632133955584,36028814232944641,60817409]),([v356,v3,v314,v2,v5,v6,v40,v241],[4444,33,40,2400,52,432,157,69,404,152,285,4192,1792,37,4212,77,2752,45,2388,4448,68,61,20,5,1436,13,313,237,29,41,53,749,57,2268,3124,9,4340,65,109,4136,4296,201,12,153,177,249,753,757,325,797,4452,397,341,493,497,129,205],[3,60,968,7192,122880,1966088,2097161,62914560,100663488,184552448,369131520,1711407104,6476005385,60129544384,206158432256,8589993984,1924145479680,6601364733953,68719480000,8796093063296,263882790797440,283678294933632,562949953481728,1126174784881664,2251804108655625,31525472269664256,4295024641,108088594375245824]),([v355,v244,v3,v2,v5,v6,v40,v241],[4320,40,500,48,13,20,5,157,4460,161,153,4464,4488,209,17,285,4472,4476,213,129,4468,229,4484,61,4324,113,12,21,265,16,105,1792,37,29,2752,109,4328,4332,201,69,237,281,313,421,233,681,241,289,217,249,717,93,273,333,393,305,4336,125],[15,116,8064,61696,458752,7864320,125829120,150994944,805372929,3221262336,30064902144,240520265729,274894684161,549755814992,3299608657984,13207024435264,52810919968848,70368794509377,140737488397440,8590132352,1970324839072768,6755399743046656,8589979648,27303072743063552,38280597939978240,72057602630615040,12926844928,144115222471245824]),([v244,v3,v2,v333,v5,v6,v40,v241],[4368,21,69,3248,153,404,112,40,1388,48,25,4504,17,1740,4496,169,2800,109,3236,229,4372,57,237,13,20,5,409,313,233,113,585,157,4460,4464,161,65,537,4492,217,249,717,261,265,273,209,29,129,4468,4484,61,12,4508,125],[3,124,904,15360,114696,1966088,2097161,12582932,58720512,79696896,142655744,281673728,1619001353,32212256784,105226702864,139586486288,1924145872912,15393699659792,17596481017856,35321811058688,492581209767936,1688850397134849,17592186083328,87960930750464,562950490297344,2322168558419968,562950490324993,4503600164896768]),([v163,v244,v3,v2,v5,v6,v40,v241],[4400,40,652,48,13,20,5,153,4464,161,157,4460,4504,4472,209,213,4496,29,169,229,4468,129,4484,113,4404,61,12,33,325,16,25,17,1740,101,2800,45,4408,4412,201,69,237,409,313,165,53,729,317,173,217,249,665,93,329,4416,341,429,197,125],[15,116,8064,28672,497664,7864320,125829120,150994944,805315585,7516196864,25770131456,240520265729,274894684161,549755814992,3301756108864,13202729730112,52810919968848,70368794509377,2147497088,140737488651392,1970324839072768,6755399743046656,2147848192,9007201404850176,3263168512,54324670507515904,74309402475364352,144115222471245824]),([v244,v3,v314,v2,v5,v6,v40,v241],[4444,33,40,2400,1440,48,69,157,404,152,4488,285,1792,37,4476,29,2752,45,2388,129,4448,57,20,5,13,313,237,421,53,61,585,153,4460,4464,161,4492,17,213,229,4468,4484,113,12,77,541,217,249,665,189,325,329,4520,125],[3,60,968,7176,122880,1966088,2097161,29360144,50331840,83889168,184590336,319422464,1627389961,32212255872,103079216128,141733970944,1924145872896,6597606637569,36507225216,26390426583168,246290605146240,1970325373845632,137439005696,2252074692118528,2199560128513,412317417472,2199560167424,4503600164896768]),([v3,v2,v360,v5,v6,v40,v241],[600,157,145,440,9,13,2788,4,33,16,209,49,25,213,388,4536,41,109,444,57,4540,113,464,69,65,73,169,85,253,93,269,105,0,37,45,8,2040,36,88,61,40,12,117,417,125,129,133],[63,993,7208,24928,509984,8126752,8389137,58724376,75505744,411205649,1622147089,6442455048,8589951040,257698201600,4123171749888,2214604808,19327520776,4947822252040,17180041280,9345851990080,123214025097216]),([v238,v355,v3,v2,v5,v40,v241],[4328,101,37,8,300,16,4332,5,29,21,153,81,4544,285,373,2752,109,201,4548,113,88,13,213,69,77,9,105,25,169,45,345,4336,57,149,221,813,501,817,129,241,157,289,177,249,321,93,265,269,273,333,337,301,305],[63,964,3188,28740,98305,917828,7340546,58758146,469774338,1610612811,6460014594,60137932304,214815486464,275414778497,556201148928,3298602005505,30786862449665,527765582119952,1688850397147137,6790583881052160,275415695361]),([v3,v361,v16,v2,v5,v6,v40,v241],[2764,33,1284,21,388,13,304,153,149,69,285,65,213,4556,389,37,129,45,4560,365,57,61,16,3152,432,2016,0,2760,2752,29,41,201,2768,2776,9,25,101,4564,109,4568,113,4572,4576,457,77,85,249,93,265,333,405,121,125,133],[3,124,928,3112,61472,983072,3145768,29360148,4194948,100666368,939823104,1208418304,15034482688,17213423616,34393292804,206158471168,824634114048,7696583491584,8796126579204,17592186077824,105553116398080,422212467163648,68719512576,563224831461376,1126999420569600,343597547520,2270491513487360,13510798884405248]),([v3,v362,v2,v5,v6,v40,v241],[328,20,49,388,13,300,161,149,9,4580,17,21,25,4584,29,33,37,4588,41,45,53,3556,57,4592,61,69,0,65,105,101,8,4,177,109,125,40,12,73,77,369,93,357,113,129,133],[31,496,7696,122896,1966100,31490064,100664096,469766656,3758301184,13959299072,120286347264,137606861568,274911535360,554084991232,1099570348320,671158784,2199158133248,4398205899264,537853952,4672949657600,26405484756992]),([v3,v16,v2,v133,v6,v40,v241],[348,17,21,25,33,153,5,69,4596,285,13,52,65,4600,213,101,4604,129,45,49,53,3556,57,4608,61,317,316,73,36,404,105,373,109,113,457,77,461,177,249,189,265,37,169,333,405,341,385,121,125,133],[31,241,7952,58384,2031632,65012752,201326592,1879052297,2147524617,4295294984,8615100427,17179875457,103079256224,412317188224,1649292607617,6597136978432,8800388321280,17600803246080,105557411594240,140780463235072,844424955756544]),([v3,v16,v2,v5,v6,v363,v40,v241],[4616,21,428,388,572,153,149,69,221,285,65,501,417,4620,389,37,2768,13,41,45,141,4624,765,61,4628,9,25,101,4632,16,3152,432,109,4636,4640,113,4644,457,77,265,85,249,93,52,0,333,405,2776,2752,29,121,2760,2764,57,125,129,133],[31,482,3650,61442,196608,1835010,14745602,50331648,83886081,402694144,3758096393,30065295361,103089700864,137455731841,274877939872,550292684929,3298535407744,4947810713728,134252032,26389369586688,35188667581440,70403112305664,985162420621312,4429742080,1126209152909312,6755399441842176,9429411730300928,126100789575286784]),([v3,v2,v5,v6,v364,v40,v241],[568,161,149,69,13,4648,17,21,65,4652,29,33,37,4656,20,49,580,388,4660,41,4664,45,53,4668,57,61,457,425,0,9,2768,40,85,249,189,265,101,25,109,333,125,405,12,4,121,8,36,113,129,133],[31,496,7696,253968,8159248,58722320,75497834,134222346,4026531882,12887261193,51581550600,68719481184,137707389280,824636080416,3298576826624,13262867403264,343599747584,17592244769792,105827997581312,146235088437248,845524485799936]),([v3,v365,v16,v2,v5,v6,v40,v241],[2768,13,4676,21,428,33,1048,153,149,69,285,65,29,37,41,45,4680,821,201,4684,61,16,388,3152,432,4688,0,213,3,2752,2760,2776,57,9,25,101,4692,136,109,4696,113,4700,457,77,85,249,93,265,333,405,121,125,133],[3,124,928,3112,12328,245792,1835040,31457284,2097796,100666368,947920896,3221798912,6444285952,8623489024,17213423620,240518176772,824633819136,3298536456192,4398080068100,8796093031040,52776558166528,211106233582080,34359749632,281749854652416,564049466099712,309237686272,1135795512549376,6755399442661376]),([v3,v16,v2,v5,v288,v6,v40,v241],[1096,21,2696,13,1092,153,5,69,285,65,412,33,3152,29,341,41,45,49,53,201,61,317,1104,9,25,16,4704,876,1036,4672,780,109,1116,4708,125,4712,1124,457,85,249,189,265,0,333,405,2768,37,2776,2760,113,469,129,133],[31,232,778,7176,26632,491528,3672072,12582912,20971521,503316481,1610637312,15032451072,120260132864,137443148417,33554593,24736,824633786496,3298535932032,4398050706176,25344,8798240571904,17609366962688,105553653137408,422248972353536,703721803087872,10737500160,1125934268170240,6755416622039040]),([v3,v366,v2,v5,v6,v40,v241],[2828,4,33,5,13,1404,404,4728,157,9,1344,473,4732,17,49,281,25,29,388,4736,217,149,109,201,4740,113,1368,69,16,105,0,37,45,8,2040,36,88,61,40,12,65,73,85,253,93,269,213,293,301,417,125,133],[127,8108,126984,393229,8127496,127927304,402653920,1610682368,2147745793,64429228032,1030842482688,3298669171200,134349441,13194278470304,52776742683296,70369281249280,145136076525568,300166724784128,70373043994625,563087442837505,3377716956495872]),([v3,v2,v333,v5,v248,v40,v241],[4744,153,141,576,69,13,1388,417,33,88,37,421,4748,17,21,25,3248,169,280,4752,41,4756,109,49,233,4368,61,425,2800,81,65,157,73,404,245,249,253,257,189,265,97,329,105,101,12,77,45,121,797,125,117,3236,229,113,133],[63,4064,61472,475168,33030176,100745248,939529234,7549784080,8590131218,257702756377,4123269267472,13194139571200,52776591885312,79164844016640,158329775129600,281474976886784,74766795444224,1688851034701824,6755399445970944,9007199556730880,23080948195131392]),([v367,v3,v2,v5,v6,v40,v241],[328,33,20,13,388,4764,69,16,4768,9,0,105,25,4772,101,8,169,4776,4,37,45,85,109,3648,61,40,4780,113,12,161,5,912,17,21,145,217,57,73,81,93,269,297,301,177,181,185,189,201],[31,2016,7424,1040384,7380992,528482304,3758096936,12884906248,17180082184,35435585544,77519126536,137438966624,274878120512,3154496,1652153123360,88320,2199025367296,4952298623232,61572653326336,70368945717248,140772051525632]),([v3,v2,v5,v6,v368,v40,v241],[4788,161,5,576,69,13,4792,17,21,25,4796,417,33,37,421,3220,20,580,388,4800,41,4804,45,49,53,4808,201,61,317,285,73,425,2820,40,9,0,85,249,93,265,653,101,105,65,109,125,117,12,169,77,4,121,8,36,113,129,133],[63,992,31776,491808,33030176,503320608,1644167762,2147492882,64424509522,206163148825,1924313120784,6597069775424,8830452761280,21990237274688,105553284039296,2111062358893568,19791214027776,2533549836083200,13510867608403968,18155411043516416,108121575600947200]),([v10,v3,v2,v5,v288,v6,v40,v241],[13,1092,5,2696,1108,1104,9,1096,65,404,4816,876,1036,341,4812,780,88,45,1116,85,4820,61,4824,189,1124,153,69,17,21,25,409,1324,149,3192,29,145,41,761,201,73,16,249,265,105,0,109,125,2820,169,177,2824,2812,93,197,129,841],[31,96,416,7696,122896,1966080,31457280,100663301,2013265924,15032385540,51539615748,210453921796,279181262852,550359793824,1099612291584,17280540672,2199091019776,4398124105728,26388815937568,8813809770496,43981002506240,70369423654912,422212465082368,3940649678667776,5629774424702976,562949955002368,9007474145239040,54043470415265792]),([v3,v2,v369,v5,v6,v40,v241],[408,157,141,416,9,13,1776,0,21,16,33,209,388,213,49,37,4832,41,45,4836,57,4840,61,4844,69,285,77,81,85,89,93,97,25,101,4,109,8,2040,36,52,113,40,12,401,121,125,129,133],[63,2017,6496,57384,1003552,16253216,16777745,50333776,218136664,822411281,3244294161,4294971456,25769836552,515396403200,8246343499776,8623523904,34360068160,9895610943552,42950033416,18691771105288,246428050194432]),([v87,v163,v3,v2,v6,v40,v241],[4408,105,25,8,208,16,4412,5,17,33,157,73,4848,169,373,1740,45,201,4852,61,52,13,209,69,65,9,101,37,285,109,337,4416,57,149,137,845,517,833,229,317,153,173,245,249,257,93,325,97,329,341,345,193,197],[63,964,3188,28740,98305,917828,7340546,58758146,469807106,1610612811,6460014594,60137932304,214815486464,275414778497,556201148928,3298602005505,30786862449665,527765582119952,1688850397147137,6790583881052160,275415695361]),([v3,v370,v33,v2,v5,v6,v40,v241],[1752,21,1256,33,388,13,212,157,149,69,209,4860,361,25,169,77,229,109,4864,365,57,113,16,2296,620,1748,1740,17,2960,4,41,201,1756,1764,9,105,4868,37,45,4872,61,4876,4880,65,461,85,249,93,325,117,341,425,125,133],[3,124,928,15392,49192,983072,3145768,29360148,4194948,235152384,805355520,1107755008,15034482688,17448304640,103079225344,137707388932,824634114048,7696583491584,8796093031040,17592454513156,105553116398080,422212467163648,34359795712,309237784576,572845560176640,1126174784913408,2252899327442944,13510798884405248]),([v3,v371,v2,v5,v6,v40,v241],[136,20,49,388,13,208,161,149,9,4884,17,21,25,4888,29,33,37,4892,41,109,233,3692,57,4896,61,69,4,105,8,0,77,101,245,45,125,40,12,65,81,369,93,97,113,385,229,133],[31,496,7696,122896,1966100,31490064,100671776,939659776,3288408064,13153992704,120286347264,137472512768,275985408256,554084991232,3298593603872,1208029696,135139328,4535510635008,8797167493120,4399145492480,52793763823616]),([v3,v33,v2,v5,v278,v40,v241],[260,29,33,37,13,157,5,69,4900,209,21,105,88,169,77,4904,229,109,49,233,3692,57,4908,113,224,81,373,36,404,101,45,61,65,457,461,177,249,189,325,25,285,333,357,117,341,425,125,133],[31,241,3856,29712,1015824,15729680,50331648,67111177,939540489,1073905672,2160066571,12884904352,17179889793,103079379072,412329443457,1649267501312,6598143674368,8802548058368,17593259966464,35186533220352,211106245345280]),([v3,v33,v2,v5,v372,v6,v40,v241],[4916,33,616,388,692,157,149,69,137,401,4920,361,25,1756,13,169,77,517,41,109,145,4924,749,113,4928,9,105,4932,16,2296,620,37,45,4936,4940,61,4944,65,325,461,85,249,93,1764,1740,17,117,88,4,1748,1752,57,341,425,125,229,133],[31,482,7682,24576,229442,1835010,14688258,50331648,201331712,1879048201,2164260865,30065295361,103089700864,137438957728,275146342529,549772656769,3298535407744,4672932806784,61572653257216,67211264,4362604544,70540551262208,422213018779648,1688849861050368,2278188103238656,4503603922927616,9007233622933504,126100789575286784]),([v3,v2,v5,v373,v6,v40,v241],[688,161,149,69,13,4948,17,21,25,4952,20,49,696,388,4956,29,33,77,4960,41,4964,45,53,4968,57,113,405,4,9,1756,40,461,85,249,89,321,261,325,12,105,0,109,117,37,8,36,125,61,341,425,129,133],[31,496,15888,245776,8128528,58785808,67109162,2013282314,2156052490,64426868745,206200373256,1924153737504,549755978016,2748781429024,4398105231680,8796227420160,54975584796672,211381152382976,283674002472960,633318739673088,3448068508745728]),([v3,v365,v33,v2,v5,v6,v40,v241],[1756,13,4676,33,616,21,1048,157,149,69,17,25,169,77,41,109,4976,825,201,4980,113,16,388,2296,620,209,3,1740,4692,4,1748,1764,57,9,105,4688,68,37,45,4696,61,4700,65,461,85,249,93,325,117,341,425,125,133],[3,124,928,3112,12328,245792,1835040,31457284,2097796,243271680,805318656,3221798912,6444285952,8858370048,120259086340,137707388932,824633819136,3298536456192,4398046513792,8796361466372,52776558166528,211106233582080,17179883520,292057810944,286972535900160,563224831369216,1126999419527168,6755399442661376]),([v3,v33,v2,v287,v5,v6,v40,v241],[1056,33,3512,13,1052,157,5,69,604,21,2296,17,333,169,77,41,109,49,233,201,113,241,1068,9,16,4984,1000,1036,4972,776,37,45,1076,4988,125,4992,1084,461,85,249,261,325,1756,25,4,1764,1748,61,465,341,425,229,133],[31,232,1800,6664,24586,491528,3670536,12582912,251658241,805312512,1077936129,15032451072,120260132864,16777377,6304,137443164289,824633786496,3298535932032,13194407968768,17592190263296,105589623554048,175956221755392,30720,10737487872,281509338025984,562952100986880,1125917087776768,6755416622039040]),([v3,v374,v2,v5,v6,v40,v241],[1820,0,21,5,13,1320,404,5008,157,9,5012,473,5016,17,388,29,49,165,37,5020,217,149,45,201,5024,61,5028,69,16,25,101,4,109,8,2040,36,52,113,40,12,77,81,85,89,93,97,209,401,181,193,125,133],[127,8108,24589,495624,7881736,127927304,402653920,536887297,3221491712,64429228032,1030842482688,134226561,3298669367809,13194278470304,52776742683296,70369818189825,70373043871745,140874977648641,285874101948416,581641701691392,3377716956495872]),([v3,v314,v2,v251,v6,v40,v241],[1440,401,21,52,25,33,5032,157,145,548,69,137,2400,285,13,280,5036,29,37,5040,129,5044,45,53,4444,113,1792,405,73,12,65,101,105,109,117,404,77,153,81,177,249,89,321,261,325,269,273,797,2388,61,125,121,133],[63,4064,61472,475168,16253216,50352160,469828752,1627402256,6509887504,12891717648,17767075856,34359751808,481053443072,8246341928512,131941445665792,140737488822272,281474982490112,562950037307392,10742464512,3377768490598400,5629499589787648]),([v375,v3,v2,v5,v6,v40,v241],[136,21,20,13,388,5052,69,16,5056,9,4,5060,105,8,285,5064,0,25,101,37,109,45,85,3760,113,40,5068,61,12,161,5,788,141,29,33,217,57,73,81,93,97,245,293,297,261,185,193,201],[31,2016,260096,787712,7350272,528482304,3758096936,4295020552,25770328328,35437676552,86109061128,137439007296,274878434144,5245504,1652153123360,839680,15393167001600,17592387424256,35184377071872,70927291777280,140772053616640]),([v3,v2,v5,v376,v6,v40,v241],[5076,161,5,548,69,33,137,5080,401,21,25,2368,20,13,696,388,5084,29,37,5088,129,5092,45,49,53,5096,201,113,405,1812,40,9,4,169,81,85,249,89,321,93,325,653,12,285,65,0,101,105,109,117,77,8,36,61,125,121,133],[127,1952,63520,466976,33030176,234889248,268436626,8053129234,25803685906,515400794137,3848458469392,65970731222144,211106232796288,422212469785728,572295970030592,1125904202268672,6755433807609856,9012147224838144,351843725934592,54043195696611328,90071992720424960]),([v67,v3,v2,v287,v5,v6,v40,v241],[13,1052,5,3512,1064,1068,9,404,5104,1000,1036,333,5100,776,52,1056,77,45,1076,85,5108,113,5112,261,1084,157,69,1408,149,2340,17,141,29,33,37,421,41,761,201,16,81,249,89,321,325,1812,285,101,4,245,1816,1804,93,305,125,229,841],[31,96,1936,30736,98336,1966080,31457280,100663301,939524100,3221227524,64424509444,206427389956,275154731012,549856477312,1174407168,1116758638624,15393230553088,17592263639040,105553116270592,422229644935200,3940649678667776,5629774424702976,140755741968384,562949954996224,9007474145232896,140754668879872,18014419992707072,108086665943711744]),([v377,v3,v2,v5,v6,v40,v241],[1872,21,0,149,1320,404,13,5124,69,16,9,388,25,52,101,88,5128,37,4,1332,109,8,45,1868,113,40,5132,61,12,1,5136,489,17,29,349,833,41,49,505,57,237,829,285,77,81,85,89,93,97,209,401,181,193,125,129,133],[127,1968,6145,516096,7864320,528482304,3758621850,4294969355,61203482632,481041055752,3849574154248,4402341479681,26388279264656,105553120986368,422212666394000,562954248536065,562954254155776,1125904419913729,2286984190640128,4653133418659840,63050394989232128]),([v378,v3,v2,v5,v6,v40,v241],[2860,33,4,149,1404,404,13,5140,69,16,9,88,105,5144,25,0,52,388,37,1412,45,8,109,2856,61,40,5148,113,12,1,5152,489,17,377,817,29,41,49,505,57,313,829,65,73,169,85,253,93,269,213,293,301,417,125,129,133],[127,1968,129024,393217,7864320,528482304,3758621850,31138668552,34359869451,481041055752,3849574154248,13194139559312,17626545784065,105553120986368,422212666394000,562984313188353,1161084283670528,2396935558291456,562984318926848,4503634205212673,63050394989232128]),([v379,v3,v2,v55,v5,v6,v40,v241],[468,13,9,1456,1,180,80,388,5156,168,456,88,105,1872,209,0,101,2860,213,4,45,41,61,188,57,196,149,1844,349,377,3804,5116,157,404,65,153,77,85,201,17,29,129,1312,5160,5120,229,333,113,401,545,341,417,549,205],[3,124,3968,61440,983040,3145768,62914560,67108885,469762432,604000256,335872000,70254600,1161822208,15032385552,51539623952,73014706192,137441050644,279189651472,549755953152,1099511635968,6597071863816,26388300038144,417792,105553118380032,985162435280896,1128098932457472,6755399462289408,9009673174777856]),([v3,v2,v380,v5,v6,v40,v241],[5172,1,5,468,69,13,88,20,33,388,1920,209,21,105,1904,213,101,5176,41,45,49,53,3804,57,5180,61,8,16,9,65,457,77,461,177,249,89,321,93,97,329,25,37,85,40,12,109,333,337,113,117,341,345,121,125,129,133],[63,992,15392,114976,4063264,62914848,469893139,1610621970,6442532882,128849674256,962123005979,1099511628864,2199023272000,4398114537472,26388341981184,222208,246290605285376,844425517343744,3412884093337600,4785076801978368,63050394834173952]),([v381,v3,v2,v5,v6,v40,v241],[88,13,20,21,388,5184,69,0,9,480,153,404,105,25,1904,101,5188,45,8,109,3912,61,40,5192,113,12,5196,149,221,209,501,817,29,33,37,229,141,233,57,237,241,65,1,457,169,81,245,249,253,257,93,265,269,273,481,333,293,337,301,305,125,277],[31,4064,28832,49153,983040,66060288,469763656,3892318248,30064787464,240518758408,1924171563016,15393162859552,52793738019904,1055531163255808,16888498694915584,18014415689371680,252201579133472768,865819227410403360,17609366634496,21502115840,3458764548206034944]),([v382,v3,v2,v5,v6,v40,v241],[52,13,20,33,388,5200,69,4,9,5204,157,404,1920,88,105,101,37,0,5208,109,8,45,3996,113,40,5212,61,12,5216,149,137,17,21,25,213,517,833,129,145,53,57,313,317,285,73,77,1,461,177,249,89,321,93,325,97,329,481,341,181,345,193,197,125,205],[31,4064,28672,233504,3932160,264241152,1879049800,15032389640,120795988008,962075033608,7696686252040,26396869006400,246290604917792,4222124653020160,67553994779657728,72057602627899424,8804685840384,10846474240,1008806316533907456,3463303297920696352,13835058192824139776]),([v383,v3,v2,v5,v6,v40,v241],[1976,21,0,13,408,16,69,9,388,25,52,101,88,5228,37,4,5232,109,8,45,1868,113,40,5236,61,12,1,141,137,209,5240,29,33,229,49,365,57,285,77,81,85,89,93,97,401,181,193,125,133],[63,240,769,64512,983040,66060288,469827736,536871179,7516217608,60130131976,74114400264,137975824577,824633745616,3298535473344,13194164699344,137975842817,537591808,17592750178305,36283884324864,74768964411392,422221080756224]),([v384,v3,v2,v5,v6,v40,v241],[2920,33,4,13,600,16,69,9,88,105,5244,25,0,52,388,37,5248,45,8,109,2856,61,40,5252,113,12,1,145,221,5256,17,21,213,129,49,365,57,65,73,169,85,253,93,269,293,301,417,125,133],[63,240,16128,49153,983040,66060288,469827736,3758115848,4294983691,60130131976,71430045704,412316863696,554050781377,3298535473344,13194164699344,554050784769,18691698264576,39583518559232,4295688192,70373066407937,422221080756224]),([v3,v385,v2,v55,v5,v6,v40,v241],[80,49,1,137,9,13,1948,33,5260,388,209,21,105,213,101,217,45,5264,365,57,61,180,456,88,168,1976,0,2920,4,41,201,188,196,16,69,65,77,85,89,93,97,25,37,5220,5268,5224,109,333,337,113,117,341,345,121,125,133],[3,61,992,7200,24736,491552,1573024,2228245,29360896,100668416,402677760,539197440,7517241344,25769803793,51539611664,85899362320,429496795152,1666448359440,2199191027712,4398080065536,8933532172288,53326314995712,167792640,492581209313280,1688884221054976,6825768185315328,9570217928704000,54043195529592832]),([v3,v2,v386,v5,v6,v40,v241],[80,1,5,69,13,88,20,388,1992,17,21,25,2936,29,33,37,5272,129,45,49,53,3804,57,5276,61,8,9,65,73,77,81,85,249,89,369,93,97,329,285,169,40,12,101,105,109,113,117,121,125,133],[31,244,3856,61456,2031632,31473680,100728843,402721034,1610649610,32212582408,240543334411,274877907232,549755818016,2181365760,3332921884672,13194139568384,26388279396352,105553275652352,21990232915968,175922422517760,844424955756544]),([v387,v3,v2,v5,v6,v40,v241],[88,33,20,13,388,5280,69,153,0,9,112,16,105,25,2936,37,3236,45,8,109,3912,61,40,5284,113,12,141,17,21,169,229,233,57,65,1,73,245,249,253,257,261,265,269,273,521,125,277],[31,4064,12576,49153,983040,66060288,67110088,402661416,536887307,3288924168,4589617160,60129616032,536888512,1030792740992,16492699583616,536883232,17592186777600,4454359072,537591808,565198848,105554215763968]),([v3,v2,v55,v327,v6,v40,v241],[80,1,5,69,13,5288,17,21,25,52,209,105,449,2936,213,49,101,5292,229,109,233,3804,57,5296,113,16,73,65,9,1952,77,461,85,249,253,369,93,269,273,4,373,136,333,337,177,341,345,125,121,133],[31,496,7700,122896,1998864,31457424,100663563,939657226,3221299210,64425164808,481061502987,549789378817,1100048498688,4295622912,68746740032,2748779145216,13198435158016,68880959488,123145303031808,422213564047360,703687467859968]),([v388,v3,v2,v5,v6,v40,v241],[52,21,20,13,388,5300,69,157,4,9,5304,16,1992,88,25,101,37,0,5308,109,8,45,3996,113,40,5312,61,12,145,285,29,33,129,53,57,77,1,81,177,249,89,321,189,325,97,329,529,125,205],[31,4064,28672,233504,3932160,264241152,268436680,536875019,3221291048,13155696648,19432210440,536876224,240518496416,4123170963584,65970798331008,536973344,539754496,650121216,70368747159552,18354339872,422216863055872]),([v3,v2,v55,v5,v308,v40,v241],[80,1,5,69,13,5288,29,33,37,1992,209,49,105,88,213,101,453,5316,129,45,53,3804,57,5320,61,16,81,65,457,77,9,1964,85,249,89,369,93,97,329,373,0,245,333,337,125,117,341,345,133],[31,496,7696,122900,1968144,31457424,100663563,402657802,3758260234,64425164808,481061502987,551903298048,1099545215745,4295622912,68746740032,1099511673344,15393163448320,52776717521408,211110528188416,69283643392,299067188838400]),([v3,v2,v389,v5,v6,v40,v241],[408,1,141,137,424,9,33,5328,0,21,13,1772,40,401,428,5340,29,5344,37,5348,129,544,45,49,201,237,61,16,69,285,77,81,85,89,93,97,388,25,52,101,88,4,109,8,36,113,12,121,125,133],[127,8128,25280,508480,16285760,117440592,402653217,805314720,3490054177,13158055969,51875151920,206158430336,4123168997376,30786332393472,105553183375376,550292955264,4398051238016,35184976076816,4947809533952,175923001557008,844425002483728]),([v3,v2,v390,v5,v6,v40,v241],[600,1,145,221,612,9,21,5332,4,33,13,2784,40,5352,17,5356,25,616,417,5360,229,732,109,49,201,313,113,16,69,65,73,169,85,253,93,269,88,105,0,52,388,37,45,8,36,61,12,117,125,133],[127,8128,254528,393920,16261184,117440592,402653217,1879146529,2416181408,13158055969,51875151920,1030792249344,3298534883456,30786332393472,105553183375376,139586797696,4535492378624,175922464489488,4398051491968,35186586943504,844425002483728]),([v3,v2,v391,v55,v5,v6,v40,v241],[1,80,137,9,33,188,13,2480,5364,96,209,21,105,213,101,129,45,49,201,748,61,196,16,69,65,77,85,89,93,97,456,88,168,388,401,5328,0,417,5332,4,41,180,184,57,25,37,5336,5368,400,109,333,337,113,117,341,345,121,125,133],[31,96,912,7184,26640,229392,1835024,2621451,12582922,25169928,41959432,209780744,814743560,16106127616,120259088384,962072690688,7696581459968,8796096954368,17901423689728,35218731827200,211106299707392,281475246718976,309237665792,3940649674018816,13510798899941376,54606145481949184,76561193699917824,432345564228714496]),([v392,v3,v2,v5,v6,v40,v241],[1368,33,20,88,13,388,5372,69,12,80,9,2532,876,25,3344,37,5376,45,8,5380,85,36,61,93,1,5,17,21,105,29,101,41,201,149,65,77,97,109,333,113,341,217],[63,1984,14336,49160,4128768,12583232,50333200,469764112,1610629138,2182676496,12893290576,17448307904,35433497728,2165376512,68732060864,1946159104,412586412032,567212507200,1100586631168,35446063168,2203327660096]),([v3,v2,v393,v5,v6,v40,v241],[112,153,141,9,21,221,1388,20,13,88,388,5384,17,105,3344,169,33,37,5388,229,4756,109,49,233,4368,201,113,241,0,16,161,65,69,81,245,253,257,261,269,273,25,101,45,8,36,61,12,481,333,337,117,465,125,133],[63,2000,14608,245776,16515088,251658512,1879050251,6459238408,12885082120,124556410889,966451527688,1099780077568,2199023272448,30786328985600,105553200152576,140737488500736,848822979012608,3412886323994624,4398049050624,35184456138752,13510798968619008]),([v3,v394,v2,v5,v6,v40,v241],[1440,20,13,876,388,33,152,157,145,9,137,2532,285,21,25,5392,29,101,5396,129,5044,45,53,4444,201,313,61,317,4,16,161,105,37,0,109,8,36,113,12,69,73,77,177,89,321,189,97,329,481,341,345,121,469,125,133],[63,2016,30752,229412,8126752,260046880,1879081664,2147485704,12885133312,120262492160,412392357888,1649267464704,2748787622400,31336083751488,246840435933696,281474976958464,17182251008,137514471424,1688867042656256,6757735978893312,27021597842341888]),([v3,v395,v2,v5,v6,v40,v241],[5416,0,21,149,13,1772,40,5432,1,1320,9,5436,489,5440,17,1340,169,145,5444,37,5448,217,5452,45,57,237,749,61,69,16,404,388,25,52,101,88,4,109,8,36,113,12,77,81,85,89,93,97,209,401,181,193,125,133],[127,16268,49165,1017864,15861768,251666440,1879049856,6442450945,128849805312,962086305792,3298669109248,268452993,13194408756864,52776836007552,211106635195392,281492157120513,281612425117697,564049599291392,1143509287174144,2326566739124224,13510799026823168]),([v3,v396,v2,v5,v6,v40,v241],[5420,4,33,149,13,2784,40,5456,1,1404,9,5460,489,5464,285,141,5468,25,1420,29,5472,217,5476,109,57,313,765,113,69,16,404,88,105,0,52,388,37,45,8,36,61,12,65,73,85,253,93,269,213,293,301,417,125,133],[127,16268,509960,786445,15763464,251666440,1879049856,32212451328,103079215105,962086305792,3298669109248,13194408167040,268960897,52776836007552,211106635195392,281479272398849,580546448261120,1200666831888384,281612425625601,2252899460063232,13510799026823168]),([v3,v397,v2,v55,v5,v6,v40,v241],[188,13,1,149,9,468,489,2552,145,5480,96,209,141,105,213,101,217,45,57,5484,749,61,80,196,456,88,168,388,5416,0,5420,4,41,180,184,5408,69,404,65,77,85,89,93,97,25,37,5424,5488,5412,109,333,337,113,117,341,345,121,125,133],[3,124,1928,14344,49416,196872,3932168,13107220,251658752,805316608,3221274624,30064902144,11272192,240518168592,343597391888,618475323408,3367254491152,13262861107216,17593528221696,35184640524288,212205744291840,285873025843200,1342218240,3940649674088448,13511073762123776,54606145482031104,76561743423242240,432345564229861376]),([v3,v398,v2,v5,v6,v40,v241],[464,20,33,88,388,13,5492,1,5,468,9,2584,209,21,105,3408,213,101,5496,41,5500,85,5504,57,61,69,12,16,876,25,37,45,8,36,93,65,77,89,189,97,653,169,285,109,333,113,117,341,121,125,129,133],[63,2016,30752,229412,3932448,29360164,239076416,805308416,1073774600,15035793408,17276338176,34397506560,68753196032,139622352448,1924199875584,6597069916160,26388281444352,105587496992768,140739638362112,316728089378816,3940649697017856]),([v399,v3,v2,v5,v6,v40,v241],[500,13,20,88,21,388,5508,9,0,480,153,404,161,105,25,285,3408,101,5512,45,8,4336,109,36,4324,61,113,12,5516,149,221,501,29,33,37,229,141,233,57,237,241,69,81,245,253,257,261,265,269,273,333,217,393,305,125,277],[63,8128,57664,196616,16515072,251658240,1879049872,2684395600,30064836624,240524722192,1924229234704,16819392,6614518137856,61572924049024,1055531246552064,17179910208,7881299352387648,9007199372222464,17187012608,21592276992,54043229976264704]),([v400,v3,v2,v5,v6,v40,v241],[652,13,20,876,33,388,5520,9,4,632,157,404,161,2584,105,101,37,169,0,5524,109,8,4416,45,36,4404,113,61,12,5528,149,137,17,21,25,517,129,145,53,57,313,317,69,73,177,89,321,189,325,97,329,341,217,429,197,125,205],[63,8128,24584,499776,33030144,503316480,3758098064,30064779280,35433644112,481049444368,3848458469392,13211856282624,33719488,123145848096384,2111062493103104,17180041280,17194033152,21709717504,15762598704840768,18014398744526848,108086459952529408]),([v3,v365,v2,v55,v5,v6,v40,v241],[188,13,161,149,9,33,1048,5540,96,209,21,105,437,213,101,441,41,45,5544,821,201,5548,61,1,80,468,456,88,168,388,4688,0,4692,4,180,196,57,4676,69,5552,65,77,85,89,93,97,25,37,4696,4700,109,333,337,113,117,341,345,121,125,133],[3,60,488,7712,58400,983072,7340064,58720272,1006633088,3221228032,12884926464,51541901312,103086555136,962072674320,1374389536784,2473901178896,13469017571344,53051440234512,70374112886784,140738562097152,285873023614976,580542145757184,5368727552,7881299348031488,27022697280047104,109212290963881984,153124586358063104,864691128461557760]),([v401,v3,v2,v5,v6,v40,v241],[2960,33,4,13,2780,36,88,69,16,9,404,5556,105,25,0,388,37,5560,45,8,109,2856,61,40,5564,113,12,5568,161,149,209,49,501,213,129,365,57,65,73,169,85,253,93,269,293,301,417,125,133],[63,1984,30720,98305,1966080,132120576,939557384,7516334088,8589967371,53688270856,69442994184,412316871296,558345749121,3298536063616,13194460398080,558345762816,18691698864128,39719907895296,8591376384,70377388638209,422229696446464]),([v3,v2,v5,v278,v6,v402,v40,v241],[1,5,9,21,209,105,264,88,388,5572,29,5576,37,13,129,45,57,61,65,69,280,276,81,260,161,1516,177,89,93,97,5580,25,5584,285,373,272,109,333,357,113,117,5588,101,20,5592,5596,224,284,292,296,125,133],[15,58,968,7176,8704,49162,196618,786468,3145861,4724868,58720260,201883652,805961732,16106127392,30064775200,38654705712,481036369952,1649267834912,6597069768704,8796093022272,69793251328,53326314078208,70368744184832,69793255424,549755950080,140738562146304,844424930328576,3377699720708096]),([v403,v3,v2,v5,v278,v6,v40,v241],[264,13,1,260,9,1516,209,5600,105,272,5572,388,29,5604,37,224,109,284,45,5608,113,292,61,296,5,21,20,88,129,57,65,69,1524,276,81,177,89,93,97,285,17,373,333,337,125,117,5612,213,5616,5620,181,193,133],[3,61,960,3073,61440,983040,15728640,50331668,50331968,234881025,33583104,319029248,591396864,3221225744,13019119636,19461595152,105226960912,414468538384,1649267966336,2748779086208,13194139861248,52777636069632,211106232541184,851968,844424935374848,1125899907710976,2251937256853504,4521192086306816]),([v3,v2,v5,v404,v6,v40,v241],[5628,161,149,96,9,33,5632,209,49,5636,25,4928,4,13,2784,40,213,453,5640,41,5644,45,53,313,61,317,65,69,73,88,16,404,85,89,93,97,105,0,109,113,117,388,37,8,36,12,417,125,129,133],[63,2016,63524,198700,8126753,58737184,469763152,3892314128,671156240,13022527504,51690603024,206158431296,68719543360,343599744064,1649351329280,6597069768704,26663160381440,35734144680448,274880333824,70918516834816,985162437362176]),([v405,v3,v2,v5,v6,v40,v241],[2016,21,0,13,1768,36,33,52,69,16,9,404,388,25,5648,101,37,4,5652,109,8,45,1868,113,40,5656,61,12,5660,161,149,209,213,49,517,129,365,57,285,77,81,85,89,93,97,401,181,193,125,133],[127,3968,12289,245760,3932160,264241152,1879053320,2147487755,30065115144,111671509000,138885988360,277025391873,1649267524864,6597072127232,26388920796160,277025488897,2150367232,35186628624385,72567769890816,150083437936640,844459392892928]),([v3,v2,v133,v5,v406,v6,v40,v241],[1,5,9,33,137,352,328,388,5664,17,5668,25,13,213,101,129,45,53,57,61,317,280,356,52,69,73,348,161,1608,77,177,89,321,189,97,329,5672,105,20,5676,37,169,109,113,5624,5680,316,5684,373,229,368,376,380,341,385,121,125,133],[31,488,3592,4352,24586,229386,1835018,6291525,58723332,469762052,553664516,7533035524,60146843652,206158431232,274877906976,3848290714624,4947802390528,61572651679744,70368744181248,424411488340992,4947802392576,8796093549056,211106232558592,1689399616143360,6755399441842176,27025995810816000,36037593649397760,216172782114406400]),([v407,v3,v2,v133,v5,v6,v40,v241],[352,13,1,348,9,1608,5664,388,17,5688,25,316,213,101,5692,45,368,109,5696,61,376,113,380,5,33,20,328,129,57,317,1524,356,52,69,73,77,245,253,93,269,5700,209,169,29,5704,5708,373,293,301,341,345,125,121,133],[3,61,193,3840,31232,491520,7864320,25165844,117440513,16779008,25178112,159514624,832569344,3288334356,30064772624,42949681168,214748495888,833225752592,3298534883840,13194139804160,425984,52776560754688,74766790714880,140737488782336,281749856716032,1688849860435968,6755433802899456,11258999204872192]),([v3,v2,v408,v5,v6,v40,v241],[5712,161,149,96,9,21,4628,0,13,5716,40,209,449,5720,213,49,5724,37,5728,41,5732,45,237,61,241,52,16,69,404,77,81,85,89,93,97,388,25,101,4,109,8,36,113,12,401,121,125,129,133],[63,2020,6252,253984,3964961,29426208,503316496,167774288,1744969744,6580076560,25912475664,103079215168,412316999680,3848294105088,13194147987456,137439094848,549758175296,21990241011712,687197265920,39582964056064,492581219794944]),([v275,v3,v2,v5,v6,v40,v241],[4688,21,0,33,1772,40,13,52,69,16,9,404,388,25,101,88,5736,37,4,5740,109,8,45,5744,113,61,12,5748,161,149,5752,209,29,41,49,821,201,237,285,3,77,81,280,85,89,93,97,401,181,193,125,229,133],[127,3968,12289,508032,7864320,125829120,2013266952,3221225483,6039994376,60142649352,206200373256,277025391873,8246337406208,26388283786496,105553426646016,277025538049,2153250816,140739694559232,290271074598912,598138662551552,7881299394035712]),([v274,v3,v2,v5,v6,v40,v241],[4692,33,4,21,2784,40,13,88,69,16,9,404,105,5756,25,0,52,388,37,5760,45,8,109,5764,61,113,12,5768,161,149,5772,17,213,41,49,825,201,313,3,65,73,280,169,85,253,93,269,293,301,417,125,129,133],[127,3968,127104,393217,7864320,125829120,2013266952,3892338696,5368709131,60142649352,206200373256,4123168630016,4402341479681,26388283786496,105553426646016,4402341507073,149533586116608,316661538242560,4300734464,562954307108864,7881299394035712]),([v409,v3,v2,v5,v6,v40,v241],[5776,13,20,88,21,388,9,16,161,404,5780,105,25,17,0,1068,1036,101,5784,45,8,109,5788,61,113,12,149,1088,221,501,169,33,37,229,141,233,201,237,241,65,153,381,69,81,245,253,257,261,265,269,273,465,125,277],[63,968,31744,229376,3932160,62914560,469762385,603991056,7516225552,60131901456,481057308688,3848290706688,13199508275456,124244816298240,2111062346301696,4294978560,7088128,2251799843055616,5371592704,5398069248,13510807495114752]),([v410,v3,v2,v5,v6,v40,v241],[5792,13,20,876,33,388,9,16,161,404,1104,1036,105,5796,101,37,29,0,5800,109,8,45,5804,113,61,12,149,1128,137,285,21,25,517,129,145,53,201,313,317,69,73,77,157,353,177,89,321,189,325,97,329,469,125,205],[63,968,7168,254976,3932160,62914560,469762385,3758097424,4362166288,60131901456,481057308688,1651951797504,15393162862848,127543351181568,2111062346301696,2147574784,2687238144,2713714688,7159808,2251799843127296,13510807495114752])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x3 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x4 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x5 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x6 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x7 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (7*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x8 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (8*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x9 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (9*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x10 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (10*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x11 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (11*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x12 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (12*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x13 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (13*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x14 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (14*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x15 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (15*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x16 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (16*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x17 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (17*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x18 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (18*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x19 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (19*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x20 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (20*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x21 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (21*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x22 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (22*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x23 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (23*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x24 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (24*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x25 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (25*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x26 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (26*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x27 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (27*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x28 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (28*8)).take 8) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 8 ptopD8 29 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  · exact ptopC8x3
  · exact ptopC8x4
  · exact ptopC8x5
  · exact ptopC8x6
  · exact ptopC8x7
  · exact ptopC8x8
  · exact ptopC8x9
  · exact ptopC8x10
  · exact ptopC8x11
  · exact ptopC8x12
  · exact ptopC8x13
  · exact ptopC8x14
  · exact ptopC8x15
  · exact ptopC8x16
  · exact ptopC8x17
  · exact ptopC8x18
  · exact ptopC8x19
  · exact ptopC8x20
  · exact ptopC8x21
  · exact ptopC8x22
  · exact ptopC8x23
  · exact ptopC8x24
  · exact ptopC8x25
  · exact ptopC8x26
  · exact ptopC8x27
  · exact ptopC8x28
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD9 : List StD := [([v89,v3,v2,v5,v6,v40,v241],[20,21,13,24,5,0,16,69,9,1,65,52,37,3,56,29,4,60,64,45,8,68,85,36,48,61,40,72,93,12,137,25,145,165,41,149,57,73,169,157,173,161,101,105,109,113,177,181,185,189,193,197,201,129,205],[63,1000,1096,260096,16517120,1056964608,1073742554,2147483675,12884955153,51544064017,103481868305,139586437832,1924145398336,2216207581760,2268145386048,13196287049736,26390431006728,35186922225672,492856093753344,3940650093432832,31525197815480320]),([v411,v3,v2,v5,v6,v40,v241],[20,33,13,28,5,4,16,69,9,1,88,25,3,84,17,0,128,77,132,45,8,136,85,36,48,61,40,140,93,12,221,141,281,37,41,149,57,285,153,289,81,161,101,105,245,293,297,261,301,305,201,229,277],[63,1000,130048,131144,16516096,1056964608,1073742554,6442477585,8589934619,51544064017,103481868305,962072699456,1108101563080,2216207581760,2268145386048,13202729492488,123282747842560,985162837944320,4406641426440,9026142216,7881299771785216]),([v7,v3,v2,v55,v5,v6,v40,v241],[80,76,13,9,16,168,172,3,24,65,105,0,28,77,101,4,176,85,180,45,184,93,188,192,61,196,137,1,5,20,145,209,141,213,41,149,57,157,153,161,25,37,32,200,204,44,109,333,337,113,117,341,345,121,125,129,133,96],[7,9,241,3840,61440,2031617,65011713,469762051,1879048194,6710887680,9932132352,51808632834,103372816386,137573171217,275012126464,137573199872,549890752513,549917294593,1099511632128,2199023255808,13194140254272,52776585396288,21760,492581209834752,1688849885431552,6825768185843712,9570149233356800,270215977667985408]),([v87,v7,v3,v2,v5,v6,v40,v241],[208,16,200,3,36,212,5,20,149,1,161,32,25,101,216,37,28,24,45,113,204,220,61,44,13,9,65,105,0,29,224,136,245,8,109,93,228,232,137,209,141,349,229,57,153,77,157,353,285,357,345,236,193,125,133],[31,480,1539,6144,122892,395264,16252932,16777249,33554433,469893120,3758145537,30064773120,240524460033,274877908257,1649401790720,2199560175904,4415226382656,8796099314016,17592387503104,246290604672001,21474840064,34366031361,281475111100416,562967267641344,208273408,1125917086754820,6755434344005632,27026012996896768]),([v238,v7,v3,v2,v5,v6,v40,v241],[300,16,200,3,36,304,5,20,149,1,161,105,308,25,24,32,37,28,109,61,204,312,113,44,13,9,17,316,68,77,101,4,177,8,45,93,320,324,221,377,213,145,129,57,65,153,381,157,169,337,236,301,385,125,133],[31,480,1539,30732,98304,425984,16252932,16777249,33554433,469774337,3758227456,30064803840,240524460033,274877908257,549822935328,3299608756480,4415226413376,8796099314016,123145302324225,140739099100160,21474870784,34366031361,281476050597888,562967133333508,3377734153678848,4503617881145344,1617559552,27026012996927488]),([v3,v2,v264,v5,v6,v40,v241],[408,153,141,137,384,9,13,412,0,21,16,285,388,29,33,416,37,420,41,45,49,53,57,424,61,428,69,20,404,77,81,85,89,93,97,25,52,101,3,4,432,109,8,68,36,113,40,12,121,125,129,133],[255,1873,6736,127168,4067520,62931136,201327024,335546416,1946255393,6778650657,26130513953,34628173840,2130303877120,33054068965376,246359349264384,412316928016,2199023912976,35459275163664,11132555984896,316934788841472,3949445792792576]),([v3,v2,v266,v5,v6,v40,v241],[600,157,145,221,392,9,13,604,4,33,16,17,21,440,25,388,169,608,41,109,49,233,57,612,113,616,69,20,65,73,404,85,253,93,269,88,105,3,0,620,37,45,8,136,36,61,40,12,117,125,229,133],[255,1873,63680,98896,4096192,62918848,201327024,1946181665,1140916272,7583957025,26935820321,1065151913984,1100585369616,33019709227008,246324989526016,206158520336,11063836434432,316797081378816,2199023976464,35321836273680,3949445792792576]),([v3,v2,v22,v55,v5,v6,v40,v241],[80,76,137,13,9,5,20,33,448,388,384,209,21,105,392,213,101,744,41,456,45,49,53,57,748,61,96,1,16,69,468,404,65,77,85,89,93,97,3,168,0,4,217,180,184,201,188,196,25,37,396,752,756,400,109,333,337,113,117,341,345,121,125,129,133],[31,33,970,15368,114824,8257546,125829258,134217730,4026531857,4831847440,9126887440,53151399953,207819374609,827854946560,1375463285760,2474974986240,30787400499200,246291728695296,281474976728064,562949953422336,3377716901576960,13510867651920128,91136,126100789567562752,432345568572875776,1747396655421014016,2449958205929897984,32281802403921133568]),([v87,v3,v2,v22,v5,v6,v40,v241],[212,21,20,752,13,388,208,69,16,788,9,404,36,3,396,25,101,792,37,392,796,384,45,113,756,800,61,400,137,149,209,105,29,33,804,229,109,49,233,57,808,161,65,77,81,245,253,93,97,285,0,169,136,224,8,201,228,232,357,345,193,125,133],[63,4032,14856,49152,2031624,6307840,260046856,268436561,536870976,3223322642,30065164305,515396091920,1657958039569,2199023255553,4400196093056,26388279461568,105621835760768,422212565731008,1688852009844736,15762598696190464,18014467228979712,252201579233411584,562952103329792,288230447020785664,4400305143808,576460821023244296,1153063346002853888,6917529130820976640]),([v3,v2,v22,v251,v5,v6,v40,v241],[688,692,137,33,9,149,756,13,48,20,384,401,21,25,29,684,37,836,129,808,45,49,53,400,113,161,404,16,405,69,73,77,81,548,85,89,261,269,40,3,0,169,680,217,700,704,12,65,392,396,752,61,101,105,109,117,125,121,133],[31,33,968,15368,115082,8257546,25166024,33554434,201326672,1879057424,15569354769,60667592721,206720466960,833290764352,1657857385472,7155415613440,61581242269696,70643647250496,140737496743936,282024732639296,1688849861705792,2251799822074880,13510798882186240,27021597765411840,36028797044139008,22517998138654720,216172784286498816,360287970216116224]),([v238,v3,v2,v22,v5,v6,v40,v241],[304,33,20,752,13,388,300,69,16,912,9,404,36,3,105,916,25,384,920,396,37,392,109,61,756,924,113,400,221,149,17,21,928,213,101,129,45,49,53,57,808,161,65,73,77,177,89,93,269,285,68,316,169,4,8,201,320,324,337,301,385,125,133],[63,4032,14856,507912,1572864,6815744,260046856,268436561,536870976,7516291089,25771900946,515396599824,1651515588625,2199023255553,13194139633344,17609368011904,105621836268672,422212565731008,3940649674048000,13510816064077824,18014467229487616,252201579233411584,4503616809451520,288230444871794696,576602590477910016,1152921590508814336,17609477062656,6917529130821484544]),([v3,v2,v22,v5,v248,v6,v40,v241],[568,572,137,13,9,149,17,21,564,25,48,756,20,392,417,33,37,421,956,41,808,45,49,53,400,61,317,161,65,69,73,576,404,16,425,81,85,89,189,97,285,3,560,40,4,217,584,588,12,384,101,105,109,125,117,77,396,229,752,113,121,129,133],[31,33,1994,7304,253960,16515082,117475336,134217730,4026532625,12884903952,52076552208,208845144081,825220923408,7698728878848,11001558730752,19793356857344,246292754464768,290271120066560,565148976679744,3377699720602368,6755399444464384,27021598082990592,36028797035741184,504403158267856896,576460752320208896,5629499536646144,1152921504657252352,6926536226948251648]),([v245,v3,v2,v22,v5,v6,v40,v241],[756,13,33,48,20,9,249,404,16,40,768,1036,25,784,333,384,3,37,1040,341,392,400,129,396,61,1044,1048,137,149,17,21,361,29,389,41,45,49,53,201,125,161,85,69,89,285,68,776,169,136,780,8,36,12,109,105,101,445],[31,481,3713,126977,2031617,6291456,27262976,234881092,301989888,3825229836,14026539020,257706426372,824635817990,1099578736640,570451040,4329309280,15427530915904,824635818080,123145302336512,985162419274752,3377734088655872,4504424263188480,4832714752,27021632132366336,824635838464,45036030642356224,824636473344,72058178163965952]),([v3,v2,v216,v5,v6,v40,v241],[1148,1,141,20,69,13,1132,473,16,21,0,65,29,33,1152,37,1156,41,45,49,53,57,1160,61,9,404,457,77,85,249,93,25,52,101,3,4,432,109,8,68,36,48,113,40,12,333,405,121,125,129,133],[255,1889,2664,61480,2031656,14688296,50332754,100665426,167821331,839188497,1119879187,2147483720,133144035328,2065879597056,32985361416192,8589985856,35321811372096,74766803273792,695785078784,147334704971776,1972523873140736]),([v3,v2,v412,v5,v6,v40,v241],[1196,1,145,20,69,13,1136,473,16,33,4,17,21,1168,25,77,1200,41,109,49,233,57,1204,113,9,404,65,461,85,249,93,88,105,3,0,620,37,45,8,136,36,48,61,40,12,117,341,425,125,229,133],[255,1889,30760,33384,2031656,14684200,50332754,100687891,167805010,839188497,1119879187,66572017664,68719476808,2063732113408,32985361416192,4295024704,691490086912,41781521571840,70506183491648,145135547482176,1972523873140736]),([v19,v3,v2,v55,v5,v6,v40,v241],[80,5,76,468,9,20,168,1224,3,1132,105,65,0,1136,101,77,4,1228,45,180,85,184,61,188,1232,93,196,1,13,473,33,209,21,213,41,49,57,16,157,404,153,161,25,37,177,1140,1236,189,1240,1144,245,333,261,405,341,425,125,129,133,96],[3,28,484,7680,122880,4063236,130023428,939524101,1342177316,6710888960,9932152832,51809222660,70111985668,962206892041,1099645849088,275012182016,2199158915081,2199211999241,4398046519808,8796093022720,123145303490688,985162468819072,43520,3377699721710080,13510798932445696,18031990696747008,36169534557691904,1080863910620430336]),([v87,v19,v3,v2,v5,v6,v40,v241],[212,20,1236,3,36,21,13,208,1,16,788,161,404,1140,333,77,1244,37,1136,796,1132,85,261,1240,1248,93,1144,149,9,105,65,0,224,136,109,8,245,61,228,232,489,209,29,33,229,49,57,153,157,353,285,297,405,493,497,1252,189,193,197,125,133],[31,99,8064,24576,1015812,3153920,130023428,134217856,268436481,3759144960,12885131265,120259092480,962123005953,1099511630017,2200098046048,13194139729985,52845277618240,79164887531585,140739100018688,844424930364544,85899356416,137489288576,1125900981796864,2251869607960576,4503600756686848,27021666483871748,540436353381498880,1729399917866131456]),([v238,v19,v3,v2,v5,v6,v40,v241],[304,20,1236,3,36,33,13,300,1,16,912,161,404,65,1276,25,1132,920,1140,341,1136,85,189,1240,1280,93,1144,149,9,316,68,101,77,4,45,8,177,113,320,324,489,17,21,213,129,49,57,153,381,157,169,509,513,1252,261,301,305,185,425,125,133],[31,99,8064,253956,786432,3407872,130023428,134217856,268436481,1610670081,15033434112,120259346432,962123005953,1099511630017,6597069815873,8800389038176,52845277872192,74766841020481,422212465126528,562956396922880,85899610368,137489288576,1125904202915840,6755468160835588,135110187894751232,144115261091610624,288230380502253568,1729399917866385408]),([v3,v296,v2,v5,v6,v40,v241],[1304,0,21,5,13,1320,404,16,153,9,473,17,388,1324,169,145,1328,37,1332,217,149,45,201,1336,61,1340,69,25,52,101,3,4,60,109,8,68,36,113,40,12,77,81,85,89,93,97,209,401,181,193,125,133],[127,1933,6157,258056,3944456,63971336,67109507,134217857,8321695744,129119813632,962366275584,67111553,3298602189440,13194209002112,52776650408576,70369281181697,70377336473601,140874952476673,285907922386944,581642750197760,3377734108315648]),([v3,v298,v2,v5,v6,v40,v241],[1308,4,33,5,13,1404,404,16,157,9,473,1408,285,141,1356,25,388,29,1412,217,149,109,201,1416,113,1420,69,88,105,3,0,128,37,45,8,136,36,61,40,12,65,73,85,253,93,269,213,293,301,417,125,133],[127,1933,129032,196621,3999752,63965192,67109507,4160798720,4294967425,128985595904,962232057856,3298602041984,67240577,13194209002112,52776650408576,70369012793345,145170165448704,300167236468736,70377336602625,563087417671681,3377734108315648]),([v20,v3,v2,v55,v5,v6,v40,v241],[80,468,13,1,16,168,1348,3,1304,105,209,0,1308,101,213,4,1456,45,180,41,184,61,188,1460,57,196,5,9,76,473,20,145,388,141,149,456,96,69,65,77,85,93,17,29,129,1312,1464,1468,1316,229,333,113,401,545,341,417,549,125,205],[7,9,241,3840,61440,2031617,65011713,1006632961,7851737152,8657045248,2214621184,51875872768,86262153216,137573171217,412451079424,687329005568,1237085388801,2336621592577,4398046515456,8796093022464,123145302900800,422212492329024,21760,1688849860855040,15762598720963840,18031990696136704,108086391084175360,432363156439367808]),([v87,v20,v3,v2,v5,v6,v40,v241],[208,16,1464,3,36,212,5,20,149,388,69,9,1312,17,213,1480,29,1308,1304,41,113,1468,1484,57,1316,788,13,161,105,209,0,37,224,136,109,8,229,61,228,232,489,141,349,804,1488,65,77,81,245,93,285,565,401,545,569,533,557,125,277],[31,996,3075,12288,245772,790528,32505860,100663297,134217729,1879310336,15032483841,120259088384,962085257217,1099511630113,2199828824320,13196287115552,85899350336,17729637581152,35184909224960,211106232634369,281543696194560,562949966007297,1125900444057600,2251869070299136,13510799432876032,18014467229044740,36046528804126720,504403226997559296]),([v20,v3,v2,v251,v5,v6,v40,v241],[688,548,33,161,1468,40,3,16,1304,25,401,0,37,1444,29,680,1532,45,700,129,704,1316,113,12,149,9,692,489,5,48,20,141,145,1488,404,405,69,73,77,81,85,261,269,17,213,1308,41,1312,1464,57,229,581,529,125,417],[7,9,241,3840,61505,2031617,14680112,251658241,1895825424,2164262656,4915752960,12969508864,291504144,17213423761,240551724288,893386776577,1168265248769,6665829089280,8796095119360,52776558157904,492581209833488,562949955518720,17592186062592,1125899907434240,2251799819977984,4591569148141568,27021597770530816,9077568005734400]),([v238,v20,v3,v2,v5,v6,v40,v241],[300,16,1464,3,36,304,5,20,149,388,69,9,209,1576,17,1304,1312,29,1308,41,61,1468,1580,57,1316,912,13,161,25,316,68,101,213,4,45,8,129,113,320,324,489,377,928,145,1488,65,73,77,177,93,169,605,525,609,417,549,553,125,205],[31,996,3075,61452,196608,851968,32505860,100663297,134217729,1879072769,15032647680,120259149824,962085257217,1099511630113,6597338226976,8802535735552,85899411776,17729637581152,105553116294145,140741783587840,281543696256000,562949966007297,1125904202100736,2251868533248004,4521329533411328,9007272269512704,54043199837306880,504403226997620736]),([v20,v3,v2,v5,v248,v6,v40,v241],[568,576,13,161,25,1392,17,560,3,1468,40,16,1308,37,417,4,1620,45,584,41,588,1316,61,12,149,9,572,489,141,48,5,20,145,1488,65,69,73,404,425,81,85,189,97,209,1304,229,521,125,401,29,1312,1464,57,129,529,617,621,205,613],[7,9,497,3841,61440,2031617,14681600,251658241,889192560,3774874112,4311773184,9748283392,1096811008,120292638817,137472510465,859027034112,1133905510401,6631469350912,26388279067488,8796093050976,114357799813216,422212471357504,562949955518464,3412884093207040,4503599629471744,63050394783805440,72057594044239872,441493500977479680]),([v245,v20,v3,v2,v5,v6,v40,v241],[1468,40,1044,1036,16,5,149,48,20,9,249,209,1476,17,1304,3,213,1664,29,1308,1316,129,1312,57,768,33,161,333,776,68,341,780,136,45,8,41,125,12,1048,489,377,501,349,517,201,85,69,577,557,521,401,553,529,417,561],[31,481,1557,63489,1015809,3145728,13631488,50331652,67108868,939536388,7516585988,60133736448,206159478787,824633721924,3573547020480,13470091575488,42953867360,17660906569824,134231556,1074136580,105587480200192,17660906571264,140738696753152,844459294074880,1143560813420544,6755433805316096,9024860161572864,18014501593939968]),([v142,v3,v2,v5,v6,v40,v241],[1696,33,0,13,1684,21,4,88,9,16,1700,1,404,105,25,17,20,101,1704,45,8,136,109,36,48,61,40,1708,113,12,141,221,281,37,41,233,57,237,241,285,153,289,3,69,81,245,161,253,257,261,269,273,521,525,201,229,277],[127,8064,57349,196624,16515200,1056964608,3221293344,4295008291,8590000179,52617871392,481439055904,3848290732033,30794915514384,527765587888128,4011018837559296,8589975553,4504166567542785,9007268376911873,4406641426448,9026142224,126100789990260736]),([v14,v3,v33,v2,v5,v6,v40,v241],[1740,13,408,16,604,3,20,69,404,25,1684,77,4,1744,109,1748,45,1752,113,1756,1760,61,1764,49,21,157,141,449,17,169,41,57,237,9,209,0,37,1688,1768,1772,1692,285,461,85,249,89,321,93,325,97,329,401,341,181,185,425,193,197,125,229,133,616],[3,124,412,529,7216,253968,8126480,25165908,117440644,419430417,562039808,1098981392,6462373904,8589935616,51808043009,68719477764,412316950532,1649270849540,2199325245569,4398046514308,131941395406980,2111062328475780,17985177601,17448394753,2251800085528577,31533993484692480,252342316624251904,4323455642278895616]),([v67,v14,v3,v2,v5,v6,v40,v241],[1408,20,1320,3,404,21,141,1684,9,1792,17,285,0,408,77,1796,45,1688,85,1768,61,1772,1800,93,1692,5,69,16,25,101,37,4,245,1804,1808,261,1812,1816,157,281,29,49,217,377,201,237,81,249,89,321,325,97,329,209,401,1420],[31,99,384,7680,24704,1015812,32505860,33554944,201334801,268435969,3758096512,30065065985,240530751489,274945024097,549755816513,3299608625344,13194139828289,52776570716225,274945019392,70369885036672,985162485964804,7881299428646916,9007200865356288,4295265792,18014432881805824,1610973312,1100599001216,36050787264397312]),([v14,v3,v2,v5,v6,v40,v235,v241],[1840,13,408,69,16,1844,404,25,101,1848,37,1852,136,1688,109,8,45,20,1320,3,113,1856,1860,61,1864,1,141,21,449,17,29,49,41,377,57,237,285,289,77,89,9,93,209,0,401,341,1684,1868,193,85,125,129,133,1772,1692],[3,124,161,7968,122880,917600,32505888,234881068,939524129,3355444768,6576742400,8724283424,51686408224,206728855561,274911725068,549755887628,1099511635968,2199069655052,4398583383297,4398583472128,8796630679553,17592736546817,91392,105553117054464,424686378812928,562949953429508,7881299360555008,27023796800323584]),([v236,v14,v3,v2,v5,v6,v40,v241],[408,16,1948,3,20,49,21,1688,9,1952,209,17,0,101,1956,37,1684,45,93,1772,1960,61,1692,13,69,404,25,29,1964,136,245,8,85,113,1968,1972,1,141,361,637,217,57,237,285,77,369,577,401,177,181,1868,121,125],[31,117,384,7680,122889,131201,8126465,8389120,50331655,67109380,939573252,7516192896,60132687876,206175207489,274877909572,549890080836,1103806595296,6597072912452,8864829278720,17660922347521,35188683833473,68739661825,70368744222208,5368712320,140746081438208,844429225140352,3377708447875072,4504703437111424]),([v238,v14,v3,v2,v5,v6,v40,v241],[304,20,1768,3,36,49,21,69,408,9,1320,316,209,17,0,1688,37,1684,85,61,1772,2012,93,1692,13,161,300,912,25,101,4,129,8,45,113,320,324,377,501,213,57,237,285,381,77,177,89,1868,269,169,605,401,385,125,133],[31,99,1924,30720,98304,425984,16252932,16779264,234881537,268437505,1610743817,15032418304,120265375745,137472508481,274877917249,550292815968,10737451104,3298541174849,13194139544192,17592723047040,105561706234496,422229684781568,562950490306560,1125908496824320,2251816999856128,4503608754339840,17592729862144,27021608507965440]),([v31,v3,v2,v413,v5,v6,v40,v241],[1132,13,1148,388,2048,404,1,16,2052,17,37,2056,29,2060,2064,45,41,2040,61,2068,57,2072,141,21,0,25,225,49,237,2076,9,65,169,157,173,217,161,201,77,2080,2032,85,2036,2084,93,2088,2044,101,105,109,113,129,529,2092,533,205],[3,124,132,769,15368,245768,3932168,12583005,29360133,109052161,142613768,142721288,815530240,1073741840,2181038145,30064777300,103079297108,206160003156,2197815297,1924145354768,15393162870800,123145303883792,422212498624513,844424963768321,1125902089453569,6755403736242176,27021597766065152,38280734273388544]),([v31,v414,v3,v2,v5,v6,v40,v241],[1148,2048,404,24,5,16,1,388,2096,285,37,2100,29,2060,2104,45,41,2040,61,2108,57,141,21,0,20,9,65,25,2032,280,2036,2084,2088,2044,225,49,237,2112,169,157,173,217,161,201,101,105,109,113,129,529,2092,533,205],[7,24,225,776,15488,245888,1843328,31457289,33554433,209715208,805313537,3221340161,12886736897,6291657,17318281480,34363940224,34364047744,206164459776,201326664,1924145354817,6597069848641,13194141106241,52776692355080,105553250566152,140737691254792,844699808258048,3377699722370048,4793870698889216]),([v64,v3,v2,v5,v6,v40,v241],[168,13,388,9,16,1,404,1696,17,2032,29,2116,45,8,41,36,61,40,2120,57,12,76,145,33,209,21,25,225,213,37,309,49,53,313,96,317,65,69,73,77,81,217,161,2040,2092,201,101,105,109,113],[3,124,388,1540,63492,2031620,14680108,260046976,1920991872,6452959236,60140879872,481103446176,1787243266592,15393162807328,57174605430816,211106836512896,422212532193408,563018740793472,70369281071616,550293537280,46179489171456]),([v31,v3,v143,v2,v5,v6,v40,v241],[2124,33,2032,4,388,9,1,2060,108,209,29,2128,109,41,2040,113,2132,57,49,0,21,141,25,225,233,237,120,241,1148,2048,105,37,2036,2084,2092,2088,2044,65,69,73,169,157,173,217,161,201,129,529,61,533,205],[3,12,240,769,1044,30736,229520,1835013,3146096,13631745,1311765,19937552,236159232,805306592,1078460417,2147483668,12884932608,120259313664,962076868673,7696581395524,26388279093312,52793738199104,1077937153,1077950465,137443377153,212205744172036,844442110198788,1231453023332352]),([v3,v143,v2,v5,v6,v40,v241],[2124,33,0,21,2032,4,13,108,153,141,388,9,209,25,225,29,2128,229,109,233,57,237,2132,113,241,120,88,69,16,3,404,105,37,45,8,136,36,61,40,12,65,73,169,85,253,93,269,293,301,125,133],[127,3976,28683,33819,984712,66060424,2080376832,2147491845,4294968336,128916455424,962152366080,3298669111297,4398180763664,26422773352448,105553799940096,2147524609,149535729197057,317758873018369,4406636806160,137988440080,1688884233043968]),([v31,v3,v415,v2,v5,v6,v40,v241],[2268,13,2044,12,388,69,1,2072,2060,2272,401,77,2276,29,2280,45,2284,41,2088,40,57,237,21,0,141,48,221,65,225,49,389,657,2048,1148,25,2032,52,2036,229,2084,61,2080,169,157,173,280,217,161,201,109,333,513,129,529,37,533,205],[3,12,496,1537,14608,245760,1835012,14680069,121635424,406848001,1648376320,2688795136,7602180,12885164128,17314086917,103079491584,962073083904,1099511889924,17314087009,68169720934464,211106232746048,422212466114628,17314097153,3940649808314369,17315135493,13515196928847872,54043195529764868,76842668643188740]),([v31,v3,v33,v2,v5,v6,v40,v241],[1740,13,1148,16,2060,3,388,69,157,604,17,2032,77,169,4,2288,109,1748,2292,41,1752,2296,113,1756,2300,57,1764,2080,49,21,20,141,25,225,233,237,616,241,1,105,0,29,129,2036,2084,201,2088,2044,65,173,217,249,325,341,61,425,433,205,2304],[3,124,396,1537,30720,4161536,266338304,1879048260,2684354948,13421773313,805320704,17987895808,241109565952,274877908992,1653562408961,2199023257604,30786326134788,246290654953476,281479271678337,562949953431812,3377699721085188,4538784049791236,554050793473,554051403777,281479326203905,9011597301819392,126100789616715776,432385146697056256]),([v67,v31,v3,v2,v5,v6,v40,v241],[2048,404,2060,3,388,1408,21,20,141,2032,1,1792,25,0,1148,169,2328,41,2036,217,2084,57,2088,2332,201,2044,5,69,16,157,285,37,29,4,85,1804,2336,1808,2340,93,1812,1816,280,477,49,377,237,1420,65,541,249,325,101,105,245,261,129,61,533,661,2304],[31,497,1536,14345,49664,2031617,65011713,67110912,939540483,1073743904,15032386048,532576534528,8521240281088,671105377,8796093028640,17598628496128,35476430455072,211656013512992,281475647805440,562954785276416,1125900444450817,2251800377835521,13510803177084928,27021597764818944,36310272020846592,76561197960856064,432345570695184896,1729382823871709184]),([v31,v3,v2,v5,v6,v40,v235,v241],[1840,13,1148,69,16,2048,1,404,1844,17,2408,37,2040,2412,29,1852,136,2036,45,8,41,388,3,2284,61,1856,2416,57,1864,141,21,25,225,49,20,377,237,65,169,157,173,89,161,201,101,105,109,333,0,113,129,529,341,2032,533,217,205,93,2088,2044],[3,252,769,130048,1966080,6295712,528482304,1610613100,7516193025,9663704320,9665118208,52615446816,70019711232,139586437193,1924145373284,2199024435268,4398046642176,9346050162788,52778705633281,105555264929792,422214612549633,563089741185025,3377974599630848,13510798886330400,18014398736001024,36028797019095044,73192290240299008,1008806316732317728]),([v236,v31,v3,v2,v5,v6,v40,v241],[1148,16,2040,3,388,49,21,20,2036,161,1952,105,25,0,169,2448,29,2032,41,201,2088,2452,57,2044,13,69,1,1948,17,2456,37,1964,136,85,8,217,2284,61,1968,1972,141,225,637,237,65,157,573,101,373,245,113,177,429,533,661],[31,241,768,15360,245769,262401,16252929,16778240,100663299,402654208,8053161988,60129542400,1030798442496,1099612291137,2199157478464,4399791439936,42949673312,9002391961664,17592286712832,35184439312385,70403171025153,35184446013441,422212465138688,562984313166080,1143492099183616,6755433800876288,9007406493302784,18014441465970944]),([v31,v3,v255,v2,v5,v6,v40,v241],[2192,33,2088,40,2092,3,388,1148,9,16,1,2480,17,2208,37,2200,29,2196,2484,45,2212,2284,129,2216,2044,93,201,12,141,48,21,20,25,225,49,389,657,237,161,0,169,2032,41,2036,2084,57,65,265,73,325,217,673,101,105,109,261,529,189,433],[3,124,1920,6145,254000,16515072,251658240,4026531844,1342178688,13958645761,53150337024,86980167680,138630135808,274894684160,554050781221,3298534981668,30786330034180,35184388866052,492585504211969,564049465148544,1125899911300480,2251799897572356,13510803177144321,27021602063646721,36099170141995008,72063091602718720,432345564311535616,4398168145920]),([v254,v31,v3,v2,v5,v6,v40,v241],[2088,40,2092,3,388,21,141,48,20,2044,161,2232,25,65,0,29,2228,169,2032,2548,41,2036,217,2084,201,149,1148,9,16,2048,1,404,2552,285,2240,77,2236,45,2244,2284,2248,61,57,12,477,49,685,377,645,237,265,73,325,173,677,689,109,333,513,113,129,341,429,37,533,125],[31,481,1536,30720,491529,16252929,16777729,33556480,4227858432,12884903936,120259280908,2061589020672,15393162789376,6106906720,17596481022016,105591771168960,422903959519296,569547023188544,3377700794284032,13510800560062464,18014400327188480,36033196139217409,34359883776,504403158270224384,576465150349947392,8070451082008657920,27670122707634225664,36893492545470857728]),([v238,v31,v3,v2,v5,v6,v40,v241],[2084,36,2040,3,388,304,49,20,21,1,1148,161,2048,316,105,25,0,2036,29,2032,41,201,2088,2604,57,2044,13,928,9,300,912,17,101,169,4,45,8,129,2284,113,320,324,377,225,237,241,65,69,73,157,177,93,701,337,609,61,433,553,205],[31,497,7681,122880,393216,1703936,65011713,67117056,2013267972,2147491872,30065295360,240518299648,4123193769984,4398449166624,8796093063456,12885426496,171798823232,53601217020192,492581209286656,562962838849536,1126037345929728,6755674612566016,12884959232,9007336693882880,70918525198336,18014544539025408,108086403967483904,432345701693915136]),([v31,v3,v2,v5,v248,v6,v40,v241],[560,13,2628,9,568,2092,161,576,572,17,2088,40,3,388,2032,37,4,2632,45,584,2284,41,588,2044,61,12,141,48,21,25,225,49,20,417,237,65,69,73,1,2048,1148,425,157,217,189,0,101,105,109,125,117,29,2036,2084,57,129,529,617,121,205,613],[3,252,769,15392,118816,8257536,58723328,469762376,1879048449,6845105152,11005902848,2419458304,17473471488,241055039553,1924145349696,6597069815872,9070974206016,17867089117248,35184908964865,211106769436673,422213004165121,1688884782039040,2251799822073856,13519594977362944,18014398517886976,252271947879202816,288230376176926720,1765974003909918720]),([v245,v31,v3,v2,v5,v6,v40,v241],[2088,40,2040,1036,388,49,21,48,20,1,161,2048,1148,776,25,333,0,169,2688,29,2032,3,2044,129,2036,57,33,2692,249,1044,768,1048,17,341,780,136,45,8,41,125,201,12,377,221,225,637,389,237,709,2304,353,85,677,109,105,553,529,37,433,561],[31,481,7681,122880,4063233,12582912,54525952,67117056,2013266948,6442459136,60264546308,481053114368,3848294891520,13196555453632,17594333569088,105563854471360,343614160992,423861736702016,268493824,1688858719421440,6755674335741440,1649271637504,8590516224,27021872658939904,1649271685120,108086665952231424,432347213499727872,576462126713929728]),([v218,v3,v2,v5,v6,v40,v241],[2032,21,4,13,2124,33,0,52,9,16,2060,1,404,20,105,101,37,29,2720,109,8,68,45,36,48,113,40,2724,61,12,145,137,25,165,41,53,57,313,317,3,69,73,169,157,173,177,161,89,321,189,97,329,529,533,201,129,205],[127,8064,24592,229457,16515200,1056964608,3221236000,4294975538,8590098483,52617814048,481438998560,3852585666576,30786325710849,527765587888128,4011018837559296,4295131153,554055761936,4731174928,4508014858338305,9007268377034753,126100789990260736]),([v139,v3,v16,v2,v5,v6,v40,v241],[2752,13,600,16,412,3,20,69,404,2124,65,0,37,2756,45,2760,109,2764,61,2768,2772,113,2776,49,33,153,145,285,453,29,41,57,313,9,25,213,4,2712,2780,2784,2716,457,169,85,249,253,257,93,265,269,273,333,293,297,405,301,305,417,125,129,133,428],[3,124,412,3632,4113,253968,8126480,25165908,117440644,159385088,822083601,1098981392,6462373904,8589935104,17179869700,103616086017,412316950532,1649270849540,2199023257220,4398616936577,131941395406980,2111062328475780,35030828544,15771394788894208,126241527057876480,34896699393,144115188616134657,4323455642278895616]),([v10,v139,v3,v2,v5,v6,v40,v241],[1324,20,1404,3,404,33,145,2124,9,600,65,2800,29,169,4,2804,109,2712,85,2780,113,2784,2808,93,2716,5,69,16,105,25,0,37,177,2812,2816,189,2820,2824,153,17,49,165,217,349,201,313,73,249,253,257,265,269,273,213,417,1340],[31,99,384,1664,30720,1015812,32505860,33556480,201327121,1879048320,2147485697,30065065985,240530751489,274945016417,1649804312768,2199023265857,13194139828289,52776570716225,70369348158080,274945030144,985162485957124,7881299428639236,9007200060055680,805666944,550306316416,4295276544,18014432881813504,36050787264397312]),([v139,v3,v2,v5,v6,v40,v235,v241],[1852,13,600,69,16,1844,404,105,2848,25,1840,68,37,2712,45,8,109,20,1404,3,61,1856,2852,113,1864,1,145,33,17,49,453,29,41,349,57,313,65,169,173,253,9,93,213,333,2124,2856,301,4,417,85,125,129,133,2784,2716],[3,124,4000,4129,122880,917600,32505888,234881068,939524896,3355443233,4966129664,8724283424,51686408224,68753294092,414497898505,549755887628,1099511635968,2199069655052,4400193995649,90752,26388279853824,107820871582464,4400194084864,140739636625409,281477137825793,562949953429508,7881299360555008,27023796800323584]),([v236,v139,v3,v2,v5,v6,v40,v241],[600,16,1948,3,20,49,33,2712,9,105,2912,25,2124,1964,213,29,4,109,93,2784,2916,113,2716,13,69,404,17,1952,68,37,177,8,85,61,1968,1972,1,145,637,389,217,57,313,65,169,369,577,245,293,2856,117,417,125],[31,117,384,7689,122880,131201,8126465,8396800,50331655,469765124,536879108,7516192896,60132687876,206175207489,274945018948,549755854916,1103806595296,6597072912452,8864829279233,17660922339328,35188683833473,68739661825,70368744238592,422216760035968,1688858520456192,5368758400,2251808406806528,4504703437111424]),([v87,v139,v3,v2,v5,v6,v40,v241],[212,20,2780,3,36,49,33,69,600,9,1404,2712,25,224,213,29,4,2124,85,113,2784,2956,93,2716,13,161,208,788,105,0,37,229,8,109,61,228,232,349,209,517,57,313,65,169,353,245,253,2856,97,285,357,569,417,125,133],[31,99,1924,6144,122880,395264,16252932,16785408,234881537,805437449,1073750017,15032387584,120265375745,137472508481,275146473568,549755854913,10737420384,3298541174849,4398315078272,26388279108224,105561706203776,422229684781568,562950222036992,1125908765345792,4398321893376,2251808403679232,4503616813572096,27021608507934720]),([v34,v3,v2,v416,v5,v6,v40,v241],[1136,13,1196,388,2984,404,1,16,25,2988,17,1700,2992,29,2996,45,41,2040,61,3000,57,2072,145,33,4,49,37,309,53,313,3004,317,9,285,153,289,77,217,161,201,65,2080,1696,85,2976,3008,93,3012,2980,101,105,229,521,2092,113,525,277],[3,124,132,3848,12289,245768,3932168,12583005,29360133,41948936,209719297,310497288,3768324096,4294967312,60129543764,68786585665,412316942420,824635293780,7696581395984,68803362817,61572651237392,492581210816528,1688849927374337,6755408031204864,63050394784761600,562950020644865,68788420609,74309943609212928]),([v34,v417,v3,v2,v5,v6,v40,v241],[1196,2984,404,28,5,16,1,388,25,3016,17,1700,3020,169,3024,45,41,2040,61,3028,57,145,33,4,20,9,1696,280,77,37,2976,3008,3012,2980,49,309,53,313,3032,317,285,153,289,217,161,201,101,105,229,521,2092,113,525,277],[7,24,225,3968,12296,245888,1837184,31457289,33554433,201328385,813694984,3221340161,12886736897,6291657,17184069504,34900807688,85903659136,962078707712,7696581396033,805306440,26388279148609,52776559706177,211106769405448,845524441974272,7881299349473024,70369281163272,807141384,9323858605326336]),([v34,v329,v3,v2,v5,v6,v40,v241],[1696,0,1684,21,388,9,1,1700,17,148,213,3036,45,41,2040,61,3040,57,49,33,4,1196,2984,25,101,37,2976,3008,2092,3012,2980,145,309,53,313,160,317,285,153,289,77,157,81,217,161,201,229,521,113,525,277],[3,12,240,273,1540,30736,229520,1835013,6291680,8388625,50331653,201357312,1879277568,2148008560,786705,4329046532,10737957392,120259838464,962072674625,7696614948932,26388279093312,52776826765376,50331909,211243671496961,844425198764289,50345988,1099545411588,1231453023332352]),([v329,v3,v2,v5,v6,v40,v241],[1696,21,0,33,1684,4,13,52,69,16,3,9,404,388,25,101,37,3036,109,8,68,45,36,113,40,3040,61,12,148,157,145,17,213,309,129,53,57,313,317,160,285,77,81,85,89,93,97,181,193,125,205],[127,8064,24577,98325,8257664,260046976,1879058440,2147491851,12884967451,52884021256,1031161249800,1101659113729,6597606705168,26388819216384,105553753803776,2147581969,1101661601793,2256536577,149533583704080,318858472783888,1688867144073216]),([v34,v3,v418,v2,v5,v6,v40,v241],[3124,13,2980,12,388,69,1,2072,1700,65,3128,17,3132,417,3136,45,3140,41,3012,40,57,313,33,4,145,48,137,49,361,77,309,657,2984,1196,1696,88,37,2976,129,3008,61,2080,285,153,289,280,217,161,201,229,521,25,525,341,497,277],[3,12,496,3856,12289,245760,1835012,14680069,121639008,440409600,1614811137,2286145536,7602180,12885164128,51539873280,69256347653,962073083904,1099511889924,68169720925248,69256347745,211106232746048,422212466114628,69256351233,1693247906991104,6755399442368516,27021598301274113,69257396229,36873221950275588]),([v34,v3,v16,v2,v5,v6,v40,v241],[2752,13,1196,16,1700,3,388,69,153,1696,65,285,0,412,29,3144,45,2760,3148,41,2764,3152,61,2768,3156,57,2776,2080,49,33,20,145,37,309,53,313,428,317,1,17,101,4,229,2976,3008,201,3012,2980,289,77,217,249,265,333,113,405,397,277,2304],[3,124,396,7680,24577,4161536,266338304,1879048260,2684354948,805309952,13421780993,17987903488,241109573632,274877907456,549755814404,3302829850625,30786326134788,246290654953476,281474976713476,562954248388993,3377699721085188,4538784049791236,1103806598656,9011597301811712,126100789616708096,1103807217665,562954302914561,432385146697056256]),([v10,v34,v3,v2,v5,v6,v40,v241],[2984,404,1700,3,388,1324,33,20,145,1696,1,1196,285,2800,37,4,3180,41,2976,217,3008,57,3012,3184,201,2980,5,69,16,153,25,17,0,169,85,2812,3188,2816,3192,93,2820,2824,280,49,485,349,313,1340,537,77,249,265,101,105,229,113,525,177,189,661,2304],[31,497,1536,6656,57353,2031617,65011713,67117056,939526147,7516193280,8589942816,532576534528,8521240281088,671091041,8799314248448,17592186069280,35476430455072,211656013512992,281477661067776,562950624534528,1125900444436481,2251800377821185,13510801029612032,27021599912296960,108086394303283712,148618787703840768,288793326130323456,1729382823871709184]),([v34,v3,v2,v5,v6,v40,v235,v241],[1852,13,1196,69,16,2984,1,404,2408,25,2040,3256,17,1840,68,1844,29,2976,45,8,41,388,3,3140,61,1856,3260,57,1864,145,33,49,37,309,53,20,349,313,317,285,153,289,77,89,161,201,101,105,229,521,333,1696,113,525,341,4,217,277,93,3012,2980],[3,252,32512,98305,1966080,6292640,528482304,1610645612,3221265152,13958676481,20402536448,104155086880,413617127424,3848290703460,4402341478473,8796094201924,17592186175488,36284085043300,211110527506433,844974687129600,3377699724728352,13510799091833344,70373040586752,54043199823413249,4402559582209,72057594038059012,144431847627161600,2017612633263308832]),([v236,v34,v3,v2,v5,v6,v40,v241],[1196,16,2040,3,388,49,33,20,2976,161,285,3292,17,1696,1964,101,37,4,41,201,3012,3296,57,2980,13,69,1,2456,25,1952,68,1948,29,85,8,217,3140,61,1968,1972,145,637,309,313,317,153,77,573,105,373,245,393,113,525,177,661],[31,241,768,15369,245760,262401,16252929,16793600,100663299,2013272068,6442467328,60129542400,1030798442496,1099612291137,2201573398592,4400194076736,42949673312,26596591272000,35184439204865,70368844922880,140771915202817,35184446013441,844424930252800,3377734080271616,13510867876321280,18014432869318912,70506189504512,36028839975452928]),([v34,v3,v255,v2,v5,v6,v40,v241],[2196,21,3012,40,2092,3,388,1196,9,16,1,2208,25,3092,17,2192,2480,29,3320,45,2212,3140,229,2216,2980,93,201,12,145,48,33,20,49,361,37,309,657,313,161,285,1696,4,41,2976,3008,57,265,77,325,81,217,725,101,105,521,261,397,189],[3,124,1920,63536,196609,16515072,251658240,4026531844,1342178688,14495608832,52613414913,74095329280,138630135808,274894684160,1649267466276,2216203124773,30786330034180,35184388866052,70918500017280,985179598357505,1125899911300480,2251799897572356,13510816062005249,18019346318385152,108086391140798464,4503616812220417,144255942827966464,4398168145920]),([v254,v34,v3,v2,v5,v6,v40,v241],[3012,40,2092,3,388,33,145,48,20,2980,161,17,3100,285,1696,2236,37,77,4,3376,41,2976,217,3008,201,149,1196,9,16,2984,1,404,2240,65,2232,2552,169,45,2244,3140,2248,61,57,12,49,733,485,349,693,313,317,265,289,325,81,677,689,229,333,393,113,25,525,341,497,125],[31,481,1536,30729,491520,16252929,16777729,33587200,4227858432,30064783372,103079247872,2061589020672,15393162789376,36171677792,52819507818688,70403104079936,422934024290368,1695446930031168,6755401118791680,27021598838194176,36028798836670464,72061993158181377,8590176256,1008806866291535872,8070454930294448640,27670116248008163328,6597069963776,36893492545470857728]),([v87,v34,v3,v2,v5,v6,v40,v241],[3008,36,2040,3,388,212,49,20,33,1,1196,161,2984,2976,17,224,101,37,4,1696,41,201,3012,3428,57,2980,13,804,9,208,788,105,285,0,29,109,8,229,3140,61,228,232,349,309,313,317,153,77,69,81,245,93,701,565,113,397,345,557,277],[31,497,7681,24576,491520,1581056,65011713,67141632,2013267972,15032909824,17179901984,240518176768,4123193769984,4398449166624,6442975552,8796093186336,171798700352,53601217020192,70375187154944,985162418653184,1126037345806848,6755674612566016,6443171840,9007340989194240,54043201996587008,72057731477118976,141287269498880,432345701693792256]),([v34,v3,v2,v251,v5,v6,v40,v241],[680,13,3452,9,688,2092,161,548,3012,40,3,388,1696,25,0,692,29,3456,45,700,3140,41,704,2980,113,12,145,48,33,137,49,20,401,37,309,53,313,1,2984,1196,405,153,77,69,81,217,261,17,4,2976,3008,57,101,105,229,521,597,117,125,121,277,601],[3,252,3872,29728,98305,8257536,58721024,1006665800,3623878912,5637156864,26038272001,35705487360,69013078272,962072674624,3298534895680,30794915512385,35321814319168,70506208297024,140737496743936,281483566646529,1724034234581248,2251799822077952,13510807472058368,135107988823355392,144115188101033984,4503608219795457,864695535116746752,3765009288508997632]),([v245,v34,v3,v2,v5,v6,v40,v241],[3012,40,2040,1036,388,49,33,48,20,1,161,2984,1196,285,3508,17,1696,3,780,37,341,4,2980,229,2976,57,21,2692,249,1044,768,333,776,68,1048,29,45,8,41,125,201,12,349,137,637,361,309,53,313,709,2304,381,85,677,557,521,25,397,101,561],[31,481,7681,253953,3932160,12582912,54525952,67371008,2013266948,15166652420,51539869696,481053114368,3848294891520,13211587839168,52795885535424,70385925357632,141081102516320,846074201768000,3377702136497152,270271488,13511073776797184,1649271637504,2149367808,54043470423171072,216174431385452544,288230719766921216,1649273208832,576462126713929728]),([v3,v16,v2,v5,v6,v40,v194,v241],[3544,49,388,20,153,5,69,3528,285,65,281,412,29,3548,37,3152,2760,53,45,13,57,3552,61,3556,9,25,101,3532,136,109,8,16,36,2764,3,113,3560,3536,457,77,85,249,404,93,265,333,0,405,2752,121,41,125,133,2768,2776],[15,115,1954,63522,460802,589824,15730722,16777344,33554561,469786625,1610940416,32212254721,240524460033,274877907649,549755838545,3298535211072,4408783929409,26388285358145,67126144,35184909287936,70394513982080,140771854385792,604323840,281500746543104,563534083678208,1125899906910208,6755399447674880,27021606361497600]),([v10,v3,v2,v5,v6,v40,v194,v241],[1324,49,20,3636,5,388,3528,9,3544,65,37,3640,169,3532,136,2812,45,8,85,404,36,2816,3,61,3560,3644,93,3536,153,69,17,25,145,165,3192,693,149,201,3648,73,249,16,265,101,105,109,0,113,177,181,185,29,2800,189,193,197,217,57,2820,2824],[63,192,832,31752,491520,7864328,260046856,805306651,3221225554,30064778257,34360033297,68719509504,416712491025,552440168768,805313800,1100048859136,2199562748168,4398692434184,26390426554432,52778705911808,70371965403200,140740810244160,1970324837274624,6755399447353344,63050669761764352,72057594037960705,137539911680,1008806316633751552]),([v3,v33,v2,v5,v6,v40,v194,v241],[3544,49,388,20,157,5,69,604,17,3684,25,2296,3532,169,77,165,1748,233,109,13,57,3688,113,3692,9,105,3528,68,37,45,8,16,36,1752,3,61,3560,3536,65,461,85,249,404,93,325,1740,117,341,4,425,41,125,133,1756,1764],[15,115,4002,61474,458882,589824,15728802,16781312,234882561,268439553,1610940416,32212254721,240524460033,274877908561,549755834433,3298535211072,4408783929409,26388285358145,33584640,570754048,35210141894400,70677996504576,140738025570304,281500746534912,562984319471616,1125899906908288,6755399447674880,27021606361497600]),([v67,v3,v2,v5,v6,v40,v194,v241],[1408,49,20,3636,5,388,3532,9,25,3752,285,3528,68,3544,77,1804,45,8,85,404,36,1808,3,61,3560,3756,93,3536,157,69,141,281,2340,29,37,645,149,201,3760,81,249,89,321,16,325,97,329,101,105,245,293,297,17,1792,261,301,305,4,217,57,1812,1816],[63,192,7944,24640,491520,7864328,260046856,805314587,7516194577,25769803858,34360033297,68719509504,413491265553,805316360,567472562240,7697118625792,8796632522760,123145948241928,422229644936768,3940649674245376,13510798888404480,126101064544945920,140754668584960,144115213845659712,25878855744,288230376151744513,137539911680,4035225266226724864]),([v3,v2,v55,v5,v6,v40,v194,v241],[76,1,5,456,9,49,20,3796,388,3528,209,105,449,3532,213,101,453,180,53,45,13,57,3800,61,3804,3544,69,3636,65,77,85,89,184,80,161,468,93,97,25,37,8,3,36,168,3560,3536,109,333,337,0,113,117,341,345,4,121,41,125,133,188,196],[63,485,7716,122916,917537,1179648,31457317,234881168,335546896,604020752,3288989712,64424509456,206254899216,274877915648,549755814400,1100586024960,15397457756288,52845306970112,43520,492581209901056,565153271646720,3377700001548800,13581167626977280,18016601827745792,37154697475301376,72057594038059009,432345564240805888,1729382261219917824]),([v3,v2,v169,v5,v6,v40,v241],[3716,1,5,388,9,21,3728,8,3528,0,13,17,361,29,49,3724,37,229,53,45,57,3732,61,3540,52,16,69,3,404,77,81,85,89,93,97,36,25,101,4,109,113,40,12,121,125,133],[63,2020,6508,122921,933984,15728677,520093712,201328912,1812037648,6510084176,25851592720,103079215360,412467953664,549756338368,7696596074496,137573239040,549756340288,1099526310144,687195357248,9896156299264,52776565080128]),([v3,v2,v5,v267,v6,v40,v241],[3612,1,5,388,9,33,17,49,3620,25,3624,8,3532,4,13,29,389,129,45,53,57,3632,61,3540,317,3,65,69,73,88,16,404,85,89,93,97,105,0,109,113,117,36,37,40,12,125,133],[63,1001,31780,103468,918688,32505893,503317264,3925868560,167809040,13019382800,51688505360,206728856320,68753068800,343597647360,1649349231360,6597069770752,274878172160,26938049560576,274878202880,549770530816,105553122952192]),([v3,v2,v344,v5,v6,v40,v241],[20,1,5,9,21,2036,8,13,4008,0,25,225,29,49,4020,37,41,109,233,365,57,4024,61,2040,16,404,333,69,73,3,77,81,245,253,3540,93,97,105,4,45,40,12,101,373,293,113,117,129,345,121,125,133],[31,1012,3381,61457,991280,7340053,58720266,469763336,3892363272,13019250728,120399593480,137438953729,275423219712,549756010592,3315722092544,13194206676224,17592186242080,105553189668096,426610511740960,598152585461760,3518437215305760]),([v3,v2,v5,v346,v6,v40,v241],[20,1,5,9,33,17,49,4056,25,2976,8,13,4012,4,37,309,41,45,53,365,57,4060,61,317,3,65,69,73,2040,16,404,341,81,177,89,3540,93,97,0,105,373,229,337,113,117,101,109,40,12,181,121,125,129,133],[31,497,15892,53781,983632,15728661,251658632,1879048202,6509580296,25837044232,240591568904,275163120032,1651414946176,7146825712384,26422678651264,35184372092929,70368744375808,422246832144384,562949953634816,1134698153660416,15762598702219776]),([v86,v3,v16,v2,v5,v6,v40,v241],[2760,13,4100,16,412,2040,20,69,249,4008,65,333,0,101,4068,37,2752,3,45,125,2768,4104,61,2776,49,153,5,285,29,41,365,57,9,25,341,4012,136,229,8,113,4108,4016,457,217,93,265,405,129,3556,121],[3,124,396,7680,253968,262161,16252944,16777332,117440772,218106368,352370704,1627389969,2237661200,4294967808,8589935108,120259133444,412853731329,3848296988676,4398046513924,17213473028,8796629893505,52776564424964,17314122240,137975827457,70918506285568,140738025267201,844991872155648,140738032041985]),([v86,v10,v3,v2,v5,v6,v40,v241],[1324,20,4112,2040,404,2812,149,4100,69,16,249,4008,105,25,0,169,4080,37,2800,3,85,201,2820,4116,93,2824,49,5,9,333,4012,136,41,8,217,61,4108,4016,153,17,145,505,73,341,265,373,229,113,129,429,3648,189,193,197,661],[31,96,1937,30720,1015809,1048609,65011713,201326595,268437504,536873088,3221454852,30064771104,240543334404,275079234689,549957150720,1099646074881,2216337342497,1099673108481,4398046522496,9070971126916,21474837792,17626570949764,43980465256448,70385924059168,141287269345280,844442110165024,16897294721024000,18014420011581472]),([v86,v3,v33,v2,v5,v6,v40,v241],[1748,13,4100,16,604,2040,20,69,249,105,4032,25,1740,3,4012,77,341,4,109,125,1756,4120,113,1764,49,157,5,17,169,41,365,57,9,333,4008,68,37,129,8,61,4108,4016,461,217,93,325,229,3692,117,425],[3,124,396,15888,245760,262161,16252944,16777332,117440772,218106896,352403456,1627389969,2237661200,4294983680,60129545220,68719493124,412853731329,3848296988676,8623492356,4398046593284,8796629893505,52776564424964,8858455040,70369281051137,422770817108992,137975922689,563499715608576,70369287864321]),([v86,v67,v3,v2,v5,v6,v40,v241],[1408,20,4112,2040,404,1804,149,4100,69,16,249,285,4044,25,1792,3,4012,101,37,4,85,201,1812,4124,93,1816,49,5,9,4008,68,341,41,8,217,61,4108,4016,157,141,29,505,333,81,325,97,329,373,229,393,3760,261,301,305,129,661],[31,96,1937,63489,983040,1048609,65011713,201326595,268500992,1610627076,2147549312,30064771104,240543334404,275079234689,549890045953,1099713282048,2216337342497,549917294593,4672924431492,8796093351040,21474837792,123179687216260,145135535337472,844442110011424,16892896674328576,18014415689744416,1133896859648,36028818521063456]),([v86,v3,v2,v55,v5,v6,v40,v241],[180,13,76,69,80,9,468,20,168,4128,2040,4008,105,333,0,4012,101,341,4,45,125,188,4132,61,196,1,5,49,209,213,41,365,57,4100,249,4112,217,3804,93,97,25,37,129,8,4108,4016,229,113,117,741,121,745],[3,124,1924,30720,491520,524293,32505860,234881060,201326724,469772288,738361344,3355443205,4508876804,60129542688,17179883552,17180098592,69793218601,979265126432,1099511662592,2199023257600,13195213275137,53188887576576,174080,70369817931777,985162431084544,4399120449537,3518437221695488,4399133884417]),([v350,v3,v2,v5,v6,v40,v241],[2044,21,12,33,2268,13,0,52,69,16,1000,9,404,40,25,101,3,4140,37,4,4144,109,8,2284,45,36,113,61,57,20,1,5,65,29,313,421,41,53,749,169,157,81,85,89,201,161,333,181,125,533,129,205],[127,8064,24592,1016960,66060288,469762053,3758098464,4831838259,60666806304,208860610592,275213451299,4295035152,3848291158016,13195239491584,52776826570753,4295393296,70373059067920,4630511617,145685317287936,844433788764161,3395292191784961]),([v352,v3,v2,v5,v6,v40,v241],[2980,33,12,3124,13,4,88,69,16,876,9,404,105,3,4148,25,0,40,37,4196,45,8,3140,109,36,61,57,113,20,1,5,17,237,409,77,41,233,765,285,153,73,85,253,201,161,293,125,525,341,229,277],[63,4032,127552,393224,33030144,234881029,1879049232,15300870160,17448304667,104430305296,137539616787,1924145406976,17179878536,6597619745792,26388346176513,17179922440,37658286407680,211108447158273,281492166541320,17280532481,1697646028783617]),([v3,v2,v5,v6,v353,v241],[20,1,5,9,13,17,657,4236,25,409,29,4240,37,421,3536,41,45,53,4136,57,133,3,333,249,73,341,81,36,85,89,201,769,101,105,109,773,777,129,61],[31,1009,15441,507984,1589328,31457672,111155208,947978248,3230679048,12887005568,25904087424,34365522176,21609125888,68754624512,412318515200]),([v356,v3,v16,v2,v5,v6,v40,v241],[2776,33,2768,40,4292,3,16,153,69,2268,405,65,0,37,4212,77,2752,4252,45,2760,2764,61,5,412,13,20,285,237,29,313,41,53,749,57,9,25,3124,109,4136,4296,201,12,457,85,249,753,757,265,333,509,513,341,493,3556,497,129,205],[3,124,468,7680,122916,1966116,2097157,62914576,20971920,218106368,830521344,3250978816,12901679109,17179869696,34359738896,68719534128,962073067536,3307124817921,4398046513936,57744,131941395726608,141845589917953,67152384,1970462276323840,8589938177,33777134644674560,8589975557,108087499158716417]),([v10,v356,v3,v2,v5,v6,v40,v241],[2820,40,4340,3,404,1324,13,20,5,2268,9,4292,65,77,4224,169,3124,4264,45,4136,85,4296,2824,57,201,12,149,153,69,16,25,0,2800,2812,2816,93,17,237,409,313,165,217,761,749,793,37,249,753,265,105,109,525,177,341,181,3648,185,433,661],[31,480,1536,6656,122892,4063236,62914560,71303168,939524113,3221225993,4295024649,25770983433,34363932673,402655584,482110079744,1649267499296,6597070946656,8796113993985,17593528224256,35184774793220,211106502412292,281475274506240,562951027204608,1688850935185920,2251869627875840,139611588449714176,144150372468948993,288232575205376000]),([v356,v3,v33,v2,v5,v6,v40,v241],[1764,21,1756,40,4292,3,16,157,69,25,4184,65,1740,3124,425,77,4,4272,109,1748,1752,113,5,604,13,20,17,237,169,313,41,233,749,57,9,2268,37,45,4136,4296,201,12,461,85,249,753,757,325,333,509,3692,513,341,493,497,229,277],[3,124,468,7716,122880,1966116,2097157,62914576,20971920,226495488,822124544,3250978816,12901679109,17179877376,34359742000,68719484944,962073067536,3307124817921,3984,4398046552336,131941395726608,141845589917953,268480000,4222262090009600,8589937157,31525334830981120,8589991937,108087499158716417]),([v67,v356,v3,v2,v5,v6,v40,v241],[1812,40,4340,3,404,1408,13,20,5,3124,9,65,4192,285,2268,4292,77,4280,45,4136,85,4296,1816,57,201,12,149,157,69,16,1792,37,4,1804,1808,93,237,281,29,313,421,217,761,765,25,801,249,753,325,101,245,333,293,3760,297,397,533,661],[31,480,1536,30732,98816,4063236,62914560,71303168,939524113,1073756169,6442451465,25770983433,34363932673,402686304,206158444832,1926292833024,6597070946656,8796113993985,17592588742660,35186788041216,211106502443012,281475274506240,562952100919808,34902897113313280,36046389225988097,562952102347264,72057871084290560,144117387129520128]),([v356,v3,v2,v55,v5,v6,v40,v241],[196,33,188,9,69,468,80,40,168,4456,3,2268,105,65,0,3124,101,77,4,4284,45,180,184,61,76,1,5,13,20,313,209,237,213,41,53,749,57,4292,4340,85,249,3804,753,757,201,25,37,4136,4296,12,109,333,509,513,341,493,497,129,205],[3,124,1924,30720,491520,7865348,8388613,251658256,956301312,3355453440,4966219776,25989480448,103213432837,412316860952,14360,229400,17042431803408,17660905521177,35184372123648,70368744179712,424961245708288,563018672898181,174080,16888498604222464,68719491073,127226689474953216,68719706113,432363225134137345]),([v244,v3,v16,v2,v5,v6,v40,v241],[2776,33,2768,40,4472,48,16,69,153,4460,65,285,0,37,4476,29,2752,428,4480,45,2760,129,2764,57,5,13,20,237,412,313,421,3556,53,61,585,161,17,213,4464,3,229,4468,4484,113,12,457,169,217,249,93,265,333,405,125],[3,124,468,7680,253956,8126468,8388613,117571600,50332048,167775744,1912791040,6764101632,25803358213,34359738880,68719477264,962072723472,7696583753744,26396869001217,35184372091664,70368744227216,422212467425552,1688858450198785,137438989824,2252899327674880,4512404310329345,1239100473344,8804682997761,9007207847297025]),([v10,v244,v3,v2,v5,v6,v40,v241],[2820,40,4492,48,404,1324,13,20,5,1340,4460,161,4472,285,29,4496,169,4464,3,4500,129,4468,217,4484,2824,61,93,12,149,69,153,16,25,17,0,37,2800,85,2812,2816,201,237,409,313,165,3648,761,697,537,249,265,213,209,229,113,177,429,189,197,125],[31,996,3072,13312,507908,16252932,251658240,285212672,3758096401,30064772096,103079313921,962077392897,1099528404993,1610617188,6609954669824,26422638904096,105690559938912,140737572241665,281484640392192,1610731524,562951032934404,1125901098024960,6755408031056896,13510807476765696,18014411478269952,108121575433814016,432345598671257600,576460889830457344]),([v244,v3,v33,v2,v5,v6,v40,v241],[1764,21,1756,40,4472,48,16,69,157,25,4504,17,1740,616,4464,77,169,4,4512,109,1748,229,1752,57,5,13,20,604,237,409,313,3692,233,113,585,161,209,4460,3,29,129,4468,4484,61,12,285,461,217,249,93,325,341,425,125],[3,124,468,15876,245760,8126468,8388613,117448720,50332048,973090304,1107410944,6629883904,25803358213,34359754752,481036340240,549755830288,7696583753744,26396869001217,35184372092304,70368744259856,422212467425552,1688858450198785,68719594496,1170380950528,8804682959361,2252899327754240,4512404310392833,9007207847297025]),([v67,v244,v3,v2,v5,v6,v40,v241],[1812,40,4492,48,404,1408,13,20,5,1420,4464,161,17,4488,285,4460,3,4472,169,4516,129,4468,217,4484,1816,61,93,12,149,69,157,16,25,1792,37,29,4,85,1804,1808,201,237,281,313,421,3760,761,697,541,249,665,325,329,213,209,245,393,261,305,125],[31,996,3072,126980,394240,16252932,251658240,285212672,3758096401,12884926977,120259085312,962077392897,1099528404993,1610744164,6601364759328,26439818675456,105690559938912,140737572241665,1610772484,281510410322944,1688850939904004,6755400632238080,27021632123986944,108121575433728000,432345568606437376,9007233620247552,51657048064,576460889830457344]),([v244,v3,v2,v55,v5,v6,v40,v241],[196,33,188,9,161,468,80,40,168,4524,48,4460,105,209,0,4464,101,213,4,4528,45,180,129,184,57,76,5,96,13,20,313,237,805,809,3804,53,61,585,4472,157,4492,65,153,77,217,93,17,29,4468,4484,12,229,333,605,113,341,569,125],[3,124,1924,30720,491520,16252932,16777221,503316504,2046820864,6710900736,9932341248,51914473472,206426865669,1924145349136,6597069776912,9345848999952,18159126446096,35253091565593,70368744212480,140737488357376,862034300764160,1161152998408193,174080,15762598700525568,18014467228971009,110338190875459584,18014467229155329,144115256800575489]),([v3,v2,v47,v5,v6,v40,v241],[16,153,137,384,9,13,21,285,449,25,412,29,33,2788,37,388,4532,41,45,53,2040,57,4300,61,428,0,1,65,69,73,77,81,85,89,93,97,17,213,3,4,229,8,36,201,40,12,101,105,109,113,117,2092,121,125,129,133],[63,65,936,64544,2065440,31462432,100663323,939524632,3489685521,13153665041,51820625937,68753031816,962072731648,7696581754880,61572663771136,211106232549896,422212465394184,1688850007065096,351843722289152,7318350480826368,63050394797146112]),([v355,v3,v2,v5,v6,v40,v241],[88,13,20,128,21,388,1792,69,0,9,2752,153,4,105,25,285,16,101,4328,45,8,136,109,36,61,40,4324,113,12,5,221,281,29,33,37,229,233,3,201,241,157,289,81,85,249,253,257,93,265,269,273,333,293,297,301,305,277],[63,8128,57664,197632,16515073,520093697,1610680464,2684395600,30064772112,103622639632,962810871824,3298534926400,4415226449088,131941399857152,2111062526724096,17179910208,15771394793308224,54183933218168896,154623804416,21692941312,72057903483453440]),([v238,v3,v16,v2,v5,v6,v40,v241],[2764,33,412,13,3,300,16,36,69,404,316,65,0,2760,37,2752,109,61,2768,4552,113,2776,21,2040,304,153,149,285,213,101,129,45,49,53,3556,57,9,25,4,177,8,320,324,457,77,461,249,93,265,269,273,169,333,513,405,301,305,385,125,133],[31,241,865,7185,24576,106496,4063233,29360168,100663592,138415112,805339146,16106135560,51545374728,68719477760,137438954528,275414810672,1651414933504,6631431077920,8796093025568,52777128591616,70920647483648,2111062326903072,2251800484776960,13510801029606400,126241527056305152,144115190760251392,17592724652032,864691131677941760]),([v3,v16,v2,v5,v248,v6,v40,v241],[568,21,2092,13,572,153,149,69,560,285,65,2768,3,412,2752,417,33,37,421,4612,41,3556,45,49,53,2776,61,317,9,25,40,16,101,4,109,584,588,125,12,457,425,85,249,189,265,0,333,405,77,2760,229,2764,113,121,129,133],[31,233,1802,14346,507912,33030152,234948616,268435712,536871169,3221231617,12885049344,120263802881,412417523712,549755815297,2147485857,1099511775392,6597074485377,26388379730048,35184372090624,4295100160,70385928766720,140875027973120,281475010265088,3940649678669824,4503599660941312,21479702528,9007199355551744,54043333072257024]),([v245,v3,v16,v2,v5,v6,v40,v241],[2768,13,33,3,412,40,1044,1036,16,69,249,776,65,333,0,37,4672,341,2752,2776,129,2760,61,21,2040,1048,153,149,285,428,29,389,2304,41,45,49,53,201,125,161,17,780,136,109,8,12,457,85,265,633,405,101,445],[31,481,1857,30720,491529,1572864,6815744,58720324,201327684,276834308,8061648900,128851116036,412317384710,549755815936,1099511629888,6598143705152,26405461032960,35459250520097,70368744188992,1141048384,140754670323200,844837247517696,1342318592,8813275000832,1126312224235520,2260613088804864,412317548544,4503891687768064]),([v3,v419,v2,v5,v6,v40,v241],[404,13,4716,153,5,9,1324,473,4720,17,281,25,169,145,2828,37,388,4724,217,149,45,201,4344,61,1340,16,1,0,29,3,4,41,8,36,57,40,12,65,69,73,77,81,85,89,93,97,101,105,109,113,117,2040,2092,121,125,133],[3,509,3856,127056,2031696,31981648,234881324,134220544,1879162880,15033630720,120271732736,962072676640,3573412839461,13469018619941,53051448623141,211106232568064,422212466247936,1688987311802624,2603643535802368,14074848359792640,56294995356155904]),([v3,v2,v333,v5,v6,v40,v241],[112,153,141,404,69,13,88,20,33,620,388,1740,17,21,25,2800,169,3,3236,41,136,109,49,233,57,4368,113,0,4,9,65,157,73,245,249,253,257,261,265,269,273,105,37,45,8,36,61,40,12,117,125,229,133],[63,2016,30752,229664,16515104,117579808,939558930,7516211216,100378,128851378201,2061684965401,2199157491712,4398046543880,61572654563392,492581309907008,2199023339520,10995118655488,633319872022528,8796095479808,70368845070336,7881299451969536]),([v238,v10,v3,v2,v5,v6,v40,v241],[912,404,2816,3,36,5,1324,149,280,300,69,16,316,105,25,0,2812,37,2800,85,189,2820,4760,93,2824,13,304,2040,9,65,101,169,4,45,8,177,113,320,324,153,17,21,145,129,3648,57,829,73,461,249,265,269,273,337,185,201],[31,484,3591,61440,196608,851968,32505860,234881153,268439552,536875520,7516454912,60129607680,481048920065,549789369985,3298534903936,4401267998848,8830452826272,123145348448384,140737488377344,282027954013184,562992903160832,7881368079959553,3221254144,9007233614573568,1168243707904,18014435017031680,3235119104,36037627484372992]),([v10,v3,v2,v5,v248,v6,v40,v241],[576,13,572,149,2092,560,9,568,65,2820,40,3,404,2800,37,4,4784,45,584,85,588,2824,61,189,12,153,69,17,21,25,5,280,1324,417,145,217,3648,73,16,425,249,265,0,101,105,109,125,169,2812,2816,93,177,181,185,193],[31,96,416,7681,59393,2031617,31457280,100663435,939524136,7516193288,25769828360,104153546760,1084228104,138042933408,274978574848,549856501760,1099579457665,2199105044480,4398717599776,26388815953952,52777095594016,70369425752064,140737490452480,844459290460672,1125899908947968,15771394789433344,18014398519992320,70403114926080]),([v245,v10,v3,v2,v5,v6,v40,v241],[2820,40,768,1036,404,5,149,280,1324,69,249,16,776,25,17,0,169,4812,341,2800,3,2824,217,2812,93,33,1048,2040,161,1044,333,780,136,45,8,85,125,201,12,153,21,1340,29,349,517,833,2304,41,761,837,265,633,105,577,109,177,181,37,433,841],[31,481,3601,61440,2031617,6291456,27262976,234881092,268439552,1610616832,6442909700,60137930752,481038434304,550326240324,1099511656512,138538465493056,422246833193056,206160527456,562950490313728,4948339590148,42958063104,3377905881056256,13515196928905216,22518032504995840,206160551936,108086425425346560,432345770388357120,576460924112601088]),([v3,v2,v147,v5,v6,v40,v241],[16,157,221,392,9,13,33,604,17,21,1776,25,388,169,453,37,4828,41,45,2040,57,4380,61,616,4,1,65,69,73,77,81,85,89,93,97,209,3,0,29,129,8,36,201,40,12,101,105,109,2092,113,117,121,125,229,133],[63,65,8096,57384,987296,15729312,50331675,469765137,1744863256,6576996369,25910312977,240518175744,274894725128,3848291028992,30786331873280,105553116302344,211106233388032,1970324910377984,175921860804616,2814750310301704,31525197398736896]),([v163,v3,v2,v5,v6,v40,v241],[52,13,20,60,33,388,2800,69,4,9,1740,157,0,16,105,101,37,169,4408,109,8,68,45,36,113,40,4404,61,12,5,137,17,21,25,165,129,53,3,201,317,73,153,173,85,249,89,321,93,325,97,329,341,181,185,193,197,205],[63,8128,25600,234560,16515073,520093697,1610623120,15032386576,17716904016,103622639632,962810871824,1108101573760,6597069933632,131941399799808,2111062526666752,8590099520,146033869824,10955523072,15771394793406528,54183933218291776,72057903483453440]),([v87,v3,v33,v2,v5,v6,v40,v241],[1752,21,604,13,3,208,16,36,69,404,1748,25,224,77,4,1740,45,113,1756,4856,61,1764,33,2040,212,157,149,209,105,169,229,109,49,233,3692,57,9,0,37,245,8,228,232,65,457,461,249,93,325,97,329,285,357,341,497,425,193,197,125,133],[31,241,865,3072,28689,99328,4063233,29360168,100663592,402685962,541077512,16106128392,51545374728,68719480832,137707421744,274877911072,1651414926336,6631431077920,26388581089536,35184372101408,70920647476480,2111062326903072,2251800619032576,4503602043323392,8796363194368,27021599911719936,252342316622688256,864691131677934592]),([v3,v33,v2,v251,v5,v6,v40,v241],[688,33,2092,13,692,157,149,69,1756,3,604,1740,401,21,25,409,680,169,77,4912,41,3692,109,49,233,1764,113,241,9,40,16,105,0,37,45,700,704,125,12,405,461,85,249,261,325,65,4,1748,129,1752,61,117,341,425,229,133],[31,233,1802,63496,458762,33030152,234889480,268500992,1610613505,6442469376,8590000129,120263802881,412417523712,1073742241,549755832480,1099511955585,6597074485377,26388379730048,35184405643264,70368744636416,985162423206144,1125899940399104,2147895296,19332089856,2251799914366976,4503616812285952,9007336794619904,54043333072257024]),([v245,v3,v33,v2,v5,v6,v40,v241],[1756,13,21,3,604,40,1044,1036,16,69,249,25,4972,333,1740,780,77,341,4,1764,229,1748,113,33,2040,1048,157,149,616,17,361,2304,169,41,109,49,233,201,125,161,776,68,29,45,8,12,461,85,325,633,105,425,849],[31,481,1857,30729,491520,1572864,6815744,58720324,201327684,4034932740,4303519748,128851116036,412317384710,549755846656,3299071766592,4398046543936,26405461032960,35459250520097,603993152,70368744342592,140754670323200,844837247517696,4832014336,1134713181839360,412317394944,8813275185152,2252212131201024,4503891687768064]),([v3,v230,v2,v5,v6,v40,v241],[404,13,4996,157,5,9,1408,473,5000,285,141,1820,25,388,29,165,37,5004,217,149,45,201,4420,61,1420,16,1,4,17,3,0,41,8,36,57,40,12,65,69,73,77,81,85,89,93,97,101,105,109,2040,2092,113,117,121,125,133],[3,509,15952,114960,1974352,31981648,234881324,1879062528,134299904,15033573376,120271675392,962072680485,3573412856096,13469018619941,53051448623141,211106232604928,985162419673088,7881436799440896,351843722133760,11260098592702720,54606145495891968]),([v3,v314,v2,v5,v6,v40,v241],[52,20,21,432,388,13,152,157,145,404,69,1792,285,3,2752,29,33,37,2388,41,68,45,53,57,4444,61,0,4,9,25,101,109,8,36,113,40,12,77,153,81,177,249,89,321,189,325,97,329,121,125,129,133],[63,2016,14372,245792,8126752,58794016,469781632,536873472,1141000192,15035793409,120309415937,7808,962072824832,16492676777536,263882840999488,1073895424,2149849088,17230215168,3223732224,281629646012416,3940649727688704]),([v87,v67,v3,v2,v5,v6,v40,v241],[788,404,1808,3,36,5,1408,149,280,208,69,16,1804,25,224,101,37,4,1792,85,261,1812,5048,93,1816,13,212,2040,9,105,285,0,77,109,8,245,61,228,232,157,141,29,33,229,3760,57,829,457,81,249,325,97,329,297,345,201],[31,484,3591,12288,245760,790528,32505860,234881153,268451840,3758358528,4294984192,60129546240,481048920065,549789369985,1101122502784,6597069848704,8830452764832,123145348448384,141288855045120,281474976794112,562992903099392,7881368079959553,1610973184,9007234688487424,1624506368,18014432869339136,2267755397120,36037627484311552]),([v67,v3,v2,v251,v5,v6,v40,v241],[548,33,692,149,2092,680,9,1812,40,3,404,1792,25,0,688,77,5072,45,700,85,704,1816,113,261,12,157,69,137,5,280,1408,401,141,29,37,217,3760,16,405,81,249,89,321,325,285,4,1804,1808,93,101,105,245,293,297,301,125],[31,96,1921,14849,49184,2031617,31457280,234897419,1879048328,6442457096,25769803818,103348240392,278921352,137539617920,274978576384,567002808352,7696649240577,8796174811136,17592188141568,35210141892640,211140592861312,281474978809856,1688867040139264,16888498603235328,18014398519973888,562967134011424,36028822799253504,36028831389712384]),([v245,v67,v3,v2,v5,v6,v40,v241],[1812,40,768,1036,404,5,149,280,1408,69,249,16,285,5100,333,1792,3,780,37,29,4,1816,217,1804,93,33,1048,2040,161,776,68,1044,341,45,8,85,125,201,12,157,137,845,1420,17,377,501,817,2304,41,761,853,89,325,633,101,577,245,293,25,397,841],[31,481,3601,126977,1966080,6291456,27262976,234881092,268566528,1610641412,6442582016,60137930752,481038434304,3850471736388,277076930224192,34472000,844459298259040,206160527456,9347996345348,1125902054982656,2251842771748352,13511005042639872,54051991622148096,216172816481931264,864691334615678976,18014441468067840,206161313792,1152921676416024576]),([v379,v3,v2,v5,v6,v40,v241],[404,13,1312,9,1,8,5116,16,388,25,1872,17,0,3,37,2860,29,4,45,41,3540,61,40,5120,57,12,149,1844,377,349,285,153,289,169,157,173,85,201,213,209,229,521,113,401,525,129,529,417,533,205],[3,252,16128,254208,786468,66060288,201326685,469765888,738312448,67895300,229638144,7516195921,60129640529,68720001052,154643988561,824633830400,3848291223556,30786351795200,105827994763268,422212493475840,598271790153732]),([v3,v2,v55,v5,v6,v40,v235,v241],[80,1,5,468,69,13,5164,1844,33,2040,1840,209,21,105,1852,213,101,180,41,45,49,53,76,149,3,3804,57,5168,61,16,404,65,457,77,461,89,9,93,25,37,8,168,1856,1864,109,333,337,0,113,117,341,345,4,121,85,125,129,133,188,196],[63,992,15392,114976,4063264,29360168,503316768,1610612763,6442460178,25769885714,34360393745,68719607808,137841606683,274877924352,549755814912,1099512545280,2200113774664,13332014694400,91136,123145302974464,175921860453376,844427480278016,3395291907293184,5629499534295040,9288683224121344,18014398509613057,252201579536056320,864691266296741896]),([v3,v2,v231,v5,v6,v40,v241],[2880,1,5,404,69,13,52,20,21,432,388,1840,3,333,29,33,1904,37,2884,41,45,49,53,3540,57,2892,61,8,0,9,77,245,249,89,93,25,101,4,109,113,40,12,121,125,129,133],[63,2016,14624,249888,8126496,125861920,939788306,272410,1073938459,15033696272,17280532507,34359740424,206158631488,275013435392,3848399749120,68719683584,274879225856,549864876032,343598825472,4948985315328,61572753129472]),([v3,v2,v5,v306,v6,v40,v241],[1924,1,5,404,69,13,3,17,21,1920,25,88,20,33,620,388,1852,341,1932,41,45,49,53,3540,57,1944,61,65,8,4,9,177,249,89,321,93,97,329,105,0,109,113,117,37,40,12,125,129,133],[63,2016,63520,204896,8126496,125837344,134219291,1879375890,458778,32213565456,240618831899,824633740864,274878105088,1374390846464,6597313037824,8796093087752,1099781373952,54975690440704,1099513069568,2199132504064,492581311217664]),([v3,v385,v2,v5,v6,v40,v241],[16,49,1,137,5220,9,13,1948,17,21,1976,25,388,29,33,2920,37,217,45,365,57,5224,61,3540,8,209,3,0,213,4,41,201,40,12,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,133],[3,125,8128,127168,917584,15745216,16777269,234888192,872517632,1090912272,15047065600,120259087393,446676697121,1683627442224,6631435796513,26388346276864,52776558397456,211123427085312,43980465438736,351981174620160,1688849866948624]),([v3,v2,v327,v5,v6,v40,v241],[16,1,5,69,13,52,20,60,388,1952,17,21,25,3,29,33,2936,37,2812,229,109,49,233,3540,57,2952,61,8,9,0,73,77,85,249,253,369,93,105,169,4,45,40,12,101,373,113,117,177,345,121,125,133],[31,500,7696,253968,8126480,125861904,939786762,1074008587,2147680267,64425820168,68820140043,137438953985,824633925792,1103942123520,6665898295296,26388279210496,4296282112,105553216935424,431008559529984,598136582242304,3377699823026176]),([v3,v2,v5,v308,v6,v40,v241],[16,1,5,69,13,3,17,21,1992,25,88,20,128,388,1964,29,33,37,1804,129,45,49,53,3540,57,2008,61,65,8,9,4,81,85,249,89,369,93,97,329,0,285,105,373,245,337,113,117,101,109,40,12,121,125,133],[31,1008,15380,245776,8126480,125894672,134218507,1879326730,2147893259,64425820168,481137000459,1649267447584,6597069914912,28587303633408,105553359536896,140737488371713,281479541424128,1688918688792576,4296409088,2286984286617600,13510798984609792]),([v236,v3,v2,v55,v5,v6,v40,v241],[80,49,13,3,76,180,9,16,168,5288,1952,105,0,1964,101,4,45,125,188,5324,61,196,1,5,69,1948,33,2040,209,21,213,217,85,3804,57,65,457,77,461,369,93,25,37,177,8,1968,1972,245,333,113,117,741,341,121,745],[31,96,905,7177,57353,65569,4063233,29360133,234881540,805309444,1140875268,6442450982,25838485508,20971649,103100189696,412337856512,554067558433,1099534172161,2199023264768,4398046512128,26392574033952,105578887643136,27648,422216760035360,3940684035263488,4512400015376416,27584685158195200,6444154912]),([v3,v2,v391,v5,v6,v40,v241],[16,1,137,400,9,33,40,13,2480,17,21,5328,25,48,29,5332,37,5336,129,808,45,49,201,61,12,65,69,73,77,81,85,89,93,97,388,401,3,0,417,4,41,8,36,57,101,105,109,113,117,121,125,133],[63,192,16160,124192,4063520,12582952,16777243,234887185,872513553,3289514001,12960399384,257698043904,910533165056,7696583098368,8796122382344,52845277714432,105553117976576,422212507013128,87960932024320,703687718666248,3377699730227208]),([v318,v3,v2,v5,v6,v40,v241],[1340,33,20,1000,13,388,52,2824,69,12,2192,9,0,40,25,101,3,3344,37,4,3348,109,8,3648,45,36,113,61,93,16,1,5,17,21,169,145,421,41,53,201,149,325,81,85,89,97,209,181,189,193,217],[127,8064,25600,1015880,66060288,469762688,3758098448,12884968464,120259543057,414490558480,1649535877264,4831841664,6614786902016,26389907507200,35184707635584,70373039440896,70373059068928,4630511744,149550787854336,844442378698880,1126449947869312]),([v319,v3,v2,v5,v6,v40,v241],[1420,33,20,876,13,388,88,1816,69,12,2196,9,4,105,3,2532,25,0,40,37,2540,45,8,3760,109,36,61,93,113,16,1,5,285,141,409,29,41,233,201,149,265,73,85,253,269,213,293,261,301,217],[127,8064,254024,787456,66060288,469762688,3758098448,30064885777,34359755794,208332128272,824767938704,3303366821888,34896612736,13195767973888,17592387373440,35218731934720,74771111968768,422216894316672,35218751751168,34561065088,563224982323328]),([v3,v255,v2,v55,v5,v6,v40,v241],[188,13,3,33,76,80,1,5,9,5400,2480,2092,2192,209,21,105,361,2196,213,101,389,5404,129,3804,45,49,657,196,201,93,69,40,168,0,4,180,184,61,16,325,65,265,857,77,861,85,89,97,25,37,2212,2216,189,12,109,333,337,261,341,345],[31,488,3594,126984,1982472,132120584,939524106,1207959552,6442451461,8589979648,17180786688,103102283777,137573171201,824633721120,7696581431552,26938035536128,105553135141216,140738159444225,281474976845824,562949953425408,3412884119879680,13510799553200128,692224,126100789585285120,144116288258605056,882705526984146944,4512396392005632,960495616]),([v3,v397,v2,v5,v6,v40,v241],[40,13,5408,1,149,404,9,2552,489,5412,285,141,5416,25,48,169,145,5420,37,5424,217,5428,45,57,749,61,16,12,388,17,3,0,29,4,41,8,36,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,133],[3,1020,31888,508048,7930000,58720784,201327180,4026544128,14227472384,120265900032,176161280,962072686692,3573413183588,13469022158948,53051469595200,211107306680320,422212471894016,1688987332780544,351843728097280,2815849312551424,13510798920909312]),([v3,v338,v2,v5,v6,v40,v241],[428,20,21,1000,388,13,52,3412,1,5,404,9,2232,285,65,29,33,3408,37,3,3420,41,3556,45,53,2776,57,61,69,12,0,40,25,101,4,109,8,36,113,77,81,85,89,261,653,333,181,121,125,129,133],[127,4000,28708,1015841,32506400,234946592,1912608768,6442455040,25770721352,240531800064,275582550016,302013440,1649536273536,6597347642496,26388715276288,8590225408,35218741284864,275045695488,72576371392512,141562290110464,1970325013135360]),([v3,v321,v2,v5,v6,v40,v241],[616,20,33,876,388,13,88,2588,1,5,404,9,17,21,2584,25,3,2236,169,77,2596,41,3692,109,233,1764,57,113,69,12,4,105,0,40,37,45,8,36,61,65,73,85,253,189,653,293,117,341,125,229,133],[127,4000,127009,917540,32506400,234889248,1912735744,6442565704,25769934848,240531800064,275582550016,1649535929472,302648320,6597347642496,26388715276288,2148450304,37385556508672,71193545703424,140771858186240,275046203392,1970325013135360]),([v254,v3,v2,v55,v5,v6,v40,v241],[188,13,149,3,76,196,69,40,168,5532,2232,105,65,0,2236,101,77,4,5536,45,180,217,184,93,80,1,468,9,2552,145,2092,209,141,213,3804,693,57,61,16,325,404,265,857,861,89,653,285,169,2244,2248,12,109,333,509,513,113,341,493,497,125],[31,96,905,15360,245760,8126465,8388641,251658246,1879048708,6442456068,9126887428,52079362052,206158430246,1924363452416,6597203991552,9345983168512,17592440586240,35321945260065,70368744195072,140737488356352,844442112884736,1126106065272864,87040,33776997207643136,36028934457923616,504403158268461056,36028934458015776,576460889744998432]),([v245,v3,v2,v55,v5,v6,v40,v241],[188,13,33,3,76,9,249,468,80,40,168,772,1036,776,105,333,0,780,101,341,4,196,129,180,61,96,161,149,137,1048,2040,209,21,361,437,213,389,441,41,45,49,53,201,125,1044,768,85,69,89,17,29,8,12,109,445],[31,481,7681,122880,1966080,6291456,27262976,503316556,1744832516,32212295684,244813791236,4123176992772,13194141630470,52776625244224,67166272,68026432,493130973446208,13194141630560,562949953560576,1125899906850816,2322718322065408,4516793769000960,696320,9007749018992640,13194141679616,9007749019729920,13194142416896,18023744368803840]),([v3,v370,v2,v5,v6,v40,v241],[36,21,212,161,149,388,9,13,4868,209,361,4872,25,29,33,2960,37,229,45,365,57,4880,61,3540,1,16,404,8,0,17,213,3,4,41,201,40,12,65,69,73,77,81,280,85,89,93,97,101,105,109,113,117,121,125,133],[3,252,8064,123044,919680,15745156,117440608,939531008,7516291104,8724547584,120273764352,962072678720,7973606883392,26663157237824,105828008853568,422212465135872,844424930400256,3377837165777152,703687442106368,5630599060619264,27021597770909696]),([v3,v2,v5,v278,v6,v40,v241],[3,1,5,796,9,13,272,209,21,105,88,20,388,224,29,33,37,284,129,45,49,53,3540,57,296,61,65,69,16,404,81,177,89,93,97,8,25,0,285,373,109,333,357,113,117,36,101,40,12,125,133],[63,992,7457,122912,4063264,62947360,201327184,805307418,1208033297,6577324048,25958547472,515396207168,824633918016,7696582050304,26388396507712,105553116274688,1133872021504,431008612614144,1099512348672,8796143443968,1688849911513088]),([v3,v2,v5,v372,v6,v40,v241],[692,161,149,48,9,33,4932,401,361,4944,25,40,13,29,4928,37,4936,129,5624,45,145,749,61,65,69,73,388,16,1,404,3,77,81,280,85,89,93,97,12,0,17,101,105,109,113,117,213,4,41,8,36,57,121,125,133],[63,2016,6144,57389,2031649,6294048,58721360,1006632976,16122953744,51557236752,206179402256,1924145350336,6597069800512,13194140124224,52776570717696,211107373432832,1970324837826560,2252624451600960,10995117178880,4521193965126144,27021597769073152]),([v263,v3,v2,v5,v6,v40,v241],[120,33,20,876,13,388,88,69,16,9,404,908,105,12,896,25,0,680,40,37,900,45,8,3912,109,36,61,113,1,5,3,209,21,409,29,41,233,241,65,153,73,169,85,253,261,269,293,301,125,229,277],[127,1992,129024,917504,66060288,201336832,1879048721,15032434704,18253742098,103642300432,141868402704,1924145398272,2216203256448,13194434183680,53326448167424,17179924480,74766808567808,141012567623680,2216223178752,17381197824,1970324987971584]),([v3,v361,v2,v5,v6,v40,v241],[36,33,304,161,149,388,9,13,17,21,2016,25,4564,213,389,4568,37,129,45,365,57,4576,61,3540,1,16,404,209,3,0,8,4,29,41,201,40,12,65,69,73,280,77,81,85,89,93,97,101,105,109,113,117,121,125,133],[3,252,4004,127104,950400,15729284,117440608,939527200,7516303360,9664102400,120273764352,2061852740672,6871947743296,26663157268544,105828008853568,422212465138688,844424930428928,3377837174164480,703687442137088,5631698563829760,27021597770940416]),([v3,v2,v133,v5,v6,v40,v241],[3,1,5,920,9,33,137,328,20,13,388,316,17,21,25,364,213,101,368,129,45,49,53,3540,57,380,61,317,16,404,69,73,77,177,89,321,189,97,329,36,105,8,37,169,0,109,113,40,12,373,341,385,121,125,133],[127,1953,30752,229920,8126496,260047392,805306522,3221243921,5368872976,61204594704,482219130896,1649267443712,32985349228544,37383396655104,492581318295552,571746046887936,35184373415936,70368844863488,3412884094058496,4573972767342592,27021597866721280]),([v3,v2,v5,v6,v363,v40,v241],[572,161,149,48,9,21,17,4628,25,4632,417,389,4644,37,40,13,4636,41,5592,45,141,765,61,3,65,69,73,280,77,81,388,16,1,404,85,89,93,97,101,105,209,0,109,113,117,12,4,29,121,8,36,57,125,129,133],[63,493,15904,49152,2031649,6311968,260047248,838869520,16106127376,51574013968,206196183056,824633729920,3299617014144,4947803177344,26388300042496,246290604635648,4672925016576,290271342374912,1688849861246976,2357352934150656,31525197396316160]),([v265,v3,v2,v5,v6,v40,v241],[992,21,20,1000,13,388,580,69,16,9,404,560,40,25,1032,101,12,37,0,1024,109,8,3996,45,36,113,61,1,5,3,17,1020,213,33,421,41,53,317,285,77,157,81,85,89,189,97,181,193,125,129,205],[127,1992,14336,509952,33030144,100745216,939524625,1610614802,32212385808,103360757776,146096017424,275951651456,3850438312448,13194286858752,53876136886784,3221407744,275961612288,1174421504,74768947249152,141287344979968,1970324912488448]),([v3,v365,v2,v5,v6,v40,v241],[40,13,1048,161,149,48,9,33,17,21,4688,25,29,4692,37,4696,41,45,821,4700,201,61,388,1,16,404,209,3,0,213,4,8,12,57,65,69,73,280,77,81,85,89,93,97,101,105,109,113,117,121,125,133],[3,252,4004,29348,1015936,3670144,62914624,473959424,1749049344,6443204608,12888571904,257832258624,996566655040,3332894785600,13228501893184,52776692378624,105553116432384,422229647558656,87960930402304,703962322321408,3377699723280384]),([v3,v2,v287,v5,v6,v40,v241],[1060,1,5,3,9,13,20,33,1036,388,776,17,21,333,29,1068,37,421,1076,41,45,49,53,1084,201,113,16,69,404,77,81,85,89,261,269,40,25,101,4,109,12,8,61,465,125,121,229,133,445],[63,993,15392,245929,8126496,58720416,469762320,134229008,1744928792,6577979408,25945964560,103079216128,412316958984,3848300396544,5497616859136,137439030272,549765521408,8796151750656,687196143616,52777137012736,510173438279680]),([v3,v2,v5,v288,v6,v40,v241],[1100,1,5,3,9,13,17,21,1104,25,409,20,33,1036,388,780,29,341,1116,41,45,49,53,1124,201,61,317,65,69,73,16,404,85,89,189,97,105,0,109,125,117,40,37,12,8,113,469,129,133],[63,2025,30753,233504,8126496,125833248,939524888,3489669136,268664848,13154648080,51849986064,206158439176,68719706880,343598694912,1649443602944,6597069799424,26663166672896,43980523831296,274887737344,70368803028992,422762263871488])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x2 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x3 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x4 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x5 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x6 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x7 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (7*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x8 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (8*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x9 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (9*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x10 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (10*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x11 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (11*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x12 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (12*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x13 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (13*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x14 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (14*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x15 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (15*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x16 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (16*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x17 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (17*8)).take 8) = true := by decide +kernel
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := levelStep ptopB ptopW ptopI8 (chunks 8 ptopD9 18 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  · exact ptopC9x2
  · exact ptopC9x3
  · exact ptopC9x4
  · exact ptopC9x5
  · exact ptopC9x6
  · exact ptopC9x7
  · exact ptopC9x8
  · exact ptopC9x9
  · exact ptopC9x10
  · exact ptopC9x11
  · exact ptopC9x12
  · exact ptopC9x13
  · exact ptopC9x14
  · exact ptopC9x15
  · exact ptopC9x16
  · exact ptopC9x17
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD10 : List StD := [([v7,v3,v2,v5,v6,v40,v241],[16,20,13,9,65,24,25,0,3,77,28,37,4,32,85,8,45,36,93,40,44,61,12,137,1,5,17,141,29,145,41,149,57,153,157,161,101,105,109,48,113,117,121,125,129,133],[7,9,497,7937,253953,8126465,58720259,234881122,838863874,3254853634,6479151106,8606711921,17196649985,34376605697,34379923457,206158433632,412316934496,3848293843056,343597460736,6047317102080,62122410188800]),([v3,v2,v22,v5,v6,v40,v241],[16,20,137,13,9,5,17,21,384,25,388,29,33,392,37,396,41,45,49,53,57,400,61,48,1,65,69,73,404,77,81,85,89,93,97,285,3,0,169,4,217,8,36,201,40,12,101,105,109,113,117,121,125,129,133],[31,33,1994,31754,1016842,15732746,16777218,503317265,1946181649,6778159121,26111639569,240786604800,893621657600,7696849993728,61572925882368,211174952035072,422281184707328,1688918619587328,351912440553472,2814819029770240,31525266117525504]),([v19,v3,v2,v5,v6,v40,v241],[16,5,20,404,9,25,1132,65,0,3,37,1136,77,4,1140,45,8,85,36,61,40,1144,93,12,1,13,473,17,21,29,33,41,49,57,153,157,161,245,333,293,297,48,261,405,301,305,177,341,181,185,189,425,193,197,125,129,133],[3,28,996,15876,507908,16252932,117440517,436207812,1644173316,6476152836,9703522308,17196646633,34376522761,68736434185,68743069705,7904,2061584450240,68169727213760,1055531162819072,16890697632192512,126102988596068352]),([v20,v3,v2,v5,v6,v40,v241],[16,404,13,1,25,1304,17,0,3,37,1308,29,4,1312,45,8,41,36,61,40,1316,57,12,5,9,20,473,141,388,145,149,48,65,69,73,77,81,85,93,213,209,229,521,113,401,525,129,529,417,533,125,205],[7,9,497,7937,253953,8126465,125829121,444596336,847252992,1384210432,3266576384,30081548385,111685929985,146045739009,283487764481,1649267445088,7696581468512,61572654301536,211655988423936,844424933543168,3448068467925248]),([v14,v3,v2,v5,v6,v40,v241],[0,13,20,69,16,9,404,25,101,1684,37,4,3,1688,109,8,45,36,113,40,1692,61,12,1,141,21,449,17,29,49,41,57,237,285,77,81,85,89,48,93,97,209,401,181,193,125,129,133],[3,124,133,7940,253956,8126468,58720292,234881029,838862340,1644240900,6479151108,8724152361,51539613224,206158508072,1924148494376,2199157474561,2199157563393,4398184136705,8864812578560,18434002781696,246565485748224]),([v31,v3,v2,v5,v6,v40,v241],[0,13,388,9,16,3,1,404,20,17,37,2032,29,4,2036,45,8,2040,41,36,61,40,2044,57,12,141,21,25,225,49,237,48,65,69,73,169,157,173,217,161,201,101,105,109,113,129,529,533,205],[3,252,769,15396,1032196,32505892,100663628,469762305,603987204,604291332,3301966080,30198988865,240518174816,824633999456,1649280024672,6597203988481,13194274029569,17596627812353,105587476289568,140737501994016,317758873288736]),([v139,v3,v2,v5,v6,v40,v241],[4,13,20,69,16,9,404,105,2124,25,0,3,37,2712,45,8,109,36,61,40,2716,113,12,1,145,33,17,49,453,29,41,57,313,65,73,169,85,253,48,93,269,213,293,301,417,125,129,133],[3,124,3972,4101,253956,8126468,58720292,234881796,838860805,1241587716,6479151108,25769806632,34896609321,206158506024,1924148494376,2199560127361,4466766064512,9629319824128,2199560216577,17592726323201,246565485748224]),([v34,v3,v2,v5,v6,v40,v241],[4,13,388,9,16,3,1,404,25,1696,17,0,20,29,2976,45,8,2040,41,36,61,40,2980,57,12,145,33,49,37,309,53,313,48,317,285,153,289,77,69,81,217,161,201,101,105,229,521,113,525,277],[3,252,3876,12289,1032196,32505892,100667468,201332484,872419329,1275383812,15113129984,120259085920,962341109825,3298535161952,6597082349664,26388547503617,105570296415776,422212477650720,8796361768961,137721020417,602532384882720]),([v3,v2,v5,v6,v40,v194,v241],[20,1,5,388,9,49,17,3528,25,29,3532,37,8,53,45,13,57,3536,61,3540,3,65,69,73,77,81,85,89,36,16,161,404,93,97,101,105,109,0,113,117,4,121,41,125,133,40,12],[63,493,3629,28705,36864,983077,15729040,55577616,205541392,4026531856,12890013712,51540659584,103079235840,137708437952,824636735872,85899368448,1099781115392,2473918860288,4398046515201,26388279480320,105553385160704]),([v86,v3,v2,v5,v6,v40,v241],[8,13,20,69,16,9,404,105,4008,25,0,3,101,4012,37,4,45,125,40,4016,61,12,1,5,49,17,29,41,365,57,333,249,73,341,81,217,3540,93,97,373,229,113,117,129,121],[3,124,3972,63492,65541,4063236,29360164,58721028,92299268,419430405,563609604,7516195616,27917314080,34493956137,483185393696,559419517696,1099645846145,6666864558848,8796227260417,19868520308736,8796228943873]),([v356,v3,v2,v5,v6,v40,v241],[12,33,40,9,69,404,16,25,2268,65,0,3,37,3124,77,4,4136,45,8,36,61,20,1,5,13,17,237,29,313,41,53,749,57,85,249,3540,753,757,201,109,333,509,513,341,493,497,129,205],[3,124,3972,63492,985092,1048581,31457296,119538432,421552128,1638072320,6459228165,2968,30744,266288168976,279172874265,31616,8280697144064,4294967941,62156766928896,4294987781,211385405538305]),([v244,v3,v2,v5,v6,v40,v241],[12,33,40,9,161,404,16,25,4460,17,0,48,37,4464,29,4,4468,45,8,129,36,57,20,5,13,237,409,313,421,3540,53,61,585,3,285,153,169,157,217,93,213,209,229,113,125],[3,124,3972,63492,2031620,2097157,29362200,121637760,423655424,1640693760,6459228165,60129542928,214748389392,412854321168,551903297561,3307124843264,6597607228160,8798240506497,5498095624192,8798240526337,17594334183425]),([v3,v16,v2,v5,v6,v40,v241],[16,21,3,13,20,153,5,69,0,285,65,29,33,2752,37,2760,41,45,49,53,57,2776,61,9,25,101,4,109,8,36,113,40,12,457,77,85,249,93,265,333,405,121,125,129,133],[31,233,1802,30732,1015820,7344140,8388864,16777473,100687877,939687937,7522484225,8589936001,17179893921,103079379073,412323152001,33572608,549890196736,1100591662336,167960580,2217283182596,30786332033028]),([v10,v3,v2,v5,v6,v40,v241],[404,13,20,5,3,0,9,16,65,37,2800,169,4,2812,45,8,85,36,61,40,2824,93,12,153,69,17,21,25,145,165,217,149,201,73,249,265,101,105,109,113,177,181,185,189,193,197],[31,96,416,7697,253953,8126465,25165963,234881064,805309976,3221299224,6445596696,8740929696,25169537,17196736641,34379923585,206292650016,412451151904,549926731808,7696581471760,61572654304784,5371928592]),([v3,v33,v2,v5,v6,v40,v241],[16,33,3,13,20,157,5,69,17,21,1740,25,4,169,77,1748,41,109,49,233,57,1764,113,9,105,0,37,45,8,36,61,40,12,65,461,85,249,93,325,117,341,425,125,229,133],[31,233,3852,28682,1015820,7340556,8392704,50334725,67112961,939687937,7522484225,8589937825,17179889793,103079379073,412323152001,16808960,151161860,559425784836,1099646029824,2200103309312,30786332033028]),([v67,v3,v2,v5,v6,v40,v241],[404,13,20,5,3,4,9,25,1792,285,0,16,77,1804,45,8,85,36,61,40,1816,93,12,157,69,141,281,29,33,37,217,149,201,81,249,89,321,325,97,329,101,105,245,293,297,261,301,305],[31,96,1937,6176,253953,8126465,25167883,100664216,939524136,3221299224,6445596696,25168769,9143584800,120275953665,962092861441,3299071755040,30786325652368,246290607768464,1100048588832,674496544,5371928592]),([v3,v2,v5,v6,v40,v235,v241],[16,1,5,404,69,13,3,17,21,1840,25,29,33,1852,37,8,41,45,49,53,20,149,3540,57,1864,61,65,77,89,9,93,101,105,109,333,0,113,117,341,4,121,85,125,129,133,40,12],[63,2016,30816,1015840,3145832,62918688,67110427,134242331,268599313,536903680,1124073499,6442477120,12885066752,51539609160,206280066560,10737598464,824633745480,1168419872768,2199023288321,30786376073216,105554240339976]),([v236,v3,v2,v5,v6,v40,v241],[16,49,13,3,20,8,9,105,1952,25,0,101,1964,37,4,45,125,40,1972,61,12,1,5,69,17,21,29,33,217,85,3540,57,65,77,369,93,373,245,113,117,177,121],[31,96,1929,30729,32801,2031617,14680069,50332428,201338892,805306406,3356229636,4305453825,8600432641,17725128737,34371010561,68719491976,137975825056,825725027072,1100048508960,2475042811904,806158368]),([v3,v255,v2,v5,v6,v40,v241],[40,13,3,33,20,16,1,5,9,48,17,21,2192,25,361,29,2196,37,389,2212,129,3540,45,49,657,12,201,93,69,0,4,8,36,61,65,265,73,77,325,81,85,89,97,101,105,109,261,301,189,193],[31,488,32268,494092,33030152,234881034,301989888,536884229,1073971205,6448218113,8623489025,120259096864,962072871200,3298539602272,4398214283521,26388279275524,52776564961280,211123580182528,43980472123392,844562536988672,240123904]),([v254,v3,v2,v5,v6,v40,v241],[40,13,149,3,20,12,69,25,2232,65,0,37,2236,77,4,2244,45,8,217,36,93,16,1,404,9,48,285,141,501,169,145,517,3540,693,57,61,265,73,325,81,89,653,109,333,509,513,113,341,493,497,125],[31,96,1929,30729,1015809,1048609,31457286,503317260,3791663116,13959004164,51539607590,206185694080,824660998144,1099543445504,2233399771169,603992840,65974992929536,70403103916704,985166713827328,70403103926304,1125934266908704]),([v3,v2,v55,v5,v6,v40,v241],[3,1,5,9,13,168,20,33,0,209,21,105,4,213,101,180,41,45,49,53,57,196,61,16,69,404,65,77,85,89,93,97,25,37,8,36,40,12,109,333,337,113,117,341,345,121,125,129,133],[31,241,3856,28816,1015825,7340177,58720296,83888392,151015432,822247433,3244294153,4294971648,8589934848,51808206880,207238463520,22784,1924145514752,6597143169280,26663157157888,37383535874048,492581215698945]),([v87,v3,v2,v5,v6,v40,v241],[36,21,20,13,3,69,16,9,404,8,25,101,224,37,4,0,45,113,40,232,61,12,161,149,209,105,29,33,229,109,49,233,3540,57,65,77,81,245,253,93,97,285,357,345,193,125,133],[31,481,1536,30737,98816,4063233,12583064,50364426,201338904,4026532360,13020692488,17213456544,103079227568,412853732000,1653568176256,2199056852992,4398616969728,17215160320,8796629903873,18146305519616,105553923146240]),([v3,v2,v251,v5,v6,v40,v241],[48,161,149,3,9,33,137,40,13,20,0,401,21,25,29,680,37,700,129,3540,45,49,53,12,113,404,16,405,69,73,77,81,85,89,261,269,65,4,8,36,61,101,105,109,117,125,121,133],[127,936,15392,114985,8257568,25166240,100663442,939533328,3489759256,13155041296,51833208848,68727865344,137439068296,824635162752,1099520017408,6597069841408,13194140722176,17592211219456,10995118080000,105554215239680,175921886920704]),([v238,v3,v2,v5,v6,v40,v241],[36,33,20,13,3,69,16,9,404,105,316,25,0,8,37,4,109,61,40,324,113,12,161,149,17,21,213,101,129,45,49,53,3540,57,65,73,77,177,89,93,269,169,337,301,385,125,133],[31,481,7697,24576,106496,4063233,12583064,50334744,201359370,4026540040,12920029192,51539610800,68853727392,412853739680,1653568176256,2199157509632,4398583392769,9350162156544,17592857174016,68855431168,105553923153920]),([v3,v2,v5,v248,v6,v40,v241],[48,161,149,3,9,13,17,21,560,25,40,20,4,417,33,37,421,584,41,3540,45,49,53,12,61,317,65,69,73,404,16,425,81,85,89,189,97,0,101,105,109,125,117,77,8,229,36,113,121,129,133],[63,1001,3240,127008,8257568,58737696,469762840,1610613778,6576705552,25905725456,103238598672,137438955336,824633758464,1649269146368,6597162041856,8796101410816,123145303491584,140737496748032,1374390751232,281475001913344,1691048909733888]),([v245,v3,v2,v5,v6,v40,v241],[40,13,33,3,20,9,249,404,16,25,776,333,0,37,780,341,4,12,129,8,61,48,161,149,137,17,21,361,29,389,41,45,49,53,201,125,85,69,89,109,105,101,445],[31,481,7689,122889,393216,1703936,31457356,236981260,874561548,16106651652,51539738630,37751880,272678984,483184345152,51539738720,302042120,1651415451648,51539741184,2750927110144,51539779584,4434554388480])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x1 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x2 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x3 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (3*8)).take 8) = true := by decide +kernel
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := levelStep ptopB ptopW ptopI9 (chunks 8 ptopD10 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  · exact ptopC10x1
  · exact ptopC10x2
  · exact ptopC10x3
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ptopD11 : List StD := [([v3,v2,v5,v6,v40,v241],[3,1,5,9,13,17,21,0,25,29,33,4,37,8,41,45,49,53,57,12,61,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,129,133],[31,497,7697,253969,1836049,14680457,54532105,205561865,811073545,3221232001,6442492289,25773474177,5368756225,42968029185,481037950977])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 8 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677288 * 2 ^ 32 + 4007690240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega

def smallCircuit : Circuit := ⟨[⟨.and, [0,5]⟩,⟨.or, [4,6]⟩,⟨.and, [2,3]⟩,⟨.or, [2,3]⟩,⟨.and, [7,9]⟩,⟨.and, [1,10]⟩,⟨.or, [0,11]⟩,⟨.or, [5,8]⟩,⟨.and, [1,13]⟩,⟨.or, [10,14]⟩,⟨.and, [5,8]⟩,⟨.or, [12,16]⟩,⟨.and, [15,17]⟩],18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by simp [PEqualNP.MetaComplexity.Monotone2,smallCircuit]
theorem witnessSize : smallCircuit.size = 13 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by decide +kernel
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_48803


theorem PEqualNP.Outside.L_meta_48803 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4007690240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4007690240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_48803.replaceShort
