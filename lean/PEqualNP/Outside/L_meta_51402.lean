import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
namespace PEqualNP.Outside.L_meta_51402
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
def inputs : List Sig := [(BitVec.ofNat 512 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)),(BitVec.ofNat 512 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)),(BitVec.ofNat 512 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)),(BitVec.ofNat 512 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),(BitVec.ofNat 512 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),(BitVec.ofNat 512 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000)),(BitVec.ofNat 512 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000)),(BitVec.ofNat 512 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000))]
def graph : Sig := (BitVec.ofNat 512 (0xfffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00fffffffffffffffffffffffffffefffefffffffefffffffcfefefafaeeccaa00))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  ∀ w i,(asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val = true := by
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
  ∃ (f : Row → Row) (roots : List Sig),(∀ r, bit (f r) d = true) ∧
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
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def qG_ (m : Nat) : Sig :=
  let x := vertex m
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001)
  | 1 => (0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)
  | 2 => (0x100000000000000010000000000000000000000000000000000000000000000010000000000000001)
  | 3 => (0x10000000000000000000000000000000000000000000000000000000000000001)
  | 4 => (0x1000000000000000100000000000000010000000000000001)
  | 5 => (0x100000000000000000000000000000001)
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
theorem qP_ (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := qG_ m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def columnPairs (m z s : Nat) (G : Sig) : List (Sig × Row × Row) :=
  if m.testBit 8 then
    (selected s).map fun (i,a) =>
      let v := 1 <<< i
      let candidates := (0 :: (List.range 8).map (fun j => 1 <<< j))
      let r := (candidates.find? fun r =>
        bit (Fin.ofNat 512 r) G != bit (Fin.ofNat 512 (r ||| v)) G).getD 0
      (a, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| v))
  else supportPairs (z/512+80) s
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (qG_ q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (qG_ q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (qG_ q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (qP_ _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (qP_ _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (qP_ _ ok.1.1.1) (qP_ _ hh.1.1) (valid q) p bank hr ha)
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (qG_ old) && plainWord (qG_ old) && (varsX old).all plainWord) && properB (qG_ rep) &&
    checkMap (swaps.map swapRows) (varsX old) (qG_ old) (varsX rep) (qG_ rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (qG_ rep) L) : Lower u (varsX old) (qG_ old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (qP_ _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (qP_ _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2) (q : Nat) :
    Lower u (varsX q) (qG_ q) (boundsBefore entries q) := by
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
    exact ⟨by omega,rfl⟩
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (qG_ m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases ht : m.testBit 8 = true
  · simp only [bit,qG_,liftGoal,if_pos ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
  · simp only [bit,qG_,liftGoal,if_neg ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
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
    (lower : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (qG_ q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (qP_ _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (qG_ e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (qG_ m) L)
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
end ForestCore
end PEqualNP.Outside.L_meta_51402
namespace PEqualNP.Outside.L_meta_51402.ForestCore
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
private def proofWord80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0
def g82Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f)),(BitVec.ofNat 152 (0x49204920492049204920492049204920492049))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7)),(BitVec.ofNat 152 (0x92409240924092409240924092409240924092))),(0x0,0x0),((BitVec.ofNat 152 (0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8)),(BitVec.ofNat 152 (0x24812481248124812481248124812481248124))),(0x0,0x0),(0x0,0x0)]
def g82C : List ColumnInfo := []
def g82A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g82D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g82L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g82D3)
  | _ => emptyPacking
def g82I (_ _ : Nat) : Option (Nat × Nat) := none
def g82 : Forest := ⟨82,3,fun i => g82Y[i]?.getD (0,0),g82C,g82A,g82L,g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3_0 : block g82 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g82B3 : block g82 3 0 1=true := g82P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82T : checkedTables g82 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g82 0 0 0 = true)
  · exact (rfl : block g82 1 0 0 = true)
  · exact (rfl : block g82 2 0 0 = true)
  · exact g82B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82G : graphValid g82 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (qG_ 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound [] baseKnown) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K82 := extendKnown [] 4 [(82,[]),(137,[16,67,118]),(161,[16,84,118]),(164,[33,84,118]),(194,[100,84,117]),(196,[33,100,84,117]),(200,[49,33,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) baseKnown low82 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xe6de3fff03fff1ffe6de3fff03fff1ffe6de3f)),(BitVec.ofNat 152 (0x648490a285024020648490a28502402064849))),(0x0,0x0),((BitVec.ofNat 152 (0x19e9c0fffc07fe3f19e9c0fffc07fe3f19e9c0)),(BitVec.ofNat 152 (0x50e8db2c3161408450e8db2c3161408450e8db))),((BitVec.ofNat 152 (0xece607fffff8003fece607fffff8003fece607)),(BitVec.ofNat 152 (0x8a7b6b04185892808a7b6b04185892808a7b6))),(0x0,0x0),((BitVec.ofNat 152 (0x1b3df8ffffffffc01b3df8ffffffffc01b3df8)),(BitVec.ofNat 152 (0x891524c082060030891524c082060030891524))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := []
def g45A : List (List Nat) := [[],[80,50]]
def g45D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g45L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g45D3)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,3,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3_0 : block g45 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B3 : block g45 3 0 1=true := g45P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K82) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (qG_ 45) 4 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K82 V82) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K82 4 [(45,[]),(75,[96,33,16,49,83]),(77,[96,32,50,83]),(89,[96,32,67,50,83]),(101,[32,99,67]),(102,[32,16,83,67,100]),(105,[48,82,96,66,64]),(108,[32,16,49,81,65,100]),(147,[16,32,67,117,101]),(150,[16,67,117,101]),(209,[96,32,67,50,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V82 low45 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f)),(BitVec.ofNat 152 (0x45c09245142904808b81248a28520901170249))),((BitVec.ofNat 152 (0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0)),(BitVec.ofNat 152 (0x96a9b6d618b228112d536dac316450225aa6db))),(0x0,0x0),((BitVec.ofNat 152 (0xfbb781ffffff8007f76f03ffffff000feede07)),(BitVec.ofNat 152 (0x235249820c03122046a49304180624408d492))),(0x0,0x0),((BitVec.ofNat 152 (0x64ffe3ffffffff80c9ffc7ffffffff0193ff8)),(BitVec.ofNat 152 (0x24920410040040004924082008008000924))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86A : List (List Nat) := [[],[65]]
def g86D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g86L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g86D4)
  | _ => emptyPacking
def g86I (_ _ : Nat) : Option (Nat × Nat) := none
def g86 : Forest := ⟨86,4,fun i => g86Y[i]?.getD (0,0),g86C,g86A,g86L,g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g86B4 : block g86 4 0 1=true := g86P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (qG_ 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16844352) (before_sound K45 V45) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K45 5 [(86,[]),(90,[50]),(139,[32,16,67,118]),(141,[16,67,118]),(163,[32,16,84,118]),(166,[33,84,118]),(172,[33,49,84,118]),(195,[32,100,84,117]),(197,[16,32,100,84,117]),(212,[33,65,49,115,83]),(216,[49,66,114,82]),(225,[16,98,50,84,67,116]),(226,[82,50,100,116]),(232,[49,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V45 low86 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfe7d01c7fc0fc7cfe7d01c7fc0fc7cfe7d01c7)),(BitVec.ofNat 152 (0x51d124928a290a051d124928a290a051d1249))),(0x0,0x0),((BitVec.ofNat 152 (0x3f8b8e38fff007f3f8b8e38fff007f3f8b8e38)),(BitVec.ofNat 152 (0x884b924930c3210884b924930c3210884b9249))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0x3fe7703ffffff803fe7703ffffff803fe7703f)),(BitVec.ofNat 152 (0x10002492410402010002492410402010002492))),(0x0,0x0),((BitVec.ofNat 152 (0xc018ffc0fffffffc018ffc0fffffffc018ffc0)),(BitVec.ofNat 152 (0x20004924820804020004924820804020004924))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g165L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g165D4)
  | _ => emptyPacking
def g165I (_ _ : Nat) : Option (Nat × Nat) := none
def g165 : Forest := ⟨165,4,fun i => g165Y[i]?.getD (0,0),g165C,g165A,g165L,g165I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165P4_0 : block g165 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g165B4 : block g165 4 0 1=true := g165P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165T : checkedTables g165 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g165 0 0 0 = true)
  · exact (rfl : block g165 1 0 0 = true)
  · exact (rfl : block g165 2 0 0 = true)
  · exact (rfl : block g165 3 0 0 = true)
  · exact g165B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165G : graphValid g165 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (qG_ 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K86 V86) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K86 5 [(165,[]),(169,[48,82,32]),(198,[16,101]),(201,[98,50,83]),(202,[16,50,101]),(204,[32,16,49,101]),(210,[64,16,114,50,49,81,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V86 low165 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (qG_ 55) 4 := by
  have q := @lower_count true (vars 55) (qG_ 55) (qP_ _ (by decide +kernel)) (graphPairs 55 66885) (by decide +kernel)
  exact q
def K55 := extendKnown K165 4 [(59,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V165 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0x1fff0007ff803ffc01fffffffffff245f3f007)),(BitVec.ofNat 152 (0x502a8350250681482d0550950a414040f37b6d))),((BitVec.ofNat 152 (0x1ffffff800003fffffffe001ffe001b15bc038)),(BitVec.ofNat 152 (0x854c2a62b62b1591482986d84c8661a159c6db))),((BitVec.ofNat 152 (0x1fffffffffffc00001fffffe00000ce425d1c0)),(BitVec.ofNat 152 (0x6703383384c19e2704e04e06f0b88a425d6db))),((BitVec.ofNat 152 (0xe00000000000000001fffffffffff22fedae07)),(BitVec.ofNat 152 (0x7803c03c0701e0380700700700c022d0c8492))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffffffffe00000000000dfa9e5ff8)),(BitVec.ofNat 152 (0x1800c004000020000180180180100452820924))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g79L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g79D4)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,4,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 1=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (qG_ 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 5 [(124,[80,49,66,33,16]),(151,[64,16,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc00ffc3fe1ffc01ffff87ffcd452be00001f)),(BitVec.ofNat 152 (0x22a4a228884522a950a81148805012bf5ad6b5))),((BitVec.ofNat 152 (0xfffff0003fffffffe00fffffc31359e2007fe0)),(BitVec.ofNat 152 (0xb00c0b102800b0182c0a0010a025922318c63))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffc001fffffff0007ffcefd1140f801f)),(BitVec.ofNat 152 (0x4c0904c013084c020302c21200af4100a5294a))),((BitVec.ofNat 152 (0x1ffffffffff80004d2fe9f003e0)),(BitVec.ofNat 152 (0x700e07021c10700c0403001c104d06c0c6318c))),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffe000000000000033aa61bfffc00)),(BitVec.ofNat 152 (0x8030080020018030180c04602110a019084210))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,1,82,8,5),(1,0,90,0,5),(2,0,89,0,4),(8,1,82,0,4),(16,0,75,0,4)]
def g91A : List (List Nat) := [[],[65]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d41
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x20120240d140ff41fd41fd31)
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2051600028b5
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 11 0 7 2 1 g91H6
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
theorem g91P5_0 : block g91 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 3=true := g91P5_0
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
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (qG_ 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(118,[80,32,50]),(155,[64,16,49,118]),(179,[64,16,49,83,118]),(182,[64,33,16,49,83,118]),(241,[64,16,33,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (0x3ffc003ffc01ffe00ffffffffffffeddea003f)),(BitVec.ofNat 152 (0x80a81a8128340a4160a02a094148524c6a1249))),((BitVec.ofNat 152 (0x3fffffc00001fffff007ff001ffc0118f681c0)),(BitVec.ofNat 152 (0x15315315b158ac8a45314c6d89919918f6b6db))),((BitVec.ofNat 152 (0x3ffffffffffe00000007ffffe000031f070e00)),(BitVec.ofNat 152 (0x19c19c19c260cf1389c2704e0de2e31f0736db))),((BitVec.ofNat 152 (0xc0000000000000000007fffffffffcbfdc7007)),(BitVec.ofNat 152 (0x1e01e01e0380f01c0e0380700e0300b3942492))),(0x0,0x0),((BitVec.ofNat 152 (0xfffffffffffffffffff800000000036237fff8)),(BitVec.ofNat 152 (0x20020020000100000004008010000000004924))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94A : List (List Nat) := [[],[50],[65],[65,50]]
def g94D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g94L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g94D5)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,5,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 1=true := g94P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact (rfl : block g94 4 0 0 = true)
  · exact g94B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (qG_ 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 6 [(94,[]),(143,[64,16,33,50,118]),(174,[33,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xe001ffc07ff01ffe003ffc07ffffd37a12000f)),(BitVec.ofNat 152 (0x48d4128d0522c8549a9128d25229934a125555))),((BitVec.ofNat 152 (0xfffe00007fffffffffc00007ff01a3a9cc0f00)),(BitVec.ofNat 152 (0x82985b16164482981305b160644d2329c83333))),((BitVec.ofNat 152 (0xffffffff80001ffffffffff800003f4479f0f0)),(BitVec.ofNat 152 (0xe01c18078700e01c01c18078701304591111))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0x1ffffffffffffffe663f7600ff)),(BitVec.ofNat 152 (0x1301602058081301202600048000643124aaaa))),((BitVec.ofNat 152 (0xffffffffffffe0000000000000019dd38dff00)),(BitVec.ofNat 152 (0x1c01800060001c01c038020700808cd204cccc))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[16,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (qG_ 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=16778597) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[]),(117,[65,49]),(121,[64,81,50,33,32,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xf003ff0ff87ff007ffff87fffcd47c560003ff)),(BitVec.ofNat 152 (0xa4280a201120a4521481102080501c1694a529))),(0x0,0x0),((BitVec.ofNat 152 (0xfffc000ffffffff801fff87fc35353a20ffc00)),(BitVec.ofNat 152 (0xc0302c40a002c060580a01010a425122318c63))),((BitVec.ofNat 152 (0xfffffff0007ffffffe00007ffcafd11df0001f)),(BitVec.ofNat 152 (0x140b002c20b0080602c220a00a741086318c6))),(0x0,0x0),((BitVec.ofNat 152 (0x7fffffffffff80004d2fe8007fe0)),(BitVec.ofNat 152 (0x982c08b044c09048130004c100d22c94a5294))),((BitVec.ofNat 152 (0xffffffffff80000000000000033aa61bff8000)),(BitVec.ofNat 152 (0xe03000c00700e0701c044702118a6118c6318))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,4),(4,0,105,0,4),(8,0,101,0,4),(32,0,77,0,4),(64,0,45,0,4)]
def g109A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x25fe0093000000520031000000000000000000200000000026000000bb970000000000000000000000006a0000000000000000)
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (2,1,3,0,0,4,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 2 53 0 8 1 3 g109H6
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
theorem g109P5_0 : block g109 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 2=true := g109P5_0
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
theorem g109G : graphValid g109 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (qG_ 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K103 V103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K103 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V103 low109 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xc003ff0ffc3ffc00ffffffffc02b3e79000fc0)),(BitVec.ofNat 152 (0x90a80a204890a92a4291204088292e194d34d3))),((BitVec.ofNat 152 (0xfffc000fffffffff003ff0fffec8a9d703f03f)),(BitVec.ofNat 152 (0x2304c411002300c13004209020009d3145145))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xfffffff0003fffffffc000fffd77e88afc003f)),(BitVec.ofNat 152 (0x4c090026104c030040584120172a00828a28a))),((BitVec.ofNat 152 (0x3fffffffffff00012697f4000fc0)),(BitVec.ofNat 152 (0x2702e08b822702409826009c110691e4b2cb2c))),((BitVec.ofNat 152 (0xffffffffffc0000000000000039d530dfff000)),(BitVec.ofNat 152 (0x3803000c00380380e03808e0208d5204c30c30))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,1,82,32,5)]
def g115A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[80],[80,100],[80,65],[80,65,97],[80,97,65],[80,97]]
def g115D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g115L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g115D5)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,5,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 1=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact g115B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (qG_ 115) 6 := lower_forest (g:=g115) (i:=0) (hints:=16842821) (before_sound K109 V109) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K109 6 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V109 low115 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xffc00ffc07fe03fffe00ffc0ffff447d401c7)),(BitVec.ofNat 152 (0xa0a86a128d0a458a0546a129a2929043d49249))),((BitVec.ofNat 152 (0xfffff00007fffc07ffff0000ff81386ac0e00)),(BitVec.ofNat 152 (0xc5314c5b162c89132984c5b2c324d386adb6db))),((BitVec.ofNat 152 (0xfffffffff8000007ffffffff0000be8947038)),(BitVec.ofNat 152 (0x1c0701c180f0e1c0e0701c303c709e0949249))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (0xf0000000000000007fffffffffffe6fe67803f)),(BitVec.ofNat 152 (0x601806020301020300806000400061c212492))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffffff8000000000001911bbffc0)),(BitVec.ofNat 152 (0x8020080004000004010080008000000024924))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
def g167D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g167D5)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B5 : block g167 5 0 1=true := g167P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact g167B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (qG_ 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K115 V115) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K115 6 [(167,[]),(171,[48,82,32]),(199,[16,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V115 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (0xfe1ff00ff87f87ffc07fff8fffd8b95000f0ff)),(BitVec.ofNat 152 (0x1440a0a0510110028505012008488941111111))),(0x0,0x0),((BitVec.ofNat 152 (0x1ffff0007ff87fff807ff1fc2b1e600f0f00)),(BitVec.ofNat 152 (0x5882c0c1620a010b06160a0411291e43333333))),((BitVec.ofNat 152 (0x1fffffff80007fffff8001ff941fb0f0000f)),(BitVec.ofNat 152 (0x610b0505802c222c08182c48a01416b6666666))),(0x0,0x0),((BitVec.ofNat 152 (0xffe000000000007ffffffffe000be4bf000ff0)),(BitVec.ofNat 152 (0x800c06060430443010203000c20260b4444444))),(0x0,0x0),((BitVec.ofNat 152 (0xffffffffffffff8000000000006442cffff000)),(BitVec.ofNat 152 (0x100808004000402040400100000008888888))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (qG_ 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior506 : Lower true (varsX 506) (qG_ 506) 8 := by
  have h := lift_ok (u := true) (ms := ([16,66,67]).map swapRows ++ fixRows 64 0)
    (raw := varsX 506) (T := qG_ 506) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (qG_ 505) 8 := by
  have h := lift_ok (u := true) (ms := ([112,66,115,117,118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 505) (T := qG_ 505) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior499 : Lower true (varsX 499) (qG_ 499) 8 := by
  have h := lift_ok (u := true) (ms := ([112,66,99,116,117]).map swapRows ++ fixRows 2 0)
    (raw := varsX 499) (T := qG_ 499) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior498 : Lower true (varsX 498) (qG_ 498) 7 := by
  have h := lift_ok (u := true) (ms := ([16,113,66,99,116,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 498) (T := qG_ 498) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (qG_ 497) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,99,116,117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 497) (T := qG_ 497) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior475 : Lower true (varsX 475) (qG_ 475) 8 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 475) (T := qG_ 475) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior443 : Lower true (varsX 443) (qG_ 443) 8 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 32 0)
    (raw := varsX 443) (T := qG_ 443) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior442 : Lower true (varsX 442) (qG_ 442) 7 := by
  have h := lift_ok (u := true) (ms := ([16,66,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 442) (T := qG_ 442) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior411 : Lower true (varsX 411) (qG_ 411) 7 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 411) (T := qG_ 411) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior379 : Lower true (varsX 379) (qG_ 379) 8 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 379) (T := qG_ 379) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (qG_ 377) 7 := by
  have h := lift_ok (u := true) (ms := ([112,66,115,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 377) (T := qG_ 377) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior347 : Lower true (varsX 347) (qG_ 347) 7 := by
  have h := lift_ok (u := true) (ms := ([33,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 347) (T := qG_ 347) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (qG_ 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [(inputs.getD 4 zero,64,80),(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80),(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior491 : Lower true (varsX 491) (qG_ 491) 7 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 194 0)
    (raw := varsX 491) (T := qG_ 491) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior490 : Lower true (varsX 490) (qG_ 490) 6 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 72 0)
    (raw := varsX 490) (T := qG_ 490) (xs := [(inputs.getD 3 zero,32,40),(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40),(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior489 : Lower true (varsX 489) (qG_ 489) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 489) (T := qG_ 489) (xs := [(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior488 : Lower true (varsX 488) (qG_ 488) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 488) (T := qG_ 488) (xs := [(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior483 : Lower true (varsX 483) (qG_ 483) 6 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 66 0)
    (raw := varsX 483) (T := qG_ 483) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior482 : Lower true (varsX 482) (qG_ 482) 5 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 482) (T := qG_ 482) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior481 : Lower true (varsX 481) (qG_ 481) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 481) (T := qG_ 481) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior474 : Lower true (varsX 474) (qG_ 474) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 136 0)
    (raw := varsX 474) (T := qG_ 474) (xs := [(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (qG_ 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 144 0)
    (raw := varsX 473) (T := qG_ 473) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior467 : Lower true (varsX 467) (qG_ 467) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 130 0)
    (raw := varsX 467) (T := qG_ 467) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior466 : Lower true (varsX 466) (qG_ 466) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 128 0)
    (raw := varsX 466) (T := qG_ 466) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior465 : Lower true (varsX 465) (qG_ 465) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 128 0)
    (raw := varsX 465) (T := qG_ 465) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior459 : Lower true (varsX 459) (qG_ 459) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 130 0)
    (raw := varsX 459) (T := qG_ 459) (xs := [(inputs.getD 1 zero,64,66),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,64,66),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior457 : Lower true (varsX 457) (qG_ 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 128 0)
    (raw := varsX 457) (T := qG_ 457) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (qG_ 441) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 144 0)
    (raw := varsX 441) (T := qG_ 441) (xs := [(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (qG_ 440) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 440) (T := qG_ 440) (xs := [(inputs.getD 4 zero,128,144)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,128,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior435 : Lower true (varsX 435) (qG_ 435) 6 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 34 0)
    (raw := varsX 435) (T := qG_ 435) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior434 : Lower true (varsX 434) (qG_ 434) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 434) (T := qG_ 434) (xs := [(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior433 : Lower true (varsX 433) (qG_ 433) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 433) (T := qG_ 433) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior427 : Lower true (varsX 427) (qG_ 427) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 130 0)
    (raw := varsX 427) (T := qG_ 427) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior426 : Lower true (varsX 426) (qG_ 426) 5 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 426) (T := qG_ 426) (xs := [(inputs.getD 3 zero,32,40)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior425 : Lower true (varsX 425) (qG_ 425) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 425) (T := qG_ 425) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior424 : Lower true (varsX 424) (qG_ 424) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 424) (T := qG_ 424) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior419 : Lower true (varsX 419) (qG_ 419) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 419) (T := qG_ 419) (xs := [(inputs.getD 1 zero,32,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior418 : Lower true (varsX 418) (qG_ 418) 4 := by
  have h := lift_ok (u := true) (ms := ([84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 418) (T := qG_ 418) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior417 : Lower true (varsX 417) (qG_ 417) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 417) (T := qG_ 417) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior410 : Lower true (varsX 410) (qG_ 410) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 410) (T := qG_ 410) (xs := [(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior409 : Lower true (varsX 409) (qG_ 409) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 409) (T := qG_ 409) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior403 : Lower true (varsX 403) (qG_ 403) 5 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 403) (T := qG_ 403) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior402 : Lower true (varsX 402) (qG_ 402) 4 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 402) (T := qG_ 402) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior401 : Lower true (varsX 401) (qG_ 401) 4 := by
  have h := lift_ok (u := true) (ms := ([16,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 401) (T := qG_ 401) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior395 : Lower true (varsX 395) (qG_ 395) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 395) (T := qG_ 395) (xs := [(inputs.getD 1 zero,128,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,128,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior393 : Lower true (varsX 393) (qG_ 393) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 393) (T := qG_ 393) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior378 : Lower true (varsX 378) (qG_ 378) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 40 0)
    (raw := varsX 378) (T := qG_ 378) (xs := [(inputs.getD 3 zero,32,40),(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,32,40),(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior371 : Lower true (varsX 371) (qG_ 371) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 34 0)
    (raw := varsX 371) (T := qG_ 371) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior370 : Lower true (varsX 370) (qG_ 370) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 32 0)
    (raw := varsX 370) (T := qG_ 370) (xs := [(inputs.getD 5 zero,2,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior369 : Lower true (varsX 369) (qG_ 369) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 32 0)
    (raw := varsX 369) (T := qG_ 369) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior363 : Lower true (varsX 363) (qG_ 363) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 66 0)
    (raw := varsX 363) (T := qG_ 363) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior361 : Lower true (varsX 361) (qG_ 361) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 361) (T := qG_ 361) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior346 : Lower true (varsX 346) (qG_ 346) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 8 0)
    (raw := varsX 346) (T := qG_ 346) (xs := [(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior345 : Lower true (varsX 345) (qG_ 345) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 16 0)
    (raw := varsX 345) (T := qG_ 345) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior339 : Lower true (varsX 339) (qG_ 339) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 2 0)
    (raw := varsX 339) (T := qG_ 339) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior338 : Lower true (varsX 338) (qG_ 338) 4 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 0 0)
    (raw := varsX 338) (T := qG_ 338) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior337 : Lower true (varsX 337) (qG_ 337) 4 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 0 0)
    (raw := varsX 337) (T := qG_ 337) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior331 : Lower true (varsX 331) (qG_ 331) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 2 0)
    (raw := varsX 331) (T := qG_ 331) (xs := [(inputs.getD 1 zero,64,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,64,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior329 : Lower true (varsX 329) (qG_ 329) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 329) (T := qG_ 329) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior315 : Lower true (varsX 315) (qG_ 315) 6 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 18 0)
    (raw := varsX 315) (T := qG_ 315) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior313 : Lower true (varsX 313) (qG_ 313) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 16 0)
    (raw := varsX 313) (T := qG_ 313) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior299 : Lower true (varsX 299) (qG_ 299) 5 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 2 0)
    (raw := varsX 299) (T := qG_ 299) (xs := [(inputs.getD 1 zero,32,34)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior297 : Lower true (varsX 297) (qG_ 297) 4 := by
  have h := lift_ok (u := true) (ms := ([16,67,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 297) (T := qG_ 297) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior496 : Lower true (varsX 496) (qG_ 496) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,115,101,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 496) (T := qG_ 496) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior376 : Lower true (varsX 376) (qG_ 376) 4 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,67,100,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 376) (T := qG_ 376) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior314 : Lower true (varsX 314) (qG_ 314) 4 := by
  have h := lift_ok (u := true) (ms := ([16,66,67]).map swapRows ++ fixRows 0 0)
    (raw := varsX 314) (T := qG_ 314) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(506,8),(505,8),(499,8),(498,7),(497,7),(475,8),(443,8),(442,7),(411,7),(379,8),(377,7),(347,7),(504,6),(491,7),(490,6),(489,6),(488,5),(483,6),(482,5),(481,5),(474,6),(473,6),(467,6),(466,5),(465,5),(459,6),(457,5),(441,6),(440,5),(435,6),(434,5),(433,5),(427,6),(426,5),(425,5),(424,4),(419,5),(418,4),(417,4),(410,5),(409,5),(403,5),(402,4),(401,4),(395,5),(393,4),(378,6),(371,6),(370,5),(369,5),(363,6),(361,5),(346,5),(345,5),(339,5),(338,4),(337,4),(331,5),(329,4),(315,6),(313,5),(299,5),(297,4),(496,4),(376,4),(314,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior506
  · exact prior505
  · exact prior499
  · exact prior498
  · exact prior497
  · exact prior475
  · exact prior443
  · exact prior442
  · exact prior411
  · exact prior379
  · exact prior377
  · exact prior347
  · exact prior504
  · exact prior491
  · exact prior490
  · exact prior489
  · exact prior488
  · exact prior483
  · exact prior482
  · exact prior481
  · exact prior474
  · exact prior473
  · exact prior467
  · exact prior466
  · exact prior465
  · exact prior459
  · exact prior457
  · exact prior441
  · exact prior440
  · exact prior435
  · exact prior434
  · exact prior433
  · exact prior427
  · exact prior426
  · exact prior425
  · exact prior424
  · exact prior419
  · exact prior418
  · exact prior417
  · exact prior410
  · exact prior409
  · exact prior403
  · exact prior402
  · exact prior401
  · exact prior395
  · exact prior393
  · exact prior378
  · exact prior371
  · exact prior370
  · exact prior369
  · exact prior363
  · exact prior361
  · exact prior346
  · exact prior345
  · exact prior339
  · exact prior338
  · exact prior337
  · exact prior331
  · exact prior329
  · exact prior315
  · exact prior313
  · exact prior299
  · exact prior297
  · exact prior496
  · exact prior376
  · exact prior314
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0xc003c0e1cfc003000e01c3f04013081311333f), BitVec.ofNat 152 (0xc9201408000005001202449000110011011115)),(BitVec.ofNat 152 (0x1c030630001c00f01e3c00809c109c29cdcc), BitVec.ofNat 152 (0x1b20742842002d0132264cb00094009409454c)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0),(BitVec.ofNat 152 (0xc0e00c1801c0e00f01e0007104e024e0ce0e0f), BitVec.ofNat 152 (0x3204e162c20168132064196004a004a04a0e0a)),(BitVec.ofNat 152 (0x70030003e0700f000003f822700c700f00ff0), BitVec.ofNat 152 (0x204d8bc2804b403200c8b34025004500f00aa0)),(BitVec.ofNat 152 (0x3800001fc038000001ffc00c3800f800fff000), BitVec.ofNat 152 (0x4db0a8014da00644599a2042800f800b4a000)),(BitVec.ofNat 152 (0x3fe0000000fffe00000fc000ffff000000), BitVec.ofNat 152 (0x49200153db492cccd11000fc000ba4a000000)),(BitVec.ofNat 152 (0x3fffc000003fff000000000fffff0000000000), BitVec.ofNat 152 (0x15292492888800000bd24a0000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(1,0,506,0,8),(2,0,505,0,8),(8,0,499,0,8),(9,0,498,0,7),(10,0,497,0,7),(32,0,475,0,8),(64,0,443,0,8),(65,0,442,0,7),(96,0,411,0,7),(128,0,379,0,8),(130,0,377,0,7),(160,0,347,0,7),(3,0,504,0,6),(16,0,491,0,7),(17,0,490,0,6),(18,0,489,0,6),(19,0,488,0,5),(24,0,483,0,6),(25,0,482,0,5),(26,0,481,0,5),(33,0,474,0,6),(34,0,473,0,6),(40,0,467,0,6),(41,0,466,0,5),(42,0,465,0,5),(48,0,459,0,6),(50,0,457,0,5),(66,0,441,0,6),(67,0,440,0,5),(72,0,435,0,6),(73,0,434,0,5),(74,0,433,0,5),(80,0,427,0,6),(81,0,426,0,5),(82,0,425,0,5),(83,0,424,0,4),(88,0,419,0,5),(89,0,418,0,4),(90,0,417,0,4),(97,0,410,0,5),(98,0,409,0,5),(104,0,403,0,5),(105,0,402,0,4),(106,0,401,0,4),(112,0,395,0,5),(114,0,393,0,4),(129,0,378,0,6),(136,0,371,0,6),(137,0,370,0,5),(138,0,369,0,5),(144,0,363,0,6),(146,0,361,0,5),(161,0,346,0,5),(162,0,345,0,5),(168,0,339,0,5),(169,0,338,0,4),(170,0,337,0,4),(176,0,331,0,5),(178,0,329,0,4),(192,0,315,0,6),(194,0,313,0,5),(208,0,299,0,5),(210,0,297,0,4),(11,0,496,0,4),(131,0,376,0,4),(193,0,314,0,4)]
def genData4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x2479848c180d060b859d92641655c910b051c326167641655c910b051c326167541655c910b031c426167641655c910b031c426167541655c9109641c32e52764165589109621c42e5276416558910)
def genData5 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0xc910b4c764cbf00b2ac4885a61b825f2059562442d30db75093aca012216986c897e016558910b4c170c92c0b2ae4885a53b859d3059532442d29d9b50b2ac701221694ecda76558600910b4a766cc2c0b2ee8885a53b36616059573442d29d9b30b02cab9221694ecd97e016558910b4a766cbb00b2ec6885a53b365d8059762442d29d9b2ec02cab1a21694ecd9758185d9110b4a766cbac0c2ec6885a53b365d6061762442d29d9b0eb2a06b1221694ecd67e01654c910b4a766b3acac1c04885a52b32616059572442d295992fc02cab12216946e3a35956380910b4a3711baca81ac4885a51b68e16540d72442d28db46fc02ca992216946cc98581655c910b4a3664bf00b2ac4885a50b36616059572442d2859b2fc02cab122168ced198581655c910b463684c2c0b2ae4885a31b425f8059562442c38dc4f2b3acb0122161c6e07959d6580910b0e3643c2cec02ca885855b32616759572442c1ada130b3acab9221598ec9975956380910acc760d332443aca885661b6e819221d65442b30d972eb2ac7012215986ca976416558910acc3644bb20b2ac4885660b949d9059562442b29d9b0fc9ac0b2a21594ecd67e4d8059510aca369c9b20b2ac6885651b325d9059562442b28d9726c82cab1a2158c6d0976416558910a74772d324ec20048853a3b469b9849c024429b05c324c82cab92214d4ee5a75958300910a6a3664c320b2ae4885351b32615059572442998da130c82cab92214cc6d098541655c910a5a3664c2c0b2ae48852b1b42616059572442939dcb0eb02ca9922149cee5675958380910a4e770cbacab1c04885271b8e5d6558e02442938dc12ec82cab122149c6c398595635c910a4e172c3b20b2ac4885270b961d605953244286ad9930b3acab922142d6d09859d655c9109f0174a1a4e82264884e63ba65f2059562442730dd12f902cab12213986daa764965809109cc367d12ceb2c04884e61b0aa527595624427305d324b3acb012213982e92764165589109ca760d1726b2ac6884e51b4e8d9059563442723d9b4fc92cab12213916cca949d65589109c4b6854a4eb2ac4884ba3b469b9849c024425c9da3511ba06b12212d86e2a7649658091096a766d4d0eb2804884b33b568e4841172442599da3512ba0ab12212cced1a6961055c91094e774b3f00b2a64884a73b6e819859572442539dab473420cb922129cec1a661d654c91094e375cc2c0b2ae8884a71ba25f8059562442538db54ecc2cb0122129c6cfa859d658091094e361d3ad0b2a64884a70ba61d90595624423e05d32693a08992211e4ed1a2e4d7640d108f2766d2f28bb2088878417649d6560c02443c10bb24eb2b0801221c185d99849d6500910d0c2edd424eb2804885a11b64c16561332442c30d90f0b3b00b2a216146cc7859d8059510) else (if j<2 then (0x58300910f48326b1700b2a64887a416849d3059532443d20b1b25c02ca99221e9058a37e01654c910f48270d12cab1c04887a21b649d6561002443d08aa2c6c02caa1a21e505e9275958300910f242f493acac2004887891685d1305d943443c48b42e6a02eca1a21e185e9276558600910f0c2f2b424eb280488786176ea12759402443c30bb33093aca01221e148e167595035c910f0a2ed1bf00b2a64887851674e165dce02443c18b42e8a82ecaa221d9064d62641654c910ec82c6c9320b2a648876115458d9059543443a31cbd2f902cab1221d18de5276416558910e8c6eacb24e82ac4887461676499059572443a28cbf26b02cbb9a21d1465d93581655cd10e8a2cfc9b20b2ee68874516764d9059573443930d333093aca01221c94e61305957458d10e4a2d29c2cbb9c0488725168e4d90597734438b0dbb3093aca01221c1ce5e97e016558910e0e72eb452eb2c048870709859d90595744438384c2cec82cab9221c1c26167541655c910dc8764d3260b2a64886e41a958f2059532443720d4ac4982ca99221b9069a37c81654c910dc834cc9e40b2a64886e41a66493059532443720d324e982ca99221b9064fa0589654c910dc82c7d0324b2a64886e11a65513059543443708d2ac6a02caa1a21b245dba351d6440d10d922ecd246eb2206886c5167e8d9059773443531dd2d1902ca99221a986dba849d6500910d4c36cd110ec02ca886a61a6ea12759402443530b4744cbacb01221a985a1a225d6580910d4a2d1d1b2eb2c04886a5168e8d9759402443528b4746c82cbb9a21a945a2a325d6580910d4a2d0d192eb2c04886a51686839359773443528b4146cbacb01221a8ced9a421d8059510d462d0d212eb2c0488696179ea12759402443439d42cec82cbb9221a1c2a167641655d110d0e150b3b20b2ae4886864a859d9259572443330d3740c910eb2a21998659a295d0558910cca746c8324b2ac688665196e8d87a01654431d1cc748cb24e012218d4663a365d6500910c5674dd233083286886264a9589875953244303a54aecc3aca99221790ecda25956380910bc8766cbe40b2ac4885e43b359f2059532442f21d9a4eb2a06b1221790ec1628dd654c910bc85664be40b2ac4885e41b68df2059532442f20db24e982ca992217906cf2064d6558910bc8367902cbb9ac4885e41b325f2059562442f20d9746b2ac7012217906ca375950358910bc8166cbe40b2ac4885e21b425f2059562442e30d94f2b3acb012217186c87959d6580910b8c16ec92ceb2c04885c51b7e4d6059773442e28d98f2b3acb012217142cd97581655c910b88966bca4eb2ac4885c31b41e56759602442dc1da34c93b06012216c8ed1a649d8500910b62766d3acac2004885aa3b46a52761802442d31dc34c93aca01221698ee167c81654) else (0x1203050680af08000000041a02bc200038410080384100808080201c20804210040000000004240800000012030400001080243405784000000704201000000000012030400000000000000000578243405784010d015e10000000000000000001c10804000000000000000000000000000000037040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8bacb4968cd0da033d674ca993b1760ec117d6eadc2b796dad85aab4967ac5d85aff5e6b9d6dab5552a7548a6b45687d09a0738e6ecd79a332e62cbf97329a5049a92923a444828f91da3846a8c914618c2b817015ffbf97e6fb5f3be17b6f55e7bc9752e8dceb97722e2dc2b7f6f2dcdb6b676c2d6daab4f692d0d9eb37662c798c312618c19802fa5e8bb9742e25b8b59682ca588af95c2b2558a995029a528a39442824f89d93826a4c89792c2524989192023a4688b9142224388590820a4087f8fc1f23d8798f01da3a8738e41c23786d8d81aa348678cc192318618c017a2e85b8b41622b8558a814a2884f89c1322584989011a228438841021f83d8780ea1c83786c0d2198318600ba1682b8540a21382584808a1081f83c0720d81983005a0a8138240420780d81802a0480780c012018018007c41768df2059532443e20bb24e982ca99221e906d92759)))
def genIndex5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x7ef07203f0d465e0f08641f0)
def genData6 (j : Nat) : Nat := if 13 ≤ j then 0 else (if j<6 then (if j<3 then (if j<1 then (0x10f905893059532443c617689d6580910f185d92759402443c5373581659cd10ed049d6560c02443b21275958400910ec44c16561332443ac1634198290d10ea458d0661332443a6168c81654c910e985a12759402443a6162e01654c910e9858165a0873443a6160595821cd10e9849d9561802443a51695958300910e945a13059732443a51684c1654c910e945a13055a53443a51675958300910e9458f8059532443a516360165cc910e944e16558e02443a51385956300910e944e16540f62443a51305978258d10e8c59d6561002443a31656116300910e8c58165a1073443a316059584cc910e8c5816561073443a156359584cc910e705c97660c024439c1725d18300910e685c976610024439a1485c97400910e585c9855d002443961725d98500910e385c9865d0024438e1685c97600910e1ce1e875816544387176a1d6580910e1c5da87594024438707859d8059510d98e499059562443653936416558d10d94695960dd034436515664f0558d10cd86612759402443273985950694d10c9ce616059473443271a065a85d0d10c9c6616759402443271985956380910c9c6616558c02443271985950694d10c9c6616540f6244327198581651cd10c9c66156c15634432719564d8600910c9c64195a187344327190655861cd10c9c64165e09634432716941a851cd10b98e896759602442e63a0589654c910b98a888758165442e61a6c81654c910b9869a2759602442e61a3c816558910b986888758165442e61a0e496558910b94e8d9059563442e53a361d6059510b94e8d6541a53442e52a321d6059510b946993059732442e51a64c1654c910b94697674c163442e51a5d853058d10b94696064c163442e51a3a416558d10b9468e8059563442e51a38c16558d10b9468c8758165442e51a0e4d6558d10b946809359563442e50a361d6059510b916889359563442e15a424d6558d10b1569c9359563442bc1a34198290d10ae468d0661332442b63a849d6500910ad86888760165442b51a321d8059510acc6974841273442b31a5d210484d10acc6908760165442a73a859d6580910a9cea16759402442a73a8581659cd10a9cea16059473442a73a05a1654c910a9c6a13059563442a71a6e01654c910a9c69a8759602442a71a6a1d6500910a9c69a8059473442a71a66156300910a9c6998059732442a71a5da1069cd10a9c6976841953442a71a5da1061cd10a9c68f8059562442a71a0e1d6558d10a9c6836859773442a71a0da1655cd10a9c6836859473442a71a0da15694d10a9c6809859563442a70a859d8059510a78ea1725d8024429e3a85c974009109f068a93991034427c1a2a4d6440d1099caa48758165442671a921d605951099c69a9021d65442671a0a5a57595108f86a687c81624423e1a9a1f2050910) else (if j<2 then (0x9109f8aa7205d1324427e1a5e4976809109f868f925da024427e1a3e4974809109f868b97596024427e1a2e5d63809109f868b9750e024427d3a66523740d109f4e8d97991034427d3a365d65809109f4e8d97595044427d3a365d6440d109f4e8d90595434427d3a26523740d109f46a637991034427d1a98dd6440d109f469b935d1034427d1a4e4d7640d109f468b935d9034427d1a2e4d7440d109f468393595434427c5a98de244c9109f12a5274d1324427b3a465d65411109ec6a540595434427b1a5e5176411109ec69397595044427b1a4e4d65411109ec68f945d9044427b1a3e5106551109dce999495d05442771a5e510654d109dc693955d905442771a4e4d80595109dc68f9460165442771a2e5576415109dc68397559544423f3a96016550d108fcea580551634423f3a95d985809108fcea57660e024423f3a95d183809108fcea197596024423f3a865d63809108fcea19750e024423f3a865373809108fcea190595434423f3a66610550d108fce9994e15034423f3a56610650d108fce9593e11064423f3a46610654d108fce9196e15034423f3a366106551108fce81985d9544423f3a066176549108fce81985d9324423f3a0661744c9108fcaa7805d9524423f2a9e01764c9108fcaa7805d1324423f1a9e156440d108fc6a580595434423f1a8e5d65809108fc6a397595044423f1a8e5d63809108fc6a39750e024423f1a8e510654d108fc6a393595044423f1a6e558050d108fc697985da024423f1a5e598050d108fc69794601634423f1a4e558058d108fc69393601654423f1a3e6176809108fc68f985d2024423f1a3e5180595108fc68398595744423f1a0e61655c9108fc6839858d724423f1a0e61435c9108fc68397619544423f1a0e5d86549108fc68397619324423f1a0e5d844c9108fc68393619544423f1a0e4984dcd108fc2a190595744423f0a8641655c9108fc2a19058d724423f0a8641435c9108f9e89985d9544423d7a366176551108f5e8d985d9524423d7a366175d91108f5e8d985d7624423d7a365f82595108f5e8d95e11764423d5a3261655c9108ede9198dd5624423b7a466373589108ede91985d9524423b7a4661764c9108ede9196e15724423b7a464b835d9108ed6909859572442377a961d654c9108dde95985d932442377a5661744c9108dde9593e1972442377a564f845c9108dd69b9561d32442374a961d654c9108bde99985d1324421f7a76616550d10877e8d98dc9515821dfa36617654910877e8d95e11764421bfa4663755891086fe9198dcd624421bfa4661765491086fe91985d9324421bfa465b855c91086fe9192e0d7644217fa5661764c91085fe95985d13244217fa564f865c91085fe9593e117244217da6e55874c91083fe99985d132443e4163c81654c9) else (0x54c910b95a8c9759562442e55a7e4d6558d10b9569a3759532442e55a4e4d6558d10b9568c9759562442e55a2e4d6558d10b9528d9759562442e35a425d6558910b74693735d903442dd1a2dcd7640d10b5ce957641572442d71a695d055c910b5569f9359773442d54a365d655c910b3ae8d2758162442c75a6a5d655c910af8ea19649c02442be3a86512700910af8e899460165442be3a25d18380910af8aa72061932442be2a9c81844c910af869b9849c02442be1a4e612700910af4e8d9760165442bd3a361d6059510af4e8d8740f42442bd3a361d0358910af4e8d8740d42442bd3a35d98380910af4e8d7460e02442bd3a351d8050d10af46a23740f42442bd1a88dd0358910af46a23740d42442bd1a68e1035c910af469a37e0132442bd1a48e1035c910af469237e0132442bb3a46598050d10aece918741562442bb3a461d0458d10aece918741132442bb3a461d0358910aece918055163442bb1a4e156440d10aec68e4841172442b73a865d6580910adcea19759402442b73a864165dc910adce959360165442b73a561d064c910adce958741564442b73a561d0558910adce958741132442b73a56016550d10adce958055163442b73a36616580910adce819859572442b73a0661654c910adca9d9859602442b71a9e01654c910adc6a68759602442b71a9a1d6500910adc6a39759602442b71a8e4d6580910adc6a25741564442b71a895d0558910adc6a09759602442b71a69615440d10adc69a5841574442b71a6961055c910adc6958059543442b71a4a1d8059510adc6925859503442b71a495d8059510adc6908760165442b71a2a1d8059510adc68a5760165442b71a221d8059510adc6839859774442b71a0e6165dc910adc6839859574442b71a0e61655c910adc2a19059574442b70a8641655c910ad92a19259572442b57a366165dd110ad5e8d9859573442b57a3661655c910ad5e8d9761764442b57a365d85d8d10ad5e8d9761762442b57a365d859d910ad5e8d9761616442b57a365d8581910ad5a8c9859572442b55a3261655c910ad528d9859572442b37a4661655c910acd6909859572442af3a859d6580910abce999460163442af3a661d0655110abce998741952442af3a661d0650d10abce998741932442af3a66016550d10abce8d6841954442af1a59a1065d110abc6966841972442af1a39a1065d110abc68e6841972442a77a865d65d8910a9dea16759532442a77a75a1654c910a9de998755952442a77a361d6558910a9de898759563442a76a99a1655d110a9d6a09759562442a75a6a61655d110a9d69a9859572442a75a661d654c910a9d68e6859574442a75a2e1d6558d10a9d2a5875956244295fa365586dd5329f8e8997596024427e3a265d63809109f8e899750e024427e3a2653738))) else (if j<4 then (0x58380910cdc6a56560c02443371a565b8540d10cdc68d98594024433719865d6500910cdc661935940244337198641654c910cdc6615059543443371586416550d10cdc5439361954443371506538359510cdc261905957444337098641655c910cdc261505957444337098541655c910cbce9998419434432f3985817458d10cbca6160595744432f298581655c910cbca616058d724432f26941984dd510cbc9a506613734432f268641655d110cbc66160595434432f1606538359510cbc26160595744432f098581655c910cbc2616058d72443277985957458d10c9de616558d724432766959584dcd10c9d66165dcd624432759859573d8910c9d66156dd562443275975978258d10c9d5a565e0d724431eb92e418758d20c7ae4b9061d434831d793e458750d10c6d9239750d724431b648e45435c910c3d2616759572442fc3a649d304c910bf0e8d2740d62442fc1a68df204c910bf069237c8132442fc1a3c837358910bf068a3740d62442fc1a28dd0350910be8e919649c02442f93a651d3050d10be4e91964c143442f93a361d4050d10be4e8d4799103442f93a351d6440d10be46923799103442f91a48dd6440d10be468d0651543442f63a36496580910bd8e899759602442f63a26518059510bd8e819259532442f62a76496580910bd86a72059532442f61a989d6580910bd868b9759602442f61a2e4d6580910bd868a5741562442f61a225d6580910bd829d9259602442f53a365d6580910bd4e8d9759402442f53a364165dcd10bd4e8d87a0165442f53a361e6059510bd4e8d8794165442f53a361d8059510bd4e8d8754165442f52a325d6580910bd46a53059532442f51a325d6580910bd46839359773442f50a365d6580910bcc6954059543442f31a495d0559110bcc6909759602442ee3a649d064c910bb8e8d2758162442ee3a259d6580910bb4e99944c163442ed3a361d6059510bb469a3759103442ed1a64c16550d10bb269923419214c2eb3a651d0650d10bace8d4758164442e73a564d6059510b9ce919059563442e73a36416558910b9ce8d8758165442e73a359d6580910b9ce898758165442e73a259d5059510b9ce819259563442e71a8a1d6059510b9c69a9759602442e71a6a1d8059510b9c69a5741564442e71a55815458d10b9c6928758165442e71a495d6059510b9c68a8758165442e71a295d6059510b9c6888758165442e71a0e5d6558910b9c6839359562442e70a959d6580910b9c29d9059562442e67a349d6558910b99e899759562442e66a949d6558910b9969f9259562442e65a649d654c910b9968a9759562442e65a225d6558910b992a52759562442e57a365d65d8d10b95e8d9759762442e57a365d6558d10b95e8d9759562442e57a36496558d10b95e8d8758165442e57a359d6) else (if j<5 then (0x4c1764c910df064930459324437a1925037350910de4e919341943443793935016550d10de465d30d1943443791944dd0650d10de46513641543443791944c17650d10de465130595434437919351e6440d10de464d474194344379193502645cd10de464d405d94344379137e594050d10de44dd90d1943443763a06488759510dd86552741952443761954850654910dd8649905957244376192641654c910dd4e4d9059773443753935416550d10dd464d905957344375193641654c910dcce5d40559544437339455d0655110dcce515141954443733945417655110dcc65d50919544437319551d0655110dcc655405d954443731945416550d10dcc55d9091954443731546416550d10db865927415624436e1964850558910db864960dd5624436e1925837358910db4e4d60595434436d19359f6440d10db464d60d91734436d1636416550d10dac65940dd5644436b1945837559110dac6516059543443673975956380910d9ce416560963443672976416558910d9c6a56540d624436719865d6059510d9c65d6558e024436719695d0558910d9c65987a016544367190e4d6558910d9c6419359562443671906496558d10d9c6416558d7244367187e4d6059510d9c5a565dce0244367167e518059510d9c59f9360165443671676576440d10d9c58195d9173443671566415458d10d9c25d9059562443665a66488759510d9964965dcd624436655664b7558910d95e4d97595634435d3935d97440d10d5ce5e975960244357297641655c910d5c9e657596024435727995d6541110d5c95d90595724435699549d0654910d5565f93597734435559764d655cd10d3a65927415624434e9925837358910d3559d93d91734434b576e4d4759110d1de5e975956244347797595635c910d1d59d95d917344346d5664b7558910cf8e8998419544433e398c817654910cf8e63205d9324433e398c81744c910cf8e619649c024433e3986512700910cf8e4b805d1324433e1a8e497480910cf869b9849c024433e1a4e612700910cf4e61305d9434433d3984c1764c910cf4e61305d1634433d3984c1744c910cf4e4f805d9324433d393e01744c910cf4a613058d724433d2984c1435c910cf466130595434433d13865b7380910cf44e194dce024433d0984c1635c910cf42613050d724433b3a96034650d10cece9198419434433b3985017655110cece61405d9434433b3946017655110ceca614050d724433b248641435c910cec66140595434433b1946016550d10cec50393619544433b098501435c910cdce959841953443373a56610550d10cdce61505d954443373985417654910cdca61905957444337298641655c910cdca61505957444337298541655c910cdc961965510344337258641655d110cdc9619059572443371a959) else (0x985956380910e9c6616558c02443a71985950694d10e9c6616541953443a719858165dd110e9c6616059773443a719858165dc910e9c6616059573443a7198581655c910e9c6616059532443a7197e016558910e9c65d8059763443a719760165d8910e9c65d8059563443a719758185d9110e9c65d6061763443a719758185d8910e9c61d9059763443a718764165d8910e9c61d9059563443a71876416558910e9c61d6540f62443a71875950358910e9c61d6059532443a71805958258d10e9c601655d163443a718059573d8910e9c5a39759602443a7168e4d6580910e9c5a29759602443a716895d6580910e9c5a19759602443a716865d6500910e9c5a19541953443a716864d6580910e9c5a19359402443a716864165dd110e9c5a19059773443a716864165dc910e9c5a19059532443a71685977380910e9c5a1655ce02443a716855d6580910e9c5a15741954443a71685417655110e9c5a09759602443a7167e01654c910e9c59d9061764443a716764185d8d10e9c59d6560e02443a71675438459510e9c597805d952443a716561d0655110e9c5958741952443a71656050654910e9c595805d954443a716061573d8910e9c58165e0d74443a7160597835c910e9c5816561373443a716059582dcd10e9c5616759602443a715859d05d9110e9c561605d764443a715858175d8910e9c5616059543443a71575838459510e9c55b80dd562443a7156e017558910e9c5598741762443a715661d0558910e9c5598141562443a715660175d8910e9c5598055163443a71096016558d10e9c2616059574443a7098581655c910e9c25f8059562443a656849d654c910e995898759532443a556361d654c910e954e1655cf62443a37a461d6558910e78ea1725d8024439e3a85c97400910e78e61725d0024439d373e01764c910e748e17640d724439d1385db7380910e6a521274113244397179a1d6580910e5c5e68759402443969275418654910e3a5a127419524438e96849d064c910e3a58987419324438d96361d064c910e355e1635d9434438d57858d764c910e355d937e11634438d5685cd7650d10e3558d87459324438d563605764c910e2d5e1645d9434438b5685d17655110e2d5a1745d9434438b54859d64dcd10e1de6167597744438779859d65dc910e1de6167595744438779859d655c910e1d5e1655cf624438757661d654c910e1d59d65e0d7444387567597835c910e1d59d65613734438756759582dcd10e1d26167595744438749859d655c910df0e8993419324437c3a264d044c910df0e4f205d9324437c393c81744c910df0e49305d1324437c237e41264c910df08dd96c81324437c237642244c910df065d30891324437c19349d064c910df064d27411324437c193485064c910df064d21411324437c192)))) else (if j<9 then (if j<7 then (0x7167595035c910f1c59d5059574443c7167541655c910f1c5855059572443c7157581655c910f1c5456059572443c707959d6580910f1a5952741952443c695649d0558910f19de52759562443c657949d6558910f195d92759532443c6567649655c910f19595725d952443c656549d1654910f19595215d952443c65565cb7558910f19559725d562443c655649d1558910f1955921dd562443c65564857558910f155e53759563443c55768dd654c910f155d93759563443c35655d17655110ef08df8049932443bc1a649d8300910ef06912760c02443bc1274c1864c910ef049d3061132443bc1214c1864c910ef04853061132443ba1a949d8400910ee86992761002443ba14849d044c910ee85212141132443b92484c1435c910ee465d4060e54443b91804d94550d10ee451d9060e54443b91474c38650d10ee451d3061943443b9143e01744c910ee450d8741132443b9143605044c910ee44e14750e02443b913850173d0910ee44dd40e1943443b91375018650d10ed8ea12759402443b61a649d8500910ed86912761402443b61a25958380910ed86632059532443b619849d6500910ed864b8059532443b61275418654910ed84855061952443b5238595035c910ed48df8059532443b51a95958300910ed469d6560c02443b51a35958380910ed468d6560c02443b51984c1654c910ed464f8059532443b51584c16550d10ed44e165dce02443b33a56014550d10ecc69d6561002443b31a35958400910ecc5614059543443b31575018655110ecc5518059543443b31475418655110eb86a52761802443ae1a449d8600910eb85a12741952443ae16849d064c910eb85a12141952443ae168485064c910eb85898741932443ae162605064c910eb4e99804d943443ad1684dd0650d10eb45a1305d943443ad1674c38458d10eb458f805d932443ad16361d0650d10eb458d8741932443ad163605064c910eb458d805d943443ad1636016550d10eb44e16758e02443ad13858173d8910eb44dd60e1163443ab3a66014650d10eac5a14741954443ab16851d0650d10eac5a1405d954443ab1685017650d10eac5a14059373443ab16461d0650d10eac591805d943443ab14858164dcd10e9ce958059563443a73a26016558d10e9ce816859532443a739858165dd110e9ce616059772443a7398581655d110e9ce616059572443a7397e016558910e9ce039359562443a738064d6558910e9ce0165dcd62443a73805957358910e9ca616059574443a7298581655c910e9ca5f8059562443a7268641655d110e9c9a15059574443a7258581655d110e9c9616059572443a71a85956380910e9c6a16558c02443a71a76558600910e9c69d8059563443a71a36558600910e9c6898059563443a719859d6580910e9c6616759402443a71) else (if j<8 then (0x3f4237c81654c910fd064f2059532443f41924c1654c910fd049d3059532443f11544d90550d10fc45513059543443ec163c81764c910fb058d2741932443ec163485064c910fb058a3741932443e91644dd0650d10fa4591305d943443e916351d0650d10fa458d405d943443e91635016550d10fa458d0651543443e6397c816558910f98c839359562443e632064d6558910f98c8165dcd62443e63205957358910f98a5f2059562443e61a649d6500910f986896558e02443e6197c816558910f986496759602443e61925956380910f986496059572443e6192581654c910f9859f2059532443e6165c817654910f985952741952443e61654850654910f985899059532443e6156c837558910f9855b205d562443e615649d0558910f985592141562443e61276416558910f9849d6540d62443e6127581654c910f9825f2059562443e53a361d6059510f94e8d6558e02443e539358165dcd10f948dd6540d62443e5237581654c910f946a13059563443e51a35950358910f946816359532443e51974c16558d10f9464d6059573443e5193581654c910f9461d3059563443e51674c1654c910f9458d9059532443e51635416550d10f945593055163443e51376416558d10f944dd8059563443e51375956380910f944dd6059563443e51305958258d10f944c1655d163443e5130595635c910f944253059563443e50a361d6059510f9164d6259532443e4563649654c910f9158d2759532443e45628dd654c910f8cd915741954443e33645417655110f8c5954741954443e31655017655110f8c5594055163443e31545816550d10f855516359543443dc373c81764c910f705c9305d932443dc1724c1744c910f70485305d932443d91744c17650d10f645cd405d943443d91474c1435c910f6250d2741132443d85435c9744c910f6150d2745132443d8543485744c910f58dd52741562443d617989d6580910f585e52759402443d61725417654910f5849d5045952443d31745417655110f385c960dd562443ce1725817558910f3849d6045562443cd1794dd6058d10f345da3759103443cd1764dd8058d10f345d93758e02443cd1764dd0458d10f345d9305d163443cd1674c1635c910f3459d3058d12443cc96349d064c910f3258a3741932443cc5635c9764c910f3158d2745932443cc563485764c910f2c5d94759103443cb17651d0559110f2c59d4059373443cb167501645cd10f255d1635d943443c95645cd7650d10f1ca5d6059572443c727959d6580910f1c95d6059572443c719758165dcd10f1c65d6059772443c7197581655cd10f1c65d6059572443c716764165dd110f1c59d9059773443c716764165dc910f1c59d9059574443c7167641655cd10f1c59d9059572443c71675977380910f1c59d655ce02443c) else (0x70cadd15b12b445664ac515812af055bcab615692acc558cab015572a9054fca9e15392a6c54cca98152d2a545484a8f150f2a0053c4a7414e529b85334a6214b52958528ca50149d2934525ca4a1491291c522ca44147f28f851e4a3b147328e051b4a35146728c85184a2f145b28a45124a201437286850aca11141928205034a051407280850049ff13fb27f04fd49f613e327c04f449e713cb27844ee49db13b327604e849cf139b27304e549c61389270c4e0c9bd137726d04d649ab135326944d04999132326344c5c98a130525ec4bcc97812ed25bc4b3c96612bd25504a94951129925144a0493c126f24d849a4930125d24b4495c927124b248448e491b1233246048b491512272448488490f121b2424480c8fd11f123d047948f111d3238846ec8d911af235846a48d311a3234046748cd1197232846448c7118b231046148c1117f22f845e48bb117322e045b48b2115b228c44f489d1137226844c4897112b2244447c88b11132214440487c10ef21cc438c87010dd21b4435c86a10d1219c431486110b9216c42cc85510a1213042548461083210041f483d107720e841c4837106b20d04194831105f20b8416482b105320a0413482510472088410481f102f205840a481310232034405c80a100b20043ffc7fe0ff31fc83f547e30fbd1f743edc7da0fb11f5c3eac7d40fa51f443e647c80f8d1f143e1c7c20f811efc3dec7bc0f751ee43dbc7b60f691ecc3d8c7b00f5d1ea83d447a70f451e843cfc79e0f391e6c3ccc7980f2d1e3c3c6c78c0f151e243c3c7860f091e0c3c0c7800efd1df43bdc77a0ef11ddc3bac7740ee51dc43b7c76e0ed91dac3b4c7680ecd1d943aec75c0eaf1d583aa47530e9d1d343a5c74a0e911d1c3a1473e0e731ce039b47350e671cc8396c7290e491c8038f471d0e371c6838c47170e2b1c5038947110e1f1c38386470b0e131c2038347050e071c0838046ff0dfb1bf037d46f90def1bcc378c6f00ddd1bb4375c6ea0dd11b9c372c6e40dc51b8436fc6de0db91b6c36cc6cc0d651a8834a468d0ce7196832346420c7b18c030b46060bfd17e82f045c70b7916b02d3c58e0b0715f02b8c5580aa1150c293450d0a111404279c4e0098d12b4249c47a08c1111c216c41408130ff01f5c3de079b0f181dac3ab07230e281c2c37206b10d3819d433006450c54183c2ee05d30b70168c2cd05850ad415842a3052b0a1413a426704cb098412cc255048f08d0117c22b04470864107420403e707bc0f241dd039306d80d14198031b05c40b1c156029d051c09cc135024f048c08f4114020d03f0078c0e401bf031805dc0ba017102d0054c0a20135024c047408700f901c802c403f006f00cc012c0210039006000540003f83428dd044c910fe050f205d132443f814349d044c910fe050d214113244))) else (if j<11 then (if j<10 then (0x4c58285c03822021820880222008880216c15e238218205b08e0860736e26cd4d7c9ad535926a94d409a2d34126794ce0999d33226554ca4992532326434c6898c531726254c44986530b26134c0897ed2f625e94bc0975d2e425bf4b7896cd2d5259b4b30963d2c625894b0095c52b1254d4a7c94ed29c25354a4c947528724ff49d4938526924c94968927d248248d490891ed239246948a8912d22424394860908520c240f47f48fdd1fa23e547b88f351e223b547648e751c4237f46f88dcd1b5236146a48d0d19a233146448c4d185230745fc8bd517622e945c08b7516a22cb45848afd15e22b9456c8ab5152229b45248a3d1462289450c8a0d140227d44f489dd137226544b8894d1252241447088bd113221d4428882d10121f943e087b50f221e143bc876d0ec21d54398870d0dd21b1435c86ad0d421a54344867d0ce2193432086350c2218142e485a50ad214b428484cd095211b4218840d08020f741e883c507720e541ac82ed05920a34128822d03e206d40bc81550262043406880ad00e2013402080350021ff53fd87f8cfea1fcb3f847efcfde1fad3f487e6cfc91f893f007dc4fb41f593e947d04f9c1f2f3e587ca4f901f173e287c2cf811ef93dec7bccf751ee13db07b54f691ec93d807adcf571ea53d387a4cf451e873cf079a4f331e573c9c792cf241e3f3c7878ccf181e2d3c54789cf0f1e153c24783cf031df13bc47764ee81dc73b7c76a4ed01d913b1c762cebb1d673ac8756cea61d3d3a5c747ce881d0139f073bce731cd7399072fce581ca13924723ce431c7738e871c4e341c6538c4714ce221c3b387070d4e161c233828702ce011bff37ec6fb4df21bcf378c6edcdd41b9f37386e64dc81b8136fc6dd4db91b6336a86d14da11b3f36786cccd951b2736486c84d8c1b15360c6c0cd7d1af735d06b94d681abb35646aa4d501a97351069ccd2f1a5534a4693cd261a43346868acd141a1f342c684cd081a0d3414681ccff19fb33f067bccf619e933cc678ccf019d733a86744ce719cb33906714cde19b9336c66cccd819ad3354669ccd219a1333c6654cc3197132c4654cca21941326464bcc8d191732286444c841905320463fcc7818e731c86384c6f18cf318c62f4c5d18b7315c6294c4e1899312c624cc48188d30fc61bcc33186330c0615cc27183f3060609cc12181b3030603cc0317fd2fe85f94bf117d92f885f04bdf17af2f4c5e74bca17912f045de4bb517612eb05d54ba617492e8c5cf4b9a17252e445c7cb8e17192e2c5c4cb88170d2e145c1cb8217012dfc5becb7916ef2dd85b8cb7016dd2db45b2cb6116bf2d6c5a84b49168f2d0c5a0cb3d16772ce859c4b37166b2cd0597cb2b164d2c8858ecb1c16352c6458bcb1616232c405844b0115f32bc85784aec15d52ba4573cae615c92b8c5) else (0x173116100000001e0200103e0c18820008620a1aa458486e862121bc1184c340800000000000015040d4102000000000000000000000000028a8200104a080000000000021ba138400000000000000000000000000000000000000000104b04610085408000104a08000000104a0d41035040800000008540b0182c060b0182000000000000000000000000000000000000000041182000000000000000000000000005b1489075410806e06095e424b16c08406d04405b0579081065410a080868421c0021071060506905d82882181c81900e904441a41760a208607206403a411046093282081c60ec06301082042085b057948d410886885c420c1c41880e504c00401b897148901b410a81ca0612070306905d82882181c81900e904402081a2082071c59c4c03e411006e41d406181b8592579095018a424082081a2082061c59c4c03e411006e523406181b9070416c922d04181a2082074c5cc4903b4130010517806101b8592092818808206982882081831671300f904482081a50a4084072c4903d411081c09182070417a82481c818205e85c859702701f410c07f06905c02181c01980e904401fc1a40a008607006603a411007f06905c02181c01980e904401fa1a20a0083070063039411007f06902802141c01940e504401fc1a417008607006603a411007f06902802141c01940e504401fa1a21700830700630394110176220218185b1081060850806805c42041950428208200880860817a17606e406d04285d9070513302501d018c0e281a4074818686885cc28420c1c41880e50442074038441c0810a0bb08642b81b800c08206842041931731280ed04405b057a488608206805c82081cd0432092074038605c824517806205e9091071060806805c81ca06202081a01760a408407203e411081c085ea092072060806e824a061c070208016cd04185b05790954108220085b0579489410816c420419504205b057c171489410a17622021981580e285e81b901d4108040e0217681c10880206e06041d406201b8971091072c5d018c516094582517206101a1071818606841c606181a1071818617622021981580e28208217241d814185e8880417617216452241d814305d85c8591489076050c17617216452241e41c30108075458646004201c1a1a21730a1083071062039413001217622021980e205d8880866038831631010c58c40417622021980e205b02068420418d0421070241c081b9093018605c41c916606201b948d018616c420418181a1081065410841c082081a4084072c5ac4903d411006e41d40618004070216c15e424185c9080442021411080850441c09072038417241c20e185d8882038607e86885c020c1c018c0e504401fa1a20a008307006303941113173101)) else (if j<12 then (0x121a0578412c084e8214809062038403c090e101844060800010820388201010820420852501840420856020000388201010821580c4582910090e0286815e104b030390061408401850060c01830200800245830200800200a45828600800245820200944820010380c08025100c08023160a458217208c58204171818515ec0610041940614458200042408082408000004838320e080014e8208281c40e180e20804080081082060089e0208241880e18578205d312100000e108445860384181008440c1ba0f84949406108e50184844420105ea0f84238420105e82420085e82420814105da0504420081bd0184080414101b91884028182173834100014882001038d04100e1080500e0800106024180906483844240a4882040e0291609440296c95ed0419080217681411082050482008002458286043e100510080469834120930184269834100000512094482000008e02021528384008e02002088384041bc185018716d15f4061d02024260909828260c18a458407e85c504181fa0a14106018080001006080e108040380810380c018200000004080200111608000000111608000000002060200000000000000042008084018402e0210061d0240185409006101bc0804008610184005c8564440600004080200001080c28511608000080f0061401824060800056024200909020000000445a03840465101245820010060c018221840610861018417208031208111009458320e0a080315ea06101806088640520386000038220105d8217a098182011108804080082091404220082002009382000c080d0202078420100000000000000000000020802000a0608000046815e104b02001f8246815f400184b50004050182050182000000000d040c0803020080a02068080000001046080172916140bc0804082042101381084050182000000000005202042082081084042080e108040420d01830460800000010380c0e48384068080000000001046081039116141840e05061020160d02060d0246e462101982463054101982462080000000000001904080000000000000000044e830380e038203c08013a080e0293a0a4e8200000000000006038380e08004340610001080204e08000002500610000002458200002038201095018503822010006038223c080e0880408041810860200086aa28121a11404000021830184424c06101061406110950250186000078081b81884c080b0203406080041e02000048502001e02a14080000000000000010802025006110602c000b000200015e122104b048854000d0002000000000000000000000000000000000040e020380906483d0186082080000000044e82045202005202038080e0293a0a4e82000000000000310080176080005d82a0e0a838202838320e08000000000) else (0x21504100b80805408080042080f024244204061a4402910080802020080024806100172080001a48384000522080922080021a0578453a088e54104005782406080f1090442008080e0d020217a424100238080010182824c0811091080516d15f5041c0e08804000010950184600085e89084164c06121e08e1080642009095018481409082855018617a4254061c44483840108028140a08031120859457a818617208041c20e140e0242540611090340809093023018600011680e11440231020e108382910a0e100424020406190900810186a140801720d0183408080850185009406100850184000e108040384201101820144024060901820244820105020200808020000000240808030080808020000000000000108024200908034060906024180906029160908034060a06028200e01831100d01820501820000000501834060d0183406080000000000420080014402021a0578412c090810184420406110182420406104b0286815e14084018500608013208000042008085018404682e021806260182020d0410881428442009084458485c504)))))
def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1e00f007800074886f0078020e9e0054ff800a5ddadf00231fc01e654507803c0001af007802037e003c0142d99357a5497803c01e00f0028ba4dde00f007802116c7ec1ec23a847e00c5678034aafaef007803c01e00f5822ca8e1e00e8108004a6eb6e6bf36b46b71ef0014ffc00059da6f80111e01950978016eced834e233ad53e00e347803c01e000ac518b00be0060be8c3c008693307803c01e00b4c68d094e02f5035e59327e00f00780013de7cf007801c1ba4304ef803c01e00f007803c01c4aa054347c01e00f15bb82db2e42f0015f29a7c21f004853cbfe00e2be18715be0022202ebc01e00b9240ed481e00aa5f8004596dcf4b1c845482caf007803c01e00d3c7803319e00c28f803c01e00761137bc01cc6f002377c00e90b62780058a495f0028a5ca9e00f0049c6c99c75f007803c00420e4131a982c81115ff5ab50fe00d00f8022f7a6cf007803c01a85744f801d1869a835a2d7c01fa952b2178246db5d61f803c0165ae24a827c01e00a1e7803a3e20356ff80356fe00f0068b495061fa6a61dbc01e00f004833c0161d355f23707e27213d0a2bc0145cf004670767450f001a9988e7c0ee5f03e503ab9f007919d9064bf007803c01e00e5dd921c9e1db40764e7937c9432c0387866b1df3be2aa4ffa8082291b7f8c781b9ef8011ad5797577a0d451815cc7a4404834bed039266438e2a8ecad5e1c4a22f1c35a4405ecbec219cc2fb0dba5e414a44e0a3a48b99c963e0035ed139bbacd2f007c33021e005b5f80154b378f007b349ab5010d90813c01a13f1252d304dfaf167e733c01e00f007803c01864f007803c006c1e1ba303c01e00d0c5abdccde39ed803313befb6d5c682e509e00f007803c0171292e89bc87de0043cb937865e7b904780212e41ef00780386dea2f00696d911e00950f803c01e00612eb4036ec31f0026fbc00bca231f800d67e00f00524dcfbe001c40202001811206108010000083a28412d0c0420400a41100808181000420a0cd8503000878e082c0080402008003410108007000408104001001c0600382)
def genData7 (j : Nat) : Nat := if 30 ≤ j then 0 else (if j<15 then (if j<7 then (if j<3 then (if j<1 then (0x26440d109f8cc4a881a213f198596024427e330b1c04884fc66163009109f8cc287012213f19850c024427e330982c6884fc6613050d109f8cc20d992213f19841a734427e330834a6884fc6610690d109f8cc20caa2213f198419534427e33083286884fc66105d91109f8cc20bb1a213f198417624427e33082a86884fc66104cc9109f8cc20939a213f198412634427e330824a6884fc66103d89109f8cc207a12213f198191034427e32dc2a06884fc65b8440d109f8cb700a92213f196e01324427e32d43c04884fc65a87009109f8cb50109a213f196a00734427e32c43a06884fc65784419109f8caf06832213f195e01624427e329c3206884fc6538540d109f8ca700992213f194a1e024427e32943804884fc6528084d109f8ca50039a213f194a00134427e32843a06884fc64f86411109f8c9f0a832213f193e15044427e327c220c884fc64f80589109f8c9f00a12213f193a03644427e327404c8884fc64e80591109f8c9d00322213f191600315027e321c3aca884fc6438758d109f8c870ea1a213f190e19434427e321c2ac6884fc6438550d109f8c8708b2a213f190e11634427e321c1aca884fc64382595109f8c8704b1a213f190e09434427e321436ea884fc64286dcd109f8c850d29a213f190a19754427e321432e6884fc6428654d109f8c850c39a213f190a13734427e321422e6884fc642841cd109f8c8507b22213f190a0e644427e32141ac8884fc64283191109f2c9507322213e592a0d644427af26c3aca884ede5187589109bbcc2ca39a213779561d324426ed312baca884dd661651cd109bacb50a39a2137595a1b734426eb2b434e6884dd656865cd109bacad0ca9a2137595a18734426eb2b424e6884dd6568484d109bacad08b9a2137595a111344267b2b42662a0477e4d87595108dfca30eb122117f9561d32443cc640b2ac4887944c16558d10de09830521a21bc12760c024437424ec2004886e45018395110dc89830999221b8943600244cb70a86c0848996d849d8500910da8b2b0601221b31656100244366280c2e86886b849d8600910d39c02cab1221a7195618024434e300b2ec68869c60165d8910d38c02cab1a21a7168596024434e2d0b28048869c58185d9110d38b030bb1a21a716061762442f83241ba06885e86484741110bc8ca06e81a217919311d04442ea32a1ba06885cc6544741110b70c90ce832216d1960dd03442da32633a0c885ac6584741110b58ca0ce832216739358165442ce32d402ca8859c65a6059510b38ca8ce8322143d96a1674cca7c73093804884f8a4a87415109f14950e822213e292a1d034426e330b28048849d65a85d0f1093acb50ba1a211e597a0a43c420fb2d42ce99941f65a859d33183ecb50b3a66107d96a16744ca0fb2d42ce898c1f65a859d130) else (if j<2 then (0x6885f4a4e6440d10be949ac881a217d29319103442fa32d1ba06885f46583740d10be8ca46e81a217d1940dd03442fa327b2a06885f464f6440d10be8c9e0ca1a217d193c1563442fa32782a86885f464f0458d10be8c9d0c81a217d193a1103442fa3273b206885f464e7440d10be8c9cc881a217d19398163442fa3272a206885f464e4050d10be8c9c60b1a217d1938c143442fa3270b206885f464e1440d10be8c9a0d992217d19341a43442fa32683286885f464d064c910be8c9a09992217d19341132442fa32632206885f464a3740d10be8c8e0c9a2617d191c15344c2fa3219bac6885f46433750d10be8c866ca1a217b39650143442f672aa0286885ece517641110bd9ca20caa2217b19691d04442f632983286885ec6530550d10bd8ca50e822217b19490143442f632918286885ec6510650d10bd8ca20aa1a217b19291d04442f632383286a05ec6434750d10bd8c868ca1a217b190d1543442f6321232a8885dce557641510bb9ca300b2a217739360165442ee52bb2206885dca546440d10bb94810eb2a217719695d05442ee32bb2206885dc6568640d10bb8cad0881a21771959d905442ee32b3b206885dc6561641510bb8cac2c81a217719581903442ee32a832a8885dc6550654d10bb8caa0ca92217719519103442ee3292ba0a885dc64e8059510bb8c9cc0b2a217719394165442ee3252ba0a885dc25d8059510bb34910eb2a217659221d65442eaf26c3aca885d5e4d5694d10bab4990eb2a217559321d65442ea926c3aca885bce556058d10b79c9ac0b2a216f196c1563442de32d822c6885bc65a6058d10b78cb460b1a216f19641763442de32c82ec4885bc6590558d10b78cb20ab12216f19499d06442de32533a0c885bc6436759510b78c86ceb1a216f190d9563442db32d31a0c9859e6576341930b3b4b4aeb2a216759758165442ceb2d43aca8859d65a6558d10b3acaeceb1a2167595d8563442ceb2bb02c68857ca5c6440d10af8cb8c881a215f191c19744c2bcb25b82e8885676533758f20aceca66eb1a4147d969d5630828fb2bb3ac71051f6576758c209f9cc2ed012213f3985d8024427e730ba404884fce6174009109f9cc20d39a213f39841a534427e73083426884fce610654d109f9cc20c39a213f398412734427e73082426884fce61041cd109f9cc20809a213f396601434427e72ac02c6884fce558050d109f9ca300b2a213f394601634427e726c02ca884fce4186549109f9c830c992213f390611324427e531b2206884fca626440d109f94c2c881a213f298191034427e52fc02c4884fca5f80509109f94bb0d012213f297612024427e331b2a06884fc6636440d109f8cc60ca1a213f198c15634427e33182a86884fc6630458d109f8cc4ec82a213f1989d9034427e3313a206884fc66) else (0xe30a81ec4886dc6026558d10db8c04caa1a21b7180597324436e300b2cc6886dc6015694d10db8c02acaa221b7180559534436e300aa4a6886dc5d98500910db8b2b0701221b716560c024436e2b0b2c04886dc56105d9110db8ac20bb1a21b7158417624436e2b082a86886dc5438459510db8a8706b2a21b7150e09654436e2a0c32a8886dc5418654d10db8a830ca9221b7130617634436e260c2e86886dc41a851cd10db88330a39a21b7087601654436cacb410e6886d9595821cd10dacc1aa0aa261b39406174344366acb420e6886cd59584cc910d9ab2b0839a21b35476174344366a82c2e86886bce016558910d79b420d39a21af36841a534435e6d0832a6886bcda1061cd10d7943ac1b2221af287583624435e50eb02c8886bca1d6058910d794320839a21af286410134435e4d0832e8886bc9a1065c910d78c9b0c01221af190a18734435e320c30e6886bc6197400910d78c328601221af186410734435e30c82026886bc6036558d10d78c02cbb1a21af180597624435e300b2ac6886bc5a17600910d78b42cb01221af16858c024435e2d083664886bc5a1069cd10d78b420d29a21af16841a434435e2d083426886bc5a10680d10d78b420caa221af168419534435e2d0832a4886bc5a10650d10d78b420c99221af168418734435e2c1c2ac6886bc5838459510d78b0708b1a21af160e0d654435e2c1c12ca886bc5838258d10d78b030bb2221af160617634435e2c0c2ec4886bc58183d9510d78b0307b2221af16060f624435d304b02c6906b660d60d8930d6cc1ac0b1261ad96841b354c35b2d083668986b65a106cc930d6cb1f0283261ad963603614c34f2c0c2ec49869de1d6558d10d3bc02cab1a21a7768597734434eed0b2ce68869dda1655cd10d3bb42ca39a21a776855a534434ecd0b2ae88869d656861cd10d3acab0c39a21a7587597634434eb0eb2ec48869d61d6558d10d3ac3acab1221a7580595634434ead0b2ee88869d5a165dcd10d3ab42cbb9221a7568597324434ead0b2ce68869d5a1654c910d3ab42ca39a21a756855a534434eacec2ec88869d59d85d8d10d3ab2f04b1a21a756560f624434e930b2ac68869758d85d8530d2eb1b0b032619f3785da024433e6f0bb0048867cde17480910cf9bc2e8012219f28741a134433e32cc04e31967c651809c632ccebb3099926199d4760e544432ef0f43aca8865d9e25759510cbb2bf02b2a2193d47617434430fb0ac1cec1061f615835d820bf1c92ed012217e3925d202442fc72093264885f8a4b705d110bf1490c881a217e196c8132442fc32d13c04885f86522780910bf0c9e40b12217e192a1d04442fc32541a08885f864a0741110bf0c90c881a217e19089132442fa72c98286885f4e513058d10be9c9aec81a217d3935d103442fa527b220))) else (if j<5 then (if j<4 then (0x8d718839d2c4832e69073a49d6058910e6cb3a60b1c21cd9674c1634439b2c6836e89873658d06dc930e6cb1a0db8a61cd937581638839b26eb02c7087364dd6058d20e6c9bac0b1a21cd5764dd634439aace98ac6887354dd6158d10e5cb3a80b2221cb9475816444396aeca3ac88872d59d4159110e5aa3ac2b2221c7567597744438eaceb2ee68871d59d65dc910e3ab3acaba221c7567595734438eaceb2ae4886f8e612700910df1c024c99221be320619524437c640c3264886f8c81844c910df143e40b1221be287c81424437c280c1486886f849d8600910df093b0801221be106a08734437c20cc1486886f8419821cd10df08250439a21be104a08134437c208c10e6886f84118204d10de9c026c99221bd3804d1324437a47081ae4886f48df804c910de8cb30601221bd19460c024437a321418c8886f46418395110de8c830632221bd180cd9434437a3009b664886f46013690d10de8c026ca1a21bd1804d3324437a2ecc1804886f45d18300910de89c6e701221bd13858e024437a270b1804886f44e14380910de89c28601221bd13840f624437a27081e84886f44c38650d10de89870ab1a21bd130e15434437a261c22c6886f44c38258d10de898704a1a21bd13061b324437a260c34a6886f44c18690d10de89830ca9a21bd130619434437a260c3264886f44c18550d10de89830999221bd130612634437a260c24a6886f44c1844c910de4833059a261bc53660a4344376690824e6886ecd210484d10dd9a420839a21bb348410134437650ea0684886eca1d4099110dd943a80b2221bb2875014244376490822e4886ec64d8400910dd8c850839a21bb190a101344376320c2664886ec641841cd10dd8c830809a21bb18458c0244376301a3286886ec6034550d10dd8c028ca1a21bb18051543443762ecc2004886ec5217400910dd8a428601221bb1484133244376290824e6886ec5210498d10dd8a420929a21bb148412134437629082406886ec521044c910dd8a420839a21bb1484101344376281c3286886ec5038550d10dd8a0704a1a21bb1406195444376280c3286886ec5018550d10dd8a0307a1221bb14060e6444376280c1ca8886ec41a841cd10dd88330999221bb1066107344375304a0286906e65018395110dcc8330999261b954760e5444372a82c1ca8886e54d984cc910db9c02ca99221b7380559524436e50ec02ca886dca1d6580910db943aca01221b7285410734436e50a82026886dca01651cd10db92c2ca81a21b7258551034436e4b082ae8886dc961055c910db92bb00b2a21b7198596024436e330b2804886dc64185d9110db8c830bb1a21b7190617624436e320c2cec886dc6418585910db8c830b03221b71855d0024436e30ab1804886dc6154300910db8c2a0839a21b7185410134436) else (0x21f93414c143443f266ea0286887e4cc54050d10fc902260a1a21f91474c143443f228682664887e450d044c910fc8a0a60a1a21f9140cd943443f22809b286887e44dd4050d10fc898a80a1a21f9130d1943443f2261a2a86887e44c14650d10fc89828aa1a21f9104cc143443f220898286887e24c94050d20fc299282a1a43f632059532443ec640ab2a4887d889d6580910fb0c92cb01221f612759402443ec24ea82a4887d84855054910fa8984cab1a21f513099543443ea260b2e64887d44c1654c910fa8982ad29a21f513055953443ea260aa4a6887cc55d4055110f98aa20aa1a21f315150154443e62a1232a8887cc51d5055110f98a2a0929a21f314154154443e628132a86887cc5015655110f8ca1aa0aa261ee32059562443dc2c483264887b849d6058910f7090ac0b1221ed3674c163443da6c2982c6887b4cdd6058d10f6998ac0b1a21ed2064c163443da2ce982c6887b458d06cc910f68b1a0d21a21ed16341943443da2c683264887b45853058d10f689bac0b1a21ed13158163443da261b2ac6887b44c16558d10f6883660b1a21ed1064c163c43da20c982c6887b24c96058d20f6491ac0b1261eb36499103443d66c8832a8887ac59d4059110f58b220ca1a21eb16150164443d628eb02c8887ac5056059110f39b3b00b2a21e736754165443ce6c2a82ca8879ca4d6059510f39482cab1a21e728758165443ce500b2ac68879c9816558d10f392bac0b2a21e723059563443ce410b02ca8879c65d6059510f38c9ac0b2a21e719059763443ce320b2ec48879c6416558d10f38c82cab1221e718758165443ce300b2ac68879c59e6059510f38b3ca0b2a21e716760165443ce2ceb2c048879c59d6500910f38b3aa0b2a21e716558e02443ce2cab18048879c5950694d10f38b2a0caa221e716541953443ce2ca832a48879c59503d8910f38b2a06b1221e716154165443ce2c132ac68879c58165dd110f38b02cbb9a21e716059772443ce2c0b2e648879c581659cd10f38b02cb31a21e716059574443ce2c0b2ae68879c581655c910f38b02cab1a21e716059532443ce2c0b28e68879c55d6059510f38ab60ab1a21e715641763443ce2ac82ec48879c5590558d10f38ab20ab1221e715158165443ce260b2ac68879c21d6059510f33c92cab1221e656259532443cca4eb2ac488795e4d6558d10f2b9bacab1a21e573059563443caac6b2e648879558d654c910f2a9bacab1a21e553059563443ca926b2ac688778dc97680910ef1b92e901221de1725d802443bc2e4ba00488774dcd7640d10ee9b9a0d39a21dd37341273443ba46e834268876cdd17641110ed923a08b9221db14050d71883b524ea02848876951d045cb10eb92ba0ab9221d692754152443aaee6b2ce68873c99d065d110e7933a0cb9221cf1605)) else (if j<6 then (0xc930eb2a213f79261d634427ef24c3a86884fde4984dcd109fbc8b0ca92213f791619324427ef22c2264884fda61655d1109fb4c2cab92213f69858d724427ed30a1ae4884fd66375591109facc6eab12213f598dcf424427eb31b9ac4884fd66373509109facc6c8b9a213f598993734427eb31322e6884fd66176551109facc2eca92213f5985d9434427eb30bb264884fd66175d91109facc2ebb12213f5985d1324427eb30b9ec4884fd66173d09109facc2caa1a213f598593734427eb308b2a4884fd661164c9109facc228992213f598191734427eb2fc3286884fd65f84595109facbf08b1a213f597e09654427eb2fc12c6884fd65f8250d109facb70aba2213f596e15724427eb2dc1ae8884fd65b835c9109facaf0cba2213f595e19724427eb2bc22ec884fd657825d9109faca70eb2a213f594e15764427eb29c1aec884fd653835c9109faca706b2a213f594e05654427eb27c32e8884fd64f865c9109fac9f08bb2213f593e11724427eb27c12ec884fd64f825d1109fac970eb2a213f592e1d634427eb25c3a86884fd64b855d9109fac9706bb2213f592e0d744427eb25c0aca884fd64b8158d109fac9702a1a213f590e05434867e930b2ae8884fd261655c9109fa4c2c6b92213f49850d724427db25c0ac6904fb64b8150d209efc9b0ea8ac13bf9461d624423ff30bb2a88847fe6176549108ffcc2ec992211ff985d9214c23ff30ba2648847fe6174485308ffcbb0ca92211ff97619324423ff2ec22648847fe5987551308ffcb30eaa2211ff9661d524423ff2cc3a648847fe5984dd5328ffcb309baa611ff96613754423ff2ac3ac88847fe5587589108ffca30e992211ff9461b754ca3ff28c36ea9847fe4d87589108ffc9b0ea12211ff93607725023ff24c3aca8847fe498758d108ffc930ea1a211ff92613734423ff22c3ac69047fe458750d208ffc8b07b92c11ff9160f725023ff20c3a8690c7fa61655c9108ff4c2c6b92211fe9850d724423fb31baac88847f66375589108fecc6e6b12211fd98dcd424423fb31b92a2b047f663724c5608fecc6e498a811fd985d9524423fb30bb2648847f661744c9108fecbf02b1a411fd97e05434823fb2dc2ae89847f65b855d1108fecb70ab92211fd96e0d724423fb2bc32e89847f657865d1108fecaf0cb92211fd95e11764423fb2bc12ec8847f653855d9108feca706b92211fd93e19724423fb27c22e48847f64f825d9108fec9f04ba2211fd92e15764423fb25c1aec8847f64b835d1108fec9702bb2611fd92e05744c23fb23c12ec9847f647825d1308fec8f00ba2651fd90e05744cbf86409b264887f0c81344c910fe11be4099221fc13089132443f826093264887f049d304c910fe090a6099221fa34241132443f424ea0284887e84854050910fc9a3a60a1a) else (0x5d110bf8c82cab92217f19059543442fe320b2a24885fc64164dcd10bf8c82c8b9a217f19059153442fe320b1ae4885fc6416344910bf8c82a8b1a217f19050d72442fe320a1a24885fc640645cd10bf3cb24e992217e79349d62442fcf24ba2e4885f9e49744c910bf3c92e8892217e69219173442fcb2f12264885f964b7558910bf2c96e6b12217e592dcd42442fcb24bb264885f9649164c910bf2c90c8b9a217db90609344c2fb32683264885f664d044c910bebc9b0eb2a217d79361576442faf26bb264885f5e4d744c910bebc9acaa1a217d79351d43442fab2d1ba64885f5652374c910beac9ec8b9a217d59399173442fab26bb286885f564c645cd10be7c93009a2657cd924d9214c2f9b249a242985eee510655110bddc8304a1a817b79651d43442f6f28c32e4885ede51825d910bdbca2ecaa2217b79351e64442f6f26a3ac8885ed65f4650d10bdacbc8caa2217b594dd564442f6b28bb286885ed6516550d10bd6c928690a8179f945d9344c2ef32a832a4885dde5d5655110bbbcab06b92217779361d65442eef24c3aca885dd65d8059510bbacaec8b9a21775955d954442eeb2a322e6885dd6528759510bbaca4aeb2a2177592a1d65442eeb252baca885dd6488759510b7ccb20ab12216f79259d65442deb2dbaac88857ee41825d130afcc82cab92215f79758d72442bef2ea1ae48857de55765c910afbcaaec892215f79160d76442bef22c1ae88857de457648530afbc8ae890a615f79158d72442bef22a1ae48857d65f645cd10afacbacab92215f59759512442beb2e322e68857d65b755c910afacb6ea892215f591dc931582beb22b2ae48857be59274c910af7c9a4eb12215ef9261172442bdf24c02e89957be497648530af7c92e8992215ef925d1214c2bdb2b13a42b057b64e2748560af6c9c4e90a815ed92dd562442bdb25b9ac48857b64b7350910af6c92ec992215ed9189d32502bbf26c2aec88577e4d815d130aefc9aec992215df935d132442bbb2d1ba6488577652374c910adfca30cba2615bf9461972442b7f28c12ec8856fe517655110adeca6eab222157f9560d72442afb2d2baa89853f65b75591109fdca300b2a213fb90619524427f720c3264884fee41844c9109fccaf08832213f7985d9544427ef30bb2a4884fde617650d109fbcc2ec992213f7985d1634427ef30ba264884fde61655d1109fbcc2cab92213f79858d724427ef30a1ae4884fde5d86551109fbcbb0ca92213f797619324427ef2ec2264884fde5987551109fbcb30ea92213f79661d434427ef2cc3a64884fde5984dd5109fbcb309b9a213f79561d644427ef2ac3ac4884fde5187595109fbca30eb1a213f79461d324427ef26c3e84884fde4d87991109fbc9b0eb22213f79361d624427ef26c3a84884fde4d86551109fb)))) else (if j<11 then (if j<9 then (if j<8 then (0x6ed51d8399110dcf1c286b8a81b9d3850d215036f2a0c32a4886dde6165dd110dbbcc2cbb9221b7798595744436ef30b2ae4886dde558755110dbbcab0e99221b7698595744436ed30b2ae4886dd961655d110dbb2c2cab9221b7598597744436eb30b2ee6886dd66165dc910dbacc2cab9a21b7598595724436eb30b2a64886dd65d85d9110dbacbb0bb1a21b7597617624436eb2ec2cec886dd65d8585910dbacbb0b03221b7587595634436eb0eb2a64886dd61d5655110dbac3aaca9221b75855cf624436eb02ab2a4886dd597835d110dbab2f06b9221b7565613734436eacac16e6886dd56175d9110dbaac2ebb1221b7558595434436eaafc22ca886dd55d8655110dba4c2caba221b7498595724435f4d0832e8986be9a1065d110d7cb420ca9221af968419324435ef2cc3ac8886bd9a1765d110d7b342caba221af668459744435eb0eb2ec4886bd61d6558910d7ac0acab1221af5685d9544435ead0bb286886bd5a164dcd10d7ab3f08b2a21af567e11634435eacec2ec8886bd59d83d9110d6f3426cba2619fb9061d634833f720c3a869067e61d064c910cfc83706b92219f90660b734433ef22c3ac68867de458750d21cfbc8b0ea1a219f59361c644433eb0e8b2648867d605764c910cfabc2eca1a219f5785d9324433eaf0b9ec48867d5db835d110cfabb706b92219f576613734433eaecc16e68867d45b835c910cfa8b305b9a219ef9760963c833df2ec12879067be498758d20cf7c930ea1a419ef9261d424433dc4ec1a42a067b61d264c910cf693b0ca92219ed27619324433da4ec226488677e4d8759510cefc9b0ea1a219dd874d9324433bb0e9a2648866fe518758910cdf24286b922197f9561d544c32ff2ac3aa88865fe55874c910cbf2c2cab922197d9561b754cb2fb2ac36ea9865f61d5654910c7fcb30eb22218fe685d9744c31fcd0bb2e88863f61d6558910bf9cbacb012217f39759504442fe72eb1c04885fce5d4380910bf9cb30881a217f3965d103442fe72c826e6885fce59045cd10bf9cab06832217f3955da02442fe72abb208885fce518640d10bf9ca2ec82a217f3945d903442fe728832ea885fce51065cd10bf9ca20ca9a217f39441915442fe726bb404885fce4d7641110bf9c9ae9012217f39359504442fe726a3a08885fce497641510bf9c92ec81a217f3925d103442fe722c1a0c885fce458341110bf9c8304b2a217f39060963442fe720c1286885fc6636440d10bf8cc4c881a217f19859103442fe33032206885fc65f6440d10bf8cbcc881a217f19759602442fe32eb2a08885fc65d6440d10bf8cbac7012217f19750e02442fe32e32206885fc65b7580910bf8cb6ea822217f196dce02442fe32caa206885fc6537380910bf8c86c8b9a217f19099373442fe321322e6885fc64165) else (0xc32a4886fce41864c910df9c830899221bf386415744437e70c82ae4886fce19035c910df9c2ac881a21bf38440d724437e701baac4886fce037358910df9c06e6a1221bf3805d9524437e700bb264886fce017558910df9c02e899221bf3805cd624437e700b9a84886fc6616580910df8cc2ca82221bf19858e024437e330b1804886fc6614380910df8cc28601221bf19841a734437e330834a6886fc6610654d10df8cc209b9a21bf198412734437e330820e6886fc65d8059510df8cbb00b1a21bf197601434437e32cc0286886fc6558058d10df8cab00a1a21bf194601654437e328c02c6886fc64d8059510df8c9300b2a21bf192601634437e324c0286886fc643825d110df8c830caa221bf190613724437e30eb02ca886fc61d6058d10df8c3a80a1a21bf187419544437e30e832a4886fc61d0650d10df8c3a0c99221bf187417644437e30e82ec4886fc61d0559110df8c3a0ab1221bf187411634437e30e82264886fc61d03d8910df8c3a07a1221bf18740d624437e30e81a84886fc61b7580910df8c36e701221bf186611034437e30cbac04886fc6197380910df8c320aa1a21bf186413734437e30c822a6886fc6158341910df8c26e701221bf1845ce024437e302832a8886fc6050654910df8c0a0c99221bf181415644437e30282ac4886fc605044c910df8c0a06b1221bf18140d424437e301baac8886fc60373d0910df8c0308b2a21bf180609654437e300c12c6886fc6018250d10df8c02ecaa221bf1805d9434437e300baec8886fc60175d8910df8c02eab2221bf1805d1634437e300b9ec4886fc60173d0910df8c02caa1a21bf180591534437e300aa2c6886fc6011655110df8c022ab2221bf176616024437e2ecc1c04886fc5d18380910df8b3b00b2a21bf167601634437e290826e6886fc51d8050d10df88370aba221bf106e15724437e20dc1ae8886fc41b835c910df88330aa1a21bf106613754437e20cc26e6886fc41982dd510df883305b9a21bf104e0d724437e208c16e6886fae418258d20df5c8304a1a41be79261d424437cf22c128690ef961d264c910df2c0a4c99221be527619524437ca4ec3264886f949d844c910df290b0ca9221be521619324437ca42c2264886f6e418358930dedc8306a1261bd983419544c37b260c3264886f64c1844c910debc9b0eb2a21bd79361d434437ab2ec1ca8886f565d8319110deac3a6ca1a21bd5874d9324437ab0e9a264886f5605364c910deac0a6899221bd5385cf624437aa70b9e84886f54df8650d10dea9bf08b1a21bd5376194344379a46c3242986eee41844c940ddcc220ca9a81bb9484113244376f28c3ac4886ed921435c910ddac3e8ca1a21bb5875194344376a91326e6886ed52164dcd10ddaa3f0ca1a21bb5476195444376a8ec328688)) else (if j<10 then (0x4443d6f2ca3ac8887add92645cd10f5bb22ecaa221eb57651d64443d6acea0ac8887ad5917650d10f5aa3ac2b2221e796541952443cf2ac82ac48879de5d6558910f3bc9acab1221e769759562443cecd0b2ae88879d65d65d8d10f3acbacbb1221e759759563443ceb2eb2ac48879d64d6558910f3ac92cab1a21e759059563443ceb0eb2ac68879d61d6059510f3ac02cab1a21e756859572443ceaceb2ae88879d59d655c910f3ab3acab1a21e756759532443ceacbb9ac48879d5958258d10f3ab2aecaa221e75655d952443ceacaba2c68879d59573d8910f3ab2ae6b1221e756558d72443ceaca8b2a48879d55b7558910f3aab2ebb1221e75565d562443ceaacaa2c68879d5591558910f3a4bacab1221df19161170887be2edb9c048877c5d97440d10ef8bb2e701221df17641574443be2ec82ae48877c5d904dcd10ef8bb208b9a21df17640d72443be2ec81a248877c5d1035c910ef8b3a0cb9a21df11641572443be20dbaae48877c419755c910ef88322ab9221de92741952443bd24e832648877a49d0558910ef493a0899221de7925d172443bcf24ba2248877989d1548560ef2b96eab1221de5725d952443bcae4bb264887795c97558910ef2b92e899221de52745952443bca4e8b2648877949d1558910ef293a2899221de521dd562443bca42bb2a488779485764c910ef290aeab1221de5215d132443bb46e83264887764c1764c910eebb9aec99221dd63745932443baaec9bac6887755cd7650d10ee7c92ec99261dcf925d1324c3b9c6e932648877349d364c910ee693a6899221dcd235d9214c3b9a46ba2429876e51d0655130edca3a0caa221db9405d954443b7280a1ae48876d5d17655110edaba2eca1a21db54750d72443b6a8ea1a248876d51d1655110edaa0aecaa221db54150d72443b3f26a3a868876750d744c910ece9a2e6a0a41d795059572443aed2eb2ae48875d95d655c910ebb2baca89221d759759773443aeb2eb2ee48875d65d655cd10ebacbacab9221d756759573443aeaaeb2ae48875d55d6544910ebaa8acab9221d6d2755952443a7f2aa3aa89874fe554755110e7d3420cba261cfa68419744439f2c1b9ac48873e5817358910e7cb02cab9221cf96058d724439ecd0bb2e88873d9a1165d110e7abb2e8b1a21cf567d91734439eaceb2ae88873d59d655c910e7ab3aca89221cf567593734439eaceb22e68873d59d635c910e7ab3ac689221cf561595724439eac2b1ae48873b49d6558910e6eb1aec99221cdd365cd6148397f2ca3ac88872f5d94759110e3ec9b0abb041c7d655d9524438faadbaac48871f5597558910df9cc2e901221bf3985d0024437e72cc0286886fce558058d10df9cab00a1a21bf394601634437e724c02c6886fce498050d10df9c8b00b1a21bf391601434437e72) else (0x979351d43443f2a8e9b286887e550d744c910fcaa1a2899221f95414d1214c3f2a6fa3286887e54dd4650d10fca9b28aa1a21f8d3448d41483f1a64a1a42a07dce5d6580910fb9c9acb01221f729759602443ee50ec02ca887dc99d8059510fb92c20aba221f725760165443ee4aeb2c04887dc95d6541110fb92ba0ab2221f725741562443ee32eb2c04887dc65d6500910fb8caa0ca9a21f719460165443ee326c02ca887dc64d6580910fb8c9aca01221f719260165443ee320b2ee8887dc64165dcd10fb8c82cbb9221f719059574443ee320b2ae6887dc641655c910fb8c82ca99221f719055954443ee320ab2a4887dc61e8059510fb8c3cc0b2a21f718794165443ee30ec02ca887dc61d5059510fb8b3b00b2a21f716754165443ee2cbb9c04887dc5957380910fb8b2a06b9221f716059573443ee2aec02ca887dc55d6580910fb8abaca82221f715758165443ee2ae832a8887dc5595440d10fb8ab208a9a21f715141954443ee2a0c22ca887dc5418259510fb8a82ecaa221f71505d952443ee2a0b2ae8887dc541655c910fb8a82caa1a21f715059512443ee2a0b22a6887dc5415458d10fb8a822caa221f715045952443ee12eb2c04887da5490558520fb2c92cab9221f659259532443eca4eb2a64887d949d5654910fb292a2c90aa1f652155952443eb32a8326a987d5e4d8759510fabc9acbb9a21f563759532443eab26b2ae6887d564d654c910faa9bacab1a21f549361d65443e72a8832a2a07cde554755110f9aabc8caa221f355459543443e6a8eab2a8887bc9a1065d110f78cbac0b2a21ef19758163443de32ab02c6887bc64d6059510f78c9ac0b1a21ef19059562443de30eb02ca887bc61d6058d10f78b3ec881a21ef16760165443de2cec02c6887bc59d6580910f78b3aca82221ef16759103443de2ceb1c04887bc59d05d9110f78b3a0ab2221ef16741163443de2ca822c6887bc5850559110f78b06eab2221ef160dd562443de2c1b9ac4887bc583645cd10f78b0308b2a21ef16060965443de2c0c12c6887bc58175d9110f78b02ebb1221ef1605d564443de2c0baac4887bc5817458d10f78b02e7b1221ef1605cd62443de2c0b2ae8887bc581655c910f78b02caa1a21ef16059512443de2c0b26e6887bc581645cd10f78b02c8a9a21ef16058d72443de2c0b1a24887bc5815458d10f78b022ab2221ef16045562443de2c089ac4887ba6096058d20f74b120ca8a41ee96241932443dd2c483262907ba5890648530f7493ac0b1221ee52759562443dca42b2ac4887b661d6341930f6cb1b0283261ed963419744c3db2c683264887b658d064c520f6cb1a0c90a61ed5635d943443daac6bb264887b558d6550d10f6ab1a2c99221ed56345931483daac29b242987b34d92358520f5cb3a80b2221eb9475816))) else (if j<13 then (if j<12 then (0x16457f62b9215aa8abb055062a3014f40a6ac52b0290514590a1504fec2798139789b444ce6261512db8953849b42466120988ed446c4231a1163889d0441621b810b28841c4152204b0ffc07e3c3e8e1f0a0f7187a983c641df50ecb8748c39481c460df406e5436581ac30d380687433c019980ca8064d0323019070c5a0607c2f4017370b67059942bcc159e0aab053b428dc13ef09bd84c482552124008d584484212e103907dd03c941d360e1c06d40352819c20c83060d02ef016a60aea05408288c137409300453020700f66071e0355018d80b84054e02678111407760331014e007f002fa00fe003a00003fc724ba404887f8c837558910ff1906e6b1221fe320dcd42443fc640bb2a4887f8c81764c910ff1902eab1221fe3205d132443fc640b9ac4887f8c817350910ff0cb24e01221fe19449c02443fc324b2c04887f86496380910ff0c928701221fe12741952443fc24e83264887f849d0558910ff093a0899221fe12740d62443fc24e81a84887f84850654910ff090a0c99221fe12141562443fc24282264887f84850358910ff090a06a1221fd3935d103443fa46f32206887f48dd6440d10fe91ba0c99221fd23741132443fa46e81e84887f48dd0358910fe91ba06a1221fd1964c163443fa32c98286887f46513058d10fe8ca260a1a21fd1904d932443fa3209a264887f461d3058d10fe8c3a60a1a21fd1674c163443fa28e98286887f44dd8058d10fe89bb00a1a21fd13758e02443fa26eb02c6887f44dd4380910fe89ba80a1a21fd13741943443fa26e822c6887f44d90550d10fe898304b1a21fd13060943443fa260bb286887f44c1764c910fe8982e8b1a21fd1305d132443fa260b2a86887f44c16454d10fe8982c6b9221fd13058d12443fa260aa2c6887f44c1435c910fe89828689221fd13045932443fa2608a264887f24c1264c910fe491a0c90a61fc63789132443f8c6e93264887f149d364c910fe293a6899221fc523459214c3f8a468a242987f1485364c910fe290a6899221fb19750143443f6328b2a08887ec64d4050d10fd8c3a80a1a21fb14899103443f6290b2206887ec51e6440d10fd8a3b00a1a21fb14759103443f628ea1c04887ec51d0655110fd8a3a0ca1a21fb14741564443f628c82a86887ec5050655110fd8a0a0ab2221fb140dd564443f6281b9e84887ec5037350910fd8a04c9b9a21fb14099173443f6280c1286887ec5017655110fd8a02eca1a21fb1405d564443f6280b9e84887ec5017350910fd8a02caa1a21fb14059373443f6280b22e6887ec5016454d10fd8a02a8b1a21fb14050d72443f6280a1a24887ec5011655110fd8a022ab2221fb14044d42443f620ca2a86887ea6094050d20fd4a120898a41fa92750142443f3286832a8987e650d044c910fcca1a0898a41f) else (0x83700d37ec5be90df0b6f5c379edbc92dde06ebbb7439b9b8dc896e0ab6f09b69cdb066d59b69adb430d9c56cbeb647db16cd8586c02b5ef5aea8d7016b46b5865ab34d53c6a69b5125a7ecd39869a2b4bc9a53ed24168fcb46c5a2d2d1216867341c1a024cfa967a033b899cf2ce1066e9b362d9a9cccf0663e3304d973ecb2065563290d9388c9506473b21758fe8c7806396b1b3d8cccc5fd62d5314ad8984c46461f2b0e1d863cc2b5611b306dd82b2c1116059b01297facbf575f87afa997c90bddf5ebb2f4357948bc5c5e04aef0576f2bb1b5d53ae8a17368b9405c662e1616fdeb7865b8eadad16cacb5ed5ab72d4156922b41259cf2cc516540b22158e72c595620eb07d580a2be295e16aea2571cab7415ae4ad0956502b0dd5786ab4f55732a9f55428a9d754b1aa3bd50e0a80753cf29ca94d6ca6635302a96714aa8a50c526229199483ca3d651c728d1945d0a27f512128815434ea13e506aa81853ff09f9a4f98a7ba53cea9e0c4ecc274bd39a29c5d4dffa6e5936709ae54d38a67f532fc990a4c4b2610d2fb497664b8425a252c5695c24ab7a5471290e941349cfa4d0525c692904919247a92318912e486da41f5203e8fb647a6a3bbd1ce08e0746cf2350119ae8c5845fd22e4516508aca4530a2839134a8926445ea21a90fec8777437c21a3d0c20857b4289212fd089683d741a6a0b9104f6823340f5a066102a080fd4044a0054ff9a7f853fa41fc2cfd9c7e7b3f0e9f6d0faee7d3a3e6e1f1a0f7e87bac3db21ec70f5a87a6b3cfb9e690f27678dd3c4a9e160f02077d33bc59dd0cee0c76a83b3b1d834ebcc757d3a951d35ce908742639de9cda8e62e72c4393e1c8d0e3d8718e388d1c2f0e0906fd437c61bd10ddcc6ea937361b7b4db1e6d1036591b1d4d8446bb935b31ac20d56a6a5734f71a698d2a6690b34511a08ccf5e67463369199a4cc0065ad32a21936cc8fa641431db18d8cc60a62bd312a187acc3046145306318148bfe85f8b2f8b97ab8bc5e5dc62eae973d0b9005c0c2de216d40b5b85a682d0a96708b29c59112c6f96204b08858072bea95e08ae06569a2b1895720aaa855012a4c150bca7a25389299b14b08a4de522728e494554a1ac5062280213dbc9e0c4e9d2714937009aae4d1a265e131fc98844bce25bd92c7495d64a982528127f49354494c24771226c907a47ea23cb91ce48da0467d23151175c8b08453c22749120088184398219d10b708512422020db9053881f640a820250ffdc7f483f5c1f848fb047cc63e051ed38f52479c03c821e178ef4476fc3b201d668e9e8743839c91cb58e460714838461bff0de546e5836c31b380d8486b9435771a8c8d2c0688e33de19cb0cd3865ca327c19148c75862f0312518638c17860162fa217a78bc1c5d522e5617018b6c05aba2d0a16560b)) else (if j<14 then (0x42a0695023a809540069fe14fd4a7dc53e469f014f7aa7b4d3d8e9e8f4f20a77cd3b4a9d834e9aa744d398a9c614e09a6ebd366a9b134d6da6a8d35029a5f4d13a67bd339a99c14cc4a659d328a99234c80a637d317a986f4c1ba5ffd2fba97d14bd7a5e352f0297494b88a5bbd2d9a96ab4b44a59f52cb696394b0ba57d52ba6959b4abca55b52a9695294a83a53ed29b294b74a55a527d28fa945b4a27a50b5281693e949e3a4e95270693614994a4c1d259e92ad493aa494d243691f948f6a472d237e91b348d3a466d22c69115486ea423d20ae901f47f3a3ebd1eee8f3f4783a3b3d1d2e8e5f4713a37bd1b428d7f46aea34ed1a328cf7466aa32cd18f68c434605a2f4d17368b4d458aa2b1d151e8a6d451aa284d13b689a344c0a2525122288d94450a21fd10ba882543f6a1f2d0f52878743b2a1d0d0e4286ff4363a1a3d0cae861f42dda160d0a968513426da123508d684494208a0f650742837f41aea0c9505ae829f4128a086503c281bf40cea05ed028680f54053a01bd006e7fff3fee9fe3cfdfe7eb13f319f904fc3e7e133ef89f794fbb27dcd3ee09f6d4fb527d9d3ec89f614fac67d413e8f9f3f4f9e27ce53e6c9f334f9827cb53e499f1c4f8ca7c593e269f104f86a7c293e0e9f044f80a7bf93df69ef2cf77e7b9d3dbd9edbcf69a7b2b3d8f9ebf4f5e27ae53d569e9d4f47a7a313d129e80cf3c279a93cce9e644f30a79793cab9e52cf25279073c729e30cf142787f3c399e144f05e780d3bf59df24ef4e779b3bbc9db4cec5a75b33a709cf8ce5ca71d1388a9c004de066e5d36d09b28cd74a6ae935169a4bcd00a671d3330995e4c97a63a93181988c4c34260cf2ff397c54bc5a5d032e2396dd4b59e5a292cab960b4ae32565d2ac59528ca71e52bd28df9440ca08e4f8b27469379c99fe4c4325a29291c9292488d23dd91b4c8baa44ed222e90edc85ca421320ab902c47fea3f651f498f5fc795a3c071d848e98c72ca387d1be08dc146cbe35b91a738d0ac670a32c918fb8c54460d22f8117368b56458e22b8915508a6e4517627d3136a8975c498623991158886cc41961fcd0f9e878a43aae1c590db886ad4339a18cf0c0985d042c86152f0a0d84bc423e610df07da83b8c1c7a0d6b064182ec4159209cb04718209c0e5205ff028b810bc06ba025f00b0801e3fec9fe3afe677eeebf5d1fa42fca27e223efc5f726fb2a7d60be909f3def97b7c8ebe355f11af8197bd83ddcdee14f6ac7b2cbd845eb66f53f7a603d189e81ef3857988bcb25e4d6f20278d7bc4c1e1baf07478213bfbddf4eef497775bba61dc48eddc76b43b3fdd942ec4375ed3ad99d5faeaaa7536ba869d34ce95e747aba231d072e7db73c9b9d2dce06e6bb7323b974dcabee4f67246b9091c776e3477174b8a2dc470e1da70c938555c1d8e0) else (0xcc20de102b07dd83d2c1e0e0e9707138383c1b3e0d2f068b833fc191e0c77060382f0c17560b9305a782c2c14de0a2b04c7825dc120e08ef043f8219c109e07df03e381cac0dce06a303458191c0b56056702a7814dc0936045701dd80d2c05b6029701298083c033e015b00a18034c00c6001effed7fdabfea5fee2ff657f96bfc2dfdd2fedd7f52bf9b5fc6afdfd7ee2bf5ddfa7efd077e67bf30df96efc7f7e2ebf095f832fbcb7dd4bee1df6cafb597da6bebfdf58efaa57d4cbea35f4d6fa497d08be7bdf36ef9957cc4be545f232f8f77c6abe275f0f6f8597c10bdf4def36f7637b95bdb75ed1ef6837b3bbd84deb5ef54b7a89bd36de946f46b7a19bcf95e72ef3497993bcbbde59af27f792ebc8ede3aef15d7887bc2ade0baeff977ebbbed5df26ef5b779cbbc05dd0eee2376f5bb725db22ed59767abb34dd936ec3775e9badbdd66eeabd7542ba8ddd3fee9c774c7ba55dd212e8a5742bba025cfa2e78373a5b9b9dcd32e6617309b976dcb1ae53f728eb93edc9b2e4b77229b906dc7c6e3ab71c4b8d9dc68ae3237180b8b25c522e2597110b874dc30ae1217069b826dc0c6e02b6ff9b7eedbf06df4b6f89b7b6dbd46de556f19b789dbc0adde36ee0b7625ba76dced6e4fb71f5b88adbf76ddfb6d6db5c2daa96d2db67ddb326d9196c5ab6145b032d7e16bbeb5dc5ae72d7016b59b5995ac2ed5df6ac8b550daa42d5156a84b539da95ed4776a09b4f6da772d38169a4b4b95a55ad25f6913b4765a342d17f6898b4495a206d0f7686ab4275a0cad0436805b3fa59f62cf8f67abb3c7d9dfacef16767b3ab59ceace276702b37359ad2cd31667cb330598e6cc2565e0b2dcd9676cb036570b2aa594e2ca396500b26cd92cac917646fb229d90dec837640ab1f1d8ef2c7156363b198d8c56c5f362d2b155d8a3ec4d16241b118588aac41d61fdb0e5d8692c2fb6161b09d58422c1ad60bab04f5820ac0cd6055b01cd80a2c02f5ff0afe4d7ee2bf395f96afb257ccabe175efaaf74d7b62bd8f5eb6af52d7a7ebd335e93af41579f2bced5e5aaf1f5785ebbe15dbeaed6d7672bb175d6faea9d750aba375d0aae7757376b9995c9aae345715eb88d5c1fadf6d6f72b7555b99adbed6d86b68b5b29ad86d6bc6b5ab5ab9ad49569dab4b55a3ead115681ab3d559ceacd95665ab30b5974acb1d64f2b25758f9ac63d62dab14b5889ac3c5619eb05557f8abe355ed6af495793abbbd5d42ae69570dab7355b2aad7356a8ab3b55912ac2555f6aaed55726ab5b5586aab55550eaa39550baa77d5322a959549baa3a55162a88f5415a9fcd4f76a79953a5a9bf54db6a6a35340a99254bf6a5ad52afa944549b2a4b75255a91cd4876a41951fba8efd470ea3395175a8b254522a2595105a874d4336a17950aba84d54226a1075072a830d41))))) else (if j<22 then (if j<18 then (if j<16 then (0x8b01422703e03245e8340600b81091222043a45c89a07400c17a2ec1a02e2204388628b51201c81900305e8bb05c4408710c11602844807206400c05c0700800c11602844a07c064c1983105e0b611c2183f0760d90bc1381f02341fa3445c8500820e01881c41200280810f01842b44407d0c80dc1101280810f01842b44607d0a80dc1101280d11501f0380610ac0e80dc1101282083405c8510820e41962ec48075045c1a82f0570960fc1c41e42f04e07c07801808c10c1792d05709610c1c41e42f03e00603384303a46e8b615a2383e8520840f80190660c41782d8470860fc1d83642f04e07c08d0430660c415c258470860fc1d834c3c85e09c04e8350660be13c2383f0690790bc0f80170660c41782d84f0961190bc1381f022c11c1983125e0ae13c2183cc3c85e09c04c8350660be12c2183883c85e07c00ad88cec3f761c3b0c5d85a6c263610fb060d827ec0fb6045b011d7efebee35f23af6ad7a1ebc9f5e01aed9d75eeba875d0bae69d726eb8c75c2badf9d6eeeb7335b35ad68d6a66b4ef5a55ad0ed673eb3035949ac7dd62b6b0bf5811abcbd5cceadf756c3ab50d594eac3755e3aad5d55ceaa7754d7aa39d5096a783539fa99dd4b06a53f5293a943d493ea42f51dfa8d3d4566a2435115a879d4296a0db501fa7f3d3ebe9eef4f3fa778d3a369cab4e1da6f2d365e9aeb4d3da682d333698ff4c47a612d2fb697974ba9a5add2c36957f4a71a51cd2756930f494fa48bd237e914f4817a3e4d1e468edf4721a353d19668c434615a2f9d16968aaf454ba289d141e899f44ada245d11a6883743b7a1bfd0d7686774303a165d0aa684b7420da0ead056e81ef40bfa02dd00367f273f719fa7cfc5e7dbf3e919f0bcf6ce7af73d439e6fcf1ee782f3bb39db2cec5e75673a399cd4ce4be71c338939c22cded66e7736c19b23cd78e6b2b351b9a71cd1fe688f33e399d5ccdce667732d79944cc83e632b3173989dcc35e60bb2fe397bfcbd765e4b2eed9765cb9f65ce32e2396f5cb61e5a472d019659cb196582f2c0b95decadbe56432ad3954dca9e654af2a0994c7ca4ae51bb286393f4c9e164e6f26ff934dc98864ba725b192b1c94ae49bb24639220c907e482723f191e7c8d56466722cf9140c88ce43f721ad90a4c8396415b2075901ec80163f9b1f958faec7c3e3d831e5d8f07c77063b131d678e97c743639ab1cc98e53c7216386f1c2b8df9c6f46375f1b618d94c6bc635471a3f8cedc668e332f195f8c9ec6416314318538c18c603e2fdb179f8b9dc5c0e2dc316bf8b2dc57de2b7f155b8a86c52fe28e3140d89eac4dc6264712eb894ec493e240311b3889cc4356210f103987d4c3cbe1d3f0e3b86f6c36261a770ced864fc30ee18070bb585b3c2bb6153f0a678517c27de12fb092f8470c22fe113b087b842) else (if j<17 then (0x400621922c83903200290c81522483c85206400701c03045107206204800e1045d82321881d81b001c5c8b20460410760a606c00817208c4c81041c43181b00201b8ac1328510848ba14c0c81722c81282142083b0510760648b904a2650a21091041d81902f41521c91782a4420760640bd06e2c91721091782981901045d8214384430520760640300540950e207a0840ec1300241b83004a0490820ea0840ec1300281b82502e0490820ea0840ec1300280800c31662503b03600381c020030c590a312c0d8010038c590a31281d81b001c1198b31281d81b001811810316428c4b036003821316428c4a07606c0070380480700c316428c4b03600481001862cc4185606c007020830c598830ac0d800e0480700c316620c2b03600412122443a45c0a912c0d80104488748bc1522242b03600412122443a45e0a606c0072244408740a91322242b03600499121d22f0548890a312132243a45e0a161e60ac0e1c3186181301e82145e8b9164a650929141c832855072a09c10c0980f410a2ed5791051682944c0790c40bd1722c80e299424a450720ca1450bd1722ca0949181d0318518820e618b17a6be0840c316428c4b07205ec91821038c590a312c1c817a6be0818b214625838e2ec5202304262c8518940ea18917b04a48c0e81862c8518960e4c9182103e0718b3106147821038c598830b813008e65a0818b310614582062cc4185c0980468250420710b2104146c1581c2c1580c2c0608b615e0b948c8b20ea08717a2e41b8b24248410748b81522483b0360068210242440800e11ba2f44307d0a40cb07f0d21741402103806407104483f8690ba0a01081c03203882250e09902e05045a07d0c21581922e5180211320400708d60f81101e822c4588810b01201c02184588810b01201c02181fc3485d0500840e01901c41121041a02e8290420740c716e2403c822c2083405d0520840e81862dc480790458170288490820e11622083885606503f8690ba0a01081c03203882245b0af42522c83e04407a0980121041a02e8290420740c00f208917a2ec1802e0428490820e11602844b03600684017a2ec1701e42422c44e04407a0980182f45c8371640b90921041d22e0510760660b615ea44c590a80ea0b00101041a02e4208390618b31201d412002c200bd1762c81802e42822c0508920fa15819a2f45d83005c8490820e11602844907606604017a2ec1721211622483e04407a08b1722c80e0990242440700cc0e80ca0280400608b11181c42a03205c8b20382640900e01981f01920500800c11622303885c0640b91640704c81201c03103e03240a01001822c4420710b80c805c0700800c11602844e0740648b91640704c81201c03303e03241701c0200304580a11381f01920500800c11622303885c06402e03804006) else (0x840718b21462681d001c9a12e02083c07407a0740082684b81080e81902a81d00209a12e04304203d03a00393425c0700900e01940e801003a0618b31061681d001c9a02122803a06503a0039340384500900e01940e80100708a00e0188290250340340091720de0a410516c2a818e2f41282182103883d031c1282182904144107a06384105507145a8880f40c71720de1741051740c60822f410c1c22101e818e0a812c9d43881f02203d04c00906e0c01281292284302203d04c00a06e0940b81292284302203d04c00a4428490718b21462701e00210921041c62cc4185c0780084428490820e31780f000e8490820e214624c4185c07800916c4708810c41500f41301a0048b62382588810c807a0980d00245b21c42083085482c0038b64382590820c905800705c0941098b21462603e03205e83005c62c85189c06381401c43245d0a20e40c70680b80710c20e40c60680500710c91041c818e0b80710c91641c818c0c01702381862cc4a07c06403005c08c0818b214627019005c0a01081862cc4185c064017028840c5d0a31061701910704c817028840c5c0730b80c915e2a45209d83901d41600205b0af14824608282c00383405c0400720cb1281d41102d852096123041416001c1a01402003906207b0aa08805c03945a0a51241c818e0500710c51641d429031c1b83004204007604807a0881722c81080e81942a818e2e45901202003a85407a0640210240400748ba1540c70820d01502783922e8528880f40ca0822f41282182142a03d03201b83482122e8550318200bd05c0a90528991041e81920b812821820a2d0528920f40c90800b812a8b41441f02403d04482704a0860848820f40c706e0840b81001d81201e82205c82113203a06503181081202003a45e0aa0638b90240410780e91101e81900b81281251682944e04807a0890280488828b510a1702403d04484013205c0a10a312620c2e03245e81202003a03e031810812020038c5e0318548a413b07185407807a0a80120dc180a412304185403d05400916c0700800c21520a808e0d01701001901e414001c9a12e01c0310510720640082684b80700c20e40c800e2e40e01201c03085603a0240410800b81521c91662103e03241a02e04a08608207c0638af0540954e91c20f00f415002410812020038c5d0ac063812020038c4407c06303714805c48c10807a0a80102d80e096020032415011c1a01402003203c8280039342280380610720640072684500700c20e40c800e0380640a20e40e009001c5c81c1320480700cc07404804e05c0a21091742b018e0d01702504284107407c0640340430700b81442122203e03241802e42122f018a2d857825024a4488403d05400916c0944b01252244201e82a00490c91702a44907206400721922c83c85206))) else (if j<20 then (if j<19 then (0x3241b834116a1701e00185c92e05422d4440750a38370380400608b90a30140200388608b20ea1481900241a0ac0280400710c20f61942903200581c02a0500800c214a1482101c0050140200388608b20e21481900241a0990280400710c20ea1481900285c8370684b80a08ba0ea16819209c1282304205083d8650b40c906e0720a010019215018e0500800e21902c83e05206400902e0500810c11622183885606489902e0504588860e215819008c4c81702822c83d8610ac0c917a6c89702a31322103c85202002303903103a86c00384106e8d545c0770b40e80101045e91080f40e800c89510a1c214624c4207c0780094382640b90a31281cc2e03c0048bb4688b98a11021881d81b00242001001901e430a1005e8b206062c8518940f61701e002c5ec12821038c590a31281f01e002a0941081c62cc4185c07800806008cc590a31281d43603c0048bd0610420618b21462503e03c00503004662cc4a0750d80e80e00245e830821030c590a31281f01d01c0058bd81d030c590a31201e01c00242092e05407245d8951001d43121045e92e04a08c10c1000ea1890824b81502503c07003a86807a08a0802640b90a31262103985c07800a0540400608880f218617a0d01711422043886007206400a17a4408710c91702a44807206400a17a0d01711021c43244486206400a07e0a80800c80f219018e4408620a80f40d80d001c5da37460c5c8810cc0ec1181b82285d91021982b038b0f20e60ac0e20bb1722c948a1041d42a03902ec8810cc1581c51764408660ac0e28bd22182b03880d017025046086449071c1a02e04a08c1091021d22e44c07a06583405c0400710c51241c81900241701001c43045a8920e40c80120b80800e21822c4490720640090682c81701001c43144907206400a05c09410c10516a24838e1001702503ca2d44907807a0890822f4170250460860828920e484105c0a812a8920f00f41100dc0e01001822e448c0de1701c02003244a031c1802e0460708810c11622503b03281802e0460408608b11238250460844588920e30210240388688b11422700100f45d82e8250384588a11281f00142ed182af0384408628b414a26444072c5d91021822c0508980f40d80d0028200bb22043145a0a51381c817a2ec5902514808c1088b014224c410730c68bd1762c8180af82022c05089245e8bb1640c20808b11341280922f45d8b28210384580a11340e801405d0820c214624c4185c0780090802640b90a312620c2e03c00481401d22c83903140a810a1c03085507207400885e08446d04a062c3004204046d03145d83481ca24c410730d41281500285dc0e11622844d03a0038bb81c22c44907a0940a80102d885282c00203405c04006207504800716c2a44b40c50580060680500800c40ea09000e0) else (0x622be45d07c0980f41122f41a0b205c8410748b81441d81b002c1b8b64208304590a31341f42921010820c316428c4d071c20037420830c5989a0f81301e82285e8371648410718b31341f02603d0458bd1722c909291420838c590a31341cb06e2c857a1231741f02603d0448bd1722c90929141c830c590a31341cb17a2ec5c8b2424a450820e2146264440790c68401760c05782e11602844e85245d83015e8404580a11238bd06e2c88f412516a2682503b0450bd1762c90f41211622702603d0450bb1722c90929142083a0548931041cc3180f45d8320608410788b114224907a2ec1920e11622844e03c0048b60380400610a504303405c0400620750430b60382588a810018a0870680500800c40ea0862680380640a20e40c800e8d81189c02103c4638b114e2701148d811a1602103c4648a710e1701140c91802102003b018c05c0a81411781c428c2ec8810cc1581c51764408660a80e28bb22043205207140b8150288404588810a38bb81c22c44a07c0980b00101041a02ec2903903e04c0580090802d857c0c50428b615225a06282145b0af04a04a48a0e00720880380540810f01842a83e85206e08a0808488518931061582203705800a16c2bc5209181c208616c2bc0e010019208616c0704b010019208616c2be170a412220860390500800c21441101901c004c340430500919102043c07203c00501001842a0390420300070802640b996214624c4185c0049140252450718b31061641100840901001ca2e818c0840901001ca2c508008c0820e81980060460410740cc002a214248410718b3123212420838c598830a32214248410718b150921041c428c498830b80c80800720700c105c8b20382640900e01981f01920720700c0c5c8b20382640900e01981f019209411a1031662603e001c5e8b2060840c5989c00381001c4324590720640070680b80800e21841c81900201a0ac0200388648820e40c80120400710c91641c819001c10812020038c5989c003812020038c598830b800706008e0618b313800602f030c598830b800602e840c598830b80060200388648b91241c81900201189902e4550818b80e61701e00280800e21922c83c8520640080682c81701001c23486107206400a0682640a01001c23486107206400a06008e0618b313800602f030c598830b800606e0c01081001d81201e82201a02102403a458a0dc9700e91740c506e0c0970250240400758bc0900f41160dc1081702003b02403d04403704a05c8a01202003ac2e04807a08b02e8408518931061701e00201f81c81c031018a0400710c91641c819001c1a42c0200388648820e40c80122e4590210200384690c1c5c8211320400708d218c0c80420480800e11b22d818e2e41381702822e83c85a0640340460840b81420ee1a42d0)) else (if j<21 then (0x810c80e28bd26e4c28bc0e818c1e82503b0450bd1722ca4cc1292303a0630a60e502c04a08c108204324384440790d400b02e0510820e11622042b0360048bd8252460740c316c2983d85245e8b94612660840e60f81301e82285e8b91652660949181d03185307280b89602a8404588810a381702a8404588810ac1180902bc1502542522e44907407a0890420480740c31662460240400718b31301c604a0860818b31301c60380480700c316428c4d03201811c22043045889188e11021822c44c03181b91c22043045d00181b91c22043201d00180e01201c030c5b0aa0740080380380618b41481281a01a00483706822cc4d00141b92e31300e800a0d01741402003a06407904401c0240380618b21462581b00245c8b20380480700c214c0d80120d1170140208380618b40f61541140d11701402003906207b0aa0891720704c81201c03281d00200e01501c03105204a0680680120b812821917224838c0b8128230428410708b11241d81941001702542422c44907407a08905c0941182142083a45c8920ec0ca0680b80820e01862cc4a0750448af1522914898b31301d41100d01701001c830c598940ea0900140dc59021020038c4c03a0040b91640840901001d030c4d00245c8b20240400718980f40080420480800e116626800e2e4590210240400740c01462680140d05902e01d0308518980f00e00142ec5c83425c0aa0e08b51101f42d002c5e8bb1640941182182103a03d00285d8af0540954ec1c80f00f41500285c8371644ba0808ba0038371642bc1281252304201d00245c8b20380480700c21462681d00285c8b204a08c10a1051241c817a2ec5c8340548708a08b91081ec2962f41b8b245c4510808b51240411760941182143844087207245d82a04a87103903b0438371640940921051240c70802f45d8b205c0a88e21411322083e85606682e04a08c10a1041c22c44907606504005c0948e21211622483a03d04502e04a08c1091011622503902f45903005c8508808b112402e04a0488808b11280c706e2c81782502484481d00201288b11422601d00181b83215e0940921180740080720c80901001c83603d0020108120200390688ba0038370640840800e41b00e80100d01982e04604087a0e114403005c08c0820f21c22c45089241e8bb05c8484588a11280d80122f45c8b223884245c0a91240bd0682c90820e91702a44907606c00b17a4c0d781c420830c590a31248bd14084948a1041c62c85189245e93035e08d0818b214624817a0710929141c830c590a31248bb14084948a1041c62c8518991101cb06e2d81a83411642a83e85205ec1292303a0618b21462583922f45c8b293304a48c0e818c1c91760c057c2142022c0508920200bb83c22c05089c0980f4112100198b242122e055071c20037) else (0xf43185a07400b1720844c81202003a06185a07400a0682640a00e81901cc2c03800483704a2640b89622804948c10807a0a80182e40e09902403806185a0740090380540700c41461502503403400a06e2b04ca1442022d428e2e41282313284083d8650a403704a2640b812420a1481d82245c82a04e8710a08b11081d80122e41b89942884045b001c560250460844ca1041c22083d8660058140244404588860e21501e82244c8170284404588860e21480468704c81702844045a07d0c21581960700900e01862d8530360040b94600840800ec0880f41300245c8b20380480700c614c0d80120dc1289902e0580921190a40d815002c0d09902e0540a08b40fa1842b0360058394600840800e81a80d801005c4b01511781c428c0680b81511781c42b0460240b91648c01081011b81301e82241b83042ea4508107c0880f4130028180a91482740e48890d81101e82600584017644086407a0030b652c8410610a80ea0980e00241a02e42884106007504800817249c0900e01862083d03a00480e018828c410740940d00d00245e93425cc510720c20ec0d80122f50921041c62003986c07800917a8490820e310618605408c0e08820e61a800e0a81190730d00e800c1005d91021801d430c4f05b0af13aa5a03a82c0040410680b90a20e41962c03a82400504017a2ec1848b81522483e85606c00b17a2ec1821091702a44907606c00a0802f45dc8b81441f02203d04c00a17a2ec1820c91702a44907606c00a17a2ec1820c91722483b03c02c00a17a2ed0648b81522403a0340048340280410700cb1681ec2a82241a02e0200390658bb1281d41120d00a01001c832c5a07b0aa0891720704c81201c03281d00200e01501c03105204a0680680121005ec1251682944907c0900f415002c1702504283a45c0a91241d819209410a1442083a45d0a91041d81942f41b83042e84107107c0880f413002c5ea1242083a45c0a91241d81b00285e8b91648490820ea1522003c86606c00c05409d0a48ba1422003c86d0ac0ca17a0941182142083a8548800f21981962e55921242083a444861c1a02e0210380638b71301e41122d857c9692304103c82c0040410680ba0a41081d031c5b8900f20a00182bc548a413a070c4186505800917a2ec1511c414a244410730da1681d00301282304304145a0a51241cc3503a005825238a2c83986c0900f4150024560250460845041011041e80122f45d82a43922c4420750d61491760941182143844103a86205d8300540950e20750c40ec1122ec1521c91762444207d0ac00917a2ec128230422810820760048bb95e0a81289d43881d01e8260050bd4248410748b81522483b03600521242083d0748b91121581b00245c8b20240380630a20ec0d80122e45901c0240380630a606c0090822ec8)))) else (if j<26 then (if j<24 then (if j<23 then (0xd41a20c116428c4e8528200bd420830851891820037418428c4e04c07a0b80120fd1721402083806207104800906e0c0970a412200e410e104578a91482750e20750440b615e29048a1050430b614825848a1050430b615e4708810c90430b62382588810c90430129220420780e516a2142903600503f8690ba0a01081c03203882800503f8690ba0a01081c0320388280051372600700700ca0840ec1300251a0210252440800e516c2980122e45901c0252440700c614c00926e0708b80e01941081d82600481c22e0540700c81440ec140160050b90382640949101c03180100700a80e01902a0240160040370602904881001c80c706e2900b89102003901e82201181021d03201d00188e091219812018a0d01701001d031c5b8980f20890680500800e818e2e03b85904491222043a0548991121581b00250e09902f05645a0790ac0d80121004c81781522644485606c0090680840900e91628371640c01081001c23470420480808d916283742803a45880dc1089902e0400708d407a0890680b80840e018e2dc4c0790448340280420700c71701dc2c82260e091818a08416c2bc52091020039410e0d01701001c832c5d8940ea0900142d852096122040072821c1a0140200390658b40f615412002812910516a2601d00188828b510a1601e82a0038371582650820e91630b916409411a1041c41c717209411899421220838e2f41b8b242083a458c0dc5903004a0490820e206403704a2640b81242083881d82241b8b20600840800e11a80c81722c80901001c235038e0840901001c236458c2f4590250462810820e40ec0091720dc5909942122d800e0dc5903095e0940909142080d80142b0128231402650820e91041d80140dd1802113205c0800e11ac1d01e822c108990240400708d916c0c81722640901001c23644207606483704a2640bc9602424508585407a0980180840901001d03545b001c590211220400708d516c28802403a0618b310616818e0480740c316620c2d031c0900e01862cc4185a06380e018828c418540940d00904408608b110216018c05c8810c116220428c0dc8e11021822e800c0dc8e11021900e800c0dc1501722861601d001c1a42e0280400740c80f20880240380618b31061581b00200700c814620c2c0460700580122e41089902003b02203d04c0091720704c81201c03181b00200e01501c0320540460700580120d0172140200390658940ea08902e05245c8890a282102e0524590790a303702883a45c8514128230420510748820f21480680ba0a01081c030c5b8980f208a0680500820e01862d0398550448340280400720c31681cc2a8240050370422640b81001c61702403d05400b1720844c81202003a06185a07400a0422640901001c22cc2d03a0048b904e2640901001d01) else (0x2a04a0794e81c82462544286807a08d0802f40f41251682944e04807a0a80162f41b83055f04945a8920f81201e82a00603c17608c0e10c414a264440790d40d80d0034170250460850808b11241d80120dd0820c11642b42b031c200bd25c8410720c31642981920dc180af25c8410618bc0880f41142f41b83025c8410718b407a08917a2e4972124208390618b312c0ca17a2ec172124208384588920ec0d80160dc1a8344208304590a313a1581942f50820e41862c8518960640370604b90921041862cc4e04407a08b17a2ec5903005c8410708b01422483b0360068bd06e0c097212420838c5a03d04504017a2e49721241c830c590a60650bb0460708810c912a2143503245e8bb0690420728931041cc3503a0058250460845028b414a24c4107a07400b04a27545a8931041f02403d05400a17a2ec128230428294498820e61a81d00305d83055e0a812a8931041cc3604807a0a801a0f05dc2e0460710d91021802a44a8800ea1a81b01a0080bd1722c90921041d22e0548920ec0d80181005dc2e22043245c0a80f40c917a2ec1b8af40880d410e2f41b83015e8494898b31281101a822c1b83015e84a44a04406a0880822f45d8b241d02a448e2f45c8b2424a450820e81440bd0682c81721041d02981b00245e8371642bd0820ec0980f41122f41b8b2424a450718b31381301e822c5e8331648410740a91238bd0682c90820e91702a44b0360050bb1722c90929142083a05102d85781c020031410c2d80e096020031410c1001fc3485c0430700cc0ea0b00140fe1a4140218380660750580090802c80e20e01828b91640700900e01942a81d00245c81c1320480700ca0740081720700900e01902a800e0dc0e01001822d428c0dc0e0962280400618580640340280400720c40e61501f02400503705405c4b01221921502003505400b02a0410550730a81100d00201509d02003083986806382a0460784e81221901e43204006a0a80182f45c8b253284948a0e41942a83940dc0e01001822cc48c0dc5792e03804006189806403405c0400720c31281d01a00241b8250248460718900638370602bc0910c81522502003505400b0680cc0720a20e40c800e0e8198b205c08c0840e21882890240400708b101b8af25c0840800e806383a0660840900e114303405c0400748920e40c80100d01980e81522483903200403704a0490880e91240c70740cc5902302083c0710c815224a0460420710c414a2460740cd1702302103e0710c014a24a0740cc1181001e8388640a912483a06e0d01710c11682a42900e81ba1502843045c0a912403716c0d41a10c11682944c85241d03706a0d11710c11602944c85281d03702a8508608b81522542920dc5b21041822c856851c5e8b2420830850a0dc57a1041842b01e821c2003716c)) else (if j<25 then (0x81101e8260060bd1722c90921041d22003c86245e8250460845021041d22003c8660058b95648490820e91001e43100a81181c2204304428690a40250460854588820e61942900a81181c4370508810c11001d434852c5e82ab1222103a8690a382a05008c0e10c51622203c8650a50b922904a0840e110a18c2900a8140230388548630a11101e432852c128230428510808b20f61942b03600582a04e0840e21411622003c8650ac00b04a08c10a1921c22203c86205782e15229148c8b91241d41120dc180af25c0940929131200d41140dc180af85c0488648940800d415002c1b83015f0b88648940800d41500281181081c43145a89181181001f0388628b51238b91650b81081202003886489245c8b285c0840901001c43005120400710c516a248390320040b20460420710c414a24706e2c85792e0420400740320970210240400708b185c8370682c89700e11662681920dc5903025c09409291020038c5989806603a0662c81181081c4310528924590230200388640a912383a0662ca1702302083c0710c015224b04a08c5020e917224838e2f4590250460850820e91722483b032c1a0b205c0400710c51241c81900281a03301c8294490720640080680400710c51241c81900201b8b285c09409211206383715f0b81281242243870802640b90a312620c2e03c0048bd3644b81501431301d42900dc1a10c11682944c851c5c8370684b845989a0ea1480740dc1a41421822d0528990a483706a43045c0a912a1470740dc1ac2e42a4304580a912a14a17a2ec1801c218a2d05289a07400a06008c0e10c51682944c8880f21a81d00301802303806c8628b51322203d03603400c17a0d01711222043a45c0a80f40ca17a2ec1a21041d22e44907606c00a0802ee1711021922e05407a07400a17a0d05921041d22e44907606c00a17a2ec5921041c22c0508920ec0d80161005dc2e22043205489510a1a81942f41a0b242083d0748b91241d81b002c5e8bb0680b88710c9170280390320058401760c01711021822c44c07a06c0680182f41a0b20600b88810e91702a44c07a07400d17a2ec1802142122e05489606c00a0802f45d81e91702a44e04407a0980161045e8bb42122e0548920ec0d80141045d83706122e44907c0880f413002c5d81c22043245d03185e8b91640b90820e91702a44907606c00c1764408608b01422603d03a00483c1760d08810c51322203c86a07400b0821005d90c51682944c07a07400a0802d90618b31301f4160020208400688410618b31301f41600285d8230384310528991101e43503a0058b6923040c598940fa0b00101041a41081c62cc4a07d05800917a2ec5c92e82504207189510a1a81962ec1a12e0540840e08b312a2143685a0660bd1764b81282304304207189510a1a81982ec97) else (0x1c080e040702038281a1581c2c060c10a141603060d4100b018322e83850c010208020000010a3038507f03e030e0d28b0a11c13c061c28c0e141a818143560e1431c06143cc0e14335161413c061415c06141522014352201431c061418c0610b991781c37040b8205c102c0c1c060e030701830a283858130185813018581301848d683848c6156030d0ae03091ba31c061a18c061033048aa0c080d028aa11848aa11840e8186f08c207848c207848c286f08c2066081a0611d07089aa0c0b018380c1c06081a040d020f01066083c4461033a06101aa061235a0e123185541f01888d608048c701848a1838487f01848f111b070ec10381c146b41c246b040243180c2c0e0e07050d48b0911a13c061a33916122342780c3a076082a0760827040b8205c1028c581848dd18b030d0c4106061904606110460611046061303060e48ba0e1c3085508e0e507c06343082180c382f0430186c0c1606081810100000000000003038381c1c0e0c2304000000001440381c10000000000000000181820603070182042a051b82022304001154230a1bc230a1bc2308002838341c185541c200000044608141c1c060a2305118340c1a060808dc18200b0305818340c1a06080c0c116c2bc52091020039410e2d852096122040072821c8e09101c432410a04848a0eb17622c2c04007208906e0c2578250242450758b80800e411608c0b8121220420710c40800d415002c118170242440840e21881001a82603400c2280494898b31061401a82201b82a02e25a0a01221921502003505400c06e0a80b89682843242a04006a0a80160420710c516a2142d031c0800f81c43145a8850b40c81720844cc140240400710ca0f21681962e41089902b0500901001c43283d032c0800e218a2c83a8520640080460684c81081c43142d03201b82113205c4b11402003a83c03d04583704a2640b914024a440800ea0e61601e82341d0230342650a81081c43142d032810a140240400708b60ec0c81720dc1a09942803845b0750ac0ca0462640800e21941e42d03201d0230342660a01041e0388650790b40cc13205d0748b911215818e08c1089902e83a4590790ac0c906e2650748b90ac0c604a08c1089941d22083c8560648341320500800e21841d4290320050340280400710c20ea1481900241b82513205e0a01242321481b02281c0260342640c41502684407c85208c0a809a2d857a965228410710750440af1522904e81c91001e43282245b0af52c84106407504384116c2bc4ea9680ea0878690bb0a210c1c83203a82c00482a0460784e81c02443203c8640800d41500341502303c2740e10c80f21902003505400c04a08d0820e91722483b00201282342083a45c8820ec0d80122f41b83042e84107107c0880f41140dc182174248410758b20f))) else (if j<28 then (if j<27 then (0xc84068103522c286004c204705c098101009a04080981040818135121013220a1430348402034081a42122c3020c8204030618a8b0a08604080d0206a4584454103462c20340828438101a4201015040c060a030645d070906507c061c8b0618507081401c110a184826c1c286b0d02c0980c205122c83870c3026030c9e01c42122c4278071060607341040f811850dc114980c217a0f02078840217a0f0207807108060f00e2100c1e01c420183342014304261028916143003e1413040fa04c061c1a820a2c346104b02603120d40c316193081941281880a1448407d44842b2459070c1408840e1828916143491741c386f0c301870501020e4030a01821001a88b512204021462430690a28386428c48402a83e030c18c2aa0f80c406341d0260310852880a0810a08c590a0845a0a0905020b8050402818320830024c00302e0498007428102480c20020033020c04403406009b01100d010602181a06850284819160a12054482000000c0400017811080b01108180126041817024c08307e0600ba8212080342814380a1040612104061110040d01041c1d0a0411c17094583040105809c10a861014027038a18460e0d0a041e82450c184107a085430942810800d41a28910c482100c4850aa83852bf410522e440404341040434105050c58506a08042e60630a0e0818b0a07207080e6820a852880a1718b0a856070a0850a0a0e18b0a0818b0897030701d040c349174283d0408b984f22e440804206485a022607060803041018482810200caf93a81c81d821657c91207608492d24481d8210170205010680814c001040420428322a840204607341064f011c880c9aa100b4103a0810802650810a102000c80fa084080c2a444071020682085cc210b4102840c4842650650a0d081850a1448b20e1907c0880c320e0e0440610b9419428342062c22680810c0880c3c0880c224e081702181101898110184840c285010102501201860fd022820e0802811410484c122a84022188110186431022030c862044061837063040306242820340818120185812018581c1c140d0ac061418c0610b915922031330564286c28143180c20346242034840c2860ce4584068c284c0814060a03060382041a0702038281a1581c282a081a040a824281050a2c206b040284222e838680c10201820410c08143c8384403838c0dc1060f00e1100e0d020f011a880c0d028d4863850c1428b11101c4218c1181868c203b0460620bb4604318230316018381d818482a4404c001c080810c061010c061307040080c0426020e0307018380c1c0609890411d07c061823c06101a30a15070404200e0304002500c207ea0826040a84060802a1010242032101c140e0a0486020de0804840101070380c1c0608180c150a08006070705020488064403828) else (0x3081a88b313a14407808d08062f41e040f08e2100c1e11cc0618bd24380c323c84981861045ea0e20ec0050800cc59210101e01c22018b205cc0030800dc188af313810606a8304590ad0a2840418428c4e04c0630401648400508840856030d18412c0980c41642be8186429442070d0f10ac0618b9835040458904d44848c209e030e09410c08181f43c42a026031518604c06181f238101f238118820e103103e47202603161bc30c0618150188043018098b0408032201806080c040818b08084030905020420184030c484000c406101c40610000124081000490204a0810004060a0305090104061a030509010406181429018400104061000212020100848082030c0903428100098208c082890c5c8200004c094030d02030680ba040d42203094220308458342815100812c08128804002180c202180c2a140a88050260308002180c20083e0409060241c1000e210080e210080e210080e6030908189080e107c06181cc06101cc06101e80e100041481c140c0409203080279811018604818180c0c040001a08b9101d07c061603040000802040127980c24080a04406101004082b050211682820420a1e0518603088e02a08101880028290394587038838503883850b945850b881b820e0a10370418004af93a80d80092be48a03600249692280d80090a2838541f020504302048390385043020443083e040c0910cc0818122198103a140810a14111c054881040619100488022bc4ec07504203405409d0a4071457891504182e01d625000825848a820c0a00eb0a800401c080e04108203180840381019400208008c0e20a6022840020829808804180840d01082084204e08420820d015027101a0210410840c00f103704203002440dc10805c09103704218260010410680a813b001406300081181c436181041e101041e1228916143043e121a02122c386008d09810102020aa0e184041541c346b41c24630aa83868ce458408e0ba138062040220828342a440206e8c488068608805031854070c48c0c614198b060e030401a0e084026862d850909e44041050384246060504014500a1f0509828d4146341c242700c2462440243044022198288386048866040c20c8840ec00440e40ec10640ec10440ec10542944042e685044714484471448447145842e60d044414484441428522e441070d1082050a048e03274192204029220424106101054070c20010414180c040810c091a4285161a30c08123483404145888c009010c0880c5468a2c22690a0c5864d20d00c316203f26141081880fc9800ca0840c542e04b02203101f917a0840c4822c002822c00207e0604b282100026840202642824388110186841022030d082044061a04406121040880c3420811018704410004060a10406143c220101a13204107080684)) else (if j<29 then (0x1480c41720c1842404101882e45648b91041c544208000bd17210174061604406150a406101a83080c3061010202020204a024030c08204080b8104081c8a4061010406101040810104081014020430311622203a85100a100090790c080a20e080a20e3161915040a010080d18b0808682080e08b80e1a1a020128b0545d070a03828281218a2c8386048862850c0910c40618994186143420614213225a48903128528840e18b9020111c516111050a111040610b90682b01382120e30b941862c342062c231608b931041c302e048086044062810c0880c3a1481c20101820d0459070c4c816206180430018400128061503040d020681030043018606009c04c062010c06101a040d0322283850128184a10195f01f4106a4603e820d06682085d90cc1501e800a4310528980e240c30c10bb21982803892bd066820c13a0c917428440a4301218081cd04101c420112e04201c30820dc1391480e284104243a03880874104087000407a03903704220c91742883882f50650a20e203041841d01890d6459070c5ea1020e183020f81101882f41821220e80c50822ec9748b91001c617607803a03d04283c038440307807088060f00e1100c5e81c21882a03b01181181c21882a038a2ec8620a51301c50384310528980e2aaf9230334108abe086820c18412821812018a840c4840708620a00e201cd04102703922c440807244840714404084c40409c1098b110201c214a20317722c4420760028bb95e2750390315440287901840a24588820e203003841f02203145e8ac916220838b02883e044062221045e9880a852880901832da57e820c003c8110186079090484908204406201e80e811018880c103c81101864b8108070e1e41c22018084b026030c19821420182142580c306684244870f20e048201050082811081c31580844588820e28281162220389030459890c2002e038432038a1001701021822450820b810907101710e80e182e20010bb05c41d01881001181c436430508083c8606100105c07203860b8080407203e820c1a01c117222038a62c10200812201020083424e22cc410716440243145c8820e210c20e80c30244310186840c4842ec45c880c5d8af93a40c41642be48903108e289088e289088e28b088e203085c810088828908882030a1408b20e181c20e80c317a2e4459071083e0440618b941862c342062c231608120201010045e8b90804060a03045902f206180049020440c1024090c81400c340880c240880c221a22500060b80840c1142219828038458804a01840012020110a040810a081a08b91141c402642a020604010200c04041710c116181421822e05080d642840681214083521822d05080d48608b01420b9214101521822e050807b024030c186048061c30a0f80c317684a83e0313026) else (0x14102430838424486042448604a74152204022380a91020a0832200910051a0af084b022bc4ec0750420af122a08312c24541060780e4070c09010408191ca0e10170240403024441020604888040790204049020541d020404902044410204441020483a06041010604830102443302403100910cc0900c421900c2218090c0407100089700e516191401ca2c301c40021640390186264072030c0810c4141a1502043030460408620a5122a1502043142880390504040070404010460424486043410404242840424584042458522283842ca57891206209992c24481882e40848b0d09010a))))))
def genIndex7 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (0x3c00324ffc0028ff18268016fc003c00247504f72d0928d104f91ec58498604828732c0b7c001699d8e7fcb624e1e0216477ec009610c8d4a82538b47cff440f3c003cc1bcdf56693cdefc002a843c003c00161a387fdc9d1698d6fc0eea8475fc003c003c003c0000283c003c003c003c0024107a613ee8fc0036f83c00304bbc00201e46311b03aca4dad2741e206eb45e5e087c001cbfbc003e2cd8317476d25fc6b8bc003c003c003c001afa18fe041cfc003c00242572e3bc39d860bc003c00145d16059c8e6c4b74163c003c003c003c003c00142cbed8fe1cbc001cc9321f20f3dc93185a16467c003471fc003c003c003c003c003674bc001619bc000436e0e87c003806a0a1e4c4ac2dbc003c00241480b6f0038c24c21ebc003c003c003c002d00846826fa7c003844dad8380654f57c001c3d949a2231c8c0084afc003c0a848cf257b4e5bc000cef0a083c003c003cc23c0038bbfc0004d01c4b0c2aac7ea43644e1bc002e033c003c003c003c0010313c003c003c003e32940c980fb8a420e6707c2aece4eabc003e6b3c002cd0409fbc002c32bc001085f443d880bc001052c820d8b0fc003cb5c015d81a1c973c003c003c000cd87a54247bd865483054767c000473bd082105a30120fb54435a8aec7b0408b4e31a047ed03c000cea1058804e690710dc7c003c003c003c003c003c00203b5a64008dbc003ac0bc000086fc003c0030473c00185b3c00146a7c0034407c001880621efc003c003c003448bc0030f07c0002b5fc003c003c0034f0fc003aa448d240661afece708042bc003c003c003c003c0028937c0028be3070eecf00d814ae1cecbc003c003c003c002c4e102e6c7d1cb23c0024359c23bc00104a3462a0323c000a54fc000446fc003c002c95fc003c00203dfa907c002ed5bc0010bc7c003c68bc003498fc003c00201dbc0024b53eefc4adfc0018d4fc003c003c003c002e32040e3c00062ffc00382e381b80911e1400e0044191143406616040930c54f8a260c11f062c1170c10101002c30f0e2008e0a182052a20001140c203040818008300811821a010060003220c3870c041020a1d09e1238200000018b0480a0e387830a003420008600030600293060841206145854c090030e39a0508082006e00d02027c10002000810a082001018400301018d3c04097000c39e027050000040010834800060400d0600b00800c0811824f00122039a1a0c00e16040840610681183800302204040008483023460100040040808180000c080023c0031204a0000700000000002000c40100280800a1400902144011e106000214081022018006000091e10401023c68104183800408002024818000004800a1c9800e08202020038022280031610080000c3910c0000414043830000182060810900406000000103) else (0xd8043c003c00283d0404fc0014ebbc003c001c75bc003c002c5bc84cba6f7cc8bac578f8f429d424bc003c000275bc3f7c00145b7a64bc0030533c003c002e71bc003438866afc000a5f88ee3d004896f0644078f04d589afc0038a024a91acc7c0010b2e47b40b96c42d6633c001902ee9c8ad6d0597c00308ed494267e40a3c06a04b3b465fc002451bc0010324831bc003c002caf3c003c0020f9c0bcf653bc00205e2830e095582a74dfb88240cb3c0000134e83fc003c003c0010a77ee5fc003c00261bbc003c003c0024e83c000667309ffc001682b074fc00243ef087eebd94a62ec6109bcc06e0d7c8965c9f1089188644953d037ee8bc40a89eaeb39cc982aaece768c05c6ba82f3c003c003c0030d9341c3cab50510d018632760f7c003c0020922c547c003c002833fc003c003c001a67500a10116843389dccb1c280548ca43bd4cf5e35bc0b90ee46a35c38fc001467e85f0c72c66ed0bfe042502c748a50c37c003e1162739891dc99bc00202c1cf23c0012d548862c7fbc02bc003c003e976c62e29d0c8694792459fc00284238a17c003c341893aee83c0034d958e0fc00269ffc002c51c8443c001ee59ae208cf90a3703afc0002623c00262d3c003c003c003c003c003c003c003c003c003c003c002484a250fc0006accaf4ccd2aa65fc0028f63c003c003c003022fc2b0ab45c080907e06b68e2c00f7c6718aafc0030243c0026e73c002c749ca27407c8f358d6f0c3b018d461e4a0f43ba0fcc00dbc0034c7648ebc003c003c0038133c002844a4e9547e249a7cef584970f88907b4f97c0018725210ac6940dd60d400cad8da125060c7088a908d744a54188c05caea2c52a4f02ec7d02338d37427bc003498bc003c003c003021e69b7c638687ae353428e429ac80fc003c78a449b0c0a4413c003c0039084485bc003c003c003c003c00248724593c001a0bbc003c0008b494e1480c7c000456fcc2e61e1011e834a8fc80453860fc003c001f04bc003cd78c3e9cbe9c086817ba6bc4b07c0020723c001427f490fcf0bc003c0000ae921c58e3fc003c0030a4b045445608b2bc002484e0db3c8ffc35c0c974263ec6fc003c003c0010607c003c000c17f46990ef885afca52419fc4f3c0034eafc0036fbfc002c4c7c353c003c003c003c003c00088c3c00245dbc000c8a1c6ec6937c000706e4ca78c7cccc7c003c003c003c000c7ac005bc003c003c41da0704d3bc00106aa80764d51c47fc003c003c69c808fc00142270ffd4dd1c33bc002074643fc4aa2c0378b3fc003cb5bcf9bcc140c6fc0024e52ed7247a8e67bc003d056ca23c002419bc00280960acd0fe7c000106141c68bd7c0028c9f0a73c003c003c003689b0ad7c0032d9c8bd3c003c002ed33c237c003c003c003c3d62950a7b3c00204e9e02bc003c00)) else (if j<3 then (0xc8047c002466e4af9a2f8ec13c003c003c0016647ee57c001c9778168e747c0004a8d8e5fc0024fc42143c8ae8857f07f69626480a8350e36cf3bc003c0030ae6c843c003c0002d4fc003c003c00305678b27c003c003c003c001ca6fc003c3788ca1201bc003c003c003a62bc003c0028de3c0020ed2b073c1dfc003c003c003c00100e7c003c003c003c003c003c00321d3c00340ffc003c00284fe025b85a7c0014b32e0e5e367c003c003c0004b17a72b4d2fcd33c003a0a3a0da4653c543c002ca33c0010ad3c00281840c798db84cce449c4ce3c001d01fc400c9b4cfe9891665cd0cd88aaa810d84c2ee414569cabbc94fc0038f4fc003c00340518e044dce8b1220fb6ed846f0c181492d0fa4af57c00221b3c00086afc000cf6647dbc00090392ccdc4efc00060a7c717c001876a4a9fe95f40ebc003c00067e204644e3a49280f7a2bdfc003c003c0030f834277c00006d08027c000eddbc001c9c40bdfc002000e0fef5044003fc003c003c003c003c002a710c7872566cf7ec3868fdfc002e0cb4e480c87c003c003c003e73c46b3c0024d57c002c023c001813bc003c0010a2bc002c4388b7023cd4ab28eb5202d66ba2a07c000c5eb6a40c9e306e386f90da70afcec03c003c003c003c6d80af7c001441b404b42a0ca3a82dfc00086cfc003c003282548992f5340c04213c003c003c0008acb8b914167089fc000a617c003c003c00321bfc0019043c00063bfc00141bd05206ae7c003c0016f7d0a7cc8f7c0030ed648d1c32d6bd7c0020f1fc811a0b6447b4b43c00207a208bfac3f0ac04625620f614b8f694cd6cfc1c53ecc5a0d77c7804a97c00161ab8f85a92349b38761001de12c8d47c0010a9bc0010693c003a5e6acaccba7012c4e4e0cc3c002e9e7c0022c5ff0242638eefbc003c003c003c003c003c003c003c003c95bc0011013506ac4be4033c003c003c003505fa86fc003c003c000865a4907c002c97a2d964fa04d15d04a0835097f81b4504eca8180dd8c690961902a206bc003e7530e9b81d10bb94b6a43334deb43f0a3430a8b0cf181fcae9f42cf41ad0073c001acba4fd8890062f582ee60ac8fd147136ccace2566d1f046c2fca916272e0a7845bbc003c8b7254b4fb3c0032f77810003614357caa70d1806de473fc00308bbc003ad7560efc003c003c00203ca64d547d7c003c00243e7c00288474468a57dcfadc72bc0030cabccb9c373c0028a6bc002cac4e544a39bc002454e4a5fc003077002f94bb245cf0cdfc003c0009022c99185c14380079fc0024fb88490cce7ebc7ae9a8cfee63c40a603a7c8dc23574063c003c0016043440ecb8861ce261bc0020a2f6c81672729f9631bc002cd8b088742d2009fc0000a47c0038e55c75622c6215ec3f94484e8fbc003c00108fbc003c001903fc00105f) else (if j<4 then (0x64949a823c003c003c000d0778aefc00386be41c9a107c00285788f2589ab08e3c0020447c0034b1bc003c003aaabc00186650f4bc002cde7c003ae7fc002e01fc0000c83c0010cc847e4c11bc003c003c0020b0bc26f045d8a1ac708a193c0038f2fc5d50d1ee1b7c003c001a317c002c5c7c001419043a80c4e4c47c003c003c31fc0024577c003cd3fc00306fec58563b1eaf3c001899487cbc0014057c002cc1fc003c003c003c00360c54093c0006387c0013063c003c003e62fc003c001ca57a5cbc003c3c3e81c07354ba905ec500fcbafc0030ad9ca854157c0026e2bc003c0006896c48fc003c0014703c003c002cdb7c003815bd08901ed6ffc6a2d09100e0847ed8947c00004dfc000244d8d5b4a670d6bc000cce9413ecbf629f3839bc003c00189d8c525a6cc8007c003c0014e938c2ac1512ae16f73c6344b0206c4c128293fcc52c9ca053a661d482bc003ce8bc001eda24347c0012c7561592997c0000edbc001c853c002c0780833c003c0028b34a0908f6d02bd050669abc0038fd549bbc003c003c003488fc003488bc0002b3ec9ec0edfc003c0035000cc642e37c0014603c003c000afcfc003c003c002c5080c33ae53c0004dc987cecdaecb57c003508c61f4506501fb8da882f54a07c003c00262102e660b804687c0038b9fc003c000a04fe0dfc00387dc42b60ea7c003c003c474ce1160aa10328fabc02d04db0c422e9387a7c0038ec7c003c003c00120f28599cf1bc0034247e153c000ca5bc00083c7c55bc0034d232139c8c7c003c003c00001f3020bc0008c5f6a0bc0002bfe8b8e8d8fc3b0481be3a2ccb7009bc0000d9fc0038b67e3ef887bc00266ffc0000dffc0010ec00cd1c1b3aecbc003c0024dc04f758e73c003c003c001284fc001cbe486c3c003c003c002238f82960e2202b86d7bc00145148b7fcc0d3079281bc0008e43c0036f8bc003c0022349021bc0024d73c003c00380ae4f47c003c303c003c0028dbf0706cbf269c3c013c0030e6bc0000633437fa71ec19566c3303e8142e1010c278bb7ad2bc000267f2d694b4f8573b01bc00166fbc003c003252bc00285492388ca1280ef8cbcd05141128415e6a7c0007017c39381d50815c9d7c003036a445bc8b12aefc6d5c67bc001425d00b30003c00047f7c003c003c003c00262508f43c0004f13c003c00126368f5bc003c001ca088f30c81f247ecd0a2970e5514223c003c00087bbc00102034c8c2c148376cbec4877c003d06fc001446244cfc00121afc001871a45fac4fa8abf87958537c003c00206f7c003c0018d5fc003c000450c89254ceecc132e848fbfc00145ab8ba28b76c1a50bc288f28335cd6101a986128273687fc90b2126899fc0000bca877bc0038e6fa7058267c0034b7a83e1a33fc003c0004ddbc003c00205cbc00209c) else (0x2cd6450254d0fc0006e954e6346164803efd4810bc003c003c001c287c0d46d0b455284f5c23fc00289e7c003c003c0018983c00344abc00327012cb7c003c002a82d8eed85dfc003c003455c6fb3c003c002cebf80d3c003c00343cfc003c839c55549c2af9fc003afafc003c003c00283942057c0030e47c003c002c676675c2877c003c001c0178e0208234623c003c0028eeb252fc000064bc0038124cecfc0010642ed34a96e028801ebc003c000082fc001e30ec0bc42934173c003c003c003c003c003c003c003c003c003034c49f7c003c0000883c003c003c5f7c003c0018b87474181f7c002030b0ddfc003c003c003c002001ac9698177c0028147c002c7f06bf3c000466bc0020c6382ea80cf893f0f17c003ce8fc0030f5eaf87c003c003c00385814c548e9d81204207c003c003c0010897c00207c44ffbc001e2d7c0028e2bc000eaebc00162e902d7674c483c4f53c00087760f2acc3fc002c91b814c06e66133c0014b9bb01fc2acafaa84d04e790df26137c00328f4ecab0d9bc001058c6c43c003c003c003c003c0020503c0038eb3c003c001697ba9f7aa03c002464fc003c000c57c43a38229479a4eff06c9b003c003c001a397c001863c468eeacae3460619cbdb23aad01))))
def genData8 (j : Nat) : Nat := if 38 ≤ j then 0 else (if j<19 then (if j<9 then (if j<4 then (if j<2 then (if j<1 then (0x58605110af58604d10aed86091329fb874c0309fa801db329fa801d9329fa801d7329fa801d7319fa801d5329fa801d5319fa801cd519f9801db329f9801d9329f9801d7329f9801d7319f9801d5329f9801d5319f9801cd519f887419309f887411109f88740d109f7874c4319f687859109f687851109f68784d109f687191109f68718d109f6811db329f6811db309f6811d9329f6811d9309f6811d7329f6811d5329f6811cd609f6811c1319f587191109f58718d109f5811db329f5811db309f5811d9329f5811d9309f5811d7329f5811d5329f5811cd609f487455319f487451109f48744d109ef874c8329ee82dd3319ee82dd3309ee829cf419ee829cf409ee829c5509ee829c5409ee829c5309ee821db309ee821d9309ee821d7319ee821d5319ee821d1109ee821cd609ee821cd519ee821cd109ee821c7309ee821c3319ed82dd3319ed82dd3309ed829cf419ed829cf409ed829c6509ed829c6409ed829c6309ed829c5509ed829c5409ed829c5309ed821db309ed821d9309ed821d7319ed821d5319ed821d1109ed821cd609ed821cd519ed821cd109ed821c7309ed821c3319de831d1109dd87cdb309dd87cd7319dd87cd3329dd87cd3319dd87cd3309dd831d1109dc874d9309dc874d5319dc874d1329dc874d1319dc874d1309be849cf219be849cf209be849cd219be849cd209be849cc329be841db329be841db309be841d9329be841d9309be841d7329be841d7319be841d5329be841d5319be841cd109be841c7309be841c3319bd849cf219bd849cf209bd849cd219bd849cd209bd849cc329bd841db329bd841db309bd841d9329bd841d9309bd841d7329bd841d7319bd841d5329bd841d5319bd841cd109bd841c7309bd841c3319bc8750d419bc8750d4097e859db3297e859db3097e859db2097e859da3297e859d93297e859d93097e859d92097e859d83297e859d33297e859d33197e859d33097e859d13297e859d13197e859d13097e851db3297e851db3097e851d93297e851d93097e851d11097e851cd1097e851c73097e851c33197d869d43097d869d42097d859db3297d859db3097d859db2097d859da3297d859da3097d859da2097d859d93297d859d93097d859d92097d859d83297d859d83097d859d82097d859d33297d859d33197d859d33097d859d13297d859d13197d859d13097d855d85097d851db3297d851db3097d851d93297d851d93097d851d11097d851cd1097d851c73097d851c3318fe861d7328fe861d7318fe861d5328fe861d5318fe861d1108fe861cd108fe861c7308fe861c3318fd861d7328fd861d7318fd861d5328fd861d5318fd861d1108fd861cd108fd861c7308fd861c331e716059510be282dc110bd18300910bb18400910b718500910af186009109f1809c632) else (0x640d10bf38541910bf38541110bf38540d10bf38441910bf38440d10bf38341910bf38341110bf3805d510bf3805d110bf3805cd10bf38058910bf38054910bf38050910bf3804c910bf287c1510bf287c1110bf287c0d10bf28780910bf28741510bf28741110bf28740d10bf28700910bf281c1510bf281c1110bf281c0d10bf280d9110bf280d8d10bf280d0d10bf28099110bf28098d10bf28090d10bf28085910bf28085110bf28084d10bf28059110bf28058d10bf28050d10bf2801d910bf2801d110bf2801cd10bf28019110bf28018d10bf28010d10bf28005910bf28005110bf28004d10bf186c1510bf186c1110bf186c0d10bf18680910bf18600910bf185dc110bf18580910bf184dc110bf184c1910bf184c1510bf184c0d10bf18480910bf18400910bf183dc110bf183c1910bf183c1510bf183c1110bf18380910bf18300910bf181c1940bf181c1930bf181c1530bf180d9510bf180d9110bf180d8d10bf180d8910bf180d0d10bf180d0910bf180cc910bf1809d910bf1809d110bf1809cd10bf18099110bf18098d10bf18095110bf18094d10bf18090d10bf18081910bf18081110bf18080d10bf18059510bf18059110bf18058d10bf18055110bf18054d10bf18050d10bf18019110bf18018d10bf18010d10bf08741910bf08741110bf08740d10be98009132be68290f10be68290d10be6821d910be6821d110be6821cd10be68219110be68218d10be68205910be68205110be68204d10be582dc110be58290f10be58290d10be5821d910be5821d110be5821cd10be58219110be58218d10be58205910be58205110be58204d10be58109132bda80cdb30bda80cd330bd68395310bd68395110bd6831d910bd6831d110bd68319110bd68305910bd68305110bd681cd731bd681cd331bd58395310bd58395110bd5831d910bd5831d110bd58319110bd58305910bd58305110bce8309132bce82cd332bce82cd132bcd82cd330bcd82cd130bb684ccb10bb684cc910bb6841d910bb6841cd10bb68418d10bb68405910bb68404d10bb584ccb10bb584cc910bb5841d910bb5841cd10bb58418d10bb58405910bb58404d10bae84cca32bae84cc932b9d84ccb30b9d84cc930b9d83d1540b7685d9110b7685d8d10b7685d8910b7685d0f10b7685d0d10b76859d910b768585910b76851d910b76851d110b76851cd10b768519110b768518d10b768505910b768505110b768504d10b758699510b7585d9110b7585d8d10b7585d8910b7585d0f10b7585d0d10b75859d910b758585910b758581910b75851d910b75851d110b75851cd10b758519110b758518d10b758505910b758505110b758504d10b6d8509132b3d85d0d41b3d85d0d40af6861d110af6861cd10af68605110af68604d10af5861d110af5861cd10af)) else (if j<3 then (0xb309fd87509109fd87506609fd87506509fd87506309fd87506209fd874cb419fd874cb409fd874c9109fd87491329fd87419309fd87411309fd87411109fd870c5409fd86dd5329fd86dd5309fd86dd5109fd86dd1329fd86dd1309fd86dd1109fd86dcd109fd86dc9309fd86dc9109fd86dc5329fd86dc5309fd86dc1329fd869cf209fd869ce209fd869cd209fd869cc209fd869c3319fd869c1319fd85dc9609fd85dc5609fd859db209fd859d9209fd84dd9329fd84dd9309fd84dd9109fd84dd5329fd84dd5309fd84dd5109fd84dcd109fd84dc9309fd84dc9109fd84dc5329fd84dc5309fd84dc1329fd849cf209fd849ce209fd849cd209fd849cc209fd849c3319fd849c2319fd849c1319fd849c0319fd83dd9409fd83dd5409fd83dc9609fd83dc9409fd83dc5609fd83dc5429fd83dc5409fd83dc1429fd839db209fd839da209fd839d9209fd839d8209fd839d3209fd839d2209fd839d1209fd839d0209fd82dd9109fd82dd5109fd82dd1109fd82dcd109fd81dd9409fd81dd5409fd81dcd609fd81dcd409fd81dc9609fd81dc9409fd80dd9419fd80dd5419fd80dcd419fd80dc9419fd809d3319fd809d2319fd809d1319fd809d031fe32058910fe32054910fe32050910fe3204c910fe22780910fe12700910fd23740d10fd130cc910fd13098d10fd13094d10fd13090d10fd13058d10fd13054d10fd13050d10fd1304c910fd03740d10fb24741110fb140d0d10fb140d0910fb14099110fb14095110fb14059110fb14055110fb14050d10fb14050910fb04741110fa94241120f974390f10f974390d10f8e84cca32f8d84cca32f8d4309132f728059510f726580910f726541110f726540d10f726059510f725741510f725059510f718059510f716580910f716500910f716099510f715059510f715055110f715054d10f715054910f695241520f595341530f555345531ef26741910ef160d9510ef160d9110ef160d8d10ef160d8910ef16059510ef16059110ef16058d10ef16058910ef06741910ee96241920ed96341930ed76398d10eb76499110e7565d8d10e7565d8910e756558d10e756558910e756059510df2135c221df1315c031df1305c430df1155c221df1145c221df1065c640df1065c630df1065c620df1045c620de6735cb10de6135cb10de5829c650de5829c640de5829c630de5755cb10de5745cb10de5155cb10de5145cb10dd987cc230dd7739cd10dd63784d10dd587cc631dcf3748f21dcd87cca32dcd255cf21db7749d110db64785110dae4789132d9f47cd331d9f47cd330d9e849cf21d9e839d332d9d849cf21d79305d430d75315d431d3e859d332d3d859d332cf9305d830cf7769d910cf66785910cf5315d831c7d859d830c7d859d820c7d855d830c7d855d820bf38641110bf38) else (0x10bf58484d21bf58484d10bf58480d10bf5844cb10bf5844c910bf5841cd10bf58404d10bf583d9510bf583d9110bf583d8910bf583d0910bf5839d910bf5839d110bf58399110bf58395110bf58385910bf58385110bf58381910bf58381110bf58319110bf582dd910bf582dd510bf582dd110bf582dcd10bf581d0d10bf581d0910bf58199110bf58195110bf58185110bf58181110bf58159510bf58159110bf58158d10bf58158910bf58155110bf58154910bf58150d10bf58150910bf5814c910bf58058f10bf58058d10bf58050f10bf58050d10bee820c540bed829cd40bed829c540bed8290d40bed828d132bed8258f20bed8258d20bed8250f21bed8250f20bed8250d21bed8250d20bed820c540bed8089132bdf864d130bdf854d130bdf824d130bdf804d132bdd86cd530bdd86cd132bdd86cd130bdd86cc930bdd84cd930bdd84cd530bdd84cc930bdd83d8930bdd83d8530bdd83d0930bdd83d0530bdd8395130bdd8395110bdd838d930bdd838d132bdd838d130bdd8389132bdd8381930bdd8381130bdd8358930bdd8355130bdd8350b30bdd8350930bbf8650d40bbf8550d40bbf8250d40bbe84cc540bbe840c540bbd84cc960bbd84cc940bbd84cc540bbd8494d40bbd8490d40bbd8454d40bbd844cb40bbd844c940bbd840c540bbd83d1540bbd83d0940b7e850c540b7d85d8930b7d85d8550b7d85d8530b7d85d0d10b7d859d932b7d859d930b7d859d132b7d859d130b7d858d930b7d858d132b7d858d130b7d8581930b7d8550d50b7d850c540afe860c540afd86cc960afd86cc560afd860c5409ff8758f209ff8758e209ff8758d209ff8758c209ff8750f209ff8750e209ff8750d209ff8750c209ff865d1309ff865d1109ff865c9109ff855d9109ff855d1309ff855d1109ff855c9109ff845d9109ff845c9109ff835d9109ff835d1109ff835c9109ff825d9309ff825d9109ff825d1309ff825d1109ff815d9309ff815d1329ff815d1309ff805d1329fe87d09109fe87cc5609fe87cc5409fe87991109fe878c5409fe87591109fe87589109fe87545609fe87509109fe874c5609fe874c5409fe870c5409fd87d89309fd87d85509fd87d85309fd87d0d109fd87d09309fd87d09109fd87d05309fd87cc9609fd87cc9409fd87cc5609fd87cc5409fd87991109fd87985409fd87951309fd87951109fd8794d409fd87945409fd878c5409fd87885409fd87595109fd87591109fd8758f209fd8758e209fd8758e109fd8758d209fd8758d109fd8758c209fd8758b309fd87589109fd87586409fd87586309fd87586209fd87551309fd87551109fd87549109fd8750f219fd8750f209fd8750e609fd8750e509fd8750e209fd8750e109fd8750d219fd8750d209fd8750d109fd8750c209fd8750b319fd875))) else (if j<6 then (if j<5 then (0xdbd4750e60dbd4750e50dbd4750e20dbd4750e10dbd4750d10dbd4750c20dbd474d230dbd4749332dbd4745210dbd4741330dbd4741310dbd43dc540dbd435c341d7e7558c20d7e7550c20d7e655d110d7e655c910d7e5755130d7d7654b50d7d7558c20d7d7550c20d7d5755110cff6758e20cff6758c20cfe7650c20cfd839d820cfd835d820cfd7650c20cfd6759110cfd6758e20cfd6758e10cfd6758d10cfd6758c20cfd6741b30bfb8641110bfb8541930bfb8541910bfb8541110bfb8441910bfb8341910bfb8341110bfb8141930bfa80cc560bfa8099110bfa808c540bfa8059110bfa804c560bfa800c540bf986c1530bf986c1510bf986c1110bf986c0d10bf984c1910bf984c1510bf984c0d10bf981c1940bf980d8930bf980d8530bf980d0d10bf980d0910bf980cc960bf980cc560bf98099110bf98098540bf98095110bf98094540bf98090d40bf98090540bf9808d930bf9808d130bf9808c540bf98088540bf98085110bf98081930bf98081110bf98059510bf98059110bf98058e10bf98058d10bf98055110bf98050e10bf98050d10bf9800c540bf78759510bf78758d10bf78750d10bf7865d110bf7865c910bf78650d10bf78645110bf7855d910bf7855d110bf7855c910bf78558d10bf78550d10bf78545110bf7845d910bf7845c910bf78459510bf78458d10bf7835d910bf7835d110bf7835c910bf78359510bf78345110bf7825d910bf7825d110bf78259510bf78258d10bf78250d10bf78245110bf78159510bf78158d10bf78150d21bf78150d10bf7805d110bf78058d10bf78050d10bf687d9110bf687d8910bf687d0910bf68799110bf68759110bf68758910bf68750910bf68719110bf686dd510bf686dcd10bf6869cd10bf68694d10bf6865d510bf6865cd10bf68654d10bf6861cd10bf684dcd10bf684c4d10bf6849cd10bf68484d10bf6845cd10bf68444d10bf6841cd10bf68404d10bf683d9110bf68399110bf68359110bf68319110bf587d9510bf587d9110bf587d8d10bf587d8910bf587d0d10bf587d0910bf58799110bf58795110bf58759510bf58759110bf58758d10bf58758910bf58755110bf58754910bf58750d10bf58750910bf5874c910bf58741910bf58741110bf58719110bf586dd510bf586dd110bf586dcd10bf586dc910bf586cc910bf5869cd10bf58698d10bf58694d10bf58690d10bf58684d21bf58684d10bf58680d10bf58655110bf58654d10bf58654910bf58650d10bf5864cb10bf5864c910bf5861cd10bf585d9110bf585d8d10bf585d8910bf5859d910bf58585910bf58550d10bf584dd910bf584dd510bf584dcd10bf584dc910bf584dc110bf584cc910bf584c5910bf584c5510bf584c4d10bf584c4910bf5849cd10bf58498d10bf58494d10bf58490d) else (0x76058d10ef567d9510ef567d9110ef567d8d10ef56759510ef56759110ef56758d10ef565d8d10ef565d8910ef56558d10ef56558910ef56159110ef56158d10ef56058f10ef56058d10edd63d8530edd6381930edd6358530dfb7641110dfb065d130dfb065d110df9849c031df9845c221df9845c031df976c1110df976c0d10df97641110df97640e10df97640d10df906dd130df906dd110df906dcd10df906dc930df906dc910df906dc530df9065d130df9065d110df9065ce40df9065ce20df9065ce10df9065cd20df9065cd10df9065c910df9065c640df9065c630df9065c620df9055c910df904dc910df9045c910df9045c620df7765d110df7765c910df77645110df77644910df7755c910df77544910df7745c910df77444910df7705d110df7165d110df5865c660df5865c650df5865c640df5865c630df5865c620df5845c660df5845c650df5845c640df5845c630df5845c620df576dd110df576dcd10df576dc910df5765d110df5765cd10df5765c910df57645110df57644d10df57644910df5755c910df57544910df574dc910df574c4910df5745c910df57444910df5639c620df5639c420df5635c620df5635c420df5439c620df5439c420df5435c660df5435c650df5435c640df5435c620df5435c420df5345c630df51758640df51758630df51758620df51750660df51750650df51750640df51750630df51750620df516dd110df516dcd10df516dc910df5165d110df5165cd10df5165c910df5155c910df514dc910df5145c910df5145c221dee7448f20dee7448d20dee274c940dee2748560dee2748540ded7648f21ded7648f20ded7648d20ded7648620ded7448620ded2758b30ded2758910ded2754910ded2750910ded274c910ded265cf20ded265cd20ded045cb10ddf764d130ddf3758f20ddf3758e20ddf3758d20ddf3758c20ddf3750f20ddf3750e20ddf3750d20ddf3750c20ddf365d130dde374c910ddd869cc20ddd865cf21ddd865cc20ddd849cc20ddd845cf21ddd845cc20ddd76cc930ddd764cb30ddd764c930ddd74cc930ddd744cb30ddd744c930ddd3758f20ddd3758e20ddd3758e10ddd3758d20ddd3758d10ddd3758c20ddd3750f21ddd3750f20ddd3750e60ddd3750e50ddd3750e40ddd3750e20ddd3750e10ddd3750d21ddd3750d20ddd3750d10ddd3750c20ddd374cb41ddd374cb40ddd36dd130ddd36dc930ddd36dc530ddd34dc930ddd34dc532ddd34dc530ddd34dc132ddd345cb31ddd345cb30ddd345c331dbf7650d40dbf7550d40dbf4750e20dbf4750c20dbe7458c20dbd839d020dbd835d020dbd825d332dbd809d031dbd805d332dbd805d031dbd7550d40dbd7458c20dbd47d0d10dbd4799110dbd4795130dbd4795110dbd4759110dbd4755130dbd4755110)) else (if j<7 then (0x454d10ff1044c910ff10444d10ff10444910ff10440d10ff1041cd10ff10404d10ff103d8910ff103d0910ff1035c910ff10358910ff10350910ff10344910ff06440d10feb2058e20feb2050e20fe92641520fe90649520fe90648d20fe90648620fe90448d20fe90448620fe6244c910fe52758910fe52754910fe52750910fe5274c910fe5264cb10fe5264c910fe52484d21fe52158910fe52154910fe52150910fe5214c910fe51448d21fe51258620fe51250620fe5045cb10fdb064d130fdb054d130fda6341930fd96341930fd93058e10fd93058d10fd93050e10fd93050d10fd9304c910fd906cd530fd906cd130fd906cc930fd9064d530fd9064d130fd9064c930fd9054d130fd73758d10fd73750d10fd73650d10fd7318c540fd73158d10fd73150d21fd73150d10fd73058d10fd73050d10fd6374c910fd53758d10fd53750d10fd536cc910fd53690d10fd53650d10fd5364cb10fd5364c910fd534cc910fd5344cb10fd5344c910fd53158d10fd53150d10fd53058f10fd53058d10fd53050f10fd53050d10fcd3258f20fcd3258d20fcd3250f21fcd3250f20fcd3250d21fcd3250d20fcd23d0930fcd2358b30fcd2358930fcd2348530fbb0650d40fb940d0d10fb940d0910fb94099110fb94095110fb94059110fb94055110fb94050e20fb94050e10fb94050d20fb94050d10fb94050910fb90651540fb90650d40fb74750d10fb74650d10fb74550d10fb74150d10fb74050d10fb64655110fb547d0d10fb54799110fb54795110fb54759110fb54755110fb54750d10fb54741310fb54650d10fb54550d10fb541d0d10fb54199110fb54195110fb54159110fb54155110fb54150d21fb54150d10fb54050f10fb54050d10fae244c940fad2448540f9d43d0530f9d4395130f9d4381130f9d4355130f9d4350530f9d4341330f9d4341130f9d34cc940f9d34cc540f9d344cb41f9d344cb40f9d344c941f9d344c940f9d344c540f7a6541110f7a5059510f795059510f795055130f795055110f795054910f778059510f768759510f76655d110f76655c910f766558d10f766550d10f766545110f766544910f765759510f758759510f758059510f756799510f7565dd110f7565dcd10f7565dc910f7565cc910f75659cd10f756598d10f75655d110f75655cd10f75655c910f756558d10f75654c910f75651cd10f755759510f755755110f755694d10f755655110f755654d10f755654910f755494d10f755159510f755155110f748759510f6d2548550f5e5355130f3d5494d40f3d5454540f3d4550d50f3d4550550efb6341930ef96341930ef960d8930ef96059510ef96059110ef96058e20ef96058e10ef96058d20ef96058d10ef96058930ef96058910ef76759510ef76758d10ef76558d10ef76158d10ef) else (if j<8 then (0xc910dfd764c520dfd7648530dfd755c560dfd7559110dfd7558910dfd7558540dfd7558520dfd745c910dfd744c910dfd744c520dfd7448530dfd735c560dfd735c540dfd7358910dfd7358520dfd7350910dfd7350520dfd655c910dfd635c910dfd435c910bff865d132bff865d130bff865d110bff845d932bff845d930bff835c540bff825d110bff815cd60bff815cd40bff8158d20bff8150d20bfd87d0910bfd87cc560bfd87cc540bfd8799110bfd878c540bfd8759110bfd8758910bfd8754560bfd8750910bfd874c560bfd874c540bfd870c540bfd8654910bfd864c910bfd864c520bfd8648530bfd8548560bfd844c910bfd844c520bfd8448530bfd8348560bfd8348540ff3805d110ff37680910ff37641110ff37580910ff37541110ff37480910ff37380910ff3705d110ff36540d10ff36440d10ff31641110ff31541110ff3065d110ff30650d10ff30645110ff3055d110ff30558d10ff30550d10ff30545110ff30458d10ff28741110ff28640d10ff28440d10ff28341910ff28341110ff28058d10ff28050d10ff27641510ff27640d10ff27440d10ff26741910ff26440d10ff26058d10ff25440d10ff24741110ff24141110ff24050d10ff23058d10ff23050d10ff21641510ff21640d10ff21440d10ff20741110ff20640d10ff20440d10ff18640d10ff18541910ff18440d10ff18341910ff18341110ff18059510ff18058d10ff18050d10ff176c1510ff176c1110ff176c0d10ff17680910ff17641510ff17641110ff17640d10ff17600910ff17580910ff17541110ff174c0d10ff17480910ff17440d10ff17400910ff17380910ff167c1910ff16741910ff16580910ff16541110ff16540d10ff16440d10ff16380910ff16300910ff16098d10ff16059510ff16058d10ff15440d10ff147c1110ff14741110ff14380910ff14300910ff141c1110ff14141110ff14090d10ff14050d10ff130d8d10ff130d0d10ff13058d10ff13050d10ff116c1510ff116c1110ff116c0d10ff11641510ff11641110ff11640d10ff11541110ff114c0d10ff11440d10ff106dd510ff106dd110ff106dcd10ff106dc910ff106cc910ff1069cd10ff10694d10ff10690d10ff10684d10ff10680d10ff1065d510ff1065d110ff1065cd10ff1065c910ff10655110ff10654d10ff10654910ff10650d10ff1064c910ff10645510ff10645110ff10644d10ff10644910ff10640f10ff10640d10ff1061cd10ff105d9110ff105d8d10ff105d8910ff1055d110ff1055c910ff10559110ff10558d10ff10558910ff10550d10ff10545110ff10544910ff104dcd10ff104dc910ff104cc910ff104c4d10ff104c4910ff1049cd10ff10498d10ff10494d10ff10484d10ff10480d10ff1045cd10ff1045c910ff10458d10ff10) else (0x10ff90654d40ff90654910ff90654540ff90654520ff9064c910ff9064c520ff90648530ff90559110ff90558910ff90558520ff9045c910ff9044c910ff9044c520ff90358910ff90350910ff7865d110ff7855d110ff7835d110ff7825d110ff7805d110ff77559110ff77558910ff773d0910ff77358910ff77350910ff7645cd10ff664dcd10ff6645cd10ff58759510ff58758d10ff58750d10ff5865d110ff5865c910ff5855d910ff5855d110ff5855c910ff5845d910ff5845c910ff58459510ff5835d910ff5835d110ff5835c910ff5825d910ff5825d110ff58259510ff58258d10ff58250d10ff58058d10ff58050d10ff58045110ff5765d110ff5765c910ff57655110ff57654910ff57650d10ff5764c910ff57645110ff57644910ff575d9110ff575d8910ff57559110ff57558910ff5745c910ff57458d10ff5744c910ff57444910ff573d8910ff573d0910ff57358910ff57350910ff56759510ff56758d10ff5655d110ff5655c910ff56550d10ff56544910ff564dcd10ff5645cd10ff56454d10ff5635c910ff56344910ff55458d10ff54750d10ff5435c910ff54344910ff5174c560ff5165d110ff5165c910ff51655110ff51654910ff51650550ff5164c910ff5164c520ff51648550ff51648530ff51559110ff51558910ff51548560ff5145c910ff5144c910ff51448530ff51358910ff51350910ff4645cd10fed8258f20fed8258d20fed8250f20fed8250d20fed2758910fed2750910fed2654520fed264c910fed264c520fed2648530fed2558520fed2548560fed244c520fed2448530fed2358520fed2350520fed2348560fed2348540fdd824d132fdd824d130fdd804d930fdd804d132fdd804d130fdd764d130fdd365d130fdd364c910fdd364c520fdd3648530fdd344c910fdd344c520fdd3448530fdd3258530fdd3250530fbd8250d40fbd8050d40fbd4799110fbd4759110fbd4558540fbd435c540fbd4350520fbd4348540fbd424c540f7d5654910efd6759110efd6558910efd6358520dff865d130dff865d110dff855d130dff855d110dff835d110dff825d930dff825d130dff825d110dff815d930dff815d132dff815d130dff805d132dff7559110dff7558910dff7358910dff7350910dff7254560dff724c560dff724c540dfd8758f20dfd8758e20dfd8758d20dfd8758c20dfd8750f20dfd8750e20dfd8750d20dfd8750c20dfd865d130dfd865d110dfd865c910dfd855d910dfd855d130dfd855d110dfd855c910dfd845d910dfd845c910dfd835d910dfd835d110dfd835c910dfd825d930dfd825d910dfd825d130dfd825d110dfd815d930dfd815d132dfd815d130dfd805d132dfd765d132dfd765d130dfd765d110dfd765c910dfd7655110dfd7654910dfd7654520dfd764))))) else (if j<14 then (if j<11 then (if j<10 then (0xda22f468bcce2f118bbdc2edc8bacc2e8c0b9c62e570b8fc2e248b83c2df70b7542dbd0b6762d830b5702d3a0b4882d000b3962cc10b2682c780b14e2c368b05c2bf28af422bae8ae502b798ad862b470aca82b0a8abb62ad58aae22a9e0aa182a6b8a9582a408a8982a068a79c29d18a6f029a40a626296f0a552293f0a4b029140a3f028e40a33028b68a284288b8a1b028518a0dc281a09ff427d389ed0278d09dc0275089cd8271909bf026da09b0826a789a482675099742640098a0260d897a425c489680258309598254b894b0250c893c824d2892d62498891e42459890e8241f8901e23ed08f04239f08dcc235108cc6230808bac22ce08ace229b88a0422618893a222a0881621eb0874221b10865a217988572214208494210d0839820c4082a62091881c82052880cc201607fee1fde87f2e1fb387e6e1f7487d4a1f3587c6c1ef907b701ec187ab01e96879e61e5c879081e2a0782a1ded8774c1dc0076a01d8d875b81d4c074941d00873841cc1872741c7b0716e1c39870681bff86f801bc086e8e1b8686db01b4a06cbe1b1006bcc1ace86aa81a88069981a44068881a000678c19cb066ae198c065b2194f864d41918063ba18ca06296188886186183f8607617fb85f7a17c405eb0178c85db4174d85cc2171605bda16e385b1016a705a28166a85936162e0585815f68577015bf056b01591855e6155f0551c152a0543414ed8532e14b3852781483851ae1453850ee141704ffc13e704f2813af84e68138484da8134a84ca2131304bd812db84b0412a684a26126a04966123a0486a1202847aa11d5046fe11a504634116b04542113b0447811038439010c484294108a841c01055840ec10230402c0ff083f580fbb83e660f7283d420f3883c6e0efc03b720ec203a9e0e8a839c00e58038f60e20838040de90374e0db9036840d84035880d3b034500cf98337c0cbf832bc0c9e8322e0c760318c0c46030d60c25030520bff02fb00bca02ea00b8102d720b4202c940b0802bb60ad302ace0a99029f00a61828ea0a200281609e38271a09a20260a096d02554093d0249e0912023de08df8231e08af8222c08708215808390207007f501f6a07c281eaa078381da4074e81cda071201ba206ce01aba068a019be0650018e0061b0180c05e60170605a98163205658151805268141c04ec8136604c40129c048a011b40450010f404278103e03e880f1a03a200e1e036a80d36033580c76030580bc002da80af60299009fa02640091c02318085c02018079201c2806960190005d6015b0050c012b0043800e98033c00b48026800780018a004d000de002200000ff98541930ff98541910ff98341930ff98341910ff98341110ff98141930ff98141110ff97641110ff9065d130ff9065d110ff9065c910ff90655130ff906551) else (0x5649950065209940464e19931264a79923e64729916a643b19082640398fa463d118ec6639718dd4636218d0a632098c1862e918b2662af18a3e627298942622c1881461e3186fa619a185f46153984c6610d1839860c19828860801816e6034980225fdf17eea5f9117d9e5f3e17c705efc97b885ec297a8c5e7c1795e5e35978585df69773e5dab176105d62175145d1e173f05cd5172b85c89971a85c459708e5c0696fa65bca16eb45b8b16da45b4996c9e5b0d16bd45ad316ace5a94169d25a55168cc5a13967bc59cd166b65990965b0594a1649659061638658ba9625858719612a58301604257f615f6457b995e54577595d58573b95c98570b95bc456d915ae6569c959fe56629593456351586055fb1579655cd956ea55a29562a556d9552e5536154785501153a454ce952a85492151de545a95114542f95068540214f9453ca94eb6539594e00536594d36533094c3a52ea14b3e52b014a4252711495a52371485e51fa9477651c094684517f1457e514014496510b143cc50db142f850a39421a506e941465032140404ff813f804fc093e7a4f7f13d7e4f4513c8c4f0393b904ec993a9e4e88139ac4e50938c44e11937c84dd0136c24d93935da4d54934de4d1a933f64cde1330e4ca6932264c6c931344c2d9302e4bee92f3c4bb492e5e4b7a92d764b4092c984b0692ba64ac792aaa4a8b129b84a4e928c64a14927d449da926f649a09260449641251c492a1243448f29235648bb122824886121ae4853920f848261203847f111f5047b711e72477a91d80474591c98470911bba46d691ae6469f11a1c466f119664646918ba460c917aa45d0116cc4593915e44559914f2451f9140a44ea9134a44b81126c447b911844446910b0441190fdc43da10eea439d90df8436110d1a432990c1e42e590b0442a410a3042719095242379086a41fb1077841c1106864187105b2414f904c04113103ce40d6902e6409c901e04056100bc40120ffde3fe70ff323fb70fe683f780fd6c3f3e0fc7a3efc8fb743ebd8faa03e928f9ea3e678f9483e3a0f87e3e0c8f7b43dd00f6c23d8e8f5b23d480f4a23d068f3923cc28f2823c7c0f1683c358f04e3bf68ef5c3bba0ee7e3b828ed963b4b0ecd63b1b0ec163ae88eb383ab38ea643a6d0e92c3a1f0e7ea39e28e70c39a88e64239760e56e39370e44038df0e2ea38a28e1f8385e8e10638270e03c37f98df5437b30de1c37600dd0c372b0dc1a36e98db4636b20da3636640d91236228d7ee35d70d6d435818d57e353d8d46434f70d37234ae0d22634588d0d034198cfd433bf0ce7e33800cd6e333e8cc6832fd0cb7632be0ca8e32890c988323d8c88232038c79031c48c69e318a8c5b631530c4ec31190c3d230d28c2b830938c1d030548c0e830180bff62fde0bf182fab8be582f808b)) else (if j<12 then (0x62b09891a61d29852a60b8980ea5fc697d4a5ed49795a5dce975ba5d049726a5c2696ef25b5c96b7a5a7e9687a59a09643a58909607257a895caa56989581a557e9545254a0950da53c294d6252ee94a62522e946ea5150943c2506893faa4f7693c0a4e70937ca4d7e9338a4c5092efa4b5e92b5a4a3a926f2495c92302482491e2246e2918ca458c9146244b89109a439e90caa42b6908e241b09047a4096900623fae8fc9a3e948f7e23d668f3a23c748ef623b468ea823a048e64238ea8e16237f88de1237248daea363c8d74a355e8d3fa346c8d032335c8cb7a327e8c85231be8c4b230c28c0ea2f948bcaa2ea28b8ba2dc48b5422cf08b2422bfe8ae7a2b488aa622a068a55a28ba8a14227dc89dca26f489a52263e8977a257e8947a24aa8915223e088dda230288a3a221a88762216e8848a20c2881621ff887dea1f2e87b121e5a878121dae875621cf8872621c1a86e9a1b3286aaa1a368670a19448631a185c85fa2177e85c2a16a0858da15c28553a14da8519a140684e4a133284afa124a847aa11768445a10ac840e20fd883e0a0f1883aba0e62837920d66833ca0c7482fda0b6e82c120a908284a098a8243208988209207c481d1a06d2819a205ea81652052081302044280f3a035a80b72026880782016c803ba006680019ffb07fd19fedc7f9f1fe087f601fd027f1e9fc067eec1fb467eb99fa867e899f9bc7e571f8de7e1d1f8147dea9f72c7da91f6267d679f53e7d379f4747d079f3b47cd29f2ea7c9d9f2027c639f11a7c299f0507bf71ef687bbd1ee947b881edac7b531ecec7b1e1ec047ae91eb307aaf1ea5c7a819e9b07a569e8f07a241e80879e79e75279ba1e692798c9e5d279529e4e0791b1e40c78e89e32e78bb1e29678929e1e078561e0ee781e9dff277dd1df0077a31de1877709dd7677481dcd4771f9dc1476e81db2c76ae1da4476791d98476491d8c476169d7f075df1d6fe75aa1d63e75779d57e75401d4a0750d9d3b874d61d2ee74a39d21a74699d13c74321d04073eb9cf5873be1ce98738e1cdc4735e1cd2c73359cc8a730d1cbd472da9cb1472ad1ca4072781c976723b9c89871ff1c76071b61c646716f9c56871421c49e71121c3d470df9c31e70b49c24a70731c14e70341c0486ff51bf606fc01bea06f8b1bdae6f539bcf86f1e9bc066ee21bb146ead1ba4a6e7a9b98a6e459b88e6e069b7c46dd69b6be6d8b1b5cc6d511b4b26d149b3c06cd09b2ce6c969b1f06c5c9b0fe6c1d9afe46bd99aede6b959adba6b4a1aca06b089ab9a6abf9aa766a831a9ac6a491a8886a001a78269c11a67c697a9a55869369a45268f29a36068b61a26468799a172683d1a08a680819fa267ce19ec4679419ddc675799ce0671619bd066d719afc669f99a006663199186621997ea65e29970265a39961a6) else (if j<13 then (0xc009afff8bff52ffa6bfde2ff2cbfb82fea8bf9c2fe42bf852fdbebf642fd62bf482fce8bf2eafc8cbf17afbfebeea2fb70bece2fae2bea82fa68be912fa20be7caf9babe632f94abe44af8dabe28af860be07af7fabdf0af7b2bddc2f756bdccaf704bdb5af694bd9c2f624bd762f5bebd5f2f53abd432f4debd29af478bd102f408bcf6af3cabce22f378bcd52f344bcc5af306bcb8af2bebca6af262bc8d2f206bc762f1aabc5f2f14ebc482f0f2bc29af08cbc1a2f026bc00aefd4bbec2ef82bbd52ef26bbbbaeeacbba4aee64bb902ee12bb80aedb6bb5faed46bb4b2ecf4bb2f2ec98bb1d2ec50bb0b2ec08baf92ebc0bae72eb78bad02eb08bab6aeaacba9faea64ba902ea1cba7e2e9d4ba6c2e982ba57ae93aba45ae8e8ba2eae882ba0dae7eab9ecae77ab9ce2e700b9b4ae6a4b9a02e63eb9842e5c4b965ae55eb949ae4eeb932ae49cb91e2e454b9072e3d0b8eb2e39cb8e0ae354b8ceae320b8b7ae2bab8a82e286b89b2e22ab881ae1ecb874ae19ab85dae152b84bae114b83eae0c2b822ae048b8042dfd8b7e5adf68b7ceadf0cb7b52dea6b79e2de54b78c2de02b777addbab7632dd68b74eadd02b7352dca6b720adc5eb709adc02b6f7adbc4b6eaadb90b6db2db52b6ce2db0ab6b9ada68b67fad98ab64aad8b6b6132d7e2b5d6ad6c8b5902d5c2b553ad4dab519ad3deb4d82d2e2b4992d1d2b45a2d0e0b41dad00cb3e62cf1ab3a9ace32b36aacd36b3332cc62b2f92cb7ab2ba2ca88b2852c9b4b24b2c8a4b2072c79eb1c82c6b6b195ac600b1632c4f0b121ac408b0e2ac2f8b09eac206b0622c11eb02aac040aff0abf44afb42be5caf7a2bd60af3b2bc82af062bbaeaed3abaeeae9eab9fcae55ab8baae11ab7d2adda2b6f4ad93ab5d0ad4d2b4d4ad15ab3e2acde2b304ac9cab1f4ac602b10cac23ab006abdfaaf00aba32ae18ab66aad08ab22aabe4aad72aad4aa982a9ecaa5baa8dcaa152a7c2a9ceaa6a8a985aa5a2a94baa4b0a911aa3b4a8c62a286a8782a158a82f2a02aa7e129ef2a79829e0aa765a9d04a71f29bf4a6db29ae4a692299caa650a98b0a60a2978ca5c12969aa58229580a540a947aa4fca936aa4b629246a4772917ca43829058a3f1a8f2aa3a628e06a36728d1ea32828c18a2e928b1ca2a2a89f8a25ea88fca2272883ca1f9a877ca1c4a86b2a18fa85e8a16228514a120a8404a0e1a82fea0a028216a06628106a0222800a9fe327f229fa927e3a9f7ba7d849f4927cb09f16a7bd29edca7af49e96279f89e68a79429e38a78789e03a779a9dc9a769e9d85a75a29d49274a69d05273969cc6272c29c9b2720c9c63a71109c2226ff69bdba6ee69b9526dcc9b53a6cc69b19a6be89adfa6b0a9aa826a2c9a6ba69449a31a685299fa2677499c0266829988a65ae994c264b2990d263ac98c6a) else (0x348b41d8621703c00a05e1384a1122c8861d8621704c0f02302325c1584e1083c8bc288861d8621704c04e05e128420e22d0761885c0f0028110380d22c8a2258861d86c1303c08c0348b228896210761b03c0090481122c8a2258861d86c1303c08b0388b228896210761b03c0090400c22f0a41d8621704c0f01c00b0cc1a0480e2340cc298841d86c1303c0700380d2298841d86213032070024320640d0330a6208761883c04802c340cc320ba1a8660f8358b629892208680e003cbd2ec340ba0e62d892208681202800c0c8300be1183a0d22c8a22704c0f0230320c02e8460e8348b2288941f03c00c2f4bb8448b225078120380b0028328448b2260480e021c328388b2288901e0380082f4bb8388b2288901f0480f02800b0c8300be128448b22889c1303c08b0c8300ba128388b2288941f03c00b2f4bb8488b2288941f0480f02c00b0ca0d22c898120380870ca0d22c8a2240780e0020bd2ee0e22c8901e0480a0024190601705a118420f83a0d22c8821704c0f023c1584a118420f83a0d22f0a22085c1301341a052138461083e0e8348b2210721703c00e05e1384a1122c8821704c0f022897056138420f22f0a22085c13012c17052128420e22c8841c85c0f002c3d0ee0e228890200680e0024110380d22c8a22704c0f0224110380d22c8a22507c0f0024120448b22889c1303c0880480e22c8a22507c0f0020100308bc288841c85c1303c07002c330701a264120388d0330a41f04c0f01c00e064950340c2290721303207002832064940340cc288720f01200a0c8110358a6248821c86c1303c08b0350a6248821c86c1301203d0458a6248821c86c1303c08a03d0a6248821c86c130120100310a62488c1c85c1303c07002c1a0480e2340c62d0a62707c1303c070034190340c62c8a6270721303207002c0d62d0a6248720f0120080c81103c0d2208721b04c0f0228320440f0350a2208721b04c04a0f4130448821c86c1303c0890cc1303d0a2208721b04c0490400c22d0a2230721704c0f01c00b0cc1c068990480e2340c42b07c1303c070038192540d0308ac1c84c0c81c00a0c8192500d0310a21c83c048028370d0300b88b0288901d03400a0a0220701a0541003c0c02a0700d82800d0d02e050100380c01c8220340b8140400e0300720880d02e050100380c01c8220340b8140400e0300720880fa360ce2908c228741a8581003c8a808dc35030d08c336b0cacc31fb0c46c30630be0c2ecb0b7ac2d0b0b14c2b9b0accc2a7b0a8ec29fb0a46c28db0a12c279309b6c269b096ec24db0926c23e308cac224b0864c20db0808c1f6b07a2c1dab0732c1beb06c2c1a530652c18bb05e2c16ab057cc153b04f8c128b046ac107b03e6c0e930362c0c8302f2c0a730246c083b01ccc0653015cc04bb0100c034b0086)))) else (if j<16 then (if j<15 then (0x301003c8e2360bc2a0881504c04a0408f0388d82e08c1e0540f0028280420e22b0881f0621003206002c150420e22a07c148400c81800a0680f8388a81c8400c8180090408f22b0881f062110320700281023c0c22b08c1f0521103207002c1c0689503e0e0308ac1c8440c81c00c0440e0348b22889c1d03c0090480e22c8a2270740f0020320440f0370a2208721904c04a0cc1303f0a2208721904c0490400c22f0a223072150440f01c00b0b821048910400e2370bc2b09c1d03c00d0cc1b068132441003c8e2370ac2307c1904c04f0cc1c06899048910388d0330ac1d0440f01c00f064950340c22b0721103207002832064940340cc288720f01200a0410e0308bc2888c1c85c1303c0700308b2288941d0340064288821c8641101180d22c882150440d021c0e0350c428882150440480350c22d072150340070400c22f0a2230721704c0f01c00b22c8a2250740d00190a2208721904404622c882150440d02181003d0c428882150440480390c22d072150340070cc220580f2358bc29886160480e02c04d0d8210580e2358b623076160480e02c00d0cc220601003c8e2358bc298861604c0f02c04f0dc2105c100388d62d88c1d85c1203c0b003832080160358b6218581203808a0440e0348b2288962185c1303c08b0440e0348b228896230761703c00b0481122c8a2258861704c0f0228120388b228896230761703c00a0c81103c0d62c8821c8661704c0f0230320440dc288821c8661704c04a0f4130458b2208721985c1303c08b0cc1303f0a2208721985c13012833070120388d0318bc2988c1d85c1303c07003c0d0308a6230761484c0c81c00a0c80d0318bc288761483c0480283308a1d068990580f2370a8120380b0134b98bc212640e237078120380b002c3308a1f068990400f2388dc2a04c0f02c04e2e630084990400e23707c1203c0b0030320821d0640d8120380880440e0348b22889c1303c0890440e0348b22889c1f03c0090481122c8a22704c0f0220120388b22889c1f03c0080c81103c0d2208721b04c0f0228320440dc288821c86c1301243d04c112208721b04c0f02243304c0fc288821c86c130124330701a264120388d0330ac1f04c0f01c00e064950340c22b0721303207002832064940340cc288720f01200a0541003c8e2350c42a0881504404b0d0140400e2350c82d0781503400b084204761183a0d22c8a2258861d86c1303c08f8460d22c8a2258841d86c0f00288b2258841d868120380b00241d8448b2258861a0480e02242509120476128448b228896218761b04c0f023e128388b228896210761b03c00a22c8a2258841d86c1203c0b00281d8348b2258861a0480e0224178461083e0e8348b2218761885c1303c08e0841584a118420f83a0d22f0a2218761885c130142138460f8) else (0x5c1584e1083c0bc280801704c04c05c1484a108380b0210701703c00b258100308b429892230721703c00b070122440e2340c62d0a62707c0f0030100300a62488c1c8501303007002c1c0388d0318b02989c1c04c0c01c00c258100308b2230721703c0092e4b207099048910388d03307c0f0030100300a2230721404c0c01c00a070150388d0300ac1c04c0c01c00b0448b220850100300870c8190500f0380d0300700c00280d22c8a22587c1103c098024114388b2288961f0440f02600a0c80f0348821b0440f0260090c8110370a2208721b0460f01600b0f413045104388821b0440f02600b0cc1303d0ec288821c86c1183c058030330681303c8dc2b0841f06c1183c058034110380d22c8a2270440f0224120448b22889c1103c0880c81103c0d2208721b0440f0228320440dc288821c86c1301243d04c112208721b0440f02243304c0fc288821c86c1301243306c1a04c1003c8e2370ac2107c1b04c04e0480e4348b2288981e0380090310a222072150480d018009069150388d0310a81d0480d01800b080190540f0380d0300a0100128100308b2250740e0140080308b82907215038050021344500e2340c8290740e01400a05c96051104300a22488c1c85c0f003021048910400e2350c22c0a22707c0f00340e0348b22504c0f0260480440e0348b22889c1d84c0d81c00b048114410f22c8941303c098128120388b22889c1d84c0d81c00a0c80d6288821c8641303c0981283d0450f6288821c8641303c09812c210480e2370b42b09c1d84c0d81c00c0390a21c834048018402641725814028892230721703c00c08412244100388d22c0a22707c0f0030110380d22c8a22504c0f0224110380d22c8a22707c0f0024120448b2288941303c0880480e22c8a22707c0f0020320440f0348821c8641303c08a0f4130448821c8641303c0890b8210481023c0e2370b42b09c1f03c00d0cc1303d0d8288821c8681201280c22e0a41c8540e0140080cc1a4500e2340c8290740e01400b0c82007419058110340400c0228320800e0368bc2a88a150460d82c04c0c82003c0da2e88c1e856110360b00301003c8e2360bc2a088150460d82c04c0388d82e08c1e056110360b00281023c8ac2207c190360881c00a0408f22b08c1f0540d8220700281a2540f8388ac1d0360881c00a0348b22889c1d8440d82c0090388b22889c1d8440d82c0090c80dc288821c864118360b01283303f0a220872190460d82c04a22f0a223072150440d82c0700282e084100388dc2f0ac27076110360b00343306c1a0400f2388dc2b08c1f064118360b013c330701a45c0e2370ac1d0440d82c070034192540d22b0740d82207002432064940370a21d0420d82c04802c320801103c0e0368bc2a88a1504c04c0c8200440f0380da2e88c1e8540f)) else (if j<17 then (0xc00b0400c02888c1c850130300700280e0350aa2287a190440480380d4310aa22854110120170548bc2a07a1885c1303c07002e1c264172581522e07a1885c0f002caf070100308b02889c1f03c00a258100308b2230721703c0091009905c960500a22488c1c85c0f00301c0400f0308b2270701303007002c100300a2230721404c0c01c00a0448b220850100300870c8200368ba22854110340890d8240440da2e88a150440d0228320801103c0e0368ba2307a1503c00c084120441003c0e0368ba2307a1503c00d0cc2105c0e2358bc2988c1d8581203a0b01c00f0dc2105c100388d62d88c1d8581203a0b0038af070100308b028896230761703c00c070122440e2340c62d88c1d85c0f003021048910400e2348b028896230761703c00e0701003c0c22c896230761404c0c01c00d0700e2340c02988c1d85013030070030330841a2640e2370ac1e0480e82c070034b98c021264100388dc1e0480e82c00c2bc1c0400c22c0a22707c0f0028b92c81c264122440e2340cc1f03c00c08412244100388d22c0a22707c0f00301c0400f0308b2270701303007002c1c0540e2340c02b0701303007002c32080160358b6218581203808a0c8200641103c0e0358b6218581203808d0c8200640f03707a1203a0b0028398c021064100380dc1e8480e82c00c0681905c150500b81e8601703c00b0a8a9495234851c028892210761a85c0f0038a408c2184a108388b028896210761b03c00e095234721222c896210761a0480e82c00d0561283e0e22f0a41d8621704c0f01c00d084172581584a108388b41d8621703c00d2bc23072108308b028896210761b03c00d08c1c8420c22c896210761a04c0e01c00d2bc100308b028896210761b03c00b258100308b41d8621703c0092e4b2048910388d0318841d86c0f0031234709905c960288941d8621703c00c244100388d22c0a2258841d86c0f0030100308b2258841d8601303007002c100300a41d8621404c0c01c00a0388d0300a6210761804c0c01c00b2f4bb0c0af094230841c22c0a2248801c86c0f0040402f4bb2c8302bc2e22c0a22507a1703c00e2f4bb0c0af0ba128420e22c0a22507c0f0038402f4bb8488b2250781203a0b002c15052128420f8388bc288841c85c1303c07003c1725815052128420e22c8841c85c0f0034bd2ec302bc2e8420c22c0a22507c0f0034bd2ec300ba108308b22507813038070034bd2ee1083a0c22c0a2240780e002caf070100308b0288941f03c00a258100308b2210721703c0092e4b207099048910388d03107c0f0030402641725814028892210721703c00c08412244100388d22c0a22507c0f00301c0400f0308b2250701303007002c100300a2210721404c0c01c00a0701b0540e2340c029070130300700301122c882140400c021c180) else (if j<18 then (0x1800d0400e0328b82a8901c0300090d02e0400e0328801e8600c0028100380ca2c07a140300082d8af29023258910400e81c82800b0d02e050100380c01c820009050100380c82c8aa2407c1403000b0400e0328b22a8901c0300090d02e0400e0328801e8600c0028300b82508c210708b02889a2007a1903400e100bd2c8300b82a22c0a2268841e8540d0038300b82508c21048100388b0288941d03400e1002e0941222c8941e0400e82400b05c14048100388b2210721503400b0501222c8841c8581003a090028370c02105c100388d41e0400e82400c0c02e08c1c0400c22c0a2250740d003017050100308b2210721503400a2e4b208499048100388d0310740d00309905c1422e0aa248841c8540d002c21048100388da2e0aa250740d002c230709905c150508b01e8621503400c2e4b20481003c0e2368801e8640d0030210481003c0e2368ba2107a1503400c0b8100380c22c0a2240700c0028140400e0308b01c8500c0024340b8140400e2340c01c03000a104bd2ec300b82a094230841ca2e0aa268801e8640d12e4370d02e0a81422e0aa268841e8540cd2f4b90dcb20c02e09423084120400ea2e0aa250740d10a827094230841c0528b22007a1a8540cd2f42508c21280120400ea2007a190330b90dc2508c2126417050120400ea2e8841e8540d01009905c14028892210721503400b084120400e2348b0288941d03400b0400f0388d22c8841c8540d00281c0400c22c8981e034060024100308b4288881c8580d01800a2e41c264120388d0310a81e0340600301122c882140400c021c330840e2368bc2a88c1e854110360b01c00e0dc2105c100388da2e88c1e854110360b00381c0400c22c89c1d0440d82c00a0400c22c88c1c854110360b0029374c01c45c0e2340cc1d0440d82c00c1011222488c1c854110360b0028210400e2348b227074110360b002c1c0400f0308b2270740d82007002c100300a223072150360801c00a070150388d0300ac1d0360801c00b0420e0300a81c0400c0180090cc210489103c0e2368bc2a88c1e8540f01c00f084122441003c0e2368ba2307a1503c00d2bc1c0400c22c0a2270740f0028960400c22c88c1c8540f0024b92c81c264122440e2340cc1d03c00c1009905c960500a22488c1c8540f003021048910400e2348b02889c1d03c00c0701003c0c22c89c1c0440c01c00b0400c02888c1c850110300700281c0540e2340c02b0701103007002c1122c882140400c021c2e03c0da2e8aa250740d00243203c0d4328b41e8540d00241a05c154490f4388bc2a07a1885c1303c07003c2105c96055124410e22e07a1885c0f0034af070104380c22c0a22707c0f002c960410e0308b2230721703c00a05c96051124410e028892230721703c00d070104380c22c89c1c04c0c01) else (0x1281905c168461083e0e8348b2218761885c1303c0900641805c168461083e0e8348b22085c1303c08f0c8190500f0380d0300700c0028af070100308b02889c1f03c00a070100308b22707c0e01c009080190540f0380d0300a0100128328348b2288901e0380082f4bb8388b224078120280090d0330c82e86a198520f8360c01e03800d104340ba14838078120280092e42705c1422d0a6268881e8580e003021048100398b4298981e03800a0d0300b82a094230841ca2e896200761a03800f0d0230841c05c14a2c8801d86a1603800d2f4120400e6200761a038009100b90d4300b82a22e896220761603800d084120400e62d8881d8580e0028340c02e09423084120400ea2e8981e03800e0d02708c2105c140481003a8ba2207a1603800f0f0280881f0701b0400ca2007a1903400d0d4280701a060150400ca2e8841e8540d0038330881a04c1003c0e0310740d002cb62bc2a09412a2e8941e0400e82400c0c0a9290232741c04a8801e8681003a090038b62a42525812a2e8841e8581003a090034370c0a408c17244100390781003a0900343c0a0100380ca2007a1803000a0d4150400e0328b01e8500c0028330681403c0e0300700c0024b6070960400c42a0720901800a0a01043c0c42a8801e8641203404b070150410f0310aa2207a150480d01301c0691503c0e0310a81d0480d012c340b8140400e030072080024280400e0310aa2007a1803404002c150400e0310a01e8500d01000a0680f0380c4280700d0100094410e4308b0288941e8540d00280e4308b0288941d0340080400e4308b41c8540d0020154410e4308ba250721503400a0d02e0400f0388d4328ba250740d0030340501003c0e2350ca2d07a1503400c0400c22c0a2250740d0020100308b829072150340084d1140388d0320a41d0340090d5104390c22e8941e8540d0028340b8100390ca2e8941d03400a0d0140400e4328b41e8540d0028100308b0288941d0340080400c22d072150340074d12e4500e2340c41d0340094410e4300a225072150340090388d4308b0288941d03400903c0e2350c22d072150340090400c22c8941d030050020100300a41c8540c0140080388d0300a41d030050020340b8100380c62d89a2007a1803000c0b8100380c22d8901e8500c0028340b8100380c62d8901c03000a2d8af2a4a42458b4298981c82800b0d02e050100380c62d8901c82000b0a0220701b0681003c0c0298801d86012030060040af2a4a408c9d070916200761882800c0a01c068150400f0300a622076140480c01800f050100380c22e0aa240761403000b0d0140400e0318b22007a198500c003034050100380c62c0761403000a2d8a9290962458b6220761482800b0d02e050100380c62c0761482000b0881a0541003c0e0300a81c0480c)))))) else (if j<28 then (if j<23 then (if j<21 then (if j<20 then (0x58b62407a0a0024410d02e8521083a0c62d8901e82800c0c02e094230841c22c0a2268801e8640d0038bd2ec300a82508c210728b82a89220072190340100a82508c210728b2200721a8540d0030bd09423084a0048100388801c8640d0034300a82508c1e2741c0488801c8681003a09003c300a82508c1e07412220072190400d02800e0f42508c21080120400e2200721a03800d0f82d09823088210801f0701b068130400f8288821c868120150370d0300b81c0400c22c0a2260780e0034300b82508c210708b02889a2007a190334402f4b20c02e0a81422c0a2268841e8540ce0c02e09423084120400e22c0a2250740cd1002e0941222c8941e0400e8228bd2ec340c02e0a82508c210708b02889a2007a190340122e4370d0300b82a22c0a2268841e8540d0038bd2e4370d0b20c02e09423084120400e22c0a2250740d004c370c0af0b82a0941222c8941e0400e82400e0c02e070100308b0288981e0328370c02f0b82a0941222c8981d0400d02800e0f43a0e4370d0330c8300b82508c21048100388b2288981e03801508412244100388d22c0a22707c0f0030402641725814028892230721703c00c2f4bb0c0af0b82184a108388b02889c0f0038402f4bb07a1222c8981203a0b002cbd2e4370d0b284a108388b0288941f03c00e0dc302be1222c8941e0480e82c00b104340b9104390c22c0a2240740d003022068150400f6340c0280480f02004c080190540f0380d0300a0100128320641403c0e0340c01c03000a0a0220701b0681003c0c029886180480f02004f0a01c068150400f0300a6218501203c0801382e0400e0310b2298901f0500c002c340b8100380c62c8a6240700c002c340b8100380c62d8901e0400f02000c0d0140400e0318b01d8581003c08003121068154398d02b0701203007002d21068154398d02b0701203007002c280420e22b0881f0621003206002c150420e22a07c148400c81800a0680f8388a81c8400c8180090a02206c1a03c0a621076180480c01c00d0a01a055140400f02988c1d85012030070038280881b0680f0298841d8601203007003428068154501003c0a623076140480c01c00e0c8190500f0380d0300700c0028b92c81c264122440e2340cc1f03c00c2e41c264120388d0320ac1f038070030200641503c0e0340c02804004a0cc220741a0581103c8dc280400c02c04d0c82007419058110340400c0228290901d46c11c29886180400c02c04c258100308b2230721703c0090400c22e0a22307217038070028120448b220858120380880380d22f0a22085c1301200f0380d22c88c1c85c0f0024330881603c8d62f0a621858120380b01340d22c882150440d021c3308a1d068990580f2370a8120380b0134320641403c0e0340c01c03000a080190540f0380d0300a010) else (0xc0d8250601604911c2e87c1203c0a80302422c89c1e0480e02c00822c8a22607c1203c0a00202522c8a22707c1203c0b00240e22c8981e0480a001c8b223072160480e02c0080400e22e072170480f0280090601222c88c1c85c1203c0b00280e22e072160480a001c37070100328b82b074110360b01c00c0fc2a0400cc2a8881d0360b01c00b0dc1c05c100330ac1d0440d82c0700303f071170420e0330ac1d0440d82c0700343a09c170511082c8aa2707c170360700343408c1c05c144418a82207a1b05c0d81c00e0d0300b8230430b42b09c1f0360700303408c17050108390c62b07c17036070034400d02e4430b42b09c1c8480e8260700343409c144410c62b07c148480e82607003428068180551082e0aa2587c1583c0580343506818055144430a82087a1b0560f01600e0d423060150408e4330a61f0560f01600d0d428068154410cc2987c160420e82c058038120400e8350c22f0a2218721583c058034104380c8288861c8581183805802c97250104388bc288861c8560f01600c03a0d0320a221872160460e01600b2d8af0b8a929091a2e8941c8228af2a4a408c9d07091a2007a18822cb62a4a4258142468ba2107a14822cb62bca408c962441003907208a2d8af070960400c81c82203f8d22e850108380c81c82800a1001c0400e0320780e0020370c02105c100388d41e0400e822c21048100388da2e0aa250740ca2e4b2048100388da2007a19032821048100388da2e8841e8540ca2f4b90dcb20c02508c210481003a8b82a8941d0340112f42508c21280120400ea2007a1903400d2e4372b02508c21264170481003a8ba2107a150340110dc300942305c12244100390781003a090038b92c81c264120380c81e0324370d01c05c140400c22e0721603800c05c14048100388b221072150328140488b221072160400e82249905c1422e0aa248841c8540ca08c1c264170508b01e862150328b90dc340a82705c1422e0aa250721503400e0a827094230841c05c1422c8801e8621503400f2e4370d0ac09c2508c2126417050120400e22d072150340130dc2a09417258140488b41c8581003a09003817050100308b222072160324370a82505c160501222e072150400d02800e03c0e2348bc2888c1c85c1303c070030910400f0388d22c88c1c85c0f002c32080160358b6218581203808a0c820874190580d8120380890641122c882160480e0220bd0f0bb0d02e451104390ca2e8901d03400e2bca9290230729162d896200761a82800d0a827094230841c85e1422d0a6248801d86a16038011094230841c84a108398b429896200761a03800f2f4bb4410e4308b0288901d03400b1002a0400c2200721a0380092f43c2ec340b9104390ca2e892208640d0038412f4bb0dc30a2e0aa240740d002cb62be96a4)) else (if j<22 then (0x50740d002434050100390ca2e0841f0640d002c340501003a8b41f0440f02400a0d0140400ec290740f0140090e0260681804f0aa2104c0c90dc2505c12a2f07c1103203a08c1a0430ac1f031c340500ea2d07a150440900243809019060120470aa228581283a0b0134370901905c130468bc1e85a1203a0b00343f0dc2a060174430ac1e0480ca050104380c82e0ac2507a1503400b0d0140410e0328a82107c1a8540d003034050104380ca2907a1503400a0d0140410e0328a41e8581103c0900301905c1604d0bc290841604a0f012c19060160490b423074168480f002c3f08e1704c120420ec2b07812032c190581122c882160480e0224320b80e22c8a2260780e0024190501003a0c22e0721603800a054140420e0310a81c8580d01800b070150388d0308ac1f052130320700303d0901304811a2286c1303c08a0f4120400e62a8881e86c0f0028400400c42a8881e86c0f01c00a090130481122e88a1704c0f022821048100388b62b07a1703c00a0dc1c0400c22d0ac1e85c0f01c00b1003a070100318b42989c1f03c070030370c0210400e62f07a1203a0b002c37070100318b42b0781203a0b01c00c0e02487c120458b22a04c0f02a04b0e8210480e62c8ac1f03a070028370c02404c1162e87c1203c0a802c362c82f0840e2358b627078120380b0034342c82e0400e2358b62607c1203c0a0034372c830084100388d62d89c1f0480f02c00e0d0b20b80e2358b6260781202800b2d0ae0398b4288720f0120092d0ae0398b4298921c83c048028410b82a0961262107a1203a0b002c340c02e08e108298841f03a07002c248448b2258841d868120380b002c258488b228896210761b0480f02c00c090130481122e8962185c1303c08b084120400e22e8aa270761703c00b0dc1c0400c22e0aa270761703c070030130481162c88a1985c1303c08a048100398b22207a1985c0f00282a0400cc288881e8661703c07002c3a0701a0420e0330ac1d85c0f01c00c0dc2105c100398bc1e8480e82c00b0dc1c05c100330ac1e0480e82c070030380901804811a298881303c0a812c3a0841a0481003a8ac1f03a07002c370901704c1162e87c1203c0a802c368bc21264160388d62f076160480e02c00e0d099050100388d62e076170480f02800d0de300849905c100388d62f076170480f02c00f0d0990500e2358b81d8581202800b2d09403a0d0330a21c83c0480280e8288720e0120062d0940380cc288761483c0480280e8360a21d8520e0120080e82705c1482e8aa2707c1703c00b0d0230841705110c2e0881e86c1703c00d0d02e0941243b0bc1e8480e82c00b0d0250501243b0bc1e8480e82c00b0d0300b8230430b82b09c1f03a0700303609817058134468ac230581303c0a81343408c170501043a8ac1f05c0e81c) else (0x90500ea2d07a150440900283a0e4370d2198508b62989c1e85c0f00343a0dc348561022d0ac1e85c0f01c00c0fc378418b42b0781203a0b01c00b100238420a6210761b03c0700282508c2185210a2c8841d86a1703c00c0a823072148430a22107a1703c0700303f0a8238430a6210781203a0b01c00c1003a0dc348408b82a89c1d85c0f01c00d0fc370a8178430ac1e0480e82c070030400e8230428b82a89c1f03c07002c3a08c1a0420cc2b07a1703c07002c3f08e170481043b0ac1e0480e82c070034370c02504a0ea2f076110360b002c400de10a2e0ac1d0440d82c07002c370941704a0ea2f076110360b002c370a8178420cc2b074110360b01c00c0e8230428b22a89c1f036070028380981804e1162a8841303c09812c3a08c1a0420e62b07a1703607002c370941704a11a2d87c1103c09802d104308bc2888c1c8581203a0b01c00c4d12e0841203b0b82b09c1f03a0700313408514048100388da2b07c1703a070034174410c82a892230721703c07002c1c450108380c22b07c1484c0c81c00c0dd1c4410c22e0ac1f03c07002837471104328b82b0781203c07002d344c12e08e1082b09a2207c0f002c37470174410cc2b0781203c07002d344c12e08c10c2e0ac2707c0f002d3408d1745010a2b07c1703c00a071140388d0308ac1f05213032070030320b8250488b22889c1e8480e822c3b0c02e08e1022c8a2270841f03a070034320c02e08c1022c8a22707c0e812c17054140420e4308bc2888c1c85c0cc068190501222c88c1c85a1203a08b068150511022f0a223072160480e82301905c140408ba2888c1c85c0e812c370c8300841003b0bc1e8480e822c370841905c1003b0bc1e8480e82c00c0e4320841203b0b82b07c0e81283908419048100388da2b07c0e812c1a05c150511082a8922307217032c1c0541023c0c82c8aa270721303204c0681905c144408b81e8621703c00b06817054144408bc2a07a1885c0cb0e4190481023c0ec2e0881e86c0cb0541023c0c22a0881e8621303204b070150420e0308ac1c84c0c81281c0541023c0c22b07c1603a08812c411003c08c1c4420aa2207c0ca1003a0dc350d11022e0ac1f0328360bc240468bc1d0440d02c00a0d02e0400ea2d07c1103c090028340b80ea2e0a41d03c050024370c02504a8bc1f0440c81003a0cc230428b82b07c0c90d02e03a8ba25074110240090dc320c02404c11a2f07a1203c00b1003f0dc310c110a2e0ac1e0480cb0b8104380c82c8aa2507c1503400b0d02e0400ca2c8aa250740d0028340b8104380ca2c8aa250781103c0900342c09c2508c214428b22207c0ca0a82809c2307110c288881f03283f0a82307c1e07110c2a8881e0480cc0d82405811c2a88a150440d02c04b0d82405811a2f074110340b0028140400e82f0ac2))) else (if j<25 then (if j<24 then (0xd02c0090e0262641805813046854110340b0130370949905c1604811a150340b002c1c0540e2340c22b07c1484207002c1a250128450e22c882160400e022c370d02c068198388bc0080e4250841a0648841d86c0090dc250681905c120460e40d82c00b0dc250681905c1203a85c1103c08b0e432048100380d81f00202404c120440d22e85c13022421048100380d22f001c370c830084100380d80f002421064120400e0348bc0f002439064120400e0348881e86c0f002c378c021064170400e03707a1203a0b0034320941122c8a22603c0080c83008c1003c8b22889c009068190481122c88c1c8580e82c00b064170400f22c88c1c85c0090681905c9522e07a1885c0f002a1c0689905c1522f0a81e8621704c0f01c00e0c8210480e0348b22889c00906413048110348b22085c13022819048100380d22c88c1c85c0f002c190448b220858120380880c80e22c8a2260780e0020190400e22e072160380080dc320c0af0941204603c0090b02508c21080194388881e86c00b0dc240641704c11a1603a0b0028370941905c9604811a1603a0b002c370d02c068198500b8170024390941a0650761a05c0080dc250681905c128150360b0028120400e2350b42105c0f00240e2340c22908c1d0521303207002c398c021264100388dc2707a1203a0b0034370841905c100388d42f074168480e82c00e0e421064120400e23505c0f00283909c19048100388d81e8641703c00c06414048100388d02c08c1c05c0f00302c09423084a00660e02207a1905c00c064180581242d0841603a0b0028370941905c16450122450580e82c00c070150388d0308ac1d052130320700301a064170541402e07a1805c0f002c1a064140480b0230701603a0b002c0e2348a4210761b0521303207002c3d2ee128448b2288941e8480e82c00c0ec3008e1022c8a2250841d06c0e81c00d0f4bb0c21083c8b2288941f03a07003017056108388bc288821704c0f01c00c0f4bb84a1122c8a22704c0f02283d2ee128388b2288941f03c00a84e128448b22085c1303c08984a108388b2210721703c0090f4bb84a0e8348b2288941f03c00b84e128460d22c8821704c0f022a128420f83a0d22c8841c85c0f002c3d2ee0e22c8a2240780e00242c09423084202660e0210741b002c1c26c150388d0308ac1484c0c81c00c0700e2340c42c8a62707c1484c0c81c00d0dc32084100388d42603c0090e432084120388d02909c009070150388d0308ac1f05213032070030362c82f0901183a8ba27074110340b0034342c82e0400ea2e8941f0440f02400c0dcb32c8300941283a8ba2707c110330342c82e03a8ba250741102400a0d824264160460ea2f07a150440d02c00d0d0990501003a8b41e85c1103c090030370949a2641704a0ea2f07a170440cc0d09) else (0xc1c05c100318bc1d8581203a0b0030150501003e0e0300a81d8580c01800c0de300849905c100388d62f076160480e82c00f070150400f0308b02a89c1d85013030070038150400f0300a22207a19850130300700341c054108380c02b0761404c0c01c00c070150400f0300ac1d8580e820070030b908499048910400f0388d8318bc1d85c0f003c2126412244100388d22e0aa270761703c00e2e499048910400f0388d62c8881e8661703c00f264122441003c0e2348b2230721703c00d0e02426418048112388d81302804b2e421264120400e2360c82b0761604c0e01c00f0d0990501003c0e2360c62e0761603800d0dc2526417258122470ac1d8581203a0b01c00f0dc2526417258122461062f076160480e82c00f2e4b207099048910388d0318bc1d85c0f00381c0540e2340c02b0761404c0c01c00c2c825290230851022c0a2268881e86c0f0038bd2c8302bc2e4408b02889c1e85c0f0034b2094124408b2270781203a0b002c990491022c88c1c8581203a0b002cb20c0af08c108308b02889c1f03c00c26417258108308b2230721703c00b26417258144408b82a892230721703c00d08e1c26417258154408b81e8621703c00d2c83008c108308b227078130380700309905c108308b82888c1c85813038070034b20400e8308b0288981e03800a2641003a0c22e072160380091009905c9605110028892230721703c00d0dc30070100328ba27074110360b00303f4c02a0400ca2207a190440d82c00c0dc1c05c100328bc1e854110360b00303f4c01c45c108380cc1d0440d82c00c05c150420e22d0a2230721504c0d01c00d068154408b42888c1c8580e8240700301a05c150511002a892230721504c0d01c00e068170551022d0a81e8621504c0d01c00d0541003c0c02888c1c85013030070030150420e0308b42a0721603406002c3c2ec230701b4410c02a8881d04c0d01c00e0e8370d4340551022c0ac1d04c0d01c00d0e8332c8230400f4328b02b07413034070038370c4af4428b02b0701203a0901c00c0a82808c1c06c154410a222074130340700382a08c1f2741c06d1042a8881c0480e82407003c3a08c1a264150400f4310ac1d04c0d01c00e0dc2a06017258154410ac1c0480e8240700382385c132441003e0e4310ac1c0480e82407003c342c82e03a8b8290740f01400a0d0b20b8100390ca2e0aa250740d003034264140400ec290740f01400a0d099050100390ca2d07a1503400b071170540e2348ac1f0540d8220700323408614048910408f0388dc2f07c1503c00e072140408f0308ac1f05211032070030122441023c0e2360b8230781503c00c05813048118348b220854110228360bc240450440d02c0080dcb20c02f094120450340b0028360901a05811a150440d02c04a0d82405811a150440)) else (if j<26 then (0xa2207c0cb4c1af08c1062d0a62707c0c9094a408c218418b42989a2207c0f00301c048910388d0318b42989c1f03c00c45d960420e0318b6230761703c00b0420e0300a6230761404c0c01c00b084122441003c0e2360c62d88c1d85c0f003821048100388d8318b82988c1d8581303807003c2345d960418b6230761703242345c108318b82988c1d85813038070034122440e2340c62d88c1d85c0f002c0e2340c02988c1d8501303007002c2e48512645104388b02889c1e85c0f00341705112645104388b82a892230721703c00e0dc3448512645104388b82b07c0f003014449914410e028892230721703c00c0c0af08c1c4408b02889a2207a1b0330400c0af0b91022c0a22707a17032c302bc230420e4308b02889c1f032c404408b02889c1e0480e822417258150420e4308b22307217032c154408b223072160480e822417258150511022e0aa2488c1c85c0cc08c17258154408b81e862170328400f0bb08c1c4410c82a8881f032c400dcb60d4344408b82b07c0ca100332c8230428b82b07c0c91003f0dc310c0af4428bc1e0480e82302a2a42808c1c4428b22207c0ca0fe300a82307c9d07110a220781203a08d08c1a26410a2f07c0c70fc370a81805c964428bc1e0480e82303f8c02385c13244108390cc1e0480e8234108380c22c0a2260780d01800a054108380c22d0a81c8580d01800b1009905c960511002889223072170330400400c42989a2207a1b03c00a0dcb6070100308b42989c1e85c0f003040070108380c62d0a62707c0f002c400dc30070100318b6270781203a0b0034372c830084100388d62d89c1e0480e82c00e2e4b208412244100388d8318b42989c1f03c00f2c821048910400e2348b02889c1f03c00d2e4b2048910400e2350a6268881e86c0f0038b208412244100388d22d0a62707a1703c00e0e0b2090120448e2340a81302804b2e4b2084120400e2360c62c0a62707813038070040342c82e0400e2360c62d0a6260780e0034bb2e42a2a6218708b4298922207a1703c00e2f4bb2c82529023084a08420e42a8881f03c00f2ec302bc2a0949d87212a220781203a0b0038b90dcb60d0b22661022d0ac1f03c00c0dcb22bc250489162d0ac1e0480f01c00d0dcb20c0af094122461062f0781203a0b0038b92c81c264122440e2340c62d0a62707c0f003c402f4bb2c82e0a8a94851c028892210761a85c0f0044bb0b82529023086108388b028896210761b03c010100bb0951c8488b2258841d8681203a0b0038bb0c0af0b823072108308b028896210761b03c0102ec300b823072108308b2258841d86813038070040ac094a408c212801a2661083a8b2210761b03c0100dcb60d41c0400c22e0aa270761703c00d0a8a90a0100318b22207a1985c0f00301c068108380c62f0761703c00a0d) else (if j<27 then (0xc22a0801e86c148440c81400b050120400e2360b822054009050100308a822052110320500282e0841203a0d22c8a2250024140481003a0d22c8821500241c054100380c22b0521103205002c1c05c150408f0308a41f0500e822050034140400c8288841c8581103805002c2e0388b2288901c030008050100380c22c0721403c040028412ec2e08c210710c82a89a2007a1903c05003c3a2e4370d02e0508b82a8941e8540f01400e0d0330b80e8290740f0140090e8b20b8230400ea2e0aa250740f01400d0a82708c2107014a2c8801e86a1503c05003834068140400e41d03c0500243a08c1a264140400e4328b41e8540f01400e070150388d0308a41f05211032050030bb08c1c4410c82a89a2207a1b032cb92c8230420e4328b82a89c1f032cb908c990420e4328bc1e85c0ca0dcb60d4348408b42989c1e85c0f00303f0dc308418b6270781203a0b002c372d8342b0998408b42989c1e85c0f00342806818056108308b02b07a1604c0e01c00e10023072108320aa258841d86c0f00302a2a42808c1c8428b2210761a85c0f00343f8c02a08c1c8418841d8681203a0b0034b92c825290230861083a0aa258841d86c0f003cb9094a408c1a26610a2c8841d86a1703c00e0d41a060158420a22107a1604c0e01c00d100372d8348408b82a89c1d85c0f00303f0de300a8178418bc1d8581203a0b0034bd2ecb90a8a98861c22e0a22207a1985c0f003cbd0dcb60d0b28408b82a89c1d85c0f00344008c108328b82a89c1f03c00a08c1a0420ca2f07a1703c0090fe3008e170481043a0cc1e0480e82c00d2ec25290230861c4410e82a89a2207a1b03c00f0d423060150420c82b07a1604c0e01c00d100370c2108328ba27074110360b0030370a8178420ca2f07a150440d82c00c2ec300a82587112a2207a190440d82c00d0dcb20c02504a1083a8ba27074110360b0038370949905c128420ea2f07a150440d82c00e0d428068158420ac1e8540d828070030bb08c1c4410c02a8881e86413034070034b92c8230410ca2c0aa27074130340700343809899060130400f41302404a2e423264108390c42b07a1504c0d01c00d0d015050104380ca2d07a1503400b0d0b20b8100390ca2e0aa250740d003034264140400e4328b41e8540d002c302bd1c4410c22c0a22707a1703c00c471104308b2270781203a0b0029104308b223072160480e82c00a05c964410c22e0aa2488c1c85c0f0030372d91c4410c22e0ac1f03c00a0dc30471104328bc1e0480e82c00b0dd1c05d104328bc1e0480e82c00b05c964410c028892230721703c00b4c1af0400c62d0a6268881e86c0f0031306bc1c0420e0318b42989c1f03c00c08412244100388d8318b42989c1f03c00d048910400e2358b42989a2207a1b03c00d4c1af08c1c8418b42989) else (0x190400e61f0440f02600b0701503a0d0320a61e0460e01600b09c2508c210520e0210761a05c0cb0d02e4500ea250741102400905c15050108388b22085c0c91001a05c150520aa248821490841a064170508b81e8621490701a05c150508bc2a07a1885283a0dc34054144308b82a89214a09423084190510e22c8881e86214b0a82307015051104330a22207a188530140400e02d072150340080d02c0501003907c188540d002834050100390721503c09002434068140400e41c8540d00243a08c1a26415050108390cc1c85c0cc0d0140388b41c854110240090d0190501003a0d41c8540d00283609019058114348b2208581203808c054140420a41c8540e0140090d019050100390d81c8580e0028150501042a072160340600243408c1a05c140408f43b07417032c1905c140410f2380b02287016832c340b80ea258841d8641102400a0d0ac03a8b2210761a8541102400b0a823856148420c429892210761a85c0cd0a82384a108310a6258841d8681203a0b00383d449104388801c86a1480ec2407c1d0200680e82c0090d02e03a8ba25074110240090d01403a8b41e854110240090a8230701b4410cc288801c86a14b0388b2288941d0340070388b225074110240070388b62507a150440900200e22c8981e0480a001c340ba1403a078120280080d12e0500e41e854110240091003a0dc340b90c22c0a2268528340b8100388941d0340080d0330b80e0288941d0340091003a0ccb20b8230420e4300a224b0d02e0388b225074110240090d0320b8100390d2260780e00283a2e42705c1422d0a62607a1603c060034340b82508c218380780080d0300b8230841c8320aa258801d8680f01800f0d0230841c05c148328b2200761a8580f01800f0e8b90c02e8308b82a8981d8580f01800d0d0300b8230400e8328b82a8981e03c0600383408c170501003a0ca2e07a1603c060034340c02e08c108388a80084d12e0388d82b0941d0340094410e4320aa250721503c050029140388a41f0540c8140084410e4308b82a8941e8540f01400b4d12e03a0ac250740d0021140388d22907c15032050024340b8100380700c001c340b8100380c42989a2007a1803c0400342e0400e0308b4298901e8500f01000c0d02e0400e0318b4298901c03c040030140400e0308b82a8901d8500f01000c0d0140400e0318b22007a198500f01000d0d0140400e0318b01d8500f01000b050100380c82c8aa2407c1403000b0b8250490e22c8a2240340090c02e08c104388b22889400905c140400e22c8841c8540f01400b068140488b221072160400e82c050030370c0210400e2370900d002439084120388d82b0940080689905c1482a892210721503c0500301c0400c82c8aa270521103205002c1a264170541422c07a188540f01400c04))))) else (if j<33 then (if j<30 then (if j<29 then (0xd886160400e02293409514048918388400c8225344b8128288400c82a0700253449d140488400c82a070024360901183d8b4280400c02c04a0d82f090118398b0100300890dc300bd2e094128460e62e0400e0231344b8104388a41e0480a81400a4d1140410e41e0480a8140090dc30090130450da2e8900c82283f0dc302bc124320aa240400c82c00c0fc2a08c1e2741243207a180400c82c00d0fc370a81725812432850100320b00303f08c17048910420e4300400c82c070034360bd2e090116240400c0224370c025048118398900d0225140410e829076160400e01400a084120400e22f07a170320362c82f0840e2368941103408a0d0b20b8100388da250740d0028372c830084100388da250324342c82e0388da2e8941d04409002c36084990580e23707a150440d022c34264140400e23507a1503c09002c370849905c100388dc1e8540f022c34264140388da2d07a1504409002c3408419048100388b62484701a04c122440e4320480e82c04b0d0b20b80e2358b6260781202800b0d8248741162d0a6260480e02c04b0d02e0398b626078120280090d0990500e2358b81d8581202800b0d82405811c29886160480e02c04b0d0140398b81d858120280090dc320c0210400ea1203a0890dc320c02404c110358ba1203a08b0dc320c12e094120398ba1203a08b0dc21064170400ea1203a0890dc240641704c1103585a1203a08b0dc25064174501203985a1203a08b0d82f0901103a894110340890d02e0400ea250740d0020340cc0e82a8941d0340080dc30094120440ea2503203a0ccb208c1003c0e4320aa24a0d02e03a8ba25074110240090d824068160440fc2a88a150440d02c04d0d8240581103b07a150440d02281003a0b41e8540d001c340b01003a0841f06a1503400a0641003a0b41e0540d0020340501003907a1503c09002434068140400e41e8540d0024380981a2641804c1103e88a1504c0b013437094170481103b07a1503c08a0e823068990400f0390cc1e85c0cb0d01403a8b41e854110240090641704c0f42d0841604a0b012819060120390b423074168480e822c21048100388b62460dc302bc210400e62603203a0cc210480e229891c37084172581003b0761603a08a0e02406818254120440f6218581302a04d0e821068950481003b0761703283709017250130440ea1d8580f022c380901906115048110358861604a0b0134370901905d1404c110370761603a08c0e42106515048100380da1d85a0cb0e83909e1905c148380bc1e05c0cb0d0230861905c148390761a05c0cb0400e22d0721503c0900200e22d0721504409001c0e22e8941d854110240080388b81c858120280070d22e0500e81e0480a0020394bc24474190581141103408a03a0d0320a221872160460e01600b0e530084) else (0x80c62c8a6240700c002c340b8100380c62c8a6240781003c0800343f0a8230480c41d8681003a09002c3707017450100318581003a09002c3f0dc2a05d140480c6160400e82400c0d0140400e0318b01d8581003c080030372d835070100308b42989a14a0dc302bc1c0400c6260480e82c00b0dc35070100308b02989a16012837070100300a6260480e82807002c2a274100310761a0480e82c00a0a8100310761a0480e8280700283707017258100318581203a0b002c37070170400c6160480e82807002c15050104380c42907a1503405002c34070150400c22d0a62685411012c108380c42c0a4260780e0024340b8108380c6270881f0680e002c108380c42d8981f0580e0024340b8108380c62c8a6260780e002c340b8108380c62d8981e03c0a002c108380c42f0981d8580e0024340420e0318b42207c198580e002c150420e0310b81d0580e002434050108380c62e0761603800a0d0140420e0318b81d8580f02800b0dcb6070100308b42989a149100b2070108380c4298920370c0af070100310a62603a08a100372d8350d00c22d0a62685284008c108380c429891c400fc370c0100310a6260480e82c00c1003a0dc350d12e0308b02989a160130400e92e08c1083e0e0300a626012c400dd2e0400c0298981203a0a01c00c0fc2a08c1c0400c41d8681203a0b00302a08c1c06c100310761a0480e828070034370701805c960400c61603a08a070170541083c0c8298580e82804b0fc370a81805c100318581203a0b0030370a817055140400c6160480e828070034342cc0e62c8a6260781203c0a81800c0d0b30398b2298981e0480a81800b0d02e0400e8318b6260780f02800b0d02e0398b626078120280090d09a0500ea2a076160480f02a060030342681403a8a81d8581202a06002d390400e8310bc260761603800a0d12c0400e8318b42207c198580e00301003a0c42e074160380080d0140400e8318b81d8580f02800b0d0140398b81d858120280090d119050100390d8318b81d8580e0030104380c82c8aa2507c1503205002c340410e0328b22a8941d03205002c340410e0328b22a8941d03c0881400c0410e0320b02b0941e8540c81400b0d0280410e0308a82107c1a8540c81400d054104380c82c8a41e0540c81400b0d01a050104380c22907a1503205003034060140410e0308a41e8540f02205003437070100308b42989a1501243a070108380c4298940480dc1c0400c4298901203a0901283a0dc158500c22d0a62685404a0e8230400f8380c4298940490fc370400c4298901203a0901c00b0fc2a08c1c0400c41d8601203a0901c00d0dc1c06017454100318501203a0901303f0dc2a060170400c6140480e8240700341c0541003c0c0298861603c08012c118398b62185010030088060128460e62)) else (if j<31 then (0x721a85c0f0038bd2ec2529023084a08420e429892200721b03c0102ec300a8250789d072126248821a0480e82c00f2e6b284a918420f8388801c86614b0f0bb08c1c06d104300aa248801c864130340700402a0a0230701b4410c4288801c86a1504404e2ed104328b82a8981f03c0090a8230781d049074188400c82c00b0e532449104390d2200721890e51484a108390b0200721905282a09c230709b45210a280801c86414c09423084998388b0210741885282a0a023070958428a02107418852c2e084120390d22c8a2260024390c82e084120400e4348b2288981e03800e0b8250490e22c8a2240340090f0bb0b8230841c4410c22c0a2268801e8640f0140110e8b90dc2e4308b0288941e8540d0030342c82e0400e2250740d0024340ccb20b80e0288941d03400a0dcb20b8250488940d00203a0ccb20b8230400e4308b0288941d03400e0dc302bc2e094124388900d0028370c0af0b8124308b2250781003a090034bb0c0af0b823071104308b02889a2207a1b03c0102c8302bc230420e4308b0288928b2094a408c212820e22c0a2258841d8634b20c0230400f8390c22c89411012cb20400e4308b0288941d03400a0c0af08c1c4308b02889a2207a18b100302bc2e4308b02889a1490c0af08c108390c22c0a2249100bb08c1c4410c22c0a2268881e86c0f0038400dcb60d10c22c0a2268524402c8230420e4300a22482ec2e094a408c21282108388b028896210761b03c011100bb0949d8488b2258841d8681203a0b0038bd2ecb2094a408c218420e22c0a2258841d86c0f0044bb0c0af0a8258488b2258841d8681203a0b003c3a0dc344308b02889a1504404a0e8332c8230420e4300a22504404b0d0332c82e0380a2250740d0028342c82e0400e4308b0288941d03400c0c83008c1003d0e22c8a22490c80e22c8a2260780e00203a0cc3208c1003d0e228892437070100308b42989a16002439050100388b6250740d002435050100308b4298941e8540d002c0e8360a21d8520e012008070150420f0320a6218581302804b0701503a0d0320a621858120128350b8100308b4298981e8580e002c340cc2e0420e0310a6260780e002c400e8370d02e0308b42989a16002c340390a01c0300061003a0b8230420e0310a626002821048100388b625001c37070100308b42989a150024400e92e070100380c42989400a0dc304b8210400e6240340090dc304b81c0400c4298981003a0900303a084120388a625001c3a0e4370d2190500e22d89400a0e837854140308b42989a1500282e0400e42d8901c0300080d02e0400e6240700c0020340b80e4298901c0300080dc30094128440e6240340090e8230420f0380c4298940090fc370c12e0480c4298981003a0900302e0400e0310b2298901f0500c002c340b81003) else (if j<32 then (0x82a8921490a8a90a023071104308b22207a18853023068990420e433072170324150501042a07216034060024b90dcb60d0998388b42989c1c85c0cc2b025290230841a2660e22c8841d862170338170541003e0e4308b2208541303404c06817054144300aa248821504404b068170550c22d0a81e8621504404b0e8370d4340550c22c0aa248541101302a0a023070154410c4288881e8621504404e0e026068990601504c1003c8821504c0901383a08c1a264150420e4330721504c0d01343406899050100390721503400a0d099050100390c22d0721503400b069140489142d084148400c8228370a81705914049052100320b002c1905c1003d0e22c88c1c85c0ca0841a064174388b81e862170328190400e22e0721603800809423084194388881e8621703283a08c1a064950400f43b07217032c34064140400e4360721603800a0d0190501003a072160380090dc2106417059140400e2370741603a08d0e42106415450120400e2370741703301905c132440f42d0841604a0b012c19060122440e42d08c1d0580e822c380981a06418454132440f4210581282c04e0dc2506417450122440ec1d0580e82303a08c1a065140408f03b07417032c2a08c21072148310a6248801d86a1603c06003c3c2ec340b9104390c82a892208640f01400e0f0bb08c210710c82a892200721903c0500383d094230850e2200721900242a08c210710ca2f0a2200721a8540d0034300a8230789d070124308801c8681003a09003cbd2ec340b9144390ca2e0a01d03400c100bb4410ca2e0a81f03c0090a8a90a023072108308b429892210761a85c0cf0c02a08c1c84a10831896210761a0480e82c00f2c82529023086108388b028896210761b03c00f2b02529023086108388b429892210761a85c0f00402a0a023072158420c029892210761a858130380700442a08c1c84a108300a6258841d8681203a0a01c010100bb4410c82a892200721b03c00b0f0bb071104328b82a07c0c9104bd2ec340b9144390ca2e0aa240740d0038302bc23071104308b02889a2207a1b0334372da108308b4298941e85c0f002c402f61083a0c62d0a62507c0f002c370c2178420c62d8941e0480e82c00c2f4370c2178420e62d8941e0480e82c00d2f4b92ca9984a918420e8318b4298941f0338bd2ec2e84a918420e22c0a22507c0f0034372d8350d2108308b4298941e85c0cc2f4338420e8318b4298941f0328370c21784a108318b6250781203a0b0034bd2ecb20c0af0ba108388b0288941f03c00e2f4370c21784a918420e62d8941e0480e82c00f2f4b92ca9984a9183a0c62d0a62507c0f00383c2ec23071104320aa248801c86c0cc0a8a90a023071104308801c86a14b2f4bb2e4b284a918420e429892200721b03c00f2ec2a2a4210708b4298922) else (0x243a08c1a264100390ca2d07a1503400c0c02306817048910400e4310781003a0b01400f0e4324b8120400e8340740094b8210481003a0d22d0020370c12e0841003a0d00d00243d4b82508c218800e01d00243a0e4370d12e8640e22d03400a0dc304b82504a110398b00d00282c09423086190388841d8640d002cb92c821048910400e2350c82a892cb908499048910400f0388d43307a1703342126412244100388d22d0a62707a1703341c0540e2348ac1f0521303207002cb92c821048100388d4300aa2504404c0e02426418054120448e23504c090130b908499054120400e2350cc1e8541303404e0d0b20b8100388d4320aa250740d003034264140400f0388d43107a1503400c470122440e4320480e8220332c8230400e4320aa24808c1a264100390cc1e85c0c90dcb20c0af084100388d6260480e8230b208412244100388d22d0a62707a14c2e4372d8342c8990388b42989c1e85c0cd0dc332c825048910398b4298981203a0b0138372c83009412244100398b6260480e8234370849905c960400e237076160480e8234370941a264170489103b076160480e82c04e0dc2526417048910400ec1d8581203a08d0e8332c8230400f0390c02a8941101303a08c1a2641003c0e43307a1504c0d0134340ccb203a0aa250740d0024342c82e0400e4328b82a8941d03400c0d01a264140400e41e8540d002834264140400e4328b41e8540d002c362c82f0901103a8b41103408a0dcb20c0250481103a8b41103408b0d824068990581103e854110340b013036090990581103a8541103408a0e02606899060130440fa150440b0130370949905c120440ea150440d022c1a0481143a8ba228521003208a0dc302bc2404c114368b21003208b0dc302bc250481143a8b21003208b08c17048110400f4388400c82a07003219050100380b41e0540d002417050100390c22c8841c8540d002c1a050124308b221072160400e82400c0689905c144320aa248841c8540d00301a26417054144308b01e8621503400c0e8b90dc340510c22e0aa250721503400d0a8230841c051104308b22007a188540d003834264140400e41c8540f02400a0d01a264140400e41c8540d0028370949905c140490721503c09002c3a08c1a264140400e4308b41c8540d0034370a817258140490c22d072160400e82400e0e4344b82a09c1402d898200781500303a0e4370d12e8641402d07815002c9905c960420e4308b22307217032c9905c960520e22d0a62488c1c85c0cc08c2126417258158388b41d8621703309905c1003e0e4308b2230721504c0d0134990400e4308b41c8540d0024bd6c82a2a50a6248881e86214a05c96054108390c22c8821703284005c96054144308b82a89220852c2307017258154308b81e86214a0dcb60d4344308b)))) else (if j<35 then (if j<34 then (0x2400d0a82808c1c0400ca2c8841d86a1503400d0fc300a823070120400c6210761a0400e82400f0a9214728b82a892210761a8540d0030bd094230841003a0aa258841d8640d003430abc2a0951c04a896210761a0400e82400e2b02508c210400ea2c8841d86a1503400d0a82808c1c854100320a2210761a8540e01400f0a8230400c8298841d8681003a0a01400d071140400e0318b41d8540d00283707017259140400c62d076160400e82400e0dc2105d140400e62d076160400e82400d07015450100320a41d858110380500301c05c15450100320a41d8500e828050034b908499450120400e0318b41d8540d00343408514048100388b82a8941d8540d0034b909d140481083c0e62c8801e8661503400e2e42126514048100380c8290761503805003834050100380c62c0761403000a08c100380c62d076150340090fc370a817450120400c62d076160400e82400f2e4370d1140400e22e0aa250761503400d09c2508c21450100398b22007a198540d0038370941745012a44100398b41d8581003a09003c3a08c1a4501083c0e0320a41d8540e01400e0dc2a05d140400c829076160400e82805003834050100380c62c0761403000a2e41c265140480e0318b41d8540d00301c055140380c829076160440e01400c100250491043a8b82a8941e0400e82400d0491043a8ba2107a160400e82400b0fc3008c17048104380c41e0400e82400d0dc30abc250491043a8ba250781003a0900383709417a58124410ea2d07a160400e82400e08c170410e0320a41e0400e82805003040264178420e429896220761603800c0d02e03a8ba25074110240090d01403a8b41e854110240090c12f0a82581c0340a0020304b82a0941e8740700e02400a0dc304b82504a11810038090029344b8104388a41e0480900243709417450128458581003809002d344501043907812024008048918398b621850100320890fc370c0af0490ca240400c82c00b0fc2a08c1e2741c0490c81e860100320b00383f0dc2a05c960490ca140400c82c00c0fc2305c12244108390c0100320b0030372bc25048918398b429890100320b0134370c0af094122460e62d8901003208c0e02406116048110110340a0128370c0af0490c02a890100320901c00c0a8230789d0701243207a180400c824070038370a81725812432850100320901c00c08c17048910420e4300400c8240700303809818454138440f6140480e02404c8d010c388ac1c0440d02207002a340609585010c3b070110340881c00c4501043a0a41d8581003805002a190400e22d0740d001c340b2190400e2210761903400a0b8210480e4348b2288980090f4320c02e0388b2288981e03800b0d0332c80e8290740d00203a0ccb208c100390ca2e0aa250740d00343406899050100390740d) else (0xe03207a0a0024108380c22c0a2260780e0024400c02e0400c22c8981e03406002caf2a4a40729162d896200761a82800c2e4340a8270841c8508b429892200761a8580e0040bd094230841c8420e62d0a6258801d8680e003cb90de108398b4298981d8580e002cb62bca4244100398b62607a0a002c340b81003a0c62d8981e82800a0b821048100388b0288941d03400b100bd2ecb20c02e0841c22c0a2268801e8640d0040bd2c8300b8100388b0288941d03400c2f42508c210701a8420e62d8801d8661603800f054108380c22e0721603800905c140400c22d0a22207216034060030b629096244100398b81d85a0a002c340501003a0c62e0761682800a054108380c22d0a81c8580d01800b06817054140400c22d0a2220721603406003817050120420f0388b2210721503400c26417050100388b2210721503400b084120400e2368b82a8941d03400b084120400f0388da2e8841e8540d0030b92c821048100388da2e0aa250740d0034b9084990481003c0e2368b41e8540d0034340420e0310a6268881e8680d01800c0420e0308b4298981e8580d01800b0d0108380c62d0a6260780d01800b08c1c0400c42989a2207a1a0340600303a0dc34850100308b4298981e8580d01800e0e8230420e0318b4298981e0340600302a09c230711b850100310a2200761a8580d0180100d01a454140420e0310a81d8580d01800d0e823069150420e0310a81d8580d01800d1012e0400c42989a2007a1903400b0dc1c0400c22d0a62507a1503400b1012e070100380c62d0a6250740d0030370c0af4b81c0400c62d8941e0400e82400e0dc304b8210400e62d8941e0400e82400d2e4b24b821048100380c62d0a6250740d0038b92c92e048100390a6268801e8640d0034370d12e084120400e22d0a62507a1503400e2e52e084120400e0318b0298941d038050038340b8100380c62d0a6240700c002c23070100310a6268801e8640d002c370d4340400c22d0a62507a1503400c08c100380c62d0a6250740d00283f0dc304b8120400c62d8941e0400e82400e2e4344b82a0841c22d0a6268801e86a1503400f2f52e09423084100390a6268801e8640d0038304b82a0941ea741c04989a2007a1a0400e8240102e4370d12e0400e22d0a62507a1503400d0dc304b82504a910400e62d8941e0400e82400f4b8230721b0400c02989a2007a190380500383a0dc350d12e854100308b0298941e8540e0140100e92e08c1083c0e0318b0298941d038050038370c12e0400c62c0a6250781003a0a01400e0d02e0390a6240700c0020340b8100380c62d0a6240700c002c402e4b24b81c0480e0318b4298941d03400e100bd0a9214720aa248841d86a1503400d094230841003a8b82a896210761903400d1002547012a2e896210761a0400e8)) else (if j<36 then (0x480c326b03089884028c09321203121724e030c350a01a060150400ca2d07a1503400c2d8af070100318b62607a0a002837070100308b4298981e8580e002eaf2a4100318801d86a0a00242a09c100328b2200761a8580e002cb6070960400c62e0761682800aabc1ca58910400e03207a0a00281c054140410f0310a41e854110340500342508c21072108398b429896200761a03800e100bd2c8308420e62d0a6260761603800d072140400c22d0a81e85412034060032140400c4288801e8541203406002c350410e0308b4298941e8540d002cb90400e4308b4298941e8540d002c35854104380c22c0a62507a15038050034340a0104380ca2c8841d86a1503400c2f4340b8100390ca258841d8640d0030342b0100390ca2c8841d86a1503400c0d028854104380c8288841d86a15038050038b90400e4308ba250761503400a070170501043c0c42a07a150480d01800d084120400e62d0a6260780e002821048100398b6220761603800a0d02e084120400ea2e0a81e03800b0d02105c140481043c0ea2e0780e0030342c82e0400e4328ba250740d002c34264140400e4328b41e8540d002c3008c1c0400c62d0a6268881e8680e00343008c108380c62d0a6260780e002c170420e0318b6220761603800a0c01c0400c22c0a2260780e00289905e108398b429896220761603800c2c8100390c22c0a2250740d0028230841c26417456108398b01d8661603800e05c100308b22207216038009050100310a222072150480d01800b264100390c22d072150340090d0b20b81003c0e2350ca2e8941d03400d0d0990501003c0e2350ca2d07a1503400d0c023070100318b6268881e8680d01800d0c0230420e0318b4298981e034060030170420e0318b4298881d8580d01800c050100380c42807a14034040028100380c62d0a6240700c0024100380c62c076140300080b821048100398b4298981e03800b104402ec340c02e0841c82a896200761a03800f08414048100398b81d8580e0028342c8300b81003a8b82a8981e03800c0d027264170501003a8b81e8580e0030412f4bb0b8210728b82a89a2007a1903400e2f4b92c82e0400ea2e0aa250740d0030b92b0990501003a8b41e8540d002c3c0d02e0420e03189a2207a1a03800c0d4108380c22d8981e8580e0028340cc2e0420e0318b6260780e002c402d8af0400c62d8981e82800a10023070100310a6268881e8680e0030400dc340400c22d0a62607a1603800c100230420e0318b4298981e03800b100340b8108380c62d8981e82800babca908c1c0400c6200761a82800b0a82708c1c0400ca2c8801d86a1603800d0d01a050108380c62e0761603800b2d8a9258100318b81d85a0a002823068108380c62e0761603800a0d0140420e0318b81d85a0a002aaf08e960400) else (if j<37 then (0x41c50c01c41e0480c52f4b90d0ac0848b22107203c0700a41e0480c62e5348318b428506a1062c38858b81c304810812031033048108120314bd2e58841c4264150420e4308518170481081203141a0481081203152e0400c0288114158500c22d0a62460fc0c4298901203190aa22070c1f8790a0120316080413848104280480c60408a088ac1e030c102288480c40a11ca2d0710318c01f4700480c60710780c30fc1805c0c6140480c70681804e120400480c70420308318c0134400480c60621704d10012031a2306a1061442c82f0450210b20bc1140d021499058114084264160450340854320a0100320854300400c82110304310c0130490a010640c104a10210340c10c01e41c8411030412840840e8a011030c18041030c3004810210031417048102104064112150210192581140c40c80e2250010192500e40c40640e2150010324b80e22c4066140388b103004c120410a812031c1081020481080c305c1304810812031810813030c120428480c4a288440c3068980410310190589140c4064142350010150510c8288514150510c22e0a2146a2907081505010830404204c0c304810a12031103043007c1e0710a812031c2e4308b0288914310c1078120314108102866148388b6245856148310a62458390761838310761830410e83038b90360838510360838510360838c88a6043865046043864106043866168450360054328b8288841c58c10c41e0312300490c80c485c1243203112e87024ba1021034521040c30bc1140830b80e40030c01240c30b80ea25001016045020c14039000c17049030c1403a8540040e43422d8910400d4344298914400fc370c430429891c411003c08c1c41d861c2c09c2141d86142809c1c41d86143f07c1e071076186100350d08b61450fc1805d8510400cc1043840681043830fc2304c120410e18300490360841003f0dc310c103608705c1240d82103f0601740d8214400cc1022981141a0601341181141a041810c1704903600422d89a14322d89a1431008b42989a1451003f4298981203a08742a8881c387814c21c0a120420480c44c2100a8480c2104408290761a81191ca2d070e30470249e8a091ea2820fc176160480e821a12042030d178402a120308400410e82a81141043a810e30442030d12a2a040e17440286112093c429078120315330481081203151a05c120420480c68661622d89a1458661422d89a1458561422d0a626851a2f22e8961448b88ba2585101043a0ca044852854110360858ca0e4298112190420e60442c904c0c326504c0c3054142160410320388d0c190388d0c150520a21440540c20430d43422e0a10370c4302be04143c08c1c26c40601725a0410330408f0c1a0408f0c150330520700161c812030e10812030cb3c0c22c6100a3027c28420) else (0x104bb0b82101c5104bb0ba0a01c50b80e4348910b20b80e8284264140400e10400b8100308a14140308540441002e0308b4285864140388b12150500c22d0a143f0310a81003143d0e42122c40d10aa2007110b82020790a810031208050304120410a81003150304120408a0e8b8288841c40c107810031103043f05c0c81003141a05c1281003150304304420400c405d108100310358308b6268514288310761840681043a0c1018a150360840540ca1500110ca2e0a22107163043107812031412432858120316300490c8120316170490c81203162306a106244100994520c42985181a841850c400f0bb08c1c432071c400ccb20410c141a2641043041003522d8910400fc370c4302bd8981081003c2ec230720a41d8620280708841d86143f07c9d0710761a041c400d48b82985143f060172598581062ec3422c8881d8518400ccb20410e8286068990410e103f08c13048910410e81081003f0dc312be0a40d82203f0609640d8214bb2bc9d81d0360862c8af245036085264962450360852c82e0390010990500e40040540c2150010400d40c22d0a626851c400fc300310a6260480e82248b42a8881c48790a80c32e41022d0a12120410a80c4100354b80c22c0aa1471012e0300a81203a0870a11ca248841c507d1ca250780c50a11ca2d07123007d1c80c40fc1805c0c6160480e8220b90681022c4062120420310154500c81203a08648c134428980c504d10a1603123004d1080c485c134420310402ec2e0710c0288981e8624402c8230420e4300a22480d02822c88)))))))
def genIndex8 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (0x51414700924df000cc4cb221f000f000571af000e00ff0001306ba66c339f000f000d72ca56183bcf0003367f000f000551ef000e910f000f0004626f0000de8f0008cd7f000b418b051f0004904a654f00074a6408851bc426c110ff000f000d8f4261fd677c5fe5b06f000a12ff000f0001451f000f000f000cc62f0c3f000b8aff000f000590af0008ea29b5db49ea201218ea75cf00092eb866c76720082f00003e3f00061b0f000c49c0357d8f7830d7617e26ef000f000e1aa8eedc0f6f000dd59d496016f631f6748f000f000cd81730a30af4283816af000f0006406c436f0005f2403d93181ac25f000f000fea3929cf000240af000f000f000da70646055a141a7e1e4b19303bdf000c3a050d2f973412d3b0bd518438a92f0f000f000f00039d6f000f000f000f000a74448f9f000d0a4f000f000f000f00090eb2c750669c1b1f000c96530a926bd3ed0f000f000f000c10ef51af000013bf0007a4af0008ac5b5a294edf000f000d4d20265f0000535f000f000f3ee462af000f000f000a56f1c0540e773e013ccf000f000f000f00060935343f000b479128a489e0735116b38a9f46b44e733f8236a7a9fd807d5cbf0004393f000f000f0a0a65a65f6f000f0005486f000f000b05df000035ac5fd100dc46e67535028f000f0009175a673f000664cf00075c8f00024b39588c47ef000f000f00069cca11bf000f000f000f000830e703fb2c2f000f000f000f000f000f000f00021eaf000f000c8daa31bd810080433a108100318530900c00030334709634a10b1412870dd20e4030030cb3001014050620252084e52cc10014458107c0d070110054f0560c819e94510dc8304010204a05804004818014510114050400004d00004b0c4040380d913820470900455ca4a52017430410c405a32a002002207b8e00209610124018014e20538024110c2500592c300200b4dc0820443cd00a04d6c03c01c10002020110541060161c4b0434500100304510f2087c304a48e2805490573ad1810041811411013c52493403452422810811c20620033ca14228e2c324ecc001044708410935f0054c20c02cd01108021c28008200300100101710044504200404020110004204680401000118328700044108004104104204021515326244a18705e1495801001d000528b0470460000010000400000000813092992450005c04052c10840131850400812112800131080c22c31020870840840002000000401873020c208c00118000370300410605234048f1890821430d42033c418a0450c30e400100030100004a1001c008940408200d0401831c00c71c008b1429800c114705708b0002c008000a0050820971c51010000c73411880000040010020821c51820580803970431c30011030c80012c200018b041008107000181080008) else (0xfaba603ef000955c1ad14f3a522d4cf236fc76bc71ae927df0002a4dcea57183f0002506917ff719e476ad79f000f0007255f000f000f000273443644023f000c047f5c993edf00090dcf000068cc86364787538c8e7e3bec25b86d1e9cfc894cdf8f000f00066e8f00086f4548df000f000f000809b18ecd0e0f000ecbce891719e32933589d22ee2bcf000689985e0c0e9b3dc04a8f7438a6d36155e79f0009271f000f000f000f000f00005def000661e3384b3b006fed6f991ba9715f000f0001698f000f47213e7f000f000f00065e83071b5ce74daf15ff000701eb30fee2ab30002bf32bdf259c67ef000e6fa0d9ff000f000e98cf000954261d28e5011dc42e1f000a4b0e16688b7f000b683932c0632223361539dc7453af000f000f000f00012c1f000f0002167f000f000f00026301434184a7675d31596aff1c5c3cfd3495543c3cd116df000e895f000b02a860786367247f000f000f000f000f000f3aef000f00050f3b43766ae457bf6eaf000b2e02deaf000a26b8e49f000799ef000b8f0e37ce1722e9a1155375a546212f8f000f000f000f6b3b1f9f0007485851ff000f11c910310cd1f14b10a2a77d42fca1bf00073466c78f592221df00080f2beef89b934aa22e42694f000f00021c4c27745bc4056a73c336130a3235b9603f000f000f000f000f000cc7bf000c6483d1890fbe03d09070988f000948a424cf000f000f000369c96c1c993add66313f000c0c41d8c66edf000f000f0008bbf62cff0003426bd9354e64c37f000be5fa026f00053ad5a8126e7e037bc2cf000d982f000074f960d93341b8f7599f1ebab1a82346583558439cdf58f71d5daa5f0006531f0002353b6aa8537d81ff0008640f000f000f000f000f000063d1337a63442f1d43fa85c9059f000f000f000f000bd37f000937ac5c0055ff000f000f000831ee987f000a0aef000f000e9d3f000f000f000311ef000cafdf000a054d3290585b529259b5013f000667c646fa3c142e7a72566d5e0678707f000a177f000f000f000303984fd4f169f25f000f00091ab767bf000c06bf000f000f000f0004ea41089a46a80615dce886fb4d9369d3a9cc1c6d63c51d9d4a70b6f5370a5a004f8a07af3f6e132644892b5f631f086f000f0009ec3473296c3f000f000f000a8b9f0009322c5b2f000a3ba6048f000f000400c922f94e1a29452a9e71ecab8a75df000f00013828f04420af000e72bf000f3dbd69914fa9215270f0492f000217148b6f0002295b5d5514b30e8f000f0005995f0009388320e4decb596e150f000f000223ff000f000ce8af000f56a616198eff5f711cef00028b1f000f000f000f000a02451fb7ea0468f773a885f40fc448bf000f000f000784bf0006660614d0230f000f0001ac0f000f00074e09253c270c72e33fde2ea)) else (if j<3 then (0x24112af673a980c8256d80a261b3f000f000344af000f360554916c4f000b147f000f0008134c3c5014af000f000e8eef5a6f000f000fab1a040f00094ea73f20674f000c392f000c507f000f000f000f000f000f000d1604eae6422f000f000d39dd209f00085ccf000f000ddfdf00004dbaae4f000257ff0006137e3a771914548f84cf0001664f000bde0e016f000f00078240b8e94fb60b1f000f000157509d97693e196f000f000624bf00010fdf000917be88ff2b900048463734ff0003cdef2b0f0008030f1a6233546e17284f000f000783ff000f0009135550ebabdf00091fd2a4bf000f000f00001bf42ee4909da78f000f00054e9cdb655718381486a6218f00093403a6c062109d0f00073c6737d5938f000654f2211f000900a3493f000f444761306902ebff000f000f000f0007d279430f000f000f00053e9920bf0006754669105aef000b925f032f0004d53f000d1b2d5e2c5ebf0000974f0005723f0000514f000f0008429f000f0007197f000f000665ef000210bf29e65faf000f000d0b2006455d9841df00015bbf000f000b01cf1b940558275f0005560f000e069069af000e24ff000615bf000558bf000a9ce82642dd3a383f000f000f000f3b57569f2aa75eff000f0005a2ef000f000f000f000f0002c296106f000f0001c9c2565005af000359cf000f000f000d749f0004e2b7653d8e070920ea7ce36f000f000f000f00083480628f00045936546a5d25113850fc75819eaf000139795bff000f000f000e415318c7005e37bf68da02fa737f0002008f0008509532fa203f000f000f000f0004717636fc577f000f000f000f000f000f000c62c1d608526d695f000273ef000503bf000f00041db73315c5ee50a7e5c336bc8255dd5aceaf000b84ed467ddd0f000f000f000f000f000f000d0b5f000f000f000c73fa0eef000f0005ac8f000c0fef000109c2657140cf000f000f000f0000adef000f000f000f000f000e4d1c8098612f000a64ff0000e8e6060f4123981425af0001ae66256e9260481f000957d905e0dbbfa09f403c9d7f000f619b1e1a214f0002431f000502906826c1cf5a361bdb5e68a4c03aaf000fcf1f0004162f000acab75edf000f0000b07f0000465d9fdf000544bf000764611e3f000f00060c1f000f00085811282f000f000f6976e66c10044a25ae18e71f4c3b84d517c21d685ca4d4545a43b4af000f998f000f0003138cb16e3d7f000e4bd5521be9f0597f00091e283dec487b3d422b1d1a1f00092523536f00075f560878e72f000e20d895110dbf000b2e8e449c75b0d63e5b0f000937e60de55ad0acc6e582410e070606cb336685744fec40ff00024af46c5f000f00034e4eadf62c838544117d21960f4f000c0d9de4c98087456d0d3ba515ecb64d7248900b44587fbe582c6) else (0xf000ddb7860aa2c5327675e374eb42546312d6894408920c70830cfdf0ba7622a2f2f736f000d385f000f000f000f000e47bf00061f5f190f000350cc25e536539c0445a10d534cbd3204c76d74df000e1a0c0f5f0005461b94f2f03f000f0008ec0f000f000f000ecacf000f00046d24018475ef000f000f000f000b36cf000e15a9014f000f0001641f000f0007045a2fbf000f70498df6616f00002dc644515e9f000aaabf000f000f000e6e94b466128a2af03915157f6f0f70d02a15513e3f99189f01dd5a7865bf000f00074c88e35971622260f55f00054fff25c61a4f00008d613f1c363d5aced8dd685301a052275a9a5e1075294d8915df000f000986d2722f000f000f0009302b505e67df000908ef000f000c035f000c480f000f0001adbb7578d0f6921a8e2f000f000f000d3ceb5f0f000f000f000bc8755b18609462ff04af000f000d04d91a5f000e4c2f00013fbf000f0001566f60ef000f0003760786703e8526f9e382f059d248466f4713c983989f000299a2f0d0c9a13b30e2861fef00084c6da96f119f00043f4f4b2d30c698a1ac7f6b2a96ec2b62ec1821e1ae2f000f000f0002232f000e3a2d4f1f000f00042881258d118a316f00075c38148ea6a821f75cf644fc6c8f000d1f0e890c18df00094411713f00091f76739f0009ec2e6f3706e7d479710631943caf00096d9b983d53bf00038dbf05cb4a992c900bf6651dbe7f000f000a0d090adf512f000e0658b47668081336ac10328aaa769cb2aca0751412bf000c684152f242408271144612003237484bba4ee4f402172234997c6bfd620d69e732b62402267470cddf79d946533f000109a398d8419f000f000f000b5a5f0000075a2adf000f0005611c3daf5c1f00075ee05b9f000f0006165f00032435702f000f000b2a491f6f0006530f000f000008d198f00e129a32076f341738df4b6b156e44c209ff000b14ea8d8352df000b1d8a35e929aa6b8f0008420c129387cf510f2ff86ff1058f000ac8ff43b32db50a1f000c2be444240f9da6bf0005551f0000b033528f0002705541a334ef000a091f000c45ef000f0005701f000f000a56cf0002287b6d8b0d6f0001db9f000f00076a252c40724f000f00011d1f00038a0f000f000435f656ef0001c5b8dd2433cd1cff000f00066d4f000f000f00020c520d720a8f00085baa386f000091df0008ab0406da4beec0af000f66ff000f00084b1f000f0002400254ba0a70dd4d042f000f000b637d1646085f0003a7c029fa562f0006db014a0f00039df4aaaf000f1def00036b131be8ed10417f0000ac4472d48cf367836a7f000f000d17e5159f000f000d473f000285bf00054eff000f0000558f0000a69c41eb9da519f2711b6ca9169b3b4f000f000f1daa237f000dba752d5161026500e870ab4d20f))) else (if j<6 then (if j<5 then (0xc6dbf00060a5f000a0aaf00019fae62e227af000f00045d1f000f000f000d0cff000f000f000947cf36245e7f0003192739be0384020f000d51c13ec02fdf000f000f582f0001515f000f000c96c644df000f000f000b3c2f000f11565b4f598f000d88a60634e9b31d4f0007aeac5e5c2f52c3ab176cb0ec0095534f0006721b464f000ee2cf0005c61f0edbb80e079c1c1d74c22b314f6f000aad09667173bf2d2c4bf61e58f2c40aca939f0007709b3900345b643f0b935aaf000f0c972c35860f000a3fe31cc987bf000f000f00020ca21fffa06a8f3b87ae4c9e2a5f00051ee09e860d4c45d043a635d02d0f000f000f0003098f000f6da0078b6b773d689fbd868f000906826b9f000f000f0005553f000760ff000928e9555f000c0ecf000f000334ad671f000f00040e53a4f6049c708f0008e99e8f887277d5295eaf000f000f00021cb113ffa0af000f000f000ee55890592d4d70bf000864474258edf71f8f000b06f1de7838bc09ef000f000f00046f264b7e6421195f00053ef01b7de899cfe2423b3ffc524758cd627e8a4752344f2e8f2f5c5f000f0001168f0004359a081d358948c9433f000b23d75a816dd7500d3278494e8aeaaebc58a0745d741f99b02a0e5f3a606f00019ba8a3dc281f0001acdd74bf0002544f000e5da701126dfc49d70b09d7f20dab4a4157ea862e3c332cab730f000a30bf000f1acf0003111f0000ef35184a0b3d624c285c08b8e2ff0009182f000f000f000285af000aeccb3aff0004b6ef000d2e2f000956bf000f000a98ef000c574f62d8addf000a1b6f000f000729df000f000f000a00bd2c77591f000f000f000f000851d96a00525f0000c4af0008102f00065aff000804306a11733f0000e608c17a71cf0005550f000f000f000014219ddc6813454a0e284aef20746e55260f000f000ddd740621266b6bb79e040df51e7f000f000aa1db618f000f15c513a72acf000024ac5545df903874503e6c70539f0005a7e90e3f000938f74c7966551cd66a8596362d7759eb342fc69145b706af000f0005236f00031b5f000350d1ecaf000f000141cc32e10198ead337610be6aeff000e4a504c0f185f000f00011c7402df000f000f000f000833353a4f000f986b4a37409928bf000c4eef0001db859db147f2022f000f000f0000261a93e9865a43df000f0000332f000f000f000f000c2635638f00004cef00052e5f85ef468f000253f4af586c9f614e401e28df000f000f000052ef00069349568f000f000f000f000e3f3f000f000f000f000f000f0001a3f28e4f000f000366df82bf000f000f990d52040f81aa474f5d8e8dcc640dd6eaff000f635f000c9e7f0001246827381d0f0001154f000451742cbf000f000f000f000123bf000f000ea2f3398edb241e6f000f0006519b18a1ad8) else (0xf000132593acf000f000f000f000f00015082570c720f0003127f000f000753cf000f000f00004f0f000e6fb2305cddaa4cfd23af000f000f00034cc797f71a31687d64df000f000f000ed305074f000f000f000f000c0bbf65cfedca375f000c474f000f00094cd6229c3bff00045fc2edb9e5ac63e02497116c994945cb29b08c2a6c0e0c7f00095dbf0008e1d86b550b6f000d11a269b49a6e1794eb7f000f000520081a9b31d39ecd173f000f000e194f000d073f0008e305427f000f00082a6f000f000132d96881286460bf000f000f274f00024e2f000f000f0008a67f000f0009821627ff00012a2e10873fc7228f000a33df0008317e303fda46991f000b07f4972f0004a6f16f1695ae33ff000cef70006329215cd3d5d9d6122a3f00081514369b373f00023e2c57c7238e05344d6ed84218b6511c2d8711d886c7241973d3ad7b003a3e42017a676f00014a182fae178f1fa76059b78f579bae0b703522477594105936df00072f7f000f0009372f000d488f000ae4842b21097f00006eee0bd12ccf000ca9ef000c4c1c2daf000ec1bb099f000d399f000e02bf00006bab2d6f000a8d440cece67f000b29891c3f000f000f5c262e3f0005a14f00005bd0ea1f00098839309474611ef79675351f00081227740f00012f6f000d2eff000f000f000f000e67a328cf000f00023944af8f000f0007572bed861fc93f5325fdab90ba56396f0004e6131127143e2de121380d8e2b433dfc3d13c3b99a7ce21ab7fcae985ddf0005aa9daa3f000f000f0000152be4b22203096f0006a73f000f000f000f000f000e91bf0001623f0001ccf94fc13d5f000f0001350f000b964f0004abbd186f000f000a4ac36a6042bf000f00079dcf00091c8a8e3f0008af98101b82db490809596f5f000a5ab667ff000f000f00011a2f000f0007aecf000f000f000f000f0004941b0d160c0f000123eb00e61f1f000d8699404a0a6a414f0003ddff000f00033a5f00054f321c2d3b8f000162b6dfeeaa6f00032b894dff0001e91b8b09c77f000f00044aba4c4817d1446f000e54ef000f000bd01f000f000d3a3f0006d7bf3446ca6f000865fba360abe4f2bd3fa8ef484e8f000f000f000f000e299f000052b06e69cd665780b7ef000f000f0003756207cbe2d26c2f000cab7f000ae34569f2301e3f7f000f000de8bf000205242d1335c9917f000f000f000a13db123f00096cb93b7f00046ab6010f000f000f000f00024168be3252cf000cab3f0000ae5f0008e6386ceb21b6db1f1806ce51438473119ed1457922bb050f00061b8ab79055bd3e683cb450256fdf000bb024eb01407333be966a1e8f000f000f000a992415e93072552d2cea04ef187d6e254501459d01bf000c52aa74796a57b19f000d202f000f36e2573e6be7dc646c619a55a95)) else (if j<7 then (0x6936133ea0cbb6f8ce08f4b8f000161ac6b0f000d545d70a8d26120685bea368f00095f4349be12e93c8d21af0005125f000f0004a9801caf000f000c3b943e11dc803c70985b15833b1f48f571b44f9c280f2171679f000a3d8f000f00006a3f000f000809d62966557ec38f0004adab608f000e09438f6f0005239c036f000f8a8663a85fff000f00005809629324e1136d647f0008861c366e97cf000f000f000f000f00064f7a55af000f000439cf000f000f000b2050126f000f000f663f54aa66bee33fa99527ceecf3491990608640892954c16f62477923104ec26eb1272b12a62dda1edd658b3bb34822aad012181f2b59f71f4b22770845e78db14d066f00045ec928ff000f000f000939569d5f000f000f000f000d45ff000485db4d51728843942f4807b421281dd918f4670f000ea37e3c4d04ff0007712f00063f0e13cf000404647614d22f000e0f1566e43563ad528a6f0006308ee8637502262f000f00026cc1547f000f6a4f000913e505753470338f0009248f000f000dbf7fe3cf000f000d42ae19c868e4447f000f000f000f000f000f000f00043d02e3b033a2999f000b5d8919af027d71d56dcf0005ad2f000f000f000f000f000f000d649b34df8e6a4dee5df3ab5ec180d82f00092d98321047aa5948174205f303af000264ebcaaf000d9bc1aaec71852fc82bba6d7761b9541b4058706723574f4659df000c01f20ea357ac170f000f46966d3f00006acc5c6f000f000dc7a70c2b1d3a63ff602f000f000747062978080ae9ef000c2918499ca7540e6f000e4409ea6f000ceb66c79b5c4f000e49aa5f245b824b41559b72ff000f000800100cca326f0003402d72ae02522a77413f000f0006c0e01248389134bc3800f0eb8d13188e604c95bd6e0f000e257365d96a9e1af5e53f304e27b8199a2ae21e9838cb82ef000b225f000f0001dbff000c4977a7df0005d1181df45c731398ecebdcfb9fcf12cf000f00094ad599ff000d8c0dacec1072c018355beacd04c0e1bc1a88e5bf000f000f00005d4f000f000b140410df00076ec31094662e012f000f000207df755f000831c96e3f4caf000f000450bc9eb045292890033f000f000f000f0002ae3f000f00031b4f000f00004d4f000f000f000b03172b7025d4aac163346cff00055b7f290154d2686861df000c656f000f0004d46ee9436adf000684ff0000b04f000d692f601433071d7b45530b7f000b42cf0007d431ee9f000f00035564a5df000d564f0009527f000f00054b5f000f0faf000940ef000653e342d5893e46c843268b415d05e32926a7ab2610c714cf0009e5ef000f000cf3e837f69f3c668f000d3ead0ab0ad34250722273d2f000f000bb05f000f000f000f000307eb19bf53df000159ab886997af0003104f000f000f000b5fba625a43c) else (0xf000f000f000f0002149f000f000f000bbe6f000f00013a84d88f00082e9f000f000f000f000b242627efe594198f000cd3ff0001586f000f504e6d09216f000f000f483f000a4c5916ca498c39a861cf00035f1f000246df00084dc6435f4bcf23c3563d96a12f3f000f000f000232af00021ad964bf000b9eef000f000d2fe93d3581e06eff000b92f074aa44ef00085d6f000f000f000f000f000744398b3f0004458f000922ae66a14baf00048223163f00073c0570ec3ebf000caaff000f000382069d2982a0d5af00085d73d50f000f041f501aa9af000f000203cf000f000f000f000f0000e5df000f000f000138ef000b3c9f000f000f000f000419d72c0c002f000f000a1ec97143abcf000f000f000f000c11f3090f00034d34ebb49d4ad2b48dc01c9f000c1c03811b4ddf000f0003311f000e2edf000f000331af000d04bf000cebd61148af31e1caa7224d0f000e68a5567343ec5f9f00073e5f000f000f208dc86126ddb81f00051bbf0005659f00095b5f0007dac851b525118d29f4a1146358e1652f0005576988ef0004f11f0003428a726442e58e5d3a6f6d6f000858d82785421e379f0003015902cf000f000f000b2eccf21f000f0001daaf000f000b245f000b6def000448ef000a310f000f000f000f000f000f000586662cdb5e47b49422cf000f000fbbe340df000f00095b6f000668b1e4a4e73824450c6f000160016f7f00023abbdfce08c3901c738355df000ada5755ebd512475e5dc40eff00082e69a50141b40b81661f00082baf08ff00048352dba653267291bc4f000f00055905b0df00055b3bd80c02e95952947537141f379a8f0008453564a93a1e2d3965542dff16e339fb3b61645c4959c432e3ee742541f39f488e12540f000160cf000a378f000c39ec5f8f0001e51f000f000f000f0004352c034f000f0006130f000a6b6f0007e37a34ce2a8f000d5d3c3746077c2ab5940f0009044ba74f000f9c601e02e3d405bba6ef00096668145292ef000608af1103314f000e92b12688007f000b4bbf000ba3c363bf0003318f0000a5766e4b4e5e377f000893f9204874e94e373b2f000e49f898be6b4f000f0001e881c827210e3245e52f75ff000f0007279f00080fff0005516ba80421c971ff000f000263930e4e4b9f000f0000ac9f00010723ecd440be0bcf000a131f00018b596cd33549a7b690399ded3dd82f9fcbdb17ab0f01696a0f7590bf47d614f6269))))
def genData9 (j : Nat) : Nat := if 15 ≤ j then 0 else (if j<7 then (if j<3 then (if j<1 then (0x6cc6febb6617f5db21bfaed905fd76982febb4a17f5da42bfaed205fd768cafebb4617f5da20bfaed085fd764c2febb2417f5d910bfaec285fd760cafebb0617f5d820bfaeb995fd75cc6febae617f5d721bfaeb905fd75c42febaca37f5d642bfaeb20dfd758cafebac637f5d621bfaeaa05fd754c6febaa617f5d521bfaea905fd75442feba8657f5d431bfaea10dfd74ccafeba6637f5d330bfae990dfd74c82feba6217f5d260bfae928dfd74942feba4857f5d241bfae9205fd748cafeba4637f5d230bfae910dfd74882feba4217f5d132bfae898dfd744c2feba2437f5d120bfae8885fd740cafeba0637f5d030bfae810dfd74082feba0217f5cf50bfae7a0dfd73d02feb9e437f5cf20bfae7885fd73982feb9ca37f5ce50bfae7215fd73906feb9c817f5ce32bfae718dfd738c2feb9c437f5ce20bfae7085fd73486feb9a417f5cd10bfae6305fd73146feb98a17f5cc42bfae620dfd73102feb98437f5cc20bfae6085fd72d42feb96837f5cb40bfae598dfd72cc2feb92217f5c750bfae3a05fd71ccafeb8e617f5c660bfae3285fd71902feb8c617f5c620bfae3085fd71142feb88817f5c430bfae1a0dfd70ccafeb86637f5c251bfae120dfd708c6feb84437f5c041bfae018dfc76ccafe3b6617f1d932bf8ec985fc75ccafe3ae637f1d532bf8ea98dfc74ccafe3a6637f1d330bf8e8995fc744c6fe3a2617f1d110bf8e6b05fc73546fe39a857f1cd41bf8e6a05fc73442fe38e617f1c540bf8e2985fc70cc6fe382837f1c131fe6e0887f310843f983221fcc1510fe608887f303443f901221fc41910fe20a887f104443f881a21fc00910fd641107e721887f339621f95cb10fb661187d7318c7e799465eed0240f6e8320faf4290bbda84a1ddd4651eeccb8877665443bab2a21bed8260bf4e110dfa70146fd380857e9c041bf4e018df970886fcb80a37e5c042bf2e020df9700c6fb38cc17d9c650bece3205f6718cafb38c617d9c620bece2305f671142fb388857d9c440bece2185f671082fb388217d5c660beae3285f571902fab8c657d5c630beae3105f571842fab88c17d5c450beae2215f571102fab88617d5c420bdce5885ee72182f7390a37b9c850bdce420dee72102f7390637b9c830bdae5885ed72182f6b90a37b5c850bdae420ded72102f6b90637b5c830bbce790dde73182ef398a3779cc50bbce6215de73106ef39881779cc20bbae790ddd73182eeb98a3775cc50bbae6215dd73106eeb9881775cc20b7ce9995be74142df3a0636f9d030b7ce8105bd74ccadeba0a16f5d031b7ae8185bd74082bf3a8835f9d440afcea18d7e750c2bf3a8415f5d441afaea2057d750c6beba8615f5d4209fcec284fe761067f3b0813f9d8319fcec184fe760827ebb0a13f5d8419faec204fd760c67ebb0613f5d820) else (if j<2 then (0xfd85110fec27887f613887fb09a43fd84d10fec0c887f604c43fb02221fd80f10fec06887f576443fabae21fd5d510feae9887f574443fab9e21fd5cd10feae4887f565443fab2621fd59110feac7887f563443fab1621fd58910feaa9887f554443faa9e21fd54d10feaa5887f552443faa1e21fd50d10fea85887f542443fa99621fd4c910fea6218ff516443fa8ae21fd45631fea2b10ff5154c7fa8aa43fd45510fea29887f514887fa8a243fd45110fea27887f513443fa89221fd41b10fea0c887f504c43fa82221fd40f10fea06887f476443fa3a221fd1cd10fe8c8887f463443fa21e21fd10d10fe82c887f414443fa09a21fbcca32fde64997ee248cbf712265fb4c832fda4d907ed26483f692e43fb49720fda4a90fed25483f692643fb49320fda4890fed24483f691e43fb48f20fda4690fed23483f690c41fb09132fbe6d987df364c3ef9ae63f7cd730fbe6a98fdf354c3ef9a665f7cd331fbe69987df344cbef9a263f7cd130fbe65987df324c3ee9b261f74d730fba6a98fdd354c3ee9a663f74d330fba68997dd344c7ee9a261f74cb30fba64987bf45503dfa1a83efd0d40f7e84a07be74ccbdeba665ef51540f7a87a0fbd43d03dea1a83ef50d40f7a85a07bd42503bf32a21df55150efaa7a877d53543bea96a1df54950bfeed985ff76506ffbb2817fdd932bfeec98dff764c2ffbb2217fdd731bfeeb985ff75506ffbaa817fdd532bfeea98dff754c2ffbaa217fdd332bfee998dff74cc2ffba2657fdd131bfee8985ff74442ffb9ac17fdcd51bfee6a15ff73506ffb9a817fdcd10bfee4b05ff72546ffb92837fdc940bfee498dff724c2ffb92217fdc560bfee2a15ff71502ffb8a657fdc530bfee0a8dff7050affb82837fdc132bfee098dfe76d42ff3b6657f9db30bfced905fe76942ff3b4657f9da30bfced105fe76542ff3b2657f9d930bfcec905fe76142ff3b0657f9d830bfcec105fe75ccaff3ae637f9d721bfceb195fe758c6ff3ac437f9d532bfcea98dfe75486ff3a8657f9d431bfcea10dfe74ccaff3a6637f9d330bfce990dfe74c82ff3a6217f9d232bfce918dfe748c2ff3a4437f9d220bfce9085fe744caff3a2637f9d130bfce890dfe74482ff3a2217f9d032bfce818dfe740c2ff3a0437f9d020bfce8085fe73d42ff39e837f9cf40bfce790dfe73c82ff39e217f9ce60bfce728dfe73942ff39c857f9ce41bfce7205fe73886ff39c417f9ce10bfce690dfe73482ff39a217f9cc60bfce628dfe73142ff398857f9cc41bfce6205fe730caff398637f9cc30bfce610dfe73082ff398217f9c750bfce3a05fe71cc2ff38ca17f9c640bfce3185fe71542ff38a817f9c530bfce2285fe71102ff388617f9c341bfce198dfe70906ff384637f9c141bfce098dfe70106ff380637f5db50bfaed995fd7) else (0x419380c7b062d030ff18420c06c5f762f4917748b9945c2e2dc016b00b44859762c6416020ae9056642adb15420a8d853ac296d147d8a200501c279313a289bdc4d76265b130f896904a4024c012420906c479a237f118f88ab4446421f610dd085b041f420a3101407ed83e641ec90f34878903b9a1d7f0e94072d838be1c110de186d8c362a1ab50d2f067f8333c19620c810631830f017fd0bd785d182df016aa0b20857a82b2615180a4a0508827cc13aa09a504bf0255c123c08e0844f4220210c50832840a41fb60f8d079f83b581d340e5e06ff037081ae80d26066c02fe817220b28055b029c4138009600477021cc104a07ce03bb81c5c0d26063c02f7016800a5c04b3023281038076e03600172809f0046e01d700c4804ec0192004e00007ff624c3ffb0aa1ffd8530ffe86887ff424c3ffa1221ffd0530ffe64b07ff32503ff98ac1ffcc540ffcec997fe764c3ff3a265ff9d130ffce8887fe73583ff39a85ff9cd40ffce2a07fe70507ff32221ff98540ffca8987fe54443ff29a81ff94540ffc86a07fe41503ff1b261ff8d132ffc68987fe31503ff12265ff88540ffc28887fe064c3ff02261ff81110ffaec997fd764c3febb221ff5d132ffae8987fd74443feb9ac1ff5cd42ffae6a07fd72443feb8ac1ff5c540ffae0a0ffd65443feb2221ff58f20ffac7107fd63843feb1a41ff58d10ffac6107fd62cc3feb1261ff58910ffac3207fd618c3feb0c41ff58550ffac2a07fd614c3feb0a41ff55130ffaa8887fd53503fea9221ff54560ffaa2a07fd51483fea1e43ff50f20ffa87307fd43943fea1c81ff50e20ffa87087fd43543fea1a81ff50d21ffa86907fd43443fea1841ff50b31ffa85987fd424c7fea1261ff50910ffa83307fd41943fea0c81ff50630ffa83107fd41583fea0aa1ff50540ffa82987fd41483fe9b261ff4d230ffa68997fd344c3fe99683ff4cb40ffa64b07fd32507fe99281ff4c910ffa62b07fd31503fe98a41ff49332ffa48997fd21583fe90aa1ff48540ffa42987fd14843fe8a221ff41b30ffa0c987fd06443fe82661ff41310ffa08987fd04443fe18a81fecc230ff660987fb06503fd83261fec1910ff60a987fb05443fd82221fec0d10ff260187f906903fc83461fe41a20ff20d087f906503fc83261fe41920ff20c887f9054c3fc82a41fe41510ff209107f904843fc82241fe41110ff207087f903443fbbb221fddd510feee8887f773443fbb9221fddc110feeca887f764443fbb1a21fdd8910fee87887f743443fba1621fdd0910fee65887f732443fb98c63fdcc531fee2c887f7154c7fb8aa21fdc5110fee26887f712443fb3b221fd9d310fece8887f673c43fb39a21fd99310fecc8887f663c43fb31a21fd95310feca8887f653c43fb29a21fd90f10fec86887f616443fb0a621))) else (if j<5 then (if j<4 then (0xe1d9f0e1586c8c33ca19010c0e85c542c8615710a3484b442446112d082d83eb41db60e3f06b68326c17260a7904af8227c0ec2066b02c38136407c602ff011f805fc0135ffdaff847f893faa5fc6efdbc7ea53f361f8defbeb7dbcbec1df518fa1a7cd43e4b5f152f82e7bcc3dc75ed44f6307adabd531e9b4f45f79edbce11e636f2c4792dbc7c9e2caf0ea78453c019def2ef0777613b8d5db3eed0976473af51d646ea96750dba65dd226e86b73ef39d69cd9ae5f8729f392a1c848e3a0718e38af1c45ee1b4709cb82b1bff6df656f70b7975bbc4dd436e32b6fcdb6f0daeb6d45b6889b372d9596c81362adb084d7e26bb835bf9ad18d6116acfb54d9a9acd46d6a06b4eb5a6bed2f6694b3486da32ed125685e340759f32cf156748b37c99adcccfc6649b2ff596f2cb19656a3296593e0c975648ab2245903ec7a46394b1ab98c54c5a6629a3132d88b2c39661803093d83a8c11160272fe097db4be175ec9af43d794cbc2b5de12ed6575bcba7e5cf8ae5fd721ab86e5bd5add096d7cb6315adb2d4ed6980b46059ee2cd8565deb274590a2c6d162a8b0e25833ac01d5f3caf23575d2b9215be2ad885686ab249582eabb755a2aab9554c2a9d4549f2a2c55048a7975392a9aa94c4ca5ab5298292f948aaa3e351b428b91448aa1ca50a7a832d408e9f9f4f9227a813c6e9da14e8a272f538ba9bfd4dd7a6d6135cc9a624cef265f9326098d04c41260f52f72973e4b6f25a1d2c7295d94ab3a53d52918943549f3a4e652618927f48f4a4625226490c048392406d1f768f52477923a251c1c8d93468c232bd189e8bcb45bea2c99158c8a784519a279512e6890a4450a20bd0f8c875d437a21a090c2085a7429aa133108a283e841bfa0bed051281fc40e020611024880df403fa00a0ff907f683f841faa0fca27dfa3ed19f50cf9907c683e089eee8f6a27ad63d321e858f39079713c8d1e2c4f0a2780c3bcd1dce8edd8769e3b089d484e8f2738939871ca70e49c71dc38be1c470e166705337f09be04dd8e6e3a36d21b4c8d95c6c1835dc1abb0d4406981348c1a298d05667d433ba19c08cd44662732cd19458c8dc63f331ae98b64c4aa61e330ab183b4c01e5f4c2f4497838bb265d0f2e5797118b7a85b862d9316b3cb4cc59f42cca16464b16058472bc695b94ac5655832a7b150cca794534f296a149d0a42851bd289c9431ca0aa4fec27c193c449d864e632701936d49aaa4d07264f130b097984b63258192ab0945049a42494923b49162485a240f11f408f04472b236e91a3c8c4c45bd22aa11340889843bf21a210b00847841a620a31035080e8400b1fc80fce47da03e701eff0f60c7a223c8d1e120eec876923ad71d370e7f07338393c1c728e238705c37ce1bbb8dc806d8036601b000d6a46aa434fb1a448d038671432f) else (0xa04014088341004908038160702a1006820012281007036190a8381a0a0220d0401346833190b834190a03c1a074200d04003850220d054200f0541c080300c00c058281207018006050200e060200461e8f05c1007030100601800a0803c180a04014080120200e0602c0e0501800814080381b0c8541c0d060280801306833190b834190a03c1a0c0380c0068f86c33148883a1a0b03e14040180a02702c14090380c0030281007030100230f4782e0803818080300c00502c10050200c0430401e0c050200a040090100703016070280c0040d05c140701c0802001036148903a1608c28080301404b058281207018006050200e060200461e8f05c1007030100601800a058200a040180860803c180a04014080120200e0602c0e050180081a0b8280e038100400207a371b0cc64241108440190c05c2c110803c1c0d45a210b0481c0981e8f0200e0622c10064280c005880381907034180a4421408012c66320d0641e0d0622c0e8501800c0722c0e85020080038f47233190b04822108803419088401e0e06c1207024c7a3c170401c0c0401806002850200e06c321507034180a02004c1a0cc642e0d064280f068300e03001a34170501c07020080040401e0a0421d0c0502004908038180b03a180a030012200c8381a0a4421d0c04009434198c85c1a0c83c1a0c4401d0c03001c3417039100743010040024200f06028100502004808038180b0381406002050200e06c321507034180a02004c1a0cc642e0d064280f068300e03001a34170501c07020080040f4200e4522410060180090803c180a448200a040092100702d14890381406002450200e06c320e06831160a448100268c8341907835168a4481c06002c1c8b4481c0802000e3d1e0b8200e060200c03001410078301408028100240401c0c0581c0a030010281007036190a8381a0c050100260d0663217068321407834180701800d1a0b8280e03810040022a78d534ba96cd4932a3b55156a872541829fb94f61a76ed3a1a9c5f4dcfa6b7d33d298f34bfea5bd52bfe951b4a00a4b9d23e290b347cca3a8d1b5a8cc94604a2cdd14a6895d4469a1f750e16868142f2a144d0882835d4133a060d01627fbb3f749f7ccfa1e7c193d919e8b4f24a77e73b5d9d714e9c2740f398c9c7fce27e703737979b80cda866c5f35bd9aaecd38a68e1340799bd4cb4a648b3194988ccc23260112f849784cba5e5c272db396a0cb33e58972bd995a1cab22547729db94abca34e509f27cb939649aea4c6d25cd92a4c9316487123b4919cc8afa447521bf909dc8302408b1fd38fb0c7b763ca11dcc8e96c72ca386f1bbc8da9c6bce34df19f48cb8463d63119181a8bd8c5d462dbf16768b0fc56fe2a9b14d28a394504a27651364898244a92246511d288b4c44262153104987ebc3dd)) else (if j<6 then (0x883a16070028261208a2d10858240e04484c200f45c291085824049090401c8b4441d0b0380121708031170a4441d0b0481c060060d05c21090401c8d85c2a130781c00d1986c34130803d1c8d854220f0682404e1b0902c1309045208f47236170882c1207024066220a84c200f47236170a8441609013868210a048208f07236170883c16070038661c0d264240e4683215078240e03003838194a834188a83a12068180161c0a0411e0c454220f054240d030034381a4a838188a83a1206818016320ca501a0c8521d07014014340a0411c0c85c290f0541c050060cc349407032148741c050050a0441c0d054200f060280e0401804007068280e0501c060100101007031160a4481c060024682e08038188803a18060028200e0622c0e850180081a0b82810070300e030012b657aa548964881d0400246e34180b9160a4481c060028542511884388803a180600286e341509c2e1445a200e8501800c1288c4212080380e0300123417050200e0601d040024682e0a0380e0401000814088361a0a83c140301004a1408834150782a0e03410060058a0441a0a8401e0a838100601801834198c85c1a0c8501e0d0601c06003450200e06c321507034180a02004c1e8d8642f148803a190b0340803011a100703016070280c0040401e0c050200a0400900b040140803010c3d1e0b8200e060200c0300140a0401c0c04008c2d15094420a44a200e868240e030034602a1288c421c45829128803a1a0700386e34180b9160a4481e070028160a0481c06001850220d0541e0a4380e040140160a0401c0c044180500402c1087028100602401010078281087028110601401428100642a0e068290e04418050060a0441c0d8682a1007830140481004d050200e06020046058200a040180860803c180a0401408012050200e06c321507034180a02004c1d03a160a8481c068100123e1a0b450100722a10078300d020034741a0a8401d0b4501e0a0340800c1f0d8662911074341607a28080301204e1a0cc341407839140701a040058d0280e4501c08038120400502c14090380d02001c7a1007228100601a0400482d14080281006024090100702d14070280d02002468320d064280f06a280e0340800c1a0501c8a03810048100121a0a0381407018040040401c0c85c240e03001034170401c0c8401e0c030014100703216078280c0040d85e29120742c110200c0450d05c140803818070180091a0b82810070300e0381000a1a050200e060280e0300800a0582812070180061e8f05c1007030100601800a058200a0401808608038180b038140600206833190b834190a03c1a0c0380c0068d05c140701c0802001028110682a0f0541c068200c00b0582812074200d04002014080381808834100481e8f05c10070200c8401a080058401e) else (0x8381b8ac54260c05c2c1509a2e148842812070280a437150942e160a049168883a16080381400f1d0dc682a1187034170a850200c45c29110742c120701802a36148642c0d45a210a0401808b1407036190a8381a0c052210a04009a3417068321407834188b03a14060034501a0a83c14884280c040128682e0a0391607428100400283414070280e85018040048f47624110803e120803810070340e0070683217098401e0b850200b0480981a0c86024100702c110702c0e0060d8481d0b0441f0a0200c05012c6c2f12058220e8381006028016220d054200f0702a0e04818060060401d0b854240e030010220d0401e0a8441e0c04009434170401c0c8401e0c0300142408c2e11050200c0440883410078301508828100250401c0c8581e0a03001036178903a190b0441a0401808b1106c34150803c1c0d06028080130682e0a0401c0d0601c060028441b0d054200f05012070200963417050200e03c1007020014340a0401d0a0380e02002470261187c3013088401f0a0240e0501386e301288c2e12088401d078200e05003874230d0401e0e0642a0f0481c0600682c14090380c0030281007030100230f45c10070301006018009058200a040180860803c180a04014080120200e0602c0e050180081106c3415078280602009234170501c0702008004068280e0501c06010010301207c3a1204019080341400b0b858260b850200a0441a0a0258602c12058220e054200d05002c70240f8643012088381b0a0220d0501386e30120642e130883c1b074200d0500387e371508c2e120803215070200d0501801e3c1107c3610450200e064240d03003434180a840180b450220e054240d03003866220f8683010078381a8a0240e04813866220d0642610078381a0c4541d090340c01008038190b054240e0340800a1a0b8200e0622a10078300d020030200e0642d14078280d020028682e0a0401c0c4501c068100163417050200e062280e0401c090200342810070301407018040048f05c100703114080300d02002c200e0602d14070280d020028662e0d0501e0d062280e0340800c0b850200c05c28108702c110701401a37180842e10070350f0401c090060e44219090401c0d064290f0441c050070401e0c054200f060220c02802c381007830150843c14088300a00c0e054200e060290e044180500587036150803c180a4380e040140181007830140843814088300a00b0e06c2a0e0683014870220c028030401107035168a44c12070228401107035168a44c1e070028481208a2d14898240e044884240e45a29130781c009190441e0d4421d0d0481c08a190441e0d852210e8682404a1e84c228843a1a09038112330983e148843a1a090124220f07035168842c12070228220f07035170a44216090128220f07035168)))) else (if j<11 then (if j<9 then (if j<8 then (0x340e0078f472371b0cc6430178b04822108803419088401e0e06a2d14898240e04d0f47238190b0482110064241107035160a44c120290f472371a0cc6430170b04822100683213088401e0e06a2d148983c0e00d0d85e2912074228b05224080301404d1b0bc522408a2d13070200c0500305c0e0582812070180081a0b8200e45a29130803c180600305e240882d1308828100602285c100702d148903c140600286c2f148903a1145a240803011634170401c8b452240e03001434170401c8b452240f0401c080060d05c0e45829120701c040050f474391b8d06430170944621090401c8b452260f03802837180bc5c2a12849168a44c1e080381400f200e86e341708c200c4582913078240e0300407a3c170401c0c45224100601800c1e8d8642f148803a1906a2d120401808e1a0cc642e0d064280f06831168a4481c060040682e0a0391689038100400287a321609044211007c3a1a0c844200f070351087434120702587a2c1208842200f86c341909044200f07036148843a1a0901587a321609044200d06426110783510074340e0088a4481d08c2910860200c05012c5e2912074228803a18080301400c14088361a078291007430120601801a220d83c140803818080124481d08c2c108682810060228441c0d8401e0a0421d0d0502004c178a4481d08a210c0401808a14088381b0d0401e0a4421d0c04009a2811070361a0803c148843a18090381004f1509c4a2310870290b0401d0d0581c00e1f0b44c23110803e1b0d04c200f852210e868240521e894462110048200e4401d0d03801a2b15098461f0e86c270a4421d0c0481c0a0280c05425118783a124401d0d0401c0a0070a8461c0d840190a4401d0d0481c060070f45e2910074320d4421808030118281007036190a8381a0c052210e8602004f14088361a078291086018080258e46e36190b048211006832180b8582210078381a8b4421609038130391c0b048210d064301509044200f07035170a4421609015472371a0b0481a0c85c2813088401e0e06a2d110742c0e00a8d852240b045170a44214080301404d1b0a4481608a2d1107428100602801a280d0542810078291107428120601801c1408038170a8481d0a0300141a0a8401e0a0441e0c8502004b1a050200e0622c1007832140600302c11058200a040180880d054200f06028100502004a0a0401c0c0581c0a03001236148902c1145a210a0401808b1407034150803c180a44214080130681408038188b03a14060028501c0d054200f052210a0481c080268d028100722c0e858200e04002c681408039170a03a1407010016391c0dc6c261289032180b858261208a2d10858240e04a0e8702d1308c34190c054261007a2e148842c120290e872371a09446210d0642e14090401c8b4441d0b03802) else (0x1e0a4421d0c0481c080250f4401f0e84c228843a1a090381183c1007c361307c291087434120260f04413852210e860240e05012c7a2f1003510860200c0448801a0a4421d0c040090220782910860180802406430170b044200f07035168842c1207023c32180a8482210078381a8b852210b04809e1a0c85c2813088401e0e06a2d110742c0e008068228b852210a040180a025045168883a1408030140090d050200f052220e850240c030030321145a210a040180880c8401e0c052210a0400921a0c8401c0c4581d0a0300141a0b8401e0a44214090381004b0c0401c8b03a16080381000a0d054200e45c280e8501c0400586430170b04c241145a210b0481c08d0c8612e15098401e8b852210b04809a1a0c85c281208039168883a16070034341709a2e14884281207028096180922d110742c10070280141a0b854281045c29110742c120701801c1906a2d10850200c0440641c0d0602910850200490d0641e0d0622c0e8501800a0d03c14884280c0401201c8b03a140802000e1a070280e85018040040f476120823c1c8d0401c0d038018130803d1c8d05c28100582404b090411e0e4682c110702c0e0058cc441d0d0581e8d850100602809836178842c0e46c1c080301400b108682a0e4682a0e04818060058e4641007236170a8481c06002c401a0803d1c8d054220f0602004c1e8b8581007234190803c1806003072240c8451b0b8441408030116220c8401e8e468301508828100260e4321007234190b03c1406002c441b0d054200f47234140481c080268d05c14080391a078200e04002c661a0a03c1c8d8501c07010016331107c34180803d1c8d850120702809c37180842e10072360f0401c0a0060cc421a4c8481e0e4683215078240e03003c160a0481c0600181408038180801187a2e080391a0c04018060028220b040140803010e1007a391a0c050200a0400941007234180b03814060024642f10074321606810060228401b0c8541c0d06028080128642e0c8501e0d0601c060028441b0d0541e8d0500c040128682e0a0391a0702008004868280e468280e0300800908228100703212068180121006228110702a12068180141c0d0652a0f0683115074240d03003450100722a10078300d0200282a10072280f0501a04004868280f072280e03408009140411e8a8401e0c8481a060058702a1047831150883c15090340c00d0e0692a0f0703115074240d030030200e450200c034080080803914070280d020020341407835140701a04004840180b8521c0a8380a0095a065280e06832148741c05005850200f470290f05418050050541c0a43a0c02801c681408238190b8521e0a8380a00c5a069280e064290e8380a00a0803c148702a0c0280202a0e068290e8300a0081e8f0763012088401f4522410070)) else (if j<10 then (0xb0542511884388b0401c0c8581c00d1e89044200f848200e0401c0d03801a3d1288c4220090401c080381a070034481f0e84810064200d050028602a1288c3c1d090200e064200d05003864200c8441e0e06a2d148983c0e0068d0501a0c054160a44c220b0480983a1c89c2e1405a29130883c16070034481309045168a44c12070228441a098401e8b05226090128421208039168a44c1e0700286e1c08031160a44c1e090380c00c190803211078381b0a4421d0d04809a320c8441e0d4401d0d038014350d0602b0a0421d0d0582404b1a08c421c0b852160803a1a0b03801a3d1204c24114421d0d0481c08b1988834130803e148843a1a0901307a120803910074340e0048a8200c852200e868240e03002c64200c8441e0e06a2d10858240e0468c840190883c1c0d45c29108582404d190803211078381a8b4441d0b03801a2409848228b44216090381143311068261007a2e148842c1202608424100722d110742c0e0050dc381708031170a4441d0b0481c060070d0602e1288c42120803a170a84c1e07003c78281107c381b0d04c200f854220f068240501b0a448180b858261208c2e11058240e0478d450230d0602a130803e170a8441609013c6827118842e14090401d0b8441e0b03801e3a0e068200e0642a0f0481c060060d05c2a1284a170a84c1d080341400d1e0a0441c0d84e150883c18088341404e1a8a0341509c2e1508828110682809a3413894281285c220f054200d05003466220f868301007c28088341404c1b8c042170803a0e8401a0a0058dc38170803215070200d0501801834180b846108582a13074240d0300346c291305c2c1385a2a11050240e0481386827118702e1408032168a8441e0a8481a060088e0481f0c048221007a28090381204d1d084341208038188a83a120681801a3c140883e1b0842a1007834110701401c361489430160942e108782c100702401c351a0a034180a850200c85c2a108782c110701402437180902e13088401c878200e04803466220d04c200f0703214878220e0280387a301208114890401c0d0380163d190c05e2410880220e06a2d14898240e0480f4643017090401107035168a44c1e07003c481145a260e040180a0048f41c8b4522610078300c0050f464240e84516890200c0450c81c8b452240e0300100e45a2912078200e0400247a3012885168a44c200f0681c00c1e8c8602f12890241145a29130481c08e1e8c8602e12884240e45a29130781c00e12849168a44c1e080381400a1e8391489040180600207a32100741a8b44810060228640d45a2912070180080722d1207020080038f464200f874220f06a210e868240e0470f0401f0d8441e0d852210e8682404d1e088230a44218080301404a1e8bc401144218080301122007829108743010024088) else (0x1c060068492210078391a8b4441d0b0380181c0803c188b44c1c090300c00b08030148883a14090300c00a0e0541c8d0602a0e04818060058c85e200e8642c0d0200c0450c840190883c1c0d0200c045064228b44214080301101a0c84c241145a210a0401808b190803a190b0441a0401808a1b0bc5c29120451689838100602801a37180bc54250922d1489838100602801c29120743611852210c040180a0260a4481d08a200e860200c05002c562a13090461f0f074270a4421d0c040180a0288c05425118783a124401d0c040180a0070d852240b054228b852210a040180a0270d852240b050228b4441d0a040180a0070e06e2b1509830170b04d170a4421408030140511b8a84a170b049168883a14080301400e1b0903a1a0b0441f0a0200c0501306c2f12058220e8381006028016381308c3e1a0c04c24110803e14040180a0280dc60251185c24110803a0e040180a0074d228108722a0e040120600504516884281006021c64200c8441e0e06a2d148983c0e006884241007035168a44c1e07002c64200c8441e0e06c291087434120268c832110783510074340e0050cc441a098401e0e06c291087434120270e464120803c1c0d4401d0d0380183210064220f07035168842c1207023464200c8441e0e06a2e148842c120268c840190883c1c0d45a220e8581c00d1204c24110803c1c0d45a210b0481c08e1988834130803c1c0d45c29108582404e10848200f07035168883a1607003064200c85c1e0d83a100682801637180842e10070360e8401a0a0060f474391b8d06632180b84a2310848200e45a29130781c0151e8b048221006832130883c1a8803a1a0700407c2d1308c44211007c361a098401f0a4421d0d0480a63d1288c4220090401c8803a1a070034723816090421a0c8602a12088401e0e06a2e148842c1202a8e46e341609034190b85026110803c1c0d45a220e8581c0151c8e06e36160984a240d06430170b04c241145a210b0481c0961d0e05a261186832180a84c200f45c2910858240521d0e46e341609446210d0642e14090401c8b4441d0b03802a37180903217098441e0d83a100682801c3718094461709044200e83a100682801c1a0c85c2a140581d0c0581c00b0d0602e15098401e0b850200b04809a170a048200e058220e0581c00b0d050240b0441c0a8401a0a0058c840190883c1c0d45a210b0481c08d190803211078381b0481c08a1509c4a23108702e14058200e8602c0e0078683217098401e0b850200b0480981a0c86024100702c110702c0e0060e8702d1308c34190c054261007c2810058240511d0e46e341609c4a231086832170a048200e05c1c0b03802a180b048160883815080341400b1b8a84a170b050240b83815080341400e1508c421c8843014894401d0d0481c060078))) else (if j<13 then (if j<12 then (0x2e1408031160a4441d0a048180600688434150723415070240c03002c441a0a8401e8e46828090381004c1c0903e18090451c8d050120702009ab910a64241007234180a838120601801c1007031160a4481c060024341508039170a03a14070100161508038188b03a14060024661a0a03c1c8d8501c070100163417050200f07234180701800b200dc68301708c38100622c148983c0e0078a0441b0d03c148803a18090300c00d1508c3810062200e8681c00a140682a140803c148883a14090300c00e1b8d054230e05c28100622d110742c0e00788834150803c1c0a83812060180182308038190781c0071f8dc602a118702e12080320e0401a0a007af576301509446210e22c14894401d0d0380203a1b8d05a2a0d22c14894441d0b0481c060082e46eb61a0a9160a44a220e8581c00d1f0e86e3419ac85a2510868240e4582913078240e0300517ab91b8d16430170944621090401c8b052260f03802637182bc54250922c148983810068280c00f1b8c15e2a128491689838100682801a2d150a04a1a852200e8642c120701801c2a548a04a2310871168803a190b03801c3e16894442150068240f0742910074341207018024bd12a90462210a802410072200e8681c00f150943c9d09429100743010068280c00e180a84a230f27438124401d0c0401a0a0078e86e341689434990b85428120803c1c8b852220e858240e03005d72371a2b04a231086932170a048200e45a220e8581c0141b8a84a174b049170a4441d0a0401a0a0300406e2a1285d2c1245a220e850200d0500386e250d05c24910742a0e0401a0a0300386e301288c2e12488401d070200d05003840190a83c1c0d0602808012874371a08c38100622c1489838120601801e281106c340f052200e860240c03003450220e06c3410078291087430100268a0441c0d868200f052210e860240e04013c7c2d1308c44200f870361a098401e0a4421d0c0400a62b15098461f0e06c260a4421d0c0481c080280a8461c0d840180a4401d0c04818060070a034150a0401e0a4441d0a04818060070a0381a0a8401e0a44214090381004d1c0dc562a130602e1509a2c148842812070200a23a1b8d4682a1408c381a0c05c2a1408031160a4441d0a048180600c08834150803c1c0a83812060180183a11868200f0703015070240c0300346e2a118702e120803015070200d0401801e3417039160a4481c0701001434170401c0c45829120701800b1a050200e45c280e8501c040058d028100703116074280c0050d02810074280e038080091a0b82810070300e0300123057870200c45829130781c00b0ba58200c45a220e8581c00a5cac83899092441c8d0641e07003080990ba58280a44a220e8581c00c10849221007235160a44c1e070030240f07235170a4441d0b048) else (0x12340a0401c0c4581d0a030014340a0401c0c45c280e8501c040060702b1407234188a83c15090340c00d190b8321407834180701800a190803211078381a0701800a0a0401c0b452240f0501800a08039168a4481c060020200e0622c14890380e020028682e08038188803a18060028682e08038190a4401d0c0380800c08038188b8501d0a0380800a1a0b8281007032140701c040058c83214078381a0c0380c0050b8200e05a2912078280c0050d05c100722d14890380c0050d05c100722d148903c10070200183417039160a4481c070100143a1c8dc6830170a84e170a02d14898401e0a0300243d1d0e46e34190c05c251188424100722d14890380c00a0dc602e15094248b452240f0401c080070e86e34180b8461c08031160a4481e08038080111e8944621090401c8803a18060030602a1288c248803a1a080381000c1508c421c08032148803a1a080380800e1a050200e4581d0b0401c080058d028100722e14074280e02002c6e2a1285c281245a200e858200e04003874371a0a84e230e0682e150a040188b852200e858200e02005868140803a140701c040048e8461a0803c1c0c8501e080380800d1b8c038100622c148983c0e0059005410062200e8681c0091b8702e100622d110742c0e0059003810070320f03801037180702e100641c080341400b0a850200f070301407018040058c15e2511884388b0522510074340e0071017ab2182bc5c2a45829128883a1607003c60af170944621090401c8b052260f03801e4012849168983810068280141a0b85428120803c1c8b852220e858240e0300442e960a85024100722d110742c0e006868248b852220e850200d050180181245a220e850200d05002466210d05c1c8d8541c0803414060068dc60210b8401c8d8381006828018200d8642a0e06830140400943210064220f07034140400941c0803c188b052260e04818060060883410078291087430100250401e0c052200e860240c03002c381007830148883a14090300c00c0e054200e0602a0e04818060058702e150803c180a8380d0401801830578b8461c08031160a44c1e07003434140803c148883a14090300c00c0ba582a1408031168883a16070030421a0a8391a0a8381206018016b9590853212488401e0e468320f03801c1a0b85014894441d0b0481c060062642e960a22c14894441d0b038018210d0481c8d4582913078240e0300344212488401c8d45829130781c00c0d05c2a8b8501d0c858240e03003046210e2642e960aa2c0e8642c0e0068cc3412078391b0a4401d0d0481c060072e56412488401e0e46a200e8681c00d198843412078391a8b852220e858240e0300404212488401e0e46a2d110742c0e0068c05c230e040188b44c1c090300c00d0d050200f052220e850240c030030)) else (if j<14 then (0x3408439168a44c1c09038120600608c208a44c220f0681a060050e86e348a040168a44c1e0b0340c00d1d08c200f8722d148983c0d0300306e1045a2913070240e048180163d1288c421a0cc421c8b4401d0c8581c00f150a046210e06a210c45c29100743216090380c01213894462150450200e858200e8682c0e0078c054230f8793a1c09442190a4401d0c0401a0a03004e5c230e26c200a84a200e8681a060068a84e230e26e2810450200e8682c0d03003c54230e26c208a4401d0c0481c090300386c240d2642c1107c2910858240e0501386c244c858220e45c1d0b0481c0a0068e8729908038170a84c1d0b03801834168b1321007431160883c190b03801c1a0c8401d0c05c1c0b038014344c850200e45c1d0b0481c0a0060d034990a0401d0a83a16070180182c1288c429908039160883c190b03801c1a0c85c28100702c110702c0e0060e04c1a4c86026110803e148842c12070280a03712a642e120722e0e858240e05003474230d264200e8622e150742c120701801e344c8501c8b83a160902801438120612c1208c361488428110682809c371205d2c1308c35170742a100682801c38130612c1308c3e1488428110682809c371285d2c1208c39170742a100682801c37150602e9609442188b8541d0a0401a0a0300446a9508438160a84c1d0b0340c00c1a0a12a1087031140883c190b0340c00e0a8421c0c05a2a0e0581a060058d034950a0401f0e0622a0e8581a060070d030950a0421c8a83a140903812060070e86e351a4b92a100582a130742c0d03003c5428118712a10450220f0642c0d03003834170a850200b450220e0581a060068e8461a4a8401f0e4541d0b0340c00d1b8a830174a841150742812070240c00e1c8c84212080381a8b452260f03801a340d0642810078381b0c45c1d0b03801c3912064261208835168842c1207023472210c848200f07035170742c0e00685c269107c2e1508828110682809818092441d0b8441e0a8401a0a0060dc612e12849220e85c260e8401a0a0070e04c1a0c454269107c2a11050220d05013c6e250bc5024910742e0f054200d05003860230d05c2612488401d0c8541c0803414060088ea5c230823c1d0b054260f0340c00d1d08c35140823c1c8a83c160681801a230c45c208f0722a0e0481c090300346c240b0461a8b44214080301163612058228b442140803011437184b824108582a13074200d0481801c2a11848208a8441e0c8401a090300346e2a0bc5024104541e0a8401a090300384617090401f0e4541d080341206006854281007c38150742c0c03002c38150803c180a83a14090300c00c1a0b8200e86a2d14890380c0058d05c100722d14890380c0050d05c1007031160a4481c07010018340a0401d0d0622c0e8501800b0a0401d0a03a140701) else (0x4a1208c39168a44c1d080341400c1808c381045a29130883c1a0681801a30118401f0e45a29130781a0600608c2e150803a188b852220e858240e03003c341208c39168883a15080341400c0d04a210c45c29110742810068280c00e0b8401f0e45a29110742c0d0300306e3097084200e46c2e13074200d0500386e210bc50200e46c2e0f054200d050038732e108481c8d8582a130781a060068e442198a048200e46a2a0f0581a06007090241145a29130481c089108481c8b452260f0380122409848228b442160903811421090401c8b4441d0b038014170a840188b852220e858240e030034682e10848200e46c2e150983c0e0068d8481609848228d85c220b0481c08d1a0842e14090411e0e46c2e0f0581c00e0e05c281047831150782a120681801a340a850208e064290f0541c0500606932170a442180a44a220e858240e03003c681c8a0411e0c05a29130782a120681801e210d0642e9588439160743216070034461c0d2642e1588431170a03a190b0481c060088e44f14090411e0e46c2c10074341607003c4f140823d140803a1a0a8481a0600685c28120823c1c8d058220e0581c00d0a0411e0c450220e054240d030030421207035168a44c1e0700284813090441a8b442160903811621090401e0e06a2d110742c0e0060702b1408038188a83c15090340c00d08a2d10850200c0438702e158a0411e8a83c14068240c00d0803c180a4441d0a0481806005839168a4481c06001c200e0622c0e850180080a8401c0c45c280e8501c040058c85e2409848228b44c1207022c642e10848200e45a29130781c00c200b838100622c148983c120701801a240c858261208a2d10858240e0460843214090401c8b83a1607002c38150a040188b8541d0b0481c060068d064301703a170a84c1e07002c6c290c8602e1608c2e11058240e0468d04e190b850200e85c1e0b0380183f180702e100642a0e0401a0a0300348034180b8200c8582a130781a060068d04e170a850200c4541e0b0340c00d1a8a034180a850200c8521e0a8380a00e1e2ec46210e442188b05225100743412070180223a5c8dc681a88431160a44c1d0b0481c060080d9642f120441c8b44c1e090381400d1a2c85c100722d13078240e050030683359039160a44c1e0701801637590c04a120722d13078240e05003474335908c200e8622c148983c120701801e34590b81c8b44c1e0902801437182bc481308c35168983a100682801c37182bc4a1208c39168983a100682801c37188c15e1288431160a44c1c0803414060080421c0b452260f0581a060050d0661007c39168a44c1e06818018)))))
def genIndex9 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (0x4a34d9cd7b8bb4d5e001e001e001e001a3406039e00021c3c5b80e077cc3e001e001ed9e48ebe001cdfb2bb50b0be0005db34740303e3c75e0000c6fe0018c8f6133e001e001e001e001e0000cade001654653d96a2de001e001e001e001e0012e2159bbe001224b6abc1253e001ae721096173be0019d07e001e0013867e0016e541db14173e001e001e001648d6783e001e001aa6ae1cde001cb68c953e001e001e000c1c1e001e00028318785e0010a85d8c1e001e0006e17e001a8ade001e001e000a405e001d283e001e00003cdc7b1a710e7996375e001e001e00068710d042221e00065f2c3ddad44c9dbe0008b2cf29bc12f7bcfe001e001e0016c24c721e0012c6be001ea7e6bf5e001e001091a30e563075e7fe0018933e000c4cf29cbe0002253e001e001e001e001e0006bd76899e001e0014781660b00c9e001e001e001e0018b19e0003763e001e001e001e001e000dd40a86fe001e000029e1983e0009ccc7d23e001b602054c8db3e0014abae54fe000c05836fd0adb4b25e355abc08c05e0008903287dab81e001e001e94b35cde000413dc138b9bc49a04696cacbe000ed5de00003e98b6163a7a30486682b95434799ca78808a9062f5d953e00152f48664aaadb6f7e001aa7a6a61e001aa08e85f05f866cf47bfe001c3b1d527b76618002000539e02002081e0853d0c7411518041041600886383428412001081c280020414301002418a163830c0c7839502000140404000200c506bc1848702000800074784022659408142021c30d06501e085008008002206893a4cd0200440040a1c0892824081001c30d00600030004005080048a120801a12049880c44002020c3180821e810a08a90160c01118049050e180800c149802011a811610604040c0025409380063c0800e0020108006010098084260828e2018f80003cb820e040840a04702060c0840014613020030214149930601a032e00b020404a8004445000e287813c00980240010b0c0028800087890e1c0080c0020c0000002080800500047821a00182142011300443820025081100c106401c19c060c18d060c03700001001608405023c1080404580000c0000620184480c2020a0051500002001610183040020d00082020c181800e081802c200800a04000061c9810604087002c08706340811408402040c00000080822200180084400100040830a0030606040830628082020c203021400028141840460703002010300042801220a02006c0820004400100080108282803638012063420b020c204060c182001c58026281011214300040400d00003001c003040210304083400f02080101404a86003c00a08041800c20081020c38400000051200f803214105023c08c0050100000008000080000a080000c10300060008e0800180081c2020410502) else (0xe73b339cc5d9e00146206adde001867a68b3a91f4b2eab5b4b705af7e000cc63eb08614fe000ee2a84dbe001e0018e37e001e78be000ad13e001e001e001e00003c5e001e0010808021c694558108c4bcdb62b4d69362d8c631675c5e001e001e0006d5fe001e2e968bbe001e0016b47274d4da3d5a6a36eec3be000ebc5e000b97873c3e001e001b9ebe0012dbbe001e001e001440927eda9903789e001e001a30c8865e001c4abe00165d5e000a099e001e001e0016385e001e001e001c58fe00000d3e001e001ca4fe001e001fba3e001e001e001e001e001e001e001e0004cec2b03e000046e2d29e0002999bd52215e2bbc6917a8f80510f730cb67e0016b7fe0014607e0003aa42e2fe001a5798001a40de001a81b680be001e001e0019a1666dfe000ca7cbc326064a45668e2228de001e0016d5a8857fbfde001e000a583e001e001e000211de001e001db13e000711fe0013294e1cfd2f7f1a8db77a505e001e001e001d5e363802cfe1e7b2ac5e001e001e001e001e001e000ca9f2c01c443e001ea5352a6f68a83be978ea75fe001e9a3e001e000c4d0c425e001e001c5cae8b9e0007a2da2d3e001e0007a0fe0006cafe001e000bd9be001e0008895c737e001e000e671e001e001e001e001e001e001e001e001e0012c5cf28be001e000e1e5e000e3d3e001e001e001e00080d52e59e001f3f3e001870fe001933105dac1b03cd1e0002becf5ac1d0e22ba0a43e001e001e001e001e001a6aec21fe001e001e00187f8c30be0017a41e00114e9e001e00181cbe0016585e0012007e00093a9cbacdb75e001e001e001e211e000222849d66371bd7e3a9fe0004147e001e001e001ec1de0001c40e6f203af61948345848181e96bbf6c1628d9e0019dc84c4fe00067de8d48de6223147cea84593783e054a25f3c6f377be001e0012b55a9420ccd63eb4ca76c09e00164b5e88de001e000a1192295e00149e6c649e000a181c22a2bfb49b215c7e0007cdc9ccf8326c6cd0c650cf3e000807ae9ffe001e001e000121a8472081823499777e001c2b3e0003697e001e001c554a2d0a7460bc9a997f7c7470de12288e8e65c2b0d4cbbe001e00023630d43e0000c07e6830a9ad5edc18eb7285aac559d8b6ce4f504382d276e1ceba1fa7902e1e86de001e001e17197b6256321f5e7c3e001c20de001e001e000c0e3e001e001e001e001e000cd09e0013839e00117816e78805b868da93fe001e00180b6054a27c6639d4a286b92819a88af2e31419fda19c1ece29de79a062ca509e001e001059899ae8d202c2ce5522c9149772cbe23e6ae27e001e001e001e000aaa1e001e001e001e0014e1fe001e0018085e001c6e6a702ce33e001e001ac6de0006527fb41e0014b4b2c3c804963f4e58763bde001285c328140ae6e70cd470277e001)) else (if j<3 then (0xc5dec2d9e001460fe001e001e001ed6f641be001e001e00185ef8271e000866049eb84f18cfa965f8b15e001e0016567e001e0000d73e0008239e001e001e001e001e0000b1fe001a293e001e001e0006079e001e00040146e18ec45e00128ef29821a49e00039e9e0000533660c06a016435cc4765469b78d2ea027e001ba29a467e001e0000e4985f6e523e001e001e000c367e00129220365e7933631fca9e000be0c75bde001e001e000c3da7bd06da5e001e001e001a469e000be5384b244de1ae102e7e001e0005aa3e001cd80ae39c127e0018a81ab01e001e0008c9790d9e0008140687b880fa2fde001e001e000be650b9d48ede100ba3c75de1248283b6b77980504922ad3c3d56ca143e4e521fdceadf8ad3f25cec2d7c2fe293833c4fafdc8430a0fe00199d14095e001e001e0004d03e001e001e001c3d083238109e001e001e0002afc582fe001431fe001e0000387e0016963a437e063e000c2244ae56b2728a1e001272ce20808d11db5e000c63de69fe001dccbc0a8b59aab35e0008ddcc02901ffe001435fe001e0f7faa72167edc0ea74e5bf529264cbe0000503e0004633e0019869e00006fde001e001e00020a26d8ff3c7e001e001e001e000f9b34423e001e001e001e001e0012117e001e0012b39e001e00091e840dc031be0008b2a8588c2a86d99ec02216ca92485ed62484e4bc867a397e001692b9c23e001e001e0004b53e001e001e000a3c9603be00065bbe0010deccbe9463be0012332240351d5e00153e3e001413085c6b7dfe001e0002a07e001e001a2f09d69a2a0fd61e001e1e3e00146b0a6c0f1bd27ef682a4b8be00105e133d3237ee4b8a05db977e0004373f6998dcfe0009d5e068f56a7e000299de001eb05e00104fc4506e95e0bdd4e35bda3216fe000ea2be00070e7e001e000c8a348918a19e001e001294fe0012814ec95e001e8b5e001e000799a04ade001e0012227c8cbe000b9f8d524e20fed8be001e001442eaa93e001e001fd62f275b1a7e000e235e001c037e00005e5e001b615e001e00192f3e00101a8dacee251ae62ce75e001e001e00083f660f00a13e001e001e001e0006043e00045e9c204a0e735bfc66d0dfe21fbe00126ede000644c4888b5a3009ac0bcc0766bb1e16964100432c44fa989e000aab3e0008203e001a494329fc1a5b3cbe001e0015da66897ba424d740090abd564d2ee7fe001e001a2ea09f7e00101b7e001e001e001e001e001e000c726b0da0a98f71be001e001e001c9b4c93152dbe000b1c807d44de8589da3a5c319966a90f8c7da02a5e000261de001e001ac22e803e001e001e001e001e50fa517e001823bc90162da59acad9be001e00179b7e001e0010602a5e70dbc4343cb41a43087e34c47e30841f7d5ba889355294e68a2dca38ff52142b66744) else (0xe0015669e001e0014885e001e001e001e001e001e001e000077449fde00013c9e001e000c9e5400de000aca5fa5e720688f7e001a157c400a55ae72eec368cc6dc6de8da59ce2c1aa32bad39d1d2768d3279e000fa59e001055973d5e001e001e00167c1acd66b4942c5d5c1c6f64a77e0012471ac506a97e00067fe28286479b121e001e0007ce1e001a8dfa8128581e00171b1d2df0c5b8497fb5eecd3ba9b85d729ede001e001e000474ea369892fe001e000401fe001e001931de001e000c1c7aa55aaf94453a61b78074d6b3e7de000cae28e12a285a5c1bd6f2604a5c488fde0012b23a05ee7f7e000842de39bad0b12ebaa3ab3a0c98a671dce57c81e4db1c7246263d52e08c3e40be0000c71e000c50062606e25e001e001e000e245e001e001e000cbfe3a83ed50f239e000418264c1e0014d3163ca44c776e14949e001e001a99b2564dc9501dc139ac4b7c8f04df5e001e0008849a4a877746a1dc45e492727d2677743abe000a005e001e001a8dde001e02fe001e000ed0fcb8520cae71e99ff2391e000886009a5e001e23f95114bcbb4d744e78b217a1240ba8e0be000e7543a06797e0a238d2be0012afbd5a9b2fd969180ace0c64c1266b9618be00056a5d55138bc291c6325d2729bf9e000ee6b8e03e0002617e0008ae8ad54cd6de001e000e2a78a3820b860f4c197e001e001c680f5ce7e61e000471be001e000c68993aba4d9eaae402b1607e001e001e001e001e001e0005bd5e0018bf66b134ce680dfe000a8736608e6efe000aa01617ce7b3e0018c35addfe0004df7a48939f3eb51e001f9bfee282187a6b7e001e0019a1bc48fe00051aadb579b7b8797b5e92cebe001e000621be001e001e0016bfde001e00025fb9230662e2177e0014e1b8dc671c4e6310143e001cb1c473149f311fbc4f6cc426461231c31e2853fed4f9aabe57cb657a69a2265a2c0c7f269e2073423948b7808787b6175fae768ea64b9a58de5e0005218f5c3e001e001ac0be9c12732e9efe001240f46392868e213e001e001e000c9aa226e674b0223e001e001e0019c73e001e0015588d28d1aede0010e77e00119ec28f5e00111ec79dfe000fcd214f7e001c023ea880b3fa9d1e850a7c8484a472be0015d8f5523e000698fe000c3c2124791e64ba9a0f8ea324970a3bbe001bc8fe001e00189b165e3e000ce3dc2ef3a890dafe001a88604c58427648b8e7a239f24afa7eb7bc72d768c9dad3a1d29651fe0014be6b8453a93c06d2dd9255e7513e001b5a0ab8fe001e0014c3148aaa017e0016d8687d19e671923e000a3efe0018201a25ca7ae81d7c463e001e001e001e000f809e00042fbe001e000e83d13d7e0015a85e001589343b3e001a4bc67238407e001e0002986678609184e52ca14601bc219e001e001c1064ddbe0006dd58a59))) else (if j<6 then (if j<5 then (0x48ffe001695403a9a7e86d41e000819c84efa33f0ad5ad8825cc6b9be89e423cd2dc8592e7a2ab100a8de00039c64baf4e052cb4fadecd9d07d9e00105b643d9e001e001e000e03526d2290a2af5e001ad0dea21652ee287038ccbc7e001e001e9fbe0004b29e00123cfe0018aaa2336c5a0f71c486bedcde0009bade0007194c49be001e000448406124712296c75f21ca7e000aab4f50e31f95cb4e299a88007e6a231e000ad6520a00ab137bce0abb39482e26393e001451d6a9504b081f2064e6b37325518be6a5d1d56d23de001e00002a3262b4281e0001e05198963528b87e001e000ac89e00148cde001e001e001e001e000499fe0013980b5fc1dc42e5d85a5c45a404dc13fe00009c804291623c3fbe0015399ec8d44165327e6368e61bcc84a30cd25e001fe7981636c92122de000844be00122c71ae22aa9e000e6a7e001e000a6bca839e001e37a46cbe001caea2647cad8a5243a61d2a972a5369a83208773616a71b4f2f84cc264ebe2ec49af214828b1983a630001ea316d26d5c339b174e8c40c41ad7cec2af624dbfa5b78ecee080d3837a9ddbb550862e4ede331e001ec9ef78c9a21c84602d523f9869909f47a8b40ed48c80c81b9abcd5964e139fa31c6d601e00006db038a4c180ae7815be00025724b758675e000e53072769209d6dfe001e0004d17e001c577e0017d888575e001abd029e1e001e001e3ede0006985e001a22c2165b80a59e0693494e7e001e000e6e2925f99dce8d5e001e001e0016e6fe001e0014c53e001065be0000053e001e001e001677b2615e001c1b5e001e00089c5e001cdee0601e001e001033c4b07e00046b38b3baae1e001e00057b1e0010237e001e001e0009a8f6906259e40c138890ce08d4a380231cbe0000449276e806987634073e90caa45e00106788d91e001f9872ca9e000f7a8e97803f0a0710272bbd2a12b987ca50be84015dd282cae512a496959e001e0006111456c6719d229020be001e000ea4be001be54a9acaac30816a6945d9262abf682aafee641ca8ee22eb7f123110e2c9156437798333a65a6bf81d4bd79998a2a9ce3a18dadfdc3e000015c567535f43999e3618b59e0000161e000479c47178cc8a0feb5d6d0cfed8501d1414cec7c3cafa704171fe00000c5e001a1dfe001e00049d5e001e001610be000804625bde001e001fad3e001e000a30fe00143b9e001e0000487e001e000652de0016081e001e0017351e0018715e001e001208a27b68b653c05e00188a844d6962027a52baad25de001e001e00028c11632a8c64b325634046a3574646de001e000c3991140e010d604847c7689e001e001e001e001e000926aca6ec6d9019918fdd5f064a14908885be001e001e0001c3aad3c7599e001e129e0002a73088acc14163eab7de001e001a17f0ab9e001) else (0x2657ab319c51e00045a860e9e9bbee01a58a04408a6ce73e6089e000803fe001e001e001e000c3c1e00075f746f9e000e659e001aaf3e0015c6be0002994d3ac0aefe0000cf0f403e000db10d626b58c164be001e001e001ea04b58be001e001e001e00106fb2dfde001e00061e7e0007667523fe0014acfe0016b8380fde001e0005e064befe00167506c2ebd85e001e001e08c44d4096907cda538ae5a6bcec6ebdad52a4dd0af69e923fde0000a1ae66ef51fe000018d06c9087fe001e0017dabe001e000c5b3e0005d83e001e001a6e1e0011d5de00188fbe001041fe7ce6b8de00047394499e0018b5de2bfe1358e430611e001e00136a3bc71fd3be001cd927213e00013e00a62843f4267e000cda7b1de6a47bd87e001e001e001e001e001e001e00145fd4951e7fac415e000adb9e000a42b277d65ebcd568bd3e0006981c95c37d5e001e001ce40a5c36ad1e001e001e001e001e000922be001e001edb5e001e001e0014626131be000b9b841efe00186c280d9e000076b0102c32fe001e001e825675da2c302ca009cc7fd03b6a24c84353c16251226ddbb63e0012aa63185e001e000ad32a1c8a240dcbe88e7eaf70ba312ede0002c544b3c750c456afadd86736cb7e001e001e00129050a8be0008a5fe001cce9e00136dde001e145810ed985e001e001e001e001ee4e2805cc33e000edcba973e001b3a7e000672889670548faae8701e00181210dabe83f0a0bebb829cd99e7e00042cfe000ed2c062807a17d4aa8e5eb6fe001e001c2bde001e000986cc49f0a2547c5e001e00006c7e001e001812c696eed37e00153aee9600d1e1b71f9c0e13a00750041c84d874241a1a2b9e0010537e000026b4bd90df3e000e7f5c4ffe000c2c823a3436d7d1939eea837017be00084e8d291295608b602e56ad7e000f76d259dc115e00001a32447e001e001e001e0014c8317c0028a2cdbe00197b9e000d397e000290fe000e313e0010418c189e0000bb20c66a3796bf9e0000d196421e000e113e0004d79e001a1e1e001628e4de3e001e001e001e8bea68b17a4233a8c49e000c06fe000ca3f3a47e001630204c8d391e001e001eccadc9089a9e001e0001863e0018153eb73a6d0dd3c01d9e0012c5fa9c3e001e79567489ac3b9a6a1b2cd34cdf12c11e001e001e001e001e001e00013d1cabfe2144cfde001e000e47b42f25d8109d38adf47e19bc4ab4e2bf107b4a535e00183ff6d639215e001b5da45ff02160915e001896be6bba0fbe001e001e001e001e001fd6b47abe001e001b72706f06921e001e001064de001e001e00024822778b801e00154f9e001f653e001e000cb99ece5e001e0008d07e0010ac9a75220bed77fec57c6c47221e001e001e019e000aa716be1e001fc0105b574b7e001e001e001e001a24272a3e001e0eb)) else (if j<7 then (0xe001e001c4cd2051875921b80a5a05295769b3eea1a70a87e001e0011ba8c3ad915389b807dc8da017b3e000ec79e001266b0dd04cde445d4b6301368595ad7e84c3e001e001a63e9685e0005a05e001e0016801e001c47720a537e1452ac07de000762fe001a81de001e00175efe000c4dc882fe001e0000855653dc89be001fa91e770676de000b8ffe0010947e00149d9e001e001e001e00166a3e001e000f548cce3785b237de001609fe001e001e00060e5b5afe257e001e001e000e76107ad4c0dc02006b5e00190f7ed15e00068a5e001e00081bf60e1e001e0004993e000eaedc571a5c98b1a19d9e00188060cb9249dee3f397de001e0007c21e00095ff9a11e00169dee6d7e00072fb4c69e000201da32c47bc8debe001e00068d3e001e001e845e000578a059a4a57e000c0f3c3b51ce3c8e06ab79646b3b293a52e15e00068820a3d4179a9be441dc6aa61bd6557036be001e6452be46e5fe001e000c975b4f1e001ba746191e001e00007f1c9647d908233e001e0006e4d31c3e000a9f925418623cc7f27072b97c00fca1f2caad50be767e001ec73e000025be001e0006551e001e00197145a8ce00be001e0002b4344a5c38236499ab9e00186f5e001e000b74f9233e0017b89e001e000297fe001e001e0011aa9f6298dc5a2b1c3f39b5907e479a9492de0011cc1e001e001e001c04fe001c207cc2125afe001e001e001e001e001e0002a41a06a82dfe000e876f84c72e1e000e2ade001e0000911e001e0016619e11b0d71e001c357e0016a6640b3e001a35ac0028685e001e001a044650de00099a3e001e0016dd3e000de5e604b2820950163e3c3d7e0002756d28fe00105f5e001ad5343881694c0d1e000da1d5724e53be001e001e001e001e001e001e00096e244e3e00099e5e00167cbe000455de000db35e00084bbe0004d23e001e0018591ac0fe001e0010185e001a6fe02f6a569e000678ef5873597e00199010cf4a1f9e001cc2885f0c6e9e000061f11eaabbbe000abcde031e001e0013acc4c38c6242013abb7e001be19e0010269e000e5b1e001565c5609e0002d66057a697be000a9bc095be852e643e001fa67ed61e001e001e001e000ecf7e001e001e0019e57e0018247e0012bdbe0004b5e45d1e0004d01e001e001e001e001e001e001e00066e4d617e000a69361d3e001e001aac741ac229b5d654aa5e001207fe0013e0931d62650e93bea824cb2a6ade001e0009143e001010447b90cddc289e000a175e000e5ade001e7a7227be297e001724bc34f402de001e0002358e4fa434c679f1aa16c8a094140c3e00115ebe0004a27e0018542a4f3f151e000e0b16cd1cd1149cfe001e061e001e001e000469d4c99ce640a79e001e000edbe9431e001e001473c8275a98dbafaccf89393675baccfa1aea67c) else (0x82f8a68675cba8f3e00042cc2cb0e65437459177dabec092643de0004596f9e3e490f1b3e0017d94878de001e001a086cb7b645441fdc2ae2929e00093b1056fe001c8a7e0010ba7e0000e113216ee44e65382b5432968cfe0010e08234b8ac1e001e001e000123bc5610c777a3fe00110947d51a151e00067d7e001e001e001e001e001e0009227e001e000d56c6a50e43be0019542214ae4a7e001c832a3340009c827e000acc5e001e001e00044bfe0000b1741f08125e001ed96cb45e0018067e001e001d7f2e51be001c65f470b28bc2a11e00159d2a8740d69e001199ced1bade12a0de001889d2e46b6932bebed953650466244e4fdd00d7a64a23d26a76409c7e001488fe0016ca24635e001e001e001e2584e3be001e001e0016b915da5297d2445e001e000ee0de001e000a465a519bc2fe001e001435c80cfe00051bfe000aaf12291603de000cbf2c11f41abe001e001e000ec598c7a27886bde80efe001e001e0014b892b0f8aa32a2f0155e0012351c57f894de000e1920834466649f1e000ae7cacd5e001e00180a741bbe001e00063e1e00101da0be3a0b5808f52686c7589a7ce6d4823e0012dd6dcb14c262a699dace47f528480cde0002a37c810a27e132b6c3f01c495d4c7a93da960241765abc3264be001e45119da8e23b721d846a032485951e545a2a279e00046a9a5d38a03e0000791e001267fe0003e0be001e24ee709dc7becbdf742921f9e690e67e001eb9e03df7547cc84ab6b65a7e0009dafe000ac86d97be001c413ccd865aa6c9be001e00152e9e001e001e0017717e001058dcc4c827deda86de658587a982e0fa6a50515b261c15940834cc0e5dc04f9f585f5e4ad4de001e0000c61c5458ba5e096e91393cd2475e000493c55ab0acd00d6e7ba3738d8a5a691b9fdcc1fa2829bc9a0da4d832d1c0dc9e001e001e000dd2e1b19e00068d7e000a0573c2d12ffe001e001e0002677410d2a17e000cb5652a0c26de001adc3e001e0010255677fe001e001684f23c7e0017c4f))))
def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1e9e1d9211100f8d84038301801a34322e281614100a080250d0c8c0a858403828180147a7266645848444240343222201e1c1a08060499e9c9916121110900d0c890888078706850200a67a7266645848444034322622201e1c1a0e060099b14920e8b088502018100966c5e52482c220e08060400594110d0a880785038201808018201c1614120e06004110d080785040383020094685c201c18100e0c06005120885840282018110443834201e1814100a080258807060583828180106c5e52483a2c22080604514110e0d8d0a88078605020098685c28201c180e0600494110e0d8d0a880785020181009a685c28201c0e0806040051a0a08070503818080126e68605c1614120e060051f1e1695941311910f8e0d850403830200a2544a464238100e0c060051c1b9b1595148c0b8b0584028201811e74706a5a565034302a1614100a080279b9a15138b8a058403828180184c4a4826242208060449f1d19969311910d0988078502009c4a464224201c0e060049c15930f8c098502018100966e60544a2e240e080604005918e0806050382018080141614120e060030504038302008c7a785c201c18100c060050584028201810c201e1814100a080240807060583828180107a6c645e52403a322c1a080604694100e0d8c8a870686050200986866645c3432281e1a180e0600694110d8d0a878501810094685c281c0e08040040d0a07050381808010140e0806020030381800705c8033ec1e24e746eb35e1a34cb46373061784b7c58f2b61504a1c4e725812148bc4331f60f047043431880ba455c28712c08a43fc1e30e4067430415f09e04141a409b038013405400f0003ff50ffd07ff40ffccbff31ffcc3ff21ffc83ff10ff983fe51ff943fe42ff907fe40ff8cbfe31ff8c3fe21ff883fe10ff583fd51ff543fd42ff507fd40ff4cbfd31ff4c3fd21ff483fd10ff183fc51ff143fc42ff107fc40ff0cbfc31ff0c3fc21ff083fc10fdc43f510)
def genIndex10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x74af729fdd04261157577800b1fde00314278002168baafc00780064d2816bc007800f001d69e470f800f00006c014e00052c2fe003c007800028782e6cd63841f000a643c0055d40175e0034a6f2cdc26b1b37c007800f001e002553d9a58431e003c00260b94b901408d3f800eaee8a5c021baf49cfd584e8df01c712f7c18bc0058552357c3bbc0056af5400f75f360f800f00109303569849f000d55fc007800f001e00104e7800ac4077cfc00206115198a86d220224d057e000d49f800f00067a3c007800f001a65901e7800f001e000177ba370500937bc00780063a9e003c00397e71dfe00152af8004c29e42b2dd006b0273cb4c07cf800940b079fc0078008dc1220bc007000a1ce40d5d55f80055322457286f91701d92240c7adc62f0008983c00780034b3e003c000ec950e000a7c0040e0f0008b99446ce52a2efe00255ef8009c97e003c0078008ab3e002a1b028b326f8647800fa3ef001e003c07c657f001e0010cbf800f000ca7f8d0f800bd4d62c0438d12e6025c7b270dfa652116e68fc005a8373b7228312fe01720cd0ad9cd7ba11b0a502abb4d69404ba5e00155fd96ff37403dfce22640f00168380ae62909b6dd64f8f1f8000df7e0010fdbafaad8be88fc003de993c9e00237d68367b98cb06027d23a7dc3e002c0b263af001e00045bbae3f0006482f04f800b228234af3611d8a4792897c0028c02227e00314d7800bb3d4ae3c002a47851286d20e6f800fbcb18dfc007800f001e002086c14181c7e003c59f800813bdaccb597adf248be0031047800113d2b4bc00418df0016a57c0031f8637be001c0df800f0008777c007800f000a43c411f80023ae2abb8d8b86064d1e00185450abbd73ca99f5df800b3eed9afc007800f0018a1688ef800b9f282f3c007800f001e9c3c007800346858dbc003157f00025338ee7800f001e003c003ec8f001e0008677e2252d3693d80cf800452cc778b0eda31f001e001058c9f3f001e0022de19cf64e7e003c000100f001e003c0048c6f000697bc0019ebf07be00087c7800b577e000445381db11039bbc005ad544f79ae84dca16ef001244bc00728ef001e003cc5f800b39103350e5616b72ade003751f8001e1800f2444aae0c4c58a0a08a8c060c4870818208043008400001840080180041880a061c1010004409020401e0c0408a161c0821a1090000000040000237080000d1004aaa44200810844182020c6120200002020cb84061070116006050044086021c707004c08a0200180121400a047028100083001000182080c600061400102158801a00003281c0801200381221138000001800810a010a008841e28100200c30924000838a04400042c00b0c041030a2c000160018e04002020a0c703020498000300030214281022409b0004b11186c4000604882) else (if j<2 then (0x2d1bce0877c000a51f000ab3041d4de213b4e46d1078893a1b8a788248b18fa14d026655cb1c1b5d3e0011720077f001d18440c780084f4608910df800f001e0024e1f17550bf5857cd4cde3f00149c8f5552a934b7c4cfc004a2bf001e002529e8a7b585a524119f80003aaa92803278005cd3e0030b330bbf001e002920de1ce035e0030eb2a1ffca7e002004780041846683421780054d9065702c31103145eb8a95975e8dbb5e003417dee7523f6b47c007800f000a257895a9f4f00142925012178e45184302c5f8006a197adbc0048d3d0222903d73f800f001a42faddf800f00021f60c27800f001e0000a5b5e4c2c1e000d4df800f000d0f4b60780092e0e85853759aa0d8fe0036e55926309a46b7c000c43d0fea1c9c3c6924f001e003c00280c3d4be7a8574384cf000c04eca971fea123e0018a34187c00fc6efc007800336de003c005a91f001d8e3c0069ce5409e000ad9f80092508619b6ea83283356bf2f63759f12bdea778eff134f001e003c0030e5b211869a53ecdb8716be0028f6b14a527c28664f075c0f0012733c0018ca82bfe4f7c0019f9f001e0018e2f800b007e003c007800f001e003c006968f0003af750948edf001e001f280889f001e7bbc0032f3cd01e0034ccc20cf000aa53863f800f00063dbc007800f001e002c8f7800913e435d4bfd8d905b5e00197f3592631564265453848f00008e3c007800d331d9b477ea9b5c5fb272d147b189eb62d95453b4a92f000b0d60e9f800f001e003d527800f001e003c007127f00158788d2784ef000a51fc007800259c9a87c007800e37ec3680f4ba6a81e5dbe6c928deaf001e001f7af800f001e0030c0b982f000021fc0078000233e003c007800f001c463c007800f00143a1479e453bb91e1b3ca741d1f001e003c0010aff001e0004de78007d7f6444b044806553024c0a6fe4f8f000f770804892fb0ce856ad107800a3e5880644768fc63803b10874d2aae5e48378c94c8fb8118e87071e69f684a0682fc007800a58fe003c007800d311cbafd30f800f192c797c007800612da7f3c007800f001e0008685e0e820c9242d0d7800f0016b4096cb2db6b93e00100548eaf001e001b1f0945f001e99a8be42f7f000818fc000252f001e003d67f5ebc43ce8c3c004445f001e002772f8000d44248fc0036fef001e003c0078002be87ae3c007800f001e001506f800f001c39bc007800e5913ac7c002894bbade001c107800f0016abdb0cc23ff001e00227dd107c587c013c007800f001e002c2e72eaad59e001c22100df001e003c007800f001e00285c7800f0003a3fc00602acc5fe003c007800fd1009d711af8007209e003531780024dae1f3ee9f800f001e003c007800a08dc9c5898fa7ef00068a7c0005c2f27057fcc966976f001e003c007800f000e3) else (0x7c1469aecb19a1534b5e002ed978008d48ebc546c7a46a0f72312c95518cc2ceab2bc005026f29f42180808a58f0008b79543f80b956291e05411a64b3ff6acfc00798e48cccb63c001286e12fe15f0ac816cc0df20d083ca0fa29b8835944781b2ac77b37745f91d0148401d3c006c5cf001e003c0060387051e00074348d530d5e003c0070dfb38de003f1ef800c415f5a98b6b922f4f19b6a8d449586327e000d70f800f000a1a357af102f001e00288d78005337e000081bdb0bcce69dc2fb099202a1e0028997800733de000b3fddb5f001e003c00399c014be003c96f80002423b99137ee510197b24a4877e18f00188bbc0012ecf001e003c002a3db021e000cf7f263f001e0008bcf800f001e0028427800f00026dfc00286d305de003c007800d421890d13a509a4029e003c007800f0014ad5565fadcf000c708f53f8004bb00b7555f7ea9f00107c09164194022d2a2141c80ae6279e003c7fd26781d7d25403b780062c2187f4b578003d51e00142ca6be14f9e003c005980f000054c11c8dc5a1594b170a47800033a660e4ba6a279575e003c0026e8c0496a79412f800f001e76411dc2e00b0cf0f89018854e3ebe0b6140f02c61a9e002f0b7800135c220fc001687f001e003c00717ded169a4b4a20a56f001e002306f800b1c5428600740be1275a7ea16378bdc07e820089d8037042e0a810253833f001e003c007800f00196fcf097800f0014af377bc2eef001e00276ff5b43b0f76df434ce56f001a2c8358785bc46cbb09976e558f00132640490827c40d42a780f625775ae5ad4864780041a3e003c000a4e9af1c81e76189550371e000f71f800f00067c61561151f1e9c5e857c1972f1c917d689f901fe285e003546f03009eca3c522eb56b330b5a81d2a195463c2428cd786dc6145fe8248b8aa2600816b5148e10566427c6cd6e8780000dce3f7c00760ce183d559124f800208f80efc00780005ca833c8adb04b35ade003c007800f005e001878385115503631482a2adf00148528aef800349be003c00780062e7e003c007800f001e00315849c91547e003c00525d307d61ea30061d2b5f3cb26960705d63454a9572a7800b0cbe003c00161af0ebe003c0079e6f001e003d240162a33fe000228ee3ff001021744c409ba4ff77decb2c081f000e8a840e38ccc187cadfc007800f00102d827bf800402be0002ad6e94f001e003c007800f0006bec6f34db92df82a8bc007800f000c4d983f7800e4650593c007800dc73e00286dfac4f00069e683998ad4dd22bdbc0012220c4200c5334780014973adcc2f12b4918be003ae0866acbda88846e8857af000614fc001a)))
def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x348f01e014415ad41e01cef80f01995b4622f01e03c0780523e03c0447f00a26c2a0ea83e01b278098de03c042b653e03c02e2f018b7cc780f0fe0081780f01e0101f80f01e0375f0b14ea4fc05a69bfe03c0780f01e03c07805a1e036e780237e0329780f01e00b764e602547c03db19fe02350a4f01f8f4b0cb85169586192a9347aa1fe91c1b16e2715f00e6b2af8051e577c005e5da85fc0780b800b286f6c52094fc0780b0d75fc0780f0190b95780f01e03cca67ccc67d4a4a1147e28821d47388bbc036180110099c001546082155002340003040)
def generatedLevels : Nat → Packing
  | 4 => (7,7,7,0,0,6,0,genData4)
  | 5 => (227,6,7,0,0,11,0,genData5)
  | 6 => (1061,5,7,0,0,15,0,genData6)
  | 7 => (1890,4,7,0,0,17,0,genData7)
  | 8 => (1856,3,7,0,0,18,0,genData8)
  | 9 => (767,2,7,0,0,17,0,genData9)
  | 10 => (47,1,7,0,0,13,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 12 0 8 3 1 genIndex5
  | 6 => lookupWord 72 429 7 13 8 1 genIndex6
  | 7 => lookupWord 354 2125 7 16 11 1 genIndex7
  | 8 => lookupWord 632 3793 6 16 11 1 genIndex8
  | 9 => lookupWord 615 3685 7 16 11 1 genIndex9
  | 10 => lookupWord 248 1492 7 15 10 1 genIndex10
  | 11 => lookupWord 22 145 6 11 6 1 genIndex11
  | _ => fun _ => none
def qF_ : Forest := ⟨507,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [112,97,83]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP4_0 : block qF_ 4 0 7 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB4 : block qF_ 4 0 7 = true := genP4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block qF_ 5 0 7 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_7 : block qF_ 5 7 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_103 : block qF_ 5 103 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_199 : block qF_ 5 199 28 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block qF_ 5 0 227 = true := (@block_merge qF_ 5 0 103 124 (@block_merge qF_ 5 0 7 96 genP5_0 genP5_7) (@block_merge qF_ 5 103 96 28 genP5_103 genP5_199))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block qF_ 6 0 96 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_96 : block qF_ 6 96 37 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_133 : block qF_ 6 133 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_229 : block qF_ 6 229 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_325 : block qF_ 6 325 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_421 : block qF_ 6 421 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_517 : block qF_ 6 517 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_613 : block qF_ 6 613 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_709 : block qF_ 6 709 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_805 : block qF_ 6 805 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_901 : block qF_ 6 901 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_997 : block qF_ 6 997 64 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block qF_ 6 0 1061 = true := (@block_merge qF_ 6 0 517 544 (@block_merge qF_ 6 0 229 288 (@block_merge qF_ 6 0 96 133 genP6_0 (@block_merge qF_ 6 96 37 96 genP6_96 genP6_133)) (@block_merge qF_ 6 229 96 192 genP6_229 (@block_merge qF_ 6 325 96 96 genP6_325 genP6_421))) (@block_merge qF_ 6 517 288 256 (@block_merge qF_ 6 517 96 192 genP6_517 (@block_merge qF_ 6 613 96 96 genP6_613 genP6_709)) (@block_merge qF_ 6 805 96 160 genP6_805 (@block_merge qF_ 6 901 96 64 genP6_901 genP6_997))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block qF_ 7 0 54 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_54 : block qF_ 7 54 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_150 : block qF_ 7 150 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_246 : block qF_ 7 246 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_342 : block qF_ 7 342 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_438 : block qF_ 7 438 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_534 : block qF_ 7 534 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_630 : block qF_ 7 630 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_726 : block qF_ 7 726 88 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_814 : block qF_ 7 814 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_910 : block qF_ 7 910 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1006 : block qF_ 7 1006 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1102 : block qF_ 7 1102 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1198 : block qF_ 7 1198 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1294 : block qF_ 7 1294 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1390 : block qF_ 7 1390 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1486 : block qF_ 7 1486 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1582 : block qF_ 7 1582 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1678 : block qF_ 7 1678 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1774 : block qF_ 7 1774 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1870 : block qF_ 7 1870 20 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block qF_ 7 0 1890 = true := (@block_merge qF_ 7 0 910 980 (@block_merge qF_ 7 0 438 472 (@block_merge qF_ 7 0 150 288 (@block_merge qF_ 7 0 54 96 genP7_0 genP7_54) (@block_merge qF_ 7 150 96 192 genP7_150 (@block_merge qF_ 7 246 96 96 genP7_246 genP7_342))) (@block_merge qF_ 7 438 192 280 (@block_merge qF_ 7 438 96 96 genP7_438 genP7_534) (@block_merge qF_ 7 630 96 184 genP7_630 (@block_merge qF_ 7 726 88 96 genP7_726 genP7_814)))) (@block_merge qF_ 7 910 480 500 (@block_merge qF_ 7 910 192 288 (@block_merge qF_ 7 910 96 96 genP7_910 genP7_1006) (@block_merge qF_ 7 1102 96 192 genP7_1102 (@block_merge qF_ 7 1198 96 96 genP7_1198 genP7_1294))) (@block_merge qF_ 7 1390 288 212 (@block_merge qF_ 7 1390 96 192 genP7_1390 (@block_merge qF_ 7 1486 96 96 genP7_1486 genP7_1582)) (@block_merge qF_ 7 1678 96 116 genP7_1678 (@block_merge qF_ 7 1774 96 20 genP7_1774 genP7_1870)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block qF_ 8 0 7 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_7 : block qF_ 8 7 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_103 : block qF_ 8 103 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_199 : block qF_ 8 199 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_295 : block qF_ 8 295 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_391 : block qF_ 8 391 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_487 : block qF_ 8 487 38 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_525 : block qF_ 8 525 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_621 : block qF_ 8 621 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_717 : block qF_ 8 717 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_813 : block qF_ 8 813 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_909 : block qF_ 8 909 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1005 : block qF_ 8 1005 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1101 : block qF_ 8 1101 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1197 : block qF_ 8 1197 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1293 : block qF_ 8 1293 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1389 : block qF_ 8 1389 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1485 : block qF_ 8 1485 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1581 : block qF_ 8 1581 4 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1585 : block qF_ 8 1585 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1681 : block qF_ 8 1681 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1777 : block qF_ 8 1777 79 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block qF_ 8 0 1856 = true := (@block_merge qF_ 8 0 909 947 (@block_merge qF_ 8 0 391 518 (@block_merge qF_ 8 0 103 288 (@block_merge qF_ 8 0 7 96 genP8_0 genP8_7) (@block_merge qF_ 8 103 96 192 genP8_103 (@block_merge qF_ 8 199 96 96 genP8_199 genP8_295))) (@block_merge qF_ 8 391 230 288 (@block_merge qF_ 8 391 96 134 genP8_391 (@block_merge qF_ 8 487 38 96 genP8_487 genP8_525)) (@block_merge qF_ 8 621 96 192 genP8_621 (@block_merge qF_ 8 717 96 96 genP8_717 genP8_813)))) (@block_merge qF_ 8 909 480 467 (@block_merge qF_ 8 909 192 288 (@block_merge qF_ 8 909 96 96 genP8_909 genP8_1005) (@block_merge qF_ 8 1101 96 192 genP8_1101 (@block_merge qF_ 8 1197 96 96 genP8_1197 genP8_1293))) (@block_merge qF_ 8 1389 196 271 (@block_merge qF_ 8 1389 96 100 genP8_1389 (@block_merge qF_ 8 1485 96 4 genP8_1485 genP8_1581)) (@block_merge qF_ 8 1585 96 175 genP8_1585 (@block_merge qF_ 8 1681 96 79 genP8_1681 genP8_1777)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block qF_ 9 0 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_96 : block qF_ 9 96 32 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_128 : block qF_ 9 128 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_224 : block qF_ 9 224 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_320 : block qF_ 9 320 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_416 : block qF_ 9 416 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_512 : block qF_ 9 512 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_608 : block qF_ 9 608 25 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_633 : block qF_ 9 633 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_729 : block qF_ 9 729 38 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block qF_ 9 0 767 = true := (@block_merge qF_ 9 0 416 351 (@block_merge qF_ 9 0 128 288 (@block_merge qF_ 9 0 96 32 genP9_0 genP9_96) (@block_merge qF_ 9 128 96 192 genP9_128 (@block_merge qF_ 9 224 96 96 genP9_224 genP9_320))) (@block_merge qF_ 9 416 192 159 (@block_merge qF_ 9 416 96 96 genP9_416 genP9_512) (@block_merge qF_ 9 608 25 134 genP9_608 (@block_merge qF_ 9 633 96 38 genP9_633 genP9_729))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block qF_ 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block qF_ 10 2 45 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block qF_ 10 0 47 = true := (@block_merge qF_ 10 0 2 45 genP10_0 genP10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_0 : block qF_ 11 0 1 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB11 : block qF_ 11 0 1 = true := genP11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genTables : checkedTables qF_ 11 := by
  intro k hk
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact genB4
  · exact genB5
  · exact genB6
  · exact genB7
  · exact genB8
  · exact genB9
  · exact genB10
  · exact genB11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genGeometry : graphValid qF_ (boundsBefore generatedKnown) = true := by
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowGenerated : Lower true (varsX 507) (qG_ 507) 12 :=
  lower_forest (g := qF_) (i := 0) (hints := 67)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_51402.ForestCore
namespace PEqualNP.Outside.L_meta_51402
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffeffffffffffffffeefffffffefffffffefffeffeefefeaa00fffffffffffffffeffffffffffffffeefffffffefffffffefffeffeefefeaa00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 2 zero,16,20)]) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 2 zero,16,20)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [count] at h
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
def upperGates : List Gate := [⟨.or, [6,4]⟩, ⟨.or, [7,6]⟩, ⟨.or, [1,0]⟩, ⟨.or, [10,2]⟩, ⟨.or, [10,3]⟩, ⟨.or, [12,4]⟩, ⟨.or, [12,7]⟩, ⟨.and, [11,8]⟩, ⟨.and, [5,14]⟩, ⟨.and, [0,3]⟩, ⟨.and, [13,9]⟩, ⟨.or, [15,16]⟩, ⟨.or, [19,17]⟩, ⟨.or, [20,18]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_51402
open PEqualNP.Outside.L_meta_51402 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_51402 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hg, eq⟩ := neg
    have fan : FanInTwo ⟨gs, o⟩ := fun t ht => ⟨(legal t ht).1,(legal t ht).2⟩
    have low := binaryLower ⟨gs, o⟩ fan computes
    change 13 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [eq, signedNot]⟩
    refine ⟨upperGates,21, upper_shape, ?_, upper_sem⟩
    change 14 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g, hg, eq⟩)), cap⟩
