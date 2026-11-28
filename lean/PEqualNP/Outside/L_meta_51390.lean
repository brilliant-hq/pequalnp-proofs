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
namespace PEqualNP.Outside.L_meta_51390
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
end PEqualNP.Outside.L_meta_51390
namespace PEqualNP.Outside.L_meta_51390.ForestCore
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
theorem prior504 : Lower true (varsX 504) (qG_ 504) 7 := by
  have h := lift_ok (u := true) (ms := ([16,65,98,67,100,101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 504) (T := qG_ 504) (xs := [])
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
theorem prior499 : Lower true (varsX 499) (qG_ 499) 7 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 162 0)
    (raw := varsX 499) (T := qG_ 499) (xs := [(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18),(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior498 : Lower true (varsX 498) (qG_ 498) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 160 0)
    (raw := varsX 498) (T := qG_ 498) (xs := [(inputs.getD 5 zero,2,34),(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,2,34),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (qG_ 497) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 160 0)
    (raw := varsX 497) (T := qG_ 497) (xs := [(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior496 : Lower true (varsX 496) (qG_ 496) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 496) (T := qG_ 496) (xs := [(inputs.getD 5 zero,128,160)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,128,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior472 : Lower true (varsX 472) (qG_ 472) 5 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 472) (T := qG_ 472) (xs := [(inputs.getD 4 zero,64,80)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior464 : Lower true (varsX 464) (qG_ 464) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,83,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 464) (T := qG_ 464) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
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
theorem prior458 : Lower true (varsX 458) (qG_ 458) 5 := by
  have h := lift_ok (u := true) (ms := ([84,117,118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 458) (T := qG_ 458) (xs := [(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior456 : Lower true (varsX 456) (qG_ 456) 4 := by
  have h := lift_ok (u := true) (ms := ([33,50,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 456) (T := qG_ 456) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior451 : Lower true (varsX 451) (qG_ 451) 5 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 451) (T := qG_ 451) (xs := [(inputs.getD 1 zero,64,66)])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,64,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior450 : Lower true (varsX 450) (qG_ 450) 4 := by
  have h := lift_ok (u := true) (ms := ([84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 450) (T := qG_ 450) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior449 : Lower true (varsX 449) (qG_ 449) 4 := by
  have h := lift_ok (u := true) (ms := ([16,84,117,118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 449) (T := qG_ 449) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior283 : Lower true (varsX 283) (qG_ 283) 4 := by
  have h := lift_ok (u := true) (ms := ([33,84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 283) (T := qG_ 283) (xs := [])
    (by decide +kernel) (qP_ _ (by decide +kernel)) (qP_ _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h
def generatedKnown : List (Nat × Nat) := [(506,8),(505,8),(504,7),(475,8),(443,8),(442,7),(411,7),(379,8),(377,7),(347,7),(499,7),(498,6),(497,6),(496,5),(491,7),(490,6),(489,6),(488,5),(483,6),(482,5),(481,5),(474,6),(473,6),(472,5),(467,6),(466,5),(465,5),(464,4),(459,6),(458,5),(457,5),(456,4),(451,5),(450,4),(449,4),(441,6),(440,5),(435,6),(434,5),(433,5),(427,6),(426,5),(425,5),(424,4),(419,5),(418,4),(417,4),(410,5),(409,5),(403,5),(402,4),(401,4),(395,5),(393,4),(378,6),(371,6),(370,5),(369,5),(363,6),(361,5),(346,5),(345,5),(339,5),(338,4),(337,4),(331,5),(329,4),(315,6),(313,5),(299,5),(297,4),(376,4),(314,4),(283,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by
  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior506
  · exact prior505
  · exact prior504
  · exact prior475
  · exact prior443
  · exact prior442
  · exact prior411
  · exact prior379
  · exact prior377
  · exact prior347
  · exact prior499
  · exact prior498
  · exact prior497
  · exact prior496
  · exact prior491
  · exact prior490
  · exact prior489
  · exact prior488
  · exact prior483
  · exact prior482
  · exact prior481
  · exact prior474
  · exact prior473
  · exact prior472
  · exact prior467
  · exact prior466
  · exact prior465
  · exact prior464
  · exact prior459
  · exact prior458
  · exact prior457
  · exact prior456
  · exact prior451
  · exact prior450
  · exact prior449
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
  · exact prior376
  · exact prior314
  · exact prior283
def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (0xf8000781cde2580200c0387e0013081311333f), BitVec.ofNat 152 (0xf8924028200000060140489200110011011115)),(BitVec.ofNat 152 (0x38061204a00c0703c780009c109c29cdcc), BitVec.ofNat 152 (0x1b640e86480001e0b44c9960094009409454c)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0),(BitVec.ofNat 152 (0xf801c01820690830383c000e04e024e0ce0e0f), BitVec.ofNat 152 (0x36409c2dc8000785a0c832c04a004a04a0e0a)),(BitVec.ofNat 152 (0xe0060039030c1c00007f02700c700f00ff0), BitVec.ofNat 152 (0x6409b17982001e0d019166825004500f00aa0)),(BitVec.ofNat 152 (0x7000003c01c300003ff8013800f800fff000), BitVec.ofNat 152 (0x409b61503600781a4b334412800f800b4a000)),(BitVec.ofNat 152 (0x780007fc01e0401ffc00001c000ffff000000), BitVec.ofNat 152 (0x924000340060124a220014000ba4a000000)),(BitVec.ofNat 152 (0x7ffff80000007fe00000001ffff0000000000), BitVec.ofNat 152 (0x1ff80000000000924a0000000000)),(BitVec.ofNat 152 0, BitVec.ofNat 152 0)]
def generatedColumns : List ColumnInfo := [(1,0,506,0,8),(2,0,505,0,8),(3,0,504,0,7),(32,0,475,0,8),(64,0,443,0,8),(65,0,442,0,7),(96,0,411,0,7),(128,0,379,0,8),(130,0,377,0,7),(160,0,347,0,7),(8,0,499,0,7),(9,0,498,0,6),(10,0,497,0,6),(11,0,496,0,5),(16,0,491,0,7),(17,0,490,0,6),(18,0,489,0,6),(19,0,488,0,5),(24,0,483,0,6),(25,0,482,0,5),(26,0,481,0,5),(33,0,474,0,6),(34,0,473,0,6),(35,0,472,0,5),(40,0,467,0,6),(41,0,466,0,5),(42,0,465,0,5),(43,0,464,0,4),(48,0,459,0,6),(49,0,458,0,5),(50,0,457,0,5),(51,0,456,0,4),(56,0,451,0,5),(57,0,450,0,4),(58,0,449,0,4),(66,0,441,0,6),(67,0,440,0,5),(72,0,435,0,6),(73,0,434,0,5),(74,0,433,0,5),(80,0,427,0,6),(81,0,426,0,5),(82,0,425,0,5),(83,0,424,0,4),(88,0,419,0,5),(89,0,418,0,4),(90,0,417,0,4),(97,0,410,0,5),(98,0,409,0,5),(104,0,403,0,5),(105,0,402,0,4),(106,0,401,0,4),(112,0,395,0,5),(114,0,393,0,4),(129,0,378,0,6),(136,0,371,0,6),(137,0,370,0,5),(138,0,369,0,5),(144,0,363,0,6),(146,0,361,0,5),(161,0,346,0,5),(162,0,345,0,5),(168,0,339,0,5),(169,0,338,0,4),(170,0,337,0,4),(176,0,331,0,5),(178,0,329,0,4),(192,0,315,0,6),(194,0,313,0,5),(208,0,299,0,5),(210,0,297,0,4),(131,0,376,0,4),(193,0,314,0,4),(224,0,283,0,4)]
def genData4 (j : Nat) : Nat := if 1 ≤ j then 0 else (0xa621c22999561d0655110)
def genData5 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x60408000000110204000000000000000000000000000000000000000000000000000000000000000099cb64f218dc5604fc7b3c1d4e46f361a4cc6330174b4572a1449c4b24114843f1e0e46c33180b45427120843c1b0c054240f060240c03003e10baa4eb02a8b1221e885a1274195454910f442c4c3a0caa2a4887a115858d4059543443d08aa2c6c02caa1a21e0c61d685417655110f0630cbab00bb2a8887831685d5405d954443c18b42e8a82ecaa221e0c5a1515017655110f062d0a0aa0bb2a88876115458d9059543443928ac2c6c82caa1a21b88695275815458910dc42cbd12ecaa404886e11a65513059543443708d2ac6a02caa1a21b485d7a25d95480910d4a34cac260b2a86886a51a558d8059543443518b2f50bb2a901221a4c5d7a85d95480910cc674ccab0e832a8886630a959587419544433185332ac3a0caa221784ecda75950655110b8c764bb2aeb2c04885a33b661d0655152442c39dc2ecabacb012215c8ec9985417655110ae2766d3b2a832a8885333b961d5055162442791d934abb2a9012213c86d7a25d954809109e4365d3aacaa404884f21b22998754154442750d914cc3a0caa2213a46cca661d0655110966770d2aecaa404884b33b06a17655152442598dc74eab2a9012212cc6d7a85d95480910966361d42acaa2e4884b31b0e9d86551524423c9da345c9aec81a211e4ecda5e5176411108e676bd0330bb2a8884733b468b955d905442398dcd4cc3aa0aa2211cc2e99561d0655110)
def genIndex5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff7b9e
def genData6 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then (0x109f8e8997596024427e3a265d63809109f8697925da024427e1a3e4976809109f868b97596024427e1a2e5d63809109f4e8d97596024427d3a365d65411109f4e8d90595434427d1a3e510654d109f468b935d9034427d1a0e4d6550d109ece9197595044427b3a366106551109ece81985d9544427b1a960276551109ec6a540595434427b1a8e4d06551109ec697945d9044427b1a4e5d65411109ec69393595044427b1a4e4565411109ec68f98419544427b1a3e5106551109ec6829661d544427b0a961d06551109e9e89985d9544427a5a225987551109dc6979441953442771a4e5576415109dc68b955d905442771a0e5d56551109cd697985d954442735a5e4976551108fcea580551634423f3a95d985809108fcea57660e024423f3a865d65809108fcea19758e024423f3a86416550d108fce9998415434423f3a56610650d108fce9593e11064423f3a46610654d108fce8d98419544423f3a066176551108fce81985d9524423f3a0661764c9108fcaa7805d9524423f2a9e01764c9108fc6a580595434423f1a8e5d65809108fc6a397595044423f1a8e5d63809108fc6a394419534423f1a8e4d65411108fc697985da024423f1a5e518058d108fc69395601634423f1a4e4d80595108fc68f985da024423f1a3e5180595108fc68398595744423f1a0e61655c9108fc6839858d724423f1a0e5d86551108fc68397619524423f1a0e5d864c9108fc68393619544423e7a266176551108f5e8d985d9544423d7a366176549108f5e8d985d7644423d7a366175d89108f5e8d97e09654423d7a3657845d9108edea587551624423b7a466176549108ede91985d9324423b7a464b855d9108ede9192e0d764423b5a5e5187589108dde95985d9324421f7a76616550d1087be89985d9544421efa265f835954087be8997e05655021dfa36617654910877e8d95e11764421dfa3647825d95086fe91985d9524421bfa4661764c91086fe9192e15764421bfa464b835d91086f6979461d6244217fa5661764c910f885890655152443e2156c815458910ec8e012655152443b23206195454910eb058d0660a43443a916341984cc910e985978049952443a51656013654d10e8c5a10655152443a31656195480910e8c5616055362443a3156e015458910e8c5598055362443661955890654910d9859790499524436519558d0654d10d94595934195344363165e4d0655110bc8e812655152442f21a6c815454910bc86972055162442e61a6c815654910b986972059562442e31a5da10655110b8c6956055362442e31a55815458910af068d0660a43442b91a341984cc910acce818655152442b31a6e015454910acc6978055162442b31a56195480910acc6958055362442731a954276551109cc6979841954442731a5e4d0655110) else (if j<2 then (0x5110dcce61505d954443733975015655110dcce515741954443733945450655110dcce51505d954443731a76550655110dcc68995419544437319855d0655110dcc661509d954443731985417655110dcc65d50919544437319564d0655110dcc6558741954443731956027655110dcc65567419544437319551d0655110dcc6554141954443731955017655110dcc6515741954443731945450655110dcc651505d954443731945416550d10dcc6515045954443731576424655110dcc551905954344373150e497655110db865927415624436e1964850558910db4e4d60595434436d1636416550d10dac651605954344369b935816550d40d9c559905516344366b925950648550d9a6556241952443665656497654910d9959592459524435699549d0654910d5a649505d9524435357955e4655110d4d5d7925d9544434e99649d0558910d1b595925d9524433e3a26610655110cf8e63205d9524433e398c81764c910cf4e61305d9324433d393e01764c910cf466136415434433d1984c16550d10cece9198419434433b3985017655110cece51805d9544433b2896017655110cec66146415434433b1985016550d10cec65186415434433b1946016550d10cec625809d9544433b140e4d8655110cdce959841953443373985417655110cdce61505d952443371985416550d10cdc561905954344337150e4d8655110cdc54194e0d654432f1985816550d10cbc58194e0d654432b9945838359540c9e59591e09065431eb92e418758d20be8e899841954442fa3a25d95480910be468d0651543442f53a361d5059510bcce9d5655202442f33a661d5055110bcce959341954442f32a661d5055110bcc6995741954442f31a55d95480910bcc6954059543442f31a5419545c910bcc2998754154442f25a25d95454910bb8e896759602442ed3a361d6059510bb46993059543442ec9a648d0648530bace998741954442eb3a35a10655110bac2998741954442e73a564d6059510b9ce896754165442e71a55815458d10b8d697685d954442de3a25d97580910b5ce957641572442d35a55d9545c910b1ee896754165442c77a25d95759510b1de896754565442be3a26518059510af8aa72061932442bd3a365d8059510af4e8d8758165442bd3a361d0358910af4e8d7660e02442bd1a34198550d10aecea17655202442bb3a461d0558910aece918740d62442bb3a46015458d10aec6a10651543442bb1a44198550d10adce959360165442b73a561d0559110adce958741562442b73a56015458d10adc6958059543442b37a8559545c910acde9d8655152442b37a661d5454910acd6a17655152442b35a561d54d8910abcea16759602442af3a661d0655110abce998741952442af3a661d064c910abce8d68419544429f3a85d975809) else (0x454910ecce017655152443b31a85595480910ecc61d5055362443b31875415458910ecc61d0655152443b31585d95480910ecc5614641543443b31585016550d10ecc55f8055162443b31576195480910ecc55d8055362443b31575018655110ecc5518641543443b31546016550d10ecc51d5061954443b25874995454910ec949d8655152443ae16849d0654910eb85a12741932443ae1684850654910eb85a12141932443ae16261d0654910eb85898741932443ae1626050654910eb85898141932443ad163e01764c910eb458d8741932443ad163605064c910eb458d8059543443ad1634198550d10eb44e16758e02443ad13858173d8910eac6198741954443ab1866017655110eac5a14741954443ab1685050655110eac5a1405d954443ab1685011655110eac5a10651543443ab16461d0655110eac5918141954443ab1646017655110eac5918045954443ab1644198550d10e9ce958059563443a716855d6580910e9c5a15741954443a71685450655110e9c5a1505d954443a71685411655110e9c59d50e1165443a7165e017654910e9c5958741954443a716561d0654910e9c5958141954443a71656050654910e9c595805d954443a715859d6580910e9c5616741764443a715858175d9110e9c561605d762443a71585816550d10e9c55d60e1165443a7156e017558910e9c5598741762443a715661d0558910e9c5598141562443a715660175d8910e9c5598055163443a656561d2654910e995958149952443a555858d6550d10e8d5598755362443a355661d5458910e5a49d5061952443935785d95454910e4d5d587553624439357561d5458910e3a5a127419524438e96849d064c910e3a58987419524438e96261d064c910e3658d87419324438d57858d764c910e3558d87459324438d563605764c910e2e5a147419544438b9685017655110e2e59187419544438b5875a17655110e2d5e1645d9544438b5685d17655110e2d5a147459544438b5685057655110e2d59187459544438796855d0655110e1e5a1505d9544438796561d0655110e1e59587419524438795661d0558910e1d5e1655d954443875785957654910e1d5e1565d762443875785597558910e1d5d957e1165443875685d57655110e1d5a157459544438756561d1654910e1d595815d952443875585d975d9110e1d5598745562443875566057558910e1b59587499524437c3a264d064c910df0e4f205d9324437c19349d064c910df064d21419324437c1924c1764c910df064930459324437a3a26610655110de4e919341943443793935016550d10de46513641543443791944c16550d10dd86552741952443761954850654910dd8649505d952443761925411654910dd4e959341953443753935416550d10dd465593419534437339855d065))) else (if j<4 then (0xfc37b1bc0dd46e434b1980c546002f11710b0454c285138098449824310b07ec3c01bf0d806542e815909c04442100f306602dc14408703c017409c03f0120054000fc8c817655152443f21a25595480910fc855f2055162443f21275415458910fc849d0655152443f11544d90550d10fc45513059543443ec163c81764c910fb058d2741932443ec163485064c910fa849d6055162443e91635016550d10fa458d0651543443e61a05952654910f98597205d952443e616549d0654910f985952141952443e6156c817558910f985592741562443e61564850558910f946556341953443e516564d0654d10f945953641153443e51635416550d10f945593055163443e336855d0655110f8cda1505d954443e336455d0655110f8cd91505d954443e31a75950655110f8c6815655162443e31686550655110f8c5a15741954443e31685417655110f8c5959341954443e316561d0655110f8c5957655202443e316559d0655110f8c5954741954443e31655050655110f8c595405d954443e3165419545c910f8c5915741954443e31645450655110f8c591505d954443e31645411655110f8c55d6055362443e31575815458910f8c5594055163443e31545816550d10f895592755162443e155458d6550d10f705c9305d932443dc1214c1764c910f585c9505d952443d61275411654910f58485505d952443d31785417655110f4c5d95741954443d31756017655110f4c5d57655202443d31755017655110f4c5d1505d954443d3157419545c910f4c545405d954443d31505d9545c910f4c505505d954443d257549d5458910f495c97655152443ce1725817558910f3849d6045562443ce1215817558910f345e53758163443cd1764dd8058d10f345d93758e02443cd1674c1635c910f3459d3058d12443cc96349d064c910f3158d725d932443cc56349d164c910f3158d215d932443cb17651d0559110f2c5d9405d564443cb1675050559110f2c59d4045564443c717955d6059510f1c5d95760165443c717655d6580910f1c5d95759504443c71675456541110f1c59d5059574443c7167541655c910f1c59d5059514443c71675416544910f1c5855059572443c7157581655c910f1c55d6059512443c7151581655c910f1a5952741952443c695649d0558910f19595725d952443c656549d1654910f19595215d952443c65565c97558910f195592745562443c65564857558910f1659d50595344c3c396455d0655110f0dda1755d954443c3575d917655110f0d5d5645d954443c35655d9545c910f0d595745d954443bc1274c1864c910ef04853061932443b91804d94550d10ee45013661543443b91306194550d10ee44c14661543443b61275418654910ed84855061952443b51584d90550d10ed45613059543443b33a06195) else (if j<5 then (0x204c08100000000000000000000000000000000000000000003202d0264a520b805188d82c42b029440b10ac0a520b101202b02943029289080a407421360b10ac0a5205140b40a603c81440c302d0264a5805142c42b02943026105080c80b4098302d044d80c80b4098a9602d014703202d026205104d80b40a5014413602d02980f405144d80a4203202d20b405102c42b0294a2a01450b10ac0a528a102c42b0294a2a01458360b10ac0a528a105180c8102d026a870c1200c80b409aa1c414602900fa890c0a407403c302d0268a5405102b0294202d0264a5105102b02942a87105080ad61c8164084032405084d80a50143f097803bc5dd0ed97683b1dd7ceb57563a8dd34e9174139fdcf8e7973b39cdce0e61729393dc98e4371d38ddc50e2570b3805be4de36ed3715b6cdad6d2366db30d8f6c63625b0cd7d6ba3595aacd4d6a53505a70d2368d3445a1cd0b68133e59e0ce7672336d998cc966032f5968cb16543295944c9364532058fcc7b63c31bd8ccc5d62a314589cc4b61e30cd854c2160f306d830c15609303d818c09603300d800bfd5fd2fdd7e8bf15f72fad7d0be55f12f7d7acbd35e52f05770bb55d62ea5740b975ca2e45704b7f5bb2dcd6d4b5b5ac2d556a4b4359a2cad644b1f58b2c35608afb5792ba55c0ad75672afd578ab95582a9d548aa154f2a55518a8353d29c54dca6553129654a0a4d522290547ca3551928a544ca1d50d285d428a0b50127fd3f89ed4f5279d3bc9d54e9273d3989c94e026f53749b14d4267d32c98d4bf25ed2f09754b6258d2b49514a424fd26c92d495248523c915489243d218909483240d1f48f1474237d1b88d3465231d1888c145f22ed1648af45622a514c8a3450227511c87f43821b50bc85b429213d09884341d20c505c825411207d02c8134052004ff07f53f31f74f9c7cb3db1eccf547a13cc1e3cf0c77d3b71daced075f3ae1d64ea074d3a21cece6472f3961ca4e4c7233901c74e2870b3841c14e046ff37e1be4de06ed3751b84dbc6db36c1b24d8c6c33601af4d686b13571aacd5069934b1a34d0868133f19ecce466f33619a4ccc663330195cca865132118ccc6061b3061824c0c5e52ee1764bac5d32e8171cb885bb2dc16d4b585a32d01674b1c58b2c41614b045732b815b4ad45672b21584abc55b2ac1554aa45492a3150ca8053d29d14dca5c51f2881434a1450728214049fc4fb27c13d49d84e9273138c9c04dd26d135c9a84d1267132c9784b3252128493c49b24c1254918489243120c90047d23d11dc8e8465231117c8b845922b114c8a044d225111c88844121f10ec870435219108c84041720a10448104052010ffc7ec3ed1f50f9c7c83e11ec0f3c78c3c31e00ef47743b71da0ec475c3ab1d40e9474439f1ce0e6472c3931c80e347143871c20e046) else (0x294112430208c08120d30209218121d06408190206408130206414101d040988142000000000136029084d90142000029064081020924082000ac88c20c30261050ca1a01422869020a408113690f4050c8c205c2a0206408181704028604000090206408112430208490c0821050400270541412130111020d420110204000a18110204a18102404028604090834200834100c0810040810004871020840810110400009020640819020405c100002014408210204090102404000000000000000000000000000000002808100c08130204074100304100c081302040022950142002941020c8142730208000012430209091808212404c0810087413020409c102706408190206408190206090143881108002408180d040000a020640819020640819020409020400c10522410240810008360409020409020400004890603410002869020800240819020400000141410000290409c1027052181208048e50c82000010c8190206408150805420150805034150804090204050804000000002408190205420150804028605034100000001420100000000002036408280d9020806e0442020f1098202218100080d060341a0504080f040024081022181824060901000ac0902026040ca4082010f48ca0ac301014181704a1819020605c18170607ca182000a05040008901018141505054141000000000000e4103904000000001064100090204000003c01d0800000087c10000000480290809020487c10000087c100000000001d0400205f014290f40508002b0242230c0ae808200083282b886c05902148e41000000817040902040000a41108040000ae80820000000b70920800000000000000000480400000000209c182b81b081104ac2000000000000030081000000000000000000f08c82221040f20b4200000000074100000000000044442b08000000000000000000000000022121f08021b040008841000004841c020400000086c130))))
def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x1e028442b45a68b024d1821b4fc0780f0020a70913b4c27958780a52aa2d7617f01e03c0780f01997c01d4f01e03c041cf000750d405529e03c0292515d7bc0780f0118fc0686abfa2e25be60db533c0780f01027c0780f00e826d20df474c506421e32b77c028361e87f4c780e0153bb712cf0143bc0780893093c01cac2d162e7f80155c6f12f8062329f8aae2a03e0297c87a8de02000fe03e28c1004e030060)
def genData7 (j : Nat) : Nat := if 17 ≤ j then 0 else (if j<8 then (if j<4 then (if j<2 then (if j<1 then (0x10655110bd8ca20caa2217b19441943442f632882a86885ec6427655110bd8c848caa221773955d905442ee32b3b20a885dc6561641510bb8caa0caa2217719541953442ee32a832a4885cd6567655110b79caac0b1a216f39358165442de32d82ac6885bc65b0458d10b78cb4c0b1a216f1968c163442de32c82ec6885bc65905d8910b78cb20ab1a216f19641562442de321b3aca885bc6436758d10b78c86cab1a216db9558d064c2db728b1a0c985b6e496341930b6ccb4c68326159d94cdd63c82b3b299bac6904fce6176809109f9cc20d39a213f39841a534427e73083426884fce610654d109f9cab00b1a213f394601654427e728c02c6884fce4d80595109f9c830ca92213f390619324427e331b2a06884fc6636440d109f8cc60ab1a213f198c11634427e3313b20a884fc6627640d109f8cc2cb012213f19858e024427e330b1804884fc6613058d109f8cc20d992213f19841a734427e330834a6884fc6610690d109f8cc20caa2213f198419534427e33083286884fc66105d91109f8cc20bb1a213f198417624427e33082a86884fc66103d89109f8cb70a81a213f196e11034427e32dc02a4884fc65b804c9109f8caf08832213f195e0d064427e32bc02c4884fc64f85419109f8c9f08832213f193e01624427e321c3aca884fc6438758d109f8c870ab1a213f190e11654427e321c22c6884fc64383595109f8c8704b2a213f190e09634427e321434a6884fc642865d5109f8c850cb9a213f190a19534427af26c3aca884ede5187589108efc9b0eb2a211bf9461d62443e4640aa2a48878c5950655110de19930138c65bc293a0b7044378327416e0886f04c98004d21de09830521a21b918060e5444372280c1ca8886e44c184cc910dc29930809a43b45326141348766700aa2a4886cc5615480910d98a030ba1a21ac532618134873c50f9046488678a09809c632ce99930138c659c527a0e12c42f4525b84a8885e8a4b7055110b99cab00aa22173195dc154442e632a832a888574a4f215c221ae349f0eb962151d95a1273c867a327416e0884f464c82419109e8c9904822213d193202624427a32640484884f464c80589109e8c9900a12213d190a06324ca7a13098264884ec65082419109d8ca101312213b1942023244276328402c4884ec650804c9109d84c280a12213a994201234826e32a4120c884dc65482411109b8ca9013122137195202424426e32a40464884dc65480589109b8ca900a122137195201324426d32a40246904cd65684ccb1099acad09992212f196209044425e32c40484884bc658808c910978cb100a12212f196201324425e130b02c4884ba6588048d208f94bf01192211f190a07768ca3cb2f414878844f656849cf2189ecad0939e4113d95a127398a27b2b424e690c4f656849cd20) else (0xb9071b55d6259520df1c024ca9221be380499324437c640c32a4886f8c81864c910df08330521a21bd3804d9324437a32cc1804886f460136cc910de8c026d29a21bd1804da434437a3009b2a6886f46013650d10de8b1b0383261bd13858e024437a270b1804886f44e103d8910de89b30382a61bd130e15634437a261c22c6886f44c38258d10de89830d99221bd13061a534437a260c3486886f44c18654d10de89830ca1a21bd130619324437a260c2a86886f241982cd130de29b30521a21bb380551624437630caa404886ec6116300910dd8c04a8b1a21bb1805536244376300a32a8886ec6014650d10dd8c028aa1a21bb1406195444376280c3286886ec5018550d10dd88330999221b9906613324c372a6cc2664886dce015654910db8c2ac601221b7180559544436e300ab2a6886dc5616580910db8ac20bb2221b7158417634436e2b082ec4886dc5610550d10db8a8708b2a21b7150e0d654436e2a1c12ca886dc5418655110db8a830ca9a21b7150619524436d304a82ca906da5498059520d9ac3aa8a9221b35865515244366ab0aa6c4886bce016558910d79b420d39a21af36841a534435e6d0832a6886bc64d8600910d78c06cab1a21af180597634435e300b2ec4886bc6016558d10d78b42cb01221af16858c024435e2d083664886bc5a1069cd10d78b420d29a21af16841a434435e2d083426886bc5a10680d10d78b420caa221af168419534435e2d0832a4886bc5a10650d10d78b420c99221af160e15634435e2c1c22ca886bc5838458d10d78b0706b2a21af160e09654435e2c1c12c6886bc58185d9110d78b030bb1a21af160617624435e2c0c1eca886bc58183d9110d78b0307b1221ae982581654835d304b02c6906ba5898059520d6cc1ac1b2a61ad983583644c35b306b06c4986b660d6059130d6cc1ac0b1261ad9684db054c35b2d083668986b65a106cc930d6cb1f0a83261ad963e05064c35b2c6c06ca986b658d80d8530d6cb1b00b2a61ad936603325835b26cc0662b06b64d98090d60d669b30521ac1ab9845816350353a6cc2664b069e61560d8950d3cb2f06832a1a7965e09065434f2cbc0a0ca869e59580d8950d3cb2b01b0aa19f196602718cb3e2ecc0e0a986735d982cd130ccebb309992617e3925da02442fc720932a4885f8e41264c910bf0cb640a92217e196c8132442fc32b902c4885f864f2058910be9caa60b1a217d3944c163442fa726bb206885f464f6540d10be8c9ec881a217d193c1563442fa327822c6885f464e8640d10be8c9cec81a217d19398163442fa327182c6885f464e1640d10be8c9a0d992217d19341a53442fa32683486885f464d0654d10be8c9a0ca1a217d19341932442fa3219bac6885ece610655110bd9ca2ec822217b39441954442f6726832a8885ec66)) else (if j<3 then (0xfb2bc22ec9847f657845d9108fecaf04bb2211fd94e15764c23fb29c2aec8847f653815d9508fec9f04bb2211fd92e15764423fb25c1aec8847f64b815d9508fec9702bb2611fd91e09765423fb23c12ec9847f647805d9328fec8702bb265fc3204d932443f826093264887f049d304c910fe090a6099221fa32055162443f22809b286887e44c25458d10fc89828ca1a21f913051543443ec640ab2a4887d85412654910fb093aa0a9221f612154152443ea2a09b2a6887d44c15654d10f98caa0caa221f318754154443e62ca832a8887cc55d8055110f98abaa901221f315750154443e62ae832a8887cc5595480910f98aa20aa1a21f315150154443e62a13b2a8887cc5424655110f98a82ecaa221f315055362443e62a0aa2e4887cc5415458910f98a828caa221f314754154443e6282a82a8887cc5015655110f98832a8a9221f252755152443e4a4caa2a4887b8c816558910f70b120ca9221ee16241932443dc24eb02c4887b84856058910f69b3a60b1a21ed3614c163443da66eb02c6887b4cc56058d10f6903260b1a21ed1674c163443da2c683664887b458d0694d10f68b1a0d21a21ed16341953443da2c683286887b458d064c910f68b0a60b1a21ed13758163443da262b02c6887b44c36558d10f68982cab1a21ed106cc163443da20c982c7887b44193058d10f64992c0b1a41ec923581624c3d8a64b0ac690facda10655110f59b220caa221eb16841954443d62cea02c8887ac5910655110f58b220ca1a21eb16150164443d62c12a2c6887ac58154d8910f58b02a8b1221eb14758164443d6282b02c8887a650d6059130f4c9a2c0b1a81e736754165443ce6c2a82ca8879c59d5059510f38b2a0caa221e716541953443ce2ca832a48879c5855059510f38abac0b2a21e715641763443ce2ac82ec48879c5590558d10f38ab20ab1221e715158165443cd2c4a82ca9079a5496059520f32b2a4ca9621e656549952443cb2c6a82ca987955953654d10f1aab2a9b1221e355655162443ad2a4bb20a9075a49d5054910e9abaaecaa221d3557551724439e2c6832e31873c581635c650e78b02c6b8c81cf16058d718839d2c4832ea9073a589065cd20e7493ac0b1221cd9674c1638439b2ce982c68873658d06dd530e6cb1a0dba261cd96341b724c39b2c6836e29873658d065d130e6c9bac0b1ca1cd937581639039b26eb02c7107364dd6058e10e6c9bac0b1a41cd937581634439aaec9bac68873559d3158d10e6a9bac2b1a43cd53758563443972cea02c88872e51d6059130e5ca3ac0b2221cb57651d6444396acea0ac88872d51d6159110e3cb3aa0b2a61c7967541654838f2cea82ca8871e55d6059520e3cabac0b2a21c757655d654438eacea8aca8871d55d6159510e36b3aa4b2e41c6d67549654838daaeb12c) else (0x1921542fcb24bb2a4885f9649764c910bf2c922ca92217e59245932442fb720c126c985f664d064c910becc82ca9a2617d79361d65442faf26c2aec885f5e4d764c910bebc9acaa1a217cf93615264caf9b249b242985eee510655110bdcca20caa2217b7985d954442f6f2cc3aa8885ede51825d910bdbca2ecaa2217b7925d954442f6d2cc3aa8885ed6627655110bdacc2ecaa2217b59791954442f6b28bb2a8885ed6516550d10bdaca22caa2217b49661d54442f3f26b2a86a05dee558341950bbccaa0caa2217799541952442eef2eab2a8885dd6557655110b7dc8304b1ac16f99641562442def24b3aca885bb6496348560afdc92ec82a215fb9060976542bf720c12ec9857e641655c910afbcbac6b92215f7955d972442bef2abb2248857de49765d510afbc92ec8aa215f79160d76442bef22bb2429857de45635c910afacbacab92215f59759512442beb23b9262b057d645655c910af7c930eb2a815ef92601764cabdf24bb242a857be497648530af6cac4e90ac15ed9389d21582bdb24bb2a48857b649764c910aefc9b0abb2215df9360576542bbf26bb2648856fe51825d910adfca2ecaa2214ff9259d654427f728c02ca884fee4186549109fdc830c992213f998419544427f32bc220c884fe64782419509fcc8702b2a413f7985d9544427ef30bb2a4884fde61764c9109fbcc2caba2213f798595724427ef30b1ae4884fde5d86551109fbcbb0ca92213f797619324427ef2cc3aa8884fde5987549109fbcb30e992213f79561d644427ef2ac3ac4884fde5187595109fbc9b0eb12213f793619544427ef24c3aca884fde498758d109fbc8b0ca92213f791619324427eb30bb2a8884fd66176549109facc2ec992213f5985d7644427eb30baec4884fd66173d89109facc2caa1a213f598459544427eb308b2a4884fd661164c9109facbf08b2a213f597e09654427eb2fc12c6884fd657845d9109facaf04bb2213f594e1d654427eb29c2aec884fd65383595109faca702b2a213f593e09764427eb25c3aca884fd64b8758d109fac970abb2213f592e0d764427eb25c0aca884fd64b8158d109fac8702b1a433ed92e05654827db25c0ac6904ef65383595409deca702b2a811ff985d9544423ff30bb2a48847fe6176505508ffcc2ec992211ff985d9215423ff30bb2429847fe5d86549108ffcbb0c992211ff9661d544423ff2cc3aa48847fe59874c9108ffcab0eb22611ff9561d644423ff2ac3ac48847fe5583dd1628ffcab07ba2c11ff9461d654423ff26c3ac48847fe4d85dd1628ffc930eb2a211ff9261d634423ff22c3aca9047fe458758d208ffc8b07b92c11ff9061d634863fb31b9262b047f66176551108fecc2eca92211fd985d9324423fb2fc1acaa047f65f81595408fecbf02b2a411fd97e05634823))) else (if j<6 then (if j<5 then (0x21bf187419324437e30e82ec8886fc61d05d8910df8c3a0ab2221bf187415624437e30e81ec4886fc61d0358910df8c32eb01221bf1865ce024437e30c82a86886fc6190454d10df8c2b0683221bf181419544437e302832a4886fc605064c910df8c0a0ab2221bf181415624437e30281ac4886fc6018459510df8c0304b2a21bf180609634437e300bb2a8886fc60175d9110df8c02ebb1221bf1805d5644437e300b9ec4886fc6016550d10df8c02c8a9a21bf180551634437e3008b2a8886fc6011559110df8bb30b01221bf17660e024437e2cec02ca886fc59d8058d10df88330aa1a21beb90609654837d720c12c6906fa6098059520df3c8b04b1a43be587499524437cb0e93264886f96052654910df2c0a4c99221be527619524437ca4ec3264886f94858654910df290b0c99221bdb9060d624c37b30682ac8986f64c1864c910debc9b0eb2a21bd5874d9324437ab029b264886f54e173d8910dea9b30aa1a21bcd23619214c376f28c3ac4886ed61d54d8910ddac3aa8b1221bb5875195444376b0ca2a86886ed51d8655110ddaa330aa1a21b7950619524436eb0eab2a8886dd61d5654910dbac0aaca9221b75585d7644436eab0baec4886dd5616550d10dbaabf08b2a21b7557619544435f720c3264b06be5a10655110d7cb420ca9221af968419324435f2c1c1acaa06bd61d65d8910d7ac3acab1221af581595624435ead0bb2a8886bd5a11655110d7ab3f08b2a21af567617644435da4cc1a42b06b74e16348560d3f2c2cab9ac1a7d68559215433f720c3aca9067ee418758d20cfcc3a0caa2219f987419524433f30e832648867e61d0558910cfcc02ecaa2219f79161d634873ef22c3ac68867d61d1655110cfac3a2ca92219f587459324433eb0e8aac48867d6057655110cfac0aeca92219f5815d9324433eb02baac48867d5e17655110cfabc2eca92219f5785d9324433eaf0baec88867d5e175d8910cfabc2eab12219f5785cf624433df2ec12c79067be498758d20cf6c3a4ca92219ed87499324433da4ec32a48867b49d864c910cefc9b0eb2a219dd874d93244337f28c3ac89866fe518758910cdeca30bba2c597d87559524431fb0eb2ac48863f5a17655110c7eb2b03b92c17f39759602442fe72eb2a08885fce5d6380910bf9cab06832217f3955da02442fe72abb208885fce517641510bf9ca20cbaa217f39441953442fe7288322a885fce4d7680910bf9c9aca822217f3925d905442fe724bb206885fce458341910bf9c8aca822217f39060965442fe720c12c6885fc65d6580910bf8cbaca822217f19758e02442fe32caa206885fc6456541110bf8c82caba2217f19059572442fe320b2a86885fc6416545110bf8c82ca892217f19059153442fe320b1ae4885fc6416344910bf8c82a8b1a217eb924) else (0xb1a2c99221ed56345931483daac29b242987b545d364c560f669b246b0a41ecd3258d21583d7308b02caa07ae5910655110f5cb220ca8a81eb96441941543d72c0b2a86a07adda17655110f5bb22ecaa221eb5685d954443d6ac8bb2a8887ad5911655110f5ab222ca0aa1eb56151951503d3a68b2ac6a079e5958341950f3cb2b02832a1e796541954443cf2ca832a48879e5950654540f3cb2a0ca8a41e796541941543cf2ca83242a879e5590558910f3cab20ab0a41e75655d954443ceacabb2a48879d5951654910f3ab2a2ca8a41e756155921543ceaacbaec48879d5597558910f3aab2a8b1a21e755645562443cdaca932a48879b5952654520f36b12ac90aa1e6d5649561483be2ecbac048877c5d97541110ef8bb2e701221df17645504443be2ec82ae88877c5d9055c910ef8bb20a8a221df17641512443be2ec81ae48877c5d90344910ef8b3a0cbaa21df16741973443be22c82ae48877c419755c910ef8832ea89221df10645572443bd24e832a48877a49d064c910ef493a0ab1221de5725d952443bcae4bb264887795c97558910ef293a2ca9221de52745932443bca4e8aac4887794857654910ef290aec99221de5215d562443bb2ec82a68987764c1764c910eeabb26eb1a21dcf925d9324c3b9a4e9b2648877348d7648530edca3a0caa221db9405d954443b6af0bb2a88876d5d9545c910edaba2ecaa221db54745954443b6a82bb2a888767e51764d130ebdcaaec82a61d795741954443af2a0bb2a88875e5417654910ebca82cab9221d757655d65443aeaeabb2a88875d55d655c910ebaabaca89221d755745954443aeaa2bb2a88875d545655c910eb693aaca9221cf967595044439f2ce82ac88873e5817559110e7cb02eab1221cf9605cd624439f2c0b2ae89873e581655d110e7cb02cab9221cf96058d724439eaecbaec88873d5d97559110e7ab3acaba221cf567595724439eaceb2a288873d59d6544910e7ab3ac6b9221cf56758d124439eace8aac88873d5857559110e7ab0acaba221cf561595724439eac2b1ae48873b89d6548560e76b12ec90aa1ced27595624439baceb2a689873758d764c910e6eb1acaba261cdd365cd614838ff2ab3aca9871f5957654910e3eb2aeca8a41c7d565d5624438faacbaac2906fce558058d10df9ca300b1a21bf392601634437e722c02c6886fce418654910df9c830c99221bf3805d9524437e700bb264886fce017558910df9c02e6b1221bf198596024437e330b2a08886fc6616380910df8cc2c601221bf19841a734437e330834a6886fc6610654d10df8cbb00b2a21bf197601634437e32ac02c6886fc6518059510df8ca300b1a21bf193601654437e324c02ca886fc6498058d10df8c830caa221bf187581654437e30eb02c6886fc61d0655110df8c3a0ca92)) else (if j<7 then (0x4c910ff093a0ab1221fe12740d62443fc242832a4887f8485064c910ff090a0ab1221fe12140d62443fa32c982c6887f464d0694d10fe8c9a0ca9a21fd1904d932443fa30e982c6887f459d3058d10fe89bb00b1a21fd13758e02443fa26eb02c6887f44d90550d10fe89b208a9a21fd13060963443fa260bb264887f44c16550d10fe8982c8a9a21fd13058d72443fa260b1a24887f44c15458d10fe89822c99221fc93049932443f924683242987f149d364c910fe291a2c90a61fc5214d932443f6330832a8887ec6516541110fd8c9a0caa221fb18741954443f63013b2a8887ec6017655110fd8bb2a901221fb16841954443f62ce832a8887ec51d0655110fd8a3a0ab2221fb14655103443f628c82a86887ec5050655110fd8a0a0ab2221fb1405d954443f6280baac8887ec5016550d10fd8a02c8a9a21fb14055163443f62808b2a8887ec5011559110fd8832a8b9221fb10651543443f4a4eaa2c4887e650d0559130fca9b28aa1a21f719541953443ee320ab2a8887dc6415654910fb8c3aa0b2a21f716754165443ee2aec02ca887dc55d6580910fb8abaca82221f715758165443ee2ae832a8887dc5595440d10fb8ab208a9a21f715159504443ee2a2832a8887dc5418459510fb8a8304b2a21f71505d954443ee2a0bb2a4887dc541655d110fb8a82cab9221f715059543443ee2a0b2a28887dc5416544910fb8a82c8a9a21f715055163443ee2a08b2a8887dc5411654910fb4c12a0b2a41f695260165483ed2a482ac2907da5412654910fb293aaca9221f652155952443eb2a0b2a68987cd6557655110f9abb2a8a9221f355791954443e6aaeaa6c4887cd55d5458910f9aaba8caa221f355655172443e6aa8b2a86887cd51d5655110f78cbac0b2a21ef19758163443de32ab02c6887bc64d6059510f78c9ac0b1a21ef19059562443de30eb02ca887bc61d6058d10f78b3b00b2a21ef16760163443de2ceb2c04887bc59d6541110f78b3ac701221ef16741764443de2ce82ac8887bc5950458d10f78b0aca82221ef16141564443de2c0c22ca887bc5818259510f78b0304b1a21ef1605d764443de2c0baec4887bc5817559110f78b02eab1221ef1605cf62443de2c0b9ac4887bc581655d110f78b02cab9221ef16059543443de2c0b2a28887bc5816544910f78b02c8a9a21ef16058d72443de2c0b1a24887bc5815458d10f78b022ab2221ef16045562443de2c089ac4887ba6096059520f74c12c0b1a41ee96260165483dd2c4832a4887ba5890654520f74b120c99221ee96241931483dd2c483242a87ba5890648530f7293acab1221ee52159562443db324b1a0c987b661d6341930f6cb1b0a83261ed963605064c3db2c683264887b658d064c520f6cb1a0c90a61ed960595344c3daac6bb264887b558d6550d10f6a) else (0xf99af7daf6caf5baf55af4faf33af17af11af0baf05aeffaeeeaeddaeccaebbaeaaae99ae88ae82ae71ae1eadaaad2bac96ac22abaeab5baafdaa7eaa2ba9c2a943a8c4a866a813a794a736a6aca638a5cfa550a4f2a489a415a380a317a2a3a245a1dca15da0e9a080a0019f6c9ee29e639de49d659d079c939c1f9bb69b429afa9aa79a4999f699a3994598e79894984c97ee977a96fb96a8965595f795a4955194f39495944293ef939c933392ca925691f8919a911b90b290548feb8f778eed8e9a8e3c8de98d968d388ce58c928c1e8bcb8b628b0f8ac78a748a2c89d98970891288bf886c880e878f873c86bd865485ca856184d78484841083b2835482f68298824581f28173812080c2806f80327fdf7f977f397edb7e887e2a7dcc7d797d107cbd7c547beb7b8d7b2f7ad17a687a0a79a1792d78cf7866780877b5774c76f97690762775d4756b750d74ba7467741473c17384732672de7280723871f071a87160711870c5707270096fc16f796f266ed36e756e176dc46d716d136cb56c4c6bc26b6f6b116a9d6a2969cb696d68f968a6685367df678c67236699663b65e8657f654264e46486643363eb6382631962bb623c61de618b612d60cf60665ffd5f9f5f415ed85e645de55d9d5d555d0d5cc55c675c1f5bcc5b845b315ade5a6a5a1759c45966590858b5585757f95790572756c9566b560d55ba555154fe54ab545853ef5386532852ca5256520351a5514750f450a150384fe54f874f294ee14e8e4e304ddd4d7f4d214cb84c654c074ba94b564af84a8f4a3149d3498b494348f04892482947aa476d473046f346b6466e461045c84575452244cf44924455440d43ba4351430942c1426e421b41c84175412240cf4092405540023faf3f3b3efe3eab3e583de43d703d123c933c1f3bab3b373ab83a7b3a1d39bf394038e2386e380537b2375f370136a3364535e7359f354c34f9349b344833f533a2335a32fc32b43256321931dc31aa3157310430b1305e300b2fb82f7b2f332ee02e8d2e2f2dd12d7e2d2b2ccd2c6f2c1c2bc92b6b2b0d2ac52a882a4029f8298f294728ff28a1284327f02792273f270226c5267d263525d72584252624c82480242223da2387232922d6228e224621f32195214220ef209c204920221ff01fd41fc31f441e991e3b1dbc1d321cd41c4a1bd61b6d1aee1a901a32199d19081894183617d8176f17111692161315891515149613f613981319128411fa117010e61088102a0fcc0f6e0f050ea70e120d9e0d4b0cd70c840c100bbd0b330a9e0a4009e2098f093108d30880082d07a307030679061005bd05540501048d043a03d1035d02c8023301a90109007f0000ff1902eca9221fe3205d932443fc640baac4887f8c817358910ff0c92cb01221fe19258e02443fc24e832a4887f849d06)))) else (if j<12 then (if j<10 then (if j<9 then (0xd1ddcf6dccfdcb3dc8cdc70dc5fdc4edc32dc00dbe4dba7db96db7adb5edb37db10dae9dad8dac7daabda9ada94da83da72da61da2fda08d9d6d9afd993d98dd971d96bd94fd93ed917d906d8f5d8ced8bdd8b7d890d85ed84dd847d836d825d814d7edd7c6d79fd78ed788d777d73ad708d6ecd6dbd6d5d6cfd6bed6a2d686d680d659d648d62cd610d5f4d5e3d5d2d5abd58fd552d54cd546d540d524d508d4f7d4f1d4d5d4b9d4b3d4add491d480d459d43dd437d410d40ad404d3fed3e2d3dcd3cbd3a4d393d38dd371d36bd365d349d343d332d321d305d2ffd2eed2d2d2b6d29ad27ed262d246d22ad20ed208d1ecd1dbd1b4d1aed1a8d181d170d15fd159d148d12cd126d120d11ad114d103d0f2d0e1d0dbd0cad0b9d09dd097d091d08bd06fd069d063d047d036d030d02ad024d013cff7cff1cfe0cfdacfc9cfb8cfb2cfaccf90cf8acf84cf7ecf78cf51cf35cf0ecf08ced6cea4ce88ce61ce45ce34ce0dcddbcdb4cd82cd71cd60cd4fcd12cce0ccc4cc92cc76cc5acc33cc0ccbcfcba8cb8ccb65cb3ecb17cae5cab3ca97ca65ca33ca0cc9f0c9dfc9cec9b2c996c985c974c963c952c936c91ac8f3c8ccc8b0c889c86dc851c835c819c7fdc7ecc7c5c7b4c7a3c787c760c739c712c6f6c6dac6bec6a2c69cc680c659c63dc621c605c5e9c5cdc5b1c5a0c59ac57ec562c546c52ac50ec4fdc4f7c4dbc4bfc498c47cc460c444c433c417c3fbc3dfc3c3c3a7c38bc37ac369c34dc331c30ac2eec2d2c2ccc2bbc29fc283c267c24bc23ac229c218c212c201c1fbc1c9c1a2c191c180c16fc15ec14dc11bc0e9c0d8c0c7c0b6c0a5c094c083c072c061c050c034c018c007bff6bfe5bfd4bfb8bf91bf80bf6fbf5ebf4dbf3cbf2bbef9bee8beb6bea5be94be83be7dbe6cbe5bbe3fbe23bdfcbde0bdc4bda8bd97bd86bd6abd4ebd32bd21bd10bcf4bcc2bc90bc69bc42bc31bc20bc0fbbfebbedbbdcbbcbbbbabb9ebb82bb66bb4abb44bb28bb01bae5bac9bab8ba91ba80ba6fba5eba42ba31ba2bba1ab9feb9d7b9bbb989b978b951b935b92fb913b8f7b8dbb8bfb8aeb887b84ab839b828b80cb7f0b7d4b7a2b791b775b76fb75eb758b73cb72bb71ab6feb6edb6e7b6e1b6dbb6bfb6aeb69db676b65ab649b638b632b621b610b5ffb5f9b5e8b5d7b5bbb5b5b5afb59eb598b587b581b570b55fb54eb532b521b51bb50ab4eeb4ddb4ccb4c6b4c0b4bab4b4b4aeb4a8b48cb470b454b42db406b3eab3ceb3bdb3acb39bb38ab379b35db341b325b309b2edb2dcb2c0b2afb29eb28db27cb260b244b212b201b1f0b1d4b1c3b1b2b1a1b190b17fb158b131b115b0f9b0e8b0d7b0c6b0b5b0a4b09eb098b092b08cb086b080b07ab074b06eb068b062b051b040b02fb029b023b01db017b006b000affaaff4afeeafe8afd7afd1afb5a) else (0xb01061c828440821024a254300418700d41522241100980ca1602143c06208e0a80900f002c0c8162264408590880ba1341902a00582a04c0588991021642343405d0840a80180f00e81902e0544300550940a80140a8138232284408610850c40880d002c240c51864e09b03205a0ac14826b0ea1802d02389291882c04085408805004804c0660b01061e0320470580500780160c60941182123e4760cc1782b84186e05c04d04c0660b0133240400598a81181601401301b02603204cc900d01662b44e87c0b808c04c0540999201a02cc5689d0d81741e02304910f115a2743905204400812443c4568920ba0c81100200990f017a2743905204400802643c05e8920ba0c81100221bc258310480800d814620c1120648a80f016a2882902200403604c064cc0133240340598a513a1f02e02344c11512443c45289d0e41481100284c11501e22882902200381922a04c8780b513a1c82902200501922a03c05905204400702a04c8780b51522482c83204400a0324540780b20a408800e0d8130190266480680b315a2743a05c04602634a0540999201a02cc568950c81741e02344910f115a2743905204400812443c4568920ba0c81100204c11501e22882902200381321e02f44e8720a408801004c8780bd1241741902200401922a03c0590520440070324540780b20a408800e0ca09c1081f23b0660be1061b81701e00603f06504e4941182103e4760dc16624c3702e00702602a04cc900d01662944e86c0ba0f01180544910f114a2482e8320440091304540788a20a408800e0540990f016a2482e8320440090324540780b20a408800e0640990f016a2a44c8720a40880140648a80f016414811001c5289822e0460788a61141481130960c41222003605689111a1cc1150a40c81481f2388690cd12c2343705d07c00d06304a08c1091f23b0660bc15c20c3702e02683182504607c8ec1982f0518930dc0b801905209c1292123e4760dc1982f05109e11c1cc31c0ce0941182123e4760dc19c20c3702e02603282504607c8ec1b82cc4986e05c00beefdeed6eebaeea9ee82ee5bee34ee0dede6edbfed98ed71ed4aed23ed07ecebecc4ec9dec76ec4fec33ec17ebfbebdfebceeb9ceb5feb43eb32eb21eb1beadeeab7ea9bea95ea79ea5dea41ea04e9dde9b6e98fe95de920e8eee8a6e87fe858e83ce815e7f9e7dde7c1e784e768e74ce730e6fee6d7e6d1e6aae678e65ce64be624e5fde5c0e599e567e535e519e4fde4e1e4c5e49ee477e466e44ae418e3fce3bfe3a3e37ce36be344e328e322e311e300e2d9e2bde2a1e26fe248e237e226e215e204e1fee1b6e18fe152e120e0f9e0d2e0abe08fe073e041e00fdfdddfb6df9adf68df36df0fdef3ded7dec6deb5dea4de93de82de71de60de4fde28ddebddb9dd92dd6bdd44d)) else (if j<11 then (0x51c1e03605a0ac14c8780a383603a04c07a8720a40880100d80980f112a1c82902200403602603c4488720a40880100d80e81301ea1c82902200403605a0a544a8720a303605a09a05a8950e41470900d81682b052a1c828e1201b03205a09a05a8720a403806c0ac4488740a40870700d81581111221c810e0d81682b052224439051c2083a05a0ac14a05182283a04207c0ea1581e22480740b41081381e82c605204c0790e11222043e00201481d02203c470a0a40e81101e238503642201600101480f81a624c3c02a00393603aa4807c05a05400705207407c0d81100a800e4f09b029827016815001c6282d05304e07905a04384806446544a8680b408704207609a89a04284818a0a489c05a04303205a09a52a05604c00705a08409c92416c09800e0d816829426624c3c05c0440c506c0840ea1331261f01100d80e81301e42c829021c1b01301e42e44905204383806c0ae0698930e81601100e01b02b023034c498780440b71622b052c05c05800716e2b05009251580b000e0d80e89201ea2ac3a05404403602603c85a8950e41481100a40e81301f02e810c0a40e80f81b008503a04d4900f80b408605204d4900f91340860900f01902f83322543405a04484805a0a609c05a04303c04207609c89a0430c506c0ca0ca8790c41681100d816829826a2543905a04403605a09944a8720b408705e0a41081d82721882d02201b02d02702d44a87a04381d02603e02e02141481301e627010a2c4560a580b40a800c2b05009281740a800c1201b032833224c3205c04403c06c0b414c1340b808716e0c81682654a41681500201e03605a0a509a0f80b808806c0840ea13913808616e0b41081352502e81500202402b21a81481300181581f02283c8690260038c11740b414a1341e41581103141911991321902b021c6282103a84e44b0218240c305244d02b02181c03205a09902b02600383805a08409a0f216c0980112480798930e815813001c15a0d31261d02a02600382b41a62484187404c00705284cc498740ac09800f11302d020e1cc3881b4084c0b4082a040ab71622b0158a55248354548600ac08b18a30c9c1360640b41582904c61d4300550940a801e8950c01061c0350548890440260330580820f01662a04605805800b04c0660b0133240400598a81181601600301381a82c0480640880500480520740989202203c47689d0cc1741b02300c89802e05444a05d0820d81300280c89802e05444a05d0820d81120a40e89c0260440788e41a82d82b022c1381a82c04806408805004804e06a0b01201902201401211c0b11580ac52a1341a82e43005908c09801aadc588ac0562954920d51461802984c05800d02e05509a1141e22443105106c08a04e06a0b01201902201401205289822e0460788aa0a408844a8604) else (0x4c05a0540091862dc1902d04ca9602d02a0048c11740840f81d11340a80102e85b82d04204d49502a0040c11740b41582950e41581103146183222b21902b021c628ba04207c0e915112a1d811230c1682b05243d02b021c6183205a09885a0560438ba05a0840990b50ec08718a30c1b03242a21e43105604483605a0ac14a0f11221c82b02241b02d04c82c4488720ac08806c0b41582911221d02b0220628ba06c0840f81d42a22443b02281b02d02682c4488760438c306e0c81682644b01680102e81b82d04204d0910ba0040c306c0c816826217014705a0a44488810f016800e1141d02103b0544488810f400905a04e0588911021e800e1041d02103e0750e089a00403a16e0b41081342443e80100740980f40a809000c0a40981101e83844d001c1481d02604407a0e817400806c0b41582925083e028e0d81581f02244107888804402d0528a08788911021e02900e01b02b0228408788910f00891860d81682b05243e028e8dc1481d0260440788e60e402903a04c0788e410c1e01100a40981101e23904b071c1d0290260440788e412c1c80822e81081f03a8708a809a00483a0520740981101e23983900b41340b11222043905a00403605a0ac1492840a30360640b41312540a303c0700d81592340b008705a0991288911021c82b04201c03605688c4488720ac1201120ac5201b02304006e0a712221c38822c1b01d02603e028a0e81481101ea2450740a40e81101e284716e06c06c02145b83205a09805a05185b82d04204e4920f016c08816e2c4560a5115014616e2b05009281e22a810e2de1b0b1158294451051c5bc361582804908aa04381d02604407905141481302203d448a11c1581f02300b000c0b41598930f017016001c628ba04207c0e98930f80b00120740980f20a408800c04c07c8920a408800c0a40980f31261f016001c1c02b022624c3c02c00381301f22643905204400703a04c0788e20a408800e0e01581131261e016001c1c02903a04c07c0ba04384803a04c07c05141e02902603e448a3149b02d0560a407c051c9b02103e0740980f912383826c0b41081352403e05d89a04502903a03c47102149b03284ca1a02d02a00381f03605e06889805800726c0c80e819112a1a02a83a05400a26c0b41582922643e44c05a05400a0784d81902f84ca1a02d02201e1360640740c815112a1a02a83a04583c26c0840f81d02b04c44d05506502f04207c0e815826416c2283a04513826c0ac8890d11261d0290260050c526c0c80e81930f21902c83604c00b08e0ad02c02c002838056624c3a0550900b00100e01598930e81542402c00404826c0c81482691361d43005509408b0903149b02d0560a402a84202403826c0c81682654b02c02a84286193836e0ae8898750ca1281120f01b02d0560a64390))) else (if j<14 then (if j<13 then (0x8e1106182b04888e0448700a40890560910428780b210810e1111b02b04802143c0590840890880ac1202381121d02a84204483105809c1290a80b21070700dd1b03205a09885c059084c360620b01382521521d02900c81682604a42e43a051c1c1361622b05280b40a383826c2b050092016c0870902dc588ac14a815810e2dc560a0124c0854780a409c9201ea2581300201c0ac14024807b02180e89201f229c4b8780b00880520740880f11cc08603a04c0880f11c814605204c0880f11d224618a0b41582901e814604207c0ea1501f224602603d44a8780b00a000e2dc560a012403d456021c0e89201ea2ac4d8740a80900120b409a8950f40a800c0740980f80b00a000c3045d02d05683c82b021c628ba04207d07c8960438ba0700b41081341e42d81100a40e81302203c4720b604401d0260440788e40ac08705204c0880f11d225810e3145d02d0562a102b0260040c11740840f89c912c0980102ea5b82d04204c4920f604c0091682a01081f03a27109a0f90c41581300301481302203e0728960038ba0522480880f11ca258410adc1902d04c84d05c8920ac098014adc588ac14aa494518980b80b00140750a89201ea2ac3a05404423604207509a0f91241581108d81902d04c84c44a8720ac0980140c81781591281641b021c1081f03a05507c89906382103e0740aa1341f21882c83604503205e22443205604c0071820840f81d13885444b0260048b404207c0e89c42683c43105b08c0980188e01481d02603d05b02600402903a04c0880f81cc0071748e01481d1240440788e61048381622b052c84140e89201ea2ac4d8740a80880640bd0ac8910c01642302206282d0560a50780590838b71622b052a8a30830c51860c94388620a61281500241682b052a254390530940a80120b41328950e414c2502a0040b41500840f81d82703c43105a05400b18a30c1948910c81542302206182d0560a502a8460438c30700c81682640aa11811030c19489b0e21902b0260040c51860b415829150815813002461cb70640b4130a540ac09801230d1b83205a09812c05a0040c386c0c81682644a42c02900c81582714a09188a0d90cc0891868e01902d04c29709b0890d014a1860c81682614b84d0428730c414c2162dc1902d04d21c828c0a40980f31261e010c04c0798930f016810c0b41498930f016810c0d80ec1512403e45405804403605a0a644c8720a303605a0ac1488910e414706c0b41308910e414606c0b41582941f21c828e2dc588ac14aa28c3c051c1b01d12403d4518930e81501200281481d02603cc3d02a00382903a04c07987805400703a04c0880f30f01681500201481302203c44987a0540080520740980f30f00a800e0d80e81301e61e02c0280040c326c0c844a8680b40a8010314618ba05a0ac1) else (0xf81d02603c44987285d03826c0b41081352403cc4987a0458ba05607c08c0f41040871740ac0f81101f21c810e2ea1b02b03e04508487204402d0562a107c8990e41471740b41582941f21c828e0d80e81301ea1c82902200401d02603d0428720a40880100740980f50e414811001c5d43605a08409a1221638b786c0b41081342443c71740b81101442404086408a0248c53744d81902f30ea1a02d0224629360640740a98750d01541d02289b03211261d43405a05400803e06c0b889410a1e41902201e1360640744498750d01541d02a00583c26c0840f81d11261e82a83240f81b02f05444a08906408846c0840f81d112a1c82b026004a360640b41321341622543905604523846c0c81682642682c44a8720ac09801807c0d81711321d419021e1b01f03605d0b08990e408886c0840f81d43843c448e2ea1b02103e0750e1151c1c02b048a2543c0590840880700ac11a8950f014810e30c15a0850f016421021c6183c26c0c81482630ea1942502286193605a0ac1498750838c30704d81902d04ca94c3a8424220c305682202c8420438c305609243a84204302d0560a45428950e414705a09852a8950e41461860b41582950e414c20e30c1c2b70640b41328720a610908830e1b02b04888e439022061a370640b41310b80a38c386c0c81682644a42c70640b41340b21061d02a84201c0b70640b4130a5816420c3a0550858c34740b41582921f014718a0b45602b0522a20790830e815421630c1902d04c2950428730c41491868e15b83205a09852a0850e61882984301c13786c0c81682601681542120ac130a503604c06a0c01701642102a00602b0494214320550840870640ac1221141a61882984405c00a06c0740980f30f01601400201b01d02603cc3a05404800806c04c0790930e81501200201b01d02603cc3a0540480080640b41322501661e028e0b41081342503c059871c1c0b703604c06a0c01702243902a00581d02603d0410520440071740d81581f02303d04102209d13603a04c0880f80a382902604407889145b9360520740981101e382903a04c07888804302103e0750e41501e224c3900d80e81301f21c82902200401301f02643905204400706c0740980f90e41481100200e81301f02243905204400805a08409a1201e42e438e2e81581f02284007c0890e408905607c08c0f410a1c810e8d81581f0230420780850e408905c0880a21202043204487a02482b03e0440820f81121c81100d80f81b02e22504483204402103e0750e01521e226439007c0d81742c05444c0890e408903e06c0b889410a1e41902211b01f03605c4480850f20c811207c0d81702c85444c0890ea0c81148e81b02d0560a487c05908403846e0d81902d04c42e02c8424220c306c0ad0440590840880640b41322521721c02)) else (if j<15 then (0x43502121b8209882840602040090c0026000a0d0506a020a01020000047602120d0506820ad06a020c15a0d09088283410085838081c040818081c0a081b822100040d040c0a08140816040b02060dd020b0102010d06845020a81034081000000000861408284f4082829408287ac1681070e60dd020e225020a1cd020b02834081a040b0205810307e0d850ae0d850ae0d841120f8411095840ec143f4142a040d0206810211010888ac2076434248907d82e02130103408147b8082c0a0d020701034081a040a39437808347286f010609e810405281044341a040d020702834081000000000000000018282c141836080000048604000000060408107e0d850ae0d850ae0d844841236080018660a141f60a1000000602050d8286c1a040d02051582434100c1022dc560a012403d453021c1c4b705a0840989241e02ec4b02281581b22e04c4901181e03405902a00582b03645c0989202303c06a0c01640980d00355ba361622b052a9251522482b02281081f03a2710a81301e22582a83281081f41f22482b02600382103e0744e21341f22641900840f81d13884d07c8620b20d813002c5b8b115829545005908383896e0c81682614a02d02a84241582614a06c0980d01701642102a00582b04c2940d80d41802e02c84205400b18a0b41582915003d02a84206282d0560a45420f90838c32704d814826b0ea1802a84a05400b0640ac0b91121a21a0290220628c32704d81482630ea1802a84a05400c0640bc1582422243443284205400a1620ac1221141a618c2202c00482403e06c0b91121a21942483205400b0560908890d50ca1081500215b8b11582974918630980b00120840f81d826a2443105308a0e81140911181f03605e0a91121a21a41902603400d2700ac8890db0ea1902a8420448c50640740cd8710c81542483604502b222436c3a8640aa1081100c81682642682f4398620ac0894700c815a134228350598620a61101168e01902d04c84d05e8730c41581140c80e81991221902a84906c08903e06c0b91121aa2443405908a0c811607c0d81742c44486b0810d01642102603400d0640bc1321d42a22443005908a0d81300311c03205a09a52a1341721a42302600583205609c130a542683505c86908c08b470adc1902d04c29505b0890d01642162dc1b0b11582954548720a403816e4d81902d04ca940598780a503816e4d816821026a4805987a04503816e06c0980d01721c81500241c0b786c06c06a0c01721c81500281581181ea2543902181581102103d44a8720438ba86c0a40e81301f21c81110d81481d02603c041021c0980f512a1c8290220038ba05607c08c0f410a1c81102dc9b02903a04c0880fa0440ba26c0740981101f014726c0a40981101e22461744d81682b05203cc3c05201e0ba26c0840) else (if j<16 then (0x908a041817040a0a08ba06c0a607a05141b08840b008450d408204c0800105041c105081c026080210a1a8106420104e42020482202a0a808204e0827041498620a183904e103907009c131081400000490142049014202208005e430403682840000440684820130f014010661c0104002401a414300000099020802040a130224083204081420810400084c08840505068402a1c810403020506e02080bd08080ba86080ba860906a02080ba86080bd08080ba8608086d03c2a100d0850c408300050f01481064081404081420121040820000005120924048882021705068204d0684000020d404100020d404120204000041a0a0d404101414102828340810008750d8200000086d03c82870d944850d80990b0c096f29502b00125b813924c004a10408202342081064908104444116e29545060f01902f42a20b7124a28306c03ec3a0010078203c10520847056090813011423811204c0440900a420900f01902f101e01d0824029081c026216183802642c30900f01902f600282b04888c3022840246122481070e1139020e1c2142041847411414810811d04505204223da0a1239037414810811c88a082042239036444384900828220d05060ec86082420509180289c14280a3d051cd05091c91108242056001826216814302642c2a10a188106491438449143844914484445438487643048a41052076448742012480ca54041492022808308f014810611c089020d1e2890a1bc250a09300081340508004e8902870051088609c8404050840409d8104051810409d8104051810504810009b020a22111080a20d080a108080a5020a430204395121208a0a1239865414306122421834142060c08251208266041030912102741a10272101030a041027a0414890418020c181050ea1b84a1a02d020c135020809d020800100839a0a1039a0a1108a041108a0412080404022501021d02004807009980080e009b000e84034201a100d050543020ec1c814602204707604580894201a100d08068282a18144c0a13068282a181870898287084c2a0a0d05068282a1c106e048207004c85874201a100b020581024441a1008410780754188a2410920f818a831284034141a04080834190c0a0d404140f40a140da110083a10a182a118142848624226c0c240606d08090ec860b02c020a0882808142f218296f29485a05125b81392442c405683501065110fc860d068307412880a17050682414142e0a0d049e4860906a020906a020897986080073814207206e08860e702840e48405048102703681068741a040e080606d080a430206020602d02081e405a041d08a04143082f81681098201a11816810781681040089a0412328561108c0a103dc0a121d041ee05a041c3285721b02d0216030303c150d408204d034290cc08208907d) else (0xa948104a48089020c921020888822dc52a8a0c5b892514182601a40830260348106036829020c8880d204182601a40830260348106036829020c8880d204180f200113601e113601f014317404c0786045041020d04287204180f204101140414872041486a0a1405045d4b7026248442604406d082042a1d90c122905068200c51820a40ec891406d0820418386041000518105222010405181040f09b03205f014511221941864d887c050d18017204181750c814810805e8428640a408541ac2202a02109b08930ea1a02d001a029026021817112408302e408203a6260286a26828405c810405c810405e8428640a4085248a24243a414203a6242182074c3105100bd0840a18083482a020c1e01d112414404ec082a0a081d90d414326c0a402861206193690c014518609802860ac12208204220850f014810801481040910104091010521c8104091431020c14c1d30c19890412202081210850c408418621821872dc130a540a2a86204122601a408342e083841a808318a41420204028a4118a0a4c3074214304034810430c1302580a20c304c014301a083804138209c100220c3056092842841a1320d610183044821902b02141392441ac08404e49181060c244b020d1c027c041a1d20a103042e104706d014810811c1b011204204806c0a482880d887c050c1b100086183604c414408e0ad119021023a1020418362041036204120205010280812040902048282808120408c311321831862dc134a540a28ba16e04e4908491439020c92287204192451321832480348106445439020c8880d2041a1720a120d20a808318a414220a090504c4c86080981141a8084022808218a3041481d1122c8604069020806902086183780a18ba06e04c31860d81306098101a0813a04100d04002608270413820e85b813224210e10e80031860d814c05101b0888041813a0410004c08840108a041505040a108a0418110408824d8088080f010200c30130143112a1a02d02100b82010504840242011124228106224845020c44))))))
def genIndex7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (0x9e30a1f00166a7c0014460891e003c0020636977644e0ccd1d6f0004527c00300cf001a4b7c00310f69c4842108e800bd34a7257ee7b09178c32327844b1ec8c05e003c0059961951e003c003ce8391c65a90e17800f001e003c007800f0016047c007800f001e003c0078002a09e0038a5fc20f001e003c00780092444746c6be17b23d1e00103ec82cf001e0000ce7800c8d505dbc00184bf000468543205f100dbe002c2f9c90f001d2dbc003d9bc201e5afc00706af001e0012d9e9478280f033c00780021b3e00127c903992c70449ce9bc68f001a77fc00484e11f9e003c0060fef001e003c006179f00150592a259cdf001c24a8fb49b3f001e002097acd7321c24b0c46c9f89b4be003c005888f0008255e3dbcf4f001e00203f7800f000a586804848ff001a32bc00709af0004537c007800f0002701869f800f001c1a46867800c2d1e00267e50f5f000e1a3c007800997b0657c007800f00187770dc2d54f000a0f3ce7a5cc41e3a78fc0078006185e003c007800f001808fc007800f001e7b488d7800f001e003c007800f001e0010bef80001ce769d8f9f80092efe0034e27800f0002063a6b21d2b3f4b077c00782b7bc5e0030c328c760a1e003c0021e591b5e000607885e8359a577879780ae1ede0020e4097cf001871fc0001fda262c03a05ff8003305e003c007800f001e003c0031f7f001e00320bf8006145e002cea3521f001c1eb0ba7800f000a6930c3f800cbcbe003c00483f50ed52afc007800a8c9e001cc6c8725379e000403f8009815e000c269c69f0019743c002124f001e00288564ce4861c127c007800615e432fc00546732fc01e1c412c4e2266304d2d0988aa317c2d80b9dd297170654440f49481af08470c428d021241c6fea88a45c08062397c6ad0b2b0712307c00206ff001e003c001d91829dc3cfc00389c6b3fe003c0029aaf000049747eedd4f000b2d445aa800526081604df3485f000481bc38559220ebe000e10c20250e3e001c14017ff001e003c58b0066a3ae2cc4229162a95b26e526279ad13ebd066e11f890f00136ba4daf800f001e003c007800b2dfe0012027800f001e003c0011bb0b65e0008337800fbae551fc00758ff000f3afc004136513000dfc005024f0012348ccfa8bc6ae9e003c004966d26bc59106df800d10855ae0111deab0b7e000cebe9a6040c1020418880220020b28004e31014502342c8000e08005022569312781800424382085c280120c48a0008100840818e6810006006408e0408385002498502040840a2c00312000030410116060c002008d01600288120a00004001848106380260e0000204081b10600201180018606043000a0430504180011034080020001004300081808000000008214041020a041000e1c0800000382141400400284800228584) else (if j<2 then (0xf001e003c0049daf001650fc007800b136808741f6926f001440fc0000f7abcfe70fc00342fe1dc847bc007800805b672fc0061ff8b19e00328a4144f00165c00d96003f001e000876f800f001e0028507800f001e003c00511bf0005047c006188f000b4cf6cee14ff037d7b96c2e9040999e0030e2f53df000c7928ad05a2f000c05fc0001ebe321e001494e1f27b1b21e7a685c75813395ff245bce5e1d6c27bc007800f00167f1e009992f001e003c002967aa8411d3c0070e0f001c763c00780062ebe003eb1f800f83632830291c18f001e0020c4f800f000009e420a05743dde003c000955f00187efc00555a313a6377c003080234123e482054c7ca20a080a35a98e207be0004a9716ccbe7c183c0019e0f000215bc00780093fc8597c007867f000781ae806d1ff001a6a3c007800f00162afc767800628de0004d77800f001057bc0028c83407e003c007800b257e0000708814f8ae88178606d9c6821e0004ab598f98b0a6620c554eac92c769bc004083f949e003c007800e270e1726b548b0c2b3b53aea0fde8d94f36ad8808d0be37be003c00091ff001d7eb8c8c8742adda29802278008a1d5277c00504af2b1f253c007800c069e003249f800f001e003c007800b3e2c76fccf0118f0b5e0020a831807835e002812e1e26169e003c721520f000904bc002c41f001068bc007800627240ef4837897a8ab1598439f800b15be003c007800014f469fcb0246cf001e002ae730a8f1c7a7c0893f800e1f5e003483f800f000d30c43ff800238d7376e3b3047c8e5d4b0013395b90aac072861801081277584a74b93d7a8a8706e0e7800f0001807c007800f001c3ffc0058ceabe0040bc00407b01bf83318526894636da21fc007d8ef000d14669a6905b87fc7556cf6197da39e00345dddf74103e0004c2512a312c6677c007de383df843789f78005968f714e77d019a28b00a54b92c4d110d708805ea9d0c243a45e4ef7800d11da2de86e780060640800a5ff80050d845c74f39981c01b028fa67919ac21891b4068f800f000c4a2e68f800398aa552a84d45bf000245bc000c07d1f02133c006033e2dbf3c82ee2555f0ef454fa004442a27fe0000212d2f135fe003c00090b32f5e002d02706bf001e0024e60915a1c5e0036f4f02e91cce3be45f7800b15482a52e0f80031586530e39c9c9b264422f68dc8d6b3d3e003c007800d0b2e18bc007800c3b977efc00299433d5e003c007800f00142b8c88841462afe0022286d93f000029501b4843603545bbc0078008bbd21748a5049aa1d0c07daeb7800c276813ec67d01db1a928062c57800f000a68d8096cb9611943d30288c78f1d5c57faf789b0013e0632862458440f80786009f123d00a7016097695ce18db7cbc007800740fe002e0178001ab980100bc006e2357e0) else (0x7800f001e003c0030f0f001e003cecf800f0009653c000ccb105e7703c00780073cde00120a81baf001233401d7800f00126d0a63408ff001e003c00300f581696d026e019b1958b2dfebf30baf001e002432b801108cd30bc001993c3f3e003c00440631f6c37881af800099146156718598f001e508430ddedf001b4d6c0169f4002b2426c29f8001221e0022b059ca50a974ed63d34e1aa02742a88a7c56fad0a2e7c000937f00140ab4c19141536e6343eb2f800f001e001462a831f00080220b4b5c7f000436249a7800f001b737c007016d232539c874f9cef001e00289d19b1f000012001878)))
def genData8 (j : Nat) : Nat := if 31 ≤ j then 0 else (if j<15 then (if j<7 then (if j<3 then (if j<1 then (0xe831d1209de831c9609de831c9409de831c2629de831c1629dd87cdb309dd87cd3309dd87ccb309dd83ddb219dd83dd3219dd839cb109dd839ca619dd839ca419dd839c9109dd839c8219dd831db209dd831d9209dd831d7219dd831d6629dd831d5629dd831d5219dd831d3219dd831d3209dd831d1219dd831d1209dd831c9609dd831c9409dd831c2629dd831c1629dc874d9309dc874d1309dc874c9309bf855d0319be849d7319be849d7219be849d6629be849d6619be849d6329be849d6319be849d6219be849d5629be849d5619be849d5319be849d5219be849d4319be849d4219be849cf219be849cf209be849ce629be849cd219be849cd209be841db309be841db209be841da329be841d9309be841d9209be841d7319be841d7219be841d6629be841d6329be841d5629be841d5319be841d5219be841cd609be841c9609be841c4329be841c2629be841c2329be841c1629be841c1329be841c0329bd859d0629bd859d0619bd859d0319bd849d7629bd849d7619bd849d7319bd849d7219bd849d6629bd849d6619bd849d6329bd849d6319bd849d6219bd849d5629bd849d5619bd849d5319bd849d5219bd849d4629bd849d4619bd849d4319bd849d4219bd849cf219bd849cf209bd849ce629bd849cd219bd849cd209bd841db309bd841db209bd841da329bd841d9309bd841d9209bd841d7319bd841d7219bd841d6629bd841d6329bd841d5629bd841d5319bd841d5219bd841cd609bd841c9609bd841c4329bd841c2629bd841c2329bd841c1629bd841c1329bd841c0329bc8750d409bc875094097e859d33197e859d33097e859d13197e859d13097e851db3097e851db2097e851da3297e851d93097e851d92097e851d32197e851d32097e851d23297e851d12197e851d12097e851cd6097e851c96097e851c94097e851c43297e851c26297e851c23297e851c16297e851c13297e851c03297d859d33197d859d33097d859d13197d859d13097d851db3097d851db2097d851da3297d851d93097d851d92097d851d32197d851d32097d851d23297d851d12197d851d12097d851cd6097d851c96097d851c94097d851c43297d851c26297d851c23297d851c16297d851c13297d851c0328ff87588628fe861d7318fe861d7218fe861d6328fe861d5318fe861d5218fe861d3218fe861d3208fe861d2328fe861d1218fe861d1208fe861c9408fe861c4328fe861c2328fe861c1328fe861c0328fd861d7318fd861d7218fd861d6328fd861d5318fd861d5218fd861d3218fd861d3208fd861d2328fd861d1218fd861d1208fd861c9408fd861c4328fd861c2328fd861c1328fd861c0328fc8758d608fc87589601fd878c832f315055110be282dc110bd18300910bb18400910b718500910af186009109f1809c632) else (if j<2 then (0x319110bd58318910bd58310b10bd58310910bce83c9a32bcd87cca32bcd82cd330bcd82cd130bb684ccb10bb684cc910bb68418d10bb68418910bb584ccb10bb584cc910bb58418d10bb58418910bb58404d21b9d84ccb30b9d84cc930b7685d0f10b7685d0d10b768519110b768518d10b768518910b768510b10b768510910b7585d0f10b7585d0d10b758519110b758518d10b758518910b758510b10b758510910b758504d21b3d85d0d40af68610b10af68610910af58610b10af58610910af58604d21aed87d8a629fb874c0309fb87480209fa809c6329fa809c5329fa801da329fa801d9329fa801d8329fa801d7319fa801d7219fa801d6629fa801d6329fa801d5629fa801d5319fa801d5219fa801d3219fa801d2329fa801d1219fa801c4329f9809c6329f9809c5329f9801da329f9801d9329f9801d8329f9801d7319f9801d7219f9801d6629f9801d6329f9801d5629f9801d5319f9801d5219f9801d3219f9801d2329f9801d1219f9801c4329f887419309f887419209f887411209f7874c4319f787484219f7805c6329f6878cb109f6878c9109f68784d219f687191109f68718d109f687189109f68710b109f687109109f681dda329f681dcf209f681dcd209f6819cb309f6819c8329f6819c2629f6819c2329f6819c1629f6819c1329f6819c0329f6811db309f6811db209f6811da329f6811d9329f6811d9309f6811d9209f6811d8329f6811d6629f6811d6329f6811d5629f6811d3209f6811d2329f6811d1209f6811cd609f6811c9609f6811c9409f6811c2629f6811c2329f6811c1629f6811c1329f6811c0329f5878cb109f5878c9109f587191109f58718d109f587189109f58710b109f587109109f581dda329f581dcf209f581dcd209f5819cb309f5819c3629f5819c2629f5819c2329f5819c1629f5819c1329f5819c0629f5819c0329f5811db309f5811db209f5811da329f5811d9329f5811d9309f5811d9209f5811d8329f5811d6629f5811d6329f5811d5629f5811d3209f5811d2329f5811d1209f5811cd609f5811c9609f5811c9409f5811c2629f5811c2329f5811c1629f5811c1329f5811c0329f5809c6329f5809c4629f487451219ee82dd3309ee829cf409ee821db309ee821d9309ee821d8329ee821d7319ee821d5319ee821cd609ed87c9b209ed87c93219ed87c93209ed87c8f219ed87c8f209ed82dd3309ed829cf409ed821db309ed821d9309ed821d7319ed821d5319ed821cd609ec87499329ec87499209ec87491219ec87491209ec8748d219ec8748d209df874c8329de83ddb219de83dd3219de839cb109de839ca619de839ca419de839c9109de839c8219de831db209de831d9209de831d7219de831d6629de831d5629de831d5219de831d3219de831d3209de831d1219d) else (0xcb10de52784b10de5265c632de5155cb10de5145cb10ddb325c031dd987cc230dd9325c031dd7329c632dd63784d21dd587cc631dcf37c8f21dcf37c8f20dcf378c832dcf3748f21dcf27ccb30dcf27cc831dcf274c831dcf265cf21dce839cb10dce829cf21dcd839cb10dcd265cf21db9205d020daf47c9321daf47c9320d9f47cd330d9e849cf21d9d849cf21d9d74cc831d9d744c831d79305d430d79205d420d75315d431d5d75cc831d5d754c831d3e849d431d3e845d431d3d849d462d3d849d461d3d849d431d3d845d462d3d845d461d3d845d431cf9625c062cf9305d830cf9205d820cf5315d831cef67c9b20cef67c9a32cdf67cdb30cdd76cc831cdd764c831cbd625d062c7d625d462bf38641110bf38640d10bf38541910bf38541110bf38540d10bf38441910bf38440d10bf38341910bf38341110bf38098910bf38094910bf38090910bf3808c910bf3805d510bf3805d110bf3805cd10bf3805c910bf38058910bf38054910bf38050910bf3804c910bf282dc110bf282c1910bf282c1510bf282c1110bf282c0d10bf28200910bf280d9110bf280d8d10bf280d8910bf280d0d10bf280d0910bf280cc910bf28099110bf28098d10bf28090d10bf28059110bf28058d10bf28050d10bf28019110bf28018d10bf28018910bf28010d10bf28010b10bf28010910bf2800c910bf186c1510bf186c1110bf186c0d10bf18680910bf18600910bf185dc110bf18580910bf184dc110bf184c1910bf184c1510bf184c0d10bf18480910bf18400910bf183dc110bf183c1910bf183c1510bf183c1110bf18380910bf18300910bf181c1940bf181c1930bf181c1530bf180d9510bf180d9110bf180d8d10bf180d8910bf180d0d10bf180d0910bf180cc910bf1809d910bf1809d110bf1809cd10bf1809c910bf1809c632bf18099110bf18098d10bf18095110bf18094d10bf18090d10bf18081910bf18081110bf18080d10bf18059510bf18059110bf18058d10bf18055110bf18054d10bf18050d10bf18019110bf18018d10bf18018910bf18010d10bf18010b10bf18010910bf1800c910bf18004d21bf08241910bf08241110bf08240d10bf08098910bf08090910bf0808c910bf08058910bf08050910bf0804c910bea80c9b20bea80c9320bea80c8f20be88048d20be68290f10be68290d10be68219110be68218d10be68204d21be681c9321be681c8f21be681c8d21be58290f10be58290d10be58219110be58218d10bda80cdb30bda80cd330bda80ccb30bd7814ca31bd683c8621bd683c8521bd6839cb10bd6839c910bd68395310bd68395110bd68384b10bd68384910bd68319110bd68318910bd68310b10bd68310910bd6818c932bd5839cb10bd5839c910bd58395310bd58395110bd58384b10bd58384910bd58))) else (if j<5 then (if j<4 then (0x60aff8458d60aff8258d60afd86cc960afd86cc560afd8698d60afd8690d60afd8650d60afd864cb60afd864c960afd85d9160afd85d8d60afd85d8960afd83d9560afd83d9160afd83d89609ff87597209ff87595409ff87595209ff8758f209ff8758e209ff8758d209ff8758c209ff855d9309ff855d9109ff845d9309ff845d9109ff835d9109ff825d9509ff825d9309ff825d9109ff815d9509ff815d9329ff815d9309ff805d9329fe87cc5609fe874c5609fd87d95309fd87d91309fd87d89509fd87d89309fd87d85509fd87d85309fd87cc9609fd87cc5609fd8790d609fd87597209fd87595209fd87595109fd87591309fd87591109fd8758f219fd8758f209fd8758e509fd8758e409fd8758e209fd8758e109fd8758d219fd8758d209fd8758d109fd8758c209fd8758b319fd8758b309fd87589109fd87551109fd87549109fd874cb619fd874cb609fd874c9109fd87499329fd87419309fd86dd5309fd86dd1309fd86dc9309fd86dc5329fd86dc5309fd86dc1329fd869cf209fd869ce209fd869cd209fd869cc209fd85dd1629fd85dd1609fd85dcd629fd85dcd609fd85dc9609fd85dc5629fd85dc5609fd85dc1629fd859db209fd859d9209fd83dd5629fd83dd5609fd83dd1629fd83dd1609fd83dc9609fd83dc5629fd83dc5609fd83dc1629fd839db209fd839da209fd839d9209fd839d8209fd81dd5609fd81dd1609fd81dcd609fd81dc960fe32098910fe32094910fe32090910fe3208c910fe32058910fe32054910fe32050910fe3204c910fd130cc910fd13098d10fd13094d10fd13090d10fd13058d10fd13054d10fd13050d10fd1304c910fc7329c632fc7328cb10fc7328c910fc7325c632fc683c8621fc6839cb10fc583c8621fc5839cb10fc53204d21fb37095110fb37055110fb25480910fb25440d10fb18095110fb18055110fb15480910fb140d0d10fb140d0910fb14099110fb14095110fb14059110fb14055110fb14050d10fb14050910fb10695110fb10655110fa94241120fa74290b10fa74290910fa6549cb10fa6545cb10f974390f10f974390d10f968395110f958395110f715059510f715055110f715054d10f715054910f695241520f355454910ef160d9510ef160d9110ef160d8d10ef160d8910ef16059510ef16059110ef16058d10ef16058910ee96241920ee76298910ed96341930ed76398d10ed56345931eb96441940eb76499110eb56445941e796541950df3215c221df3205c620df2809c632df2135c221df1819c062df1815c062df1809c632df1315c031df1305c430df1145c221df1065c650df1065c640df1065c630df1065c620df1045c620de987c8220de7875cb10de72744b10de7265c632de6829c632de6735cb10de6135cb10de587c8621de5755cb10de5745) else (0xddf3758e20ddf3758d20ddf3758c20ddd869cc20ddd865cf21ddd865cc20ddd76cd130ddd76cc930ddd764d130ddd764cb30ddd764c930ddd3758f21ddd3758f20ddd3758e60ddd3758e50ddd3758e40ddd3758e20ddd3758e10ddd3758d21ddd3758d20ddd3758d10ddd3758c20ddd374cb61ddd374cb60ddd36dd530ddd36dd130ddd36dc930ddd36dc532ddd36dc530ddd36dc132ddd365d130ddd365cb31ddd365cb30ddd365c331dbe7458c20dbd7695110dbd7650d40dbd7458c20dbd4759130dbd4759110d7e7558c20d7d7558c20d7d5759720d7d5759520d7d5759510cff7558d60cff6759720cff6759520cff6758e20cff6758c20cfd839d820cfd835d820cfd7558b60cfd67d9530cfd67d8950cfd6759720cfd6759530cfd6759520cfd6759510cfd6759110cfd6758e50cfd6758e40cfd6758e20cfd6758e10cfd6758d10cfd6758c20cfd6758950cfd674da32cfd674da30cfd6741b30cfd65dcd60cfd65dc960cfd65dc560cfd63dc560cfd635c361bfb8541930bfb8541910bfb8441910bfb8341950bfb8341910bfb8241950bfb8141950bfb8141930bf986c1530bf980d9530bf980d9130bf980d8950bf980d8930bf980d8550bf980d8530bf980cc960bf980cc560bf98098d60bf98090d60bf9808d930bf98081930bf98059530bf98059520bf98059510bf98059110bf98058e10bf98058d10bf98055110bf78759510bf78758d10bf7855d910bf78558d10bf7845d910bf78459510bf78458d10bf7835d910bf78359510bf7825d910bf78259510bf78258d10bf78159510bf78158d21bf78158d10bf78058d10bf6869cd10bf68694d10bf6865d510bf6865cd10bf68654d10bf587d9510bf587d9110bf587d8d10bf587d8910bf58759510bf58759110bf58758d10bf58758910bf58755110bf58754910bf5874c910bf586cc910bf5869cd10bf58698d10bf58694d10bf58690d10bf58684d21bf58684d10bf58680d10bf58655110bf58654d10bf58654b10bf58654910bf58650d10bf5864cb10bf5864c910bf585d9110bf585d8d10bf585d8910bf5859d910bf58585910bf58550d10bf583d9510bf583d9110bf583d8910bf5839d910bf58385910bf58381910bf58159510bf58159110bf58158d10bf58158910bf58155110bf58154910bf5814c910bf58058f10bf58058d10bef8549932bef8149932bef8049932bed8298d62bed8290d60bed8289932bed8259720bed8259520bed8258f21bed8258f20bed8258d21bed8258d20bdf854d930bdf844d930bdf824d930bdd86cd130bdd86cc930bdd83d9530bdd83d9130bdd83d8930bdd83d8530bdd838d930bdd8389932bdd8381930bdd8359130bdd8358b30bdd8358930bbd84cc960bbd849d562bbd849cd62bbd8458d40b7d85d8950b7d85d8550aff8558d)) else (if j<6 then (0x53758d10fd536cc910fd53694d10fd53690d10fd53654d10fd53650d10fd5364cb10fd5364c910fd53158d10fd53058f10fd53058d10fce6349932fcd6349932fcd3258f21fcd3258f20fcd3258d21fcd3258d20fcd2358b30fcd2358930fcd2348530fb94059110fb94055110fb90695110fb90650d40fb67655110fb65458d10fb64655110fb58755110fb57695110fb57655110fb554d8910fb5545c910fb55458910fb54759110fb54755110fb54655110fb54650d10fb54550d10fb54159110fb54155110fb51695110f9d4359130f9d3458d40f796541950f795059530f795059520f795059510f795055110f795054910f755759510f755755110f755655110f755654d10f755654b10f755654910f755159510f6d5259720f6d5259520efb6341930ef96341a30ef96341930ef960d9530ef960d9130ef960d8950ef960d8930ef96059540ef96059530ef96059520ef96059510ef96059130ef96059110ef96058e50ef96058e40ef96058e20ef96058e10ef96058d40ef96058d20ef96058d10ef96058950ef96058930ef96058910ef76759510ef76758d10ef76558d10ef76159510ef76158d10ef76058d10ef567d9510ef567d9110ef567d8d10ef56759510ef56759110ef56758d10ef565d8d10ef565d8910ef56558d10ef56558b10ef56558910ef56159510ef56159110ef56158d21ef56158d10ef56058f10ef56058d10eed6259720eed6259520eed264cb60eed264c960eed2648560edd63d9530edd63d8530edd6381930edd6359530edd6358530edd6341b30edd6341930edd36cc960edd36cc560edd3690d60edd3650d60edd364cb61edd364cb60edd364c961edd364c960edd364c560ebd6458540ebd4650d60ebd4650560e7d65d8950e7d65d8550e7d6558950e7d6558550df976c1530df97641530df97641520df97641510df97641110df97640e10df97640d10df906dd530df906dd130df906dc930df906dc530df9065d520df9065d510df9065d130df9065d110df9065ce50df9065ce40df9065ce20df9065ce10df9065cd20df9065cd10df9065c910df9055c910df5765d510df5765d110df5765cd10df5765c910df57645510df57645110df57644d10df57644910df5755c910df57544910df5639c620df5639c420df5635c660df5635c650df5635c640df5635c620df5635c420df5365c632df5365c630df5165d510df5165d110df5165cd21df5165cd10df5165c910df5155c910dee2748560ded7649720ded7649520ded7648f21ded7648f20ded7648d21ded7648d20ded2758b31ded2758b30ded2758910ded2754910ded274cb61ded274cb60ded274c910ded26dc532ded26dc132ded265d721ded265d720ded265d632ded265d520ded265cf21ded265cf20ded265cd21ded265cd20ddf3758f20) else (0x64c520fdd3648530fdd3258530fbd8459540fbd6550d40fbd4654540f7d5654910f7d5654520f7d5648550efd8258d60efd8058d60efd7558d60efd655cd60efd655c560efd6558d40efd6558910efd6558540efd6558520efd6550560efd6548560efd6458550efd635c560efd6358520efd6348560efd624c560dff855d930dff845d930dff825d930dff815d932dff815d930dff805d932dff724c560dfd8759720dfd8759540dfd8759520dfd8758f20dfd8758e20dfd8758d20dfd8758c20dfd855d930dfd855d910dfd845d930dfd845d910dfd835d910dfd825d950dfd825d930dfd825d910dfd815d950dfd815d932dfd815d930dfd805d932dfd7655110dfd7654910dfd7654540dfd7654520dfd7650550dfd764c910dfd764c520dfd7648550dfd7648530dfd755cd62dfd755cd60dfd755c560dfd7559110dfd7558910dfd7558520dfd735c560dfd7358910dfd7358520dfd655d130dfd655d110dfd655c910dfd635c910bff855cd62bff855cd60bff835d562bff8359540bff815cd60bff8159540bff8159520bff8158d20bfd87cc560bfd874c560bfd8654910bfd8654520bfd8650550bfd864c910bfd864c520bfd8648550bfd8648530bfd8348560ff36540d10ff36440d10ff30558d10ff30458d10ff28640d10ff28341910ff28058d10ff27641510ff27640d10ff26058d10ff23058d10ff21641510ff21640d10ff20640d10ff18640d10ff18541910ff18341910ff18059510ff18058d10ff17680910ff17641510ff17641110ff17640d10ff17580910ff17541110ff17380910ff16741910ff16580910ff16541110ff16540d10ff16440d10ff16380910ff16300910ff16098d10ff16059510ff16058d10ff15440d10ff130d8d10ff13058d10ff11641510ff11641110ff11640d10ff11541110ff106cc910ff1069cd10ff10694d10ff10690d10ff10684d10ff10680d10ff1065d510ff1065d110ff1065cd10ff1065c910ff10655110ff10654d10ff10654910ff10650d10ff1064c910ff10645510ff10645110ff10644d10ff10644910ff10640f10ff10640d10ff105d9110ff105d8d10ff105d8910ff1055d110ff1055c910ff10559110ff10558d10ff10558910ff10550d10ff10545110ff10544910ff10458d10ff10454d10ff103d8910ff1035c910ff10358910ff10344910feb2058e20fe92641520fe90649520fe90648d20fe52758910fe52754910fe5274c910fe52684d21fe52654b10fe52654910fe5264cb10fe5264c910fe52158910fe52154910fe5214c910fe51648d21fda6341930fd963c1930fd96341930fd936c1530fd93641530fd93058e10fd93058d10fd9304c910fd906cd130fd906cc930fd9064d130fd9064c930fd9054d130fd73758d10fd73158d21fd73158d10fd73058d10fd)))) else (if j<11 then (if j<9 then (if j<8 then (0x4986cc61b1e86c241af886b6e1ac106ac21a98869c61a4a868981a10867f619e58674a19bf8665819790657019378646018fb0638218cd862d6189d861e41868861601847860be181a05fe017e005f1617ad85e56178005d6e174605cd6172505c5216fc85b9c16d185ad21692859cc1658858f8161e8582415ec0574615b705686158c055d01559854fc15270543c14ed0532c14b585280148d051e814648512814280501813e904f3013aa04e52137a04d88134a04cd2131a04c1212ec84b5212bf04aa612850498c124d848d612228483e11fa0476a11b88465a11798457c113f8449e110f843ca10d5842e2109b8420e106b84108101b03fc60fca83e980f8683d9c0f4f03cc80f1503bea0ee003b200eb283a560e7d839960e41038720e04837c60dde8372e0db8836960d86035ae0d51035020d28834100cdf833000ca80322c0c75831760c45830b60c1082fce0bde02f180bae02e620b6c82d2a0b1c02bd40ad582aec0aa082a360a75829760a45828b60a180281e09ed0275e09c20266c09740257a0944024c409140240408ee0234e08b90223e08750214c083882082080881fb807d601ef807a101e2e077601d6e074601c90070201b8a06ca81ac0069a81a00066a8195406308183005ef0174805b781674058a015c8055a014fe05250145204fc8139204c00126e047701186044c010e404210103803fb00fa003d280ef403a780e48037c80d9c034a00cd2031f00c1202e000b2002b500a88028f009dc025f0093a02390088e0209007ba01de0071801ae0063001768058e0150804f601230042200df0031200a28021600688012e002e80000ff98541930ff98541910ff98341950ff98341930ff98341910ff98141950ff98141930ff98059520ff96541110ff90655110ff90654910ff90654540ff90654520ff90650550ff9064c910ff9064c520ff90648550ff90648530ff90559130ff90559110ff90558910ff90558520ff90358910ff58759510ff58758d10ff5855d910ff5845d910ff58459510ff5835d910ff5825d910ff58259510ff58258d10ff58058d10ff57655110ff57654910ff5764c910ff575d9110ff575d8910ff57559110ff57558910ff573d8910ff57358910ff56759510ff56758d10ff5655d110ff5655c910ff56550d10ff56545110ff56544910ff56454d10ff5635c910ff56344910ff55458d10ff5174c560ff51655110ff51654910ff51654520ff51650550ff5164c910ff5164c520ff51648550ff51648530ff51559110ff51558910ff51358910fed8549932fed8349932fed8259720fed8259520fed8258f20fed8258d20fed2654910fed2654520fed264c910fed264c520fed2648550fed2648530fed2558520fed2358520fed2348560fdd824d930fdd804d930fdd654d130fdd364c910fdd3) else (0x26450799417c5049940c6501c13fde4fd313ec44f9193dd24f5a13cea4f2013bda4ecf93aa24e86939a64e4c938c84e12937904dba936444d67935344d2b134244cf3933784cbe9329a4c84931bc4c4d130984c0192f604bbb12e784b7992d684b3a92c764b0312b664ab012a1a4a5d128ce4a0c9278c49c6126a449899259e494a924b64909123b048c512278487492122481c91fd647d611eb2478d11dc0474691c6a46e711ae2468a119aa46349185445e4116cc45939158045341147045041139244ca112d2449c911fe44651112a442b1101043e710f1443a310e0e436910d1c432510c2a42f290b4c42b390a64427210936422b907d641ce9069e4192105de415f90514412a9044040f59036c40ca90298408b901ce4059100fa401f1001c3fe50fee43f9e8fe1a3f6e8fd5a3f2d0fc043eeb8fb4e3eb90fa7a3e840f9ba3e568f8fa3e1f0f8263df18f7663dbf0f6923d8a0f5dc3d5c8f5083d278f4343cfa0f37e3cca0f2c83c9f0f2303c6c8f1483c2b0f02e3bf38ef323baf8ee0e3b5c8ed083b2a0ec343af50eb423aae8ea463a748e92c3a218e7ea39d60e6da39998e5f2395f8e514392d0e44038fa8e39e38d20e2fc38a70e228386a8e12c382e0e04e37f90df7a37c68dec437990de04376b8dd44372a0dc3436eb0db06369d0d9d8364c8d8a036088d79035c48d676357b8d57035440d4b035140d3be34d78d2e034a00d22034660d0f2341a8cff633de0cef0339c8ce0833650cd2a332d8cc5632f60cb5a32b98ca72327a8c98032430c8ac32018c76031ac0c61e31608c4dc31178c3e030d88c2f830a10c21a30670c13c302d0c0222feb8bf442fb68be842f868bdb02f568bd042f2b8bc622f030bb662ead8ba242e648b9282e2f8b8682e020b7622db40b6522d750b57e2d4a0b4dc2d218b4302cef0b33e2cb28b22e2c670b11e2c258b0042be18af082ba50ae202b660ad242b298ac322aed0ab2c2aab8aa302a6f0a9482a378a8882a000a77829b48a62229640a4fe29188a3d028d48a2d4289d0a1f6285e0a0f0281a09ff427dd89ef827a109e10275f89cec271b89bf026dc89af426a009a20266889938262e8983c25f20976825c7096b22592095ca2553094d82519093fa24e68933a24b409270247c891882447890be241788ff423e288f1623b008e74238c88de6236188d26233408c8e230908bce22de08b0e22b308a6c2285889a2224b888c42216887f021dc886f421a0085ee215e8850621270843c20f70836820bd082802080881982049080ba201407ff01fdf07f121faa07e3e1f7007d561f3b07c8c1f0d87bcc1edb07b0c1eab07a4c1e710793c1e2a878401df8077761dc5876b61d8b875a61d4a074aa1d0b073b81cd1072e41c9c072061c5f871321c2f8705e1bff86fa81bd486ee81b9f86e141b7206d861b)) else (if j<10 then (0x50200c280161ffe47fdc1ff107fac1fe507f799fd687f421fc9e7f0f9fbde7edd1fb0a7eaa9fa2c7e759f9627e409f8a27e109f7d87ddb9f7187da41f6307d741f5527d3a1f4887d029f3967cc89f2cc7c989f20c7c6b1f1567c401f0a07c089efb87bce9eed07b949ede87b621ed147b281ec407af59eb6c7ac31eaac7a909e9ce7a5b9e90e7a2e1e84e79fb9e78479c91e6ba79941e5f0795f1e512792f1e45278fa1e38878ca1e2be78951e1f478651e13478379e07e78051dfaa77d29ded677a29de2077701dd7477451dcbe77179dbfe76e79db2a76b51da7e768a1d9c8765a1d90876251d82a75f51d77475c79d6b475929d5d675589d4e4751e9d3fc74e21d31474af9d24074781d16c74431d07a74019cfa673cc9ced2739c9ce0873629cd3473379cc7e73079cbb472d29cad6729b1ca0272639c91072299c84671ef9c76871c21c6b271949c5fc71699c528712f9c45e71021c39e70cf9c2e8709d1c20a70681c14070381c08070059bfa26fcb9beb06f919bdf06f669bd4e6f3e1bca26f0e1bbe26ee09bb226eae1ba586e809b9c06e5a9b9146e321b8686e049b7a86dcd1b6d46d9d1b5f66d5e1b5186d2e1b44e6cf91b3846cc91b2c46c969b1fa6c691b1586c431b0b66c181b0006be81af406bb81ae806b881adb66b531acec6b259ac406afa9ab946aca9aac06a981a9f66a631a9226a309a86c6a031a7ac69d09a6ec69941a5be695a1a4cc69201a42068f01a37468c51a2b468951a1fe68679a13e68379a07e680799fc867da19f1267aa19e3e676899cfc672219bec66d419afa66a419a266662999166621197f265df996f665a3195fa655a194ea65251940c64e61932464a71923264721914a64331905863fb98f9863cb98ec4639698df0635f18d08632518bee62d998ade6293189ba6254188b4620b187ae61c71869e61859858e61469849c61029837860bc1826860759813060279800c5fe617f245fa997e465f6f97d365f2917c265ee517b025e99979e85e5d179145e2a978405dfa977625dc3176b65d95975f65d6a9754a5d3a9748a5d0a973c05cdd173145cad172545c7f9719e5c4f970e85c249703c5bf996f865bbf96e9e5b8816db65b5596cf65b2816c405afa96b8a5aca96ac05a9816a005a6a969545a3a968805a05967b659d3166ec5999165e6595a164d6591b163ee58e39631a58a99623c586f9614058309604e57f695f7057c415ea6578a15daa574b15cae570c15bbc56d495ad45698159ec565e1590e56291584455f41577055bc9567e5582955a05550154e0551b1540c54f01535654bb152825483951a45449950b2540f94fd453d814ef653a314e2c537314d58533e14c84530414b9252ca14aaa5290149d65258948e45219947e851dd146f651a09460e516694526512a1443e50f29435650b894) else (0xc02c0a22486c1483c0b00280c02c0a2248620c60500d030894208620f02c04904c0d02c8921b0520f02c0090981504c920340b22909c1b05c0f02c00d094182580e028882088120182540f02885208801c192540f02c85208801c182540e02885208801c1d04c0f2390b8260741502400a0641343c0b22a0981d054090028250600e0300b029896218761985611836098160100c82d0ac2909886014844090028300a82607819058130400b0220500a00343c2dc36074980549203c8a014022c3c2dc36074980549203c8a014022c3c2dc36074980549203c8a014022c3c2dc36074980549203c8a014022c468f83b8de310ac2a8941e06e18848110400d8288820929bfaa6fb29bdea6f4c9bc7a6ee69baba6e769b8fa6dfc9b73a6db49b66a6d8a9b5726d429b4a26d049b3aa6cbc9b2126c6a9b0ca6bf09aee26b629ac826ae89aa9a6a5a9a86269e09a6ca697a9a53269149a34a68909a13a681699f7a67a699d6a670e99b5a669e999c2662e997b265be9961a6544993e264c0992226450990b2641298f6a63c098e4a636e98cb262ea98aa2627a98932621e9877261ae985da61349846a60d8982fa60909818a6048980925fec97efa5f9097d8a5f2a97c425eec97b225e86979b25e52978925e00977725dae976025d48974425cd8972fa5c7c9718a5c3e970925c0096f9a5bae96e525b7096d5a5b1e96bea5ad696aca5a8e9695a5a329683a59e0966f25998965d259509648a58ea9627a58669609257f695f2257a495d8a571695b7a56a695a0a564a9589a560c957a255d8956aa5590955da555c954e25500952fa54909518a543e9501a53e294efa539094d8a532a94bca52c494a5a5268949125216947ca51ce946aa51869458a51349444250f69432250ae9422a5070941324fc493cf24ebe939524df4936024d0c932624c2e92f3a4b4692b224a54927fa498a9240a488e92042479c91c7a46aa9188a45a49149a449e910aa43b690ce242a69087a41a0904b240c29013a3fc68fd4a3eb68f90a3dba8f5423cc88f1523bb88ec9a3aa88e882398e8e41a389c8e0ca37b48dd2a36cc8d8c235a88d45a348e8d01a337e8cb8a325a8c72231688c3fa308a8c0322f988bc6a2e9c8b8a22daa8b48a2ca48b0722b948ac322a7a8a86a29a68a4a228a08a10227ea89e2a272a89b02264289712255a893c2247c89022238a88c0a22708877a217e8847a20c88812a1ff487e7a1f4887b021e248773a1d64873ea1c9a870c21bd086d9a1af2869fa1a288665a192286292182685e52172085a8a162485712155a8541214ae850ea13c684d4a12e8849d2120a845e210f08412a0fae83cea0ec6838aa0da2834e20cc48316a0bc882cda0a90828ea09bc824d208b68206a079c81bda0664818120590813fa049e810fa03c080c92029c8094201dc8))) else (if j<13 then (if j<12 then (0xb0a809c25c230721885210a05010c208621484c0b012014033082188521302c0480d8290749c04c920440f23909c2307c1702c00f0d8260649804c920340b22909c2307c1702c00f094182580e028882088120182541223c0a4270721482200a0609503c0a2148220070d8192541323c0b4270721482200b0649503c0b214822007060950380a2148220070541303c8e42e094160340900281504d0f02c8a8250580d02400a05c168521384a1083e0e227082198561083c0b01421484a10838894158420f02c00a05c168521184089c20866158420f02c04d05e138460f2250561083c0b00280e2248821d8641584c0b00240a2248821d8641584c0b0024250480b028892208761985610a03c89220876190561302c00902c89220876190561302c0090300b02889c20866158420f02c04b0300a2250561083c0b00200c02c0a224866158420c80340c227082198561083c0b01280d02c894158420f02c00804c920440f23b09c23076190561302c00d04c920340b22b09c23076190561302c00d04c920340b22b094190561303c0b0030250600e028886198420881241223c0ac27076188561082200a0600f029862158420880201323c0bc27076188561082200a0640f02d86215842088020180380a6188561082200805c168521384a1083e0e2270821883c0b0138170561484e128420f838892190520f02c00e05c168521184089c208620f02c04b05c1584e1183c892190520f02c00b0a01203c0e2248821d05c0b0028250480b028892208741702c00a0941202c0a2248821c70a41303c892208741702c0090981302c892208741702c0090480c02c0a2270821883c0b0128120300b028892190520f02c00a0300b028892188318140340c2270821883c0b0124130340b2248641483c0b0024360a41d04c920440f23b09c230741702c00e0d826064132480d02c8ac2708c1d05c0b0038262941504c920340b22b0941905c0f02c00e094182580e0288820881201223c0ac27072148220080609503c0a2148220070d81323c0bc27072148220090649503c0b214822007060950380a2148220070941202c0a0240801c70390861c8621484c0b01200a421872188521302c0480480c0298861c86214842010421872188521302c0480310861c8621484c0b01200b0290861c8620f02c0480300b028896218721b0520f02c00b0300b028896218721883200d0310861c8620f02c0480340b2258861c86c1483c0b00282604c920340b2290962187c1b05c0f02c00e094180380a6248861c82204903c0a6258721482200703c0b625872148220070380a6258721482200704810039082188521302c0490480c029082188521302c0490480c02886214841814041082188521302c0480500c4208621484c0b0120120300b028894208620f02c04a0480) else (0x8a41502400808c1c0681684a0e832082198480a0130200721484a1083b082188521183c0b0134200621484a0c82b082188521183c0b01361484a0c82909c230721885211832e148420c823072188460e02804a0801a0621484a0c82989218852118332148420c820862118380a0126148420c820862118380a0125224811a46109c230721885211832d224791a823072188521183c0b012c2207a14843082188521183c0b012c2206a14833082188521183c0b012e1283a0c820862118380a0126128420a820862118380a01242a060120441023c8e8320b82989c218660f02c0500a4180481103c8e8320b8298961b0560f02c00f0b01404c122408f23a0d8320b82909c230761983402a068120441023c8e8360c6270861983c0b013c29064120440f23a0d82d8961b0560f02c00e0a01203c0e2248821d86c1583c0b0030250480b028892208761b0560f02c00c0941202c0a2248821d8660c90a41303c892208761b0560f02c00b0981302c892208761b0560f02c00b0481003b082188521183c0b0128120300ac20862148460f02c04a0300a42708c1c862148460c90480c02989218852118321224811a46109c230721885211832c14043082188521183c0b012414033082188521183c0b01242904c920440f23909c230761b0560f02c00e098132480d02c8a42708c1d86c1583c0b0038250600e028886198320881240a4270721583208801c0f0298921583208801c0b4270721583208801c0f02d8921583208801c0e0298921583208801c260961384a0b82a0881c866158420cc09e148420c81c866108380a01282784a0e832082198420e02804a0960881c862148418272960881c8621484c0b0124440a02708e1484a1083b082188521302c04e1102a09423852128320ac208621484c0b0138430b025852128320ac230721885210c8521083208c1c862120280491142809c25852128320a21885210b85210832082188480a01202585210832082188480a01242c2a02709708c1c8621484242729608c1c8621484c0b0124440a02785210c208621484c0b012c440a8258520cc208621484c0b012c2584a0a8220721885210809e148420c81c8621202804909e1283a0c8208621202804984a1082a082188480a01203b0aa250789c060120441023c8e8320b82b08c0b0144290749c0481103c8e8320b82b05c0b00343a0b2250809c050130489023c8e8360c82e0a42708c1d20ec2a89c1e270120441023c8e8360cc2302c04f0a41d270120440f23a0d82f05c0b0030280480f0388922087c1702c00a0941202c0a2248821f05c0b0028250480b02889220871c2904c0f2248821f05c0b00242604c0b2248821f05c0b0024120400ec208621484c0b0124120300ac208621484c0b0124120300ac23072188521080480c02886214841837)) else (if j<14 then (0x5208801c3604c8f02f09c1c852088024192540f02c85208801c182540e02885208801c3809a250661825c110410f02e0a22185208816010098132440b82a0981d8520881600b0500d0310b428898208620e02804b0a0190481003c0e4350ba2686c1683c0b0038130440f2390d42e0981b0580f02c00c0a01203c0e42c8922087c1702c00b0a41303d0b2248821f05c0b0028250380b02889220871c120390cc208621484c0b0124140410cc208621484c0b012429074130440f2390d42f09c2307c1702c00e0288921d0540900180a4208620d0240460288941483409001825061160408e029084090124184540f2380a4150240080e828070120400f03a89a1b05a0f02c00d0440f23a0981b0580f02c0090a01203c0e2248821f05c0b00282904c0f2248821f05c0b0024120400ec208621484c0b012414043082188521302c0480d829074132481103c8ec2708c1f05c0b00382c04c1243d0e2248821c802c8921d0540900180c4208620d02404602c8941483409001827069160408e031084090124194540f2380b4150240080dc25060120380c02c0a2025060124400b02a8982287c0b012c25060124400c02c0aa2708a1a83c0b013426066160410f02c8a8230580a01c00c09c1a0400c22b098230780a012827060100308a82306c0e02804a0981985c1143c0b22b08c1602c07003025062160400a8220280480941243c0b0288922087c1702c00b0981343c0b2248821f05c0b0028124400c02b082188521302c04a0480c02b08c1c8621484202c45112c230721885210805110033082188521302c0490480c02c0a2270821883c0b0128120300b0288921b0520f02c00a0500d03089c208620f02c04904c0d02c8921b0520f02c0090981904d0f0340b22b09c2307c1702c00d0981504d0f0340b22b09c1b05c0f02c00d0488f02b09c1c8520880201323c0bc27072148220080390b224874150240070390b2250520d024007065150380b229054090020250601202c0aa2608a1f02c04a0dc25060120300b02a89c2286a0f02c04d09819858132481002c8a8230580a01c00d09c1a050920308ac2608c1e02804b09c18050920308a82306c0e02804b0e0260661704c9202c8ac230580b01c00d094188581202a0880a0120250480b0288922087c1702c00a0981302c8922087c1702c0090480c02b082188521302c0490480c02b08c1c862148420370b0a809c25c230721885210a0500cc208621484c0b01200c02c0a2270821883c0b01240c02c0a22486c1483c0b00240d03089c208620f02c0480340b22486c1483c0b0020360981904c920340b22b09c2307c1702c00e0981504c920340b22b09c1b05c0f02c00d0488f02b09c1c8520880203604c8f02f09c1c8520880240f42c8921d05409001c0f42c8941483409001c194540f02c) else (0x2002004a0e0260661804d0f0300b82985209803026065160420f02c8a4230540901c00c0e026065170460f02c8ac1502c00b0e4274941a460122380d0310b42a0880a01381d064984450d21c86c148340b002c2904c9203c8e4348921f0540b002c2604d1102c8a22487c1502c00a02c8a42086c148340901c00904c0b2288921b0520d02c009094180491002c0aa2488a1d82604b0941845c1183c0a6230540981c00b0981945c1183c0b6230540981c00b0981945c108380b22988c1502607003025060108380c02c0a62182604a04c8f02e0ac2508c1c8520981200b0649503c0b829882148260480281323c0bc2508c1c8520981200a0649503c0b620852098120090649503e0e02e0a6208520981200b0a0120390d22487c1502607002825049110288921f0540981c00a094124400b028892208760981282c04c12445104350c2248821d82604c0a41303d0d22487c150260700282604d1102c8921f0540981c00a0940e02c0a2248821d82604902908c1c86214846098120124400c029882188521182604a4510c42307218852118260490288962086c148340981c0090300b028896208620d82604902c8962086c148340981c0090a41d04c0f2390dc2508c1f0540981c00d0981904d1102c8ac2508c1f0540981c00d0981504d1102c8ac2588c1b05c0d0260700381223c0ac2508c1c8520981200a0609503c0a6208520981200904c8f02f0942307214826048028192540f02d88214826048024182540e0298821482604802438098192601383c0c02c8a42305407003438098192601383c0d0300b22b0540b00341d0649805c150208721b0520d02c00c0a4132481103c8e2240821f0540b00302604c920340b2288902087c1502c00c04c0c02c8a2250821b0520d01c00b04c0d0300b2288921b0520d02c00b094180480c02c0aa2488a1c90dc250601283c0c02c0ac1502c00b0e0260641383c0d02f0540b00283809819260128380d2300b22b0540b00341302e0981c85208801c360641323c0b82b09c1c85208802c380649503c0b8288520880241904c8f02f09c1c852088024380649503c0b21482200804c0b82a0981c852088020380649503e0e02e0a21482200a0a01203c0e2248821f0540b0028250480b0288922087c1502c00a0941202c0a2248821c70b0130488922087182904c0f2248821f0540b00242604c0b2248821f0540b0024250380b02889220871c120300a423072188521080480c028862148418370b0a809c2528d08c1c86214842c120300b0288921b0520d02c00a0300b028892188318130340b22486c148340b0024360a41d04c920449003c8ec2508c1f0540b003c360981904c920348c02c8ac2508c1f0540b003c26054132480d2300b22b09c1b05c0d02c00e0488f02b09c1c852088020182540f0288))))) else (if j<23 then (if j<19 then (if j<17 then (if j<16 then (0x2c00d0a41d04c120440f03a89a1b05a0f02c00d0a41904c1003c8e8320b6270861b0560f02c0700403f0a41904c920441003c8e8360b62586c1583c0b00442904c920440f238890208761b0560f02c00e098132480d02c8a2240821d86c1583c0b00383b0a41d270130400f23a0c82f08c1702c07003c290749c04c920441003c8e8360bc1702c00e0a4132481103c8e2240821f05c0b00302604c920340b2288902087c1702c00c09c1a058122380c0200200490e828070120400f03a0d82f05c0b0030290741c04c1103c0e8360bc1702c00c05a1484e1083c89c210561083c0b01c00d0749805c1684e1183c894158420f02c00d0741926017020874158420f02c00b2481103c8e2240821d8641584c0b0030130340b22889020876190561302c00c0300b22889c210561083c0b01c00b04c0d0300b228894158420f02c00b05815852138420f227082190520f02c0700381d260170581584e1183c892190520f02c00e07419260170540821c8641483c0b00302904c920440f238890208741702c00c098132480d02c8a2240821d05c0b0030130300b22889c208641483c0b01c00c04c0d0300b228892190520f02c00b09c1a058122380c02002004906417056138460f0240641403c0b00300b2290861c86c1483c0b01c00a04c0d02c8a2250861c86c1483c0b0030130300b2288942086c1483c0b01c00c04c0d0300b2288921b0520f02c00b09c1a058122380c0200200490941202c0a0240801c70e81c0541203c0e02c05008002837060150480f02c0a01402000a098192581043c0b8288861482205803027068960410f0310b2218520881600c0941243c0b028892208761582600b0b0130490f42c892208761582600b0940e02c0a2248821d856098028120390dc208621102c058024124440ac208621102c058024120300ac23072188521182600a0490f0300a218852118260090b02744d0d42f08c1c86214846098030140410f437082188440b01600a051110310bc208621102c0580280a227082198520d02c0580240c02c0a224866148360980240c42c89c20866148340b01600a094182580e02888614822058028278941a860960400c82888208812c27068960400c2208220480941202c0a2248821c70b013048892208718250380b02889220871c120400ec20862148440b0124120300ac20862148440b0124120300ac23072188521080480c028862148418370b0a809c25c230721885210a05010c20862148440b012014033082188521102c0480480c02c0a227082188340b01280c02c0a2248620c60500d03089c208620d02c049094182580e0288820881202904d1203d0e2248821e0580a002c2604d1202d0a2248821e0580a002c130340b4288921a0520e02800a0a01c058120400e0300800801282506016048100300a) else (0x2403f0f0360c82107c1d06c1905489a1e86416834090314ba0e0360b42b0a42107c1d04c1103e89a1d0540910c82f0841f0741b06415a248601684a0d0238c50b42b0a4a80841f074130440fa1805a11023c2107c1d2701b06417054130440fa268641683409007419260170540821c864148340900302904c920440f238890208741502400c098132480d02c8a2240821d054090030920440f238892190520d02400a04c0c02c8a227082190520f01400b04c0d02c8a2248641483409002838098192600f2380d02c8a41502400c09c1a058122380c0200200490d826064136480d02d8aa268781602800d0e026054136480d02d8aa26868168380a003838098196600f0340b62a0580a002c362609243c8aa268741502400a2dc152490f22a89416834090028b72611503c8a4150240080d81904d0f02e89a1d054090028380541343c0ba2505a0d02400a0e0194540f02d0540900201243c0aa26874150240080490f02a89416834090020184540f02905409001c380651503c0b4150240080a41904c1003c8e4310ba2708a1b05a0f02c0700403f0a41904c920441003c8e4350ba2686c1683c0b00441d26017055134350b0208721b0520f02c00e0a4132481103c8e4350b2240821f05c0b003827068160488e0310a02002004a094160491002908a1a83409012825061160400a42102404809c1a458100300a4210240490ec29074132481003c8ea2708a1b05a0f02c0700402907413248110400f23a89a1b05a0f02c00e07419260170540821c86c1483c0b00302904c920440f2388902087c1702c00c0480e42e89a1d054090020120390ba2505a0d024008065150380b41502400709c1a4581203108409012025062160400a8220280480dc25060120400c02c0a82202804b098198581043c0b22a08c16028070030380981985c1143c0b22b0580b002c1d06416451134410f227088168420f02c07003c1d0649805c1644d1143c898168420f02c00e098198581043c0b22a08c16028070030380981985c1143c0b22a08c160280700341d26017055134450f0208721b0520f02c00e0981343c0d02c8a2240821f05c0b0030130300b22889c2086c1483c0b01c00c04c0d0300b2288921b0520f02c00b0dc25060120400c02c0a62182604b09819858132481002c8a8230580a01c00d0e0260661704c9202c8ac1602c00b0741926016227088168420f02c0700301d0649805c1622605a1083c0b002c260661604c9202c8a8230580a01c00c0e0260661704c9202c8a8230580a01c00d07419260170540821c86c1483c0b00302604c920340b2288902087c1702c00c0300b22889c2086c1483c0b01c00b04c0d0300b2288921b0520f02c00b094180490e0300b02a89a22872837094180480e0300b02880e828070120400f03a89a1b05a0f0)) else (if j<18 then (0x1683409003c382b02b2801b064920440f0340b41502400e09819058130400b62808814020060030b70641303c0b62a89a1c05008002c380641303c0b62a8601684008002c382601303c0b62a8901683008002c38064152480f02d8a01402000a2dc980549203c8a0140200090741944d0f42c8921d05a0d02400b04c0f42c8921d0540900201302c8921d05409001c1303d0b2250520d02400804c0b2250520d0240070e0194540f2380b4150240090749844d0f42c89a1d0520d02400b0d81d04c9203c8e42e89a1d0540900303c054132480f2390ba2505a0d02400c0741944d0f42c89a1d05a0d02400b0d81d04c0f42e89a1d0540900283c0541303d0ba2505a0d02400a0749844d0f42c874148340900289203c8e42c8921d0540900241302c8a224874150240082480f2390b2250520d02400902c8a227084148340b01400904c0b22889414834090020380651503c8e02c8a41502400a0f0380d81d0641303c0b62587a1805a1002000f0e03604c0f02c8961c05a0c02000b0f0380d81d0641303c0b6258701402000d2f8b72c4ac294a006c982480d2298961e0580a00403c2dc36074980549203c8a6258701402000e0c02a08c1e068140400c021860158400801800f2dcb12b02b294a006c982480d229860158480a0040300781a058140400c021868158300801800e074190541303c0b226870158300800303c074190541303c0b624860168460c02000e0f01d0641504c0f02d89015830080030be2c4a006c9805c920348a625868158380a003c3c0d81d260152480f229890158300800342a078160501003c0c0220500801800c0741303c0ba26870140200090741303c0ba1805a100200090741303c0ba2405a0c0200092dcac0aca006c982481103c0d22a0580a003836074152480f2280500800241d0641504c0f02e09a1c05c0c02000c0741303c0ba26870140200090741303c0ba1805a100200090e0360b42b0a42622487a1805a1102400d314380d8320841f0741b0648921e86416834090040380d82d0ac2904c1103c8921d054090034360b42604c0d02c8921d05409002c1d05c1504c1103c892190520d02400c0741905c1504c0d02c892190520d02400d0a41d064130440f2380d02d054090030380d82b0440d2248741402400a0741905411034892190520c02400b0a41d05c1303c8e035050090028380981905c130440b22905009002e3789618848100360a22082241d0649805c15226872190520d02400c0a41d04c920440f23a89a1d0540900301d0649805c1522405a1083409002c1d04c920440f23a8601684409002c29074132481103c8ea2686416834090034380d81303c0b2248701402000a074190541303c0b2240520c02000b0741504c0f2380b014020009120c530c380d8320b42b0a426a2687a1805a11) else (0x300b029892218754300a8230781a05010030086190561002007003c300781a05915050100300861b0560c02007003c2706a160380c8220280480e81c0541203c0e02c0500800282706a160480e0320880a012425060104380c02c0aa2282a04a0e427068122380d0320880a01282807016048100380c02002004a094180408e0300b02b08c0b0128250600f2380c02c0ac1702c00a094180380c02c0a183b0a82507818048110408f2380ac2302c04e098192600e0340b22b05c0b002827069160380c22908409012427069160480e0308a42102404a094180480b0298942187c0b012826066160410f02c8a8230580a01c00c09418458102380a42102404909819858132481002c8a8230580a01c00d0f8380dc310b02609420064130480a6250861f02c0510dc180541203c0b0280500800280c02c0a2270821883c0b01240c02c0a22486c1483c0b00241003c0e22486c1483c0b00242a060120441023c8e8320b82989c218660f02c0500ec2a8941e27018048110408f23a0c82e0ac2302c05109c1a4580e03108409012027069160480e0310840901243a070150480f0380b01402000a0dc180541203c0b0280500800282807016048100380c02002004a09c1a4580e03108409012027069160480e0310840901261283a0c820862118380a0124230701a05a1283a0c8208660e02804c0961282a0881c8621484202785210832072188480a01242784a0e832082188480a01242c0982584e1282e0a0260881ca0a82708e148420c0260780a01282809c2305a1283a0c82202804a0941202c0a0240801c70e81c0541203c0e02c05008002837060150480f02c0a01402000a0a01c058120400e030080080128250480b0288922087c1702c00a0941202c0a2248821c70a01203c0e2248821f05c0b002827069160380c42102404809c1a458120380c4210240490941202c0a0240801c70941202c0a0240801c70bc1d064170548961e868168380a003029074130440f6258781602800a0f0380d8320b42b0a426a26876180561202800f0f01d0641705689218056128380a00301d04c1103d860158480a0024380d8320841f0741b06489a1d868158380a003c29074130440f625868158380a002c3c0e0360b42b0a42107c1d04c1103e89a1e0580a00443c0bc1d06417054130440fa26868168380a003cb7294982480d22a89a1d05408a2dc982480d22a860168440892dca5260920348aa268641683408b2dca52609203c0d229054089110300a82708c1f06c11036860168400900383d0c01e068160440da26864168300900343b0a81e05c140400f03505009002c3909c1a05c140440c02d05009002cbe2dc320b4260841b064130340ba26874150240100e0b12b02b2942106c1904c0d02e86016844090040be2c4a006c9805c130340ba26864))) else (if j<21 then (if j<20 then (0x6c1906017054130340b2260520e0280100300b22889c2086c1483c0b01c00b04c0d0300b2288921b0520f02c00b0641684e1082e084158460e0280700311d0641685210832084158460e0280700341003c8e2270821b0520f02c07002c920441003c8e22486c1483c0b002c1d0649805c1644d1143c898168420f02c00e0741926017058898168420f02c00b314c30e0320b42b0a426a26872180521102400f0c8290982107c1d06c19a248601484a0d02400f3142d0ac292a02107c1d04c1103c86014844090040380c82d0ac262942106c1904c0d02c86014844090044380c82d0ac260942106c1904c0d02c860148480a0046380c82d0ac27098a584e0d82c8601484c0b003c380d82d0ac290988921e8601684408c314380d8320841f0741b0641522487a1905a0d0240380d82d0ac2904c1103c8921d05408c0e0360b42604c0d02c8921d05408b314c30f0380d8320b42b0a42621e860168440900403f0f0380d8320841f0741b0648921e86416834090044c53043c2e8380d82d0ac290841f074130440f224874150240140fc382dc360c82d0982106c1904c0d02c8921d0540900483f0e0370d8320b4260841b064130340b22487816028012098132480d02c8a2240821f05c0b0030451043c0ec3a0e0360b42b0a42107c1d04c1103c8921e0580a00542904c920440f2388902087c1702c00c118420ec3a0d42e0ac2a0881f07814044102240821e0280530fc3c0e0360c82f0841f0741b064170540921e0540e02801307419260170540821c86c1483c0b0030421003d0d4330c02207c1e06c1a05c160240821d0640e0280541144410c3c0e0360c82d0ac29098874180541202801149518059120410a0200200494dd180551203d0a014020009098192581043c0b828886148220580302a07816448106380c02002004a04c0b82a0981c8520880202604e120340b82a090220724278941a860960400c82888208812c2807016048100380c02002004a0e81c0541203c0e02c050080028300781a058140400c0218660c02004c0f0380d81d0641303c0b62587c1805c1002000f0e03604c0f02d0961c05c0c02000b0f0380d81d0641303c0b6258701402000d0f0380d81d0641303c0b6258701402000d0f01d0641504c0f02d8901583008003037060150480f02c0a01402000a09819058130400c02c8a0230500801c00d09819058130400c02c8a0230500801c00d0dc25060120300b02989221872825060960410e02888208812529474160510f6380c0230500801c00c4a51d0581443d8e03008c140200700302506016048100300a02002004a0c02a08c1e068140400c021864158400801c00f0c01e06816050100300861b0560c020070038260641604c100300b22808c140200700343e0e0370c42c09c260942006819050130480d0) else (0x561302c00c0e0370cc2e09e148230761a82a04b0f0380d82b8460d8218641602a070030390dc320b4264961361885a0a802c2c096122248821d8641584c0b002c2d09a132248821d8641584c0b002c3e0dc2e0b42c44b08c1e86a16842c3c0d82d0ac2944d0fa1a05a1302c00c0dc220842044e09c2307a1a8328360841f0751382707c1683c0b002c360b42104d0f82f09c1f05c0b002c380dc2e89c220530982307a0a812c380d82b07c11837098230580a81c00c0e4370b42104d1282f09c1e85a0a80302c04c128288922087c1702c00a04c0f82c8921e0580a00202d04e0b2248821f05c0b00241203e0a224878160280080f0380d82b4450d42307a1a05a11026070038470d81f06d114360942307c168340981c00e0e0360ac1f0450dc2508c1f0540981c00d11c3606d110370942307c15026070030b7294982480d22a89a1d05409002cb7260920348aa1805a1102400a2dca5260920348aa2686416834090030b7294982480f0348a41502400a2f8b70d8b12b0a52801b260920348aa26874150240b72c4ac0aca52801b260920348aa1805a11023cbe2c4a006c9805c152480d22a89a1905a0d023cb72b02b2801b260920440f0348a4150234290741904c1103c8e0340b415022c29074132481103c8ea2687415022c1d04c920440f23a8601684408a0a41d04c920440f23a89a1905a0d0230c5304ba0e02d0ac290841f074130440fa26874150240123142d0ac292a02107c1d04c1103e860168440900402107c1d2701b0641704c1103e89a1905a0d0240100e02d0ac210741b064132481103c0d02d05409004025060104380c02c0aa2282a04a098192600f2380c02c8ac2305c0b01c00d0e0260649803c8e0340c02c8ac1702c00d0dc25060124380c02c0a2025062160400a822028048098198581043c0b22a08c1602807003025062160481002a0880a0124260661604c920400b22a08c160280700342706a160480c82202804807819059144410c42005a128340901400d0c02a09c26059144410c422860168440901400f2f8a006c9805e928368a624056118380a00382107c1d2701b0641784e1183d890158460e0280100741926017054890168420d02400b0c82f0b42b0a42621805a1102400badcb12b02b29498a4a0da29860158480a00381d06417054130440f2248641483408c0741905c1504c0d02c892190520d02301d0649805c15226872190520d022c1d0649805c1522405a1083408a0fc3c0c82f0841f0741b0641522687414834090040320bc260841f0741b06415224860168420d0240100841f0749c06c1905c1504c1103c894148340900403f0c82106c1926017054130340b2250520d0240100fc3c4e1360841f0741b0648961c05a12834090040c54e1360c82d0ac290988961e8601684409003c3f0c821)) else (if j<22 then (0x3a0d82d0a409020078170024450e8360841d8540902007c00a0e8360b41382c0902007c00930c370c42c09c2544a87a1a05a1302c00d314c430c32475198268781a05a130230c430c380c82d09913a1e8681684c08c2e8370b0200501304a0f42a89a1f05c0b0038360741303d0ba268741502400a2ecba0e02d0841383d0ba2687c1702301d0480f42a89a1d054090024450b42b0a61383d8641584c0b002c470ae11836086190561202c07002c2107c1d84c89a1f0560f02c00a11c1f06e11834898230560e02c070030470ac1f0460da2608a1f0580b01c00c120380c82d09913a1f0681704c0b0030380b42104e0f42e89a1f05c0b002c4706e110368982287c1602c07002c480ad1143488c1a0540981c00a0b92708814a2488a1d8260490ac1f0450da2488c15026070028380b42104e1243d0ba268761582600c0a41d04c0f8370982307c1602a070031384d82b07c118370982307c1602c00c0e8360b42944c8922087a1a05a130230450e8360841d44c8922087c1683c08c10c360b42684c8922087c1905c08b0e8360b41382c8922087c170228430e0360ae118348921f0641602a04c0e8380d82b0460d22487c1602a04b0e829074130440f23a0bc2705c08b0e8290741303e0dc2608c1602a04b0e82904c920440f82705a0f0228370c42c09c2544a8681702c00a120380c82d09913a1a05c089120471102b0911143608a1a05408b1043c0841f0751322705c08911c3d0f01f06c174450d22608c150230370b1250801304a8982287c0b012c370b020050130490aa2705c0b002c360741303d0bc1905c1102400a0d81303d0b82505c0d0240090d81d04c0f42e894150240090d81d04c0f42e898210540b01400b0ec390b92708814a2608c0890e02d08413a2705c08711c3b0ac1f0450da2608c150228360741203d0aa268741502400a0e82c89c2004c12a2608c0b01283a0b020050130490ea2705c0b002c470e43806d110368982305408a0c02f0901f06c174450dc208681502302b09c260901b4440dc2286815022c3a0e0370ba270510942107c0b012c3a0dc2d04d0942107c1702c00a0ac1b45c1404c1183c0dc2305408b0e8370b22504c1282c8922087283a0d81303e0b2248781602800a074130440fa1a05a1302c0090a4130440f22705a0f02c0090a41d04c1103e0b62587c1702c00b0b227080130498922282a0490a41d04c0f835892230580a81c00b0b0200501304a0f82d89a1682a00b0a41d0481103c8e8298961f05c0b00301d0480f23a0b6258781602800a0a41d0481103c8e82d8961f05c0b00301d0480f23a0a6258781602800a0dc330c83188209c20866168328480d832876198248641683c0b002c3e0dc2e0b42c49612c230761985610c0f0360b42b0a613c1d8641584c0b0030480d8320b42684f07619) else (0xc61d864894218721a05c0b0030c530cba0b4ac0ac292a2134228681702c00e30cb70c82d098a584d08a1a05c070030c30e0b70c82d098a584d08a1a05c0b0034c12e8212801f0749c84c8942305c0b0034ba2dc2d084132498942305c07002cba0e0b70b42104c9262508c1702c00c314c30c8b187619020872190561283c0b0038c30b4ac0ac2984c89020876190561302c00e30c2d098a584c89020876190561302c00d30c382dc2b8460d224876190561202c00d30c380ac278460d2248761905612028070038b42a0212801f0781d2721383e892190561302c0102e82d2b02b0a5132240821e8681684c0b0038c52e8212801f075132240821f05a0f02c00e2e82d04c9282c8902087c1702c00b2e8382dc2b0460d22487c1602c00b2e8380ac140460d22487c16028070030ba04c0f82c8921e0580a00244430c2b09c234450d022868150240700343d07c1b068164450d22408c150240700343b2e82b07c1404410436890230540901c00e0e4b706d110340ca2408c150240700303008c1f06c1a059114350821a0540901c00e0ac272942306d110340c422868150240700382b06d17050920441083c0d03108c1502407003cba0d81d04c0f42e898210540b01400c2e8360741303d0ba268741502400b0f8370b82d0b02584a8861890e0370b82205110032892218128390dc2d084138490f02e89608a0dc2c04c1223a0982207223c0a4132481103c8e82707c1683c0b0034370b0130480a2248821c8120370c42c09c258170020c30e0370c82d0982581700243b0dc2c0801304a08c0b0124370b0200501304b001cba0dc2e0881404a08c0b0124ba0e0370b42104c1242f0024410e82d0ac290a20f4170024450e82107c1d0720f22700243b0e8380b42104c1283d0bc00a0a4130440f03889c0070e029074130440f03a0bc0090e82d0a4282248821e05c0091143a0841d0708922087c0090e82d04c122248821f00203a0e02b044102248780b00243a0a41303c0e2248821f00243a0b01304a0a2248821c80e81303c8921e0580a0020410e82107c1d07089c0080e8380b0200501304b00203a0e0b70b42104c1243f0026380a41d270130440f23a0bc1f05c0b00342c2a02709708c1c8621484242c2a0202701404c1223c8e42708c1cc104ba0841f0741c4540940f0028430b4262248821d054130024430e02b224874150480b0024410e82d0ac2981d05c0081143a0841f0751502607c0090ec3a0b42104d0b81f00203a0a41d04c1103c8e41f00243a0a41d04c0f2390780b00243a0d82904c0f2380902007c00a0e82904c1103c8e02507c0091043a0841f0749c02507c0090e8370b4134250841f00203a0dc2d0841324907c008114430d8328540801c864170028430d82d0a60f0240801d05c00a10c360b42682c09020074170028)))) else (if j<27 then (if j<25 then (if j<24 then (0x890e0360ac1f0449043d0780890e8380d82b0451023c0901e02283c0d82d0ac2983c0580080f0380d82b0a42683608a1d860158480b01800f0d81f0741b0660d22608a1e0560e02c0600383c0d82d0ac298170480080e0360ac1f04c1103e0da2608a1e0580b01800f0d8320b4268170480070f0380d82b22205c100280090e0360ac1f0460f2200280090d81d04c0f0140200070d82d0a50f2248821c054009114360841d43c892208740090d82d09889220874170440090d82d04d0f2248821d0020380d82b22487417040090024380d82b0450f224870090024380a41d04c1103c8ec1d0024290741303c8e823070090024360a41303c8e8260881d00242904c1103c8e8270740080d82904c0f838892208740090d81303c8921c05008002048114c30d82d0ac2943c05400a120c30e0360c82d0990b01500284830c360ac290990d82287a1805a1102c05003c3c0d81f0741b0641543489822874168340b0140100ec360741303d0b8210540b01400b2e8360ac1f04c1103d0da2608a1d0540b01400f0bc1f0741b064154368921805a128340b01400f30c2b4450da1a05a110220ba0ac1f0460f43689a1f05408a11c2b8460d821864158480b0028c12e82d2b02b0a61383e08a1d8641584c0b003c4707c1b8460d22608c158380b002cc530c322c51d46489820868168460f02c00e314ba084a007c1d84c8982287c1583c0b0038470ac1f0460da2608a1f0580b002cc30b4ac0ac2944e08a1e8681684c0b0034470e01b8440da2687c1602c00a30c380c82d098a544e08a1e8681684c0b0038ba0e02d0841324a0f42e8982287c1702c00e30c2b09d1143408a1a05a11024070030ba0b8220510c0210240482e82b07c140450da2408a1f0540901c00d2e8360741303d0ba268741502400b0a4132480f23a0d62587c1602c00b04c920440f2398942187a1a05a1302c00d4e1b70ae118358961e868160229386dc2b0460d6250861f05808a0b4ac0ac2984d8942187a1a05c0b0030382dc2b4450d2240821e8681684408c11c1f06d114348902087c1683408b0e0b70ac114348902087c150228474440d2240821f05408811c4430c2b09111436868150228470f41f06c174450d22705408a11c3b2e82b07c1143689c150228470e4382dc1b4440da2705408a0c02407c1b05d114368921a05408b8e02b09ca50901b4440da1a05408b8e02b06d17050920460f03705408b2e8380a41d04c920440f23a0b6250861f05c0b0040ba0a41d04c9203c8e8358961f0580b0034ba0a4132481103c8e2240821f05c0b0034ba074132481103c8e42187a1a05a1302c00e2e82904c920440f2388942187c1683c0b0038ba0b02004c1223a0c02202804a2e829074132480f23a0d6240861f0580a01c00f2e836074132480f23a0b6258781602800d30c322) else (0x460f0340c02d02c0700342c080130480c22187a0480e0b60b020050130480b61c90dc310b0260940a4218720374d8310b0270940a61e0524370c42c09c260940a61c80e0320b4260940b61e0520370b025080130480a6250861f02c04c0dd360b020050130480a61f02282e0881404a100310861f0124380b42104c1283c0b61c80dc29074120440f2390aa1f0228360741203c8ea1d054090024380a41d0481103c8ea1c80d81d0480f2390aa268741502400b0741203c8e8298961e0580a00282c8942004c126250861f02c04a0741203e0a625878160280090f03a0a4130440f22705a0c90e8380a41d04c1103e0bc0890e9360841f0741303c89c1683283a0e02c0801404c1203a0b627022c3a0e1360b42104e1203e0b627022c2c4942004c120410aa2608a1f02c04c0dc2c0801404c1203d0aa1f02283a04c0f826074150240080d81d04c0fa1d0540900201303e09a1d05409001c360741303e874150240080741303e08a1d054090020ba0b822050120410c82287c04a0e02d084130480f42e8720ba0ac1f0441003e08a1d02241d0480f42a89a1d0540900243a0e02e050108310942107c04a0e82d04c0f82d0942107c0891153a074130440f61e05202904c1103c8961c60e0b70a41d04c1103d87202c080130481022187a0480a41d04c0f2218780870e0b60b020050130480f61c90841f0741c8540f22587203a0b02004c120398942187c04a0e8384d82c0801404c120398961cb0e8290741303c0e4218780890480f42889a1d0560d0240094d81f06d11434894218781684a0d02303c4d82107c1d8701584e0f0270580cc075150480f42a874150240090841f0741c0550f2268720c907c1b05c16054898228720d02281d0480f42a876190561102400a0741203d0aa26874150240090dc310b0270950aa1c0521090e0320b4260950ba1c052109110c30ac2408e08a1c0521102283c0d82d0ac292a20f81d05242c0950a2248821e05a1080b4262248821e05a10704c0f224874150240070480f4288921d0540900201203e0a224878160280080d81d8541203e0a81602800910c370b42682c090200741490e8360b4292248821e05a10910c360b42682c892208741490dc310b0270950a21e05a1090e8360b42b0a50f21e05a1090e0370d8320b42642c87816842847110c30d82b0208781684408a11c3607c1b2240821e8340890d81d04c0f21d0540900203604c0f024874150240080d81d04c0f21d054090020360741303c8741502400811cba0d82b07c1183c0821d0228360741203d0a2248741502400a120430d8320b42682c8741490e8370b0200501304a0e42887283a0d81d04c0f8388741502400a0e8360741303d0e21e0580a00283c0d82d0ac292a1074158424360c82d098a541d0561080f0380d82b28d074158480)) else (if j<26 then (0xc8821e02243a0d81d04c0f4388781602800a0e81d04c0f224878160280090e8374d829074130440f23907283a4d8290741303c8e02107808a0e9360a4130440f2380941c90f03a4d82107c1d2701303c0941cb0e8380b814248104250841f01283a0b4132480f4250841c80e82e08814248104250841f01283a0e1360b42104c9203d0941ca0e9360ac1f0449003d07808907c1b05d150248821d0380890f1360841f0749c02507c1483283c4d81f06c172580941c83808a10c2d098252248821d05410910c380ac232248741504808910c382dc320b42621d054109110430ac8821d054120220450d81d04c0f8168480a0024454e8360b42b0a40f81684800a0e1370d8320b42602e05a120028470d82b421878168400a0024470d81f06c172250861e8300a002c1d04c0f42005008001c470d82b07c1183d0861c02800a11536074130440f61c0540090a4130440f2258740070e1360a41d04c1103d8740090a41d04c0f221870090020380c82d09a2502d8701500242b09223421870168400900242107c1d8701503c8961d00241f06c17858152250861e83009002c360741303d870140200080d81303d0961c050080020360741303d870140200080d81d04c0f421870140200090e02d084138480f02d8740090ac1f0461003d0861c0240090e13606c130360c02d0861c02400b0ac1b04c0d8300b415840090028470ac244218781684008811c1f06c172250861e83008911c2b07c1183d0861c0220470e01b0440d82d0861c02c00a11d360ac24021878168400a0128474d81f06c172240861e8300a012c474d82b07c118420f0218700a012c474d81b0440d8320b0218700a01c00c0ac2406c110360b4158400b00282b0902306c110360b4158400a01c00c0741303e0b6248861e0580a81800b0741203e0a6248861e0580a81800b04c0f82d0941e0580a0021450d81d04c0f82d87c1a05c1202800c04c0f82d0961e05c0e0280090d81d04d1203e0b6258781602800b0741203e0a625878160280090dc2c89420050130490e8320b829892218738360741303d0e82d8961e0580a002c2b09023421878168400901241f06c1705a152250861e83009012c2e08814848100310861d01242b07c110420f4218700901241b0440d0320b4218700901c00a0ac2406c110340c82d056100240700313606c1302e0880a81c0080dc310b0270940a8168420380dd360c82d0980b81684242c0801304a10029894230124370b0200501304a0f02989c08a0e4370b82205210031894230128380dd360b42104e1283c0b627022c2c080130490e0328982287c04a0e02c0801404c124380ba268728382dc1b04c0d0300b8228740b002c2b098a506c130340c02e05a1102c00c0e0370b8148400c4250841f0128370b41383c0b4250841f02242b06d1704c92) else (0xd07c1b06817058890228720d02404c0c01f06c1a05c164450d420868168420d0240700401f06c1a4450d2250861e05a128340901c00e0841f0741c44d0f2270520c92e82107c1d0711504c0f0270540cb114430e0360a4262248821d060150480a00384530c2d0ac2943c052110024c30e0320b42642c0521100244430c2b0a426822872180521102400c07c1d06c194450da2708218052128340b01400f0e02b098a506c130340b2180521102400d110c30ac24a1c8440870c02407c1b4450d21884a0d02c00b30c322c42909a1d2250861c8601484a0f02c00f314c30b4ac0ac292a20f421870148430c30c82d098a582d0861c05210a30c380c82d098a582d0861c05210b110c30ac27090230228721102404b30c370c42c09c2542805210930c380c82d0982542c0521090d82904c0f438892208780090e8360741303d0e21e0580a0028360a41d04c1103d0e2248781602800c0d82d0a50f2248821c054009114360841d0550f2248821d0028360b42602c89220874150024360b41343c0b2248821d0024c30f0360c82f4548781805400a114c30d82d0ac2943c870150028c30d8320b42642c8701500244430c360ac2909887a1805a1102400c0d82107c1d43c8921d00203607c1d06c192248741683409002cba0d81d04c0f21d054090024ba0d81303c0921d054090024ba0d81d04c0f21d054090024ba0d81d04c0f0208741502400a104ba0d82107c1d4540921d0028ba0d82d0841342c8740080ecba0d82b07c130440f2248741502400d0e0b70d8320b42621d0540090e0b70d82d0841343c8740090e0b70d81b04c0d02c8921d054090030c30e0b70ac242248781684408a2e8382dc2b0460f2248740892e82d2b02b0a4a883c89020874158430c30e02b09c232248781684409012cba0e02b050110420f22487409012cba04c0f224874150240080e0b70ac242240821e05a1102281f06c172240821e8340880e0b70ac1183c8902087408911cc30ac0821e05a1102204707c1b2240821e83408811cba0ac1f0460f02087408930c2d2b02b0a4a883c89020874158430c30b4262960b2240821d05610a314c32e82d2b02b0a60f020874158430c32dc320b42682c0821d05610a30c382dc320b4262960b0208741584304430c2b09c0821e05a1102404a07c1b0688902087a0d0240490ecba0b822050104300821d02404b0ecba0ac1f0501183c0821d02404b2e8360741303c874150240092e8360741303c8921d054090028c30dc360c42c09c2542887814a30c370c82d0982542c8781490dc2d04c9202d0942107c0890e0374d82d084132480b41f0228380dd3606c130348c02d0780b002c3a0b4290a10f2248821e05243a0e02b0441043c8921e02243a04c0f22487816028008114c30e82d0ac290a10f21e05283a0ac1f0441043))) else (if j<29 then (if j<28 then (0x980b8160020384d8320b4268940b0150024384d82d084138480b4090024390e0b706c130340ba1d02c00a0ac27098a506c130340b8168440b00302b06d17050132481183c0d02d02c00c0e5370b02004c120300880a0128b70c82d098a502d0861e05a10a0e0b70c82d098a502d0861e05a10b2dc2d0841324a0f02d8942187c04b0e0b70b42104c9283c0b6250861f0230390e0b706c130340c02c08a1d0240700342b09c262941b04c0d0300b8168440901c00e0ac1b45c1404c920460f0340c02d0240700382e0881484810031084090124360a41303d0e2248821e00243a04c0f224878160280081143a0e03604c0f2248821e0580a00313a0d81d04c0f8160280081153a0b42b0a40f8160020ba0741303e084150240080ecba0ac1f04c1103e898228741502400d0e02b06c1945c132481103c0d02d0540b01400f4d82904c1103e0e2250020384d829074130440f8380b400a0f1360841f0761c04c0f2250028384d82d084138480f62500242107c1d8701303c8641584400a2e829074132480f23a8740892e82c080130488e430084090128ba0a41d04c9203c8e02287409012cba0d81d04c9203c8ea1d05409002c3b2e82b07c1103e8740882e8382dc29074132481103c8e82d0861f0238ba074132481103c8e42187816842cba0a4132481103c8e2250861f05a0cc314ba0b4ac0ac292a00f421878168430c12e8212801f0749c04c0f2250861f05a0ce2e82d084132480f82d8942187c04b2e8380b42104c9203e0b6250861f02303b2e82b07c140441003c08a1d02404c2e81d04c0f822874150240092e8360741303e89a1d054090028370b0130490e2248821c81143a0e0370488922087203b2e82c080130481042a89823012cba0dc2c0801404c1203d0aa27022c3b2e82e088140481043289823012cba0e02d084130480f42e89c08a0e0b70b020050130490e02e89c08b0e0b70b42104c1243c0ba2702282b06e1704c120441043c0d2300b80a81c00e07c1d06c1905c1522608a1d0520d02400d07c1d06c1905c154450d224860168420d02c0500413607c1d06c19434894218701684a0d02c05003c3c4d82107c1d870150250580d002d386dc2b4450d22587a1a05a11022cc1084a007c1d84e0f22608a1d0561183c0b003cc50c8b1074194218721a05a1083c0b0034322c4300ac174450d21a05408a07c1b4450d2250861e05a1283408b0ad114348942187a1a05a110228320b4262961382c89822876190561302c00e8e0320ac2705e138460d82d864158480b003a38adc320b4262961382c89822876190561302c0100f41f06c172268720d02203007c1b05d114348921a05a1083408c0c8b1074192250861c868168420f02c00d084a007c1d2721383c8942187c148330212801f0781d2721383c892190561083c0b003c3) else (0xc314c12e83604c0fa268741502400b11cb706c110368a6250861e0500a0030470ac110350861e868168400a002c4707c1b05c1103489421878168300a0034470ac1f0460f035894218781402800cadc2b0901b0440da29860158400a00302407c1b05c1103689218056128300a0036b70ac1b05c1103c0da2a0500a002c470e0360440d2248781402406002cb72c4ac29692a29876180561202800c0c82f09a1d8661522587218056128380a0038c50b42b0a42684e0f61d860158480a00342107c1d0661383d8961e0560e02800c2dcac2809203e8a6258781602800b0d81d2480fa298961e0580a0028360a413a481103c8921d05409002cc530c380d8290988921e86016844090034c52e8380d81303c8921d05409002cc50a42107c1d0661383d89618056118380a003c2904c920440f23a89a1d05409002cba0a41d04c920440f23a89a1d0540900342b0440d422868168400901800a07c1b05e150440d225088168300901800d0ac1f0460f035894220500901800b0912307c1b05e150440d420860168300901800f0fc384d829074130440f02d8961d054090038ba4d8290741303c0d6258741402400c2e93607413a481103d87a1805a1102400d0fc3c4d82904e920440f22587416834090039360a41d04c0f0358902187414028050034360741303c0b6258701402000a0ac240440d61e860168400900283c07c1b05c110348961d05a0c02400c0ac1f0440f0358961d050090028384d81b04c110340b6258741402400c0f1360c8290981d0648961e8601684a0d02400f315360b42b0a41303d87a1805a1102400d0e1360c82d09aa504c0b61e860168440900383c4d82107c1d04c0f22587416834090034384d82d08413a480f02d8961d054090035360ac2488c110340861e860140280500343c4d81f06c1785811034890218741402805003d360ac1f046100358902187414028050034384d81b0440d8300b6240861d0500a01400e0d81d04c0f421870140200090d81d04c0f02d8961c050080028c50c81d066872190561283409002c2d0ac2904c0fa26876190561102400c0b42604c0ba26876190561102400b07c1b05c110368921905612830090030380ac1b04c110340b6190561002400c0c81d06689a1c8641584a0d02400b3142d0ac2904c0fa1d8641584409003038adc320b42604c0ba1d864158440900342107c1d04c0fa248641584a0d02400c07c1b05e160440d820864158400a01400d0ac1b0440d8300b821864158400a01400d3042107c1d4541303c89a1d0560d02400d0a42107c1d4541303d8921805a118340900382d04d0f02e89a1d054090024380ac1b05c1143c0d02d05009002c38adc2d0841343c0ba268741502400c0ac1b05c1143c0d8300b8210500a01400d0741203d0aa26874150240090e1370c82d0)) else (if j<30 then (0x144440da1d0216380511103502144730c0821e05a11021c472e81183c0821d021c3085c8641602143809e0d4160214c58748641441103085c8641602184409e0d0210580868a58921a05101404c1183602143b050130460d8086314c10a41d2258641474d81102002204522508a1a05408509e2603508408509088814305e06081484c0d421021411220203488c14021011034880c30492892190540860e63809d240350218398e0144440d408630c370b02510370490e21c430c370950a10c30dc260950b81462e8370490a10ba0dc130490b14390e0270990881460360208390e01404d08c08603602080d22305808404e1103602100d80820368880830e0130440d80850e8b704c12103a03c8740041161d21905103805013423021411808204c11808303688808330c2f02406815031a1d414205e02083809c2642040908880832210580830e83704c92103a0d88e4004120430d82941450e8360a60f414511c360210580850a50508390e027098084146416020888416020d0580820e105808341a0208470d811022021411808204c118083036020a3a8da0f415841636225830e3604d0b0e3a221810e3a409810e3a8dc13849801536846020c370950a0c3c0c82f45440e02642c30dc1242830d80f40030e01342c30d80fa1d0010481142941584144811c440ac24415841c410f01d2258314470f43c05c8960c611c3b0450f10480e02642c40e01342c311c390e01b0350b184811c440ac24409811c3b0e4142218114470ec1140981143804d800c8942286815021626035020d3c89024e224808385c184c110350211388442836020a0d80820b21261031202983d056105120474158480a811924a248641448e124035021126a22020c470450f80a8116384440d0d13a22020d45874864144512172190511448350841602153b04c1183602163a0b21261048ea0f4158412430b112a10430d1d81838ea0f4098110c345e060cc3435020cba435020c3a03c8e0c3b044900c2709908c0843120d80832f705081404d08c0842ee0d08b9c16020cb984428e09480830b42b0a42684e0f625876180561202800d3142107c1d0661383d8961e0560e02800d314360741303d0ba1d86415844090030c104c0f42c89a1d0560d02400a0a4130440f625878160280090d829074136481103e8981602800b2e8360741303d0ba268741502400b0e02b0440d62587a1a05a1002800b0e02b0460f0358961e0500a0028ba04c0f42c8921d054090024ba0d81d04c9203c8e42e89a1d054090034380ac110358961e868168400901800c0e02b0460f0358961e0500901800b04c0f02d8961c050080020360a41d04c1103d8961e0580a002c4830c3c0e0360a426a1d860158480a00343c2e8380d81303e89a1e0580a002c48314c30d82909a87a1805a1102400) else (0x4830c360a405144830c360160214ba0d82903e05143603d0e21c42e83603e0210470d8888140214470d8112200214c30d8260150016172248601602143c22508a180540860980d42102101781820348809050413035084084034880838414204c112203075050a892190540840e02603505408503505083804d11035021447110c30ac24408611c3b2e811408511c4430c2b092084158420470f4172260860c630c8921a0560c511c3b2e81143e0818470e4b706c0d42e081cc32dc262950b81462e8b704c9242c52e83603d0010894228681502162603508408484c110350840850c124a1c864150218274900da1d0540860c124a2486415021a3809d240350214))))))
def genIndex8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (0x74cc1e897f8a2b40442ce1f80078000d93d1a43c7f082651228107780061dd31a65c83a1f2a13138345002505cf85115ec78004966201d3621016b218a25a201c8057ff9ce7099b18e58ea38907800451bf8002809d8d6cce70033a1fd49fe28698db0f800018ed953a0bd58b254bb0214f80059e7b0287800586a909d5005a20361e1a0db59c25408780018f5912b51b539e0f80be5fd4083707d22309120e5f1780078006deff19378007800497e8043f800721f8c30813ac085780060e449e9bc1f5c600132f80070c6ac330065f800387e190b40799a199130a8963c5278004a27589dba1c780078007dddf8006dd4b5d209b5f8007800520391e121e8701f185b9000e85de4c4cd5789017800780071d3856000cb69d49df74501ac79f8002100f80061ac89e74e097800503778006146091409bf7800018b1980e4f15473c981c12a99dc61ff780078007800780078007800383ae80f983978004db69c667800609bc977f80021610905f9e97800383d648f216078001d96589ef80078004cdc01527800780009079927f8003cd07a26da0cb98c5ce3316451a70910c8090ded7c87d4946845813e780070d3b5c5f8003dcead04780061d5a40b78006d8cf80070c5b828916871fa755ef1cc084b35131192215840d7ba0f50a39484586368877800780008c8780030eae21acc4b780061f3780069b6c1f1c1c625d78d26208fa229f800610570a91444f8007800081bc92758b69d5dde0891a0f800780064b978007800780060a789a9d9a3780001b1a8b710a0f80078001983a152c0b1e9cd7800201af800497c613a78001568780050afa58324d9e5e37800392df80078007a08a8dff80058764823049c397d71f5f8007800462678007800723588f07800780078001c61f80028cae0cd3055248ae5c7f80069f075f0f80058b9b08df1f171fee11d68f199da7800617a81203438400080851420019022858b047ca020c0c3145a040010c9d1040600f41040003308001bf0800101221c090122c00206183800220301020410c100000b08091a40008000060469d023c0010060a0c280948f04040000e141800c9820306188ad0024782028030c001c4870c000062800008181409200b402500080050200106060448a083010e0000c020000005040c0810014002122400100441070004089000020d0809304001c5870001007034d78d00001030e0018004000010a0c48c100060102241830618507101838008d8401002c0802214593081061e08207880e04c8902085070290138001028000080852a0021108000064c00182082c0040000282500801102041010c002000600289000400a06100860014085000000026004000e0c0000c0400c0a000000408302301000400100010e001800604101000408500000050200005001828b0000584) else (0xcb384cf0bf8a23780078000017814dd0c91961a8d1a041916ff80078004482b1ac7165b11e16057800780078007800304ff8000db340fb7800449169bc491a01707800780078007800414e78007829f81378007a21f8003212a13bf80078007800653bf800780069ec85baf8003c22b9b9a982c015ee2d40fa2e29f80010dd095b2113d0cbd148f800780078007800780078003ca4780024a2980370e254db7800780078007800780061a1f80051880824f80070d28a16a480f800312cf800780078005c92f80041cacdc578007800694139c45032861f35aa1e02f800780078007800588cf80049a278007800780078007859c1487800244aaa072609bddeb21df80078004e07fd3178004837d4b8193978007800408921baac11f8006012019f78001231f80054c380d37800780029cff8007800110de0c8f800780031f9a19b8a1360b60d6bf80078002108c0211e0b11dbb47695beb0687db1c07459d275a1780011c0f8003e1599be7800780078007800780070e0f80078000c1cf8002831c8b0f988f80050b30112ba2bcc9b19d8f800411158bc780075d8f8005c33f800721a780011db351d19f91c748571c8114854780031440cdff95738a5f800780078007800422ff8007800780048f359d978001917780001771949a21b003cd41c78002a25f8e6d027287d80c72e14780078003187cdd1160ff80000c7f800217f508a780068623df658cd9875a0628c85201979af802084bfc89584897068d9d7714c017df800780059b7780078007217f80078004892506089c6ad692832697b6db0389cc583d96add251939f8007800449bf800780078001917b1d078006993f800184ef80078000030550df800107a30a8780028cce0003047893678001e27e025780078002e2df80078b2f8f17800306f780051e5384af800522db56548e9780021092a2278003820780078004de7221709b078002c28a10429cb780041d860d5748fb97bf8002da778047800780078007800780014e659621a180c9fa600a206f8001e04cdaaf800213b780079c5197a3207e0c25c9558679622f8006162f800780078007800780011cbf800780078a34066522ee0da612bf80030e610b4c8f0fc82780078002db7602af800393cfc91f80055cd91bbc924608450990d8829282889c014fd5cf800780031ae9d64a8b8360ac07c08a778006890d4b5d116419ee406f8001a13d134f80078007800780078004c5501c1d03878000c6f18534830f80078007800688aa909900a51c8c85fd8fef800707cca0058df01cdb8ae5a1f6919b806e052c8ad7011f8007800780030f61813c86c3116890e78004a19780061e6f8007800780078002818455ff800598ff1d086071dbf7800780068477232e1e5e0f6b88120f81cc4022c89aba4f1a5a7e1e370d9b5a5520c78e771)) else (if j<3 then (0x147cde780040a99ca5c15a3cfe28ed8849780078002606b614f83b2a2040c39dedb07ab98541a7b0c31c633cb8f80049515205b9b29223f1598042696e75d1c07790d4f169f800099fa23328082e18f852094b61dadc256507fd5308abc0a4390378007800780078001824780070b07800780071217800502581a579fcf800590a780049af7800780078006c0598ba7d03420e78007800780078007800780069f8f8001080281c8929e5dd780078005914b44e04d6f800780078007800250ca9325a267800202ff80078006cb6f9e4bc7cf800780018a8ae2e158c7800780000ec4426f800780078000205705b015df80078007800093df80015a1b94cf80050c651e3c0d458a6b0f921fbe9a8b1f2187b7d46f15bb115f8003887f800487ede0ef18739e2345ef80010292979780078007800694e98c4f800119e09bdf8007800780078001e1c446211d600c428c5300b19a4b9fda83df8ee7155f800718bf8007dce780038ef29e47a11780030ed7199bd7e308c1e21f80019137800204878000cdae5bbf8000e1d780001b67800780078007800780058ebb0f42076f5a0f80025a3f80078538cda78000164aa278d44d511a20af80065dc78007007e0e07800780019b17800620940de40d5a073f8003019b963f80078006805413eec8338017800486e619af800780059aaf80008ecc57109f5560261c2e9ad9208589c483ba20df8007800208ef80030d07800780078007800780078007800611bf170f147f8007800780024078d9878003042a9f7f80078001c8718887800780078002dcff80070947800611de9fc156af8007006780078005485a1b47800780078007800296c6157b14fe8b11854f800780078007800409844d5f80078007800780078001cd79dead02b88ab095041a6f8007800620272106085f8007800780032098956010b981ecd027800780028d97078001d9c4ff8007800780011bfd807616d0522f8007539a1957800780024a0692e7800780061fb78004871f8001d03f800493848b8943f3a33b5c0e1237800760df8001072b94d780078000450b1ef78003c34f800780051b3e94538cc78007800780001d3780039de1129414078007800780040eb78005a247800780018f38055f8007800780028f9cda8600ea859605e2e15505a15d5f8002cc728b5e9cf7800718df800581e10e1405f609781b48d3df8007481086bf80019438884c8ff78007800780040e4f80045a5f883f8007201e48678002158f80070f55880f800656fc0977800304a4983780028aed0147800090ed12a40ace1ee9944f80078007800780020c9a54430c078007800512ef80078000d4cf8007800600d896ba587362a780078007800197278003937a08f399dc96310f77800780029eaf800394f780060e28234982230a2e086f80078002202fd) else (if j<4 then (0xe311787800394a2926c601512550dec9f3f5340103dc43e003ccba68be7a20f800585aa878e8732a10f80070ff9960f174295378005df6d018f80009ceb850cc677800780061019d98eda8ec46f8d8f800088b506d780068566111f800396f78007800200aa427f80078007800780071949ca3a173f8007630f464c8f8d87701e06a1cf9c969a82c67d008b023f488fe1638507800000f290c780038e9f8003575cce279907800702e61d7c004f82f41c37800780050952d2f904c78005a254972f8007800286f95e23845306558bb71b9298f40916d52f94bf80078007800701c161bc016fa04f800415f407140cf59f40c4d9429f800392481bd399478b578004844c9dc984bd08e78001836b95cf8007182310cb96939c3f800703ff22c5490bdb67800185c7800295ed18cf8001d2d780078001133f8001c18f800621e48eef80019e8b19179756a15d0c1a81a7950f9ebf80034cf4971a8f7adb2cc3d78003870f800780048b4460f0a35780078005c68a06a715d251e80e589f4cd7a6db8b036780078007800609b78001128f800300d6154c222993355aff9a39989ddc49d4348e1b4b7c135c1d9c18d28757800790d2c4eb002f1d6b951ca1271a2f1c0722a082db8bac0fdf800780078007800780029557800312d78007800780051beca21780078004e085184780011ea78007800780049bb21e2a83e78007c737800780008697800704d81def800693d5a047800582189b89181616da140810698229156f80078001d6e780078ac7800589f2848dc3c6858d89a1166881b69fff8005234780071dde893b91869c7c0fe78000229299b515e7cf3f84659a175a4f8002c275a18a504c05ef80078003c8a01238063b02d78005175f800189882283cbc45b9520141468cb991c9f80078007800003c012629e6021bf800613c780011193ca4f8006839f8006418182ea409c9d1780044a6f8003556942eec8df80010ce7800780078006976d8bf7800780058a0780078005a0bf8001176123178001cbf24dce0335881f80078002c4bf80078004064f80078001902780070d86121f143188be15c591b78000200e070212f7800202cf8007ce4515a8131d60625cf7894d9b23866f11ad17311ab7800780048e854f2780078007800780006175125f80078006587d19cf80054515118fcc84db3d80cf8fc9c3bf8002d3a780041d1fd0d2091f8006057f8003ddcf800751e5c2930a21e1978005168e992e16ef80078005995d0eff800758b7800521d29858060422f780078000a0b20bdf80020f2f80078005c7ef8001dbb0a0a00b3c02c1ca6780058fd242840a630aac8577800780078007cbd78007800706100c1699819543e1ef800559319c4f80041aa78e7a5497800711cf800648d60db81375936f8007800416a3a0d093f11ec6180582b1a) else (0x780039c7217111b0f80001ed00fac5c069c5b5eb499c3cb63c3e20a1f8007800200e78000a15710f28bbb1a9480c5d6378002a24a06e960e4206780078005d48f800780070cef80059ae70173dae78007800780005cd7800397e780078000cd878006997780058fc5cf2e20ec465f800780079d57cdeb049b07ba1f77800780078007800780058e5691078005096f800383ef84e7800780078006079283f7dd87800780078007800780078005c326d72f80078000979c09af80078006578f80078002197f800780078007800780010587ca26996a967295ff8007800202a780078007800780011f84840f80030dac082191eb067780058102902f80021f6f80009a5f800780010cfa98aba2e74bec07fc0d63142f8005dea780026101c7771896c31f800320ff8001d63f8004ca16a2d00c2f80011ede0b7da167d02f8001991f800348c78006d087800259e6986f8002893798664174dd6bc62b22ae1126ce2f800094af8002d7c780078005945809ff80070ca20b978003d3fc01088f2186c987260ddf8007800111520a5780064ddf8007800780021007800554d6142045ff984f80068bcf800780009b819c17800780039967800711c29b7a0404092f80078004051f8002846e5b2780078d0bd2cf800115978001a1ef417f800407f3dc1f80039ccc178801298350dee0cc7dd3e8d41b9faf80065955034c84f3484f0e8c056f800780000adf8006463b03a286d81f08d61f80039087800780078006cb7780078000a3201f618dc112c780028d741ee780054a52c45fa11f1207e1c99d288f4e0d21826b47d1035d167d9ad18436546799d693ff8000c9af80011d47800780069227800010af800780078003d32f80044540481a84d090604b2ed270015780030e3d888d477f8007800408d791f116c986b7800101fad6c01bc9cdbf80029eb780010c0e838f800780001357800780051342904c1ba4061b86418a13dde29491d82f800780069df81306daec88608beea28e1df7619f80058163165219a6938a1990d89ba304882dce5000198d1780078003cb54074f8002c5078001c80780058a4d998e48ef8aa64c60990c55e7c2ae11ff8002027b9b339477800780078fb841291eff80049ca190ff8007800497cf8317800458af80078007800780070af78007800489e1c2a1141f800292f805d204131a0780030dcfd7f60))))
def genData9 (j : Nat) : Nat := if 17 ≤ j then 0 else (if j<8 then (if j<4 then (if j<2 then (if j<1 then (0x5cc2febae437f5d720bfaeb885fd7598afebacc37f5d641bfaeb195fd758c6febac437f5d520bfaea885fd7518afeba8c37f5d431bfaea10dfd74cc6feba6617f5d321bfae9905fd74c42feba4c57f5d261bfae9305fd74942feba4837f5d240bfae9195fd748c6feba4617f5d221bfae9105fd74842feba2617f5d121bfae8905fd74442feba0637f5d030bfae810dfd74082feba0217f5cf62bfae7b0dfd73d82feb9e817f5cf21bfae7905fd73c42feb9cc57f5ce61bfae7305fd73942feb9c837f5ce40bfae7195fd738c6feb9c617f5ce21bfae7105fd73842feb9a437f5cd20bfae6885fd7318afeb98c37f5cc60bfae6205fd73086feb98417f5cc10bfae5b0dfd72d82feb96817f5cb31bfae5985fd72c42feb94c37f5ca60bfae5285fd72906feb94817f5ca31bfae5185fd72886feb94417f5ca10bfae4885fd72186feb90c17f5c850bfae420dfd72102feb90637f5c830bfae4085fd71d02feb8e617f5c720bfae3315fd718cafeb88657f5c362bfae1b0dfd70cc6feb86437f5c262bfae1195fd7018afeb80657f1db30bf8ed905fc768cafe3b2657f1d930bf8ec905fc760cafe3ae637f1d721bf8eb315fc758cafe3aac57f1d531bf8ea90dfc74cc6fe3a6617f1d321bf8e9905fc748cafe3a2637f1d130bf8e890dfc74482fe39e437f1cf20bf8e6b15fc73582fe39a817f1cd21bf8e6905fc72582fe392837f1c940bf8e498dfc724c2fe38c657f1c532bf8e2195fc7098afe384657f1c162bf8e0995fc700cbf9b8221fcc4210fe60c887f305443f982221fcc0d10fe404887f106443f882a21fc41110fe206887f002443f590441f9c8621fcce5887e572c43ed98461f5cc631f9e65197bb40903dba0c83ed95310f6ca8887b554443bda84a1bed8260deec330eef6298afd384437e9c062bf4e030dfa70106fd380637e5c221bf2e0315f970186fcb80837e5c031bece3305f671942fb38c817d9c632bece3185f671882fb388c57d9c460bece2285f671102fb388617d9c420bece2085f571982fab8ca17d5c640beae3195f5718c2fab8c417d5c610beae2315f571182fab88a17d5c440beae2185f571082f7396217b9c861bdce4305ee72142f7390837b9c840bdce418dee720c2f6b96217b5c861bdae4305ed72142f6b90837b5c840bdae418ded720c2ef39e43779cc62bbce630dde73182ef39881779cc20bbae790ddd7318aeeb98c3775cc60bbae6205dd73082df3a0c56f9d061b7ce8305be740c6df3a0616f9d020b7ae8315bd74186deba0c16f5d031b7ae8185bd74082bf3a8c55f9d461afcea3057e75102bf3a8635f9d430afcea1057d7518abeba8c35f5d460afaea2057d750c6beba8615f5d4209fcec284fe761067f3b0813f9d8319fcec184fe760827ebb0a13f5d8419faec204fd760c67ebb0613f5d820) else (0xfbc9b20fde4d197ef264cbf793243fbc9920fde4b907ef25483f792643fbc9320fde4890fef24483f791e43fbc8f20fde4690fef23483f719065fb49b21fda4d907ed268cbf693265fb49921fda4c907ed25c83f692a41fb49321fda49907ed24487f692241fb48f21fda47907ed23487f691a41f7cdb31fbe6d987df364c7ef9b261f7cd330fbe68987df32cc3ef99465f7cca31fbe64987df320c7ef39e43f78c932fbae790fdd36cc7ee9b661f74d931fba6c987dd34cc3ee9a261f74cb30fba6518fdd324c3ee99065f74c831f7e8ca07bf43503dfa1281ef95110f7a8ca07bd43d03dea1a81ef50b40f7a84a06ff655837fb22c1bfd8d60dfec5316ff625837f312c5bf59560dfac8b0efd645837eb1ec3bf58f60dfac6b0efd635837eb16c1bf58960dfac4315ff76cc6ffbb6617fddb21bfeed905ff768caffbb2837fdd940bfeec995ff764c6ffbb2617fdd921bfeec905ff760caffbae417fdd562bfeeab05ff75502ffbaa637fdd530bfeea90dff75482ffba6617fdd321bfee9905ff7458affba2c17fdd131bfee8985ff74486ffba2417fdcf21bfee7905ff7358affb9ac17fdcd40bfee690dff73482ffb92c17fdc941bfee4a05ff724c6ffb92617fdc562bfee2b05ff71502ffb8a657fdc530bfee2905ff7058affb82837fdc132bfee098dff70486ff3b6617f9db20bfced285fe768caff3b4617f9da20bfceca85fe764caff3b2617f9d920bfcec285fe760caff3b0617f9d820bfcebb15fe75d86ff3ae637f9d721bfceb315fe75986ff3ac657f9d631bfceb10dfe7558aff3aac37f9d531bfcea90dfe7518aff3a8c37f9d431bfcea10dfe74cc6ff3a6617f9d321bfce9905fe74c42ff3a4657f9d231bfce9185fe74886ff3a4417f9d210bfce898dfe744c2ff3a2437f9d120bfce8885fe740c6ff3a0617f9d021bfce8105fe74042ff39ec57f9cf61bfce7b05fe73d02ff39e437f9cf20bfce7885fe7398aff39cc37f9ce60bfce7285fe73906ff39c817f9ce21bfce7105fe73842ff39a437f9cd20bfce6885fe7318aff398c37f9cc60bfce6205fe730c6ff398617f9cc21bfce6105fe73042ff396c37f9cb60bfce5a05fe72cc6ff396617f9cb10bfce530dfe72982ff394a17f9ca41bfce5205fe728caff394637f9ca30bfce5085fe72442ff390c57f9c861bfce4305fe72142ff390837f9c840bfce4195fe720c6ff390617f9c821bfce4105fe72042ff38c657f9c532bfce2195fe70d8aff384c57f9c232bfce0b15fe704caff380c57f9c032bfaed98dfd76cc2febb6437f5db20bfaed315fd76982febb4a17f5da40bfaed195fd768c2febb4417f5da10bfaeca85fd76506febb2817f5d932bfaec98dfd764c2febb2437f5d920bfaec885fd76142febb0657f5d830bfaec105fd75d8afebaec37f5d760bfaeb98dfd7)) else (if j<3 then (0x7ac43c7e1dcd0ea9073c839481c440dfb06dec36121a850d128675c32ee19290c6d861802fca17610b8085acc2ca616050adb854f0298213ec09c604cb025bc1290090f0456c21f6109b082683ffc1f1a0f1b07590396c1bd20d770687032b8189c0c0005c282c2815300a2604de82574120c0894040801e540e6a06d50343818e40b7c05430268811c4083403c3019f80b3404c8020400db005a001da007200007ff654c3ffb2261ffd8950ffec4987ff61543ffb0a61ffcc960ffe62b07fe764cbff3b261ff9d562ffce6b17fe73583ff31ac5ff98d60ffc86b07fe364c3ff13265ff81930ffaec997fd764c3febaac5ff5d560ffae6b17fd73583feb8ac1ff59720ffacab07fd65503feb2a61ff59520ffaca887fd644c3feb2221ff58f21ffac7907fd63983feb1ca1ff58e40ffac7107fd63843feb1ac5ff58d60ffac6a07fd63487feb1a41ff58d10ffac6107fd62cc7feb1661ff58950ffac498ffd624c3feb1221ff58550ffac2a07fd614c3feb0a41ff55110ffaa4887fd51503fea8a41ff50d60ffa82b07fd41543fe9b465ff4da30ffa6c987fd32d87fe996c1ff4c961ffa64b07fd32443fe98ac1ff4c520ffa4c997fd21583fe90aa1ff48530ffa0d987fd064c3fd98461fecc130ff641107fb20483fd83281fec1930ff60c907fb054c3fd82a41fec1120ff405087fa02443fc98061fe48020ff20d287f906903fc83461fe41a20ff20d087f906543fc83281fe41930ff20c907f906443fc82a61fe41520ff20a887f904883fc82421fe41120ff208887f903843fc81a21fdd9510feec8887f763443fbb1221fdd0f10fee86887f742c43fba1221fdccb10fee64887f7318c7fb98a63fdc8621fee4290ff716507fb8b263fdc5921fee2890ff676443fb3a621fd9d110fece7887f673443fb39621fd9c910fece3197f664c43fb32221fd98f10fecc6887f662c43fb31221fd95310feca8887f653c43fb29a21fd94b10feca4887f643c43fb21a21fd90b10fec84887f632c43fb19221fd85910fec29887f614443fb09e21fd84e21fec2690ff613443fb09621fd84910fec0c887f604c43fb02221fd80f10fec06887f602c43fb01221fd5d910feaeb887f575443faba621fd5d110feae7887f573443fab9621fd5c910feae3197f565c43fab2a21fd59310feac8887f563c43fab1a21fd58b10feac4887f554443faa9e21fd54d10feaa5887f552443faa1e21fd50d10fea85887f542443fa99621fd4c910fea6218ff521087fa8b283fd45931fea2c90ff516443fa8ae21fd45510fea29887f514887fa8a243fd45110fea27887f513443fa89621fd44910fea0d887f506443fa82621fd41110fea07887f503443fa81621fd40910fe8c8887f463443fa31221fd10f10fe886887f442c43fa21221fd0cb10fe864887f413487f793643) else (0xdd80313ff55fea2fee87f3fbf7c9fb00fd3b7e453ee8df59cfa267cbf3e335f06ef7987b6f3d891eae6f4d47a1f3cec5e624f27c790e3c685e24cf0ab78183bed5de74eeec774abb88ddbaaed6c7693bb31dd82ceb26753aba6c9d1dee85073e1b9d8dcd9ae67f7314396b5ca64e4b77210b8de5c5eae25f70f238539c1a6e03d6fe5b7e19be28debd6f0f37621b9d2dc656df9b6d09b4feda0d6cb2b645db16ed83c6bee35d85ae02d68f6b0a35719aaccd4fd6a4eb50ada796d36b695d34891a364d1406870341b9a01ccf93678c33a759beacd5f6676b32119824cba0659bb2b399470c9906481b22699074c7926382b19e18bfac58b62763117d87a4c34e6172b09cd8372c12c6054300b57f52bf135f47af8757b32bd395e712f19d77fcbb7a5d842eaa17436b9bb5cb22e459715ab8295bd2adca96d82b64f5af7ad63d6a5eb4cf5a2eacfad6716b32259612c9896398b13658502c0295f30af14575a2b9515be8ad9456912b29d5858abb1559b2ab1154c8aa0454d22a51151c8a896541229eed4eb6a6c55320a973d4a60a4be522aa8f8d46f4a31151542892143aca14950672814d3fd49f8a4f99a7b713cf89e1c4ed9a754d39e69c814e0c26ee136689ac24d282677932ea99034c4d260c52fd897834b8d25aa12c5a95e84ac4254c529a2947a4a11a4f5526d893034951a490d23c6917a4896242e920d88ffa47c8a3cc51dc68e834708a358118e08bbf456c22999140c89794488220ed0f808745435c218410ad084c0421520de50590822940bc203d101167f9b3f871fa28fc307d8b3e881f0c8f7147abe3d0f9e624f17a78303bdf1dc10ed0075fc3aae9d364e8bc73ec39af9cb6ce4307155384d9bf84deba6ebe371d1b720da886cdb36391af70d6d46af835431a850d32068f1342919eccce4c66ab3318196f8ca8664da324198ffcc71a6309313e187bcc2fa6102304c98108bfc45f822f9597a54bc585dcc2eb617454b96a5c282dcd96c80b5925a722d1216758b2ec591f2c6416158afc857692b69958f4ab8455592a7c95240a86053d029b394c1ca52a522c28e194520a1e250a3282613ff89f604f50277813a649c3c4da3268f9326c980a4b81258792a98946849b9249a922e8909047cd23b691c348d90468c231a917788b324539226c91208887a43dd21c310cbc859e426f2107906bc82d44113205e10194801c3fa51f9e0fae07c683db01ea80f3c078d83bdf1dad8eb8074ee3a291ced8e634725a38df1c3f8e0c46fc6375f1b7f8da586c3635b21aa00d2f068ca340519b30cbd06504321018ca8c444611a301217cb8bb085ce82e2616c80b454596a2c5516038ae9c568e2ac315288a7a05310290414448a0a44f92277b138009a384c02257d125409090475223371170089dc442e2193108c082e0409e1fd40fb58))) else (if j<6 then (if j<5 then (0xa028080060b04c2509848160a048200e8641982a13850200c0481d0c8301004b0983c1609038150602001228138703412070301086418080260e8701c0c8481c0b4481506020018370e860240f052240a8301000b160984a130902c14090401ca1509c461408030120701004a0983c16090381404002060281388c381a0b0481c0c040080268f074381b070321509038160501000d1e0dc6c1d0c054240f05014040030582509848160a048200e8642a10c1509c2810060240e864200802584c1e0b0481d0c054200800504c1e0b0481508030100091409c381a09038180843210040130783a1c0d8381909038168602a1004003878371b0743012078290c05420080068b04c2509848160a048200e50a84e230a04018090380802504c1e0b0481c0a020010130782c1205018080040c0502711870341609038180801004d1e0e870360e0642a120702c0a02001a3c1b8d83a180a8481e0a0280800611470130782d0e0602008005050200c0421c0c030100490983c16094381406020012301409c461c0d0481c0c448210e02009c3a1c07032120702d1287028080060dc3a180903c14894381404002c8a381b04c1e0b030100400282810060200c030100480983c16090280c04002060281388c381a0b0481c0c040080268f074381b070321509038160501000d1e0dc6c1d0c054240f05014040032f227788fbc0edded2ee8576d0bb21dd6feeb07752cba61dd122e79b736db97ddc9bae40b71aeb8b05c402e11d701cb7d0dbce2dd9f6e54b6e3db50ed95b6c20b5c9dabf6d50569f5b4b45a392d1096800b3c759c72cd436641b2e7d952ec97d6443b1d6d8d12c581623cb0e0d84f6c185602cafe1d7cfebd895e52aed55740ab8d95bdfadadd6b16b48359a2ac8f5628eb06357c8abab55b6eac6755afaa95d52e6a85953a8a98dd4acaa4a551f2a8c9544caa1a55060a804d3ea69ea54ef2a749538829b154d2aa665530f697a94b59a56f52946936548efa41ad1e128def466aa2ea5154289bd445aa1ddd0c96858b4241a0ded0456811140049fb74fb867c973dbe9e98cf29278893be49dc24ec9275413a409cf04e602724138ae9c22cdf4e6ed536f89b47cd89a6b6935399a5f4d10e6791334499694c9a663cb31739877cc1d25fbd2f5a97624b8de5b672d389667cb17657c52b7095884aa325423299f94924a31250a527e993bbc9c3a4d39261892cec941e493d241a91d8c8cfe45bf226490fdc86da4241208a8ff5c7d323d491dea8ea5c726a37f71b418d4cc67a23281187d8be645c4a2cd515d48a9ac535628eb13bb8989c49f62405116c886fc414a1fc10f41875a4390a1b7d0d438664430ee17810b3c8565429aa142709aa84a54236210cd07f483c141c420d3d063582d8c14da09bf047f820240e92065302ae81154072a02b10) else (0x1002009a451f0e872381b8c4502713094381a0c8602410078381a0c0582970983c16090280c0400202810060200c03010048210fc421e0e868321644c200a8441c0a0300407e210f87436190ba240a8441c0a0068c85a2b148990c054240a00511470360983c16060200800504c1e0b0481c0a0200102a1388c2810060240e0200942c130942612058281208039430150983c190b04c200b042140401401c2c1284c240b05024100742a090060a84e140803012074280802802c2810060200c8501808028028602813870341609038180842808028038602a1388c3c1a0b050200c040080268b04c2509848160a048200e50a84e230a040180903808025050200c0401806020090301409c461c0d058240e060200401343a190983c17090441c0a0240800c230f0701d0c84c1e0b444180b0401204007908701d0c84c1e0b84a200b03012040071187c3b1c0dc622a138984a1e0d064301208840180b0522104815c783b1c07432150983c16880280902003878380e8642a130782d1005012040068b04c2509848160a048200e824098130782c1207028090200248a380983c16880301004810016130782c12880280c048100143c1d0e038190a8481c0b440140481001c3c1b87430150903c1488028090200343a190a84c1e0b04014020028701d0c84c1e0b84c1c0a0200163c1c0d83a190983c170602c10040034701d0c84c1e0b84816060200163e1c8e06e311609c4c251006832180a04c240d0602c14a0f070360e8642a130782c0a0200183c1c0d83a190a84c1e0b028080060f0701d0c854260f058200a0200800d160984a130902c14090401ca0983c1609038140400208a381b04c1e0b03010040028260f058240a030100081e0e870360e0642a120702c0a02001a3c1b8d83a180a8481e0a028080060c054260f0642c130802c1105010060070a84e230a04018090380802504c1e0b0481c0a020010451c0d8260f0581808020014140803010060180802404c1e0b0481406020010301409c461c0d058240e06020040134783a1c0d838190a8481c0b028080068c054270f0682c14080301105010060070a84e230a04018090380802504c1e0b0481c0a020010451c0d8260f0581808020014140803010060180802404c1e0b0481406020010301409c461c0d058240e06020040134783a1c0d838190a8481c0b028080069187c3b1c0dc622a138984a1e0d064301208840180b0542205015c58261284c240b05024100728542711850200c0481c040128260f058240e050100080983c16090280c04002078371b07430150903c140501000c1f0e06e311609c4c251006832180a04c240c0582a110280aa2c13094261205828120803942a1388c2810060240e020094130782c12070280800404c1e0b04814060200103c1b8d83a180a8481e)) else (if j<7 then (0x204e230d058240e0602004012870360c854240e0581404002832150983c160802804004878341608834128803414060240c00d1d8a83c170a0401c0d444140481801a39138682e1409044180a444140481801c2712868281206830160a848220e82409c391b89c4a1a0c050241006830160a442090280e44e250d060200e06830160a442090270e06c2d1304c16090401d0a824018381b0ac220d0481d0a0280a00b148742e13078381b084280a02803070260c85c26110582a1085014050068e04c19098481a0b05426110742a090070e06e260c860260f0682c148541200d13094261205828120803a15048030703713064300f07034160a42a090068a0240f07225108782c0a005094240b05225108782c0a005094240b0522510871c581309225108718521307a25108782c0a004898260b44a210f0581400912838160a44a210e38e82410074210c854240a0250dc240c054210c854240a0250dc240c054220e8642a1091b848180a432150838dc58a8138961107432150850ec2810842190a848140491c85019084321509028092120803c1c898421907028094120803c1c894341507028014120602c14898421907028094120602c14894341507028014120602c14894320c70a04420898421907028092130883d128682a0e050024280d06226108641c0a02484c1a0b44a1a0a838140091b894301047030160a8440a0258dc4a1807a38180b0541605002c6e2c54080281309245208f474261107386c290e84d241107a3a130883c1605003878290a84d241107a3a130682c0e05003872270d0411c0d0642205012870260c83d1c0d05c160500286c260c84d240d05a2a130883c1605003872270b051240d0622d15098441a0702809e381305426920682d1509834160702801c3913a94349808034188b4542205013470260ca601e0d05a2a0b028016250c258200a4420902409c34960803110824090250c2581c0a442090240d830124782a130742a090050dc3095078290a824010360c84d1e0b84c1d0a824014380ca541e0b42a090040dc3095070290a824010301509c3c1a0b050200c040140401001c1d0c854260f058200a010014380e864260f05a250e0501000b1e0e06c1d0c84c1e0b430150802001a380e864260f05a240a8301000b1e0e06c1d0c854260f058140400317cb758ab14aa00da61240d450140400387e3c1c0d91287028080048c85a2b148990c05420080050fc7832178843e1d0d8642e1544a180a83010011168ac52210f87426110781404003078b71b07530154903d140501000c1e0dc6c1d0c054240f05014040030602a1288c3c180b048200a040080268c054260f0642c130802c1105010060070c054270f0682c14080301105010060070f074381b070321509038160501000d180a04e230e0682c1207030) else (0x200c0421a0a83010060070c4401a0c860281309034180b0502611074320d11807834160a04018090441d0c8301004e0e8642a130782c130702a0c040030781d0c854260f05a240c058220c0400383c1a0b050200c04018060200961d0c854260f058240a0301000b1f0c4401a0c860281309034180b052250c8340601e0d0582810060210c8301004c1e07432150983c168902a0c040030601e0d0582810060210c8301004c1e07432150983c168902a0c040030781d0c854260f05a2610054180a020038421f0e87036190b854261107a250d0541c0a00890066220d86830170b0501a0c44c210c838140511f8c8421b0c8602e1509834168943415070280221f0d85c2c1508835130843415060280c00f1808c381a0b0481c0c042190602009a3c1b070321509038168902a0c040034601e0c0582410050210c8301004c1e0d83a180a8481e0a448150602001a1d0c854260f058200a8300800b228e85a2c0984812080392451d0e05c2b150502210048200f02809c451d0b4521307824100782c0a0060803c1d0e0682611078240d0501c0a0070b04a200c050261208840180b0542205013c6e2c100602813090441e0c0582a0b02801e2a0f0582810078301105010060060b04a200a04c240d0602c15098441cd1508c3c1408032120883808025874260f05c260e050100091b074260f05c180b0401000a150782810060220d0301004a0e84c1e0b84816060200123716094401c0c05026120803c1c0d0602c1480a8461e0b050200e0602004012c6c1d0a84c1e0e0581404002854230f0582810060200401286c1d0a84c1e0b028080048742a130782e1005014040050b856271106c341409044200d0642205013c702d15884361909848220f0682e0b02801e2b0f86c2e110803c1b088280a030034582509848160a048200e48a846140803012070100490983c160903814040020260f058240a030100081508c3c1609040140801004a1b0742a12078280a0200121d0a84c1e0b0401402002470371709c280d06024100781404c1c0dc5a260982c120803c16050030401a0c860260d058240d0501c0a0068b04e200e0682813090401e0e06832110280a0381608038190a04c2410078381a0b82c0a00809c34160a04c200c058220a0200c00d1388c3414080321208838080258e032130782e1307028080050e06c190983c170602c1004002c4e1a0a04018088340c04012870190983c170902c0c0400284e230d05828120803010020096381b0642a130782c0a02001427118682c1409040180a040080260e06c190a84c1e0b0501404002c70190a84c1e0b84014050100162b0d85c26110683017088280a0300344e230a04018090380802484c1e0b0481c0a020010381b04c1e0b030100400242810060200c030100480983c16090280c0400)))) else (if j<12 then (if j<10 then (if j<9 then (0xa42a090058d832134782e130742a090050e032950782d0a824010130902c14090401d0a824014381b864309507838160a42a09006114823a1a0b052281007438130903c1c890421e05014c8a411d8e870361a0b05428100783a1c0a04c241007839128843c160500687c381b8c4582612880321809848160a448210f0280a63e1c8e06e36188b04e251006832180a04c240c05829128843c160500647037160984a130902c14090401cc1c0d8260f058240e0501000a1e0e06c1d0c84c1e0b44a1e0c05820080078e06c130782c128702c0c04002c7c391c0dc622c138984a200d0643014098481a0c05829128843ae3c1c0d83a190983c16894381404003478381b07432130782d1287028080068f070360e864260f05a2410870280a02003c9045218e06c32168ac522644a210f0602c1205004884401e8d466220f878361a0b02410878340e0501487e3c1b0c8421f0e86c321504a210f0682c0e0500488a3a1c0dc5c2d1608842200a04c24894421d023108763a1a8b8562a1107c3c1408841120843c0a02991474381b0b456291087c3a130883d128843c1605004c80391b8cc5c271106c341406831120843c0a0288fc70371b0c85a261086c32130682d128843c1605004c8e361587c361106a2410878280a0300388a381b04c1e0b4381808020016451f0e872381b8c4502713094381a0c8602410078381a0c05829128843b43c1d0e06c1c0c854240e05a250e0501000f1e0dc6c1d0c054240f052250e0501000e2290c5a2c13094120803a190a84308a431c0b8562a138241007432150902809e45218b45226048200e8602a120500348a34160a852281388c401e0e8702813090401e0e842190a84814058228e8682c150a0401e0e0502410072180a84814012188b04e261288c401a0c860281309030160a842190a848140561b8c458271288034180a048180a4301509028022301509c461e0d050200c042180a84010060080c4582713094401a0c860281309034180b0542611074321508b0c054271187834140803011074321004013c542711850200c04019090301004c1b8c4582713094401a0c860281309034180b052190a8450602a1388c3c1a0a040180843210040138602a1388c3c1a0a0401808432100401387032168ac4c251086c32130682d0c054240a0088ac48230f86c220d842180a84014060070b04c2509848160a048200e8642a10d1509c46140803012074321004013060281388c381a0b0481c0c042190802009e3015094461e0c048200a042190802009c411a0803c1d0e0682e160a04c24100783913084320e0501548234100783a1c0c85c2a1409848200f072250d0541c0a00a8f862200d06430170b05026120602c148984219070280a83e1888034190c05c2a1409848180b052250d0541c0a00a0c03c1a0b05) else (0x8030030381a0c860281309034180b052250c8338381a0a04018084320c04012838190983c168902a0c0400283c180a04018084320c0401283a180983c168902a0c0400283a190983c168984015060280800c0e0682e160a0442089842190702809a1c0c85c2a130883d128682a0e0500343c180b858280d06226108641c0a02687430170a84c1a0b44a1a0a8381400d0e864220d44c210d054180a030030381a0903818084320c040128381909038168902a0c0400283c180904014084320c0401283a180903c148902a0c0400283a190983c160802a0c02002858130923d1c090401c81505124110823d1c090401e05013052134903d1c090401e0b028016130883d1c0903414070280143b150943c1809044208f47030160a8440a0280dc521d0c048220f47030160a82c0a0070a43a160983d1c0c04414040180183a16094401409849208f47034180b0542611074454230f050208e06424110701004c1d074260f4702e1307028080059146c1d0983d1c0b83016080200182a0e050208e060220d0301004b20870260f4702e1205818080058a8461e0b048208e0602004012c6c1d0a8481e8e05814040028761d0a84c1e8e05c200a0280800c1d8a84e1e0d048221047a381a0c8440a0278e0521d0c848220f47034170581400d1d8a43a170983d1c0d844140501801a2c1284c248f4702c14090401cb1508c281047030120701004a0983d1c0b0481c0a0200121307a3816090280c04002450230e058240e0602004012874360e054240e0581404002854230f05824104702810020096360e854240f470280a0200141d0a84c1e8e058200a010014270a2481a0c45a28120803c0a026098269205a28120803c1605002c260d05a2812068280e050028722752869301207034188b4542205013870260ca60240e0682d150581400c130642c130802d1408828080300304e230d050200c45424110701004c1b864260f05a2a1307028080058e06c190983c168a8301608020018270c050200c450220d0301004b1c060260f05a2a1205818080058dc4a1807030160a1c4e230d05824100622810020096381b0642a120782d140501000b1c0642a130782d15080280a02003070260c85c261105a2a110501406006894240b0502410071c4e230a040188a0481c040128260f05a281207028080048e06c130782d140602008005050200c450200c030100490983c168a04814060200123712860240e0602c14409c461a0b0481c0c4502004012c70360c854240e05a280a02001625118602c120802810020094371b0602a12078280a020014190a84c1e0b450200a0100142712868309608030148841204b138692c10062210481204e250d0612c1007030148841204c0982c120803a150480206c19098491e0b054260e8541200c1c0dc32184a83c160)) else (if j<11 then (0x50702801a3712860240c0582913084320e0501346e250c048180b052250d0541c0a0068e47037198c8622210880361a0c860130883a190690e06c321087c3a1b0c826110743415070280203b15078281108226108641c0a0260a43a130883d128682a0e05002c72270d0501a0c44c210c8381404c1c09832130682d128682a0e0500306e250c048200c0582a110280963712860240f0602c150581400b1f0e47037170b458221088028130942611074078381b0b456291087c3a130883e130883c16050048782f0e8642e15098441f09834160702801e3913868281208034190881404b1c098321307834170581400a1e0e06c3216898421b0c84c1a0b84c220f058140121e8c03c1a0b858280d06426110681c0a0278f05e1d0c85c2a130682e130682c0e05003c762a138783414088401a0c8440a0268e0521d0c84c220f0682e0b0280183e1c0dc662e13888361a0a03419090441d04814478381b0ac3e1b08836120883c140481801e3c17874321508836128883416060240c00f1609c401a0a04c241108034188841204e148742e13078351105012060058e04c190b84c220b44414048180183e1c8e06e36190b44c210d864260d05c26110742a0900a0f4601e0d058220d84c220c858180a02803c702c100642813090441e0d05a15048038762a0f05c2810078361085014050068e44e1a0b85026110602e10850140500711474381b0b050130903c1c894421e0b028020371b0b04a130902c14894421e0b02801c451c04c1e0b44a1e0c058200800611474381b8b04c2509848160a44a210e70e870130782d1287028080050dc260f05a250e05010009228e05a29132251087830160902801a451d0e06e2d1604c24894421cb228e87036168a4260f44a210f0581400e1b8d85a260982d128843c160500308a380983c1687030100400288a3a1c0dc5026128481e0e058291288439e3a1c0481c0b44a1c0a020014370903c1489438140400245825048200e8642a1081509d4a090401d0c854240a0259105027118502410074210c854240a027110542511850240c054210c854240a02710c582712850240c054220e8642a10d1509c2810060220e86420080259146e28138942812060290c8542182813850200c04219080200942a12850200c042190802009443162a04e258441d0c8542142a13a9411074321509028094441409c4614084210c854240a026110542511850190843215090280982c1284814090401d0c8542142a13850200c0481d0c8401004b1409c240e060210c8401004a150942410050210c8401004a0e0682e160a04c24100783913084320e05014038190b8542813090401e0e44a1a0a838140100f0602e160a04c240c0582913084320e0501403a180b854281309030160a44a1a0a838140100e8642810060210d05418) else (0x8e8501c0c848200f07034170581400d1b894301207030160a204e1a8b0401c0c8440a0248a43a19098441e0e0682e0b028018270d4581c0c8440a0240dc4a1809040180b0542205012c6e250c048180b050e3712860240c0582a1102809445208e8682c148a0401d0e04c240f07224108781405322904763a1c0d8682c150a0401e0e8702813090401e0e44a210f0581401a23108763a1a8b8562a1107c3c1408841120843c0a029914823b1d0e06c2d158a4421f0e84c220f44a210f05814015208d0401e0e87032170a85026120803c1c89434150702802a210f874381b0c85c2a130883d128682a0e05004458200e0642813090401e0e0682e0b02801e270d4582812080321102809438168ac421d0d86426120883c1a0b82c0a0080dc4a1809038180b0510270d458240e064220501243a190c05c2a094421c0d0501c0a00687432170a84c220f0481a0a0381400d0e8642e15098341609034140702801a1f0e86c34190bc461a89840150883814060080fc7832178843e1d0d8642e1504a210f0501c0a0090803c1d0e0682611078240d0501c0a0070843e1d0e06c32170a84c220f04c1407028020200d06430130682c12068280e0500347e321086c32180b854260d058260a038140101c0d85a29130241007430150902801a451c0d864210e8642a090401d0d0541c0a0080e06c2d1484c1e090401e0b028018250902c14090401c71c0d85a260982c120803c160500304a1809030160a048200e491488431e0e06c32168ac522603a180a84814011211006a331107c3c1b0d02410074320e0501407e3c1c0d864210f87436190481d0d0541c0a0089147438170ac541408840120803c0a027114742d1484c1e090401e0b02801846210ec7435170ac54220f878281108024100781405322904783b1d0e06c2d158a4421f0e84c220f0481e0b02802a381b8b44c1305824100782c0a0060fc70371b0c85a261086c32130682c120782c0a0090dc4a120582812080390280e0481e0e448210f0280943a14070241007839128843c160500344a180902c14890421e0501286e250c048180b05225108782c0a0068dc4a1809030160a44a210e50c03c1a0b858120843c1a070280982f0e8642e1504a210f0682c0e05003458200a04c24894421c815078281108224108781404a14874261107a25108782c0a00589c341406831120843c0a0250e04c190983416894421e0b02801837128601c0c0582912884394370c048180a43015090280143e1c8e06e33190c45c2d1609c4c2584c220e8642a1131e0e06c32168ac522684c220e8602a12050040781d0c85c2b0903015090381400c1d8a83c1408842108642a120501308a1d098441e8602a1205002872270d0501a0c842190a8481404c1c064260d05a180a8481400a1d0a038120803c1c894341))) else (if j<14 then (if j<13 then (0x4180b858280d0622410864180802887c361a0b858220d448210d054180803003c541e0b050200f060220a0200c00c1587c36170a044200f068220a0200c00e138682c1409840180b044140401801a2b0d85c26110683016088280803003478381b07432130782d1208438140501001e3c1c0d83a190983c168943814040034781d0c854260f05a2610054180a020038781d0c854260f05a240a8301000c0e854260f05c200a0280800a1b0742a130782c0a020012380c854260f05c200a0280800b1c0d832150983c160501000a0e86530170a8210e8682a0e0500305213490441e8e448210f0581400c1304d240d05a29120843c16050030261007a39130843415070280c00c09a48221007a39128682a0e050030260c05a29130843415070280c00c09834180b452250d0541c0a0058e04c194c03d1c0c05a2a1105814060070e04c194c03d1c0d0602d150581400d138682c124703010020092250c048160a448210f0280943712860240c05829128843c160500346e250c048180b05225108728582510050261206830160a44a210e689c341409034180b05224108781404d1c098321309034160a44a210f0581400e1b860240c052180a8481400a1c06426120682c148602a120500306e250c048180b05226108641c0a0268dc4a1809030160a44a1a0a8381400d1c89c341409034180b05226108641c0a0278e04c19098481a0b052250d0541c0a0070dc4a1809040180b0542205012c6e250c0481e0c0582a0b028016391389434180a048200d0602c150881404f1c09832180983c1a0b054160500306e250c038180b050e3e1c0dc622c1309440190c04c240b0522410878140531f0e470371b0c458271288034190c05026120602c14894421e0b0280323e1c8e06e311609c4c251006832180a04c240d0602c14894421d7228f874391c0dc5c2d1608842200a04c24894421d2200e47037198b84e220d868280d0622410878140521f8e06e36190b44c210d864260d05a25108782c0a0098c458271288034180a048180a430150902802038190b4562612884361909834168602a120500447c311006832180b858281309030160a44c210c838140541f0c4401a0c8602e150a04c240c05829128682a0e050050803311080361a0c8602e160a034188984219070280a63f1908436190c05c2a130682d128682a0e05004458251007830140984822100602c1508814050160803a180a04c241107830160a82c0a0078b8562711078361a0a04c24110803419088140511c0b456210e86c3213090441e0d05c16050040501c0903c1c890421e05012874280e048200f07225108782c0a0068a83c1409044200f07224108781404d1487426120883c1c894421e0b02801a3a14070241007839128682a0e050034521d09848220f072250d0541c0a006) else (0x88401e8e44a1a0a8381400e1c098321349030168a44c210d0541c0a03004070260c84d240d0602d1489434150702801e3813065301307830168a844160501801c3813065301307834180b4541605003470b7158441a8943c14040180161d0c850200c0421a0a8301006006074329808835120843415060200c00d148742c1307a38180882808030030541e0b048208e0602004012858271006828130923d1c0d06020040138521d0b84d240f47034110501006006898321609840168a044140401801838130642e130882d14088280803003470b70983c1689438140400283a190983c168984015060280800c0e86530130782d1205418080058ec3a150983d1c0b8401405010018360e854269207a38160501000b1c0642a130782d15080280a02003070b71b065301509a481e0b450140400388e381587c361106a2410878280a0068c0542711878341408030108602a10040180202b1207c361106a180a8401400b1807834160a040180843415060200c00e0f86c2e1106a250d054180a0058a83c160a0401e0c04414040180182b0f86c2e11078360a028014270d058281308030160882808030034702b0d85c26110682e0a0280163712860240c058287231118635190b452260421d0c054240a0300418ac31c0c85a2b14899120843a180a84814010210fc7835190843a19448210e8682a0e050180223f5f0f064210f8743619448210e8682a0e0500448c421dae86a2d148843a1307a24108782c0a0300498ac15d0e06c2d158a4421f0e84c220f448210f058140141f8e16e321689842190982d120843c16050180223f1c2dc6c3216898421b0c84c1a0b448210f05814013192c46029130843e1d0d865128602a1107028022461a8b45429540843c1d0a04c200f842180a848140600a3145aac158a852a81087c3a130883d0c054240a0090c85a2713294421a0c850260c05c210c054240a03004c7032168ac4e2652884361909834168602a120500488435108783a9c0c8582a14098401e898421a0a838140600a885401f0f075381b0c85c2a130883d128682a0e05004c7e321086832980b05428130602d130843415070280c0141f8c8421b0d06530170a84c1a0b44a1a0a83814012168843a190a04d241007830170882c0a030040702d158843a1b0c85026920883c1a0b82c0a0088a03816090401c0c04008025094301609040180a04008025108803d1a8cc60220f878361a0b858120843c1a060200a846210ec6a2e158a8441f0f0502210448210e0200a4401c8cc5c271106c3414068311208438080280e4561f0d8441a890421e0a0200c00d180a84e230f0682810060210c054200803004056271208c3e1b08834108602a100401801e300f0682c150a040180843415060200c00f1807834160a04018084320c04013080331106c3)) else (if j<15 then (0x5074260f05a180a840100091c064260f05a180a8401000a1c064260f05a240a8301000a1c0642a130782d15080280a02003072b71386930170a248220c454200a028080101d0702a1207838160501000a1b8602a120782c140501000a1e0e06c1d0c84c1e0b44a1e0c05820080078e06c130782c128702c0c04002c78381b07432130782d1287028080068f070360e864260f05a250e0501000d1e0e06c1d0c84c1e0b448210e050140400791478381b0c85a2b14899128843c180b040100111f8f07036190bc421f0e86c32170a8251087830160602002a451e0e87036168ac52210f874261107a2510870280800a0fc70371b0c85a261086c32130682d12884381404004c78381b0ac3e1b088351208438140501001e45168ac52210f874261107a180a8401000f1c0c85a2b13084361909834168602a1004004056291307c361106c210c054200a020038781d0c854260f05a240a8301000c1e07432150983c168984015060280800e1f8c8421b0c8602e1509834168943015060200221f0e86c32170a8441a89842180a83014040080742a130782e1005014040050ac3e1d0d85c2611078361005014040070e16e2d158a44c890421d0c054240a00731470b71b0c8421f0e86c32890421d0d0541c0a0090e16e36168ac52130883d120843c1605003c70b71b0b44c130682d120843c160500383a190b05428130803d130843415070280c0100e86530170b054261107a250d0541c0a00787432160a850260c05a26108682a0e050180201d0ca602e160a84c1a0b44a1a0a8381400f1d8a43a19098401e8e0602e1105814060078e0521d0c84d24110803d1c0d05c1605003c50230e058240e0602004012874280e048200f070200401284a230c0582410050200401286e250c048180b05020040128601e0d05828100602410878340c040138541e0a04018890421c0401284e1a0a04018890421c0401284e1a0a04018084320c04012870b7158441a8943c140500283a190a040180843415060200c00c0e865301106a250d054180a0058a43a160983d1c0c0441404018018290e85c269207a381b0501400b130642c130802d14088280803003070260c85c261105a2a0a028016371286024100602c148841204b0e86530150421d0d0541c0a0300303a194c05c2a890421d0d0541c0a0068a43a134903d1c890421e0b0280c00d1487426920883d1c890421e0b02801a260c84d240b45224108782c0a03003470260c84d240d05a29120843c160500383a194c059130802a11070280c00c0e86530170b2240a8441c0a0058ec3a13490401e8e842180a84814060070742692088401e8e4301509028018380c84d240c05a2a108602a120501801c380c84d240d0602d148602a1205003476290e84d241007a39130843415070280c0101487426920) else (if j<16 then (0xa0068f874391c0dc58130942611072c783a1c0d8260f84c1e0b028016471e0e06c1106c241107828090300358637188b0522712c4a1487430150902801e45218e06c29130241007430150902801cc3190bc52268ec662a09438180a8481c0a008115862d158a4502689c3d0e8602a1205003d8638190b4522612c4e1687430150902801e44618ac5227134461a0843a180a84814060080843e1d0e066270f44a1e0a8381400d0f874361a0cc461a890421e0a83814060078ed742c1549440130904214890421e05013d74371608028130903e148943c16050038741307c2c120803c160500288c455d0d83a1307c2d0f0682c1205003884415d04c1f0b04a1e0b0381400c5d0d83a130903e168943c1605003076ba0e84c1f0b448210f058140600691474381b8b02612048200e511474381b04c1e090401e0b028018415d0843e1d8a84c1e0943c160702801c3b5d0b8552711050241086224108781404f5d0e05a21098481f0b44a1e0b02801a3b5d0ac3e14098441f0d448210f05814060082e86c1d0903e148943c1605002c72b71609c40130943818890421e05013870b716080281309438168943c1605003870b7190b44c1305a1e0d058240a0068e56e2e13888281288031120843c0a0270e16e2d1084c250f05a250f0581400d1c8e16e1b09c441a0c05a24108782c0a030040561106a210f0682c10048180161f0d85e2a1106825108782c0c0481801c2b0f844210f06a2510878280903003436110683216894421e0a0240c00c1807c3a1b0d0642f1186a26108602a11070280c0121c0ac4e265286c271106830170843015090280c0121228c3e1b0bc54220d440180a848180903004056245186c220d0642d108602a100481801e3c9b0843e1d4e04c1e0983c150702801c3c9b07c36174b0441a090441e0a830120600807c36174b0441a88034160883012060070ec7437160a24a200a04c240f0742e14894421d11d8e86c1d098481e0e85a250f0581400e1d0a43a13090441e0e44a1e0b02801a381709c289208032130883c0a0260b426920782e130883c1605002c5c2711051241006426110781404c1c4d85a2109a481e0b84c1e0b02801a381586c33170a04d241107834180b8441605018025361587c229007836120883c140481801c2b0d85c229007834190b444140481801c3716094401409848160a44a210e60e26c1b098441a8c05c2411078280903003c561b098441a8c05a220d0582009030038561b0b84c221087835180b444140481801e360e84c1f0e05a250e0501000b1b074260f05a250e0501000a1d0d8381509038160501000a1d0a038120803c1c0501000a1b8d830150903c140501000a1b89430120602c140501000a0e8642a130782c128702c0c0400303a130782d1287028080048e032130782d128702808) else (0x2d148a04d1387a251087430150902801c4510874381989c3d128843c150702801c2d1304c16894421e0d058240a0060b426128782d128843c1605002c702b08835128783416080240c00c1c0ac2210878351287828090300307e389b0a43a130883d1c0b84c1e0b02801f3614874260f47036120883c140481801c2c098491288438c290983d128843c160500247c37162a04e258441d0c8542163e1b8b150200a04c248f474261107346c290e84d241107a3a130782c0a0068dc58a8098491e8e048200e50d852134903d1c090401e0b0280183f1e4d85213490441e8e04c1e0a8381400f1484c240f07225108782c0a0058b04a130902c14894421c90983c168943814040020743716080281309225108728743614874261107a250f0581400c218f872381b8b04b0883a190a843090431e0e06c291341d0c05424))))))
def genIndex9 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (0x13b6f1b632635448f000f0005474f008f000f00094e8a9d153f4f000f000f000920ef000b066f000f000f000f000f000f000f56061c29386820d2d67f000340549def00081d7d23ba24d8094f000f000f0005a97f0002cfef000f000703b21cf53c5f000948ff0007019f00094c5515e60d7f000f000f000f000f000bdb5f0004115321c0a98f000f00058e0bcaf413bd0ae91a5f000f0004554f0004aaf6de2c578f000f000f00042309a0af000f000f00062ddc2a78c4a82b490be2217f44dd57aea1c40c933eb3124f00051847b9df000f000295b05be0206f000f000f000325d23c8f00081375158f0006110f000858d82eb617df1213d6aa3906588aa95f00045ace0e1f000f000ad52f000926ac278a17a1301110f545065256da08316142c15d7907aa3cd0d7b5168d10ebb2190bbf0b9f00073f14132e23ef0009334f000f14942e233fa5382f000f1662a13153bf00051932391b49c6d0920100abe5114bbbcf000d9b910e3a211655a10ed53bf2373f00080fcf493f0003ca7f5daf000f000b0d4f0003194c0e5fcc801a825bc0577f00009949000f000f000f0005809b2a6c189f00021ede3a4f000f000f000f000f5dff00041d20cfdf000612fc417f2fef000f0003397f000f00022ef402ec45cf00052fa5485f0009147bc9640f91594e55f829605a031b0e599f00084abd1710b6440b484aaa9b799cd9d74e12069d3858fbd4a9007c1ee6583f00081f7f000c553f00002a8f000f000f000d43f549ba41a756d9b6ff000144ff0000b0303f68487bd94f2c0f49293d139a44c89846de03e798c85e444eff0000008b834e7020c0038102044c99d16002015e0c000000c0004424280120030700386080b3c187004c0800e107100618000080800b4c0408c00050010c00a802448c121c040181020782180c00040400850a404860200087000030100040000e08183001c080026850f3a0c580142c000180830102300862408205002000700188a52e4822300002a11600b8130007921a4cb04020870626fc0090014586021c1010e24387100c207000000120080030270903120078200441031a2c0000c14100124c180021c080100c68c1a046070844104022860c06282002a000870838782121c1001044001022400158040820004a010e0078002105020204082080c18700000810e3c08a00e4114062c000280820000080011000301000c180021008002001810888083060402902143030c08086280008018044050a7c000001410600380040800080021001400044842c441820000007141800e041800100b80010060100100000306003090004487020019d00042800404009080800902002020c0c6821210087020010b0608001002c002000c01716281010824000380c703125800204000020008391080410100340000e00000) else (if j<2 then (0x404eb2e8f000c16091270c2d4c4f13d61002d33f4253f000839eb3a6f00010bff0000cf5f00064c6f00020a68494b2a55051ac589c56f0000178f000a07e726731698484f000a5c721c951b1a55935d961a650ba9470f000243535649ca240771441b5bd4349005d9d884d95909d34f231268cca1381b290f0009376f000a265f000f000f000d8edd2d3f000dcbc6b93f000f000d33df000f00040585406f000f000f00033a182f3f000f000f0006379f000f4a96cae82451231f000a41bf000fb76210c317bf000f000c42a44add4c7f000d3ed8347f000d2f82d8ff000f000c5a405c18552f000935eb2db5a0492d681b7403810fae24e199d31b8e3d432c1b1c1f000c47d6b9f95891bf8f000c15bf000f000e306f000f000f598840c73700bf9021df000f000f000f000f000fb5130391a8b8b8cf000f0000b3bf000fb39c31c4d77f000f00031431430442b4392e344f558ca0c816450fda5ed3b2ab30ef0000bdbb532718894b0d353e9cc93c3f000f000f000fb6ef000f000b5ba62f1f000f000f000f000295a1c4cf00083fbf000ac49f000b1c8f000f000f00074f7b30a9c9c5a9a24bde31d2082f000f00043b0798bb380c131a378f000cd9c44baf000628162c8fd89c208f000f000f000f000f00065aaf000f00098f3f45f9514f3f353d2a1ec55b224387103538bc404c23da51e207ff0007366a243ab70c5aef000f000691e8551f000f00073c4f000f000ad08f000e200f000f1a4f000c976f000150bf000f00004e2f0005a22b479f00019a1f0004d2cf000f000f000db3a9252f000f000732bf00089e57aa004b5f000a530f4204bbb24d1556af000f000f00073a0f0004460f000f0000c78f0004ab794577b7583a93320f000f00075e3ddcff000f0009317f000f000f0007a08f0008326f000d1c5f38ec09f92c27329f000f000bdbce4f6f000b12a842643fd3146d123f000f000d255f000f00094315576f00094f17bf2c91f22e7e14b3464f210452df000e4e975c5a3a29afaf000252af0008228f00013b7a23f73428447c20b83004280f000f00030c87387f000f000dd7df000f000f000e218146f12af72f42534439d0de10454f000ab2eb4d3a283e21bf1535b507a09fc6cf00043def1906044f0006261f000f000029905e0f000e19234dc559ae340f000b085a04392ff01baf000f0008da780c5f000f000ab0df000f000f000f00001c73362e8e3e35b503113bd95dc838fad9ab001f000a1b31ce43009e078533ea34eb3be3b6bd196f0007506f000f000f2e10089230355a3f000e2fd33e5b507d974430df535c2e5b524f000f00049aff000f00051281aed4cbef000f000f000c3f2f000f000b4bbf000f000f000f000f00074a0335ca35f4b3ff00040a0749af000dcac4bedf000f000d423d9eafb870857f000f000) else (0xa9ddbd38f000c3b20346b33231c3f571803df000e224a97fb323c0958b02843cf2d5f0004508d42ef0007309cd9bf000f0008b4af00081fd9107821fe287baa91452308cbda6353ae0fbe4a38aacf0006086fd53a10801c60096603aece052582582c38daa03f000c351f000d8c6f000e0a4e47ef000cca4f0004b683d11699c7407f0003436fb22f00002c4696a731af00013303443f000db30a4a83db4e2c78004d2a1f000d54db31b897a75b9e16e510db18fd533f0007ab8a4a783eaa1eaf00075ab3d8b80f2e4aff000d5b4441c4437f000a58af00080ea25d6f0004bdcc5bbd1a3614c84cd4b6d30ffcc0514caf00001e362667461f272c1f2f000cbe10276f000018a8cc1f0007d54f00023fef0006b2665b0f000516b22ca15cf24734371b471f000f000f000800f102df000f000f000f0005d5f8410c0ad0ba5c2848427022af0003cf9f000923cb4ff1a1d0388cdbeb2e4656c83133135955b402b527c6b2bf0757b44f000f100f00015e9f000911ef000f0006bb9f00003f5f000bb32f000e56fc023197560c301f91546f0008310f000b2c3f000f00094def000f000048cf000f000f00000a8d3bcf000f000f00045a6a504912cf0009cadda0f90dc327a22123d074c9ef00012c9cc4df00014ed83ec71170b43d4e3f000f000e46bf00072ccb37c9ab69491c25e73e7919cf000f000fccbecc9b58bc06cf00030644172f000f000c5dbf000f000f000f000f00052741bd3f000b4fcf0000372318285400de4f000f000e3aba9dcf000dd04f000f000f000f0003177f000f000f00001019099a325f000f000f000a0f3f000f1dec2512198f00023dd5b47f00045e6f000f000f000f00054d7f000f000f000f000f0007dcdc237c596637ff000f000f000828e908062aeb4134402f000f000f0005d9338d6f0007072f53ff1fef000f000f000f000f000552eedaff000c3cef000ca91f000536d0597f053f000d0ec73ff31044c6bf229f000fb2821df304bd1b5f00084e4500a65a1f000f000f000f000f000f000dd45b5dd2536e1398345f000d9999185d1e6c191f000f000f0008b6a12ad0dabf000f000426b1144fc9470f6f0000cd17d49c977f000f01204b18de68293f00042dfc5b390e94374a1972973b238d05f0451f1fff0009472cba3db0e220501877060a17e4499a1a9f3c7e5421026512df0337d1ae0aae03735d290b6a56783f0906b629c459e6bd471b4f000c97df000b511f000f119f000f000250e6403f000f14ff000bdb7f0000063f015d19ad3a592bc10e0b302a9eb13dfbb3674ccf000f000d262f000f000758712ace449538c3b14c2b255b7e232f000f000f000c18cf0005225c049f000f000f000f00024a11bb8f00034c1f000f000f000ecbf05a7f000f000e0343d66537ef000904164a253c959aef000c2c6))) else (if j<5 then (if j<4 then (0x8aad808ab3ba401cd0b5f00040a3e9869a84c0cccb4b20a162d0c2cff000333b74aef000f000f000f000c1d9f000f000d979f000f000c254f0002af2d43ef000f000e2d7f000355cf00092ecf000f000f0004213f0004d69b16c4046f00085b1f000f00025d3f0004b11f125ada900710d6562baf000f00001bff0005d90c909f000f000f000852c79b0f000f000b018f000c1e8f57ef000b4f54478848870def000f000f000f000b555f000f000f00068c591b2248df000f000925ff000f000f000f000f000c13f03360279f0007dbff000ccc7f000334c7997f000f00043b565c2e05a731944ee732ff0006baafbc4f00002daf0008c165084f000fbe289d4203c745321f42b01f000c1d5a538f15ff000426923d58209a4d8b4c94a81f000f00085001a94f000f0004ab5f000e1b9843b7c4ef000f000f000a2915150e3b3f0004032ec19f000f000a016f000f000c55d436fa56ef31ea2f6302af1afc2deb46c61294503f000a5e190b3f000f000f000a541fd9dfc5cb33c23cff000f00002ed41f020f7c175fb9ee4ead12e0145f360cbc7a4c8cb1712cbf0008076822fe20af000c0aff000847f71bb3235900b619d1083b14a34d4ecb4f000f000f000845ef00095adf000f000c28bf0003221c31ff000f00035483585b1060111f000736cf000f000e2e69c0e104df0000013f00001094477f000f000f0009b2c2021f000f0003ca0ed1cd341246e1527f000ab5d358e93ee140dad8c6201705643f7eb31e35d85a250c2bc88f000f5132b7889420285b32d9367f000585800d05006b561936100b08239ed6d30035364d091453723111ca35d2dc4b7f59339bcf04533da72aba3efc51588afe1a1d079b0b1236e314ec4b8fdb9f000222d62a9b981505b74685259255e12976c54022c22493167524068ee338a54e5e4d6602c95a84b8af000f000043ad393b203aaa3f000618691e2bb63f0009069d0676275b0f8d220651645666383104784b6f000f159f000f000f000f000f000f000c2897057f000f000f00014c2f0004bd81cb6f09bf000e9a890abf0001180f000c1e1f000519ef0008b46a57c45e7717fa53d8de060e604180073f000c475f000b526f0000b920352e4ddc2b8329d018bd3a7515c7c5594d5e5c6f0002586cbd95054d5d5f00000246a90d34bf000554aa19bf000f000b30b42ee032e902823ca3b3c1236f000f000f000f000f0000569f000327ed17311f31ca6f000f000fba1f000f000456b918d021a3496f401e06d02a34b08dc6ea51dbb046c6a34ac5510c1130dae1daaf000139ff000f000f000f000f000f000207cc37b024ca152f0001246137d89ce02a4f000f00022d1f00022b9f000c5c0f0008c93910bbcf6f000a984f000ba9df000f000d0daebc54422ebf7c2a0f00045b64455c24a99bfe0b2f00092b0) else (0xf000f000f377c498f000f000618e33aa3097f00083e21992d428949e75190520d41dd138a2bed27bf000315680d9a30764f424ec6b4ce5d1e55654f0302f644a54a422c5bbc6f0004568f000c99651fc04b434b9001470bc80e8d482608b110af000c161f000435529dbf0004223f000f000f000f000a227d1efe2fcf000f000f000abbdf000d1e00581f06af0001c63a0273be4f000f0002092f0003bab3432f000a1abe32c3580f000f000c06f75a5b4fbf00081483b95f000211ff00011d3f4dff0002133c9d722cdf000f000f000f0000a0b81e5db84f00053cc72165b49c446f000f000f000f00038e1f000f9e3c087f000d2b1501ef000f000f000f501e39cf000f00051e7f000f000f000f000f0000327dc47f000c489f000f000f000f000f000f5ca62442b5cf000d2959036b91bf93071c4526d0cd9c40b1116c3c00324156371d0225af11b45439176f000a3aff000b11dd048f0003162f000a4e6859d79b492b641bcf0005412b4429b69f00033b1e52345e5d5e25444f000e5176142c433f00019c2450c8579f0007502404f4bb7f000541ef00060a9f0004134f00085ccf38453e9249540b78090c22b2415ed46fd4dac51f000148e845933e3f000f28f197cf01fd226f000e54500c1f0003354f000f0003539e9e789bb01cb30b8f000f00045ce9256f000fb255a932d918b4e9c3ce5eab54cf000f000c33af000f000f000f000f000326ff000b1a2f000324f72f2ddda3549f9832098f000f0000980504af02921d6ea9b65e8093353db58dedc994465c419fa0dadcee5219b3e1b138204acf2626cf0001bf5a16ff00064eb754eb2e97151836ac4feac8af000ad5ae2e039a785d0f000f0007aa5b57300f1e51ff000f000f0003b06ac6da486e544f000e181c48051fbc348d20ff0008522f000f0009cb2dde3a2d87282f000d42f20fee421e4c3f000b595b47b52b3e3e1e462f000fb8b1242f000f0d39b4202aaf000842559e6f00080f43234403f3591f000f000e9c5f000f000f000f000f000504cc50d839500a7f000a268f2f7356535d4f000b1ce924bf1ca0050f000800d2215f000eb330247f000c3056136f000cca8e3cbf00044bcf000a174f000d1f1e3502531f000f00083d0f000f0000497f000f000e518f000f000f2b5659bf000c122f000f000f0008a143331f000f000f00030d222fb0cb3ec3d4c1e31c0129f854b25c840c70365f000f000f000e991f0007277f0006af9f0001273f97e0a9cf0002d43ed8a528df000f000e40054cb53685155f000f0002222f000f000f000f000229ae28a34cf2b1e24c084f3911af396144e21d8420ca1cc25bfb47af0003b8d4b298db6f45ab2a2f000f000f000a1418c64f000205c65c3839aa035f000fd968d8d208df0007c6920a2706851db81ae8b48130ceb6c92f5acc6)) else (if j<6 then (0x4343e57fb34ff000f000f000f000a411427f2298b157c0e2b50904e75248330413567093f00081ac98c700cff000f0001c7923148040e0f5c4e1f528edbdf000f000f000f000f00090dbf0000d4b14ce012bf0002312f00092bf41f82dd2f000f00084b2f000050a9105f000f000b05e043942bdf000f000f0000363f000f000f0009c8bf00013356bd0f000f000f000e40ac081f000008ef000f369f00071120257fcbd90eb9529f00020259463b590ea11d0aca44cf000c3f8d445d2ce940ff000b21ebce5f000619ff000f000f00010cb2a10c9baf00080dff00072d9f000f000f000d49ff000c9b3f000b37af000223af000f000f000f000f000a102f000026471541bfe548af00062b799b2f00032bbf000f0007d6374b3f00020dd41fa4219511cf00090c6f00033c6f00033153bc9f000f00075de4a053c4bf000f00010d1f000f32a05eb715de988f00050d8713af0002592034ddda5e5d8f000f3acc0bdf00013b8f48b7398e47cf000f00088df91e9f0006aae74e0f000f00011e4f00061ad0b2d3d581d64f000f000ea92f000f000098ff29bc5ec92dcb07df000f000e09c93c1f000f000f000dc538a0ef000f000f00070eff338a1dcf000543df409508ff0002b993414f00033a3ad78f000f333c179aa99f00075cbf000f000b49db3b4f0001466a3b9759ff000f000440ed4be42e3f000f000d557bcf8f000f000f000f2ea9052f000f000153ea41f03c29241546af000f000f00029d0f000d416549023f9f011a574a359d0d58399f000536bf01bf000b22e4b4f44d9b98733e0642df00000c0f0003440c328cddb200cf0003118d14d23584070bb58ab45dd14951c906281dd530ff0e4b3d940d6f512406e21a7816dd39bf000e1aaf000d27df000f389b005c458f000e01df000f4819d862288f00004f874a5baabcc9ff0005308f000f000f074e2f9c2f0f000f00074a6f4085202d58cf000f000f000052f945b625c9199357d1b4df000915a43e8f000f000b50ff00073e4f000f000307b40cd6250f000399075b5f000f000f000f000ec6fa233f000900ef000f000f000f294f000d4dbf000c017d4c4256225701c98f000b32272d27a9641be5c97f00053216abbd1f5f00054674993cd59f000f000f337f000f00060880339f000d318f0003bca0424f000f000f000f00014daf000fc28f000d09ec1d4f000f000f000f1a06c5fe170fcc501954cb7d0caf0002214f000459cf000e96b951ba90cf000f00071cdf000198d3985f00000551042e130f0004b6230a5f000f000f000f00040f0134af000c0ce7270cc52f000f0003059d53cf000f0000cebc1d1f00061bdf000b394f000d584caaaf000f000f000f00041833b597d92f000f000f00005cd3483a575d1da1385051af0002456a35733d873ad03d3d165c0e74163f000) else (0xf000f000628cf000f000f00025c4f0004c952572f0006375f000f0005b74f000f000417cf00043dc554733fceda8b14032d49a9ff000e29259e964d293aef00094fdf000f00013bbf000f000f000f0006b90f52bf000aba2001a829eb9a2fb8ec44be429827124f92a079286e35af13cf000f000f000f45d402274fa10eef000f0006b89013d6550f00041eb34bf454ff000f000425b19b1f000f000c5b8f00053a82505f000f000f000f000aca941f63207126ec5a9b09a816a813e93d7f0003030d57b75af93e6c434f000f0003020d260f000f000f000f0004061f8aeabecb476f000f00054d035c9e065746990c4f00069dff000))))
def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x22a19d1c1b9b048403928a8674706e12100e04025229d1c1b84840382810014403c3a38343230120c0a0604006a2a09d1a16151494100f0e8e0a0989080787040100aa8a82767468585450403c3a38282624201e1c0a0400a9f1c1b9896139312900d0c8c0a0989060585040100aa7c72706e62584e4a403432302826241816140a0400a9815138f0d0b0a080604028100801c706e62584e4c4a403432302826241a18161412100ea981513918f0d0a080604840381009c703a32261e16120e0a040059e1c1b0e8c89878583028201001a544e3c34282018100c06040261c0e8c8987858482818100167c72706e62584e4c4a403432302826241a181614a181513918f0d0b0a08060401009a78706c3a322a261e160a04006181513918f0d0b0a08060401009a78706c3a322a261e160a040061e1c0e8c8a89878584028100801a807e7c72706e12100e4a32221201d9c8484038100967e78706c12100e0a04005191695949303028201001484807a6a6660443e3c36342e2c12100c06040299f9e1917908f8e8d8c8b8a848302818100225c5a584442402826244a3211d9a971595110f8f0a0888040100a05a5652423e3a26221e0a04006201c999713910d8d0a06860401009c7e70645a4c423632261a160a04007158f8d8b8886840281008016584c4a2624161412100e51513918a08060483810094261e16120e0a04004229c1b0987858302010014282018100c06040240987858482818100108a7c7472706e62504e4c4a3834323024201e1c1a181614b981413918e0d0b0907060401009a7874706c38322a241c160a04006981512918f0c0b0908050401009a786e6c3a302a241e140a040060e8c8a8987858402808014100a0402002828100073a49a74be25151dc8974201fa4f5c75738e1bb4d6c68332a1804b945972b014b49ec4cf25011d48943fb1da0e3469431716e0a844e424710e07e439c1ab0c404a41e40bb042014404c00f0003ff62ffd87ff60ffd03ff31ffcc3ff21ffc83ff10ff98bfe61ff983fe50ff907fe40ff8cbfe31ff8c3fe21ff883fe10ff58bfd61ff583fd50ff507fd40ff4cbfd31ff4c3fd21ff483fd10ff18bfc61ff183fc50ff107fc40ff0cbfc31ff0c3fc21ff083fc10fdc43f510)
def genIndex10 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (0xff001e00038f317a5cd1a552c9060863362c463c0078005207e003c004a71f000c5d9166bab8e60c83d74b162c2f097e6e19313ae7610ee1da381d96b11db4bf683ef80061bf6bdb18485b10459e003255515f4d5de00231dda98f001e8bf5269e04d03737e0133f80040ba18e702df800f000c227c0019da421d49d110e0a6de24298e24589a68f00014a52881816d367e00097a7800f0000767c00213bf0001b6f6fef800f000cb8d12620e24c11e014020a63ef0013c83185f800f00058be8dd522b3043380bc007800f0008b43c007800749fc5d621ab98ff001e003c007800f0014ba80a67800f001e003c007800f000095b2f37800757e810ca4e95ff2df5e001d088155f00102000ebf800f001e003c005188cb02425211b01803356667c74a40a854e7e003c00780045bbe003c00225af000fa09730986fa465e002c29f800f0019b868b47945f001e00390ad8f2f001e0019871aadd2c96bc0819ba5bf131a786e5696b9d2d3e70d97348ec91a24243cef96e3f00069bd859f11935940794450e0e7f001e001a2e9a3df001e003c007800b35200d8a417800b5b5e003c007800a03da635cae92be00f3e002e567800f001e003c007800dc59e003c00016af001ea7d8d6880252236ac40cdf800f000e6abc0026f5896be0038925257519301302c079f6d63be003c00129b6ad18403c007800816ca397c007800b39fe001157f800d58f83e40dcfae8f001c833c0078009bd5e00355df800e87b2a90186d14ff000dbdbc9cf800f001e003c0078009603e7f3d51780001a9e003c0078005149c38fc0042b029f1e00157bf800f000986fc0078000ccbe001e4dc0270d4fe00089eb807d04d41c7c0038c3f00044194d1f8009171e002c168e89f001e003c007800f001e003c0078004cbd62361767800239ca1b7c007800f001e0033097800b43de003c0000e87dafe8a7c007800f000c0d3d127222124ae297835f8000cd4c83810cf80049f240fc104f800523faaba846780010d9c697c004150323ae53b4b83f008d5444d745878006359e003c0025696247e00397f3049a19c80350a4780093b01c21054ae01f000023f946e93f35d3a76d0df1ac0f0002088622386820a00caf0a0019410000800418c950280104029821f0208906300020302102832e0001604109802c7008104082000a2430130000000808500181c00b2a004850e1018900081850808000000050006187151808580060840014100870e202881a083060a105840c780030c000000c14002040400b022c20018643200610f000004580020011f00187020804081100c0820204184031400200050000400180021c1050668002001080100004850804381041c11316080190000402020430d04340010a0cb0812000050804283020c9020a0000b0010080000410d0600082) else (0xead377800e0ea94e3c004a47dd1be003c0028cdf001c82bc00661824abe000d43da23bbf2c54b2fb128bdc9e649ac297800f001e0036a3f8005de1d878d4ab293c0a3e17bc005a28d22cfac14f7912d52dbe0028a12a8c65114a00572e4f721a7e2d107d686e652d0c534e4f800f397d14fc003e5cd40a1bd349608b2ab9a04aba4f218ac333e001809a6e73bf4c9dfd6c407ff0016571183f8002d0f2a53c007800544e653418cc00f5441c7fe800f302f00049a6169b862e51f16968f47662f000d252390f800f001e001d75863cf000349bc0060308c742a4253c38c554d5e71a0d7184a1d1fa503d87d985b18fe003c0078007205c15001c75f4fb05e00313af800f1bcca5fc0009eac32fe003c007800f000a3f477df800bbc3e003c007800ce2b660e56e02f5f001e003d3b6eb8f001e003c00393a73e9e003c003632f0006ac993de02cf001e00272d6938f00058ffc007800c19fe003c00780085ade003c004206a4ff09e4857e0c83b06c920efaf800f00123d882cb200f157bc07c00211aa1efe002524f8003637e003c005a7a163fe00341bf800ac27e002f0a42b3dc176563d15253aec1e29fa4197800dc07e003917486000634c23c00119df001e003f41f8005dca669bc0078004503e0034e9f994a4a16187ccc49bd98f3e003c006706f001e000c31d09b3368a4bb95cb12bf001e003c005c45f001e047528a1ee807a521fd027800d02fe002c227800b23de003ce578003339749f0e698d6f001e003c007899f001c837c001321bc14e1ce96c9132b32488d3152883e2417092944b680a4dc966f274af11b75f68092c15e8bde37f8b7a087d108d3a9e0bb3762df30090e714382da4b10760b8bc00184fe2cbc979c6df8001ca00117c005b0313da23ee8eaf80032b3630302bb322f000472052ff800e0c9e003c007800f001e002cfbf80070d2a7c7c0061b672dda246d7c72317bbc2b23962780094cbe003c002186f001e000f2c217cf001a0302f87800436be003c42d61d432c6c5bc234e8ae2afe0031330a21154127ca33378008d50c213c007800f001997f11cf800f001e0008b0f800f000f25490c7800f001e003100db12416a0413c007a3af001e001c9a200bf0010607c0020fff001e00237ff800f000ac68e7b7800f0008053c007800213de0028337800f000603b8537800f641a93bc003131f001e00246e78005bf78223c007800819942dfc0078004000a64e84b8244f3e7c7c20a1f800f001e003c007800f001e003c00718e9c43e00092c3977f00066c0d22f800117de00172668fe0e450414c11b6bef001e003097f9afd5dd84fa0ab78002031e002b12a8ddf001a52ed7031d245b66a84cc80afff000a713f2af13cf0000793c007800d41e41ddb08cc3ea2ccbbcc8635a6c3045e00115e2a59f00125ee90ec50)) else (if j<3 then (0x420bc5b8bbc0078009dfa4067931f800047de9f214f3db5e50a0a6bc0042b7150c401b893fa8361064908865615151dd43cec53fe8c24fbe003c00780014c9e003d01598bcccfe002d64f80050e547e574769175487261143d7800f001e003389531ef001e003c0071e2f001e003c0058ea7105a45770bb436f001e002cd113181173e003c007800f000fb5558bf800336eb2ffc002040f001e002033f217338345c7c004825d054827018af800f24543e18fade37f0002043c0075cbf3cfc702c5fd0aa191bc82376e3803f0007b6bc0032ccf000866a11dfe5de539e003c0078008c5481c2512ef1323fc0bc44a9a253ce399be0c1d060df001e0010eb0305959ee38210b78000421e003c005173f001e001c86f800b4783757c007800f000a3c06bfd109f00184a415ad688f000271fc0031fa63f158afc005a52ec19e0026f3f800f001e003c007800f0011a4e748110bf001e003f57b93750f8eb0687366608907e000cf645f7a02b62764ad3233f00161efc00685cf001e003c007800503be001d1aa310f0008b5387e01a4a43e02b7f0cb4dd132b2c2b631589af001489bc0028d7d471e00291b918c5a81c77689b35bc3638a024553f04d64a8ebb472df800f001e0000a0f800d0e838691545d49b18481fb483b2c3d4d7a3c7c77997e06236bc87707800211c83afc0061e0036447a7c0039d0f001e003c0039dcbc5b5937c007800f001e00108e021bf55217f9c4af800b2189bdfc0068f4b025e002909f800e575e00286af800f000eb47c003a912555e0020b1f800f0010b174027187b53be001f7f1930f103e15af824a60a3fb0282b2732b44145690037e7800f001e0018f5d292f001486b94212ef8183e001cd0e261f001e002ca271fbe483e002851c868f001878cc85161cd5c96973c000edeebf944ce8a3f8005911e00236ff0e1f000c24bc006167e07300f3c0078001d2dc974cbed1784179e003c007800a32277cbc003172f000e443c0078003039e003c002eddf001e003c004020b1886be6d55ede950d4f9a7c006a709ca28c00d70a0e4f001c708ca499bbf0012363c007800f000eb7fd65fea951b3e003c0072ac88d738546e6319ef00185e578a70cb542841946f44b049305627fc00614af000c56ef2ce2f3f001e003c007800f001cc4c00422c6f001ebf144592991c0b8a24017f8002c215c44b031a2dbc2c4b56c273eabf515844e8f321de1c1c462755b78003341851bc007800f001e003c007800f001e003c004db01225e07cc57630cc229e003c007800c0abe0030e638acd25183424b7b8d2f001e000b516c9ce3a3884926064dc006afa2fc0058daf001e003449f800f00068c28bfaf02f001e003c0029a7f00189cb4b0453fd2e82af59237878d115e00042862d7f001e003c007800f001e000953501af0014b) else (0x1e002caf42a36a949800823f800f20365b275bb82920be0a39169405afd5883a7c0040bbf00102e851fddf14351280c9677800f000e163c005207f00160a314160)))
def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (0x780f00c3544797d41e01cee2c6cd287c066af01e03c0780f00a4660444f00a26c2f8041de01b0780987e03c045f653e03ea780f00b7bc0780f01e03c3902f01e0101f80f01e037470ab4ca4c53e619b9e03c0780f01e036d780f01e03c0780f01e01a4780c9fe0180e57248363c07157dab3a33fadf003afc011b851706d1d4ca8be00acfe515db37c06d2b845bb28b9af00a3c4605b5d2858c951ef01e028582be4a943c0780f01663c035df0192fc07802d9e00cfa64cc6a414a104145f1ac3199739e013172a781080e890031050820c30c5000002044)
def generatedLevels : Nat → Packing
  | 4 => (1,7,7,0,0,0,0,genData4)
  | 5 => (50,6,7,0,0,9,0,genData5)
  | 6 => (520,5,7,0,0,13,0,genData6)
  | 7 => (1132,4,7,0,0,16,0,genData7)
  | 8 => (1518,3,7,0,0,18,0,genData8)
  | 9 => (803,2,7,0,0,17,0,genData9)
  | 10 => (47,1,7,0,0,13,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking
def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 5 0 1 genIndex5
  | 6 => lookupWord 18 109 5 11 6 1 genIndex6
  | 7 => lookupWord 188 1129 7 15 10 1 genIndex7
  | 8 => lookupWord 385 2310 7 16 11 1 genIndex8
  | 9 => lookupWord 496 2978 7 16 11 1 genIndex9
  | 10 => lookupWord 259 1552 7 15 10 1 genIndex10
  | 11 => lookupWord 22 145 6 11 6 1 genIndex11
  | _ => fun _ => none
def qF_ : Forest := ⟨507,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [96,81,67]],generatedLevels,generatedIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP4_0 : block qF_ 4 0 1 = true := by
  apply cellsBlock (ar := 5) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB4 : block qF_ 4 0 1 = true := genP4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block qF_ 5 0 50 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block qF_ 5 0 50 = true := genP5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block qF_ 6 0 36 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_36 : block qF_ 6 36 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_132 : block qF_ 6 132 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_228 : block qF_ 6 228 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_324 : block qF_ 6 324 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_420 : block qF_ 6 420 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_516 : block qF_ 6 516 4 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block qF_ 6 0 520 = true := (@block_merge qF_ 6 0 228 292 (@block_merge qF_ 6 0 36 192 genP6_0 (@block_merge qF_ 6 36 96 96 genP6_36 genP6_132)) (@block_merge qF_ 6 228 192 100 (@block_merge qF_ 6 228 96 96 genP6_228 genP6_324) (@block_merge qF_ 6 420 96 4 genP6_420 genP6_516)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block qF_ 7 0 70 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_70 : block qF_ 7 70 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_166 : block qF_ 7 166 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_262 : block qF_ 7 262 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_358 : block qF_ 7 358 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_454 : block qF_ 7 454 13 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_467 : block qF_ 7 467 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_563 : block qF_ 7 563 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_659 : block qF_ 7 659 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_755 : block qF_ 7 755 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_851 : block qF_ 7 851 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_947 : block qF_ 7 947 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1043 : block qF_ 7 1043 89 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block qF_ 7 0 1132 = true := (@block_merge qF_ 7 0 467 665 (@block_merge qF_ 7 0 262 205 (@block_merge qF_ 7 0 70 192 genP7_0 (@block_merge qF_ 7 70 96 96 genP7_70 genP7_166)) (@block_merge qF_ 7 262 96 109 genP7_262 (@block_merge qF_ 7 358 96 13 genP7_358 genP7_454))) (@block_merge qF_ 7 467 288 377 (@block_merge qF_ 7 467 96 192 genP7_467 (@block_merge qF_ 7 563 96 96 genP7_563 genP7_659)) (@block_merge qF_ 7 755 192 185 (@block_merge qF_ 7 755 96 96 genP7_755 genP7_851) (@block_merge qF_ 7 947 96 89 genP7_947 genP7_1043))))
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
theorem genP8_487 : block qF_ 8 487 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_583 : block qF_ 8 583 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_679 : block qF_ 8 679 34 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_713 : block qF_ 8 713 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_809 : block qF_ 8 809 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_905 : block qF_ 8 905 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1001 : block qF_ 8 1001 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1097 : block qF_ 8 1097 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1193 : block qF_ 8 1193 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1289 : block qF_ 8 1289 54 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1343 : block qF_ 8 1343 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1439 : block qF_ 8 1439 79 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block qF_ 8 0 1518 = true := (@block_merge qF_ 8 0 713 805 (@block_merge qF_ 8 0 295 418 (@block_merge qF_ 8 0 103 192 (@block_merge qF_ 8 0 7 96 genP8_0 genP8_7) (@block_merge qF_ 8 103 96 96 genP8_103 genP8_199)) (@block_merge qF_ 8 295 192 226 (@block_merge qF_ 8 295 96 96 genP8_295 genP8_391) (@block_merge qF_ 8 487 96 130 genP8_487 (@block_merge qF_ 8 583 96 34 genP8_583 genP8_679)))) (@block_merge qF_ 8 713 384 421 (@block_merge qF_ 8 713 192 192 (@block_merge qF_ 8 713 96 96 genP8_713 genP8_809) (@block_merge qF_ 8 905 96 96 genP8_905 genP8_1001)) (@block_merge qF_ 8 1097 192 229 (@block_merge qF_ 8 1097 96 96 genP8_1097 genP8_1193) (@block_merge qF_ 8 1289 54 175 genP8_1289 (@block_merge qF_ 8 1343 96 79 genP8_1343 genP8_1439)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block qF_ 9 0 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_96 : block qF_ 9 96 34 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_130 : block qF_ 9 130 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_226 : block qF_ 9 226 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_322 : block qF_ 9 322 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_418 : block qF_ 9 418 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_514 : block qF_ 9 514 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_610 : block qF_ 9 610 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_706 : block qF_ 9 706 16 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_722 : block qF_ 9 722 81 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block qF_ 9 0 803 = true := (@block_merge qF_ 9 0 418 385 (@block_merge qF_ 9 0 130 288 (@block_merge qF_ 9 0 96 34 genP9_0 genP9_96) (@block_merge qF_ 9 130 96 192 genP9_130 (@block_merge qF_ 9 226 96 96 genP9_226 genP9_322))) (@block_merge qF_ 9 418 192 193 (@block_merge qF_ 9 418 96 96 genP9_418 genP9_514) (@block_merge qF_ 9 610 96 97 genP9_610 (@block_merge qF_ 9 706 16 81 genP9_706 genP9_722))))
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
end PEqualNP.Outside.L_meta_51390.ForestCore
namespace PEqualNP.Outside.L_meta_51390
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0,3,0,4,1,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7,6,7] : List ℕ).length / 2,(List.ofFn x).getD (([0,3,0,4,1,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,3,0,4,1,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,4,6,0,7,1,7,3,7,4,7,5,7,6,7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0,1,2,3,4,5,6,7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xffffffffffffffffffffffffffffffeefffffffefffffffeffeeffeeeeeeaa00ffffffffffffffffffffffffffffffeefffffffefffffffeffeeffeeeeeeaa00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 2 zero,64,68)]) (by decide +kernel) (qP_ _ (by decide +kernel))
    (qP_ _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 2 zero,64,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
def upperGates : List Gate := [⟨.or, [4,2]⟩, ⟨.or, [1,0]⟩, ⟨.or, [9,3]⟩, ⟨.or, [6,5]⟩, ⟨.or, [11,4]⟩, ⟨.or, [9,7]⟩, ⟨.or, [11,7]⟩, ⟨.and, [12,13]⟩, ⟨.and, [10,14]⟩, ⟨.and, [8,6]⟩, ⟨.and, [0,3]⟩, ⟨.or, [15,16]⟩, ⟨.or, [19,17]⟩, ⟨.or, [20,18]⟩]
theorem upper_shape : ∀ g ∈ upperGates,(g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel
end PEqualNP.Outside.L_meta_51390
open PEqualNP.Outside.L_meta_51390 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_51390 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
