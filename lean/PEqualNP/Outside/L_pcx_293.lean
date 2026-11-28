import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_293
-- The pack-bit argument reuses p6h6i6l’s earlier L-lib-529 proof, PR 40623.
namespace Pcx293.Chi
abbrev BitSeq := Nat → Bool

def chi (x : BitSeq) (i : Nat) : Bool := x i ^^ (!x (i+1) && x (i+2))

theorem affine_step (x : BitSeq) (i : Nat) :
    x i = (chi x i ^^ (!chi x (i+1) && x (i+2))) := by
  unfold chi
  rw [show i+1+1=i+2 by omega, show i+1+2=i+3 by omega]
  cases x i <;> cases x (i+1) <;> cases x (i+2) <;> cases x (i+3) <;> decide

structure Aff where
  bias : Bool
  live : Bool
  deriving DecidableEq

def Aff.run (a : Aff) (z : Bool) := a.bias ^^ (a.live && z)
def Aff.comp (a b : Aff) : Aff := ⟨a.run b.bias, a.live && b.live⟩
def Aff.one : Aff := ⟨false,true⟩
theorem Aff.comp_run (a b : Aff) (z : Bool) : (a.comp b).run z=a.run (b.run z) := by
  rcases a with ⟨a,p⟩; rcases b with ⟨b,q⟩
  cases a <;> cases p <;> cases b <;> cases q <;> cases z <;> decide
theorem Aff.assoc (a b c : Aff) : (a.comp b).comp c=a.comp (b.comp c) := by
  rcases a with ⟨a,p⟩; rcases b with ⟨b,q⟩; rcases c with ⟨c,r⟩
  cases a <;> cases p <;> cases b <;> cases q <;> cases c <;> cases r <;> decide

def scan (y : BitSeq) (i : Nat) : Nat → Aff
| 0 => Aff.one
| n+1 => Aff.comp ⟨y i, !y (i+1)⟩ (scan y (i+2) n)

theorem scan_correct (x : BitSeq) (i n : Nat) :
    (scan (chi x) i n).run (x (i+2*n)) = x i := by
  induction n generalizing i with
  | zero => simp [scan,Aff.one,Aff.run]
  | succ n ih =>
    rw [scan,Aff.comp_run,show i+2*(n+1)=i+2+2*n by omega,ih]
    exact (affine_step x i).symm

theorem scan_live (y : BitSeq) (i n : Nat) :
    (scan y i n).live=true ↔ ∀ t < n, y (i+1+2*t)=false := by
  induction n generalizing i with
  | zero => simp [scan,Aff.one]
  | succ n ih =>
    change ((!y (i+1)) && (scan y (i+2) n).live) = true ↔ _
    rw [Bool.and_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨h₀,h⟩ t ht
      cases t with
      | zero => simpa using h₀
      | succ t =>
        rw [show i+1+2*(t+1)=i+2+1+2*t by omega]
        exact h t (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega),?_⟩
      intro t ht
      rw [show i+2+1+2*t=i+1+2*(t+1) by omega]
      exact h _ (by omega)

theorem periodic_shift {f : BitSeq} {k : Nat} (h : ∀ j, f (j+k)=f j) (i n : Nat) :
    f (i+k*n)=f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ,←Nat.add_assoc,h,ih]

theorem periodic_mod {f : BitSeq} {k : Nat} (h : ∀ j, f (j+k)=f j) (n : Nat) :
    f n=f (n % k) := by
  calc
    _ = f (n % k+k*(n/k)) := congrArg f (Nat.mod_add_div n k).symm
    _ = _ := periodic_shift h _ _

theorem chi_periodic {x : BitSeq} {k : Nat} (h : ∀ j, x (j+k)=x j) :
    ∀ j, chi x (j+k)=chi x j := by
  intro j
  unfold chi
  rw [show j+k+1=j+1+k by omega, show j+k+2=j+2+k by omega,h,h,h]

theorem odd_cover {y : BitSeq} {k i : Nat} (odd : k % 2=1)
    (per : ∀ j, y (j+k)=y j)
    (all : ∀ t < k, y (i+1+2*t)=false) : ∀ n, y (i+n)=false := by
  have hk : 0 < k := by omega
  let a := fun t => y (i+1+2*t)
  have ap : ∀ j, a (j+k)=a j := by
    intro j
    change y (i+1+2*(j+k))=y (i+1+2*j)
    rw [show i+1+2*(j+k)=(i+1+2*j+k)+k by omega,per,per]
  have unbounded (t : Nat) : a t=false := (periodic_mod ap t).trans (all _ (Nat.mod_lt _ hk))
  intro n
  by_cases nOdd : n % 2=1
  · have e : i+n=i+1+2*(n/2) := by omega
    rw [e]; exact unbounded _
  · have e : i+n+k=i+1+2*((n+k)/2) := by omega
    rw [←per (i+n),e]; exact unbounded _

theorem no_output_implies_zero {x : BitSeq} {k i : Nat} (odd : k % 2=1)
    (per : ∀ j, x (j+k)=x j)
    (off : ∀ n, chi x (i+n)=false) : x i=false := by
  have two (n : Nat) : x (i+n)=x (i+n+2) := by
    have e := affine_step x (i+n)
    rw [off n,show i+n+1=i+(n+1) by omega,off (n+1)] at e
    simpa using e
  have same (t : Nat) : x (i+2*t)=x i := by
    induction t with
    | zero => simp
    | succ t ih => rw [show i+2*(t+1)=i+2*t+2 by omega,←two,ih]
  have one : x (i+1)=x i := by
    rw [←per (i+1),show i+1+k=i+2*((1+k)/2) by omega]
    exact same _
  have two' : x (i+2)=x i := by simpa using same 1
  have e : chi x i=false := by simpa using off 0
  unfold chi at e
  rw [one,two'] at e
  cases q : x i <;> simp_all

theorem inverse_chi {x : BitSeq} {k : Nat} (odd : k % 2=1)
    (per : ∀ j, x (j+k)=x j) (i : Nat) :
    (scan (chi x) i k).bias=x i := by
  have e := scan_correct x i k
  rw [show i+2*k=i+k+k by omega,per,per] at e
  cases live : (scan (chi x) i k).live with
  | false => simpa [Aff.run,live] using e
  | true =>
    have xoff := no_output_implies_zero odd per (odd_cover odd (chi_periodic per) ((scan_live _ _ _).mp live))
    simpa [Aff.run,xoff,live] using e

end Pcx293.Chi

namespace Pcx293.Linear

abbrev Seq := Nat → Bool
abbrev Pair := Bool × Bool


def mid (x : Seq) (i : Nat) := x i ^^ (x (i+1) ^^ x (i+2))

def next (p : Pair) (z : Bool) : Pair := (p.2, p.1 ^^ (p.2 ^^ z))

def walk (y : Seq) (p : Pair) : Nat → Pair
| 0 => p
| n+1 => next (walk y p n) (y n)

theorem next_correct (a b c : Bool) : next (a,b) (a ^^ (b ^^ c))=(b,c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem exhaustive (x : Seq) (i : Nat) :
    walk (mid x) (x 0,x 1) i=(x i,x (i+1)) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [walk,ih]; exact next_correct ..

def choices : List Pair := [(false,false),(false,true),(true,false),(true,true)]
theorem in_choices (p : Pair) : p ∈ choices := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide


theorem decode_complete {x y : Seq} (h : ∀ i, y i=mid x i) :
    ∃ p ∈ choices, ∀ i, (walk y p i).1=x i := by
  have e : y=mid x := funext h
  subst y
  exact ⟨_,in_choices _, fun i => congrArg Prod.fst (exhaustive x i)⟩

def get (y : Seq) (p : Pair) (n : Nat) := (walk y p n).1

theorem mid_get (y : Seq) (p : Pair) (i : Nat) : mid (get y p) i=y i := by
  unfold mid get
  change ((walk y p i).1 ^^ ((walk y p i).2 ^^ ((walk y p i).1 ^^ ((walk y p i).2 ^^ y i)))) = y i
  cases (walk y p i).1 <;> cases (walk y p i).2 <;> cases y i <;> decide

theorem closed {y : Seq} {k : Nat} {p : Pair} (period : ∀ i, y (i+k)=y i)
    (close : walk y p k=p) (i : Nat) : walk y p (i+k)=walk y p i := by
  induction i with
  | zero => simpa [walk] using close
  | succ i ih => rw [show i+1+k=i+k+1 by omega,walk,walk,period,ih]


theorem circular_characterization {y x : Seq} {k : Nat} (py : ∀ i, y (i+k)=y i) :
    (∀ i, x (i+k)=x i) ∧ (∀ i, mid x i=y i) ↔
    ∃ p ∈ choices, walk y p k=p ∧ ∀ i, get y p i=x i := by
  constructor
  · rintro ⟨px,hm⟩
    have e := funext hm
    subst y
    refine ⟨_,in_choices _,?_,fun i => congrArg Prod.fst (exhaustive x i)⟩
    rw [exhaustive,show k=0+k by omega,px 0,show 0+k+1=1+k by omega,px 1]
  · rintro ⟨p,_,hclose,hx⟩
    have e := funext hx
    subst x
    exact ⟨fun i => congrArg Prod.fst (closed py hclose i),mid_get _ _⟩


theorem triple (y : Seq) (p : Pair) (i : Nat) :
    get y p (i+3) = (get y p i ^^ (y i ^^ y (i+1))) := by
  unfold get
  change ((walk y p i).2 ^^ (((walk y p i).1 ^^ ((walk y p i).2 ^^ y i)) ^^ y (i+1))) = _
  cases (walk y p i).1 <;> cases (walk y p i).2 <;> cases y i <;> cases y (i+1) <;> decide

def pxor (y : Seq) (b : Nat) : Nat → Bool
| 0 => false
| n+1 => pxor y b n ^^ (y (b+3*n) ^^ y (b+3*n+1))

theorem prefix_decode (y : Seq) (p : Pair) (b n : Nat) :
    get y p (b+3*n)=(get y p b ^^ pxor y b n) := by
  induction n with
  | zero => simp [pxor]
  | succ n ih =>
    rw [show b+3*(n+1)=b+3*n+3 by omega,triple,ih,pxor]
    cases get y p b <;> cases pxor y b n <;> cases y (b+3*n) <;> cases y (b+3*n+1) <;> decide

end Pcx293.Linear

namespace Pcx293.AllRotation

universe u
variable {A : Type u}
structure Law (A : Type u) where
  one : A
  op : A → A → A
  left : ∀ a, op one a=a
  right : ∀ a, op a one=a
  assoc : ∀ a b c, op (op a b) c=op a (op b c)

def Law.prod (M : Law A) : List A → A
| [] => M.one
| x::xs => M.op x (M.prod xs)

theorem Law.prod_append (M : Law A) (a b : List A) :
    M.prod (a++b)=M.op (M.prod a) (M.prod b) := by
  induction a with
  | nil => simp [prod,M.left]
  | cons x xs ih => simp [prod,ih,M.assoc]

inductive T (A : Type u)
| tip (v : A)
| join (l r : T A)

def T.vals : T A → List A
| .tip x => [x]
| .join l r => l.vals++r.vals


def T.up (M : Law A) : T A → A
| .tip x => x
| .join l r => M.op (l.up M) (r.up M)

theorem T.up_eq (M : Law A) (t : T A) : t.up M=M.prod t.vals := by
  induction t with
  | tip x => simp [up,vals,Law.prod,M.right]
  | join l r ihl ihr => simp [up,vals,ihl,ihr,Law.prod_append]


def T.down (M : Law A) : T A → A → A → List A
| .tip x,b,a => [M.op x (M.op a b)]
| .join l r,b,a =>
    l.down M b (M.op (r.up M) a) ++ r.down M (M.op b (l.up M)) a

theorem T.down_length (M : Law A) (t : T A) (b a : A) : (t.down M b a).length=t.vals.length := by
  induction t generalizing b a with
  | tip => rfl
  | join l r ihl ihr => simp [T.down,T.vals,ihl,ihr]


theorem T.down_get (M : Law A) (t : T A) (b a : A) (j : Nat) (hj : j < t.vals.length) :
    (t.down M b a)[j]'(by rwa [down_length]) =
    M.op (M.prod (t.vals.drop j)) (M.op a (M.op b (M.prod (t.vals.take j)))) := by
  induction t generalizing b a j with
  | tip x =>
    have : j=0 := by simp [vals] at hj; omega
    subst j
    simp [down,vals,Law.prod,M.right]
  | join l r ihl ihr =>
    by_cases h : j < l.vals.length
    · have h' : j < (l.down M b (M.op (r.up M) a)).length := by rwa [down_length]
      simp only [vals,down] at hj ⊢
      rw [List.getElem_append_left h',ihl _ _ _ h, List.drop_append_of_le_length (by omega),
          List.take_append_of_le_length (by omega), Law.prod_append,T.up_eq]
      simp only [M.assoc]
    · have hh : l.vals.length ≤ j := Nat.le_of_not_gt h
      have h' : (l.down M b (M.op (r.up M) a)).length ≤ j := by rwa [down_length]
      have hr : j-l.vals.length < r.vals.length := by simp [vals] at hj; omega
      simp only [vals,down] at hj ⊢
      rw [List.getElem_append_right h']
      simp only [down_length]
      rw [ihr _ _ _ hr, List.drop_append,List.drop_eq_nil_of_le hh,List.nil_append,
          List.take_append,List.take_of_length_le hh,Law.prod_append,T.up_eq]
      simp only [M.assoc]

def T.leaves : T A → Nat
| .tip _ => 1
| .join l r => l.leaves+r.leaves

def T.cost : T A → Nat
| .tip _ => 2
| .join l r => 3+l.cost+r.cost


theorem T.exact_cost (t : T A) : t.cost+3=5*t.leaves := by
  induction t with
  | tip x => rfl
  | join l r ihl ihr => simp [cost,leaves]; omega


def balanced (v : Nat → A) (start : Nat) : Nat → T A
| 0 => .tip (v start)
| h+1 => .join (balanced v start h) (balanced v (start+2^h) h)

def T.height : T A → Nat
| .tip _ => 0
| .join l r => max l.height r.height + 1

theorem shape (v : Nat → A) (h s : Nat) :
    (balanced v s h).leaves=2^h ∧ (balanced v s h).height=h := by
  induction h generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ h ih =>
    rcases ih s with ⟨a,b⟩; rcases ih (s+2^h) with ⟨c,d⟩
    simp [balanced,T.leaves,T.height,a,b,c,d,Nat.pow_succ,Nat.mul_two]

end Pcx293.AllRotation

namespace Pcx293.Unit

universe u
variable {V : Type u}
abbrev Lit (V : Type u) := V × Bool
abbrev Clause (V : Type u) := List (Lit V)
abbrev Form (V : Type u) := Clause V → Prop
abbrev State (V : Type u) := Lit V → Prop
def neg (l : Lit V) : Lit V := (l.1,!l.2)
@[local simp] theorem neg_neg (l : Lit V) : neg (neg l)=l := by
  rcases l with ⟨x,b⟩; cases b <;> rfl

private theorem not_ne_self (b : Bool) : b≠ !b := by cases b <;> decide

def adv (F : Form V) (s : State V) (l : Lit V) :=
  s l ∨ ∃ c, F c ∧ l ∈ c ∧ ∀ t ∈ c, t≠l → s (neg t)
def iter (F : Form V) (s : State V) : Nat → State V
| 0 => s
| n+1 => adv F (iter F s n)
def Sat (F : Form V) (w : V → Bool) := ∀ c, F c → ∃ l∈c, w l.1=l.2

theorem keep {F : Form V} {s : State V} {l : Lit V} {m n : Nat}
    (hl : iter F s m l) (le : m ≤ n) : iter F s n l := by
  induction le with
  | refl => exact hl
  | step h ih => exact .inl ih

theorem sound {F : Form V} {s : State V} {w : V → Bool}
    (model : Sat F w) (base : ∀ l, s l → w l.1=l.2) (n : Nat) (l : Lit V) :
    iter F s n l → w l.1=l.2 := by
  induction n generalizing l with
  | zero => apply base
  | succ n ih =>
    rintro (old | ⟨c,fc,lc,unit⟩)
    · exact ih _ old
    · rcases model c fc with ⟨x,hx,sat⟩
      by_cases e : x=l
      · exact e ▸ sat
      · have opposite := ih (neg x) (unit x hx e)
        change w x.1= !x.2 at opposite
        rw [sat] at opposite
        exact False.elim (not_ne_self _ opposite)

theorem no_conflict {F : Form V} {s : State V} {w : V → Bool}
    (model : Sat F w) (base : ∀ l, s l → w l.1=l.2) (n : Nat) :
    ¬ ∃ c, F c ∧ ∀ l∈c, iter F s n (neg l) := by
  rintro ⟨c,fc,all⟩
  rcases model c fc with ⟨x,h,sat⟩
  have q := sound model base n (neg x) (all _ h)
  change w x.1= !x.2 at q
  rw [sat] at q
  exact not_ne_self _ q


theorem fire {F : Form V} {s : State V} {L : List (Lit V)} {t : Lit V}
    (fc : F (t :: L.map neg)) (known : ∀ x∈L, s x) : adv F s t := by
  apply Or.inr
  refine ⟨_,fc,by simp,?_⟩
  intro x hx ne
  rcases List.mem_cons.mp hx with same | mapped
  · exact False.elim (ne same)
  · rcases List.mem_map.mp mapped with ⟨z,hz,rfl⟩
    simpa using known _ hz

def clause (a : List (Lit V)) (t : Lit V) := t :: a.map neg

theorem fire₁ {F : Form V} {s : State V} {p z : Lit V}
    (fc : F (clause [p] z)) (hp : s p) : adv F s z := by
  apply fire fc
  simpa using hp

theorem fire₂ {F : Form V} {s : State V} {p q z : Lit V}
    (fc : F (clause [p,q] z)) (hp : s p) (hq : s q) : adv F s z := by
  apply fire fc
  intro x m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with rfl|rfl <;> assumption

inductive Gate (V : Type u)
| and (a b c : V)
| or (a b c : V)
| xor (a b c : V)
| copy (a c : V)
| inv (a c : V)

def Gate.clauses : Gate V → List (Clause V)
| .and a b c => [
  clause [(a,false)] (c,false),clause [(b,false)] (c,false),clause [(a,true),(b,true)] (c,true)]
| .or a b c => [
  clause [(a,true)] (c,true),clause [(b,true)] (c,true),clause [(a,false),(b,false)] (c,false)]
| .xor a b c => [
  clause [(a,false),(b,false)] (c,false),clause [(a,true),(b,false)] (c,true),
  clause [(a,false),(b,true)] (c,true),clause [(a,true),(b,true)] (c,false)]
| .copy a c => [clause [(a,false)] (c,false),clause [(a,true)] (c,true)]
| .inv a c => [clause [(a,false)] (c,true),clause [(a,true)] (c,false)]

def Gate.Holds (w : V → Bool) : Gate V → Prop
| .and a b c => w c=(w a && w b)
| .or a b c => w c=(w a || w b)
| .xor a b c => w c=(w a ^^ w b)
| .copy a c => w c=w a
| .inv a c => w c= !w a

theorem clause_sat_iff (w : V → Bool) (L : List (Lit V)) (t : Lit V) :
    (∃ x∈clause L t,w x.1=x.2) ↔ ((∀ z∈L,w z.1=z.2) → w t.1=t.2) := by
  constructor
  · rintro ⟨x,hx,yes⟩ all
    rcases List.mem_cons.mp hx with rfl|hm
    · exact yes
    · rcases List.mem_map.mp hm with ⟨z,hz,rfl⟩
      change w z.1= !z.2 at yes
      rw [all _ hz] at yes
      exact False.elim (not_ne_self _ yes)
  · intro h
    by_cases all : ∀ z∈L,w z.1=z.2
    · exact ⟨t,by simp [clause],h all⟩
    · obtain ⟨z,hz,wrong⟩ : ∃ z∈L,w z.1≠z.2 := by
        apply Classical.byContradiction
        intro none
        apply all
        intro z hz
        exact Classical.byContradiction (fun hn => none ⟨z,hz,hn⟩)
      refine ⟨neg z,List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨z,hz,rfl⟩)),?_⟩
      change w z.1= !z.2
      cases x : w z.1 <;> cases y : z.2 <;> simp_all

theorem Gate.sat_iff (g : Gate V) (w : V → Bool) :
    Sat (fun c => c∈g.clauses) w ↔ g.Holds w := by
  cases g with
  | and a b c | or a b c | xor a b c =>
    simp only [Sat,Gate.clauses,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
      forall_eq,clause_sat_iff,Gate.Holds]
    cases ha : w a <;> cases hb : w b <;> cases hc : w c <;> simp_all
  | copy a c | inv a c =>
    simp only [Sat,Gate.clauses,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
      forall_eq,clause_sat_iff,Gate.Holds]
    cases ha : w a <;> cases hc : w c <;> simp_all

def Gate.weight (g : Gate V) := (g.clauses.map List.length).sum
theorem Gate.weight_le (g : Gate V) : g.weight ≤ 12 := by
  cases g <;> simp +arith [weight,clauses,clause]
theorem Gate.width_le (g : Gate V) (c : Clause V) (h : c∈g.clauses) : c.length ≤ 3 := by
  cases g with
  | and | or =>
    simp only [Gate.clauses,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> simp [clause]
  | xor =>
    simp only [Gate.clauses,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp [clause]
  | copy | inv =>
    simp only [Gate.clauses,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> simp [clause]

end Pcx293.Unit

namespace Pcx293.Selector
open PEqualNP.Outside.L_pcx_293.Pcx293.Unit
universe u
variable {V : Type u}

inductive ScanTree (V : Type u)
| tip (wire : V)
| join (wire : V) (l r : ScanTree V)

def ScanTree.root : ScanTree V → V
| .tip w | .join w _ _ => w
def ScanTree.depth : ScanTree V → Nat
| .tip _ => 0
| .join _ l r => max l.depth r.depth + 1
def ScanTree.leaf : ScanTree V → List V
| .tip w => [w]
| .join _ l r => l.leaf++r.leaf
def ScanTree.gates (join : V → V → V → Gate V) : ScanTree V → List (Gate V)
| .tip _ => []
| .join w l r => (join l.root r.root w)::(l.gates join ++ r.gates join)

def Covered (F : Form V) (g : Gate V) := ∀ c∈g.clauses, F c
def Realizes (F : Form V) (g : V → V → V → Gate V) (t : ScanTree V) :=
  ∀ op∈t.gates g,Covered F op

theorem parts {F : Form V} {g : V → V → V → Gate V} {w : V} {l r : ScanTree V}
    (covered : Realizes F g (.join w l r)) :
    Covered F (g l.root r.root w) ∧ Realizes F g l ∧ Realizes F g r := by
  exact ⟨covered _ (by simp [ScanTree.gates]),
    fun op h => covered _ (by simp [ScanTree.gates,h]), fun op h => covered _ (by simp [ScanTree.gates,h])⟩

theorem or_true {F : Form V} {S : State V} {a b c : V} (enc : Covered F (.or a b c))
    (yes : S (a,true) ∨ S (b,true)) : adv F S (c,true) := by
  rcases yes with h|h
  · exact fire₁ (enc _ (by simp [Gate.clauses])) h
  · exact fire₁ (enc _ (by simp [Gate.clauses])) h

theorem and_true {F : Form V} {S : State V} {a b c : V} (enc : Covered F (.and a b c))
    (p : S (a,true)) (q : S (b,true)) : adv F S (c,true) :=
  fire₂ (enc _ (by simp [Gate.clauses])) p q

theorem xor_mismatch {F : Form V} {S : State V} {a b c : V} (enc : Covered F (.xor a b c))
    (v : Bool) (ha : S (a,v)) (hb : S (b,!v)) : adv F S (c,true) := by
  cases v with
  | false => exact fire₂ (enc _ (by simp [Gate.clauses])) ha hb
  | true => exact fire₂ (enc _ (by simp [Gate.clauses])) ha hb

theorem some_to_root {F : Form V} {S : State V} (t : ScanTree V) (n : Nat)
    (covered : Realizes F Gate.or t) (some : ∃ w∈t.leaf,iter F S n (w,true)) :
    iter F S (n+t.depth) (t.root,true) := by
  induction t with
  | tip w =>
    rcases some with ⟨v,hv,hy⟩
    obtain rfl : v=w := by simpa [ScanTree.leaf] using hv
    exact hy
  | join w l r ihl ihr =>
    rcases parts covered with ⟨enc,cl,cr⟩
    change iter F S (n+(max l.depth r.depth+1)) (w,true)
    rw [←Nat.add_assoc]
    apply or_true enc
    rcases some with ⟨v,hv,hy⟩
    rcases List.mem_append.mp hv with left | right
    · exact .inl (keep (ihl cl ⟨v,left,hy⟩) (by omega))
    · exact .inr (keep (ihr cr ⟨v,right,hy⟩) (by omega))

theorem all_to_root {F : Form V} {S : State V} (t : ScanTree V) (n : Nat)
    (covered : Realizes F Gate.and t) (all : ∀ w∈t.leaf,iter F S n (w,true)) :
    iter F S (n+t.depth) (t.root,true) := by
  induction t with
  | tip w => exact all w (by simp [ScanTree.leaf])
  | join w l r ihl ihr =>
    rcases parts covered with ⟨enc,cl,cr⟩
    change iter F S (n+(max l.depth r.depth+1)) (w,true)
    rw [←Nat.add_assoc]
    apply and_true enc
    · exact keep (ihl cl (fun v hv => all _ (by simp [ScanTree.leaf,hv]))) (by omega)
    · exact keep (ihr cr (fun v hv => all _ (by simp [ScanTree.leaf,hv]))) (by omega)


theorem reject {I : Type u} {F : Form V} {S : State V}
    (t : ScanTree V) (n : Nat) (enc : Realizes F Gate.or t)
    (raw cand mism : I → V) (invalid : V)
    (inv_in : invalid∈t.leaf) (mm_in : ∀ i,mism i∈t.leaf)
    (cmp : ∀ i,Covered F (.xor (raw i) (cand i) (mism i)))
    (why : iter F S n (invalid,true) ∨
      ∃ i b, iter F S n (raw i,b) ∧ iter F S n (cand i,!b)) :
    iter F S (n+1+t.depth) (t.root,true) := by
  apply some_to_root t _ enc
  rcases why with iv|⟨i,b,rr,cc⟩
  · exact ⟨invalid,inv_in,keep iv (by omega)⟩
  · exact ⟨mism i,mm_in i,xor_mismatch (cmp i) b rr cc⟩


theorem conflict_of_rejects {F : Form V} {S : State V} (t : ScanTree V) (n : Nat)
    (enc : Realizes F Gate.and t) (unit : F [(t.root,false)])
    (all : ∀ w∈t.leaf,iter F S n (w,true)) :
    ∃ c,F c ∧ ∀ l∈c,iter F S (n+t.depth) (neg l) := by
  refine ⟨_,unit,?_⟩
  intro l h
  obtain rfl : l=(t.root,false) := List.mem_singleton.mp h
  exact all_to_root t n enc all


theorem forced_of_no_support {F : Form V} {S : State V} (t : ScanTree V) (n : Nat)
    (enc : Realizes F Gate.and t) (raw : V) (b : Bool)
    (conclusion : F (clause [(t.root,true)] (raw,!b)))
    (all : ∀ w∈t.leaf, ∃ dead wrong,
        Covered F (.or dead wrong w) ∧ (iter F S n (dead,true) ∨ iter F S n (wrong,true))) :
    iter F S (n+1+t.depth+1) (raw,!b) := by
  apply fire₁ conclusion
  apply all_to_root t _ enc
  intro w hw
  rcases all w hw with ⟨d,v,cv,known⟩
  exact or_true cv known

end Pcx293.Selector

namespace Pcx293.Word



def pack (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0

theorem pack_bit (n : Nat) (f : Nat → Bool) (k : Nat) :
    (pack n f).testBit k = (decide (k < n) && f k) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,List.range_succ,List.foldl_append]
    change ((pack n f) ||| ((f n).toNat <<< n)).testBit k = _
    rw [Nat.testBit_or,ih,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
    rcases Nat.lt_trichotomy k n with h|h|h
    · have h₁ : ¬k ≥ n := by omega
      have h₂ : k < n+1 := by omega
      simp [h,h₁,h₂]
    · subst n; simp
    · have h₁ : ¬k < n := by omega
      have h₂ : ¬k < n+1 := by omega
      have h₃ : k-n≠0 := by omega
      simp [h₁,h₂,h₃]

def cyc (k w i : Nat) := w.testBit (i % k)
theorem cyc_period (k w i : Nat) : cyc k w (i+k)=cyc k w i := by simp [cyc]

theorem pack_bounded (k : Nat) (f : Nat → Bool) : pack k f < 2^k := by
  have eq : pack k f % 2^k=pack k f := by
    apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_mod_two_pow,pack_bit]
    cases decide (i < k) <;> rfl
  exact eq ▸ Nat.mod_lt _ (Nat.two_pow_pos _)

theorem pack_recover {k w : Nat} (hw : w < 2^k) : pack k (cyc k w)=w := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases h : i < k
  · simp [pack_bit,cyc,h,Nat.mod_eq_of_lt h]
  · have hi : w < 2^i := Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
    simp [pack_bit,h,Nat.testBit_lt_two_pow hi]

def step (k word : Nat) := (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
theorem step_eq (k w : Nat) : step k w = pack k (fun i => xor (w.testBit i)
    (!(w.testBit ((i+1) % k)) && w.testBit ((i+2) % k))) := rfl

theorem step_bits {k : Nat} (hk : 0 < k) (w i : Nat) :
    cyc k (step k w) i = Chi.chi (cyc k w) i := by
  simp [cyc,step_eq,pack_bit,Chi.chi,Nat.mod_lt i hk]

def unstep (k w : Nat) := pack k (fun i => (Chi.scan (cyc k w) i k).bias)
theorem chi_inverse_word {k w : Nat} (odd : k % 2=1) (hw : w < 2^k) :
    unstep k (step k w)=w := by
  have hk : 0 < k := by omega
  have eq : cyc k (step k w)=Chi.chi (cyc k w) := funext (step_bits hk w)
  unfold unstep
  rw [eq]
  have id := funext (Chi.inverse_chi odd (cyc_period k w))
  rw [id,pack_recover hw]

def rot (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k-s % k))) % 2^k

theorem rot_at {k w : Nat} (hk : 0 < k) (hw : w < 2^k) (s i : Nat) :
    cyc k (rot k s w) i = cyc k w (i+(k-s % k)) := by
  let j := i % k
  let d := s % k
  have hj : j < k := Nat.mod_lt _ hk
  have hd : d < k := Nat.mod_lt _ hk
  have tr : (i+(k-d)) % k=(j+(k-d)) % k := (Nat.mod_add_mod i k _).symm
  unfold cyc rot
  change ((((w <<< d) ||| (w >>> (k-d))) % 2^k).testBit j) = w.testBit ((i+(k-d)) % k)
  rw [tr,Nat.testBit_mod_two_pow,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases h : d ≤ j
  · have eq : j+(k-d)=(j-d)+k := by omega
    have hi : w < 2^(k-d+j) := Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
    rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (show j-d < k by omega)]
    simp [hj,h,Nat.testBit_lt_two_pow hi]
  · have ht : j+(k-d) < k := by omega
    rw [Nat.mod_eq_of_lt ht,Nat.add_comm j (k-d)]
    simp [h,hj]

def mix (k d w : Nat) := w ^^^ rot k d w ^^^ rot k (k-d) w

theorem mix_bounded {k w : Nat} (hw : w < 2^k) (d : Nat) : mix k d w < 2^k :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hw (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (Nat.mod_lt _ (Nat.two_pow_pos _))

def sampled (k d w : Nat) (t : Nat) := cyc k w (d*t)
def measured (k d y : Nat) (t : Nat) := cyc k y (d*(t+1))

theorem mix_mid {k d w : Nat} (dp : 0 < d) (dk : d < k) (hw : w < 2^k) :
    measured k d (mix k d w)=Linear.mid (sampled k d w) := by
  funext t
  have hk : 0 < k := by omega
  simp only [measured,mix,cyc,Nat.testBit_xor]
  change ((cyc k w (d*(t+1)) ^^ cyc k (rot k d w) (d*(t+1))) ^^
      cyc k (rot k (k-d) w) (d*(t+1)))=_
  rw [rot_at hk hw,rot_at hk hw,Nat.mod_eq_of_lt dk,Nat.mod_eq_of_lt (show k-d < k by omega)]
  have e₁ : d*(t+1)+(k-d)=d*t+k := by rw [Nat.mul_succ];omega
  have e₂ : d*(t+1)+(k-(k-d))=d*(t+2) := by
    rw [show k-(k-d)=d by omega]; exact (Nat.mul_succ _ _).symm
  rw [e₁,cyc_period,e₂]
  unfold Linear.mid sampled
  cases cyc k w (d*t) <;> cases cyc k w (d*(t+1)) <;> cases cyc k w (d*(t+2)) <;> decide

def unsample (k d i : Nat) := if d=1 then i else if i % 2=0 then i/2 else (i+k)/2

theorem unsample_law {k d : Nat} (odd : k % 2=1) (hd : d=1 ∨ d=2) (w i : Nat) :
    sampled k d w (unsample k d i)=cyc k w i := by
  rcases hd with rfl|rfl
  · simp [sampled,unsample]
  · unfold unsample sampled
    by_cases hi : i % 2=0
    · simp [hi,show 2*(i/2)=i by omega]
    · simp [hi,show 2*((i+k)/2)=i+k by omega,cyc_period]

def gen (k d y : Nat) (p : Linear.Pair) :=
  pack k (fun i => Linear.get (measured k d y) p (unsample k d i))

theorem gen_complete {k d w : Nat} (odd : k % 2=1) (hd : d=1 ∨ d=2)
    (dk : d < k) (hw : w < 2^k) :
    ∃ p∈Linear.choices, gen k d (mix k d w) p=w := by
  have dp : 0 < d := by omega
  let x := sampled k d w
  refine ⟨(x 0,x 1),Linear.in_choices _,?_⟩
  unfold gen
  rw [mix_mid dp dk hw]
  have e : ∀ t, Linear.get (Linear.mid x) (x 0,x 1) t=x t :=
    fun t => congrArg Prod.fst (Linear.exhaustive x t)
  change pack k (fun i => Linear.get (Linear.mid x) (x 0,x 1) (unsample k d i))=w
  simp only [e]
  have z : (fun i => x (unsample k d i))=cyc k w := funext (unsample_law odd hd _)
  rw [z,pack_recover hw]

end Pcx293.Word

namespace Pcx293.Family
open PEqualNP.Outside.L_pcx_293.Pcx293.Word
abbrev Entry := Nat × Bool

def phase (k d mask w : Nat) := step k (mix k d w) ^^^ mask

theorem step_bounded (k w : Nat) : step k w < 2^k := step_eq k w ▸ pack_bounded _ _
theorem phase_bounded {k mask : Nat} (hm : mask < 2^k) (d w : Nat) : phase k d mask w < 2^k :=
  Nat.xor_lt_two_pow (step_bounded _ _) hm

def back (k d mask out : Nat) (p : Linear.Pair) :=
  gen k d (unstep k (out ^^^ mask)) p

theorem back_complete {k d mask w : Nat} (odd : k % 2=1) (hd : d=1 ∨ d=2)
    (dk : d < k) (hw : w < 2^k) :
    ∃ p∈Linear.choices,back k d mask (phase k d mask w) p=w := by
  unfold back phase
  rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  rw [chi_inverse_word odd (mix_bounded hw d)]
  exact gen_complete odd hd dk hw


def children (k d mask : Nat) (out : Entry) : List Entry :=
  Linear.choices.map fun p =>
    let z := back k d mask out.1 p
    (z,out.2 && decide (phase k d mask z=out.1))

theorem children_length (k d m : Nat) (o : Entry) : (children k d m o).length=4 := by
  simp [children,Linear.choices]

theorem children_character {k d mask w y : Nat} {ok : Bool} (odd : k % 2=1)
    (hd : d=1 ∨ d=2) (dk : d < k) :
    (w,true) ∈ children k d mask (y,ok) ↔ ok=true ∧ w < 2^k ∧ phase k d mask w=y := by
  simp only [children,List.mem_map]
  constructor
  · rintro ⟨p,hp,e⟩
    have ew := congrArg Prod.fst e
    have ev := congrArg Prod.snd e
    change back k d mask y p=w at ew
    change (ok && decide (phase k d mask (back k d mask y p)=y))=true at ev
    rw [ew] at ev
    rw [Bool.and_eq_true] at ev
    rcases ev with ⟨o,v⟩
    refine ⟨o,?_,of_decide_eq_true v⟩
    rw [←ew]; apply pack_bounded
  · rintro ⟨rfl,hw,eq⟩
    subst y
    rcases back_complete (mask:=mask) odd hd dk hw with ⟨p,hp,he⟩
    exact ⟨p,hp,by simp [he]⟩

def direct (k d : Nat) (masks : List Nat) (x : Nat) :=
  masks.foldl (fun w a => phase k d a w) x


def all (k d : Nat) : List Nat → Entry → List Entry
| [],o => [o]
| m::ms,o => (all k d ms o).flatMap (children k d m)

theorem all_length (k d : Nat) (ms : List Nat) (o : Entry) :
    (all k d ms o).length=4^ms.length := by
  have flat (m : Nat) (xs : List Entry) :
      (xs.flatMap (children k d m)).length=xs.length*4 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [children_length,ih];omega
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [all,flat,ih,Nat.pow_succ]

theorem all_valid {k d : Nat} (odd : k % 2=1) (hd : d=1 ∨ d=2) (dk : d < k)
    (ms : List Nat) (hb : ∀ m∈ms,m < 2^k) {y : Nat} (hy : y < 2^k) {ok : Bool} (w : Nat) :
    (w,true)∈all k d ms (y,ok) ↔ ok=true ∧ w < 2^k ∧ direct k d ms w=y := by
  induction ms generalizing w with
  | nil =>
    simp only [all,List.mem_singleton,direct,List.foldl_nil,Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,rfl⟩;exact ⟨rfl,hy,rfl⟩
    · rintro ⟨rfl,_,rfl⟩;exact ⟨rfl,rfl⟩
  | cons m ms ih =>
    have rest : ∀ j∈ms,j < 2^k := fun j h => hb _ (List.mem_cons_of_mem _ h)
    have hm : m < 2^k := hb _ (by simp)
    simp only [all,List.mem_flatMap]
    constructor
    · rintro ⟨⟨z,v⟩,hz,inc⟩
      rcases (children_character odd hd dk).mp inc with ⟨rfl,hw,ph⟩
      rcases (ih rest z).mp hz with ⟨o,_,eq⟩
      exact ⟨o,hw,by simpa [direct,←ph] using eq⟩
    · rintro ⟨o,hw,eq⟩
      let z := phase k d m w
      have zi : (z,true) ∈ all k d ms (y,ok) :=
        (ih rest z).mpr ⟨o,phase_bounded hm _ _,eq⟩
      exact ⟨(z,true),zi,(children_character odd hd dk).mpr ⟨rfl,hw,rfl⟩⟩

def names (k d init : Nat) (masks : List Nat) (out : Nat) := (all k d masks (out,true)).map
  (fun p => (init ^^^ p.1,p.2))
theorem names_complete {k d init : Nat} (odd : k % 2=1) (hd : d=1 ∨ d=2) (dk : d < k)
    (masks : List Nat) (hb : ∀ m∈masks,m < 2^k) {y : Nat} (hy : y < 2^k)
    (key : init < 2^k) (name : Nat) :
    (name,true)∈names k d init masks y ↔ name < 2^k ∧ direct k d masks (init ^^^ name)=y := by
  simp only [names,List.mem_map]
  constructor
  · rintro ⟨⟨w,b⟩,hw,eq⟩
    change (init ^^^ w,b) = (name,true) at eq
    rw [Prod.mk.injEq] at eq
    obtain ⟨nam,rfl⟩ := eq
    rw [←nam]; simp only [←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]
    rcases (all_valid odd hd dk masks hb hy w).mp hw with ⟨_,wb,direc⟩
    exact ⟨Nat.xor_lt_two_pow key wb,direc⟩
  · rintro ⟨hn,h⟩
    let w := init ^^^ name
    exact ⟨(w,true),(all_valid odd hd dk masks hb hy w).mpr
      ⟨rfl,Nat.xor_lt_two_pow key hn,h⟩,by simp [w,←Nat.xor_assoc]⟩

end Pcx293.Family

namespace Pcx293.Tracks
open PEqualNP.Outside.L_pcx_293.Pcx293.Word PEqualNP.Outside.L_pcx_293.Pcx293.Family

def constant (k j : Nat) := 3^(k+j) % 2^k
def rowMask (k key j : Nat) := rot k (2*j) key ^^^ constant k (j+1)
def colMask (k r key j : Nat) := rot k (3*(j+1)+1) key ^^^ constant k (r+(j+1))

def first (k r key name : Nat) :=
  (List.range r).foldl (fun rowState rowIndex =>
    step k (rowState ^^^ rot k 1 rowState ^^^ rot k (k-1) rowState) ^^^
      rot k (2*rowIndex) key ^^^ constant k (rowIndex+1)) (rot k 1 key ^^^ name)

def second (k r key name : Nat) :=
  (List.range r).foldl (fun colState colIndex =>
    step k (colState ^^^ rot k 2 colState ^^^ rot k (k-2) colState) ^^^
      rot k (3*(colIndex+1)+1) key ^^^ constant k (r+(colIndex+1))) (rot k 3 key ^^^ name)

def rowNames (k r key out : Nat) :=
  names k 1 (rot k 1 key) ((List.range r).map (rowMask k key)) out
def colNames (k r key out : Nat) :=
  names k 2 (rot k 3 key) ((List.range r).map (colMask k r key)) out

theorem first_eq (k r key name : Nat) : first k r key name =
    direct k 1 ((List.range r).map (rowMask k key)) (rot k 1 key ^^^ name) := by
  simp [first,direct,List.foldl_map,phase,mix,rowMask,Nat.xor_assoc]

theorem second_eq (k r key name : Nat) : second k r key name =
    direct k 2 ((List.range r).map (colMask k r key)) (rot k 3 key ^^^ name) := by
  simp [second,direct,List.foldl_map,phase,mix,colMask,Nat.xor_assoc]

theorem rot_bounded (k s w : Nat) : rot k s w < 2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem const_bounded (k j : Nat) : constant k j < 2^k := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem posted_row {k r key out : Nat} (h : k % 6=3) (bound : out < 2^k) (x : Nat) :
    (x,true)∈rowNames k r key out ↔ x < 2^k ∧ first k r key x=out := by
  rw [first_eq]
  apply names_complete (by omega) (.inl rfl) (by omega) _ _ bound (rot_bounded ..)
  intro m hm
  rcases List.mem_map.mp hm with ⟨j,_,rfl⟩
  exact Nat.xor_lt_two_pow (rot_bounded ..) (const_bounded ..)

theorem posted_col {k r key out : Nat} (h : k % 6=3) (bound : out < 2^k) (x : Nat) :
    (x,true)∈colNames k r key out ↔ x < 2^k ∧ second k r key x=out := by
  rw [second_eq]
  apply names_complete (by omega) (.inr rfl) (by omega) _ _ bound (rot_bounded ..)
  intro m hm
  rcases List.mem_map.mp hm with ⟨j,_,rfl⟩
  exact Nat.xor_lt_two_pow (rot_bounded ..) (const_bounded ..)

theorem both_lengths (k r key o₁ o₂ : Nat) :
    (rowNames k r key o₁).length=4^r ∧ (colNames k r key o₂).length=4^r := by
  simp [rowNames,colNames,names,all_length]

end Pcx293.Tracks

namespace Pcx293.Budget


def internal : Nat → Nat
| 0 => 0
| r+1 => 1+4*internal r

theorem geometric (r : Nat) : 3*internal r+1=4^r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Nat.pow_succ,internal];omega


def roundGates (k : Nat) := k+3*(5*k-3)+4*k+4*(6*k)
theorem round_le (k : Nat) : roundGates k ≤ 44*k := by unfold roundGates;omega


def leafGates (k n : Nat) := 3*k*n+2*k*n+2*k*(n-1)+(n-1)
theorem leaf_le (k n : Nat) : leafGates k n ≤ (7*k+1)*n := by
  have bound := Nat.mul_le_mul_left (2*k) (Nat.sub_le n 1)
  unfold leafGates
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at *
  omega

def allGates (k r : Nat) := 2*(roundGates k*internal r+leafGates k (4^r))
theorem gates_le (k r : Nat) : allGates k r ≤ (44*k+2)*4^r := by
  have collect := geometric r
  have first := Nat.mul_le_mul_right (internal r) (round_le k)
  have second := leaf_le k (4^r)
  have ent : (44*k)*internal r ≤ (15*k)*4^r := by
    rw [←collect,Nat.mul_add,Nat.mul_one,Nat.mul_left_comm (15*k) 3,←Nat.mul_assoc 3 (15*k)]
    have mu : 44*k ≤ 3*(15*k) := by omega
    have zz := Nat.mul_le_mul_right (internal r) mu
    omega
  unfold allGates
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at *
  omega


def total (k r : Nat) := 13*allGates k r+8*k+4

theorem literal_budget (k r : Nat) : total k r ≤ 8192*(k+1)*4^r := by
  have h := gates_le k r
  have p : 1 ≤ 4^r := Nat.one_le_pow _ _ (by decide)
  have q := Nat.mul_le_mul_left k p
  unfold total
  simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one,Nat.mul_assoc] at *
  omega


def ticks (r L : Nat) := 1+r*(7*L+13)+2*L+2*r+8
theorem round_budget (r L : Nat) : ticks r L ≤ 128*(r+1)*(L+1) := by
  simp only [ticks,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one,Nat.mul_assoc,
    Nat.mul_left_comm r 7,Nat.mul_comm r 13]
  omega

end Pcx293.Budget

namespace Pcx293.Wire
open PEqualNP.Outside.L_pcx_293.Pcx293.Unit
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}


def value (s : A → Bool) (p : Lit A) : Bool := s p.1 == p.2

theorem signed_true (s : A → Bool) (p : Lit A) : value s p=true ↔ s p.1=p.2 := by simp [value]
@[local simp] theorem value_neg (s : A → Bool) (p : Lit A) : value s (neg p)= !value s p := by
  rcases p with ⟨a,v⟩; cases h : s a <;> cases v <;> simp [value,neg,h]


def signmap (f : A → Lit B) (p : Lit A) : Lit B := if p.2 then f p.1 else neg (f p.1)
@[local simp] theorem signmap_neg (f : A → Lit B) (p : Lit A) : signmap f (neg p)=neg (signmap f p) := by
  rcases p with ⟨a,v⟩; cases v <;> simp [signmap,neg]

theorem signmap_eval (s : B → Bool) (f : A → Lit B) (p : Lit A) :
    value s (signmap f p)=value (fun a => value s (f a)) p := by
  rcases p with ⟨a,b⟩
  cases b with
  | false =>
    change value s (neg (f a)) = (value s (f a) == false)
    rw [value_neg]; cases value s (f a) <;> rfl
  | true =>
    change value s (f a) = (value s (f a) == true)
    cases value s (f a) <;> rfl

def transClause (f : A → Lit B) (c : Clause A) : Clause B := c.map (signmap f)
def transForm (f : A → Lit B) (F : Form A) (d : Clause B) := ∃ c,F c ∧ transClause f c=d

theorem transported_models (s : B → Bool) (f : A → Lit B) (F : Form A) :
    Sat (transForm f F) s ↔ Sat F (fun a => value s (f a)) := by
  constructor
  · intro ok c fc
    rcases ok (transClause f c) ⟨c,fc,rfl⟩ with ⟨d,hd,sd⟩
    rcases List.mem_map.mp hd with ⟨a,ha,rfl⟩
    exact ⟨a,ha,(signed_true _ _).mp (signmap_eval s f a ▸ (signed_true _ _).mpr sd)⟩
  · rintro ok _ ⟨c,fc,rfl⟩
    rcases ok _ fc with ⟨a,ha,sa⟩
    exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,(signed_true _ _).mp
      ((signmap_eval s f a).symm ▸ (signed_true _ _).mpr sa)⟩

theorem transported_steps {F : Form A} {G : Form B} (f : A → Lit B)
    (included : ∀ c,F c → G (transClause f c)) {S : State A} {T : State B}
    (seeded : ∀ p,S p → T (signmap f p)) (j n : Nat) (ctx : ∀ p,T p → iter G T j p) (q : Lit A) :
    iter F S n q → iter G T (j+n) (signmap f q) := by
  induction n generalizing q with
  | zero => intro h; exact ctx _ (seeded _ h)
  | succ n ih =>
    rintro (old|⟨c,fc,qc,needed⟩)
    · exact .inl (ih q old)
    · apply Or.inr
      refine ⟨transClause f c,included _ fc,List.mem_map.mpr ⟨q,qc,rfl⟩,?_⟩
      intro z hz neq
      rcases List.mem_map.mp hz with ⟨p,hp,rfl⟩
      have diff : p≠q := fun eq => neq (congrArg _ eq)
      have val := ih (neg p) (needed _ hp diff)
      rw [←signmap_neg]; exact val

theorem shift_steps {F : Form A} {G : Form B} (f : A → Lit B)
    (included : ∀ c,F c → G (transClause f c)) {S : State A} {T : State B}
    (j : Nat) (seeded : ∀ p,S p → iter G T j (signmap f p)) (n : Nat) (q : Lit A) :
    iter F S n q → iter G T (j+n) (signmap f q) := by
  induction n generalizing q with
  | zero => exact seeded q
  | succ n ih =>
    rintro (old|⟨c,fc,qc,needed⟩)
    · exact .inl (ih q old)
    · apply Or.inr
      refine ⟨transClause f c,included _ fc,List.mem_map.mpr ⟨q,qc,rfl⟩,?_⟩
      intro z hz neq
      rcases List.mem_map.mp hz with ⟨p,hp,rfl⟩
      have diff : p≠q := fun eq => neq (congrArg _ eq)
      rw [←signmap_neg]; exact ih (neg p) (needed _ hp diff)

end Pcx293.Wire

namespace Pcx293.Tape
open PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Wire
universe u
abbrev Vars (I : Type u) (n : Nat) := Sum I (Fin n)
abbrev Ref (I : Type u) (n : Nat) := Lit (Vars I n)

inductive Op | band | bor | bxor

def Op.eval (op : Op) (a b : Bool) : Bool :=
  match op with | .band => a && b | .bor => a || b | .bxor => a ^^ b

def Op.g (op : Op) : Gate (Fin 3) :=
  match op with | .band => .and 0 1 2 | .bor => .or 0 1 2 | .bxor => .xor 0 1 2


inductive P (I : Type u) : Nat → Type u
| empty : P I 0
| push : P I n → Op → Ref I n → Ref I n → P I (n+1)

variable {I : Type u} {n : Nat}
def liftV : Vars I n → Vars I (n+1) := Sum.map id Fin.castSucc
def liftR (r : Ref I n) : Ref I (n+1) := (liftV r.1,r.2)
def last : Ref I (n+1) := (.inr (Fin.last n),true)

def ports (a b : Ref I n) (j : Fin 3) : Ref I (n+1) :=
  if j=0 then liftR a else if j=1 then liftR b else last

def pcs (op : Op) (a b : Ref I n) :=
  op.g.clauses.map (transClause (ports a b))

def P.cnf : {n : Nat} → P I n → List (Clause (Vars I n))
| _, .empty => []
| _, .push p op a b => p.cnf.map (List.map liftR) ++ pcs op a b

def env (v : I → Bool) (x : Fin n → Bool) : Vars I n → Bool := Sum.elim v x

def ext (x : Fin n → Bool) (lastVal : Bool) (j : Fin (n+1)) :=
  if h : j.val < n then x ⟨j.val,h⟩ else lastVal

theorem ext_old (x : Fin n → Bool) (b : Bool) (i : Fin n) : ext x b i.castSucc=x i := by simp [ext,i.isLt]
theorem ext_new (x : Fin n → Bool) (b : Bool) : ext x b (Fin.last n)=b := by simp [ext]
theorem env_lift (v : I → Bool) (x : Fin n → Bool) (b : Bool) (i : Vars I n) :
    env v (ext x b) (liftV i)=env v x i := by cases i <;> simp [env,liftV,ext_old]
theorem val_lift (v : I → Bool) (x : Fin n → Bool) (b : Bool) (r : Ref I n) :
    value (env v (ext x b)) (liftR r)=value (env v x) r := by simp [value,liftR,env_lift]

def P.run (v : I → Bool) : {n : Nat} → P I n → Fin n → Bool
| _, .empty => Fin.elim0
| _, .push p op a b => let x:=p.run v;ext x (op.eval (value (env v x) a) (value (env v x) b))

theorem appended_evaluation (v : I → Bool) (x : Fin n → Bool) (op : Op) (a b : Ref I n)
    (z : Bool) : Sat (fun c => c∈pcs op a b) (env v (ext x z)) ↔
      z=op.eval (value (env v x) a) (value (env v x) b) := by
  let f := ports a b
  let F := fun c => c∈op.g.clauses
  have eq : (fun c => c∈pcs op a b) = transForm f F := by
    funext c; apply propext; exact List.mem_map
  rw [eq,transported_models,Gate.sat_iff]
  have e₀ : value (env v (ext x z)) (f 0)=value (env v x) a := val_lift .. 
  have e₁ : value (env v (ext x z)) (f 1)=value (env v x) b := val_lift ..
  have e₂ : value (env v (ext x z)) (f 2)=z := by
    change (ext x z (Fin.last n) == true)=z
    rw [ext_new];cases z <;>rfl
  cases op <;> simp only [Op.g,Gate.Holds,Op.eval,e₀,e₁,e₂]

theorem prior_evaluation (v : I → Bool) (x : Fin n → Bool) (z : Bool) (p : P I n) :
    Sat (fun c => c∈p.cnf.map (List.map liftR)) (env v (ext x z)) ↔
    Sat (fun c => c∈p.cnf) (env v x) := by
  constructor
  · intro ok c hc
    rcases ok _ (List.mem_map.mpr ⟨c,hc,rfl⟩) with ⟨q,hq,eq⟩
    rcases List.mem_map.mp hq with ⟨l,hl,rfl⟩
    exact ⟨l,hl,(env_lift v x z l.1) ▸ eq⟩
  · rintro ok _ ht
    rcases List.mem_map.mp ht with ⟨c,hc,rfl⟩
    rcases ok _ hc with ⟨l,hl,yes⟩
    exact ⟨liftR l,List.mem_map.mpr ⟨_,hl,rfl⟩,(env_lift v x z l.1).symm ▸ yes⟩

theorem sat_append {U : Type u} (s : U → Bool) (f g : List (Clause U)) :
    Sat (fun c => c∈f++g) s ↔ (Sat (fun c=>c∈f) s ∧ Sat (fun c=>c∈g) s) := by
  constructor
  · intro h
    exact ⟨fun c hc=>h c (by simp [hc]),fun c hc=>h c (by simp [hc])⟩
  · rintro ⟨a,b⟩ c hc
    rcases List.mem_append.mp hc with h|h
    · exact a c h
    · exact b c h

theorem ext_split (x : Fin (n+1) → Bool) :
    ext (fun i=>x i.castSucc) (x (Fin.last n))=x := by
  funext j
  by_cases h : j.val < n
  · simp [ext,h]
  · have eq : j=Fin.last n := Fin.ext (by have := j.isLt; simp;omega)
    subst j; exact ext_new ..


theorem unique_aux (p : P I n) (v : I → Bool) (x : Fin n → Bool) :
    Sat (fun c => c∈p.cnf) (env v x) ↔ x=p.run v := by
  induction p with
  | empty =>
    constructor
    · intro _;funext i;exact Fin.elim0 i
    · intros; intro c hc;cases hc
  | push p op a b ih =>
    let y := fun (i : Fin _) => x i.castSucc
    let z := x (Fin.last _)
    have split : ext y z=x := ext_split x
    have hm : Sat (fun c => c∈(P.push p op a b).cnf) (env v (ext y z)) ↔
        ext y z=(P.push p op a b).run v := by
      rw [P.cnf,sat_append,prior_evaluation,appended_evaluation,ih y]
      change (_ ∧ _) ↔ ext y z=ext (p.run v) _
      constructor
      · rintro ⟨hy,hz⟩;rw [hy] at hz;rw [hy,hz]
      · intro hh
        have eq (i : Fin _) := congrFun hh i.castSucc
        have hy : y=p.run v := funext (fun i=>by simpa [ext_old] using eq i)
        have endEq := congrFun hh (Fin.last _)
        exact ⟨hy,by simpa only [ext_new,hy] using endEq⟩
    simpa only [split] using hm

def litWeight {U} (f : List (Clause U)) := (f.map List.length).sum
theorem map_weight {A : Type u} {B : Type v} (ls : List (Clause A)) (lift : Lit A → Lit B) :
    litWeight (ls.map (List.map lift))=litWeight ls := by
  induction ls with
  | nil => rfl
  | cons a as ih => simpa [litWeight] using congrArg ((a.length)+·) ih

theorem append_weight {U} (a b : List (Clause U)) :
    litWeight (a++b)=litWeight a+litWeight b := by simp [litWeight]

theorem weight (p : P I n) : litWeight p.cnf ≤ 12*n := by
  induction p with
  | empty => simp [P.cnf,litWeight]
  | push p op a b ih =>
    rw [P.cnf,append_weight,map_weight]
    have eq : litWeight (pcs op a b)=op.g.weight := map_weight op.g.clauses _
    rw [eq]
    have := Gate.weight_le op.g
    omega

theorem width (p : P I n) (c : Clause (Vars I n)) (hc : c∈p.cnf) : c.length ≤ 3 := by
  induction p with
  | empty => cases hc
  | push p op a b ih =>
    rcases List.mem_append.mp hc with h|h
    · rcases List.mem_map.mp h with ⟨l,hl,rfl⟩;simpa using ih l hl
    · rcases List.mem_map.mp h with ⟨l,hl,rfl⟩
      simpa [transClause] using Gate.width_le op.g l hl

end Pcx293.Tape

namespace Pcx293.Make
open PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Wire
open PEqualNP.Outside.L_pcx_293.Pcx293.Tape (Op)
abbrev W := Lit Nat
abbrev Vec := List W
abbrev A2 := W × W
def pos (i : Nat) : W := (i,true)
structure Line where
  id : Nat
  op : Op
  a : W
  b : W
structure Net where
  n : Nat := 0
  lines : List Line := []
  constraints : List (Clause Nat) := []
  high : Nat := 0
  ordered : ∀ l∈lines, l.id ≤ high ∧ l.a.1 < l.id ∧ l.b.1 < l.id ∧ l.id % 2=1 := by simp_all
  nodup : (lines.map Line.id).Nodup := by simp_all
  slots : lines.length ≤ n := by simp_all
  thin : ∀ c∈constraints,c.length ≤ 3 := by simp_all
abbrev B := StateM Net

def nextId (s : Net) (a b : W) := 2*((max s.high (max a.1 b.1))/2 + 1)+1
def inserted (s : Net) (op : Op) (a b : W) : Net :=
  let i:=nextId s a b
  have hi : s.high < i ∧ a.1 < i ∧ b.1 < i ∧ i % 2=1 := by dsimp [i,nextId];omega
  { n:=s.n+1,lines:=⟨i,op,a,b⟩::s.lines,constraints:=s.constraints,high:=i,
    ordered:=by
      rintro l mem
      rcases List.mem_cons.mp mem with rfl|h
      · exact ⟨Nat.le_refl _,hi.2⟩
      · obtain ⟨atMost,ha,hb,hodd⟩:=s.ordered l h
        exact ⟨by omega,ha,hb,hodd⟩,
    nodup:=by
      apply List.nodup_cons.mpr
      refine ⟨?_,s.nodup⟩
      intro m;rcases List.mem_map.mp m with ⟨l,hl,eq⟩
      have le:=(s.ordered l hl).1
      change l.id=i at eq;omega,
    slots:=Nat.add_le_add_right s.slots 1,thin:=s.thin }

def emit (op : Op) (a b : W) : B W := do
  let s←get
  set (inserted s op a b)
  return pos (nextId s a b)

def add (c : Clause Nat) : B Unit := modify fun s=>
  {s with
    constraints := (c.take 3)::s.constraints
    thin := by
      intro g mg
      rcases List.mem_cons.mp mg with rfl|m
      · simp only [List.length_take];omega
      · exact s.thin _ m }
def lineF (l : Line) : List (Clause Nat) := l.op.g.clauses.map
  (transClause (fun j : Fin 3=>if j=0 then l.a else if j=1 then l.b else pos l.id))

def Net.form (s : Net) := s.constraints ++ s.lines.flatMap lineF


inductive ScanTree (A : Type)
| tip (x : A)
| node (l r : ScanTree A)

def shape (f : Nat → A) (start n : Nat) : ScanTree A :=
  if n ≤ 1 then .tip (f start) else
    .node (shape f start (n/2)) (shape f (start+n/2) (n-n/2))
termination_by n
decreasing_by all_goals omega

inductive Cached (A : Type)
| leaf (a : A)
| node (prod : A) (l r : Cached A)
def Cached.prod : Cached A → A
| .leaf x | .node x _ _ => x

def build (op : A → A → B A) : ScanTree A → B (Cached A)
| .tip x => pure (.leaf x)
| .node l r => do
  let l←build op l;let r←build op r;let v←op l.prod r.prod
  return .node v l r

def down (op : A → A → B A) (id : A) (rot : Bool) : Cached A → A → A → B (List A)
| .leaf x, bef,aft => do
  if rot then return [←op x (←op aft bef)] else return [bef]
| .node _ l r,bef,aft => do
  let la←if rot then op r.prod aft else pure id
  let rb←op bef l.prod
  let first←down op id rot l bef la
  let second←down op id rot r rb aft
  return first++second

def scan (op : A → A → B A) (id : A) (v : List A) (rot : Bool) : B (List A) := do
  if v.isEmpty then return []
  let t←build op (shape (fun i=>v.getD i id) 0 v.length)
  down op id rot t id id

def reduce (op : Op) (id : W) (v : Vec) : B W := do
  if v.isEmpty then return id
  let t←build (emit op) (shape (fun i=>v.getD i id) 0 v.length)
  return t.prod

def byIndex (n : Nat) (f : Nat → B A) := (List.range n).mapM f

def inverseChi (k : Nat) (one zero : W) (y : Vec) : B Vec := do
  let ord : List A2 := (List.range k).map fun t =>
    (y.getD ((2*t) % k) zero,neg (y.getD ((2*t+1) % k) zero))
  let compose : A2 → A2 → B A2 := fun p q => do
    let b←emit .bxor p.1 (←emit .band p.2 q.1)
    return (b,←emit .band p.2 q.2)
  let vals←scan compose (zero,one) ord true
  return (List.range k).map fun i=>
    (vals.getD (if i % 2=0 then i/2 else (i+k)/2) (zero,one)).1

def rot (k : Nat) (zero : W) (v : Vec) (s : Nat) : Vec :=
    (List.range k).map fun i=>v.getD ((i+(k-s % k)) % k) zero

def raw (k t : Nat) := (List.range k).map (fun i=>pos (2*(k*t+i)))
def vX (k : Nat) (z : W) (a b : Vec) : B Vec := byIndex k fun i=>emit .bxor (a.getD i z) (b.getD i z)

def check (k d : Nat) (_one zero : W) (w y : Vec) : B W := do
  let us←vX k zero (←vX k zero w (rot k zero w d)) (rot k zero w (k-d))
  let bad←byIndex k fun i=>do
    let v←emit .band (neg (us.getD ((i+1) % k) zero)) (us.getD ((i+2) % k) zero)
    let bit←emit .bxor (us.getD i zero) v
    emit .bxor bit (y.getD i zero)
  reduce .bor zero bad

def indices (k q : Nat) := (List.range (k/3)).map (fun t=>q+3*t)
abbrev Entry := Vec × W

def coordSide (k : Nat) (zero : W) (u : Nat → W) (q : Nat) : B Vec := do
  let dif←(indices k q).mapM (fun t=>emit .bxor (u t) (u (t+1)))
  let pre←scan (emit .bxor) zero dif false
  pre.mapM (fun e=>emit .bxor (if q=2 then u 0 else zero) e)

def signs : List (Bool×Bool) := [(false,false),(false,true),(true,false),(true,true)]
def child (k d : Nat) (one zero dead : W) (y : Vec) (sides : List Vec) (sg : Bool×Bool) : B Entry := do
  let w := (List.range k).map fun i=>
    let t := if d=1 then i else if i % 2=0 then i/2 else (i+k)/2
    let s := (sides.getD (t % 3) []).getD (t/3) zero
    if (if t % 3=0 then sg.1 else if t % 3=1 then sg.2 else xor sg.1 sg.2) then Pcx293.Unit.neg s else s
  let bad←check k d one zero w y
  return (w,←emit .bor dead bad)

def expand (k d : Nat) (one zero : W) (p : Entry) (mask : Vec) : B (List Entry) := do
  let y←vX k zero p.1 mask
  let z←inverseChi k one zero y
  let u := fun t=>z.getD ((d*(t+1)) % k) zero
  let sides←byIndex 3 (coordSide k zero u)
  signs.mapM (child k d one zero p.2 y sides)

def mask (k r d j : Nat) (z : W) (key : Vec) : Vec :=
  let rk := rot k z key (if d=1 then 2*j else 3*(j+1)+1)
  let c := 3^(k+(if d=1 then j+1 else r+(j+1))) % 2^k
  (List.range k).map (fun i=>let b:=rk.getD i z;if c.testBit i then neg b else b)

def genLayers (k r d : Nat) (one zero : W) (key : Vec) :
    List Nat → List Entry → B (List Entry)
| [],nodes => pure nodes
| j::js,nodes => do
  let m:=mask k r d j zero key
  let kids←nodes.mapM (fun p=>expand k d one zero p m)
  genLayers k r d one zero key js kids.flatten

def filterName (k : Nat) (zero : W) (init name : Vec) (p : Entry) : B Entry := do
  let pred←vX k zero p.1 init
  let mm←vX k zero name pred
  return (pred,←reduce .bor zero (p.2::mm))

def block (_k : Nat) (one zero : W) (name : Vec) (labels : List Entry) (i : Nat) (sign : Bool) : B Unit := do
  let flags←labels.mapM (fun p=>do
    let lit:=p.1.getD i zero
    emit .bor p.2 (if sign then neg lit else lit))
  let none←reduce .band one flags
  let b:=name.getD i zero
  add [neg none,if sign then neg b else b]

def track (k r d : Nat) (one zero : W) : B Unit := do
  let key:=raw k 2
  let init:=rot k zero key (if d=1 then 1 else 3)
  let name:=raw k (d-1)
  let nodes←genLayers k r d one zero key (List.range r).reverse [(raw k (d+2),zero)]
  let labels←nodes.mapM (filterName k zero init name)
  let allBad←reduce .band one (labels.map Prod.snd)
  add [neg allBad]
  let _←(List.range k).mapM (fun i=>do
    block k one zero name labels i false
    block k one zero name labels i true)
  pure ()

def make (k r : Nat) : Net := Id.run do
  let s : Net := {n:=5*k+1}
  let one:=pos (2*(5*k))
  let m : B Unit := do
    track k r 1 one (neg one)
    track k r 2 one (neg one)
    add [one]
  return (m.run s).2

def total (k r : Nat) :=
  let s:=make k r
  (s.n-5*k,(s.form.map List.length).sum)
end Pcx293.Make

namespace Pcx293.MCost
open PEqualNP.Outside.L_pcx_293.Pcx293.Make
def score (s : Net) := s.n+12*s.lines.length + (s.constraints.map List.length).sum
def Cost (m : B A) (c : Nat) (P : A → Prop) :=
  ∀ s, score (m.run s).2 ≤ score s+c ∧ P (m.run s).1

theorem ret (x : A) {P : A → Prop} (h : P x) : Cost (pure x) 0 P := fun _=>⟨Nat.le_refl _,h⟩
theorem bind {m : B A} {f : A → B D} {a b : Nat} {P : A → Prop} {Q : D → Prop}
    (h : Cost m a P) (g : ∀ v,P v → Cost (f v) b Q) : Cost (m >>= f) (a+b) Q := by
  intro s
  rcases h s with ⟨s₀,p⟩
  rcases g (m.run s).1 p (m.run s).2 with ⟨s₁,q⟩
  refine ⟨?_,q⟩
  change score ((f (m.run s).1).run (m.run s).2).2 ≤ score s+(a+b)
  omega

theorem weaken {m : B A} {a b : Nat} {P Q : A → Prop} (h : Cost m a P) (ab : a ≤ b)
    (pq : ∀ x,P x → Q x) : Cost m b Q := by
  intro s;rcases h s with ⟨sz,v⟩;exact ⟨by omega,pq _ v⟩

theorem one (op : Tape.Op) (a b : W) : Cost (emit op a b) 13 (fun _=>True) := by
  intro s
  refine ⟨?_,trivial⟩
  change s.n+1+12*(s.lines.length+1)+(s.constraints.map List.length).sum ≤ score s+13
  unfold score;omega

theorem add_cost (c : Pcx293.Unit.Clause Nat) : Cost (add c) c.length (fun _=>True) := by
  intro s; refine ⟨?_,trivial⟩
  change s.n+12*s.lines.length+((c.take 3).length+(s.constraints.map List.length).sum) ≤ score s+c.length
  simp only [List.length_take];unfold score;omega

theorem mapM (xs : List A) (f : A → B D) (n : Nat) (P : D → Prop)
    (h : ∀ x∈xs,Cost (f x) n P) :
    Cost (xs.mapM f) (xs.length*n) (fun ys=>ys.length=xs.length ∧ ∀ y∈ys,P y) := by
  induction xs with
  | nil => intro s;exact ⟨by change score s ≤ score s+0*n; simp,rfl,by intro y (hy : y ∈ ([] : List D)); cases hy⟩
  | cons x xs ih =>
    rw [List.mapM_cons]
    have h0 := h x (by simp)
    have h1 := ih (fun a ha=>h a (by simp [ha]))
    apply weaken (bind h0 (fun y py=>bind h1 (fun ys pys=>ret (y::ys) (P:=fun zs=>zs.length=(x::xs).length ∧ ∀ z∈zs,P z) (by
      rcases pys with ⟨e,all⟩
      exact ⟨by simp [e],fun z hz=>by rcases List.mem_cons.mp hz with rfl|r;exact py;exact all _ r⟩))))
    · simp [Nat.succ_mul,Nat.add_comm]
    · exact fun _ hx=>hx

def leaves : ScanTree A → Nat | .tip _=>1 | .node a b=>leaves a+leaves b
def height : ScanTree A → Nat | .tip _=>0 | .node a b=>max (height a) (height b)+1
def csv : Cached A → Nat | .leaf _=>1 | .node _ a b=>csv a+csv b
theorem positive (t : ScanTree A) : 0 < leaves t := by
  induction t with
  | tip => exact Nat.zero_lt_one
  | node a b ha hb => simp [leaves];omega
theorem cpos (t : Cached A) : 0 < csv t := by
  induction t with
  | leaf => exact Nat.zero_lt_one
  | node x a b ha hb => simp [csv];omega

theorem shape_leaves (f : Nat → A) (s n : Nat) (h : 0 < n) : leaves (shape f s n)=n := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    rw [shape]
    split
    · change 1=n;omega
    · change leaves (shape f s (n/2)) + leaves (shape f (s+n/2) (n-n/2)) = n
      rw [ih _ (by omega) _ (by omega),ih _ (by omega) _ (by omega)]
      omega

theorem shape_height (f : Nat → A) (s n h : Nat) (cap : n ≤ 2^h) : height (shape f s n) ≤ h := by
  induction h generalizing s n with
  | zero =>
    have sn : n ≤ 1 := cap
    rw [shape,if_pos sn];exact Nat.le_refl _
  | succ h ih =>
    rw [shape]
    split
    · exact Nat.zero_le _
    · change max (height (shape f s (n/2))) (height (shape f (s+n/2) (n-n/2)))+1 ≤ h+1
      rw [Nat.pow_succ] at cap
      exact Nat.add_le_add_right (Nat.max_le.mpr ⟨ih _ _ (by omega),ih _ _ (by omega)⟩) 1

theorem build_cost (op : A → A → B A) (b : Nat) (ho : ∀ a c,Cost (op a c) b (fun _=>True)) (t : ScanTree A) :
    Cost (build op t) ((leaves t-1)*b) (fun z=>csv z=leaves t) := by
  induction t with
  | tip x => intro s; exact ⟨by change score s ≤ score s+0*b; simp,rfl⟩
  | node l r hl hr =>
    simp only [build]
    apply weaken (bind hl (fun lc lh=>bind hr (fun rc rh=>bind (ho lc.prod rc.prod)
      (fun v _=>ret (Cached.node v lc rc) (P:=fun z=>csv z=leaves (.node l r)) (by simp [csv,leaves,lh,rh])))))
    · have pl := positive l;have pr := positive r
      have eq : leaves (.node l r)-1=(leaves l-1)+(leaves r-1)+1 := by simp [leaves];omega
      rw [eq,Nat.add_mul,Nat.add_mul,Nat.one_mul];omega
    · exact fun _ hx=>hx


theorem down_cost (op : A → A → B A) (z : A) (b : Nat) (ho : ∀ a c,Cost (op a c) b (fun _=>True))
    (rot : Bool) (t : Cached A) (bef aft : A) :
    Cost (down op z rot t bef aft)
      ((if rot then 4*csv t-2 else csv t-1)*b) (fun xs=>xs.length=csv t) := by
  induction t generalizing bef aft with
  | leaf x =>
    cases rot with
    | false => intro s; exact ⟨by change score s ≤ score s+0*b; simp,rfl⟩
    | true =>
      apply weaken (bind (ho aft bef) (fun y _=>bind (ho x y) (fun w _=>ret [w] (P:=fun xs=>xs.length=1) rfl)))
      · simp [csv,Nat.two_mul]
      · exact fun _ h=>h
  | node val l r hl hr =>
    simp only [down]
    have pl := cpos l;have pr := cpos r
    have finish (la rb : A) := bind (hl bef la) (fun al hal=>bind (hr rb aft) (fun ar har=>
      ret (al++ar) (P:=fun xs=>xs.length=csv (.node val l r)) (by simp [csv,hal,har])))
    cases rot with
    | false =>
      apply weaken (bind (ret z (P:=fun _=>True) trivial) (fun la _=>bind (ho bef l.prod) (fun rb _=>finish la rb)))
      · simp only [Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero,csv]
        have eq : csv l+csv r-1=(csv l-1)+(csv r-1)+1 := by omega
        rw [eq,Nat.add_mul,Nat.add_mul,Nat.one_mul];omega
      · exact fun _ h=>h
    | true =>
      apply weaken (bind (ho r.prod aft) (fun la _=>bind (ho bef l.prod) (fun rb _=>finish la rb)))
      · simp only [ite_true,Nat.zero_add,Nat.add_zero,csv]
        have eq : 4*(csv l+csv r)-2=(4*csv l-2)+(4*csv r-2)+2 := by omega
        rw [eq,Nat.add_mul,Nat.add_mul,Nat.two_mul];omega
      · exact fun _ h=>h

end Pcx293.MCost

namespace Pcx293.MCost
open PEqualNP.Outside.L_pcx_293.Pcx293.Make

theorem lengthAfter {m : B (List A)} {c n : Nat} {P : A → Prop}
    (h : Cost m c (fun xs=>xs.length=n ∧ ∀ x∈xs,P x)) : Cost m c (fun xs=>xs.length=n) :=
  weaken h (Nat.le_refl _) (fun _ hx=>hx.1)

theorem byIdx (n b : Nat) (f : Nat → B A) (h : ∀ i,Cost (f i) b (fun _=>True)) :
    Cost (byIndex n f) (n*b) (fun xs=>xs.length=n) := by
  simpa [byIndex] using lengthAfter (mapM (List.range n) f b _ (fun i _=>h i))

theorem scan_bound (op : A → A → B A) (z : A) (rot : Bool) (b : Nat)
    (hh : ∀ x y,Cost (op x y) b (fun _=>True)) (v : List A) :
    Cost (scan op z v rot) (((if rot then 5 else 2)*v.length)*b) (fun out=>out.length=v.length) := by
  cases v with
  | nil =>
    intro s;exact ⟨by change score s ≤ score s+(_*0)*b;simp,rfl⟩
  | cons x xs =>
    let v:=x::xs
    let t:=shape (fun i=>v.getD i z) 0 v.length
    have nt : leaves t=v.length := shape_leaves (fun i=>v.getD i z) 0 v.length (by simp [v])
    have hb := build_cost op b hh t
    unfold scan
    simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    apply weaken (bind hb (fun tree eq=> by
      have h := down_cost op z b hh rot tree z z
      have ee : csv tree=v.length := eq.trans nt
      rw [ee] at h;exact h))
    · rw [nt]
      have hv : 0 < v.length := by simp [v]
      rw [←Nat.add_mul]
      apply Nat.mul_le_mul_right _ 
      cases rot <;> change _ ≤ _ <;> simp [v] <;> omega
    · exact fun _ e=>e

theorem reduce_bound (op : Tape.Op) (z : W) (v : Vec) :
    Cost (reduce op z v) (13*v.length) (fun _=>True) := by
  cases v with
  | nil => intro s;exact ⟨by change score s ≤ score s+13*0;simp,trivial⟩
  | cons x xs =>
    let v:=x::xs
    let t:=shape (fun i=>v.getD i z) 0 v.length
    have nt : leaves t=v.length := shape_leaves (fun i=>v.getD i z) 0 v.length (by simp [v])
    unfold reduce;simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    apply weaken (bind (build_cost _ _ (one op) t) (fun p _=>ret p.prod (P:=fun _=>True) trivial))
    · rw [nt];simp [v,Nat.mul_comm] <;> omega
    · exact fun _ h=>h

theorem vx_bound (k : Nat) (z : W) (a b : Vec) :
    Cost (vX k z a b) (13*k) (fun xs=>xs.length=k) := by
  simpa [vX,Nat.mul_comm] using byIdx k 13 _ (fun _=>one .bxor _ _)

theorem inverse_bound (k : Nat) (oneW zero : W) (y : Vec) :
    Cost (inverseChi k oneW zero y) (195*k) (fun xs=>xs.length=k) := by
  let ord : List A2 := (List.range k).map fun t=>
    (y.getD ((2*t) % k) zero, Unit.neg (y.getD ((2*t+1) % k) zero))
  let comp : A2 → A2 → B A2 := fun p q=>do
    let b←emit .bxor p.1 (←emit .band p.2 q.1)
    return (b,←emit .band p.2 q.2)
  have hc (p q) : Cost (comp p q) 39 (fun _=>True) :=
    bind (one .band _ _) (fun a _=>bind (one .bxor _ a) (fun b _=>bind (one .band _ _) (fun c _=>ret (b,c) trivial)))
  have h := scan_bound comp (zero,oneW) true 39 hc ord
  have len : ord.length=k := by simp [ord]
  apply weaken (bind h (fun vals _=>ret ((List.range k).map fun i=>
    (vals.getD (if i % 2=0 then i/2 else (i+k)/2) (zero,oneW)).1)
    (P:=fun xs=>xs.length=k) (by simp)))
  · simp [len];omega
  · exact fun _ e=>e

theorem check_bound (k d : Nat) (oneW zero : W) (w y : Vec) :
    Cost (check k d oneW zero w y) (78*k) (fun _=>True) := by
  let per := fun (us : Vec) i=>do
    let v←emit .band (Unit.neg (us.getD ((i+1) % k) zero)) (us.getD ((i+2) % k) zero)
    let bit←emit .bxor (us.getD i zero) v
    emit .bxor bit (y.getD i zero)
  have hc (us i) : Cost (per us i) 39 (fun _=>True) :=
    bind (one .band _ _) (fun v _=>bind (one .bxor _ v) (fun b _=>one .bxor b _))
  apply weaken (bind (vx_bound k zero w _) (fun v _=>bind (vx_bound k zero v _) (fun us _=>
    bind (byIdx k 39 (per us) (hc us)) (fun bad eb=>by
      have h:=reduce_bound .bor zero bad;rw [eb] at h;exact h))))
  · omega
  · exact fun _ e=>e

end Pcx293.MCost

namespace Pcx293.MCost
open PEqualNP.Outside.L_pcx_293.Pcx293.Make

theorem side_bound (k : Nat) (z : W) (u : Nat → W) (q : Nat) :
    Cost (coordSide k z u q) (52*k) (fun _=>True) := by
  let xs:=indices k q
  have dl := lengthAfter (mapM xs (fun t=>emit .bxor (u t) (u (t+1))) 13 _ (fun _ _=>one .bxor _ _))
  have xl : xs.length ≤ k := by simp [xs,indices];omega
  apply weaken (bind dl (fun ds ld=>bind (show Cost (scan (emit .bxor) z ds false)
    ((2*xs.length)*13) (fun yy=>yy.length=xs.length) by
      have h := scan_bound (emit .bxor) z false 13 (one .bxor) ds;simpa [ld] using h)
    (fun pre pl=>by
      have v:=lengthAfter (mapM pre (fun e=>emit .bxor (if q=2 then u 0 else z) e) 13 _ (fun _ _=>one .bxor _ _))
      rw [pl] at v;exact v)))
  · omega
  · exact fun _ _=>trivial

theorem child_bound (k d : Nat) (o z dead : W) (y : Vec) (sides : List Vec) (sg : Bool×Bool) :
    Cost (child k d o z dead y sides sg) (78*k+13) (fun _=>True) := by
  unfold child
  apply weaken (bind (check_bound k d o z _ y) (fun bad _=>bind (one .bor dead bad)
    (fun w _=>ret (_,w) (P:=fun _=>True) trivial)))
  · omega
  · exact fun _ _=>trivial

theorem expand_bound (k d : Nat) (o z : W) (p : Entry) (mask : Vec) :
    Cost (expand k d o z p mask) (700*(k+1)) (fun es=>es.length=4) := by
  unfold expand
  apply weaken (bind (vx_bound k z p.1 mask) (fun y _=>bind (inverse_bound k o z y)
    (fun iv _=>bind (byIdx 3 (52*k) _ (side_bound k z _))
      (fun sides _=>lengthAfter (mapM signs (child k d o z p.2 y sides) (78*k+13) _
        (fun g _=>child_bound k d o z p.2 y sides g))))))
  · change 13*k+(195*k+(3*(52*k)+4*(78*k+13))) ≤ _;omega
  · exact fun _ h=>h

theorem flatten_four (as : List (List A)) (h : ∀ a∈as,a.length=4) :
    as.flatten.length = as.length*4 := by
  induction as with
  | nil => rfl
  | cons x xs ih =>
    simp [h x (by simp),ih (fun a ha=>h _ (by simp [ha]))];omega

theorem layer_bound (k r d : Nat) (o z : W) (key : Vec) (js : List Nat) (ns : List Entry) :
    Cost (genLayers k r d o z key js ns)
      (700*(k+1)*ns.length*Budget.internal js.length)
      (fun out=>out.length=ns.length*4^js.length) := by
  induction js generalizing ns with
  | nil =>
    intro s
    refine ⟨?_,?_⟩
    · change score s ≤ score s+_*Budget.internal 0;simp [Budget.internal]
    · change ns.length=ns.length*4^0;simp
  | cons j js ih =>
    unfold genLayers
    apply weaken (bind (mapM ns (fun p=>expand k d o z p (mask k r d j z key)) (700*(k+1)) (fun es=>es.length=4) (fun p _=>expand_bound k d o z p _))
      (fun kids hk=>by
        have e : kids.flatten.length=ns.length*4 := (flatten_four _ hk.2).trans (by rw [hk.1])
        have h:=ih kids.flatten;rw [e] at h;exact h))
    · simp only [List.length_cons,Budget.internal,Nat.mul_add,Nat.mul_one]
      simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] <;> rw [←Nat.mul_assoc 4 700] <;> exact Nat.le_refl _
    · intro v hv
      rw [hv,List.length_cons,Nat.pow_succ]
      simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem filter_bound (k : Nat) (z : W) (initial nm : Vec) (p : Entry) :
    Cost (filterName k z initial nm p) (39*k+13) (fun _=>True) := by
  unfold filterName
  apply weaken (bind (vx_bound k z p.1 initial) (fun pre _=>bind (vx_bound k z nm pre) (fun mm hlen=>
    bind (show Cost (reduce .bor z (p.2::mm)) (13*(k+1)) (fun _=>True) by
      simpa [hlen] using reduce_bound .bor z (p.2::mm)) (fun cc _=>ret (pre,cc) (P:=fun _=>True) trivial))))
  · omega
  · exact fun _ _=>trivial

theorem block_bound (k : Nat) (o z : W) (nm : Vec) (labels : List Entry) (i : Nat) (b : Bool) :
    Cost (block k o z nm labels i b) (26*labels.length+2) (fun _=>True) := by
  unfold block
  apply weaken (bind (lengthAfter (mapM labels (fun p=>emit .bor p.2 (if b then Unit.neg (p.1.getD i z) else p.1.getD i z)) 13 (fun _=>True) (fun _ _=>one .bor _ _))) (fun flags hh=>bind
    (show Cost (reduce .band o flags) (13*labels.length) (fun _=>True) by rw [←hh];exact reduce_bound .band o flags)
    (fun g _=>add_cost [Unit.neg g,if b then Unit.neg (nm.getD i z) else nm.getD i z])))
  · change labels.length*13+(13*labels.length+2) ≤ _;omega
  · exact fun _ _=>trivial

theorem consensus (k : Nat) (o z : W) (nm : Vec) (labels : List Entry) :
    Cost ((List.range k).mapM (fun i=>do
      block k o z nm labels i false
      block k o z nm labels i true)) (k*(52*labels.length+4)) (fun _=>True) := by
  apply weaken (mapM _ _ (52*labels.length+4) _ (fun i _=>
    weaken (bind (block_bound k o z nm labels i false) (fun _ _=>block_bound k o z nm labels i true)) (by omega) (fun _ _=>trivial)))
  · simp
  · exact fun _ _=>trivial

def laneCost (k r : Nat) := 700*(k+1)*Budget.internal r + 4^r*(39*k+13)+13*4^r+1+k*(52*4^r+4)
theorem track_bound (k r d : Nat) (o z : W) : Cost (track k r d o z) (laneCost k r) (fun _=>True) := by
  unfold track
  have ini := layer_bound k r d o z (raw k 2) (List.range r).reverse [(raw k (d+2),z)]
  simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.mul_one,Nat.one_mul,List.length_reverse,List.length_range] at ini
  apply weaken (bind ini (fun nodes nh=>bind
    (show Cost (nodes.mapM (filterName k z _ _)) (4^r*(39*k+13)) (fun xs=>xs.length=4^r) by
      have h:=lengthAfter (mapM nodes _ (39*k+13) _ (fun x _=>filter_bound k z (rot k z (raw k 2) (if d=1 then 1 else 3)) (raw k (d-1)) x))
      rw [nh] at h;exact h)
    (fun labels lh=>bind
      (show Cost (reduce .band o (labels.map Prod.snd)) (13*4^r) (fun _=>True) by simpa [lh] using reduce_bound .band o (labels.map Prod.snd))
      (fun bad _=>bind (add_cost [Unit.neg bad]) (fun _ _=>bind
        (show Cost _ (k*(52*4^r+4)) (fun _=>True) by
          have h:=consensus k o z (raw k (d-1)) labels;rw [lh] at h;exact h)
        (fun _ _=>ret () (P:=fun _=>True) trivial))))))
  · unfold laneCost
    change 700*(k+1)*Budget.internal r+(4^r*(39*k+13)+(13*4^r+(1+(k*(52*4^r+4)+0)))) ≤ _;omega
  · exact fun _ _=>trivial

end Pcx293.MCost

namespace Pcx293.MCost
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Tape PEqualNP.Outside.L_pcx_293.Pcx293.Unit

theorem literal_each (l : Line) : litWeight (lineF l) ≤ 12 := by
  have e : litWeight (lineF l)=l.op.g.weight := map_weight _ _
  rw [e];exact Gate.weight_le _

theorem form_weight (s : Net) : s.n + litWeight s.form ≤ score s := by
  have go (xs : List Line) : litWeight (xs.flatMap lineF) ≤ 12*xs.length := by
    induction xs with
    | nil => exact Nat.le_refl _
    | cons x xs ih =>
      rw [List.flatMap_cons,append_weight,List.length_cons]
      have := literal_each x;omega
  unfold Net.form score
  rw [append_weight]
  have bound:=go s.lines
  change s.n+((s.constraints.map List.length).sum+litWeight (s.lines.flatMap lineF)) ≤ _
  omega

theorem geom_le (r : Nat) : Budget.internal r ≤ 4^r := by have := Budget.geometric r;omega

theorem lane_numeric (k r : Nat) : laneCost k r ≤ 900*(k+1)*4^r := by
  let n:=4^r
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
  have hk : k ≤ k*n := by simpa using Nat.mul_le_mul_left k hn
  have q : 700*(k+1)*Budget.internal r ≤ 700*(k+1)*n := Nat.mul_le_mul_left _ (geom_le r)
  unfold laneCost
  change 700*(k+1)*Budget.internal r+n*(39*k+13)+13*n+1+k*(52*n+4) ≤ 900*(k+1)*n
  have zz : n*(39*k)=39*(k*n) := by ac_rfl
  have zs : k*(52*n)=52*(k*n) := by ac_rfl
  have zz' : n*13=13*n := Nat.mul_comm .. 
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc,zz,zs,zz',Nat.mul_comm k 4] at *
  omega

theorem actual_literal_budget (k r : Nat) :
    (make k r).n + 1 + litWeight (make k r).form ≤ 8192*(k+1)*4^r := by
  let s : Net:={n:=5*k+1}
  let oneW:=pos (2*(5*k))
  have c:=bind (track_bound k r 1 oneW (neg oneW)) (fun _ _=>bind (track_bound k r 2 oneW (neg oneW))
    (fun _ _=>add_cost [oneW]))
  have h := (c s).1
  change score (make k r) ≤ (5*k+1)+(laneCost k r+(laneCost k r+1)) at h
  have v:=form_weight (make k r)
  have q:=lane_numeric k r
  have hn:1 ≤ 4^r:=Nat.one_le_pow _ _ (by decide)
  have hk:k ≤ k*4^r:=by simpa using Nat.mul_le_mul_left k hn
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at q ⊢
  omega

end Pcx293.MCost

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Wire

def HoldsLine (e : Nat → Bool) (l : Line) :=
  e l.id = l.op.eval (value e l.a) (value e l.b)
def Model (e : Nat → Bool) (s : Net) :=
  (∀ l∈s.lines,HoldsLine e l) ∧ (∀ c∈s.constraints,∃ p∈c,e p.1=p.2)

theorem line_iff (e : Nat → Bool) (l : Line) :
    Sat (fun c=>c∈lineF l) e ↔ HoldsLine e l := by
  let f := fun j : Fin 3=>if j=0 then l.a else if j=1 then l.b else pos l.id
  have eq : (fun c=>c∈lineF l)=transForm f (fun c=>c∈l.op.g.clauses) := by
    funext c;exact propext List.mem_map
  rw [eq,transported_models,Gate.sat_iff]
  rcases l with ⟨n,op,a,b⟩
  have h : value e (pos n)=e n := by simp [value,pos]
  cases op <;> simp [Tape.Op.g,Tape.Op.eval,Gate.Holds,HoldsLine,f,h]

theorem model_iff (e : Nat → Bool) (s : Net) :
    Sat (fun c=>c∈s.form) e ↔ Model e s := by
  constructor
  · intro ok
    exact ⟨fun l h=> (line_iff e l).mp (fun c hc=>ok _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨l,h,hc⟩))),
      fun c hc=>ok c (List.mem_append_left _ hc)⟩
  · rintro ⟨lines,cs⟩ c h
    rcases List.mem_append.mp h with hc|hl
    · exact cs _ hc
    · rcases List.mem_flatMap.mp hl with ⟨l,lh,cl⟩
      exact (line_iff e l).mpr (lines l lh) _ cl


def LinesOK (e : Nat → Bool) (s : Net) := ∀ l∈s.lines,HoldsLine e l
def Good (e : Nat → Bool) (m : B A) (P : A → Prop) :=
  ∀ s,LinesOK e (m.run s).2 → (LinesOK e s ∧ (m.run s).2.constraints=s.constraints) ∧ P (m.run s).1

theorem pureG (e : Nat → Bool) (a : A) {P : A → Prop} (p : P a) : Good e (pure a) P :=
  fun _ h=>⟨⟨h,rfl⟩,p⟩
theorem mono {e : Nat → Bool} {m : B A} {P Q : A → Prop}
    (hp : Good e m P) (f : ∀ a,P a → Q a) : Good e m Q := by
  intro s h;rcases hp s h with ⟨v,r⟩;exact ⟨v,f _ r⟩
theorem bindG {e : Nat → Bool} {m : B A} {f : A → B D} {P : A → Prop} {Q : D → Prop}
    (hp : Good e m P) (hq : ∀ a,Good e (f a) (fun b=>P a → Q b)) :
    Good e (m >>= f) Q := by
  intro s h
  obtain ⟨⟨s₀,eq2⟩,v₂⟩ := hq (m.run s).1 (m.run s).2 h
  obtain ⟨⟨s₁,eq1⟩,v₁⟩ := hp s s₀
  exact ⟨⟨s₁,eq2.trans eq1⟩,v₂ v₁⟩

theorem em (e : Nat → Bool) (op : Tape.Op) (a b : W) :
    Good e (emit op a b) (fun c=>value e c=op.eval (value e a) (value e b)) := by
  intro s h
  have atNew := h (⟨nextId s a b,op,a,b⟩) (List.mem_cons_self ..)
  refine ⟨⟨fun l hl=>h l (List.mem_cons_of_mem _ hl),rfl⟩,?_⟩
  change value e (pos (nextId s a b))=_
  simpa [value,pos,HoldsLine] using atNew

theorem map_eval (e : Nat → Bool) (xs : List A) (f : A → B D) (project : D → C) (g : A → C)
    (h : ∀ a∈xs,Good e (f a) (fun w=>project w=g a)) :
    Good e (xs.mapM f) (fun out=>out.map project=xs.map g) := by
  induction xs with
  | nil => exact pureG _ _ rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply bindG (h x (by simp))
    intro d
    apply bindG (ih (fun a ha=>h a (by simp [ha])))
    intro ds
    exact pureG _ (d::ds) (by intro eq head; simp [eq,head])


theorem vec_xor (e : Nat → Bool) (k : Nat) (zero : W) (a b : Vec) :
    Good e (vX k zero a b) (fun xs=>xs.map (value e)=(List.range k).map
      (fun i=>xor (value e (a.getD i zero)) (value e (b.getD i zero)))) :=
  map_eval _ _ _ _ _ (fun _ _=>em e .bxor _ _)

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation

def skeleton (f : A → D) : Cached A → T D
| .leaf x=>.tip (f x)
| .node _ l r=>.join (skeleton f l) (skeleton f r)
def target (f : A → D) : ScanTree A → T D
| .tip x=>.tip (f x)
| .node l r=>.join (target f l) (target f r)
def safe (M : Law D) (f : A → D) : Cached A → Prop
| .leaf _=>True
| .node v l r=>
    f v=M.op (f l.prod) (f r.prod) ∧ safe M f l ∧ safe M f r

theorem product_safe (M : Law D) (f : A → D) (t : Cached A) (h : safe M f t) :
    f t.prod=(skeleton f t).up M := by
  induction t with
  | leaf => rfl
  | node x l r ihl ihr =>
    rcases h with ⟨q,hl,hr⟩
    change f x=M.op ((skeleton f l).up M) ((skeleton f r).up M)
    rw [q,ihl hl,ihr hr]

theorem cache_model (e : Nat → Bool) (M : Law D) (f : A → D) (op : A → A → B A)
    (ok : ∀ x y,Good e (op x y) (fun z=>f z=M.op (f x) (f y))) (t : ScanTree A) :
    Good e (build op t) (fun c=>safe M f c ∧ skeleton f c=target f t) := by
  induction t with
  | tip x => exact pureG _ _ ⟨trivial,rfl⟩
  | node l r ihl ihr =>
    apply bindG ihl;intro lc
    apply bindG ihr;intro rc
    apply bindG (ok lc.prod rc.prod);intro val
    exact pureG _ (Cached.node val lc rc) (by
      rintro vv ⟨rs,rq⟩ ⟨ls,lq⟩
      exact ⟨⟨vv,ls,rs⟩, by simp [skeleton,target,lq,rq]⟩)

def preRows (M : Law D) : T D → D → List D
| .tip _,b=>[b]
| .join l r,b=>preRows M l b ++ preRows M r (M.op b (l.up M))

theorem down_model (e : Nat → Bool) (M : Law D) (f : A → D) (op : A → A → B A)
    (ok : ∀ x y,Good e (op x y) (fun z=>f z=M.op (f x) (f y)))
    (zero : A) (_iz:f zero=M.one) (cy : Bool) (c : Cached A) (bef aft : A) :
    Good e (down op zero cy c bef aft) (fun out=> safe M f c → 
      out.map f= if cy then (skeleton f c).down M (f bef) (f aft)
        else preRows M (skeleton f c) (f bef)) := by
  induction c generalizing bef aft with
  | leaf x =>
    cases cy with
    | false => exact pureG _ _ (fun _=>rfl)
    | true =>
      apply bindG (ok aft bef);intro h
      apply bindG (ok x h);intro g
      exact pureG _ [g] (by intro gx hx _;simp [skeleton,T.down,gx,hx])
  | node v l r il ir =>
    cases cy with
    | true =>
      apply bindG (ok r.prod aft);intro la
      apply bindG (ok bef l.prod);intro rb
      apply bindG (il bef la);intro left
      apply bindG (ir rb aft);intro right
      exact pureG _ (left++right) (by
        rintro rightOK leftOK rbOK laOK ⟨_,ls,rs⟩
        simp only [List.map_append,skeleton,ite_true,T.down]
        rw [leftOK ls,rightOK rs]
        simp only [ite_true,laOK,rbOK,product_safe M f l ls,product_safe M f r rs])
    | false =>
      apply bindG (pureG e zero (P:=fun x=>x=zero) rfl);intro la
      apply bindG (ok bef l.prod);intro rb
      apply bindG (il bef la);intro left
      apply bindG (ir rb aft);intro right
      exact pureG _ (left++right) (by
        rintro rightOK leftOK rbOK laOK ⟨_,ls,rs⟩
        simp only [List.map_append,skeleton,Bool.false_eq_true,ite_false,preRows]
        rw [leftOK ls,rightOK rs]
        simp only [Bool.false_eq_true,ite_false,rbOK,product_safe M f l ls])

theorem scan_model (e : Nat → Bool) (M : Law D) (f : A → D) (op : A → A → B A)
    (ok : ∀ x y,Good e (op x y) (fun z=>f z=M.op (f x) (f y)))
    (zero : A) (iz : f zero=M.one) (cy : Bool) (v : List A) (h : v≠[]) :
    Good e (scan op zero v cy) (fun out=>
      let t:=target f (shape (fun i=>v.getD i zero) 0 v.length)
      out.map f= if cy then t.down M M.one M.one else preRows M t M.one) := by
  rcases v with _|⟨x,xs⟩
  · contradiction
  unfold scan
  simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
  apply bindG (cache_model e M f op ok _)
  intro cc
  apply mono (down_model e M f op ok zero iz cy cc zero zero)
  rintro out hh ⟨safeC,equ⟩
  simpa only [equ,iz] using hh safeC

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation PEqualNP.Outside.L_pcx_293.Pcx293.Chi PEqualNP.Outside.L_pcx_293.Pcx293.Wire

theorem target_vals (f : A → D) (g : Nat → A) (s n : Nat) (posi : 0 < n) :
    (target f (shape g s n)).vals=(List.range' s n).map (fun i=>f (g i)) := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    rw [Make.shape]
    split
    · obtain rfl : n=1 := by omega
      rfl
    · change (target f (shape g s (n/2))).vals ++ (target f (shape g (s+n/2) (n-n/2))).vals = _
      rw [ih _ (by omega) _ (by omega),ih _ (by omega) _ (by omega),←List.map_append,List.range'_append_1]
      rw [show n/2+(n-n/2)=n by omega]

theorem target_input (f : A → D) (v : List A) (z : A) (h : v≠[]) :
    (target f (shape (fun i=>v.getD i z) 0 v.length)).vals=v.map f := by
  rw [target_vals _ _ _ _ (List.length_pos_iff.mpr h)]
  apply List.ext_getElem
  · simp
  · intro i a b
    have hi : i < v.length := by simpa using b
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,hi]

def rotProducts (M : Law D) (xs : List D) :=
  (List.range xs.length).map fun j=>M.prod (xs.drop j ++ xs.take j)

theorem compiled_cyclic (e : Nat → Bool) (M : Law D) (f : A → D) (op : A → A → B A)
    (ok : ∀ x y,Good e (op x y) (fun z=>f z=M.op (f x) (f y)))
    (zero : A) (iz : f zero=M.one) (v : List A) (h : v≠[]) :
    Good e (scan op zero v true) (fun out=>out.map f=rotProducts M (v.map f)) := by
  apply mono (scan_model e M f op ok zero iz true v h)
  intro out eq
  let t:=target f (shape (fun i=>v.getD i zero) 0 v.length)
  change out.map f=t.down M M.one M.one at eq
  rw [eq]
  have vt : t.vals=v.map f := target_input f v zero h
  rw [←vt]
  apply List.ext_getElem
  · simp [T.down_length,rotProducts]
  · intro j hj hj'
    have jv : j < t.vals.length := by simpa [T.down_length] using hj
    rw [T.down_get _ _ _ _ _ jv]
    simp [rotProducts,M.left,Law.prod_append]

def affLaw : Law Aff where
  one:=Aff.one
  op:=Aff.comp
  left a := by rcases a with ⟨x,p⟩; cases x <;> cases p <;> rfl
  right a := by rcases a with ⟨x,p⟩; cases x <;> cases p <;> rfl
  assoc:=Aff.assoc

def coeffs (y : BitSeq) (i : Nat) : Nat → List Aff
| 0=>[]
| n+1=>⟨y i,!y (i+1)⟩::coeffs y (i+2) n

theorem coeff_len (y : BitSeq) (i n : Nat) : (coeffs y i n).length=n := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>simp [coeffs,ih]

theorem coeff_get (y : BitSeq) (i n j : Nat) (hj:j < n) :
    (coeffs y i n)[j]'(by rwa [coeff_len])=⟨y (i+2*j),!y (i+2*j+1)⟩ := by
  induction n generalizing i j with
  | zero=>omega
  | succ n ih =>
    cases j with
    | zero=>simp [coeffs]
    | succ j =>
      simp only [coeffs,List.getElem_cons_succ]
      rw [ih _ _ (by omega),show i+2*j.succ=i+2+2*j by omega]

theorem coeff_prod (y : BitSeq) (i n : Nat) : affLaw.prod (coeffs y i n)=Chi.scan y i n := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih => change Aff.comp _ (affLaw.prod (coeffs y (i+2) n))=Aff.comp _ (Chi.scan y (i+2) n);rw [ih]

theorem coeff_cut (y : BitSeq) (i a b : Nat) :
    coeffs y i (a+b)=coeffs y i a ++ coeffs y (i+2*a) b := by
  induction a generalizing i with
  | zero=>simp [coeffs]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [coeffs,List.cons_append,List.cons.injEq,true_and]
    rw [ih,show i+2*(a+1)=i+2+2*a by omega]

theorem coeff_per {k : Nat} (y : BitSeq) (per : ∀ i,y (i+k)=y i) (i n : Nat) :
    coeffs y (i+k) n=coeffs y i n := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>simp [coeffs,show i+k+1=i+1+k by omega,show i+k+2=i+2+k by omega,per,ih]

theorem cyclic_is_scan {k : Nat} (y:BitSeq) (per:∀ i,y (i+k)=y i) (j:Nat) (hj:j < k) :
    affLaw.prod ((coeffs y 0 k).drop j ++ (coeffs y 0 k).take j) = Chi.scan y (2*j) k := by
  have e : coeffs y 0 k=coeffs y 0 j++coeffs y (2*j) (k-j) := by
    simpa [show j+(k-j)=k by omega] using coeff_cut y 0 j (k-j)
  rw [e]
  have len := coeff_len y 0 j
  have d:=List.drop_append_length (l₁:=coeffs y 0 j) (l₂:=coeffs y (2*j) (k-j))
  have t:=List.take_append_length (l₁:=coeffs y 0 j) (l₂:=coeffs y (2*j) (k-j))
  rw [len] at d t;rw [d,t]
  rw [←coeff_prod]
  have endEq : coeffs y (2*j+2*(k-j)) j=coeffs y 0 j := by
    rw [show 2*j+2*(k-j)=(0+k)+k by omega,coeff_per y per,coeff_per y per]
  have split := coeff_cut y (2*j) (k-j) j
  rw [show k-j+j=k by omega,endEq] at split
  rw [←split]

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Chi
def project (e : Nat → Bool) (p : A2) : Aff := ⟨value e p.1,value e p.2⟩
def bits (e : Nat → Bool) (k : Nat) (v : Vec) (z : W) (i : Nat) := value e (v.getD (i % k) z)
def pairGate (p q : A2) : B A2 := do
  let b←emit .bxor p.1 (←emit .band p.2 q.1)
  return (b,←emit .band p.2 q.2)
theorem pair_ok (e : Nat → Bool) (p q : A2) :
    Good e (pairGate p q) (fun v=>project e v=affLaw.op (project e p) (project e q)) := by
  apply bindG (em e .band _ _);intro x
  apply bindG (em e .bxor _ _);intro y
  apply bindG (em e .band _ _);intro w
  exact pureG _ (y,w) (by intro eqw eqy eqx; unfold project affLaw Aff.comp Aff.run; simp [eqw,eqy,eqx,Tape.Op.eval])

def orderW (k : Nat) (z : W) (y : Vec) := (List.range k).map fun t=>
  (y.getD ((2*t) % k) z, Unit.neg (y.getD ((2*t+1) % k) z))
theorem order_sem (e : Nat → Bool) (k : Nat) (z : W) (v : Vec) :
    (orderW k z v).map (project e) = coeffs (bits e k v z) 0 k := by
  apply List.ext_getElem
  · simp [orderW,coeff_len]
  · intro j hl hr
    have hj : j < k := by simpa [coeff_len] using hr
    rw [coeff_get _ _ _ _ hj]
    simp [orderW,project,bits,value_neg]

theorem inv_order {k : Nat} (odd : k % 2=1) (i : Nat) (hi : i < k) :
    let j:=if i % 2=0 then i/2 else (i+k)/2
    j < k ∧ (2*j=i ∨ 2*j=i+k) := by dsimp;split <;> omega

theorem inv_compiled {k : Nat} (odd : k % 2=1) (e : Nat → Bool) (oneW z : W) (v : Vec)
    (zero : value e z=false) (one : value e oneW=true) :
    Good e (inverseChi k oneW z v) (fun out=>out.map (value e)=(List.range k).map
      (fun i=>(Chi.scan (bits e k v z) i k).bias)) := by
  let y:=bits e k v z
  have per : ∀i,y (i+k)=y i := fun i=>by simp [y,bits]
  let vord:=orderW k z v
  have vl : vord.length=k := by simp [vord,orderW]
  have ne : vord≠[] := fun h=>by rw [h] at vl;simp at vl;omega
  have idZ : project e (z,oneW)=affLaw.one := by simp [project,affLaw,Aff.one,zero,one]
  apply bindG (compiled_cyclic e affLaw (project e) pairGate (pair_ok e) _ idZ vord ne)
  intro vals
  apply pureG
  intro veq
  rw [order_sem] at veq
  have ln : vals.length=k := by
    have l:=congrArg List.length veq
    simpa [rotProducts,coeff_len] using l
  apply List.ext_getElem
  · simp
  · intro i hl hr
    have hi : i < k := by simpa using hr
    let j:=if i % 2=0 then i/2 else (i+k)/2
    have ⟨hj,modj⟩ := inv_order odd i hi
    have lj : j < vals.length := by simpa [ln] using hj
    have vm : (vals.map (project e))[j]?=(rotProducts affLaw (coeffs y 0 k))[j]? :=
      congrArg (fun (v : List Aff)=>v[j]?) veq
    have eqj : project e vals[j]=(Chi.scan y (2*j) k) := by
      have jq : (List.range k)[j]?=some j := by rw [List.getElem?_eq_getElem (by simpa using hj)];simp
      apply Eq.trans _ (cyclic_is_scan y per _ hj)
      simpa [rotProducts,lj,coeff_len,jq] using vm
    have sp : Chi.scan y (2*j) k=Chi.scan y i k := by
      rcases modj with h|h
      · rw [h]
      · rw [h,←coeff_prod,coeff_per y per,coeff_prod]
    have bit:=congrArg Aff.bias (eqj.trans sp)
    simp only [List.getElem_map,List.getElem_range]
    change value e (vals.getD j (z,oneW)).1=(Chi.scan y i k).bias
    simpa [project,List.getD_eq_getElem?_getD,lj] using bit

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation PEqualNP.Outside.L_pcx_293.Pcx293.Wire

theorem pre_len (M : Law D) (t : T D) (b : D) : (preRows M t b).length=t.vals.length := by
  induction t generalizing b with
  | tip x=>rfl
  | join l r il ir=>simp [preRows,T.vals,il,ir]

theorem pre_get (M : Law D) (t : T D) (b : D) (j : Nat) (hj:j < t.vals.length) :
    (preRows M t b)[j]'(by rwa [pre_len])=M.op b (M.prod (t.vals.take j)) := by
  induction t generalizing b j with
  | tip x=>
    have : j=0 := by simp [T.vals] at hj;omega
    subst j;simp [preRows,T.vals,Law.prod,M.right]
  | join l r il ir=>
    by_cases h : j < l.vals.length
    · have hp : j < (preRows M l b).length := by rwa [pre_len]
      simp only [preRows,T.vals]
      rw [List.getElem_append_left hp,il _ _ h,List.take_append_of_le_length (Nat.le_of_lt h)]
    · have hr : j-l.vals.length < r.vals.length := by simp [T.vals] at hj;omega
      have hp : (preRows M l b).length ≤ j := by rw [pre_len];omega
      simp only [preRows,T.vals]
      rw [List.getElem_append_right hp]
      simp only [pre_len]
      rw [ir _ _ hr,List.take_append,List.take_of_length_le (Nat.le_of_not_gt h),
        Law.prod_append,T.up_eq,M.assoc]

def preProducts (M : Law D) (v : List D) :=
  (List.range v.length).map (fun j=>M.prod (v.take j))

theorem compiled_prefix (e : Nat → Bool) (M : Law D) (f : A → D) (op : A → A → B A)
    (ok : ∀ x y,Good e (op x y) (fun z=>f z=M.op (f x) (f y)))
    (zero : A) (iz : f zero=M.one) (v : List A) :
    Good e (scan op zero v false) (fun out=>out.map f=preProducts M (v.map f)) := by
  by_cases h : v=[]
  · subst v;exact pureG _ _ rfl
  apply mono (scan_model e M f op ok zero iz false v h)
  intro out eq
  let t:=target f (shape (fun i=>v.getD i zero) 0 v.length)
  change out.map f=preRows M t M.one at eq
  rw [eq]
  have vt : t.vals=v.map f := target_input f v zero h
  rw [←vt]
  apply List.ext_getElem
  · simp [pre_len,preProducts]
  · intro j hj hj'
    have jv : j < t.vals.length := by simpa [pre_len] using hj
    rw [pre_get _ _ _ _ jv]
    simp [preProducts,M.left]

def xorLaw : Law Bool where
  one:=false
  op:=xor
  left x:=by cases x <;> rfl
  right x:=by cases x <;> rfl
  assoc x y z:=by cases x <;> cases y <;> cases z <;> rfl

def delta (u : Nat → Bool) (q t : Nat) : Bool := u (q+3*t) ^^ u (q+3*t+1)
theorem prod_delta (u : Nat → Bool) (q n : Nat) :
    xorLaw.prod ((List.range n).map (delta u q))=Linear.pxor u q n := by
  induction n with
  | zero=>rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,Law.prod_append,ih]
    simp [Law.prod,xorLaw,Linear.pxor,delta]

theorem side_model (e : Nat → Bool) (k : Nat) (z : W) (zero:value e z=false)
    (u : Nat → W) (q : Nat) :
    Good e (coordSide k z u q) (fun out=>out.map (value e)=(List.range (k/3)).map
      (fun j=>(if q=2 then value e (u 0) else false) ^^ Linear.pxor (fun t=>value e (u t)) q j)) := by
  let uv := fun t=>value e (u t)
  let d := delta uv q
  have rawD:=map_eval e (indices k q) (fun t=>emit .bxor (u t) (u (t+1))) (value e)
    (fun t=>uv t ^^ uv (t+1)) (fun _ _=>em e .bxor _ _)
  apply bindG rawD;intro dif
  apply bindG (compiled_prefix e xorLaw (value e) (emit .bxor) (fun x y=>em e .bxor x y) z zero dif);intro pre
  apply mono (map_eval e pre (fun a=>emit .bxor (if q=2 then u 0 else z) a) (value e)
    (fun a=>value e (if q=2 then u 0 else z) ^^ value e a) (fun _ _=>em e .bxor _ _))
  intro out rest head raw
  change dif.map (value e) = ((List.range (k/3)).map (fun t=>q+3*t)).map _ at raw
  have actual : dif.map (value e)=(List.range (k/3)).map d := by rw [List.map_map] at raw; exact raw
  let b:=if q=2 then uv 0 else false
  have bval : value e (if q=2 then u 0 else z)=b := by by_cases h:q=2 <;> simp [b,uv,h,zero]
  rw [rest]
  change pre.map (fun a=>value e (if q=2 then u 0 else z) ^^ value e a) = _
  rw [bval]
  change pre.map ((fun v=>b ^^ v) ∘ (value e)) = _
  rw [←List.map_map,head,actual]
  unfold preProducts
  simp only [List.length_map,List.length_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have h : i < k/3 := List.mem_range.mp hi
  dsimp [Function.comp_def]
  rw [←List.map_take,List.take_range,Nat.min_eq_left (Nat.le_of_lt h)]
  rw [prod_delta]

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation
def toWord (e:Nat → Bool) (k:Nat) (z:W) (v:Vec) := Word.pack k (fun i=>value e (v.getD i z))
theorem bounded (e:Nat → Bool) (k:Nat) (z:W) (v:Vec) : toWord e k z v < 2^k := Word.pack_bounded ..
theorem read_here (e:Nat → Bool) (k:Nat) (z:W) (v:Vec) {i:Nat} (hi:i < k):
    (toWord e k z v).testBit i=value e (v.getD i z) := by simp [toWord,Word.pack_bit,hi]
theorem cyc_read (e:Nat → Bool) {k:Nat} (hk:0 < k) (z:W) (v:Vec) (i:Nat):
    Word.cyc k (toWord e k z v) i=bits e k v z i := read_here e k z v (Nat.mod_lt _ hk)

theorem canonical {k w v:Nat} (hw:w < 2^k) (hv:v < 2^k)
    (eq:∀ i < k,w.testBit i=v.testBit i) : w=v := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases h:i < k
  · exact eq _ h
  · have q : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw q),Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv q)]

theorem at_tab (e:Nat → Bool) (k:Nat) (z:W) (v:Vec) (f:Nat → Bool)
    (eq:v.map (value e)=(List.range k).map f) (i:Nat) (hi:i < k) :
    value e (v.getD i z)=f i := by
  have len : v.length=k := by simpa using congrArg List.length eq
  have lim:i < v.length:=by omega
  have eqi := congrArg (fun (b:List Bool)=>b[i]?) eq
  have r : (List.range k)[i]?=some i := by rw [List.getElem?_eq_getElem (by simpa using hi)];simp
  simpa [List.getD_eq_getElem?_getD,lim,r] using eqi

theorem vx_value (e:Nat → Bool) (k:Nat) (z:W) (a b:Vec):
    Good e (vX k z a b) (fun out=>toWord e k z out=(toWord e k z a ^^^ toWord e k z b)) := by
  apply mono (vec_xor e k z a b)
  intro out h
  apply canonical (bounded ..) (Nat.xor_lt_two_pow (bounded ..) (bounded ..))
  intro i lt
  rw [read_here _ _ _ _ lt,Nat.testBit_xor,read_here _ _ _ _ lt,read_here _ _ _ _ lt]
  exact at_tab e k z out _ h i lt

theorem rot_value (e:Nat → Bool) (k s:Nat) (z:W) (v:Vec) :
    toWord e k z (Make.rot k z v s)=Word.rot k s (toWord e k z v) := by
  apply canonical (bounded ..) (Nat.mod_lt _ (Nat.two_pow_pos _))
  intro i hi
  have hk : 0 < k := by omega
  have r := Word.rot_at hk (bounded e k z v) s i
  have right := cyc_read e hk z v (i+(k-s % k))
  rw [right] at r
  rw [read_here _ _ _ _ hi]
  change value e (((List.range k).map (fun j=>v.getD ((j+(k-s % k)) % k) z)).getD i z) = _
  have ri:(List.range k)[i]?=some i := by rw [List.getElem?_eq_getElem (by simpa using hi)];simp
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,ri,Option.map_some,Option.getD_some]
  simpa only [Word.rot,Word.cyc,Nat.mod_eq_of_lt hi,bits,List.getD_eq_getElem?_getD] using r.symm

theorem inverse_value (e:Nat → Bool) {k:Nat} (odd:k % 2=1) (oneW z:W) (v:Vec)
    (zero:value e z=false) (one:value e oneW=true):
    Good e (inverseChi k oneW z v) (fun out=>toWord e k z out=Word.unstep k (toWord e k z v)) := by
  apply mono (inv_compiled odd e oneW z v zero one)
  intro out h
  have hk : 0 < k := by omega
  have eq : Word.cyc k (toWord e k z v)=bits e k v z := funext (cyc_read e hk z v)
  apply canonical (bounded ..) (Word.pack_bounded ..)
  intro i hi
  rw [read_here _ _ _ _ hi,Word.pack_bit]
  simp only [hi,decide_true,Bool.true_and,eq]
  exact at_tab e k z out _ h i hi

def orLaw : Law Bool where
  one:=false;op:=or
  left x:=by cases x <;> rfl
  right x:=by cases x <;> rfl
  assoc x y z:=by cases x <;> cases y <;> cases z <;> rfl
def andLaw : Law Bool where
  one:=true;op:=and
  left x:=by cases x <;> rfl
  right x:=by cases x <;> rfl
  assoc x y z:=by cases x <;> cases y <;> cases z <;> rfl

theorem reduced (e:Nat → Bool) (M:Law Bool) (op : Tape.Op)
    (agree:∀ a b,op.eval a b=M.op a b) (z:W) (iz:value e z=M.one) (xs:Vec):
    Good e (reduce op z xs) (fun w=>value e w=M.prod (xs.map (value e))) := by
  cases xs with
  | nil=> exact pureG _ _ iz
  | cons a l=>
    let xs:=a::l
    let t:=Make.shape (fun i=>xs.getD i z) 0 xs.length
    have hh (a b:W) : Good e (emit op a b) (fun z=>value e z=M.op (value e a) (value e b)) :=
      mono (em e op a b) (fun w h=>h.trans (agree ..))
    unfold reduce
    simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    apply bindG (cache_model e M (value e) (emit op) hh t)
    intro p
    exact pureG _ p.prod (by rintro ⟨s,eq⟩;rw [product_safe M _ _ s,eq,T.up_eq,target_input _ xs z (by simp [xs])])

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.AllRotation

theorem or_off (v : List Bool) : orLaw.prod v=false ↔ ∀b∈v,b=false := by
  induction v with
  | nil => simp [Law.prod,orLaw]
  | cons a as ih =>
    change (a || orLaw.prod as)=false ↔ _
    cases a <;> simp [ih]

theorem and_on (v : List Bool) : andLaw.prod v=true ↔ ∀b∈v,b=true := by
  induction v with
  | nil => simp [Law.prod,andLaw]
  | cons a as ih =>
    change (a && andLaw.prod as)=true ↔ _
    cases a <;> simp [ih]

def diffCode (e:Nat → Bool) (k:Nat) (z:W) (us y:Vec) (i:Nat) : Bool :=
  (value e (us.getD i z) ^^ (!value e (us.getD ((i+1) % k) z) && value e (us.getD ((i+2) % k) z))) ^^ value e (y.getD i z)

theorem diff_reads (e:Nat → Bool) (k:Nat) (z:W) (us y:Vec) (i:Nat) (hi:i < k) :
    diffCode e k z us y i =
      ((Word.step k (toWord e k z us)).testBit i ^^ (toWord e k z y).testBit i) := by
  have hk : 0 < k := by omega
  have sb:=Word.step_bits hk (toWord e k z us) i
  have eq:=funext (cyc_read e hk z us)
  rw [eq] at sb
  simp only [Word.cyc,Nat.mod_eq_of_lt hi] at sb
  rw [sb,read_here e k z y hi]
  simp [diffCode,Chi.chi,bits,Nat.mod_eq_of_lt hi]

theorem xor_false (a b:Bool) : (a ^^ b)=false ↔ a=b := by cases a <;> cases b <;> decide

theorem diff_witness (e:Nat → Bool) (k:Nat) (z:W) (us y:Vec) :
    orLaw.prod ((List.range k).map (diffCode e k z us y)) =
      decide (Word.step k (toWord e k z us) ≠ toWord e k z y) := by
  let a:=Word.step k (toWord e k z us);let b:=toWord e k z y
  have eq : orLaw.prod ((List.range k).map (diffCode e k z us y))=false ↔ a=b := by
    rw [or_off]
    constructor
    · intro h
      apply canonical (show a < 2^k by dsimp [a]; rw [Word.step_eq]; exact Word.pack_bounded _ _) (bounded e k z y)
      intro i hi
      apply (xor_false _ _).mp
      rw [←diff_reads e k z us y i hi]
      exact h _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
    · rintro h j hj
      rcases List.mem_map.mp hj with ⟨i,hi,rfl⟩
      rw [diff_reads _ _ _ _ _ _ (List.mem_range.mp hi)]
      apply (xor_false _ _).mpr (congrArg (fun n:Nat=>n.testBit i) h)
  by_cases ab:a=b
  · have :=eq.mpr ab;change _=decide (a≠b);simp [this,ab]
  · change _=decide (a≠b)
    rw [decide_eq_true ab]
    cases ov:orLaw.prod ((List.range k).map (diffCode e k z us y)) with
    | false=>exact False.elim (ab (eq.mp ov))
    | true=>rfl

theorem validate (e:Nat → Bool) (k d:Nat) (oneW z:W) (zero:value e z=false) (w y:Vec) :
    Good e (check k d oneW z w y) (fun out=>value e out =
      decide (Word.step k (Word.mix k d (toWord e k z w)) ≠ toWord e k z y)) := by
  let per := fun (us : Vec) i=>do
    let b←emit .band (Unit.neg (us.getD ((i+1) % k) z)) (us.getD ((i+2) % k) z)
    let v←emit .bxor (us.getD i z) b
    emit .bxor v (y.getD i z)
  have calcB (us:Vec) (i:Nat) : Good e (per us i) (fun f=>value e f=diffCode e k z us y i) := by
    apply bindG (em e .band _ _);intro b
    apply bindG (em e .bxor _ b);intro v
    apply mono (em e .bxor v _)
    intro c ec ev eb
    simp only [diffCode,ec,ev,eb,Tape.Op.eval,value_neg]
  apply bindG (vx_value e k z w (rot k z w d));intro v
  apply bindG (vx_value e k z v (rot k z w (k-d)));intro us
  apply bindG (map_eval e (List.range k) (per us) (value e) (diffCode e k z us y) (fun i _=>calcB us i));intro bad
  apply mono (reduced e orLaw .bor (fun _ _=>rfl) z zero bad)
  intro l eqFinal bitsOK usOK vOK
  rw [eqFinal,bitsOK,diff_witness,usOK,vOK,rot_value,rot_value]
  rfl
end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire

def cell (u : Nat → Bool) (q j:Nat) : Bool :=
  (if q=2 then u 0 else false) ^^ Linear.pxor u q j
def phaseSign (p : Linear.Pair) (q:Nat):=if q=0 then p.1 else if q=1 then p.2 else xor p.1 p.2

theorem linear_cell (u:Nat → Bool) (p:Linear.Pair) (t:Nat) :
     (if phaseSign p (t % 3) then !(cell u (t % 3) (t/3)) else cell u (t % 3) (t/3)) =
        Linear.get u p t := by
  have eq:=Linear.prefix_decode u p (t % 3) (t/3)
  rw [show t % 3+3*(t/3)=t by omega] at eq
  rw [eq]
  rcases p with ⟨a,b⟩
  have h : t % 3=0 ∨ t % 3=1 ∨ t % 3=2 := by omega
  rcases h with h|h|h <;> rw [h] <;> unfold cell phaseSign <;>
    cases a <;> cases b <;> cases h0:u 0 <;> cases Linear.pxor u _ (t/3) <;>
    simp [Linear.get,Linear.walk,Linear.next,h0]

theorem lookup_map {A D : Type} (f:A → D) (g:Nat → D) (xs:List A) (z:A) (n i:Nat)
    (eq:xs.map f=(List.range n).map g) (hi:i < n) : f (xs.getD i z)=g i := by
  have ln:xs.length=n:=by simpa using congrArg List.length eq
  have li:i < xs.length:=by omega
  have eqi:=congrArg (fun (v:List D)=>v[i]?) eq
  have r : (List.range n)[i]?=some i := by rw [List.getElem?_eq_getElem (by simpa using hi)];simp
  simpa [List.getD_eq_getElem?_getD,li,r] using eqi

def uns (k d i:Nat):=if d=1 then i else if i % 2=0 then i/2 else (i+k)/2
theorem unlt {k d i:Nat} (h:k % 2=1) (hi:i < k) : uns k d i < k := by
  unfold uns;split
  · exact hi
  · split <;> omega

def childWord (k d:Nat) (z:W) (ss: List Vec) (p:Linear.Pair) :=
  (List.range k).map fun i=>
    let t:=uns k d i
    let w:=(ss.getD (t % 3) []).getD (t/3) z
    if phaseSign p (t % 3) then Unit.neg w else w

theorem child_word {k d:Nat} (h:k % 6=3) (e:Nat → Bool) (z:W) (ss:List Vec) (y:Nat) (p:Linear.Pair)
    (layers:ss.map (List.map (value e))=(List.range 3).map (fun q=>(List.range (k/3)).map (cell (Word.measured k d y) q))) :
    toWord e k z (childWord k d z ss p)=Word.gen k d y p := by
  apply canonical (bounded ..) (Word.pack_bounded ..)
  intro i hi
  let t:=uns k d i
  let q:=t % 3
  let j:=t/3
  have tlt:t < k:=unlt (by omega) hi
  have qlt:q < 3:=Nat.mod_lt _ (by decide)
  have jlt:j < k/3:=by dsimp [j];omega
  have found:=lookup_map _ _ _ [] 3 q layers qlt
  have cellOK:=lookup_map _ _ _ z _ j found jlt
  rw [read_here e k z _ hi,Word.pack_bit]
  simp only [hi,decide_true,Bool.true_and]
  have rr:(List.range k)[i]?=some i:=by rw [List.getElem?_eq_getElem (by simpa using hi)];simp
  have get : (childWord k d z ss p).getD i z=
      if phaseSign p q then Unit.neg ((ss.getD q []).getD j z) else (ss.getD q []).getD j z := by
    simp [childWord,List.getD_eq_getElem?_getD,rr];rfl
  rw [get]
  have lin:=linear_cell (Word.measured k d y) p t
  change (if _ then _ else _) = Linear.get (Word.measured k d y) p t at lin
  change value e (if phaseSign p q then _ else _) = Linear.get (Word.measured k d y) p t
  by_cases active:phaseSign p q=true
  · rw [if_pos active,value_neg,cellOK]
    simpa only [q,j,active,ite_true] using lin
  · rw [if_neg active,cellOK]
    simpa [q,j,active] using lin

def decodeEntry (e:Nat → Bool) (k:Nat) (z:W) (p:Make.Entry) : Nat×Bool :=
  (toWord e k z p.1,!value e p.2)

theorem child_sem {k d:Nat} (h:k % 6=3) (e:Nat → Bool) (z o dead:W) (zero:value e z=false)
    (ss:List Vec) (target:Vec) (y:Nat) (p:Linear.Pair)
    (layers:ss.map (List.map (value e))=(List.range 3).map (fun q=>(List.range (k/3)).map (cell (Word.measured k d y) q))) :
    Good e (child k d o z dead target ss p) (fun w=>
      let num:=Word.gen k d y p
      decodeEntry e k z w=(num,(!value e dead && decide (Word.step k (Word.mix k d num)=toWord e k z target)))) := by
  let w:=childWord k d z ss p
  have ww:=child_word h e z ss y p layers
  apply bindG (validate e k d o z zero w target)
  intro bad
  apply bindG (em e .bor dead bad)
  intro flag
  exact pureG _ (w,flag) (by
    intro bf val
    change (toWord e k z w,!value e flag)=_
    rw [bf,val,ww]
    simp [Tape.Op.eval,Bool.not_or])
end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire

def scalarChild (e:Nat → Bool) (k d:Nat) (z dead:W) (ss:List Vec) (target:Vec) (p:Linear.Pair) :=
  let n:=toWord e k z (childWord k d z ss p)
  (n,!value e dead && decide (Word.step k (Word.mix k d n)=toWord e k z target))

theorem child_unconditional (e:Nat → Bool) (k d:Nat) (z o dead:W) (zero:value e z=false)
    (ss:List Vec) (target:Vec) (p:Linear.Pair) :
    Good e (child k d o z dead target ss p) (fun w=>decodeEntry e k z w=scalarChild e k d z dead ss target p) := by
  let w:=childWord k d z ss p
  apply bindG (validate e k d o z zero w target)
  intro bad;apply bindG (em e .bor dead bad);intro flag
  exact pureG _ (w,flag) (by
    intro bf val
    change (toWord e k z w,!value e flag)=_
    rw [bf,val];simp [scalarChild,w,Tape.Op.eval,Bool.not_or])

theorem sideSet (e:Nat → Bool) (k:Nat) (z:W) (zero:value e z=false) (u:Nat → W) :
    Good e (byIndex 3 (coordSide k z u)) (fun ss=>
      ss.map (List.map (value e))=(List.range 3).map (fun q=>(List.range (k/3)).map (cell (fun t=>value e (u t)) q))) :=
  map_eval e _ _ _ _ (fun q _=>side_model e k z zero u q)

theorem xor_move (x m y:Nat): (x=y ^^^ m) ↔ (x ^^^ m = y) := by
  constructor
  · rintro rfl;simp [Nat.xor_assoc]
  · intro h;rw [←h,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem expand_value {k d:Nat} (h:k % 6=3) (e:Nat → Bool) (oneW zero:W)
    (hz:value e zero=false) (ho:value e oneW=true) (parent:Make.Entry) (mask:Vec) :
    Good e (expand k d oneW zero parent mask) (fun kids=>
      kids.map (decodeEntry e k zero)=Family.children k d (toWord e k zero mask) (decodeEntry e k zero parent)) := by
  let y0:=toWord e k zero parent.1;let m:=toWord e k zero mask
  have hk:0 < k:=by omega
  apply bindG (vx_value e k zero parent.1 mask);intro y
  apply bindG (inverse_value e (show k % 2=1 by omega) oneW zero y hz ho);intro iv
  let signal:=fun t:Nat=>iv.getD ((d*(t+1)) % k) zero
  apply bindG (sideSet e k zero hz signal);intro ss
  apply mono (map_eval e signs (child k d oneW zero parent.2 y ss) (decodeEntry e k zero)
    (scalarChild e k d zero parent.2 ss y) (fun p _=>child_unconditional e k d zero oneW parent.2 hz ss y p))
  intro out alg layers ivOK yOK
  change toWord e k zero y=y0 ^^^ m at yOK
  have sig : (fun t=>value e (signal t))=Word.measured k d (Word.unstep k (y0 ^^^ m)) := by
    funext t;unfold Word.measured Word.cyc
    rw [←yOK,←ivOK,read_here _ _ _ _ (Nat.mod_lt _ hk)]
  rw [sig] at layers
  rw [alg]
  change signs.map _ = Linear.choices.map _
  change List.map _ Linear.choices=List.map _ Linear.choices
  apply List.map_congr_left; intro p mem
  have eqW:=child_word (d:=d) h e zero ss (Word.unstep k (y0 ^^^ m)) p layers
  simp only [scalarChild,eqW,yOK,decodeEntry,Family.back,Family.phase]
  simp only [xor_move (Word.step k (Word.mix k d (Word.gen k d (Word.unstep k (y0 ^^^ m)) p))) m y0]
  rfl

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire

def M (k r d key j:Nat) := if d=1 then Tracks.rowMask k key j else Tracks.colMask k r key j

theorem mask_word (e:Nat → Bool) (k r d j:Nat) (z:W) (key:Vec):
    toWord e k z (mask k r d j z key)=M k r d (toWord e k z key) j := by
  let s:=if d=1 then 2*j else 3*(j+1)+1
  let c:=Tracks.constant k (if d=1 then j+1 else r+(j+1))
  have me : M k r d (toWord e k z key) j=Word.rot k s (toWord e k z key) ^^^ c := by
    by_cases h:d=1 <;> simp [M,s,c,Tracks.rowMask,Tracks.colMask,h]
  rw [me]
  apply canonical (bounded ..) (Nat.xor_lt_two_pow (Tracks.rot_bounded ..) (Tracks.const_bounded ..))
  intro i hi
  rw [read_here _ _ _ _ hi,Nat.testBit_xor,←rot_value e k s z key,read_here _ _ _ _ hi]
  have rr:(List.range k)[i]?=some i:=by rw [List.getElem?_eq_getElem (by simpa using hi)];simp
  let b:=(Make.rot k z key s).getD i z
  change value e (((List.range k).map (fun t=>if c.testBit t then Unit.neg ((Make.rot k z key s).getD t z) else (Make.rot k z key s).getD t z)).getD i z)
      =(value e b ^^ c.testBit i)
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,rr,Option.map_some,Option.getD_some]
  cases h:c.testBit i <;> simp [b,value_neg,List.getD_eq_getElem?_getD]

theorem all_append (k d:Nat) (xs ys:List Nat) (e:Family.Entry):
    Family.all k d (xs++ys) e=(Family.all k d ys e).flatMap (Family.all k d xs) := by
  induction xs with
  | nil=>simp [Family.all]
  | cons x xs ih=>simp [Family.all,ih,List.flatMap_assoc,Function.comp_def]

theorem layers_value {k d:Nat} (h:k % 6=3) (e:Nat → Bool) (r:Nat) (o z:W)
    (hz:value e z=false) (ho:value e o=true) (key:Vec) (js:List Nat) (ns:List Make.Entry) :
    Good e (genLayers k r d o z key js ns) (fun final=>
      final.map (decodeEntry e k z)=(ns.map (decodeEntry e k z)).flatMap
        (Family.all k d (js.reverse.map (M k r d (toWord e k z key))))) := by
  let dec:=decodeEntry e k z
  let mk:=M k r d (toWord e k z key)
  induction js generalizing ns with
  | nil=>exact pureG _ _ (by simp [Family.all])
  | cons j js ih=>
    apply bindG (map_eval e ns (fun p=>expand k d o z p (mask k r d j z key))
      (List.map dec) (fun p=>Family.children k d (mk j) (dec p))
      (fun p _=>by simpa only [mask_word] using expand_value (d:=d) h e o z hz ho p (mask k r d j z key)))
    intro kids
    apply mono (ih kids.flatten)
    intro result deeper kidsOk
    rw [deeper]
    change List.flatMap _ (kids.flatten.map dec) = _
    rw [List.map_flatten,kidsOk]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.flatMap_map]
    rw [←List.flatMap_def,List.flatMap_assoc]
    apply congrArg (fun f=>ns.flatMap f)
    funext p
    rw [all_append]
    simp [Family.all,mk,dec]

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire

theorem xor_detect (e:Nat → Bool) (k:Nat) (z:W) (a b mm:Vec)
    (bitsOK:mm.map (value e)=(List.range k).map
      (fun i=>xor (value e (a.getD i z)) (value e (b.getD i z)))) :
    orLaw.prod (mm.map (value e))=decide (toWord e k z a≠toWord e k z b) := by
  let p:=toWord e k z a;let q:=toWord e k z b
  have hf : orLaw.prod (mm.map (value e))=false ↔ p=q := by
    rw [or_off,bitsOK]
    constructor
    · intro h
      apply canonical (bounded ..) (bounded ..)
      intro j hj;rw [read_here _ _ _ _ hj,read_here _ _ _ _ hj]
      exact (xor_false _ _).mp (h _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))
    · intro eq bval mem
      rcases List.mem_map.mp mem with ⟨i,hi,rfl⟩;have lt:=List.mem_range.mp hi
      apply (xor_false _ _).mpr
      rw [←read_here _ k z a lt,←read_here _ k z b lt]
      exact congrArg (fun n:Nat=>n.testBit i) eq
  by_cases eq:p=q
  · change _=decide (p≠q);simp [hf.mpr eq,eq]
  · change _=decide (p≠q);rw [decide_eq_true eq]
    cases ev : orLaw.prod (mm.map (value e)) with
    | false => exact False.elim (eq (hf.mp ev))
    | true => rfl

def filtered (init name : Nat) (p : Family.Entry) : Family.Entry :=
  (init ^^^ p.1, p.2 && decide ((init ^^^ p.1)=name))

theorem checked_name (e:Nat → Bool) (k:Nat) (z:W) (iz:value e z=false) (initial nm:Vec) (p:Make.Entry):
    Good e (filterName k z initial nm p) (fun out=>
      decodeEntry e k z out=filtered (toWord e k z initial) (toWord e k z nm) (decodeEntry e k z p)) := by
  apply bindG (vx_value e k z p.1 initial);intro pred
  apply bindG (vec_xor e k z nm pred);intro mm
  apply bindG (reduced e orLaw .bor (fun _ _=>rfl) z iz (p.2::mm));intro flag
  apply pureG
  intro fg mmOK predOK
  have xm:=xor_detect e k z nm pred mm mmOK
  change (toWord e k z pred,!value e flag)=_
  rw [fg,List.map_cons]
  change (_,!(value e p.2 || orLaw.prod (mm.map (value e))))=_
  rw [xm,predOK,Nat.xor_comm (toWord e k z p.1) _]
  simp [filtered,decodeEntry,Bool.not_or,eq_comm]

theorem filter_live {name init : Nat} {xs : List Family.Entry} :
    (∃ p∈xs.map (filtered init name),p.2=true) ↔ (init ^^^ name,true)∈xs := by
  constructor
  · rintro ⟨p,mp,ok⟩
    rcases List.mem_map.mp mp with ⟨⟨w,v⟩,inxs,rfl⟩
    change (v && decide ((init ^^^ w)=name))=true at ok
    rw [Bool.and_eq_true] at ok
    rcases ok with ⟨rfl,eq⟩
    have eqW := of_decide_eq_true eq
    rw [←eqW,←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]
    exact inxs
  · intro h
    exact ⟨_,List.mem_map.mpr ⟨_,h,rfl⟩,by simp [filtered,←Nat.xor_assoc]⟩

def preMasks (k r d key:Nat) := (List.range r).map (M k r d key)
theorem generated_labels {k : Nat} (h:k % 6=3) (e:Nat → Bool) (r d:Nat) (o z:W)
    (hz:value e z=false) (ho:value e o=true) :
    let key:=raw k 2
    let y:=raw k (d+2)
    let init:=rot k z key (if d=1 then 1 else 3)
    let nm:=raw k (d-1)
    Good e (do
      let nodes←genLayers k r d o z key (List.range r).reverse [(y,z)]
      nodes.mapM (filterName k z init nm))
    (fun labels=>labels.map (decodeEntry e k z)=
      (Family.all k d (preMasks k r d (toWord e k z key)) (toWord e k z y,true)).map
      (filtered (toWord e k z init) (toWord e k z nm))) := by
  dsimp only
  let key:=raw k 2;let out:=raw k (d+2)
  let init:=rot k z key (if d=1 then 1 else 3)
  let name:=raw k (d-1);let dec:=decodeEntry e k z
  apply bindG (layers_value h e r o z hz ho key (List.range r).reverse [(out,z)]);intro nodes
  apply mono (map_eval e nodes (filterName k z init name) dec
    (fun p=>filtered (toWord e k z init) (toWord e k z name) (dec p)) (fun _ _=>checked_name e k z hz init name _))
  intro ls actual tree
  rw [actual]
  change nodes.map ((filtered (toWord e k z init) (toWord e k z name)) ∘ dec)=_
  rw [←List.map_map,tree]
  simp [preMasks,decodeEntry,hz,dec,init,key,name,out]

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit

def side (e:Nat → Bool) (s:Net) := ∀c∈s.constraints, ∃l∈c,e l.1=l.2
def D (e:Nat → Bool) (m:B A) (T:Prop) :=
  ∀s,LinesOK e (m.run s).2 → LinesOK e s ∧ (side e (m.run s).2 ↔ side e s ∧ T)
theorem dAdd (e:Nat → Bool) (c:Clause Nat) : D e (add c) (∃l∈c.take 3,e l.1=l.2) := by
  intro s h; refine ⟨h,?_⟩
  change (∀ g∈c.take 3::s.constraints,∃ l∈g,e l.1=l.2) ↔ _
  constructor
  · intro ok;exact ⟨fun g m=>ok g (List.mem_cons_of_mem _ m),ok _ (List.mem_cons_self ..)⟩
  · rintro ⟨old,new⟩ g mg
    rcases List.mem_cons.mp mg with rfl|h
    · exact new
    · exact old _ h
theorem dPure (e:Nat → Bool) (a:A) : D e (pure a) True := fun s h=>⟨h,by change side e s ↔ side e s ∧ True;simp⟩
theorem dIff {e:Nat → Bool} {m:B A} {T U:Prop} (h:D e m T) (eq:T↔U) : D e m U := by
  intro s h₀;rcases h s h₀ with ⟨l,ok⟩;exact ⟨l,ok.trans (and_congr_right (fun _=>eq))⟩
theorem link {e:Nat → Bool} {m:B A} {f:A → B C} {P:A → Prop} {R:A → Prop} {Q:Prop}
    (h:Good e m P) (k:∀a,D e (f a) (R a)) (done:∀a,P a → (R a↔Q)) : D e (m >>= f) Q := by
  intro s final
  obtain ⟨entry,fc⟩:=k (m.run s).1 (m.run s).2 final
  obtain ⟨⟨beg,same⟩,pa⟩:=h s entry
  have equals : side e (m.run s).2 ↔ side e s := by unfold side;rw [same]
  exact ⟨beg,fc.trans (and_congr equals (done _ pa))⟩
theorem seqD {e:Nat → Bool} {m:B A} {f:A → B C} {T Q:Prop}
    (a:D e m T) (b:∀x,D e (f x) Q) : D e (m >>= f) (T∧Q) := by
  intro s final
  obtain ⟨mid,fs⟩:=b (m.run s).1 (m.run s).2 final
  obtain ⟨old,mk⟩:=a s mid
  exact ⟨old,fs.trans ((and_congr_left (fun _=>mk)).trans and_assoc)⟩
theorem dMap {e:Nat → Bool} (l:List A) (m:A → B C) {T:A → Prop} (atOne:∀a,D e (m a) (T a)):
    D e (l.mapM m) (∀a∈l,T a) := by
  induction l with
  | nil => exact dIff (dPure e []) (by simp)
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact dIff (seqD (atOne x) (fun c=>seqD ih (fun cs=>dPure e (c::cs)))) (by simp [forall_eq_or_imp])

theorem literalOK (e:Nat → Bool) (p:W) : (∃l∈[p],e l.1=l.2) ↔ value e p=true := by
  simp [value]
theorem twoOK (e:Nat → Bool) (p q:W) :
    (∃l∈[p,q],e l.1=l.2) ↔ value e p=true ∨ value e q=true := by
  simp [value]

def live (e:Nat → Bool) (p:Make.Entry) := value e p.2=false
def bit (e:Nat → Bool) (v:Vec) (z:W) (i:Nat):= value e (v.getD i z)
def support (e:Nat → Bool) (labels:List Make.Entry) (i:Nat) (sign:Bool) (z:W) :=
  ∃p∈labels,live e p ∧ bit e p.1 z i=sign

theorem any_false (v:List Bool) : andLaw.prod v=false ↔ ∃b∈v,b=false := by
  induction v with
  | nil=>simp [AllRotation.Law.prod,andLaw]
  | cons b bs ih=>
    change (b && andLaw.prod bs)=false ↔ _
    cases b <;> simp [ih]

theorem block_side (e:Nat → Bool) (k:Nat) (o z:W) (ho:value e o=true)
    (nm:Vec) (labels:List Make.Entry) (i:Nat) (sign:Bool) :
    D e (block k o z nm labels i sign) (bit e nm z i=sign → support e labels i sign z) := by
  let bad := fun p:Make.Entry=>value e p.2 || (if sign then !bit e p.1 z i else bit e p.1 z i)
  let f := fun p:Make.Entry=>emit .bor p.2 (if sign then neg (p.1.getD i z) else p.1.getD i z)
  let nmLit:=if sign then neg (nm.getD i z) else nm.getD i z
  have flags := map_eval e labels f (value e) bad (fun p _=>mono (em e .bor p.2 _) (by
    intro w hw;rw [hw];cases sign <;> simp [bad,bit,Tape.Op.eval,value_neg]))
  apply link flags
    (fun fl=>link (reduced e andLaw .band (fun _ _=>rfl) o ho fl)
      (fun g=>dAdd e [neg g,nmLit]) (Q:=(andLaw.prod (fl.map (value e))=false ∨ value e nmLit=true))
      (by intro g hg; change (∃l∈[neg g,nmLit],e l.1=l.2) ↔ _;rw [twoOK,value_neg,hg];simp))
  intro fl hfl
  rw [hfl,any_false]
  have n : value e nmLit=true ↔ bit e nm z i≠sign := by
    cases sign <;> simp [nmLit,bit,value_neg] <;> cases value e (nm.getD i z) <;> decide
  rw [n]
  have be : (∃b∈labels.map bad,b=false) ↔ support e labels i sign z := by
    constructor
    · rintro ⟨b,hb,ob⟩
      rcases List.mem_map.mp hb with ⟨p,hp,rfl⟩
      refine ⟨p,hp,?_⟩
      unfold bad at ob;unfold live
      cases sign <;> simp_all
    · rintro ⟨p,hp,lv,bs⟩
      exact ⟨_,List.mem_map.mpr ⟨p,hp,rfl⟩,by cases sign <;> simp_all [bad,live]⟩
  rw [be]
  constructor
  · rintro (got|no) hh
    · exact got
    · exact False.elim (no hh)
  · intro f
    by_cases eq:bit e nm z i=sign
    · exact .inl (f eq)
    · exact .inr eq

theorem global_side (e:Nat → Bool) (o:W) (ho:value e o=true) (labels:List Make.Entry) :
    D e (do let g←reduce .band o (labels.map Prod.snd);add [neg g]) (∃p∈labels,live e p) := by
  apply link (reduced e andLaw .band (fun _ _=>rfl) o ho _)
    (fun g=>dAdd e [neg g])
  intro g ok
  change (∃l∈[neg g],e l.1=l.2) ↔ _
  rw [literalOK,value_neg,ok]
  simp only [Bool.not_eq_true',any_false,List.map_map]
  constructor
  · rintro ⟨b,hb,ob⟩
    rcases List.mem_map.mp hb with ⟨p,hp,rfl⟩;exact ⟨p,hp,ob⟩
  · rintro ⟨p,hp,ok⟩;exact ⟨_,List.mem_map.mpr ⟨p,hp,rfl⟩,ok⟩
end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit

def blocksProp (e:Nat → Bool) (k:Nat) (nm:Vec) (labels:List Make.Entry) (z:W) :=
  ∀i∈List.range k,
  (bit e nm z i=false → support e labels i false z) ∧
  (bit e nm z i=true → support e labels i true z)

def checks (k:Nat) (o z:W) (nm:Vec) (labels:List Make.Entry) : Make.B Unit := do
  let allBad←reduce .band o (labels.map Prod.snd)
  add [neg allBad]
  let _←(List.range k).mapM (fun i=>do
    block k o z nm labels i false
    block k o z nm labels i true)
  pure ()

theorem checks_side (e:Nat → Bool) (k:Nat) (o z:W) (ho:value e o=true) (nm:Vec) (labels:List Make.Entry) :
    D e (checks k o z nm labels) ((∃p∈labels,live e p) ∧ blocksProp e k nm labels z) := by
  have loop:=dMap (e:=e) (List.range k) (fun i=>do
      block k o z nm labels i false
      block k o z nm labels i true) (fun i=>
    seqD (block_side e k o z ho nm labels i false) (fun _=>block_side e k o z ho nm labels i true))
  have g:=seqD (global_side e o ho labels) (fun _=>seqD loop (fun _=>dPure e ()))
  exact dIff g (by simp [blocksProp])

theorem live_word (e:Nat → Bool) (k:Nat) (z:W) (nm:Vec) (labels:List Make.Entry)
    (ini:Nat) (xs:List Family.Entry)
    (lab:labels.map (decodeEntry e k z)=xs.map (filtered ini (toWord e k z nm))) :
    ((∃p∈labels,live e p) ∧ blocksProp e k nm labels z) ↔ (ini ^^^ toWord e k z nm,true)∈xs := by
  let n:=toWord e k z nm
  have eqL : (∃p∈labels,live e p) ↔ (ini ^^^ n,true)∈xs := by
    rw [←filter_live,←lab]
    constructor
    · rintro ⟨p,hp,lv⟩;exact ⟨decodeEntry e k z p,List.mem_map.mpr ⟨p,hp,rfl⟩,by simp [decodeEntry,live] at *;assumption⟩
    · rintro ⟨b,mem,hh⟩
      rcases List.mem_map.mp mem with ⟨p,hp,rfl⟩
      exact ⟨p,hp,by simpa [decodeEntry,live] using hh⟩
  constructor
  · exact fun h=>eqL.mp h.1
  · intro good
    rcases eqL.mpr good with ⟨p,mem,lv⟩
    refine ⟨⟨p,mem,lv⟩,?_⟩
    have inc : decodeEntry e k z p∈xs.map (filtered ini n) := by rw [←lab];exact List.mem_map.mpr ⟨p,mem,rfl⟩
    rcases List.mem_map.mp inc with ⟨t,ht,eq⟩
    have a:=congrArg Prod.fst eq;have b:=congrArg Prod.snd eq
    change ini ^^^ t.1=toWord e k z p.1 at a
    change (t.2 && decide ((ini ^^^ t.1)=n)) = !value e p.2 at b
    rw [show value e p.2=false from lv,a] at b
    simp only [Bool.not_false,Bool.and_eq_true,decide_eq_true_eq] at b
    have beq (i:Nat) (hi:i < k) : bit e p.1 z i=bit e nm z i := by
      change value e (p.1.getD i z)=value e (nm.getD i z)
      rw [←read_here _ k _ _ hi,←read_here _ k _ _ hi];exact congrArg (fun a:Nat=>a.testBit i) b.2
    intro i hi
    exact ⟨fun val=>⟨p,mem,lv,(beq i (List.mem_range.mp hi)).trans val⟩,
      fun val=>⟨p,mem,lv,(beq i (List.mem_range.mp hi)).trans val⟩⟩

def laneAccept (e:Nat → Bool) (k r d:Nat) (z:W) :=
  let key:=toWord e k z (raw k 2)
  let nm:=toWord e k z (raw k (d-1))
  let out:=toWord e k z (raw k (d+2))
  let ini:=Word.rot k (if d=1 then 1 else 3) key
  Family.direct k d (preMasks k r d key) (ini ^^^ nm)=out

theorem track_model {k d:Nat} (h:k % 6=3) (hd:d=1 ∨ d=2) (e:Nat → Bool)
    (r:Nat) (o z:W) (hz:value e z=false) (ho:value e o=true) :
    D e (track k r d o z) (laneAccept e k r d z) := by
  let key:=raw k 2;let nm:=raw k (d-1);let y:=raw k (d+2)
  let ini:=rot k z key (if d=1 then 1 else 3)
  let keyV:=toWord e k z key
  let nameV:=toWord e k z nm
  let outV:=toWord e k z y
  let ms:=preMasks k r d keyV
  apply link (generated_labels h e r d o z hz ho) (fun ls=>checks_side e k o z ho nm ls)
  intro ls lab
  rw [live_word e k z nm ls (toWord e k z ini) (Family.all k d ms (outV,true)) lab]
  have mb : ∀m∈ms,m < 2^k := by
    intro m hm
    rcases List.mem_map.mp hm with ⟨j,jm,rfl⟩
    by_cases hd1 : d=1
    · rw [M,if_pos hd1]
      exact Nat.xor_lt_two_pow (Tracks.rot_bounded ..) (Tracks.const_bounded ..)
    · rw [M,if_neg hd1]
      exact Nat.xor_lt_two_pow (Tracks.rot_bounded ..) (Tracks.const_bounded ..)
  have form:=Family.all_valid (d:=d) (ok:=true) (by omega : k % 2=1) hd (by omega) ms mb (bounded e k z y) (toWord e k z ini ^^^ nameV)
  rw [form]
  have bound:=Nat.xor_lt_two_pow (bounded e k z ini) (bounded e k z nm)
  change (true=true ∧ (toWord e k z ini ^^^ nameV) < 2^k ∧ _) ↔ _
  simp only [true_and]
  have rem : (toWord e k z ini ^^^ nameV) < 2^k := bound
  rw [and_iff_right rem]
  rw [rot_value e k (if d=1 then 1 else 3) z key]
  rfl

theorem lane_row (e:Nat → Bool) (k r:Nat) (z:W) : laneAccept e k r 1 z ↔
    Tracks.first k r (toWord e k z (raw k 2)) (toWord e k z (raw k 0))=toWord e k z (raw k 3) := by
  rw [Tracks.first_eq];rfl

theorem lane_col (e:Nat → Bool) (k r:Nat) (z:W) : laneAccept e k r 2 z ↔
    Tracks.second k r (toWord e k z (raw k 2)) (toWord e k z (raw k 1))=toWord e k z (raw k 4) := by
  rw [Tracks.second_eq];rfl
end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit

theorem unique_id {ls:List Line} (nodup:(ls.map Line.id).Nodup)
    {l l':Line} (hl:l∈ls) (hr:l'∈ls) (eq:l.id=l'.id) : l=l' := by
  induction ls with
  | nil => simp at hl
  | cons a as ih =>
    obtain ⟨notin,nd⟩:=List.nodup_cons.mp nodup
    rcases List.mem_cons.mp hl with e1|t1
    · rcases List.mem_cons.mp hr with e2|t2
      · exact e1.trans e2.symm
      · exact False.elim (notin (List.mem_map.mpr ⟨_,t2,eq.symm.trans (congrArg Line.id e1)⟩))
    · rcases List.mem_cons.mp hr with e2|t2
      · exact False.elim (notin (List.mem_map.mpr ⟨_,t1,eq.trans (congrArg Line.id e2)⟩))
      · exact ih nd t1 t2

noncomputable def getVal (s:Net) (base:Nat → Bool) (j:Nat) : Bool := by
  classical
  exact if found : ∃l∈s.lines,l.id=j then
    let l:=Classical.choose found
    have spec:=Classical.choose_spec found
    have lt: l.a.1 < j ∧ l.b.1 < j := by
      obtain ⟨_,ha,hb,_⟩:=s.ordered l spec.1
      have eq : l.id=j := spec.2
      omega
    l.op.eval (getVal s base l.a.1 == l.a.2) (getVal s base l.b.1 == l.b.2)
  else base j
termination_by j
decreasing_by all_goals first | exact lt.1 | exact lt.2

theorem val_line (s:Net) (base:Nat → Bool) : LinesOK (getVal s base) s := by
  intro l hl
  rw [HoldsLine,getVal]
  have found: ∃x∈s.lines,x.id=l.id := ⟨l,hl,rfl⟩
  rw [dif_pos found]
  have eq := unique_id s.nodup (Classical.choose_spec found).1 hl (Classical.choose_spec found).2
  simp only [eq,value]

theorem val_free (s:Net) (base:Nat → Bool) (j:Nat)
    (no:¬∃l∈s.lines,l.id=j) : getVal s base j=base j := by
  rw [getVal,dif_neg no]

theorem val_even (s:Net) (base:Nat → Bool) (j:Nat) : getVal s base (2*j)=base (2*j) := by
  apply val_free
  rintro ⟨l,hl,e⟩
  have odd:=(s.ordered l hl).2.2.2
  omega

end Pcx293.Sim

namespace Pcx293.Sim
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit
def constantWire (k:Nat) := pos (2*(5*k))
def rowWord (e:Nat → Bool) (k track:Nat) := Word.pack k (fun i=>e (2*(k*track+i)))
def agrees (e:Nat → Bool) (k r:Nat) :=
  rowWord e k 3=Tracks.first k r (rowWord e k 2) (rowWord e k 0) ∧
  rowWord e k 4=Tracks.second k r (rowWord e k 2) (rowWord e k 1)

theorem raw_word (e:Nat → Bool) (k:Nat) (z:W) (t:Nat) :
    toWord e k z (raw k t)=rowWord e k t := by
  apply canonical (bounded ..) (Word.pack_bounded ..)
  intro i lt
  have ri:(List.range k)[i]?=some i := by rw [List.getElem?_eq_getElem (by simpa using lt)];simp
  rw [read_here _ _ _ _ lt];rw [Word.pack_bit]
  simp [raw,List.getD_eq_getElem?_getD,ri,value,pos,lt]

theorem full_formula {k r:Nat} (h:k % 6=3) (e:Nat → Bool) :
    Sat (fun c=>c∈(make k r).form) e ↔
      LinesOK e (make k r) ∧ e (2*(5*k))=true ∧ agrees e k r := by
  let o:=constantWire k
  let z:=neg o
  let init:Net:={n:=5*k+1}
  let both:=fun (_:Unit)=>do
    track k r 2 o z
    add [o]
  have ref (ho:e (2*(5*k))=true) : value e o=true := by simp [o,constantWire,value,pos,ho]
  have equivalence (ho:e (2*(5*k))=true) (eqs:LinesOK e (make k r)) :
      side e (make k r) ↔ agrees e k r := by
    have ho':=ref ho
    have hz:value e z=false := by simpa [z,value_neg,ho']
    have p:=seqD (track_model h (.inl rfl) e r o z hz ho') (fun _=>
      seqD (track_model h (.inr rfl) e r o z hz ho') (fun _=>dAdd e [o]))
    have t:=(p init eqs).2
    change side e (make k r) ↔ side e init ∧ laneAccept e k r 1 z ∧ laneAccept e k r 2 z ∧
      (∃l∈[o],e l.1=l.2) at t
    rw [t,literalOK,ho',lane_row,lane_col]
    have ini:side e init:=by intro c mc;cases mc
    simp only [ini,true_and,and_true,raw_word,agrees]
    exact and_congr eq_comm eq_comm
  rw [model_iff]
  constructor
  · rintro ⟨hw,hs⟩
    have mem:[o]∈(make k r).constraints:=List.mem_cons_self ..
    have on:=(literalOK e o).mp (hs _ mem)
    have ho:e (2*(5*k))=true:=by simpa [o,constantWire,value,pos] using on
    exact ⟨hw,ho,(equivalence ho hw).mp hs⟩
  · rintro ⟨hw,ho,ok⟩
    exact ⟨hw,(equivalence ho hw).mpr ok⟩

theorem model_exists {k r:Nat} (h:k % 6=3) (base:Nat → Bool)
    (one:base (2*(5*k))=true) :
    agrees base k r ↔ ∃e:Nat → Bool, (∀j,e (2*j)=base (2*j)) ∧ Sat (fun c=>c∈(make k r).form) e := by
  have follows (e:Nat → Bool) (he:∀j,e (2*j)=base (2*j)) : agrees e k r ↔ agrees base k r := by
    unfold agrees rowWord;simp only [he]
  constructor
  · intro ok
    let s:=make k r
    let e:=getVal s base
    have ev : ∀j,e (2*j)=base (2*j):=val_even s base
    exact ⟨e,ev,(full_formula h e).mpr ⟨val_line s base,(ev _).trans one,(follows e ev).mpr ok⟩⟩
  · rintro ⟨e,ev,ok⟩
    exact (follows e ev).mp ((full_formula h e).mp ok).2.2

end Pcx293.Sim

namespace Pcx293.Dense
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Sim PEqualNP.Outside.L_pcx_293.Pcx293.Unit
abbrev V (k:Nat) := Fin 5 × Fin k
def size (k r:Nat) := (make k r).n+1
def ids (k r:Nat):= (make k r).lines.map Line.id
def rawAt (k:Nat) (hk:0 < k) (j:Nat) : Option (V k) :=
  if raw : j % 2=0 ∧ j/2 < 5*k then some (⟨(j/2)/k,(Nat.div_lt_iff_lt_mul hk).mpr raw.2⟩,⟨(j/2) % k,Nat.mod_lt _ hk⟩)
  else none
def name (k r:Nat) (hk:0 < k) (j:Nat) : Sum (V k) (Fin (size k r)) :=
  if mem:j∈ids k r then .inr ⟨(ids k r).idxOf j + 1,by
    have l:=List.idxOf_lt_length_of_mem mem
    have sz: (ids k r).length ≤ (make k r).n := by simpa [ids] using (make k r).slots
    unfold size;omega⟩
  else match rawAt k hk j with
    | some t => .inl t
    | none => .inr ⟨0,Nat.zero_lt_succ _⟩

def base (k:Nat) (hk:0 < k) (v:V k → Bool) (j:Nat) : Bool := ((rawAt k hk j).map v).getD true
noncomputable def aux (k r:Nat) (hk:0 < k) (v:V k → Bool) (i:Fin (size k r)) :=
  if i.val=0 then true else getVal (make k r) (base k hk v) ((ids k r).getD (i.val-1) 0)

theorem even_no_id (k r j:Nat) : 2*j∉ids k r := by
  rintro h
  rcases List.mem_map.mp h with ⟨l,hl,eq⟩
  have odd:=((make k r).ordered l hl).2.2.2
  omega

theorem canonical (k r:Nat) (hk:0 < k) (v:V k → Bool) (j:Nat):
    Sum.elim v (aux k r hk v) (name k r hk j)=getVal (make k r) (base k hk v) j := by
  by_cases h:j∈ids k r
  · have lt:=List.idxOf_lt_length_of_mem h
    simp [name,h,aux,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,List.getElem_idxOf]
  · rw [val_free _ _ _ (by rintro ⟨l,hl,eq⟩;apply h;exact List.mem_map.mpr ⟨l,hl,eq⟩)]
    simp only [name,h,dite_eq_right,base]
    cases e:rawAt k hk j <;> simp [aux]

theorem raw_coord (k:Nat) (h:0 < k) (t:Fin 5) (i:Fin k) :
    rawAt k h (2*(k*t.val+i.val))=some (t,i) := by
  have smaller : k*t.val+i.val < 5*k := by
    calc
      _ < k*t.val+k := Nat.add_lt_add_left i.isLt _
      _ = (t.val+1)*k := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm t.val k]
      _ ≤ _ := Nat.mul_le_mul_right k (by have := t.isLt;omega)
  simp [rawAt,smaller,Nat.mul_add_div h,Nat.div_eq_of_lt i.isLt,Nat.mod_eq_of_lt i.isLt,Nat.mul_add_mod]

theorem name_raw (k r:Nat) (h:0 < k) (t:Fin 5) (i:Fin k) :
    name k r h (2*(k*t.val+i.val))=Sum.inl (t,i) := by
  simp [name,even_no_id,raw_coord]

theorem base_raw (k:Nat) (h:0 < k) (v:V k → Bool) (t:Fin 5) (i:Fin k):
    base k h v (2*(k*t.val+i.val))=v (t,i) := by simp [base,raw_coord]
theorem base_one (k:Nat) (h:0 < k) (v:V k → Bool):
    base k h v (2*(5*k))=true := by simp [base,rawAt]

end Pcx293.Dense

namespace Pcx293.Dense
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Sim PEqualNP.Outside.L_pcx_293.Pcx293.Unit

def litMap (k r:Nat) (h:0 < k) (x:Lit Nat) := (name k r h x.1,x.2)
def clauses (k r:Nat) (h:0 < k) := (make k r).form.map (List.map (litMap k r h))
def word {k:Nat} (v:V k → Bool) (t:Fin 5) := Word.pack k (fun i=>if lt:i < k then v (t,⟨i,lt⟩) else false)
def valid {k:Nat} (r:Nat) (v:V k → Bool) := word v 3=Tracks.first k r (word v 2) (word v 0) ∧
  word v 4=Tracks.second k r (word v 2) (word v 1)

theorem mapped_width (s:Net) (c:Clause Nat) (mem:c∈s.form) : c.length ≤ 3 := by
  rcases List.mem_append.mp mem with h|h
  · exact s.thin _ h
  · rcases List.mem_flatMap.mp h with ⟨l,hl,found⟩
    rcases List.mem_map.mp found with ⟨d,hd,rfl⟩
    simpa [transClause] using Gate.width_le l.op.g d hd

theorem width (k r:Nat) (h:0 < k) {c} (hc:c∈clauses k r h) : c.length ≤ 3 := by
  rcases List.mem_map.mp hc with ⟨j,hj,rfl⟩
  simpa using mapped_width _ _ hj

theorem map_model (k r:Nat) (h:0 < k) (w:Sum (V k) (Fin (size k r)) → Bool) :
    Sat (fun c=>c∈clauses k r h) w ↔ Sat (fun c=>c∈(make k r).form) (fun j=>w (name k r h j)) := by
  constructor
  · intro ok c mem
    rcases ok _ (List.mem_map.mpr ⟨c,mem,rfl⟩) with ⟨b,hb,sat⟩
    rcases List.mem_map.mp hb with ⟨l,hl,rfl⟩;exact ⟨l,hl,sat⟩
  · intro ok c mem
    rcases List.mem_map.mp mem with ⟨c,hc,rfl⟩
    rcases ok c hc with ⟨l,hl,sat⟩
    exact ⟨_,List.mem_map.mpr ⟨l,hl,rfl⟩,sat⟩

theorem read_word {k r:Nat} (h:0 < k) (v:V k → Bool) (a:Fin (size k r) → Bool) (t:Fin 5) :
    rowWord (fun j=>Sum.elim v a (name k r h j)) k t.val=word v t := by
  apply Sim.canonical (Word.pack_bounded ..) (Word.pack_bounded ..)
  intro i lt
  simp [rowWord,word,Word.pack_bit,lt,name_raw k r h t ⟨i,lt⟩]

theorem valid_iff {k r:Nat} (h:0 < k) (v:V k → Bool) (a:Fin (size k r) → Bool) :
    Sim.agrees (fun j=>Sum.elim v a (name k r h j)) k r ↔ valid r v := by
  unfold Sim.agrees valid
  have eq (t:Fin 5):=read_word (r:=r) h v a t
  rw [←eq 3,←eq 2,←eq 0,←eq 4,←eq 1];rfl

theorem extensions {k r:Nat} (h:k % 6=3) (v:V k → Bool) :
    valid r v ↔ ∃a:Fin (size k r) → Bool, Sat (fun c=>c∈clauses k r (by omega)) (Sum.elim v a) := by
  have hk:0 < k:=by omega
  constructor
  · intro ok
    let a:=aux k r hk v
    let e:=getVal (make k r) (base k hk v)
    have eq : (fun j=>Sum.elim v a (name k r hk j))=e:=funext (canonical k r hk v)
    refine ⟨a,(map_model k r hk _).mpr ?_⟩
    have va := (valid_iff hk v a).mpr ok
    rw [eq] at va ⊢
    exact (full_formula h e).mpr ⟨val_line (make k r) (base k hk v),(val_even _ _ _).trans (base_one ..),va⟩
  · rintro ⟨a,sat⟩
    exact (valid_iff hk v a).mp ((full_formula h _).mp ((map_model k r hk _).mp sat)).2.2

end Pcx293.Dense

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape

def put (w:W) (b:Bool) : W:=if b then w else neg w
@[local simp] theorem put_neg (w:W) (b:Bool) : put (neg w) b=put w (!b) := by cases b <;> simp [put,neg_neg]
theorem aligns (e:Nat → Bool) (w:W) : put w (value e w)=(w.1,e w.1) := by
  rcases w with ⟨j,b⟩;cases h:e j <;> cases b <;> simp [put,neg,value,h]
def Covered (F:Form Nat) (s:Net) := ∀c∈s.form,F c
def Cert (F:Form Nat) (m:B A) (P:A → Prop) := ∀s,Covered F (m.run s).2 → Covered F s ∧ P (m.run s).1
theorem ret (x:A) {P:A → Prop} (p:P x) : Cert F (pure x) P := fun _ h=>⟨h,p⟩
theorem mono {m:B A} {P Q:A → Prop} (a:Cert F m P) (pq:∀ a,P a → Q a) : Cert F m Q := by
  intro s h;rcases a s h with ⟨prev,hs⟩;exact ⟨prev,pq _ hs⟩
theorem bind {m:B A} {f:A → B D} {P:A → Prop} {Q:D → Prop} (p:Cert F m P)
    (q:∀a,Cert F (f a) (fun b=>P a → Q b)) : Cert F (m >>= f) Q := by
  intro s h
  rcases q (m.run s).1 (m.run s).2 h with ⟨mid,qa⟩
  rcases p s mid with ⟨old,r⟩;exact ⟨old,qa r⟩

def inBits (x y:Bool) (p:Lit (Fin 3)) := p=(0,x) ∨ p=(1,y)
theorem exact_gate (op:Op) (x y:Bool) : adv (fun c=>c∈op.g.clauses) (inBits x y) (2,op.eval x y) := by
  cases op <;> cases x <;> cases y <;> first
    | exact fire₁ (by decide) (show inBits _ _ (0,_) from .inl rfl)
    | exact fire₁ (by decide) (show inBits _ _ (1,_) from .inr rfl)
    | exact fire₂ (by decide) (show inBits _ _ (0,_) from .inl rfl) (show inBits _ _ (1,_) from .inr rfl)

def Drives (F:Form Nat) (S:State Nat) (w:W) (t:Nat) (v:Bool) := iter F S t (put w v)

theorem run_line (F:Form Nat) (S:State Nat) (l:Line) (h:∀c∈lineF l,F c)
    (t:Nat) (x y:Bool) (a:Drives F S l.a t x) (b:Drives F S l.b t y) :
    Drives F S (pos l.id) (t+1) (l.op.eval x y) := by
  let m := fun i:Fin 3 => if i=0 then l.a else if i=1 then l.b else pos l.id
  have lift := shift_steps (F:=fun c=>c∈l.op.g.clauses) (G:=F) (T:=S) (S:=inBits x y) m
    (fun c hc=>h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)) t
  have haveIn (p:Lit (Fin 3)) (hp:inBits x y p) : iter F S t (signmap m p) := by
    rcases hp with rfl|rfl
    · simpa [m,signmap,put,Drives] using a
    · simpa [m,signmap,put,Drives] using b
  have endg:=lift haveIn 1 (2,l.op.eval x y) (exact_gate ..)
  simpa [Drives,m,signmap,put] using endg

theorem atom (F:Form Nat) (S:State Nat) (op:Op) (a b:W) :
    Cert F (emit op a b) (fun w=>∀ t x y,Drives F S a t x → Drives F S b t y → Drives F S w (t+1) (op.eval x y)) := by
  intro s covered
  have clause (l:Line) (hl:l∈(inserted s op a b).lines) (c) (hc:c∈lineF l) : F c :=
    covered c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨l,hl,hc⟩))
  refine ⟨?_,run_line F S ⟨nextId s a b,op,a,b⟩ (clause _ (List.mem_cons_self ..))⟩
  intro c hc
  rcases List.mem_append.mp hc with le|ri
  · exact covered c (List.mem_append_left _ le)
  · rcases List.mem_flatMap.mp ri with ⟨l,hl,hc⟩
    exact clause l (List.mem_cons_of_mem _ hl) c hc

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape
structure Env where
  F:Form Nat
  S:State Nat
  e:Nat → Bool

def K (c:Env) (n:Nat) (w:W) := Drives c.F c.S w n (value c.e w)
theorem later (c:Env) {m n:Nat} {w:W} (h:K c m w) (le:m ≤ n) : K c n w := keep h le
theorem flip (c:Env) (n:Nat) (w:W) : K c n (neg w) ↔ K c n w := by
  simp [K,Drives,put_neg,value_neg]

def R (c:Env) (m:B A) (P:A → Prop) :=
  ∀s, Sim.LinesOK c.e (m.run s).2 → Covered c.F (m.run s).2 → 
    Sim.LinesOK c.e s ∧ Covered c.F s ∧ P (m.run s).1
theorem rRet (c:Env) (a:A) {P:A → Prop} (yes:P a) : R c (pure a) P:=fun _ h g=>⟨h,g,yes⟩
theorem rMono {c:Env} {m:B A} {P Q:A → Prop} (p:R c m P) (pq:∀a,P a → Q a) : R c m Q := by
  intro s a b;rcases p s a b with ⟨x,y,h⟩;exact ⟨x,y,pq _ h⟩
theorem rBind {c:Env} {m:B A} {f:A → B D} {P:A → Prop} {Q:D → Prop} (p:R c m P)
    (q:∀a,R c (f a) (fun b=>P a → Q b)) : R c (m >>= f) Q := by
  intro s a b
  rcases q (m.run s).1 (m.run s).2 a b with ⟨la,ca,hg⟩
  rcases p s la ca with ⟨lx,cx,r⟩;exact ⟨lx,cx,hg r⟩

theorem strict (c:Env) (op:Op) (x y:W) : R c (emit op x y)
    (fun z=>∀t,K c t x → K c t y → K c (t+1) z) := by
  intro s eqs cv
  rcases atom c.F c.S op x y s cv with ⟨old,drive⟩
  rcases Sim.em c.e op x y s eqs with ⟨⟨olde,_⟩,eq⟩
  refine ⟨olde,old,?_⟩
  intro t hx hy
  unfold K
  rw [eq]
  exact drive t _ _ hx hy

inductive Matched (P:A → D → Prop) : List A → List D → Prop
| nil : Matched P [] []
| cons : P a b → Matched P xs ys → Matched P (a::xs) (b::ys)

theorem rMap {c:Env} (xs:List A) (m:A → B D) (P:A → D → Prop) (me:∀a∈xs,R c (m a) (P a)):
    R c (xs.mapM m) (fun out=>Matched P xs out) := by
  induction xs with
  | nil=>exact rRet c _ .nil
  | cons x xs ih=>
    rw [List.mapM_cons]
    apply rBind (me x (by simp))
    intro d
    apply rBind (ih (fun a h=>me a (by simp [h])))
    intro ds
    exact rRet c _ (by intro hs hd;exact .cons hd hs)

theorem rAll {c:Env} (xs:List A) (m:A → B D) (P:D → Prop) (me:∀a∈xs,R c (m a) P):
    R c (xs.mapM m) (fun out=>∀z∈out,P z) := by
  apply rMono (rMap xs m (fun _ z=>P z) me)
  intro out h z hz
  clear me
  induction h with
  | nil=>cases hz
  | cons f fs ih=>
    rcases List.mem_cons.mp hz with rfl|q
    · exact f
    · exact ih q

def CacheK {A:Type} (ok:Nat → A → Prop) (n:Nat) : Cached A → Prop
| .leaf a => ok n a
| .node v l r => ok n v ∧ CacheK ok n l ∧ CacheK ok n r

theorem cache_root {A:Type} {ok:Nat → A → Prop} {t:Cached A} (h:CacheK ok n t) : ok n t.prod := by
  cases t with
  | leaf=>exact h
  | node=>exact h.1

theorem cache_later {A:Type} {ok:Nat → A → Prop} (more:∀{m n a},ok m a → m ≤ n → ok n a) {t:Cached A}
    {m n:Nat} (h:CacheK ok m t) (le:m ≤ n) : CacheK ok n t := by
  induction t with
  | leaf=>exact more h le
  | node v l r hl hr=>exact ⟨more h.1 le,hl h.2.1,hr h.2.2⟩

def tips {A:Type} (p:A → Prop) : ScanTree A → Prop
| .tip a=>p a
| .node l r=> tips p l ∧ tips p r

theorem build_time (c:Env) {A:Type} (ok:Nat → A → Prop) (more:∀{m n a},ok m a → m ≤ n → ok n a)
    (op:A → A → B A) (d:Nat) (step:∀x y,R c (op x y) (fun z=>∀t,ok t x → ok t y → ok (t+d) z))
    (t:ScanTree A) (n:Nat) (hs:tips (ok n) t) :
    R c (build op t) (CacheK ok (n+MCost.height t*d)) := by
  induction t with
  | tip x=>exact rRet c _ (by simpa [MCost.height,CacheK,tips] using hs)
  | node l r hl hr=>
    simp only [build]
    apply rBind (hl hs.1);intro a
    apply rBind (hr hs.2);intro b
    apply rBind (step a.prod b.prod);intro z
    apply rRet
    intro sc cb ca
    let m:=n+(max (MCost.height l) (MCost.height r))*d
    have ll:n+MCost.height l*d ≤ m := Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_max_left ..)) n
    have rr:n+MCost.height r*d ≤ m := Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_max_right ..)) n
    have nn : n+MCost.height (.node l r)*d=m+d := by simp [m,MCost.height,Nat.add_mul,Nat.add_assoc]
    rw [nn]
    exact ⟨sc m (more (cache_root ca) ll) (more (cache_root cb) rr),
      cache_later (ok:=ok) more ca (Nat.le_trans ll (Nat.le_add_right ..)),cache_later (ok:=ok) more cb (Nat.le_trans rr (Nat.le_add_right ..))⟩

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit
def ch : Cached A → Nat | .leaf _=>0 | .node _ l r=>max (ch l) (ch r)+1
theorem build_height (op:A → A → B A) (t:ScanTree A) (s:Net): ch ((build op t).run s).1=MCost.height t := by
  induction t generalizing s with
  | tip x=>rfl
  | node l r hl hr=>
    change max (ch ((build op l).run s).1) (ch ((build op r).run ((build op l).run s).2).1)+1=_
    rw [hl,hr];rfl

def All (p:A → Prop) (xs:List A):=∀x∈xs,p x
theorem all_get {p:A → Prop} (xs:List A) (z:A) (hz:p z) (all:All p xs) (j:Nat) : p (xs.getD j z) := by
  by_cases h:j < xs.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,all _ (List.getElem_mem h)]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length ≤ j),hz]
theorem shape_tips (p:A → Prop) (f:Nat → A) (ok:∀i,p (f i)) (s n:Nat) : tips p (shape f s n) := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih=>
    rw [shape];split
    · exact ok _
    · exact ⟨ih _ (by omega) _,ih _ (by omega) _⟩

theorem down_time (c:Env) (ok:Nat → A → Prop) (more:∀{m n a},ok m a → m ≤ n → ok n a)
    (op:A → A → B A) (d:Nat) (step:∀x y,R c (op x y) (fun z=>∀t,ok t x → ok t y → ok (t+d) z))
    (id:A) (rot:Bool) (tree:Cached A) (bef aft:A) :
    R c (down op id rot tree bef aft) (fun out=>∀n, CacheK ok n tree → ok n id → ok n bef → ok n aft → 
      All (ok (n+(ch tree+2)*d)) out) := by
  induction tree generalizing bef aft with
  | leaf x=>
    cases rot with
    | false=>
      apply rRet;intro n _ _ be _ z mz
      obtain rfl: z=bef:=List.mem_singleton.mp mz
      exact more be (Nat.le_add_right ..)
    | true=>
      apply rBind (step aft bef);intro ab
      apply rBind (step x ab);intro xab
      apply rRet;intro sx sab n hx _ hbf haft z mz
      obtain rfl: z=xab:=List.mem_singleton.mp mz
      have q:=sx (n+d) (more hx (Nat.le_add_right ..)) (sab n haft hbf)
      simpa [ch,Nat.two_mul,Nat.add_assoc] using q
  | node v l r il ir=>
    let L:=fun la=>down op id rot l bef la
    let R':=fun rb=>down op id rot r rb aft
    have qla : R c (if rot then op r.prod aft else pure id)
        (fun a=>∀n,CacheK ok n r → ok n id → ok n aft → ok (n+d) a) := by
      cases rot with
      | false=>exact rRet _ _ (fun _ _ h _=>more h (Nat.le_add_right ..))
      | true=>exact rMono (step r.prod aft) (fun a f n kr _ ha=>f n (cache_root kr) ha)
    have de : down op id rot (.node v l r) bef aft =
        ((if rot then op r.prod aft else pure id) >>= fun la=>do
          let rb←op bef l.prod
          let xl←down op id rot l bef la
          let xr←down op id rot r rb aft
          return xl++xr) := by cases rot <;> rfl
    rw [de]
    apply rBind qla;intro la
    apply rBind (step bef l.prod);intro rb
    apply rBind (il bef la);intro xl
    apply rBind (ir rb aft);intro xr
    apply rRet
    intro qr ql qb qa n tree base be af z mem
    let m:=n+d
    have nb : ok m id:=more base (Nat.le_add_right ..)
    have nbe:ok m bef:=more be (Nat.le_add_right ..)
    have naf:ok m aft:=more af (Nat.le_add_right ..)
    have leL: (ch l+2)*d ≤ (max (ch l) (ch r)+2)*d := Nat.mul_le_mul_right d (Nat.add_le_add_right (Nat.le_max_left ..) _)
    have leR: (ch r+2)*d ≤ (max (ch l) (ch r)+2)*d := Nat.mul_le_mul_right d (Nat.add_le_add_right (Nat.le_max_right ..) _)
    have total : n+(ch (.node v l r)+2)*d=m+(max (ch l) (ch r)+2)*d := by
      simp [ch,m,Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    rw [total]
    rcases List.mem_append.mp mem with member|member
    · have h:=ql m (cache_later (ok:=ok) more tree.2.1 (Nat.le_add_right ..)) nb nbe (qa n tree.2.2 base af) z member
      exact more h (Nat.add_le_add_left leL m)
    · have h:=qr m (cache_later (ok:=ok) more tree.2.2 (Nat.le_add_right ..)) nb (qb n be (cache_root tree.2.1)) naf z member
      exact more h (Nat.add_le_add_left leR m)

theorem scan_time (c:Env) (ok:Nat → A → Prop) (more:∀{m n a},ok m a → m ≤ n → ok n a)
    (op:A → A → B A) (d:Nat) (step:∀x y,R c (op x y) (fun z=>∀t,ok t x → ok t y → ok (t+d) z))
    (id:A) (v:List A) (rot:Bool) (n B:Nat) (sz:v.length ≤ 2^B) (iz:ok n id) (vi:All (ok n) v) :
    R c (scan op id v rot) (fun out=>All (ok (n+(2*B+2)*d)) out) := by
  cases v with
  | nil=>exact rRet _ [] (by intro a h;cases h)
  | cons a v=>
    let xs:=a::v
    let t:=shape (fun i=>xs.getD i id) 0 xs.length
    have use:=build_time c ok more op d step t n (shape_tips _ _ (all_get xs id iz vi) ..)
    have height:=MCost.shape_height (fun i=>xs.getD i id) 0 xs.length B sz
    unfold scan;simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    intro s hs cs
    let res:=(build op t).run s
    have downp:=down_time c ok more op d step id rot res.1 id id res.2 hs cs
    obtain ⟨hl,fl,kc⟩:=use s downp.1 downp.2.1
    have he:ch res.1=MCost.height t := build_height op t s
    have base:=more iz (Nat.le_add_right n (MCost.height t*d))
    have known:=downp.2.2 _ kc base base base
    refine ⟨hl,fl,?_⟩
    intro w hw
    have timing:=known w hw
    apply more timing
    rw [he]
    change MCost.height t ≤ B at height
    have h':=Nat.mul_le_mul_right d height
    simp only [Nat.add_mul,Nat.two_mul] at *;omega

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape

theorem timedScan (c:Env) (ok:Nat → A → Prop) (more:∀{m n a},ok m a → m ≤ n → ok n a)
    (op:A → A → B A) (d:Nat) (step:∀x y,R c (op x y) (fun z=>∀t,ok t x → ok t y → ok (t+d) z))
    (id:A) (v:List A) (rot:Bool) :
    R c (scan op id v rot) (fun out=>∀n B,v.length ≤ 2^B → ok n id → All (ok n) v → All (ok (n+(2*B+2)*d)) out) := by
  intro s eqs cv
  have triv:=scan_time c (fun _ _=>True) (by intros;trivial) op d
    (fun x y=>rMono (step x y) (by intros;trivial)) id v rot 0 v.length (Nat.le_of_lt Nat.lt_two_pow_self)
    trivial (by intros x h;trivial) s eqs cv
  exact ⟨triv.1,triv.2.1,fun n B cap iz xs=>(scan_time c ok more op d step id v rot n B cap iz xs s eqs cv).2.2⟩

theorem timedReduce (c:Env) (op:Op) (id:W) (xs:Vec) :
    R c (reduce op id xs) (fun w=>∀n B,xs.length ≤ 2^B → K c n id → All (K c n) xs → K c (n+B) w) := by
  cases xs with
  | nil=>exact rRet c id (fun _ _ _ iz _=>later c iz (Nat.le_add_right ..))
  | cons a xs=>
    let v:=a::xs
    let t:=shape (fun i=>v.getD i id) 0 v.length
    unfold reduce;simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    have dummy:=build_time c (fun _ (_:W)=>True) (by intros;trivial) (emit op) 1
      (fun x y=>rMono (strict c op x y) (by intros;trivial)) t 0 (shape_tips _ _ (by intros;trivial) ..)
    apply rBind (P:=fun a=>∀ n B,v.length ≤ 2^B → K c n id → All (K c n) v → K c (n+B) a.prod) (by
      intro s eqs cv
      rcases dummy s eqs cv with ⟨old,prev,_⟩
      refine ⟨old,prev,?_⟩
      intro n h cap iz vv
      have heights:=MCost.shape_height (fun i=>v.getD i id) 0 v.length h cap
      have got:=build_time c (K c) (later c) (emit op) 1 (strict c op) t n
        (shape_tips _ _ (all_get v id iz vv) ..) s eqs cv
      exact later c (cache_root got.2.2) (by change n+MCost.height t*1 ≤ n+h;change MCost.height t ≤ h at heights;omega))
    intro a;exact rRet _ _ idfun
where idfun {P:Prop} : P → P := fun p=>p

theorem all_later (c:Env) {xs:Vec} {n m:Nat} (h:All (K c n) xs) (le:n ≤ m) :
    All (K c m) xs := fun w hw=>later c (h w hw) le

theorem all_map {A D:Type} {p:D → Prop} {f:A → D} {xs:List A} (g:∀i∈xs,p (f i)) : All p (xs.map f) := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨a,ha,rfl⟩;exact g _ ha

theorem vx_time (c:Env) (k:Nat) (z:W) (x y:Vec):
    R c (vX k z x y) (fun out=>∀n,K c n z → All (K c n) x → All (K c n) y → All (K c (n+1)) out) := by
  apply rMono (rAll (List.range k) (fun i=>emit .bxor (x.getD i z) (y.getD i z))
    (fun w=>∀n,K c n z → All (K c n) x → All (K c n) y → K c (n+1) w) (fun i _=>
      rMono (strict c .bxor _ _) (fun w step n iz xx yy=>step n (all_get x z iz xx i) (all_get y z iz yy i))))
  exact fun ys h n iz xx yy w mem=>h w mem n iz xx yy

theorem mask_time (c:Env) (k r d j:Nat) (z:W) (key:Vec) (n:Nat) (iz:K c n z) (all:All (K c n) key) :
    All (K c n) (mask k r d j z key) := by
  have rot:All (K c n) (rot k z key (if d=1 then 2*j else 3*(j+1)+1)):=all_map (fun i _=>all_get key z iz all _)
  have signed (p:W) (b:Bool) (yes:K c n p) : K c n (if b then neg p else p) := by
    cases b;exact yes;exact (flip c n _).mpr yes
  apply all_map;intro i hi
  exact signed _ _ (all_get _ z iz rot i)

def pairK (c:Env) (n:Nat) (p:A2):= K c n p.1 ∧ K c n p.2
def compose (p q:A2) : B A2 := do
    let b←emit .bxor p.1 (←emit .band p.2 q.1)
    return (b,←emit .band p.2 q.2)

theorem comp_time (c:Env) (p q:A2) : R c (compose p q)
    (fun out=>∀n,pairK c n p → pairK c n q → pairK c (n+2) out) := by
  apply rBind (strict c .band p.2 q.1);intro a
  apply rBind (strict c .bxor p.1 a);intro b
  apply rBind (strict c .band p.2 q.2);intro d
  apply rRet;intro sd sb sa n pp qq
  exact ⟨sb (n+1) (later c pp.1 (by omega)) (sa n pp.2 qq.1),later c (sd n pp.2 qq.2) (by omega)⟩

theorem inv_time (c:Env) (k:Nat) (o z:W) (y:Vec) : R c (inverseChi k o z y)
    (fun out=>∀n H,k ≤ 2^H → K c n o → K c n z → All (K c n) y → All (K c (n+4*H+4)) out) := by
  let v : List A2 := (List.range k).map fun t=>(y.getD ((2*t) % k) z,neg (y.getD ((2*t+1) % k) z))
  have next:=timedScan c (pairK c) (fun h le=>⟨later c h.1 le,later c h.2 le⟩) compose 2
    (comp_time c) (z,o) v true
  apply rBind next;intro vs
  apply rRet;intro done n H cap one zero all
  have input:All (pairK c n) v := all_map (fun _ _=>⟨all_get _ z zero all _,(flip c n _).mpr (all_get _ z zero all _)⟩)
  have got:=done n H (by simpa [v] using cap) ⟨zero,one⟩ input
  apply all_map;intro i _
  have vv:=all_get vs (z,o) (show pairK c (n+(2*H+2)*2) (z,o) from
      ⟨later c zero (Nat.le_add_right ..),later c one (Nat.le_add_right ..)⟩) got (if i % 2=0 then i/2 else (i+k)/2)
  exact later c vv.1 (by omega)

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape

theorem Matched.sz {P:A → D → Prop} {xs:List A} {ys:List D} (h:Matched P xs ys) : ys.length=xs.length := by
  induction h with
  | nil=>rfl
  | cons _ _ ih=>simp [ih]
theorem Matched.result {P:D → Prop} {xs:List A} {ys:List D} (h:Matched (fun _ z=>P z) xs ys) : All P ys := by
  intro a ha
  induction h with
  | nil=>cases ha
  | cons x _ ih=>rcases List.mem_cons.mp ha with rfl|q;exact x;exact ih q
theorem rAllLen {c:Env} (xs:List A) (m:A → B D) (P:D → Prop) (me:∀a∈xs,R c (m a) P):
    R c (xs.mapM m) (fun out=>out.length=xs.length ∧ All P out) :=
  rMono (rMap xs m (fun _ z=>P z) me) (fun _ h=>⟨h.sz,h.result⟩)

def vv (c:Env) (n:Nat) (xs:Vec) := All (K c n) xs
def entryK (c:Env) (n:Nat) (p:Make.Entry):=vv c n p.1 ∧ K c n p.2
theorem rot_time (c:Env) (n k shift:Nat) (z:W) (xs:Vec) (zz:K c n z) (hx:vv c n xs) :
    vv c n (rot k z xs shift) := all_map (fun i _=>all_get xs z zz hx _)

theorem coord_time (c:Env) (k:Nat) (z:W) (u:Nat → W) (q:Nat) :
    R c (coordSide k z u q) (fun out=>∀n H,k ≤ 2^H → K c n z → (∀i,K c n (u i)) → vv c (n+2*H+4) out) := by
  apply rBind (rAllLen (indices k q) (fun t=>emit .bxor (u t) (u (t+1)))
    (fun w=>∀n,(∀i,K c n (u i)) → K c (n+1) w) (fun t _=>rMono (strict c .bxor _ _)
      (fun w f n h=>f n (h t) (h (t+1)))));intro diff
  apply rBind (timedScan c (K c) (later c) (emit .bxor) 1 (strict c .bxor) z diff false);intro pre
  apply rMono (rAll pre (fun e=>emit .bxor (if q=2 then u 0 else z) e)
    (fun w=>∀n,K c n (if q=2 then u 0 else z) → vv c n pre → K c (n+1) w)
    (fun a h=>rMono (strict c .bxor _ _) (fun w f n got p=>f n got (p _ h))))
  intro out fm scan dif n H cap zz u' w hw
  have cap':diff.length ≤ 2^H:=by rw [dif.1];simp [indices];omega
  have ts:=scan (n+1) H cap' (later c zz (by omega)) (fun x hx=>dif.2 x hx n u')
  have ba:K c n (if q=2 then u 0 else z):=by split;exact u' _;exact zz
  have run:=fm w hw (n+1+(2*H+2)*1) (later c ba (by omega)) ts
  exact later c run (by omega)

theorem check_time (c:Env) (k d:Nat) (o z:W) (w y:Vec):
    R c (check k d o z w y) (fun b=>∀n H,k ≤ 2^H → K c n z → vv c n w → vv c n y → K c (n+H+5) b) := by
  apply rBind (vx_time c k z w (rot k z w d));intro xa
  apply rBind (vx_time c k z xa (rot k z w (k-d)));intro us
  let read := fun i=>us.getD i z
  let prog:=fun i=>do
    let v←emit .band (neg (read ((i+1) % k))) (read ((i+2) % k))
    let bit←emit .bxor (read i) v
    emit .bxor bit (y.getD i z)
  have piece (i:Nat) : R c (prog i) (fun b=>∀n,K c n z → vv c n us → vv c n y → K c (n+3) b) := by
    apply rBind (strict c .band _ _);intro a
    apply rBind (strict c .bxor _ _);intro bit
    apply rMono (strict c .bxor _ _)
    intro w endEq bitEq bEq n zz uss yy
    have ready (j:Nat):K c n (read j):=all_get _ z zz uss j
    have a':=bEq n ((flip c n _).mpr (ready _)) (ready _)
    have b':=bitEq (n+1) (later c (ready _) (by omega)) a'
    exact endEq (n+2) b' (later c (all_get y z zz yy i) (by omega))
  apply rBind (rAllLen (List.range k) prog _ (fun i _=>piece i));intro bad
  apply rMono (timedReduce c .bor z bad)
  intro out rd mixed two first n H cap zz ww yy
  have t1:=first n zz ww (rot_time c n k d z w zz ww)
  have t2:=two (n+1) (later c zz (by omega)) t1 (all_later c (rot_time c n k _ z w zz ww) (by omega))
  have members:vv c (n+5) bad:=fun i hi=>mixed.2 i hi (n+2) (later c zz (by omega)) t2 (all_later c yy (by omega))
  exact later c (rd (n+5) H (by simpa [mixed.1] using cap) (later c zz (by omega)) members) (by omega)

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape

theorem child_time (c:Env) (k d:Nat) (o z dead:W) (y:Vec) (sides:List Vec) (sg:Bool×Bool) :
    R c (child k d o z dead y sides sg) (fun out=>∀n H,k ≤ 2^H → K c n z → K c n dead → vv c n y → All (vv c n) sides → entryK c (n+H+6) out) := by
  let w:Vec := (List.range k).map fun i=>
    let t := if d=1 then i else if i % 2=0 then i/2 else (i+k)/2
    let s := (sides.getD (t % 3) []).getD (t/3) z
    if (if t % 3=0 then sg.1 else if t % 3=1 then sg.2 else xor sg.1 sg.2) then neg s else s
  apply rBind (check_time c k d o z w y);intro bad
  apply rBind (strict c .bor dead bad);intro inv
  apply rRet;intro ore ck n H max zero de yy ss
  have signed (a:W) (b:Bool) (ok:K c n a):K c n (if b then neg a else a):=by
    cases b;exact ok;exact (flip c n _).mpr ok
  have rs (t:Nat): K c n ((sides.getD (t % 3) []).getD (t/3) z) := all_get _ z zero
    (all_get _ [] (by intro a mem;cases mem) ss (t % 3)) (t/3)
  have wk:vv c n w := all_map fun _ _=>signed _ _ (rs _)
  exact ⟨all_later c wk (by omega),ore (n+H+5) (later c de (by omega)) (ck n H max zero wk yy)⟩

def delay (H:Nat) := 7*H+15
theorem expand_time (c:Env) (k d:Nat) (o z:W) (p:Make.Entry) (m:Vec) :
    R c (expand k d o z p m) (fun out=>∀n H,k ≤ 2^H → K c n o → K c n z → entryK c n p → vv c n m → All (entryK c (n+delay H)) out) := by
  apply rBind (vx_time c k z p.1 m);intro y
  apply rBind (inv_time c k o z y);intro iv
  let u:=fun t=>iv.getD ((d*(t+1)) % k) z
  apply rBind (rAll (List.range 3) (coordSide k z u)
    (fun s=>∀n H,k ≤ 2^H → K c n z → (∀i,K c n (u i)) → vv c (n+2*H+4) s) (fun q _=>coord_time c k z u q));intro sides
  apply rMono (rAll signs (child k d o z p.2 y sides)
    (fun out=>∀n H,k ≤ 2^H → K c n z → K c n p.2 → vv c n y → All (vv c n) sides → entryK c (n+H+6) out)
    (fun sg _=>child_time c k d o z p.2 y sides sg))
  intro xs children coords inverse ystep n H cap one zero node maskK
  have yy:=ystep n zero node.1 maskK
  have ii:=inverse (n+1) H cap (later c one (by omega)) (later c zero (by omega)) yy
  let middle:=n+1+4*H+4
  have mi: K c middle z :=later c zero (by dsimp [middle];omega)
  have ts : ∀i,K c middle (u i):=fun i=>all_get _ z mi ii _
  let finish:=middle+2*H+4
  have fin:All (vv c finish) sides:=fun s hs=>coords s hs middle H cap mi ts
  intro x hx
  have endx:=children x hx finish H cap (later c zero (by dsimp [finish,middle];omega))
    (later c node.2 (by dsimp [finish,middle];omega))
    (all_later c yy (by dsimp [finish,middle];omega)) fin
  have e:finish+H+6=n+delay H:=by dsimp [finish,middle,delay];omega
  exact e ▸ endx

theorem layer_time (c:Env) (k r d:Nat) (o z:W) (key:Vec) (js:List Nat) (nodes:List Make.Entry):
    R c (genLayers k r d o z key js nodes)
    (fun out=>∀n H,k ≤ 2^H → K c n o → K c n z → vv c n key → All (entryK c n) nodes → 
      All (entryK c (n+js.length*delay H)) out) := by
  induction js generalizing nodes with
  | nil=>exact rRet c _ (fun n H _ _ _ _ fn=>by simpa using fn)
  | cons j js ih=>
    let mk:=mask k r d j z key
    apply rBind (rAll nodes (fun p=>expand k d o z p mk)
      (fun out=>∀n H,k ≤ 2^H → K c n o → K c n z → vv c n key → All (entryK c n) nodes → All (entryK c (n+delay H)) out)
      (fun p hp=>rMono (expand_time c k d o z p mk) (fun out rs n H cap one zero keys es=>
        rs n H cap one zero (es p hp) (mask_time c k r d j z key n zero keys))));intro kids
    apply rMono (ih kids.flatten)
    intro out rest ch n H cap one zero keys ns
    have level : All (entryK c (n+delay H)) kids.flatten := by
      intro a ha
      rcases List.mem_flatten.mp ha with ⟨sub,hs,inc⟩
      exact ch sub hs n H cap one zero keys ns a inc
    have done:=rest (n+delay H) H cap (later c one (Nat.le_add_right ..)) (later c zero (Nat.le_add_right ..))
      (all_later c keys (Nat.le_add_right ..)) level
    simpa [Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using done

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape
def yes (c:Env) (n:Nat) (w:W):=iter c.F c.S n w
def join (both:Bool) (P Q:Prop) : Prop:=if both then P ∧ Q else P ∨ Q
def jop (both:Bool) : Op:=if both then .band else .bor
def seeds (left right:Prop) (p:Lit (Fin 3)) : Prop := (p=(0,true) ∧ left) ∨ (p=(1,true) ∧ right)
theorem short_local (both:Bool) (p q:Prop) (h:join both p q) :
    adv (fun c=>c∈(jop both).g.clauses) (seeds p q) (2,true) := by
  cases both with
  | false=>
    rcases (show p∨q from h) with a|b
    · exact fire₁ (by decide) (show seeds p q (0,true) from .inl ⟨rfl,a⟩)
    · exact fire₁ (by decide) (show seeds p q (1,true) from .inr ⟨rfl,b⟩)
  | true=>
    exact fire₂ (by decide) (show seeds p q (0,true) from .inl ⟨rfl,h.1⟩) (show seeds p q (1,true) from .inr ⟨rfl,h.2⟩)

theorem short (c:Env) (both:Bool) (x y:W) : R c (emit (jop both) x y)
    (fun z=>∀t, join both (yes c t x) (yes c t y) → yes c (t+1) z) := by
  intro s eqs cv
  rcases strict c (jop both) x y s eqs cv with ⟨l,old,_⟩
  refine ⟨l,old,?_⟩
  intro t proof
  let m:=fun i:Fin 3=>if i=0 then x else if i=1 then y else pos (nextId s x y)
  let g:=(jop both).g
  have inc (cl) (hc:cl∈g.clauses) : c.F (transClause m cl):=
    cv _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨⟨nextId s x y,jop both,x,y⟩,List.mem_cons_self ..,List.mem_map.mpr ⟨cl,hc,rfl⟩⟩))
  have hv (p) (hs:seeds (yes c t x) (yes c t y) p) : iter c.F c.S t (signmap m p) := by
    rcases hs with ⟨rfl,a⟩|⟨rfl,b⟩
    · simpa [signmap,m,yes] using a
    · simpa [signmap,m,yes] using b
  have hit:=shift_steps m inc t hv 1 (2,true) (short_local both _ _ proof)
  change iter c.F c.S (t+1) (pos (nextId s x y))
  simpa [m,signmap] using hit

def hot (both:Bool) (P:A → Prop) : ScanTree A → Prop
| .tip a=>P a
| .node l r=>join both (hot both P l) (hot both P r)

theorem tree_hot (c:Env) (both:Bool) (t:ScanTree W) : R c (build (emit (jop both)) t)
    (fun q=>∀n,hot both (yes c n) t → yes c (n+MCost.height t) q.prod) := by
  induction t with
  | tip x=>exact rRet c _ (fun _ h=>h)
  | node l r hl hr=>
    apply rBind hl;intro a
    apply rBind hr;intro b
    apply rBind (short c both a.prod b.prod);intro w
    apply rRet
    intro s rb la n cond
    let m:=n+max (MCost.height l) (MCost.height r)
    have leL:n+MCost.height l ≤ m:=Nat.add_le_add_left (Nat.le_max_left ..) _
    have leR:n+MCost.height r ≤ m:=Nat.add_le_add_left (Nat.le_max_right ..) _
    change yes c (m+1) w
    apply s m
    cases both with
    | false=>
      rcases (show _ ∨ _ from cond) with a|b
      · exact .inl (keep (la n a) leL)
      · exact .inr (keep (rb n b) leR)
    | true=>exact ⟨keep (la n cond.1) leL,keep (rb n cond.2) leR⟩

def listHot (both:Bool) (p:A → Prop) (xs:List A):=if both then All p xs else ∃a∈xs,p a
theorem hot_target (both:Bool) (p:A → Prop) (t:ScanTree A) :
    hot both p t ↔ listHot both p (Sim.target id t).vals := by
  induction t with
  | tip x=>cases both <;> simp [hot,listHot,Sim.target,AllRotation.T.vals,All]
  | node l r ih jh=>
    change join both (hot both p l) (hot both p r) ↔ _
    rw [ih,jh]
    cases both <;> simp [join,listHot,Sim.target,AllRotation.T.vals,All,List.mem_append] <;> grind

theorem hot_reduce (c:Env) (both:Bool) (o:W) (xs:Vec) : R c (reduce (jop both) o xs)
    (fun w=>∀n H,xs≠[] → xs.length ≤ 2^H → listHot both (yes c n) xs → yes c (n+H) w) := by
  cases xs with
  | nil=>exact rRet _ _ (fun _ _ no=>False.elim (no rfl))
  | cons a xs=>
    let v:=a::xs
    let t:=shape (fun i=>v.getD i o) 0 v.length
    unfold reduce;simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    apply rBind (tree_hot c both t);intro ca
    apply rRet
    intro got n H ne cap h
    have eq:(Sim.target id t).vals=v := by simpa [t] using Sim.target_input id v o ne
    have ok:=got n ((hot_target both (yes c n) t).mpr (eq.symm ▸ h))
    exact keep ok (Nat.add_le_add_left (MCost.shape_height _ _ _ H cap) n)

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape
theorem Matched.get {P:A → D → Prop} {xs:List A} {ys:List D} (h:Matched P xs ys)
    (i:Nat) (hi:i < xs.length) (a:A) (d:D) : P (xs.getD i a) (ys.getD i d) := by
  induction h generalizing i with
  | nil=>simp at hi
  | cons ok _ ih=>
    cases i with
    | zero=>exact ok
    | succ i=>exact ih i (by simp at hi;exact hi)

theorem joinGood {c:Env} {m:B A} {P Q:A → Prop} (work:R c m P) (sem:Sim.Good c.e m Q) :
    R c m (fun a=>P a ∧ Q a) := by
  intro s ls cv
  rcases work s ls cv with ⟨a,b,v⟩;exact ⟨a,b,v,(sem s ls).2⟩

theorem direct_atom (c:Env) (op:Op) (a b:W) :
    R c (emit op a b) (fun w=>∀n x y,Drives c.F c.S a n x → Drives c.F c.S b n y → Drives c.F c.S w (n+1) (op.eval x y)) := by
  intro s ls cv
  exact ⟨(Sim.em c.e op a b s ls).1.1,atom c.F c.S op a b s cv⟩

theorem cmp_time (c:Env) (k:Nat) (z:W) (nm pred:Vec):
    R c (vX k z nm pred) (fun mm=>mm.length=k ∧ ∀i < k,∀n b,Drives c.F c.S (nm.getD i z) n b → 
      Drives c.F c.S (pred.getD i z) n (!b) → yes c (n+1) (mm.getD i z)) := by
  let P:=fun i (w:W)=>∀ n b,Drives c.F c.S (nm.getD i z) n b → Drives c.F c.S (pred.getD i z) n (!b) → 
      yes c (n+1) w
  apply rMono (rMap (List.range k) (fun i=>emit .bxor (nm.getD i z) (pred.getD i z)) P (fun i _=>
    rMono (direct_atom c .bxor _ _) (fun w f n b l r=>by
      have q:=f n b (!b) l r
      cases b <;> exact q)))
  intro mm hs
  refine ⟨by simpa using hs.sz,?_⟩
  intro i hi
  have q:=hs.get i (by simpa using hi) 0 z
  have eq:(List.range k).getD i 0=i := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show i < (List.range k).length by simpa using hi)]
  simpa only [eq,P] using q

def miss (c:Env) (n k:Nat) (z:W) (nm:Vec) (v:Nat) :=
  ∃i < k,∃ b,Drives c.F c.S (nm.getD i z) n b ∧ v.testBit i= !b

theorem filtered_time (c:Env) (k:Nat) (z:W) (ini nm:Vec) (p:Make.Entry) :
    R c (filterName k z ini nm p) (fun out=>
      Sim.toWord c.e k z out.1=Sim.toWord c.e k z ini ^^^ Sim.toWord c.e k z p.1 ∧
      ∀n H,k ≤ 2^H → K c n z → vv c n ini → entryK c n p → 
        vv c (n+1) out.1 ∧
        ((value c.e p.2=true ∨ miss c n k z nm (Sim.toWord c.e k z out.1)) → yes c (n+H+3) out.2)) := by
  apply rBind (joinGood (vx_time c k z p.1 ini) (Sim.vx_value c.e k z p.1 ini));intro pred
  apply rBind (cmp_time c k z nm pred);intro mm
  apply rBind (hot_reduce c false z (p.2::mm));intro flag
  apply rRet
  rintro red cmp ⟨vp,wordEq⟩
  refine ⟨wordEq.trans (Nat.xor_comm ..),?_⟩
  intro n H cap zero iniK node
  have pk:=vp n zero node.1 iniK
  refine ⟨pk,?_⟩
  intro why
  apply keep (red (n+2) (H+1) (by simp) (by rw [List.length_cons,cmp.1,Nat.pow_succ];have := Nat.two_pow_pos H;omega) ?_) (by omega)
  change ∃v∈p.2::mm,yes c (n+2) v
  rcases why with inv|⟨i,hi,b,hnm,hbit⟩
  · have actual:=node.2
    unfold K at actual;rw [inv] at actual
    exact ⟨_,List.mem_cons_self ..,keep actual (by omega)⟩
  · have beq : value c.e (pred.getD i z)= !b := (Sim.read_here c.e k z pred hi).symm.trans hbit
    have wire:=all_get pred z (later c zero (Nat.le_add_right n 1)) pk i
    unfold K at wire;rw [beq] at wire
    have mmK:=cmp.2 i hi (n+1) b (keep hnm (by omega)) wire
    have lim : i < mm.length:=by rwa [cmp.1]
    have element : mm.getD i z∈mm:=by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lim]
    exact ⟨_,List.mem_cons_of_mem _ element,mmK⟩

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Tape
def conflict (c:Env) (n:Nat) := ∃cl,c.F cl ∧ ∀l∈cl,iter c.F c.S n (neg l)
def unsupported (c:Env) (n:Nat) (z:W) (labels:List Make.Entry) (i:Nat) (sign:Bool) :=
  ∀p∈labels, yes c n p.2 ∨ Drives c.F c.S (p.1.getD i z) n (!sign)

theorem add_rule (c:Env) (cl:Clause Nat) : R c (add cl) (fun _=>c.F (cl.take 3)) := by
  intro s hl h
  refine ⟨hl,?_,h _ (List.mem_append_left _ (List.mem_cons_self ..))⟩
  intro a ha
  rcases List.mem_append.mp ha with left|right
  · exact h a (List.mem_append_left _ (List.mem_cons_of_mem _ left))
  · exact h a (List.mem_append_right _ right)

theorem bool_claim (c:Env) (n:Nat) (none b:W) (cl:c.F [neg none,b]) (on:yes c n none) :
    yes c (n+1) b := by
  apply Or.inr
  refine ⟨_,cl,by simp,?_⟩
  intro x hx ne;rcases List.mem_cons.mp hx with rfl | mem
  · simpa [yes,neg_neg] using on
  · exact False.elim (ne (List.mem_singleton.mp mem))

theorem block_time (c:Env) (k:Nat) (o z:W) (nm:Vec) (labs:List Make.Entry) (i:Nat) (b:Bool) :
    R c (block k o z nm labs i b) (fun _=>∀n H,labs≠[] → labs.length ≤ 2^H → unsupported c n z labs i b → 
      Drives c.F c.S (nm.getD i z) (n+H+2) (!b)) := by
  let l:=fun p:Make.Entry=>if b then neg (p.1.getD i z) else p.1.getD i z
  let mm:=fun p:Make.Entry=>emit .bor p.2 (l p)
  have fl:=rAllLen labs mm (fun f=>∀n,unsupported c n z labs i b → yes c (n+1) f)
    (fun p hp=>rMono (short c false p.2 (l p)) (fun f rs n us=>rs n (by
      rcases us p hp with d|no
      · exact .inl d
      · exact .inr (by cases b <;> exact no))))
  apply rBind fl;intro flags
  apply rBind (hot_reduce c true o flags);intro out
  apply rMono (add_rule c [neg out,if b then neg (nm.getD i z) else nm.getD i z])
  intro _ cl red flagsOk n H ne cap all
  have pos:flags≠[]:=by intro emp;rw [emp] at flagsOk;have eq:=flagsOk.1;have eq':labs.length=0:=eq.symm;exact ne (List.length_eq_zero_iff.mp eq')
  have hi:=red (n+1) H pos (flagsOk.1 ▸ cap) (fun f hf=>flagsOk.2 f hf n all)
  have got:=bool_claim c _ out _ cl hi
  cases b <;> exact keep got (by omega)

theorem global_time (c:Env) (o:W) (labs:List Make.Entry) : R c
    (do let g←reduce .band o (labs.map Prod.snd);add [neg g])
    (fun _=>∀n H,labs≠[] → labs.length ≤ 2^H → (∀p∈labs,yes c n p.2) → conflict c (n+H)) := by
  apply rBind (hot_reduce c true o (labs.map Prod.snd));intro g
  apply rMono (add_rule c [neg g])
  intro _ cl red n H ne cap rej
  have pos : labs.map Prod.snd≠[]:=by cases labs <;> simp_all
  have fi:=red n H pos (by simpa using cap) (all_map rej)
  exact ⟨[neg g],cl,fun l mem=>by obtain rfl:=List.mem_singleton.mp mem;simpa [yes,neg_neg] using fi⟩

theorem rImp {c:Env} {m:B A} {P Q:A → Prop} (p:R c m P) (q:R c m Q) :
    R c m (fun a=>P a ∧ Q a) := by
  intro s hs cs;have a:=p s hs cs;exact ⟨a.1,a.2.1,a.2.2,(q s hs cs).2.2⟩

theorem pair_seq {c:Env} {m:B A} {f:A → B D} {P Q:Prop} (p:R c m (fun _=>P)) (q:∀a,R c (f a) (fun _=>Q)) :
    R c (m >>= f) (fun _=>P∧Q) := rBind p (fun a=>rMono (q a) (fun _ b p=>⟨p,b⟩))

theorem rCollect {c:Env} (xs:List A) (f:A → B D) (P:A → Prop) (step:∀a,R c (f a) (fun _=>P a)):
    R c (xs.mapM f) (fun _=>∀a∈xs,P a) := by
  induction xs with
  | nil=>exact rRet c _ (by simp)
  | cons x xs ih=>
    rw [List.mapM_cons]
    apply rBind (step x);intro z
    apply rBind ih;intro vs
    exact rRet c _ (by intro tail head a hb;rcases List.mem_cons.mp hb with rfl|m;exact head;exact tail a m)

def outcome (c:Env) (k:Nat) (z:W) (nm:Vec) (labels:List Make.Entry) :=
  ∀n H,labels≠[] → labels.length ≤ 2^H → 
  ((∀p∈labels,yes c n p.2) → conflict c (n+H)) ∧
  (∀i < k,∀b,unsupported c n z labels i b → Drives c.F c.S (nm.getD i z) (n+H+2) (!b))

theorem checks_time (c:Env) (k:Nat) (o z:W) (nm:Vec) (labs:List Make.Entry):
    R c (Sim.checks k o z nm labs) (fun _=>outcome c k z nm labs) := by
  have sides (i:Nat):=pair_seq (block_time c k o z nm labs i false) (fun _=>block_time c k o z nm labs i true)
  have sequence:=pair_seq (global_time c o labs) (fun _=>pair_seq (rCollect (List.range k) _ _ sides)
    (fun _=>rRet c () (P:=fun _=>True) trivial))
  apply rMono sequence
  rintro _ ⟨glob,ck,_⟩ n H ne cap
  refine ⟨glob _ _ ne cap,?_⟩
  intro i hi b h
  have q:=ck i (List.mem_range.mpr hi)
  cases b
  · exact q.1 _ _ ne cap h
  · exact q.2 _ _ ne cap h

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Sim

def validWord (e:Nat → Bool) (k r d:Nat) (z:W) (w:Nat) :=
  let key:=toWord e k z (raw k 2)
  let y:=toWord e k z (raw k (d+2))
  w < 2^k ∧ (if d=1 then Tracks.first k r key w else Tracks.second k r key w)=y

def ini (k d:Nat) (z:W):=Make.rot k z (raw k 2) (if d=1 then 1 else 3)
def rawNodes (e:Nat → Bool) (k r d:Nat) (z:W) :=
  Family.all k d (preMasks k r d (toWord e k z (raw k 2))) (toWord e k z (raw k (d+2)),true)

theorem node_sound {k d:Nat} (h:k % 6=3) (hd:d=1∨d=2) (e:Nat → Bool) (r:Nat) (z:W)
    (p:Make.Entry) (inc:decodeEntry e k z p∈rawNodes e k r d z) (alive:value e p.2=false):
    validWord e k r d z (toWord e k z (ini k d z) ^^^ toWord e k z p.1) := by
  let key:=toWord e k z (raw k 2)
  let ms:=preMasks k r d key
  let y:=toWord e k z (raw k (d+2))
  have base:(toWord e k z p.1,true)∈Family.all k d ms (y,true):=by simpa [decodeEntry,alive,rawNodes,ms,key,y] using inc
  have bound:∀m∈ms,m < 2^k := by
    intro m hm;rcases List.mem_map.mp hm with ⟨i,hi,rfl⟩
    by_cases x:d=1
    · rw [M,if_pos x];exact Nat.xor_lt_two_pow (Tracks.rot_bounded ..) (Tracks.const_bounded ..)
    · rw [M,if_neg x];exact Nat.xor_lt_two_pow (Tracks.rot_bounded ..) (Tracks.const_bounded ..)
  obtain ⟨_,_,finished⟩:=
    (Family.all_valid (k:=k) (d:=d) (ok:=true) (by omega) hd (by omega) ms bound (bounded e k z _) _).mp base
  refine ⟨Nat.xor_lt_two_pow (bounded ..) (bounded ..),?_⟩
  unfold ini
  rw [rot_value]
  rcases hd with rfl|rfl
  · have me : M k r 1 key=Tracks.rowMask k key := by rfl
    simpa [Tracks.first_eq,me,preMasks,ms,key,y,M,←Nat.xor_assoc] using finished
  · have me : M k r 2 key=Tracks.colMask k r key := by rfl
    simpa [Tracks.second_eq,me,preMasks,ms,key,y,M,←Nat.xor_assoc] using finished

theorem Matched.pre {A B:Type} {P:A → B → Prop} {xs:List A} {ys:List B} (h:Matched P xs ys) :
    ∀y∈ys,∃x∈xs,P x y := by
  induction h with
  | nil=>simp
  | cons ok t ih=>
    intro y hy
    rcases List.mem_cons.mp hy with rfl|m
    · exact ⟨_,List.mem_cons_self ..,ok⟩
    · rcases ih _ m with ⟨x,mx,xp⟩;exact ⟨x,List.mem_cons_of_mem _ mx,xp⟩

theorem nodes_length (e:Nat → Bool) (k r d:Nat) (z:W) :
    (rawNodes e k r d z).length=4^r := by simp [rawNodes,Family.all_length,preMasks]

def fits (k:Nat) (hyp:Nat → Bool → Prop) (w:Nat):=∀i < k,∀b,hyp i b → w.testBit i=b
def laneTime (n H r:Nat):=n+r*delay H+H+3+2*r+2
def laneClaim (c:Env) (k r d:Nat) (o z:W):=
  let nm:=raw k (d-1)
  ∀n H,k ≤ 2^H → K c n o → K c n z → vv c n (raw k 2) → vv c n (raw k (d+2)) → 
  ∀hyp:Nat → Bool → Prop,(∀i < k,∀b,hyp i b → Drives c.F c.S (nm.getD i z) n b) → 
    ((¬ ∃w,validWord c.e k r d z w ∧ fits k hyp w) → conflict c (laneTime n H r)) ∧
    (∀i < k,∀b,(∀w,validWord c.e k r d z w → fits k hyp w → w.testBit i≠b) → 
      Drives c.F c.S (nm.getD i z) (laneTime n H r) (!b))

end Pcx293.Flow

namespace Pcx293.Flow
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Wire PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Sim

theorem track_time (c:Env) {k d:Nat} (h:k % 6=3) (hd:d=1∨d=2) (r:Nat) (o z:W)
    (zo:value c.e z=false) (oo:value c.e o=true) : R c (track k r d o z) (fun _=>laneClaim c k r d o z) := by
  let key:=raw k 2;let y:=raw k (d+2);let nm:=raw k (d-1);let iniW:=ini k d z
  let js:=(List.range r).reverse
  let st : List Make.Entry:=[(y,z)]
  have layer:=joinGood (layer_time c k r d o z key js st) (layers_value (d:=d) h c.e r o z zo oo key js st)
  apply rBind layer;intro ns
  have tm:=rMap (c:=c) ns (filterName k z iniW nm) _ (fun p _=>filtered_time c k z iniW nm p)
  apply rBind tm;intro labs
  apply rMono (checks_time c k o z nm labs)
  rintro _ selector lab ⟨nt,sem⟩ n H cap ooK zzK kk yy hyp sent
  have eqN:ns.map (decodeEntry c.e k z)=rawNodes c.e k r d z := by
    simpa [rawNodes,preMasks,st,y,js,key,decodeEntry,zo] using sem
  have len:labs.length=4^r := by
    rw [lab.sz,←nodes_length c.e k r d z,←eqN,List.length_map]
  have ne:labs≠[]:=by
    intro emp
    have pp : 0 < 4^r:=Nat.pow_pos (by decide)
    exact (Nat.ne_of_gt pp) (len.symm.trans (by rw [emp];rfl))
  have capL:labs.length ≤ 2^(2*r):=by rw [len,Nat.pow_mul] <;> exact Nat.le_refl _
  let mid:=n+r*delay H
  let budget:=mid+H+3
  have nk:All (entryK c mid) ns := by
    have got:=nt n H cap ooK zzK kk (by
      intro p mem
      obtain rfl : p=(y,z):=List.mem_singleton.mp mem
      exact ⟨yy,zzK⟩)
    simpa [mid,js] using got
  have zzM: K c mid z:=later c zzK (Nat.le_add_right ..)
  have ik:vv c mid iniW:=all_later c (rot_time c n k _ z key zzK kk) (Nat.le_add_right ..)
  have facts (p:Make.Entry) (hp:p∈labs) :
      vv c (mid+1) p.1 ∧ (yes c budget p.2 ∨
        validWord c.e k r d z (toWord c.e k z p.1) ∧ fits k hyp (toWord c.e k z p.1)) := by
    obtain ⟨src,mem,prop⟩:=lab.pre p hp
    obtain ⟨wordEq,tm⟩:=prop
    obtain ⟨bitsK,kill⟩:=tm mid H cap zzM ik (nk src mem)
    refine ⟨bitsK,?_⟩
    by_cases vs:value c.e src.2=true
    · exact .inl (kill (.inl vs))
    have live : value c.e src.2=false := by cases v:value c.e src.2 <;> simp_all
    have inc : decodeEntry c.e k z src∈rawNodes c.e k r d z := by
      rw [←eqN];exact List.mem_map.mpr ⟨src,mem,rfl⟩
    have valid:=node_sound h hd c.e r z src inc live
    rw [←wordEq] at valid
    by_cases f:fits k hyp (toWord c.e k z p.1)
    · exact .inr ⟨valid,f⟩
    · apply Or.inl;apply kill;apply Or.inr
      apply Classical.byContradiction;intro no;apply f
      intro i hi b pres
      cases ba:(toWord c.e k z p.1).testBit i <;> cases b <;> try rfl
      all_goals exact False.elim (no ⟨i,hi,_,keep (sent i hi _ pres) (Nat.le_add_right ..),by simp [ba]⟩)
  have report:=selector budget (2*r) ne capL
  refine ⟨?_,?_⟩
  · intro impossible
    obtain ⟨cl,inc,full⟩:=report.1 (fun p hp=>((facts p hp).2).elim id (fun ok=>False.elim (impossible ⟨_,ok⟩)))
    exact ⟨cl,inc,fun w hw=>keep (full w hw) (by dsimp [laneTime,budget,mid];omega)⟩
  · intro i hi b all
    apply report.2 i hi b
    intro p hp
    obtain ⟨bits,flag⟩:=facts p hp
    rcases flag with yes|⟨valid,fitting⟩
    · exact .inl yes
    · apply Or.inr
      have bad:=all _ valid fitting
      have eq: value c.e (p.1.getD i z) = !b := by
        rw [←read_here c.e k z p.1 hi]
        cases e:(toWord c.e k z p.1).testBit i <;> cases b <;> simp_all
      have atI:=all_get p.1 z (later c zzM (by omega : mid ≤ mid+1)) bits i
      unfold K at atI;rw [eq] at atI;exact keep atI (by dsimp [budget];omega)

end Pcx293.Flow

namespace Pcx293.Product
open PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Flow
abbrev Raw (k:Nat):=V k
def Extends {k:Nat} (p:Raw k → Option Bool) (v:Raw k → Bool) := ∀j b,p j=some b → v j=b
def Completed {k:Nat} (r:Nat) (p:Raw k → Option Bool) (v:Raw k → Bool):=valid r v ∧ Extends p v
def anchor {k:Nat} (p:Raw k → Option Bool) (j:Raw k) := (p j).getD false
def totalAt {k:Nat} (p:Raw k → Option Bool):=∀j:Raw k,2 ≤ j.1.val → ∃b,p j=some b
def giv {k:Nat} (p:Raw k → Option Bool) (t:Fin 5) (j:Nat) (b:Bool):=∃i:Fin k,i.val=j ∧ p (t,i)=some b
def validAt {k:Nat} (r:Nat) (p:Raw k → Option Bool) (col:Bool) (w:Nat) :=
  w < 2^k ∧ (if col then Tracks.second k r (word (anchor p) 2) w else Tracks.first k r (word (anchor p) 2) w)
    =word (anchor p) (if col then 4 else 3)
def allowed {k:Nat} (r:Nat) (p:Raw k → Option Bool) (col:Bool) (w:Nat) :=
  validAt r p col w ∧ fits k (giv p (if col then 1 else 0)) w

def splice {k:Nat} (p:Raw k → Option Bool) (x y:Nat) (j:Raw k) : Bool :=
  if j.1=0 then x.testBit j.2.val else if j.1=1 then y.testBit j.2.val else anchor p j

theorem word_bit {k:Nat} (v:Raw k → Bool) (t:Fin 5) (i:Fin k): (word v t).testBit i.val=v (t,i) := by
  simp [word,Word.pack_bit,i.isLt]

theorem word_ext {k:Nat} (a b:Raw k → Bool) (t:Fin 5) (eq:∀i,a (t,i)=b (t,i)) : word a t=word b t := by
  apply Sim.canonical (Word.pack_bounded ..) (Word.pack_bounded ..)
  intro i hi;exact (word_bit a t ⟨i,hi⟩).trans ((eq _).trans (word_bit b t ⟨i,hi⟩).symm)

theorem key_agrees {k:Nat} {p:Raw k → Option Bool} (tot:totalAt p) {v:Raw k → Bool}
    (extend:Extends p v) (t:Fin 5) (high:2 ≤ t.val) : word v t=word (anchor p) t := by
  apply word_ext;intro i
  obtain ⟨b,hb⟩:=tot (t,i) high;simp [anchor,hb,extend _ _ hb]

theorem from_completion {k r:Nat} {p:Raw k → Option Bool} (tot:totalAt p) {v:Raw k → Bool}
    (done:Completed r p v) (col:Bool) : allowed r p col (word v (if col then 1 else 0)) := by
  refine ⟨⟨Word.pack_bounded ..,?_⟩,?_⟩
  · obtain ⟨row,col'⟩:=done.1
    have h2:=key_agrees tot done.2 2 (by decide)
    have h3:=key_agrees tot done.2 3 (by decide)
    have h4:=key_agrees tot done.2 4 (by decide)
    cases col
    · simpa [←h2,←h3] using row.symm
    · simpa [←h2,←h4] using col'.symm
  · rintro i hi b ⟨j,rfl,h⟩
    rw [word_bit];exact done.2 _ _ h

theorem splice_w0 {k:Nat} (p:Raw k → Option Bool) (x y:Nat) (bound:x < 2^k):
    word (splice p x y) 0=x := by
  apply Sim.canonical (Word.pack_bounded ..) bound
  intro i hi
  simp [Word.pack_bit,hi,splice]
theorem splice_w1 {k:Nat} (p:Raw k → Option Bool) (x y:Nat) (bound:y < 2^k):
    word (splice p x y) 1=y := by
  apply Sim.canonical (Word.pack_bounded ..) bound
  intro i hi
  simp [Word.pack_bit,hi,splice]
theorem splice_whi {k:Nat} (p:Raw k → Option Bool) (x y:Nat) (t:Fin 5) (hi:2 ≤ t.val):
    word (splice p x y) t=word (anchor p) t := by
  apply word_ext;intro i
  have ne0:t≠0:=by intro e;subst t;contradiction
  have ne1:t≠1:=by intro e;subst t;contradiction
  simp [splice,ne0,ne1]

theorem combine {k r:Nat} {p:Raw k → Option Bool} {x y:Nat} (a:allowed r p false x) (b:allowed r p true y):
    Completed r p (splice p x y) := by
  constructor
  · unfold valid
    rw [splice_w0 _ _ _ a.1.1,splice_w1 _ _ _ b.1.1,splice_whi _ _ _ 2 (by decide),
      splice_whi _ _ _ 3 (by decide),splice_whi _ _ _ 4 (by decide)]
    exact ⟨a.1.2.symm,b.1.2.symm⟩
  · rintro ⟨t,i⟩ sign h
    by_cases r:t=0
    · subst t;simpa [splice] using a.2 i.val i.isLt sign ⟨i,rfl,h⟩
    by_cases s:t=1
    · subst t;simpa [splice] using b.2 i.val i.isLt sign ⟨i,rfl,h⟩
    · simp [splice,r,s,anchor,h]

end Pcx293.Product

namespace Pcx293.Product
open PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Flow PEqualNP.Outside.L_pcx_293.Pcx293.Wire

def seed {k:Nat} (p:Raw k → Option Bool) (l:Lit Nat):=
  ∃t:Fin 5,∃i:Fin k,l.1=2*(k*t.val+i.val) ∧ p (t,i)=some l.2

noncomputable def ctx {k:Nat} (r:Nat) (hk:0 < k) (p:Raw k → Option Bool): Env:=
  ⟨fun c=>c∈(make k r).form,seed p,Sim.getVal (make k r) (base k hk (anchor p))⟩

theorem at_coord {k r:Nat} (hk:0 < k) (p:Raw k → Option Bool) (t:Fin 5) (i:Fin k) :
    (ctx r hk p).e (2*(k*t.val+i.val))=anchor p (t,i) := (Sim.val_even _ _ _).trans (base_raw ..)
theorem raw_bit (k:Nat) (t:Fin 5) (i:Fin k) (z:W):
    (raw k t.val).getD i.val z=pos (2*(k*t.val+i.val)) := by
  have lt:=i.isLt
  have ri:(List.range k)[i.val]?=some i.val := by rw [List.getElem?_eq_getElem (by simpa using lt)];simp
  simp [raw,List.getD_eq_getElem?_getD,ri]
theorem seed_at {k r:Nat} (hk:0 < k) (p:Raw k → Option Bool) (t:Fin 5) (i:Fin k) (b:Bool)
    (h:p (t,i)=some b) (z:W) : Drives (ctx r hk p).F (ctx r hk p).S ((raw k t.val).getD i.val z) 0 b := by
  rw [raw_bit]
  have ht:(put (pos (2*(k*t.val+i.val))) b)=(2*(k*t.val+i.val),b):=by cases b <;> rfl
  unfold Drives;rw [ht];exact ⟨t,i,rfl,h⟩

theorem raws_known {k r:Nat} (hk:0 < k) (p:Raw k → Option Bool) (tot:totalAt p) (t:Fin 5) (big:2 ≤ t.val):
    vv (ctx r hk p) 1 (raw k t.val) := by
  intro w inc
  rcases List.mem_map.mp inc with ⟨j,mj,rfl⟩
  let i:Fin k:=⟨j,List.mem_range.mp mj⟩
  obtain ⟨b,hb⟩:=tot (t,i) big
  have prev:=seed_at (r:=r) hk p t i b hb (pos 0)
  rw [raw_bit] at prev
  have ready:value (ctx r hk p).e (pos (2*(k*t.val+i.val)))=b := by simp [value,pos,at_coord hk p t i,anchor,hb]
  apply later (m:=0)
  · unfold K;rw [ready];exact prev
  · decide

theorem rawWord_eq {k r:Nat} (hk:0 < k) (p:Raw k → Option Bool) (z:W) (t:Fin 5) :
    Sim.toWord (ctx r hk p).e k z (raw k t.val)=word (anchor p) t := by
  apply Sim.canonical (Sim.bounded ..) (Word.pack_bounded ..)
  intro j lt
  let i:Fin k:=⟨j,lt⟩
  have eq:=Sim.read_here (ctx r hk p).e k z (raw k t.val) i.isLt
  rw [raw_bit] at eq
  exact eq.trans ((by simp [value,pos,at_coord hk p t i]:value (ctx r hk p).e (pos (2*(k*t.val+i.val)))=anchor p (t,i)).trans (word_bit _ t i).symm)

theorem anchor_claims {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) :
    let c:=ctx r (by omega : 0 < k) p
    let o:=Sim.constantWire k;let z:=neg o
    K c 1 o ∧ K c 1 z ∧ laneClaim c k r 1 o z ∧ laneClaim c k r 2 o z := by
  let hk:0 < k:=by omega
  let c:=ctx r hk p
  let o:=Sim.constantWire k;let z:=neg o
  let s:Net:={n:=5*k+1}
  have oo:value c.e o=true := by
    have q: c.e (2*(5*k))=true := (Sim.val_even _ _ _).trans (base_one ..)
    simpa [value,Sim.constantWire,o,pos] using q
  have zz:value c.e z=false := by simp [z,value_neg,oo]
  have r:=pair_seq (track_time c h (.inl rfl) r o z zz oo) (fun _=>pair_seq
    (track_time c h (.inr rfl) r o z zz oo) (fun _=>add_rule c [o]))
  have ok := (r s (Sim.val_line (make k _) _) (fun _ h=>h)).2.2
  obtain ⟨row,col,unit⟩:=ok
  have tick:K c 1 o:=by
    unfold K;rw [oo];change adv c.F c.S o
    exact .inr ⟨[o],unit,List.mem_cons_self ..,by simp⟩
  exact ⟨tick,(flip c 1 o).mpr tick,row,col⟩

def evidence {k:Nat} (r:Nat) (hk:0 < k) (p:Raw k → Option Bool) (H:Nat) (col:Bool) :=
  let c:=ctx r hk p
  let t:Fin 5:=if col then 1 else 0
  let bt:=laneTime 1 H r
  ((¬∃w,allowed r p col w) → conflict c bt) ∧
  (∀i:Fin k,∀b,(∀w,allowed r p col w → w.testBit i.val≠b) → 
    iter c.F c.S bt (2*(k*t.val+i.val),!b))

def trk (col:Bool) : Fin 5:=if col then 1 else 0
def dst (col:Bool) : Fin 5:=if col then 4 else 3
def dist (col:Bool) : Nat:=if col then 2 else 1
theorem off (col:Bool):dist col-1=(trk col).val:=by cases col <;> rfl
theorem dy (col:Bool):dist col+2=(dst col).val:=by cases col <;> rfl
theorem di (col:Bool):2 ≤ (dst col).val:=by cases col <;> decide
theorem splitLane (c:Env) (k r:Nat) (o z:W) (row:laneClaim c k r 1 o z) (cl:laneClaim c k r 2 o z) (b:Bool) :
    laneClaim c k r (dist b) o z:=by cases b;exact row;exact cl
theorem direction (b:Bool) (x y:Nat) : (if dist b=1 then x else y)=(if b then y else x) := by cases b <;> rfl
theorem logicalEq {k r:Nat} (e:Nat → Bool) (v:Raw k → Bool) (col:Bool) (z:W) (w:Nat)
    (eq:∀t:Fin 5,Sim.toWord e k z (raw k t.val)=word v t) :
    validWord e k r (dist col) z w ↔
    w < 2^k ∧ (if col then Tracks.second k r (word v 2) w else Tracks.first k r (word v 2) w)=word v (dst col) := by
  unfold validWord;dsimp only
  have wk:Sim.toWord e k z (raw k 2)=word v 2:=eq 2
  rw [dy,wk,eq (dst col),direction]
theorem val_eq {k r:Nat} (hk:0 < k) (p:Raw k → Option Bool) (col:Bool) (z:W) (w:Nat):
    validWord (ctx r hk p).e k r (dist col) z w ↔ validAt r p col w :=
  logicalEq _ _ _ _ _ (rawWord_eq (r:=r) hk p z)
theorem drive_at (c:Env) (t:Fin 5) (i:Fin k) (z:W) (n:Nat) (b:Bool)
    (yes:Drives c.F c.S ((raw k t.val).getD i.val z) n b):iter c.F c.S n (2*(k*t.val+i.val),b) := by
  rw [raw_bit] at yes;cases b <;>exact yes

theorem reports {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) (tot:totalAt p) (H:Nat) (cap:k ≤ 2^H) (col:Bool):
    evidence r (by omega) p H col := by
  let hk:0 < k:=by omega
  let c:=ctx r hk p;let o:=Sim.constantWire k;let z:=neg o
  obtain ⟨one,zero,row,col'⟩:=anchor_claims (r:=r) h p
  let t:=trk col
  let d:=dist col
  let out:=dst col
  have dt:d-1=t.val:=off col
  have u:d+2=out.val:=dy col
  have lc:laneClaim c k r d o z:=splitLane c k r o z row col' col
  have acts:=lc 1 H cap one zero (raws_known hk p tot 2 (by decide)) (u.symm ▸ raws_known hk p tot out (di col)) (giv p t)
    (by rintro i hi b ⟨x,rfl,m⟩;rw [dt];exact keep (seed_at hk p t x b m z) (by decide))
  have equiv:=val_eq (r:=r) hk p col z
  constructor
  · intro no
    apply acts.1;rintro ⟨w,valid,f⟩;exact no ⟨w,(equiv w).mp valid,f⟩
  · intro i b every
    have ev:=acts.2 i.val i.isLt b (fun w v f=>every w ⟨(equiv w).mp v,f⟩)
    rw [dt] at ev
    exact drive_at c t i z _ _ ev

end Pcx293.Product

namespace Pcx293.Product
open PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Flow PEqualNP.Outside.L_pcx_293.Pcx293.Wire

theorem no_models {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) (tot:totalAt p) (H:Nat) (cap:k ≤ 2^H) :
    (¬∃v,Completed r p v) → conflict (ctx r (by omega) p) (laneTime 1 H r) := by
  intro none
  by_cases row:∃w,allowed r p false w
  · apply (reports h p tot H cap true).1
    rintro ⟨w,f⟩;rcases row with ⟨a,b⟩;exact none ⟨_,combine b f⟩
  · exact (reports h p tot H cap false).1 row

theorem flip_target (b a:Bool) (h:b=a) : b≠ !a := by subst b;cases a <;> decide

theorem consensus {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) (tot:totalAt p) (H:Nat) (cap:k ≤ 2^H)
    (has:∃v,Completed r p v) (j:Raw k) (b:Bool) (same:∀v,Completed r p v → v j=b) :
    let c:=ctx r (by omega) p
    iter c.F c.S (laneTime 1 H r) (2*(k*j.1.val+j.2.val),b) := by
  rcases j with ⟨t,i⟩
  rcases has with ⟨v,ok⟩
  by_cases low:t=0
  · subst t
    have must (w:Nat) (is:allowed r p false w): w.testBit i.val≠ !b := by
      have v':=from_completion tot ok true
      have together:=combine is v'
      have ans:=same _ together
      apply flip_target;simpa [splice] using ans
    have ev:=(reports h p tot H cap false).2 i (!b) must
    simpa only [Bool.not_not,Bool.false_eq_true,ite_false,ite_true] using ev
  by_cases mid:t=1
  · subst t
    have must (w:Nat) (is:allowed r p true w): w.testBit i.val≠ !b := by
      have together:=combine (from_completion tot ok false) is
      apply flip_target;simpa [splice] using same _ together
    have ev:=(reports h p tot H cap true).2 i (!b) must
    simpa only [Bool.not_not,Bool.false_eq_true,ite_false,ite_true] using ev
  · have hi:2 ≤ t.val:=by
      have l:t.val≠0:=fun q=>low (Fin.ext q)
      have m:t.val≠1:=fun q=>mid (Fin.ext q)
      omega
    obtain ⟨s,hs⟩:=tot (t,i) hi
    have sb:s=b:=(ok.2 (t,i) s hs).symm.trans (same _ ok)
    subst s
    have base : seed p (2*(k*t.val+i.val),b) :=⟨t,i,rfl,hs⟩
    exact keep (m:=0) (F:=(ctx r (by omega) p).F) (s:=seed p) base (Nat.zero_le _)

theorem admissible_budget (r H:Nat) : laneTime 1 H r ≤ 128*(r+1)*(H+1) := by
  simp only [laneTime,delay,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc,
    Nat.mul_left_comm r 7,Nat.mul_comm r 15];omega

end Pcx293.Product

namespace Pcx293.Product
open PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Unit PEqualNP.Outside.L_pcx_293.Pcx293.Flow PEqualNP.Outside.L_pcx_293.Pcx293.Wire
def typedSeed {k:Nat} (r:Nat) (p:Raw k → Option Bool) (l:Lit (Sum (V k) (Fin (size k r)))) :=
    ∃a:Raw k,l.1=.inl a ∧ p a=some l.2

def TForm (k r:Nat) (h:0 < k): Form (Sum (V k) (Fin (size k r))) := fun c=>c∈clauses k r h

theorem trans_lit (k r:Nat) (h:0 < k) (l:Lit Nat) :
    signmap (fun j=>(name k r h j,true)) l=litMap k r h l := by
  rcases l with ⟨j,b⟩;cases b <;>rfl

theorem forwards {k r:Nat} (h:0 < k) (p:Raw k → Option Bool) (n:Nat) (x:Lit Nat):
    iter (ctx r h p).F (ctx r h p).S n x → 
    iter (TForm k r h) (typedSeed r p) n (litMap k r h x) := by
  let f:=fun j=>(name k r h j,true)
  have included (c) (mem:(ctx r h p).F c) : TForm k r h (transClause f c):=by
    apply List.mem_map.mpr;refine ⟨c,mem,?_⟩
    exact List.map_congr_left (fun a _=>(trans_lit k r h a).symm)
  have base (a) (yes:(ctx r h p).S a) : iter (TForm k r h) (typedSeed r p) 0 (signmap f a):=by
    obtain ⟨t,i,eq,val⟩:=yes
    rw [trans_lit]
    exact ⟨(t,i),by change name k r h a.1 = _;rw [eq,name_raw],val⟩
  intro src
  have q:=shift_steps f included 0 base n x src
  simpa only [Nat.zero_add,f,trans_lit] using q

def TypedConflict {k r:Nat} (h:0 < k) (p:Raw k → Option Bool) (B:Nat) :=
  ∃cl,TForm k r h cl ∧ ∀l∈cl,iter (TForm k r h) (typedSeed r p) B (neg l)

theorem conflict_trans {k r:Nat} (h:0 < k) (p:Raw k → Option Bool) (a b:Nat) (le:a ≤ b) :
    conflict (ctx r h p) a → TypedConflict (r:=r) h p b := by
  rintro ⟨cl,inc,rejected⟩
  refine ⟨cl.map (litMap k r h),List.mem_map.mpr ⟨cl,inc,rfl⟩,?_⟩
  intro t ht;rcases List.mem_map.mp ht with ⟨l,hl,rfl⟩
  exact keep (forwards h p a (neg l) (rejected l hl)) le

theorem initial_sound {k r:Nat} {p:Raw k → Option Bool} {v:Raw k → Bool} (a:Fin (size k r) → Bool)
    (ext:Extends p v) (l) (seed:typedSeed r p l) : Sum.elim v a l.1=l.2 := by
  obtain ⟨j,eq,r⟩:=seed;rw [eq];exact ext j l.2 r

theorem typed_up {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) (tot:totalAt p)
    (H B:Nat) (cap:k ≤ 2^H) (fits:laneTime 1 H r ≤ B) :
    ((¬∃v,Completed r p v) ↔ TypedConflict (r:=r) (by omega) p B) ∧
    ((∃v,Completed r p v) → ∀j:Raw k,∀b,
      (∀v,Completed r p v → v j=b) ↔ iter (TForm k r (by omega)) (typedSeed r p) B (.inl j,b)) := by
  have hk:0 < k:=by omega
  constructor
  · constructor
    · intro bad;exact conflict_trans hk p _ _ fits ((no_models h p tot H cap) bad)
    · rintro clash ⟨v,valid,ext⟩
      rcases (Dense.extensions h v).mp valid with ⟨a,model⟩
      exact no_conflict (F:=TForm k r hk) model (initial_sound a ext) B clash
  · intro has j b
    constructor
    · intro same
      have live:=consensus h p tot H cap has j b same
      have sent:=forwards hk p _ _ live
      change iter _ _ _ (name k r hk (2*(k*j.1.val+j.2.val)),b) at sent
      rw [name_raw] at sent
      exact keep sent fits
    · intro known v complete
      rcases (Dense.extensions h v).mp complete.1 with ⟨a,model⟩
      exact sound (F:=TForm k r hk) model (initial_sound a complete.2) B (.inl j,b) known

end Pcx293.Product

namespace Pcx293.Witness
open PEqualNP.Outside.L_pcx_293.Pcx293.Make PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.ProofComplexity

def formula (k r : Nat) (hk : 0 < k) : Finset (Clause (Sum (V k) (Fin (size k r)))) :=
    ((clauses k r hk).map List.toFinset).toFinset

theorem width (k r : Nat) (h : 0 < k) :
    ∀ C∈formula k r h,C.card ≤ 3 := by
  intro C mem
  rcases List.mem_map.mp (List.mem_toFinset.mp mem) with ⟨c,hc,rfl⟩
  exact Nat.le_trans (List.toFinset_card_le _) (Dense.width k r h hc)

theorem aggregate_weight {A:Type} [DecidableEq A] (cs : List (List A)) :
    (∑ c ∈ (cs.map List.toFinset).toFinset,c.card) ≤ (cs.map List.length).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    let t:=c.toFinset
    let F:=(cs.map List.toFinset).toFinset
    simp only [List.map_cons,List.toFinset_cons,List.sum_cons]
    change (∑ g ∈ insert t F,g.card) ≤ c.length+(cs.map List.length).sum
    by_cases ht : t∈F
    · rw [Finset.insert_eq_of_mem ht];exact Nat.le_trans ih (Nat.le_add_left _ _)
    · rw [Finset.sum_insert ht]
      exact Nat.add_le_add (List.toFinset_card_le _) ih

theorem posted_size (k r : Nat) (h : 0 < k) :
    size k r + (∑ C ∈ formula k r h,C.card) ≤ 8192*(k+1)*4^r := by
  have le:=aggregate_weight (clauses k r h)
  have eq : ((clauses k r h).map List.length).sum=Tape.litWeight (make k r).form := by
    simp [clauses,Tape.litWeight,List.map_map,Function.comp_def]
  rw [eq] at le
  exact Nat.le_trans (Nat.add_le_add_left le (size k r)) (MCost.actual_literal_budget k r)

theorem finsat (k r:Nat) (h:0 < k) (w:Sum (V k) (Fin (size k r)) → Bool) :
    Satisfies w (↑(formula k r h):Set _) ↔ Unit.Sat (fun c=>c∈clauses k r h) w := by
  constructor
  · intro ok c hc
    have found : c.toFinset∈formula k r h := List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,hc,rfl⟩)
    rcases ok _ found with ⟨l,hl,sat⟩
    exact ⟨l,List.mem_toFinset.mp hl,sat⟩
  · intro ok C hC
    rcases List.mem_map.mp (List.mem_toFinset.mp hC) with ⟨c,mem,rfl⟩
    rcases ok c mem with ⟨l,hl,sat⟩
    exact ⟨l,List.mem_toFinset.mpr hl,sat⟩

theorem pack_sum (n:Nat) (f:Nat → Bool) : Word.pack n f = ∑j:Fin n,(f j.val).toNat*2^j.val := by
  induction n with
  | zero => simp [Word.pack]
  | succ n ih =>
    rw [Word.pack,List.range_succ,List.foldl_append]
    change Word.pack n f ||| ((f n).toNat <<< n) = _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,←ih]
    cases eq:f n
    · simp
    · simp [Nat.shiftLeft_eq,Nat.or_two_pow_eq_add_of_lt (Word.pack_bounded n f)]

theorem word_sum {k:Nat} (v:V k → Bool) (t:Fin 5) : word v t = ∑j:Fin k,(v (t,j)).toNat*2^j.val := by
  simp [word,pack_sum]

theorem posted_extensions {k r:Nat} (h:k % 6=3) (v:V k → Bool) :
    (let w:=fun t:Fin 5 => ∑j:Fin k,(v (t,j)).toNat*2^j.val
     w 3=Tracks.first k r (w 2) (w 0) ∧ w 4=Tracks.second k r (w 2) (w 1)) ↔
      ∃ a:Fin (size k r) → Bool,Satisfies (Sum.elim v a) (↑(formula k r (by omega)):Set _) := by
  have v':=Dense.extensions h (r:=r) v
  simpa only [valid,word_sum,←finsat] using v'

end Pcx293.Witness

namespace Pcx293.Witness
open PEqualNP.Outside.L_pcx_293.Pcx293.Dense PEqualNP.Outside.L_pcx_293.Pcx293.Product PEqualNP.ProofComplexity

def advance {A:Type} (f:Finset (Clause A)) (s:Set (Literal A)):Set (Literal A) :=
  s ∪ {l|∃ C ∈ f,l∈C ∧ ∀ other∈C,other≠l → PEqualNP.Search.negLit other∈s}

theorem advance_fun {A:Type} (f:Finset (Clause A)) :
    advance f = (fun S:Set (Literal A)=>S ∪ {l|∃ C ∈ f,l∈C ∧ ∀ other∈C,other≠l → PEqualNP.Search.negLit other∈S}) := rfl

theorem adv_eq {k r:Nat} (h:0 < k) (s:Set (Literal (Sum (V k) (Fin (size k r))))) :
    advance (formula k r h) s={q|Unit.adv (TForm k r h) (fun q=>q∈s) q} := by
  apply Set.ext;intro q
  constructor
  · rintro (old|⟨C,hC,inC,need⟩)
    · exact .inl old
    · rcases List.mem_map.mp (List.mem_toFinset.mp hC) with ⟨c,hc,rfl⟩
      exact .inr ⟨c,hc,List.mem_toFinset.mp inC,fun p hp diff=>need p (List.mem_toFinset.mpr hp) diff⟩
  · rintro (old|⟨c,hc,mem,need⟩)
    · exact .inl old
    · exact .inr ⟨c.toFinset,List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,hc,rfl⟩),List.mem_toFinset.mpr mem,
        fun p hp diff=>need p (List.mem_toFinset.mp hp) diff⟩

theorem iter_eq {k r:Nat} (h:0 < k) (p:Raw k → Option Bool) (N:Nat):
    (advance (formula k r h))^[N] ({q|typedSeed r p q}) = {q|Unit.iter (TForm k r h) (typedSeed r p) N q} := by
  induction N with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply',ih,adv_eq];rfl

theorem conflict_eq {k r:Nat} (h:0 < k) (p:Raw k → Option Bool) (B:Nat):
    TypedConflict (r:=r) h p B ↔
    ∃C∈formula k r h,∀l∈C,PEqualNP.Search.negLit l∈(advance (formula k r h))^[B] {q|typedSeed r p q} := by
  rw [iter_eq]
  constructor
  · rintro ⟨cl,hc,fx⟩
    exact ⟨cl.toFinset,List.mem_toFinset.mpr (List.mem_map.mpr ⟨cl,hc,rfl⟩),
      fun l hl=>fx l (List.mem_toFinset.mp hl)⟩
  · rintro ⟨cl,found,fx⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp found) with ⟨c,hc,rfl⟩
    exact ⟨c,hc,fun l hl=>fx l (List.mem_toFinset.mpr hl)⟩

theorem posted_up {k r:Nat} (h:k % 6=3) (p:Raw k → Option Bool) (total:totalAt p) :
    let hk:0 < k:=by omega
    let B:=128*(r+1)*(Nat.clog 2 k+1)
    let f:=formula k r hk
    let known:=(advance f)^[B] {q|typedSeed r p q}
    ((¬∃v,Completed r p v) ↔ ∃C∈f,∀l∈C,PEqualNP.Search.negLit l∈known) ∧
    ((∃v,Completed r p v) → ∀raw:Raw k,∀sign:Bool,(∀v,Completed r p v → v raw=sign) ↔ (Sum.inl raw,sign)∈known) := by
  dsimp only
  have t:=typed_up h (r:=r) p total (Nat.clog 2 k) _ (Nat.le_pow_clog (by decide) k) (admissible_budget r _)
  refine ⟨t.1.trans (conflict_eq _ p _),?_⟩
  intro hv raw sign
  rw [iter_eq]
  exact t.2 hv raw sign

end Pcx293.Witness

end PEqualNP.Outside.L_pcx_293

set_option maxRecDepth 1600 in
theorem PEqualNP.Outside.L_pcx_293 : (∀ (k r : ℕ), k % 6 = 3 →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let V := Fin 5 × Fin k
  let word := fun (v : V → Bool) (track : Fin 5) =>
    ∑ j : Fin k, (v (track,j)).toNat * 2^j.val
  let agrees := fun (v : V → Bool) =>
    word v 3 = first (word v 2) (word v 0) ∧
    word v 4 = second (word v 2) (word v 1)
  let rounds := 128*(r+1)*(Nat.clog 2 k+1)
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    m + (∑ C ∈ F, C.card) ≤ 8192*(k+1)*4^r ∧
    (∀ C ∈ F, C.card ≤ 3) ∧
    (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
    ∀ ρ : V → Option Bool, (∀ j : V, 2 ≤ j.1.val → ∃ b : Bool, ρ j = some b) →
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
      let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
        S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
          PEqualNP.Search.negLit other ∈ S}
      let known := (advance^[rounds]) seed
      let complete := fun v : V → Bool => agrees v ∧
        ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
      ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, PEqualNP.Search.negLit l ∈ known) ∧
      ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
        (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known)) := by
  intro k r h
  dsimp only
  refine ⟨PEqualNP.Outside.L_pcx_293.Pcx293.Dense.size k r,PEqualNP.Outside.L_pcx_293.Pcx293.Witness.formula k r (by omega),PEqualNP.Outside.L_pcx_293.Pcx293.Witness.posted_size k r (by omega),
    PEqualNP.Outside.L_pcx_293.Pcx293.Witness.width k r (by omega),?_,?_⟩
  · intro v
    exact PEqualNP.Outside.L_pcx_293.Pcx293.Witness.posted_extensions h v
  · intro p full
    have result:=PEqualNP.Outside.L_pcx_293.Pcx293.Witness.posted_up (r:=r) h p full
    simpa only [PEqualNP.Outside.L_pcx_293.Pcx293.Product.Completed,PEqualNP.Outside.L_pcx_293.Pcx293.Dense.valid,PEqualNP.Outside.L_pcx_293.Pcx293.Witness.word_sum,PEqualNP.Outside.L_pcx_293.Pcx293.Product.Extends,
      PEqualNP.Outside.L_pcx_293.Pcx293.Witness.advance_fun,PEqualNP.Outside.L_pcx_293.Pcx293.Product.Raw,PEqualNP.Outside.L_pcx_293.Pcx293.Dense.V,PEqualNP.Outside.L_pcx_293.Pcx293.Product.typedSeed,PEqualNP.Outside.L_pcx_293.Pcx293.Tracks.first,PEqualNP.Outside.L_pcx_293.Pcx293.Tracks.second,
      PEqualNP.Outside.L_pcx_293.Pcx293.Tracks.constant,PEqualNP.Outside.L_pcx_293.Pcx293.Word.rot,PEqualNP.Outside.L_pcx_293.Pcx293.Word.step] using result
