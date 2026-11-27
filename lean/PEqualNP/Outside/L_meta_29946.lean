import PEqualNP.Defs

/-!
Exact four-separated two-round row-mark parity characterization.
Auxiliary proofs use a Boolean-coordinate F₂ development (finite differences,
rank, and cyclic window geometry) and transport directly to the posted types.
This proof was developed independently for L-meta-29946.
-/

namespace PEqualNP.Outside.L_meta_29946_aux

namespace PNP29946.Binary
abbrev Fn (V : Type) := V → Bool

structure AddSpace (V : Type) where
  add : V → V → V
  origin : V
  commute : ∀ x a b, add (add x a) b = add (add x b) a
  reach : ∀ x y, ∃ u, add x u=y

def xor {V : Type} (f g : Fn V) : Fn V := fun x => f x ^^ g x
def prod {V : Type} (f g : Fn V) : Fn V := fun x => f x && g x
def move {V : Type} (s : AddSpace V) (u : V) (f : Fn V) : Fn V := fun x => f (s.add x u)
def diff {V : Type} (s : AddSpace V) (u : V) (f : Fn V) : Fn V := xor (move s u f) f

def Low {V : Type} (s : AddSpace V) : Nat → Fn V → Prop
  | 0,f => ∀ x y, f x = f y
  | d+1,f => ∀ u, Low s d (diff s u f)

variable {V : Type} {s : AddSpace V}

theorem low_const (d : Nat) (c : Bool) : Low s d (fun _=>c) := by
  induction d generalizing c with
  | zero => intro x y; rfl
  | succ d ih =>
    intro u
    have h : diff s u (fun _=>c)=(fun _=>false) := by funext x; simp [diff,xor,move]
    rw [h]
    exact ih false

theorem low_succ {d : Nat} {f : Fn V} (p : Low s d f) : Low s (d+1) f := by
  induction d generalizing f with
  | zero =>
    intro u x y
    change (f (s.add x u) ^^ f x) = (f (s.add y u) ^^ f y)
    rw [p (s.add x u) x,p (s.add y u) y,Bool.xor_self,Bool.xor_self]
  | succ d ih => intro a; exact ih (p a)

theorem low_mono {i j : Nat} {f : Fn V} (h : i≤j) (p : Low s i f) :
    Low s j f := by
  induction h with
  | refl => exact p
  | step _ ih => exact low_succ ih

theorem low_move {d : Nat} {f : Fn V} (u : V) (p : Low s d f) : Low s d (move s u f) := by
  induction d generalizing f with
  | zero => exact fun _ _=>p _ _
  | succ d ih =>
    intro a
    have e : diff s a (move s u f) = move s u (diff s a f) := by
      funext x
      simp [diff,move,xor,s.commute x a u]
    rw [e]
    exact ih (p a)

theorem low_xor {d : Nat} {f g : Fn V} (p : Low s d f) (q : Low s d g) :
    Low s d (xor f g) := by
  induction d generalizing f g with
  | zero =>
    intro x y
    change (f x ^^ g x) = (f y ^^ g y)
    rw [p x y,q x y]
  | succ d ih =>
    intro u
    have e : diff s u (xor f g) = xor (diff s u f) (diff s u g) := by
      funext x
      change ((f (s.add x u) ^^ g (s.add x u)) ^^ (f x ^^ g x)) =
        ((f (s.add x u) ^^ f x) ^^ (g (s.add x u) ^^ g x))
      generalize f (s.add x u)=a
      generalize g (s.add x u)=b
      generalize f x=c
      generalize g x=e
      cases a <;> cases b <;> cases c <;> cases e <;> decide
    rw [e]
    exact ih (p u) (q u)

private theorem low_scaled {d : Nat} {f : Fn V} (c : Bool) (p : Low s d f) :
    Low s d (fun x=>c && f x) := by
  cases c
  · exact low_const _ false
  · exact p

theorem low_prod (i j : Nat) {f g : Fn V} (p : Low s i f) (q : Low s j g) :
    Low s (i+j) (prod f g) := by
  cases i with
  | zero =>
    have e : prod f g=fun x=>f s.origin && g x := by
      funext x
      exact congrArg (· && g x) (p x s.origin)
    rw [e,Nat.zero_add]
    exact low_scaled _ q
  | succ i =>
    cases j with
    | zero =>
      have e : prod f g=fun x=>g s.origin && f x := by
        funext x
        change (f x && g x) = (g s.origin && f x)
        rw [q x s.origin,Bool.and_comm]
      rw [e,Nat.add_zero]
      exact low_scaled _ p
    | succ j =>
      intro u
      have e : diff s u (prod f g) = xor (prod (diff s u f) (move s u g)) (prod f (diff s u g)) := by
        funext x
        change ((f (s.add x u) && g (s.add x u)) ^^ (f x && g x)) =
          (((f (s.add x u) ^^ f x) && g (s.add x u)) ^^ (f x && (g (s.add x u) ^^ g x)))
        generalize f (s.add x u)=a
        generalize g (s.add x u)=b
        generalize f x=c
        generalize g x=e
        cases a <;> cases b <;> cases c <;> cases e <;> decide
      rw [e]
      have A := low_prod i (j+1) (p u) (low_move u q)
      have B := low_prod (i+1) j p (q u)
      have en : i+(j+1)=(i+1)+j := by omega
      rw [en] at A
      exact low_xor A B
termination_by i+j
decreasing_by all_goals omega

def Additive (s : AddSpace V) (l : Fn V) : Prop :=
  ∀ x u, l (s.add x u) = (l x ^^ l u)

theorem low_affine {l : Fn V} (p : Additive s l) (c : Bool) :
    Low s 1 (fun x=>l x ^^ c) := by
  intro u x y
  change (((l (s.add x u)) ^^ c) ^^ (l x ^^ c)) =
    (((l (s.add y u)) ^^ c) ^^ (l y ^^ c))
  rw [p,p]
  cases l x <;> cases l y <;> cases l u <;> cases c <;> decide

theorem low_three_iff (f : Fn V) :
    Low s 3 f ↔ ∀ v : Fin 4→V, ∀ x,
       ((List.ofFn v).foldl (fun g u=>diff s u g) f) x=false := by
  change (∀ (a b c : V) (x y : V), diff s c (diff s b (diff s a f)) x =
    diff s c (diff s b (diff s a f)) y) ↔ _
  constructor
  · intro h v x
    simp only [List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
    change (diff s (v 2) (diff s (v 1) (diff s (v 0) f)) (s.add x (v 3)) ^^
      diff s (v 2) (diff s (v 1) (diff s (v 0) f)) x) = false
    rw [h (v 0) (v 1) (v 2) (s.add x (v 3)) x,Bool.xor_self]
  · intro h a b c x y
    obtain ⟨u,hu⟩ := s.reach x y
    let v : Fin 4→V := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => u)))
    have z := h v x
    simp only [List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil] at z
    change (diff s c (diff s b (diff s a f)) (s.add x u) ^^
      diff s c (diff s b (diff s a f)) x) = false at z
    rw [hu] at z
    generalize e1 : (diff s c (diff s b (diff s a f)) x)=q at z ⊢
    generalize e2 : (diff s c (diff s b (diff s a f)) y)=r at z ⊢
    cases q <;> cases r <;> simp_all

end PNP29946.Binary

namespace PNP29946.Binary
variable {V : Type} {s : AddSpace V}

def quad (a b c d : Fn V) := xor (prod a b) (xor (prod b c) (prod c d))
def top (a b c d e : Fn V) := prod (prod b d) (prod (xor a c) (xor c e))
def correct (a b c d e : Fn V) :=
  xor (prod (prod a b) c)
    (xor (prod b c) (xor (prod c d) (xor (prod (prod c d) e) (prod (prod b c) d))))

/-- The only fourth-degree part of the false row's nonlinear product. -/
theorem squarefree (a b c d e : Fn V) :
    xor (prod (quad a b c d) (quad b c d e)) (top a b c d e) = correct a b c d e := by
  funext x
  simp only [quad,top,correct,xor,prod]
  cases a x <;> cases b x <;> cases c x <;> cases d x <;> cases e x <;> decide

theorem low_quad {a b c d : Fn V}
    (ha : Low s 1 a) (hb : Low s 1 b) (hc : Low s 1 c) (hd : Low s 1 d) :
    Low s 2 (quad a b c d) :=
  low_xor (low_prod 1 1 ha hb) (low_xor (low_prod 1 1 hb hc) (low_prod 1 1 hc hd))

theorem low_correct {a b c d e : Fn V}
    (ha : Low s 1 a) (hb : Low s 1 b) (hc : Low s 1 c) (hd : Low s 1 d) (he : Low s 1 e) :
    Low s 3 (correct a b c d e) :=
  low_xor (low_prod 2 1 (low_prod 1 1 ha hb) hc)
    (low_xor (low_mono (by decide : 2≤3) (low_prod 1 1 hb hc))
       (low_xor (low_mono (by decide : 2≤3) (low_prod 1 1 hc hd))
          (low_xor (low_prod 2 1 (low_prod 1 1 hc hd) he)
             (low_prod 2 1 (low_prod 1 1 hb hc) hd))))

def row (a b c d e l m r : Fn V) :=
  xor (prod (xor (quad a b c d) l) (xor (quad b c d e) m)) r

theorem row_error (a b c d e l m r : Fn V)
    (ha : Low s 1 a) (hb : Low s 1 b) (hc : Low s 1 c) (hd : Low s 1 d) (he : Low s 1 e)
    (hl : Low s 1 l) (hm : Low s 1 m) (hr : Low s 2 r) :
    Low s 3 (xor (row a b c d e l m r) (top a b c d e)) := by
  let u := quad a b c d
  let v := quad b c d e
  have expand : xor (row a b c d e l m r) (top a b c d e) =
      xor (xor (prod u v) (top a b c d e))
        (xor (prod u m) (xor (prod l v) (xor (prod l m) r))) := by
    funext x
    change ((((u x ^^ l x) && (v x ^^ m x)) ^^ r x) ^^ top a b c d e x) =
      (((u x && v x) ^^ top a b c d e x) ^^
        ((u x && m x) ^^ ((l x && v x) ^^ ((l x && m x) ^^ r x))))
    cases u x <;> cases v x <;> cases l x <;> cases m x <;>
      cases r x <;> cases top a b c d e x <;> decide
  rw [expand,squarefree]
  exact low_xor (low_correct ha hb hc hd he)
    (low_xor (low_prod 2 1 (low_quad ha hb hc hd) hm)
      (low_xor (low_prod 1 2 hl (low_quad hb hc hd he))
        (low_xor (low_mono (by decide : 2≤3) (low_prod 1 1 hl hm))
          (low_mono (by decide : 2≤3) hr))))

theorem common_low {n : Nat} {a b : Fn V} (e : Low s n (xor a b)) :
    Low s n a ↔ Low s n b := by
  constructor
  · intro h
    have v : (xor a (xor a b))=b := by
      funext x
      change (a x ^^ (a x ^^ b x))=b x
      cases a x <;> cases b x <;> decide
    exact v ▸ low_xor h e
  · intro h
    have v : (xor b (xor a b))=a := by
      funext x
      change (b x ^^ (a x ^^ b x))=a x
      cases a x <;> cases b x <;> decide
    exact v ▸ low_xor h e

theorem row_cubic_iff (a b c d e l m r : Fn V)
    (ha : Low s 1 a) (hb : Low s 1 b) (hc : Low s 1 c) (hd : Low s 1 d) (he : Low s 1 e)
    (hl : Low s 1 l) (hm : Low s 1 m) (hr : Low s 2 r) :
    Low s 3 (row a b c d e l m r) ↔ Low s 3 (top a b c d e) :=
  common_low (row_error a b c d e l m r ha hb hc hd he hl hm hr)

end PNP29946.Binary

namespace PNP29946.Binary
abbrev Word (k : Nat) := Fin k → Bool

def wireAdd {k : Nat} (x y : Word k) : Word k := fun j => x j ^^ y j

def wireSpace (k : Nat) : AddSpace (Word k) where
  add := wireAdd
  origin := fun _ => false
  commute := by
    intro x a b
    funext j
    change ((x j ^^ a j) ^^ b j) = ((x j ^^ b j) ^^ a j)
    cases x j <;> cases a j <;> cases b j <;> decide
  reach := by
    intro x y
    refine ⟨wireAdd x y,?_⟩
    funext j
    change (x j ^^ (x j ^^ y j))=y j
    cases x j <;> cases y j <;> decide

theorem coordinate {k : Nat} (j : Fin k) :
    Low (wireSpace k) 1 (fun x=>x j) := by
  have q : Additive (wireSpace k) (fun x=>x j) := fun _ _=>rfl
  simpa using low_affine q false

def idx {k : Nat} (h : 0<k) (n : Nat) : Fin k := ⟨n % k,Nat.mod_lt _ h⟩
def fwd {k : Nat} (h : 0<k) (i : Fin k) (t : Nat) : Fin k := idx h (i.val+t)
def rot {k : Nat} (h : 0<k) (s : Nat) (x : Word k) (i : Fin k) : Bool :=
  x (idx h (i.val+k-s % k))
def back {k : Nat} (h : 0<k) (i : Fin k) := idx h (i.val+k-1)
def mix {k : Nat} (h : 0<k) (x : Word k) (i : Fin k) : Bool :=
  (x i ^^ x (fwd h i 1)) ^^ x (back h i)
def step {k : Nat} (h : 0<k) (x : Word k) (i : Fin k) : Bool :=
  x i ^^ ((true ^^ x (fwd h i 1)) && x (fwd h i 2))

theorem fwd_fwd {k : Nat} (h : 0<k) (i : Fin k) (p q : Nat) :
    fwd h (fwd h i p) q = fwd h i (p+q) := by
  apply Fin.ext
  change ((i.val+p) % k+q) % k=(i.val+(p+q)) % k
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem back_fwd {k : Nat} (h : 0<k) (i : Fin k) (p : Nat) (hp : 0<p) :
    back h (fwd h i p) = fwd h i (p-1) := by
  apply Fin.ext
  change (((i.val+p) % k)+k-1) % k=(i.val+(p-1)) % k
  have z : (i.val+p) % k+k-1=(i.val+p) % k+(k-1) := by omega
  rw [z, Nat.mod_add_mod]
  have zz : i.val+p+(k-1) = i.val+(p-1)+k := by omega
  rw [zz, Nat.add_mod_right]

structure Params (k : Nat) where
  name : Word k
  c₁ : Word k
  c₂ : Word k

def zz {k : Nat} (h : 0<k) (p : Params k) (x : Word k) : Word k :=
  mix h (wireAdd (rot h 1 x) p.name)
def yy {k : Nat} (h : 0<k) (p : Params k) (x : Word k) : Word k :=
  wireAdd (wireAdd (step h (zz h p x)) (rot h 0 x)) p.c₁
def mm {k : Nat} (h : 0<k) (p : Params k) (x : Word k) : Word k :=
  mix h (yy h p x)
def outFalse {k : Nat} (h : 0<k) (p : Params k) (x : Word k) : Word k :=
  wireAdd (wireAdd (step h (mm h p x)) (rot h 2 x)) p.c₂

def ya {k : Nat} (h : 0<k) (p : Params k) (x : Word k) (i : Fin k) : Bool :=
  ((zz h p x i ^^ zz h p x (fwd h i 2)) ^^ rot h 0 x i) ^^ p.c₁ i
def ma {k : Nat} (h : 0<k) (p : Params k) (x : Word k) (i : Fin k) : Bool :=
  mix h (ya h p x) i

theorem low_z {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 1 (fun x=>zz h p x i) := by
  have lc (j : Fin k) : Low (wireSpace k) 1 (fun x=>rot h 1 x j ^^ p.name j) :=
    low_xor (coordinate _) (low_const _ _)
  exact low_xor (low_xor (lc i) (lc (fwd h i 1))) (lc (back h i))

theorem low_ya {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 1 (fun x=>ya h p x i) :=
  low_xor (low_xor (low_xor (low_z h p i) (low_z h p (fwd h i 2))) (coordinate _)) (low_const _ _)

theorem low_ma {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 1 (fun x=>ma h p x i) :=
  low_xor (low_xor (low_ya h p i) (low_ya h p (fwd h i 1))) (low_ya h p (back h i))

theorem y_split {k : Nat} (h : 0<k) (p : Params k) (x : Word k) (i : Fin k) :
    yy h p x i = ((zz h p x (fwd h i 1) && zz h p x (fwd h i 2)) ^^ ya h p x i) := by
  simp only [yy,wireAdd,step,ya]
  have expansion (a b : Bool) : ((true ^^ a) && b) = ((a && b) ^^ b) := by cases a <;> cases b <;> rfl
  simp only [expansion,Bool.xor_assoc,Bool.xor_left_comm]

theorem low_y {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 2 (fun x=>yy h p x i) := by
  have e : (fun x=>yy h p x i) =
      xor (prod (fun x=>zz h p x (fwd h i 1)) (fun x=>zz h p x (fwd h i 2))) (fun x=>ya h p x i) :=
    funext (fun x=>y_split h p x i)
  rw [e]
  exact low_xor (low_prod 1 1 (low_z h p _) (low_z h p _))
    (low_succ (low_ya h p _))

theorem low_m {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 2 (fun x=>mm h p x i) :=
  low_xor (low_xor (low_y h p i) (low_y h p (fwd h i 1))) (low_y h p (back h i))

def atZ {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) (t : Nat) : Fn (Word k) :=
  fun x=>zz h p x (fwd h i t)

theorem mix_split {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) (t : Nat) (ht : 0<t) (x : Word k) :
    mm h p x (fwd h i t) =
      (quad (atZ h p i t) (atZ h p i (t+1)) (atZ h p i (t+2)) (atZ h p i (t+3)) x ^^
        ma h p x (fwd h i t)) := by
  simp only [mm,ma,mix,y_split,back_fwd h i t ht,fwd_fwd,quad,prod,xor,atZ]
  have e1 : t-1+1=t := by omega
  have e2 : t-1+2=t+1 := by omega
  have e3 : t+1+1=t+2 := by omega
  have e4 : t+1+2=t+3 := by omega
  rw [e1,e2,e3,e4]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

def lowL {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) : Fn (Word k) :=
  xor (fun _ => true) (fun x=>ma h p x (fwd h i 1))
def lowM {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) : Fn (Word k) :=
  fun x=>ma h p x (fwd h i 2)
def lowR {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) : Fn (Word k) :=
  xor (xor (fun x=>mm h p x i) (fun x=>rot h 2 x i)) (fun _=>p.c₂ i)

theorem full_split {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    (fun x=>outFalse h p x i) =
      row (atZ h p i 1) (atZ h p i 2) (atZ h p i 3) (atZ h p i 4) (atZ h p i 5)
        (lowL h p i) (lowM h p i) (lowR h p i) := by
  funext x
  have t1 := mix_split h p i 1 (by decide) x
  have t2 := mix_split h p i 2 (by decide) x
  simp only [outFalse,wireAdd,step,t1,t2,row,xor,prod,lowL,lowM,lowR]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

theorem out_cubic_iff {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 3 (fun x=>outFalse h p x i) ↔
      Low (wireSpace k) 3 (top (atZ h p i 1) (atZ h p i 2) (atZ h p i 3) (atZ h p i 4) (atZ h p i 5)) := by
  rw [full_split]
  apply row_cubic_iff
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_xor (low_const _ _) (low_ma h p _)
  · exact low_ma h p _
  · exact low_xor (low_xor (low_m h p _) (low_succ (coordinate _))) (low_const _ _)

end PNP29946.Binary

namespace PNP29946.Binary
abbrev Bits4 := Bool × Bool × Bool × Bool

def add4 (x y : Bits4) : Bits4 :=
  ⟨(x.1 ^^ y.1), (x.2.1 ^^ y.2.1), (x.2.2.1 ^^ y.2.2.1), (x.2.2.2 ^^ y.2.2.2)⟩

def zero4 : Bits4 := (false,false,false,false)

def space4 : AddSpace Bits4 where
  add := add4
  origin := zero4
  commute := by
    rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ ⟨i,j,k,l⟩
    have t (x y z : Bool) : ((x ^^ y) ^^ z)=((x ^^ z) ^^ y) := by
      cases x <;> cases y <;> cases z <;> decide
    simp [add4,t]
  reach := by
    rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩
    have t (x y : Bool) : (x ^^ (x ^^ y))=y := by
      cases x <;> cases y <;> decide
    exact ⟨add4 ⟨a,b,c,d⟩ ⟨e,f,g,h⟩, by simp [add4,t]⟩

def Hom {V W : Type} (s : AddSpace V) (t : AddSpace W) (φ : V→W) :=
  ∀ x u, φ (s.add x u)=t.add (φ x) (φ u)

theorem diff_comp {V W : Type} {s : AddSpace V} {t : AddSpace W}
    {φ : V→W} (h : Hom s t φ) (u : V) (f : Fn W) :
    diff s u (fun x=>f (φ x))=(fun x=>diff t (φ u) f (φ x)) := by
  funext x
  simp [diff,xor,move,h x u]

theorem low_pullback {V W : Type} {s : AddSpace V} {t : AddSpace W}
    {φ : V→W} (h : Hom s t φ) {n : Nat} {f : Fn W} (p : Low t n f) :
    Low s n (fun x => f (φ x)) := by
  induction n generalizing f with
  | zero => exact fun x y=>p (φ x) (φ y)
  | succ n ih =>
    intro u
    rw [diff_comp h]
    exact ih (p (φ u))

theorem low_descend {V W : Type} {s : AddSpace V} {t : AddSpace W}
    {φ : V→W} (h : Hom s t φ) (surj : ∀ y, ∃ x, φ x=y) {n : Nat} {f : Fn W}
    (p : Low s n (fun x => f (φ x))) : Low t n f := by
  induction n generalizing f with
  | zero =>
    intro x y
    obtain ⟨a,rfl⟩ := surj x
    obtain ⟨b,rfl⟩ := surj y
    exact p a b
  | succ n ih =>
    intro u
    obtain ⟨a,rfl⟩ := surj u
    have A := p a
    rw [diff_comp h] at A
    exact ih A

def four (c : Bits4) (x : Bits4) : Bool :=
  (x.1 ^^ c.1) && (x.2.1 ^^ c.2.1) && (x.2.2.1 ^^ c.2.2.1) && (x.2.2.2 ^^ c.2.2.2)

def e0 : Bits4 := (true,false,false,false)
def e1 : Bits4 := (false,true,false,false)
def e2 : Bits4 := (false,false,true,false)
def e3 : Bits4 := (false,false,false,true)

theorem mixed_four (c : Bits4) :
    diff space4 e3 (diff space4 e2 (diff space4 e1 (diff space4 e0 (four c)))) zero4 = true := by
  obtain ⟨a,b,c,d⟩ := c
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem four_not_cubic (c : Bits4) : ¬Low space4 3 (four c) := by
  intro h
  have s := (low_three_iff (s:=space4) _).mp h
  let dir : Fin 4→Bits4 := Fin.cases e0 (Fin.cases e1 (Fin.cases e2 (fun _=>e3)))
  have z := s dir zero4
  simp only [List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil] at z
  change diff space4 e3 (diff space4 e2 (diff space4 e1 (diff space4 e0 (four c)))) zero4 = false at z
  rw [mixed_four] at z
  contradiction

theorem product_not_cubic_if_full {V : Type} {s : AddSpace V} {chart : V→Bits4}
    (h : Hom s space4 chart) (surj : ∀ y, ∃ x, chart x=y) (c : Bits4) :
    ¬Low s 3 (fun x=>four c (chart x)) :=
  fun degree => four_not_cubic c (low_descend h surj degree)

def inner (a x : Bits4) : Bool :=
  (((a.1 && x.1) ^^ (a.2.1 && x.2.1)) ^^ (a.2.2.1 && x.2.2.1)) ^^ (a.2.2.2 && x.2.2.2)

def all4 (x : Bits4) : Bool := x.1 && x.2.1 && x.2.2.1 && x.2.2.2

theorem four_eq (c x : Bits4) : four c x = all4 (add4 x c) := rfl

theorem inner_add (a x y : Bits4) :
    inner a (add4 x y) = (inner a x ^^ inner a y) := by
  have dis (a b c : Bool) : (a && (b ^^ c))=((a && b) ^^ (a && c)) := by
    cases a <;> cases b <;> cases c <;> rfl
  simp only [add4,inner,dis]
  rw [Bool.xor_assoc] 
  -- Associativity and commutativity move all x terms before all y terms.
  simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

def skip (j : Fin 4) (x : Bits4) : Bool :=
  if j.val=0 then x.2.1 && x.2.2.1 && x.2.2.2
  else if j.val=1 then x.1 && x.2.2.1 && x.2.2.2
  else if j.val=2 then x.1 && x.2.1 && x.2.2.2
  else x.1 && x.2.1 && x.2.2.1

def coeff (a : Bits4) (j : Fin 4) : Bool :=
  if j.val=0 then a.1 else if j.val=1 then a.2.1 else if j.val=2 then a.2.2.1 else a.2.2.2

theorem finite_pivot {a x : Bits4} (j : Fin 4) (hj : coeff a j=true) :
    all4 x = ((!(inner a x ^^ inner a (true,true,true,true))) && skip j x) := by
  have H : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by have := j.isLt; omega
  rcases a with ⟨a,b,c,d⟩
  rcases x with ⟨e,f,g,h⟩
  rcases H with w|w|w|w <;>
    cases e <;> cases f <;> cases g <;> cases h <;>
    simp_all [coeff,skip,all4,inner,w,Bool.xor_assoc,Bool.xor_left_comm]

theorem product_cubic_if_relation {V : Type} {s : AddSpace V} {X : V→Bits4}
    (h1 : Low s 1 (fun x=>(X x).1)) (h2 : Low s 1 (fun x=>(X x).2.1))
    (h3 : Low s 1 (fun x=>(X x).2.2.1)) (h4 : Low s 1 (fun x=>(X x).2.2.2))
    {a : Bits4} (j : Fin 4) (hj : coeff a j=true) (c : Bool) (relation : ∀ x, inner a (X x)=c) :
    Low s 3 (fun x=>all4 (X x)) := by
  let d := !(c ^^ inner a (true,true,true,true))
  have point : (fun x=>all4 (X x))=(fun x=>d && skip j (X x)) := by
    funext x
    rw [finite_pivot j hj,relation x]
  rw [point]
  have hS : Low s 3 (fun x=>skip j (X x)) := by
    have H : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by have := j.isLt; omega
    rcases H with w|w|w|w
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h2 h3) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h3) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h2) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h2) h3
  exact low_prod 0 3 (low_const _ d) hS

end PNP29946.Binary

namespace PNP29946.Binary
abbrev Zero {k : Nat} : Word k := fun _=>false

def head {k : Nat} (x : Word (k+1)) := x 0
def tail {k : Nat} (x : Word (k+1)) : Word k := fun i=>x i.succ
def cons {k : Nat} (b : Bool) (x : Word k) : Word (k+1) := Fin.cases b x

@[simp] theorem head_cons {k : Nat} (b : Bool) (x : Word k) : head (cons b x)=b := rfl
@[simp] theorem tail_cons {k : Nat} (b : Bool) (x : Word k) : tail (cons b x)=x := rfl
@[simp] theorem cons_head_tail {k : Nat} (x : Word (k+1)) : cons (head x) (tail x)=x := by
  funext i
  refine Fin.cases ?_ (fun _=>?_) i <;> rfl

@[simp] theorem cons_zero {k : Nat} : cons false (Zero : Word k) = Zero := by
  funext i
  refine Fin.cases ?_ (fun _=>?_) i <;> rfl

@[simp] theorem add_head {k : Nat} (x y : Word (k+1)) :
    head (wireAdd x y) = (head x ^^ head y) := rfl
@[simp] theorem add_tail {k : Nat} (x y : Word (k+1)) :
    tail (wireAdd x y) = wireAdd (tail x) (tail y) := rfl
@[simp] theorem add_cons {k : Nat} (a b : Bool) (x y : Word k) :
    wireAdd (cons a x) (cons b y) = cons (a ^^ b) (wireAdd x y) := by
  funext i
  refine Fin.cases ?_ (fun _=>?_) i <;> rfl

theorem add_cancel {k : Nat} (x y : Word k) : wireAdd (wireAdd x y) y=x := by
  funext j
  change ((x j ^^ y j) ^^ y j)=x j
  cases x j <;> cases y j <;> decide

def dot : (k : Nat) → Word k → Word k → Bool
  | 0,_,_ => false
  | k+1,x,y => (head x && head y) ^^ dot k (tail x) (tail y)

@[simp] theorem dot_cons {k : Nat} (a b : Bool) (x y : Word k) :
    dot (k+1) (cons a x) (cons b y)=((a&&b) ^^ dot k x y) := rfl

@[simp] theorem dot_zero {k : Nat} (x : Word k) : dot k Zero x = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (false ^^ dot k Zero (tail x))=false
    rw [ih]
    rfl

theorem dot_add {k : Nat} (a x y : Word k) :
    dot k a (wireAdd x y)=(dot k a x ^^ dot k a y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (head a && (head x ^^ head y) ^^ dot k (tail a) (wireAdd (tail x) (tail y))) =
      (((head a && head x) ^^ dot k (tail a) (tail x)) ^^ ((head a && head y) ^^ dot k (tail a) (tail y)))
    rw [ih]
    generalize head a=u
    generalize head x=v
    generalize head y=w
    generalize dot k (tail a) (tail x)=p
    generalize dot k (tail a) (tail y)=q
    cases u <;> cases v <;> cases w <;> cases p <;> cases q <;> decide

theorem dot_sym {k : Nat} (x y : Word k) : dot k x y=dot k y x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((head x && head y) ^^ dot k (tail x) (tail y)) =
      ((head y && head x) ^^ dot k (tail y) (tail x))
    rw [ih,Bool.and_comm]

structure SubBits (k : Nat) where
  carries : Word k → Prop
  zero_in : carries Zero
  closed_add : ∀ x y, carries x → carries y → carries (wireAdd x y)

def zeroSlice {k : Nat} (H : SubBits (k+1)) : SubBits k :=
  ⟨fun x=>H.carries (cons false x), by simpa using H.zero_in,
    fun x y hx hy=>by simpa only [add_cons,Bool.false_xor] using H.closed_add _ _ hx hy⟩

def clean {k : Nat} (u x : Word (k+1)) : Word (k+1) :=
  if head x then wireAdd x u else x

theorem clean_head {k : Nat} {u : Word (k+1)} (h : head u=true) (x : Word (k+1)) :
    head (clean u x)=false := by
  unfold clean
  split
  · rename_i q
    simp [h,q]
  · rename_i q
    exact Bool.eq_false_iff.mpr q

theorem zero_cons_eq {k : Nat} {x : Word (k+1)} (h : head x=false) :
    cons false (tail x)=x := by rw [←h,cons_head_tail]

theorem clean_in {k : Nat} (H : SubBits (k+1)) {u : Word (k+1)}
    (hs : H.carries u) (x : Word (k+1)) :
    H.carries (clean u x) ↔ H.carries x := by
  unfold clean
  split
  · constructor
    · intro ha
      have h := H.closed_add _ _ ha hs
      rw [add_cancel] at h
      exact h
    · intro ha; exact H.closed_add _ _ ha hs
  · rfl

theorem clean_pair {k : Nat} (u x : Word (k+1)) (v : Word k) :
    dot (k+1) (cons (dot k v (tail u)) v) x = dot k v (tail (clean u x)) := by
  change ((dot k v (tail u) && head x) ^^ dot k v (tail x)) =
    dot k v (tail (clean u x))
  unfold clean
  split
  · rename_i h
    rw [h,add_tail,dot_add,Bool.and_true,Bool.xor_comm]
  · rename_i h
    rw [Bool.eq_false_iff.mpr h]
    simp

theorem separator (k : Nat) (H : SubBits k) (x : Word k) (hx : ¬H.carries x) :
    ∃ u, dot k u x=true ∧ ∀ y, H.carries y → dot k u y=false := by
  induction k with
  | zero =>
    have e : x=Zero := by funext i; exact Fin.elim0 i
    exact False.elim (hx (e.symm ▸ H.zero_in))
  | succ k ih =>
    by_cases some : ∃ u, H.carries u ∧ head u=true
    · obtain ⟨u,hu,he⟩ := some
      have bad : ¬(zeroSlice H).carries (tail (clean u x)) := by
        intro h
        change H.carries (cons false (tail (clean u x))) at h
        rw [zero_cons_eq (clean_head he x)] at h
        exact hx ((clean_in H hu x).mp h)
      obtain ⟨v,vx,vh⟩ := ih (zeroSlice H) _ bad
      refine ⟨cons (dot k v (tail u)) v,?_,?_⟩
      · rw [clean_pair]
        exact vx
      · intro y hy
        rw [clean_pair]
        apply vh
        change H.carries (cons false (tail (clean u y)))
        rw [zero_cons_eq (clean_head he y)]
        exact (clean_in H hu y).mpr hy
    · have zero : ∀ y, H.carries y → head y=false :=
          fun y hy=>Bool.eq_false_iff.mpr (fun e=>some ⟨y,hy,e⟩)
      by_cases bit : head x=true
      · refine ⟨cons true Zero,?_,?_⟩
        · change ((true && head x) ^^ dot k Zero (tail x))=true
          simp [bit]
        · intro y hy
          change ((true && head y) ^^ dot k Zero (tail y))=false
          simp [zero y hy]
      · have hxoff : head x=false := Bool.eq_false_iff.mpr bit
        have bad : ¬(zeroSlice H).carries (tail x) := by
          intro h
          change H.carries (cons false (tail x)) at h
          rw [zero_cons_eq hxoff] at h
          exact hx h
        obtain ⟨v,vx,vh⟩ := ih (zeroSlice H) _ bad
        refine ⟨cons false v,?_,?_⟩
        · change ((false && head x) ^^ dot k v (tail x))=true
          simpa using vx
        · intro y hy
          change ((false && head y) ^^ dot k v (tail y))=false
          simp only [Bool.false_and,Bool.false_xor]
          apply vh
          change H.carries (cons false (tail y))
          rwa [zero_cons_eq (zero y hy)]

theorem double_ortho {k : Nat} (H : SubBits k) (x : Word k) :
    H.carries x ↔ ∀ u, (∀ y, H.carries y → dot k u y=false) → dot k u x=false := by
  constructor
  · exact fun p _ h=>h _ p
  · intro h
    classical
    by_cases mem : H.carries x
    · exact mem
    · obtain ⟨u,ux,q⟩ := separator k H x mem
      have b := h u q
      rw [ux] at b
      contradiction

end PNP29946.Binary

namespace PNP29946.Binary

theorem wire_add_zero {k : Nat} (x : Word k) : wireAdd x Zero=x := by
  funext i
  change (x i ^^ false)=x i
  simp

theorem wire_zero_add {k : Nat} (x : Word k) : wireAdd Zero x=x := by
  funext i
  change (false ^^ x i)=x i
  simp

theorem wire_self {k : Nat} (x : Word k) : wireAdd x x=Zero := by
  funext i
  change (x i ^^ x i)=false
  simp

theorem wire_cut1 {k : Nat} (x y a : Word k) :
    wireAdd (wireAdd x y) a = wireAdd (wireAdd x a) y := by
  exact (wireSpace k).commute x y a

theorem wire_cut2 {k : Nat} (x y a : Word k) :
    wireAdd (wireAdd x y) a = wireAdd x (wireAdd y a) := by
  funext i
  change ((x i ^^ y i) ^^ a i) = (x i ^^ (y i ^^ a i))
  rw [Bool.xor_assoc]

theorem wire_cut3 {k : Nat} (x y a : Word k) :
    wireAdd (wireAdd x a) (wireAdd y a)=wireAdd x y := by
  rw [←wire_cut2,wire_cut1 x a y,wire_cut2 (wireAdd x y) a a,wire_self,wire_add_zero]

def InSpan {k : Nat} : List (Word k) → Word k → Prop
  | [],x => x=Zero
  | a::as,x => InSpan as x ∨ InSpan as (wireAdd x a)

theorem span_zero {k : Nat} (L : List (Word k)) : InSpan L Zero := by
  induction L with
  | nil => rfl
  | cons a as ih => exact Or.inl ih

theorem span_gen {k : Nat} (L : List (Word k)) {x : Word k} (hx : x∈L) :
    InSpan L x := by
  induction L with
  | nil => simp at hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · apply Or.inr
      rw [wire_self]
      exact span_zero as
    · exact Or.inl (ih hx)

theorem span_add {k : Nat} (L : List (Word k)) (x y : Word k)
    (hx : InSpan L x) (hy : InSpan L y) : InSpan L (wireAdd x y) := by
  induction L generalizing x y with
  | nil =>
    change x=Zero at hx
    change y=Zero at hy
    change wireAdd x y=Zero
    rw [hx,hy,wire_add_zero]
  | cons a as ih =>
    rcases hx with ha|ha <;> rcases hy with hb|hb
    · exact Or.inl (ih _ _ ha hb)
    · exact Or.inr ((wire_cut2 x y a).symm ▸ ih _ _ ha hb)
    · exact Or.inr ((wire_cut1 x y a).symm ▸ ih _ _ ha hb)
    · exact Or.inl (wire_cut3 x y a ▸ ih _ _ ha hb)

def span {k : Nat} (L : List (Word k)) : SubBits k :=
  ⟨InSpan L,span_zero L,span_add L⟩

def Null {k : Nat} (L : List (Word k)) (u : Word k) :=
  ∀ z∈L, dot k u z=false

theorem span_null {k : Nat} (L : List (Word k)) {u x : Word k}
    (h : Null L u) (p : InSpan L x) : dot k u x=false := by
  induction L generalizing x with
  | nil =>
    change x=Zero at p
    rw [p,dot_sym,dot_zero]
  | cons a l ih =>
    have old : Null l u := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rcases p with p|p
    · exact ih old p
    · have y := ih old p
      rw [dot_add,h a List.mem_cons_self,Bool.xor_false] at y
      exact y

theorem span_iff_test {k : Nat} (L : List (Word k)) (x : Word k) :
    InSpan L x ↔ ∀ u, Null L u → dot k u x=false := by
  constructor
  · intro p u h; exact span_null L h p
  · intro h
    apply (double_ortho (span L) x).mpr
    intro u hu
    apply h u
    intro a ha
    exact hu a (span_gen L ha)

def nullSpace {k : Nat} {L : List (Word k)} : AddSpace {x : Word k // Null L x} where
  add x y := ⟨wireAdd x.val y.val,fun z hz => by
    rw [dot_sym,dot_add, dot_sym z x.val,dot_sym z y.val,x.property z hz,y.property z hz]
    rfl⟩
  origin := ⟨Zero,fun z _ => dot_zero z⟩
  commute := by intro x a b; exact Subtype.ext ((wireSpace k).commute x.val a.val b.val)
  reach := by
    intro x y
    have c : Null L (wireAdd x.val y.val) := by
      intro z hz
      rw [dot_sym,dot_add, dot_sym z x.val,dot_sym z y.val,x.property z hz,y.property z hz]
      rfl
    refine ⟨⟨wireAdd x.val y.val,c⟩,Subtype.ext ?_⟩
    funext j
    change (x.val j ^^ (x.val j ^^ y.val j))=y.val j
    cases x.val j <;> cases y.val j <;> decide

def fourWord (x : Bits4) : Word 4 :=
  cons x.1 (cons x.2.1 (cons x.2.2.1 (cons x.2.2.2 Zero)))

def wordFour (x : Word 4) : Bits4 := (head x,head (tail x),head (tail (tail x)),head (tail (tail (tail x))))

theorem four_round (x : Bits4) : wordFour (fourWord x)=x := by
  rcases x with ⟨a,b,c,d⟩
  rfl

theorem word_round (x : Word 4) : fourWord (wordFour x)=x := by
  unfold fourWord wordFour
  have h : tail (tail (tail (tail x)))=Zero := by funext p; exact Fin.elim0 p
  rw [←h]
  repeat rw [cons_head_tail]

theorem word_add_four (x y : Bits4) : fourWord (add4 x y)=wireAdd (fourWord x) (fourWord y) := by
  simp only [fourWord,add4,add_cons]
  congr 4

theorem inner_dot (a x : Bits4) : dot 4 (fourWord a) (fourWord x)=inner a x := by
  simp only [fourWord,dot,inner,head_cons,tail_cons,Bool.xor_false,Bool.xor_assoc]

theorem nonzero_coeff (a : Bits4) (h : a≠zero4) : ∃ j, coeff a j=true := by
  rcases a with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp only [zero4,ne_eq,Prod.mk.injEq] at h
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact False.elim (h True.intro)

theorem chart_separator {V : Type} {s : AddSpace V} {chart : V→Bits4}
    (h : Hom s space4 chart) (zero : chart s.origin=zero4)
    (nonsurj : ¬∀ b, ∃ x, chart x=b) :
    ∃ a j, coeff a j=true ∧ ∀ x, inner a (chart x)=false := by
  let H : SubBits 4 := ⟨fun b=>∃ x, fourWord (chart x)=b,
      ⟨s.origin,by rw [zero]; simp [fourWord,zero4]⟩,
      fun a b ⟨x,hx⟩ ⟨y,hy⟩ => ⟨s.add x y, by
        rw [h]
        change fourWord (add4 (chart x) (chart y))=wireAdd a b
        rw [word_add_four,hx,hy]⟩⟩
  classical
  have notAll : ¬∀ b : Bits4, H.carries (fourWord b) := by
    intro z
    apply nonsurj
    intro b
    obtain ⟨x,hx⟩ := z b
    exact ⟨x,by simpa only [four_round] using congrArg wordFour hx⟩
  have existsBad : ∃ b : Bits4, ¬H.carries (fourWord b) := Classical.not_forall.mp notAll
  obtain ⟨b,hb⟩ := existsBad
  obtain ⟨v,hit,skip⟩ := separator 4 H (fourWord b) hb
  let a := wordFour v
  have eq : fourWord a=v := word_round v
  have nz : a≠zero4 := by
    intro a0
    have vz : v=Zero := by rw [←eq,a0]; simp [fourWord,zero4]
    rw [vz,dot_zero] at hit
    contradiction
  obtain ⟨j,w⟩ := nonzero_coeff a nz
  refine ⟨a,j,w,?_⟩
  intro x
  rw [←inner_dot,eq]
  exact skip _ ⟨x,rfl⟩

end PNP29946.Binary

namespace PNP29946.Binary
abbrev Forms4 (k : Nat) := Word k × Word k × Word k × Word k

def chart {k : Nat} (f : Forms4 k) (x : Word k) : Bits4 :=
  ⟨dot k x f.1,dot k x f.2.1,dot k x f.2.2.1,dot k x f.2.2.2⟩

def scaled {k : Nat} (c : Bool) (x : Word k) := if c then x else Zero

def combine {k : Nat} (a : Bits4) (f : Forms4 k) : Word k :=
  wireAdd (wireAdd (wireAdd (scaled a.1 f.1) (scaled a.2.1 f.2.1))
    (scaled a.2.2.1 f.2.2.1)) (scaled a.2.2.2 f.2.2.2)

theorem dot_scaled {k : Nat} (c : Bool) (x y : Word k) :
    dot k x (scaled c y)=(c && dot k x y) := by
  cases c
  · change dot k x Zero=(false&&dot k x y)
    rw [dot_sym,dot_zero]
    rfl
  · rfl

theorem chart_pair {k : Nat} (a : Bits4) (f : Forms4 k) (x : Word k) :
    inner a (chart f x)=dot k x (combine a f) := by simp only [inner,chart,combine,dot_add,dot_scaled]

theorem dot_left_add {k : Nat} (x y z : Word k) :
    dot k (wireAdd x y) z=(dot k x z ^^ dot k y z) := by
  rw [dot_sym, dot_add, dot_sym z x, dot_sym z y]

theorem chart_hom {k : Nat} (f : Forms4 k) :
    Hom (wireSpace k) space4 (chart f) := by
  intro x y
  change chart f (wireAdd x y)=add4 (chart f x) (chart f y)
  simp only [chart,add4,dot_left_add]

theorem chart_zero {k : Nat} (f : Forms4 k) : (chart f) Zero=zero4 := by
  simp only [chart,zero4,dot_zero]

def path {k d : Nat} (ask : Fin d→Nat→Word k) : List (Word k) := List.ofFn (fun j=>ask j 0)

def run {k d : Nat} (ask : Fin d→Nat→Word k) (x : Word k) : Nat :=
  (List.ofFn (fun j : Fin d=>j)).foldl
    (fun h j => 2*h+(if dot k x (ask j h) then 1 else 0)) 0

private theorem fold_zero {k d : Nat} {ask : Fin d→Nat→Word k} {x : Word k}
    (zero : ∀ j, dot k x (ask j 0)=false) (L : List (Fin d)) :
    L.foldl (fun h j => 2*h+(if dot k x (ask j h) then 1 else 0)) 0=0 := by
  induction L with
  | nil => rfl
  | cons j js ih =>
    change js.foldl (fun h j => 2*h+(if dot k x (ask j h) then 1 else 0))
      (2*0+(if dot k x (ask j 0) then 1 else 0))=0
    rw [zero j]
    exact ih

theorem run_zero {k d : Nat} (ask : Fin d→Nat→Word k) (x : Word k)
    (n : Null (path ask) x) : run ask x=0 := by
  exact fold_zero (fun j=>n (ask j 0) (List.mem_ofFn.mpr ⟨j,rfl⟩)) _

theorem rel_from_restricted_product {k : Nat} {Q : List (Word k)} (f : Forms4 k) (offset : Bits4)
    (degree : Low (nullSpace (L:=Q)) 3 (fun x=>four offset (chart f x.val))) :
    ∃ a j, coeff a j=true ∧ InSpan Q (combine a f) := by
  let proj : {x : Word k // Null Q x}→Bits4 := fun x=>chart f x.val
  have lin : Hom nullSpace space4 proj := fun x y=>chart_hom f x.val y.val
  have h0 : proj (nullSpace (L:=Q)).origin=zero4 := chart_zero f
  have notsurj : ¬∀ b, ∃ x, proj x=b := fun h =>
    product_not_cubic_if_full lin h offset degree
  obtain ⟨a,j,hj,hn⟩ := chart_separator lin h0 notsurj
  refine ⟨a,j,hj,(span_iff_test Q _).mpr ?_⟩
  intro u hu
  rw [←chart_pair]
  exact hn ⟨u,hu⟩

/-- An adaptive strategy is already constrained by its all-zero transcript.
    One witness vector per row must be in that transcript's fixed query span. -/
theorem adaptive_row_hit {k d : Nat} (ask : Fin d→Nat→Word k) (readout : Nat→Word k→Bool)
    (out : Word k→Bool) (f : Forms4 k) (offset : Bits4)
    (degree : ∀ h, Low (wireSpace k) 3 (readout h))
    (correct : ∀ x, out x = readout (run ask x) x)
    (error : Low (wireSpace k) 3 (xor out (fun x=>four offset (chart f x)))) :
    ∃ a j, coeff a j=true ∧ InSpan (path ask) (combine a f) := by
  let Q := path ask
  let lift : {x : Word k // Null Q x} → Word k := Subtype.val
  have hom : Hom (nullSpace (L:=Q)) (wireSpace k) lift := fun _ _=>rfl
  have fEq : (fun x=>out (lift x)) = (fun x=>readout 0 (lift x)) := by
    funext x
    exact (correct (lift x)).trans (by rw [run_zero ask _ x.property])
  have isLow : Low (nullSpace (L:=Q)) 3 (fun x=>out (lift x)) := by
    rw [fEq]
    exact low_pullback hom (degree 0)
  have diffLow : Low (nullSpace (L:=Q)) 3
       (xor (fun x=>out (lift x)) (fun x=>four offset (chart f (lift x)))) :=
    low_pullback hom error
  exact rel_from_restricted_product f offset ((common_low diffLow).mp isLow)

end PNP29946.Binary

namespace PNP29946.Binary
def appendBit (x : Nat) (t : Bool) := 2*x+(if t then 1 else 0)
def encode (L : List Bool) := L.foldl appendBit 0

def little : List Bool → Nat
  | [] => 0
  | b::L => appendBit (little L) b

theorem rev_encode (L : List Bool) : encode L.reverse=little L := by
  induction L with
  | nil => rfl
  | cons b as ih =>
    simp only [List.reverse_cons,encode,List.foldl_append,List.foldl_cons,List.foldl_nil,little]
    exact congrArg (appendBit · b) ih

theorem little_inj (L R : List Bool) (sz : L.length=R.length) (e : little L=little R) : L=R := by
  induction L generalizing R with
  | nil => exact (List.eq_nil_of_length_eq_zero (by simpa using sz.symm)).symm
  | cons b l ih =>
    cases R with
    | nil => simp at sz
    | cons c r =>
      have ar : appendBit (little l) b=appendBit (little r) c := e
      have se : little l=little r ∧ b=c := by
        cases b <;> cases c <;> simp [appendBit] at ar ⊢ <;> omega
      have len : l.length=r.length := by simpa only [List.length_cons,Nat.succ.injEq] using sz
      rw [se.2,ih r len se.1]

theorem encode_inj {L R : List Bool} (sz : L.length=R.length) (e : encode L=encode R) : L=R := by
  have q : little L.reverse=little R.reverse := by rw [←rev_encode,←rev_encode,List.reverse_reverse,List.reverse_reverse]; exact e
  have eq := little_inj _ _ (by simpa only [List.length_reverse] using sz) q
  simpa only [List.reverse_reverse] using congrArg List.reverse eq

def fixed {k d : Nat} (f : Fin d→Word k) : Fin d→Nat→Word k := fun j _=>f j

theorem fixed_run {k d : Nat} (q : Fin d→Word k) (x : Word k) :
    run (fixed q) x=encode ((List.ofFn q).map (dot k x)) := by
  simp only [run,fixed,encode, List.map_ofFn,Function.comp_def]
  have e : List.ofFn (fun i : Fin d => dot k x (q i)) =
        (List.ofFn (fun i : Fin d=>i)).map (fun i=>dot k x (q i)) := by rw [List.map_ofFn]; rfl
  rw [e,List.foldl_map]
  rfl

theorem fixed_answers {k d : Nat} (f : Fin d→Word k) {x y : Word k}
    (e : run (fixed f) x=run (fixed f) y) :
    ∀ j, dot k x (f j)=dot k y (f j) := by
  rw [fixed_run,fixed_run] at e
  have g := encode_inj (by simp) e
  simp only [List.map_ofFn] at g
  intro j
  have u : (((List.ofFn (fun i => dot k x (f i))).getD j.val false)) =
      (((List.ofFn (fun i => dot k y (f i))).getD j.val false)) := congrArg (fun l=>l.getD j.val false) g
  simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt] using u

theorem fixed_span_value {k d : Nat} (q : Fin d→Word k) {x y v : Word k}
    (e : run (fixed q) x=run (fixed q) y) (mem : InSpan (List.ofFn q) v) :
    dot k x v=dot k y v := by
  have n : Null (List.ofFn q) (wireAdd x y) := by
    intro z hz
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
    rw [dot_left_add,fixed_answers q e j,Bool.xor_self]
  have m := span_null (List.ofFn q) n mem
  rw [dot_left_add] at m
  generalize dot k x v=a at m ⊢
  generalize dot k y v=b at m ⊢
  cases a <;> cases b <;> simp_all

theorem low_pairing {k : Nat} (l : Word k) (c : Bool) :
    Low (wireSpace k) 1 (fun x=>dot k x l ^^ c) :=
  low_affine (fun x y=>dot_left_add x y l) c

def replaceTop {k : Nat} (f : Forms4 k) (offset a : Bits4) (j : Fin 4) (known : Bool) : Word k→Bool :=
  fun x => (!(known ^^ inner a (true,true,true,true))) && skip j (add4 (chart f x) offset)

theorem replaceLow {k : Nat} (f : Forms4 k) (offset a : Bits4) (j : Fin 4) (known : Bool) :
    Low (wireSpace k) 3 (replaceTop f offset a j known) := by
  let X := fun x=>add4 (chart f x) offset
  have h1 : Low (wireSpace k) 1 (fun x=>(X x).1) := low_pairing _ _
  have h2 : Low (wireSpace k) 1 (fun x=>(X x).2.1) := low_pairing _ _
  have h3 : Low (wireSpace k) 1 (fun x=>(X x).2.2.1) := low_pairing _ _
  have h4 : Low (wireSpace k) 1 (fun x=>(X x).2.2.2) := low_pairing _ _
  have hS : Low (wireSpace k) 3 (fun x=>skip j (X x)) := by
    have H : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by have := j.isLt; omega
    rcases H with w|w|w|w
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h2 h3) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h3) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h2) h4
    · simp [skip,w]; exact low_prod 2 1 (low_prod 1 1 h1 h2) h3
  exact low_prod 0 3 (low_const _ _) hS

theorem replaceMatches {k : Nat} (f : Forms4 k) (offset a : Bits4) (j : Fin 4)
    (hit : coeff a j=true) (x : Word k) (known : Bool) (h : inner a (add4 (chart f x) offset)=known) :
    four offset (chart f x)=replaceTop f offset a j known x := by
  rw [four_eq,finite_pivot j hit,h]
  rfl

theorem nonadaptive_readout {k d : Nat} (q : Fin d→Word k)
    (o : Word k→Bool) (f : Forms4 k) (offset : Bits4)
    (error : Low (wireSpace k) 3 (xor o (fun x=>four offset (chart f x))))
    (hit : ∃ a j, coeff a j=true ∧ InSpan (List.ofFn q) (combine a f)) :
    ∃ readout : Nat→Word k→Bool, (∀ h, Low (wireSpace k) 3 (readout h)) ∧
      ∀ x, o x=readout (run (fixed q) x) x := by
  obtain ⟨a,j,hj,hs⟩ := hit
  classical
  let E := xor o (fun x=>four offset (chart f x))
  let K : Word k→Bool := fun x=>inner a (add4 (chart f x) offset)
  let R : Nat→Word k→Bool := fun h =>
    if yes : ∃ x, run (fixed q) x=h then xor E (replaceTop f offset a j (K (Classical.choose yes)))
    else fun _=>false
  refine ⟨R,?_ ,?_⟩
  · intro h
    unfold R
    split
    · exact low_xor error (replaceLow _ _ _ _ _)
    · exact low_const _ false
  · intro x
    unfold R
    let yes : ∃ y, run (fixed q) y=run (fixed q) x := ⟨x,rfl⟩
    rw [dite_eq_left yes]
    let y := Classical.choose yes
    have he : run (fixed q) y=run (fixed q) x := Classical.choose_spec yes
    have hk : K x=K y := by
      simp only [K,inner_add,chart_pair]
      rw [fixed_span_value q he.symm hs]
    change o x = (E x ^^ replaceTop f offset a j (K y) x)
    rw [← replaceMatches f offset a j hj x _ hk]
    change o x = ((o x ^^ four offset (chart f x)) ^^ four offset (chart f x))
    cases o x <;> cases four offset (chart f x) <;> decide

end PNP29946.Binary

namespace PNP29946.Binary

def unit {k : Nat} (i : Fin k) : Word k := fun j=>j==i

theorem unit_dot {k : Nat} (i : Fin k) (x : Word k) : dot k x (unit i)=x i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) i
    · have z : tail (unit (0:Fin (k+1)))=Zero := by
        funext p
        change (p.succ==0)=false
        apply beq_eq_false_iff_ne.mpr
        intro H
        have Hx := congrArg Fin.val H
        simp only [Fin.val_succ,Fin.val_zero] at Hx
        omega
      have e : head (unit (0:Fin (k+1)))=true := by simp [head,unit]
      change ((head x && head (unit (0:Fin (k+1)))) ^^
        dot k (tail x) (tail (unit (0:Fin (k+1)))))=x 0
      rw [z,e,dot_sym,dot_zero]
      simp [head]
    · have eqb : tail (unit j.succ)=unit j := by
        funext p
        change (p.succ==j.succ)=(p==j)
        by_cases eq : p=j
        · simp [eq]
        · have ne : p.succ≠j.succ := by simpa using eq
          exact (beq_eq_false_iff_ne.mpr ne).trans ((beq_eq_false_iff_ne.mpr eq).symm)
      have f : head (unit j.succ)=false := by
        change ((0:Fin (k+1))==j.succ)=false
        apply beq_eq_false_iff_ne.mpr
        intro H
        have Hx := congrArg Fin.val H
        simp only [Fin.val_succ,Fin.val_zero] at Hx
        omega
      change ((head x && head (unit j.succ)) ^^ dot k (tail x) (tail (unit j.succ)))=x j.succ
      rw [f,eqb,ih]
      simp [tail]

def zC {k : Nat} (h : 0<k) (i : Fin k) : Word k :=
  let e := fun j : Fin k => unit (idx h (j.val+k-1 % k))
  wireAdd (wireAdd (e i) (e (fwd h i 1))) (e (back h i))

def zN {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :=
  mix h p.name i

theorem z_affine_pair {k : Nat} (h : 0<k) (p : Params k) (x : Word k) (i : Fin k) :
    zz h p x i = (dot k x (zC h i) ^^ zN h p i) := by
  simp only [zz,zN,mix,wireAdd,zC,dot_add,unit_dot,rot]
  rw [Bool.xor_assoc]
  simp only [Bool.xor_assoc,Bool.xor_left_comm]

def rowForm {k : Nat} (h : 0<k) (i : Fin k) : Forms4 k :=
  let r := fun t => zC h (fwd h i t)
  (r 2,r 4,wireAdd (r 1) (r 3),wireAdd (r 3) (r 5))

def rowOffset {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) : Bits4 :=
  let r := fun t => zN h p (fwd h i t)
  (r 2,r 4,r 1 ^^ r 3,r 3 ^^ r 5)

theorem pair_effect {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    top (atZ h p i 1) (atZ h p i 2) (atZ h p i 3) (atZ h p i 4) (atZ h p i 5)
      = fun x=>four (rowOffset h p i) (chart (rowForm h i) x) := by
  funext x
  simp only [top,four,prod,xor,atZ,rowOffset,chart,rowForm,dot_add,z_affine_pair]
  simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.and_assoc]

theorem actual_error {k : Nat} (h : 0<k) (p : Params k) (i : Fin k) :
    Low (wireSpace k) 3 (xor (fun x=>outFalse h p x i)
      (fun x=>four (rowOffset h p i) (chart (rowForm h i) x))) := by
  rw [←pair_effect,full_split]
  apply row_error
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_z h p _
  · exact low_xor (low_const _ _) (low_ma h p _)
  · exact low_ma h p _
  · exact low_xor (low_xor (low_m h p _) (low_succ (coordinate _))) (low_const _ _)

theorem actual_row_hit {k d : Nat} (h : 0<k) (p : Params k)
    (ask : Fin d→Nat→Word k) (readout : Nat→Fin k→Word k→Bool)
    (selected : Fin k→Bool) (degree : ∀ a i, Low (wireSpace k) 3 (readout a i))
    (correct : ∀ x i, selected i=true → outFalse h p x i=readout (run ask x) i x) :
    ∀ i, selected i=true → ∃ a j, coeff a j=true ∧ InSpan (path ask) (combine a (rowForm h i)) := by
  intro i hi
  exact adaptive_row_hit ask (fun a=>readout a i) (fun x=>outFalse h p x i)
    (rowForm h i) (rowOffset h p i) (fun a=>degree a i) (fun x=>correct x i hi)
    (actual_error h p i)

end PNP29946.Binary

namespace PNP29946.Binary
def Fits {k : Nat} (h : 0<k) (p : Params k) (marked : Fin k→Bool) (d : Nat) : Prop :=
  ∃ (ask : Fin d→Nat→Word k) (read : Nat→Fin k→Word k→Bool),
    (∀ a i, Low (wireSpace k) 3 (read a i)) ∧
    ∀ x i, marked i=true → outFalse h p x i = read (run ask x) i x

def AllHits {k : Nat} (h : 0<k) (marked : Fin k→Bool) (Q : List (Word k)) : Prop :=
  ∀ i, marked i=true → ∃ a j, coeff a j=true ∧ InSpan Q (combine a (rowForm h i))

theorem fits_iff_hits {k : Nat} (h : 0<k) (p : Params k) (marked : Fin k→Bool) (d : Nat) :
    Fits h p marked d ↔ ∃ qs : Fin d→Word k, AllHits h marked (List.ofFn qs) := by
  constructor
  · rintro ⟨ask,read,lo,eq⟩
    exact ⟨fun j=>ask j 0,actual_row_hit h p ask read marked lo eq⟩
  · rintro ⟨q,H⟩
    classical
    have existence (i : Fin k) (mem : marked i=true) :
        ∃ r : Nat→Word k→Bool, (∀ a, Low (wireSpace k) 3 (r a)) ∧
          ∀ x, outFalse h p x i=r (run (fixed q) x) x :=
      nonadaptive_readout q (fun x=>outFalse h p x i) (rowForm h i) (rowOffset h p i)
        (actual_error h p i) (H i mem)
    let read : Nat→Fin k→Word k→Bool := fun a i =>
      if mem : marked i=true then Classical.choose (existence i mem) a else fun _ => false
    refine ⟨fixed q,read,?_ ,?_⟩
    · intro a i
      unfold read
      split
      · exact (Classical.choose_spec (existence i (by assumption))).1 a
      · exact low_const 3 false
    · intro x i mem
      unfold read
      rw [dite_eq_left mem]
      exact (Classical.choose_spec (existence i mem)).2 x

end PNP29946.Binary

namespace PNP29946.PeriodThree

def Rec (f : Nat→Bool) : Prop := ∀ n, ((f n ^^ f (n+1)) ^^ f (n+2)) = false
def Period (f : Nat→Bool) (k : Nat) : Prop := ∀ n, f (n+k)=f n

theorem step {f : Nat→Bool} (rec : Rec f) (n : Nat) :
    f (n+2)= (f n ^^ f (n+1)) := by
  have h := rec n
  cases h0:f n <;> cases h1:f (n+1) <;> cases h2:f (n+2) <;>
    simp_all

theorem period3 {f : Nat→Bool} (rec : Rec f) : Period f 3 := by
  intro n
  have a := step rec n
  have b := step rec (n+1)
  change f (n+3) = (f (n+1) ^^ f (n+2)) at b
  rw [b,a]
  cases h0:f n <;> cases h1:f (n+1) <;> decide

/-- A period-three sequence equals its first three entries on every index. -/
theorem mod3 {f : Nat→Bool} (h : Period f 3) (n : Nat) : f n=f (n % 3) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases b : n<3
    · rw [Nat.mod_eq_of_lt b]
    · have e : n-3+3=n := by omega
      have j := h (n-3)
      have i := ih (n-3) (by omega)
      rw [e] at j
      have m : (n-3) % 3=n % 3 := by omega
      exact j.trans (i.trans (congrArg f m))

private theorem common_base_zero {f : Nat→Bool} (h : Rec f)
    (e1 : f 0=f 1) (e2 : f 1=f 2) : ∀ n, f n=false := by
  have a := h 0
  change ((f 0 ^^ f 1) ^^ f 2)=false at a
  have v : f 0=false := by rw [←e2,←e1] at a; simpa using a
  intro n
  have j := mod3 (period3 h) n
  have w : n % 3=0 ∨ n % 3=1 ∨ n % 3=2 := by omega
  rcases w with w|w|w <;> rw [j,w] <;> simp [←e2,←e1,v]

theorem divides {f : Nat→Bool} (rec : Rec f) {k : Nat} (cyc : Period f k)
    (nonzero : ∃ n, f n=true) : 3 ∣ k := by
  have p := period3 rec
  have h0 := cyc 0
  have h1 := cyc 1
  rw [Nat.zero_add] at h0
  rw [mod3 p] at h0 h1
  have w : k % 3=0 ∨ k % 3=1 ∨ k % 3=2 := by omega
  rcases w with zero|one|two
  · exact Nat.dvd_of_mod_eq_zero zero
  · have z : (1+k) % 3=2 := by omega
    rw [one] at h0
    rw [z] at h1
    obtain ⟨n,hn⟩ := nonzero
    rw [common_base_zero rec h0.symm h1.symm n] at hn
    contradiction
  · have z : (1+k) % 3=0 := by omega
    rw [two] at h0
    rw [z] at h1
    obtain ⟨n,hn⟩ := nonzero
    rw [common_base_zero rec h1 (h0.trans h1).symm n] at hn
    contradiction

private theorem base_class {f : Nat→Bool} (rec : Rec f) (nonzero : ∃ n, f n=true) :
    ∃ r : Fin 3, (∀ j : Nat, j<3 → f j = !(j==r.val)) := by
  have h := step rec 0
  change f 2 = (f 0 ^^ f 1) at h
  cases e0 : f 0 <;> cases e1 : f 1 <;> simp only [e0,e1] at h
  · have W (j : Nat) : f j=false := by
      rw [mod3 (period3 rec)]
      have e : j % 3=0 ∨ j % 3=1 ∨ j % 3=2 := by omega
      rcases e with e|e|e <;> rw [e] <;> assumption
    obtain ⟨j,ej⟩ := nonzero
    rw [W j] at ej
    contradiction
  · refine ⟨0,?_⟩
    intro j hj
    have e : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases e with rfl|rfl|rfl <;> simp [e0,e1,h] <;> decide
  · refine ⟨1,?_⟩
    intro j hj
    have e : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases e with rfl|rfl|rfl <;> simp [e0,e1,h] <;> decide
  · refine ⟨2,?_⟩
    intro j hj
    have e : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases e with rfl|rfl|rfl <;> simp [e0,e1,h] <;> decide

theorem classify {f : Nat→Bool} (rec : Rec f) {k : Nat} (cyc : Period f k)
    (nonzero : ∃ n, f n=true) :
    3 ∣ k ∧ ∃ r : Fin 3, ∀ j, f j = !(j % 3==r.val) := by
  obtain ⟨r,h⟩ := base_class rec nonzero
  refine ⟨divides rec cyc nonzero,r,?_⟩
  intro j
  rw [mod3 (period3 rec)]
  exact h (j % 3) (by omega)

theorem exact {f : Nat→Bool} (k : Nat) :
    (Rec f ∧ Period f k) ↔ (∀ n, f n=false) ∨
       (3 ∣ k ∧ ∃ r : Fin 3, ∀ j, f j = !(j % 3==r.val)) := by
  constructor
  · intro ⟨h,g⟩
    by_cases q : ∃ n, f n=true
    · exact Or.inr (classify h g q)
    · exact Or.inl (fun j => Bool.eq_false_iff.mpr (fun c => q ⟨j,c⟩))
  · rintro (z|⟨h,r,z⟩)
    · exact ⟨fun n=>by simp [z],fun n=>by simp [z]⟩
    · constructor
      · intro n
        rw [z,z,z]
        have n1 : (n+1) % 3 = (n % 3+1) % 3 := by omega
        have n2 : (n+2) % 3 = (n % 3+2) % 3 := by omega
        rw [n1,n2]
        have x : n % 3=0 ∨ n % 3=1 ∨ n % 3=2 := by omega
        have y : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have := r.isLt; omega
        rcases x with x|x|x <;> rcases y with y|y|y <;> rw [x,y] <;> decide
      · intro n
        rw [z,z]
        have mod : k % 3=0 := Nat.mod_eq_zero_of_dvd h
        have f : (n+k) % 3=n % 3 := by omega
        rw [f]

end PNP29946.PeriodThree

namespace PNP29946.OrbitFour
open Binary (idx fwd fwd_fwd)

def separated {k : Nat} (h : 0<k) (P : Fin k→Bool) :=
  ∀ i, P i=true → P (fwd h i 1)=false ∧ P (fwd h i 2)=false ∧ P (fwd h i 3)=false

def orbit {k : Nat} (P : Fin k→Bool) :=
  4 ∣ k ∧ ∃ a : Fin 4, ∀ i, P i=true ↔ i.val % 4=a.val

theorem fwd_zero {k : Nat} (h : 0<k) (i : Fin k) : fwd h i 0=i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem fwd_full {k : Nat} (h : 0<k) (i : Fin k) : fwd h i k=i := by
  apply Fin.ext
  change (i.val+k) % k=i.val
  rw [Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

theorem exclude_next {k : Nat} (h : 0<k) {P : Fin k→Bool}
    (sep : separated h P) (i : Fin k) (hi : P i=true)
    (j : Nat) (j0 : 0<j) (j4 : j<4) :
    P (fwd h i j)=false := by
  obtain ⟨a,b,c⟩ := sep i hi
  have q : j=1 ∨ j=2 ∨ j=3 := by omega
  rcases q with rfl|rfl|rfl <;> assumption

def gap {k : Nat} (i j : Fin k) : Nat :=
  if i.val≤j.val then j.val-i.val else j.val+k-i.val

theorem gap_lt {k : Nat} (i j : Fin k) : gap i j<k := by
  have i0 := i.isLt; have j0 := j.isLt
  unfold gap
  split <;> omega

theorem gap_end {k : Nat} (h : 0<k) (i j : Fin k) :
    fwd h i (gap i j)=j := by
  apply Fin.ext
  change (i.val+gap i j) % k=j.val
  have i0 := i.isLt; have j0 := j.isLt
  unfold gap
  split
  · have e : i.val+(j.val-i.val)=j.val := by omega
    rw [e,Nat.mod_eq_of_lt j0]
  · have e : i.val+(j.val+k-i.val)=j.val+k := by omega
    rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt j0]

theorem gap_phase {k : Nat} (i j : Fin k) (hk : 4∣k) :
    gap i j % 4=0 ↔ i.val % 4=j.val % 4 := by
  have hk' := Nat.mod_eq_zero_of_dvd hk
  have il := i.isLt; have jl := j.isLt
  unfold gap
  split <;> omega

theorem closed_subset_forces_orbit {k : Nat} (h : 0<k) {P S : Fin k→Bool}
    (sep : separated h P) (sub : ∀ i, S i=true → P i=true)
    (next : ∀ i, S i=true → S (fwd h i 4)=true)
    (nonempty : ∃ i, S i=true) : orbit P := by
  obtain ⟨i,hi⟩ := nonempty
  have act (n : Nat) : S (fwd h i (4*n))=true := by
    induction n with
    | zero => simpa only [Nat.mul_zero,fwd_zero] using hi
    | succ n ih =>
      have z := next _ ih
      rw [fwd_fwd] at z
      exact z
  have four : 4∣k := by
    apply Nat.dvd_of_mod_eq_zero
    by_cases hn : k % 4=0
    · exact hn
    · have rpos : 0<k % 4 := by omega
      have rlt : k % 4<4 := by omega
      let a := fwd h i (4*(k/4))
      have A : S a=true := act _
      have e : fwd h a (k % 4)=i := by
        dsimp [a]
        rw [fwd_fwd]
        have ar : 4*(k/4)+k % 4=k := by omega
        rw [ar,fwd_full]
      have no := exclude_next h sep a (sub _ A) (k % 4) rpos rlt
      rw [e,sub _ hi] at no
      contradiction
  refine ⟨four,⟨i.val % 4,by omega⟩,?_⟩
  intro j
  have e := gap_end h i j
  have phase := gap_phase i j four
  constructor
  · intro hj
    let m := gap i j/4
    let r := gap i j % 4
    have mAct := sub _ (act m)
    have rem : fwd h (fwd h i (4*m)) r=j := by
      rw [fwd_fwd]
      have ar : 4*m+r=gap i j := by dsimp [m,r]; omega
      rw [ar,e]
    have rr : r=0 := by
      by_cases nz : r=0
      · exact nz
      · have np : 0<r := Nat.pos_of_ne_zero nz
        have lt : r<4 := by dsimp [r]; omega
        have qq := exclude_next h sep _ mAct r np lt
        rw [rem,hj] at qq
        contradiction
    exact (phase.mp rr).symm
  · intro hj
    have ph : gap i j % 4=0 := phase.mpr hj.symm
    have ar : 4*(gap i j/4)=gap i j := by omega
    have zz := act (gap i j/4)
    rw [ar,e] at zz
    exact sub _ zz

end PNP29946.OrbitFour

namespace PNP29946.Binary

def rIdx {k : Nat} (h : 0<k) (t : Nat) (i : Fin k) : Fin k := idx h (i.val+k-t)

theorem fwd_rIdx {k : Nat} (h : 0<k) (i : Fin k) (t : Nat) (ht : t<k) :
    fwd h (rIdx h t i) t=i := by
  apply Fin.ext
  change (((i.val+k-t) % k)+t) % k=i.val
  rw [Nat.mod_add_mod]
  have eq : i.val+k-t+t=i.val+k := by omega
  rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

theorem rIdx_fwd {k : Nat} (h : 0<k) (i : Fin k) (t : Nat) (ht : t<k) :
    rIdx h t (fwd h i t)=i := by
  apply Fin.ext
  change (((i.val+t) % k)+k-t) % k=i.val
  have e : (i.val+t) % k+k-t=(i.val+t) % k+(k-t) := by omega
  rw [e,Nat.mod_add_mod]
  have eq : i.val+t+(k-t)=i.val+k := by omega
  rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]

theorem fwd_eq_iff {k : Nat} (h : 0<k) (i j : Fin k) (t : Nat) (ht : t<k) :
    fwd h i t=j ↔ i=rIdx h t j := by
  constructor
  · intro eq
    have a := congrArg (rIdx h t) eq
    rw [rIdx_fwd h i t ht] at a
    exact a
  · intro eq
    rw [eq,fwd_rIdx h j t ht]

theorem two_back {k : Nat} (h : 0<k) (k3 : 2<k) (i : Fin k) :
    back h (back h i)=rIdx h 2 i := by
  apply (fwd_eq_iff h _ _ 2 k3).mp
  have e : fwd h (fwd h (back h (back h i)) 1) 1=fwd h (back h i) 1 := by
    rw [show fwd h (back h (back h i)) 1=back h i from fwd_rIdx h _ 1 (by omega)]
  rw [fwd_fwd] at e
  exact e.trans (fwd_rIdx h i 1 (by omega))

def adjoint {k : Nat} (h : 0<k) (v : Word k) : Word k :=
  fun j=>(v j ^^ v (fwd h j 1)) ^^ v (fwd h j 2)

theorem adjoint_zero {k : Nat} (h : 0<k) : adjoint h Zero=Zero := by
  funext i
  rfl

theorem adjoint_add {k : Nat} (h : 0<k) (a b : Word k) :
    adjoint h (wireAdd a b)=wireAdd (adjoint h a) (adjoint h b) := by
  funext i
  simp only [adjoint,wireAdd,Bool.xor_assoc,Bool.xor_left_comm]

theorem adjoint_unit {k : Nat} (h : 0<k) (k3 : 2<k) (i : Fin k) :
    adjoint h (unit i)=zC h i := by
  funext j
  have h1 : 1 % k=1 := Nat.mod_eq_of_lt (by omega)
  have e : idx h ((fwd h i 1).val+k-1)=i := rIdx_fwd h i 1 (by omega)
  have e2 : idx h ((back h i).val+k-1)=rIdx h 2 i := two_back h k3 i
  have a : ((fwd h j 1)==i)=(j==rIdx h 1 i) := by
    by_cases b : fwd h j 1=i
    · rw [beq_iff_eq.mpr b,beq_iff_eq.mpr ((fwd_eq_iff h j i 1 (by omega)).mp b)]
    · rw [beq_eq_false_iff_ne.mpr b,beq_eq_false_iff_ne.mpr
        (fun ne => b ((fwd_eq_iff h j i 1 (by omega)).mpr ne))]
  have b : ((fwd h j 2)==i)=(j==rIdx h 2 i) := by
    by_cases b : fwd h j 2=i
    · rw [beq_iff_eq.mpr b,beq_iff_eq.mpr ((fwd_eq_iff h j i 2 k3).mp b)]
    · rw [beq_eq_false_iff_ne.mpr b,beq_eq_false_iff_ne.mpr
        (fun ne => b ((fwd_eq_iff h j i 2 k3).mpr ne))]
  simp only [adjoint,unit,zC,wireAdd,h1,e,e2,a,b,rIdx]
  rw [Bool.xor_comm (j==i)]

def localForm {k : Nat} (h : 0<k) (i : Fin k) : Forms4 k :=
  let u := fun t=>unit (fwd h i t)
  (u 2,u 4,wireAdd (u 1) (u 3),wireAdd (u 3) (u 5))

theorem adjoint_local {k : Nat} (h : 0<k) (k3 : 2<k) (i : Fin k) (v : Bits4) :
    adjoint h (combine v (localForm h i)) = combine v (rowForm h i) := by
  have carry (b : Bool) (x : Word k) : adjoint h (scaled b x) = scaled b (adjoint h x) := by
    cases b
    · exact adjoint_zero h
    · rfl
  simp only [combine,adjoint_add,localForm,rowForm,carry,adjoint_unit h k3]

def periodic {k : Nat} (r : Fin 3) : Word k := fun i => !(i.val % 3==r.val)

theorem kernel_adjoint {k : Nat} (h : 0<k) (v : Word k) :
    adjoint h v=Zero ↔ v=Zero ∨ (3 ∣ k ∧ ∃ r, v=periodic r) := by
  let f : Nat→Bool := fun n=>v (idx h n)
  have roll (n t : Nat) : fwd h (idx h n) t = idx h (n+t) := by
    apply Fin.ext
    change ((n % k)+t) % k=(n+t) % k
    rw [Nat.mod_add_mod]
  have cyclic : PeriodThree.Period f k := by
    intro n
    have e : idx h (n+k)=idx h n := by
      apply Fin.ext
      exact Nat.add_mod_right _ _
    exact congrArg v e
  have edge (i : Fin k) : idx h i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  constructor
  · intro g
    have recurrent : PeriodThree.Rec f := by
      intro n
      have q := congrFun g (idx h n)
      simp only [adjoint,roll] at q
      exact q
    rcases (PeriodThree.exact k).mp ⟨recurrent,cyclic⟩ with z|⟨m,r,z⟩
    · exact Or.inl (funext (fun i=>by simpa only [f,edge] using z i.val))
    · exact Or.inr ⟨m,r,funext (fun i=>by simpa only [f,edge,periodic] using z i.val)⟩
  · intro r
    have recurrent : PeriodThree.Rec f := by
      apply ((PeriodThree.exact k).mpr ?_).1
      rcases r with z|⟨m,r,z⟩
      · exact Or.inl (fun n=>by simp [f,z])
      · refine Or.inr ⟨m,r,fun n=>?_⟩
        change v (idx h n)= _
        rw [z]
        simp only [periodic,idx,Nat.mod_mod_of_dvd n m]
    funext i
    have a := recurrent i.val
    simp only [f,←roll,edge] at a
    exact a

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

theorem fwd_parameter_inj {k : Nat} (h : 0<k) (i : Fin k) {a b : Nat}
    (ha : a<k) (hb : b<k) (e : fwd h i a=fwd h i b) : a=b := by
  let A : Fin k := ⟨a,ha⟩
  let B : Fin k := ⟨b,hb⟩
  have z : fwd h A i.val = fwd h B i.val := by
    apply Fin.ext
    change (a+i.val) % k=(b+i.val) % k
    have q := congrArg Fin.val e
    change (i.val+a) % k=(i.val+b) % k at q
    simpa only [Nat.add_comm] using q
  have p := congrArg (rIdx h i.val) z
  rw [rIdx_fwd h _ _ i.isLt,rIdx_fwd h _ _ i.isLt] at p
  exact congrArg Fin.val p

/-- Positive consecutive length-five windows of separated starts have only
one possible overlap: precisely their opposite endpoints, at gap four. -/
theorem overlap {k : Nat} (h : 0<k) (big : 9≤k) {P : Fin k→Bool}
    (sep : separated h P) {i j : Fin k} (hi : P i=true) (hj : P j=true) (neq : i≠j)
    {a b : Nat} (a1 : 1≤a) (a5 : a≤5) (b1 : 1≤b) (b5 : b≤5)
    (hit : fwd h i a=fwd h j b) :
    (a=5 ∧ b=1 ∧ fwd h i 4=j) ∨ (a=1 ∧ b=5 ∧ fwd h j 4=i) := by
  have larger {s t : Fin k} {u v : Nat} (su : v≤u) (tv : v<k)
      (z : fwd h s u=fwd h t v) : fwd h s (u-v)=t := by
    have e : fwd h (fwd h s (u-v)) v=fwd h t v := by
      rw [fwd_fwd, Nat.sub_add_cancel su]
      exact z
    have a := congrArg (rIdx h v) e
    rwa [rIdx_fwd h _ _ tv,rIdx_fwd h _ _ tv] at a
  by_cases q : a=b
  · subst b
    have eq : fwd h i (a-a)=j := larger (by omega) (by omega) hit
    rw [Nat.sub_self,fwd_zero h] at eq
    exact False.elim (neq eq)
  · by_cases more : b≤a
    · have dest : fwd h i (a-b)=j := larger more (by omega) hit
      have notSmall : ¬a-b<4 := by
        intro sm
        have bad := exclude_next h sep i hi (a-b) (by omega) sm
        rw [dest,hj] at bad
        contradiction
      refine Or.inl ⟨by omega,by omega,?_⟩
      have ee : a-b=4 := by omega
      rwa [ee] at dest
    · have dest : fwd h j (b-a)=i := larger (by omega) (by omega) hit.symm
      have notSmall : ¬b-a<4 := by
        intro sm
        have bad := exclude_next h sep j hj (b-a) (by omega) sm
        rw [dest,hi] at bad
        contradiction
      refine Or.inr ⟨by omega,by omega,?_⟩
      have ee : b-a=4 := by omega
      rwa [ee] at dest

def Local {k : Nat} (h : 0<k) (i : Fin k) (a : Bits4) : Word k :=
  combine a (localForm h i)

def localVal (a : Bits4) (t : Nat) : Bool :=
  if t=1 then a.2.2.1 else if t=2 then a.1 else if t=3 then (a.2.2.1 ^^ a.2.2.2)
  else if t=4 then a.2.1 else if t=5 then a.2.2.2 else false

theorem unit_at {k : Nat} {i j : Fin k} (h : j=i) : unit i j=true :=
  beq_iff_eq.mpr h
theorem unit_off {k : Nat} {i j : Fin k} (h : j≠i) : unit i j=false :=
  beq_eq_false_iff_ne.mpr h

theorem scaled_apply {k : Nat} (c : Bool) (v : Word k) (j : Fin k) :
    scaled c v j=(c && v j) := by cases c <;> rfl

theorem local_outside {k : Nat} (h : 0<k) (i j : Fin k) (a : Bits4)
    (away : ∀ t, 1≤t → t≤5 → j≠fwd h i t) : Local h i a j=false := by
  have z (t : Nat) (lo : 1≤t) (hi : t≤5) : unit (fwd h i t) j=false := unit_off (away t lo hi)
  simp only [Local,combine,localForm,wireAdd,scaled_apply]
  simp only [z 1 (by decide) (by decide),z 2 (by decide) (by decide),z 3 (by decide) (by decide),
    z 4 (by decide) (by decide),z 5 (by decide) (by decide),Bool.false_xor]
  rcases a with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem local_at {k : Nat} (h : 0<k) (big : 9≤k) (i : Fin k) (a : Bits4)
    {t : Nat} (lo : 1≤t) (hi : t≤5) :
    Local h i a (fwd h i t)=localVal a t := by
  have distinct (u : Nat) (u5 : u≤5) (ne : t≠u) : fwd h i t≠fwd h i u :=
    fun e=>ne (fwd_parameter_inj h i (by omega) (by omega) e)
  have label (u : Nat) (u5 : u≤5) : unit (fwd h i u) (fwd h i t) = decide (t=u) := by
    by_cases c : t=u
    · subst t; simp only [unit,beq_self_eq_true,decide_true]
    · rw [unit_off (distinct u u5 c),decide_eq_false c]
  simp only [Local,combine,localForm,wireAdd,scaled_apply,localVal,label 1 (by decide),label 2 (by decide),label 3 (by decide),label 4 (by decide),label 5 (by decide)]
  have vals : t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
  rcases a with ⟨a,b,c,d⟩
  rcases vals with rfl|rfl|rfl|rfl|rfl <;>
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem local_private {k : Nat} (h : 0<k) (big : 9≤k) {P : Fin k→Bool}
    (sep : separated h P) {i j : Fin k} (hi : P i=true) (hj : P j=true) (ne : i≠j)
    (a : Bits4) {t : Nat} (lo : 2≤t) (lt : t≤4) :
    Local h j a (fwd h i t)=false := by
  apply local_outside
  intro z z1 z5 eq
  have a := overlap h big sep hi hj ne (by omega : 1≤t) (by omega : t≤5) z1 z5 eq
  rcases a with a|a <;> omega

theorem local_nonzero {k : Nat} (h : 0<k) (big : 9≤k) (i : Fin k) (a : Bits4)
    (az : a≠zero4) : Local h i a≠Zero := by
  intro same
  have bit (t : Nat) (lo : 1≤t) (hi : t≤5) : localVal a t=false := by
    have c := congrFun same (fwd h i t)
    rwa [local_at h big i a lo hi] at c
  have c := bit 1 (by decide) (by decide)
  have u := bit 2 (by decide) (by decide)
  have v := bit 4 (by decide) (by decide)
  have d := bit 5 (by decide) (by decide)
  rcases a with ⟨a,b,c',d'⟩
  exact az (by simpa [localVal,zero4] using And.intro u (And.intro v (And.intro c d)))

theorem no_two_periodic_zeros {k : Nat} (h : 0<k) (k3 : 3∣k)
    (r : Fin 3) (i : Fin k) (t : Nat) :
    ¬(periodic r (fwd h i t)=false ∧ periodic r (fwd h i (t+1))=false) := by
  intro ⟨a,b⟩
  have x : (i.val+t) % 3=r.val := by
    simpa only [periodic,fwd,idx,Nat.mod_mod_of_dvd _ k3,Bool.not_eq_false',beq_iff_eq] using a
  have y : (i.val+(t+1)) % 3=r.val := by
    simpa only [periodic,fwd,idx,Nat.mod_mod_of_dvd _ k3,Bool.not_eq_false',beq_iff_eq] using b
  omega

theorem hit_nonzero {k : Nat} (h : 0<k) (big : 9≤k) (i : Fin k) (a : Bits4)
    (az : a≠zero4) : combine a (rowForm h i)≠Zero := by
  intro br
  rw [←adjoint_local h (by omega : 2<k) i a] at br
  rcases (kernel_adjoint h (Local h i a)).mp br with z|⟨k3,r,z⟩
  · exact local_nonzero h big i a az z
  · have out (t : Nat) (lo : 5<t) (hi : t<k) :
        Local h i a (fwd h i t)=false := by
      apply local_outside
      intro u u1 u5 eq
      have neq := fwd_parameter_inj h i hi (by omega) eq
      omega
    have b6 := out 6 (by decide) (by omega)
    have b7 := out 7 (by decide) (by omega)
    rw [z] at b6 b7
    exact no_two_periodic_zeros h k3 r i 6 ⟨b6,b7⟩

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

def indices (k : Nat) : List (Fin k) := List.ofFn (fun i=>i)

theorem indices_mem {k : Nat} (i : Fin k) : i∈indices k := List.mem_ofFn.mpr ⟨i,rfl⟩

theorem indices_nd (k : Nat) : (indices k).Nodup := by
  unfold indices
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simp only [List.getElem_ofFn] at eq
  exact congrArg Fin.val eq

def sumBits {α : Type} (f : α→Bool) : List α→Bool
  | [] => false
  | a::as => f a ^^ sumBits f as

def sumWords {α : Type} {k : Nat} (f : α→Word k) : List α→Word k
  | [] => Zero
  | a::as => wireAdd (f a) (sumWords f as)

theorem sum_eval {α : Type} {k : Nat} (f : α→Word k) (L : List α) (j : Fin k) :
    sumWords f L j=sumBits (fun i=>f i j) L := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    change (f a j ^^ sumWords f as j)=(f a j ^^ sumBits (fun i=>f i j) as)
    rw [ih]

theorem sumBits_zero {α : Type} {f : α→Bool} {L : List α}
    (z : ∀ i∈L, f i=false) : sumBits f L=false := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    change (f a ^^ sumBits f as)=false
    rw [z _ List.mem_cons_self,ih (fun i hi=>z _ (List.mem_cons_of_mem _ hi))]
    rfl

theorem sumBits_only {α : Type} {f : α→Bool} {L : List α} (nd : L.Nodup) {i : α} (hi : i∈L)
    (zero : ∀ j∈L, i≠j → f j=false) : sumBits f L=f i := by
  induction L with
  | nil => simp at hi
  | cons a as ih =>
    obtain ⟨fr,no⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp hi with e|e
    · subst a
      have tail : sumBits f as=false := sumBits_zero
        (fun j hj=>zero j (List.mem_cons_of_mem _ hj) (fun q=>fr (q ▸ hj)))
      change (f i ^^ sumBits f as)=f i
      rw [tail,Bool.xor_false]
    · have r : i≠a := fun q=>fr (q ▸ e)
      change (f a ^^ sumBits f as)=f i
      rw [zero a List.mem_cons_self r,ih no e (fun j hj hj' => zero j (List.mem_cons_of_mem _ hj) hj'),Bool.false_xor]

theorem sumBits_xor {α : Type} (f g : α→Bool) (L : List α) :
    sumBits (fun i=>f i ^^ g i) L = (sumBits f L ^^ sumBits g L) := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    change ((f a ^^ g a) ^^ sumBits (fun i=>f i ^^ g i) as) =
      ((f a ^^ sumBits f as) ^^ (g a ^^ sumBits g as))
    rw [ih]
    simp only [Bool.xor_assoc,Bool.xor_left_comm]

def localSum {k : Nat} (h : 0<k) (w : Fin k→Bits4) (S : Word k) : Word k :=
  sumWords (fun i=>scaled (S i) (Local h i (w i))) (indices k)

theorem localSum_linear {k : Nat} (h : 0<k) (w : Fin k→Bits4) (S T : Word k) :
    localSum h w (wireAdd S T)=wireAdd (localSum h w S) (localSum h w T) := by
  funext j
  simp only [localSum,sum_eval,scaled_apply,wireAdd]
  have d (a b c : Bool) : ((a ^^ b) && c)=((a&&c) ^^ (b&&c)) := by cases a <;> cases b <;> cases c <;> decide
  simp only [d,sumBits_xor]

theorem localSum_zero {k : Nat} (h : 0<k) (w : Fin k→Bits4) : localSum h w Zero=Zero := by
  funext j
  simp only [localSum,sum_eval,scaled_apply,Bool.false_and]
  exact sumBits_zero (fun i hi=>rfl)

def Below {k : Nat} (S P : Word k) := ∀ i, S i=true → P i=true

theorem localSum_at_private {k : Nat} (h : 0<k) (big : 9≤k) {P S : Word k}
    (sep : separated h P) (sub : Below S P) (w : Fin k→Bits4)
    (i : Fin k) (hi : P i=true) {t : Nat} (lo : 2≤t) (up : t≤4) :
    localSum h w S (fwd h i t) = (S i && localVal (w i) t) := by
  unfold localSum
  rw [sum_eval]
  have single := sumBits_only (f:=fun j=>scaled (S j) (Local h j (w j)) (fwd h i t))
    (indices_nd k) (indices_mem i) (fun j hj ne=>by
      cases p : S j
      · rfl
      · rw [scaled_apply,local_private h big sep hi (sub j p) ne (w j) lo up]
        rfl)
  rw [single,scaled_apply,local_at h big i _ (by omega) (by omega)]

def endpointMask : Bits4 := (false,false,true,true)

theorem endpoint_of_zero_interior (a : Bits4) (nz : a≠zero4)
    (a2 : localVal a 2=false) (a3 : localVal a 3=false) (a4 : localVal a 4=false) :
    a=endpointMask := by
  obtain ⟨a,b,c,d⟩ := a
  change a=false at a2
  change b=false at a4
  change (c ^^ d)=false at a3
  subst a; subst b
  cases c <;> cases d <;> simp_all [zero4,endpointMask]

theorem zero_sum_endpoints {k : Nat} (h : 0<k) (big : 9≤k) {P S : Word k}
    (sep : separated h P) (sub : Below S P) (w : Fin k→Bits4)
    (nz : ∀ i, P i=true → w i≠zero4) (z : localSum h w S=Zero) (i : Fin k) (hi : S i=true) :
    w i=endpointMask := by
  have atRow (t : Nat) (lo : 2≤t) (up : t≤4) : localVal (w i) t=false := by
    have c := localSum_at_private h big sep sub w i (sub _ hi) lo up
    rw [z,hi,Bool.true_and] at c
    exact c.symm
  exact endpoint_of_zero_interior _ (nz i (sub i hi)) (atRow 2 (by decide) (by decide))
    (atRow 3 (by decide) (by decide)) (atRow 4 (by decide) (by decide))

theorem zero_sum_closed {k : Nat} (h : 0<k) (big : 9≤k) {P S : Word k}
    (sep : separated h P) (sub : Below S P) (w : Fin k→Bits4)
    (nz : ∀ i, P i=true → w i≠zero4) (z : localSum h w S=Zero) (i : Fin k) (hi : S i=true) :
    S (fwd h i 4)=true := by
  by_cases yes : S (fwd h i 4)=true
  · exact yes
  · exfalso
    have no := Bool.eq_false_iff.mpr yes
    have nd (j : Fin k) (ne : i≠j) : scaled (S j) (Local h j (w j)) (fwd h i 5)=false := by
      rw [scaled_apply]
      cases s : S j
      · rfl
      · rw [Bool.true_and]
        apply local_outside
        intro t t1 t5 e
        have o := overlap h big sep (sub i hi) (sub j s) ne (by decide : 1≤5) (by decide : 5≤5) t1 t5 e
        rcases o with ⟨_,_,e⟩|⟨w,_,_⟩
        · rw [←e,no] at s
          contradiction
        · omega
    have a := sumBits_only (f:=fun j=>scaled (S j) (Local h j (w j)) (fwd h i 5))
      (indices_nd k) (indices_mem i) (fun j _ ne=>nd j ne)
    have b := congrFun z (fwd h i 5)
    change sumWords _ _ _=false at b
    rw [sum_eval,a,scaled_apply,hi,Bool.true_and,local_at h big i _ (by decide) (by decide),
      zero_sum_endpoints h big sep sub w nz z i hi] at b
    contradiction

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

theorem nonzero_has_true {k : Nat} {x : Word k} (nz : x≠Zero) : ∃ i, x i=true := by
  classical
  by_cases p : ∃ i, x i=true
  · exact p
  · exact False.elim (nz (funext (fun i=>Bool.eq_false_iff.mpr (fun a=>p ⟨i,a⟩))))

theorem xor_below {k : Nat} {P S T : Word k} (s : Below S P) (t : Below T P) :
    Below (wireAdd S T) P := by
  intro i h
  cases e : S i
  · have z : T i=true := by simpa [wireAdd,e] using h
    exact t i z
  · exact s i e

theorem xor_zero_equal {k : Nat} {S T : Word k} (h : wireAdd S T=Zero) : S=T := by
  have c := congrArg (fun a=>wireAdd a T) h
  rw [add_cancel,wire_zero_add] at c
  exact c

theorem saturated {k : Nat} (h : 0<k) {P S : Word k}
    (sep : separated h P) (sub : Below S P)
    (close : ∀ i, S i=true → S (fwd h i 4)=true) (nz : S≠Zero) : S=P := by
  obtain ⟨i,hi⟩ := nonzero_has_true nz
  obtain ⟨four,r,phase⟩ := closed_subset_forces_orbit h sep sub close ⟨i,hi⟩
  have walk (n : Nat) : S (fwd h i (4*n))=true := by
    induction n with
    | zero => simpa only [Nat.mul_zero,fwd_zero] using hi
    | succ n ih =>
      have z := close _ ih
      rw [fwd_fwd] at z
      exact z
  funext j
  by_cases choose : P j=true
  · have classEq := ((phase i).mp (sub i hi)).trans ((phase j).mp choose).symm
    have rem : gap i j % 4=0 := (gap_phase i j four).mpr classEq
    have e : 4*(gap i j/4)=gap i j := by omega
    have q := walk (gap i j/4)
    rw [e,gap_end h i j] at q
    rw [q,choose]
  · have ne : S j=false := Bool.eq_false_iff.mpr (fun e=>choose (sub j e))
    rw [ne,Bool.eq_false_iff.mpr choose]

def Relates {k : Nat} (h : 0<k) (P : Word k) (w : Fin k→Bits4) (S : Word k) : Prop :=
  Below S P ∧ adjoint h (localSum h w S)=Zero

theorem relation_if_zero_or_periodic {k : Nat} (h : 0<k) (P : Word k) (w : Fin k→Bits4) (S : Word k) :
    Relates h P w S ↔ Below S P ∧
      (localSum h w S=Zero ∨ (3∣k ∧ ∃ r, localSum h w S=periodic r)) := by
  simp only [Relates,kernel_adjoint]

theorem zero_periodic_disjoint {k : Nat} (h : 0<k) (big : 9≤k)
    {P S T : Word k} (sep : separated h P) (s : Below S P) (t : Below T P) (w : Fin k→Bits4)
    (nz : ∀ i, P i=true → w i≠zero4) (sz : S≠Zero) (z : localSum h w S=Zero)
    (k3 : 3∣k) (r : Fin 3) (per : localSum h w T=periodic r) : False := by
  obtain ⟨i,hi⟩ := nonzero_has_true sz
  have fixed := zero_sum_endpoints h big sep s w nz z i hi
  have check (a : Nat) (lo : 2≤a) (up : a≤4) (vv : localVal endpointMask a=false) :
      periodic r (fwd h i a)=false := by
    have e := localSum_at_private h big sep t w i (s i hi) lo up
    rwa [per,fixed,vv,Bool.and_false] at e
  have x := check 2 (by decide) (by decide) rfl
  have y := check 3 (by decide) (by decide) rfl
  exact no_two_periodic_zeros h k3 r i 2 ⟨x,y⟩

theorem periodic_distinct_on_three {k : Nat} (h : 0<k) (k3 : 3∣k) (i : Fin k)
    (r s : Fin 3)
    (eq : ∀ t, 2≤t → t≤4 → periodic r (fwd h i t)=periodic s (fwd h i t)) : r=s := by
  have existsIdx : ∃ t, 2≤t ∧ t≤4 ∧ (i.val+t) % 3=r.val := by
    have bound := r.isLt
    by_cases a : (i.val+2) % 3=r.val
    · exact ⟨2,by decide,by decide,a⟩
    · by_cases b : (i.val+3) % 3=r.val
      · exact ⟨3,by decide,by decide,b⟩
      · exact ⟨4,by decide,by decide,by omega⟩
  obtain ⟨t,tlo,tup,hj⟩ := existsIdx
  have e := eq t tlo tup
  simp only [periodic,fwd,idx,Nat.mod_mod_of_dvd _ k3,hj,BEq.rfl,Bool.not_true] at e
  apply Fin.ext
  apply beq_iff_eq.mp
  simpa only [Bool.not_eq_false'] using e.symm

theorem periodic_same_for_two {k : Nat} (h : 0<k) (big : 9≤k) {P S T : Word k}
    (sep : separated h P) (s : Below S P) (t : Below T P) (w : Fin k→Bits4)
    (inh : ∃ i, P i=true) (k3 : 3∣k) (r u : Fin 3)
    (sr : localSum h w S=periodic r) (tr : localSum h w T=periodic u) : r=u := by
  obtain ⟨i,hi⟩ := inh
  have readS (a : Nat) (lo : 2≤a) (up : a≤4) :
      periodic r (fwd h i a)=(S i && localVal (w i) a) := by
    have e := localSum_at_private h big sep s w i hi lo up
    rwa [sr] at e
  have readT (a : Nat) (lo : 2≤a) (up : a≤4) :
      periodic u (fwd h i a)=(T i && localVal (w i) a) := by
    have e := localSum_at_private h big sep t w i hi lo up
    rwa [tr] at e
  have sees (r : Fin 3) (b : Bool)
      (f : ∀ a, 2≤a → a≤4 → periodic r (fwd h i a)=(b && localVal (w i) a)) : b=true := by
    cases b
    · exact False.elim (no_two_periodic_zeros h k3 r i 2
        ⟨f 2 (by decide) (by decide),f 3 (by decide) (by decide)⟩)
    · rfl
  have a := sees r (S i) readS
  have b := sees u (T i) readT
  apply periodic_distinct_on_three h k3 i r u
  intro c lo up
  rw [readS c lo up,readT c lo up,a,b]

theorem unique_nonzero_relation {k : Nat} (h : 0<k) (big : 9≤k) {P S T : Word k}
    (sep : separated h P) (w : Fin k→Bits4) (nz : ∀ i, P i=true → w i≠zero4)
    (s : Relates h P w S) (t : Relates h P w T) (ns : S≠Zero) (nt : T≠Zero) : S=T := by
  obtain ⟨s,ss⟩ := (relation_if_zero_or_periodic h P w S).mp s
  obtain ⟨t,tt⟩ := (relation_if_zero_or_periodic h P w T).mp t
  rcases ss with zs|⟨k3,r,ps⟩ <;> rcases tt with zt|⟨l3,u,pt⟩
  · exact (saturated h sep s (zero_sum_closed h big sep s w nz zs) ns).trans
      (saturated h sep t (zero_sum_closed h big sep t w nz zt) nt).symm
  · exact False.elim (zero_periodic_disjoint h big sep s t w nz ns zs l3 u pt)
  · exact False.elim (zero_periodic_disjoint h big sep t s w nz nt zt k3 r ps)
  · obtain ⟨i,hi⟩ := nonzero_has_true ns
    have e := periodic_same_for_two h big sep s t w ⟨i,s i hi⟩ k3 r u ps pt
    rw [←e] at pt
    by_cases n : wireAdd S T=Zero
    · exact xor_zero_equal n
    · have k : localSum h w (wireAdd S T)=Zero := by
        rw [localSum_linear,ps,pt,wire_self]
      exact False.elim (zero_periodic_disjoint h big sep (xor_below s t) t w nz n k k3 r pt)

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

theorem local_zero {k : Nat} (h : 0<k) (i : Fin k) : Local h i zero4=Zero := by
  funext j
  rfl

theorem local_add {k : Nat} (h : 0<k) (i : Fin k) (a b : Bits4) :
    Local h i (add4 a b)=wireAdd (Local h i a) (Local h i b) := by
  funext j
  simp only [Local,combine,add4,wireAdd,scaled_apply]
  have d (a b c : Bool) : ((a ^^ b) && c)=((a&&c) ^^ (b&&c)) := by cases a <;> cases b <;> cases c <;> decide
  simp only [d,Bool.xor_assoc,Bool.xor_left_comm]

theorem sum_add {α : Type} {k : Nat} (f g : α→Word k) (L : List α) :
    sumWords (fun i=>wireAdd (f i) (g i)) L=wireAdd (sumWords f L) (sumWords g L) := by
  funext j
  simp only [sum_eval,wireAdd,sumBits_xor]

theorem sum_dot {α : Type} {k : Nat} (u : Word k) (f : α→Word k) (L : List α) :
    dot k u (sumWords f L)=sumBits (fun i=>dot k u (f i)) L := by
  induction L with
  | nil =>
    change dot k u Zero=false
    rw [dot_sym,dot_zero]
  | cons i rest ih =>
    simp only [sumWords,sumBits,dot_add,ih]

def packed {k : Nat} (h : 0<k) (a : Fin k→Bits4) : Word k :=
  sumWords (fun i=>Local h i (a i)) (indices k)

def combo {k : Nat} (h : 0<k) (P : Word k) : SubBits k where
  carries u := ∃ aa : Fin k→Bits4, (∀ i, P i=false → aa i=zero4) ∧ packed h aa=u
  zero_in := by
    refine ⟨fun _=>zero4,fun _ _=>rfl,?_⟩
    funext j
    rw [packed,sum_eval,sumBits_zero (fun i _=>by rw [local_zero])]
  closed_add := by
    rintro u v ⟨a,az,sa⟩ ⟨b,bz,sb⟩
    refine ⟨fun i=>add4 (a i) (b i),fun i hi=>by change add4 (a i) (b i)=zero4; rw [az i hi,bz i hi]; rfl,?_⟩
    simp only [packed,local_add,sum_add,← sa,← sb]

theorem one_into_combo {k : Nat} (h : 0<k) {P : Word k} (i : Fin k) (hi : P i=true)
    (c : Bits4) : (combo h P).carries (Local h i c) := by
  let aa := fun j : Fin k => if j=i then c else zero4
  refine ⟨aa,?_ ,?_⟩
  · intro j hj
    have ne : j≠i := fun x=>Bool.noConfusion (hi.symm.trans (x ▸ hj))
    simp [aa,ne]
  · funext j
    rw [packed,sum_eval]
    have hu := sumBits_only (f:=fun z=>Local h z (aa z) j) (indices_nd k) (indices_mem i)
      (fun z _ ne=>by simp only [aa,ite_eq_right ne.symm,local_zero])
    rw [hu]
    simp [aa]

def Guards {k : Nat} (h : 0<k) (P U : Word k) :=
  ∀ i, P i=true → U (fwd h i 2)=false ∧ U (fwd h i 4)=false ∧
    U (fwd h i 1)=U (fwd h i 3) ∧ U (fwd h i 3)=U (fwd h i 5)

theorem combo_ortho_iff {k : Nat} (h : 0<k) (P U : Word k) :
    (∀ z, (combo h P).carries z → dot k U z=false) ↔ Guards h P U := by
  constructor
  · intro all i hi
    have h1 := all _ (one_into_combo h i hi e0)
    have h2 := all _ (one_into_combo h i hi e1)
    have h3 := all _ (one_into_combo h i hi e2)
    have h4 := all _ (one_into_combo h i hi e3)
    have field3 : (U (fwd h i 1) ^^ U (fwd h i 3))=false := by
      simpa [Local,combine,localForm,dot_add,dot_scaled,e2,unit_dot] using h3
    have field4 : (U (fwd h i 3) ^^ U (fwd h i 5))=false := by
      simpa [Local,combine,localForm,dot_add,dot_scaled,e3,unit_dot] using h4
    have xor0 (a b : Bool) (e : (a ^^ b)=false) : a=b := by cases a <;> cases b <;> simp_all
    exact ⟨by simpa [Local,combine,localForm,dot_add,dot_scaled,e0,unit_dot] using h1,
      by simpa [Local,combine,localForm,dot_add,dot_scaled,e1,unit_dot] using h2,
      xor0 _ _ field3,xor0 _ _ field4⟩
  · rintro guards z ⟨aa,az,rfl⟩
    rw [packed,sum_dot]
    apply sumBits_zero
    intro i _
    cases on : P i
    · rw [az i on,local_zero,dot_sym,dot_zero]
    · obtain ⟨a,b,c,d⟩ := guards i on
      simp only [Local,combine,localForm,dot_add,dot_scaled,unit_dot,a,b,c,d,
        Bool.and_false,Bool.xor_self,Bool.xor_false]

def Passes {k : Nat} (h : 0<k) (P : Word k) (r : Fin 3) :=
  ∀ U, Guards h P U → dot k U (periodic r)=false

theorem passes_representation {k : Nat} (h : 0<k) (P : Word k) (r : Fin 3) :
    Passes h P r ↔ (combo h P).carries (periodic r) := by
  rw [double_ortho]
  constructor
  · intro q U G
    exact q U ((combo_ortho_iff h P U).mp G)
  · intro q U G
    exact q U ((combo_ortho_iff h P U).mpr G)

theorem periodic_relation_from_pass {k : Nat} (h : 0<k) (big : 9≤k)
    (P : Word k) (r : Fin 3) (k3 : 3∣k) (pass : Passes h P r) :
    ∃ w S, (∀ i, P i=true → w i≠zero4) ∧ S≠Zero ∧ Relates h P w S := by
  classical
  obtain ⟨aa,az,e⟩ := (passes_representation h P r).mp pass
  let S : Word k := fun i=>decide (aa i≠zero4)
  let w : Fin k→Bits4 := fun i=>if aa i=zero4 then e0 else aa i
  have b : Below S P := by
    intro i on
    by_cases t : P i=false
    · exact False.elim (of_decide_eq_true on (az i t))
    · cases q : P i <;> simp_all
  have wz : ∀ i, P i=true → w i≠zero4 := by
    intro i _
    unfold w
    by_cases h : aa i=zero4
    · rw [ite_eq_left h]; decide
    · rwa [ite_eq_right h]
  have eq : localSum h w S=periodic r := by
    rw [←e]
    unfold localSum packed
    congr 1
    funext i
    by_cases p : aa i=zero4 <;> simp [S,w,scaled,p,local_zero]
  have nz : S≠Zero := by
    intro sure
    rw [sure,localSum_zero] at eq
    let i : Fin k := ⟨0,h⟩
    have bad1 : periodic r (fwd h i 0)=false := by rw [←eq]
    have bad2 : periodic r (fwd h i 1)=false := by rw [←eq]
    exact no_two_periodic_zeros h k3 r i 0 ⟨bad1,bad2⟩
  exact ⟨w,S,wz,nz,(relation_if_zero_or_periodic h P w S).mpr ⟨b,Or.inr ⟨k3,r,eq⟩⟩⟩

theorem pass_from_periodic_relation {k : Nat} (h : 0<k) {P S : Word k}
    (w : Fin k→Bits4) (sub : Below S P) (r : Fin 3)
    (q : localSum h w S=periodic r) : Passes h P r := by
  apply (passes_representation h P r).mpr
  let aa : Fin k→Bits4 := fun i=> if S i then w i else zero4
  refine ⟨aa,?_ ,?_⟩
  · intro i no
    have p : S i=false := Bool.eq_false_iff.mpr (fun v=>Bool.noConfusion ((sub i v).symm.trans no))
    simp [aa,p]
  · rw [←q]
    unfold packed localSum
    congr 1
    funext i
    cases e : S i <;> simp [aa,e,scaled,local_zero]

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

theorem local_endpoint {k : Nat} (h : 0<k) (i : Fin k) :
    Local h i endpointMask=wireAdd (unit (fwd h i 1)) (unit (fwd h i 5)) := by
  funext j
  simp only [Local,combine,localForm,scaled_apply,endpointMask,wireAdd,Bool.false_and,
    Bool.true_and,Bool.false_xor,Bool.xor_assoc]
  generalize unit (fwd h i 1) j=a
  generalize unit (fwd h i 3) j=b
  generalize unit (fwd h i 5) j=c
  cases a <;> cases b <;> cases c <;> decide

theorem reverse_phase {k : Nat} (h : 0<k) (four : 4∣k) (big : 9≤k) (i : Fin k) :
    (rIdx h 1 i).val % 4=(rIdx h 5 i).val % 4 := by
  have d := Nat.mod_eq_zero_of_dvd four
  change ((i.val+k-1) % k) % 4=((i.val+k-5) % k) % 4
  rw [Nat.mod_mod_of_dvd _ four,Nat.mod_mod_of_dvd _ four]
  omega

theorem endpoint_sum_orbit {k : Nat} (h : 0<k) (big : 9≤k) (P : Word k)
    (o : orbit P) : localSum h (fun _=>endpointMask) P=Zero := by
  obtain ⟨four,a,phase⟩ := o
  funext j
  simp only [localSum,sum_eval,local_endpoint,scaled_apply,wireAdd]
  have d (a b c : Bool) : (a && (b ^^ c))=((a&&b)^^(a&&c)) := by cases a <;> cases b <;> cases c <;> rfl
  simp only [d,sumBits_xor]
  have one (t : Nat) (ht : t<k) :
      sumBits (fun i=>P i && unit (fwd h i t) j) (indices k)=P (rIdx h t j) := by
    have v : unit (fwd h (rIdx h t j) t) j=true := unit_at (fwd_rIdx h j t ht).symm
    have z (i : Fin k) (neq : rIdx h t j≠i) : unit (fwd h i t) j=false :=
      unit_off (fun e=>neq ((fwd_eq_iff h i j t ht).mp e.symm).symm)
    have ax := sumBits_only (f:=fun i=>P i && unit (fwd h i t) j)
        (indices_nd k) (indices_mem (rIdx h t j)) (fun i _ ne=>by rw [z i ne,Bool.and_false])
    rw [ax,v,Bool.and_true]
  rw [one 1 (by omega),one 5 (by omega)]
  have eq : (rIdx h 1 j).val % 4=(rIdx h 5 j).val % 4 := reverse_phase h four big j
  have same : P (rIdx h 1 j)=P (rIdx h 5 j) := by
    cases p : P (rIdx h 1 j) <;> cases q : P (rIdx h 5 j) <;> try rfl
    · have f := (phase _).mpr (eq.trans ((phase _).mp q))
      rw [p] at f
      contradiction
    · have f := (phase _).mpr (eq.symm.trans ((phase _).mp p))
      rw [q] at f
      contradiction
  rw [same,Bool.xor_self]

def Saving {k : Nat} (h : 0<k) (P : Word k) :=
  ∃ w : Fin k→Bits4, ∃ S : Word k,
    (∀ i, P i=true → w i≠zero4) ∧ S≠Zero ∧ Relates h P w S

theorem saving_iff {k : Nat} (h : 0<k) (big : 9≤k) (P : Word k) (sep : separated h P) :
    Saving h P ↔ orbit P ∨ (3∣k ∧ ∃ r, Passes h P r) := by
  constructor
  · rintro ⟨w,S,wz,nz,rel⟩
    obtain ⟨sub,a⟩ := (relation_if_zero_or_periodic h P w S).mp rel
    rcases a with x|⟨k3,r,e⟩
    · exact Or.inl (closed_subset_forces_orbit h sep sub (zero_sum_closed h big sep sub w wz x)
        (nonzero_has_true nz))
    · exact Or.inr ⟨k3,r,pass_from_periodic_relation h w sub r e⟩
  · rintro (orb|⟨k3,r,e⟩)
    · have mem : ∃ i, P i=true := by
        obtain ⟨four,a,phase⟩ := orb
        have e : a.val<k := by have := a.isLt; omega
        exact ⟨⟨a.val,e⟩,(phase _).mpr (Nat.mod_eq_of_lt a.isLt)⟩
      refine ⟨fun _=>endpointMask,P,fun _ _=>by change endpointMask≠zero4; decide,?_ ,?_⟩
      · intro no
        rw [no] at mem
        obtain ⟨i,e⟩ := mem
        contradiction
      · exact (relation_if_zero_or_periodic h P _ P).mpr
          ⟨fun _ h=>h,Or.inl (endpoint_sum_orbit h big P orb)⟩
    · exact periodic_relation_from_pass h big P r k3 e

end PNP29946.Binary

namespace PNP29946.Binary

def enumerate {k : Nat} : List (Word k) → List (Word k)
  | [] => [Zero]
  | a::as => enumerate as ++ (enumerate as).map (fun x=>wireAdd x a)

theorem enum_size {k : Nat} (L : List (Word k)) : (enumerate L).length=2^L.length := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    simp only [enumerate,List.length_append,List.length_map,List.length_cons,ih,Nat.pow_succ]
    omega

theorem enum_spec {k : Nat} (L : List (Word k)) (x : Word k) :
    x∈enumerate L ↔ InSpan L x := by
  induction L generalizing x with
  | nil => simp [enumerate,InSpan]
  | cons a l ih =>
    simp only [enumerate,List.mem_append,List.mem_map,ih,InSpan]
    constructor
    · rintro (z | ⟨u,hu,rfl⟩)
      · exact Or.inl z
      · exact Or.inr (by rw [add_cancel]; exact hu)
    · rintro (z | z)
      · exact Or.inl z
      · exact Or.inr ⟨wireAdd x a,z,add_cancel x a⟩

theorem map_nodup_on {α β : Type} {L : List α} {f : α→β} (nd : L.Nodup)
    (inj : ∀ a∈L, ∀ b∈L, f a=f b → a=b) : (L.map f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simp only [List.getElem_map] at eq
  exact (List.nodup_iff_eq_of_getElem_eq.mp nd) _ _ _ _
    (inj _ (List.getElem_mem _) _ (List.getElem_mem _) eq)

def selectors {k : Nat} (J : List (Fin k)) : List (Word k) := enumerate (J.map unit)

theorem selectors_size {k : Nat} (J : List (Fin k)) : (selectors J).length=2^J.length := by
  rw [selectors,enum_size,List.length_map]

def InRows {k : Nat} (S : Word k) (J : List (Fin k)) := ∀ i, S i=true → i∈J

theorem selector_outside {k : Nat} (J : List (Fin k)) {x : Word k}
    (mem : x∈selectors J) {i : Fin k} (not : i∉J) : x i=false := by
  rw [selectors,enum_spec] at mem
  induction J generalizing x with
  | nil =>
    change x=Zero at mem
    rw [mem]
  | cons j js ih =>
    have neq : i≠j := fun e=>not (e ▸ List.mem_cons_self)
    have q : i∉js := fun h=>not (List.mem_cons_of_mem _ h)
    rcases mem with mem|mem
    · exact ih mem q
    · have hh := ih mem q
      change (x i ^^ unit j i)=false at hh
      rwa [unit_off neq,Bool.xor_false] at hh

theorem selectors_nd {k : Nat} (J : List (Fin k)) (nd : J.Nodup) : (selectors J).Nodup := by
  induction J with
  | nil => simp [selectors,enumerate]
  | cons i js ih =>
    obtain ⟨ni,njs⟩ := List.nodup_cons.mp nd
    have ht := ih njs
    change (selectors js ++ (selectors js).map (fun x=>wireAdd x (unit i))).Nodup
    apply List.nodup_append.mpr
    refine ⟨ht,map_nodup_on ht (fun a _ b _ e=>?_ ),?_⟩
    · have z := congrArg (fun v=>wireAdd v (unit i)) e
      simpa only [add_cancel] using z
    · intro a am b bm e
      obtain ⟨z,zm,rfl⟩ := List.mem_map.mp bm
      have out := congrFun e i
      change a i = (z i ^^ unit i i) at out
      rw [selector_outside js am ni,selector_outside js zm ni,unit_at rfl] at out
      contradiction

theorem selector_in_rows {k : Nat} (J : List (Fin k)) {x : Word k} (mem : x∈selectors J) :
    InRows x J := by
  classical
  intro i yes
  by_cases q : i∈J
  · exact q
  · rw [selector_outside J mem q] at yes
    contradiction

def marks {k : Nat} (P : Word k) : List (Fin k) := (indices k).filter P

theorem marks_mem {k : Nat} {P : Word k} {i : Fin k} : i∈marks P ↔ P i=true :=
  ⟨fun q=>(List.mem_filter.mp q).2,fun h=>List.mem_filter.mpr ⟨indices_mem _,h⟩⟩

theorem marks_nd {k : Nat} (P : Word k) : (marks P).Nodup :=
  List.filter_sublist.nodup (indices_nd k)

def image {k : Nat} (h : 0<k) (w : Fin k→Bits4) (S : Word k) : Word k :=
  adjoint h (localSum h w S)

theorem image_add {k : Nat} (h : 0<k) (w : Fin k→Bits4) (S T : Word k) :
    image h w (wireAdd S T)=wireAdd (image h w S) (image h w T) := by
  simp only [image,localSum_linear,adjoint_add]

def hitAt {k : Nat} (h : 0<k) (w : Fin k→Bits4) (i : Fin k) :=
  combine (w i) (rowForm h i)

theorem image_unit {k : Nat} (h : 0<k) (big : 9≤k) (w : Fin k→Bits4) (i : Fin k) :
    image h w (unit i)=hitAt h w i := by
  have e : localSum h w (unit i)=Local h i (w i) := by
    funext j
    rw [localSum,sum_eval]
    have z := sumBits_only (f:=fun t=>scaled (unit i t) (Local h t (w t)) j)
      (indices_nd k) (indices_mem i) (fun t _ q=>by rw [scaled_apply,unit_off q.symm,Bool.false_and])
    rw [z,scaled_apply,unit_at rfl,Bool.true_and]
  rw [image,e]
  exact adjoint_local h (by omega) i (w i)

theorem sum_adjoint {α : Type} {k : Nat} (h : 0<k) (f : α→Word k) (L : List α) :
    adjoint h (sumWords f L)=sumWords (fun i=>adjoint h (f i)) L := by
  induction L with
  | nil => exact adjoint_zero h
  | cons a as ih => simp only [sumWords,adjoint_add,ih]

theorem span_sum {α : Type} {k : Nat} (Q : List (Word k)) (f : α→Word k) (L : List α)
    (m : ∀ i∈L, InSpan Q (f i)) : InSpan Q (sumWords f L) := by
  induction L with
  | nil => exact span_zero Q
  | cons a as ih =>
    exact span_add Q _ _ (m _ List.mem_cons_self) (ih (fun i hi=>m _ (List.mem_cons_of_mem _ hi)))

theorem image_span {k : Nat} (h : 0<k) (big : 9≤k) (Q : List (Word k)) (w : Fin k→Bits4) (S : Word k)
    (g : ∀ i, S i=true → InSpan Q (hitAt h w i)) :
    InSpan Q (image h w S) := by
  rw [image,localSum,sum_adjoint]
  apply span_sum
  intro i m
  cases yes : S i
  · simp only [scaled,yes,Bool.false_eq_true,ite_false,adjoint_zero]
    exact span_zero Q
  · simp only [scaled,yes,ite_true,Local,adjoint_local h (by omega : 2<k)]
    exact g i yes

theorem list_rank {k : Nat} (h : 0<k) (big : 9≤k) (Q : List (Word k)) (w : Fin k→Bits4) (J : List (Fin k))
    (nd : J.Nodup) (g : ∀ i∈J, InSpan Q (hitAt h w i))
    (injective : ∀ S T, InRows S J → InRows T J → image h w S=image h w T → S=T) :
    J.length≤Q.length := by
  let D := (selectors J).map (image h w)
  have all : D ⊆ enumerate Q := by
    intro y hy
    obtain ⟨S,hs,rfl⟩ := List.mem_map.mp hy
    apply (enum_spec Q _).mpr
    exact image_span h big Q w S (fun i x=>g i (selector_in_rows J hs i x))
  have Dnd : D.Nodup := map_nodup_on (selectors_nd J nd)
    (fun s sm t tm eq=>injective s t (selector_in_rows J sm) (selector_in_rows J tm) eq)
  have l := Dnd.length_le_of_subset all
  change ((selectors J).map (image h w)).length ≤ (enumerate Q).length at l
  rw [List.length_map,selectors_size,enum_size] at l
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp l

end PNP29946.Binary

namespace PNP29946.Binary
open OrbitFour

theorem coeff_nonzero (a : Bits4) (j : Fin 4) (hc : coeff a j=true) : a≠zero4 := by
  intro h
  rw [h] at hc
  simp [coeff,zero4] at hc

theorem span_subset {k : Nat} {Q R : List (Word k)} (sub : Q⊆R)
    {u : Word k} (p : InSpan Q u) : InSpan R u := by
  apply (span_iff_test R u).mpr
  intro x h
  exact span_null Q (fun q m=>h q (sub m)) p

theorem collisions_relation {k : Nat} (h : 0<k) {P S T : Word k} (w : Fin k→Bits4)
    (a : Below S P) (b : Below T P) (e : image h w S=image h w T) :
    Relates h P w (wireAdd S T) := by
  refine ⟨xor_below a b,?_⟩
  change image h w (wireAdd S T)=Zero
  rw [image_add,e,wire_self]

theorem rank_lower {k : Nat} (h : 0<k) (big : 9≤k) (P : Word k) (sep : separated h P)
    (Q : List (Word k)) (hits : AllHits h P Q) :
    (marks P).length≤Q.length ∨ ((marks P).length≤Q.length+1 ∧ Saving h P) := by
  classical
  have W (i : Fin k) (hi : P i=true) :
      ∃ v : Bits4, v≠zero4 ∧ InSpan Q (combine v (rowForm h i)) := by
    obtain ⟨v,j,c,s⟩ := hits i hi
    exact ⟨v,coeff_nonzero v j c,s⟩
  let w : Fin k→Bits4 := fun i => if hi : P i=true then Classical.choose (W i hi) else zero4
  have wz (i : Fin k) (hi : P i=true) : w i≠zero4 := by
    simpa only [w,dite_eq_left hi] using (Classical.choose_spec (W i hi)).1
  have ws (i : Fin k) (hi : P i=true) : InSpan Q (hitAt h w i) := by
    simpa only [hitAt,w,dite_eq_left hi] using (Classical.choose_spec (W i hi)).2
  by_cases none : ∃ S, S≠Zero ∧ Relates h P w S
  · obtain ⟨U,U0,ur⟩ := none
    obtain ⟨i,hi⟩ := nonzero_has_true U0
    let J := (marks P).erase i
    have Jnd : J.Nodup := (List.erase_sublist).nodup (marks_nd P)
    have hm : i∈marks P := marks_mem.mpr (ur.1 i hi)
    have noti : i∉J := (marks_nd P).not_mem_erase
    have only (j : Fin k) (hs : j∈J) : P j=true :=
      marks_mem.mp (List.mem_of_mem_erase hs)
    have rr : J.length≤Q.length := by
      apply list_rank h big Q w J Jnd (fun j hj=>ws _ (only j hj))
      intro S T ss ts same
      let V := wireAdd S T
      have nr := collisions_relation h w (fun j bj=>only j (ss j bj)) (fun j bj=>only j (ts j bj)) same
      by_cases z : V=Zero
      · exact xor_zero_equal z
      · have e := unique_nonzero_relation h big sep w wz nr ur z U0
        have fs : S i=false := Bool.eq_false_iff.mpr (fun a=>noti (ss i a))
        have ft : T i=false := Bool.eq_false_iff.mpr (fun a=>noti (ts i a))
        have e' := congrFun e i
        change (S i ^^ T i)=U i at e'
        rw [fs,ft,hi] at e'
        contradiction
    have l : J.length=(marks P).length-1 := List.length_erase_of_mem hm
    exact Or.inr ⟨by omega,⟨w,U,wz,U0,ur⟩⟩
  · apply Or.inl
    apply list_rank h big Q w (marks P) (marks_nd P) (fun i hi=>ws i (marks_mem.mp hi))
    intro S T ss ts same
    have a := collisions_relation h w (fun i h=>marks_mem.mp (ss i h)) (fun i h=>marks_mem.mp (ts i h)) same
    have v : wireAdd S T=Zero := Classical.byContradiction (fun n=>none ⟨_,n,a⟩)
    exact xor_zero_equal v

theorem queries_pad {k d : Nat} (Q : List (Word k)) (bound : Q.length≤d) :
    ∃ q : Fin d→Word k, Q⊆List.ofFn q := by
  let R := Q++List.replicate (d-Q.length) Zero
  have e : R.length=d := by simp [R]; omega
  let q : Fin d→Word k := fun j => R[j.val]'(by rw [e]; exact j.isLt)
  refine ⟨q,?_⟩
  intro x hx
  have xr : x∈R := List.mem_append_left _ hx
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp xr
  apply List.mem_ofFn.mpr
  refine ⟨⟨i,by omega⟩,?_⟩
  exact eq

theorem all_mark_upper {k d : Nat} (h : 0<k) (P : Word k) (le : (marks P).length≤d) :
    ∃ q : Fin d→Word k, AllHits h P (List.ofFn q) := by
  let Q := (marks P).map (hitAt h (fun _=>e0))
  obtain ⟨q,qq⟩ := queries_pad Q (by simpa [Q] using le)
  refine ⟨q,?_⟩
  intro i hi
  refine ⟨e0,0,rfl,span_gen _ (qq ?_)⟩
  exact List.mem_map.mpr ⟨i,marks_mem.mpr hi,rfl⟩

theorem save_mark_upper {k d : Nat} (h : 0<k) (big : 9≤k) (P : Word k) (b : (marks P).length≤d+1)
    (save : Saving h P) : ∃ q : Fin d→Word k, AllHits h P (List.ofFn q) := by
  obtain ⟨w,S,wz,S0,rel⟩ := save
  obtain ⟨i,hi⟩ := nonzero_has_true S0
  let J := (marks P).erase i
  let Q := J.map (hitAt h w)
  have hm : i∈marks P := marks_mem.mpr (rel.1 i hi)
  have Jlen : J.length=(marks P).length-1 := List.length_erase_of_mem hm
  have Qlen : Q.length≤d := by simp only [Q,List.length_map,Jlen]; omega
  obtain ⟨q,qq⟩ := queries_pad Q Qlen
  refine ⟨q,?_⟩
  intro j hj
  obtain ⟨a,ha⟩ := nonzero_coeff (w j) (wz j hj)
  refine ⟨w j,a,ha,span_subset qq ?_⟩
  have direct (u : Fin k) (hu : P u=true) (ne : u≠i) : InSpan Q (hitAt h w u) := by
    apply span_gen Q
    exact List.mem_map.mpr ⟨u,(List.mem_erase_of_ne ne).mpr (marks_mem.mpr hu),rfl⟩
  by_cases u : j=i
  · subst j
    let T := wireAdd S (unit i)
    have val : image h w T=hitAt h w i := by
      have z : image h w S=Zero := rel.2
      rw [show T=wireAdd S (unit i) from rfl,image_add,z,image_unit h big,wire_zero_add]
    change InSpan Q (hitAt h w i)
    rw [←val]
    apply image_span h big
    intro u hU
    have n : u≠i := by
      intro eq; subst u
      change (S i ^^ unit i i)=true at hU
      rw [hi,unit_at rfl] at hU
      contradiction
    have yes : S u=true := by
      change (S u ^^ unit i u)=true at hU
      rwa [unit_off n,Bool.xor_false] at hU
    exact direct u (rel.1 u yes) n
  · exact direct j hj u

theorem fit_rank_exact {k d : Nat} (h : 0<k) (big : 9≤k) (P : Word k) (sep : separated h P) (p : Params k) :
    Fits h p P d ↔
      (marks P).length≤d ∨ ((marks P).length≤d+1 ∧ (orbit P ∨ (3∣k ∧ ∃ r, Passes h P r))) := by
  rw [fits_iff_hits,←saving_iff h big P sep]
  constructor
  · rintro ⟨q,qh⟩
    simpa only [List.length_ofFn] using rank_lower h big P sep (List.ofFn q) qh
  · rintro (plain|⟨bound,save⟩)
    · exact all_mark_upper h P plain
    · exact save_mark_upper h big P bound save

end PNP29946.Binary

namespace PNP29946.Binary

theorem sumBits_map {α β : Type} (g : α→β) (f : β→Bool) (L : List α) :
    sumBits f (L.map g) = sumBits (fun a=>f (g a)) L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons,sumBits,ih]

theorem dot_indices {k : Nat} (x y : Word k) :
    dot k x y = sumBits (fun i=>x i && y i) (indices k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : indices (k+1)=0::(indices k).map Fin.succ := by
      simp [indices,List.ofFn_succ,List.map_ofFn,Function.comp_def]
    rw [e,sumBits,sumBits_map]
    change ((x 0 && y 0) ^^ dot k (tail x) (tail y)) =
      ((x 0 && y 0) ^^ sumBits (fun i=>x i.succ && y i.succ) (indices k))
    rw [ih]
    rfl

theorem sum_basis {k : Nat} (x : Word k) : sumWords (fun i=>scaled (x i) (unit i)) (indices k)=x := by
  funext j
  rw [sum_eval]
  have e := sumBits_only (f:=fun t=>scaled (x t) (unit t) j) (indices_nd k) (indices_mem j)
    (fun t _ ne=>by rw [scaled_apply,unit_off ne,Bool.and_false])
  rw [e,scaled_apply,unit_at rfl,Bool.and_true]

theorem additive_zero {k : Nat} {g : Word k→Bool} (h : Additive (wireSpace k) g) : g Zero=false := by
  have a := h Zero Zero
  change g (wireAdd Zero Zero)=(g Zero ^^ g Zero) at a
  rwa [wire_self,Bool.xor_self] at a

theorem additive_sum {k : Nat} {g : Word k→Bool} (h : Additive (wireSpace k) g) {α : Type}
    (f : α→Word k) (L : List α) : g (sumWords f L)=sumBits (fun a=>g (f a)) L := by
  induction L with
  | nil => exact additive_zero h
  | cons a L ih =>
    change g ((wireSpace k).add (f a) (sumWords f L))=(g (f a) ^^ sumBits (fun a=>g (f a)) L)
    rw [h,ih]

theorem additive_coefficients {k : Nat} {g : Word k→Bool} (h : Additive (wireSpace k) g) (x : Word k) :
    g x=dot k x (fun i=>g (unit i)) := by
  have e : g x=sumBits (fun i=>g (scaled (x i) (unit i))) (indices k) :=
    (congrArg g (sum_basis x).symm).trans (additive_sum h _ _)
  rw [e,dot_indices]
  congr 1
  funext i
  cases a : x i
  · exact additive_zero h
  · rfl

theorem sum_card_parity {α : Type} (f : α→Bool) (L : List α) :
    sumBits f L=false ↔ (L.filter f).length % 2=0 := by
  induction L with
  | nil => simp [sumBits]
  | cons a rest ih =>
    cases c : f a
    · simp only [sumBits,List.filter_cons,c,Bool.false_xor,ite_false,Bool.false_eq_true]
      exact ih
    · have possible : (rest.filter f).length % 2=0 ∨ (rest.filter f).length % 2=1 := by omega
      simp only [sumBits,List.filter_cons,c,ite_true,List.length_cons,Bool.true_xor]
      cases e : sumBits f rest with
      | false =>
        have n := ih.mp e
        constructor
        · intro bad; contradiction
        · intro k; omega
      | true =>
        have n : ¬(rest.filter f).length % 2=0 := fun z=>Bool.noConfusion (e.symm.trans (ih.mpr z))
        constructor
        · intro _; omega
        · intro _; rfl

end PNP29946.Binary

namespace PNP29946.Authentic
open PNP29946.Binary

abbrev F := ZMod 2
abbrev W (k : Nat) := Fin k → F
abbrev D (k : Nat) := W k →ₗ[F] F

def toBit (a : F) : Bool := decide (a≠0)
def ofBit (a : Bool) : F := if a then 1 else 0

theorem values (a : F) : a=0 ∨ a=1 := by
  change Fin 2 at a
  obtain ⟨n,hn⟩ := a
  have h : n=0 ∨ n=1 := by omega
  rcases h with h|h
  · left
    apply Fin.ext
    exact h
  · right
    apply Fin.ext
    exact h
@[simp] theorem bit_zero : toBit (0:F)=false := by decide
@[simp] theorem bit_one : toBit (1:F)=true := by decide
@[simp] theorem bit_round (a : Bool) : toBit (ofBit a)=a := by cases a <;> decide
@[simp] theorem mod_round (a : F) : ofBit (toBit a)=a := by rcases values a with rfl|rfl <;> decide
theorem bit_inj {a b : F} (h : toBit a=toBit b) : a=b := by
  simpa only [mod_round] using congrArg ofBit h

@[simp] theorem bit_eq_false (a : F) : toBit a=false ↔ a=0 := by rcases values a with rfl|rfl <;> decide

theorem bit_add (a b : F) : toBit (a+b)=(toBit a ^^ toBit b) := by
  rcases values a with rfl|rfl <;> rcases values b with rfl|rfl <;> decide
theorem bit_sub (a b : F) : toBit (a-b)=(toBit a ^^ toBit b) := by
  rcases values a with rfl|rfl <;> rcases values b with rfl|rfl <;> decide
theorem bit_mul (a b : F) : toBit (a*b)=(toBit a && toBit b) := by
  rcases values a with rfl|rfl <;> rcases values b with rfl|rfl <;> decide

def enc {k : Nat} (w : W k) : Word k := fun i=>toBit (w i)
def dec {k : Nat} (w : Word k) : W k := fun i=>ofBit (w i)

@[simp] theorem dec_enc {k : Nat} (x : W k) : dec (enc x)=x := by funext i; exact mod_round (x i)
@[simp] theorem enc_dec {k : Nat} (x : Word k) : enc (dec x)=x := by funext i; exact bit_round (x i)

theorem enc_add {k : Nat} (x y : W k) : enc (x+y)=wireAdd (enc x) (enc y) := by
  funext i
  exact bit_add (x i) (y i)
theorem dec_add {k : Nat} (x y : Word k) : dec (wireAdd x y)=dec x + dec y := by
  funext i
  apply bit_inj
  change toBit (ofBit (x i ^^ y i))=toBit (ofBit (x i)+ofBit (y i))
  simp only [bit_add,bit_round]
@[simp] theorem enc_zero {k : Nat} : enc (0:W k)=Binary.Zero := by funext i; exact bit_zero

def encFn {k : Nat} (f : W k→F) : Word k→Bool := fun x=>toBit (f (dec x))
def decFn {k : Nat} (f : Word k→Bool) : W k→F := fun x=>ofBit (f (enc x))

@[simp] theorem enc_eval {k : Nat} (f : W k→F) (x : W k) : encFn f (enc x)=toBit (f x) := by
  simp [encFn]
@[simp] theorem enclin_round {k : Nat} (f : Word k→Bool) : encFn (decFn f)=f := by
  funext i
  simp [encFn,decFn]

def zDiff {k : Nat} (f : W k→F) (u : W k) : W k→F := fun x=>f (x+u)-f x
def ZCubic {k : Nat} (f : W k→F) : Prop :=
  ∀ v : Fin 4→W k, ∀ x, ((List.ofFn v).foldl zDiff f) x=0

theorem enc_diff {k : Nat} (f : W k→F) (u : W k) :
    encFn (zDiff f u) = Binary.diff (wireSpace k) (enc u) (encFn f) := by
  funext x
  change toBit (f (dec x+u)-f (dec x)) =
    (toBit (f (dec (wireAdd x (enc u)))) ^^ toBit (f (dec x)))
  rw [dec_add,dec_enc,bit_sub]

theorem enc_fold {k : Nat} (L : List (W k)) (f : W k→F) :
    encFn (L.foldl zDiff f)=
      (L.map enc).foldl (fun g u=>Binary.diff (wireSpace k) u g) (encFn f) := by
  induction L generalizing f with
  | nil => rfl
  | cons u L ih => simp only [List.foldl_cons,List.map_cons,ih,enc_diff]

theorem degree_transport {k : Nat} (f : W k→F) :
    ZCubic f ↔ Low (wireSpace k) 3 (encFn f) := by
  rw [Binary.low_three_iff]
  constructor
  · intro h v x
    let u : Fin 4→W k := fun j=>dec (v j)
    have eq : (List.ofFn u).map enc=List.ofFn v := by simp [u,List.map_ofFn,Function.comp_def]
    have result := congrFun (enc_fold (List.ofFn u) f) x
    rw [eq] at result
    rw [←result]
    change toBit (((List.ofFn u).foldl zDiff f) (dec x))=false
    rw [h u]
    exact bit_zero
  · intro h u x
    let v : Fin 4→Word k := fun j=>enc (u j)
    have eq : (List.ofFn u).map enc=List.ofFn v := by rw [List.map_ofFn] <;> rfl
    have result := congrFun (enc_fold (List.ofFn u) f) (enc x)
    rw [eq,h v,enc_eval] at result
    exact (bit_eq_false _).mp result

def linearCoeffs {k : Nat} (a : D k) : Word k := fun i=>encFn a (unit i)

theorem enc_linear {k : Nat} (a : D k) (x : W k) :
    toBit (a x)=dot k (enc x) (linearCoeffs a) := by
  have hom : Additive (wireSpace k) (encFn a) := by
    intro u v
    change toBit (a (dec (wireAdd u v)))=(toBit (a (dec u)) ^^ toBit (a (dec v)))
    rw [dec_add,map_add,bit_add]
  change toBit (a x) = dot k (enc x) (fun i=>encFn (⇑a) (unit i))
  exact (enc_eval (⇑a) x).symm.trans (additive_coefficients hom (enc x))

def toLinear {k : Nat} (a : Word k) : D k where
  toFun x := ofBit (dot k (enc x) a)
  map_add' x y := by
    apply bit_inj
    change toBit (ofBit (dot k (enc (x+y)) a)) =
      toBit (ofBit (dot k (enc x) a) + ofBit (dot k (enc y) a))
    simp only [bit_add,bit_round,enc_add,dot_left_add]
  map_smul' c x := by
    rcases values c with rfl|rfl
    · change ofBit (dot k (enc ((0:F) • x)) a)=(0:F) • ofBit (dot k (enc x) a)
      simp [dot_zero,ofBit]
    · change ofBit (dot k (enc ((1:F) • x)) a)=(1:F) • ofBit (dot k (enc x) a)
      simp

theorem bit_toLinear {k : Nat} (a : Word k) (x : W k) :
    toBit (toLinear a x)=dot k (enc x) a := bit_round _

def runMod {k d : Nat} (a : Fin d→Nat→D k) (x : W k) : Nat :=
  (List.finRange d).foldl (fun h j=>2*h+(if a j h x=0 then 0 else 1)) 0

theorem run_transport {k d : Nat} (a : Fin d→Nat→D k) (q : Fin d→Nat→Word k)
    (rel : ∀ j t x, toBit (a j t x)=dot k (enc x) (q j t)) (x : W k) :
    runMod a x=run q (enc x) := by
  have eq : (fun (h : Nat) (j : Fin d)=>2*h+(if a j h x=0 then 0 else 1)) =
      (fun h j=>2*h+(if dot k (enc x) (q j h) then 1 else 0)) := by
    funext h j
    rw [←rel j h x]
    rcases values (a j h x) with z|z
    · rw [z]; simp
    · rw [z]; simp
  unfold runMod run
  rw [eq] <;> rfl

def outMod {k : Nat} (hk : 0<k) (name c₁ c₂ : Bool→W k) (x : W k) (b : Bool) : W k :=
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W k) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W k) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W k) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let z := mix (gap b) (rot (spin b) x + name b)
  let y := step z + rot (if b then 4 else 0) x + c₁ b
  step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b

def params {k : Nat} (name c₁ c₂ : Bool→W k) : Params k :=
  ⟨enc (name false),enc (c₁ false),enc (c₂ false)⟩

theorem out_transport {k : Nat} (hk : 0<k) (big : 9≤k) (name c₁ c₂ : Bool→W k) (x : W k) (i : Fin k) :
    toBit (outMod hk name c₁ c₂ x false i)=outFalse hk (params name c₁ c₂) (enc x) i := by
  have one : 1 % k=1 := Nat.mod_eq_of_lt (by omega)
  simp only [outMod, Bool.false_eq_true, ite_false, Pi.add_apply, bit_add, bit_mul, bit_one,
    outFalse, wireAdd, step, mm, mix, yy, zz, PNP29946.Binary.rot, fwd, back, params, enc, idx, one]

def Fit {k : Nat} (hk : 0<k) (mark : Fin k→Bool×Bool) (d : Nat) (name c₁ c₂ : Bool→W k) : Prop :=
  ∃ (ask : Fin d→Nat→D k) (readout : Nat→Bool→Fin k→W k→F),
    (∀ h b i, ZCubic (readout h b i)) ∧
      ∀ x b i, (if b then (mark i).2 else (mark i).1)=true →
        outMod hk name c₁ c₂ x b i = readout (runMod ask x) b i x

theorem fits_transport {k : Nat} (hk : 0<k) (big : 9≤k) (P : Word k) (d : Nat)
    (name c₁ c₂ : Bool→W k) :
    Fit hk (fun i=>(P i,false)) d name c₁ c₂ ↔ Binary.Fits hk (params name c₁ c₂) P d := by
  constructor
  · rintro ⟨ask,r,complete,correct⟩
    let q : Fin d→Nat→Word k := fun j h=>linearCoeffs (ask j h)
    let ro := fun h i=>encFn (r h false i)
    refine ⟨q,ro,(fun h i=>(degree_transport _).mp (complete h false i)),?_⟩
    intro x i pi
    let z := dec x
    have hz : enc z=x := enc_dec x
    have a := correct z false i pi
    have pe := congrArg toBit a
    rw [out_transport hk big,run_transport ask q (fun j r x=>enc_linear (ask j r) x)] at pe
    change outFalse hk (params name c₁ c₂) (enc z) i =
      toBit (r (run q (enc z)) false i z) at pe
    rw [←hz]
    simpa only [ro,enc_eval] using pe
  · rintro ⟨q,r,complete,correct⟩
    let ask : Fin d→Nat→D k := fun j h=>toLinear (q j h)
    let ro : Nat→Bool→Fin k→W k→F := fun h b i=>if b then fun _=>0 else decFn (r h i)
    refine ⟨ask,ro,?_ ,?_⟩
    · intro h b i
      apply (degree_transport _).mpr
      cases b
      · simpa only [ro,Bool.false_eq_true,ite_false,enclin_round] using complete h i
      · exact low_const 3 false
    · intro x b i pi
      cases b
      · apply bit_inj
        rw [out_transport hk big,run_transport ask q (fun j h x=>bit_toLinear (q j h) x)]
        change outFalse hk (params name c₁ c₂) (enc x) i = toBit (ofBit (r (run q (enc x)) i (enc x)))
        simpa only [bit_round] using correct (enc x) i pi
      · contradiction

end PNP29946.Authentic

namespace PNP29946.Authentic
open PNP29946.Binary

def setBits {k : Nat} (Q : Finset (Fin k)) : Word k := fun i=>decide (i∈Q)

def bitsSet {k : Nat} (w : Word k) : Finset (Fin k) := Finset.univ.filter (fun i=>w i=true)

@[simp] theorem set_round {k : Nat} (w : Word k) : setBits (bitsSet w)=w := by
  funext i
  cases h : w i <;> simp [setBits,bitsSet,h]

theorem marked_length {k : Nat} (P : Finset (Fin k)) : (marks (setBits P)).length=P.card := by
  have e : (marks (setBits P)).Perm P.toList := by
    apply (List.perm_ext_iff_of_nodup (marks_nd _) P.nodup_toList).mpr
    intro i
    simp [marks_mem,setBits]
  rw [e.length_eq,Finset.length_toList]

theorem decide_congr_eq (a b : Prop) [Decidable a] [Decidable b] :
    decide a=decide b ↔ (a↔b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha,hb]

theorem setBits_in {k : Nat} (P : Finset (Fin k)) (i : Fin k) : setBits P i=true ↔ i∈P := by
  change decide (i∈P)=true ↔ i∈P
  exact decide_eq_true_iff (p := i ∈ P)

theorem setBits_out {k : Nat} (P : Finset (Fin k)) (i : Fin k) : setBits P i=false ↔ i∉P := by
  change decide (i∈P)=false ↔ i∉P
  exact decide_eq_false_iff_not

theorem setBits_pair {k : Nat} (P : Finset (Fin k)) (i j : Fin k) :
    setBits P i=setBits P j ↔ (i∈P ↔ j∈P) :=
  decide_congr_eq (i∈P) (j∈P)

def ModGuards {k : Nat} (hk : 0<k) (P U : Finset (Fin k)) : Prop :=
  ∀ i ∈ P, idx hk (i.val+2) ∉ U ∧ idx hk (i.val+4) ∉ U ∧
    (idx hk (i.val+1) ∈ U ↔ idx hk (i.val+3) ∈ U) ∧
    (idx hk (i.val+3) ∈ U ↔ idx hk (i.val+5) ∈ U)

theorem guards_transport {k : Nat} (hk : 0<k) (P U : Finset (Fin k)) :
    Guards hk (setBits P) (setBits U) ↔ ModGuards hk P U := by
  constructor
  · intro A i hi
    obtain ⟨a,b,c,d⟩ := A i ((setBits_in P i).mpr hi)
    exact ⟨(setBits_out _ _).mp a,(setBits_out _ _).mp b,
      (setBits_pair _ _ _).mp c,(setBits_pair _ _ _).mp d⟩
  · intro A i hi
    obtain ⟨a,b,c,d⟩ := A i ((setBits_in P i).mp hi)
    exact ⟨(setBits_out _ _).mpr a,(setBits_out _ _).mpr b,
      (setBits_pair _ _ _).mpr c,(setBits_pair _ _ _).mpr d⟩

theorem parity_transport {k : Nat} (U : Finset (Fin k)) (r : Fin 3) :
    dot k (setBits U) (periodic r)=false ↔ (U.filter (fun j=>j.val % 3≠r.val)).card % 2=0 := by
  let L := (indices k).filter (fun j=>setBits U j && periodic r j)
  let S := U.filter (fun j=>j.val % 3≠r.val)
  have e : L.Perm S.toList := by
    apply (List.perm_ext_iff_of_nodup (List.filter_sublist.nodup (indices_nd _)) S.nodup_toList).mpr
    intro j
    simp [L,S,setBits,periodic,indices_mem,beq_eq_false_iff_ne]
  rw [dot_indices,sum_card_parity]
  change L.length % 2=0 ↔ S.card % 2=0
  rw [e.length_eq,Finset.length_toList]

def ModPasses {k : Nat} (hk : 0<k) (P : Finset (Fin k)) (r : Fin 3) : Prop :=
  ∀ U : Finset (Fin k), ModGuards hk P U → (U.filter (fun j=>j.val % 3≠r.val)).card % 2=0

theorem passes_transport {k : Nat} (hk : 0<k) (P : Finset (Fin k)) (r : Fin 3) :
    Passes hk (setBits P) r ↔ ModPasses hk P r := by
  constructor
  · intro b U g
    exact (parity_transport U r).mp (b (setBits U) ((guards_transport hk P U).mpr g))
  · intro b w g
    let U := bitsSet w
    have eq : setBits U=w := set_round w
    rw [←eq] at g ⊢
    exact (parity_transport U r).mpr (b U ((guards_transport hk P U).mp g))

def ModOrbit {k : Nat} (P : Finset (Fin k)) : Prop :=
  4∣k ∧ ∃ a : Fin 4, ∀ i : Fin k, i∈P ↔ i.val % 4=a.val

theorem orbit_transport {k : Nat} (P : Finset (Fin k)) :
  OrbitFour.orbit (setBits P) ↔ ModOrbit P := by simp [OrbitFour.orbit,ModOrbit,setBits]

def ModSep {k : Nat} (hk : 0<k) (P : Finset (Fin k)) : Prop :=
  ∀ i ∈ P, idx hk (i.val+1) ∉ P ∧ idx hk (i.val+2) ∉ P ∧ idx hk (i.val+3) ∉ P

theorem sep_transport {k : Nat} (hk : 0<k) (P : Finset (Fin k)) :
    OrbitFour.separated hk (setBits P) ↔ ModSep hk P := by
  constructor
  · intro A i hi
    obtain ⟨a,b,c⟩ := A i ((setBits_in P i).mpr hi)
    exact ⟨(setBits_out _ _).mp a,(setBits_out _ _).mp b,(setBits_out _ _).mp c⟩
  · intro A i hi
    obtain ⟨a,b,c⟩ := A i ((setBits_in P i).mp hi)
    exact ⟨(setBits_out _ _).mpr a,(setBits_out _ _).mpr b,(setBits_out _ _).mpr c⟩

theorem official_rank {k : Nat} (hk : 0<k) (big : 9≤k) (P : Finset (Fin k)) (d : Nat)
    (name c₁ c₂ : Bool→W k) (sep : ModSep hk P) :
    Fit hk (fun i=>(decide (i∈P), false)) d name c₁ c₂ ↔
      P.card≤d ∨ (P.card≤d+1 ∧ (ModOrbit P ∨ (3∣k ∧ ∃ r, ModPasses hk P r))) := by
  change Fit hk (fun i=>(setBits P i,false)) d name c₁ c₂ ↔ _
  rw [fits_transport hk big,fit_rank_exact hk big _ ((sep_transport hk P).mpr sep),marked_length,
    orbit_transport]
  simp only [passes_transport]

end PNP29946.Authentic

end PEqualNP.Outside.L_meta_29946_aux

theorem PEqualNP.Outside.L_meta_29946 :
let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
∀ (k : ℕ) (hk : 0 < k), 9 ≤ k →
  ∀ (P : Finset (Fin k)) (d : ℕ) (name c₁ c₂ : Bool → Fin k → ZMod 2),
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let mark := fun i : Fin k => (decide (i ∈ P), false)
    let orbit := 4 ∣ k ∧ ∃ a : Fin 4, ∀ i : Fin k, i ∈ P ↔ i.val % 4 = a.val
    let passes := fun r : Fin 3 => ∀ U : Finset (Fin k),
      (∀ i ∈ P, ix (i.val + 2) ∉ U ∧ ix (i.val + 4) ∉ U ∧
        (ix (i.val + 1) ∈ U ↔ ix (i.val + 3) ∈ U) ∧
        (ix (i.val + 3) ∈ U ↔ ix (i.val + 5) ∈ U)) →
        (U.filter (fun j => j.val % 3 ≠ r.val)).card % 2 = 0
    (∀ i ∈ P, ix (i.val + 1) ∉ P ∧ ix (i.val + 2) ∉ P ∧ ix (i.val + 3) ∉ P) →
      (fits k hk mark d name c₁ c₂ ↔
        P.card ≤ d ∨ (P.card ≤ d + 1 ∧ (orbit ∨ (3 ∣ k ∧ ∃ r, passes r))))
 := by
  dsimp only
  intro k hk big P d name c₁ c₂
  intro sep
  exact PEqualNP.Outside.L_meta_29946_aux.PNP29946.Authentic.official_rank hk big P d name c₁ c₂ sep
