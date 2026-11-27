import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_27599_aux
namespace Lower26514
abbrev Fn (n : Nat) := (Fin n → Bool) → Bool
def start {n : Nat} : List (Fn n) := [fun _ => false,fun _ => true] ++ (List.ofFn (fun i : Fin n => [fun x => x i,fun x => !(x i)] )).flatten
inductive Run {n : Nat} : List (Fn n) → Nat → Fn n → Prop
  | stop {v k t} : t ∈ v → Run v k t
  | step {v k t a b} : a ∈ v → b ∈ v → Run (v ++ [fun x => a x && b x,fun x => !(a x && b x)]) k t → Run v (k+1) t
def six : Fn 6 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)
def five : Fn 5 := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
end Lower26514

namespace Pin26514
open Lower26514
abbrev inv {n} (f : Fn n) : Fn n := fun x => !(f x)
abbrev meet {n} (a b : Fn n) : Fn n := fun x => a x && b x
abbrev Has {n} (S : List (Fn n)) (f : Fn n) := f∈S ∧ inv f∈S
abbrev Both {n} (S : List (Fn n)) := Has S (fun _ => false)
abbrev Const {n} (f : Fn n) := ∃ c, ∀ x, f x = c
def append {n} (S : List (Fn n)) (a b : Fn n) := S ++ [meet a b,inv (meet a b)]
private theorem neg2 {n} (f : Fn n) : inv (inv f)=f := by funext x; simp
private theorem swap {n S} {f : Fn n} (h : Has S f) : Has S (inv f) := ⟨h.2,by rw [neg2]; exact h.1⟩
private theorem old {n S} {f a b : Fn n} (h : Has S f) : Has (append S a b) f := ⟨List.mem_append_left _ h.1,List.mem_append_left _ h.2⟩
private theorem fresh {n} (S : List (Fn n)) (a b : Fn n) : Has (append S a b) (meet a b) := by constructor <;> apply List.mem_append_right <;> simp
private theorem extend {n m} {S : List (Fn n)} {D : List (Fn m)} {a b : Fn n} (p : (Fin m → Bool) → (Fin n → Bool)) (base : ∀ f∈S,Has D (f ∘ p)) (h : Has D ((meet a b) ∘ p)) : ∀ f∈append S a b, Has D (f ∘ p) := by
  intro f hf; rcases List.mem_append.mp hf with hf|hf; exact base _ hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact h; exact swap h
private theorem absorb {n} {S : List (Fn n)} {a b : Fn n} (z : Both S) (ha : Has S a) (hb : Has S b) (h : Const a ∨ Const b) : Has S (meet a b) := by
  rcases h with ⟨c,h⟩|⟨c,h⟩ <;> cases c
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet,h]] using z
  · simpa only [show meet a b = b by funext x; simp [meet,h]] using hb
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet,h]] using z
  · simpa only [show meet a b = a by funext x; simp [meet,h]] using ha

theorem weaken {n S k} {f : Fn n} (h : Run S k f) : ∀ {l},k≤l → Run S l f := by
  induction h with
  | stop ht => intro l hl; exact .stop ht
  | @step v k t a b ha hb h ih => intro l hl; obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l≠0); exact .step ha hb (ih (by omega))

theorem project {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool)) (D : List (Fn m)) (base : ∀ f∈S, Has D (f ∘ p)) : Run D k (t ∘ p) := by
  induction h generalizing D with
  | stop ht => exact .stop (base _ ht).1
  | @step v k t a b ha hb h ih =>
    apply Run.step (base _ ha).1 (base _ hb).1; apply ih; exact extend p (fun f hf => old (base f hf)) (fresh _ _ _)


theorem save {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool)) (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b)) (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ¬Const (t ∘ p)) (bank : ∀ f∈S, Stable f ∨ Const (f ∘ p))
    (D : List (Fn m)) (constants : Both D) (base : ∀ f∈S, Has D (f ∘ p)) : ∃ l, l+1≤k ∧ Run D l (t ∘ p) := by
  classical
  induction h generalizing D with
  | stop ht => exact False.elim ((bank _ ht).elim nt nc)
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f∈append v a b,Stable f ∨ Const (f ∘ p) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf; exact bank _ hf
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨l,hl,hr⟩ := ih nt nc next _ (old constants) (extend p (fun f hf => old (base f hf)) (fresh _ _ _))
      exact ⟨l+1,by omega,.step (base _ ha).1 (base _ hb).1 hr⟩
    · have ca : Const (a ∘ p) ∨ Const (b ∘ p) := by rcases bank a ha with h|h <;> rcases bank b hb with j|j <;> tauto
      have hit := absorb constants (base _ ha) (base _ hb) ca
      exact ⟨k,by omega,project h p D (extend p base hit)⟩

theorem saveTwo {n m S k} {t : Fn n} (h : Run S k t) (p : Bool → (Fin m → Bool) → (Fin n → Bool)) (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b)) (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ∀ c, ¬Const (t ∘ p c))
    (bank : ∀ f∈S, Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x)=false))
    (D : Bool → List (Fn m)) (constants : ∀ c, Both (D c)) (base : ∀ c f, f∈S → Has (D c) (f ∘ p c)) :
    ∃ c l, l+2≤k ∧ Run (D c) l (t ∘ p c) := by
  classical
  induction h generalizing D with
  | stop ht => rcases bank _ ht with ht|ht; exact (nt ht).elim; exact (nc false (ht.1 false)).elim
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f∈append v a b,Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x)=false) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf; exact bank _ hf
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨c,l,hl,hr⟩ := ih nt nc next (fun c => append (D c) (a ∘ p c) (b ∘ p c)) (fun c => old (constants c)) (fun c => extend (p c) (fun f hf => old (base c f hf)) (fresh _ _ _))
      exact ⟨c,l+1,by omega,.step (base c _ ha).1 (base c _ hb).1 hr⟩
    · have force : ∃ c, ∀ x, meet a b (p c x)=false := by
        by_cases sa : Stable a
        · obtain ⟨c,hc⟩ := ((bank _ hb).resolve_left (fun h => sab ⟨sa,h⟩)).2
          exact ⟨c,fun x => by simp [meet,hc]⟩
        · obtain ⟨c,hc⟩ := ((bank _ ha).resolve_left sa).2
          exact ⟨c,fun x => by simp [meet,hc]⟩
      obtain ⟨c,hc⟩ := force
      have hit : (meet a b ∘ p c) = fun _ => false := funext hc
      have next : ∀ f∈append v a b,Stable f ∨ Const (f ∘ p c) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf
        · exact (bank _ hf).imp_right (fun h => h.1 c)
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl
          · exact Or.inr ⟨false,hc⟩
          · exact Or.inr ⟨true,fun x => by simp [Function.comp_apply,inv,hc]⟩
      obtain ⟨l,hl,hr⟩ := save h (p c) Stable nand neg nt (nc c) next (D c) (constants c) (extend (p c) (base c) (hit ▸ constants c))
      exact ⟨c,l,by omega,hr⟩
end Pin26514

namespace Coord26514
open Lower26514 Pin26514
abbrev Code (m : Nat) := Option (Fin m)
def pin {n m} (c : Fin n → Code m) (v : Bool) (x : Fin m → Bool) (i : Fin n) := (c i).elim v x
def stable {n m} (c : Fin n → Code m) (f : Fn n) := ∀ x, f (pin c false x)=f (pin c true x)
private theorem both {n} : Both (@start n) := ⟨by simp [start],by change (fun _ => true)∈_; simp [start]⟩
private theorem lit {n} (i : Fin n) : Has start (fun x => x i) := by
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr <;> exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp⟩
private theorem casesStart {n} {f : Fn n} (h : f∈start) : (∃ b, f=fun _ => b) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=(fun x => !(x i)) := by
  rcases List.mem_append.mp h with h|h
  · simp at h; rcases h with rfl|rfl; exact Or.inl ⟨false,rfl⟩; exact Or.inl ⟨true,rfl⟩
  · obtain ⟨l,hl,h⟩ := List.mem_flatten.mp h; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; exact Or.inr ⟨i,by simpa using h⟩
private theorem negHas {n S} {f : Fn n} (h : Has S f) : Has S (inv f) := ⟨h.2,by rw [show inv (inv f) = f by funext x; simp [inv]]; exact h.1⟩
private theorem available {n m} (c : Fin n → Code m) (v : Bool) (f : Fn n) (hf : f∈start) : Has start (f ∘ pin c v) := by
  rcases casesStart hf with ⟨b,rfl⟩|⟨i,hi⟩
  · cases b; exact both; exact negHas both
  · cases h : c i with
    | none => rcases hi with rfl|rfl <;> cases v <;> simp only [Function.comp_def,pin,h,Option.elim,Bool.not_true,Bool.not_false] <;> first | exact both | exact negHas both
    | some j => rcases hi with rfl|rfl <;> simp only [Function.comp_def,pin,h,Option.elim] <;> first | exact lit j | exact negHas (lit j)
private theorem bank {n m} (c : Fin n → Code m) (f : Fn n) (hf : f∈start) : stable c f ∨ ((∀ b, Const (f ∘ pin c b)) ∧ ∃ b, ∀ x, f (pin c b x)=false) := by
  rcases casesStart hf with ⟨b,rfl⟩|⟨i,h⟩
  · exact Or.inl fun _ => rfl
  · cases he : c i with
    | some j => rcases h with rfl|rfl <;> exact Or.inl (by simp [stable,pin,he])
    | none => rcases h with rfl|rfl
              · exact Or.inr ⟨fun b => ⟨b,by simp [pin,he,Function.comp_def]⟩,false,by simp [pin,he]⟩
              · exact Or.inr ⟨fun b => ⟨!b,by simp [pin,he,Function.comp_def]⟩,true,by simp [pin,he]⟩
private theorem sand {n m} (c : Fin n → Code m) (a b : Fn n) (ha : stable c a) (hb : stable c b) : stable c (meet a b) := by intro x; simp only [meet,ha x,hb x]
private theorem sneg {n m} (c : Fin n → Code m) (a : Fn n) (h : stable c a) : stable c (inv a) := by intro x; simp only [inv,h x]
theorem one {n m k} (c : Fin n → Code m) (v : Bool) (f : Fn n) (h : Run start k f) (dep : ¬stable c f) (nc : ¬Const (f ∘ pin c v)) : ∃ l,l+1≤k ∧ Run start l (f ∘ pin c v) :=
  save h _ _ (sand c) (sneg c) dep nc (fun a ha => (bank c a ha).imp_right fun z => z.1 v) _ both (available c v)
theorem two {n m k} (c : Fin n → Code m) (f : Fn n) (h : Run start k f) (dep : ¬stable c f) (nc : ∀ b,¬Const (f ∘ pin c b)) : ∃ b l,l+2≤k ∧ Run start l (f ∘ pin c b) :=
  saveTwo h _ _ (sand c) (sneg c) dep nc (bank c) _ (fun _ => both) (available c)
end Coord26514


namespace Prefix27599
open PEqualNP.CircuitLowerBounds Lower26514

private def neg {n} (f : Fn n) : Fn n := fun x => !(f x)
private def Dual {n} (v : List (Fn n)) (f : Fn n) := f ∈ v ∧ neg f ∈ v
private abbrev zeroF {n} : Fn n := fun _ => false
private theorem dualNeg {n} {v : List (Fn n)} {f} (h : Dual v f) : Dual v (neg f) := by
  have e : neg (neg f) = f := by funext x; simp [neg]
  exact ⟨h.2, e.symm ▸ h.1⟩
private theorem dualIncl {n} {v w : List (Fn n)} {f} (sub : v ⊆ w) (h : Dual v f) : Dual w f := ⟨sub h.1,sub h.2⟩
private theorem raise {n} {v : List (Fn n)} {k t} (h : Run v k t) : Run v (k+1) t := by
  induction h with
  | stop hm => exact .stop hm
  | step ha hb _ ih => exact .step ha hb ih

private def value {n} (ws : List (Fn n)) (g : Gate) : Fn n := fun x =>
  g.op.eval (g.inputs.map fun i => (ws.getD i zeroF) x)
private def extend {n} (ws : List (Fn n)) (g : Gate) := ws ++ [value ws g]
private def scalar (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
private abbrev Good (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
private def cost (g : Gate) := match g.op with | .not => 0 | _ => 1

private theorem takeGate {n k} {v ws : List (Fn n)} {t : Fn n} (g : Gate) (ok : Good g)
    (hz : Dual v zeroF) (hw : ∀ i, Dual v (ws.getD i zeroF))
    (cont : ∀ u : List (Fn n), v ⊆ u → Dual u (value ws g) → Run u k t) : Run v (k+cost g) t := by
  rcases g with ⟨op,ins⟩
  obtain ⟨hOp,hlen⟩ := ok
  cases ins with
  | nil => rcases hOp with rfl|rfl|rfl
           · exact raise (cont v (fun _ h => h) (dualNeg hz))
           · exact raise (cont v (fun _ h => h) hz)
           · exact cont v (fun _ h => h) (dualNeg hz)
  | cons a l => cases l with
    | nil => rcases hOp with rfl|rfl|rfl
             · apply raise; apply cont _ (fun _ h => h)
               convert hw a using 1; funext x; simp [value,GateOp.eval]
             · apply raise; apply cont _ (fun _ h => h)
               convert hw a using 1; funext x; simp [value,GateOp.eval]
             · exact cont v (fun _ h => h) (dualNeg (hw a))
    | cons b tail =>
      have hnil : tail = [] := by simpa using hlen
      subst tail
      rcases hOp with rfl|rfl|rfl
      · apply Run.step (hw a).1 (hw b).1
        apply cont _ (List.subset_append_left ..)
        constructor <;> apply List.mem_append_right <;> simp only [List.mem_cons,List.not_mem_nil,or_false]
        · left; funext x; simp [value,GateOp.eval]
        · right; funext x; simp [value,neg,GateOp.eval]
      · apply Run.step (hw a).2 (hw b).2
        apply cont _ (List.subset_append_left ..)
        constructor <;> apply List.mem_append_right <;> simp only [List.mem_cons,List.not_mem_nil,or_false]
        · right; funext x; simp [value,neg,GateOp.eval]
        · left; funext x; simp [value,neg,GateOp.eval]
      · exact cont v (fun _ h => h) (dualNeg (hw a))

private theorem avail {n} {v ws : List (Fn n)} (hz : Dual v zeroF) (hw : ∀ f ∈ ws, Dual v f)
    (i : Nat) : Dual v (ws.getD i zeroF) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · simpa [List.getD_eq_getElem?_getD,h] using hz

private theorem compile {n} (gs : List Gate) (o : Nat) (ws v : List (Fn n))
    (hgood : ∀ g ∈ gs, Good g) (hz : Dual v zeroF) (hw : ∀ f ∈ ws, Dual v f) :
    Run v (gs.map cost).sum ((gs.foldl extend ws).getD o zeroF) := by
  induction gs generalizing v ws with
  | nil => exact .stop (avail hz hw o).1
  | cons g gs ih =>
    rw [List.map_cons,List.sum_cons,Nat.add_comm,List.foldl_cons]
    apply takeGate g (hgood _ List.mem_cons_self) hz (avail hz hw)
    intro u sub hval
    apply ih _ _ (fun q hq => hgood q (List.mem_cons_of_mem _ hq)) (dualIncl sub hz)
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · exact dualIncl sub (hw _ h)
    · obtain rfl := List.mem_singleton.mp h; exact hval

private theorem readMap {n} (x : Fin n → Bool) (ws : List (Fn n)) (i : Nat) :
    (ws.map (fun f => f x)).getD i false = ws.getD i zeroF x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases ws[i]? <;> rfl
private theorem foldMap {n} (x : Fin n → Bool) (gs : List Gate) (ws : List (Fn n)) :
    (gs.foldl extend ws).map (fun f => f x) = gs.foldl scalar (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons,ih,extend,List.map_append,List.map_cons,List.map_nil,scalar,value,readMap]

private theorem cost_le (gs : List Gate) : (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih => cases g with | mk op ins => cases op <;> simp [cost] at * <;> omega

def perm (x : Fin 9 → Bool) := ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
def plug (y : Fin 8 → Bool) : Fin 9 → Bool := ![true,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7]
def residual : Fn 8 := perm ∘ plug
private def orig : List (Fn 9) := List.ofFn (fun i : Fin 9 => fun x => x i) ++ [fun x => x 0 || x 1]
private def bank : List (Fn 9) := start ++ [fun x => x 0 || x 1,fun x => !(x 0 || x 1),fun x => x 0 || x 3,fun x => !(x 0 || x 3)]
private def off (y : Fin 8 → Bool) : Fin 9 → Bool := ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7]
private def stable (f : Fn 9) := ∀ x, f (plug x)=f (off x)

private theorem lit {n} (i : Fin n) : Dual start (fun x => x i) := by
  have hm : [fun x : Fin n → Bool => x i, fun x => !(x i)] ∈ List.ofFn (fun j : Fin n => [fun x => x j,fun x => !(x j)]) := List.mem_ofFn.mpr ⟨i,rfl⟩
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr
  · exact ⟨_,hm,List.mem_cons_self⟩
  · exact ⟨_,hm,List.mem_cons_of_mem _ List.mem_cons_self⟩
private theorem each (Q : Fn 9 → Prop) (z : Q zeroF) (nn : ∀ f,Q f → Q (neg f)) (raw : ∀ i : Fin 9,Q (fun x => x i)) (l : Q (fun x => x 0 || x 1)) (r : Q (fun x => x 0 || x 3)) : ∀ f∈bank,Q f := by
  intro f h; rcases List.mem_append.mp h with h|h
  · rcases List.mem_append.mp h with h|h
    · simp at h; rcases h with rfl|rfl; exact z; exact nn _ z
    · obtain ⟨ls,hm,h⟩ := List.mem_flatten.mp h; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      simp at h; rcases h with rfl|rfl; exact raw i; exact nn _ (raw i)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl|rfl|rfl; exact l; exact nn _ l; exact r; exact nn _ r
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem pinPrefixStrong (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (sz : C.size ≤ 12)
    (rep : ∀ x, C.eval (List.ofFn x) = perm x) (h0 : C.gates.head? = some ⟨.or,[0,1]⟩) : Run start 10 residual := by
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil => contradiction
  | cons g tail =>
      obtain rfl : g = ⟨.or,[0,1]⟩ := Option.some.inj h0
      have ht : ∀ g∈tail, Good g := fun g hg => fan g (List.mem_cons_of_mem _ hg)
      have hz : Dual bank zeroF := ⟨List.mem_append_left _ List.mem_cons_self,List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have availBank : ∀ f∈orig, Dual bank f := by
        intro f hf; rcases List.mem_append.mp hf with hr|hs
        · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact dualIncl (List.subset_append_left ..) (lit i)
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl <;> constructor <;> apply List.mem_append_right <;> simp only [List.mem_cons,List.not_mem_nil,or_false,neg] <;> tauto
      have h := compile tail o orig bank ht hz availBank
      have eq : (tail.foldl extend orig).getD o zeroF = perm := by
        have inputs : ∀ x : Fin 9 → Bool, orig.map (fun f => f x) = scalar (List.ofFn x) ⟨.or,[0,1]⟩ := by decide +kernel
        funext x; rw [←readMap,foldMap,inputs]; exact rep x
      rw [eq] at h
      have dep : ¬stable perm := by unfold stable; decide +kernel
      have nc : ¬Pin26514.Const (perm ∘ plug) := by unfold Pin26514.Const; decide +kernel
      have all : ∀ f∈bank,stable f ∨ Pin26514.Const (f ∘ plug) := by
        apply each
        · exact Or.inl fun _ => rfl
        · intro f hf; rcases hf with h|⟨c,h⟩
          · exact Or.inl fun x => congrArg Bool.not (h x)
          · exact Or.inr ⟨!c,fun x => congrArg Bool.not (h x)⟩
        · intro i; fin_cases i <;> first | exact Or.inl fun _ => rfl | exact Or.inr ⟨true,fun _ => rfl⟩
        · exact Or.inr ⟨true,fun x => by simp [plug]⟩
        · exact Or.inr ⟨true,fun x => by simp [plug]⟩
      have z' : Dual (@start 8) zeroF := ⟨List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self⟩
      have base : ∀ f∈bank, Pin26514.Has start (f ∘ plug) := by
        apply each
        · exact z'
        · intro f hf; exact dualNeg hf
        · intro i; fin_cases i <;> first | exact dualNeg z' | exact lit 0 | exact lit 1 | exact lit 2 | exact lit 3 | exact lit 4 | exact lit 5 | exact lit 6 | exact lit 7
        · change Dual start ((fun x : Fin 9 → Bool => x 0 || x 1) ∘ plug)
          rw [show (fun x : Fin 9 → Bool => x 0 || x 1) ∘ plug = neg (@zeroF 8) by funext x; simp [Function.comp_def,plug,neg,zeroF]]; exact dualNeg z'
        · change Dual start ((fun x : Fin 9 → Bool => x 0 || x 3) ∘ plug)
          rw [show (fun x : Fin 9 → Bool => x 0 || x 3) ∘ plug = neg (@zeroF 8) by funext x; simp [Function.comp_def,plug,neg,zeroF]]; exact dualNeg z'
      have z : Pin26514.Both (@start 8) := ⟨List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self⟩
      obtain ⟨l,hl,small⟩ := Pin26514.save h plug stable (fun a b ha hb x => by simp only [Pin26514.meet,ha x,hb x]) (fun f hf x => by simp only [Pin26514.inv,hf x]) dep nc all start z base
      have bound := cost_le tail; change tail.length+1 ≤ 12 at sz
      exact Pin26514.weaken small (by omega)
end Prefix27599

namespace Residual27743Kernel


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev Wire := Bool × ℕ
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def zero : Wire := (false,0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flip (a : Wire) : Wire := (!a.1,a.2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def reps (w : List Wire) := w.map Prod.snd
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)






open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def separation (m a : ℕ) := a ^^^ (a >>> m)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def full (m : ℕ) := (1 <<< m)-1
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def enough (m c : ℕ) := (c &&& full m) == full m
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]






set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))






set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all


end Residual27743Kernel
namespace Residual27743
open Lower26514

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def residual : Fn 8 := fun x =>
  (x 3 && x 7) || (x 4 && x 6) || (x 0 && x 2 && x 7) ||
  (x 0 && x 4 && x 5) || (x 1 && x 2 && x 6) || (x 1 && x 3 && x 5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def first : Fin 8 → Coord26514.Code 7 :=
  ![none,some 0,some 1,some 2,some 3,some 4,some 5,some 6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def minor : Fn 7 := fun x =>
  (x 2 && x 6) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 4) ||
  (x 0 && x 1 && x 5) || (x 0 && x 2 && x 4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cols : Fin 7 → Nat := ![
  0x38e38f0c24f1f0e27cdc71c676dc71c786003878301e6e38e33b6,
  0x9249115e39713ae3f1f81f878e000000071c381c71f8fc0fc3c7,
  0x1249222afc27fc0fc45ffe007f000000007e03fe07e00fff003f8,
  0x24924ff0494a255489bfffff80000007f800000000000fffffc00,
  0x3f03f440fff8400fffe4924a921f81f8007ffc0007fff00000000,
  0x3ffc0880fffffff010092495205ffe00007ffffff800000000000,
  0x3fffffff92048a09221249204dbfffffff8000000000000000000]

open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev rows (j : Nat) (i : Fin 7) := (cols i).testBit j
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def bank := 0 :: List.ofFn cols
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Covered (av : List Nat) (v : List (Fn 7)) := ∀ f∈v, ∃ w : Wire, w.2 ∈ av ∧ ∀ j, read j w = f (rows j)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem covStart : Covered bank Lower26514.start := by
  intro f hf
  rcases List.mem_append.mp hf with hc|hl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl
    · exact ⟨zero,by simp [zero,bank],fun j => read_zero j⟩
    · exact ⟨flip zero,by simp [zero,Residual27743Kernel.flip,bank],fun j => by simp [read_flip,read_zero]⟩
  · obtain ⟨l,hl,hf⟩ := List.mem_flatten.mp hl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    have mem : cols i∈bank := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl
    · exact ⟨(false,cols i),mem,fun j => by simp [Residual27743Kernel.read,rows]⟩
    · exact ⟨(true,cols i),mem,fun j => by simp [Residual27743Kernel.read,rows]⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem possibleOfRun {v : List (Fn 7)} {k : Nat} {t : Fn 7} (run : Run v k t)
    (diff : ∀ i<105, t (rows i) ≠ t (rows (105+i)))
    (av : List Nat) (cov : Covered av v) : Possible 105 k av := by
  induction run generalizing av with
  | stop mem =>
    obtain ⟨w, wm, hw⟩ := cov _ mem
    have good : Good 105 w.2 := by
      intro i hi eq
      have same : read i w = read (105+i) w := by simp [Residual27743Kernel.read,eq]
      exact diff i hi (by simpa only [hw] using same)
    have nz : w.2≠0 := by intro h; have hh:=good 0 (by decide); simp [h] at hh
    exact ⟨0,{w.2},Nat.zero_le _,Live.done good nz,by simpa using wm⟩
  | @step v k t a b ha hb rest ih =>
    obtain ⟨u,hu,ua⟩ := cov a ha
    obtain ⟨w,hw,wb⟩ := cov b hb
    let z := meet u w
    have ext : Covered (av++[z.2]) (v++[fun x => a x && b x,fun x => !(a x && b x)]) := by
      intro f hf
      rcases List.mem_append.mp hf with old|new
      · obtain ⟨c,hc,ce⟩ := cov f old
        exact ⟨c,List.mem_append_left _ hc,ce⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
        rcases new with rfl|rfl
        · exact ⟨z,by simp,fun j => by simp [z,read_meet,ua,wb]⟩
        · exact ⟨flip z,by simp [Residual27743Kernel.flip],fun j => by simp [read_flip,z,read_meet,ua,wb]⟩
    obtain ⟨l,S,le,live,sub⟩ := pullPaid (op_lt u.1 w.1) hu hw (ih diff _ ext)
    refine ⟨l,S,?_,live,sub⟩
    exact le.trans (Nat.add_le_add_left (Bool.toNat_le _) _)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem labels : ∀ i : Fin 105, minor (rows i.val) ≠ minor (rows (105+i.val)) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def Ban (m k : Nat) (v : List Nat) := ∀ n, n ≤ k → ¬Live m n v.toFinset
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem banOfSearch (k : Nat) (v : List Nat) (nd : v.Nodup) (no : search 105 k v = false) : Ban 105 k v := by
  intro n le ok
  exact Bool.noConfusion (no.symm.trans (complete 105 k ok le v rfl nd))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def missing (cs : List (List Nat)) (w : List Nat) : Bool := !(cs.contains (w.mergeSort))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem banOfChildren {k : Nat} (v : List Nat) (cs : List (List Nat)) (nd : v.Nodup)
    (blocked : (terminal 105 v || anyGate 105 k (missing cs) v) = false)
    (checked : ∀ w ∈ cs, Ban 105 k w) : Ban 105 (k+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,he,hg,hz⟩ := live
    have mem : a∈v := List.mem_toFinset.mp (he ▸ Finset.mem_singleton_self _)
    simp [ends hg v mem] at blocked
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,he,hd,_,_,ab,fresh,tail⟩ := live
    have ok := transition (go:=missing cs) hd ab fresh he nd (show n≤k by omega) tail (by
      intro w hw _
      by_contra! hm
      have inc : w.mergeSort ∈ cs := by simpa [missing] using hm
      apply checked _ inc n (by omega)
      have hv : w.mergeSort.toFinset = w.toFinset := by ext x; simp
      simpa only [hv,hw] using tail)
    simp [ok] at blocked
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w33 : Nat := 0x24f170e25ccc30c63240000000003878301e6e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w48 : Nat := 0x494a255489adb6df800000000000000000000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w52 : Nat := 0x619311a61d0d80d8304000000071c381c71f8fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w57 : Nat := 0x6c237406c44db60032000000007e03fe07e00fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w62 : Nat := 0x6df84006dde4924a92000000007ffc0007fff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w67 : Nat := 0x6dfb75f01009249520400000007ffffff800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w79 : Nat := 0xe007100e041f8000780000000070038007000fc0003c0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w89 : Nat := 0x11041020104091f81f8000000000000000000000fc0fc000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w99 : Nat := 0x22048022404801ffe00000000000000000000000fff00000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w118 : Nat := 0x91150000000e2f16816858a0000000000000071f8fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w127 : Nat := 0x1222a0000000fc456da005f0000000000000007e00fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w140 : Nat := 0x247700000000489b6db6a80000007f800000000000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w154 : Nat := 0x3870c000000026cd45142568001c786000000001e6e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w160 : Nat := 0x3f4400000000fefe4924a920001f80000000007fff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w166 : Nat := 0x3f77f00000009221249204da001ffff8000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w182 : Nat := 0x240115000713a0001b01b068e0000000000381c0000fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w192 : Nat := 0x48022a0007bc00001b6c006d000000000003fe00000fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w206 : Nat := 0x900bb000022550001b6db500000007f800000000000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w221 : Nat := 0xe00b0c0001b0e00018618464c070078600007830000e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w228 : Nat := 0xfc08800007bff00009249520407e00000003fff800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w234 : Nat := 0xfc0bbf00048a00001249204da07e07ff8000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w246 : Nat := 0x1041011c306030c03038038082000000071c381c70181c01c041
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w257 : Nat := 0x2082022d8060c0d80038e0009000000007e038607e001c700048
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w272 : Nat := 0x41040f0490a051481238e398000000078000000000001c71cc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w288 : Nat := 0x7007040db08000d8320820880038038007fc40007e1900000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w295 : Nat := 0x71c0080db0e0f100001041100038e00007fc787c800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w301 : Nat := 0x71c70f392040a090202082009238e38798000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w316 : Nat := 0x8208104209110a23c1c01c070c0000000000000001e0e00e0386
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w330 : Nat := 0x9009000e390000e3f048048100000000071c000071f800000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w343 : Nat := 0x9240000e39713a010090090204000000071c381c000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w355 : Nat := 0x9249005a29512aa3600000078e000000071c381c71f8000003c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w363 : Nat := 0x9249115039003a03b0001f800e000000001c001c01f8000fc007
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w369 : Nat := 0x9249115820402082212012048a00000000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w386 : Nat := 0x9249115e39713ae3f1f81f878e000000071c381c71f8fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w420 : Nat := 0x104102082421f002445c7000760000000000007800000e38003b0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w434 : Nat := 0x12012000fc20400fc444920012000000007e000007e0000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w447 : Nat := 0x12480000fc27fc000009240020000000007e03fe0000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w459 : Nat := 0x1249200ab425d80b444000007f000000007e03fe07e00000003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w467 : Nat := 0x1249222a1c20ec01c0407e0007000000000e007e00e0003f00038
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w473 : Nat := 0x1249222a90048809001248004d000000000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w490 : Nat := 0x1249222afc27fc0fc45ffe007f000000007e03fe07e00fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w521 : Nat := 0x1861800c24b1d0a27440000076dc71c006003878301e6000003b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w536 : Nat := 0x1b01b000b6b0400b76400000121f81f8007ffc0007fff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w550 : Nat := 0x1b6c0000b6b5daa010000000205ffe00007ffffff800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w563 : Nat := 0x1b6db00f92048a09220000004dbffff8078000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w579 : Nat := 0x1b6db33fffb7ffafff5ffff87fe00000007fc3ffc7ff8ffffc3ff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w592 : Nat := 0x20820f0000402040089c71c6000000078000000000000e38e3000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w606 : Nat := 0x240244404948000489a4924a80000000000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w619 : Nat := 0x24900880494a25500009249500000000000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w631 : Nat := 0x24924dd00148015009a001ff80000007f800000000000000ffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w638 : Nat := 0x24924ee00848245080a07e0780000007f80000000000003f03c00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w646 : Nat := 0x24924ff0000000000012492000000007f80000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w662 : Nat := 0x24924ff0494a255489bfffff80000007f800000000000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w693 : Nat := 0x28a28d0400d000e0388001c600dc71c786003800301e6000e3006
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w708 : Nat := 0x2d02d44003d800003ba0004a801f81f80001fc00001ff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w722 : Nat := 0x2db4088003d803f010000095005ffe000001fc01f800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w735 : Nat := 0x2db6ddd5020002002200012000bfffffff8000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w751 : Nat := 0x2db6dff5ebdf37febfbffffff8e00007f871c381c71f8ffffffc7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w761 : Nat := 0x30c30e080460e04040c07006061c71c7860038783000603803030
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w776 : Nat := 0x360364401c684001c0e01202821f81f8000e3c0000e0700000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w790 : Nat := 0x36d808801c68ec5000002405001ffe00000e3c7e3800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w803 : Nat := 0x36db6eea1000880100004800051fffffff8000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w819 : Nat := 0x36db6ffafd6ffd5fcdffffffff000007f87e03fe07e00fffffff8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w828 : Nat := 0x3803840024f040027cc41042121c01c000003800001e600000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w840 : Nat := 0x38e0080024f1f0e010082084205c7000000038783000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w853 : Nat := 0x38e38f0c0000800020104100449c71c7860000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w865 : Nat := 0x38e38f0c24f1f0e27cdc71c676dc71c786003878301e6e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w898 : Nat := 0x39e79f1de7f7f3ee7fdff1fe7efc71c78671fbf9f71feff8ff3f7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w910 : Nat := 0x3aebaf2efcf7fceffcdfffc67fdc71c7867e3bfe37fe6fffe33fe
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w929 : Nat := 0x3cf3cffc6dfbf5f6fdfffffff6dc71c7fe003878301e6ffffffb6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w945 : Nat := 0x3f000000fff8400010000000001f8000007ffc000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w957 : Nat := 0x3f03f4409200000922000000001f81f8000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w970 : Nat := 0x3f03f440fff8400fffe4924a921f81f8007ffc0007fff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1001 : Nat := 0x3f27f555ffff53afffff93fafaff81f8007fff81c7ffffc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1011 : Nat := 0x3f4bf66afffffc0ffffffe4aff1f81f8007ffffe07ffffff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1027 : Nat := 0x3f93fff0fffa655fffffffff921f81fff87ffc0007ffffffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1046 : Nat := 0x3fe3ff4cfff9f0effffcf3cef6dff1ff867ffc7837fffe38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1051 : Nat := 0x3ffc088092048a0000000000001ffe00000000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1064 : Nat := 0x3ffc0880fffffff010092495205ffe00007ffffff800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1092 : Nat := 0x3ffc9995fffffffe3f1fa5fd78fffe00007fffffff1f8fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1100 : Nat := 0x3ffd2aaaffffffffd45ffe957f5ffe00007fffffffe00fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1113 : Nat := 0x3ffe4ff0fffffff499bfffffa05ffe07f87ffffff8000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1128 : Nat := 0x3fff8f8cfffffff27cdd75d776dfffc7867ffffff81e6e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1135 : Nat := 0x3ffffcc0ffffffffffedb6dfb25ffff8007ffffffffff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1143 : Nat := 0x3fffffff92048a09221249204dbfffffff8000000000000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1174 : Nat := 0x3fffffffb6f5faeb7ede79e67fffffffff803878301e6e38e33b6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1184 : Nat := 0x3fffffffdb4eaf5dabbfffffcdbfffffff80000000000fffffc00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1188 : Nat := 0x3ffffffff3979baf3f1fc9f87dfffffffff1c381c71f8fc0fc3c7
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1193 : Nat := 0x3ffffffffe27fe0fe65fff207fbffffffffe03fe07e00fff003f8
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1198 : Nat := 0x3ffffffffffcca0ffff6db6adfbffffffffffc0007fff00000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev w1203 : Nat := 0x3ffffffffffffff9321b6db56dfffffffffffffff800000000000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def raw : List Nat := [w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q0 : List Nat := [w33,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q1 : List Nat := [w33,w386,w490,w662,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q2 : List Nat := [w48,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q3 : List Nat := [w52,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q4 : List Nat := [w57,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q5 : List Nat := [w62,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q6 : List Nat := [w67,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q7 : List Nat := [w79,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q8 : List Nat := [w89,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q9 : List Nat := [w99,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q10 : List Nat := [w118,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q11 : List Nat := [w127,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q12 : List Nat := [w140,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q13 : List Nat := [w154,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q14 : List Nat := [w160,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q15 : List Nat := [w166,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q16 : List Nat := [w182,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q17 : List Nat := [w192,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q18 : List Nat := [w206,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q19 : List Nat := [w221,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q20 : List Nat := [w228,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q21 : List Nat := [w234,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q22 : List Nat := [w246,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q23 : List Nat := [w257,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q24 : List Nat := [w272,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q25 : List Nat := [w288,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q26 : List Nat := [w295,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q27 : List Nat := [w301,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q28 : List Nat := [w316,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q29 : List Nat := [w330,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q30 : List Nat := [w343,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q31 : List Nat := [w355,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q32 : List Nat := [w363,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q33 : List Nat := [w369,w386,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q34 : List Nat := [w386,w420,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q35 : List Nat := [w386,w434,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q36 : List Nat := [w386,w447,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q37 : List Nat := [w386,w459,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q38 : List Nat := [w386,w467,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q39 : List Nat := [w386,w473,w490,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q40 : List Nat := [w386,w490,w521,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q41 : List Nat := [w386,w490,w521,w662,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q42 : List Nat := [w386,w490,w536,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q43 : List Nat := [w386,w490,w550,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q44 : List Nat := [w386,w490,w563,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q45 : List Nat := [w386,w490,w579,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q46 : List Nat := [w386,w490,w592,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q47 : List Nat := [w386,w490,w606,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q48 : List Nat := [w386,w490,w619,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q49 : List Nat := [w386,w490,w631,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q50 : List Nat := [w386,w490,w638,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q51 : List Nat := [w386,w490,w646,w662,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q52 : List Nat := [w386,w490,w662,w693,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q53 : List Nat := [w386,w490,w662,w708,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q54 : List Nat := [w386,w490,w662,w722,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q55 : List Nat := [w386,w490,w662,w735,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q56 : List Nat := [w386,w490,w662,w751,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q57 : List Nat := [w386,w490,w662,w761,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q58 : List Nat := [w386,w490,w662,w776,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q59 : List Nat := [w386,w490,w662,w790,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q60 : List Nat := [w386,w490,w662,w803,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q61 : List Nat := [w386,w490,w662,w819,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q62 : List Nat := [w386,w490,w662,w828,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q63 : List Nat := [w386,w490,w662,w840,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q64 : List Nat := [w386,w490,w662,w853,w865,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q65 : List Nat := [w386,w490,w662,w865,w898,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q66 : List Nat := [w386,w490,w662,w865,w910,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q67 : List Nat := [w386,w490,w662,w865,w929,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q68 : List Nat := [w386,w490,w662,w865,w945,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q69 : List Nat := [w386,w490,w662,w865,w957,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q70 : List Nat := [w386,w490,w662,w865,w970,w1001,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q71 : List Nat := [w386,w490,w662,w865,w970,w1011,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q72 : List Nat := [w386,w490,w662,w865,w970,w1027,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q73 : List Nat := [w386,w490,w662,w865,w970,w1046,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q74 : List Nat := [w386,w490,w662,w865,w970,w1051,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q75 : List Nat := [w386,w490,w662,w865,w970,w1064,w1092,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q76 : List Nat := [w386,w490,w662,w865,w970,w1064,w1100,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q77 : List Nat := [w386,w490,w662,w865,w970,w1064,w1113,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q78 : List Nat := [w386,w490,w662,w865,w970,w1064,w1128,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q79 : List Nat := [w386,w490,w662,w865,w970,w1064,w1135,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q80 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1174]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q81 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1184]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q82 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1188]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q83 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1193]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q84 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1198]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q85 : List Nat := [w386,w490,w662,w865,w970,w1064,w1143,w1203]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q86 : List Nat := [w386,w490,w662,w929,w970,w1064,w1143]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def q87 : List Nat := [w386,w490,w662,w970,w1064,w1143,w1174]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem must : ∀ i : Fin raw.length, enough 105 (cover 105 (raw.filter (fun x => x != raw[i.val]'i.isLt))) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem wide (closedRaw : Ban 105 9 raw) : Wide 105 9 bank := by
  rintro ⟨k,S,lim,live,sub⟩
  have bankEq : ∀ x ∈ bank, x=0 ∨ x∈raw := by decide +kernel
  have mem (x : Nat) (hx : x∈S) : x∈raw := by
    exact (bankEq _ (sub x hx)).resolve_left (liveNonzero live x hx)
  have hit (x : Nat) (hx : x∈raw) : x∈S := by
    by_contra absent
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hx
    have hcov := enoughSup live (raw.filter (fun w => w != raw[i])) (by
      intro y hy; apply List.mem_filter.mpr; refine ⟨mem y hy,?_⟩; apply bne_iff_ne.mpr
      intro e; apply absent; simpa only [←eq,←e] using hy)
    exact Bool.noConfusion ((must ⟨i,hi⟩).symm.trans hcov)
  have eq : raw.toFinset=S := by ext x; simpa using (show x∈raw ↔ x∈S from ⟨hit x,mem x⟩)
  apply closedRaw k lim; simpa only [eq] using live
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fromRoot (closedRaw : Ban 105 9 raw) (k) (h : Run Lower26514.start k residual) : 11 ≤ k := by
  have dep : ¬Coord26514.stable first residual := by unfold Coord26514.stable; decide +kernel
  have eq : residual ∘ Coord26514.pin first true = minor := funext (by decide +kernel)
  have nc : ¬Pin26514.Const (residual ∘ Coord26514.pin first true) := by rw [eq]; unfold Pin26514.Const; decide +kernel
  obtain ⟨l, hl, hr⟩ := Coord26514.one first true residual h dep nc
  rw [eq] at hr
  by_contra! small
  have hr' := Pin26514.weaken hr (show l≤9 by omega)
  exact wide closedRaw (possibleOfRun hr' (fun i hi => labels ⟨i,hi⟩) bank covStart)
end Residual27743

namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num0 : Ban 105 8 q0 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num16 : Ban 105 8 q16 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num32 : Ban 105 8 q32 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num48 : Ban 105 8 q48 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num64 : Ban 105 8 q64 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num80 : Ban 105 8 q80 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num1 : Ban 105 8 q1 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num17 : Ban 105 8 q17 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num33 : Ban 105 8 q33 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num49 : Ban 105 8 q49 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num65 : Ban 105 8 q65 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num81 : Ban 105 8 q81 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num2 : Ban 105 8 q2 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num18 : Ban 105 8 q18 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num34 : Ban 105 8 q34 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num50 : Ban 105 8 q50 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num66 : Ban 105 8 q66 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num82 : Ban 105 8 q82 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num3 : Ban 105 8 q3 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num19 : Ban 105 8 q19 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num35 : Ban 105 8 q35 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num51 : Ban 105 8 q51 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num67 : Ban 105 8 q67 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num83 : Ban 105 8 q83 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num4 : Ban 105 8 q4 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num20 : Ban 105 8 q20 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num36 : Ban 105 8 q36 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num52 : Ban 105 8 q52 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num68 : Ban 105 8 q68 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num84 : Ban 105 8 q84 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num5 : Ban 105 8 q5 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num21 : Ban 105 8 q21 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num37 : Ban 105 8 q37 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num53 : Ban 105 8 q53 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num69 : Ban 105 8 q69 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num85 : Ban 105 8 q85 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num6 : Ban 105 8 q6 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num22 : Ban 105 8 q22 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num38 : Ban 105 8 q38 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num54 : Ban 105 8 q54 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num70 : Ban 105 8 q70 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num86 : Ban 105 8 q86 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num7 : Ban 105 8 q7 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num23 : Ban 105 8 q23 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num39 : Ban 105 8 q39 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num55 : Ban 105 8 q55 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num71 : Ban 105 8 q71 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num87 : Ban 105 8 q87 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num8 : Ban 105 8 q8 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num24 : Ban 105 8 q24 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num40 : Ban 105 8 q40 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num56 : Ban 105 8 q56 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num72 : Ban 105 8 q72 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num9 : Ban 105 8 q9 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num25 : Ban 105 8 q25 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num41 : Ban 105 8 q41 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num57 : Ban 105 8 q57 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num73 : Ban 105 8 q73 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num10 : Ban 105 8 q10 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num26 : Ban 105 8 q26 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num42 : Ban 105 8 q42 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num58 : Ban 105 8 q58 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num74 : Ban 105 8 q74 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num11 : Ban 105 8 q11 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num27 : Ban 105 8 q27 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num43 : Ban 105 8 q43 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num59 : Ban 105 8 q59 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num75 : Ban 105 8 q75 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num12 : Ban 105 8 q12 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num28 : Ban 105 8 q28 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num44 : Ban 105 8 q44 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num60 : Ban 105 8 q60 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num76 : Ban 105 8 q76 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num13 : Ban 105 8 q13 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num29 : Ban 105 8 q29 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num45 : Ban 105 8 q45 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num61 : Ban 105 8 q61 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num77 : Ban 105 8 q77 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num14 : Ban 105 8 q14 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num30 : Ban 105 8 q30 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num46 : Ban 105 8 q46 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num62 : Ban 105 8 q62 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num78 : Ban 105 8 q78 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743
namespace Residual27743
open Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num15 : Ban 105 8 q15 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num31 : Ban 105 8 q31 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num47 : Ban 105 8 q47 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num63 : Ban 105 8 q63 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem num79 : Ban 105 8 q79 := banOfSearch _ _ (by decide +kernel) (by decide +kernel)
end Residual27743

namespace Residual27743
open Lower26514 Residual27743Kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def missSet (cs : List (List Nat)) (w : List Nat) : Bool := !(cs.any (fun c => w.all (fun a => c.contains a) && c.all (fun a => w.contains a)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem banBySet {k : Nat} (v : List Nat) (cs : List (List Nat)) (nd : v.Nodup)
    (blocked : (terminal 105 v || anyGate 105 k (missSet cs) v) = false)
    (checked : ∀ w ∈ cs, Ban 105 k w) : Ban 105 (k+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,he,hg,hz⟩ := live
    have mem : a∈v := List.mem_toFinset.mp (he ▸ Finset.mem_singleton_self _)
    simp [ends hg v mem] at blocked
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,he,hd,_,_,ab,fresh,tail⟩ := live
    have ok := transition (go:=missSet cs) hd ab fresh he nd (show n≤k by omega) tail (by
      intro w hw _
      by_contra! hm
      have inc : ∃ c∈cs, (∀ x∈w, x∈c) ∧ ∀ x∈c,x∈w := by simpa [missSet] using hm
      obtain ⟨c,hc,hwc,hcw⟩ := inc
      apply checked _ hc n (by omega)
      have eq : c.toFinset=w.toFinset := by ext x; simpa using (show x∈c ↔ x∈w from ⟨hcw _,hwc _⟩)
      simpa only [eq,hw] using tail)
    simp [ok] at blocked
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem closedRaw : Ban 105 9 raw := by
  apply banBySet raw [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21,q22,q23,q24,q25,q26,q27,q28,q29,q30,q31,q32,q33,q34,q35,q36,q37,q38,q39,q40,q41,q42,q43,q44,q45,q46,q47,q48,q49,q50,q51,q52,q53,q54,q55,q56,q57,q58,q59,q60,q61,q62,q63,q64,q65,q66,q67,q68,q69,q70,q71,q72,q73,q74,q75,q76,q77,q78,q79,q80,q81,q82,q83,q84,q85,q86,q87] (by decide +kernel) (by decide +kernel)
  exact List.forall_mem_cons.mpr ⟨num0,List.forall_mem_cons.mpr ⟨num1,List.forall_mem_cons.mpr ⟨num2,List.forall_mem_cons.mpr ⟨num3,List.forall_mem_cons.mpr ⟨num4,List.forall_mem_cons.mpr ⟨num5,List.forall_mem_cons.mpr ⟨num6,List.forall_mem_cons.mpr ⟨num7,List.forall_mem_cons.mpr ⟨num8,List.forall_mem_cons.mpr ⟨num9,List.forall_mem_cons.mpr ⟨num10,List.forall_mem_cons.mpr ⟨num11,List.forall_mem_cons.mpr ⟨num12,List.forall_mem_cons.mpr ⟨num13,List.forall_mem_cons.mpr ⟨num14,List.forall_mem_cons.mpr ⟨num15,List.forall_mem_cons.mpr ⟨num16,List.forall_mem_cons.mpr ⟨num17,List.forall_mem_cons.mpr ⟨num18,List.forall_mem_cons.mpr ⟨num19,List.forall_mem_cons.mpr ⟨num20,List.forall_mem_cons.mpr ⟨num21,List.forall_mem_cons.mpr ⟨num22,List.forall_mem_cons.mpr ⟨num23,List.forall_mem_cons.mpr ⟨num24,List.forall_mem_cons.mpr ⟨num25,List.forall_mem_cons.mpr ⟨num26,List.forall_mem_cons.mpr ⟨num27,List.forall_mem_cons.mpr ⟨num28,List.forall_mem_cons.mpr ⟨num29,List.forall_mem_cons.mpr ⟨num30,List.forall_mem_cons.mpr ⟨num31,List.forall_mem_cons.mpr ⟨num32,List.forall_mem_cons.mpr ⟨num33,List.forall_mem_cons.mpr ⟨num34,List.forall_mem_cons.mpr ⟨num35,List.forall_mem_cons.mpr ⟨num36,List.forall_mem_cons.mpr ⟨num37,List.forall_mem_cons.mpr ⟨num38,List.forall_mem_cons.mpr ⟨num39,List.forall_mem_cons.mpr ⟨num40,List.forall_mem_cons.mpr ⟨num41,List.forall_mem_cons.mpr ⟨num42,List.forall_mem_cons.mpr ⟨num43,List.forall_mem_cons.mpr ⟨num44,List.forall_mem_cons.mpr ⟨num45,List.forall_mem_cons.mpr ⟨num46,List.forall_mem_cons.mpr ⟨num47,List.forall_mem_cons.mpr ⟨num48,List.forall_mem_cons.mpr ⟨num49,List.forall_mem_cons.mpr ⟨num50,List.forall_mem_cons.mpr ⟨num51,List.forall_mem_cons.mpr ⟨num52,List.forall_mem_cons.mpr ⟨num53,List.forall_mem_cons.mpr ⟨num54,List.forall_mem_cons.mpr ⟨num55,List.forall_mem_cons.mpr ⟨num56,List.forall_mem_cons.mpr ⟨num57,List.forall_mem_cons.mpr ⟨num58,List.forall_mem_cons.mpr ⟨num59,List.forall_mem_cons.mpr ⟨num60,List.forall_mem_cons.mpr ⟨num61,List.forall_mem_cons.mpr ⟨num62,List.forall_mem_cons.mpr ⟨num63,List.forall_mem_cons.mpr ⟨num64,List.forall_mem_cons.mpr ⟨num65,List.forall_mem_cons.mpr ⟨num66,List.forall_mem_cons.mpr ⟨num67,List.forall_mem_cons.mpr ⟨num68,List.forall_mem_cons.mpr ⟨num69,List.forall_mem_cons.mpr ⟨num70,List.forall_mem_cons.mpr ⟨num71,List.forall_mem_cons.mpr ⟨num72,List.forall_mem_cons.mpr ⟨num73,List.forall_mem_cons.mpr ⟨num74,List.forall_mem_cons.mpr ⟨num75,List.forall_mem_cons.mpr ⟨num76,List.forall_mem_cons.mpr ⟨num77,List.forall_mem_cons.mpr ⟨num78,List.forall_mem_cons.mpr ⟨num79,List.forall_mem_cons.mpr ⟨num80,List.forall_mem_cons.mpr ⟨num81,List.forall_mem_cons.mpr ⟨num82,List.forall_mem_cons.mpr ⟨num83,List.forall_mem_cons.mpr ⟨num84,List.forall_mem_cons.mpr ⟨num85,List.forall_mem_cons.mpr ⟨num86,List.forall_mem_cons.mpr ⟨num87,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem lower (k) (h : Run Lower26514.start k residual) : 11 ≤ k := fromRoot closedRaw k h
end Residual27743

end PEqualNP.Outside.L_meta_27599_aux
open PEqualNP.Outside.L_meta_27599_aux
theorem PEqualNP.Outside.L_meta_27599 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩) := by
  rintro ⟨C,fan,sz,rep,_,_,_,_,a,_⟩
  have h := Prefix27599.pinPrefixStrong C fan sz rep a
  have eq : Prefix27599.residual = Residual27743.residual := funext (by decide +kernel)
  rw [eq] at h; have := Residual27743.lower _ h; omega
