import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_29252_aux
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


namespace Physical26514
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
private theorem cost_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : (gs.map cost).sum < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hg : g.op = .not
    · have h0 : cost g = 0 := by simp [cost,hg]
      simpa [h0] using Nat.lt_succ_of_le (cost_le gs)
    · have htail : ∃ q ∈ gs, q.op = .not := by
        obtain ⟨q,hq,hop⟩ := h; rcases List.mem_cons.mp hq with rfl|hmem
        · contradiction
        · exact ⟨q,hmem,hop⟩
      have hcost : cost g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [cost]
      simp; specialize ih htail; omega


theorem normalize {n} (gs : List Gate) (o : Nat) (hgood : ∀ g ∈ gs, Good g)
    (hnot : ∃ g ∈ gs, g.op = .not) (t : Fn n)
    (rep : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = t x) :
    ∃ k, k + 1 ≤ gs.length ∧ Run start k t := by
  let raw : List (Fn n) := List.ofFn fun i : Fin n => fun x => x i
  have hz : Dual (start (n:=n)) zeroF := ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
  have hin : ∀ f ∈ raw, Dual start f := by
    intro f hf; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hh : [fun x : Fin n → Bool => x i,fun x => !(x i)] ∈
        List.ofFn (fun j : Fin n => [fun x => x j,fun x => !(x j)]) := List.mem_ofFn.mpr ⟨i,rfl⟩
    constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr
    · exact ⟨_,hh,List.mem_cons_self⟩
    · exact ⟨_,hh,List.mem_cons_of_mem _ List.mem_cons_self⟩
  have h := compile gs o raw start hgood hz hin
  have heq : (gs.foldl extend raw).getD o zeroF = t := by
    funext x
    rw [←readMap,foldMap]
    simp only [raw,List.map_ofFn,Function.comp_def]; exact rep x
  exact ⟨_,cost_lt hnot,heq ▸ h⟩


theorem convertOfLower {n} {t : Fn n} {gs ms : List Gate} {o out : Nat}
    (hgood : ∀ g ∈ gs, Good g) (rep : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = t x)
    (hmono : ∀ g ∈ ms, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hrep : ∀ x, Circuit.eval ⟨ms,out⟩ (List.ofFn x) = t x)
    (lower : ∀ k, Run start k t → ms.length ≤ k+1) :
    ∃ (ls : List Gate) (z : Nat), (∀ g ∈ ls, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ls.length ≤ gs.length ∧ ∀ x, Circuit.eval ⟨ls,z⟩ (List.ofFn x) = t x := by
  by_cases h : ∃ g ∈ gs, g.op = .not
  · obtain ⟨k,hk,hr⟩ := normalize gs o hgood h t rep
    exact ⟨ms,out,hmono,le_trans (lower k hr) hk,hrep⟩
  · refine ⟨gs,o,?_,le_rfl,rep⟩
    intro g hg
    obtain ⟨ho,hf⟩ := hgood g hg
    exact ⟨ho.imp_right (fun q => q.resolve_right (fun hn => h ⟨g,hg,hn⟩)),hf⟩

end Physical26514


namespace Integration29252
open PEqualNP.CircuitLowerBounds

def edges : List Nat := [0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7]

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem finish {ws : List Gate} {out : Nat}
    (mono : ∀ g ∈ ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨ws,out⟩ (List.ofFn x)=graph x)
    (lower : ∀ k, Lower26514.Run Lower26514.start k graph → ws.length ≤ k+1) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fan _ rep; exact Physical26514.convertOfLower fan rep mono computes lower
end Integration29252


namespace Witness29252
open PEqualNP.CircuitLowerBounds

def edges : List Nat := [0,3,0,4,1,4,0,5,2,5,3,5,1,6,2,6,4,6,0,7,1,7,2,7,4,7]

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)


def gates : List Gate := [
  ⟨.and,[0,3]⟩, ⟨.or,[0,1]⟩, ⟨.or,[4,7]⟩, ⟨.and,[9,10]⟩,
  ⟨.or,[0,2]⟩, ⟨.or,[12,3]⟩, ⟨.and,[13,5]⟩,
  ⟨.or,[1,2]⟩, ⟨.or,[15,4]⟩, ⟨.or,[6,7]⟩, ⟨.and,[16,17]⟩,
  ⟨.or,[8,11]⟩, ⟨.or,[14,18]⟩, ⟨.or,[19,20]⟩]

theorem size : gates.length = 14 := rfl
theorem mono : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [gates]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,21⟩ (List.ofFn x) = graph x := by
  decide +kernel

end Witness29252

namespace GraphKernel29252
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem avail_mono {d:Nat} {bank:List Nat} {w:Nat} (h : Avail false d bank w) :
    Avail true d bank w:=by
  rcases h with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction
theorem reach_up {d:Nat} {roots:List Nat} {p bank} (h:NatReach false d roots p bank) :
    NatReach true d roots p bank:=by
  induction p generalizing bank with
  | zero=>exact h
  | succ p ih =>
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=h
    have hop' : allowedB true op = true:=by
      rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩ <;> first | decide | contradiction
    exact ⟨b,a,c,op,hop',rfl,ih hrb,avail_mono ha,avail_mono hc⟩
theorem lower_down {d:Nat} {roots:List Nat} {T L:Nat} (h : Lower true d roots T L) :
    Lower false d roots T L:=fun p bank hr ha=>h p bank (reach_up hr) (avail_mono ha)
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
end GraphKernel29252

namespace GraphReplay29252
open GraphKernel29252

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
structure Cut where
  domain : Nat
  goal : Nat
  bound : Nat
  roots : List Nat

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def GoodCut (d t : Nat) (c : Cut) := subValidB d c.domain t c.goal = true ∧ Lower true c.domain c.roots c.goal c.bound

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
structure Table where
  n : Nat → Nat
  hashAt : Nat → Nat → Nat
  wires : Nat → Nat → List Nat
  ops : Nat → Nat → List (Nat × Nat × Nat)
  flags : Nat → Nat → Nat
  seed : Nat
  cuts : List Cut

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def choose : List Cut → Nat → List Cut
  | [], _ => []
  | c::cs, bits => if bits.testBit 0 then c :: choose cs (bits >>> 1) else choose cs (bits >>> 1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem choose_mem {c : Cut} (cs : List Cut) (w) (h : c ∈ choose cs w) : c ∈ cs := by
  induction cs generalizing w with
  | nil => simp [choose] at h
  | cons a cs ih =>
    simp only [choose] at h
    split at h
    · rcases List.mem_cons.mp h with rfl|hc; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (ih _ hc)
    · exact List.mem_cons_of_mem _ (ih _ h)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pools (T : Table) (s i : Nat) := (choose T.cuts (T.flags s i)).map fun c =>
  (c.domain,c.bound,runOps true c.domain (0,c.roots) (T.ops s i))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def idx (T : Table) (s h : Nat) := bsr (T.hashAt s) h 32 0 (T.n s)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def chartRows (T : Table) (pairs : List (Nat × Nat)) (s i : Nat) :=
  (T.wires s i).map fun w => (w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cell (T : Table) (d goal : Nat) (pairs : List (Nat × Nat)) (s i : Nat) :=
  barP true d (goal &&& d) (maskP pairs.length) (chartRows T pairs) T.wires T.n T.hashAt (idx T) id T.seed [] (pools T) s i

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def atRoot (T : Table) (ws : List Nat) (s : Nat) :=
  T.cuts.any (fun c => checkPool true c.domain c.bound s (0,c.roots) ws) ||
  found T.wires T.n (fun j ys => idx T j (hk T.seed ys)) s ws

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem replay (T : Table) (d goal : Nat) (roots : List Nat) (pairs : List (Nat × Nat)) (L : Nat)
    (hd : d &&& mask256 = d)
    (hp : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(goal&&&d).testBit p.1&&(goal&&&d).testBit p.2) = true)
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(goal.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d goal)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((goal&&&d).testBit p.1 != (goal&&&d).testBit p.2)) = true)
    (properFail : ∀ zs ∈ (roots.map (· &&& d)).sublists, zs ≠ roots.map (· &&& d) → unorientedCov pairs zs = false)
    (prior : ∀ c ∈ T.cuts, GoodCut d goal c)
    (cells : ∀ s ≤ L-1, ∀ i < T.n s, cell T d goal pairs s i = true)
    (root : ∀ s, roots.length-1 ≤ s → s ≤ L-1 → atRoot T (roots.map (· &&& d)) s = true) : Lower true d roots goal L := by
  apply lower_of_search hinit properFail
  intro s hs run
  have le := run_len run
  rw [List.length_map] at le
  have yes := root s (by omega) hs
  rw [atRoot,Bool.or_eq_true] at yes
  rcases yes with hit|hit
  · obtain ⟨c,hc,hcheck⟩ := List.any_eq_true.mp hit
    exact checkRootSub_sound (prior c hc).1 (prior c hc).2 hcheck run
  · simp only [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hit
    let chk := fun s i (g : Nat × Nat × Nat) (ys : List Nat) => (pools T s i).any (fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) ys)
    have ck {s i g ys} (h : chk (s+1) i g ys = true) : ¬ RunD true d (goal&&&d) s ys := by
      obtain ⟨e,he,hy⟩ := List.any_eq_true.mp h
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
      have ok := prior c (choose_mem _ _ hc)
      exact cpcs ok.1 ok.2 (T.ops (s+1) i) g hy
    have comp (s) (hs : s ≤ L-1) (i) (hi : i < T.n s) :
        bar true d (goal&&&d) (maskP pairs.length) (chartRows T pairs) T.wires T.n T.hashAt (idx T) id T.seed [] chk s i = true := by
      change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (pools T s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) _ _ = true
      rw [←barP_eq]; exact cells s hs i hi
    exact bar_all (pairs:=pairs) hd rfl rfl rfl (fun _ _ => rfl) hp (fun h => h) ck comp s hs _ hit.1 (Run.perm hit.2 run)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def unpack (dict : Nat → Nat) (width code : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => dict (code &&& ((1<<<width)-1)) :: unpack dict width (code >>> width) n

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def unpackOps (dict : Nat → Nat) (width code : Nat) : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | n+1 => (code &&& 3,dict ((code >>> 2) &&& ((1<<<width)-1)),dict ((code >>> (2+width)) &&& ((1<<<width)-1))) :: unpackOps dict width (code >>> (2+2*width)) n
end GraphReplay29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252

namespace C0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x330033
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x320020
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,17),(4,5),(4,20),(16,17),(16,20)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x220022,0x300030,0x330000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 2, i => fld ((#[0x6e057] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 3, i => fld ((#[0x6e057] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 2, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | 3, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C0


namespace C1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x50500000505
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x50400000400
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(2,10),(2,34),(8,10),(8,40),(32,34),(32,40)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x40400000404,0x50000000500,0x50500000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 2, i => fld ((#[0x2343] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 3, i => fld ((#[0x2343] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 2, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | 3, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C1


namespace C2

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x3030000000000000303
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x3020000000000000200
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,65),(8,9),(8,72),(64,65),(64,72)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x2020000000000000202,0x3000000000000000300,0x3030000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 2, i => fld ((#[0xbc96e] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 3, i => fld ((#[0xbc96e] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 2, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | 3, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C2


namespace C3

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x5050000000000000505
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x5040000000000000400
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(2,10),(2,66),(8,10),(8,72),(64,66),(64,72)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x4040000000000000404,0x5000000000000000500,0x5050000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 2, i => fld ((#[0xd9823] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 3, i => fld ((#[0xd9823] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 2, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | 3, i => fld ((#[579] : Array Nat)[i/32]?.getD 0) 10 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 2, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C3


namespace C4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xeea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(2,10),(3,7),(3,11),(4,5),(6,7),(6,14),(8,9),(8,10),(12,13),(12,14)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaaaa,0xcccc,0xf0f0,0xff00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0x3d3b0] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C4


namespace C6

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf0f0f0f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xe0a0e00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,17),(2,10),(3,11),(3,19),(8,9),(8,10),(16,17),(18,19),(18,26),(24,25),(24,26)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0x77db1] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C6


namespace C11

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x333300003333
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x332000002220
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(4,5),(8,9),(8,40),(12,13),(12,44),(32,40),(33,37),(33,41),(36,37),(36,44)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x222200002222,0x303000003030,0x330000003300,0x333300000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0x2d750] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C11


namespace C14

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x303030303030303
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x302030002020200
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,17),(8,9),(8,40),(16,17),(24,25),(24,56),(32,40),(33,41),(33,49),(48,49),(48,56)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x202020202020202,0x300030003000300,0x303000003030000,0x303030300000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0xaf45d] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C14


namespace C16

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xff00000000000000ff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xee00000000000000a0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,65),(2,66),(3,7),(3,67),(4,5),(6,7),(6,70),(64,65),(64,66),(68,69),(68,70)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaa00000000000000aa,0xcc00000000000000cc,0xf000000000000000f0,0xff0000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0x69156] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C16


namespace C21

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf000f00000000000f000f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xe000e00000000000a0000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,17),(1,65),(2,66),(3,19),(3,67),(16,17),(18,19),(18,82),(64,65),(64,66),(80,81),(80,82)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xa000a00000000000a000a,0xc000c00000000000c000c,0xf000000000000000f0000,0xf000f0000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0xbce70] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0xe44] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 2 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C21


namespace C28

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xfefaeea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(2,10),(3,7),(3,11),(3,19),(4,5),(4,20),(6,7),(6,14),(6,22),(8,9),(8,10),(12,13),(12,14),(12,28),(16,17),(16,20),(18,19),(18,22),(18,26),(24,25),(24,26),(24,28)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0x33333333,0x32322220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xcccccccc,0xccc8cc80,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xffff,0xeea0,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xf0f0f0f,0xe0a0e00,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaaaa,0xfafa,0xa0a0a0a,0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0a0a0,0xf0f0f0f0,0xfafa0000,0xfafafafa,0xff00ff00,0xffff0000,0xffffaaaa,0xfffff0f0] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xc7c5d8dfe577f196478c] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xf0814e8086af979561912baff] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x6380d] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0xa75415a87545ba6545ba5435] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0xdba7546cba7546ba75406ba97546ba75426] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 6, i => fld ((#[0xba7545] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xb99d12b91d12c72d12c7ed12] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0x2dd1b446d217445d21] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0x421e13] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | 6, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C28


namespace C30

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffff0000ffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xffec0000eea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(2,10),(2,34),(3,7),(3,11),(3,35),(4,5),(6,7),(6,14),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,44),(32,34),(32,40),(33,35),(33,37),(33,41),(36,37),(36,38),(36,44)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f00000f0f,0xf0c00000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f00000f0f0,0xf0e00000e0a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xffff,0xeea0,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00]⟩,⟨0x50500000505,0x50400000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0x333300003333,0x332000002220,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xff00,0xffcc,0x330000003300,0x333300003300,0xaaaa0000aaaa,0xcccc0000cc00,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffcc00000000,0xffcc0000ffcc,0xffff00000000,0xffff0000cccc,0xffff0000ff00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xa5f567605761f914437f] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xda0a3d94148d02375e4d6ffe2] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x76e79] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x987645b87545876415b87435] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0xcb87646b876426ba87646db87646b876406] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 6, i => fld ((#[0xb87645] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xba2192d62e12baa192d6ee12] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0x2d9186c6191b846e21] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0x49c087] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | 6, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C30


namespace C33

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf0f0f0f0f0f0f0f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xf0e0f0c0e0a0e00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,17),(2,10),(2,34),(3,11),(3,19),(3,35),(8,9),(8,10),(8,40),(16,17),(18,19),(18,26),(18,50),(24,25),(24,26),(24,56),(32,34),(32,40),(33,35),(33,41),(33,49),(48,49),(48,50),(48,56)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f00000f0f,0xf0c00000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f00000f0f0000,0xf0e00000e0a0000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f,0xe0a0e00,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x50500000505,0x50400000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0x303030303030303,0x302030002020200,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xf000f00,0xf0c0f0c,0x300030003000300,0x303030303000300,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c000c00,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0c0f0c00000000,0xf0c0f0c0f0c0f0c,0xf0f00000f0f0000,0xf0f0f0f00000000,0xf0f0f0f0c0c0c0c,0xf0f0f0f0f000f00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xf188ec025aa1d5e2f55d] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xab40363c6544d8917d130be62] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x260ba] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0xa87645a76415ba7435ba7545] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0xba76406ba76426cba7646dba7646ba97646] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 6, i => fld ((#[0xba7645] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xb91d92b99d92d6edd2d62dd2] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0x2de176c6d91b745d91] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0x799090] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | 6, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C33


namespace C35

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x3333333333333333
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x3332332032322220
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(4,5),(4,20),(8,9),(8,40),(12,13),(12,28),(12,44),(16,17),(16,20),(24,25),(24,28),(24,56),(32,40),(33,37),(33,41),(33,49),(36,37),(36,44),(36,52),(48,49),(48,52),(48,56)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0x33333333,0x32322220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x3333333300000000,0x3332332000000000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x333300003333,0x332000002220,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0x303030303030303,0x302030002020200,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x222200002222,0x323200003232,0x202020202020202,0x303020203030202,0x2222222222222222,0x3030202030302020,0x3030303030303030,0x3232000032320000,0x3232323232323232,0x3300330033003300,0x3333000033330000,0x3333222233332222,0x3333303033333030,0x3333333300000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xfbc9aba8d2567f01044d] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xefd91d25b6957954aec2133ac] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x667d8] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0xd96415da9545da9435d97645] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0xdba9646da96406da96426da98646dca9646] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 6, i => fld ((#[0xda9645] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xa89912b62912b6e912a81912] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0x2911a4859216446991] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0x85ce08] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | 6, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C35


namespace C38

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffff000000000000ffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xffee000000000000eea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,65),(2,10),(2,66),(3,7),(3,11),(3,67),(4,5),(6,7),(6,14),(6,70),(8,9),(8,10),(8,72),(12,13),(12,14),(12,76),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f0000000000000f0f,0xf0e0000000000000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0000000000000f0f0,0xf0e0000000000000e0a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x33330000000000003333,0x33220000000000002220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xffff,0xeea0,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00]⟩,⟨0xff00000000000000ff,0xee00000000000000a0,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000]⟩,⟨0x5050000000000000505,0x5040000000000000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x33330000000000003300,0xaaaa000000000000aaaa,0xcccc000000000000cccc,0xf0f0000000000000f0f0,0xff00000000000000ff00,0xffff0000000000000000,0xffff000000000000ff00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xb155] : Array Nat)[i/32]?.getD 0) 16 (i%32)
  | 5, i => fld ((#[0xd07fe] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x90af8] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x58c85] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 5, i => fld ((#[0x358d16] : Array Nat)[i/32]?.getD 0) 22 (i%32)
  | 6, i => fld ((#[0x58d15] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xcbb12] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xb11] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[15] : Array Nat)[i/32]?.getD 0) 4 (i%32)
  | 6, i => fld ((#[63] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C38


namespace C40

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xff00ff0000000000ff00ff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xfe00ee0000000000fa00a0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,17),(1,65),(2,66),(3,7),(3,19),(3,67),(4,5),(4,20),(6,7),(6,22),(6,70),(16,17),(16,20),(18,19),(18,22),(18,82),(64,65),(64,66),(68,69),(68,70),(68,84),(80,81),(80,82),(80,84)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0x3300330000000000330033,0x3200220000000000320020,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xcc00cc0000000000cc00cc,0xcc00cc0000000000c80080,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xff00000000000000ff,0xee00000000000000a0,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000]⟩,⟨0xf000f00000000000f000f,0xe000e00000000000a0000,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaa00000000000000aa,0xfa00000000000000fa,0xa000a00000000000a000a,0xf000a00000000000f000a,0xaa00aa0000000000aa00aa,0xcc00cc0000000000cc00cc,0xf000a00000000000f000a0,0xf000f00000000000f000f0,0xfa00000000000000fa0000,0xfa00fa0000000000fa00fa,0xff00000000000000ff0000,0xff00aa0000000000ff00aa,0xff00f00000000000ff00f0,0xff00ff0000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xaa16b90f3f6ee6b4190d] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xf65f4c5e63b64189a7e62fd2e] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x8f174] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0xd87545da5435da6545d75415] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0xda75406da97546dba7546da75426dca7546] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 6, i => fld ((#[0xda7545] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xa91d12b7e912b72912a99d12] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 5, i => fld ((#[0x2921744691174869d1] : Array Nat)[i/32]?.getD 0) 14 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0xb82268] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | 6, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 4 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C40


namespace C42

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf0f0f0f000000000f0f0f0f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xf0e0f0e000000000e0a0e00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,17),(1,65),(2,10),(2,66),(3,11),(3,19),(3,67),(8,9),(8,10),(8,72),(16,17),(18,19),(18,26),(18,82),(24,25),(24,26),(24,88),(64,65),(64,66),(64,72),(80,81),(80,82),(80,88)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f0000000000000f0f,0xf0e0000000000000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0000000000000f0f0000,0xf0e0000000000000e0a0000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x30303030000000003030303,0x30203020000000002020200,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f,0xe0a0e00,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x5050000000000000505,0x5040000000000000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf000f00000000000f000f,0xe000e00000000000a0000,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x30303030000000003000300,0xa0a0a0a000000000a0a0a0a,0xc0c0c0c000000000c0c0c0c,0xf000f00000000000f000f00,0xf0f0000000000000f0f0000,0xf0f0f0f0000000000000000,0xf0f0f0f000000000f000f00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xf6446] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0x26e50] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | 6, i => fld ((#[0x3f37a] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x58c85] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 5, i => fld ((#[0x358d16] : Array Nat)[i/32]?.getD 0) 22 (i%32)
  | 6, i => fld ((#[0x58d15] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xcbad2] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xad1] : Array Nat)[i/32]?.getD 0) 12 (i%32)
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[15] : Array Nat)[i/32]?.getD 0) 4 (i%32)
  | 6, i => fld ((#[63] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C42


namespace C44

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0x333333330000000033333333
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0x333233220000000032322220
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(1,65),(4,5),(4,20),(8,9),(8,72),(12,13),(12,28),(12,76),(16,17),(16,20),(24,25),(24,28),(24,88),(64,65),(64,72),(68,69),(68,76),(68,84),(80,81),(80,84),(80,88)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0x33333333,0x32322220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x33330000000000003333,0x33220000000000002220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x3300330000000000330033,0x3200220000000000320020,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x30303030000000003030303,0x30203020000000002020200,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x3030000000000000303,0x3020000000000000200,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x2222,0x2020202,0x22222222,0x32323232,0x33003322,0x33023302,0x33223322,0x33323332,0x33332222,0x33333322,0x220000000000000022,0x22220000000000002222,0x30300000000000003232,0x30320000000000003032,0x32320000000000003232,0x33220000000000003322,0x33320000000000003332,0x33330000000000002222,0x33330000000000003232,0x200020000000000020002,0x2200220000000000220022,0x3200320000000000320032,0x3300220000000000330022,0x3300330000000000000022,0x3300330000000000020002,0x3300330000000000220022,0x3300330000000000320032,0x3300330000000000330022,0x20202020000000002020202,0x30203020000000003020302,0x30300000000000003030202,0x30300020000000003030002,0x30302020000000003030202,0x30303020000000003030302,0x30303030000000002020202,0x30303030000000003030202,0x111011100000000011101110,0x111111000000000011111100,0x111111110000000010101010,0x111111110000000011110000,0x222022200000000022202220,0x222222000000000022222200,0x222222220000000020202020,0x222222220000000022220000,0x222222220000000022222222,0x303030300000000030303030,0x303030300000000032323232,0x303230320000000030323032,0x323232300000000032323230,0x323232320000000032323030,0x323232320000000032323232,0x330033000000000033003300,0x330033220000000033003322,0x330233020000000033023302,0x332233220000000033203320,0x332233220000000033223300,0x332233220000000033223322,0x333033300000000033303330,0x333233320000000033323332,0x333300000000000033330000,0x333300000000000033332222,0x333300220000000033330022,0x333322200000000033332220,0x333322220000000033332020,0x333322220000000033332222,0x333333000000000033333300,0x333333220000000033333322,0x333333330000000000000000,0x333333330000000000002222,0x333333330000000002020202,0x333333330000000022202220,0x333333330000000022222200,0x333333330000000022222222,0x333333330000000030303030,0x333333330000000032323232,0x333333330000000033330000,0x333333330000000033332222] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 3 => 8
  | 4 => 32
  | 5 => 52
  | 6 => 13
  | 7 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 3, i => fld ((#[0xf9819eb7e7c37f1c0f3e7e77c7d868450423fbc3] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 4, i => fld ((#[0xfa4d2f3dd8c4a43b912cb7eb1ad6c1a60b0a4f4299ab99812f949f689514826e1817cd80a567828a72d826f72a556fe490a248ad546a55459d63d6ed3666031b29292252905c1780412e44034b7019f9] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0x8c85e8bcec849fa7def67c9fd7af62794af777fc72d8572b98720487066f6f9306d341646c9625e06124b5949d523895014e4ad1a485e54308d3f27d3b6a6303072959f2783d0e8e108ca402af00242d,0xf05ebefed1edb7aed019e1244de2afd7a3bd1221c7a87bcf73bb5f5b99c2a264a9fb989c4619c0949895b96d7096252932e4] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0xfcc13db323ad1c96ccf157f0b4d66649e7b36d0834c5f31ac82f63119b2c0b202] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0x6ccf1] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 3, i => fld ((#[0x86f99b248eedc2d490edbad48cedc2d487019b1487019b0490edb2d486fd9b24] : Array Nat)[i/32]?.getD 0) 32 (i%32)
  | 4, i => fld ((#[0x90ed9ad54b0ddb364a961b35ab082c37ecd6ac586edb2d58b0ddad586161bb5ab0d2bb66b5607586cd6ac18b0e0335aad61c066b54ac366b5612586ed9b158b0ddb360b15db35ab04ac376b561b586f99ad58b0ddb358855db35ab022c376cd61f576cd6ac0ab0ddb85aa561bb5ab0bac776cd6ac586edbad58b0d9ad5835643b66b55ac376e16a8586ed9ac46b19db35ab161bb66b0f2c376cd9285] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 5, i => fld ((#[0x8701db35881a1bb70b5614686ed9ad5801a4c876cd6ac686ed9ad5805a1bb66b56286010d9ad583964c376cd92c686ed9ad589da1bb74cd6ac686ed9ad5895a1bb66b5616686ed9ad5845a1bb66b562a686cd92d5839a1bb66c961c686ed9ad5889a1bb66b5615686ed9ad583da5c380cd6ac686f5db35ab1a1bb6acd6ac676e19ad5819a43b66b560268b0ddb35ab1a1bb72e16ac686ed9ad5891a1bb66b56136010ddad586561bb72cd92c686eda335ab1a24376cd6ac6,0x87060335ab1a1bb66b56036990ddb35ab1a1bb66b562669721db35ab1a54376cd6ac686ed9ad5875a44376b56196010ddb3588161c276cd6ac686f1db35ab1a1bb66b96ac68705db85ab1a1c066b560b686ed9af5ab1a1bb66b562b686ed9ad58a5a1bb66b560a600ed9ad581961bb66b56086] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 6, i => fld ((#[0x21bb66b560b686edcb35ab1a5c376cd6ac6010ddb35ab161bb66c96ac68705db35ab1a4c376cd6ac686ed9ad5851a1bb66b561c68701db35ab1a44376cd6ac686edc335ab1a1bb66b56026] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 7, i => fld ((#[0x4376cd6ac5] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 3, i => fld ((#[0x76a172b066b55ab1486a582b076cd66b1466ad96b086ed86b1486a172b066b566b145aad96b086ed76b145aa582b076cd76b1466a992b086b586b1476a992b086b55ab14] : Array Nat)[i/32]?.getD 0) 68 (i%32)
  | 4, i => fld ((#[0x92b086b586b1392b086b55ab1376ea66c95ab1376a992b086b5366a992b086b538acf86715ab2394cf86c95ab1386ea66c95ab1376ba5a0986b2396b086ed76b1382b076cd76b1394ef86c95ab135aad96b086ed35aa582b076cd3870a76e166b1398cf870176b1376a172b066b5384b776e166b1386d2662d76b237ab7765166b2386d666715ab2382b076cd66b1388cf862d76b2386a582b076cd366ad96b086ed376be5a5166b2396b086ed86b1372b066b566b1398b7870176b1386a172b066b5378b7760986b2372b066b55ab13] : Array Nat)[i/32]?.getD 0) 52 (i%32)
  | 5, i => fld ((#[0x80b776b1266b266b12862e76b2286b586b1286725ab2272b066b5276ca5ab1286b55ab1296b386ed266c95ab1282b376cd280cf76b1290ef86b1292b086b5276ca5ab125ab25ab1290b786b1266ca5ab1276e266b1286ed76b12765166b2266715ab2286e266b1286b286b1286715ab2266b566b1272b366b5266725ab2290cf86b1266b55ab12662d76b22862d76b22,0x76cd76b1286ca5ab12870176b1292b386b5286ed86b1286c95ab1270b766b1290cf86b1280b776b1276e166b12760986b225a0986b2276cd66b1276b276b125a5166b2296b086ed282b076cd2765266b2286e266b12870276b12] : Array Nat)[i/32]?.getD 0) 36 (i%32)
  | 6, i => fld ((#[0x76b2166b5186ed1000005ab1176cd186b5166b215ab2176b1186b1166b1186b21] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 3, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0x29401803c0210300000392a8000021810151418000024410,0x900c004b00050308204a2833d80000] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | 6, i => fld ((#[0x2ffff3effff7efbdf7df] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | 7, i => fld ((#[63] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 7 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 7 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C44


namespace C49

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf0f00000f0f00000f0f00000f0f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xf0e00000f0e00000f0c00000e00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,65),(2,10),(2,34),(2,66),(3,11),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(32,34),(32,40),(33,35),(33,41),(33,97),(64,65),(64,66),(64,72),(96,97),(96,98),(96,104)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f00000f0f,0xf0c00000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0000000000000f0f,0xf0e0000000000000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x303000003030000030300000303,0x302000003020000030000000200,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x505000005050000050500000505,0x504000005040000050400000400,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xa0a00000a0a00000a0a00000a0a,0xc0c00000c0c00000c0c00000c0c,0xf0000000f0000000f0000000f00,0xf0f0000000000000f0f00000000,0xf0f00000f0f0000000000000000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 6 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 6, i => fld ((#[0xde658] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 6, i => fld ((#[0x46885] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 6, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 6, i => fld ((#[15] : Array Nat)[i/32]?.getD 0) 4 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 3 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C49


namespace C57

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffffffffffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xfffeffecfefaeea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(2,10),(2,34),(3,7),(3,11),(3,19),(3,35),(4,5),(4,20),(6,7),(6,14),(6,22),(6,38),(8,9),(8,10),(8,40),(12,13),(12,14),(12,28),(12,44),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(24,25),(24,26),(24,28),(24,56),(32,34),(32,40),(33,35),(33,37),(33,41),(33,49),(36,37),(36,38),(36,44),(36,52),(48,49),(48,50),(48,52),(48,56)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xffffffff,0xfefaeea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xffff0000ffff,0xffec0000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f0f0f0f0f,0xf0e0f0c0e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x3333333333333333,0x3332332032322220,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xffffffff00000000,0xfffeffec00000000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xffff0000ffff0000,0xfffe0000fefa0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xff00ff00ff00ff,0xfe00ec00fa00a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f0f0f0f0f0,0xf0f0f0e0f0f0e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xcccccccccccccccc,0xccccccccccc8cc80,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x5555555555555555,0x5554554454504400,6,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xff00ff00000000,0xfe00ec00000000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x33333333,0x32322220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xcccccccc,0xccc8cc80,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xf0f00000f0f,0xf0c00000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f00000f0f0,0xf0e00000e0a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f00000f0f0000,0xf0e00000e0a0000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0x5555000055550000,0x5554000054500000,5,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xcc00cc00cc00cc,0xcc00cc00c80080,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x5050505050505050,0x5050504050504000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x50500000505,0x50400000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaaaaaaaa,0xff00ff00,0xffccffcc,0xaaaa0000aaaa,0xaaaaff00ffaa,0xfafa0000fafa,0xff000000ff00,0xaa00aa00aa00aa,0xa0a0a0a0a0a0a0a,0xa0a0a0aff0aff0a,0xf000f000f000f00,0xf0f0a0a0f0f0a0a,0x2222222222222222,0x3300330033003300,0x3300bbaa3300bbaa,0x3333333333003300,0x3b0a3b0a3b0a3b0a,0x44cc44cc44cc44cc,0x50f050f050f050f0,0x5500550055005500,0x55aa55aa55aa55aa,0x55ff000055ff0000,0x55ff55ff00000000,0x88aa88aa88aa88aa,0xaa00aa00aa00aa00,0xaaaaaaaa00aa00aa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffaaffaa,0xbbaabbaabbaabbaa,0xcccccccc44444444,0xcccccccccc00cc00,0xcccccccccccccccc,0xcccccccceeeeeeee,0xcccceeeecccceeee,0xcececececececece,0xdddddddd00000000,0xeecceecceecceecc,0xeeeeeeeeeeeeeeee,0xf0f000f0f0f000f0,0xf0f0a0a0f0f0a0a0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0fff0fff0,0xf0f0fff0f0f0fff0,0xf0ff0000f0ff0000,0xf3f0f3f0f3f0f3f0,0xf500f500f500f500,0xfaf0faf0faf0faf0,0xfafa0000fafa0000,0xfafafafafafafafa,0xfcfcececfcf0eca0,0xfcfcfcfcfcfcfcfc,0xfefeccccfefacc00,0xff005500ff005500,0xff00ff00ff00ff00,0xff00ffaaff00ffaa,0xff0aff0aff0aff0a,0xffaaffaaffaaffaa,0xffccffcc00000000,0xffccffccffccffcc,0xfff0fff0fff0fff0,0xfffcffecf0f0a0a0,0xfffeffccfafa0000,0xffff0000ffff0000,0xffff0000ffffff00,0xffff0f00ffff0f00,0xffff3300ffff3300,0xffffaa00ffffaa00,0xffffaaaaffffaaaa,0xffffccccffffcccc,0xfffff0f0fffff0f0,0xffffff00ffffff00,0xffffffff00000000,0xffffffff0000aaaa,0xffffffff0a0a0a0a,0xffffffff22222222,0xffffffffaa00aa00,0xffffffffaaaaaaaa,0xffffffffcccccccc,0xfffffffff0f0f0f0,0xffffffffff00ff00,0xffffffffffff0000] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 4
  | 5 => 16
  | 6 => 46
  | 7 => 68
  | 8 => 27
  | 9 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0x9b7c857ac7541401d7cb] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0xf90f5f3382e9872e1289d47bcd1c76cacacc26c3b30b04d56743a573b46e2be5b1a80110cf108708] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0xb9e0aae38baa7f79f2bd9db81950488cda28b53884a8182f4f82bdc7fd887efbb7ecf57393c6891e5a03c51d1b4c404428f43a30b32bbd2acf82a89c2713624fe01bb4a1806813ff71203a0bcd609a51,0xfa43ef7d66f43d0efa67e5f57e5302dd96ece35bccf51cbf03c5000c3073c23f3bde83] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0x78957773e17670275a5171c4c6ec175fb495f47e5b6aa5b3855922b546f3530644fd714536042ceb3f8472fb2c2f2a22ef212af7126f8125fd31b86c16f05157090b8810b73e03edc0341d02850015e9,0xf5a5cf5719e7f49e664be643ee513de2f83dc9dfd4883d2ecfd2cbbd0e94cc562ca8e6c9636c6349c4128bed3abb2d3ba568b0ce9acc26ac055a5c42a5ad29a26696a04932368bc3f8391e8324d7f058,0xfd083fcca6fa0aaf6c03] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 8, i => fld ((#[0xf846ff43eddd228dd199d8805d1430bd532bd182b65aea74e0871de7a138748ee453604403436ec2346302c9302c3082b3d62496d1c21a1c00d17f5113ef913a6004ec9] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 9, i => fld ((#[0x4ec9] : Array Nat)[i/32]?.getD 0) 15 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x7cf1a9f34b1dab350695eb5507cd2c77cd589a5] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 5, i => fld ((#[0x8ed541e34159f396a7cd0b672d57a83e699f396a9cf9a67cd4f9a16099cb5507cd0566abd41f34099f354e7cd0266aa0f9a0a09a3be6a6878b68ed57a8343da3be6a9cd0f68ed541a1e15a3be6a78d0b68ed57a83c69a3be6a9cf1a6] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 6, i => fld ((#[0x8ef9aa73e680bbe6ac141f3409e3b5507cd0502f0df35507cd0278af9cb5507cd3c77cd4f9a1a2de3be6aa0d0f06f1daaf507cd0d78ef9aa8343c43c77cd539f3435c0008ef941f28b1df35507cd0e78af9aa83e6813c77cd541f3411e3b5507cd0d0af1df35507cd0978ef9aa83c681bc77cd541e3421e7c77cd4f9a16f3e3b55ea0f9a79f1df354e7cd3be72d541f340de7c76aa0f9a0aef9cb5507cd0878ef9ab050687bc77cd541f3441e3be74d4f9a16f1e1be6aa0d0f77cd541f340c13c774d57a83e69df35507cd0804f1df3a6a9cf9a7,0x23ba6aa0f9a0af1e2be6aa0d0f78ef9ab05078d3cd8ef9a9f342de6c76abd41f34f1e1be6aa0f1a79b1df354e7cd3cd8ed541f3415df396ac141f34f1df353e6858178f15f355078d3808ef9c283e51a3b55ea0f9a02f0df396aa0f9a7] : Array Nat)[i/32]?.getD 0) 53 (i%32)
  | 7, i => fld ((#[0x23be6aa101a600023b5507cd1568f15f35507cd01800023be6aa0d0f600023be507c98768ef9ab0507cd0d88f0df35507cd0d8011df355088f9a700023c26aa0f9a68ef9d35507cd038011df355aa0f9a7011df366aa0f9a78ef9d35507cd08800023b556a0f9a6011df386aa0f9a700023be6aa0f1a68f15f35507cd0d8011df35507cd1979b1df35507cd03800023be6aa0e9a6011dfbe6aa0f9a79b1df35507cd0889f1df3560a0f9a80001f396aa0f9a69f1e1be6aa0f9a800023be6aa121a601263be6aa0f9a78ef9aa83e681818011df35507cd1778ef9aa83e684018011df376aa0f9a70001f35508cf9a6,0x11df3558a0f9a78ef9d3560a0f9a8000253e6aa0f9a68f0df3a6aa0f9a800023be6aa0d11600025be6aa0f9a6011df35507cd9a700023be6a7cd0b68ef9aa83e68683800023b55ea0f9a600023be70a0f98600023be6ab8f9a68ef9aa83e68688800023be6a9cf9a69b1df3560a0f9a88f15f3a6aa0f9a8011df3552a0f9a701223be6aa0f9a700023b5507cd0569b1e1be6aa0f9a8011df3568a0f9a700023be6aa8f9a600023be6a98f9a600023be6a7cd1268ef9ab0507cd0189b1e2be6aa0f9a88f0df35507cd018011e0be6aa0f9a79f1df35507cd0389f1df35507cd08800023c06aa0f9a6011df35507ce1a7,0x11df355084f9a70001f35507cd0260001f35507cd1669f1e2be6aa0f9a8] : Array Nat)[i/32]?.getD 0) 60 (i%32)
  | 8, i => fld ((#[0x4c8ef9aa83e69e3be6aa0f9a02f1df35507cd0a78ef9ab2507cd3c77cd541f344de8477cd541f34f1df35507cd0d78ef9db5507cd3c77cd58283e69e3c37cd541f34f1e2be6aa0f9a78ef9aa84a7cd3cf8ef9aa83e69e3be70d541f34f1df3a6aa0f9a78ef9aa83e683bc78cf9aa83e69e3c47cd541f34f3a3be6aa0f9a78ef9aa83e68c3c77cd541f3431e3be6aa0f9a06f1df35507cd0079b1df35507cd3c77cd541f3421e3be6aa0f9a0ce023be6aa0f9a6] : Array Nat)[i/32]?.getD 0) 53 (i%32)
  | 9, i => fld ((#[0x23be6aa0f9a6] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xe53b1dd10d40d4faf8d2b79e679f23b55f30141a5795ec7743e60353ea834ace799e7c8ed586a07c695] : Array Nat)[i/32]?.getD 0) 83 (i%32)
  | 5, i => fld ((#[0x9e7c8ed57cc2506948ee886a36a7d7c6948ee87cc06a7d506948ee886a06a7d7c6948eea86a36a7d7c6948ee87cc26a7d506948eea7cc06a7d506948eea86a06a7d7c6948eea7cc26a7d506949e7f8ed586a37c6949e7f8ed57cc0506949e7f8ed586a07c6949e7f8ed57cc2506949e7c8ed586a37c6949e7c8ed57cc0506949e7c8ed586a07c694] : Array Nat)[i/32]?.getD 0) 68 (i%32)
  | 6, i => fld ((#[0x8ed686a07c6938eea6a7d506938ed67cc2506938eea6a7d7c6938ee87ca16a7d386a36a7f7c6939e7f8ed57c6a37cc06a7f506939e7f8ed5506a386a06a7f7c69370636a696a6831a0d6a7f7c6a38eea7ca16a7d306058ed67c6a37cc26a7f5069310058ed6506a39e7c8ed57c6a39e7c8ed5506a38ed586a37c6938ed57cc0506938ed586a07c6938ee86a7d7c6a38ed57cc2506938ee86a7d506a39e7f8ed5506931a216a7f506a386a36a7d7c6939e7f8ed57c6938eea6a7d7c6a37cc06a7d506938eea6a7d506a386a06a7d7c693,0x7cc26a7d506939e7f8ed57ca139e7c8ed55069386a38e7d7c6937cc08e7d506939e7c8ed57c69386a08e7d7c6937cc28e7d506938ee86a7d506938ed686a37c6939e7c8ed57ca1370636a696a6838ed67cc0506938ee86a7d7c693] : Array Nat)[i/32]?.getD 0) 52 (i%32)
  | 7, i => fld ((#[0x3e018e6a27c636a6828ed67ca129e7f8ed526a6b6a6a26a7f506926a7f7c6923e21506a27c616a6826a7d7c6a26a23506a26a0d7c6a26a7d506a27c2b6aa3200006a6919e7c8ed527ca16a7f234078ed628e7d7c6a23e038e6a27c058ed628e7d506a28ed5506928ee86a7d28ed57c6923e616a6828e21506a28ed67c6a234376a7f28ed6506a26a21506a28e333e6a2,0x50356a7f26a7d506928e313e6a26a7d7c6923e636a6828e616a68234058ed6286a37c6926a7f7c6a27cc0506926a696a68250616a6826a7f506a286a07c6928e7d506927ca16a7d250058ed628e0d7c6a27cc2506928e7d7c6926a0f7c6a250197cd62501b7cd6250636a6828ed6506927ca18e7d28ed67c6927c356a7f28ed57c6a28ed5506a27c296aa3234356a7f2,0x3e0d7c6a28eea6a7d28e636a6828ed57ca12] : Array Nat)[i/32]?.getD 0) 36 (i%32)
  | 8, i => fld ((#[0x8e6918ed616aa31507d16a6b18ef916a7f16aa11506917c6917ca113e6918ed516a6916a7d16a6a17cd517c7d18ea116a6813e6a17c6a18e6a18e7d1506a17cd6100000] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 9, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 6, i => fld ((#[0x4600010000080002000040002000010008c00008000ab82078000000004000000004000000002600054000080001000020042800008010c00008000000004000020000400020000200008,0x4000020000800004000080002000020000400020000100005c113c004280002] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 7, i => fld ((#[0x8b8781193c040660154f18327c00332000d42518f1c337a004a848c9e2466f400c608113c0049e0045f0103514497c010661061f0a81f8022550012a2014f400198c1d3c0a83e000332832780025448d9e3030f,0x22267a0063062c3e8012a083278c197ca20be1428f00035100a3ce089e346cf000660408bc0112a0212a2286f81507c2845e008331233785133c208de0864f8004a8020ce000661442f40019a00254e88de5044f,0x1289780117c2249e02033] : Array Nat)[i/32]?.getD 0) 21 (i%32)
  | 8, i => fld ((#[0x14587c020be6444f328c79c193c2a87e0044f32267d10a3e2845e120af38987a0517ce0c9ea154f383278d11bc6a25e4549f383279c4c3c0845e5161f0068f810a3c688de0024f] : Array Nat)[i/32]?.getD 0) 21 (i%32)
  | 9, i => fld ((#[15] : Array Nat)[i/32]?.getD 0) 4 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 7 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 7 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C57


namespace C58

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffffffff00000000ffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xfffeffee00000000fefaeea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(1,65),(2,10),(2,66),(3,7),(3,11),(3,19),(3,67),(4,5),(4,20),(6,7),(6,14),(6,22),(6,70),(8,9),(8,10),(8,72),(12,13),(12,14),(12,28),(12,76),(16,17),(16,20),(18,19),(18,22),(18,26),(18,82),(24,25),(24,26),(24,28),(24,88),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(68,84),(80,81),(80,82),(80,84),(80,88)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0x333333330000000033333333,0x333233220000000032322220,8,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xffffffff,0xfefaeea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xffff000000000000ffff,0xffee000000000000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xff00ff0000000000ff00ff,0xfe00ee0000000000fa00a0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f000000000f0f0f0f,0xf0e0f0e000000000e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xffff000000000000ffff0000,0xfffe000000000000fefa0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f000000000f0f0f0f0,0xf0f0f0e000000000f0f0e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xcccccccc00000000cccccccc,0xcccccccc00000000ccc8cc80,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x555555550000000055555555,0x555455440000000054504400,6,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x33333333,0x32322220,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xcccccccc,0xccc8cc80,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xf0f0000000000000f0f,0xf0e0000000000000e00,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0000000000000f0f0,0xf0e0000000000000e0a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x555500000000000055550000,0x555400000000000054500000,5,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0x3300330000000000330033,0x3200220000000000320020,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xcc00cc0000000000cc00cc,0xcc00cc0000000000c80080,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x505050500000000050505050,0x505050400000000050504000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x330033,0x320020,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0xcc00cc,0xc80080,4,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000]⟩,⟨0x5050000000000000505,0x5040000000000000400,4,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xaa00aa,0xaaaaaaaa,0xff00ffaa,0xff0aff0a,0xffaaffaa,0xfff0fff0,0xffffff00,0xaaaa000000000000aaaa,0xfafa000000000000fafa,0xaa00aa0000000000aa00aa,0xff00ff00000000000000aa,0xff00ff00000000000a000a,0xff00ff0000000000aa00aa,0xff00ff0000000000f000f0,0xff00ff0000000000ff0000,0xa0a0a0a000000000a0a0a0a,0xf0f0a0a000000000f0f0a0a,0x333333330000000033003300,0x3333bbbb000000003300bbaa,0x3b3b3b3b000000003b0a3b0a,0xaaaaaaaa00000000aaaaaaaa,0xbbbbbbbb00000000bbaabbaa,0xcccccccc00000000cccccccc,0xcccccccc00000000eeeeeeee,0xcccceeee00000000cccceeee,0xcceeccee00000000cceeccee,0xcececece00000000cececece,0xeeeeeeee00000000eeeeeeee,0xf0f0a0a000000000f0f0a0a0,0xf0f0f0f000000000f0f0f0f0,0xfafa000000000000fafa0000,0xfafafafa00000000fafafafa,0xff00ff0000000000ff00ff00,0xff00ff0000000000ffaaffaa,0xff00ffaa00000000ff00ffaa,0xff0aff0a00000000ff0aff0a,0xffaaffaa00000000ffaaffaa,0xfff0fff000000000fff0fff0,0xffff000000000000ffff0000,0xffffaaaa00000000ffffaaaa,0xfffff0f000000000fffff0f0,0xffffff0000000000ffffff00,0xffffffff0000000000000000,0xffffffff000000000000aaaa,0xffffffff0000000000aa00aa,0xffffffff000000000a0a0a0a,0xffffffff00000000aaaaaaaa,0xffffffff00000000f0f0f0f0,0xffffffff00000000ff00ff00,0xffffffff00000000ff00ffaa,0xffffffff00000000ff0aff0a,0xffffffff00000000ffaaffaa,0xffffffff00000000fff0fff0,0xffffffff00000000ffff0000,0xffffffff00000000ffffff00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 5 => 7
  | 6 => 30
  | 7 => 46
  | 8 => 15
  | 9 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 5, i => fld ((#[0xe2f1fa906d8ed576275c5cf553ec3628be9] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0xf7c51f3332e4c71d59ded0367c7c91c7574c3117c2e52b3b1daadbfa761ba486b95dd594c078d3d47a2be788ad6a399675155edd55dbaf4eca64894c4098838424347c32a93b14b4405dd4] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0xafdadaeb84a9307a65bda5c3ea05e79240f8ba518704685a2776b1e7411b735c46f4366db8d6926768eba64d9a6402855a6753ced4476838b74365152f0082430320fb21b1aa1b0bc12ef30a7f40a3f7,0xeb0c4eaf1de6f14e3954e075ac9d7ac92c6c763dc4bd1c4ba4c2378bfb89bfac5b1aa8] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 8, i => fld ((#[0xed4b0ba75eb23daaa86294161714cd707c460ed250eed4d50f48ded398e12f4ee2a8060708f] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 9, i => fld ((#[0x183aa] : Array Nat)[i/32]?.getD 0) 17 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 5, i => fld ((#[0xaa07544486aa079d5116aa681d512699d5943046aa681d5136aa68144506aa681c5116] : Array Nat)[i/32]?.getD 0) 40 (i%32)
  | 6, i => fld ((#[0xba692075611f3aa675650c7c2a81d59421f0ae681d5947c2a9a275651f09a47565047aa681d5111dee9a07565047aa89a075445ea9a075650a7c2a81e75651f0aa68dd5947aa681f75445c0aa681d5546aa681d5942df39a07565047aa681d5940df2aa681d5947c2d9a075651ea9e681d5117c6a9a075651eeaa691d58c7c2e99d59431ea9a475650c7c2a9a059441f0ba691d5947aa681d5113df0aa681c5947030ba691d59aa9a07565027] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 7, i => fld ((#[0x2baa681d5947000aa681c5946baa9a481d5948c2a9a07dd5948000aa681d6c16000aa681d6946000aa681d511602a9a0756505702a9a075650c702eaa69207567030ba681d5947034aa681d5947cea9a481d5948000aa681d5d4602a9a07565067c2a9e681d5948000aa07565086000aa681d614602a9a481d5817030aa691d5947ceeaa681d594802daa681d5947aa69207565048c2a9a075650f8000aa079d594602a9a075650e7000aa681d6c96033aa681d5947000aa681d654602a9a181d594702a9a481d6d4702a9a07565007,0x2a9a281d594702eaa681d6d47000aa692075b6036aa681d594702a9a0756504702a9a075650d7c2a9a07565078000baa9a075b6000aa68165106c2aa2681d594802a9a381d5947baa9a075650c802eaa681d589702caa681d5947] : Array Nat)[i/32]?.getD 0) 52 (i%32)
  | 8, i => fld ((#[0x2a9e681d5947aa681d5943dc0aa681d6d46aa681d59425f0aa681d5947bea9a075651ea9a481d5947aa99a075651eeaa681d5947aa681d5941deaa2681d5947aa696075651ea9a07565017aa681f75651f5aa681d5947] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 9, i => fld ((#[0xaa681d5946] : Array Nat)[i/32]?.getD 0) 40 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 5, i => fld ((#[0xc16ea8199f9d514c16ea8199f1d514447705baa066524aa4ae83a946051444f705baa05d524c16ea819dde6514c16ea819dd26514] : Array Nat)[i/32]?.getD 0) 60 (i%32)
  | 6, i => fld ((#[0xaa4aa518144f383aa460513aa0667e7544ea81a8766523aa0601d9948ea92aa060513c16ea819948ea92a9460513c16ea8199d4eb83a8766523aa0667c7544ea8180f5d523c16ea817544d445c16ea813b60ea3d7548f3abaa460513aa3a03d7548ea8d80f5d523aa06a3d7548f05baa066513aa2601d9948ee83a9460513ba0ea81a944ee83a9460513aa067779944ea81a9460513c16ea817548ea819dd26513aa06a518144ea8a80766523] : Array Nat)[i/32]?.getD 0) 46 (i%32)
  | 7, i => fld ((#[0xa87665229dd26512a9460512aa05d512a949651258f5d522c16ea812aa5a0752ba0ea512a9460512aa06a512c1d6a812aa4605125816a522aa9a6812aa06651299f9d51258766522a94a0512aa060512ba06a512a8f5d522aa4a0512aa05d52299f1d512d60ea99281496512aa460512589605228016a52281456512c14aa812,0x80766522a945651281456512c266a812aa4a0512be0ea752aa066522a94565129dde6512aa06675280f5d522ba0ea512a9460522a8960522] : Array Nat)[i/32]?.getD 0) 32 (i%32)
  | 8, i => fld ((#[0x2651175485651181486a811a9d4605119a046a51199486675181d46a52175446a991] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | 9, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 5, i => fld ((#[0x8000000000000000000] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 6, i => fld ((#[0x8160001000060002000014000a008090000c000200000000a6000080008000800000180004000040001000100001200008010880015000240001c010b008200009d908580000] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 7, i => fld ((#[0x113f0213f4010ba00535279f4959f0049f1105f5201f1210b7210b5105f6000b5259f0303fa00270313f4959f7210b7210b6000b0115f4010a6005b1015f0303f5e59f7201f5a59f5211f5a11f5211f,0x113f5251f5a59f4303f5201f1105f6002f5259f0315f008270115f4010a7210b5211f] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 8, i => fld ((#[0x8313f0115f5a59f1211f6001f1105f1211f0303f1211f0113f0287f1105f1211f9115f0303f] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 9, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 6 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 6 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C58


namespace C59

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffff0000ffff0000ffff0000ffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xffee0000ffee0000ffec0000eea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,65),(2,10),(2,34),(2,66),(3,7),(3,11),(3,35),(3,67),(4,5),(6,7),(6,14),(6,38),(6,70),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,44),(12,76),(32,34),(32,40),(33,35),(33,37),(33,41),(33,97),(36,37),(36,38),(36,44),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(96,97),(96,98),(96,104),(100,101),(100,102),(100,108)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xffff0000ffff,0xffec0000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xffff000000000000ffff,0xffee000000000000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f,0xf0e00000f0e00000f0c00000e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f0,0xf0e00000f0e00000f0e00000e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x3333000033330000333300003333,0x3322000033220000332000002220,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xff000000ff000000ff000000ff,0xee000000ee000000ec000000a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x505000005050000050500000505,0x504000005040000050400000400,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x5050000050500000505000005050,0x5040000050400000504000004000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xffee0000ffee,0xddcc000000000000ddcc,0xffcc000000000000ffcc,0xffee000000000000ffee,0xee000000ee000000ee000000ee,0xa0a00000a0a00000a0a00000a0a,0x1100000011000000110000001100,0x3300000033000000330000003300,0x3322000033220000332200003322,0x3b0a00003b0a00003b0a00003b0a,0x5500000055000000550000005500,0x5544000055440000554400005544,0xaaaa0000aaaa0000aaaa0000aaaa,0xbbaa0000bbaa0000bbaa0000bbaa,0xcccc0000cccc0000cccc0000cccc,0xddcc0000ddcc0000ddcc0000ddcc,0xee000000ee000000ee000000ee00,0xeeee0000eeee0000eeee0000eeee,0xf0f00000f0f00000f0f00000f0f0,0xf3f00000f3f00000f3f00000f3f0,0xff000000ff000000ff000000ff00,0xff0a0000ff0a0000ff0a0000ff0a,0xffaa0000ffaa0000ffaa0000ffaa,0xffcc0000ffcc0000ffcc0000ffcc,0xffee0000ffee0000ffee0000ffee,0xfff00000fff00000fff00000fff0,0xffff000000000000ffff00000000,0xffff0000ee000000ffff0000ee00,0xffff0000ffff0000000000000000,0xffff0000ffff0000ee000000ee00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 17
  | 7 => 7
  | 8 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0x1a8c657f698aea6] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 5, i => fld ((#[0xf4c7debc15cb3e4a6b758c7a2492fe375ba3008f242d1187f4] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0xf89f5f3292f0996a6a67a5bcd9fed29a28c949e8843198076678fb55daa95448953f883ab09128a70c0a8] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0xcd4e3c789da6ff4a46d996240575da3ae1e] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 8, i => fld ((#[0x6842f] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x73779317bab49cbdd5e4c5] : Array Nat)[i/32]?.getD 0) 29 (i%32)
  | 5, i => fld ((#[0xd524e601b9ba49cc6e51cc289b94939816eea92731b9ab4a0e6e668e609b9aa39896e6af2831b94939836] : Array Nat)[i/32]?.getD 0) 34 (i%32)
  | 6, i => fld ((#[0x394939826e6a927310e0e6ab4731b9aa49cd63f354941cc7e6af4730afcd51cc395f9ac524e63f354939867e6a927b98fcd5a928b9f97a49cc13f354939847e6af49458fcd524e62dc1cd526e637359bd1cc7] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 7, i => fld ((#[0x1cd5e92731f9aa49cc3b839acd1cc6e6a928b98fcd524e629f9ab524e63839aa39856] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 8, i => fld ((#[0x39aa49cc6] : Array Nat)[i/32]?.getD 0) 34 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xd41a44a397314e41a44a317314e41a44a397314] : Array Nat)[i/32]?.getD 0) 52 (i%32)
  | 5, i => fld ((#[0xe62a457313d41a447313d5ea399323d3e729a333e41a447313a44a317313d5ea49a393395a3b9323a44a397313d62a457313] : Array Nat)[i/32]?.getD 0) 40 (i%32)
  | 6, i => fld ((#[0xd5ea392b3ba312a15932261da3b2a447312a399322a3b9322a457312a477312729a332a317312d5ea392a467312a397312bb3a39291da3b2a49a392] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 7, i => fld ((#[0xa391a3b1a4917311a331a3119321] : Array Nat)[i/32]?.getD 0) 16 (i%32)
  | 8, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 6, i => fld ((#[0x5004d84d7121887840294128446844d12] : Array Nat)[i/32]?.getD 0) 8 (i%32)
  | 7, i => fld ((#[0x7777ffd7f7f75f] : Array Nat)[i/32]?.getD 0) 8 (i%32)
  | 8, i => fld ((#[87] : Array Nat)[i/32]?.getD 0) 7 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 5 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 5 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C59


namespace C62

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0c0e0a0e00
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,9),(1,17),(1,65),(2,10),(2,34),(2,66),(3,11),(3,19),(3,35),(3,67),(8,9),(8,10),(8,40),(8,72),(16,17),(18,19),(18,26),(18,50),(18,82),(24,25),(24,26),(24,56),(24,88),(32,34),(32,40),(33,35),(33,41),(33,49),(33,97),(48,49),(48,50),(48,56),(64,65),(64,66),(64,72),(80,81),(80,82),(80,88),(96,97),(96,98),(96,104),(112,113),(112,114),(112,120)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xf0f0f0f0f0f0f0f,0xf0e0f0c0e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f000000000f0f0f0f,0xf0e0f0e000000000e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f,0xf0e00000f0e00000f0c00000e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f0000,0xf0e00000f0e00000f0e00000e0a0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x3030303030303030303030303030303,0x3020302030203020302030002020200,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x505000005050000050500000505,0x504000005040000050400000400,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x5050000050500000505000005050000,0x5040000050400000504000004000000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf000f000f000f000f000f000f000f,0xe000e000e000e000e000c000a0000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0xf0e0f0e0f0e0f0e,0xd0c0d0c000000000d0c0d0c,0xf0c0f0c000000000f0c0f0c,0xf0e0f0e000000000f0e0f0e,0xa0a00000a0a00000a0a00000a0a,0xe000e000e000e000e000e000e000e,0x1000100010001000100010001000100,0x3000300030003000300030003000300,0x3000b0a03000b0a03000b0a03000b0a,0x3020302030203020302030203020302,0x5000500050005000500050005000500,0x5040504050405040504050405040504,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xb0a0b0a0b0a0b0a0b0a0b0a0b0a0b0a,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0xd0c0d0c0d0c0d0c0d0c0d0c0d0c0d0c,0xe000e000e000e000e000e000e000e00,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e,0xf000f000f000f000f000f000f000f00,0xf000f0a0f000f0a0f000f0a0f000f0a,0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a,0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c,0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e,0xf0f00000f0f00000f0f00000f0f0000,0xf0f03000f0f03000f0f03000f0f0300,0xf0f0f000f0f0f000f0f0f000f0f0f00,0xf0f0f0f000000000f0f0f0f00000000,0xf0f0f0f0e000e000f0f0f0f0e000e00,0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0e000e000e000e00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 17
  | 7 => 7
  | 8 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 4, i => fld ((#[0xfb3ab9612f95004] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 5, i => fld ((#[0x86778807087f5dd7b9404e51c47c5131ea1295d71559906c84] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0xffddcffb72d1c5dc622d9edf991a3b8bfb7856ec7a5e87583756e2b4c95f4897d3800430bd61f0c713aa2] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0x1c08bb7338e9963c6adaf137d471426ce3] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | 8, i => fld ((#[0x528e8] : Array Nat)[i/32]?.getD 0) 19 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 4, i => fld ((#[0x7757a3979bbd58bdd5eac5] : Array Nat)[i/32]?.getD 0) 29 (i%32)
  | 5, i => fld ((#[0xd5e4e601b9bbc9cc6eeaf2731b9abd20e6e664e609b92730826e5e4e60db97939816e6af5831b9a939886] : Array Nat)[i/32]?.getD 0) 34 (i%32)
  | 6, i => fld ((#[0x7357b49cc7e6af28398fcd5eb28b1f9abc9cc2bf357939867e6af27358fcd66b2731f9aac9cc23f352730e47073589398dcd5e4e62df97ac9cc13839a9c9cc6e6af4945ce0e5e4e609b9abc9ee63f357939897] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 7, i => fld ((#[0xe6b32731b9abd64e63839a939846e6af2730efcd5e4e629f9abca2e63f357a49cc7] : Array Nat)[i/32]?.getD 0) 39 (i%32)
  | 8, i => fld ((#[0x39abc9cc6] : Array Nat)[i/32]?.getD 0) 34 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 4, i => fld ((#[0xe419449317314d419449397314e419449397314] : Array Nat)[i/32]?.getD 0) 52 (i%32)
  | 5, i => fld ((#[0xe5a9457313d419447313e4194473139449317313d56bc99393d56939bb23d5a9457313d3e7299333944939731339193bbb23] : Array Nat)[i/32]?.getD 0) 40 (i%32)
  | 6, i => fld ((#[0x9457312944731293973129467312947731261d93b2bc99392939bb2293bbb22b9d93b2ab39392d569392911bb229317312d5693927299332a3b9312] : Array Nat)[i/32]?.getD 0) 28 (i%32)
  | 7, i => fld ((#[0xbc919391bb2193b1933173119311] : Array Nat)[i/32]?.getD 0) 16 (i%32)
  | 8, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 4, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 5, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 6, i => fld ((#[0x47ee9a24488489185b1092da814100] : Array Nat)[i/32]?.getD 0) 7 (i%32)
  | 7, i => fld ((#[0xffb73fb7f777f7] : Array Nat)[i/32]?.getD 0) 8 (i%32)
  | 8, i => fld ((#[55] : Array Nat)[i/32]?.getD 0) 6 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 5 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 5 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,0,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C62


namespace C67

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def d : Nat := 0xffffffffffffffffffffffffffffffff
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def target : Nat := 0xfffeffeefffeffeefffeffecfefaeea0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def roots : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pairs : List (Nat × Nat) := [(1,5),(1,9),(1,17),(1,65),(2,10),(2,34),(2,66),(3,7),(3,11),(3,19),(3,35),(3,67),(4,5),(4,20),(6,7),(6,14),(6,22),(6,38),(6,70),(8,9),(8,10),(8,40),(8,72),(12,13),(12,14),(12,28),(12,44),(12,76),(16,17),(16,20),(18,19),(18,22),(18,26),(18,50),(18,82),(24,25),(24,26),(24,28),(24,56),(24,88),(32,34),(32,40),(33,35),(33,37),(33,41),(33,49),(33,97),(36,37),(36,38),(36,44),(36,52),(48,49),(48,50),(48,52),(48,56),(64,65),(64,66),(64,72),(68,69),(68,70),(68,76),(68,84),(80,81),(80,82),(80,84),(80,88),(96,97),(96,98),(96,104),(100,101),(100,102),(100,108),(100,116),(112,113),(112,114),(112,116),(112,120)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def cuts : List Cut := [⟨0xffffffffffffffff,0xfffeffecfefaeea0,10,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xffffffff00000000ffffffff,0xfffeffee00000000fefaeea0,10,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xffff0000ffff0000ffff0000ffff,0xffee0000ffee0000ffec0000eea0,9,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xf0e0f0e0f0e0f0e0f0e0f0c0e0a0e00,9,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x33333333333333333333333333333333,0x33323322333233223332332032322220,9,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x333333330000000033333333,0x333233220000000032322220,8,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xff00ff00ff00ff00ff00ff00ff00ff,0xfe00ee00fe00ee00fe00ec00fa00a0,8,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xffff0000ffff,0xffec0000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f0f0f0f0f,0xf0e0f0c0e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x3333333333333333,0x3332332032322220,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xffff000000000000ffff,0xffee000000000000eea0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xff00ff0000000000ff00ff,0xfe00ee0000000000fa00a0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f000000000f0f0f0f,0xf0e0f0e000000000e0a0e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f,0xf0e00000f0e00000f0c00000e00,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xffff0000ffff0000ffff0000ffff0000,0xfffe0000fffe0000fffe0000fefa0000,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0e0a0,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xcccccccccccccccccccccccccccccccc,0xccccccccccccccccccccccccccc8cc80,7,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x55555555555555555555555555555555,0x55545544555455445554554454504400,7,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xffff0000ffff0000,0xfffe0000fefa0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xff00ff00ff00ff,0xfe00ec00fa00a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xf0f0f0f0f0f0f0f0,0xf0f0f0e0f0f0e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xcccccccccccccccc,0xccccccccccc8cc80,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x5555555555555555,0x5554554454504400,6,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0xffff000000000000ffff0000,0xfffe000000000000fefa0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000]⟩,⟨0xff00ff0000000000ff00ff00000000,0xfe00ee0000000000fe00ec00000000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f0f0f000000000f0f0f0f0,0xf0f0f0e000000000f0f0e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xcccccccc00000000cccccccc,0xcccccccc00000000ccc8cc80,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x33333333000000003333333300000000,0x33323322000000003332332000000000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x555555550000000055555555,0x555455440000000054504400,6,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f0,0xf0e00000f0e00000f0e00000e0a0,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf0f00000f0f00000f0f00000f0f0000,0xf0e00000f0e00000f0e00000e0a0000,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x3333000033330000333300003333,0x3322000033220000332000002220,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x55550000555500005555000055550000,0x55540000555400005554000054500000,6,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xcc00cc00cc00cc00cc00cc00cc00cc,0xcc00cc00cc00cc00cc00cc00c80080,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x3030303030303030303030303030303,0x3020302030203020302030002020200,6,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x50505050505050505050505050505050,0x50505040505050405050504050504000,6,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x5555000055550000,0x5554000054500000,5,[0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000]⟩,⟨0xcc00cc00cc00cc,0xcc00cc00c80080,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x5050505050505050,0x5050504050504000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]⟩,⟨0x3300330000000000330033,0x3200220000000000320020,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xcc00cc0000000000cc00cc,0xcc00cc0000000000c80080,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0x330033000000000033003300000000,0x320022000000000032002000000000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000]⟩,⟨0xff000000ff000000ff000000ff,0xee000000ee000000ec000000a0,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x303000003030000030300000303,0x302000003020000030000000200,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x505000005050000050500000505,0x504000005040000050400000400,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x5050000050500000505000005050,0x5040000050400000504000004000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0x5050000050500000505000005050000,0x5040000050400000504000004000000,5,[0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩,⟨0xf000f000f000f000f000f000f000f,0xe000e000e000e000e000c000a0000,5,[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def dict (i : Nat) : Nat := ((#[0x554455ee554455ee,0x5544ffee5544ffee,0x554e554e554e554e,0x55aa55aa55aa55aa,0x5f4e5f4e5f4e5f4e,0xffccffceffccffce,0xffccffeeffccffee,0xffceffceffceffce,0xffeeffeeffeeffee,0xfffefffefffefffe,0xffffffeeffffffee,0xddccddcc00000000ddccddcc,0xfdccfdcc00000000fdccfdcc,0xfdecfdec00000000fdecfdec,0xffccddcc00000000ffccddcc,0xffccfdcc00000000ffccfdcc,0xffccffcc00000000ffccffcc,0xffccffce00000000ffccffce,0xffccffee00000000ffccffee,0xffceffce00000000ffceffce,0xffeeddcc00000000ffeeddcc,0xffeeffee00000000ffeeffee,0xfffcfffc00000000fffcfffc,0xfffefffe00000000fffefffe,0xffffffcc00000000ffffffcc,0xffffffee00000000ffffffee,0xfffffffc00000000fffffffc,0x22000000220000002200000022,0xaa000000aa000000aa000000aa,0xee000000ee000000ee000000ee,0xa0a00000a0a00000a0a00000a0a,0xf0000000f0000000f0000000f00,0xf0c00000f0c00000f0c00000f0c,0x2222000022220000222200002222,0x3300000033000000330000003300,0x5500000055000000550000005500,0x5544000055440000554400005544,0x88aa000088aa000088aa000088aa,0xaa000000aa000000aa000000aa00,0xaa880000aa880000aa880000aa88,0xaaaa0000aaaa0000aaaa0000aaaa,0xbbaa0000bbaa0000bbaa0000bbaa,0xeeee0000eeee0000eeee0000eeee,0xf0fa0000f0fa0000f0fa0000f0fa,0xf3f00000f3f00000f3f00000f3f0,0xf8fa0000f8fa0000f8fa0000f8fa,0xfafa0000fafa0000fafa0000fafa,0xfbfa0000fbfa0000fbfa0000fbfa,0xfcfc0000fcfc0000fcfc0000fcfc,0xfefe0000fefe0000fefe0000fefe,0xff000000ff000000ff000000ff00,0xffaa0000ffaa0000ffaa0000ffaa,0xffcc0000ffcc0000ffcc0000ffcc,0xffee0000ffee0000ffee0000ffee,0xfff00000fff00000fff00000fff0,0xfffa0000fffa0000fffa0000fffa,0xfffe0000fffe0000fffe0000fffe,0x20002000200020002000200020002,0xa000a000a000a000a000a000a000a,0xe000e000e000e000e000e000e000e,0x220022002200220022002200220022,0x320032003200320032003200320032,0x330022003300220033002200330022,0x540054005400540054005400540054,0x550044005500440055004400550044,0xaa00aa00aa00aa00aa00aa00aa00aa,0xcc00ce00cc00ce00cc00ce00cc00ce,0xcc00ee00cc00ee00cc00ee00cc00ee,0xce00ce00ce00ce00ce00ce00ce00ce,0xee00ee00ee00ee00ee00ee00ee00ee,0xfa00fa00fa00fa00fa00fa00fa00fa,0xfc00fc00fc00fc00fc00fc00fc00fc,0xff00aa00ff00aa00ff00aa00ff00aa,0xff00cc00ff00cc00ff00cc00ff00cc,0x2020202020202020202020202020202,0x3000300030003000300030003000300,0x5000500050005000500050005000500,0x5040504050405040504050405040504,0x80a080a080a080a080a080a080a080a,0xa000a000a000a000a000a000a000a00,0xa080a080a080a080a080a080a080a08,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xb0a0b0a0b0a0b0a0b0a0b0a0b0a0b0a,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e,0xf000f000f000f000f000f000f000f00,0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a,0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c,0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e,0xf0f000a0f0f000a0f0f000a0f0f000a,0xf0f03000f0f03000f0f03000f0f0300,0xf0f080a0f0f080a0f0f080a0f0f080a,0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xf0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a,0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c,0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e,0xf0f0f000f0f0f000f0f0f000f0f0f00,0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a,0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c,0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e,0x10f010f010f010f010f010f010f010f0,0x11001100110011001100110011001100,0x110011aa110011aa110011aa110011aa,0x1100bbaa1100bbaa1100bbaa1100bbaa,0x110a110a110a110a110a110a110a110a,0x11101110111011101110111011101110,0x11111100111111001111110011111100,0x11aa11aa11aa11aa11aa11aa11aa11aa,0x11fa11fa11fa11fa11fa11fa11fa11fa,0x11ff000011ff000011ff000011ff0000,0x11ff11aa11ff11aa11ff11aa11ff11aa,0x1b0a1b0a1b0a1b0a1b0a1b0a1b0a1b0a,0x22002200220022002200220022002200,0x22222222222222222222222222222222,0x30f010f030f010f030f010f030f010f0,0x31003100310031003100310031003100,0x31ff000031ff000031ff000031ff0000,0x32323232323232323232323232323232,0x33001100330011003300110033001100,0x33003100330031003300310033003100,0x33003300330033003300330033003300,0x33003302330033023300330233003302,0x33003322330033223300332233003322,0x33003b0a33003b0a33003b0a33003b0a,0x3300bbaa3300bbaa3300bbaa3300bbaa,0x33023302330233023302330233023302,0x33223322332233223322332233223322,0x33303330333033303330333033303330,0x33323332333233323332333233323332,0x33332222333322223333222233332222,0x33333300333333003333330033333300,0x33333322333333223333332233333322,0x33333330333333303333333033333330,0x3b0a3b0a3b0a3b0a3b0a3b0a3b0a3b0a,0x444444cc444444cc444444cc444444cc,0x444c444c444c444c444c444c444c444c,0x44664466446644664466446644664466,0x44cc44cc44cc44cc44cc44cc44cc44cc,0x505050f0505050f0505050f0505050f0,0x5050d0f05050d0f05050d0f05050d0f0,0x50f050f050f050f050f050f050f050f0,0x51505150515051505150515051505150,0x54545454545454545454545454545454,0x55005500550055005500550055005500,0x550055aa550055aa550055aa550055aa,0x5500ffaa5500ffaa5500ffaa5500ffaa,0x550a550a550a550a550a550a550a550a,0x55445544554455445544554455445544,0x554455ee554455ee554455ee554455ee,0x5544ffee5544ffee5544ffee5544ffee,0x554e554e554e554e554e554e554e554e,0x55505550555055505550555055505550,0x55551100555511005555110055551100,0x55554444555544445555444455554444,0x55555500555555005555550055555500,0x55555544555555445555554455555544,0x555f0000555f0000555f0000555f0000,0x55aa55aa55aa55aa55aa55aa55aa55aa,0x55ff000055ff000055ff000055ff0000,0x5d5f00005d5f00005d5f00005d5f0000,0x5f0a5f0a5f0a5f0a5f0a5f0a5f0a5f0a,0x5f4e5f4e5f4e5f4e5f4e5f4e5f4e5f4e,0x88aa88aa88aa88aa88aa88aa88aa88aa,0xa0a2a0a2a0a2a0a2a0a2a0a2a0a2a0a2,0xa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa,0xa2a0a2a0a2a0a2a0a2a0a2a0a2a0a2a0,0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xaa88aa88aa88aa88aa88aa88aa88aa88,0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0,0xaaaa0022aaaa0022aaaa0022aaaa0022,0xaaaa00aaaaaa00aaaaaa00aaaaaa00aa,0xaaaa2200aaaa2200aaaa2200aaaa2200,0xaaaa8888aaaa8888aaaa8888aaaa8888,0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00,0xaaaaaa88aaaaaa88aaaaaa88aaaaaa88,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffaaaaaaffaaaaaaffaaaaaaffaa,0xaaaaffeeaaaaffeeaaaaffeeaaaaffee,0xafaaafaaafaaafaaafaaafaaafaaafaa,0xafaeafaeafaeafaeafaeafaeafaeafae,0xbbaabbaabbaabbaabbaabbaabbaabbaa,0xbbbabbbabbbabbbabbbabbbabbbabbba,0xbbbbbbaabbbbbbaabbbbbbaabbbbbbaa,0xc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4cc,0xc8fac8fac8fac8fac8fac8fac8fac8fa,0xcc00ce00cc00ce00cc00ce00cc00ce00,0xcc00dd00cc00dd00cc00dd00cc00dd00,0xcc00ee00cc00ee00cc00ee00cc00ee00,0xcccc44cccccc44cccccc44cccccc44cc,0xcccccccccccccccccccccccccccccccc,0xcccccceecccccceecccccceeccccccee,0xcccccececccccececccccececccccece,0xcccccfcccccccfcccccccfcccccccfcc,0xccccddccccccddccccccddccccccddcc,0xcccceecccccceecccccceecccccceecc,0xcccceeeecccceeeecccceeeecccceeee,0xccccffccccccffccccccffccccccffcc,0xccccffeeccccffeeccccffeeccccffee,0xccceccceccceccceccceccceccceccce,0xcceecceecceecceecceecceecceeccee,0xccfeccfeccfeccfeccfeccfeccfeccfe,0xccff88aaccff88aaccff88aaccff88aa,0xccffcceeccffcceeccffcceeccffccee,0xcd00cd00cd00cd00cd00cd00cd00cd00,0xcdcccdcccdcccdcccdcccdcccdcccdcc,0xce00ce00ce00ce00ce00ce00ce00ce00,0xcecccecccecccecccecccecccecccecc,0xcececececececececececececececece,0xcfcccfcccfcccfcccfcccfcccfcccfcc,0xcfcecfcecfcecfcecfcecfcecfcecfce,0xd0f0d0f0d0f0d0f0d0f0d0f0d0f0d0f0,0xdd00dd00dd00dd00dd00dd00dd00dd00,0xddccddccddccddccddccddccddccddcc,0xddff0000ddff0000ddff0000ddff0000,0xee00ee00ee00ee00ee00ee00ee00ee00,0xee00eeaaee00eeaaee00eeaaee00eeaa,0xee0aee0aee0aee0aee0aee0aee0aee0a,0xeecceecceecceecceecceecceecceecc,0xeee0eee0eee0eee0eee0eee0eee0eee0,0xeeeceeeceeeceeeceeeceeeceeeceeec,0xeeeeee00eeeeee00eeeeee00eeeeee00,0xeeeeeecceeeeeecceeeeeecceeeeeecc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xf0f000a0f0f000a0f0f000a0f0f000a0,0xf0f000f0f0f000f0f0f000f0f0f000f0,0xf0f050f0f0f050f0f0f050f0f0f050f0,0xf0f080a0f0f080a0f0f080a0f0f080a0,0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0,0xf0f0a0b0f0f0a0b0f0f0a0b0f0f0a0b0,0xf0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0,0xf0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a0,0xf0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0,0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0,0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0,0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f3f0f0f0f3f0f0f0f3f0f0f0f3f0,0xf0f0f5f0f0f0f5f0f0f0f5f0f0f0f5f0,0xf0f0f5f4f0f0f5f4f0f0f5f4f0f0f5f4,0xf0f0faf0f0f0faf0f0f0faf0f0f0faf0,0xf0f0fafaf0f0fafaf0f0fafaf0f0fafa,0xf0f0fff0f0f0fff0f0f0fff0f0f0fff0,0xf0f0fffcf0f0fffcf0f0fffcf0f0fffc,0xf0fa0000f0fa0000f0fa0000f0fa0000,0xf0faf0faf0faf0faf0faf0faf0faf0fa,0xf0ff0000f0ff0000f0ff0000f0ff0000,0xf1f0f1f0f1f0f1f0f1f0f1f0f1f0f1f0,0xf2f0f2f0f2f0f2f0f2f0f2f0f2f0f2f0,0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2,0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0,0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2,0xf3f3f3f0f3f3f3f0f3f3f3f0f3f3f3f0,0xf500f500f500f500f500f500f500f500,0xf5a0f5a0f5a0f5a0f5a0f5a0f5a0f5a0,0xf5c4f5c4f5c4f5c4f5c4f5c4f5c4f5c4,0xf5e4f5e4f5e4f5e4f5e4f5e4f5e4f5e4,0xf5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0,0xf5f4f5f4f5f4f5f4f5f4f5f4f5f4f5f4,0xf5ff0000f5ff0000f5ff0000f5ff0000,0xf8fa0000f8fa0000f8fa0000f8fa0000,0xf8faf8faf8faf8faf8faf8faf8faf8fa,0xfa00fa00fa00fa00fa00fa00fa00fa00,0xfac8fac8fac8fac8fac8fac8fac8fac8,0xfaf0faf0faf0faf0faf0faf0faf0faf0,0xfaf8faf8faf8faf8faf8faf8faf8faf8,0xfafa0000fafa0000fafa0000fafa0000,0xfafaf2f0fafaf2f0fafaf2f0fafaf2f0,0xfafafaf0fafafaf0fafafaf0fafafaf0,0xfafafafafafafafafafafafafafafafa,0xfafb0000fafb0000fafb0000fafb0000,0xfaff0000faff0000faff0000faff0000,0xfbfa0000fbfa0000fbfa0000fbfa0000,0xfbfafbfafbfafbfafbfafbfafbfafbfa,0xfc00fc00fc00fc00fc00fc00fc00fc00,0xfca8fca8fca8fca8fca8fca8fca8fca8,0xfcf0fef0fcf0fef0fcf0fef0fcf0fef0,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xfcff0000fcff0000fcff0000fcff0000,0xfdccfdccfdccfdccfdccfdccfdccfdcc,0xfdecfdecfdecfdecfdecfdecfdecfdec,0xfeaafeaafeaafeaafeaafeaafeaafeaa,0xfeccfeccfeccfeccfeccfeccfeccfecc,0xfef0eea0fef0eea0fef0eea0fef0eea0,0xfef0fef0fef0fef0fef0fef0fef0fef0,0xfefaee00fefaee00fefaee00fefaee00,0xfefe0000fefe0000fefe0000fefe0000,0xfefefefefefefefefefefefefefefefe,0xff005500ff005500ff005500ff005500,0xff00aa00ff00aa00ff00aa00ff00aa00,0xff00cc00ff00cc00ff00cc00ff00cc00,0xff00f500ff00f500ff00f500ff00f500,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff0aff00ff0aff00ff0aff00ff0a,0xff00ffaaff00ffaaff00ffaaff00ffaa,0xff00ffeeff00ffeeff00ffeeff00ffee,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xff0eff0eff0eff0eff0eff0eff0eff0e,0xff22ff22ff22ff22ff22ff22ff22ff22,0xff32ff32ff32ff32ff32ff32ff32ff32,0xff33ff22ff33ff22ff33ff22ff33ff22,0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8,0xffaa5500ffaa5500ffaa5500ffaa5500,0xffaacc88ffaacc88ffaacc88ffaacc88,0xffaaeeaaffaaeeaaffaaeeaaffaaeeaa,0xffaaff88ffaaff88ffaaff88ffaaff88,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xffcc5544ffcc5544ffcc5544ffcc5544,0xffccaa88ffccaa88ffccaa88ffccaa88,0xffccddccffccddccffccddccffccddcc,0xffcceeccffcceeccffcceeccffcceecc,0xffccf5c4ffccf5c4ffccf5c4ffccf5c4,0xffccfdccffccfdccffccfdccffccfdcc,0xffccffccffccffccffccffccffccffcc,0xffccffceffccffceffccffceffccffce,0xffccffeeffccffeeffccffeeffccffee,0xffceffceffceffceffceffceffceffce,0xffee5544ffee5544ffee5544ffee5544,0xffeeddccffeeddccffeeddccffeeddcc,0xffeeffeeffeeffeeffeeffeeffeeffee,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xfffa0000fffa0000fffa0000fffa0000,0xfffafffafffafffafffafffafffafffa,0xfffcfffcfffcfffcfffcfffcfffcfffc,0xfffe0000fffe0000fffe0000fffe0000,0xfffefffefffefffefffefffefffefffe,0xffff0000ffff0000ffff0000ffff0000,0xffff00aaffff00aaffff00aaffff00aa,0xffff0300ffff0300ffff0300ffff0300,0xffff0500ffff0500ffff0500ffff0500,0xffff0504ffff0504ffff0504ffff0504,0xffff0a00ffff0a00ffff0a00ffff0a00,0xffff0a0affff0a0affff0a0affff0a0a,0xffff0f00ffff0f00ffff0f00ffff0f00,0xffff0f0cffff0f0cffff0f0cffff0f0c,0xffff1100ffff1100ffff1100ffff1100,0xffff2200ffff2200ffff2200ffff2200,0xffff2222ffff2222ffff2222ffff2222,0xffff3300ffff3300ffff3300ffff3300,0xffff3322ffff3322ffff3322ffff3322,0xffff3330ffff3330ffff3330ffff3330,0xffff5500ffff5500ffff5500ffff5500,0xffff5544ffff5544ffff5544ffff5544,0xffff88aaffff88aaffff88aaffff88aa,0xffffa2a0ffffa2a0ffffa2a0ffffa2a0,0xffffaa00ffffaa00ffffaa00ffffaa00,0xffffaa88ffffaa88ffffaa88ffffaa88,0xffffaaa0ffffaaa0ffffaaa0ffffaaa0,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffbbaaffffbbaaffffbbaaffffbbaa,0xffffccccffffccccffffccccffffcccc,0xffffce00ffffce00ffffce00ffffce00,0xffffee00ffffee00ffffee00ffffee00,0xffffeeeeffffeeeeffffeeeeffffeeee,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffff3f0fffff3f0fffff3f0fffff3f0,0xfffffafafffffafafffffafafffffafa,0xfffffcfcfffffcfcfffffcfcfffffcfc,0xffffff00ffffff00ffffff00ffffff00,0xffffffaaffffffaaffffffaaffffffaa,0xffffffccffffffccffffffccffffffcc,0xffffffeeffffffeeffffffeeffffffee,0xfffffff0fffffff0fffffff0fffffff0,0xfffffffcfffffffcfffffffcfffffffc,0xffffffff00000000ffffffff00000000,0xffffffff00000022ffffffff00000022,0xffffffff00002222ffffffff00002222,0xffffffff0000aa00ffffffff0000aa00,0xffffffff00020002ffffffff00020002,0xffffffff00220022ffffffff00220022,0xffffffff00320032ffffffff00320032,0xffffffff00330022ffffffff00330022,0xffffffff02020202ffffffff02020202,0xffffffff0a000a00ffffffff0a000a00,0xffffffff22002200ffffffff22002200,0xffffffff22222222ffffffff22222222,0xffffffffa2a0a2a0ffffffffa2a0a2a0,0xffffffffaa00aa00ffffffffaa00aa00,0xffffffffaaa0aaa0ffffffffaaa0aaa0,0xffffffffaaaa2200ffffffffaaaa2200,0xffffffffaaaaaa00ffffffffaaaaaa00,0xffffffffcc00ce00ffffffffcc00ce00,0xffffffffcc00ee00ffffffffcc00ee00,0xffffffffce00ce00ffffffffce00ce00,0xffffffffee00ee00ffffffffee00ee00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000aa000000aa00,0xffffffffffffffff0a000a000a000a00,0xffffffffffffffff2200220022002200,0xffffffffffffffffa2a0a2a0a2a0a2a0,0xffffffffffffffffaa00aa00aa00aa00,0xffffffffffffffffaaa0aaa0aaa0aaa0,0xffffffffffffffffaaaa2200aaaa2200,0xffffffffffffffffaaaaaa00aaaaaa00,0xffffffffffffffffcc00ce00cc00ce00,0xffffffffffffffffcc00ee00cc00ee00,0xffffffffffffffffce00ce00ce00ce00,0xffffffffffffffffee00ee00ee00ee00,0xffffffffffffffffffffffffaa00aa00] : Array Nat)[i]?.getD 0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def num : Nat → Nat
  | 5 => 30
  | 6 => 133
  | 7 => 336
  | 8 => 462
  | 9 => 215
  | 10 => 19
  | 11 => 1
  | _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def hash : Nat → Nat → Nat
  | 5, i => fld ((#[0xf5fd6f59ecee27cda731d7350d1092d0035cfc38c1746b8d4eb1999abfe8aa281a9252a30aa9b9927a8d575c046e60c69651575684fe504afb5468fc32f2a2afd02826026f521340708522] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 6, i => fld ((#[0x3a132392993780e3586a32db62ab0228ad42867d27b81208661f26b1bf691b9261b37d1ac11175a61729a15eda1588512b1511f770f72a0ca8e0ad500a4380957f08c5f0343502d2002579021ca00607,0x7433573f1e7384a71f6f7024b6ecfa6d0a3699ad6913363d6d58d53579de5793d57683560f254c3f538e752f1a527e8522bf4e94e4c0de4621d44bdf42c9c41e1d41953410f340d343c1c83a7053a3ae,0xae3a4add1cada36aaa64a8881a7d99a694aa66e5a664ba58de9dfa39c2ec9c24e94d3694b36947df931e991e178d95f8624785ef08375b81e1080c947f9077ec267d4f87ce0c7b4d578fc8781ef75814,0xf14e6ee87beb2dfeaa8ae9eaae3b89e35b2df620d9f9ad723dd51a8ccccccc17ccb80ec8c18c894ec6435c40f6c2d7ac1c05c0f4cbff56bf740bef95bee3dbb947ba4edba196b9181b6fcbb6b0caf3f4,0xfcbf4f8bfef76d4f5852f38db] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 7, i => fld ((#[0x17ce91764616149153b715276141b71382413661135b91357f1348d12436106700fd6f0f7c60ef110cd1f0bf870ba900ad9807d4a074ec0733d06d51065cd0589d05295051b30433904220041e700e3f,0x2b0a72a5d52a17e29b9e2969f295e92817027cb826dee26863259d9253c124069237be220952106e20ef720e58204f01fc801f9591f6651f4781e4a21d2251c03f1b7d21a89c196c019687182f418079,0x4405843db1426f142293414a140a253f03e3ed3f3be043bd503a9883a6db3a65e3a51e3930a39203384c3382ab3708a36993351f2334a4315e830a9f300b32fcdc2eb1c2cebe2c8c72c71e2be982b50a,0x5f0c15e0ff5dcaa5d2fa5d15e5c1805bc815b4dc5ac6958e4757cab566c9560bf541de510ce502ec4fb4c4f3144d4e64c5884bd5b4b77049eba494d44942f482fb47e81478d2468cc461164438b440c3,0x761d075f027551774ccb73e1c723a57212f6fbf46d9b06cbb06a1bc69eb569e0c68e3e68b5d687c567acb66d436670b65f956531364e77649456492762aa46274d625e260f4f60e4660aa36029c5f74b,0x947529453693af7933ef93367928f49265d9264e91924908888ea438e8a18e2a38db10871e586795864ca8553f853cb840058373f8318b80c947f1957ddd37cd8e7c6497b49f7af36793057903c78d0c,0xae654adc77ad855ad62fab1e5aadada9e8da9b98a6923a664ba653ca604ca5e9da51aba42eba1ef8a1983a13c1a0e569fbb39d6d89af119acde99ca99995298ebb98868959fc9553e9531994db994b6d,0xc619dc5639c4ebcc2d9ac24ccc1cdac17c2c1598c152bc1282c1174c10aebf52bbf256be2a1bcccebb0fdba770b92d0b82abb7f0cb70f4b6a31b60c3b5756b4e2bb436ab3677b2885b1096ae9abae829,0xdc3b0dc366dbd9bdba44db57ad9815d8ea2d7437d656ed5216d4a21d49e9d3b16d39a3d1bcdd0f0dd0c3ed08a5d02e7d0138cf78fcde67cdb45cd2a8c9ca2c8822c8515c7f1fc7e02c7970c7433c72b5,0xf389ef1d52f1c9ff17d8f1287f10b2ef627ef0f0ee7d4ee2ceed5d5ed27eeca7feb5ebeb5c1eacb9e9ddae92ebe8182e7e83e75ade7116e6b2be552be4b3fe4acbe34b3e32bddf7fcde190ddb24dc3ca,0xffb16ff917fe267fc4a1fafc2fa9b9f9661f8912f8803f7471f4ee3f4cedf4b50f4896f4823f3e03] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 8, i => fld ((#[0xfb620d60c0ca5c0c7df0c6750afb70af3c0adcc0ad170a36b093c608e5d08c9f08aed083d907cd1068f4062ee05fbb05e880552304b2e041e7037560351202c3b0232c01d6a01d2300e73009fe00825,0x259fc24af523855234c022fd521cd520d892075a1fc511f8651e7fa1db9e1d2821ccdb1be1c1a40219c1319bf51976017d771622115984152761464f13a33134c5129fe11fb111b1f119231152a11351,0x327c9322323218731f1e31ef930e0530dad30b8b2fd222ede92e90d2e5b62e57f2d7a22d4f52ce232c71e2b50a2b01529b9e29a8f28f3128de526d6326a612682a26778263ea2630325d9a25ae525ab2,0x4551e4526d44bca4388a437584134e40cef3fff63fc503dac73d44c3c50f3b91e39b0739360389953837e3829b371bc36bca36834360ce3605b3602535b5b350423473633f1933ce43358a334fc334d7,0x5aeb05abad59f08595db5860355f6555ef95487e54487541855383a5352953090524b251758508ba50749500814ed654ec024b8fc4b3b14a8084a220497cb4940d48d24485894835f4723146bb54685e,0x6a9a86a300699f0694266918968cb968a7e686266853e682ec6809b67e9066810662f1658b964ea564e4363d68637f162ef462d2762992627e261191608ec608625fe395fb345ec395e67e5e4955c910,0x7ddcb7da557d63c7ccbf7ca697c8c67c2d17b87c7b4d77ae7f7a7bc786b6761d0760bc75864749fc72b23722597212671131710fb71014704a0703546f6306dd866c8df6c51f6c1a06b9b66aed76ab00,0x9113690de7905b48f8558f7a08f0e28dbe38db8c8d8368d5938d2718cffc8aa3f8a83487b8e8794e87825867958653685e0785bc384798841de83cd381c8581b1a814fa806127ebb07eb6b7e4c17e31e,0x9fbb39f44a9f38f9ee759eb829e8279ccc89bfa19ac4a9ab099a39799f2c9997c996b8980dc97c7297a6796f0a966e09662b96579960d095c4995a16956629531494f3a940719265d92464920ff913d9,0xb13cab0e54b09d2b00d4aff3aaec2eae5faae5b6adff4ad76aad61facbf2ac769aba47ab7c9aa341a9db6a9b05a945ea7db3a77cda6ca1a6b4ba6a42a58b1a54efa45eda2787a1e96a1ad4a08be9fcc7,0xc2e16c2704c24ccc09cdbf357be5c6be160bdafdbd6cbbb5d9bb3dcbafbdba9edba874ba67cba63dba4cdb8ff6b8c27b8404b7550b7230b6463b5b48b5154b4f41b4c15b3bddb3855b2f17b2225b142c,0xd51bed51acd4ef7d4edcd47c2d3f6dd3f3ed3dc7d3486d3012cee1bceb8dce75cce610cd376cd2bccaaefc9669c8822c8380c7ef9c6d39c6b17c644fc62e7c5d95c4b2bc4990c482cc4294c3abfc37ec,0xeb393eade5e9b8ce992be8866e83abe7e83e7d74e75f5e56cfe496fe2775e2139e1ac2e0841e0049dfebbdfa3ddea6ede2cfdc516dc01edbc94db308db1bedafe9d9b59d9733d8ea2d7731d7362d5e5b,0xfa71ef9846f9805f9671f8b3bf88cdf817bf7f0af6fb0f6663f5ba2f58f8f4eaff4b5df3a6df2584f1bf2f18d2f1146f104bf0637f029defe2cefbe1ef4afef30aee157ede6eed858ecca7ec18ceb550,0xff40dfeacdfe280fdefbfdbf2fd9f9fd801fcd8afca07fc58ffba7cfb909fb205faa3a] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 9, i => fld ((#[0x1ace81aaa71aa6b192501618015bd0156d91527612a7712a04111230ff330fe800f4de0ebae0bcc00ba49097cc09772097310935a077870705506c5a061f50614005fe60578e04bae0370c02cac0149e,0x47ae24788044fcf44a4440f88406f03e0c23db3a3a8793a15e39ef13902a38aee3791d3764836519361933462d330293162a2eb902d0f22c6cb270e4256cd24f32241e020d891e0641e05c1dcf71af6b,0x6975b66602642f762e0a6256c5ff595ec395d08e5cc865c5cd5af4b59fe559912597dc56a4d560415545d552e25376c515d04eda44d8704d5554ccfd4c1334b44c4a6be4a37e4a256492884835f480d8,0x905869043a8fe268ddd58c06d87ed886f308685684a908468784176834f4810c67f1307e8437e47d7dc787c5247c03e7b8457ae7f7ac937abe279bee795d37959b757f3723bf71f316e5386c25b69f3c,0xc842bc763fc6fd9c482cc471dc0eeabfc53be2a1bdafdbcf49bcd0fb8ebfb3729b36fbb345ead99bac84aaafdda9d8ea9d769fb389ee759e3d69dbd69d3769af6f9ad339ac4a996ec996b89721d954cb,0xe1a7ce0be3e08afdfebbdef2dddf98dd457dcf75dc341dbec5dbe10dbb10db5d1d82d9d67e6d300cd254bd2155d1858d0b3cd02f0cede1cecffcccc0cc581cbe58cb7bbcb43ac9dcfc979fc9493c911d,0xfe8e1fe660fe03afb6b6fa547f6309f581bf368bf2bcaf27e4f1c15f04e0efdd3ee4c8eb365eade5e9dece95c7e90ebe871de5934e565be5496] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 10, i => fld ((#[0xfb090f7914ecda6eb557e60dad9520b8ceaa4142a3fe89dfbe9ac4a996b88671f79e126cde366f4c5c2a34838d17f1e] : Array Nat)[i/32]?.getD 0) 20 (i%32)
  | 11, i => fld ((#[0x38c4c] : Array Nat)[i/32]?.getD 0) 18 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packW : Nat → Nat → Nat
  | 5, i => fld ((#[0xc056a470c5e841b196ba2cc57a5b6c451662eb5e855b114598bad7a106c65ae8b385796db136ba2ce1d6af6c65ae62eb5e8b9b017fa2ce15e5b6c65ae630975af5b196ba04c5d6bd6c65ae70eb578b9ad74598bad7a006c05fe70eb578b9b015b91c2d7a106c65ae710975abdb017f9c425d6af6b5d1662eb5e809b196ba2cc5c6bd6c65ae62eb5e8ddb016b98c71d6bd6c65ae8b3871abdb017fa2ce1c6af6c05ae711c75abdb016ba2cc634bd6c65ae8b315e981b017ca2ce1d6af6c05ae8b388d2bdb0d4598bad7a156c351662eb5e841b196ba2cc5d2bd6] : Array Nat)[i/32]?.getD 0) 58 (i%32)
  | 6, i => fld ((#[0xb5d1646bd5798010f88b5d1662eb5e9f5f016bad4e2470c5ebe02d7238e3ad7aaf7c048dd6bd578dc2af80bed1670eb578a1f196badd1662eb5ebe028b3175af550107c05ae8b386b2bcb6f80b5cc5d6d65e8b9f012375af55e37083e22d7459c4c5d6bd7c0516470b5eabc20f8091bad7aaf1702df116ba2cfa62eb5ebe02d72384af55e847c65aec34598bad7af8cb5d164eeb5eabdf017ca2c8dd6bd57be02d74591c697aaf7c05ae630975b597af6ba2c8dd2bd57821f012384bad7aaf05be0247095eabca2107c65aeb7459c3ad5ef80b5d0262eb6b2f5c018da2cc5d6bd01b5ae8b2375af55e017c05feb7459c3ad5ef8091bad7aaf4d841f016b9c3adacaf173e2ed74598bad7aaf7,0xc05ae8b3175af4caf8091b8d7aaf14041f016ba2ce1d6b957be1ad74598bad7a7d7b5d1646eb5eabc0af8cb5d9a8b3175af5f014591bad7aaf08be02812375af55e107c55ae8b3175af55ef80a2c8dd6bd5783df016ba2cc5d2d65eb803017ea2ce1d6af600602d75791c317ad80a2c8e18bd54041f196ba2d0662eb5ebe1ad7459c4c5d6bd7c35ae8b3e98bad7af8091bad7aaf15841c0180b5d6e470a5eb6027f2384af55e107c5dae8b3875abca2e00c55ae8b3875abdb016ba2cc5acbd2dbe02d74598bad7a677c05ae8b3175af4daf8cb5d1646e35eabdf016591b8d7aaf083e32d74598bad7a557c051646bd5796c16f80a2cc5d6bd54055f017fa2c8dc6bd57be028b2371af55e157,0xc55ae8b2575af55ef8bb5d164eeb5eabdf196ba2c95d6bd57b803017da2ce1d6af6c051662eb5eab42af80b5d1670e36b2bdf114591bad7aaf083e028b2375af55e0d7c051646bd5796c20f80a2c8dbebd57841f196ba2cc618eb5ebe028b235eabd12107c65ae46eb5eabc5cf80a2cc5d6bd56841f017f91bad7aaf173e0246eb5eabc5c157c056a46eb5eabc20f80b5d1662eb5e9adf196b91c25d6bd57be02ff2384bad7aaf7c048e12eb5eabc2af80b5d1662d65e981f014591bad7aaf0a3e0246eb5eabc5c107c65ae8b38863ad5ef6ba2cc5d6bd54021f014091bad7aaf0abdae8b2371af55e087b5d1646eb5eabc08f80b5c8dc6bd579edf017fa2ce218eb57bdae46eb5eabc6e087,0xc05fec3459c3ad5ef80adc8dd6bd56841ed74598bad7aad043e02d75b9c48e16bd7c65ae8b3175af450f80a2c8d7aaf30041c018bb5d1670eb57b61a8b2375af55e107c051646bd5796020f6b91bad7aaf17021f196ba2cc5d6bd28be028b2374af55e157c55ae8b3875abc50f8cb5d1670eb578a1f016ba2cc5d6bd4abdae470975af55e087c05ae8b3171b597af80bfd1670eb578a1f017ea2ce1d6af28be32d74591af55e5b7c051646e35eabc16f6ba048dd6bd57821f016ba2cc5d6bd49be32d74598bad7a337c05ae62eb6b2f46ef89b5d1646eb5eabdf017fa2c8d7aaf2dbe028b235eabcb6157c051646e95eabc20f80b0d6e470c5e841f196ba2ce1d6af28be02ff459c3ad5e517,0x5ae8b235eabcb6087c65aec3459c3ad5ef80a2c8d7aaf30055f012379bad7aaf083e02d73884badacaf7] : Array Nat)[i/32]?.getD 0) 67 (i%32)
  | 7, i => fld ((#[0xc05ae8b2374af55e7d800602d94591bad7aaf7c05ae8b3875b355e518c05f68b2375af55e288c05ae8b2375af568af800003016bad48e18bd600602d74598badb8bd7c05167f3175af55e158c05ae8b3891bad7eaf8c05ae8b3191b8dbcbd8c051646eb5eabc50128c05ae8b236b2f55e5b8c05ae8b235eabcb6458c05ae8b2375b5d7aaf8c05ae8b3175b597a338c056e8b23863ad7a108c051646eb5eabca2138c05ae632375b797a378c05ae8b2375af55e428c05ae470975b517aaf800602d72381bad7aaf7c051646eb5e94450108c05ae8b3875b595e518c0516832375af55e10800602e34591bad7aaf7c051646eb5eabcaa158005ae8b2375af55e0a7c05ae8b235eabcfa5b800602d74591bb97aaf7b5d1662eb5eabc82088c05ae46eb5eabcee2e800602f54591bad7aaf7,0xc051646eb5eabc3c108c05ae8b2375af55e768c05164f2375af55e108c05ae8b235eabcee5b8c05868b23862f55e10800602d74598bad7a91700622d74598c8dd6bd700602d74591af55e5a7c056e46eb5eabc50108006028b2371af55e107c05ae8b3175b597a518c05ae8b3891af55e608c05ae8b3e91af55e608c05ae8b2375af55e788006028b2375af55e177c05ae8b2371af568af800602d75191b8d7aaf7c35ae8b3891bad7aaf8c051646eb5eabca20b8c05ae8b3691bad7aaf8c059a8b2375af55e108c05ae8b3c91bad7aaf8c05ae8b2375af55ea08b5d868b2375af55e088c05ae8b3d91bad7aaf8c05ae8b3875b595e288c05ae8b3891af55e588c0516832375af55e15800602d74598bad7a6a7c05ae46eb6a2f55e2e800602d72386bad7aaf7c05ae8b3175af55e6a8,0x3017fa2ce1d6af6c05ae712375af55e9b8c05ae8b235eabcfa60800602fd4591bad7aaf7c05ae8b235ead15e5c8c05ae712384badbcaf8c05ae8b236a2f55e5b8c051646eb5eabca20c8c058e8b2375af55e1080061ed74591bad7aaf7c05ae8b2371af55e928c05ae8b3175b597a288c05164b2375af55e128c05aec35b91c317a778000031b85a2cc5d6bd6c5dae8b2375af55e518c05ae8b2371af55e648c05ae470f75af568af8c05ae712379bad7aaf80062ad74591bad7aaf7c051646eb5eabc500b8c059a8b2375af55e158000030d6ba2cc5d6bd6c05ae8b2375af55e6e8c05aeb73891bad7aad8b5d6e8b2375af55e088c05167f23862f55e108c05ae8b3175af55e438b5d1646eb5eabca207800602d74591bad9caf7c05aeb72375af55e7b800602d74591c6d7aaf7,0xc05ae632384badbcbd8c05ae8b2375af572af800602d74598c6d7aaf7b5d16832375af55e088c05ae8b3891c2d7aaf800602f34598c8dd6bd700602d72387bad7aaf7006028b2375af55e0e7c05aeb7459c3adacaf8c05ae8b3191bad7a91800602d72375af55e2d7c05ae813191badbcbd8b5d167f3175af55e088c0586b72375af55e108006028b2375af55e197c05ae8b3191bad7a8c800602ef4591bad7aaf7c05ae712375b795e2e800602d74591af55e8a7c05ae712384af55e518c051646eb5eabc6c10800003196ba2ce1d6af6c0516712371af55e10800602d74591ba97aaf7c05aec3459c3adacaf8b5d1646eb5eabcaa088005ae8b2375af55e06700602d7459c3ad76af700612d74591bad7aaf7c056e8b2375af4a2108c051646eb5eabc38108c05ae8b3175af55e448,0x602d74591badbaaf7b5d9a8b2375af55e088c05ae8b2775b357aaf8c05ae8b3891b795e5b8c056e8b2375af55e0b800602470975af55e107c05ae8b2575af55e438c051646eb5eabc66108c05ae632375b797a2e8c05ae470975af568af8c65ae8b23863ad7aaf8c05ae8b3898bad7aa8800003196ba2cc5d6bd600602e54591bad7aaf7c05ae8b3e98bad7aa8800632d74598bad7aaf7c05aec34598badacbd8c05ae8b3e91b8d7aaf8c05ae8b2775b597aaf8c051646eb5eabc74108c056e8b235eabcb610800602d74591af55e5c7c05ae8b2775af55e458c05ae8b3175af576af8c05fe8b23863ad7aaf8c0516470c75af55e158c05868b2375af55e0b8c051646eb5eabd5a1080061ad74598c8dd6bd7c05ae712375af55e378c051646eb5eabd32108c05ae7d2375af55e378,0xc05ae712375af55e2b8c05ae46eb5ead15e2f8c05ae7f3891c257aaf8006028b2375af55e127c05ae8b3191b797a5b8c05ae46eb5eabcc82e8c05ae8b2375af55e848c05ae8b2371b597aaf8c05ae8b3175b597a558c05ae8b2371af55e45800602d74598bad7a8f7005ae8b2375af55e097c05ae47095eabcee51800602d74991bad7aaf7c05ae8b3175af5507d800602d74591badb6af7c05ae470975af55e92800602d74598badb4bd7c05ae8b2371af55e7d8c05ae470975af55e648c051646eb5eabc66158c05aecb3891b8d7aaf80060246eb5eabc5c107c051646eb5eabc90108c05ae46eb5eabcfa378c051646eb5eabcbe10800602d72375af55e9e7c05ae46eb5ead15e2e8006028b2375af55e1a7c05aeb74598badacbd8c051646eb5eabcb610800602d75e91bad7aaf7,0xc051646eb5eabc50158c051662eb5eabc82108c05ae8b2375af55e7a8c05fa8b2375af55e518c05ae813891bad7aaf800602d7459c3ad9aaf7c05ae813e91bad7aaf8c05ae8b2575af576af8c05ae8b4198badacbd8006028b235eabcb6107c048e190975af55e108c05ae8b2375af55e948c05ae8b3191ba5bcbd8b5d16470c75af55e088c04e246eb5eabc5c10800602d74591b897aaf7006028b2375af55e137c65ae8b2375af55e518c05ae8b235ead15e5b8c05ae8b2375af55e7b8c05ae8b23732f568af8c05ae8b3791bad7aaf8c05968b3175af55e108c05fe8b2375af55e518c051646eb5eabca2158c05ae8b3891c317aa8800602d75b91bad7aab7c04e2470975af55e108c05ae8b3191bad7a97800602fb4591bad7aaf7c05ae46eb5eabd242e800602df4591bad7aaf7,0xb5d1646eb5eabc6608800602d72384be57aaf700602d74591c297aaf7c05ae8b2375af55e668c05ae712375af55e2e8c05164b2375af55e108c051662eb5eabc8215800602d74391bad7aaf7005ae8b2375af55e07700602d74591c317aa47c05ae7d2375af55e2e800602d74591b997aaf7c05aecd4598badacbd8c05ae8b2371b517aaf8c05ae8b3191bad7a8f800602d74591b917aaf700616d74598bad7a037c05ae8b235eabd245b800602d72591b8d7aaf7c05ae8b235eabcc85b800602d72375af55e2f7c05ae8b238bbad7aaf8c55ae8b2375af55e288c65ae8b2375af55e288c05ae712371af55e288c048e18eb5eabc5c108c05a68b2375af55e108c051646eb5eabc5c108c05ae7d2384bad7aaf8c05164f2375af55e138c05fe8b2375af55e288c05968b3175af55e158,0xb5d1646eb5eabca2088c051646eb5eabc8c108c05fec34591bad7aaf8c05868b2375af55e158c051646eb5eabc500e800602d74598c8dd6dd700602d74591bad84af7c05ae8b237fbad7aaf8c05ae8b3898bad7aad8c05ae8b3e98bad7aad8c05aeb53891bad7aaf8c051646f475af55e108c05ae8b2375b617aaf8006028b2375af55e0c700602d74591bad5e877c05ae470975af55e7d8b5d164f2375af55e078c05ae8b3191b797a608c0516470c75af450108c05ae8b38863adacaf800602d74591af55e6270062ed74591bad7aaf700602d74591af55e71700602d72791c257aaf7c051671235eabcb610800602d75f91bad7aaf7c05ae812375af55e7d8b5d1646eb5eabc50068c05ae8b3175b357aaf8c05ae8b3875aed5e28800003016badc8e16bd6c051646f075af55e108,0xc05ae8b3175af55a7d8c051646eb5eabcaa108c051a8b2375af55e108c05ae8b2775af55e448b5d968b3175af55e088b5d1646eb5eabc5008800602d72375af55e387b5d164b2375af55e068c05ae8b31863adacbd800602d74591c4d7aaf7c05feb74591bad7aaf8c056e8b2375af55e158c05ae46eb6b2f55e2e8c05968b3f75af55e108c05ae8b3991bad7aaf8c05ae46eb5eabc8a2e800602d74598c8dd6db7c0516470c75af55e0b8c45ae8b3891bad7aaf8c05ae8b3891af55e5b8c0516470c5eabca2108c05ae8b3891b7d7aaf8c05ae8b3e91af55e5b8c056e8b2371af55e10800602f74598c8dd6bd7c051646eb5eabd2c108c65aec34591bad7aaf8c052e8b2375af55e108c05ae46eb5eabcfa2e8c05ae470975b597aaf8c05ae8b3891af55e898c05ae470975af55e458,0xc05167f3175af55e10800602d72375af55e737c05ae8b2575b597aaf8c05ae8b2575af55e45800602d75f98bad7aaf7c05ae8b3891ba57aaf8c05ae8b3e91ba57aaf800003116ba2cc5d6bd6c05aec35b9c48e18bd8c05ae46e35eabcee288c05ae8b3891b8dbcaf8c65aeb74591bad7aaf800602d75791bad7aaf7c051646eb5eabd50108c0596b72375af55e108c05ae8b23862f55e848] : Array Nat)[i/32]?.getD 0) 76 (i%32)
  | 8, i => fld ((#[0x602d74591c41d6bd57c003016ba2c8dd6c65eabe00000c05aeb72375af55af80b5d1662eb5eabcfa419c05aecd4598c8dd6de5ec803016ba2c8dd6bd5b2be00180b5d1646eb5eabd57000c05ae8b2375b397aaf8000030173a2c8dd6bd57b803016b91badbcbd578ba00180b5d568b2375af55f000c05ae8b23793ad7aaf8c05ae8b3191bad8abd57ce02d7459c48de0eb5eabe7016bb0d167d2375af55f200c05ae8b2375af97aaf8c05ae8b2375b597aaf144803016ba2c8dfaeb5eabe00000c05ae9f2375af55ee00c05aed54591bad7aaf8000031b85a2c8dd6bd57be02d74591bad7aaf228a240180b5c8dd6bd579dc5d000c05ae8b2375af55eae8c05ae8b3892c8dd6bd57c803016ba2cb246eb5eabe00180b5d165f2375af55f00000602d74591af55e607c05ae8b3491bad7aaf144803016b98c8dd6bd578ba3016ba2c8dd6cd5eabca3380b5d16632d91bad7aaf9,0x602d765a2cc5d6de5ec602d74ba2ce246eb5eabe40000c05ae471575af55ee0000602d74791bad7aaf700602d74591c21d6bd57c003016ba2cba46eb5eabe00000c05ae992375af55ee0000602d72375af55e9b7c05ae8b2375af55e7b144803016ba2c8deceb5eabe3016ba2c8dd6d45eabca3380b5d16712375af55e469c05ae8b3891c31d6de57c8000183b5d1646eb5eabdc0000c05ae8aeb69af482f80b5d16632375af55e3f9c05aeb7459f48dd6bd57c8000180b5c8e3aeb5eabdc0180b5d1646eb5eabc3b00000602d74591bad5e867c05ae8b3891bd1d6bd57c803016ba2caa46eb5eabe00180b5d1646eb5ead15f000c05ae8b2375af55e24800003016b91bcdd6bd57b803016ba2c8dd6bd57a7e00180b5d1646eb5eabc6b000c05ae8b2375b217aaf8c05ae8b3891c31d6bd144803016ba2c8dd6bd5791200180b5d16712375b3d5f000c05ae8b2375af55ea28,0x602d74591bad7aaf4d4602d7459f48dd6bd5795640180b5d1646eb5eaed5f180b5d868b2375af55e45900602d74591bad7aaf4bc003016bb451646eb5eabe00180b5d1646eb64af55f180b5d16632375af55e82900602d74591b797aaf2dc0000000c05ae8aeb5ea7180000c05fe8b2375af55ee00006028b2375af55e157c05ae8b3191bad9ebd57c8000180b5d15d6bd57a71c0180b5d1646eb5eac55f180b5d968b3f9c3ad7aaf900003016ba2c8dd6ce57b8000180b5d16471b5eabdc0180b5d1646eb5eabc4f000c05ae8b235eabcee5b8c05ae470c84bad7aaf3bc8000180b5c8e12bd57945f016ba2ce2470c5eabca3380b5d6e8b3891b8d7aaf9c05aec34591bad7aaf3ec803016ba2cc646bd5796e3016ba2c8dd6bd579f0a3200c05ae8b2375b297aaf8c05ae8b3891bad7aaf4b4803016ba2c8dfceb5eabe00180b5d16471875af55f180b5d164b2375b0d7aaf9,0xc05aeb74591badacbd57c8000180b5d1646ed5eabdc0180b5d1646eb60af55f180b5d16712375b0d5e289c05aeb74591bad7aaf22ce02d7459fce262eb5eabe40000c05aecb2075af55ef80b5d167f3e98bad7aaf900003016ba2c8ddebd57b8000180bad1646eb5eabdc0000c05ae46eb5eabc6ee00c05ae9d4591bad7aaf8c05ae8b3191c31d6de5ec8000180b5d16470b5eabdc0180b5d16632374af55f000c05ae8b3175b797a418c05ae470c75af55e77174e02d75ba2c8dd6bd579f67016ba9516632375af55f380b5d1646eb5eabcee2e900602d74591c19d6bd57c602d7459c48dd6bd57aa27016bb2d6e712375af55f20000632d74591bad7aaf700602d759a2c8dd6bd57c003016ba2c8dd6bd5aabe00180b5d368b2375af55f000c05ae8b2375af55e4d8c05aec34591badacbd57ce02d7459c48dd6bd579567016ba2c8dd6d45eabc51380b5d1a8b3891bad7aaf9,0x602d74591bad7aaf2cc003016ba2cfe46bd579d23016ba2cc646fa75af55f200c05ae8b2375af55e7f800602d74591badbcaf1a4003016ba2c8dd6de5795a3016ba2cca46eb5eabc51200c05ae8b2375b757aaf8c05ae8b3891badbcaf28c803016ba2c8dc6bd57a3a3016ba2c8e18eb5e9dc5120000602d74c98bad7aaf700602d762a2c8dd6bd57c0000180b5d1646e85eabdc0180b5d1646eb6d2f55f180b5d1646eb5eabcfa559c05aeb7459c48e18eb5ec8000180b751646eb5eabdc0180b5d16492375af55f000c0516470c75af55e10800602d74591bad80bd57c602d74592c8dd6de5eabe7016ba2c8de0eb5eabcef20000602d72375af55e31700602d74591bada2bd57c602d74591c31d6bd5a2be7016ba2ce246eb5e94451380b5d16833891bad7aaf900602d74593c8dd6bd57c602d745a0cfa46eb5eabe7016ba2c8dd6bd579e45120000602d74598bad7aa87,0x3016ba2c8dc2bd57b8000000c2dae8b3175af580000c0dae8b2375af55ee00c05ae8b238b3ad7aaf8c05ae8b3891badbcaf1448000185b5d1662eb5eabdf016badd1646e35eabcef380b5d6e712375af55e28900602cb4591bad7aaf084602d74598c8dfaeb5eabe40180b5d16712371af55f000c05ae8b2375af55e3d8c05ae974591bad7aaf3bc803016ba2cc646eb5ea5a3016ba2d0646eb5eabcfb200c05ae8b2375af574af800602d74591badb6bd57c003016ba2cc646bd5798200000c05d28b2375af55ee00c05ae8b23823ad7aaf8c05ae8b23863ad7aaf494803016ba2c8dd6bd5795e00180b5d1646eb5eabc77180b5d9a8b3891bad7aaf9c05aec34591bada8bd57ce02d74591c31d6bd579927016bb35167d2375af55f20000602d76591b8d7aaf700003016ba2c8de2bd57be02d7459fcc5d6bd579f640180b5d1646eb5eabd49180b5d16632375b797a339,0x602d745a248dd6bd57c003016ba2c8dd6bd578fa3016bb1d16712375af55f380b5d1646eb5eabca2449006028b3191bad7aaf084602d7459c48dd6cf5794640180b5d16471275af55f000c05ae8b2891bad7aaf8006028b2375af55e410840000180b5d1647075eabdf016ba2c8dd6bd5790c5120000602d74591bb17aaf700003016ba2c8dd6dd57b803016ba2cc646eb5eaa200000c05ae8b23862f550f80b5d16632375af55e359c05ae8b3191badbcbd28ce028b3891c31d6bd578427016badd1646eb6a2f55f200c05aecb2375af55e80800003016b91bad7aaf15b800016ba2c8dd6bd57821c0000c05ae7f2384af55ef80b5d167f3891c317aaf900602d7459848dd6bd57c602d74592c8dd6bd579e67016ba2ce246eb5eabc3d200c05ae8b3391bad7aaf800602d75b92c8dd6bd57c602d7459c49e46eb5eabe7016bb0d167123862f55f380b5d16470c5eabcee519,0xc05ae8b237f3ad7aaf28c8000180b5d1662eb5ea71c0180a2cc646eb5eabc2b00000602d74575af53841700602d74598bad7aaf4e4602d7459f48e18eb5eabe40180b5d1646eb5eabc81000c05ae8b2b91bad7aaf800003016ba548dd6bd57be02d7459c48dd6bd578da40180b5d1646eb5eabc73180b5d1646eb5ead15e299c05ae8b2375af4ee51144803016ba2cfe62eb6f2f600000c05ae812375af55ef80b5d6e8b3891bad7a519c05ae8b3191badbcbd1448000180b5d1646eb6dabdc0180b5d16772375af55f000c051646eb5eabca2108c05ae8b3891bad7aaf0e48000180b5d1646eb6f295c0180b5d16472275af55f180b5d16632e91bad7aaf900602d7459a48dd6bd57c0000180b5d1646eb6f2b1c0000c05ee8b2375af55ef80b5d1646eb5ead15e51900003014591bad7aaf0b3e02d74591bad7aaf3a8a27016bb351646eb5eabcfb380b5d16752375af55e289,0x602d74591bad7aaf3dc003016b98c8dd6bd578de00000c15ae8b2375af55ee0000602d72375af55e2e700602d74591bad7aaf54c003016ba2cb646eb5eabe00180b5d1646eb662f55f00000602d7459c3adacaf700602d74598c8dd6bd57c003014591bad7aaf1404200180b5d166b2375af55f180b5d1646eb5eabd2451900602d74591c05d6bd57c003016ba2c8dd6bd5790600000c05aecb2175af55ee0000602ed4598c8dd6bd7c05ae8b2375af55e6428c8000180b5d1646d25eabdc0000c05da8b2375af482e00c05da8b3191bad7aaf8c05aec3459c48dd6de57c8000180b851646eb5eabdf016ba2cee4f2375af55f380b5d86b73891bad7aaf900602d74591bad9abd57c602d74591bad7ab4578a240180b5d1646eb5eabd21000c05ae8b2375af55e72800602d74591bad7aaf424602d75ba2c8e18eb5e9de40000c05ae46e35eabc50e0000602d74598bc57aaf7,0x3016bad48dd6bd57b8000180b5c8e1ceb5eabdc0180b5d1646eb5eabc53180b5d167d2375af55e33900602d74591b8dbcbd57c602d74591bad7aaf490a27016ba2c8dd6bd579dc3d200c05ae46eb5eabd1c2e800003016ba2c8d7aaf2f3e02d74591c31d6bd579f640000c05ae8b3183af55ef80b5d868b23862f55e779c05ae8b2375af55e641448000180b5d1646f75eabdf016ba2cc646eb68af55f380b5d6e46eb5eabcee28900602d74591b8d7aaf3bc003016ba2c9e470c5eabe301459c48dd6bd5794421380b5d6e8b3891badbcaf9c05ae8b3891bad7aaf1d4803016ba2c8dd6c55eabe3016badd1671235eabcb7200c05ae8b3191b8d7aaf800003016ba2c8d7aaf31be02d7459d49646eb5eabe40180b5d1646fb75af55f180b5d16712375af55ead900602d74591c31f2bd57c602d7459c48dd6bd57a667016bae51646eb5ead15f200c05ae470975af55e8e8,0x3014591bad7aaf0c3e02d761a2c8dd6bd5a2be40180b5ce246eb5eabc5d180b5d16712375af55e489c05aec74591bad7aaf3bce02d7459c48dd6bd5797e701459c48dd6bd578a02120000602d75891bad7aaf700602d74591bad7ab357c602d74598c8dd6bd579fe40180b5d1646eb5eabcf9000c05ae8b2375af55e208c05ae8b23863adacbd57ce02d7459c48dd6bd5796e40180b5d164d2375af55f00000602d74598badacbd700003016ba2c8d7aaf44b803016ba2cc5d6d65eabe3016ba2c8e18eb5eabc8b200c05ae8b2375af55e3f800602d74591bad84bd57c003016ba2cc5d6bd5791600180b5d1646eb5eabcc3000c05ae8b2375af55e68800003014591bad7aaf05b8000180b5d1646e75eabdf016bb0d16632375b797b200c05ae712384bad7aaf8c05ae8b2791badbcbd57c8000180b5d1662eb5eab5f016ba2c8dd6bd5dabc51380b5d16712375af55e339,0x602d752a2c8dd6bd57c0000180b5d86b723862f5f016ba2c8dd6bd5a2bca520000602d723813ad7aaf7c05ae8b238b3ad7aaf28c803016ba2c8d7aaf4716e3016badd1646eb5ead15f200c05aeb75191bad7aaf800602d756a2c8dd6bd57c002d74598c8dd6bd5782200180b5d1646eb5eabca1000c05ae8b2375af55e828c05ae8b2375af55e7d19c803016ba2c8dd6bf5eabe00180a2cfe46eb5eabc21000c05ae8b2375af55e2c8c05ae8b2791bad7aaf3e4e02d75ba2c8dd6bd3b94640000c05aebf2375af55ee0000602d74591badbca7700602c34591bad7aaf084003016ba2c8dd6de57a9e00180b5d1646eb5eabcf3180b5d6e8b3191badbcbd9c05ae8b3e91bad7aaf28c8000180b5d167f115eabdc0000c45ae8b2375af55ef80b5d16632375af55e57900003016ba2c8d7aaf2db803016bae51646eb5eabe00000c05ae8b236faf55ee00c05ae8b3891bad86af8,0xc05aeb74591bad7aaf3248000180b5d1646eb6cabdc0180b5d02632375af55f000c05ae8b2375af55e4e8c05aeb74591af55e772dc8000180b5c8dd6bd579b1c0180b5d1671235eabcb7180b5ce2470c84bad7aaf9c05ae8b23863ada8bd57c8000180b5d1646eb5babdf016ba2c8dd6bd579f4a3200c05ae8b3191bad7aad800602d74591bad7aaf34c003016ba2cc646eb5ea663016ba2cc646eb61af55f200c05ae8b2375af55e25800602d74592c8dd6bd57c003016ba2c8dd6dc5eabe3016ba2cc646eb6f2f4ab380b5d166323893ad7aaf9c05aecb459c4c5d6bd57ce02d761a2c8dd6bd57a4a7016ba2c9e46eb67af55f200c05ae8b2375af55e1b8c05aecb459f4c5d6bd57ce02d7459f48dd6bd578a27016bb0d1646eb5eabcc9200c056e8b2375af55e10800003016ba2c8dd6c257be02d761adc8dd6bd579de40000c05ae8b2374af55ee00c05ae8b3291bad7aaf8,0x602d74591bad7aaf21c602d765a2cc5d6bd579f640000c05ae8b2372af55ef80b5d1646eb5eabcfa289000030179a2c8dd6bd57b803016ba2c8dd6bd5794a00000c05ae8b235eabcb0e00c05ae8b237d3ad7aaf800602d74591bad7aaf41c602d73891c31d6bd578ba7016bb4d16712375af55f200c05ae470975af55e778c05ae8b3891bad7aaf174803016ba9d1646eb5eabe3016ba2d06632375b797b200c05ae632384bad7aaf8c05ae8b2375b597aaf28ce02d7459dc8dd6bd5794640000c05ae912375af55ee0000602d74591bad78af700003016b91badaabd57b8000180b5d6262eb5eabdf016ba2c8dd6bd579448b380b5d16632375af55e409c05ae8b3898bad7aaf20c8000180b5d1646eb57a15f016ba2cfa62eb5eabc83200c05ae8b238cbad7aaf8c05aeb74591bad7aaf494803016ba2c8dd6bd57a323016ba2c8e20eb5ead15f380b0d16712375af55e109,0x3016ba2c8dd6bd579c8a3200c05ae8b2375af55e75800602d7459d48dd6bd57c003016ba2c8e36eb5eabe00000c05b68b2375af55ef80b5d1646eb5eabd08519000030d6ba2c8dd6bd57be02b7459c48dd6bd5784240180b5d1646eb5eae15f180b5d1646eb5eabcee5b900602d72384badbcbd57c003016ba2c8dd6cb5eabe00180b5d7e8b2375af55f00000602d7459fc157aaf7] : Array Nat)[i/32]?.getD 0) 85 (i%32)
  | 9, i => fld ((#[0xc05ae8b3191bad7aaf144803016ba2d0a46eb5eabe00000c051646eb5eabc20e00c05ae8b2375af55e5d800602d765aec8dd6bd57c003016ba2c8dd6bd5794e00180b5d16471175af55f000c05ae8b2375af568af800602d74591bad7aaf544003016bb2d6e46eb5eabe00180b5d928b2375af55f000c05ae8b2375af55e55800602d746a2c8dd6bd57c602d74591badbcbd579467016ba2cfe712375af55f200c05ae8b3175af55e328c05ae8b2375b1d7aaf20c803016bb2d167eeb5eabe3016ba2c8df8eb5eabca3380b5d868b3891bad7aaf9c05ae8b2375af55e7728c803016ba2cc646eb6f2f63016badd1646eb5eabd1d200c05ae8b2375b795e70800602d74591badbcbd20c602d74598c8dd6de5eabe7016ba2cc646eb5eabca3200c05ae8b23862f55e518c05ae8b2375b797aaf20c803016badd1646e35eabe00180b5d1646eb5eabd2d000c05ae974591bad7aaf8,0x602d751a2c8dd6bd57c003016bb0d16470c5eabe00180b5d6e46eb5eabc5100000602d74591b8d7aaf7c05ae8b238fbad7aaf144803016ba2c8df2eb5eabe00180a2ce246eb5eabc21000c05aecd4591bad7aaf8c05aecb4591c51d6bd57c803016ba2c8dd6bd57aaa00180b5d1646eb5eabd4f180b5d968b3f91bad7aaf9000030178a2c8dd6bd57be02d74591bad9ebd5794640180b5d1646eb5eac15f00000616d74591bad7aaf700602d765a2bad7aaf2a40000180bb51646eb5eabdc0180b5d1646eb5eabcfd000c05ae8b2378bad7aaf800602d74591bad7aaf494003016badd16470c75af600180b5d1646eb5eabcc900000602d7237abad7aaf700602d74591bad7a51144003016ba2d0646eb5eabe3016ba2c8dd6de5eabc5120000602d74c91bad7aaf700003016ba2c8d7aaf45be02d74591bad7aaf3b8a240180b5d167f3175af55f180b5d6e8b3891bad7aaf9,0x602d74591bad7aaf11c003016bb2d15d6bd57a3a00180b5d6e8b2375af4a3180b5d6e8b2375b797aaf900602d74591bad7aaf0e4602d74592c8dd6bd578a240000c05ae8b2378af55ef80b5d768b3191bad7aaf9c05aeb74591bad7aaf3bc803016ba2cfdd6bd578ca00180b5d167d2375af55f000c05aec74591bad7aaf8c05aeb74598c8dd6bd57c803016ba2c8dd6d05eabe3016ba2cfe46eb6f2f55f200c05ae8b2375af55e80800602d74591c81d6bd57c602d74591badbcbd578aa40180b5d328b2375af55f180b5d868b2375b797aaf9c05ae8b3191c51d6bd57c803016ba2c8e0eeb5eabe3016ba2cfe632375af55f200c05ae8b3f91c317aaf8c05aecb4591bad7aaf40ce02d761a2c8dd6bd579de40180b5d1662eb5eabca9000c05ae8b2382bad7aaf800602d74591bad7aaf1e4003016ba2c8dd6bd5787a00180b5d164f2375af55f180b5d868b3191bad7aaf9,0x3016b91c25d6bd57be02d7459c48e18eb5eabe40180b5d1646eb5eabc61000c05ae8b2375af55e33800602d74591bad7aaf25c003016baed1646eb6f2be3016ba2d06632375af55f200c05ae8b2375b597aaf800602d74591bad7aaf22c003016ba2c8dd6bd5788a00180b5d1646eb5eabc75000c05aeb74591af55e5b8c05ae8b2375b797aaf29c803016ba2c8dd6bd57ab600180b5d1646eb61af55f000c05ae8b2375af55e99800602d74591bad7aaf134602d74591c31d6bd57a3a40180b5d1646eb5eabc9300000602d74591b817aaf700003016ba2c8e0ebd57b803016ba2c8dd6bd579d200000c05ae8aeb5ea3882e00c05ae8b238a3adbcaf800602d74591bad7aaf3ec003016ba2bad7aaf4710600180bb51646eb5eabce1000c05aec35b91bad7aaf8c05ae8b3191bad7aaf2ac803016ba2c8dd6c45eabe00180b5d828b2375af55f000c05ae8b2375af55e368,0xc05ae8b2375af55e8e144e02d7459c48dd6bd5794640180b5d1646eb5eabd1b00000602d74591af55e5b700602d72386425d6bd57c003016ba2c8e3eeb5eabe00180b5d1646eb5eabd31180b5d16713191bad7aaf900003016bac48dd6bd57be02d7459f4c646eb5eabe7016ba2ce246eb5eabc83200c05aecb4598bad7aaf8c05ae8b2375af55e8e28ce02d74593c8dd6bd5794640180b5d1646eb6a2f55f180b5d768b3f91bad7aaf900602d74591c85d6bd57c003016ba2c8dd6c75eabe00180b5d1646f875af55f180b5d968b3891bad7aaf9c05aecd4598c8dd6bd57c8000180b5c8dd6bd578b9c0180b5d1646fc75af55f000c05ae8b23803ad7aaf800602d74591bad7aaf244003016ba2c8dd6bd5797e00000c05ae8b3175af54ce00c05ae8b3191bad7aaf800602d74598bad7aaf534003016ba2c8dd6bd5790600180b5d1646eb5eabcb7000c05ae8b2375af55e6f8,0x602d754a2c8dd6bd57c003016ba2c8e3ceb5eabe00180b5d16532375af55f000c05ae8b2591bad7aaf800602d74591bad7aaf254003016ba2c8dd6bd57a8600180b5d16632375af4e1000c05ae8b2375af55e4f8c05ae8b3891bad7aaf144803016ba2c8dd6bd381063016ba2cc646eb5eabce120000602d74591bad5e887c05ae8b3191bad7aaf3ece02d74591c31d6de5eabe40180b5d1646eb5eabc3f000c05ae470c75af55e2e800602d769a2c8dd6bd57c602d74591c31d6bd579de40180b5d1646eb5eabc5d000c05aebb4591c51d6af800003016b91bad7aaf4ebe02d74598c8e18eb5eabe40180b5d1646eb5eabc8f000c05ae8b3f91c517aaf800602d74591bad9ebd57c003016ba2cc5d6bd5790600180b5d1646eb5eabc69000c05ae8b3f75af55e8e800602d74591bad7aaf264003016ba2c8dd6bd5788600180b5d1646eb6caf55f000c05ae8b2375af55e568,0x602d74591bad86bd578a240180b5d1646eb5eabd03000c05ae8b2375af55ea38c05ae8b3191bad7aaf20c803016ba2c8dd6bd5791a00180b5d1646eb5eabd4b180b5d868b2375af55e8e900602d74591bad7aaf564003016ba2c8de8eb5eabe00180b5d1646eb5eac95f180b5d968b2375b797aaf900602d758a2c8dd6bd57c602d74598c8dd6bd578ce40180b5d16470c75af451000c05aea14591bad7aaf800003016ba2c8dd6d957b803016ba2c8dd6bd578aa00180b5d1646eb69af55f000c05ae8b3891badbcaf8c05aecb4598c8dd6bd57ce02d7459fc8dd6bd579fa40180b5d9e8b2375af55f000c05ae8b23783ad7aaf8] : Array Nat)[i/32]?.getD 0) 85 (i%32)
  | 10, i => fld ((#[0xc05aebb4591bad7aaf8c05aeb74591bad7aaf8c05ae8b238a3ad7aaf8c05ae8b3f91bad7aaf8c05aec34591bad7aaf8c05ae8b2375af55e328c05ae8b2375af55e288c05ae8b2375b797aaf8c05ae8b2375af55e518c05ae8b2375af55e778c05ae8b3191bad7aaf8c05ae8b2375af55e418c05aecb4591bad7aaf8c05ae8b2375af55e708c05ae8b23863ad7aaf8c05ae8b2375af55ea68c05ae8b3891bad7aaf8c05ae8b2375af55e8e8c05ae8b2375af55e548] : Array Nat)[i/32]?.getD 0) 76 (i%32)
  | 11, i => fld ((#[0x602d74591bad7aaf7] : Array Nat)[i/32]?.getD 0) 67 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def packO : Nat → Nat → Nat
  | 5, i => fld ((#[0xb5ce2a2aa19fabc91bad91af575abd6adbafc035991b78a2abd91abd5eabd6b5cfac02b5b2abca2c8d98af591abd6b5ce2c02b5b2abca2c8d91af591abd6adbafc035991b7891af5a2abd5eabd6c02e591afc91af55e879a294675abe6a2c32c035991b7891abd75abd5eabd6adbafb5b5991b7891af5a2abd5eabd6a2c30c035991b7891abd75abd5eabd6a2d0498badc035991b7891abd5eabd6a2c32c035991b7891af575abd5eabd6c024e9f2b7b2abca2c8d98af591abd6a2c32b5b5991b7891af575abd5eabd6b5ce275ab5b2abca2c8d91af5a2abd6a2c30c035991b7891af575abd5eabd6a2c30b5b5991b7891af575abd5eabd6c02569f2a39fabc91bad98af591abd6adbacc035991b78a2abd91abd5eabd6a2d0698badc035991b7891abd5eabd684b59a2c3091b7891abd75abd5eabd6adbacc035991b7891af5a2abd5eabd6adbacb5b5991b7891af5a2abd5eabd684b59a2c3091b7891af575abd5eabd671b59adbac91b78a2abd91abd5eabd6b33afa2cc5c035991b7891abd5eabd6b5ae591afc91af55e879a294675abe671b59adbac91b7891af5a2abd5eabd6b5cfac02a19fabc91bad98af591abd6b5ce2c02a19fabc91bad91af591abd6b33aca2cc5c035991b7891abd5eabd6] : Array Nat)[i/32]?.getD 0) 124 (i%32)
  | 6, i => fld ((#[0xc04fab33afa2cc598af591abd5c02b5b2abca2c8d98af791abd5a2aa19fabc91bad91af575abd584b59a2c3091b7875abd5eabd5a2d06b5cfa98bad98af591abd5b5aed91b0c91af55e8a1a2abe5c035991b78a2abd91abd5eabd5b5ce29fabc91bad91af591abd5adbaf91b7891af5a2abd5eabd5a2c3291b7891abd75abd5eabd5a2d06b5ce291c3191af575abd5c02b5b2abca2c8d91af591abd5b5ce275ab5b2abca2c8d91af55a2c32b5b525ea3991abf75abd5c02b5b2abca2c8d98af591abd5a2c303b94591af775abe75abd5a2badc035991b7891abd5eabd5c035991b789194575abe5eabd5b5ae591afc5e879a294675abe571b59adbac91b78a2abd5eabd5a2c3091b7891abd75abd5eabd5c04fab33aca2cc598af591abd5a2c30b5b525ea3991abf75abd5b5ce2a2c3091af575abe75abd5c035991b7891af5a2abd5eabd5a2d0498bad91b7891abd5eabd5c2dadc2cc691abdc029991abc5c0252490a19c2bf91af5a2abe5b5b5991b7891af5a2abd5eabd5b5ce2a2aa39fabc91bad91af55a2c3291b7891af575abd5eabd5c033591b3c91abd5e94575abe5,0x98b73b2b78a2c8d91abd5eabd5b5ce2adbac91af5a2abea2abd591afc91af55e879a294675abe5c02a19fabc91bad98af791abd5c04e691afd5e879a294675abe5a2cc5c035991b7891abd5eabd5b5ce691afd5e879a294675abe5a2d04b5ce291c3191af575abd5c02ed91b0c5e8a1a2abe91abd5b5cde912f59187ba294675abe5b33aca2cc591b7891abd5eabd5b5b3591b3c91af55e94575abe5a2a917cabc759dd91af775abd5b5ce29fabc91bad91af575abd598badc035991b7891abd5eabd5c02a19fabc91bad91af591abd5c02a19fabc91bad98af591abd5b5ce2a2bd291af57590591abe575aada8abca29dd91af7a2abd5b5ce2a2c3091bad91af575abd5c033591b3c91af55e94575abe5c02ed91b0c91af55e8a1a2abe5adbaf91b78a2abd91abd5eabd598b6b9fb7891bad91abd5eabd5b335ba2cc591b7891abd5eabd5adbacc035991b78a2abd5eabd5b5ce2a2c8dadbac91af5a2abd598bafc035991b7891abd5eabd5adbafb5b52a2abd5ea3991abf5b5cfa9fabc91bad98af591abd5adbacb5b5991b78a2abd5eabd5b5cfaadbac91b79a2abd5eabd5,0xc02ed91b0c918a15e8a1a2abe5c033591b3c919455e94575abe5c035991b78918a1a2abe5eabd5b5aed91b0c91af55e8a1a2abe5b5cfab2abca2c8d98af591abd5adbac91b7891af5a2abd5eabd5b5ce2c02b5b2abca2c8d91af55b5c5e7eaf59894791abd75abe5b5ce2b1bafa2c3191af575abd5b5ce2a33ac91af5a290591abe5c035991b7891abd75abd5eabd5b5ce275ab7b2abca2c8d91af55a2c32c035991b7875abd5eabd5b5ce2b2abca2c8d91af591abd5a2c32b5b5991b7875abd5eabd5b5cfaa2c3291b7975abd5eabd5b5ce2a2aa19fabc91bad91af55a0b5b98bad91b7891abd5eabd5a2c30c035991b7875abd5eabd5a2c30b5b5991b7875abd5eabd5b5cfaa2c3091b7975abd5eabd5b33afa2cc591b7891abd5eabd5b5cf696af5988a3a2abe91abd5b5ce286427a2c3091af575abd5c035991b7891af575abd5eabd5c04fa9fabc91bad98af591abd5a2d04b5cfa98bad98af591abd5c04faadbac91b79a2abd5eabd5c0282491459c2bf91af575abe5adbac3b8a191af7a2abea2abd5b5b5991b7891af575abd5eabd5a2d06c04fa98bad98af591abd5,0xa2badb5b5991b7891af55eabd5b5ce2b2abca2c8d91af5a2abd5c04fab2abca2c8d98af591abd575ab5b2abca2c8d91af5a2abd5c035991b78a2abe91abd5eabd5b5ce2b33afa2cc591af591abd5c033591b3c91af55e94575abe5b5ce2c02a19fabc91bad91af55b5ce2a33af91af5a290591abe5c04faa2c3291b7975abd5eabd5c035991b7891abd75abe5eabd5b5cfab33aca2cc598af591abd5c02ed91b0c91af55e8a1a2abe5c035991b7891af5a2abe5eabd59f2a39fabc91bad98af591abd5c04faa2c3091b7975abd5eabd5adbac91b78a2abd91abd5eabd5b5b5991b7891af5a2abe5eabd5b5b3591b3c91af55e94575abe5adbafc035991b78a2abd5eabd5adbacb5b52a2abd5ea3991abf5a2d04c04fa98bad98af591abd59f2b7b2abca2c8d98af591abd5a2cc6c035991b7891abd5eabd5a2d0698bad91b7891abd5eabd5c02e591afc5e879a294675abe5adbafb5b5991b78a2abd5eabd5b5cfaadbaf91b79a2abd5eabd5b5ce2b33aca2cc591af591abd5b5ce2a2bad91af5a2abd75abd5c035991b7891af575abe5eabd5b5b5991b7891af575abe5eabd5,0xc04faadbaf91b79a2abd5eabd5a2badc035991b7891af55eabd5b5cfab33afa2cc598af591abd5b5ce2a2bd091af57590591abe5a2c3091b7891af575abd5eabd5] : Array Nat)[i/32]?.getD 0) 104 (i%32)
  | 7, i => fld ((#[0xb33aca2cc598af791abd4b586d9c0a291af5a2abe491b3c91af55e94575abe4b5aed91b0c5e8a1a2abe4579c991b3f5e94575abe4a2aa19fabc91bad75abd4b2b78a2c8d91abd5eabd4b5cfa91bad98af591abd491af55e879a294675abe4adbaca2abd91abd5eabd4b5cea91b0d5e8a1a2abe4adbaf91b78a2abd5eabd4adbaf91b7aa2abd5eabd492b78918a1a2abe5eabd4a2cc691b7891abd5eabd4b5ce291af5a2abd75abd4b5cee91b3d5e94575abe4a2d0698bad91abd5eabd491afe5e879a294675abe4a2c305ea3991abf75abd4a2c1075a85579df91af74b5ce291af5a2abe75abe491b7891af575abe5eabd4b5ce291c3191af575abd4b58f59c43291af575abd4b5cfa98baf98af591abd4c05a2adce191af5a2abd4adbaf98af7a2abd91abd475891adce291af5a2abd4c04fa98af591abe91abd486427a2c3091af775abd4b5aada8abca29dd91af74,0xb5ce291af5a294675abe491aff5e879a294675abe4b5ce291af59194575abe4b1bafa2c3191af775abd4b5ce2a2bad91af575abd498aa39fabc91bad91abd4c02b5b2abca2c8d91abd4ab3afa2a85579df91af74b5ce291af5a2abea2abd4b5ce2adbac91af5a2abd491b7891abd75abe5eabd4b33afa2cc591af591abd4b33afa2cc598af591abd4922f791879a294675abe4b5d129c43191af575abd4adbac579dd91af7a2abd4adbaca29dd91af7a2abd4c02a19fabc91bad91af54b5b525ea3991abf75abe49c07b91af5a294675abe4b5ce2a2cc591af591abd49f0a391b79a2abe5eabd4491459c2bf91af575abe4c04faa2bad91b795eabd496af5988a3a2abe91abd491b7891af5a2abe5eabd4a33af91af5a290591abe4b5cfa98bad98af591abd498b5b91b7891abd5eabd4a2c325ea3991abf75abd4a29379c43391af575abd498b5b91b7891abd5eabd4,0xb5b5991b7891af55eabd4a2aa39fabc91bad91af54b33afa2cc598af791abd4b5b3591b3c5e94575abe4ae3afa2ad1579dd91af74a2c3091af575abd5eabd4adbafa2abd5ea3991abf4b5c5a7e2f59194775abe4b5ce2a2c3191af575abd4c02ada8abca29dd91af74adbac9c2bf91af5a2abd491b78a2abe91abd5eabd4b5cea92af5918a1a2abe4a2bad91af7a2abd75abd4c2dad91abdc029991abc4c033591b3c5e94575abe4adbac91b7ba2abd5eabd4a2c4075ad1579dd91af74a2bd091af57590591abe4c02ed91b0c5e8a1a2abe4b5b52a2abe5ea3991abf4b5cfaa2cc598af591abd4c02a19fabc91bad91abd43214591b7b75abe5eabd4b2abca2c8d91af5a2abd4c04fa91b79a2abd5eabd4b5ce291bad91af575abd491b0e5e8a1a2abe91abd4c04ee91b3d5e94575abe49c33c91af55e94575abe43b8a191af7a2abea2abd475b3591b3c5e94575abe4,0xa2c3091abd75abd5eabd491afc5e879a294675abe475b5991b7891abd5eabd4c04fa98bad98af591abd475ab5b2abca2c8d91af54b5aa19fabc91bad91abd4a2c40861dd91af775abd4b5cd28faf5918a3a2abe491b7891af5a2abd5eabd498aa39fabc91bad91abd4a2c1275a85579df91af74a2d0498bad91abd5eabd4c04fa91bad98af591abd4b5ce2a2bad91af5a2abd4b5da2adce191af5a2abd47d2bf759f598af791abd4b5a917cabc759dd91af74a2c3291af575abd5eabd475aafa8abca29dd91af74a2c3091af575abe75abd4a2cfeb5ce291bad91af54c035991b7891af55eabd4b5ce2adbac91af5a2abd4b43acadce191af5a2abd4a2bad91b7891af55eabd4c04fa98baf98af591abd4c04ea91b0d5e8a1a2abe491b0c91af55e8a1a2abe4c02917cabc759dd91af74b5ce291af5a2abd75abe4b5ce291af5a290691abe491b3e91abd5e94575abe4,0x5eaada8abca29dd91af74c04faa2cc598af591abd491b3c919455e94575abe4adbaf91af5a2abd5eabd4b5b52a2abd5ea3991abf4b5ce2a2c3091af575abd491b0e918a15e8a1a2abe4b5ce2a2cc691af591abd4a2c3291abd75abd5eabd4a2c30579dd91af775abd4c035991b7875abd5eabd49fabc91bad91af591abd4c035991b7891abd5eabd4b58f9adce391af5a2abd49fabc91bad98af591abd4c035991b7891abd5eabd4a2bad91b7891abd5eabd4adbac91b79a2abd5eabd491b789194575abe5eabd4b5ce291af59194675abe4b5ce2adbaf91af5a2abd4ae3afad9dd91af7a2abd491b7a9194575abe5eabd491b0c5e8a1a2abe91abd4b5b5991b7875abd5eabd4b5cfa91b7975abd5eabd4a2badb5b525ea3991abf4b5ce2b2abca2c8d91af54c02a19fabc91bad91abd4a2d0691c3191af575abd4b5ce2b2abfa2c8d91af54a2d0698bad98af591abd4,0xa2bd291af57590591abe4a2c4275ad1579dd91af74a2c3091bad91af575abd4b5cea91b0d5e8a1a2abe4adbafa2abd91abd5eabd4a2c3291b7b75abd5eabd43914591b3f5e94575abe4adbac91b78a2abd5eabd498baf91b7891abd5eabd4adbac91b7aa2abd5eabd498ab7b2abca2c8d91abd4c05129c43191af575abd4a2c3091af775abe75abd4a29359c43391af575abd49fabc91bad98af791abd45ea917cabc759dd91af74a2c309c2bf91af575abd49fb7891bad91abd5eabd4adbac98af7a2abd91abd4a2c3091b7b75abd5eabd4b5cfaa2cc698af591abd4a2c8dadbac91af5a2abd4b5ce2a2c3291af575abd4b5ce2adc8f91af5a2abd4a2d0698bad98af791abd4b5ce2b2bafa2c8d91af54a2a937cabc759dd91af74a2c32579dd91af775abd4b5daab0ce1a2bad91af5491b78a2abd91abd5eabd4b5ce2adbaf91af5a2abd4a2b3591b3c5e94575abe4,0xb5cfa91b79a2abe5eabd4b5ce291af591abe91abd43b87991af7a294675abe4b5b3591b3c5e94575abe4a2d0491c3191af575abd491b3c91af55e94575abe4a2d0498bad98af591abd491b0c918a15e8a1a2abe498bad91b7891abd5eabd4b5ce2adbaf91af5a2abd4b5ce2a2c3091af575abd4490a19c2bf91af5a2abe4b33aca2cc591abd5eabd4c04fa91b7975abd5eabd4b5ce2a2c3291af575abd4ab3aca2a85579df91af74b5cee91b3d5e94575abe4c035991b7875abe5eabd4adbaf579dd91af7a2abd43a8a191b0f5e8a1a2abe4ae3aca2ad1579dd91af74912f59187ba294675abe4b5ce2a2c8d91af591abd4b5b5991b7875abe5eabd4b5cfa91b7975abe5eabd49fabc91bad91af575abd4a8abca29dd91af7a2abd4b5ce2a2c3091af575abd4a92bfa29f598af791abd4b5aed91b0c5e8a1a2abe4a2c329c2bf91af575abd4b58e59c14691af575abe4,0xc04faa2cc698af591abd4a2c30759dd91af775abd475aada8abca29dd91af74320a191b7ba2abe5eabd486427a2c3091af575abd4b5ce291af5918a1a2abe4b5cfa98af591abe91abd4a2d109c43191af575abd4c04ee91b3d5e94575abe47cabc759dd91af775abd4a2c3291b7975abd5eabd4ae3acad9dd91af7a2abd4a2cc591b7891abd5eabd4adbaca2abd5ea3991abf498ab7b2abca2c8d91abd475893adce291af5a2abd4c2cc691abdc029991abc4adbaf9c2bf91af5a2abd4adbac918a1a2abea2abd4adbaf91b7ba2abd5eabd4a2c42861dd91af775abd47eaf59894791abd75abe4c02ed91b0c5e8a1a2abe4c035991b78a2abe5eabd4adbac91af5a2abea2abd4b5ce2a2c3291af575abd4a2cfdb5ce291bad91af54b5ce2a2c3291af575abd4a2c3091b7975abd5eabd4b5cee93af59194575abe4b5b5991b78a2abe5eabd4b5cfaa2c8d98af591abd4,0xc04fa91b7975abe5eabd4b5ce291c3291af575abd4a2badb5b5991b785eabd4b5cfaa2bad91b795eabd4b5cd28faf5918a3a2abe45eab5b2abca2c8d91abd49c30c91af55e8a1a2abe49f14791b7975abe5eabd4b2abca2c8d91af591abd4b2abca2c8d98af591abd4a2aa19fabc91bad91af54b5ce291af57590591abe493b789194575abe5eabd4b5c5a7e2f59194775abe46f29f9c2bc91af55eabd4a2c3098af791abd75abd4c04ee93af59194575abe4b33afa2cc591abd5eabd4b5ce291af5a2abe75abd491b7891af575abd5eabd4b43afadce191af5a2abd4c033591b3c5e94575abe475aef91b0c5e8a1a2abe4a2c309194575abe75abd4b5ce2adbaf91af5a2abd4a2aed91b0c5e8a1a2abe4a2d0498bad98af791abd4c04ea91b0d5e8a1a2abe491b3c91abd5e94575abe491b0c91af55e8a1a2abe475ab5b2abca2c8da2abd4b5ce291af5758a1a2abe4,0xb2abca2c8d98af791abd4b5ce298baf91af591abd4b5ce291af5a290591abe491b3e919455e94575abe4c04faa2c8d98af591abd4c04fa91b79a2abe5eabd4a2d129c43191af575abd4c04ea92af5918a1a2abe491b7891abd75abd5eabd475aed91b0c5e8a1a2abe4b5b5991b78a2abd5eabd4b5cfa91b79a2abd5eabd4a2c3291b7875abd5eabd4b5ce2a2c8d91bad91af5491afd5e879a294675abe4a2c3291b7a75abd5eabd45eaa19fabc91bad91abd4b5b525ea3991abf75abd4c02b5b2abca2c8d91af54b1bafa2c3191af575abd4b5ce291af575abe75abd4a33ac91af5a290591abe4adbaf91b79a2abd5eabd4b5ce2adbac91af5a2abd4b5ab5b2abca2c8d91abd4b5ce29fabf91bad91af54a2badc035991b785eabd4b5ce291af5a294575abe4a2c3298af791abd75abd4a2c3091b7875abd5eabd475ab7b2abca2c8d91af54a2c3091b7a75abd5eabd4,0xb5ce291bad91af591abd4a2b3791b3c5e94575abe491b78918a1a2abe5eabd491b7a918a1a2abe5eabd4a2b5991b7891abd5eabd4b33aca2cc591af591abd4b33aca2cc598af591abd4c02b5b2abca2c8d91abd4a2bad91af5a2abd75abd4adbac91af7a2abea2abd4adbac91af5a2abd5eabd4c035991b78a2abd5eabd4a2a917cabc759dd91af74b5ce29fabc91bad91af54b5ce2a2c8d91af5a2abd43b94591af775abe75abd4] : Array Nat)[i/32]?.getD 0) 84 (i%32)
  | 8, i => fld ((#[0x861dd91af775abd35e8e99194675abe3b2abca2c8da2abd398af791abe91abd3a2cc591abd5eabd357a05b2af7a2c8d3a8abca29dd91af735e93d9194475abe3b5929759c25eabe3a2c3275abd5eabd3a2a499c2bf91af53758d1a2ce291af535e8cda2cc691abd391af5758a1a2abe3a2bad91b795eabd35e871a290691abe391b78a2abe5eabd39894791abd75abe3a29bd919c05eabe3b0ce1a2bad91af53c2dadc029991abc391b7aa2abe5eabd3a2c3291af775abd3b3abca2ce191af5391af5918a1a2abe391a958a2bc75af5390abdaec8ca2af53b33afa2cc591abd38faf5918a3a2abe3a2c3291abd75abd391b3c5e94575abe3988a3a2abe91abd3,0xa2c8d91abd5eabd391af5a294575abe3a292f91c5375af53a292d91c5375af5375a9d9c2bc91af53aecc4a2af591abd3a287db0c8ea2bad3a2aa39fabc91bad33b8a191af7a2abe37599191b7b5eabd35ea3991abf75abe391c3291af575abd391af575abd5eabd3c01bd919c05eabe391abe919c35eabe398c5275af591abd391b79a2abd5eabd3a2c7875b795eabd3a291691b7a5eabd35eaa39fabc91bad391af57590591abe3919d1862f775abd35799191b7b5eabd3adce291af5a2abd3a2bd07590591abe34714591abf75abe3a2cfa91b795eabd35e91991c3275abd391af5a2abe75abd391b3e5e94575abe391af55e94575abe35795b9c3af91af53,0xb3abfa2ce191af5398baf98af591abd391b0c5e8a1a2abe3a2bad91b7a5eabd3a8abfa29dd91af73adce191af5a2abd3ad9df91af7a2abd3b32f7a2cc591abd3adbafa2abd5eabd398a9b91abd91abc3b5b5991b785eabd3b5cfa91b795eabd391abd5e94575abe398a9b91abd91abc3578d1a2ce291af53a2c8d91bad91af535e93d9194475abe375b5991b785eabd39c0a091af5a2abe3adbaf91af7a2abd3a2c3091af775abd3a2c3075abe75abd391af575abe75abd3adbac91af5a2abd3a2bad98af791abd3adbafa2abd91abd393af79194575abe35e921adc8fa2abd39fabf91bad91af539c14791af575abe388abd91c5075af53918a15e8a1a2abe3,0x91b78a2abd5eabd37588dadc8ea2abd35e88dadc8ea2abd391af55e8a1a2abe391b7aa2abd5eabd391bad91af591abd3adc8ca2c8da2abd391bad98af591abd375899918a0a2abe3b59bd919c05eabe3a2d0691c3175abd3a299191b7b5eabd391abd75abd5eabd375ab5b2abca2c8d3b33aca2cc591abd398c8f91abd5eabd3a2c3291af775abd398af7a2abd91abd3a29f598af791abd3a2c3291af775abd39c43091af575abd39fabc91bad91af53a2c8d91af5a2abd3c035991b785eabd3a2a9d9c2bc91af53579f99faf791bad3a29599c3af91af539c43391af575abd3a2bad91b785eabd398baf91af591abd3a2abe5ea3991abf391af5a290591abe3,0xa8bafa29dd91af7391bad862f775abd3759f598af791abd3a0af791c3175abd3a2ce291af55eabd39c3af91af55eabd39c0a391af5a2abe35eab5b2abca2c8d391af575abe5eabd3adbaca2abd91abf391af7a2abe75abd3a295191baf91abd3a2be5759dd91af73b03aca2b795eabd39fb7891bad5eabd398baf98af791abd391af5a2abd75abd3b5899918a0a2abe391879a294675abe3b5ce291af575abd35e87db0c8ea2bad3918a1a2abe5eabd391af7758a1a2abe3a2c7a75b795eabd35e95598baf91abd3579dd91af775abd391af5a2abe75abe391c3191af575abd3918e99194675abe398bad98af591abd392af7918a1a2abe39fabc91bad91abd3,0x7589b918a0a2abe391abdc029991abc3c0099918a0a2abe37e2f59194775abe391af5a2abe5eabd391abdc029991abc3adbac91af7a2abd391af5a2abea2abd3b5ce2a2c8d91af539894791abd75abe3adbac91af5a2abd39c43291af575abd391af7a294575abe39fabf91bad91abd398bad98af791abd391a03adaf7a2abd35eaa19fabc91bad3b33afa2cc591abd3b593d9194475abe375a85579df91af739c2bf91af575abd39f3af91b795eabd37591691b7a5eabd3a2cc591af591abd3a2bad5ea3991abf391b7b75abd5eabd3a2cc598af591abd3a2c8dadbaca2abd37587db0c8ea2bad391bad98af791abd37cabc759dd91af73a2cc691abd5eabd3,0x9c43191af575abd3adce391af5a2abd3a2c3191af575abd391b3e5e94575abe3b5ce291af591abd391af55e94575abe398c5075af591abd39194d75b7a5eabd3b5ce291af591abe39fc3091bad75abd391b0e5e8a1a2abe375889aec8ea2af535eab5b2abca2c8d39fabc91bad91abd39fabc91bad75abd3a2cfa98af591abd391abd75abe5eabd3b5ce291af575abd3a2abd5ea3991abf3a2c8dadaf7a2abd3a2bd27590591abe3c04fa91b795eabd3a2c3091bad75abd391bad91af575abd391ab1aeabca2af5392af7918a1a2abe391af5a294675abe3adce091af5a2abd3918a1a2abea2abd391af59194575abe3a2bad91af575abd391af775abe75abd3,0x9c14791af575abe398a9b91abd91abc3b5cfa98af591abd34710591abf91abe398a9b91abd91abc391b7975abd5eabd3aecc7a2af591abd391a01adaf7a2abd3a293d9194475abe3a2cfe91bad91af539c14691af575abe3a2ad2579dd91af7391af7a2abe75abe391bad91abd5eabd3a2d0491c3175abd391af5a2abd75abe3a2abe91abd5eabd35eaa19fabc91bad391b3d5e94575abe3b5ce291af575abe391af5a290691abe38a2bc75af55eabd39187ba294675abe3aecc4a2af591abd38faf5918a3a2abe3aeabca2af55eabd3b5ab5b2abca2c8d3579dd91af775abe3b5d0a91c5175af5391b0f5e8a1a2abe3a2cc598af791abd391b0d5e8a1a2abe3,0x3b8a191af7a2abe3a2d0698bad91abd3c013d9194475abe386427a2c3075abd3578d3a2ce291af53988a3a2abe91abd35e93191c3375abd391b7891af55eabd369abd919c35eabe3b5ce291af5a2abe3902f5adc8ca2abd39c2bf91af575abe375a499c2bf91af536b2be91b785eabd3aec8ca2c8da2af5391abdb59c15eabe391b7b75abe5eabd3759bf919c05eabe391abeb59c15eabe391abdb59c15eabe3a2bad91af55eabd3b58f1919c25eabe393af59194575abe3a2bad91af5a2abd391b3c5e94575abe3579dd91af7a2abe3470a1a2abe91abf391b3f5e94575abe33b94591af775abe391af7a2abd75abd3adbaca2abea2abd3758c9a2c8e91abd3,0xa2aa19fabc91bad3a293391c3375abd3a2ad2579dd91af73a2cc698af591abd3adbaca2abd5eabd39c2bf91af5a2abe391af7a294675abe3a2c3291abf75abd3b03afa2b795eabd398af791abd75abd391abd75a9991abc3a2bad91af775abd391b7ba2abe5eabd3759bd919c05eabe35e95598baf91abd391af7a2abea2abd3adbac91af7a2abd39194575abe75abd3b5ce291af575abe391af5a2abd5eabd391af59194675abe35e8cda2cc691abd3adbaf91af5a2abd3adbaca2abd91abd375b5b91b785eabd392af5918a1a2abe375a05b2af7a2c8d3b2abca2c8d91af53759dd91af775abd3b2abfa2c8d91af53a2ad1579dd91af73a2c3091abf75abd3,0xb5d9ea2ce191af53a2bad579dd91af73a2c3291af575abd3adc8f91af5a2abd3a2c3191af775abd3b2bafa2c8d91af53b5ce291af5a2abe3b2d6ca2c8da2abd3579599c3af91af53a0af798bad91abd393af79194575abe3b0ce2a2bad91af5391b7875abd5eabd3adbaf91af5a2abd3918a9a2b7a5eabd391b7891abd5eabd375ab7b2abca2c8d391b7891abd5eabd391b7a75abd5eabd398c5275af591abd35e899918a0a2abe391b7a91abd5eabd3b3bafa2ce191af535ea5a9fabf91bad3b5b525ea3991abf37588baec8ea2af53a2bad91abd5eabd3a2c3091af575abd39194575abe5eabd3b2abca2c8d91abd391b0c5e8a1a2abe3a2cc691af591abd3,0xa29f598af791abd3a2bada2abd75abd375ad2579dd91af73a293f9194475abe37e2f59194775abe3adbafa2abd91abf3579dd91af7a2abd3a29dd91af7a2abd3a2a85579df91af73c04fa98af591abd39c14491af575abe3b32f7a2cc591abd3a2cc698af791abd35e879a294675abe3b5ce291bad91af53a2be6759dd91af7393af79194575abe391af7a2abd75abe3a2b5991b785eabd39c2bc91af55eabd3b5ce2a2bad91af539c2bc91af55eabd392af7918a1a2abe3a2abd91abd5eabd391b7975abe5eabd391c5091bad75af53c02b5b2abca2c8d39f3af98af591abd3b1bafa2c3175abd3ad9dd91af7a2abd3a33aca290591abe391af55e8a1a2abe3,0x91b7ba2abd5eabd39c37891af55eabd3a2d0498bad91abd33b94691af775abe3adbaf91af7a2abd3a2b5b91b785eabd3adbaf91af5a2abd3a2c3091af575abd35ea3991abf75abd35e93f9194475abe398af791abd75abe3b2abca2c8d91abd35ea66b2abfa2c8d3b2abfa2c8d91abd35e8a1a2abe91abd33b8a291af7a2abe391871a290691abe3b2b78a2c8d5eabd398baf91abd5eabd398c5075af591abd3a2c8d91af591abd3a2bad9c2bf91af53919455e94575abe39c0a291af5a2abe3a2c8d98af591abd391b79a2abe5eabd3a2bad91b7b5eabd3b5ce291af5a2abd35e899918a0a2abe3a2bad91af7a2abd3b33aca2cc591abd39c0a391af5a2abe3,0x91b0e5e8a1a2abe3a2c8d98af791abd37588fadc8ea2abd398af7a2abe91abd3b5aa19fabc91bad375ad2579dd91af73a33afa290591abe3759f598af791abd3b4af7a2cfd91bad3a2c3291af575abd3a2cfd91bad91af53a2c3091af775abd3a2c3291af575abd3a29f99faf791bad398bad91abd5eabd3a2c3091abd75abd391b7875abe5eabd391b3d5e94575abe3a293191c3375abd35e89b918a0a2abe3a29bf919c05eabe391abda2a9991abc391b7a75abe5eabd3aecc7a2af591abd391af591abe91abd35eab7b2abca2c8d398af591abe91abd382af591c3075abd39c2bf91af5a2abd37cabf759dd91af7375ad1579dd91af73b5ce2a2bad91af53,0x91b3f5e94575abe391b0f5e8a1a2abe391b0d5e8a1a2abe375b5991b785eabd3b5885a29c25eabe33b94591af775abe3c02a19fabc91bad3b5ce291af5a2abd3861df91af775abd3adbaf91af7a2abd3a2c3075abd5eabd3919d3862f775abd3a2b5991b785eabd391c3091bad75abd3] : Array Nat)[i/32]?.getD 0) 64 (i%32)
  | 9, i => fld ((#[0xa2abe91abd291c5175af52b5ce291af52aebafa2af52a2c8da2af5275b7a5eabd291c5075af52579dd91af729fabc91bad2a2c8da2abd2a2c5175af5298baf91abd2a290591abe275abe5eabd291bad91af52a2c8e91abd25e90591abe2a2c8d91bad29194775abe2a2bad91af5291af775abe291abd5eabd2a2abd91abf25eabe5eabd291abe5eabd291abd5eabd291abd75abe275abe75abd291abe5eabd2adbaca2abd29fabf91bad2a294575abe2,0xa29dd91af72a2bad75abd2a2abea2abd2adbaca2abd2918a3a2abe2759dd91af72b5ce291af52a2cc591abd2a2c8d75af52578cba2c8e29c2bc91af52a2c8d91bad2b5a9991abc25e94575abe2578c9a2c8e2c029991abc2a2c8d91baf2b59c15eabe29faf791bad2758c9a2c8e29c2bf91af52a2abd75abd291b7b5eabd2a295391baf2a2abe75abe291c3175abd2a2abe5eabd2a295191baf275a9b91abc291af7a2abe291bad91abd291af5a2abd2,0xadc8ea2abd2a2c8d91abf2a2abd75abe2a2abd5eabd2a290691abe2918a1a2abe2758c9a2c8e2a2af591abd291af7a2abd2a2c8e91bad291b795eabd2a2c3175abd2a2abd91abd25e95191baf291bad5eabd2adaf7a2abd2adc8ca2abd2a2b7a5eabd2a295191baf2a2bad5eabd275af591abd275a9991abc291bad91abd291bad75abd2b2af7a2c8d2a2bad91af7291baf91abd291c3075abd2919c25eabe2a294675abe29194575abe2a2bad91abd2,0xa2c3075abd291af575abd2a2c5275af52a2cc691abd291c5375af52a2af55eabd298bad91abd291b785eabd291b7a5eabd2aec8ea2af529194675abe2adbafa2abd275b7a5eabd2b2abca2c8d25e8a1a2abe2b2abfa2c8d2918a0a2abe291abf75abd2aec8fa2af52758cba2c8e275a9991abc2862f775abd291abf91abe275af55eabd298af791abd291abf91abe2b59c15eabe2a2bada2abd298baf91abd25e8c9a2c8e2a2b795eabd2a2cfe91bad2,0xa2abe91abf291af575abe28a2bf75af52adbafa2abd2a2c3075abd2918a3a2abe2aeabfa2af5291af591abd2a2a9991abc298af591abd291af591abe2a2c8d91abd291abf75abe29194575abe25ea3991abf291bada2af52aec8ca2af525e90591abe2759c15eabe2a2c8d91af52a2cc591abd2a2c3275abd29194775abe275a3991abf2adc8fa2abd2b2bafa2c8d291abd91abc29190591abe291abd91abc257a9b91abc2adbafa2abd2919c05eabe2,0xa2a3991abf275b795eabd2919c15eabe2918a1a2abe2759c25eabe2579df91af7291abd5eabe29194475abe291af5a2abe291abe5eabe291abd5eabe25ea9b91abc298af791abd275abd5eabd2b0c8ea2bad2a2c3275abd2a2cfd91bad291af775abd2a2c3275abd2a2af575af52a2a9b91abc291abd75abd291c5275af5291bad75af525e94575abe291abe91abd2a2ce291af5291bad91abf291c3375abd2a29c25eabe25ea9991abc29c3af91af52,0x5e8a1a2abe2b2af7a2c8d25795391baf291abe91abd291c3275abd28a2bc75af52a2bad91abf2aeabca2af527590591abe25795191baf2a2c8d5eabd2a2a9991abc2a2cc691abd2a2abe75abd2a29c15eabe25ea9991abc2a2b7a5eabd2919c35eabe291af55eabd2a2c8d91abd29faf791bad2a2ce191af52758a1a2abe2] : Array Nat)[i/32]?.getD 0) 44 (i%32)
  | 10, i => fld ((#[0xa2af51a2abd175af5191bad1a2bad1a2c8e1a2abe15eabd175abe191af7191abd191abe1a2c8d15eabe175abd191abc191af5191abf191baf1] : Array Nat)[i/32]?.getD 0) 24 (i%32)
  | 11, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def flags0 : Nat → Nat → Nat
  | 5, i => fld ((#[0] : Array Nat)[i/32]?.getD 0) 1 (i%32)
  | 6, i => fld ((#[0x10000000004800000000000000000000000000040000000000000000000000000000000000000000000000000000000020000000000000000000000000004c000000000000000001000000000800000000000000000000000000000000000000000000000000000000000000000100000000002c0400000c00000000000000000100000000000000000000000000000,0x10000000000000000000400000000000000000000000000000000000000000000000000001000300000200040000000000000000020000000002000000004c0000000000000010004000000000000000002200001000200000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000,0x10000000008000000001000001000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000020000000000,0x100000000000000000000000000012000000000000000000080000400080000000000000000000000000000000000000000000000000000000100000000040000000000000000000000000000000000000400000000200000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000c0000000020000000008,0x100000000000000000000000000000] : Array Nat)[i/32]?.getD 0) 38 (i%32)
  | 7, i => fld ((#[0x40000000000400000000000400000000000040010002817c0008000000e800000000008000000010004000400000050000000000024009000000170000000000000000000000100000000000200000000000c0000000000100000000000400000000000000000000000200000004009e000000000030000000000040000000000000000000000020000000000000000002000100000000000000000000000200000000010400000000008000000000041,0x80000000000000000000000000000000001000000000400800040000003400c0001006f80000000000100000000000a000000000034000800000000000000000120000000000060000000000000000000000080010000000400020000801e00000000004800000000004000000000000000000000000000000000000100000000058000000000040000000000040000000000100000000000900000000000000000000002600000000000800000004007800000000050,0x210fe0000000000480000000000000000000005100000000000000200000002800000000001000000000008000000000000004400000138000800000020008000000000000000000000000000180700058084000f800000000048000200000008002000000020000000000090020000000520000000000080000000000000208020000f8000000000000000000000240000000000100000000002000020002000400000000001000000000000400000000000000800000041,0x100000003000010002007d00400000029800000000000000000000024080400084124000000000028000000000010000000000080000000800200000000000080000000001800000000001000000000802000000000000800a000000100000000000820004000000080000000000080000000001200000000000800800024097c000000000090000000000010000000000080000000000000000010000100000001005700900000009c00000000003000000000000000200020008,0x8200000000000000080004004000100000002000000000008000000000034001000000008000000000000000000000200020000000200000000000402000000000a00400010003e0000000000040000000000980200008025f00000000000800040000001c0048000000400000000000000000000001800000000000400100000000800900000000000000000010000000000020000000000020102010000550082000402be00000000004800000000000000000000003,0x24000000000000000000000090000000000010000000000200000000000000000000000000010000001f000000000010000400000010004000000068000001000020000000100200000000000040000000000800000000004100100000001000080000007400000000000000800000008000000000000000000000048000000000008000000000000000000000000000000000200000000000080000000000000000000000280000000004000000000000000100000041,0x80000000001040000000000200000000000800000000002400000004016c00400000005800800004004000000000010000000000004000000000040200000000070000000000280000000000200000000000900000002004f0000000000020000000001200000000000000000000000000020000000800000000000800000000002000000000008000000000010000000000048000a000202380000000001200020000002000000000014400000000000000000000001,0x200002003c000800000028000000000000000000000240000000000000000000002080000000000100000040000400208002012c000000000018000000000090000000000080000000000080000001000200000000400f00160010003e00000000000000000012007800000000000000000000002000000000008000000000220000000000440000000000240000000000300000000000200000000000000100000001600000000000000000000002000000000004,0x100000000000000000000000200000000000400000000000800280008011c0000000000080000000000004000000000c00000000004c0000000000900000000000000000000001000000000000400000000029800000000000000000000000000000000040000000000060000000000080000000000020080000001480000000000080000002800f000000000024000400000104000000000000000000000040012000000000000000000108001000302f800000000008,0x2000000000000000000000000000200000001000000000008000000000010000000000008000000000008000000000200020000001040000000000200000000000440120000003600000000003000000000001800000000000000600040096000000000020000000000090000000000120000000000120000000000480000000000180000000000404100004088a0000000000000000000000200000000000400000000000000200000007c00000000009000800000008,0x10000000000004004800000020002000000018002000000a60000000000480008000000380180040001f00000000003c0000000100400008000000300000000000400100000001204080400016400000000020000000000000] : Array Nat)[i/32]?.getD 0) 47 (i%32)
  | 8, i => fld ((#[0x82000805f00022002801f00014002405f00020000005110020000001420020001001f10010000405f00002002005f00010602001f00016002001b20018001005f20006000401f00030000001400006000001a000100012007000a0002401f10090002005780010002805f00010002005f00030001401f000b014a005f00028002004400016000005b10038001405f00020000401200030002805f08010000005f00016000005f00020000001600016002005b00012002805b000000024005,0x20030001405f00006000001600000000005f00002000005f000d0003005f08038000405f00010000405f00080002005f00000000004420080000005f00020000001a00020000801210080001000a0001002a005f00010002005f000a0000800000010000000700020000001f20030000001f00090002005f000e0000001210020001001f00090000005f00014000405f00080002005f00030002805f20010001001f100e0000805f00000000001e00030003001f00010003805b12880000801f,0x20038000405f00040000000300080002005f00010000200404010000405f00034000401f10000000005f000300000014000160020017000b0000001f00000000087f00020500005f000200020018000b0002005f20010000401f00006000001e00002002005f20080000005f00004002405f00016000005710000000805800000002801f00000000001b10000000401600010000200400016002005700020000005810038000405f000a0000001a00010001005f08080000005f000200000054,0x30010000001700016000005f00014000005f000000004016000300000014008a0000001a00014000405f00880000001b00006002005f00010002085f00092000005f20010000005f100a0000001810012002605f00010000005f008b0002005310000000805c00038000004400030000001400006000005410800001005f02820000005b00800000405200200008025f00098003005f20020001001f20006000801f00082000805f00090000205f000e00000012000200000016000380000012,0x6000405f000a2000805f000a0000001800022000801f200300010017200a0001001b000000010004000b8002405f00040003000a00010002005f00002000001c00036000005f00084000805f00010000001f200a0000805f000a0000001800000000001e00004002085f00000002e05f00000500005d00010000005f00028002005400006000005800036000001f200a0000801f00080000004800000000001e00020000001200022000805f000a0000001b00020000005400090002001f,0x2005f000b0008001f00004006005f00830002005f000080030006000b004a005f10000000405400000000001700000100045d00000002800900010000005f100a0001001f000060000054200a0000004b00040000000030000000005f00030002805f00012000005f00002002085f00090002005f000800010008200a0001001f200a0000001f00020000001200010000200600080000000800030000001700010000405f00010000805f00020000005810080000805f000100000014,0xa2000801f10030001001f10000000801200020000005800000100005d00000000801a080e0000805f20080000801f00000100005d000a2002805f00020000005400006000005f000b0002405f000b0002005f00082002805f00010000001400000002001000800001001a00038000000600014000405f00016002005f00020020005f00080000805f008000008052000b0002405f00020000001000000000801610800001005f00004002400d000200008012000000002016000000008019,0x10008000b0000001f00020100005f000b0002001f000b0002005f00080000000b08018000001f10020001001f00002002005f00002000001e00022003801f00010000000400000000001c200a0001805f00080000005f00000000001e000000020010000b0002805f00830001001f00000500005d00020000001200070003000f00000002205f000300004000008a0002005f00028003000f02091102445f80000000000800022300005f000000000004000080000000008000000007,0x80000005f00094000005f0000201a005f00012000401f12810000401f04080002405f00022000005f00000001005f00090002005f00000500005d00838000005f000000000008200c0001005f00090002005f00014000405f000b0502007f00000000000800000002005f00030502087f000b0102005f00010001200600030502005f00020000001300000000201a00010002005f040000000004000a0002405f00010000005f00010000005f00006000001c00000002401f00036000005f,0x10084002a05f00020000005f20010000005f00008000000300010002001f00000000000400000000805400016002005b00016000001f000e00000048000b0002005f00000000a01400000000000400010002005f000a0000001800000000401500010000005f00002002800d00800001001a10010001000600020000001220030000401f10000000401e00010002005f10000000005f00020000001320012001201f02820000005700082000805f00030000001604010000000400080002005f,0x40030180005f00010000200400016000005b00020000401210000000805000004000001e00800001001600014002405f20080000801f00020000001800030002805f00010000405f50080000001b00006000001a20010000401f00000000005f00010002005f00090002005f000a0000001808060000001f00004002005f000b0000005300006001401f200a0000005f00000100005f00000000005f00010000201400080000005f00060002005800090002001f000840024057000380000012,0x20030001001f00000000e01f00080000000800000002005f00020000001a00016002005700010000004400014000405f00090002005f00220000005f00002002805f20030000401f00030000001400000002601f00000100105d00006000805f00020000001000004000001c40010000005f008b0003005f00000500205d000b0003005f000a0002405f10030000001400000000000b00082000805f0019004240df000a0000001800010000801f00014000405f00010002005f000800034057,0x10000000400090003005f00080000005f00002002805f10000000405c10000000005f00016000005710000000801a000e0000000a00000002005f000200000018000b0002005f20030000005f20030000004700020002001400004002405f000a0002005f20030000405f000a00000018000a0000800000830000001600010000200400020000005800024003401f00810000001700000000000700010000204400000500005d00004002005f00000000601800010000005f00080001005f,0xa0003001f00030000005400010000005f00020000001402091102905f20080000005f000160020057200a0001001f000b0000601f10000000801e00020000201600080000005f00006000001620084001201f10020000001800080002005f10090002005b00800000000b00032000005f00000002005f00000002005f000b0002005f00060002004800030000400000820002005300090002005f008000000053008e0000005f00010001000420080000805f800800000008008000012016,0x800080000005f008a0001001f200c0000005f00020482001f00000000004800490042815f00800001001610000000005f00006000005800080002001f50000000005f20018000005f00022000805f] : Array Nat)[i/32]?.getD 0) 48 (i%32)
  | 9, i => fld ((#[0x10000480be00288006017c0000280002fa0036000c01f0002800080be80288006007c4040000002f80000000005f2012000500be00050001017c0058000f00fa0082000805f2012800480be001c000a007c0450000002fb0030000005f0016000400be80058003017c0011001402f80810001205f0002000500be00080004017c8058001202f800b0003001f0116000600be002c0008017c0008001402f80002002801f0116000400be40040001007d0040000402f80016002c01f,0x8002800080be00040002807c0002001200f80010000001f0004800480be80208002017c0410280802fb0014000405f5016c00180be400c0008017c0448001802fa00b6000005f0016000410be0008800a007d0018000002f800b000a005f40068000c0be002c3008007d0050000c02fa0036000805f0100000200be00018003007c0000000002f80020000005f00000005803e40208002017c0054001200f80026000005f0006000400be00200009017d0041000402fb0810001405f,0x2800000be800d0001017c0003001700f900b0002001f0010000480be00010009017c001b000002fa0038000405f6002000080be800c8002817c0410000802f90010000e01f2012000400be82280004017d0050000c02f90030001401f2006000000be800c0005007d001b000202f80010001201f4014000100be002c800a017d0050000402f80082000805f0006800080be00040000817d8050000002f900a0000005f0016000600be0000000b807c0008001402f80010000205f,0x100000003f42200006017d001b000600fa0014000405f0010400000be800c0005007d8040000002f80000000005f0004000200be00050000017c0001001402f90016000401f40140003003e40240009017c0050001a00fa0010000405f0000800400be402c000a017c401c000202f80030000005f0016000400be40280006007c0058001002fa00a0001801f0004000200be002c0008017c0058201800f80010000601f4010000100bf020c0004017d001c000a00fa0016000c05f,0x14000480be0204000e017c4070000400f80016000001f20100001003e00280008017c401c000200f80820001005f0016000400be02080000017c0458001802fa0014000405f0006000500be0000800a017c0410000802fa80b6000c05f1002000000be002c000c017c8059001c00f80830000005f6002000000be00058000007c0018001002fa00a2000805f2002000080be80058003017c0058000002f800b0002005f0016000400be002c0008017c004b000600f80090002005f,0x4006800080be80380006007c0058001802f80080002405f00060007003e00240008017c0458001802f80002002005f0110000680be000c000c017c0458001002f80090002005f0004000000be402c0008007c0008000002f90092000801f00128001c0bf40200002017c000b000600f88036001c01f0014000400be40240008017c4070000402f800a2000805f00060007003e00240008017e040a000a02fa00a2000805f0014400000be0028000d007c0058001802fa0882001805f,0x90009007e0018000a02f900b0002005f0016000400be40200002017c4078001400f80010000205f10170004803e4024800a017d0050000002fa0030001405f0016800480be80040001017c0003001700f900b4003401f0016000400be800d0005007c0048001002f80020001005f4006000080be00288002017e001c000a02f80086002c01f] : Array Nat)[i/32]?.getD 0) 47 (i%32)
  | 10, i => fld ((#[0x1000f0001007d800a000200fa00e2000801f4010400100be00040000807e0018000002f80084002401f00040002003e0004800a007c0000000002f80000000005f0012000400bf00050001017c0058001800fd0082000801f0016000400be02000004017c0010000002fa00a0000005f] : Array Nat)[i/32]?.getD 0) 47 (i%32)
  | 11, i => fld ((#[31] : Array Nat)[i/32]?.getD 0) 5 (i%32)
  | _, _ => 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def wf (s i : Nat) := let w := packW s i; unpack dict 9 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def po (s i : Nat) := let w := packO s i; unpackOps dict 9 (w >>> 4) (w &&& 15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def tab : Table := ⟨num,hash,wf,po,flags0,1,cuts⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def test := cell tab d target pairs
end C67


end Lower29252


namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk2_0 : ∀ i, 0 ≤ i → i < 1 → test 2 i = true := span_ok (by decide +kernel : span (test 2) 1 0 = true)
end C0
namespace C16
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C16
namespace C35
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 5 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 5 0 = true)
end C35
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 8 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 8 0 = true)
end C44
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 13 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 5 8 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 8 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 0 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_24 : ∀ i, 24 ≤ i → i < 27 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 3 24 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_40 : ∀ i, 40 ≤ i → i < 46 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 6 40 = true)
end C58
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 3 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 3 0 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_96 : ∀ i, 96 ≤ i → i < 104 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 96 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_56 : ∀ i, 56 ≤ i → i < 64 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 56 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_152 : ∀ i, 152 ≤ i → i < 160 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 152 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_248 : ∀ i, 248 ≤ i → i < 256 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 248 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_8 : ∀ i, 8 ≤ i → i < 16 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 8 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_104 : ∀ i, 104 ≤ i → i < 112 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 104 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_200 : ∀ i, 200 ≤ i → i < 208 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 200 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_296 : ∀ i, 296 ≤ i → i < 304 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 296 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_392 : ∀ i, 392 ≤ i → i < 400 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 392 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_24 : ∀ i, 24 ≤ i → i < 32 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 24 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_120 : ∀ i, 120 ≤ i → i < 128 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 120 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk10_0 : ∀ i, 0 ≤ i → i < 8 → test 10 i = true := span_ok (by decide +kernel : span (test 10) 8 0 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C0
namespace C21
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C21
namespace C35
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C35
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_8 : ∀ i, 8 ≤ i → i < 16 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 8 8 = true)
end C44
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 1 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 1 0 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_8 : ∀ i, 8 ≤ i → i < 16 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 8 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_0 : ∀ i, 0 ≤ i → i < 1 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 1 0 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_0 : ∀ i, 0 ≤ i → i < 8 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 0 = true)
end C58
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 8 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 0 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 16 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 8 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_104 : ∀ i, 104 ≤ i → i < 112 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 104 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_64 : ∀ i, 64 ≤ i → i < 72 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 64 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_160 : ∀ i, 160 ≤ i → i < 168 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 160 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_256 : ∀ i, 256 ≤ i → i < 264 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 256 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_16 : ∀ i, 16 ≤ i → i < 24 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 16 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_112 : ∀ i, 112 ≤ i → i < 120 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 112 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_208 : ∀ i, 208 ≤ i → i < 216 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 208 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_304 : ∀ i, 304 ≤ i → i < 312 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 304 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_400 : ∀ i, 400 ≤ i → i < 408 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 400 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_32 : ∀ i, 32 ≤ i → i < 40 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 32 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_128 : ∀ i, 128 ≤ i → i < 136 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 128 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk10_8 : ∀ i, 8 ≤ i → i < 16 → test 10 i = true := span_ok (by decide +kernel : span (test 10) 8 8 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C1
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk2_0 : ∀ i, 0 ≤ i → i < 1 → test 2 i = true := span_ok (by decide +kernel : span (test 2) 1 0 = true)
end C1
namespace C28
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C28
namespace C38
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 1 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 1 0 = true)
end C38
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_16 : ∀ i, 16 ≤ i → i < 24 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 8 16 = true)
end C44
namespace C49
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C49
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_16 : ∀ i, 16 ≤ i → i < 24 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 16 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 7 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 7 0 = true)
end C58
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_8 : ∀ i, 8 ≤ i → i < 15 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 7 8 = true)
end C58
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_8 : ∀ i, 8 ≤ i → i < 10 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 2 8 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_16 : ∀ i, 16 ≤ i → i < 24 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 16 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_112 : ∀ i, 112 ≤ i → i < 120 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 112 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_72 : ∀ i, 72 ≤ i → i < 80 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 72 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_168 : ∀ i, 168 ≤ i → i < 176 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 168 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_264 : ∀ i, 264 ≤ i → i < 272 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 264 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_24 : ∀ i, 24 ≤ i → i < 32 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 24 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_120 : ∀ i, 120 ≤ i → i < 128 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 120 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_216 : ∀ i, 216 ≤ i → i < 224 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 216 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_312 : ∀ i, 312 ≤ i → i < 320 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 312 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_408 : ∀ i, 408 ≤ i → i < 416 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 408 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_40 : ∀ i, 40 ≤ i → i < 48 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 40 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_136 : ∀ i, 136 ≤ i → i < 144 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 136 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk10_16 : ∀ i, 16 ≤ i → i < 19 → test 10 i = true := span_ok (by decide +kernel : span (test 10) 3 16 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C1
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C1
namespace C28
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 5 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 5 0 = true)
end C28
namespace C38
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 1 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 1 0 = true)
end C38
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_24 : ∀ i, 24 ≤ i → i < 32 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 8 24 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_24 : ∀ i, 24 ≤ i → i < 32 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 24 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C58
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_0 : ∀ i, 0 ≤ i → i < 1 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 1 0 = true)
end C58
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_24 : ∀ i, 24 ≤ i → i < 32 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 24 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_120 : ∀ i, 120 ≤ i → i < 128 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 120 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_80 : ∀ i, 80 ≤ i → i < 88 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 80 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_176 : ∀ i, 176 ≤ i → i < 184 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 176 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_272 : ∀ i, 272 ≤ i → i < 280 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 272 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_32 : ∀ i, 32 ≤ i → i < 40 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 32 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_128 : ∀ i, 128 ≤ i → i < 136 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 128 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_224 : ∀ i, 224 ≤ i → i < 232 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 224 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_320 : ∀ i, 320 ≤ i → i < 328 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 320 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_416 : ∀ i, 416 ≤ i → i < 424 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 416 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_48 : ∀ i, 48 ≤ i → i < 56 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 48 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_144 : ∀ i, 144 ≤ i → i < 152 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 144 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk11_0 : ∀ i, 0 ≤ i → i < 1 → test 11 i = true := span_ok (by decide +kernel : span (test 11) 1 0 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C2
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk2_0 : ∀ i, 0 ≤ i → i < 1 → test 2 i = true := span_ok (by decide +kernel : span (test 2) 1 0 = true)
end C2
namespace C28
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C28
namespace C38
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C38
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 8 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 0 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 8 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 0 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_32 : ∀ i, 32 ≤ i → i < 40 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 32 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 16 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 8 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 3 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 3 0 = true)
end C59
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 16 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 8 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_32 : ∀ i, 32 ≤ i → i < 40 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 32 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_128 : ∀ i, 128 ≤ i → i < 133 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 5 128 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_88 : ∀ i, 88 ≤ i → i < 96 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 88 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_184 : ∀ i, 184 ≤ i → i < 192 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 184 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_280 : ∀ i, 280 ≤ i → i < 288 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 280 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_40 : ∀ i, 40 ≤ i → i < 48 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 40 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_136 : ∀ i, 136 ≤ i → i < 144 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 136 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_232 : ∀ i, 232 ≤ i → i < 240 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 232 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_328 : ∀ i, 328 ≤ i → i < 336 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 328 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_424 : ∀ i, 424 ≤ i → i < 432 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 424 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_56 : ∀ i, 56 ≤ i → i < 64 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 56 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_152 : ∀ i, 152 ≤ i → i < 160 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 152 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C2
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C2
namespace C30
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C30
namespace C40
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C40
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_8 : ∀ i, 8 ≤ i → i < 16 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 8 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_8 : ∀ i, 8 ≤ i → i < 16 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 8 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_40 : ∀ i, 40 ≤ i → i < 48 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 40 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_16 : ∀ i, 16 ≤ i → i < 24 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 16 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 8 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 0 = true)
end C59
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_16 : ∀ i, 16 ≤ i → i < 17 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 16 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_40 : ∀ i, 40 ≤ i → i < 48 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 40 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 8 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 0 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_96 : ∀ i, 96 ≤ i → i < 104 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 96 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_192 : ∀ i, 192 ≤ i → i < 200 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 192 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_288 : ∀ i, 288 ≤ i → i < 296 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 288 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_48 : ∀ i, 48 ≤ i → i < 56 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 48 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_144 : ∀ i, 144 ≤ i → i < 152 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 144 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_240 : ∀ i, 240 ≤ i → i < 248 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 240 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_336 : ∀ i, 336 ≤ i → i < 344 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 336 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_432 : ∀ i, 432 ≤ i → i < 440 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 432 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_64 : ∀ i, 64 ≤ i → i < 72 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 64 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_160 : ∀ i, 160 ≤ i → i < 168 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 160 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C3
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk2_0 : ∀ i, 0 ≤ i → i < 1 → test 2 i = true := span_ok (by decide +kernel : span (test 2) 1 0 = true)
end C3
namespace C30
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 5 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 5 0 = true)
end C30
namespace C40
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 5 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 5 0 = true)
end C40
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_16 : ∀ i, 16 ≤ i → i < 24 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 16 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_48 : ∀ i, 48 ≤ i → i < 56 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 48 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_24 : ∀ i, 24 ≤ i → i < 30 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 6 24 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_8 : ∀ i, 8 ≤ i → i < 10 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 2 8 = true)
end C59
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 7 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 7 0 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_48 : ∀ i, 48 ≤ i → i < 56 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 48 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_8 : ∀ i, 8 ≤ i → i < 16 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 8 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_104 : ∀ i, 104 ≤ i → i < 112 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 104 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_200 : ∀ i, 200 ≤ i → i < 208 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 200 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_296 : ∀ i, 296 ≤ i → i < 304 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 296 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_56 : ∀ i, 56 ≤ i → i < 64 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 56 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_152 : ∀ i, 152 ≤ i → i < 160 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 152 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_248 : ∀ i, 248 ≤ i → i < 256 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 248 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_344 : ∀ i, 344 ≤ i → i < 352 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 344 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_440 : ∀ i, 440 ≤ i → i < 448 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 440 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_72 : ∀ i, 72 ≤ i → i < 80 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 72 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_168 : ∀ i, 168 ≤ i → i < 176 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 168 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C3
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C3
namespace C30
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C30
namespace C40
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C40
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_24 : ∀ i, 24 ≤ i → i < 32 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 24 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 16 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 8 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_56 : ∀ i, 56 ≤ i → i < 64 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 56 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 8 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 0 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C59
namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_0 : ∀ i, 0 ≤ i → i < 1 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 1 0 = true)
end C62
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_56 : ∀ i, 56 ≤ i → i < 64 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 56 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_16 : ∀ i, 16 ≤ i → i < 24 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 16 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_112 : ∀ i, 112 ≤ i → i < 120 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 112 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_208 : ∀ i, 208 ≤ i → i < 216 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 208 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_304 : ∀ i, 304 ≤ i → i < 312 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 304 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_64 : ∀ i, 64 ≤ i → i < 72 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 64 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_160 : ∀ i, 160 ≤ i → i < 168 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 160 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_256 : ∀ i, 256 ≤ i → i < 264 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 256 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_352 : ∀ i, 352 ≤ i → i < 360 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 352 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_448 : ∀ i, 448 ≤ i → i < 456 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 448 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_80 : ∀ i, 80 ≤ i → i < 88 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 80 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_176 : ∀ i, 176 ≤ i → i < 184 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 176 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C4
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C4
namespace C33
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C33
namespace C42
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 1 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 1 0 = true)
end C42
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_32 : ∀ i, 32 ≤ i → i < 40 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 32 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_16 : ∀ i, 16 ≤ i → i < 24 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 16 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_64 : ∀ i, 64 ≤ i → i < 68 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 4 64 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_8 : ∀ i, 8 ≤ i → i < 16 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 8 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_8 : ∀ i, 8 ≤ i → i < 16 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 8 = true)
end C59
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 8 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 0 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_64 : ∀ i, 64 ≤ i → i < 72 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 64 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_24 : ∀ i, 24 ≤ i → i < 32 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 24 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_120 : ∀ i, 120 ≤ i → i < 128 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 120 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_216 : ∀ i, 216 ≤ i → i < 224 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 216 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_312 : ∀ i, 312 ≤ i → i < 320 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 312 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_72 : ∀ i, 72 ≤ i → i < 80 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 72 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_168 : ∀ i, 168 ≤ i → i < 176 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 168 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_264 : ∀ i, 264 ≤ i → i < 272 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 264 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_360 : ∀ i, 360 ≤ i → i < 368 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 360 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_456 : ∀ i, 456 ≤ i → i < 462 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 6 456 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_88 : ∀ i, 88 ≤ i → i < 96 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 88 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_184 : ∀ i, 184 ≤ i → i < 192 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 184 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C6
namespace C33
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 5 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 5 0 = true)
end C33
namespace C42
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_0 : ∀ i, 0 ≤ i → i < 1 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 1 0 = true)
end C42
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_40 : ∀ i, 40 ≤ i → i < 48 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 40 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_24 : ∀ i, 24 ≤ i → i < 32 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 24 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_0 : ∀ i, 0 ≤ i → i < 8 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 0 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_16 : ∀ i, 16 ≤ i → i < 24 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 16 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_16 : ∀ i, 16 ≤ i → i < 17 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 16 = true)
end C59
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_8 : ∀ i, 8 ≤ i → i < 16 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 8 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_72 : ∀ i, 72 ≤ i → i < 80 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 72 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_32 : ∀ i, 32 ≤ i → i < 40 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 32 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_128 : ∀ i, 128 ≤ i → i < 136 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 128 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_224 : ∀ i, 224 ≤ i → i < 232 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 224 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_320 : ∀ i, 320 ≤ i → i < 328 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 320 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_80 : ∀ i, 80 ≤ i → i < 88 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 80 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_176 : ∀ i, 176 ≤ i → i < 184 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 176 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_272 : ∀ i, 272 ≤ i → i < 280 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 272 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_368 : ∀ i, 368 ≤ i → i < 376 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 368 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_0 : ∀ i, 0 ≤ i → i < 8 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 0 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_96 : ∀ i, 96 ≤ i → i < 104 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 96 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_192 : ∀ i, 192 ≤ i → i < 200 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 192 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C11
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C11
namespace C33
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C33
namespace C42
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 1 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 1 0 = true)
end C42
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_48 : ∀ i, 48 ≤ i → i < 52 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 4 48 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_32 : ∀ i, 32 ≤ i → i < 40 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 32 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_8 : ∀ i, 8 ≤ i → i < 16 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 8 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_24 : ∀ i, 24 ≤ i → i < 32 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 24 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_0 : ∀ i, 0 ≤ i → i < 7 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 7 0 = true)
end C59
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_16 : ∀ i, 16 ≤ i → i < 24 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 8 16 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_80 : ∀ i, 80 ≤ i → i < 88 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 80 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_40 : ∀ i, 40 ≤ i → i < 48 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 40 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_136 : ∀ i, 136 ≤ i → i < 144 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 136 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_232 : ∀ i, 232 ≤ i → i < 240 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 232 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_328 : ∀ i, 328 ≤ i → i < 336 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 328 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_88 : ∀ i, 88 ≤ i → i < 96 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 88 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_184 : ∀ i, 184 ≤ i → i < 192 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 184 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_280 : ∀ i, 280 ≤ i → i < 288 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 280 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_376 : ∀ i, 376 ≤ i → i < 384 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 376 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_8 : ∀ i, 8 ≤ i → i < 16 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 8 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_104 : ∀ i, 104 ≤ i → i < 112 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 104 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_200 : ∀ i, 200 ≤ i → i < 208 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 200 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C14
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 1 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 1 0 = true)
end C14
namespace C35
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk4_0 : ∀ i, 0 ≤ i → i < 4 → test 4 i = true := span_ok (by decide +kernel : span (test 4) 4 0 = true)
end C35
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk3_0 : ∀ i, 0 ≤ i → i < 8 → test 3 i = true := span_ok (by decide +kernel : span (test 3) 8 0 = true)
end C44
namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_0 : ∀ i, 0 ≤ i → i < 8 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 0 = true)
end C44
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_40 : ∀ i, 40 ≤ i → i < 46 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 6 40 = true)
end C57
namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_16 : ∀ i, 16 ≤ i → i < 24 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 16 = true)
end C57
namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_32 : ∀ i, 32 ≤ i → i < 40 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 32 = true)
end C58
namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_0 : ∀ i, 0 ≤ i → i < 1 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 1 0 = true)
end C59
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk5_24 : ∀ i, 24 ≤ i → i < 30 → test 5 i = true := span_ok (by decide +kernel : span (test 5) 6 24 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk6_88 : ∀ i, 88 ≤ i → i < 96 → test 6 i = true := span_ok (by decide +kernel : span (test 6) 8 88 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_48 : ∀ i, 48 ≤ i → i < 56 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 48 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_144 : ∀ i, 144 ≤ i → i < 152 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 144 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk7_240 : ∀ i, 240 ≤ i → i < 248 → test 7 i = true := span_ok (by decide +kernel : span (test 7) 8 240 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_0 : ∀ i, 0 ≤ i → i < 8 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 0 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_96 : ∀ i, 96 ≤ i → i < 104 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 96 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_192 : ∀ i, 192 ≤ i → i < 200 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 192 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_288 : ∀ i, 288 ≤ i → i < 296 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 288 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk8_384 : ∀ i, 384 ≤ i → i < 392 → test 8 i = true := span_ok (by decide +kernel : span (test 8) 8 384 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_16 : ∀ i, 16 ≤ i → i < 24 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 16 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_112 : ∀ i, 112 ≤ i → i < 120 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 8 112 = true)
end C67
namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem chunk9_208 : ∀ i, 208 ≤ i → i < 215 → test 9 i = true := span_ok (by decide +kernel : span (test 9) 7 208 = true)
end C67
end Lower29252

namespace Lower29252
open GraphKernel29252 GraphReplay29252
namespace C0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk2_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 2 2 = true) s lo (by omega))
end C0

namespace C1
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk2_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 2 2 = true) s lo (by omega))
end C1

namespace C2
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk2_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 2 2 = true) s lo (by omega))
end C2

namespace C3
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk2_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 2 2 = true) s lo (by omega))
end C3

namespace C4
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C5.low : Lower true 0xff00ff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000] 0xfe00ec 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xcc00cc,0,2)] (by decide +kernel) (by decide +kernel) C0.low

namespace C6
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C6

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C7.low : Lower true 0x33333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0x32322220 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33003300,1,9)] (by decide +kernel) (by decide +kernel) C0.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C8.low : Lower true 0x33333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0x33323320 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33003300,0,8)] (by decide +kernel) (by decide +kernel) C0.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C9.low : Lower true 0xf0f00000f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xf0c00000e00 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa0a00000a0a,8,9)] (by decide +kernel) (by decide +kernel) C1.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C10.low : Lower true 0xf0f00000f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xf0e00000e0a 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa0a00000a0a,0,1)] (by decide +kernel) (by decide +kernel) C1.low

namespace C11
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C11

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C12.low : Lower true 0x555500005555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0x555400005450 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050,0,4)] (by decide +kernel) (by decide +kernel) C1.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C13.low : Lower true 0x33003300330033 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0x33003300320020 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33003300000000,0,32)] (by decide +kernel) (by decide +kernel) C0.low

namespace C14
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C14

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C15.low : Lower true 0x505050505050505 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0x505050405050400 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050000,0,16)] (by decide +kernel) (by decide +kernel) C1.low

namespace C16
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C16

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C17.low : Lower true 0xf0f0000000000000f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xf0e0000000000000e00 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c0000000000000c0c,8,10)] (by decide +kernel) (by decide +kernel) C2.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C18.low : Lower true 0xf0f0000000000000f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xf0e0000000000000e0a 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa0a0000000000000a0a,0,1)] (by decide +kernel) (by decide +kernel) C3.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C19.low : Lower true 0x33330000000000003333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0x33220000000000002220 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30300000000000003030,1,5)] (by decide +kernel) (by decide +kernel) C2.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C20.low : Lower true 0x55550000000000005555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0x55540000000000005450 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50500000000000005050,0,4)] (by decide +kernel) (by decide +kernel) C3.low

namespace C21
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤3) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 4 := replay tab d target roots pairs 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp [tab,cuts]) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 1 3 = true) s lo (by omega))
end C21

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C22.low : Lower true 0x3300330000000000330033 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x3200220000000000320020 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300330000000000000000,1,65)] (by decide +kernel) (by decide +kernel) C0.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C23.low : Lower true 0x3300330000000000330033 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x3300330000000000320020 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3300330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) C0.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C24.low : Lower true 0x30303030000000003030303 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x30203020000000002020200 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30300000000000003030000,1,17)] (by decide +kernel) (by decide +kernel) C2.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C25.low : Lower true 0x50505050000000005050505 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x50505040000000005050400 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50500000000000005050000,0,16)] (by decide +kernel) (by decide +kernel) C3.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C26.low : Lower true 0x303000003030000030300000303 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x302000003020000030000000200 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x303000000000000030300000000,8,40)] (by decide +kernel) (by decide +kernel) C2.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C27.low : Lower true 0x505000005050000050500000505 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x504000005040000050400000400 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C1.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh0 : Lower true 0xcccccccc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0xccc8cc80 5 := lower_iso [(0x33333333,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C8.low

namespace C28
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C7.low⟩
    · exact ⟨(by decide +kernel),sh0⟩
    · exact ⟨(by decide +kernel),C4.low⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),C6.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C28

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C29.low : Lower true 0xffffffff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0xfffeffec 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00ff00,0,8)] (by decide +kernel) (by decide +kernel) C5.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh1 : Lower true 0xf0f00000f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xf0e00000e0a0 5 := lower_iso [(0xf0f00000f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C10.low

namespace C30
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C9.low⟩
    · exact ⟨(by decide +kernel),sh1⟩
    · exact ⟨(by decide +kernel),C4.low⟩
    · exact ⟨(by decide +kernel),C1.low⟩
    · exact ⟨(by decide +kernel),C11.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C30

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C31.low : Lower true 0xffff0000ffff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xfffe0000fefa 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f00000f0f0,0,4)] (by decide +kernel) (by decide +kernel) C10.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh2 : Lower true 0xff00ff00000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000] 0xfe00ec00000000 5 := lower_iso [(0xff00ff,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C5.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C32.low : Lower true 0xff00ff00ff00ff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0xfe00ec00fa00a0 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00ff00000000,2,34)] (by decide +kernel) (by decide +kernel) sh2

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh3 : Lower true 0xf0f00000f0f0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xf0e00000e0a0000 5 := lower_iso [(0xf0f00000f0f,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C10.low

namespace C33
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C9.low⟩
    · exact ⟨(by decide +kernel),sh3⟩
    · exact ⟨(by decide +kernel),C6.low⟩
    · exact ⟨(by decide +kernel),C1.low⟩
    · exact ⟨(by decide +kernel),C14.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C33

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C34.low : Lower true 0xf0f0f0f0f0f0f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0xf0f0f0e0f0f0e0a 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f00000f0f0000,0,16)] (by decide +kernel) (by decide +kernel) C10.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh4 : Lower true 0x3333333300000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0x3332332000000000 5 := lower_iso [(0x33333333,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C8.low

namespace C35
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C7.low⟩
    · exact ⟨(by decide +kernel),sh4⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),C11.low⟩
    · exact ⟨(by decide +kernel),C14.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C35

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C36.low : Lower true 0x3333333333333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0x3333333333323320 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333333300000000,0,32)] (by decide +kernel) (by decide +kernel) C8.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh5 : Lower true 0x5555000055550000 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0x5554000054500000 5 := lower_iso [(0x555500005555,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C12.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C37.low : Lower true 0x5555555555555555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0x5554554454504400 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5555000055550000,4,20)] (by decide +kernel) (by decide +kernel) sh5

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh6 : Lower true 0xf0f0000000000000f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xf0e0000000000000e0a0 5 := lower_iso [(0xf0f0000000000000f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C18.low

namespace C38
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C17.low⟩
    · exact ⟨(by decide +kernel),sh6⟩
    · exact ⟨(by decide +kernel),C19.low⟩
    · exact ⟨(by decide +kernel),C4.low⟩
    · exact ⟨(by decide +kernel),C16.low⟩
    · exact ⟨(by decide +kernel),C3.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C38

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C39.low : Lower true 0xffff000000000000ffff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xfffe000000000000fefa 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0000000000000f0f0,0,4)] (by decide +kernel) (by decide +kernel) C18.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh7 : Lower true 0xcc00cc0000000000cc00cc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xcc00cc0000000000c80080 5 := lower_iso [(0x3300330000000000330033,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C23.low

namespace C40
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C22.low⟩
    · exact ⟨(by decide +kernel),sh7⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),C16.low⟩
    · exact ⟨(by decide +kernel),C21.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C40

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C41.low : Lower true 0xff00ff0000000000ff00ff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xfe00ee0000000000fe00ec 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00ff0000000000000000,1,65)] (by decide +kernel) (by decide +kernel) C5.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh8 : Lower true 0xf0f0000000000000f0f0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xf0e0000000000000e0a0000 5 := lower_iso [(0xf0f0000000000000f0f,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C18.low

namespace C42
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C17.low⟩
    · exact ⟨(by decide +kernel),sh8⟩
    · exact ⟨(by decide +kernel),C24.low⟩
    · exact ⟨(by decide +kernel),C6.low⟩
    · exact ⟨(by decide +kernel),C3.low⟩
    · exact ⟨(by decide +kernel),C21.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C42

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C43.low : Lower true 0xf0f0f0f000000000f0f0f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xf0f0f0e000000000f0f0e0a 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0000000000000f0f0000,0,16)] (by decide +kernel) (by decide +kernel) C18.low

namespace C44
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤7) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk3_0 i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk4_0 chunk4_8) (range_split chunk4_16 chunk4_24)) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk5_0 (range_split chunk5_8 chunk5_16)) (range_split (range_split chunk5_24 chunk5_32) (range_split chunk5_40 chunk5_48))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk6_0 chunk6_8) i (Nat.zero_le _) hi
  · exact fun i hi => chunk7_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 8 := replay tab d target roots pairs 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C7.low⟩
    · exact ⟨(by decide +kernel),C19.low⟩
    · exact ⟨(by decide +kernel),C22.low⟩
    · exact ⟨(by decide +kernel),C24.low⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),C2.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 4 4 = true) s lo (by omega))
end C44

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C45.low : Lower true 0x333333330000000033333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x333233220000000033323320 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x333333330000000000000000,1,65)] (by decide +kernel) (by decide +kernel) C8.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C46.low : Lower true 0x333333330000000033333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x333333330000000033323320 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x333333330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) C8.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh9 : Lower true 0x555500000000000055550000 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0x555400000000000054500000 5 := lower_iso [(0x55550000000000005555,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C20.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C47.low : Lower true 0x555555550000000055555555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x555455440000000054504400 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x555500000000000055550000,4,20)] (by decide +kernel) (by decide +kernel) sh9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C48.low : Lower true 0xff000000ff000000ff000000ff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xee000000ee000000ec000000a0 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00000000000000ff00000000,2,34)] (by decide +kernel) (by decide +kernel) C16.low

namespace C49
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤6) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk6_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 7 := replay tab d target roots pairs 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C9.low⟩
    · exact ⟨(by decide +kernel),C17.low⟩
    · exact ⟨(by decide +kernel),C26.low⟩
    · exact ⟨(by decide +kernel),C27.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 3 4 = true) s lo (by omega))
end C49

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C50.low : Lower true 0xf0f00000f0f00000f0f00000f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xf0e00000f0e00000f0e00000e0a 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f00000f0f0000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C10.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C51.low : Lower true 0x3333000033330000333300003333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x3322000033220000332000002220 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3333000000000000333300000000,8,40)] (by decide +kernel) (by decide +kernel) C19.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C52.low : Lower true 0x5555000055550000555500005555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x5554000055540000555400005450 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5555000055550000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C12.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C53.low : Lower true 0xf000f000f000f000f000f000f000f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xe000e000e000e000e000c000a0000 5 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf000f00000000000f000f00000000,2,34)] (by decide +kernel) (by decide +kernel) C21.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C54.low : Lower true 0x330033003300330033003300330033 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x330033003300330033003300320020 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x330033003300330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) C13.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C55.low : Lower true 0x3030303030303030303030303030303 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x3020302030203020302030002020200 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3030303000000000303030300000000,8,40)] (by decide +kernel) (by decide +kernel) C24.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C56.low : Lower true 0x5050505050505050505050505050505 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x5050504050505040505050405050400 6 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5050505050505050000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C15.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh10 : Lower true 0xffffffff00000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000] 0xfffeffec00000000 6 := lower_iso [(0xffffffff,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C29.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh11 : Lower true 0xffff0000ffff0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000] 0xfffe0000fefa0000 6 := lower_iso [(0xffff0000ffff,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C31.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh12 : Lower true 0xf0f0f0f0f0f0f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0xf0f0f0e0f0f0e0a0 6 := lower_iso [(0xf0f0f0f0f0f0f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C34.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh13 : Lower true 0xcccccccccccccccc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0xccccccccccc8cc80 6 := lower_iso [(0x3333333333333333,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C36.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh14 : Lower true 0xcc00cc00cc00cc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0xcc00cc00c80080 5 := lower_iso [(0x33003300330033,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C13.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh15 : Lower true 0x5050505050505050 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000] 0x5050504050504000 5 := lower_iso [(0x505050505050505,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C15.low

namespace C57
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤9) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk5_0 chunk5_8) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk6_0 (range_split chunk6_8 chunk6_16)) (range_split chunk6_24 (range_split chunk6_32 chunk6_40))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split (range_split chunk7_0 chunk7_8) (range_split chunk7_16 chunk7_24)) (range_split (range_split chunk7_32 chunk7_40) (range_split chunk7_48 (range_split chunk7_56 chunk7_64)))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk8_0 chunk8_8) (range_split chunk8_16 chunk8_24)) i (Nat.zero_le _) hi
  · exact fun i hi => chunk9_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 10 := replay tab d target roots pairs 10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C28.low⟩
    · exact ⟨(by decide +kernel),C30.low⟩
    · exact ⟨(by decide +kernel),C33.low⟩
    · exact ⟨(by decide +kernel),C35.low⟩
    · exact ⟨(by decide +kernel),sh10⟩
    · exact ⟨(by decide +kernel),sh11⟩
    · exact ⟨(by decide +kernel),C32.low⟩
    · exact ⟨(by decide +kernel),sh12⟩
    · exact ⟨(by decide +kernel),sh13⟩
    · exact ⟨(by decide +kernel),C37.low⟩
    · exact ⟨(by decide +kernel),sh2⟩
    · exact ⟨(by decide +kernel),C7.low⟩
    · exact ⟨(by decide +kernel),sh0⟩
    · exact ⟨(by decide +kernel),C9.low⟩
    · exact ⟨(by decide +kernel),sh1⟩
    · exact ⟨(by decide +kernel),sh3⟩
    · exact ⟨(by decide +kernel),sh5⟩
    · exact ⟨(by decide +kernel),sh14⟩
    · exact ⟨(by decide +kernel),sh15⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),C1.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 5 5 = true) s lo (by omega))
end C57

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh16 : Lower true 0xffff000000000000ffff0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000] 0xfffe000000000000fefa0000 6 := lower_iso [(0xffff000000000000ffff,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C39.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh17 : Lower true 0xf0f0f0f000000000f0f0f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xf0f0f0e000000000f0f0e0a0 6 := lower_iso [(0xf0f0f0f000000000f0f0f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C43.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh18 : Lower true 0xcccccccc00000000cccccccc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xcccccccc00000000ccc8cc80 6 := lower_iso [(0x333333330000000033333333,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C46.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh19 : Lower true 0x505050500000000050505050 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x505050400000000050504000 5 := lower_iso [(0x50505050000000005050505,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C25.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh20 : Lower true 0xcc00cc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000] 0xc80080 4 := lower_iso [(0x330033,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C0.low

namespace C58
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤9) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk5_0 i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk6_0 chunk6_8) (range_split chunk6_16 chunk6_24)) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split chunk7_0 (range_split chunk7_8 chunk7_16)) (range_split chunk7_24 (range_split chunk7_32 chunk7_40))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk8_0 chunk8_8) i (Nat.zero_le _) hi
  · exact fun i hi => chunk9_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 10 := replay tab d target roots pairs 10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C44.low⟩
    · exact ⟨(by decide +kernel),C28.low⟩
    · exact ⟨(by decide +kernel),C38.low⟩
    · exact ⟨(by decide +kernel),C40.low⟩
    · exact ⟨(by decide +kernel),C42.low⟩
    · exact ⟨(by decide +kernel),sh16⟩
    · exact ⟨(by decide +kernel),sh17⟩
    · exact ⟨(by decide +kernel),sh18⟩
    · exact ⟨(by decide +kernel),C47.low⟩
    · exact ⟨(by decide +kernel),C7.low⟩
    · exact ⟨(by decide +kernel),sh0⟩
    · exact ⟨(by decide +kernel),C17.low⟩
    · exact ⟨(by decide +kernel),sh6⟩
    · exact ⟨(by decide +kernel),sh9⟩
    · exact ⟨(by decide +kernel),C22.low⟩
    · exact ⟨(by decide +kernel),sh7⟩
    · exact ⟨(by decide +kernel),sh19⟩
    · exact ⟨(by decide +kernel),C0.low⟩
    · exact ⟨(by decide +kernel),sh20⟩
    · exact ⟨(by decide +kernel),C3.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 5 5 = true) s lo (by omega))
end C58

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh21 : Lower true 0xf0f00000f0f00000f0f00000f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xf0e00000f0e00000f0e00000e0a0 6 := lower_iso [(0xf0f00000f0f00000f0f00000f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C50.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh22 : Lower true 0x5050000050500000505000005050 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x5040000050400000504000004000 5 := lower_iso [(0x505000005050000050500000505,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C27.low

namespace C59
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤8) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk5_0 chunk5_8) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk6_0 (range_split chunk6_8 chunk6_16)) i (Nat.zero_le _) hi
  · exact fun i hi => chunk7_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk8_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 9 := replay tab d target roots pairs 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C30.low⟩
    · exact ⟨(by decide +kernel),C38.low⟩
    · exact ⟨(by decide +kernel),C49.low⟩
    · exact ⟨(by decide +kernel),sh21⟩
    · exact ⟨(by decide +kernel),C51.low⟩
    · exact ⟨(by decide +kernel),C48.low⟩
    · exact ⟨(by decide +kernel),C27.low⟩
    · exact ⟨(by decide +kernel),sh22⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 4 5 = true) s lo (by omega))
end C59

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C60.low : Lower true 0xffff0000ffff0000ffff0000ffff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xfffe0000fffe0000fffe0000fefa 7 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C31.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C61.low : Lower true 0xff00ff00ff00ff00ff00ff00ff00ff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xfe00ee00fe00ee00fe00ec00fa00a0 8 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00ff0000000000ff00ff00000000,2,34)] (by decide +kernel) (by decide +kernel) C40.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh23 : Lower true 0xf0f00000f0f00000f0f00000f0f0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xf0e00000f0e00000f0e00000e0a0000 6 := lower_iso [(0xf0f00000f0f00000f0f00000f0f,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C50.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh24 : Lower true 0x5050000050500000505000005050000 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x5040000050400000504000004000000 5 := lower_iso [(0x505000005050000050500000505,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C27.low

namespace C62
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤8) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => chunk4_0 i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk5_0 chunk5_8) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk6_0 (range_split chunk6_8 chunk6_16)) i (Nat.zero_le _) hi
  · exact fun i hi => chunk7_0 i (Nat.zero_le _) hi
  · exact fun i hi => chunk8_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 9 := replay tab d target roots pairs 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C33.low⟩
    · exact ⟨(by decide +kernel),C42.low⟩
    · exact ⟨(by decide +kernel),C49.low⟩
    · exact ⟨(by decide +kernel),sh23⟩
    · exact ⟨(by decide +kernel),C55.low⟩
    · exact ⟨(by decide +kernel),C27.low⟩
    · exact ⟨(by decide +kernel),sh24⟩
    · exact ⟨(by decide +kernel),C53.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 4 5 = true) s lo (by omega))
end C62

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C63.low : Lower true 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0e0a 7 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C34.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C64.low : Lower true 0x33333333333333333333333333333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x33323322333233223332332032322220 9 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33333333000000003333333300000000,8,40)] (by decide +kernel) (by decide +kernel) C44.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C65.low : Lower true 0x33333333333333333333333333333333 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x33333333333333333333333333323320 7 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33333333333333330000000000000000,0,64)] (by decide +kernel) (by decide +kernel) C36.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem C66.low : Lower true 0x55555555555555555555555555555555 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x55545544555455445554554454504400 7 := lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x55555555555555550000000000000000,2,66)] (by decide +kernel) (by decide +kernel) C37.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh25 : Lower true 0xffff0000ffff0000ffff0000ffff0000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xfffe0000fffe0000fffe0000fefa0000 7 := lower_iso [(0xffff0000ffff0000ffff0000ffff,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C60.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh26 : Lower true 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0e0a0 7 := lower_iso [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C63.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh27 : Lower true 0xcccccccccccccccccccccccccccccccc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xccccccccccccccccccccccccccc8cc80 7 := lower_iso [(0x33333333333333333333333333333333,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C65.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh28 : Lower true 0xff00ff0000000000ff00ff00000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0xfe00ee0000000000fe00ec00000000 6 := lower_iso [(0xff00ff0000000000ff00ff,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C41.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh29 : Lower true 0x33333333000000003333333300000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x33323322000000003332332000000000 6 := lower_iso [(0x333333330000000033333333,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C45.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh30 : Lower true 0x55550000555500005555000055550000 [0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x55540000555400005554000054500000 6 := lower_iso [(0x5555000055550000555500005555,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C52.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh31 : Lower true 0xcc00cc00cc00cc00cc00cc00cc00cc [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xcc00cc00cc00cc00cc00cc00c80080 6 := lower_iso [(0x330033003300330033003300330033,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C54.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh32 : Lower true 0x50505050505050505050505050505050 [0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0x50505040505050405050504050504000 6 := lower_iso [(0x5050505050505050505050505050505,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C56.low

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sh33 : Lower true 0x330033000000000033003300000000 [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] 0x320022000000000032002000000000 5 := lower_iso [(0x3300330000000000330033,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) C22.low

namespace C67
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allCells (s) (hs : s≤11) : ∀ i < tab.n s, test s i = true := by
  interval_cases s
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (Nat.not_lt_zero i hi).elim
  · exact fun i hi => (range_split (range_split chunk5_0 chunk5_8) (range_split chunk5_16 chunk5_24)) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split (range_split (range_split chunk6_0 chunk6_8) (range_split chunk6_16 chunk6_24)) (range_split (range_split chunk6_32 chunk6_40) (range_split chunk6_48 chunk6_56))) (range_split (range_split (range_split chunk6_64 chunk6_72) (range_split chunk6_80 chunk6_88)) (range_split (range_split chunk6_96 chunk6_104) (range_split chunk6_112 (range_split chunk6_120 chunk6_128))))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split (range_split (range_split (range_split chunk7_0 chunk7_8) (range_split chunk7_16 (range_split chunk7_24 chunk7_32))) (range_split (range_split chunk7_40 chunk7_48) (range_split chunk7_56 (range_split chunk7_64 chunk7_72)))) (range_split (range_split (range_split chunk7_80 chunk7_88) (range_split chunk7_96 (range_split chunk7_104 chunk7_112))) (range_split (range_split chunk7_120 (range_split chunk7_128 chunk7_136)) (range_split chunk7_144 (range_split chunk7_152 chunk7_160))))) (range_split (range_split (range_split (range_split chunk7_168 chunk7_176) (range_split chunk7_184 (range_split chunk7_192 chunk7_200))) (range_split (range_split chunk7_208 chunk7_216) (range_split chunk7_224 (range_split chunk7_232 chunk7_240)))) (range_split (range_split (range_split chunk7_248 chunk7_256) (range_split chunk7_264 (range_split chunk7_272 chunk7_280))) (range_split (range_split chunk7_288 (range_split chunk7_296 chunk7_304)) (range_split chunk7_312 (range_split chunk7_320 chunk7_328)))))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split (range_split (range_split (range_split chunk8_0 (range_split chunk8_8 chunk8_16)) (range_split (range_split chunk8_24 chunk8_32) (range_split chunk8_40 chunk8_48))) (range_split (range_split chunk8_56 (range_split chunk8_64 chunk8_72)) (range_split (range_split chunk8_80 chunk8_88) (range_split chunk8_96 chunk8_104)))) (range_split (range_split (range_split chunk8_112 (range_split chunk8_120 chunk8_128)) (range_split (range_split chunk8_136 chunk8_144) (range_split chunk8_152 chunk8_160))) (range_split (range_split (range_split chunk8_168 chunk8_176) (range_split chunk8_184 chunk8_192)) (range_split (range_split chunk8_200 chunk8_208) (range_split chunk8_216 chunk8_224))))) (range_split (range_split (range_split (range_split chunk8_232 (range_split chunk8_240 chunk8_248)) (range_split (range_split chunk8_256 chunk8_264) (range_split chunk8_272 chunk8_280))) (range_split (range_split chunk8_288 (range_split chunk8_296 chunk8_304)) (range_split (range_split chunk8_312 chunk8_320) (range_split chunk8_328 chunk8_336)))) (range_split (range_split (range_split chunk8_344 (range_split chunk8_352 chunk8_360)) (range_split (range_split chunk8_368 chunk8_376) (range_split chunk8_384 chunk8_392))) (range_split (range_split (range_split chunk8_400 chunk8_408) (range_split chunk8_416 chunk8_424)) (range_split (range_split chunk8_432 chunk8_440) (range_split chunk8_448 chunk8_456)))))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split (range_split (range_split (range_split chunk9_0 (range_split chunk9_8 chunk9_16)) (range_split chunk9_24 (range_split chunk9_32 chunk9_40))) (range_split (range_split chunk9_48 (range_split chunk9_56 chunk9_64)) (range_split (range_split chunk9_72 chunk9_80) (range_split chunk9_88 chunk9_96)))) (range_split (range_split (range_split chunk9_104 (range_split chunk9_112 chunk9_120)) (range_split (range_split chunk9_128 chunk9_136) (range_split chunk9_144 chunk9_152))) (range_split (range_split chunk9_160 (range_split chunk9_168 chunk9_176)) (range_split (range_split chunk9_184 chunk9_192) (range_split chunk9_200 chunk9_208))))) i (Nat.zero_le _) hi
  · exact fun i hi => (range_split chunk10_0 (range_split chunk10_8 chunk10_16)) i (Nat.zero_le _) hi
  · exact fun i hi => chunk11_0 i (Nat.zero_le _) hi
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem low : Lower true d roots target 12 := replay tab d target roots pairs 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
    intro c hc
    simp only [tab,cuts,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(by decide +kernel),C57.low⟩
    · exact ⟨(by decide +kernel),C58.low⟩
    · exact ⟨(by decide +kernel),C59.low⟩
    · exact ⟨(by decide +kernel),C62.low⟩
    · exact ⟨(by decide +kernel),C64.low⟩
    · exact ⟨(by decide +kernel),C44.low⟩
    · exact ⟨(by decide +kernel),C61.low⟩
    · exact ⟨(by decide +kernel),C30.low⟩
    · exact ⟨(by decide +kernel),C33.low⟩
    · exact ⟨(by decide +kernel),C35.low⟩
    · exact ⟨(by decide +kernel),C38.low⟩
    · exact ⟨(by decide +kernel),C40.low⟩
    · exact ⟨(by decide +kernel),C42.low⟩
    · exact ⟨(by decide +kernel),C49.low⟩
    · exact ⟨(by decide +kernel),sh25⟩
    · exact ⟨(by decide +kernel),sh26⟩
    · exact ⟨(by decide +kernel),sh27⟩
    · exact ⟨(by decide +kernel),C66.low⟩
    · exact ⟨(by decide +kernel),sh11⟩
    · exact ⟨(by decide +kernel),C32.low⟩
    · exact ⟨(by decide +kernel),sh12⟩
    · exact ⟨(by decide +kernel),sh13⟩
    · exact ⟨(by decide +kernel),C37.low⟩
    · exact ⟨(by decide +kernel),sh16⟩
    · exact ⟨(by decide +kernel),sh28⟩
    · exact ⟨(by decide +kernel),sh17⟩
    · exact ⟨(by decide +kernel),sh18⟩
    · exact ⟨(by decide +kernel),sh29⟩
    · exact ⟨(by decide +kernel),C47.low⟩
    · exact ⟨(by decide +kernel),sh21⟩
    · exact ⟨(by decide +kernel),sh23⟩
    · exact ⟨(by decide +kernel),C51.low⟩
    · exact ⟨(by decide +kernel),sh30⟩
    · exact ⟨(by decide +kernel),sh31⟩
    · exact ⟨(by decide +kernel),C55.low⟩
    · exact ⟨(by decide +kernel),sh32⟩
    · exact ⟨(by decide +kernel),sh5⟩
    · exact ⟨(by decide +kernel),sh14⟩
    · exact ⟨(by decide +kernel),sh15⟩
    · exact ⟨(by decide +kernel),C22.low⟩
    · exact ⟨(by decide +kernel),sh7⟩
    · exact ⟨(by decide +kernel),sh33⟩
    · exact ⟨(by decide +kernel),C48.low⟩
    · exact ⟨(by decide +kernel),C26.low⟩
    · exact ⟨(by decide +kernel),C27.low⟩
    · exact ⟨(by decide +kernel),sh22⟩
    · exact ⟨(by decide +kernel),sh24⟩
    · exact ⟨(by decide +kernel),C53.low⟩) allCells (fun s lo hi => span_ok (by decide +kernel : span (atRoot tab (roots.map (· &&& d))) 6 6 = true) s lo (by omega))
end C67

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem core : Lower true 0xffffffffffffffffffffffffffffffff [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] 0xfffeffeefffeffeefffeffecfefaeea0 12 := C67.low
end Lower29252

namespace Bridge29252
open GraphKernel29252 Lower26514
abbrev dom : Nat := 2^128-1
def bits (f : Fn 7) := Nat.ofBits (n:=128) (fun r => f (fun i => r.val.testBit i.val))
private theorem db (i : Nat) : dom.testBit i=decide (i<128) := Nat.testBit_two_pow_sub_one ..
private theorem meet (a b : Fn 7) : bits (fun x => a x && b x)=opD dom 0 (bits a) (bits b) := by
  change bits _ = ((bits a &&& bits b) &&& dom)
  apply Nat.eq_of_testBit_eq; intro i; simp only [bits,Nat.testBit_ofBits,Nat.testBit_and,db]; by_cases h : i<128 <;> simp [h]
private theorem flip (a : Fn 7) : bits (fun x => !(a x))=negD dom (bits a) := by
  apply Nat.eq_of_testBit_eq; intro i; by_cases h : i<128
  · have hh : i<256 := by omega
    simp only [bits,negD,Nat.testBit_ofBits,Nat.testBit_and,Nat.testBit_xor,db,mask256_bit]; simp [h,hh]
  · simp only [bits,negD,Nat.testBit_ofBits,Nat.testBit_and,db]; simp [h]
private theorem reach {v : List (Fn 7)} {k t} (h : Lower26514.Run v k t) (roots : List Nat) {p bank} (hr : NatReach true dom roots p bank) (av : ∀ f∈v, Avail true dom bank (bits f)) : ∃ q b, q≤p+k ∧ NatReach true dom roots q b ∧ Avail true dom b (bits t) := by
  induction h generalizing p bank with
  | stop hh => exact ⟨p,bank,by omega,hr,av _ hh⟩
  | @step v k t a b ha hb tail ih =>
    let z := opD dom 0 (bits a) (bits b)
    have next : NatReach true dom roots (p+1) (z::bank) := ⟨bank,bits a,bits b,0,by decide,rfl,hr,av _ ha,av _ hb⟩
    have hv : Avail true dom (z::bank) z := Or.inr (Or.inl ⟨z,List.mem_cons_self,rfl⟩)
    obtain ⟨q,w,sz,hr',av'⟩ := ih next (by
      intro f hf; rcases List.mem_append.mp hf with h|h
      · exact avail_cons _ _ (av f h)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl
        · rw [meet]; exact hv
        · rw [flip,meet]; exact avail_neg (by decide) hv)
    exact ⟨q,w,by omega,hr',av'⟩
def cols : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
abbrev target : Nat := 0xfffeffeefffeffeefffeffecfefaeea0
private def drop2 : Fin 8 → Coord26514.Code 7 := ![some 0,some 1,none,some 2,some 3,some 4,some 5,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem liftBound (hc : Lower true dom cols target 12) (k) (h : Lower26514.Run Lower26514.start k Integration29252.graph) : 13≤k := by
  have dep : ¬Coord26514.stable drop2 Integration29252.graph := by unfold Coord26514.stable; decide +kernel
  have nc : ¬Pin26514.Const (Integration29252.graph ∘ Coord26514.pin drop2 false) := by unfold Pin26514.Const; decide +kernel
  obtain ⟨l,hl,run⟩ := Coord26514.one drop2 false _ h dep nc
  have av : ∀ f ∈ (@Lower26514.start 7), Avail true dom cols (bits f) := by
    intro f hf; rcases List.mem_append.mp hf with h|h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl <;> apply (availB_iff ..).mp <;> decide +kernel
    · obtain ⟨ls,hm,h⟩ := List.mem_flatten.mp h; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl <;> apply (availB_iff ..).mp <;> revert i <;> decide +kernel
  obtain ⟨q,b,le,hr,ok⟩ := reach run cols (p:=0) (bank:=cols) rfl av
  have e : bits (Integration29252.graph ∘ Coord26514.pin drop2 false)=target := by decide +kernel
  rw [e] at ok; have := hc q b hr ok; omega
end Bridge29252

namespace FinalBridge29252
theorem finish (hc : GraphKernel29252.Lower true Bridge29252.dom Bridge29252.cols Bridge29252.target 12) :
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply Integration29252.finish Witness29252.mono Witness29252.computes
  intro k h; rw [Witness29252.size]; have := Bridge29252.liftBound hc k h; omega
end FinalBridge29252

end PEqualNP.Outside.L_meta_29252_aux
open PEqualNP.Outside.L_meta_29252_aux
theorem PEqualNP.Outside.L_meta_29252 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := FinalBridge29252.finish Lower29252.core
