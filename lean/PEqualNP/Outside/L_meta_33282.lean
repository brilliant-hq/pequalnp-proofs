import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

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
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_zero]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
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
def Good (m a : ℕ) := ∀ i < m, a.testBit i ≠ a.testBit (m+i)
def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0,S => ∃ a, S={a} ∧ Good m a ∧ a≠0
  | k+1,S => ∃ U a b d, S=insert a (insert b U) ∧ d<4 ∧ a≠0 ∧ b≠0 ∧ a≠b ∧
      combine d a b ∉ insert a (insert b U) ∧ Live m k (insert (combine d a b) U)
lemma Live.done {m a} (hg : Good m a) (nz : a≠0) : Live m 0 {a} := ⟨a,rfl,hg,nz⟩
lemma Live.step {m k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
    (fresh : combine d a b ∉ insert a (insert b U)) (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := ⟨U,a,b,d,rfl,hd,ha,hb,diff,fresh,next⟩
lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; simpa using hn
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; simp
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i < m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ne,fresh,tail⟩ := h
    have ih := hyp tail
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

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

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2]
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i < m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i < m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]






def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i < m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i < m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
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

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero => obtain ⟨a,rfl,hg,hn⟩ := h; exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | succ n =>
      obtain ⟨U,a,b,d,rfl,hd,_,_,ab,fresh,tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))




def Projection (m h : ℕ) := { f : ℕ → ℕ // (∀ d a b, d<4 → f (combine d a b)=combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0<h }
abbrev Projection.toFun {m h} (p : Projection m h) := p.val
lemma Projection.combineEq {m h} (p : Projection m h) : ∀ d a b, d<4 → p.toFun (combine d a b)=combine d (p.toFun a) (p.toFun b) := p.property.1
lemma Projection.good {m h} (p : Projection m h) : ∀ a, Good m a → Good h (p.toFun a) := p.property.2.1
lemma Projection.someRow {m h} (p : Projection m h) : 0<h := p.property.2.2
def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
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

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    obtain ⟨a,rfl,hg,hn⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k hyp =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fz,tail⟩ := live
    have ih := hyp tail
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩





lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i < m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i < m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i < m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i < m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i < m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i < m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j < m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r < m) : Projection m m := ⟨slice m q r, slice_hom m q r, by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  , by omega⟩

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i < m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

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
    simp [needed,yes] at no
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

def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases k with
  | zero => obtain ⟨a,rfl,hg,hn⟩ := live; exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | succ k =>
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fz,tail⟩ := live
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩
def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf

abbrev FloorData := ℕ × ℕ × List ℕ
abbrev FloorData.pairMask (s : FloorData) := s.1
abbrev FloorData.lower (s : FloorData) := s.2.1
abbrev FloorData.basis (s : FloorData) := s.2.2
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0 < m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r < m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def essentialSet (m : ℕ) (v : List ℕ) := v.all fun x => !(enough m (cover m (v.filter (fun y => y != x))))
lemma essential_eq {m k S v} (live : Live m k S) (sub : ∀ a∈S, a∈v) (ess : essentialSet m v=true) : S=v.toFinset := by
  ext a
  constructor
  · exact fun h => List.mem_toFinset.mpr (sub a h)
  intro ha
  by_contra bad
  have contra := List.all_eq_true.mp ess a (List.mem_toFinset.mp ha)
  have cv := enoughSup live (v.filter (fun y => y != a)) (by
    intro x hx; have ne : x≠a := by rintro rfl;exact bad hx
    simp [ne,sub x hx])
  simp [cv] at contra
lemma floorEx {m : ℕ} {s : FloorData} (ex : Excluded m (s.lower-1) s.basis)
    (ess : essentialSet m s.basis=true) (nd : s.basis.Nodup) : Floor m s := by
  intro k ⟨j,S,lim,live,sub⟩
  by_contra bad
  have raw (a) (ha : a∈S) : a∈s.basis := (List.mem_cons.mp (sub a ha)).resolve_left (liveNonzero live a ha)
  have eq := essential_eq live raw ess
  exact ex ⟨j,by omega,eq ▸ live,nd⟩
abbrev Shelf (m : ℕ) := ℕ → {s : FloorData // Floor m s}
def lookupRows (go : ℕ → List ℕ → Bool) : List ℕ → List (List ℕ) → Bool
  | _,[] => false
  | code,v::vs => go (code.headD 0) v || lookupRows go code.tail vs
lemma lookup_ok {go : ℕ→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (tags : List ℕ) : lookupRows go tags vs=true := by
  induction vs generalizing tags with
  | nil => simp at mem
  | cons x xs ih =>
    rw [lookupRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _)
def audit (m : ℕ) (db : Shelf m) (branches : ℕ → List ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,g,v => if g=0 then search m (k+1) v else if g%2=1 then
      !(contradictsFloor m (k+1) v (db ((g >>> 1) % 256)).val (g >>> 9))
    else terminal m v || lookupRows (audit m db branches k) (branches (g/2)) (successors m k v)
lemma audit_ok {m : ℕ} (pos : 0 < m) (db : Shelf m) (branches : ℕ → List ℕ)
    (k : ℕ) (v : List ℕ) (ok : feasible m k v) (g : ℕ) : audit m db branches k g v=true := by
  induction k generalizing g v with
  | zero => obtain ⟨j,lim,h,nd⟩ := ok; exact complete _ 0 h lim _ rfl nd
  | succ k ih =>
    rw [audit];split
    · obtain ⟨j,lim,h,nd⟩ := ok;exact complete _ _ h lim _ rfl nd
    split
    · simp [floor_consistent pos ok _ (db _).property]
    rw [Bool.or_eq_true]
    rcases move ok with t|⟨w,hw,next⟩
    · exact Or.inl t
    · exact Or.inr (lookup_ok hw (fun i => ih w next i) _)
lemma audit_off {m k v g db branches} (p : 0 < m) (e : audit m db branches k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audit_ok p db branches k v h g))
open PEqualNP.CircuitLowerBounds


def edges : List ℕ := [0,3,1,4,0,5,3,5,0,6,1,6,2,6,4,6,0,7,1,7,2,7,3,7,4,7,6,7]

def target (xs : List Bool) : Bool := decide (∃ i < edges.length / 2,
  xs.getD (edges.getD (2 * i) 0) false = true ∧ xs.getD (edges.getD (2 * i + 1) 0) false = true)

def gs : List Gate := [⟨.or,[6,7]⟩,⟨.or,[1,2]⟩,⟨.or,[9,4]⟩,⟨.and,[8,10]⟩,⟨.or,[5,7]⟩,⟨.or,[0,3]⟩,⟨.and,[12,13]⟩,⟨.and,[4,1]⟩,⟨.or,[0,7]⟩,⟨.or,[3,6]⟩,⟨.and,[16,17]⟩,⟨.or,[11,14]⟩,⟨.or,[19,15]⟩,⟨.or,[20,18]⟩]

theorem count : gs.length = 14 := rfl

theorem basis (g : Gate) (hg : g ∈ gs) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [gs] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
theorem evalBits : ∀ a b c d e f g h : Bool,
    Circuit.eval ⟨gs, 21⟩ [a,b,c,d,e,f,g,h] = target [a,b,c,d,e,f,g,h] := by
  decide +kernel

theorem computes (x : Fin 8 → Bool) : Circuit.eval ⟨gs, 21⟩ (List.ofFn x) = target (List.ofFn x) :=
  evalBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

def inputs : List ℕ := [0x4008200040004022185088100a10e004000080410614108054107010180a404002839409a890a4c006020847000e010e0f30c780c380f01f80e00c1c1e3831e01c1fe01fc383c1fe0e007fffe0ffc01fff,0x1000209000200c0ca0809001a808c7840200601940802400194187822802a41ea024b090ca0323ac2803800307800700e0ff0c0f800fc00ffe00700f01fe1c03e001fe1ffe03c03fe0ff0007c01ff07ffff00,0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x801875002100042001ca0011323c02005000aa4003ea801235a812101a280008c88e0002ad201231b01c00c3f8003800ff000ff0000ffff00007800ffe001ffc0001ffe00003ffc000fffff8001fff8001fff,0x4000c8000034ca000016d263c0010000834ca0000013349878000000457b54ac00048012331cc5c00c0e000fc00003fff00000ffffff000000007fff000001ffffffe00000003ffffff000000001ffffffe000,0x1f7ea0000146fadb5ad40000a000801420afad54b5a80000240000242064c673131370c7c00000600000ffff0000003ffffffff000000000000007ffffffffe000000000000003ffffffffffffffe0000000000,0x29a4d15624700000000000000000200000c9319f26324c12382632383800000000018002000000000101ffffffffffc00000000000000000000007fffffffffffffffffffffffc0000000000000000000000000,0x124b02084984931393181048c044c1183000000000000000000000000000000000020004000000000000fffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000]
def seeds : List Wire := inputs.map (fun a => (false,a))
def sample (j : ℕ) (i : Fin 8) : Bool := (inputs.getD i.val 0).testBit j
set_option maxRecDepth 8000 in
lemma listed (j : ℕ) : seeds.map (read j)=List.ofFn (sample j) := by
  let b := fun n => (inputs.getD n 0).testBit j
  change [false != b 0,false != b 1,false != b 2,false != b 3,false != b 4,false != b 5,false != b 6,false != b 7] = [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7]
  simp
set_option maxRecDepth 8000 in
lemma labels : ∀ j : Fin 333, target (List.ofFn (sample j.val))=true ∧ target (List.ofFn (sample (333+j.val)))=false := by decide +kernel
theorem trace (C : Circuit) (fan : ∀ g∈C.gates, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target (List.ofFn x)) :
    ∃ k≤C.gates.countP counted, Live 333 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have good : Good 333 out.2 := by
    intro i hi same
    let j : Fin 333 := ⟨i,hi⟩
    have diff : read i out=read (333+i) out := by simp [read,same]
    have p := ev i;have n := ev (333+i)
    rw [listed,result,(labels j).1] at p
    rw [listed,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  have ess : essentialSet 333 inputs=true := by decide +kernel
  exact ⟨k,limit,essential_eq live stays ess ▸ live⟩
def row0 : List ℕ := []
def row1 : List ℕ := [111,0,121]
def row2 : List ℕ := [111,23,23,111,121,11,11,121,75879,41,11,40023,75367,33,11,42083,74855,55,11,74855,74855,29,11,74855,115,2,115,0,11,23]
def row3 : List ℕ := [123,40023,41,75367,42593,42595,74855]
def row4 : List ℕ := [111]
def row5 : List ℕ := [115]
def row6 : List ℕ := [41,74855,111,23,41,111,121,11,41,121,40023,43053,123,103,123,103,43107,43107,11,43107,123,75879,123,75879,75879,75879,11,75879,123,75879,123,75879,75879,75879,11,75879,115,8,115,41,10,40023,11,23]
def row7 : List ℕ := [115,0,123]
def row8 : List ℕ := [123,11]
def row9 : List ℕ := [111,0,123]
def row10 : List ℕ := [43053,43053]
def row11 : List ℕ := [123]
def row12 : List ℕ := [111,14,0,111,77927,41,40015,40015,77415,16,11,44131,76903,45,11,76903,76903,16,11,76903,115,18,115,0,123,123,11,11,123,20,11,22,11,40015]
def row13 : List ℕ := [121,40015,41,77415,44641,44643,76903,40023]
def row14 : List ℕ := [41,76903,111,0,41,111,123,11,41,123,40015,40015,145531,103,143995,103,45155,45155,11,45155,47227,77927,45691,77927,77927,77927,11,77927,79995,77927,78459,77927,77927,77927,11,77927,115,8,115,41]
def row15 : List ℕ := [40053,40053,448830581,40053,38001,11,40021,11,37969,123,99,123,99,123,123,103,123,103,123,11,11,1838426397815,97,11,1838426397815,11,1804058270829]
def row16 : List ℕ := [11,37969,163688567,38001,11,40023,123,103,123,103,123,123,40023,123,41,123,11,11,40023,448830583,448830583,97,11,448830583,40053,40053,448830581,40053,37969,30,448830581,40023,448830581,448830581,448831095,99,11,448830581,11,440441965]
def row17 : List ℕ := [40053,40053,457219189,40053,38001,99,121,99,121,103,121,103,121,11,11,1872794524791,97,11,1872794524791,1254302454875,1254302454875,11,40015,11,37963]
def row18 : List ℕ := [163690615,38001,40015,448830573,121,103,121,103,121,40015,121,41,121,11,11,40015,457219191,457219191,97,11,457219191,40053,40053,457219189,40053,37963,34,457219189,40015,457219189,457219189,457219703,99,11,457219189,306222171,306222171,11,37963,11,40015]
def row19 : List ℕ := [11,40023,40055,40055,40045,40045,11,40023,123,97,123,97,123,40023,123,41,123,11,11,40023,180393073,41079,103,11,180393073,40023,180395125,40567,99,180395125,180395125,180395125,180395125,180393073,11,180395125,37979,37979,11,40045]
def row20 : List ℕ := [73,73,121,121,11,11,591437943,109671,11,2422550336625,591437431,109667,2422550338677,2422550338677,2422550338677,2422550338677,2422550336625,11,2422550338677,37979,37979]
def row21 : List ℕ := [40055,40055,40,40015,40045,40045,40045,121,97,121,97,121,40015,121,41,121,11,11,40015,188781681,41079,103,11,188781681,40015,188783733,40567,99,188783733,188783733,188783733,188783733,188781681,11,188783733,37979,37979,37979,37979,11,11,11,40015]
def row22 : List ℕ := [11,37969,40053,40053,448830581,40053,38001,11,40021,123,103,123,103,123,123,99,123,99,123,11,11,1838426397815,97,11,1838426397815,11,1804058270829]
def row23 : List ℕ := [11,40021,163623031,40053,11,40023,123,99,123,99,123,123,40023,123,41,123,11,11,38001,38001,314610801,38001,40021,44,314610801,40023,314610801,314610801,180396151,103,11,314610801,40023,180395127,180395127,97,11,180395127,11,172006509]
def row24 : List ℕ := [40053,40053,457219189,40053,38001,103,121,103,121,99,121,99,121,11,11,1872794524791,97,11,1872794524791,1254302454875,1254302454875,11,37963,11,40015]
def row25 : List ℕ := [163625079,40053,40015,163621997,121,99,121,99,121,40015,121,41,121,11,11,38001,38001,322999409,38001,40015,48,322999409,40015,322999409,322999409,188784759,103,11,322999409,40015,188783735,188783735,97,11,188783735,172004443,172004443,11,40015,11,40015]
def row26 : List ℕ := [0,144499,0,177275]
def row27 : List ℕ := [121,121,73,73,11,11,591437943,109671,11,2422550336625,591437431,109667,2422550338677,2422550338677,2422550338677,2422550338677,2422550336625,11,2422550338677,37979,37979]
def row28 : List ℕ := [595631223,40045,73,52,0,73,121,40015,40015,121,177275,11,11,177275,40015,591434865,591437943,109671,11,591434865,54,591436919,40015,591436919,591436919,591436919,109665,11,591436919,40015,591436917,591437431,109667,591436917,591436917,591436917,591436917,591434865,11,591436917,37979,37979,144499,37979,144499,37979]
def row29 : List ℕ := [111,40045,40045,40045,40045,40045,111,40045,123,40023,4,6,12,41,123,40023,121,40015,24,26,28,41,121,40015,41079,103,38001,38001,38001,38001,38001,38001,32,38001,38001,38001,38001,38001,36,38001,38001,38001,38001,40055,97,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,38,40055,40055,40055,40055,40055,42,40055,40055,40055,40055,40567,99,40053,40053,40053,40053,40053,40055,40053,40053,38001,40053,40053,40053,40053,40053,40053,40053,40053,40053,40053,46,40053,40053,40053,40053,40053,50,40053,40053,40053,40053,115,37989,37979,37979,115,37989,37979,37979,38001,38001,38001,38001,40045,40045,40045,40045,37989,37979,37989,37979,37989,37979,37989,37979,40045,40045,40045,40045,40023,11,40023,40015,40045,56,40045,40045,40045,40045]
def row30 : List ℕ := [172004463,109,109,172004463,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,155232379,119,119,38001,109,38001,38001,38001,38001,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,117,117,40053,40053,40053,117,40053,113,38001,38001,113,38001,40053,103,38001,113,38001,163615859,103,103,163615859,172004463,109,109,172004463,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,117,40053,40053,40053,117,40053,99,40053,40053,40053,40053,40053,40053,40053,40053,38001,40053,172005499,119,119,40053,91,40053,40053,40053,40053,40053,109,40053,40053,40053,40053,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,163615859,99,163615859,99,163615859,91,38001,163615859,38001,38001,163615859,109,163615859,172004463,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004475,172004475,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473]
def row31 : List ℕ := [115,38003,91,103,103,103,115,38003,113,38001,58,103,103,103,113,38001,111,37999,109,109,109,109,111,37999,123,38011,38011,38011,38011,38011,123,38011,121,38009,38009,38009,38009,38009,121,38009,38523,117,119,119,119,119,119,119,117,119,119,119,119,119,119,60,119,119,119,119,119,119,119,119,38011,38011,38011,38011,38011,38011,38009,38009,38009,38009,38009,38009,39035,119,119,117,91,117,117,117,117,117,117,117,117,38001,117,117,109,117,117,117,117,38011,38011,38011,38011,38011,38011,38009,38009,38009,38009,38009,38009,38003,91,38003,38001,38003,109,38003,37999,38011,38011,38011,38011,38009,38009,38009,38009,38001,109,38001,37999,38011,38011,38011,38011,38009,38009,38009,38009,38011,38011,38011,38011,38011,38011,38011,38011,38009,38009,38009,38009,38009,38009]
def row32 : List ℕ := [117,117,40053,40053,40053,117,40053,113,38001,38001,113,38001,40053,103,38001,113,38001,163615859,103,103,163615859,172004463,109,109,172004463,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,172005499,119,119,117,40053,40053,40053,117,40053,99,40053,40053,40053,40053,40053,40053,40053,40053,38001,40053,40053,91,40053,40053,40053,40053,40053,109,40053,40053,40053,40053,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,172004463,109,109,172004463,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,155232379,119,119,38001,109,38001,38001,38001,38001,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473,163615859,99,163615859,99,163615859,91,38001,163615859,38001,38001,163615859,109,163615859,172004463,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004475,172004475,172004475,172004475,172004475,172004475,172004475,172004475,172004473,172004473,172004473,172004473,172004473,172004473]
def row33 : List ℕ := [111,23,23,111,121,11,11,121,75879,41,11,40023,74855,29,11,74855,74855,55,11,74855,75367,33,11,42083,115,2,115,0,11,23]
def row34 : List ℕ := [123,40023,41,42595,74855,42593,75367]
def row35 : List ℕ := [41,74855,111,23,41,111,121,11,41,121,40023,43053,123,75879,123,75879,75879,75879,11,75879,123,75879,123,75879,75879,75879,11,75879,123,103,123,103,43107,43107,11,43107,115,8,115,41,10,40023,11,23]
def row36 : List ℕ := [111,14,0,111,77927,41,40015,40015,76903,16,11,76903,76903,45,11,76903,77415,16,11,44131,115,18,115,0,123,123,11,11,123,20,11,22,11,40015]
def row37 : List ℕ := [121,40015,41,44643,76903,44641,77415,40023]
def row38 : List ℕ := [41,76903,111,0,41,111,123,11,41,123,40015,40015,79995,77927,78459,77927,77927,77927,11,77927,47227,77927,45691,77927,77927,77927,11,77927,145531,103,143995,103,45155,45155,11,45155,115,8,115,41]
def row39 : List ℕ := [11,40021,163623031,40053,11,40023,123,99,123,99,123,123,40023,123,41,123,11,11,40023,180395127,180395127,97,11,180395127,38001,38001,314610801,38001,40021,44,314610801,40023,314610801,314610801,180396151,103,11,314610801,11,172006509]
def row40 : List ℕ := [163625079,40053,40015,163621997,121,99,121,99,121,40015,121,41,121,11,11,40015,188783735,188783735,97,11,188783735,38001,38001,322999409,38001,40015,48,322999409,40015,322999409,322999409,188784759,103,11,322999409,172004443,172004443,11,40015,11,40015]
def row41 : List ℕ := [11,40023,40055,40055,40045,40045,11,40023,123,97,123,97,123,40023,123,41,123,11,11,40023,180395125,40567,99,180395125,180395125,180395125,180395125,180393073,11,180395125,40023,180393073,41079,103,11,180393073,37979,37979,11,40045]
def row42 : List ℕ := [73,73,121,121,11,11,591437431,109667,2422550338677,2422550338677,2422550338677,2422550338677,2422550336625,11,2422550338677,591437943,109671,11,2422550336625,37979,37979]
def row43 : List ℕ := [40055,40055,84,40015,40045,40045,40045,121,97,121,97,121,40015,121,41,121,11,11,40015,188783733,40567,99,188783733,188783733,188783733,188783733,188781681,11,188783733,40015,188781681,41079,103,11,188781681,37979,37979,37979,37979,11,11,11,40015]
def row44 : List ℕ := [11,37969,163688567,38001,11,40023,123,103,123,103,123,123,40023,123,41,123,11,11,40053,40053,448830581,40053,37969,30,448830581,40023,448830581,448830581,448831095,99,11,448830581,40023,448830583,448830583,97,11,448830583,11,440441965]
def row45 : List ℕ := [163690615,38001,40015,448830573,121,103,121,103,121,40015,121,41,121,11,11,40053,40053,457219189,40053,37963,34,457219189,40015,457219189,457219189,457219703,99,11,457219189,40015,457219191,457219191,97,11,457219191,306222171,306222171,11,37963,11,40015]
def row46 : List ℕ := [121,121,73,73,11,11,591437431,109667,2422550338677,2422550338677,2422550338677,2422550338677,2422550336625,11,2422550338677,591437943,109671,11,2422550336625,37979,37979]
def row47 : List ℕ := [595631223,40045,73,52,0,73,121,40015,40015,121,177275,11,11,177275,40015,591436917,591437431,109667,591436917,591436917,591436917,591436917,591434865,11,591436917,92,591436919,40015,591436919,591436919,591436919,109665,11,591436919,40015,591434865,591437943,109671,11,591434865,37979,37979,144499,37979,144499,37979]
def row48 : List ℕ := [111,40045,40045,40045,40045,40045,111,40045,123,40023,66,68,70,41,123,40023,121,40015,72,74,76,41,121,40015,40567,99,40053,40053,40053,40053,40053,40055,40053,40053,38001,40053,40053,40053,40053,40053,40053,40053,40053,40053,40053,78,40053,40053,40053,40053,40053,80,40053,40053,40053,40053,40055,97,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,82,40055,40055,40055,40055,40055,86,40055,40055,40055,40055,41079,103,38001,38001,38001,38001,38001,38001,88,38001,38001,38001,38001,38001,90,38001,38001,38001,38001,115,37989,37979,37979,115,37989,37979,37979,38001,38001,38001,38001,40045,40045,40045,40045,37989,37979,37989,37979,37989,37979,37989,37979,40045,40045,40045,40045,40023,11,40023,40015,40045,94,40045,40045,40045,40045]
def row49 : List ℕ := [111,42095,109,109,109,109,111,42095,123,42107,42107,42107,42107,42107,123,42107,121,42105,42105,42105,42105,42105,121,42105,42619,113,119,119,119,119,119,119,113,119,119,64,119,119,119,119,119,119,119,119,119,119,119,119,42107,42107,42107,42107,42107,42107,42105,42105,42105,42105,42105,42105,43131,119,119,113,109,113,113,113,113,42107,42107,42107,42107,42107,42107,42105,42105,42105,42105,42105,42105,117,40053,96,99,117,40053,99,99,40053,40053,113,40053,40053,113,40053,91,40053,40051,40053,109,40053,42095,42107,42107,42107,42107,42105,42105,42105,42105,115,40051,91,99,115,40051,99,99,40051,91,113,40051,113,113,40051,109,40051,42095,42107,42107,42107,42107,42105,42105,42105,42105,42107,42107,42107,42107,42107,42107,42107,42107,42105,42105,42105,42105,42105,42105]
def row50 : List ℕ := [111,35,35,111,121,11,11,121,75877,67,11,72789,75365,31,11,74849,74853,27,11,74853,74853,55,11,74853,119,2,119,0,11,35]
def row51 : List ℕ := [111,35,35,111,77925,67,72783,72783,77413,21,76901,19,76901,45,11,76901,119,18,119,0,123,11,123,11]
def row52 : List ℕ := [95,121,95,121,101,121,101,121,11,67,457252469,97,11,1872928775283,1254302454875,1254302454875]
def row53 : List ℕ := [297908341,72817,72783,448863339,121,101,121,101,121,72783,121,67,121,11,67,104,457251957,72783,457251957,457251957,457251957,95,72783,457251955,457252469,97,11,457251955,306222171,306222171,11,72783]
def row54 : List ℕ := [101,121,101,121,95,121,95,121,11,67,457252469,97,11,1872928775283,1254302454875,1254302454875]
def row55 : List ℕ := [72821,72821,72783,297872491,121,95,121,95,121,72783,121,67,121,11,67,108,323034225,72783,323034225,323034225,73845,101,72783,323034227,73333,97,11,323034227,172004443,172004443,11,72783]
def row56 : List ℕ := [11,72787,297873525,72819,72811,72811,11,72789,123,97,123,97,123,72789,123,67,123,109679,109679,11,67,314646645,101,11,448863345,314645621,95,11,314645621,37979,37979,37979,37979,11,72811]
def row57 : List ℕ := [73,73,121,121,11,74819,2422684590197,109669,2422684589173,109663,37979,37979]
def row58 : List ℕ := [297875573,72819,114,72783,72811,72811,72811,121,97,121,97,121,72783,121,67,121,11,67,72783,457251953,323035253,101,72783,323034229,323034229,95,37979,37979,37979,37979,11,72781]
def row59 : List ℕ := [35]
def row60 : List ℕ := [121,121,73,73,11,74819,2422684590197,109669,2422684589173,109663,37979,37979]
def row61 : List ℕ := [595663989,72811,73,118,74819,73,121,72783,72783,121,177275,11,74819,177275,72783,591469681,591470709,109669,72783,591469685,591469685,109663,120,591469683,72783,591469683,591469683,591470197,109665,11,591469683,37979,37979,144503,37979,144503,37979]
def row62 : List ℕ := [111,72811,72811,72811,72811,72811,111,72811,123,72789,100,67,67,67,123,72789,121,72783,102,67,67,67,121,72783,73845,101,72817,72817,72817,72817,72817,72817,72817,72817,72817,72817,106,72817,72817,72817,72817,72821,95,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,110,72821,72821,72821,72821,73333,97,72819,72819,72821,72819,72819,72819,72819,72819,72819,72819,112,72819,72819,72819,72819,72819,116,72819,72819,72819,72819,119,37991,37979,37979,119,37991,37979,37979,72817,72817,72817,72817,72821,72821,72821,72821,72819,72819,72819,72819,72811,72811,72811,72811,37991,37979,37991,37979,37991,37979,37991,37979,72811,72811,72811,72811,72789,11,72789,72783,72811,122,72811,72811,72811,72811]
def row63 : List ℕ := [440474735,107,107,440474735,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,297904251,115,115,72817,107,72817,72817,72817,72817,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,117,117,72821,72821,72821,117,72821,113,72817,72817,113,72817,72821,101,72817,113,72817,440474735,107,107,440474735,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,117,72821,72821,72821,117,72821,95,72821,72821,72821,72821,72821,440475259,115,72821,72821,107,72821,72821,72821,72821,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,297833591,95,297833591,95,297833591,91,72817,297833591,72817,72817,297833591,101,297833591,101,297833591,91,72821,297833591,72821,72821,297833591,297833581,297833591,440474735,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474747,440474747,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745]
def row64 : List ℕ := [113,72817,124,101,101,101,113,72817,111,72815,107,107,107,107,111,72815,123,72827,72827,72827,72827,72827,123,72827,121,72825,72825,72825,72825,72825,121,72825,73339,115,117,117,117,117,117,117,115,117,117,117,117,117,117,107,117,117,117,117,72827,72827,72827,72827,72825,72825,72825,72825,72825,72825,73851,117,117,115,126,115,115,115,115,115,115,115,115,72827,72827,72827,72827,72827,72827,72825,72825,72825,72825,72825,72825,119,38007,91,101,119,38007,101,101,38007,91,117,38007,117,117,38007,115,38007,115,38007,91,38007,72817,38007,37997,38007,72815,72827,72827,72827,72827,72825,72825,72825,72825,72817,107,72817,72815,72827,72827,72827,72827,72825,72825,72825,72825,72827,72827,72827,72827,72827,72827,72827,72827,72825,72825,72825,72825,72825,72825]
def row65 : List ℕ := [110689,59,109665,109661,110177,45,109665,13,109665,17,119,14,119,0,115,35,115,35,123,23,123,23,23,109661]
def row66 : List ℕ := [440547445,74863,121,107599,109665,121,59,107599,59,121,97,121,109665,97,109665,121,591504501,89,591505013,93,40045,40045,144503,40045,144503,40045,72811,72811,144499,72811,144499,72811,74857,74857,177275,74857,177275,74857]
def row67 : List ℕ := [108661,97,74863,107637,89,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,108149,93,74865,74865,107637,74865,74865,74865,74865,74865,74865,74865,74865,74865,74865,119,40045,40045,40045,119,40045,40045,40045,74863,74863,74863,74863,107637,107637,107637,107637,74865,74865,74865,74865,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,115,72811,72811,72811,115,72811,72811,72811,74863,74863,74863,74863,74865,74865,74865,74865,72811,72811,72811,72811,72811,72811,72811,72811,123,74857,74857,74857,123,74857,74857,74857,74863,74857,74863,74863,74863,74863,74857,74857,74857,74857,121,107599,130,59,121,107599,59,59,74863,132,74863,74863,74863,74863]
def row68 : List ℕ := [111,23,23,111,121,11,11,121,75879,41,11,40023,74855,55,11,74855,74855,29,11,74855,75367,33,11,42083,115,2,115,0,11,23]
def row69 : List ℕ := [123,40023,41,42593,42595,74855,75367]
def row70 : List ℕ := [111,14,0,111,77927,41,40015,40015,76903,45,11,76903,76903,16,11,76903,77415,16,11,44131,115,18,115,0,123,123,11,11,123,20,11,22,11,40015]
def row71 : List ℕ := [121,40015,41,44641,44643,76903,77415,40023]
def row72 : List ℕ := [41,76903,111,0,41,111,123,11,41,123,40015,40015,47227,77927,45691,77927,77927,77927,11,77927,79995,77927,78459,77927,77927,77927,11,77927,145531,103,143995,103,45155,45155,11,45155,115,8,115,41]
def row73 : List ℕ := [595631223,40045,73,52,0,73,121,40015,40015,121,177275,11,11,177275,92,591436919,40015,591436919,591436919,591436919,109665,11,591436919,40015,591436917,591437431,109667,591436917,591436917,591436917,591436917,591434865,11,591436917,40015,591434865,591437943,109671,11,591434865,37979,37979,144499,37979,144499,37979]
def row74 : List ℕ := [111,40045,40045,40045,40045,40045,111,40045,123,40023,136,138,70,41,123,40023,121,40015,140,142,144,41,121,40015,40055,97,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,40055,82,40055,40055,40055,40055,40055,86,40055,40055,40055,40055,40567,99,40053,40053,40053,40053,40053,40055,40053,40053,38001,40053,40053,40053,40053,40053,40053,40053,40053,40053,40053,78,40053,40053,40053,40053,40053,80,40053,40053,40053,40053,41079,103,38001,38001,38001,38001,38001,38001,32,38001,38001,38001,38001,38001,36,38001,38001,38001,38001,115,37989,37979,37979,115,37989,37979,37979,38001,38001,38001,38001,40045,40045,40045,40045,37989,37979,37989,37979,37989,37979,37989,37979,40045,40045,40045,40045,40023,11,40023,40015,40045,146,40045,40045,40045,40045]
def row75 : List ℕ := [111,35,35,111,121,11,11,121,75877,67,11,72789,74853,55,11,74853,74853,27,11,74853,75365,31,11,74849,119,2,119,0,11,35]
def row76 : List ℕ := [111,35,35,111,77925,67,72783,72783,76901,45,11,76901,76901,19,77413,21,119,18,119,0,123,11,123,11]
def row77 : List ℕ := [11,72787,297873525,72819,72811,72811,11,72789,123,97,123,97,123,72789,123,67,123,109679,109679,11,67,314645621,95,11,314645621,314646645,101,11,448863345,37979,37979,37979,37979,11,72811]
def row78 : List ℕ := [73,73,121,121,11,74819,2422684589173,109663,2422684590197,109669,37979,37979]
def row79 : List ℕ := [297875573,72819,156,72783,72811,72811,72811,121,97,121,97,121,72783,121,67,121,11,67,72783,323034229,323034229,95,72783,457251953,323035253,101,37979,37979,37979,37979,11,72781]
def row80 : List ℕ := [72821,72821,72783,297872491,121,95,121,95,121,72783,121,67,121,11,67,72783,323034227,73333,97,11,323034227,108,323034225,72783,323034225,323034225,73845,101,172004443,172004443,11,72783]
def row81 : List ℕ := [297908341,72817,72783,448863339,121,101,121,101,121,72783,121,67,121,11,67,72783,457251955,457252469,97,11,457251955,104,457251957,72783,457251957,457251957,457251957,95,306222171,306222171,11,72783]
def row82 : List ℕ := [121,121,73,73,11,74819,2422684589173,109663,2422684590197,109669,37979,37979]
def row83 : List ℕ := [595663989,72811,73,118,74819,73,121,72783,72783,121,177275,11,74819,177275,164,591469683,72783,591469683,591469683,591470197,109665,11,591469683,72783,591469685,591469685,109663,72783,591469681,591470709,109669,37979,37979,144503,37979,144503,37979]
def row84 : List ℕ := [111,72811,72811,72811,72811,72811,111,72811,123,72789,150,67,67,67,123,72789,121,72783,152,67,67,67,121,72783,73333,97,72819,72819,72821,72819,72819,72819,72819,72819,72819,72819,154,72819,72819,72819,72819,72819,158,72819,72819,72819,72819,72821,95,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,160,72821,72821,72821,72821,73845,101,72817,72817,72817,72817,72817,72817,72817,72817,72817,72817,162,72817,72817,72817,72817,119,37991,37979,37979,119,37991,37979,37979,72819,72819,72819,72819,72821,72821,72821,72821,72817,72817,72817,72817,72811,72811,72811,72811,37991,37979,37991,37979,37991,37979,37991,37979,72811,72811,72811,72811,72789,11,72789,72783,72811,166,72811,72811,72811,72811]
def row85 : List ℕ := [111,74863,134,97,97,97,111,74863,123,74875,74875,74875,74875,74875,123,74875,121,74873,74873,74873,74873,74873,121,74873,75387,113,117,117,117,117,117,117,117,113,117,117,117,117,117,117,117,117,117,74875,74875,74875,74875,74875,74875,74873,74873,74873,74873,74873,74873,75899,117,117,113,113,113,113,74875,74875,74875,74875,74875,74875,74873,74873,74873,74873,74873,74873,119,40055,148,97,119,40055,97,97,40055,117,40055,117,40055,113,40055,113,40055,37979,40055,72819,40055,40045,40055,74863,74875,74875,74875,74875,74873,74873,74873,74873,115,72819,168,97,115,72819,97,97,72819,113,72819,113,72819,72811,72819,74863,74875,74875,74875,74875,74873,74873,74873,74873,74875,74875,74875,74875,74875,74875,74875,74875,74873,74873,74873,74873,74873,74873]
def row86 : List ℕ := [110689,59,109665,109661,109665,17,109665,13,110177,45,119,14,119,0,115,35,115,35,123,23,123,23,23,109661]
def row87 : List ℕ := [440547445,74863,121,107599,109665,121,59,107599,59,121,97,121,109665,97,109665,121,591505013,93,591504501,89,40045,40045,144503,40045,144503,40045,72811,72811,144499,72811,144499,72811,74857,74857,177275,74857,177275,74857]
def row88 : List ℕ := [108149,93,74865,74865,107637,74865,74865,74865,74865,74865,74865,74865,74865,74865,74865,107637,89,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,108661,97,74863,119,40045,40045,40045,119,40045,40045,40045,74865,74865,74865,74865,107637,107637,107637,107637,74863,74863,74863,74863,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,115,72811,72811,72811,115,72811,72811,72811,74865,74865,74865,74865,74863,74863,74863,74863,72811,72811,72811,72811,72811,72811,72811,72811,123,74857,74857,74857,123,74857,74857,74857,74863,74857,74863,74863,74863,74863,74857,74857,74857,74857,121,107599,172,59,121,107599,59,59,74863,174,74863,74863,74863,74863]
def row89 : List ℕ := [314715771,111,74865,113,74865,74865,107637,113,74865,93,74865,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,117,117,107637,107637,107637,117,107637,113,74865,117,107637,107637,107637,117,107637,89,107637,107637,107637,107637,107637,583085691,111,107637,107637,107,107637,107637,107637,107637,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,440444023,109,440444023,109,440444023,109,74865,440444023,74865,74865,440444023,109,440444023,109,440444023,109,107637,440444023,107637,107637,440444023,109,440444023,440476787,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,440476787,107,440476787,107,440476787,107,74865,440476787,74865,74865,440476787,107,440476787,107,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177]
def row90 : List ℕ := [77435,111,117,117,117,117,117,117,111,117,117,107,117,117,117,117,117,117,117,117,76923,76923,76923,76923,76921,76921,76921,76921,77947,117,117,119,42103,109,109,119,42103,109,109,42103,109,117,42103,117,117,42103,111,42103,111,42103,109,42103,74867,42103,109,42103,74865,76923,76923,76923,76923,76921,76921,76921,76921,115,74867,107,107,115,74867,107,107,74867,111,74867,111,74867,107,74867,74865,76923,76923,76923,76923,76921,76921,76921,76921,113,74865,176,93,113,74865,93,93,74865,178,111,74865,111,111,76923,76923,76923,76923,76921,76921,76921,76921,123,76923,76923,76923,123,76923,76923,76923,76923,76923,76923,76923,76923,76923,76923,76923,76923,76923,121,76921,76921,76921,121,76921,76921,76921,76921,76921,76921,76921,76921,76921]
def row91 : List ℕ := [111,35,35,111,121,11,11,121,75877,67,11,72789,74853,27,11,74853,74853,55,11,74853,75365,31,11,74849,119,2,119,0,11,35]
def row92 : List ℕ := [111,35,35,111,77925,67,72783,72783,76901,19,76901,45,11,76901,77413,21,119,18,119,0,123,11,123,11]
def row93 : List ℕ := [595663989,72811,73,118,74819,73,121,72783,72783,121,177275,11,74819,177275,72783,591469685,591469685,109663,164,591469683,72783,591469683,591469683,591470197,109665,11,591469683,72783,591469681,591470709,109669,37979,37979,144503,37979,144503,37979]
def row94 : List ℕ := [111,72811,72811,72811,72811,72811,111,72811,123,72789,182,67,67,67,123,72789,121,72783,184,67,67,67,121,72783,72821,95,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,72821,160,72821,72821,72821,72821,73333,97,72819,72819,72821,72819,72819,72819,72819,72819,72819,72819,154,72819,72819,72819,72819,72819,158,72819,72819,72819,72819,73845,101,72817,72817,72817,72817,72817,72817,72817,72817,72817,72817,106,72817,72817,72817,72817,119,37991,37979,37979,119,37991,37979,37979,72821,72821,72821,72821,72819,72819,72819,72819,72817,72817,72817,72817,72811,72811,72811,72811,37991,37979,37991,37979,37991,37979,37991,37979,72811,72811,72811,72811,72789,11,72789,72783,72811,186,72811,72811,72811,72811]
def row95 : List ℕ := [117,117,72821,72821,72821,117,72821,113,72817,72817,113,72817,72821,101,72817,113,72817,440474735,107,107,440474735,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,440475259,115,72821,117,72821,72821,72821,117,72821,95,72821,72821,72821,72821,72821,72821,107,72821,72821,72821,72821,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,440474735,107,107,440474735,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,297904251,115,115,72817,107,72817,72817,72817,72817,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745,297833591,101,297833591,101,297833591,91,72821,297833591,72821,72821,297833591,95,297833591,95,297833591,91,72817,297833591,72817,72817,297833591,297833581,297833591,440474735,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474747,440474747,440474747,440474747,440474747,440474747,440474747,440474747,440474745,440474745,440474745,440474745,440474745,440474745]
def row96 : List ℕ := [111,107631,107,107,107,107,111,107631,123,107643,107643,107643,107643,107643,123,107643,121,107641,107641,107641,107641,107641,121,107641,108155,113,115,115,115,115,115,115,113,115,115,115,115,115,107643,107643,107643,107643,107643,107643,107641,107641,107641,107641,107641,107641,108667,115,115,113,107,113,113,113,113,107643,107643,107643,107643,107641,107641,107641,107641,107641,107641,119,72823,91,95,119,72823,95,95,72823,115,72823,115,72823,91,113,72823,113,113,72823,91,72823,72821,72823,72813,72823,107631,107643,107643,107643,107643,107641,107641,107641,107641,117,72821,188,95,117,72821,95,95,72821,190,115,72821,115,115,72821,113,72821,113,72821,107,72821,107631,107643,107643,107643,107643,107641,107641,107641,107641,107643,107643,107643,107643,107643,107643,107643,107643,107641,107641,107641,107641,107641,107641]
def row97 : List ℕ := [110689,59,109665,109661,109665,13,109665,17,110177,45,119,14,119,0,115,35,115,35,123,23,123,23,23,109661]
def row98 : List ℕ := [107637,89,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,107637,108149,93,74865,74865,107637,74865,74865,74865,74865,74865,74865,74865,74865,74865,74865,108661,97,74863,119,40045,40045,40045,119,40045,40045,40045,107637,107637,107637,107637,74865,74865,74865,74865,74863,74863,74863,74863,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,40045,115,72811,72811,72811,115,72811,72811,72811,74865,74865,74865,74865,74863,74863,74863,74863,72811,72811,72811,72811,72811,72811,72811,72811,123,74857,74857,74857,123,74857,74857,74857,74863,74857,74863,74863,74863,74863,74857,74857,74857,74857,121,107599,194,59,121,107599,59,59,74863,132,74863,74863,74863,74863]
def row99 : List ℕ := [117,117,107637,107637,107637,117,107637,113,74865,583085691,111,107637,117,107637,107637,107637,117,107637,89,107637,107637,107637,107637,107637,107637,107,107637,107637,107637,107637,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,113,74865,74865,107637,113,74865,93,74865,314715771,111,74865,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,440444023,109,440444023,109,440444023,109,107637,440444023,107637,107637,440444023,109,440444023,109,440444023,109,74865,440444023,74865,74865,440444023,109,440444023,440476787,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,440476787,107,440476787,107,440476787,107,440476787,107,440476787,107,74865,440476787,74865,74865,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085179,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177,583085177]
def row100 : List ℕ := [142971,111,113,113,113,113,113,113,111,113,142459,142459,142459,142459,142457,142457,142457,142457,143483,113,113,119,107639,109,109,119,107639,109,109,107639,109,113,107639,113,113,107639,111,107639,111,107639,109,107639,107637,107639,109,107639,107635,142459,142459,142459,142459,142457,142457,142457,142457,117,107637,196,89,117,107637,89,89,107637,113,107637,113,107637,198,111,107637,111,111,107637,107,107637,107635,142459,142459,142459,142459,142457,142457,142457,142457,115,107635,107,107,115,107635,107,107,107635,107,113,107635,113,113,107635,111,107635,111,142459,142459,142459,142459,142457,142457,142457,142457,123,142459,142459,142459,123,142459,142459,142459,142459,142459,142459,142459,142459,142459,142459,142459,142459,142459,121,142457,142457,142457,121,142457,142457,142457,142457,142457,142457,142457,142457,142457]
def row101 : List ℕ := [119,62,119,117,119,91,119,115,119,98,119,113,119,109,119,111,123,123,123,123,121,121,121,121,117,128,117,115,117,170,117,113,117,180,117,111,123,123,123,123,121,121,121,121,115,192,115,113,115,107,115,111,123,123,123,123,121,121,121,121,113,200,113,111,123,123,123,123,121,121,121,121,123,123,123,123,123,123,123,123,121,121,121,121,121,121]
def row102 : List ℕ := [51,53,0,49,0,47]
def row103 : List ℕ := [49,0,47]
def row104 : List ℕ := [51,37937]
def row105 : List ℕ := [53,37935]
def row106 : List ℕ := [49,25,25,49,47,23,23,47,53,51,53,53,53,51,53,37937,23,53,53,53,25,51,51,37935,204,206,0,0,208,53,210,51]
def row107 : List ℕ := [47,53,0,51,0,49]
def row108 : List ℕ := [49,0,51]
def row109 : List ℕ := [47,39985]
def row110 : List ℕ := [53,39987]
def row111 : List ℕ := [49,25,25,49,53,47,53,53,53,47,23,53,53,39985,53,53,25,47,51,23,51,23,39987,39987,214,216,0,0,218,53,220,47]
def row112 : List ℕ := [49,51,0,53,0,47]
def row113 : List ℕ := [53,0,47]
def row114 : List ℕ := [49,72751]
def row115 : List ℕ := [51,37941]
def row116 : List ℕ := [51,49,51,51,51,49,51,72751,51,51,53,25,53,25,25,51,37941,37941,47,23,47,23,23,49,224,226,0,0,228,51,230,49]
def row117 : List ℕ := [49,47,0,53,0,51]
def row118 : List ℕ := [53,0,51]
def row119 : List ℕ := [49,72755]
def row120 : List ℕ := [47,72757]
def row121 : List ℕ := [49,49,49,49,47,49,49,47,53,25,53,25,25,47,72757,72757,51,23,51,23,72755,72755,23,49,234,236,0,0,238,47,240,49]
def row122 : List ℕ := [74293]
def row123 : List ℕ := [53,42545]
def row124 : List ℕ := [51,206,0,51,49,25,49,25,0,244,25,49,47,216,0,47,53,53,53,53,246,53,25,25,53,246,208,53,25,53,218,53]
def row125 : List ℕ := [42545,53]
def row126 : List ℕ := [47]
def row127 : List ℕ := [51]
def row128 : List ℕ := [53,53,250,53,51,252,0,51,49,25,25,49,47,254,0,47,53,250,53,53,25,25,53,42545]
def row129 : List ℕ := [107059]
def row130 : List ℕ := [53,75311]
def row131 : List ℕ := [49,226,0,49,47,23,47,23,0,258,23,47,51,51,51,51,260,51,23,23,51,260,228,51,23,51,53,206,53,0,210,51]
def row132 : List ℕ := [75311,53]
def row133 : List ℕ := [49]
def row134 : List ℕ := [53]
def row135 : List ℕ := [51,51,264,51,53,266,0,53,49,268,0,49,47,23,23,47,51,264,51,51,23,23,51,75311]
def row136 : List ℕ := [53,75317]
def row137 : List ℕ := [49,49,49,49,272,49,25,25,49,272,53,53,25,25,53,0,25,268,25,49,51,226,51,0,230,49,47,236,47,0,240,49]
def row138 : List ℕ := [49,49,272,49,53,25,25,53,51,252,0,51,47,254,0,47,49,272,49,49,25,25,75317,75317]
def row139 : List ℕ := [53,108083]
def row140 : List ℕ := [49,236,0,49,47,47,47,47,278,47,23,23,47,278,238,47,53,216,53,0,220,47,51,51,23,23,51,0,23,254,23,47]
def row141 : List ℕ := [47,47,278,47,53,266,0,53,51,23,23,51,49,268,0,49,47,278,47,47,23,23,108083,108083]
def row142 : List ℕ := [53,212,53,51,53,25,53,49,53,222,53,47,51,232,51,49,51,23,51,47,49,242,47,49,53,248,256,53,51,262,270,51,49,274,276,49,47,280,282,47]
def row143 : List ℕ := [11]
def row144 : List ℕ := [11,11,55,55,11,29,286,0,11,37935]
def row145 : List ℕ := [286,55,47,0,29]
def row146 : List ℕ := [11,11,55,55,11,27,286,0,11,72751]
def row147 : List ℕ := [55,288,55,55,55,55,29,290,29,27,47,47,47,47,29,11,29,11,55,55,55,55,55,55,55,55,11,55,55,292,55,55,55,55,47,47,47,47,27,11,27,11,47,11,47,47,47,47]
def row148 : List ℕ := [31]
def row149 : List ℕ := [27]
def row150 : List ℕ := [25]
def row151 : List ℕ := [300,49]
def row152 : List ℕ := [41521]
def row153 : List ℕ := [49,49,25,25,25,25,304,25,25]
def row154 : List ℕ := [31,25,25,31,27,25,25,27,49,49,49,25,49,49,25,25,25,25,31,296,31,27,49,49,49,49,31,298,31,302,49,49,49,49,27,296,27,302,49,306,49,49,49,49]
def row155 : List ℕ := [286,55,51,0,33]
def row156 : List ℕ := [11,11,55,55,11,33,286,0,11,39987]
def row157 : List ℕ := [11,11,55,55,11,31,286,0,11,72755]
def row158 : List ℕ := [33,310,33,31,55,312,55,55,55,55,51,51,51,51,33,11,33,11,55,314,55,55,55,55,51,51,51,51,31,11,31,11,55,55,55,55,55,55,55,55,11,55,51,11,51,51,51,51]
def row159 : List ℕ := [33]
def row160 : List ℕ := [29]
def row161 : List ℕ := [300,53]
def row162 : List ℕ := [53,53,25,25,25,25,244,25,25]
def row163 : List ℕ := [33,25,33,25,33,318,33,29,53,53,53,53,33,320,33,322,29,25,25,29,53,53,53,25,53,53,25,25,25,25,53,53,53,53,29,318,29,322,53,324,53,53,53,53]
def row164 : List ℕ := [74309]
def row165 : List ℕ := [328,74309]
def row166 : List ℕ := [105,0,69,0,330]
def row167 : List ℕ := [105]
def row168 : List ℕ := [105,0,81]
def row169 : List ℕ := [0,69]
def row170 : List ℕ := [69,69,328]
def row171 : List ℕ := [81,332,300,81,105,25,105,25,0,334,25,105,69,336,334,69,38999,33,338,37971,37975,31,338,37975,38487,25,37973,300,25,37973,340,37973,0,25]
def row172 : List ℕ := [37993,0,38487,37971,33,38485,38487]
def row173 : List ℕ := [85,33]
def row174 : List ℕ := [33,37975,81,346,33,81,105,25,33,105,69,0,33,69,41065,38999,39529,38999,38999,38999,0,38999,73833,87,72297,87,38997,38997,38997,0,25,38997,0,38997,0,25]
def row175 : List ℕ := [105,23,23,105,69,11,11,69,41047,33,11,37969,40023,55,11,40023,40535,29,40021,40021,40021,40021,37969,11,40021,83,332,83,0,11,23]
def row176 : List ℕ := [40535,37969,33,40533,40535,40021]
def row177 : List ℕ := [83]
def row178 : List ℕ := [33,40023,83,0,33,83,105,23,33,105,69,11,33,69,37969,11,43113,41047,41577,41047,41047,41047,11,41047,75881,87,87,41047,74345,41045,87,41045,41045,41045,37969,11,41045,354,37969,11,23]
def row179 : List ℕ := [83,0,81]
def row180 : List ℕ := [105,11]
def row181 : List ℕ := [83,72785]
def row182 : List ℕ := [11,11]
def row183 : List ℕ := [81]
def row184 : List ℕ := [105,358,0,105,45143,33,11,11,44119,11,11,44119,44631,360,362,44117,83,336,83,0,81,81,11,11,81,364,11,366]
def row185 : List ℕ := [44631,33,33,44629,44631,37969]
def row186 : List ℕ := [33,44119,83,334,33,83,81,11,33,81,105,0,33,105,11,11,45161,45143,43625,45143,45143,45143,11,45143,77929,87,76393,87,45141,45141,0,45141]
def row187 : List ℕ := [40021,72789]
def row188 : List ℕ := [37969,374,85]
def row189 : List ℕ := [72789,40021,374]
def row190 : List ℕ := [11,11,155232361,87,172004457,172004457,11,37969,85,85,40021,85,81,37969,81,33,81,11,11,85,40021,85,29,40021,40021,40021,40021,37969,172005481,87,376,40021,172004457,172004457,11,40021,378,37969,11,172004457]
def row191 : List ℕ := [142423]
def row192 : List ℕ := [142423,2388182209617]
def row193 : List ℕ := [382,0,583052373,69,0,0,11,11,384,583052373,583052373,0,180394089,142423,0,583052373,583052373,2388182209617]
def row194 : List ℕ := [69]
def row195 : List ℕ := [155234409,87,386,11,155233385,155233385,155233385,85,85,44117,85,69,33,69,33,69,388,0,11,11,85,44117,85,0,11,44117,180394089,87,0,44117,44117,180393041,155233385,155233385,0,11,11,11]
def row196 : List ℕ := [87,37969]
def row197 : List ℕ := [85,72785,374]
def row198 : List ℕ := [0,142423]
def row199 : List ℕ := [37969,37969,297833577,297833577,392,0,155263081,85,394,37971,0,37971,87,87,37975,87,83,37971,83,33,83,72785,72785,297833577,297833577,362,0,87,37975,87,31,297834089,85,376,37975,0,37975,396,297833577]
def row200 : List ℕ := [155266153,155266153,155267177,85,11,155266153,87,87,44119,87,69,33,69,33,69,340,0,11,11,87,44119,87,11,11,44119,314611305,85,11,44119,392,11,37969,37969,11,37969,11,11,11]
def row201 : List ℕ := [87]
def row202 : List ℕ := [33,332,33,27,81,354,378,85,402,394,72789]
def row203 : List ℕ := [0,142419]
def row204 : List ℕ := [406,33,336,33,0,388,83,0,392,85]
def row205 : List ℕ := [142423,382]
def row206 : List ℕ := [0,142419,0,142417]
def row207 : List ℕ := [583052373,69,382,0,0,0,11,11,583052373,0,384,583052373,180394089,142423,0,583052373,583052373,2388182209617]
def row208 : List ℕ := [155267177,142423,384,583046225]
def row209 : List ℕ := [37993,37993,410,412,0,0,69,11,11,69,142419,0,0,142419,142417,11,11,142417,414,142423,11,142423,142423,38505,142421,142423,142423,142423,142421,11,142423,416,142421,11,142421,39017,142423,396,142421,142421,583046225,406,11]
def row210 : List ℕ := [83,37971,342,344,348,33,83,37971,81,37969,350,352,356,33,81,37969,105,37993,37993,37993,37993,37993,105,37993,69,33,368,370,372,33,69,11,38505,85,87,87,87,87,87,87,85,87,87,87,87,87,87,380,87,87,87,87,37993,37993,37993,37993,87,390,87,87,87,87,39017,87,87,85,398,85,85,85,85,85,85,85,85,37969,85,37993,37993,37993,37993,37993,37993,85,400,85,85,85,85,37971,404,37971,37969,37993,37993,37993,37993,37971,408,37971,11,37993,37993,37993,37993,37969,11,37969,11,37993,418,37993,37993,37993,37993]
def row211 : List ℕ := [85,0,105]
def row212 : List ℕ := [105,25,105,25,0,334,25,105,69,422,334,69,73815,25,25,40017,340,40017,72791,27,338,72791,73303,29,338,40019,85,332,85,300,40017,300,0,25]
def row213 : List ℕ := [25,25]
def row214 : List ℕ := [0,25,0,75863,0,43091]
def row215 : List ℕ := [0,25]
def row216 : List ℕ := [25,25,25,25,25,426,25,25,25,25,40041,40041,40041,75863,75863,40041,75863,75863,75863,75863,75863,75863,75863,75863,75863,75863,75863,75863,75863,75863,40041,40041,40041,75863,43091,43091,43091,43091,43091,43091,43091,43091,25,25,25,25,43091,43091,43091,43091,428,0,0,0,428,0,0,430,428,0,0,430]
def row217 : List ℕ := [105,25]
def row218 : List ℕ := [42545]
def row219 : List ℕ := [75317]
def row220 : List ℕ := [105,25,105,25,105,583085143,436,583085655,438]
def row221 : List ℕ := [105,42545,436]
def row222 : List ℕ := [105,75317,438]
def row223 : List ℕ := [105,25,105,25,426,434,25,105,77911,25,440,434,25,25,25,76887,442,77399,444,85,336,85,0,81,422,81]
def row224 : List ℕ := [142423,142423,25]
def row225 : List ℕ := [25,25,25,0,583052371,69,0,25,448,583052371,583052371,0,180396137,142423,0,25]
def row226 : List ℕ := [142423,25]
def row227 : List ℕ := [25,69,142419,452,583052371,142419]
def row228 : List ℕ := [76375,87]
def row229 : List ℕ := [670463732841,670463732841,87,87,76887,87,83,670463732841,670463732841,87,76887,87,69,83,44115,83,69,0,25,670463732841,25,0,25]
def row230 : List ℕ := [452,670463732841,87,87,69,69,83]
def row231 : List ℕ := [163621993,163621993,163623017,87,450,454,163621993,163621993,163621993,83,83,44115,83,69,25,69,25,69,388,25,163621993,25,83,83,44115,83,456,458,44115,460,44115,44115,180396137,87,163621993,163621993,388,25]
def row232 : List ℕ := [142419,142419,25]
def row233 : List ℕ := [25,25,25,0,583085143,69,0,25,464,583085143,583085143,0,448831081,142419,0,25]
def row234 : List ℕ := [25,69,142423,452,583085143,142423]
def row235 : List ℕ := [87,83]
def row236 : List ℕ := [87,87,76887,87,83,670463732841,670463732841,670463732841,670463732841,83,44115,83,69,87,76887,87,69,0,25,670463732841,25,0,25]
def row237 : List ℕ := [87,452,670463732841,83,69,69,87]
def row238 : List ℕ := [163687529,163687529,163688553,83,466,468,163687529,163687529,163687529,87,87,76887,87,69,25,69,25,69,388,25,163687529,25,87,87,76887,87,470,472,76887,474,76887,76887,448831081,83,163687529,163687529,388,25]
def row239 : List ℕ := [81,332,300,81,105,25,105,25,0,334,25,105,69,336,334,69,38487,25,37973,300,25,37973,340,37973,37975,31,338,37975,38999,33,338,37971,0,25]
def row240 : List ℕ := [37973,55,332,25,55,74857,0,40023]
def row241 : List ℕ := [108083]
def row242 : List ℕ := [340,85,25,336,25,11,76905,0,44119,40017,482]
def row243 : List ℕ := [300,300,25]
def row244 : List ℕ := [25,25,486]
def row245 : List ℕ := [83,83]
def row246 : List ℕ := [87,87]
def row247 : List ℕ := [488,40041,69,334,25,69,77417,430,490,87,44631,492,83]
def row248 : List ℕ := [75311]
def row249 : List ℕ := [25,422,25,11,340,81,142441,0,109655,37973,496]
def row250 : List ℕ := [488,40041,69,334,25,69,142953,430,490,87,110167,492,83]
def row251 : List ℕ := [244,244,74293]
def row252 : List ℕ := [25,583085655,105,0,502]
def row253 : List ℕ := [142423,142423,142419]
def row254 : List ℕ := [163623017,142419,25,142419,506,464]
def row255 : List ℕ := [583052371,69,25,25,25,0,0,25,583052371,0,448,583052371,180396137,142423,0,25]
def row256 : List ℕ := [142419,69,25,142419,452,583052371]
def row257 : List ℕ := [142423,142419,142423]
def row258 : List ℕ := [163688553,142423,25,142423,514,448]
def row259 : List ℕ := [583085143,69,25,25,25,0,0,25,583085143,0,464,583085143,448831081,142419,0,25]
def row260 : List ℕ := [142423,69,25,142423,452,583085143]
def row261 : List ℕ := [40041,40041,25,25,25,426,25,25,25,504,69,440,25,434,25,69,25,69,142417,0,25,142417,508,142423,510,142423,512,142423,142423,40553,142419,142423,142423,142423,142423,142419,516,142419,518,142419,520,142419,142419,41065,142423,142421,0,142421,25]
def row262 : List ℕ := [81,40017,424,25,25,25,81,40017,105,40041,105,40041,40041,40041,432,25,40041,40041,105,40041,69,25,446,25,25,25,69,25,40553,83,87,87,87,87,87,87,87,83,87,87,87,87,87,87,87,87,87,40041,40041,40041,40041,40041,40041,87,462,87,87,87,87,41065,87,87,83,83,83,83,40041,40041,40041,40041,40041,40041,83,476,83,83,83,83,85,37973,478,25,85,37973,25,25,37973,83,37973,83,37973,480,37973,40017,40041,40041,40041,40041,37973,484,37973,494,40041,40041,40041,40041,40017,498,40017,500,40041,522,40041,40041,40041,40041]
def row263 : List ℕ := [85]
def row264 : List ℕ := [83,72789]
def row265 : List ℕ := [85,0,83]
def row266 : List ℕ := [110679,29,11,11,109655,11,11,109655,110167,360,85,85,11,11,85,364,11,526,83,422,83,0,528,44113,105,530,105]
def row267 : List ℕ := [110167,29,29,44625,110167,40021]
def row268 : List ℕ := [29,109655,105,0,29,105,11,11,45161,110679,43625,110679,110679,110679,11,110679,143465,87,141929,87,45137,45137,85,11,85,29,83,334,83,29,0,45137]
def row269 : List ℕ := [85,85,40021,85,81,37969,81,33,81,11,11,172005481,87,85,40021,85,29,40021,40021,40021,40021,37969,376,40021,172004457,172004457,11,40021,11,11,155232361,87,172004457,172004457,11,37969,378,37969,11,172004457]
def row270 : List ℕ := [142423,2388182211669]
def row271 : List ℕ := [382,0,583052369,69,540,583052369,583052369,0,180398185,142423,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row272 : List ℕ := [172011625,87,542,11,172010601,172010601,172010601,81,81,44113,81,69,29,69,29,69,81,44113,81,0,11,44113,180398185,87,172010601,172010601,11,11,11,11,180395093,180395093,0,11,388,0,0,44113]
def row273 : List ℕ := [87,40021]
def row274 : List ℕ := [172109929,81,11,583050345,87,87,109655,87,69,29,69,29,69,87,109655,87,11,11,109655,583050857,81,11,109655,40021,40021,11,40021,11,11,11,11,11,546,11,340,0,583050345,583050345]
def row275 : List ℕ := [105,23,23,105,69,11,11,69,40535,29,40021,40021,40021,40021,37969,11,40021,40023,55,11,40023,41047,33,11,37969,83,332,83,0,11,23]
def row276 : List ℕ := [40021,29,40021,41047,38481,41047]
def row277 : List ℕ := [105,23,29,105,69,11,29,69,40023,29,40021,38993,40021,40021,354,40021,40021,11,39017,40535,37481,40535,40535,40535,11,40535,75369,87,87,40535,74345,40021,87,11,38993,83,0,83,29,11,23]
def row278 : List ℕ := [72789,40021]
def row279 : List ℕ := [40021,72789,556]
def row280 : List ℕ := [85,37969,556]
def row281 : List ℕ := [31,332,31,29,81,402,85,354,40021,558,560]
def row282 : List ℕ := [105,25,105,25,0,334,25,105,69,422,334,69,73303,29,338,40019,72791,27,338,72791,73815,25,25,40017,340,40017,85,332,85,300,40017,300,0,25]
def row283 : List ℕ := [42089,0,40019,29,73815,40529,73815]
def row284 : List ℕ := [73301,29]
def row285 : List ℕ := [108137,87,87,107113,105,25,29,105,69,0,29,69,72791,29,41041,40019,41065,73303,39529,73303,73303,73303,0,73303,25,41041,0,41041,85,568,85,29,41041,0,0,25]
def row286 : List ℕ := [440444009,440444009,546,0,172074601,81,83,40019,83,29,0,40019,87,87,72791,87,83,440444009,440444009,528,0,87,72791,87,27,440444521,81,378,72791,0,72791,40021,40021,558,40019,72789,72789,396,440444009]
def row287 : List ℕ := [388,83,0,406,29,422,29,0,0,546,81]
def row288 : List ℕ := [0,142421,0,142419]
def row289 : List ℕ := [583052369,69,382,0,583052369,0,540,583052369,180398185,142423,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row290 : List ℕ := [172109929,142423,540,583048277]
def row291 : List ℕ := [42089,42089,410,576,0,0,69,11,11,69,578,142423,11,142423,142423,42601,142417,142423,142423,142423,142417,11,142423,580,142417,11,142417,43113,142423,142421,11,142421,11,583048277,583048277,406,11,142419,0,142419,0,396,142417]
def row292 : List ℕ := [105,42089,42089,42089,42089,42089,105,42089,69,29,532,534,536,29,69,11,42601,81,87,87,87,87,87,87,81,87,87,538,87,87,87,87,87,87,87,87,42089,42089,42089,42089,87,544,87,87,87,87,43113,87,87,42089,42089,42089,42089,42089,42089,81,548,81,81,81,81,85,40021,550,552,85,40021,554,29,40021,40021,81,40021,40021,81,40021,562,40021,40019,42089,42089,42089,42089,40021,11,40021,11,83,40019,564,566,83,40019,570,29,40019,572,81,40019,81,81,42089,42089,42089,42089,40019,574,40019,11,42089,582,42089,42089,42089,42089]
def row293 : List ℕ := [382,0,583052373,69,0,0,11,11,384,583052373,180394089,142423,583052373,0,0,583052373,583052373,2388182209617]
def row294 : List ℕ := [85,85,44117,85,69,33,69,33,69,388,0,11,11,180394089,87,85,44117,85,0,11,44117,0,44117,44117,180393041,155233385,155233385,155234409,87,586,11,155233385,155233385,155233385,0,11,11,11]
def row295 : List ℕ := [670463732841,670463732841,87,76887,87,69,83,44115,83,69,0,25,670463732841,25,87,87,76887,87,83,670463732841,670463732841,0,25]
def row296 : List ℕ := [25,142423]
def row297 : List ℕ := [592,670463732841,87,69,69,83,87]
def row298 : List ℕ := [142423,25,142423]
def row299 : List ℕ := [25,25,25,0,583052371,69,0,25,596,583052371,180396137,142423,583052371,0,0,25]
def row300 : List ℕ := [25,69,142419,592,583052371,142419]
def row301 : List ℕ := [83,83,44115,83,69,25,69,25,69,388,25,163621993,25,180396137,87,83,83,44115,83,456,590,44115,594,44115,44115,163621993,163621993,163621993,163621993,163623017,87,598,600,163621993,163621993,163621993,388,25]
def row302 : List ℕ := [382,0,583052369,69,540,583052369,180398185,142423,583052369,0,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row303 : List ℕ := [81,81,44113,81,69,29,69,29,69,180398185,87,81,44113,81,0,11,44113,172010601,172010601,172011625,87,604,11,172010601,172010601,172010601,11,11,180395093,180395093,11,11,388,0,0,44113,0,11]
def row304 : List ℕ := [142423,180398697,180399721,44137,180399721,142423,0,0,0,0,382]
def row305 : List ℕ := [382,0,583052373,69,0,0,11,11,180394089,142423,384,583052373,583052373,0,0,583052373,583052373,2388182209617]
def row306 : List ℕ := [25,25,25,0,583052371,69,0,25,180396137,142423,596,583052371,583052371,0,0,25]
def row307 : List ℕ := [382,0,583052369,69,180398185,142423,540,583052369,583052369,0,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row308 : List ℕ := [142423,51,142423,0,384,583052369]
def row309 : List ℕ := [583052373,11,583052369]
def row310 : List ℕ := [180394089,69]
def row311 : List ℕ := [583052371,142423,49,142423,0,596,382]
def row312 : List ℕ := [0,110185,105,142423]
def row313 : List ℕ := [105,25,105,25,105,583085655,438,583085143,436]
def row314 : List ℕ := [44137,25,438]
def row315 : List ℕ := [110185,109161,583085143,438,583052371,0,583085655,583085655,583085655,583085655]
def row316 : List ℕ := [438,180396137,69]
def row317 : List ℕ := [142423,47,142423,0,540,583052373]
def row318 : List ℕ := [583052369,11,583052373]
def row319 : List ℕ := [180398185,69]
def row320 : List ℕ := [105,44137,44137,142423,105,44137,142423,142423,44137,142423,608,142423,44649,69,142423,142423,610,142423,142423,142423,142423,142423,612,142423,142423,142423,142423,142423,614,142423,142423,142423,142423,583052373,616,583052373,382,583052373,618,583052373,620,583052373,396,583052373,583052371,583052373,11,583052373,583052369,583052371,622,583052371,624,583052371,626,628,583052371,630,632,583052371,396,583052371,583052369,583052369,634,583052369,382,583052369,636,583052369,638]
def row321 : List ℕ := [180399721,105]
def row322 : List ℕ := [0,142423,583085143,0,592]
def row323 : List ℕ := [0,110185,142423]
def row324 : List ℕ := [44137,44137,45161,142423,105,44137,45161,105,142423,642,142423,142423,142423,69,142423,69,44649,69,11,142423,600,142423,11,142423,583052373,11,583052373,69,142421,11,142421,11,583052371,644,583052371,69,142419,434,142419,646,583052369,11,583052369,69,142417,11,142417,11]
def row325 : List ℕ := [105,358,0,105,44631,360,362,44117,44119,11,11,44119,45143,33,11,11,83,336,83,0,81,81,11,11,81,364,11,366]
def row326 : List ℕ := [44117,360,45143,11,45143,618,44113]
def row327 : List ℕ := [105,0,0,105,44119,360,11,44117,44117,11,39017,44631,37481,44631,44631,44631,11,44631,77417,87,76393,87,11,11,83,0,83,0,81,11,81,11]
def row328 : List ℕ := [43607,360,44117,180394089,69,0,620]
def row329 : List ℕ := [31,336,31,0,362,85,0,388,87,0,396]
def row330 : List ℕ := [105,25,105,25,426,434,25,105,77399,444,76887,442,77911,25,626,434,25,25,25,85,336,85,0,81,422,81]
def row331 : List ℕ := [44137,300,44115,444,77911,334,77911,628]
def row332 : List ℕ := [75317,105,438]
def row333 : List ℕ := [0,105]
def row334 : List ℕ := [110185,109161,583052371,0,583085143,438,583085655,583085655,583085655,583085655]
def row335 : List ℕ := [110185,142423]
def row336 : List ℕ := [105,25,25,105,76887,664,666,44115,44115,75317,41065,77399,39529,77399,77399,77399,110185,87,109161,87,668,670,25,25,25,85,366,85,0,81,526,81]
def row337 : List ℕ := [76375,664,44115,388,180396137,69,456,180465257,87,632]
def row338 : List ℕ := [87,76887,87,69,83,44115,83,69,0,25,670463732841,25,670463732841,670463732841,87,87,76887,87,83,670463732841,670463732841,0,25]
def row339 : List ℕ := [448834665,448834665,180465257,69,83,44115,83,388,0,44115,87,87,76887,87,83,448834665,448834665,87,76887,87,388,676,76887,44115,76887,76887,448835177,69,0,76887,0,76887,0,44115]
def row340 : List ℕ := [87,69,69,83,592,670463732841,87]
def row341 : List ℕ := [44115,69,83,334,644,448834665,87,76887,87,77911,87,666,680,76887,69]
def row342 : List ℕ := [25,0,583052371,583052371,182562409,69,11,25,11,25]
def row343 : List ℕ := [45139,76375,684,69,180465257,180465257,180465257,448834665,69,83,83,180465257,180465257,87,77399,87,69,44115,77399,182562409,69,11,77399,11,77399]
def row344 : List ℕ := [27,422,27,0,0,528,81,388,87,0,396]
def row345 : List ℕ := [110167,360,109655,11,11,109655,110679,29,11,11,85,85,11,11,85,364,11,526,83,422,83,0,528,44113,105,530,105]
def row346 : List ℕ := [44113,360,110679,11,110679,636,44117]
def row347 : List ℕ := [105,0,0,105,109655,360,11,44113,43113,110167,41577,110167,110167,110167,11,110167,142953,87,141929,87,11,11,85,11,85,11,44113,11,83,0,83]
def row348 : List ℕ := [109143,360,44113,180398185,69,0,638]
def row349 : List ℕ := [105,44137,44137,44137,44137,44137,105,44137,44649,69,87,87,87,87,87,87,69,87,87,588,87,87,87,87,87,602,87,87,87,87,87,606,87,87,87,87,44137,44137,44137,44137,45161,87,87,44137,640,648,44137,44137,44137,44137,44137,44137,85,44117,650,652,85,44117,654,656,44117,11,44117,69,44117,658,44117,44115,44117,11,44117,44113,44137,44137,44137,44137,83,44115,660,662,83,44115,672,674,44115,678,682,44115,686,69,44115,688,44115,44113,44137,44137,44137,44137,81,44113,690,692,81,44113,694,696,44113,11,44113,69,44137,44137,44137,44137]
def row350 : List ℕ := [25,182491753]
def row351 : List ℕ := [182562409,69,25,0,11,25,583085143,583085143,11,25]
def row352 : List ℕ := [44649,142423,44649,44649,142423,142423,142423,44649,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,44649,105,44649,142423,105,44649,11,11,11,11,69,69,69,69,25,11,11,25,11,11,11,11,25,700,25,0,69,702,69,69,69,69,25,11,25,11,11,11,11,11,69,69,69,69]
def row353 : List ℕ := [583052883,25,142423]
def row354 : List ℕ := [0,583085655,53]
def row355 : List ℕ := [583052883,53,583085655,69,583052883,0,11,583052883,583085143,583085143,583085143,583085143,11,583052883]
def row356 : List ℕ := [143447,43625,69,142423,142423,142423,44649,44137,69,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,583052885,11,583052885,11,583052885,69,583052885,69,583052885,11,583052885,583052883,583052885,11,583052885,583052881,583052883,706,583052883,708,583052883,710,69,583052883,69,69,583052883,11,583052883,583052881,583052881,11,583052881,11,583052881,69,583052881,69]
def row357 : List ℕ := [583052883,53,583052883,0,583085655,69,11,583052883,583085143,583085143,583085143,583085143,11,583052883]
def row358 : List ℕ := [105,25,25,105,77399,69,44627,69,11,44627,39529,76887,41065,76887,76887,76887,69,76887,87,109673,87,110697,714,69,25,69,69,85,11,85,11,11,44627,81,11,81,11]
def row359 : List ℕ := [25,0,182562409,69,11,25,583085143,583085143,11,25]
def row360 : List ℕ := [448835177,448835177,182562409,69,83,44627,83,69,11,44627,77911,43603,718,69,448835177,448835177,448835177,87,87,76887,76887,448834665,69,11,44627]
def row361 : List ℕ := [87,43625,87,105,44649,704,69,44649,44649,44649,44649,105,44649,105,44649,44137,69,87,87,87,69,87,87,87,87,87,87,87,87,87,87,87,87,87,87,87,87,44649,44649,44649,44649,44649,712,69,44649,44649,44649,44649,44649,44649,85,44629,11,69,85,44629,69,69,44629,69,44629,69,44629,11,44629,44627,44629,11,44629,44625,44649,44649,44649,44649,83,44627,716,69,83,44627,69,69,44627,720,69,44627,69,69,44627,11,44627,44625,44649,44649,44649,44649,81,44625,11,69,81,44625,69,69,44625,69,44625,69,44649,44649,44649,44649]
def row362 : List ℕ := [105,23,23,105,69,11,11,69,73813,31,11,72785,72789,27,72789,72789,72789,72789,72785,11,72789,73301,55,11,72787,87,332,87,0,11,23]
def row363 : List ℕ := [73301,72785,31,73299,72789,73301]
def row364 : List ℕ := [31,72789,108649,85,85,107113,105,23,31,105,69,11,31,69,72785,11,75881,83,73813,73811,74345,73813,73813,73813,73813,73813,72785,11,73813,73811,73811,11,73811,87,0,87,31,402,72785,11,23]
def row365 : List ℕ := [87,0,81]
def row366 : List ℕ := [105,730,0,105,77909,31,11,11,76885,360,77397,11,11,76883,87,336,87,0,392,76885,81,81,11,11,81,364,11,366]
def row367 : List ℕ := [77397,31,31,77395,77397,72785]
def row368 : List ℕ := [31,76885,81,11,31,81,105,0,31,105,11,11,77929,77909,76393,77909,77909,77909,110697,85,109161,85,77907,77907,11,77907,87,334,87,31,0,77909]
def row369 : List ℕ := [297872489,297872489,297873513,85,11,297872489,83,83,76883,83,69,31,69,31,69,11,11,83,76883,83,11,11,76883,314646633,85,11,76883,362,11,340,0,72785,72785,11,72785,11,11,11]
def row370 : List ℕ := [556,40021,72789]
def row371 : List ℕ := [72785,556,85]
def row372 : List ℕ := [11,11,297904233,83,440474729,440474729,11,72785,85,85,72789,85,81,72785,81,31,81,11,11,85,72789,85,27,72789,72789,72789,72789,72785,440475241,83,440474729,440474729,11,72789,740,72785,742,72789,11,440474729]
def row373 : List ℕ := [142419]
def row374 : List ℕ := [142419,2388450679889]
def row375 : List ℕ := [746,0,583085141,69,11,11,748,583085141,583085141,0,448863849,142419,583085141,2388450679889,0,0,0,583085141]
def row376 : List ℕ := [297906281,83,750,11,448863337,448863337,448863337,85,85,76885,85,69,31,69,31,69,11,11,85,76885,85,0,11,76885,448863849,83,76885,448863313,448863337,448863337,0,11,388,0,0,76885,11,11]
def row377 : List ℕ := [81,332,300,81,105,25,105,25,0,334,25,105,69,336,334,69,37975,31,338,37975,38487,25,37973,300,25,37973,340,37973,38999,33,338,37971,0,25]
def row378 : List ℕ := [72809,0,37975,31,87,38995,38997]
def row379 : List ℕ := [87,31]
def row380 : List ℕ := [81,758,31,81,105,25,31,105,69,0,31,69,37975,31,38485,37975,38483,37975,38505,37975,37481,38487,38485,0,25,38485,0,38485,40553,37975,39529,38999,0,38483,0,25]
def row381 : List ℕ := [87,87,37975,87,83,37971,83,33,83,72785,72785,297833577,297833577,362,0,297834089,85,87,37975,87,31,560,37975,0,37975,37969,37969,297833577,297833577,392,0,155263081,85,742,37971,0,37971,382,297833577]
def row382 : List ℕ := [560,31,332,31,29,81,402,85,354,40021,740]
def row383 : List ℕ := [388,87,0,396,31,336,31,0,362,85]
def row384 : List ℕ := [142419,746]
def row385 : List ℕ := [0,142423,0,142417]
def row386 : List ℕ := [297873513,142419,748,583081041]
def row387 : List ℕ := [583085141,69,746,0,11,11,583085141,0,748,583085141,448863849,142419,583085141,2388450679889,0,0,0,583085141]
def row388 : List ℕ := [72809,72809,768,770,0,0,69,11,11,69,142417,11,11,142417,772,142421,11,142421,73321,142419,142421,142421,142421,142419,142421,583081041,774,142419,11,142419,142419,73833,142421,11,142419,396,11,142423,0,142423,0,382,142421]
def row389 : List ℕ := [81,72785,724,726,728,31,81,72785,105,72809,72809,72809,72809,72809,105,72809,69,31,732,734,736,31,69,11,73321,83,85,85,85,85,85,85,83,85,85,85,85,85,72785,85,72809,72809,72809,72809,72809,72809,85,738,85,85,85,85,73833,85,85,83,744,83,83,83,83,72809,72809,72809,72809,83,752,83,83,83,83,87,37975,754,756,87,37975,760,31,37975,762,85,37975,85,85,37975,83,37975,83,37975,764,37975,72785,72809,72809,72809,72809,37975,766,37975,11,72809,72809,72809,72809,72785,11,72785,11,72809,776,72809,72809,72809,72809]
def row390 : List ℕ := [105,23,23,105,69,11,11,69,40023,55,11,40023,40535,29,40021,40021,40021,40021,37969,11,40021,41047,33,11,37969,83,332,83,0,11,23]
def row391 : List ℕ := [55,332,25,55,74857,0,40023,37973]
def row392 : List ℕ := [105,23,23,105,69,11,11,69,73301,55,11,72787,72789,27,72789,72789,72789,72789,72785,11,72789,73813,31,11,72785,87,332,87,0,11,23]
def row393 : List ℕ := [105,74857,74857,74857,74857,74857,105,74857,69,55,11,55,55,55,69,55,75369,81,85,85,85,85,85,85,85,81,85,85,85,85,85,74857,74857,74857,74857,85,11,85,85,85,85,75881,85,85,74857,74857,74857,74857,81,11,81,81,81,81,87,40023,780,55,87,40023,55,55,40023,85,40023,85,40023,81,40023,81,40023,782,40023,72787,74857,74857,74857,74857,40023,11,40023,11,83,72787,784,55,83,72787,55,55,72787,81,72787,81,74857,74857,74857,74857,72787,11,72787,11,74857,11,74857,74857,74857,74857]
def row394 : List ℕ := [83,83,76883,83,69,31,69,31,69,11,11,314646633,85,83,76883,83,11,11,76883,11,76883,297872489,297872489,297873513,85,11,297872489,340,0,362,11,72785,72785,11,72785,11,11,11]
def row395 : List ℕ := [105,358,0,105,44119,11,11,44119,44631,360,362,44117,45143,33,11,11,83,336,83,0,81,81,11,11,81,364,11,366]
def row396 : List ℕ := [87,87,44119,87,69,33,69,33,69,340,0,11,11,314611305,85,87,44119,87,11,11,44119,11,44119,155266153,155266153,155267177,85,11,155266153,392,11,37969,37969,11,37969,11,11,11]
def row397 : List ℕ := [25,336,25,11,76905,0,44119,340,85,40017,482]
def row398 : List ℕ := [105,730,0,105,77397,11,11,76883,76885,360,77909,31,11,11,87,336,87,0,392,76885,81,81,11,11,81,364,11,366]
def row399 : List ℕ := [0,11,0,110165,0,75845,0,108083]
def row400 : List ℕ := [108083,11,11,108083,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,110165,76881,110165,75845,11,11,75845,11,108083,11,11,11,11,110165,110165,110165,110165,75845,11,11,75845,798,482,0,0,108083,0,0,108083,11,11,11,11,75845,11,11,75845,108083,0,0,108083]
def row401 : List ℕ := [105,76905,76905,76905,76905,76905,105,76905,77417,69,85,85,85,85,85,85,69,85,85,788,85,85,85,85,85,11,85,85,85,85,76905,76905,76905,76905,77929,85,85,76905,11,76905,76905,76905,76905,87,44119,790,11,87,44119,11,11,44119,792,85,44119,85,85,44119,11,44119,69,44119,794,44119,76883,44119,11,44119,76881,76905,76905,76905,76905,83,76883,796,11,83,76883,11,11,76883,11,76883,69,76883,11,76883,76881,76905,76905,76905,76905,81,81,11,76881,11,11,81,76881,800,11,11,11,76881,11,11,76881,11,69,76905,76905,76905,76905]
def row402 : List ℕ := [300]
def row403 : List ℕ := [300,25]
def row404 : List ℕ := [0,77417,77417,583052885,804,0,0,107575,806]
def row405 : List ℕ := [806,300]
def row406 : List ℕ := [25,300,300]
def row407 : List ℕ := [804,0,0,142421,804,69,0,107575,812]
def row408 : List ℕ := [0,77417,77417,583085653,804,0,0,107575,806]
def row409 : List ℕ := [77417,142421,77417,77417,142421,142421,142421,77417,142421,142421,142421,142421,142421,142421,142421,142421,77417,105,77417,142421,105,77417,808,810,0,0,142421,142421,142421,142421,69,69,69,69,814,488,0,0,107575,11,11,107575,816,810,0,0,69,69,69,69,107575,11,11,107575,107575,11,107575,11,69,69,69,69]
def row410 : List ℕ := [105,354,0,105,44631,69,44117,44631,44631,69,490,44631,11,44631,37481,44119,38505,44631,69,44117,44117,11,44631,44137,43607,45161,69,69,83,334,83,0,81,11,81,11]
def row411 : List ℕ := [69,334,25,69,77417,430,44631,490,87,492,83,488,40041]
def row412 : List ℕ := [105,402,0,105,77397,69,77395,69,11,77395,72297,76885,73833,76885,76885,76885,69,76885,76885,11,85,109673,85,110697,69,69,87,334,87,0,492,77395,81,11,81,11]
def row413 : List ℕ := [85,76393,85,105,77417,818,69,77417,77417,77417,77417,105,77417,105,77417,76905,69,85,85,85,69,85,85,85,85,85,85,85,85,85,85,85,85,77393,85,77417,77417,77417,77417,77417,69,77417,77417,77417,77417,87,44631,820,69,87,44631,69,69,44631,85,44631,85,44631,69,44631,69,44631,822,44631,77395,44631,11,44631,77393,77417,77417,77417,77417,83,77395,824,69,83,77395,69,69,77395,69,77395,69,77395,11,77395,77393,77417,77417,77417,77417,81,77393,11,69,81,77393,69,69,77393,11,69,77393,69,69,77417,77417,77417,77417]
def row414 : List ℕ := [87,0,85]
def row415 : List ℕ := [110675,27,11,11,109651,11,110163,360,87,422,87,0,546,109649,85,85,11,11,85,364,11,526,11,109651,105,828,105]
def row416 : List ℕ := [110163,27,27,110161,110163,72789]
def row417 : List ℕ := [27,109651,105,0,27,105,11,11,110697,110675,109161,110675,110675,110675,143465,83,141929,83,110673,110673,87,334,87,27,0,110673,85,11,85,27,11,110675]
def row418 : List ℕ := [142419,2388316462165]
def row419 : List ℕ := [746,0,583117905,69,836,583117905,583117905,0,448899177,142419,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row420 : List ℕ := [440512617,83,838,11,440511593,440511593,440511593,81,81,109649,81,69,27,69,27,69,81,109649,81,0,11,109649,448899177,83,440511593,440511593,0,11,388,0,0,109649,11,11,11,11,314645589,314645589]
def row421 : List ℕ := [440545385,81,11,440544361,83,83,109651,83,69,27,69,27,69,83,109651,83,11,11,109651,583116393,81,528,11,340,0,72789,72789,11,72789,11,11,11,11,11,11,109651,440544361,440544361]
def row422 : List ℕ := [105,25,105,25,0,334,25,105,69,422,334,69,72791,27,338,72791,73303,29,338,40019,73815,25,25,40017,340,40017,85,332,85,300,40017,300,0,25]
def row423 : List ℕ := [107625,0,72791,27,87,41041,41043]
def row424 : List ℕ := [27,87]
def row425 : List ℕ := [42601,72791,73815,41577,105,25,27,105,69,0,27,69,72791,27,40531,72791,40529,72791,40553,72791,39529,73303,0,40531,25,40529,0,40529,85,848,85,27,40529,0,0,25]
def row426 : List ℕ := [87,87,72791,87,83,440444009,440444009,528,0,440444521,81,87,72791,87,27,378,72791,0,72791,440444009,440444009,546,0,83,40019,83,29,172074601,81,0,40019,72789,72789,40021,40021,558,40019,382,440444009]
def row427 : List ℕ := [388,87,0,396,27,422,27,0,0,528,81]
def row428 : List ℕ := [105,23,23,105,69,11,11,69,72789,27,72789,72789,72789,72789,72785,11,72789,73301,55,11,72787,73813,31,11,72785,87,332,87,0,11,23]
def row429 : List ℕ := [72789,27,72789,85,73809,73811]
def row430 : List ℕ := [105,23,27,105,69,11,27,69,72789,27,73299,72789,72789,73297,72789,72789,72789,11,73321,72789,72297,73301,11,73299,75369,72789,72789,72789,74345,72789,73813,11,73297,87,0,87,27,402,72789,11,23]
def row431 : List ℕ := [85,85,72789,85,81,72785,81,31,81,11,11,440475241,83,85,72789,85,27,72789,72789,72789,72789,72785,440474729,440474729,11,72789,11,11,297904233,83,440474729,440474729,11,72785,742,72789,740,72785,11,440474729]
def row432 : List ℕ := [0,142423,0,142421]
def row433 : List ℕ := [583117905,69,746,0,583117905,0,836,583117905,448899177,142419,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row434 : List ℕ := [440545385,142419,836,583081045]
def row435 : List ℕ := [107625,107625,768,864,0,0,69,11,11,69,866,142419,11,142419,142419,108137,142417,142419,142419,142419,142417,868,142417,11,142417,108649,142419,396,11,142423,0,142423,0,382,142417,142421,11,142421,11,11,142419,583081045,583081045]
def row436 : List ℕ := [105,107625,107625,107625,107625,107625,105,107625,69,27,830,832,834,27,69,11,108137,81,83,83,83,83,83,83,81,83,107625,107625,107625,107625,83,840,83,83,83,83,108649,83,83,107625,107625,107625,107625,107625,107625,81,842,81,81,81,81,87,72791,844,846,87,72791,850,27,72791,83,72791,83,72791,852,81,72791,81,81,72791,404,72791,72789,107625,107625,107625,107625,72791,854,72791,11,85,72789,856,858,85,72789,860,27,72789,862,83,72789,83,83,72789,72789,81,72789,72789,81,107625,107625,107625,107625,72789,11,72789,11,107625,870,107625,107625,107625,107625]
def row437 : List ℕ := [746,0,583117905,69,836,583117905,448899177,142419,583117905,0,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row438 : List ℕ := [81,81,109649,81,69,27,69,27,69,448899177,83,81,109649,81,0,11,109649,440511593,440511593,440512617,83,874,11,440511593,440511593,440511593,388,0,0,109649,0,11,11,11,314645589,314645589,11,11]
def row439 : List ℕ := [142419,448899689,448900713,109673,448900713,142419,0,0,746]
def row440 : List ℕ := [746,0,583117905,69,448899177,142419,836,583117905,583117905,0,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row441 : List ℕ := [142419,25,142419]
def row442 : List ℕ := [583085143,882,142419,53,142419,0,746]
def row443 : List ℕ := [0,0,44649,105,142419]
def row444 : List ℕ := [109673,25,436]
def row445 : List ℕ := [44649,43625,583085143,436,583085143,0,583052883,583085143,583085143,583085655]
def row446 : List ℕ := [436,0,448831081,69]
def row447 : List ℕ := [25,25,25,0,583085143,69,0,25,448831081,142419,882,583085143,583085143,0,0,25]
def row448 : List ℕ := [748,142419,51,142419,0,583117905]
def row449 : List ℕ := [583085141,11,583117905]
def row450 : List ℕ := [0,448863849,69]
def row451 : List ℕ := [746,0,583085141,69,11,11,448863849,142419,748,583085141,583085141,0,583085141,2388450679889,0,0,0,583085141]
def row452 : List ℕ := [142419,47,142419,0,836,583085141]
def row453 : List ℕ := [583117905,11,583085141]
def row454 : List ℕ := [448899177,69]
def row455 : List ℕ := [105,109673,109673,142419,105,109673,142419,142419,109673,142419,878,142419,110185,69,142419,142419,880,142419,142419,142419,142419,583085143,884,583085143,886,583085143,440,888,583085143,890,892,583085143,894,142419,583085143,142419,142419,583085143,406,583085143,583085141,583085143,406,583085143,583117905,583085141,896,583085141,746,583085141,898,583085141,900,583085141,902,142419,583085141,142419,142419,583085141,11,583085141,583117905,583117905,904,583117905,746,583117905,906,583117905,908]
def row456 : List ℕ := [448900713,105]
def row457 : List ℕ := [142423,583085143,0,592]
def row458 : List ℕ := [0,44649,583085143]
def row459 : List ℕ := [109673,109673,110697,142419,105,109673,110697,105,142419,912,142419,142419,142419,69,142419,69,110185,69,11,142419,583085143,914,583085143,69,142423,434,142423,916,468,142419,583085141,11,583085141,69,142421,11,142421,11,11,142419,583117905,11,583117905,69,142417,11,142417,11]
def row460 : List ℕ := [105,25,105,25,426,434,25,105,76887,442,77399,444,77911,25,440,434,25,25,25,85,336,85,0,81,422,81]
def row461 : List ℕ := [109673,300,76887,442,87,334,45139,888]
def row462 : List ℕ := [42545,105,436]
def row463 : List ℕ := [44649,43625,583085143,0,583085143,436,583052883,583085143,583085143,583085655]
def row464 : List ℕ := [44649,583085143]
def row465 : List ℕ := [105,25,25,105,76887,924,44627,76887,334,76887,76887,42545,40553,76887,39529,77399,44649,76887,43625,77911,926,928,25,25,25,85,366,85,0,81,526,81]
def row466 : List ℕ := [87,924,76887,470,388,448831081,69,448835177,83,892]
def row467 : List ℕ := [87,87,76887,87,83,670463732841,670463732841,83,44115,83,69,87,76887,87,69,0,25,670463732841,25,670463732841,670463732841,0,25]
def row468 : List ℕ := [25,25,25,0,583085143,69,0,25,882,583085143,448831081,142419,583085143,0,0,25]
def row469 : List ℕ := [87,87,76887,87,69,25,69,25,69,388,25,163687529,25,448831081,83,87,87,76887,87,470,934,76887,474,76887,76887,163687529,163687529,163687529,163687529,163688553,83,936,468,163687529,163687529,163687529,388,25]
def row470 : List ℕ := [83,44115,83,69,87,76887,87,69,0,25,670463732841,25,87,87,76887,87,83,670463732841,670463732841,670463732841,670463732841,0,25]
def row471 : List ℕ := [87,87,76887,87,83,448834665,448834665,448835177,69,87,76887,87,388,940,76887,44115,76887,76887,0,76887,0,76887,448834665,448834665,83,44115,83,388,180465257,69,0,44115,0,44115]
def row472 : List ℕ := [83,69,69,87,87,592,670463732841]
def row473 : List ℕ := [87,76887,87,77911,76887,69,87,334,944,914,448834665,83,334,44115,69]
def row474 : List ℕ := [583085143,583085143,25,0,182562409,69,11,25,11,25]
def row475 : List ℕ := [77911,43603,948,69,448835177,448835177,448835177,448834665,69,87,87,76887,76887,448835177,448835177,83,44627,83,69,182562409,69,11,44627,11,44627]
def row476 : List ℕ := [33,336,33,0,388,83,0,392,85,0,406]
def row477 : List ℕ := [29,422,29,0,0,546,81,388,83,0,406]
def row478 : List ℕ := [105,730,0,105,76885,360,77397,11,11,76883,77909,31,11,11,87,336,87,0,392,76885,81,81,11,11,81,364,11,366]
def row479 : List ℕ := [76885,360,85,11,77907,898,109649]
def row480 : List ℕ := [105,0,0,105,76885,360,77395,76885,11,76885,76885,11,73321,76885,72297,77397,11,77395,77417,76885,76393,77909,11,11,87,0,87,0,81,11,81,11]
def row481 : List ℕ := [85,360,76885,0,448863849,69,900]
def row482 : List ℕ := [746,0,583085141,69,11,11,748,583085141,448863849,142419,583085141,0,583085141,2388450679889,0,0,0,583085141]
def row483 : List ℕ := [85,85,76885,85,69,31,69,31,69,11,11,448863849,83,85,76885,85,0,11,76885,76885,448863313,448863337,448863337,297906281,83,964,11,448863337,448863337,448863337,388,0,0,76885,0,11,11,11]
def row484 : List ℕ := [110163,360,109651,11,110675,27,11,11,87,422,87,0,546,109649,85,85,11,11,85,364,11,526,11,109651,105,828,105]
def row485 : List ℕ := [109649,360,110675,11,110675,906,76885]
def row486 : List ℕ := [105,0,0,105,109651,360,11,109649,108649,110163,107113,110163,110163,110163,142953,83,141929,83,11,11,87,0,87,0,85,11,85,11,109649,11,11,110163]
def row487 : List ℕ := [109139,360,109649,448899177,69,0,908]
def row488 : List ℕ := [105,109673,109673,109673,109673,109673,105,109673,110185,69,83,83,83,83,83,83,69,83,83,876,83,83,83,83,109673,109673,109673,109673,110697,83,83,109673,910,918,109673,109673,109673,109673,109673,109673,87,76887,920,922,87,76887,930,932,76887,938,83,76887,83,83,76887,942,946,76887,950,69,76887,952,76887,76885,76887,954,76887,109649,109673,109673,109673,109673,85,76885,956,958,85,76885,960,962,76885,966,83,76885,83,83,76885,11,76885,69,76885,11,76885,109649,109673,109673,109673,109673,81,109649,968,970,81,109649,972,974,109649,11,109649,69,109673,109673,109673,109673]
def row489 : List ℕ := [25,450927209]
def row490 : List ℕ := [182562409,69,25,0,583052371,583052371,11,25,11,25]
def row491 : List ℕ := [110185,142419,110185,110185,142419,142419,142419,110185,142419,142419,142419,142419,110185,105,110185,142419,105,110185,25,978,25,0,142419,142419,142419,142419,69,980,69,69,69,69,25,11,25,11,25,11,25,11,11,11,11,11,142419,142419,142419,142419,69,69,69,69,11,11,11,11,11,11,11,11,69,69,69,69]
def row492 : List ℕ := [583085655,25,142419]
def row493 : List ℕ := [0,583085655,49]
def row494 : List ℕ := [583085655,49,583085655,69,583085655,0,583052371,583085655,11,583085655,11,583085655,583085143,583085655]
def row495 : List ℕ := [143443,109161,69,142419,142419,142419,110185,109673,69,142419,142419,142419,142419,142419,583085655,984,583085655,986,583085655,988,69,583085655,69,69,583085655,142419,583085655,142419,583085655,11,583085655,583085653,583085655,11,583085655,583118417,583085653,11,583085653,11,583085653,69,583085653,69,583085653,142419,583085653,142419,583085653,11,583085653,583118417,583118417,11,583118417,11,583118417,69,583118417,69]
def row496 : List ℕ := [583085655,49,583085655,0,583085655,69,583052371,583085655,11,583085655,11,583085655,583085143,583085655]
def row497 : List ℕ := [105,25,25,105,77399,69,44115,77399,77399,69,11,77399,11,77399,39529,76887,40553,77399,69,44115,77399,44137,76375,45161,992,69,25,69,69,85,11,85,11,81,11,81,11]
def row498 : List ℕ := [25,0,182562409,69,583052371,583052371,11,25,11,25]
def row499 : List ℕ := [180465257,180465257,182562409,69,87,77399,87,69,44115,77399,11,77399,11,77399,45139,76375,996,69,180465257,180465257,180465257,83,83,448834665,69]
def row500 : List ℕ := [83,109161,83,105,110185,982,69,110185,110185,110185,110185,105,110185,105,110185,109673,69,83,83,83,69,83,83,83,83,83,83,83,83,110185,110185,110185,110185,110185,990,69,110185,110185,110185,110185,110185,110185,87,77399,994,69,87,77399,69,69,77399,83,77399,83,77399,998,69,77399,69,69,77399,11,77399,77397,77399,11,77399,110161,110185,110185,110185,110185,85,77397,11,69,85,77397,69,69,77397,83,77397,83,77397,69,77397,69,77397,11,77397,110161,110185,110185,110185,110185,81,110161,11,69,81,110161,69,69,110161,69,110161,69,110185,110185,110185,110185]
def row501 : List ℕ := [109655,11,11,109655,110167,360,110679,29,11,11,85,85,11,11,85,364,11,526,83,422,83,0,528,44113,105,530,105]
def row502 : List ℕ := [87,87,109655,87,69,29,69,29,69,583050857,81,87,109655,87,11,11,109655,11,109655,172109929,81,11,583050345,11,11,40021,40021,11,40021,11,11,11,340,0,546,11,583050345,583050345]
def row503 : List ℕ := [0,11,0,77393,0,75333,0,75311]
def row504 : List ℕ := [77393,77393,109653,77393,77393,77393,77393,77393,77393,77393,77393,77393,77393,77393,109653,77393,75333,11,11,75333,11,75311,11,11,11,11,77393,77393,77393,77393,75333,11,11,75333,1006,496,0,0,75311,0,0,75311,11,11,11,11,77393,77393,77393,77393,75333,11,11,75333,75311,0,0,75311,75311,11,75311,11]
def row505 : List ℕ := [109651,11,110163,360,110675,27,11,11,87,422,87,0,546,109649,85,85,11,11,85,364,11,526,11,109651,105,828,105]
def row506 : List ℕ := [83,83,109651,83,69,27,69,27,69,583116393,81,83,109651,83,11,11,109651,440545385,81,11,440544361,340,0,528,11,11,11,11,109651,72789,72789,11,72789,11,11,11,440544361,440544361]
def row507 : List ℕ := [142953,69,81,81,81,81,81,81,69,81,142441,142441,142441,142441,143465,81,81,142441,11,142441,142441,142441,142441,87,109655,1002,11,87,109655,11,11,109655,1004,81,109655,81,81,109655,11,109655,69,109655,11,109655,109653,109655,498,109655,109651,142441,142441,142441,142441,85,85,11,109653,11,11,85,109653,1008,11,11,11,109653,11,81,109653,81,81,109653,11,11,109653,11,69,109653,11,109653,109651,142441,142441,142441,142441,83,109651,1010,11,83,109651,11,11,109651,1012,81,109651,81,81,109651,11,109651,69,142441,142441,142441,142441,105,142441,142441,142441,105,142441,142441,142441]
def row508 : List ℕ := [0,142953,142953,583052881,0,107575,804,0,806]
def row509 : List ℕ := [804,0,0,142417,804,69,0,107575,812]
def row510 : List ℕ := [0,142953,142953,583118417,804,0,0,107575,806]
def row511 : List ℕ := [142953,142417,142953,142953,142417,142417,142417,142953,142953,105,142953,142417,105,142953,1016,810,0,0,142417,142417,142417,142417,69,69,69,69,107575,11,11,107575,1018,488,0,0,107575,11,107575,11,142417,142417,142417,142417,69,69,69,69,107575,11,107575,11,1020,810,0,0,142417,142417,142417,142417,69,69,69,69]
def row512 : List ℕ := [105,354,0,105,110167,69,44113,110167,110167,69,11,110167,490,110167,41577,109655,42601,110167,69,44113,110167,44137,109143,45161,69,69,85,11,85,11,44113,11,83,334,83]
def row513 : List ℕ := [69,334,25,69,142953,430,110167,490,87,492,83,488,40041]
def row514 : List ℕ := [105,402,0,105,110163,69,109649,110163,110163,69,107113,109651,108137,110163,69,109649,110163,109673,109139,110697,69,69,87,334,87,0,492,110163,85,11,85,11,11,110163,109649,11]
def row515 : List ℕ := [81,141929,81,105,142953,1022,69,142953,142953,142953,142953,105,142953,105,142953,142441,69,81,81,81,69,81,81,81,81,142953,142953,142953,142953,142953,69,142953,142953,142953,142953,87,110167,1024,69,87,110167,69,69,110167,81,110167,81,110167,69,110167,69,110167,11,110167,110165,110167,1026,110167,110163,142953,142953,142953,142953,85,110165,11,69,85,110165,69,69,110165,110165,81,110165,110165,81,110165,11,69,110165,69,69,110165,11,110165,110163,142953,142953,142953,142953,83,110163,1028,69,83,110163,69,69,110163,81,110163,81,110163,69,110163,69,142953,142953,142953,142953]
def row516 : List ℕ := [105,180398697,184594025,244]
def row517 : List ℕ := [180398697,105,184594025,244]
def row518 : List ℕ := [142419,25,142419,514,464,163623017]
def row519 : List ℕ := [0,244,25,74293,74293]
def row520 : List ℕ := [0,0,25,25]
def row521 : List ℕ := [0,0,0,75317,75317,75317]
def row522 : List ℕ := [0,0,110185,53]
def row523 : List ℕ := [244,74293]
def row524 : List ℕ := [142419,1046,75317]
def row525 : List ℕ := [142419,142423,142423,514]
def row526 : List ℕ := [0,74293]
def row527 : List ℕ := [25,142419,746,142423,1052]
def row528 : List ℕ := [142419,53,142419,0,746,882,583085143]
def row529 : List ℕ := [25,142419,0,583085655]
def row530 : List ℕ := [44649,1032,142423,142423,142423,142423,1034,44137,142423,1036,142423,45161,142423,45161,45161,53,44137,44137,142421,412,142421,0,142419,142419,1038,1040,142419,1042,1044,1048,1050,1054,1056,1058,142417,576,142417]
def row531 : List ℕ := [180399721,44137,180399721,142423,142423,180398697,0,0,0,0,382]
def row532 : List ℕ := [105,180399721]
def row533 : List ℕ := [0,41521]
def row534 : List ℕ := [0,0,1066]
def row535 : List ℕ := [0,142423,77929,142417]
def row536 : List ℕ := [0,0,142423,110697]
def row537 : List ℕ := [25,0,502,0,583085655,105]
def row538 : List ℕ := [142419,25,142423,1066,382]
def row539 : List ℕ := [44649,105,142419]
def row540 : List ℕ := [583085655,49]
def row541 : List ℕ := [0,142423,143465,142421]
def row542 : List ℕ := [142423,43625,44137,1032,142423,1032,142423,142423,1062,142423,1064,142423,44649,142423,1068,44649,44649,44649,105,43625,105,105,44649,44649,44649,142421,1070,142421,0,142419,1072,142419,1074,1076,382,1078,1080,142417,1082,142417]
def row543 : List ℕ := [583052373,69,382,0,0,0,11,11,180394089,142423,583052373,0,384,583052373,0,583052373,583052373,2388182209617]
def row544 : List ℕ := [583052371,69,25,25,25,0,0,25,180396137,142423,583052371,0,596,583052371,0,25]
def row545 : List ℕ := [583052369,69,382,0,180398185,142423,583052369,0,540,583052369,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row546 : List ℕ := [105,44137,44137,142423,105,44137,44649,69,142423,142423,142423,44137,142423,608,142423,142423,1086,142423,142423,142423,142423,142423,1088,142423,142423,142423,142423,142423,1090,142423,142423,142423,142423,583052373,618,583052373,620,583052373,616,583052373,382,583052373,396,583052373,583052371,583052373,11,583052373,583052369,583052371,626,628,583052371,630,632,583052371,622,583052371,624,583052371,396,583052371,583052369,583052369,636,583052369,638,583052369,634,583052369,382]
def row547 : List ℕ := [142419,69,25,142419,592,583052371]
def row548 : List ℕ := [105,44137,45161,105,44649,69,142423,142423,142423,69,142423,69,142423,1064,11,142423,1094,142423,11,142423,45161,142423,44137,44137,142421,11,142421,11,583052373,11,583052373,69,142419,434,142419,646,583052371,644,583052371,69,142417,11,142417,11,583052369,11,583052369,69]
def row549 : List ℕ := [143447,43625,69,44137,69,142423,142423,142423,142423,44649,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,142423,583052885,69,583052885,69,583052885,11,583052885,11,583052885,11,583052885,583052883,583052885,11,583052885,583052881,583052883,710,69,583052883,69,69,583052883,706,583052883,708,583052883,11,583052883,583052881,583052881,69,583052881,69,583052881,11,583052881,11]
def row550 : List ℕ := [583052373,69,382,0,0,0,11,11,583052373,0,180394089,142423,384,583052373,0,583052373,583052373,2388182209617]
def row551 : List ℕ := [142423,384,155267177,583046225]
def row552 : List ℕ := [410,412,0,0,69,11,11,69,142419,0,0,142419,142417,11,11,142417,38505,142421,142423,142423,142423,142421,1100,142423,11,142423,142423,11,142423,39017,142423,1102,142421,11,142421,396,142421,142421,583046225,37993,37993,406,11]
def row553 : List ℕ := [25,0,0,25]
def row554 : List ℕ := [25,502,0,0,583085655,105]
def row555 : List ℕ := [142419,25,142419,506,464,163623017]
def row556 : List ℕ := [583052371,69,25,25,25,0,0,25,583052371,0,180396137,142423,448,583052371,0,25]
def row557 : List ℕ := [142423,25,142423,514,448,163688553]
def row558 : List ℕ := [583085143,69,25,25,25,0,0,25,583085143,0,448831081,142419,464,583085143,0,25]
def row559 : List ℕ := [25,25,25,1106,25,25,25,1108,69,440,25,434,25,69,25,69,142417,0,25,142417,40553,142419,142423,142423,142423,142423,142419,1110,142423,1112,142423,512,142423,142423,41065,142423,1114,142419,1116,142419,520,142419,142419,40041,40041,142421,0,142421,25]
def row560 : List ℕ := [583052369,69,382,0,583052369,0,180398185,142423,540,583052369,11,11,2388182211669,2388182211669,0,0,0,583052369]
def row561 : List ℕ := [142423,540,172109929,583048277]
def row562 : List ℕ := [410,576,0,0,69,11,11,69,42601,142417,142423,142423,142423,142417,1120,142423,11,142423,142423,11,142423,43113,142423,1122,142417,11,142417,42089,42089,142421,11,142421,11,583048277,583048277,142419,0,142419,0,396,142417,406,11]
def row563 : List ℕ := [105,318844521,11]
def row564 : List ℕ := [142419,748,297873513,583081041]
def row565 : List ℕ := [0,44649,51]
def row566 : List ℕ := [0,110185,51]
def row567 : List ℕ := [142419,51,142419,0,748,583117905]
def row568 : List ℕ := [108083,108083,0,11,0,11]
def row569 : List ℕ := [142417,108083]
def row570 : List ℕ := [77417,1126,142421,142421,142421,1126,1128,142421,77929,142421,77929,77929,51,76905,76905,142423,412,142423,1130,1102,142421,616,11,142419,770,142419,1132,1134,11,142417,142417,11,11,142417,1136,11,1138,11,11]
def row571 : List ℕ := [142421,76393,76905,1126,142421,1126,142421,142421,11,142421,142421,11,77417,105,76393,105,77417,77417,142423,0,142423,0,382,11,142419,0,142419,0,746,11,142417,11,142417,11,11,11]
def row572 : List ℕ := [583085141,69,746,0,11,11,583085141,0,448863849,142419,748,583085141,583085141,2388450679889,0,0,0,583085141]
def row573 : List ℕ := [768,770,0,0,69,11,11,69,142417,11,11,142417,73321,142419,142421,142421,142421,142419,1128,142421,11,142421,142421,583081041,73833,142421,1144,142419,11,142419,142419,11,142419,72809,72809,142423,0,142423,0,382,142421,396,11]
def row574 : List ℕ := [105,448899689,453095017,244]
def row575 : List ℕ := [448899689,105,453095017,244]
def row576 : List ℕ := [0,244,25,41521,41521]
def row577 : List ℕ := [0,0,0,42545,42545,42545]
def row578 : List ℕ := [0,0,44649,49]
def row579 : List ℕ := [142423,1046,42545]
def row580 : List ℕ := [142419,142423,142423]
def row581 : List ℕ := [142423,142423,1160,142419]
def row582 : List ℕ := [25,142423,1066,382,142419]
def row583 : List ℕ := [142423,49,142423,0,596,382,583052371]
def row584 : List ℕ := [25,142423,0,583052883]
def row585 : List ℕ := [110185,1148,142419,142419,142419,142419,1150,109673,142419,110697,142419,110697,110697,49,109673,109673,142423,142423,1152,1040,142423,1154,1156,1158,1114,142419,1162,1164,1166,1168,142421,770,142421,0,142417,864,142417]
def row586 : List ℕ := [448900713,109673,448900713,142419,142419,448899689,0,0,746]
def row587 : List ℕ := [105,448900713]
def row588 : List ℕ := [0,0,583085655,45161]
def row589 : List ℕ := [0,0,1052]
def row590 : List ℕ := [142423,1052,25,142419,746]
def row591 : List ℕ := [0,0,142423]
def row592 : List ℕ := [110185,105,142423]
def row593 : List ℕ := [583085655,53]
def row594 : List ℕ := [0,583085653,77929,142417]
def row595 : List ℕ := [0,142419,143465,142421]
def row596 : List ℕ := [142419,109161,109673,1148,142419,1148,142419,142419,1172,142419,1174,142419,110185,110185,110185,110185,105,109161,105,105,110185,110185,110185,142423,1176,142423,1108,142419,1178,1180,1182,1184,1186,142421,1188,142421,0,142417,1190,142417]
def row597 : List ℕ := [583117905,69,746,0,448899177,142419,583117905,0,836,583117905,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row598 : List ℕ := [44649,43625,583085143,436,583052883,583085143,583085143,0,583085143,583085655]
def row599 : List ℕ := [583085143,69,25,25,25,0,0,25,448831081,142419,583085143,0,882,583085143,0,25]
def row600 : List ℕ := [583085141,69,746,0,11,11,448863849,142419,583085141,0,748,583085141,583085141,2388450679889,0,0,0,583085141]
def row601 : List ℕ := [105,109673,109673,142419,105,109673,110185,69,142419,142419,142419,109673,142419,878,142419,142419,1194,142419,142419,142419,142419,583085143,440,888,583085143,1196,892,583085143,1198,142419,583085143,142419,142419,583085143,884,583085143,886,583085143,406,583085143,583085141,583085143,406,583085143,583117905,583085141,898,583085141,900,583085141,1200,142419,583085141,142419,142419,583085141,896,583085141,746,583085141,11,583085141,583117905,583117905,906,583117905,908,583117905,904,583117905,746]
def row602 : List ℕ := [105,109673,110697,105,110185,69,142419,142419,142419,69,142419,69,142419,1174,11,142419,110697,142419,109673,109673,142423,434,142423,916,520,142419,583085143,914,583085143,69,142421,11,142421,11,11,142419,583085141,11,583085141,69,142417,11,142417,11,583117905,11,583117905,69]
def row603 : List ℕ := [583085655,49,583085655,69,583052371,583085655,583085655,0,11,583085655,11,583085655,583085143,583085655]
def row604 : List ℕ := [143443,109161,69,109673,69,142419,142419,142419,142419,110185,142419,142419,142419,142419,583085655,1206,69,583085655,69,69,583085655,142419,583085655,142419,583085655,984,583085655,986,583085655,11,583085655,583085653,583085655,11,583085655,583118417,583085653,69,583085653,69,583085653,142419,583085653,142419,583085653,11,583085653,11,583085653,11,583085653,583118417,583118417,69,583118417,69,583118417,11,583118417,11]
def row605 : List ℕ := [583117905,69,746,0,583117905,0,448899177,142419,836,583117905,0,0,0,583117905,11,11,2388316462165,2388316462165]
def row606 : List ℕ := [142419,836,440545385,583081045]
def row607 : List ℕ := [768,864,0,0,69,11,11,69,108137,142417,142419,142419,142419,142417,1210,142419,11,142419,142419,108649,142419,1212,142417,11,142417,107625,107625,142423,0,142423,0,382,142417,396,11,142421,11,142421,11,11,142419,583081045,583081045]
def row608 : List ℕ := [105,587345513,11]
def row609 : List ℕ := [0,44649,47]
def row610 : List ℕ := [75311,75311,0,11,0,11]
def row611 : List ℕ := [142421,75311]
def row612 : List ℕ := [0,110185,47]
def row613 : List ℕ := [142953,1216,142417,142417,142417,1216,143465,142417,143465,143465,47,142441,142441,142423,576,142423,1218,1122,142417,634,11,142421,142421,11,11,142421,1220,11,1222,11,11,142419,864,142419,1224,1212,142417,904,11]
def row614 : List ℕ := [142417,141929,142441,1216,142417,1216,142417,142417,11,142417,142953,105,141929,105,142953,142953,142423,0,142423,0,382,11,142421,11,142421,11,142417,11,11,11,142419,0,142419,0,746,11]
def row615 : List ℕ := [105,105,105,142423,1060,142423,1084,142423,1092,1096,142423,1098,69,142423,1104,142423,142421,142423,1118,142423,142419,142423,1124,142423,142417,142421,1140,142421,1142,142421,11,142421,69,142421,1146,142421,142419,142421,11,142421,142417,142419,1170,142419,1192,142419,1202,1204,142419,1208,69,142419,1214,142419,142417,142417,1226,142417,1228,142417,11,142417,69]
def row616 : List ℕ := [87,420,87,85,87,524,87,83,87,584,87,81,105,105,105,105,87,698,87,722,85,778,85,83,85,786,85,81,105,105,105,105,85,802,85,826,83,872,83,81,105,105,105,105,83,976,83,1000,105,105,105,105,81,1014,81,1030,105,1230,105,105,105,105]
def row617 : List ℕ := [61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,61,59,59,59,59,59,59,59,59,57,47,57,57,57,57,59,59,59,59,57,57,57,57,47,47,47,47]
def row618 : List ℕ := [15]
def row619 : List ℕ := [39,39,37]
def row620 : List ℕ := [37,25,37,1238]
def row621 : List ℕ := [37,15,37,1238]
def row622 : List ℕ := [39,37,39]
def row623 : List ℕ := [39,25,39,1244]
def row624 : List ℕ := [39,15,39,1244]
def row625 : List ℕ := [25,1236,0,25,15,300,0,15,39,37,39,39,39,39,37,1240,39,1242,39,39,39,1246,37,1248,37]
def row626 : List ℕ := [37]
def row627 : List ℕ := [37,25,37,1244]
def row628 : List ℕ := [39,39,25]
def row629 : List ℕ := [25,15,25,1256]
def row630 : List ℕ := [39,25,39]
def row631 : List ℕ := [39,15,39,1260]
def row632 : List ℕ := [37,39,39,1244]
def row633 : List ℕ := [15,1252,0,15,39,25,39,39,39,39,25,1254,39,1258,39,39,39,1262,25,37,1236,37,0,1264,25]
def row634 : List ℕ := [37,15,37,1244]
def row635 : List ℕ := [25,15,25,1260]
def row636 : List ℕ := [25,39,39,1260]
def row637 : List ℕ := [39,15,39,39,39,39,15,1268,39,1270,39,39,39,37,300,37,0,1264,15,25,1252,25,0,1272,15]
def row638 : List ℕ := [39]
def row639 : List ℕ := [37,37,25]
def row640 : List ℕ := [25,15,25,1278]
def row641 : List ℕ := [37,25,37]
def row642 : List ℕ := [37,15,37,1282]
def row643 : List ℕ := [37,39,39]
def row644 : List ℕ := [39,39,1286,37]
def row645 : List ℕ := [15,1276,0,15,37,25,37,37,37,37,25,1280,37,37,37,1284,25,39,1236,39,0,1246,37,1288,25]
def row646 : List ℕ := [25,15,25,1282]
def row647 : List ℕ := [25,37,37,1282]
def row648 : List ℕ := [37,15,37,37,37,37,15,1292,37,37,37,39,300,39,0,1248,37,1288,15,25,1276,25,0,1294,15]
def row649 : List ℕ := [25,39,39]
def row650 : List ℕ := [39,39,1298,25]
def row651 : List ℕ := [25,37,37]
def row652 : List ℕ := [37,37,1302,25]
def row653 : List ℕ := [25,15,25,25,25,25,15,25,25,39,1252,39,0,1262,25,1300,15,37,1276,37,0,1284,25,1304,15]
def row654 : List ℕ := [39,1250,39,37,39,1266,39,25,39,1274,39,15,37,1290,37,25,37,1296,37,15,25,1306,25,15]
def row655 : List ℕ := [65,65,65,65,65,65,65,65,65,65,65,65,65,65,63,63,63,63,59,59,59,59,63,51,63,63,63,63,65,65,65,65,63,63,63,63,59,59,59,59,51,51,51,51]
def row656 : List ℕ := [17]
def row657 : List ℕ := [13]
def row658 : List ℕ := [1236,43]
def row659 : List ℕ := [41515]
def row660 : List ℕ := [43,43,15,15,15,15,1318,15,15]
def row661 : List ℕ := [17,15,15,17,43,43,43,15,43,43,15,15,15,15,15,15,15,15,43,43,43,43,17,1312,17,13,17,1314,17,1316,43,43,43,43,13,1312,13,1316,43,1320,43,43,43,43]
def row662 : List ℕ := [73795,57,37,37,37,37,37,72771,1252]
def row663 : List ℕ := [1252,57,27,67]
def row664 : List ℕ := [75843,57,37,37,37,37,37,74819,1252]
def row665 : List ℕ := [67,37,67,67,67,67,57,57,57,37,57,57,37,37,37,37,37,37,37,37,67,67,67,67,67,67,67,67,67,67,67,67,57,1324,57,57,57,57,27,1326,27,19,57,1328,57,57,57,57]
def row666 : List ℕ := [103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,103,101,101,101,101,101,101,101,101,101,101,101,101,101,101,101,101,97,97,97,97,97,97,97,97,97,97,97,97,93,93,93,93,85,85,85,85,93,79,93,93,93,93]
def row667 : List ℕ := [286,45]
def row668 : List ℕ := [41517]
def row669 : List ℕ := [11,11,11,1336,11,45,45,11,11]
def row670 : List ℕ := [21]
def row671 : List ℕ := [21,1312,1334,21,45,1338,45,45,45,45,17,1340,1334,17,11,11,11,11,21,1340,21,17,21,11,21,11,45,45,45,45,45,45,45,45,45,45,45,45,11,45,17,11,17,11]
def row672 : List ℕ := [67,67,67,67,59,59,59,59,55,55,55,55,45,45,45,45,67,67,67,67,67,67,67,67,67,67,67,67,67,67,59,59,59,59,55,55,55,55,59,45,59,59,59,59]
def row673 : List ℕ := [73795,63,39,39,39,39,39,72771,1276]
def row674 : List ℕ := [1276,63,31,67]
def row675 : List ℕ := [75843,63,39,39,39,39,39,74819,1276]
def row676 : List ℕ := [67,39,67,67,67,67,63,63,63,39,63,63,39,39,39,39,39,39,39,39,67,67,67,67,67,67,67,67,67,67,67,67,63,1346,63,63,63,63,31,1348,31,21,63,1350,63,63,63,63]
def row677 : List ℕ := [41]
def row678 : List ℕ := [1276,65]
def row679 : List ℕ := [41537]
def row680 : List ℕ := [65,65,39,39,39,39,1358,39,39]
def row681 : List ℕ := [41,39,39,41,65,65,65,39,65,65,39,39,39,39,39,39,39,39,65,65,65,65,41,1354,41,33,41,318,41,1356,65,65,65,65,33,1354,33,1356,65,1360,65,65,65,65]
def row682 : List ℕ := [1252,61]
def row683 : List ℕ := [74301]
def row684 : List ℕ := [61,61,37,37,37,37,1366,37,37]
def row685 : List ℕ := [41,37,41,37,61,61,61,61,41,1354,41,29,41,320,41,1364,61,61,61,37,61,61,37,37,37,37,37,37,37,37,61,61,61,61,29,1354,29,1364,61,1368,61,61,61,61]
def row686 : List ℕ := [99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,97,97,97,97,97,97,97,97,97,97,97,97,97,97,97,97,95,95,95,95,95,95,95,95,95,95,95,95,89,89,89,89,81,81,81,81,89,75,89,89,89,89]
def row687 : List ℕ := [19]
def row688 : List ℕ := [45,1338,45,45,45,45,19,1314,1334,19,13,1374,1334,13,11,11,11,11,45,45,45,45,45,45,45,45,45,45,45,45,11,45,19,1374,19,13,19,11,19,11,13,11,13,11]
def row689 : List ℕ := [21,15,15,21,19,15,15,19,43,43,43,15,43,43,15,15,15,15,21,1340,21,19,43,43,43,43,21,1374,21,1316,43,43,43,43,19,1340,19,1316,43,1320,43,43,43,43]
def row690 : List ℕ := [73]
def row691 : List ℕ := [75,0,73]
def row692 : List ℕ := [79,15]
def row693 : List ℕ := [69,109641]
def row694 : List ℕ := [73,0,69]
def row695 : List ℕ := [73,15,73,15,0,1380,15,73,69,1382,0,69,38991,1384,1386,37965,38479,21,37967,15,15,37967,75,1388,75]
def row696 : List ℕ := [37961,0,38479,37965,1384,38479,15]
def row697 : List ℕ := [15,79]
def row698 : List ℕ := [71]
def row699 : List ℕ := [1394,37967,75,0,1396,75,73,15,15,73,69,0,0,69,37965,15,38991,79,37455,79,15,37965,79,38991,79,38991,38991,38991,15,38991]
def row700 : List ℕ := [37455,1394,37965,79,71]
def row701 : List ℕ := [69,0,77]
def row702 : List ℕ := [69,330]
def row703 : List ℕ := [79,11,40015]
def row704 : List ℕ := [77,1388,0,77,73,1402,0,73,69,11,69,11,0,1404,11,69,41039,1406,11,37963,40527,45,11,11,40015,1406,40015,40015,40015,40015,37963,11,40015]
def row705 : List ℕ := [79]
def row706 : List ℕ := [11,0,40527,37963,1406,40527,1410,40015]
def row707 : List ℕ := [11,79,40015]
def row708 : List ℕ := [1414,40015,77,0,1396,77,73,0,1396,73,69,11,11,69,37963,11,41039,79,39503,79,1410,37963,11,11,79,37963,41039,37963,79,41039,41039,41039,41039,41039,37963,11,41039]
def row709 : List ℕ := [40015]
def row710 : List ℕ := [39503,1414,37963,41039,79,1418,37963,79,37963]
def row711 : List ℕ := [77,0,75]
def row712 : List ℕ := [69,142413]
def row713 : List ℕ := [77]
def row714 : List ℕ := [69,1422,0,69,43087,1384,1424,37961,42575,17,42063,15,15,42063,77,77,15,15,77,0,15,1426,75,1402,75]
def row715 : List ℕ := [42575,37961,1384,42575,15,37965]
def row716 : List ℕ := [1384,42063,79,43087,43087,79,77,15,15,77,75,0,1396,75,69,0,0,69,43087,79,41551,79,15,37961,43087,43087,15,43087,37961,15]
def row717 : List ℕ := [41551,79,71,1384,37961]
def row718 : List ℕ := [79,43053]
def row719 : List ℕ := [79,11]
def row720 : List ℕ := [75]
def row721 : List ℕ := [45135,1436,44623,11,11,11,44111,1438,77,1382,77,0,75,75,11,11,75,0,11,1440,73,1422,73]
def row722 : List ℕ := [44623,11,1436,44623,1410,37963]
def row723 : List ℕ := [1436,44111,77,1380,0,77,75,11,11,75,73,1426,0,73,45135,79,43599,79,1410,11,11,11,79,45135,79,45135,45135,45135,43053,43053]
def row724 : List ℕ := [446736975]
def row725 : List ℕ := [43599,1448]
def row726 : List ℕ := [43599,1436,11,45135,79,0,79,71,1450]
def row727 : List ℕ := [40015,1418]
def row728 : List ℕ := [37963,1418]
def row729 : List ℕ := [11,11,41039,71,1454,37963,1454,37963,11,37963,79,79,40015,79,75,37963,75,1418,75,11,11,79,40015,79,1418,40015,40015,40015,40015,37963,40015,71,1456,40015,1456,40015,11,40015]
def row730 : List ℕ := [71,71,79,40015,79,40527,75,1410,79,1410,40015]
def row731 : List ℕ := [71,40015,38475,39503,79,37963,79,41039,79,11,71,75,75,11,11,41039,37963,41039,71,15,41039,15,41039,11,41039]
def row732 : List ℕ := [45135,71,79,79,44111,79,69,11,69,0,69,11,11,79,44111,79,0,11,44111,44111,71,0,44111,44111,180393035,0,44111,0,11,11,11,0,11]
def row733 : List ℕ := [71,44111,71,79,44111,79,44623,69,1410,79,1410]
def row734 : List ℕ := [71,44111,71,43599,45135,79,71,79,11,71,69,69,11,11,11,45135,45135,71,15,45135,45135,155234379,15,45135]
def row735 : List ℕ := [71,37963]
def row736 : List ℕ := [79,1418]
def row737 : List ℕ := [15,15,1470,0,79,79,0,37965,77,37965,77,71,77,37965,77,0,77,15,15,71,21,71,21,79,79,1456,15,0,15,37963,37963,1472,37965]
def row738 : List ℕ := [1470,0,79,79,0,37961,73,37961,73,71,73,37961,73,0,73,15,15,71,17,71,17,79,79,1456,15,0,15,15,15,37963,37963,1472,37961]
def row739 : List ℕ := [79,79,71,71,69,71,69,69,11,69,1450,69,11,11,71,11,71,11,11,11,79,79,11,11,1470,11,37963,37963,11,37963,11,11,11,1470,11]
def row740 : List ℕ := [69,71]
def row741 : List ℕ := [1480,1382,0,0,1386,77,0,1470,79]
def row742 : List ℕ := [19,1388,1396,19,1454,79,1396,1472]
def row743 : List ℕ := [13,1402,1396,13,1454,79,1396,1472]
def row744 : List ℕ := [1480,1422,0,0,1424,73,0,1470,79]
def row745 : List ℕ := [77,37965,1390,1392,1398,1400,77,37965,75,37963,1408,1412,1416,1420,75,37963,73,37961,1428,1430,1432,1434,73,37961,69,11,1442,1444,1446,1452,69,11,79,79,79,79,79,79,71,79,79,79,37965,15,71,37965,37963,1458,1460,1462,71,37963,37961,15,71,37961,71,1464,1466,1468,71,11,79,71,79,79,1474,79,79,79,79,79,79,79,79,37963,79,79,1476,79,79,79,79,79,1478,79,79,79,79,37965,15,37965,37961,37965,1482,37965,11,37965,1484,37963,37965,37963,1486,37963,37961,37963,11,37963,11,37961,1488,37961,11]
def row746 : List ℕ := [11,40015]
def row747 : List ℕ := [163622991,71,15,15,15,15]
def row748 : List ℕ := [15,15,15,15,15,15,15,15,11,1492,0,11,40015,40015,40015,38987,40015,40015,40015,40015,71,71,71,71,71,71,71,71,71,1494,71,71,71,71,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,40015,15,15,15,15,15,15,15,15,15,15,15,15]
def row749 : List ℕ := [77,15,15,77,73,15,15,73,69,11,11,69,41039,71,38987,15,38987,15,38987,15,38987,15,38987,11,38987,11,79,40015,79,40527,38987,40015,71,38987,11,71,79,40015,79,40015,40015,40015,40015,40015]
def row750 : List ℕ := [45135,71,79,44111,79,44623,71,71,71,44111,11,71,79,44111,79,44111,44111,44111,77,15,77,15,15,15,75,11,75,11,73,15,73,15,15,15]
def row751 : List ℕ := [11,11,41039,71,15,38987,15,38987,11,38987,40527,37451,75,40015,75,38987,75,71,40015,11,71,79,79,40015,40015]
def row752 : List ℕ := [45135,71,44623,11,71,69,71,44111,1494,71,11,71,71,79,79,15,15,11,11,15,15]
def row753 : List ℕ := [79,79,79,71,79,79,77,38989,15,71,71,71,77,38989,75,38987,1496,71,1498,71,71,71,75,71,75,38987,73,38985,15,71,71,71,73,38985,71,71,1500,71,71,71,69,71,79,79,71,79,79,79,79,38989,71,71,38989,38987,1502,71,71,71,38987,38985,71,71,38985,71,1504,71,71,71,71,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,38989,15,38989,38985,38989,15,38989,15,38989,15,38987,38989,38987,15,38987,38985,38987,11,38987,11,38985,15,38985,15]
def row754 : List ℕ := [0,15,0,75847,0,43085]
def row755 : List ℕ := [15,15,15,15,43085,43085,40009,43085,43085,43085,43085,43085,75847,15,75847,15,75847,15,75847,15,75847,15,75847,15,43085,43085,43085,43085,43085,43085,43085,43085,15,15,15,15,43085,43085,43085,43085,1508,0,0,0,1508,0,0,0,15,15,15,15,43085,43085,43085,43085,1508]
def row756 : List ℕ := [79,42539]
def row757 : List ℕ := [79,0,73]
def row758 : List ℕ := [45133,15,44621,1512,44109,1384,79,1382,79,0,75,1514,75,0,73,73,15,15,73,0,15,1380,15,15]
def row759 : List ℕ := [178299469]
def row760 : List ℕ := [43597,1518]
def row761 : List ℕ := [77,77,71,71,69,71,69,15,69,15,69,109641,15,109641,15,109641,71,71,15,71,1520,15,15,77,77,15,15,1386,15,1386,15,15,15,15,15]
def row762 : List ℕ := [73,15,73,15,0,1380,15,73,69,1382,0,69,37967,15,15,37967,38479,21,38991,1384,1386,37965,75,1388,75]
def row763 : List ℕ := [45,1388,45,15,37967,74825]
def row764 : List ℕ := [15,1382,15,11,76873,0,40011]
def row765 : List ℕ := [74311]
def row766 : List ℕ := [71,1530,71]
def row767 : List ℕ := [69,1380,15,69,77385,0,1532,77]
def row768 : List ℕ := [73,15,73,15,0,1380,15,73,69,1514,0,69,41037,15,15,40011,40525,19,40013,1384,1386,40013,79,1388,79]
def row769 : List ℕ := [15,1514,15,11,142409,0,37967]
def row770 : List ℕ := [69,1380,15,69,142921,0,1532,77]
def row771 : List ℕ := [73,15,73,40009,15,15,1510,15,15,15,73,40009,69,15,1516,15,15,15,69,15,77,77,77,77,77,77,71,77,77,77,37967,15,71,37967,40011,15,71,40011,40009,15,15,15,71,40009,71,15,71,15,77,71,77,77,15,77,77,77,77,77,1522,77,77,77,77,79,37967,1524,15,79,37967,15,15,37967,77,37967,77,37967,1526,37967,40011,37967,15,37967,40009,37967,1528,37967,1534,75,40011,1536,15,75,40011,15,15,77,77,77,77,40011,15,40011,40009,40011,1538,40011,1540,40009,15,40009,15]
def row772 : List ℕ := [69,0,330]
def row773 : List ℕ := [71,69,328]
def row774 : List ℕ := [79,37967,38991,79,75,1544,1396,75,73,15,15,73,69,1440,0,69,38991,71,37965,38991,38991,1396,15,38991,1546,38991,38991,79,37455,79,38991,71]
def row775 : List ℕ := [72271,40013,40013,73807,73,15,15,73,69,1410,0,69,41037,71,40013,40013,15,41035,1546,41035,77,40015,77,40527,41035,71,79,1544,79,1396,41035,1396]
def row776 : List ℕ := [45133,71,77,44111,77,44623,71,71,71,44109,76367,44109,77903,44109,44109,44109,44109,15,79,1440,79,0,75,1410,75,0,73,15,73,15,15,15]
def row777 : List ℕ := [38991,71,1544,71,45]
def row778 : List ℕ := [71,1440,71,11,1546,79,41035]
def row779 : List ℕ := [71,0,71,69]
def row780 : List ℕ := [71,1410,71,11,1546,75,38991]
def row781 : List ℕ := [77,77,77,71,77,77,79,38991,1548,71,71,71,79,38991,75,41035,1550,71,71,71,75,41035,73,41033,15,71,71,71,73,41033,71,71,1552,71,71,71,69,71,77,77,71,77,77,77,77,38991,71,71,38991,41035,71,71,41035,41033,15,71,71,71,41033,71,71,71,71,77,77,77,77,41033,77,77,77,77,77,38991,77,38991,77,38991,1554,38991,41035,38991,15,38991,41033,38991,1556,38991,1558,77,77,77,77,41035,15,41035,41033,41035,1560,41035,1558,41033,15,41033,15]
def row782 : List ℕ := [73,15,73,15,0,1380,15,73,69,1514,0,69,40013,1384,1386,40013,40525,19,41037,15,15,40011,79,1388,79]
def row783 : List ℕ := [42057,0,77,40013,1384,40523,15]
def row784 : List ℕ := [1394,40013,73295,40013,41037,72271,73,15,15,73,69,0,0,69,40013,15,38991,40013,37455,40525,15,40013,41035,40013,15,41035,79,0,79,1396]
def row785 : List ℕ := [77,40013,71,1394,40013]
def row786 : List ℕ := [79,0,77]
def row787 : List ℕ := [69,1572,0,69,43083,1384,1424,42057,42571,13,42059,15,15,42059,79,1402,79,0,77,77,15,15,77,0,15,1426]
def row788 : List ℕ := [42571,42057,1384,42571,15,40013]
def row789 : List ℕ := [1384,42059,108623,43083,43083,107087,77,15,15,77,69,0,0,69,43087,75,41551,75,15,42057,43083,43083,15,43083,79,0,79,1396,42057,15]
def row790 : List ℕ := [41547,75,71,1384,42057]
def row791 : List ℕ := [45131,1436,44619,11,11,11,44107,1438,79,79,11,11,79,0,11,1410,77,1514,77,0,73,1572,73]
def row792 : List ℕ := [44619,11,1436,44619,1410,40015]
def row793 : List ℕ := [1436,44107,77,1380,0,77,73,1426,0,73,45135,75,43599,75,1410,11,11,11,110671,45131,109135,45131,45131,45131,79,11,79,11,43053,43053]
def row794 : List ℕ := [312519243]
def row795 : List ℕ := [43595,1588]
def row796 : List ℕ := [43595,1436,11,45131,75,0,75,71,1590]
def row797 : List ℕ := [79,79,40015,79,75,37963,75,1418,75,11,11,40015,71,79,40015,79,1418,40015,40015,40015,40015,37963,1456,40015,1456,40015,11,40015,11,11,41039,71,1454,37963,1454,37963,11,37963]
def row798 : List ℕ := [79,40015,79,40527,75,1410,71,71,79,1410,40015]
def row799 : List ℕ := [71,40015,40527,37451,75,40015,75,38987,75,11,71,79,79,40015,40015,11,11,41039,71,15,38987,15,38987,11,38987]
def row800 : List ℕ := [45131,71,75,75,44107,75,69,11,69,0,69,75,44107,75,0,11,44107,44107,71,0,44107,0,44107,11,11,11,11,180395087,180395087,0,11,0,11]
def row801 : List ℕ := [71,44107,71,75,44107,75,44619,69,1410,75,1410]
def row802 : List ℕ := [71,44107,71,43595,45131,75,71,75,11,71,69,69,11,45131,45131,71,15,45131,15,45131,11,11,163622991,163622991]
def row803 : List ℕ := [71,40015]
def row804 : List ℕ := [15,15,1606,0,40013,75,0,40013,77,40013,77,71,77,40013,77,0,77,15,15,71,19,71,19,40525,75,1454,15,0,15,40015,40015,1454,40013]
def row805 : List ℕ := [1606,0,75,75,0,42057,73,42057,73,71,73,42057,73,0,73,15,15,71,15,71,13,75,75,1454,15,0,15,40015,40015,1454,42057,15,15]
def row806 : List ℕ := [75,75,71,71,69,71,69,69,11,69,1590,69,71,11,71,11,11,11,75,75,11,11,40015,40015,11,40015,11,11,11,11,11,1606,11,1606,11]
def row807 : List ℕ := [77,1388,0,77,73,1402,0,73,69,11,69,11,0,1404,11,69,40015,1406,40015,40015,40015,40015,37963,11,40015,40527,45,11,11,41039,1406,11,37963]
def row808 : List ℕ := [11,0,40015,1406,40015,79,38475,1410]
def row809 : List ℕ := [77,0,1396,77,73,0,1396,73,69,11,11,69,40015,1414,40015,38987,40015,40015,40015,11,79,40015,79,40527,1410,40015,11,11,79,40015,40015,40015,79,40015,41039,11,38987]
def row810 : List ℕ := [79,1414,40015,40015,40015,75,1418,40015,40015]
def row811 : List ℕ := [21,1388,1396,21,1456,75,1396,1454]
def row812 : List ℕ := [17,1402,1396,17,1456,75,1396,1454]
def row813 : List ℕ := [1480,1514,0,0,1386,77,0,1606,75]
def row814 : List ℕ := [1480,1572,0,0,1424,73,0,1606,75]
def row815 : List ℕ := [77,40013,1564,1566,1568,1570,77,40013,73,42057,1574,1576,1578,1580,73,42057,69,11,1582,1584,1586,1592,69,11,75,75,75,75,75,75,71,75,75,75,40015,1594,1596,1598,71,40015,40013,15,71,40013,42057,15,71,42057,71,1600,1602,1604,71,11,75,71,75,40013,1608,75,75,75,40013,75,1610,75,75,75,75,75,1612,75,75,75,75,79,40015,1614,1616,79,40015,1618,1620,40015,40015,75,40015,40015,75,40015,1622,40015,40013,40015,1624,40015,42057,40015,11,40015,11,40013,15,40013,42057,40013,1626,40013,11,42057,1628,42057,11]
def row816 : List ℕ := [11,37963]
def row817 : List ℕ := [155234379,71,15,15,15,15]
def row818 : List ℕ := [41039,37963,37963,37963,15,15,15,15,15,15,15,15,11,1632,0,11,37963,37963,37963,41039,37963,37963,37963,37963,71,71,71,71,71,71,71,71,71,1634,71,71,71,71,37963,37963,37963,37963,37963,37963,37963,37963,37963,37963,37963,37963,15,15,15,15,15,15,15,15,15,15,15,15]
def row819 : List ℕ := [79,40015,41039,79,77,15,15,77,73,15,15,73,69,11,11,69,41039,71,41039,37963,41039,37963,41039,15,41039,15,41039,15,41039,15,41039,11,41039,11,41039,79,39503,79,41039,37963,71,41039,11,71]
def row820 : List ℕ := [45131,71,75,44111,75,44623,71,71,71,44107,11,71,109135,44107,110671,44107,44107,44107,79,11,79,11,77,15,77,15,15,15,73,15,73,15,15,15]
def row821 : List ℕ := [75,75,11,11,41039,71,41039,37963,15,41039,15,41039,11,41039,38475,39503,79,37963,79,41039,79,71,40015,11,71]
def row822 : List ℕ := [45131,71,44619,11,71,69,71,44107,1634,71,11,71,71,75,75,11,11,15,15,15,15]
def row823 : List ℕ := [75,75,75,71,75,75,79,41039,1636,71,1638,71,71,71,79,71,79,41039,77,41037,15,71,71,71,77,41037,73,43081,15,71,71,71,73,43081,71,71,1640,71,71,71,69,71,75,75,71,75,75,75,75,41039,1642,71,71,71,41039,41037,71,71,41037,43081,71,71,43081,71,1644,71,71,71,71,41037,75,75,41037,75,75,75,75,75,75,75,75,41039,75,41039,75,41039,15,41039,41037,41039,15,41039,43081,41039,11,41039,11,41037,15,41037,43081,41037,15,41037,15,43081,15,43081,15]
def row824 : List ℕ := [45129,15,44617,1512,44105,1384,79,1422,79,0,77,77,15,15,77,0,15,1426,15,15,75,1572,75]
def row825 : List ℕ := [178297417]
def row826 : List ℕ := [43593,1650]
def row827 : List ℕ := [73,73,71,71,69,71,69,15,69,15,69,71,71,15,71,1652,15,15,73,73,15,15,1424,15,15,15,15,15,142413,142413,15,142413,15,1424,15]
def row828 : List ℕ := [69,1422,0,69,42063,15,15,42063,42575,17,43087,1384,1424,37961,77,77,15,15,77,0,15,1426,75,1402,75]
def row829 : List ℕ := [45,1402,45,15,42063,72781]
def row830 : List ℕ := [15,1422,15,11,76877,0,42059]
def row831 : List ℕ := [71,71,1530]
def row832 : List ℕ := [69,1426,15,69,1662,73,77389]
def row833 : List ℕ := [0,15,0,75335,0,41033]
def row834 : List ℕ := [15,15,15,15,41033,41033,42061,41033,41033,41033,41033,41033,75335,15,75335,15,75335,15,75335,15,75335,15,75335,15,41033,41033,42061,41033,41033,41033,41033,41033,15,15,15,15,41033,41033,41033,41033,1666,0,0,0,1666,0,0,0,15,15,15,15,41033,41033,41033,41033,1666]
def row835 : List ℕ := [69,1572,0,69,42059,15,15,42059,42571,13,43083,1384,1424,42057,79,1402,79,0,77,77,15,15,77,0,15,1426]
def row836 : List ℕ := [15,1572,15,11,42063,0,109645]
def row837 : List ℕ := [69,1426,15,69,1662,73,110157]
def row838 : List ℕ := [69,15,1648,15,15,15,69,15,73,73,73,73,73,73,71,73,73,73,42063,15,71,42063,42061,15,15,15,71,42061,42059,15,71,42059,71,15,71,15,73,71,73,73,1654,73,73,73,73,79,42063,1656,15,79,42063,15,15,42063,73,42063,73,42063,15,42063,42061,42063,1658,42063,42059,42063,1660,42063,1664,77,77,15,42061,15,15,77,42061,1668,15,15,15,42061,15,73,42061,73,73,42061,15,42061,15,75,42059,1670,15,75,42059,15,15,42059,73,42059,73,42061,15,42059,42061,42059,1672,42059,1674]
def row839 : List ℕ := [79,42063,43087,79,77,15,15,77,75,1544,1396,75,69,1440,0,69,43087,71,37961,43087,15,43087,43087,1396,1546,43087,43087,79,41551,79,43087,71]
def row840 : List ℕ := [107087,42059,43083,108111,77,15,15,77,69,1410,0,69,43083,71,42057,43083,15,43083,1546,43083,43083,40015,41547,40527,43083,71,79,1544,79,1396,43083,1396]
def row841 : List ℕ := [45129,71,73,44111,73,44623,71,71,71,44105,141903,44105,143439,44105,44105,44105,79,1440,79,0,77,15,77,15,15,15,44105,15,75,1410,75]
def row842 : List ℕ := [43087,71,1544,71,45]
def row843 : List ℕ := [71,1440,71,11,1546,79,43083]
def row844 : List ℕ := [71,1410,71,11,1546,75,43087]
def row845 : List ℕ := [73,73,73,71,73,73,79,43087,1678,71,71,71,79,43087,77,43085,15,71,71,71,77,43085,75,43083,1680,71,71,71,75,43083,71,71,1682,71,71,71,69,71,73,73,71,73,73,73,73,43087,71,71,43087,43085,15,71,71,71,43085,43083,71,71,43083,71,71,71,71,73,73,73,73,43087,73,43087,73,43087,15,43087,43085,43087,1684,43087,43083,43087,1686,43087,1558,43085,43085,73,43085,43085,73,43085,15,43085,15,43083,73,43083,73,43085,15,43083,43085,43083,1688,43083,1558]
def row846 : List ℕ := [69,69,43599,69,15,15,15,15,11,11,11,11,15,15,15,15,71,71,71,43599,71,69,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,69,69,69,69,15,15,15,15,69,69,69,69,15,15,15,15,15,15,15,15,69,69,69,69]
def row847 : List ℕ := [69,69,43597,69,15,15,15,15,71,71,71,43597,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,15,15,15,15,69,69,69,69,11,11,11,11,15,15,15,15,15,15,15,15,69,69,69,69,15,15,15,15,69,69,69,69]
def row848 : List ℕ := [69,69,43595,69,15,15,15,15,15,15,15,15,71,71,71,43595,71,69,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,11,11,11,11,69,69,69,69,15,15,15,15,15,15,15,15,69,69,69,69,15,15,15,15,69,69,69,69]
def row849 : List ℕ := [69,69,43593,69,71,71,71,43593,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,71,15,15,15,15,69,69,69,69,15,15,15,15,11,11,11,11,15,15,15,15,69,69,69,69,15,15,15,15,69,69,69,69,15,15,15,15]
def row850 : List ℕ := [71,71,71,71,69,71,79,43599,1692,71,11,71,71,71,79,71,79,43599,77,43597,1694,71,15,71,71,71,77,71,77,43597,75,43595,1696,71,11,71,71,71,75,71,75,43595,73,43593,1698,71,15,71,71,71,73,71,73,43593,71,69,71,71,71,71,71,43599,71,71,43599,43597,71,71,43597,43595,71,71,43595,43593,71,71,43593,43599,69,43599,69,43599,15,43599,43597,43599,11,43599,43595,43599,15,43599,43593,43597,69,43597,69,43597,15,43597,43593,43595,69,43595,69,43597,15,43595,43597,43595,15,43595,43593,43593,69,43593,69]
def row851 : List ℕ := [79,79,44111,79,69,11,69,0,69,11,11,44111,71,79,44111,79,0,11,44111,0,44111,44111,180393035,0,44111,45135,71,0,11,11,11,0,11]
def row852 : List ℕ := [79,44111,79,44623,69,1410,44111,71,71,79,1410]
def row853 : List ℕ := [71,44111,44623,11,71,69,1494,71,11,71,71,79,79,45135,71,15,15,11,11,15,15]
def row854 : List ℕ := [75,75,44107,75,69,11,69,0,69,44107,71,75,44107,75,0,11,44107,0,44107,0,44107,45131,71,11,11,180395087,180395087,11,11,0,11,0,11]
def row855 : List ℕ := [75,44107,75,44619,69,1410,44107,71,71,75,1410]
def row856 : List ℕ := [71,44107,44619,11,71,69,1634,71,11,71,71,75,75,45131,71,11,11,15,15,15,15]
def row857 : List ℕ := [44111,1438,44623,11,11,11,45135,1436,77,1382,77,0,75,75,11,11,75,0,11,1440,73,1422,73]
def row858 : List ℕ := [44111,1438,79,11,1410,44107]
def row859 : List ℕ := [44111,1438,11,44111,44111,11,79,44111,79,44623,1410,44111,11,11,79,44111,79,45135,77,0,77,0,75,11,75,11,73,0,73]
def row860 : List ℕ := [79,1438,44111,44111,69]
def row861 : List ℕ := [21,1382,21]
def row862 : List ℕ := [17,1422,17]
def row863 : List ℕ := [44109,1384,44621,1512,45133,15,79,1382,79,0,75,1514,75,0,73,73,15,15,73,0,15,1380,15,15]
def row864 : List ℕ := [44109,1384,77,1410,15,44105]
def row865 : List ℕ := [77391,44109,45133,76367,73,15,15,73,44109,1384,1410,44109,44109,15,38991,44109,37455,44621,15,44109,79,0,79,0,75,0,75,0,15,15]
def row866 : List ℕ := [77,44109,71,1384,44109]
def row867 : List ℕ := [44109,69,77,44109,77,0,44109,448834633,77,44109,77,71,77,71,15,71,0,15,44109,44621,69,0,15,0,15,0,44109,0,44109,15,15,15,15]
def row868 : List ℕ := [44109,69,77,1410,77,44109,45133,77,71,1410,69]
def row869 : List ℕ := [583052877,69,11,15,11,15]
def row870 : List ℕ := [45133,15,1738,69,15,69,69,44109,69,77,77,71,71,44621,69,11,15,11,15,15,15]
def row871 : List ℕ := [44107,1438,44619,11,11,11,45131,1436,79,79,11,11,79,0,11,1410,77,1514,77,0,73,1572,73]
def row872 : List ℕ := [44107,1438,75,11,1410,44111]
def row873 : List ℕ := [44107,1438,11,44107,41039,44107,39503,44619,1410,44107,11,11,110159,44107,109135,45131,79,11,79,11,44107,11,77,0,77,0,73,0,73]
def row874 : List ℕ := [75,1438,44107,44107,69]
def row875 : List ℕ := [19,1514,19]
def row876 : List ℕ := [13,1572,13]
def row877 : List ℕ := [44105,1384,44617,1512,45129,15,79,1422,79,0,77,77,15,15,77,0,15,1426,15,15,75,1572,75]
def row878 : List ℕ := [44105,1384,73,1410,15,44109]
def row879 : List ℕ := [1384,44105,142927,44105,45129,141903,77,15,15,77,1410,44105,43087,44105,41551,44617,15,44105,79,0,79,0,44105,15,15,15,75,0,75]
def row880 : List ℕ := [73,44105,71,1384,44105]
def row881 : List ℕ := [44105,69,73,44105,73,0,73,44105,73,71,73,71,15,71,0,15,44105,44617,69,0,15,0,15,0,44105,15,15,583052365,583052365,15,15,0,44105]
def row882 : List ℕ := [44105,69,73,1410,73,44105,45129,73,71,1410,69]
def row883 : List ℕ := [448835145,69,11,15,11,15]
def row884 : List ℕ := [69,44105,45129,15,1766,69,15,69,69,73,73,71,71,44617,69,11,15,11,15,15,15]
def row885 : List ℕ := [69,69,69,71,69,71,71,71,69,69,44111,1702,1704,1706,71,44111,44109,15,71,44109,44107,1708,1710,1712,71,44107,44105,15,71,44105,71,71,71,79,44111,1714,1716,79,44111,1718,1720,44111,11,44111,69,44111,1722,44111,44109,44111,11,44111,44107,44111,1724,44111,44105,77,44109,1726,1728,77,44109,1730,1732,44109,1734,1736,44109,1740,69,44109,15,44109,44105,75,44107,1742,1744,75,44107,1746,1748,44107,11,44107,69,44109,1750,44107,44109,44107,1752,44107,44105,73,44105,1754,1756,73,44105,1758,1760,44105,1762,1764,44105,1768,69]
def row886 : List ℕ := [45135,71,44623,69,71,71,71,69,44111,44111,44107,44107,79,44111,79,44111,77,44109,77,44109,44109,44109,75,44107,75,44107,73,44105,73,44105,44105,44105]
def row887 : List ℕ := [79,44111,45135,79,77,15,15,77,75,11,11,75,73,15,15,73,45135,71,11,45135,15,45135,45135,11,15,45135,45135,79,43599,79,45135,71,11,71]
def row888 : List ℕ := [109135,44107,45131,110159,77,15,15,77,73,15,15,73,45131,71,11,45131,15,45131,15,45131,45131,40015,43595,40527,45131,71,11,71,79,11,79,11,45131,11]
def row889 : List ℕ := [69,69,11,11,45135,71,11,45135,15,45135,45135,155234379,15,45135,71,43599,45135,79,71,79,71,44111,11,71]
def row890 : List ℕ := [69,69,45131,71,11,45131,15,45131,15,45131,71,43595,45131,75,71,75,71,44107,11,71,11,11,163622991,163622991]
def row891 : List ℕ := [71,71,71,71,1772,71,79,45135,1774,71,71,71,79,45135,77,45133,15,71,71,71,77,45133,75,45131,1776,71,71,71,75,45131,73,45129,15,71,71,71,73,45129,71,71,71,71,71,69,71,45135,1778,71,71,71,45135,45133,71,71,45133,45131,1780,71,71,71,45131,45129,71,71,45129,45135,11,45135,69,45135,15,45135,45133,45135,11,45135,45131,45135,15,45135,45129,45133,15,45133,69,45133,15,45133,45129,45131,11,45131,69,45133,15,45131,45133,45131,15,45131,45129,45129,15,45129,69]
def row892 : List ℕ := [44623,69,71,71,71,69,44111,44111,44107,44107,45135,71,79,44111,79,44111,77,44109,77,44109,44109,44109,75,44107,75,44107,73,44105,73,44105,44105,44105]
def row893 : List ℕ := [44621,69,44621,69,44621,15,37455,44109,38991,44621,15,44621,44621,76879,43597,77903,79,11,79,11,11,44621,75,11,75,11,11,44621,73,15,73,15,15,69]
def row894 : List ℕ := [44621,69,77,44621,77,69,44621,448835145,69,43597,71,71,15,44621,44109,69,11,44621,11,44621,15,15,15,69]
def row895 : List ℕ := [44617,69,44617,69,41551,44105,43087,44617,15,44617,44617,142415,43593,143439,79,11,79,11,11,44617,77,15,77,15,44617,15,15,69,75,11,75,11,11,44617]
def row896 : List ℕ := [44617,69,73,44617,73,69,69,43593,71,71,15,44617,44105,69,11,44617,15,15,583052877,583052877,15,69,11,44617]
def row897 : List ℕ := [71,71,71,1784,69,69,71,71,69,69,71,69,71,44623,11,71,44623,44621,15,71,44621,44619,11,71,44619,44617,15,71,44617,79,44623,11,69,79,44623,69,69,44623,69,44623,69,44623,11,44623,44621,44623,11,44623,44619,44623,11,44623,44617,77,44621,1786,69,77,44621,69,69,44621,1788,69,44621,69,69,44621,15,44621,44617,75,44619,11,69,75,44619,69,69,44619,69,44619,69,44621,11,44619,44621,44619,11,44619,44617,73,44617,1790,69,73,44617,69,69,44617,1792,69,44617,69,69]
def row898 : List ℕ := [71,0,75]
def row899 : List ℕ := [75855,21,74831,43,75343,17,71,15,71,15,15,74831,75,0,75,0,69,1796,69]
def row900 : List ℕ := [75343,72777,21,75341,75343]
def row901 : List ℕ := [21,74831,69,0,21,69,388,72777,79,75855,79,75855,75855,75855,75855,79,74319,79,75853,75853,71,15,71,21,72777,15,15,75855,75,0,75,21]
def row902 : List ℕ := [77903,21,76879,1438,77391,11,71,1382,71,0,1470,76879,75,75,11,11,75,0,11,1440,11,76877,73,1796,73]
def row903 : List ℕ := [77391,21,21,77389,77391,72779]
def row904 : List ℕ := [21,76879,77903,79,79,76367,75,11,21,75,73,1426,21,73,79,77903,79,77903,77903,77903,77901,77901,71,0,71,21,0,77903,11,77901]
def row905 : List ℕ := [142413]
def row906 : List ℕ := [142413,1810]
def row907 : List ℕ := [1810,77]
def row908 : List ℕ := [79,79,1812,72777,77,77,74829,77,73,72777,73,21,73,77,74829,77,17,79,79,1814,74829,15,15,15,15,0,72777,0,74829]
def row909 : List ℕ := [109641,1810]
def row910 : List ℕ := [77903,77,79,79,76879,79,69,21,69,21,69,109641,109641,79,76879,79,0,76879,77,1814,76879,0,11,1386,0,0,76879,11,11,11,11,1818,11]
def row911 : List ℕ := [73,15,73,15,0,1380,15,73,69,1382,0,69,38479,21,37967,15,15,37967,38991,1384,1386,37965,75,1388,75]
def row912 : List ℕ := [72777,0,21,21,38991,38989,38991]
def row913 : List ℕ := [73,15,21,73,69,0,21,69,37967,21,38479,38479,38477,38477,79,38479,79,38479,15,38479,38479,79,37455,79,0,38477,75,1410,75,21]
def row914 : List ℕ := [1418,79]
def row915 : List ℕ := [77,37965,77,71,77,37965,77,0,77,15,15,79,79,71,21,71,21,1456,15,0,15,15,15,1470,0,79,79,0,37965,37963,37963,1828,37965]
def row916 : List ℕ := [1418,40015]
def row917 : List ℕ := [21,1388,1396,21,1456,75,1396,1832]
def row918 : List ℕ := [0,21,1382,21]
def row919 : List ℕ := [73,0,0,73,69,11,11,69,73807,21,72783,19,73295,45,11,72781,71,1388,71]
def row920 : List ℕ := [72779,21,73295,73293,73295]
def row921 : List ℕ := [73807,79,79,72271,73,0,21,73,69,11,21,69,72783,21,73805,73805,72779,11,79,73807,79,73807,73807,73807,11,73805,71,0,71,21,1396,72779]
def row922 : List ℕ := [11,11,73807,77,75,72779,75,21,0,72779,79,79,72783,79,75,11,11,79,72783,79,19,72783,77,0,72783,1832,72779,1828,72783]
def row923 : List ℕ := [0,21,0,21,13]
def row924 : List ℕ := [21,1796,21,388,73,388,1812,1818]
def row925 : List ℕ := [73,72777,1798,1800,1802,21,73,72777,69,21,1804,1806,1808,21,69,11,79,77,79,79,79,79,79,79,77,79,79,79,79,79,79,1816,79,79,79,79,79,79,79,79,79,79,79,77,77,77,77,77,1820,77,77,77,77,71,21,1822,1824,71,15,1826,21,79,1830,79,79,79,79,77,77,77,77,72779,1834,15,72779,72777,15,15,72777,15,1836,15,11,75,72779,1838,1840,75,72779,1842,21,77,1844,77,77,77,77,72779,1846,72779,72777,72779,11,72779,11,72777,1848,72777,11]
def row926 : List ℕ := [73,0,0,73,69,11,11,69,73295,45,11,72781,72783,19,73807,21,71,1388,71]
def row927 : List ℕ := [69,11,11,69,108623,45,11,74825,107599,13,108111,17,71,1402,71,0,77,0,77]
def row928 : List ℕ := [77,1388,0,77,73,1402,0,73,69,11,69,11,0,1404,11,69,40527,45,11,11,40015,1406,40015,40015,40015,40015,37963,11,40015,41039,1406,11,37963]
def row929 : List ℕ := [74825,0,45,1388,45,15,37967]
def row930 : List ℕ := [71,1544,71,45,38991]
def row931 : List ℕ := [71,1544,71,45,43087]
def row932 : List ℕ := [72781,45,0,45,43,74831]
def row933 : List ℕ := [77,72781,1852,45,45,45,77,72781,73,74825,1854,45,45,45,73,74825,69,45,11,45,45,45,69,45,79,75,79,79,79,79,79,79,79,75,79,79,79,79,79,79,79,79,79,79,11,79,79,79,79,79,79,79,72781,75,75,72781,75,75,75,75,75,11,75,75,75,75,71,45,1856,45,71,45,45,45,79,79,79,79,75,75,75,75,72781,1858,1860,72781,74825,1658,1862,74825,11,11,11,11,72781,1864,72781,74825,72781,11,72781,11,74825,11,74825,11]
def row934 : List ℕ := [143439,17,142415,1438,142927,11,71,1422,71,0,1470,142415,77,1796,77,0,75,75,11,11,75,0,11,1440,11,76873]
def row935 : List ℕ := [142927,17,17,77385,142927,74827]
def row936 : List ℕ := [143437]
def row937 : List ℕ := [17,142415,143439,79,79,141903,77,1872,17,77,75,11,17,75,79,143439,79,143439,143439,143439,77897,77897,71,0,71,17,0,143439,11,77897]
def row938 : List ℕ := [77,1810]
def row939 : List ℕ := [77,77,74829,77,73,72777,73,21,73,79,79,77,74829,77,17,1876,74829,79,79,1812,72777,15,15,15,15,0,74829,0,72777]
def row940 : List ℕ := [143439,73,79,79,142415,79,69,17,69,17,69,79,142415,79,0,142415,73,1812,142415,0,11,1424,0,0,142415,1812,11,142413,142413,11,11,11,11]
def row941 : List ℕ := [69,1422,0,69,42575,17,42063,15,15,42063,43087,1384,1424,37961,77,77,15,15,77,0,15,1426,75,1402,75]
def row942 : List ℕ := [17,17,43087,38985,43087,74829]
def row943 : List ℕ := [69,0,17,69,42063,17,42575,42575,38473,38473,79,42575,79,42575,15,42575,42575,79,41551,79,0,38473,77,15,77,17,75,1410,75,17]
def row944 : List ℕ := [73,37961,73,71,73,37961,73,0,73,15,15,79,79,71,17,71,17,1456,15,0,15,1470,0,79,79,0,37961,15,15,37963,37963,1828,37961]
def row945 : List ℕ := [17,1402,1396,17,1456,75,1396,1832]
def row946 : List ℕ := [0,17,1422,17]
def row947 : List ℕ := [75343,17,74831,43,75855,21,71,15,71,15,15,74831,75,0,75,0,69,1796,69]
def row948 : List ℕ := [74829,17,75855,73289,75855]
def row949 : List ℕ := [69,0,17,69,74831,17,73801,74829,388,74829,79,75343,79,75343,75343,75343,75343,79,74319,79,71,15,71,17,74829,15,15,75343,75,0,75,17]
def row950 : List ℕ := [77,388,17,1796,17,388,1876,1812]
def row951 : List ℕ := [69,11,11,69,108111,17,107599,13,108623,45,11,74825,71,1402,71,0,77,0,77]
def row952 : List ℕ := [74827,17,108623,75337,108623]
def row953 : List ℕ := [108111,79,79,107087,69,11,17,69,107599,17,75849,74827,74827,11,79,108111,79,108111,108111,108111,11,75849,71,0,71,17,1396,74827,77,0,77,17]
def row954 : List ℕ := [11,11,108111,73,75,74827,75,17,0,74827,79,79,107599,79,75,11,11,79,107599,79,13,107599,73,0,107599,1832,74827,1828,107599]
def row955 : List ℕ := [19,0,19,17]
def row956 : List ℕ := [69,17,1868,1870,1874,17,69,11,79,73,79,79,79,79,79,79,73,79,79,1878,79,79,79,79,79,79,79,79,79,79,79,79,79,79,79,73,1880,73,73,73,73,71,17,1882,1884,71,15,1886,17,79,1888,79,79,79,79,73,73,73,73,74829,15,15,74829,74827,1890,15,74827,15,1892,15,11,77,74829,1894,1896,77,74829,1898,17,74829,73,74829,73,74829,1900,74829,11,75,74827,1902,1904,75,74827,1906,17,74827,1908,73,74827,73,73,74829,1910,74827,74829,74827,11,74827,11]
def row957 : List ℕ := [44623,11,11,11,44111,1438,45135,1436,77,1382,77,0,75,75,11,11,75,0,11,1440,73,1422,73]
def row958 : List ℕ := [71,71,69,71,69,69,11,69,1450,69,11,11,79,79,71,11,71,11,11,11,11,11,79,79,1470,11,37963,37963,11,37963,11,11,11,1470,11]
def row959 : List ℕ := [77391,11,76879,1438,77903,21,71,1382,71,0,1470,76879,75,75,11,11,75,0,11,1440,11,76877,73,1796,73]
def row960 : List ℕ := [76877,43,1796,11,43,107595]
def row961 : List ℕ := [0,11,0,110159,0,75845]
def row962 : List ℕ := [110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,110159,76875,110159,11,11,11,11,110159,110159,110159,110159,75845,11,11,75845,1922,0,0,0,1922,0,0,0,11,11,11,11,75845,11,11,75845,1922,0,0,0,11,11,11,11,75845,11,11,75845]
def row963 : List ℕ := [142927,11,142415,1438,143439,17,71,1422,71,0,1470,142415,77,1796,77,0,75,75,11,11,75,0,11,1440,11,76873]
def row964 : List ℕ := [79,69,79,79,79,79,79,79,69,79,79,79,79,79,79,11,79,79,79,79,79,79,79,79,79,79,79,71,11,1914,11,71,11,11,11,79,1916,79,79,79,79,69,11,11,69,76877,1528,1556,76877,76875,11,11,76875,76873,1660,1686,76873,77,76877,1918,11,77,76877,11,11,76877,11,76877,69,76877,1920,76877,76873,75,75,11,76875,11,11,75,76875,1924,11,11,11,76875,11,11,76875,11,69,76877,11,76875,76877,76875,11,76875,76873,73,76873,1926,11,73,76873,11,11,76873,11,76873,69]
def row965 : List ℕ := [44623,69,44111,44111,69,69,11,11,79,44111,79,44111,69,44111,44111,11,79,44111,79,45135,77,1380,77,0,75,11,75,11,73,1426,73]
def row966 : List ℕ := [1530,74311]
def row967 : List ℕ := [1932,71]
def row968 : List ℕ := [77391,69,77389,69,77389,388,79,76879,79,76879,76879,76879,79,76879,79,77903,71,1380,71,0,1532,77389,75,11,75,11,11,77389,73,1934,73,388]
def row969 : List ℕ := [77389,69,1934,69,43]
def row970 : List ℕ := [142927,69,77385,69,79,142415,79,142415,142415,142415,79,142415,79,143439,71,1426,71,0,1662,77385,77,1934,77,388,77385,388,75,11,75,11,11,77385]
def row971 : List ℕ := [79,79,79,79,69,79,79,79,69,79,79,79,79,79,79,79,79,79,79,79,79,77387,79,79,79,79,79,71,69,1930,69,71,69,69,69,79,79,79,79,69,69,69,69,77389,1534,1558,77389,77387,11,11,77387,77385,1664,1558,77385,77,77389,1936,69,77,77389,69,69,77389,69,77389,69,77389,1938,77389,77385,75,77387,11,69,75,77387,69,69,77387,11,69,77387,69,69,77389,11,77387,77389,77387,11,77387,77385,73,77385,1940,69,73,77385,69,69,77385,69,77385,69]
def row972 : List ℕ := [74831,43,75343,17,75855,21,71,15,71,15,15,74831,75,0,75,0,69,1796,69]
def row973 : List ℕ := [45,0,45,43,74831,72781]
def row974 : List ℕ := [43,1796,11,43,76877,107595]
def row975 : List ℕ := [69,1934,69,43,77389]
def row976 : List ℕ := [71,0,79]
def row977 : List ℕ := [108109,43,107597,13,108621,19,71,15,71,15,15,107595,79,0,79,0,69,1952,69]
def row978 : List ℕ := [43,1952,11,43,109645,74831]
def row979 : List ℕ := [69,1934,69,43,110157]
def row980 : List ℕ := [79,142413,15]
def row981 : List ℕ := [71,1932]
def row982 : List ℕ := [143437,43,142413,1960,142413,142413,142413,142413,109641,142925,1960,71,71,15,15,71,0,15,1962,15,15,15,142413,15,109641,79,1796,79,0,75,1952,75]
def row983 : List ℕ := [77,73,77,77,77,77,77,77,77,73,77,77,77,77,77,77,77,77,73,73,73,73,71,43,15,43,71,43,43,43,77,15,77,77,77,77,73,15,73,73,73,73,74831,15,15,74831,107595,15,15,107595,15,15,15,15,79,74831,1944,43,79,74831,43,43,74831,77,74831,77,74831,73,74831,73,74831,1946,74831,107595,74831,1948,74831,1950,75,107595,1954,43,75,107595,43,43,77,77,77,77,107595,73,107595,73,107595,1956,107595,1958,69,43,1964,43,69,43,43,43]
def row984 : List ℕ := [44621,1512,44109,1384,45133,15,79,1382,79,0,75,1514,75,0,73,73,15,15,73,0,15,1380,15,15]
def row985 : List ℕ := [15,1512,45133,1410,45133,109641]
def row986 : List ℕ := [44109,1512,44621,44621,1410,15,42539,42539,38479,44621,37455,44621,44623,77,43599,77,79,1440,79,0,75,1410,75,0,73,15,73,15,15,15]
def row987 : List ℕ := [1518,43597]
def row988 : List ℕ := [43597,1512,15,1974,0,77,69,44621,77]
def row989 : List ℕ := [71,71,69,71,69,15,69,15,69,109641,15,109641,15,109641,77,77,71,71,15,71,1520,15,15,15,15,77,77,1386,15,1386,15,15,15,15,15]
def row990 : List ℕ := [77,44109,77,71,77,44621,69,71,15,71,0,15,44109,0,15,0,15,77,44109,77,0,44109,69,44109,448834633,0,44109,0,44109,15,15,15,15]
def row991 : List ℕ := [77,44109,45133,77,69,71,1410,77,1410,44109,69]
def row992 : List ℕ := [69,43597,44109,69,71,71,15,44621,77,44621,77,69,44621,69,44621,448835145,11,44621,11,44621,15,69,15,15]
def row993 : List ℕ := [71,69]
def row994 : List ℕ := [1986,1382,0,0,1386,77,0,1470,79]
def row995 : List ℕ := [1986,1514,0,0,1386,77,0,1606,75]
def row996 : List ℕ := [76879,1438,77391,11,77903,21,71,1382,71,0,1470,76879,75,75,11,11,75,0,11,1440,11,76877,73,1796,73]
def row997 : List ℕ := [76879,1438,79,11,77901,109643]
def row998 : List ℕ := [76879,1438,77389,76879,11,76879,76879,11,79,76879,79,77391,79,76879,79,77903,71,0,71,0,75,11,75,11,11,77389,73,0,73,388]
def row999 : List ℕ := [79,1438,76879,0,76879,69]
def row1000 : List ℕ := [79,79,76879,79,69,21,69,21,69,109641,109641,76879,77,79,76879,79,0,1814,76879,77903,77,1386,0,0,76879,0,11,11,11,11,11,1818,11]
def row1001 : List ℕ := [1810,142413]
def row1002 : List ℕ := [17,1796,17,388,1876,2002,77,388]
def row1003 : List ℕ := [110157,1438,109645,11,110669,19,71,1514,71,0,1606,109643,79,79,11,11,79,0,11,1410,11,109645,73,1952,73]
def row1004 : List ℕ := [109643,1438,110669,11,110669,76879]
def row1005 : List ℕ := [109645,1438,110157,110157,11,109643,73807,110157,72271,110157,110159,77,109135,77,71,0,71,0,79,11,79,11,109643,11,11,110157,73,0,73,388]
def row1006 : List ℕ := [109133,1438,109643,0,77,69]
def row1007 : List ℕ := [75,75,109643,75,69,19,69,19,69,109641,109641,77,77,75,109643,75,0,1814,109643,77,77,1386,0,0,109643,0,11,11,11,11,11,1818,11]
def row1008 : List ℕ := [13,1952,13,388,1876,2002,77,388]
def row1009 : List ℕ := [142925,1960,142413,1960,142413,142413,142413,142413,109641,143437,43,71,71,15,15,71,0,15,1962,15,109641,15,142413,15,15,79,1796,79,0,75,1952,75]
def row1010 : List ℕ := [109641,1960,143437,1410,142413,143437,15]
def row1011 : List ℕ := [1960,142413,142927,77,77,141903,1410,109641,75855,109641,142925,109641,74319,142925,142925,142925,142925,142925,109641,71,15,71,15,109641,15,15,142925,15,15,79,0,79,388,75,0,75,388]
def row1012 : List ℕ := [141901,142925,77,1960,109641,1810,109641,77,109641]
def row1013 : List ℕ := [142925,69,73,109641,73,1810,77,77,142413,77,73,77,142413,77,1810,142413,142413,142413,142413,109641,142413,69,15,15,15,109641,15,15,15,142413,2002,109641,1818,142413,2002,109641,1818,142413]
def row1014 : List ℕ := [69,73,1410,77,142413,77,143437,77,1410,142413,69]
def row1015 : List ℕ := [69,142413,110665,141901,77,109641,77,142925,77,73,73,142925,109641,142925,69,15,69,15,15,15,142925,11,142925,11,142925]
def row1016 : List ℕ := [77,69,77,77,77,77,77,77,69,77,77,77,77,77,109641,77,77,77,77,71,15,1968,1970,71,15,1972,1976,77,1978,77,77,77,77,69,1980,1982,15,1984,69,76879,1988,15,76879,109643,1990,15,109643,109641,15,15,109641,79,76879,1992,1994,79,76879,1996,1998,76879,2000,77,76879,77,77,76879,11,76879,69,76879,11,76879,109643,76879,2004,76879,109641,75,109643,2006,2008,75,109643,2010,2012,77,2014,77,77,77,77,109643,11,109643,69,109643,2016,109643,109641,73,109641,2018,2020,73,109641,2022,2024,109641,2026,2028,109641,2030,69]
def row1017 : List ℕ := [15,142413]
def row1018 : List ℕ := [142413,142413,110153,142413,142413,142413,142413,142413,142413,142413,142413,142413,15,2034,15,0,142413,142413,142413,142413,69,1738,69,69,69,69,15,11,15,11,15,11,15,11,11,11,11,11,142413,142413,142413,142413,69,69,69,69,11,11,11,11,11,11,11,11,142413,142413,142413,142413,69,69,69,69]
def row1019 : List ℕ := [77,142415,143439,77,142925,69,110153,142413,110153,69,74319,142413,75855,142413,142413,142413,142413,142413,71,15,71,15,110153,15,15,110153,15,69,79,11,79,11,110153,11,11,110153,75,11,75,11,110153,11,11,110153]
def row1020 : List ℕ := [77,44111,45135,77,73,15,15,73,44621,69,44109,44109,69,69,11,15,11,15,37455,44109,38479,44109,69,44109,79,11,79,11,75,11,75,11,15,69]
def row1021 : List ℕ := [44621,69,71,71,11,15,11,15,45133,15,1738,69,15,69,69,77,77,44109,69,15,15]
def row1022 : List ℕ := [142925,69,143437,109129,73,142413,73,110153,73,77,77,142413,142413,142413,69,15,15,15,110153,15,69,11,110153,11,110153]
def row1023 : List ℕ := [77,77,77,73,110153,2036,69,2038,69,69,69,73,69,73,110153,77,69,77,77,77,69,77,77,77,77,77,77,77,77,71,69,2040,69,71,69,69,69,77,77,77,77,69,2042,69,69,69,69,77391,11,15,77391,110155,11,15,110155,110153,15,15,110153,79,77391,11,69,79,77391,69,69,77391,77,77391,77,77391,69,77391,69,77391,11,77391,110155,77391,11,77391,110153,75,110155,11,69,75,110155,69,69,77,77,77,77,110155,69,110155,69,110155,11,110155,110153,110153,2044,69,110153,69,69]
def row1024 : List ℕ := [108621,19,108109,43,107597,13,71,15,71,15,15,107595,79,0,79,0,69,1952,69]
def row1025 : List ℕ := [108109,107593,19,108109,108107]
def row1026 : List ℕ := [19,107597,69,0,19,69,388,107593,108623,77,107087,77,108619,108619,75855,108621,74319,108621,108621,108621,71,15,71,19,107593,15,15,108619,79,0,79,19]
def row1027 : List ℕ := [110669,19,110157,1438,109645,11,71,1514,71,0,1606,109643,79,79,11,11,79,0,11,1410,11,109645,73,1952,73]
def row1028 : List ℕ := [110157,19,19,110157,110155,72783]
def row1029 : List ℕ := [19,109645,77903,110669,110669,76367,73,1426,19,73,110671,77,109135,77,110667,110667,110669,110669,71,0,71,19,0,110667,79,11,79,19,11,110669]
def row1030 : List ℕ := [108621,75,1812,107593,77,77,107597,77,73,107593,73,19,73,77,107597,77,13,107597,75,1814,107597,15,15,15,15,0,107593,0,107597]
def row1031 : List ℕ := [77,77,75,75,109643,75,69,19,69,19,69,109641,109641,75,109643,75,0,77,77,1814,109643,0,11,1386,0,0,109643,11,11,11,11,1818,11]
def row1032 : List ℕ := [73,15,73,15,0,1380,15,73,69,1514,0,69,40525,19,41037,15,15,40011,40013,1384,1386,40013,79,1388,79]
def row1033 : List ℕ := [107593,0,19,19,41037,41037,41035]
def row1034 : List ℕ := [40527]
def row1035 : List ℕ := [73,15,19,73,69,0,19,69,40013,19,40523,40523,40525,40525,40527,77,39503,77,15,40523,38479,40525,37455,40525,0,40525,79,2068,79,19]
def row1036 : List ℕ := [77,40013,77,71,77,40013,77,0,77,15,15,40525,75,71,19,71,19,1454,15,0,15,15,15,1606,0,40013,75,0,40013,40015,40015,1454,40013]
def row1037 : List ℕ := [0,19,1514,19]
def row1038 : List ℕ := [73,0,0,73,69,11,11,69,72783,19,73807,21,73295,45,11,72781,71,1388,71]
def row1039 : List ℕ := [72783,19,79,73805,73803]
def row1040 : List ℕ := [73,0,19,73,69,11,19,69,72783,19,73291,72783,73293,72783,72783,11,79,72783,79,73807,79,72783,79,73295,11,73293,71,0,71,19,1396,72783]
def row1041 : List ℕ := [79,79,72783,79,75,11,11,72783,77,79,72783,79,19,0,72783,11,11,75,72779,75,21,73807,77,0,72779,1828,72783,1832,72779]
def row1042 : List ℕ := [0,19,0,19,17]
def row1043 : List ℕ := [19,1952,19,388,73,388,1812,1818]
def row1044 : List ℕ := [73,107593,2048,2050,2052,19,73,107593,69,19,2054,2056,2058,19,69,11,77,77,77,77,77,77,75,77,77,77,75,2060,75,75,75,75,75,75,75,75,77,75,77,77,77,77,77,77,2062,77,77,77,77,71,19,2064,2066,71,15,2070,19,75,2072,75,75,75,75,77,77,77,77,72783,1484,15,72783,107593,15,15,107593,15,2074,15,11,79,72783,2076,2078,79,72783,2080,19,72783,75,72783,75,72783,2082,77,72783,77,77,72783,2084,72783,107593,72783,11,72783,11,107593,2086,107593,11]
def row1045 : List ℕ := [143435,13,142411,1438,142923,11,71,1572,71,0,1606,142411,79,79,11,11,79,0,11,1410,11,142409,77,1952,77]
def row1046 : List ℕ := [142923,13,13,142921,142923,107599]
def row1047 : List ℕ := [13,142411,143439,75,75,141903,77,1872,13,77,110671,143435,109135,143435,143435,143435,143433,143433,71,0,71,13,0,143435,79,11,79,13,11,143433]
def row1048 : List ℕ := [77,77,107597,77,73,107593,73,19,73,107597,75,77,107597,77,13,1876,107597,108621,75,1812,107593,15,15,15,15,0,107597,0,107593]
def row1049 : List ℕ := [143435,73,75,75,142411,75,69,13,69,13,69,75,142411,75,0,142411,73,1812,142411,0,11,1424,0,0,142411,11,11,11,11,1812,11,142413,142413]
def row1050 : List ℕ := [69,1572,0,69,42571,13,42059,15,15,42059,43083,1384,1424,42057,79,1402,79,0,77,77,15,15,77,0,15,1426]
def row1051 : List ℕ := [15,13,43083,43081,43083,107597]
def row1052 : List ℕ := [69,0,13,69,42059,13,42571,42571,42569,42569,40527,42571,39503,42571,15,42571,42575,75,41551,75,0,42569,79,2068,79,13,77,15,77,15]
def row1053 : List ℕ := [73,42057,73,71,73,42057,73,0,73,15,15,75,75,71,15,71,13,1454,15,0,15,1606,0,75,75,0,42057,40015,40015,1454,42057,15,15]
def row1054 : List ℕ := [0,13,1572,13]
def row1055 : List ℕ := [69,11,11,69,107599,13,108111,17,108623,45,11,74825,71,1402,71,0,77,0,77]
def row1056 : List ℕ := [107599,13,79,75849,75851]
def row1057 : List ℕ := [69,11,13,69,107599,13,75339,107599,75337,107599,107599,11,79,107599,79,108111,79,107599,79,108623,11,75337,71,0,71,13,1396,107599,77,0,77,13]
def row1058 : List ℕ := [79,79,107599,79,75,11,11,107599,73,79,107599,79,13,0,107599,11,11,75,74827,75,17,108111,73,0,74827,1828,107599,1832,74827]
def row1059 : List ℕ := [21,0,21,13]
def row1060 : List ℕ := [107597,13,108109,43,108621,19,71,15,71,15,15,107595,79,0,79,0,69,1952,69]
def row1061 : List ℕ := [107597,13,77,108617,108619]
def row1062 : List ℕ := [69,0,13,69,107597,13,108105,107597,388,107597,73295,107597,72271,108109,108107,107597,75343,107597,74319,108621,71,15,71,15,107597,15,15,108107,79,0,79,13]
def row1063 : List ℕ := [77,388,13,1952,13,388,1876,1812]
def row1064 : List ℕ := [69,13,2090,2092,2094,13,69,11,75,73,75,75,75,75,75,75,73,75,107597,2096,75,75,75,107597,75,75,75,75,75,75,75,73,2098,73,73,73,73,71,15,2100,2102,71,15,2104,13,75,2106,75,75,75,75,73,73,73,73,107599,1486,15,107599,107597,15,15,107597,15,2108,15,11,79,107599,2110,2112,79,107599,2114,13,107599,75,107599,75,107599,2116,73,107599,73,73,107599,2118,107599,107597,107599,11,107599,11,77,107597,2120,2122,77,107597,2124,13,107597,73,107597,73,107597,2126,107597,11]
def row1065 : List ℕ := [44619,11,11,11,44107,1438,45131,1436,79,79,11,11,79,0,11,1410,77,1514,77,0,73,1572,73]
def row1066 : List ℕ := [71,71,69,71,69,69,11,69,1590,69,75,75,71,11,71,11,11,11,11,11,75,75,11,11,40015,40015,11,40015,11,11,11,1606,11,1606,11]
def row1067 : List ℕ := [0,11,0,77387,0,75333]
def row1068 : List ℕ := [77387,77387,109647,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,77387,109647,77387,11,11,11,11,77387,77387,77387,77387,75333,11,11,75333,2134,0,0,0,2134,0,0,0,11,11,11,11,75333,11,11,75333,2134,0,0,0,11,11,11,11,75333,11,11,75333]
def row1069 : List ℕ := [109645,11,110157,1438,110669,19,71,1514,71,0,1606,109643,79,79,11,11,79,0,11,1410,11,109645,73,1952,73]
def row1070 : List ℕ := [109645,43,1952,11,43,74831]
def row1071 : List ℕ := [142923,11,142411,1438,143435,13,71,1572,71,0,1606,142411,79,79,11,11,79,0,11,1410,11,142409,77,1952,77]
def row1072 : List ℕ := [75,69,75,75,75,75,75,75,69,75,109645,75,75,109645,75,75,75,75,75,75,75,71,11,2130,11,71,11,11,11,75,2132,75,75,75,75,69,11,11,69,109647,11,11,109647,109645,1538,1560,109645,142409,1672,1688,142409,79,79,11,109647,11,11,79,109647,2136,11,11,11,109647,11,75,109647,75,75,109647,11,11,109647,11,69,109647,11,109647,109645,109647,11,109647,142409,77,109645,2138,11,77,109645,11,11,109645,11,109645,69,109645,2140,109645,142409,73,142409,2142,11,73,142409,11,11,142409,11,142409,69]
def row1073 : List ℕ := [44619,69,44107,44107,69,69,11,11,39503,44107,40527,44107,69,44107,75,44111,75,45135,79,11,79,11,44107,11,77,1380,77,0,73,1426,73]
def row1074 : List ℕ := [110157,69,110157,69,110157,388,72271,109645,73295,110157,109643,110157,110157,76879,109133,77903,71,1380,71,0,1532,110157,79,11,79,11,11,110157,73,1934,73,388]
def row1075 : List ℕ := [110157,69,1934,69,43]
def row1076 : List ℕ := [142923,69,142921,69,107087,142411,108623,142411,142411,142411,75,142415,75,143439,71,1426,71,0,1662,142921,79,11,79,11,11,142921,77,1934,77,388,142921,388]
def row1077 : List ℕ := [75,75,75,75,69,75,75,75,69,75,75,75,75,110157,75,75,110157,75,75,75,75,71,69,2146,69,71,69,69,69,75,75,75,75,69,69,69,69,110159,11,11,110159,110157,1540,1558,110157,142921,1674,1558,142921,79,110159,11,69,79,110159,69,69,110159,110159,75,110159,110159,75,110159,11,69,110159,69,69,110159,11,110159,110157,110159,11,110159,142921,77,110157,2148,69,77,110157,69,69,110157,69,110157,69,110157,2150,110157,142921,73,142921,2152,69,73,142921,69,69,142921,69,142921,69]
def row1078 : List ℕ := [44617,1512,44105,1384,45129,15,79,1422,79,0,77,77,15,15,77,0,15,1426,15,15,75,1572,75]
def row1079 : List ℕ := [15,1512,45129,1410,45129,142413]
def row1080 : List ℕ := [44105,1512,44617,44617,1410,15,42539,42539,42575,44617,41551,44617,44623,73,43599,73,79,1440,79,0,77,15,77,15,15,15,75,1410,75]
def row1081 : List ℕ := [43593,1512,15,1652,0,73,69,44617,73]
def row1082 : List ℕ := [71,71,69,71,69,15,69,15,69,73,73,71,71,15,71,1652,15,15,15,15,73,73,1424,15,142413,142413,15,142413,15,15,15,15,15,1424,15]
def row1083 : List ℕ := [73,44105,73,71,73,44617,69,71,15,71,0,15,44105,0,15,0,15,73,44105,73,0,44105,69,0,44105,15,15,15,15,583052365,583052365,0,44105]
def row1084 : List ℕ := [73,44105,45129,73,69,71,1410,73,1410,44105,69]
def row1085 : List ℕ := [69,43593,44105,69,71,71,15,44617,73,44617,73,69,44617,69,11,44617,15,69,15,15,583052877,583052877,11,44617]
def row1086 : List ℕ := [1986,1422,0,0,1424,73,0,1470,79]
def row1087 : List ℕ := [1986,1572,0,0,1424,73,0,1606,75]
def row1088 : List ℕ := [142415,1438,142927,11,143439,17,71,1422,71,0,1470,142415,77,1796,77,0,75,75,11,11,75,0,11,1440,11,76873]
def row1089 : List ℕ := [142415,1438,79,11,77897,142411]
def row1090 : List ℕ := [142415,1438,77385,142415,11,142415,142415,11,79,142415,79,142927,79,142415,79,143439,71,0,71,0,77,0,77,388,75,11,75,11,11,77385]
def row1091 : List ℕ := [79,1438,142415,0,142415,69]
def row1092 : List ℕ := [79,79,142415,79,69,17,69,17,69,142415,73,79,142415,79,0,1812,142415,143439,73,1424,0,0,142415,0,11,142413,142413,1812,11,11,11,11,11]
def row1093 : List ℕ := [142413,1960,142413,142413,142413,142413,109641,142925,1960,143437,43,71,71,15,15,71,0,15,1962,15,142413,15,109641,15,15,79,1796,79,0,75,1952,75]
def row1094 : List ℕ := [142413,1960,142413,77,1410,110665,15]
def row1095 : List ℕ := [77391,142413,143437,76367,142413,1960,142413,110153,142413,142413,1410,142413,75343,142413,142413,142413,74319,142413,142925,71,15,71,15,142413,15,15,110153,15,15,79,0,79,388,75,0,75,388]
def row1096 : List ℕ := [77,142413,73,1960,142413,142413,1810,142413,142413]
def row1097 : List ℕ := [77,77,142413,77,73,142413,69,77,142413,77,1810,142413,142413,142413,142413,109641,73,109641,73,1810,142925,69,15,15,15,142413,15,15,15,109641,1818,142413,2002,109641,1818,142413,2002,109641]
def row1098 : List ℕ := [77,142413,77,143437,69,77,1410,142413,73,1410,69]
def row1099 : List ℕ := [143437,109129,73,142413,73,110153,73,142413,69,77,77,142413,142413,142925,69,15,69,15,15,15,110153,11,110153,11,110153]
def row1100 : List ℕ := [142411,1438,142923,11,143435,13,71,1572,71,0,1606,142411,79,79,11,11,79,0,11,1410,11,142409,77,1952,77]
def row1101 : List ℕ := [142411,1438,75,11,143433,142415]
def row1102 : List ℕ := [142411,1438,142921,142411,11,142411,108111,142411,107087,142923,110159,142411,109135,143435,71,0,71,0,79,11,79,11,142411,11,11,142921,77,0,77,388]
def row1103 : List ℕ := [75,1438,142411,0,142411,69]
def row1104 : List ℕ := [75,75,142411,75,69,13,69,13,69,142411,73,75,142411,75,0,1812,142411,143435,73,1424,0,0,142411,0,11,11,11,11,11,142413,142413,1812,11]
def row1105 : List ℕ := [73,69,73,73,73,73,73,73,69,73,73,73,73,71,15,2156,2158,71,15,2160,2162,73,2164,73,73,73,73,69,2166,2168,15,2170,69,142415,2172,15,142415,142413,15,15,142413,142411,2174,15,142411,79,142415,2176,2178,79,142415,2180,2182,142415,2184,73,142415,73,73,142415,11,142415,69,142415,1848,142415,142413,142415,11,142415,142411,77,142413,2186,2188,77,142413,2190,2192,142413,142413,73,142413,142413,73,142413,2194,2196,142413,2198,69,75,142411,2200,2202,75,142411,2204,2206,142411,2208,73,142411,73,73,142411,11,142411,69,142413,2086,142411,142413]
def row1106 : List ℕ := [109641,0,15]
def row1107 : List ℕ := [142925,109641,109641,109641,109641,109641,142925,109641,109641,109641,109641,109641,15,2212,15,0,109641,109641,109641,109641,69,1766,69,69,69,69,15,11,15,11,15,11,15,11,11,11,11,11,109641,109641,109641,109641,69,69,69,69,11,11,11,11,11,11,11,11,109641,109641,109641,109641,69,69,69,69]
def row1108 : List ℕ := [74319,142413,142925,75343,142925,76879,77903,141901,142925,69,142925,109641,142925,109641,142925,109641,142925,69,71,15,71,15,142925,15,15,142925,15,69,79,11,79,11,142925,11,11,142925,75,11,75,11,142925,11,11,142925]
def row1109 : List ℕ := [41551,44105,44105,42575,73,44111,45135,73,77,15,15,77,44617,69,44105,44105,69,69,11,15,11,15,69,44105,79,11,79,11,15,69,75,11,75,11]
def row1110 : List ℕ := [44617,69,71,71,11,15,11,15,45129,15,69,44105,1766,69,15,69,69,73,73,15,15]
def row1111 : List ℕ := [142925,69,142925,109641,110665,141901,77,109641,77,142925,77,69,142413,73,73,15,15,15,142925,15,69,11,142925,11,142925]
def row1112 : List ℕ := [69,73,73,73,73,73,77,142925,2214,69,2216,69,69,69,77,69,77,142925,73,73,69,73,73,73,73,71,69,2218,69,71,69,69,69,73,73,73,73,69,2220,69,69,69,69,142927,11,15,142927,142925,15,15,142925,142923,11,15,142923,79,142927,11,69,79,142927,69,69,142927,73,142927,73,142927,69,142927,69,142927,11,142927,142925,142927,11,142927,142923,142925,73,142925,73,142925,2222,69,142925,69,69,75,142923,11,69,75,142923,69,69,142923,73,142923,73,142923,69,142923,69,142925,11,142923,142925]
def row1113 : List ℕ := [79,1490,1506,79,77,1542,1562,77,75,1630,1646,75,73,1676,1690,73,1700,1770,1782,1794,79,1850,79,77,79,1866,79,75,79,1912,79,73,79,1928,79,1942,77,1966,77,73,77,2032,77,2046,77,2088,75,77,75,2128,75,73,75,2144,75,2154,73,2210,73,2224]
def group0 (i : ℕ) : List ℕ := (if i≤15 then (if i≤7 then (if i≤3 then (if i≤1 then (if i≤0 then row0 else row1) else (if i≤2 then row2 else row3)) else (if i≤5 then (if i≤4 then row4 else row5) else (if i≤6 then row6 else row7))) else (if i≤11 then (if i≤9 then (if i≤8 then row8 else row9) else (if i≤10 then row10 else row11)) else (if i≤13 then (if i≤12 then row12 else row13) else (if i≤14 then row14 else row15)))) else (if i≤23 then (if i≤19 then (if i≤17 then (if i≤16 then row16 else row17) else (if i≤18 then row18 else row19)) else (if i≤21 then (if i≤20 then row20 else row21) else (if i≤22 then row22 else row23))) else (if i≤27 then (if i≤25 then (if i≤24 then row24 else row25) else (if i≤26 then row26 else row27)) else (if i≤29 then (if i≤28 then row28 else row29) else (if i≤30 then row30 else row31)))))
def group1 (i : ℕ) : List ℕ := (if i≤47 then (if i≤39 then (if i≤35 then (if i≤33 then (if i≤32 then row32 else row33) else (if i≤34 then row34 else row35)) else (if i≤37 then (if i≤36 then row36 else row37) else (if i≤38 then row38 else row39))) else (if i≤43 then (if i≤41 then (if i≤40 then row40 else row41) else (if i≤42 then row42 else row43)) else (if i≤45 then (if i≤44 then row44 else row45) else (if i≤46 then row46 else row47)))) else (if i≤55 then (if i≤51 then (if i≤49 then (if i≤48 then row48 else row49) else (if i≤50 then row50 else row51)) else (if i≤53 then (if i≤52 then row52 else row53) else (if i≤54 then row54 else row55))) else (if i≤59 then (if i≤57 then (if i≤56 then row56 else row57) else (if i≤58 then row58 else row59)) else (if i≤61 then (if i≤60 then row60 else row61) else (if i≤62 then row62 else row63)))))
def group2 (i : ℕ) : List ℕ := (if i≤79 then (if i≤71 then (if i≤67 then (if i≤65 then (if i≤64 then row64 else row65) else (if i≤66 then row66 else row67)) else (if i≤69 then (if i≤68 then row68 else row69) else (if i≤70 then row70 else row71))) else (if i≤75 then (if i≤73 then (if i≤72 then row72 else row73) else (if i≤74 then row74 else row75)) else (if i≤77 then (if i≤76 then row76 else row77) else (if i≤78 then row78 else row79)))) else (if i≤87 then (if i≤83 then (if i≤81 then (if i≤80 then row80 else row81) else (if i≤82 then row82 else row83)) else (if i≤85 then (if i≤84 then row84 else row85) else (if i≤86 then row86 else row87))) else (if i≤91 then (if i≤89 then (if i≤88 then row88 else row89) else (if i≤90 then row90 else row91)) else (if i≤93 then (if i≤92 then row92 else row93) else (if i≤94 then row94 else row95)))))
def group3 (i : ℕ) : List ℕ := (if i≤111 then (if i≤103 then (if i≤99 then (if i≤97 then (if i≤96 then row96 else row97) else (if i≤98 then row98 else row99)) else (if i≤101 then (if i≤100 then row100 else row101) else (if i≤102 then row102 else row103))) else (if i≤107 then (if i≤105 then (if i≤104 then row104 else row105) else (if i≤106 then row106 else row107)) else (if i≤109 then (if i≤108 then row108 else row109) else (if i≤110 then row110 else row111)))) else (if i≤119 then (if i≤115 then (if i≤113 then (if i≤112 then row112 else row113) else (if i≤114 then row114 else row115)) else (if i≤117 then (if i≤116 then row116 else row117) else (if i≤118 then row118 else row119))) else (if i≤123 then (if i≤121 then (if i≤120 then row120 else row121) else (if i≤122 then row122 else row123)) else (if i≤125 then (if i≤124 then row124 else row125) else (if i≤126 then row126 else row127)))))
def group4 (i : ℕ) : List ℕ := (if i≤143 then (if i≤135 then (if i≤131 then (if i≤129 then (if i≤128 then row128 else row129) else (if i≤130 then row130 else row131)) else (if i≤133 then (if i≤132 then row132 else row133) else (if i≤134 then row134 else row135))) else (if i≤139 then (if i≤137 then (if i≤136 then row136 else row137) else (if i≤138 then row138 else row139)) else (if i≤141 then (if i≤140 then row140 else row141) else (if i≤142 then row142 else row143)))) else (if i≤151 then (if i≤147 then (if i≤145 then (if i≤144 then row144 else row145) else (if i≤146 then row146 else row147)) else (if i≤149 then (if i≤148 then row148 else row149) else (if i≤150 then row150 else row151))) else (if i≤155 then (if i≤153 then (if i≤152 then row152 else row153) else (if i≤154 then row154 else row155)) else (if i≤157 then (if i≤156 then row156 else row157) else (if i≤158 then row158 else row159)))))
def group5 (i : ℕ) : List ℕ := (if i≤175 then (if i≤167 then (if i≤163 then (if i≤161 then (if i≤160 then row160 else row161) else (if i≤162 then row162 else row163)) else (if i≤165 then (if i≤164 then row164 else row165) else (if i≤166 then row166 else row167))) else (if i≤171 then (if i≤169 then (if i≤168 then row168 else row169) else (if i≤170 then row170 else row171)) else (if i≤173 then (if i≤172 then row172 else row173) else (if i≤174 then row174 else row175)))) else (if i≤183 then (if i≤179 then (if i≤177 then (if i≤176 then row176 else row177) else (if i≤178 then row178 else row179)) else (if i≤181 then (if i≤180 then row180 else row181) else (if i≤182 then row182 else row183))) else (if i≤187 then (if i≤185 then (if i≤184 then row184 else row185) else (if i≤186 then row186 else row187)) else (if i≤189 then (if i≤188 then row188 else row189) else (if i≤190 then row190 else row191)))))
def group6 (i : ℕ) : List ℕ := (if i≤207 then (if i≤199 then (if i≤195 then (if i≤193 then (if i≤192 then row192 else row193) else (if i≤194 then row194 else row195)) else (if i≤197 then (if i≤196 then row196 else row197) else (if i≤198 then row198 else row199))) else (if i≤203 then (if i≤201 then (if i≤200 then row200 else row201) else (if i≤202 then row202 else row203)) else (if i≤205 then (if i≤204 then row204 else row205) else (if i≤206 then row206 else row207)))) else (if i≤215 then (if i≤211 then (if i≤209 then (if i≤208 then row208 else row209) else (if i≤210 then row210 else row211)) else (if i≤213 then (if i≤212 then row212 else row213) else (if i≤214 then row214 else row215))) else (if i≤219 then (if i≤217 then (if i≤216 then row216 else row217) else (if i≤218 then row218 else row219)) else (if i≤221 then (if i≤220 then row220 else row221) else (if i≤222 then row222 else row223)))))
def group7 (i : ℕ) : List ℕ := (if i≤239 then (if i≤231 then (if i≤227 then (if i≤225 then (if i≤224 then row224 else row225) else (if i≤226 then row226 else row227)) else (if i≤229 then (if i≤228 then row228 else row229) else (if i≤230 then row230 else row231))) else (if i≤235 then (if i≤233 then (if i≤232 then row232 else row233) else (if i≤234 then row234 else row235)) else (if i≤237 then (if i≤236 then row236 else row237) else (if i≤238 then row238 else row239)))) else (if i≤247 then (if i≤243 then (if i≤241 then (if i≤240 then row240 else row241) else (if i≤242 then row242 else row243)) else (if i≤245 then (if i≤244 then row244 else row245) else (if i≤246 then row246 else row247))) else (if i≤251 then (if i≤249 then (if i≤248 then row248 else row249) else (if i≤250 then row250 else row251)) else (if i≤253 then (if i≤252 then row252 else row253) else (if i≤254 then row254 else row255)))))
def group8 (i : ℕ) : List ℕ := (if i≤271 then (if i≤263 then (if i≤259 then (if i≤257 then (if i≤256 then row256 else row257) else (if i≤258 then row258 else row259)) else (if i≤261 then (if i≤260 then row260 else row261) else (if i≤262 then row262 else row263))) else (if i≤267 then (if i≤265 then (if i≤264 then row264 else row265) else (if i≤266 then row266 else row267)) else (if i≤269 then (if i≤268 then row268 else row269) else (if i≤270 then row270 else row271)))) else (if i≤279 then (if i≤275 then (if i≤273 then (if i≤272 then row272 else row273) else (if i≤274 then row274 else row275)) else (if i≤277 then (if i≤276 then row276 else row277) else (if i≤278 then row278 else row279))) else (if i≤283 then (if i≤281 then (if i≤280 then row280 else row281) else (if i≤282 then row282 else row283)) else (if i≤285 then (if i≤284 then row284 else row285) else (if i≤286 then row286 else row287)))))
def group9 (i : ℕ) : List ℕ := (if i≤303 then (if i≤295 then (if i≤291 then (if i≤289 then (if i≤288 then row288 else row289) else (if i≤290 then row290 else row291)) else (if i≤293 then (if i≤292 then row292 else row293) else (if i≤294 then row294 else row295))) else (if i≤299 then (if i≤297 then (if i≤296 then row296 else row297) else (if i≤298 then row298 else row299)) else (if i≤301 then (if i≤300 then row300 else row301) else (if i≤302 then row302 else row303)))) else (if i≤311 then (if i≤307 then (if i≤305 then (if i≤304 then row304 else row305) else (if i≤306 then row306 else row307)) else (if i≤309 then (if i≤308 then row308 else row309) else (if i≤310 then row310 else row311))) else (if i≤315 then (if i≤313 then (if i≤312 then row312 else row313) else (if i≤314 then row314 else row315)) else (if i≤317 then (if i≤316 then row316 else row317) else (if i≤318 then row318 else row319)))))
def group10 (i : ℕ) : List ℕ := (if i≤335 then (if i≤327 then (if i≤323 then (if i≤321 then (if i≤320 then row320 else row321) else (if i≤322 then row322 else row323)) else (if i≤325 then (if i≤324 then row324 else row325) else (if i≤326 then row326 else row327))) else (if i≤331 then (if i≤329 then (if i≤328 then row328 else row329) else (if i≤330 then row330 else row331)) else (if i≤333 then (if i≤332 then row332 else row333) else (if i≤334 then row334 else row335)))) else (if i≤343 then (if i≤339 then (if i≤337 then (if i≤336 then row336 else row337) else (if i≤338 then row338 else row339)) else (if i≤341 then (if i≤340 then row340 else row341) else (if i≤342 then row342 else row343))) else (if i≤347 then (if i≤345 then (if i≤344 then row344 else row345) else (if i≤346 then row346 else row347)) else (if i≤349 then (if i≤348 then row348 else row349) else (if i≤350 then row350 else row351)))))
def group11 (i : ℕ) : List ℕ := (if i≤367 then (if i≤359 then (if i≤355 then (if i≤353 then (if i≤352 then row352 else row353) else (if i≤354 then row354 else row355)) else (if i≤357 then (if i≤356 then row356 else row357) else (if i≤358 then row358 else row359))) else (if i≤363 then (if i≤361 then (if i≤360 then row360 else row361) else (if i≤362 then row362 else row363)) else (if i≤365 then (if i≤364 then row364 else row365) else (if i≤366 then row366 else row367)))) else (if i≤375 then (if i≤371 then (if i≤369 then (if i≤368 then row368 else row369) else (if i≤370 then row370 else row371)) else (if i≤373 then (if i≤372 then row372 else row373) else (if i≤374 then row374 else row375))) else (if i≤379 then (if i≤377 then (if i≤376 then row376 else row377) else (if i≤378 then row378 else row379)) else (if i≤381 then (if i≤380 then row380 else row381) else (if i≤382 then row382 else row383)))))
def group12 (i : ℕ) : List ℕ := (if i≤399 then (if i≤391 then (if i≤387 then (if i≤385 then (if i≤384 then row384 else row385) else (if i≤386 then row386 else row387)) else (if i≤389 then (if i≤388 then row388 else row389) else (if i≤390 then row390 else row391))) else (if i≤395 then (if i≤393 then (if i≤392 then row392 else row393) else (if i≤394 then row394 else row395)) else (if i≤397 then (if i≤396 then row396 else row397) else (if i≤398 then row398 else row399)))) else (if i≤407 then (if i≤403 then (if i≤401 then (if i≤400 then row400 else row401) else (if i≤402 then row402 else row403)) else (if i≤405 then (if i≤404 then row404 else row405) else (if i≤406 then row406 else row407))) else (if i≤411 then (if i≤409 then (if i≤408 then row408 else row409) else (if i≤410 then row410 else row411)) else (if i≤413 then (if i≤412 then row412 else row413) else (if i≤414 then row414 else row415)))))
def group13 (i : ℕ) : List ℕ := (if i≤431 then (if i≤423 then (if i≤419 then (if i≤417 then (if i≤416 then row416 else row417) else (if i≤418 then row418 else row419)) else (if i≤421 then (if i≤420 then row420 else row421) else (if i≤422 then row422 else row423))) else (if i≤427 then (if i≤425 then (if i≤424 then row424 else row425) else (if i≤426 then row426 else row427)) else (if i≤429 then (if i≤428 then row428 else row429) else (if i≤430 then row430 else row431)))) else (if i≤439 then (if i≤435 then (if i≤433 then (if i≤432 then row432 else row433) else (if i≤434 then row434 else row435)) else (if i≤437 then (if i≤436 then row436 else row437) else (if i≤438 then row438 else row439))) else (if i≤443 then (if i≤441 then (if i≤440 then row440 else row441) else (if i≤442 then row442 else row443)) else (if i≤445 then (if i≤444 then row444 else row445) else (if i≤446 then row446 else row447)))))
def group14 (i : ℕ) : List ℕ := (if i≤463 then (if i≤455 then (if i≤451 then (if i≤449 then (if i≤448 then row448 else row449) else (if i≤450 then row450 else row451)) else (if i≤453 then (if i≤452 then row452 else row453) else (if i≤454 then row454 else row455))) else (if i≤459 then (if i≤457 then (if i≤456 then row456 else row457) else (if i≤458 then row458 else row459)) else (if i≤461 then (if i≤460 then row460 else row461) else (if i≤462 then row462 else row463)))) else (if i≤471 then (if i≤467 then (if i≤465 then (if i≤464 then row464 else row465) else (if i≤466 then row466 else row467)) else (if i≤469 then (if i≤468 then row468 else row469) else (if i≤470 then row470 else row471))) else (if i≤475 then (if i≤473 then (if i≤472 then row472 else row473) else (if i≤474 then row474 else row475)) else (if i≤477 then (if i≤476 then row476 else row477) else (if i≤478 then row478 else row479)))))
def group15 (i : ℕ) : List ℕ := (if i≤495 then (if i≤487 then (if i≤483 then (if i≤481 then (if i≤480 then row480 else row481) else (if i≤482 then row482 else row483)) else (if i≤485 then (if i≤484 then row484 else row485) else (if i≤486 then row486 else row487))) else (if i≤491 then (if i≤489 then (if i≤488 then row488 else row489) else (if i≤490 then row490 else row491)) else (if i≤493 then (if i≤492 then row492 else row493) else (if i≤494 then row494 else row495)))) else (if i≤503 then (if i≤499 then (if i≤497 then (if i≤496 then row496 else row497) else (if i≤498 then row498 else row499)) else (if i≤501 then (if i≤500 then row500 else row501) else (if i≤502 then row502 else row503))) else (if i≤507 then (if i≤505 then (if i≤504 then row504 else row505) else (if i≤506 then row506 else row507)) else (if i≤509 then (if i≤508 then row508 else row509) else (if i≤510 then row510 else row511)))))
def group16 (i : ℕ) : List ℕ := (if i≤527 then (if i≤519 then (if i≤515 then (if i≤513 then (if i≤512 then row512 else row513) else (if i≤514 then row514 else row515)) else (if i≤517 then (if i≤516 then row516 else row517) else (if i≤518 then row518 else row519))) else (if i≤523 then (if i≤521 then (if i≤520 then row520 else row521) else (if i≤522 then row522 else row523)) else (if i≤525 then (if i≤524 then row524 else row525) else (if i≤526 then row526 else row527)))) else (if i≤535 then (if i≤531 then (if i≤529 then (if i≤528 then row528 else row529) else (if i≤530 then row530 else row531)) else (if i≤533 then (if i≤532 then row532 else row533) else (if i≤534 then row534 else row535))) else (if i≤539 then (if i≤537 then (if i≤536 then row536 else row537) else (if i≤538 then row538 else row539)) else (if i≤541 then (if i≤540 then row540 else row541) else (if i≤542 then row542 else row543)))))
def group17 (i : ℕ) : List ℕ := (if i≤559 then (if i≤551 then (if i≤547 then (if i≤545 then (if i≤544 then row544 else row545) else (if i≤546 then row546 else row547)) else (if i≤549 then (if i≤548 then row548 else row549) else (if i≤550 then row550 else row551))) else (if i≤555 then (if i≤553 then (if i≤552 then row552 else row553) else (if i≤554 then row554 else row555)) else (if i≤557 then (if i≤556 then row556 else row557) else (if i≤558 then row558 else row559)))) else (if i≤567 then (if i≤563 then (if i≤561 then (if i≤560 then row560 else row561) else (if i≤562 then row562 else row563)) else (if i≤565 then (if i≤564 then row564 else row565) else (if i≤566 then row566 else row567))) else (if i≤571 then (if i≤569 then (if i≤568 then row568 else row569) else (if i≤570 then row570 else row571)) else (if i≤573 then (if i≤572 then row572 else row573) else (if i≤574 then row574 else row575)))))
def group18 (i : ℕ) : List ℕ := (if i≤591 then (if i≤583 then (if i≤579 then (if i≤577 then (if i≤576 then row576 else row577) else (if i≤578 then row578 else row579)) else (if i≤581 then (if i≤580 then row580 else row581) else (if i≤582 then row582 else row583))) else (if i≤587 then (if i≤585 then (if i≤584 then row584 else row585) else (if i≤586 then row586 else row587)) else (if i≤589 then (if i≤588 then row588 else row589) else (if i≤590 then row590 else row591)))) else (if i≤599 then (if i≤595 then (if i≤593 then (if i≤592 then row592 else row593) else (if i≤594 then row594 else row595)) else (if i≤597 then (if i≤596 then row596 else row597) else (if i≤598 then row598 else row599))) else (if i≤603 then (if i≤601 then (if i≤600 then row600 else row601) else (if i≤602 then row602 else row603)) else (if i≤605 then (if i≤604 then row604 else row605) else (if i≤606 then row606 else row607)))))
def group19 (i : ℕ) : List ℕ := (if i≤623 then (if i≤615 then (if i≤611 then (if i≤609 then (if i≤608 then row608 else row609) else (if i≤610 then row610 else row611)) else (if i≤613 then (if i≤612 then row612 else row613) else (if i≤614 then row614 else row615))) else (if i≤619 then (if i≤617 then (if i≤616 then row616 else row617) else (if i≤618 then row618 else row619)) else (if i≤621 then (if i≤620 then row620 else row621) else (if i≤622 then row622 else row623)))) else (if i≤631 then (if i≤627 then (if i≤625 then (if i≤624 then row624 else row625) else (if i≤626 then row626 else row627)) else (if i≤629 then (if i≤628 then row628 else row629) else (if i≤630 then row630 else row631))) else (if i≤635 then (if i≤633 then (if i≤632 then row632 else row633) else (if i≤634 then row634 else row635)) else (if i≤637 then (if i≤636 then row636 else row637) else (if i≤638 then row638 else row639)))))
def group20 (i : ℕ) : List ℕ := (if i≤655 then (if i≤647 then (if i≤643 then (if i≤641 then (if i≤640 then row640 else row641) else (if i≤642 then row642 else row643)) else (if i≤645 then (if i≤644 then row644 else row645) else (if i≤646 then row646 else row647))) else (if i≤651 then (if i≤649 then (if i≤648 then row648 else row649) else (if i≤650 then row650 else row651)) else (if i≤653 then (if i≤652 then row652 else row653) else (if i≤654 then row654 else row655)))) else (if i≤663 then (if i≤659 then (if i≤657 then (if i≤656 then row656 else row657) else (if i≤658 then row658 else row659)) else (if i≤661 then (if i≤660 then row660 else row661) else (if i≤662 then row662 else row663))) else (if i≤667 then (if i≤665 then (if i≤664 then row664 else row665) else (if i≤666 then row666 else row667)) else (if i≤669 then (if i≤668 then row668 else row669) else (if i≤670 then row670 else row671)))))
def group21 (i : ℕ) : List ℕ := (if i≤687 then (if i≤679 then (if i≤675 then (if i≤673 then (if i≤672 then row672 else row673) else (if i≤674 then row674 else row675)) else (if i≤677 then (if i≤676 then row676 else row677) else (if i≤678 then row678 else row679))) else (if i≤683 then (if i≤681 then (if i≤680 then row680 else row681) else (if i≤682 then row682 else row683)) else (if i≤685 then (if i≤684 then row684 else row685) else (if i≤686 then row686 else row687)))) else (if i≤695 then (if i≤691 then (if i≤689 then (if i≤688 then row688 else row689) else (if i≤690 then row690 else row691)) else (if i≤693 then (if i≤692 then row692 else row693) else (if i≤694 then row694 else row695))) else (if i≤699 then (if i≤697 then (if i≤696 then row696 else row697) else (if i≤698 then row698 else row699)) else (if i≤701 then (if i≤700 then row700 else row701) else (if i≤702 then row702 else row703)))))
def group22 (i : ℕ) : List ℕ := (if i≤719 then (if i≤711 then (if i≤707 then (if i≤705 then (if i≤704 then row704 else row705) else (if i≤706 then row706 else row707)) else (if i≤709 then (if i≤708 then row708 else row709) else (if i≤710 then row710 else row711))) else (if i≤715 then (if i≤713 then (if i≤712 then row712 else row713) else (if i≤714 then row714 else row715)) else (if i≤717 then (if i≤716 then row716 else row717) else (if i≤718 then row718 else row719)))) else (if i≤727 then (if i≤723 then (if i≤721 then (if i≤720 then row720 else row721) else (if i≤722 then row722 else row723)) else (if i≤725 then (if i≤724 then row724 else row725) else (if i≤726 then row726 else row727))) else (if i≤731 then (if i≤729 then (if i≤728 then row728 else row729) else (if i≤730 then row730 else row731)) else (if i≤733 then (if i≤732 then row732 else row733) else (if i≤734 then row734 else row735)))))
def group23 (i : ℕ) : List ℕ := (if i≤751 then (if i≤743 then (if i≤739 then (if i≤737 then (if i≤736 then row736 else row737) else (if i≤738 then row738 else row739)) else (if i≤741 then (if i≤740 then row740 else row741) else (if i≤742 then row742 else row743))) else (if i≤747 then (if i≤745 then (if i≤744 then row744 else row745) else (if i≤746 then row746 else row747)) else (if i≤749 then (if i≤748 then row748 else row749) else (if i≤750 then row750 else row751)))) else (if i≤759 then (if i≤755 then (if i≤753 then (if i≤752 then row752 else row753) else (if i≤754 then row754 else row755)) else (if i≤757 then (if i≤756 then row756 else row757) else (if i≤758 then row758 else row759))) else (if i≤763 then (if i≤761 then (if i≤760 then row760 else row761) else (if i≤762 then row762 else row763)) else (if i≤765 then (if i≤764 then row764 else row765) else (if i≤766 then row766 else row767)))))
def group24 (i : ℕ) : List ℕ := (if i≤783 then (if i≤775 then (if i≤771 then (if i≤769 then (if i≤768 then row768 else row769) else (if i≤770 then row770 else row771)) else (if i≤773 then (if i≤772 then row772 else row773) else (if i≤774 then row774 else row775))) else (if i≤779 then (if i≤777 then (if i≤776 then row776 else row777) else (if i≤778 then row778 else row779)) else (if i≤781 then (if i≤780 then row780 else row781) else (if i≤782 then row782 else row783)))) else (if i≤791 then (if i≤787 then (if i≤785 then (if i≤784 then row784 else row785) else (if i≤786 then row786 else row787)) else (if i≤789 then (if i≤788 then row788 else row789) else (if i≤790 then row790 else row791))) else (if i≤795 then (if i≤793 then (if i≤792 then row792 else row793) else (if i≤794 then row794 else row795)) else (if i≤797 then (if i≤796 then row796 else row797) else (if i≤798 then row798 else row799)))))
def group25 (i : ℕ) : List ℕ := (if i≤815 then (if i≤807 then (if i≤803 then (if i≤801 then (if i≤800 then row800 else row801) else (if i≤802 then row802 else row803)) else (if i≤805 then (if i≤804 then row804 else row805) else (if i≤806 then row806 else row807))) else (if i≤811 then (if i≤809 then (if i≤808 then row808 else row809) else (if i≤810 then row810 else row811)) else (if i≤813 then (if i≤812 then row812 else row813) else (if i≤814 then row814 else row815)))) else (if i≤823 then (if i≤819 then (if i≤817 then (if i≤816 then row816 else row817) else (if i≤818 then row818 else row819)) else (if i≤821 then (if i≤820 then row820 else row821) else (if i≤822 then row822 else row823))) else (if i≤827 then (if i≤825 then (if i≤824 then row824 else row825) else (if i≤826 then row826 else row827)) else (if i≤829 then (if i≤828 then row828 else row829) else (if i≤830 then row830 else row831)))))
def group26 (i : ℕ) : List ℕ := (if i≤847 then (if i≤839 then (if i≤835 then (if i≤833 then (if i≤832 then row832 else row833) else (if i≤834 then row834 else row835)) else (if i≤837 then (if i≤836 then row836 else row837) else (if i≤838 then row838 else row839))) else (if i≤843 then (if i≤841 then (if i≤840 then row840 else row841) else (if i≤842 then row842 else row843)) else (if i≤845 then (if i≤844 then row844 else row845) else (if i≤846 then row846 else row847)))) else (if i≤855 then (if i≤851 then (if i≤849 then (if i≤848 then row848 else row849) else (if i≤850 then row850 else row851)) else (if i≤853 then (if i≤852 then row852 else row853) else (if i≤854 then row854 else row855))) else (if i≤859 then (if i≤857 then (if i≤856 then row856 else row857) else (if i≤858 then row858 else row859)) else (if i≤861 then (if i≤860 then row860 else row861) else (if i≤862 then row862 else row863)))))
def group27 (i : ℕ) : List ℕ := (if i≤879 then (if i≤871 then (if i≤867 then (if i≤865 then (if i≤864 then row864 else row865) else (if i≤866 then row866 else row867)) else (if i≤869 then (if i≤868 then row868 else row869) else (if i≤870 then row870 else row871))) else (if i≤875 then (if i≤873 then (if i≤872 then row872 else row873) else (if i≤874 then row874 else row875)) else (if i≤877 then (if i≤876 then row876 else row877) else (if i≤878 then row878 else row879)))) else (if i≤887 then (if i≤883 then (if i≤881 then (if i≤880 then row880 else row881) else (if i≤882 then row882 else row883)) else (if i≤885 then (if i≤884 then row884 else row885) else (if i≤886 then row886 else row887))) else (if i≤891 then (if i≤889 then (if i≤888 then row888 else row889) else (if i≤890 then row890 else row891)) else (if i≤893 then (if i≤892 then row892 else row893) else (if i≤894 then row894 else row895)))))
def group28 (i : ℕ) : List ℕ := (if i≤911 then (if i≤903 then (if i≤899 then (if i≤897 then (if i≤896 then row896 else row897) else (if i≤898 then row898 else row899)) else (if i≤901 then (if i≤900 then row900 else row901) else (if i≤902 then row902 else row903))) else (if i≤907 then (if i≤905 then (if i≤904 then row904 else row905) else (if i≤906 then row906 else row907)) else (if i≤909 then (if i≤908 then row908 else row909) else (if i≤910 then row910 else row911)))) else (if i≤919 then (if i≤915 then (if i≤913 then (if i≤912 then row912 else row913) else (if i≤914 then row914 else row915)) else (if i≤917 then (if i≤916 then row916 else row917) else (if i≤918 then row918 else row919))) else (if i≤923 then (if i≤921 then (if i≤920 then row920 else row921) else (if i≤922 then row922 else row923)) else (if i≤925 then (if i≤924 then row924 else row925) else (if i≤926 then row926 else row927)))))
def group29 (i : ℕ) : List ℕ := (if i≤943 then (if i≤935 then (if i≤931 then (if i≤929 then (if i≤928 then row928 else row929) else (if i≤930 then row930 else row931)) else (if i≤933 then (if i≤932 then row932 else row933) else (if i≤934 then row934 else row935))) else (if i≤939 then (if i≤937 then (if i≤936 then row936 else row937) else (if i≤938 then row938 else row939)) else (if i≤941 then (if i≤940 then row940 else row941) else (if i≤942 then row942 else row943)))) else (if i≤951 then (if i≤947 then (if i≤945 then (if i≤944 then row944 else row945) else (if i≤946 then row946 else row947)) else (if i≤949 then (if i≤948 then row948 else row949) else (if i≤950 then row950 else row951))) else (if i≤955 then (if i≤953 then (if i≤952 then row952 else row953) else (if i≤954 then row954 else row955)) else (if i≤957 then (if i≤956 then row956 else row957) else (if i≤958 then row958 else row959)))))
def group30 (i : ℕ) : List ℕ := (if i≤975 then (if i≤967 then (if i≤963 then (if i≤961 then (if i≤960 then row960 else row961) else (if i≤962 then row962 else row963)) else (if i≤965 then (if i≤964 then row964 else row965) else (if i≤966 then row966 else row967))) else (if i≤971 then (if i≤969 then (if i≤968 then row968 else row969) else (if i≤970 then row970 else row971)) else (if i≤973 then (if i≤972 then row972 else row973) else (if i≤974 then row974 else row975)))) else (if i≤983 then (if i≤979 then (if i≤977 then (if i≤976 then row976 else row977) else (if i≤978 then row978 else row979)) else (if i≤981 then (if i≤980 then row980 else row981) else (if i≤982 then row982 else row983))) else (if i≤987 then (if i≤985 then (if i≤984 then row984 else row985) else (if i≤986 then row986 else row987)) else (if i≤989 then (if i≤988 then row988 else row989) else (if i≤990 then row990 else row991)))))
def group31 (i : ℕ) : List ℕ := (if i≤1007 then (if i≤999 then (if i≤995 then (if i≤993 then (if i≤992 then row992 else row993) else (if i≤994 then row994 else row995)) else (if i≤997 then (if i≤996 then row996 else row997) else (if i≤998 then row998 else row999))) else (if i≤1003 then (if i≤1001 then (if i≤1000 then row1000 else row1001) else (if i≤1002 then row1002 else row1003)) else (if i≤1005 then (if i≤1004 then row1004 else row1005) else (if i≤1006 then row1006 else row1007)))) else (if i≤1015 then (if i≤1011 then (if i≤1009 then (if i≤1008 then row1008 else row1009) else (if i≤1010 then row1010 else row1011)) else (if i≤1013 then (if i≤1012 then row1012 else row1013) else (if i≤1014 then row1014 else row1015))) else (if i≤1019 then (if i≤1017 then (if i≤1016 then row1016 else row1017) else (if i≤1018 then row1018 else row1019)) else (if i≤1021 then (if i≤1020 then row1020 else row1021) else (if i≤1022 then row1022 else row1023)))))
def group32 (i : ℕ) : List ℕ := (if i≤1039 then (if i≤1031 then (if i≤1027 then (if i≤1025 then (if i≤1024 then row1024 else row1025) else (if i≤1026 then row1026 else row1027)) else (if i≤1029 then (if i≤1028 then row1028 else row1029) else (if i≤1030 then row1030 else row1031))) else (if i≤1035 then (if i≤1033 then (if i≤1032 then row1032 else row1033) else (if i≤1034 then row1034 else row1035)) else (if i≤1037 then (if i≤1036 then row1036 else row1037) else (if i≤1038 then row1038 else row1039)))) else (if i≤1047 then (if i≤1043 then (if i≤1041 then (if i≤1040 then row1040 else row1041) else (if i≤1042 then row1042 else row1043)) else (if i≤1045 then (if i≤1044 then row1044 else row1045) else (if i≤1046 then row1046 else row1047))) else (if i≤1051 then (if i≤1049 then (if i≤1048 then row1048 else row1049) else (if i≤1050 then row1050 else row1051)) else (if i≤1053 then (if i≤1052 then row1052 else row1053) else (if i≤1054 then row1054 else row1055)))))
def group33 (i : ℕ) : List ℕ := (if i≤1071 then (if i≤1063 then (if i≤1059 then (if i≤1057 then (if i≤1056 then row1056 else row1057) else (if i≤1058 then row1058 else row1059)) else (if i≤1061 then (if i≤1060 then row1060 else row1061) else (if i≤1062 then row1062 else row1063))) else (if i≤1067 then (if i≤1065 then (if i≤1064 then row1064 else row1065) else (if i≤1066 then row1066 else row1067)) else (if i≤1069 then (if i≤1068 then row1068 else row1069) else (if i≤1070 then row1070 else row1071)))) else (if i≤1079 then (if i≤1075 then (if i≤1073 then (if i≤1072 then row1072 else row1073) else (if i≤1074 then row1074 else row1075)) else (if i≤1077 then (if i≤1076 then row1076 else row1077) else (if i≤1078 then row1078 else row1079))) else (if i≤1083 then (if i≤1081 then (if i≤1080 then row1080 else row1081) else (if i≤1082 then row1082 else row1083)) else (if i≤1085 then (if i≤1084 then row1084 else row1085) else (if i≤1086 then row1086 else row1087)))))
def group34 (i : ℕ) : List ℕ := (if i≤1100 then (if i≤1094 then (if i≤1091 then (if i≤1089 then (if i≤1088 then row1088 else row1089) else (if i≤1090 then row1090 else row1091)) else (if i≤1093 then (if i≤1092 then row1092 else row1093) else row1094)) else (if i≤1097 then (if i≤1096 then (if i≤1095 then row1095 else row1096) else row1097) else (if i≤1099 then (if i≤1098 then row1098 else row1099) else row1100))) else (if i≤1107 then (if i≤1104 then (if i≤1102 then (if i≤1101 then row1101 else row1102) else (if i≤1103 then row1103 else row1104)) else (if i≤1106 then (if i≤1105 then row1105 else row1106) else row1107)) else (if i≤1110 then (if i≤1109 then (if i≤1108 then row1108 else row1109) else row1110) else (if i≤1112 then (if i≤1111 then row1111 else row1112) else row1113))))
def guides (i : ℕ) : List ℕ := (if (i / 32)≤17 then (if (i / 32)≤8 then (if (i / 32)≤4 then (if (i / 32)≤2 then (if (i / 32)≤1 then (if (i / 32)≤0 then group0 i else group1 i) else group2 i) else (if (i / 32)≤3 then group3 i else group4 i)) else (if (i / 32)≤6 then (if (i / 32)≤5 then group5 i else group6 i) else (if (i / 32)≤7 then group7 i else group8 i))) else (if (i / 32)≤13 then (if (i / 32)≤11 then (if (i / 32)≤10 then (if (i / 32)≤9 then group9 i else group10 i) else group11 i) else (if (i / 32)≤12 then group12 i else group13 i)) else (if (i / 32)≤15 then (if (i / 32)≤14 then group14 i else group15 i) else (if (i / 32)≤16 then group16 i else group17 i)))) else (if (i / 32)≤26 then (if (i / 32)≤22 then (if (i / 32)≤20 then (if (i / 32)≤19 then (if (i / 32)≤18 then group18 i else group19 i) else group20 i) else (if (i / 32)≤21 then group21 i else group22 i)) else (if (i / 32)≤24 then (if (i / 32)≤23 then group23 i else group24 i) else (if (i / 32)≤25 then group25 i else group26 i))) else (if (i / 32)≤30 then (if (i / 32)≤28 then (if (i / 32)≤27 then group27 i else group28 i) else (if (i / 32)≤29 then group29 i else group30 i)) else (if (i / 32)≤32 then (if (i / 32)≤31 then group31 i else group32 i) else (if (i / 32)≤33 then group33 i else group34 i)))))
lemma block_off {m k db branches vs i n ts} (p : 0 < m)
    (e : lookupRows (audit m db branches k) ts ((vs.drop i).take n)=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (lookup_ok hw (fun g => audit_ok p db branches k w h g) _))
def spec41 : FloorData := (0xe098026000000000b,4,[0x40000080000000005ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff67fffffffffffff,0x80200000000000011fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd9ffffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3fcfff3ffffffffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof41 : Floor 333 spec41 := floorChecked (by decide +kernel)
def book41 (_i : ℕ) : {s : FloorData // Floor 333 s} := ⟨spec41,proof41⟩
def spec75 : FloorData := (0x1fffededc0000000000000000000001f9f,4,[0x805410300000000000000000000000a0dffffffffffffffffffffffffffffffffffffffffffffffffffc1ff21fffffffffffffffffffffffffff,0x1941838200000000000000000000002c29fffffffffffffffffffffffffffffffffffffffffffffffffffe1fff23fffffffffffffffffffffff60,0x3ffffffffffffffffffffffffffffffffffffffffffffffffff5a836347ffffffffffffffffffffff1f1ffffffffffffffffffffffffffffffffffffffffffffffffffffe12123fffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffe6323c3c7fffffffffffffffffffffc1c1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe060])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof75 : Floor 333 spec75 := floorChecked (by decide +kernel)
def book75 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩)
def spec82 : FloorData := (0xe046000046000000000000000000000026000,4,[0x4000000008000000000000000000000008001ffffffffffffffffffffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffffffffff,0x8008000000000000000000000000000040001ffffffffffffffffffffffffffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffffffffffffffffffffff3ff3fffff3ffffffffffffffffffffffb3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd9fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof82 : Floor 333 spec82 := floorChecked (by decide +kernel)
def book82 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else ⟨spec82,proof82⟩)
def spec89 : FloorData := (0x3fc1ede01e000ec00000000000000000f80000eb,4,[0x1001410004000500000000000000000090000045ffffffffffffffffffffffffffffffffffffffffffff83ff21fffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffeafc363febfff27fffffffffffffffff2fffffb9ffffffffffffffffffffffffffffffffffffffffffffffe121ffffff13fffffffffffffffffffffffff,0x33018380000004000000000000000001c00000c1fffffffffffffffffffffffffffffffffffffffffffffffffffe1fff13fffffffffffffffffffffff14,0x3fffffffffffffffffffffffffffffffffffffffffffcc7e3c3ff3fffa7ffffffffffffffffe0fffff29fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff07ffff14])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof89 : Floor 333 spec89 := floorChecked (by decide +kernel)
def book89 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else (if i≤7 then ⟨spec82,proof82⟩ else ⟨spec89,proof89⟩))
def spec99 : FloorData := (0x1ffe0000000001f6f5c000000000007d6e0000000000,4,[0x8040000000001410300000000000028180000000001ffffffffffffffffffffffffffffffffffffffffc1fffffffffffe91fffffffffffffffffffffffffff,0x194000000000018582000000000000b0900000000001fffffffffffffffffffffffffffffffffffffffffe1ffffffffffffea3ffffffffffffe91ffffffffff,0x3ffffffffffffffffffffffffffffffffffffffff5abfffffffffc36347fffffffffffc7e3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe090a3fffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffe633fffffffffe3a3c7fffffffffff0723fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8291ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof99 : Floor 333 spec99 := floorChecked (by decide +kernel)
def book99 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤7 then (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else ⟨spec82,proof82⟩) else (if i≤8 then ⟨spec89,proof89⟩ else ⟨spec99,proof99⟩))
def spec113 : FloorData := (0xff00001e0001f6e0000016c00001f0000001b60000000000,4,[0x4000000400014100000005000000a0000000280000000001fffffffffffffffffffffffffffffffffffe0ffffffffffe91fffffffffffffffffffffffffffffffff,0xca00000000018580000004000002c0000001200000000001fffffffffffffffffffffffffffffffffffffffffe1ffffffffffffe93ffffffffffffe49ffffffffff,0x3fffffffffffffffffffffffffffffffffffadffffebfffc363ffffff27fffff1fffffffd3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe091fffffe93fffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffff31fffff3fffe3a3ffffffa7ffffc1ffffffe93ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ffffffe49ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof113 : Floor 333 spec113 := floorChecked (by decide +kernel)
def book113 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤7 then (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else ⟨spec82,proof82⟩) else (if i≤9 then (if i≤8 then ⟨spec89,proof89⟩ else ⟨spec99,proof99⟩) else ⟨spec113,proof113⟩))
def spec137 : FloorData := (0x3a300098000000000000000000000000000000000000000000000000b,4,[0x100000200000000000000000000000000000000000000000000000005fffffffffffffffffffffffffffdcffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x204000000000000000000000000000000000000000000000000000011ffffffffffffffffffffffffffffffff67fffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffffcf9fffcffffffffffffffffffffffffffffffffffffffffffffffffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof137 : Floor 333 spec137 := floorChecked (by decide +kernel)
def book137 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤8 then (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else (if i≤7 then ⟨spec82,proof82⟩ else ⟨spec89,proof89⟩)) else (if i≤10 then (if i≤9 then ⟨spec99,proof99⟩ else ⟨spec113,proof113⟩) else ⟨spec137,proof137⟩))
def spec146 : FloorData := (0x38230000046000000000000000000000000000000000000000000000026000,4,[0x10000000008000000000000000000000000000000000000000000000008001fffffffffffffffffffffffdcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x20040000000000000000000000000000000000000000000000000000040001ffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffcff9ffffff3ffffffffffffffffffffffffffffffffffffffffffffffb3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd9fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof146 : Floor 333 spec146 := floorChecked (by decide +kernel)
def book146 (i : ℕ) : {s : FloorData // Floor 333 s} := (if i≤8 then (if i≤6 then (if i≤5 then ⟨spec41,proof41⟩ else ⟨spec75,proof75⟩) else (if i≤7 then ⟨spec82,proof82⟩ else ⟨spec89,proof89⟩)) else (if i≤10 then (if i≤9 then ⟨spec99,proof99⟩ else ⟨spec113,proof113⟩) else (if i≤11 then ⟨spec137,proof137⟩ else ⟨spec146,proof146⟩)))
def spec163 : FloorData := (0xfff0000000000fefb8000000000000000000000000000000000007e6e0000000000,4,[0x4020000000000a10600000000000000000000000000000000000028180000000001ffffffffffffffffe0ffffffffffff11fffffffffffffffffffffffffffffffffffffffffffffffffff,0xca00000000000c584000000000000000000000000000000000000b0900000000001ffffffffffffffffff0ffffffffffffe47ffffffffffffffffffffffffffffffffffffd91ffffffffff,0x3ffffffffffffffffad5fffffffffe1628ffffffffffffffffffffffffffffffffffffc7e3fffffffffffffffffffffffffffffffffffffff01047fffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffff319ffffffffff1a38ffffffffffffffffffffffffffffffffffff0723fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8191ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof163 : Floor 333 spec163 := floorChecked (by decide +kernel)
def book163 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else ⟨spec163,proof163⟩
def spec170 : FloorData := (0xef1f00000003c670f6000000000000000000000000000000001f11b80000000000000,4,[0xc00a00000002808068000000000000000000000000000000002a02400000000000001fffffffffffffff0fffffffffff98fffffffffffffffffffffffffffffffffffffee47fffffffffffff,0x42000000000300c020000000000000000000000000000000000c00600000000000001ffffffffffffffffe0ffffffffffff09fffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffb5edfffffff87b1f53fffffffffffffffffffffffffffffffff1ff8fffffffffffffffffffffffffffffffffffffffc398f09fffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffff39f1fffffffc7f1f93ffffffffffffffffffffffffffffffffc1fc8ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ee47fffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof170 : Floor 333 spec170 := floorChecked (by decide +kernel)
def book170 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩)
def spec177 : FloorData := (0xff0000f0007f70000001d800000000000000000000000000001f0000002b60000000000,4,[0x40000020005080000000a000000000000000000000000000000a0000000280000000001ffffffffffffe0fffffffff88ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xca0000000062c00000008000000000000000000000000000002c0000001200000000001ffffffffffffffffff0ffffffffffffe27ffffffffffffffffffffffffffffffffffffd49ffffffffff,0x3ffffffffffffadffff5fff0b1ffffffe4ffffffffffffffffffffffffffffff1fffffffd3ffffffffffffffffffffffffffffffff808ffffffe27fffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffff31ffff9fff8d1fffffff4fffffffffffffffffffffffffffffc1ffffffe93ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ffffffd49ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof177 : Floor 333 spec177 := floorChecked (by decide +kernel)
def book177 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else ⟨spec177,proof177⟩)
def spec184 : FloorData := (0x381f0f0000f007b006b0000000000000000000000000000007c0000012d80000000000000,4,[0x1000020000a00100014000000000000000000000000000000280000000a00000000000001ffffffffffffe0fffffffff84ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x300a000000c00340010000000000000000000000000000000b00000004800000000000001fffffffffffffff0fffffffffff94fffffffffffffffffffffffffffffffffffffed27fffffffffffff,0x3ffffffffffefedf5fffe1ffa9ffa9ffffffffffffffffffffffffffffffc7fffffff4ffffffffffffffffffffffffffffffffff0ff84ff94ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffcff1f9ffff1ffc9ffe9ffffffffffffffffffffffffffffff07ffffffa4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83fffffed27fffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof184 : Floor 333 spec184 := floorChecked (by decide +kernel)
def book184 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else (if i≤15 then ⟨spec177,proof177⟩ else ⟨spec184,proof184⟩))
def spec193 : FloorData := (0x74c0000000000000000000009800000000000000000000004c0000000000000000000000000,4,[0x200000000000000000000000200000000000000000000000100000000000000000000000001fffffffffb3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x410000000000000000000000000000000000000000000000800000000000000000000000001ffffffffffffffffffffffffffffffff67fffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffff9e7fffffffffffffffffffffcfffffffffffffffffffffff67fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb3fffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof193 : Floor 333 spec193 := floorChecked (by decide +kernel)
def book193 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤15 then (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else ⟨spec177,proof177⟩) else (if i≤16 then ⟨spec184,proof184⟩ else ⟨spec193,proof193⟩))
def spec194 : FloorData := (0x384c000000000000000000046000000000000000000000046000000000000000000000000000,4,[0x1000000000000000000000008000000000000000000000008000000000000000000000000001fffffffffb3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2010000000000000000000000000000000000000000000080000000000000000000000000001ffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffcfe7ffffffffffffffffffff3ffffffffffffffffffffff73fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof194 : Floor 333 spec194 := floorChecked (by decide +kernel)
def book194 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤15 then (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else ⟨spec177,proof177⟩) else (if i≤17 then (if i≤16 then ⟨spec184,proof184⟩ else ⟨spec193,proof193⟩) else ⟨spec194,proof194⟩))
def spec208 : FloorData := (0x1c0004c000000000000230000000000000000000000046000000000000000000000000000000000,4,[0x800000000000000000040000000000000000000000008000000000000000000000000000000001fffffffffb3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1000010000000000000000000000000000000000000080000000000000000000000000000000001fffffffffffffffffffffffdcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffe7fffe7fffffffffffff9fffffffffffffffffffffff73fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb9fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof208 : Floor 333 spec208 := floorChecked (by decide +kernel)
def book208 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤16 then (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else (if i≤15 then ⟨spec177,proof177⟩ else ⟨spec184,proof184⟩)) else (if i≤18 then (if i≤17 then ⟨spec193,proof193⟩ else ⟨spec194,proof194⟩) else ⟨spec208,proof208⟩))
def spec232 : FloorData := (0x1c1f00780fc0000f00000000000730000000003e000000000000000000000000001c980000000000000,4,[0x8000050020000020000000000024000000000240000000000000000000000000008200000000000001ffe0fffff03ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3f7ebff0ff47ffff5fffffffffff99fffffffffcbfffffffffffffffffffffffffff7cffffffffffffffffffff87f03ffffffffffffffff8cffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x180c0060070000000000000000020000000000700000000000000000000000000018000000000000001fffffffffffffff0fffffffffff8cfffffffffffffffffffffffffffffffffffffe367fffffffffffff,0x3e7f1ff8ff87ffff9fffffffffffd9fffffffff83ffffffffffffffffffffffffffe6cffffffffffffffffffffffffffffffffffffffffffffffffffffc1ffffffffffffffffffffffffffe367fffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof232 : Floor 333 spec232 := floorChecked (by decide +kernel)
def book232 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<13 then book146 i else (if i≤16 then (if i≤14 then (if i≤13 then ⟨spec163,proof163⟩ else ⟨spec170,proof170⟩) else (if i≤15 then ⟨spec177,proof177⟩ else ⟨spec184,proof184⟩)) else (if i≤18 then (if i≤17 then ⟨spec193,proof193⟩ else ⟨spec194,proof194⟩) else (if i≤19 then ⟨spec208,proof208⟩ else ⟨spec232,proof232⟩)))
def spec83 : FloorData := (0x3fe4e001e4e7c0000000000000000007c6e000,5,[0x3fffffffffffffffffffffffffffffffffffffffffffffe1773ffd77377ffffffffffffffffffafb3fffffffffffffffffffffffffffffffffffffffffffffffff1fb1ffffb1ffffffffffffffffffffff91fff,0x24000001818200000000000000000003018001ffffffffffffffffffffffffffffffffffffffffffffffe1b1ffffff83fffffffffffffffffffffffff,0x3fffffffffffffffffffffffffffffffffffffffffffffc9b7bffc36347ffffffffffffffffffc7e3fffffffffffffffffffffffffffffffffffffffffffffffffffffffe1b183fffffffffffffffffffffffff,0x12080002080800000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8391fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof83 : Floor 333 spec83 := floorChecked (by decide +kernel)
def book83 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else ⟨spec83,proof83⟩
def spec105 : FloorData := (0xfe01e000000001e001cc00000000ec98126000000008b,5,[0x40000000004000100000000040000080000000005ffffffffffffffffffffffffffffffffffffffc1fffffffffffffffffffffffffff367fffffffffffff,0xa40000000000028001000000000088200000000000111fffffffffffffffffffffffffffffffffffffffffe1ffffffffffffe33ffffffffffffed9ffffffffff,0x3ffffffffffffffffffffffffffffffffffffff4bfebffffffffc3ffe67ffffffff37cfff3fffffffee9fffffffffffffffffffffffffffffffffffffffffffffffffffe1ffe33fffffffffffffffffffffff74,0x3fffffffffffffffffffffffffffffffffffffff3ff3fffffffff3fffe7fffffffe3ecffb3ffffffffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1367ed9ffffffff74])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof105 : Floor 333 spec105 := floorChecked (by decide +kernel)
def book105 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩)
def spec139 : FloorData := (0xffa7f5eb80000000000000000000000000000000000000000000001f1f,5,[0x8100a10600000000000000000000000000000000000000000000000a0dfffffffffffffffffffffffffc3d8fa1fffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffffffffa8b8d7acffffffffffffffffffffffffffffffffffffffffffffffede9ffffffffffffffffffffffffffc58fff47fffffffffffffffffffffffffffffffffffffffffffffffe0,0x3fffffffffffffffffffffffff32bc1628fffffffffffffffffffffffffffffffffffffffffffffff1f1fffffffffffffffffffffffffffff0a147fffffffffffffffffffffffffffffffffffffffffffffffff,0x4441081000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0e0])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof139 : Floor 333 spec139 := floorChecked (by decide +kernel)
def book139 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else ⟨spec139,proof139⟩)
def spec147 : FloorData := (0xffa70000f4ef80000000000000000000000000000000000000000007c6e000,5,[0x3fffffffffffffffffffff85b9fffeb72efffffffffffffffffffffffffffffffffffffffffffafb3ffffffffffffffffffffffffc7d8fffffb1ffffffffffffffffffffffffffffffffffffffffffffff91fff,0x90000000c18400000000000000000000000000000000000000000003018001ffffffffffffffffffffff858fffffff07fffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffff26bdfffe1628fffffffffffffffffffffffffffffffffffffffffffc7e3ffffffffffffffffffffffffffffffff0b107fffffffffffffffffffffffffffffffffffffffffffffffff,0x48400001081000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8391fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof147 : Floor 333 spec147 := floorChecked (by decide +kernel)
def book147 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else (if i≤23 then ⟨spec139,proof139⟩ else ⟨spec147,proof147⟩))
def spec153 : FloorData := (0x3f07af03ab000d800000000000000000000000000000000000000000f800006b,5,[0x2005080100000a00000000000000000000000000000000000000000090000045ffffffffffffffffffff0ffd0ffd4ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffcbf0b1fabdffe4ffffffffffffffffffffffffffffffffffffffffff2fffffb9ffffffffffffffffffffff850fffffff27fffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffedf6bdf8b9ffecffffffffffffffffffffffffffffffffffffffffffcfffffe9ffffffffffffffffffffffffffc54fff27fffffffffffffffffffffffffffffffffffffffffffffff94,0x1008400440001000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff07ffff94])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof153 : Floor 333 spec153 := floorChecked (by decide +kernel)
def book153 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤23 then (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else ⟨spec139,proof139⟩) else (if i≤24 then ⟨spec147,proof147⟩ else ⟨spec153,proof153⟩))
def spec154 : FloorData := (0xcf382b3c2f056000000000000000000000000000000000000000001f000b6000,5,[0x8010002808028000000000000000000000000000000000000000000a00028001ffffffffffffffffffff0ffd4ffd0ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffffffffffffffffffeb8fb9b7bdf73fffffffffffffffffffffffffffffffffffffffffedfffb3ffffffffffffffffffffffffc7d4fffffa9ffffffffffffffffffffffffffffffffffffffffffffff49fff,0x3fffffffffffffffffff6dafbd87b1f53ffffffffffffffffffffffffffffffffffffffffff1fffd3ffffffffffffffffffffffffffffc3d0fa9fffffffffffffffffffffffffffffffffffffffffffffffffff,0x1040404040080000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0fff49fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof154 : Floor 333 spec154 := floorChecked (by decide +kernel)
def book154 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤23 then (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else ⟨spec139,proof139⟩) else (if i≤25 then (if i≤24 then ⟨spec147,proof147⟩ else ⟨spec153,proof153⟩) else ⟨spec154,proof154⟩))
def spec169 : FloorData := (0x1f00f00000003e30019800000000000000000000000000000000f098226000000000b,5,[0x20000000100000200000000000000000000000000000000040000080000000005fffffffffffffff0fffffffffff9cfffffffffffffffffffffffffffffffffffffef67fffffffffffff,0x20000000000204000000000000000000000000000000000000080200000000000011ffffffffffffffffff0ffffffffffffe67ffffffffffffffffffffffffffffffffffffdd9ffffffffff,0x3fffffffffffffff5ff5fffffff8b9ffecfffffffffffffffffffffffffffffffff3fcfff3ffffffffe9ffffffffffffffffffffffffffc1cffe67ffffffffffffffffffffffffffffffffffffffffffffffff4,0x3fffffffffffffff9ff9fffffffcf9fffcffffffffffffffffffffffffffffffffe3ecffb3ffffffffe9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f67dd9fffffffff4])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof169 : Floor 333 spec169 := floorChecked (by decide +kernel)
def book169 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤24 then (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else (if i≤23 then ⟨spec139,proof139⟩ else ⟨spec147,proof147⟩)) else (if i≤26 then (if i≤25 then ⟨spec153,proof153⟩ else ⟨spec154,proof154⟩) else ⟨spec169,proof169⟩))
def spec195 : FloorData := (0x7f4c000000000000000000f4eb80000000000000000001e4e5c0000000000000000000000000,5,[0x3fffffff8367fffffffffffffffffeb72efffffffffffffffffffd77377ffffffffffffffffffffffffffffffffc7b3fffffffffffffffffffb1ffffffffffffffffffffffb1fffffffffffffffffffffffffff,0x3fffffff9167fffffffffffffffffed7acfffffffffffffffffffdb7b67fffffffffffffffffffffffffffffffff8b3fffffffffffffffffffff47ffffffffffffffffffffffa3fffffffffffffffffffffffff,0x2410000000000000000000000000000000000000000002080800000000000000000000000001fffffffffffffffffffffffffffff0b147fffffffffffffffffffffffffffffffffffffffffffffffff,0x4880000000000000000001081000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffe1b1a3fffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof195 : Floor 333 spec195 := floorChecked (by decide +kernel)
def book195 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<21 then book232 i else (if i≤24 then (if i≤22 then (if i≤21 then ⟨spec83,proof83⟩ else ⟨spec105,proof105⟩) else (if i≤23 then ⟨spec139,proof139⟩ else ⟨spec147,proof147⟩)) else (if i≤26 then (if i≤25 then ⟨spec153,proof153⟩ else ⟨spec154,proof154⟩) else (if i≤27 then ⟨spec169,proof169⟩ else ⟨spec195,proof195⟩)))
def spec201 : FloorData := (0xf875c0000000000000003b300098000000000000000001e000cc000000000000000000000008b,5,[0x200000000000000000100000200000000000000000004000100000000000000000000000005ffffff87fa3ffffffffffffffffccffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffff5f167fffffffffffffffabdffecffffffffffffffffffebfff67ffffffffffffffffffffffff9ffffffff8a3fffffffffffffffffffff67ffffffffffffffffffffff33fffffffffffffffffffffffff,0x3ffffff6f577fffffffffffffff8b9ffecfffffffffffffffffff3fffe7fffffffffffffffffffffffe9ffffffffffffffffffffffffffc4cfff67fffffffffffffffffffffffffffffffffffffffffffffff74,0x80880000000000000000440001000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffe1fff33fffffffffffffffffffffff74])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof201 : Floor 333 spec201 := floorChecked (by decide +kernel)
def book201 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else ⟨spec201,proof201⟩
def spec202 : FloorData := (0x37b85c000000000000003c370560000000000000000003e00d6000000000000000000000000000,5,[0x201000000000000000002808028000000000000000000140028000000000000000000000000001ffffff87fa3ffffffffffffffffc8ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffff58f67ffffffffffffffb7bdf73ffffffffffffffffffdbff73ffffffffffffffffffffffffffffffffffc7a3fffffffffffffffffffa9ffffffffffffffffffffff29fffffffffffffffffffffffffff,0x3fffffd6af77ffffffffffffff87b1f53ffffffffffffffffffe3ffd3ffffffffffffffffffffffffffffffffffffffffffffffffffffc3c8fa9fffffffffffffffffffffffffffffffffffffffffffffffffff,0x84080000000000000004040080000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffc1ff29fffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof202 : Floor 333 spec202 := floorChecked (by decide +kernel)
def book202 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩)
def spec209 : FloorData := (0x3c0074c000000000007a70000000d80000000000001e4e0000006c0000000000000000000000000,5,[0x3ffffc7ff367fffffffffff5b9ffffffeefffffffffffffd773ffffff77fffffffffffffffffffffffffffffe3fffb3ffffffffffffd8fffffffffffffffffffffffb1fffffffffffffffffffffffffffffffff,0x3ffffcfff167fffffffffff6bdffffffecfffffffffffffdb7bffffff67fffffffffffffffffffffffffffffffff8b3fffffffffffffffffffff27ffffffffffffffffffffff93fffffffffffffffffffffffff,0x1000410000000000000000000000000000000000002080000000800000000000000000000000001ffffffffffffffffffffff858fffffff27fffffffffffffffffffffffffffffffffffffffffffffffff,0x2000880000000000008400000001000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffe1b1ffffff93fffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof209 : Floor 333 spec209 := floorChecked (by decide +kernel)
def book209 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else ⟨spec209,proof209⟩)
def spec216 : FloorData := (0xdc7805c000000000f002b003b0000000000000007c00d6000000000000000000000000000000000,5,[0x3ffffc75ff67ffffffffebffb9ffbdfffffffffffffffafff73fffffffffffffffffffffffffffffffffffffe3fffa3ffffffffffffd4fffffffffffffffffffffff29fffffffffffffffffffffffffffffffff,0x8800000000000000c00140010000000000000000300028000000000000000000000000000000001ffffff87fa3ffffffffffffffffc4ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffff576ff77ffffffffe1ffa9ffa9fffffffffffffffc7ffd3fffffffffffffffffffffffffffffffffffffffffffffffffffff0ffd4ffc4ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2080080000000001000400040000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffff83ff29fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof216 : Floor 333 spec216 := floorChecked (by decide +kernel)
def book216 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else (if i≤31 then ⟨spec209,proof209⟩ else ⟨spec216,proof216⟩))
def spec225 : FloorData := (0x7f00007ec0000000f00000000000019800000001e00000000000014c0000000000003260000000000,5,[0x200000000020000000000000200000000040000000000000100000000000000080000000001ffe0fffff13ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffebffff167fffffff5ffffffffffffecffffffffebfffffffffffff67ffffffffffffff3ffffffffffffffffff813ffffffffffffffffffffe67fffffffffffffffffffffeb3fffffffffffffffffffffffff,0x4c0000450000000000000000000000000000000300000000000002800000000000002000000000001ffffffffffffffffff0ffffffffffffe67ffffffffffffffffffffffffffffffffffffcd9ffffffffff,0x3ffb1ffff9a7fffffff9fffffffffffffcffffffffc3ffffffffffffd67ffffffffffffdb3fffffffffffffffffffffffffffffffffffffffffffffffffffe1ffffffffffffeb3ffffffffffffcd9ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof225 : Floor 333 spec225 := floorChecked (by decide +kernel)
def book225 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤31 then (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else ⟨spec209,proof209⟩) else (if i≤32 then ⟨spec216,proof216⟩ else ⟨spec225,proof225⟩))
def spec59 : FloorData := (0x3ffffffffe3ffcffffffffff7f,6,[0x10180a404002839409a890a4c0000000000000000000000000000000000000000000000000000000000383c1fe0e007cffe0ffc01f7f,0x2802a41ea024b090ca0323ac29ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03fe0ff1c07f01ff07ffff80,0x1a280008c80e0002ad201230b1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000fffff8301fff8001fff,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7b54ac003c8072331cc5c01c1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff001c00301ffffffe080,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4c6731313f0c7c00000600101ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000080])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof59 : Floor 333 spec59 := floorEx (audit_off (db:=book225) (branches:=guides) (g:=11) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book59 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤31 then (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else ⟨spec209,proof209⟩) else (if i≤33 then (if i≤32 then ⟨spec216,proof216⟩ else ⟨spec225,proof225⟩) else ⟨spec59,proof59⟩))
def spec122 : FloorData := (0x7f1ff3e3e1c7ce1f63e01f603c7c3e01f0ff80001f003b6000,6,[0x2006001408004000140068028002402a02400000a002280000000000000000000000000000000000000700f003e1c00e0003e01f603c003e01f00000001f003b6000,0x5000a240038a80120580120018280000c08e00002c00120001ffffffffffffffffffffffffffffffffff8e0fffc1ffff1e09fffe09fffffc1ffffffffffffffc49fff,0x340a0000010308068000000050b04800004800003000540001fffffffffffffffffffffffffffffffffffff0c1c1ffffffffc1fe09ffffffffe0f007fffffffffffff,0x3fffffffffffffffffffffffffffffffffafed5cbdbc7063e5383fe53fe7c7f3ff1f70ffffc1ffe93fffffffffffffffffffffffffffffffffffffffffffffe3831e09c1fe09fffffffffffffffffe0ffc49fff,0x3fffffffffffffffffffffffffffffffffc9f19f3e3e7c73f93e3ff93f870783fc1f80ffffc1ff893ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc383c1fe0f007fffe0ffc49fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof122 : Floor 333 spec122 := floorEx (audit_off (db:=book59) (branches:=guides) (g:=15) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book122 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤32 then (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else (if i≤31 then ⟨spec209,proof209⟩ else ⟨spec216,proof216⟩)) else (if i≤34 then (if i≤33 then ⟨spec225,proof225⟩ else ⟨spec59,proof59⟩) else ⟨spec122,proof122⟩))
def spec91 : FloorData := (0x1ffffedffffedefc000000000000001ffffcfffff,7,[0x106141080541070000000000000001409a890a4c00000000000000000000000000000000000000000003831e01c1fe00fc000000000000001e0ffc01fff,0x802400194183820000000000000000ca0303ac29fffffffffffffffffffffffffffffffffffffffffffc03e121fe1fff03fffffffffffffffff07ffff00,0x3fffffffffffffffffffffffffffffffffffffffffffea803635a836307ffffffffffffffead207231b1fffffffffffffffffffffffffffffffffffffffffffffc0121ffe12103ffffffffffffffffff8301fff,0x133498380000004000000000000000331cc1c00c1fffffffffffffffffffffffffffffffffffffffffffffffffe00012103fffffffffffffffffffffe000,0x3ffffffffffffffffffffffffffffffffffffffffffe4c123c26323c387ffffffffffffffc0000600101ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000300000])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof91 : Floor 333 spec91 := floorEx (audit_off (db:=book122) (branches:=guides) (g:=1322) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book91 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<29 then book195 i else (if i≤32 then (if i≤30 then (if i≤29 then ⟨spec201,proof201⟩ else ⟨spec202,proof202⟩) else (if i≤31 then ⟨spec209,proof209⟩ else ⟨spec216,proof216⟩)) else (if i≤34 then (if i≤33 then ⟨spec225,proof225⟩ else ⟨spec59,proof59⟩) else (if i≤35 then ⟨spec122,proof122⟩ else ⟨spec91,proof91⟩)))
def spec107 : FloorData := (0xfffffe0000001ffffffdc000000ffedbfd6e0000001f9f,7,[0x8040000000805410300000004040028180000000a0c00000000000000000000000000000000000000c1c1e0000001c1fe01dc000000e0e007d6e0000001f9f,0x601940000000194187820000001ea024b0900000002c29ffffffffffffffffffffffffffffffffffffff01fe1ffffffffe1ffe23ffffffff1247e91ffffffff60,0xaa400000000035a8121000000008c88600000000003131fffffffffffffffffffffffffffffffffffffffe001fffffffffe00023fffffffffff8291ffffffffff,0x3fffffffffffffffffffffffffffffffffffff54b5abffffffc00024247ffffff31378c7e3ffffffc0c1fffffffffffffffffffffffffffffffffffffffffffffffffe00000023fffffffffffffffffffffe060,0x3fffffffffffffffffffffffffffffffffffff9f2633ffffffe632383c7fffffe003c80723ffffffc1c1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff001240291ffffffe060])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof107 : Floor 333 spec107 := floorEx (audit_off (db:=book91) (branches:=guides) (g:=1376) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book107 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else ⟨spec107,proof107⟩
def spec115 : FloorData := (0x7ff001ffe003ff6e001f6f7c003fff000007dfe0007f6e000,7,[0x4000080400614100014107000180a000002838000a89000000000000000000000000000000000000000e0001c1e0031e00001e017c003c1f000007dfe0007c00000,0x200001940002400000185820002a4000000b0900003218001fffffffffffffffffffffffffffffffffff00ffffe1fffe091fffffe83ffffe0ffffffe01ffffffffff,0x4ca0000000049858000000400054ac000000120000c4c0001fffffffffffffffffffffffffffffffffffffffe001fffffffffe09083fffffffffff8201ffffffffff,0x3fffffffffffffffffffffffffffffffffffadfff5abff80363ffc36307ffe731fffffc7c3fff0723ffffffffffffffffffffffffffffffffffffffffffffffffc0091ffe09083ffffffffffffffffff8091fff,0x3ffffffffffffffffffffffffffffffffff931ffe633ff923a3ffe3a387ff8001fffff0603fff0123fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000fffff8201fff8091fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof115 : Floor 333 spec115 := floorEx (audit_off (db:=book107) (branches:=guides) (g:=1378) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book115 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩)
def spec121 : FloorData := (0x78ff0fe01e3fc1ffe01e001ec3fc01f00eed81b600f80000eb,7,[0x4000000410014100040005010000a004000028009000004400000000000000000000000000000000000e00c001e3801e0001e001ec38001f00e0001b600f80000eb,0x50000a40006a80120028001002280000088a00000120000191fffffffffffffffffffffffffffffffffff00ffffe1fffe001fffffe13ffffe0ffffffe49ffffffffff,0x30ca0000003301878000000407b002c00048012001c00000c1ffffffffffffffffffffffffffffffffffffff01fe1ffffffffe1ffe13ffffffff1127e49ffffffff14,0x3fffffffffffffffffffffffffffffffffafadf4bfeb807c243fc3ffe27cc7ff1ff374ffd3fe0ffffe29fffffffffffffffffffffffffffffffffffffffffffc03e001fe1ffe13fffffffffffffffff07ffff14,0x3fffffffffffffffffffffffffffffffffcf31ff3ff3cc7e383ff3fffa7807fc1fe3a4fe93fe0fffff29ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03fe0ff1127e49ff07ffff14])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof121 : Floor 333 spec121 := floorEx (audit_off (db:=book115) (branches:=guides) (g:=1342) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book121 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else ⟨spec121,proof121⟩)
def spec171 : FloorData := (0xfffff000000ffe7fffb8000000000000000000000000000000fff1bfe6e0000001f1f,7,[0x4020000008100a10600000000000000000000000000000004040028180000000a0c0000000000000010e0f000000c380f01b8000000000000000000000000000000e0e007e6e0000001f1f,0xc0ca0000001a808c7840000000000000000000000000000001ea024b0900000002c29ffffffffffffffe0ff0fffffffc18ffe47ffffffffffffffffffffffffffffffff0e47d91ffffffffe0,0x42000000001320c020000000000000000000000000000000008c80600000000003031ffffffffffffffff000ffffffffff00047fffffffffffffffffffffffffffffffffff8191ffffffffff,0x3ffffffffffffffb5ad5fffffe00b01428fffffffffffffffffffffffffffffff313f8c7e3ffffffc1c1fffffffffffffffffffffffff001800047fffffffffffffffffffffffffffffffffffffffffffffe0e0,0x3ffffffffffffff39319fffffe44f11838ffffffffffffffffffffffffffffffe003c80723ffffffc1c1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000e40191ffffffe0e0])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof171 : Floor 333 spec171 := floorEx (audit_off (db:=book121) (branches:=guides) (g:=294) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book171 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else (if i≤39 then ⟨spec121,proof121⟩ else ⟨spec171,proof171⟩))
def spec179 : FloorData := (0x7ff00fff00fff70000feff8000000000000000000000000003fff000007efe0007f6e000,7,[0x40004020185080000a10e000000000000000000000000000180a000002838000a890000000000000000e000e0f00c7800000f01f8000000000000000000000000003c1f000007efe0007c00000,0x20000ca00090000000c5840000000000000000000000000002a4000000b0900003218001ffffffffffff00ffff0fff808ffffffe07ffffffffffffffffffffffffffffe0ffffffd01ffffffffff,0x4ca0000001262c0000000800000000000000000000000000054ac000000120000c4c0001ffffffffffffffff000ffffffffff01007fffffffffffffffffffffffffffffffffff8101ffffffffff,0x3ffffffffffffadffad5fe00b1fffe1620fffffffffffffffffffffffffffe731fffffc7c3fff0723ffffffffffffffffffffffff0008ffff01007ffffffffffffffffffffffffffffffffffffffffff8091fff,0x3fffffffffff931ff319fe48d1ffff1a30fffffffffffffffffffffffffff8001fffff0603fff0123fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000fffff8101fff8091fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof179 : Floor 333 spec179 := floorEx (audit_off (db:=book171) (branches:=guides) (g:=308) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book179 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤39 then (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else ⟨spec121,proof121⟩) else (if i≤40 then ⟨spec171,proof171⟩ else ⟨spec179,proof179⟩))
def spec185 : FloorData := (0x38ff1f00f3f07ff03eb001d80000000000000000000000003fc01f00f2d82b600f800006b,7,[0x40000022005080100000a000000000000000000000000010000a0040000280090000044000000000000e01000f3007800380001d800000000000000000000000038001f00e0002b600f800006b,0x1000020004a00100214000000000000000000000000000002280000080a00000120000091ffffffffffff00ffff0fff800ffffffe27ffffffffffffffffffffffffffffe0ffffffd49ffffffffff,0x30ca000006c063c0010000800000000000000000000000007b002c00048012001c00000c1ffffffffffffffe0ff0fffffffc14ffe27ffffffffffffffffffffffffffffffff0d27d49ffffffff94,0x3ffffffffffefadf5ff581f0a1f8a9ffe4fffffffffffffffffffffffffcc7ff1ff3f4ffd3fe0fffff29fffffffffffffffffffc0f800fc14ffe27fffffffffffffffffffffffffffffffffffffffff07ffff94,0x3ffffffffffcf31f9ff991f8c1fce9fff4fffffffffffffffffffffffff807fc1fe3a4fe93fe0fffff29ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03fe0ff0d27d49ff07ffff94])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof185 : Floor 333 spec185 := floorEx (audit_off (db:=book179) (branches:=guides) (g:=316) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book185 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤39 then (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else ⟨spec121,proof121⟩) else (if i≤41 then (if i≤40 then ⟨spec171,proof171⟩ else ⟨spec179,proof179⟩) else ⟨spec185,proof185⟩))
def spec186 : FloorData := (0x3f1fef1f0cf387b3c6f0f600000000000000000000000003c7c3e01f13f80001f003b6000,7,[0x200c00a08010002808068000000000000000000000000028002402a02400000a0022800000000000000700e01f0c038003c000f600000000000000000000000003c003e01f00000001f003b6000,0x1000420018a0010301c020000000000000000000000000018280000c00e00002c00120001fffffffffff8e0ffe0fffc784fffff09fffffffffffffffffffffffffffffc1ffffffffffffffc49fff,0x340a000010c20340010000000000000000000000000000050b04800004800003000540001ffffffffffffff10e0fffffffc390f09ffffffffffffffffffffffffffffffffe0ec07fffffffffffff,0x3ffffffffffefedb5ede618fa987a1f53fffffffffffffffffffffffffe7c7f3ff1ff0ffffc1ffe93ffffffffffffffffffffff30c784c390f09fffffffffffffffffffffffffffffffffffffffffe0ffc49fff,0x3ffffffffffc9f139f1e71cfc9c7e1f93fffffffffffffffffffffffff870783fc1f80ffffc1ff893ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc383c1fe0ec07fffe0ffc49fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof186 : Floor 333 spec186 := floorEx (audit_off (db:=book185) (branches:=guides) (g:=326) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book186 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤40 then (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else (if i≤39 then ⟨spec121,proof121⟩ else ⟨spec171,proof171⟩)) else (if i≤42 then (if i≤41 then ⟨spec179,proof179⟩ else ⟨spec185,proof185⟩) else ⟨spec186,proof186⟩))
def spec203 : FloorData := (0x3fff5c00000000000000ffb7f5eb80000000000000001fffededc0000000000000000000001f9f,7,[0x8200000000000000008100a10600000000000000000805410300000000000000000000000a0c0000008470000000000000000c380f00b80000000000000001c1fe00dc0000000000000000000001f9f,0x20900000000000000001a808c38400000000000000001941838200000000000000000000002c29ffffff078a3fffffffffffffffc48fff47fffffffffffffffffe1fff23fffffffffffffffffffffff60,0x3ffffff50167ffffffffffffff32bc1628fffffffffffffffff5a836347ffffffffffffffffffffff1f1fffffff80a3ffffffffffffffffff0a147ffffffffffffffffffe12123fffffffffffffffffffffffff,0x3fffffd62577fffffffffffffe00b01428ffffffffffffffffe6323c3c7fffffffffffffffffffffc1c1fffffffffffffffffffffffff00480a147fffffffffffffffffffffffffffffffffffffffffffffe060,0x84880000000000000004441081000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffe00012123fffffffffffffffffffffe060])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof203 : Floor 333 spec203 := floorEx (audit_off (db:=book186) (branches:=guides) (g:=1234) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book203 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<37 then book91 i else (if i≤40 then (if i≤38 then (if i≤37 then ⟨spec107,proof107⟩ else ⟨spec115,proof115⟩) else (if i≤39 then ⟨spec121,proof121⟩ else ⟨spec171,proof171⟩)) else (if i≤42 then (if i≤41 then ⟨spec179,proof179⟩ else ⟨spec185,proof185⟩) else (if i≤43 then ⟨spec186,proof186⟩ else ⟨spec203,proof203⟩)))
def spec210 : FloorData := (0x1c0384c00000000003823000004600000000000000e046000046000000000000000000000026000,7,[0x10000000000000100000000080000000000000040000000080000000000000000000000080000000000380000000000003800000004600000000000000e000000046000000000000000000000026000,0x800000000000000020040000000000000000000008008000000000000000000000000000040001fffffffc7b3fffffffffffffffffffb9ffffffffffffffffffffffb9fffffffffffffffffffffffffff,0x1002010000000000000000000000000000000000010080000080000000000000000000000000001fffffffffffffffffffffc7dcfffffb9ffffffffffffffffffffffffffffffffffffffffffffffd9fff,0x3ffffe7fcfe7ffffffffffcff9ffffff3fffffffffffffe3f73ffff73ffffffffffffffffffffffb3fffffffffffffffffffffffffffffffffffffffffffffffff1fb9ffffb9ffffffffffffffffffffffd9fff])
def next210 := successors 333 5 spec210.basis
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_0 : Block 333 5 next210 0 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,1250]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_1 : Block 333 5 next210 2 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,37]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_2 : Block 333 5 next210 4 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,1266]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_3 : Block 333 5 next210 6 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,25]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_4 : Block 333 5 next210 8 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,1274]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_5 : Block 333 5 next210 10 2 := block_off (db:=book203) (branches:=guides) (ts:=[39,15]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_6 : Block 333 5 next210 12 2 := block_off (db:=book203) (branches:=guides) (ts:=[37,1290]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_7 : Block 333 5 next210 14 2 := block_off (db:=book203) (branches:=guides) (ts:=[37,25]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_8 : Block 333 5 next210 16 2 := block_off (db:=book203) (branches:=guides) (ts:=[37,1296]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_9 : Block 333 5 next210 18 2 := block_off (db:=book203) (branches:=guides) (ts:=[37,15]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_10 : Block 333 5 next210 20 2 := block_off (db:=book203) (branches:=guides) (ts:=[25,1306]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block210_11 : Block 333 5 next210 22 2 := block_off (db:=book203) (branches:=guides) (ts:=[25,15]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof210 : Floor 333 spec210 := by
  apply floorEx _ (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=12) (width:=2) (vs:=next210) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact block210_0
  · exact block210_1
  · exact block210_2
  · exact block210_3
  · exact block210_4
  · exact block210_5
  · exact block210_6
  · exact block210_7
  · exact block210_8
  · exact block210_9
  · exact block210_10
  · exact block210_11
def book210 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else ⟨spec210,proof210⟩
def spec217 : FloorData := (0xfcf875c000000003f07af03bb000d80000000003fc1ede01e000ec00000000000000000f80000eb,7,[0x4000200000000002005080100000a0000000000100141000400050000000000000000009000004400002080700000000003007800380000d80000000003801e0001e000ec00000000000000000f80000eb,0x3ffff875f167ffffffffcbf0b1fabdffe4ffffffffffeafc363febfff27fffffffffffffffff2fffffb9ffffc3ff8a3fffffffffff850fffffff27ffffffffffffe121ffffff13fffffffffffffffffffffffff,0xc800000000000006c061c00100008000000000033018380000004000000000000000001c00000c1ffffff078a3fffffffffffffffc44fff27fffffffffffffffffe1fff13fffffffffffffffffffffff14,0x3ffff176f577ffffffff81f0a1f8a9ffe4ffffffffffcc7e3c3ff3fffa7ffffffffffffffffe0fffff29fffffffffffffffffffc0f850fc44fff27fffffffffffffffffffffffffffffffffffffffff07ffff14,0x2080880000000001008400440001000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffc03e121fe1fff13fffffffffffffffff07ffff14])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof217 : Floor 333 spec217 := floorEx (audit_off (db:=book210) (branches:=guides) (g:=1310) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book217 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩)
def spec227 : FloorData := (0x3ff0007fec00000fff0000000000fefb8000001ffe0000000001f6f5c000000000007f6e0000000000,7,[0x8200000004020000000000a106000000080400000000014103000000000000281800000000000060000470000000e0f0000000000f01b8000001c1e0000000001e015c000000000007f6e0000000000,0x100000900000000ca00000000000c584000000194000000000018582000000000000b0900000000001ff80ffff813fffffff0ffffffffffffe47fffffffe1ffffffffffffea3ffffffffffffc91ffffffffff,0x3ffebfff0167fffffad5fffffffffe1628fffffff5abfffffffffc36347fffffffffffc7e3fffffffffffffffff8013ffffffffffffffffff01047ffffffffffffffffffe090a3fffffffffffffffffffffffff,0x24c0002450000000000000000000000000000026300000000002282800000000000002000000000001ffffffffffffffff000ffffffffff01047fffffffffffffffffffffffffffffffffff8091ffffffffff,0x3fcb1fff49a7fffff319ffffffffff1a38ffffffc003fffffffffc12147fffffffffff0523fffffffffffffffffffffffffffffffffffffffffffffffffe001fffffffffe090a3fffffffffff8091ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof227 : Floor 333 spec227 := floorEx (audit_off (db:=book217) (branches:=guides) (g:=1330) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book227 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else ⟨spec227,proof227⟩)
def spec233 : FloorData := (0x1c7f00f87fc0001f00f00000003f3001980000fe01e000000001e001cc00000000fc98326000000008b,7,[0x200000000020000000100000200000000040000000004000100000000040000080000000004006000807000001000f0000000380001980000c001e000000001e001cc00000000e000326000000008b,0x8000150020000020000000000224000000000a40000000000028001000000000088200000000000111ff80ffff803fffffff0ffffffffffffe67fffffffe1ffffffffffffe33ffffffffffffcd9ffffffffff,0x3f7ebfe0f147ffff5ff5fffffff899ffecfffff4bfebffffffffc3ffe67ffffffff37cfff3fffffffee9ffffff07803fffffffffffffffc0cffe67fffffffffffffffffe1ffe33fffffffffffffffffffffff74,0x184c0160470000000000000000020000000001f00300000000030003800000000018002000000000101ffffffffffffffe0ff0fffffffc0cffe67ffffffffffffffffffffffffffffffff0367cd9ffffffff74,0x3e7b1fe8f987ffff9ff9fffffffcd9fffcffffe03fc3ffffffffc3ffc67fffffffe26cfdb3fffffffee9ffffffffffffffffffffffffffffffffffffff01fe1ffffffffe1ffe33ffffffff0367cd9ffffffff74])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof233 : Floor 333 spec233 := floorEx (audit_off (db:=book227) (branches:=guides) (g:=1344) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book233 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else (if i≤47 then ⟨spec227,proof227⟩ else ⟨spec233,proof233⟩))
def spec234 : FloorData := (0x1f9f037b8fc000ef1f00000003c770f600000f3e3e000000003e01f6000000001f1db80000000000000,7,[0x1000201000000c00a00000002808068000006001400000000140068000000002a0240000000000000003800303800000e01f00000003c000f600000f003e000000003e01f6000000001f00000000000000000,0x800065002000042000000000302c02000000a240000000000580120000000000c08600000000000001fc60fffc703fffffe0ffffffffffff09ffffffffc1fffffffffffe09fffffffffffffffffffffffffff,0x3f7ebf908f47fffb5edfffffff8791f53fffff5cbdbffffffff83fe53fffffffff1f78fffffffffffffffffffc84703ffffffffffffffc388f09ffffffffffffffffffc1fe09fffffffffffffffffffffffffff,0x1a0c0462070000000000000000020000000018706000000000600380000000000018000000000000001ffffffffffffff10e0fffffffc388f09ffffffffffffffffffffffffffffffffe0e247fffffffffffff,0x3e4f1f98cf87fff39f1fffffffc7d1f93ffffe18383ffffffff83fc13ffffffffc1e48fffffffffffffffffffffffffffffffffffffffffffffffffff0c1c1ffffffffc1fe09ffffffffe0e247fffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof234 : Floor 333 spec234 := floorEx (audit_off (db:=book233) (branches:=guides) (g:=1370) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book234 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤47 then (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else ⟨spec227,proof227⟩) else (if i≤48 then ⟨spec233,proof233⟩ else ⟨spec234,proof234⟩))
def spec241 : FloorData := (0xe07f3c007ec0ff0000f0007f70000001d80ff00001e0001f6e0000016c00001f0000003b60000000000,7,[0x4000200040000020005080000000a004000000400014100000005000000a0000000280000000000006020007000e00000f0007800000001d80e000001e0001e000000016c00001f0000003b60000000000,0x400048000000ca0000000062c0000000800ca00000000018580000004000002c0000001200000000001ff80ffff813fffffff0ffffffffffffe27fffffffe1ffffffffffffe93ffffffffffffc49ffffffffff,0x3ffeb87ff167fadffff5fff0b1ffffffe4ffadffffebfffc363ffffff27fffff1fffffffd3ffffffffffffffc3ff813fffffffffff808ffffffe27ffffffffffffe091fffffe93fffffffffffffffffffffffff,0x804c1000450000000000000000000000001300000300002280000002800000000000002000000000001ffffffffffff00ffff0fff808ffffffe27ffffffffffffffffffffffffffffe0ffffffc49ffffffffff,0x33fb1a7ff9a7f31ffff9fff8d1fffffff4fe01ffffc3fffc123fffffd27ffffc1ffffffc93fffffffffffffffffffffffffffffffffffffffffffff00ffffe1fffe091fffffe93ffffe0ffffffc49ffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof241 : Floor 333 spec241 := floorEx (audit_off (db:=book234) (branches:=guides) (g:=1352) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book241 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤47 then (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else ⟨spec227,proof227⟩) else (if i≤49 then (if i≤48 then ⟨spec233,proof233⟩ else ⟨spec234,proof234⟩) else ⟨spec241,proof241⟩))
def spec248 : FloorData := (0xfc1fdc780ff81f0f0000f007b007b0000781f03e00007c01f60000000007c000001ed80000000000000,7,[0x8018050021000020000a00100034000050000240000a80120000000000280000008a000000000000001c00c0780038000f0000f0000007b0000780003e00007c00000000000007c000001ed80000000000000,0x4000880000300a000000c003400100000300a0000000300068000000000b00000004800000000000001e3e0ff87f03ffff0fffffffffff84fffffffffc1ffffffffffffffffffffffffffe127fffffffffffff,0x3f7ea470ff46fedf5fffe1ffa9ff89ffffafedfcbffff07fe53fffffffffc7ffffff74ffffffffffffffffff2387f03fffffffff0ff84ff84fffffffffffffff83fe09fffffffffffffffffffffffffffffffff,0x980d10600700000000000000000200000c0300700000c00380000000000000000018000000000000001ffffffffffc7e0f0ffff0ff84ff84ffffffffffffffffffffffffffffff83fffffe127fffffffffffff,0x327f0678ff84ff1f9ffff1ffc9ffc9ffff0fc1f83ffff07fc13fffffffff07fffffe24fffffffffffffffffffffffffffffffffffffffffffffff87e0fc1ffff83fe09fffffffff83fffffe127fffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof248 : Floor 333 spec248 := floorEx (audit_off (db:=book241) (branches:=guides) (g:=1362) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book248 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤48 then (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else (if i≤47 then ⟨spec227,proof227⟩ else ⟨spec233,proof233⟩)) else (if i≤50 then (if i≤49 then ⟨spec234,proof234⟩ else ⟨spec241,proof241⟩) else ⟨spec248,proof248⟩))
def spec155 : FloorData := (0xffffafffaff5ef8000000000000000000000000000000000000001ffffcfff7f,8,[0x2185088100a10e0000000000000000000000000000000000000001409a890a4c000000000000000000030c780c380f00f8000000000000000000000000000000000000001e0ffc01f7f,0x809001a808c3840000000000000000000000000000000000000000ca0303ac29fffffffffffffffffffc0f850fc50fff07fffffffffffffffffffffffffffffffffffffffff07ffff80,0x3fffffffffffffffffffca00b132bc1620fffffffffffffffffffffffffffffffffffffffead207231b1fffffffffffffffffffff0050ffff0a107ffffffffffffffffffffffffffffffffffffffffff8301fff,0x3fffffffffffffffffff6d26bc00b01428ffffffffffffffffffffffffffffffffffffffff31cc7c01c1fffffffffffffffffffffffff00500a107fffffffffffffffffffffffffffffffffffffffffffffe080,0x1048404441081000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000300080])
def next155 := successors 333 6 spec155.basis
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_0 : Block 333 6 next155 0 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,212]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_1 : Block 333 6 next155 2 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,51]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_2 : Block 333 6 next155 4 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,25]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_3 : Block 333 6 next155 6 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,49]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_4 : Block 333 6 next155 8 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,222]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_5 : Block 333 6 next155 10 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,47]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_6 : Block 333 6 next155 12 2 := block_off (db:=book248) (branches:=guides) (ts:=[51,232]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_7 : Block 333 6 next155 14 2 := block_off (db:=book248) (branches:=guides) (ts:=[51,49]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_8 : Block 333 6 next155 16 2 := block_off (db:=book248) (branches:=guides) (ts:=[51,23]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_9 : Block 333 6 next155 18 2 := block_off (db:=book248) (branches:=guides) (ts:=[51,47]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_10 : Block 333 6 next155 20 2 := block_off (db:=book248) (branches:=guides) (ts:=[49,242]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_11 : Block 333 6 next155 22 2 := block_off (db:=book248) (branches:=guides) (ts:=[47,49]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_12 : Block 333 6 next155 24 2 := block_off (db:=book248) (branches:=guides) (ts:=[53,248]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_13 : Block 333 6 next155 26 2 := block_off (db:=book248) (branches:=guides) (ts:=[256,53]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_14 : Block 333 6 next155 28 2 := block_off (db:=book248) (branches:=guides) (ts:=[51,262]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_15 : Block 333 6 next155 30 2 := block_off (db:=book248) (branches:=guides) (ts:=[270,51]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_16 : Block 333 6 next155 32 2 := block_off (db:=book248) (branches:=guides) (ts:=[49,274]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_17 : Block 333 6 next155 34 2 := block_off (db:=book248) (branches:=guides) (ts:=[276,49]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_18 : Block 333 6 next155 36 2 := block_off (db:=book248) (branches:=guides) (ts:=[47,280]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block155_19 : Block 333 6 next155 38 2 := block_off (db:=book248) (branches:=guides) (ts:=[282,47]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof155 : Floor 333 spec155 := by
  apply floorEx _ (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=20) (width:=2) (vs:=next155) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact block155_0
  · exact block155_1
  · exact block155_2
  · exact block155_3
  · exact block155_4
  · exact block155_5
  · exact block155_6
  · exact block155_7
  · exact block155_8
  · exact block155_9
  · exact block155_10
  · exact block155_11
  · exact block155_12
  · exact block155_13
  · exact block155_14
  · exact block155_15
  · exact block155_16
  · exact block155_17
  · exact block155_18
  · exact block155_19
def book155 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<45 then book203 i else (if i≤48 then (if i≤46 then (if i≤45 then ⟨spec210,proof210⟩ else ⟨spec217,proof217⟩) else (if i≤47 then ⟨spec227,proof227⟩ else ⟨spec233,proof233⟩)) else (if i≤50 then (if i≤49 then ⟨spec234,proof234⟩ else ⟨spec241,proof241⟩) else (if i≤51 then ⟨spec248,proof248⟩ else ⟨spec155,proof155⟩)))
def spec211 : FloorData := (0x3c07f4c0000000000ffa70000f4ef8000000000003fe4e001e4e7c0000000000000000007c6e000,8,[0x3ffffc7f8367ffffffffff85b9fffeb72effffffffffffe1773ffd77377ffffffffffffffffffafb3fffffffe3fc7b3ffffffffffc7d8fffffb1ffffffffffffff1fb1ffffb1ffffffffffffffffffffff91fff,0x9000000000000090000000c18400000000000024000001818200000000000000000003018000000000078000000000000f8000000f4e00000000000003e000001e4e000000000000000000007c6e000,0x3ffffcff0167ffffffffff26bdfffe1628ffffffffffffc9b7bffc36347ffffffffffffffffffc7e3ffffffffff80b3ffffffffffffffffff0b107ffffffffffffffffffe1b183fffffffffffffffffffffffff,0x1002410000000000000000000000000000000000012080002080800000000000000000000000001fffffffffffffffffffff0058ffff0b107ffffffffffffffffffffffffffffffffffffffffff8391fff,0x2004880000000000048400001081000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffc01b1ffe1b183ffffffffffffffffff8391fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof211 : Floor 333 spec211 := floorEx (audit_off (db:=book155) (branches:=guides) (g:=91) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book211 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else ⟨spec211,proof211⟩
def spec218 : FloorData := (0xdf7b85c00000000cf382b3c3f05600000000001c7ce0d63e00d6000000000000000001f000b6000,8,[0x201000000000008010002808028000000000008004000140028000000000000000000a000280000000030380000000000c038003c0005600000000001c00e0003e00d6000000000000000001f000b6000,0x3ffffc758f67ffffffffeb8fb9b7bdf73ffffffffffffae3f73dbff73fffffffffffffffffedfffb3fffffffe3fc7a3ffffffffffc7d4fffffa9ffffffffffffff1f29ffff29ffffffffffffffffffffff49fff,0x8800000000000010c20140010000000000000010308028000000000000000000000003000140001fffffc847a3ffffffffffffffc3c0fa9ffffffffffffffffffc1ff29fffffffffffffffffffffffffff,0x3ffff556af77fffffffe618fa987a1f53ffffffffffe7c73fd3e3ffd3fffffffffffffffffc1ffe93ffffffffffffffffffffff30c7d4c3c0fa9fffffffffffffffffffffffffffffffffffffffffe0fff49fff,0x2084080000000001040404040080000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffe3831f29c1ff29fffffffffffffffffe0fff49fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof218 : Floor 333 spec218 := floorEx (audit_off (db:=book211) (branches:=guides) (g:=91) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book218 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩)
def spec219 : FloorData := (0xfffff5c00000000ffffafffbff5ef8000000001ffffedffffedefc000000000000001ffffcfffff,9,[0x4008200000000002185088100a10e0000000000106141080541070000000000000001409a890a4c000020847000000000030c780c380f00f80000000003831e01c1fe00fc000000000000001e0ffc01fff,0x20900000000000809001a808c3840000000000802400194183820000000000000000ca0303ac280000030780000000000c0f800fc00f5e00000000001c03e001fe1ede00000000000000001ff07cfff00,0x3ffff8750167ffffffffca00b132bc1620ffffffffffea803635a836307ffffffffffffffead207231b1ffffc3f80a3ffffffffff0050ffff0a107fffffffffffc0121ffe12103ffffffffffffffffff8301fff,0xc800000000000016d261c00100008000000000133498380000004000000000000000331cc1c00c1fffffc000a3ffffffffffffff00400a107fffffffffffffffe00012103fffffffffffffffffffffe000,0x3ffff1562577fffffffe0000a000a01420fffffffffe4c123c26323c387ffffffffffffffc0000600101fffffffffffffffffff00005000400a107ffffffffffffffffffffffffffffffffffffffe0000300000,0x2084880000000001048404441081000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffe000012000012103ffffffffffffffe0000300000])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof219 : Floor 333 spec219 := floorEx (audit_off (db:=book218) (branches:=guides) (g:=109) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book219 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else ⟨spec219,proof219⟩)
def spec235 : FloorData := (0x1fff03ffffc000fffff000000fff7fffb8000fffffe0000001ffffffdc000000fffdbff6e0000001f9f,9,[0x8200000004020000008100a10600000008040000000805410300000004040028180000000a0c0060008470000010e0f000000c380f01b80000c1c1e0000001c1fe01dc000000e0e007f6e0000001f9f,0x1000209000000c0ca0000001a808c7840000601940000000194187820000001ea024b0900000002c2803800307800000e0ff0000000fc00ffe00000f01fe00000001fe1ffe00000000ff0007c000000001f00,0x800075002000042000000001322c02000000aa400000000035a8121000000008c88600000000003131fc00fff8003fffff000ffffffffff00047fffffe001fffffffffe00023fffffffffff8091ffffffffff,0x3f7ebf800147fffb5ad5fffffe00901428ffff54b5abffffffc00024247ffffff31378c7e3ffffffc0c1fffffc00003ffffffffffffff000800047fffffffffffffffe00000023fffffffffffffffffffffe060,0x1a4c0562470000000000000000020000000019f26300000002632383800000000018002000000000101ffffffffffffff00000ffffff000800047ffffffffffffffffffffffffffffff000240091ffffffe060,0x3e4b1f884987fff39319fffffe44d11838fffe000003ffffffc00000047fffffe002480523ffffffc0c1fffffffffffffffffffffffffffffffffffff000001ffffffe00000023ffffff000240091ffffffe060])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof235 : Floor 333 spec235 := floorEx (audit_off (db:=book219) (branches:=guides) (g:=1372) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book235 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else (if i≤55 then ⟨spec219,proof219⟩ else ⟨spec235,proof235⟩))
def spec243 : FloorData := (0xe3ff3c07fec7ff00fff00fff70000feff87ff001ffe003ff6e001f6f7c003fff000007ffe0007f6e000,9,[0x4008200040004020185080000a10e004000080400614100014107000180a000002838000a890000006020047000e000e0f00c7800000f01f80e0001c1e0031e00001e017c003c1f000007ffe0007c00000,0x100000900020000ca00090000000c5840200001940002400000185820002a4000000b09000032180000380000780070000ff000f8000000fee00700001fe0003e000001f6e00003fe0000007c000007f6e000,0x400048000004ca0000001262c0000000804ca0000000049858000000400054ac000000120000c4c0001fc00fff8013fffff000ffffffffff01007fffffe001fffffffffe09083fffffffffff8001ffffffffff,0x3ffeb87f0167fadffad5fe00b1fffe1620ffadfff5abff80363ffc36307ffe731fffffc7c3fff0723fffffffc3f8013ffffffffff0008ffff01007fffffffffffc0091ffe09083ffffffffffffffffff8091fff,0x824c1002450000000000000000000000009300026300012280002282800000000000002000000000001fffffffffff800ff000ff0008ffff01007ffffffffffffffffffffffffffc000fffff8001fff8091fff,0x33cb1a7f49a7931ff319fe48d1ffff1a30f001ffc003ff80123ffc12107ff8001fffff0403fff0123fffffffffffffffffffffffffffffffffffff800ffe001ffc0091ffe09083ffc000fffff8001fff8091fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof243 : Floor 333 spec243 := floorEx (audit_off (db:=book235) (branches:=guides) (g:=107) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book243 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤55 then (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else ⟨spec219,proof219⟩) else (if i≤56 then ⟨spec235,proof235⟩ else ⟨spec243,proof243⟩))
def spec249 : FloorData := (0xfc7ffcf87ff8ff1f00f3f07ff03fb001df8ff0fe01e3fc1ffe01e001ec3fc01f00fed83b600f80000eb,9,[0x4000200040000022005080100000a004000000410014100040005010000a0040000280090000044006020807000e01000f3007800380001d80e00c001e3801e0001e001ec38001f00e0003b600f80000eb,0x8018150021000020004a00100234000050000a40006a80120028001002280000088a000001200001901c00c0f80038001f0003f000003fb000078000fe0003fc000001e000003fc00000fed800000f80000eb,0x4000c8000030ca000006c063c0010000830ca0000003301878000000407b002c00048012001c00000c1e380ff07803fffe0ff0fffffffc04ffe27ffff01fe1ffffffffe1ffe13ffffffff0127c49ffffffff14,0x3f7ea060f146fadf5ff581f0a1f889ffe4afadf4bfeb807c243fc3ffe27cc7ff1ff374ffd3fe0ffffe29ffff0307803ffffffffc0f800fc04ffe27fffffffffc03e001fe1ffe13fffffffffffffffff07ffff14,0x984d11604700000000000000000200000c1301f00304c02380030003800000000018002000000000101ffffffffffc700e0ff0c0f800fc04ffe27ffffffffffffffffffffffffc03fe0ff0127c49ff07ffff14,0x327b0268f984f31f9ff991f8c1fcc9fff40e01e03fc3807c003fc3ffc27807fc1fe224fc93fe0ffffe29fffffffffffffffffffffffffffffffff8700f01fe1c03e001fe1ffe13c03fe0ff0127c49ff07ffff14])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof249 : Floor 333 spec249 := floorEx (audit_off (db:=book243) (branches:=guides) (g:=1332) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book249 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤55 then (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else ⟨spec219,proof219⟩) else (if i≤57 then (if i≤56 then ⟨spec235,proof235⟩ else ⟨spec243,proof243⟩) else ⟨spec249,proof249⟩))
def spec250 : FloorData := (0xff9fdf7b8fff1fef1f0cf387b3c7f0f607f1ff3e3e1c7ce1f63e01f603c7c3e01f1ff80001f003b6000,9,[0x1000201000200c00a08010002808068002006001408004000140068028002402a02400000a0022800003800303800700e01f0c038003c000f600700f003e1c00e0003e01f603c003e01f00000001f003b6000,0x8018650021000420018a0010303c02005000a240038a80120580120018280000c08e00002c001200001c00c378003800ef000cf00003c7f00007800f3e001c7c00003e000003c7c0001f1ff80001f00000000,0x4000880000340a000010c203400100000340a0000010308068000000050b04800004800003000540001e060fc84703fff10e0fffffffc380f09fffff0c1c1ffffffffc1fe09ffffffffe0e007fffffffffffff,0x3f7ea4108f46fedb5ede618fa98781f53fafed5cbdbc7063e5383fe53fe7c7f3ff1f70ffffc1ffe93fffffff2084703ffffffff30c784c380f09ffffffffffe3831e09c1fe09fffffffffffffffffe0ffc49fff,0x9a0d14620700000000000000000200000c8318706020c10380600380000000000018000000000000001ffffffffffc0e010e0f30c784c380f09fffffffffffffffffffffffffc383c1fe0e007fffe0ffc49fff,0x324f0618cf849f139f1e71cfc9c7c1f93f01c018383c7063c1383fc13f870783fc1e00ffffc1ff893ffffffffffffffffffffffffffffffffffff80e00c1c1e3831e09c1fe09fc383c1fe0e007fffe0ffc49fff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof250 : Floor 333 spec250 := floorEx (audit_off (db:=book249) (branches:=guides) (g:=109) (by decide) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def book250 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤56 then (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else (if i≤55 then ⟨spec219,proof219⟩ else ⟨spec235,proof235⟩)) else (if i≤58 then (if i≤57 then ⟨spec243,proof243⟩ else ⟨spec249,proof249⟩) else ⟨spec250,proof250⟩))
def spec123 : FloorData := (0x7ffffffffffffffffffffffffffffffffefffdffffffffffff,10,[0x4000080410614108054107010180a404002839409a890a4c00000000000000000000000000000000000e00c1c1e3831e01c1fe01fc383c1fe0e007dffe0ffc01fff,0x200601940802400194187822802a41ea024b090ca0323ac280000000000000000000000000000000000700f01fe1c03e001fe1ffe03c03fe0ff0007c01ff07ffff00,0x5000aa4003ea801235a812101a280008c88e0002ad201231b1ffffffffffffffffffffffffffffffffff800ffe001ffc0001ffe00003ffc000fffff8201fff8001fff,0x34ca0000013349878000000457b54ac00048012331cc5c00c1fffffffffffffffffffffffffffffffffffff000001ffffffe00000003ffffff001000201ffffffe000,0x3fffffffffffffffffffffffffffffffffafad54b5a80000240000242064c673131370c7c00000600001ffffffffffffffffffffffffffffffffffffffffffe000000000000003ffffffffffffffe0000000000,0x3fffffffffffffffffffffffffffffffffc9319f26324c12382632383800000000038006000000000101fffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000010002000000000000])
def next123 := successors 333 8 spec123.basis
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_0 : Block 333 8 next123 0 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1490]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_1 : Block 333 8 next123 2 2 := block_off (db:=book250) (branches:=guides) (ts:=[1506,79]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_2 : Block 333 8 next123 4 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,1542]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_3 : Block 333 8 next123 6 2 := block_off (db:=book250) (branches:=guides) (ts:=[1562,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_4 : Block 333 8 next123 8 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,1630]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_5 : Block 333 8 next123 10 2 := block_off (db:=book250) (branches:=guides) (ts:=[1646,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_6 : Block 333 8 next123 12 2 := block_off (db:=book250) (branches:=guides) (ts:=[73,1676]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_7 : Block 333 8 next123 14 2 := block_off (db:=book250) (branches:=guides) (ts:=[1690,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_8 : Block 333 8 next123 16 2 := block_off (db:=book250) (branches:=guides) (ts:=[1700,1770]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_9 : Block 333 8 next123 18 2 := block_off (db:=book250) (branches:=guides) (ts:=[1782,1794]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_10 : Block 333 8 next123 20 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1850]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_11 : Block 333 8 next123 22 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_12 : Block 333 8 next123 24 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1866]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_13 : Block 333 8 next123 26 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,75]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_14 : Block 333 8 next123 28 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1912]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_15 : Block 333 8 next123 30 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_16 : Block 333 8 next123 32 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1928]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_17 : Block 333 8 next123 34 2 := block_off (db:=book250) (branches:=guides) (ts:=[79,1942]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_18 : Block 333 8 next123 36 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,1966]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_19 : Block 333 8 next123 38 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_20 : Block 333 8 next123 40 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,2032]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_21 : Block 333 8 next123 42 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,2046]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_22 : Block 333 8 next123 44 2 := block_off (db:=book250) (branches:=guides) (ts:=[77,2088]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_23 : Block 333 8 next123 46 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,77]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_24 : Block 333 8 next123 48 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,2128]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_25 : Block 333 8 next123 50 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,73]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_26 : Block 333 8 next123 52 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,2144]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_27 : Block 333 8 next123 54 2 := block_off (db:=book250) (branches:=guides) (ts:=[75,2154]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_28 : Block 333 8 next123 56 2 := block_off (db:=book250) (branches:=guides) (ts:=[73,2210]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block123_29 : Block 333 8 next123 58 2 := block_off (db:=book250) (branches:=guides) (ts:=[73,2224]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof123 : Floor 333 spec123 := by
  apply floorEx _ (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=30) (width:=2) (vs:=next123) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact block123_0
  · exact block123_1
  · exact block123_2
  · exact block123_3
  · exact block123_4
  · exact block123_5
  · exact block123_6
  · exact block123_7
  · exact block123_8
  · exact block123_9
  · exact block123_10
  · exact block123_11
  · exact block123_12
  · exact block123_13
  · exact block123_14
  · exact block123_15
  · exact block123_16
  · exact block123_17
  · exact block123_18
  · exact block123_19
  · exact block123_20
  · exact block123_21
  · exact block123_22
  · exact block123_23
  · exact block123_24
  · exact block123_25
  · exact block123_26
  · exact block123_27
  · exact block123_28
  · exact block123_29
def book123 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<53 then book155 i else (if i≤56 then (if i≤54 then (if i≤53 then ⟨spec211,proof211⟩ else ⟨spec218,proof218⟩) else (if i≤55 then ⟨spec219,proof219⟩ else ⟨spec235,proof235⟩)) else (if i≤58 then (if i≤57 then ⟨spec243,proof243⟩ else ⟨spec249,proof249⟩) else (if i≤59 then ⟨spec250,proof250⟩ else ⟨spec123,proof123⟩)))
def spec187 : FloorData := (0x3ffffffffffffffffefffff8000000000000000000000003fffffffff3ffeffffffffff7f,10,[0x40004022185088100a10e000000000000000000000000010180a404002839409a890a4c000000000000e010e0f30c780c380f01f8000000000000000000000000383c1fe0e007effe0ffc01f7f,0x200c0ca0809001a808c7840000000000000000000000002802a41ea024b090ca0323ac2800000000000700e0ff0c0f800fc00ffe00000000000000000000000003c03fe0ff0007c01ff07ffff00,0x100042001ca0011321c02000000000000000000000000001a280008c80e0002ad201230b1fffffffffff800ff000ff0000ffff00007ffffffffffffffffffffffffffc000fffff8101fff8001fff,0x34ca000016d263c0010000800000000000000000000000057b54ac00048012331cc5c00c1ffffffffffffff00000ffffff001000007ffffffffffffffffffffffffffffff000c00101ffffffe080,0x3ffffffffffefadb5ad40000a000a01420ffffffffffffffffffffffffe4c6731313f0c7c00000600101fffffffffffffffffff000000001000007ffffffffffffffffffffffffffffffffffffffe0000000080,0x3ffffffffffc931393181048c044e11830ffffffffffffffffffffffff80000000038006000000000101fffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000c001000000000080])
def next187 := successors 333 8 spec187.basis
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_0 : Block 333 8 next187 0 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,420]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_1 : Block 333 8 next187 2 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,85]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_2 : Block 333 8 next187 4 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,524]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_3 : Block 333 8 next187 6 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,83]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_4 : Block 333 8 next187 8 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,584]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_5 : Block 333 8 next187 10 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,81]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_6 : Block 333 8 next187 12 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_7 : Block 333 8 next187 14 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_8 : Block 333 8 next187 16 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,698]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_9 : Block 333 8 next187 18 2 := block_off (db:=book123) (branches:=guides) (ts:=[87,722]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_10 : Block 333 8 next187 20 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,778]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_11 : Block 333 8 next187 22 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,83]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_12 : Block 333 8 next187 24 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,786]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_13 : Block 333 8 next187 26 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,81]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_14 : Block 333 8 next187 28 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_15 : Block 333 8 next187 30 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_16 : Block 333 8 next187 32 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,802]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_17 : Block 333 8 next187 34 2 := block_off (db:=book123) (branches:=guides) (ts:=[85,826]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_18 : Block 333 8 next187 36 2 := block_off (db:=book123) (branches:=guides) (ts:=[83,872]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_19 : Block 333 8 next187 38 2 := block_off (db:=book123) (branches:=guides) (ts:=[83,81]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_20 : Block 333 8 next187 40 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_21 : Block 333 8 next187 42 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_22 : Block 333 8 next187 44 2 := block_off (db:=book123) (branches:=guides) (ts:=[83,976]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_23 : Block 333 8 next187 46 2 := block_off (db:=book123) (branches:=guides) (ts:=[83,1000]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_24 : Block 333 8 next187 48 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_25 : Block 333 8 next187 50 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_26 : Block 333 8 next187 52 2 := block_off (db:=book123) (branches:=guides) (ts:=[81,1014]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_27 : Block 333 8 next187 54 2 := block_off (db:=book123) (branches:=guides) (ts:=[81,1030]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_28 : Block 333 8 next187 56 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,1230]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_29 : Block 333 8 next187 58 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block187_30 : Block 333 8 next187 60 2 := block_off (db:=book123) (branches:=guides) (ts:=[105,105]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof187 : Floor 333 spec187 := by
  apply floorEx _ (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=31) (width:=2) (vs:=next187) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact block187_0
  · exact block187_1
  · exact block187_2
  · exact block187_3
  · exact block187_4
  · exact block187_5
  · exact block187_6
  · exact block187_7
  · exact block187_8
  · exact block187_9
  · exact block187_10
  · exact block187_11
  · exact block187_12
  · exact block187_13
  · exact block187_14
  · exact block187_15
  · exact block187_16
  · exact block187_17
  · exact block187_18
  · exact block187_19
  · exact block187_20
  · exact block187_21
  · exact block187_22
  · exact block187_23
  · exact block187_24
  · exact block187_25
  · exact block187_26
  · exact block187_27
  · exact block187_28
  · exact block187_29
  · exact block187_30
def book187 (i : ℕ) : {s : FloorData // Floor 333 s} := if i<61 then book123 i else ⟨spec187,proof187⟩
def spec251 : FloorData := (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,12,[0x4008200040004022185088100a10e004000080410614108054107010180a404002839409a890a4c006020847000e010e0f30c780c380f01f80e00c1c1e3831e01c1fe01fc383c1fe0e007fffe0ffc01fff,0x1000209000200c0ca0809001a808c7840200601940802400194187822802a41ea024b090ca0323ac2803800307800700e0ff0c0f800fc00ffe00700f01fe1c03e001fe1ffe03c03fe0ff0007c01ff07ffff00,0x801875002100042001ca0011323c02005000aa4003ea801235a812101a280008c88e0002ad201231b01c00c3f8003800ff000ff0000ffff00007800ffe001ffc0001ffe00003ffc000fffff8001fff8001fff,0x4000c8000034ca000016d263c0010000834ca0000013349878000000457b54ac00048012331cc5c00c1e000fc00003fff00000ffffff000000007fff000001ffffffe00000003ffffff000000001ffffffe000,0x3f7ea0000146fadb5ad40000a000801420afad54b5a80000240000242064c673131370c7c00000600001ffff0000003ffffffff000000000000007ffffffffe000000000000003ffffffffffffffe0000000000,0x9a4d15624700000000000000000200000c9319f26324c12382632383800000000018002000000000101ffffffffffc00000000000000000000007fffffffffffffffffffffffc0000000000000000000000000,0x324b02084984931393181048c044c1183000000000000000000000000000000000020004000000000001fffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000])
def next251 := successors 333 10 spec251.basis
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_0 : Block 333 10 next251 0 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,62]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_1 : Block 333 10 next251 2 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,117]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_2 : Block 333 10 next251 4 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,91]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_3 : Block 333 10 next251 6 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,115]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_4 : Block 333 10 next251 8 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,98]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_5 : Block 333 10 next251 10 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,113]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_6 : Block 333 10 next251 12 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,109]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_7 : Block 333 10 next251 14 2 := block_off (db:=book187) (branches:=guides) (ts:=[119,111]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_8 : Block 333 10 next251 16 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_9 : Block 333 10 next251 18 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_10 : Block 333 10 next251 20 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_11 : Block 333 10 next251 22 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_12 : Block 333 10 next251 24 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,128]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_13 : Block 333 10 next251 26 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,115]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_14 : Block 333 10 next251 28 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,170]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_15 : Block 333 10 next251 30 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,113]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_16 : Block 333 10 next251 32 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,180]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_17 : Block 333 10 next251 34 2 := block_off (db:=book187) (branches:=guides) (ts:=[117,111]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_18 : Block 333 10 next251 36 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_19 : Block 333 10 next251 38 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_20 : Block 333 10 next251 40 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_21 : Block 333 10 next251 42 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_22 : Block 333 10 next251 44 2 := block_off (db:=book187) (branches:=guides) (ts:=[115,192]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_23 : Block 333 10 next251 46 2 := block_off (db:=book187) (branches:=guides) (ts:=[115,113]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_24 : Block 333 10 next251 48 2 := block_off (db:=book187) (branches:=guides) (ts:=[115,107]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_25 : Block 333 10 next251 50 2 := block_off (db:=book187) (branches:=guides) (ts:=[115,111]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_26 : Block 333 10 next251 52 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_27 : Block 333 10 next251 54 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_28 : Block 333 10 next251 56 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_29 : Block 333 10 next251 58 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_30 : Block 333 10 next251 60 2 := block_off (db:=book187) (branches:=guides) (ts:=[113,200]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_31 : Block 333 10 next251 62 2 := block_off (db:=book187) (branches:=guides) (ts:=[113,111]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_32 : Block 333 10 next251 64 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_33 : Block 333 10 next251 66 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_34 : Block 333 10 next251 68 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_35 : Block 333 10 next251 70 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_36 : Block 333 10 next251 72 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_37 : Block 333 10 next251 74 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_38 : Block 333 10 next251 76 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_39 : Block 333 10 next251 78 2 := block_off (db:=book187) (branches:=guides) (ts:=[123,123]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_40 : Block 333 10 next251 80 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_41 : Block 333 10 next251 82 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block251_42 : Block 333 10 next251 84 2 := block_off (db:=book187) (branches:=guides) (ts:=[121,121]) (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proof251 : Floor 333 spec251 := by
  apply floorEx _ (by decide +kernel) (by decide +kernel)
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (q:=43) (width:=2) (vs:=next251) (by decide) (by decide +kernel)
  intro j
  fin_cases j
  · exact block251_0
  · exact block251_1
  · exact block251_2
  · exact block251_3
  · exact block251_4
  · exact block251_5
  · exact block251_6
  · exact block251_7
  · exact block251_8
  · exact block251_9
  · exact block251_10
  · exact block251_11
  · exact block251_12
  · exact block251_13
  · exact block251_14
  · exact block251_15
  · exact block251_16
  · exact block251_17
  · exact block251_18
  · exact block251_19
  · exact block251_20
  · exact block251_21
  · exact block251_22
  · exact block251_23
  · exact block251_24
  · exact block251_25
  · exact block251_26
  · exact block251_27
  · exact block251_28
  · exact block251_29
  · exact block251_30
  · exact block251_31
  · exact block251_32
  · exact block251_33
  · exact block251_34
  · exact block251_35
  · exact block251_36
  · exact block251_37
  · exact block251_38
  · exact block251_39
  · exact block251_40
  · exact block251_41
  · exact block251_42
open PEqualNP.CircuitLowerBounds
theorem lower (C : Circuit) (fan : ∀ g∈C.gates, g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target (List.ofFn x)) : 13≤C.gates.countP counted := by
  by_contra small
  obtain ⟨k,lim,h⟩ := trace C fan result
  have ok : feasible 333 12 inputs := ⟨k,by omega,h,by decide +kernel⟩
  have no := floor_consistent (by decide) ok spec251 proof251 0
  have yes : contradictsFloor 333 12 inputs spec251 0=true := by decide +kernel
  exact Bool.noConfusion (yes.symm.trans no)
theorem solve (gates : List Gate) (o : ℕ)
    (legal : ∀ g∈gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (result : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x)=target (List.ofFn x)) :
    ∃ (v : List Gate) (p : ℕ), (∀ g∈v, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ v.length≤gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨v,p⟩ (List.ofFn x)=target (List.ofFn x) := by
  by_cases all : ∀ g∈gates, g.op=.and ∨ g.op=.or
  · exact ⟨gates,o,fun g h => ⟨all g h,(legal g h).2⟩,le_rfl,result⟩
  push Not at all
  obtain ⟨g,mem,na,no⟩ := all
  have nt : g.op=.not := ((legal g mem).1.resolve_left na).resolve_left no
  have lt : gates.countP counted < gates.length := List.countP_lt_length_iff.mpr ⟨g,mem,by simp [counted,nt]⟩
  have lb := lower ⟨gates,o⟩ (by intro v hv; simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal v hv) result
  change 13≤gates.countP counted at lb
  exact ⟨gs,21,basis,count ▸ (by omega : 14≤gates.length),computes⟩
end PEqualNP.Outside.L_meta_33282

theorem PEqualNP.Outside.L_meta_33282 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ result
  exact PEqualNP.Outside.L_meta_33282.solve gates o legal result
