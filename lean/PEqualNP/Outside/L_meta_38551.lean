import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38551.Support

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
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
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
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

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
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
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
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
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
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
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

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

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
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
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

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
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

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

end PEqualNP.Outside.L_meta_38551.Support

namespace PEqualNP.Outside.L_meta_38551.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_38551.Support

theorem viaPin {m h t : ℕ} {w v : List ℕ} {x : ℕ} (p : Projection m h) (wide : Wide h t v)
    (zero : p.toFun x=0)
    (ess : ∃ i : Fin m, ∀ b∈w, b.testBit i.val≠b.testBit (m+i.val) → b=x)
    (mem : ∀ y∈w, p.toFun y=0 ∨ p.toFun y∈v) : Wide m (t+1) w := by
  rintro ⟨k,S,le,live,sub⟩
  obtain ⟨i,hi⟩ := ess
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  have xs : x∈S := hi b (sub b hb) sep ▸ hb
  obtain ⟨j,T,cost,ok,incl⟩ := projectLive p live
  have one : 0 < (S.filter (fun y => p.toFun y=0)).card :=
    Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨xs,zero⟩⟩
  have cost' : j+(S.filter (fun y => p.toFun y=0)).card≤k := cost
  apply wide
  refine ⟨j,T,by omega,ok,?_⟩
  intro y hy
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (incl y hy)
  exact (mem u (sub u hu)).resolve_left (liveNonzero ok _ hy)

def Pinned (m t : ℕ) (w : List ℕ) (x : ℕ) : Prop :=
  ∃ (h : ℕ) (p : Projection m h) (v : List ℕ), p.toFun x=0 ∧ Wide h t v ∧ ∀ y∈w, p.toFun y=0 ∨ p.toFun y∈v
theorem pinned {m h t : ℕ} {w v : List ℕ} {x : ℕ} (p : Projection m h) (wide : Wide h t v)
    (zero : p.toFun x=0) (mem : ∀ y∈w, p.toFun y=0 ∨ p.toFun y∈v) : Pinned m t w x :=
  ⟨h,p,v,zero,wide,mem⟩

theorem viaFirst {m t : ℕ} {w : List ℕ} (single : terminal m w=false)
    (joined : ∀ a∈w, ∀ b∈w, a=b ∨ enough m (cover m ((a ||| b)::w.filter (fun x => x != a && x != b)))=false)
    (pins : ∀ x∈w, Pinned m t w x) : Wide m (t+2) w := by
  rintro ⟨k,S,le,live,sub⟩
  cases k with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rfl,hg,_⟩ := live
    exact absurd (single.symm.trans (ends hg w (sub a (Finset.mem_singleton_self a)))) Bool.false_ne_true
  | succ k =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rfl,hd,_,_,ab,_,tail⟩ := live
    have ma : a∈w := sub a (Finset.mem_insert_self _ _)
    have mb : b∈w := sub b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have mu : ∀ u∈U, u∈w := fun u hu => sub u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have key : ∀ x∈w, (x=a ∨ x=b) →
        (x∈U ∨ ∀ (h : ℕ) (p : Projection m h), p.toFun x=0 → p.toFun (combine d a b)=0) → False := by
      intro x mx hx gone
      obtain ⟨h,p,v,zero,wide,mem⟩ := pins x mx
      obtain ⟨j,T,cost,ok,incl⟩ := projectLive p tail
      have one : 0 < ((insert (combine d a b) U).filter (fun y => p.toFun y=0)).card := by
        rcases gone with kept|dies
        · exact Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem kept,zero⟩⟩
        · exact Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,dies h p zero⟩⟩
      have cost' : j+((insert (combine d a b) U).filter (fun y => p.toFun y=0)).card≤k := cost
      apply wide
      refine ⟨j,T,by omega,ok,?_⟩
      intro y hy
      have nz := liveNonzero ok y hy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (incl y hy)
      rcases Finset.mem_insert.mp hu with rfl|hu
      · have split := combine_eq_cases d (p.toFun a) (p.toFun b) hd
          (hx.elim (fun e => Or.inl (e ▸ zero)) (fun e => Or.inr (Or.inl (e ▸ zero))))
        rw [p.combineEq _ _ _ hd] at nz ⊢
        rcases split with e|e|e
        · exact (nz e).elim
        · rw [e] at nz ⊢; exact (mem a ma).resolve_left nz
        · rw [e] at nz ⊢; exact (mem b mb).resolve_left nz
      · exact (mem u (mu u hu)).resolve_left nz
    by_cases ka : a∈U
    · exact key a ma (Or.inl rfl) (Or.inl ka)
    by_cases kb : b∈U
    · exact key b mb (Or.inr rfl) (Or.inl kb)
    interval_cases d
    · exact key a ma (Or.inl rfl) (Or.inr (fun _ p z => by rw [p.combineEq _ _ _ (by decide),z]; simp [combine]))
    · have cov := enoughSup tail ((a ||| b)::w.filter (fun x => x != a && x != b)) (by
        intro y hy
        rcases Finset.mem_insert.mp hy with e|hu
        · rw [e]; simp [combine]
        · have ya : y≠a := fun e => ka (e ▸ hu)
          have yb : y≠b := fun e => kb (e ▸ hu)
          exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨mu y hu,by simp [ya,yb]⟩))
      rcases joined a ma b mb with e|e
      · exact ab e
      · exact absurd (e.symm.trans cov) Bool.false_ne_true
    · exact key a ma (Or.inl rfl) (Or.inr (fun _ p z => by rw [p.combineEq _ _ _ (by decide),z]; simp [combine]))
    · exact key b mb (Or.inr rfl) (Or.inr (fun _ p z => by rw [p.combineEq _ _ _ (by decide),z]; simp [combine]))

def target (x : Fin 6 → Bool) := Nat.testBit (4008373992 * 2 ^ 32 + 4008242376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def falsePoints : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,32,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,33,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,52,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60]
def truePoints : List ℕ := [3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63,3,6,7,10,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63]
def sample (points : List ℕ) (i : Fin 975) (j : Fin 6) := (points.getD i.val 0).testBit j.val
def inputs : List ℕ := [0x1242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a490922489492124491292424892257fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000001ffffffffffffffffffffffffffffffffffffffffffffffffc0000000007ffffffffffffffffffe0000000003fffffffff8000000000fffffffffffffffffffc0000000007fffffffff,0x36d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6ef800000000000000000000000000003fffffffff8000000000000000000000000000000000000007fffffffff0000000000000000000000000000000000000000000000001fffffffffc00000000000000000000000000000000000000000000000000000000000000000001fffffffffc0000000000000000000,0x38e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc7737fffffffff0000000001fffffffffc0000000000000000000fffffffffe0000000003fffffffff800000000000000000000000000003fffffffff8000000000fffffffffe00000000000000000000000000000fffffffffe00000000000000000007ffffffffffffffffffe00000000000000000000000000000,0x3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7ffffffffffffffffffe00000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000003fffffffffffffffffff000000000000000000000000000000000000000fffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000,0x3ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def seeds : List Wire := [(true,0x1242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a49092248949212449129242489225248491244a490922489492124491292424892257fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000001ffffffffffffffffffffffffffffffffffffffffffffffffc0000000007ffffffffffffffffffe0000000003fffffffff8000000000fffffffffffffffffffc0000000007fffffffff),(false,0x36d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6efedadb76ddfdb5b6edbbfb6b6ddb77f6d6dbb6ef800000000000000000000000000003fffffffff8000000000000000000000000000000000000007fffffffff0000000000000000000000000000000000000000000000001fffffffffc00000000000000000000000000000000000000000000000000000000000000000001fffffffffc0000000000000000000),(false,0x38e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc77371ce3b8ee6e39c771dcdc738ee3b9b8e71dc7737fffffffff0000000001fffffffffc0000000000000000000fffffffffe0000000003fffffffff800000000000000000000000000003fffffffff8000000000fffffffffe00000000000000000000000000000fffffffffe00000000000000000007ffffffffffffffffffe00000000000000000000000000000),(false,0x3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7e0fc3f0f8fc1f87e1f1f83f0fc3e3f07e1f87c7ffffffffffffffffffe00000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000003fffffffffffffffffff000000000000000000000000000000000000000fffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000),(false,0x3ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ff003ff00ffe007fe01ffc00ffc03ff801ff807ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000),(false,0x3ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffc0000fffff80001fffff00003ffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem listed : ∀ i : Fin 975, seeds.map (read i.val)=List.ofFn (sample falsePoints i) ∧
    seeds.map (read (975+i.val))=List.ofFn (sample truePoints i) := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem labels : ∀ i : Fin 975, target (sample falsePoints i)=false ∧ target (sample truePoints i)=true := by decide +kernel
theorem kept : reps seeds=inputs := by decide +kernel
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    Possible 975 (C.gates.countP counted) inputs := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 975 out.2 := by
    intro i hi same
    let j : Fin 975 := ⟨i,hi⟩
    have diff : read i out=read (975+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (975+i))
      rw [same]
    have p := ev i;have n := ev (975+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  exact ⟨k,S,limit,live,kept ▸ sub⟩

def w1 : List ℕ := [0x2aaad5bd555ab7aaab56f5556adeaaad5b8000000000000000000000000000000000,0x333366d6666cdacccd9b5999b36b33366d000000000000000000003ffffff8000000,0x3c3c78e7878f1cf0f1e39e1e3c73c3c78e00000000000001ffffffc0000000000000,0x3fc07f07f80fe0ff01fc1fe03f83fc07f00000000ffffffe00000000000000000000,0x3fff8007fff000fffe001fffc003fff8007ffffff000000000000000000000000000]
def w2 : List ℕ := [0x7ffffffffffffffffffc007ffffffffff800fffffc007ff001ffc007ff,0x2add5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadfff001ffc007ff001ffc00000ffe003ff800001ffc00000fffffc00000,0x336e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736fffffe000007ffffe00000000fffffc00000001ffffffff00000000000,0x3c778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc77ffffffffff80000000000000fffffffffffffe0000000000000000000,0x3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87ffffffffffffffffffffffff000000000000000000000000000000000]
def w3 : List ℕ := [0x2add5bab756ead800000003ff800,0x336e6dcdb9b736800001ffc00000,0x3c778ef1de3bc7000ffe00000000,0x3f87f0fe1fc3f87ff00000000000]
def w4 : List ℕ := [0x4222422242224222422242224222422242224222422242224222422242224222ffffffffffffffffffff0000ffffffffffff0000ffff0000ffffffff0000ffff,0xd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6efd6ef0000ffff00000000ffff000000000000ffff0000000000000000ffff00000000,0xe776e776e776e776e776e776e776e776e776e776e776e776e776e776e776e776ffff00000000ffff000000000000ffff000000000000ffffffff000000000000,0xf878f878f878f878f878f878f878f878f878f878f878f878f878f878f878f878ffffffffffff0000000000000000ffffffffffffffff00000000000000000000,0xff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ff80ffffffffffffffffffffffffffff000000000000000000000000000000000000]
def w16 : List ℕ := [0x49129244a49129244a49129244a49129244a49129244a49129244a49129244affffffffffffffffff00003ffffffffc0000ffffc0000fffffffff00003ffff,0xdb77f6ddfdb77f6ddfdb77f6ddfdb77f6ddfdb77f6ddfdb77f6ddfdb77f6ddf00000000000003ffff00000000000000000000000000000003ffff000000000,0xe3b9b8ee6e3b9b8ee6e3b9b8ee6e3b9b8ee6e3b9b8ee6e3b9b8ee6e3b9b8ee6ffffc0000ffffc0000000000000ffffc000000003ffffffffc0000000000000,0xfc3e3f0f8fc3e3f0f8fc3e3f0f8fc3e3f0f8fc3e3f0f8fc3e3f0f8fc3e3f0f8fffffffff000000000000000000fffffffffffffc0000000000000000000000,0xffc03ff00ffc03ff00ffc03ff00ffc03ff00ffc03ff00ffc03ff00ffc03ff00fffffffffffffffffffffffffff000000000000000000000000000000000000]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide3_6 : Wide 55 6 w3 :=
  viaSearch (by decide +kernel)
def p1_1 : Projection 135 55 :=
  pick [3,6,8,10,13,15,17,19,21,23,25,30,33,35,37,40,42,44,46,48,50,52,57,60,62,64,67,69,71,73,75,77,79,84,87,89,91,94,96,98,100,102,104,106,111,114,116,118,121,123,125,127,129,131,133] (by decide +kernel) (by decide +kernel) (by decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide1_7 : Wide 135 7 w1 :=
  viaPin (t := 6) (x := 0x2aaad5bd555ab7aaab56f5556adeaaad5b8000000000000000000000000000000000) p1_1 wide3_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p2_0 : Projection 231 55 :=
  pick [11,12,13,14,15,16,17,18,19,20,21,33,34,35,36,37,38,39,40,41,42,43,55,56,57,58,59,60,61,62,63,64,65,88,89,90,91,92,93,94,95,96,97,98,143,144,145,146,147,148,149,150,151,152,153] (by decide +kernel) (by decide +kernel) (by decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide2_7 : Wide 231 7 w2 :=
  viaPin (t := 6) (x := 0x7ffffffffffffffffffc007ffffffffff800fffffc007ff001ffc007ff) p2_0 wide3_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide4_7 : Wide 256 7 w4 :=
  viaSearch (by decide +kernel)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide16_7 : Wide 252 7 w16 :=
  viaSearch (by decide +kernel)
def p0_5 : Projection 975 252 :=
  pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524] (by decide +kernel) (by decide +kernel) (by decide)
def p0_4 : Projection 975 252 :=
  pick [0,1,2,3,4,5,6,7,18,19,20,21,22,23,24,25,26,27,39,40,41,42,43,44,45,46,57,58,59,60,61,62,63,64,65,66,78,79,80,81,82,83,84,85,96,97,98,99,100,101,102,103,104,105,117,118,119,120,121,122,123,124,135,136,137,138,139,140,141,142,143,144,156,157,158,159,160,161,162,163,174,175,176,177,178,179,180,181,182,183,195,196,197,198,199,200,201,202,213,214,215,216,217,218,219,220,221,222,234,235,236,237,238,239,240,241,252,253,254,255,256,257,258,259,260,261,273,274,275,276,277,278,279,280,291,292,293,294,295,296,297,298,299,300,546,547,548,549,550,551,552,553,564,565,566,567,568,569,570,571,572,573,585,586,587,588,589,590,591,592,603,604,605,606,607,608,609,610,611,612,624,625,626,627,628,629,630,631,642,643,644,645,646,647,648,649,650,651,663,664,665,666,667,668,669,670,681,682,683,684,685,686,687,688,689,690,702,703,704,705,706,707,708,709,720,721,722,723,724,725,726,727,728,729,741,742,743,744,745,746,747,748,759,760,761,762,763,764,765,766,767,768] (by decide +kernel) (by decide +kernel) (by decide)
def p0_3 : Projection 975 256 :=
  pick [0,1,2,8,9,10,11,18,19,20,21,28,29,30,31,32,39,40,41,47,48,49,50,57,58,59,60,67,68,69,70,71,78,79,80,86,87,88,89,96,97,98,99,106,107,108,109,110,117,118,119,125,126,127,128,135,136,137,138,145,146,147,148,149,156,157,158,164,165,166,167,174,175,176,177,184,185,186,187,188,312,313,314,320,321,322,323,330,331,332,333,340,341,342,343,344,351,352,353,359,360,361,362,369,370,371,372,379,380,381,382,383,390,391,392,398,399,400,401,408,409,410,411,418,419,420,421,422,429,430,431,437,438,439,440,447,448,449,450,457,458,459,460,461,546,547,548,554,555,556,557,564,565,566,567,574,575,576,577,578,585,586,587,593,594,595,596,603,604,605,606,613,614,615,616,617,624,625,626,632,633,634,635,642,643,644,645,652,653,654,655,656,663,664,665,671,672,673,674,681,682,683,684,691,692,693,694,695,780,781,782,788,789,790,791,798,799,800,801,808,809,810,811,812,819,820,821,827,828,829,830,837,838,839,840,847,848,849,850,851,858,859,860,866,867,868,869,876,877,878,879,886,887,888,889,890] (by decide +kernel) (by decide +kernel) (by decide)
def p0_2 : Projection 975 256 :=
  pick [0,3,4,8,12,13,14,18,22,23,24,28,29,33,34,35,39,42,43,47,51,52,53,57,61,62,63,67,68,72,73,74,78,81,82,86,90,91,92,96,100,101,102,106,107,111,112,113,195,198,199,203,207,208,209,213,217,218,219,223,224,228,229,230,234,237,238,242,246,247,248,252,256,257,258,262,263,267,268,269,312,315,316,320,324,325,326,330,334,335,336,340,341,345,346,347,351,354,355,359,363,364,365,369,373,374,375,379,380,384,385,386,390,393,394,398,402,403,404,408,412,413,414,418,419,423,424,425,468,471,472,476,480,481,482,486,490,491,492,496,497,501,502,503,546,549,550,554,558,559,560,564,568,569,570,574,575,579,580,581,585,588,589,593,597,598,599,603,607,608,609,613,614,618,619,620,624,627,628,632,636,637,638,642,646,647,648,652,653,657,658,659,702,705,706,710,714,715,716,720,724,725,726,730,731,735,736,737,780,783,784,788,792,793,794,798,802,803,804,808,809,813,814,815,819,822,823,827,831,832,833,837,841,842,843,847,848,852,853,854,897,900,901,905,909,910,911,915,919,920,921,925,926,930,931,932] (by decide +kernel) (by decide +kernel) (by decide)
def p0_1 : Projection 975 231 :=
  pick [5,9,12,15,19,22,25,28,30,33,36,44,48,51,54,58,61,64,67,69,72,75,122,126,129,132,136,139,142,145,147,150,153,161,165,168,171,175,178,181,184,186,189,192,200,204,207,210,214,217,220,223,225,228,231,239,243,246,249,253,256,259,262,264,267,270,278,282,285,288,292,295,298,301,303,306,309,317,321,324,327,331,334,337,340,342,345,348,356,360,363,366,370,373,376,379,381,384,387,434,438,441,444,448,451,454,457,459,462,465,473,477,480,483,487,490,493,496,498,501,504,512,516,519,522,526,529,532,535,537,540,543,551,555,558,561,565,568,571,574,576,579,582,590,594,597,600,604,607,610,613,615,618,621,668,672,675,678,682,685,688,691,693,696,699,707,711,714,717,721,724,727,730,732,735,738,746,750,753,756,760,763,766,769,771,774,777,785,789,792,795,799,802,805,808,810,813,816,863,867,870,873,877,880,883,886,888,891,894,902,906,909,912,916,919,922,925,927,930,933,941,945,948,951,955,958,961,964,966,969,972] (by decide +kernel) (by decide +kernel) (by decide)
def p0_0 : Projection 975 135 :=
  pick [39,41,43,44,46,47,48,50,51,53,54,56,57,58,60,61,63,64,66,67,68,69,71,72,74,75,77,156,158,160,161,163,164,165,167,168,170,171,173,174,175,177,178,180,181,183,184,185,186,188,189,191,192,194,234,236,238,239,241,242,243,245,246,248,249,251,252,253,255,256,258,259,261,262,263,264,266,267,269,270,272,351,353,355,356,358,359,360,362,363,365,366,368,369,370,372,373,375,376,378,379,380,381,383,384,386,387,389,585,587,589,590,592,593,594,596,597,599,600,602,603,604,606,607,609,610,612,613,614,615,617,618,620,621,623] (by decide +kernel) (by decide +kernel) (by decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wide0_9 : Wide 975 9 inputs :=
  viaFirst (t := 7) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.mpr ⟨pinned p0_0 wide1_7 (by decide +kernel) (by decide +kernel),
    List.forall_mem_cons.mpr ⟨pinned p0_1 wide2_7 (by decide +kernel) (by decide +kernel),
    List.forall_mem_cons.mpr ⟨pinned p0_2 wide4_7 (by decide +kernel) (by decide +kernel),
    List.forall_mem_cons.mpr ⟨pinned p0_3 wide4_7 (by decide +kernel) (by decide +kernel),
    List.forall_mem_cons.mpr ⟨pinned p0_4 wide16_7 (by decide +kernel) (by decide +kernel),
    List.forall_mem_cons.mpr ⟨pinned p0_5 wide16_7 (by decide +kernel) (by decide +kernel),
    fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩)
def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [12, 0]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [15, 11]⟩], 16⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
theorem binary_floor {C : Circuit} (fan : FanInTwo C) (d : ∀ x, C.eval (List.ofFn x) = target x) :
    10 ≤ C.gates.countP counted := by
  obtain ⟨k,S,le,live,sub⟩ := trace C fan (funext d)
  by_contra! low
  exact wide0_9 ⟨k,S,by omega,live,sub⟩
theorem mono_enough : ∀ s, HasCircuitSize 6 target s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x)=target x := by
  rintro s ⟨C,fan,sz,correct⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g,hg,hop⟩ := hn
    have low := binary_floor fan correct
    have lt : C.gates.countP counted < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro equal
      have is := List.countP_eq_length.mp equal g hg
      simp [counted,hop] at is
    refine ⟨witness,wmono,?_,wcomputes⟩
    change C.gates.length ≤ s at sz
    change 11 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_38551.Data

theorem PEqualNP.Outside.L_meta_38551 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008242376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008242376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_38551.Data.mono_enough
