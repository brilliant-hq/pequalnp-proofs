import PEqualNP.Defs

/-! A five-input support and a single negation force a read-once cone. Six
coordinate witnesses rule out every choice of signs on a support of size five.
For the monotone case, ten positive-direction witnesses force all ten inputs. -/

namespace PEqualNP.Outside.L_meta_19331

namespace FiveGateCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- AND/OR cost one unit of branching. Negation costs none. -/
def branching (g : Gate) : Bool := match g.op with | .not => false | _ => true

def operands (g : Gate) := if branching g then g.inputs else g.inputs.take 1

/-- Input positions that are both valid and absent from the rest of the required wires. -/
def fresh (n : ℕ) (g : Gate) (W : Finset ℕ) :=
  (operands g).filter fun a => decide (a<n ∧ a∉W.erase n)

def step (n : ℕ) (g : Gate) (W : Finset ℕ) : Finset ℕ :=
  if n∈W then W.erase n ∪ (fresh n g W).toFinset else W

/-- Scan from the output towards the inputs, retaining exactly the wires still needed. -/
def back (n : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], W => W
  | g::gs, W => step n g (back (n+1) gs W)

def costs (gs : List Gate) := gs.countP branching
def negs (gs : List Gate) := gs.countP (fun g=> !branching g)

def Law (n : ℕ) (g : Gate) (W : Finset ℕ) : Prop :=
  if n∈W then
    (operands g).length = 1+(branching g).toNat ∧
    (operands g).Nodup ∧ ∀ a∈operands g, a<n ∧ a∉W.erase n
  else branching g=false

/-- Every required gate introduces fresh, distinct earlier wires. Only a negation may be skipped. -/
def Tree (n : ℕ) : List Gate → Finset ℕ → Prop
  | [], _ => True
  | g::gs, W => Law n g (back (n+1) gs W) ∧ Tree (n+1) gs W

private theorem maxOps (g : Gate) (fan : g.inputs.length≤2) :
    (operands g).length≤1+(branching g).toNat := by
  cases h : branching g <;> simp [operands,h,fan]

private theorem stepCount (n : ℕ) (g : Gate) (W : Finset ℕ) (mem : n∈W) :
    (step n g W).card + 1 = W.card + (fresh n g W).toFinset.card := by
  have dis : Disjoint (W.erase n) (fresh n g W).toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx h
    have hf : x∈fresh n g W := List.mem_toFinset.mp h
    have := (List.mem_filter.mp hf).2
    simpa [hx] using this
  simp only [step,if_pos mem,Finset.card_union_of_disjoint dis,Finset.card_erase_of_mem mem]
  have := Finset.card_pos.mpr ⟨_,mem⟩
  omega

private theorem stepBound (n : ℕ) (g : Gate) (W : Finset ℕ) (fan : g.inputs.length≤2) :
    (step n g W).card ≤ W.card + (branching g).toNat := by
  by_cases mem : n∈W
  · have h₁ := stepCount n g W mem
    have h₂ := List.toFinset_card_le (fresh n g W)
    have h₃ : (fresh n g W).length≤(operands g).length := List.length_filter_le _ _
    have h₄ := maxOps g fan
    omega
  · simp [step,mem]

private theorem lawMax (n : ℕ) (g : Gate) (W : Finset ℕ) (fan : g.inputs.length≤2)
    (maxi : (step n g W).card = W.card + (branching g).toNat) : Law n g W := by
  by_cases mem : n∈W
  · rw [Law, if_pos mem]
    have h₁ := stepCount n g W mem
    have h₂ := List.toFinset_card_le (fresh n g W)
    have h₃ : (fresh n g W).length≤(operands g).length := List.length_filter_le _ _
    have h₄ := maxOps g fan
    have eqLen : (fresh n g W).length=(operands g).length := by omega
    have allFresh : ∀ a∈operands g, a<n ∧ a∉W.erase n := by
      simpa only [decide_eq_true_eq] using List.length_filter_eq_length_iff.mp eqLen
    have eqList : fresh n g W=operands g := List.filter_eq_self.mpr (fun a ha=>decide_eq_true (allFresh a ha))
    have nd : (fresh n g W).toFinset.card = (fresh n g W).length := by omega
    have hnd : (fresh n g W).Nodup :=
      (Multiset.toFinset_card_eq_card_iff_nodup (m:=((fresh n g W) : Multiset ℕ))).mp nd
    exact ⟨by omega, eqList ▸ hnd, allFresh⟩
  · have := maxi
    cases b : branching g <;> simp_all [Law,step]

theorem bound (n : ℕ) (gs : List Gate) (W : Finset ℕ)
    (fan : ∀ g∈gs,g.inputs.length≤2) : (back n gs W).card ≤ W.card + costs gs := by
  induction gs generalizing n with
  | nil => simp [back,costs]
  | cons g gs ih =>
    have a:=stepBound n g (back (n+1) gs W) (fan g List.mem_cons_self)
    have b:=ih (n+1) (fun g hg=>fan g (List.mem_cons_of_mem _ hg))
    have cost : costs (g::gs) = costs gs + (branching g).toNat := by
      cases h : branching g <;> simp [costs,h]
    rw [back,cost]
    omega

theorem treeAtMaximum (n : ℕ) (gs : List Gate) (W : Finset ℕ)
    (fan : ∀ g∈gs,g.inputs.length≤2) (sat : (back n gs W).card = W.card + costs gs) :
    Tree n gs W := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    have htail := fun g hg=>fan g (List.mem_cons_of_mem _ hg)
    have a:=stepBound n g (back (n+1) gs W) (fan g List.mem_cons_self)
    have b:=bound (n+1) gs W htail
    have cost : costs (g::gs) = costs gs + (branching g).toNat := by
      cases h : branching g <;> simp [costs,List.countP_cons,h]
    simp only [back,cost] at sat
    exact ⟨lawMax n g _ (fan g List.mem_cons_self) (by omega), ih (n+1) htail (by omega)⟩

theorem counts (gs : List Gate) : costs gs + negs gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : branching g <;> simp_all [costs,negs,List.countP_cons] <;> omega

/-- The five-input conclusion includes the case where the physical negation is unused. -/
theorem five {n : ℕ} (C : Circuit) (hC : FanInTwo C) (small : C.size≤5)
    (hn : 0<negs C.gates) (hs : 5≤(back n C.gates {C.output}).card) :
    C.size=5 ∧ costs C.gates=4 ∧ negs C.gates=1 ∧
    (back n C.gates {C.output}).card=5 ∧ Tree n C.gates {C.output} := by
  have hfan := fun g hg=>(hC g hg).2
  have total := counts C.gates
  have hbound := bound n C.gates {C.output} hfan
  simp only [Finset.card_singleton] at hbound
  change C.gates.length≤5 at small
  refine ⟨by change C.gates.length=5; omega,by omega,by omega,by omega,treeAtMaximum _ _ _ hfan ?_⟩
  simp only [Finset.card_singleton]
  omega

end FiveGateCone


namespace FiveGateCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i=>w.getD i false)

private theorem depends (g : Gate) (x y : List Bool)
    (h : ∀ a∈operands g,x.getD a false=y.getD a false) : value g x=value g y := by
  obtain ⟨op,ins⟩ := g
  cases op
  case not =>
    cases ins with
    | nil => rfl
    | cons a as =>
      have eq := h a (by simp [operands,branching])
      simpa [value,GateOp.eval] using eq
  all_goals
    unfold value
    congr 1
    apply List.map_congr_left
    exact fun a ha=>h a (by simpa [operands,branching] using ha)

private def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun x g=>x++[value g x]) w

private theorem earlier (x : List Bool) (b : Bool) (j : ℕ) (hj : j≠x.length) :
    (x++[b]).getD j false=x.getD j false := by
  by_cases lt : j<x.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private theorem stage (g : Gate) {n} (W : Finset ℕ) (x y : List Bool)
    (lx : x.length=n) (ly : y.length=n)
    (h : ∀ i∈step n g W,x.getD i false=y.getD i false) :
    ∀ j∈W,(x++[value g x]).getD j false=(y++[value g y]).getD j false := by
  intro j hj
  by_cases same : j=n
  · subst j
    have ex : (x++[value g x]).getD n false=value g x := by rw [← lx]; simp
    have ey : (y++[value g y]).getD n false=value g y := by rw [← ly]; simp
    rw [ex,ey]
    apply depends
    intro a ha
    by_cases valid : a<n
    · apply h
      rw [step,if_pos hj]
      by_cases old : a∈W.erase n
      · exact Finset.mem_union_left _ old
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_filter.mpr
          ⟨ha,decide_eq_true ⟨valid,old⟩⟩))
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
  · rw [earlier _ _ _ (by omega),earlier _ _ _ (by omega)]
    apply h
    rw [step]
    split
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,hj⟩)
    · exact hj

theorem agree {n : ℕ} (gs : List Gate) (W : Finset ℕ) (x y : List Bool)
    (lx : x.length=n) (ly : y.length=n)
    (h : ∀ i∈back n gs W,x.getD i false=y.getD i false) :
    ∀ j∈W,(run gs x).getD j false=(run gs y).getD j false := by
  induction gs generalizing n x y with
  | nil => exact h
  | cons g gs ih =>
    apply ih (n:=n+1) (x++[value g x]) (y++[value g y]) (by simp [lx]) (by simp [ly])
    exact stage g _ _ _ lx ly h

/-- A promise can use any family of input strings of one fixed length. -/
def Supports {α : Type} (rows : α→List Bool) (f : α→Bool) (S : Finset ℕ) :=
  ∀ a b, (∀ j∈S,(rows a).getD j false = (rows b).getD j false) → f a=f b

theorem supports {α : Type} (C : Circuit) (n : ℕ) (rows : α→List Bool)
    (len : ∀a,(rows a).length=n) (f : α→Bool) (eval : ∀a,C.eval (rows a)=f a) :
    Supports rows f (back n C.gates {C.output}) := by
  intro a b h
  rw [← eval a,← eval b]
  exact agree C.gates {C.output} _ _ (len a) (len b) h C.output (by simp)

theorem fiveOfPromise {α : Type} (C : Circuit) (n : ℕ) (rows : α→List Bool)
    (len : ∀a,(rows a).length=n) (f : α→Bool) (eval : ∀a,C.eval (rows a)=f a)
    (necessary : ∀S, Supports rows f S → 5≤S.card)
    (ok : FanInTwo C) (small : C.size≤5) (hn : 0<negs C.gates) :
    C.size=5 ∧ costs C.gates=4 ∧ negs C.gates=1 ∧
    (back n C.gates {C.output}).card=5 ∧ Tree n C.gates {C.output} :=
  five C ok small hn (necessary _ (supports C n rows len f eval))

end FiveGateCone


namespace FiveGateCone.Promised
open PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev V := Fin 5
def rows (r : V×V) := oneEach r.1 r.2
def matrix (m : ℕ) (u v : V) := m.testBit (5*u.val+v.val)

private theorem access (u v : V) (j : ℕ) : (oneEach u v).getD j false =
    decide (j=u.val ∨ j=5+v.val) := by
  have table : ∀ (u v : V) (i : Fin 10), (oneEach u v).getD i.val false =
      decide (i.val=u.val ∨ i.val=5+v.val) := by decide +kernel
  by_cases hj : j<10
  · exact table u v ⟨j,hj⟩
  · have hu:=u.isLt
    have hv:=v.isLt
    rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
    simp [show j≠u.val by omega,show j≠5+v.val by omega]

private def side (m : ℕ) (col : Bool) (A : Finset V) :=
  ∀ a∉A,∀ b∉A, ∀ t : V, (if col then matrix m t a else matrix m a t) =
    (if col then matrix m t b else matrix m b t)

private instance {m col A} : Decidable (side m col A) := by unfold side; infer_instance

private def lower (m : ℕ) (col : Bool) (k : ℕ) :=
  ∀ A : Finset V, side m col A → k≤A.card

private instance {m col k} : Decidable (lower m col k) := by unfold lower; infer_instance

private theorem addBounds {m i j : ℕ} (hL : lower m false i) (hR : lower m true j)
    (S : Finset ℕ) (h : Supports rows (fun r=>matrix m r.1 r.2) S) : i+j≤S.card := by
  let A := Finset.univ.filter (fun a : V=>a.val∈S)
  let B := Finset.univ.filter (fun a : V=>5+a.val∈S)
  have left : side m false A := by
    intro a ha b hb t
    have ha' : a.val∉S := by simpa [A] using ha
    have hb' : b.val∉S := by simpa [A] using hb
    apply h (a,t) (b,t)
    intro k hk
    have ka : k≠a.val := fun e=>ha' (e ▸ hk)
    have kb : k≠b.val := fun e=>hb' (e ▸ hk)
    simp only [rows,access,ka,kb,false_or,or_false]
  have right : side m true B := by
    intro a ha b hb t
    have ha' : 5+a.val∉S := by simpa [B] using ha
    have hb' : 5+b.val∉S := by simpa [B] using hb
    apply h (t,a) (t,b)
    intro k hk
    have ka : k≠5+a.val := fun e=>ha' (e ▸ hk)
    have kb : k≠5+b.val := fun e=>hb' (e ▸ hk)
    simp only [rows,access,ka,kb,false_or,or_false]
  let T := A.image Fin.val
  let U := B.image (fun a=>5+a.val)
  have dis : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    rintro x hT hU
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hU
    have := a.isLt
    omega
  have sub : T ∪ U ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with h|h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
  have cT : T.card=A.card := Finset.card_image_of_injective _ Fin.val_injective
  have cU : U.card=B.card := Finset.card_image_of_injective _ (by intro a b h; exact Fin.ext (Nat.add_left_cancel (show 5+a.val=5+b.val from h)))
  have count := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis,cT,cU] at count
  exact (Nat.add_le_add (hL _ left) (hR _ right)).trans count

def bounds : List (ℕ×ℕ×ℕ) := [
  (16236156,2,3)]

private def passes (e : ℕ×ℕ×ℕ) : Bool :=
  decide (lower e.1 false e.2.1 ∧ lower e.1 true e.2.2)

private theorem checked : bounds.all passes=true := by decide +kernel

theorem rawNeeded {m i j : ℕ} (mem : (m,i,j)∈bounds) (S : Finset ℕ)
    (h : Supports rows (fun r=>matrix m r.1 r.2) S) : i+j≤S.card := by
  obtain ⟨hL,hR⟩ := of_decide_eq_true (List.all_eq_true.mp checked _ mem)
  exact addBounds hL hR _ h

theorem namedFive {m i j : ℕ} (mem : (m,i,j)∈bounds) (need : 5 ≤ i + j)
    (C : Circuit) (ok : FanInTwo C) (small : C.size≤5) (hn : 0<negs C.gates)
    (rep : Represents (matrix m) C) :
    C.size=5 ∧ costs C.gates=4 ∧ negs C.gates=1 ∧
    (back 10 C.gates {C.output}).card=5 ∧ Tree 10 C.gates {C.output} :=
  fiveOfPromise C 10 rows (fun a=>by simp [rows,oneEach])
    (fun r=>matrix m r.1 r.2) (fun r=>rep r.1 r.2)
    (fun S h=>need.trans (rawNeeded mem S h)) ok small hn

end FiveGateCone.Promised


namespace FiveGateCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- In a positive coordinate true can only be gained, in a negative coordinate it can only be lost. -/
def LeSign (p x y : Bool) : Prop :=
  if p then (x=true → y=true) else (y=true → x=true)

private def gate (g : Gate) (x : List Bool) := g.op.eval (g.inputs.map fun i=>x.getD i false)
private def run' (gs : List Gate) (x : List Bool) := gs.foldl (fun w g=>w++[gate g w]) x

private def Legal (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)

private theorem gateSign (g : Gate) (legal : Legal g) (p : Bool) (x y : List Bool)
    (h : ∀ a∈operands g, LeSign (if branching g then p else !p) (x.getD a false) (y.getD a false)) :
    LeSign p (gate g x) (gate g y) := by
  obtain ⟨op,l⟩ := g
  cases op with
  | and =>
    cases p <;> simp only [branching,ite_true,operands,LeSign,Bool.false_eq_true,ite_false,
      gate,GateOp.eval,List.all_eq_true,List.mem_map] at *
    all_goals
      intro hx a ha
      obtain ⟨b,hb,rfl⟩ := ha
      exact h b hb (hx _ ⟨_,hb,rfl⟩)
  | or =>
    cases p <;> simp only [branching,ite_true,operands,LeSign,Bool.false_eq_true,ite_false,
      gate,GateOp.eval,List.any_eq_true,List.mem_map] at *
    all_goals
      rintro ⟨a,⟨b,hb,rfl⟩,hv⟩
      exact ⟨_,⟨_,hb,rfl⟩,h b hb hv⟩
  | not =>
    cases l with
    | nil => cases p <;> simp [LeSign,gate]
    | cons a l =>
      have hk:=h a (by simp [operands,branching])
      change LeSign (!p) (x.getD a false) (y.getD a false) at hk
      change LeSign p (!(x.getD a false)) (!(y.getD a false))
      generalize x.getD a false=bx at hk ⊢
      generalize y.getD a false=byy at hk ⊢
      cases p <;> cases bx <;> cases byy <;> simp_all [LeSign]
  | mod m => simp [Legal] at legal
  | maj => simp [Legal] at legal

def Signed (W : Finset ℕ) (orientation : ℕ→Bool) (x y : List Bool) :=
  ∀ a∈W,LeSign (orientation a) (x.getD a false) (y.getD a false)

private theorem oldValue (x : List Bool) (b : Bool) (j : ℕ) (hj : j≠x.length) :
    (x++[b]).getD j false=x.getD j false := by
  by_cases lt : j<x.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private theorem moveSign (n : ℕ) (g : Gate) (W : Finset ℕ) (p : ℕ→Bool)
    (legal : Legal g) (tree : Law n g W) :
    ∃ q : ℕ→Bool, ∀ x y : List Bool, x.length=n → y.length=n →
    Signed (step n g W) q x y → Signed W p (x++[gate g x]) (y++[gate g y]) := by
  let sign := if branching g then p n else !p n
  let q (i : ℕ) := if i∈W.erase n then p i else sign
  refine ⟨q,?_⟩
  intro x y lx ly h a ha
  by_cases curr : a=n
  · subst a
    have law := (show _ ∧ _ ∧ _ from (by simpa only [Law, if_pos ha] using tree))
    have ex : (x++[gate g x]).getD n false=gate g x := by rw [← lx]; simp
    have ey : (y++[gate g y]).getD n false=gate g y := by rw [← ly]; simp
    rw [ex,ey]
    apply gateSign g legal (p n)
    intro i hi
    obtain ⟨valid,newWire⟩ := law.2.2 i hi
    have member : i ∈ step n g W := by
      rw [step, if_pos ha]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨hi,decide_eq_true ⟨valid,newWire⟩⟩))
    simpa only [q,if_neg newWire,sign] using h i member
  · rw [oldValue _ _ _ (by omega),oldValue _ _ _ (by omega)]
    have mem : a∈W.erase n := Finset.mem_erase.mpr ⟨curr,ha⟩
    have old : a∈step n g W := by rw [step]; split <;> first | exact Finset.mem_union_left _ mem | exact ha
    simpa only [q,if_pos mem] using h a old

private theorem pushSign (n : ℕ) (gs : List Gate) (W : Finset ℕ) (p : ℕ→Bool)
    (ok : ∀g∈gs,Legal g) (tree : Tree n gs W) :
    ∃ q : ℕ→Bool, ∀ x y : List Bool, x.length=n → y.length=n →
    Signed (back n gs W) q x y → Signed W p (run' gs x) (run' gs y) := by
  induction gs generalizing n with
  | nil => exact ⟨p,fun _ _ _ _ h=>h⟩
  | cons g gs ih =>
    obtain ⟨mid,hmid⟩ := ih (n+1) (fun g h=>ok g (List.mem_cons_of_mem _ h)) tree.2
    obtain ⟨q,hq⟩ := moveSign n g (back (n+1) gs W) mid (ok _ List.mem_cons_self) tree.1
    refine ⟨q,fun x y lx ly h=>?_⟩
    exact hmid _ _ (by simp [lx]) (by simp [ly]) (hq _ _ lx ly h)

theorem unate (n : ℕ) (C : Circuit) (ok : FanInTwo C) (tree : Tree n C.gates {C.output}) :
    ∃ q : ℕ→Bool, ∀ x y : List Bool, x.length=n → y.length=n →
    Signed (back n C.gates {C.output}) q x y → C.eval x=true → C.eval y=true := by
  obtain ⟨q,hq⟩ := pushSign n C.gates {C.output} (fun _=>true) (fun g hg=>(ok g hg).1) tree
  exact ⟨q,fun x y lx ly h=>hq x y lx ly h C.output (by simp)⟩

private theorem gatePositive (n : ℕ) (g : Gate) (W : Finset ℕ)
    (legal : Legal g) (noNot : branching g=true) (x y : List Bool) (lx : x.length=n) (ly : y.length=n)
    (h : Signed (step n g W) (fun _=>true) x y) :
    Signed W (fun _=>true) (x++[gate g x]) (y++[gate g y]) := by
  intro a ha
  by_cases curr : a=n
  · subst a
    have ex : (x++[gate g x]).getD n false=gate g x := by rw [← lx]; simp
    have ey : (y++[gate g y]).getD n false=gate g y := by rw [← ly]; simp
    rw [ex,ey]
    apply gateSign _ legal true
    rw [noNot]
    change ∀ a∈operands g, LeSign true (x.getD a false) (y.getD a false)
    intro i hi
    by_cases valid : i<n
    · have mem : i∈step n g W := by
        rw [step,if_pos ha]
        by_cases old : i∈W.erase n
        · exact Finset.mem_union_left _ old
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_filter.mpr
            ⟨hi,decide_eq_true ⟨valid,old⟩⟩))
      exact h i mem
    · rw [List.getD_eq_default x false (by omega),List.getD_eq_default y false (by omega)]
      simp [LeSign]
  · rw [oldValue _ _ _ (by omega),oldValue _ _ _ (by omega)]
    apply h
    rw [step]
    split
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨curr,ha⟩)
    · exact ha

private theorem pushPositive (n : ℕ) (gs : List Gate) (W : Finset ℕ)
    (ok : ∀g∈gs, Legal g ∧ branching g=true) (x y : List Bool)
    (lx : x.length=n) (ly : y.length=n) (h : Signed (back n gs W) (fun _=>true) x y) :
    Signed W (fun _=>true) (run' gs x) (run' gs y) := by
  induction gs generalizing n x y with
  | nil => exact h
  | cons g gs ih =>
    have both:=ok g List.mem_cons_self
    apply ih (n+1) (fun g hg=>ok g (List.mem_cons_of_mem _ hg)) _ _ (by simp [lx]) (by simp [ly])
    exact gatePositive n g _ both.1 both.2 x y lx ly h

theorem positive (n : ℕ) (C : Circuit) (ok : FanInTwo C) (none : negs C.gates=0)
    (x y : List Bool) (lx : x.length=n) (ly : y.length=n)
    (h : Signed (back n C.gates {C.output}) (fun _=>true) x y) : C.eval x=true → C.eval y=true := by
  have hg (g : Gate) (mem : g∈C.gates) : branching g=true := by
    have zero:=List.countP_eq_zero.mp none g mem
    simpa using zero
  exact pushPositive n C.gates {C.output} (fun g mem=>⟨(ok g mem).1,hg g mem⟩)
    x y lx ly h C.output (by simp)

end FiveGateCone


namespace FiveGateCone.Binate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Promised

abbrev Row := Fin 5 × Fin 5

/-- On omitting one signal, either orientation of the pivot gives a violating pair. -/
structure Witness where
  omitted : Fin 10
  pivot : Fin 10
  positiveFrom : Row
  positiveTo : Row
  negativeFrom : Row
  negativeTo : Row

def Witness.src (w : Witness) (b : Bool) := if b then w.positiveFrom else w.negativeFrom
def Witness.dst (w : Witness) (b : Bool) := if b then w.positiveTo else w.negativeTo

def Test (m : ℕ) (w : Witness) := ∀ b : Bool,
  matrix m (w.src b).1 (w.src b).2=true ∧ matrix m (w.dst b).1 (w.dst b).2=false ∧
  ∀ i : Fin 10, i≠w.omitted →
    if i=w.pivot then LeSign b ((rows (w.src b)).getD i.val false) ((rows (w.dst b)).getD i.val false)
    else (rows (w.src b)).getD i.val false=(rows (w.dst b)).getD i.val false

instance {p x y} : Decidable (LeSign p x y) := by unfold LeSign; infer_instance
instance (m : ℕ) (w : Witness) : Decidable (Test m w) := by unfold Test; infer_instance

private theorem selfSign (b v : Bool) : LeSign b v v := by cases b <;> simp [LeSign]

def Compatible (s : Finset ℕ) (q : ℕ→Bool) (m : ℕ) :=
  ∀ a b : Row, Signed s q (rows a) (rows b) → matrix m a.1 a.2=true → matrix m b.1 b.2=true

theorem mustRead {m : ℕ} {s : Finset ℕ} {q : ℕ→Bool} (ok : Compatible s q m)
    (w : Witness) (test : Test m w) : w.omitted.val∈s := by
  by_contra absent
  let b := q w.pivot.val
  obtain ⟨yes,no,atCoord⟩ := test b
  have pair : Signed s q (rows (w.src b)) (rows (w.dst b)) := by
    intro j hj
    by_cases h : j<10
    · let i : Fin 10 := ⟨j,h⟩
      have ne : i≠w.omitted := by intro eq; exact absent (congrArg Fin.val eq ▸ hj)
      have chk := atCoord i ne
      by_cases piv : i=w.pivot
      · rw [if_pos piv] at chk
        have eq : j=w.pivot.val := congrArg Fin.val piv
        simpa only [b,← eq] using chk
      · rw [if_neg piv] at chk
        change (rows (w.src b)).getD j false=(rows (w.dst b)).getD j false at chk
        rw [chk]
        exact selfSign _ _
    · have len (a : Row) : (rows a).length=10 := by simp [rows,oneEach]
      have z (a : Row) : (rows a).getD j false=false := List.getD_eq_default _ _ (by rw [len];omega)
      rw [z,z]
      exact selfSign _ _
  have ans := ok _ _ pair yes
  simp [no] at ans

structure Book where
  mask : ℕ
  tests : List Witness

def Book.checked (d : Book) := d.tests.all (fun w=>decide (Test d.mask w)) &&
  decide (6≤(d.tests.map (fun w=>w.omitted.val)).toFinset.card)

def books : List Book := [
  ⟨16236156,[⟨7,5,(0,2),(0,0),(1,0),(1,2)⟩,⟨0,1,(0,2),(1,2),(1,0),(0,0)⟩,⟨8,5,(0,3),(0,0),(1,0),(1,3)⟩,⟨9,5,(0,4),(0,0),(2,0),(2,4)⟩,⟨1,0,(1,0),(0,0),(0,2),(1,2)⟩,⟨5,7,(1,0),(1,2),(0,2),(0,0)⟩]⟩]

private theorem checked : books.all Book.checked=true := by decide +kernel

theorem needsSix {m : ℕ} (h : m ∈ books.map Book.mask) (s : Finset ℕ) (q : ℕ→Bool)
    (hyp : Compatible s q m) : 6≤s.card := by
  obtain ⟨d,mem,rfl⟩ := List.mem_map.mp h
  obtain ⟨yes,size⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked _ mem)
  have sub : (d.tests.map (fun w=>w.omitted.val)).toFinset ⊆ s := by
    intro i hi
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    exact mustRead hyp w (of_decide_eq_true (List.all_eq_true.mp yes _ hw))
  exact (of_decide_eq_true size).trans (Finset.card_le_card sub)

private theorem look : books.all (fun d=>bounds.any fun e=>decide (e.1=d.mask ∧ 5 ≤ e.2.1+e.2.2))=true := by
  decide +kernel

theorem noNegationCircuit {m : ℕ} (mem : m ∈ books.map Book.mask) (C : Circuit)
    (ok : FanInTwo C) (small : C.size≤5) (hn : 0<negs C.gates) : ¬Represents (matrix m) C := by
  intro rep
  have orig:=mem
  obtain ⟨d,hm,rfl⟩ := List.mem_map.mp mem
  obtain ⟨e,he,good⟩ := List.any_eq_true.mp (List.all_eq_true.mp look _ hm)
  obtain ⟨eq,big⟩ := of_decide_eq_true good
  have eqmem : (d.mask,e.2.1,e.2.2)∈bounds := eq ▸ he
  obtain ⟨_,_,_,card,tree⟩ := namedFive eqmem big C ok small hn rep
  obtain ⟨q,hq⟩ := unate 10 C ok tree
  have lim := needsSix orig (back 10 C.gates {C.output}) q (by
    intro x y order yes
    have eval (t : Row) : C.eval (rows t)=matrix d.mask t.1 t.2 := rep t.1 t.2
    apply (eval y).symm.trans
    apply hq _ _ (by simp [rows,oneEach]) (by simp [rows,oneEach]) order
    exact (eval x).trans yes)
  omega

end FiveGateCone.Binate


namespace FiveGateCone.Positive
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Promised Binate

def flags (m : ℕ) (i : Fin 10) (x y : Row) : Prop :=
  matrix m x.1 x.2=true ∧ matrix m y.1 y.2=false ∧
    ∀ j : Fin 10, j≠i → LeSign true ((rows x).getD j.val false) ((rows y).getD j.val false)

instance {m i x y} : Decidable (flags m i x y) := by unfold flags; infer_instance

structure Pattern where
  m : ℕ
  witness : Fin 10 → Row × Row

def patterns : List Pattern := [
  ⟨16236156,![((0,2),(1,2)),((1,0),(0,0)),((2,0),(0,0)),((3,0),(0,0)),((4,0),(0,0)),((1,0),(1,2)),((1,1),(1,2)),((0,2),(0,0)),((0,3),(0,0)),((0,4),(0,0))]⟩]

private def valid (p : Pattern) := ∀ i, flags p.m i (p.witness i).1 (p.witness i).2
private instance {p} : Decidable (valid p) := by unfold valid; infer_instance
private theorem checked : patterns.all (fun p=>decide (valid p))=true := by decide +kernel

theorem needsTen {m} (mem : m∈patterns.map Pattern.m) (S : Finset ℕ) (cmp : Compatible S (fun _=>true) m) :
    10≤S.card := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
  have all : valid p := of_decide_eq_true (List.all_eq_true.mp checked _ hp)
  have subset : Finset.range 10 ⊆ S := by
    intro j hj
    by_contra no
    let i : Fin 10 := ⟨j,Finset.mem_range.mp hj⟩
    obtain ⟨yes,nay,others⟩ := all i
    have order : Signed S (fun _=>true) (rows (p.witness i).1) (rows (p.witness i).2) := by
      intro v hv
      by_cases low : v<10
      · apply others ⟨v,low⟩
        intro eq
        have vj : v=j := congrArg Fin.val eq
        exact no (vj ▸ hv)
      · have z (r : Row) : (rows r).getD v false=false :=
          List.getD_eq_default _ _ (by simp [rows,oneEach]; omega)
        rw [z,z]
        simp [LeSign]
    have res:=cmp _ _ order yes
    simp [nay] at res
  simpa using Finset.card_le_card subset

theorem excludeMono {m : ℕ} (mem : m∈patterns.map Pattern.m) (C : Circuit)
    (ok : FanInTwo C) (rep : Represents (matrix m) C) (hn : negs C.gates=0) : 9≤C.size := by
  have needed:=needsTen mem (back 10 C.gates {C.output}) (by
    intro x y order yes
    have ev (r : Row) : C.eval (rows r)=matrix m r.1 r.2 := rep r.1 r.2
    exact (ev y).symm.trans (positive 10 C ok hn _ _ (by simp [rows,oneEach]) (by simp [rows,oneEach])
      order ((ev x).trans yes)))
  have limit:=bound 10 C.gates {C.output} (fun g hg=>(ok g hg).2)
  have c:=counts C.gates
  rw [Finset.card_singleton] at limit
  change 9≤C.gates.length
  omega

private theorem subset : books.all (fun d=>decide (d.mask∈patterns.map Pattern.m))=true := by decide +kernel

theorem twentyImpossible {m : ℕ} (mem : m ∈ books.map Book.mask) :
    ¬∃ C : Circuit,FanInTwo C ∧ C.size≤5 ∧ Represents (matrix m) C := by
  rintro ⟨C,ok,small,rep⟩
  by_cases zero : negs C.gates=0
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp mem
    have lb:=excludeMono (of_decide_eq_true (List.all_eq_true.mp subset _ hd)) C ok rep zero
    omega
  · exact noNegationCircuit mem C ok small (by omega) rep

end FiveGateCone.Positive


end PEqualNP.Outside.L_meta_19331

theorem PEqualNP.Outside.L_meta_19331 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236156 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact PEqualNP.Outside.L_meta_19331.FiveGateCone.Positive.twentyImpossible (m:=16236156) (by decide +kernel)
