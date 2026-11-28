import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49860

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 5
def zero : Sig := 0
def one : Sig := BitVec.allOnes 5
def neg (v : Sig) := ~~~v
def bit (i : Fin 5) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

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

def negTag : GateOp → Bool
  | .not => true
  | _ => false

def binNext (a b : Sig) : List Sig := [a &&& b, a ||| b]

private def needed (targets bank : List Sig) : ℕ := (targets.toFinset \ bank.toFinset).card

private lemma growth (gs : List Gate) (w : List Sig) :
    ∃ u, u.length = gs.length ∧ execute gs w = w ++ u := by
  induction gs generalizing w with
  | nil => exact ⟨[],rfl,by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨u,hu,e⟩ := ih (w++[gv w g])
    refine ⟨gv w g :: u,by simp [hu],?_⟩
    change execute gs (w++[gv w g]) = _
    rw [e]
    simp

private lemma missingBound {targets bank w : List Sig} (gs : List Gate)
    (inc : ∀ v ∈ w, v ∈ bank) (ends : ∀ v ∈ targets, v ∈ execute gs w) :
    needed targets bank ≤ gs.length := by
  obtain ⟨u,hu,e⟩ := growth gs w
  have sub : targets.toFinset \ bank.toFinset ⊆ u.toFinset := by
    intro v hv
    obtain ⟨ht,hb⟩ := Finset.mem_sdiff.mp hv
    have haveWire := ends _ (List.mem_toFinset.mp ht)
    rw [e] at haveWire
    rcases List.mem_append.mp haveWire with old | newWire
    · exact (hb (List.mem_toFinset.mpr (inc _ old))).elim
    · exact List.mem_toFinset.mpr newWire
  exact (Finset.card_le_card sub).trans ((List.toFinset_card_le u).trans hu.le)

def search (targets : List Sig) : ℕ → ℕ → List Sig → Bool
  | 0, _, bank => targets.all bank.contains
  | n+1, d, bank =>
    search targets n d bank ||
    (decide (needed targets bank ≤ n+1) && (bank.any (fun a => bank.any (fun b => (binNext a b).any fun v =>
      !bank.contains v && search targets n d (v::bank))) ||
    (d != 0 && bank.any (fun a => !bank.contains (neg a) && search targets n (d-1) (neg a::bank)))))

private lemma readMem {bank w : List Sig} (inc : ∀ v ∈ w, v ∈ bank) (hz : zero ∈ bank) (j : ℕ) :
    w.getD j zero ∈ bank := by
  by_cases lt : j < w.length
  · rw [List.getD_eq_getElem _ _ lt]
    exact inc _ (List.getElem_mem lt)
  · rwa [List.getD_eq_default _ _ (by omega)]

private lemma gateShape {bank w : List Sig} (g : Gate)
    (inc : ∀ v ∈ w, v ∈ bank) (hz : zero ∈ bank) (ho : one ∈ bank)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gv w g ∈ bank ∨ (∃ a ∈ bank, ∃ b ∈ bank, gv w g ∈ binNext a b) ∨
      (g.op = .not ∧ ∃ a ∈ bank, gv w g = neg a) := by
  have unitAnd (x : Sig) : x &&& one = x := BitVec.and_allOnes
  obtain ⟨op,args⟩ := g
  obtain ⟨legal,size⟩ := legal
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at legal
  rcases legal with rfl | rfl | rfl
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨j,rest⟩⟩⟩
    · exact Or.inl ho
    · left; simpa [gv,prime,unitAnd] using readMem inc hz a
    · right; left
      exact ⟨_,readMem inc hz a,_,readMem inc hz b,by simp [gv,prime,unitAnd,binNext]⟩
    · simp at size
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨j,rest⟩⟩⟩
    · exact Or.inl hz
    · left; simpa [gv,prime,zero] using readMem inc hz a
    · right; left
      exact ⟨_,readMem inc hz a,_,readMem inc hz b,by simp [gv,prime,zero,binNext]⟩
    · simp at size
  · right; right
    cases args with
    | nil => exact ⟨rfl,zero,hz,rfl⟩
    | cons a args => exact ⟨rfl,_,readMem inc hz a,rfl⟩

private lemma canHold (targets : List Sig) {n d bank} (yes : search targets n d bank = true) :
    search targets (n+1) d bank = true := by simp [search,yes]

private lemma searchComplete (targets : List Sig) (fuel : ℕ) (gs : List Gate) (d : ℕ) (w bank : List Sig)
    (budget : gs.length ≤ fuel) (nots : (gs.filter fun g => negTag g.op).length ≤ d)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (inc : ∀ v ∈ w, v ∈ bank) (hz : zero ∈ bank) (ho : one ∈ bank)
    (endpoints : ∀ v ∈ targets, v ∈ execute gs w) : search targets fuel d bank = true := by
  induction fuel generalizing d gs w bank with
  | zero =>
    have : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    apply List.all_eq_true.mpr
    intro v hv
    simpa using inc _ (endpoints v hv)
  | succ n ih =>
    cases gs with
    | nil => exact canHold targets (ih [] d w bank (by simp) nots legal inc hz ho endpoints)
    | cons g gs =>
      have room := (missingBound (g::gs) inc endpoints).trans budget
      have lim : gs.length ≤ n := by simpa using budget
      have bound : (gs.filter fun k => negTag k.op).length ≤ d := by
        cases h : negTag g.op <;> simp [h] at nots <;> omega
      have laws := fun k (hk : k ∈ gs) => legal k (List.mem_cons_of_mem _ hk)
      let v := gv w g
      have hits : ∀ x ∈ targets, x ∈ execute gs (w++[v]) := endpoints
      have incNew : ∀ x ∈ w++[v], x ∈ v::bank := by
        intro x hx
        rcases List.mem_append.mp hx with old | fresh
        · exact List.mem_cons_of_mem _ (inc x old)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp fresh))
      by_cases prior : v ∈ bank
      · apply canHold
        apply ih gs d (w++[v]) bank lim bound laws _ hz ho hits
        intro x hx
        rcases List.mem_append.mp hx with old | fresh
        · exact inc x old
        · exact (List.mem_singleton.mp fresh).symm ▸ prior
      · obtain existsOld | binary | unary := gateShape g inc hz ho (legal g List.mem_cons_self)
        · exact (prior existsOld).elim
        · obtain ⟨a,ha,b,hb,hv⟩ := binary
          have cont := ih gs d (w++[v]) (v::bank) lim bound laws incNew
            (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ho) hits
          simp only [search,Bool.or_eq_true]
          right
          simp only [Bool.and_eq_true,Bool.or_eq_true]
          refine ⟨by simpa using room, Or.inl ?_⟩
          apply List.any_eq_true.mpr
          refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,List.any_eq_true.mpr ⟨v,hv,?_⟩⟩⟩
          simp [prior,cont]
        · obtain ⟨op,a,ha,hv⟩ := unary
          have charged : negTag g.op = true := by simp [op,negTag]
          have cap : (gs.filter fun k => negTag k.op).length + 1 ≤ d := by
            simpa only [List.filter_cons, charged, ite_true, List.length_cons] using nots
          have bound' : (gs.filter fun k => negTag k.op).length ≤ d-1 := by omega
          have positive : d ≠ 0 := by omega
          have cont := ih gs (d-1) (w++[v]) (v::bank) lim bound' laws incNew
            (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ho) hits
          have eq : v = neg a := hv
          rw [eq] at prior cont
          simp only [search,Bool.or_eq_true]
          right
          simp only [Bool.and_eq_true,Bool.or_eq_true]
          refine ⟨by simpa using room, Or.inr ?_⟩
          refine ⟨by simpa using positive,List.any_eq_true.mpr ⟨a,ha,?_⟩⟩
          simp [prior,cont]


def raw : List Sig := [30,28,24,16,0,31]
def wanted : List Sig := [8,10,14]

private lemma initial : ∀ t : Fin 5, raw.map (bit t) =
    (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true] := by decide +kernel

private lemma masking (C : Circuit) (hm : PEqualNP.MetaComplexity.FanInTwo C) (t : Fin 5) (j : ℕ) :
    bit t ((execute C.gates raw).getD j zero) =
    (C.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true])).getD j false := by
  rw [←b_read, execute_bits _ _ _ (fun g hg => (hm g hg).1),initial]
  rfl

private lemma executeLength (gs : List Gate) (w : List Sig) : (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).length = _
    rw [ih]
    simp
    omega

private lemma outputMember (C : Circuit) (j : Fin (6 + C.size)) (v : Sig)
    (eq : (execute C.gates raw).getD j.val zero = v) : v ∈ execute C.gates raw := by
  have lt : j.val < (execute C.gates raw).length := by
    rw [executeLength]; exact j.isLt
  rw [←eq, List.getD_eq_getElem _ _ lt]
  exact List.getElem_mem lt

private lemma chargeEq (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter fun g => negTag g.op).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases op : g.op <;> simp [negTag]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem impossible : search wanted 5 2 raw = false := by decide +kernel

end PEqualNP.Outside.L_meta_49860

open PEqualNP.Outside.L_meta_49860 in
theorem PEqualNP.Outside.L_meta_49860 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (10 : Nat).testBit t.val ∧
    w.getD r.val false = (14 : Nat).testBit t.val)) := by
  rintro ⟨C,p,q,r,hm,_,negations,limit,correct⟩
  have one : (execute C.gates raw).getD p.val zero = 8 := by
    apply bit_ext
    intro t
    rw [masking C hm]
    exact (correct t).1
  have two : (execute C.gates raw).getD q.val zero = 10 := by
    apply bit_ext
    intro t
    rw [masking C hm]
    exact (correct t).2.1
  have three : (execute C.gates raw).getD r.val zero = 14 := by
    apply bit_ext
    intro t
    rw [masking C hm]
    exact (correct t).2.2
  have seen : ∀ v ∈ wanted, v ∈ execute C.gates raw := by
    intro v hv
    simp only [wanted,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact outputMember C p _ one
    · exact outputMember C q _ two
    · exact outputMember C r _ three
  rw [chargeEq] at negations
  have found := searchComplete wanted 5 C.gates 2 raw raw limit negations hm
    (fun _ h => h) (by decide) (by decide) seen
  rw [impossible] at found
  contradiction
