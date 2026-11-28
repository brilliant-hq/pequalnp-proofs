import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53138_aux

abbrev Mask := BitVec 5

def inputs : List Mask := [30, 28, 24, 16, 0, 31]


def oneGate (bank : List Mask) (out : Mask) : Bool :=
  bank.any fun a =>
    (out == ~~~a) ||
    bank.any fun b => (out == (a &&& b)) || (out == (a ||| b))

def mono (b : List Mask) (v : Mask) : Bool :=
  b.any fun x => b.any fun y => (v == (x &&& y)) || (v == (x ||| y))

def fee (b : List Mask) (v : Mask) : Nat := if mono b v then 0 else 1

def spent : Nat → List Mask → Nat
  | k+1, x :: b => spent k b + fee b x
  | _, _ => 0

def fuel : List Mask → List Mask → Nat
  | [], _ => 0
  | x :: xs, b => fee b x + fuel xs (x::b)

private theorem fee_mono {a b : List Mask} (sub : ∀ v ∈ a, v ∈ b) (x : Mask) :
    fee b x ≤ fee a x := by
  have h : mono a x = true → mono b x = true := by
    simp only [mono, List.any_eq_true]
    rintro ⟨u,hu,v,hv,op⟩
    exact ⟨u,sub _ hu,v,sub _ hv,op⟩
  unfold fee
  split <;> split <;> simp_all

def containsTargets (bank : List Mask) : Bool :=
  bank.contains 2 && bank.contains 6 && bank.contains 12


def missing (bank : List Mask) : Nat :=
  (if (2 : Mask) ∈ bank then 0 else 1) +
  (if (6 : Mask) ∈ bank then 0 else 1) +
  (if (12 : Mask) ∈ bank then 0 else 1)

def candidates (bank : List Mask) : List Mask :=
  ((bank.map (fun a => ~~~a)) ++
    (bank.flatMap fun a => bank.flatMap fun b => [a &&& b, a ||| b])).eraseDups

def nextMasks (k : Nat) (b : List Mask) : List Mask :=
  if missing b = k+1 then [2,6,12].filter (oneGate b) else candidates b

def search : Nat → List Mask → Nat → Bool
  | 0, b, _ => containsTargets b
  | k + 1, b, cost =>
    decide (missing b ≤ k+1) &&
      (search k b cost || (nextMasks k b).any fun x => !(b.contains x) &&
        (decide (fee b x ≤ cost) && search k (x :: b) (cost - fee b x)))

def Good : List Mask → List Mask → Prop
  | [], b => containsTargets b = true
  | x::xs, b => oneGate b x = true ∧ Good xs (x::b)

private theorem deficit_mono {a b : List Mask} (sub : ∀ v ∈ a, v ∈ b) :
    missing b ≤ missing a := by
  have term (x : Mask) : (if x ∈ b then 0 else 1) ≤ (if x ∈ a then 0 else 1) := by
    by_cases ha : x ∈ a
    · simp [ha, sub _ ha]
    · simp [ha]; split <;> decide
  have := term 2
  have := term 6
  have := term 12
  unfold missing
  omega

private theorem deficit_step (b : List Mask) (x : Mask) : missing b ≤ missing (x :: b) + 1 := by
  by_cases a : (2 : Mask) ∈ b <;> by_cases c : (6 : Mask) ∈ b <;> by_cases d : (12 : Mask) ∈ b <;>
    by_cases e : x = 2 <;> by_cases f : x = 6 <;> by_cases g : x = 12 <;>
    simp_all [missing, eq_comm]

private theorem deficit_bound {xs bank : List Mask} (p : Good xs bank) :
    missing bank ≤ xs.length := by
  induction xs generalizing bank with
  | nil =>
    change containsTargets bank = true at p
    simp [containsTargets] at p
    simp [missing, p]
  | cons x xs ih =>
    obtain ⟨_, tail⟩ := p
    have := ih tail
    have := deficit_step bank x
    simp only [List.length_cons]
    omega

private theorem candidate_mem {x : Mask} {a b : List Mask} (h : oneGate a x = true)
    (sub : ∀ v ∈ a, v ∈ b) : x ∈ candidates b := by
  simp only [oneGate, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨v, hv, h | ⟨w, hw, h | h⟩⟩ := h <;> subst x <;>
    simp only [candidates, List.mem_eraseDups, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false]
  · exact Or.inl ⟨v, sub _ hv, rfl⟩
  · exact Or.inr ⟨v, sub _ hv, w, sub _ hw, Or.inl rfl⟩
  · exact Or.inr ⟨v, sub _ hv, w, sub _ hw, Or.inr rfl⟩

private theorem search_complete {xs a b : List Mask} (hp : Good xs a)
    (sub : ∀ v ∈ a, v ∈ b) {cost : Nat} (enough : fuel xs a ≤ cost) : search xs.length b cost = true := by
  induction xs generalizing a b cost with
  | nil =>
    change containsTargets a = true at hp
    change containsTargets b = true
    simp [containsTargets] at hp ⊢
    exact ⟨⟨sub _ hp.1.1, sub _ hp.1.2⟩, sub _ hp.2⟩
  | cons x xs ih =>
    have bound := Nat.le_trans (deficit_mono sub) (deficit_bound hp)
    change fee a x + fuel xs (x::a) ≤ cost at enough
    have cheaper := fee_mono sub x
    obtain ⟨hg, ht⟩ := hp
    simp only [List.length_cons, search, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    refine ⟨bound, ?_⟩
    by_cases hx : x ∈ b
    · left
      apply ih ht _ (by omega)
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hx
      · exact sub _ hv
    · right
      have grow : ∀ v ∈ x::a, v ∈ x::b := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simp
        · exact List.mem_cons_of_mem _ (sub _ hv)
      have bp := Nat.le_trans (deficit_mono grow) (deficit_bound ht)
      have avail : x ∈ nextMasks xs.length b := by
        unfold nextMasks
        split <;> rename_i cond
        · have useful : x = 2 ∨ x = 6 ∨ x = 12 := by
            by_cases ha : x = 2
            · exact Or.inl ha
            by_cases hb : x = 6
            · exact Or.inr (Or.inl hb)
            by_cases hc : x = 12
            · exact Or.inr (Or.inr hc)
            have rest : missing (x :: b) = missing b := by
              simp only [missing, List.mem_cons, Ne.symm ha, Ne.symm hb, Ne.symm hc, false_or]
            omega
          have monotone : oneGate b x = true := by
            simp only [oneGate, List.any_eq_true, Bool.or_eq_true] at hg ⊢
            obtain ⟨v,hv,nv | ⟨w,hw,bv⟩⟩ := hg
            · exact ⟨v, sub _ hv, Or.inl nv⟩
            · exact ⟨v, sub _ hv, Or.inr ⟨w,sub _ hw,bv⟩⟩
          exact List.mem_filter.mpr ⟨by simpa using useful, monotone⟩
        · exact candidate_mem hg sub
      refine ⟨x, avail, ?_⟩
      simp only [Bool.not_eq_true']
      exact ⟨by simpa using hx, by omega, ih ht grow (by omega)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 40000000 in
private theorem checked : search 6 inputs 2 = false := by decide +kernel

def Trace : Nat → List Mask → Prop
  | 0, bank => bank = inputs
  | n + 1, bank => ∃ old v, bank = v :: old ∧ Trace n old ∧ oneGate old v = true

theorem Trace.start : Trace 0 inputs := rfl

theorem Trace.add {n bank v} (h : Trace n bank) (hv : oneGate bank v = true) :
    Trace (n+1) (v :: bank) := ⟨bank, v, rfl, h, hv⟩

private theorem zero_mem {n bank} (h : Trace n bank) : (0 : Mask) ∈ bank := by
  induction n generalizing bank with
  | zero => rw [show bank = inputs from h]; decide
  | succ n ih =>
    obtain ⟨old, v, rfl, hr, _⟩ := h
    exact List.mem_cons_of_mem v (ih hr)

private theorem append_zero {n bank} (h : Trace n bank) :
    Trace (n + 1) (0 :: bank) := by
  apply Trace.add h
  simp only [oneGate, List.any_eq_true, Bool.or_eq_true]
  exact ⟨0, zero_mem h, Or.inr ⟨0, zero_mem h, Or.inl (by decide)⟩⟩

private theorem no_trace {bank} (h : Trace 6 bank) : spent 6 bank ≤ 2 → containsTargets bank ≠ true := by
  obtain ⟨s5, f, rfl, h5, hf⟩ := h
  obtain ⟨s4, e, rfl, h4, he⟩ := h5
  obtain ⟨s3, d, rfl, h3, hd⟩ := h4
  obtain ⟨s2, c, rfl, h2, hc⟩ := h3
  obtain ⟨s1, b, rfl, h1, hb⟩ := h2
  obtain ⟨s0, a, rfl, h0, ha⟩ := h1
  change s0 = inputs at h0
  subst s0
  intro cost hit
  have p : Good [a,b,c,d,e,f] inputs := ⟨ha,hb,hc,hd,he,hf,hit⟩
  have success : search 6 inputs 2 = true := search_complete p (fun _ h => h) (by
    simp only [spent] at cost
    simp only [fuel]; omega)
  rw [checked] at success
  contradiction

theorem need_six {n bank} (h : Trace n bank) (cost : spent n bank ≤ 2) (hit : containsTargets bank = true) :
    7 ≤ n := by
  by_cases enough : 7 ≤ n
  · exact enough
  apply False.elim
  have pad (k : Nat) : Trace (n + k) (List.replicate k 0 ++ bank) := by
    induction k with
    | zero => simpa using h
    | succ k ih => simpa [Nat.add_assoc, List.replicate_succ] using append_zero ih
  have fee0 (b : List Mask) (hb : (0 : Mask) ∈ b) : fee b 0 = 0 := by
    have m : mono b 0 = true := by
      simp only [mono, List.any_eq_true, Bool.or_eq_true]
      exact ⟨0,hb,0,hb,Or.inl (by decide)⟩
    unfold fee; rw [m]; rfl
  have fuel_pad (k : Nat) : spent (n+k) (List.replicate k 0 ++ bank) = spent n bank := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, Nat.add_succ]
      simp only [List.cons_append, spent]
      rw [ih, fee0 _ (List.mem_append_right _ (zero_mem h)), Nat.add_zero]
  have five : n + (6 - n) = 6 := by omega
  have padded := pad (6 - n)
  rw [five] at padded
  have same_cost := fuel_pad (6-n)
  rw [five] at same_cost
  apply no_trace padded (by omega)
  simpa [containsTargets, List.contains_append] using hit


theorem input_bit_values (t : Fin 5) :
    inputs.map (fun x => x.getLsbD t.val) =
      (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true] := by
  revert t
  decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def bits (t : Fin 5) (w : List Mask) : List Bool :=
  w.map (fun m => m.getLsbD t.val)

private theorem bit_read (w : List Mask) (i : Nat) (t : Fin 5) :
    (bits t w).getD i false = (w.getD i 0).getLsbD t.val := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

private theorem read_mem (w : List Mask) (i : Nat) :
    w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · right
    simp [List.getD_eq_getElem?_getD, h]
  · left
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]

private theorem andFee {bank : List Mask} {a b : Mask} (ha : a ∈ bank) (hb : b ∈ bank) :
    fee bank (a &&& b) ≤ 0 := by
  have m : mono bank (a &&& b) = true := by
    simp only [mono, List.any_eq_true, Bool.or_eq_true]
    exact ⟨a,ha,b,hb,Or.inl (by simp)⟩
  simp [fee,m]

private theorem orFee {bank : List Mask} {a b : Mask} (ha : a ∈ bank) (hb : b ∈ bank) :
    fee bank (a ||| b) ≤ 0 := by
  have m : mono bank (a ||| b) = true := by
    simp only [mono, List.any_eq_true, Bool.or_eq_true]
    exact ⟨a,ha,b,hb,Or.inr (by simp)⟩
  simp [fee,m]

private theorem anyFee (bank : List Mask) (a : Mask) : fee bank a ≤ 1 := by
  unfold fee; split <;> decide

private theorem andGate {bank : List Mask} {a b : Mask} (ha : a ∈ bank) (hb : b ∈ bank) :
    oneGate bank (a &&& b) = true := by
  simp only [oneGate, List.any_eq_true, Bool.or_eq_true]
  exact ⟨a, ha, Or.inr ⟨b, hb, Or.inl (by simp)⟩⟩

private theorem orGate {bank : List Mask} {a b : Mask} (ha : a ∈ bank) (hb : b ∈ bank) :
    oneGate bank (a ||| b) = true := by
  simp only [oneGate, List.any_eq_true, Bool.or_eq_true]
  exact ⟨a, ha, Or.inr ⟨b, hb, Or.inr (by simp)⟩⟩

private theorem notGate {bank : List Mask} {a : Mask} (ha : a ∈ bank) :
    oneGate bank (~~~a) = true := by
  simp only [oneGate, List.any_eq_true, Bool.or_eq_true]
  exact ⟨a, ha, Or.inl (by simp)⟩

private def mark (op : GateOp) : Bool := @decide (op = .not) (lineDegreeGateOpDecEq _ _)

private theorem gate_step (g : Gate) (w bank : List Mask)
    (allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2)
    (available : ∀ m ∈ w, m ∈ bank) (h₀ : 0 ∈ bank) (h₁ : 31 ∈ bank) :
    ∃ v : Mask, fee bank v ≤ (if mark g.op then 1 else 0) ∧ oneGate bank v = true ∧ ∀ t : Fin 5,
      g.op.eval (g.inputs.map fun i => (bits t w).getD i false) = v.getLsbD t.val := by
  have rd (i : Nat) : w.getD i 0 ∈ bank := by
    rcases read_mem w i with h | h
    · rw [h]
      exact h₀
    · exact available _ h
  have full (t : Fin 5) : (31 : Mask).getLsbD t.val = true := by
    revert t
    decide
  cases g with
  | mk op ins =>
    change op = .and ∨ op = .or ∨ op = .not at allowed
    change ins.length ≤ 2 at arity
    cases ins with
    | nil =>
      rcases allowed with rfl | rfl | rfl
      · exact ⟨31 &&& 31, andFee h₁ h₁, andGate h₁ h₁, fun t => (full t).symm⟩
      · exact ⟨0 ||| 0, orFee h₀ h₀, orGate h₀ h₀, by simp [GateOp.eval]⟩
      · exact ⟨~~~0, anyFee bank _, notGate h₀, fun t => (full t).symm⟩
    | cons i tail =>
      cases tail with
      | nil =>
        rcases allowed with rfl | rfl | rfl
        · exact ⟨_, andFee (rd i) (rd i), andGate (rd i) (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        · exact ⟨_, orFee (rd i) (rd i), orGate (rd i) (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        · exact ⟨_, anyFee bank _, notGate (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
      | cons j rest =>
        cases rest with
        | nil =>
          rcases allowed with rfl | rfl | rfl
          · exact ⟨_, andFee (rd i) (rd j), andGate (rd i) (rd j), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
          · exact ⟨_, orFee (rd i) (rd j), orGate (rd i) (rd j), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
          · exact ⟨_, anyFee bank _, notGate (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        | cons k ks =>
          simp at arity

private def evalLists (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private theorem trace_fold (gs : List Gate) (n : Nat) (w bank : List Mask)
    (valid : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (tr : Trace n bank)
    (available : ∀ m ∈ w, m ∈ bank) (h₀ : 0 ∈ bank) (h₁ : 31 ∈ bank) :
    ∃ w' bank', Trace (n + gs.length) bank' ∧
      spent (n+gs.length) bank' ≤ spent n bank + (gs.filter fun u => mark u.op).length ∧
      (∀ m ∈ w', m ∈ bank') ∧ 0 ∈ bank' ∧
      ∀ t : Fin 5, evalLists gs (bits t w) = bits t w' := by
  induction gs generalizing n w bank with
  | nil => exact ⟨w, bank, tr, by simp, available, h₀, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨hop, ar⟩ := valid g (by simp)
    obtain ⟨v, price, hv, heval⟩ := gate_step g w bank hop ar available h₀ h₁
    have av : ∀ m ∈ w ++ [v], m ∈ v :: bank := by
      intro m hm
      simp at hm ⊢
      rcases hm with hm | rfl
      · exact Or.inr (available _ hm)
      · exact Or.inl rfl
    obtain ⟨w', bank', tr', score, av', z', ev'⟩ :=
      ih (n + 1) (w ++ [v]) (v :: bank) (fun u hu => valid u (List.mem_cons_of_mem _ hu))
        (Trace.add tr hv) av (List.mem_cons_of_mem _ h₀) (List.mem_cons_of_mem _ h₁)
    refine ⟨w', bank', ?_, ?_, av', z', ?_⟩
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tr'
    · have equal : n + (g::gs).length = n+1+gs.length := by simp; omega
      rw [equal]
      simp only [spent] at score
      by_cases hn : mark g.op = true <;> simp [hn] at price ⊢ <;> omega
    · intro t
      specialize ev' t
      change evalLists gs (bits t w ++ [g.op.eval (g.inputs.map fun i => (bits t w).getD i false)]) = _
      rw [heval t]
      simpa only [bits, List.map_append, List.map_cons, List.map_nil] using ev'


theorem circuit_mask_trace (D : Circuit) (fan : FanInTwo D) :
    ∃ bank, Trace D.size bank ∧ spent D.size bank ≤ PEqualNP.NotBracket.notCount D ∧ ∀ k : Nat, ∃ m ∈ bank, ∀ t : Fin 5,
      ((D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD k false) =
        m.getLsbD t.val := by
  have fv : ∀ g ∈ D.gates,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := fan
  obtain ⟨w, bank, tr, price, av, z, ev⟩ := trace_fold D.gates 0 inputs inputs fv Trace.start
    (fun _ h => h) (by decide) (by decide)
  refine ⟨bank, by simpa [Circuit.size] using tr, by simpa [spent, mark, Circuit.size, PEqualNP.NotBracket.notCount] using price, ?_⟩
  intro k
  refine ⟨w.getD k 0, ?_, ?_⟩
  · rcases read_mem w k with hk | hk
    · rw [hk]
      exact z
    · exact av _ hk
  · intro t
    rw [← input_bit_values t]
    change (evalLists D.gates (bits t inputs)).getD k false = _
    rw [ev t, bit_read]

theorem masks_of_three_outputs (D : Circuit) (fan : FanInTwo D)
    (p q r A B C : Nat)
    (compute : ∀ t : Fin 5,
      let x := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]
      (D.wires x).getD p false = A.testBit t.val ∧
      (D.wires x).getD q false = B.testBit t.val ∧
      (D.wires x).getD r false = C.testBit t.val) :
    ∃ bank, Trace D.size bank ∧ spent D.size bank ≤ PEqualNP.NotBracket.notCount D ∧ BitVec.ofNat 5 A ∈ bank ∧
      BitVec.ofNat 5 B ∈ bank ∧ BitVec.ofNat 5 C ∈ bank := by
  obtain ⟨bank, tr, price, wire⟩ := circuit_mask_trace D fan
  have member (k v : Nat) (hk : ∀ t : Fin 5,
      (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD k false =
        v.testBit t.val) : BitVec.ofNat 5 v ∈ bank := by
    obtain ⟨m, hm, he⟩ := wire k
    have eqv : BitVec.ofNat 5 v = m := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have eqbit := (hk ⟨j, hj⟩).symm.trans (he ⟨j, hj⟩)
      simpa only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and] using eqbit
    rw [eqv]
    exact hm
  exact ⟨bank, tr, price, member p A (fun t => (compute t).1),
    member q B (fun t => (compute t).2.1), member r C (fun t => (compute t).2.2)⟩

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.not, [3]⟩, ⟨.and, [6, 0]⟩, ⟨.and, [7, 0]⟩, ⟨.and, [8, 1]⟩], 11⟩


theorem fit_three :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ 3 ∧ D.size ≤ 6 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (2 : Nat).testBit t.val ∧
      w.getD q.val false = (6 : Nat).testBit t.val ∧
      w.getD r.val false = (12 : Nat).testBit t.val := by
  refine ⟨witness, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ?_, ?_, by decide, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness, Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro j hj i hi
    change j < 6 at hj
    have cases_j : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases cases_j with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt, witness] at hi <;> omega
  · decide

end PEqualNP.Outside.L_meta_53138_aux

theorem PEqualNP.Outside.L_meta_53138 :
    let fits := fun (b : Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ D.size ≤ 6 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (2 : Nat).testBit t.val ∧
      w.getD q.val false = (6 : Nat).testBit t.val ∧
      w.getD r.val false = (12 : Nat).testBit t.val
fits 3 ∧ ¬ fits 2 := by
  constructor
  · exact PEqualNP.Outside.L_meta_53138_aux.fit_three
  · rintro ⟨D, p, q, r, fan, _, count, size, compute⟩
    obtain ⟨bank, tr, price, a, b, c⟩ := PEqualNP.Outside.L_meta_53138_aux.masks_of_three_outputs D fan p.val q.val r.val 2 6 12 compute
    have hit : PEqualNP.Outside.L_meta_53138_aux.containsTargets bank = true := by
      simp only [PEqualNP.Outside.L_meta_53138_aux.containsTargets, Bool.and_eq_true, List.contains_iff_mem]
      exact ⟨⟨a, b⟩, c⟩
    have := PEqualNP.Outside.L_meta_53138_aux.need_six tr (by omega) hit
    omega
  
