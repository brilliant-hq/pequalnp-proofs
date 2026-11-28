import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50171_aux

abbrev Mask := BitVec 6

def inputs : List Mask := [62, 60, 56, 48, 32, 0, 63]


def oneGate (bank : List Mask) (out : Mask) : Bool :=
  bank.any fun a =>
    (out == ~~~a) ||
    bank.any fun b => (out == (a &&& b)) || (out == (a ||| b))

def containsTargets (bank : List Mask) : Bool :=
  bank.contains 18 && bank.contains 26 && bank.contains 50


def missing (bank : List Mask) : Nat :=
  (if (18 : Mask) ∈ bank then 0 else 1) +
  (if (26 : Mask) ∈ bank then 0 else 1) +
  (if (50 : Mask) ∈ bank then 0 else 1)

def candidates (bank : List Mask) : List Mask :=
  ((bank.map (fun a => ~~~a)) ++
    (bank.flatMap fun a => bank.flatMap fun b => [a &&& b, a ||| b])).eraseDups

def nextMasks (k : Nat) (b : List Mask) : List Mask :=
  if missing b = k+1 then [18,26,50].filter (oneGate b) else candidates b

def search : Nat → List Mask → Bool
  | 0, b => containsTargets b
  | k + 1, b =>
    decide (missing b ≤ k+1) &&
      (search k b || (nextMasks k b).any fun x => !(b.contains x) && search k (x :: b))

def Good : List Mask → List Mask → Prop
  | [], b => containsTargets b = true
  | x::xs, b => oneGate b x = true ∧ Good xs (x::b)

private theorem deficit_mono {a b : List Mask} (sub : ∀ v ∈ a, v ∈ b) :
    missing b ≤ missing a := by
  have term (x : Mask) : (if x ∈ b then 0 else 1) ≤ (if x ∈ a then 0 else 1) := by
    by_cases ha : x ∈ a
    · simp [ha, sub _ ha]
    · simp [ha]; split <;> decide
  have := term 18
  have := term 26
  have := term 50
  unfold missing
  omega

private theorem deficit_step (b : List Mask) (x : Mask) : missing b ≤ missing (x :: b) + 1 := by
  by_cases a : (18 : Mask) ∈ b <;> by_cases c : (26 : Mask) ∈ b <;> by_cases d : (50 : Mask) ∈ b <;>
    by_cases e : x = 18 <;> by_cases f : x = 26 <;> by_cases g : x = 50 <;>
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
    (sub : ∀ v ∈ a, v ∈ b) : search xs.length b = true := by
  induction xs generalizing a b with
  | nil =>
    change containsTargets a = true at hp
    change containsTargets b = true
    simp [containsTargets] at hp ⊢
    exact ⟨⟨sub _ hp.1.1, sub _ hp.1.2⟩, sub _ hp.2⟩
  | cons x xs ih =>
    have bound := Nat.le_trans (deficit_mono sub) (deficit_bound hp)
    obtain ⟨hg, ht⟩ := hp
    simp only [List.length_cons, search, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    refine ⟨bound, ?_⟩
    by_cases hx : x ∈ b
    · left
      apply ih ht
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
        · have useful : x = 18 ∨ x = 26 ∨ x = 50 := by
            by_cases ha : x = 18
            · exact Or.inl ha
            by_cases hb : x = 26
            · exact Or.inr (Or.inl hb)
            by_cases hc : x = 50
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
      exact ⟨by simpa using hx, ih ht grow⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 40000000 in
private theorem checked : search 6 inputs = false := by decide +kernel

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

private theorem six_trace {bank} (h : Trace 6 bank) :
    containsTargets bank ≠ true := by
  obtain ⟨s₅, f, rfl, h₅, hf⟩ := h
  obtain ⟨s₄, e, rfl, h₄, he⟩ := h₅
  obtain ⟨s₃, d, rfl, h₃, hd⟩ := h₄
  obtain ⟨s₂, c, rfl, h₂, hc⟩ := h₃
  obtain ⟨s₁, b, rfl, h₁, hb⟩ := h₂
  obtain ⟨s₀, a, rfl, h₀, ha⟩ := h₁
  change s₀ = inputs at h₀
  subst s₀
  intro hit
  have p : Good [a,b,c,d,e,f] inputs := ⟨ha,hb,hc,hd,he,hf,hit⟩
  have success : search 6 inputs = true := search_complete p (fun _ h => h)
  rw [checked] at success
  contradiction

theorem need_six {n bank} (h : Trace n bank) (hit : containsTargets bank = true) :
    7 ≤ n := by
  by_cases enough : 7 ≤ n
  · exact enough
  apply False.elim
  have pad (k : Nat) : Trace (n + k) (List.replicate k 0 ++ bank) := by
    induction k with
    | zero => simpa using h
    | succ k ih => simpa [Nat.add_assoc, List.replicate_succ] using append_zero ih
  have five : n + (6 - n) = 6 := by omega
  have padded := pad (6 - n)
  rw [five] at padded
  apply six_trace padded
  simpa [containsTargets, List.contains_append] using hit


theorem input_bit_values (t : Fin 6) :
    inputs.map (fun x => x.getLsbD t.val) =
      (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] := by
  revert t
  decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def bits (t : Fin 6) (w : List Mask) : List Bool :=
  w.map (fun m => m.getLsbD t.val)

private theorem bit_read (w : List Mask) (i : Nat) (t : Fin 6) :
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

private theorem gate_step (g : Gate) (w bank : List Mask)
    (allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2)
    (available : ∀ m ∈ w, m ∈ bank) (h₀ : 0 ∈ bank) (h₁ : 63 ∈ bank) :
    ∃ v : Mask, oneGate bank v = true ∧ ∀ t : Fin 6,
      g.op.eval (g.inputs.map fun i => (bits t w).getD i false) = v.getLsbD t.val := by
  have rd (i : Nat) : w.getD i 0 ∈ bank := by
    rcases read_mem w i with h | h
    · rw [h]
      exact h₀
    · exact available _ h
  have full (t : Fin 6) : (63 : Mask).getLsbD t.val = true := by
    revert t
    decide
  cases g with
  | mk op ins =>
    change op = .and ∨ op = .or ∨ op = .not at allowed
    change ins.length ≤ 2 at arity
    cases ins with
    | nil =>
      rcases allowed with rfl | rfl | rfl
      · exact ⟨63 &&& 63, andGate h₁ h₁, fun t => (full t).symm⟩
      · exact ⟨0 ||| 0, orGate h₀ h₀, by simp [GateOp.eval]⟩
      · exact ⟨~~~0, notGate h₀, fun t => (full t).symm⟩
    | cons i tail =>
      cases tail with
      | nil =>
        rcases allowed with rfl | rfl | rfl
        · exact ⟨_, andGate (rd i) (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        · exact ⟨_, orGate (rd i) (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        · exact ⟨_, notGate (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
      | cons j rest =>
        cases rest with
        | nil =>
          rcases allowed with rfl | rfl | rfl
          · exact ⟨_, andGate (rd i) (rd j), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
          · exact ⟨_, orGate (rd i) (rd j), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
          · exact ⟨_, notGate (rd i), by intro t; simp only [GateOp.eval, List.map_cons, List.map_nil, bit_read]; simp⟩
        | cons k ks =>
          simp at arity

private def evalLists (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private theorem trace_fold (gs : List Gate) (n : Nat) (w bank : List Mask)
    (valid : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (tr : Trace n bank)
    (available : ∀ m ∈ w, m ∈ bank) (h₀ : 0 ∈ bank) (h₁ : 63 ∈ bank) :
    ∃ w' bank', Trace (n + gs.length) bank' ∧
      (∀ m ∈ w', m ∈ bank') ∧ 0 ∈ bank' ∧
      ∀ t : Fin 6, evalLists gs (bits t w) = bits t w' := by
  induction gs generalizing n w bank with
  | nil => exact ⟨w, bank, tr, available, h₀, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨hop, ar⟩ := valid g (by simp)
    obtain ⟨v, hv, heval⟩ := gate_step g w bank hop ar available h₀ h₁
    have av : ∀ m ∈ w ++ [v], m ∈ v :: bank := by
      intro m hm
      simp at hm ⊢
      rcases hm with hm | rfl
      · exact Or.inr (available _ hm)
      · exact Or.inl rfl
    obtain ⟨w', bank', tr', av', z', ev'⟩ :=
      ih (n + 1) (w ++ [v]) (v :: bank) (fun u hu => valid u (List.mem_cons_of_mem _ hu))
        (Trace.add tr hv) av (List.mem_cons_of_mem _ h₀) (List.mem_cons_of_mem _ h₁)
    refine ⟨w', bank', ?_, av', z', ?_⟩
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tr'
    · intro t
      specialize ev' t
      change evalLists gs (bits t w ++ [g.op.eval (g.inputs.map fun i => (bits t w).getD i false)]) = _
      rw [heval t]
      simpa only [bits, List.map_append, List.map_cons, List.map_nil] using ev'


theorem circuit_mask_trace (D : Circuit) (fan : FanInTwo D) :
    ∃ bank, Trace D.size bank ∧ ∀ k : Nat, ∃ m ∈ bank, ∀ t : Fin 6,
      ((D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD k false) =
        m.getLsbD t.val := by
  have fv : ∀ g ∈ D.gates,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := fan
  obtain ⟨w, bank, tr, av, z, ev⟩ := trace_fold D.gates 0 inputs inputs fv Trace.start
    (fun _ h => h) (by decide) (by decide)
  refine ⟨bank, by simpa [Circuit.size] using tr, ?_⟩
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
    (compute : ∀ t : Fin 6,
      let x := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
      (D.wires x).getD p false = A.testBit t.val ∧
      (D.wires x).getD q false = B.testBit t.val ∧
      (D.wires x).getD r false = C.testBit t.val) :
    ∃ bank, Trace D.size bank ∧ BitVec.ofNat 6 A ∈ bank ∧
      BitVec.ofNat 6 B ∈ bank ∧ BitVec.ofNat 6 C ∈ bank := by
  obtain ⟨bank, tr, wire⟩ := circuit_mask_trace D fan
  have member (k v : Nat) (hk : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD k false =
        v.testBit t.val) : BitVec.ofNat 6 v ∈ bank := by
    obtain ⟨m, hm, he⟩ := wire k
    have eqv : BitVec.ofNat 6 v = m := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      have eqbit := (hk ⟨j, hj⟩).symm.trans (he ⟨j, hj⟩)
      simpa only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and] using eqbit
    rw [eqv]
    exact hm
  exact ⟨bank, tr, member p A (fun t => (compute t).1),
    member q B (fun t => (compute t).2.1), member r C (fun t => (compute t).2.2)⟩

end PEqualNP.Outside.L_meta_50171_aux

theorem PEqualNP.Outside.L_meta_50171 :
  ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (18 : Nat).testBit t.val ∧
    w.getD q.val false = (26 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, fan, _, _, size, compute⟩
  obtain ⟨bank, tr, a, b, c⟩ := PEqualNP.Outside.L_meta_50171_aux.masks_of_three_outputs D fan p.val q.val r.val 18 26 50 compute
  have hit : PEqualNP.Outside.L_meta_50171_aux.containsTargets bank = true := by
    simp only [PEqualNP.Outside.L_meta_50171_aux.containsTargets, Bool.and_eq_true, List.contains_iff_mem]
    exact ⟨⟨a, b⟩, c⟩
  have := PEqualNP.Outside.L_meta_50171_aux.need_six tr hit
  omega

