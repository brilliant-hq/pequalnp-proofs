import PEqualNP.Defs

-- Choose a two-row, three-column restriction of the two-block graph.
namespace PEqualNP.Outside.L_meta_25007_aux

private theorem pairInj {α : Type*} {a b : α} (hab : a ≠ b) :
    Function.Injective (![a, b] : Fin 2 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem tripleInj {α : Type*} {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem mask35_representatives {n : ℕ} (S T : Finset (Fin n))
    (hn : 3 ≤ n) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hT : T.Nonempty) (hTc : Tᶜ.Nonempty) :
    ∃ (r : Fin 2 → Fin n) (c : Fin 3 → Fin n),
      Function.Injective r ∧ Function.Injective c ∧
      ∀ i j, decide ((r i ∈ S ∧ c j ∈ T) ∨ (r i ∉ S ∧ c j ∉ T)) =
        (35 : ℕ).testBit (3 * i.val + j.val) := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y, hy⟩ := hSc
  obtain ⟨t, ht⟩ := hT
  obtain ⟨u, hu⟩ := hTc
  have hy' : y ∉ S := Finset.mem_compl.mp hy
  have hu' : u ∉ T := Finset.mem_compl.mp hu
  have hxy : x ≠ y := fun h => hy' (h ▸ hx)
  have htu : t ≠ u := fun h => hu' (h ▸ ht)
  have hex : ∃ w : Fin n, w ≠ t ∧ w ≠ u := by
    by_contra! h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {t, u} := by
      intro w _
      by_cases hwt : w = t
      · simp [hwt]
      · simp [h w hwt]
    have hcard := Finset.card_le_card hsub
    simp [htu] at hcard
    omega
  obtain ⟨w, hwt, hwu⟩ := hex
  by_cases hw : w ∈ T
  · refine ⟨![x, y], ![t, w, u], pairInj hxy, tripleInj hwt.symm htu hwu, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hx, hy', ht, hu', hw] <;> decide
  · refine ⟨![y, x], ![u, w, t], pairInj hxy.symm, tripleInj hwu.symm htu.symm hwt, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hx, hy', ht, hu', hw] <;> decide

end PEqualNP.Outside.L_meta_25007_aux

-- Enumerate the truth tables attainable within three gates on the six selected inputs.
namespace PEqualNP.Outside.L_meta_25007_aux

def raw : List Nat := [0, 7, 56, 9, 18, 36]

inductive CanStep (p : List Nat) : Nat → Prop where
  | zero : CanStep p 0
  | top : CanStep p 63
  | copy {a} (ha : a ∈ p) : CanStep p a
  | neg {a} (ha : a ∈ p) : CanStep p (63 ^^^ a)
  | conj {a b} (ha : a ∈ p) (hb : b ∈ p) : CanStep p (a &&& b)
  | disj {a b} (ha : a ∈ p) (hb : b ∈ p) : CanStep p (a ||| b)

inductive Reach : Nat → List Nat → Prop where
  | start : Reach 0 raw
  | step {k p t} (hr : Reach k p) (ht : CanStep p t) : Reach (k + 1) (t :: p)

private def candidates (p : List Nat) : List Nat :=
  (0 :: 63 :: (p ++ p.map (fun a => 63 ^^^ a) ++
    p.flatMap (fun a => p.flatMap (fun b => [a &&& b, a ||| b])))).eraseDups

private theorem mem_candidates {p t} (ht : CanStep p t) : t ∈ candidates p := by
  simp only [candidates, List.mem_eraseDups, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_flatMap]
  cases ht with
  | zero => simp
  | top => simp
  | copy ha => exact Or.inr (Or.inr (Or.inl (Or.inl ha)))
  | neg ha => exact Or.inr (Or.inr (Or.inl (Or.inr ⟨_, ha, rfl⟩)))
  | conj ha hb => exact Or.inr (Or.inr (Or.inr ⟨_, ha, _, hb, by simp⟩))
  | disj ha hb => exact Or.inr (Or.inr (Or.inr ⟨_, ha, _, hb, by simp⟩))

private def safe : Nat → List Nat → Bool
  | 0, p => !(p.contains 35)
  | n + 1, p => !(p.contains 35) && (candidates p).all (fun t => safe n (t :: p))

private theorem descend {k p} (h : Reach k p) (m : Nat)
    (hs : safe (m + k) raw = true) : safe m p = true := by
  induction h generalizing m with
  | start => simpa using hs
  | step hr ht ih =>
    have hp := ih (m + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs)
    exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 hp).2 _ (mem_candidates ht)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem raw_safe : safe 3 raw = true := by decide +kernel

theorem not_target {k p} (hr : Reach k p) (hk : k ≤ 3) : 35 ∉ p := by
  have h := descend hr (3 - k) (by simpa [Nat.sub_add_cancel hk] using raw_safe)
  cases hmk : 3 - k with
  | zero => simpa [hmk, safe] using h
  | succ n =>
    rw [hmk] at h
    simpa using (Bool.and_eq_true_iff.1 h).1

end PEqualNP.Outside.L_meta_25007_aux

-- Pack the values of a wire on the six inputs and follow each gate of the circuit.
namespace PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pack6 (p : Fin 6 → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn p)).toNat

private theorem pack6_bit (p : Fin 6 → Bool) (i : Nat) :
    (pack6 p).testBit i = if h : i < 6 then p ⟨i, h⟩ else false := by
  simp only [pack6, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD]
  by_cases h : i < 6
  · rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using h)]
    simp only [List.getElem_ofFn, Option.getD_some, dite_eq_left h]
  · simp [h]

private theorem pack6_and (p q : Fin 6 → Bool) :
    pack6 (fun i => p i && q i) = pack6 p &&& pack6 q := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 6 <;> simp [pack6_bit, Nat.testBit_and, h]

private theorem pack6_or (p q : Fin 6 → Bool) :
    pack6 (fun i => p i || q i) = pack6 p ||| pack6 q := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 6 <;> simp [pack6_bit, Nat.testBit_or, h]

private theorem pack6_not (p : Fin 6 → Bool) :
    pack6 (fun i => !(p i)) = 63 ^^^ pack6 p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (63 : Nat) = 2^6 - 1 by decide, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 6 <;> simp [pack6_bit, h]

private theorem pack6_false : pack6 (fun _ => false) = 0 := by decide
private theorem pack6_true : pack6 (fun _ => true) = 63 := by decide

private def nextBool (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

private theorem gate_step {g : Gate} {p : List Nat} (w : Fin 6 → List Bool)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hw : ∀ i, pack6 (fun k => (w k).getD i false) ∈ p) :
    CanStep p (pack6 (fun k => nextBool g (w k))) := by
  obtain ⟨op, ins⟩ := g
  change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at hop
  change ins.length ≤ 2 at hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => simpa [nextBool, GateOp.eval, pack6_true] using (CanStep.top (p := p))
    | cons a tail =>
      cases tail with
      | nil => simpa [nextBool, GateOp.eval] using CanStep.copy (hw a)
      | cons b tail =>
        cases tail with
        | nil => simpa [nextBool, GateOp.eval, pack6_and] using CanStep.conj (hw a) (hw b)
        | cons c tail => simp at hlen
  · cases ins with
    | nil => simpa [nextBool, GateOp.eval, pack6_false] using (CanStep.zero (p := p))
    | cons a tail =>
      cases tail with
      | nil => simpa [nextBool, GateOp.eval] using CanStep.copy (hw a)
      | cons b tail =>
        cases tail with
        | nil => simpa [nextBool, GateOp.eval, pack6_or] using CanStep.disj (hw a) (hw b)
        | cons c tail => simp at hlen
  · cases ins with
    | nil => simpa [nextBool, GateOp.eval, pack6_true] using (CanStep.top (p := p))
    | cons a tail => simpa [nextBool, GateOp.eval, pack6_not] using CanStep.neg (hw a)

private def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [nextBool g ws]) w

private theorem trace_aux (gs : List Gate) (hg : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (p : List Nat) (j : Nat) (hr : Reach j p) (w : Fin 6 → List Bool)
    (n : Nat) (hlen : ∀ k, (w k).length = n)
    (hw : ∀ i, pack6 (fun k => (w k).getD i false) ∈ p) :
    ∃ q, Reach (j + gs.length) q ∧
      ∀ i, pack6 (fun k => (runGates gs (w k)).getD i false) ∈ q := by
  induction gs generalizing p j w n with
  | nil => exact ⟨p, hr, hw⟩
  | cons g gs ih =>
    let b := fun k => nextBool g (w k)
    let t := pack6 b
    let w' := fun k => w k ++ [b k]
    have hg' := hg g (by simp)
    have hs : CanStep p t := gate_step w hg'.1 hg'.2 hw
    have hlen' (k) : (w' k).length = n + 1 := by simp [w', hlen k]
    have hw' (i) : pack6 (fun k => (w' k).getD i false) ∈ t :: p := by
      by_cases he : i = n
      · subst i
        have eq : (fun k => (w' k).getD n false) = b := by
          funext k
          simp [w', List.getD_eq_getElem?_getD, hlen k]
        rw [eq]
        exact List.mem_cons_self
      · have eq : (fun k => (w' k).getD i false) = (fun k => (w k).getD i false) := by
          funext k
          by_cases hi : i < n
          · simp [w', List.getD_eq_getElem?_getD, List.getElem?_append, hlen k, hi]
          · have hn : n + 1 ≤ i := by omega
            have h1 : (w k).length ≤ i := by rw [hlen]; omega
            have h2 : (w' k).length ≤ i := by rw [hlen']; omega
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
              List.getElem?_eq_none h2]
        rw [eq]
        exact List.mem_cons_of_mem _ (hw i)
    obtain ⟨q, hq, hm⟩ := ih (fun g' h => hg g' (List.mem_cons_of_mem _ h))
      (t :: p) (j+1) (.step hr hs) w' (n+1) hlen' hw'
    refine ⟨q, ?_, hm⟩
    simpa [Nat.add_assoc, Nat.add_comm 1] using hq

theorem circuit_trace (C : Circuit) (hC : FanInTwo C) (samples : Fin 6 → List Bool)
    (n : Nat) (hlen : ∀ k, (samples k).length = n)
    (hraw : ∀ i, pack6 (fun k => (samples k).getD i false) ∈ raw) :
    ∃ p, Reach C.size p ∧ pack6 (fun k => C.eval (samples k)) ∈ p := by
  obtain ⟨p, hp, hm⟩ := trace_aux C.gates hC raw 0 .start samples n hlen hraw
  exact ⟨p, by simpa [Circuit.size] using hp, hm C.output⟩

end PEqualNP.Outside.L_meta_25007_aux

-- Each input wire restricts to a row indicator, a column indicator, or zero.
namespace PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.Represents

def rowIdx (k : Fin 6) : Fin 2 := ⟨k.val / 3, by omega⟩
def colIdx (k : Fin 6) : Fin 3 := ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩

def samples {n : Nat} (r : Fin 2 → Fin n) (c : Fin 3 → Fin n) (k : Fin 6) : List Bool :=
  oneEach (r (rowIdx k)) (c (colIdx k))

theorem samples_size {n : Nat} (r : Fin 2 → Fin n) (c : Fin 3 → Fin n) (k : Fin 6) :
    (samples r c k).length = n + n := by simp [samples, oneEach]

theorem readOne {n : Nat} (u v : Fin n) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hlist : oneEach u v = List.ofFn (fun q : Fin (n+n) =>
      decide (q.val = u.val ∨ q.val = n + v.val)) := by
    apply List.ext_getElem
    · simp [oneEach]
    · intro j h h'
      simp only [oneEach, List.length_append, List.length_ofFn] at h h' ⊢
      by_cases hj : j < n
      · rw [List.getElem_append_left (by simpa using hj)]
        simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
        omega
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, decide_eq_decide]
        omega
  rw [hlist]
  by_cases hi : i < n+n
  · simp [List.getD_eq_getElem?_getD, hi]
  · have hu := u.isLt
    have hv := v.isLt
    have h₁ : i ≠ u.val := by omega
    have h₂ : i ≠ n + v.val := by omega
    simp [List.getD_eq_getElem?_getD, hi, h₁, h₂]

theorem initialShape {n : Nat} {r : Fin 2 → Fin n} {c : Fin 3 → Fin n}
    (hr : Function.Injective r) (hc : Function.Injective c) (i : Nat) :
    (fun k : Fin 6 => (samples r c k).getD i false) = (fun _ => false) ∨
    (∃ a : Fin 2, (fun k : Fin 6 => (samples r c k).getD i false) =
      (fun k => decide (rowIdx k = a))) ∨
    ∃ b : Fin 3, (fun k : Fin 6 => (samples r c k).getD i false) =
      (fun k => decide (colIdx k = b)) := by
  by_cases hrow : ∃ a, i = (r a).val
  · obtain ⟨a, rfl⟩ := hrow
    refine Or.inr (Or.inl ⟨a, ?_⟩)
    funext k
    rw [samples, readOne, decide_eq_decide]
    have hx := (r a).isLt
    constructor
    · rintro (e|e)
      · exact (hr (Fin.ext e)).symm
      · omega
    · intro h
      exact Or.inl (by rw [h])
  · by_cases hcol : ∃ b, i = n + (c b).val
    · obtain ⟨b, rfl⟩ := hcol
      refine Or.inr (Or.inr ⟨b, ?_⟩)
      funext k
      rw [samples, readOne, decide_eq_decide]
      constructor
      · rintro (e|e)
        · exact False.elim (hrow ⟨_,e⟩)
        · exact (hc (Fin.ext (Nat.add_left_cancel e))).symm
      · intro h
        exact Or.inr (by rw [h])
    · left
      funext k
      rw [samples, readOne]
      simp [show i ≠ (r (rowIdx k)).val from fun h => hrow ⟨_,h⟩,
        show i ≠ n + (c (colIdx k)).val from fun h => hcol ⟨_,h⟩]

end PEqualNP.Outside.L_meta_25007_aux

namespace PEqualNP.Outside.L_meta_25007_aux

theorem rawSample {n : Nat} {r : Fin 2 → Fin n} {c : Fin 3 → Fin n}
    (hr : Function.Injective r) (hc : Function.Injective c) (i : Nat) :
    pack6 (fun k => (samples r c k).getD i false) ∈ raw := by
  rcases initialShape hr hc i with h | ⟨a,h⟩ | ⟨b,h⟩
  · rw [h]
    decide +kernel
  · rw [h]
    fin_cases a <;> decide +kernel
  · rw [h]
    fin_cases b <;> decide +kernel

end PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.Outside.L_meta_25007_aux in
theorem PEqualNP.Outside.L_meta_25007 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C := by
  intro n S T hn hS hSc hT hTc
  rintro ⟨C, hC, hsize, hrep⟩
  obtain ⟨r,c,hr,hc,hmask⟩ := mask35_representatives S T hn hS hSc hT hTc
  obtain ⟨p, hp, hout⟩ := circuit_trace C hC (samples r c) (n+n)
    (samples_size r c) (rawSample hr hc)
  have hf : (fun k => C.eval (samples r c k)) =
      (fun k : Fin 6 => (35 : Nat).testBit k.val) := by
    funext k
    change C.eval (PEqualNP.Represents.oneEach (r (rowIdx k)) (c (colIdx k))) = _
    refine (hrep _ _).trans ((hmask (rowIdx k) (colIdx k)).trans ?_)
    congr 1
    change 3 * (k.val / 3) + k.val % 3 = k.val
    omega
  rw [hf] at hout
  have hbits : pack6 (fun k : Fin 6 => (35 : Nat).testBit k.val) = 35 := by decide +kernel
  rw [hbits] at hout
  exact not_target hp hsize hout
