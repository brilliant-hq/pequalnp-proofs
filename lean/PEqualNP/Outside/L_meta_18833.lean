import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18833_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]



def okMono (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => decide (g.inputs.length ≤ 2)
  | PEqualNP.CircuitLowerBounds.GateOp.or => decide (g.inputs.length ≤ 2)
  | _ => false

theorem okMono_spec (C : PEqualNP.CircuitLowerBounds.Circuit) (h : C.gates.all okMono = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have hg' := List.all_eq_true.mp h g hg
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [okMono]

def okFan (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => decide (g.inputs.length ≤ 2)
  | PEqualNP.CircuitLowerBounds.GateOp.or => decide (g.inputs.length ≤ 2)
  | PEqualNP.CircuitLowerBounds.GateOp.not => decide (g.inputs.length ≤ 2)
  | _ => false

theorem okFan_spec (C : PEqualNP.CircuitLowerBounds.Circuit) (h : C.gates.all okFan = true) :
    PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  have hg' := List.all_eq_true.mp h g hg
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [okFan]


theorem repWitness (bank : List (BitVec 196)) (goal : BitVec 196)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Nat) (A : Fin 14 → Fin 14 → Bool)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hsz : C.size ≤ s)
    (hBank : ∀ u v : Fin 14, (bank.map fun w => w.getLsbD (14 * u.val + v.val)) =
      PEqualNP.Represents.oneEach u v)
    (hGoal : ∀ u v : Fin 14, goal.getLsbD (14 * u.val + v.val) = A u v)
    (hEval : (C.gates.foldl hcsStep bank).getD C.output 0 = goal) :
    PEqualNP.Represents.RepSizeAtMost A s := by
  refine ⟨C, hmono, hsz, ?_⟩
  intro u v
  have hr : 14 * u.val + v.val < 196 := by omega
  have hfan : ∀ g ∈ C.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    have h1 := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  have hbits := hcsFoldBits bank ⟨14 * u.val + v.val, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (PEqualNP.Represents.oneEach u v)).getD C.output false = A u v
  rw [← hBank u v, ← hbits, ← hcsGetDBit, hEval, hGoal]

def witness : Circuit := ⟨[⟨.or, [0, 21]⟩, ⟨.or, [1, 22]⟩, ⟨.or, [2, 23]⟩, ⟨.or, [3, 24]⟩, ⟨.or, [4, 25]⟩, ⟨.or, [5, 26]⟩, ⟨.or, [6, 27]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [42, 38]⟩, ⟨.and, [28, 43]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [45, 39]⟩, ⟨.and, [29, 46]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [48, 40]⟩, ⟨.and, [30, 49]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [51, 41]⟩, ⟨.and, [31, 52]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [54, 35]⟩, ⟨.and, [32, 55]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [57, 36]⟩, ⟨.and, [33, 58]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [60, 37]⟩, ⟨.and, [34, 61]⟩, ⟨.or, [44, 47]⟩, ⟨.or, [63, 50]⟩, ⟨.or, [64, 53]⟩, ⟨.or, [65, 56]⟩, ⟨.or, [66, 59]⟩, ⟨.or, [67, 62]⟩], 68⟩
def bank : List (BitVec 196) := [BitVec.ofNat 196 0x3fff, BitVec.ofNat 196 0xfffc000, BitVec.ofNat 196 0x3fff0000000, BitVec.ofNat 196 0xfffc0000000000, BitVec.ofNat 196 0x3fff00000000000000, BitVec.ofNat 196 0xfffc00000000000000000, BitVec.ofNat 196 0x3fff000000000000000000000, BitVec.ofNat 196 0xfffc000000000000000000000000, BitVec.ofNat 196 0x3fff0000000000000000000000000000, BitVec.ofNat 196 0xfffc0000000000000000000000000000000, BitVec.ofNat 196 0x3fff00000000000000000000000000000000000, BitVec.ofNat 196 0xfffc00000000000000000000000000000000000000, BitVec.ofNat 196 0x3fff000000000000000000000000000000000000000000, BitVec.ofNat 196 0xfffc000000000000000000000000000000000000000000000, BitVec.ofNat 196 0x4001000400100040010004001000400100040010004001, BitVec.ofNat 196 0x8002000800200080020008002000800200080020008002, BitVec.ofNat 196 0x10004001000400100040010004001000400100040010004, BitVec.ofNat 196 0x20008002000800200080020008002000800200080020008, BitVec.ofNat 196 0x40010004001000400100040010004001000400100040010, BitVec.ofNat 196 0x80020008002000800200080020008002000800200080020, BitVec.ofNat 196 0x100040010004001000400100040010004001000400100040, BitVec.ofNat 196 0x200080020008002000800200080020008002000800200080, BitVec.ofNat 196 0x400100040010004001000400100040010004001000400100, BitVec.ofNat 196 0x800200080020008002000800200080020008002000800200, BitVec.ofNat 196 0x1000400100040010004001000400100040010004001000400, BitVec.ofNat 196 0x2000800200080020008002000800200080020008002000800, BitVec.ofNat 196 0x4001000400100040010004001000400100040010004001000, BitVec.ofNat 196 0x8002000800200080020008002000800200080020008002000]
def goal : BitVec 196 := BitVec.ofNat 196 0xd001a0034006808c01180a2000450188031016002c005800b
end PEqualNP.Outside.L_meta_18833_aux
open PEqualNP.Outside.L_meta_18833_aux in
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_18833 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 14 => decide ((u.val < 7 ∧ v.val < 7 ∧ (v.val + 7 - u.val) % 7 ∈ [0, 1, 3]) ∨ (7 ≤ u.val ∧ 7 ≤ v.val ∧ (u.val + 7 - v.val) % 7 ∈ [0, 1, 3]))) 41) := by
  exact repWitness bank goal witness 41 _ (okMono_spec _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
