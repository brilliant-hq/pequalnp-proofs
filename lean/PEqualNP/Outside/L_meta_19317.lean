import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19317
abbrev flag (v : Nat) : Nat := 1 <<< v
def pairRange (x y : Nat) : Nat := flag (x &&& y) ||| flag (x ||| y)
def direct (ws : List Nat) (x : Nat) : Nat :=
  ws.foldl (fun s y => s ||| pairRange x y) (flag x ||| flag (127 ^^^ x))
def mates (t x : Nat) : Nat :=
  (List.range 128).foldl (fun acc y =>
    if x &&& y == t || x ||| y == t then acc ||| flag y else acc) 0
structure Pool where
  wires : List Nat
  choices : Nat
  finish : Nat
def insert (partners : Nat → Nat) (p : Pool) (x : Nat) : Pool :=
  ⟨x :: p.wires, p.choices ||| direct p.wires x, p.finish ||| partners x⟩
def initial (partners : Nat → Nat) : Pool :=
  [0,127,7,24,96,33,74,20].foldl (insert partners) ⟨[],0,flag 46 ||| flag (127 ^^^ 46)⟩
def safe (partners : Nat → Nat) : Nat → Pool → Bool
  | 0, p => p.choices &&& p.finish == 0
  | k+1, p => (p.choices &&& p.finish == 0) && (List.range 128).all fun x =>
    !p.choices.testBit x || safe partners k (insert partners p x)
def table : Nat → Nat
  | 0 => 70368744177664
  | 1 => 0
  | 2 => 87960930222080
  | 3 => 0
  | 4 => 74766790688768
  | 5 => 0
  | 6 => 93458488360960
  | 7 => 0
  | 8 => 70643622084608
  | 9 => 0
  | 10 => 88304527605760
  | 11 => 0
  | 12 => 75058848464896
  | 13 => 0
  | 14 => 93823560581120
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 70368744194048
  | 33 => 0
  | 34 => 87960930242560
  | 35 => 0
  | 36 => 74766790706176
  | 37 => 0
  | 38 => 93458488382720
  | 39 => 0
  | 40 => 70643622101056
  | 41 => 0
  | 42 => 88304527626320
  | 43 => 0
  | 44 => 75058848482372
  | 45 => 0
  | 46 => 255215669413347748732087646062404195669
  | 47 => 85071889804449249577362540869195923456
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 0
  | 58 => 0
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 3894222643901120721608978479448064
  | 63 => 1298074214633706907202992826482688
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 0
  | 68 => 0
  | 69 => 0
  | 70 => 0
  | 71 => 0
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 0
  | 81 => 0
  | 82 => 0
  | 83 => 0
  | 84 => 0
  | 85 => 0
  | 86 => 0
  | 87 => 0
  | 88 => 0
  | 89 => 0
  | 90 => 0
  | 91 => 0
  | 92 => 0
  | 93 => 0
  | 94 => 0
  | 95 => 0
  | 96 => 0
  | 97 => 0
  | 98 => 0
  | 99 => 0
  | 100 => 0
  | 101 => 0
  | 102 => 0
  | 103 => 0
  | 104 => 0
  | 105 => 0
  | 106 => 0
  | 107 => 0
  | 108 => 0
  | 109 => 0
  | 110 => 13835269161514696704
  | 111 => 4611756387171565568
  | 112 => 0
  | 113 => 0
  | 114 => 0
  | 115 => 0
  | 116 => 0
  | 117 => 0
  | 118 => 0
  | 119 => 0
  | 120 => 0
  | 121 => 0
  | 122 => 0
  | 123 => 0
  | 124 => 0
  | 125 => 0
  | 126 => 211106232532992
  | 127 => 70368744177664
  | _ => 0
def Has (s x : Nat) : Prop := s.testBit x = true

theorem hasFlag (i : Nat) : Has (flag i) i := by
  simp [Has, flag, Nat.testBit_shiftLeft]

theorem hasUnion {s t x : Nat} : Has (s ||| t) x ↔ Has s x ∨ Has t x := by
  simp [Has, Nat.testBit_or]

theorem hasFold {α : Type} (f : α → Nat) (l : List α) (z x : Nat) :
    Has (l.foldl (fun acc a => acc ||| f a) z) x ↔
      Has z x ∨ ∃ a ∈ l, Has (f a) x := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, hasUnion, List.mem_cons]
    aesop

theorem directSpec (ws : List Nat) (x : Nat) :
    Has (direct ws x) x ∧ Has (direct ws x) (127 ^^^ x) ∧
    ∀ y ∈ ws, Has (direct ws x) (x &&& y) ∧ Has (direct ws x) (x ||| y) := by
  simp only [direct, hasFold, hasUnion, pairRange]
  refine ⟨Or.inl (Or.inl (hasFlag _)), Or.inl (Or.inr (hasFlag _)), ?_⟩
  intro y hy
  exact ⟨Or.inr ⟨y, hy, Or.inl (hasFlag _)⟩, Or.inr ⟨y, hy, Or.inr (hasFlag _)⟩⟩

def Good (p : Pool) : Prop :=
  (∀ x ∈ p.wires, x < 128 ∧ Has p.choices x ∧ Has p.choices (127 ^^^ x)) ∧
  (∀ x ∈ p.wires, ∀ y ∈ p.wires, Has p.choices (x &&& y) ∧ Has p.choices (x ||| y)) ∧
  (∀ x ∈ p.wires, ∀ y < 128, x &&& y = 46 ∨ x ||| y = 46 → Has p.finish y) ∧
  Has p.finish 46 ∧ Has p.finish (127 ^^^ 46)

theorem tableSpec : ∀ x : Fin 128, ∀ y : Fin 128,
    (x.val &&& y.val = 46 ∨ x.val ||| y.val = 46) → (table x.val).testBit y.val = true := by
  decide +kernel

theorem goodInsert {p : Pool} (hp : Good p) (a : Nat) (ha : a < 128) :
    Good (insert table p a) := by
  obtain ⟨hw, hpair, hmate, ht, hnt⟩ := hp
  obtain ⟨hd, hn, hb⟩ := directSpec p.wires a
  refine ⟨?_, ?_, ?_, hasUnion.mpr (.inl ht), hasUnion.mpr (.inl hnt)⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨ha, hasUnion.mpr (.inr hd), hasUnion.mpr (.inr hn)⟩
    · obtain ⟨h1,h2,h3⟩ := hw x hx
      exact ⟨h1, hasUnion.mpr (.inl h2), hasUnion.mpr (.inl h3)⟩
  · intro x hx y hy
    change x ∈ a :: p.wires at hx
    change y ∈ a :: p.wires at hy
    rcases List.mem_cons.mp hx with eqx | hx <;> rcases List.mem_cons.mp hy with eqy | hy
    all_goals try subst x
    all_goals try subst y
    · simp only [Nat.and_self, Nat.or_self]
      exact ⟨hasUnion.mpr (.inr hd), hasUnion.mpr (.inr hd)⟩
    · exact ⟨hasUnion.mpr (.inr (hb y hy).1), hasUnion.mpr (.inr (hb y hy).2)⟩
    · rw [Nat.and_comm, Nat.or_comm]
      exact ⟨hasUnion.mpr (.inr (hb x hx).1), hasUnion.mpr (.inr (hb x hx).2)⟩
    · exact ⟨hasUnion.mpr (.inl (hpair x hx y hy).1), hasUnion.mpr (.inl (hpair x hx y hy).2)⟩
  · intro x hx y hy h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hasUnion.mpr (.inr (tableSpec ⟨_,ha⟩ ⟨_,hy⟩ h))
    · exact hasUnion.mpr (.inl (hmate x hx y hy h))

theorem initialGood : Good (initial table) := by
  unfold initial
  simp only [List.foldl_cons, List.foldl_nil]
  iterate 8 first | apply goodInsert <;> try decide
  simp [Good, hasUnion, hasFlag]
inductive Move (ws : List Nat) : Nat → Prop
  | keep {a} : a ∈ ws → Move ws a
  | neg {a} : a ∈ ws → Move ws (127 ^^^ a)
  | conj {a b} : a ∈ ws → b ∈ ws → Move ws (a &&& b)
  | disj {a b} : a ∈ ws → b ∈ ws → Move ws (a ||| b)

theorem moveChoice {p : Pool} (h : Good p) {x : Nat} (m : Move p.wires x) : Has p.choices x := by
  cases m with
  | keep a => exact (h.1 _ a).2.1
  | neg a => exact (h.1 _ a).2.2
  | conj a b => exact (h.2.1 _ a _ b).1
  | disj a b => exact (h.2.1 _ a _ b).2

inductive Run : Nat → List Nat → Prop
  | done {n ws} : 46 ∈ ws → Run n ws
  | tick {n ws x} : x < 128 → Move ws x → Run n (x :: ws) → Run (n+1) ws

theorem oneChoice {p : Pool} (hp : Good p) (r : Run 1 p.wires) : Has p.choices 46 := by
  cases r with
  | done h => exact (hp.1 _ h).2.1
  | tick _ m rest =>
    cases rest with
    | done out =>
      rcases List.mem_cons.mp out with eq | old
      · rw [eq]
        exact moveChoice hp m
      · exact (hp.1 _ old).2.1

theorem directFinish {p : Pool} (hp : Good p) {x : Nat} (hx : x < 128)
    (d : Has (direct p.wires x) 46) : Has p.finish x := by
  have flagEq (a b : Nat) : Has (flag a) b → b = a := by
    simpa [Has, flag, Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero] using
      (show (a ≤ b ∧ b - a = 0) → b = a from by omega)
  rw [direct, hasFold] at d
  rcases d with base | ⟨a,ha,hab⟩
  · rcases hasUnion.mp base with s | s
    · rw [← flagEq _ _ s]
      exact hp.2.2.2.1
    · have he := flagEq _ _ s
      have h : x = 127 ^^^ 46 := by rw [he, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [h]
      exact hp.2.2.2.2
  · rcases hasUnion.mp hab with s | s
    · exact hp.2.2.1 a ha x hx (.inl (by rw [Nat.and_comm]; exact (flagEq _ _ s).symm))
    · exact hp.2.2.1 a ha x hx (.inr (by rw [Nat.or_comm]; exact (flagEq _ _ s).symm))

theorem baseSound {p : Pool} (hp : Good p) (h : p.choices &&& p.finish == 0) :
    ¬ Run 2 p.wires := by
  have disjoint (x : Nat) (hc : Has p.choices x) (hf : Has p.finish x) : False := by
    have he := congrArg (fun v : Nat => v.testBit x) (eq_of_beq h)
    simp [Has] at hc hf
    simp [Nat.testBit_and, hc, hf] at he
  intro r
  cases r with
  | done h => exact disjoint 46 (hp.1 _ h).2.1 hp.2.2.2.1
  | tick hx m rest =>
    have hg := goodInsert hp _ hx
    obtain old | new := hasUnion.mp (oneChoice hg rest)
    · exact disjoint 46 old hp.2.2.2.1
    · exact disjoint _ (moveChoice hp m) (directFinish hp hx new)

theorem safeSound {k : Nat} {p : Pool} (hp : Good p) (h : safe table k p = true) :
    ¬ Run (k+2) p.wires := by
  induction k generalizing p with
  | zero => exact baseSound hp h
  | succ k ih =>
    simp only [safe, Bool.and_eq_true, List.all_eq_true] at h
    intro r
    cases r with
    | done hm => exact baseSound hp h.1 (.done hm)
    | tick hx m rest =>
      have hc := moveChoice hp m
      have hh := h.2 _ (List.mem_range.mpr hx)
      simp [Has] at hc
      simp [hc] at hh
      exact ih (goodInsert hp _ hx) hh rest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
abbrev Samples := Fin 7 → List Bool
def Models (ws : List Nat) (bits : Samples) : Prop :=
  ∀ i : Nat, ∃ x ∈ ws, x < 128 ∧ ∀ t : Fin 7, (bits t).getD i false = x.testBit t.val
def val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def push (w : List Bool) (g : Gate) := w ++ [val g w]

theorem allOnes : ∀ t : Fin 7, (127 : Nat).testBit t.val = true := by decide
theorem opWitness {ws : List Nat} {bs : Samples} (hm : Models ws bs) (hz : 0 ∈ ws) (ht : 127 ∈ ws)
    (g : Gate) (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hn : g.inputs.length ≤ 2) :
    ∃ x < 128, Move ws x ∧ ∀ t, val g (bs t) = x.testBit t.val := by
  rcases g with ⟨op,is⟩
  change is.length ≤ 2 at hn
  change op = _ ∨ op = _ ∨ op = _ at hop
  cases is with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨127, by decide, .keep ht, fun t => (allOnes t).symm⟩
    · exact ⟨0, by decide, .keep hz, fun t => by simp [val, GateOp.eval]⟩
    · exact ⟨127, by decide, .keep ht, fun t => (allOnes t).symm⟩
  | cons i tail =>
    obtain ⟨a,ha,ba,ea⟩ := hm i
    have hnot : ∀ t : Fin 7, (!(bs t).getD i false) = (127 ^^^ a).testBit t.val := by
      intro t
      rw [Nat.testBit_xor, allOnes, ea]
      cases a.testBit t.val <;> rfl
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨a, ba, .keep ha, fun t => by simpa [val, GateOp.eval] using ea t⟩
      · exact ⟨a, ba, .keep ha, fun t => by simpa [val, GateOp.eval] using ea t⟩
      · exact ⟨_, Nat.xor_lt_two_pow (n:=7) (by decide) ba, .neg ha, fun t => by simpa [val, GateOp.eval] using hnot t⟩
    | cons j tail =>
      have e : tail = [] := by simpa using hn
      subst tail
      obtain ⟨b,hb,bb,eb⟩ := hm j
      rcases hop with rfl | rfl | rfl
      · refine ⟨_, lt_of_le_of_lt Nat.and_le_left ba, .conj ha hb, ?_⟩
        intro t
        simpa [val, GateOp.eval, Nat.testBit_and] using congrArg₂ Bool.and (ea t) (eb t)
      · refine ⟨_, Nat.or_lt_two_pow (n:=7) ba bb, .disj ha hb, ?_⟩
        intro t
        simpa [val, GateOp.eval, Nat.testBit_or] using congrArg₂ Bool.or (ea t) (eb t)
      · exact ⟨_, Nat.xor_lt_two_pow (n:=7) (by decide) ba, .neg ha, fun t => by simpa [val, GateOp.eval] using hnot t⟩

theorem pushModels {ws : List Nat} {bs : Samples} (hm : Models ws bs) {N : Nat}
    (hl : ∀ t, (bs t).length = N) {g : Gate} {x : Nat} (hx : x < 128)
    (he : ∀ t, val g (bs t) = x.testBit t.val) : Models (x::ws) (fun t => push (bs t) g) := by
  intro i
  by_cases e : i = N
  · subst i
    refine ⟨x, .head _, hx, fun t => ?_⟩
    simpa [push, List.getD_eq_getElem?_getD, List.getElem?_append, hl t] using he t
  · obtain ⟨v,hv,bv,ev⟩ := hm i
    refine ⟨v, .tail _ hv, bv, fun t => ?_⟩
    rw [← ev t]
    by_cases hi : i < N
    · simp [push, List.getD_eq_getElem?_getD, List.getElem?_append, hl t, hi]
    · have hl' : (bs t)[i]? = none := List.getElem?_eq_none (by rw [hl]; omega)
      have d : i - N ≠ 0 := by omega
      simp [push, List.getD_eq_getElem?_getD, List.getElem?_append, hl t, hi, d]
theorem uniqueSig : ∀ x : Fin 128, (∀ t : Fin 7, x.val.testBit t.val = (46 : Nat).testBit t.val) → x.val = 46 := by
  decide +kernel

theorem gatesRun (gs : List Gate) (bs : Samples) (ws : List Nat) (out N k : Nat)
    (hm : Models ws bs) (hz : 0 ∈ ws) (ht : 127 ∈ ws) (hl : ∀ t, (bs t).length = N)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (budget : gs.length ≤ k)
    (goal : ∀ t : Fin 7, (gs.foldl push (bs t)).getD out false = (46 : Nat).testBit t.val) : Run k ws := by
  induction gs generalizing bs ws N k with
  | nil =>
    obtain ⟨x,hx,bx,he⟩ := hm out
    have eq := uniqueSig ⟨x,bx⟩ (fun t => (he t).symm.trans (goal t))
    exact .done (eq ▸ hx)
  | cons g gs ih =>
    cases k with
    | zero => simp at budget
    | succ k =>
      obtain ⟨op,len⟩ := hg g (.head _)
      obtain ⟨x,bx,m,h⟩ := opWitness hm hz ht g op len
      refine .tick bx m (ih (fun t => push (bs t) g) (x::ws) (N+1) k (pushModels hm hl bx h)
        (.tail _ hz) (.tail _ ht) ?_ (fun a ha => hg a (.tail _ ha)) (by simpa using budget) goal)
      intro t
      simp [push, hl t]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem exhaustive : safe table 3 (initial table) = true := by decide +kernel

def row : Fin 7 → Fin 5 := ![0,2,1,2,1,0,2]
def col : Fin 7 → Fin 5 := ![0,0,0,1,1,2,2]
def samples (t : Fin 7) := oneEach (row t) (col t)
theorem initialModels : Models (initial table).wires samples := by
  have small : ∀ i : Fin 10, ∃ v : Fin 128, v.val ∈ (initial table).wires ∧
      ∀ t : Fin 7, (samples t).getD i.val false = v.val.testBit t.val := by decide +kernel
  intro i
  by_cases hi : i < 10
  · obtain ⟨v,hv,he⟩ := small ⟨i,hi⟩
    exact ⟨v.val,hv,v.isLt,he⟩
  · refine ⟨0, by decide, by decide, fun t => ?_⟩
    have len : (samples t).length = 10 := by simp [samples, oneEach]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (samples t).length ≤ i by omega)]

theorem result : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 5 ∧ Represents (fun u v : Fin 5 => (3247678 : Nat).testBit (5 * u.val + v.val)) C := by
  rintro ⟨C, hC, bound, rep⟩
  apply safeSound initialGood exhaustive
  refine gatesRun C.gates samples _ C.output 10 5 initialModels (by decide) (by decide)
    (fun t => by simp [samples, oneEach]) ?_ bound ?_
  · intro g hg
    obtain ⟨op,len⟩ := hC g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, len⟩
  · have htab : ∀ t : Fin 7, (3247678 : Nat).testBit (5 * (row t).val + (col t).val) = (46 : Nat).testBit t.val := by decide
    intro t
    exact (rep (row t) (col t)).trans (htab t)
end PEqualNP.Outside.L_meta_19317


theorem PEqualNP.Outside.L_meta_19317 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247678 : ℕ).testBit (5 * u.val + v.val)) C := PEqualNP.Outside.L_meta_19317.result
