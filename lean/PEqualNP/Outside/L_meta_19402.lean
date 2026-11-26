import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19402_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def orChain (start first : ℕ) (rest : List ℕ) : List Gate :=
  rest.foldl
    (fun gs v => gs ++ [⟨GateOp.or, [if gs.length = 0 then first else start + gs.length - 1, v]⟩])
    []

/-- The wire at the end of `orChain start first rest`. -/
def chainOut (start first : ℕ) (rest : List ℕ) : ℕ :=
  if rest.length = 0 then first else start + rest.length - 1

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem orChain_snoc_aux (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++
      [⟨GateOp.or, [if (orChain s f r).length = 0 then f else s + (orChain s f r).length - 1, v]⟩] := by
  unfold orChain; rw [List.foldl_append]; rfl

theorem orChain_length (s f : ℕ) (r : List ℕ) : (orChain s f r).length = r.length := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r v ih => rw [orChain_snoc_aux]; simp [ih]

theorem orChain_snoc (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++ [⟨GateOp.or, [chainOut s f r, v]⟩] := by
  rw [orChain_snoc_aux, orChain_length]; rfl

theorem orChain_ops (s f : ℕ) (r : List ℕ) :
    ∀ g ∈ orChain s f r, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction r using List.reverseRecOn with
  | nil => intro g hg; simp [orChain] at hg
  | append_singleton r v ih =>
    intro g hg
    rw [orChain_snoc, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · exact ⟨rfl, rfl⟩

theorem chainOut_lt (s f : ℕ) (r : List ℕ) (hf : f < s) : chainOut s f r < s + r.length := by
  unfold chainOut; split <;> omega

theorem orChain_eval (s f : ℕ) (r : List ℕ) (w : List Bool) (hw : w.length = s) (hf : f < s)
    (hr : ∀ v ∈ r, v < s) :
    (run (orChain s f r) w).getD (chainOut s f r) false =
      (w.getD f false || r.any (fun v => w.getD v false)) := by
  induction r using List.reverseRecOn with
  | nil => simp [orChain, run_nil, chainOut]
  | append_singleton r v ih =>
    have hr' : ∀ u ∈ r, u < s := fun u hu => hr u (List.mem_append_left _ hu)
    have hv : v < s := hr v (by simp)
    rw [orChain_snoc, run_append, run_singleton]
    have hlen : (run (orChain s f r) w).length = s + r.length := by
      rw [run_length, orChain_length, hw]
    have hco : chainOut s f (r ++ [v]) = (run (orChain s f r) w).length := by
      rw [hlen]; simp [chainOut]
    rw [hco, getD_snoc_length]
    have hv' : (run (orChain s f r) w).getD v false = w.getD v false :=
      getD_run _ _ _ (by omega)
    simp only [List.map_cons, List.map_nil, eval_or2]
    rw [ih hr', hv', List.any_append]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]


theorem early (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem lastBit (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst i
  simp [List.getD_eq_getElem?_getD]

theorem leftBit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa), List.getElem?_eq_getElem (by simpa)]
  simp [Fin.ext_iff]

theorem rightBit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD (n+i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by simpa)]
  simp [Fin.ext_iff]

theorem lookup (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i = l.length then b else l.getD i false := by
  by_cases h : i < l.length
  · rw [early _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases e : i = l.length
    · simp [e]
    · have hs : 1 ≤ i-l.length := by omega
      rw [List.getElem?_eq_none (by simpa using hs), if_neg e, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]


def tail (s a b c x y z : ℕ) : List Gate := [
  ⟨.or,[y,z]⟩, ⟨.or,[x,b]⟩, ⟨.or,[b,s]⟩, ⟨.and,[a,s]⟩,
  ⟨.and,[1,s+1]⟩, ⟨.and,[c,s+2]⟩, ⟨.or,[s+3,s+4]⟩, ⟨.or,[s+6,s+5]⟩]

theorem tail_eval (s a b c x y z : ℕ) (w : List Bool) (hw : w.length = s)
    (hrow : 1 < s) (ha : a < s) (hb : b < s) (hc : c < s) (hx : x < s) (hy : y < s) (hz : z < s) :
    (run (tail s a b c x y z) w).getD (s+7) false =
      ((w.getD a false && (w.getD y false || w.getD z false)) ||
       (w.getD 1 false && (w.getD x false || w.getD b false)) || (w.getD c false && (w.getD b false || (w.getD y false || w.getD z false)))) := by
  simp only [tail, run, List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  have g0 : a ≠ s := by omega
  have g1 : a ≠ s+1 := by omega
  have g2 : a ≠ s+1+1 := by omega
  have g3 : a ≠ s+1+1+1 := by omega
  have g4 : a ≠ s+1+1+1+1 := by omega
  have g5 : a ≠ s+1+1+1+1+1 := by omega
  have g6 : a ≠ s+1+1+1+1+1+1 := by omega
  have g7 : a ≠ s+1+1+1+1+1+1+1 := by omega
  have g8 : b ≠ s := by omega
  have g9 : b ≠ s+1 := by omega
  have g10 : b ≠ s+1+1 := by omega
  have g11 : b ≠ s+1+1+1 := by omega
  have g12 : b ≠ s+1+1+1+1 := by omega
  have g13 : b ≠ s+1+1+1+1+1 := by omega
  have g14 : b ≠ s+1+1+1+1+1+1 := by omega
  have g15 : b ≠ s+1+1+1+1+1+1+1 := by omega
  have g16 : c ≠ s := by omega
  have g17 : c ≠ s+1 := by omega
  have g18 : c ≠ s+1+1 := by omega
  have g19 : c ≠ s+1+1+1 := by omega
  have g20 : c ≠ s+1+1+1+1 := by omega
  have g21 : c ≠ s+1+1+1+1+1 := by omega
  have g22 : c ≠ s+1+1+1+1+1+1 := by omega
  have g23 : c ≠ s+1+1+1+1+1+1+1 := by omega
  have g24 : x ≠ s := by omega
  have g25 : x ≠ s+1 := by omega
  have g26 : x ≠ s+1+1 := by omega
  have g27 : x ≠ s+1+1+1 := by omega
  have g28 : x ≠ s+1+1+1+1 := by omega
  have g29 : x ≠ s+1+1+1+1+1 := by omega
  have g30 : x ≠ s+1+1+1+1+1+1 := by omega
  have g31 : x ≠ s+1+1+1+1+1+1+1 := by omega
  have g32 : y ≠ s := by omega
  have g33 : y ≠ s+1 := by omega
  have g34 : y ≠ s+1+1 := by omega
  have g35 : y ≠ s+1+1+1 := by omega
  have g36 : y ≠ s+1+1+1+1 := by omega
  have g37 : y ≠ s+1+1+1+1+1 := by omega
  have g38 : y ≠ s+1+1+1+1+1+1 := by omega
  have g39 : y ≠ s+1+1+1+1+1+1+1 := by omega
  have g40 : z ≠ s := by omega
  have g41 : z ≠ s+1 := by omega
  have g42 : z ≠ s+1+1 := by omega
  have g43 : z ≠ s+1+1+1 := by omega
  have g44 : z ≠ s+1+1+1+1 := by omega
  have g45 : z ≠ s+1+1+1+1+1 := by omega
  have g46 : z ≠ s+1+1+1+1+1+1 := by omega
  have g47 : z ≠ s+1+1+1+1+1+1+1 := by omega
  have g48 : 1 ≠ s := by omega
  have g49 : 1 ≠ s+1 := by omega
  have g50 : 1 ≠ s+1+1 := by omega
  have g51 : 1 ≠ s+1+1+1 := by omega
  have g52 : 1 ≠ s+1+1+1+1 := by omega
  have g53 : 1 ≠ s+1+1+1+1+1 := by omega
  have g54 : 1 ≠ s+1+1+1+1+1+1 := by omega
  have g55 : 1 ≠ s+1+1+1+1+1+1+1 := by omega
  have g56 : s ≠ s+1 := by omega
  have g57 : s ≠ s+1+1 := by omega
  have g58 : s ≠ s+1+1+1 := by omega
  have g59 : s ≠ s+1+1+1+1 := by omega
  have g60 : s ≠ s+1+1+1+1+1 := by omega
  have g61 : s ≠ s+1+1+1+1+1+1 := by omega
  have g62 : s ≠ s+1+1+1+1+1+1+1 := by omega
  have g63 : s+1 ≠ s := by omega
  have g64 : s+1 ≠ s+1+1 := by omega
  have g65 : s+1 ≠ s+1+1+1 := by omega
  have g66 : s+1 ≠ s+1+1+1+1 := by omega
  have g67 : s+1 ≠ s+1+1+1+1+1 := by omega
  have g68 : s+1 ≠ s+1+1+1+1+1+1 := by omega
  have g69 : s+1 ≠ s+1+1+1+1+1+1+1 := by omega
  have g70 : s+2 ≠ s := by omega
  have g71 : s+2 ≠ s+1 := by omega
  have g72 : s+2 ≠ s+1+1+1 := by omega
  have g73 : s+2 ≠ s+1+1+1+1 := by omega
  have g74 : s+2 ≠ s+1+1+1+1+1 := by omega
  have g75 : s+2 ≠ s+1+1+1+1+1+1 := by omega
  have g76 : s+2 ≠ s+1+1+1+1+1+1+1 := by omega
  have g77 : s+3 ≠ s := by omega
  have g78 : s+3 ≠ s+1 := by omega
  have g79 : s+3 ≠ s+1+1 := by omega
  have g80 : s+3 ≠ s+1+1+1+1 := by omega
  have g81 : s+3 ≠ s+1+1+1+1+1 := by omega
  have g82 : s+3 ≠ s+1+1+1+1+1+1 := by omega
  have g83 : s+3 ≠ s+1+1+1+1+1+1+1 := by omega
  have g84 : s+4 ≠ s := by omega
  have g85 : s+4 ≠ s+1 := by omega
  have g86 : s+4 ≠ s+1+1 := by omega
  have g87 : s+4 ≠ s+1+1+1 := by omega
  have g88 : s+4 ≠ s+1+1+1+1+1 := by omega
  have g89 : s+4 ≠ s+1+1+1+1+1+1 := by omega
  have g90 : s+4 ≠ s+1+1+1+1+1+1+1 := by omega
  have g91 : s+5 ≠ s := by omega
  have g92 : s+5 ≠ s+1 := by omega
  have g93 : s+5 ≠ s+1+1 := by omega
  have g94 : s+5 ≠ s+1+1+1 := by omega
  have g95 : s+5 ≠ s+1+1+1+1 := by omega
  have g96 : s+5 ≠ s+1+1+1+1+1+1 := by omega
  have g97 : s+5 ≠ s+1+1+1+1+1+1+1 := by omega
  have g98 : s+6 ≠ s := by omega
  have g99 : s+6 ≠ s+1 := by omega
  have g100 : s+6 ≠ s+1+1 := by omega
  have g101 : s+6 ≠ s+1+1+1 := by omega
  have g102 : s+6 ≠ s+1+1+1+1 := by omega
  have g103 : s+6 ≠ s+1+1+1+1+1 := by omega
  have g104 : s+6 ≠ s+1+1+1+1+1+1+1 := by omega
  have g105 : s+7 ≠ s := by omega
  have g106 : s+7 ≠ s+1 := by omega
  have g107 : s+7 ≠ s+1+1 := by omega
  have g108 : s+7 ≠ s+1+1+1 := by omega
  have g109 : s+7 ≠ s+1+1+1+1 := by omega
  have g110 : s+7 ≠ s+1+1+1+1+1 := by omega
  have g111 : s+7 ≠ s+1+1+1+1+1+1 := by omega
  simp only [lookup,List.length_append,List.length_cons,List.length_nil,hw,Nat.reduceAdd,g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31,g32,g33,g34,g35,g36,g37,g38,g39,g40,g41,g42,g43,g44,g45,g46,g47,g48,g49,g50,g51,g52,g53,g54,g55,g56,g57,g58,g59,g60,g61,g62,g63,g64,g65,g66,g67,g68,g69,g70,g71,g72,g73,g74,g75,g76,g77,g78,g79,g80,g81,g82,g83,g84,g85,g86,g87,g88,g89,g90,g91,g92,g93,g94,g95,g96,g97,g98,g99,g100,g101,g102,g103,g104,g105,g106,g107,g108,g109,g110,g111,ite_true,ite_false,eq_self,Bool.or_false,Bool.and_true]

def rr (k : ℕ) := (List.range k).map (fun i => 3+i)
def cc (n k : ℕ) := (List.range k).map (fun i => n+(4+i))

theorem range_read (k t : ℕ) (f : ℕ → Bool) (hf : ∀ i, i ≤ k → f i = decide (i = t)) :
    (f 0 || (List.range k).any (fun j => f (1+j))) = decide (t ≤ k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  rw [hf 0 (by omega)]
  simp only [decide_eq_true_eq]
  constructor
  · rintro (h | ⟨j,hj,hf'⟩)
    · omega
    · rw [hf _ (by omega), decide_eq_true_eq] at hf'
      omega
  · intro ht
    cases t with
    | zero => exact Or.inl rfl
    | succ j =>
      right
      refine ⟨j, by omega, ?_⟩
      rw [hf _ (by omega)]
      simp +arith

def circ (n k : ℕ) : Circuit :=
  let s := n+n
  let t := s+(k+1)
  let p := t+k
  ⟨orChain s 2 (rr (k+1)) ++ orChain t (n+3) (cc n k) ++
    tail p 0 n (chainOut s 2 (rr (k+1))) (chainOut t (n+3) (cc n k)) (n+1) (n+2), p+7⟩

theorem mono (n k : ℕ) : Monotone2 (circ n k) := by
  intro g hg
  simp only [circ, List.mem_append] at hg
  rcases hg with (h|h)|h
  · obtain ⟨e,l⟩ := orChain_ops _ _ _ _ h
    simp [e,l]
  · obtain ⟨e,l⟩ := orChain_ops _ _ _ _ h
    simp [e,l]
  · simp [tail] at h
    rcases h with h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem correct (n k : ℕ) (hn : n = k+4) (u v : Fin n) :
    (circ n k).eval (oneEach u v) = decide ((u.val = 0 ∧ (v.val=1 ∨ v.val=2)) ∨
      (u.val=1 ∧ ¬ (v.val=1 ∨ v.val=2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2)) := by
  let w := oneEach u v
  let s := n+n
  let t := s+(k+1)
  let p := t+k
  let l := orChain s 2 (rr (k+1))
  let r := orChain t (n+3) (cc n k)
  let w1 := run l w
  let w2 := run r w1
  let left := chainOut s 2 (rr (k+1))
  let right := chainOut t (n+3) (cc n k)
  have h0 : w.length = s := by simp [w, oneEach, s]
  have h1 : w1.length = t := by simp [w1,l,run_length,orChain_length,rr,h0,t]
  have h2 : w2.length = p := by simp [w2,r,run_length,orChain_length,cc,h1,p]
  have hl : left < t := by simpa [left,t,rr] using chainOut_lt s 2 (rr (k+1)) (by dsimp [s]; omega)
  have hr : right < p := by simpa [right,p,cc] using chainOut_lt t (n+3) (cc n k) (by dsimp [t,s]; omega)
  have old1 (i : ℕ) (hi : i < s) : w1.getD i false = w.getD i false := getD_run _ _ _ (by omega)
  have old2 (i : ℕ) (hi : i < t) : w2.getD i false = w1.getD i false := getD_run _ _ _ (by omega)
  have old (i : ℕ) (hi : i < s) : w2.getD i false = w.getD i false := (old2 i (by dsimp [t]; omega)).trans (old1 i hi)
  have readL : w2.getD left false = decide (2 ≤ u.val) := by
    rw [old2 _ hl]
    change (run (orChain s 2 (rr (k+1))) w).getD (chainOut s 2 (rr (k+1))) false = _
    rw [orChain_eval _ _ _ _ h0 (by dsimp [s]; omega) (by intro q hq; simp [rr] at hq; obtain ⟨i,hi,rfl⟩ := hq; dsimp [s]; omega)]
    simp only [rr, List.any_map, Function.comp_def]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
    rw [leftBit u v 2 (by omega), decide_eq_true_eq]
    constructor
    · rintro (e|⟨i,hi,e⟩)
      · omega
      · rw [leftBit u v _ (by omega), decide_eq_true_eq] at e
        omega
    · intro hu
      by_cases h : u.val = 2
      · exact Or.inl h.symm
      · refine Or.inr ⟨u.val-3, by omega, ?_⟩
        rw [leftBit u v _ (by omega), decide_eq_true_eq]
        omega
  have readR : w2.getD right false = decide (3 ≤ v.val) := by
    change (run (orChain t (n+3) (cc n k)) w1).getD (chainOut t (n+3) (cc n k)) false = _
    rw [orChain_eval _ _ _ _ h1 (by dsimp [t,s]; omega) (by intro q hq; simp [cc] at hq; obtain ⟨i,hi,rfl⟩ := hq; dsimp [t,s]; omega)]
    simp only [cc,List.any_map,Function.comp_def]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
    rw [old1 _ (by dsimp [s]; omega), rightBit u v 3 (by omega), decide_eq_true_eq]
    constructor
    · rintro (e|⟨i,hi,e⟩)
      · omega
      · rw [old1 _ (by dsimp [s]; omega), rightBit u v _ (by omega), decide_eq_true_eq] at e
        omega
    · intro hv
      by_cases h : v.val = 3
      · exact Or.inl h.symm
      · refine Or.inr ⟨v.val-4, by omega, ?_⟩
        rw [old1 _ (by dsimp [s]; omega), rightBit u v _ (by omega), decide_eq_true_eq]
        omega
  change (run ((l ++ r) ++ _) w).getD (p+7) false = _
  rw [run_append,run_append]
  change (run (tail p 0 n left right (n+1) (n+2)) w2).getD (p+7) false = _
  rw [tail_eval _ _ _ _ _ _ _ _ h2 (by dsimp [p,t,s]; omega) (by dsimp [p,t,s]; omega) (by dsimp [p,t,s]; omega)
    (by dsimp [p]; omega) hr (by dsimp [p,t,s]; omega) (by dsimp [p,t,s]; omega),
    readL,readR,old 0 (by dsimp [s]; omega),old 1 (by dsimp [s]; omega),
    old n (by dsimp [s]; omega),old (n+1) (by dsimp [s]; omega),old (n+2) (by dsimp [s]; omega),
    leftBit u v 0 (by omega),leftBit u v 1 (by omega),
    rightBit u v 1 (by omega),rightBit u v 2 (by omega)]
  have rz : w.getD n false = decide (0 = v.val) := by simpa [w] using rightBit u v 0 (by omega)
  rw [rz]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  omega

end PEqualNP.Outside.L_meta_19402_aux
open PEqualNP.Outside.L_meta_19402_aux
theorem PEqualNP.Outside.L_meta_19402 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) (2 * n + 1) := by
  intro n hn
  refine ⟨circ n (n-4), mono _ _, ?_, correct _ _ (by omega)⟩
  simp [PEqualNP.CircuitLowerBounds.Circuit.size,circ,tail,orChain_length,rr,cc]
  omega

