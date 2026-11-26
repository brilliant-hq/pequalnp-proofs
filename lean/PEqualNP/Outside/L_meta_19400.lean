import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19400_aux

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
  ⟨.or,[y,z]⟩, ⟨.or,[x,y]⟩, ⟨.and,[a,s]⟩,
  ⟨.and,[b,x]⟩, ⟨.and,[c,s+1]⟩, ⟨.or,[s+2,s+3]⟩, ⟨.or,[s+5,s+4]⟩]

theorem tail_eval (s a b c x y z : ℕ) (w : List Bool) (hw : w.length = s)
    (ha : a < s) (hb : b < s) (hc : c < s) (hx : x < s) (hy : y < s) (hz : z < s) :
    (run (tail s a b c x y z) w).getD (s+6) false =
      ((w.getD a false && (w.getD y false || w.getD z false)) ||
       (w.getD b false && w.getD x false) || (w.getD c false && (w.getD x false || w.getD y false))) := by
  simp only [tail, run, List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  have h0 : a ≠ s := by omega
  have h1 : a ≠ s+1 := by omega
  have h2 : a ≠ s+1+1 := by omega
  have h3 : a ≠ s+1+1+1 := by omega
  have h4 : a ≠ s+1+1+1+1 := by omega
  have h5 : a ≠ s+1+1+1+1+1 := by omega
  have h6 : a ≠ s+1+1+1+1+1+1 := by omega
  have h7 : b ≠ s := by omega
  have h8 : b ≠ s+1 := by omega
  have h9 : b ≠ s+1+1 := by omega
  have h10 : b ≠ s+1+1+1 := by omega
  have h11 : b ≠ s+1+1+1+1 := by omega
  have h12 : b ≠ s+1+1+1+1+1 := by omega
  have h13 : b ≠ s+1+1+1+1+1+1 := by omega
  have h14 : c ≠ s := by omega
  have h15 : c ≠ s+1 := by omega
  have h16 : c ≠ s+1+1 := by omega
  have h17 : c ≠ s+1+1+1 := by omega
  have h18 : c ≠ s+1+1+1+1 := by omega
  have h19 : c ≠ s+1+1+1+1+1 := by omega
  have h20 : c ≠ s+1+1+1+1+1+1 := by omega
  have h21 : x ≠ s := by omega
  have h22 : x ≠ s+1 := by omega
  have h23 : x ≠ s+1+1 := by omega
  have h24 : x ≠ s+1+1+1 := by omega
  have h25 : x ≠ s+1+1+1+1 := by omega
  have h26 : x ≠ s+1+1+1+1+1 := by omega
  have h27 : x ≠ s+1+1+1+1+1+1 := by omega
  have h28 : y ≠ s := by omega
  have h29 : y ≠ s+1 := by omega
  have h30 : y ≠ s+1+1 := by omega
  have h31 : y ≠ s+1+1+1 := by omega
  have h32 : y ≠ s+1+1+1+1 := by omega
  have h33 : y ≠ s+1+1+1+1+1 := by omega
  have h34 : y ≠ s+1+1+1+1+1+1 := by omega
  have h35 : z ≠ s := by omega
  have h36 : z ≠ s+1 := by omega
  have h37 : z ≠ s+1+1 := by omega
  have h38 : z ≠ s+1+1+1 := by omega
  have h39 : z ≠ s+1+1+1+1 := by omega
  have h40 : z ≠ s+1+1+1+1+1 := by omega
  have h41 : z ≠ s+1+1+1+1+1+1 := by omega
  have h42 : s ≠ s+1 := by omega
  have h43 : s ≠ s+1+1 := by omega
  have h44 : s ≠ s+1+1+1 := by omega
  have h45 : s ≠ s+1+1+1+1 := by omega
  have h46 : s ≠ s+1+1+1+1+1 := by omega
  have h47 : s ≠ s+1+1+1+1+1+1 := by omega
  have h48 : s+1 ≠ s := by omega
  have h49 : s+1 ≠ s+1+1 := by omega
  have h50 : s+1 ≠ s+1+1+1 := by omega
  have h51 : s+1 ≠ s+1+1+1+1 := by omega
  have h52 : s+1 ≠ s+1+1+1+1+1 := by omega
  have h53 : s+1 ≠ s+1+1+1+1+1+1 := by omega
  have h54 : s+2 ≠ s := by omega
  have h55 : s+2 ≠ s+1 := by omega
  have h56 : s+2 ≠ s+1+1+1 := by omega
  have h57 : s+2 ≠ s+1+1+1+1 := by omega
  have h58 : s+2 ≠ s+1+1+1+1+1 := by omega
  have h59 : s+2 ≠ s+1+1+1+1+1+1 := by omega
  have h60 : s+3 ≠ s := by omega
  have h61 : s+3 ≠ s+1 := by omega
  have h62 : s+3 ≠ s+1+1 := by omega
  have h63 : s+3 ≠ s+1+1+1+1 := by omega
  have h64 : s+3 ≠ s+1+1+1+1+1 := by omega
  have h65 : s+3 ≠ s+1+1+1+1+1+1 := by omega
  have h66 : s+4 ≠ s := by omega
  have h67 : s+4 ≠ s+1 := by omega
  have h68 : s+4 ≠ s+1+1 := by omega
  have h69 : s+4 ≠ s+1+1+1 := by omega
  have h70 : s+4 ≠ s+1+1+1+1+1 := by omega
  have h71 : s+4 ≠ s+1+1+1+1+1+1 := by omega
  have h72 : s+5 ≠ s := by omega
  have h73 : s+5 ≠ s+1 := by omega
  have h74 : s+5 ≠ s+1+1 := by omega
  have h75 : s+5 ≠ s+1+1+1 := by omega
  have h76 : s+5 ≠ s+1+1+1+1 := by omega
  have h77 : s+5 ≠ s+1+1+1+1+1+1 := by omega
  have h78 : s+6 ≠ s := by omega
  have h79 : s+6 ≠ s+1 := by omega
  have h80 : s+6 ≠ s+1+1 := by omega
  have h81 : s+6 ≠ s+1+1+1 := by omega
  have h82 : s+6 ≠ s+1+1+1+1 := by omega
  have h83 : s+6 ≠ s+1+1+1+1+1 := by omega
  simp only [lookup, List.length_append, List.length_cons, List.length_nil, hw, Nat.reduceAdd, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, ite_true, ite_false, eq_self, Bool.or_false, Bool.and_true]

def rr (k : ℕ) := (List.range k).map (fun i => 3+i)
def cc (n k : ℕ) := (List.range k).map (fun i => n+(1+i))

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
  let t := s+k
  let p := t+k
  ⟨orChain s 2 (rr k) ++ orChain t n (cc n k) ++
    tail p 0 1 (chainOut s 2 (rr k)) (chainOut t n (cc n k)) (n+(n-2)) (n+(n-1)), p+6⟩

theorem mono (n k : ℕ) : Monotone2 (circ n k) := by
  intro g hg
  simp only [circ, List.mem_append] at hg
  rcases hg with (h|h)|h
  · obtain ⟨e,l⟩ := orChain_ops _ _ _ _ h
    simp [e,l]
  · obtain ⟨e,l⟩ := orChain_ops _ _ _ _ h
    simp [e,l]
  · simp [tail] at h
    rcases h with h|h|h|h|h|h|h <;> subst g <;> simp

theorem correct (n k : ℕ) (hn : n = k+3) (u v : Fin n) :
    (circ n k).eval (oneEach u v) = decide ((u.val = 0 ∧ (v.val+1=n ∨ v.val+2=n)) ∨
      (u.val=1 ∧ ¬ (v.val+1=n ∨ v.val+2=n)) ∨ (2 ≤ u.val ∧ v.val+1 ≠ n)) := by
  let w := oneEach u v
  let s := n+n
  let t := s+k
  let p := t+k
  let l := orChain s 2 (rr k)
  let r := orChain t n (cc n k)
  let w1 := run l w
  let w2 := run r w1
  let left := chainOut s 2 (rr k)
  let right := chainOut t n (cc n k)
  have h0 : w.length = s := by simp [w, oneEach, s]
  have h1 : w1.length = t := by simp [w1,l,run_length,orChain_length,rr,h0,t]
  have h2 : w2.length = p := by simp [w2,r,run_length,orChain_length,cc,h1,p]
  have hl : left < t := by simpa [left,t,rr] using chainOut_lt s 2 (rr k) (by dsimp [s]; omega)
  have hr : right < p := by simpa [right,p,cc] using chainOut_lt t n (cc n k) (by dsimp [t,s]; omega)
  have old1 (i : ℕ) (hi : i < s) : w1.getD i false = w.getD i false := getD_run _ _ _ (by omega)
  have old2 (i : ℕ) (hi : i < t) : w2.getD i false = w1.getD i false := getD_run _ _ _ (by omega)
  have old (i : ℕ) (hi : i < s) : w2.getD i false = w.getD i false := (old2 i (by dsimp [t]; omega)).trans (old1 i hi)
  have readL : w2.getD left false = decide (2 ≤ u.val) := by
    rw [old2 _ hl]
    change (run (orChain s 2 (rr k)) w).getD (chainOut s 2 (rr k)) false = _
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
  have readR : w2.getD right false = decide (v.val ≤ k) := by
    change (run (orChain t n (cc n k)) w1).getD (chainOut t n (cc n k)) false = _
    rw [orChain_eval _ _ _ _ h1 (by dsimp [t,s]; omega) (by intro q hq; simp [cc] at hq; obtain ⟨i,hi,rfl⟩ := hq; dsimp [t,s]; omega)]
    simp only [cc,List.any_map,Function.comp_def]
    have hh := range_read k v.val (fun i => w1.getD (n+i) false) (by
      intro i hi
      rw [old1 _ (by dsimp [s]; omega)]
      exact rightBit u v _ (by omega))
    simpa using hh
  change (run ((l ++ r) ++ _) w).getD (p+6) false = _
  rw [run_append,run_append]
  change (run (tail p 0 1 left right (n+(n-2)) (n+(n-1))) w2).getD (p+6) false = _
  rw [tail_eval _ _ _ _ _ _ _ _ h2 (by dsimp [p,t,s]; omega) (by dsimp [p,t,s]; omega)
    (by dsimp [p]; omega) hr (by dsimp [p,t,s]; omega) (by dsimp [p,t,s]; omega),
    readL,readR,old 0 (by dsimp [s]; omega),old 1 (by dsimp [s]; omega),
    old (n+(n-2)) (by dsimp [s]; omega),old (n+(n-1)) (by dsimp [s]; omega),
    leftBit u v 0 (by omega),leftBit u v 1 (by omega),
    rightBit u v (n-2) (by omega),rightBit u v (n-1) (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  omega

end PEqualNP.Outside.L_meta_19400_aux
open PEqualNP.Outside.L_meta_19400_aux
theorem PEqualNP.Outside.L_meta_19400 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (u.val = 1 ∧ ¬ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (2 ≤ u.val ∧ v.val + 1 ≠ n))) (2 * n + 1) := by
  intro n hn
  refine ⟨circ n (n-3), mono _ _, ?_, correct _ _ (by omega)⟩
  simp [PEqualNP.CircuitLowerBounds.Circuit.size,circ,tail,orChain_length,rr,cc]
  omega
