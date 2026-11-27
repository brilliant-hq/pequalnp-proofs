import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25605

def mix (x : Int → Bool) (z : Int) : Bool :=
  xor (xor (x (z-1)) (x z)) (x (z+1))

def evolve (x inj : Int → Bool) (z : Int) : Bool :=
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)

def pack (width : Nat) (bits : Nat → Bool) : Nat :=
  (List.range width).foldl (fun acc idx => acc ||| ((bits idx).toNat <<< idx)) 0

def block (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  pack width (fun i => tape (edge+1+(i : Int)))

def fits (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) : Prop :=
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true

def tails (w mask : Nat) : List Nat :=
  (List.range (2 ^ (2*w+5))).filter (fun pattern => mask.testBit (pattern % 2^w))

def trial (b : Int) (x : Int → Bool) (code : Nat) (site : Int) : Bool :=
  if site ≤ b then x site else code.testBit (site-b-1).toNat

def fixed (w : Nat) (b : Int) (x inj : Int → Bool) (mask offset : Nat) : Bool :=
  let site := b-2+(offset : Int)
  (tails w mask).all (fun code => evolve (trial b x code) inj site == evolve x inj site)

def advance (w : Nat) (b : Int) (x inj : Int → Bool) (mask : Nat) : Int × Nat :=
  let f := b-3+(((List.range (w+5)).takeWhile (fixed w b x inj mask)).length : Int)
  (f, (tails w mask).foldl (fun acc code =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial b x code) inj) f)) 0)

theorem oneBit (bit : Bool) (i j : Nat) :
    (bit.toNat <<< i).testBit j = (decide (i = j) && bit) := by
  cases bit <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem pack_bit (bits : Nat → Bool) (width j : Nat) :
    (pack width bits).testBit j = (decide (j < width) && bits j) := by
  induction width with
  | zero => simp [pack]
  | succ w ih =>
    have step : pack (w+1) bits = pack w bits ||| ((bits w).toNat <<< w) := by
      simp [pack, List.range_succ, List.foldl_append]
    rw [step, Nat.testBit_lor, oneBit, ih]
    by_cases e : w = j
    · subst j
      simp
    · have split : j < w + 1 ↔ j < w := by omega
      simp [split,e]

theorem pack_lt (bits : Nat → Bool) (w : Nat) : pack w bits < 2^w := by
  by_contra! ge
  obtain ⟨j, hj, set⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow ge
  rw [pack_bit] at set
  simp [Nat.not_lt_of_ge hj] at set

theorem pack_mod (bits : Nat → Bool) {w n : Nat} (h : w ≤ n) :
    pack n bits % 2^w = pack w bits := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · simp [Nat.testBit_mod_two_pow, pack_bit, hj, show j < n from by omega]
  · simp [Nat.testBit_mod_two_pow, pack_bit, hj]

theorem block_trial {w : Nat} {b : Int} (x : Int → Bool) (code : Nat) :
    block w (trial b x code) b = code % 2^w := by
  apply Nat.eq_of_testBit_eq
  intro j
  have gt : ¬ b+1+(j : Int) ≤ b := by omega
  have index : (b+1+(j : Int)-b-1).toNat = j := by omega
  simp only [block, pack_bit, trial, ite_eq_right gt, index, Nat.testBit_mod_two_pow]

theorem block_eq {w : Nat} {b : Int} {x y : Int → Bool}
    (h : ∀ j < w, x (b+1+(j : Int)) = y (b+1+(j : Int))) :
    block w x b = block w y b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w <;> simp [block, pack_bit, hj, h j]

theorem block_congr {w : Nat} {b : Int} {x y : Int → Bool}
    (h : ∀ z, b+1 ≤ z → z ≤ b+(w : Int) → x z = y z) : block w x b = block w y b :=
  block_eq (fun j hj => h _ (by omega) (by omega))

theorem evolve_agree {x y : Int → Bool} (inj : Int → Bool) (z : Int)
    (same : ∀ j, z-1 ≤ j → j ≤ z+3 → x j = y j) :
    evolve x inj z = evolve y inj z := by
  have mixes (s : Int) (lo : z ≤ s) (hi : s ≤ z+2) : mix x s = mix y s := by
    simp [mix, same (s-1) (by omega) (by omega), same s (by omega) (by omega),
      same (s+1) (by omega) (by omega)]
  simp [evolve, mixes z (by omega) (by omega), mixes (z+1) (by omega) (by omega),
    mixes (z+2) (by omega) (by omega)]

theorem trial_fits {w mask code : Nat} {b : Int} {x : Int → Bool}
    (h : code ∈ tails w mask) : fits w b x mask (trial b x code) := by
  refine ⟨fun z hz => ite_eq_left hz, ?_⟩
  rw [block_trial]
  exact (List.mem_filter.mp h).2

theorem fit_code {w mask : Nat} {b : Int} {x t : Int → Bool} (h : fits w b x mask t) :
    ∃ code ∈ tails w mask, ∀ z ≤ b+(2*w+5 : Nat), trial b x code z = t z := by
  let code := block (2*w+5) t b
  refine ⟨code, ?_, ?_⟩
  · apply List.mem_filter.mpr
    have mod : code % 2^w = block w t b := pack_mod _ (by omega)
    exact ⟨List.mem_range.mpr (pack_lt _ _), mod.symm ▸ h.2⟩
  · intro z hz
    by_cases le : z ≤ b
    · simp [trial,le,h.1 z le]
    · let j := (z-b-1).toNat
      have jl : j < 2*w+5 := by dsimp [j]; omega
      have same : b+1+(j : Int) = z := by dsimp [j]; omega
      simp only [trial, ite_eq_right le]
      change (pack (2*w+5) (fun k => t (b+1+(k : Int)))).testBit j = t z
      rw [pack_bit, same]
      simp [jl]

theorem folds_bit (codes : List Nat) (key : Nat → Nat) (value acc : Nat) :
    ((codes.foldl (fun a c => a ||| ((1 : Nat) <<< key c)) acc).testBit value = true) ↔
      acc.testBit value = true ∨ ∃ c ∈ codes, key c = value := by
  induction codes generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    aesop

theorem prefixRange (ok : Nat → Bool) (n : Nat) :
    let l := ((List.range n).takeWhile ok).length
    l ≤ n ∧ (∀ j < l, ok j = true) ∧ (l < n → ok l = false) := by
  dsimp only
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ]
    by_cases all : ∀ j < n, ok j = true
    · have okRange : ∀ j ∈ List.range n, ok j = true := fun j hj => all j (List.mem_range.mp hj)
      rw [List.takeWhile_append_of_pos okRange]
      cases hn : ok n
      · have drop : List.takeWhile ok [n] = [] := by simp [List.takeWhile, hn]
        rw [drop, List.append_nil, List.length_range]
        exact ⟨Nat.le_succ n, all, fun _ => hn⟩
      · have take : List.takeWhile ok [n] = [n] := by simp [List.takeWhile, hn]
        rw [take, List.length_append, List.length_range]
        change n+1 ≤ n+1 ∧ (∀ j < n+1, ok j = true) ∧ (n+1 < n+1 → ok (n+1) = false)
        refine ⟨le_rfl, fun j hj => ?_, by omega⟩
        by_cases eql : j = n
        · simpa only [eql] using hn
        · exact all j (by omega)
    · obtain ⟨le,lt,bad⟩ := ih
      have short : ((List.range n).takeWhile ok).length < n := by
        refine lt_of_le_of_ne le (fun eq => all (fun j hj => lt j ?_))
        rwa [eq]
      rw [List.takeWhile_append, List.length_range, ite_eq_right (ne_of_lt short)]
      exact ⟨Nat.le.step le, lt, fun _ => bad short⟩


theorem fixed_iff {w mask off : Nat} {b : Int} {x inj : Int → Bool} (ho : off < w+5) :
    fixed w b x inj mask off = true ↔
      ∀ t : Int → Bool, fits w b x mask t →
        evolve t inj (b-2+(off : Int)) = evolve x inj (b-2+(off : Int)) := by
  simp only [fixed, List.all_eq_true, beq_iff_eq]
  refine ⟨?_, fun h c hc => h _ (trial_fits hc)⟩
  intro h t ht
  obtain ⟨c, hc, agree⟩ := fit_code ht
  rw [← evolve_agree inj _ (fun z _ hi => agree z (by omega))]
  exact h c hc

theorem unrestricted_right {w mask : Nat} {b : Int} {x : Int → Bool}
    (hx : mask.testBit (block w x b) = true) (inj : Int → Bool) (z : Int)
    (hz : b+(w : Int)+1 < z) :
    ∃ t : Int → Bool, fits w b x mask t ∧ evolve t inj z ≠ evolve x inj z := by
  let flip := !(xor (evolve x inj z) (inj z))
  let t : Int → Bool := fun j => if j ≤ b+(w : Int) then x j else
    if j = z+3 then flip else false
  have small (j : Int) (h : j ≤ b+(w : Int)) : t j = x j := ite_eq_left h
  have large (j : Int) (h : b+(w : Int) < j) (ne : j ≠ z+3) : t j = false := by
    simp [t, not_le.mpr h, ne]
  have last : t (z+3) = flip := by simp [t, show ¬ z+3 ≤ b+(w : Int) by omega]
  have a : mix t z = false := by
    simp [mix, large (z-1) (by omega) (by omega), large z (by omega) (by omega),
      large (z+1) (by omega) (by omega)]
  have c : mix t (z+1) = false := by
    simp [mix, large z (by omega) (by omega), large (z+1) (by omega) (by omega),
      large (z+1+1) (by omega) (by omega)]
  have d : mix t (z+2) = flip := by
    rw [mix, show z+2-1 = z+1 by omega, show z+2+1 = z+3 by omega,
      large (z+1) (by omega) (by omega), large (z+2) (by omega) (by omega), last]
    simp
  refine ⟨t, ⟨fun j hj => small j (by omega), ?_⟩, ?_⟩
  · rwa [block_congr (fun j _ hi => small j hi)]
  · simp only [evolve, a, c, d, Bool.not_false, Bool.true_and, Bool.false_xor]
    change xor (!(xor (evolve x inj z) (inj z))) (inj z) ≠ evolve x inj z
    cases evolve x inj z <;> cases inj z <;> decide

theorem exact_advance (w : Nat) (b : Int) (x inj : Int → Bool) (mask : Nat)
    (hx : mask.testBit (block w x b) = true) :
    let next := advance w b x inj mask
    let f := next.1
    b-3 ≤ f ∧ f ≤ b+(w : Int)+1 ∧
      (∀ t : Int → Bool, fits w b x mask t → ∀ j ≤ f, evolve t inj j = evolve x inj j) ∧
      (∃ t : Int → Bool, fits w b x mask t ∧ evolve t inj (f+1) ≠ evolve x inj (f+1)) ∧
      (∀ value : Fin (2^w), next.2.testBit value.val = true ↔
        ∃ t : Int → Bool, fits w b x mask t ∧ block w (evolve t inj) f = value.val) := by
  let l := ((List.range (w+5)).takeWhile (fixed w b x inj mask)).length
  let f := b-3+(l : Int)
  have pr : l ≤ w+5 ∧ (∀ j < l, fixed w b x inj mask j = true) ∧
      (l < w+5 → fixed w b x inj mask l = false) := prefixRange _ _
  have short : l < w+5 := by
    by_contra! ge
    have holds := pr.2.1 (w+4) (by omega)
    let z := b-2+((w+4 : Nat) : Int)
    obtain ⟨t, ht, diff⟩ := unrestricted_right hx inj z (by dsimp [z]; omega)
    exact diff ((fixed_iff (show w+4 < w+5 by omega)).mp holds t ht)
  have lo : b-3 ≤ f := by dsimp [f]; omega
  have hi : f ≤ b+(w : Int)+1 := by dsimp [f]; omega
  change b-3 ≤ f ∧ f ≤ b+(w : Int)+1 ∧
    (∀ t : Int → Bool, fits w b x mask t → ∀ j ≤ f, evolve t inj j = evolve x inj j) ∧
    (∃ t : Int → Bool, fits w b x mask t ∧ evolve t inj (f+1) ≠ evolve x inj (f+1)) ∧ _
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · intro t ht j hj
    by_cases left : j ≤ b-3
    · exact evolve_agree inj j (fun z _ hz => ht.1 z (by omega))
    · let off := (j-(b-2)).toNat
      have below : off < l := by dsimp [off]; dsimp [f] at hj; omega
      have index : b-2+(off : Int) = j := by dsimp [off]; omega
      simpa only [index] using (fixed_iff (show off < w+5 by omega)).mp
        (pr.2.1 off below) t ht
  · by_contra! all
    have eq : fixed w b x inj mask l = true :=
      (fixed_iff short).mpr (fun t ht => by
        have index : b-2+(l : Int) = f+1 := by dsimp [f]; omega
        simpa only [index] using all t ht)
    rw [pr.2.2 short] at eq
    contradiction
  · intro value
    change ((tails w mask).foldl (fun acc code =>
      acc ||| ((1 : Nat) <<< block w (evolve (trial b x code) inj) f)) 0).testBit value.val = true ↔ _
    rw [folds_bit]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨code, hc, eq⟩
      exact ⟨trial b x code, trial_fits hc, eq⟩
    · rintro ⟨t, ht, eq⟩
      obtain ⟨code, hc, agree⟩ := fit_code ht
      refine ⟨code, hc, ?_⟩
      rw [← eq]
      apply block_congr
      intro z _ hz
      exact evolve_agree inj z (fun loc _ upper => agree loc (by omega))

theorem block_bit_eq {w : Nat} {b : Int} {x y : Int → Bool}
    (eq : block w x b = block w y b) (z : Int) (lo : b+1 ≤ z) (hi : z ≤ b+(w : Int)) :
    x z = y z := by
  let j := (z-b-1).toNat
  have jl : j < w := by dsimp [j]; omega
  have index : b+1+(j : Int) = z := by dsimp [j]; omega
  have h := congrArg (fun code => Nat.testBit code j) eq
  change (pack w (fun k => x (b+1+(k : Int)))).testBit j =
    (pack w (fun k => y (b+1+(k : Int)))).testBit j at h
  simpa only [pack_bit, decide_eq_true_eq.mpr jl, Bool.true_and, index] using h

abbrev BoxState := (Int → Bool) × Int × Nat

def members (w : Nat) (st : BoxState) (y : Int → Bool) : Prop :=
  fits w st.2.1 st.1 st.2.2 y

def advanceState (w : Nat) (inj : Int → Bool) (st : BoxState) : BoxState :=
  let delta := advance w st.2.1 st.1 inj st.2.2
  (evolve st.1 inj, delta.1, delta.2)

theorem step_sound (w : Nat) (st : BoxState) (inj : Int → Bool)
    (valid : members w st st.1) :
    ∀ t, members w st t → members w (advanceState w inj st) (evolve t inj) := by
  rcases st with ⟨x,b,mask⟩
  obtain ⟨_, _, same, _, image⟩ := exact_advance w b x inj mask valid.2
  intro t ht
  let f := (advance w b x inj mask).1
  let value : Fin (2^w) := ⟨block w (evolve t inj) f, pack_lt _ _⟩
  refine ⟨same t ht, ?_⟩
  exact (image value).mpr ⟨t, ht, rfl⟩

def reached (w n : Nat) (init : BoxState) (injections : Nat → Int → Bool) : BoxState :=
  (List.range n).foldl (fun state tick => advanceState w (injections tick) state) init

theorem reached_succ (w n : Nat) (init : BoxState) (injections : Nat → Int → Bool) :
    reached w (n+1) init injections = advanceState w (injections n) (reached w n init injections) := by
  simp [reached, List.range_succ, List.foldl_append]

theorem reached_valid (w n : Nat) (init : BoxState) (injections : Nat → Int → Bool)
    (valid : members w init init.1) :
    members w (reached w n init injections) (reached w n init injections).1 := by
  induction n with
  | zero => exact valid
  | succ n ih =>
    rw [reached_succ]
    exact step_sound w _ _ ih _ ih


def run (inj : Nat → Int → Bool) (n : Nat) (x : Int → Bool) : Int → Bool :=
  (List.range n).foldl (fun st tick => evolve st (inj tick)) x

theorem run_succ (inj : Nat → Int → Bool) (n : Nat) (x : Int → Bool) :
    run inj (n+1) x = evolve (run inj n x) (inj n) := by
  simp [run, List.range_succ, List.foldl_append]

theorem run_prefix (inj : Nat → Int → Bool) (n : Nat) {x y : Int → Bool} (b : Int)
    (same : ∀ z ≤ b, x z = y z) :
    ∀ z ≤ b-3*(n : Int), run inj n x z = run inj n y z := by
  induction n with
  | zero => simpa [run] using same
  | succ n ih =>
    rw [run_succ,run_succ]
    intro z hz
    exact evolve_agree (inj n) z (fun j _ h => ih j (by omega))

def separatesAt (x y : Int → Bool) (z : Int) : Prop :=
  x z ≠ y z ∧ ∀ j > z, x j = y j

theorem separates_step {x y : Int → Bool} {b : Int} (inj : Int → Bool)
    (h : separatesAt x y b) : separatesAt (evolve x inj) (evolve y inj) (b+1) := by
  refine ⟨?_, fun z hz => evolve_agree inj z (fun j lo _ => h.2 j (by omega))⟩
  have mixEq (z : Int) (hz : b+2 ≤ z) : mix x z = mix y z := by
    simp [mix, h.2 (z-1) (by omega), h.2 z (by omega), h.2 (z+1) (by omega)]
  have diff := h.1
  have eq1 := h.2 (b+1) (by omega)
  have eq2 := h.2 (b+1+1) (by omega)
  have centerX : mix x (b+1) = xor (xor (x b) (y (b+1))) (y (b+1+1)) := by
    simp only [mix, show b+1-1 = b by omega, eq1, eq2]
  have centerY : mix y (b+1) = xor (xor (y b) (y (b+1))) (y (b+1+1)) := by
    simp only [mix, show b+1-1 = b by omega]
  simp only [evolve]
  rw [mixEq (b+1+1) (by omega), mixEq (b+1+2) (by omega), centerX, centerY]
  revert diff
  generalize x b = a
  generalize y b = c
  generalize y (b+1) = d
  generalize y (b+1+1) = e
  generalize (!(mix y (b+1+1)) && mix y (b+1+2)) = f
  generalize inj (b+1) = g
  intro ne
  cases a <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> simp_all

theorem separates_run (inj : Nat → Int → Bool) (n : Nat) {x y : Int → Bool} {b : Int}
    (h : separatesAt x y b) : separatesAt (run inj n x) (run inj n y) (b+(n : Int)) := by
  induction n with
  | zero => simpa [run] using h
  | succ n ih =>
    rw [run_succ,run_succ, show b+((n+1 : Nat) : Int) = b+(n : Int)+1 by omega]
    exact separates_step (inj n) ih

def edgeOf (A : (Int → Bool) → Prop) (f : (Int → Bool) → Int → Bool)
    (reference : Int → Bool) (b : Int) : Prop :=
  (∀ seed, A seed → ∀ z ≤ b, f seed z = reference z) ∧
  ∃ seed, A seed ∧ f seed (b+1) ≠ reference (b+1)

theorem edge_compare {A : (Int → Bool) → Prop} {f : (Int → Bool) → Int → Bool}
    {ref : Int → Bool} {a b : Int}
    (same : ∀ seed, A seed → ∀ z ≤ a, f seed z = ref z)
    (diff : ∃ seed, A seed ∧ f seed (b+1) ≠ ref (b+1)) : a ≤ b := by
  by_contra! gt
  obtain ⟨seed, hs, hd⟩ := diff
  exact hd (same seed hs (b+1) (by omega))

theorem actual_edge (u n : Nat) (b : Int) (x : Int → Bool) (mask : Nat) (inj : Nat → Int → Bool)
    (positive : 0 < n) (initial : mask.testBit (block u x b) = true) :
    ∃ edge, edge ≤ b+(u : Int)+(n : Int) ∧
      edgeOf (fits u b x mask) (run inj n) (run inj n x) edge := by
  classical
  let first := b-3*(n : Int)
  let far := b+(u : Int)+1
  let flip : Int → Bool := fun z => if z = far then !x z else x z
  have no (z : Int) (hz : z < far) : flip z = x z := ite_eq_right (ne_of_lt hz)
  have fall : fits u b x mask flip := by
    refine ⟨fun z hz => no z (by dsimp [far]; omega),?_⟩
    rwa [block_congr (fun z _ hi => no z (by dsimp [far]; omega))]
  have sep : separatesAt flip x far := by
    refine ⟨?_, fun z hz => ite_eq_right (ne_of_gt hz)⟩
    cases v : x far <;> simp [flip,v]
  have moving := (separates_run inj n sep).1
  let variableAt := fun (j : Nat) => ∃ seed,
    fits u b x mask seed ∧ run inj n seed (first+(j : Int)+1) ≠ run inj n x (first+(j : Int)+1)
  let witness := (far+(n : Int)-first-1).toNat
  have atWitness : first+(witness : Int)+1 = far+(n : Int) := by
    dsimp [witness,first,far]
    omega
  have existsVariable : ∃ j, variableAt j := by
    refine ⟨witness,flip,fall,?_⟩
    rwa [atWitness]
  let k := Nat.find existsVariable
  let edge := first+(k : Int)
  have k_le : k ≤ witness := by
    apply Nat.find_min'
    exact ⟨flip,fall,by rwa [atWitness]⟩
  refine ⟨edge,?_,⟨?_,Nat.find_spec existsVariable⟩⟩
  · dsimp [edge,far] at *
    omega
  · intro seed hs z hz
    by_cases left : z ≤ first
    · exact run_prefix inj n b hs.1 z left
    by_contra bad
    let j := (z-first-1).toNat
    have idx : first+(j : Int)+1 = z := by dsimp [j]; omega
    have earlier : j < k := by dsimp [edge] at hz; omega
    apply Nat.find_min existsVariable earlier
    exact ⟨seed,hs,by rwa [idx]⟩

theorem reached_anchor (w n : Nat) (init : BoxState) (inj : Nat → Int → Bool) :
    (reached w n init inj).1 = run inj n init.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reached_succ,run_succ]
    change evolve (reached w n init inj).1 (inj n) = _
    rw [ih]

theorem step_prefix (w : Nat) (st : BoxState) (inj : Int → Bool)
    (valid : members w st st.1) {y : Int → Bool} (hy : members w (advanceState w inj st) y) :
    ∃ t, members w st t ∧ ∀ z ≤ (advanceState w inj st).2.1+(w : Int), evolve t inj z = y z := by
  rcases st with ⟨x,b,mask⟩
  obtain ⟨_,_,same,_,image⟩ := exact_advance w b x inj mask valid.2
  let f := (advance w b x inj mask).1
  let value : Fin (2^w) := ⟨block w y f,pack_lt _ _⟩
  obtain ⟨t,ht,eq⟩ := (image value).mp hy.2
  refine ⟨t,ht,?_⟩
  intro z hz
  change z ≤ f+(w : Int) at hz
  by_cases left : z ≤ f
  · exact (same t ht z left).trans (hy.1 z left).symm
  · exact block_bit_eq eq z (by omega) hz

theorem step_limit (w : Nat) (st : BoxState) (inj : Int → Bool)
    (valid : members w st st.1) : st.2.1-3 ≤ (advanceState w inj st).2.1 := by
  rcases st with ⟨x,b,mask⟩
  exact (exact_advance w b x inj mask valid.2).1

theorem reached_limit (w k : Nat) (init : BoxState) (inj : Nat → Int → Bool)
    (valid : members w init init.1) :
    (reached w 1 init inj).2.1-3*(k : Int) ≤ (reached w (k+1) init inj).2.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [reached_succ w (k+1) init inj]
    have h := step_limit w (reached w (k+1) init inj) (inj (k+1)) (reached_valid w _ _ _ valid)
    omega

theorem reached_sound (w n : Nat) (init : BoxState) (inj : Nat → Int → Bool)
    (valid : members w init init.1) (seed : Int → Bool) (hs : members w init seed) :
    members w (reached w n init inj) (run inj n seed) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [reached_succ,run_succ]
    exact step_sound w _ _ (reached_valid w n _ _ valid) _ ih

theorem reached_prefix (w k : Nat) (init : BoxState) (inj : Nat → Int → Bool)
    (valid : members w init init.1) :
    ∀ y, members w (reached w (k+1) init inj) y →
      ∃ seed, members w init seed ∧
        ∀ z ≤ (reached w 1 init inj).2.1+(w : Int)-3*(k : Int), run inj (k+1) seed z = y z := by
  induction k with
  | zero =>
    intro y hy
    simpa [reached,run] using step_prefix w init (inj 0) valid hy
  | succ k ih =>
    intro y hy
    rw [reached_succ w (k+1) init inj] at hy
    let prev := reached w (k+1) init inj
    have prevOk : members w prev prev.1 := reached_valid w _ _ _ valid
    obtain ⟨before,hbefore,same⟩ := step_prefix w prev (inj (k+1)) prevOk hy
    obtain ⟨seed,hs,initial⟩ := ih before hbefore
    refine ⟨seed,hs,?_⟩
    intro z zle
    rw [run_succ]
    have hlim := reached_limit w (k+1) init inj valid
    rw [reached_succ w (k+1) init inj] at hlim
    have after : z ≤ (advanceState w (inj (k+1)) prev).2.1+(w : Int) := by
      change (reached w 1 init inj).2.1-3*((k+1 : Nat) : Int) ≤
        (advanceState w (inj (k+1)) prev).2.1 at hlim
      omega
    exact (evolve_agree (inj (k+1)) z (fun j _ hi => initial j (by omega))).trans (same z after)

def padMask (u w mask : Nat) : Nat :=
  (List.range (2^w)).foldl (fun acc pat =>
    if mask.testBit (pat % 2^u) then acc ||| ((1 : Nat) <<< pat) else acc) 0

theorem pad_bits (u w mask v : Nat) (hv : v < 2^w) :
    (padMask u w mask).testBit v = mask.testBit (v % 2^u) := by
  have filterFold (l : List Nat) (acc : Nat) :
      l.foldl (fun a pat => if mask.testBit (pat % 2^u) then a ||| (1 <<< pat) else a) acc =
      (l.filter (fun pat => mask.testBit (pat % 2^u))).foldl (fun a pat => a ||| (1 <<< pat)) acc := by
    induction l generalizing acc with
    | nil => rfl
    | cons a l ih => cases h : mask.testBit (a % 2^u) <;>
        simp [List.foldl_cons,h,ih]
  apply Bool.eq_iff_iff.mpr
  rw [padMask, filterFold, folds_bit]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_filter, List.mem_range]
  exact ⟨by rintro ⟨a,⟨_,bit⟩,rfl⟩; exact bit, fun h => ⟨v,⟨hv,h⟩,rfl⟩⟩

theorem pad_fits {u w : Nat} (uw : u ≤ w) (b : Int) (x : Int → Bool) (mask : Nat) (y : Int → Bool) :
    members w (x,b,padMask u w mask) y ↔ fits u b x mask y := by
  change (∀ z ≤ b, y z = x z) ∧ (padMask u w mask).testBit (block w y b) = true ↔ _
  have range : block w y b < 2^w := pack_lt _ _
  rw [pad_bits u w mask (block w y b) range]
  change (∀ z ≤ b, y z = x z) ∧ mask.testBit (pack w (fun i => y (b+1+(i : Int))) % 2^u) = true ↔ _
  rw [pack_mod _ uw]
  rfl

theorem reached_diff (w k : Nat) (init : BoxState) (inj : Nat → Int → Bool)
    (valid : members w init init.1) :
    let final := reached w (k+1) init inj
    let f := final.2.1
    ∃ y, members w final y ∧ y (f+1) ≠ run inj (k+1) init.1 (f+1) := by
  dsimp only
  rw [reached_succ w k init inj,run_succ inj k,← reached_anchor w k init inj]
  let prev := reached w k init inj
  have v : members w prev prev.1 := reached_valid w _ _ _ valid
  obtain ⟨_,_,_,⟨t,ht,neq⟩,_⟩ := exact_advance w prev.2.1 prev.1 (inj k) prev.2.2 v.2
  exact ⟨evolve t (inj k),step_sound w prev _ v t ht,neq⟩

def track (u w n : Nat) (b : Int) (x : Int → Bool) (mask : Nat) (inj : Nat → Int → Bool) : BoxState :=
  reached w n (x,b,padMask u w mask) inj

theorem track_first (u w : Nat) (b e : Int) (x : Int → Bool) (mask : Nat) (inj : Nat → Int → Bool)
    (h : u ≤ w) (valid : fits u b x mask x)
    (actual : edgeOf (fits u b x mask) (run inj 1) (run inj 1 x) e) :
    (track u w 1 b x mask inj).2.1 = e := by
  obtain ⟨_,_,same,diff,_⟩ := exact_advance w b x (inj 0) (padMask u w mask) ((pad_fits h b x mask x).mpr valid).2
  have matchFirst (y : Int → Bool) : run inj 1 y = evolve y (inj 0) := by simp [run]
  rw [matchFirst x] at actual
  have agreement : ∀ seed, fits w b x (padMask u w mask) seed →
      ∀ z ≤ e, evolve seed (inj 0) z = evolve x (inj 0) z := by
    intro seed hs z hz
    rw [← matchFirst]
    exact actual.1 seed ((pad_fits h b x mask seed).mp hs) z hz
  have variation : ∃ seed, fits w b x (padMask u w mask) seed ∧
      evolve seed (inj 0) (e+1) ≠ evolve x (inj 0) (e+1) := by
    obtain ⟨seed,hs,neq⟩ := actual.2
    exact ⟨seed,(pad_fits h b x mask seed).mpr hs,by rwa [← matchFirst]⟩
  exact le_antisymm (edge_compare same variation) (edge_compare agreement diff)

theorem track_known (u w k : Nat) (b e : Int) (x : Int → Bool) (mask : Nat) (inj : Nat → Int → Bool)
    (h : u ≤ w) (valid : fits u b x mask x)
    (actual : edgeOf (fits u b x mask) (run inj (k+1)) (run inj (k+1) x) e) :
    (track u w (k+1) b x mask inj).2.1 ≤ e := by
  apply edge_compare (A := fits u b x mask) (f := run inj (k+1)) _ actual.2
  intro y hy z hz
  let init : BoxState := (x,b,padMask u w mask)
  have own : members w init x := (pad_fits h b x mask x).mpr valid
  have r := reached_sound w (k+1) init inj own y ((pad_fits h b x mask y).mpr hy)
  have eq := r.1 z hz
  change run inj (k+1) y z = (reached w (k+1) init inj).1 z at eq
  rwa [reached_anchor] at eq

theorem width_test (u k v : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (hx : mask.testBit (block u x b) = true) :
    let t := max 1 v
    ∃ e₁ e : Int,
      edgeOf (fits u b x mask) (run inj 1) (run inj 1 x) e₁ ∧
      edgeOf (fits u b x mask) (run inj (k+1)) (run inj (k+1) x) e ∧
      e ≤ b+(u : Int)+((k+1 : Nat) : Int) ∧
      let g := e-e₁+3*(k : Int)
      0 ≤ g ∧
        (∀ w : Nat, u ≤ w →
          let first := (track u w 1 b x mask inj).2.1
          let final := track u w (k+1) b x mask inj
          let f := final.2.1
          let pass := f+(t : Int)+3*(k : Int) ≤ first+(w : Int)
          first = e₁ ∧ f ≤ e ∧
            (∀ z : Int, z+3*(k : Int) ≤ first+(w : Int) →
              ∀ observed : Int → Bool,
                (∃ y, members w final y ∧ ∀ j ≤ z, y j = observed j) ↔
                (∃ seed, fits u b x mask seed ∧ ∀ j ≤ z, run inj (k+1) seed j = observed j)) ∧
            (pass ↔ g+(t : Int) ≤ (w : Int)) ∧
            (pass → f = e ∧
              ∀ val : Fin (2^v),
                (∃ word : Fin (2^w), final.2.2.testBit word.val = true ∧
                  word.val % (2^v) = val.val) ↔
                (∃ seed, fits u b x mask seed ∧ block v (run inj (k+1) seed) e = val.val))) ∧
        g+(t : Int) ≤ (u : Int)+4*((k+1 : Nat) : Int)+(t : Int) := by
  let t := max 1 v
  obtain ⟨e₁,_,realOne⟩ := actual_edge u 1 b x mask inj (by decide) hx
  obtain ⟨e,ue,realAll⟩ := actual_edge u (k+1) b x mask inj (by omega) hx
  let g := e-e₁+3*(k : Int)
  have original : fits u b x mask x := ⟨fun _ _ => rfl,hx⟩
  have e1 := track_first u u b e₁ x mask inj le_rfl original realOne
  have approx := track_known u u k b e x mask inj le_rfl original realAll
  have control := ((pad_fits (u:=u) (w:=u) le_rfl b x mask x).mpr original)
  have lower := reached_limit u k (x,b,padMask u u mask) inj control
  have nonnegative : 0 ≤ g := by
    change (track u u 1 b x mask inj).2.1-3*(k : Int) ≤ (track u u (k+1) b x mask inj).2.1 at lower
    dsimp [g]
    omega
  have initialEdge : b-3 ≤ e₁ := by
    rw [← e1]
    exact step_limit u _ (inj 0) control
  refine ⟨e₁,e,realOne,realAll,ue,nonnegative,?_,?_⟩
  · intro w uw
    let init : BoxState := (x,b,padMask u w mask)
    let first := (track u w 1 b x mask inj).2.1
    let final := track u w (k+1) b x mask inj
    let f := final.2.1
    let pass := f+(t : Int)+3*(k : Int) ≤ first+(w : Int)
    have own : members w init x := (pad_fits uw b x mask x).mpr original
    have start : first = e₁ := track_first u w b e₁ x mask inj uw original realOne
    have order : f ≤ e := track_known u w k b e x mask inj uw original realAll
    have sound (seed : Int → Bool) (hseed : fits u b x mask seed) :
        members w final (run inj (k+1) seed) :=
      reached_sound w (k+1) init inj own seed ((pad_fits uw b x mask seed).mpr hseed)
    have complete (y : Int → Bool) (hy : members w final y) :
        ∃ seed, fits u b x mask seed ∧
          ∀ z ≤ first+(w : Int)-3*(k : Int), run inj (k+1) seed z = y z := by
      obtain ⟨seed,hs, same⟩ := reached_prefix w k init inj own y hy
      exact ⟨seed,(pad_fits uw b x mask seed).mp hs,same⟩
    have passEdge (allowed : pass) : f = e := by
      have ht : 1 ≤ t := le_max_left 1 v
      have avail : f+1 ≤ first+(w : Int)-3*(k : Int) := by dsimp [pass] at allowed; omega
      obtain ⟨y,hy,neq⟩ := reached_diff w k init inj own
      obtain ⟨seed,hs,eq⟩ := complete y hy
      have far : e ≤ f := by
        apply edge_compare (A := fits u b x mask) (f := run inj (k+1)) (ref := run inj (k+1) x) realAll.1
        refine ⟨seed,hs,?_⟩
        rw [eq (f+1) avail]
        exact neq
      exact le_antisymm order far
    refine ⟨start,order,?_,?_,?_⟩
    · intro z hz ref
      change z+3*(k : Int) ≤ first+(w : Int) at hz
      constructor
      · rintro ⟨y,hy,eq⟩
        obtain ⟨seed,hs,matchedPrefix⟩ := complete y hy
        exact ⟨seed,hs,fun j hj => (matchedPrefix j (by omega)).trans (eq j hj)⟩
      · rintro ⟨seed,hs,eq⟩
        exact ⟨run inj (k+1) seed,sound seed hs,eq⟩
    · change pass ↔ g+(t : Int) ≤ (w : Int)
      constructor
      · intro h
        have eq := passEdge h
        dsimp [pass] at h
        dsimp [g]
        omega
      · intro h
        dsimp [g] at h
        dsimp [pass]
        omega
    · intro hp
      have hpass : pass := hp
      have eq := passEdge hpass
      have bound : f+(v : Int) ≤ first+(w : Int)-3*(k : Int) := by
        dsimp [pass] at hpass
        have ht : v ≤ t := le_max_right _ _
        omega
      have vw : v ≤ w := by
        dsimp [pass] at hpass
        have ht : v ≤ t := le_max_right _ _
        have c : 0 ≤ e-first+3*(k : Int) := by dsimp [g] at nonnegative; omega
        omega
      refine ⟨eq,fun value => ⟨?_,?_⟩⟩
      · rintro ⟨word,hword,hmod⟩
        let y := trial f final.1 word.val
        have stored : block w y f = word.val := by
          rw [block_trial,Nat.mod_eq_of_lt word.isLt]
        have agree : members w final y := by
          refine ⟨fun z hz => ite_eq_left hz,?_⟩
          change final.2.2.testBit (block w y f) = true
          rwa [stored]
        obtain ⟨seed,hs,matched⟩ := complete y agree
        refine ⟨seed,hs,?_⟩
        rw [← eq,block_congr (fun z _ hi => matched z (le_trans hi bound)),block_trial]
        exact hmod
      · rintro ⟨seed,hs,heq⟩
        refine ⟨⟨block w (run inj (k+1) seed) f,pack_lt _ _⟩,(sound seed hs).2,?_⟩
        change pack w (fun i => run inj (k+1) seed (f+1+(i : Int))) % 2^v = value.val
        rw [pack_mod _ vw]
        exact eq.symm ▸ heq
  · change g+(t : Int) ≤ _
    dsimp [g]
    omega

end PEqualNP.Outside.L_meta_25605

theorem PEqualNP.Outside.L_meta_25605 : let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x injection : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (allowedMask : Nat) =>
  let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => allowedMask.testBit (pattern % 2^w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b-2+(offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)
∀ (u n v : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool), 0 < n → mask.testBit (block u x b) = true →
  let run := fun (length : Nat) (seed : Int → Bool) =>
    (List.range length).foldl (fun st tick => evolve st (inj tick)) seed
  let realEdge := fun (length : Nat) (edge : Int) =>
    (∀ seed, fits u b x mask seed → ∀ z ≤ edge, run length seed z = run length x z) ∧
    (∃ seed, fits u b x mask seed ∧ run length seed (edge+1) ≠ run length x (edge+1))
  let pad := fun (w : Nat) => (List.range (2^w)).foldl (fun (acc pat : Nat) =>
    if mask.testBit (pat % (2^u)) then acc ||| ((1 : Nat) <<< pat) else acc) 0
  let track := fun (w len : Nat) =>
    (List.range len).foldl (fun (st : (Int → Bool) × Int × Nat) tick =>
      let nxt := advance w st.2.1 st.1 (inj tick) st.2.2
      (evolve st.1 (inj tick), nxt.1, nxt.2)) (x, b, pad w)
  let t := max 1 v
  ∃ E₁ E : Int, realEdge 1 E₁ ∧ realEdge n E ∧ E ≤ b+(u : Int)+(n : Int) ∧
    let G := E-E₁+3*((n-1 : Nat) : Int)
    0 ≤ G ∧
    (∀ w : Nat, u ≤ w →
      let first := (track w 1).2.1
      let final := track w n
      let F := final.2.1
      let pass := F+(t : Int)+3*((n-1 : Nat) : Int) ≤ first+(w : Int)
      first = E₁ ∧ F ≤ E ∧
      (∀ z : Int, z+3*((n-1 : Nat) : Int) ≤ first+(w : Int) →
        ∀ observed : Int → Bool,
          (∃ y, fits w F final.1 final.2.2 y ∧ ∀ j ≤ z, y j = observed j) ↔
          (∃ seed, fits u b x mask seed ∧ ∀ j ≤ z, run n seed j = observed j)) ∧
      (pass ↔ G+(t : Int) ≤ (w : Int)) ∧
      (pass → F = E ∧
        ∀ val : Fin (2^v),
          (∃ word : Fin (2^w), final.2.2.testBit word.val = true ∧
            word.val % (2^v) = val.val) ↔
          (∃ seed, fits u b x mask seed ∧ block v (run n seed) E = val.val))) ∧
    G+(t : Int) ≤ (u : Int)+4*(n : Int)+(t : Int) := by
  dsimp only
  intro u n v b x mask inj positive hx
  cases n with
  | zero => omega
  | succ k => exact PEqualNP.Outside.L_meta_25605.width_test u k v b x mask inj hx
