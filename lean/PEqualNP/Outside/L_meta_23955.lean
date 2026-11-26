import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23955

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma stepWire_length (w : List Bool) (g : Gate) :
    (stepWire w g).length = w.length + 1 := by
  simp [stepWire]

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepWire_length]
    simp only [List.length_cons]
    omega

private lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_lt {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp [Fin.ext_iff]

private lemma oneEach_getD_mid {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ)
    (hlo : n ≤ i) (hhi : i < n + m) :
    (oneEach u v).getD i false = decide (i - n = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hlo])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [Fin.ext_iff]

private lemma oneEach_getD_ge {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : n + m ≤ i) :
    (oneEach u v).getD i false = false := by
  apply List.getD_eq_default
  rw [oneEach_length]
  exact hi

private def findPre {a b : ℕ} (h : Fin a → Fin b) (w : ℕ) : Option (Fin a) :=
  (List.finRange a).find? (fun i => decide ((h i).val = w))

private lemma findPre_some {a b : ℕ} {h : Fin a → Fin b} {w : ℕ} {i : Fin a}
    (hfind : findPre h w = some i) : (h i).val = w := by
  have h1 := List.find?_some hfind
  exact of_decide_eq_true h1

private lemma findPre_none {a b : ℕ} {h : Fin a → Fin b} {w : ℕ}
    (hfind : findPre h w = none) (i : Fin a) : (h i).val ≠ w := by
  have h1 := List.find?_eq_none.mp hfind i (List.mem_finRange i)
  exact of_decide_eq_false (Bool.eq_false_iff.mpr h1)

private def remapWire {n m n' m' : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (len : ℕ) (w : ℕ) : ℕ :=
  if w < n then
    match findPre f w with
    | some i => i.val
    | none => n' + m' + len
  else if w < n + m then
    match findPre g (w - n) with
    | some j => n' + j.val
    | none => n' + m' + len
  else if w < n + m + len then
    n' + m' + (w - (n + m))
  else
    n' + m' + len

private def remapGate {n m n' m' : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (len : ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map (remapWire f g len)⟩

private def pullCircuit {n m n' m' : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (C : Circuit) : Circuit :=
  ⟨C.gates.map (remapGate f g C.gates.length), remapWire f g C.gates.length C.output⟩

private lemma pullCircuit_fanInTwo {n m n' m' : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (C : Circuit) (hC : FanInTwo C) : FanInTwo (pullCircuit f g C) := by
  intro gt hgt
  rw [pullCircuit, List.mem_map] at hgt
  rcases hgt with ⟨gt0, hgt0, rfl⟩
  have h0 := hC gt0 hgt0
  refine ⟨h0.1, ?_⟩
  simp only [remapGate, List.length_map]
  exact h0.2

private lemma pullCircuit_size {n m n' m' : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (C : Circuit) : (pullCircuit f g C).size = C.size := by
  simp [Circuit.size, pullCircuit]

private lemma wires_match {n m n' m' : ℕ}
    (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (len : ℕ) (u : Fin n') (v : Fin m')
    (gs : List Gate) (w1 w2 : List Bool)
    (k : ℕ) (hk : k + gs.length ≤ len)
    (hlen1 : w1.length = n + m + k)
    (hlen2 : w2.length = n' + m' + k)
    (hin1 : ∀ i < n, w1.getD i false = decide (i = (f u).val))
    (hin2 : ∀ j < m, w1.getD (n + j) false = decide (j = (g v).val))
    (hin1' : ∀ i < n', w2.getD i false = decide (i = u.val))
    (hin2' : ∀ j < m', w2.getD (n' + j) false = decide (j = v.val))
    (hgate : ∀ t < k, w2.getD (n' + m' + t) false = w1.getD (n + m + t) false) :
    ∀ idx : ℕ,
      ((gs.map (remapGate f g len)).foldl stepWire w2).getD (remapWire f g len idx) false =
      (gs.foldl stepWire w1).getD idx false := by
  have hcur : ∀ (a1 a2 : List Bool) (r : ℕ),
      r ≤ len →
      a1.length = n + m + r →
      a2.length = n' + m' + r →
      (∀ i < n, a1.getD i false = decide (i = (f u).val)) →
      (∀ j < m, a1.getD (n + j) false = decide (j = (g v).val)) →
      (∀ i < n', a2.getD i false = decide (i = u.val)) →
      (∀ j < m', a2.getD (n' + j) false = decide (j = v.val)) →
      (∀ t < r, a2.getD (n' + m' + t) false = a1.getD (n + m + t) false) →
      ∀ idx : ℕ, a2.getD (remapWire f g len idx) false = a1.getD idx false := by
    intro a1 a2 r hr ha1 ha2 h1 h2 h1' h2' hg_eq idx
    unfold remapWire
    split_ifs with hlt1 hlt2 hlt3
    · cases hfp : findPre f idx with
      | some i =>
        have hfi := findPre_some hfp
        rw [h1' i.val i.isLt, h1 idx hlt1]
        rw [decide_eq_decide]
        constructor
        · intro heq
          have hi : i = u := Fin.ext heq
          rw [← hfi, hi]
        · intro heq
          have hi : f i = f u := Fin.ext (hfi.trans heq)
          exact congrArg Fin.val (hf hi)
      | none =>
        have hnone := findPre_none hfp u
        dsimp only
        rw [List.getD_eq_default a2 _ (by omega)]
        rw [h1 idx hlt1]
        simp [Ne.symm hnone]
    · have hsub : idx - n < m := by omega
      have hidx : idx = n + (idx - n) := by omega
      cases hgp : findPre g (idx - n) with
      | some j =>
        have hgj := findPre_some hgp
        rw [h2' j.val j.isLt, hidx, h2 (idx - n) hsub]
        rw [decide_eq_decide]
        constructor
        · intro heq
          have hj : j = v := Fin.ext heq
          rw [← hgj, hj]
        · intro heq
          have hj : g j = g v := Fin.ext (hgj.trans heq)
          exact congrArg Fin.val (hg hj)
      | none =>
        have hnone := findPre_none hgp v
        dsimp only
        rw [List.getD_eq_default a2 _ (by omega)]
        rw [hidx, h2 (idx - n) hsub]
        simp [Ne.symm hnone]
    · by_cases ht : idx - (n + m) < r
      · have hidx : idx = n + m + (idx - (n + m)) := by omega
        have heq := hg_eq (idx - (n + m)) ht
        conv_rhs => rw [hidx]
        exact heq
      · rw [List.getD_eq_default a2 _ (by omega)]
        rw [List.getD_eq_default a1 _ (by omega)]
    · rw [List.getD_eq_default a2 _ (by omega)]
      rw [List.getD_eq_default a1 _ (by omega)]
  induction gs generalizing w1 w2 k with
  | nil =>
    exact hcur w1 w2 k (by simpa using hk) hlen1 hlen2 hin1 hin2 hin1' hin2' hgate
  | cons gt rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval_eq :
        (remapGate f g len gt).op.eval ((remapGate f g len gt).inputs.map fun i => w2.getD i false) =
        gt.op.eval (gt.inputs.map fun i => w1.getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro idx _
      exact hcur w1 w2 k (by simp at hk; omega) hlen1 hlen2 hin1 hin2 hin1' hin2' hgate idx
    have hstep1 : (stepWire w1 gt).length = n + m + (k + 1) := by
      rw [stepWire_length, hlen1]; omega
    have hstep2 : (stepWire w2 (remapGate f g len gt)).length = n' + m' + (k + 1) := by
      rw [stepWire_length, hlen2]; omega
    apply ih (stepWire w1 gt) (stepWire w2 (remapGate f g len gt)) (k + 1) (by simp at hk; omega)
      hstep1 hstep2
    · intro i hi
      rw [stepWire, List.getD_append _ _ _ _ (by omega)]
      exact hin1 i hi
    · intro j hj
      rw [stepWire, List.getD_append _ _ _ _ (by omega)]
      exact hin2 j hj
    · intro i hi
      rw [stepWire, List.getD_append _ _ _ _ (by omega)]
      exact hin1' i hi
    · intro j hj
      rw [stepWire, List.getD_append _ _ _ _ (by omega)]
      exact hin2' j hj
    · intro t ht
      by_cases htk : t < k
      · rw [stepWire, stepWire,
            List.getD_append _ _ _ _ (by omega),
            List.getD_append _ _ _ _ (by omega)]
        exact hgate t htk
      · have hteq : t = k := by omega
        subst hteq
        rw [stepWire, stepWire,
            List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
        have h1 : n' + m' + t - w2.length = 0 := by omega
        have h2 : n + m + t - w1.length = 0 := by omega
        rw [h1, h2]
        simpa using hval_eq

end PEqualNP.Outside.L_meta_23955

open PEqualNP.Outside.L_meta_23955 in
theorem PEqualNP.Outside.L_meta_23955 : ∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C' := by
  intro n m n' m' A f g C hf hg hC hrep
  refine ⟨pullCircuit f g C, pullCircuit_fanInTwo f g C hC, (pullCircuit_size f g C).le, ?_⟩
  intro u v
  have hw := wires_match f g hf hg C.gates.length u v C.gates
    (PEqualNP.Represents.oneEach (f u) (g v)) (PEqualNP.Represents.oneEach u v) 0
    (by omega)
    (by rw [oneEach_length]; omega)
    (by rw [oneEach_length]; omega)
    (fun i hi => oneEach_getD_lt (f u) (g v) i hi)
    (fun j hj => by
      have h := oneEach_getD_mid (f u) (g v) (n + j) (by omega) (by omega)
      simpa using h)
    (fun i hi => oneEach_getD_lt u v i hi)
    (fun j hj => by
      have h := oneEach_getD_mid u v (n' + j) (by omega) (by omega)
      simpa using h)
    (fun t ht => absurd ht (Nat.not_lt_zero t))
    C.output
  have heval : (pullCircuit f g C).eval (PEqualNP.Represents.oneEach u v) =
      C.eval (PEqualNP.Represents.oneEach (f u) (g v)) := hw
  rw [heval, hrep (f u) (g v)]
