import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23955

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private def mapGate (wire : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map wire⟩

private theorem lookup_snoc (xs : List Bool) (value : Bool) (i : Nat) :
    (xs ++ [value]).getD i false =
      if i = xs.length then value else xs.getD i false := by
  rcases Nat.lt_trichotomy i xs.length with small | rfl | big
  · rw [ite_eq_right (Nat.ne_of_lt small), List.getD_append _ _ _ _ small]
  · rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  · have out : xs.length + 1 ≤ i := by omega
    rw [ite_eq_right (Nat.ne_of_gt big), List.getD_eq_default _ _ (by simpa using out),
      List.getD_eq_default _ _ (Nat.le_of_lt big)]

private theorem mapFold (wire : Nat → Nat) (oldSize newSize bound : Nat)
    (outputs : ∀ j < bound, ∀ w, (wire w = newSize+j) ↔ (w = oldSize+j))
    (gs : List Gate) (xs ys : List Bool) (j : Nat)
    (room : j + gs.length ≤ bound)
    (oldLen : xs.length = oldSize+j) (newLen : ys.length = newSize+j)
    (same : ∀ w, xs.getD w false = ys.getD (wire w) false) :
    ∀ w, (gs.foldl step xs).getD w false =
      ((gs.map (mapGate wire)).foldl step ys).getD (wire w) false := by
  induction gs generalizing xs ys j with
  | nil => exact same
  | cons gate gs ih =>
    have jlt : j < bound := by simp at room; omega
    have equalGate : gate.op.eval (gate.inputs.map fun i => xs.getD i false) =
        (mapGate wire gate).op.eval ((mapGate wire gate).inputs.map fun i => ys.getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left (fun a _ => same a)
    apply ih (step xs gate) (step ys (mapGate wire gate)) (j+1)
    · simp at room
      omega
    · simp [step, oldLen, Nat.add_assoc]
    · simp [step, newLen, Nat.add_assoc]
    · intro w
      rw [step, step, lookup_snoc, lookup_snoc, equalGate, same w, oldLen, newLen]
      by_cases h : w = oldSize+j
      · rw [ite_eq_left h, ite_eq_left ((outputs j jlt w).mpr h)]
      · rw [ite_eq_right h, ite_eq_right (fun e => h ((outputs j jlt w).mp e))]

private def embed {n m n' m' : Nat} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (j : Fin (n'+m')) : Nat :=
  if h : j.val < n' then (f ⟨j.val, h⟩).val else n + (g ⟨j.val-n', by omega⟩).val

private theorem embed_injective {n m n' m' : Nat} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (embed f g) := by
  intro a b equal
  apply Fin.ext
  unfold embed at equal
  split at equal <;> split at equal
  · exact congrArg (fun j : Fin n' => j.val) (hf (Fin.ext equal))
  · have h := (f ⟨a.val, by assumption⟩).isLt
    omega
  · have h := (f ⟨b.val, by assumption⟩).isLt
    omega
  · have h : (g ⟨a.val-n', by omega⟩).val = (g ⟨b.val-n', by omega⟩).val := by omega
    have offsets := congrArg Fin.val (hg (Fin.ext h))
    change a.val-n' = b.val-n' at offsets
    omega

private noncomputable def rewire {n m n' m' : Nat}
    (f : Fin n' → Fin n) (g : Fin m' → Fin m) (bound w : Nat) : Nat := by
  classical
  exact if w < n+m then
    if h : ∃ j : Fin (n'+m'), embed f g j = w then h.choose.val else n'+m'+bound
    else n'+m' + (w-(n+m))

private theorem rewire_output {n m n' m' : Nat} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (bound j : Nat) (inside : j < bound) (w : Nat) :
    rewire f g bound w = (n'+m')+j ↔ w = (n+m)+j := by
  classical
  unfold rewire
  split
  · next small =>
    split
    · next h =>
      have chosen := h.choose.isLt
      omega
    · omega
  · omega

private theorem length_each {n m : Nat} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n+m := by simp [oneEach]

private theorem each_lookup {n m : Nat} (u : Fin n) (v : Fin m) (w : Nat) :
    (oneEach u v).getD w false = decide (w = u.val ∨ w = n+v.val) := by
  by_cases left : w<n
  · unfold oneEach
    rw [List.getD_append _ _ _ _ (by simpa using left),
      List.getD_eq_getElem _ _ (by simpa using left)]
    have miss : w ≠ n+v.val := by omega
    simp [List.getElem_ofFn, Fin.ext_iff, miss]
  · by_cases right : w<n+m
    · unfold oneEach
      rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
        List.getD_eq_getElem _ _ (by simp; omega)]
      have miss : w ≠ u.val := by have e := u.isLt; omega
      have shifted : w-n = v.val ↔ w = n+v.val := by omega
      simp [List.getElem_ofFn, Fin.ext_iff, miss, shifted]
    · rw [List.getD_eq_default _ _ (by rw [length_each]; omega)]
      have neither : ¬ (w = u.val ∨ w = n+v.val) := by
        have a := u.isLt
        have b := v.isLt
        omega
      simp [neither]


private theorem lookup_rewire {n m n' m' : Nat} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (u : Fin n') (v : Fin m') (bound w : Nat) :
    (oneEach (f u) (g v)).getD w false =
      (oneEach u v).getD (rewire f g bound w) false := by
  classical
  let left : Fin (n'+m') := ⟨u.val, by have h := u.isLt; omega⟩
  let right : Fin (n'+m') := ⟨n'+v.val, by have h := v.isLt; omega⟩
  have embedLeft : embed f g left = (f u).val := by simp [embed, left, u.isLt]
  have embedRight : embed f g right = n+(g v).val := by
    have ne : ¬ n'+v.val < n' := by omega
    simp [embed, right, ne]
  rw [each_lookup, each_lookup]
  unfold rewire
  split
  · next oldRaw =>
    split
    · next found =>
      have eqLeft : w = (f u).val ↔ found.choose.val = u.val := by
        constructor
        · intro eq
          have same := found.choose_spec.trans (eq.trans embedLeft.symm)
          exact congrArg Fin.val (embed_injective f g hf hg same)
        · intro eq
          have same : found.choose = left := Fin.ext eq
          exact found.choose_spec.symm.trans ((congrArg (embed f g) same).trans embedLeft)
      have eqRight : w = n+(g v).val ↔ found.choose.val = n'+v.val := by
        constructor
        · intro eq
          have same := found.choose_spec.trans (eq.trans embedRight.symm)
          exact congrArg Fin.val (embed_injective f g hf hg same)
        · intro eq
          have same : found.choose = right := Fin.ext eq
          exact found.choose_spec.symm.trans ((congrArg (embed f g) same).trans embedRight)
      simp [eqLeft, eqRight]
    · next missing =>
      have neL : w ≠ (f u).val := fun equal => missing ⟨left,embedLeft.trans equal.symm⟩
      have neR : w ≠ n+(g v).val := fun equal => missing ⟨right,embedRight.trans equal.symm⟩
      have newL : n'+m'+bound ≠ u.val := by have h := u.isLt; omega
      have newR : n'+m'+bound ≠ n'+v.val := by have h := v.isLt; omega
      simp [neL,neR,newL,newR]
  · next oldGate =>
    have neL : w ≠ (f u).val := by have h := (f u).isLt; omega
    have neR : w ≠ n+(g v).val := by have h := (g v).isLt; omega
    have newL : n'+m'+(w-(n+m)) ≠ u.val := by have h := u.isLt; omega
    have newR : n'+m'+(w-(n+m)) ≠ n'+v.val := by have h := v.isLt; omega
    simp [neL,neR,newL,newR]

end PEqualNP.Outside.L_meta_23955

open PEqualNP.Outside.L_meta_23955 in
theorem PEqualNP.Outside.L_meta_23955 : (∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C') := by
  intro n m n' m' A f g C hf hg shape rep
  let wire := rewire f g C.size
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map (mapGate wire), wire C.output⟩
  refine ⟨D, ?_, by simp [D, PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro gate mem
    rcases List.mem_map.mp mem with ⟨source, oldmem, rfl⟩
    exact ⟨(shape source oldmem).1, by simpa [mapGate] using (shape source oldmem).2⟩
  · intro u v
    have equal := mapFold wire (n+m) (n'+m') C.size (rewire_output f g C.size)
      C.gates (PEqualNP.Represents.oneEach (f u) (g v)) (PEqualNP.Represents.oneEach u v)
      0 (by simp [PEqualNP.CircuitLowerBounds.Circuit.size])
      (by simp [length_each]) (by simp [length_each]) (lookup_rewire f g hf hg u v C.size) C.output
    have simulates : C.eval (PEqualNP.Represents.oneEach (f u) (g v)) =
        D.eval (PEqualNP.Represents.oneEach u v) := equal
    exact simulates.symm.trans (rep (f u) (g v))
