import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23955_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private theorem W_nil (w : List Bool) : W [] w = w := rfl

private theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

private theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

private theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

private theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

private theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

private theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

private theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

private theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

private theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

private noncomputable def pull {a b : Nat} (f : Fin a → Fin b) (k : Nat) (offset missing : Nat) : Nat :=
  if h : ∃ i : Fin a, (f i).val = k then offset + (Classical.choose h).val else missing

private lemma oe {n m : Nat} (u : Fin n) (v : Fin m) (k : Nat) :
    (oneEach u v).getD k false = true ↔ k = u.val ∨ k = n + v.val := by
  by_cases h : k < n
  · unfold oneEach
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff]
    omega
  · unfold oneEach
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    by_cases h2 : k-n < m
    · simp [List.getD_eq_getElem?_getD, h2, Fin.ext_iff]
      have := u.isLt
      omega
    · simp [List.getD_eq_getElem?_getD, h2]
      have := u.isLt
      have := v.isLt
      omega

private noncomputable def idx {n m a b : Nat} (f : Fin a → Fin n) (g : Fin b → Fin m)
    (s k : Nat) :=
  if k < n then pull f k 0 (a+b+s)
  else if k < n+m then pull g (k-n) a (a+b+s) else a+b+(k-(n+m))

private lemma raw {n m a b : Nat} (f : Fin a → Fin n) (g : Fin b → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (s k : Nat) (u : Fin a) (v : Fin b) :
    (oneEach u v).getD (idx f g s k) false = (oneEach (f u) (g v)).getD k false := by
  rw [Bool.eq_iff_iff, oe, oe]
  have hu := u.isLt
  have hv := v.isLt
  have hfu := (f u).isLt
  have hgv := (g v).isLt
  unfold idx
  split_ifs with h1 h2
  · unfold pull
    split_ifs with h
    · have hs := Classical.choose_spec h
      have hb := (Classical.choose h).isLt
      have he : (Classical.choose h).val = u.val ↔ k = (f u).val := by
        constructor
        · intro eq; exact hs.symm.trans (congrArg (fun x => (f x).val) (Fin.ext eq))
        · intro eq; exact congrArg Fin.val (hf (Fin.ext (hs.trans eq)))
      omega
    · have hx : k ≠ (f u).val := fun e => h ⟨u,e.symm⟩
      omega
  · unfold pull
    split_ifs with h
    · have hs := Classical.choose_spec h
      have he : (Classical.choose h).val = v.val ↔ k-n = (g v).val := by
        constructor
        · intro eq; exact hs.symm.trans (congrArg (fun x => (g x).val) (Fin.ext eq))
        · intro eq; exact congrArg Fin.val (hg (Fin.ext (hs.trans eq)))
      omega
    · have hx : k-n ≠ (g v).val := fun e => h ⟨v,e.symm⟩
      omega
  · omega

private lemma nextWire {n m a b : Nat} (f : Fin a → Fin n) (g : Fin b → Fin m)
    (s k t : Nat) (ht : t < s) :
    idx f g s k = a+b+t ↔ k = n+m+t := by
  unfold idx
  split_ifs with h1 h2
  · unfold pull
    split_ifs with h
    · have := (Classical.choose h).isLt; omega
    · omega
  · unfold pull
    split_ifs with h
    · have := (Classical.choose h).isLt; omega
    · omega
  · omega

private noncomputable def remap (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩

private lemma simW {n m a b : Nat} (f : Fin a → Fin n) (g : Fin b → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (s : Nat) (u : Fin a) (v : Fin b)
    (gs : List Gate) : gs.length ≤ s → ∀ k,
      (W (gs.map (remap (idx f g s))) (oneEach u v)).getD (idx f g s k) false =
      (W gs (oneEach (f u) (g v))).getD k false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ k => raw f g hf hg s k u v
  | append_singleton gs gate ih =>
    intro hsz k
    have ht : gs.length < s := by simpa using hsz
    have hlen {x y : Nat} (i : Fin x) (j : Fin y) : (oneEach i j).length = x+y := by simp [oneEach]
    simp only [List.map_append, List.map_cons, List.map_nil, W_snoc_getD, hlen, List.length_map]
    rw [if_congr (nextWire f g s k _ ht) rfl rfl]
    split_ifs
    · change gate.op.eval ((gate.inputs.map _).map _) = gate.op.eval (gate.inputs.map _)
      congr 1
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => ih ht.le i)
    · exact ih ht.le k

theorem main (n m a b : Nat) (A : Fin n → Fin m → Bool) (f : Fin a → Fin n) (g : Fin b → Fin m)
    (C : Circuit) (hf : Function.Injective f) (hg : Function.Injective g) (hc : FanInTwo C)
    (hr : Represents A C) : ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      Represents (fun u v => A (f u) (g v)) D := by
  let r := idx f g C.size
  refine ⟨⟨C.gates.map (remap r),r C.output⟩, ?_, ?_, ?_⟩
  · intro gate ht
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp ht
    simpa [remap] using hc g' hg'
  · simp [Circuit.size]
  · intro u v
    exact (simW f g hf hg C.size u v C.gates (le_refl _) C.output).trans (hr (f u) (g v))

end PEqualNP.Outside.L_meta_23955_aux

theorem PEqualNP.Outside.L_meta_23955 : (∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C') := PEqualNP.Outside.L_meta_23955_aux.main
