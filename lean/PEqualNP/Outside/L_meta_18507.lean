import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18507_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

def shifted (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (k + ·)⟩

lemma readAfter (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (p.length+i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma run_shift (p w : List Bool) (gs : List Gate) :
    run (gs.map (shifted p.length)) (p ++ w) = p ++ run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have h : (shifted p.length g).op.eval ((shifted p.length g).inputs.map fun i => (p ++ w).getD i false) = b := by
      simp only [shifted, List.map_map, Function.comp_def, readAfter, b]
    change run (gs.map (shifted p.length)) ((p ++ w) ++ [_]) = p ++ run gs (w ++ [b])
    rw [h, List.append_assoc, ih]

lemma readBefore (p w : List Bool) (i : ℕ) (h : i < p.length) :
    (p ++ w).getD i false = p.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

def mk {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Gate :=
  ⟨.or, [i.val, n + (π i).val]⟩

def joint {n : ℕ} (π : Equiv.Perm (Fin n)) (u v i : Fin n) : Bool :=
  decide (i = u ∨ i = π.symm v)

lemma run_first {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) (l : List (Fin n)) (acc : List Bool) :
    run (l.map (mk π)) (oneEach u v ++ acc) = oneEach u v ++ (acc ++ l.map (joint π u v)) := by
  induction l generalizing acc with
  | nil => simp [run]
  | cons i l ih =>
    have left : (oneEach u v ++ acc).getD i.val false = decide (i = u) := by
      rw [readBefore _ _ _ (by simp [oneEach]; omega)]
      rw [oneEach, readBefore _ _ _ (by simp)]
      simp [List.getD]
    have right : (oneEach u v ++ acc).getD (n+(π i).val) false = decide (π i = v) := by
      rw [readBefore _ _ _ (by simp [oneEach])]
      rw [oneEach, List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD]
    have hg : (mk π i).op.eval ((mk π i).inputs.map fun j => (oneEach u v ++ acc).getD j false) = joint π u v i := by
      change ((oneEach u v ++ acc).getD i.val false || ((oneEach u v ++ acc).getD (n+(π i).val) false || false)) = _
      rw [left, right]
      simp [joint,π.eq_symm_apply]
    change run (l.map (mk π)) ((oneEach u v ++ acc) ++ [_]) = _
    rw [hg, List.append_assoc, ih]
    simp

end PEqualNP.Outside.L_meta_18507_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_18507_aux

theorem PEqualNP.Outside.L_meta_18507 : ∀ (n s : ℕ) (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)), (∀ a b, H a b = H b a) → (∀ a, H a a = false) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ (∀ a : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = a)) = false) ∧ (∀ a b : Fin n, a ≠ b → C.eval (List.ofFn fun i : Fin n => decide (i = a ∨ i = b)) = H a b)) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => H u (π.symm v)) (n + s) := by
  intro n s H π _ hloop ⟨C,hgood,hsize,hsingle,hpair⟩
  let gs := (List.ofFn (mk π)) ++ C.gates.map (shifted (n+n))
  refine ⟨⟨gs,n+n+C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ (List.ofFn (mk π)) ++ C.gates.map (shifted (n+n)) at hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      exact ⟨by simp [mk], by simp [mk]⟩
    · obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp h
      exact ⟨(hgood g hmem).1, by simpa [shifted] using (hgood g hmem).2⟩
  · change gs.length ≤ n+s
    simpa [gs,Circuit.size] using Nat.add_le_add_left hsize n
  · intro u v
    let p := oneEach u v
    have plen : p.length = n+n := by simp [p,oneEach]
    have hfirst : run (List.ofFn (mk π)) p = p ++ List.ofFn (joint π u v) := by
      simpa [p,List.map_ofFn,Function.comp_def] using run_first π u v (List.ofFn id) []
    change (run gs p).getD (n+n+C.output) false = _
    change ((List.ofFn (mk π) ++ C.gates.map (shifted (n+n))).foldl _ p).getD _ _ = _
    rw [List.foldl_append]
    change (run (C.gates.map (shifted (n+n))) (run (List.ofFn (mk π)) p)).getD _ _ = _
    rw [hfirst, ← plen, run_shift, readAfter]
    change C.eval (List.ofFn (joint π u v)) = H u (π.symm v)
    by_cases h : u = π.symm v
    · change C.eval (List.ofFn fun i => decide (i = u ∨ i = π.symm v)) = H u (π.symm v)
      simpa [← h,hloop] using hsingle u
    · exact hpair _ _ h
