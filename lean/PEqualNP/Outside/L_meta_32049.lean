import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32049_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc_lt (w : List Bool) (b : Bool) (m : ℕ) (hm : m < w.length) :
    (w ++ [b]).getD m false = w.getD m false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

theorem foldl_prefix (gs : List Gate) :
    ∀ (w : List Bool) (m : ℕ), m < w.length →
      (gs.foldl step w).getD m false = w.getD m false := by
  induction gs with
  | nil => intro w m _; rfl
  | cons g gs ih =>
    intro w m hm
    have hlt : m < (step w g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (step w g) m hlt]
    exact getD_snoc_lt w _ m hm

theorem getD_ofFn_fin7 (x : Fin 7 → Bool) (m : ℕ) (hm : m < 7) :
    (List.ofFn x).getD m false = x ⟨m, hm⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]

theorem list_any_true_of_mem {l : List Bool} (h : true ∈ l) : l.any id = true := by
  rw [List.any_eq_true]
  exact ⟨true, h, rfl⟩

theorem foldl_agree (h : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      h < w1.length →
      w1.getD h false = true →
      w2.getD h false = true →
      (∀ m, m ≠ 0 → w1.getD m false = w2.getD m false) →
      (∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ h ∈ g.inputs)) →
      ∀ m, m ≠ 0 → (gs.foldl step w1).getD m false = (gs.foldl step w2).getD m false := by
  induction gs with
  | nil =>
    intro w1 w2 _ _ _ _ hag _ m hm
    exact hag m hm
  | cons g gs ih =>
    intro w1 w2 hlen hhlt hw1 hw2 hag hgs m hm
    have hg := hgs g (List.mem_cons_self)
    have hgs' : ∀ g' ∈ gs, 0 ∉ g'.inputs ∨ (g'.op = GateOp.or ∧ h ∈ g'.inputs) :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hval : g.op.eval (g.inputs.map fun idx => w1.getD idx false) =
        g.op.eval (g.inputs.map fun idx => w2.getD idx false) := by
      rcases hg with h0 | ⟨hor, hmem⟩
      · congr 1
        apply List.map_congr_left
        intro idx hidx
        have hne : idx ≠ 0 := fun heq => h0 (heq ▸ hidx)
        exact hag idx hne
      · rw [hor]
        have h1 : true ∈ g.inputs.map (fun idx => w1.getD idx false) :=
          List.mem_map.mpr ⟨h, hmem, hw1⟩
        have h2 : true ∈ g.inputs.map (fun idx => w2.getD idx false) :=
          List.mem_map.mpr ⟨h, hmem, hw2⟩
        simp only [GateOp.eval]
        rw [list_any_true_of_mem h1, list_any_true_of_mem h2]
    have hlen' : (step w1 g).length = (step w2 g).length := by
      simp only [step, List.length_append, List.length_singleton, hlen]
    have hhlt' : h < (step w1 g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    have hw1' : (step w1 g).getD h false = true := by
      rw [step, getD_snoc_lt w1 _ h hhlt]; exact hw1
    have hw2' : (step w2 g).getD h false = true := by
      rw [step, getD_snoc_lt w2 _ h (hlen ▸ hhlt)]; exact hw2
    have hag' : ∀ k, k ≠ 0 → (step w1 g).getD k false = (step w2 g).getD k false := by
      intro k hk
      by_cases hlt : k < w1.length
      · rw [step, step, getD_snoc_lt w1 _ k hlt, getD_snoc_lt w2 _ k (hlen ▸ hlt)]
        exact hag k hk
      · by_cases heq : k = w1.length
        · subst heq
          rw [step, step, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (le_refl _), Nat.sub_self,
            hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
          simpa using hval
        · have hge1 : (step w1 g).length ≤ k := by
            simp only [step, List.length_append, List.length_singleton]
            omega
          have hge2 : (step w2 g).length ≤ k := by
            simp only [step, List.length_append, List.length_singleton]
            omega
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (step w1 g) (step w2 g) hlen' hhlt' hw1' hw2' hag' hgs' m hm

theorem eval_out_zero (C : Circuit) (x : Fin 7 → Bool) (ho : C.output = 0) :
    C.eval (List.ofFn x) = x 0 := by
  rw [Circuit.eval, ho, wires_eq_foldl, foldl_prefix C.gates (List.ofFn x) 0 (by simp)]
  exact getD_ofFn_fin7 x 0 (by omega)

theorem rule_out_mid (C : Circuit) (i : Fin C.gates.length) (h : ℕ)
    (heval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
       (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)))
    (huniq : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hor : (C.gates.get i).op = GateOp.or)
    (hmem : h ∈ (C.gates.get i).inputs)
    (hh7 : h < 7)
    (x1 x2 : Fin 7 → Bool)
    (hx1h : x1 ⟨h, hh7⟩ = true)
    (hx2h : x2 ⟨h, hh7⟩ = true)
    (hagree : ∀ j : Fin 7, j.val ≠ 0 → x1 j = x2 j)
    (hdiff : ((x1 0 && x1 1) || (x1 1 && x1 2) || (x1 2 && x1 3) ||
              (x1 3 && x1 4) || (x1 4 && x1 5) || (x1 5 && x1 6) || (x1 6 && x1 0)) ≠
             ((x2 0 && x2 1) || (x2 1 && x2 2) || (x2 2 && x2 3) ||
              (x2 3 && x2 4) || (x2 4 && x2 5) || (x2 5 && x2 6) || (x2 6 && x2 0))) :
    False := by
  by_cases ho : C.output = 0
  · have h0 := heval (fun j => decide (j.val = 0))
    rw [eval_out_zero C _ ho] at h0
    simp at h0
  · have hgs : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ h ∈ g.inputs) := by
      intro g hg
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      by_cases hj : 0 ∈ (C.gates.get j).inputs
      · right
        have hji : j = i := huniq j hj
        subst hji
        exact ⟨hor, hmem⟩
      · left
        exact hj
    have hw1 : (List.ofFn x1).getD h false = true := by
      rw [getD_ofFn_fin7 x1 h hh7]; exact hx1h
    have hw2 : (List.ofFn x2).getD h false = true := by
      rw [getD_ofFn_fin7 x2 h hh7]; exact hx2h
    have hag : ∀ m, m ≠ 0 → (List.ofFn x1).getD m false = (List.ofFn x2).getD m false := by
      intro m hm
      by_cases hm7 : m < 7
      · rw [getD_ofFn_fin7 x1 m hm7, getD_ofFn_fin7 x2 m hm7]
        exact hagree ⟨m, hm7⟩ hm
      · have hge : 7 ≤ m := by omega
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega : (List.ofFn x1).length ≤ m),
          List.getElem?_eq_none (by simp; omega : (List.ofFn x2).length ≤ m)]
    have heq : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
      rw [Circuit.eval, Circuit.eval, wires_eq_foldl, wires_eq_foldl]
      exact foldl_agree h C.gates (List.ofFn x1) (List.ofFn x2) (by simp) (by simp; omega)
        hw1 hw2 hag hgs C.output ho
    rw [heval x1, heval x2] at heq
    exact hdiff heq

theorem main :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
      (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
      0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
      7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
      (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
        (C.wires (List.ofFn x)).getD h false = true) →
      7 ≤ h := by
  intro C i k h _ _ heval _ huniq hor _ _ _ hmem hh0 _ hx
  by_contra hlt
  have hh7 : h < 7 := by omega
  obtain ⟨x, _, hx1, hx6, hwh⟩ := hx
  have hget : (C.wires (List.ofFn x)).getD h false = x ⟨h, hh7⟩ := by
    rw [wires_eq_foldl, foldl_prefix C.gates (List.ofFn x) h (by simp; omega)]
    exact getD_ofFn_fin7 x h hh7
  have hcase : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hget] at hwh
    exact Bool.false_ne_true (hx1.symm.trans hwh)
  · exact rule_out_mid C i 2 heval huniq hor hmem (by omega)
      (fun j => decide (j.val = 0 ∨ j.val = 2 ∨ j.val = 6))
      (fun j => decide (j.val = 2 ∨ j.val = 6))
      (by simp) (by simp)
      (by intro j hj; fin_cases j <;> simp_all) (by decide)
  · exact rule_out_mid C i 3 heval huniq hor hmem (by omega)
      (fun j => decide (j.val = 0 ∨ j.val = 1 ∨ j.val = 3))
      (fun j => decide (j.val = 1 ∨ j.val = 3))
      (by simp) (by simp)
      (by intro j hj; fin_cases j <;> simp_all) (by decide)
  · exact rule_out_mid C i 4 heval huniq hor hmem (by omega)
      (fun j => decide (j.val = 0 ∨ j.val = 1 ∨ j.val = 4))
      (fun j => decide (j.val = 1 ∨ j.val = 4))
      (by simp) (by simp)
      (by intro j hj; fin_cases j <;> simp_all) (by decide)
  · exact rule_out_mid C i 5 heval huniq hor hmem (by omega)
      (fun j => decide (j.val = 0 ∨ j.val = 1 ∨ j.val = 5))
      (fun j => decide (j.val = 1 ∨ j.val = 5))
      (by simp) (by simp)
      (by intro j hj; fin_cases j <;> simp_all) (by decide)
  · rw [hget] at hwh
    exact Bool.false_ne_true (hx6.symm.trans hwh)

end PEqualNP.Outside.L_meta_32049_aux

theorem PEqualNP.Outside.L_meta_32049 :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
      (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
      0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
      7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
      (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
        (C.wires (List.ofFn x)).getD h false = true) →
      7 ≤ h :=
  PEqualNP.Outside.L_meta_32049_aux.main
