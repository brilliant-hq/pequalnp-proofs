import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20542

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ (n : ℕ) : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [n, n + 1]⟩,
        ⟨GateOp.or, [0, n + 2]⟩,
        ⟨GateOp.or, [2 * n, 1]⟩,
        ⟨GateOp.or, [2 * n + 2, 2]⟩,
        ⟨GateOp.and, [2 * n + 1, 2 * n + 3]⟩,
        ⟨GateOp.not, [2 * n + 4]⟩,
        ⟨GateOp.or, [2 * n + 1, 2 * n + 2]⟩,
        ⟨GateOp.and, [2 * n + 6, 2 * n + 5]⟩ ],
    output := 2 * n + 7 }

lemma circ_fit (n : ℕ) : FanInTwo (circ n) := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_size (n : ℕ) : (circ n).size ≤ 8 := by
  simp [circ, Circuit.size]

lemma getD_append_lt {l₁ l₂ : List Bool} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_add {l₁ l₂ : List Bool} {k : ℕ} :
    (l₁ ++ l₂).getD (l₁.length + k) false = l₂.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

lemma oneEach_length {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach, Nat.two_mul]

lemma oneEach_left {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD k false = decide (u.val = k) := by
  unfold oneEach
  rw [getD_append_lt (by simp [hk])]
  simp [List.getD_eq_getElem?_getD, hk, Fin.ext_iff, eq_comm]

lemma oneEach_right {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (v.val = k) := by
  unfold oneEach
  have hlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp [hk, Fin.ext_iff, eq_comm]

lemma circ_eval {n : ℕ} (hn : 4 ≤ n) (u v : Fin n) :
    (circ n).eval (oneEach u v) =
      let x0 := decide (u.val = 0)
      let x1 := decide (u.val = 1)
      let x2 := decide (u.val = 2)
      let y0 := decide (v.val = 0)
      let y1 := decide (v.val = 1)
      let y2 := decide (v.val = 2)
      let cx := y0 || y1
      let a := x0 || y2
      let k := cx || x1
      (a || k) && !(a && (k || x2)) := by
  set x := oneEach u v
  have hxlen : x.length = 2 * n := oneEach_length u v
  have hx0 : x.getD 0 false = decide (u.val = 0) := oneEach_left u v (by omega)
  have hx1 : x.getD 1 false = decide (u.val = 1) := oneEach_left u v (by omega)
  have hx2 : x.getD 2 false = decide (u.val = 2) := oneEach_left u v (by omega)
  have hy0 : x.getD n false = decide (v.val = 0) := by
    simpa using oneEach_right u v (k := 0) (by omega)
  have hy1 : x.getD (n + 1) false = decide (v.val = 1) := oneEach_right u v (by omega)
  have hy2 : x.getD (n + 2) false = decide (v.val = 2) := oneEach_right u v (by omega)
  set cx := decide (v.val = 0) || decide (v.val = 1)
  set a := decide (u.val = 0) || decide (v.val = 2)
  set k := cx || decide (u.val = 1)
  set k2 := k || decide (u.val = 2)
  set ak2 := a && k2
  set nak2 := !ak2
  set aok := a || k
  set out := aok && nak2
  have hw : (circ n).wires x = x ++ [cx, a, k, k2, ak2, nak2, aok, out] := by
    unfold Circuit.wires circ
    dsimp only
    rw [List.foldl_cons]
    have h0 : x ++ [GateOp.eval GateOp.or (List.map (fun i => x.getD i false) [n, n + 1])] =
        x ++ [cx] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hy0, hy1]
    rw [h0, List.foldl_cons]
    have h1 : (x ++ [cx]) ++ [GateOp.eval GateOp.or (List.map (fun i => (x ++ [cx]).getD i false) [0, n + 2])] =
        x ++ [cx, a] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [getD_append_lt (by omega), getD_append_lt (by omega), hx0, hy2]
      simp [a]
    rw [h1, List.foldl_cons]
    have h2 : (x ++ [cx, a]) ++ [GateOp.eval GateOp.or (List.map (fun i => (x ++ [cx, a]).getD i false) [2 * n, 1])] =
        x ++ [cx, a, k] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h20 : (x ++ [cx, a]).getD (2 * n) false = cx := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a]) (k := 0)
      rw [h20, getD_append_lt (by omega), hx1]
      simp [k]
    rw [h2, List.foldl_cons]
    have h3 : (x ++ [cx, a, k]) ++ [GateOp.eval GateOp.or (List.map (fun i => (x ++ [cx, a, k]).getD i false) [2 * n + 2, 2])] =
        x ++ [cx, a, k, k2] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h30 : (x ++ [cx, a, k]).getD (2 * n + 2) false = k := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k]) (k := 2)
      rw [h30, getD_append_lt (by omega), hx2]
      simp [k2]
    rw [h3, List.foldl_cons]
    have h4 : (x ++ [cx, a, k, k2]) ++ [GateOp.eval GateOp.and (List.map (fun i => (x ++ [cx, a, k, k2]).getD i false) [2 * n + 1, 2 * n + 3])] =
        x ++ [cx, a, k, k2, ak2] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have h40 : (x ++ [cx, a, k, k2]).getD (2 * n + 1) false = a := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2]) (k := 1)
      have h41 : (x ++ [cx, a, k, k2]).getD (2 * n + 3) false = k2 := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2]) (k := 3)
      rw [h40, h41]
      simp [ak2]
    rw [h4, List.foldl_cons]
    have h5 : (x ++ [cx, a, k, k2, ak2]) ++ [GateOp.eval GateOp.not (List.map (fun i => (x ++ [cx, a, k, k2, ak2]).getD i false) [2 * n + 4])] =
        x ++ [cx, a, k, k2, ak2, nak2] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      have h50 : (x ++ [cx, a, k, k2, ak2]).getD (2 * n + 4) false = ak2 := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2]) (k := 4)
      rw [h50]
      simp [nak2]
    rw [h5, List.foldl_cons]
    have h6 : (x ++ [cx, a, k, k2, ak2, nak2]) ++ [GateOp.eval GateOp.or (List.map (fun i => (x ++ [cx, a, k, k2, ak2, nak2]).getD i false) [2 * n + 1, 2 * n + 2])] =
        x ++ [cx, a, k, k2, ak2, nak2, aok] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h60 : (x ++ [cx, a, k, k2, ak2, nak2]).getD (2 * n + 1) false = a := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2, nak2]) (k := 1)
      have h61 : (x ++ [cx, a, k, k2, ak2, nak2]).getD (2 * n + 2) false = k := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2, nak2]) (k := 2)
      rw [h60, h61]
      simp [aok]
    rw [h6, List.foldl_cons]
    have h7 : (x ++ [cx, a, k, k2, ak2, nak2, aok]) ++ [GateOp.eval GateOp.and (List.map (fun i => (x ++ [cx, a, k, k2, ak2, nak2, aok]).getD i false) [2 * n + 6, 2 * n + 5])] =
        x ++ [cx, a, k, k2, ak2, nak2, aok, out] := by
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have h70 : (x ++ [cx, a, k, k2, ak2, nak2, aok]).getD (2 * n + 6) false = aok := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2, nak2, aok]) (k := 6)
      have h71 : (x ++ [cx, a, k, k2, ak2, nak2, aok]).getD (2 * n + 5) false = nak2 := by
        simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2, nak2, aok]) (k := 5)
      rw [h70, h71]
      simp [out]
    rw [h7, List.foldl_nil]
  unfold Circuit.eval
  rw [hw]
  have hout : (x ++ [cx, a, k, k2, ak2, nak2, aok, out]).getD (2 * n + 7) false = out := by
    simpa [hxlen] using getD_append_add (l₁ := x) (l₂ := [cx, a, k, k2, ak2, nak2, aok, out]) (k := 7)
  simpa [circ] using hout

lemma circ_rep {n : ℕ} (hn : 4 ≤ n) :
    Represents (fun u v : Fin n => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))) (circ n) := by
  intro u v
  rw [circ_eval hn u v]
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  match u, v with
  | 0, 0 => simp
  | 0, 1 => simp
  | 0, 2 => simp
  | 0, _ + 3 => simp
  | 1, 0 => simp
  | 1, 1 => simp
  | 1, 2 => simp
  | 1, _ + 3 => simp
  | 2, 0 => simp
  | 2, 1 => simp
  | 2, 2 => simp
  | 2, _ + 3 => simp
  | _ + 3, 0 => simp
  | _ + 3, 1 => simp
  | _ + 3, 2 => simp
  | _ + 3, _ + 3 => simp

end PEqualNP.Outside.L_meta_20542

theorem PEqualNP.Outside.L_meta_20542 : (∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))) C) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_20542.circ n, PEqualNP.Outside.L_meta_20542.circ_fit n, PEqualNP.Outside.L_meta_20542.circ_size n, PEqualNP.Outside.L_meta_20542.circ_rep hn⟩
