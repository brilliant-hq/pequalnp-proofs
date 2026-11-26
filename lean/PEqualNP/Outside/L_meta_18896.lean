import PEqualNP.Defs

-- Prefix evaluation lemmas adapted from L-meta-18545 by rogatov.
namespace PEqualNP.Outside.L_meta_18896_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

def Shape (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
    gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < n + j

theorem shape_of {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Shape n C.gates := by
  intro j hj
  refine ⟨h.1 _ (List.getElem_mem _), h.2.2 _ (List.getElem_mem _), ?_⟩
  intro i hi
  apply h.2.1 j hj i
  simpa only [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi

theorem shape_to {n o : ℕ} {gs : List Gate} (h : Shape n gs) : IsAO2 n (⟨gs,o⟩ : Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    exact (h j hj).1
  · intro j hj i hi
    apply (h j hj).2.2 i
    simpa only [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    exact (h j hj).2.1

theorem shape_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (h : Shape n (gs ++ [g])) : Shape n gs := by
  intro j hj
  have z := h j (by simp; omega)
  have he : (gs ++ [g])[j]'(by simp; omega) = gs[j] := List.getElem_append_left hj
  rwa [he] at z

def Mask (m : ℕ) (gs : List Gate) (u : Option ℕ) : Prop :=
  ∀ i, u = some i → i < m + gs.length

def rval (ws : List Bool) (u : Option ℕ) : Bool :=
  u.elim false fun i => ws.getD i false

theorem extend_rval {m : ℕ} {gs extra : List Gate} {u : Option ℕ} {x : List Bool}
    (hx : x.length = m) (hu : Mask m gs u) :
    rval (run (gs ++ extra) x) u = rval (run gs x) u := by
  cases u with
  | none => rfl
  | some i =>
    exact run_prefix gs extra x i (by rw [hx]; exact hu i rfl)

def keepGate (op : GateOp) (m : ℕ) (gs : List Gate) (a b : Option ℕ) : List Gate × Option ℕ :=
  match a,b with
  | some i, some j => ([⟨op,[i,j]⟩], some (m + gs.length))
  | none, _ => ([], match op with | .or => b | _ => none)
  | _, none => ([], match op with | .or => a | _ => none)

theorem emit {op : GateOp} (hop : op = .and ∨ op = .or) {m : ℕ} {gs : List Gate}
    {a b : Option ℕ} (hgs : Shape m gs) (ha : Mask m gs a) (hb : Mask m gs b) :
    let (extra,r) := keepGate op m gs a b
    Shape m (gs ++ extra) ∧ Mask m (gs ++ extra) r ∧
    extra.length = (if a.isSome && b.isSome then 1 else 0) ∧
    r.isSome = op.eval [a.isSome,b.isSome] ∧
    ∀ y : List Bool, y.length = m →
      rval (run (gs ++ extra) y) r = op.eval [rval (run gs y) a,rval (run gs y) b] := by
  cases a with
  | none =>
    cases b with
    | none => rcases hop with rfl | rfl <;> simpa [keepGate, Mask, GateOp.eval, rval] using hgs
    | some j =>
      rcases hop with rfl | rfl
      · simpa [keepGate, Mask, GateOp.eval, rval] using hgs
      · simpa [keepGate, Mask, GateOp.eval, rval] using And.intro hgs hb
  | some i =>
    cases b with
    | none =>
      rcases hop with rfl | rfl
      · simpa [keepGate, Mask, GateOp.eval, rval] using hgs
      · simpa [keepGate, Mask, GateOp.eval, rval] using And.intro hgs ha
    | some j =>
      change Shape m (gs ++ [⟨op,[i,j]⟩]) ∧
        Mask m (gs ++ [⟨op,[i,j]⟩]) (some (m+gs.length)) ∧ 1 = 1 ∧
        true = op.eval [true,true] ∧ ∀ y, y.length = m →
          rval (run (gs ++ [⟨op,[i,j]⟩]) y) (some (m+gs.length)) =
            op.eval [rval (run gs y) (some i),rval (run gs y) (some j)]
      refine ⟨?_, by simp [Mask], rfl, ?_, ?_⟩
      · intro k hk
        by_cases h : k < gs.length
        · simpa only [List.getElem_append_left h] using hgs k h
        · have he : k = gs.length := by simp at hk; omega
          subst k
          have helem : (gs ++ [⟨op,[i,j]⟩])[gs.length]'(by simp) = (⟨op,[i,j]⟩ : Gate) := by simp
          simp only [helem, List.length_cons, List.length_nil, zero_add]
          refine ⟨hop, trivial, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact ha _ rfl
          · have := List.mem_singleton.mp hx
            subst x
            exact hb _ rfl
      · rcases hop with rfl|rfl <;> rfl
      · intro y hy
        have hlen : m + gs.length = (run gs y).length := by rw [run_length, hy]
        simp only [rval, Option.elim, run_snoc, hlen, getD_at, List.map_cons, List.map_nil]

def source {n m : ℕ} (p : Fin n → Option (Fin m)) (x : Fin m → Bool) : List Bool :=
  List.ofFn fun i => (p i).elim false x

def support {n m : ℕ} (p : Fin n → Option (Fin m)) : List Bool :=
  List.ofFn fun i => (p i).isSome

def countLive {n m : ℕ} (p : Fin n → Option (Fin m)) (gs : List Gate) : ℕ :=
  (gs.filter fun g => g.inputs.all fun i => (run gs (support p)).getD i false).length

theorem compile {n m : ℕ} (p : Fin n → Option (Fin m)) (gs : List Gate) (sh : Shape n gs) :
    ∃ ds : List Gate, Shape m ds ∧ ds.length ≤ countLive p gs ∧
      ∀ i, ∃ u : Option ℕ, Mask m ds u ∧ u.isSome = (run gs (support p)).getD i false ∧
        ∀ x : Fin m → Bool, rval (run ds (List.ofFn x)) u = (run gs (source p x)).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp [Shape], by simp [countLive], ?_⟩
    intro i
    by_cases hi : i < n
    · cases hp : p ⟨i,hi⟩ with
      | none =>
        refine ⟨none, by simp [Mask], ?_, ?_⟩
        · simp [run, support, List.getD_eq_getElem?_getD, hi, hp]
        · intro x
          simp [run, source, rval, List.getD_eq_getElem?_getD, hi, hp]
      | some v =>
        refine ⟨some v.val, by simp [Mask, v.isLt], ?_, ?_⟩
        · simp [run, support, List.getD_eq_getElem?_getD, hi, hp]
        · intro x
          simp [run, source, rval, List.getD_eq_getElem?_getD, hi, hp, v.isLt]
    · exact ⟨none, by simp [Mask], by simp [run, support, List.getD_eq_getElem?_getD, hi],
        fun x => by simp [run, source, rval, List.getD_eq_getElem?_getD, hi]⟩
  | append_singleton gs g ih =>
    have sh' := shape_prefix sh
    obtain ⟨ds, hd, cost, reps⟩ := ih sh'
    have gSh := sh gs.length (by simp)
    have gel : (gs ++ [g])[gs.length]'(by simp) = g := by simp
    rw [gel] at gSh
    obtain ⟨a,b,hin⟩ := List.length_eq_two.mp gSh.2.1
    have ha := gSh.2.2 a (by simp [hin])
    have hb := gSh.2.2 b (by simp [hin])
    obtain ⟨u,hu,huF,huX⟩ := reps a
    obtain ⟨v,hv,hvF,hvX⟩ := reps b
    generalize hresult : keepGate g.op m ds u v = res
    obtain ⟨extra,r⟩ := res
    have step := emit gSh.1 hd hu hv
    rw [hresult] at step
    obtain ⟨hd',hr,hcount,hflags,hvalues⟩ := step
    have sLen : (run gs (support p)).length = n + gs.length := by simp [run_length, support]
    have prefAgree (i : ℕ) (hi : i < n + gs.length) :
        (run (gs ++ [g]) (support p)).getD i false = (run gs (support p)).getD i false := by
      exact run_prefix _ _ _ _ (by simpa [support] using hi)
    have countStep : countLive p (gs ++ [g]) = countLive p gs + extra.length := by
      unfold countLive
      rw [List.filter_append, List.length_append]
      have same : gs.filter (fun q => q.inputs.all fun i =>
          (run (gs ++ [g]) (support p)).getD i false) =
          gs.filter (fun q => q.inputs.all fun i => (run gs (support p)).getD i false) := by
        apply List.filter_congr
        intro q hq
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hq
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        constructor <;> intro h i hi
        · rw [← prefAgree i (lt_of_lt_of_le ((sh' j hj).2.2 i hi) (by omega))]
          exact h i hi
        · rw [prefAgree i (lt_of_lt_of_le ((sh' j hj).2.2 i hi) (by omega))]
          exact h i hi
      rw [same, hcount, huF, hvF]
      simp only [List.filter_cons, hin, List.all_cons, List.all_nil, Bool.and_true,
        prefAgree a ha, prefAgree b hb, List.filter_nil]
      cases (run gs (support p)).getD a false <;>
        cases (run gs (support p)).getD b false <;> simp
    refine ⟨ds ++ extra, hd', ?_, ?_⟩
    · rw [List.length_append, countStep]
      omega
    · intro i
      by_cases hi : i < n + gs.length
      · obtain ⟨w,hw,hF,hX⟩ := reps i
        refine ⟨w, ?_, (prefAgree i hi).symm ▸ hF, ?_⟩
        · intro t ht
          have hb' := hw t ht
          simp only [List.length_append]
          omega
        · intro x
          rw [extend_rval (by simp : (List.ofFn x).length = m) hw, hX]
          exact (run_prefix _ _ _ _ (by simpa [source] using hi)).symm
      · by_cases he : i = n + gs.length
        · subst i
          refine ⟨r,hr,?_,?_⟩
          · rw [run_snoc, ← sLen, getD_at, hin, hflags, huF, hvF]
            rfl
          · intro x
            have srcLen : (run gs (source p x)).length = n + gs.length := by simp [run_length, source]
            rw [run_snoc, ← srcLen, getD_at, hin]
            rw [hvalues _ (by simp), huX x, hvX x]
            rfl
        · have ho : n + (gs ++ [g]).length ≤ i := by simp; omega
          refine ⟨none, by simp [Mask], ?_, ?_⟩
          · rw [List.getD_eq_default _ _ (by simpa [run_length,support] using ho)]
            rfl
          · intro x
            rw [List.getD_eq_default _ _ (by simpa [run_length,source] using ho)]
            rfl
end PEqualNP.Outside.L_meta_18896_aux

open PEqualNP.Outside.L_meta_18896_aux in
theorem PEqualNP.Outside.L_meta_18896 : (∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Option (Fin x2)),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x6 : List Bool := x3.wires (List.ofFn fun (x6 : Fin x1) => (x4 x6).isSome);     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x7 ∧ x7.size ≤ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.all fun (x9 : ℕ) => x6.getD x9 Bool.false) x3.gates).length ∧ ∀ (x8 : Fin x2 → Bool), x7.eval (List.ofFn x8) = x3.eval (List.ofFn fun (x9 : Fin x1) => (x4 x9).elim Bool.false x8)) := by
  intro n m C p hC
  dsimp only
  obtain ⟨ds, sh, hcost, reps⟩ := compile p C.gates (shape_of hC)
  obtain ⟨u, _, _, hua⟩ := reps C.output
  let o := u.getD (m + ds.length)
  refine ⟨⟨ds,o⟩, shape_to sh, hcost, ?_⟩
  intro x
  change (run ds (List.ofFn x)).getD o false = (run C.gates (source p x)).getD C.output false
  rw [← hua x]
  cases u with
  | some i => rfl
  | none =>
    change (run ds (List.ofFn x)).getD (m + ds.length) false = false
    exact List.getD_eq_default _ _ (by simp [run_length])
