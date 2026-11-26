import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20838

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.Represents

def BitsLE (xs ys : List Bool) : Prop :=
  ∀ i, xs.getD i false = true → ys.getD i false = true

lemma append_mono {xs ys as bs : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (hab : BitsLE as bs) :
    BitsLE (xs ++ as) (ys ++ bs) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hab _ hi

lemma gate_mono {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (hxy : BitsLE xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨i, hi, rfl⟩
    exact hxy i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hxy i h⟩

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) :
    BitsLE (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · apply append_mono hlen hxy
      intro i hi
      cases i with
      | zero => exact gate_mono (hgs g List.mem_cons_self) hxy hi
      | succ i => simp at hi

lemma wire_true_mono {C : Circuit} (hC : Monotone2 C) {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (i : ℕ) :
    wireVal C xs i = true → wireVal C ys i = true := by
  apply fold_mono C.gates _ xs ys hlen hxy i
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

lemma ofFn_mono {n : ℕ} {f g : Fin n → Bool}
    (hfg : ∀ i, f i = true → g i = true) : BitsLE (List.ofFn f) (List.ofFn g) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    exact hfg ⟨i, h⟩ hi
  · have h' : (List.ofFn f).length ≤ i := by simpa using Nat.le_of_not_gt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hi
    cases hi

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (scan boolStep gs x).getD i false = (scan boolStep gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (scan boolStep gs x).length = j := by simp [scan_length, hx, j]
    have ey : (scan boolStep gs y).length = j := by simp [scan_length, hy, j]
    rw [scan_snoc, scan_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  show (scan boolStep C.gates (List.ofFn x)).getD C.output false =
    (scan boolStep C.gates (List.ofFn y)).getD C.output false
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private def inputBits (u v : Fin 5) (k : Fin 10) : Bool :=
  decide (k.val=u.val ∨ k.val=5+v.val)

private def erased (u v : Fin 5) (i k : Fin 10) : Bool :=
  if k=i then false else inputBits u v k

private theorem inputBits_list : ∀u v : Fin 5,List.ofFn (inputBits u v)=oneEach u v := by decide +kernel

private theorem separatingInputs : ∀i : Fin 10,∃u v a b : Fin 5,
    (32441377 : ℕ).testBit (5*u.val+v.val)=true ∧
    (32441377 : ℕ).testBit (5*a.val+b.val)=false ∧
    ∀k : Fin 10,erased u v i k=true → inputBits a b k=true := by decide +kernel

theorem lower : ¬PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32441377 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  rintro ⟨C,hm,small,rep⟩
  have onPair (u v : Fin 5) : circuitFun 10 C (inputBits u v)=(32441377 : ℕ).testBit (5*u.val+v.val) := by
    change C.eval (List.ofFn (inputBits u v))=_
    rw [inputBits_list]
    exact rep u v
  have all (i : Fin 10) : ∃x y : Fin 10→Bool,(∀j,j≠i → x j=y j) ∧ circuitFun 10 C x≠circuitFun 10 C y := by
    obtain ⟨u,v,a,b,one,zero,ext⟩ := separatingInputs i
    refine ⟨inputBits u v,erased u v i,fun j ne => by simp [erased,ne],?_⟩
    intro eq
    have sy : circuitFun 10 C (erased u v i)=true := eq ▸ (onPair u v).trans one
    have no := wire_true_mono hm (xs:=List.ofFn (erased u v i)) (ys:=List.ofFn (inputBits a b))
      (by simp) (ofFn_mono ext) C.output sy
    change circuitFun 10 C (inputBits a b)=true at no
    rw [onPair,zero] at no
    contradiction
  have bound := essential_bound C (fun g hg => (hm g hg).2) all
  omega

end PEqualNP.Outside.L_meta_20838

namespace PEqualNP.Outside.L_meta_20838

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [11, 5]⟩,
    ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [14, 8]⟩,
    ⟨.or, [15, 9]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [12, 17]⟩], 18⟩

set_option maxHeartbeats 1000000 in
theorem upper : RepSizeAtMost (fun u v : Fin 5 => (32441377 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  have strict : PEqualNP.TopForm.IsAO2 10 witness := by decide +kernel
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  exact ⟨by simpa using strict.1 g hg, (strict.2.2 g hg).le⟩

end PEqualNP.Outside.L_meta_20838

theorem PEqualNP.Outside.L_meta_20838 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32441377 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32441377 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_20838.upper, PEqualNP.Outside.L_meta_20838.lower⟩
