import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl stepWire xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
      omega

theorem foldl_stepWire_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl stepWire xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire xs g) i (by simp [stepWire]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_append_add (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (i + p.length) false = w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

theorem oneEach_len (n : ℕ) (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.1) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  by_cases h : i = u.1
  · rw [decide_eq_true (Fin.ext h : (⟨i, hi⟩ : Fin n) = u), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

theorem oneEach_getD_right (n : ℕ) (u v : Fin n) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < 2 * n) :
    (oneEach u v).getD i false = decide (i - n = v.1) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hj : i - n < n := by omega
  by_cases h : i - n = v.1
  · rw [decide_eq_true (Fin.ext h : (⟨i - n, hj⟩ : Fin n) = v), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]


abbrev Sig (α : Type) := α → Bool

structure Net {α : Type} (input : α → List Bool) (N : ℕ) where
  gates : List Gate
  mono : Monotone2 ⟨gates, 0⟩
  len : ∀ z, (input z).length = N

variable {α : Type} {input : α → List Bool} {N : ℕ}

def Has (s : Net input N) (f : Sig α) : Prop :=
  ∃ w < N + s.gates.length, ∀ z, (s.gates.foldl stepWire (input z)).getD w false = f z

def Keeps (s t : Net input N) : Prop := ∀ {f : Sig α}, Has s f → Has t f

structure Ext (s t : Net input N) (cost : ℕ) : Prop where
  count : t.gates.length ≤ s.gates.length + cost
  keep : Keeps s t

theorem Ext.refl (s : Net input N) : Ext s s 0 :=
  ⟨by simp, fun h => h⟩

theorem Ext.trans {s t u : Net input N} {a b : ℕ} (h : Ext s t a) (g : Ext t u b) :
    Ext s u (a+b) :=
  ⟨by have := h.count; have := g.count; omega, fun hf => g.keep (h.keep hf)⟩

theorem Ext.mono {s t : Net input N} {a b : ℕ} (h : Ext s t a) (hle : a ≤ b) :
    Ext s t b := ⟨by have := h.count; omega, h.keep⟩

theorem gate_bin (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b)
    (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => op.eval [a z, b z]) := by
  obtain ⟨i, hi, hvi⟩ := ha
  obtain ⟨j, hj, hvj⟩ := hb
  let g : Gate := ⟨op, [i,j]⟩
  let t : Net input N := ⟨s.gates ++ [g], by
    intro e he
    change e ∈ s.gates ++ [g] at he
    rcases List.mem_append.mp he with old | new
    · exact s.mono e old
    · have eq : e = g := by simpa using new
      subst e
      exact ⟨hop, by simp [g]⟩, s.len⟩
  refine ⟨t, ⟨by simp [t], ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨w, hw, hv⟩ := hf
    refine ⟨w, by simp [t]; omega, ?_⟩
    intro z
    simpa only [t,List.foldl_append] using
      (foldl_stepWire_getD_lt [g] (s.gates.foldl stepWire (input z)) w
        (by simpa [foldl_stepWire_len,s.len] using hw)).trans (hv z)
  · refine ⟨N+s.gates.length, by simp [t], ?_⟩
    intro z
    change ((s.gates ++ [g]).foldl stepWire (input z)).getD _ false = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    rw [getD_snoc_self _ _ _ (by simp [foldl_stepWire_len,s.len])]
    change op.eval [(s.gates.foldl stepWire (input z)).getD i false, (s.gates.foldl stepWire (input z)).getD j false] = _
    rw [hvi,hvj]

theorem gate_or (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => a z || b z) := by
  simpa [GateOp.eval] using gate_bin s ha hb .or (by simp)

theorem gate_and (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => a z && b z) := by
  simpa [GateOp.eval] using gate_bin s ha hb .and (by simp)

theorem many {ι : Type} [Fintype ι] (s : Net input N) (f : ι → Sig α) (c : ℕ)
    (step : ∀ (i : ι) (u : Net input N), Keeps s u →
      ∃ v, Ext u v c ∧ Has v (f i)) :
    ∃ t, Ext s t (Fintype.card ι * c) ∧ ∀ i, Has t (f i) := by
  classical
  have loop (l : List ι) : ∃ t, Ext s t (l.length*c) ∧ ∀ i ∈ l, Has t (f i) := by
    induction l with
    | nil => exact ⟨s, by simpa using Ext.refl s, by simp⟩
    | cons a l ih =>
      obtain ⟨u,hu,hl⟩ := ih
      obtain ⟨v,hv,ha⟩ := step a u hu.keep
      refine ⟨v,by simpa [Nat.succ_mul] using hu.trans hv,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hv.keep (hl i hi)
  obtain ⟨v,hv,ha⟩ := loop (Finset.univ : Finset ι).toList
  exact ⟨v, by simpa using hv, fun i => ha i (by simp)⟩

theorem any_list {ι : Type} (s : Net input N) (f : ι → Sig α) (l : List ι)
    (hne : l ≠ []) (hs : ∀ i ∈ l, Has s (f i)) :
    ∃ t, Ext s t (l.length-1) ∧ Has t (fun z => l.any (fun i => f i z)) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => exact ⟨s, by simpa using Ext.refl s, by simpa using hs a (by simp)⟩
    | cons b bs =>
      obtain ⟨u,hu,hl⟩ := ih (by simp) (fun i hi => hs i (by simp [hi]))
      obtain ⟨v,hv,hh⟩ := gate_or u (hu.keep (hs a (by simp))) hl
      exact ⟨v, by simpa using hu.trans hv, by simpa using hh⟩

theorem any_family {ι : Type} [Fintype ι] [Nonempty ι] (s : Net input N)
    (f : ι → Sig α) (hs : ∀ i, Has s (f i)) :
    ∃ t, Ext s t (Fintype.card ι - 1) ∧
      Has t (fun z => decide (∃ i, f i z = true)) := by
  classical
  have hn : (Finset.univ : Finset ι).toList ≠ [] := by simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty
  obtain ⟨t,ht,hf⟩ := any_list s f _ hn (fun i _ => hs i)
  refine ⟨t, by simpa using ht, ?_⟩
  convert hf using 2
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]


theorem rawL {n : ℕ} (net : Net (fun z : Fin n × Fin n => oneEach z.1 z.2) (2*n))
    (k : ℕ) (hk : k<n) : Has net (fun z => decide (z.1.val=k)) := by
  refine ⟨k,by omega,?_⟩
  intro z
  rw [foldl_stepWire_getD_lt _ _ _ (by rw [oneEach_len]; omega)]
  simpa [eq_comm] using oneEach_getD_left n z.1 z.2 k hk

theorem rawR {n : ℕ} (net : Net (fun z : Fin n × Fin n => oneEach z.1 z.2) (2*n))
    (k : ℕ) (hk : k<n) : Has net (fun z => decide (z.2.val=k)) := by
  refine ⟨n+k,by omega,?_⟩
  intro z
  rw [foldl_stepWire_getD_lt _ _ _ (by rw [oneEach_len]; omega)]
  simpa [eq_comm] using oneEach_getD_right n z.1 z.2 (n+k) (by omega) (by omega)

end PEqualNP.Outside.L_meta_19402_aux

open PEqualNP.Outside.L_meta_19402_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19402 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) (2 * n + 1) := by
  intro n hn
  classical
  letI : Nonempty (Fin (n-2)) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (n-3)) := ⟨⟨0,by omega⟩⟩
  let s0 : Net (fun z : Fin n × Fin n => oneEach z.1 z.2) (2*n) :=
    ⟨[],by simp [Monotone2],fun z => oneEach_len n z.1 z.2⟩
  obtain ⟨s1,e1,r⟩ := any_family s0 (fun i : Fin (n-2) => fun z => decide (z.1.val=i.val+2))
    (fun i => rawL s0 (i.val+2) (by have := i.isLt; omega))
  have r' : Has s1 (fun z => decide (2≤z.1.val)) := by
    convert r using 2
    rename_i z
    simp only [decide_eq_true_eq, decide_eq_decide]
    constructor
    · intro h
      exact ⟨⟨z.1.val-2,by have := z.1.isLt; omega⟩,by simp; omega⟩
    · rintro ⟨i,hi⟩; omega

  obtain ⟨s2,e2,c⟩ := any_family s1 (fun i : Fin (n-3) => fun z => decide (z.2.val=i.val+3))
    (fun i => rawR s1 (i.val+3) (by have := i.isLt; omega))
  have c' : Has s2 (fun z => decide (3≤z.2.val)) := by
    convert c using 2
    rename_i z
    simp only [decide_eq_true_eq,decide_eq_decide]
    constructor
    · intro h
      exact ⟨⟨z.2.val-3,by have := z.2.isLt; omega⟩,by simp; omega⟩
    · rintro ⟨i,hi⟩; omega
  obtain ⟨s3,e3,r0⟩ := gate_or s2 (rawL s2 0 (by omega)) (e2.keep r')
  obtain ⟨s4,e4,r1⟩ := gate_or s3 (rawL s3 1 (by omega)) (e3.keep (e2.keep r'))
  obtain ⟨s5,e5,c12⟩ := gate_or s4 (rawR s4 1 (by omega)) (rawR s4 2 (by omega))
  obtain ⟨s6,e6,t1⟩ := gate_and s5 (e5.keep (e4.keep r0)) c12
  obtain ⟨s7,e7,t2⟩ := gate_and s6 (e6.keep (e5.keep r1)) (rawR s6 0 (by omega))
  obtain ⟨s8,e8,t3⟩ := gate_and s7 (rawL s7 1 (by omega)) (e7.keep (e6.keep (e5.keep (e4.keep (e3.keep c')))))
  obtain ⟨s9,e9,t12⟩ := gate_or s8 (e8.keep (e7.keep t1)) (e8.keep t2)
  obtain ⟨s10,e10,out⟩ := gate_or s9 t12 (e9.keep t3)
  obtain ⟨w,hw,hout⟩ := out
  refine ⟨⟨s10.gates,w⟩,s10.mono,?_,?_⟩
  · have h1:=e1.count; have h2:=e2.count; have h3:=e3.count; have h4:=e4.count
    have h5:=e5.count; have h6:=e6.count; have h7:=e7.count; have h8:=e8.count; have h9:=e9.count; have h10:=e10.count
    simp only [Fintype.card_fin] at h1 h2
    change s10.gates.length ≤ 2*n+1
    have : s0.gates.length=0 := rfl
    omega
  · intro u v
    change (s10.gates.foldl stepWire (oneEach u v)).getD w false = _
    rw [hout (u,v)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    have hu:=u.isLt
    have hv:=v.isLt
    omega
