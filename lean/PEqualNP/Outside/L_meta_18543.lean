import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18543_aux

open PEqualNP.CircuitLowerBounds

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.BlindGate

def push (D : Circuit) (op : GateOp) (i j : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨op,[i,j]⟩], 26+D.size⟩

def Good (D : Circuit) : Prop :=
  IsAO2 26 D ∧ ∀ g ∈ D.gates, g.inputs.Nodup

def V (D : Circuit) (w : ℕ) (f : (Fin 26 → Bool) → Bool) : Prop :=
  w < 26+D.size ∧ ∀ x, wireValue D 26 x w = f x

theorem sz (D : Circuit) (op : GateOp) (i j : ℕ) : (push D op i j).size = D.size+1 := by
  simp [push,Circuit.size]

theorem valid (D : Circuit) (op : GateOp) (i j : ℕ) (hD : Good D)
    (hop : op = .and ∨ op = .or) (hi : i < 26+D.size) (hj : j < 26+D.size) (hij : i ≠ j) :
    Good (push D op i j) := by
  obtain ⟨⟨ha,hb,hc⟩,hd⟩ := hD
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ha g hg
    · exact hop
  · intro t ht u hu
    by_cases het : t < D.gates.length
    · change u ∈ ((D.gates ++ [_]).getD t _).inputs at hu
      rw [getD_ltz _ _ _ _ het] at hu
      exact hb t het u hu
    · have e : t = D.gates.length := by change t < (D.gates ++ [_]).length at ht; simp at ht; omega
      subst t
      change u ∈ ((D.gates ++ [_]).getD D.gates.length _).inputs at hu
      rw [getD_at'] at hu
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl | rfl
      · exact hi
      · exact hj
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hc g hg
    · rfl
  · intro g hg
    simp only [push,List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hd g hg
    · simpa using hij

theorem old (D : Circuit) (op : GateOp) (i j : ℕ) {w f} (h : V D w f) :
    V (push D op i j) w f := by
  refine ⟨by rw [sz]; have := h.1; omega, fun x => ?_⟩
  change (run (D.gates ++ [_]) (List.ofFn x)).getD w false = _
  rw [run_prefix _ _ _ _ (by simpa [Circuit.size] using h.1)]
  exact h.2 x

theorem val (D : Circuit) (op : GateOp) (i j : ℕ) {f g} (h : V D i f) (k : V D j g) :
    V (push D op i j) (26+D.size) (fun x => op.eval [f x,g x]) := by
  refine ⟨by rw [sz]; omega, fun x => ?_⟩
  change (run (D.gates ++ [_]) (List.ofFn x)).getD (26+D.size) false = _
  rw [run_snoc,show 26+D.size = (run D.gates (List.ofFn x)).length by simp [run_length,Circuit.size], getD_at]
  change op.eval [wireValue D 26 x i, wireValue D 26 x j] = _
  rw [h.2 x,k.2 x]

theorem input (D : Circuit) (i : Fin 26) : V D i.val (fun x => x i) := by
  refine ⟨by have := i.isLt; omega, fun x => ?_⟩
  change (run D.gates (List.ofFn x)).getD i.val false = _
  rw [run_input _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]


theorem orE (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by simp [GateOp.eval]
theorem andE (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by simp [GateOp.eval]

open PEqualNP.HeptadCover in
theorem evalFour (p : Fin 13 → Bool) :
    decide (∃ i ∈ singerLines3 0, p i = true) = (p 0 || p 1 || p 3 || p 9) := by
  have hs : singerLines3 0 = {0,1,3,9} := by decide
  rw [hs]
  simp [Bool.or_assoc]

end PEqualNP.Outside.L_meta_18543_aux

open PEqualNP.Outside.L_meta_18543_aux PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.HeptadCover in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_18543 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →       x1.output < (26 : ℕ) + x1.size →         (∀ x6 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x6 < (26 : ℕ) + x1.size ∧ x2 x6 ≠ ↑x6) →           ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) (x9 : ℕ) (x10 : ℕ),             x7.size ≤ x1.size + (14 : ℕ) ∧               PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧                 (∀ x11 ∈ x7.gates, x11.inputs.Nodup) ∧                   x7.output = (26 : ℕ) + x8 ∧                     x7.gates[x8]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } ∧                       ∀ (x11 : Fin (26 : ℕ) → Bool),                         have x12 : Bool := Decidable.decide (∃ x12 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true);                         have x13 : Bool := Decidable.decide (∃ x13 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 (x2 x13) = Bool.true);                         have x14 : Bool := x1.eval (List.ofFn x11);                         PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x9 = (x14 || x12) ∧ PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x10 = (x14 || x13 || x11 (13 : Fin (26 : ℕ))) := by
  intro C h hao hnd ho hw
  have g0 : Good C := ⟨hao,hnd⟩
  have vx0 : V C 0 (fun x : Fin 26 → Bool => x 0) := input C (0 : Fin 26)
  have vx1 : V C 1 (fun x : Fin 26 → Bool => x 1) := input C (1 : Fin 26)
  have vx3 : V C 3 (fun x : Fin 26 → Bool => x 3) := input C (3 : Fin 26)
  have vx9 : V C 9 (fun x : Fin 26 → Bool => x 9) := input C (9 : Fin 26)
  have vx13 : V C 13 (fun x : Fin 26 → Bool => x 13) := input C (13 : Fin 26)
  have h0 := hw (0 : Fin 13) (by decide)
  have va0 : V C (h 0) (fun x => wireValue C 26 x (h 0)) := ⟨h0.1, fun _ => rfl⟩
  have h1 := hw (1 : Fin 13) (by decide)
  have va1 : V C (h 1) (fun x => wireValue C 26 x (h 1)) := ⟨h1.1, fun _ => rfl⟩
  have h3 := hw (3 : Fin 13) (by decide)
  have va3 : V C (h 3) (fun x => wireValue C 26 x (h 3)) := ⟨h3.1, fun _ => rfl⟩
  have h9 := hw (9 : Fin 13) (by decide)
  have va9 : V C (h 9) (fun x => wireValue C 26 x (h 9)) := ⟨h9.1, fun _ => rfl⟩
  have vout : V C C.output (fun x => C.eval (List.ofFn x)) := ⟨ho,fun _ => rfl⟩
  let D1 := push C .or 0 1
  have l0 : V C 0 (fun x : Fin 26 → Bool => x 0) := vx0
  have r0 : V C 1 (fun x : Fin 26 → Bool => x 1) := vx1
  have sz1 : D1.size = C.size+1 := by simp [D1,sz]
  have g1 : Good D1 := valid C .or _ _ g0 (by simp) l0.1 r0.1 (by omega)
  have up0 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V C w f) : V D1 w f := old C .or _ _ v
  have vt0 : V D1 (26+C.size+0) (fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) := by
    rw [show 26+C.size+0 = 26+C.size by omega]
    exact val C .or _ _ l0 r0
  let D2 := push D1 .or 3 9
  have l1 : V D1 3 (fun x : Fin 26 → Bool => x 3) := up0 (vx3)
  have r1 : V D1 9 (fun x : Fin 26 → Bool => x 9) := up0 (vx9)
  have sz2 : D2.size = C.size+2 := by simp [D2,sz,sz1]
  have g2 : Good D2 := valid D1 .or _ _ g1 (by simp) l1.1 r1.1 (by omega)
  have up1 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D1 w f) : V D2 w f := old D1 .or _ _ v
  have vt1 : V D2 (26+C.size+1) (fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) := by
    rw [show 26+C.size+1 = 26+D1.size by omega]
    exact val D1 .or _ _ l1 r1
  let D3 := push D2 .or (26+C.size+0) (26+C.size+1)
  have l2 : V D2 (26+C.size+0) (fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) := up1 (vt0)
  have r2 : V D2 (26+C.size+1) (fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) := vt1
  have sz3 : D3.size = C.size+3 := by simp [D3,sz,sz2]
  have g3 : Good D3 := valid D2 .or _ _ g2 (by simp) l2.1 r2.1 (by omega)
  have up2 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D2 w f) : V D3 w f := old D2 .or _ _ v
  have vt2 : V D3 (26+C.size+2) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) x,(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) x]) := by
    rw [show 26+C.size+2 = 26+D2.size by omega]
    exact val D2 .or _ _ l2 r2
  let D4 := push D3 .and 0 (h 0)
  have l3 : V D3 0 (fun x : Fin 26 → Bool => x 0) := up2 (up1 (up0 (vx0)))
  have r3 : V D3 (h 0) (fun x => wireValue C 26 x (h 0)) := up2 (up1 (up0 (va0)))
  have sz4 : D4.size = C.size+4 := by simp [D4,sz,sz3]
  have g4 : Good D4 := valid D3 .and _ _ g3 (by simp) l3.1 r3.1 (h0.2.symm)
  have up3 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D3 w f) : V D4 w f := old D3 .and _ _ v
  have vt3 : V D4 (26+C.size+3) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) := by
    rw [show 26+C.size+3 = 26+D3.size by omega]
    exact val D3 .and _ _ l3 r3
  let D5 := push D4 .and 1 (h 1)
  have l4 : V D4 1 (fun x : Fin 26 → Bool => x 1) := up3 (up2 (up1 (up0 (vx1))))
  have r4 : V D4 (h 1) (fun x => wireValue C 26 x (h 1)) := up3 (up2 (up1 (up0 (va1))))
  have sz5 : D5.size = C.size+5 := by simp [D5,sz,sz4]
  have g5 : Good D5 := valid D4 .and _ _ g4 (by simp) l4.1 r4.1 (h1.2.symm)
  have up4 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D4 w f) : V D5 w f := old D4 .and _ _ v
  have vt4 : V D5 (26+C.size+4) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) := by
    rw [show 26+C.size+4 = 26+D4.size by omega]
    exact val D4 .and _ _ l4 r4
  let D6 := push D5 .and 3 (h 3)
  have l5 : V D5 3 (fun x : Fin 26 → Bool => x 3) := up4 (up3 (up2 (up1 (up0 (vx3)))))
  have r5 : V D5 (h 3) (fun x => wireValue C 26 x (h 3)) := up4 (up3 (up2 (up1 (up0 (va3)))))
  have sz6 : D6.size = C.size+6 := by simp [D6,sz,sz5]
  have g6 : Good D6 := valid D5 .and _ _ g5 (by simp) l5.1 r5.1 (h3.2.symm)
  have up5 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D5 w f) : V D6 w f := old D5 .and _ _ v
  have vt5 : V D6 (26+C.size+5) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) := by
    rw [show 26+C.size+5 = 26+D5.size by omega]
    exact val D5 .and _ _ l5 r5
  let D7 := push D6 .and 9 (h 9)
  have l6 : V D6 9 (fun x : Fin 26 → Bool => x 9) := up5 (up4 (up3 (up2 (up1 (up0 (vx9))))))
  have r6 : V D6 (h 9) (fun x => wireValue C 26 x (h 9)) := up5 (up4 (up3 (up2 (up1 (up0 (va9))))))
  have sz7 : D7.size = C.size+7 := by simp [D7,sz,sz6]
  have g7 : Good D7 := valid D6 .and _ _ g6 (by simp) l6.1 r6.1 (h9.2.symm)
  have up6 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D6 w f) : V D7 w f := old D6 .and _ _ v
  have vt6 : V D7 (26+C.size+6) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) := by
    rw [show 26+C.size+6 = 26+D6.size by omega]
    exact val D6 .and _ _ l6 r6
  let D8 := push D7 .or (26+C.size+3) (26+C.size+4)
  have l7 : V D7 (26+C.size+3) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) := up6 (up5 (up4 (vt3)))
  have r7 : V D7 (26+C.size+4) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) := up6 (up5 (vt4))
  have sz8 : D8.size = C.size+8 := by simp [D8,sz,sz7]
  have g8 : Good D8 := valid D7 .or _ _ g7 (by simp) l7.1 r7.1 (by omega)
  have up7 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D7 w f) : V D8 w f := old D7 .or _ _ v
  have vt7 : V D8 (26+C.size+7) (fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) := by
    rw [show 26+C.size+7 = 26+D7.size by omega]
    exact val D7 .or _ _ l7 r7
  let D9 := push D8 .or (26+C.size+5) (26+C.size+6)
  have l8 : V D8 (26+C.size+5) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) := up7 (up6 (vt5))
  have r8 : V D8 (26+C.size+6) (fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) := up7 (vt6)
  have sz9 : D9.size = C.size+9 := by simp [D9,sz,sz8]
  have g9 : Good D9 := valid D8 .or _ _ g8 (by simp) l8.1 r8.1 (by omega)
  have up8 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D8 w f) : V D9 w f := old D8 .or _ _ v
  have vt8 : V D9 (26+C.size+8) (fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) := by
    rw [show 26+C.size+8 = 26+D8.size by omega]
    exact val D8 .or _ _ l8 r8
  let D10 := push D9 .or (26+C.size+7) (26+C.size+8)
  have l9 : V D9 (26+C.size+7) (fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) := up8 (vt7)
  have r9 : V D9 (26+C.size+8) (fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) := vt8
  have sz10 : D10.size = C.size+10 := by simp [D10,sz,sz9]
  have g10 : Good D10 := valid D9 .or _ _ g9 (by simp) l9.1 r9.1 (by omega)
  have up9 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D9 w f) : V D10 w f := old D9 .or _ _ v
  have vt9 : V D10 (26+C.size+9) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) := by
    rw [show 26+C.size+9 = 26+D9.size by omega]
    exact val D9 .or _ _ l9 r9
  let D11 := push D10 .or C.output (26+C.size+2)
  have l10 : V D10 C.output (fun x => C.eval (List.ofFn x)) := up9 (up8 (up7 (up6 (up5 (up4 (up3 (up2 (up1 (up0 (vout))))))))))
  have r10 : V D10 (26+C.size+2) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) x,(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) x]) := up9 (up8 (up7 (up6 (up5 (up4 (up3 (vt2)))))))
  have sz11 : D11.size = C.size+11 := by simp [D11,sz,sz10]
  have g11 : Good D11 := valid D10 .or _ _ g10 (by simp) l10.1 r10.1 (by omega)
  have up10 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D10 w f) : V D11 w f := old D10 .or _ _ v
  have vt10 : V D11 (26+C.size+10) (fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) x,(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) x]) x]) := by
    rw [show 26+C.size+10 = 26+D10.size by omega]
    exact val D10 .or _ _ l10 r10
  let D12 := push D11 .or C.output (26+C.size+9)
  have l11 : V D11 C.output (fun x => C.eval (List.ofFn x)) := up10 (up9 (up8 (up7 (up6 (up5 (up4 (up3 (up2 (up1 (up0 (vout)))))))))))
  have r11 : V D11 (26+C.size+9) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) := up10 (vt9)
  have sz12 : D12.size = C.size+12 := by simp [D12,sz,sz11]
  have g12 : Good D12 := valid D11 .or _ _ g11 (by simp) l11.1 r11.1 (by omega)
  have up11 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D11 w f) : V D12 w f := old D11 .or _ _ v
  have vt11 : V D12 (26+C.size+11) (fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) x]) := by
    rw [show 26+C.size+11 = 26+D11.size by omega]
    exact val D11 .or _ _ l11 r11
  let D13 := push D12 .or (26+C.size+11) 13
  have l12 : V D12 (26+C.size+11) (fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) x]) := vt11
  have r12 : V D12 13 (fun x : Fin 26 → Bool => x 13) := up11 (up10 (up9 (up8 (up7 (up6 (up5 (up4 (up3 (up2 (up1 (up0 (vx13))))))))))))
  have sz13 : D13.size = C.size+13 := by simp [D13,sz,sz12]
  have g13 : Good D13 := valid D12 .or _ _ g12 (by simp) l12.1 r12.1 (by omega)
  have up12 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D12 w f) : V D13 w f := old D12 .or _ _ v
  have vt12 : V D13 (26+C.size+12) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) x]) x,(fun x : Fin 26 → Bool => x 13) x]) := by
    rw [show 26+C.size+12 = 26+D12.size by omega]
    exact val D12 .or _ _ l12 r12
  let D14 := push D13 .and (26+C.size+10) (26+C.size+12)
  have l13 : V D13 (26+C.size+10) (fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) x,(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) x]) x]) := up12 (up11 (vt10))
  have r13 : V D13 (26+C.size+12) (fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) x]) x,(fun x : Fin 26 → Bool => x 13) x]) := vt12
  have sz14 : D14.size = C.size+14 := by simp [D14,sz,sz13]
  have g14 : Good D14 := valid D13 .and _ _ g13 (by simp) l13.1 r13.1 (by omega)
  have up13 {w : ℕ} {f : (Fin 26 → Bool) → Bool} (v : V D13 w f) : V D14 w f := old D13 .and _ _ v
  have vt13 : V D14 (26+C.size+13) (fun x => GateOp.and.eval [(fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x : Fin 26 → Bool => x 1) x]) x,(fun x => GateOp.or.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x : Fin 26 → Bool => x 9) x]) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => C.eval (List.ofFn x)) x,(fun x => GateOp.or.eval [(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 0) x,(fun x => wireValue C 26 x (h 0)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 1) x,(fun x => wireValue C 26 x (h 1)) x]) x]) x,(fun x => GateOp.or.eval [(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 3) x,(fun x => wireValue C 26 x (h 3)) x]) x,(fun x => GateOp.and.eval [(fun x : Fin 26 → Bool => x 9) x,(fun x => wireValue C 26 x (h 9)) x]) x]) x]) x]) x,(fun x : Fin 26 → Bool => x 13) x]) x]) := by
    rw [show 26+C.size+13 = 26+D13.size by omega]
    exact val D13 .and _ _ l13 r13
  refine ⟨D14,C.size+13,26+C.size+10,26+C.size+12,by omega,g14.1,g14.2,?_,?_,?_⟩
  · change 26+D13.size = _
    omega
  · change (D13.gates ++ [_])[C.size+13]? = _
    rw [show C.size+13=D13.gates.length from sz13.symm]
    simp
  · intro x hpts hpairs hout
    have hs : singerLines3 0 = {0,1,3,9} := by decide
    have hleft := (up13 (up12 (up11 vt10))).2 x
    have hright := (up13 vt12).2 x
    let p := fun i : Fin 13 => x (Fin.castAdd 13 i)
    let q := fun i : Fin 13 => p i && wireValue C 26 x (h i)
    have hp : hpts = (x 0 || x 1 || x 3 || x 9) := evalFour p
    have hq : hpairs = (q 0 || q 1 || q 3 || q 9) := by
      change decide (∃ i ∈ singerLines3 0, p i = true ∧ wireValue C 26 x (h i) = true) = _
      simpa only [q,Bool.and_eq_true] using evalFour q
    constructor
    · rw [hleft,hp]
      simp only [orE,andE]
      change (hout || ((x 0 || x 1) || (x 3 || x 9))) = _
      ac_rfl
    · rw [hright,hq]
      simp only [orE,andE]
      change ((hout || ((q 0 || q 1) || (q 3 || q 9))) || x 13) = _
      ac_rfl
