import Mathlib

import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_25236

namespace CubicRelabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gate (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def circuit (f : Nat → Nat) (c : Circuit) : Circuit := ⟨c.gates.map (gate f), f c.output⟩
def run (gs : List Gate) (x : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem snoc_ne (x : List Bool) (v : Bool) (i : Nat) (h : i ≠ x.length) :
    (x ++ [v]).getD i false = x.getD i false := by
  by_cases lt : i < x.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end CubicRelabel

namespace GraphRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open CubicRelabel (gate circuit run snoc_ne)

def wire {n m : Nat} (f : Fin n → Option (Fin m)) (gates i : Nat) : Nat :=
  if h : i < n then (f ⟨i,h⟩).elim (m+gates) Fin.val else m+(i-n)

theorem simulate {n m : Nat} (f : Fin n → Option (Fin m)) (total : Nat) (gs : List Gate)
    (used : Nat) (room : used+gs.length ≤ total) (x y : List Bool)
    (hx : x.length = n+used) (hy : y.length = m+used)
    (agree : ∀ i, y.getD (wire f total i) false = x.getD i false) :
    ∀ i, (run (gs.map (gate (wire f total))) y).getD (wire f total i) false = (run gs x).getD i false := by
  induction gs generalizing used x y with
  | nil => exact agree
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => x.getD i false)
    have same : (gate (wire f total) g).op.eval ((gate (wire f total) g).inputs.map fun i => y.getD i false) = v := by
      simp only [gate,List.map_map,Function.comp_def,agree,v]
    change ∀ i, (run (gs.map (gate (wire f total))) (y ++ [_])).getD (wire f total i) false =
      (run gs (x ++ [v])).getD i false
    rw [same]
    simp only [List.length_cons] at room
    apply ih (used+1) (by omega) (x++[v]) (y++[v]) (by simp [hx]; omega) (by simp [hy]; omega)
    intro i
    by_cases step : i=x.length
    · have eq : wire f total i = y.length := by simp [wire,step,hx,hy]
      rw [eq,step]
      simp
    · have ne : wire f total i ≠ y.length := by
        by_cases h : i<n
        · unfold wire
          rw [dite_eq_left h]
          cases e : f ⟨i,h⟩ with
          | none => change m+total ≠ y.length; omega
          | some j => change j.val ≠ y.length; have := j.isLt; omega
        · simp only [wire,dite_eq_right h]
          omega
      rw [snoc_ne _ _ _ ne,snoc_ne _ _ _ step,agree]

def raw {n m : Nat} (f : Fin n → Option (Fin m)) (x : List Bool) (i : Fin n) : Bool :=
  (f i).elim false (fun j => x.getD j.val false)

end GraphRestriction

namespace InducedMatrix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem get_pin {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]

theorem readLeft {n m : Nat} (u : Fin n) (v : Fin m) (p : Fin n) :
    (oneEach u v).getD p.val false = decide (p=u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using p.isLt)]
  exact get_pin _ p

theorem readRight {n m : Nat} (u : Fin n) (v : Fin m) (p : Fin m) :
    (oneEach u v).getD (n+p.val) false = decide (p=v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  exact get_pin _ p

end InducedMatrix

namespace CloneRow
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def firstValue (g : Gate) (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)

theorem prepend_gate {n m a b s : Nat} (A : Fin n → Fin m → Bool) (B : Fin a → Fin b → Bool)
    (r : Fin a → Fin n) (c : Fin b → Fin m) (g : Gate) (ok : g.op ∈ ({.and,.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : Fin (n+m) → Option (Fin (a+b+1)))
    (pins : ∀ i j p, let y := oneEach i j; GraphRestriction.raw f (y++[firstValue g y]) p = (oneEach (r i) (c j)).getD p.val false)
    (values : ∀ i j, A (r i) (c j) = B i j) (h : RepSizeAtMost A s) : RepSizeAtMost B (s+1) := by
  obtain ⟨C,leg,size,rep⟩ := h
  let ren := GraphRestriction.wire f C.size
  refine ⟨⟨g :: C.gates.map (CubicRelabel.gate ren),ren C.output⟩,?_,?_,?_⟩
  · intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact ok
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      simpa [CubicRelabel.gate] using leg u hu
  · change (g :: C.gates.map _).length ≤ s+1
    simpa [Circuit.size] using size
  · intro i j
    let x := oneEach (r i) (c j)
    let y := oneEach i j ++ [firstValue g (oneEach i j)]
    have hx : x.length = n+m := by simp [x,oneEach]
    have hy : y.length = a+b+1 := by simp [y,oneEach,Nat.add_assoc]
    have agree (p : Nat) : y.getD (ren p) false = x.getD p false := by
      by_cases lt : p<n+m
      · have he := pins i j ⟨p,lt⟩
        change GraphRestriction.raw f y ⟨p,lt⟩ = x.getD p false at he
        unfold GraphRestriction.raw at he
        simp only [ren,GraphRestriction.wire,dite_eq_left lt]
        cases e : f ⟨p,lt⟩ with
        | none => simp only [e,Option.elim_none] at he ⊢; rw [List.getD_eq_default _ _ (by omega)]; exact he
        | some v => simpa [e] using he
      · simp only [ren,GraphRestriction.wire,dite_eq_right lt]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have eq := GraphRestriction.simulate f C.size C.gates 0 (by simp [Circuit.size]) x y (by simpa using hx) (by simpa using hy) agree C.output
    exact eq.trans ((rep _ _).trans (values i j))

def foldRow {n : Nat} (u : Fin n) : Fin (n+1) → Fin n := Fin.lastCases u id
def graph {n m : Nat} (A : Fin n → Fin m → Bool) (u : Fin n) (i : Fin (n+1)) (j : Fin m) := A (foldRow u i) j
def merge {n : Nat} (u : Fin n) : Gate := ⟨.or,[u.val,n]⟩

def sources {n m : Nat} (u : Fin n) : Fin (n+m) → Option (Fin (n+1+m+1)) :=
  Fin.addCases (fun i => some (if i=u then Fin.last (n+1+m) else ⟨i.val,by have := i.isLt; omega⟩))
    (fun j => some ⟨n+1+j.val,by have := j.isLt; omega⟩)

theorem merge_value {n m : Nat} (u : Fin n) (v : Fin (n+1)) (j : Fin m) :
    firstValue (merge u) (oneEach v j) = (decide (u.castSucc=v) || decide (Fin.last n=v)) := by
  have h1 := InducedMatrix.readLeft v j u.castSucc
  have h2 := InducedMatrix.readLeft v j (Fin.last n)
  simp only [Fin.val_castSucc,Fin.val_last] at h1 h2
  simp only [merge,firstValue,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,h1,h2]

theorem row_bits {n : Nat} (u i : Fin n) (r : Fin (n+1)) :
    (if i=u then (decide (u.castSucc=r) || decide (Fin.last n=r)) else decide (i.castSucc=r)) = decide (i=foldRow u r) := by
  have diff (a : Fin n) : Fin.last n ≠ a.castSucc := by
    intro e
    have v := congrArg Fin.val e
    simp only [Fin.val_last,Fin.val_castSucc] at v
    have := a.isLt
    omega
  cases r using Fin.lastCases <;> by_cases hi : i=u <;> simp_all [foldRow]

theorem cloned_pins {n m : Nat} (u : Fin n) (v : Fin (n+1)) (j : Fin m) (p : Fin (n+m)) :
    GraphRestriction.raw (sources u) (oneEach v j ++ [firstValue (merge u) (oneEach v j)]) p =
      (oneEach (foldRow u v) j).getD p.val false := by
  have len : (oneEach v j).length = n+1+m := by simp [oneEach]; omega
  induction p using Fin.addCases with
  | left i =>
    simp only [GraphRestriction.raw,sources,Fin.addCases_left,Option.elim_some,Fin.val_castAdd,InducedMatrix.readLeft]
    rw [←row_bits u i v]
    by_cases eq : i=u
    · simp only [eq,ite_true,Fin.val_last]
      rw [←len]
      simpa using merge_value u v j
    · simp only [eq,ite_false]
      rw [List.getD_append _ _ _ _ (by have := i.isLt; omega)]
      exact InducedMatrix.readLeft v j i.castSucc
  | right idx =>
    simp only [GraphRestriction.raw,sources,Fin.addCases_right,Option.elim_some,Fin.val_natAdd,InducedMatrix.readRight]
    rw [List.getD_append _ _ _ _ (by have := idx.isLt; omega)]
    exact InducedMatrix.readRight v j idx

theorem upper {n m s : Nat} (A : Fin n → Fin m → Bool) (u : Fin n) (h : RepSizeAtMost A s) :
    RepSizeAtMost (graph A u) (s+1) :=
  prepend_gate A (graph A u) (foldRow u) id (merge u) (by simp [merge]) (sources u) (cloned_pins u) (fun _ _ => rfl) h

end CloneRow

namespace MatrixTranspose
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph {n m : Nat} (A : Fin n → Fin m → Bool) (j : Fin m) (i : Fin n) := A i j

def wire {n m : Nat} : Fin (n+m) → Option (Fin (m+n)) :=
  Fin.addCases (fun i => some (Fin.natAdd m i)) (fun j => some (j.castAdd n))

theorem samples {n m : Nat} (i : Fin n) (j : Fin m) (p : Fin (n+m)) :
    GraphRestriction.raw wire (oneEach j i) p = (oneEach i j).getD p.val false := by
  induction p using Fin.addCases with
  | left x => simp only [GraphRestriction.raw,wire,Fin.addCases_left,Option.elim_some,Fin.val_natAdd,Fin.val_castAdd,InducedMatrix.readRight,InducedMatrix.readLeft]
  | right y => simp only [GraphRestriction.raw,wire,Fin.addCases_right,Option.elim_some,Fin.val_castAdd,Fin.val_natAdd,InducedMatrix.readRight,InducedMatrix.readLeft]

theorem transfer {n m s : Nat} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) : RepSizeAtMost (graph A) s := by
  obtain ⟨C,leg,size,rep⟩ := h
  let f := @wire n m
  let ren := GraphRestriction.wire f C.size
  refine ⟨CubicRelabel.circuit ren C,?_,?_,?_⟩
  · intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    simpa [CubicRelabel.gate] using leg v hv
  · simpa [CubicRelabel.circuit,Circuit.size] using size
  · intro j i
    let x := oneEach i j
    let y := oneEach j i
    have hx : x.length = n+m := by simp [x,oneEach]
    have hy : y.length = m+n := by simp [y,oneEach]
    have agree (p : Nat) : y.getD (ren p) false = x.getD p false := by
      by_cases lt : p<n+m
      · have he := samples i j ⟨p,lt⟩
        change GraphRestriction.raw f y ⟨p,lt⟩ = x.getD p false at he
        unfold GraphRestriction.raw at he
        simp only [ren,GraphRestriction.wire,dite_eq_left lt]
        cases e : f ⟨p,lt⟩ with
        | none => simp only [e,Option.elim_none] at he ⊢; rw [List.getD_eq_default _ _ (by omega)]; exact he
        | some v => simpa [e] using he
      · simp only [ren,GraphRestriction.wire,dite_eq_right lt]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have eq := GraphRestriction.simulate f C.size C.gates 0 (by simp [Circuit.size]) x y (by simpa using hx) (by simpa using hy) agree C.output
    exact eq.trans (rep i j)

end MatrixTranspose

namespace Family25236
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def board (a b : Nat) (i : Fin a) (j : Fin b) :=
  decide ((i.val = 0 ∧ j.val ≠ 0) ∨ (i.val = 1 ∧ j.val = 0) ∨ (2 ≤ i.val ∧ j.val ≤ 1))

def seed : Circuit :=
  ⟨[⟨.or,[0,3]⟩,⟨.or,[1,4]⟩,⟨.or,[6,7]⟩,⟨.or,[7,5]⟩,⟨.and,[6,9]⟩,
    ⟨.or,[10,2]⟩,⟨.and,[8,11]⟩],12⟩

theorem base : RepSizeAtMost (board 3 3) 7 := by
  refine ⟨seed,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [seed,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem row_eq (n m : Nat) (hn : 3 ≤ n) :
    CloneRow.graph (board n m) ⟨2,by omega⟩ = board (n+1) m := by
  funext i j
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : 2 ≤ n := by omega
  cases i using Fin.lastCases <;>
    simp [CloneRow.graph,CloneRow.foldRow,board,h0,h1,h2]

theorem col_eq (r n : Nat) (hn : 3 ≤ n) :
    MatrixTranspose.graph (CloneRow.graph (MatrixTranspose.graph (board r n)) ⟨2,by omega⟩)
      = board r (n+1) := by
  funext i j
  have h0 : n ≠ 0 := by omega
  have h1 : ¬n ≤ 1 := by omega
  cases j using Fin.lastCases <;>
    simp [MatrixTranspose.graph,CloneRow.graph,CloneRow.foldRow,board,h0,h1]

theorem upper (n : Nat) (hn : 3 ≤ n) : RepSizeAtMost (board n n) (2*n+1) := by
  induction n, hn using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    have row := CloneRow.upper _ (⟨2,by omega⟩ : Fin n) ih
    rw [row_eq n n hn] at row
    have col := MatrixTranspose.transfer _ (CloneRow.upper _ (⟨2,by omega⟩ : Fin n)
      (MatrixTranspose.transfer _ row))
    rw [col_eq (n+1) n hn] at col
    convert col using 1

end Family25236

end PEqualNP.Outside.L_meta_25236


theorem PEqualNP.Outside.L_meta_25236 : (∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val ≤ 1))) (2 * n + 1)) := by
  exact PEqualNP.Outside.L_meta_25236.Family25236.upper
