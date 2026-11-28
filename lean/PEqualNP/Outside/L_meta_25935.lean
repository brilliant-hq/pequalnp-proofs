import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25935
namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def permWire (n : ℕ) (π : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then ↑(π ⟨w, h⟩) else w

def ordered (op : GateOp) (l : List ℕ) : List ℕ :=
  match op, l with
  | .and, [a,b] | .or, [a,b] => [min a b, max a b]
  | _, _ => l

lemma ordered_eval (op : GateOp) (l : List ℕ) (w : ℕ → Bool) :
    op.eval ((ordered op l).map w) = op.eval (l.map w) := by
  rcases l with _ | ⟨a,t⟩
  · cases op <;> rfl
  rcases t with _ | ⟨b,t⟩
  · cases op <;> rfl
  cases t with
  | cons c t => cases op <;> rfl
  | nil =>
    by_cases h : a ≤ b
    · cases op <;> simp [ordered, min_eq_left h, max_eq_right h]
    · have hb := Nat.le_of_not_ge h
      cases op <;> simp [ordered, min_eq_right hb, max_eq_left hb, GateOp.eval,
        Bool.and_comm, Bool.or_comm]

lemma ordered_mem (op : GateOp) (l : List ℕ) (i : ℕ) :
    i ∈ ordered op l ↔ i ∈ l := by
  rcases l with _ | ⟨a,t⟩
  · cases op <;> rfl
  rcases t with _ | ⟨b,t⟩
  · cases op <;> rfl
  cases t with
  | cons c t => cases op <;> rfl
  | nil =>
    by_cases h : a ≤ b
    · cases op <;> simp [ordered, min_eq_left h, max_eq_right h]
    · have hb := Nat.le_of_not_ge h
      cases op <;> simp [ordered, min_eq_right hb, max_eq_left hb, or_comm]

def permGate (n : ℕ) (π : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  { op := g.op, inputs := ordered g.op (g.inputs.map (permWire n π)) }

def permCircuit (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permGate n π), output := permWire n π C.output }

lemma permWire_lt (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    permWire n π w < n := by
  simp only [permWire, h, ↓reduceDIte]
  exact (π ⟨w, h⟩).isLt

lemma permWire_ge (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) :
    permWire n π w = w := by
  have hlt : ¬ w < n := Nat.not_lt.mpr h
  simp only [permWire, hlt, ↓reduceDIte]

lemma getD_append_singleton_lt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i dflt = l.getD i dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_singleton_eq {α : Type*} (l : List α) (v dflt : α) :
    (l ++ [v]).getD l.length dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma getD_append_singleton_gt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : l.length < i) :
    (l ++ [v]).getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD]
  have hge : (l ++ [v]).length ≤ i := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [List.getElem?_eq_none hge]
  rfl

lemma getD_ge_length {α : Type*} (l : List α) (dflt : α) {i : ℕ} (h : l.length ≤ i) :
    l.getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma foldl_perm_eq {α : Type*} (n : ℕ) (π : Equiv.Perm (Fin n)) (dflt : α)
    (val : Gate → List α → α)
    (hval : ∀ g (acc5 acc1 : List α),
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      val (permGate n π g) acc5 = val g acc1)
    (gs : List Gate) :
    ∀ (acc5 acc1 : List α),
      acc5.length = acc1.length →
      n ≤ acc1.length →
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).length =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).length ∧
      ∀ w, ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).getD
        (permWire n π w) dflt =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).getD w dflt := by
  induction gs with
  | nil =>
    intro acc5 acc1 hlen _ hacc
    exact ⟨hlen, hacc⟩
  | cons g t ih =>
    intro acc5 acc1 hlen hn hacc
    simp only [List.map_cons, List.foldl_cons]
    have hv : val (permGate n π g) acc5 = val g acc1 := hval g acc5 acc1 hacc
    rw [hv]
    apply ih
    · simp only [List.length_append, List.length_singleton, hlen]
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro w
      rcases Nat.lt_trichotomy w acc1.length with hwlt | rfl | hwgt
      · have hpwlt : permWire n π w < acc5.length := by
          by_cases hwn : w < n
          · have h1 := permWire_lt n π hwn
            omega
          · rw [permWire_ge n π (Nat.le_of_not_lt hwn)]
            omega
        rw [getD_append_singleton_lt acc5 _ dflt hpwlt,
            getD_append_singleton_lt acc1 _ dflt hwlt, hacc w]
      · have hpweq : permWire n π acc1.length = acc1.length := permWire_ge n π hn
        rw [hpweq, ← hlen, getD_append_singleton_eq, hlen, getD_append_singleton_eq]
      · have hpwgt : acc5.length < permWire n π w := by
          have hnw : n ≤ w := by omega
          rw [permWire_ge n π hnw]
          omega
        rw [getD_append_singleton_gt acc5 _ dflt hpwgt,
            getD_append_singleton_gt acc1 _ dflt hwgt]

lemma wires_permCircuit (C : Circuit) (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    ∀ w, ((permCircuit n π C).wires (List.ofFn x)).getD (permWire n π w) false = (C.wires (List.ofFn (x ∘ ⇑π))).getD w false := by
  unfold Circuit.wires
  intro w
  change ((C.gates.map (permGate n π)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD (permWire n π w) false =
    (C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (x ∘ ⇑π))).getD w false
  have h := foldl_perm_eq n π false
    (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false))
    (fun g acc5 acc1 hacc => by
      change g.op.eval ((ordered g.op (g.inputs.map (permWire n π))).map _) = _
      rw [ordered_eval]
      simp only [List.map_map, Function.comp_def, hacc])
    C.gates
    (List.ofFn x)
    (List.ofFn (x ∘ ⇑π))
    (by simp)
    (by simp)
    (by
      intro w
      by_cases hw : w < n
      · have hpw : permWire n π w = (π ⟨w, hw⟩).val := by simp [permWire, hw]
        have hpwlt : (π ⟨w, hw⟩).val < n := (π ⟨w, hw⟩).isLt
        rw [hpw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        simp [hpwlt, hw]
      · have hnw : n ≤ w := Nat.le_of_not_lt hw
        rw [permWire_ge n π hnw, getD_ge_length _ false (by simp; exact hnw),
            getD_ge_length _ false (by simp; exact hnw)])
  exact h.2 w

end Core
end PEqualNP.Outside.L_meta_25935

namespace PEqualNP.Outside.L_meta_25935
namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev X := Fin 9 → Bool
def wv (C : Circuit) (x : X) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
def pm (x : X) := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
def Shape (j : ℕ) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, a < 9+j ∧ g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < 9+j ∧ g.inputs = [a,b])
def Normal (C : Circuit) : Prop :=
  (∀ j : Fin C.gates.length, Shape j (C.gates.get j)) ∧
  (∀ j : Fin C.gates.length,
    (∃ x y, wv C x (9+j.val) ≠ wv C y (9+j.val)) ∧
    ∀ k, k < 9+j.val → ∃ x, wv C x (9+j.val) ≠ wv C x k) ∧
  (∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
    ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)

abbrev Wire (π : Equiv.Perm (Fin 9)) := permWire 9 π
abbrev Gate' (π : Equiv.Perm (Fin 9)) := permGate 9 π
abbrev Circ (π : Equiv.Perm (Fin 9)) := permCircuit 9 π

lemma wireInv (π : Equiv.Perm (Fin 9)) (w : ℕ) : Wire π.symm (Wire π w) = w := by
  change permWire 9 π.symm (permWire 9 π w) = w
  by_cases h : w < 9
  · simp [permWire, h, (π ⟨w,h⟩).isLt]
  · rw [permWire_ge 9 π (by omega), permWire_ge 9 π.symm (by omega)]

lemma wireBound (π : Equiv.Perm (Fin 9)) {w j : ℕ} (h : w < 9+j) : Wire π w < 9+j := by
  change permWire 9 π w < 9+j
  by_cases hr : w < 9
  · have := permWire_lt 9 π hr
    omega
  · rw [permWire_ge 9 π (by omega)]
    exact h

lemma wireInj (π : Equiv.Perm (Fin 9)) : Function.Injective (Wire π) :=
  fun a b h => (wireInv π a).symm.trans ((congrArg (Wire π.symm) h).trans (wireInv π b))

lemma shapeMap (π : Equiv.Perm (Fin 9)) {g : Gate} {j : ℕ} (h : Shape j g) :
    Shape j (Gate' π g) := by
  rcases h with ⟨op,a,ha,ins⟩ | ⟨op,a,b,hab,hb,ins⟩
  · exact Or.inl ⟨op,Wire π a,wireBound π ha,by simp [permGate,op,ins,ordered]⟩
  · have ha := wireBound π (hab.trans hb)
    have hb' := wireBound π hb
    have ne : Wire π a ≠ Wire π b := fun he => hab.ne (wireInj π he)
    refine Or.inr ⟨op, min (Wire π a) (Wire π b),max (Wire π a) (Wire π b),?_,?_,?_⟩
    · omega
    · omega
    · rcases op with op|op <;> simp [permGate,ins,op,ordered]

lemma getGate (π : Equiv.Perm (Fin 9)) (C : Circuit) (j : Fin (Circ π C).gates.length) :
    (Circ π C).gates.get j = Gate' π (C.gates.get ⟨j.val,by simpa [permCircuit] using j.isLt⟩) := by
  simp [permCircuit, List.get_eq_getElem]

lemma allFan {C : Circuit} (h : Normal C) : FanInTwo C := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨op,a,_,ins⟩ | ⟨op,a,b,_,_,ins⟩ := h.1 ⟨i,hi⟩
  · simp_all [List.get_eq_getElem]
  · rcases op with op|op <;> simp_all [List.get_eq_getElem]

lemma valMap (π : Equiv.Perm (Fin 9)) (C : Circuit) (x : X) (w : ℕ) :
    wv (Circ π C) (x ∘ π.symm) (Wire π w) = wv C x w := by
  have h := wires_permCircuit C 9 π (x ∘ π.symm) w
  simpa [wv, Function.comp_assoc] using h

lemma valGate (π : Equiv.Perm (Fin 9)) (C : Circuit) (x : X) (j : ℕ) :
    wv (Circ π C) (x ∘ π.symm) (9+j) = wv C x (9+j) := by
  simpa only [Wire, permWire_ge 9 π (by omega : 9 ≤ 9+j)] using valMap π C x (9+j)

lemma normalMap (π : Equiv.Perm (Fin 9)) (C : Circuit) (h : Normal C) : Normal (Circ π C) := by
  have len : (Circ π C).gates.length = C.gates.length := by simp [permCircuit]
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [getGate]
    exact shapeMap π (h.1 _)
  · intro j
    let i : Fin C.gates.length := ⟨j, len ▸ j.isLt⟩
    obtain ⟨⟨x,y,ne⟩, earlier⟩ := h.2.1 i
    constructor
    · exact ⟨x ∘ π.symm, y ∘ π.symm, by simpa only [valGate] using ne⟩
    · intro k hk
      obtain ⟨x,hx⟩ := earlier (Wire π.symm k) (wireBound π.symm hk)
      refine ⟨x ∘ π.symm, ?_⟩
      have he := valMap π C x (Wire π.symm k)
      rw [show Wire π (Wire π.symm k) = k from wireInv π.symm k] at he
      rwa [valGate, he]
  · intro j hj
    let i : Fin C.gates.length := ⟨j, len ▸ j.isLt⟩
    obtain ⟨k,hk,hm⟩ := h.2.2 i (by simpa only [i,len] using hj)
    refine ⟨⟨k, len.symm ▸ k.isLt⟩, hk, ?_⟩
    rw [getGate]
    apply (ordered_mem ..).mpr
    exact List.mem_map.mpr ⟨9+j.val, hm, permWire_ge 9 π (by omega)⟩

lemma computesMap (π : Equiv.Perm (Fin 9)) (hp : ∀ x : X, pm (x ∘ π) = pm x)
    {C : Circuit} (hc : ∀ x : X, C.eval (List.ofFn x) = pm x) :
    ∀ x : X, (Circ π C).eval (List.ofFn x) = pm x := by
  intro x
  exact (wires_permCircuit C 9 π x C.output).trans ((hc _).trans (hp x))

end Core
end PEqualNP.Outside.L_meta_25935

namespace PEqualNP.Outside.L_meta_25935
namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact getD_append_singleton_lt _ _ _ hi

def short (f g : Gate) : Circuit := ⟨[f,g],10⟩

lemma before {C : Circuit} {f g : Gate} {gs : List Gate} (hc : C.gates = f :: g :: gs)
    (x : X) (i : ℕ) (hi : i < 11) : wv C x i = wv (short f g) x i := by
  change (C.gates.foldl step (List.ofFn x)).getD i false = _
  rw [hc,List.foldl_cons,List.foldl_cons,keep gs _ (by simp [step]; omega)]
  rfl

def bad (f g : Gate) : Prop :=
  (∃ b : Bool, ∀ x : X, wv (short f g) x 10 = b) ∨
  ∃ k : Fin 10, ∀ x : X, wv (short f g) x 10 = wv (short f g) x k

lemma notBad {C : Circuit} (h : Normal C) {f g : Gate} {gs : List Gate}
    (hh : C.gates = f :: g :: gs) : ¬bad f g := by
  let j : Fin C.gates.length := ⟨1, by simp [hh]⟩
  obtain ⟨⟨x,y,ne⟩,hprev⟩ := h.2.1 j
  change wv C x 10 ≠ wv C y 10 at ne
  rintro (⟨b, hb⟩ | ⟨k,hk⟩)
  · exact ne (by rw [before hh x 10 (by decide), before hh y 10 (by decide),hb,hb])
  · obtain ⟨z,hz⟩ := hprev k k.isLt
    exact hz (by
      change wv C z 10 = wv C z k.val
      rw [before hh z 10 (by decide),before hh z k.val (by have := k.isLt; omega),hk])

def candidate (tag : Fin 3) (a b : Fin 10) : Gate :=
  if tag = 2 then ⟨.not,[a.val]⟩ else ⟨if tag = 0 then .and else .or,[a.val,b.val]⟩
def legal (t : Fin 3) (a b : Fin 10) : Prop := if t = 2 then b = 0 else a < b

lemma params {g : Gate} (hs : Shape 1 g) :
    ∃ (t : Fin 3) (a b : Fin 10), legal t a b ∧ g = candidate t a b := by
  cases g with
  | mk op ins =>
    rcases hs with ⟨ho,a,ha,hi⟩ | ⟨ho,a,b,hab,hb,hi⟩
    · exact ⟨2,⟨a,ha⟩,0,by simp [legal],by simp_all [candidate]⟩
    · have ha : a < 10 := by omega
      rcases ho with ho | ho
      · exact ⟨0,⟨a,ha⟩,⟨b,hb⟩,hab,by simp_all [candidate]⟩
      · exact ⟨1,⟨a,ha⟩,⟨b,hb⟩,hab,by simp_all [candidate]⟩

theorem find_second {C : Circuit} {f : Gate} (hh : C.gates.head? = some f)
    (he : ∀ x : X, C.eval (List.ofFn x) = pm x)
    (ho : C.output+1 = 9+C.size)
    (hone : ¬∀ x : X, (⟨[f],9⟩ : Circuit).eval (List.ofFn x) = pm x) :
    ∃ g gs, C.gates = f :: g :: gs := by
  cases C with
  | mk gates o =>
    rcases gates with _ | ⟨f',gs⟩
    · simp at hh
    · change some f' = some f at hh
      have hf : f' = f := Option.some.inj hh
      subst f'
      cases gs with
      | nil =>
        have h : o = 9 := by simp [Circuit.size] at ho; omega
        subst o
        exact False.elim (hone he)
      | cons g gs => exact ⟨g,gs,rfl⟩

end Core
end PEqualNP.Outside.L_meta_25935

namespace PEqualNP.Outside.L_meta_25935
namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Case25935

deriving instance DecidableEq for GateOp
deriving instance DecidableEq for Gate
def f0 : Gate := ⟨.not, [0]⟩
def reps : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [1]⟩, ⟨.not, [4]⟩]
def forward : Fin 8 → Fin 9 → Fin 9 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 3, 6, 1, 4, 7, 2, 5, 8], ![0, 2, 1, 3, 5, 4, 6, 8, 7], ![0, 6, 3, 1, 7, 4, 2, 8, 5], ![0, 1, 2, 6, 7, 8, 3, 4, 5], ![0, 3, 6, 2, 5, 8, 1, 4, 7], ![0, 2, 1, 6, 8, 7, 3, 5, 4], ![0, 6, 3, 2, 8, 5, 1, 7, 4]]
def backward : Fin 8 → Fin 9 → Fin 9 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 3, 6, 1, 4, 7, 2, 5, 8], ![0, 2, 1, 3, 5, 4, 6, 8, 7], ![0, 3, 6, 2, 5, 8, 1, 4, 7], ![0, 1, 2, 6, 7, 8, 3, 4, 5], ![0, 6, 3, 1, 7, 4, 2, 8, 5], ![0, 2, 1, 6, 8, 7, 3, 5, 4], ![0, 6, 3, 2, 8, 5, 1, 7, 4]]
lemma invA : ∀ p i, backward p (forward p i) = i := by decide +kernel
lemma invB : ∀ p i, forward p (backward p i) = i := by decide +kernel
def perm (p : Fin 8) : Equiv.Perm (Fin 9) :=
  ⟨forward p, backward p, invA p, invB p⟩
lemma fixes : ∀ p, Gate' (perm p) f0 = f0 := by decide +kernel
set_option maxRecDepth 16384 in
lemma preserves : ∀ p (x : X), pm (x ∘ perm p) = pm x := by decide +kernel
lemma single : ¬∀ x : X, (⟨[f0],9⟩ : Circuit).eval (List.ofFn x) = pm x := by decide +kernel
local instance (t : Fin 3) (a b : Fin 10) : Decidable (legal t a b) := by
  unfold legal; split <;> infer_instance
local instance (f g : Gate) : Decidable (bad f g) := by unfold bad; infer_instance
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma coverage : ∀ (t : Fin 3) (a b : Fin 10), legal t a b →
    (∃ p, Gate' (perm p) (candidate t a b) ∈ reps) ∨ bad f0 (candidate t a b) := by
  decide +kernel
end Case25935
end Core
end PEqualNP.Outside.L_meta_25935

open PEqualNP.Outside.L_meta_25935.Core PEqualNP.Outside.L_meta_25935.Core.Case25935 in
theorem PEqualNP.Outside.L_meta_25935 : (∀ s : ℕ,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    (C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩)) := by
  rintro s ⟨C, _, hs, he, ho, hshape, hdiff, huse, hfirst⟩
  have hn : Normal C := ⟨hshape,hdiff,huse⟩
  obtain ⟨g,gs,hgs⟩ := find_second (f := f0) hfirst he ho single
  let j : Fin C.gates.length := ⟨1,by simp [hgs]⟩
  have hget : C.gates.get j = g := by simp [List.get_eq_getElem,hgs,j]
  have hgShape := hn.1 j
  rw [hget] at hgShape
  obtain ⟨t,a,b,hleg,hg⟩ := params hgShape
  have hc := coverage t a b hleg
  rw [← hg] at hc
  rcases hc with ⟨p,hrep⟩ | hbad
  · let π := perm p
    let D := Circ π C
    have hd : Normal D := normalMap π C hn
    have hsize : D.size = C.size := by simp [D,permCircuit,PEqualNP.CircuitLowerBounds.Circuit.size]
    have hpos : 0 < C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size,hgs]
    have hOut : D.output = C.output := permWire_ge 9 π (by omega)
    refine ⟨D,allFan hd,hsize.le.trans hs,computesMap π (preserves p) he,by omega,
      hd.1,hd.2.1,hd.2.2,?_,?_⟩
    · change (C.gates.map (Gate' π)).head? = some f0
      rw [hgs]
      exact congrArg some (fixes p)
    · simp only [D, permCircuit,hgs,List.map_cons,List.tail_cons,List.head?_cons,
        Option.some.injEq]
      simpa only [reps,List.mem_cons,List.not_mem_nil,or_false] using hrep
  · exact (notBad hn hgs hbad).elim
