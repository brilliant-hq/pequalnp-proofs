import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23988_aux

open CircuitLowerBounds MetaComplexity Represents

inductive Ref where
  | zero | one | wire (i : ℕ)

def value (w : ℕ → Bool) : Ref → Bool
  | .zero => false
  | .one => true
  | .wire i => w i

def gateValue (g : Gate) (w : ℕ → Bool) := g.op.eval (g.inputs.map w)

def Shape (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)

def Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2

/
inductive Step (g : Gate) (f : ℕ → Ref) (cut : ℕ) : Type where
  | reuse (r : Ref)
      (src : ∀ i, r = .wire i → ∃ j ∈ g.inputs, f j = .wire i)
      (correct : ∀ w, gateValue g (fun j => value w (f j)) = value w r)
  | emit (h : Gate) (legal : Legal h) (miss : cut ∉ g.inputs)
      (src : ∀ i ∈ h.inputs, ∃ j ∈ g.inputs, f j = .wire i)
      (correct : ∀ w, gateValue g (fun j => value w (f j)) = gateValue h w)

private theorem step_exists (g : Gate) (f : ℕ → Ref) (cut : ℕ)
    (hc : f cut = .zero) (hs : Shape g) : Nonempty (Step g f cut) := by
  rcases g with ⟨op, ins⟩
  change ((op = .and ∨ op = .or) ∧ ins.length = 2) ∨
    (op = .not ∧ ins.length = 1) at hs
  rcases hs with ⟨hop, hlen⟩ | ⟨rfl, hlen⟩
  · obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    have reuse (i : ℕ) (hi : i ∈ [a,b])
        (hv : ∀ w, gateValue ⟨op,[a,b]⟩ (fun j => value w (f j)) = value w (f i)) :
        Nonempty (Step ⟨op,[a,b]⟩ f cut) :=
      ⟨.reuse (f i) (fun _ he => ⟨i,hi,he⟩) hv⟩
    have emit (x y : ℕ) (hx : f a = .wire x) (hy : f b = .wire y) :
        Nonempty (Step ⟨op,[a,b]⟩ f cut) := by
      refine ⟨.emit ⟨op,[x,y]⟩ ?_ ?_ ?_ ?_⟩
      · rcases hop with rfl | rfl <;> simp [Legal]
      · change cut ∉ [a,b]; simp; grind
      · intro i hi
        rcases (by simpa using hi : i = x ∨ i = y) with rfl | rfl
        · exact ⟨a, by simp, hx⟩
        · exact ⟨b, by simp, hy⟩
      · simp [gateValue, hx, hy, value]
    rcases hop with rfl | rfl <;> cases ha : f a <;> cases hb : f b <;> first
      | exact emit _ _ ha hb
      | apply reuse a (by simp); solve | simp [gateValue, GateOp.eval, ha, hb, value]
      | apply reuse b (by simp); solve | simp [gateValue, GateOp.eval, ha, hb, value]
  · obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hlen
    cases ha : f a with
    | zero => exact ⟨.reuse .one (by simp) (by simp [gateValue, GateOp.eval, ha, value])⟩
    | one => exact ⟨.reuse .zero (by simp) (by simp [gateValue, GateOp.eval, ha, value])⟩
    | wire x =>
      exact ⟨.emit ⟨.not, [x]⟩ (by simp [Legal]) (by simp; grind)
        (by simp [ha]) (by simp [gateValue, ha, value])⟩

def read (xs : List Bool) (i : ℕ) := xs.getD i false

def run (gs : List Gate) (xs : List Bool) := (Circuit.mk gs 0).wires xs

@[simp] theorem run_nil (xs : List Bool) : run [] xs = xs := rfl

theorem run_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    run (g :: gs) xs = run gs (xs ++ [gateValue g (read xs)]) := rfl

@[simp] theorem run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [gateValue g (read (run gs xs))] := by
  unfold run Circuit.wires
  rw [List.foldl_append]
  rfl

@[simp] theorem run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => rw [run_cons, ih]; simp; omega

theorem read_snoc (xs : List Bool) (b : Bool) (i : ℕ) :
    read (xs ++ [b]) i = if i = xs.length then b else read xs i := by
  by_cases h : i < xs.length
  · simp [read, List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · have he := List.getElem?_append_right (l₂ := [b]) (Nat.le_of_not_lt h)
    rw [read, List.getD_eq_getElem?_getD, he]
    split_ifs with hi
    · simp [hi]
    · have hp : 0 < i - xs.length := by omega
      simp [List.getElem?_eq_none (show [b].length ≤ i - xs.length from hp),
        read, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]

def Used (C : Circuit) (i : ℕ) := (∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i

def Allowed {m : ℕ} (n : ℕ) (k : Fin (m+1)) (C : Circuit) (w : ℕ) :=
  (∀ i : Fin n, w = i → Used C i) ∧
  (∀ j : Fin m, w = n + j → Used C (n + (k.succAbove j).val))

theorem allowed_fresh {n m w : ℕ} {k : Fin (m+1)} {C : Circuit} (hw : n + m ≤ w) :
    Allowed n k C w := by
  constructor <;> intro i hi <;> have := i.isLt <;> omega

def initial {m : ℕ} (n : ℕ) (k : Fin (m+1)) (w : ℕ) : Ref :=
  if w < n then .wire w
  else if h : w - n < m + 1 then
    k.insertNth (α := fun _ => Ref) .zero (fun v => Ref.wire (n + v.val)) ⟨w - n, h⟩
  else .zero

@[simp] theorem initial_left {m n : ℕ} (k : Fin (m+1)) (i : Fin n) :
    initial n k i = .wire i := by simp [initial, i.isLt]

theorem initial_right {m n : ℕ} (k j : Fin (m+1)) :
    initial n k (n + j.val) = k.insertNth (α := fun _ => Ref) .zero (fun v => Ref.wire (n + v.val)) j := by
  simp [initial, j.isLt]

theorem left_read {n m : ℕ} (u i : Fin n) (v : Fin m) :
    read (oneEach u v) i = decide (i = u) := by
  simp [read, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left]

theorem right_read {n m : ℕ} (u : Fin n) (v j : Fin m) :
    read (oneEach u v) (n + j.val) = decide (j = v) := by
  simp [read, oneEach, List.getD_eq_getElem?_getD]

@[simp] theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by simp [oneEach]

theorem indices {n m : ℕ} (k : Fin (m+1)) (P : ℕ → Prop)
    (left : ∀ i : Fin n, P i) (cut : P (n + k.val))
    (right : ∀ j : Fin m, P (n + (k.succAbove j).val))
    (beyond : ∀ w, n + (m+1) ≤ w → P w) : ∀ w, P w := by
  intro w
  by_cases hl : w < n
  · exact left ⟨w, hl⟩
  by_cases hr : w < n + (m+1)
  · have all := (Fin.forall_iff_succAbove (P := fun j => P (n + j.val)) k).2 ⟨cut,right⟩
    simpa [Nat.add_sub_of_le (Nat.le_of_not_lt hl)] using all ⟨w-n, by omega⟩
  · exact beyond w (by omega)

structure Simulation {n m : ℕ} (k : Fin (m+1)) (C : Circuit) (gs hs : List Gate)
    (f : ℕ → Ref) : Prop where
  cut : f (n + k.val) = .zero
  bound : ∀ i t, f i = .wire t → t < n + m + hs.length
  source : ∀ i t, Used C i → f i = .wire t → Allowed n k C t
  legal : ∀ h ∈ hs, Legal h
  reads : ∀ h ∈ hs, ∀ t ∈ h.inputs, Allowed n k C t
  size : hs.length ≤ gs.length
  strict : (∃ g ∈ gs, n + k.val ∈ g.inputs) → hs.length < gs.length
  correct : ∀ (u : Fin n) (v : Fin m) i,
    read (run gs (oneEach u (k.succAbove v))) i =
      value (read (run hs (oneEach u v))) (f i)

theorem start {n m : ℕ} (k : Fin (m+1)) (C : Circuit) :
    Simulation (n := n) k C [] [] (initial n k) := by
  have beyond (i : ℕ) (hi : n + (m+1) ≤ i) : initial n k i = .zero := by
    simp [initial, show ¬ i < n by omega, show ¬ i-n < m+1 by omega]
  refine ⟨by simp [initial_right], ?_, ?_, by simp, by simp, by simp, by simp, ?_⟩
  · apply indices (n := n) k
    · intro i t h; simp at h; subst t; simp; omega
    · simp [initial_right]
    · intro j t h; simp [initial_right] at h; subst t; simp
    · intro i hi; simp [beyond i hi]
  · apply indices (n := n) k
    · intro i t hu h; simp at h; subst t
      constructor
      · intro j hj; simpa [← hj] using hu
      · intro j hj; have := i.isLt; omega
    · simp [initial_right]
    · intro j t hu h; simp [initial_right] at h; subst t
      constructor
      · intro i hi; have := i.isLt; omega
      · intro l hl; have e : j = l := Fin.ext (by omega); simpa [← e] using hu
    · intro i hi; simp [beyond i hi]
  · intro u v
    apply indices (n := n) k
    · intro i; simp [value, left_read]
    · simp [initial_right, right_read, value, Ne.symm (Fin.succAbove_ne k v)]
    · intro j; simp [initial_right, right_read, value]
    · intro i hi
      simp [beyond i hi, value, read, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show (oneEach u (k.succAbove v)).length ≤ i by simpa using hi)]

theorem advance {n m : ℕ} {k : Fin (m+1)} {C : Circuit} {gs hs : List Gate}
    {f : ℕ → Ref} (s : Simulation (n := n) k C gs hs f) (g : Gate)
    (hg : g ∈ C.gates) (shape : Shape g) :
    ∃ hs' f', Simulation (n := n) k C (gs ++ [g]) hs' f' := by
  let old := n + (m+1) + gs.length
  let newIdx := n + m + hs.length
  have cut_ne : n + k.val ≠ old := by dsimp [old]; have := k.isLt; omega
  have used (j : ℕ) (hj : j ∈ g.inputs) : Used C j := Or.inl ⟨g,hg,hj⟩
  let vals := fun (ls : List Gate) (u : Fin n) (v : Fin m) => read (run ls (oneEach u v))
  have build (ls : List Gate) (r : Ref)
      (legal : ∀ h ∈ ls, Legal h) (reads : ∀ h ∈ ls, ∀ t ∈ h.inputs, Allowed n k C t)
      (lo : hs.length ≤ ls.length) (hi : ls.length ≤ hs.length + 1)
      (dropGate : n + k.val ∈ g.inputs → ls.length ≤ hs.length)
      (bound : ∀ t, r = .wire t → t < n + m + ls.length)
      (source : ∀ t, r = .wire t → Allowed n k C t)
      (keep : ∀ u v i, value (vals ls u v) (f i) = value (vals hs u v) (f i))
      (result : ∀ u v, gateValue g (fun j => value (vals hs u v) (f j)) =
        value (vals ls u v) r) :
      ∃ ls' f', Simulation (n := n) k C (gs ++ [g]) ls' f' := by
    refine ⟨ls, fun i => if i = old then r else f i, ?_⟩
    constructor
    · simp [cut_ne, s.cut]
    · intro i t hit
      split_ifs at hit with h
      · exact bound t hit
      · have := s.bound i t hit; omega
    · intro i t hu hit
      split_ifs at hit
      · exact source t hit
      · exact s.source i t hu hit
    · exact legal
    · exact reads
    · simp; have := s.size; omega
    · rintro ⟨h,hm,hr⟩
      rcases List.mem_append.mp hm with hm | hm
      · have := s.strict ⟨h,hm,hr⟩; simp; omega
      · have he : h = g := by simpa using hm
        subst h; have := dropGate hr; have := s.size; simp; omega
    · intro u v i
      rw [run_snoc, read_snoc]
      simp only [run_length, oneEach_length]
      change (if i = old then _ else _) = _
      by_cases he : i = old
      · simp only [he, ite_true]
        rw [show read (run gs (oneEach u (k.succAbove v))) =
          (fun j => value (vals hs u v) (f j)) from funext (s.correct u v)]
        exact result u v
      · simp only [he, ite_false]
        exact (s.correct u v i).trans (keep u v i).symm
  obtain ⟨step⟩ := step_exists g f (n + k.val) s.cut shape
  cases step with
  | reuse r src correct =>
    apply build hs r s.legal s.reads (by omega) (by omega) (by simp)
    · intro t ht
      obtain ⟨j,_,hj⟩ := src t ht
      exact s.bound j t hj
    · intro t ht
      obtain ⟨j,hj,he⟩ := src t ht
      exact s.source j t (used j hj) he
    · intros; rfl
    · exact fun u v => correct (vals hs u v)
  | emit h legal miss src correct =>
    apply build (hs ++ [h]) (.wire newIdx)
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact s.legal a ha
      · simpa [List.mem_singleton.mp ha] using legal
    · intro a ha t ht
      rcases List.mem_append.mp ha with ha | ha
      · exact s.reads a ha t ht
      · obtain rfl := List.mem_singleton.mp ha
        obtain ⟨j,hj,he⟩ := src t ht
        exact s.source j t (used j hj) he
    · simp
    · simp
    · exact fun hm => (miss hm).elim
    · intro t ht; cases ht; simp [newIdx]
    · intro t ht; cases ht; apply allowed_fresh; dsimp [newIdx]; omega
    · intro u v i
      cases he : f i with
      | zero | one => rfl
      | wire t =>
        have ht := s.bound i t he
        simp [vals, value, read_snoc, Nat.ne_of_lt ht]
    · intro u v
      rw [correct]
      simp [value, vals, read_snoc, newIdx]

theorem simulate {n m : ℕ} (k : Fin (m+1)) (C : Circuit)
    (shape : ∀ g ∈ C.gates, Shape g) :
    ∃ hs f, Simulation (n := n) k C C.gates hs f := by
  suffices ∀ gs : List Gate, (∀ g ∈ gs, g ∈ C.gates) →
      ∃ hs f, Simulation (n := n) k C gs hs f by
    exact this C.gates (by simp)
  intro gs
  induction gs using List.reverseRecOn with
  | nil => exact fun _ => ⟨_, _, start k C⟩
  | append_singleton gs g ih =>
    intro sub
    have hg := sub g (by simp)
    obtain ⟨hs,f,s⟩ := ih (fun a ha => sub a (by simp [ha]))
    exact advance s g hg (shape g hg)

end PEqualNP.Outside.L_meta_23988_aux

open PEqualNP.Outside.L_meta_23988_aux in
theorem PEqualNP.Outside.L_meta_23988 : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C _ shape rep hit nonconst
  obtain ⟨gs,f,s⟩ := simulate (n := n) k C shape
  have hval (u : Fin n) (v : Fin m) :
      value (read (run gs (PEqualNP.Represents.oneEach u v))) (f C.output) =
        A u (k.succAbove v) :=
    (s.correct u v C.output).symm.trans (rep u (k.succAbove v))
  obtain ⟨u,u',v,v',hne⟩ := nonconst
  cases ho : f C.output with
  | zero | one =>
    exact (hne (by simp [← hval, ho, value])).elim
  | wire t =>
    refine ⟨⟨gs,t⟩, s.legal, ?_, s.strict hit, ?_, ?_⟩
    · intro i j
      have hv := hval i j
      rw [ho] at hv
      exact hv
    · intro i h
      rcases h with ⟨g,hg,hi⟩ | hi
      · exact (s.reads g hg i hi).1 i rfl
      · exact (s.source C.output t (Or.inr rfl) ho).1 i hi
    · intro j h
      rcases h with ⟨g,hg,hj⟩ | hj
      · exact (s.reads g hg _ hj).2 j rfl
      · exact (s.source C.output t (Or.inr rfl) ho).2 j hj
