import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27791

open PEqualNP.CircuitLowerBounds

def firstGate : Gate := ⟨GateOp.or, [0, 4]⟩
def secondGate : Gate := ⟨GateOp.or, [2, 6]⟩

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def bank (x : Fin 9 → Bool) := step (step (List.ofFn x) firstGate) secondGate

def matchVal (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def lo (i : Fin 9) : Nat := ![176, 96, 80, 132, 69, 66, 20, 12, 10] i
def hi (i : Fin 9) : Nat := ![177, 98, 84, 140, 85, 98, 84, 140, 266] i
def bits (n : Nat) (k : Fin 9) := n.testBit k.val

set_option maxRecDepth 4096 in
theorem witnesses : ∀ i : Fin 9,
    matchVal (bits (lo i)) ≠ matchVal (bits (hi i)) ∧
    ∀ k : Fin 11, k.val ≠ i.val →
      (bank (bits (lo i)))[k.val]? = (bank (bits (hi i)))[k.val]? := by decide

theorem bank_len (x : Fin 9 → Bool) : (bank x).length = 11 := by simp [bank, step]

theorem unchanged (gs : List Gate) (u v : List Bool) (i : Nat)
    (hlen : u.length = v.length)
    (heq : ∀ k, k ≠ i → u[k]? = v[k]?)
    (hmiss : i ∉ gs.flatMap Gate.inputs) :
    ∀ k, k ≠ i → (gs.foldl step u)[k]? = (gs.foldl step v)[k]? := by
  induction gs generalizing u v with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hmiss
    have args : (g.inputs.map fun a => u.getD a false) =
        (g.inputs.map fun a => v.getD a false) := by
      apply List.map_congr_left
      intro a ha
      simpa only [List.getD_eq_getElem?_getD] using
        congrArg (fun z : Option Bool => z.getD false) (heq a (by rintro rfl; exact hmiss.1 ha))
    apply ih (step u g) (step v g) (by simp [step, hlen]) _ hmiss.2
    intro k hk
    by_cases h : k < u.length
    · simpa only [step, List.getElem?_append_left h, List.getElem?_append_left (hlen ▸ h)] using heq k hk
    · simp only [step, List.getElem?_append_right (Nat.le_of_not_gt h),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_gt h), hlen, args]

theorem raw (gs : List Gate) (out : Nat) (hout : 9 ≤ out)
    (correct : ∀ x, ((gs.foldl step (bank x)).getD out false) = matchVal x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hmiss
  obtain ⟨hdiff, hp⟩ := witnesses i
  apply hdiff
  rw [← correct, ← correct]
  simp only [List.getD_eq_getElem?_getD]
  apply congrArg (fun z : Option Bool => z.getD false)
  apply unchanged _ _ _ i.val (by simp [bank_len]) _ hmiss out (by omega)
  intro k hk
  by_cases h : k < 11
  · exact hp ⟨k, h⟩ hk
  · simp only [List.getElem?_eq_none (show (bank (bits (lo i))).length ≤ k by rw [bank_len]; omega),
        List.getElem?_eq_none (show (bank (bits (hi i))).length ≤ k by rw [bank_len]; omega)]

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h₁ := h g (by simp)
    have h₂ := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega


def binary (o : Bool) (a b : Nat) : Gate := ⟨if o then GateOp.or else GateOp.and, [a,b]⟩


theorem stable (gs : List Gate) (u v : List Bool) (out : Nat) (hlen : u.length = v.length)
    (heq : ∀ k ∈ out :: gs.flatMap Gate.inputs, u[k]? = v[k]?) :
    (gs.foldl step u)[out]? = (gs.foldl step v)[out]? := by
  induction gs generalizing u v with
  | nil => exact heq _ (by simp)
  | cons g gs ih =>
    have args : (g.inputs.map fun a => u.getD a false) =
        (g.inputs.map fun a => v.getD a false) := by
      apply List.map_congr_left
      intro a ha
      simpa only [List.getD_eq_getElem?_getD] using congrArg
        (fun z : Option Bool => z.getD false) (heq a (by simp [ha]))
    apply ih (step u g) (step v g) (by simp [step, hlen])
    intro k hk
    have old : u[k]? = v[k]? := heq k (by simpa only [List.mem_cons, List.flatMap_cons,
      List.mem_append] using (show k = out ∨ k ∈ g.inputs ∨ k ∈ gs.flatMap Gate.inputs by
        rcases List.mem_cons.mp hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)))
    by_cases h : k < u.length
    · simpa only [step, List.getElem?_append_left h, List.getElem?_append_left (hlen ▸ h)] using old
    · simp only [step, List.getElem?_append_right (Nat.le_of_not_gt h),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_gt h), hlen, args]

theorem shape (g : Gate) (n : Nat) (len : g.inputs.length = 2)
    (h : (g.op = GateOp.not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
       ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b])) :
    ∃ a b o, a < b ∧ b < n ∧ g = binary o a b := by
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨_, a, _, hi⟩ | ⟨hop, a, b, hab, hb, hi⟩
  · change ins = [a] at hi
    change ins.length = 2 at len
    simp [hi] at len
  · rcases hop with h | h
    · exact ⟨a,b,false,hab,hb, by cases h; cases hi; rfl⟩
    · exact ⟨a,b,true,hab,hb, by cases h; cases hi; rfl⟩

theorem exactWidths (gs : List Gate) (cap : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (full : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h := cap g (by simp)
    have h' := slots gs (fun a ha => cap a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at full
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ht
    · omega
    · exact ih (fun a ha => cap a (by simp [ha])) (by omega) _ ht

def schedule (n : Nat) (gs : List Gate) :=
  ∀ j : Fin gs.length, ∃ a b o, a < b ∧ b < n+j.val ∧ gs.get j = binary o a b

def possible (n : Nat) (hist : List Nat) (pre : (Fin 9 → Bool) → List Bool) : Prop :=
  ∃ gs : List Gate, n + gs.length = 21 ∧ schedule n gs ∧
    (hist ++ gs.flatMap Gate.inputs).Nodup ∧
    ∀ x, (gs.foldl step (pre x)).getD 20 false = matchVal x

theorem advance {n hist pre} (h : possible n hist pre) (hlt : n < 21) :
    ∃ a b o, a < b ∧ b < n ∧ a ∉ hist ∧ b ∉ hist ∧
      possible (n+1) (hist ++ [a,b]) (fun x => step (pre x) (binary o a b)) := by
  obtain ⟨gs, len, sched, nd, eqn⟩ := h
  cases gs with
  | nil => simp at len; omega
  | cons g gs =>
    obtain ⟨a,b,o,hab,hb,rfl⟩ := sched ⟨0,by simp⟩
    change (hist ++ a :: b :: gs.flatMap Gate.inputs).Nodup at nd
    have hd := List.disjoint_of_nodup_append nd
    refine ⟨a,b,o,hab,by simpa using hb,fun h => hd h (by simp),fun h => hd h (by simp),gs,?_,?_,?_,eqn⟩
    · simp at len; omega
    · intro j
      obtain ⟨c,d,p,hcd,hd',hg⟩ := sched ⟨j.val+1,by simp⟩
      exact ⟨c,d,p,hcd,by dsimp at hd'; omega,hg⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using nd

theorem lose {n hist pre} (poss : possible n hist pre) (outfree : 20 ∉ hist)
    (x y : Fin 9 → Bool) (diff : matchVal x ≠ matchVal y)
    (len : (pre x).length = (pre y).length)
    (agree : ∀ k, k ∉ hist → (pre x)[k]? = (pre y)[k]?) : False := by
  obtain ⟨gs,_,_,hn,eqn⟩ := poss
  apply diff
  rw [← eqn, ← eqn]
  simp only [List.getD_eq_getElem?_getD]
  apply congrArg (fun z : Option Bool => z.getD false)
  apply stable gs _ _ _ len
  intro k hk
  apply agree
  rcases List.mem_cons.mp hk with rfl | hk
  · exact outfree
  · exact fun hm => List.disjoint_of_nodup_append hn hm hk

def collision (hist : List Nat) (p : (Fin 9 → Bool) → List Bool) (code : Nat) : Prop :=
  let x := bits (code / 512)
  let y := bits (code % 512)
  matchVal x ≠ matchVal y ∧ ∀ k : Fin 14, k.val ∉ hist → (p x)[k.val]? = (p y)[k.val]?

theorem excluded {n hist p code} (poss : possible n hist p) (outfree : 20 ∉ hist)
    (hc : collision hist p code) (plen : ∀ x, (p x).length = n) (hn : n ≤ 14) : False := by
  apply lose poss outfree (bits (code / 512)) (bits (code % 512)) hc.1 (by simp [plen])
  intro k hk
  by_cases h : k < 14
  · exact hc.2 ⟨k,h⟩ hk
  · simp only [List.getElem?_eq_none (show (p (bits (code / 512))).length ≤ k by rw [plen]; omega),
      List.getElem?_eq_none (show (p (bits (code % 512))).length ≤ k by rw [plen]; omega)]

instance collisionDec (hist : List Nat) (p : (Fin 9 → Bool) → List Bool) (code : Nat) :
    Decidable (collision hist p code) := by
  unfold collision
  dsimp only
  infer_instance

def pre20 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 7 11))
def codes20 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 35412, 35412, 34402, 34402, 10836, 10836, 0, 0, 84133, 5898, 0, 0, 0, 0, 0, 0, 6796, 6796]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 0, 0, 49250, 135434, 0, 0, 0, 0, 0, 0, 49250, 7308]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 70285, 41044, 41044, 35938, 19554, 41044, 0, 0, 41044, 7434, 0, 0, 0, 0, 0, 0, 41044, 6284]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 0, 0, 67724, 132362, 0, 0, 0, 0, 0, 0, 21153, 67724]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 0, 0, 34900, 13578, 0, 0, 0, 0, 0, 0, 34900, 14476]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 0, 0, 33890, 87306, 0, 0, 0, 0, 0, 0, 33890, 22668]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 38154, 0, 0, 0, 0, 0, 0, 10324, 39052]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 71435]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test20 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 7, 11] : List Nat) → b.val ∉ ([9, 10, 7, 11] : List Nat) →
    collision ([9, 10, 7, 11] ++ [a.val,b.val]) (fun x => step (pre20 x) (binary o a.val b.val))
      ((codes20 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad20 (poss : possible 13 [9, 10, 7, 11] pre20) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test20 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre20,step,bank_len]) (by decide)

def pre19 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 6 11))
def codes19 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 35412, 35412, 34402, 34402, 0, 0, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 0, 0, 10836, 10836]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 0, 0, 11348, 11348]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 0, 0, 19554, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 0, 0, 14420, 14420]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 0, 0, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 0, 0, 25698, 34900]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 0, 0, 26708, 26708]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 0, 0, 10324, 39052]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 38154]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test19 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 6, 11] : List Nat) → b.val ∉ ([9, 10, 6, 11] : List Nat) →
    collision ([9, 10, 6, 11] ++ [a.val,b.val]) (fun x => step (pre19 x) (binary o a.val b.val))
      ((codes19 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad19 (poss : possible 13 [9, 10, 6, 11] pre19) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test19 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre19,step,bank_len]) (by decide)

def pre18 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 5 11))
def codes18 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 35412, 35412, 0, 0, 10836, 10836, 6796, 6796, 84133, 5898, 0, 0, 0, 0, 0, 0, 34402, 34402]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 0, 0, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 0, 0, 67233, 49250]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 0, 0, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 0, 0, 41044, 35938]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 0, 0, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 0, 0, 37986, 37986]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 0, 0, 34900, 42082]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 0, 0, 26708, 26708]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 87306, 0, 0, 0, 0, 0, 0, 33890, 22668]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22283]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test18 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 5, 11] : List Nat) → b.val ∉ ([9, 10, 5, 11] : List Nat) →
    collision ([9, 10, 5, 11] ++ [a.val,b.val]) (fun x => step (pre18 x) (binary o a.val b.val))
      ((codes18 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad18 (poss : possible 13 [9, 10, 5, 11] pre18) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test18 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre18,step,bank_len]) (by decide)

def pre17 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 4 11))
def codes17 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 0, 0, 34402, 34402, 10836, 10836, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 0, 0, 35412, 35412]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 0, 0, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 0, 0, 35924, 35924]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 0, 0, 41044, 35938, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 0, 0, 69772, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 0, 0, 38996, 38996]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 0, 0, 34900, 42082]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 0, 0, 25698, 34900]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 0, 0, 34900, 14476]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 13578]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test17 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 4, 11] : List Nat) → b.val ∉ ([9, 10, 4, 11] : List Nat) →
    collision ([9, 10, 4, 11] ++ [a.val,b.val]) (fun x => step (pre17 x) (binary o a.val b.val))
      ((codes17 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad17 (poss : possible 13 [9, 10, 4, 11] pre17) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test17 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre17,step,bank_len]) (by decide)

def pre16 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 2 11))
def codes16 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 0, 0, 68236, 68236, 35412, 35412, 34402, 34402, 10836, 10836, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 0, 0, 41556, 41556]
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 0, 0, 42068, 42068]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 0, 0, 41044, 43096]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 0, 0, 69772, 41044]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 0, 0, 41044, 35938]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 0, 0, 19554, 41044]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 0, 0, 41044, 69772]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41044, 7434]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test16 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 2, 11] : List Nat) → b.val ∉ ([9, 10, 2, 11] : List Nat) →
    collision ([9, 10, 2, 11] ++ [a.val,b.val]) (fun x => step (pre16 x) (binary o a.val b.val))
      ((codes16 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad16 (poss : possible 13 [9, 10, 2, 11] pre16) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test16 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre16,step,bank_len]) (by decide)

def pre15 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary true 9 10)) x) (binary false 0 11))
def codes15 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 0, 0, 49762, 49762]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 0, 0, 41556, 41556]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 0, 0, 68236, 68236]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 0, 0, 35412, 35412]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 0, 0, 34402, 34402]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 0, 0, 10836, 10836]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 0, 0, 6796, 6796]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82081, 5898]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test15 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10, 0, 11] : List Nat) → b.val ∉ ([9, 10, 0, 11] : List Nat) →
    collision ([9, 10, 0, 11] ++ [a.val,b.val]) (fun x => step (pre15 x) (binary o a.val b.val))
      ((codes15 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad15 (poss : possible 13 [9, 10, 0, 11] pre15) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test15 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre15,step,bank_len]) (by decide)

def pre14 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary true 9 10))
def codes14 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 35412, 35412, 34402, 34402, 10836, 10836, 6796, 6796, 84133, 5899, 0, 0, 0, 0, 0, 84133]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 135434, 49250]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 70285, 41044, 41044, 35938, 19554, 41044, 41044, 6284, 41044, 7947, 0, 0, 0, 0, 0, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 132362, 67724]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 14091, 0, 0, 0, 0, 0, 34900]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 0, 33890]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38667, 0, 0, 0, 0, 0, 10324]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 0, 6284]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 5899]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test14 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10] : List Nat) → b.val ∉ ([9, 10] : List Nat) →
    (a.val = 0 ∧ b.val = 11 ∧ o = false) ∨ (a.val = 2 ∧ b.val = 11 ∧ o = false) ∨ (a.val = 4 ∧ b.val = 11 ∧ o = false) ∨ (a.val = 5 ∧ b.val = 11 ∧ o = false) ∨ (a.val = 6 ∧ b.val = 11 ∧ o = false) ∨ (a.val = 7 ∧ b.val = 11 ∧ o = false) ∨ collision ([9, 10] ++ [a.val,b.val]) (fun x => step (pre14 x) (binary o a.val b.val))
      ((codes14 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad14 (poss : possible 12 [9, 10] pre14) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test14 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad15 next
  · exact bad16 next
  · exact bad17 next
  · exact bad18 next
  · exact bad19 next
  · exact bad20 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre14,step,bank_len]) (by decide)

def pre13 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary false 9 10))
def codes13 : Nat → List Nat
  | 0 => [0, 0, 49250, 49763, 41556, 41556, 67724, 68237, 35412, 35412, 33890, 34403, 10836, 10836, 6284, 6797, 82081, 5898, 0, 0, 0, 0, 82081, 92341]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 36437, 36437, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 49250, 49763]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 19554, 41044, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 69772, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 39509, 39509, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 67724, 68237]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35413, 42595, 25698, 10324, 35413, 14989, 35413, 13578, 0, 0, 0, 0, 131857, 35413]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 33890, 34403]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 17506, 10324]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 6284, 6797]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 7951]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test13 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([9, 10] : List Nat) → b.val ∉ ([9, 10] : List Nat) →
    collision ([9, 10] ++ [a.val,b.val]) (fun x => step (pre13 x) (binary o a.val b.val))
      ((codes13 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad13 (poss : possible 12 [9, 10] pre13) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test13 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre13,step,bank_len]) (by decide)

def pre12 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 6 10)) x) (binary false 4 9))
def codes12 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 0, 0, 34402, 34402, 0, 0, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 10836, 10836, 35412, 35412]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 0, 0, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 11348, 11348, 35924, 35924]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 0, 0, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 19554, 41044, 69772, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 14420, 14420, 38996, 38996]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 26708, 26708, 34900, 42082]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 10324, 39052, 34900, 14476]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 38154, 34900, 13578]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25698, 34900]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test12 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([6, 10, 4, 9] : List Nat) → b.val ∉ ([6, 10, 4, 9] : List Nat) →
    collision ([6, 10, 4, 9] ++ [a.val,b.val]) (fun x => step (pre12 x) (binary o a.val b.val))
      ((codes12 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad12 (poss : possible 13 [6, 10, 4, 9] pre12) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test12 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre12,step,bank_len]) (by decide)

def pre11 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 6 10)) x) (binary false 0 9))
def codes11 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 11348, 11348, 49762, 49762]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 19554, 41044, 41556, 41556]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 14420, 14420, 68236, 68236]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 0, 0, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 25698, 34900, 35412, 35412]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 26708, 26708, 34402, 34402]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 10324, 39052, 6796, 6796]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 38154, 82081, 5898]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10836, 10836]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test11 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([6, 10, 0, 9] : List Nat) → b.val ∉ ([6, 10, 0, 9] : List Nat) →
    collision ([6, 10, 0, 9] ++ [a.val,b.val]) (fun x => step (pre11 x) (binary o a.val b.val))
      ((codes11 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad11 (poss : possible 13 [6, 10, 0, 9] pre11) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test11 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre11,step,bank_len]) (by decide)

def pre10 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary false 6 10))
def codes10 : Nat → List Nat
  | 0 => [0, 0, 49250, 49763, 41556, 41556, 67724, 68237, 35412, 35412, 33890, 34403, 0, 0, 6284, 6797, 90289, 5899, 0, 90289, 0, 0, 10836, 10836]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 36437, 36437, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 49250, 49763, 0, 0, 11348, 11348]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 69772, 41044, 0, 0, 19554, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 39509, 39509, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 67724, 68237, 0, 0, 14420, 14420]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35413, 42595, 0, 0, 35413, 14989, 35413, 14091, 0, 35413, 0, 0, 17506, 10324]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 33890, 34403, 0, 0, 26708, 26708]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 6284, 6797, 0, 0, 10324, 39052]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 5899, 0, 0, 10324, 38154]
  | 9 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17506, 10324]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test10 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([6, 10] : List Nat) → b.val ∉ ([6, 10] : List Nat) →
    (a.val = 0 ∧ b.val = 9 ∧ o = false) ∨ (a.val = 4 ∧ b.val = 9 ∧ o = false) ∨ collision ([6, 10] ++ [a.val,b.val]) (fun x => step (pre10 x) (binary o a.val b.val))
      ((codes10 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad10 (poss : possible 12 [6, 10] pre10) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test10 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad11 next
  · exact bad12 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre10,step,bank_len]) (by decide)

def pre9 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 4 9)) x) (binary false 6 10))
def codes9 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 0, 0, 34402, 34402, 0, 0, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 35412, 35412, 10836, 10836]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 0, 0, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 35924, 35924, 11348, 11348]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 0, 0, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 69772, 41044, 19554, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 38996, 38996, 14420, 14420]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 34900, 42082, 26708, 26708]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 34900, 14476, 10324, 39052]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 13578, 10324, 38154]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25698, 34900]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test9 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([4, 9, 6, 10] : List Nat) → b.val ∉ ([4, 9, 6, 10] : List Nat) →
    collision ([4, 9, 6, 10] ++ [a.val,b.val]) (fun x => step (pre9 x) (binary o a.val b.val))
      ((codes9 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad9 (poss : possible 13 [4, 9, 6, 10] pre9) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test9 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre9,step,bank_len]) (by decide)

def pre8 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 4 9)) x) (binary false 2 10))
def codes8 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 0, 0, 68236, 68236, 0, 0, 34402, 34402, 10836, 10836, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 35412, 35412, 41556, 41556]
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 0, 0, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 35924, 35924, 42068, 42068]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 38996, 38996, 41044, 43096]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 34900, 42082, 41044, 35938]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 25698, 34900, 19554, 41044]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 34900, 14476, 41044, 69772]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 13578, 41044, 7434]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69772, 41044]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test8 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([4, 9, 2, 10] : List Nat) → b.val ∉ ([4, 9, 2, 10] : List Nat) →
    collision ([4, 9, 2, 10] ++ [a.val,b.val]) (fun x => step (pre8 x) (binary o a.val b.val))
      ((codes8 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad8 (poss : possible 13 [4, 9, 2, 10] pre8) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test8 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre8,step,bank_len]) (by decide)

def pre7 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary false 4 9))
def codes7 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 41556, 41556, 68236, 68236, 0, 0, 34402, 34402, 10836, 10836, 6796, 6796, 82081, 5898, 0, 0, 82081, 84133, 35412, 35412]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 0, 0, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 135434, 49250, 35924, 35924]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 0, 0, 41044, 35938, 19554, 41044, 41044, 6284, 41044, 7438, 0, 0, 0, 41044, 102604, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 132362, 67724, 38996, 38996]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 66209, 33890, 34900, 42082]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 40206, 0, 0, 0, 10324, 27750, 34900]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 17057, 6284, 34900, 14476]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 7438, 34900, 13578]
  | 10 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131857, 34900]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test7 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([4, 9] : List Nat) → b.val ∉ ([4, 9] : List Nat) →
    (a.val = 2 ∧ b.val = 10 ∧ o = false) ∨ (a.val = 6 ∧ b.val = 10 ∧ o = false) ∨ collision ([4, 9] ++ [a.val,b.val]) (fun x => step (pre7 x) (binary o a.val b.val))
      ((codes7 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad7 (poss : possible 12 [4, 9] pre7) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test7 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad8 next
  · exact bad9 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre7,step,bank_len]) (by decide)

def pre6 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 2 10)) x) (binary false 4 9))
def codes6 : Nat → List Nat
  | 0 => [0, 0, 49762, 49762, 0, 0, 68236, 68236, 0, 0, 34402, 34402, 10836, 10836, 6796, 6796, 82081, 5898, 0, 0, 0, 0, 41556, 41556, 35412, 35412]
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 0, 0, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 42068, 42068, 35924, 35924]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 41044, 43096, 38996, 38996]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 41044, 35938, 34900, 42082]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 19554, 41044, 25698, 34900]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 41044, 69772, 34900, 14476]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41044, 7434, 34900, 13578]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69772, 41044]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test6 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([2, 10, 4, 9] : List Nat) → b.val ∉ ([2, 10, 4, 9] : List Nat) →
    collision ([2, 10, 4, 9] ++ [a.val,b.val]) (fun x => step (pre6 x) (binary o a.val b.val))
      ((codes6 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad6 (poss : possible 13 [2, 10, 4, 9] pre6) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test6 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre6,step,bank_len]) (by decide)

def pre5 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 2 10)) x) (binary false 0 9))
def codes5 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 42068, 42068, 49762, 49762]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 41044, 43096, 68236, 68236]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 69772, 41044, 35412, 35412]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 41044, 35938, 34402, 34402]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 19554, 41044, 10836, 10836]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 41044, 69772, 6796, 6796]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41044, 7434, 82081, 5898]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41556, 41556]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test5 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([2, 10, 0, 9] : List Nat) → b.val ∉ ([2, 10, 0, 9] : List Nat) →
    collision ([2, 10, 0, 9] ++ [a.val,b.val]) (fun x => step (pre5 x) (binary o a.val b.val))
      ((codes5 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad5 (poss : possible 13 [2, 10, 0, 9] pre5) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test5 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre5,step,bank_len]) (by decide)

def pre4 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary false 2 10))
def codes4 : Nat → List Nat
  | 0 => [0, 0, 49250, 49763, 0, 0, 67724, 68237, 35412, 35412, 33890, 34403, 10836, 10836, 6284, 6797, 90289, 5899, 0, 90289, 0, 0, 41556, 41556]
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 36437, 36437, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 49250, 49763, 0, 0, 42068, 42068]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 39509, 39509, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 67724, 68237, 0, 0, 41044, 43096]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35413, 42595, 17506, 10324, 35413, 14989, 35413, 14091, 0, 35413, 0, 0, 69772, 41044]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 33890, 34403, 0, 0, 41044, 35938]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 17506, 10324, 0, 0, 19554, 41044]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 6284, 6797, 0, 0, 41044, 69772]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 5899, 0, 0, 41044, 7434]
  | 9 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69772, 41044]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test4 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([2, 10] : List Nat) → b.val ∉ ([2, 10] : List Nat) →
    (a.val = 0 ∧ b.val = 9 ∧ o = false) ∨ (a.val = 4 ∧ b.val = 9 ∧ o = false) ∨ collision ([2, 10] ++ [a.val,b.val]) (fun x => step (pre4 x) (binary o a.val b.val))
      ((codes4 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad4 (poss : possible 12 [2, 10] pre4) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test4 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad5 next
  · exact bad6 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre4,step,bank_len]) (by decide)

def pre3 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 0 9)) x) (binary false 6 10))
def codes3 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 0, 0, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 49762, 49762, 11348, 11348]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 69772, 41044, 41044, 35938, 0, 0, 41044, 69772, 41044, 7434, 0, 0, 0, 0, 41556, 41556, 19554, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 0, 0, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 68236, 68236, 14420, 14420]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 0, 0, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 35412, 35412, 25698, 34900]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 34402, 34402, 26708, 26708]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 6796, 6796, 10324, 39052]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82081, 5898, 10324, 38154]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10836, 10836]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test3 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([0, 9, 6, 10] : List Nat) → b.val ∉ ([0, 9, 6, 10] : List Nat) →
    collision ([0, 9, 6, 10] ++ [a.val,b.val]) (fun x => step (pre3 x) (binary o a.val b.val))
      ((codes3 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad3 (poss : possible 13 [0, 9, 6, 10] pre3) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test3 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre3,step,bank_len]) (by decide)

def pre2 : (Fin 9 → Bool) → List Bool := (fun x => step ((fun x => step (bank x) (binary false 0 9)) x) (binary false 2 10))
def codes2 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 0, 0, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 0, 0, 49762, 49762, 42068, 42068]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 0, 0, 68236, 68236, 41044, 43096]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 25698, 34900, 34900, 14476, 34900, 13578, 0, 0, 0, 0, 35412, 35412, 69772, 41044]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 0, 0, 34402, 34402, 41044, 35938]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 38154, 0, 0, 0, 0, 10836, 10836, 19554, 41044]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 0, 0, 6796, 6796, 41044, 69772]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82081, 5898, 41044, 7434]
  | 11 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41556, 41556]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test2 (a : Fin 13) : ∀ (b : Fin 13) (o : Bool),
    a.val < b.val → a.val ∉ ([0, 9, 2, 10] : List Nat) → b.val ∉ ([0, 9, 2, 10] : List Nat) →
    collision ([0, 9, 2, 10] ++ [a.val,b.val]) (fun x => step (pre2 x) (binary o a.val b.val))
      ((codes2 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad2 (poss : possible 13 [0, 9, 2, 10] pre2) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test2 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  exact excluded next (by simp; omega) hc (by intro x; simp [pre2,step,bank_len]) (by decide)

def pre1 : (Fin 9 → Bool) → List Bool := (fun x => step (bank x) (binary false 0 9))
def codes1 : Nat → List Nat
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 35924, 35924, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 0, 0, 135434, 49250, 49762, 49762]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 102604, 41044, 41044, 35938, 19554, 41044, 41044, 6284, 41044, 7438, 0, 0, 0, 41044, 41556, 41556]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 38996, 38996, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 0, 0, 132362, 67724, 68236, 68236]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34900, 42082, 27750, 34900, 34900, 14476, 34900, 13578, 0, 0, 131857, 34900, 35412, 35412]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 0, 0, 66209, 33890, 34402, 34402]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 40206, 0, 0, 0, 10324, 10836, 10836]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 0, 0, 17057, 6284, 6796, 6796]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 7438, 82081, 5898]
  | 10 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82081, 84133]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test1 (a : Fin 12) : ∀ (b : Fin 12) (o : Bool),
    a.val < b.val → a.val ∉ ([0, 9] : List Nat) → b.val ∉ ([0, 9] : List Nat) →
    (a.val = 2 ∧ b.val = 10 ∧ o = false) ∨ (a.val = 6 ∧ b.val = 10 ∧ o = false) ∨ collision ([0, 9] ++ [a.val,b.val]) (fun x => step (pre1 x) (binary o a.val b.val))
      ((codes1 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad1 (poss : possible 12 [0, 9] pre1) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test1 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad2 next
  · exact bad3 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre1,step,bank_len]) (by decide)

def pre0 : (Fin 9 → Bool) → List Bool := bank
def codes0 : Nat → List Nat
  | 0 => [0, 0, 49250, 49763, 41556, 41556, 67724, 68237, 35412, 35412, 33890, 34403, 10836, 10836, 6284, 6797, 90289, 5899, 0, 90289, 90289, 92341]
  | 1 => [0, 0, 0, 0, 42068, 42068, 49250, 50280, 36437, 36437, 67233, 49250, 11348, 11348, 49250, 7308, 49250, 135434, 49250, 49763, 135434, 49250]
  | 2 => [0, 0, 0, 0, 0, 0, 41044, 43096, 102604, 41044, 41044, 35938, 19554, 41044, 41044, 6284, 41044, 7438, 102604, 41044, 0, 41044]
  | 3 => [0, 0, 0, 0, 0, 0, 0, 0, 39509, 39509, 37986, 37986, 14420, 14420, 21153, 67724, 67724, 132362, 67724, 68237, 132362, 67724]
  | 4 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35413, 42595, 19558, 10324, 35413, 14989, 35413, 14091, 0, 35413, 131857, 35413]
  | 5 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26708, 26708, 33890, 22668, 33890, 21770, 33890, 34403, 66209, 33890]
  | 6 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10324, 39052, 10324, 40206, 19558, 10324, 0, 10324]
  | 7 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6284, 70922, 6284, 6797, 17057, 6284]
  | 8 => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5386, 5899, 5386, 7438]
  | _ => []
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem test0 (a : Fin 11) : ∀ (b : Fin 11) (o : Bool),
    a.val < b.val → a.val ∉ ([] : List Nat) → b.val ∉ ([] : List Nat) →
    (a.val = 0 ∧ b.val = 9 ∧ o = false) ∨ (a.val = 2 ∧ b.val = 10 ∧ o = false) ∨ (a.val = 4 ∧ b.val = 9 ∧ o = false) ∨ (a.val = 6 ∧ b.val = 10 ∧ o = false) ∨ (a.val = 9 ∧ b.val = 10 ∧ o = false) ∨ (a.val = 9 ∧ b.val = 10 ∧ o = true) ∨ collision ([] ++ [a.val,b.val]) (fun x => step (pre0 x) (binary o a.val b.val))
      ((codes0 a.val).getD (2*b.val + o.toNat) 0) := by
  fin_cases a <;> decide

theorem bad0 (poss : possible 11 [] pre0) : False := by
  obtain ⟨a,b,o,hab,hb,ha',hb',next⟩ := advance poss (by decide)
  have hc := test0 ⟨a,by omega⟩ ⟨b,hb⟩ o hab ha' hb'
  simp only at hc
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | hc
  · exact bad1 next
  · exact bad4 next
  · exact bad7 next
  · exact bad10 next
  · exact bad13 next
  · exact bad14 next
  · exact excluded next (by simp; omega) hc (by intro x; simp [pre0,step,bank_len]) (by decide)

end PEqualNP.Outside.L_meta_27791
open PEqualNP.Outside.L_meta_27791 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_27791 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩) := by
  rintro ⟨C, hfan, hsize, hfun, hout, hnorm, _, hlive, h₁, h₂⟩
  obtain ⟨gs, hgs⟩ : ∃ gs, C.gates = firstGate :: secondGate :: gs := by
    cases he : C.gates with
    | nil => simp [he] at h₁
    | cons a tail =>
      cases tail with
      | nil => simp [he] at h₂
      | cons b gs =>
        simp [he] at h₁ h₂
        exact ⟨gs, by rw [h₁, h₂]; rfl⟩
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size, hgs, List.length_cons] at hsize hout
  have correct : ∀ x, (gs.foldl step (bank x)).getD C.output false = matchVal x := by
    intro x
    have hx := hfun x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = matchVal x at hx
    rw [hgs] at hx
    exact hx
  have cover : Finset.range (10 + gs.length) ⊆ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset := by
    intro w hw
    apply List.mem_toFinset.mpr
    have hw' := Finset.mem_range.mp hw
    by_cases low : w < 9
    · exact raw gs _ (by omega) correct ⟨w, low⟩
    · let j : Fin C.gates.length := ⟨w - 9, by simp [hgs]; omega⟩
      have hj : j.val + 1 < C.gates.length := by simp [j, hgs]; omega
      obtain ⟨k, _, hread⟩ := hlive j hj
      have heq : 9 + j.val = w := by dsimp [j]; omega
      rw [heq] at hread
      have hmem : C.gates.get k ∈ firstGate :: secondGate :: gs :=
        by rw [← hgs]; exact List.get_mem C.gates k
      rcases List.mem_cons.mp hmem with hf | ht
      · rw [hf] at hread
        simp [firstGate] at hread
        omega
      rcases List.mem_cons.mp ht with hs | ht
      · rw [hs] at hread
        simp [secondGate] at hread
        omega
      exact List.mem_flatMap_of_mem ht hread
  have cap := slots gs (fun g hg => (hfan g (by rw [hgs]; simp [hg])).2)
  have lower := Finset.card_le_card cover
  rw [Finset.card_range] at lower
  have bound := List.toFinset_card_le (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)
  have size : gs.length = 10 := by omega
  have full : (gs.flatMap Gate.inputs).length = 20 := by omega
  have uniq : (gs.flatMap Gate.inputs).Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(gs.flatMap Gate.inputs) : Multiset Nat))).mp
      (show (gs.flatMap Gate.inputs).toFinset.card = (gs.flatMap Gate.inputs).length by omega)
  have wid := exactWidths gs (fun g hg => (hfan g (by rw [hgs]; simp [hg])).2) (by omega)
  apply bad0
  refine ⟨gs,by omega,?_,uniq,?_⟩
  · intro j
    have hj : j.val+2 < C.gates.length := by simp [hgs]
    have norm := hnorm ⟨j.val+2,hj⟩
    simp [hgs] at norm
    apply shape _ _ (wid _ (List.get_mem gs j))
    rw [show 11 + j.val = 9 + (j.val+2) by omega]
    exact norm
  · have out : C.output = 20 := by omega
    simpa only [out, pre0] using correct
